"""Coach personnel : « !coach #TAG » dans un salon dédié.

Lit le profil et les 25 derniers combats du joueur (limite de l'API) et répond avec :
bilan, bêtes noires (decks adverses qui te battent), gestion de l'élixir, moments de la journée,
effet des défaites (tilt), analyse de ton deck principal (même moteur que DeckBot), cartes fortes que tu
possèdes sans les jouer, cartes à monter en priorité, et un plan d'action.

Il réutilise DeckBot.py (même dépôt). Variables d'environnement :
  CR_API_KEY, DISCORD_BOT_TOKEN, DISCORD_CHANNEL_ID (= le salon du coach, pas celui de DeckBot)
Lancement : python Coach.py repondre
"""
import re
import sys
import time
import datetime
from zoneinfo import ZoneInfo

import DeckBot as d

PARIS = ZoneInfo("Europe/Paris")
MIN_COMBATS = 8                   # en dessous, pas assez de combats récents pour conseiller
MIN_ARCHETYPE = 3                 # parties contre un même type de deck avant d'en parler
MIN_CARTE_ADVERSE = 4             # apparitions d'une carte adverse avant d'en parler
MIN_PAR_TRANCHE = 6               # combats minimum par tranche horaire / situation
MAX_DEMANDES = 3                  # demandes traitées par passage (chaque analyse fait des appels à l'API)

# Cartes qui définissent le plan de jeu d'un deck, par ordre de priorité
PLANS = [
    ("Lava Hound", "air"), ("Balloon", "air"),
    ("Golem", "tank"), ("Elixir Golem", "tank"), ("Electro Giant", "tank"), ("Goblin Giant", "tank"),
    ("Royal Giant", "tank"), ("Giant", "tank"),
    ("X-Bow", "siege"), ("Mortar", "siege"),
    ("Graveyard", "cycle"), ("Hog Rider", "cycle"), ("Royal Hogs", "cycle"), ("Ram Rider", "cycle"),
    ("Battle Ram", "cycle"), ("Miner", "cycle"), ("Goblin Barrel", "cycle"), ("Skeleton Barrel", "cycle"),
    ("P.E.K.K.A", "lourd"), ("Mega Knight", "lourd"), ("Sparky", "lourd"),
]
NOM_PLAN = {"air": "decks aériens", "tank": "decks à gros tank", "siege": "decks de siège",
            "cycle": "decks rapides (cycle)", "lourd": "decks lourds", "autre": "autres decks"}
CONSEIL_PLAN = {
    "air": "garde toujours de quoi défendre dans les airs et ne le gaspille pas en attaque ; le sort et le bâtiment doivent rester dispos pour Ballon / Meute de lave.",
    "tank": "punis le tank : attaque l'autre voie dès qu'il le pose, et réserve ton meilleur dégât pur pour le tuer au pont.",
    "siege": "ne laisse pas le siège s'installer : mets la pression dès qu'il le pose et garde un sort ou une carte rapide pour le détruire.",
    "cycle": "garde ton élixir pour défendre et fais des échanges positifs : évite de poser en avance, sinon tu te fais cycler.",
    "lourd": "ne t'engage pas en défense avec des unités fragiles : use de bâtiment et de troupes à petits coûts pour tenir.",
    "autre": "regarde quelle carte revient dans tes défaites et prépare-lui une réponse précise.",
}


# ========================
# 🔹 Lecture des combats
# ========================
def type_vers_mode(t):
    for mode, m in d.MODES.items():
        if t in m["types"]:
            return mode
    return "autre"


def lire_combats(brut):
    """Combats 1c1 exploitables, du plus ancien au plus récent."""
    res = []
    for b in brut or []:
        eq, ad = b.get("team") or [], b.get("opponent") or []
        if len(eq) != 1 or len(ad) != 1:
            continue
        me, op = eq[0], ad[0]
        mes, adv = me.get("cards") or [], op.get("cards") or []
        if len(mes) != 8 or len(adv) != 8:
            continue
        try:
            t = datetime.datetime.strptime(b["battleTime"][:15], "%Y%m%dT%H%M%S").replace(tzinfo=datetime.timezone.utc)
        except (KeyError, ValueError):
            continue
        c1, c2 = me.get("crowns", 0), op.get("crowns", 0)
        res.append({"t": t, "mode": type_vers_mode(b.get("type", "")), "win": c1 > c2, "loss": c1 < c2,
                    "c1": c1, "c2": c2, "trophees": me.get("trophyChange"), "fuite": me.get("elixirLeaked"),
                    "mes": mes, "adv": adv})
    res.sort(key=lambda c: c["t"])
    return res


def plan_adverse(cartes):
    noms = {c.get("name") for c in cartes}
    for nom, plan in PLANS:
        if nom in noms:
            return nom, plan
    return None, "autre"


def pct(a, b):
    return f"{100 * a / b:.0f}%" if b else "–"


# ========================
# 🔹 Analyses
# ========================
def bilan(combats):
    n = len(combats)
    v = sum(c["win"] for c in combats)
    l = sum(c["loss"] for c in combats)
    trois = sum(1 for c in combats if c["win"] and c["c1"] == 3)
    subi = sum(1 for c in combats if c["loss"] and c["c2"] == 3)
    serie, sens = 0, None
    for c in reversed(combats):
        etat = "V" if c["win"] else ("D" if c["loss"] else "N")
        if sens is None:
            sens = etat
        if etat != sens:
            break
        serie += 1
    par_mode = {}
    for c in combats:
        m = par_mode.setdefault(c["mode"], [0, 0])
        m[0] += 1
        m[1] += c["win"]
    gains = [c["trophees"] for c in combats if c["trophees"] is not None]
    return {"n": n, "v": v, "l": l, "trois": trois, "subi": subi, "serie": serie, "sens": sens,
            "par_mode": par_mode, "trophees": sum(gains) if gains else None}


def betes_noires(combats):
    """Types de decks adverses et cartes adverses qui reviennent dans tes défaites."""
    plans = {}
    for c in combats:
        if not (c["win"] or c["loss"]):
            continue
        _, plan = plan_adverse(c["adv"])
        e = plans.setdefault(plan, [0, 0])
        e[0] += 1
        e[1] += c["win"]
    mauvais = sorted(((p, g, w) for p, (g, w) in plans.items() if g >= MIN_ARCHETYPE and w / g <= 0.34),
                     key=lambda x: (x[2] / x[1], -x[1]))
    n = sum(1 for c in combats if c["win"] or c["loss"])
    base = sum(c["win"] for c in combats) / n if n else 0
    cartes = {}
    for c in combats:
        if not (c["win"] or c["loss"]):
            continue
        for x in c["adv"]:
            e = cartes.setdefault(x["id"], {"nom": x.get("name", "?"), "g": 0, "d": 0})
            e["g"] += 1
            e["d"] += c["loss"]
    cartes_noires = sorted((e for e in cartes.values()
                            if e["g"] >= MIN_CARTE_ADVERSE and e["d"] / e["g"] >= 0.75 and e["d"] / e["g"] >= (1 - base) + 0.25),
                           key=lambda e: (-e["d"] / e["g"], -e["g"]))[:3]
    return plans, mauvais, cartes_noires


def elixir(combats):
    v = [c["fuite"] for c in combats if c["fuite"] is not None and c["win"]]
    p = [c["fuite"] for c in combats if c["fuite"] is not None and c["loss"]]
    tout = [c["fuite"] for c in combats if c["fuite"] is not None]
    if len(tout) < 8:
        return None
    return {"moy": sum(tout) / len(tout), "victoires": sum(v) / len(v) if v else None,
            "defaites": sum(p) / len(p) if p else None}


def moments(combats):
    tranches = {"nuit (0h-6h)": range(0, 6), "matin (6h-12h)": range(6, 12),
                "après-midi (12h-18h)": range(12, 18), "soir (18h-24h)": range(18, 24)}
    res = {}
    for nom, h in tranches.items():
        sel = [c for c in combats if (c["win"] or c["loss"]) and c["t"].astimezone(PARIS).hour in h]
        if len(sel) >= MIN_PAR_TRANCHE:
            res[nom] = (len(sel), sum(c["win"] for c in sel) / len(sel))
    if len(res) < 2:
        return None
    meilleur = max(res.items(), key=lambda x: x[1][1])
    pire = min(res.items(), key=lambda x: x[1][1])
    if meilleur[1][1] - pire[1][1] < 0.25:
        return None
    return meilleur, pire


def tilt(combats):
    """Taux de victoire du combat suivant, selon que le précédent a été gagné ou perdu (même session de jeu)."""
    apres_d, apres_v = [0, 0], [0, 0]
    for a, b in zip(combats, combats[1:]):
        if (b["t"] - a["t"]).total_seconds() > 30 * 60 or not (b["win"] or b["loss"]) or not (a["win"] or a["loss"]):
            continue
        cible = apres_d if a["loss"] else apres_v
        cible[0] += 1
        cible[1] += b["win"]
    if apres_d[0] < MIN_PAR_TRANCHE // 2 or apres_v[0] < MIN_PAR_TRANCHE:
        return None
    return apres_d, apres_v


def deck_principal(combats, mode):
    decks = {}
    for c in combats:
        if c["mode"] != mode:
            continue
        cle = tuple(sorted(x["id"] for x in c["mes"]))
        e = decks.setdefault(cle, {"cartes": c["mes"], "n": 0, "v": 0, "dernier": c["t"]})
        e["n"] += 1
        e["v"] += c["win"]
        e["dernier"] = max(e["dernier"], c["t"])
    return max(decks.values(), key=lambda e: (e["n"], e["dernier"])) if decks else None


def cartes_fortes_non_jouees(profil, jouees, stats, p0):
    res = []
    for cid, c in profil.items():
        s = stats.get(cid)
        if cid in jouees or not s or s["games"] < 3 * d.MIN_PARTIES_CARTE:
            continue
        niv = d.niveau_jeu(c)
        if niv >= 13 and s["wr"] - p0 >= 0.025:
            res.append((s["wr"] - p0, d.nom_fr(s["name"]), niv, s["wr"], cid))
    return sorted(res, reverse=True)[:4]


def deck_avec_carte(ids, evo, carte_id, stats, p0, profil):
    """Deck de départ où la carte conseillée prend la place de la carte la moins utile du même rôle.
    Renvoie (nouveau_deck, carte_sortante, note_avant, note_apres) ou None si elle ne s'intègre pas sans dégrader le deck."""
    cible = stats.get(carte_id)
    if not cible or carte_id in ids:
        return None
    avant = d.note_deck(ids, stats, p0, profil)
    meilleur = None
    for pos, i in enumerate(ids):
        s = stats.get(i)
        if evo[pos] or not s or d.role(s["name"]) != d.role(cible["name"]) or abs(s.get("elixir", 0) - cible.get("elixir", 0)) > 2:
            continue
        nouveau = list(ids)
        nouveau[pos] = carte_id
        note = d.note_deck(nouveau, stats, p0, profil)
        if meilleur is None or note > meilleur[3]:
            meilleur = (nouveau, i, avant, note)
    if meilleur is None or meilleur[3] < avant - 0.002:           # pas question de proposer un deck nettement moins bon
        return None
    return meilleur


def cartes_a_monter(deck, profil, stats, p0):
    res = []
    for x in deck["cartes"]:
        c = profil.get(x["id"])
        if not c:
            continue
        manque = 16 - d.niveau_jeu(c)
        s = stats.get(x["id"])
        if manque >= 2:
            bonus = (s["wr"] - p0) if s and s["games"] >= d.MIN_PARTIES_CARTE else 0
            res.append((manque + 20 * bonus, d.nom_fr(x.get("name", "?")), d.niveau_jeu(c)))
    return sorted(res, reverse=True)[:3]


# ========================
# 🔹 Construction de la réponse
# ========================
def construire(tag):
    """Renvoie (texte_simple, [embeds])."""
    profil_brut = d.api_get(f"/players/{d.enc(tag)}")
    if not profil_brut:
        return f"Je ne trouve pas le joueur {tag}. Vérifie le tag (lettres et chiffres, sans espace).", []
    combats = lire_combats(d.api_get(f"/players/{d.enc(tag)}/battlelog"))
    nom = profil_brut.get("name", tag)
    if len(combats) < MIN_COMBATS:
        return (f"{nom} : je n'ai trouvé que {len(combats)} combat{'s' if len(combats) > 1 else ''} récent{'s' if len(combats) > 1 else ''} en 1 contre 1 "
                f"(il m'en faut au moins {MIN_COMBATS}). L'historique ne garde que les 25 derniers combats : "
                "joue un peu puis relance la commande."), []
    profil = {c["id"]: c for c in profil_brut.get("cards") or []}
    b = bilan(combats)
    plans, mauvais, noires = betes_noires(combats)
    el = elixir(combats)
    mo = moments(combats)
    ti = tilt(combats)
    priorites = []

    # --- Bilan
    termines = b["v"] + b["l"]
    lignes = [f"**{b['v']}V – {b['l']}D** sur {b['n']} combats (`{pct(b['v'], termines)}` de victoires) · "
              f"3 couronnes : {b['trois']} gagnées, {b['subi']} subies"]
    if b["serie"] >= 3 and b["sens"] in ("V", "D"):
        lignes.append(("🔥 " if b["sens"] == "V" else "🥶 ") + f"Série en cours : {b['serie']} {'victoires' if b['sens'] == 'V' else 'défaites'} d'affilée")
    if b["trophees"] is not None:
        lignes.append(f"🏆 Trophées sur la période : `{b['trophees']:+d}`")
    noms_modes = {"classe": "Classé", "voie": "Voie des trophées", "gdc": "Guerre", "autre": "Autres"}
    detail = " · ".join(f"{noms_modes.get(m, m)} {w}/{g}" for m, (g, w) in sorted(b["par_mode"].items(), key=lambda x: -x[1][0]))
    lignes.append(f"-# Victoires / combats par mode : {detail}")
    sections = ["**📊 Bilan**\n" + "\n".join(lignes)]

    # --- Bêtes noires
    if mauvais or noires:
        txt = []
        for plan, g, w in mauvais[:2]:
            txt.append(f"• Contre les **{NOM_PLAN[plan]}** : {w}/{g} (`{pct(w, g)}`)")
            priorites.append(f"**{NOM_PLAN[plan].capitalize()}** : {CONSEIL_PLAN[plan]}")
        if noires:
            txt.append("• Cartes qui reviennent dans tes défaites : "
                       + ", ".join(f"**{d.nom_fr(e['nom'])}** (perdu {e['d']}/{e['g']})" for e in noires))
        sections.append("**🎯 Tes bêtes noires**\n" + "\n".join(txt))
    else:
        sections.append("**🎯 Tes bêtes noires**\nAucun type de deck ne te bat de façon répétée sur cet échantillon. 👍")

    # --- Élixir
    if el:
        txt = f"Élixir perdu en moyenne : `{el['moy']:.1f}` par combat"
        if el["victoires"] is not None and el["defaites"] is not None:
            txt += f" (victoires `{el['victoires']:.1f}` · défaites `{el['defaites']:.1f}`)"
        if el["moy"] >= 1.5 or (el["defaites"] is not None and el["victoires"] is not None and el["defaites"] - el["victoires"] >= 0.8):
            txt += "\n⚠️ Tu laisses ton élixir plein trop souvent, surtout quand tu perds."
            priorites.append("**Élixir** : pose une carte dès que tu approches des 10 : un élixir perdu est un échange offert à l'adversaire.")
        sections.append("**⚡ Gestion de l'élixir**\n" + txt)

    # --- Mental et horaires
    txt = []
    if ti:
        (g1, w1), (g2, w2) = ti
        txt.append(f"Après une défaite : `{pct(w1, g1)}` de victoires ({g1} combats) · après une victoire : `{pct(w2, g2)}` ({g2})")
        if w1 / g1 + 0.2 <= w2 / g2:
            txt.append("⚠️ Tu joues moins bien juste après une défaite.")
            priorites.append("**Après une défaite** : fais une pause de quelques minutes avant de relancer, ça rapporte plus que d'enchaîner.")
    if mo:
        (n1, (g1, p1)), (n2, (g2, p2)) = mo
        txt.append(f"Ton meilleur créneau : {n1} (`{100 * p1:.0f}%`, {g1} combats) · le moins bon : {n2} (`{100 * p2:.0f}%`, {g2})")
    if txt:
        sections.append("**🧠 Mental et horaires**\n" + "\n".join(txt))

    embed1 = {"title": f"🧠 Coach de {nom}", "color": 15105570,
              "description": ("\n\n".join(sections))[:4000],
              "footer": {"text": f"Basé sur tes {b['n']} derniers combats (limite de l'API) : indicatif, pas une vérité absolue"}}
    embeds = [embed1]

    # --- Deck principal (même moteur que le bot d'analyse de deck)
    modes_jeu = [m for m in ("classe", "voie") if b["par_mode"].get(m)]
    mode = max(modes_jeu, key=lambda m: b["par_mode"][m][0]) if modes_jeu else None
    stats, p0, dp = None, 0.5, None
    if mode:
        dp = deck_principal(combats, mode)
        ids = [x["id"] for x in dp["cartes"]]
        slots = [1 if (x.get("evolutionLevel") or 0) > 0 else 0 for x in dp["cartes"]]
        try:
            texte_deck, embed_deck = d.construire_reponse(mode, [(ids, slots, getattr(d, "TT_DEFAUT", 159000000))], tag, False)
        except Exception as e:                                       # l'analyse du deck ne doit pas bloquer le reste
            print(f"[Coach] analyse du deck impossible : {e}", file=sys.stderr)
            texte_deck, embed_deck = None, None
        if embed_deck:
            embed_deck = dict(embed_deck)
            embed_deck["title"] = f"🔎 Ton deck principal ({d.MODES[mode]['nom']}, {dp['n']} combats, {pct(dp['v'], dp['n'])} de victoires)"
            embed_deck.pop("footer", None)
            embeds.append(embed_deck)
        data, _ = d.donnees_du_mode(mode)
        if data:
            stats, p0, _ = d.stats_cartes(data)

    # --- Cartes
    if stats and profil:
        jouees = {x["id"] for c in combats if c["mode"] in ("classe", "voie") for x in c["mes"]}
        fortes = cartes_fortes_non_jouees(profil, jouees, stats, p0)
        montees = cartes_a_monter(dp, profil, stats, p0) if dp else []
        txt = []
        if montees:
            txt.append("**⬆️ À monter en priorité** (dans ton deck) : " + ", ".join(f"{n} (niv. {niv}/16)" for _, n, niv in montees))
            priorites.append(f"**Niveaux** : monte d'abord {montees[0][1]} (niv. {montees[0][2]}/16), c'est la carte de ton deck qui te coûte le plus en puissance.")
        if fortes:
            txt.append("**💎 Cartes fortes que tu possèdes sans les jouer** : "
                       + ", ".join(f"{n} (niv. {niv}/16, `{100 * wr:.1f}%`)" for _, n, niv, wr, _ in fortes))
            ids_dp = [x["id"] for x in dp["cartes"]] if dp else []
            evo_dp = [(x.get("evolutionLevel") or 0) > 0 for x in dp["cartes"]] if dp else []
            slots_dp = [1 if e else 0 for e in evo_dp]
            propose = None
            for _, nom_c, niv_c, wr_c, cid in fortes:
                r = deck_avec_carte(ids_dp, evo_dp, cid, stats, p0, profil) if dp else None
                if r:
                    propose = (nom_c, niv_c, r)
                    break
            if propose:
                nom_c, niv_c, (nouveau, sortante, av, ap) = propose
                lien = d.lien_deck(nouveau, slots_dp, getattr(d, "TT_DEFAUT", 159000000))
                priorites.append(
                    f"**Essaie {nom_c}** (niv. {niv_c}/16) : elle gagne plus que la moyenne chez les meilleurs joueurs et tu l'as déjà à un bon niveau.\n"
                    f"🔁 {d.nom_fr(stats[sortante]['name'])} → **{nom_c}** · estimé `≈{100 * av:.1f}%` → `≈{100 * ap:.1f}%` "
                    f"(à la place du changement proposé plus haut, pas en plus)\n"
                    f"[📥 Copier ce deck]({lien})")
            else:
                priorites.append(f"**Essaie** {fortes[0][1]} : elle gagne plus que la moyenne chez les meilleurs joueurs. "
                                 "Aucune carte de ton deck ne peut lui laisser sa place sans l'affaiblir : elle demande de revoir plus de cartes.")
        if txt:
            embeds.append({"title": "🃏 Tes cartes", "color": 15105570, "description": "\n\n".join(txt)[:4000]})

    # --- Plan d'action
    if priorites:
        embeds.append({"title": "🚀 Ton plan d'action", "color": 5763719,
                       "description": "\n\n".join(f"{i + 1}. {p}" for i, p in enumerate(priorites[:5]))[:4000],
                       "footer": {"text": "Relance !coach #TAG dans quelques jours pour voir ta progression"}})
    return None, embeds


# ========================
# 🔹 Discord
# ========================
def lire_tag(contenu):
    texte = d.sans_accents(contenu)
    m = re.fullmatch(r"(?:!coach\s+)?#([0-9a-z]{3,15})", texte.strip())
    if m:
        return "#" + m.group(1).upper(), True
    if texte.startswith("!coach"):
        return None, True
    return None, False


def repondre():
    manquants = [n for n, v in (("DISCORD_BOT_TOKEN", d.BOT_TOKEN), ("DISCORD_CHANNEL_ID", d.CHANNEL_ID), ("CR_API_KEY", d.API_KEY)) if not v]
    if manquants:
        print(f"[ERREUR] Variable(s) manquante(s) : {', '.join(manquants)}", file=sys.stderr)
        sys.exit(1)
    code, moi = d.discord("GET", "/users/@me")
    if code != 200 or not moi:
        print(f"[ERREUR] Jeton du bot refusé par Discord (code {code}).", file=sys.stderr)
        sys.exit(1)
    code, messages = d.discord("GET", f"/channels/{d.CHANNEL_ID}/messages?limit=50")
    if code != 200 or messages is None:
        print(f"[ERREUR] Impossible de lire le salon (code {code}).", file=sys.stderr)
        sys.exit(1)
    maintenant = d.maintenant_utc()
    traites = 0
    for m in sorted(messages, key=lambda x: int(x["id"])):
        auteur = m.get("author") or {}
        if auteur.get("bot") or auteur.get("id") == moi.get("id"):
            continue
        if any(r.get("me") for r in m.get("reactions") or []):
            continue
        tag, demande = lire_tag((m.get("content") or "").strip())
        if not demande:
            continue
        try:
            age = (maintenant - datetime.datetime.fromisoformat(m["timestamp"])).total_seconds() / 3600
        except (KeyError, ValueError):
            age = 0
        if age > d.AGE_MAX_DEMANDE_H:
            continue
        if traites >= MAX_DEMANDES:
            break
        traites += 1
        code, _ = d.discord("PUT", f"/channels/{d.CHANNEL_ID}/messages/{m['id']}/reactions/{d.COCHE}/@me")
        if code not in (200, 204):
            print(f"[ERREUR] Impossible d'ajouter une réaction (code {code}).", file=sys.stderr)
            continue
        corps = {"message_reference": {"message_id": m["id"], "fail_if_not_exists": False},
                 "allowed_mentions": {"parse": [], "replied_user": False}}
        if not tag:
            corps["content"] = "Écris `!coach #TAG` (ton tag est dans ton profil, sous ton nom) ou simplement `#TAG`."
        else:
            try:
                texte, embeds = construire(tag)
            except Exception as e:
                print(f"[ERREUR] Analyse impossible : {e}", file=sys.stderr)
                texte, embeds = "Désolé, l'analyse a échoué. Réessaie dans quelques minutes.", []
            if embeds:
                corps["embeds"] = embeds
            else:
                corps["content"] = texte
        # Discord limite à 6000 caractères d'embeds par message : un embed par message
        suite = []
        if corps.get("embeds"):
            suite = corps["embeds"][1:]
            corps["embeds"] = corps["embeds"][:1]
        code, _ = d.discord("POST", f"/channels/{d.CHANNEL_ID}/messages", json=corps)
        if code not in (200, 201):
            print(f"[ERREUR] Réponse non envoyée (code {code}).", file=sys.stderr)
            d.discord("DELETE", f"/channels/{d.CHANNEL_ID}/messages/{m['id']}/reactions/{d.COCHE}/@me")
            continue
        for emb in suite:
            time.sleep(1)
            c2, _ = d.discord("POST", f"/channels/{d.CHANNEL_ID}/messages",
                              json={"embeds": [emb], "allowed_mentions": {"parse": []}})
            if c2 not in (200, 201):
                print(f"[ERREUR] Suite de la réponse non envoyée (code {c2}).", file=sys.stderr)
        print(f"Demande {m['id']} traitée.")
    if not traites:
        print("Aucune nouvelle demande.")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "repondre":
        repondre()
    else:
        print("[ERREUR] Utilise : python Coach.py repondre", file=sys.stderr)
        sys.exit(1)