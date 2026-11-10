"""Coach personnel : « !coach #TAG » dans un salon dédié.

Lit le profil et les 25 derniers combats du joueur (limite de l'API) et répond avec :
bilan, bêtes noires (decks adverses qui te battent), gestion de l'élixir, moments de la journée,
effet des défaites (tilt), analyse de ton deck principal (même moteur que DeckBot), cartes fortes que tu
possèdes sans les jouer, cartes à monter en priorité, et un plan d'action.

Il réutilise DeckBot.py (même dépôt). Variables d'environnement :
  CR_API_KEY, DISCORD_BOT_TOKEN, DISCORD_CHANNEL_ID (= le salon du coach, pas celui de DeckBot)
Lancement : python Coach.py repondre
"""
import os
import re
import sys
import json
import math
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
# 🔹 Analyses supplémentaires
# ========================
def niveau_cartes(cartes):
    """Niveau moyen (échelle /16) des cartes d'un deck lu dans un combat."""
    niv = [c["level"] + 16 - c["maxLevel"] for c in cartes if c.get("level") is not None and c.get("maxLevel")]
    return sum(niv) / len(niv) if len(niv) == len(cartes) else None


def ecart_niveaux(combats):
    """Écart de niveau moyen (toi - adversaire) et résultats selon cet écart."""
    lignes = []
    for c in combats:
        if not (c["win"] or c["loss"]):
            continue
        a, b = niveau_cartes(c["mes"]), niveau_cartes(c["adv"])
        if a is not None and b is not None:
            lignes.append((a - b, c["win"]))
    if len(lignes) < 8:
        return None
    if all(abs(e) < 0.05 for e, _ in lignes):
        return {"egalises": True}
    groupes = {"sous": [0, 0], "egal": [0, 0], "sur": [0, 0]}
    for e, w in lignes:
        g = groupes["sous" if e <= -0.5 else ("sur" if e >= 0.5 else "egal")]
        g[0] += 1
        g[1] += w
    return {"egalises": False, "moy": sum(e for e, _ in lignes) / len(lignes), "groupes": groupes}


def facon_de_perdre(combats):
    defaites = [c for c in combats if c["loss"]]
    if len(defaites) < 4:
        return None
    de_peu = sum(1 for c in defaites if c["c2"] - c["c1"] == 1)
    nettes = sum(1 for c in defaites if c["c2"] - c["c1"] >= 2)
    sans_couronne = sum(1 for c in defaites if c["c1"] == 0)
    return {"n": len(defaites), "de_peu": de_peu, "nettes": nettes, "zero": sans_couronne}


def sessions(combats):
    """Numéro de chaque combat dans sa session de jeu (nouvelle session après 30 minutes sans jouer)."""
    res, pos, prec = [], 0, None
    for c in combats:
        if prec is None or (c["t"] - prec).total_seconds() > 30 * 60:
            pos = 0
        pos += 1
        prec = c["t"]
        res.append((pos, c))
    return res


def fatigue(combats):
    debut, fin = [0, 0], [0, 0]
    for pos, c in sessions(combats):
        if not (c["win"] or c["loss"]):
            continue
        cible = debut if pos <= 3 else (fin if pos >= 6 else None)
        if cible is not None:
            cible[0] += 1
            cible[1] += c["win"]
    if debut[0] < 5 or fin[0] < 5:
        return None
    return debut, fin


def elixir_moyen_cartes(cartes):
    v = [c["elixirCost"] for c in cartes if c.get("elixirCost") is not None]
    return sum(v) / len(v) if len(v) >= 7 else None


def vitesse_adverse(combats):
    """Résultats selon la vitesse du deck adverse (élixir moyen)."""
    seaux = {"rapides (≤ 3,2)": [0, 0], "moyens (3,3 à 3,9)": [0, 0], "lourds (≥ 4,0)": [0, 0]}
    for c in combats:
        if not (c["win"] or c["loss"]):
            continue
        m = elixir_moyen_cartes(c["adv"])
        if m is None:
            continue
        k = "rapides (≤ 3,2)" if m <= 3.2 else ("lourds (≥ 4,0)" if m >= 4.0 else "moyens (3,3 à 3,9)")
        seaux[k][0] += 1
        seaux[k][1] += c["win"]
    return {k: v for k, v in seaux.items() if v[0] >= 3}


def forme(profil_brut, b):
    v, d_ = profil_brut.get("wins"), profil_brut.get("losses")
    termines = b["v"] + b["l"]
    if not v or d_ is None or termines < 8 or v + d_ < 200:
        return None
    globale = v / (v + d_)
    recente = b["v"] / termines
    return globale, recente


def parcours_legendes(profil_brut, combats):
    cur = profil_brut.get("currentPathOfLegendSeasonResult") or {}
    meilleur = profil_brut.get("bestPathOfLegendSeasonResult") or {}
    gains = [c["trophees"] for c in combats if c["mode"] == "classe" and c["trophees"] is not None]
    if not cur and len(gains) < 6:
        return None
    return {"cur": cur, "meilleur": meilleur, "gains": gains}



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
    fa = fatigue(combats)
    priorites = []
    termines = b["v"] + b["l"]

    # ===== Embed 1 : bilan, forme, parcours =====
    lignes = [f"**{b['v']}V – {b['l']}D** sur {b['n']} combats (`{pct(b['v'], termines)}` de victoires) · "
              f"3 couronnes : {b['trois']} gagnées, {b['subi']} subies"]
    if b["serie"] >= 3 and b["sens"] in ("V", "D"):
        lignes.append(("🔥 " if b["sens"] == "V" else "🥶 ") + f"Série en cours : {b['serie']} {'victoires' if b['sens'] == 'V' else 'défaites'} d'affilée")
    if b["trophees"] is not None:
        lignes.append(f"🏆 Trophées sur la période : `{b['trophees']:+d}`")
    noms_modes = {"classe": "Classé", "voie": "Voie des trophées", "gdc": "Guerre", "autre": "Autres"}
    detail = " · ".join(f"{noms_modes.get(m, m)} {w}/{g}" for m, (g, w) in sorted(b["par_mode"].items(), key=lambda x: -x[1][0]))
    lignes.append(f"-# Victoires / combats par mode : {detail}")
    sections1 = ["**📊 Bilan**\n" + "\n".join(lignes)]

    fo = forme(profil_brut, b)
    if fo:
        glob, rec = fo
        txt = f"Ces derniers combats : `{100 * rec:.0f}%` de victoires · sur toute ta carrière : `{100 * glob:.0f}%`"
        if rec - glob >= 0.08:
            txt += "\n🔥 Tu es en forme : au-dessus de ta moyenne habituelle."
        elif glob - rec >= 0.08:
            txt += "\n📉 Tu es en dessous de ta moyenne habituelle : change peut-être une carte, ou fais une pause."
        sections1.append("**📈 Ta forme du moment**\n" + txt)

    pl = parcours_legendes(profil_brut, combats)
    if pl:
        txt = []
        cur, best, gains = pl["cur"], pl["meilleur"], pl["gains"]
        if cur:
            morceaux = []
            if cur.get("leagueNumber") is not None:
                morceaux.append(f"ligue {cur['leagueNumber']}")
            if cur.get("trophies") is not None:
                morceaux.append(f"{cur['trophies']} trophées")
            if cur.get("rank"):
                morceaux.append(f"rang mondial {cur['rank']}")
            if morceaux:
                txt.append("Cette saison : " + " · ".join(morceaux))
        if best and best.get("trophies") is not None and best.get("leagueNumber") is not None:
            txt.append(f"Ton meilleur résultat de saison : ligue {best['leagueNumber']}, {best['trophies']} trophées")
        if len(gains) >= 6:
            net = sum(gains)
            moy = net / len(gains)
            txt.append(f"Sur tes {len(gains)} derniers combats classés : `{net:+d}` trophées (`{moy:+.1f}` par combat). "
                       f"À ce rythme, 20 combats de plus = `{20 * moy:+.0f}`.")
        if txt:
            sections1.append("**🏆 Parcours des légendes**\n" + "\n".join(txt))
    embed1 = {"title": f"🧠 Coach de {nom}", "color": 15105570, "description": ("\n\n".join(sections1))[:4000],
              "footer": {"text": f"Basé sur tes {b['n']} derniers combats (limite de l'API) : indicatif, pas une vérité absolue"}}
    embeds = [embed1]

    # ===== Embed 2 : comment tu joues =====
    sections2 = []
    # niveaux
    en = ecart_niveaux(combats)
    if en:
        if en["egalises"]:
            sections2.append("**⚖️ Niveaux des cartes**\nLes niveaux étaient identiques dans tous tes combats (mode à niveaux égalisés) : "
                             "tes résultats ne dépendent pas de tes niveaux ici.")
        else:
            g = en["groupes"]
            noms_g = {"sous": "en dessous de l'adversaire", "egal": "à niveau égal", "sur": "au-dessus de l'adversaire"}
            lg = [f"• {noms_g[k]} : {v[1]}/{v[0]} (`{pct(v[1], v[0])}`)" for k, v in g.items() if v[0] >= 2]
            txt = f"Écart moyen avec tes adversaires : `{en['moy']:+.1f}` niveau\n" + "\n".join(lg)
            sous, egal_sur = g["sous"], [g["egal"][0] + g["sur"][0], g["egal"][1] + g["sur"][1]]
            if sous[0] >= 3 and egal_sur[0] >= 3 and sous[1] / sous[0] + 0.2 <= egal_sur[1] / egal_sur[0]:
                txt += "\n⚠️ Tu perds surtout quand tes cartes sont moins hautes que celles de l'adversaire."
                priorites.append("**Niveaux** : tes défaites viennent surtout des combats où tu es sous-niveau : monte tes cartes avant de changer de deck.")
            sections2.append("**⚖️ Niveaux des cartes**\n" + txt)
    # façon de perdre
    fp = facon_de_perdre(combats)
    if fp:
        txt = (f"Sur tes {fp['n']} défaites : {fp['de_peu']} de peu (1 couronne d'écart), {fp['nettes']} nettes (2 couronnes ou plus), "
               f"{fp['zero']} sans marquer de couronne")
        if fp["de_peu"] / fp["n"] >= 0.5:
            txt += "\n⚠️ La moitié de tes défaites se jouent à une couronne : ce sont des matchs gagnables."
            priorites.append("**Matchs serrés** : tu perds souvent d'une seule couronne. Garde un sort et un peu d'élixir pour la fin du combat, et ne lance pas de grosse attaque en toute fin.")
        elif fp["zero"] / fp["n"] >= 0.6:
            txt += "\n⚠️ Tu perds souvent sans avoir marqué : ton attaque manque de pression."
            priorites.append("**Attaque** : tu perds sans marquer. Mets de la pression sur la voie opposée quand l'adversaire pose sa carte principale, et garde une carte de dégâts pour la tour.")
        sections2.append("**🥊 Comment tu perds**\n" + txt)
    # bêtes noires
    if mauvais or noires:
        txt = []
        for plan, g, w in mauvais[:2]:
            txt.append(f"• Contre les **{NOM_PLAN[plan]}** : {w}/{g} (`{pct(w, g)}`)")
            priorites.append(f"**{NOM_PLAN[plan].capitalize()}** : {CONSEIL_PLAN[plan]}")
        if noires:
            txt.append("• Cartes qui reviennent dans tes défaites : "
                       + ", ".join(f"**{d.nom_fr(e['nom'])}** (perdu {e['d']}/{e['g']})" for e in noires))
        sections2.append("**🎯 Tes bêtes noires**\n" + "\n".join(txt))
    else:
        sections2.append("**🎯 Tes bêtes noires**\nAucun type de deck ne te bat de façon répétée sur cet échantillon. 👍")
    # vitesse des decks adverses
    va = vitesse_adverse(combats)
    if len(va) >= 2:
        txt = "\n".join(f"• Decks {k} : {w}/{g} (`{pct(w, g)}`)" for k, (g, w) in va.items())
        pire = min(va.items(), key=lambda x: x[1][1] / x[1][0])
        if pire[1][1] / pire[1][0] <= 0.34:
            txt += f"\n⚠️ Les decks {pire[0].split(' (')[0]} te posent le plus de problèmes."
            conseil = {"rapides": "contre un deck rapide, ne pose pas ta grosse carte en premier et garde de l'élixir pour défendre : ils veulent te faire dépenser pour t'attaquer ensuite.",
                       "moyens": "joue la défense en premier, puis contre-attaque avec les unités qui ont survécu.",
                       "lourds": "contre un deck lourd, ne laisse pas leur élixir se remplir : mets la pression pendant qu'ils investissent."}[pire[0].split(" (")[0]]
            priorites.append(f"**Decks {pire[0].split(' (')[0]}** : {conseil}")
        sections2.append("**🏎️ Vitesse des decks adverses**\n" + txt)
    # élixir
    if el:
        txt = f"Élixir perdu en moyenne : `{el['moy']:.1f}` par combat"
        if el["victoires"] is not None and el["defaites"] is not None:
            txt += f" (victoires `{el['victoires']:.1f}` · défaites `{el['defaites']:.1f}`)"
        if el["moy"] >= 1.5 or (el["defaites"] is not None and el["victoires"] is not None and el["defaites"] - el["victoires"] >= 0.8):
            txt += "\n⚠️ Tu laisses ton élixir plein trop souvent, surtout quand tu perds."
            priorites.append("**Élixir** : pose une carte dès que tu approches des 10 : un élixir perdu est un échange offert à l'adversaire.")
        sections2.append("**⚡ Gestion de l'élixir**\n" + txt)
    # mental, horaires, fatigue
    txt = []
    if ti:
        (g1, w1), (g2, w2) = ti
        txt.append(f"Après une défaite : `{pct(w1, g1)}` de victoires ({g1} combats) · après une victoire : `{pct(w2, g2)}` ({g2})")
        if w1 / g1 + 0.2 <= w2 / g2:
            txt.append("⚠️ Tu joues moins bien juste après une défaite.")
            priorites.append("**Après une défaite** : fais une pause de quelques minutes avant de relancer, ça rapporte plus que d'enchaîner.")
    if fa:
        (gd, wd), (gf, wf) = fa
        txt.append(f"Dans une session : combats 1 à 3 `{pct(wd, gd)}` ({gd}) · à partir du 6ᵉ `{pct(wf, gf)}` ({gf})")
        if wd / gd - wf / gf >= 0.2:
            txt.append("⚠️ Tu fatigues : tes résultats chutent quand tu enchaînes les combats.")
            priorites.append("**Fatigue** : arrête-toi après 5 combats d'affilée, ou fais une pause avant de continuer : tes résultats baissent nettement après le 6ᵉ.")
    if mo:
        (n1, (g1, p1)), (n2, (g2, p2)) = mo
        txt.append(f"Ton meilleur créneau : {n1} (`{100 * p1:.0f}%`, {g1} combats) · le moins bon : {n2} (`{100 * p2:.0f}%`, {g2})")
    if txt:
        sections2.append("**🧠 Mental, fatigue et horaires**\n" + "\n".join(txt))
    embeds.append({"title": "🔬 Comment tu joues", "color": 15105570, "description": ("\n\n".join(sections2))[:4000]})

    # ===== Embed 3 : deck principal (même moteur que le bot d'analyse de deck) =====
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

    # ===== Embed 4 : cartes et deck proche des meilleurs =====
    if stats and profil:
        sections4 = []
        jouees = {x["id"] for c in combats if c["mode"] in ("classe", "voie") for x in c["mes"]}
        fortes = cartes_fortes_non_jouees(profil, jouees, stats, p0)
        montees = cartes_a_monter(dp, profil, stats, p0) if dp else []
        if montees:
            sections4.append("**⬆️ À monter en priorité** (dans ton deck) : " + ", ".join(f"{n} (niv. {niv}/16)" for _, n, niv in montees))
            priorites.append(f"**Niveaux** : monte d'abord {montees[0][1]} (niv. {montees[0][2]}/16), c'est la carte de ton deck qui te coûte le plus en puissance.")
        ids_dp = [x["id"] for x in dp["cartes"]] if dp else []
        evo_dp = [(x.get("evolutionLevel") or 0) > 0 for x in dp["cartes"]] if dp else []
        slots_dp = [1 if e else 0 for e in evo_dp]
        if fortes:
            sections4.append("**💎 Cartes fortes que tu possèdes sans les jouer** : "
                             + ", ".join(f"{n} (niv. {niv}/16, `{100 * wr:.1f}%`)" for _, n, niv, wr, _ in fortes))
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
        if sections4:
            embeds.append({"title": "🃏 Tes cartes", "color": 15105570, "description": "\n\n".join(sections4)[:4000]})

    # ===== Embed 5 : plan d'action =====
    if priorites:
        embeds.append({"title": "🚀 Ton plan d'action", "color": 5763719,
                       "description": "\n\n".join(f"{i + 1}. {p}" for i, p in enumerate(priorites[:6]))[:4000],
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