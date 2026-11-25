"""Coach personnel : « !coach #TAG » dans un salon dédié.

Lit le profil et les 25 derniers combats du joueur (limite de l'API), les range dans un historique permanent
(historique/TAG.json : à chaque demande et deux fois par jour on ajoute les nouveaux combats, jusqu'à 300 par joueur),
puis répond avec : bilan, bêtes noires (types de decks adverses qui te battent), gestion de l'élixir, moments de la journée,
effet des défaites (tilt), fatigue, analyse de ton deck principal (même moteur que DeckBot), ton historique (tendance,
tes decks, tes matchups), cartes fortes que tu possèdes sans les jouer, cartes à monter en priorité, et un plan d'action
classé par impact. Une observation n'est annoncée que si l'échantillon est assez grand pour qu'elle ne soit pas du hasard.

Il réutilise DeckBot.py (même dépôt). Variables d'environnement :
  CR_API_KEY, DISCORD_BOT_TOKEN, DISCORD_CHANNEL_ID (= le salon du coach, pas celui de DeckBot)
Lancement : python Coach.py repondre      (répond aux demandes du salon)
            python Coach.py historique    (met à jour l'historique des joueurs déjà passés)
"""
import os
import re
import random
import sys
import json
import math
import time
import datetime
from concurrent.futures import ThreadPoolExecutor
from zoneinfo import ZoneInfo

import DeckBot as d

PARIS = ZoneInfo("Europe/Paris")
MIN_COMBATS = 8                   # en dessous, pas assez de combats récents pour conseiller
MIN_ARCHETYPE = 5                 # parties contre un même type de deck avant d'en parler
MIN_CARTE_ADVERSE = 5             # apparitions d'une carte adverse avant d'en parler
MIN_PAR_TRANCHE = 8               # combats minimum par tranche horaire / situation
MAX_DEMANDES = 3                  # demandes traitées par passage (chaque analyse fait des appels à l'API)
Z_TENDANCE = 1.2                  # à partir de là (≈ 88 % de certitude) on signale une tendance, sans en faire une priorité
Z_MIN = 1.64                      # à partir de là (≈ 95 %) l'observation est jugée solide et peut entrer dans le plan d'action
MIN_HISTORIQUE = 40               # combats en mémoire pour afficher la section « Ton historique »

# Historique permanent
DOSSIER_HISTO = "historique"
MAX_COMBATS_HISTO = 300
MAX_FICHIERS_HISTO = 80
EXPIRATION_HISTO_JOURS = 120
CODES_MODE = {"classe": "c", "voie": "v", "gdc": "g", "autre": "a"}
MODE_DU_CODE = {v: k for k, v in CODES_MODE.items()}

# Plan de jeu d'un deck adverse : chaque carte donne des points aux plans qu'elle sert ; le plan qui en a le plus l'emporte
POIDS_PLANS = {
    "Lava Hound": {"air": 3, "tank": 1}, "Balloon": {"air": 3},
    "Flying Machine": {"air": 0.5}, "Minion Horde": {"air": 0.5}, "Skeleton Dragons": {"air": 0.5}, "Phoenix": {"air": 0.5},
    "Golem": {"tank": 3}, "Elixir Golem": {"tank": 2}, "Electro Giant": {"tank": 3}, "Goblin Giant": {"tank": 3},
    "Royal Giant": {"tank": 2.5}, "Giant": {"tank": 2.5},
    "X-Bow": {"siege": 3.5}, "Mortar": {"siege": 3.5},
    "Graveyard": {"cycle": 2.5}, "Hog Rider": {"cycle": 3}, "Royal Hogs": {"cycle": 2.5}, "Ram Rider": {"cycle": 2.5},
    "Battle Ram": {"cycle": 2.5}, "Miner": {"cycle": 2}, "Goblin Barrel": {"cycle": 1.5}, "Skeleton Barrel": {"cycle": 1.5},
    "P.E.K.K.A": {"lourd": 2.5}, "Mega Knight": {"lourd": 2.5}, "Sparky": {"lourd": 3},
}
NOM_PLAN = {"air": "decks aériens", "tank": "decks à gros tank", "siege": "decks de siège",
            "cycle": "decks rapides (cycle)", "lourd": "decks lourds", "autre": "autres decks"}
GROS_DEGATS = {"P.E.K.K.A", "Mini P.E.K.K.A", "Inferno Tower", "Inferno Dragon", "Executioner", "Sparky", "Prince", "Dark Prince",
               "Lightning", "Rocket", "Fireball", "Poison"}
RNG = random.Random()


def v(*options):
    """Une formulation au hasard : les conseils ne sont pas toujours les mêmes mots."""
    return RNG.choice(options)


TUEURS_TANK = {"P.E.K.K.A", "Mini P.E.K.K.A", "Inferno Tower", "Inferno Dragon", "Hunter", "Prince", "Sparky", "Mighty Miner", "Executioner"}
CARTES_RAPIDES = {"Hog Rider", "Battle Ram", "Miner", "Ram Rider", "Royal Hogs", "Goblin Barrel", "Skeleton Barrel", "Goblin Drill"}


def traits_deck(cartes):
    """Ce que le deck du joueur contient vraiment (pour ne pas lui conseiller d'utiliser ce qu'il n'a pas)."""
    noms = {c.get("name") for c in cartes or []}
    return {"batiment": bool(noms & d.BATIMENTS), "sort": bool(noms & d.SORTS), "degats": bool(noms & GROS_DEGATS),
            "anti_air": sum(1 for n in noms if n in d.ANTI_AIR), "connu": bool(noms),
            "zone_air": bool(noms & d.ZONE_AIR), "cible_air": bool(noms & d.CIBLE_AIR),
            "tueur_tank": bool(noms & TUEURS_TANK), "rapide": bool(noms & CARTES_RAPIDES)}


def manque_de_reponse(plan, t):
    """Ce qui manque réellement au deck du joueur pour répondre à ce type de deck adverse (texte), ou None s'il a de quoi répondre."""
    if not t["connu"]:
        return None
    if plan == "air":
        if t["anti_air"] < 2:
            return "ton deck a peu de réponses aériennes : contre Ballon et Meute de lave, c'est ton vrai point faible. Ajoute une carte qui touche les airs."
        if not t["cible_air"]:
            return "tu n'as pas de dégâts ciblés contre un gros air (Ballon, Meute de lave) : ajoute une Tour infernale, un Mousquetaire ou un Chasseur."
        if not t["zone_air"]:
            return "tu n'as pas de dégâts de zone contre les airs : les nuées aériennes (Horde de serviteurs, Bébé dragon) vont te poser problème."
    if plan in ("tank", "lourd") and not t["tueur_tank"]:
        return "ton deck n'a pas de vrai tueur de tank (Tour infernale, Mini P.E.K.K.A, Chasseur…) : c'est ton vrai point faible ici."
    if plan == "siege" and not (t["sort"] or t["rapide"]):
        return "ton deck n'a ni sort ni carte rapide pour détruire un siège : ajoutes-en une."
    return None


def conseil_plan(plan, deck=None):
    """Conseil contre un type de deck adverse. Si on connaît le deck du joueur, on vérifie d'abord qu'il a de quoi répondre :
    sinon le conseil dit ce qui manque, plutôt que de supposer des cartes qu'il n'a pas."""
    t = traits_deck(deck)
    manque = manque_de_reponse(plan, t)
    if manque:
        return manque + " En attendant, " + v("contre-attaque sur l'autre voie dès qu'il investit.", "ne défends pas à perte : punis-le sur l'autre voie.")
    if plan == "air":
        reserve = [x for x, ok in (("ton sort", t["sort"] or not t["connu"]), ("ton bâtiment", t["batiment"] or not t["connu"])) if ok]
        r = " et ".join(reserve) if reserve else "tes cartes anti-air"
        return v(f"garde toujours de quoi défendre dans les airs et ne le gaspille pas en attaque ; {r} doit rester dispo pour Ballon / Meute de lave.",
                 f"réserve ta réponse aérienne pour la défense, et vérifie que {r} est prêt quand le Ballon ou la Meute de lave arrive.")
    if plan == "tank":
        return v("punis le tank : attaque l'autre voie dès qu'il le pose, et réserve ton meilleur dégât pur pour le tuer au pont.",
                 "dès que le tank est posé, contre-attaque sur l'autre voie ; garde ton plus gros dégât pour l'arrêter au pont.")
    if plan == "siege":
        outil = "un sort ou une carte rapide" if t["sort"] or not t["connu"] else "une carte rapide"
        return v(f"ne laisse pas le siège s'installer : mets la pression dès qu'il le pose et garde {outil} pour le détruire.",
                 f"empêche le siège de se poser tranquille : attaque-le tout de suite et garde {outil} pour le détruire.")
    if plan == "cycle":
        return v("garde ton élixir pour défendre et fais des échanges positifs : évite de poser en avance, sinon tu te fais cycler.",
                 "face au cycle, ne pose pas en avance : défends avec peu d'élixir et ne rends que des échanges positifs.")
    if plan == "lourd":
        outil = "un bâtiment et des troupes à petits coûts" if t["batiment"] or not t["connu"] else "des troupes à petits coûts"
        return v(f"ne t'engage pas en défense avec des unités fragiles : use de {outil} pour tenir.",
                 f"contre un deck lourd, tiens avec {outil} plutôt qu'avec des unités fragiles.")
    return v("regarde quelle carte revient dans tes défaites et prépare-lui une réponse précise.",
             "repère la carte qui revient dans tes défaites et garde-lui une réponse précise.")


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


# ========================
# 🔹 Historique permanent (au-delà des 25 combats de l'API)
# ========================
def chemin_histo(tag):
    return os.path.join(d.DOSSIER, DOSSIER_HISTO, tag.lstrip("#").upper() + ".json")


def _carte_txt(c):
    f = {"n": 0, "e": 1, "h": 2}[d.forme_carte(c)]
    return f"{c['id']}.{c.get('level', 0)}.{c.get('maxLevel', 0)}.{f}"


def compacter(c, table):
    """Un combat sous forme de liste courte ; `table` retient le nom et le coût de chaque carte vue."""
    for x in c["mes"] + c["adv"]:
        table[str(x["id"])] = [x.get("name", "?"), x.get("elixirCost") or 0]
    fuite = c["fuite"]
    return [c["t"].strftime("%Y%m%dT%H%M%S"), CODES_MODE.get(c["mode"], "a"), c["c1"], c["c2"], c["trophees"],
            round(fuite, 1) if isinstance(fuite, (int, float)) else None,
            ",".join(_carte_txt(x) for x in c["mes"]), ",".join(_carte_txt(x) for x in c["adv"])]


def _cartes_depuis_txt(txt, table):
    res = []
    for bloc in txt.split(","):
        i, niv, mx, f = (int(x) for x in bloc.split("."))
        nom, el = table.get(str(i), ["?", 0])
        res.append({"id": i, "name": nom, "level": niv, "maxLevel": mx, "elixirCost": el,
                    "evolutionLevel": 1 if f == 1 else 0, "forme": f})
    return res


def decompacter(row, table):
    t, m, c1, c2, tr, fuite, mes, adv = row
    return {"t": datetime.datetime.strptime(t, "%Y%m%dT%H%M%S").replace(tzinfo=datetime.timezone.utc),
            "mode": MODE_DU_CODE.get(m, "autre"), "win": c1 > c2, "loss": c1 < c2, "c1": c1, "c2": c2,
            "trophees": tr, "fuite": fuite, "mes": _cartes_depuis_txt(mes, table), "adv": _cartes_depuis_txt(adv, table)}


def charger_histo(tag):
    try:
        with open(chemin_histo(tag), "r", encoding="utf-8") as f:
            data = json.load(f)
        data.setdefault("cartes", {})
        data.setdefault("combats", [])
        return data
    except (OSError, ValueError):
        return {"tag": tag.upper(), "nom": "", "maj": "", "cartes": {}, "combats": []}


def sauver_histo(tag, data):
    chemin = chemin_histo(tag)
    os.makedirs(os.path.dirname(chemin), exist_ok=True)
    tmp = chemin + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
    os.replace(tmp, chemin)


def maj_histo(tag, nom, combats):
    """Ajoute les combats lus dans l'API à l'historique du joueur (doublons écartés), garde les 300 derniers.
    Renvoie (tous_les_combats_décompactés, nombre_de_nouveaux)."""
    data = charger_histo(tag)
    connus = {r[0] for r in data["combats"]}
    nouveaux = 0
    for c in combats:
        cle = c["t"].strftime("%Y%m%dT%H%M%S")
        if cle in connus:
            continue
        connus.add(cle)
        data["combats"].append(compacter(c, data["cartes"]))
        nouveaux += 1
    data["combats"].sort(key=lambda r: r[0])
    data["combats"] = data["combats"][-MAX_COMBATS_HISTO:]
    if nouveaux or nom != data.get("nom"):
        data["nom"] = nom
        data["maj"] = d.maintenant_utc().isoformat()
        data["tag"] = tag.upper()
        try:
            sauver_histo(tag, data)
        except OSError as e:
            print(f"[Coach] historique non enregistré : {e}", file=sys.stderr)
    utilises = {x for r in data["combats"] for x in (r[6] + "," + r[7]).split(",")}
    ids = {int(x.split(".")[0]) for x in utilises}
    table = {k: val for k, val in data["cartes"].items() if int(k) in ids}
    return [decompacter(r, table) for r in data["combats"]], nouveaux


def nettoyer_histo():
    """Supprime les fichiers d'historique abandonnés (120 jours) et garde au plus 80 joueurs (les plus récents)."""
    dossier = os.path.join(d.DOSSIER, DOSSIER_HISTO)
    if not os.path.isdir(dossier):
        return
    limite = d.maintenant_utc() - datetime.timedelta(days=EXPIRATION_HISTO_JOURS)
    fichiers = []
    for nom in os.listdir(dossier):
        if not nom.endswith(".json"):
            continue
        chemin = os.path.join(dossier, nom)
        try:
            with open(chemin, "r", encoding="utf-8") as f:
                maj = datetime.datetime.fromisoformat(json.load(f).get("maj") or "1970-01-01T00:00:00+00:00")
        except (OSError, ValueError):
            maj = datetime.datetime.fromtimestamp(0, datetime.timezone.utc)
        if maj < limite:
            os.remove(chemin)
        else:
            fichiers.append((maj, chemin))
    for _, chemin in sorted(fichiers, reverse=True)[MAX_FICHIERS_HISTO:]:
        os.remove(chemin)


def rafraichir_historique():
    """Relit le journal de chaque joueur déjà passé et ajoute ses nouveaux combats (lancé deux fois par jour)."""
    if not d.API_KEY:
        print("[ERREUR] Variable manquante : CR_API_KEY", file=sys.stderr)
        sys.exit(1)
    dossier = os.path.join(d.DOSSIER, DOSSIER_HISTO)
    if not os.path.isdir(dossier):
        print("Aucun historique à mettre à jour.")
        return
    tags = []
    for nom in sorted(os.listdir(dossier)):
        if nom.endswith(".json"):
            tags.append("#" + nom[:-5])

    def lire(tag):
        return tag, d.api_get(f"/players/{d.enc(tag)}/battlelog")

    with ThreadPoolExecutor(max_workers=5) as ex:
        logs = list(ex.map(lire, tags))
    total = 0
    for tag, brut in logs:
        if brut is None:
            continue
        _, n = maj_histo(tag, charger_histo(tag).get("nom", ""), lire_combats(brut))
        total += n
    nettoyer_histo()
    print(f"Historique : {len(tags)} joueurs lus, {total} nouveaux combats")


# ========================
# 🔹 Statistiques
# ========================
def z_ecart(g1, w1, g2, w2):
    """Écart (en erreurs-types) entre deux taux de victoire : positif si le premier est meilleur. Sous ≈ 1,2, c'est probablement du hasard."""
    if g1 <= 0 or g2 <= 0:
        return 0.0
    p = (w1 + w2) / (g1 + g2)
    se = math.sqrt(p * (1 - p) * (1 / g1 + 1 / g2))
    return (w1 / g1 - w2 / g2) / se if se > 0 else 0.0


def tendance(z):
    """« (tendance) » quand l'écart est net mais pas encore solide."""
    return " *(tendance, à confirmer)*" if z < Z_MIN else ""


def plan_adverse(cartes):
    """Plan de jeu d'un deck adverse par points : chaque carte sert un ou plusieurs plans, la carte de victoire la plus chère
    compte double, un élixir moyen très bas ou très haut oriente vers le cycle ou le lourd. Renvoie (carte_principale, plan)."""
    score, principale, cout_max = {}, None, -1
    for c in cartes:
        nom = c.get("name")
        for plan, pts in POIDS_PLANS.get(nom, {}).items():
            score[plan] = score.get(plan, 0) + pts
        if nom in d.CARTES_VICTOIRE and (c.get("elixirCost") or 0) > cout_max:
            cout_max, principale = c.get("elixirCost") or 0, nom
    if principale and POIDS_PLANS.get(principale):
        meilleur = max(POIDS_PLANS[principale].items(), key=lambda x: x[1])[0]
        score[meilleur] = score.get(meilleur, 0) + 1
    moy = elixir_moyen_cartes(cartes)
    if moy is not None:
        if moy <= 3.3:
            score["cycle"] = score.get("cycle", 0) + 1
        elif moy >= 4.2:
            score["lourd"] = score.get("lourd", 0) + 1
            score["tank"] = score.get("tank", 0) + 0.5
    if not score or max(score.values()) < 2:
        return principale, "autre"
    return principale, max(score.items(), key=lambda x: (x[1], x[0]))[0]


def pct(a, b):
    return f"{100 * a / b:.0f}%" if b else "–"


# ========================
# 🔹 Analyses
# ========================
def bilan(combats):
    n = len(combats)
    nb_v = sum(c["win"] for c in combats)
    nb_l = sum(c["loss"] for c in combats)
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
    # trophées : une échelle par mode, on ne les additionne jamais entre eux
    trophees = {}
    for c in combats:
        if c["trophees"] is not None and c["mode"] in ("classe", "voie"):
            trophees[c["mode"]] = trophees.get(c["mode"], 0) + c["trophees"]
    return {"n": n, "v": nb_v, "l": nb_l, "trois": trois, "subi": subi, "serie": serie, "sens": sens,
            "par_mode": par_mode, "trophees": trophees}


def betes_noires(combats):
    """Types de decks adverses et cartes adverses qui reviennent dans tes défaites (seulement si l'écart dépasse le hasard)."""
    termines = [c for c in combats if c["win"] or c["loss"]]
    n, vict = len(termines), sum(c["win"] for c in termines)
    base = vict / n if n else 0
    plans = {}
    for c in termines:
        _, plan = plan_adverse(c["adv"])
        e = plans.setdefault(plan, [0, 0])
        e[0] += 1
        e[1] += c["win"]
    mauvais = []
    for p, (g, w) in plans.items():
        if g < MIN_ARCHETYPE or n - g < MIN_ARCHETYPE:
            continue
        autres = (vict - w) / (n - g)
        z = z_ecart(n - g, vict - w, g, w)
        if w / g <= autres - 0.15 and z >= Z_TENDANCE:
            mauvais.append((p, g, w, z))
    mauvais.sort(key=lambda x: (x[2] / x[1], -x[1]))
    cartes = {}
    for c in termines:
        for x in c["adv"]:
            e = cartes.setdefault(x["id"], {"nom": x.get("name", "?"), "g": 0, "d": 0})
            e["g"] += 1
            e["d"] += c["loss"]
    cartes_noires = sorted((e for e in cartes.values()
                            if e["g"] >= MIN_CARTE_ADVERSE and e["d"] / e["g"] >= 0.70 and e["d"] / e["g"] >= (1 - base) + 0.20),
                           key=lambda e: (-e["d"] / e["g"], -e["g"]))[:3]
    return plans, [(p, g, w) for p, g, w, _ in mauvais], cartes_noires, {p: z for p, g, w, z in mauvais}, base


MIN_PLAN_PAR_DECK = 5             # parties d'UN deck contre un type adverse avant d'en parler
MIN_DECK_TOTAL = 12               # combats terminés avec un deck avant d'analyser ses résultats à part


def cle_deck(c):
    return tuple(sorted(x["id"] for x in c["mes"]))


def noms_decks(decks):
    """Un nom court par deck (sa carte de victoire, sinon sa première carte) ; numéroté si deux decks ont la même."""
    noms, vus = {}, {}
    for cle, e in decks.items():
        cartes = [x.get("name", "?") for x in e["cartes"]]
        base = next((n for n in cartes if n in d.CARTES_VICTOIRE), cartes[0] if cartes else "?")
        vus[base] = vus.get(base, 0) + 1
        noms[cle] = d.nom_fr(base) + (f" ({vus[base]})" if vus[base] > 1 else "")
    return noms


def resultats_par_deck(combats):
    """Pour chacun de TES decks : combats terminés, victoires, et résultats contre chaque type de deck adverse."""
    decks = {}
    for c in combats:
        if not (c["win"] or c["loss"]) or not c["mes"]:
            continue
        e = decks.setdefault(cle_deck(c), {"cartes": c["mes"], "n": 0, "v": 0, "plans": {}})
        e["n"] += 1
        e["v"] += c["win"]
        p = e["plans"].setdefault(plan_adverse(c["adv"])[1], [0, 0])
        p[0] += 1
        p[1] += c["win"]
    return decks


def lecture_plan_par_deck(decks, plan):
    """Contre un type de deck adverse, est-ce un problème de TON deck précis ou de tous tes decks ?
    Renvoie (statut, détail) : « un_deck » (un deck concentre le problème, les autres s'en sortent), « tous » (aucun de tes decks n'y arrive),
    ou « inconnu » (un seul deck testé, ou trop peu de parties pour savoir)."""
    lignes = [(cle, e["plans"][plan][0], e["plans"][plan][1]) for cle, e in decks.items() if plan in e["plans"]]
    sérieux = [x for x in lignes if x[1] >= MIN_PLAN_PAR_DECK]
    if len(sérieux) < 2:
        return "inconnu", None
    meilleur_cas = None
    for cle, g, w in sérieux:
        autres_g = sum(x[1] for x in lignes if x[0] != cle)
        autres_w = sum(x[2] for x in lignes if x[0] != cle)
        if autres_g < MIN_PLAN_PAR_DECK:
            continue
        z = z_ecart(autres_g, autres_w, g, w)
        if w / g <= autres_w / autres_g - 0.15 and z >= Z_TENDANCE and (meilleur_cas is None or z > meilleur_cas[0]):
            meilleur_cas = (z, cle, g, w, autres_g, autres_w)
    if meilleur_cas:
        return "un_deck", meilleur_cas
    if all(w / g <= 0.45 for _, g, w in sérieux):
        return "tous", sérieux
    return "inconnu", None


def betes_noires_propres_a_un_deck(decks, deja):
    """Problèmes qu'un seul de tes decks rencontre et que la moyenne de tous tes combats cache : (cle_deck, plan, g, w, z)."""
    res = []
    for cle, e in decks.items():
        if e["n"] < MIN_DECK_TOTAL:
            continue
        for plan, (g, w) in e["plans"].items():
            if plan in deja or plan == "autre" or g < MIN_PLAN_PAR_DECK or e["n"] - g < MIN_PLAN_PAR_DECK:
                continue
            autres_g, autres_w = e["n"] - g, e["v"] - w
            z = z_ecart(autres_g, autres_w, g, w)
            if w / g <= autres_w / autres_g - 0.20 and z >= Z_MIN:
                res.append((cle, plan, g, w, z))
    res.sort(key=lambda x: -x[4])
    return res[:2]


def elixir(combats):
    vic = [c["fuite"] for c in combats if c["fuite"] is not None and c["win"]]
    per = [c["fuite"] for c in combats if c["fuite"] is not None and c["loss"]]
    tout = [c["fuite"] for c in combats if c["fuite"] is not None]
    if len(tout) < 8:
        return None
    return {"moy": sum(tout) / len(tout), "victoires": sum(vic) / len(vic) if vic else None,
            "defaites": sum(per) / len(per) if per else None, "n": len(tout)}


def moments(combats):
    """Renvoie (statut, données) : « ok » avec (meilleur, pire) si l'écart est net et dépasse le hasard,
    « neutre » s'il n'y a pas de différence nette, « manque » s'il n'y a pas assez de combats par créneau."""
    tranches = {"nuit (0h-6h)": range(0, 6), "matin (6h-12h)": range(6, 12),
                "après-midi (12h-18h)": range(12, 18), "soir (18h-24h)": range(18, 24)}
    res = {}
    for nom, h in tranches.items():
        sel = [c for c in combats if (c["win"] or c["loss"]) and c["t"].astimezone(PARIS).hour in h]
        if len(sel) >= MIN_PAR_TRANCHE:
            res[nom] = (len(sel), sum(c["win"] for c in sel))
    if len(res) < 2:
        return "manque", None
    meilleur = max(res.items(), key=lambda x: x[1][1] / x[1][0])
    pire = min(res.items(), key=lambda x: x[1][1] / x[1][0])
    ecart = meilleur[1][1] / meilleur[1][0] - pire[1][1] / pire[1][0]
    z = z_ecart(meilleur[1][0], meilleur[1][1], pire[1][0], pire[1][1])
    if ecart < 0.20 or z < Z_TENDANCE:
        return "neutre", None
    return "ok", (meilleur, pire, z)


def tilt(combats):
    """Résultat du combat suivant selon que le précédent a été perdu ou gagné (même session, même mode)."""
    apres_d, apres_v = [0, 0], [0, 0]
    for a, b in zip(combats, combats[1:]):
        if (b["t"] - a["t"]).total_seconds() > 30 * 60 or a["mode"] != b["mode"] \
                or not (b["win"] or b["loss"]) or not (a["win"] or a["loss"]):
            continue
        cible = apres_d if a["loss"] else apres_v
        cible[0] += 1
        cible[1] += b["win"]
    if apres_d[0] < 5 or apres_v[0] < 8:
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


def cartes_fortes_non_jouees(profil, jouees, stats, p0, noms_deck=None):
    """Cartes que tu as bien montées et qui gagnent plus que la moyenne, jamais jouées. Si on connaît ton deck,
    seules celles qui peuvent y prendre la place d'une carte du même genre sont proposées."""
    res = []
    for cid, c in profil.items():
        s = stats.get(cid)
        if cid in jouees or not s or s["games"] < 3 * d.MIN_PARTIES_CARTE:
            continue
        if noms_deck and not any(d.roles_compatibles(s["name"], n) for n in noms_deck):
            continue
        niv = d.niveau_jeu(c)
        if niv >= 13 and s["wr"] - p0 >= 0.025:
            res.append((s["wr"] - p0, d.nom_fr(s["name"]), niv, s["wr"], cid))
    return sorted(res, reverse=True)[:4]


def deck_avec_carte(ids, evo, carte_id, stats, p0, profil):
    """Deck de départ où la carte conseillée trouve sa place.
    1) elle prend la place d'une carte du même genre ; 2) sinon elle entre à une place libre et une seconde carte est ajustée.
    Renvoie (nouveau_deck, [(sortante, entrante)], note_avant, note_apres) ou None si rien n'est possible sans dégrader le deck."""
    cible = stats.get(carte_id)
    if not cible or carte_id in ids:
        return None
    avant = d.note_deck(ids, stats, p0, profil)
    meilleur = None
    for pos, i in enumerate(ids):
        if not d.remplacement_possible(carte_id, i, stats):
            continue
        nouveau = list(ids)
        nouveau[pos] = carte_id
        if not d.coherent_apres_changement(ids, nouveau, stats):
            continue
        reelle = d.note_deck(nouveau, stats, p0, profil)
        note = reelle - (d.EVO_PERTE if evo[pos] else 0.0)
        if meilleur is None or note > meilleur[0]:
            meilleur = (note, nouveau, [(i, carte_id)], reelle)
    if meilleur is None or meilleur[0] < avant - 0.002:
        # pas d'échange direct : elle entre à une place libre (écart d'élixir ≤ 2) et on ajuste une autre carte du deck
        meilleur = None
        pool = {i for i, c in (profil or {}).items() if i not in ids and i != carte_id and d.manque(c) <= d.MAX_NIVEAUX_MANQUANTS
                and i in stats and stats[i]["games"] >= d.MIN_PARTIES_CARTE}
        for pos, i in enumerate(ids):
            if i not in stats or abs((stats[i].get("elixir") or 0) - (cible.get("elixir") or 0)) > 2:
                continue
            base = list(ids)
            base[pos] = carte_id
            for pos2, j in enumerate(base):
                if pos2 == pos or j not in stats:
                    continue
                for e in pool:
                    if not d.remplacement_possible(e, j, stats):
                        continue
                    nouveau = list(base)
                    nouveau[pos2] = e
                    if not d.coherent_apres_changement(ids, nouveau, stats):
                        continue
                    reelle = d.note_deck(nouveau, stats, p0, profil)
                    note = reelle - (d.EVO_PERTE if evo[pos] else 0.0) - (d.EVO_PERTE if evo[pos2] else 0.0)
                    if meilleur is None or note > meilleur[0]:
                        meilleur = (note, nouveau, [(i, carte_id), (j, e)], reelle)
    if meilleur is None or meilleur[0] < avant - 0.002:
        return None                                                 # pas question de proposer un deck nettement moins bon
    return meilleur[1], meilleur[2], avant, meilleur[3]


def cartes_a_monter(deck, profil, stats, p0):
    res = []
    for x in deck["cartes"]:
        c = profil.get(x["id"])
        if not c:
            continue
        retard = d.manque(c)
        s = stats.get(x["id"])
        if retard >= 2:
            bonus = (s["wr"] - p0) if s and s["games"] >= d.MIN_PARTIES_CARTE else 0
            res.append((retard + 20 * bonus, d.nom_fr(x.get("name", "?")), d.niveau_jeu(c), retard))
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
    if debut[0] < 6 or fin[0] < 6:
        return None
    return debut, fin


def elixir_moyen_cartes(cartes):
    vals = [c["elixirCost"] for c in cartes if c.get("elixirCost") is not None]
    return sum(vals) / len(vals) if len(vals) >= 7 else None


def vitesse_adverse(combats):
    """Résultats selon la vitesse du deck adverse (élixir moyen) ; il faut 5 parties par catégorie."""
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
    return {k: val for k, val in seaux.items() if val[0] >= 5}


def vitesse_pire(va):
    """La catégorie de vitesse qui te pose vraiment problème (nettement sous les autres, au-delà du hasard), ou None."""
    if len(va) < 2:
        return None
    for nom, (g, w) in sorted(va.items(), key=lambda x: x[1][1] / x[1][0]):
        autres_g = sum(x[0] for k, x in va.items() if k != nom)
        autres_w = sum(x[1] for k, x in va.items() if k != nom)
        z = z_ecart(autres_g, autres_w, g, w)
        if w / g <= autres_w / autres_g - 0.15 and z >= Z_TENDANCE:
            return nom, g, w, z
        break
    return None


def forme(profil_brut, b):
    gagnees, perdues = profil_brut.get("wins"), profil_brut.get("losses")
    termines = b["v"] + b["l"]
    if not gagnees or perdues is None or termines < 12 or gagnees + perdues < 200:
        return None
    globale = gagnees / (gagnees + perdues)
    recente = b["v"] / termines
    z = z_ecart(termines, b["v"], gagnees + perdues, gagnees)
    return globale, recente, z


def parcours_legendes(profil_brut, combats):
    cur = profil_brut.get("currentPathOfLegendSeasonResult") or {}
    meilleur = profil_brut.get("bestPathOfLegendSeasonResult") or {}
    gains = [c["trophees"] for c in combats if c["mode"] == "classe" and c["trophees"] is not None]
    if not cur and len(gains) < 6:
        return None
    return {"cur": cur, "meilleur": meilleur, "gains": gains}


def analyse_historique(tous):
    """Lignes de la section « Ton historique » (decks, cartes, matchups, élixir du deck), ou [] s'il n'y a rien de net à dire."""
    termines = [c for c in tous if c["win"] or c["loss"]]
    n = len(termines)
    if n < MIN_HISTORIQUE:
        return []
    vict = sum(c["win"] for c in termines)
    depuis = termines[0]["t"].astimezone(PARIS).strftime("%d/%m")
    fen = []
    for k in (5, 10, 25):
        if n > k:
            sel = termines[-k:]
            fen.append(f"{k} derniers `{pct(sum(c['win'] for c in sel), k)}`")
    lignes = [f"{n} combats gardés depuis le {depuis} : `{pct(vict, n)}` de victoires · " + " · ".join(fen + [f"tous `{pct(vict, n)}`"])]
    # trophées sur tout l'historique
    gains = {}
    for c in termines:
        if c["trophees"] is not None and c["mode"] in ("classe", "voie"):
            e = gains.setdefault(c["mode"], [0, 0])
            e[0] += 1
            e[1] += c["trophees"]
    noms = {"classe": "Classé", "voie": "Voie des trophées"}
    morceaux = [f"{noms[m]} `{net:+d}` sur {g} combats" for m, (g, net) in gains.items() if g >= 10]
    if morceaux:
        lignes.append("🏆 Trophées : " + " · ".join(morceaux))
    # tes decks
    decks = {}
    for c in termines:
        cle = tuple(sorted(x["id"] for x in c["mes"]))
        e = decks.setdefault(cle, {"cartes": c["mes"], "g": 0, "w": 0})
        e["g"] += 1
        e["w"] += c["win"]
    frequents = sorted((e for e in decks.values() if e["g"] >= 10), key=lambda e: -e["g"])[:3]
    if len(frequents) >= 2:
        morceaux = []
        for e in frequents:
            arch = d.archetype([(x.get("name", "?"), x.get("elixirCost")) for x in e["cartes"]])
            nom_deck = d.nom_fr(arch) if arch != "Autre" else d.nom_fr(e["cartes"][0].get("name", "?")) + "…"
            morceaux.append(f"{nom_deck} `{pct(e['w'], e['g'])}` ({e['g']})")
        lignes.append("🃏 Tes decks : " + " · ".join(morceaux))
    # cartes : meilleure et moins bonne (seulement si tu changes de deck assez pour comparer)
    par_carte = {}
    for c in termines:
        for x in c["mes"]:
            e = par_carte.setdefault(x["id"], {"nom": x.get("name", "?"), "g": 0, "w": 0})
            e["g"] += 1
            e["w"] += c["win"]
    notes = []
    for e in par_carte.values():
        reste_g, reste_w = n - e["g"], vict - e["w"]
        if e["g"] >= 20 and reste_g >= 20:
            z = z_ecart(e["g"], e["w"], reste_g, reste_w)
            notes.append((z, e))
    if notes:
        haut, bas = max(notes, key=lambda x: x[0]), min(notes, key=lambda x: x[0])
        morceaux = []
        if haut[0] >= Z_MIN and haut[1]["w"] / haut[1]["g"] - (vict - haut[1]["w"]) / (n - haut[1]["g"]) >= 0.10:
            morceaux.append(f"✅ {d.nom_fr(haut[1]['nom'])} `{pct(haut[1]['w'], haut[1]['g'])}` ({haut[1]['g']})")
        if bas[0] <= -Z_MIN and (vict - bas[1]["w"]) / (n - bas[1]["g"]) - bas[1]["w"] / bas[1]["g"] >= 0.10:
            morceaux.append(f"⚠️ {d.nom_fr(bas[1]['nom'])} `{pct(bas[1]['w'], bas[1]['g'])}` ({bas[1]['g']})")
        if morceaux:
            lignes.append("🎴 Quand tu les joues : " + " · ".join(morceaux))
    # matchups par type de deck adverse
    plans = {}
    for c in termines:
        _, plan = plan_adverse(c["adv"])
        e = plans.setdefault(plan, [0, 0])
        e[0] += 1
        e[1] += c["win"]
    morceaux = []
    for plan, (g, w) in sorted(plans.items(), key=lambda x: -x[1][0])[:4]:
        if g < 8 or plan == "autre":
            continue
        autres_g, autres_w = n - g, vict - w
        marque = ""
        if autres_g >= 8:
            z = z_ecart(g, w, autres_g, autres_w)
            if z >= Z_MIN and w / g >= autres_w / autres_g + 0.12:
                marque = "✅ "
            elif z <= -Z_MIN and w / g <= autres_w / autres_g - 0.12:
                marque = "⚠️ "
        morceaux.append(f"{marque}{NOM_PLAN[plan]} {w}/{g}")
    if morceaux:
        lignes.append("⚔️ Matchups : " + " · ".join(morceaux))
    # résultats selon l'élixir moyen de ton deck
    seaux = {"decks rapides (≤ 3,2)": [0, 0], "decks moyens": [0, 0], "decks lourds (≥ 4,0)": [0, 0]}
    for c in termines:
        m = elixir_moyen_cartes(c["mes"])
        if m is None:
            continue
        k = "decks rapides (≤ 3,2)" if m <= 3.2 else ("decks lourds (≥ 4,0)" if m >= 4.0 else "decks moyens")
        seaux[k][0] += 1
        seaux[k][1] += c["win"]
    valides = {k: x for k, x in seaux.items() if x[0] >= 15}
    if len(valides) >= 2:
        meilleur = max(valides.items(), key=lambda x: x[1][1] / x[1][0])
        pire = min(valides.items(), key=lambda x: x[1][1] / x[1][0])
        z = z_ecart(meilleur[1][0], meilleur[1][1], pire[1][0], pire[1][1])
        if z >= Z_TENDANCE and meilleur[1][1] / meilleur[1][0] - pire[1][1] / pire[1][0] >= 0.12:
            lignes.append(f"⚡ Tu gagnes plus avec des {meilleur[0]} (`{pct(meilleur[1][1], meilleur[1][0])}`) "
                          f"qu'avec des {pire[0]} (`{pct(pire[1][1], pire[1][0])}`){tendance(z)}")
    return lignes


# ========================
# 🔹 Construction de la réponse
# ========================
class Priorites:
    """Plan d'action : chaque conseil porte une estimation de ce que le problème coûte en winrate (impact) et le nombre de
    combats derrière (fiabilité). Le classement final suit impact × fiabilité ; les conseils « Niveaux » sont fusionnés."""

    def __init__(self):
        self.liste = []

    def ajouter(self, cle, texte, impact, n, solide=True):
        """Ajoute un conseil au plan d'action, seulement si l'observation est solide (écart au-delà du hasard, Z_MIN)."""
        if not solide:
            return
        for e in self.liste:
            if e["cle"] == cle and cle == "niveaux":
                e["texte"] += "\n↳ " + texte.split(" : ", 1)[-1]
                e["impact"] = max(e["impact"], impact)
                e["n"] = max(e["n"], n)
                return
        self.liste.append({"cle": cle, "texte": texte, "impact": impact, "n": n})

    def classes(self, maxi=6):
        return [e["texte"] for e in sorted(self.liste, key=lambda e: -(e["impact"] * min(1.0, e["n"] / 12)))[:maxi]]


def regrouper(embeds, limite=5800):
    """Regroupe les embeds en messages : Discord accepte 10 embeds et 6000 caractères au total par message."""
    messages, courant, taille = [], [], 0
    for e in embeds:
        t = len(e.get("title", "")) + len(e.get("description", "")) + len((e.get("footer") or {}).get("text", ""))
        if courant and (taille + t > limite or len(courant) >= 10):
            messages.append(courant)
            courant, taille = [], 0
        courant.append(e)
        taille += t
    if courant:
        messages.append(courant)
    return messages


def construire(tag):
    """Renvoie (texte_simple, [embeds])."""
    profil_brut = d.api_get(f"/players/{d.enc(tag)}")
    if not profil_brut:
        return f"Je ne trouve pas le joueur {tag}. Vérifie le tag (lettres et chiffres, sans espace).", []
    nom = profil_brut.get("name", tag)
    recents = lire_combats(d.api_get(f"/players/{d.enc(tag)}/battlelog"))
    try:
        tous, _ = maj_histo(tag, nom, recents)
    except Exception as e:                                           # l'historique ne doit jamais bloquer le coaching
        print(f"[Coach] historique indisponible : {e}", file=sys.stderr)
        tous = recents
    if len(tous) < len(recents):
        tous = recents
    if len(tous) < MIN_COMBATS:
        return (f"{nom} : je n'ai trouvé que {len(tous)} combat{'s' if len(tous) > 1 else ''} récent{'s' if len(tous) > 1 else ''} en 1 contre 1 "
                f"(il m'en faut au moins {MIN_COMBATS}). L'historique de l'API ne garde que les 25 derniers combats : "
                "joue un peu puis relance la commande."), []
    combats = recents if len(recents) >= MIN_COMBATS else tous         # « derniers combats » = ceux que l'API a gardés
    profil = {c["id"]: c for c in profil_brut.get("cards") or []}
    b = bilan(combats)
    plans, mauvais, noires, z_plans, base_tous = betes_noires(tous)
    el = elixir(tous)
    statut_mo, mo = moments(tous)
    ti = tilt(tous)
    fa = fatigue(tous)
    prio = Priorites()
    termines = b["v"] + b["l"]
    termines_tous = sum(1 for c in tous if c["win"] or c["loss"])
    taux_def = 1 - base_tous

    # ===== Embed 1 : bilan, forme, parcours =====
    lignes = [f"**{b['v']}V – {b['l']}D** sur {b['n']} combats (`{pct(b['v'], termines)}` de victoires) · "
              f"3 couronnes : {b['trois']} gagnées, {b['subi']} subies"]
    if b["serie"] >= 3 and b["sens"] in ("V", "D"):
        lignes.append(("🔥 " if b["sens"] == "V" else "🥶 ") + v(f"Série en cours : {b['serie']} {'victoires' if b['sens'] == 'V' else 'défaites'} d'affilée",
                                                                  f"En ce moment : {b['serie']} {'victoires' if b['sens'] == 'V' else 'défaites'} de suite"))
    noms_modes = {"classe": "Classé", "voie": "Voie des trophées"}
    if b["trophees"]:
        lignes.append("🏆 Trophées sur la période : " + " · ".join(f"{noms_modes[m]} `{val:+d}`" for m, val in b["trophees"].items()))
    noms_modes = {"classe": "Classé", "voie": "Voie des trophées", "gdc": "Guerre", "autre": "Autres"}
    detail = " · ".join(f"{noms_modes.get(m, m)} {w}/{g}" for m, (g, w) in sorted(b["par_mode"].items(), key=lambda x: -x[1][0]))
    lignes.append(f"-# Victoires / combats par mode : {detail}")
    sections1 = ["**📊 Bilan**\n" + "\n".join(lignes)]

    fo = forme(profil_brut, b)
    if fo:
        glob, rec, z_f = fo
        txt = f"Ces derniers combats : `{100 * rec:.0f}%` de victoires (sur {b['v'] + b['l']} combats) · sur toute ta carrière : `{100 * glob:.0f}%`"
        if rec - glob >= 0.10 and z_f >= Z_TENDANCE:
            txt += "\n🔥 " + v("Tu es en forme : au-dessus de ta moyenne habituelle.", "Bonne passe : tu fais mieux que d'habitude.", "Tu joues au-dessus de ton niveau moyen en ce moment.") + tendance(z_f)
        elif glob - rec >= 0.10 and -z_f >= Z_TENDANCE:
            txt += "\n📉 " + v("Tu es en dessous de ta moyenne habituelle : change peut-être une carte, ou fais une pause.", "Passage à vide : tu fais moins bien que d'habitude. Une pause peut aider.", "Tes résultats sont sous ta moyenne : ajuste ton deck ou souffle un peu.") + tendance(-z_f)
        sections1.append("**📈 Ta forme du moment**\n" + txt)

    pl = parcours_legendes(profil_brut, tous)
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
    memoire = f" · {len(tous)} combats en mémoire pour les tendances" if len(tous) > len(recents) else ""
    embed1 = {"title": f"🧠 Coach de {nom}", "color": 15105570, "description": d.assembler(sections1),
              "footer": {"text": f"Bilan sur tes {b['n']} derniers combats{memoire} · indicatif, pas une vérité absolue"}}
    embeds = [embed1]

    # ===== Deck principal (lu avant l'analyse : les conseils s'y adaptent) =====
    modes_jeu = [m for m in ("classe", "voie") if b["par_mode"].get(m)]
    mode = max(modes_jeu, key=lambda m: b["par_mode"][m][0]) if modes_jeu else None
    dp = deck_principal(combats, mode) if mode else None
    cartes_deck = dp["cartes"] if dp else None

    # ===== Embed 2 : comment tu joues =====
    sections2 = []
    en = ecart_niveaux(tous)
    niveaux_sous = False
    if en:
        if en["egalises"]:
            sections2.append("**⚖️ Niveaux des cartes**\nLes niveaux étaient identiques dans tous tes combats (mode à niveaux égalisés) : "
                             "tes résultats ne dépendent pas de tes niveaux ici.")
        else:
            g = en["groupes"]
            noms_g = {"sous": "en dessous de l'adversaire", "egal": "à niveau égal", "sur": "au-dessus de l'adversaire"}
            lg = [f"• {noms_g[k]} : {x[1]}/{x[0]} (`{pct(x[1], x[0])}`)" for k, x in g.items() if x[0] >= 2]
            txt = f"Écart moyen avec tes adversaires : `{en['moy']:+.1f}` niveau\n" + "\n".join(lg)
            sous, egal_sur = g["sous"], [g["egal"][0] + g["sur"][0], g["egal"][1] + g["sur"][1]]
            if sous[0] >= 4 and egal_sur[0] >= 4:
                z_n = z_ecart(egal_sur[0], egal_sur[1], sous[0], sous[1])
                ecart_n = egal_sur[1] / egal_sur[0] - sous[1] / sous[0]
                if ecart_n >= 0.20 and z_n >= Z_TENDANCE:
                    niveaux_sous = True
                    txt += "\n⚠️ " + v("Tu perds surtout quand tes cartes sont moins hautes que celles de l'adversaire.", "Tes défaites tombent surtout quand tu es sous-niveau.", "Le niveau pèse : tu gagnes nettement moins quand l'adversaire est plus haut.") + tendance(z_n)
                    prio.ajouter("niveaux", "**Niveaux** : " + v("tes défaites viennent surtout des combats où tu es sous-niveau : monte tes cartes avant de changer de deck.", "avant de toucher à ton deck, monte tes cartes : c'est là que tu perds des points.", "tes cartes sont trop basses face à certains adversaires : le niveau avant le deck."),
                                 ecart_n * sous[0] / (sous[0] + egal_sur[0]), sous[0] + egal_sur[0], solide=z_n >= Z_MIN)
            sections2.append("**⚖️ Niveaux des cartes**\n" + txt)
    fp = facon_de_perdre(tous)
    if fp:
        txt = (f"Sur tes {fp['n']} défaites : {fp['de_peu']} de peu (1 couronne d'écart), {fp['nettes']} nettes (2 couronnes ou plus), "
               f"{fp['zero']} sans marquer de couronne")
        part_def = fp["n"] / termines_tous if termines_tous else 0
        if fp["de_peu"] / fp["n"] >= 0.5:
            txt += "\n⚠️ " + v("La moitié de tes défaites se jouent à une couronne : ce sont des matchs gagnables.", "Beaucoup de défaites à une seule couronne : tu étais tout près.", "Tu perds souvent de justesse : ces matchs étaient à ta portée.")
            prio.ajouter("serres", "**Matchs serrés** : " + v("tu perds souvent d'une seule couronne. Garde un sort et un peu d'élixir pour la fin du combat, et ne lance pas de grosse attaque en toute fin.", "garde un sort et de l'élixir pour les dernières secondes ; évite de tout lancer à la fin.", "dans les dernières minutes, joue prudent : un sort en réserve vaut souvent la couronne qui manque."),
                         part_def * fp["de_peu"] / fp["n"] * 0.3, fp["n"] * 2)
        elif fp["zero"] / fp["n"] >= 0.6:
            txt += "\n⚠️ " + v("Tu perds souvent sans avoir marqué : ton attaque manque de pression.", "Beaucoup de défaites sans couronne : il faut plus de pression.", "Tu repars souvent sans avoir touché de tour : attaque plus.")
            suite = " Ton niveau en dessous de l'adversaire explique sans doute une partie de ça." if niveaux_sous else ""
            prio.ajouter("attaque", "**Attaque** : " + v("tu perds sans marquer. Mets de la pression sur la voie opposée quand l'adversaire pose sa carte principale, et garde une carte de dégâts pour la tour.", "quand l'adversaire dépense sa carte principale, attaque l'autre voie et garde un dégât pour la tour.", "force l'adversaire à défendre : lance une attaque sur la voie opposée dès qu'il investit.") + suite,
                         part_def * fp["zero"] / fp["n"] * 0.2, fp["n"] * 2)
        sections2.append("**🥊 Comment tu perds**\n" + txt)
    par_deck = resultats_par_deck(tous)
    noms_d = noms_decks(par_deck)
    propres = betes_noires_propres_a_un_deck(par_deck, {p for p, _, _ in mauvais})
    if mauvais or noires or propres:
        txt = []
        for plan, g, w in mauvais[:2]:
            statut, det = lecture_plan_par_deck(par_deck, plan)
            cartes_conseil = cartes_deck
            ligne = f"• Contre les **{NOM_PLAN[plan]}** : {w}/{g} (`{pct(w, g)}`){tendance(z_plans.get(plan, 0))}"
            if statut == "un_deck":
                z_u, cle_u, g_u, w_u, ag, aw = det
                ligne += (f"\n   ↳ C'est surtout **ton deck {noms_d[cle_u]}** : {w_u}/{g_u} (`{pct(w_u, g_u)}`), "
                          f"alors que tes autres decks font {aw}/{ag} (`{pct(aw, ag)}`)")
                cartes_conseil = par_deck[cle_u]["cartes"]
            elif statut == "tous":
                ligne += "\n   ↳ Quel que soit le deck que tu joues : le problème n'est pas une carte en particulier"
            txt.append(ligne)
            base_autres = (sum(1 for c in tous if c["win"]) - w) / max(1, termines_tous - g)
            texte_conseil = conseil_plan(plan, cartes_conseil)
            if statut == "un_deck":
                texte_conseil = f"avec ton deck {noms_d[cle_u]} : " + texte_conseil + " Ou joue plutôt tes autres decks contre ce type d'adversaire."
            prio.ajouter("plan-" + plan, f"**{NOM_PLAN[plan].capitalize()}** : {texte_conseil}",
                         max(0.0, base_autres - w / g) * g / termines_tous, g, solide=z_plans.get(plan, 0) >= Z_MIN)
        for cle_u, plan, g_u, w_u, z_u in propres:
            ag, aw = par_deck[cle_u]["n"] - g_u, par_deck[cle_u]["v"] - w_u
            txt.append(f"• Avec **ton deck {noms_d[cle_u]}** seulement : contre les **{NOM_PLAN[plan]}**, {w_u}/{g_u} (`{pct(w_u, g_u)}`) "
                       f"contre {aw}/{ag} (`{pct(aw, ag)}`) face aux autres types")
            prio.ajouter("plan-deck-" + plan, f"**{NOM_PLAN[plan].capitalize()}, avec {noms_d[cle_u]}** : {conseil_plan(plan, par_deck[cle_u]['cartes'])}",
                         max(0.0, aw / ag - w_u / g_u) * g_u / termines_tous, g_u, solide=True)
        if noires:
            txt.append("• Cartes qui reviennent dans tes défaites : "
                       + ", ".join(f"**{d.nom_fr(e['nom'])}** (perdu {e['d']}/{e['g']})" for e in noires))
        sections2.append("**🎯 Tes bêtes noires**\n" + "\n".join(txt))
    else:
        sections2.append("**🎯 Tes bêtes noires**\n" + v("Aucun type de deck ne te bat de façon répétée sur cet échantillon. 👍", "Pas de deck qui te pose problème de façon répétée ici. 👍", "Rien de récurrent dans tes défaites sur cet échantillon. 👍"))
    va = vitesse_adverse(tous)
    if len(va) >= 2:
        txt = "\n".join(f"• Decks {k} : {w}/{g} (`{pct(w, g)}`)" for k, (g, w) in va.items())
        pire = vitesse_pire(va)
        if pire:
            nom_v, g_v, w_v, z_v = pire
            court = nom_v.split(" (")[0]
            txt += "\n⚠️ " + v(f"Les decks {court} te posent le plus de problèmes.", f"Ton point faible : les decks {court}.", f"Tu souffles surtout contre les decks {court}.") + tendance(z_v)
            deja = {"rapides": {"plan-cycle"}, "lourds": {"plan-lourd", "plan-tank"}, "moyens": set()}[court]
            if not any(e["cle"] in deja for e in prio.liste):          # pas deux conseils pour le même problème
                conseil = v(*{"rapides": ("contre un deck rapide, ne pose pas ta grosse carte en premier et garde de l'élixir pour défendre : ils veulent te faire dépenser pour t'attaquer ensuite.",
                                           "face à un deck rapide, défends d'abord avec peu d'élixir : ne pose pas ta grosse carte en premier."),
                              "moyens": ("joue la défense en premier, puis contre-attaque avec les unités qui ont survécu.",
                                         "défends d'abord, et contre-attaque avec ce qui reste de ta défense."),
                              "lourds": ("contre un deck lourd, ne laisse pas leur élixir se remplir : mets la pression pendant qu'ils investissent.",
                                         "ne laisse pas un deck lourd poser tranquillement : attaque pendant qu'il dépense.")}[court])
                autres_v = (sum(x[1] for k, x in va.items() if k != nom_v)) / max(1, sum(x[0] for k, x in va.items() if k != nom_v))
                prio.ajouter("vitesse", f"**Decks {court}** : {conseil}", max(0.0, autres_v - w_v / g_v) * g_v / termines_tous, g_v, solide=z_v >= Z_MIN)
        sections2.append("**🏎️ Vitesse des decks adverses**\n" + txt)
    if el:
        txt = f"Élixir perdu en moyenne : `{el['moy']:.1f}` par combat"
        if el["victoires"] is not None and el["defaites"] is not None:
            txt += f" (victoires `{el['victoires']:.1f}` · défaites `{el['defaites']:.1f}`)"
        if el["moy"] >= 1.5 or (el["defaites"] is not None and el["victoires"] is not None and el["defaites"] - el["victoires"] >= 0.8):
            txt += "\n⚠️ " + v("Tu laisses ton élixir plein trop souvent, surtout quand tu perds.", "Ton élixir déborde trop souvent, surtout dans tes défaites.", "Tu gaspilles de l'élixir en laissant la jauge pleine, surtout quand tu perds.")
            prio.ajouter("elixir", "**Élixir** : " + v("pose une carte dès que tu approches des 10 : un élixir perdu est un échange offert à l'adversaire.", "ne reste pas à 10 : joue une petite carte plutôt que de laisser déborder.", "une jauge pleine, c'est de l'élixir perdu : pose quelque chose avant d'y arriver."),
                         0.03 + min(0.03, max(0.0, el["moy"] - 1.5) * 0.02), el["n"])
        txt += f"\n-# Mesuré sur {el['n']} combats ; le jeu ne donne pas la durée d'un combat, un combat long et un combat court pèsent donc pareil."
        sections2.append("**⚡ Gestion de l'élixir**\n" + txt)
    txt = []
    if ti:
        (g1, w1), (g2, w2) = ti
        txt.append(f"Après une défaite : `{pct(w1, g1)}` de victoires ({g1} combats) · après une victoire : `{pct(w2, g2)}` ({g2})")
        z_t = z_ecart(g2, w2, g1, w1)
        if w2 / g2 - w1 / g1 >= 0.15 and z_t >= Z_TENDANCE:
            txt.append("⚠️ " + v("Tu joues moins bien juste après une défaite.", "Une défaite te déstabilise : tu rejoues moins bien juste après.", "Tes combats après une défaite sont plus faibles.") + tendance(z_t))
            prio.ajouter("tilt", "**Après une défaite** : " + v("fais une pause de quelques minutes avant de relancer, ça rapporte plus que d'enchaîner.", "respire cinq minutes avant le combat suivant : enchaîner à chaud te coûte.", "ne relance pas tout de suite : une courte pause améliore le combat suivant."),
                         (w2 / g2 - w1 / g1) * taux_def, g1 + g2, solide=z_t >= Z_MIN)
    if fa:
        (gd, wd), (gf, wf) = fa
        txt.append(f"Dans une session : combats 1 à 3 `{pct(wd, gd)}` ({gd}) · à partir du 6ᵉ `{pct(wf, gf)}` ({gf})")
        z_fa = z_ecart(gd, wd, gf, wf)
        if wd / gd - wf / gf >= 0.15 and z_fa >= Z_TENDANCE:
            txt.append("⚠️ " + v("Tu fatigues : tes résultats chutent quand tu enchaînes les combats.", "Plus tu enchaînes, moins tu gagnes.", "La fatigue se voit : tes résultats baissent en fin de session.") + tendance(z_fa))
            prio.ajouter("fatigue", "**Fatigue** : " + v("arrête-toi après 5 combats d'affilée, ou fais une pause avant de continuer : tes résultats baissent nettement après le 6ᵉ.", "limite tes sessions à 5 combats : ça baisse nettement à partir du 6ᵉ.", "fais une vraie pause au bout de 5 combats : au-delà, tu perds plus."),
                         (wd / gd - wf / gf) * gf / (gd + gf), gd + gf, solide=z_fa >= Z_MIN)
    if statut_mo == "ok":
        (n1, (g1, w1)), (n2, (g2, w2)), z_m = mo
        txt.append(f"Ton meilleur créneau : {n1} (`{pct(w1, g1)}`, {g1} combats) · le moins bon : {n2} (`{pct(w2, g2)}`, {g2}){tendance(z_m)}")
    elif statut_mo == "neutre":
        txt.append("-# Horaires : pas de créneau nettement meilleur que les autres sur cet échantillon.")
    else:
        txt.append("-# Horaires : pas assez de combats par créneau (il en faut 8) pour conclure.")
    if txt:
        sections2.append("**🧠 Mental, fatigue et horaires**\n" + "\n".join(txt))
    sections2.append("-# Lecture indicative : ce sont des écarts constatés sur tes combats récents (nombres entre parenthèses = combats concernés), pas des certitudes. "
                     "Seuls les écarts nets (au-delà du hasard) entrent dans le plan d'action.")
    embeds.append({"title": "🔬 Comment tu joues", "color": 15105570, "description": d.assembler(sections2)})

    # ===== Embed 3 : ton historique =====
    histo = analyse_historique(tous)
    if histo:
        embeds.append({"title": "📚 Ton historique", "color": 15105570, "description": d.assembler(["\n".join(histo)])})

    # ===== Embed 4 : deck principal (même moteur que le bot d'analyse de deck) =====
    stats, p0 = None, 0.5
    if mode and dp:
        ids = [x["id"] for x in dp["cartes"]]
        slots = [1 if (x.get("evolutionLevel") or 0) > 0 else 0 for x in dp["cartes"]]
        titre_deck = f"🔎 Ton deck principal ({d.MODES[mode]['nom']}, {dp['n']} combats, {pct(dp['v'], dp['n'])} de victoires)"
        try:
            texte_deck, embed_deck = d.construire_reponse(mode, [(ids, slots, getattr(d, "TT_DEFAUT", 159000000))], tag, False)
        except Exception as e:                                       # l'analyse du deck ne doit pas bloquer le reste
            print(f"[Coach] analyse du deck impossible : {e}", file=sys.stderr)
            texte_deck, embed_deck = "L'analyse de ton deck n'a pas pu être faite cette fois-ci (le reste du rapport n'en dépend pas). Réessaie dans quelques minutes.", None
        if embed_deck:
            embed_deck = dict(embed_deck)
            embed_deck["title"] = titre_deck
            embed_deck.pop("footer", None)
            embeds.append(embed_deck)
        elif texte_deck:
            embeds.append({"title": titre_deck, "color": 3447003, "description": texte_deck})
        try:
            data, _ = d.donnees_du_mode(mode)
            if data:
                stats, p0, _ = d.stats_cartes(data)
        except Exception as e:
            print(f"[Coach] données du mode indisponibles : {e}", file=sys.stderr)

    # ===== Embed 5 : cartes et deck proche des meilleurs =====
    if stats and profil:
        sections4 = []
        jouees = {x["id"] for c in tous if c["mode"] in ("classe", "voie") for x in c["mes"]}
        noms_deck = [x.get("name", "") for x in cartes_deck] if cartes_deck else None
        fortes = cartes_fortes_non_jouees(profil, jouees, stats, p0, noms_deck)
        montees = cartes_a_monter(dp, profil, stats, p0) if dp else []
        if montees:
            sections4.append("**⬆️ À monter en priorité** (dans ton deck) : " + ", ".join(f"{n} (niv. {niv}/16)" for _, n, niv, _ in montees))
            prio.ajouter("niveaux", "**Niveaux** : " + v(f"monte d'abord {montees[0][1]} (niv. {montees[0][2]}/16), c'est la carte de ton deck qui te coûte le plus en puissance.", f"commence par {montees[0][1]} (niv. {montees[0][2]}/16) : c'est ta carte la plus en retard.", f"{montees[0][1]} (niv. {montees[0][2]}/16) est ta priorité : le plus gros gain de puissance."),
                         min(0.04, 0.006 * montees[0][3]), 20)
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
                nom_c, niv_c, (nouveau, changes, av, ap) = propose
                lien, _ = d.version_et_lien(nouveau, mode, profil, stats, {i: slots_dp[p] for p, i in enumerate(ids_dp)}, getattr(d, "TT_DEFAUT", 159000000))
                echanges = "\n".join(f"🔁 {d.nom_fr(stats[s]['name'])} → **{d.nom_fr(stats[e]['name'])}**" for s, e in changes)
                prio.ajouter("carte-forte",
                             f"**Essaie {nom_c}** (niv. {niv_c}/16) : elle gagne plus que la moyenne chez les meilleurs joueurs et tu l'as déjà à un bon niveau.\n"
                             f"{echanges} · estimé `≈{100 * av:.1f}%` → `≈{100 * ap:.1f}%` "
                             f"(à la place du changement proposé plus haut, pas en plus)\n"
                             f"[📥 Copier ce deck]({lien})", max(0.0, ap - av), 20)
            else:
                prio.ajouter("carte-forte", f"**Essaie** {fortes[0][1]} : elle gagne plus que la moyenne chez les meilleurs joueurs. "
                             "Je n'ai pas trouvé d'échange qui garde ton deck équilibré (défense aérienne, élixir) : "
                             "si tu veux la tester, remplace une carte du même genre et vérifie ton deck avec `!deck`.", 0.005, 20)
        if sections4:
            embeds.append({"title": "🃏 Tes cartes", "color": 15105570, "description": d.assembler(sections4)})

    # ===== Embed 6 : plan d'action =====
    conseils = prio.classes(6)
    if conseils:
        embeds.append({"title": "🚀 Ton plan d'action", "color": 5763719,
                       "description": d.assembler([f"{i + 1}. {p}" for i, p in enumerate(conseils)]),
                       "footer": {"text": "Classé par effet estimé sur tes résultats · relance !coach #TAG dans quelques jours pour voir ta progression"}})
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
    manquants = [n for n, val in (("DISCORD_BOT_TOKEN", d.BOT_TOKEN), ("DISCORD_CHANNEL_ID", d.CHANNEL_ID), ("CR_API_KEY", d.API_KEY)) if not val]
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
        suite = []
        if not tag:
            corps["content"] = "Écris `!coach #TAG` (ton tag est dans ton profil, sous ton nom) ou simplement `#TAG`."
        else:
            try:
                texte, embeds = construire(tag)
            except Exception as e:
                print(f"[ERREUR] Analyse impossible : {e}", file=sys.stderr)
                texte, embeds = "Désolé, l'analyse a échoué. Réessaie dans quelques minutes.", []
            if embeds:
                # Discord : 10 embeds et 6000 caractères au total par message -> on regroupe au lieu d'un message par embed
                groupes = regrouper(embeds)
                corps["embeds"] = groupes[0]
                suite = groupes[1:]
            else:
                corps["content"] = texte
        code, _ = d.discord("POST", f"/channels/{d.CHANNEL_ID}/messages", json=corps)
        if code not in (200, 201):
            print(f"[ERREUR] Réponse non envoyée (code {code}).", file=sys.stderr)
            d.discord("DELETE", f"/channels/{d.CHANNEL_ID}/messages/{m['id']}/reactions/{d.COCHE}/@me")
            continue
        for groupe in suite:
            time.sleep(1)
            c2, _ = d.discord("POST", f"/channels/{d.CHANNEL_ID}/messages",
                              json={"embeds": groupe, "allowed_mentions": {"parse": []}})
            if c2 not in (200, 201):
                print(f"[ERREUR] Suite de la réponse non envoyée (code {c2}).", file=sys.stderr)
        print(f"Demande {m['id']} traitée.")
    if not traites:
        print("Aucune nouvelle demande.")


if __name__ == "__main__":
    commande = sys.argv[1] if len(sys.argv) > 1 else ""
    if commande == "repondre":
        repondre()
    elif commande == "historique":
        rafraichir_historique()
    else:
        print("[ERREUR] Utilise : python Coach.py repondre | historique", file=sys.stderr)
        sys.exit(1)