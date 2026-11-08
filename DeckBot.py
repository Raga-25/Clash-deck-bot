"""Bot d'analyse de deck : un joueur colle son deck dans un salon Discord, le bot répond avec une
évaluation et des améliorations possibles.

Utilisation dans le salon (le « !deck » est facultatif : coller directement le lien suffit ; « !aide » affiche les consignes) :
    !deck gdc <lien du deck>        (guerre de clan)
    !deck classe <lien du deck>     (classé = Parcours des légendes)
    !deck voie <lien du deck>       (voie des trophées)
Le lien est celui que donne le jeu en appuyant sur « Copier le deck » (il contient aussi le tag du joueur :
le bot en déduit le niveau de ses cartes).

Deux modes de lancement (voir deckbot.yml) :
  python DeckBot.py repondre   lit le salon, répond aux nouvelles demandes (toutes les 5 minutes)
  python DeckBot.py collect    enregistre les stats des cartes chez les meilleurs joueurs (toutes les 6 heures)

Variables d'environnement :
  CR_API_KEY          clé API Clash Royale (liée à l'IP du proxy RoyaleAPI)
  DISCORD_BOT_TOKEN   jeton du bot Discord (repondre)
  DISCORD_CHANNEL_ID  identifiant du salon où le bot répond (repondre)
  DECKBOT_DIR         (facultatif) dossier des fichiers de données
"""
import os
import re
import sys
import json
import time
import unicodedata
import datetime
import requests
from concurrent.futures import ThreadPoolExecutor

# ========================
# 🔹 Réglages
# ========================
API_KEY = os.environ.get("CR_API_KEY")
BOT_TOKEN = os.environ.get("DISCORD_BOT_TOKEN")
CHANNEL_ID = os.environ.get("DISCORD_CHANNEL_ID")
DOSSIER = os.environ.get("DECKBOT_DIR", ".")
API_BASE = "https://proxy.royaleapi.dev/v1"
DISCORD_API = "https://discord.com/api/v10"

NB_JOUEURS = 100                   # joueurs lus pour le classé et la voie des trophées
NB_CLANS = 20                      # meilleurs clans de guerre dont on lit les membres
LOCALISATION_FRANCE = 57000087     # classement de secours (France)

MODES = {
    "gdc": {"nom": "Guerre de clan", "fichier": "data_gdc.json", "jours": 21,
            "types": {"riverRacePvP", "riverRaceDuel", "riverRaceDuelColosseum"}},
    "classe": {"nom": "Classé (Parcours des légendes)", "fichier": "data_classe.json", "jours": 10,
               "types": {"pathOfLegend"}},
    "voie": {"nom": "Voie des trophées", "fichier": "data_voie.json", "jours": 10,
             "types": {"PvP"}},
}
ALIAS = {
    "gdc": "gdc", "guerre": "gdc", "war": "gdc",
    "classe": "classe", "ranked": "classe", "parcours": "classe", "pol": "classe", "legendes": "classe",
    "voie": "voie", "trophees": "voie", "ladder": "voie", "route": "voie",
}
MODE_PAR_DEFAUT = "classe"

MIN_COMBATS_MODE = 300             # en dessous, pas assez de données pour évaluer ce mode
MIN_PARTIES_CARTE = 100            # une carte doit avoir au moins 100 parties pour être jugée
LISSAGE = 100                      # lissage du winrate des cartes
MAX_NIVEAUX_MANQUANTS = 3          # on ne conseille pas une carte à plus de 3 niveaux du max
NB_CHANGEMENTS = 2                 # au plus 2 cartes changées
GAIN_MINIMUM = 0.004               # gain estimé minimum (0,4 point)
PENALITE_NIVEAU = 0.004            # estimation : -0,4 point par niveau manquant et par carte
AGE_MAX_DEMANDE_H = 12             # on ignore les demandes plus vieilles que 12 h
MAX_DEMANDES_PAR_PASSAGE = 5

# Synergies entre paires de cartes (comptées pendant la collecte, calculées chaque semaine)
FICHIER_PAIRES = "data_paires.json"
FICHIER_SYNERGIES = "synergies.json"
FENETRE_PAIRES_JOURS = 21          # les paires des 21 derniers jours comptent
MIN_PARTIES_PAIRE = 150            # une paire doit avoir au moins 150 parties (tous modes) pour compter
MIN_PARTIES_PAIRE_MODE = 40        # pour avoir sa propre valeur dans un mode
LISSAGE_SYNERGIE = 300             # plus la paire a de parties, moins on la rapproche de zéro
POIDS_SYNERGIE = 1.0               # poids de la synergie dans l'estimation d'un deck
SEUIL_CITATION = 0.005             # une paire n'est citée que si elle pèse au moins 0,5 point

CARTES_VICTOIRE = {
    "Hog Rider", "Royal Hogs", "Royal Giant", "Giant", "Goblin Giant", "Elixir Golem",
    "Golem", "Electro Giant", "Lava Hound", "Balloon", "Ram Rider", "Battle Ram",
    "Graveyard", "Goblin Barrel", "Skeleton Barrel", "Miner", "Mortar", "X-Bow",
    "Sparky", "Goblin Drill", "Rune Giant", "Three Musketeers",
}
SORTS = {
    "Fireball", "Arrows", "Zap", "The Log", "Poison", "Lightning", "Rocket", "Tornado", "Freeze",
    "Rage", "Clone", "Earthquake", "Giant Snowball", "Barbarian Barrel", "Goblin Curse",
    "Royal Delivery", "Void", "Mirror", "Vines",
}
BATIMENTS = {
    "Cannon", "Tesla", "Inferno Tower", "Bomb Tower", "Barbarian Hut", "Goblin Hut", "Tombstone",
    "Furnace", "Elixir Collector", "Goblin Cage",
}

# Noms français des cartes (l'API ne les donne qu'en anglais).
# Une carte absente de cette liste s'affiche en anglais : ajoute-la ici si besoin.
NOMS_FR = {
    "Knight": "Chevalier", "Archers": "Archères", "Goblins": "Gobelins", "Giant": "Géant",
    "P.E.K.K.A": "P.E.K.K.A", "Minions": "Gargouilles", "Balloon": "Ballon", "Witch": "Sorcière",
    "Barbarians": "Barbares", "Golem": "Golem", "Skeletons": "Squelettes", "Valkyrie": "Valkyrie",
    "Skeleton Army": "Armée de squelettes", "Bomber": "Bombardier", "Musketeer": "Mousquetaire",
    "Baby Dragon": "Bébé dragon", "Prince": "Prince", "Wizard": "Sorcier",
    "Mini P.E.K.K.A": "Mini P.E.K.K.A", "Spear Goblins": "Gobelins à lances",
    "Giant Skeleton": "Squelette géant", "Hog Rider": "Chevaucheur de cochon",
    "Minion Horde": "Horde de gargouilles", "Ice Wizard": "Sorcier de glace",
    "Royal Giant": "Géant royal", "Guards": "Gardes", "Princess": "Princesse",
    "Dark Prince": "Prince des ténèbres", "Three Musketeers": "Trois Mousquetaires",
    "Lava Hound": "Molosse de lave", "Ice Spirit": "Esprit de glace", "Fire Spirit": "Esprit de feu",
    "Miner": "Mineur", "Sparky": "Sparky", "Bowler": "Bouliste", "Lumberjack": "Bûcheron",
    "Battle Ram": "Bélier de combat", "Inferno Dragon": "Dragon infernal", "Ice Golem": "Golem de glace",
    "Mega Minion": "Méga gargouille", "Dart Goblin": "Gobelin à sarbacane",
    "Goblin Gang": "Bande de gobelins", "Electro Wizard": "Électro-sorcier",
    "Elite Barbarians": "Barbares d'élite", "Hunter": "Chasseur", "Executioner": "Bourreau",
    "Bandit": "Bandit", "Royal Recruits": "Recrues royales", "Night Witch": "Sorcière de la nuit",
    "Bats": "Chauves-souris", "Royal Ghost": "Fantôme royal", "Ram Rider": "Chevaucheur de bélier",
    "Zappies": "Zappies", "Rascals": "Garnements", "Cannon Cart": "Chariot canon",
    "Mega Knight": "Méga chevalier", "Skeleton Barrel": "Tonneau de squelettes",
    "Flying Machine": "Machine volante", "Wall Breakers": "Casseurs de murs",
    "Royal Hogs": "Cochons royaux", "Goblin Giant": "Géant gobelin", "Fisherman": "Pêcheur",
    "Magic Archer": "Archer magique", "Electro Dragon": "Dragon électrique",
    "Firecracker": "Artificière", "Mighty Miner": "Mineur puissant", "Elixir Golem": "Golem d'élixir",
    "Battle Healer": "Guérisseuse de combat", "Skeleton King": "Roi squelette",
    "Archer Queen": "Reine des archères", "Golden Knight": "Chevalier doré", "Monk": "Moine",
    "Skeleton Dragons": "Dragons squelettes", "Mother Witch": "Sorcière mère",
    "Electro Spirit": "Esprit électrique", "Electro Giant": "Géant électrique", "Phoenix": "Phénix",
    "Little Prince": "Petit prince", "Goblin Demolisher": "Démolisseur gobelin",
    "Goblin Machine": "Machine gobelin", "Suspicious Bush": "Buisson suspect",
    "Rune Giant": "Géant des runes", "Berserker": "Berserker", "Boss Bandit": "Boss bandit",
    "Spirit Empress": "Impératrice des esprits", "Vines": "Lianes", "Cannon": "Canon",
    "Mortar": "Mortier", "Tesla": "Tesla", "Inferno Tower": "Tour infernale",
    "Bomb Tower": "Tour à bombes", "Barbarian Hut": "Hutte de barbares",
    "Goblin Hut": "Hutte de gobelins", "Tombstone": "Pierre tombale", "Furnace": "Fournaise",
    "X-Bow": "Arbalète", "Elixir Collector": "Pompe à élixir", "Goblin Cage": "Cage à gobelin",
    "Goblin Drill": "Foreuse à gobelins", "Fireball": "Boule de feu", "Arrows": "Flèches",
    "Rage": "Rage", "Rocket": "Roquette", "Goblin Barrel": "Tonneau à gobelins", "Freeze": "Gel",
    "Mirror": "Miroir", "Lightning": "Foudre", "Zap": "Zap", "Poison": "Poison",
    "Graveyard": "Cimetière", "The Log": "La Bûche", "Tornado": "Tornade", "Clone": "Clone",
    "Earthquake": "Séisme", "Barbarian Barrel": "Tonneau de barbares",
    "Heal Spirit": "Esprit guérisseur", "Giant Snowball": "Boule de neige géante",
    "Royal Delivery": "Livraison royale", "Void": "Néant", "Goblin Curse": "Malédiction gobelin",
}


def nom_fr(nom):
    return NOMS_FR.get(nom, nom)


session = requests.Session()
session.headers.update({"Authorization": f"Bearer {API_KEY}", "Accept": "application/json"})


def maintenant_utc():
    return datetime.datetime.now(datetime.timezone.utc)


def enc(tag):
    return tag.replace("#", "%23")


def sans_accents(texte):
    return "".join(c for c in unicodedata.normalize("NFD", texte) if unicodedata.category(c) != "Mn").lower()


# ========================
# 🔹 API Clash Royale
# ========================
def api_get(path, params=None, tentatives=3):
    """GET sur l'API (via le proxy). Renvoie le JSON, ou None en cas d'échec."""
    for essai in range(tentatives):
        try:
            r = session.get(f"{API_BASE}{path}", params=params, timeout=20)
        except requests.RequestException as e:
            print(f"[API réseau] {path} : {e}", file=sys.stderr)
            time.sleep(2)
            continue
        if r.status_code == 200:
            return r.json()
        if r.status_code in (429, 500, 502, 503, 504):
            time.sleep(2 * (essai + 1))
            continue
        print(f"[API {r.status_code}] {path}", file=sys.stderr)
        return None
    return None


def joueurs_a_lire(mode):
    """Tags des joueurs dont on lit les combats, pour un mode."""
    if mode == "gdc":
        chemins = ["/locations/global/rankings/clanwars", f"/locations/{LOCALISATION_FRANCE}/rankings/clanwars"]
        clans = []
        for chemin in chemins:
            data = api_get(chemin, {"limit": NB_CLANS})
            clans = [it["tag"] for it in ((data or {}).get("items") or []) if it.get("tag")]
            if clans:
                break

        def membres(tag):
            data = api_get(f"/clans/{enc(tag)}/members")
            return [m["tag"] for m in ((data or {}).get("items") or []) if m.get("tag")]

        with ThreadPoolExecutor(max_workers=10) as ex:
            listes = list(ex.map(membres, clans))
        vus, res = set(), []
        for liste in listes:
            for t in liste:
                if t not in vus:
                    vus.add(t)
                    res.append(t)
        return res
    if mode == "classe":
        m1 = maintenant_utc().replace(day=1) - datetime.timedelta(days=1)
        m2 = m1.replace(day=1) - datetime.timedelta(days=1)
        chemins = [f"/locations/global/pathoflegend/{m1:%Y-%m}/rankings/players",
                   f"/locations/{LOCALISATION_FRANCE}/pathoflegend/players",
                   f"/locations/global/pathoflegend/{m2:%Y-%m}/rankings/players"]
    else:
        # classements par trophées ; s'ils sont indisponibles, on prend les meilleurs du Parcours des légendes
        m1 = maintenant_utc().replace(day=1) - datetime.timedelta(days=1)
        chemins = ["/locations/global/rankings/players", f"/locations/{LOCALISATION_FRANCE}/rankings/players",
                   f"/locations/global/pathoflegend/{m1:%Y-%m}/rankings/players",
                   f"/locations/{LOCALISATION_FRANCE}/pathoflegend/players"]
    for chemin in chemins:
        print(f"[{mode}] essai du classement {chemin}", file=sys.stderr)
        data = api_get(chemin, {"limit": NB_JOUEURS})
        items = (data or {}).get("items") or []
        if items:
            return [it["tag"] for it in items if it.get("tag")]
    return []


# ========================
# 🔹 Données stockées (stats par carte)
# ========================
def chemin_donnees(mode):
    return os.path.join(DOSSIER, MODES[mode]["fichier"])


def charger_donnees(mode, strict=False):
    chemin = chemin_donnees(mode)
    vide = {"version": 1, "last": {}, "cards": {}, "days": {}}
    if not os.path.exists(chemin):
        return vide
    try:
        with open(chemin, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError) as e:
        print(f"[ERREUR] Fichier illisible ({chemin}) : {e}", file=sys.stderr)
        if strict:
            sys.exit(1)
        return vide
    for cle, defaut in (("last", {}), ("cards", {}), ("days", {})):
        data.setdefault(cle, defaut)
    return data


def sauver_donnees(mode, data):
    chemin = chemin_donnees(mode)
    tmp = chemin + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    os.replace(tmp, chemin)


def collecter(mode, tags, data, paires=None):
    """Ajoute les nouveaux combats des joueurs (stats par carte). Renvoie leur nombre."""
    types = MODES[mode]["types"]

    def lire(tag):
        return tag, api_get(f"/players/{enc(tag)}/battlelog") or []

    with ThreadPoolExecutor(max_workers=10) as ex:
        logs = list(ex.map(lire, tags))
    nouveaux = 0
    for tag, combats in logs:
        derniere = data["last"].get(tag, "")
        plus_recent = derniere
        for b in combats:
            bt = b.get("battleTime", "")
            if not bt or bt <= derniere:
                continue
            plus_recent = max(plus_recent, bt)
            if b.get("type") not in types:
                continue
            eq = (b.get("team") or [None])[0]
            adv = (b.get("opponent") or [None])[0]
            if not eq or not adv:
                continue
            cartes = eq.get("cards") or []
            if len(cartes) != 8 or len({c["id"] for c in cartes}) != 8:
                continue
            c1, c2 = eq.get("crowns", 0), adv.get("crowns", 0)
            if c1 == c2:
                continue
            jour = f"{bt[:4]}-{bt[4:6]}-{bt[6:8]}"
            d = data["days"].setdefault(jour, {"b": 0, "w": 0, "c": {}})
            d["b"] += 1
            d["w"] += 1 if c1 > c2 else 0
            for c in cartes:
                e = d["c"].setdefault(str(c["id"]), [0, 0])
                e[0] += 1
                e[1] += 1 if c1 > c2 else 0
                data["cards"][str(c["id"])] = [c.get("name", "?"), c.get("elixirCost") or 0]
            if paires is not None:
                compter_paires(paires, jour, mode, sorted(c["id"] for c in cartes), c1 > c2)
            nouveaux += 1
        if plus_recent:
            data["last"][tag] = plus_recent
    return nouveaux


def compter_paires(paires, jour, mode, ids, victoire):
    """Ajoute un combat aux compteurs : cartes seules et 28 paires de cartes du deck."""
    m = paires["days"].setdefault(jour, {}).setdefault(mode, {"b": 0, "w": 0, "c": {}, "p": {}})
    v = 1 if victoire else 0
    m["b"] += 1
    m["w"] += v
    for i, a in enumerate(ids):
        e = m["c"].setdefault(str(a), [0, 0])
        e[0] += 1
        e[1] += v
        for b in ids[i + 1:]:
            e = m["p"].setdefault(f"{a}-{b}", [0, 0])
            e[0] += 1
            e[1] += v


def charger_paires(strict=False):
    chemin = os.path.join(DOSSIER, FICHIER_PAIRES)
    vide = {"version": 1, "days": {}}
    if not os.path.exists(chemin):
        return vide
    try:
        with open(chemin, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError) as e:
        print(f"[ERREUR] Fichier illisible ({chemin}) : {e}", file=sys.stderr)
        if strict:
            sys.exit(1)
        return vide
    data.setdefault("days", {})
    return data


def sauver_paires(data):
    chemin = os.path.join(DOSSIER, FICHIER_PAIRES)
    tmp = chemin + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    os.replace(tmp, chemin)


def nettoyer_paires(paires, aujourdhui):
    """Supprime les jours trop anciens ; les paires vues une seule fois dans un jour déjà ancien sont allégées."""
    limite = (aujourdhui - datetime.timedelta(days=FENETRE_PAIRES_JOURS)).strftime("%Y-%m-%d")
    allege = (aujourdhui - datetime.timedelta(days=2)).strftime("%Y-%m-%d")
    for jour in [j for j in paires["days"] if j < limite]:
        del paires["days"][jour]
    for jour, modes in paires["days"].items():
        if jour >= allege:
            continue
        for m in modes.values():
            m["p"] = {k: v for k, v in m["p"].items() if v[0] >= 2}


def _somme(paires, modes):
    """Additionne les jours de la fenêtre. Renvoie (combats, victoires, cartes, paires)."""
    b = w = 0
    cartes, duos = {}, {}
    for jour in paires["days"].values():
        for nom, m in jour.items():
            if nom not in modes:
                continue
            b += m["b"]
            w += m["w"]
            for k, (g, v) in m["c"].items():
                e = cartes.setdefault(k, [0, 0])
                e[0] += g
                e[1] += v
            for k, (g, v) in m["p"].items():
                e = duos.setdefault(k, [0, 0])
                e[0] += g
                e[1] += v
    return b, w, cartes, duos


def _lifts(b, w, cartes, duos, minimum):
    """Écart brut de chaque paire : winrate réel de la paire moins ce que laissent attendre ses deux cartes."""
    if b == 0:
        return {}
    p0 = w / b
    res = {}
    for k, (g, v) in duos.items():
        if g < minimum:
            continue
        a, c = k.split("-")
        ca, cc = cartes.get(a), cartes.get(c)
        if not ca or not cc or ca[0] == 0 or cc[0] == 0:
            continue
        # winrate de chaque carte hors parties jouées avec l'autre (sinon la synergie se cache dans la moyenne)
        ga, gc = ca[0] - g, cc[0] - g
        if ga < 30 or gc < 30:
            continue
        attendu = (ca[1] - v) / ga + (cc[1] - v) / gc - p0
        res[k] = (g, v / g - attendu)
    return res


def calculer_synergies(paires):
    """Synergie de chaque paire fréquente : globale (tous modes) et propre à chaque mode.
    La valeur de chaque mode est rapprochée de la valeur globale quand elle a peu de parties."""
    tous = set(MODES)
    b, w, cartes, duos = _somme(paires, tous)
    glob = {}
    for k, (g, brut) in _lifts(b, w, cartes, duos, MIN_PARTIES_PAIRE).items():
        glob[k] = brut * g / (g + LISSAGE_SYNERGIE)
    modes = {}
    for nom in MODES:
        bm, wm, cm, dm = _somme(paires, {nom})
        res = {}
        for k, (g, brut) in _lifts(bm, wm, cm, dm, MIN_PARTIES_PAIRE_MODE).items():
            ref = glob.get(k, 0.0)
            res[k] = round((brut * g + LISSAGE_SYNERGIE * ref) / (g + LISSAGE_SYNERGIE), 4)
        modes[nom] = res
    return {"version": 1, "ts": maintenant_utc().isoformat(), "fenetre_jours": FENETRE_PAIRES_JOURS,
            "combats": b, "global": {k: round(v, 4) for k, v in glob.items()}, "modes": modes}


def commande_synergies():
    paires = charger_paires(strict=True)
    syn = calculer_synergies(paires)
    chemin = os.path.join(DOSSIER, FICHIER_SYNERGIES)
    tmp = chemin + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(syn, f, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    os.replace(tmp, chemin)
    print(f"Synergies : {syn['combats']} combats, {len(syn['global'])} paires globales, "
          + ", ".join(f"{m} {len(v)}" for m, v in syn["modes"].items()))


_SYN = {"data": None, "mode": None}


def charger_synergies():
    chemin = os.path.join(DOSSIER, FICHIER_SYNERGIES)
    try:
        with open(chemin, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def definir_synergies(mode):
    _SYN["data"], _SYN["mode"] = charger_synergies(), mode


def synergie_paire(a, b, syn, mode):
    if not syn:
        return 0.0
    k = f"{min(a, b)}-{max(a, b)}"
    v = (syn.get("modes") or {}).get(mode, {}).get(k)
    return v if v is not None else (syn.get("global") or {}).get(k, 0.0)


def bonus_synergie(ids, syn, mode):
    """Effet des paires sur le winrate estimé du deck (même échelle qu'une moyenne de 8 cartes)."""
    if not syn:
        return 0.0
    ids = list(ids)
    total = sum(synergie_paire(ids[i], ids[j], syn, mode) for i in range(len(ids)) for j in range(i + 1, len(ids)))
    return POIDS_SYNERGIE * total / len(ids)


def lignes_synergie(ids, syn, mode, nom):
    """Meilleure et pire paire du deck, si elles pèsent assez."""
    if not syn:
        return []
    paires = sorted(((synergie_paire(ids[i], ids[j], syn, mode), ids[i], ids[j])
                     for i in range(len(ids)) for j in range(i + 1, len(ids))), key=lambda x: x[0])
    res = []
    if paires and paires[-1][0] >= SEUIL_CITATION:
        v, a, b = paires[-1]
        res.append(f"✨ Bonne synergie : {nom(a)} + {nom(b)} (`{100 * v:+.1f}` pt)")
    if paires and paires[0][0] <= -SEUIL_CITATION:
        v, a, b = paires[0]
        res.append(f"⚠️ Paire qui sous-performe : {nom(a)} + {nom(b)} (`{100 * v:+.1f}` pt)")
    return res


def nettoyer(data, mode, aujourdhui):
    limite = (aujourdhui - datetime.timedelta(days=MODES[mode]["jours"])).strftime("%Y-%m-%d")
    for jour in [j for j in data["days"] if j < limite]:
        del data["days"][jour]


def aujourdhui_utc():
    return maintenant_utc().date()


def collecte_tous_modes():
    manquants = [] if API_KEY else ["CR_API_KEY"]
    if manquants:
        print(f"[ERREUR] Variable(s) manquante(s) : {', '.join(manquants)}", file=sys.stderr)
        sys.exit(1)
    jour_semaine = aujourdhui_utc().weekday()
    paires = charger_paires(strict=True)
    echecs = 0
    for mode in MODES:
        if mode == "gdc" and jour_semaine not in (0, 3, 4, 5, 6):   # la guerre va du jeudi au lundi
            print("gdc : hors période de guerre, rien à collecter")
            continue
        tags = joueurs_a_lire(mode)
        if not tags:
            print(f"[ERREUR] {mode} : classement introuvable.", file=sys.stderr)
            echecs += 1
            continue
        data = charger_donnees(mode, strict=True)
        n = collecter(mode, tags, data, paires)
        nettoyer(data, mode, aujourdhui_utc())
        sauver_donnees(mode, data)
        print(f"{mode} : {len(tags)} joueurs lus, {n} nouveaux combats ({len(data['days'])} jours en mémoire)")
    nettoyer_paires(paires, aujourdhui_utc())
    sauver_paires(paires)
    if echecs == len(MODES):
        sys.exit(1)


# ========================
# 🔹 Évaluation d'un deck
# ========================
def stats_cartes(data):
    """Winrate lissé et usage de chaque carte. Renvoie (par_carte, p0, nb_combats)."""
    jeux, vict, combats = {}, {}, 0
    for j in data["days"].values():
        combats += j["b"]
        for cid, (g, w) in j["c"].items():
            jeux[int(cid)] = jeux.get(int(cid), 0) + g
            vict[int(cid)] = vict.get(int(cid), 0) + w
    total_g = sum(jeux.values())
    p0 = sum(vict.values()) / total_g if total_g else 0.5
    par_carte = {}
    for cid, g in jeux.items():
        nom, elixir = data["cards"].get(str(cid), ["?", 0])
        par_carte[cid] = {"name": nom, "elixir": elixir, "games": g,
                          "wr": (vict[cid] + LISSAGE * p0) / (g + LISSAGE),
                          "usage": g / combats if combats else 0}
    return par_carte, p0, combats


def role(nom):
    if nom in CARTES_VICTOIRE:
        return "victoire"
    if nom in SORTS:
        return "sort"
    if nom in BATIMENTS:
        return "batiment"
    return "troupe"


def niveau_jeu(carte):
    return carte.get("level", 0) + 16 - carte.get("maxLevel", 16)


def manque(carte):
    return max(0, carte.get("maxLevel", carte.get("level", 0)) - carte.get("level", 0))


def note_deck(ids, stats, p0, profil):
    total = 0.0
    for i in ids:
        wr = stats[i]["wr"] if i in stats and stats[i]["games"] >= MIN_PARTIES_CARTE else p0
        pen = PENALITE_NIVEAU * manque(profil[i]) if profil and i in profil else 0.0
        total += wr - pen
    return total / len(ids) + bonus_synergie(ids, _SYN["data"], _SYN["mode"])


def elixir_moyen(ids, stats, profil):
    couts = []
    for i in ids:
        c = (profil.get(i, {}).get("elixirCost") if profil else None) or stats.get(i, {}).get("elixir")
        if c:
            couts.append(c)
    return sum(couts) / len(couts) if couts else 0.0


def ameliorer(ids, evo, stats, p0, profil, exclues=()):
    """Remplacements proposés : renvoie (nouveau_deck, [(sortant, entrant)])."""
    cartes = list(ids)
    if profil:
        pool = {i for i, c in profil.items() if i not in cartes and manque(c) <= MAX_NIVEAUX_MANQUANTS}
    else:
        pool = set(stats)
    pool = {i for i in pool if i in stats and stats[i]["games"] >= MIN_PARTIES_CARTE and i not in exclues}
    changements = []
    while len(changements) < NB_CHANGEMENTS:
        base = note_deck(cartes, stats, p0, profil)
        meilleur = None
        for pos, sortant in enumerate(cartes):
            if evo[pos] or sortant not in stats:
                continue
            for entrant in pool:
                if role(stats[entrant]["name"]) != role(stats[sortant]["name"]):
                    continue
                if abs((stats[entrant]["elixir"] or 0) - (stats[sortant]["elixir"] or 0)) > 1:
                    continue
                nouveau = cartes[:pos] + [entrant] + cartes[pos + 1:]
                gain = note_deck(nouveau, stats, p0, profil) - base
                if gain >= GAIN_MINIMUM and (meilleur is None or gain > meilleur[0]):
                    meilleur = (gain, pos, sortant, entrant)
        if not meilleur:
            break
        _, pos, sortant, entrant = meilleur
        cartes[pos] = entrant
        pool.discard(entrant)
        changements.append((sortant, entrant))
    return cartes, changements


def optimiser_ensemble(decks_ids, evos, stats, p0, profil):
    """Améliore plusieurs decks de guerre à la fois, sans aucune carte en commun entre eux.

    Une carte déjà présente dans un des 4 decks ne peut pas être proposée dans un autre : les remplaçantes viennent
    uniquement des cartes libres. Les doublons de départ sont corrigés en priorité (ils pèsent plus lourd que tout gain).
    Renvoie (decks, changements) ; changement = (numéro_deck, carte_sortante, carte_entrante, None)."""
    decks = [list(d) for d in decks_ids]
    n = len(decks)

    def doublons(ds):
        tous = [c for d in ds for c in d]
        return len(tous) - len(set(tous))

    def objectif(ds):
        return sum(note_deck(d, stats, p0, profil) for d in ds) - 1.0 * doublons(ds)

    def compatibles(x, y):
        if x not in stats or y not in stats:
            return False
        if role(stats[x]["name"]) != role(stats[y]["name"]):
            return False
        return abs((stats[x]["elixir"] or 0) - (stats[y]["elixir"] or 0)) <= 1

    utilisees = {c for d in decks for c in d}
    if profil:
        pool = {i for i, c in profil.items() if i not in utilisees and manque(c) <= MAX_NIVEAUX_MANQUANTS}
    else:
        pool = set(stats) - utilisees
    pool = {i for i in pool if i in stats and stats[i]["games"] >= MIN_PARTIES_CARTE}
    limite = NB_CHANGEMENTS + (2 if doublons(decks) else 0)
    nb = [0] * n
    changements = []
    for _ in range(4 * n):
        courant = objectif(decks)
        meilleur = None
        for k in range(n):
            for pos in range(8):
                x = decks[k][pos]
                if evos[k][pos]:
                    continue
                if nb[k] < limite:
                    for y in pool:
                        if not compatibles(x, y):
                            continue
                        decks[k][pos] = y
                        gain = objectif(decks) - courant
                        decks[k][pos] = x
                        if gain >= GAIN_MINIMUM and (meilleur is None or gain > meilleur[0]):
                            meilleur = (gain, "remplace", k, pos, y, None, None)
        if not meilleur:
            break
        _, genre, k, pos, y, _j, _pos2 = meilleur
        x = decks[k][pos]
        decks[k][pos] = y
        pool.discard(y)
        nb[k] += 1
        changements.append((k, x, y, None))
    return decks, changements


def autres_decks_guerre(tag, decks_colles, combien):
    """Retrouve les autres decks de guerre du joueur dans ses combats récents (l'API ne garde que 25 combats).
    On ne garde que des decks sans carte commune avec les decks collés ni entre eux."""
    if not tag or combien <= 0:
        return []
    combats = api_get(f"/players/{enc(tag)}/battlelog") or []
    vus = {}
    for rang, b in enumerate(combats):                      # du plus récent au plus ancien
        if b.get("type") not in MODES["gdc"]["types"]:
            continue
        eq = (b.get("team") or [None])[0]
        cartes = (eq or {}).get("cards") or []
        ids = [c["id"] for c in cartes]
        if len(ids) != 8 or len(set(ids)) != 8:
            continue
        e = vus.setdefault(tuple(sorted(ids)), {"ids": ids, "n": 0, "rang": rang})
        e["n"] += 1
    interdites = {c for d in decks_colles for c in d}
    choisis = []
    for e in sorted(vus.values(), key=lambda e: (-e["n"], e["rang"])):
        if interdites & set(e["ids"]):
            continue
        choisis.append(e["ids"])
        interdites |= set(e["ids"])
        if len(choisis) == combien:
            break
    return choisis


def points_attention(ids, stats, profil):
    noms = [stats[i]["name"] for i in ids if i in stats]
    notes = []
    if noms and not any(n in CARTES_VICTOIRE for n in noms):
        notes.append("aucune carte de victoire détectée")
    nb_sorts = sum(1 for n in noms if n in SORTS)
    if nb_sorts == 0:
        notes.append("aucun sort")
    elif nb_sorts > 3:
        notes.append(f"beaucoup de sorts ({nb_sorts})")
    el = elixir_moyen(ids, stats, profil)
    if el and el < 2.6:
        notes.append(f"élixir moyen très bas ({el:.1f})")
    elif el > 4.4:
        notes.append(f"élixir moyen très élevé ({el:.1f})")
    rares = [nom_fr(stats[i]["name"]) for i in ids if i not in stats or stats[i]["games"] < MIN_PARTIES_CARTE]
    if rares:
        notes.append("peu de données sur " + ", ".join(rares))
    return notes


def etiquette(score, p0):
    ecart = 100 * (score - p0)
    if ecart >= 1.5:
        return "🟢 Très bon deck"
    if ecart >= 0.7:
        return "🟢 Bon deck"
    if ecart > -0.7:
        return "🟡 Dans la moyenne"
    if ecart > -1.5:
        return "🟠 Un peu faible"
    return "🔴 Faible"


# ========================
# 🔹 Lecture de la demande
# ========================
CONSIGNES = """🔎 **ANALYSE DE DECK**

1️⃣ Copie ton deck dans le jeu (bouton « Copier le deck »)
2️⃣ Colle-le ici, avec le mode écrit avant le lien :
• `gdc` = guerre de clan
• `voie` = voie des trophées
• rien = classé (par défaut)
Exemple : `gdc` puis ton message copié
3️⃣ Le bot répond sous ton message en 5-10 min. Un ✅ = demande prise en compte.

⚔️ **En guerre** : colle le ou les decks à améliorer (`gdc` avant). Le bot retrouve tes autres decks de guerre grâce à ton tag et n'utilise aucune de leurs cartes. Si tu veux tout contrôler, colle les 4 decks dans le même message.

📋 **Tu reçois** :
• la note estimée du deck et le winrate de chaque carte
• les points faibles
• jusqu'à 2 cartes à remplacer (niveaux et élixir avant/après)
• un lien pour copier le deck amélioré

💡 Le lien contient ton tag : le bot connaît le niveau de tes cartes. C'est une estimation, pas une garantie. En guerre, données du jeudi au lundi seulement. Un deck par message (jusqu'à 4 en guerre)."""

AIDE = ("Utilise : `!deck <mode> <lien du deck>`\n"
        "Modes : `gdc` (guerre), `classe` (Parcours des légendes), `voie` (voie des trophées).\n"
        "Le lien s'obtient dans le jeu avec « Copier le deck ».")


def lire_un_lien(url):
    """Lit un lien « Copier le deck » : renvoie (ids, slots, tt, tag) ou None."""
    m_deck = re.search(r"deck=([\d;]+)", url)
    if not m_deck:
        return None
    ids = [int(x) for x in m_deck.group(1).split(";") if x]
    m_slots = re.search(r"slots=([\d;]+)", url)
    slots = [int(x) for x in m_slots.group(1).split(";") if x] if m_slots else []
    if len(slots) != 8:
        slots = [0] * 8
    m_tt = re.search(r"tt=(\d+)", url)
    m_id = re.search(r"[?&]id=([0-9a-z]+)", url)
    return ids, slots, int(m_tt.group(1)) if m_tt else None, ("#" + m_id.group(1).upper()) if m_id else None


def lire_demande(contenu):
    """Renvoie (mode, decks, tag, mode_devine) ; decks = liste de (ids, slots, tt). Lève ValueError avec un message."""
    texte = sans_accents(contenu)
    liens = re.findall(r"https?://\S+", texte) or [texte]
    decks, tag, vus = [], None, set()
    for lien in liens:
        lu = lire_un_lien(lien)
        if not lu:
            continue
        ids, slots, tt, t = lu
        if len(ids) != 8 or len(set(ids)) != 8:
            raise ValueError("Chaque lien doit contenir 8 cartes différentes. " + AIDE)
        if tuple(ids) in vus:
            continue
        vus.add(tuple(ids))
        decks.append((ids, slots, tt))
        tag = tag or t
    if not decks:
        raise ValueError("Je ne trouve pas de deck dans ton message. " + AIDE)
    avant_lien = re.sub(r"https?://\S+", " ", texte)
    mode, devine = None, False
    for mot in re.findall(r"[a-z]+", avant_lien.replace("!deck", " ")):
        if mot in ALIAS:
            mode = ALIAS[mot]
            break
    if mode is None:
        mode, devine = MODE_PAR_DEFAUT, True
    return mode, decks[:4], tag, devine


def lien_deck(ids, slots, tt):
    lien = f"https://link.clashroyale.com/fr?clashroyale://copyDeck?deck={';'.join(str(i) for i in ids)}"
    lien += f"&slots={';'.join(str(s) for s in slots)}"
    if tt:
        lien += f"&tt={tt}"
    return lien


# ========================
# 🔹 Réponse
# ========================
_CACHE_DIRECT = {}


def donnees_du_mode(mode):
    """Données stockées si elles suffisent, sinon lecture en direct chez les meilleurs joueurs.
    Renvoie (data, source) ; data vaut None si le classement est introuvable."""
    data = charger_donnees(mode)
    if sum(j["b"] for j in data["days"].values()) >= MIN_COMBATS_MODE:
        return data, "stockees"
    if mode not in _CACHE_DIRECT:
        tags = joueurs_a_lire(mode)
        if not tags:
            _CACHE_DIRECT[mode] = (None, "introuvable")
        else:
            direct = {"version": 1, "last": {}, "cards": {}, "days": {}}
            collecter(mode, tags, direct)
            _CACHE_DIRECT[mode] = (direct, "direct")
    return _CACHE_DIRECT[mode]


def construire_reponse(mode, decks, tag, devine):
    """Renvoie (texte_simple, embed)."""
    ids, slots, tt = decks[0]
    nom_mode = MODES[mode]["nom"]
    data, source = donnees_du_mode(mode)
    if data is None:
        return (f"Je n'arrive pas à récupérer les meilleurs joueurs du mode **{nom_mode}** pour le moment. "
                "Réessaie un peu plus tard.", None)
    stats, p0, combats = stats_cartes(data)
    if combats < MIN_COMBATS_MODE:
        precision = (" Les combats de guerre ne restent que peu de temps dans l'historique des joueurs : "
                     "réessaie pendant la guerre (du jeudi au lundi)." if mode == "gdc" else "")
        return (f"Je n'ai trouvé que {combats} combats récents pour le mode **{nom_mode}** "
                f"(il m'en faut au moins {MIN_COMBATS_MODE}).{precision}", None)

    definir_synergies(mode)
    profil = None
    if tag:
        p = api_get(f"/players/{enc(tag)}")
        if p and p.get("cards"):
            profil = {c["id"]: c for c in p["cards"]}
            if not all(i in profil for d in decks for i in d[0]):
                profil = None
    autres = []
    if mode == "gdc" and tag:
        autres = autres_decks_guerre(tag, [d[0] for d in decks], 4 - len(decks))
    if mode == "gdc" and len(decks) >= 2:
        return None, construire_embed_gdc(decks, autres, stats, p0, combats, profil, source)
    exclues = {c for a in autres for c in a}
    evo = [s > 0 for s in slots]

    score = note_deck(ids, stats, p0, profil)
    el_avant = elixir_moyen(ids, stats, profil)
    nouveau, changements = ameliorer(ids, evo, stats, p0, profil, exclues)
    score_apres = note_deck(nouveau, stats, p0, profil)

    def nom_carte(i, avec_niveau=True):
        nom = nom_fr(stats[i]["name"]) if i in stats else f"carte {i}"
        if profil and i in profil and avec_niveau:
            nom += f" (niv. {niveau_jeu(profil[i])}/16)"
        return nom

    lignes = []
    for pos, i in enumerate(ids):
        s = stats.get(i)
        if s and s["games"] >= MIN_PARTIES_CARTE:
            lignes.append(f"{nom_carte(i)}{' ✨' if evo[pos] else ''} — `{100 * s['wr']:.1f}%`")
        else:
            lignes.append(f"{nom_carte(i)}{' ✨' if evo[pos] else ''} — peu de données")
    sections = [f"**{etiquette(score, p0)}** · winrate estimé `≈{100 * score:.1f}%` "
                f"(moyenne du mode : `{100 * p0:.1f}%`)\n-# {combats} combats analysés · {nom_mode}"
                + (" · données lues en direct" if source == "direct" else "")
                + (f"\n-# Mode non précisé : j'ai pris « {nom_mode} ». Pour un autre mode, écris `gdc` ou `voie` avant le lien." if devine else ""),
                "**🧩 Tes cartes** (winrate de chaque carte dans ce mode)\n" + "\n".join(lignes)]
    notes = points_attention(ids, stats, profil)
    notes_syn = lignes_synergie(ids, _SYN["data"], mode, lambda i: nom_carte(i, False))
    if notes_syn:
        sections.append("**🔗 Synergies**\n" + "\n".join(notes_syn))
    if notes:
        sections.append("**⚠️ Points d'attention**\n" + "\n".join(f"• {n.capitalize()}" for n in notes))
    if changements:
        lig = []
        for sortant, entrant in changements:
            lig.append(f"🔁 {nom_carte(sortant)} → **{nom_carte(entrant)}**")
        el_apres = elixir_moyen(nouveau, stats, profil)
        nouveaux_slots = [0 if nouveau[p] != ids[p] else slots[p] for p in range(8)]
        sections.append("**🔧 Améliorations proposées**\n" + "\n".join(lig)
                        + f"\n📊 estimé `≈{100 * score:.1f}%` → `≈{100 * score_apres:.1f}%`"
                        + f"\n⚡ élixir `{el_avant:.1f}` → `{el_apres:.1f}`"
                        + f"\n[📥 Copier le deck amélioré]({lien_deck(nouveau, nouveaux_slots, tt)})"
                        + ("" if profil else "\n-# Sans ton tag, je ne peux pas vérifier que tu possèdes ces cartes ni leur niveau."))
    else:
        sections.append(f"**🔧 Améliorations** : rien de mieux à proposer{' avec tes cartes' if profil else ''} (⚡ élixir `{el_avant:.1f}`).")
    if mode == "gdc":
        if autres:
            sections.append("**🛡️ Tes autres decks de guerre** (retrouvés dans ton historique, je n'utilise aucune de leurs cartes)\n"
                            + "\n".join(f"Deck {chr(66 + k)} : " + ", ".join(nom_carte(i, False) for i in a) for k, a in enumerate(autres)))
        if len(autres) < 3:
            sections.append(f"-# 💡 Je n'ai retrouvé que {len(autres)} autre{'s' if len(autres) > 1 else ''} deck{'s' if len(autres) > 1 else ''} de guerre dans ton historique "
                            "(l'API ne garde que tes 25 derniers combats). Pour être sûr qu'aucune carte n'est en commun, colle tes 4 decks dans le même message.")
    elif len(decks) > 1:
        sections.append("-# Plusieurs decks collés : seul le premier est analysé dans ce mode.")
    sections.append("-# Estimation basée sur le winrate des cartes chez les meilleurs joueurs, niveau des cartes pris en compte : "
                    "un conseil, pas une garantie.")
    embed = {"title": f"🔎 Analyse de deck — {nom_mode}", "description": "\n\n".join(sections)[:4000], "color": 3447003,
             "footer": {"text": "Autre deck ? Colle le lien (écris gdc, voie ou classe avant) · !aide pour les consignes"}}
    return None, embed


def construire_embed_gdc(decks, autres, stats, p0, combats, profil, source):
    """Analyse de plusieurs decks de guerre à la fois, sans carte commune.
    `autres` : decks retrouvés dans l'historique du joueur, qui ne sont pas modifiés (seules leurs cartes sont protégées)."""
    nb = len(decks)
    ids_liste = [d[0] for d in decks] + list(autres)
    evos = [[s > 0 for s in d[1]] for d in decks] + [[True] * 8 for _ in autres]
    tous = [c for ids in ids_liste for c in ids]
    doublons = sorted({c for c in tous if tous.count(c) > 1})
    tous_nouveaux, changements = optimiser_ensemble(ids_liste, evos, stats, p0, profil)
    nouveaux = tous_nouveaux[:nb]
    ids_liste_modif = ids_liste[:nb]
    avant = sum(note_deck(i, stats, p0, profil) for i in ids_liste_modif) / nb
    apres = sum(note_deck(i, stats, p0, profil) for i in nouveaux) / nb

    def nom(i):
        n = nom_fr(stats[i]["name"]) if i in stats else f"carte {i}"
        if profil and i in profil:
            n += f" (niv. {niveau_jeu(profil[i])}/16)"
        return n

    entete = (f"**{etiquette(avant, p0)}** · moyenne estimée de tes {nb} decks `≈{100 * avant:.1f}%` → "
              f"`≈{100 * apres:.1f}%` (moyenne du mode : `{100 * p0:.1f}%`)\n"
              f"-# {combats} combats analysés · Guerre de clan" + (" · données lues en direct" if source == "direct" else ""))
    if doublons:
        entete += ("\n⚠️ Cartes présentes dans plusieurs decks : " + ", ".join(nom_fr(stats[c]["name"]) if c in stats else str(c) for c in doublons)
                   + " (corrigé ci-dessous)")
    sections = [entete]
    for k, deck in enumerate(nouveaux):
        slots = [decks[k][1][p] if deck[p] == ids_liste[k][p] else 0 for p in range(8)]
        lignes = []
        for kk, sortant, entrant, origine in changements:
            if kk != k:
                continue
            lignes.append(f"🔁 {nom(sortant)} → **{nom(entrant)}**")
        el_av = elixir_moyen(ids_liste[k], stats, profil)
        el_ap = elixir_moyen(deck, stats, profil)
        note_av, note_ap = note_deck(ids_liste[k], stats, p0, profil), note_deck(deck, stats, p0, profil)
        bloc = f"**Deck {k + 1}** · `≈{100 * note_av:.1f}%` → `≈{100 * note_ap:.1f}%` · ⚡ `{el_av:.1f}` → `{el_ap:.1f}`\n"
        bloc += "\n".join(lignes) if lignes else "✅ inchangé"
        bloc += f"\n[📥 Copier le deck {k + 1}]({lien_deck(deck, slots, decks[k][2])})"
        sections.append(bloc)
    if autres:
        sections.append("**🛡️ Decks retrouvés dans ton historique** (non modifiés)\n"
                        + "\n".join(f"Deck {nb + k + 1} : " + ", ".join(nom_fr(stats[i]["name"]) if i in stats else str(i) for i in a) for k, a in enumerate(autres)))
    toutes = [c for d in tous_nouveaux for c in d]
    sections.append(f"-# Les {len(tous_nouveaux)} decks n'ont aucune carte en commun ({len(set(toutes))} cartes différentes). "
                    "Estimation basée sur le winrate des cartes chez les meilleurs joueurs, niveau des cartes pris en compte : un conseil, pas une garantie."
                    + ("" if profil else " Sans ton tag, je ne peux pas vérifier que tu possèdes ces cartes ni leur niveau."))
    return {"title": "🔎 Analyse de tes decks de guerre", "description": "\n\n".join(sections)[:4000], "color": 3447003,
            "footer": {"text": "Autre analyse ? Colle tes 4 liens (écris gdc avant) · !aide pour les consignes"}}


# ========================
# 🔹 Discord (bot)
# ========================
def discord(methode, chemin, **kw):
    """Appel à l'API Discord. Renvoie (code, json) ; réessaie en cas de limite de débit."""
    entetes = {"Authorization": f"Bot {BOT_TOKEN}", "User-Agent": "DiscordBot (clash-deck-bot, 1.0)"}
    for _ in range(3):
        try:
            r = requests.request(methode, f"{DISCORD_API}{chemin}", headers=entetes, timeout=15, **kw)
        except requests.RequestException as e:
            print(f"[Discord réseau] {e}", file=sys.stderr)
            time.sleep(2)
            continue
        if r.status_code == 429:
            try:
                attente = float(r.json().get("retry_after", 2))
            except ValueError:
                attente = 2
            time.sleep(attente + 0.5)
            continue
        try:
            corps = r.json() if r.text else None
        except ValueError:
            corps = None
        return r.status_code, corps
    return 0, None


COCHE = "%E2%9C%85"   # ✅


def repondre():
    manquants = [n for n, v in (("DISCORD_BOT_TOKEN", BOT_TOKEN), ("DISCORD_CHANNEL_ID", CHANNEL_ID), ("CR_API_KEY", API_KEY)) if not v]
    if manquants:
        print(f"[ERREUR] Variable(s) manquante(s) : {', '.join(manquants)}", file=sys.stderr)
        sys.exit(1)
    code, moi = discord("GET", "/users/@me")
    if code != 200 or not moi:
        print(f"[ERREUR] Jeton du bot refusé par Discord (code {code}).", file=sys.stderr)
        sys.exit(1)
    code, messages = discord("GET", f"/channels/{CHANNEL_ID}/messages?limit=50")
    if code != 200 or messages is None:
        print(f"[ERREUR] Impossible de lire le salon (code {code}) : le bot a-t-il accès au salon et à l'historique ?", file=sys.stderr)
        sys.exit(1)

    maintenant = maintenant_utc()
    if messages and all(not m.get("content") for m in messages if not (m.get("author") or {}).get("bot")) \
            and any(not (m.get("author") or {}).get("bot") for m in messages):
        print("[ATTENTION] Les messages sont vides : active « Message Content Intent » dans le portail développeur Discord.",
              file=sys.stderr)

    traites = 0
    for m in sorted(messages, key=lambda x: int(x["id"])):
        auteur = m.get("author") or {}
        if auteur.get("bot") or auteur.get("id") == moi.get("id"):
            continue
        if any(r.get("me") for r in m.get("reactions") or []):
            continue
        contenu = (m.get("content") or "").strip()
        texte = sans_accents(contenu)
        if texte.startswith(("!aide", "!help")):
            if traites >= MAX_DEMANDES_PAR_PASSAGE:
                break
            traites += 1
            code, _ = discord("PUT", f"/channels/{CHANNEL_ID}/messages/{m['id']}/reactions/{COCHE}/@me")
            if code in (200, 204):
                code, _ = discord("POST", f"/channels/{CHANNEL_ID}/messages",
                                  json={"content": CONSIGNES, "message_reference": {"message_id": m["id"], "fail_if_not_exists": False},
                                        "allowed_mentions": {"parse": [], "replied_user": False}})
                if code not in (200, 201):
                    discord("DELETE", f"/channels/{CHANNEL_ID}/messages/{m['id']}/reactions/{COCHE}/@me")
            continue
        # Une demande : soit « !deck ... », soit directement un lien « Copier le deck » du jeu collé dans le salon
        if not (texte.startswith("!deck") or re.search(r"copydeck\?deck=[\d;]+", texte)):
            continue
        try:
            age = (maintenant - datetime.datetime.fromisoformat(m["timestamp"])).total_seconds() / 3600
        except (KeyError, ValueError):
            age = 0
        if age > AGE_MAX_DEMANDE_H:
            continue
        if traites >= MAX_DEMANDES_PAR_PASSAGE:
            break
        traites += 1

        # On marque d'abord la demande comme prise en charge (évite les doublons en cas de problème)
        code, _ = discord("PUT", f"/channels/{CHANNEL_ID}/messages/{m['id']}/reactions/{COCHE}/@me")
        if code not in (200, 204):
            print(f"[ERREUR] Impossible d'ajouter une réaction (code {code}) : donne au bot la permission « Ajouter des réactions ».", file=sys.stderr)
            continue
        corps = {"message_reference": {"message_id": m["id"], "fail_if_not_exists": False},
                 "allowed_mentions": {"parse": [], "replied_user": False}}
        try:
            texte, embed = construire_reponse(*lire_demande(contenu))
            if embed:
                corps["embeds"] = [embed]
            else:
                corps["content"] = texte
        except ValueError as e:
            corps["content"] = str(e)
        code, _ = discord("POST", f"/channels/{CHANNEL_ID}/messages", json=corps)
        if code not in (200, 201):
            print(f"[ERREUR] Réponse non envoyée (code {code}).", file=sys.stderr)
            discord("DELETE", f"/channels/{CHANNEL_ID}/messages/{m['id']}/reactions/{COCHE}/@me")  # on réessaiera
            continue
        print(f"Demande {m['id']} traitée.")
    if not traites:
        print("Aucune nouvelle demande.")


# ========================
# 🔹 Programme principal
# ========================
def main(argv):
    mode = argv[1] if len(argv) > 1 else ""
    if mode == "repondre":
        repondre()
    elif mode == "collect":
        collecte_tous_modes()
    elif mode == "synergies":
        commande_synergies()
    else:
        print("[ERREUR] Mode inconnu. Utilise : repondre, collect ou synergies.", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main(sys.argv)