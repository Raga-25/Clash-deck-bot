"""Bot d'analyse de deck : un joueur colle son deck dans un salon Discord, le bot répond avec une
évaluation et des améliorations possibles.

Utilisation dans le salon :
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
        chemins = ["/locations/global/rankings/players", f"/locations/{LOCALISATION_FRANCE}/rankings/players"]
    for chemin in chemins:
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


def collecter(mode, tags, data):
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
            nouveaux += 1
        if plus_recent:
            data["last"][tag] = plus_recent
    return nouveaux


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
        n = collecter(mode, tags, data)
        nettoyer(data, mode, aujourdhui_utc())
        sauver_donnees(mode, data)
        print(f"{mode} : {len(tags)} joueurs lus, {n} nouveaux combats ({len(data['days'])} jours en mémoire)")
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
    return total / len(ids)


def elixir_moyen(ids, stats, profil):
    couts = []
    for i in ids:
        c = (profil.get(i, {}).get("elixirCost") if profil else None) or stats.get(i, {}).get("elixir")
        if c:
            couts.append(c)
    return sum(couts) / len(couts) if couts else 0.0


def ameliorer(ids, evo, stats, p0, profil):
    """Remplacements proposés : renvoie (nouveau_deck, [(sortant, entrant)])."""
    cartes = list(ids)
    if profil:
        pool = {i for i, c in profil.items() if i not in cartes and manque(c) <= MAX_NIVEAUX_MANQUANTS}
    else:
        pool = set(stats)
    pool = {i for i in pool if i in stats and stats[i]["games"] >= MIN_PARTIES_CARTE}
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
AIDE = ("Utilise : `!deck <mode> <lien du deck>`\n"
        "Modes : `gdc` (guerre), `classe` (Parcours des légendes), `voie` (voie des trophées).\n"
        "Le lien s'obtient dans le jeu avec « Copier le deck ».")


def lire_demande(contenu):
    """Renvoie (mode, ids, slots, tt, tag, mode_devine) ou lève ValueError avec un message."""
    texte = sans_accents(contenu)
    m_deck = re.search(r"deck=([\d;]+)", texte)
    if not m_deck:
        raise ValueError("Je ne trouve pas de deck dans ton message. " + AIDE)
    ids = [int(x) for x in m_deck.group(1).split(";") if x]
    if len(ids) != 8 or len(set(ids)) != 8:
        raise ValueError("Le lien doit contenir 8 cartes différentes. " + AIDE)
    avant_lien = re.sub(r"https?://\S+", " ", texte)
    mode, devine = None, False
    for mot in re.findall(r"[a-z]+", avant_lien.replace("!deck", " ")):
        if mot in ALIAS:
            mode = ALIAS[mot]
            break
    if mode is None:
        mode, devine = MODE_PAR_DEFAUT, True
    m_slots = re.search(r"slots=([\d;]+)", texte)
    slots = [int(x) for x in m_slots.group(1).split(";") if x] if m_slots else []
    if len(slots) != 8:
        slots = [0] * 8
    m_tt = re.search(r"tt=(\d+)", texte)
    m_id = re.search(r"[?&]id=([0-9a-z]+)", texte)
    tag = "#" + m_id.group(1).upper() if m_id else None
    return mode, ids, slots, int(m_tt.group(1)) if m_tt else None, tag, devine


def lien_deck(ids, slots, tt):
    lien = f"https://link.clashroyale.com/fr?clashroyale://copyDeck?deck={';'.join(str(i) for i in ids)}"
    lien += f"&slots={';'.join(str(s) for s in slots)}"
    if tt:
        lien += f"&tt={tt}"
    return lien


# ========================
# 🔹 Réponse
# ========================
def construire_reponse(mode, ids, slots, tt, tag, devine):
    """Renvoie (texte_simple, embed)."""
    data = charger_donnees(mode)
    stats, p0, combats = stats_cartes(data)
    nom_mode = MODES[mode]["nom"]
    if combats < MIN_COMBATS_MODE:
        return (f"Je n'ai pas encore assez de données pour le mode **{nom_mode}** "
                f"({combats} combats enregistrés, il m'en faut au moins {MIN_COMBATS_MODE}). Réessaie dans quelques jours.", None)

    profil = None
    if tag:
        p = api_get(f"/players/{enc(tag)}")
        if p and p.get("cards"):
            profil = {c["id"]: c for c in p["cards"]}
            if not all(i in profil for i in ids):
                profil = None
    evo = [s > 0 for s in slots]

    score = note_deck(ids, stats, p0, profil)
    el_avant = elixir_moyen(ids, stats, profil)
    nouveau, changements = ameliorer(ids, evo, stats, p0, profil)
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
                + (f"\n-# Mode non précisé : j'ai pris « {nom_mode} »." if devine else ""),
                "**🧩 Tes cartes** (winrate de chaque carte dans ce mode)\n" + "\n".join(lignes)]
    notes = points_attention(ids, stats, profil)
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
    sections.append("-# Estimation basée sur le winrate des cartes chez les meilleurs joueurs, niveau des cartes pris en compte : "
                    "un conseil, pas une garantie.")
    embed = {"title": f"🔎 Analyse de deck — {nom_mode}", "description": "\n\n".join(sections)[:4000], "color": 3447003}
    return None, embed


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
        if not sans_accents(contenu).startswith("!deck"):
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
    else:
        print("[ERREUR] Mode inconnu. Utilise : repondre ou collect.", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main(sys.argv)