"""Zelda Multiplayer – autoritativ PvP-server på UDP 27030.

JSON-meldinger: hello, create (size=4/10), join (lobby), team, ready,
start, score og spectate. Hver klient får egen lobbytilstand, serverklokke,
rundetid og listen over tilgjengelige spill. Story bruker ikke denne tjenesten.
"""
import hashlib
import hmac
import http.server
import os
import json
import math
import socket
import sqlite3
import threading
import time
import zlib

PORT = 27030
MAX_PLAYERS = 50
MAX_VISIBLE_PEERS = 49
STATE_INTERVAL = 0.05
TIME_SCALE = 120  # Spillets verdensklokke går ca. 120 spillsekunder per reelt sekund.
STARTER_RUBIES = 50
STARTER_INV = {"sticks": 10, "nuts": 10, "seeds": 30}
SHOP_CATALOG = {
    "sticks": {"price": 10, "qty": 5, "cap": 10},
    "nuts": {"price": 15, "qty": 5, "cap": 20},
    "seeds": {"price": 10, "qty": 10, "cap": 30},
    "bombs": {"price": 30, "qty": 5, "cap": 20},
    "potion": {"price": 25, "qty": 1, "cap": 3},
}
PVP_ITEM_CAPS = {k: v["cap"] for k, v in SHOP_CATALOG.items()}


def next_state_deadline(previous, now):
    """Keep the relay on its fixed cadence and skip deadlines already missed."""
    elapsed = max(0.0, now - previous)
    deadline = previous + (int(elapsed / STATE_INTERVAL) + 1) * STATE_INTERVAL
    return deadline if deadline > now else deadline + STATE_INTERVAL


def udp_state_packet(state, pose_v2):
    def encode(payload):
        return json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode()

    if pose_v2:
        packet = encode(state)
        if len(packet) <= 65507:
            return packet
        if len(packet) < 256 * 1024:
            compressed = b"OPZ1" + zlib.compress(packet, 1)
            if len(compressed) <= 65507:
                return compressed
    peers = [dict(peer, bones=peer["bones"].partition("|")[0]) for peer in state["peers"]]
    return encode(dict(state, peers=peers))


ARENAS = ("gohma", "sword", "zora")
CTF_ARENAS = ("gohma", "zora")   # 2026-11-23: CTF-brett   # 2026-11-23: PvP-brett (se ARENAS i oot_mp_gui.py)

class ZeldaServer:
    def __init__(self, db_path="stats.db"):
        self.lock = threading.RLock()
        self.db = sqlite3.connect(db_path, check_same_thread=False)
        self.db.execute("create table if not exists events(t real, player text, kind text, data text)")
        self.db.execute("create table if not exists matches(id integer primary key, started real, ended real, red int, blue int)")
        self.db.execute(
            "create table if not exists player_profiles("
            "name text primary key, rubies integer not null default 0, "
            "wins integer not null default 0, losses integer not null default 0, "
            "kills integer not null default 0, updated real not null)"
        )
        self.db.execute(
            "create table if not exists player_inventory("
            "player text not null, item_id text not null, qty integer not null default 0, "
            "updated real not null, primary key(player, item_id))"
        )
        self.db.execute(   # v0.94.268: eget Story-inventar per spiller (navn), lagret som JSON
            "create table if not exists story_inventory(name text primary key, data text not null, updated real not null)"
        )
        self.db.execute(   # v0.94.285: konto per spillernavn. Lagrer bare salt + PBKDF2 av klientens avledede nøkkel (aldri passordet).
            "create table if not exists accounts(name text primary key, salt blob not null, hash blob not null, created real not null)"
        )
        self.db.execute(
            "create table if not exists transactions("
            "id integer primary key autoincrement, t real not null, player text not null, "
            "kind text not null, delta_rubies integer not null, item_id text, "
            "delta_qty integer not null, detail text)"
        )
        self.db.commit()
        self.players = {}
        self.invites = {}          # mottaker -> [{'from', 'lobby', 't'}]
        self.presence = []         # hendelser: {'seq','kind':'joined'|'left','name','lobby','team','reason','t'}
        self.pres_seq = 0
        self.lobbies = {0: self.new_lobby(0, "Public", 50, None)}
        self.next_lobby = 1
        self.chat_channels = {}    # (mode, lobby) -> siste 100 meldinger
        self.chat_seq = 0
        self._clock_started = None

    def day_time(self, now):
        """Én felles spillklokke, initialisert fra første aktive klient."""
        if self._clock_started is None:
            self._clock_started = now
        return (int(self._clock_started) + int((now - self._clock_started) * TIME_SCALE)) % 86400

    def world_weather(self, now):
        """Naturlig felles værsyklus: Bluesky(0), Cloudy(4), Rain(1), Thunderstorm(3). Bytter hvert 4–8 min."""
        if getattr(self, "_weather_cur", None) is None or now >= getattr(self, "_weather_next", 0.0):
            import random
            cur = getattr(self, "_weather_cur", None)
            if cur is None:
                nxt = 0
            else:
                # Naturlige overganger som i spillet: sol -> skyet -> regn -> torden -> skyet -> sol
                trans = {
                    0: (0, 0, 4, 4, 1),
                    4: (0, 0, 4, 1, 1, 3),
                    1: (4, 4, 1, 3, 0),
                    3: (1, 1, 4, 4),
                }
                nxt = random.choice(trans.get(cur, (0, 4, 1)))
            self._weather_cur = nxt
            self._weather_next = now + random.uniform(240.0, 480.0)
        return self._weather_cur

    @staticmethod
    def new_lobby(lobby_id, name, capacity, host, game_mode="ctf", arena="gohma"):
        return {"id": lobby_id, "name": name, "capacity": capacity, "host": host,
                "game_mode": game_mode if game_mode in ("ctf", "deathmatch", "story") else "ctf",
                "arena": arena if arena in ARENAS else "gohma",   # 2026-11-23: brett (gohma = Deku-treets bossrom, sword = sverd-banen)
                "score": {"Red": 0, "Blue": 0}, "round": 1, "target": 5,
                "started": False, "started_at": None, "created": time.time()}

    def members(self, lobby_id, now):
        return {name: p for name, p in self.players.items()
                if p["lobby"] == lobby_id and now - p["seen"] < 15}

    def event(self, name, kind, message, now):
        self.db.execute("insert into events values(?,?,?,?)", (now, name, kind, json.dumps(message)))
        self.db.commit()

    def ensure_profile(self, name, now):
        """Opprett fast PvP-profil og startbeholdning hvis spilleren er ny (kun PvP)."""
        row = self.db.execute("select 1 from player_profiles where name=?", (name,)).fetchone()
        if row is not None:
            return
        self.db.execute("insert into player_profiles(name,rubies,wins,losses,kills,updated) values(?,?,0,0,0,?)",
                        (name, STARTER_RUBIES, now))
        for item_id, qty in STARTER_INV.items():
            self.db.execute("insert into player_inventory(player,item_id,qty,updated) values(?,?,?,?)",
                            (name, item_id, qty, now))
        self.db.execute("insert into transactions(t,player,kind,delta_rubies,item_id,delta_qty,detail) values(?,?,?,?,?,?,?)",
                        (now, name, "starter", STARTER_RUBIES, None, 0, "starter profile"))
        self.db.commit()

    def get_profile(self, name):
        """Les PvP-profil og lagret PvP-inventar for spilleren."""
        row = self.db.execute("select rubies,wins,losses,kills from player_profiles where name=?", (name,)).fetchone()
        if row is None:
            return {"rubies": 0, "wins": 0, "losses": 0, "kills": 0, "inventory": {}}
        inv_rows = self.db.execute("select item_id,qty from player_inventory where player=? order by item_id", (name,)).fetchall()
        return {"rubies": row[0], "wins": row[1], "losses": row[2], "kills": row[3],
                "inventory": {item_id: qty for item_id, qty in inv_rows}}

    def credit_reward(self, name, delta_rubies=0, wins=0, losses=0, kills=0, kind="reward", detail="", now=None):
        """Oppdater PvP-profil atomisk ved poeng, KO eller seier."""
        now = time.time() if now is None else now
        self.ensure_profile(name, now)
        self.db.execute(
            "update player_profiles set rubies=max(0,rubies+?), wins=wins+?, losses=losses+?, kills=kills+?, updated=? where name=?",
            (int(delta_rubies), int(wins), int(losses), int(kills), now, name),
        )
        if delta_rubies:
            self.db.execute("insert into transactions(t,player,kind,delta_rubies,item_id,delta_qty,detail) values(?,?,?,?,?,?,?)",
                            (now, name, kind, int(delta_rubies), None, 0, detail))
        self.db.commit()

    def buy_item(self, name, item_id, now):
        """Kjøp ett PvP-objekt for rubies atomisk i SQLite."""
        self.ensure_profile(name, now)
        spec = SHOP_CATALOG.get(item_id)
        if spec is None:
            return f"Ukjent vare '{item_id}' ({', '.join(SHOP_CATALOG)})"
        row = self.db.execute("select rubies from player_profiles where name=?", (name,)).fetchone()
        cur_rubies = row[0] if row else 0
        if cur_rubies < spec["price"]:
            return f"Ikke nok rubies ({cur_rubies}/{spec['price']})"
        irow = self.db.execute("select qty from player_inventory where player=? and item_id=?", (name, item_id)).fetchone()
        cur_qty = irow[0] if irow else 0
        if cur_qty >= spec["cap"]:
            return f"Full beholdning av {item_id} ({cur_qty}/{spec['cap']})"
        add = min(spec["qty"], spec["cap"] - cur_qty)
        new_qty = cur_qty + add
        self.db.execute("update player_profiles set rubies=rubies-?, updated=? where name=?", (spec["price"], now, name))
        self.db.execute(
            "insert into player_inventory(player,item_id,qty,updated) values(?,?,?,?) "
            "on conflict(player,item_id) do update set qty=excluded.qty, updated=excluded.updated",
            (name, item_id, new_qty, now),
        )
        self.db.execute("insert into transactions(t,player,kind,delta_rubies,item_id,delta_qty,detail) values(?,?,?,?,?,?,?)",
                        (now, name, "buy", -spec["price"], item_id, add, f"{cur_qty}->{new_qty}"))
        self.db.commit()
        return None

    def consume_inventory(self, name, items, now):
        """Registrer forbruk av PvP-gjenstander; klienten kan aldri øke antall utenom serverkjøp."""
        if not isinstance(items, dict):
            return
        self.ensure_profile(name, now)
        changed = False
        for item_id, raw_qty in items.items():
            if item_id not in PVP_ITEM_CAPS or not isinstance(raw_qty, int):
                continue
            row = self.db.execute("select qty from player_inventory where player=? and item_id=?", (name, item_id)).fetchone()
            cur_qty = row[0] if row else 0
            new_qty = max(0, min(cur_qty, raw_qty))
            if new_qty < cur_qty:
                self.db.execute(
                    "update player_inventory set qty=?, updated=? where player=? and item_id=?",
                    (new_qty, now, name, item_id),
                )
                changed = True
        if changed:
            self.db.commit()

    def record_point(self, name, kind, message, lobby, team, now):
        """Registrer ett poeng og avslutt kampen ved minst 5 poeng og >= 2 poengs ledelse."""
        lobby["score"][team] += 1
        self.event(name, kind, message, now)
        members = self.members(lobby["id"], now)
        for member_name, member in members.items():
            if member.get("team") == team:
                delta_r = 15 if kind == "score" else 10
                kills = 1 if kind == "eliminated" else 0
                self.credit_reward(member_name, delta_rubies=delta_r, kills=kills, kind=kind, detail=f"lobby#{lobby['id']}", now=now)
        red, blue = lobby["score"]["Red"], lobby["score"]["Blue"]
        if max(red, blue) >= lobby["target"] and abs(red - blue) >= 2:
            started = lobby["started_at"] or now
            winner = "Red" if red > blue else "Blue"
            for member_name, member in members.items():
                if member.get("team") == winner:
                    self.credit_reward(member_name, delta_rubies=50, wins=1, kind="match_win", detail=f"{blue}-{red}", now=now)
                elif member.get("team") in ("Red", "Blue"):
                    self.credit_reward(member_name, delta_rubies=15, losses=1, kind="match_loss", detail=f"{blue}-{red}", now=now)
            self.db.execute("insert into matches(started,ended,red,blue) values(?,?,?,?)",
                            (started, now, red, blue))
            self.db.commit()
            lobby["score"] = {"Red": 0, "Blue": 0}
            lobby["round"] += 1
            lobby["started"] = False
            lobby["started_at"] = None
            for member in members.values():
                member["ready"] = False

    PRESENT_TIMEOUT = 3.0   # klienten sier hello hvert 1 s

    def presence_event(self, kind, name, reason, now):
        p = self.players.get(name) or {}
        self.pres_seq += 1
        self.presence.append({'seq': self.pres_seq, 'kind': kind, 'name': name, 'lobby': p.get('lobby', 0),
                              'team': p.get('team'), 'reason': reason, 't': now})
        del self.presence[:-50]

    def check_timeouts(self, now):
        for n, p in self.players.items():
            if p.get('present') and now - p['seen'] > self.PRESENT_TIMEOUT:
                p['present'] = False
                self.presence_event('left', n, 'timeout', now)

    def record_hit(self, name, message, now):
        attacker = self.players[name]
        lobby = self.lobbies[attacker["lobby"]]
        target = message.get("target")
        victim = self.players.get(target) if isinstance(target, str) else None
        if (not lobby["started"] or lobby["game_mode"] != "deathmatch"
                or lobby["capacity"] not in (20, 50) or message.get("match") != lobby["started_at"]):
            return "Treffet tilhører ingen aktiv stor Deathmatch"
        if (not victim or victim["lobby"] != lobby["id"] or not victim.get("present")
                or attacker["team"] not in ("Red", "Blue") or victim["team"] not in ("Red", "Blue")
                or attacker["team"] == victim["team"]):
            return "Ugyldig motspiller"
        if any(p.get("banc") != "HyruleField_Child" or now - p.get("pose_at", float("-inf")) > 1.5
               for p in (attacker, victim)):
            return "Begge spillere må ha fersk posisjon i arenaen"
        down_until = lobby["down_until"]
        if now < max(down_until.get(name, 0), down_until.get(target, 0)):
            return "Spilleren er slått ned"
        attack = message.get("attack")
        if attack not in ("swing", "spin"):
            return "Ukjent angrep"
        x, y, z = attacker["pos"]
        tx, ty, tz = victim["pos"]
        if math.hypot(x - tx, z - tz) > (2.4 if attack == "spin" else 2.0) or abs(y - ty) > 1.5:
            return "Motspilleren er utenfor rekkevidde"
        seq = message.get("seq")
        previous, last_time = lobby["last_hits"].get(name, (0, float("-inf")))
        if type(seq) is not int or not previous < seq <= 2**31 - 1 or now - last_time < 0.45:
            return "Treffet er allerede behandlet eller kom for tidlig"
        lobby["last_hits"][name] = (seq, now)
        damage = lobby["damage"]
        hp = lobby["hp"]
        amount = 8 if attack == "spin" else 4
        damage[target] = damage.get(target, 0) + amount
        remaining = hp.get(target, 12) - amount
        if remaining <= 0:
            hp.pop(target, None)
            down_until[target] = now + 5.0
            self.record_point(target, "eliminated", {"attacker": name}, lobby, attacker["team"], now)
        else:
            hp[target] = remaining
        return None

    def check_account(self, name, key, now):
        """v0.94.285: «open» = navnet har ingen konto og ingen nøkkel ble sendt; «created» = første nøkkel tar navnet;
        «ok» = riktig nøkkel; «denied» = navnet har konto og nøkkelen mangler eller er feil."""
        key = key if isinstance(key, str) and 16 <= len(key) <= 128 else None
        cache = self.__dict__.setdefault("_auth_ok", {})   # navn -> sha256(nøkkel) som allerede er sjekket (PBKDF2 er treg)
        if key is not None and cache.get(name) == hashlib.sha256(key.encode()).digest():
            return "ok"
        row = self.db.execute("select salt, hash from accounts where name=?", (name,)).fetchone()
        if row is None:
            if key is None:
                return "open"
            salt = os.urandom(16)
            digest = hashlib.pbkdf2_hmac("sha256", key.encode(), salt, 200_000)
            self.db.execute("insert into accounts(name,salt,hash,created) values(?,?,?,?)", (name, salt, digest, now))
            self.db.commit()
            cache[name] = hashlib.sha256(key.encode()).digest()
            return "created"
        if key is None:
            return "denied"
        digest = hashlib.pbkdf2_hmac("sha256", key.encode(), row[0], 200_000)
        if hmac.compare_digest(digest, row[1]):
            cache[name] = hashlib.sha256(key.encode()).digest()
            return "ok"
        return "denied"

    def handle(self, message, addr, now=None, *, reply_to_pose=True):
        with self.lock:
            return self._handle_locked(message, addr, now, reply_to_pose=reply_to_pose)

    def _handle_locked(self, message, addr, now=None, *, reply_to_pose=True):
        now = time.time() if now is None else now
        name = str(message.get("name") or f"{addr[0]}:{addr[1]}")[:40]
        team = message.get("team") if message.get("team") in ("Red", "Blue") else None
        player = self.players.get(name)
        if message.get("t") == "hit":
            self.check_timeouts(now)
            if not player or not player.get("present") or (player["addr"] != addr and player["addr"][1] != 0):
                return {"t": "state", "error": "Ukjent avsender for treff"}
            return self.response_for(name, now, self.record_hit(name, message, now))
        if player is None:
            player = {"addr": addr, "seen": now, "lobby": 0, "team": team, "ready": False}
            self.players[name] = player
            if self.lobbies[0]["host"] is None:
                self.lobbies[0]["host"] = name
        self.check_timeouts(now)
        player.update(addr=addr, seen=now)
        if message.get("t") == "bye":
            if player.get('present'):
                player['present'] = False
                self.presence_event('left', name, 'bye', now)
            player['seen'] = now - 60   # regnes som borte med en gang
            return self.response_for(name, now)
        if not player.get('present'):
            player['present'] = True
            self.presence_event('joined', name, 'connect', now)
        if "team" in message and player["team"] != team:
            player["team"] = team
            player["ready"] = False
        assets = message.get("assets")
        if isinstance(assets, str) and len(assets) == 64 and all(c in "0123456789abcdef" for c in assets):
            player["assets"] = assets
        banc = message.get("banc")
        if isinstance(banc, str):
            banc = banc.strip()
            if banc and len(banc) <= 64 and banc.replace("_", "").isalnum():
                if player.get("banc") != banc:
                    player.pop("pose_at", None)
                player["banc"] = banc
        model = message.get("model")
        if model in ("Green", "Blue", "Red", "Pink", "Orange", "Yellow", "Cyan", "Purple", "White", "Black", "No tunic"):
            player["model"] = model
        mode = message.get("mode")
        if mode in ("Story", "PvP"):
            player["mode"] = mode
        elif "mode" not in player:
            player["mode"] = "PvP"
        current_lobby = self.lobbies.get(player.get("lobby", 0), self.lobbies[0])
        if ((player["mode"] == "Story" and current_lobby["game_mode"] != "story" and player.get("lobby") != 0)
                or (player["mode"] == "PvP" and current_lobby["game_mode"] == "story")):
            player.update(lobby=0, ready=False, team=None)
        color = message.get("color")
        if color in ("Grønn", "Blå", "Rød", "Lilla", "Gull", "Hvit"):
            player["color"] = color
        pos = message.get("pos")
        if (isinstance(pos, (list, tuple)) and len(pos) == 3
                and all(isinstance(v, (int, float)) and not isinstance(v, bool)
                        and math.isfinite(float(v)) and -1e5 <= float(v) <= 1e5 for v in pos)):
            player["pos"] = [round(float(v), 3) for v in pos]
            player["pose_at"] = now
        yaw = message.get("yaw")
        if isinstance(yaw, (int, float)) and not isinstance(yaw, bool) and math.isfinite(float(yaw)):
            player["yaw"] = round(float(yaw), 4)
        anim = message.get("anim")
        if isinstance(anim, str) and len(anim) <= 40:
            player["anim"] = anim
        hearts = message.get("hearts")
        if (isinstance(hearts, (list, tuple)) and len(hearts) == 2
                and all(isinstance(v, int) and not isinstance(v, bool) for v in hearts)
                and 0 <= hearts[0] <= 80 and 4 <= hearts[1] <= 80):
            player["hearts"] = list(hearts)
        if isinstance(message.get("follow"), bool):
            player["follow"] = message["follow"]
        bones = message.get("bones")
        if message.get("t") in ("hello", "pose"):
            player["pose_v2"] = message.get("pose_v2") is True
        if isinstance(bones, str) and len(bones) <= 2048 and bones.isascii():
            player["bones"] = bones
        kind = message.get("t", "hello")
        # v0.94.286: kontosjekk for alle meldinger med nøkkel (cachet); uten nøkkel beholdes forrige status
        if "key" in message or "_auth" not in player:
            k_ = message.get("key")
            if player.get("_auth_key") != k_ or "_auth" not in player:
                player["_auth"] = self.check_account(name, k_, now); player["_auth_key"] = k_
        if kind != "pose":
            self.ensure_profile(name, now)
        error = None

        if kind == "story_create":
            lobby_name = " ".join(str(message.get("lobby_name") or "").split())[:24]
            password = str(message.get("password") or "")[:64]
            if player["mode"] != "Story":
                error = "Story-lobby kan bare opprettes i Story-modus"
            elif not lobby_name or any(ord(c) < 32 for c in lobby_name):
                error = "Skriv inn et lobbynavn"
            else:
                lobby_id = self.next_lobby
                self.next_lobby += 1
                lobby = self.new_lobby(lobby_id, lobby_name, 50, name, "story")
                lobby.update(password=password, empty_since=None)
                self.lobbies[lobby_id] = lobby
                player.update(lobby=lobby_id, ready=False, team=None)
        elif kind == "story_join":
            try:
                lobby = self.lobbies[int(message.get("lobby"))]
            except (ValueError, TypeError, KeyError):
                lobby = None
            if player["mode"] != "Story":
                error = "Story-lobby kan bare brukes i Story-modus"
            elif lobby is None or (lobby["id"] != 0 and lobby["game_mode"] != "story"):
                error = "Story-lobbien finnes ikke"
            elif lobby.get("password") and message.get("password") != lobby["password"] and player["lobby"] != lobby["id"]:
                error = "Feil passord"
            elif len(self.members(lobby["id"], now)) >= lobby["capacity"] and player["lobby"] != lobby["id"]:
                error = "Lobbien er full"
            else:
                player.update(lobby=lobby["id"], ready=False, team=None)
        elif kind == "story_leave":
            player.update(lobby=0, ready=False, team=None)
        elif kind == "chat":
            text = str(message.get("text") or "").strip()[:240]
            if text:
                self.chat_seq += 1
                color = player.get("color") if player.get("color") in ("Grønn", "Blå", "Rød", "Lilla", "Gull", "Hvit") else "Hvit"
                key = (player["mode"], player["lobby"])
                channel = self.chat_channels.setdefault(key, [])
                channel.append({"seq": self.chat_seq, "name": name, "text": text, "color": color})
                del channel[:-100]
        elif kind == "create":
            capacity = {2: 2, 4: 4, 10: 10, 20: 20, 50: 50}.get(message.get("size"))
            game_mode = message.get("game_mode", "ctf")
            arena = message.get("arena") or "gohma"
            if capacity is None:
                error = "Velg 1v1, 2v2, 5v5, 10v10 eller 25v25"
            elif game_mode not in ("ctf", "deathmatch"):
                error = "Ukjent spilltype"
            elif arena not in ARENAS:
                error = "Ukjent brett"
            elif game_mode == "ctf" and arena not in CTF_ARENAS:
                error = "Capture the flag finnes bare i Gohma-rommet og Zora's Domain"
            else:
                lobby_id = self.next_lobby
                self.next_lobby += 1
                lobby = self.new_lobby(lobby_id, f"Game {lobby_id} ({capacity // 2}v{capacity // 2})", capacity, name, game_mode,
                                       arena)
                self.lobbies[lobby_id] = lobby
                player.update(lobby=lobby_id, ready=False)
                self.event(name, "create", message, now)
        elif kind == "join":
            try:
                lobby_id = int(message.get("lobby"))
                lobby = self.lobbies[lobby_id]
            except (ValueError, TypeError, KeyError):
                lobby = None
            if lobby is None:
                error = "Lobbien finnes ikke"
            elif len(self.members(lobby["id"], now)) >= lobby["capacity"] and player["lobby"] != lobby["id"]:
                error = "Lobbien er full"
            elif lobby["started"] and player["lobby"] != lobby["id"]:
                error = "Kampen har allerede startet"
            else:
                player.update(lobby=lobby["id"], ready=False)
                self.invites[name] = [i for i in self.invites.get(name, []) if i["lobby"] != lobby["id"]]
        elif kind == "watch":   # tilskuer: kan gå inn også i full/startet kamp, uten lag
            try:
                lobby = self.lobbies[int(message.get("lobby"))]
            except (ValueError, TypeError, KeyError):
                lobby = None
            if lobby is None:
                error = "Lobbien finnes ikke"
            else:
                player.update(lobby=lobby["id"], ready=False, team=None)
        elif kind == "leave":
            player.update(lobby=0, ready=False)
            self.presence_event('left_game', name, 'leave', now)
        elif kind == "invite":
            target = str(message.get("to") or "")[:40]
            if target not in self.players or target == name:
                error = "Spilleren er ikke pålogget"
            elif player["lobby"] == 0:
                error = "Lag eller bli med i en kamp før du inviterer"
            else:
                lst = [i for i in self.invites.get(target, []) if i["lobby"] != player["lobby"]]
                lst.append({"from": name, "lobby": player["lobby"], "t": now})
                self.invites[target] = lst[-5:]
        elif kind == "decline":
            lid = message.get("lobby")
            self.invites[name] = [i for i in self.invites.get(name, []) if i["lobby"] != lid]
        elif kind in ("team", "spectate"):
            player["team"] = None if kind == "spectate" else team
            player["ready"] = False
        elif kind == "mode":
            lobby = self.lobbies[player["lobby"]]
            game_mode = message.get("game_mode")
            if lobby["host"] != name:
                error = "Bare lobbyverten kan velge spilltype"
            elif lobby["started"]:
                error = "Spilltypen kan ikke endres under en kamp"
            elif game_mode not in ("ctf", "deathmatch"):
                error = "Ukjent spilltype"
            elif game_mode == "ctf" and lobby.get("arena", "gohma") not in CTF_ARENAS:
                error = "Capture the flag finnes bare i Gohma-rommet og Zora's Domain"
            else:
                lobby["game_mode"] = game_mode
                for member in self.members(lobby["id"], now).values():
                    member["ready"] = False
        elif kind == "ready":
            player["ready"] = bool(message.get("ready", True))
        elif kind == "start":
            lobby = self.lobbies[player["lobby"]]
            if lobby["host"] != name:
                error = "Bare serververten kan starte"
            elif len(self.members(lobby["id"], now)) < 2:
                error = "Minst to spillere trengs"
            else:
                lobby.update(started=True, started_at=now, score={"Red": 0, "Blue": 0})
                lobby.update(last_hits={}, damage={}, hp={}, down_until={})
                self.event(name, "start", message, now)
        elif kind == "stop":
            lobby = self.lobbies[player["lobby"]]
            if lobby["host"] != name:
                error = "Bare lobbyverten kan stoppe kampen"
            else:
                lobby.update(started=False, started_at=None, score={"Red": 0, "Blue": 0})
                for member in self.members(lobby["id"], now).values():
                    member["ready"] = False
                self.event(name, "stop", message, now)
        elif kind == "score" and team in ("Red", "Blue"):
            lobby = self.lobbies[player["lobby"]]
            if lobby["game_mode"] == "ctf" and lobby["started"] and lobby["host"] == name:
                self.record_point(name, "score", message, lobby, team, now)
        elif kind == "eliminated" and team in ("Red", "Blue"):
            lobby = self.lobbies[player["lobby"]]
            scoring_team = "Blue" if team == "Red" else "Red"
            if lobby["game_mode"] == "deathmatch" and lobby["started"] and lobby["capacity"] not in (20, 50):
                self.record_point(name, "eliminated", message, lobby, scoring_team, now)
        elif kind == "buy":
            if player.get("_auth") == "denied":   # v0.94.286: beskyttet navn – bare eieren kan bruke rubiene
                error = "Feil passord for dette navnet"
            else:
                error = self.buy_item(name, str(message.get("item_id") or "").strip().lower(), now)
        elif kind == "inv_consume":
            if player.get("_auth") != "denied":
                self.consume_inventory(name, message.get("items") or {}, now)
        elif kind == "acct_change":   # v0.94.286: bytt passord – krever gyldig nåværende nøkkel
            new_key = message.get("new_key")
            if player.get("_auth") in ("ok", "created") and isinstance(new_key, str) and 16 <= len(new_key) <= 128:
                salt = os.urandom(16)
                self.db.execute("update accounts set salt=?, hash=? where name=?",
                                (salt, hashlib.pbkdf2_hmac("sha256", new_key.encode(), salt, 200_000), name))
                self.db.commit()
                self.__dict__.setdefault("_auth_ok", {})[name] = hashlib.sha256(new_key.encode()).digest()
                player["_auth"], player["_auth_key"] = "ok", new_key
                player["_acct_msg"] = ("changed", now)
            else:
                player["_acct_msg"] = ("change_denied", now)
        elif kind == "inv_save":   # v0.94.268: lagre eget Story-inventar (siste versjon vinner)
            inv = message.get("inv")
            auth = player.get("_auth")
            if auth == "denied":
                player["_send_inv_until"] = now + 3.0   # svaret bærer feilen
            elif isinstance(inv, dict) and len(json.dumps(inv)) <= 16384:
                self.db.execute("insert into story_inventory(name,data,updated) values(?,?,?) "
                                "on conflict(name) do update set data=excluded.data, updated=excluded.updated",
                                (name, json.dumps(inv, sort_keys=True), now))
                self.db.commit()
        elif kind == "inv_get":
            player["_send_inv_until"] = now + 3.0   # svaret går med de neste state-pakkene i 3 s

        # Tomme private Story-kanaler ryddes bort etter nøyaktig 10 minutter.
        for lobby_id, lobby in list(self.lobbies.items()):
            if lobby_id == 0 or lobby.get("game_mode") != "story":
                continue
            if self.members(lobby_id, now):
                lobby["empty_since"] = None
            elif lobby.get("empty_since") is None:
                lobby["empty_since"] = now
            elif now - lobby["empty_since"] >= 600:
                del self.lobbies[lobby_id]
                self.chat_channels.pop(("Story", lobby_id), None)

        # Flytt verten hvis vedkommende har forsvunnet.
        for lobby in self.lobbies.values():
            members = self.members(lobby["id"], now)
            if lobby["host"] not in members:
                lobby["host"] = next(iter(members), None)
        if kind == "pose" and not reply_to_pose and error is None:
            return None
        return self.response_for(name, now, error)

    def visible_peers(self, name, now):
        """AOI (Area of Interest): returner opptil 49 nærmeste aktive spillere i samme sone (50 totalt)."""
        me = self.players.get(name) or {}
        my_lobby = me.get("lobby")
        my_banc = me.get("banc") or ""
        my_pos = me.get("pos")
        my_mode = me.get("mode", "PvP")
        cand = []
        for n, p in self.players.items():
            if n == name or not p.get("present") or p["lobby"] != my_lobby or p.get("mode", "PvP") != my_mode:
                continue
            p_banc = p.get("banc") or ""
            if my_banc and p_banc and p_banc != my_banc:
                continue
            p_pos = p.get("pos")
            dist = math.dist(my_pos, p_pos) if (my_pos and p_pos) else 999999.0
            cand.append((dist, n, p))
        cand.sort(key=lambda item: (item[0], item[1]))
        out = []
        for dist, n, p in cand[:MAX_VISIBLE_PEERS]:
            out.append({
                "name": n,
                "team": p.get("team"),
                "lobby": p.get("lobby", 0),
                "zone": p.get("banc") or "",
                "model": p.get("model") or "",
                "color": p.get("color") or "",
                "pos": p.get("pos"),
                "yaw": p.get("yaw", 0.0),
                "anim": p.get("anim") or "",
                "hearts": p.get("hearts"),
                "bones": p.get("bones") or "",
                "dist": round(dist, 2) if dist < 999990.0 else None,
            })
        return out

    def response_for(self, name, now, error=None):
        player = self.players[name]
        lobby = self.lobbies[player["lobby"]]
        members = self.members(lobby["id"], now)
        elapsed = max(0, int(now - lobby["started_at"])) if lobby["started_at"] is not None else 0
        summaries = []
        for item in sorted(self.lobbies.values(), key=lambda x: x["id"]):
            count = len(self.members(item["id"], now))
            if count or item["id"] == player["lobby"] or item.get("game_mode") == "story":
                summaries.append({"id": item["id"], "name": item["name"], "players": count,
                                  "capacity": item["capacity"], "started": item["started"], "host": item["host"],
                                  "game_mode": item["game_mode"], "arena": item.get("arena", "gohma"),
                                  "protected": bool(item.get("password"))})
        asset_hashes = {p.get("assets") for p in self.members(lobby["id"], now).values() if p.get("assets")}
        same_channel = lambda p: (p.get("present") and p.get("mode", "PvP") == player.get("mode", "PvP")
                                  and (player.get("mode") != "Story" or p.get("lobby") == player.get("lobby")))
        story_inv = None
        if now < player.get("_send_inv_until", 0):
            if player.get("_auth") == "denied":
                story_inv = {"inv": None, "updated": None, "error": "wrong_password"}
            else:
                row = self.db.execute("select data, updated from story_inventory where name=?", (name,)).fetchone()
                story_inv = {"inv": json.loads(row[0]), "updated": row[1]} if row else {"inv": None, "updated": None}
                story_inv["account"] = player.get("_auth") or "open"
        return {"t": "state", "story_inv": story_inv, "score": lobby["score"], "round": lobby["round"],
                "players": {n: p["team"] for n, p in members.items()},
                "members": [{"name": n, "team": p["team"], "ready": p["ready"],
                             "assets": (p.get("assets") or "")[:12]} for n, p in members.items()],
                "assets_match": len(asset_hashes) < 2,
                "lobby": {"id": lobby["id"], "name": lobby["name"], "host": lobby["host"],
                          "capacity": lobby["capacity"], "started": lobby["started"], "started_at": lobby["started_at"],
                          "elapsed": elapsed, "game_mode": lobby["game_mode"], "arena": lobby.get("arena", "gohma")},
                "lobbies": summaries, "profile": None if player.get("_auth") == "denied" else self.get_profile(name), "shop": SHOP_CATALOG,
                "account": player.get("_auth"), "acct_msg": (player.get("_acct_msg") or (None, 0))[0] if now - (player.get("_acct_msg") or (None, 0))[1] < 3 else None,
                "online": [{"name": n, "lobby": p["lobby"]} for n, p in self.players.items()
                           if p.get('present') and n != name and p.get("mode", "PvP") == player.get("mode", "PvP")],
                "present": sorted(n for n, p in self.players.items() if same_channel(p)),
                "roster": [{"name": n, "zone": p.get("banc") or "", "model": p.get("model") or "",
                            "color": p.get("color") or "", "mode": p.get("mode", "PvP"),
                            "follow": p.get("follow") is True}
                           for n, p in sorted(self.players.items()) if same_channel(p)],
                "peers": self.visible_peers(name, now),
                "chat": list(self.chat_channels.get((player["mode"], player["lobby"]), ())[-50:]),
                "damage_total": lobby.get("damage", {}).get(name, 0) if lobby["started"] else 0,
                "presence": [e for e in self.presence[-20:]
                             if e.get("name") == name or (e.get("name") in self.players
                                 and same_channel(self.players[e["name"]]))], "presence_seq": self.pres_seq,
                "invites": [i for i in self.invites.get(name, []) if now - i["t"] < 120 and i["lobby"] in self.lobbies],
                "server_time": now, "day_time": self.day_time(now), "weather": self.world_weather(now),
                "time_scale": TIME_SCALE, "error": error}


def make_http_handler(server):
    class TunnelHandler(http.server.BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, fmt, *args):
            return

        def _client_addr(self):
            fwd = self.headers.get("CF-Connecting-IP") or self.headers.get("X-Forwarded-For")
            if fwd:
                return (fwd.split(",")[0].strip(), 0)
            return (self.client_address[0], 0)

        def _send_json(self, payload, status=200):
            body = json.dumps(payload).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Connection", "keep-alive")
            self.end_headers()
            self.wfile.write(body)

        def do_GET(self):
            self._send_json({"ok": True, "service": "zelda-server", "port": PORT})

        def do_POST(self):
            try:
                length = int(self.headers.get("Content-Length") or 0)
            except ValueError:
                length = 0
            if not (0 < length <= 65535):
                self._send_json({"t": "state", "error": "Ugyldig pakkestørrelse"}, 400)
                return
            try:
                raw = self.rfile.read(length)
                message = json.loads(raw)
                response = server.handle(message, self._client_addr())
                self._send_json(response or {"t": "state"})
            except Exception as exc:  # noqa: BLE001
                self._send_json({"t": "state", "error": str(exc)}, 400)

    return TunnelHandler


def reset_account(name):
    """v0.94.286: glemt passord – kjør på serveren: python3 server.py --reset-account <navn>"""
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "stats.db")
    if not os.path.isfile(path):
        raise SystemExit(f"fant ikke databasen {path}")
    db = sqlite3.connect(path)
    n = db.execute("delete from accounts where name=?", (name,)).rowcount
    db.commit()
    print(f"konto '{name}': {'nullstilt – neste passord som settes tar navnet' if n else 'fantes ikke'}")


def main():
    import sys
    if len(sys.argv) == 3 and sys.argv[1] == "--reset-account":
        reset_account(sys.argv[2]); return
    server = ZeldaServer()
    http_srv = http.server.ThreadingHTTPServer(("0.0.0.0", PORT), make_http_handler(server))
    threading.Thread(target=http_srv.serve_forever, daemon=True, name="HTTPServer").start()
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind(("0.0.0.0", PORT))
    print(f"zelda-server på HTTP/TCP og UDP {PORT}", flush=True)
    next_state = time.monotonic() + STATE_INTERVAL
    while True:
        sock.settimeout(max(0.001, next_state - time.monotonic()))
        try:
            data, addr = sock.recvfrom(65535)
        except (socket.timeout, ConnectionResetError):
            # Windows can report a previous UDP send to a departed client here.
            pass
        else:
            try:
                message = json.loads(data)
                response = server.handle(message, addr, reply_to_pose=False)
                if response and response.get("error"):
                    sock.sendto(json.dumps(response).encode(), addr)
            except (ValueError, TypeError, KeyError) as exc:
                print(f"ugyldig melding fra {addr}: {exc!r}", flush=True)
            except OSError:
                pass
        if time.monotonic() < next_state:
            continue
        now = time.time()
        with server.lock:
            server.check_timeouts(now)
            # Coalesce poses so a busy lobby does not trigger a full fan-out per packet.
            for name, player in list(server.players.items()):
                if now - player["seen"] < 15 and player["addr"][1] != 0:
                    try:
                        packet = udp_state_packet(server.response_for(name, now), player.get("pose_v2", False))
                        sock.sendto(packet, player["addr"])
                    except OSError:
                        pass
        next_state = next_state_deadline(next_state, time.monotonic())


if __name__ == "__main__":
    main()
