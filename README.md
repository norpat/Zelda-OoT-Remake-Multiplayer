# ▲ Zelda OoT Remake Multiplayer ▲

**Multiplayer mod (Story Co-op and PvP) for *The Legend of Zelda: Ocarina of Time* (Nintendo Switch 2 edition), running in the Lichii emulator.**

> ⚠️ **Work in progress.** This project is still actively being developed, so expect bugs and rough edges.

---

## Overview

Each player runs the game on their own Windows PC in the Lichii emulator. The mod syncs players either directly or via the included Python server (`src/server.py`):

- **Story Co-op:** Play through the game together with shared progress (chests, switches, keys, enemies, time of day, weather, and optional *FOLLOW* zone sync). Additional players in the same zone appear as animated puppets.
- **PvP (work in progress):** Lobby in Bombchu Bowling Alley with *Capture the Flame* and *Deathmatch* modes, team selection, shop counter, and a Radio Jukebox in the PvP menu.
- **Player puppets & animations:** Supports up to 50 players in the same zone using lightweight actor puppets (`CoopPuppet_*`) with real-time skeleton bone sync.
- **Navi for every player:** Each remote player's puppet gets its own fairy (cutscene Navi actor) circling it; works across zone changes. Turn off with `coop_fairies: false` in the config.
- **Nameplates in the game world:** Each remote player's name floats above their puppet as small floating letters (A–Z, 0–9, one actor per character), always turned toward your camera, including your own name. In PvP the letters use the team colour (red or blue; spectators white). Toggle with the NAMES checkbox in the GUI or `/plates on|off`. Needs the `CoopGlyph_*` actors in the romfs mod and a game restart after they are added.
- **Accounts:** Optional password per player name protects your server-side inventory and PvP profile.
- **Chat commands:** e.g. `/zone <scene> [start]` to travel to a scene (boss rooms blocked).
- **Zelda-styled GUI:** Shows game/network status, connected players, PvP lobby controls, and an in-app chat.

## Requirements

- Windows PCs running the **Lichii** emulator.
- **Your own legal copy** of *Ocarina of Time* for Switch 2 – this repository contains **no** game files, keys, or ROMs.
- Python 3.12+ if running or building from source.

## Install

1. Copy the `.pchtxt` patch files from [`patches/`](patches/) into Lichii's mod folder (`Open Mod Data Location` → e.g. `OoT_MP_Test/exefs/`).
2. Start the game in Lichii and load your save.
3. Run `src/oot_mp_gui.py` (or build `OoT_Multiplayer.exe`), enter your player name, and choose **Story** or **PvP**.

## Build from source

No `.exe` is included – build it from source:

```bash
pip install -r requirements.txt
cd src
python -m PyInstaller --noconfirm OoT_Multiplayer.spec
```

The built executable will be in `src/dist/OoT_Multiplayer.exe`. You can also run `python src/oot_mp_gui.py` directly.

## Networking: do I need the default server / a domain?
No. By default the mod connects to the author's public server through an HTTPS tunnel (`SERVER_URL` in
`src/oot_mp_gui.py`). That only exists so friends can play over the internet without opening ports. You can run your own
server (`python src/server.py`, listens on UDP + TCP **27030**) and point the mod to it with an environment variable:

| Setup | How to point the mod at your server | Notes |
|---|---|---|
| **Same home network (LAN)** | `OOT_SERVER_URL=http://192.168.1.50:27030` (the server PC's local IP) | Fastest, nothing exposed to the internet. |
| **Over the internet with a VPN** (Tailscale, ZeroTier, …) | `OOT_SERVER_URL=http://<server VPN IP>:27030` | Recommended for friends: one virtual LAN, no open ports. |
| **Over the internet with port forwarding** | `OOT_SERVER_URL=http://<public IP or dynamic-DNS name>:27030` | Forward UDP+TCP 27030 on your router to the server PC. |
| **Through your own HTTPS tunnel** | `OOT_SERVER_URL=https://<your-tunnel-host>` | E.g. Cloudflare Tunnel or a reverse proxy in front of port 27030. |
| **Direct UDP (testing)** | `OOT_PVP_LOCAL_PORT=27030` and `OOT_PVP_TEST_HOST=<server IP>` | Skips HTTP entirely. |

Set the variable before starting `OoT_Multiplayer.exe`, e.g. in a small `.bat` file: `set OOT_SERVER_URL=http://192.168.1.50:27030`
followed by `start "" OoT_Multiplayer.exe`. Everyone who should play together must use the same server.

## Known limitations

- Work in progress: some bosses, cutscenes, and edge cases in Story and PvP are still being refined.
- Tied to the specific game build/version we play on; game updates may break offsets.

## License

Copyright (C) 2026 NorPat. This project is licensed under the **GNU General Public License v3.0** – see [LICENSE](LICENSE). You may use, study, share and modify it under the terms of the GPLv3; derived works must also be released under the GPLv3.

## Credits

Made by **NorPat**.

### Thanks

- **[daurosk/oot-remake-multiplayer](https://github.com/daurosk/oot-remake-multiplayer)** (GPLv3) – their research and documentation on how the game handles enemies, bosses and flags helped this project a lot. Anything taken from their work is credited here.
  - The live actor list (actor node at +0x538) used for the enemy search, and the idea of pausing the AI of enemy copies, come from their `docs/objects.md`.

*The Legend of Zelda* is a trademark of Nintendo. This is an unofficial fan project and is not affiliated with or endorsed by Nintendo.
