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
