"""OoT Co-oP (Switch 2 / Lichii) – GUI-versjon.

Automatisk: finner Lichii, finner spillminnet, prøver kjente adresser (med validering),
finner andre spillere på lokalnettet. Viser bare en kort veiledning hvis noe må finnes på nytt.
"""
import atexit, ctypes, ctypes.wintypes as wt, functools, hashlib, json, math, os, queue, random, socket, struct, subprocess, sys, threading, time
if os.name == "nt":
    try:
        _winmm = ctypes.WinDLL("winmm")
        if _winmm.timeBeginPeriod(1) == 0:
            atexit.register(_winmm.timeEndPeriod, 1)
    except Exception:
        pass
import tkinter as tk
import traceback
import zlib
import tkinter.messagebox
from tkinter import ttk

import numpy as np
np.seterr(all="ignore")   # NaN i tilfeldig minne under søk er forventet

# --- Zelda Theme & Hylia Serif Font Loader (Plan 8) ---
ZELDA_FONT = "Segoe UI"
try:
    _font_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), "assets", "HyliaSerif.otf")
    if os.path.exists(_font_file):
        _gdi32 = ctypes.WinDLL("gdi32")
        if _gdi32.AddFontResourceExW(_font_file, 0x10, 0) > 0:
            ZELDA_FONT = "Hylia Serif Beta"
except Exception:
    pass

# GDB Call & Respawn Helper (Plan 3 & Plan 10)
try:
    import gcall
    from gdbc import Gdb
except ImportError:
    for _p in (os.path.dirname(os.path.abspath(__file__)), os.getcwd()):
        if _p not in sys.path:
            sys.path.insert(0, _p)
    try:
        import gcall
        from gdbc import Gdb
    except ImportError:
        gcall = None
        Gdb = None


VERSION = "0.94.322"


def puppet_low_hp_pulse(now):
    """Rolig, treg puls helt av/på (~5,7 s periode) for tydelig og behagelig lav-HP-varsel."""
    return 0.5 + 0.5 * math.sin(now * 1.1)


def follow_locked_by_peer(friend, roster, own_name):
    """FOLLOW er eksklusiv: en annen spillers aktive valg låser lokal boks."""
    if isinstance(friend, dict) and friend.get('follow') is True:
        return True
    return any(isinstance(row, dict) and row.get('name') != own_name and row.get('follow') is True
               for row in (roster or []))


CALL_TELEPORT_COOLDOWN = 6.0
SERVER_URL = os.getenv("OOT_SERVER_URL", "https://oot.premiumaroma.no").strip()
SERVER_ADDR = ("oot.premiumaroma.no", 443)   # Cloudflare tunnel
_test_pvp_port = os.getenv("OOT_PVP_LOCAL_PORT", "")
if _test_pvp_port.isascii() and _test_pvp_port.isdecimal() and len(_test_pvp_port) <= 5:
    if 1 <= int(_test_pvp_port) <= 65535:
        _test_pvp_host = os.getenv("OOT_PVP_TEST_HOST", "127.0.0.1")
        socket.inet_pton(socket.AF_INET, _test_pvp_host)
        SERVER_ADDR = (_test_pvp_host, int(_test_pvp_port))
        SERVER_URL = ""
GAME_PORT, DISC_PORT = 27015, 27016
MODE_PORTS = {"Story": (27015, 27016), "PvP": (27025, 27026)}   # v0.74: ulike porter – ulik modus snakker ikke sammen


def server_port_label():
    from urllib.parse import urlsplit

    if SERVER_URL:
        try:
            endpoint = urlsplit(SERVER_URL)
            if endpoint.scheme in ("http", "https") and endpoint.hostname:
                default_port = 443 if endpoint.scheme == "https" else 80
                port = endpoint.port if endpoint.port is not None else default_port
                return f"{endpoint.scheme.upper()} {port}"
        except ValueError:
            pass
        return "Invalid server URL"
    return f"UDP {SERVER_ADDR[1]}"
CHUNK = 16 << 20       # v0.8.3: 16 MB (var 64) – lavere minnetopp
DEFAULT_POS_OFF = 0x35B58EA80     # Link: fysikk-post + 0x40
DEFAULT_RUPEE_OFF = 0x37F37C134
DEFAULT_CAM_OFF = 0x1E821FB50     # kamera->verden 3x4 rad-major; view (verden->kamera) ligger på -0x30
CAM_FOV = 45.0                     # vertikal synsvinkel (fra kamerastrukturen, bekreftet med skjermbilde)
GHOST_HEIGHT = 1.1                 # høyde på skyggefiguren (barne-Link ca. 1,1 m)
MARKER_HEIGHT = 1.4                # markør over vennens posisjon (barne-Link ca. 1,1 m)

CFG_DIR = os.path.join(os.getenv("APPDATA", "."), "OoT_Multiplayer")
CFG = os.path.join(CFG_DIR, "config.json")
k32 = ctypes.WinDLL("kernel32", use_last_error=True)
u32w = ctypes.WinDLL("user32", use_last_error=True)
_nt = ctypes.WinDLL("ntdll")
_nt.NtWriteVirtualMemory.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_char_p, ctypes.c_size_t,
                                      ctypes.POINTER(ctypes.c_size_t)]


# ======================================================================= minne
class MBI(ctypes.Structure):
    _fields_ = [("BaseAddress", ctypes.c_void_p), ("AllocationBase", ctypes.c_void_p),
                ("AllocationProtect", wt.DWORD), ("PartitionId", wt.WORD),
                ("RegionSize", ctypes.c_size_t), ("State", wt.DWORD),
                ("Protect", wt.DWORD), ("Type", wt.DWORD)]


def find_pid():
    out = subprocess.run(["tasklist", "/FI", "IMAGENAME eq lichii.exe", "/FO", "CSV", "/NH"],
                         capture_output=True, text=True, creationflags=0x08000000).stdout
    for line in out.splitlines():
        parts = line.strip().strip('"').split('","')
        if len(parts) > 1 and parts[0].lower() == "lichii.exe":
            return int(parts[1])
    return None


class Proc:
    def __init__(self, pid):
        self.pid = pid
        self.h = k32.OpenProcess(0x10 | 0x20 | 0x08 | 0x400, False, pid)
        if not self.h:
            raise OSError(f"kan ikke åpne Lichii (feil {ctypes.get_last_error()})")
        self.base, self.size = self._guest_region()

    def _guest_region(self):
        addr, mbi, best = 0, MBI(), (0, 0)
        while k32.VirtualQueryEx(self.h, ctypes.c_void_p(addr), ctypes.byref(mbi), ctypes.sizeof(mbi)):
            b, s = mbi.BaseAddress or 0, mbi.RegionSize
            if mbi.State == 0x1000 and (mbi.Protect & 0xFF) in (4, 0x40) and s > best[1]:
                best = (b, s)
            addr = b + s
        return best

    def alive(self):
        code = wt.DWORD()
        return k32.GetExitCodeProcess(self.h, ctypes.byref(code)) and code.value == 259

    def read(self, addr, n):
        buf = ctypes.create_string_buffer(n); got = ctypes.c_size_t()
        if not k32.ReadProcessMemory(self.h, ctypes.c_void_p(addr), buf, n, ctypes.byref(got)) and got.value == 0:
            raise OSError("lesing feilet")
        return buf.raw[:got.value]

    def write(self, addr, data):
        """NtWriteVirtualMemory: ~0,004 ms. WriteProcessMemory mot Lichii tok ~124 ms (FlushInstructionCache) og
        frøs modd-vinduet hver gang den skrev rupees/ting. Faller tilbake til WriteProcessMemory ved feil."""
        data = bytes(data)
        n = ctypes.c_size_t()
        st = _nt.NtWriteVirtualMemory(self.h, ctypes.c_void_p(addr), data, len(data), ctypes.byref(n))
        if st == 0 and n.value == len(data):
            return
        w = ctypes.c_size_t()
        if not k32.WriteProcessMemory(self.h, ctypes.c_void_p(addr), data, len(data), ctypes.byref(w)):
            raise OSError("skriving feilet")

    def f32(self, off, n=1):
        v = struct.unpack(f"<{n}f", self.read(self.base + off, 4 * n)); return v if n > 1 else v[0]

    def u32(self, off, n=1):
        v = struct.unpack(f"<{n}I", self.read(self.base + off, 4 * n)); return v if n > 1 else v[0]

    def chunks(self, lo=0, hi=None):
        """Gjeste-RAM i biter (valgfritt bare området lo..hi, 16-byte-justert)."""
        hi = self.size if hi is None else min(hi, self.size)
        lo = max(0, lo) & ~0xF
        for off in range(lo, hi, CHUNK):
            d = self.read(self.base + off, min(CHUNK, hi - off))
            yield off, np.frombuffer(d[: len(d) - len(d) % 4], dtype="<u4")


# ======================================================================= validering / signaturer
def valid_pos(p, off):
    """Fysikk-post: header 0x02xxxxxx 0x80000000 på off-0x40, enhets-retning på off-16, fornuftig posisjon."""
    try:
        hdr, tag = p.u32(off - 0x40, 2)
        fx, fy, fz = p.f32(off - 16, 3)
        x, y, z = p.f32(off, 3)
    except OSError:
        return False
    return ((hdr >> 24) in (1, 2) and tag == 0x80000000
            and abs(math.hypot(fx, fz) - 1) < 0.05 and abs(fy) < 0.05
            and all(math.isfinite(v) and abs(v) < 100000 for v in (x, y, z))
            and abs(x) + abs(y) + abs(z) > 1.0   # tom post etter scenebytte/omstart står i (0,0,0)
            and not (y == 0.0 and x % 50 == 0 and z % 50 == 0))   # v0.25: tomme poster med standardtall (0,0,-250), (250,0,-500) …


def valid_rupee(p, off):
    """Variabel-post: (verdi, verdi, 0, markør). Markøren varierer mellom økter/PC-er
    (0x85AEB718 her, 0x85016718 på den andre PC-en), så vi krever bare at den samme
    markøren går igjen i nabopostene i tabellen."""
    try:
        v, disp, zero, mark = p.u32(off, 4)
        around = p.u32(off - 0x100, 0x80)
    except OSError:
        return False
    return v == disp and zero == 0 and v < 1000 and is_marker(mark) and around.count(mark) >= 4


def valid_counter(p, off):
    """Samme som valid_rupee for kjente poster i tabellen (tåler at visningsverdi disp henger etter)."""
    try:
        v, disp, zero, mark = p.u32(off, 4)
        around = p.u32(off - 0x100, 0x80)
    except OSError:
        return False
    return v < 1000 and abs(v - disp) < 1000 and zero == 0 and is_marker(mark) and around.count(mark) >= 4


def is_marker(mark):
    """Markøren er en (32-bit) peker til variabelklassens vtable i spillkoden. Alle sett: 0x84F83718, 0x84FCC718,
    0x85016718, 0x851D9718, 0x85282718, 0x8590C718, 0x85AEB718 – dvs. 0x8xxxx718 (vtable flytter med ASLR,
    men slutter alltid på 0x718). v0.8.1: en falsk post med markør 0x0200802F slapp gjennom den gamle sjekken."""
    return 0x80000000 <= mark < 0x90000000 and (mark & 0xFFF) == 0x718


def valid_pos_light(p, off):
    """Overvåking: bare header + endelige tall (retningen kan vippe når Link hopper/står i skråning)."""
    try:
        hdr, tag = p.u32(off - 0x40, 2)
        x, y, z = p.f32(off, 3)
    except OSError:
        return False
    return ((hdr >> 24) in (1, 2) and tag == 0x80000000
            and all(math.isfinite(v) and abs(v) < 100000 for v in (x, y, z))
            and abs(x) + abs(y) + abs(z) > 1.0   # tom post etter scenebytte/omstart står i (0,0,0)
            and not (y == 0.0 and x % 50 == 0 and z % 50 == 0))   # v0.25: tomme poster med standardtall (0,0,-250), (250,0,-500) …


def valid_rupee_light(p, off):
    try:
        v, disp, _z, mark = p.u32(off, 4)
    except OSError:
        return False
    # visningen henger litt etter når tallet teller opp/ned; markøren må fortsatt være ekte (ellers skriv ikke!)
    return v < 1000 and abs(v - disp) < 1000 and is_marker(mark)


def read_cam(p, off):
    """Returnerer (høyre, opp, fremover, øye) fra kamera->verden-matrisen."""
    m = p.f32(off, 12)
    return (m[0], m[4], m[8]), (m[1], m[5], m[9]), (-m[2], -m[6], -m[10]), (m[3], m[7], m[11])


def valid_cam(p, off, near=None):
    """Kamera->verden (off) og verden->kamera (off-0x30) må være hverandres transponerte rotasjon,
    ortonormal, og øyet i nærheten av Link."""
    try:
        inv = p.f32(off, 12); view = p.f32(off - 0x30, 12)
    except OSError:
        return False
    if not all(math.isfinite(v) for v in inv + view):
        return False
    for i in range(3):
        if abs(sum(inv[i * 4 + j] ** 2 for j in range(3)) - 1) > 0.01:
            return False
        for j in range(3):
            if abs(inv[i * 4 + j] - view[j * 4 + i]) > 2e-3:
                return False
    if near is not None:
        q = cam_quality(p, off, near)
        if q is None:
            return False
        dist, dot = q
        # Spillkameraet står 1–30 m fra Link og ser omtrent mot ham (mildt: kameraet kan se opp/ned)
        if not (1.0 < dist < 30 and dot > 0.3):
            return False
    return True


def _cam_readable(p, off):
    """Sant hvis adressen fortsatt ser ut som en kameramatrise (ortonormal + view/invers-par), uansett hvor øyet er.
    Brukes for å skille «kamera som bare er langt unna nå» fra «adresse som ikke er kamera i det hele tatt»."""
    return valid_cam(p, off, None)


def cam_quality(p, off, near):
    """(avstand øye→Link, cos-vinkel mellom kameraretning og retning mot Link)."""
    try:
        r, u, f, eye = read_cam(p, off)
    except OSError:
        return None
    d = [near[i] - eye[i] for i in range(3)]
    nd = math.sqrt(sum(v * v for v in d)) or 1e-6
    return nd, sum(d[i] * f[i] for i in range(3)) / nd


def cam_scan(p, near, progress, regions=None):
    """Søk etter view+inverse-par (16-byte-justert). Returnerer grupper av like kameraer, største først:
    [(antall, [offsets], øye, avstand, dot)]. Spillkameraet finnes i mange kopier (render-buffere).
    regions: liste av (lo, hi) for raskt søk i et begrenset område; None = hele gjeste-RAM."""
    np.seterr(all="ignore")   # gjelder per tråd – søket kjører i en bakgrunnstråd
    found = []
    regions = regions or [(0, p.size)]
    n_chunks = max(1, sum(max(1, (hi - lo) // CHUNK) for lo, hi in regions))
    it = (c for lo, hi in regions for c in p.chunks(lo, hi))
    for k, (off, q) in enumerate(it):
        n = len(q) - 24
        if n > 0:
            n -= n % 4

            fq = q.view(np.float32)

            def a(d):
                return fq[d:d + n:4]

            def eq(x, y):          # transponert er ikke bit-likt (siste bit kan avvike)
                return np.abs(x - y) < 1e-4
            r0 = a(0)
            # NB: ikke krev r01 != 0 – et vannrett kamera kan ha nøyaktig 0 der. Utelukk bare akse-justerte (identitet o.l.).
            axis = (a(1) == 0) & (a(2) == 0) & (a(4) == 0)
            m = (np.abs(r0) <= 1.0) & ~axis & eq(a(13), a(4)) & eq(a(14), a(8)) & eq(a(16), a(1)) & eq(a(18), a(9))
            m &= np.abs(r0 * r0 + a(1) * a(1) + a(2) * a(2) - 1) < 0.01
            for i in np.nonzero(m)[0].tolist():
                found.append(off + (i * 4 + 12) * 4)
        progress((k + 1) / n_chunks)
    groups = {}
    for o in found:
        if valid_cam(p, o, near):
            key = tuple(round(v, 2) for v in read_cam(p, o)[3])
            groups.setdefault(key, []).append(o)
    out = []
    for eye, offs in groups.items():
        dist, dot = cam_quality(p, offs[0], near) if near is not None else (0.0, 0.0)
        out.append((len(offs), offs, eye, dist, dot))
    out.sort(key=lambda g: -g[0])
    return out


CAM_VT_OFF = 0x4C29B90


def cam_scan_vtable(p, main_va, p_act, near):
    """Raskt (<0,5 s) kamerasøk via Camera-objektets vtable (main+0x4C29B90, matrise på +0x300) rundt p_act."""
    if not main_va or not p_act or near is None:
        return None
    vt = main_va + CAM_VT_OFF
    lo = max(0, (p_act - (32 << 20)) & ~0xFFFFF)
    hi = min(p.size, p_act + (192 << 20))
    scored = []
    for off, q in p.chunks(lo, hi):
        n = len(q) - (len(q) % 8)
        if n <= 0:
            continue
        arr = np.frombuffer(q[:n], dtype=np.uint64)
        for i in np.nonzero(arr == vt)[0].tolist():
            cam = off + i * 8 + 0x300
            if valid_cam(p, cam, near):
                qd = cam_quality(p, cam, near)
                if qd and 1.5 < qd[0] < 12 and qd[1] > 0.7:
                    scored.append((qd[1], cam, qd[0]))
    if not scored:
        return None
    # Mange kamera-kopier ser riktige ut, men noen står stille («døde»). Les matrisene på nytt og foretrekk de som endrer seg.
    try:
        snap = {cam: p.read(p.base + cam, 0x30) for _d, cam, _q in scored}
        time.sleep(0.3)
        moving = {cam for cam in snap if p.read(p.base + cam, 0x30) != snap[cam]}
    except OSError:
        moving = set()
    scored.sort(key=lambda t: (t[1] in moving, t[0]), reverse=True)
    return scored[0][1]


REGION_STEP = 0x10000000   # hele spillområdet flytter seg i slike steg (sett: 0, −0x40000000, −0x140000000)


def find_rupees_by_region(p, pos=None):
    """Rupee-posten flytter seg sammen med hele området i hele 0x10000000-steg. Prøv først forskyvningen fra
    Link-posten avrundet (Link kan i tillegg ligge noen fysikk-plasser unna), så alle steg. Streng validering
    (verdi == visning, 0, markør som gjentas i tabellen) gjør feil treff svært usannsynlig."""
    shifts = []
    if pos is not None:
        shifts.append(round((pos - DEFAULT_POS_OFF) / REGION_STEP) * REGION_STEP)
    k_max = p.size // REGION_STEP + 1
    shifts += sorted((k * REGION_STEP for k in range(-k_max, k_max + 1)), key=abs)
    for s in dict.fromkeys(shifts):
        o = DEFAULT_RUPEE_OFF + s
        if 0 < o < p.size and valid_rupee(p, o):
            return o
    return None


def find_link_auto(p, progress):
    """Ett søk gjennom minnet: fysikk-poster + kamerastrukturer. Kamerastrukturen (øye, 1,1,1,0,0, siktepunkt,
    …, FOV 45 på +0x40, 1e6 på +0x74) sikter nøyaktig på Link, så posten med den posisjonen er Link.
    Returnerer (pos_off eller None, fysikk-poster, antall strukturer)."""
    np.seterr(all="ignore")
    phys, structs = [], []
    n_chunks = max(1, p.size // CHUNK)
    for k, (off, q) in enumerate(p.chunks()):
        i = np.nonzero((((q[:-1] >> 24) == 1) | ((q[:-1] >> 24) == 2)) & (q[1:] == 0x80000000))[0]
        i = i[(i % 4) == 0]
        phys.append(i.astype(np.int64) * 4 + off + 0x40)
        n = len(q) - 32
        if n > 0:
            j = np.nonzero((q[3:3 + n] == 0x3F800000) & (q[4:4 + n] == 0x3F800000) & (q[5:5 + n] == 0x3F800000)
                           & (q[6:6 + n] == 0) & (q[7:7 + n] == 0)
                           & (q[16:16 + n] > 0x41A00000) & (q[16:16 + n] < 0x42F00000))[0]   # FOV 20–120°
            # (v0.8.1: +0x74 = 1e6 kreves ikke lenger – utendørs har kameraet annen sikteavstand)
            structs += [off + int(x) * 4 for x in j]
        progress((k + 1) / n_chunks)
    phys = [int(o) for o in np.concatenate(phys) if valid_pos(p, int(o))]
    # Les alt på nytt NÅ (Link kan ha flyttet seg under søket) og match siktepunkt mot fysikk-poster
    from collections import Counter
    targets = Counter()
    for s in structs:
        try:
            t = p.f32(s + 0x20, 3)
        except OSError:
            continue
        if abs(t[0]) + abs(t[1]) + abs(t[2]) > 1.0:
            targets[tuple(round(v, 2) for v in t)] += 1
    for tgt, _n in targets.most_common(3):
        for o in phys:
            try:
                if math.dist(p.f32(o, 3), tgt) < 0.05:
                    return o, phys, len(structs)
            except OSError:
                pass
    return None, phys, len(structs)


def relink_near(p, old_pos, cam_off, window=256 << 20):
    """Finn Link sin (nye) fysikk-post etter områdebytte: let bare ±window rundt den gamle posten (fysikk-postene
    ligger samlet), og velg posten som står 1,5–12 m foran kameraet og ser mest rett på (Link). Foretrekk poster
    som beveger seg. Returnerer offset eller None."""
    lo, hi = max(0, old_pos - window), min(p.size, old_pos + window)
    cands = []
    for off, q in p.chunks(lo, hi):
        i = np.nonzero((((q[:-1] >> 24) == 1) | ((q[:-1] >> 24) == 2)) & (q[1:] == 0x80000000))[0]
        i = i[(i % 4) == 0]
        cands += [int(x) * 4 + off + 0x40 for x in i]
    cands = [o for o in cands if valid_pos(p, o)]
    if not cands or cam_off is None:
        return None
    a = {o: p.f32(o, 3) for o in cands}
    time.sleep(0.6)
    r, u, f, eye = read_cam(p, cam_off)
    best = None
    for o in cands:
        try:
            b = p.f32(o, 3)
        except OSError:
            continue
        d = [b[i] - eye[i] for i in range(3)]
        dist = math.sqrt(sum(v * v for v in d)) or 1e-6
        dot = sum(d[i] * f[i] for i in range(3)) / dist
        if not (1.5 < dist < 12 and dot > 0.5):
            continue
        moving = math.dist(a[o], b) > 0.05
        score = dot + (0.5 if moving else 0) - 0.02 * abs(dist - 4)   # Link: ca. 3–5 m foran, ofte i bevegelse
        if best is None or score > best[0]:
            best = (score, o, dist, dot, moving)
    if best:
        log(f"gjenfinning: {len(cands)} fysikk-poster rundt gammel post; valgt guest+0x{best[1]:X} "
            f"({best[2]:.1f} m foran kamera, retning {best[3]:.2f}, {'beveger seg' if best[4] else 'står stille'})")
        return best[1]
    return None


def relink_joint(p, pos_anchor, cam_anchors, wait=2.0, full=False):
    """Finn Link + spillkamera samtidig ut fra bevegelse: når spilleren går, flytter Link-posten og kameraøyet seg
    likt (kameraet følger Link). Gamle poster og andre kameraer står stille. Returnerer (pos, cam) eller (None, None)
    hvis ingenting beveget seg (spilleren står stille – prøv igjen senere)."""
    lo, hi = max(0, pos_anchor - (256 << 20)), min(p.size, pos_anchor + (256 << 20))
    recs = []
    for off, q in p.chunks(lo, hi):
        i = np.nonzero((((q[:-1] >> 24) == 1) | ((q[:-1] >> 24) == 2)) & (q[1:] == 0x80000000))[0]
        i = i[(i % 4) == 0]
        recs += [int(x) * 4 + off + 0x40 for x in i]
    recs = [o for o in recs if valid_pos(p, o)]
    span = 32 << 20
    regions = sorted({(max(0, a - span) & ~(CHUNK - 1), min(p.size, a + span)) for a in cam_anchors if a and 0 < a < p.size})
    if full or not regions:
        cams = [g[1][0] for g in cam_scan(p, None, lambda _f: None)]          # fullt søk (~1 min)
    else:
        cams = [g[1][0] for g in cam_scan(p, None, lambda _f: None, regions)]
    if not recs or not cams:
        log(f"gjenfinning: ingen kandidater ({len(recs)} poster, {len(cams)} kameraer{', fullt søk' if full else ''})")
        return None, None
    a_rec = {o: p.f32(o, 3) for o in recs}
    a_cam = {c: read_cam(p, c)[3] for c in cams}
    time.sleep(wait)
    best = None
    moved_cams = moved_recs = 0
    for o in recs:
        try:
            moved_recs += math.dist(p.f32(o, 3), a_rec[o]) >= 0.3
        except OSError:
            pass
    for c in cams:
        try:
            r, u, f, eye = read_cam(p, c)
        except OSError:
            continue
        de = [eye[i] - a_cam[c][i] for i in range(3)]
        if math.sqrt(sum(v * v for v in de)) < 0.3:
            continue
        moved_cams += 1
        for o in recs:
            try:
                b = p.f32(o, 3)
            except OSError:
                continue
            dr = [b[i] - a_rec[o][i] for i in range(3)]
            mr = math.sqrt(sum(v * v for v in dr))
            if mr < 0.3:
                continue
            diff = math.sqrt(sum((de[i] - dr[i]) ** 2 for i in range(3)))
            me = math.sqrt(sum(v * v for v in de))
            # Kameraet følger med forsinkelse/demping: krev samme retning (vannrett) og omtrent samme lengde
            hx = math.hypot(de[0], de[2]) * math.hypot(dr[0], dr[2])
            cosang = (de[0] * dr[0] + de[2] * dr[2]) / hx if hx > 1e-6 else 0
            if cosang < 0.7 or not (0.3 <= me / mr <= 3.0):
                continue
            d = [b[i] - eye[i] for i in range(3)]
            dist = math.sqrt(sum(v * v for v in d)) or 1e-6
            dot = sum(d[i] * f[i] for i in range(3)) / dist
            if not (1.5 < dist < 12 and dot > 0.5):
                continue
            score = dot + cosang - 0.1 * abs(math.log(me / mr))
            if best is None or score > best[0]:
                best = (score, o, c, dist, dot, mr, diff)
    if best:
        log(f"gjenfinning (bevegelse): {len(recs)} poster, {len(cams)} kameraer; Link guest+0x{best[1]:X} + kamera guest+0x{best[2]:X} "
            f"flyttet {best[5]:.1f} m sammen (avvik {best[6]:.2f}), {best[3]:.1f} m foran, retning {best[4]:.2f}")
        return best[1], best[2]
    try:
        mc = sorted(((math.dist(read_cam(p, c)[3], a_cam[c]), c) for c in cams), reverse=True)[:3]
        mrr = sorted(((math.dist(p.f32(o, 3), a_rec[o]), o) for o in recs), reverse=True)[:3]
        log("  mest bevegelse – kameraer: " + ", ".join(f"0x{c:X} {d:.1f} m" for d, c in mc) +
            " | poster: " + ", ".join(f"0x{o:X} {d:.1f} m" for d, o in mrr))
    except OSError:
        pass
    log(f"gjenfinning: ingen par flyttet seg sammen ({len(recs)} poster/{moved_recs} beveget, {len(cams)} kameraer/{moved_cams} beveget"
        f"{', fullt søk' if full else ''}) – står spilleren stille?")
    return None, None


def phys_scan(p, progress):
    """Alle fysikk-poster (header 0x02xxxxxx 0x80000000, 16-byte-justert). Returnerer posisjons-offsets."""
    phys = []
    n = max(1, p.size // CHUNK)
    for k, (off, q) in enumerate(p.chunks()):
        i = np.nonzero((((q[:-1] >> 24) == 1) | ((q[:-1] >> 24) == 2)) & (q[1:] == 0x80000000))[0]
        i = i[(i % 4) == 0]
        phys.append(i.astype(np.int64) * 4 + off + 0x40)
        progress((k + 1) / n)
    return [int(o) for o in np.concatenate(phys) if valid_pos(p, int(o))]


def rupee_scan(p, value, progress):
    """Variabel-poster med gitt verdi: (v, v, 0, markør, 0, type∈{1,8,0x20}).
    Markøren er ikke fast mellom PC-er, så den sjekkes bare med valid_rupee (gjentas i nabopostene)."""
    hits = []
    n = max(1, p.size // CHUNK)
    for k, (off, q) in enumerate(p.chunks()):
        j = np.nonzero(q[:-6] == value)[0]
        if len(j):
            m = ((q[j + 1] == value) & (q[j + 2] == 0) & (q[j + 3] > 0xFFFFFF) & (q[j + 4] == 0)
                 & np.isin(q[j + 5], (1, 8, 0x20)))
            hits.extend(int(x) * 4 + off for x in j[m])
        progress((k + 1) / n)
    return [o for o in hits if valid_rupee(p, o)]


# ======================================================================= logging
APP_DIR = os.path.dirname(sys.executable if getattr(sys, "frozen", False) else os.path.abspath(__file__))
PC = os.getenv("COMPUTERNAME", socket.gethostname())
_LOG_FILES = [os.path.join(CFG_DIR, "log.txt"), os.path.join(APP_DIR, "logs", f"{PC}.log")]
_log_lock = threading.Lock()


SKIP = set()   # v0.57 feilsoking: delsystemer som hoppes over (/skip a,b,c)


LOG_MAX_BYTES = 25 << 20
_log_last = {}
_log_n = [0]


def log(msg):
    """Skriver til %APPDATA%\\OoT_Multiplayer\\log.txt og <exe-mappe>\\logs\\<PC>.log (delt mappe → begge sider ser)."""
    now = time.time()
    line = f"{time.strftime('%Y-%m-%d %H:%M:%S')} [{PC}] v{VERSION} {msg}\n"
    with _log_lock:
        # v0.94.303: identisk melding innen 60 s skrives ikke igjen (f.eks. «mål-patch» uten endring hvert 15. s)
        t_ = _log_last.get(msg)
        if t_ is not None and now - t_ < 60:
            return
        _log_last[msg] = now
        if len(_log_last) > 4000:
            for k in [k for k, v in _log_last.items() if now - v > 60]:
                del _log_last[k]
        _log_n[0] += 1
        for path in _LOG_FILES:
            try:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                if _log_n[0] % 200 == 1 and os.path.exists(path) and os.path.getsize(path) > LOG_MAX_BYTES:
                    # v0.94.303: over 25 MB -> <navn>.1.log (forrige .1 overskrives), så loggen aldri passerer ~50 MB
                    os.replace(path, os.path.splitext(path)[0] + '.1' + os.path.splitext(path)[1])
                with open(path, "a", encoding="utf-8") as f:
                    f.write(line)
            except OSError:
                pass


# ======================================================================= config
def load_cfg():
    try:
        with open(CFG, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, ValueError):
        return {}


def save_cfg(c):
    os.makedirs(CFG_DIR, exist_ok=True)
    with open(CFG, "w", encoding="utf-8") as f:
        json.dump(c, f, indent=2)
    write_look_copy(c.get("look"))


def write_look_copy(look):
    """v0.94.308: kopi av valgt tunikafarge ved siden av exe-en (look.txt). auto_restart.py leser den først:
    startes spillet fra et annet miljø (annen APPDATA) fikk egen Link feil grunnfarge, og fargeplagget oppå
    ga to tunikaer som flimret (hvit Link som blinket cyan, 2026-11-23)."""
    if look not in LOOKS:
        return
    try:
        d = os.path.dirname(sys.executable) if getattr(sys, "frozen", False) else os.path.dirname(os.path.abspath(__file__))
        f = os.path.join(d, "look.txt")
        if not os.path.isfile(f) or open(f, encoding="utf-8").read().strip() != look:
            open(f, "w", encoding="utf-8").write(look)
    except OSError:
        pass


def local_ips():
    ips = set()
    try:
        for a in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            if not a[4][0].startswith(("127.", "169.254.")):
                ips.add(a[4][0])
    except OSError:
        pass
    return sorted(ips)


# ======================================================================= synk
# Ting i variabeltabellen, relativt til rupee-posten: (navn, verdi-offset, maks-offset, visningsnavn)
ITEMS = [
    ("rupees", 0x000, 0x230, "Rupees"),
    ("nuts",   0x8E8, 0x1B8, "Deku Nuts"),   # delt teller; Link 2-bruk gis tilbake av _ammo_tick
    ("seeds",  0x910, 0x1E0, "Seeds"),   # delt teller; Link 2-bruk gis tilbake av _ammo_tick
    # ("sticks", 0x938, 0x208, "Deku Sticks"),   # av: telleren ping-ponget og ble stående på 0   # delt teller; Link 2-bruk gis tilbake av _ammo_tick
]


class CounterSync:
    """Delt beholdning med kumulative deltaer (tåler tapte UDP-pakker). Maks leses fra spillet."""

    def __init__(self, p, off, maxv=999, name="rupees", cap_off=None):
        self.p, self.off, self.max, self.name, self.cap_off = p, off, maxv, name, cap_off
        self.expected = p.u32(off); self.my_cum = 0; self.seen = None
        self.behind_since = None   # når vennen fikk et høyere tall enn oss (for utjevning)
        self.mute_until = 0.0      # v0.94.268: modden skriver selv (PvP-gjenoppretting o.l.) – ikke tell som funn/forbruk

    def mute(self, secs=2.0):
        self.mute_until = time.time() + secs

    def cap(self):
        if self.cap_off is not None:
            try:
                c = self.p.u32(self.cap_off)
                if 0 < c < 1000:
                    return c
            except OSError:
                pass
        return self.max

    def tick(self):
        cur = self.p.u32(self.off)
        if cur != self.expected:
            if time.time() >= self.mute_until:
                self.my_cum += cur - self.expected
            self.expected = cur
        return cur

    def _set(self, new):
        for o in (self.off, self.off + 4):
            self.p.write(self.p.base + o, struct.pack("<I", new))
        self.expected = new          # ikke en egen endring -> påvirker ikke my_cum
        self.set_t = time.time()

    def equalize(self, remote_val, now, force=False):
        """Delt bag: høyeste tall vinner. Ved tilkobling med en gang, ellers når vennen har
        ligget høyere i 3 s (så vanlige endringer underveis ikke slås sammen feil)."""
        if remote_val is None:
            return
        cur = self.tick()
        if remote_val <= cur:
            self.behind_since = None; return
        if not force:
            if self.behind_since is None:
                self.behind_since = now; return
            if now - self.behind_since < 3:
                return
        new = min(self.cap(), remote_val)
        if new > cur:
            log(f"{self.name}: utjevnet til vennens tall {cur} -> {new}")
            self._set(new)
        self.behind_since = None

    def apply(self, remote_cum, reset):
        if self.seen is None or reset:
            self.seen = remote_cum; return
        inc, self.seen = remote_cum - self.seen, remote_cum
        if inc:
            before = self.tick()
            new = max(0, min(self.cap(), before + inc))
            log(f"{self.name}-synk fra venn: {inc:+d} ({before} -> {new})")
            self._set(new)


# ======================================================================= markør over spillet
def lichii_window(pid):
    found = []

    @ctypes.WINFUNCTYPE(wt.BOOL, wt.HWND, wt.LPARAM)
    def cb(h, _):
        wpid = wt.DWORD(); u32w.GetWindowThreadProcessId(h, ctypes.byref(wpid))
        if wpid.value == pid and u32w.IsWindowVisible(h):
            n = u32w.GetWindowTextLengthW(h)
            if n:
                b = ctypes.create_unicode_buffer(n + 1); u32w.GetWindowTextW(h, b, n + 1)
                if "Lichii" in b.value:
                    found.append((h, b.value))
        return True
    u32w.EnumWindows(cb, 0)
    # Hovedvinduet heter «Lichii | build-… | <spill> | …». Innstillingsdialogen heter «Lichii Configuration» – ikke tegn over den.
    for h, t in found:
        if t.startswith("Lichii |"):
            return h
    for h, t in found:
        if "Configuration" not in t and "Config" not in t:
            return h
    return None


def game_rect(h):
    """Spillbildet i Lichii-vinduet: klientområde minus menylinje/statuslinje, 16:9 sentrert."""
    r = wt.RECT(); u32w.GetClientRect(h, ctypes.byref(r))
    pt = wt.POINT(0, 0); u32w.ClientToScreen(h, ctypes.byref(pt))
    try:
        scale = u32w.GetDpiForWindow(h) / 96
    except (AttributeError, OSError):
        scale = 1.0
    menu, status = 22 * scale, 26 * scale
    w, ah = r.right, r.bottom - menu - status
    if w <= 0 or ah <= 0:
        return None
    gw, gh = (ah * 16 / 9, ah) if w / ah > 16 / 9 else (w, w * 9 / 16)
    return pt.x + (w - gw) / 2, pt.y + menu + (ah - gh) / 2, gw, gh


def project(cam, P, rect, fov=CAM_FOV):
    """Verdenspunkt -> skjerm. Returnerer (x, y, synlig); utenfor/bak gir et punkt på kanten (for pil)."""
    r, u, f, eye = cam
    x0, y0, w, h = rect
    d = [P[i] - eye[i] for i in range(3)]
    vx = sum(d[i] * r[i] for i in range(3))
    vy = sum(d[i] * u[i] for i in range(3))
    vz = sum(d[i] * f[i] for i in range(3))
    t = math.tan(math.radians(fov) / 2)
    if vz > 0.1:
        sx = x0 + w / 2 + vx / (vz * t * (w / h)) * w / 2
        sy = y0 + h / 2 - vy / (vz * t) * h / 2
        if x0 <= sx <= x0 + w and y0 <= sy <= y0 + h:
            return sx, sy, True
    if abs(vx) < 1e-3 and abs(vy) < 1e-3:
        vy = -1.0                      # rett bak: pil nederst
    ang = math.atan2(-vy, vx)
    cx, cy, m = x0 + w / 2, y0 + h / 2, 40
    k = min((w / 2 - m) / max(abs(math.cos(ang)), 1e-6), (h / 2 - m) / max(abs(math.sin(ang)), 1e-6))
    return cx + math.cos(ang) * k, cy + math.sin(ang) * k, False


class Overlay:
    """Gjennomsiktig, klikk-gjennom vindu over hele skrivebordet som tegner vennen."""
    KEY = "#010203"

    def __init__(self, root):
        self.win = tk.Toplevel(root); self.win.overrideredirect(True); self.win.attributes("-topmost", True)
        self.win.configure(bg=self.KEY); self.win.attributes("-transparentcolor", self.KEY)
        gx, gy = u32w.GetSystemMetrics(76), u32w.GetSystemMetrics(77)
        gw, gh = u32w.GetSystemMetrics(78), u32w.GetSystemMetrics(79)
        self.origin = (gx, gy)
        self.win.geometry(f"{gw}x{gh}{gx:+d}{gy:+d}")
        self.cv = tk.Canvas(self.win, width=gw, height=gh, bg=self.KEY, highlightthickness=0); self.cv.pack()
        self.win.update_idletasks()
        hw = u32w.GetParent(self.win.winfo_id()) or self.win.winfo_id()
        u32w.SetWindowLongW(hw, -20, u32w.GetWindowLongW(hw, -20) | 0x80000 | 0x20 | 0x80)  # layered, klikk-gjennom, toolwindow

    def clear(self):
        self.cv.delete("all")

    def draw_ghost(self, foot, head, dirpt, name, dist, hat_hex=None):
        """Gjennomskinnelig Link-silhuett (stipple) der vennen står, skalert etter avstand, med retningspil på bakken."""
        ox, oy = self.origin
        fx, fy = foot[0] - ox, foot[1] - oy
        hx, hy = head[0] - ox, head[1] - oy
        h = max(18.0, min(700.0, fy - hy))                 # høyde i piksler (hode → føtter)
        c, cv = (hat_hex or ACC), self.cv
        tunic = hat_hex or "#3fa34d"
        cap = hat_hex or "#2f8a3b"
        face_x = (dirpt[0] - foot[0]) if dirpt else 0.0
        sgn = 1 if face_x >= 0 else -1                      # luen peker bakover (motsatt av retningen han ser)
        stp = "gray50"
        # retningspil på bakken
        if dirpt:
            dx, dy = dirpt[0] - ox, dirpt[1] - oy
            cv.create_line(fx, fy, dx, dy, fill="black", width=6, arrow="last", arrowshape=(14, 16, 6))
            cv.create_line(fx, fy, dx, dy, fill=c, width=3, arrow="last", arrowshape=(12, 14, 5))
        # bein
        cv.create_rectangle(fx - 0.12 * h, fy - 0.30 * h, fx + 0.12 * h, fy, fill="#6b4b2a", stipple=stp, outline=c, width=2)
        # tunika
        cv.create_polygon(fx - 0.21 * h, fy - 0.30 * h, fx + 0.21 * h, fy - 0.30 * h, fx + 0.15 * h, fy - 0.62 * h,
                          fx - 0.15 * h, fy - 0.62 * h, fill=tunic, stipple=stp, outline=c, width=2)
        # hode
        cv.create_oval(fx - 0.15 * h, fy - 0.90 * h, fx + 0.15 * h, fy - 0.60 * h, fill="#e8c39a", stipple=stp, outline=c, width=2)
        # lue
        cv.create_polygon(fx - 0.17 * h, fy - 0.78 * h, fx + 0.17 * h, fy - 0.78 * h, fx, fy - 1.0 * h,
                          fx - sgn * 0.52 * h, fy - 0.62 * h, fill=cap, stipple=stp, outline=c, width=2)
        label = f"{name}  {dist:.0f} m"
        cv.create_text(fx + 1, hy - 0.2 * h - 11, text=label, fill="black", font=("Segoe UI", 12, "bold"))
        cv.create_text(fx, hy - 0.2 * h - 12, text=label, fill=c, font=("Segoe UI", 12, "bold"))

    def draw_friend(self, sx, sy, on_screen, name, dist, hat_hex=None):
        ox, oy = self.origin
        x, y = sx - ox, sy - oy
        c = hat_hex or ACC
        label = f"{name}  {dist:.0f} m"
        if on_screen:
            self.cv.create_polygon(x, y + 10, x - 9, y - 4, x + 9, y - 4, fill=c, outline="black", width=2)
            self.cv.create_text(x + 1, y - 21, text=label, fill="black", font=("Segoe UI", 12, "bold"))
            self.cv.create_text(x, y - 22, text=label, fill=c, font=("Segoe UI", 12, "bold"))
        else:
            self.cv.create_oval(x - 16, y - 16, x + 16, y + 16, fill="#1d232a", outline=c, width=3)
            self.cv.create_text(x, y, text="!", fill=c, font=("Segoe UI", 14, "bold"))
            self.cv.create_text(x, y + 28, text=label, fill=c, font=("Segoe UI", 10, "bold"))


# ======================================================================= hele baggen
BAG_FIRST, BAG_LAST, ENTRY = 0x140, 0x1338, 0x28   # inventar-blokken (type 0x20) relativt til rupee-posten
BAG_TYPE = 0x20
LEARN_SPAN = 300                                    # lære-modus logger endringer i ±300 poster rundt rupees


class BagSync:
    """Synker inventar-blokken (≈115 poster av type 0x20) mellom spillerne.

    * «eie»-poster (ting, oppgraderinger, quest items, kapasiteter): høyeste verdi vinner, med en gang.
    * forbruksvarer (bomber, piler …): delta-synk som rupees. En post blir forbruksvare første gang verdien
      går NED hos en av dere (lært automatisk, lagret i config og delt med vennen).
    * poster som endrer seg mange ganger i minuttet (trolig tilstand, ikke beholdning) settes til «ignorert».
    Postene i ITEMS (rupees, nuts, frø, sticks) håndteres av CounterSync og hoppes over her.
    """

    def __init__(self, p, rup, cfg, skip_rels):
        self.p, self.rup, self.cfg = p, rup, cfg
        self.delta = set(r for r in cfg.get("bag_delta", []) if BAG_FIRST <= r <= BAG_LAST)
        self.ignored = set(cfg.get("bag_ignored", []))
        self.rels = []
        # Standard inventar (type 0x20): +0x140..+0x1338
        for rel in range(BAG_FIRST, BAG_LAST + 1, ENTRY):
            if rel in skip_rels:
                continue
            try:
                if p.u32(rup + rel + 0x14) == BAG_TYPE and valid_rupee(p, rup + rel):
                    self.rels.append(rel)
            except OSError:
                pass
        self.last = {r: self._read(r) for r in self.rels}
        self.counters = {}                 # rel -> CounterSync for forbruksvarer
        for r in self.delta & set(self.rels):
            self._make_counter(r, seen0=None)
        self.changes = {}                  # rel -> [tidspunkter] for «ustabil»-sjekk
        self.learn_last = {}
        log(f"bag: {len(self.rels)} poster i inventar-blokken, {len(self.delta)} kjente forbruksvarer, "
            f"{len(self.ignored)} ignorert; eier nå {sum(1 for r in self.rels if self.last[r])} ting")

    def _read(self, rel):
        return self.p.u32(self.rup + rel)

    def _write(self, rel, v):
        for o in (rel, rel + 4):
            self.p.write(self.p.base + self.rup + o, struct.pack("<I", v))
        self.last[rel] = v

    def _make_counter(self, rel, seen0):
        c = CounterSync(self.p, self.rup + rel, 999, f"bag{rel:+#x}")
        c.seen = seen0
        self.counters[rel] = c
        return c

    def _save(self):
        self.cfg["bag_delta"] = sorted(self.delta); self.cfg["bag_ignored"] = sorted(self.ignored)
        save_cfg(self.cfg)

    def mark_delta(self, rel, why):
        if rel in self.delta or rel in self.ignored or rel not in self.rels:
            return
        self.delta.add(rel)
        c = self._make_counter(rel, seen0=0)
        if why == "lokal":
            # Registrer nedgangen vi nettopp så, så den sendes til vennen som delta
            c.expected = self.last[rel]
        log(f"bag: rupees{rel:+#x} er forbruksvare ({why}) – synkes som delta fra nå")
        self._save()

    def tick(self, now):
        """Les blokken. Returnerer (verdier, kumulative deltaer) til nettverksmeldingen."""
        vals = {}
        for rel in self.rels:
            if rel in self.ignored:
                continue
            if rel in self.counters:
                vals[rel] = self.counters[rel].tick()
                continue
            v = self._read(rel)
            old = self.last[rel]
            if v != old:
                t = self.changes.setdefault(rel, [])
                t.append(now); t[:] = [x for x in t if now - x < 60]
                log(f"bag: rupees{rel:+#x} endret {old} -> {v} (lokalt)")
                if len(t) >= 10:
                    self.ignored.add(rel); self._save()
                    log(f"bag: rupees{rel:+#x} endrer seg {len(t)} ganger/min – ignoreres (trolig tilstand, ikke beholdning)")
                elif v < old:
                    self.last[rel] = old
                    self.mark_delta(rel, "lokal")
                    vals[rel] = self.counters[rel].tick()
                    continue
                self.last[rel] = v
            vals[rel] = v
        cums = {rel: c.my_cum for rel, c in self.counters.items()}
        return vals, cums

    def apply(self, msg, reset, now):
        """Bruk vennens bag-data. JSON-nøkler er strenger."""
        for r in msg.get("bag_delta", []):
            if r in self.rels and r not in self.delta:
                self.mark_delta(r, "lært av vennen")
        for r in msg.get("bag_ignored", []):
            if r not in self.ignored and r in self.rels:
                self.ignored.add(r); self._save()
                log(f"bag: rupees{r:+#x} ignoreres (lært av vennen)")
        cums = {int(k): v for k, v in (msg.get("bag_cums") or {}).items()}
        vals = {int(k): v for k, v in (msg.get("bag") or {}).items()}
        for rel, c in self.counters.items():
            if rel in cums:
                c.apply(cums[rel], reset)
            c.equalize(vals.get(rel), now, force=reset)
        for rel, rv in vals.items():
            if rel in self.counters or rel in self.ignored or rel not in self.rels or rel not in self.last:
                continue
            cur = self._read(rel)
            if isinstance(rv, int) and 0 <= rv <= 0xFFFFFFFF and rv > cur:
                merged = max(cur, rv)
                if merged > cur:
                    log(f"inventar: rupees{rel:+#x} {cur} -> {merged} (oppgradering/ting synket)")
                    self._write(rel, merged)

    def owned(self):
        return sum(1 for r in self.rels if r not in self.ignored and self.last.get(r))


def learn_table(p, rup, state, now):
    """Lære-modus: logg endringer i hele variabeltabellen rundt rupees (utenom inventar-blokken),
    så vi kan kartlegge hjerter, magi, flagg osv. ved å se hva som endrer seg når man gjør noe."""
    try:
        words = p.u32(rup - LEARN_SPAN * ENTRY, 2 * LEARN_SPAN * ENTRY // 4)
    except OSError:
        return
    step = ENTRY // 4
    marker = p.u32(rup + 12)
    for k in range(2 * LEARN_SPAN):
        i = k * step
        if words[i + 3] != marker:
            continue
        rel = (k - LEARN_SPAN) * ENTRY
        if BAG_FIRST <= rel <= BAG_LAST or rel in (0x2738, 0x2760):   # bag logges av BagSync; «siste endring» er støy
            continue
        v = words[i]
        old = state.get(rel)
        state[rel] = v
        if old is not None and old != v and v < 100000 and old < 100000:
            n = state.setdefault(("n", rel), 0) + 1
            state[("n", rel)] = n
            if n <= 20:   # ikke spam loggen med poster som endrer seg hele tiden
                log(f"lær: rupees{rel:+#x} {old} -> {v} (type {words[i + 5]:#x})")


# ======================================================================= app
BG, FG, MUTED, OK, WARN, ACC = "#0b1410", "#efe6c8", "#8a9a85", "#5cc85c", "#e0a030", "#e8c35a"
# Zelda-palett: skog-grønt, pergament-tekst, gull-rammer
PANEL, FIELD, BORDER, GOLD, GOLD_D, BTN, BTN_H, SEL, HEART = "#13221a", "#0f1a14", "#2c4a35", "#e8c35a", "#9c7c2c", "#1d3324", "#2a4a33", "#2f6d3a", "#ff6b6b"
# --- Ytelsesmåling: summerer tid/antall per del og logger hvert 30. s («ytelse: …») ---
_PERF = {}; _PERF_LK = threading.Lock(); _PERF_T0 = [time.time()]

def perf_add(name, dt, n=1):
    with _PERF_LK:
        c = _PERF.setdefault(name, [0, 0.0, 0.0])
        c[0] += n; c[1] += dt; c[2] = max(c[2], dt)

def perf_report():
    now = time.time(); span = now - _PERF_T0[0]
    if span < 30:
        return
    with _PERF_LK:
        items = sorted(_PERF.items(), key=lambda kv: -kv[1][1]); _PERF.clear(); _PERF_T0[0] = now
    parts = [(f"{k} {v[0] / span:.1f}/s {v[1] / span / 1000:.1f} kB/s maks {v[2]:.0f} B" if k.endswith('-B')   # v0.94.303: bytes
              else f"{k} {v[0] / span:.1f}/s {1000 * v[1] / span:.1f}ms/s maks {1000 * v[2]:.0f}ms") for k, v in items]
    log('ytelse (' + f'{span:.0f} s): ' + ' | '.join(parts))

MODES = ['Story', 'PvP']   # v0.73
GAME_MODES = ('Capture the Flame', 'Deathmatch')   # velges i PvP-lobbyen
LOOKS = ['Green', 'Blue', 'Red', 'Pink', 'Orange', 'Yellow', 'Cyan', 'Purple', 'White', 'Black']   # v0.67: tunikafarge (romfs-mod OoT_MP_Tunic)
TUNIC_LETTER = {'Green': 'G', 'Blue': 'B', 'Red': 'R', 'Pink': 'M', 'Orange': 'O', 'Yellow': 'Y', 'Cyan': 'C', 'Purple': 'P', 'White': 'W', 'Black': 'K'}
TUNIC_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(sys.executable if getattr(sys, "frozen", False) else __file__))),
                         'user', 'load', '0400486024DEC000', 'OoT_MP_Tunic')
COLOR_EN = {'Grønn': 'Green', 'Rød': 'Red', 'Blå': 'Blue', 'Hvit': 'White', 'Gul': 'Yellow', 'Lilla': 'Purple', 'Rosa': 'Pink', 'Oransje': 'Orange', 'Svart': 'Black'}   # hvordan din Link vises hos vennen (Mt_Cloth = trøye + hoveddel av lua)

HAT_COLORS = {
    "Grønn": "#2f8a3b",
    "Blå":   "#2e6fd8",
    "Rød":   "#d63c3c",
    "Lilla": "#8e44ad",
    "Gull":  "#f0c040",
    "Hvit":  "#e6e9ee",
}
HAT_RGB = {
    "Grønn": (0.18, 0.54, 0.23),
    "Blå":   (0.18, 0.44, 0.85),
    "Rød":   (0.84, 0.24, 0.24),
    "Lilla": (0.56, 0.27, 0.68),
    "Gull":  (0.94, 0.75, 0.25),
    "Hvit":  (0.92, 0.94, 0.96),
}

# A (bit 0x1) er prat/bekreft. Speil-Linken i PvP får stikker og øvrige knapper, men ikke denne.
PUPPET_TALK_BIT = 0x1
ZONE_LABELS = {
    "Market_Child": "Market",
    "InsideTheDekuTree": "Deku Tree",
    "KokiriForest_Child": "Kokiri",
    "HyruleField_Child": "Hyrule Field",
}
ROSTER_MODELS = tuple(LOOKS) + ("No tunic",)


def zone_label(banc):
    """Kort stedsnavn til Connected. Ukjente soner vises uten _Child."""
    if not isinstance(banc, str):
        return ""
    banc = banc.strip()
    if not banc:
        return ""
    if banc in ZONE_LABELS:
        return ZONE_LABELS[banc]
    return banc.replace("_Child", "").replace("_", " ")[:28]


def _hearts_badge(hearts):
    """Formater [cur, max] i kvart-hjerter til kompakt visning f.eks. '♥ 3/3' eller '♥ 2.5/3'."""
    if not isinstance(hearts, (list, tuple)) or len(hearts) < 2:
        return ""
    try:
        c, m = int(hearts[0]), int(hearts[1])
    except (TypeError, ValueError):
        return ""
    if m <= 0:
        return ""
    cf = c / 4.0; mf = m / 4.0
    cs = str(int(cf)) if cf.is_integer() else f"{cf:.2f}".rstrip("0").rstrip(".")
    ms = str(int(mf)) if mf.is_integer() else f"{mf:.2f}".rstrip("0").rstrip(".")
    return f"♥ {cs}/{ms}"


def connected_line(name, zone="", model="", you=False, mode="", hearts=None):
    """Én rad: nick, hvor de er, tunika-modell, modus og ev. hjerter."""
    you_s = " (you)" if you else ""
    hb = _hearts_badge(hearts)
    parts = [p for p in (zone_label(zone), str(model).strip() if model else "", str(mode).strip() if mode else "", hb) if p]
    mid = ("  ·  " + "  ·  ".join(parts)) if parts else ""
    return f"● {name or '?'}{you_s}{mid}"


def connected_items(names, roster, you, self_zone, self_model, peers=None, self_mode="", self_hearts=None):
    """Connected-rader. Serverlista er rekkefølgen. Tom sone eller modell fylles fra egen tilstand eller P2P."""
    peers = peers or {}
    by = {}
    if isinstance(roster, list):
        for row in roster:
            if isinstance(row, dict) and row.get("name"):
                by[str(row["name"])] = row
    order = list(names) if isinstance(names, list) else sorted(by)
    out = []
    for name in order:
        row = by.get(name) or {}
        peer = peers.get(name) or {}
        if name == you:
            zone = self_zone or row.get("zone") or ""
            model = self_model or row.get("model") or ""
            mode = self_mode or row.get("mode") or ""
            hearts = self_hearts if self_hearts is not None else row.get("hearts")
        else:
            zone = row.get("zone") or peer.get("zone") or ""
            model = row.get("model") or peer.get("model") or ""
            mode = row.get("mode") or peer.get("mode") or ""
            hearts = peer.get("hearts") if peer.get("hearts") is not None else row.get("hearts")
        out.append(connected_line(name, zone, model, you=(name == you), mode=mode, hearts=hearts))
    return out


def mask_puppet_pad(raw, share_interact):
    """Behold stikkene. I PvP fjernes A, så speil-Linken ikke starter NPC-prat eller bekrefter meldinger."""
    if share_interact or not raw:
        return raw
    data = bytearray(raw)
    if len(data) < 12:
        return bytes(data)
    for off in (0, 4, 8):
        word = struct.unpack_from("<I", data, off)[0]
        struct.pack_into("<I", data, off, word & ~PUPPET_TALK_BIT)
    return bytes(data)


def mirror_bodies(player_count):
    """Én Link speiler de andre, også ved 10+. En tredje Player_Child henger spillet."""
    return 1 if int(player_count or 0) >= 1 else 0


def visible_fairies(player_count):
    """Lokal Link har spillets Navi. Speil-Linken har sin egen. De deler ikke fe."""
    return 1 + mirror_bodies(player_count)


def assign_fairies(ordered_actors, mine_id, puppet_id):
    """Nærmest spilleren først. En låst id beholdes. Samme aktør blir aldri begges fe."""
    alive = []
    seen = set()
    for actor in ordered_actors:
        if actor in seen:
            continue
        seen.add(actor)
        alive.append(actor)
    mine = mine_id if mine_id in seen else None
    puppet = puppet_id if puppet_id in seen and puppet_id != mine else None
    for actor in alive:
        if mine is None:
            mine = actor
            continue
        if puppet is None and actor != mine:
            puppet = actor
            break
    if puppet == mine:
        puppet = None
    return mine, puppet


def navi_orbit(pos, now):
    """Skulderhøyde rundt en Link. Brukes bare på en levende Navi."""
    ang = now * 1.6
    return [pos[0] + 0.45 * math.cos(ang), pos[1] + 1.3 + 0.12 * math.sin(now * 3.1), pos[2] + 0.45 * math.sin(ang)]


class FigureSync:
    r"""v0.10 (eksperimentelt): vennen som EKTE figur i spillet (Saria). Krever patch MBX v3b i Lichii
    (load\0400486024DEC000\OoT_MP_Test\exefs\test_b.pchtxt) og at figuren er laget med oot_re\lag_figur.py,
    som skriver figur.json (pid + actor-VA) ved siden av exe-en. Hvert bilde skrives vennens posisjon i postkassen
    (main+0x6FE388: +0 magi 0x0B4D, +4 f32 x,y,z, +0x10 u64 actor); spillets egen kode kaller da 0x944E70 og flytter figuren."""
    SIG = bytes.fromhex("7f2303d5d1fdffd0308a43b91f362d71")   # hule A (main+0x74410C)
    V3 = bytes.fromhex("fd7bbea9")                             # hule B ord 2 (stp x29,x30) = v3
    def __init__(self):
        self.p = None; self.mbx = None; self.actor = None; self.state = "av"; self.active = False
        self._scan = None; self._jt = 0; self._msg = ""
        self.host = None; self._off = self.Y_OFF; self._lk = threading.Lock(); self._samples = []; self._want = False; self._thr = None
    def _note(self, msg):
        if msg != self._msg:
            self._msg = msg; log(f"figur: {msg}")
    def _find_mbx(self, p):
        off = 0
        while off < p.size:
            n = min(4 << 20, p.size - off)
            try:
                d = p.read(p.base + off, n)
            except (MemoryError, OSError):
                off += n; continue
            i = d.find(self.SIG)
            if i != -1:
                base = off + i - 0x74410C
                ok = p.read(p.base + base + 0x74428C, 4) == self.V3
                return (p.base + base + 0x6FE388) if ok else "gammel"
            off += n
        return None
    def tick(self, p, friend, alive, now, me=None, follow_me=False):
        if p is None:
            self.p = None; self.mbx = None; return
        if p is not self.p:
            self.p, self.mbx, self.actor = p, None, None
        if now - self._jt > 2:                       # les figur.json på nytt hvert 2. s
            self._jt = now
            try:
                with open(os.path.join(APP_DIR, "figur.json"), encoding="utf-8") as f:
                    j = json.load(f)
                self.actor = int(j["actor"], 16) if j.get("pid") == p.pid else None
                self.host = int(j["host"], 16) if (self.actor and j.get("host")) else None
                if self.actor is None:
                    self._note("figur.json hører til en annen Lichii-økt – lag figuren på nytt")
            except (FileNotFoundError, ValueError, KeyError):
                self.actor = None
        if self.actor is None:
            self._stop(); return
        if self.mbx is None:
            if self._scan is None:
                self._note("leter etter patch v3 (postkasse) …")
                self._scan = {}
                threading.Thread(target=lambda: self._scan.update(r=self._find_mbx(p)), daemon=True).start()
                return
            if "r" not in self._scan:
                return
            r = self._scan["r"]; self._scan = None
            if not isinstance(r, int):
                self._note("patch v3 er ikke lastet i Lichii" if r is None else "gammel patch (ikke v3) – start Lichii på nytt")
                self.actor = None; self._jt = now + 30; return
            self.mbx = r; self._note(f"postkasse funnet, figur 0x{self.actor:X}")
        pos = friend.get("pos") if (alive and friend) else None
        if pos is None and follow_me and me:          # test alene: figuren går 2 m bak meg
            fx, fz = me[3], me[4] if len(me) > 4 else 0
            n = math.hypot(fx, fz) or 1
            pos = [me[0] - fx / n * 2, me[1], me[2] - fz / n * 2]
        ok = bool(pos and len(pos) == 3 and all(math.isfinite(v) and abs(v) < 1e5 for v in pos))
        if ok and self._samples and math.dist(self._samples[-1][1], pos) > 15:   # v0.56: vennen teleporterte –
            self._jump_hold = now + 8.0                                         # ikke dra figuren inn i et rom som lastes
            self._samples.clear()
        if ok and now < getattr(self, '_jump_hold', 0):
            ok = False
        with self._lk:
            if ok:
                if not self._samples or list(self._samples[-1][1]) != list(pos):
                    self._samples.append((now, tuple(pos)))
                    del self._samples[:-8]
                self._want = True
            else:
                self._want = False
        if ok and not self.active:
            self.active = True; self._note("figuren følger vennen (jevn interpolering, 120 Hz)")
        if not ok:
            self._stop()
        if self._thr is None:
            self._thr = threading.Thread(target=self._writer, daemon=True); self._thr.start()

    Y_OFF = -0.58                                     # Links post ligger 0,58 m over bakken (målt); uten dette faller figuren og spretter
    DELAY = 0.10                                      # vis vennen 100 ms bak sanntid → alltid to punkter å gli mellom
    def _interp(self, t):
        sm = self._samples
        if not sm:
            return None
        if t <= sm[0][0]:
            return sm[0][1]
        for (t0, a), (t1, b) in zip(sm, sm[1:]):
            if t0 <= t <= t1:
                k = (t - t0) / ((t1 - t0) or 1e-6)
                return tuple(a[i] + (b[i] - a[i]) * k for i in range(3))
        return sm[-1][1]                              # ingen nyere pakke: stå på siste punkt
    def _writer(self):
        while True:
            time.sleep(1 / 120)
            try:
                with self._lk:
                    if not (self._want and self.mbx and self.p and self.actor):
                        continue
                    pos = self._interp(time.time() - self.DELAY); p, mbx, actor = self.p, self.mbx, self.actor
                if pos is None:
                    continue
                y = pos[1] + self.Y_OFF
                host = self.host
                if host:                                   # v0.24: områdebytte sletter figuren → aldri kall 0x944E70 på frigjort minne (heng/krasj)
                    vt = struct.unpack("<Q", p.read(p.base + host, 8))[0]
                    if getattr(self, "_vt", None) is None or getattr(self, "_vt_host", None) != host:
                        self._vt, self._vt_host = vt, host
                    elif vt != self._vt:
                        with self._lk:
                            self.actor = None
                        p.write(mbx, bytes(4))
                        log("figur: figuren er borte (områdebytte?) – slutter å skrive. Lag den på nytt.")
                        continue
                if host:                                   # v0.13: la fysikken styre høyden (unngår sprett i bakker/trapper)
                    cur = struct.unpack("<f", p.read(p.base + host + 0x320, 4))[0]
                    if math.isfinite(cur):
                        # v0.16: lær høydeforskjellen mellom vennens post og bakken der hun står.
                        # target = vennens y + off. Faller hun under target → bakken er lavere → off ned.
                        # Står hun over target (bakken holder henne oppe) → off opp. Hun settes ALDRI under sin egen høyde
                        # (= aldri inn i bakken), og løftes bare så mye som vennen faktisk går opp.
                        target = pos[1] + self._off
                        err = cur - target
                        if abs(err) < 3.0:
                            # v0.17: lær raskt NED (bakken er lavere), men bare sakte OPP. Før fulgte off henne opp
                            # så raskt at target alltid ≈ hennes høyde → i oppoverbakke ble hun flyttet inn i bakken og falt gjennom.
                            # v0.18: tregere læring ned (0,03) + løft foran i oppoverbakke (vennens stigefart × 0,25 s),
                            # ellers rekker hun ikke opp når man løper i bakke og går inn i terrenget.
                            self._off += (0.03 if err < 0 else 0.003) * err
                            self._off = max(self._off, self.Y_OFF - 1.2)
                            now = time.time(); py, pt = getattr(self, "_py", (pos[1], now))
                            if now - pt > 0.05:
                                vy = (pos[1] - py) / (now - pt); self._py = (pos[1], now)
                                self._vy = 0.4 * getattr(self, "_vy", 0.0) + 0.6 * vy
                            lead = max(0.0, min(getattr(self, "_vy", 0.0) * 0.6 + (0.15 if getattr(self, "_vy", 0.0) > 0.3 else 0.0), 1.5))
                            y = max(cur, pos[1] + self._off + lead)
                        elif err < 0:                       # langt under (falt gjennom/ned en skrent): sett henne på target
                            y = target
                        else:
                            y = cur
                # v0.20: måling viste at spillet IGNORERER skrevet høyde ved korte flytt (hun fulgte terrenget innenfra, 5 m under),
                # men ved et stort hopp (~5 m) ble hun teleportert til riktig høyde. Står hun > 0,5 m under målet: «spark» via et punkt
                # 6 m over i ett bilde, så tilbake til målet → teleport til riktig høyde.
                # v0.23: spark fjernet (sidelengs teleport løftet henne ikke; loddrett ga fall). I stedet: hold igjen farten
                # vannrett når hun ligger under målet (oppoverbakke) – sakte gange i bakke virker, så hun får tid til å følge terrenget.
                tx, tz = pos[0], pos[2]
                now = time.time(); lx, lz, lt = getattr(self, "_xz", (tx, tz, now)); dt = min(now - lt, 0.1)
                under = host and math.isfinite(cur) and y - cur > 0.25
                vmax = 2.5 if under else 12.0
                dx, dz = tx - lx, tz - lz; dist = math.hypot(dx, dz)
                if dist > 8.0:
                    lx, lz = tx, tz                                  # langt unna (teleport/områdebytte): hopp rett dit
                elif dist > vmax * dt:
                    k = vmax * dt / dist; lx, lz = lx + dx * k, lz + dz * k
                else:
                    lx, lz = tx, tz
                self._xz = (lx, lz, now); pos = (lx, pos[1], lz)
                p.write(mbx + 4, struct.pack("<3f", pos[0], y, pos[2]) + struct.pack("<Q", actor))   # +4 x,y,z | +0x10 actor
                p.write(mbx, struct.pack("<I", 0x0B4D))
            except OSError:
                with self._lk:
                    self.mbx = None
            except Exception as e:  # noqa: BLE001
                log(f"figur-skriver feil: {e!r}"); time.sleep(1)
    def _stop(self):
        with self._lk:
            self._want = False; self._samples.clear()
        if self.active and self.mbx and self.p:
            try:
                self.p.write(self.mbx, bytes(4))
            except OSError:
                pass
            self._note("figuren står (ingen venn)")
        self.active = False


class PadLink:
    """INP v4 + posisjons-/kamerasynk + drop-in/drop-out (v0.29): Link-kopien = spiller 2 over nett.
    - Finner R raskt (2 MB-justert søk ~0,02 s, fullt søk som reserve).
    - Lærer spillerens og kopiens x19 (også hvis modden startes på nytt etter at kopien er laget via R+0x288).
    - Finner heap-delta fra x19 sine selv-pekere (+0x38/+0x40) og slår opp actor = *(x19+0x18) + transform x8/x9.
    - Kjører egen 120 Hz bakgrunnstråd som roterer vennens venstre stikke etter sanntids kameravinkel og synker posisjon/rotasjon jevnt.
    - Drop-in / Drop-out: skjuler Link 2 på stedet (skala 0) når vennen kobler fra, og viser ham igjen ved tilkobling."""
    MARK, R_OFF, MAGIC, ACT_VT = 0x4F4F504E, 0x4D6B900, 0xB4E, 0x4B25E18

    def __init__(self):
        self.hR = None; self.R = None; self.main = None; self.player = None; self.copy = None
        self.delta = None; self.p_act = None; self.p_x8 = None; self.c_act = None; self.c_x8 = None; self.c_x9 = None
        self.p_x19_h = None; self.c_x19_h = None
        self.scene_changed = False; self.last_pos = None; self.last_warp_t = 0
        self.cur_banc = None; self.friend_banc = None; self._banc_t = 0; self._banc_since = 0
        self._friend_tp_t = 0.0; self._evarg_ctor_fails = 0; self._last_call_err = None
        self.h_blm = None; self.h_evarg = None
        self._p_act_since = 0.0; self._last_p_act = None
        self._pending_tp = None        # (banc, pos, rot, t) – teleport etter ankomst (TVANG / /tp på tvers av soner)
        self._last_tp_done = 0.0       # v0.94.154: siste fullførte teleport (dobbeltsperre mot frys)
        self.suppress_warp_until = 0   # ikke send dør-varsel for vårt eget tvangs-sonebytte
        self.seen = {}; self.busy = False; self.last_try = 0; self.active = False; self.has_v4 = False
        self._lk = threading.Lock()
        self._call_lk = threading.Lock(); self._ev_lk = threading.Lock(); self._call_timeouts = 0
        self._p = None; self._cam_off = None; self._alive = False; self._hidden = False
        self._pad_hex = None; self._f_cam_a = None; self._my_cam_a = None
        self._t_pos = None; self._t_rot = None
        self._thr = None
        self._last_zero_t = 0
        self._last_spawn_try = 0
        self._deleting = False; self._last_del_try = 0.0
        self._deleted_x19 = None; self._deleted_until = 0.0
        self._f_hearts = None
        self._c_sv_cur = None; self._c_sv_max = None; self._last_hp_sync = 0.0
        self.pvp_message_filter = False
        self.share_interact = True   # Story deler knapper. PvP skrur dette av, så speil-Linken ikke prater.

    def set_pvp_message_filter(self, p, enabled):
        """Native OutOfNoEscapeArea-sperre: aktiv kun i PvP, aldri i Story."""
        self.pvp_message_filter = bool(enabled)
        if self.hR is None:
            return False
        p.write(p.base + self.hR + 0xEF8, struct.pack('<I', int(self.pvp_message_filter)))
        log(f'pvp-meldingssperre: {"på" if enabled else "av"}')
        return True

    def _find(self, p):
        needle = struct.pack("<I", self.MARK)
        # R ligger på main+0x4D6B900; i vertsminnet slutter hR alltid på 0xD8B900 eller 0x18B900 -> ~0,01 s
        hi_fast = min(p.size, 0x3C0000000)
        for low in (0xD8B900, 0x18B900, 0x8B900):
            for off in (*range(0x280000000 + low, hi_fast, 0x200000), *range(low, min(0x280000000, hi_fast), 0x200000)):
                try:
                    d = p.read(p.base + off + 0x298, 16)
                except OSError:
                    continue
                if d[:4] == needle:
                    va = struct.unpack_from("<Q", d, 8)[0]      # markør (4) + fyll (4) + R (8) på +0x2A0
                    if va & 0xFFF == 0x900 and va > self.R_OFF:
                        return off, va
        for off in range(0, p.size, CHUNK):          # reserve: full skanning der uleselige biter hoppes over
            try:
                b = p.read(p.base + off, min(CHUNK, p.size - off))
            except OSError:
                continue
            i = b.find(needle)
            while i != -1:
                if 0x298 <= i and i + 0x10 <= len(b):
                    va = struct.unpack_from("<Q", b, i + 8)[0]
                    if va & 0xFFF == 0x900 and va > self.R_OFF:
                        return off + i - 0x298, va
                i = b.find(needle, i + 1)
        return None, None

    def _u64(self, p, va):
        if not va or self.delta is None:
            return 0
        h = va - self.delta
        if not (0 <= h <= p.size - 8):
            return 0
        return struct.unpack("<Q", p.read(p.base + h, 8))[0]

    def _ensure_delta(self, p, x19, reset_delta=True):
        if self.delta is not None:
            try:
                if p.read(p.base + x19 - self.delta + 0x38, 16) == struct.pack("<2Q", x19 + 0x7648, x19 + 0x7610):
                    return True
            except OSError:
                pass
            if not reset_delta:
                return False
            self.delta = None
        exp = struct.pack("<2Q", x19 + 0x7648, x19 + 0x7610)
        for step in (0x200000, 0x10000):
            low = (x19 + 0x38) & (step - 1)
            hi_fast = min(p.size, 0x3A0000000)
            for off in (*range(0x280000000 + low, hi_fast, step), *range(low, p.size, step)):
                try:
                    if p.read(p.base + off, 16) == exp:
                        self.delta = x19 - (off - 0x38)
                        log(f"PadLink: heap-delta +0x{self.delta:X}")
                        return True
                except OSError:
                    continue
        return False

    def _is_valid_x19(self, p, x19, reset_delta=True):
        if not x19 or not self._ensure_delta(p, x19, reset_delta=reset_delta):
            return False
        try:
            a = self._u64(p, x19 + 0x18)
            if not a:
                return False
            vt_exp = (self.main or 0) + self.ACT_VT
            return self._u64(p, a) == vt_exp
        except OSError:
            return False

    def _resolve_actors(self, p):
        x0 = self.player or self.copy
        if not x0 or not self._ensure_delta(p, x0):
            return
        vt_exp = (self.main or 0) + self.ACT_VT
        if self.player:
            if not self._is_valid_x19(p, self.player):
                log("PadLink: spiller-actor er borte (områdebytte)")
                self.player = None
                self.p_act = self.p_x8 = self.p_x19_h = None
                self.scene_changed = True
            else:
                self.p_x19_h = self.player - self.delta
                a = self._u64(p, self.player + 0x18)
                self.p_act = a - self.delta
                p270 = self._u64(p, a + 0x270)
                p50 = self._u64(p, p270 + 0x50) if p270 else 0
                x8 = self._u64(p, p50 + 0x20) if p50 else 0
                if x8:
                    self.p_x8 = x8 - self.delta
        if self.copy:
            if not self._is_valid_x19(p, self.copy, reset_delta=(self.player is None)):
                log("PadLink: kopi-actor er borte – nullstiller kopi")
                self.copy = None
                self.c_act = self.c_x8 = self.c_x9 = self.c_x19_h = None
                if self.hR is not None:
                    try:
                        p.write(p.base + self.hR + 0x288, bytes(8))
                    except OSError:
                        pass
            else:
                self.c_x19_h = self.copy - self.delta
                a = self._u64(p, self.copy + 0x18)
                c270 = self._u64(p, a + 0x270)
                c50 = self._u64(p, c270 + 0x50) if c270 else 0
                x8 = self._u64(p, c50 + 0x20) if c50 else 0
                x9 = self._u64(p, x8 + 0x1C8) if x8 else 0
                if not x8:   # x19 gyldig men uten komponenter = halvslettet «zombie» – glem den så en ny lages
                    if not getattr(self, "_c_bad_since", 0):
                        self._c_bad_since = time.time()
                    elif time.time() - self._c_bad_since > 3.0:
                        log(f"PadLink: kopi 0x{self.copy:X} mangler komponenter (zombie) – lager ny Link 2")
                        self._deleted_x19 = self.copy; self._deleted_until = time.time() + 1e9
                        self.copy = None; self.c_act = self.c_x8 = self.c_x9 = self.c_x19_h = None
                        self._c_bad_since = 0
                        try: p.write(p.base + self.hR + 0x288, bytes(8))
                        except OSError: pass
                        return
                else:
                    self._c_bad_since = 0
                if x8:
                    if self.c_act != a - self.delta:
                        log(f"PadLink: kopi-actor 0x{a:X} (vert +0x{a - self.delta:X}), x8 0x{x8:X}")
                    self.c_act, self.c_x8, self.c_x9 = a - self.delta, x8 - self.delta, (x9 - self.delta if x9 else None)
                self._silence_copy_savevars(p, a)

    SAVEVAR_VT = 0x4B63438

    def _silence_copy_savevars(self, p, c_act_va):
        """Hindre Link 2 (kopien) fra å skrive sitt eget liv/maks-liv over spillerens SaveContext (hjerte-flimring)."""
        if not self.copy or not self.delta or not self.main:
            return
        try:
            c_sub = self.copy - 0x1F40
            if self._u64(p, c_sub + 0x18) != c_act_va:
                return
            vt_exp = self.main + self.SAVEVAR_VT
            for rel in (0x1C10, 0x1C18):
                sv = self._u64(p, c_sub + rel)
                if sv and self._u64(p, sv) == vt_exp:
                    val_off = sv - self.delta + 0x8
                    if rel == 0x1C10:
                        self._c_sv_cur = val_off
                    else:
                        self._c_sv_max = val_off
                    key_off = sv - self.delta + 0xC
                    key = struct.unpack("<I", p.read(p.base + key_off, 4))[0]
                    if key != 0:
                        p.write(p.base + key_off, bytes(4))
                        log(f"PadLink: deaktiverte kopi SaveVar +0x{rel:X} (gammel nøkkel 0x{key:08X} -> 0)")
        except OSError:
            pass

    # ------------------------------------------------------------ CALL v1: spillkall uten GDB (call_v1.pchtxt)
    CALL_OFF = 0x700            # postkasse M = R+0x700: +0 tilstand (1 kall, 2 kjører, 3 ferdig), +8 funksjon, +0x10 x0..x7, +0x50 resultat
    F_ALLOC, F_EVARG_CTOR, F_EV_START, GOT_EVMGR = 0x3ECA0, 0xD79F10, 0xD7A820, 0x4C7E090
    GOT_ACTMGR, F_ACT_CREATE, F_ACT_DELETE = 0x4C7F3E0, 0x372A70, 0xA6490
    F_AS_PLAY = 0x2022A0             # spill AS-kommando (forespørsel på +0: aktør, +8 navn, +0x10 slot, +0x14 fart, +0x18/+0x1C -1, +0x20 hopp-hvis-lik)

    def _u64v(self, p, va):
        return struct.unpack('<Q', p.read(p.base + va - self.delta, 8))[0]

    def read_anim(self, p, a):
        """(navn, bilde) for aktørens AS-slot 0, eller (None, None). Kjede: [[[[akt+0x270]+0x40]+0x18]+0x18] = kontroller, +0x20 slot-tabell."""
        try:
            c = self._u64v(p, self._u64v(p, self._u64v(p, struct.unpack('<Q', p.read(p.base + a + 0x270, 8))[0] + 0x40) + 0x18) + 0x18)
            if struct.unpack('<i', p.read(p.base + c - self.delta + 0x18, 4))[0] <= 0:
                return None, None
            slot = self._u64v(p, self._u64v(p, c + 0x20))
            nptr = self._u64v(p, slot + 0x10)
            cache = self.__dict__.setdefault('_anim_names', {})
            name = cache.get(nptr)
            if name is None:   # navnet ligger utenfor hovedminnet – les via spillets LD8-gadget (8 byte per kall), mellomlagres
                if len(cache) > 2000:
                    cache.clear()
                raw = b''
                for k in range(0, 64, 8):
                    v = self.game_call(p, self.F_LD8, (nptr + k - 8,), timeout=0.5)
                    if v is None:
                        return None, None
                    raw += struct.pack('<Q', v & 0xFFFFFFFFFFFFFFFF)
                    if b'\0' in raw:
                        break
                name = raw.split(b'\0', 1)[0].decode('ascii', 'replace')
                cache[nptr] = name
            try:
                frame = struct.unpack('<f', p.read(p.base + slot - self.delta + 0xE8, 4))[0]
            except OSError:
                frame = 0.0
            return (name or None), round(frame, 1)
        except Exception:  # noqa: BLE001
            return None, None

    def set_anim_frame(self, p, a, frame):
        """v0.62: sett bildenummeret i AS-slot 0 (samme kjede som read_anim)."""
        try:
            c = self._u64v(p, self._u64v(p, self._u64v(p, struct.unpack('<Q', p.read(p.base + a + 0x270, 8))[0] + 0x40) + 0x18) + 0x18)
            slot = self._u64v(p, self._u64v(p, c + 0x20))
            p.write(p.base + slot - self.delta + 0xE8, struct.pack('<f', float(frame)))
            return True
        except Exception:  # noqa: BLE001
            return False

    def play_anim(self, p, a, name):
        """Be aktøren spille AS-kommandoen `name` på slot 0 (spillets egen avspilling)."""
        if not name or len(name) > 70 or not self.actor_alive(p, a):
            return None
        try:
            if struct.unpack('<I', p.read(p.base + a + 0x2C, 4))[0] != 4:
                return None
        except OSError:
            return None
        blk = getattr(self, '_anim_blk', None)
        if blk is None:
            va = self.game_call(p, self.F_ALLOC, (0x10, 0x8000))
            if not va:
                return None
            # v0.72: er minnet koblet slik modden tror? (F_ALLOC-minne lå av og til et annet sted – spillet leste nuller)
            ok = False
            try:
                p.write(p.base + va - self.delta, b'ANIMCHK\0')
                ok = struct.pack('<Q', (self.game_call(p, self.F_LD8, (va - 8,)) or 0) & 0xFFFFFFFFFFFFFFFF) == b'ANIMCHK\0'
            except OSError:
                pass
            self._anim_blk = blk = (va if ok else False); self._anim_cells = {}
            log(f'animasjon: avspillingsminne {"F_ALLOC" if ok else "patch-område (F_ALLOC ikke koblet)"}')
        cells = self._anim_cells
        if blk:
            if a not in cells:
                if len(cells) >= 120:
                    cells.clear()
                cells[a] = len(cells)
            i = cells[a]
            name_va = blk + 0x100 * i; req_va = name_va + 0x80
            hn, hq = p.base + name_va - self.delta, p.base + req_va - self.delta
        else:   # én celle i patch-området R+0xE00..0xE7F (navn 0x40, forespørsel 0x30; 0x700 er CALL-postkassen)
            name_va = self.R + 0xE00; req_va = self.R + 0xE40
            hn, hq = p.base + self.hR + 0xE00, p.base + self.hR + 0xE40
        try:
            p.write(hn, name.encode('ascii')[:0x3F] + b'\0')
            p.write(hq, struct.pack('<QQifffBxxxxxxxQ', a + self.delta, name_va, 0, 1.0, -1.0, -1.0, 1, 0))
        except OSError:
            return None
        return self.game_call(p, self.F_AS_PLAY, (req_va,), timeout=1.0)

    WEB_SPRING_ID = 0x7E3D5B9D        # constraint-id for gulvvevets fjaer-kontakt

    def deku_web_body(self, p, actor):
        """Finn vevets fjaerlegeme (spill-VA), eller None hvis kjeden ikke finnes.

        Kjeden: actor -> physics(+0x270) -> controllers(+0x50) -> constraints(+0xD8)
                -> entry(id=0x7E3D5B9D) -> slider -> body(+0x110).
        Legemet verifiseres paa masse 180 (float32 paa +0x13C).
        """
        u = lambda address: self._gv_u64(p, address)
        i = lambda address: self._gv_u32(p, address)
        try:
            physics = u(actor + self.delta + 0x270)
            controllers = u(u(physics + 0x50) + 0x20)
            constraints = u(u(controllers + 0xD8) + 0x20)
            count = i(constraints + 0x10)
            if not 0 < count <= 32:
                return None
            entries = u(constraints + 0x18)
            for index in range(count):
                entry = u(entries + index * 8)
                if i(entry) == self.WEB_SPRING_ID:
                    slider = u(entry + 0x20)
                    break
            else:
                return None
            if u(slider) != self.main + 0x4C35DC8:
                return None
            body = u(slider + 0x110)
            if abs(p.f32(body - self.delta + 0x13C) - 180.0) > 0.1:
                return None
            return body
        except (OSError, ValueError, struct.error):
            return None

    def deku_web_y(self, p, body):
        """Fjaerlegemets hoyde (Y) i spillkoordinater, eller None."""
        try:
            return float(p.f32(body - self.delta + 0x9C))
        except (OSError, ValueError, struct.error):
            return None

    def deku_web_impulse(self, p, actor, impulse, body=None):
        """Apply one downward impulse to the floor web's native spring body.

        Spillets rutine (main+0x38BF1C0) gjoer: v += impuls * (1/masse).
        Med masse 180 gir impuls 380 et farts-steg paa 2,1 m/s.
        """
        if self.cur_banc != 'InsideTheDekuTree' or not self.actor_alive(p, actor):
            return False
        if not body:
            body = self.deku_web_body(p, actor)
        if not body:
            return False
        try:
            # R+0xED0 is reserved for the web impulse vector.
            p.write(p.base + self.hR + 0xED0, struct.pack('<3f', 0, -impulse, 0))
            return self.game_call(p, 0x38BF1C0, (body, self.R + 0xED0), timeout=0.35) is not None
        except (OSError, ValueError, struct.error):
            return False

    AIHOLD_TABLE_R = 0x600   # aihold_v1.pchtxt: tabellen ligger i R+0x600 (+0 antall<=16, +4 and, +8 or, +0x10 komponenter)

    TARGET_MBOX_R = 0x780          # target_v2.pchtxt: +0 Link 2-aktør, +8 teller, +0x10 siste mål, +0x18 Link 2 valgt, +0x20 fiende, +0x28 modus

    def set_target_link2(self, p, mode=0):
        """Fortell mål-patchen hvor Link 2 er (0 = av). modus 0 = fienden velger nærmeste Link, 1 = alltid Link 1, 2 = alltid Link 2."""
        if self.hR is None:
            return False
        if self.copy and self.c_act is not None and self.delta is not None:
            va = self.c_act + self.delta
        elif getattr(self, "_active_puppet_act", None) is not None and self.delta is not None and self.actor_alive(p, self._active_puppet_act):
            va = self._active_puppet_act + self.delta
        else:
            va = 0
        try:
            h = p.base + self.hR + self.TARGET_MBOX_R
            p.write(h + 0x28, struct.pack('<I', mode))
            p.write(h, struct.pack('<Q', va))
            return va
        except OSError:
            return False

    def set_blind(self, p, actors):
        """dist_v1 v0.52: disse aktørene (kopier vi følger) ser ingen Link -> egen AI angriper ikke; eierens animasjon vises."""
        if self.hR is None or self.delta is None:
            return False
        vals = [a + self.delta for a in actors[:8]] + [0] * (8 - len(actors[:8]))
        try:
            p.write(p.base + self.hR + self.TARGET_MBOX_R + 0x40, struct.pack('<8Q', *vals))
            return True
        except OSError:
            return False

    def target_stats(self, p):
        """(kall, ganger Link 2 valgt, aihold-pauser) – viser om patchene er lastet og i bruk."""
        try:
            h = p.base + self.hR
            n, _l, k = struct.unpack('<QQQ', p.read(h + self.TARGET_MBOX_R + 8, 24))
            ah = struct.unpack('<Q', p.read(h + self.AIHOLD_TABLE_R + 0xF8, 8))[0]
            return n, k, ah
        except (OSError, TypeError):
            return None

    PERC_CTX, PERC_OFF = 0x538, 0x1D38   # sanse-komponenten (Perception): [[akt+0x270]+0x538]+0x1D38; eier +0x58, matriser +0x360 og +0x390
    def sync_l2_perception(self, p):
        """Fiendene «ser» spilleren via Perception-komponenten. For Link 2 oppdaterer spillet aldri posisjonen der
        (den står igjen der kopien ble laget), så fiendene tror Link 2 står ved Link 1. Vi skriver den ekte posisjonen dit."""
        if self.copy is None or self.c_act is None or self.delta is None:
            return None
        try:
            va = self.c_act + self.delta
            ctx = struct.unpack('<Q', p.read(p.base + self.c_act + 0x270, 8))[0]
            blk = struct.unpack('<Q', p.read(p.base + ctx - self.delta + self.PERC_CTX, 8))[0]
            h = p.base + blk - self.delta + self.PERC_OFF
            if struct.unpack('<Q', p.read(h + 0x58, 8))[0] != va:
                return False                      # ikke Link 2 sin komponent (annen spillversjon/oppsett) – ikke skriv
            x, y, z = p.f32(self.c_act + 0x31C, 3)
            if not all(math.isfinite(v) for v in (x, y, z)):
                return False
            for base in (0x360, 0x390):
                p.write(h + base + 0x04, struct.pack('<f', x)); p.write(h + base + 0x14, struct.pack('<f', y)); p.write(h + base + 0x24, struct.pack('<f', z))
            return True
        except (OSError, struct.error, TypeError):
            return None

    PUPPET_BATCH_R = 0x1700   # puppet_batch_v1.pchtxt: 0x4D6D000 (32B header + 50 * 64B slots = 3232 B)
    PUPPET_MAGIC = 0x50555035
    PUPPET_MAX = 50
    PUPPET_HOOK = 0x03CE044
    PUPPET_HOOK_BYTES = bytes.fromhex("e7 e0 e1 94")
    PUPPET_STEP = 0x3C46300
    PUPPET_POSE_LEASE_R = PUPPET_BATCH_R + 0xCFC
    PUPPET_POSE_GUARD_MAGIC = struct.pack("<I", 0x5047)

    def publish_puppet_pose_owners(self, p, owners):
        if self.hR is None or self.delta is None:
            return
        try:
            lease = p.base + self.hR + self.PUPPET_POSE_LEASE_R
            if getattr(self, "_pose_guard_proc", None) is not p:
                self._pose_guard_active = False
                self._pose_guard_proc = p
                self._pose_guard_owners = None
            if not self._pose_guard_active:
                if p.read(lease - 4, 4) != self.PUPPET_POSE_GUARD_MAGIC:
                    return
                self._pose_guard_active = True
            if owners != self._pose_guard_owners:
                p.write(lease, bytes(4))
                pointers = tuple(owner + self.delta for owner in owners)
                p.write(lease + 4, struct.pack(f"<{len(pointers)}Q", *pointers).ljust(self.PUPPET_MAX * 8, b"\0"))
                self._pose_guard_owners = owners
            if owners:
                # Native copy calls exhaust the lease if the client stops renewing it.
                p.write(lease, struct.pack("<I", 1024))
        except OSError:
            return

    def puppet_batch_available(self, p):
        """Check the loaded executable before enabling the puppet pool."""
        if p is None or self.hR is None or self.main is None or self.R is None:
            return False
        addr = p.base + self.hR + self.main + self.PUPPET_HOOK - self.R
        try:
            return p.read(addr, 4) == self.PUPPET_HOOK_BYTES
        except OSError:
            return False

    def write_puppet_batch(self, p, entries):
        """Skriv opptil 50 dukke-aktører til delt batch-tabell (R+0x1700) i ett enkelt minnekall.
        Hver entry er (actor_host_or_va, (x, y, z), yaw_eller_rot9, force_set_mtx).
        """
        if self.hR is None or self.main is None or self.delta is None or p is None:
            return False
        items = list(entries or ())[:self.PUPPET_MAX]
        seq = (getattr(self, "_pup_seq", 0) + 1) & 0xFFFFFFFF
        self._pup_seq = seq
        act_vt = (self.main + self.ACT_VT) & 0xFFFFFFFFFFFFFFFF
        buf = bytearray(32 + len(items) * 64)
        struct.pack_into("<IIIIQQ", buf, 0, self.PUPPET_MAGIC, len(items), seq, 0, act_vt, 0)
        for idx, item in enumerate(items):
            act, pos, rot_or_yaw = item[0], item[1], item[2]
            force_mtx = bool(item[3]) if len(item) > 3 else True
            act_va = act if act >= self.delta else (act + self.delta)
            if isinstance(rot_or_yaw, (list, tuple)) and len(rot_or_yaw) == 9:
                rot9 = tuple(float(v) for v in rot_or_yaw)
            else:
                yaw = float(rot_or_yaw or 0.0)
                s, c = math.sin(yaw), math.cos(yaw)
                rot9 = (c, 0.0, s, 0.0, 1.0, 0.0, -s, 0.0, c)
            flags = 3 if force_mtx else 1
            off = 32 + idx * 64
            struct.pack_into("<Q3f9fII", buf, off, act_va, float(pos[0]), float(pos[1]), float(pos[2]), *rot9, flags, 0)
        try:
            p.write(p.base + self.hR + self.PUPPET_BATCH_R, bytes(buf))
            return True
        except OSError:
            return False

    def write_puppet_transforms_direct(self, p, entries):
        """v0.94.184: Skriv 48 B pos+rot direkte til act+0x31C og act+0x358 (0 game_call -> ekte 60 Hz uten 1028 ms/s blokkering)."""
        if self.main is None or self.delta is None or p is None:
            return 0
        act_vt = (self.main + self.ACT_VT) & 0xFFFFFFFFFFFFFFFF
        written = 0
        for item in (entries or ())[:self.PUPPET_MAX]:
            act, pos, rot_or_yaw = item[0], item[1], item[2]
            act_h = (act - self.delta) if act >= self.delta else act
            if act_h <= 0 or act_h >= p.size - 0x400:
                continue
            try:
                hdr = p.read(p.base + act_h, 0x30)
                if len(hdr) != 0x30:
                    continue
                vt, state = struct.unpack_from("<Q", hdr, 0)[0], struct.unpack_from("<I", hdr, 0x2C)[0]
                if vt != act_vt or state != 4:
                    continue
                if isinstance(rot_or_yaw, (list, tuple)) and len(rot_or_yaw) == 9:
                    rot9 = tuple(float(v) for v in rot_or_yaw)
                else:
                    yaw = float(rot_or_yaw or 0.0)
                    s, c = math.sin(yaw), math.cos(yaw)
                    rot9 = (c, 0.0, s, 0.0, 1.0, 0.0, -s, 0.0, c)
                b48 = struct.pack("<3f9f", float(pos[0]), float(pos[1]), float(pos[2]), *rot9)
                p.write(p.base + act_h + 0x31C, b48)
                p.write(p.base + act_h + 0x358, b48)
                if float(pos[1]) > -100.0:
                    self._active_puppet_act = act_h
                written += 1
            except OSError:
                continue
        return written

    def puppet_batch_armed(self, p):
        """An empty batch must have completed on this running emulator (or auto-arm once when local Link is ready)."""
        if self.hR is None:
            return False
        try:
            addr = p.base + self.hR + self.PUPPET_BATCH_R
            magic, _, _, ack = struct.unpack('<IIII', p.read(addr, 16))
            if magic == self.PUPPET_MAGIC and ack > 0:
                return True
            if (getattr(self, 'p_act', None) is not None and hasattr(self, 'game_call')
                    and time.time() - getattr(self, '_pup_arm_try_t', 0) > 2.0):
                self._pup_arm_try_t = time.time()
                self.write_puppet_batch(p, ())
                # v0.94.155: godta armingen hvis spillet SETT ack, ogsa returnerer
                # spillet kallet (eller timeout) pa en langsom PC (peer: 330-1200 ms).
                # Før dette ble peeren aldri armert -> tomme batcher -> dukkene stod
                # stille (ack=0 av 9331 skriv).
                self.game_call(p, self.PUPPET_STEP, timeout=2.0)
                magic, _, _, ack = struct.unpack('<IIII', p.read(addr, 16))
                if magic == self.PUPPET_MAGIC and ack > 0:
                    return True
                if time.time() - getattr(self, '_pup_arm_log_t', 0) > 15:
                    self._pup_arm_log_t = time.time()
                    log(f'dukkepool: batchen er ikke armert (ack={ack}) – '
                        f'spillkall={getattr(self, "_last_call_err", None)}')
            return False
        except OSError:
            return False

    PUPPET_BONE_COUNT = 309
    PUPPET_BONE_STRIDE = 0x60
    PUPPET_SKEL_BYTES = 309 * 0x60  # 29664 B
    PUPPET_SYNC_BONES = (
        0, 3, 4, 11, 12, 13, 14, 19, 23,
        57, 58, 59, 64, 68, 102, 103,
        229, 230, 231, 232, 233, 234,
        242, 243, 244, 245, 307, 308,
    )  # 28 hovedbein i Player_Child: 4*s16 quat per bein + 3*s16 rot-translasjon = 230 byte (308 B base64)
    # v0.94.208: eksakte forelder-indekser for alle 27 ikke-rot hovedbein (0.000000 feil mot idle LocalMtx).
    # Player_Child sin LocalMtx (sk+0x18) overskrives i flere pass per bilde (20-38 deg hopp på hode 103 under gange),
    # mens WorldMtx (sk+0x20) er den ferdig rendrede posen. Beregn derfor L = Wc @ Wp^T fra WorldMtx også for hovedbeina.
    PUPPET_SYNC_PARENTS = (
        (3, 0), (4, 0), (11, 4), (12, 11), (13, 12), (14, 13), (19, 14), (23, 19),
        (57, 11), (58, 57), (59, 58), (64, 59), (68, 64), (102, 11), (103, 102),
        (229, 11), (230, 0), (231, 230), (232, 231), (233, 232), (234, 233),
        (242, 230), (243, 242), (244, 243), (245, 244), (307, 230), (308, 0),
    )

    PUPPET_PHYSICS_BONES = tuple(range(104, 229)) + tuple(range(246, 307))
    # v0.94.181: alle 121 Ph_* fysikkbein (lue Ph_Cap_1..7, hår, skjørt, belte) med eksakt forelder-indeks fra BFRES.
    # Nintendo sin Phive-fysikk skriver kun til WorldMtx (sk+0x20), så vi regner ut L = Wc @ Wp^T (0.00000 feil).
    PUPPET_PH_PARENTS = (
        (114, 113), (117, 116), (120, 119), (123, 122), (128, 127), (131, 130), (134, 133), (138, 137),
        (177, 176), (178, 177), (179, 176), (180, 179), (181, 176), (182, 181), (183, 176), (184, 183),
        (185, 184), (186, 176), (187, 186), (188, 187), (189, 188), (190, 176), (191, 190), (192, 191),
        (193, 176), (194, 193), (195, 194), (196, 176), (197, 196), (198, 197), (199, 176), (200, 199),
        (201, 200), (202, 176), (203, 202), (204, 203), (205, 176), (206, 205), (207, 206),
        (208, 104), (209, 208), (210, 209), (211, 210), (212, 211), (213, 212), (214, 213),
        (215, 104), (216, 215), (217, 104), (218, 217), (219, 104), (220, 219), (221, 104), (222, 221),
        (223, 104), (224, 223), (225, 11), (226, 225), (227, 11), (228, 227),
        (246, 243), (247, 243), (248, 247), (249, 243), (250, 243), (251, 242), (252, 242),
        (253, 230), (254, 230), (255, 230), (256, 255), (257, 256), (258, 255), (259, 258), (260, 259),
        (261, 260), (262, 255), (263, 262), (264, 263), (265, 264), (266, 255), (267, 266), (268, 267),
        (269, 268), (270, 255), (271, 270), (272, 271), (273, 272), (274, 255), (275, 274), (276, 275),
        (277, 276), (278, 255), (279, 278), (280, 279), (281, 280), (282, 255), (283, 282), (284, 283),
        (285, 284), (286, 255), (287, 286), (288, 287), (289, 288), (290, 255), (291, 290), (292, 291),
        (293, 292), (294, 255), (295, 294), (296, 295), (297, 296), (298, 255), (299, 298), (300, 299),
        (301, 300), (302, 255), (303, 302), (304, 303), (305, 304), (306, 255),
    )
    PUPPET_FULL_POSE_LEN = (
        4 * (((len(PUPPET_SYNC_BONES) * 4 + 3) * 2 + 2) // 3)
        + 1
        + 4 * ((len(PUPPET_PHYSICS_BONES) * 3 + 2) // 3)
    )

    @staticmethod
    def _compact_quats(values):
        """Store the largest component's index plus three 7-bit components."""
        scale = 63 * math.sqrt(2) / 32767.0
        packed = bytearray()
        for start in range(0, len(values), 4):
            q = values[start:start + 4]
            largest = max(range(4), key=lambda i: abs(q[i]))
            sign = -1 if q[largest] < 0 else 1
            word = largest
            for i, value in enumerate(q):
                if i != largest:
                    word = (word << 7) | (max(-63, min(63, round(value * sign * scale))) + 63)
            packed.extend(word.to_bytes(3, 'little'))
        return bytes(packed)

    @staticmethod
    def _expand_quats(compact):
        scale = 32767.0 / (63 * math.sqrt(2))
        values = []
        for off in range(0, len(compact), 3):
            word = int.from_bytes(compact[off:off + 3], 'little')
            largest = word >> 21
            if largest > 3:
                return None
            q = [round((((word >> shift) & 127) - 63) * scale) for shift in (14, 7, 0)]
            q.insert(largest, round(math.sqrt(max(0, 32767 ** 2 - sum(v * v for v in q)))))
            values.extend(q)
        return struct.pack(f'<{len(values)}h', *values)

    @classmethod
    @functools.lru_cache(maxsize=256)
    def _decode_pose(cls, payload):
        import base64
        body, _, physics = payload.partition('|')
        try:
            raw = base64.b64decode(body, validate=True)
        except ValueError:
            return None
        if len(raw) != (len(cls.PUPPET_SYNC_BONES) * 4 + 3) * 2:
            return None
        if len(physics) == 4 * ((len(cls.PUPPET_PHYSICS_BONES) * 3 + 2) // 3):
            try:
                extra = cls._expand_quats(base64.b64decode(physics, validate=True))
            except ValueError:
                extra = None
            if extra is not None and len(extra) == len(cls.PUPPET_PHYSICS_BONES) * 8:
                return cls.PUPPET_SYNC_BONES + cls.PUPPET_PHYSICS_BONES, raw + extra
        return cls.PUPPET_SYNC_BONES, raw

    @staticmethod
    def _rows_to_quat(m):
        m00, m01, m02, m10, m11, m12, m20, m21, m22 = m
        tr = m00 + m11 + m22
        if tr > 0.0:
            s = math.sqrt(tr + 1.0) * 2.0
            qx, qy, qz, qw = (m21 - m12) / s, (m02 - m20) / s, (m10 - m01) / s, 0.25 * s
        elif m00 > m11 and m00 > m22:
            s = math.sqrt(max(1e-8, 1.0 + m00 - m11 - m22)) * 2.0
            qx, qy, qz, qw = 0.25 * s, (m01 + m10) / s, (m02 + m20) / s, (m21 - m12) / s
        elif m11 > m22:
            s = math.sqrt(max(1e-8, 1.0 + m11 - m00 - m22)) * 2.0
            qx, qy, qz, qw = (m01 + m10) / s, 0.25 * s, (m12 + m21) / s, (m02 - m20) / s
        else:
            s = math.sqrt(max(1e-8, 1.0 + m22 - m00 - m11)) * 2.0
            qx, qy, qz, qw = (m02 + m20) / s, (m12 + m21) / s, 0.25 * s, (m10 - m01) / s
        n = math.sqrt(qx * qx + qy * qy + qz * qz + qw * qw)
        if not (n > 1e-6 and math.isfinite(n)):
            return (0.0, 0.0, 0.0, 1.0)
        if qw < 0.0:
            n = -n
        return (qx / n, qy / n, qz / n, qw / n)

    @staticmethod
    def _quat_to_rows(q):
        qx, qy, qz, qw = q
        n = math.sqrt(qx * qx + qy * qy + qz * qz + qw * qw)
        if not (n > 1e-6 and math.isfinite(n)):
            return (1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0)
        x, y, z, w = qx / n, qy / n, qz / n, qw / n
        return (
            1.0 - 2.0 * (y * y + z * z), 2.0 * (x * y - z * w), 2.0 * (x * z + y * w),
            2.0 * (x * y + z * w), 1.0 - 2.0 * (x * x + z * z), 2.0 * (y * z - x * w),
            2.0 * (x * z - y * w), 2.0 * (y * z + x * w), 1.0 - 2.0 * (x * x + y * y),
        )

    @classmethod
    def pack_skeleton_pose(cls, raw_skel, include_physics=False):
        """Encode body rotations and optionally append the secondary rotations."""
        if not isinstance(raw_skel, (bytes, bytearray)) or len(raw_skel) != cls.PUPPET_SKEL_BYTES:
            return None
        import base64
        indices = cls.PUPPET_SYNC_BONES + cls.PUPPET_PHYSICS_BONES if include_physics else cls.PUPPET_SYNC_BONES
        body_count = len(cls.PUPPET_SYNC_BONES) * 4 + 3

        def encode(values):
            body = base64.b64encode(struct.pack(f'<{body_count}h', *values[:body_count])).decode('ascii')
            if not include_physics:
                return body
            return body + '|' + base64.b64encode(cls._compact_quats(values[body_count:])).decode('ascii')

        rust = cls._get_rust_engine() if hasattr(cls, "_get_rust_engine") else None
        if rust is not None:
            idx_arr, out_shorts, _, _, _ = cls._rust_pack_bufs(indices)
            n = rust.oot_pack_bones(raw_skel, len(raw_skel), idx_arr, len(indices), out_shorts, len(out_shorts))
            if n > 0:
                return encode(out_shorts[:n])
        vals = []
        for idx, bi in enumerate(indices):
            off = bi * cls.PUPPET_BONE_STRIDE
            r0 = struct.unpack_from("<3f", raw_skel, off + 0x20)
            r1 = struct.unpack_from("<3f", raw_skel, off + 0x30)
            r2 = struct.unpack_from("<3f", raw_skel, off + 0x40)
            if not all(math.isfinite(v) for v in (*r0, *r1, *r2)):
                return None
            q = cls._rows_to_quat((*r0, *r1, *r2))
            for c in q:
                vals.append(max(-32767, min(32767, int(round(c * 32767.0)))))
            if idx == 1:  # bi == 3 (Skl_Root): ta også med hoftens translasjon (x, y, z)
                tx, ty, tz = struct.unpack_from("<3f", raw_skel, off + 0x50)
                if not all(math.isfinite(v) for v in (tx, ty, tz)):
                    return None
                for t in (tx, ty, tz):
                    vals.append(max(-32767, min(32767, int(round(t * 4096.0)))))
        return encode(vals)

    @classmethod
    def apply_packed_pose(cls, base_skel, packed_b64):
        """Apply one network pose to the puppet's rest skeleton."""
        return cls.apply_interpolated_pose(base_skel, packed_b64, packed_b64, 1.0)

    @classmethod
    def _get_rust_engine(cls):
        cached = getattr(cls, "_rust_dll", False)
        if cached is not False:
            return cached
        dll = None
        for base_dir in (getattr(sys, "_MEIPASS", None), os.path.dirname(os.path.abspath(__file__)), os.getcwd()):
            if not base_dir:
                continue
            cand = os.path.join(base_dir, "oot_rust_engine.dll")
            if os.path.isfile(cand):
                try:
                    d = ctypes.CDLL(cand)
                    d.oot_pack_bones.argtypes = [
                        ctypes.c_char_p, ctypes.c_size_t,
                        ctypes.POINTER(ctypes.c_uint16), ctypes.c_size_t,
                        ctypes.POINTER(ctypes.c_int16), ctypes.c_size_t,
                    ]
                    d.oot_pack_bones.restype = ctypes.c_int32
                    d.oot_apply_interp_bones.argtypes = [
                        ctypes.c_char_p, ctypes.c_size_t,
                        ctypes.POINTER(ctypes.c_uint16), ctypes.c_size_t,
                        ctypes.POINTER(ctypes.c_int16), ctypes.POINTER(ctypes.c_int16),
                        ctypes.c_size_t, ctypes.c_float, ctypes.c_char_p,
                    ]
                    d.oot_apply_interp_bones.restype = ctypes.c_int32
                    dll = d
                    break
                except OSError:
                    pass
        cls._rust_dll = dll
        return dll

    @classmethod
    def _rust_pack_bufs(cls, indices):
        buffers = getattr(cls._rust_buffers, "buffers", None)
        if buffers is None:
            buffers = cls._rust_buffers.buffers = {}
        if indices not in buffers:
            n = len(indices)
            shorts = n * 4 + 3
            buffers[indices] = (
                (ctypes.c_uint16 * n)(*indices), (ctypes.c_int16 * shorts)(),
                (ctypes.c_int16 * shorts)(), (ctypes.c_int16 * shorts)(),
                ctypes.create_string_buffer(cls.PUPPET_SKEL_BYTES),
            )
        return buffers[indices]

    _rust_buffers = threading.local()

    def smooth_puppet_skeleton(self, actor, skel_bytes):
        """v0.94.218: Rask 60 Hz numpy-glatting av skjelett og 121 Ph_* fysikkbein (lue/hår/skjørt) mot kvantiseringsstøy og mikro-jitter."""
        if not isinstance(skel_bytes, (bytes, bytearray)) or len(skel_bytes) != self.PUPPET_SKEL_BYTES:
            return skel_bytes
        try:
            cur = np.frombuffer(skel_bytes, dtype=np.float32).reshape(self.PUPPET_BONE_COUNT, 24).copy()
            cache = self.__dict__.setdefault("_skel_ema_cache", {})
            prev = cache.get(actor)
            if prev is None or prev.shape != cur.shape:
                cache[actor] = cur
                return skel_bytes
            w = getattr(self, "_skel_ema_w", None)
            if w is None:
                w = np.full((self.PUPPET_BONE_COUNT, 1), 0.45, dtype=np.float32)
                for bi in self.PUPPET_PHYSICS_BONES:
                    w[bi, 0] = 0.24
                # v0.94.282: nakke/hode (102/103) mykere – spillets hode-IK rykker 15–20° på én frame hos avsenderen
                # (måling 2026-11-21: overføringen er nøyaktig, rykket kommer fra avsenderen selv)
                for bi in (102, 103):
                    w[bi, 0] = float(getattr(self, 'head_smooth_w', 0.22))
                self._skel_ema_w = w
            # Glatt rotasjonsrader (floats 8..19 = +0x20..+0x4C) og translasjon (20..22 = +0x50..+0x58)
            blended = prev[:, 8:23] + w * (cur[:, 8:23] - prev[:, 8:23])
            # Re-normaliser de tre 3D rotasjonsradene så skjelettet aldri krymper
            for r0 in (0, 4, 8):
                row = blended[:, r0:r0 + 3]
                nrm = np.sqrt(np.sum(row * row, axis=1, keepdims=True))
                ok = nrm > 1e-4
                blended[:, r0:r0 + 3] = np.where(ok, row / np.where(ok, nrm, 1.0), cur[:, 8 + r0:8 + r0 + 3])
            cur[:, 8:23] = blended
            cache[actor] = cur
            return cur.tobytes()
        except Exception:
            return skel_bytes

    @classmethod
    def apply_interpolated_pose(cls, base_skel, b64_a, b64_b, alpha):
        """Interpolate body and transmitted secondary bone rotations."""
        if not isinstance(base_skel, (bytes, bytearray)) or len(base_skel) != cls.PUPPET_SKEL_BYTES:
            return None
        if not isinstance(b64_b, str) or not b64_b or len(b64_b) > cls.PUPPET_FULL_POSE_LEN:
            return None
        decoded_b = cls._decode_pose(b64_b)
        if decoded_b is None:
            return None
        indices, raw_b = decoded_b
        previous = cls._decode_pose(b64_a) if isinstance(b64_a, str) and len(b64_a) <= cls.PUPPET_FULL_POSE_LEN else None
        raw_a = previous[1] if previous and previous[0] == indices else raw_b
        expected_shorts = len(indices) * 4 + 3
        rust = cls._get_rust_engine() if hasattr(cls, "_get_rust_engine") else None
        if rust is not None:
            idx_arr, _, sa_arr, sb_arr, out_skel = cls._rust_pack_bufs(indices)
            ctypes.memmove(sa_arr, raw_a, len(raw_a))
            ctypes.memmove(sb_arr, raw_b, len(raw_b))
            rc = rust.oot_apply_interp_bones(
                bytes(base_skel), len(base_skel), idx_arr, len(indices),
                sa_arr, sb_arr, expected_shorts, float(alpha), out_skel,
            )
            if rc == 0:
                return out_skel.raw
        va = struct.unpack(f"<{expected_shorts}h", raw_a)
        vb = struct.unpack(f"<{expected_shorts}h", raw_b)
        buf = bytearray(base_skel)
        pos = 0
        t = max(0.0, min(1.0, float(alpha)))
        inv_t = 1.0 - t
        for idx, bi in enumerate(indices):
            ax, ay, az, aw = (va[pos + k] / 32767.0 for k in range(4))
            bx, by, bz, bw = (vb[pos + k] / 32767.0 for k in range(4))
            pos += 4
            if ax * bx + ay * by + az * bz + aw * bw < 0.0:
                bx, by, bz, bw = -bx, -by, -bz, -bw
            qx = ax * inv_t + bx * t
            qy = ay * inv_t + by * t
            qz = az * inv_t + bz * t
            qw = aw * inv_t + bw * t
            n = math.sqrt(qx * qx + qy * qy + qz * qz + qw * qw)
            if n > 1e-8:
                qx, qy, qz, qw = qx / n, qy / n, qz / n, qw / n
            else:
                qx, qy, qz, qw = bx, by, bz, bw
            m = cls._quat_to_rows((qx, qy, qz, qw))
            off = bi * cls.PUPPET_BONE_STRIDE
            struct.pack_into("<I", buf, off + 0x00, 0x00800000)
            struct.pack_into("<4f", buf, off + 0x20, m[0], m[1], m[2], 0.0)
            struct.pack_into("<4f", buf, off + 0x30, m[3], m[4], m[5], 0.0)
            struct.pack_into("<4f", buf, off + 0x40, m[6], m[7], m[8], 0.0)
            if idx == 1:
                tx = (va[pos] * inv_t + vb[pos] * t) / 4096.0
                ty = (va[pos + 1] * inv_t + vb[pos + 1] * t) / 4096.0
                tz = (va[pos + 2] * inv_t + vb[pos + 2] * t) / 4096.0
                pos += 3
                struct.pack_into("<4f", buf, off + 0x50, tx, ty, tz, 0.0)
        return bytes(buf)

    @classmethod
    def _inject_world_physics_into_local(cls, raw_skel, world_raw):
        """v0.94.208: Beregn ekte lokal rotasjon L = Wc @ Wp^T fra WorldMtx (sk+0x20) for både 27 hovedbein og 121 Ph_* fysikkbein."""
        buf = bytearray(raw_skel)
        unpack = struct.unpack_from
        pack = struct.pack_into
        stride = cls.PUPPET_BONE_STRIDE
        for ci, pi in cls.PUPPET_SYNC_PARENTS + cls.PUPPET_PH_PARENTS:
            wc = unpack("<12f", world_raw, ci * 0x40)
            wp = unpack("<12f", world_raw, pi * 0x40)
            # L = Wc @ Wp^T (verifisert 0.00000 feil mot Player_Child LocalMtx)
            c00, c01, c02, _, c10, c11, c12, _, c20, c21, c22, _ = wc
            p00, p01, p02, _, p10, p11, p12, _, p20, p21, p22, _ = wp
            r00 = c00 * p00 + c01 * p01 + c02 * p02
            r01 = c00 * p10 + c01 * p11 + c02 * p12
            r02 = c00 * p20 + c01 * p21 + c02 * p22
            r10 = c10 * p00 + c11 * p01 + c12 * p02
            r11 = c10 * p10 + c11 * p11 + c12 * p12
            r12 = c10 * p20 + c11 * p21 + c12 * p22
            r20 = c20 * p00 + c21 * p01 + c22 * p02
            r21 = c20 * p10 + c21 * p11 + c22 * p12
            r22 = c20 * p20 + c21 * p21 + c22 * p22
            if not math.isfinite(r00 + r11 + r22):
                continue
            off = ci * stride
            pack("<4f", buf, off + 0x20, r00, r01, r02, 0.0)
            pack("<4f", buf, off + 0x30, r10, r11, r12, 0.0)
            pack("<4f", buf, off + 0x40, r20, r21, r22, 0.0)
        return bytes(buf)

    def read_my_packed_pose(self, p):
        """Les det faktiske skjelettet som spillets egen animasjonsmotor har satt på vår egen Player_Child nå."""
        if p is None or self.p_act is None:
            return None
        bh = self.actor_bones_host(p, self.p_act)
        if bh is None:
            return None
        try:
            raw = p.read(p.base + bh, self.PUPPET_SKEL_BYTES)
            if len(raw) != self.PUPPET_SKEL_BYTES:
                return None
            if getattr(self, "_puppet_anim_frames", None) is None:
                built = self.build_puppet_anim_frames(raw)
                if built is not None:
                    self._puppet_anim_frames = built
            wbh = self.__dict__.get("_world_bones_cache", {}).get(self.p_act)
            if wbh is not None:
                wlen = self.PUPPET_BONE_COUNT * 0x40
                wraw = p.read(p.base + wbh, wlen)
                if len(wraw) == wlen:
                    raw = self._inject_world_physics_into_local(raw, wraw)
            return self.pack_skeleton_pose(raw, include_physics=True)
        except OSError:
            return None

    def sync_enemy_slot0_pos(self, p, act, pos):
        """v0.94.217: Skriv fjern-Link sin 3D-posisjon til fiendens mål-slot0+0x20..+0x7F
        KUN når dist_v1 faktisk har satt slot0+0x10 til CoopPuppet sitt hptr (0 hysterese-konflikt, 0 game_call)."""
        if p is None or self.delta is None or act is None or not pos or len(pos) < 3:
            return False
        pup_act = getattr(self, "_active_puppet_act", None)
        if pup_act is None:
            return False
        try:
            pup_hptr = struct.unpack("<Q", p.read(p.base + pup_act + 0x1B0, 8))[0]
            if not pup_hptr:
                return False
        except OSError:
            return False
        cache = self.__dict__.setdefault("_slot0_base_cache", {})
        s0 = cache.get(act)
        if s0 is None:
            try:
                ct = struct.unpack("<Q", p.read(p.base + act + 0x270, 8))[0]
                if not (self.delta < ct < self.delta + p.size - 0x500):
                    return False
                c418 = struct.unpack("<Q", p.read(p.base + ct - self.delta + 0x418, 8))[0]
                if not (self.delta < c418 < self.delta + p.size - 0x100):
                    return False
                s0 = c418 - self.delta + 0x28
                cache[act] = s0
            except (OSError, struct.error):
                return False
        try:
            cur_hptr = struct.unpack("<Q", p.read(p.base + s0 + 0x10, 8))[0]
            if cur_hptr != pup_hptr:
                return False
            x, y, z = float(pos[0]), float(pos[1]), float(pos[2])
            yh = y + 0.7
            p.write(p.base + s0 + 0x20, struct.pack("<24f",
                    x, y, z,  x, y, z,
                    x, yh, z, x, yh, z, x, yh, z, x, yh, z, x, yh, z, x, yh, z))
            return True
        except OSError:
            cache.pop(act, None)
            return False

    def _deku_local_host(self, p, act):
        """Returner host-offset til LocalMtx for Dekubaba (91 bein), eller None."""
        if p is None or self.delta is None or act is None:
            return None
        cache = self.__dict__.setdefault("_deku_local_cache", {})
        cached = cache.get(act)
        if cached is not None:
            return cached
        try:
            ct = struct.unpack("<Q", p.read(p.base + act + 0x270, 8))[0]
            if not (self.delta < ct < self.delta + p.size - 0x20):
                return None
            c8 = struct.unpack("<Q", p.read(p.base + ct - self.delta + 0x08, 8))[0]
            mu = struct.unpack("<Q", p.read(p.base + c8 - self.delta + 0x18, 8))[0]
            mh = struct.unpack("<Q", p.read(p.base + mu - self.delta + 0x18, 8))[0]
            sk = struct.unpack("<Q", p.read(p.base + mh - self.delta + 0x140, 8))[0]
            sk_h = sk - self.delta
            cnt = struct.unpack("<H", p.read(p.base + sk_h + 0x48, 2))[0]
            if cnt < 3 or cnt > 256:
                return None
            lh = struct.unpack("<Q", p.read(p.base + sk_h + 0x18, 8))[0] - self.delta
            if lh <= 0 or lh >= p.size - cnt * 0x60:
                return None
            cache[act] = lh
            return lh
        except (OSError, struct.error):
            return None

    def read_deku_aim(self, p, act):
        """Les Dekubaba svingledd (bone 2) yaw i radianer fra LocalMtx."""
        lh = self._deku_local_host(p, act)
        if lh is None:
            return None
        try:
            lm = struct.unpack("<12f", p.read(p.base + lh + 2 * 0x60 + 0x20, 48))
            return math.atan2(lm[2], lm[10])
        except (OSError, struct.error):
            return None

    def write_deku_aim(self, p, act, yaw):
        """Skriv Dekubaba svingledd (bone 2) Y-rotasjon direkte til LocalMtx (0 game_call)."""
        lh = self._deku_local_host(p, act)
        if lh is None:
            return False
        try:
            s, c = math.sin(yaw), math.cos(yaw)
            b48 = struct.pack("<12f", c, 0.0, s, 0.0, 0.0, 1.0, 0.0, 0.0, -s, 0.0, c, 0.0)
            p.write(p.base + lh + 2 * 0x60 + 0x20, b48)
            return True
        except OSError:
            return False

    PUPPET_BLINK_SLOTS = (
        (0, 0x118), (1, 0x128), (2, 0x128), (3, 0x118), (4, 0x118), (5, 0x100),
        (6, 0x128), (7, 0x108), (8, 0x118), (9, 0x118), (10, 0x118), (11, 0x118),
        (12, 0x130), (13, 0x130), (14, 0x110), (15, 0x120), (16, 0x120), (17, 0x130),
        (18, 0x118), (19, 0x118), (20, 0x118), (21, 0x120), (22, 0x130), (23, 0x118),
    )

    F_COPY8 = 0x3C46F80   # copy_v1.pchtxt: copy8(x0=dst, x1=src, x2=len) – kopierer via spillets CPU (Lichii ser skrivingen)

    def guest_va_of(self, p, host_off):
        """v0.94.261: gjestens VA for en vert-offset. Forskyvningen er ikke lik overalt (heap vs. andre områder
        er forskjøvet med n*0x80000000) – prøv kandidater og la spillet lese tilbake med F_LD8."""
        try:
            want = struct.unpack('<Q', p.read(p.base + host_off, 8))[0]
        except OSError:
            return None
        for k in (0, -1, 1, -2, 2, -3, 3, -4, 4):
            va = host_off + self.delta + k * 0x80000000
            got = self.game_call(p, self.F_LD8, (va - 8,), timeout=1.0)
            if got is not None and (got & 0xFFFFFFFFFFFFFFFF) == want:
                return va
        return None

    def host_of_va(self, p, va):
        """Motsatt: vert-offset for en gjeste-VA (spillet skriver et merke, vi leter blant kandidatene)."""
        mark = 0x5A5A0000 | (int(time.time()) & 0xFFFF)
        if self.game_call(p, self.F_ST32, (va, mark)) is None:
            return None
        for k in (0, -1, 1, -2, 2, -3, 3, -4, 4):
            h = va - self.delta - k * 0x80000000
            try:
                if 0 <= h < p.size and struct.unpack('<I', p.read(p.base + h, 4))[0] == mark:
                    return h
            except OSError:
                pass
        return None

    def paint_own_tunic(self, p, color):
        """v0.94.261: egen Link bytter farge med en gang: nye texler kopieres av spillet (copy8, copy_v1.pchtxt)
        inn i teksturen egen Link tegnes med, så emulatoren laster den på nytt. Dukkenes kopier røres ikke."""
        try:
            col = color.lower()
            tex = open(os.path.join(TUNIC_DIR, 'self', col, 'tile.texels'), 'rb').read()
            if self.hR is None or self.delta is None:
                return 'spillet ikke klart'
            dst = getattr(self, '_own_tex_va', None)
            if dst is None:
                sigs = {}
                for c in (look.lower() for look in LOOKS):
                    try:
                        sigs[c] = open(os.path.join(TUNIC_DIR, 'self', c, 'tile.texels'), 'rb').read()[4096:4096 + 64]
                    except OSError:
                        pass
                hits = []   # (vert-offset, har BNTX-hode)
                CH = 32 << 20
                for i0 in range(0, p.size, CH):
                    try:
                        blk = p.read(p.base + i0, CH)
                    except OSError:
                        continue
                    for sg in sigs.values():
                        j0 = blk.find(sg)
                        while j0 >= 0:
                            a = i0 + j0 - 4096
                            try:
                                hdr = p.read(p.base + a - 0x1000, 4) == b'BNTX'
                            except OSError:
                                hdr = False
                            hits.append((a, hdr)); j0 = blk.find(sg, j0 + 1)
                bare = [a for a, h in hits if not h]
                alone = [a for a in bare if all(abs(a - b) > 0x1000000 for b in bare if b != a)]   # dukkenes kopier ligger samlet
                if len(alone) != 1:
                    log(f'tunika: maling – uklart hvilken tekstur er egen ({[hex(a) for a in bare]})')
                    return 'fant ikke egen tunika-tekstur entydig'
                dst = self.guest_va_of(p, alone[0])
                if dst is None:
                    return 'fant ikke gjeste-adressen'
                self._own_tex_va = dst
            buf = getattr(self, '_paint_buf', None)
            if buf is None:
                va = self.game_call(p, self.F_ALLOC, (0x10, len(tex) + 0x100), timeout=3.0)
                hb = self.host_of_va(p, va) if va else None
                if hb is None:
                    return 'fant ikke minnebufferen'
                buf = self._paint_buf = (va, hb)
            p.write(p.base + buf[1], tex)
            r = self.game_call(p, self.F_COPY8, (dst, buf[0], len(tex)), timeout=5.0)
            log(f'tunika: malte egen Link {color} ({len(tex)} byte -> 0x{dst:X}) -> {r}')
            return f'malt {color} -> {r}'
        except Exception as e:  # noqa: BLE001
            return f'feil {e!r}'

    def blink_set_target(self, p, act, low):
        """v0.94.259: registrer dukke for lav-HP-puls; en bakgrunnstråd skriver verdien ~120 ganger i sekundet."""
        tg = self.__dict__.setdefault('_blink_targets', {})
        if low:
            tg[act] = True
        elif tg.pop(act, None) is not None:
            self.set_puppet_low_hp_blink(p, act, 0.0)
        self._blink_p = p
        if tg and not getattr(self, '_blink_thr', None):
            def _loop():
                while True:
                    tgs = dict(self.__dict__.get('_blink_targets', {}))
                    if not tgs:
                        time.sleep(0.2); continue
                    v = puppet_low_hp_pulse(time.time())
                    for a_ in tgs:
                        try:
                            if not self.set_puppet_low_hp_blink(self._blink_p, a_, v):
                                self._blink_targets.pop(a_, None)
                        except Exception:  # noqa: BLE001
                            self._blink_targets.pop(a_, None)
                    time.sleep(1 / 120)
            self._blink_thr = threading.Thread(target=_loop, daemon=True); self._blink_thr.start()

    def set_puppet_low_hp_blink(self, p, act, val):
        """Gjengi native lav-HP-effekt i samtlige parameterbuffere (0 game_call).

        Dirty-bit 0 settes bare hvis det mangler. Å slå det av og på igjen hvert
        bilde flimrer i 60 Hz uansett hvor rolig sinuskurven er.
        """
        if p is None or self.delta is None or self.main is None or act is None:
            return False
        act_vt = (self.main + self.ACT_VT) & 0xFFFFFFFFFFFFFFFF
        try:
            hdr = p.read(p.base + act, 0x30)
            if len(hdr) != 0x30 or struct.unpack_from("<Q", hdr, 0)[0] != act_vt or struct.unpack_from("<I", hdr, 0x2C)[0] != 4:
                return False
            cache = self.__dict__.setdefault("_pup_blink_addrs", {})
            groups = cache.get(act)
            if groups is None:
                d = self.delta
                u64 = lambda h: struct.unpack("<Q", p.read(p.base + h, 8))[0]
                ct = u64(act + 0x270)
                if not (d < ct < d + p.size - 0x20):
                    return False
                c8 = u64(ct - d + 0x08)
                if not (d < c8 < d + p.size - 0x20):
                    return False
                mu = u64(c8 - d + 0x18)
                if not (d < mu < d + p.size - 0x20):
                    return False
                mh = u64(mu - d + 0x18)
                if not (d < mh < d + p.size - 0x160):
                    return False
                m_arr = u64(mh - d + 0x150)
                if not (d < m_arr < d + p.size - 24 * 0x80):
                    return False
                groups = []
                for mat_idx, u_off in self.PUPPET_BLINK_SLOTS:
                    mat_base = (m_arr - d) + mat_idx * 0x80
                    ptrs = {f: u64(mat_base + f) for f in (0x40, 0x48, 0x50, 0x58, 0x70)}
                    if not all(d < ptr < d + p.size - 0x140 for ptr in ptrs.values()):
                        continue
                    # Read-only sampling av native Player_Child viste at samme puls
                    # speiles til disse feltene. Bare +0x40 ga ingen synlig dukkeeffekt.
                    addrs = [ptrs[0x40] - d + u_off,
                             ptrs[0x48] - d + 0x28,
                             ptrs[0x58] - d + u_off - 0x30,
                             ptrs[0x70] - d + 0x68]
                    # Kun materialene med denne ekstra parameterblokken har +0x50
                    # nøyaktig 0x20 bytes før hovedbufferen. Ikke gjet på de øvrige.
                    if ptrs[0x50] == ptrs[0x40] - 0x20:
                        addrs.append(ptrs[0x50] - d + u_off + 0x20)
                    groups.append((tuple(addrs), mat_base + 0x2C))
                cache[act] = tuple(groups)
            if not groups:
                return False
            b4 = struct.pack("<f", float(val))
            _lt = self.__dict__.setdefault('_blink_log_t', {})
            if time.time() - _lt.get(act, 0) > 2.0:   # v0.94.263: diagnostikk (blink bare på blå dukke)
                _lt[act] = time.time()
                try:
                    _nv = struct.unpack('<Q', p.read(p.base + act + 0x260, 8))[0]
                    _nm = p.read(p.base + _nv - self.delta, 40).split(bytes(1), 1)[0].decode('ascii', 'replace')
                except Exception:  # noqa: BLE001
                    _nm = '?'
                log(f'blink: {_nm} @0x{act:X} grupper={len(groups)} verdi={float(val):.2f} mål={len(self.__dict__.get("_blink_targets", {}))}')
            _only40 = getattr(self, 'blink_mode', 'all') == '40'   # v0.94.264: test – bare hovedbufferen (+0x40) som spillet selv
            for addrs, flag_addr in groups:
                for val_addr in (addrs[:1] if _only40 else addrs):
                    p.write(p.base + val_addr, b4)
                cur_f = struct.unpack("<I", p.read(p.base + flag_addr, 4))[0]
                want_f = cur_f | 0x0101
                if want_f != cur_f:
                    p.write(p.base + flag_addr, struct.pack("<I", want_f))
            return True
        except (OSError, struct.error):
            return False

    def actor_skel_info(self, p, act):
        """v0.94.228: Returner (bones_h, bone_count) for vilkårlig aktør (f.eks. Gohma 151 bein), eller None."""
        if p is None or self.delta is None or act is None:
            return None
        cache = self.__dict__.setdefault("_gen_skel_cache", {})
        cached = cache.get(act)
        if cached is not None:
            return cached
        try:
            ct = struct.unpack("<Q", p.read(p.base + act + 0x270, 8))[0]
            if not (self.delta < ct < self.delta + p.size - 0x20):
                return None
            c8 = struct.unpack("<Q", p.read(p.base + ct - self.delta + 0x08, 8))[0]
            if not (self.delta < c8 < self.delta + p.size - 0x20):
                return None
            mu = struct.unpack("<Q", p.read(p.base + c8 - self.delta + 0x18, 8))[0]
            if not (self.delta < mu < self.delta + p.size - 0x20):
                return None
            mh = struct.unpack("<Q", p.read(p.base + mu - self.delta + 0x18, 8))[0]
            if not (self.delta < mh < self.delta + p.size - 0x160):
                return None
            sk = struct.unpack("<Q", p.read(p.base + mh - self.delta + 0x140, 8))[0]
            if not (self.delta < sk < self.delta + p.size - 0x60):
                return None
            sk_h = sk - self.delta
            cnt = struct.unpack("<H", p.read(p.base + sk_h + 0x48, 2))[0]
            if not (1 <= cnt <= 512):
                return None
            bones_va = struct.unpack("<Q", p.read(p.base + sk_h + 0x18, 8))[0]
            if not (self.delta < bones_va < self.delta + p.size - cnt * 0x60):
                return None
            res = (bones_va - self.delta, cnt)
            cache[act] = res
            return res
        except (OSError, struct.error):
            return None

    @classmethod
    def pack_generic_skeleton(cls, raw_skel, cnt):
        """v0.94.230: Pakk alle `cnt` bein i LocalMtx til base64 med 16-bits kvaternioner (3*int16, 256x høyere presisjon enn int8) + 3*int16 trans for 0..15."""
        if not isinstance(raw_skel, (bytes, bytearray)) or len(raw_skel) != cnt * 0x60:
            return None
        try:
            import base64
            arr = np.frombuffer(raw_skel, dtype=np.float32).reshape(cnt, 24)
            m00, m01, m02 = arr[:, 8], arr[:, 9], arr[:, 10]
            m10, m11, m12 = arr[:, 12], arr[:, 13], arr[:, 14]
            m20, m21, m22 = arr[:, 16], arr[:, 17], arr[:, 18]
            qx = np.empty(cnt, dtype=np.float32)
            qy = np.empty(cnt, dtype=np.float32)
            qz = np.empty(cnt, dtype=np.float32)
            for i in range(cnt):
                q = cls._rows_to_quat((
                    float(m00[i]), float(m01[i]), float(m02[i]),
                    float(m10[i]), float(m11[i]), float(m12[i]),
                    float(m20[i]), float(m21[i]), float(m22[i]),
                ))
                if q[3] < 0.0:
                    qx[i], qy[i], qz[i] = -q[0], -q[1], -q[2]
                else:
                    qx[i], qy[i], qz[i] = q[0], q[1], q[2]
            q3 = np.stack((qx, qy, qz), axis=1)
            q_i16 = np.clip(np.rint(q3 * 32767.0), -32767, 32767).astype(np.int16)
            t_cnt = min(cnt, 16)
            t_i16 = np.clip(np.rint(arr[:t_cnt, 20:23] * 2048.0), -32767, 32767).astype(np.int16)
            return base64.b64encode(q_i16.tobytes() + t_i16.tobytes()).decode("ascii")
        except Exception:
            return None

    @classmethod
    def apply_generic_skeleton(cls, base_skel, cnt, b64_pose):
        """v0.94.230: Pakk ut 16-bits base64-skjelett inn i `base_skel` (vektorisert numpy, <0,2 ms)."""
        if not isinstance(base_skel, (bytes, bytearray)) or len(base_skel) != cnt * 0x60 or not isinstance(b64_pose, str):
            return None
        try:
            import base64
            raw = base64.b64decode(b64_pose)
            t_cnt = min(cnt, 16)
            q_bytes = cnt * 6
            if len(raw) != q_bytes + t_cnt * 6:
                return None
            q3 = np.frombuffer(raw[:q_bytes], dtype=np.int16).astype(np.float32).reshape(cnt, 3) / 32767.0
            x, y, z = q3[:, 0], q3[:, 1], q3[:, 2]
            w = np.sqrt(np.maximum(0.0, 1.0 - (x * x + y * y + z * z)))
            xx, yy, zz = x * x, y * y, z * z
            xy, xz, yz = x * y, x * z, y * z
            wx, wy, wz = w * x, w * y, w * z
            out = np.frombuffer(base_skel, dtype=np.float32).reshape(cnt, 24).copy()
            out[:, 8] = 1.0 - 2.0 * (yy + zz)
            out[:, 9] = 2.0 * (xy - wz)
            out[:, 10] = 2.0 * (xz + wy)
            out[:, 12] = 2.0 * (xy + wz)
            out[:, 13] = 1.0 - 2.0 * (xx + zz)
            out[:, 14] = 2.0 * (yz - wx)
            out[:, 16] = 2.0 * (xz - wy)
            out[:, 17] = 2.0 * (yz + wx)
            out[:, 18] = 1.0 - 2.0 * (xx + yy)
            trans = np.frombuffer(raw[q_bytes:], dtype=np.int16).astype(np.float32).reshape(t_cnt, 3) / 2048.0
            out[:t_cnt, 20:23] = trans
            return out.tobytes()
        except Exception:
            return None

    def smooth_generic_skeleton(self, actor, skel_bytes, cnt, w=0.45):
        """v0.94.228: 60 Hz numpy-glatting for vilkårlig skjelettstørrelse (f.eks. Gohma 151 bein)."""
        if not isinstance(skel_bytes, (bytes, bytearray)) or len(skel_bytes) != cnt * 0x60:
            return skel_bytes
        try:
            cur = np.frombuffer(skel_bytes, dtype=np.float32).reshape(cnt, 24).copy()
            cache = self.__dict__.setdefault("_gen_skel_ema", {})
            prev = cache.get(actor)
            if prev is None or prev.shape != cur.shape:
                cache[actor] = cur
                return skel_bytes
            blended = prev[:, 8:23] + float(w) * (cur[:, 8:23] - prev[:, 8:23])
            for r0 in (0, 4, 8):
                row = blended[:, r0:r0 + 3]
                nrm = np.sqrt(np.sum(row * row, axis=1, keepdims=True))
                ok = nrm > 1e-4
                blended[:, r0:r0 + 3] = np.where(ok, row / np.where(ok, nrm, 1.0), cur[:, 8 + r0:8 + r0 + 3])
            cur[:, 8:23] = blended
            cache[actor] = cur
            return cur.tobytes()
        except Exception:
            return skel_bytes

    def actor_bones_host(self, p, act):
        """Returner host-offset til aktørens nn::g3d LocalMtx-tabell (309 * 0x60 = 29664 B), eller None."""
        if p is None or self.delta is None or act is None:
            return None
        cache = self.__dict__.setdefault("_bones_cache", {})
        cached = cache.get(act)
        if cached is not None:
            return cached
        try:
            ct = struct.unpack("<Q", p.read(p.base + act + 0x270, 8))[0]
            if not (self.delta < ct < self.delta + p.size - 0x20):
                return None
            c8 = struct.unpack("<Q", p.read(p.base + ct - self.delta + 0x08, 8))[0]
            if not (self.delta < c8 < self.delta + p.size - 0x20):
                return None
            mu = struct.unpack("<Q", p.read(p.base + c8 - self.delta + 0x18, 8))[0]
            if not (self.delta < mu < self.delta + p.size - 0x20):
                return None
            mh = struct.unpack("<Q", p.read(p.base + mu - self.delta + 0x18, 8))[0]
            if not (self.delta < mh < self.delta + p.size - 0x160):
                return None
            sk = struct.unpack("<Q", p.read(p.base + mh - self.delta + 0x140, 8))[0]
            if not (self.delta < sk < self.delta + p.size - 0x60):
                return None
            sk_h = sk - self.delta
            cnt = struct.unpack("<H", p.read(p.base + sk_h + 0x48, 2))[0]
            if cnt != self.PUPPET_BONE_COUNT:
                return None
            bones_va = struct.unpack("<Q", p.read(p.base + sk_h + 0x18, 8))[0]
            if not (self.delta < bones_va < self.delta + p.size - self.PUPPET_SKEL_BYTES):
                return None
            bones_h = bones_va - self.delta
            cache[act] = bones_h
            world_va = struct.unpack("<Q", p.read(p.base + sk_h + 0x20, 8))[0]
            if self.delta < world_va < self.delta + p.size - self.PUPPET_BONE_COUNT * 0x40:
                self.__dict__.setdefault("_world_bones_cache", {})[act] = world_va - self.delta
            return bones_h
        except (OSError, struct.error):
            return None

    @staticmethod
    def _rot3_xyz(rx, ry, rz):
        cx, sx = math.cos(rx), math.sin(rx)
        cy, sy = math.cos(ry), math.sin(ry)
        cz, sz = math.cos(rz), math.sin(rz)
        return (
            (cy * cz, -cy * sz, sy),
            (sx * sy * cz + cx * sz, -sx * sy * sz + cx * cz, -sx * cy),
            (-cx * sy * cz + sx * sz, cx * sy * sz + sx * cz, cx * cy),
        )

    @staticmethod
    def _mul3(a, b):
        return tuple(
            tuple(sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3))
            for i in range(3)
        )

    @classmethod
    def _apply_bone_rot(cls, buf, bone_idx, rx=0.0, ry=0.0, rz=0.0, dy=0.0):
        off = bone_idx * cls.PUPPET_BONE_STRIDE
        r0 = struct.unpack_from("<3f", buf, off + 0x20)
        r1 = struct.unpack_from("<3f", buf, off + 0x30)
        r2 = struct.unpack_from("<3f", buf, off + 0x40)
        m = cls._mul3((r0, r1, r2), cls._rot3_xyz(rx, ry, rz))
        struct.pack_into("<I", buf, off + 0x00, 0x00800000)
        struct.pack_into("<4f", buf, off + 0x20, m[0][0], m[0][1], m[0][2], 0.0)
        struct.pack_into("<4f", buf, off + 0x30, m[1][0], m[1][1], m[1][2], 0.0)
        struct.pack_into("<4f", buf, off + 0x40, m[2][0], m[2][1], m[2][2], 0.0)
        if dy:
            tx, ty, tz, tw = struct.unpack_from("<4f", buf, off + 0x50)
            struct.pack_into("<4f", buf, off + 0x50, tx, ty + dy, tz, tw)

    @classmethod
    def build_puppet_anim_frames(cls, base_skel):
        """Bygg (wait_frame, run_frames[16], attack_frames[8]) fra Player_Child sitt hvile-skjelett (29664 B)."""
        if not isinstance(base_skel, (bytes, bytearray)) or len(base_skel) != cls.PUPPET_SKEL_BYTES:
            return None
        wait_frame = bytes(base_skel)
        run_frames = []
        for idx in range(16):
            ph = (idx / 16.0) * 2.0 * math.pi
            s = math.sin(ph)
            b = bytearray(wait_frame)
            cls._apply_bone_rot(b, 3, dy=0.025 * abs(math.cos(ph)))
            cls._apply_bone_rot(b, 4, rx=0.08, ry=0.10 * s)
            cls._apply_bone_rot(b, 11, rx=0.06, ry=0.08 * s)
            cls._apply_bone_rot(b, 231, rz=0.65 * s)
            cls._apply_bone_rot(b, 232, rz=-0.75 * max(0.0, -s) - 0.15)
            cls._apply_bone_rot(b, 233, rz=0.25 * s)
            cls._apply_bone_rot(b, 242, rz=-0.65 * s)
            cls._apply_bone_rot(b, 243, rz=-0.75 * max(0.0, s) - 0.15)
            cls._apply_bone_rot(b, 244, rz=-0.25 * s)
            cls._apply_bone_rot(b, 13, ry=-0.45 * s)
            cls._apply_bone_rot(b, 14, ry=-0.30 * max(0.0, s))
            cls._apply_bone_rot(b, 58, ry=0.45 * s)
            cls._apply_bone_rot(b, 59, ry=0.30 * max(0.0, -s))
            run_frames.append(bytes(b))
        attack_frames = []
        for idx in range(8):
            t = idx / 7.0
            sw = math.sin(t * math.pi)
            slash = (t - 0.35) * 2.2
            b = bytearray(wait_frame)
            cls._apply_bone_rot(b, 4, ry=-0.35 * slash)
            cls._apply_bone_rot(b, 11, ry=-0.35 * slash, rx=0.15 * sw)
            cls._apply_bone_rot(b, 57, ry=-0.30 * slash)
            cls._apply_bone_rot(b, 58, ry=-0.85 * slash, rz=0.45 * sw)
            cls._apply_bone_rot(b, 59, ry=-0.45 * (1.0 - sw))
            cls._apply_bone_rot(b, 64, rx=0.50 * slash)
            cls._apply_bone_rot(b, 231, rz=0.25 * sw)
            cls._apply_bone_rot(b, 242, rz=-0.25 * sw)
            attack_frames.append(bytes(b))
        return wait_frame, tuple(run_frames), tuple(attack_frames)

    def ensure_puppet_anim_frames(self, p):
        """Les hvile-skjelettet fra Player_Child én gang (når Link står i ro) og forhåndsberegn Wait/Run/Attack."""
        frames = getattr(self, "_puppet_anim_frames", None)
        if frames is not None and getattr(self, "_puppet_anim_captured_idle", False):
            return frames
        if p is None or self.p_act is None:
            return frames
        bh = self.actor_bones_host(p, self.p_act)
        if bh is None:
            return frames
        try:
            an, _ = self.read_anim(p, self.p_act)
        except Exception:  # noqa: BLE001
            an = None
        is_idle = bool(an and "wait" in an.lower() and "evtwait" not in an.lower())
        if frames is not None and not is_idle:
            return frames
        try:
            raw = p.read(p.base + bh, self.PUPPET_SKEL_BYTES)
            if len(raw) != self.PUPPET_SKEL_BYTES:
                return frames
            # Sjekk at Skl_Root (bone 3) har gyldig rotasjon og translasjon
            vals = struct.unpack_from("<12f", raw, 3 * self.PUPPET_BONE_STRIDE + 0x20)
            if not all(math.isfinite(v) for v in vals) or abs(vals[0]) + abs(vals[1]) + abs(vals[2]) < 0.1:
                return frames
            built = self.build_puppet_anim_frames(raw)
            if built is not None:
                self._puppet_anim_frames = built
                self._puppet_anim_captured_idle = is_idle
                return built
        except (OSError, struct.error):
            pass
        return frames

    AIHOLD_MAX = 29               # R+0x600: 0x10 hode + 29*8, R+0x6F8 = patchens teller (R+0x700 er CALL-postkassen)
    def set_ai_hold(self, p, comps, mode=1):
        """Skriv AI-pause-tabellen: BSA-komponentene i `comps` får hjernen hoppet over (bit 0 satt). Tom liste = ingen pause.
        Returnerer False hvis patchen ikke er lastet."""
        if self.hR is None:
            return False
        try:
            comps = list(comps)[:self.AIHOLD_MAX]
            ht = p.base + self.hR + self.AIHOLD_TABLE_R
            a_, o_ = (0xFFFFFFFF, 1) if mode == 1 else (0xFFFFFFFE, 0)
            p.write(ht + 0x10, b''.join(struct.pack('<Q', c) for c in comps))
            p.write(ht, struct.pack('<III', len(comps), a_, o_))
            return True
        except OSError:
            return False

    def bsa_comp(self, p, a):
        """Gjeste-VA til fiendens «hjerne»-komponent (BSA) = [[akt+0x270]+0xB0], eller None."""
        try:
            ct = struct.unpack('<Q', p.read(p.base + a + 0x270, 8))[0]
            v = struct.unpack('<Q', p.read(p.base + ct - self.delta + 0xB0, 8))[0]
            return v or None
        except OSError:
            return None

    F_ACT_FORCE_SET_MTX = 0x4C6580   # aktørens vtable-slot 0x218: tar ny +0x31C..+0x34B inn i fysikkroppen (teleport-sti)

    def move_actor_real(self, p, a, pos, rot=None):
        """Flytt en aktør slik at det holder: skriv posisjon (+0x31C) og evt. rotasjon (+0x328), og kall spillets egen setter.
        Bare levende (riktig vtable) og våkne aktører (tilstand +0x2C == 4) – ellers kan kallet henge spillet."""
        try:
            if not self.actor_alive(p, a) or struct.unpack('<I', p.read(p.base + a + 0x2C, 4))[0] != 4:
                return None
        except OSError:
            return None
        try:
            p.write(p.base + a + 0x31C, struct.pack('<3f', *pos))
            if rot and len(rot) == 9:
                p.write(p.base + a + 0x328, struct.pack('<9f', *rot))
        except OSError:
            return None
        return self.game_call(p, self.F_ACT_FORCE_SET_MTX, (a + self.delta, 0), timeout=1.0)
    START_POS = {"KokiriForest_Child": "LostWoodBridge_FrontOfHyruleField",       # kjente navngitte startpunkt (ankomst) per sone
                 "HyruleField_Child": "HyruleField_FrontOfLostWoodBridge"}

    GOT_GDM = 0x4C7E180   # GameDataMgr-peker; STR64-tabell på gdm+0x618 (post 0x108 byte, tekst på +0x74)

    def save_tables(self, p):
        """Finn GameDataMgr-tabellene én gang. True når enum-tabellen er kjent."""
        if self.hR is None or self.main is None or p is None:
            return False
        if getattr(self, 'h_enum', None) is not None and getattr(self, 'h_str64', None) is not None:
            return True
        if time.time() - getattr(self, '_gdm_scan_t', 0) < 5.0:
            return False
        self._gdm_scan_t = time.time()
        try:
            u64 = lambda o: struct.unpack('<Q', p.read(p.base + o, 8))[0]
            gdm_va = u64(self.hR + (u64(self.hR + (self.main + self.GOT_GDM - self.R)) - self.R))
            ok = lambda o: u64(o + 0x248) == self.main + 0x4C1F500 and u64(o + 0x630) == 0x60
            h_gdm = self._find_host_ptr(p, gdm_va, ok)
            if h_gdm is None:
                return False
            shift = gdm_va - h_gdm
            self.h_str64 = u64(h_gdm + 0x618) - shift
            self.h_s32 = u64(h_gdm + 0xD8) - shift
            self.h_bools = u64(h_gdm + 0x18) - shift
            self.n_bools = struct.unpack('<I', p.read(p.base + h_gdm + 0x10, 4))[0]
            self.h_enum = u64(h_gdm + 0x258) - shift
            return True
        except OSError:
            self.h_str64 = None
            return False

    def read_door(self, p):
        """Under en ekte sonedør (ca. 10 s) står målsone i STR64[34] og navngitt startpunkt i STR64[33]. Gir (banc, start) eller None."""
        if self.hR is None or self.main is None:
            return None
        try:
            if not self.save_tables(p):
                return None
            nul = bytes(1)
            rd = lambda i: p.read(p.base + self.h_str64 + i * 0x108 + 0x74, 64).split(nul, 1)[0]
            start, banc = rd(33), rd(34)
            if not start or not banc:
                return None
            start, banc = start.decode('ascii'), banc.decode('ascii')
            if '_' in banc and banc.replace('_', '').isalnum() and start.replace('_', '').isalnum():
                return banc, start
        except (OSError, UnicodeDecodeError):
            self.h_str64 = None
        return None

    def read_last_start(self, p):
        """Siste startpunkt-navn (STR64[33]) selv utenfor en dør – reserve når sonen ikke har lært startpunkt."""
        if self.read_door(p) is None and getattr(self, 'h_str64', None) is None:
            return None
        try:
            v = p.read(p.base + self.h_str64 + 33 * 0x108 + 0x74, 64).split(bytes(1), 1)[0].decode('ascii')
            return v if v and v.replace('_', '').isalnum() else None
        except (OSError, UnicodeDecodeError, TypeError):
            return None

    def read_bools(self, p):
        """Alle verdens-flagg (GameDataMgr bool-tabell) som bytes 0/1, eller None."""
        if getattr(self, 'h_bools', None) is None:
            self.read_door(p)
        if getattr(self, 'h_bools', None) is None or not getattr(self, 'n_bools', 0):
            return None
        try:
            raw = p.read(p.base + self.h_bools, self.n_bools * 0x18)
        except OSError:
            self.h_str64 = self.h_bools = None
            return None
        return raw[0x16::0x18]

    def set_bool(self, p, i):
        if getattr(self, 'h_bools', None) is None or not (0 <= i < self.n_bools):
            return False
        try:
            p.write(p.base + self.h_bools + i * 0x18 + 0x16, bytes((1, 1)))
            return True
        except OSError:
            return False

    BOSS_FLAGS = (8594, 8595, 10771, 11111, 11139, 10848, 10856, 10833, 11136)   # 8595 = InsideTheDekuTree_BossArea_ShutIn, 8594 = _ChangeENVForBoss (Murmur3-navn)   # settes når bosskampen starter (dør låst o.l.) – synkes ikke, kan nullstilles med /resetboss

    def clear_bool(self, p, i):
        if getattr(self, 'h_bools', None) is None or not (0 <= i < self.n_bools):
            return False
        try:
            p.write(p.base + self.h_bools + i * 0x18 + 0x16, bytes((0, 0)))
            return True
        except OSError:
            return False

    # v0.94.268: tilfeldige drops (navn fra daurosk docs/objects.md «Drops»). Spores som borte-hos-én = borte-hos-begge,
    # og slettes når de dukker opp der vår kopi ble drept fordi vennen drepte fienden (ellers dobbel loot).
    DROP_NAMES = frozenset(('Obj_Rupee_Green', 'Obj_Rupee_Blue', 'Obj_Rupee_Red', 'Obj_Rupee_Purple', 'Obj_Rupee_Silver',
                            'Obj_Rupee_Gold', 'Obj_Heart', 'Obj_MagicJar_Small', 'Obj_MagicJar_Large', 'Obj_ArrowBundle_Small',
                            'Obj_ArrowBundle_Medium', 'Obj_ArrowBundle_Large', 'Obj_Bomb', 'Obj_Bombchu', 'Obj_DekuNut',
                            'Obj_DekuSeed', 'Obj_Arrow_Fire', 'Obj_Fairy'))
    SYNC_PREFIX = ('Enemy_', 'Obj_Pot', 'Obj_Rock', 'Obj_Stone', 'Obj_Boulder', 'Obj_Bush', 'Obj_Grass', 'Obj_Kusa', 'Obj_Barrel', 'Obj_Crate', 'Obj_WoodBox', 'Obj_Deku_MoveFloor', 'Obj_MoveFloor', 'Obj_Lift', 'Obj_MovableBox', 'Obj_PushBlock', 'Obj_SpiderWeb', 'Obj_Deku_SpiderWeb', 'Obj_Web', 'Obj_Cobweb', 'Obj_Kumo', 'Obj_Deku_Web', 'Obj_InsideTheDekuTree_SpiderWeb', 'Obj_InsideTheDekuTree_InteractiveSpiderWeb', 'Obj_InsideTheDekuTree_FallingLadder', 'Obj_InsideTheDekuTree_FallingFloor', 'Obj_InsideTheDekuTree_Stopper', 'Obj_InsideTheDekuTree_WaterGate')

    ACT_MGR_PTR = 0x4E91888        # daurosk/oot-remake-multiplayer (GPLv3, docs/objects.md): [[main+0x4E91888]+0x118]+0x670 = aktørliste

    def scan_actors(self, p):
        t0 = time.perf_counter()
        try:
            if getattr(self, 'use_actor_list', True) and getattr(self, '_list_fail', 0) < 20:
                r = self._list_actors_raw(p)
                if r is not None:
                    self._list_fail = 0
                    # Lista mangler noen aktører (f.eks. *_DekuStickDrop, Gohma-larver). Minnesøk hvert 30. s finner dem;
                    # de som fortsatt lever tas med hver gang (ellers tror modden de er borte og lager dem på nytt -> heng).
                    now_ = time.time()
                    if now_ - getattr(self, '_list_old_t', 0) > 120 or getattr(self, '_list_old_banc', None) != self.cur_banc:
                        self._list_old_t = now_; self._list_old_banc = self.cur_banc
                        self._scan_full_t = 0
                        old = self._scan_actors_raw(p) or {}
                        self._list_extra = {a: v[0] for a, v in old.items() if a not in r}
                        if now_ - getattr(self, '_list_log_t', 0) > 300:
                            self._list_log_t = now_
                            log(f"aktørliste: {getattr(self, '_list_len', '?')} i lista, {len(r)} synk-aktører derfra, {len(old)} fra minnesøk, "
                                f"{len(self._list_extra)} bare i minnesøket: {sorted(set(self._list_extra.values()))[:8]}")
                    for a, nm in list(getattr(self, '_list_extra', {}).items()):
                        if a in r:
                            continue
                        if not self.actor_alive(p, a):
                            self._list_extra.pop(a, None); continue
                        try:
                            pos = p.f32(a + 0x31C, 3)
                            if all(math.isfinite(v) for v in pos):
                                r[a] = (nm, tuple(pos))
                        except OSError:
                            pass
                    return r
                self._list_fail = getattr(self, '_list_fail', 0) + 1
                if self._list_fail == 20:
                    log(f"aktørliste: virker ikke her – bruker minnesøk ({getattr(self, '_list_why', '?')})")
            r = self._scan_actors_raw(p)
            if r:
                self._last_old_scan = r
            return r
        finally:
            perf_add('fiendesøk', time.perf_counter() - t0)

    def _find_list_head(self, p):
        """Finn listehodet ved å gå fra vår egen Link (node på akt+0x538, eier +0x10) til noden som ikke er en aktør:
        hodet har antallet (u32 < 5000) der eier-feltet ellers står. (daurosk: hode = [[main+0x4E91888]+0x118]+0x670.)"""
        if self.p_act is None:
            self._list_why = "ingen Link ennå"
            return 0
        d = self.delta
        whys = []
        for a0 in [self.p_act] + list(getattr(self, '_last_old_scan', {}) or {})[:4]:
            h_ = self._find_list_head_from(p, a0 + d + 0x538, a0 + d)
            whys.append(getattr(self, '_list_why', ''))
            if h_:
                return h_
        self._list_why = " || ".join(whys)
        return 0

    def _find_list_head_from(self, p, start, own_va):
        try:
            own = self._u64(p, start + 0x10)
            if own != own_va:
                self._list_why = f"node peker ikke tilbake ({hex(own)} vs {hex(own_va)})"
                return 0
            node = self._u64(p, start); steps = 0; act_n = 0; odd = []
            for _ in range(6000):
                if not node or node == start:
                    break
                steps += 1
                own = self._u64(p, node + 0x10)
                if 1 <= own < 5000:
                    self._list_why = f"hode funnet {hex(node)} (antall {own})"
                    return node
                if own and own + 0x538 == node:
                    act_n += 1
                elif len(odd) < 4:
                    odd.append(f"{hex(node)}:{hex(own)}/{hex(self._u64(p, node + 0x18))}")
                node = self._u64(p, node)
            self._list_why = f"fant ikke hode: {steps} steg, {act_n} aktører, slutt {hex(node or 0)} (start {hex(start)}), rare {odd}"
        except OSError as e:
            self._list_why = f"hode-søk {e!r}"
        return 0

    def _list_actors_raw(self, p, prefix=None):
        """Som _scan_actors_raw, men leser spillets egen ringliste over aktører (node på akt+0x538: neste +0, eier +0x10;
        antall u32 på hode+0x10). Ufullstendig runde (lista endres mens vi leser) -> None. Idé og adresser: daurosk."""
        main, delta = self.main, self.delta
        if main is None or delta is None or self.hR is None:
            return None
        try:
            if self.p_act is None:
                self._list_why = "ingen Link ennå"
                return None
            # I denne versjonen er lista ikke en ring: den ender i en vaktnode (eier 0, neste 0). Gå bakover (prev +8)
            # fra vår Link til første node, så forover til slutten.
            me_node = self.p_act + delta + 0x538
            if self._u64(p, me_node + 0x10) != self.p_act + delta:
                self._list_why = "Link-noden peker ikke tilbake"
                return None
            seen_offs = self.__dict__.setdefault('_list_offs', set())

            def _ok(nd):   # ekte node: eier ligger 0x538 (aktør) eller 0x3A0/0x3A8 (andre objekter) før noden
                try:
                    o_ = self._u64(p, nd + 0x10)
                except OSError:
                    return False
                if not o_:
                    return False
                off_ = nd - o_
                if off_ in (0x538, 0x3A0, 0x3A8):
                    return True
                # v0.94.317: Kokiri-skogen har noder med annen avstand (lista stoppet etter 1 node – «rar lengde 1»,
                # dukker og kule ble aldri funnet). Godta rimelig avstand og logg den første gangen.
                if 0x10 <= off_ <= 0x2000 and off_ % 8 == 0:
                    if off_ not in seen_offs:
                        seen_offs.add(off_); log(f'aktørliste: ny node-avstand 0x{off_:X} i {self.cur_banc}')
                    return True
                return False
            first = me_node; back = 0
            while back < 6000:
                pv = self._u64(p, first + 8)
                if not pv or not _ok(pv):
                    break
                first = pv; back += 1
            cnt = 6000
            vt = main + self.ACT_VT; now = time.time(); found = {}
            node = first; n = 0
            while node and _ok(node) and n < cnt:
                n += 1
                nh = node - delta
                nxt, _prv, own = struct.unpack('<QQQ', p.read(p.base + nh, 24))
                if own and own + 0x538 == node:
                    a = own - delta
                    try:
                        if struct.unpack('<Q', p.read(p.base + a, 8))[0] == vt:
                            nv = struct.unpack('<Q', p.read(p.base + a + 0x260, 8))[0]
                            nm = p.read(p.base + nv - delta, 48).split(bytes(1), 1)[0].decode('ascii')
                            if 'Boss' in nm or 'Gohma' in nm:
                                self.__dict__.setdefault('_bosses', {})[a] = nm
                            if nm == 'Npc_Navi':
                                self.__dict__.setdefault('_navis', {})[a] = now
                            if nm.startswith(('Weapon_', 'Obj_DekuStick', 'Item_')):
                                self.__dict__.setdefault('_weapons', {})[a] = (nm, now)
                            if (nm.startswith(prefix) if prefix else (nm.startswith(self.SYNC_PREFIX) or nm in self.DROP_NAMES)) and 'Boss' not in nm:
                                pos = p.f32(a + 0x31C, 3)
                                if all(math.isfinite(v) for v in pos) and abs(pos[0]) + abs(pos[1]) + abs(pos[2]) > 1.0:
                                    found[a] = (nm, tuple(pos))
                            elif getattr(self, '_diag_all', None) is not None:
                                self._diag_all[a] = nm
                    except (OSError, UnicodeDecodeError, TypeError):
                        pass
                node = nxt
            if n >= cnt or n < 20:
                self._list_why = f"rar lengde {n}"
                return None
            self._list_len = n
            return found
        except (OSError, struct.error, TypeError) as e:
            self._list_why = getattr(self, '_list_why', '') + ' ' + repr(e)
            return None

    def _scan_actors_raw(self, p, diag=None):
        """Levende aktører (vtable == ACT_VT, status 4) som kan synkes: {vert-offset: (navn, pos)}. ~2 s."""
        main, p_act, delta = self.main, self.p_act, self.delta
        if main is None or p_act is None or delta is None:
            return None
        vt = np.uint64(main + self.ACT_VT); found = {}
        lo = max(0, p_act - (512 << 20)); hi = min(p.size, p_act + (1024 << 20))
        # Fullt søk hvert 30. s (og første gang / ny sone); ellers bare 1 MB-bitene der det sist var aktører (± én bit)
        now = time.time(); full = now - getattr(self, '_scan_full_t', 0) > 30 or not getattr(self, '_scan_pages', None) \
            or getattr(self, '_scan_banc', None) != self.cur_banc
        if full:
            chunks = p.chunks(lo, hi)
        else:
            def _pages():
                for pg in sorted(self._scan_pages):
                    try:
                        yield pg, p.read(p.base + pg, 0x100000)
                    except OSError:
                        pass
            chunks = _pages()
        pages = set()
        for off, q in chunks:
            n = len(q) - (len(q) % 8)
            if n < 8:
                continue
            for i in np.nonzero(np.frombuffer(q[:n], dtype=np.uint64) == vt)[0].tolist():
                a = off + i * 8
                try:
                    nv = struct.unpack('<Q', p.read(p.base + a + 0x260, 8))[0]
                    nm = p.read(p.base + nv - delta, 48).split(bytes(1), 1)[0].decode('ascii')
                    if 'Boss' in nm or 'Gohma' in nm:
                        self.__dict__.setdefault('_bosses', {})[a] = nm
                    if nm == 'Npc_Navi':
                        self.__dict__.setdefault('_navis', {})[a] = now
                        pg = a & ~0xFFFFF; pages.update((pg - 0x100000, pg, pg + 0x100000))
                    if nm.startswith(('Weapon_', 'Obj_DekuStick', 'Item_')):
                        self.__dict__.setdefault('_weapons', {})[a] = (nm, now)
                        pg = a & ~0xFFFFF; pages.update((pg - 0x100000, pg, pg + 0x100000))
                    if not (nm.startswith(self.SYNC_PREFIX) or nm in self.DROP_NAMES) or 'Boss' in nm:
                        if full and diag is not None:   # v0.89: egen liste per kall (delt _diag_all ble nullstilt av andre tråder)
                            diag[a] = nm
                        elif full and getattr(self, '_diag_all', None) is not None:
                            self._diag_all[a] = nm
                        continue
                    pos = p.f32(a + 0x31C, 3)
                    if all(math.isfinite(v) for v in pos) and abs(pos[0]) + abs(pos[1]) + abs(pos[2]) > 1.0:
                        found[a] = (nm, tuple(pos))
                        pg = a & ~0xFFFFF; pages.update((pg - 0x100000, pg, pg + 0x100000))
                except (OSError, UnicodeDecodeError, TypeError):
                    pass
            del q
        if full:
            self._scan_full_t = now; self._scan_banc = self.cur_banc
            if diag is not None:   # v0.94.304: siste fulle liste kan gjenbrukes (tunika-vakta)
                self._last_full_diag = (now, self.cur_banc, dict(diag))
        self._scan_pages = {pg for pg in pages if lo <= pg < hi} | (set() if full else self._scan_pages)
        return found

    def actor_alive(self, p, a):
        if a is None or self.main is None:
            return False
        try:
            return struct.unpack('<Q', p.read(p.base + a, 8))[0] == self.main + self.ACT_VT
        except OSError:
            return False

    def navi_ready(self, p, actor, x8):
        """True bare når Navi lever, er tegnet, og transformen kan leses. Død aktør flyttes aldri."""
        if not x8 or not self.actor_alive(p, actor):
            return False
        try:
            if struct.unpack('<I', p.read(p.base + actor + 0x2C, 4))[0] != 4:
                return False
            p.read(p.base + x8 + 0x228, 4)
            return True
        except OSError:
            return False

    def actor_x8(self, p, a):
        """Transform-komponent (vert-offset) for aktøren på vert-offset a: [[[akt+0x270]+0x50]+0x20] – samme som for Link 2."""
        try:
            va = a + self.delta
            c270 = self._u64(p, va + 0x270); c50 = self._u64(p, c270 + 0x50) if c270 else 0
            x8 = self._u64(p, c50 + 0x20) if c50 else 0
            return x8 - self.delta if x8 else None
        except OSError:
            return None

    def move_actor(self, p, a, x8, pos, rot):
        try:
            r = rot if rot and len(rot) == 9 else p.f32(a + 0x328, 9)
            h = p.base + x8
            p.write(h + 0x1D0, struct.pack('<12f', r[0], r[1], r[2], pos[0], r[3], r[4], r[5], pos[1], r[6], r[7], r[8], pos[2]))
            w = struct.unpack('<I', p.read(h + 0x228, 4))[0]
            p.write(h + 0x228, struct.pack('<I', w | 3))
            return True
        except OSError:
            return False

    def create_actor(self, p, name, pos, scale=1.0, request_handle=0, runtime_request=False):
        """Lag aktør etter navn (requestCreateActor via CALL v1, data i R+0xC00, egen stack)."""
        if self.hR is None or self.main is None:
            return None
        if getattr(self, 'en_stack', None) is None:
            va = self.game_call(p, self.F_ALLOC, (0x10, 0x10000))
            if not va:
                return None
            self.en_stack = (va + 0x10000 - 0x100) & ~0xF
        R = self.R; h = p.base + self.hR + 0xC00; base = R + 0xC00
        arg = bytearray(0x100)
        struct.pack_into('<3f', arg, 0, pos[0], pos[1] + 0.5, pos[2])
        struct.pack_into('<9f', arg, 0x0C, 1, 0, 0, 0, 1, 0, 0, 0, 1)
        struct.pack_into('<3f', arg, 0x30, scale, scale, scale)
        arg[0x98] = 1 if runtime_request else 3
        default_name = base + 0x30
        if runtime_request:
            default_name = self._gv_u64(p, self.main + 0x4C7DAD0)
            if not default_name:
                return None
        struct.pack_into('<Q', arg, 0x40, default_name)
        nb = name.encode()[:0x3F]
        name_capacity = 0x40 if runtime_request else 0
        p.write(h, nb + bytes(0x40 - len(nb)) + struct.pack('<QQ', base, name_capacity) + bytes(0xB0) + bytes(arg))
        got = struct.unpack('<Q', p.read(p.base + self.hR + (self.main + self.GOT_ACTMGR - R), 8))[0]
        mgr = struct.unpack('<Q', p.read(p.base + self.hR + (got - R), 8))[0]
        return self.game_call(p, self.F_ACT_CREATE, (mgr, base + 0x40, base + 0x100, request_handle, 1, 0, 0, 0), timeout=3.0, stack_top=self.en_stack)

    def set_material_visible(self, p, act_host, mat, vis):
        """Vis/skjul ett materiale i aktørens modell (som spillets OneshotModelSetMaterialVisible, main+0x29637F0):
        modell = [[[[[akt+0x270]+8]+0x18]+0x28][0]], indeks = modell.vt[0xD0](modell, &navn), modell.vt[0x1C8](modell, indeks, vis).
        Serialisert med _mat_lk så flere tråder ikke overskriver R+0xF80 eller kaller 0x4F7620 på en utdatert modell."""
        d = self.delta
        if d is None or self.main is None or self.hR is None or not act_host:
            return None
        lk = self.__dict__.setdefault('_mat_lk', threading.Lock())
        want = 1 if vis else 0
        q = lambda va: struct.unpack('<Q', p.read(p.base + va - d, 8))[0]
        with lk:
            if not self.actor_alive(p, act_host):
                return None
            try:
                model = q(q(q(q(q(q(act_host + d + 0x270) + 8) + 0x18) + 0x28)))
                vt = q(model)
            except OSError:
                return None
            if not (0 < vt - self.main < 0x6000000):
                return None
            idx_cache = self.__dict__.setdefault('_mat_idx', {})
            idx = idx_cache.get((model, mat))
            if idx is None:
                hm = self.hR - (self.R - self.main)
                f_find = struct.unpack('<Q', p.read(p.base + hm + (vt - self.main) + 0xD0, 8))[0] - self.main
                h = p.base + self.hR + 0xF80          # R+0xF80 navn, R+0xFC0 peker (R+0x700..0x1017 er ledig)
                nb = mat.encode()
                p.write(h, nb + bytes(0x40 - len(nb))); p.write(h + 0x40, struct.pack('<Q', self.R + 0xF80))
                raw_idx = self.game_call(p, f_find, (model, self.R + 0xFC0))
                if raw_idx is None or (raw_idx & 0xFFFFFFFF) >= 0x80000000:
                    return None
                idx = raw_idx & 0xFFFFFFFF
                if len(idx_cache) > 512:
                    idx_cache.clear()
                idx_cache[(model, mat)] = idx
            try:   # f_vis (0x35961F0) kaller 0x4F7620 bare når bitet faktisk endres; hopp over CALL når det alt stemmer
                mask_va = q(model + 0xE8)
                if mask_va:
                    word = struct.unpack('<I', p.read(p.base + mask_va - d + (idx >> 5) * 4, 4))[0]
                    if ((word >> (idx & 31)) & 1) == want:
                        return 1
            except OSError:
                pass
            if not self.actor_alive(p, act_host):
                return None
            hm = self.hR - (self.R - self.main)
            f_vis = struct.unpack('<Q', p.read(p.base + hm + (vt - self.main) + 0x1C8, 8))[0] - self.main
            return self.game_call(p, f_vis, (model, idx, want))

    TUNIC_SHOW = ('Mt_Cloth',)   # v0.94.33: buksene beholdes på Linken (de forsvant – usynlige ben)
    BODY_SHOW = ('Mt_Skin', 'Mt_Cloth_Pants', 'Mt_PantsParts', 'Mt_Fur_Boots', 'Mt_Fur_Boots_AlphaMask')   # kroppen skal bli på selve Linken når farge-rustningen tas på
    TUNIC_HIDE = ('Mt_Cloth_Pants', 'Mt_Eye_Inner', 'Mt_Eye_Outer', 'Mt_Band', 'Mt_Cloth_Parts', 'Mt_Cloth_Parts_AlphaMask', 'Mt_EyeShadow_test', 'Mt_Eyebrow', 'Mt_Eyelashes_01',
                  'Mt_Eyelashes_02', 'Mt_Eyelashes_03', 'Mt_Face', 'Mt_Face_Eyelid', 'Mt_Feather', 'Mt_Fur_Boots',
                  'Mt_Fur_Boots_AlphaMask', 'Mt_Hairs', 'Mt_Leather', 'Mt_Metal', 'Mt_PantsParts', 'Mt_ShoulderBelt',
                  'Mt_Skin', 'Mt_Teeth', 'Mt_Vest')
    F_EQUIP = 0x2df7b20   # EquipmentUser::equip(eu, kind, &char*, 2, -1, 1, 0) – kind 8 = ArmorUpper (daurosk docs/puppet.md)
    F_EQUIP_STATE = 0xE34C40   # EquipmentUser::change_state(eu, slot, state) – state 1 = i hånda, 2 = lagt vekk (docs/puppet.md)
    F_EQUIP_STATE_READ = 0xCE7AB0  # EquipmentUser::state(eu, slot) – 1 = i hånda, 2 = vekk, 0 = ingen (docs/puppet.md)
    # Navnceller i patch-området (R+0x700..0x1017 er ledig): navn + char*-peker per equip-kind.
    GEAR_CELL = {0: (0x800, 0x900), 5: (0x840, 0x908), 6: (0x880, 0x910), 11: (0x8C0, 0x918)}

    def actor_equipment_user(self, p, actor):
        """EquipmentUser-komponenten til en aktør: [[akt+0x270]+0x200] (0 = aktøren har ingen)."""
        try:
            if self.delta is None or not actor:
                return 0
            gva = actor + self.delta
            return self._u64v(p, self._u64v(p, gva + 0x270) + 0x200)
        except (OSError, TypeError, struct.error):
            return 0

    def actor_equip(self, p, actor, kind, name):
        """Klekke en aktør med et utstyrt stykke: 0x2df7b20(eu, kind, &char*, 2, -1, 1, 0).

        ⚠ FORBUDT mot dukkenes EquipmentUser (v0.94.150): gjentatte kall fryser spillet
        (status=1 i kall-kassen, 0 FPS, svart skjerm) – bekreftet på begge PC-ene.
        Kallet er avviklet; dukken bærer stykkene fra EquipmentUserParam, og tilstanden
        settes med actor_equip_state().
        """
        if self.hR is None or self.main is None or not name:
            return None
        eu = self.actor_equipment_user(p, actor)
        if not eu:
            return 'no-eu'
        cell = self.GEAR_CELL.get(kind)
        if not cell:
            return None
        noff, poff = cell
        try:
            nb = name.encode()[:0x3F]
            p.write(p.base + self.hR + noff, nb + bytes(0x40 - len(nb)))
            p.write(p.base + self.hR + poff, struct.pack('<Q', self.R + noff))
        except OSError:
            return None
        return self.game_call(p, self.F_EQUIP, (eu, kind, self.R + poff, 2, 0xFFFFFFFFFFFFFFFF, 1, 0), timeout=3.0)

    def actor_equip_state(self, p, actor, slot, state):
        """Sette et utstyrt stykke i hånda (1) eller vekk (2): 0xE34C40(eu, slot, state)."""
        eu = self.actor_equipment_user(p, actor)
        if not eu:
            return 'no-eu'
        return self.game_call(p, self.F_EQUIP_STATE, (eu, slot, state), timeout=3.0)

    def actor_equip_state_read(self, p, actor, slot):
        """Spillets egen tilstandslesing for en slot: 0xCE7AB0(eu, slot).

        Returnerer 1 = i hånda, 2 = lagt vekk, 0 = ingen stykke, None = feilet.
        Dette er spillets egen sannhet. Request-byten på eu+0x13BC er derimot
        bare et flyktig ønske som spillet nuller straks det er utført
        (docs/puppet.md: "the byte is a request, not the state"). Samme kringle
        bruker coop-modens egen Director::OwnState.
        """
        eu = self.actor_equipment_user(p, actor)
        if not eu:
            return None
        r = self.game_call(p, self.F_EQUIP_STATE_READ, (eu, slot), timeout=1.5)
        if r is None:
            return None
        try:
            v = int(r)
        except (TypeError, ValueError):
            return None
        if v not in (0, 1, 2):
            # Ukjent svar: da vet vi ikke hva spillet gjorde. Ikke gå ut fra noe,
            # og ikke ring i en løkke (v0.94.151).
            self._last_call_err = f'ugyldig tilstand {v}'
            return None
        return v

    # ---- v0.94.149: lese EquipmentUser-slottene (ren minnelesing, ingen spillkall) ----
    def actor_equip_slot(self, p, actor, slot):
        """(stykkets aktør-VA, id) i EquipmentUser-sloten; (0, 0) hvis sloten er tom.

        Slottene ligger paa eu+0x20 med 0x18 per slot: +0x8 = holder-peker, +0x10 = id
        (0xFFFFFFFF = tom). Holder-pekeren peker paa et lenke-objekt der +0x40 er stykkets aktør.
        """
        eu = self.actor_equipment_user(p, actor)
        if not eu or self.delta is None:
            return 0, 0
        link = eu + 0x20 + 0x18 * slot
        try:
            sid = struct.unpack('<I', p.read(p.base + link + 0x10 - self.delta, 4))[0]
            holder = self._u64v(p, link + 8)
        except (OSError, struct.error, TypeError):
            return 0, 0
        if not holder or sid == 0xFFFFFFFF:
            return 0, 0
        try:
            piece = self._u64v(p, holder + 0x40)
        except (OSError, struct.error, TypeError):
            return 0, 0
        return piece, sid

    def actor_equip_slot_byte(self, p, actor, slot):
        """Statusbyten for sloten (eu+0x13BC+slot): 2 = i hånda, 4 = lagt vekk."""
        eu = self.actor_equipment_user(p, actor)
        if not eu or self.delta is None:
            return None
        try:
            return p.read(p.base + eu + 0x13BC + slot - self.delta, 1)[0]
        except (OSError, IndexError, TypeError):
            return None

    def actor_piece_name(self, p, piece):
        """Navnet på en aktør (aktør+0x260 -> char*)."""
        if not piece or self.delta is None:
            return None
        try:
            nptr = self._u64v(p, piece + 0x260)
            if not nptr:
                return None
            raw = p.read(p.base + nptr - self.delta, 48).split(b'\0')[0]
            return raw.decode('utf-8', 'replace') or None
        except (OSError, struct.error, TypeError):
            return None

    def actor_piece_state(self, p, piece):
        """Stykkets tilstand (piece+0x2C): 4 = i hånda, 6 = gjemt."""
        if not piece or self.delta is None:
            return None
        try:
            return struct.unpack('<I', p.read(p.base + piece + 0x2C - self.delta, 4))[0]
        except (OSError, struct.error, TypeError):
            return None

    def _wear_tunic(self, p, copy, c_act, look, who='l2'):
        """Ta på Link 2 tunika-rustningen i vennens farge og vis bare tunikaen på den."""
        try:
            d = self.delta
            if c_act is None or d is None:   # scene-/pekeroppdagelse kan nullstille delta mens denne jobben venter
                return
            # v0.94.178: F_EQUIP (0x2DF7B20) fryser spilltråden permanent hvis den kalles rett etter
            # rombytte/teleport eller før pakken er lastet i gjeldende sone.
            now_t = time.time()
            if (not self.cur_banc
                    or now_t - getattr(self, '_banc_since', now_t) < 12.0
                    or now_t < getattr(self, '_tp_t', 0) + 8.0):
                # v0.94.311: for tidlig (rett etter teleport/sonebytte) – ikke tell dette som et forsøk. Før ble det siste av
                # to forsøk brukt opp her i PvP-arenaen (hyppige teleporter), og egen Link fikk aldri ny farge (GAMER: Purple).
                if who == 'me':
                    log(f'tunika: venter – rett etter teleport/sonebytte ({look})')
                return
            name = f'Armor_Child_Tunic_{TUNIC_LETTER[look]}'
            for m in self.TUNIC_SHOW + ('Mt_Cloth_Pants',):   # v0.94.24: vis vanlig tunika mens den nye lages (ellers «Link uten tunika og lue» en stund)
                self.set_material_visible(p, c_act, m, True)
            a = c_act + d
            eu = self._u64v(p, self._u64v(p, a + 0x270) + 0x200)
            if not eu:
                if who == 'me':
                    log(f'tunika: fant ikke utstyrskomponenten til min Link ({look}) – prøver igjen')
                return
            # navnet i patch-området R+0x7C0 (vert hR) – F_ALLOC-minne var ikke alltid koblet likt (spillet leste nuller)
            p.write(p.base + self.hR + 0x7C0, name.encode()[:0x37] + bytes(0x38 - min(len(name), 0x37)))
            p.write(p.base + self.hR + 0x7F8, struct.pack('<Q', self.R + 0x7C0))
            loaded = self.__dict__.setdefault('_tun_loaded', set())
            load_key = (self.cur_banc, name)
            if load_key not in loaded:   # v0.94.178: sjekk alltid i gjeldende sone før F_EQUIP
                dg0 = {}; self._scan_full_t = 0; self._scan_actors_raw(p, dg0)
                if any(n0 == name for n0 in dg0.values()):
                    loaded.add(load_key)
            if load_key not in loaded:
                # v0.68: equip-kallet laster pakken på spilltråden og frøs spillet når den ikke var lastet ennå.
                # Last den først med en vanlig (asynkron) aktør under bakken, skjul den, og ta på etterpå. Den slettes ikke (sletting hang).
                l2p = p.f32(c_act + 0x31C, 3)
                rr = self.create_actor(p, name, [l2p[0], l2p[1] - 30.0, l2p[2]])
                log(f'tunika: laster {name} først -> {rr}')
                if rr is None:
                    return
                time.sleep(4.0)
                dg = {}; self._scan_full_t = 0; self._scan_actors_raw(p, dg)
                for ha, nm in list(dg.items()):
                    if nm == name:
                        for m in self.TUNIC_HIDE + self.TUNIC_SHOW:
                            self.set_material_visible(p, ha, m, False)
                self._diag_all = None
                loaded.add(load_key)
                return   # neste forsøk (om 5 s) tar den på
            # v0.94.280: har Link allerede på seg dette plagget (f.eks. etter omstart av modden i samme spill)?
            # Å ta på samme stykke igjen frøs spilltråden (23:29:55, Armor_Child_Tunic_C). Sjekk aktørene ved Link først.
            try:
                lp_ = p.f32(c_act + 0x31C, 3)
                dgw = {}; self._scan_full_t = 0; self._scan_actors_raw(p, dgw); self._diag_all = None
                worn_arm = next((ha for ha, nm in dgw.items() if nm == name and math.dist(p.f32(ha + 0x31C, 3), lp_) < 0.3), None)
                worn = worn_arm is not None
                other = any(nm.startswith('Armor_Child_Tunic_') and nm != name and math.dist(p.f32(ha + 0x31C, 3), lp_) < 0.3 for ha, nm in dgw.items())
                # v0.94.279/280: oppstartsfargen ligger i romfs – uten annet mod-plagg på er Link allerede riktig farge
                if who == 'me' and look == getattr(self, 'romfs_look', None) and not other:
                    worn = True
            except OSError:
                worn = False
            if worn:
                if worn_arm is not None:
                    # v0.94.297: plagget sitter allerede på (modd-omstart i samme spill) – sørg for at bare plagget vises.
                    # Før kunne grunn-tunikaen (romfs-fargen) bli synlig igjen under plagget: to tunikaer oppå hverandre
                    # som flimret mellom fargene (hvit Link som blinket cyan).
                    try:
                        for m in self.TUNIC_SHOW:
                            self.set_material_visible(p, worn_arm, m, True)
                            self.set_material_visible(p, c_act, m, False)
                        self.__dict__.setdefault('_tun_worn', {})[who] = (worn_arm, c_act)
                    except OSError:
                        pass
                self.__dict__[{'l2': '_tun_done', 'me': '_tun_done_me'}.get(who, '_tun_done_bot')] = (copy, look)
                log(f"tunika: {'Link 2' if who == 'l2' else 'min Link'} har allerede {name} på – tar ikke på igjen")
                return
            equip_called = (copy, look)   # v0.94.313: F_EQUIP aldri to ganger for samme farge, heller ikke etter et unntak
            r = self.game_call(p, self.F_EQUIP, (eu, 8, self.R + 0x7F8, 2, 0xFFFFFFFFFFFFFFFF, 1, 0), timeout=3.0)
            who_label = 'Link 2' if who == 'l2' else 'min Link'
            log(f'tunika: {who_label} tar på {name} -> {r}')
            if r is None:
                # v0.94.114: None betyr at spilltråden ikke ble ferdig. Nytt kall hvert 5. s holdt den opptatt.
                self.__dict__[{'l2': '_tun_fail', 'me': '_tun_fail_me'}.get(who, '_tun_fail_bot')] = (copy, look)
                log(f'tunika: stopper nye forsøk for {who_label} ({name})')
                return
            l2 = p.f32(c_act + 0x31C, 3)
            arm = None
            for _ in range(10):   # rustningen lages litt etterpå – finn den ved Link 2
                time.sleep(0.5)
                dg = {}
                self._scan_full_t = 0
                self._scan_actors_raw(p, dg)
                others = []
                for ha, nm in list(dg.items()):
                    if nm.startswith('Armor_Child_Tunic_'):
                        try:
                            if math.dist(p.f32(ha + 0x31C, 3), l2) < 0.3:   # festet del står i aktørens origo (0,00 m)
                                if nm == name:
                                    arm = ha
                                else:
                                    others.append(ha)   # en tidligere farge som fortsatt henger på Link 2
                        except OSError:
                            pass
                self._diag_all = None
                if arm:
                    break
            if not arm:
                # v0.94.114: ett nytt equip-kall etter «fant ikke» hang spilltråden. Ikke prøv igjen for denne kopien.
                self.__dict__[{'l2': '_tun_fail', 'me': '_tun_fail_me'}.get(who, '_tun_fail_bot')] = (copy, look)
                log(f'tunika: fant ikke {name} ved Link 2 – stopper nye forsøk')
                return
            for m in self.TUNIC_HIDE:
                self.set_material_visible(p, arm, m, False)
            for m in self.TUNIC_SHOW:
                self.set_material_visible(p, arm, m, True)
                self.set_material_visible(p, c_act, m, False)
            for m in self.BODY_SHOW:   # v0.94.38: equip kan skjule kropp/støvler på Link 2; fargen kommer kun fra rustningen
                self.set_material_visible(p, c_act, m, True)
            for old in others:   # tidligere farger på Link 2 skjules
                for m in self.TUNIC_SHOW + self.TUNIC_HIDE:
                    self.set_material_visible(p, old, m, False)
            if others:
                log(f'tunika: skjulte {len(others)} gammel(e) tunika på Link 2')
            self._tun_arm, self._tun_arm_copy = arm, copy
            self.__dict__[{'l2': '_tun_done', 'me': '_tun_done_me'}.get(who, '_tun_done_bot')] = (copy, look)
            self.__dict__.setdefault('_tun_worn', {})[who] = (arm, c_act)
            log(f'tunika: {"Link 2" if who == "l2" else "min Link"} har {look} tunika ({name} @0x{arm:X})')
        except Exception as e:  # noqa: BLE001
            log(f'tunika: feil {e!r}')
            if 'equip_called' in locals():
                self.__dict__[{'l2': '_tun_fail', 'me': '_tun_fail_me'}.get(who, '_tun_fail_bot')] = (copy, look)
        finally:
            self._tun_busy = False

    # v0.80 «hit replay» – overført fra daurosk/oot-remake-multiplayer lichii/hook/coop_hit_replay.h (GPLv3):
    # en hel treffpost skrives inn i Life-komponenten; spillets egen skadefunksjon gir liv, rykk og tilbakeslag.
    HIT_TEMPLATE = (
        0x472d7288, 0x00000021, 0x000000b9, 0x00000001, 0x00060001, 0x40040000, 0x00000014, 0x00000000,
        0x00220000, 0x00001000, 0x0000000a, 0x00000000, 0x00000200, 0x00000000, 0x00000000, 0xc21085f6,
        0x42c63e88, 0x40501269, 0x3e76ed80, 0xb3c00000, 0xbf787210, 0x40588db0, 0xc1129418, 0xc0cb90a0,
        0xc210600c, 0x42c45791, 0x409352f5, 0xbdcc4eb0, 0x3ecc555c, 0xc0d481b8, 0x000343ff, 0x00040000,
        0x00000004, 0x000000be, 0x00000002, 0x03000000, 0x03010102, 0x00030000)

    def hit_replay(self, p, victim, attacker, amount, heavy=False):
        """Gi `victim` (vert-offset) et treff fra `attacker` (vert-offset) gjennom spillets egen Life-steg."""
        if victim is None or self.delta is None:
            return False
        try:
            d = self.delta
            life = self._u64v(p, self._u64v(p, victim + d + 0x270) + 0x2B8)
            if not life:
                return False
            last = struct.unpack('<I', p.read(p.base + life + 0x1B18 - d, 4))[0]
            hid = (0x1000 if last == 0xFFFFFFFF else last + 2) & 0x7FFFFFFF
            rec = list(self.HIT_TEMPLATE)
            att = (attacker + d) if attacker is not None else 0
            rec[0], rec[1] = att & 0xFFFFFFFF, att >> 32
            rec[2] = hid; rec[(0x2C4 - 0x240) // 4] = hid; rec[3] = 0
            at = p.f32(victim + 0x31C, 3)
            frm = p.f32(attacker + 0x31C, 3) if attacker is not None else at
            # v0.94.309: treff på avstand (sprettert, 6,7 m) ble ikke tatt av spillet (HP ikke trukket, ingen reaksjon).
            # Legg angrepsstedet maks 1,2 m fra offeret i angriperens retning, som et nærslag.
            ddx, ddz = frm[0] - at[0], frm[2] - at[2]
            dd = math.hypot(ddx, ddz)
            if dd > 1.2:
                frm = [at[0] + ddx / dd * 1.0, at[1], at[2] + ddz / dd * 1.0]
            if heavy:   # skyv angrepsstedet litt lenger bort -> kraftigere tilbakeslag? (spillet bestemmer selv)
                frm = [at[i] + (frm[i] - at[i]) * 2.0 for i in range(3)]
            raw = bytearray(struct.pack('<38I', *rec))
            struct.pack_into('<3f', raw, 0x27C - 0x240, at[0], at[1] + 1.0, at[2])
            struct.pack_into('<3f', raw, 0x2A0 - 0x240, *frm)
            p.write(p.base + life + 0x1F8 - d, struct.pack('<4I', 0x00060001, 0x40040000, hid, 2))
            p.write(p.base + life + 0x224 - d, struct.pack('<2i', 4, int(amount)))
            p.write(p.base + life + 0x240 - d, bytes(raw))
            p.write(p.base + life + 0x240 + 0xC - d, struct.pack('<I', 1))
            return True
        except Exception:  # noqa: BLE001
            return False

    def delete_actor(self, p, a):
        """Slett en aktør – ALDRI samme adresse to ganger på 60 s (dobbel sletting kan henge spillet)."""
        dd = self.__dict__.setdefault('_del_t', {})
        now = time.time()
        if now - dd.get(a, 0) < 60:
            return None
        if not self.actor_alive(p, a):
            return None
        dd[a] = now
        if len(dd) > 500:
            for k in [k for k, t in dd.items() if now - t > 60]:
                dd.pop(k, None)
        self.__dict__.setdefault('self_deleted', set()).add(a)
        return self.game_call(p, self.F_ACT_DELETE, (a + self.delta, 0), timeout=2.0)

    def learn_start(self, banc, start, kilde):
        if banc and start and self.START_POS.get(banc) == start and getattr(self, '_door_seen', None) != (banc, start):
            self._door_seen = (banc, start); log(f'PadLink: startpunkt bekreftet {banc} -> {start} ({kilde})')
        if banc and start and self.START_POS.get(banc) != start:
            self.START_POS[banc] = start; self.learned_new = True
            log(f'PadLink: lærte startpunkt {banc} -> {start} ({kilde})')

    GOT_WM, F_LD8, F_ST32 = 0x4E7EAB0, 0x37AF070, 0x9B25C0   # WorldMgr-peker; minnegadgets
    F_GET_TIME = 0x2A8DE0  # WorldTime-getter; server_clock_v1 styrer den kun når PvP-magi er aktiv

    def _time_addr(self, p):
        """Original v0.94.49-oppslag via spilltråden. Ingen direkte klokkeskanning."""
        now = time.time()
        if getattr(self, '_wt_addr', None) and now - self._wt_t < 10:
            return self._wt_addr
        self._wt_addr, self._wt_t = None, now
        if self.hR is None or self.main is None:
            return None
        ld = lambda va: self.game_call(p, self.F_LD8, (va - 8,))
        wm = struct.unpack('<Q', p.read(p.base + self.hR + (self.main + self.GOT_WM - self.R), 8))[0]
        obj = ld(wm + 0x578) if wm else None
        self._wt_obj = obj
        t = ld(obj + 0xD48) if obj else None
        flags = ld(t + 8) if t else None
        if not t or flags is None or (flags >> 8) & 2:
            return None
        self._wt_addr = t + 0x28
        return self._wt_addr

    def read_time(self, p):
        a = self._time_addr(p)
        obj = getattr(self, '_wt_obj', None)
        v = self.game_call(p, self.F_GET_TIME, (obj,)) if a and obj else None
        return None if v is None else (v & 0xFFFFFFFF) % 86400

    WEATHERS = ('Bluesky', 'Rain', 'Snow', 'Thunderstorm', 'Cloudy')   # verdi fra tid/vær-objektets vtable+0xF0
    GOT_WEATHER, F_SET_WEATHER = 0x4C7E898, 0x3454FB0                   # SetWeather(mgr, &navn, overgang) – 0 = straks

    def read_weather(self, p):
        a = self._time_addr(p)          # sørger for at _wt_obj er satt
        obj = getattr(self, '_wt_obj', None)
        if not a or not obj:
            return None
        if getattr(self, '_wt_fget', None) is None:
            vt = self.game_call(p, self.F_LD8, (obj - 8,))
            f = self.game_call(p, self.F_LD8, (vt + 0xF0 - 8,)) if vt else None
            self._wt_fget = (f - self.main) if f else None
        if not self._wt_fget:
            return None
        v = self.game_call(p, self._wt_fget, (obj,))
        return v if v is not None and 0 <= v < len(self.WEATHERS) else None

    def write_weather(self, p, w, speed=5):
        if self.hR is None or not (0 <= w < len(self.WEATHERS)):
            return False
        mgr_p = struct.unpack('<Q', p.read(p.base + self.hR + (self.main + self.GOT_WEATHER - self.R), 8))[0]
        mgr = self.game_call(p, self.F_LD8, (mgr_p - 8,)) if mgr_p else None
        if not mgr:
            return False
        name = self.WEATHERS[w].encode()
        h = p.base + self.hR + 0xE80                     # v0.83: R+0xE80 navn, R+0xEC0 peker (R+0xA00..0xB30 = botens falske kontroller)
        p.write(h, name + bytes(0x40 - len(name))); p.write(h + 0x40, struct.pack('<Q', self.R + 0xE80))
        return self.game_call(p, self.F_SET_WEATHER, (mgr, self.R + 0xEC0, speed), timeout=3.0) is not None

    def write_time(self, p, sec):
        a = self._time_addr(p)
        return a is not None and self.game_call(p, self.F_ST32, (a, int(sec) % 86400)) is not None

    def _find_host_ptr(self, p, va, check_fn):
        """Oversett gjeste-VA til verts-offset (p.base + off) via 2 MB-vinduer når VA ligger i et annet segment enn self.delta."""
        if not va:
            return None
        if self.delta:
            cand = va - self.delta
            if 0 <= cand < p.size:
                try:
                    if check_fn(cand):
                        return cand
                except OSError:
                    pass
        low = va & 0x1FFFFF
        hi = min(p.size, 0x3C0000000)
        for s, e in ((0x280000000 + low, hi), (low, min(0x280000000, hi))):
            for o in range(s, e, 0x200000):
                try:
                    if check_fn(o):
                        return o
                except OSError:
                    pass
        return None

    def read_banc(self, p):
        """Gjeldende sone (banc-navn) fra BancLoadMgr+0x4C; pekeren ligger på R+0x1260D0."""
        if self.hR is None:
            return None
        try:
            if self.h_blm is not None:
                s = p.read(p.base + self.h_blm + 0x4C, 75)
                if s.startswith(b"Work/Banc/GameBancParam/"):
                    return s.split(b"\0")[0].decode("latin1").split("/")[-1].split(".")[0] or None
                self.h_blm = None
            if time.time() - getattr(self, "_blm_scan_t", 0) < 3.0:   # fullt søk er tregt (sonelasting) – maks hvert 3. s
                return None
            self._blm_scan_t = time.time()
            va = struct.unpack("<Q", p.read(p.base + self.hR + 0x1260D0, 8))[0]
            h_blm = self._find_host_ptr(p, va, lambda o: p.read(p.base + o + 0x4C, 24) == b"Work/Banc/GameBancParam/")
            if h_blm is None:
                return None
            self.h_blm = h_blm
            s = p.read(p.base + h_blm + 0x4C, 75)
            return s.split(b"\0")[0].decode("latin1").split("/")[-1].split(".")[0] or None
        except OSError:
            self.h_blm = None
            return None

    def banc_tick(self, p, now):
        """Følg med på sonen, og utfør ventende teleport når ny aktør + posisjon er klar i målsonen."""
        if self.p_act != self._last_p_act:
            self._last_p_act = self.p_act
            self._p_act_since = now if self.p_act is not None else 0.0
        if now - self._banc_t < 0.5:
            return
        self._banc_t = now
        d = self.read_door(p)
        if d:
            self.learn_start(d[0], d[1], 'dør')
        b = self.read_banc(p)
        if b and b != self.cur_banc:
            if self.cur_banc is not None:
                log(f"PadLink: sone {self.cur_banc} -> {b}"); self.scene_changed = True
                self._zone_dead = set(getattr(self, "_zone_dead", set()))   # alle kopier fra forrige sone er døde – ta dem aldri i bruk igjen
                if self.copy is not None:   # sonebytte fjerner alle aktører – gammel Link 2 finnes ikke lenger
                    self._zone_dead.add(self.copy)
                    log("PadLink: sonebytte – glemmer gammel Link 2")
                    self.copy = None; self.c_act = self.c_x8 = self.c_x9 = None
                    self._c_sv_cur = self._c_sv_max = None; self._hidden = False
                    self.__dict__.get("_pup_blink_addrs", {}).clear()
                    try: p.write(p.base + self.hR + 0x288, bytes(8))
                    except Exception: pass
            self.cur_banc = b; self._banc_since = now; self._zone_pos = self.my_apos(p)   # posisjon i det sonen byttet (lasting pågår så lenge den står stille her)
        tp = self._pending_tp
        if tp:
            if now - tp[3] > 40:
                self._pending_tp = None
            elif (self.cur_banc == tp[0] and now - tp[3] >= 6 and self.p_act is not None and self.p_x8 is not None
                  and now - self._p_act_since >= 1.5
                  and now - self._banc_since >= 8.0 and self.my_apos(p) is not None):
                self._pending_tp = None
                # v0.94.154: ikke teleporter rett etter en annen teleport. Et dobbelt-
                # bytte (partyteleport + 'teleport etter sonebytte' 0,5 s senere) fros
                # spillet (0 FPS, svart skjerm) på lokal PC 2026-11-19 00:38.
                if now - getattr(self, '_last_tp_done', 0) < 10.0:
                    log(f'PadLink: teleport etter sonebytte hoppet over (teleportert '
                        f'{now - getattr(self, "_last_tp_done", 0):.1f} s siden)')
                    return
                if tp[1]:
                    ok = self.teleport_player(p, tp[1], tp[2]); log(f"PadLink: teleport etter sonebytte -> {ok}")

    def game_call(self, p, func_off, args=(), timeout=2.0, stack_top=0):
        if time.time() < getattr(self, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN:   # v0.56: ingen spillkall rett etter teleport (spillet frøs ved Gohma)
            self._last_call_err = 'tp_cooldown'
            return None
        t0 = time.perf_counter()
        try:
            return self._game_call_raw(p, func_off, args, timeout, stack_top)
        finally:
            perf_add('spillkall', time.perf_counter() - t0)

    def _game_call_raw(self, p, func_off, args=(), timeout=2.0, stack_top=0):
        """Kall main+func_off(x0..x7) på spilltråden via call_v1-patchen. Trådsikker via _call_lk.
        stack_top != 0: kallet kjører på en egen stack (M+0x58, call_v1 med 59 instr.) som ikke overskrives etterpå –
        nødvendig når funksjonen gir en arbeidertråd pekere inn i sin egen stackramme (requestCreateActor)."""
        if self.hR is None or self.main is None or getattr(self, "has_call", None) is False:
            self._last_call_err = 'no_call'
            return None
        with self._call_lk:
            h = p.base + self.hR + self.CALL_OFF
            try:
                busy_deadline = time.time() + 0.25
                while struct.unpack("<I", p.read(h, 4))[0] not in (0, 3):
                    if time.time() >= busy_deadline:
                        self._last_call_err = 'busy'
                        return None
                    time.sleep(0.01)
                a = (list(args) + [0] * 8)[:8]
                p.write(h + 8, struct.pack("<9Q", self.main + func_off, *a))
                p.write(h + 0x58, struct.pack("<Q", stack_top))
                p.write(h, struct.pack("<I", 1))
                t0 = time.time()
                while time.time() - t0 < timeout:
                    if struct.unpack("<I", p.read(h, 4))[0] == 3:
                        res = struct.unpack("<Q", p.read(h + 0x50, 8))[0]
                        p.write(h + 0x58, bytes(8)); p.write(h, bytes(4)); self.has_call = True; self._call_timeouts = 0
                        self._last_call_err = None
                        return res
                    time.sleep(0.004)
                if struct.unpack("<I", p.read(h, 4))[0] == 1:      # aldri plukket opp -> patchen mangler eller spillet er midt i lasting
                    p.write(h, bytes(4))
                    self._call_timeouts += 1
                    if getattr(self, "has_call", None) is None and self._call_timeouts >= 3:
                        self.has_call = False; log("PadLink: call_v1-patchen svarer ikke – sonebytte (TVANG) er ikke tilgjengelig")
                self._last_call_err = 'timeout'
            except OSError:
                self._last_call_err = 'oserror'
            return None

    GOT_BGMMGR = 0x4C7F3F8
    F_BGM_SIMPLE = 0x3356A40         # StartBgm(BgmMgr, &str_ptr, start_flag: 1=start, 0=stop)
    F_BGM_ENTRY_VOL = 0x3356790      # SetEntryVolume(BgmEntry, vol_f32_bits)
    F_BGM_EV_PLAY = 0x3784430        # SoundEvent::Play(ev) – setter +0x68 |= 0x1000 -> 0x1022 (faktisk avspilling)
    F_BGM_EV_VOL = 0x3784360         # SoundEvent::SetVolumePtr(ev, &{vol, fade_sec, 0}, 0) – virker også når +0x68 & 4 != 0
    F_BGM_EV_STOP = 0x3784450        # SoundEvent::StopPtr(ev) – setter +0x68 |= 0x2000 (stopper BGM_Market & c38[103])
    F_BGM_EV_LOOKUP = 0x378B300      # SoundMgr::FindEvent(c38, &out_ev, name_hash)
    F_MURMUR3 = 0x1739E0             # Murmur3_32(cstr, 0)

    def _gv_bytes(self, p, va, n):
        if self.main is not None and self.hR is not None and self.R is not None and self.main <= va < self.main + 0x5200000:
            return p.read(p.base + self.hR + (va - self.R), n)
        if self.delta is None:
            raise OSError("mangler delta")
        return p.read(p.base + va - self.delta, n)

    def _gv_u64(self, p, va):
        return struct.unpack("<Q", self._gv_bytes(p, va, 8))[0]

    def _gv_u32(self, p, va):
        return struct.unpack("<I", self._gv_bytes(p, va, 4))[0]

    def _bgm_entries_set_vol(self, p, mgr, vol, exclude_ev=0):
        """Sett BgmEntry-volum i aktiv [mgr+0x290]-liste (1.0=normal, <1.0=dempet)."""
        if not mgr:
            return 0
        vbits = struct.unpack("<I", struct.pack("<f", max(0.0, min(1.0, float(vol)))))[0]
        head = self._gv_u64(p, mgr + 0x298)
        cnt = self._gv_u32(p, mgr + 0x2A0)
        noff = struct.unpack("<i", self._gv_bytes(p, mgr + 0x2A4, 4))[0]
        sentinel = mgr + 0x290
        cur = head
        updated = 0
        for _ in range(min(cnt, 16)):
            if not cur or cur == sentinel:
                break
            entry = cur - noff
            v54 = self._gv_u32(p, entry + 0x54)
            if (v54 & 4) != 0:
                if exclude_ev and self._gv_u64(p, entry + 0x30) == exclude_ev:
                    cur = self._gv_u64(p, cur + 8)
                    continue
                if self.game_call(p, self.F_BGM_ENTRY_VOL, (entry, vbits), timeout=1.0) is not None:
                    updated += 1
            cur = self._gv_u64(p, cur + 8)
        return updated

    def _bgm_lookup_ev(self, p, c38, name):
        """Slå opp SoundEvent-peker for BGM-navn via F_MURMUR3 + F_BGM_EV_LOOKUP. Returnerer None hvis spillkall svikter."""
        if not c38 or not name:
            return 0
        b = name.encode("ascii", "ignore")[:40] + b"\0"
        p.write(p.base + self.hR + 0x5D0, b)
        h = self.game_call(p, self.F_MURMUR3, (self.R + 0x5D0, 0), timeout=1.0)
        if h is None:
            return None
        if not h:
            return 0
        p.write(p.base + self.hR + 0x5B8, bytes(8))
        ok = self.game_call(p, self.F_BGM_EV_LOOKUP, (c38, self.R + 0x5B8, h & 0xFFFFFFFF), timeout=1.0)
        if ok is None:
            return None
        return struct.unpack("<Q", p.read(p.base + self.hR + 0x5B8, 8))[0] if ok else 0

    def _bgm_stop_track(self, p, mgr, c38, name):
        """Stopp én SoundEvent direkte via F_BGM_EV_STOP (eller F_BGM_SIMPLE reserve). Returnerer False ved timeout."""
        if not name:
            return True
        ev = self._bgm_lookup_ev(p, c38, name)
        if ev is None:
            return False
        if ev:
            return self.game_call(p, self.F_BGM_EV_STOP, (ev,), timeout=1.0) is not None
        b = name.encode("ascii", "ignore")[:40] + b"\0"
        p.write(p.base + self.hR + 0x5D0, b)
        p.write(p.base + self.hR + 0x5C0, struct.pack("<Q", self.R + 0x5D0))
        return self.game_call(p, self.F_BGM_SIMPLE, (mgr, self.R + 0x5C0, 0), timeout=1.0) is not None

    def set_lobby_bgm(self, p, play_name="BGM_Drugstore", stop_names=("BGM_Market",), vol=0.35):
        """Bytt bakgrunnsmusikk og demp volum lokalt via BgmMgr + SoundEvent (kun PvP-lobby)."""
        if self.hR is None or self.R is None or self.main is None or self.delta is None:
            return False
        if getattr(self, "has_call", None) is False:
            return False
        vol = max(0.0, min(1.0, float(vol)))
        with self._ev_lk:
            try:
                mgr = self._gv_u64(p, self._gv_u64(p, self.main + self.GOT_BGMMGR))
                if not mgr:
                    return False
                c38 = self._gv_u64(p, mgr + 0x38)
                for nm in (stop_names or ()):
                    if nm and nm != play_name:
                        if not self._bgm_stop_track(p, mgr, c38, nm):
                            return False
                started = False
                play_ev = 0
                if play_name and play_name.lower() not in ("off", "none", "mute"):
                    play_ev = self._bgm_lookup_ev(p, c38, play_name)
                    if play_ev is None:
                        return False
                # Stopp eventuelle andre aktivt spillende c38-hendelser (f.eks. c38[103] 0xB2964231 i Market_Child)
                try:
                    c38_cnt = self._gv_u32(p, c38 + 0x80)
                    c38_arr = self._gv_u64(p, c38 + 0x88)
                    if c38_arr and 0 < c38_cnt <= 256:
                        for i in range(c38_cnt):
                            ev_i = self._gv_u64(p, c38_arr + i * 8)
                            if ev_i and ev_i != play_ev and (self._gv_u32(p, ev_i + 0x68) & 0x20):
                                if self.game_call(p, self.F_BGM_EV_STOP, (ev_i,), timeout=1.0) is None:
                                    return False
                except OSError:
                    pass
                self._bgm_entries_set_vol(p, mgr, 0.0 if play_ev else vol, exclude_ev=play_ev)
                if play_name and play_name.lower() not in ("off", "none", "mute"):
                    if play_ev:
                        p.write(p.base + self.hR + 0x5E0, struct.pack("<ffI", vol, 0.25, 0))
                        if self.game_call(p, self.F_BGM_EV_VOL, (play_ev, self.R + 0x5E0, 0), timeout=1.0) is None:
                            return False
                        if self.game_call(p, self.F_BGM_EV_PLAY, (play_ev,), timeout=1.0) is None:
                            return False
                        try:
                            p.write(p.base + play_ev - self.delta + 0x21C, struct.pack("<2f", vol, vol))
                        except OSError:
                            pass
                        started = True
                    else:
                        b = play_name.encode("ascii", "ignore")[:40] + b"\0"
                        p.write(p.base + self.hR + 0x5D0, b)
                        p.write(p.base + self.hR + 0x5C0, struct.pack("<Q", self.R + 0x5D0))
                        if self.game_call(p, self.F_BGM_SIMPLE, (mgr, self.R + 0x5C0, 1), timeout=1.0) is None:
                            return False
                        started = True
                if hasattr(self, "_list_actors_raw") and hasattr(self, "delete_actor"):
                    try:
                        bgm_actors = self._list_actors_raw(p, prefix="BGM_") or {}
                        for ah, (aname, _apos) in bgm_actors.items():
                            if aname == "BGM_MiniGameShop_Bombchu":
                                self.delete_actor(p, ah)
                    except OSError:
                        pass
                return started or bool(mgr)
            except OSError:
                return False

    def restore_lobby_bgm(self, p, stop_names=("BGM_Drugstore", "BGM_Shop_ScrubBusiness", "BGM_Shop_Desert",
                                                "BGM_MiniGame", "BGM_House", "BGM_GreatFairyFountain", "BGM_Silence"),
                          restart_market=False):
        """Gjenopprett normalt BGM-volum og stopp midlertidig PvP-lobbysang når spiller forlater lobbyen."""
        if self.hR is None or self.R is None or self.main is None or self.delta is None:
            return False
        if getattr(self, "has_call", None) is False:
            return False
        with self._ev_lk:
            try:
                mgr = self._gv_u64(p, self._gv_u64(p, self.main + self.GOT_BGMMGR))
                if not mgr:
                    return False
                c38 = self._gv_u64(p, mgr + 0x38)
                for nm in stop_names:
                    if not self._bgm_stop_track(p, mgr, c38, nm):
                        return False
                self._bgm_entries_set_vol(p, mgr, 1.0)
                if restart_market:
                    ev_m = self._bgm_lookup_ev(p, c38, "BGM_Market")
                    if ev_m:
                        p.write(p.base + self.hR + 0x5E0, struct.pack("<ffI", 1.0, 0.25, 0))
                        if self.game_call(p, self.F_BGM_EV_VOL, (ev_m, self.R + 0x5E0, 0), timeout=1.0) is None:
                            return False
                        if self.game_call(p, self.F_BGM_EV_PLAY, (ev_m,), timeout=1.0) is None:
                            return False
                    else:
                        p.write(p.base + self.hR + 0x5D0, b"BGM_Market\0")
                        p.write(p.base + self.hR + 0x5C0, struct.pack("<Q", self.R + 0x5D0))
                        if self.game_call(p, self.F_BGM_SIMPLE, (mgr, self.R + 0x5C0, 1), timeout=1.0) is None:
                            return False
                return True
            except OSError:
                return False

    def event_busy(self, p):
        """Returnerer kort årsak hvis EventMgr har aktiv/ventende event (f.eks. ankomst-event), ellers None."""
        if self.hR is None or self.R is None or self.main is None or self.delta is None:
            return None
        try:
            got = struct.unpack("<Q", p.read(p.base + self.hR + (self.main + self.GOT_EVMGR - self.R), 8))[0]
            mgr = struct.unpack("<Q", p.read(p.base + self.hR + (got - self.R), 8))[0]
            if not (mgr and self.R <= mgr):
                return None
            hm = p.base + mgr - self.delta
            fl = struct.unpack("<I", p.read(hm + 0xB8, 4))[0]
            if fl & 0x801:
                return f"fl=0x{fl:x}"
            x68 = struct.unpack("<Q", p.read(hm + 0x68, 8))[0]
            if x68:
                return f"x68=0x{x68:x}"
            cnt = struct.unpack("<I", p.read(hm + 0x310, 4))[0]
            if cnt:
                return f"cnt={cnt}"
        except (OSError, TypeError, ValueError):
            return None
        return None

    SYNC_EVENT_SKIP_PREFIXES = (
        "Dm_SY_", "Demo_SY_", "Door", "Treasure", "ItemGet", "Warp",
        "Fade", "Save", "Title", "GameOver", "Sys_", "System_",
        "BancChange",   # v0.94.281: sone-bytte (f.eks. BancChangeGo_Market) – startet hos vennen ga evig lasteskjerm; FOLLOW/party_warp tar sonebytter
    )

    def read_active_event(self, p):
        """v0.94.245: Les aktivt cutscene/event-navn fra EventMgr + 0x68 -> +0x08 (0 game_call). Returnerer str eller None."""
        if p is None or self.hR is None or self.R is None or self.main is None or self.delta is None:
            return None
        try:
            got = struct.unpack("<Q", p.read(p.base + self.hR + (self.main + self.GOT_EVMGR - self.R), 8))[0]
            mgr = struct.unpack("<Q", p.read(p.base + self.hR + (got - self.R), 8))[0]
            if not (mgr and self.R <= mgr):
                return None
            x68 = struct.unpack("<Q", p.read(p.base + mgr - self.delta + 0x68, 8))[0]
            if not (self.delta < x68 < self.delta + p.size - 0x40):
                return None
            nptr = struct.unpack("<Q", p.read(p.base + x68 - self.delta + 0x08, 8))[0]
            if not (self.delta < nptr < self.delta + p.size - 0x80):
                return None
            raw = p.read(p.base + nptr - self.delta, 0x80)
            nul = raw.find(b"\x00")
            if nul <= 3:
                return None
            name = raw[:nul].decode("ascii", errors="ignore")
            if len(name) < 4 or not all(c.isalnum() or c == "_" for c in name):
                return None
            if name.startswith(self.SYNC_EVENT_SKIP_PREFIXES):
                return None
            return name
        except (OSError, TypeError, ValueError, struct.error):
            return None

    def start_event(self, p, ev_name):
        """v0.94.245: Start en cutscene/event via EventMgr::startEvent (F_EV_START) med 0 ekstra parametere."""
        if not ev_name or p is None or self.p_act is None or self.delta is None:
            return False
        if len(ev_name) > 63 or ev_name.startswith(self.SYNC_EVENT_SKIP_PREFIXES):
            return False
        if self.event_busy(p) is not None:
            return False
        with self._ev_lk:
            try:
                if getattr(self, "ev_arg", None) is None or self.h_evarg is None:
                    va = self.game_call(p, self.F_ALLOC, (0x10, 0x2000))
                    if not va:
                        return False
                    if self.game_call(p, self.F_EVARG_CTOR, (va,)) is None:
                        return False
                    h_ev = self._find_host_ptr(p, va, lambda o: struct.unpack("<Q", p.read(p.base + o + 8, 8))[0] == va + 0x18)
                    if h_ev is None:
                        return False
                    self.ev_arg, self.h_evarg = va, h_ev
                else:
                    if self.game_call(p, self.F_EVARG_CTOR, (self.ev_arg,)) is None:
                        return False
                arg, harg = self.ev_arg, p.base + self.h_evarg
                cap, arr, cnt = struct.unpack("<I4xQI", p.read(harg, 0x14))
                if arr != arg + 0x18 or cnt != 0 or cap < 1:
                    self.ev_arg = self.h_evarg = None
                    return False
                p_act, delta = self.p_act, self.delta
                if p_act is None or delta is None:
                    return False
                act_va = p_act + delta
                p.write(harg + 0x1958, struct.pack("<QI", act_va, struct.unpack("<I", p.read(p.base + p_act + 0x48, 4))[0]))
                nptr = struct.unpack("<Q", p.read(harg + 0x1A90, 8))[0]
                if not (arg <= nptr < arg + 0x1B20):
                    return False
                p.write(harg + (nptr - arg), ev_name.encode("ascii") + b"\0")
                got = struct.unpack("<Q", p.read(p.base + self.hR + (self.main + self.GOT_EVMGR - self.R), 8))[0]
                mgr = struct.unpack("<Q", p.read(p.base + self.hR + (got - self.R), 8))[0]
                r = self.game_call(p, self.F_EV_START, (mgr, arg))
                log(f"PadLink.start_event: {ev_name} -> {r}")
                return bool(r and r & 1)
            except (OSError, struct.error) as e:
                log(f"PadLink.start_event feil ({ev_name}): {e}")
                return False

    def change_banc(self, p, banc, start_pos=None, boot_event="Dm_SY_BancChangeArrive"):
        """Ekte sonebytte som en dør: start eventen Dm_SY_BancChangeGo med parameterne NextBanc/NextStartPos/… (se UTVIKLING.md 2026-11-12).
        Returnerer True når eventen er lagt i kø. Krever call_v1.pchtxt og at spillerens aktør er funnet."""
        start_pos = start_pos or self.START_POS.get(banc)
        if not banc or not start_pos or self.p_act is None or self.delta is None:
            log(f"PadLink.change_banc: mangler klar tilstand ({banc} p_act={self.p_act is not None} delta={self.delta is not None})")
            return False
        with self._ev_lk:
            try:
                if getattr(self, "ev_arg", None) is None or self.h_evarg is None:   # 0x2000 byte fra spillets heap, gjenbrukes hele økta
                    va = self.game_call(p, self.F_ALLOC, (0x10, 0x2000))
                    if not va:
                        log(f'PadLink.change_banc: allokering avvist for {banc}')
                        return False
                    ctor = self.game_call(p, self.F_EVARG_CTOR, (va,))
                    if ctor is None:
                        log(f'PadLink.change_banc: første ctor svarte ikke for {banc}')
                        return False
                    h_ev = self._find_host_ptr(p, va, lambda o: struct.unpack("<Q", p.read(p.base + o + 8, 8))[0] == va + 0x18)
                    if h_ev is None:
                        log(f"PadLink.change_banc: fant ikke vertsminne for ev_arg 0x{va:X}")
                        return False
                    self.ev_arg, self.h_evarg = va, h_ev
                else:
                    ctor = self.game_call(p, self.F_EVARG_CTOR, (self.ev_arg,))
                    if ctor is None:
                        err = getattr(self, '_last_call_err', None)
                        log(f'PadLink.change_banc: gjenbrukt ctor svarte ikke ({err}) for {banc}')
                        if err != 'tp_cooldown':
                            self._evarg_ctor_fails = getattr(self, '_evarg_ctor_fails', 0) + 1
                            if self._evarg_ctor_fails >= 2:
                                self.ev_arg = self.h_evarg = None
                                self._evarg_ctor_fails = 0
                        return False
                self._evarg_ctor_fails = 0
                arg, harg = self.ev_arg, p.base + self.h_evarg
                cap, arr, cnt = struct.unpack("<I4xQI", p.read(harg, 0x14))
                if arr != arg + 0x18 or cnt != 0 or cap < 5:           # feil vert-oversettelse eller uventet layout -> ikke rør noe
                    log(f"PadLink.change_banc: uventet arg-layout (kap {cap}, array 0x{arr:X}, antall {cnt})")
                    self.ev_arg = self.h_evarg = None
                    return False
                hs = p.base + self.hR + 0x400                             # verdistrenger i R+0x400.. (64 byte hver)
                params = (("NextBanc", 1, banc), ("NextStartPos", 1, start_pos), ("NextStartPosAir", 1, ""),
                          ("BootEventName", 1, boot_event), ("IsCheckAir", 4, 0))
                for k, (name, typ, val) in enumerate(params):
                    e = harg + 0x18 + k * 0xC8
                    nptr = struct.unpack("<Q", p.read(e + 8, 8))[0]
                    if not (arg <= nptr < arg + 0x1B20):
                        nptr = arg + 0x18 + k * 0xC8 + 0x14; p.write(e + 8, struct.pack("<QI", nptr, 0x80))
                    p.write(harg + (nptr - arg), name.encode() + b"\0")
                    p.write(e, struct.pack("<I", typ))
                    if typ == 1:
                        b = val.encode()[:63]; p.write(hs + k * 0x40, b + bytes(0x40 - len(b)))
                        p.write(e + 0x98, struct.pack("<Q", self.R + 0x400 + k * 0x40))
                    else:
                        p.write(e + 0x98, bytes([1 if val else 0]))
                p.write(harg + 0x10, struct.pack("<I", len(params)))
                p_act, delta = self.p_act, self.delta
                if p_act is None or delta is None:   # avbryt hvis pekeroppdagelsen startet på nytt under oppsettet
                    return False
                act_va = p_act + delta
                p.write(harg + 0x1958, struct.pack("<QI", act_va, struct.unpack("<I", p.read(p.base + p_act + 0x48, 4))[0]))
                nptr = struct.unpack("<Q", p.read(harg + 0x1A90, 8))[0]
                if not (arg <= nptr < arg + 0x1B20):
                    return False
                p.write(harg + (nptr - arg), b"Dm_SY_BancChangeGo\0")
                got = struct.unpack("<Q", p.read(p.base + self.hR + (self.main + self.GOT_EVMGR - self.R), 8))[0]
                mgr = struct.unpack("<Q", p.read(p.base + self.hR + (got - self.R), 8))[0]
                r = self.game_call(p, self.F_EV_START, (mgr, arg))
                log(f"PadLink.change_banc: {banc} @ {start_pos} -> {r}")
                ok = bool(r and r & 1)
                if ok:
                    self._tp_t = self._banc_since = time.time()
                return ok
            except OSError:
                return False

    def teleport_player(self, p, target_pos, target_rot=None):
        """Teleporterer spillerens egen Link (Link 1) til gitt 3D-posisjon (Co-op Party Teleport)."""
        p_act, p_x8 = self.p_act, self.p_x8
        if p_act is None or p_x8 is None or not target_pos:
            return False
        self._tp_t = self._banc_since = time.time()   # v0.55/0.56: rommet lastes etter flytting – ikke lag/slett/flytt aktører (spillet frøs ved Gohma)
        self._last_tp_done = time.time()               # v0.94.154: siste fullførte teleport (dobbeltsperre)
        try:
            tx, ty, tz = target_pos
            rot = target_rot if (target_rot and len(target_rot) == 9) else (1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0)
            mat3x4 = struct.pack("<12f",
                                 rot[0], rot[1], rot[2], tx,
                                 rot[3], rot[4], rot[5], ty,
                                 rot[6], rot[7], rot[8], tz)
            hx8 = p.base + p_x8
            p.write(hx8 + 0x1D0, mat3x4)
            p.write(hx8 + 0x208, struct.pack("<3f", 1.0, 1.0, 1.0))
            w = struct.unpack("<I", p.read(hx8 + 0x228, 4))[0]
            p.write(hx8 + 0x228, struct.pack("<I", w | 7))
            p.write(p.base + p_act + 0x31C, struct.pack("<3f", tx, ty, tz))
            log(f"PadLink: Party Teleport -> teleporterte egen Link til ({tx:.2f}, {ty:.2f}, {tz:.2f})")
            return True
        except OSError as e:
            log(f"PadLink: Party Teleport feil: {e}")
            return False

    def _worker(self, p):
        try:
            if self.hR is None:
                self.hR, self.R = self._find(p)
                if self.hR is None:
                    return
                self.main = self.R - self.R_OFF
                log(f"PadLink: R funnet guest+0x{self.hR:X} (gjest 0x{self.R:X}, main 0x{self.main:X})")
                fake = bytearray(0x200); struct.pack_into("<Q", fake, 0, self.R + 0x200)
                vt = bytearray(0x40); struct.pack_into("<Q", vt, 0x20, self.main + 0x19F0)
                p.write(p.base + self.hR, bytes(fake)); p.write(p.base + self.hR + 0x200, bytes(vt))
                p.write(p.base + self.hR + 0xEF8, struct.pack('<II', int(self.pvp_message_filter), 0))
                log(f'pvp-meldingssperre: {"på" if self.pvp_message_filter else "av"}')
            h = p.base + self.hR; t0 = time.time(); seen = {}
            # Vakt: den falske kontrolleren må alltid peke på vtable-en (ellers krasjer INP-kroken på main+0x574B44
            # med «Unmapped Read64 @ 0x20» så snart magien er på). Sett 2026-11-12 da R+0 var null.
            if struct.unpack("<Q", p.read(h + 0xA00, 8))[0] != self.R + 0x200:   # v0.83: botens falske kontroller (inp_v5) peker på samme vtable
                p.write(h + 0xA00, struct.pack("<Q", self.R + 0x200))
            if struct.unpack("<Q", p.read(h, 8))[0] != self.R + 0x200 or struct.unpack("<Q", p.read(h + 0x220, 8))[0] != self.main + 0x19F0:
                p.write(h, struct.pack("<Q", self.R + 0x200)); p.write(h + 0x220, struct.pack("<Q", self.main + 0x19F0))
                log("PadLink: skrev falsk kontroller/vtable på nytt (var ødelagt)")
            while time.time() - t0 < 0.25:
                d = p.read(h + 0x290, 0x20)
                for x in (struct.unpack_from("<Q", d, 0)[0], struct.unpack_from("<Q", d, 0x18)[0]):
                    if x:
                        seen[x] = seen.get(x, 0) + 1
            if any(p.read(h + 0x2C0, 0x20)):
                self.has_v4 = True

            # Valider eksisterende spiller og kopi i minnet
            p_valid = self._is_valid_x19(p, self.player) if self.player else False
            c_valid = self._is_valid_x19(p, self.copy, reset_delta=not p_valid) if self.copy else False

            if not p_valid and self.player is not None:
                log("PadLink: spiller x19 er borte (scenebytte)")
                self.player = None
                self.p_act = self.p_x8 = None
                self.scene_changed = True

            if not c_valid and self.copy is not None:
                log("PadLink: kopi x19 er borte – nullstiller kopi")
                self.copy = None
                self.c_act = self.c_x8 = self.c_x9 = None
                self._c_sv_cur = self._c_sv_max = None
                try:
                    p.write(h + 0x288, bytes(8))
                except OSError:
                    pass

            # Kun aktører som faktisk har gyldig vtable i minnet (unngå kopi som er under sletting)
            now_w = time.time()
            try:
                bot_x19 = struct.unpack("<Q", p.read(h + 0x2B0, 8))[0]   # v0.83: test-boten er verken spiller eller Link 2
            except OSError:
                bot_x19 = 0
            valid_seen = [x for x in seen if self._is_valid_x19(p, x, reset_delta=(self.delta is None)) and not (x == self._deleted_x19 and now_w < self._deleted_until)
                          and not (bot_x19 and x == bot_x19)]

            self._last_valid_seen = list(valid_seen)
            # Lagret spiller (R+0x2B8, skrives av modden) vinner – ellers kan en omstart forveksle spiller og gammel Link 2
            if self.player is None:
                try:
                    saved = struct.unpack("<Q", p.read(h + 0x2B8, 8))[0]
                except OSError:
                    saved = 0
                if saved and saved in valid_seen:
                    self.player = saved
                    prev_copy = struct.unpack("<Q", p.read(h + 0x288, 8))[0]
                    if prev_copy in valid_seen and prev_copy != saved:
                        self.copy = prev_copy; self.active = True; self._hidden = True
                        p.write(h + 0x280, struct.pack("<I", self.MAGIC))
                    log(f"PadLink: spiller fra R+0x2B8: 0x{self.player:X}" + (f", kopi 0x{self.copy:X}" if self.copy else ""))
            # Hvis spilleren ikke er satt:
            if self.player is None:
                if len(valid_seen) == 1:
                    self.player = valid_seen[0]
                    log(f"PadLink: spiller x19 funnet: 0x{self.player:X}")
                elif len(valid_seen) >= 2:
                    prev_copy = struct.unpack("<Q", p.read(h + 0x288, 8))[0]
                    if prev_copy in valid_seen:
                        self.copy = prev_copy
                        self.player = next(x for x in valid_seen if x != prev_copy)
                        self.active = True
                        p.write(h + 0x280, struct.pack("<I", self.MAGIC))
                        log(f"PadLink: gjenopptok fra R – spiller 0x{self.player:X}, kopi 0x{self.copy:X}")
                        self._hidden = True   # kan være skjult fra en tidligere økt – tving «vis» ved neste tilkobling
                    else:
                        p_cand = None
                        if self._cam_off is not None:
                            best_dot = -1.0
                            for cand in valid_seen:
                                try:
                                    a = self._u64(p, cand + 0x18)
                                    apos = p.f32(a - self.delta + 0x31C, 3)
                                    q = cam_quality(p, self._cam_off, apos)
                                    if q and q[1] > best_dot:
                                        best_dot = q[1]
                                        p_cand = cand
                                except Exception:
                                    pass
                        if p_cand:
                            self.player = p_cand
                            cands = [x for x in valid_seen if x != p_cand]
                            self.copy = cands[0] if cands else None
                            log(f"PadLink: identifisert via kamera – spiller 0x{self.player:X}, kopi 0x{self.copy:X}")
                            if self.copy:
                                p.write(h + 0x288, struct.pack("<Q", self.copy))
                                p.write(h + 0x280, struct.pack("<I", self.MAGIC))
                                self.active = True
                        else:
                            self.player = valid_seen[0]
                            log(f"PadLink: valgte spiller 0x{self.player:X}")

            if self.player is not None:
                try:
                    if struct.unpack("<Q", p.read(h + 0x2B8, 8))[0] != self.player:
                        p.write(h + 0x2B8, struct.pack("<Q", self.player))
                except OSError:
                    pass
            # Hvis spiller er satt og gyldig: self.player endres ALDRI!
            # Hvis kopien mangler: finn kopi blant andre gyldige aktører
            if self.player is not None and self.copy is None and time.time() - self._banc_since > 4.0:   # ikke midt i sonelasting
                new = [x for x in valid_seen if x != self.player and x not in getattr(self, "_zone_dead", ())]
                if new:
                    self.copy = new[0]; self._l2_tries = 0
                    log(f"PadLink: kopi (spiller 2) x19 registrert: 0x{self.copy:X}")
                    p.write(h + 0x288, struct.pack("<Q", self.copy))
                    p.write(h + 0x280, struct.pack("<I", self.MAGIC))
                    self.active = True

            # Sikkerhet: player og copy må ALDRI være samme x19!
            if self.copy and self.player and self.copy == self.player:
                log("PadLink SIKKERHET: copy var lik player! Nullstiller kopi.")
                self.copy = None
                p.write(h + 0x288, bytes(8))

            self._resolve_actors(p)
            cur_pos = self.my_apos(p)
            if cur_pos:
                self.last_pos = cur_pos
        except OSError as e:
            if self.hR is not None:
                log(f"PadLink: lesefeil ({e}) – søker R på nytt")
            self.hR = None
        except Exception as e:
            log(f"PadLink FEIL: {e!r}")
        finally:
            if self.hR is None and not getattr(self, "_nf_logged", False):
                self._nf_logged = True; log("PadLink: R ikke funnet ennå (er inp_v4 lastet?)")
            self.busy = False


    SPAWN_OFF = 0x800          # R+0x800: navn, navn-peker og spawn-arg (statisk, leses av ActorMgr-arbeidertråden etter retur)

    def _spawn_link2(self, p):
        """Lag Link 2 (Player_Child) via CALL v1 på egen stack; faller tilbake til GDB (gcall) hvis patchen er for gammel."""
        if (self.copy is not None or getattr(self, "_spawning", False) or getattr(self, "_tun_busy", False)
                or time.time() < getattr(self, "_tp_t", 0) + CALL_TELEPORT_COOLDOWN):
            return
        pos = self.my_apos(p)
        if not pos or self.hR is None or self.main is None:
            return
        self._spawning = True
        try:
            if getattr(self, "spawn_stack", None) is None:
                va = self.game_call(p, self.F_ALLOC, (0x10, 0x10000))
                if not va:
                    raise RuntimeError("fikk ikke stack fra spillet")
                self.spawn_stack = (va + 0x10000 - 0x100) & ~0xF
            sx, sy, sz = pos[0] + 1.5, pos[1] + 3.0, pos[2]
            R = self.R; h = p.base + self.hR + self.SPAWN_OFF; base = R + self.SPAWN_OFF
            arg = bytearray(0x100)
            struct.pack_into("<3f", arg, 0, sx, sy, sz)
            struct.pack_into("<9f", arg, 0x0C, 1, 0, 0, 0, 1, 0, 0, 0, 1)
            struct.pack_into("<3f", arg, 0x30, 1, 1, 1)
            arg[0x98] = 3
            struct.pack_into("<Q", arg, 0x40, base + 0x30)   # streng-peker som spawn-tilbakekallet leser (main+0x3ADE06C): må peke på "" (null -> krasj)
            nm2 = getattr(self, 'link2_actor', 'Player_Child')
            self._l2_tries = getattr(self, '_l2_tries', 0) + 1
            if nm2 != 'Player_Child' and self._l2_tries > 4:   # v0.66: fargeaktøren ble ikke laget (mangler mod?) -> vanlig Link
                log(f'PadLink: {nm2} ble ikke laget - bruker Player_Child'); nm2 = self.link2_actor = 'Player_Child'
            log(f'PadLink: Link 2-aktør {nm2}')
            p.write(h, (nm2.encode() + b"\0").ljust(0x40, b"\0") + struct.pack("<Q", base) + bytes(0xB8) + bytes(arg))   # navn @+0, navn** @+0x40, arg @+0x100
            got = struct.unpack("<Q", p.read(p.base + self.hR + (self.main + self.GOT_ACTMGR - R), 8))[0]
            mgr = struct.unpack("<Q", p.read(p.base + self.hR + (got - R), 8))[0]
            log(f"PadLink: lager Link 2 via CALL v1 ved ({sx:.1f}, {sy:.1f}, {sz:.1f}) …")
            res = self.game_call(p, self.F_ACT_CREATE, (mgr, base + 0x40, base + 0x100, 0, 1, 0, 0, 0), timeout=3.0, stack_top=self.spawn_stack)
            log(f"PadLink: requestCreateActor -> {res}")
            if res is not None:
                self._last_spawn_try = time.time() + 12.0   # registrering tar ~5 s – ikke lag en ekstra Link 2 imens
                return
            log("PadLink: CALL v1-spawn svarte ikke – prøver GDB")
        except Exception as e:  # noqa: BLE001
            self._spawn_failures = getattr(self, '_spawn_failures', 0) + 1
            log(f"PadLink: CALL v1-spawn feilet ({e!r}) – ingen automatisk GDB-fallback")
            return
        finally:
            self._spawning = False
        self._spawn_failures = getattr(self, '_spawn_failures', 0) + 1
        log("PadLink: automatisk Link 2-spawn stoppes etter mislykket forsøk")

    def spawn_player_child(self, p, pos):
        """v0.84: lag en ekstra Player_Child (test-boten) på samme måte som Link 2 (CALL v1, egen stack, data i R+SPAWN_OFF)."""
        if self.hR is None or self.main is None:
            return None
        if getattr(self, "spawn_stack", None) is None:
            va = self.game_call(p, self.F_ALLOC, (0x10, 0x10000))
            if not va:
                return None
            self.spawn_stack = (va + 0x10000 - 0x100) & ~0xF
        R = self.R; h = p.base + self.hR + self.SPAWN_OFF; base = R + self.SPAWN_OFF
        arg = bytearray(0x100)
        struct.pack_into("<3f", arg, 0, *pos)
        struct.pack_into("<9f", arg, 0x0C, 1, 0, 0, 0, 1, 0, 0, 0, 1)
        struct.pack_into("<3f", arg, 0x30, 1, 1, 1)
        arg[0x98] = 3
        struct.pack_into("<Q", arg, 0x40, base + 0x30)
        p.write(h, b"Player_Child\0".ljust(0x40, b"\0") + struct.pack("<Q", base) + bytes(0xB8) + bytes(arg))
        got = struct.unpack("<Q", p.read(p.base + self.hR + (self.main + self.GOT_ACTMGR - R), 8))[0]
        mgr = struct.unpack("<Q", p.read(p.base + self.hR + (got - R), 8))[0]
        return self.game_call(p, self.F_ACT_CREATE, (mgr, base + 0x40, base + 0x100, 0, 1, 0, 0, 0), timeout=3.0, stack_top=self.spawn_stack)

    def _spawn_link2_gdb(self, p):
        """Reserve: ActorMgr::requestCreateActor('Player_Child', ...) via GDB (gcall)."""
        global gcall, Gdb
        if self.copy is not None:
            return  # Kopi finnes allerede, aldri spawn flere!
        if getattr(self, "_spawning", False) or getattr(self, "disable_link2", False):
            return
        self._spawning = True
        try:
            if gcall is None or Gdb is None:
                for _p in (os.path.dirname(os.path.abspath(__file__)), os.getcwd()):
                    if _p not in sys.path:
                        sys.path.insert(0, _p)
                import gcall
                from gdbc import Gdb
            player_pos = self.my_apos(p)
            if not player_pos:
                return
            sx, sy, sz = round(player_pos[0] + 1.5, 2), round(player_pos[1] + 3.0, 2), round(player_pos[2], 2)
            log(f"PadLink: Auto-respawn av Link 2 ved ({sx}, {sy}, {sz}) ...")

            def setup_spawn(g, main_va, base):
                mgr = g.u64(g.u64(main_va + 0x4C7F3E0))
                g.write(base + 0x400, b"Player_Child\0")
                g.write(base + 0x380, struct.pack("<Q", base + 0x400))
                arg = bytearray(0x100)
                struct.pack_into("<3f", arg, 0, sx, sy, sz)
                struct.pack_into("<9f", arg, 0x0C, 1, 0, 0, 0, 1, 0, 0, 0, 1)
                struct.pack_into("<3f", arg, 0x30, 1, 1, 1)
                arg[0x98] = 3
                g.write(base + 0x200, bytes(arg))
                return [mgr, base + 0x380, base + 0x200, 0, 1, 0, 0, 0], None

            res, g2, _, _, _ = gcall.call(0x372A70, setup_spawn, stop_off=0x744040, stop_timeout=15)
            gcall.finish(g2)
            log(f"PadLink: Auto-respawn fullført (x0={res})")
        except Exception as e:
            log(f"PadLink: Auto-respawn feilet ({e})")
        finally:
            self._spawning = False

    def _delete_link2(self, p):
        """Sletter Link 2 for ekte via Actor::requestDelete (CALL v1, 0xA6490) når vennen kobler fra."""
        if self.c_act is None or self.delta is None or getattr(self, "_deleting", False):
            return
        self._deleting = True
        self._last_del_try = time.time()
        c_act_va = self.c_act + self.delta

        def run():
            try:
                res = self.game_call(p, self.F_ACT_DELETE, (c_act_va, 0), timeout=2.0)
                if res is not None:
                    self._deleted_x19 = self.copy
                    self._deleted_until = time.time() + 2.5
                    self.copy = None
                    self.c_act = self.c_x8 = self.c_x9 = None
                    self._c_sv_cur = self._c_sv_max = None
                    self._hidden = False
                    if self.hR is not None:
                        try:
                            p.write(p.base + self.hR + 0x288, bytes(8))
                        except OSError:
                            pass
                    log(f"PadLink: Link 2 slettet (despawnet, x0={res})")
            except OSError:
                pass
            finally:
                self._deleting = False

        threading.Thread(target=run, daemon=True).start()

    def tick(self, p, now, alive=False):
        if p is None or self.busy:
            return
        if now - self.last_try >= 2:
            self.last_try = now; self.busy = True
            threading.Thread(target=self._worker, args=(p,), daemon=True).start()
        # Watchdog auto-respawn: KUN hvis venn er tilkoblet, kopien mangler, og vi ikke har spawnet nylig
        self.banc_tick(p, now)
        # v0.67: Link 2 får tunika i vennens farge: rustningen Armor_Child_Tunic_<L> (romfs-mod OoT_MP_Tunic) tas på som
        # overdel (kind 8) og festes ben for ben; bare tunikaen vises på den, og Link 2 sin egen tunika skjules.
        fl = getattr(self, 'friend_look', None)
        if (fl in TUNIC_LETTER and self.copy is not None and self.c_act is not None and alive
                and not getattr(self, 'bot_control', False) and not getattr(self, '_spawning', False)
                and getattr(self, '_tun_done', None) != (self.copy, fl) and getattr(self, '_tun_fail', None) != (self.copy, fl)
                and now - getattr(self, '_tun_try', 0) > 5.0
                and not getattr(self, '_tun_busy', False) and now - getattr(self, '_tp_t', 0) > 8.0):
            self._tun_try = now; self._tun_busy = True
            threading.Thread(target=self._wear_tunic, args=(p, self.copy, self.c_act, fl), daemon=True).start()
        # v0.94.34: vakt – skjul tunika-deler i feil farge som sitter på en Link (to farger samtidig)
        if (now - getattr(self, '_tun_dup_t', 0) > 5.0 and not getattr(self, '_tun_dup_busy', False)
                and not getattr(self, '_tun_busy', False) and not getattr(self, '_spawning', False)
                and self.p_act is not None and not getattr(self, 'bot_control', False)
                and now >= getattr(self, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN):
            self._tun_dup_t = now; self._tun_dup_busy = True
            want = {}
            if self.c_act is not None and getattr(self, 'friend_look', None) in TUNIC_LETTER:
                want[self.c_act] = f"Armor_Child_Tunic_{TUNIC_LETTER[self.friend_look]}"
            if getattr(self, 'my_look', None) in TUNIC_LETTER:
                want[self.p_act] = f"Armor_Child_Tunic_{TUNIC_LETTER[self.my_look]}"
            def _dup(want=want):
                try:
                    # v0.94.304: før tvang vi et fullt aktørsøk (~1,5 GB lest) hvert 5. s = ~35 % av moddens CPU.
                    # Gjenbruk siste fulle liste (< 30 s, samme sone), ellers fullt søk høyst hvert 30. s.
                    lf_ = getattr(self, '_last_full_diag', None)
                    if lf_ and time.time() - lf_[0] < 30 and lf_[1] == self.cur_banc:
                        dg = lf_[2]
                    elif time.time() - getattr(self, '_tun_dup_full_t', 0) >= 30:
                        self._tun_dup_full_t = time.time()
                        dg = {}; self._scan_full_t = 0; self._scan_actors_raw(p, dg)
                    else:
                        return
                    hid = self.__dict__.setdefault('_tun_dup_hidden', set())
                    for a_, nm_ in dg.items():
                        if not nm_.startswith('Armor_Child_Tunic_') or a_ in hid:
                            continue
                        try:
                            q_ = p.f32(a_ + 0x31C, 3)
                        except OSError:
                            continue
                        for act_, wn in want.items():
                            if nm_ != wn and math.dist(q_, p.f32(act_ + 0x31C, 3)) < 0.3:
                                for m in self.TUNIC_SHOW + self.TUNIC_HIDE:
                                    self.set_material_visible(p, a_, m, False)
                                hid.add(a_); log(f'tunika: skjulte feil farge {nm_} på en Link')
                except Exception as e:  # noqa: BLE001
                    log(f'tunika: dup-feil {e!r}')
                finally:
                    self._tun_dup_busy = False
            threading.Thread(target=_dup, daemon=True).start()
        # v0.94.32: vakt – har tunika-delen falt av Linken (spillet tar av utstyr på ekte spillere), vis vanlig tunika og ta på igjen
        if (now - getattr(self, '_tun_watch_t', 0) > 3.0 and not getattr(self, '_tun_busy', False)
                and not getattr(self, '_spawning', False) and not getattr(self, '_tun_watch_busy', False)
                and now >= getattr(self, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN):
            self._tun_watch_t = now
            watch_items = list(self.__dict__.get('_tun_worn', {}).items())
            if watch_items:
                self._tun_watch_busy = True
                def _watch(watch_items=watch_items):
                    try:
                        for who_, (arm_, act_) in watch_items:
                            if getattr(self, '_spawning', False) or getattr(self, '_tun_busy', False):
                                break
                            try:
                                off = math.dist(p.f32(arm_ + 0x31C, 3), p.f32(act_ + 0x31C, 3)) if self.actor_alive(p, arm_) else 99.0
                            except OSError:
                                off = 99.0
                            if off <= 0.6:   # v0.94.35: sitter på – sørg for at Linkens egen tunika er skjult (ellers to farger)
                                for m in self.TUNIC_SHOW:
                                    self.set_material_visible(p, act_, m, False)
                                for m in self.BODY_SHOW:
                                    self.set_material_visible(p, act_, m, True)
                            else:
                                # v0.94.299: etter sonebytte peker _tun_worn på det gamle plagget (120 m unna), men Linken har
                                # fortsatt et farge-plagg på. Da skal grunn-tunikaen IKKE vises (ellers to farger samtidig).
                                try:
                                    dg_ = {}; self._scan_full_t = 0; self._scan_actors_raw(p, dg_)
                                    lp_ = p.f32(act_ + 0x31C, 3)
                                    new_arm = next((a_ for a_, nm_ in dg_.items() if nm_.startswith('Armor_Child_Tunic_')
                                                    and math.dist(p.f32(a_ + 0x31C, 3), lp_) < 0.6), None)
                                except OSError:
                                    new_arm = None
                                if new_arm is not None:
                                    self.__dict__.setdefault('_tun_worn', {})[who_] = (new_arm, act_)
                                    for m in self.TUNIC_SHOW:
                                        self.set_material_visible(p, new_arm, m, True)
                                        self.set_material_visible(p, act_, m, False)
                                    log(f'tunika: {"Link 2" if who_ == "l2" else "min Link"} har fortsatt farge-plagg ({dg_[new_arm]}) etter sonebytte – grunn-tunikaen forblir skjult')
                                    continue
                                self.__dict__.get('_tun_worn', {}).pop(who_, None)
                                for m in self.TUNIC_SHOW + ('Mt_Cloth_Pants',):
                                    self.set_material_visible(p, act_, m, True)
                                if who_ == 'l2':   # v0.94.265: egen Link tas IKKE på igjen automatisk (samme stykke to ganger -> frys)
                                    self.__dict__.pop('_tun_done', None)
                                self.__dict__.pop('_tun_fail' if who_ == 'l2' else '_tun_fail_me', None)
                                log(f'tunika: delen falt av {"Link 2" if who_ == "l2" else "min Link"} ({off:.1f} m) – viser vanlig tunika og tar på igjen')
                    except Exception as e:  # noqa: BLE001
                        log(f'tunika: watch-feil {e!r}')
                    finally:
                        self._tun_watch_busy = False
                threading.Thread(target=_watch, daemon=True).start()
        # v0.94.222: F_EQUIP (0x2DF7B20) i _wear_tunic frøs GAMER2 i Story-modus; bare nødvendig ved PvP-lagbytte (Story bruker romfs-tunika).
        ml = getattr(self, 'my_look', None)
        # v0.94.265: egen farge live igjen – men equip KUN ved fargebytte, aldri samme farge to ganger på samme Link
        # (frysen i v0.94.222 kom trolig av at vakta tok på samme stykke igjen; daurosk: equip bare når navnet avviker).
        _tried = self.__dict__.setdefault('_own_tun_tried', {})   # (spiller, farge) -> antall forsøk (1 = last pakken, 2 = ta på)
        if (ml in TUNIC_LETTER and self.player is not None and self.p_act is not None
                and _tried.get((self.player, ml), 0) < 20   # v0.94.313: forsøk før F_EQUIP er gratis; F_EQUIP kalles maks én gang (done/fail)
                and getattr(self, '_tun_done_me', None) != (self.player, ml) and getattr(self, '_tun_fail_me', None) != (self.player, ml)
                and now - getattr(self, '_tun_try', 0) > 5.0
                and not getattr(self, '_tun_busy', False) and not getattr(self, '_spawning', False)
                and now - getattr(self, '_tp_t', 0) > 8.0 and self._zone_ready(p, now)):
            self._tun_try = now; self._tun_busy = True; _tried[(self.player, ml)] = _tried.get((self.player, ml), 0) + 1
            threading.Thread(target=self._wear_tunic, args=(p, self.player, self.p_act, ml, 'me'), daemon=True).start()
        if alive and self._zone_ready(p, now):
            threading.Thread(target=self._cleanup_orphans, args=(p, now), daemon=True).start() if now - getattr(self, "_orph_t", 0) >= 5.0 else None
        if not alive:
            self._last_spawn_try = 0
        cross = (not self.friend_banc or not self.cur_banc or self.friend_banc != self.cur_banc)   # ukjent sone = ingen Link 2 ennå   # vennen er i en annen sone -> ingen Link 2 her
        if alive and not cross and not getattr(self, 'suppress_link2', False) and self._pending_tp is None and self.copy is None and self.p_act is not None and not getattr(self, "_spawning", False) and not getattr(self, "_tun_busy", False) and getattr(self, '_spawn_failures', 0) < 2 and now >= max(getattr(self, "_tp_t", 0), getattr(self, "_friend_tp_t", 0)) + CALL_TELEPORT_COOLDOWN and self._zone_ready(p, now) and not (getattr(self, 'warp_banc', None) and self.warp_banc != self.cur_banc and now - self.warp_t < 25):   # vent til sonen er ferdig lastet
            if now - getattr(self, "_last_spawn_try", 0) > 3.0:   # 1. forsøk straks ved tilkobling, ellers hvert 3. s
                self._last_spawn_try = now
                threading.Thread(target=self._spawn_link2, args=(p,), daemon=True).start()

    def my_pad(self, p):
        """Egen ekte kontroller (kopiert av patchen) som hex – sendes til vennen."""
        if self.hR is None:
            return None
        if not getattr(self, '_btn_thr', None):
            self._btn_acc = 0; self._btn_p = p
            def _sample():
                while True:
                    time.sleep(0.004)   # 250 Hz: fanger korte trykk som faller mellom to pakker
                    try:
                        q = self._btn_p
                        if q is not None and self.hR is not None:
                            b = struct.unpack('<I', q.read(q.base + self.hR + 0x2C8, 4))[0]
                            self._btn_acc |= b
                            if b and b != getattr(self, '_btn_last', 0):
                                hist = self.__dict__.setdefault('_btn_hist', [])
                                hist.append((time.time(), b & ~getattr(self, '_btn_last', 0))); del hist[:-20]
                            self._btn_last = b
                    except Exception:  # noqa: BLE001
                        pass
            self._btn_thr = threading.Thread(target=_sample, daemon=True); self._btn_thr.start()
        self._btn_p = p
        try:
            raw = bytearray(p.read(p.base + self.hR + 0x2C0, 0x20))
            cur = struct.unpack_from('<I', raw, 8)[0]
            allb = cur | self._btn_acc
            newb = allb & ~getattr(self, '_btn_prev_pkt', 0)
            if newb:
                hist = self.__dict__.setdefault('_btn_hist', [])
                hist.append((time.time(), newb)); del hist[:-20]
            self._btn_prev_pkt = cur
            struct.pack_into('<I', raw, 8, cur | self._btn_acc)   # trykk som skjedde siden forrige pakke tas med
            self._btn_acc = 0
            return raw.hex()
        except OSError:
            return None

    def _zone_ready(self, p, now):
        """Ny sone ferdig lastet: minst 4 s siden bytte, og egen Link har flyttet seg > 3 m fra posisjonen ved byttet (maks 15 s ventetid)."""
        age = now - self._banc_since
        if age < 4.0:
            return False
        zp = getattr(self, "_zone_pos", None)
        if not zp or age > 15.0:
            return True
        cp = self.my_apos(p)
        return bool(cp) and math.dist(cp, zp) > 3.0

    def _cleanup_orphans(self, p, now):
        """Slett ekstra Link 2-er (verken spiller eller kopi), f.eks. laget midt i sonelasting – de faller gjennom bakken i en løkke."""
        if now - getattr(self, "_orph_t", 0) < 5.0 or self.player is None or self.copy is None or self.delta is None:
            return
        self._orph_t = now
        done = self.__dict__.setdefault("_orph_done", set())
        try:
            bot = struct.unpack("<Q", p.read(p.base + self.hR + 0x2B0, 8))[0]   # v0.83: test-boten (inp_v5) slettes ikke
        except OSError:
            bot = 0
        for x in getattr(self, "_last_valid_seen", []):
            if x in (self.player, self.copy) or x in done or (bot and x == bot):
                continue
            done.add(x)
            try:
                a = self._u64(p, x + 0x18)
                r = self.game_call(p, self.F_ACT_DELETE, (a, 0), timeout=2.0)
                log(f"PadLink: slettet ekstra Link 2 0x{x:X} -> {r}")
            except Exception as e:  # noqa: BLE001
                log(f"PadLink: kunne ikke slette ekstra Link 2 0x{x:X}: {e!r}")

    def my_apos(self, p):
        """Spillerens eksakte fot-posisjon fra player_actor+0x31C (hvis kjent)."""
        p_act = self.p_act
        if p_act is None:
            return None
        try:
            pos = p.f32(p_act + 0x31C, 3)
            if all(math.isfinite(v) and abs(v) < 1e5 for v in pos) and abs(pos[0]) + abs(pos[1]) + abs(pos[2]) > 1.0:
                return list(pos)
        except OSError:
            pass
        return None

    def my_arot(self, p):
        """Spillerens 3x3 rotasjonsmatrise fra player_actor+0x328 (9 floats)."""
        p_act = self.p_act
        if p_act is None:
            return None
        try:
            rot = p.f32(p_act + 0x328, 9)
            if all(math.isfinite(v) and abs(v) <= 1.05 for v in rot):
                return list(rot)
        except OSError:
            pass
        return None

    def my_cam_angle(self, p, cam_off=None):
        """Egen kameravinkel i verden: bruker først levende kameramatrise (oppdateres også når man står stille!),
        med spillets interne (s13 - s9) fra x19 som reserve."""
        if cam_off is not None:
            try:
                _r, _u, f, _eye = read_cam(p, cam_off)
                if math.hypot(f[0], f[2]) > 1e-4 and all(math.isfinite(v) for v in f):
                    return float(math.atan2(f[0], f[2]))
            except OSError:
                pass
        h = self.p_x19_h if self.p_x19_h is not None else self.c_x19_h
        if h is None:
            return None
        try:
            s9, s13 = p.f32(h + 0x74EC, 2)
            if math.isfinite(s9) and math.isfinite(s13):
                return float(s13 - s9)
        except OSError:
            pass
        return None

    def apply(self, p, pad_hex, friend_cam_a=None, my_cam_a=None, target_pos=None, target_rot=None, alive=True, cam_off=None, hearts=None):
        """Oppdater mål-tilstand for 120 Hz-tråden (og start tråden ved behov)."""
        with self._lk:
            self._p = p
            self._cam_off = cam_off
            self._alive = bool(alive)
            self._pad_hex = pad_hex if alive else None
            self._f_cam_a = friend_cam_a if alive else None
            self._my_cam_a = my_cam_a
            if alive and target_pos:
                self._t_pos = list(target_pos)
            elif not alive:
                self._t_pos = None
            if alive and target_rot:
                self._t_rot = list(target_rot)
            elif not alive:
                self._t_rot = None
            self._f_hearts = hearts if (alive and hearts) else None
        if self._thr is None:
            self._thr = threading.Thread(target=self._loop, daemon=True)
            self._thr.start()

    def _set_visible(self, p, visible, snap_pos=None, snap_rot=None):
        """Drop-in / Drop-out: skjul Link 2 på stedet (skala 0) ved frakobling, og vis ham (skala 1) ved tilkobling."""
        if self.c_act is None or self.c_x8 is None:
            return
        try:
            s = 1.0 if visible else 0.0
            s_bytes = struct.pack("<3f", s, s, s)
            p.write(p.base + self.c_act + 0x34C, s_bytes)
            hx8 = p.base + self.c_x8
            p.write(hx8 + 0x208, s_bytes)
            if not visible:   # gjem Link 2 ved min egen Link – ikke ved en dør (ga «Cannot exit right now» i bossrom)
                mp_ = self.my_apos(p)
                snap_pos = [mp_[0], mp_[1] + 3.0, mp_[2]] if mp_ else snap_pos   # 3 m over hodet ditt, så han ikke dytter deg
            cx, cy, cz = snap_pos if snap_pos else p.f32(self.c_act + 0x31C, 3)
            if visible:
                rot = snap_rot if (snap_rot and len(snap_rot) == 9) else (1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0)
            else:
                rot = (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
            mat3x4 = struct.pack("<12f",
                                 rot[0], rot[1], rot[2], cx,
                                 rot[3], rot[4], rot[5], cy,
                                 rot[6], rot[7], rot[8], cz)
            p.write(hx8 + 0x1D0, mat3x4)
            w = struct.unpack("<I", p.read(hx8 + 0x228, 4))[0]
            p.write(hx8 + 0x228, struct.pack("<I", w | 7))
            if self.c_x9 is not None:
                hx9 = p.base + self.c_x9
                b = p.read(hx9 + 0x1F2, 1)[0]
                p.write(hx9 + 0x1F2, bytes([b | 0x80]))
            if self._hidden != (not visible):
                self._hidden = not visible
                log(f"PadLink: Link 2 {'skjult (frakoblet)' if not visible else 'synlig igjen (tilkoblet)'}")
        except OSError:
            pass

    def _player_sv(self, p):
        """(vert-offset liv, vert-offset maks) for VÅR Link sin SaveVar (spiller-aktør − 0x1F40 + 0x1C10/0x1C18)."""
        if self.player is None or self.delta is None:
            return None, None
        if getattr(self, '_p_sv_for', None) != self.player:
            res = []
            for rel in (0x1C10, 0x1C18):
                sv = self._u64(p, self.player - 0x1F40 + rel)
                res.append(sv - self.delta + 0x8 if sv and self._u64(p, sv) == self.main + self.SAVEVAR_VT else None)
            self._p_sv, self._p_sv_for = tuple(res), self.player
        return self._p_sv

    def _sync_copy_health(self, p, cur_q, max_q):
        """Synk Link 2 sin egen SaveVar-helse så den ikke synker til 0 og gir falsk skadepose/rød blinking."""
        now = time.time()
        if now - self._last_hp_sync < 0.2:
            return
        self._last_hp_sync = now
        try:
            # Spillet gir helbredelse fra hjerter til Link 2 (begge er «spillere»). Øker kopiens liv utover det vi skrev,
            # gis økningen til vår egen Link i stedet (ellers forsvinner den når vi skriver vennens liv tilbake).
            lw = getattr(self, '_c_hp_written', None)
            if self._c_sv_cur is not None and lw is not None:
                now_c = struct.unpack("<I", p.read(p.base + self._c_sv_cur, 4))[0]
                if lw < now_c <= lw + 80:
                    pc, pm = self._player_sv(p)
                    if pc is not None:
                        hp = struct.unpack("<I", p.read(p.base + pc, 4))[0]
                        mx = struct.unpack("<I", p.read(p.base + pm, 4))[0] if pm is not None else 80
                        new = min(hp + (now_c - lw), mx)
                        if new != hp:
                            p.write(p.base + pc, struct.pack("<I", new))
                            log(f"PadLink: hjerte plukket av Link 2 – ga +{new - hp} til egen Link ({hp} -> {new})")
            # Fiende slo Link 2 (vennens dukke) her: liv sank under det vi skrev -> send skaden til vennen (felt «l2d»)
            if self._c_sv_cur is not None and lw is not None:
                now_c2 = struct.unpack("<I", p.read(p.base + self._c_sv_cur, 4))[0]
                if now_c2 < lw and lw - now_c2 <= 40:
                    self.l2_dmg_total = getattr(self, 'l2_dmg_total', 0) + (lw - now_c2)
                    log(f"PadLink: Link 2 ble truffet her (-{lw - now_c2} kvartaler) – sendes til vennen (sum {self.l2_dmg_total})")
            self._c_hp_written = cur_q
            for off, target in ((self._c_sv_cur, cur_q), (self._c_sv_max, max_q)):
                if off is not None and target is not None:
                    cur = struct.unpack("<I", p.read(p.base + off, 4))[0]
                    if cur != target:
                        p.write(p.base + off, struct.pack("<I", target))
        except OSError:
            pass

    def _loop(self):
        while True:
            time.sleep(1 / 120)
            try:
                with self._lk:
                    p = self._p
                    cam_off = self._cam_off
                    alive = self._alive
                    pad_hex = self._pad_hex
                    friend_cam_a = self._f_cam_a
                    my_cam_a = self._my_cam_a
                    target_pos = self._t_pos
                    target_rot = self._t_rot
                    f_hearts = self._f_hearts
                if p is None or self.hR is None or not self.active:
                    continue
                if getattr(self, 'bot_control', False):
                    # Spillerboten eier denne instansen midlertidig; ingen nettverksdukke skal overskrive den.
                    continue
                if not alive:
                    # Nullstill kontroller og hold Link 2 skjult på stedet (drop-out)
                    h = p.base + self.hR
                    p.write(h + 0x8, bytes(8)); p.write(h + 0x114, bytes(4)); p.write(h + 0x120, bytes(16))
                    if struct.unpack("<I", p.read(h + 0x280, 4))[0] != self.MAGIC:
                        p.write(h + 0x280, struct.pack("<I", self.MAGIC))
                    self._set_visible(p, False)
                    self._sync_copy_health(p, 12, 16)
                    # IKKE _delete_link2 her: requestDelete fjerner ikke Player_Child helt (vtable består i minutter),
                    # aktøren blir en «zombie» som flyter/er usynlig når den gjenbrukes. Skjul i stedet, vis ved tilkobling.
                    continue
                if self._hidden:
                    self._set_visible(p, True, target_pos, target_rot)
                # Les fersk egen kameravinkel i 120 Hz-løkken for umiddelbar respons når man snur kameraet
                live_cam_a = self.my_cam_angle(p, cam_off)
                if live_cam_a is not None:
                    my_cam_a = live_cam_a
                raw = bytes.fromhex(pad_hex) if pad_hex else bytes(0x20)
                if len(raw) != 0x20:
                    raw = bytes(0x20)
                d = bytearray(raw)
                sx, sy = struct.unpack_from("<2f", d, 0x10)
                smag = math.hypot(sx, sy) if (math.isfinite(sx) and math.isfinite(sy)) else 0.0
                if smag > 1e-3 and friend_cam_a is not None and my_cam_a is not None:
                    s9_m = math.atan2(-sx, sy) + (friend_cam_a - my_cam_a)
                    sx_n = -smag * math.sin(s9_m)
                    sy_n = smag * math.cos(s9_m)
                    struct.pack_into("<2f", d, 0x10, sx_n, sy_n)
                # Nullstill alltid høyre stikke (+0x128, +0x12C) på Link 2 så den aldri påvirker kameraet
                struct.pack_into("<2f", d, 0x18, 0.0, 0.0)
                if not getattr(self, 'share_interact', True):
                    d[:] = mask_puppet_pad(bytes(d), False)
                h = p.base + self.hR
                p.write(h + 0x8, bytes(d[0:8])); p.write(h + 0x114, bytes(d[8:12])); p.write(h + 0x120, bytes(d[0x10:0x20]))
                if struct.unpack("<I", p.read(h + 0x280, 4))[0] != self.MAGIC:
                    p.write(h + 0x280, struct.pack("<I", self.MAGIC))
                if target_pos and self.c_act is not None and self.c_x8 is not None and self.friend_banc == self.cur_banc and self.cur_banc and time.time() - max(getattr(self, '_tp_t', 0), getattr(self, '_friend_tp_t', 0)) > 8.0:   # ikke flytt til koordinater fra en annen sone / rett etter teleport (v0.56)
                    self._sync_pos(p, target_pos, target_rot, smag > 0.08)
                if self.c_act is not None and f_hearts:
                    h_cur = max(1, min(80, int(f_hearts[0])))
                    h_max = max(4, min(80, int(f_hearts[1])))
                    self._sync_copy_health(p, h_cur, h_max)
                self._eq_swap(p, d)
                # Vennen har pinne/sprettert framme, men Link 2 ikke (trykket gikk tapt): gi Link 2 et kort trykk på bruk-knappen
                now2 = time.time()
                fdr = getattr(self, 'friend_dr', [])
                need = [n for n in fdr if n not in (getattr(self, 'l2_drawn', None) or [])]
                bit = next((getattr(self, 'friend_db', {}).get(n) for n in need if getattr(self, 'friend_db', {}).get(n)), None)
                if False and need and bit and not (getattr(self, 'l2_drawn', None)):   # av: ga usynlig pinne
                    t_miss = self.__dict__.setdefault('_dr_miss', now2)
                    if now2 - t_miss > 1.0 and not getattr(self, '_dr_done', False):   # bare ett trykk per gang vennen tar fram tingen
                        self._dr_inj = now2; self._dr_done = True; log(f'ting: Link 2 mangler {need[0]} – trykker vennens knapp 0x{bit:X}')
                    if now2 - getattr(self, '_dr_inj', 0) < 0.15:
                        struct.pack_into('<I', d, 8, struct.unpack_from('<I', d, 8)[0] | bit)
                        p.write(h + 0x114, bytes(d[8:12]))
                else:
                    self._dr_miss = now2
                if not fdr:
                    self._dr_done = False
                # v0.94.114: ikke flytt Navi. Skriving av transformen hang spillet i v0.94.113.
                if getattr(self, 'navi2', None) is not None:
                    self.navi2 = None
                fit = getattr(self, 'friend_item', None)   # vennens aktive ting – hold den på Link 2 hvert bilde
                if False and isinstance(fit, int) and 0 < fit < 64 and self.c_act is not None:   # av: spillet bruker lagringens valgte ting
                    ha = p.base + self.c_act + 0x1D8
                    if struct.unpack('<I', p.read(ha, 4))[0] != fit:
                        p.write(ha, struct.pack('<I', fit))
            except OSError:
                pass
            except Exception as e:  # noqa: BLE001
                log(f"PadLink-løkke feil: {e!r}"); time.sleep(0.5)

    def _eq_swap(self, p, d):
        """Lån vennens knappeoppsett mens Link 2 bruker en ting (vennen holder bruk-knappen eller har pinne/sprettert framme),
        og legg vårt eget tilbake 0,6 s etter. Spillet henter tingen fra lagringen, som Link og Link 2 deler."""
        he = getattr(self, 'h_enum', None); fe = getattr(self, 'friend_eq', None)
        if he is None or not getattr(self, 'eq_ok', False):
            return
        now = time.time()
        btn = struct.unpack_from('<I', d, 8)[0]
        dbits = 0
        for v in (getattr(self, 'friend_db', {}) or {}).values():
            dbits |= int(v or 0)
        using = bool(fe) and (bool(btn & (dbits or 0x20)) or getattr(self, 'friend_drawn', False))   # bare vennens ting-knapp, eller ting framme
        using = False                       # lån av (brukeren valgte hvert sitt oppsett); legger bare tilbake et evt. lånt oppsett
        if now - getattr(self, '_eq_user_t', 0) < 4.0:
            using = False                       # du byttet selv nettopp – ikke overstyr
        saved = getattr(self, '_eq_saved', None)
        idx = getattr(self, 'eq_idx', ())
        try:
            if using:
                self._eq_use_t = now
                if saved is None:
                    self._eq_saved = [struct.unpack('<I', p.read(p.base + he + k * 0x38 + 0x1C, 4))[0] for k in idx]
                    log(f'knapper: låner vennens oppsett mens Link 2 bruker en ting')
                wrote = getattr(self, '_eq_wrote2', None)
                for i, (k, v) in enumerate(zip(idx, fe)):
                    a = p.base + he + k * 0x38 + 0x1C
                    cur = struct.unpack('<I', p.read(a, 4))[0]
                    if wrote is not None and cur != wrote[i] and cur != v and cur != self._eq_saved[i]:
                        self._eq_saved[i] = cur; self._eq_user_t = now   # du byttet i menyen: det blir ditt nye oppsett
                        log('knapper: du byttet selv – slutter å låne')
                        continue
                    if cur != v:
                        p.write(a, struct.pack('<2I', v, v))
                self._eq_wrote2 = list(fe)
            elif saved is not None and now - getattr(self, '_eq_use_t', 0) > 2.5:
                for k, v, f in zip(idx, saved, fe or saved):
                    a = p.base + he + k * 0x38 + 0x1C
                    cur = struct.unpack('<I', p.read(a, 4))[0]
                    if cur == f or fe is None:          # bare hvis det fortsatt er vennens (ikke noe du byttet selv i mellomtiden)
                        p.write(a, struct.pack('<2I', v, v))
                self._eq_saved = None; self._eq_wrote2 = None
                log('knapper: la tilbake ditt eget oppsett')
        except OSError:
            pass

    def _sync_pos(self, p, target_pos, target_rot, moving):
        """Hold Link 2 på samme plass/rotasjon som vennen via transform-komponenten x8 (+0x1d0..+0x1fc + dirty-bits).
        VIKTIG: x8+0x1d0..0x1fc er en 3x4 matrise [r00,r01,r02,x, r10,r11,r12,y, r20,r21,r22,z]. Hele 3x4-matrisen må
        skrives (som spillets 0x4C6630 gjør), ellers overskriver gammel rotasjon i x8 Link 2 sin retning!
        v0.31 (Plan 1): Mens vennen løper (moving=True), styrer 120 Hz kamerarotert stikke Link 2 100 % uten at _sync_pos
        dytter ham tilbake til en 15–30 ms gammel UDP-posisjon (griper kun inn hvis avviket > 1.25 m). Det sekundet vennen
        stopper (moving=False), glir _sync_pos ham silkemykt inn på eksakt sluttposisjon (> 0.04 m)!"""
        try:
            tx, ty, tz = target_pos
            if not all(math.isfinite(v) and abs(v) < 1e5 for v in (tx, ty, tz)):
                return
            cx, cy, cz = p.f32(self.c_act + 0x31C, 3)
            dx, dy, dz = tx - cx, ty - cy, tz - cz
            dist_xz = math.hypot(dx, dz)
            thr_xz = 1.25 if moving else 0.04
            if dist_xz < thr_xz and abs(dy) < (0.80 if moving else 0.25):
                return
            if dist_xz > 3.0 or abs(dy) > 2.5:
                nx, ny, nz = tx, ty, tz
            elif not moving:
                nx, ny, nz = cx + dx * 0.35, cy + dy * 0.35, cz + dz * 0.35
            else:
                nx, ny, nz = cx + dx * 0.20, cy + dy * 0.20, cz + dz * 0.20
            rot = target_rot if (target_rot and len(target_rot) == 9) else p.f32(self.c_act + 0x328, 9)
            mat3x4 = struct.pack("<12f",
                                 rot[0], rot[1], rot[2], nx,
                                 rot[3], rot[4], rot[5], ny,
                                 rot[6], rot[7], rot[8], nz)
            hx8 = p.base + self.c_x8
            p.write(hx8 + 0x1D0, mat3x4)
            p.write(hx8 + 0x208, struct.pack("<3f", 1.0, 1.0, 1.0))
            w = struct.unpack("<I", p.read(hx8 + 0x228, 4))[0]
            p.write(hx8 + 0x228, struct.pack("<I", w | 3))
            if self.c_x9 is not None:
                hx9 = p.base + self.c_x9
                b = p.read(hx9 + 0x1F2, 1)[0]
                p.write(hx9 + 0x1F2, bytes([b | 0x80]))
        except OSError:
            pass


def _asset_category(rel):
    """Klassifiser en mod-fil i lesbar kategori for feilsøking av Assets: MISMATCH."""
    low = rel.lower()
    if low.endswith('.pchtxt') or '/exefs/' in low or low.startswith('exefs/'):
        return 'patches'
    if '/pack/' in low or '.pack' in low or '.bfres' in low:
        return 'models'
    if '/tex/' in low or '.bntx' in low:
        return 'textures'
    if '/rsdb/' in low or '/system/resource/' in low or '.rsizetable' in low or '.rstbl' in low:
        return 'rsdb'
    return 'other'


def asset_manifest(load_root=None):
    """Returner (sha256_hex, {rel_path: [size, sha256_8]}) for aktive romfs/exefs og .pchtxt-patcher."""
    base_load = load_root or os.path.abspath(os.path.join(APP_DIR, '..', 'user', 'load', '0400486024DEC000'))
    roots = [
        ('OoT_MP_Tunic', ('romfs', 'exefs')),
        ('OoT_MP_Test', ('exefs',)),
    ]
    entries = []
    skipped_bak = []
    for mod_name, subs in roots:
        mod_dir = os.path.join(base_load, mod_name)
        for sub in subs:
            sub_dir = os.path.join(mod_dir, sub)
            if not os.path.isdir(sub_dir):
                continue
            for folder, _dirs, names in os.walk(sub_dir):
                for n in names:
                    full = os.path.join(folder, n)
                    rel = f"{mod_name}/{os.path.relpath(full, mod_dir).replace(os.sep, '/')}"
                    low_n = n.lower()
                    if low_n.endswith(('.bak', '.disabled')) or low_n in ('angin_tile_a_alb.bntx.zs', 'angin_tile_a_dark_alb.bntx.zs'):
                        skipped_bak.append(rel)
                        continue
                    entries.append((rel, full))
    if not entries:
        return None, {}
    digest = hashlib.sha256()
    files = {}
    for rel, full in sorted(entries, key=lambda x: x[0]):
        digest.update(rel.encode('utf-8'))
        fhash = hashlib.sha256()
        size = 0
        with open(full, 'rb') as f:
            for block in iter(lambda: f.read(1024 * 1024), b''):
                size += len(block)
                digest.update(block)
                fhash.update(block)
        files[rel] = [size, fhash.hexdigest()[:8]]
    return digest.hexdigest(), files


def diff_asset_manifests(mine, theirs):
    """Sammenlign lokale og vennens {rel: [size, sha8]} og returner (only_mine, only_theirs, changed, cats)."""
    mine = mine or {}
    theirs = theirs or {}
    only_mine = sorted(k for k in mine if k not in theirs)
    only_theirs = sorted(k for k in theirs if k not in mine)
    changed = sorted(k for k in mine if k in theirs and list(mine[k]) != list(theirs[k]))
    cats = []
    seen = set()
    for rel in only_mine + only_theirs + changed:
        c = _asset_category(rel)
        if c not in seen:
            seen.add(c); cats.append(c)
    return {'only_mine': only_mine, 'only_theirs': only_theirs, 'changed': changed, 'cats': cats}


def asset_fingerprint(load_root=None):
    """SHA-256 av aktive modeller, teksturer og ARM64-patcher, uten spillkall."""
    h, _files = asset_manifest(load_root=load_root)
    return h


class PuppetFollower:
    """v0.94.160: port av oppstrøms `CoopFollow::Follower`.

    Kilde: `D:\\Switch2\\ext\\daurosk\\lichii\\hook\\coop_follow.h` (GPL-3.0-or-later).

    Modellen: dukken skal ikke teletransporteres til målet hvert bilde. En
    *jeger* per dukke bæres fram av en utglattet fart, lukker resten av gapet
    med en eksponential, overskrider aldri målet, og setter seg nøyaktig der
    når fjernspilleren står stille. Det gir jevne steg uten lag, og en stopp
    lander eksakt.

    Parametrene er de samme som i C++-referansen:
      kAheadMaxMs 150, kTauMs 40, kJumpM 0,75, kRestM 0,005, kMaxStepMs 100,
      kVelTauMs 60, kSoftM 0,05, kSoftTauMs 160, kPassM 0,02, kSameM 1e-5.
    """

    # v0.94.186: K_AHEAD_MAX_MS = 0.0 + mykere tau (55/80 ms) + farts-demper (maks 1.35x snittfart per bilde)
    # fjerner både bakoverhopp og 10-12 m/s innhentings-spiker ved 20 FPS emulator-takt.
    K_AHEAD_MAX_MS = 0.0
    K_TAU_MS = 55.0
    K_JUMP_M = 0.75
    K_REST_M = 0.005
    K_MAX_STEP_MS = 100.0
    K_VEL_TAU_MS = 80.0
    K_SOFT_M = 0.05
    K_SOFT_TAU_MS = 160.0
    K_PASS_M = 0.02
    K_SAME_M = 1e-5
    # v0.94.161: sikkerhetsklemmer. Oppstrøms faar hopp (teleport) håndtert av
    # kallerens egen easing (coop_snap.h) FØR jegeren ser den. Vi har ingen
    # slik easing, og en rått hopp gir en enorm fart -> ville ekstrapolert
    # dukken mange meter og falt ut av verden. Derfor klemmes farten, og
    # framskridtstrekningen kan aldri overstige kJumpM.
    K_MAX_SPEED = 12.0
    K_MAX_AHEAD_M = 0.75
    K_YAW_TAU_MS = 35.0
    K_YAW_SNAP_RAD = 1.8

    def __init__(self):
        self.drawn = None      # hvor dukken er tegnet
        self.rest = None       # idle-twitch: hvor den holdes stille
        self.vel = (0.0, 0.0, 0.0)
        self.last_ms = 0.0
        self.yaw = None
        self.yaw_ms = 0.0

    @staticmethod
    def _dist(a, b):
        return math.sqrt(sum((a[i] - b[i]) ** 2 for i in range(3)))

    @staticmethod
    def _still(v):
        return abs(v[0]) < 1e-3 and abs(v[1]) < 1e-3 and abs(v[2]) < 1e-3

    def reset(self):
        self.drawn = None
        self.rest = None
        self.yaw = None
        self.yaw_ms = 0.0

    def step_yaw(self, target_yaw, now_ms):
        """v0.94.176: korteste-vinkel eksponentiell yaw-glatting (0 game_call)."""
        if not math.isfinite(target_yaw):
            return self.yaw if self.yaw is not None else 0.0
        if self.yaw is None or now_ms < self.yaw_ms:
            self.yaw = float(target_yaw)
            self.yaw_ms = now_ms
            return self.yaw
        dt_ms = min(now_ms - self.yaw_ms, self.K_MAX_STEP_MS)
        if dt_ms <= 0.0:
            return self.yaw
        diff = ((target_yaw - self.yaw + math.pi) % (2.0 * math.pi)) - math.pi
        if abs(diff) > self.K_YAW_SNAP_RAD or abs(diff) < 1e-4:
            self.yaw = float(target_yaw)
        else:
            k = 1.0 - math.exp(-dt_ms / self.K_YAW_TAU_MS)
            self.yaw = self.yaw + diff * k
        self.yaw_ms = now_ms
        return self.yaw

    def _set(self, at, now_ms):
        self.drawn = at
        self.last_ms = now_ms
        return at

    def step(self, target, velocity, target_ms, now_ms):
        """target: hvor målet er (3-tuppel), velocity: m/s, target_ms/now_ms: ms."""
        if not all(math.isfinite(v) for v in target) or not all(math.isfinite(v) for v in velocity):
            self.reset()
            return target
        first = self.drawn is None or now_ms < self.last_ms
        dt_ms = 0.0 if first else min(now_ms - self.last_ms, self.K_MAX_STEP_MS)
        if not first and dt_ms <= 0.0:
            return self.drawn                       # to ganger i samme bilde
        if first:
            self.vel = tuple(float(v) for v in velocity)
        else:
            k = 1.0 - math.exp(-dt_ms / self.K_VEL_TAU_MS)
            self.vel = tuple(self.vel[i] + (velocity[i] - self.vel[i]) * k for i in range(3))
        # v0.94.161: klem farten (et hopp gir ellers enorme hastigheter)
        sp = math.sqrt(sum(v * v for v in self.vel))
        if sp > self.K_MAX_SPEED:
            f = self.K_MAX_SPEED / sp
            self.vel = tuple(v * f for v in self.vel)
        ahead_ms = 0.0 if not target_ms else max(-self.K_AHEAD_MAX_MS,
                                                 min(self.K_AHEAD_MAX_MS, now_ms - target_ms))
        ahead = tuple(self.vel[i] * (ahead_ms / 1000.0) for i in range(3))
        # v0.94.161: framskridtstrekningen kan aldri overstige kJumpM
        ad = math.sqrt(sum(v * v for v in ahead))
        if ad > self.K_MAX_AHEAD_M:
            f = self.K_MAX_AHEAD_M / ad
            ahead = tuple(v * f for v in ahead)
        want = tuple(target[i] + ahead[i] for i in range(3))
        if first:
            self.rest = None
            return self._set(want, now_ms)
        if self.rest is not None:
            if self._still(velocity) and self._dist(want, self.rest) < self.K_SAME_M:
                return self._set(self.rest, now_ms)
            self.rest = None
        drawn = self.drawn
        gap = self._dist(drawn, want)
        if gap > self.K_JUMP_M:
            return self._set(want, now_ms)            # teleport/hopp: tas med én gang
        nxt = tuple(drawn[i] + self.vel[i] * dt_ms / 1000.0 for i in range(3))
        along = sum((want[i] - nxt[i]) * (want[i] - drawn[i]) for i in range(3))
        if along < 0.0 and (self._still(velocity) or self._dist(nxt, want) > self.K_PASS_M):
            nxt = want                                  # aldri forbi målet
        tau = (self.K_TAU_MS if (self._still(velocity) or gap >= self.K_SOFT_M)
               else self.K_SOFT_TAU_MS + (self.K_TAU_MS - self.K_SOFT_TAU_MS) * (gap / self.K_SOFT_M))
        close = 1.0 - math.exp(-dt_ms / tau)
        cand = tuple(nxt[i] + (want[i] - nxt[i]) * close for i in range(3))
        # v0.94.186: farts-demper per steg – hindrer 10-12 m/s innhentingsrykk ved 20 FPS emulator-takt
        step_d = self._dist(drawn, cand)
        max_step = max(sp * 1.35, 3.0) * (dt_ms / 1000.0)
        if step_d > max_step > 1e-6:
            f = max_step / step_d
            drawn = tuple(drawn[i] + (cand[i] - drawn[i]) * f for i in range(3))
        else:
            drawn = cand
        if self._still(velocity) and self._dist(drawn, want) <= self.K_REST_M:
            drawn = want
            self.rest = drawn
        self.drawn = drawn
        self.last_ms = now_ms
        return drawn


class App:
    def __init__(self, root):
        self.root = root
        self.cfg = load_cfg()
        self.gport, self.dport = MODE_PORTS.get(self.cfg.get("mode"), (GAME_PORT, DISC_PORT))
        self.session = random.getrandbits(32)
        self.name = self.cfg.get("name") or os.getenv("USERNAME", "spiller")
        self.hat_color = self.cfg.get("hat_color") if self.cfg.get("hat_color") in HAT_COLORS else "Grønn"
        self.p = None; self.pos_off = None; self.rupees = None; self.syncs = {}
        self.cam_off = None; self.cam_scanning = False; self.cam_last_scan = 0
        self.overlay = None; self.lwin = None; self.lwin_t = 0
        self.ready = False
        self.peer = None; self.friend = None; self.friend_t = 0; self.friend_session = None
        self.figure = FigureSync()
        self.pad = PadLink()
        self.pad.START_POS = dict(PadLink.START_POS, **(self.cfg.get('start_pos') or {}))   # lærte startpunkter (lagres i config)
        self.players = {}          # ip -> (name, last_seen, session)
        self._web_imp_n = 0       # tellere for faktisk kallrate (v0.94.197)
        self._web_imp_n0 = 0
        self._web_imp_t = 0.0
        self._web_rate = 0.0
        self.ui_q = queue.Queue()
        self.answer = queue.Queue()
        self.chat_seq = 0
        self.chat_out = []         # [(id, name, text, color)] siste 8 utgående meldinger
        self.chat_seen = set()     # (friend_session, id) så hver melding bare vises én gang
        self.chat_history = []     # felles historikk for hovedvindu og stort chatvindu
        self.chat_window = None
        self.chat_popup_log = None
        self.chat_popup_var = None
        self._fast_net_lk = threading.Lock()
        self.asset_hash = None
        self.asset_files = {}
        self.friend_assets = None
        self._asset_diff = None
        self._game_mode = 'ctf'

        root.title(f"Zelda Multiplayer {VERSION}"); root.configure(bg=BG)
        root.geometry("680x1010"); root.resizable(False, False)
        st = ttk.Style(); st.theme_use("clam")
        st.configure(".", background=BG, foreground=FG, fieldbackground=FIELD, bordercolor=BORDER, lightcolor=BORDER, darkcolor=BORDER)
        st.configure("TButton", padding=(10, 4), background=BTN, foreground=GOLD, bordercolor=GOLD_D, focuscolor=GOLD_D,
                     font=("Segoe UI", 9, "bold"))
        st.map("TButton", background=[("active", BTN_H)], foreground=[("active", "#fff3c4")])
        st.configure("TEntry", fieldbackground=FIELD, foreground=FG, insertcolor=GOLD, bordercolor=BORDER)
        st.configure("TCombobox", fieldbackground=FIELD, background=BTN, foreground=FG, arrowcolor=GOLD, bordercolor=BORDER)
        st.map("TCombobox", fieldbackground=[("readonly", FIELD)], foreground=[("readonly", FG)])
        st.configure("Horizontal.TProgressbar", troughcolor=FIELD, background=GOLD_D)

        def card(parent, title, **pack):
            """Panel med gull-ramme og tittel (Zelda-meny-stil)."""
            outer = tk.Frame(parent, bg=GOLD_D, padx=1, pady=1); outer.pack(fill="x", padx=14, pady=(4, 4), **pack)
            inner = tk.Frame(outer, bg=PANEL); inner.pack(fill="both", expand=True)
            if title:
                tk.Label(inner, text=title, bg=PANEL, fg=GOLD, font=(ZELDA_FONT, 17, "bold")).pack(anchor="center", padx=10, pady=(6, 0))
            return outer, inner

        # --- Tittel ---
        hdr = tk.Frame(root, bg=BG); hdr.pack(fill="x", padx=14, pady=(10, 2))
        tk.Label(hdr, text="▲  Zelda Multiplayer  ▲", bg=BG, fg=GOLD, font=(ZELDA_FONT, 32, "bold")).pack(anchor="center")
        tk.Label(hdr, text=f"Ocarina of Time  ·  v{VERSION}  ·  Made by NorPat", bg=BG, fg=GOLD_D,
                 font=(ZELDA_FONT, 14, "italic")).pack(anchor="center", pady=(0, 4))
        tk.Frame(root, bg=GOLD_D, height=1).pack(fill="x", padx=40, pady=(0, 6))

        # --- Spiller: navn og utseende ---
        _o, pc = card(root, "Player")
        top = tk.Frame(pc, bg=PANEL); top.pack(fill="x", padx=10, pady=(4, 8))
        top_in = tk.Frame(top, bg=PANEL); top_in.pack(anchor="center")
        tk.Label(top_in, text="Name", bg=PANEL, fg=MUTED, font=("Segoe UI", 9)).pack(side="left")
        self.name_var = tk.StringVar(value=self.name)
        e = ttk.Entry(top_in, textvariable=self.name_var, width=14); e.pack(side="left", padx=(6, 16))
        e.bind("<FocusOut>", lambda _e: self._save_name())
        e.bind("<Return>", lambda _e: self._save_name())
        # v0.94.285: passord for navnet (beskytter inventaret på serveren). Bare en avledet nøkkel lagres/sendes.
        tk.Label(top_in, text="🔒", bg=PANEL, fg=MUTED, font=("Segoe UI", 9)).pack(side="left")
        self.pw_var = tk.StringVar()
        self.pw_entry = ttk.Entry(top_in, textvariable=self.pw_var, width=10, show="•")
        self.pw_entry.pack(side="left", padx=(2, 14))
        self.pw_entry.bind("<Return>", lambda _e: self._save_password())
        self.pw_entry.bind("<FocusOut>", lambda _e: self._save_password())
        # Utseende: gjelder egen Link og hvordan vennen ser deg. Fargen beholdes internt (chat/markør).
        self.color_dot = tk.Label(top_in, text="●", fg=HAT_COLORS[self.hat_color], bg=PANEL, font=("Segoe UI", 13))
        self.color_var = tk.StringVar(value=self.hat_color)
        tk.Label(top_in, text="Link", bg=PANEL, fg=MUTED, font=("Segoe UI", 9)).pack(side="left")
        self.look = {'Vanlig': 'Normal', 'Uten trøye': 'No tunic'}.get(self.cfg.get("look"), self.cfg.get("look"))
        self.look = self.cfg.get("look") if self.cfg.get("look") in LOOKS else 'Red'
        write_look_copy(self.look)
        self.look_var = tk.StringVar(value=self.look)
        self.pad.my_look = self.look
        try:   # v0.94.279: fargen auto_restart la i romfs ved spillstart
            _md = os.path.dirname(sys.executable if getattr(sys, 'frozen', False) else os.path.abspath(__file__))
            _rl = os.path.join(os.path.dirname(_md), 'user', 'load', '0400486024DEC000', 'OoT_MP_Tunic', 'romfs_look.txt')
            self.pad.romfs_look = open(_rl, encoding='utf-8').read().strip() if os.path.isfile(_rl) else self.look
        except OSError:
            self.pad.romfs_look = self.look
        log(f'tunika: oppstartsfarge i romfs = {self.pad.romfs_look}')
        self.pad.link2_actor = self.cfg.get('link2_actor') or 'Player_Child'
        cb_look = self.cb_look = ttk.Combobox(top_in, textvariable=self.look_var, values=LOOKS, width=11, state="readonly")
        cb_look.pack(side="left", padx=(6, 0))
        cb_look.bind("<<ComboboxSelected>>", lambda _e: self._save_look())
        self.root.after(3000, self._pvp_look_loop)   # v0.94.321: PvP-tunika = lagfarge
        # v0.73: Story / PvP
        tk.Label(top_in, text="Mode", bg=PANEL, fg=MUTED, font=("Segoe UI", 9)).pack(side="left", padx=(10, 0))
        self.mode = self.cfg.get("mode") if self.cfg.get("mode") in MODES else "Story"
        self.pad.pvp_message_filter = (self.mode == 'PvP')
        self.pad.share_interact = (self.mode != 'PvP')
        self.mode_var = tk.StringVar(value=self.mode)
        cb_mode = ttk.Combobox(top_in, textvariable=self.mode_var, values=MODES, width=7, state="readonly")
        cb_mode.pack(side="left", padx=(6, 0))
        cb_mode.bind("<<ComboboxSelected>>", lambda _e: self._save_mode())
        self.tvang_var = tk.BooleanVar(value=bool(self.cfg.get("tvang", False)))
        self.tvang = bool(self.cfg.get("tvang", False))   # vanlig bool: kan leses fra nett-tråden (Tk-variabler kan IKKE – ga vranglås)
        self.follow_cb = tk.Checkbutton(top_in, text="FOLLOW", variable=self.tvang_var, command=self._tvang_toggled,
                       bg=PANEL, fg=FG, selectcolor=FIELD, activebackground=PANEL, activeforeground=GOLD,
                       font=("Segoe UI", 9))
        # v0.94.294: navneskilt av/på (v0.94.295: Story og PvP)
        self.names_var = tk.BooleanVar(value=bool(self.cfg.get("nameplates", True)))
        self.names_cb = tk.Checkbutton(top_in, text="NAMES", variable=self.names_var, command=self._names_toggled,
                       bg=PANEL, fg=FG, selectcolor=FIELD, activebackground=PANEL, activeforeground=GOLD,
                       font=("Segoe UI", 9))
        if self.cfg.get("mode") != "PvP":   # v0.79: FOLLOW finnes bare i Story
            self.follow_cb.pack(side="left", padx=(10, 0))
        self.names_cb.pack(side="left", padx=(10, 0))   # v0.94.295: NAMES i både Story og PvP

        # --- Spill-status (to kolonner) og Nettverk side om side ---
        row = tk.Frame(root, bg=BG); row.pack(fill="x", padx=14, pady=(4, 4)); self._status_row = row
        left = tk.Frame(row, bg=GOLD_D, padx=1, pady=1); left.pack(side="left", fill="both", expand=True, padx=(0, 4))
        right = tk.Frame(row, bg=GOLD_D, padx=1, pady=1); right.pack(side="left", fill="both", expand=True, padx=(4, 0))
        gl = tk.Frame(left, bg=PANEL); gl.pack(fill="both", expand=True)
        nr = tk.Frame(right, bg=PANEL); nr.pack(fill="both", expand=True)
        tk.Label(gl, text="Game", bg=PANEL, fg=GOLD, font=(ZELDA_FONT, 17, "bold")).pack(anchor="center", padx=10, pady=(6, 2))
        tk.Label(nr, text="Network", bg=PANEL, fg=GOLD, font=(ZELDA_FONT, 17, "bold")).pack(anchor="center", padx=10, pady=(6, 2))
        self.checks = {}
        g_in = tk.Frame(gl, bg=PANEL); g_in.pack(fill="x", padx=10, pady=(0, 8))
        for idx, (key, text) in enumerate((("lichii", "Lichii"), ("game", "Memory"), ("pos", "Link 3D"),
                                           ("rupees", "Save"), ("cam", "Camera"), ("clock", "Clock"))):
            cell = tk.Frame(g_in, bg=PANEL); cell.grid(row=idx, column=0, sticky="ew", pady=1)
            g_in.columnconfigure(0, weight=1)
            dot = tk.Label(cell, text="●", fg=MUTED, bg=PANEL, font=("Segoe UI", 10)); dot.pack(side="left")
            tk.Label(cell, text=text, fg=FG, bg=PANEL, font=("Segoe UI", 9, "bold"), width=8, anchor="w").pack(side="left", padx=4)
            info = tk.Label(cell, text="", fg=MUTED, bg=PANEL, font=("Segoe UI", 8), anchor="e"); info.pack(side="right")
            self.checks[key] = (dot, info)
        self.net_lbls = {}
        self.net_key_lbls = {}
        self.net_rows = {}
        n_in = tk.Frame(nr, bg=PANEL); n_in.pack(fill="x", padx=10, pady=(0, 8))
        for idx, (key, text) in enumerate((("state", "Status"), ("ping", "Ping"), ("rate", "Packets"),
                                           ("ip", "Server"), ("host", "Host"))):
            cell = tk.Frame(n_in, bg=PANEL); cell.grid(row=idx, column=0, sticky="ew", pady=1)
            self.net_rows[key] = cell
            n_in.columnconfigure(0, weight=1)
            key_lbl = tk.Label(cell, text=text, fg=FG, bg=PANEL, font=("Segoe UI", 9, "bold"), width=8, anchor="w")
            key_lbl.pack(side="left")
            self.net_key_lbls[key] = key_lbl
            v = tk.Label(cell, text="–", fg=MUTED, bg=PANEL, font=("Consolas", 9), anchor="e"); v.pack(side="right")
            self.net_lbls[key] = v
        if "port" in self.net_lbls:
            self.net_lbls["port"].config(text=server_port_label(), fg=FG)
        self.net_lbls["ip"].config(text=", ".join(local_ips()) or "?", fg=FG)
        # vert: klikk på verdien for å bytte (Auto -> Meg -> Vennen)
        self.host_mode = self.cfg.get("host_mode", "auto") if self.cfg.get("host_mode") in ("auto", "me", "friend") else "auto"
        self.net_lbls["host"].config(cursor="hand2")
        self.net_lbls["host"].bind("<Button-1>", lambda _e: self._cycle_host())

        # veiledningspanel (skjult når ikke i bruk)
        self.guide = tk.Frame(root, bg=FIELD)
        self.guide_lbl = tk.Label(self.guide, text="", bg=FIELD, fg=FG, wraplength=560, justify="left", font=("Segoe UI", 10))
        self.guide_lbl.pack(fill="x", padx=10, pady=(8, 4))
        self.guide_entry = ttk.Entry(self.guide, width=10)
        self.guide_btn = ttk.Button(self.guide, text="OK", command=self._guide_ok)
        self.prog = ttk.Progressbar(root, mode="determinate", maximum=1.0)

        # --- Koble til ---
        _o, cc = card(root, "Connected")
        pl = tk.Frame(cc, bg=PANEL); pl.pack(fill="x", padx=10, pady=(4, 8))
        lst_fr = tk.Frame(pl, bg=PANEL); lst_fr.pack(fill="x")
        self.plist = tk.Listbox(lst_fr, height=5, bg=FIELD, fg=FG, selectbackground=SEL, selectforeground="#ffffff",
                                highlightthickness=1, highlightbackground=BORDER, borderwidth=0, font=("Segoe UI", 9),
                                justify="center", cursor="hand2")
        _sb = ttk.Scrollbar(lst_fr, orient="vertical", command=self.plist.yview)   # plass til mange spillere (50–100)
        self.plist.config(yscrollcommand=_sb.set)
        _sb.pack(side="right", fill="y"); self.plist.pack(side="left", fill="x", expand=True)
        self.plist.bind("<Button-1>", lambda _e: self._open_connected_window())
        self._conn_title = cc.winfo_children()[0]   # tittel får antall fra serveren
        self.conn_window = None
        self.conn_popup_list = None
        self.ip_var = tk.StringVar(value=self.cfg.get("last_ip", ""))

        # --- Story-kanaler: Public er standard; private lobbyer isolerer dukker og chat. ---
        self.story_lobby_outer, slc = card(root, "Story lobby")
        if self.mode != 'Story':
            self.story_lobby_outer.pack_forget()
        self.story_lobby_info = tk.Label(slc, text="Public · everyone", bg=PANEL, fg=GOLD,
                                         font=("Segoe UI", 10, "bold"), justify="center")
        self.story_lobby_info.pack(fill="x", padx=10, pady=(4, 3))
        self.story_lobby_list = tk.Listbox(slc, height=4, bg=FIELD, fg=FG, selectbackground=SEL,
                                           highlightthickness=1, highlightbackground=BORDER,
                                           borderwidth=0, font=("Segoe UI", 9))
        self.story_lobby_list.pack(fill="x", padx=10, pady=3)
        self.story_lobby_list.bind('<ButtonRelease-1>', lambda _e: self._story_lobby_join())
        slcreate = tk.Frame(slc, bg=PANEL); slcreate.pack(fill="x", padx=10, pady=(2, 2))
        self.story_lobby_name = tk.StringVar()
        self.story_lobby_entry = ttk.Entry(slcreate, textvariable=self.story_lobby_name, width=18)
        self.story_lobby_entry.pack(side="left", fill="x", expand=True)
        self.story_lobby_entry.bind('<Return>', lambda _e: self._story_lobby_create())
        ttk.Button(slcreate, text="Create", command=self._story_lobby_create).pack(side="right", padx=(4, 0))
        slpass = tk.Frame(slc, bg=PANEL); slpass.pack(fill="x", padx=10, pady=(0, 8))
        tk.Label(slpass, text="Password (optional)", bg=PANEL, fg=MUTED, font=("Segoe UI", 8)).pack(side="left")
        self.story_lobby_password = tk.StringVar()
        self.story_lobby_password_entry = ttk.Entry(slpass, textvariable=self.story_lobby_password, show='•', width=14)
        self.story_lobby_password_entry.pack(side="right", fill="x", expand=True, padx=(6, 0))

        # --- Story-modus Boss-HP-boks (dukker automatisk opp kun under bosskamp, skjules ellers) ---
        self.boss_outer, bc = card(root, "Boss")
        self.boss_outer.pack_forget()
        self._boss_card_shown = False
        self.boss_name_lbl = tk.Label(bc, text="No active boss", bg=PANEL, fg=GOLD, font=("Segoe UI", 11, "bold"),
                                      justify="center", anchor="center")
        self.boss_name_lbl.pack(fill="x", padx=10, pady=(4, 2))
        self.boss_bar = tk.Canvas(bc, height=14, bg=FIELD, highlightthickness=1, highlightbackground=BORDER)
        self.boss_bar.pack(fill="x", padx=10, pady=(2, 3))
        self._boss_bar_rect = self.boss_bar.create_rectangle(0, 0, 0, 14, fill="#c93b3b", width=0)
        self.boss_hp_lbl = tk.Label(bc, text="", bg=PANEL, fg=HEART, font=("Segoe UI", 9, "bold"),
                                    justify="center", anchor="center")
        self.boss_hp_lbl.pack(fill="x", padx=10, pady=(0, 8))
        self._boss_ui_last = None

        # --- Autoritativ PvP-lobby på .121 ---
        self.lobby_outer, lc = card(root, "PvP")
        if self.mode != 'PvP':
            self.lobby_outer.pack_forget()
        else:
            # Lobbyen er hovedkontrollen i PvP og må ligge over diagnostikk og chat.
            self.lobby_outer.pack(before=row)
        self.lobby_info = tk.Label(lc, text="Connecting to server …", bg=PANEL, fg=FG,
                                   justify="center", anchor="center", font=("Segoe UI", 9, "bold"))
        self.lobby_info.pack(fill="x", padx=10, pady=(4, 2))
        self.counter_fr = tk.Frame(lc, bg=FIELD, highlightthickness=1, highlightbackground=GOLD)
        counter_head = tk.Frame(self.counter_fr, bg=FIELD)
        counter_head.pack(fill="x", padx=8, pady=(6, 2))
        tk.Label(counter_head, text="Counter", bg=FIELD, fg=GOLD, font=("Segoe UI", 11, "bold")).pack(side="left")
        self.counter_ruby = tk.Label(counter_head, text="", bg=FIELD, fg=FG, font=("Segoe UI", 9))
        self.counter_ruby.pack(side="left", padx=8)
        ttk.Button(counter_head, text="Close", command=self._counter_close).pack(side="right")
        counter_row = tk.Frame(self.counter_fr, bg=FIELD)
        counter_row.pack(fill="x", padx=8, pady=(0, 6))
        self.counter_btns = {}
        for row_i, (item_id, label, price, qty) in enumerate(self.PVP_COUNTER):
            btn = ttk.Button(counter_row, text=f"{label}   +{qty}   {price} r",
                             command=lambda i=item_id: self._shop_buy(i))
            btn.grid(row=row_i, column=0, padx=2, pady=2, sticky="ew")
            self.counter_btns[item_id] = btn
        counter_row.columnconfigure(0, weight=1)
        self.game_mode_var = tk.StringVar(value=self.cfg.get('game_mode_name') if self.cfg.get('game_mode_name') in GAME_MODES else 'Capture the Flame')
        _gmode = lambda: 'deathmatch' if self.game_mode_var.get() == 'Deathmatch' else 'ctf'
        # --- Trinn 1: velg spillmodus ---
        self.mode_pick = tk.Frame(lc, bg=PANEL)
        tk.Label(self.mode_pick, text='Choose game mode', bg=PANEL, fg=MUTED, font=('Segoe UI', 9)).pack(pady=(4, 4))
        pick_row = tk.Frame(self.mode_pick, bg=PANEL); pick_row.pack(pady=(0, 8))
        for _gm, _sub in (('Capture the Flame', 'Light the enemy torch'), ('Deathmatch', 'Knock out the other team')):
            _b = tk.Frame(pick_row, bg=FIELD, highlightthickness=1, highlightbackground=BORDER, cursor='hand2')
            _b.pack(side='left', padx=8)
            _t = tk.Label(_b, text=_gm, bg=FIELD, fg=GOLD, font=('Segoe UI', 13, 'bold'), padx=18, pady=(8))
            _t.pack()
            _s = tk.Label(_b, text=_sub, bg=FIELD, fg=MUTED, font=('Segoe UI', 8), padx=18)
            _s.pack(pady=(0, 8))
            for _w in (_b, _t, _s):
                _w.bind('<Button-1>', lambda _e, g=_gm: self._pick_game_mode(g))
        # --- Trinn 2: valg for valgt spillmodus ---
        self.mode_opts = tk.Frame(lc, bg=PANEL)
        hdr = tk.Frame(self.mode_opts, bg=PANEL); hdr.pack(fill='x', padx=10, pady=(2, 4))
        ttk.Button(hdr, text='‹ Game modes', command=self._unpick_game_mode).pack(side='left')
        self.mode_title = tk.Label(hdr, text='', bg=PANEL, fg=GOLD, font=('Segoe UI', 12, 'bold'))
        self.mode_title.pack(side='left', padx=10)
        ttk.Button(hdr, text='Goto Lobby', command=self._goto_lobby).pack(side='right')
        sec = lambda txt: tk.Label(self.mode_opts, text=txt, bg=PANEL, fg=MUTED, anchor='w', font=('Segoe UI', 8, 'bold'))
        sec('FIND OR HOST A GAME').pack(fill='x', padx=10, pady=(4, 0))
        self.lobby_games = tk.Listbox(self.mode_opts, height=4, bg=FIELD, fg=FG, selectbackground=SEL,
                                      highlightthickness=1, highlightbackground=BORDER,
                                      borderwidth=0, font=('Segoe UI', 9))
        self.lobby_games.pack(fill='x', padx=10, pady=3)
        self.lobby_games.bind('<Double-Button-1>', lambda _e: self._lobby_join())
        # v0.94.316/320: brettvalg. CTF bare på brett med 'ctf' (Gohma, Zora's Domain); Deathmatch på alle.
        self.arena_var = tk.StringVar(value=self.cfg.get('arena_pick') if self.cfg.get('arena_pick') in self.ARENAS else 'gohma')
        _arena = lambda: (self.arena_var.get() if (_gmode() == 'deathmatch' or self.ARENAS.get(self.arena_var.get(), {}).get('ctf'))
                          else 'gohma')
        self.arena_row = tk.Frame(self.mode_opts, bg=PANEL)
        tk.Label(self.arena_row, text='Arena:', bg=PANEL, fg=MUTED, font=('Segoe UI', 9)).pack(side='left')
        self._arena_radios = {}
        for _k, _lbl in (('gohma', 'Gohma room'), ('sword', 'Sword course (rolling boulder)'), ('zora', "Zora's Domain"), ('field', 'Hyrule Field (night)')):
            self._arena_radios[_k] = tk.Radiobutton(self.arena_row, text=_lbl, value=_k, variable=self.arena_var, bg=PANEL, fg=FG, selectcolor=FIELD,
                           activebackground=PANEL, activeforeground=GOLD, font=('Segoe UI', 9),
                           command=lambda: (self.cfg.__setitem__('arena_pick', self.arena_var.get()), save_cfg(self.cfg))
                           )
            self._arena_radios[_k].pack(side='left', padx=4)
        r1 = tk.Frame(self.mode_opts, bg=PANEL); r1.pack(fill='x', padx=10, pady=2)
        ttk.Button(r1, text='Host 1v1', command=lambda: self._server_cmd('create', size=2, game_mode=_gmode(), arena=_arena())).pack(side='left')
        ttk.Button(r1, text='Host 2v2', command=lambda: self._server_cmd('create', size=4, game_mode=_gmode(), arena=_arena())).pack(side='left', padx=4)
        ttk.Button(r1, text='Host 5v5', command=lambda: self._server_cmd('create', size=10, game_mode=_gmode(), arena=_arena())).pack(side='left')
        ttk.Button(r1, text='Host 25v25', command=lambda: self._server_cmd('create', size=50, game_mode=_gmode(), arena=_arena())).pack(side='left', padx=4)
        ttk.Button(r1, text='Spectate', command=self._lobby_watch).pack(side='right')
        ttk.Button(r1, text='Join', command=self._lobby_join).pack(side='right', padx=4)
        sec('YOUR GAME').pack(fill='x', padx=10, pady=(8, 0))
        self.lobby_members = tk.Label(self.mode_opts, text='Not in a game', bg=PANEL, fg=FG,
                                      justify='center', anchor='center', font=('Segoe UI', 9))
        self.lobby_members.pack(fill='x', padx=10, pady=2)
        r2 = tk.Frame(self.mode_opts, bg=PANEL); r2.pack(fill='x', padx=10, pady=2)
        ttk.Button(r2, text='Blue', command=lambda: self._select_team('Blue')).pack(side='left')
        ttk.Button(r2, text='Red', command=lambda: self._select_team('Red')).pack(side='left', padx=4)
        ttk.Button(r2, text='Leave', command=lambda: self._server_cmd('leave')).pack(side='left')
        ttk.Button(r2, text='Start', command=lambda: self._server_cmd('start')).pack(side='right')
        ttk.Button(r2, text='Ready', command=self._lobby_ready).pack(side='right', padx=4)
        r3 = tk.Frame(self.mode_opts, bg=PANEL); r3.pack(fill='x', padx=10, pady=(6, 2))
        tk.Label(r3, text='Invite', bg=PANEL, fg=MUTED, font=('Segoe UI', 9)).pack(side='left')
        self.invite_var = tk.StringVar(value='')
        self.invite_box = ttk.Combobox(r3, textvariable=self.invite_var, state='readonly', width=24, values=())
        self.invite_box.pack(side='left', padx=6)
        ttk.Button(r3, text='Invite', command=self._lobby_invite).pack(side='left')
        self.invite_in = tk.Frame(self.mode_opts, bg=PANEL)
        self.invite_in_lbl = tk.Label(self.invite_in, text='', bg=PANEL, fg=GOLD, font=('Segoe UI', 9, 'bold'))
        self.invite_in_lbl.pack(side='left')
        ttk.Button(self.invite_in, text='Decline', command=self._invite_decline).pack(side='right')
        ttk.Button(self.invite_in, text='Accept', command=self._invite_accept).pack(side='right', padx=4)
        self.assets_info = tk.Label(self.mode_opts, text='Assets: checking …', bg=PANEL, fg=MUTED,
                                    justify='center', anchor='center', font=('Segoe UI', 8))
        self.assets_info.pack(fill='x', padx=10, pady=(6, 6))
        self._game_mode_picked = False   # starter alltid på «Choose game mode» (brukerønske 2026-11-17)
        (self.mode_opts if self._game_mode_picked else self.mode_pick).pack(fill='x')
        if self._game_mode_picked:
            self.mode_title.config(text=self.game_mode_var.get())
        # --- Radio Jukebox på PvP-menyen ---
        self.jukebox_fr = tk.Frame(lc, bg=FIELD, highlightthickness=1, highlightbackground=BORDER)
        self.jukebox_fr.pack(fill='x', padx=10, pady=(2, 8))
        jb_top = tk.Frame(self.jukebox_fr, bg=FIELD); jb_top.pack(fill='x', padx=8, pady=(5, 2))
        jb_title_in = tk.Frame(jb_top, bg=FIELD); jb_title_in.pack(anchor='center')
        tk.Label(jb_title_in, text='♪ Radio Jukebox', bg=FIELD, fg=GOLD, font=('Segoe UI', 9, 'bold')).pack(side='left')
        self.jukebox_now = tk.Label(jb_title_in, text='', bg=FIELD, fg=FG, font=('Segoe UI', 8))
        self.jukebox_now.pack(side='left', padx=8)
        jb_ctrl = tk.Frame(self.jukebox_fr, bg=FIELD); jb_ctrl.pack(fill='x', padx=8, pady=(2, 6))
        jb_ctrl_in = tk.Frame(jb_ctrl, bg=FIELD); jb_ctrl_in.pack(anchor='center')
        ttk.Button(jb_ctrl_in, text='◀', width=3, command=lambda: self._jukebox_step(-1)).pack(side='left')
        self.jukebox_track_var = tk.StringVar(value='')
        self.jukebox_box = ttk.Combobox(jb_ctrl_in, textvariable=self.jukebox_track_var, state='readonly', width=24,
                                        values=[lbl for _, lbl in self.PVP_JUKEBOX_TRACKS])
        self.jukebox_box.pack(side='left', padx=4)
        self.jukebox_box.bind('<<ComboboxSelected>>', self._jukebox_on_select)
        ttk.Button(jb_ctrl_in, text='▶', width=3, command=lambda: self._jukebox_step(1)).pack(side='left')
        self.jukebox_mute_btn = ttk.Button(jb_ctrl_in, text='Mute', width=6, command=self._jukebox_toggle_mute)
        self.jukebox_mute_btn.pack(side='left', padx=(8, 0))
        self._jukebox_refresh()
        # Butikken ligger i spillet (NPC i lobbyen), ikke i GUI-et.

        # Interne liv-/statusfelt beholdes fordi spillogikken oppdaterer dem, men panelet
        # vises ikke lenger: PvP-lobbyen og spillet selv viser informasjonen bedre.
        _o, ic = card(root, "Life and inventory")
        _o.pack_forget()
        inv_top = tk.Frame(ic, bg=PANEL); inv_top.pack(fill="x", padx=10, pady=(4, 2))
        self.hearts_lbl = tk.Label(inv_top, text="♥ You: waiting …", bg=PANEL, fg=HEART, font=("Segoe UI", 12, "bold"), anchor="w")
        self.hearts_lbl.pack(side="left")
        self.friend_hearts_lbl = tk.Label(inv_top, text="♥ Friend: offline", bg=PANEL, fg=MUTED, font=("Segoe UI", 12, "bold"), anchor="e")
        self.friend_hearts_lbl.pack(side="right")
        self.peer_color_lbl = tk.Label(ic, text="", bg=PANEL, fg=GOLD, font=("Segoe UI", 8, "italic"), anchor="w")
        self.peer_color_lbl.pack(fill="x", padx=10, pady=(0, 2))
        self.status = tk.Label(ic, text="Starting up and connecting to Lichii …", bg=PANEL, fg=FG, justify="left", anchor="w",
                               font=("Segoe UI", 9))
        self.status.pack(fill="x", padx=10, pady=(0, 8))

        # --- Chat ---
        chat_outer = tk.Frame(root, bg=GOLD_D, padx=1, pady=1)
        chat_outer.pack(fill="both", expand=True, padx=14, pady=(4, 12))
        chat_frame = tk.Frame(chat_outer, bg=PANEL); chat_frame.pack(fill="both", expand=True)
        chat_hdr = tk.Frame(chat_frame, bg=PANEL); chat_hdr.pack(fill="x", padx=10, pady=(6, 0))
        self.cmd_btn = ttk.Button(chat_hdr, text="Commands", command=self._show_commands)   # v0.94.298: bare for Story-hosten
        self.cmd_btn.place(relx=1.0, rely=0.5, anchor="e")
        self.root.after(1500, self._cmd_btn_tick)
        tk.Label(chat_hdr, text="Chat", bg=PANEL, fg=GOLD, font=(ZELDA_FONT, 17, "bold")).pack(anchor="center")
        chat_in_row = tk.Frame(chat_frame, bg=PANEL)
        chat_in_row.pack(side="bottom", fill="x", padx=10, pady=(4, 8))
        self.chat_var = tk.StringVar()
        self.chat_entry = ttk.Entry(chat_in_row, textvariable=self.chat_var)
        self.chat_entry.pack(side="left", fill="x", expand=True, padx=(0, 6))
        self.chat_entry.bind("<Return>", lambda _e: self._send_chat())
        self.chat_log = tk.Text(chat_frame, height=16, bg=FIELD, fg=FG, insertbackground=FG, relief="flat",
                                highlightthickness=1, highlightbackground=BORDER, font=("Segoe UI", 9), wrap="word",
                                state="disabled", padx=8, pady=6, cursor="hand2")
        self.chat_log.pack(side="top", fill="both", expand=True, padx=10, pady=(4, 0))
        self.chat_log.bind("<Button-1>", lambda _e: self._open_chat_window())
        self.chat_log.tag_configure("sys", foreground=MUTED, font=("Segoe UI", 8, "italic"))
        for cname, chex in HAT_COLORS.items():
            self.chat_log.tag_configure(f"col_{cname}", foreground=chex, font=("Segoe UI", 9, "bold"))
        self._append_chat_sys(f"Welcome to Zelda Multiplayer {VERSION}! Type a message below to chat with your friend.")

        # Skjulte variabler for bakoverkompatibilitet (markør/skygge styres nå fra config, standard av når Link 2 er aktiv)
        self.marker_var = tk.BooleanVar(value=bool(self.cfg.get("marker", False)))
        self.ghost_var = tk.BooleanVar(value=bool(self.cfg.get("ghost", False)))
        self.folg_var = tk.BooleanVar(value=bool(self.cfg.get("figur_folg_meg", False)))

        log(f"start, IP {', '.join(local_ips())}, config {CFG}")
        self._net_setup()
        def read_assets():
            try:
                ah, files = asset_manifest()
                self.asset_hash = ah
                self.asset_files = files
                self._assets_sent_key = None
                if not ah:
                    log('assets: ikke funnet')
                    return
                cats = {}
                for rel in files:
                    c = _asset_category(rel)
                    cats[c] = cats.get(c, 0) + 1
                log(f'assets: {ah} ({len(files)} filer: {cats})')
                for rel, (sz, fh) in sorted(files.items()):
                    log(f'assets:   [{_asset_category(rel)}] {rel} ({sz} B, {fh})')
                if getattr(self, 'friend_assets', None):
                    self._log_asset_diff()
            except OSError as e:
                log(f'assets: kontrollsum feilet {e!r}')
        threading.Thread(target=read_assets, daemon=True, name='AssetFingerprint').start()
        threading.Thread(target=self._worker, daemon=True).start()
        threading.Thread(target=self._fast_net_loop, daemon=True).start()
        root.after(50, self._tick)

    # ------------------------------------------------------------ ui-hjelpere (tråd-sikre)
    def ui(self, fn, *a):
        self.ui_q.put((fn, a))

    def set_check(self, key, state, info=""):
        def f():
            pair = self.checks.get(key)
            if not pair:
                return
            dot, lbl = pair
            dot.config(fg={"ok": OK, "work": WARN, "off": MUTED, "err": "#e05050"}[state]); lbl.config(text=info)
        self.ui(f)

    def show_guide(self, text, entry=False, button="OK"):
        """Vis veiledning og vent på svar fra brukeren (kalles fra arbeidstråden)."""
        def f():
            self.guide.pack(fill="x", padx=12, pady=6, after=self._status_row)
            self.guide_lbl.config(text=text)
            self.guide_entry.pack_forget(); self.guide_btn.pack_forget()
            if entry:
                self.guide_entry.delete(0, "end"); self.guide_entry.pack(side="left", padx=10, pady=(0, 8))
                self.guide_entry.focus_set()
            self.guide_btn.config(text=button); self.guide_btn.pack(side="left", padx=10, pady=(0, 8))
        while not self.answer.empty():
            self.answer.get_nowait()
        self.ui(f)
        return self.answer.get()

    def hide_guide(self):
        self.ui(self.guide.pack_forget)

    def _guide_ok(self):
        self.answer.put(self.guide_entry.get().strip())

    def progress(self, frac):
        def f():
            if not self.prog.winfo_ismapped():
                self.prog.pack(fill="x", padx=12, after=self._status_row)
            self.prog["value"] = frac
            if frac >= 1:
                self.prog.pack_forget()
        self.ui(f)

    def _ghost_toggled(self):
        self.cfg["ghost"] = bool(self.ghost_var.get()); save_cfg(self.cfg)
        log(f"skyggefigur {'på' if self.cfg['ghost'] else 'av'}")

    # v0.94.283: en fe (Navi) ved hver spiller-dukke. Spillets egen Npc_Navi hang spillet (har «følg spilleren»-hjerne).
    # Dm_Npc_Navi (cutscene-Navi) har bare event-AI: lages med create_actor og flyttes via fysikk-kroppen som Link.
    # Regler fra tidligere heng: aldri lage under sonelasting/teleport, aldri flytte en død aktør, aldri slette (parker).
    FAIRY_ACTOR = 'Dm_Npc_Navi'
    # v0.94.290: CoopFairy (tools/fairy_pack.py) = Dm_Npc_Navi med Naviens Wait-animasjon, så vingene blafrer.
    # Brukes når pakken finnes i romfs og spillet faktisk kan lage den (krever omstart etter pakking); ellers Dm_Npc_Navi.
    FAIRY_COOP = 'CoopFairy'

    @property
    def fairy_actor(self):
        ok = getattr(self, '_fairy_coop_ok', None)
        if ok is None:
            ok = self._fairy_coop_ok = os.path.isfile(os.path.join(TUNIC_DIR, 'romfs', 'Pack', 'Actor', self.FAIRY_COOP + '.pack.zs'))
            log(f"fe: bruker {self.FAIRY_COOP if ok else self.FAIRY_ACTOR} ({'pakke funnet' if ok else 'ingen CoopFairy-pakke'})")
        return self.FAIRY_COOP if ok else self.FAIRY_ACTOR
    FAIRY_MAX = 8

    def _fairy_move(self, p, a, x8, pos, yaw=None):
        """Som Link-teleporten: matrise i fysikk-kroppen + flagg |7 (move_actor sin |3 flyttet ikke Dm_Npc_Navi).
        v0.94.290: yaw (radianer) snur feen i fartsretningen (ellers fløy den sidelengs rundt dukken)."""
        try:
            h = p.base + x8
            m = list(struct.unpack('<12f', p.read(h + 0x1D0, 48)))
            m[3], m[7], m[11] = pos
            if yaw is not None:
                c_, s_ = math.cos(yaw), math.sin(yaw)
                m[0], m[1], m[2] = c_, 0.0, s_
                m[4], m[5], m[6] = 0.0, 1.0, 0.0
                m[8], m[9], m[10] = -s_, 0.0, c_
            p.write(h + 0x1D0, struct.pack('<12f', *m))
            w = struct.unpack('<I', p.read(h + 0x228, 4))[0]
            p.write(h + 0x228, struct.pack('<I', w | 7))
            # v0.94.292: aktøren kan løsne fra fysikk-kroppen (sett på GAMER2: fe og navneskilt ble stående ~130 m unna
            # mens kroppen fulgte dukken). Aktørens egen posisjon/rotasjon skrives derfor også – da tegnes den der igjen.
            p.write(p.base + a + 0x31C, struct.pack('<3f', *pos))
            if yaw is not None:
                p.write(p.base + a + 0x328, struct.pack('<9f', m[0], m[1], m[2], m[4], m[5], m[6], m[8], m[9], m[10]))
        except OSError:
            pass

    def _fairy_lost(self, p, a):
        """v0.94.290: fe parkert 200 m ned (eldre versjoner) – CoopFairy-aktøren blir liggende der selv om fysikk-kroppen
        flyttes, og ville tegnes under bakken. Slike tas ikke inn igjen."""
        try:
            fy = p.f32(a + 0x320); my = p.f32(self.pad.p_act + 0x320)
        except (OSError, TypeError):
            return False
        if fy < my - 50.0:
            log(f'fe: 0x{a:X} ligger {my - fy:.0f} m under spilleren (gammel parkering) – brukes ikke')
            return True
        return False

    def _fairy_park_leftovers(self, p, now, zone):
        """v0.94.298: feer fra Story (eller før modd-omstart) ble hengende i lufta i PvP. Våre CoopFairy (aldri spillets
        Dm_Npc_Navi) parkeres 3 m under bakken, én gang per sone, når sonen er ferdig lastet."""
        pad = self.pad
        st = self.__dict__.setdefault('_fairy_off', {})
        if st.get('zone') == zone or self.fairy_actor != self.FAIRY_COOP:
            return
        if (not pad.cur_banc or now - getattr(pad, '_banc_since', now) < 12.0 or now < getattr(pad, '_tp_t', 0) + 8.0
                or not pad._zone_ready(p, now)):
            return
        st['zone'] = zone
        n = 0
        self.__dict__.pop('_fairy', None)   # Story-tilstanden gjelder ikke lenger
        for a0 in (pad._list_actors_raw(p, prefix=self.FAIRY_COOP) or {}):
            x0 = pad.actor_x8(p, a0)
            if x0 and pad.navi_ready(p, a0, x0):
                try:
                    lp = p.f32(pad.p_act + 0x31C, 3)
                    self._fairy_move(p, a0, x0, (lp[0], lp[1] - 3.0, lp[2]))
                    n += 1
                except OSError:
                    pass
        if n:
            log(f'fe: parkerte {n} fe(er) under bakken (ikke Story)')

    def _coop_fairies(self, p, now, entries, zone):
        pad = self.pad
        if not self.cfg.get('coop_fairies', True) or getattr(self, 'mode', 'Story') != 'Story':   # bare Story (ingen feer i PvP)
            self._fairy_park_leftovers(p, now, zone)
            return
        self.__dict__.pop('_fairy_off', None)   # tilbake i Story: parker på nytt neste gang det byttes bort
        st = self.__dict__.setdefault('_fairy', {'zone': None})
        if st.get('zone') != zone:
            st.clear(); st.update(zone=zone, pool=[], owner={}, parked=set(), spawns=0, spawn_t=0.0, busy=False, known=None)
        if (not pad.cur_banc or now - getattr(pad, '_banc_since', now) < 12.0 or now < getattr(pad, '_tp_t', 0) + 8.0
                or not pad._zone_ready(p, now)):
            return
        if st['known'] is None:
            # Feer som finnes fra før (f.eks. fra forrige modd-start i samme spill) gjenbrukes – ellers hoper de seg opp.
            # Bare når ingen cutscene kjører (da kan en Dm_Npc_Navi være spillets egen).
            if pad.event_busy(p) is not None:
                return
            st['known'] = set()
            for a0 in (pad._list_actors_raw(p, prefix=self.fairy_actor) or {}):
                x0 = pad.actor_x8(p, a0)
                if x0 and pad.navi_ready(p, a0, x0) and not self._fairy_lost(p, a0):
                    st['pool'].append((a0, x0))
            if st['pool']:
                log(f"fe: gjenbruker {len(st['pool'])} fe(er) som fantes fra før")
        # v0.94.289: feer som dukket opp senere enn 1 s etter create_actor ble aldri tatt inn (fantes, men ble ikke styrt,
        # og nye ble laget i stedet). Hvert 3. s: alle Dm_Npc_Navi som ikke er våre tas inn i bassenget (ikke under cutscene).
        if not st['busy'] and now - st.get('sweep_t', 0) > 3.0 and pad.event_busy(p) is None:
            st['sweep_t'] = now
            found = pad._list_actors_raw(p, prefix=self.fairy_actor) or {}
            st['total'] = len(found)
            mine = {a for a, _ in st['pool']} | {a for a, _ in st['owner'].values()}
            for a0 in found:
                if a0 not in mine and a0 not in st['known']:
                    x0 = pad.actor_x8(p, a0)
                    if self._fairy_lost(p, a0):
                        st['known'].add(a0); continue
                    if x0 and pad.navi_ready(p, a0, x0):
                        st['pool'].append((a0, x0)); st['adopted'] = st.get('adopted', 0) + 1
                        log(f'fe: tok inn usporet fe 0x{a0:X} (forsinket spawn)')
        names = {e[0]: e[1] for e in entries}
        for nm in list(st['owner']):   # spilleren er borte: fe tilbake i bassenget (parkeres)
            if nm not in names:
                st['pool'].append(st['owner'].pop(nm))
        for nm in names:
            if nm in st['owner']:
                continue
            if st['pool']:
                st['owner'][nm] = st['pool'].pop()
                continue
            if (not st['busy'] and not self.__dict__.get('_glyph', {}).get('busy')   # v0.94.291: aldri to create_actor samtidig
                  and st['spawns'] < self.FAIRY_MAX and now - st['spawn_t'] > 4.0
                  and not (st.get('miss') and now - st['spawn_t'] < 10.0)):   # forrige fant ingen: gi den tid til å dukke opp
                st['busy'] = True; st['spawn_t'] = now; st['spawns'] += 1
                lp = self._plate_pos(p, names[nm], st)   # v0.94.298: fysikk-kroppens posisjon (+0x31C kunne stå igjen etter teleport)
                if lp is None:
                    st['busy'] = False; continue
                def _spawn(pos=(lp[0], lp[1] + 1.5, lp[2])):
                    try:
                        fa_ = self.fairy_actor
                        r = pad.create_actor(p, fa_, list(pos))
                        if not r and fa_ == self.FAIRY_COOP:   # spillet kjenner ikke CoopFairy ennå (ikke startet på nytt)
                            self._fairy_coop_ok = False; st['spawns'] -= 1
                            log('fe: CoopFairy kunne ikke lages – bruker Dm_Npc_Navi til spillet startes på nytt')
                            return
                        time.sleep(1.0)
                        found = pad._list_actors_raw(p, prefix=self.fairy_actor) or {}
                        mine = {a for a, _ in st['pool']} | {a for a, _ in st['owner'].values()}
                        new = [a for a in found if a not in st['known'] and a not in mine]
                        st['miss'] = not new
                        for a in new[:1]:
                            x8 = pad.actor_x8(p, a)
                            if x8 and pad.navi_ready(p, a, x8):
                                st['pool'].append((a, x8))
                                if fa_ == self.FAIRY_COOP:   # v0.94.290: Naviens vente-animasjon (vingene blafrer)
                                    log(f"fe: Wait-animasjon -> {pad.play_anim(p, a, self.cfg.get('fairy_anim', 'Wait'))}, nå {pad.read_anim(p, a)}")
                        log(f'fe: laget {self.fairy_actor} -> {r}, {len(new)} ny(e), basseng {len(st["pool"])}')
                    except Exception as e:  # noqa: BLE001
                        log(f'fe: spawn-feil {e!r}')
                    finally:
                        st['busy'] = False
                threading.Thread(target=_spawn, daemon=True, name='FairySpawn').start()
        for nm, (a, x8) in list(st['owner'].items()):
            if not pad.navi_ready(p, a, x8):   # død aktør flyttes aldri
                st['owner'].pop(nm, None); continue
            lp = self._plate_pos(p, names[nm], st)   # v0.94.298: der dukken faktisk tegnes
            if lp is None:
                continue
            ph = (hash(nm) % 628) / 100.0
            ang = now * 1.3 + ph
            pos = (lp[0] + 0.55 * math.cos(ang), lp[1] + 1.35 + 0.12 * math.sin(now * 3.1 + ph), lp[2] + 0.55 * math.sin(ang))
            self._fairy_move(p, a, x8, pos, -ang + math.radians(float(self.cfg.get('fairy_yaw_off', 0))))
            st['parked'].discard(a)
        if now - st.get('log_t', 0) > 10:
            st['log_t'] = now
            try:
                log('fe: ' + ', '.join(f"{nm} dukke {[round(v, 1) for v in (self._plate_pos(p, names[nm], st) or (0, 0, 0))]} fe@0x{a:X} {[round(v, 1) for v in p.f32(a + 0x31C, 3)]} x8 {[round(v, 1) for v in (p.f32(_x + 0x1DC), p.f32(_x + 0x1EC), p.f32(_x + 0x1FC))]}"
                                       for nm, (a, _x) in st['owner'].items() if nm in names) + f" | ledige {len(st['pool'])}, i scenen {st.get('total', '?')}, tatt inn {st.get('adopted', 0)}")
            except OSError:
                pass
        for a, x8 in st['pool']:   # ledige feer parkeres 3 m under bakken (sletting hang tidligere)
            if a not in st['parked'] and pad.navi_ready(p, a, x8):
                try:
                    lp = p.f32(a + 0x31C, 3)
                    self._fairy_move(p, a, x8, (lp[0], lp[1] - 3.0, lp[2]))   # v0.94.290: 200 m ned løsnet CoopFairy fra fysikk-kroppen
                    st['parked'].add(a)
                except OSError:
                    pass

    # ------------------------------------------------------------------ v0.94.291: navneskilt i spillet
    # Én aktør per tegn: CoopGlyph_<A-Z/0-9> (tools/glyph_pack.py) = Kokiri-treskilt-aktøren med Kakariko-plakatens
    # modell (v0.94.293; gjennomsiktig «mask»-materiale, skalert via rotbeinet) og egen tekstur (hvit bokstav, svart kant). Et navn = en rad slike skilt over hodet til dukken,
    # snudd mot kameraet og flyttet via fysikk-kroppen som feene. Samme regler som feene: aldri lage under sonelasting,
    # aldri flytte en død aktør, aldri slette (ledige parkeres under bakken). Krever omstart av spillet etter pakking.
    GLYPH_PREFIX = 'CoopGlyph_'
    GLYPH_CHARS = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789'
    GLYPH_MAX = 48            # tegn-aktører per sone
    GLYPH_W = 0.055           # v0.94.294: mindre bokstaver (skala 0,11, ~7 cm); v0.94.293: bare tekst (Kakariko-plakat, materiale «mask», skala 0,15) – tett som vanlig skrift
    GLYPH_H = 1.3             # plakatens origo over dukkens føtter (bokstaven ~0,1 m høy)

    GLYPH_TEAM = {'Red': 'R', 'Blue': 'B'}   # v0.94.295: PvP-lagfarge -> CoopGlyphR_/CoopGlyphB_ (hvit = CoopGlyph_)

    def _glyph_actor(self, ch, col=''):
        return f'CoopGlyph{col}_{ch}'

    def _glyph_ok(self, ch, col=''):
        key = self._glyph_actor(ch, col)
        have = self.__dict__.setdefault('_glyph_have', {})
        if key not in have:
            have[key] = os.path.isfile(os.path.join(TUNIC_DIR, 'romfs', 'Pack', 'Actor', f'{key}.pack.zs'))
        return have[key] and key not in self.__dict__.setdefault('_glyph_bad', set())

    def _plate_text(self, nm):
        return ''.join(c for c in str(nm).upper() if c in self.GLYPH_CHARS and self._glyph_ok(c))[:10]

    def _plate_glyphs(self, nm, col=''):
        """Navnet som aktørnavn (ett per tegn), i lagfargen når den finnes – ellers hvitt."""
        return tuple(self._glyph_actor(c, col) if col and self._glyph_ok(c, col) else self._glyph_actor(c)
                     for c in self._plate_text(nm))

    def _plate_pos(self, p, a, st):
        """v0.94.296: der figuren faktisk tegnes = fysikk-kroppens matrise (x8 +0x1DC/+0x1EC/+0x1FC). akt+0x31C kunne stå
        igjen etter teleport (PvP-lobbyen: navnet 10 m foran Link). Reserve: +0x31C."""
        pad = self.pad
        c = st.setdefault('x8c', {})
        x8 = c.get(a)
        if x8 is None:
            x8 = c[a] = pad.actor_x8(p, a) or 0
        try:
            if x8:
                t = (p.f32(x8 + 0x1DC), p.f32(x8 + 0x1EC), p.f32(x8 + 0x1FC))
                if all(math.isfinite(v) and abs(v) < 1e5 for v in t) and abs(t[0]) + abs(t[1]) + abs(t[2]) > 1.0:
                    return t
            return p.f32(a + 0x31C, 3)
        except OSError:
            c.pop(a, None)
            return None

    def _plate_colors(self, names):
        """v0.94.295: PvP = lagfarge per spiller (rød/blå, tilskuer hvit); Story = hvit."""
        if getattr(self, 'mode', 'Story') != 'PvP':
            return {}
        teams = {pe.get('name'): pe.get('team') for pe in (getattr(self, 'pvp_peers', ()) or ()) if isinstance(pe, dict)}
        try:
            teams[self.name] = self._active_pvp_team()
        except Exception:  # noqa: BLE001
            pass
        return {nm: self.GLYPH_TEAM.get(teams.get(nm), '') for nm in names}

    # ------------------------------------------------------------------ v0.94.307: Z-sikting (Navi) på andre spillere
    # Dukkene kan ikke siktes på (ingen AttentionSender; å legge den inn i dukkepakkene gjorde at de ikke ble laget).
    # tools/target_pack.py lager CoopTarget_E: treskilt-aktøren med fiendens AttentionSender (EnemyCommon LockOn/AutoAim)
    # og usynlig modell. Én per motstander, flyttet til dukkens bryst hver tikk (som navneskiltene). Testet 2026-11-23:
    # Z ved målet -> LockOnWait/LockOnTurn; Z uten mål -> Wait. Standard bare i PvP (cfg z_target: pvp|all|off).
    ZTGT_ACTOR = 'CoopTarget_E'
    ZTGT_H = 1.6   # v0.94.309: 0.9 ga låsepilen under bakken på GAMER; 1.6 bekreftet over bakken (2026-11-23)

    def _z_opponents(self, names):
        mode = str(self.cfg.get('z_target', 'pvp')).lower()
        cur = getattr(self, 'mode', 'Story')
        if mode == 'off' or (mode == 'pvp' and cur != 'PvP'):
            return set()
        if cur != 'PvP':
            return set(names)
        teams = {pe.get('name'): pe.get('team') for pe in (getattr(self, 'pvp_peers', ()) or ()) if isinstance(pe, dict)}
        try:
            mine = self._active_pvp_team()
        except Exception:  # noqa: BLE001
            mine = None
        # lagspill: bare motstanderlaget; deathmatch/uten lag: alle
        return {nm for nm in names if not (mine in ('Red', 'Blue') and teams.get(nm) == mine)}

    def _nearest_opp_puppet(self):
        """v0.94.307: nærmeste motstander-dukke (vert-offset) – angriperen for tilbakeslag når Link 2 (c_act) ikke finnes."""
        try:
            seen_t, pups = getattr(self, '_puppets_seen', (0, {}))
            me = self.pad.my_apos(self.p)
            if time.time() - seen_t > 1.0 or not pups or not me:
                return None
            opp = self._z_opponents_pvp(pups)
            best = None
            for nm_, act_ in pups.items():
                if nm_ in opp:
                    pos_ = self.p.f32(act_ + 0x31C, 3)
                    dd = math.dist(pos_, me)
                    if best is None or dd < best[0]:
                        best = (dd, act_)
            return best[1] if best else None
        except Exception:  # noqa: BLE001
            return None

    def _z_opponents_pvp(self, names):
        """Motstandere i PvP uansett cfg z_target (treff-sjekken)."""
        teams = {pe.get('name'): pe.get('team') for pe in (getattr(self, 'pvp_peers', ()) or ()) if isinstance(pe, dict)}
        try:
            mine = self._active_pvp_team()
        except Exception:  # noqa: BLE001
            mine = None
        return {nm for nm in names if not (mine in ('Red', 'Blue') and teams.get(nm) == mine)}

    def _coop_targets(self, p, now, entries, zone):
        pad = self.pad
        self._puppets_seen = (now, {e[0]: e[1] for e in entries if e[0] != self.name})   # v0.94.307: brukes av _pvp_swing
        # v0.94.310: nettverksposisjonen (e[2]) er sann posisjon. Dukkens fysikk-kropp kunne stå fast et gammelt sted
        # (GAMER2: Z-målet for Pat sto 5 min på samme punkt mens Pat gikk rundt).
        net_pos = {}
        for e in entries:
            try:
                q = e[2]
                if e[0] != self.name and len(q) >= 3 and all(math.isfinite(float(v)) and abs(float(v)) < 1e5 for v in q[:3]):
                    net_pos[e[0]] = (float(q[0]), float(q[1]), float(q[2]))
            except (TypeError, ValueError, IndexError):
                pass
        self._puppets_pos = (now, net_pos)
        st = self.__dict__.setdefault('_ztgt', {'zone': None})
        if st.get('ok') is None:
            st['ok'] = os.path.isfile(os.path.join(TUNIC_DIR, 'romfs', 'Pack', 'Actor', f'{self.ZTGT_ACTOR}.pack.zs'))
            if not st['ok']:
                log(f'z-mål: {self.ZTGT_ACTOR} finnes ikke i romfs (tools/target_pack.py) – Z-sikting på spillere av')
        if not st['ok']:
            return
        if st.get('zone') != zone:
            st.clear(); st.update(ok=True, zone=zone, free=[], owner={}, parked=set(), busy=False, spawn_t=0.0, spawns=0, known=None)
        names = {e[0]: e[1] for e in entries if e[0] != self.name}
        want = self._z_opponents(names)
        if now - st.get('dbg_t', 0) > 30:
            st['dbg_t'] = now
            log(f"z-mål: zt={self.cfg.get('z_target')} modus={getattr(self, 'mode', None)} sone={zone} banc={pad.cur_banc} navn={list(names)} vil={sorted(want)} eiere={list(st['owner'])} "
                f"ledige={len(st['free'])} kjent={None if st['known'] is None else len(st['known'])}")
        if (not pad.cur_banc or now - getattr(pad, '_banc_since', now) < 12.0 or now < getattr(pad, '_tp_t', 0) + 8.0
                or not pad._zone_ready(p, now)):
            return
        if st['known'] is None:   # mål fra forrige modd-start i samme spill/sone gjenbrukes
            if pad.event_busy(p) is not None:
                return
            st['known'] = set()
            for a0 in (pad._list_actors_raw(p, prefix=self.ZTGT_ACTOR) or {}):
                x0 = pad.actor_x8(p, a0)
                if x0 and pad.navi_ready(p, a0, x0):
                    st['free'].append((a0, x0))
                st['known'].add(a0)
        for nm in list(st['owner']):
            if nm not in want:
                st['free'].append(st['owner'].pop(nm))
        for nm in want:
            if nm in st['owner']:
                continue
            if st['free']:
                st['owner'][nm] = st['free'].pop()
                continue
            if st['busy'] or self.__dict__.get('_fairy', {}).get('busy') or self.__dict__.get('_glyph', {}).get('busy') \
                    or st['spawns'] >= 8 or now - st['spawn_t'] < 1.5:
                continue
            try:
                lp = p.f32(names[nm] + 0x31C, 3)
            except OSError:
                continue
            st['busy'] = True; st['spawn_t'] = now; st['spawns'] += 1

            def _spawn(pos=(lp[0], lp[1] - 3.0, lp[2])):
                try:
                    r = pad.create_actor(p, self.ZTGT_ACTOR, list(pos))
                    if not r:
                        st['ok'] = False
                        log(f'z-mål: {self.ZTGT_ACTOR} kunne ikke lages – start spillet på nytt etter pakking')
                        return
                    time.sleep(1.0)
                    mine = set(a for a, _ in st['owner'].values()) | {a for a, _ in st['free']}
                    for a in (pad._list_actors_raw(p, prefix=self.ZTGT_ACTOR) or {}):
                        if a in st['known'] or a in mine:
                            continue
                        st['known'].add(a)
                        x8 = pad.actor_x8(p, a)
                        if x8 and pad.navi_ready(p, a, x8):
                            st['free'].append((a, x8))
                    log(f'z-mål: laget {self.ZTGT_ACTOR} -> {r}')
                except Exception as e:  # noqa: BLE001
                    log(f'z-mål: spawn-feil {e!r}')
                finally:
                    st['busy'] = False
            threading.Thread(target=_spawn, daemon=True, name='ZTargetSpawn').start()
        pst = self.__dict__.setdefault('_glyph', {})
        for nm, (a, x8) in list(st['owner'].items()):
            if not pad.navi_ready(p, a, x8):   # død/ødelagt: glem den, ny lages
                st['owner'].pop(nm); continue
            lp = net_pos.get(nm) or (self._plate_pos(p, names[nm], pst) if nm in names else None)
            if lp is None:
                continue
            goal = (lp[0], lp[1] + float(self.cfg.get('z_target_height', self.ZTGT_H)), lp[2])
            self._fairy_move(p, a, x8, goal)
            st['parked'].discard(a)
            # v0.94.309: GAMER: Z-låsen satt under bakken. Logg hvor målet faktisk er (kropp og aktør) mot ønsket punkt.
            if now - st.get('pos_t', 0) > 10:
                st['pos_t'] = now
                try:
                    body = (p.f32(x8 + 0x1DC), p.f32(x8 + 0x1EC), p.f32(x8 + 0x1FC))
                    ay = p.f32(a + 0x31C, 3)
                    log(f"z-mål: {nm} mål 0x{a:X} ønsket y={goal[1]:.2f} kropp=({body[0]:.1f},{body[1]:.2f},{body[2]:.1f}) "
                        f"aktør=({ay[0]:.1f},{ay[1]:.2f},{ay[2]:.1f}) kilde=({lp[0]:.1f},{lp[1]:.2f},{lp[2]:.1f}) "
                        f"{'nett' if nm in net_pos else 'dukke'} dukke={self._plate_pos(p, names[nm], pst) if nm in names else None}")
                except (OSError, TypeError):
                    pass
        for a, x8 in st['free']:   # ledige parkeres 6 m under bakken
            if a not in st['parked'] and pad.navi_ready(p, a, x8):
                try:
                    lp = p.f32(a + 0x31C, 3)
                    self._fairy_move(p, a, x8, (lp[0], lp[1] - 6.0, lp[2]))
                    st['parked'].add(a)
                except OSError:
                    pass
        if now - st.get('log_t', 0) > 30 and (st['owner'] or want):
            st['log_t'] = now
            log(f"z-mål: {', '.join(st['owner']) or '-'} (vil ha {', '.join(sorted(want)) or '-'}), ledige {len(st['free'])}, laget {st['spawns']}")

    def _coop_nameplates(self, p, now, entries, zone):
        pad = self.pad
        st = self.__dict__.setdefault('_glyph', {'zone': None})
        on = bool(self.cfg.get('nameplates', True)) and getattr(self, 'mode', 'Story') in ('Story', 'PvP')   # v0.94.295: også PvP
        if not on:
            entries = ()   # slått av: alle tegn tilbake i bassenget og parkeres (under)
            if not st.get('owner'):
                return
        if st.get('zone') != zone:
            st.clear(); st.update(zone=zone, free={}, owner={}, parked=set(), busy=False, spawn_t=0.0, spawns=0, known=None)
        if (not pad.cur_banc or now - getattr(pad, '_banc_since', now) < 12.0 or now < getattr(pad, '_tp_t', 0) + 8.0
                or not pad._zone_ready(p, now)):
            return
        names = {e[0]: e[1] for e in entries}
        if on and self.cfg.get('nameplate_self', True) and pad.p_act is not None and self.name not in names:
            names[self.name] = pad.p_act   # v0.94.294: eget navn over egen Link også
        cols = self._plate_colors(names)
        glyphs = {nm: self._plate_glyphs(nm, cols.get(nm, '')) for nm in names}
        if st['known'] is None:
            # tegn som finnes fra før (forrige modd-start i samme spill/sone) gjenbrukes
            if not names or pad.event_busy(p) is not None:
                return
            st['known'] = set()
            n_ = 0
            # v0.94.296: alle tegn i alle farger (også gamle lagfarger fra før modd-omstart) – ellers ble de hengende i lufta
            for a0, d0 in (pad._list_actors_raw(p, prefix='CoopGlyph') or {}).items():
                ch = d0[0] if isinstance(d0, (tuple, list)) and d0 else None
                if isinstance(ch, str) and ch.startswith('CoopGlyph'):
                    x0 = pad.actor_x8(p, a0)
                    if x0 and pad.navi_ready(p, a0, x0):
                        st['free'].setdefault(ch, []).append((a0, x0)); n_ += 1
                st['known'].add(a0)
            if n_:
                log(f'navneskilt: gjenbruker {n_} tegn som fantes fra før')
        for nm in list(st['owner']):   # spilleren er borte eller navnet endret: tegnene tilbake i bassenget
            if nm not in names or st['owner'][nm]['glyphs'] != glyphs[nm]:   # også nytt lag = ny farge
                for sl in st['owner'].pop(nm)['slots']:
                    if sl:
                        st['free'].setdefault(sl[0], []).append(sl[1:])
        for nm in names:
            txt = glyphs[nm]
            if not txt:
                continue
            o = st['owner'].setdefault(nm, {'text': self._plate_text(nm), 'glyphs': txt, 'col': cols.get(nm, ''),
                                            'slots': [None] * len(txt)})
            for i, ch in enumerate(txt):
                if o['slots'][i] is not None:
                    continue
                if st['free'].get(ch):
                    o['slots'][i] = (ch,) + st['free'][ch].pop()
                    continue
                fairy_busy = self.__dict__.get('_fairy', {}).get('busy')
                if st['busy'] or fairy_busy or st['spawns'] >= self.GLYPH_MAX or now - st['spawn_t'] < 1.5:
                    continue
                try:
                    lp = p.f32(names[nm] + 0x31C, 3)
                except OSError:
                    continue
                st['busy'] = True; st['spawn_t'] = now; st['spawns'] += 1

                def _spawn(ch=ch, pos=(lp[0], lp[1] - 3.0, lp[2])):
                    try:
                        r = pad.create_actor(p, ch, list(pos))
                        if not r:   # spillet kjenner ikke aktøren (pakket etter spillstart)
                            self.__dict__.setdefault('_glyph_bad', set()).add(ch); st['spawns'] -= 1
                            log(f'navneskilt: {ch} kunne ikke lages – start spillet på nytt etter pakking')
                            return
                        time.sleep(1.0)
                        found = pad._list_actors_raw(p, prefix=ch) or {}
                        mine = {sl[1] for o_ in st['owner'].values() for sl in o_['slots'] if sl} | {a for v in st['free'].values() for a, _ in v}
                        new = [a for a in found if a not in st['known'] and a not in mine]
                        for a in new:
                            st['known'].add(a)
                            x8 = pad.actor_x8(p, a)
                            if x8 and pad.navi_ready(p, a, x8):
                                st['free'].setdefault(ch, []).append((a, x8))
                        log(f'navneskilt: laget {ch} -> {r}, {len(new)} ny(e)')
                    except Exception as e:  # noqa: BLE001
                        log(f'navneskilt: spawn-feil {e!r}')
                    finally:
                        st['busy'] = False
                threading.Thread(target=_spawn, daemon=True, name='GlyphSpawn').start()
        # v0.94.296: skiltene står parallelt med skjermen (vendt mot kameraets synsretning). Før: snudd mot kamera-øyet,
        # men når kameraadressen var tapt (cam_off None/ugyldig) ble de snudd mot egen Link -> speilvendt tekst når man
        # snudde kameraet. my_cam_angle har spillets egen kameravinkel (s13 - s9) som reserve – den brukes også av styringen.
        cam_a = None
        try:
            cam_a = pad.my_cam_angle(p, getattr(self, 'cam_off', None))
        except Exception:  # noqa: BLE001
            cam_a = None
        eye = None
        if cam_a is None:
            try:
                eye = p.f32(pad.p_act + 0x31C, 3)
            except (OSError, TypeError):
                eye = None
        yoff = math.radians(float(self.cfg.get('glyph_yaw_off', 0)))
        for nm, o in st['owner'].items():
            if nm not in names:
                continue
            lp = self._plate_pos(p, names[nm], st)
            if lp is None:
                continue
            base = (lp[0], lp[1] + float(self.cfg.get('glyph_height', self.GLYPH_H)), lp[2])
            o['at'] = (round(lp[0], 1), round(lp[1], 1), round(lp[2], 1))
            if cam_a is not None:
                yaw = cam_a + math.pi   # skiltets forside mot kameraet (motsatt synsretningen)
            else:
                yaw = math.atan2(eye[0] - base[0], eye[2] - base[2]) if eye else 0.0
            yaw += yoff
            rx, rz = math.cos(yaw), -math.sin(yaw)   # skiltets +X (leseretning) i verden
            n_ = len(o['slots'])
            for i, sl in enumerate(o['slots']):
                if not sl:
                    continue
                ch, a, x8 = sl
                if not pad.navi_ready(p, a, x8):   # død aktør flyttes aldri
                    o['slots'][i] = None; continue
                k = (i - (n_ - 1) / 2) * float(self.cfg.get('glyph_spacing', self.GLYPH_W))
                self._fairy_move(p, a, x8, (base[0] + rx * k, base[1], base[2] + rz * k), yaw)
                st['parked'].discard(a)
        for ch, lst in st['free'].items():   # ledige tegn parkeres 6 m under bakken
            for a, x8 in lst:
                if a not in st['parked'] and pad.navi_ready(p, a, x8):
                    try:
                        lp = p.f32(a + 0x31C, 3)
                        self._fairy_move(p, a, x8, (lp[0], lp[1] - 6.0, lp[2]))
                        st['parked'].add(a)
                    except OSError:
                        pass
        if now - st.get('log_t', 0) > 15 and st['owner']:
            st['log_t'] = now
            log('navneskilt: ' + ', '.join(f"{nm} '{o['text']}'{('/' + o['col']) if o.get('col') else ''} {sum(1 for s in o['slots'] if s)}/{len(o['slots'])} @{o.get('at')}"
                                           for nm, o in st['owner'].items())
                + f" | ledige {sum(len(v) for v in st['free'].values())}, laget {st['spawns']}"
                + f" | kamera {'-' if cam_a is None else round(math.degrees(cam_a))}° ({'matrise' if getattr(self, 'cam_off', None) else 'spillvinkel'})")

    def _names_toggled(self):
        self.cfg["nameplates"] = bool(self.names_var.get()); save_cfg(self.cfg)
        log(f"navneskilt {'på' if self.cfg['nameplates'] else 'av'} (GUI)")

    def _tvang_toggled(self):
        self.tvang = bool(self.tvang_var.get()); self.cfg["tvang"] = self.tvang; save_cfg(self.cfg)
        log(f"TVANG {'på' if self.cfg['tvang'] else 'av'}")

    def _folg_toggled(self):
        self.cfg["figur_folg_meg"] = bool(self.folg_var.get()); save_cfg(self.cfg)
        log(f"figur følger meg (test) {'på' if self.cfg['figur_folg_meg'] else 'av'}")

    def _marker_toggled(self):
        self.cfg["marker"] = bool(self.marker_var.get()); save_cfg(self.cfg)
        log(f"markør {'på' if self.cfg['marker'] else 'av'}")
        if self.overlay and not self.cfg["marker"]:
            self.overlay.clear()

    def _save_name(self):
        self.name = self.name_var.get().strip() or self.name
        self.cfg["name"] = self.name; save_cfg(self.cfg)

    def _save_mode(self):
        md = self.mode_var.get()
        if md in MODES and md != self.mode:
            self.mode = md; self.cfg['mode'] = md; save_cfg(self.cfg)
            self.pad.suppress_link2 = (md == 'PvP')   # Link 2-spawn utløser EvtWait; aldri samtidig med scenebytte.
            self.pad.share_interact = (md != 'PvP')
            if md != 'PvP':
                self.pad.navi2 = None
            if self.p and self.pad.hR is not None:
                try:
                    self.pad.set_pvp_message_filter(self.p, md == 'PvP')
                except OSError as exc:
                    log(f'pvp-meldingssperre: kunne ikke skrive flagg {exc!r}')
            else:
                self.pad.pvp_message_filter = (md == 'PvP')
            self._mode_generation = getattr(self, '_mode_generation', 0) + 1
            generation = self._mode_generation
            self._ctf_reset_at = 0   # En planlagt CtF-runde skal aldri starte etter retur til Story.
            self._pvp_spawn = None; self._pvp_on_since = time.time()
            log(f'modus valgt: {md}')
            self._pvp_look_tick()
            if md == 'PvP':   # v0.79: FOLLOW bare i Story
                self.follow_cb.pack_forget()   # v0.94.295: NAMES blir stående (navneskilt i lagfarge i PvP)
                self._pvp_lobby_done = False
                self._pvp_travel_retry = 0
                self._pvp_in_arena = False; self._pvp_social_lobby = False
                self._ctf_actors = {}; self._ctf_lit = {}; self._ctf_friend_lit = {}; self._ctf_point_sent = {}
                self.boss_outer.pack_forget(); self._boss_card_shown = False
                self.story_lobby_outer.pack_forget()
                self.lobby_outer.pack(fill='x', padx=14, pady=4, before=self._status_row)
            else:
                if not self.follow_cb.winfo_manager():
                    self.follow_cb.pack(side="left", padx=(10, 0), before=self.names_cb)
                self.lobby_outer.pack_forget()
                self.story_lobby_outer.pack(fill='x', padx=14, pady=4, before=self._status_row)
                self._pvp_in_arena = False; self._pvp_social_lobby = False
                self._ctf_actors = {}; self._ctf_lit = {}; self._ctf_friend_lit = {}; self._ctf_point_sent = {}
                self._reload_due = 0   # Ingen samtidig banc-reload i modusovergangen.
                self._append_chat_sys('🔄 Story mode: go through a door to restore removed enemies and NPCs')
            # Spillkall, teleport og liv må aldri blokkere Tk-hovedtråden.
            threading.Thread(target=self._mode_game_transition, args=(md, generation),
                             daemon=True, name='ModeTransition').start()
            # v0.74: bytt til modusens porter – spillere i en annen modus hører oss ikke
            try:
                ip = self.peer[0] if self.peer else None
                for sk_ in (self.gs, self.ds):
                    sk_.close()
                self._net_setup()
                self.players = {}; self.friend = None; self.friend_session = None
                self.peer = (ip, self.gport) if ip else None
                log(f'nett: {md} bruker porter {self.gport}/{self.dport}')
            except Exception as e:  # noqa: BLE001
                log(f'nett: portbytte feilet {e!r}')
            self._append_chat_sys('⚔️ PvP mode: no sharing, enemies paused, hit your friend! Your spawn is where you stand now.' if md == 'PvP'
                                  else '🤝 Story mode: co-op as before.')

    def _mode_game_transition(self, md, generation):
        """Kort, kansellerbar spilldel av modusbytte; ingen CtF/boss-reset samtidig."""
        try:
            time.sleep(0.35)
            if generation != getattr(self, '_mode_generation', 0) or self.mode != md:
                return
            if md == 'Story':
                self._pvp_leave_lobby()
            self._pvp_set_hp(md == 'PvP')
            self._pvp_set_inv_mode(md == 'PvP')
            log(f'modus: spillovergang til {md} fullført')
        except Exception as e:  # noqa: BLE001
            log(f'modus: spillovergang feilet {e!r}')

    @staticmethod
    def _tunic_mod_dir():
        return os.path.join(os.path.dirname(APP_DIR), "user", "load", "0400486024DEC000", "OoT_MP_Tunic")

    @classmethod
    def _detect_boot_look(cls):
        """v0.94.254: Finn hvilken tunikafarge romfs/Tex/Angin_Tile_A_Alb.bntx.zs hadde da spillet startet."""
        try:
            mod = cls._tunic_mod_dir()
            cur = os.path.join(mod, "romfs", "Tex", "Angin_Tile_A_Alb.bntx.zs")
            if not os.path.isfile(cur):
                return "Green"
            cur_b = open(cur, "rb").read()
            for lk in LOOKS:
                ref = os.path.join(mod, "self", lk.lower(), "Tex", "Angin_Tile_A_Alb.bntx.zs")
                if os.path.isfile(ref) and open(ref, "rb").read() == cur_b:
                    return lk
        except OSError:
            pass
        return "Green"

    @classmethod
    def _sync_own_tunic_romfs(cls, lk):
        """v0.94.254: Kopier valgt farge inn i romfs/Tex/ med én gang så neste oppstart også har riktig farge."""
        import shutil
        col = lk.lower() if lk in LOOKS else None
        if not col:
            return False
        try:
            mod = cls._tunic_mod_dir()
            src_dir = os.path.join(mod, "self", col, "Tex")
            dst_dir = os.path.join(mod, "romfs", "Tex")
            if not os.path.isdir(src_dir) or not os.path.isdir(dst_dir):
                return False
            for fn in ("Angin_Tile_A_Alb.bntx.zs", "Angin_Tile_A_Dark_Alb.bntx.zs"):
                s = os.path.join(src_dir, fn)
                if os.path.isfile(s):
                    shutil.copyfile(s, os.path.join(dst_dir, fn))
            return True
        except OSError as e:
            log(f'tunika: romfs-kopiering feilet ({lk}): {e}')
            return False

    def _account_key(self):
        """Avledet nøkkel for nåværende navn (None = ingen passord satt)."""
        return (self.cfg.get('account_keys') or {}).get(self.name)

    def _save_password(self):
        pw = self.pw_var.get()
        if not pw:
            return
        import hashlib
        key = hashlib.sha256(f"oot-mp-v1:{self.name.strip().lower()}:{pw}".encode()).hexdigest()
        self.pw_var.set('')
        old = self._account_key()
        if old and old != key and getattr(self, '_acct_state', None) in ('ok', 'created'):
            # innlogget: bytt passord på serveren; det nye lagres først når serveren bekrefter
            self._acct_pending_key = key
            self._server_cmd('acct_change', key=old, new_key=key)
            self._append_chat_sys('🔒 Changing password …')
            log(f'konto: ber serveren bytte passord for {self.name}')
            return
        keys = dict(self.cfg.get('account_keys') or {}); keys[self.name] = key
        self.cfg['account_keys'] = keys; save_cfg(self.cfg)
        self._sinv_denied = False
        self._append_chat_sys(f'🔒 Password saved for {self.name}. Your inventory and PvP profile on the server are now tied to it.')
        log(f'konto: passord satt for {self.name} (bare avledet nøkkel lagret)')
        if getattr(self, 'mode', 'Story') == 'Story':   # hent på nytt med nøkkelen
            self._sinv_loaded = False; self._inv_load_pending = time.time(); self._server_cmd('inv_get', key=key)

    PVP_LOOKS = ('Blue', 'Red')   # v0.94.321: i PvP kan man bare være blå eller rød (= laget); andre farger kun i Story

    def _pvp_look_tick(self):
        """PvP: tunikaen følger laget (Blue/Red). Story: tilbake til lagret farge. Lagret Story-farge (cfg) røres ikke."""
        story = self.cfg.get('look') if self.cfg.get('look') in LOOKS else 'Red'
        if getattr(self, 'mode', 'Story') == 'PvP':
            tm = getattr(self, '_pvp_team', None)
            if tm not in self.PVP_LOOKS:
                for pe in ((getattr(self, '_server_state', None) or {}).get('members') or ()):
                    if isinstance(pe, dict) and pe.get('name') == getattr(self, 'name', None) and pe.get('team') in self.PVP_LOOKS:
                        tm = pe.get('team')
            want = tm if tm in self.PVP_LOOKS else (self.look if self.look in self.PVP_LOOKS else
                                                   (story if story in self.PVP_LOOKS else 'Blue'))
            vals = list(self.PVP_LOOKS)
        else:
            want, vals = story, list(LOOKS)
        cb = getattr(self, 'cb_look', None)
        if cb is not None and list(cb.cget('values')) != vals:
            cb.config(values=vals)
        if self.look != want:
            log(f"tunika: {'PvP-lag' if vals != list(LOOKS) else 'Story'} -> {want} (var {self.look})")
            self.look = want; self.pad.my_look = want
            if self.look_var.get() != want:
                self.look_var.set(want)

    def _pvp_look_loop(self):
        try:
            self._pvp_look_tick()
        except Exception as e:  # noqa: BLE001
            log(f'tunika: lagfarge-feil {e!r}')
        self.root.after(1000, self._pvp_look_loop)

    def _save_look(self):
        lk = self.look_var.get()
        if getattr(self, 'mode', 'Story') == 'PvP':
            # v0.94.321: i PvP er fargen = laget; valget bytter lag, Story-fargen beholdes
            if lk in self.PVP_LOOKS:
                self._select_team(lk)
                self._append_chat_sys(f'👕 Team {lk} – the tunic changes in a few seconds.')
                self._pvp_look_tick()
            else:
                self.look_var.set(self.look)
            return
        if lk in LOOKS:
            self.look = lk; self.cfg['look'] = lk; save_cfg(self.cfg); self.pad.my_look = lk
            if lk in ('Red', 'Blue'):
                self._pvp_team = lk
            log(f'utseende valgt: {lk}')
            self._append_chat_sys(f'👕 {lk} lagret – tunikaen byttes om noen sekunder.')

    def _self_tunic_tick(self, now):
        """v0.94.257: overlayen fra v0.94.254 er av.

        Den spawnet CoopPuppet_<farge> og skjulte materialer på dukkene som
        eksterne spillere allerede bruker. Egen farge kommer fra romfs ved
        oppstart (auto_restart.apply_tunic). Denne funksjonen gjør én
        opprydding: vis materialene igjen på egen Link og på dukker i nærheten.
        Den lager ingen nye aktører.
        """
        if getattr(self, '_st_undo_done', False) or getattr(self, '_st_undo_busy', False):
            return
        if not self.ready or self.p is None or self.pad.p_act is None:
            return
        if not self.pad.cur_banc or not self.pad._zone_ready(self.p, now):
            return
        self._st_undo_busy = True
        p, p_act = self.p, self.pad.p_act

        def _show(act, materials):
            if not act or not self.pad.actor_alive(p, act):
                return 0
            n = 0
            for m in materials:
                if self.pad.set_material_visible(p, act, m, True) is not None:
                    n += 1
            return n

        def _undo():
            try:
                pos = self.pad.my_apos(p)
                # v0.94.297: har egen Link et farge-plagg på (Armor_Child_Tunic_*), skal grunn-tunikaen være skjult –
                # å vise den igjen ga to tunikaer oppå hverandre (flimring mellom to farger).
                arm_on = False
                try:
                    if pos is not None:
                        dga = {}; self.pad._scan_full_t = 0; self.pad._scan_actors_raw(p, dga); self.pad._diag_all = None
                        arm_on = any(nm.startswith('Armor_Child_Tunic_') and math.dist(p.f32(ha + 0x31C, 3), pos) < 0.3
                                     for ha, nm in dga.items())
                except OSError:
                    arm_on = False
                own = 0 if arm_on else _show(p_act, self.pad.TUNIC_SHOW)
                if arm_on:
                    log('tunika: egen Link har farge-plagg på – grunn-tunikaen forblir skjult')
                found = self.pad._list_actors_raw(p, prefix='CoopPuppet_') or {}
                near = []
                for act in found:
                    if act == p_act or not self.pad.actor_alive(p, act):
                        continue
                    if pos is None:
                        near.append(act)
                        continue
                    try:
                        raw = p.read(p.base + act + 0x31C, 12)
                        q = struct.unpack('<3f', raw) if len(raw) == 12 else None
                    except (OSError, struct.error):
                        q = None
                    # Parkerete dukker ligger på y=-2000. Overlayen kan ha gjemt
                    # materialene deres, og poolen gjenbruker dem ved neste farge.
                    if q is not None and (math.dist(pos, q) < 40.0 or q[1] < -100.0):
                        near.append(act)
                    if len(near) >= 8:
                        break
                show = self.pad.TUNIC_SHOW + self.pad.TUNIC_HIDE
                restored = sum(_show(act, show) for act in near)
                log(f'tunika: overlay av. Egen Mt_Cloth satt på {own} materiale(r), '
                    f'{len(near)} nær-dukke(r) fikk materialene synlige igjen ({restored} kall).')
            except Exception as e:  # noqa: BLE001
                log(f'tunika: opprydding feilet {e!r}')
            finally:
                self._st_undo_done = True
                self._st_undo_busy = False

        threading.Thread(target=_undo, daemon=True).start()

    def _save_color(self):
        c = self.color_var.get()
        if c in HAT_COLORS:
            self.hat_color = c
            self.color_dot.config(fg=HAT_COLORS[c])
            self.cfg["hat_color"] = c; save_cfg(self.cfg)
            log(f"hattefarge valgt: {c}")

    @staticmethod
    def _render_chat_item(widget, item):
        widget.config(state="normal")
        if widget.index("end-1c") != "1.0":
            widget.insert("end", "\n")
        widget.insert("end", f"[{item['time']}] ", "sys")
        if item["kind"] == "sys":
            widget.insert("end", item["text"], "sys")
        else:
            widget.insert("end", f"{item['sender']}: ", item["tag"])
            widget.insert("end", item["text"])
        widget.see("end")
        widget.config(state="disabled")

    def _append_chat_item(self, item):
        self.chat_history.append(item)
        del self.chat_history[:-500]
        self._render_chat_item(self.chat_log, item)
        if self.chat_popup_log is not None and self.chat_popup_log.winfo_exists():
            self._render_chat_item(self.chat_popup_log, item)

    def _append_chat_sys(self, text):
        log(f'chat-sys: {text}')
        self.ui(self._append_chat_item,
                {"kind": "sys", "time": time.strftime("%H:%M"), "text": text})

    def _append_chat_msg(self, sender, text, color_name):
        tag = f"col_{color_name}" if color_name in HAT_COLORS else "col_Grønn"
        self.ui(self._append_chat_item,
                {"kind": "msg", "time": time.strftime("%H:%M"), "sender": sender, "text": text, "tag": tag})

    def _open_chat_window(self):
        if self.chat_window is not None and self.chat_window.winfo_exists():
            self.chat_window.deiconify()
            self.chat_window.lift()
            self.chat_window.focus_set()
            return
        win = tk.Toplevel(self.root, bg=BG)
        self.chat_window = win
        win.title(f"Zelda Multiplayer {VERSION} – Chat")
        win.geometry("900x650")
        win.minsize(560, 360)
        outer = tk.Frame(win, bg=GOLD_D, padx=1, pady=1)
        outer.pack(fill="both", expand=True, padx=10, pady=10)
        frame = tk.Frame(outer, bg=PANEL)
        frame.pack(fill="both", expand=True)
        tk.Label(frame, text="Chat", bg=PANEL, fg=GOLD,
                 font=(ZELDA_FONT, 20, "bold")).pack(anchor="center", pady=(8, 0))
        log_widget = tk.Text(frame, bg=FIELD, fg=FG, relief="flat", wrap="word",
                             highlightthickness=1, highlightbackground=BORDER,
                             font=("Segoe UI", 11), state="disabled", padx=12, pady=10)
        log_widget.pack(fill="both", expand=True, padx=12, pady=(6, 8))
        log_widget.tag_configure("sys", foreground=MUTED, font=("Segoe UI", 10, "italic"))
        for cname, chex in HAT_COLORS.items():
            log_widget.tag_configure(f"col_{cname}", foreground=chex, font=("Segoe UI", 11, "bold"))
        self.chat_popup_log = log_widget
        for item in self.chat_history:
            self._render_chat_item(log_widget, item)
        row = tk.Frame(frame, bg=PANEL)
        row.pack(fill="x", padx=12, pady=(0, 12))
        self.chat_popup_var = tk.StringVar()
        entry = ttk.Entry(row, textvariable=self.chat_popup_var, font=("Segoe UI", 11))
        entry.pack(side="left", fill="x", expand=True, padx=(0, 8))
        entry.bind("<Return>", lambda _e: self._send_chat_popup())
        ttk.Button(row, text="Send", command=self._send_chat_popup).pack(side="right")
        entry.focus_set()

        def close():
            self.chat_popup_log = None
            self.chat_popup_var = None
            self.chat_window = None
            win.destroy()
        win.protocol("WM_DELETE_WINDOW", close)

    def _open_connected_window(self):
        if getattr(self, "conn_window", None) is not None and self.conn_window.winfo_exists():
            self.conn_window.deiconify()
            self.conn_window.lift()
            self.conn_window.focus_set()
            return
        win = tk.Toplevel(self.root, bg=BG)
        self.conn_window = win
        win.title(f"Zelda Multiplayer {VERSION} – Connected")
        win.geometry("560x520")
        win.minsize(380, 300)
        outer = tk.Frame(win, bg=GOLD_D, padx=1, pady=1)
        outer.pack(fill="both", expand=True, padx=10, pady=10)
        frame = tk.Frame(outer, bg=PANEL)
        frame.pack(fill="both", expand=True)
        title_lbl = tk.Label(frame, text=self._conn_title.cget("text"), bg=PANEL, fg=GOLD,
                             font=(ZELDA_FONT, 20, "bold"))
        title_lbl.pack(anchor="center", pady=(8, 4))
        self.conn_popup_title = title_lbl
        lst_fr = tk.Frame(frame, bg=PANEL)
        lst_fr.pack(fill="both", expand=True, padx=12, pady=(4, 12))
        lb = tk.Listbox(lst_fr, bg=FIELD, fg=FG, selectbackground=SEL, selectforeground="#ffffff",
                        highlightthickness=1, highlightbackground=BORDER, borderwidth=0,
                        font=("Segoe UI", 11), justify="center")
        sb = ttk.Scrollbar(lst_fr, orient="vertical", command=lb.yview)
        lb.config(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        lb.pack(side="left", fill="both", expand=True)
        self.conn_popup_list = lb
        for i in range(self.plist.size()):
            lb.insert("end", self.plist.get(i))
            try:
                lb.itemconfig(i, foreground=self.plist.itemcget(i, "foreground") or FG)
            except Exception:
                pass

        def close():
            self.conn_popup_list = None
            self.conn_popup_title = None
            self.conn_window = None
            win.destroy()
        win.protocol("WM_DELETE_WINDOW", close)

    def _send_chat_popup(self):
        if self.chat_popup_var is None:
            return
        self.chat_var.set(self.chat_popup_var.get())
        self.chat_popup_var.set("")
        self._send_chat()

    def _send_chat(self):
        txt = self.chat_var.get().strip()
        if not txt:
            return
        low = __import__('unicodedata').normalize('NFKC', txt).lower().strip()
        if low.startswith('/') and not getattr(self, '_remote_run', False) and not self._cmd_allowed():
            self.chat_var.set("")   # v0.94.298: sendes heller ikke som chat
            if getattr(self, 'mode', 'Story') != 'Story':
                self._append_chat_sys('Commands are off in PvP.')
            else:
                host = (self.friend or {}).get('name')
                self._append_chat_sys(f"Only the host{f' ({host})' if host else ''} can use commands.")
            log(f'kommando avvist (ikke Story-host): {txt[:40]}')
            return
        if low.startswith('/') and not getattr(self, '_remote_run', False) and low.split()[0] not in self.HOST_CMDS:
            self.chat_var.set("")   # v0.94.301: juks-/test-kommandoer (/goto, /spawn, /skip …) bare via remote_cmd.txt
            self._append_chat_sys('Unknown command – click Commands to see the list.')
            log(f'kommando avvist (juks/test, bare fjernstyring): {txt[:40]}')
            return
        if low == '/help' and not getattr(self, '_remote_run', False):
            self.chat_var.set(""); self._show_commands()   # v0.94.301: hosten ser bare sin egen liste
            return
        if low.split()[0] in ('/drive', '/stick', '/btn', '/walkto'):   # v0.94.304: styr egen Link (bare fjernstyring, test)
            self.chat_var.set("")
            threading.Thread(target=self._drive_cmd, args=(low.split(),), daemon=True).start()
            return
        if low.startswith('/rupees'):   # v0.94.301: bare fjernstyring (test) – f.eks. sette tilbake rupees etter test-spawn
            self.chat_var.set("")
            try:
                n = max(0, min(999, int(low.split()[1])))
                old = self.rupees.tick()
                self.rupees.mute(3.0); self.rupees._set(n)
                log(f'rupees: satt {old} -> {n} (fjern-kommando)')
                self._append_chat_sys(f'rupees: {old} -> {n}')
            except Exception as e:  # noqa: BLE001
                log(f'rupees: feilet: {e!r}')
            return
        if low.startswith('/mode'):
            self.chat_var.set("")
            requested = next((m for m in MODES if low == f'/mode {m.lower()}'), None)
            if requested is None:
                self._append_chat_sys(f'Bruk: /mode {" eller /mode ".join(MODES)}')
            else:
                self.mode_var.set(requested)
                self._save_mode()
            return
        if low in ("/opendoor", "/door"):
            self.chat_var.set("")
            def _od():
                try:
                    p = self.p; me = self.pad.my_apos(p)
                    self.pad._diag_all = {}; self.pad._scan_full_t = 0
                    t0 = time.time()
                    while time.time() - t0 < 8 and not self.pad._diag_all:
                        time.sleep(0.5)
                    time.sleep(1.0)
                    allm = dict(self.pad._diag_all or {}); self.pad._diag_all = None
                    keys = ('SpiderWeb', 'Door', 'Shutter', 'Gate', 'Bars', 'Web')
                    n = 0
                    for a, nm in allm.items():
                        if not any(k in nm for k in keys) or 'AirWall' in nm:
                            continue
                        try:
                            pos = p.f32(a + 0x31C, 3)
                        except OSError:
                            continue
                        if me and math.dist(pos, me) < 6.0:
                            r = self.pad.delete_actor(p, a); n += 1
                            log(f'dør: fjernet {nm} ved {[round(v, 1) for v in pos]} -> {r}')
                    self.ui(self._append_chat_sys, f'🚪 Removed {n} door/web objects near you (only on this PC, comes back when the room reloads)')
                except Exception as e:  # noqa: BLE001
                    log(f'dør: feil {e!r}')
            threading.Thread(target=_od, daemon=True).start()
            return
        if low.startswith("/goto"):
            self.chat_var.set("")
            names = {"gohma": (2.0, 47.0, 67.6)}
            arg = low.split()[1:]
            try:
                xyz = list(names[arg[0]]) if len(arg) == 1 and arg[0] in names else [float(v) for v in arg[:3]]
                assert len(xyz) == 3
            except (ValueError, AssertionError, KeyError):
                self._append_chat_sys("Usage: /goto x y z  or  /goto gohma"); return
            def _go():
                r = self.pad.teleport_player(self.p, xyz) if self.p else None
                time.sleep(0.5)
                self._append_chat_sys(f"goto {xyz} -> {r}, now {self.pad.my_apos(self.p)}")
            threading.Thread(target=_go, daemon=True).start()
            return
        if low == "/testmove":
            self.chat_var.set("")
            def _tm():
                try:
                    p, pad = self.p, self.pad
                    me = pad.my_apos(p)
                    best = None
                    for a, (nm, _f, last) in list(getattr(self, '_ac_track', {}).items()):
                        if nm.startswith('Enemy_'):
                            try:
                                q = p.f32(a + 0x31C, 3)
                            except OSError:
                                continue
                            d = math.dist(q, me)
                            if best is None or d < best[0]:
                                best = (d, a, nm, q)
                    if not best or best[0] > 20:
                        self.ui(self._append_chat_sys, 'testmove: no enemy within 20 m'); return
                    d, a, nm, q = best
                    tgt = [q[0] + (me[0] - q[0]) * 0.5, q[1], q[2] + (me[2] - q[2]) * 0.5]
                    t0 = time.time(); n = 0; offs = []
                    while time.time() - t0 < 3.0:
                        r = pad.move_actor_real(p, a, tgt); n += 1
                        offs.append(math.dist(p.f32(a + 0x31C, 3), tgt))
                    q2 = p.f32(a + 0x31C, 3)
                    time.sleep(1.0); q3 = p.f32(a + 0x31C, 3)
                    msg = (f'testmove: {nm} {[round(v, 1) for v in q]} -> mål {[round(v, 1) for v in tgt]}; {n} kall på 3 s, '
                           f'avvik mens holdt snitt {sum(offs) / max(1, len(offs)):.2f} m maks {max(offs or [0]):.2f} m; '
                           f'rett etter {[round(v, 1) for v in q2]}, 1 s senere {[round(v, 1) for v in q3]}')
                    log(msg); self.ui(self._append_chat_sys, msg)
                except Exception as e:  # noqa: BLE001
                    log(f'testmove: feil {e!r}')
            threading.Thread(target=_tm, daemon=True).start()
            return
        if low.startswith("/target"):
            self.chat_var.set("")
            arg = low.split()[1] if len(low.split()) > 1 else ""
            if arg in ("off", "1", "me"):
                self.target_on, self.target_mode = True, 1
            elif arg in ("2", "friend"):
                self.target_on, self.target_mode = True, 2
            else:
                self.target_on, self.target_mode = True, 0
            st_ = self.pad.target_stats(self.p) if self.p else None
            txt = {0: "nearest Link", 1: "only my Link (old behaviour)", 2: "always Link 2"}[self.target_mode]
            self._append_chat_sys(f"Enemy target: {txt}" + (f" (patch calls {st_[0]}, chose Link 2 {st_[1]}x)" if st_ else " (patch not loaded?)"))
            return
        if low.startswith("/blind"):
            self.chat_var.set("")
            self.blind_on = not low.endswith("off")
            if not self.blind_on and self.p:
                self.pad.set_blind(self.p, []); self._blind_prev = []
            self._append_chat_sys(f"Blind {'ON' if self.blind_on else 'OFF'} (copies of the friend's enemies {'only show the owner attacks' if self.blind_on else 'attack on their own'})")
            return
        if low.startswith("/bossfollow"):
            self.chat_var.set("")
            self.boss_follow_on = not low.endswith("off")
            if not self.boss_follow_on and self.p:
                self._boss_release(self.p)
            self._append_chat_sys(f"Boss follow {'ON' if self.boss_follow_on else 'OFF'}")
            return
        if low.startswith("/aihold"):
            self.chat_var.set("")
            self.ai_hold_on = not low.endswith("off")
            if not self.ai_hold_on and self.p:
                self.pad.set_ai_hold(self.p, []); self._held_prev = []
            self._append_chat_sys(f"AI hold {'ON' if self.ai_hold_on else 'OFF'} (copies of the friend's enemies {'pause their own AI' if self.ai_hold_on else 'run their own AI'})")
            return
        if low == "/resetboss":
            self.chat_var.set("")
            self._rb_ver = getattr(self, '_rb_ver', 0) + 1
            self._do_resetboss()
            return
        if low.split()[0] in self.INFO_CMDS if low else False:
            self.chat_var.set("")
            threading.Thread(target=self._info_cmd, args=(low,), daemon=True).start()
            return
        if low == "/near":
            self.chat_var.set("")
            def _near():
                try:
                    self.pad._diag_all = {}; self.pad._scan_full_t = 0
                    t0 = time.time()
                    while time.time() - t0 < 8 and not self.pad._diag_all:
                        time.sleep(0.5)
                    time.sleep(1.0)
                    me = self.pad.my_apos(self.p) or (0, 0, 0); out = []
                    allm = dict(self.pad._diag_all); self.pad._diag_all = None
                    items = [(a, (nm, None, None)) for a, nm in allm.items()] + list(getattr(self, '_ac_track', {}).items())
                    for a, (nm, _f, last) in items:
                        try: pos = self.p.f32(a + 0x31C, 3)
                        except OSError: continue
                        d = math.dist(pos, me)
                        if d < 25: out.append((d, nm, a, pos))
                    out.sort()
                    for d, nm, a, pos in out[:40]:
                        log(f"near: {d:5.1f} m {nm} @0x{a:X} pos ({pos[0]:.1f}, {pos[1]:.1f}, {pos[2]:.1f})" + (f" liv {self._actor_hp(self.p, a)}" if nm.startswith('Enemy_') else ''))
                    self.ui(self._append_chat_sys, f"📋 Logged {len(out)} objects near you")
                except Exception as e:  # noqa: BLE001
                    log(f"near: feil {e!r}")
            threading.Thread(target=_near, daemon=True).start()
            return
        if low in ("/tp", "/warp", "!tp", "!warp", "/here", "/samle", "/teleport"):
            self.chat_var.set("")
            if not self.peer or not hasattr(self, "gs"):
                self._append_chat_sys("⚠️ Not connected to a friend!")
                return
            if self._in_boss_fight() or (self.friend or {}).get('bf'):
                self._append_chat_sys("⚠️ /tp is blocked during a boss fight (the game would trap you in a loop).")
                return
            apos = self.pad.my_apos(self.p) if (self.p and self.ready) else None
            arot = self.pad.my_arot(self.p) if (self.p and self.ready) else None
            if apos:
                pkt = {"t": "party_warp", "s": self.session, "name": self.name, "pos": apos, "rot": arot,
                       "banc": self.pad.cur_banc, "force": True}
                try:
                    self.gs.sendto(json.dumps(pkt).encode(), self.peer)
                    fname = getattr(self, "peer_name", None) or (self.friend or {}).get("name") or "vennen"
                    self._append_chat_sys(f"🌀 You teleported {fname} to you!")
                    log(f"chat kommando {low}: teleporterte {fname} til ({apos[0]:.2f}, {apos[1]:.2f}, {apos[2]:.2f})")
                except OSError:
                    pass
            return
        self.chat_var.set("")
        self.chat_seq += 1
        item = {"id": self.chat_seq, "name": self.name, "text": txt[:240], "color": self.hat_color}
        self.chat_out.append(item)
        del self.chat_out[:-8]
        self._append_chat_msg(self.name, item["text"], self.hat_color)
        log(f"chat ut ({self.name}): {item['text']}")
        if time.time() - getattr(self, '_server_seen', 0) < 5:
            self._server_cmd('chat', text=item['text'])
        elif self.peer and hasattr(self, "gs"):
            try:
                pkt = {"t": "chat", "s": self.session, "chat": list(self.chat_out)}
                self.gs.sendto(json.dumps(pkt).encode(), self.peer)
            except OSError:
                pass

    # ------------------------------------------------------------ automatiske sjekker
    def _worker(self):
        while True:
            try:
                self._attach_once()
            except MemoryError:
                log("MINNEFEIL: for lite ledig minne – venter 60 s før neste forsøk (lukk andre programmer / større sidefil)")
                self.set_check("game", "err", "out of memory – waiting")
                time.sleep(60)
            except Exception as e:  # noqa: BLE001 – vis feilen, prøv igjen
                log(f"FEIL: {e!r}")
                self.set_check("game", "err", str(e)[:40])
            self.ready = False
            time.sleep(2)

    def _attach_once(self):
        self.set_check("lichii", "work", "waiting …")
        pid = None
        while not pid:
            pid = find_pid(); time.sleep(0 if pid else 2)
        p = Proc(pid)
        self.set_check("lichii", "ok", f"PID {pid}")
        if p.size < (1 << 30):
            raise OSError("fant ikke spillminnet")
        self.set_check("game", "ok", f"{p.size >> 20} MB")

        cfg = self.cfg
        # v0.30: Kjør PadLink-oppslag med én gang (~0,02 s!) så vi har p_act+0x31C (eksakt Link-posisjon uten veiledning!)
        try:
            self.pad._worker(p)
        except Exception:
            pass
        # Kjente forskyvninger: 0 eller -0x140000000 (samme spill, annen plass i emulatorminnet).
        shifts = [0, -0x140000000, 0x140000000, -0xC0000000, 0xC0000000] + [s for s in cfg.get("known_shifts", []) if s]
        pos_c = [cfg.get("pos_off")] + [DEFAULT_POS_OFF + s for s in shifts]
        rup_c = [cfg.get("rupee_off")] + [DEFAULT_RUPEE_OFF + s for s in shifts]
        pos = next((o for o in pos_c if o and 0 < o < p.size and valid_pos(p, o)), None)
        rup = next((o for o in rup_c if o and 0 < o < p.size and valid_rupee(p, o)), None)
        # Har vi den ene, gir forskyvningen den andre.
        if pos and not rup and valid_rupee(p, DEFAULT_RUPEE_OFF + pos - DEFAULT_POS_OFF):
            rup = DEFAULT_RUPEE_OFF + pos - DEFAULT_POS_OFF
        if rup and not pos and valid_pos(p, DEFAULT_POS_OFF + rup - DEFAULT_RUPEE_OFF):
            pos = DEFAULT_POS_OFF + rup - DEFAULT_RUPEE_OFF
        if pos is None and self.pad.p_act is not None and self.pad.my_apos(p) is not None:
            pos = self.pad.p_act + 0x31C
            log(f"posisjon funnet direkte fra PadLink (player_actor+0x31C): guest+0x{pos:X}")
        # v0.43: Helautomatisk tilkobling uten popup-veiledning eller "gå 3 sekunder"!
        # Hvis Link ikke er ute i verden ennå (f.eks. meny/tittelbilde), venter vi rolig i bakgrunnen på PadLink.
        if pos is None:
            self.set_check("pos", "work", "waiting for Link …")
            t_wait_pos = time.time()
            while not getattr(self, "_stop", False) and pos is None:
                try:
                    self.pad._worker(p)
                except Exception:
                    pass
                if self.pad.p_act is not None and self.pad.my_apos(p) is not None:
                    pos = self.pad.p_act + 0x31C
                    log(f"posisjon funnet direkte fra PadLink (player_actor+0x31C): guest+0x{pos:X}")
                    break
                pos = next((o for o in pos_c if o and 0 < o < p.size and valid_pos(p, o)), None)
                if pos is not None:
                    break
                # Prøv rask kamerabasert deteksjon hvert 5. sekund
                if int(time.time() - t_wait_pos) % 5 == 0 and pos is None:
                    cam0 = self.cfg.get("cam_off")
                    if cam0 and 0 < cam0 < p.size and valid_cam(p, cam0, None):
                        pos = relink_near(p, DEFAULT_POS_OFF, cam0)
                time.sleep(0.5)

        if rup is None and pos is not None:
            shift = pos - DEFAULT_POS_OFF
            cand_shifts = [shift, 0, -0x140000000, 0x140000000, -0xC0000000, 0xC0000000]
            for s in dict.fromkeys(cand_shifts):
                cand = DEFAULT_RUPEE_OFF + s
                if 0 < cand < p.size and valid_rupee(p, cand):
                    rup = cand
                    log(f"rupees funnet automatisk: guest+0x{rup:X} (shift {s:+#x})")
                    break
            if rup is None:   # sikker kilde: GameDataMgr s32-post 962 (fungerer også i nye lagringsfiler og mens HUD teller)
                try:
                    self.pad._gdm_scan_t = 0; self.pad.read_door(p)
                    h_s32 = getattr(self.pad, 'h_s32', None)
                    if h_s32 is not None:
                        cand = h_s32 + 962 * 0x28 + 0x1C
                        if valid_counter(p, cand):
                            rup = cand
                            log(f'rupees funnet i GameDataMgr (post 962): guest+0x{rup:X}')
                except Exception:  # noqa: BLE001
                    pass
            if rup is None:
                rup = find_rupees_by_region(p, pos)
                if rup is not None:
                    log(f"rupees funnet ved områdeforskyvning: guest+0x{rup:X}")

        if pos is None or rup is None:
            self.set_check("pos", "work", "waiting for rupees …")
            time.sleep(0.5)
            return

        if pos is not None and rup is not None:
            shift = pos - DEFAULT_POS_OFF
            if shift not in shifts:
                cfg.setdefault("known_shifts", []).append(shift)
                log(f"ny forskyvning lært: {shift:+#x}")
        if (cfg.get("pos_off"), cfg.get("rupee_off")) != (pos, rup):
            cfg.update(pos_off=pos, rupee_off=rup); save_cfg(cfg)
        same = self.p is not None and self.p.pid == p.pid and self.pos_off == pos and self.rupees and self.rupees.off == rup
        if not same:
            log(f"tilkoblet: pos=guest+0x{pos:X} {tuple(round(v, 1) for v in p.f32(pos, 3))}, "
                f"rupees=guest+0x{rup:X} ({p.u32(rup)}), markør=0x{p.u32(rup + 12):08X}, "
                f"forskyvning {pos - DEFAULT_POS_OFF:+#x}")
            self.syncs = {}
            self.cnt_epoch = random.getrandbits(32)   # v0.94.268: nye tellere (my_cum=0) -> vennen må nullstille «seen»
            for name, rel, cap_rel, _label in ITEMS:
                if valid_counter(p, rup + rel):
                    self.syncs[name] = CounterSync(p, rup + rel, 999, name, rup + cap_rel)
                else:
                    log(f"{name}: fant ikke gyldig post på rupees{rel:+#x} – synkes ikke")
            self.rupees = self.syncs["rupees"]
            log("synker: " + ", ".join(f"{n}={c.expected}/{c.cap()}" for n, c in self.syncs.items()))
            try:
                self.bag = BagSync(p, rup, self.cfg, {rel for _n, rel, _c, _l in ITEMS} | {0x8E8, 0x910, 0x938})   # nøtter/frø/pinner: aldri synk (Link 2 bruker dem også)
            except OSError as e:
                self.bag = None; log(f"bag: kunne ikke lese inventar-blokken: {e!r}")
            self.learn_state = {}
        else:
            # samme økt: behold kumulative tellere, ellers tror vennen at vi har mistet ting
            for c in self.syncs.values():
                c.p = p; c.expected = p.u32(c.off)
            if getattr(self, "bag", None):
                self.bag.p = p
                for c in self.bag.counters.values():
                    c.p = p; c.expected = p.u32(c.off)
        self.p, self.pos_off = p, pos
        self.set_check("pos", "ok", f"0x{pos:X}"); self.set_check("rupees", "ok", f"{self.rupees.expected}")
        self.ready = True
        if getattr(self, 'mode', 'Story') == 'Story':
            if self.cfg.get('pvp_saved_hp'):
                self._pvp_set_hp(False)
            if self.cfg.get('pvp_saved_inv'):
                self._pvp_set_inv_mode(False)
        else:
            self._pvp_set_inv_mode(True)
        self._ensure_cam(p, pos)
        # Overvåking: tål korte avvik (hopp, skråning, menyer, lasting). Koble på nytt først etter ~6 s med feil.
        fails = cam_fails = far = 0
        last_joint = 0.0
        frozen_since, last_xyz = None, None
        ap_last, ap_moved_t = None, time.time()   # v0.94.302: Link-aktørens posisjon (uavhengig av fysikk-posten)
        while p.alive() and fails < 6:
            # --- Gammel Link-post etter områdebytte? (den gamle blir liggende med gamle tall og passerer valideringen)
            try:
                xyz = p.f32(pos, 3)
            except OSError:
                xyz = None
            # En gammel post (etter områdebytte) står bit-for-bit stille. Står posisjonen stille i ≥5 s, sjekk hvert 10. s
            # om en ANNEN post + et kamera flytter seg sammen (= spilleren går) – i så fall er det den ekte Link.
            if xyz is not None:
                if xyz == last_xyz:
                    frozen_since = frozen_since or time.time()
                else:
                    frozen_since = None
                last_xyz = xyz
            # v0.94.302: står også Link-aktøren stille, står spilleren bare i ro – da er en stille post ventet, og vi
            # søker ikke (før: 512 MB lest hvert 30. s og hele minnet hvert 3. min når man sto i ro, ~1 CPU-kjerne)
            try:
                ap_ = self.pad.my_apos(p)
            except Exception:  # noqa: BLE001
                ap_ = None
            if ap_ is not None and (ap_last is None or math.dist(ap_, ap_last) > 0.05):
                ap_last, ap_moved_t = ap_, time.time()
            idle_ = ap_ is not None and time.time() - ap_moved_t > 10
            if frozen_since and not idle_ and time.time() - frozen_since >= 5 and time.time() - last_joint >= 30:
                last_joint = time.time()
                anchors = [self.cam_off, getattr(self, "last_cam", None), self.cfg.get("cam_off"), *self.cfg.get("cam_history", [])]
                full = time.time() - getattr(self, "_last_full_joint", 0) >= 180 and getattr(self, "_joint_misses", 0) >= 2
                if full:
                    self._last_full_joint = time.time()
                try:
                    new, cam = relink_joint(p, pos, anchors, full=full)
                except MemoryError:
                    log("MINNEFEIL under gjenfinning – hopper over i 2 min")
                    new = cam = None; last_joint = time.time() + 90
                self._joint_misses = 0 if new is not None else getattr(self, "_joint_misses", 0) + 1
                if new is not None and new != pos:
                    log(f"Link-post guest+0x{pos:X} sto stille mens Link gikk – byttet til guest+0x{new:X} "
                        f"{tuple(round(v, 1) for v in p.f32(new, 3))} (trolig områdebytte)")
                    pos = new; self.pos_off = new
                    self.cfg["pos_off"] = new; save_cfg(self.cfg)
                    self.set_check("pos", "ok", f"0x{new:X}")
                    frozen_since = None; last_xyz = None
                if cam is not None and cam != self.cam_off:
                    log(f"kamera byttet til guest+0x{cam:X} (fulgte Link)")
                    self.cam_off = self.last_cam = cam
                    self.cfg["cam_off"] = cam; save_cfg(self.cfg)
                    self.set_check("cam", "ok", f"0x{cam:X}")
            ok = (valid_pos_light(p, pos) or (self.pad.p_act is not None and pos == self.pad.p_act + 0x31C and self.pad.my_apos(p) is not None)) and valid_rupee_light(p, rup)
            fails = 0 if ok else fails + 1
            if fails == 1:
                log("validering feilet et øyeblikk (venter før ny oppkobling)")
            if self.cam_off is not None:
                try:
                    cam_ok = valid_cam(p, self.cam_off, p.f32(pos, 3))
                except OSError:
                    cam_ok = False
                cam_fails = 0 if cam_ok else cam_fails + 1
                try:   # «dødt» kamera: Link har flyttet seg > 2 m mens kamera-øyet står helt stille
                    lp = p.f32(pos, 3); ce = read_cam(p, self.cam_off)[3]
                    ref = getattr(self, '_cam_ref', None)
                    if ref is None or ref[2] != self.cam_off:
                        self._cam_ref = (lp, ce, self.cam_off)
                    elif math.dist(lp, ref[0]) > 2.0:
                        if math.dist(ce, ref[1]) < 0.01:
                            log(f"kamera guest+0x{self.cam_off:X} følger ikke Link (dødt kamera) – søker på nytt")
                            self.__dict__.setdefault('_cam_dead', set()).add(self.cam_off)
                            if self.cfg.get('cam_off') == self.cam_off:
                                self.cfg.pop('cam_off', None)
                            self.cfg['cam_history'] = [o for o in self.cfg.get('cam_history', []) if o != self.cam_off]
                            save_cfg(self.cfg)
                            cam_fails = 5
                        self._cam_ref = (lp, ce, self.cam_off)
                except (OSError, ValueError, TypeError):
                    pass
                if cam_fails >= 5:
                    log(f"kamera guest+0x{self.cam_off:X} ugyldig i 5 s – søker på nytt")
                    self.cam_off = None; cam_fails = 0
                    self.set_check("cam", "work", "searching …")
            if self.cam_off is None:
                self._ensure_cam(p, pos)
            time.sleep(1)
        if p.alive():
            log("adresser ugyldige i 6 s – kobler på nytt")
        self.ready = False
        for k in ("pos", "rupees"):
            self.set_check(k, "off", "")

    def _ensure_cam(self, p, pos):
        """Finn kamera: lagret/standard + forskyvning, ellers søk i bakgrunnen (maks hvert 30. s)."""
        if self.cam_off is not None or self.cam_scanning:
            return
        near = p.f32(pos, 3)
        if abs(near[0]) + abs(near[1]) + abs(near[2]) < 1.0:
            return            # ingen ekte Link-posisjon ennå – et kamerasøk nå ville funnet feil kamera
        shift = pos - DEFAULT_POS_OFF
        # Pålitelig først: kamera-vtable rundt Link (0,3 s). Lagrede adresser kan peke på et «dødt» kamera som består
        # gyldighetssjekken men ikke følger synet -> feil kameravinkel -> Link 2 går baklengs.
        if getattr(self.pad, 'main', None) and getattr(self.pad, 'p_act', None):
            try:
                best = cam_scan_vtable(p, self.pad.main, self.pad.p_act, self.pad.my_apos(p) or near)
            except Exception:  # noqa: BLE001
                best = None
            if best is not None:
                self.cam_off = self.last_cam = best; self.cfg['cam_off'] = best; save_cfg(self.cfg)
                log(f'kamera: guest+0x{best:X} (vtable)')
                self.set_check('cam', 'ok', f'0x{best:X}')
                return
        for o in (self.cfg.get("cam_off"), DEFAULT_CAM_OFF + shift, DEFAULT_CAM_OFF):
            if o and 0 < o < p.size and o not in getattr(self, '_cam_dead', ()) and valid_cam(p, o, near):
                self.cam_off = self.last_cam = o
                log(f"kamera: guest+0x{o:X} (kjent adresse), øye {tuple(round(v, 1) for v in read_cam(p, o)[3])}")
                self.set_check("cam", "ok", f"0x{o:X}")
                return
        # Raskt søk (±32 MB rundt tidligere kamera-adresser) er alltid lov; fullt søk maks hvert 30. s.
        # Historikk: behold bare adresser som ikke er bevist feile (de som nå validerer, eller som vi ikke kan lese)
        raw = [o for o in self.cfg.get("cam_history", []) if o]
        hist = [o for o in raw if not (0 < o < p.size) or valid_cam(p, o, near) or not _cam_readable(p, o)]
        if len(hist) != len(raw):
            log(f"cam_history: fjernet {len(raw) - len(hist)} adresse(r) som ikke er kamera nær Link")
            self.cfg["cam_history"] = hist; save_cfg(self.cfg)
        anchors = list(dict.fromkeys([a for a in (getattr(self, "last_cam", None), self.cfg.get("cam_off"),
                                                  DEFAULT_CAM_OFF + shift, DEFAULT_CAM_OFF, *hist) if a]))
        full_ok = time.time() - self.cam_last_scan >= 120   # v0.8.3: maks hvert 2. min (var 30 s)
        quick_ok = time.time() - getattr(self, "cam_last_quick", 0) >= 5
        if not (full_ok or quick_ok):
            return
        self.cam_scanning = True
        self.set_check("cam", "work", "searching …")

        def choose(groups, label, t):
            log(f"kamera-søk ({label}): {sum(g[0] for g in groups)} kandidater i {len(groups)} grupper på {time.time() - t:.1f} s")
            for n, offs, eye, dist, dot in groups[:3]:
                log(f"  gruppe: {n} kopier, øye {eye}, {dist:.1f} m fra Link, retning {dot:.2f}, første guest+0x{offs[0]:X}")
            # Velg ut fra Link sin posisjon NÅ (han kan ha flyttet seg under søket): kameraet som ser mest rett
            # mot Link og står 1,5–12 m unna. (Flertall virker ikke når kameraet beveger seg under søket.)
            now_pos = p.f32(pos, 3)
            scored = []
            for _n, offs, _eye, _d, _dot in groups:
                q = cam_quality(p, offs[0], now_pos)
                if q and 1.5 < q[0] < 12 and q[1] > 0.7 and offs[0] not in getattr(self, '_cam_dead', ()):   # må faktisk se mot Link
                    scored.append((q[1], offs[0], q[0]))
            scored.sort(reverse=True)
            if not scored:
                return None
            log(f"  valgt: retning {scored[0][0]:.2f}, {scored[0][2]:.1f} m fra Link")
            return scored[0][1]

        def run():
            try:
                best = None
                if getattr(self.pad, "main", None) and getattr(self.pad, "p_act", None):
                    t = time.time()
                    apos = self.pad.my_apos(p) or p.f32(pos, 3)
                    best = cam_scan_vtable(p, self.pad.main, self.pad.p_act, apos)
                    if best is not None:
                        log(f"kamera funnet via vtable på {time.time() - t:.2f} s: guest+0x{best:X}")
                if best is None and quick_ok and anchors:
                    self.cam_last_quick = time.time()
                    span = 32 << 20
                    regions = sorted({(max(0, a - span) & ~(CHUNK - 1), min(p.size, a + span)) for a in anchors})
                    t = time.time()
                    best = choose(cam_scan(p, p.f32(pos, 3), lambda _f: None, regions), "raskt", t)
                if best is None and full_ok:
                    self.cam_last_scan = time.time()
                    t = time.time()
                    best = choose(cam_scan(p, p.f32(pos, 3), lambda _f: None), "fullt", t)
                if best is not None:
                    self.cam_off = self.last_cam = best
                    self.cfg["cam_off"] = best
                    self.cfg["cam_history"] = ([best] + [o for o in hist if o != best])[:8]
                    save_cfg(self.cfg)
                    log(f"kamera funnet ved søk: guest+0x{best:X} (forskyvning fra standard {best - DEFAULT_CAM_OFF:+#x})")
                    self.set_check("cam", "ok", f"0x{best:X}")
                else:
                    self.set_check("cam", "err", "not found – retrying")
            except Exception as e:  # noqa: BLE001
                log(f"kamera-søk FEIL: {e!r}")
                if isinstance(e, MemoryError):
                    self.cam_last_scan = time.time() + 150    # neste fulle søk tidligst om ~3 min
                self.set_check("cam", "err", "error")
            finally:
                self.cam_scanning = False
        threading.Thread(target=run, daemon=True).start()

    def _find_link(self, p, phys):
        if not phys:
            raise OSError("ingen fysikk-objekter – er spillet lastet?")
        snap = lambda: {o: p.f32(o, 3) for o in phys if valid_pos(p, o)}  # noqa: E731
        self.show_guide("Finner Link: stå helt stille og trykk OK.")
        a = snap(); time.sleep(1.0); a2 = snap()
        still_noise = {o for o in a if o in a2 and math.dist(a[o], a2[o]) > 0.01}
        self.show_guide("Gå med Link noen meter (2–3 sekunder), stå stille igjen og trykk OK.")
        b = snap()
        moved = [o for o in a if o in b and o not in still_noise and math.dist(a[o], b[o]) > 1.0]
        time.sleep(1.0); c = snap()
        moved = [o for o in moved if o in c and math.dist(b[o], c[o]) < 0.01]
        self.hide_guide()
        if not moved:
            raise OSError("fant ikke Link – prøv igjen på et rolig sted")
        # Link: det som flyttet seg mest (NPC-er står stort sett stille når du står stille)
        moved.sort(key=lambda o: -math.dist(a[o], b[o]))
        return moved[0]

    def _find_rupees(self, p):
        while True:
            v = self.show_guide("Hvor mange rupees har du nå?", entry=True)
            if not v.isdigit():
                continue
            self.hide_guide()
            cands = rupee_scan(p, int(v), self.progress)
            log(f"rupee-søk etter {v}: {len(cands)} kandidater")
            while len(cands) > 1:
                v = self.show_guide(f"{len(cands)} mulige. Plukk opp eller bruk noen rupees, og skriv det nye tallet:",
                                    entry=True)
                if v.isdigit():
                    cands = [o for o in cands if valid_rupee(p, o) and p.u32(o) == int(v)]
            if cands:
                self.hide_guide(); return cands[0]

    # ------------------------------------------------------------ nett
    def _net_setup(self):
        self.gport, self.dport = MODE_PORTS.get(self.cfg.get("mode"), (GAME_PORT, DISC_PORT))
        self.gs = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.gs.bind(("0.0.0.0", self.gport)); self.gs.setblocking(False)
        self.ds = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.ds.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.ds.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
        self.ds.bind(("0.0.0.0", self.dport)); self.ds.setblocking(False)
        if not hasattr(self, 'ss'):   # Behold den ephemeral UDP-porten ved Story/PvP-bytte.
            self.ss = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            self.ss.bind(("0.0.0.0", 0)); self.ss.setblocking(False)
        if not hasattr(self, '_http_in_q'):
            self._http_in_q = queue.Queue()
            self._http_out_q = queue.Queue(maxsize=32)
            self._server_states = queue.Queue()
            self._server_tx_stop = threading.Event()
            threading.Thread(target=self._http_server_worker, daemon=True, name="CloudflareTunnelWorker").start()
            threading.Thread(target=self._server_receive_loop, daemon=True, name="ServerPoseReceive").start()
            threading.Thread(target=self._server_pose_loop, daemon=True, name="ServerPoseSend").start()
        self.last_hello = 0

    def _server_receive_loop(self):
        """Publish incoming poses independently of the Tk event loop."""
        while True:
            packets = []
            while True:
                try:
                    packets.append(self._http_in_q.get_nowait())
                except queue.Empty:
                    break
            while True:
                try:
                    data, _ = self.ss.recvfrom(65535)
                    packets.append(data)
                except OSError:
                    break
            for data in packets:
                try:
                    if data.startswith(b"OPZ1"):
                        inflater = zlib.decompressobj()
                        data = inflater.decompress(data[4:], 256 * 1024)
                        if not inflater.eof or inflater.unused_data:
                            continue
                    state = json.loads(data)
                    if not isinstance(state, dict) or state.get('t') != 'state':
                        continue
                except (ValueError, TypeError, zlib.error):
                    continue
                peers = state.get('peers')
                if isinstance(peers, list) and isinstance(state.get('score'), dict):
                    frames = {(peer['name'], peer['zone']): peer for peer in peers
                             if isinstance(peer, dict)
                             and isinstance(peer.get('name'), str)
                             and isinstance(peer.get('zone'), str)}
                    self._server_peer_frames = (time.time(), frames)
                self._server_states.put(state)
            time.sleep(1.0 / 120.0)

    def _http_server_worker(self):
        """Persistent HTTPS-worker mot Cloudflare-tunnelen https://oot.premiumaroma.no."""
        import urllib.parse, http.client, ssl
        conn = None
        last_host = None
        ctx = ssl.create_default_context()
        while True:
            payload = self._http_out_q.get()
            if payload is None:
                continue
            url = SERVER_URL
            if not url:
                continue
            try:
                parsed = urllib.parse.urlsplit(url)
                scheme = parsed.scheme or "https"
                host = parsed.netloc or parsed.path
                path = parsed.path if parsed.netloc else "/api"
                if not path or path == "/":
                    path = "/api"
                if conn is None or last_host != (scheme, host):
                    if conn is not None:
                        try:
                            conn.close()
                        except Exception:
                            pass
                    if scheme == "https":
                        conn = http.client.HTTPSConnection(host, timeout=3.5, context=ctx)
                    else:
                        conn = http.client.HTTPConnection(host, timeout=3.5)
                    last_host = (scheme, host)
                conn.request("POST", path, body=payload, headers={
                    "Content-Type": "application/json",
                    "User-Agent": f"OoT-Multiplayer/{VERSION}",
                    "Connection": "keep-alive",
                })
                resp = conn.getresponse()
                data = resp.read()
                if resp.status == 200 and data:
                    self._http_in_q.put(data)
            except Exception:  # noqa: BLE001
                if conn is not None:
                    try:
                        conn.close()
                    except Exception:
                        pass
                conn = None

    def _server_cmd(self, kind, **fields):
        """Send en lobby-/kamp-/posisjonshendelse til oot.premiumaroma.no (eller lokal UDP-testserver)."""
        msg = {'t': kind, 'name': self.name, 'v': VERSION, **fields}
        if 'key' not in msg:   # v0.94.286: kontonøkkel med alle meldinger (beskytter PvP-profil og inventar)
            k_ = self._account_key() if hasattr(self, 'cfg') else None
            if k_:
                msg['key'] = k_
        if kind in ('hello', 'pose'):
            msg['pose_v2'] = True
        if self.asset_hash:
            msg['assets'] = self.asset_hash
        raw = json.dumps(msg).encode()
        if SERVER_URL:
            if hasattr(self, '_http_out_q'):
                if kind == 'pose' and not self._http_out_q.empty():
                    return True
                try:
                    self._http_out_q.put_nowait(raw)
                    return True
                except queue.Full:
                    return False
        try:
            self.ss.sendto(raw, SERVER_ADDR)
            return True
        except OSError as e:
            self._append_chat_sys(f'⚠️ Server unavailable: {e}')
            return False

    def _handle_presence(self, m):
        """Serveren eier hvem som er med: vis «X joined/left» én gang per hendelse (løpenummer)."""
        evs = m.get('presence') or []
        last = getattr(self, '_pres_seq_seen', None)
        top = int(m.get('presence_seq') or 0)
        if last is None:          # første svar: ikke gjenta gammel historikk
            self._pres_seq_seen = top
            return
        if top < last:            # serveren er startet på nytt
            self._pres_seq_seen = top
            return
        for e in evs:
            seq = int(e.get('seq') or 0)
            if seq <= last or e.get('name') == self.name:
                continue
            why = {'timeout': ' (timeout)', 'bye': '', 'leave': ''}.get(e.get('reason'), '')
            if e.get('kind') == 'joined':
                self._append_chat_sys(f"🟢 {e.get('name')} joined")
            elif e.get('kind') == 'left':
                self._append_chat_sys(f"🔴 {e.get('name')} left{why}")
            elif e.get('kind') == 'left_game':
                self._append_chat_sys(f"↩️ {e.get('name')} left the game")
            log(f"server: {e.get('name')} {e.get('kind')} ({e.get('reason')})")
        self._pres_seq_seen = top

    def _handle_server_chat(self, messages):
        """Vis hver servermelding én gang; egen melding er allerede vist lokalt."""
        if not isinstance(messages, list):
            return
        seen = self.__dict__.setdefault('_server_chat_seen', set())
        for item in messages:
            if not isinstance(item, dict):
                continue
            seq, sender, text = item.get('seq'), item.get('name'), item.get('text')
            if not isinstance(seq, int) or seq in seen or not isinstance(text, str) or not text:
                continue
            seen.add(seq)
            if sender != self.name:
                self._append_chat_msg(str(sender or '?'), text[:240], item.get('color') or 'Hvit')
        if len(seen) > 2000:
            self._server_chat_seen = set(sorted(seen)[-1000:])

    def _server_says_friend_present(self, now):
        """PvP: serveren bestemmer om vennen er med. Uten svar fra serveren (offline) faller vi tilbake til direkte trafikk."""
        if getattr(self, 'mode', 'Story') != 'PvP' or now - getattr(self, '_server_seen', 0) > 5:
            return True
        fname = (self.friend or {}).get('name')
        present = (getattr(self, '_server_state', None) or {}).get('present')
        if not fname or present is None:
            return True
        return fname in present

    def _server_bye(self):
        self._server_tx_stop.set()
        if SERVER_URL:
            try:
                import urllib.request
                req = urllib.request.Request(
                    SERVER_URL.rstrip('/') + '/api',
                    data=json.dumps({'t': 'bye', 'name': self.name, 'v': VERSION}).encode(),
                    headers={'Content-Type': 'application/json', 'User-Agent': f'OoT-Multiplayer/{VERSION}'},
                    method='POST',
                )
                urllib.request.urlopen(req, timeout=1.0).read()
            except Exception:
                pass
            return
        try:
            self.ss.sendto(json.dumps({'t': 'bye', 'name': self.name, 'v': VERSION}).encode(), SERVER_ADDR)
        except OSError:
            pass

    def _pvp_server_pose(self):
        pad = self.pad
        p = self.p
        banc = pad.cur_banc or ''
        if not (p and self.ready):
            return {'banc': banc}
        actor = pad.p_act
        pos = pad.my_apos(p)
        if pos is None:
            return {'banc': banc}
        pose = {'banc': banc, 'pos': [round(v, 2) for v in pos],
                'follow': bool(getattr(self, 'tvang', False))}
        # Ikke stol på Tk-løkkens cache: les fersk HP direkte i servertråden (0 game_call).
        hearts = None
        try:
            hp_off = self.rupees.off
            h_cur, h_max = p.u32(hp_off + 0x28), p.u32(hp_off + 0x50)
            if 0 <= h_cur <= 80 and 4 <= h_max <= 80:
                hearts = [h_cur, h_max]
                self._my_hearts_last = hearts
        except (AttributeError, OSError):
            hearts = getattr(self, '_my_hearts_last', None)
        if (isinstance(hearts, (list, tuple)) and len(hearts) == 2
                and all(isinstance(v, (int, float)) and not isinstance(v, bool) for v in hearts)
                and 0 <= hearts[0] <= 80 and 4 <= hearts[1] <= 80):
            pose['hearts'] = [int(hearts[0]), int(hearts[1])]
        rot = pad.my_arot(p)
        if rot is not None:
            # Inverse of the yaw-to-matrix conversion in write_puppet_batch.
            pose['yaw'] = math.atan2(rot[2], rot[0])
        an = getattr(self, '_pvp_an', None)
        if isinstance(an, str) and an:
            pose['anim'] = an[:40]
        bones = pad.read_my_packed_pose(p)
        if isinstance(bones, str) and bones:
            pose['bones'] = bones
        if p is not self.p or pad is not self.pad or actor != pad.p_act or banc != (pad.cur_banc or ''):
            return {}
        return pose

    def _server_pose_loop(self):
        """Capture and send periodic server poses without waiting for Tk."""
        stop = self._server_tx_stop
        last_hello = float('-inf')
        while not stop.wait(0.05):
            mode = getattr(self, 'mode', 'Story')
            now = time.monotonic()
            announce = now - last_hello >= 1.0
            if not announce and not (self.p and self.ready):
                continue
            try:
                pose = self._pvp_server_pose()
                if stop.is_set() or not pose or mode != getattr(self, 'mode', 'Story'):
                    continue
                if announce:
                    # v0.94.320: ukjent lag i PvP (rett etter mod-omstart) sendes ikke – serveren nullstilte da laget
                    tm = self._active_pvp_team() if mode == 'PvP' else None
                    extra = {} if (mode == 'PvP' and tm is None) else {'team': tm}
                    self._server_cmd('hello', mode=mode,
                                     model=getattr(self, 'look', '') or '', color=self.hat_color,
                                     **extra, **pose)
                    last_hello = now
                elif 'pos' in pose:
                    self._server_cmd('pose', mode=mode, **pose)
            except OSError:
                continue

    def _ctf_server_tick(self, now):
        """Server oot.premiumaroma.no eier 50-spiller AOI/peers (Story + PvP), og PvP-klokke/lobby/lag/score/runder."""
        is_pvp = getattr(self, 'mode', 'Story') == 'PvP'
        while True:
            try:
                m = self._server_states.get_nowait()
            except queue.Empty:
                break
            try:
                score = m.get('score') if m.get('t') == 'state' else None
                if not isinstance(score, dict):
                    continue
                clean = {k: int(score.get(k, 0)) for k in ('Blue', 'Red')}
                rnd = max(1, int(m.get('round', 1)))
            except (ValueError, TypeError):
                continue
            old = getattr(self, '_server_score', None)
            old_round = getattr(self, '_server_round', None)
            old_prof = getattr(self, '_pvp_profile', None)
            if not getattr(self, '_server_online', False):
                log(f'server: tilkoblet {SERVER_URL or f"{SERVER_ADDR[0]}:{SERVER_ADDR[1]}"}')
            self._server_online = True; self._server_seen = now
            self._server_score = clean; self._server_round = rnd; self._server_state = m
            self.pvp_peers = m['peers'] if isinstance(m.get('peers'), list) else []
            self._handle_presence(m)
            self._handle_server_chat(m.get('chat'))
            if m.get('account') in ('open', 'created', 'ok', 'denied'):
                if m['account'] != getattr(self, '_acct_state', None):
                    log(f"konto: serveren sier {m['account']} for {self.name}")
                    if m['account'] == 'denied' and getattr(self, '_acct_state', None) is not None:
                        self._append_chat_sys(f'⛔ Wrong password for {self.name} – PvP profile and inventory are locked until you type the right one in 🔒.')
                self._acct_state = m['account']
            if m.get('acct_msg') == 'changed' and getattr(self, '_acct_pending_key', None):
                keys = dict(self.cfg.get('account_keys') or {}); keys[self.name] = self._acct_pending_key
                self.cfg['account_keys'] = keys; save_cfg(self.cfg); self._acct_pending_key = None
                self._append_chat_sys('🔒 Password changed.')
                log(f'konto: passord byttet for {self.name}')
            elif m.get('acct_msg') == 'change_denied' and getattr(self, '_acct_pending_key', None):
                self._acct_pending_key = None
                self._append_chat_sys('⛔ Could not change the password (not logged in with the old one).')
            si_ = m.get('story_inv')
            if isinstance(si_, dict) and si_.get('error') == 'wrong_password':
                if not getattr(self, '_sinv_denied', False):
                    self._sinv_denied = True; self._inv_load_pending = 0
                    self._append_chat_sys(f'⛔ {self.name} has a password on the server – type it in the 🔒 field. Inventory is not loaded or saved until then.')
                    log(f'konto: serveren avviste nøkkelen for {self.name} – inventar lastes/lagres ikke')
                si_ = None
            elif isinstance(si_, dict) and si_.get('account') == 'created' and not getattr(self, '_acct_note', False):
                self._acct_note = True
                self._append_chat_sys(f'🔒 The name {self.name} is now yours on the server.')
            if getattr(self, '_inv_load_pending', 0) and isinstance(si_, dict):
                self._inv_load_pending = 0; self._sinv_loaded = True
                if not si_.get('inv'):
                    self._append_chat_sys(f'💾 No saved Story inventory for {self.name} yet')
                elif self.p and self.ready and getattr(self, 'rupees', None) and getattr(self, 'mode', 'Story') == 'Story':
                    try:
                        done, nb = self._story_inv_apply(si_['inv'])
                        self._sinv_last = None
                        self._append_chat_sys(f"💾 Inventory loaded: {', '.join(done)} (+{nb} items)")
                    except OSError as e:
                        self._append_chat_sys(f'⚠️ Inventory load failed: {e}')
            if not is_pvp:
                lobby = m.get('lobby') or {}
                token = (lobby.get('id'), lobby.get('name'))
                if token != getattr(self, '_story_lobby_token', None):
                    if getattr(self, '_story_lobby_token', None) is not None:
                        self._append_chat_sys(f"🌍 Story channel: {lobby.get('name') or 'Public'}")
                    self._story_lobby_token = token
                error = m.get('error')
                if error and error != getattr(self, '_server_error', None):
                    self._append_chat_sys(f'⚠️ {error}')
                self._server_error = error
                self._draw_story_lobby()
                continue
            if isinstance(m.get('shop'), dict):
                self._pvp_shop = m['shop']
            prof = m.get('profile')
            if isinstance(prof, dict):
                self._pvp_handle_profile(prof, old_prof)
            self._apply_arena((m.get('lobby') or {}).get('arena'))
            selected_mode = (m.get('lobby') or {}).get('game_mode')
            if selected_mode in ('ctf', 'deathmatch') and selected_mode != self._game_mode:
                self._game_mode = selected_mode
                log(f'server: spilltype er {selected_mode}')
                self._append_chat_sys('🔥 Capture the Flame' if selected_mode == 'ctf' else '⚔️ Deathmatch – first to 5 knockouts')
                if selected_mode == 'ctf':
                    self._ctf_reset_at = now + 2.5
            self._sync_pvp_travel(m.get('lobby') or {}, rnd, now)
            if isinstance(m.get('day_time'), int):
                self._server_day_clock = (m['day_time'] % 86400, now)
            error = m.get('error')
            if error and error != getattr(self, '_server_error', None):
                self._append_chat_sys(f'⚠️ {error}')
            self._server_error = error
            if old is not None and (clean != old or rnd != old_round):
                if max(old.values()) >= 5 and rnd > (old_round or 0):
                    winner = max(old, key=old.get)
                    self._append_chat_sys(f'🏆 {winner} wins the match! New match started.')
                else:
                    self._append_chat_sys(f'🔥 Score: Blue {clean["Blue"]} – {clean["Red"]} Red')
                log(f'server: score {old} -> {clean}, runde {old_round} -> {rnd}')
                if self._game_mode == 'ctf':
                    self._ctf_reset_at = now + 2.5
                    scoring_team = self._ctf_scoring_team(old, clean)
                    if scoring_team and rnd == old_round:
                        self._append_chat_sys(f'🎇 {scoring_team} scores!')
                        self._ctf_reset_at = now + 4.5
                        threading.Thread(target=self._ctf_celebrate, args=(scoring_team,),
                                         daemon=True, name='CtFCelebration').start()

    def _sync_pvp_travel(self, lobby, round_number, now):
        """Start the arena from server state and return from a finished large match."""
        started = bool(lobby.get('started'))
        token = (lobby.get('id'), lobby.get('started_at'), round_number) if started else None
        large = lobby.get('capacity') in (20, 50) and lobby.get('game_mode') == 'deathmatch'
        large_token = token if large else None
        previous = getattr(self, '_pvp_large_match', None)
        if not started:
            self._pvp_manual_lobby_tok = None
        if previous and previous != large_token:
            if getattr(self, '_pvp_travel_busy', False):
                return
            self._pvp_in_arena = self._pvp_lobby_done = False
            self._pvp_field_origin = None
            self._pvp_travel_retry = self._pvp_down_until = 0
            if not started and self.p and self.ready:
                self._pvp_lobby_try_t = now
                threading.Thread(target=self._pvp_go_lobby, daemon=True, name='PvPReturn').start()
        self._pvp_large_match = large_token
        if (started and token != getattr(self, '_pvp_manual_lobby_tok', None)
                and self.p and self.ready and not getattr(self, '_pvp_in_arena', False)
                and not getattr(self, '_pvp_travel_busy', False)
                and now >= getattr(self, '_pvp_travel_retry', 0)):
            self._pvp_travel_retry = now + 10.0
            threading.Thread(target=self._pvp_go_arena, daemon=True, name='PvPArena').start()

    @staticmethod
    def _ctf_scoring_team(old, new):
        """Return the team whose score increased; a round reset is not a point."""
        increased = [team for team in ('Blue', 'Red') if new.get(team, 0) > old.get(team, 0)]
        return increased[0] if len(increased) == 1 else None

    def _pick_game_mode(self, gm):
        """Trinn 1 -> 2 i PvP-lobbyen: vis valgene for valgt spillmodus."""
        self.game_mode_var.set(gm); self.mode_title.config(text=gm)
        self.cfg['game_mode_name'] = gm; self.cfg['game_mode_picked'] = True; save_cfg(self.cfg)
        self._game_mode_picked = True
        self.mode_pick.pack_forget(); self.mode_opts.pack(fill='x')
        if hasattr(self, 'arena_row'):   # v0.94.320: brettvalg for begge; CTF viser bare CTF-brett
            ctf = gm != 'Deathmatch'
            for k_, rb_ in getattr(self, '_arena_radios', {}).items():
                rb_.pack_forget()
                if not ctf or self.ARENAS[k_].get('ctf'):
                    rb_.pack(side='left', padx=4)
            if ctf and not self.ARENAS.get(self.arena_var.get(), {}).get('ctf'):
                self.arena_var.set('gohma')
            self.arena_row.pack(fill='x', padx=10, pady=(2, 0), before=self.lobby_games)
        self._draw_lobby()

    def _unpick_game_mode(self):
        self._game_mode_picked = False; self.cfg['game_mode_picked'] = False; save_cfg(self.cfg)
        self.mode_opts.pack_forget(); self.mode_pick.pack(fill='x')

    def _lobby_watch(self):
        selection = self.lobby_games.curselection()
        ids = getattr(self, '_lobby_ids', [])
        if selection and selection[0] < len(ids):
            self._pvp_team = None
            self._server_cmd('watch', lobby=ids[selection[0]])

    def _lobby_invite(self):
        who = self.invite_var.get().split('  ')[0].strip()
        if who:
            self._server_cmd('invite', to=who)
            self._append_chat_sys(f'✉️ Invited {who}')

    def _invite_accept(self):
        inv = getattr(self, '_shown_invite', None)
        if inv:
            self._server_cmd('join', lobby=inv.get('lobby'))

    def _invite_decline(self):
        inv = getattr(self, '_shown_invite', None)
        if inv:
            self._server_cmd('decline', lobby=inv.get('lobby'))
            self._shown_invite = None; self.invite_in.pack_forget()

    def _lobby_join(self):
        selection = self.lobby_games.curselection()
        ids = getattr(self, '_lobby_ids', [])
        if selection and selection[0] < len(ids):
            self._server_cmd('join', lobby=ids[selection[0]])

    def _active_pvp_team(self):
        """Returner valgt serverlag (Red/Blue/None), ikke overskriv lagvalg ved periodisk hello."""
        if hasattr(self, '_pvp_team'):
            return self._pvp_team
        # v0.94.320: etter mod-omstart – laget serveren har for meg (members)
        for pe in ((getattr(self, '_server_state', None) or {}).get('members') or ()):
            if isinstance(pe, dict) and pe.get('name') == getattr(self, 'name', None) and pe.get('team') in ('Red', 'Blue'):
                return pe.get('team')
        lk = (getattr(self, 'cfg', None) or {}).get('look')
        return lk if lk in ('Red', 'Blue') else None

    def _select_team(self, team):
        """Velg lag eller tilskuer på serveren uten at hello tilbakestiller valget."""
        if team in ('Red', 'Blue'):
            self._pvp_team = team
            return self._server_cmd('team', team=team)
        self._pvp_team = None
        return self._server_cmd('spectate')

    def _is_ctf_score_reporter(self):
        """Serveren godtar kun CtF-poeng fra lobbyverten; fall tilbake til _time_host() uten lobbyvert."""
        lobby_host = ((getattr(self, '_server_state', None) or {}).get('lobby') or {}).get('host')
        if lobby_host:
            return lobby_host == getattr(self, 'name', None)
        return self._time_host()

    def _lobby_ready(self):
        state = getattr(self, '_server_state', {})
        members = state.get('members', [])
        me = next((p for p in members if p.get('name') == self.name), {})
        self._server_cmd('ready', ready=not bool(me.get('ready')))

    def _story_lobby_create(self):
        name = " ".join(self.story_lobby_name.get().split())[:24]
        if not name:
            self._append_chat_sys('Skriv inn et lobbynavn, f.eks. noobcrew')
            return
        password = self.story_lobby_password.get()[:64]
        self.story_lobby_name.set('')
        self.story_lobby_password.set('')
        self._server_cmd('story_create', lobby_name=name, password=password)

    def _story_lobby_join(self):
        selection = self.story_lobby_list.curselection()
        ids = getattr(self, '_story_lobby_ids', [])
        if selection and selection[0] < len(ids):
            self._server_cmd('story_join', lobby=ids[selection[0]], password=self.story_lobby_password.get()[:64])

    def _draw_story_lobby(self):
        if not hasattr(self, 'story_lobby_list') or getattr(self, 'mode', 'Story') != 'Story':
            return
        state = getattr(self, '_server_state', {})
        current = state.get('lobby') or {}
        members = state.get('members') or []
        self.story_lobby_info.config(text=f"{current.get('name') or 'Public'} · {len(members)} player(s)")
        games = [g for g in (state.get('lobbies') or []) if g.get('id') == 0 or g.get('game_mode') == 'story']
        if not any(g.get('id') == 0 for g in games):
            games.insert(0, {'id': 0, 'name': 'Public', 'players': 0, 'capacity': 50})
        items = [f"{'●' if g.get('id') == current.get('id') else '○'} {'🔒 ' if g.get('protected') else ''}{g.get('name')}  ({g.get('players', 0)})" for g in games]
        old_selection = self.story_lobby_list.curselection()
        if list(self.story_lobby_list.get(0, 'end')) != items:
            self.story_lobby_list.delete(0, 'end')
            for item in items:
                self.story_lobby_list.insert('end', item)
            if old_selection and old_selection[0] < len(items):
                self.story_lobby_list.selection_set(old_selection[0])
        self._story_lobby_ids = [g.get('id') for g in games]

    def _draw_lobby(self):
        if not hasattr(self, 'lobby_games') or getattr(self, 'mode', 'Story') != 'PvP':
            return
        state = getattr(self, '_server_state', {})
        lobby = state.get('lobby') or {}
        elapsed = int(lobby.get('elapsed', 0))
        mode_name = 'Deathmatch' if self._game_mode == 'deathmatch' else 'Capture the Flame'
        score = state.get('score') or {'Blue': 0, 'Red': 0}
        self.lobby_info.config(text=f"{lobby.get('name', 'Connecting …')}  ·  host: {lobby.get('host') or '–'}  ·  "
                                    f"{'started' if lobby.get('started') else 'waiting'}  {elapsed // 60:02d}:{elapsed % 60:02d}\n"
                                    f"{mode_name}  ·  Blue {score.get('Blue', 0)} – {score.get('Red', 0)} Red")
        if lobby.get('id') and self.game_mode_var.get() != mode_name:   # i en kamp: vis den kampens modus
            self.game_mode_var.set(mode_name)
            if getattr(self, '_game_mode_picked', False):
                self.mode_title.config(text=mode_name)
        want = 'deathmatch' if self.game_mode_var.get() == 'Deathmatch' else 'ctf'
        games = [g for g in (state.get('lobbies') or []) if g.get('id') != 0 and (g.get('id') == lobby.get('id') or g.get('game_mode', 'ctf') == want)]
        items = [f"#{g.get('id')}  {'DM' if g.get('game_mode') == 'deathmatch' else 'CtF'}"
                 f"{ {'sword': '  Sword course', 'zora': "  Zora's Domain", 'field': '  Hyrule Field'}.get(g.get('arena'), '')}  {g.get('name')}  "
                 f"{g.get('players')}/{g.get('capacity')}  {'playing' if g.get('started') else 'open'}" for g in games]
        old_selection = self.lobby_games.curselection()
        if list(self.lobby_games.get(0, 'end')) != items:
            self.lobby_games.delete(0, 'end')
            for item in items:
                self.lobby_games.insert('end', item)
            if old_selection and old_selection[0] < len(items):
                self.lobby_games.selection_set(old_selection[0])
        self._lobby_ids = [g.get('id') for g in games]
        members = state.get('members') or []
        self.lobby_members.config(text="\n".join(
            f"{'✓' if p.get('ready') else '○'} {p.get('name')}  ·  {p.get('team') or 'Spectator'}  ·  {p.get('assets') or '…'}"
            for p in members) or 'No players')
        online = state.get('online') or []
        vals = tuple(f"{o.get('name')}  ({'lobby' if not o.get('lobby') else 'game ' + str(o.get('lobby'))})" for o in online)
        if tuple(self.invite_box.cget('values') or ()) != vals:
            self.invite_box.config(values=vals)
        invites = state.get('invites') or []
        inv = invites[-1] if invites else None
        if inv and inv.get('lobby') != lobby.get('id'):
            self._shown_invite = inv
            self.invite_in_lbl.config(text=f"✉️ {inv.get('from')} invites you to game {inv.get('lobby')}")
            if not self.invite_in.winfo_ismapped():
                self.invite_in.pack(fill='x', padx=10, pady=(2, 3), before=self.assets_info)
        elif self.invite_in.winfo_ismapped():
            self._shown_invite = None; self.invite_in.pack_forget()
        self._maybe_send_assets()
        if not state.get('assets_match', True):
            diff = getattr(self, '_asset_diff', None) or {}
            cats = diff.get('cats') or []
            # v0.94.304: hvem har andre filer enn meg (serveren sender hvert medlems hash) – vises før dere kobler til
            my12 = (self.asset_hash or '')[:12]
            odd_ = sorted(str(p.get('name')) for p in (members or ()) if isinstance(p, dict) and p.get('assets')
                          and my12 and p.get('assets') != my12 and p.get('name') != self.name)
            who_ = f" with {', '.join(odd_)}" if odd_ else ''
            if cats:
                self.assets_info.config(text=f"Assets: MISMATCH{who_} – {', '.join(cats)} differ (se /assets / logg)", fg=WARN)
            else:
                self.assets_info.config(text=f'Assets: MISMATCH{who_} – textures/models/patches differ (se /assets)', fg=WARN)
            if odd_ and tuple(odd_) != getattr(self, '_odd_assets_shown', None):
                self._odd_assets_shown = tuple(odd_)
                self._append_chat_sys(f"⛔ {', '.join(odd_)} {'has' if len(odd_) == 1 else 'have'} different game files than you – "
                                      f"you can't play together until everyone runs the same mod version.")
                log(f'assets: lobbyen sier ulike filer hos {odd_} (min {my12})')
        elif self.asset_hash and members and all(p.get('assets') for p in members):
            self.assets_info.config(text=f'Assets: OK  ·  {self.asset_hash[:12]}', fg=OK)
        else:
            self.assets_info.config(text='Assets: checking …', fg=MUTED)

    def _maybe_send_assets(self):
        """Send vår lokale filoversikt én gang per P2P-økt så eventuelle asset-avvik logges detaljert."""
        files = getattr(self, 'asset_files', None)
        ah = getattr(self, 'asset_hash', None)
        fs = getattr(self, 'friend_session', None)
        if not (self.peer and fs and files and ah and hasattr(self, 'gs')):
            return
        key = (fs, self.gport, ah)
        if getattr(self, '_assets_sent_key', None) == key:
            return
        self._assets_sent_key = key
        try:
            self.gs.sendto(json.dumps({
                't': 'assets', 's': self.session, 'name': self.name,
                'hash': ah[:12], 'files': files,
            }).encode(), self.peer)
        except OSError as e:
            self._assets_sent_key = None
            log(f'assets: kunne ikke sende oversikt: {e!r}')

    def _handle_incoming_assets(self, m):
        """Motta vennens filliste og logg nøyaktig hvilke filer som skiller seg."""
        files = m.get('files')
        if not isinstance(files, dict):
            return
        self.friend_assets = {
            's': m.get('s'),
            'name': m.get('name') or 'venn',
            'hash': m.get('hash') or '?',
            'files': files,
        }
        self._log_asset_diff()

    def _log_asset_diff(self):
        mine = getattr(self, 'asset_files', None)
        fa = getattr(self, 'friend_assets', None)
        if not mine or not fa:
            return
        theirs = fa.get('files') or {}
        fname = fa.get('name') or 'venn'
        my_h = (getattr(self, 'asset_hash', None) or '?')[:12]
        fr_h = (fa.get('hash') or '?')[:12]
        diff = diff_asset_manifests(mine, theirs)
        self._asset_diff = diff
        key = (my_h, fr_h, fa.get('s'))
        if getattr(self, '_asset_diff_key', None) == key:
            return
        self._asset_diff_key = key
        om, ot, ch, cats = diff['only_mine'], diff['only_theirs'], diff['changed'], diff['cats']
        if not (om or ot or ch):
            log(f'assets-diff: LIKT med {fname} ({my_h})')
            if getattr(self, '_assets_block', None):
                self._assets_block = None
                self.ui(self._append_chat_sys, f'✅ Game files now match {fname} – you can play together.')
            return
        if self.cfg.get('require_same_assets', True):   # v0.94.303: ulike filer = ikke spill sammen (dukker/synk av)
            self._assets_block = fa.get('s')
        log(f'assets-diff: ULIKE vs {fname} ({my_h} vs {fr_h}) – kategorier={cats}')
        for rel in om:
            sz, fh = mine[rel]
            log(f'assets-diff:   bare hos meg: {rel} ({sz} B, {fh})')
        for rel in ot:
            sz, fh = theirs[rel]
            log(f'assets-diff:   bare hos {fname}: {rel} ({sz} B, {fh})')
        for rel in ch:
            s1, h1 = mine[rel]; s2, h2 = theirs[rel]
            log(f'assets-diff:   ulik: {rel} (meg {s1} B/{h1} vs {fname} {s2} B/{h2})')
        summary = f"⚠️ Assets mismatch vs {fname}: {', '.join(cats)} (kun meg {len(om)}, kun {fname} {len(ot)}, ulike {len(ch)}) – se /assets eller logg"
        self.ui(self._append_chat_sys, summary)
        if getattr(self, '_assets_block', None):
            names_ = [os.path.basename(r) for r in (list(om) + list(ot) + list(ch))[:4]]
            self.ui(self._append_chat_sys, f"⛔ You can't play with {fname} until your game files match "
                                           f"({', '.join(names_)}{' …' if len(om) + len(ot) + len(ch) > 4 else ''}). "
                                           f"Both need the same mod version – update and restart the mod.")

    def _ctf_server_point(self, team):
        if self._server_cmd('score', team=team):
            log(f'server: sendte CtF-poeng for {team}')

    def connect(self, ip):
        self.peer = (ip, self.gport); self.cfg["last_ip"] = ip; save_cfg(self.cfg)
        log(f"kobler til {ip}:{self.gport}")
        self.friend_session = None
        self.set_check("net", "work", f"connecting to {ip} …")

    def _connect_selected(self):
        sel = self.plist.curselection()
        ips = getattr(self, '_live_ips', [])
        if sel and sel[0] < len(ips):
            self.connect(ips[sel[0]])   # Listen viser nick; IP brukes kun internt ved tilkobling.

    def _connect_ip(self):
        ip = self.ip_var.get().strip()
        if ip:
            self.connect(ip)

    def _fast_net_loop(self):
        """Plan 1 (v0.31): Egen 60 Hz bakgrunnstråd som sender ferske kontroller- og posisjonspakker (t=fast)
        og mottar innkommende pakker uten å vente på Tkinter sin GUI-timer (~25 Hz). Fjerner siste rest av lugging!"""
        next_t = time.perf_counter()
        while True:
            next_t += 1.0 / 60.0
            rem = next_t - time.perf_counter()
            if rem > 0.001:
                time.sleep(rem)
            elif rem < -0.1:
                next_t = time.perf_counter()
            try:
                if not hasattr(self, "gs"):
                    continue
                now = time.time()
                self._drain_udp(now)
                p = self.p if self.ready else None
                peer = self.peer
                if getattr(self, '_web_render_sample', None) is not None or getattr(self, '_web_render_live', False):
                    self._render_deku_web(p, now)
                if p is not None and peer is not None:
                    apos = self.pad.my_apos(p)
                    arot = self.pad.my_arot(p)
                    # v0.94.153: tidsstempel pa prøven (monotont, samme klokke som posisjonen
                    # ble lest). Mottakeren interpolerer pa SENDERENS tidsakse, slik at
                    # nettets ankomstjitter ikke blir posisjonsjitter.
                    ts = time.monotonic()
                    cam_a = self.pad.my_cam_angle(p, self.cam_off)
                    pad_hex = self.pad.my_pad(p)
                    if apos and pad_hex is not None:
                        bones_b64 = self.pad.read_my_packed_pose(p) if hasattr(self.pad, "read_my_packed_pose") else None
                        # v0.94.179: avrunding + kompakt JSON holder hele UDP-pakken under 1472 B MTU (ingen fragmentering/lag)
                        r4 = lambda seq: [round(v, 4) for v in seq]
                        pkt = {
                            "t": "fast",
                            "s": self.session,
                            "name": self.name,
                            "color": self.hat_color,
                            "ts": round(ts, 4),
                            "pos": [round(apos[0], 4), round(apos[1] + 0.56, 4), round(apos[2], 4)],
                            "face": [round(arot[6], 4), round(arot[8], 4)] if arot else [0.0, 1.0],
                            "apos": r4(apos),
                            "arot": r4(arot) if arot else None,
                            "cam_a": round(cam_a, 4) if isinstance(cam_a, (int, float)) else cam_a,
                            "pad": pad_hex,
                            "banc": self.pad.cur_banc,
                        }
                        if bones_b64:
                            pkt["bones"] = bones_b64
                        # v0.94.304: spillet tegner ~30 bilder/s, vi sender 60/s – annenhver pakke var en kopi. Send bare når
                        # noe har endret seg (ny spillramme, knapp, kamera, sone), ellers en livstegn-pakke hvert 0,25 s.
                        sig_ = (pkt["apos"], pkt["arot"], pkt["cam_a"], pad_hex, pkt["banc"], bones_b64)
                        if sig_ == getattr(self, '_fast_sig', None) and time.time() - getattr(self, '_fast_sent_t', 0) < 0.25:
                            pkt = None
                        else:
                            self._fast_sig = sig_
                        try:
                            if pkt is None:
                                raise OSError('uendret')
                            _fp = json.dumps(pkt, separators=(',', ':')).encode(); self.gs.sendto(_fp, peer)
                            self._fast_sent_t = time.time(); perf_add('fast-B', len(_fp))   # v0.94.303: state-pakken trenger da ikke posisjon/bein
                        except OSError:
                            pass
                    if self.pad.scene_changed and now < self.pad.suppress_warp_until:
                        self.pad.scene_changed = False          # vårt eget tvangs-sonebytte: ikke send varsel tilbake (ping-pong)
                    if self.pad.scene_changed and (now - getattr(self, "_last_warp_send_t", 0) > 4.0):
                        self._last_warp_send_t = now
                        self.pad.scene_changed = False
                        warp_pkt = {
                            "t": "party_warp",
                            "s": self.session,
                            "name": self.name,
                            "banc": self.pad.read_banc(p) or self.pad.cur_banc,
                            "start": self.pad.START_POS.get(self.pad.read_banc(p) or self.pad.cur_banc),
                            "pos": apos, "rot": arot,
                        }
                        try:
                            self.gs.sendto(json.dumps(warp_pkt).encode(), peer)
                            self._append_chat_sys("🚪 You entered a new area / went through a door!")
                            log("Dør-varsel: sendte party_warp (varsel) til vennen")
                        except OSError:
                            pass
                self._drain_udp(now)
            except Exception:
                pass

    def _handle_incoming_chat(self, friend_s, chat_list):
        if not isinstance(chat_list, list):
            return
        for item in chat_list:
            if not isinstance(item, dict):
                continue
            cid = item.get("id")
            txt = item.get("text")
            sender = item.get("name") or (self.friend.get("name") if self.friend else "Venn")
            col = item.get("color") or (self.friend.get("color") if self.friend else "Blå")
            if cid is not None and txt and (friend_s, cid) not in self.chat_seen:
                self.chat_seen.add((friend_s, cid))
                self._append_chat_msg(sender, str(txt), col)
                log(f"chat inn ({sender}): {txt}")

    def _handle_party_warp(self, m):
        now = time.time()
        if now - getattr(self, "_last_warp_recv_t", 0) < 3.0:
            return
        self._last_warp_recv_t = now
        w_name = m.get("name", "Vennen")
        banc, pos, rot, force = m.get("banc"), m.get("pos"), m.get("rot"), bool(m.get("force"))
        if banc:
            self.pad.friend_banc = banc
            self.pad.warp_banc, self.pad.warp_t = banc, now   # vennen er på vei dit – ikke lag Link 2 her før vi er der også
            self.pad.learn_start(banc, m.get('start'), 'fra venn')
        if force:
            self._append_chat_sys(f"🌀 {w_name} teleported you to them!")
        else:
            self._append_chat_sys(f"🚪 {w_name} went through a door / into a new area!")
        log(f"party_warp inn fra {w_name}: banc={banc} force={force} (her: {self.pad.cur_banc})")
        if not (force or (self.tvang and getattr(self, 'mode', 'Story') != 'PvP')) or not (self.p and self.ready):
            return
        if self._in_boss_fight():
            self._append_chat_sys('⚠️ Ignored teleport: you are in a boss fight.')
            return
        p = self.p
        if banc and self.pad.cur_banc and banc != self.pad.cur_banc:
            if not force and now - getattr(self, "_last_tvang_t", 0) < 5.0:      # ping-pong-sperre
                return
            self._last_tvang_t = now

            def _go():
                ok = self.pad.change_banc(p, banc)
                if ok:
                    self.pad.suppress_warp_until = time.time() + 20
                    self.pad._pending_tp = (banc, pos, rot, time.time()) if (force and pos) else None
                    self.ui(self._append_chat_sys, f"🌀 Følger {w_name} til {banc} …")
                else:
                    self.ui(self._append_chat_sys, f"⚠️ Kan ikke følge til {banc} (ukjent startpunkt eller call_v1-patchen mangler)")
            threading.Thread(target=_go, daemon=True).start()
        elif force and pos:
            # v0.94.154: ikke teleport midt i en rom-omlasting. Lokal PC frøs 00:38
            # (0 FPS) da en teleport traff midt i scenelastingen.
            if now - getattr(self.pad, '_banc_since', 0) < 8.0:
                self.pad._pending_tp = (self.pad.cur_banc, pos, rot, now)
                log(f'party_warp: teleport utsatt til rommet er stabilt (banc={banc})')
            else:
                self.pad.teleport_player(p, pos, rot)

    def _puppet_follower_on(self, now=None):
        """v0.94.161: bruk CoopFollow::Follower-modellen for dukkenes bevegelse?

        Standard er PAA (v0.94.161): modellen halverer de store hoppene
        (maks avvik -68 %) og kutter etterslepet mot fjernspilleren med
        65-75 %, mot ~1 cm ekstra per-bilde-deviasjon.

        Filen 'puppet_follower.flag' i mod-mappen kan overstyre:
          '1'/'on'/'ja' -> PAA     '0'/'off'/'nei' -> AV     (filen mangler -> PAA)
        """
        now = now if now is not None else time.time()
        if now - getattr(self, '_fol_flag_t', 0) < 1.0:
            return getattr(self, '_fol_flag', True)
        self._fol_flag_t = now
        try:
            path = os.path.join(APP_DIR, 'puppet_follower.flag')
            if not os.path.exists(path):
                self._fol_flag = True          # standard: modellen er PAA
            else:
                try:
                    with open(path, encoding='utf-8-sig') as fh:
                        txt = fh.read().strip().lower()
                except OSError:
                    txt = ''
                self._fol_flag = txt not in ('0', 'off', 'nei', 'false', 'no')
        except OSError:
            self._fol_flag = True
        return self._fol_flag

    def _puppet_force_mtx(self, now=None):
        """v0.94.159: skal modellmatrisen settes direkte (batch-flagg bit 1)?

        Uten force_set_mtx skriver vi bare posisjonen, og speletts egen fysikk
        integrerer dukkeaktoren paa toppen -> dukken ligger etter og vaerer.
        Filen 'puppet_force_mtx.flag' i mod-mappen slar den paa (1) eller av (0).
        """
        now = now if now is not None else time.time()
        if now - getattr(self, '_fm_flag_t', 0) < 1.0:
            return getattr(self, '_fm_flag', False)
        self._fm_flag_t = now
        try:
            path = os.path.join(APP_DIR, 'puppet_force_mtx.flag')
            if not os.path.exists(path):
                self._fm_flag = False
            else:
                try:
                    with open(path, encoding='utf-8-sig') as fh:
                        txt = fh.read().strip().lower()
                except OSError:
                    txt = ''
                self._fm_flag = txt not in ('0', 'off', 'nei', 'false', 'no')
        except OSError:
            self._fm_flag = False
        return self._fm_flag

    def _puppet_arrival_mode(self, now=None):
        """v0.94.157: A/B-bryter for tidsaksen.

        Filen 'puppet_arrival_time.flag' i mod-mappen styrer modusen:
          * finnes ikke            -> ny tidsakse (senderens tidsstempel)
          * innhold '1'/'on'/'ja'  -> gammel oppførsel (ANKOMSTTID)
          * innhold '0'/'off'/'nei'-> ny tidsakse
        Da kan gammel og ny interpolasjon måles mot hverandre i samme sesjon.
        """
        now = now if now is not None else time.time()
        if now - getattr(self, '_arr_flag_t', 0) < 1.0:
            return getattr(self, '_arr_flag', False)
        self._arr_flag_t = now
        try:
            path = os.path.join(APP_DIR, 'puppet_arrival_time.flag')
            if not os.path.exists(path):
                self._arr_flag = False
            else:
                try:
                    with open(path, encoding='utf-8-sig') as fh:
                        txt = fh.read().strip().lower()
                except OSError:
                    txt = ''
                self._arr_flag = txt not in ('0', 'off', 'nei', 'false', 'no')
        except OSError:
            self._arr_flag = False
        return self._arr_flag

    def _sample_log(self, arrival, ts, pos):
        """v0.94.158: logg mottatte prøver (ankomsttid, sendertid, posisjon).

        Gir kontrollert offline A/B: de SAMME prøvene kan rendres både på
        ankomsttidsakse (gammel) og senderens tidsakse (ny).
        """
        try:
            fn = getattr(self, '_sample_fn', None)
            if fn is None:
                fn = self._sample_fn = os.path.join(APP_DIR, 'logs', f'samples_{PC}.csv')
                new = not os.path.exists(fn)
                fh = open(fn, 'a', encoding='utf-8', newline='')
                if new:
                    fh.write('arrival,ts,x,y,z\n')
                self._sample_fh = fh
            fh = self._sample_fh
            fh.write(f'{arrival:.5f},{ts:.5f},{pos[0]:.4f},{pos[1]:.4f},{pos[2]:.4f}\n')
            if (getattr(self, '_sample_n', 0) or 0) % 40 == 0:
                fh.flush()
            self._sample_n = (getattr(self, '_sample_n', 0) or 0) + 1
        except OSError:
            pass

    def _net_delay(self, raw):
        """v0.94.157: nettets forsinkelse = ankomsttid - sendertid.

        Minimumsfiltret gir referansen; resten (median over min) er nettjitteren,
        altså nettopp feilen den gamle ankomsttids-interpolasjonen ville gitt.
        """
        d = getattr(self, '_net_raw_min', None)
        if d is None or raw < d:
            d = raw
            self._net_raw_min = d
        exc = raw - d
        lst = getattr(self, '_net_exc', None)
        if lst is None:
            lst = self._net_exc = []
        lst.append(exc)
        if len(lst) > 240:
            del lst[0]
        t = time.time()
        if t - getattr(self, '_net_log_t', 0) >= 5.0:
            self._net_log_t = t
            s = sorted(lst)
            med = s[len(s) // 2]
            p95 = s[min(len(s) - 1, int(len(s) * 0.95))]
            log(f'nett-jitter: forsinkelse over min median {med*1000:.1f} ms, '
                f'p95 {p95*1000:.1f} ms (n={len(s)})')

    def _friend_sample_time(self, ts, now):
        """v0.94.154: senderens tidsstempel -> lokal tid for prøven.

        offset = lokal klokke - senderklokke (inneholder nettforsinkelsen). Vi tar
        minimums-estimatet (den minste forsinkelsen vi har sett) og lar det stige
        sakte. Da havner prøvene pa senderens EKTE tidsakse: avstanden mellom to
        prover blir senderens egen avstand, uansett nettjitter. Uten dette brukte
        interpolasjonen ankomsttiden, og nettjitteren ble posisjonsjitter.
        """
        if not isinstance(ts, (int, float)) or ts <= 0:
            return now
        off = now - float(ts)
        cur = getattr(self, '_friend_off', None)
        if cur is None or off < cur:
            self._friend_off = off
        else:
            self._friend_off = cur + (off - cur) * 0.02
        return float(ts) + self._friend_off

    def _drain_udp(self, now):
        with self._fast_net_lk:
            while True:
                try:
                    data, addr = self.gs.recvfrom(65535)
                except OSError:
                    break
                try:
                    m = json.loads(data)
                except ValueError:
                    continue
                if m.get("s") == self.session:
                    continue
                t = m.get("t")
                if t == "chat":
                    self._handle_incoming_chat(m.get("s"), m.get("chat"))
                    continue
                if t == "party_warp":
                    self._handle_party_warp(m)
                    continue
                if t == "assets":
                    self._handle_incoming_assets(m)
                    continue
                if t not in ("state", "fast"):
                    continue
                if getattr(self, '_assets_block', None) and m.get("s") == self._assets_block:
                    continue   # v0.94.303: ulike spillfiler – ingen dukke/synk med denne spilleren (chat og assets går fortsatt)
                if self.peer is None:            # den andre koblet til oss – koble tilbake automatisk
                    self.connect(addr[0])
                reset = m.get("s") != self.friend_session
                if reset:
                    self._friend_fast_t = 0.0
                    self._friend_last_ts = 0.0
                # v0.94.182: En treg `state`-pakke fra Tkinter-tråden (~15 Hz, 50-120 ms forsinket, uten `ts`)
                # må ALDRI overskrive fersk 60 Hz `fast`-posisjon/rotasjon/bein eller `_friend_sample_t`!
                # Det var rotårsaken til 20-31 cm bakoverhopp (rubber-banding) hvert halvsekund.
                is_fast = (t == "fast")
                stale_state = (not is_fast) and (not reset) and (now - getattr(self, "_friend_fast_t", 0.0) < 0.5)
                ts = m.get("ts")
                if is_fast and isinstance(ts, (int, float)) and ts > 0:
                    last_ts = getattr(self, "_friend_last_ts", 0.0)
                    if not reset and float(ts) < last_ts:
                        continue  # gammel / ombyttet UDP-pakke
                    self._friend_last_ts = float(ts)
                    self._friend_fast_t = now
                    self._net_delay(time.time() - float(ts))
                    if self._puppet_arrival_mode():
                        # v0.94.157: A/B - gammel oppførsel (ankomsttid)
                        self._friend_sample_t = now
                    else:
                        self._friend_sample_t = self._friend_sample_time(ts, time.time())
                elif not stale_state:
                    if is_fast:
                        self._friend_fast_t = now
                    self._friend_sample_t = now
                if is_fast and isinstance(m.get("apos"), list) and len(m["apos"]) >= 3:
                    # v0.94.158: logg prøven for offline A/B
                    self._sample_log(time.time(), float(ts) if isinstance(ts, (int, float)) else 0.0, m["apos"])
                if not stale_state:
                    try:   # v0.55/0.94.92: vennen hoppet langt (teleport) -> brems bare Link 2 (_friend_tp_t), aldri egne spillkall/scenebytte (_tp_t)
                        op, np_ = (self.friend or {}).get("pos"), m.get("pos")
                        if op and np_ and math.dist(op[:3], np_[:3]) > 15:
                            self.pad._friend_tp_t = now
                    except (TypeError, ValueError):
                        pass
                if self.friend is None or reset:
                    self.friend = dict(m)
                elif stale_state:
                    for k, v in m.items():
                        if k not in ("pos", "apos", "arot", "face", "bones", "ts", "cam_a"):
                            self.friend[k] = v
                else:
                    self.friend.update(m)
                self.friend_t, self.friend_session = now, m.get("s")
                if m.get("pt"):
                    self._rx_pt = (m["pt"], now)
                pe = m.get("pe")
                if isinstance(pe, list) and len(pe) == 2 and pe[0]:
                    rtt = (now - pe[0] - pe[1]) * 1000
                    if 0 <= rtt < 5000:
                        self.ping_ms = rtt if getattr(self, "ping_ms", None) is None else self.ping_ms * 0.8 + rtt * 0.2
                self._rx_count = getattr(self, "_rx_count", 0) + 1
                if m.get("banc"):
                    self.pad.friend_banc = m.get("banc")
                if m.get("look") in LOOKS:
                    if m.get("look") != getattr(self.pad, 'friend_look', None):
                        log(f'tunika: vennen har {m.get("look")}')
                    self.pad.friend_look = m.get("look")
                # Auto-forskjellig hattefarge hvis begge har valgt nøyaktig samme farge ved tilkobling:
                f_col = self.friend.get("color")
                if f_col and f_col == self.hat_color and self.session > (self.friend_session or 0):
                    alt = "Blå" if self.hat_color != "Blå" else "Rød"
                    self.hat_color = alt
                    self.ui(lambda a=alt: (self.color_var.set(a), self.color_dot.config(fg=HAT_COLORS[a])))
                    self._append_chat_sys(f"You both had {f_col} – your colour was switched to {alt} so you differ!")
                if "chat" in m:
                    self._handle_incoming_chat(m.get("s"), m.get("chat"))
                # v0.94.277: serveren styrer inventaret (eget per spiller, husket på navn) – ingen P2P-deling av rupees/ammo/bag
                if t == "state" and self.ready and getattr(self, 'mode', 'Story') != 'PvP' and not self.cfg.get('server_inventory', True):
                    try:
                        # v0.94.268: «reset» over kan allerede være brukt opp av en «fast»-pakke (sesjonen settes der),
                        # og spill-omkobling lager nye tellere uten ny sesjon. Da ble vennens kumulative tall regnet som
                        # funn (+102 rupees). Egen teller-epoke per tellersett, sjekket bare her i state-pakkene.
                        ce = (m.get("s"), m.get("ce"))
                        creset = ce != getattr(self, '_friend_ce', None) or getattr(self, '_my_ce_seen', None) != (getattr(self, 'cnt_epoch', 0), id(self.syncs))
                        self._friend_ce = ce; self._my_ce_seen = (getattr(self, 'cnt_epoch', 0), id(self.syncs))
                        if creset:
                            log(f"tellere: ny teller-epoke (venn {ce[1]}) – nullstiller kumulative tall")
                        cums = m.get("cums") or {"rupees": m.get("cum", 0)}
                        vals = m.get("vals") or {"rupees": m.get("rupees")}
                        for n, c in self.syncs.items():
                            if n in cums:
                                c.apply(cums[n], creset)
                            c.equalize(vals.get(n), now, force=creset)
                        if getattr(self, "bag", None):
                            self.bag.apply(m, creset, now)
                    except OSError:
                        pass
            alive = bool(self.friend and now - self.friend_t < 2) and self._server_says_friend_present(now)
            if self.p is not None:
                my_cam_a = self.pad.my_cam_angle(self.p, self.cam_off)
                mirror_alive = alive and not bool(getattr(self, 'cfg', {}).get('pvp_puppet_pool', True))
                f_pos = None
                if mirror_alive and self.friend:
                    f_pos = self.friend.get("apos")
                    if not f_pos and self.friend.get("pos"):
                        fp = self.friend["pos"]
                        f_pos = [fp[0], fp[1] - 0.56, fp[2]]
                self.pad.apply(self.p,
                               self.friend.get("pad") if mirror_alive and self.friend else None,
                               self.friend.get("cam_a") if mirror_alive and self.friend else None,
                               my_cam_a,
                               f_pos,
                               self.friend.get("arot") if mirror_alive and self.friend else None,
                               alive=mirror_alive,
                               cam_off=self.cam_off,
                               hearts=self.friend.get("hearts") if (mirror_alive and self.friend) else None)

    def _cycle_host(self):
        if getattr(self, 'mode', 'Story') == 'PvP':
            return   # PvP-vert og klokke eies av .121; lobbyvert vises i lobbykortet.
        order = ("auto", "me", "friend")
        self.host_mode = order[(order.index(getattr(self, "host_mode", "auto")) + 1) % 3]
        self.cfg["host_mode"] = self.host_mode; save_cfg(self.cfg)
        log(f"vert: valg satt til {self.host_mode}")
        self._net_draw_t = 0

    def _time_host(self):
        """Vert (tid/vær/plattformer/skjeletter): valgt i vinduet (Meg/Vennen), ellers PC-en med lavest IP."""
        if not self.peer:
            return True
        mine_m = getattr(self, "host_mode", "auto")
        their_m = (self.friend or {}).get("hm", "auto")
        want_me = mine_m == "me" or their_m == "friend"
        want_them = mine_m == "friend" or their_m == "me"
        if want_me != want_them:          # begge er enige (eller bare én har valgt) -> følg valget
            return want_me
        f = self.peer[0]; pre = f.rsplit('.', 1)[0]
        mine = next((ip for ip in local_ips() if ip.rsplit('.', 1)[0] == pre), None)
        if not mine:
            return True
        return tuple(int(x) for x in mine.split('.')) < tuple(int(x) for x in f.split('.'))

    AMMO_REFUND = {0x8E8: 'nøtter', 0x910: 'frø', 0x938: 'pinner'}   # pinner tas ikke med: de brukes også opp når en brennende pinne knekker

    def _story_inv_snapshot(self):
        """v0.94.268: Story-inventaret per spiller (navn) til serveren: tellere, pinner og hele bag-blokken."""
        p, rup = self.p, self.rupees.off
        inv = {n: int(c.expected) for n, c in self.syncs.items()}
        inv['sticks'] = int(p.u32(rup + 0x938))
        bag = getattr(self, 'bag', None)
        if bag:
            inv['bag'] = {f'{r:x}': int(bag.last.get(r, 0)) for r in bag.rels if r not in bag.ignored and bag.last.get(r)}
            for r, c in bag.counters.items():
                if r not in bag.ignored:
                    inv['bag'][f'{r:x}'] = int(c.expected)
        return inv

    def _safe_start_tick(self, now):
        """v0.94.289: trygg start. Lagringsfilen starter om natten i Hyrule Field med 1 hjerte ved fiender, og spillere døde
        mens de sto stille. Én gang per nytt spill (ny SaveVar-adresse), 1 s etter at Link er i verden: fyll livet til maks.
        Ikke ved 0 liv (Game Over) og ikke i PvP. Av med config safe_start: false."""
        if (not self.cfg.get('safe_start', True) or getattr(self, 'mode', 'Story') != 'Story'
                or not (self.p and self.ready and getattr(self, 'rupees', None)) or self.rupees.off is None):
            return
        off = self.rupees.off
        if getattr(self, '_ss_off', None) != off:
            self._ss_off = off; self._ss_t = now + 1.0; self._ss_done = False
            return
        if self._ss_done or now < self._ss_t:
            return
        self._ss_done = True
        p = self.p
        cur, mx = p.u32(off + 0x28), p.u32(off + 0x50)
        if 0 < cur < mx <= 80:
            p.write(p.base + off + 0x28, struct.pack('<I', mx))
            log(f'trygg start: liv {cur}/{mx} -> {mx}/{mx} (kvarte hjerter)')
        else:
            log(f'trygg start: liv {cur}/{mx} – ingen endring')

    def _story_inv_tick(self, now):
        if (getattr(self, 'mode', 'Story') != 'Story' or not (self.p and self.ready and getattr(self, 'rupees', None))
                or now - getattr(self, '_sinv_t', 0) < 2.0):
            return
        self._sinv_t = now
        if getattr(self, '_sinv_rup', None) != self.rupees.off:     # nytt spill/tilkobling: vent 20 s før første lagring
            self._sinv_rup = self.rupees.off; self._sinv_ready = now + 20
            if self.cfg.get('server_inventory', True):   # ny tilkobling: hent eget inventar fra serveren
                self._sinv_loaded = False; self._inv_load_pending = now; self._server_cmd('inv_get', key=self._account_key())
                log(f'inv-db: henter Story-inventar for {self.name} fra serveren (tilkobling)')
            return
        if self.cfg.get('server_inventory', True) and not getattr(self, '_sinv_loaded', True):
            # ikke lagre før serveren har svart (ellers kunne spillets lagringsfil overskrive serverens inventar)
            if now - (getattr(self, '_inv_load_pending', 0) or 0) > 10:
                self._inv_load_pending = now; self._server_cmd('inv_get', key=self._account_key())
            return
        if now < getattr(self, '_sinv_ready', 0) or now - (getattr(self, '_inv_load_pending', 0) or 0) < 10:
            return
        try:
            inv = self._story_inv_snapshot()
        except (OSError, AttributeError):
            return
        last_ = getattr(self, '_sinv_last', None)
        if isinstance(last_, dict) and inv != last_:   # v0.94.278: revisjon – hver endring i loggen (for mye loot synes med en gang)
            ch = [f'{k} {last_.get(k)}->{v}' for k, v in inv.items() if k != 'bag' and last_.get(k) != v]
            nb = sum(1 for k, v in (inv.get('bag') or {}).items() if (last_.get('bag') or {}).get(k) != v)
            if ch or nb:
                big = any(k == 'rupees' and isinstance(last_.get(k), int) and v - last_[k] > 200 for k, v in inv.items())
                log(f"inv-db: endring {', '.join(ch)}{f' (+{nb} bag-poster)' if nb else ''}{' – MISTENKELIG STOR ØKNING' if big else ''}")
        if getattr(self, '_sinv_denied', False):   # feil passord: ikke prøv å lagre (serveren avviser uansett)
            return
        if inv != getattr(self, '_sinv_last', None) and self._server_cmd('inv_save', inv=inv, key=self._account_key()):
            self._sinv_last = inv

    def _story_inv_apply(self, inv):
        """Skriv lagret Story-inventar (fra serveren) inn i spillet. Bare på /inv load."""
        p, rup = self.p, self.rupees.off
        done = []
        for n, c in self.syncs.items():
            v = inv.get(n)
            if isinstance(v, int) and 0 <= v <= 999:
                c._set(min(c.cap(), v)); done.append(f'{n}={v}')
        v = inv.get('sticks')
        if isinstance(v, int) and 0 <= v <= 99:
            for o in (0x938, 0x93C):
                p.write(p.base + rup + o, struct.pack('<I', v))
            done.append(f'sticks={v}')
        bag = getattr(self, 'bag', None); nb = 0
        if bag and isinstance(inv.get('bag'), dict):
            for k, v in inv['bag'].items():
                try:
                    r = int(k, 16)
                except (TypeError, ValueError):
                    continue
                if r not in bag.rels or r in bag.ignored or not isinstance(v, int) or not 0 <= v <= 0xFFFFFFFF:
                    continue
                if r in bag.counters:
                    bag.counters[r]._set(v)
                else:
                    bag._write(r, v)
                nb += 1
        log(f'inv-db: lastet Story-inventar for {self.name}: {", ".join(done)}, {nb} bag-poster')
        return done, nb

    def _ammo_tick(self, now):
        """Ammo brukt av Link 2 (vennens kast speiles i vårt spill) gis tilbake: faller tallet uten at VI har trykket en
        gjenstandsknapp de siste 1,5 s, var det Link 2."""
        if not (self.p and self.ready and getattr(self, 'rupees', None)) or now - getattr(self, '_am_t', 0) < 0.05:
            return
        # v0.94.268: AV med dukker (standard): ingen Link 2-kopi bruker ammo lenger. Refusjonen spiste i stedet vennens
        # forbruk som kom via den delte telleren og sendte det tilbake som +1 -> uendelig med nøtter/frø.
        if bool(getattr(self, 'cfg', {}).get('pvp_puppet_pool', True)):
            return
        self._am_t = now
        try:
            raw = bytes.fromhex(self.pad.my_pad(self.p) or '')
            btn = struct.unpack_from('<I', raw, 0)[0] if len(raw) >= 4 else 0
            if btn & ~0xC03:   # alt utenom A (0x1), B (0x2), +/- (0x400/0x800)
                self._am_btn_t = now
            last = self.__dict__.setdefault('_am_last', {})
            for rel, nm in self.AMMO_REFUND.items():
                v = self.p.u32(self.rupees.off + rel)
                old = last.get(rel)
                sy_ = next((c for c in self.syncs.values() if c.off == self.rupees.off + rel), None)
                if sy_ is not None and now - getattr(sy_, 'set_t', 0) < 2.0:
                    last[rel] = v; continue   # endringen kom fra vennen via delt teller – ikke Link 2
                if old is not None and 0 <= old - v <= 3 and v < old and now - getattr(self, '_am_btn_t', 0) > 4.0:   # 4 s: sikting med sprettert kan ta tid
                    self.p.write(self.p.base + self.rupees.off + rel, struct.pack('<I', old))
                    log(f'ammo: Link 2 brukte {old - v} {nm} – gitt tilbake ({v} -> {old})')
                    v = old
                last[rel] = v
        except (OSError, ValueError, struct.error):
            pass

    def _flag_tick(self, now):
        """Verdens-flagg (kister, vegger, brytere …): send flagg som går 0 -> 1 og holder seg i 8 s; skriv inn vennens."""
        if now - getattr(self, '_fl_tick', 0) < 1.0 or getattr(self, '_fl_busy', False) or not (self.p and self.ready):
            return
        self._fl_tick = now; self._fl_busy = True
        self._room_reload_tick(now)
        fresh = bool(self.friend and now - self.friend_t < 2)
        fb = (self.friend or {}).get('flagbits') if fresh else None
        theirs = []
        if fb:
            try:
                raw = __import__('base64').b64decode(fb)
                theirs = [k * 8 + j for k, byte in enumerate(raw) if byte for j in range(8) if byte >> j & 1]
            except Exception:  # noqa: BLE001
                theirs = []
        def run():
            try:
                _tf = time.perf_counter()
                cur = self.pad.read_bools(self.p)
                perf_add('flagg-les', time.perf_counter() - _tf)
                if cur is None:
                    return
                prev = getattr(self, '_fl_prev', None)
                pend = self.__dict__.setdefault('_fl_pend', {}); noisy = self.__dict__.setdefault('_fl_noisy', set())
                sent = self.__dict__.setdefault('flags_out', set()); got = self.__dict__.setdefault('_fl_got', set())
                if prev is not None and len(prev) == len(cur) and prev != cur:
                    for i in range(len(cur)):
                        if cur[i] != prev[i]:
                            if cur[i] and i not in got:
                                pend.setdefault(i, now)
                            elif not cur[i]:
                                noisy.add(i); pend.pop(i, None)
                # v0.65: synket boss-start – når ShutIn (8595) slår seg på hos meg, si fra; vennen hoppes hit så introen starter likt
                try:
                    SH = 8595
                    if SH < len(cur):
                        if prev is not None and len(prev) == len(cur) and cur[SH] and not prev[SH]:
                            self._my_bst = [round(time.time(), 2), self.pad.cur_banc, self.pad.my_apos(self.p)]
                            log(f'cutscene: boss-start hos meg {self._my_bst}')
                        fb = (self.friend or {}).get('bst')
                        if (isinstance(fb, list) and len(fb) == 3 and fb[2] and fb[0] != getattr(self, '_bst_done', None)
                                and time.time() - fb[0] < 6 and fb[1] == self.pad.cur_banc and not cur[SH]
                                and getattr(self, 'cut_sync_on', True)):
                            self._bst_done = fb[0]
                            r = self.pad.teleport_player(self.p, fb[2])
                            log(f'cutscene: vennen startet bossen – hopper til {[round(v, 1) for v in fb[2]]} -> {r}')
                            self._append_chat_sys('🎬 Boss intro synced: moved you to your friend')
                except Exception as e:  # noqa: BLE001
                    log(f'cutscene: feil {e!r}')
                t_first = self.__dict__.setdefault('_fl_t0', now)
                if not getattr(self, '_fl_full_done', False) and now - t_first > 60:   # én gang: send alle satte flagg (fremgang fra før modden startet)
                    self._fl_full_done = True
                    full = {i for i in range(len(cur)) if cur[i] and i not in noisy and i not in PadLink.BOSS_FLAGS}
                    sent.update(full); log(f'flagg: sender alle {len(full)} satte verdens-flagg én gang')
                for i, t0 in list(pend.items()):
                    if now - t0 >= 8.0:
                        pend.pop(i)
                        if cur[i] and i not in noisy and i not in sent and i not in PadLink.BOSS_FLAGS:
                            sent.add(i); log(f'flagg: sender verdens-flagg {i} til vennen')
                nset = []
                # v0.57: ikke skriv vennens flagg de første 15 s etter flytting (frys-test)
                for i in (theirs if time.time() - getattr(self.pad, '_tp_t', 0) >= 15.0 else []):
                    if i in PadLink.BOSS_FLAGS:
                        continue
                    if isinstance(i, int) and 0 <= i < len(cur) and not cur[i] and i not in got:
                        if self.pad.set_bool(self.p, i):
                            got.add(i); nset.append(i)
                    elif isinstance(i, int):
                        got.add(i)
                if nset:
                    log(f'flagg: satte {len(nset)} verdens-flagg fra vennen: {nset[:12]}' + (' …' if len(nset) > 12 else ''))
                    fz = (self.friend or {}).get('banc')
                    if fz and fz == self.pad.cur_banc and now - getattr(self.pad, '_banc_since', now) > 10:
                        self._reload_due = now + 2.0   # vent litt – flere flagg kommer ofte samtidig
                if sent:
                    bits = bytearray((max(sent) >> 3) + 1)
                    for i in sent:
                        bits[i >> 3] |= 1 << (i & 7)
                    self._fl_bits = __import__('base64').b64encode(bytes(bits)).decode()
                self._fl_prev = self.pad.read_bools(self.p) or cur
            except Exception as e:  # noqa: BLE001
                log(f'flagg: feil {e!r}')
            finally:
                self._fl_busy = False
        threading.Thread(target=run, daemon=True).start()

    def _room_reload_tick(self, now):
        """Vennen løste/åpnet noe i samme rom: last rommet på nytt (inn igjen samme sted) så stiger, plattformer o.l. vises."""
        due = getattr(self, '_reload_due', 0)
        if not due or now < due:
            return
        self._reload_due = 0
        if now - getattr(self, '_last_reload_t', 0) < 20 or now - getattr(self, '_last_tvang_t', 0) < 10:
            return
        p, banc = self.p, self.pad.cur_banc
        # v0.94.247: Aldri auto-omlast store utendørssoner (HyruleField, KokiriForest, Market osv.) – det teleporterer spilleren til inngangen og kan henge spillet!
        if not banc or not any(k in banc for k in ('Dungeon', 'DekuTree', 'Dodongo', 'Jabu', 'Temple', 'Well', 'IceCavern', 'Ganon')):
            return
        start = (self.pad.START_POS.get(banc) or self.pad.read_last_start(p)) if (p and self.ready and banc) else None
        if not start:
            log(f'rom-omlasting: hopper over (ukjent startpunkt for {banc})')
            return
        pos, rot = self.pad.my_apos(p), self.pad.my_arot(p)
        if not pos:
            return
        self._last_reload_t = self._last_tvang_t = now
        def go():
            ok = self.pad.change_banc(p, banc, start)
            log(f'rom-omlasting: startpunkt {start}')
            if ok:
                self.pad.suppress_warp_until = time.time() + 20
                self.pad._pending_tp = (banc, pos, rot, time.time())
                self.ui(self._append_chat_sys, '🔄 Your friend changed something here – reloading the room …')
            log(f'rom-omlasting: {banc} -> {ok}')
        threading.Thread(target=go, daemon=True).start()

    def _actor_hp_addr(self, p, a):
        """Vert-adresser (liv, maks) for en aktør, mellomlagret. None hvis den ikke har liv."""
        c = self.__dict__.setdefault('_hp_addr', {})
        if a in c:
            return c[a]
        try:
            d = self.pad.delta
            u = lambda off: struct.unpack('<Q', p.read(p.base + off, 8))[0]
            life = u(u(a + 0x270) - d + 0x2B8) - d
            r = (u(life + 0x1C10) - d + 8, u(life + 0x1C18) - d + 8)
        except Exception:  # noqa: BLE001
            r = None
        if len(c) > 400:
            c.clear()
        c[a] = r
        return r

    def _share_hp(self, p, a, nm, their_hp, their_max):
        """v0.94.218: Delt skade og død: laveste liv vinner (inkl. 0 så begge ser fienden dø samtidig)."""
        if not isinstance(their_hp, int) or not isinstance(their_max, int) or their_hp < 0:
            return
        ad = self._actor_hp_addr(p, a)
        if not ad:
            return
        try:
            cur, mx = struct.unpack('<I', p.read(p.base + ad[0], 4))[0], struct.unpack('<I', p.read(p.base + ad[1], 4))[0]
        except OSError:
            return
        if their_max != mx and 'Boss' in nm and 'Egg' not in nm and 'Larva' not in nm and 0 < their_max <= 100000:
            # v0.94.241: adopter vertens eksakte co-op boss-maks-HP (f.eks. 42 HP på Gohma, også ved korrigering ned)
            p.write(p.base + ad[1], struct.pack('<I', their_max))
            p.write(p.base + ad[0], struct.pack('<I', their_hp))
            log(f'boss: adopterte co-op HP {nm} {cur}/{mx} -> {their_hp}/{their_max}')
            return
        if mx != their_max or cur <= their_hp or cur > 100000:
            return
        p.write(p.base + ad[0], struct.pack('<I', their_hp))
        if time.time() - getattr(self, '_hp_log', 0) > 1:
            self._hp_log = time.time(); log(f'skade: {nm} {cur} -> {their_hp}/{mx} (vennen slo)')

    def _actor_hp(self, p, a):
        """(liv, maks) for en aktør via livskomponenten, eller (None, None)."""
        try:
            d = self.pad.delta
            u = lambda off: struct.unpack('<Q', p.read(p.base + off, 8))[0]
            life = u(u(a + 0x270) - d + 0x2B8) - d
            cur = struct.unpack('<I', p.read(p.base + u(life + 0x1C10) - d + 8, 4))[0]
            mx = struct.unpack('<I', p.read(p.base + u(life + 0x1C18) - d + 8, 4))[0]
            return cur, mx
        except Exception:  # noqa: BLE001
            return None, None

    def _boss_tick(self, now):
        """Boss-logger (bare lesing): skriver navn, posisjon, retning og liv for bosser til logs/boss_<PC>.csv hvert 0,5 s."""
        if now - getattr(self, '_boss_t', 0) < 0.03 or not (self.p and self.ready):
            return
        self._boss_t = now
        bosses = getattr(self.pad, '_bosses', None)
        if not bosses:
            self._my_boss = None
            return
        p = self.p
        me = self.pad.my_apos(p)
        rows = []; mine = []
        write_csv = now - getattr(self, '_boss_csv_t', 0) >= 0.5
        if write_csv:
            self._boss_csv_t = now
        for a, nm in list(bosses.items()):
            try:
                pos = p.f32(a + 0x31C, 3); rot = p.f32(a + 0x328, 9)
                if struct.unpack('<Q', p.read(p.base + a, 8))[0] != self.pad.main + 0x4B25E18:
                    bosses.pop(a, None); continue
            except OSError:
                bosses.pop(a, None); continue
            # v0.94.224: kun boss/egg/larver i samme rom (< 35 m) – ellers spam-spawner følgeren 2F-egg 70 m unna
            if me and math.dist(pos, me) >= 35.0:
                continue
            hp, mx = self._actor_hp(p, a)
            # v0.94.241: eksakt co-op standard-HP for kjente bosser (Gohma = alltid 42 HP, aldri 2x på nytt ved mod-omstart!)
            if (self._time_host() and nm == 'Enemy_DungeonBoss_Gohma'
                    and isinstance(hp, int) and isinstance(mx, int) and mx != 42 and 0 < mx <= 5000):
                srv_p = (getattr(self, '_server_state', None) or {}).get('present')
                n_pl = len(srv_p) if isinstance(srv_p, list) and len(srv_p) >= 2 else (2 if (self.friend and now - getattr(self, 'friend_t', 0) < 5) else 1)
                if n_pl >= 2:
                    ad = self._actor_hp_addr(p, a)
                    if ad:
                        new_mx = 42
                        new_cur = new_mx if hp >= mx else min(hp, new_mx)
                        try:
                            p.write(p.base + ad[1], struct.pack('<I', new_mx))
                            p.write(p.base + ad[0], struct.pack('<I', new_cur))
                            hp, mx = new_cur, new_mx
                            log(f'boss: co-op standard HP {nm} -> {new_cur}/{new_mx}')
                        except OSError:
                            pass
            if a not in self.__dict__.setdefault('_boss_seen', set()):
                self._boss_seen.add(a); log(f'boss: fant {nm} @0x{a:X} pos {[round(v, 1) for v in pos]} liv {hp}/{mx}')
                self.ui(self._append_chat_sys, f'👑 Boss spotted: {nm} – logging for sync research')
            mine.append((a, nm, pos, rot, hp, mx))
            if 'Egg' not in nm and 'Larva' not in nm:
                r3 = self.__dict__.setdefault('_boss_awake2', {}).setdefault(a, [pos[1], pos[1], pos])
                r3[0] = min(r3[0], pos[1]); r3[1] = max(r3[1], pos[1]); r3[2] = pos
            if write_csv:
                rows.append(f'{time.strftime("%H:%M:%S")}.{int(now * 10) % 10},{nm},0x{a:X},{pos[0]:.2f},{pos[1]:.2f},{pos[2]:.2f},'
                            + ','.join(f'{v:.3f}' for v in rot) + f',{hp},{mx},{self.pad.cur_banc}')
        def _an(a):
            try:
                return list(self.pad.read_anim(p, a))
            except Exception:  # noqa: BLE001
                return [None, None]
        self._my_boss = [[nm, [round(v, 3) for v in pos], [round(v, 4) for v in rot], hp, mx] + _an(a) for a, nm, pos, rot, hp, mx in mine] or None
        self._my_boss_bones = None
        self._boss_sync(p, mine, now)
        if rows:
            try:
                fn = os.path.join(APP_DIR, 'logs', f'boss_{PC}.csv')
                with open(fn, 'a', encoding='utf-8') as f:
                    f.write(chr(10).join(rows) + chr(10))
            except OSError:
                pass

    def _boss_tick_async(self, now):
        """Keep boss animation lookups off the Tk event thread."""
        if (getattr(self, '_boss_tick_busy', False)
                or now - getattr(self, '_boss_t', 0) < 0.03
                or not (self.p and self.ready)):
            return
        self._boss_tick_busy = True

        def run():
            try:
                self._boss_tick(now)
            except Exception as exc:
                log(f'boss: synk feilet {exc!r}')
            finally:
                self._boss_tick_busy = False

        threading.Thread(target=run, daemon=True, name="BossTick").start()

    REMOTE_FILE = 'remote_cmd.txt'   # én kommando per linje; modden kjører dem som chat-kommandoer og sletter fila

    def _remote_tick(self, now):
        """Fjernstyring for testing: les remote_cmd.txt ved exe-en, kjør hver linje som om den ble skrevet i chatten."""
        if now - getattr(self, '_rc_t', 0) < 0.5:
            return
        self._rc_t = now
        fn = os.path.join(APP_DIR, self.REMOTE_FILE)
        if not os.path.exists(fn):
            return
        try:
            lines = [l.strip() for l in open(fn, encoding='utf-8-sig').read().splitlines() if l.strip()]
            os.remove(fn)
        except OSError:
            return
        for line in lines[:20]:
            log(f'fjern-kommando: {line}')
            if line.lower().split()[0] in self.INFO_CMDS:
                threading.Thread(target=self._info_cmd, args=(line,), daemon=True).start()
            else:
                def run(t=line):   # fjernstyring for testing (fil ved exe-en) går forbi host-sperren
                    self._remote_run = True
                    try:
                        self.chat_var.set(t); self._send_chat()
                    finally:
                        self._remote_run = False
                self.ui(run)

    INFO_CMDS = ('/zone', '/cfg', '/spawn', '/plates', '/blinkmode', '/paint', '/skip', '/status', '/enemies', '/boss', '/flags', '/items', '/ping', '/bot', '/ctf', '/arena', '/lobby', '/match', '/team', '/inv', '/buy', '/bgm', '/assets', '/pvpflags', '/pvpfilter', '/torches', '/tp', '/memsnap', '/actors', '/help')

    def _info_cmd(self, line):
        """Info-kommandoer (svar i chat og logg). Brukes også fra chatten."""
        cmd = line.lower().split()[0]
        p, pad, now = self.p, self.pad, time.time()
        out = []
        try:
            if cmd == '/help':
                out.append('Modus/PvP: /mode Story | /mode PvP | /lobby | /arena | /bgm [sang|off] [vol] | /match [ctf|dm|ready|start|create 2v2|join ID] | /team [Blue|Red|Spectate] | /inv | /buy <vare> | /assets | /ctf | /torches | /pvpfilter | /pvpflags 10771,11111')
                out.append('Debug/Verden: /status | /near | /enemies | /boss | /flags | /items | /opendoor | /goto x y z | /tp | /ping')
                out.append('AI/Bot: /target [0|1|2] | /blind [off] | /bossfollow [off] | /aihold [off] | /resetboss | /testmove | /bot ... | /skip ...')
            elif cmd == '/skip':
                SKIP.clear(); SKIP.update(x for x in (line.split()[1] if len(line.split()) > 1 else '').split(',') if x)
                out.append(f'hopper over: {sorted(SKIP)}'); log(f'skip: {sorted(SKIP)}')
            elif cmd == '/zone':   # v0.94.287: /zone <sone> [startpunkt] – ekte sonebytte som en dør (f.eks. /zone InsideTheDekuTree Entrance)
                parts = line.split()
                if len(parts) < 2 or not (self.p and self.pad.p_act is not None):
                    out.append('bruk: /zone <sone> [startpunkt]  (f.eks. /zone InsideTheDekuTree Entrance)')
                elif 'Boss' in parts[1]:
                    out.append('zone: bossrom er sperret (spillet henger)')
                else:
                    banc_, start_ = parts[1], (parts[2] if len(parts) > 2 else ('Entrance' if parts[1] == 'InsideTheDekuTree' else None))
                    r_ = False
                    for _try in range(30):   # som PvP-byttet: vent til ingen hendelse kjører, prøv igjen (inntil ~60 s)
                        pad_ = self.pad
                        try:
                            an_ = pad_.read_anim(self.p, pad_.p_act)[0] if pad_.p_act is not None else None
                        except Exception:  # noqa: BLE001
                            an_ = None
                        if pad_.p_act is not None and an_ != 'EvtWait' and not pad_.event_busy(self.p) and time.time() - getattr(pad_, '_tp_t', 0) > 6.0:
                            r_ = pad_.change_banc(self.p, banc_, start_)
                            if r_:
                                break
                        if _try % 5 == 0:   # v0.94.289: hvorfor venter vi?
                            log(f'zone: venter (forsøk {_try}): anim={an_} hendelse={pad_.event_busy(self.p)} '
                                f'teleport for {time.time() - getattr(pad_, "_tp_t", 0):.0f} s siden, change_banc={r_}')
                        time.sleep(2.0)
                    log(f'zone: {banc_} @ {start_} -> {r_}')
                    out.append(f'zone: {banc_} @ {start_} -> {r_}')
            elif cmd == '/spawn':   # v0.94.283 test: /spawn <aktørnavn> [høyde] – lager aktøren 1,5 m foran egen Link
                parts = line.split()
                if len(parts) < 2 or not (self.p and self.pad.p_act is not None):
                    out.append('bruk: /spawn <navn> [høyde]')
                else:
                    nm_, dy_ = parts[1], (float(parts[2]) if len(parts) > 2 else 1.2)
                    sc_ = float(parts[3]) if len(parts) > 3 else 1.0   # v0.94.291: /spawn <navn> [høyde] [skala]
                    lp_ = self.p.f32(self.pad.p_act + 0x31C, 3)
                    pos_ = [lp_[0] + 1.0, lp_[1] + dy_, lp_[2] + 1.0]
                    def _sp(nm_=nm_, pos_=pos_, sc_=sc_):
                        r_ = self.pad.create_actor(self.p, nm_, pos_, scale=sc_)
                        log(f'spawn-test: {nm_} ved {[round(v, 1) for v in pos_]} skala {sc_} -> {r_}')
                        for t_ in (1.0, 3.0, 8.0):
                            time.sleep(t_)
                            f_ = self.pad._list_actors_raw(self.p, prefix=nm_) or {}
                            log(f'spawn-test: etter {t_:.0f}s finnes {len(f_)} {nm_}: {[(hex(k), [round(x, 1) for x in v[1]]) for k, v in f_.items()][:3]}')
                    threading.Thread(target=_sp, daemon=True).start()
                    out.append(f'spawn-test: lager {nm_}')
            elif cmd == '/cfg':   # v0.94.307 test: /cfg <nøkkel> [verdi] – les/sett en innstilling (verdi som JSON, ellers tekst)
                parts = line.split(None, 2)
                if len(parts) < 2:
                    out.append(f'bruk: /cfg <nøkkel> [verdi]  ({CFG})')
                else:
                    if len(parts) > 2:
                        try:
                            v_ = json.loads(parts[2])
                        except ValueError:
                            v_ = parts[2]
                        self.cfg[parts[1]] = v_; save_cfg(self.cfg)
                    out.append(f'cfg {parts[1]} = {self.cfg.get(parts[1])!r}  ({CFG})')
            elif cmd == '/blinkmode':   # /blinkmode 40 | all
                self.pad.blink_mode = (line.split()[1] if len(line.split()) > 1 else 'all')
                self.pad.__dict__.get('_pup_blink_addrs', {}).clear()
                out.append(f'blinkmodus: {self.pad.blink_mode}')
            elif cmd == '/paint':   # v0.94.262: AV – adressesøk med F_LD8 på ugyldig adresse frøs spillet (se HANDOVER)
                out.append('maling er slått av (frøs spillet) – egen farge byttes ved neste omstart')
            elif cmd == '/plates':   # v0.94.291: /plates on|off – navneskilt over de andre spillerne
                v = (line.split()[1].lower() if len(line.split()) > 1 else '')
                if v in ('on', 'off', 'på', 'av'):
                    self.cfg['nameplates'] = v in ('on', 'på'); save_cfg(self.cfg)
                out.append(f"navneskilt: {'på' if self.cfg.get('nameplates', True) else 'av'}")
            elif cmd == '/ping':
                out.append('pong')
            elif cmd == '/pvpflags':   # /pvpflags 10771,11111 – hvilke boss-flagg som holdes av i PvP (i tillegg til dørflaggene)
                v = line.split()[1] if len(line.split()) > 1 else ''
                self.cfg['pvp_flags'] = [int(x) for x in v.split(',') if x.strip().isdigit()]; save_cfg(self.cfg)
                out.append(f"pvp-flagg: {self.cfg['pvp_flags']}")
            elif cmd == '/pvpfilter':
                if p and pad.hR is not None:
                    fl, hits = p.u32(pad.hR + 0xEF8, 2)
                    out.append(f'pvp-meldingssperre: aktiv={bool(fl)} (R+0xEF8={fl}), blokkerte={hits} (R+0xEFC)')
                else:
                    out.append('pvp-meldingssperre: ingen R funnet ennå')
            elif cmd == '/tp':   # v0.94.322 test: /tp x y z – teleporter egen Link, logger landingspunkt etter 3 s
                parts = line.split()
                try:
                    pos_ = [float(v) for v in parts[1:4]]
                    assert len(pos_) == 3
                except Exception:  # noqa: BLE001
                    out.append('bruk: /tp x y z')
                else:
                    r_ = self.pad.teleport_player(self.p, pos_)
                    def _landed(pos_=pos_):
                        time.sleep(3.0)
                        log(f'tp: {pos_} -> landet {[round(v, 2) for v in (self.pad.my_apos(self.p) or [])]}')
                    threading.Thread(target=_landed, daemon=True).start()
                    out.append(f'tp: {pos_} -> {r_}')
            elif cmd == '/actors':   # v0.94.322 test: /actors [filter] – antall levende aktører per navn (logges)
                parts = line.split(); flt = parts[1].lower() if len(parts) > 1 else ''
                allm = {}; self.pad._scan_full_t = 0
                found = self.pad._scan_actors_raw(self.p, allm) or {}
                allm.update({a_: v_[0] for a_, v_ in found.items()})
                cnt = {}
                for a_, nm_ in allm.items():
                    if flt in nm_.lower():
                        cnt[nm_] = cnt.get(nm_, 0) + 1
                log(f'actors ({len(allm)} totalt, filter {flt!r}): ' + ', '.join(f'{k}×{v}' for k, v in sorted(cnt.items())))
                me_ = self.pad.my_apos(self.p); near = []
                for a_, nm_ in allm.items():
                    try:
                        q_ = self.p.f32(a_ + 0x31C, 3); near.append((math.dist(q_, me_), nm_))
                    except Exception:  # noqa: BLE001
                        pass
                log('actors nærmest: ' + ', '.join(f'{n_} {d_:.1f}m' for d_, n_ in sorted(near)[:25]))
                out.append(f'actors: {len(cnt)} navn (se logg)')
            elif cmd == '/memsnap':   # v0.94.322 test: /memsnap <sek> – lagrer Link- og Weapon_DekuStick-minne hvert 0.2 s (logs/memsnap.bin)
                parts = line.split(); secs_ = float(parts[1]) if len(parts) > 1 else 10.0
                def _snap(secs_=secs_):
                    pad_, p_ = self.pad, self.p
                    allm = {}; pad_._scan_full_t = 0
                    pad_._scan_actors_raw(p_, allm)
                    sticks = [a for a, nm in allm.items() if nm == 'Weapon_DekuStick']
                    regs = [('link', pad_.p_act)] + [(f'stick{i}', a) for i, a in enumerate(sticks)]
                    log(f'memsnap: {[(n, hex(a)) for n, a in regs]} i {secs_} s')
                    import pickle
                    frames = []; t0 = time.time()
                    while time.time() - t0 < secs_:
                        fr = {'t': time.time() - t0}
                        for n, a in regs:
                            try:
                                fr[n] = p_.read(p_.base + a, 0x4000)
                            except OSError:
                                fr[n] = None
                        frames.append(fr); time.sleep(0.2)
                    with open(os.path.join(APP_DIR, 'logs', 'memsnap.bin'), 'wb') as fh:
                        pickle.dump({'regs': regs, 'frames': frames}, fh)
                    log(f'memsnap: {len(frames)} bilder lagret')
                threading.Thread(target=_snap, daemon=True).start()
                out.append(f'memsnap: {secs_} s')
            elif cmd == '/torches':
                torches = getattr(self, '_ctf_actors', {}) or {}
                lit = getattr(self, '_ctf_lit', {}) or {}
                out.append(f'ctf tent-cache={lit}, arena={getattr(self, "_pvp_in_arena", False)}, game={getattr(self, "_game_mode", None)}')
                for tm, a in torches.items():
                    try:
                        s2c, s30 = p.u32(a + 0x2C, 2)
                        s480 = p.u32(a + 0x480)
                        pos = [round(v, 1) for v in p.f32(a + 0x31C, 3)]
                        lit_now, v6c = self._ctf_torch_lit(a)
                        hx = f'0x{v6c:X}' if v6c is not None else 'None'
                        out.append(f'  {tm} @0x{a:X}: pos={pos} +2C={s2c} +30={s30} +480={s480} pb0+6C={hx} lit={lit_now}')
                    except OSError as e:
                        out.append(f'  {tm} @0x{a:X}: OSError {e}')
            elif cmd == '/ctf':
                self._ctf_setup(); out.append('ctf: stolper satt opp på nytt')
            elif cmd == '/lobby':
                lb = (getattr(self, '_server_state', None) or {}).get('lobby') or {}
                if lb.get('started'):
                    self._pvp_manual_lobby_tok = (lb.get('id'), lb.get('started_at'), getattr(self, '_server_round', 1))
                    if lb.get('host') == self.name:
                        self._server_cmd('stop')
                threading.Thread(target=self._pvp_go_lobby, daemon=True, name='CmdLobby').start()
                out.append('pvp: lobbyovergang forsøkt')
            elif cmd == '/arena':
                self._pvp_manual_lobby_tok = None
                threading.Thread(target=self._pvp_go_arena, daemon=True, name='CmdArena').start()
                out.append('pvp: arenaovergang forsøkt')
            elif cmd == '/assets':
                ah = (getattr(self, 'asset_hash', None) or '?')[:12]
                files = getattr(self, 'asset_files', None) or {}
                out.append(f'assets: meg={ah} ({len(files)} filer)')
                fa = getattr(self, 'friend_assets', None)
                if fa and files:
                    d = diff_asset_manifests(files, fa.get('files'))
                    fn = fa.get('name') or 'venn'
                    fh = (fa.get('hash') or '?')[:12]
                    if not (d['only_mine'] or d['only_theirs'] or d['changed']):
                        out.append(f'assets-diff: likt med {fn} ({fh})')
                    else:
                        out.append(f"assets-diff vs {fn} ({fh}): kategorier={d['cats']}")
                        for r in d['only_mine']:
                            out.append(f"  kun meg: {r} ({files[r][0]} B, {files[r][1]})")
                        for r in d['only_theirs']:
                            v = fa['files'][r]
                            out.append(f"  kun {fn}: {r} ({v[0]} B, {v[1]})")
                        for r in d['changed']:
                            v1, v2 = files[r], fa['files'][r]
                            out.append(f"  ulik: {r} (meg {v1[0]} B/{v1[1]} vs {fn} {v2[0]} B/{v2[1]})")
                else:
                    out.append('assets-diff: venter på vennens filliste')
            elif cmd == '/team':
                arg = (line.split()[1] if len(line.split()) > 1 else '').capitalize()
                if arg in ('Blue', 'Red'):
                    self._select_team(arg); out.append(f'server: lag {arg}')
                elif arg.lower() in ('spectate', 'spec', 'none'):
                    self._select_team(None); out.append('server: tilskuer')
                else:
                    out.append(f'server: nåværende lag={self._active_pvp_team()} (bruk Blue|Red|Spectate)')
            elif cmd == '/inv':
                if getattr(self, 'mode', 'Story') != 'PvP':
                    sub = line.split()[1:]
                    if sub and sub[0].lower() == 'load':
                        self._inv_load_pending = time.time()
                        self._server_cmd('inv_get', key=self._account_key())
                        out.append(f'inv-db: henter lagret Story-inventar for {self.name} fra serveren …')
                    else:
                        last = getattr(self, '_sinv_last', None)
                        out.append(f'inv-db ({self.name}): lagres automatisk på serveren hvert 5. s ved endring. '
                                   f'Sist sendt: ' + (', '.join(f'{k}={v}' for k, v in last.items() if k != 'bag') + f", {len(last.get('bag') or {})} bag-poster" if last else 'ingenting ennå')
                                   + ' | /inv load = hent tilbake')
                else:
                    pr = getattr(self, '_pvp_profile', None)
                    if not pr:
                        out.append('pvp-db: venter på profil fra PvP-server (.121)')
                    else:
                        inv = pr.get('inventory') or {}
                        inv_txt = ', '.join(f'{k}={v}' for k, v in sorted(inv.items())) or 'tomt'
                        out.append(f"pvp-db ({self.name}): rubies={pr.get('rubies', 0)} | W/L/K={pr.get('wins', 0)}/{pr.get('losses', 0)}/{pr.get('kills', 0)} | {inv_txt}")
                        shop = getattr(self, '_pvp_shop', None) or {}
                        if shop:
                            out.append('butikk (/buy <vare>): ' + ', '.join(f"{k} (+{v['qty']})={v['price']}r" for k, v in shop.items()))
            elif cmd == '/buy':
                if getattr(self, 'mode', 'Story') != 'PvP':
                    out.append('pvp-db: /buy fungerer kun i PvP-modus')
                else:
                    sub = line.split()[1:] if len(line.split()) > 1 else []
                    if not sub:
                        shop = getattr(self, '_pvp_shop', None) or {}
                        out.append('bruk: /buy <vare> (' + (', '.join(shop) or 'sticks, nuts, seeds, bombs, potion') + ')')
                    else:
                        item_id = sub[0].lower()
                        self._server_cmd('buy', item_id=item_id)
                        out.append(f'pvp-db: sendte kjøp av {item_id}')
            elif cmd == '/bgm':
                sub = line.split()[1:] if len(line.split()) > 1 else []
                cur_tr, cur_vol = self._pvp_lobby_bgm_cfg()
                if not sub:
                    out.append(f'pvp-bgm: sang={cur_tr}, volum={cur_vol:.2f} (bruk: /bgm <shop|desert|drugstore|minigame|house|fairy|market|off> [0.0..1.0])')
                else:
                    tr, vol = cur_tr, cur_vol
                    for tok in sub:
                        tl = tok.lower()
                        try:
                            v = float(tok)
                            if 0.0 <= v <= 1.0:
                                vol = round(v, 2)
                                continue
                        except ValueError:
                            pass
                        if tl == 'default':
                            tr, vol = self.PVP_LOBBY_BGM_DEFAULT, self.PVP_LOBBY_BGM_VOL_DEFAULT
                        elif tl in self.PVP_LOBBY_BGM_ALIASES:
                            tr = self.PVP_LOBBY_BGM_ALIASES[tl]
                        elif tok.startswith('BGM_'):
                            tr = tok
                    self.cfg['pvp_lobby_bgm'] = tr
                    self.cfg['pvp_lobby_bgm_vol'] = vol
                    self.cfg['pvp_jukebox_arena'] = True
                    save_cfg(self.cfg)
                    self._pvp_lobby_bgm_applied = None
                    if getattr(self, 'mode', 'Story') == 'PvP' and p and self.ready and (
                            pad.cur_banc == self.PVP_LOBBY_BANC or self._pvp_jukebox_in_arena(True)):
                        self._pvp_sync_lobby_bgm(now=now, force=True)
                    if hasattr(self, '_jukebox_refresh'):
                        self._jukebox_refresh()
                    out.append(f'pvp-bgm: satt til sang={tr}, volum={vol:.2f}')
            elif cmd == '/match':
                sub = line.split()[1:] if len(line.split()) > 1 else []
                act = sub[0].lower() if sub else 'status'
                if act in ('ctf', 'dm', 'deathmatch'):
                    gm = 'deathmatch' if act in ('dm', 'deathmatch') else 'ctf'
                    self._server_cmd('mode', game_mode=gm); out.append(f'server: spilltype -> {gm}')
                elif act == 'ready':
                    self._server_cmd('ready', ready=True); out.append('server: klar (ready=True)')
                elif act == 'start':
                    self._pvp_manual_lobby_tok = None
                    self._server_cmd('start'); out.append('server: start forsøkt')
                elif act == 'leave':   # v0.94.320: forlat lobbyen (samme som Leave-knappen)
                    self._server_cmd('leave'); out.append('server: leave')
                elif act == 'stop':
                    self._server_cmd('stop'); out.append('server: stop forsøkt')
                elif act == 'create':
                    arg_sz = sub[1].lower() if len(sub) > 1 else '2v2'
                    sz = {'1v1': 2, '2': 2, '2v2': 4, '4': 4, '5v5': 10, '10': 10,
                          '10v10': 20, '20': 20, '25v25': 50, '50': 50}.get(arg_sz, 4)
                    gm = ('deathmatch' if (len(sub) > 2 and sub[2] in ('dm', 'deathmatch'))
                          else 'ctf' if (len(sub) > 2 and sub[2] == 'ctf') else self._game_mode)
                    # v0.94.316/320: brett – /match create 1v1 dm sword | 1v1 ctf zora | gohma (standard)
                    ar = next((t.lower() for t in sub[2:] if t.lower() in self.ARENAS), 'gohma')
                    if gm == 'ctf' and not self.ARENAS[ar].get('ctf'):
                        out.append('Capture the flag finnes bare i: ' + ', '.join(k for k, v in self.ARENAS.items() if v.get('ctf')))
                    else:
                        self._server_cmd('create', size=sz, game_mode=gm, arena=ar); out.append(f'server: create {sz} {gm} {ar}')
                elif act == 'join' and len(sub) > 1 and sub[1].isdigit():
                    self._server_cmd('join', lobby=int(sub[1])); out.append(f'server: join #{sub[1]}')
                else:
                    st = getattr(self, '_server_state', None) or {}
                    lb = st.get('lobby') or {}
                    out.append(f"server: lobby=#{lb.get('id')} mode={lb.get('game_mode')} arena={lb.get('arena')} host={lb.get('host')} started={lb.get('started')} score={st.get('score')} runde={st.get('round')}")
            elif cmd == '/bot':
                out.append(self._bot_cmd(line.split()[1:]))
            elif cmd == '/status':
                me = pad.my_apos(p) if (p and self.ready) else None
                f = self.friend or {}
                fp = f.get('pos')
                out.append(f"sone {pad.cur_banc} | min pos {[round(v, 1) for v in me] if me else None} | liv {getattr(self, 'last_hearts', None)}")
                out.append(f"venn {f.get('name')} sone {pad.friend_banc} pos {[round(v, 1) for v in fp] if fp else None} avstand {round(math.dist(me, fp), 1) if (me and fp) else None} m | fersk {bool(self.friend and now - self.friend_t < 2)} | ping {getattr(self, 'ping_ms', None)}")
                out.append(f"vert: {'meg' if self._time_host() else 'venn'} ({getattr(self, 'host_mode', 'auto')}) | Link 2 {'finnes' if pad.copy is not None else 'mangler'} | bosskamp {self._in_boss_fight()}")
                out.append(f"fiender: mine {len(getattr(self, '_my_enem', None) or [])} venn {len((f.get('enem') or []))} par {len(getattr(self, '_en_map', {}))} følger {sum(1 for v in getattr(self, '_en_follow', {}).values() if v)}")
            elif cmd == '/enemies':
                fol = getattr(self, '_en_follow', {}); m = getattr(self, '_en_map', {})
                mine = {v[0]: hid for hid, v in m.items()}
                for ent in (getattr(self, '_my_enem', None) or [])[:15]:
                    a, nm, pos, _r, d = ent[:5]
                    hp, mx, an = (ent[5], ent[6], ent[7]) if len(ent) >= 8 else (None, None, None)
                    hid = mine.get(a)
                    out.append(f"{nm[6:]} {d} m liv {hp}/{mx} anim {an} {'FØLGER venn' if (hid is not None and fol.get(hid)) else 'styrer selv'}")
                if not out:
                    out.append('ingen fiender i lista')
            elif cmd == '/boss':
                for a, nm in list(getattr(pad, '_bosses', {}).items())[:8]:
                    try:
                        q = p.f32(a + 0x31C, 3)
                    except OSError:
                        continue
                    hp, mx = self._actor_hp(p, a)
                    out.append(f"{nm} pos {[round(v, 1) for v in q]} liv {hp}/{mx}")
                out.append(f"bosskamp {self._in_boss_fight()}")
            elif cmd == '/flags':
                out.append(f"sendt {len(self.__dict__.get('flags_out', set()))} | mottatt {len(self.__dict__.get('_fl_got', set()))} | siste mottatte {sorted(self.__dict__.get('_fl_got', set()))[-10:]}")
            elif cmd == '/items':
                out.append(f"knapper {getattr(self, '_my_eq', None)} | framme {getattr(self, '_my_drawn', None)} | aktiv ting {getattr(self, '_my_item', None)}")
        except Exception as e:  # noqa: BLE001
            out.append(f'feil {e!r}')
        for o in out:
            self._append_chat_sys(f'ℹ️ {o}')

    # v0.94.60: Ingen NPC. Boten er den separate Player_Zelda_Bot-instansen (Link 2-plassen)
    # og styres med spillets egen kontroller/fysikk. Den kan ikke dele instans med en ekte venn.
    BOT_ACTOR = 'Player_Zelda_Bot'

    def _bot_input(self, buttons=0, sx=0.0, sy=0.0):
        p, pad = self.p, self.pad
        if not (p and pad.hR is not None):
            return False
        try:
            h = p.base + pad.hR
            p.write(h + 0xA08, struct.pack('<Q', int(buttons)))
            p.write(h + 0xB14, bytes(4))
            p.write(h + 0xB20, struct.pack('<4f', float(sx), float(sy), 0.0, 0.0))
            return True
        except OSError:
            return False

    # v0.94.304: testverktøy – styr EGEN Link via kontroller 2 (inp_v5: R+0xA00, gjelder x19 == [R+0x2B0]).
    # Navn -> bits i den falske kontrolleren (fra RE-notater: B/sverd 0x10, hopp 0x08, slag 0x20); ellers hex.
    DRIVE_BTN = {'sword': 0x10, 'b': 0x10, 'jump': 0x08, 'slash': 0x20, 'none': 0}

    def _drive_set(self, on):
        p, pad = self.p, self.pad
        if not (p and pad.hR is not None and pad.player):
            return False
        if on:   # inp_v5 krever magi 0xB4E i R+0x280 også for kontroller 2 (modden setter den bare når Link 2-kopien finnes)
            p.write(p.base + pad.hR + 0x280, struct.pack('<I', pad.MAGIC))
        p.write(p.base + pad.hR + 0x2B0, struct.pack('<Q', pad.player if on else 0))
        if not on:
            self._bot_input()
        return True

    def _drive_cmd(self, a):
        """/drive off | /stick sx sy sek [knapp] | /btn knapp [sek] | /walkto x z [maks_sek]   (stikke -1..1, y=fram)"""
        p, pad = self.p, self.pad
        out = []
        try:
            if not (p and self.ready and pad.hR is not None and pad.player):
                out.append('drive: spillet er ikke klart'); return
            if getattr(self, '_bot_owner', False):
                out.append('drive: test-boten bruker kontroller 2'); return
            cmd = a[0]
            def btn_of(s_):
                return self.DRIVE_BTN.get(s_, None) if s_ in self.DRIVE_BTN else int(s_, 16)
            if cmd == '/drive':
                self._drive_set(False); out.append('drive: av (vanlig kontroller)'); return
            self._drive_busy = True
            self._drive_set(True)
            t0 = time.time(); start = pad.my_apos(p)
            if cmd == '/stick':
                sx, sy, secs = float(a[1]), float(a[2]), float(a[3]) if len(a) > 3 else 0.5
                b_ = btn_of(a[4]) if len(a) > 4 else 0
                while time.time() - t0 < secs:
                    self._bot_input(b_, sx, sy); time.sleep(1 / 60)
            elif cmd == '/btn':
                b_ = btn_of(a[1]); secs = float(a[2]) if len(a) > 2 else 0.15
                while time.time() - t0 < secs:
                    self._bot_input(b_); time.sleep(1 / 60)
                self._bot_input(); time.sleep(0.6)   # la animasjonen starte før kontroller 2 slippes
            elif cmd == '/walkto':
                tx, tz = float(a[1]), float(a[2]); lim = float(a[3]) if len(a) > 3 else 15.0
                stuck_t, last = time.time(), None
                while time.time() - t0 < lim:
                    me = pad.my_apos(p)
                    if not me:
                        break
                    dx, dz = tx - me[0], tz - me[2]; dist = math.hypot(dx, dz)
                    if dist < 0.4:
                        break
                    if last and math.dist(me, last) > 0.05:
                        stuck_t = time.time()
                    last = me
                    if time.time() - stuck_t > 1.5:   # står fast: hopp/rull
                        self._bot_input(0x08); time.sleep(0.1); stuck_t = time.time()
                    cam = pad.my_cam_angle(p, getattr(self, 'cam_off', None)) or 0.0
                    ang = math.atan2(-dx, dz) - cam
                    st_ = min(1.0, max(0.3, dist / 1.5))
                    self._bot_input(0, -st_ * math.sin(ang), st_ * math.cos(ang)); time.sleep(1 / 60)
            self._bot_input(); time.sleep(0.05)
            self._drive_set(False)
            end = pad.my_apos(p)
            moved = math.dist(start, end) if start and end else -1
            out.append(f"drive: {' '.join(a)} ferdig på {time.time() - t0:.1f} s, flyttet {moved:.2f} m, nå "
                       f"{[round(v, 1) for v in end] if end else None}, anim {self._drive_anim()}")
        except Exception as e:  # noqa: BLE001
            out.append(f'drive: feil {e!r}')
            try:
                self._drive_set(False)
            except Exception:  # noqa: BLE001
                pass
        finally:
            self._drive_busy = False
            for m in out:
                log(m); self.ui(self._append_chat_sys, m)

    def _drive_anim(self):
        try:
            return self.pad.read_anim(self.p, self.pad.p_act)[0]
        except Exception:  # noqa: BLE001
            return None

    def _bot_stop(self):
        self._bot_input()
        self.pad.bot_control = False
        if self.p and self.pad.hR is not None:
            try:
                self.p.write(self.p.base + self.pad.hR + 0x2B0, bytes(8))
            except OSError:
                pass
        self._bot_owner = False; self._bot_act = None; self._bot_route = None
        self._bot_attack_until = 0; self._my_bot = None
        # Vanlig venn-spawn skal aldri arve botens Zelda-aktor etter at boten stoppes.
        self.pad.link2_actor = self.cfg.get('link2_actor') or 'Player_Child'

    def _bot_cmd(self, a):
        p, pad = self.p, self.pad
        if not (p and self.ready and pad.hR is not None):
            return 'bot: spillet er ikke klart'
        sub = (a[0].lower() if a else 'status')
        if sub in ('stop', 'del'):
            self.cfg.pop('bot_route', None); save_cfg(self.cfg)
            self._bot_stop()
            return 'spillerbot: stoppet'
        if self.mode != 'PvP':
            return 'bot: spillerboten kan bare brukes i PvP'
        if self.friend and time.time() - self.friend_t < 2:
            self._bot_stop()
            return 'spillerbot: kan ikke brukes mens en ekte venn bruker Link 2'
        if sub == 'spawn':
            if getattr(self, '_bot_owner', False) and pad.c_act is not None:
                return f'spillerbot: finnes allerede @0x{pad.c_act:X}'
            # Uten fersk venn er en eksisterende Link 2 den frakoblede spillerklonen.
            # Ikke slett den: Player-aktorer kan etterlate en ubrukelig «zombie».
            pad.link2_actor = self.BOT_ACTOR
            pad._spawn_failures = 0; pad._l2_tries = 0
            if pad.c_act is None:
                log(f'bot: lager én ekstra spillerinstans av typen {self.BOT_ACTOR}')
                pad._spawn_link2(p)
            # Player-kloner kan registreres sent via ActorMgr-arbeidertråden.
            for _ in range(100):
                if pad.c_act is not None:
                    break
                time.sleep(0.2)
            if pad.c_act is None or pad.copy is None:
                return 'spillerbot: spillerinstansen ble ikke laget'
            self._bot_act = pad.c_act; self._bot_owner = True
            self._bot_target = list(p.f32(pad.c_act + 0x31C, 3))
            pad.bot_control = True
            p.write(p.base + pad.hR + 0x2B0, struct.pack('<Q', pad.copy))
            pad._set_visible(p, True)
            self._bot_input()
            log(f'bot: Player_Zelda_Bot @0x{pad.c_act:X} styres av kontroller 2')
            return f'spillerbot: klar @0x{pad.c_act:X}'
        bot = pad.c_act if getattr(self, '_bot_owner', False) else None
        if bot is None:
            return 'spillerbot: ingen bot (bruk /bot spawn)'
        if sub in ('anim', 'attack'):
            self._bot_attack_until = time.time() + 0.22
            return 'spillerbot: sverdslag via spillerkontrolleren'
        if sub == 'goto':
            self._bot_target = [float(a[1]), float(a[2]), float(a[3])]
            return f'spillerbot: går til {self._bot_target}'
        if sub in ('patrol', 'circle'):
            pos = list(p.f32(bot + 0x31C, 3))
            n = float(a[1]) if len(a) > 1 else (4.0 if sub == 'patrol' else 2.0)
            self._bot_route = (sub, pos, n, time.time())
            return f'spillerbot: {sub} {n} m'
        if sub == 'bases':
            a = ['path'] + [f"{v[0]},{v[2]}" for v in self.PVP_BASES.values()]
            sub = 'path'
        if sub == 'path':
            y = p.f32(bot + 0x31C, 3)[1]
            pts = [[float(v.split(',')[0]), y, float(v.split(',')[1])] for v in a[1:] if ',' in v]
            if len(pts) < 2:
                return 'spillerbot: path trenger minst 2 punkter x,z'
            self._bot_route = ('path', pts, 0, time.time())
            return f'spillerbot: sti med {len(pts)} punkter'
        if sub == 'come':
            me = pad.my_apos(p)
            if me:
                self._bot_target = [me[0] + 1.0, me[1], me[2]]
            return 'spillerbot: kommer'
        try:
            pos = p.f32(bot + 0x31C, 3); an = pad.read_anim(p, bot)
        except Exception:  # noqa: BLE001
            pos, an = None, None
        return f'spillerbot: @0x{bot:X} pos {[round(v, 2) for v in pos] if pos else None} anim {an}'

    def _bot_tick(self, now):
        """20 Hz AI-input til en faktisk spilleraktør; aldri transform-/animasjonsjuk."""
        if not getattr(self, '_bot_owner', False):
            return
        if now - getattr(self, '_bot_t', 0) < 0.05 or not (self.p and self.ready):
            return
        self._bot_t = now
        p, pad = self.p, self.pad
        if self.mode != 'PvP' or (self.friend and now - self.friend_t < 2):
            self._bot_stop()
            return
        bot = pad.c_act
        if bot is None or pad.copy is None:
            self._bot_stop()
            return
        try:
            h = p.base + pad.hR
            if struct.unpack('<Q', p.read(h + 0x2B0, 8))[0] != pad.copy:
                p.write(h + 0x2B0, struct.pack('<Q', pad.copy))
            pos = p.f32(bot + 0x31C, 3)
        except OSError:
            return
        rt = getattr(self, '_bot_route', None)
        if rt:
            kind, c, n, t0 = rt
            if kind == 'path':
                if math.hypot(c[n][0] - pos[0], c[n][2] - pos[2]) < 0.5:
                    n = (n + 1) % len(c); self._bot_route = (kind, c, n, t0)
                self._bot_target = list(c[n])
            elif kind == 'patrol':
                ph = ((now - t0) * 1.2 / n) % 2.0
                f = ph if ph < 1.0 else 2.0 - ph
                self._bot_target = [c[0] + n * f, c[1], c[2]]
            else:
                ang = (now - t0) * 1.2 / max(n, 0.5)
                self._bot_target = [c[0] + n * math.cos(ang), c[1], c[2] + n * math.sin(ang)]
        if now < getattr(self, '_bot_attack_until', 0):
            self._bot_input(0x10)
            return
        tgt = getattr(self, '_bot_target', None) or list(pos)
        dx, dz = tgt[0] - pos[0], tgt[2] - pos[2]
        distance = math.hypot(dx, dz)
        if distance < 0.35:
            self._bot_input()
            return
        cam = pad.my_cam_angle(p, getattr(self, 'cam_off', None)) or 0.0
        angle = math.atan2(-dx, dz) - cam
        strength = min(1.0, max(0.25, distance / 1.5))
        self._bot_input(0, -strength * math.sin(angle), strength * math.cos(angle))

    def _cmd_allowed(self):
        """v0.94.298: chat-kommandoer bare for hosten i Story. I PvP kan ingen bruke dem (juks).
        v0.94.300: Story-hosten = den som står som «Host» i Nettverk-panelet (_time_host, kan byttes ved klikk) –
        ikke serverens Public-lobby-host (den var en annen spiller enn den vinduet viste)."""
        if getattr(self, 'mode', 'Story') != 'Story':
            return False
        return self._time_host()

    def _cmd_btn_tick(self):
        try:
            ok = self._cmd_allowed()
            if ok and not self.cmd_btn.winfo_ismapped():
                self.cmd_btn.place(relx=1.0, rely=0.5, anchor="e")
            elif not ok and self.cmd_btn.winfo_ismapped():
                self.cmd_btn.place_forget()
        except Exception:  # noqa: BLE001
            pass
        self.root.after(1500, self._cmd_btn_tick)

    # v0.94.301: det Story-hosten kan skrive selv; alt annet (/goto, /spawn, /skip, /paint …) er juks/test og
    # virker bare via remote_cmd.txt ved exe-en
    HOST_CMDS = ('/tp', '/warp', '/here', '/samle', '/teleport', '/resetboss', '/opendoor', '/door', '/near',
                 '/target', '/aihold', '/status', '/enemies', '/boss', '/flags', '/items', '/mode', '/help',
                 '/inv', '/ping')

    def _show_commands(self):
        for line in ("Commands (type in the chat, Enter sends):",
                     "  /tp – teleport your friend to you (blocked in boss fights)",
                     "  /resetboss – reset the boss room on both PCs (unlocks the boss door)",
                     "  /opendoor – remove doors and spider webs within 6 m of you (this PC only)",
                     "  /near – write nearby enemies and objects to the log (for bug reports)",
                     "  /target near|me|friend – who enemies attack (default: nearest Link)",
                     "  /aihold on|off – pause the AI of enemy copies your friend controls",
                     "  /status /enemies /boss /flags /items – show game info in the chat"):
            self._append_chat_sys(line)

    def _do_resetboss(self):
        n = 0
        if self.p and self.ready:
            for i in PadLink.BOSS_FLAGS:
                n += bool(self.pad.clear_bool(self.p, i))
            for st in ('flags_out', '_fl_got'):
                for i in PadLink.BOSS_FLAGS:
                    self.__dict__.get(st, set()).discard(i)
        log(f'boss: nullstilte {n} boss-flagg {PadLink.BOSS_FLAGS}')
        self._append_chat_sys(f'🔄 Boss reset: cleared {n} boss flags – leave the area and come back')

    def _in_boss_fight(self):
        """Sant hvis min Link er nær en boss som har våknet (vært nede fra taket)."""
        try:
            me = self.pad.my_apos(self.p) if (self.p and self.ready) else None
            if not me:
                return False
            for a, r2 in getattr(self, '_boss_awake2', {}).items():
                if r2[1] - r2[0] > 5 and math.dist(r2[2], me) < 35:
                    return True
        except Exception:  # noqa: BLE001
            pass
        return False

    def _boss_near(self, r):
        """Står min Link innen r m fra en kjent boss (ikke egg/larver)?"""
        try:
            me = self.pad.my_apos(self.p)
            for a, nm in list(getattr(self.pad, '_bosses', {}).items()):
                lim = r if 'Boss' in nm else min(r, 10.0)   # v0.94.220: egg/larver i naborom skal ikke slå av mål-patchen
                if me and math.dist(self.p.f32(a + 0x31C, 3), me) < lim:
                    return True
        except Exception:  # noqa: BLE001
            pass
        return False

    def _boss_release(self, p):
        self._boss_pins = {}
        self._boss_skel_pin = None
        self._boss_aggro_name = None
        if getattr(self, '_boss_comps', None):
            self._boss_comps = []
            self.pad.set_ai_hold(p, list(getattr(self, '_held_prev', None) or []))
            log('boss: AI-pause sluppet')

    def _boss_sync(self, p, mine, now):
        """Boss og adds (alt med «Boss» i navnet): laveste liv vinner hos begge; verten styrer plasseringen."""
        pad = self.pad
        fresh = bool(self.friend and now - self.friend_t < 2)
        theirs = (self.friend or {}).get('boss') if fresh else None
        if not theirs or not mine or pad.friend_banc != pad.cur_banc or now - getattr(pad, '_banc_since', 0) < 3:
            self._boss_release(p)
            return
        me = pad.my_apos(p)
        if not me or not any(math.dist(q, me) < 35 for _a, _n, q, _r, _h, _m in mine):
            self._boss_release(p)
            return   # min Link er ikke i bossrommet – ikke rør bossen (ellers tror spillet at kampen er i gang og sperrer utgangene)
        fp = (self.friend or {}).get('pos')
        if not fp or not any(math.dist(e[1], fp) < 35 for e in theirs if len(e) >= 2):
            self._boss_release(p)
            return   # vennen er ikke i bossrommet – da er vennens boss i hvile og skal ikke styre min
        # v0.94.238: tilfeldig boss-target-bytte hvert 30. sekund – KUN når bossen står på gulvet (y < 49.0), aldri i taket!
        is_th = self._time_host()
        fname = (self.friend or {}).get('name') or ''
        boss_on_floor = any(
            ('Boss' in n2 and 'Egg' not in n2 and 'Larva' not in n2 and 'Child' not in n2 and q[1] < 49.0)
            for _a, n2, q, _r, _h, _m in mine
        )
        if is_th:
            bt = getattr(self, '_my_boss_target', None)
            cands = [c for c in (self.name, fname) if c]
            need_init = (not bt or not isinstance(bt, list) or len(bt) < 2 or bt[0] not in cands)
            due_swap = (not need_init and now - bt[1] >= 30.0 and boss_on_floor)
            if need_init or due_swap:
                prev_t = bt[0] if (isinstance(bt, list) and bt) else None
                pool = [c for c in cands if c != prev_t] or cands
                pick = random.choice(pool) if pool else self.name
                self._my_boss_target = [pick, round(now, 1)]
                log(f'boss: aggro-target byttet til {pick} (neste bytte om 30 s på gulv)')
            aggro_name = self._my_boss_target[0]
        else:
            fbt = (self.friend or {}).get('bt')
            aggro_name = fbt[0] if (isinstance(fbt, list) and len(fbt) >= 1 and fbt[0]) else (fname or self.name)
        self._boss_aggro_name = aggro_name
        host = (aggro_name == self.name)
        used = set(); hold_now = []; pins = {}; skel_pin = None
        has_bb = bool(isinstance((self.friend or {}).get('bb'), list) and len((self.friend or {}).get('bb')) == 2)
        for ent in theirs:
            if len(ent) < 5:
                continue
            nm, pos, rot, hp, mx = ent[:5]
            if math.dist(pos, me) >= 35.0:
                continue   # v0.94.224: dobbeltsperre mot egg/larver i andre rom
            t_an = ent[5] if len(ent) >= 6 else None
            t_fr = ent[6] if len(ent) >= 7 else None
            c = sorted((math.dist(q, pos), a) for a, n2, q, _r, _h, _m in mine if n2 == nm and a not in used)
            is_add = 'Egg' in nm or 'Larva' in nm or 'Child' in nm
            if is_add and not host and (not c or c[0][0] > 8) and (hp or 0) > 0 and getattr(self, 'boss_follow_on', True):
                # v0.60: vertens add finnes ikke hos meg (min Gohma har AI-pause og legger ikke egg) -> lag den
                cr = self.__dict__.setdefault('_bs_created', [])
                cr[:] = [x for x in cr if now - x[2] < 6]
                if now - getattr(self, '_bs_cr_t', 0) > 0.5 and not any(x[0] == nm and math.dist(x[1], pos) < 3 for x in cr):
                    self._bs_cr_t = now; cr.append((nm, tuple(pos), now))
                    r = pad.create_actor(p, nm, pos)
                    log(f'boss: laget {nm} hos meg ved {[round(v, 1) for v in pos]} -> {r}')
                continue
            if not c:
                continue
            d0, a = c[0]
            if is_add and d0 > 15:
                continue
            used.add(a)
            try:
                myy = p.f32(a + 0x31C, 3)[1]
            except OSError:
                continue
            awake = self.__dict__.setdefault('_boss_awake', {})
            r2 = awake.setdefault(a, [myy, myy]); r2[0] = min(r2[0], myy); r2[1] = max(r2[1], myy)
            if 'Egg' in nm or 'Larva' in nm or r2[1] - r2[0] > 5:   # bossen må ha våknet hos meg (vært nede) før livet deles
                self._share_hp(p, a, nm, hp, mx)
            adds = 'Egg' in nm or 'Larva' in nm or 'Child' in nm
            try:
                qy = p.f32(a + 0x31C, 3)[1]
            except OSError:
                continue
            rng = self.__dict__.setdefault('_boss_yr', {}).setdefault(nm, [qy, qy])
            rng[0] = min(rng[0], qy, pos[1]); rng[1] = max(rng[1], qy, pos[1])
            # gulv kjent først når vi har sett henne både oppe og nede (> 5 m forskjell); i taket/klatring = ikke rør (hang spillet)
            on_floor = rng[1] - rng[0] > 5 and pos[1] < rng[0] + 2.5 and qy < rng[0] + 2.5
            follow = (not host and getattr(self, 'boss_follow_on', True) and (hp or 0) > 0
                      and (self._actor_hp(p, a)[0] or 0) > 0)
            my_an = None
            if follow:
                try:
                    my_an = pad.read_anim(p, a)[0]
                except Exception:  # noqa: BLE001
                    my_an = None
            in_cut = isinstance(my_an, str) and my_an.startswith('C0')
            host_cut = isinstance(t_an, str) and t_an.startswith('C0')
            # v0.94.232: hvis vertens Gohma står rett vei på gulvet (y<49, rot[4]>0.85), men følgeren henger fast skjev/opp-ned
            # i gammel klatre-modus (my_rot[4]<0.75), slipp AI-pause + move_actor kort så spillet lander henne rett vei
            need_upright = False
            if follow and not in_cut and not is_add and pos[1] < 49.0 and len(rot) == 9 and rot[4] > 0.85:
                try:
                    my_up_y = p.f32(a + 0x328, 9)[4]
                    if my_up_y < 0.75:
                        need_upright = True
                        if now - getattr(self, '_bs_up_log', 0) > 2:
                            self._bs_up_log = now; log(f'boss: slipper AI-pause kort for å rette opp {nm} på gulvet (my_up_y={my_up_y:.2f})')
                except OSError:
                    pass
            if follow and not in_cut and not need_upright:   # v0.94.232: ikke avbryt lokal kuttscene (C0*) eller gulv-oppretting
                c_ = pad.bsa_comp(p, a)
                if c_:
                    hold_now.append(c_)
            # v0.94.232: flytt FØRST + 60 Hz glattet move_actor (x8+0x1D0) – ALDRI skriv direkte til act+0x31C
            if not host and not in_cut and not need_upright and (on_floor or follow or adds) and all(math.isfinite(v) for v in pos):
                x8 = self.__dict__.setdefault('_bs_x8', {}).get(a) or pad.actor_x8(p, a)
                if x8:
                    self._bs_x8[a] = x8
                    rot9 = tuple(rot) if len(rot) == 9 else None
                    if follow:
                        pins[a] = (x8, tuple(pos), rot9, now)
                    if d0 > (0.05 if follow else 1.0):
                        try:
                            q = p.f32(a + 0x31C, 3)
                        except OSError:
                            continue
                        k = 1.0 if follow else (1.0 if d0 > 8 else 0.4)
                        pad.move_actor(p, a, x8, [c0 + (t - c0) * k for c0, t in zip(q, pos)], rot9)
                        if now - getattr(self, '_bs_log', 0) > 3:
                            self._bs_log = now; log(f'boss: flyttet {nm} {d0:.1f} m mot vertens plassering (følger={follow})')
            if follow and not in_cut and t_an and not host_cut:
                # v0.94.233: ingen set_anim_frame-napping (ga 1.35-13.5 m WorldMtx-hopp hvert 0.25 s);
                # og når verten er pauset (pos + t_fr uendret > 0.30 s), bytt til Wait så hun står helt stille
                want_an = t_an
                if not is_add:
                    pst = self.__dict__.setdefault('_bs_pause_st', {})
                    prev_st = pst.get(a)
                    pos_t = (round(pos[0], 2), round(pos[1], 2), round(pos[2], 2))
                    fr_t = round(t_fr, 2) if isinstance(t_fr, (int, float)) else None
                    if prev_st and prev_st[0] == pos_t and prev_st[1] == fr_t:
                        if now - prev_st[2] > 6.0:
                            # v0.94.239: verten har fryst/stått helt stille > 6 s – slipp AI-pause så den friske spilleren kan spille videre
                            self._boss_release(p)
                            return
                        if now - prev_st[2] > 0.30 and any(k in t_an for k in ('Walk', 'Run', 'Move', 'Turn')):
                            want_an = 'Wait'
                    else:
                        pst[a] = (pos_t, fr_t, now)
                skip_add_an = is_add and any(want_an.startswith(k) for k in ('Wait', 'Turn', 'Sleep', 'Idle'))
                if not skip_add_an and my_an != want_an:
                    try:
                        lt = self.__dict__.setdefault('_bs_an_t', {})
                        if now >= lt.get(a, 0):
                            r_an = pad.play_anim(p, a, want_an)
                            lt[a] = now + ((0.05 if not is_add else 0.20) if r_an else 2.0)
                            if now - getattr(self, '_bs_an_log', 0) > 2:
                                self._bs_an_log = now; log(f'boss: animasjon {nm} {my_an} -> {want_an} -> {r_an}')
                    except Exception as e:  # noqa: BLE001
                        if now - getattr(self, '_bs_an_err', 0) > 10:
                            self._bs_an_err = now; log(f'boss: animasjon feil {e!r}')
        if False and not host:   # v0.62b: AV – sletting ga lage/slette-løkke på klienten -> slett hos meg
            tadds = [(e[0], e[1]) for e in theirs if len(e) >= 5 and ('Egg' in e[0] or 'Larva' in e[0])]
            orph = self.__dict__.setdefault('_bs_orph', {})
            for a, nm, q, _r, _h, _m in mine:
                if 'Egg' not in nm and 'Larva' not in nm:
                    continue
                if any(n2 == nm and math.dist(q, tp) < 4 for n2, tp in tadds):
                    orph.pop(a, None); continue
                t0 = orph.setdefault(a, now)
                if now - t0 > 1.5:
                    orph.pop(a, None); r = pad.delete_actor(p, a)
                    log(f'boss: slettet {nm} hos meg (verten har den ikke) -> {r}')
        self._boss_pins = pins
        self._boss_skel_pin = skel_pin
        # v0.94.227: rydd foreldreløse adds (rester fra forrige forsøk) med HP=0 i stedet for delete_actor
        if not host:
            tadds = [(e[0], e[1]) for e in theirs if len(e) >= 5 and ('Egg' in e[0] or 'Larva' in e[0])]
            orph = self.__dict__.setdefault('_bs_orph', {})
            orph_done = self.__dict__.setdefault('_bs_orph_done', set())
            for a, nm, q, _r, h_, m_ in mine:
                if ('Egg' not in nm and 'Larva' not in nm) or (h_ or 0) <= 0 or a in orph_done:
                    orph.pop(a, None); continue
                if any(n2 == nm and math.dist(q, tp) < 8.0 for n2, tp in tadds):
                    orph.pop(a, None); continue
                t0 = orph.setdefault(a, now)
                if now - t0 > 2.0:
                    orph.pop(a, None); orph_done.add(a)
                    self._share_hp(p, a, nm, 0, m_)
                    log(f'boss: satte HP=0 på foreldreløs {nm} @0x{a:X}')
        if set(hold_now) != set(getattr(self, '_boss_comps', [])):
            self._boss_comps = list(hold_now)
            ok_ = pad.set_ai_hold(p, hold_now + list(getattr(self, '_held_prev', None) or []))
            log(f'boss: AI-pause for {len(hold_now)} boss(er) -> {ok_}')

    def _pvp_set_hp(self, pvp):
        """v0.93: PvP = 1 hjerte (maks og nå = 4 kvartaler). Livet fra Story lagres og settes tilbake."""
        try:
            p, off = self.p, self.rupees.off
            if p is None or off is None:
                return
            cur, mx = p.u32(off + 0x28), p.u32(off + 0x50)
            if pvp:
                if not self.cfg.get('pvp_saved_hp') and mx > 4:
                    self.cfg['pvp_saved_hp'] = [cur, mx]; save_cfg(self.cfg)
                p.write(p.base + off + 0x50, struct.pack('<I', 12)); p.write(p.base + off + 0x28, struct.pack('<I', 12))
                self._pvp_hp_shadow = 12
                log(f'pvp: liv satt til 3 hjerter (lagret {cur}/{mx})')
            else:
                self._pvp_hp_shadow = None
                sv = self.cfg.pop('pvp_saved_hp', None); save_cfg(self.cfg)
                if sv:
                    p.write(p.base + off + 0x50, struct.pack('<I', sv[1])); p.write(p.base + off + 0x28, struct.pack('<I', max(4, sv[0])))
                    log(f'pvp: liv tilbake til {sv}')
        except Exception as e:  # noqa: BLE001
            log(f'pvp: liv-feil {e!r}')

    PVP_INV_RELS = (("rupees", 0x000, 0x230), ("sticks", 0x938, 0x208), ("nuts", 0x8E8, 0x1B8), ("seeds", 0x910, 0x1E0))

    def _pvp_set_inv_mode(self, pvp):
        """Skill PvP-inventar helt fra Story: ta øyeblikksbilde før PvP, og legg tilbake ved retur til Story."""
        try:
            p = getattr(self, 'p', None)
            off = self.rupees.off if getattr(self, 'rupees', None) else None
            if p is None or off is None:
                return
            if pvp:
                if not self.cfg.get('pvp_saved_inv'):
                    snap = {}
                    for key, rel, _cap_rel in self.PVP_INV_RELS:
                        snap[key] = p.u32(off + rel)
                    self.cfg['pvp_saved_inv'] = snap; save_cfg(self.cfg)
                    log(f'pvp-db: lagret Story-inventar {snap}')
                self._pvp_profile_applied = False
                self._pvp_inv_last = None
                prof = getattr(self, '_pvp_profile', None)
                if isinstance(prof, dict):
                    self._pvp_apply_profile(prof, force=True)
            else:
                sv = self.cfg.pop('pvp_saved_inv', None); save_cfg(self.cfg)
                self._pvp_profile_applied = False
                self._pvp_inv_last = None
                if isinstance(sv, dict):
                    for sync in (getattr(self, 'syncs', None) or {}).values():
                        sync.mute(3.0)   # v0.94.268: tilbakeskrivingen er ikke et funn/forbruk – ellers sendes den som delta til vennen
                    for key, rel, _cap_rel in self.PVP_INV_RELS:
                        if key in sv and isinstance(sv[key], int):
                            val = max(0, sv[key])
                            p.write(p.base + off + rel, struct.pack('<I', val))
                            p.write(p.base + off + rel + 4, struct.pack('<I', val))
                    self._pvp_restore_pouch()
                    for sync in (getattr(self, 'syncs', None) or {}).values():
                        sync.expected = p.u32(sync.off)
                    log(f'pvp-db: Story-inventar lagt tilbake {sv}')
                if self.cfg.get('server_inventory', True):   # v0.94.278: serveren er fasit for Story – hent derfra, ikke fra lokalt øyeblikksbilde
                    self._sinv_loaded = False; self._inv_load_pending = time.time(); self._server_cmd('inv_get', key=self._account_key())
                    log('inv-db: tilbake i Story – henter inventaret fra serveren')
        except Exception as e:  # noqa: BLE001
            log(f'pvp-db: modusbytte-feil {e!r}')

    def _pvp_apply_profile(self, profile, force=False):
        """Skriv serverens lagrede PvP-rubies og inventar til spillminnet (kun i PvP-modus)."""
        if getattr(self, 'mode', 'Story') != 'PvP':
            return False
        p = getattr(self, 'p', None)
        off = self.rupees.off if getattr(self, 'rupees', None) else None
        if not (p and getattr(self, 'ready', False) and off is not None and isinstance(profile, dict)):
            return False
        if not self.cfg.get('pvp_saved_inv'):
            snap = {key: p.u32(off + rel) for key, rel, _cap_rel in self.PVP_INV_RELS}
            self.cfg['pvp_saved_inv'] = snap; save_cfg(self.cfg)
            log(f'pvp-db: lagret Story-inventar før profilskriving {snap}')
        inv = profile.get('inventory') or {}
        rubies = max(0, int(profile.get('rubies', 0) or 0))
        if force or not getattr(self, '_pvp_profile_applied', False):
            rcap = p.u32(off + 0x230)
            rcap = rcap if 0 < rcap <= 9999 else 200
            rv = min(rubies, rcap)
            p.write(p.base + off, struct.pack('<I', rv))
            p.write(p.base + off + 4, struct.pack('<I', rv))
            last = {}
            for key, rel, cap_rel in self.PVP_INV_RELS[1:]:
                if key in inv:
                    cap = p.u32(off + cap_rel)
                    cap = cap if 0 < cap <= 99 else 99
                    val = max(0, min(cap, int(inv[key])))
                    p.write(p.base + off + rel, struct.pack('<I', val))
                    p.write(p.base + off + rel + 4, struct.pack('<I', val))
                    last[key] = val
            self._pvp_write_pouch(inv)
            self._pvp_inv_last = last
            self._pvp_profile_applied = True
            log(f'pvp-db: lastet PvP-profil rubies={rubies}, inv={last}')
            if getattr(self, '_counter_open', False):
                self._counter_refresh()
        return True

    def _pvp_write_sv(self, rel, val):
        raw = struct.pack('<I', int(val))
        off = self.rupees.off
        self.p.write(self.p.base + off + rel, raw)
        self.p.write(self.p.base + off + rel + 4, raw)

    def _pvp_read_pouch(self):
        """Øyeblikksbilde av bomber, bombveske og flaske før PvP skriver over dem."""
        p, off = self.p, self.rupees.off
        snap = {key: (p.u32(off + rel), p.u32(off + rel + 4)) for key, rel in self.PVP_POUCH}
        snap['bottle_item'] = None
        pad = getattr(self, 'pad', None)
        h = getattr(pad, 'h_enum', None) if pad is not None else None
        if h is not None:
            base = h + 60 * 0x38
            snap['bottle_item'] = (p.u32(base + 0x1C), p.u32(base + 0x20))
        return snap

    def _pvp_write_pouch(self, inv):
        """Skriv bomber og drikk fra serverprofilen. Pinner, nøtter og frø skrives for seg."""
        if not isinstance(inv, dict) or getattr(self, 'p', None) is None or getattr(self, 'rupees', None) is None:
            return
        if 'pvp_saved_pouch' not in self.cfg:
            self.cfg['pvp_saved_pouch'] = self._pvp_read_pouch()
            save_cfg(self.cfg)
        shop = getattr(self, '_pvp_shop', None) or {}
        bombs = inv.get('bombs')
        if isinstance(bombs, int):
            cap = (shop.get('bombs') or {}).get('cap', 20)
            val = max(0, min(int(cap) if isinstance(cap, int) else 20, bombs))
            self._pvp_write_sv(0x708, val)
            if val > 0:
                self._pvp_write_sv(0x780, 1)
        potion = inv.get('potion')
        if isinstance(potion, int):
            cap = (shop.get('potion') or {}).get('cap', 3)
            val = max(0, min(int(cap) if isinstance(cap, int) else 3, potion))
            self._pvp_write_sv(0x550, val)
            self._pvp_write_bottle(val > 0)

    def _pvp_write_bottle(self, filled):
        pad = getattr(self, 'pad', None)
        if pad is None:
            return
        if getattr(pad, 'h_enum', None) is None and hasattr(pad, 'save_tables'):
            try:
                pad.save_tables(self.p)
            except Exception:  # noqa: BLE001
                return
        h = getattr(pad, 'h_enum', None)
        if h is None:
            return
        if filled:
            pair = (self.RED_POTION, self.RED_POTION)
        else:
            pair = (self.cfg.get('pvp_saved_pouch') or {}).get('bottle_item')
            if not pair:
                return
        base = h + 60 * 0x38
        self.p.write(self.p.base + base + 0x1C, struct.pack('<I', int(pair[0])))
        self.p.write(self.p.base + base + 0x20, struct.pack('<I', int(pair[1])))

    def _pvp_restore_pouch(self):
        snap = self.cfg.pop('pvp_saved_pouch', None)
        save_cfg(self.cfg)
        if not isinstance(snap, dict) or getattr(self, 'p', None) is None or getattr(self, 'rupees', None) is None:
            return
        for key, rel in self.PVP_POUCH:
            pair = snap.get(key)
            if isinstance(pair, (list, tuple)) and len(pair) == 2:
                off = self.rupees.off
                self.p.write(self.p.base + off + rel, struct.pack('<I', int(pair[0])))
                self.p.write(self.p.base + off + rel + 4, struct.pack('<I', int(pair[1])))
        pair = snap.get('bottle_item')
        pad = getattr(self, 'pad', None)
        h = getattr(pad, 'h_enum', None) if pad is not None else None
        if h is not None and isinstance(pair, (list, tuple)) and len(pair) == 2:
            base = h + 60 * 0x38
            self.p.write(self.p.base + base + 0x1C, struct.pack('<I', int(pair[0])))
            self.p.write(self.p.base + base + 0x20, struct.pack('<I', int(pair[1])))

    def _pvp_handle_profile(self, prof, old_prof):
        """Oppdater PvP-profil fra server; kun aktiv i PvP-modus."""
        if getattr(self, 'mode', 'Story') != 'PvP':
            return
        prof_name = getattr(self, '_pvp_profile_name', None)
        if prof_name != self.name:
            self._pvp_profile_name = self.name
            self._pvp_profile_applied = False
        self._pvp_profile = prof
        if not getattr(self, '_pvp_profile_applied', False):
            self._pvp_apply_profile(prof, force=True)
            return
        if isinstance(old_prof, dict):
            old_inv = old_prof.get('inventory') or {}
            new_inv = prof.get('inventory') or {}
            dr = int(prof.get('rubies', 0)) - int(old_prof.get('rubies', 0))
            increased = {k: new_inv[k] for k in new_inv if new_inv[k] > old_inv.get(k, 0)}
            if dr > 0 and not increased:
                self._append_chat_sys(f'💎 +{dr} PvP rubies (totalt {prof.get("rubies", 0)})')
                self._pvp_apply_profile(prof, force=True)
            elif increased:
                self._append_chat_sys(f'🛍️ PvP purchase complete: {increased} (rubies left: {prof.get("rubies", 0)})')
                self._pvp_apply_profile(prof, force=True)
        if getattr(self, '_counter_open', False):
            self._counter_refresh()

    def _pvp_inv_watch(self, now):
        """Send forbruk utenfor arenaen til serverens PvP-database (kun PvP)."""
        if getattr(self, 'mode', 'Story') != 'PvP' or not getattr(self, '_pvp_profile_applied', False):
            return
        if getattr(self, '_pvp_in_arena', False) or now - getattr(self, '_pvp_inv_t', 0) < 1.5:
            return
        self._pvp_inv_t = now
        p = getattr(self, 'p', None)
        off = self.rupees.off if getattr(self, 'rupees', None) else None
        last = getattr(self, '_pvp_inv_last', None)
        if not (p and off is not None and isinstance(last, dict)):
            return
        try:
            decreased = {}
            for key, rel, _cap_rel in self.PVP_INV_RELS[1:]:
                if key in last:
                    cur = p.u32(off + rel)
                    if 0 <= cur < last[key]:
                        decreased[key] = cur
                        last[key] = cur
            if decreased:
                self._server_cmd('inv_consume', items=decreased)
                log(f'pvp-db: lagret forbruk {decreased}')
        except OSError:
            pass

    def _pvp_respawn(self, pc, pm, teleport=True):
        """PvP: livet ville gått til 0 – fullt liv igjen og tilbake til startpunktet (ingen GAME OVER)."""
        p = self.p
        try:
            mh = getattr(self, '_my_hearts_last', None)   # [nå, maks] i kvartaler, samme som GUI-et viser
            mx = 12 if getattr(self, 'mode', 'Story') == 'PvP' else (mh[1] if mh and 4 <= mh[1] <= 80 else 12)
            p.write(p.base + pc, struct.pack("<I", mx))
            self._pvp_hp_shadow = mx
            log(f'pvp: liv satt til {mx} kvartaler ({mx // 4} hjerter)')
        except OSError:
            pass
        if teleport:
            self._pvp_deaths = getattr(self, '_pvp_deaths', 0) + 1
            tm = self._active_pvp_team()
            if self._game_mode == 'deathmatch' and tm in ('Red', 'Blue'):
                self._server_cmd('eliminated', team=tm)
        sp = getattr(self, '_pvp_spawn', None)
        r = self.pad.teleport_player(p, sp) if (sp and teleport) else None
        log(f'pvp: jeg ble slått ut ({self._pvp_deaths}) – fullt liv, tilbake til start {sp} -> {r}')
        self._append_chat_sys(f'💥 You were knocked out! ({self._pvp_deaths})')

    PVP_SWING = ('Attack', 'Slash', 'Cut', 'Swing', 'Spin', 'Thrust', 'Stab', 'Atk', 'Sword')
    PVP_SHOT = ('bowshoot', 'slingshot', 'pachinko')   # v0.94.308: sprettert bruker BowShoot (målt 10:22:41)
    PVP_SHOT_RANGE = 15.0
    PVP_SHOT_COS = 0.97   # ca. 14° fra Links retning

    def _pvp_swing(self, now):
        """Hver PC oppdager bare sine egne sverdtreff og sender dem i en egen PvP-teller.
        Det gjør at også gjestens slag registreres, uten at begge PC-ene rapporterer samme angrep."""
        p, pad = self.p, self.pad
        if getattr(self, '_pvp_social_lobby', False) and pad.cur_banc == self.PVP_LOBBY_BANC:
            return
        lobby = (getattr(self, '_server_state', {}).get('lobby') or {})
        large_match = lobby.get('capacity') in (20, 50) and lobby.get('game_mode') == 'deathmatch'
        if pad.p_act is None:
            return
        try:
            an = pad.read_anim(p, pad.p_act)[0]
        except Exception:  # noqa: BLE001
            an = None
        prev = getattr(self, '_pvp_an', None)
        self._pvp_an = an
        if not an or an == prev:
            return
        if now - getattr(self, '_pvp_an_log', 0) > 0.5:
            self._pvp_an_log = now; log(f'pvp: min animasjon {prev} -> {an}')
        # v0.94.308: sprettert/bue (BowShoot) – før ble bare sverdslag sjekket, så skudd ga aldri treff.
        shot = any(k in an.lower() for k in self.PVP_SHOT)
        if not shot and not any(k.lower() in an.lower() for k in self.PVP_SWING):
            return
        me, rot = pad.my_apos(p), pad.my_arot(p)
        if not me or not rot:
            return
        spin = ('spin' in an.lower() or 'chargeattack' in an.lower())
        if shot and large_match:
            return   # serveren godtar bare swing/spin ennå (server.py record_hit)
        if large_match:
            match = lobby.get('started_at')
            team = self._active_pvp_team()
            if (match is None or not getattr(self, '_pvp_in_arena', False)
                    or pad.cur_banc != 'HyruleField_Child' or team not in ('Red', 'Blue')
                    or now - getattr(self, '_pvp_hit_last', 0) < 0.45):
                return
            enemy = 'Red' if team == 'Blue' else 'Blue'
            fx, fz = rot[2], rot[8]
            for peer in getattr(self, 'pvp_peers', ()):
                if (peer.get('team') != enemy or peer.get('lobby') != lobby.get('id')
                        or peer.get('zone') != pad.cur_banc or not peer.get('name')):
                    continue
                pos = peer.get('pos')
                if (not isinstance(pos, list) or len(pos) != 3
                        or not all(isinstance(v, (int, float)) and abs(v) <= 1e5 for v in pos)):
                    continue
                dx, dz = pos[0] - me[0], pos[2] - me[2]
                d = math.hypot(dx, dz)
                if d > (2.4 if spin else 2.0) or abs(pos[1] - me[1]) > 1.5:
                    continue
                if not spin and d > 0.3 and (fx * dx + fz * dz) < 0.3 * d * (math.hypot(fx, fz) or 1):
                    continue
                self._pvp_hit_seq = getattr(self, '_pvp_hit_seq', 0) + 1
                if self._server_cmd('hit', target=peer['name'], match=match,
                                    attack='spin' if spin else 'swing', seq=self._pvp_hit_seq):
                    self._pvp_hit_last = now
                break
            return
        # v0.94.307: motstanderen er en CoopPuppet (dukkepoolen), ikke den gamle Link 2 (c_act) – før ble ingen slag
        # registrert i 1v1/små kamper fordi c_act alltid var None. Nærmeste motstander-dukke brukes (tegnet posisjon).
        tgt_act, l2 = pad.c_act, None
        if tgt_act is not None:
            try:
                l2 = p.f32(tgt_act + 0x31C, 3)
            except OSError:
                tgt_act = None
        if l2 is None:
            seen_t, pups = getattr(self, '_puppets_seen', (0, {}))
            if now - seen_t > 1.0 or not pups:
                return
            opp = self._z_opponents_pvp(pups)
            best = None
            fx0, fz0 = rot[2], rot[8]
            fn0 = math.hypot(fx0, fz0) or 1
            for nm_, act_ in pups.items():
                if nm_ not in opp:
                    continue
                pos_ = (getattr(self, '_puppets_pos', (0, {}))[1].get(nm_)
                        or self._plate_pos(p, act_, self.__dict__.setdefault('_glyph', {})))   # v0.94.310: nettverksposisjon først
                if pos_ is None:
                    continue
                dd = math.hypot(pos_[0] - me[0], pos_[2] - me[2])
                if shot:   # skudd: den som står nærmest siktelinjen, ikke nærmest meg
                    if dd > self.PVP_SHOT_RANGE or dd < 0.1:
                        continue
                    if ((pos_[0] - me[0]) * fx0 + (pos_[2] - me[2]) * fz0) / (dd * fn0) < self.PVP_SHOT_COS:
                        continue
                if best is None or dd < best[0]:
                    best = (dd, act_, pos_)
            if best is None:
                return
            _, tgt_act, l2 = best
        dx, dz = l2[0] - me[0], l2[2] - me[2]
        d = math.hypot(dx, dz)
        fx, fz = rot[2], rot[8]   # forover = kolonne 2 (målt: 0,93 mot Link 2 som sto foran)
        if shot:
            # Ingen veggsjekk: skuddet treffer hvis motstanderen står innen PVP_SHOT_RANGE og nær siktelinjen
            # (Z-lås snur Link mot målet). Høydeforskjell opp til 4 m (plattformer i arenaen).
            if d > self.PVP_SHOT_RANGE or abs(l2[1] - me[1]) > 4.0 or d < 0.1:
                return
            if (fx * dx + fz * dz) / (d * (math.hypot(fx, fz) or 1)) < self.PVP_SHOT_COS:
                return
        else:
            if d > (2.4 if spin else 2.0) or abs(l2[1] - me[1]) > 1.5:
                return
            if not spin and d > 0.3 and (fx * dx + fz * dz) / (d * (math.hypot(fx, fz) or 1)) < 0.3:   # ikke foran meg
                return
        if now - getattr(self, '_pvp_hit_last', 0) < 0.45:
            return
        self._pvp_hit_last = now
        dmg = 2 if shot else (8 if spin else 4)   # 3 hjerter i PvP; slag = 1 hjerte, spinn = 2, sprettert = ½.
        self._pvp_hit_total = getattr(self, '_pvp_hit_total', 0) + dmg
        log(f'pvp: TREFF på vennen med {an} ({d:.1f} m) -{dmg} kvartaler (PvP-sum {self._pvp_hit_total})')
        try:
            # Vis samme treff på angriperens Link 2. Mottakeren gjør dette også på sin ekte Link.
            r = pad.hit_replay(p, tgt_act, pad.p_act, dmg)
            log(f'pvp: skadereaksjon på motstanderen (hit replay {r})')
            if not r:
                pad.play_anim(p, tgt_act, 'Damage')
        except Exception as e:  # noqa: BLE001
            log(f'pvp: skadereaksjon på Link 2 feilet {e!r}')

    # v0.94.316: brett (arena). Klasseverdiene under er Gohma-rommet; _apply_arena() overstyrer dem per instans når
    # lobbyen (serverens «arena»-felt) eller /cfg pvp_arena velger et annet brett. CTF finnes bare i Gohma-rommet.
    ARENAS = {
        'gohma': {'name': 'Gohma-arenaen', 'banc': 'InsideTheDekuTree', 'start': 'Entrance',
                  'positions': ([6.7, 48.0, 67.6], [7.7, 48.0, 66.6]), 'y': (40.0, 65.0), 'box': None, 'boss_door': True,
                  'ctf': True, 'bases': {'Blue': [19.9, 47.0, 50.0], 'Red': [23.8, 47.0, 86.4]}},
        # Sverd-banen i Kokiri-skogen (kula Obj_Kokiri_RollingRock_A_01 ved (-79.9, 120.7, 27.0); banen
        # Land_Kokiri_RollingRockArea_* x -94..-78, z 17..47, gulv y≈118.6 – fra KokiriForest_Child_Dynamic.bcett).
        'sword': {'name': 'Sverd-banen', 'banc': 'KokiriForest_Child', 'start': 'LostWoodBridge_FrontOfHyruleField',
                  'positions': ([-79.0, 119.4, 18.0], [-86.5, 119.4, 45.5]), 'y': (112.0, 130.0),
                  'box': (-104.0, -66.0, 6.0, 58.0), 'boss_door': False, 'rock': 'Obj_Kokiri_RollingRock_A_01'},
        # v0.94.320: Zora's Domain (barn). Basene ved spillets egne ankomstpunkter (daurosk coop_start_points.inc):
        # Rød ved inngangen fra Zora's River (4.5, 103.9, -37.0), Blå ved stien til Zora's Fountain (89.0, 119.4, 15.6).
        # Lake Hylia-ankomst (3.3, 93.6, -3.7) er bunnen. Grenser: bare høyde inntil målt.
        'zora': {'name': "Zora's Domain", 'banc': 'ZoraDomain_Child', 'start': 'ZoraDomain_FromZoraRiver',
                 'positions': ([4.5, 104.4, -34.0], [86.0, 119.9, 15.6]), 'y': (80.0, 150.0), 'box': None,
                 'boss_door': False, 'ctf': True,
                 'bases': {'Red': [4.5, 104.4, -37.0], 'Blue': [89.0, 119.9, 15.6]},
                 'team_spawn': {'Red': [4.5, 104.4, -34.0], 'Blue': [86.0, 119.9, 15.6]},   # 3 m fra fakkelen (stod i den)
                 # v0.94.320: facklene sto over bakken. Fot = gulv (StartPos-y fra ZoraDomain_Child_Static.bcett) - 0.5;
                 # midtfakkelen mellom spillets to fakkelstativer på plassen (36.1, 114.4, 12.7 / 18.6) i stedet for
                 # midtpunktet (over bassenget). Lyssøyle over hver base så man ser hvor man skal.
                 'torch_y': {'Red': 103.4, 'Blue': 118.9}, 'mid': [36.1, 114.4, 15.6], 'base_pillars': True},
        # v0.94.322: Hyrule Field om natten (brukerønske): Rød ved Gerudo Valley-inngangen, Blå ved Kakariko-trappa
        # (spillets ankomstpunkter, daurosk coop_start_points.inc) – ca. 500 m mellom basene. Ingen NPC-er/fiender
        # (clear_radius dekker hele feltet), klokka holdes på natt, lyssøyler viser vei.
        'field': {'name': 'Hyrule Field (night)', 'banc': 'HyruleField_Child', 'start': 'HyruleField_FrontOfGerudoValley',
                  'positions': ([-291.0, 138.6, 165.8], [121.5, 153.4, 39.6]), 'y': (100.0, 230.0), 'box': None,
                  'boss_door': False, 'ctf': True,
                  # v0.94.322: gulv målt med /tp (landingspunkt); base-y = gulv + 0.5 som i Zora, fakkelfot = gulv - 0.5
                  'bases': {'Red': [-294.1, 138.6, 166.7], 'Blue': [124.3, 153.4, 38.6]},   # Blå 70 m fra uglen ved Kakariko
                  'team_spawn': {'Red': [-291.0, 138.6, 165.8], 'Blue': [121.5, 153.4, 39.6]},
                  'torch_y': {'Red': 137.6, 'Blue': 152.4},
                  'mid': [-53.1, 148.6, 90.5], 'base_pillars': True, 'night': 0, 'clear_radius': 700.0, 'no_stalchild': 60.0,
                  # lyssøyler (ikke flammer) ~45 m fra hverandre langs ruta Rød–Blå (målte gulvpunkter + 0.5)
                  'route': [[-252.2, 141.7, 161.4], [-202.5, 142.2, 149.1], [-161.2, 142.8, 127.5], [-119.1, 152.0, 112.0],
                            [-74.7, 149.3, 97.9], [-31.0, 149.2, 84.1], [13.1, 149.4, 71.2], [57.0, 151.4, 57.5],
                            [101.0, 154.7, 46.8]]},
    }
    PVP_ARENA_Y = (40.0, 65.0)
    PVP_ARENA_BOX = None
    ROCK_SNAP = 3.0    # v0.94.319: kula hopper bare ved større avvik (m)
    ROCK_PULL = 0.25   # ellers trekkes den denne brøkdelen mot vennens posisjon per tick
    PVP_BANC = 'InsideTheDekuTree'                       # CtF/DM-arena, aldri sosial lobby
    PVP_ARENA_START = 'Entrance'                         # vanlig inngang; bossrommet nås med intern teleport
    PVP_ARENA_POSITIONS = ([6.7, 48.0, 67.6], [7.7, 48.0, 66.6])
    PVP_LOBBY_BANC = 'Market_Child'
    PVP_LOBBY_START = 'Market_Entrance'                  # vanlig ankomst; Bowling nås med kontrollert intern teleport
    PVP_LOBBY = ([-25.1325, 100.0286, 9.5089], [-24.1325, 100.0286, 9.5089])
    PVP_LOBBY_CENTER = PVP_LOBBY[0]
    PVP_LOBBY_RADIUS = 400.0                             # v0.94.100: hele byen er lobby (brukerønske); ut av byen = sonebytte
    PVP_BASES = {'Blue': [19.9, 47.0, 50.0], 'Red': [23.8, 47.0, 86.4]}
    PVP_EXIT = [0.2, 101.5, 18.0]                         # trygt sted ved inngangen til Deku-treet (gulv y≈101.04, unngår SystemTextNPC på [-5.6, 100.0, 2.3])
    PVP_CENTER = (18.5, 67.8)
    PVP_RADIUS = 15.0
    PVP_LOBBY_BGM_DEFAULT = 'BGM_Drugstore'
    PVP_LOBBY_BGM_VOL_DEFAULT = 0.35
    PVP_LOBBY_BGM_ALIASES = {
        'shop': 'BGM_Drugstore',
        'bgm_shop': 'BGM_Drugstore',
        'drugstore': 'BGM_Drugstore',
        'scrub': 'BGM_Shop_ScrubBusiness',
        'desert': 'BGM_Shop_Desert',
        'minigame': 'BGM_MiniGame',
        'house': 'BGM_House',
        'fairy': 'BGM_GreatFairyFountain',
        'market': 'BGM_Market',
        'off': 'BGM_Silence',
        'mute': 'BGM_Silence',
        'silence': 'BGM_Silence',
    }
    PVP_JUKEBOX_TRACKS = [
        ('BGM_Drugstore', 'Potion Shop (Vendor)'),
        ('BGM_Shop_ScrubBusiness', 'Business Scrub Shop'),
        ('BGM_Shop_Desert', 'Desert Shop'),
        ('BGM_MiniGame', 'Mini-Game'),
        ('BGM_House', 'House'),
        ('BGM_GreatFairyFountain', 'Great Fairy Fountain'),
        ('BGM_Market', 'Market'),
        ('BGM_Silence', 'Mute (Off)'),
    ]

    def _jukebox_label_for(self, track_id):
        for tid, lbl in self.PVP_JUKEBOX_TRACKS:
            if tid == track_id:
                return lbl
        return track_id

    def _jukebox_refresh(self):
        if not hasattr(self, 'jukebox_track_var'):
            return
        tr, vol = self._pvp_lobby_bgm_cfg()
        lbl = self._jukebox_label_for(tr)
        vals = [l for _, l in self.PVP_JUKEBOX_TRACKS]
        if lbl not in vals:
            vals.append(lbl)
        self.jukebox_box.config(values=vals)
        self.jukebox_track_var.set(lbl)
        muted = (tr == 'BGM_Silence' or vol <= 0.0)
        self.jukebox_now.config(text='Muted' if muted else lbl, fg=MUTED if muted else FG)
        self.jukebox_mute_btn.config(text='Play' if muted else 'Mute')

    def _jukebox_set(self, track_id, vol):
        vol = round(max(0.0, min(1.0, float(vol))), 2)
        if track_id != 'BGM_Silence' and vol > 0.0:
            self._jukebox_last_track = track_id
            self._jukebox_last_vol = vol
        self.cfg['pvp_lobby_bgm'] = track_id
        self.cfg['pvp_lobby_bgm_vol'] = vol
        self.cfg['pvp_jukebox_arena'] = True   # v0.94.321: brukt jukeboks -> gjelder også i arenaene
        save_cfg(self.cfg)
        self._pvp_lobby_bgm_applied = None
        self._jukebox_refresh()
        if getattr(self, 'mode', 'Story') == 'PvP' and self.p and getattr(self, 'ready', False) and (
                getattr(self.pad, 'cur_banc', None) == self.PVP_LOBBY_BANC or self._pvp_jukebox_in_arena(True)):
            self._pvp_sync_lobby_bgm(force=True, async_worker=True)

    def _jukebox_step(self, delta):
        cur_tr, cur_vol = self._pvp_lobby_bgm_cfg()
        ids = [tid for tid, _ in self.PVP_JUKEBOX_TRACKS]
        idx = ids.index(cur_tr) if cur_tr in ids else 0
        nxt = ids[(idx + delta) % len(ids)]
        if nxt != 'BGM_Silence' and cur_vol <= 0.0:
            cur_vol = getattr(self, '_jukebox_last_vol', self.PVP_LOBBY_BGM_VOL_DEFAULT)
        self._jukebox_set(nxt, cur_vol)

    def _jukebox_on_select(self, _ev=None):
        sel = self.jukebox_track_var.get()
        tid = next((t for t, l in self.PVP_JUKEBOX_TRACKS if l == sel), sel)
        _, cur_vol = self._pvp_lobby_bgm_cfg()
        if tid != 'BGM_Silence' and cur_vol <= 0.0:
            cur_vol = getattr(self, '_jukebox_last_vol', self.PVP_LOBBY_BGM_VOL_DEFAULT)
        self._jukebox_set(tid, cur_vol)

    def _jukebox_on_vol(self, val):
        try:
            pct = int(float(val))
        except (TypeError, ValueError):
            return
        self.jukebox_vol_lbl.config(text=f'{pct}%')
        if getattr(self, '_jukebox_vol_job', None) is not None:
            try:
                self.root.after_cancel(self._jukebox_vol_job)
            except Exception:
                pass
        self._jukebox_vol_job = self.root.after(150, lambda p=pct: self._jukebox_apply_vol(p))

    def _jukebox_apply_vol(self, pct):
        self._jukebox_vol_job = None
        tr, _ = self._pvp_lobby_bgm_cfg()
        vol = round(max(0.0, min(1.0, pct / 100.0)), 2)
        if vol > 0.0 and tr == 'BGM_Silence':
            tr = getattr(self, '_jukebox_last_track', self.PVP_LOBBY_BGM_DEFAULT)
        self._jukebox_set(tr, vol)

    def _jukebox_toggle_mute(self):
        cur_tr, cur_vol = self._pvp_lobby_bgm_cfg()
        if cur_tr == 'BGM_Silence' or cur_vol <= 0.0:
            tr = getattr(self, '_jukebox_last_track', self.PVP_LOBBY_BGM_DEFAULT)
            vol = getattr(self, '_jukebox_last_vol', self.PVP_LOBBY_BGM_VOL_DEFAULT)
            if tr == 'BGM_Silence':
                tr = self.PVP_LOBBY_BGM_DEFAULT
            if vol <= 0.0:
                vol = self.PVP_LOBBY_BGM_VOL_DEFAULT
            self._jukebox_set(tr, vol)
        else:
            self._jukebox_last_track = cur_tr
            self._jukebox_last_vol = cur_vol
            self._jukebox_set('BGM_Silence', 0.0)

    def _pvp_lobby_bgm_cfg(self):
        cfg = getattr(self, 'cfg', None) or {}
        tr = cfg.get('pvp_lobby_bgm') or self.PVP_LOBBY_BGM_DEFAULT
        try:
            vol = float(cfg.get('pvp_lobby_bgm_vol', self.PVP_LOBBY_BGM_VOL_DEFAULT))
        except (TypeError, ValueError):
            vol = self.PVP_LOBBY_BGM_VOL_DEFAULT
        return tr, max(0.0, min(1.0, vol))

    def _pvp_restore_lobby_bgm(self, restart_market=False, async_worker=False):
        if getattr(self, '_pvp_lobby_bgm_applied', None) is None:
            return
        if async_worker:
            if getattr(self, '_pvp_bgm_busy', False):
                return
            self._pvp_bgm_busy = True
            def work():
                try:
                    self._pvp_restore_lobby_bgm(restart_market=restart_market, async_worker=False)
                finally:
                    self._pvp_bgm_busy = False
            threading.Thread(target=work, daemon=True, name='PvPBGMRestore').start()
            return
        self._pvp_lobby_bgm_applied = None
        if self.p and self.ready:
            self.pad.restore_lobby_bgm(self.p, restart_market=restart_market)

    def _pvp_jukebox_in_arena(self, force=False):
        """True når jukebox-valget skal spilles i arenaen (PvP, inne i arenaen, jukeboxen brukt)."""
        pad = self.pad
        return bool(getattr(self, 'mode', 'Story') == 'PvP'
                    and self.p and getattr(self, 'ready', False)
                    and getattr(self, '_pvp_in_arena', False)
                    and (getattr(self, 'cfg', None) or {}).get('pvp_jukebox_arena')
                    and getattr(pad, 'cur_banc', None) == self.PVP_BANC
                    and (force or not getattr(self, '_pvp_travel_busy', False)))

    def _pvp_sync_lobby_bgm(self, now=None, force=False, async_worker=False):
        """Bytt musikk i Bombchu-lobbyen til dempet BGM_Drugstore (kun i PvP)."""
        if now is None:
            now = time.time()
        pad, p = self.pad, self.p
        lobby_st = (getattr(self, '_server_state', None) or {}).get('lobby') or {}
        tok = (lobby_st.get('id'), lobby_st.get('started_at'), getattr(self, '_server_round', 1)) if lobby_st.get('started') else None
        in_lobby = (getattr(self, 'mode', 'Story') == 'PvP'
                    and p and getattr(self, 'ready', False)
                    and getattr(pad, 'cur_banc', None) == self.PVP_LOBBY_BANC
                    and not getattr(self, '_pvp_in_arena', False)
                    and (force or (not getattr(self, '_pvp_travel_busy', False)
                                   and (not lobby_st.get('started') or tok == getattr(self, '_pvp_manual_lobby_tok', None)))))
        # v0.94.321: jukeboxen gjelder også i arenaen, men først etter at spilleren selv har brukt den
        # (ellers beholder arenaen sin egen musikk).
        if not in_lobby:
            in_lobby = self._pvp_jukebox_in_arena(force)
        if not in_lobby:
            self._pvp_restore_lobby_bgm(
                restart_market=(getattr(self, 'mode', 'Story') == 'Story' and getattr(pad, 'cur_banc', None) == self.PVP_LOBBY_BANC),
                async_worker=async_worker,
            )
            return False
        if not force:
            if now < getattr(pad, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN:
                return False
            if now - getattr(pad, '_banc_since', 0) < 0.8:
                return False
        tr, vol = self._pvp_lobby_bgm_cfg()
        key = (tr, round(vol, 2), getattr(pad, '_banc_since', 0))
        if not force and getattr(self, '_pvp_lobby_bgm_applied', None) == key:
            return True
        if not force and now - getattr(self, '_pvp_bgm_try_t', 0) < 1.5:
            return False
        self._pvp_bgm_try_t = now
        stop_list = ['BGM_Market', 'BGM_Shop_ScrubBusiness', 'BGM_Shop_Desert', 'BGM_Drugstore',
                     'BGM_MiniGame', 'BGM_House', 'BGM_GreatFairyFountain', 'BGM_Silence']
        if async_worker:
            if getattr(self, '_pvp_bgm_busy', False):
                return False
            self._pvp_bgm_busy = True
            def work():
                try:
                    ok = pad.set_lobby_bgm(p, play_name=tr, stop_names=[s for s in stop_list if s != tr], vol=vol)
                    if ok:
                        self._pvp_lobby_bgm_applied = key
                        log(f'pvp-bgm: lobby-musikk satt til {tr} (vol={vol:.2f})')
                finally:
                    self._pvp_bgm_busy = False
            threading.Thread(target=work, daemon=True, name='PvPBGMSet').start()
            return False
        ok = pad.set_lobby_bgm(p, play_name=tr, stop_names=[s for s in stop_list if s != tr], vol=vol)
        if ok:
            self._pvp_lobby_bgm_applied = key
            log(f'pvp-bgm: lobby-musikk satt til {tr} (vol={vol:.2f})')
        return ok

    def _pvp_wait_banc(self, banc, generation, seconds=20.0):
        """Vent kansellerbart på en ferdig scenelasting uten å blokkere GUI-et."""
        deadline = time.time() + seconds
        while time.time() < deadline:
            if generation != getattr(self, '_mode_generation', 0) or self.mode != 'PvP':
                return False
            if self.pad.cur_banc == banc and time.time() - getattr(self.pad, '_banc_since', 0) > 3.0:
                try:
                    anim = self.pad.read_anim(self.p, self.pad.p_act)[0] if self.pad.p_act is not None else None
                except Exception:  # noqa: BLE001
                    anim = None
                if anim != 'EvtWait':
                    return True
            time.sleep(0.25)
        return False

    def _pvp_change_banc(self, banc, start, generation):
        """Ikke kollider med Link 2-spawn, EvtWait eller pågående EventMgr-event; avvisning kan være midlertidig."""
        deadline = time.time() + 90.0
        next_diag = 0.0
        while time.time() < deadline:
            if generation != getattr(self, '_mode_generation', 0) or self.mode != 'PvP':
                return False
            pad = self.pad
            try:
                anim = pad.read_anim(self.p, pad.p_act)[0] if pad.p_act is not None else None
            except Exception:  # noqa: BLE001
                anim = None
            ev_busy = pad.event_busy(self.p) if (self.p and hasattr(pad, 'event_busy')) else None
            settled = (pad.p_act is not None and not getattr(pad, '_spawning', False)
                       and time.time() - getattr(pad, '_tp_t', 0) > 6.0 and anim != 'EvtWait' and not ev_busy)
            if not settled and time.time() >= next_diag:
                next_diag = time.time() + 10.0
                log(f'pvp: venter på ro før {banc}: aktør={pad.p_act is not None} '
                    f'anim={anim} spawner={getattr(pad, "_spawning", False)} '
                    f'ev={ev_busy or "-"} teleport-alder={time.time() - getattr(pad, "_tp_t", 0):.1f}s')
            if settled:
                r = pad.change_banc(self.p, banc, start)
                log(f'pvp: scenebytte {banc} @ {start} -> {r}')
                if r:
                    return True
                fails = getattr(self, '_pvp_cb_fails', 0) + 1
                self._pvp_cb_fails = fails
                if fails >= 5:
                    self._pvp_cb_fails = 0
                    self._pvp_travel_retry = time.time() + 30.0
                    return False
            else:
                self._pvp_cb_fails = 0
            time.sleep(2.0)
        return False

    def _at_counter(self, pos):
        """True når Link står ved disken i Bombchu-hallen."""
        if not pos or len(pos) < 3:
            return False
        return math.dist(pos[:3], self.PVP_SHOP_POS) <= self.PVP_SHOP_RANGE

    def _shop_near(self, p, actor):
        """NPC-er ved bordet og disken. 4 m bommet på 038 og 067 (begge 4,7 m)."""
        try:
            return math.dist(p.f32(actor + 0x31C, 3), self.PVP_SHOP_POS) < 8.0
        except OSError:
            return False

    def _counter_a_down_raw(self):
        """A på den ekte kontrolleren (bit 0x1 i ordet på hR+0x2C0)."""
        pad, p = getattr(self, 'pad', None), getattr(self, 'p', None)
        if pad is None or p is None or getattr(pad, 'hR', None) is None:
            return False
        try:
            return bool(struct.unpack('<I', p.read(p.base + pad.hR + 0x2C0, 4))[0] & 1)
        except OSError:
            return False

    def _counter_should_open(self, pos, a_down):
        """Åpne disken på en ny A ved bordet. Holder ikke menyen oppe av seg selv."""
        prev = getattr(self, '_counter_a_down', False)
        self._counter_a_down = bool(a_down)
        if not (bool(a_down) and not prev) or getattr(self, '_counter_open', False):
            return False
        if getattr(self, 'mode', 'Story') != 'PvP':
            return False
        if getattr(self, '_pvp_in_arena', False) or getattr(self, '_pvp_travel_busy', False):
            return False
        if not getattr(self, '_pvp_social_lobby', False):
            return False
        if getattr(getattr(self, 'pad', None), 'cur_banc', None) != self.PVP_LOBBY_BANC:
            return False
        return self._at_counter(pos)

    def _counter_refresh(self):
        lbl = getattr(self, 'counter_ruby', None)
        if lbl is None:
            return
        prof = getattr(self, '_pvp_profile', None) or {}
        rub = int(prof.get('rubies') or 0) if isinstance(prof, dict) else 0
        lbl.config(text=f'{rub} rubies')
        shop = getattr(self, '_pvp_shop', None) or {}
        for item_id, label, price, qty in self.PVP_COUNTER:
            spec = shop.get(item_id) or {}
            btn = getattr(self, 'counter_btns', {}).get(item_id)
            if btn is not None:
                btn.config(text=f"{label}   +{spec.get('qty', qty)}   {spec.get('price', price)} r")

    def _counter_set_open(self, open_):
        fr = getattr(self, 'counter_fr', None)
        self._counter_open = bool(open_) and fr is not None
        if fr is None:
            return
        if open_:
            self._counter_refresh()
            if not fr.winfo_ismapped():
                fr.pack(fill='x', padx=10, pady=(0, 6), after=self.lobby_info)
        elif fr.winfo_ismapped():
            fr.pack_forget()

    def _counter_close(self):
        self._counter_set_open(False)

    def _counter_tick(self, now):
        """A ved disken åpner kjøpsmenyen. Å gå vekk lukker den."""
        pos = None
        try:
            if getattr(self, 'p', None) is not None and getattr(self, 'ready', False):
                pos = self.pad.my_apos(self.p)
        except Exception:  # noqa: BLE001
            pos = None
        if self._counter_should_open(pos, self._counter_a_down_raw()):
            self._counter_set_open(True)
            self._append_chat_sys('🛒 Counter open')
        elif not self._at_counter(pos) or getattr(self, 'mode', 'Story') != 'PvP':
            self._counter_set_open(False)

    def _shop_buy(self, item_id):
        """Kjøp PvP-vare. Serveren trekker rubinene. Kun PvP."""
        if getattr(self, 'mode', 'Story') != 'PvP':
            self._append_chat_sys('PvP Shop is only available in PvP mode.')
            return
        if not item_id:
            for msg in self._info_cmd('/inv'):
                self._append_chat_sys(msg)
            return
        self._server_cmd('buy', item_id=item_id)
        self._append_chat_sys(f'🛒 Buying {item_id} …')

    def _goto_lobby(self):
        """Start én bakgrunnsreise til Bombchu-lobbyen uten å blokkere Tk-tråden."""
        if self.mode != 'PvP':
            self._append_chat_sys('Goto Lobby is only available in PvP mode.')
            return
        if not (self.p and self.ready and self.pad.p_act is not None):
            self._append_chat_sys('Wait until the game and Link are ready before entering the lobby.')
            return
        if getattr(self, '_pvp_travel_busy', False):
            self._append_chat_sys('Lobby travel is already in progress.')
            return
        lb = (getattr(self, '_server_state', None) or {}).get('lobby') or {}
        if lb.get('started'):
            self._pvp_manual_lobby_tok = (lb.get('id'), lb.get('started_at'), getattr(self, '_server_round', 1))
            if lb.get('host') == self.name:
                self._server_cmd('stop')
        self._pvp_travel_retry = 0
        self._pvp_lobby_done = False
        threading.Thread(target=self._pvp_go_lobby, daemon=True, name='GotoLobby').start()

    def _pvp_go_lobby(self):
        """PvP: ekte scenebytte til Bombchu Bowling Alley, en safe zone uten NPC-sletting."""
        if getattr(self, '_pvp_travel_busy', False):
            return
        self._pvp_travel_busy = True
        self.pad.suppress_link2 = True
        generation = getattr(self, '_mode_generation', 0)
        try:
            p, pad = self.p, self.pad
            if not (p and self.ready and pad.p_act is not None):
                return
            self._pvp_in_arena = False; self._pvp_social_lobby = False
            self._pvp_restore_lobby_bgm(restart_market=False)
            self._ctf_actors = {}; self._ctf_lit = {}; self._ctf_friend_lit = {}; self._ctf_point_sent = {}
            current_banc = pad.read_banc(p) or pad.cur_banc   # ikke bruk et foreldet sonenavn etter Story-retur
            if current_banc:
                pad.cur_banc = current_banc
            if current_banc != self.PVP_LOBBY_BANC:
                st = pad.read_last_start(p)
                if st == 'LostWoodBridge_FrontOfHyruleField' and current_banc != 'KokiriForest_Child':
                    st = None
                self._story_return = {'banc': current_banc, 'start': st, 'pos': pad.my_apos(p)}
                r = self._pvp_change_banc(self.PVP_LOBBY_BANC, self.PVP_LOBBY_START, generation)
                log(f'pvp: bytter til Bombchu-lobby -> {r}')
                if not r or not self._pvp_wait_banc(self.PVP_LOBBY_BANC, generation):
                    log('pvp: Bombchu-lobby avbrutt eller kunne ikke lastes')
                    return
            fs = (self.friend or {}).get('s') if self.friend else None
            slot = 1 if (fs is not None and fs < self.session) else 0
            pos = self.PVP_LOBBY[slot]
            r = pad.teleport_player(p, pos)
            self._pvp_spawn = list(pos)
            self._pvp_social_lobby = True
            self._pvp_lobby_done = True
            pad.suppress_link2 = False
            self._pvp_set_hp(True)
            self._pvp_lobby_bgm_applied = None
            self._pvp_sync_lobby_bgm(force=True)
            log(f'pvp: Bombchu safe zone plass {slot} {pos} -> {r}')
            self.ui(self._append_chat_sys, '🛡️ Bombchu lobby – safe zone. Choose a game and press Start.')
        except Exception as e:  # noqa: BLE001
            log(f'pvp: lobby-feil {e!r}')
        finally:
            self._pvp_travel_busy = False

    def _pvp_go_arena(self):
        """Forlat safe zone og last en arena som passer spilltypen."""
        if getattr(self, '_pvp_travel_busy', False) or self.mode != 'PvP':
            return
        self._pvp_travel_busy = True
        self.pad.suppress_link2 = True
        generation = getattr(self, '_mode_generation', 0)
        try:
            p, pad = self.p, self.pad
            if not (p and self.ready and pad.p_act is not None):
                return
            self._pvp_social_lobby = False; self._pvp_in_arena = False
            self._pvp_restore_lobby_bgm(restart_market=False)
            self._ctf_actors = {}; self._ctf_lit = {}; self._ctf_friend_lit = {}; self._ctf_point_sent = {}
            lobby = (getattr(self, '_server_state', {}).get('lobby') or {})
            if self._game_mode == 'deathmatch' and lobby.get('capacity') in (20, 50):
                field = 'HyruleField_Child'
                if pad.cur_banc != field:
                    self._pvp_field_origin = (pad.p_act, pad.my_apos(p))
                    if not self._pvp_change_banc(field, pad.START_POS[field], generation):
                        return
                    if not self._pvp_wait_banc(field, generation):
                        return
                origin = getattr(self, '_pvp_field_origin', None)
                if origin is not None:
                    old_actor, old_pos = origin
                    deadline = time.monotonic() + 20
                    while time.monotonic() < deadline:
                        if self.mode != 'PvP' or generation != getattr(self, '_mode_generation', 0):
                            return
                        arrived = pad.my_apos(p)
                        if arrived and (pad.p_act != old_actor or old_pos is None
                                        or math.dist(old_pos, arrived) > 3.0
                                        or math.dist(arrived, (198.18, 163.38, 309.63)) < 3.0):
                            break
                        time.sleep(0.25)
                    else:
                        log('pvp: Hyrule Field rapportert, men spillerposisjonen ble ikke lastet')
                        return
                pos = pad.my_apos(p)
                if pos is None or self.mode != 'PvP' or generation != getattr(self, '_mode_generation', 0):
                    return
                # Move off the bridge approach before releasing the mirror spawn.
                spawn = [184.0, 163.4, 314.0]
                if not pad.teleport_player(p, spawn, pad.my_arot(p)):
                    log('pvp: kunne ikke flytte Link vekk fra broutgangen')
                    return
                # The position write can be visible while the scene is still
                # settling, then get replaced by the bridge arrival transform.
                time.sleep(CALL_TELEPORT_COOLDOWN)
                landed = pad.my_apos(p)
                if self.mode != 'PvP' or generation != getattr(self, '_mode_generation', 0):
                    return
                if pad.cur_banc != field or not landed or math.dist(landed, spawn) > 5.0:
                    log(f'pvp: feltspawn mangler bekreftelse etter teleport, pos={landed}')
                    return
                self._pvp_field_origin = None
                self._pvp_spawn = spawn
                self._pvp_in_arena = True
                self._pvp_lobby_done = True
                self._pvp_set_hp(True)
                self.ui(self._append_chat_sys, '⚔️ Deathmatch started in Hyrule Field.')
                return
            if pad.cur_banc != self.PVP_BANC:
                r = self._pvp_change_banc(self.PVP_BANC, self.PVP_ARENA_START, generation)
                log(f'pvp: bytter fra lobby til {self._game_mode}-arena -> {r}')
                if not r or not self._pvp_wait_banc(self.PVP_BANC, generation):
                    log('pvp: arenaovergang avbrutt eller kunne ikke lastes')
                    return
            if self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('clear_radius', 0) > 200:
                self._pvp_preclear(generation)   # v0.94.322: hele feltet tømt før spillerne flyttes til basene
            ts = self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('team_spawn') or {}
            if ts and self._game_mode == 'ctf':   # v0.94.320: rett etter mod-omstart er laget ukjent – vent inntil 10 s
                t_end = time.time() + 10.0
                while (self._active_pvp_team() not in ts and time.time() < t_end
                       and generation == getattr(self, '_mode_generation', 0) and self.mode == 'PvP'):
                    time.sleep(0.5)
            fs = (self.friend or {}).get('s') if self.friend else None
            slot = 1 if (fs is not None and fs < self.session) else 0
            pos = self.PVP_ARENA_POSITIONS[slot]
            if ts and self._game_mode == 'ctf' and self._active_pvp_team() in ts:   # v0.94.320: CTF-start ved egen base
                pos = ts[self._active_pvp_team()]
            # Marker _pvp_in_arena før teleport (pos x≈6.7/7.7 < 8.0) så _pvp_early_exit ikke kaster ut ved spawn.
            self._pvp_exit_armed = False
            self._pvp_exit_t = time.time()
            self._pvp_in_arena = True
            self._pvp_lobby_done = True   # v0.94.320: ellers drar AutoLobby oss ut av arenaen etter mod-omstart
            r = pad.teleport_player(p, pos)
            self._pvp_spawn = list(pos)
            for i_ in (8595, 8594):
                if generation != getattr(self, '_mode_generation', 0) or self.mode != 'PvP':
                    self._pvp_in_arena = False
                    return
                pad.clear_bool(p, i_)
            pad.suppress_link2 = False
            self._pvp_set_hp(True)
            if self._game_mode == 'ctf':
                self._ctf_setup()
            # v0.94.320: spillet kan sette Link tilbake til ankomstpunktet mens scenen ennå starter (sett i Zora's Domain:
            # teleport til blå base 17:51:50, stod ved elveinngangen 17:52:27). Sjekk etter oppsettet og prøv igjen.
            for _try in range(3):
                if generation != getattr(self, '_mode_generation', 0) or self.mode != 'PvP' or not self._pvp_in_arena:
                    break
                while time.time() < getattr(pad, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN:
                    time.sleep(0.25)
                me_ = pad.my_apos(p)
                if not me_ or math.dist(me_, pos) <= 4.0:
                    break
                r = pad.teleport_player(p, pos)
                log(f'pvp: stod {[round(v, 1) for v in me_]}, {math.dist(me_, pos):.0f} m fra startplassen – teleporterer igjen -> {r}')
                time.sleep(2.0)
            if self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('clear_radius', 0) > 200:
                self._pvp_preclear(generation)   # det som ble lastet inn ved basen
            log(f"pvp: i {self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('name', 'arenaen')} ({self._game_mode}) plass {slot} -> {r}")
            self.ui(self._append_chat_sys, '⚔️ Match started – safe zone is disabled in the arena!')
        except Exception as e:  # noqa: BLE001
            import traceback
            log(f'pvp: arena-feil {e!r}\n{traceback.format_exc()}')
        finally:
            self.pad.suppress_link2 = False
            self._pvp_travel_busy = False

    PVP_PRECLEAR_TRIG = ('EventRequestActor', 'EventProxyRequestActor', 'Dm_Locator', 'SystemTextNPC')

    def _pvp_bury(self, p, a, nm):
        """v0.94.322: fiende som ikke kan slettes (Enemy_Guay_Fixed, Peahat-larve): flytt 500 m ned og deaktiver."""
        try:
            pos = p.f32(a + 0x31C, 3)
            if pos[1] < -200:
                return True
            p.write(p.base + a + 0x31C, struct.pack('<3f', pos[0], pos[1] - 500.0, pos[2]))
            p.write(p.base + a + 0x2C, struct.pack('<I', 5))
            log(f'pvp: {nm} kunne ikke slettes – flyttet under bakken')
            return True
        except OSError:
            return False

    def _pvp_preclear(self, generation):
        """v0.94.322: store brett (Hyrule Field): slett alle NPC-er, fiender og hendelsesutløsere i hele scenen
        før spillerne teleporteres til basene (uglen ved Kakariko startet samtale ved blå base)."""
        p, pad = self.p, self.pad
        t0 = time.time(); n = 0; fail = 0
        while time.time() < getattr(pad, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN:
            if generation != getattr(self, '_mode_generation', 0) or self.mode != 'PvP':
                return
            time.sleep(0.25)
        gone = self.__dict__.setdefault('_pvp_gone', set())
        bad, badn = set(), set()
        for _round in range(3):
            allm = {}; pad._scan_full_t = 0
            found = pad._scan_actors_raw(p, allm) or {}
            allm.update({a_: v_[0] for a_, v_ in found.items()})
            todo = [(a, nm) for a, nm in sorted(allm.items()) if a not in bad
                    and ((nm.startswith(('Npc_', 'Enemy_')) and nm != 'Npc_Navi') or nm in self.PVP_PRECLEAR_TRIG)]
            if not todo:
                break
            for a, nm in todo:
                if generation != getattr(self, '_mode_generation', 0) or self.mode != 'PvP':
                    return
                r = pad.delete_actor(p, a)
                if r:
                    gone.add(a); n += 1
                else:
                    fail += 1; bad.add(a); badn.add(nm)
                    if nm.startswith('Enemy_') and self._pvp_bury(p, a, nm):
                        gone.add(a)
        log(f'pvp: forhåndsrydding av {pad.cur_banc}: {n} NPC/fiender/utløsere fjernet, {fail} feilet {sorted(badn)}, {time.time() - t0:.1f} s')

    # Capture the Flame: fakkelstolper ved basene og tent fakkel/lyssøyle i midten.
    # Obj_BlueFire/Obj_FireTemple_Fire beholdes KUN i oppryddingen etter v0.94.43.
    CTF_OBJ = ('Obj_CandleStick', 'Obj_BlueFire', 'Obj_FireTemple_Fire', 'Obj_FireTemple_CandleStick', 'Obj_LightSourceBase', 'EftLoc_SageRoom', 'EftLoc_GanonCastle_Barrier_Light', 'EftLoc_FairySpirit_AppearPoint')
    CTF_SCORE_EFFECT = {'Blue': 'EftLoc_SageRoom_BlueLight_00', 'Red': 'EftLoc_GanonCastle_Barrier_Light_A_01'}

    def _ctf_celebrate(self, team):
        """Kort, skadeløs effekt over scorende base; opprydding skjer ved fakkelreset."""
        effect = self.CTF_SCORE_EFFECT.get(team)
        if not effect or self.mode != 'PvP' or self._game_mode != 'ctf':
            return
        base = self.PVP_BASES[team]
        try:
            for name, pos in ((effect, [base[0], base[1] + 2.0, base[2]]),
                              ('EftLoc_FairySpirit_AppearPoint', [base[0], base[1] + 3.0, base[2]]),
                              ('EftLoc_SageRoom_LightPillar_00', [base[0], base[1] + 0.5, base[2]])):
                result = self.pad.create_actor(self.p, name, pos)
                log(f'ctf: poengeffekt {team} {name} -> {result}')
                time.sleep(0.25)
        except Exception as e:  # noqa: BLE001
            log(f'ctf: poengeffekt feilet {e!r}')

    def _ctf_setup(self):
        if (self.mode != 'PvP' or self._game_mode != 'ctf' or not getattr(self, '_pvp_in_arena', False)
                or getattr(self, '_ctf_busy', False)):
            return
        generation = getattr(self, '_mode_generation', 0)
        p, pad = self.p, self.pad
        self._ctf_busy = True
        self._ctf_actors = {}; self._ctf_lit = {}; self._ctf_friend_lit = {}; self._ctf_point_sent = {}

        def cancelled():
            return (generation != getattr(self, '_mode_generation', 0) or self.mode != 'PvP'
                    or self._game_mode != 'ctf' or not self._pvp_in_arena)

        def wait_cooldown():
            while not cancelled():
                remaining = getattr(pad, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN - time.time()
                if remaining <= 0:
                    return True
                time.sleep(min(0.25, remaining))
            return False

        try:
            # Arena entry (or a bounceback teleport) guards native calls; always wait out cooldown before F_ACT_DELETE/create_actor.
            if not wait_cooldown():
                return
            allm = {}; pad._scan_full_t = 0
            pad._scan_actors_raw(p, allm)
            for a, nm in allm.items():   # gamle stolper/flammer ved basene (tester, forrige runde) fjernes
                if cancelled():
                    log('ctf: oppsett avbrutt ved modusbytte')
                    return
                if nm.startswith(self.CTF_OBJ):
                    try:
                        q = p.f32(a + 0x31C, 3)
                    except OSError:
                        continue
                    mid = [(self.PVP_BASES['Blue'][k] + self.PVP_BASES['Red'][k]) / 2 for k in range(3)]
                    spots_ = list(self.PVP_BASES.values()) + [mid] + [list(v) for v in (self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('route') or ())]
                    # v0.94.322: på lange brett (route) finnes ingen egne CTF-gjenstander – fjern alle (gamle fakler i lufta)
                    if (self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('route')
                            or any(math.dist(q, b) < (10.0 if nm.startswith('EftLoc') else 4.0) for b in spots_)):
                        if not wait_cooldown():
                            return
                        # Én kort forespørsel: fem lange forsøk per aktør blokkerte modusbyttet.
                        r_ = pad.game_call(p, pad.F_ACT_DELETE, (a + pad.delta, 0), timeout=0.75)
                        log(f'ctf: fjerner gammel {nm} -> {r_}')
            if cancelled():
                return
            time.sleep(0.5)
            b, r = self.PVP_BASES['Blue'], self.PVP_BASES['Red']
            out = []
            ar_ = self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {})
            ty = ar_.get('torch_y') or {}
            c = list(ar_.get('mid') or [(b[0] + r[0]) / 2, b[1], (b[2] + r[2]) / 2])
            plan = [('Obj_CandleStick_NoGimmick_OnOff', [b[0], ty.get('Blue', b[1] - 0.5), b[2]], 1.0),
                    ('Obj_CandleStick_NoGimmick_OnOff', [r[0], ty.get('Red', r[1] - 0.5), r[2]], 1.0),
                    ('Obj_FireTemple_CandleStick_A_01', [c[0], c[1] - (1.3 if not ar_.get('mid') else 0.8), c[2]], 1.0),
                    ('EftLoc_SageRoom_LightPillar_00', list(c), 1.0)]
            for pt_ in (ar_.get('route') or ()):   # v0.94.322: lys som viser vei – ikke flammer (ellers kan man tenne pinnen underveis)
                plan.append(('EftLoc_SageRoom_LightPillar_00', [pt_[0], pt_[1] - 0.5, pt_[2]], 1.0))
            if ar_.get('no_stalchild'):   # v0.94.322: spillets egen «ingen Stalchild her»-sone over hele ruta (forsøk)
                for pt_ in [b, r, c] + [list(v) for v in (ar_.get('route') or ())]:
                    plan.append(('ForbidStalchildDivingArea', [pt_[0], pt_[1], pt_[2]], float(ar_['no_stalchild'])))
            if ar_.get('base_pillars'):   # v0.94.320: synlig søyle + lagfarget lys over hver base
                for tm_, bp_ in (('Blue', b), ('Red', r)):
                    plan.append(('EftLoc_SageRoom_LightPillar_00', [bp_[0], bp_[1] - 0.5, bp_[2]], 1.0))
                    if self.CTF_SCORE_EFFECT.get(tm_):
                        plan.append((self.CTF_SCORE_EFFECT[tm_], [bp_[0], bp_[1] + 2.0, bp_[2]], 1.0))
            for nm, pos, sc in plan:
                if cancelled():
                    log('ctf: oppsett avbrutt før ny aktør')
                    return
                res = None
                for _ in range(3):
                    if not wait_cooldown():
                        log('ctf: oppsett avbrutt under cooldown')
                        return
                    res = pad.create_actor(p, nm, pos, sc)
                    if res is not None or cancelled():
                        break
                    time.sleep(0.5)
                out.append(res); time.sleep(0.5)
            if cancelled():
                return
            log(f'ctf: basefakler og midtfakkel opprettet -> {out}')
            self._ctf_banc_t = getattr(pad, '_banc_since', 0)   # v0.94.322: ny scenelasting (Game Over) -> sett opp på nytt
            self._ctf_find_torches()
        except Exception as e:  # noqa: BLE001
            log(f'ctf: feil {e!r}')
        finally:
            self._ctf_busy = False

    def _ctf_torch_lit(self, a):
        """Les ekte tenntilstand fra [[actor+0x270]+0xB0]+0x6C (bit 16). Returnerer (lit, raw_6c) eller (None, None)."""
        p, pad = getattr(self, 'p', None), getattr(self, 'pad', None)
        d = getattr(pad, 'delta', None)
        if not p or d is None:
            return None, None
        try:
            s2c, s30 = p.u32(a + 0x2C, 2)
            if s2c != 4 or s30 != 0:   # deaktiveres under teleportering / rom 0 – aldri tell falsk tenning
                return None, None
            p270 = struct.unpack('<Q', p.read(p.base + a + 0x270, 8))[0]
            if not p270 or not (0 < p270 - d < p.size - 0xB8):
                return None, None
            pb0 = struct.unpack('<Q', p.read(p.base + p270 - d + 0xB0, 8))[0]
            if not pb0 or not (0 < pb0 - d < p.size - 0x70):
                return None, None
            v6c = p.u32(pb0 - d + 0x6C)
            return bool(v6c & 0x10000), v6c
        except OSError:
            return None, None

    def _ctf_find_torches(self):
        """Finn basefaklene og les starttilstand fra pb0+0x6C bit 16 (ikke actor+0x480 som svinger med LOD)."""
        self._ctf_scan_busy = True
        try:
            p, pad = self.p, self.pad
            allm = {}; pad._scan_full_t = 0
            pad._scan_actors_raw(p, allm)
            current = {}
            self._ctf_lit = getattr(self, '_ctf_lit', {})
            me = pad.my_apos(p) if (p and getattr(self, 'ready', False)) else None
            in_room10 = (me is None or self._ctf_in_room(me))
            for a, nm in allm.items():
                if nm != 'Obj_CandleStick_NoGimmick_OnOff':
                    continue
                try:
                    pos = p.f32(a + 0x31C, 3)
                    team = min(self.PVP_BASES, key=lambda t: math.dist(pos, self.PVP_BASES[t]))
                    if math.dist(pos, self.PVP_BASES[team]) < 3.0:
                        current[team] = a
                        lit_now, _ = self._ctf_torch_lit(a)
                        active_lit = in_room10 and bool(lit_now)
                        self._ctf_lit.setdefault(team, active_lit)
                except OSError:
                    pass
            self._ctf_actors = current
            self._ctf_scan_t = time.time()
            log(f'ctf: fakler {current}, tent-tilstand {self._ctf_lit}')
        except Exception as e:  # noqa: BLE001
            log(f'ctf: fakkel-søk feilet {e!r}')
            self._ctf_scan_t = time.time()
        finally:
            self._ctf_scan_busy = False

    def _ctf_in_room(self, me):
        """v0.94.320: er Link inne på CTF-brettet? Gohma: under inngangshallen (y<70). Andre brett: innenfor grensene."""
        if getattr(self, '_arena_cur', 'gohma') == 'gohma':
            return me[1] < 70.0
        return not self._arena_outside(me)

    def _stal_follow(self, now):
        """v0.94.322: flytt en av spillets egne ForbidStalchildDivingArea-soner til Links posisjon (Stalchild dukker
        ikke opp inne i slike soner). Adressene fornyes av aktørryddingen hvert 1.5 s."""
        areas = getattr(self, '_stal_areas', None)
        if (not areas or self.mode != 'PvP' or not getattr(self, '_pvp_in_arena', False)
                or now - getattr(self, '_stal_t', 0) < 0.2 or now < getattr(self.pad, '_tp_t', 0) + 2.0):
            return
        self._stal_t = now
        try:
            me = self.pad.my_apos(self.p)
            if not me:
                return
            for a in areas[:2]:
                if self.pad.actor_alive(self.p, a):
                    self.p.write(self.p.base + a + 0x31C, struct.pack('<3f', me[0], me[1], me[2]))
            if now - getattr(self, '_stal_log_t', 0) > 60:
                self._stal_log_t = now
                log(f'stalchild: {min(2, len(areas))} av {len(areas)} sperresoner følger Link {[round(v, 1) for v in me]}')
        except OSError:
            pass

    def _ctf_tick(self, now):
        if (getattr(self, 'cfg', None) or {}).get('stal_follow') and self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('no_stalchild'):
            self._stal_follow(now)   # v0.94.322: testet 10:53–10:58 – hjalp ikke (Stalchild kom likevel); av som standard
        if self.mode != 'PvP' or self._game_mode != 'ctf' or not getattr(self, '_pvp_in_arena', False):
            self._ctf_reset_at = 0
            return
        if getattr(self.pad, 'cur_banc', None) != self.PVP_BANC:
            # Game Over / ekstern soneovergang ut av Deku-treet: nullstill stale arena-pekere.
            self._pvp_in_arena = False; self._ctf_reset_at = 0
            self._ctf_actors = {}; self._ctf_lit = {}; self._ctf_friend_lit = {}; self._ctf_point_sent = {}
            return
        if getattr(self, '_ctf_busy', False):
            return
        bt_ = getattr(self.pad, '_banc_since', 0)
        if (getattr(self, '_ctf_banc_t', None) is not None and bt_ and bt_ != self._ctf_banc_t
                and now - bt_ > 8.0 and not getattr(self, '_pvp_travel_busy', False)):
            # v0.94.322: Game Over lastet arenaen på nytt i samme sone – alle fakler/lys var borte
            log('ctf: arenaen ble lastet på nytt (Game Over?) – setter opp fakler og lys igjen')
            self._ctf_banc_t = None
            threading.Thread(target=self._ctf_setup, daemon=True).start()
            return
        if getattr(self, '_ctf_reset_at', 0) and now >= self._ctf_reset_at:
            self._ctf_reset_at = 0
            threading.Thread(target=self._ctf_setup, daemon=True).start()
            return
        if len(getattr(self, '_ctf_actors', {})) < 2:
            if not getattr(self, '_ctf_scan_busy', False) and now - getattr(self, '_ctf_scan_t', 0) >= 2.0:
                self._ctf_scan_t = now   # Maks én bakgrunnsskanning hvert 2. s (ingen tick-spam når {} mangler).
                threading.Thread(target=self._ctf_find_torches, daemon=True, name='CtFFindTorches').start()
            if not getattr(self, '_ctf_actors', None):
                return
        if now - getattr(self, '_ctf_tick_t', 0) < 0.20:
            return
        self._ctf_tick_t = now
        tp_t = getattr(self.pad, '_tp_t', 0)
        if tp_t and now < tp_t + CALL_TELEPORT_COOLDOWN:
            return
        me = self.pad.my_apos(self.p) if (self.p and getattr(self, 'ready', False)) else None
        if me is not None and not self._ctf_in_room(me):   # Link er fortsatt i rom 0 (ankomst/bounceback) – ikke tell fakler
            return
        self._ctf_lit = getattr(self, '_ctf_lit', {})
        self._ctf_point_sent = getattr(self, '_ctf_point_sent', {})
        friend_lit = getattr(self, '_ctf_friend_lit', {})
        remote = set((self.friend or {}).get('ctfl', []))
        for team in self.PVP_BASES:
            lit = team in remote
            was = friend_lit.get(team, False)
            friend_lit[team] = lit
            # En lokal tenning kan allerede ha gitt poeng; ikke tell samme hendelse via vennen også.
            if lit and not was and not self._ctf_lit.get(team, False):
                log(f'ctf: {team}-fakkelen ble tent (meldt av vennen)')
                self._ctf_lit[team] = True
                if self._is_ctf_score_reporter() and not getattr(self, '_ctf_point_sent', {}).get(team, False):
                    self._ctf_point_sent[team] = True
                    self._ctf_server_point(team)
        self._ctf_friend_lit = friend_lit
        for team, a in list(getattr(self, '_ctf_actors', {}).items()):
            lit, _ = self._ctf_torch_lit(a)
            if lit is None:
                continue
            was = self._ctf_lit.get(team, lit)
            self._ctf_lit[team] = lit
            if lit and not was:
                log(f'ctf: {team}-fakkelen ble tent (pb0+0x6C bit 16)')
                if self._is_ctf_score_reporter() and not getattr(self, '_ctf_point_sent', {}).get(team, False):
                    self._ctf_point_sent[team] = True   # Ny runde nullstiller sperren i _ctf_setup.
                    self._ctf_server_point(team)

    def _pvp_leave_lobby(self):
        """Story: avbryt reise og gå ut av PvP-scenen uten å beholde lobbyregler."""
        try:
            p, pad = self.p, self.pad
            self._pvp_in_arena = False; self._pvp_social_lobby = False
            self._pvp_restore_lobby_bgm(restart_market=False)
            self._ctf_actors = {}; self._ctf_lit = {}; self._ctf_friend_lit = {}; self._ctf_point_sent = {}
            deadline = time.time() + 22.0
            while getattr(self, '_pvp_travel_busy', False) and self.mode == 'Story' and time.time() < deadline:
                time.sleep(0.25)
            if self.mode != 'Story' or not (p and self.ready):
                return
            ret = getattr(self, '_story_return', None) or {}
            can_return = (pad.cur_banc == self.PVP_LOBBY_BANC
                          or (pad.cur_banc == self.PVP_BANC and ret.get('banc')
                              and ret.get('banc') not in (self.PVP_LOBBY_BANC, self.PVP_BANC)))
            if can_return:
                banc = ret.get('banc') or 'KokiriForest_Child'
                start = ret.get('start') or self.pad.START_POS.get(banc)
                if (banc == self.PVP_LOBBY_BANC
                        or not start
                        or (start == 'LostWoodBridge_FrontOfHyruleField' and banc != 'KokiriForest_Child')):
                    banc, start = 'KokiriForest_Child', 'LostWoodBridge_FrontOfHyruleField'
                r = False
                for _attempt in range(4):
                    if self.mode != 'Story':
                        return
                    while self.mode == 'Story' and time.time() < getattr(pad, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN:
                        time.sleep(0.25)
                    r = pad.change_banc(p, banc, start)
                    log(f'pvp: ut av {pad.cur_banc} til Story {banc} @ {start} -> {r}')
                    if r:
                        break
                    time.sleep(1.5)
                if r:   # «Story fullført» skal først logges når målscenen faktisk er stabil
                    deadline = time.time() + 20.0
                    while self.mode == 'Story' and time.time() < deadline:
                        if pad.cur_banc == banc and time.time() - getattr(pad, '_banc_since', 0) > 3.0:
                            break
                        time.sleep(0.25)
            elif pad.cur_banc == self.PVP_BANC and getattr(self, '_arena_cur', 'gohma') == 'gohma':
                me = pad.my_apos(p)
                if me and math.dist(me, self.PVP_ARENA_POSITIONS[0]) <= 40:
                    safe_exit = [0.2, 101.5, 18.0]   # Deku-treet hovedhall (gulv y≈101.04, vekk fra SystemTextNPC ved døra)
                    r = pad.teleport_player(p, safe_exit)
                    log(f'pvp: ut av arenaen til inngangen -> {r}')
        except Exception as e:  # noqa: BLE001
            log(f'pvp: lobby-feil {e!r}')

    def _arena_key(self):
        """v0.94.316: valgt brett – serverens lobby-felt først, ellers /cfg pvp_arena (lokal test), ellers Gohma."""
        k = getattr(self, '_arena_from_server', None) or self.cfg.get('pvp_arena') or 'gohma'
        if k not in self.ARENAS or (getattr(self, '_game_mode', 'ctf') == 'ctf' and not self.ARENAS[k].get('ctf')):
            k = 'gohma'
        return k

    def _apply_arena(self, server_arena=None):
        """Sett PVP_BANC/startplass/grenser for valgt brett (instansverdier skygger klasseverdiene)."""
        if server_arena is not None:
            self._arena_from_server = server_arena if server_arena in self.ARENAS else None
        k = self._arena_key()
        if getattr(self, '_arena_cur', 'gohma') == k and 'PVP_BANC' in self.__dict__:
            return
        a = self.ARENAS[k]
        self.PVP_BANC, self.PVP_ARENA_START = a['banc'], a['start']
        self.PVP_ARENA_POSITIONS = tuple(list(v) for v in a['positions'])
        self.PVP_ARENA_Y, self.PVP_ARENA_BOX = a['y'], a['box']
        self.PVP_BASES = {t: list(v) for t, v in (a.get('bases') or self.ARENAS['gohma']['bases']).items()}
        if getattr(self, '_arena_cur', 'gohma') != k:
            log(f"pvp: brett -> {a['name']} ({a['banc']})")
            try:
                self._append_chat_sys(f"🗺️ Arena: {a['name']}")
            except Exception:  # noqa: BLE001
                pass
        self._arena_cur = k

    def _rock_leader(self):
        """Hvem styrer kula: spilleren med lavest sesjon (samme regel som startplass 0). Uten venn: meg."""
        fs = (self.friend or {}).get('s') if self.friend else None
        return not (fs is not None and fs < getattr(self, 'session', 0))

    def _rock_tick(self, now):
        """v0.94.316: sverd-banens rullende kule synket. Lederen sender kulas matrise + fart (state-feltet «rock»);
        de andre skriver den (med fart-framskriving) inn i sin egen kule. Treff tas av hvert spill selv (livvakta i PvP
        setter tilbake HP, så kula slår over ende uten å ta liv)."""
        a = self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {})
        name = a.get('rock')
        p, pad = self.p, self.pad
        if (not name or getattr(self, 'mode', 'Story') != 'PvP' or not getattr(self, '_pvp_in_arena', False) or not p
                or pad.cur_banc != a.get('banc') or now - getattr(pad, '_banc_since', now) < 10.0
                or now < getattr(pad, '_tp_t', 0) + 8.0):
            self._my_rock = None
            return
        st = self.__dict__.setdefault('_rock', {})
        zk = (id(p), pad.cur_banc, getattr(pad, '_banc_since', 0))
        if st.get('zone') != zk:
            st.clear(); st['zone'] = zk
        if not st.get('act'):
            if now - st.get('scan_t', 0) < 3.0:
                return
            st['scan_t'] = now
            found = pad._list_actors_raw(p, prefix=name) or {}
            for act in found:
                x8 = pad.actor_x8(p, act)
                if x8:
                    st['act'], st['x8'] = act, x8
                    log(f'kule: fant {name} @0x{act:X} pos {[round(v, 1) for v in found[act][1]]} – '
                        f"{'jeg styrer den' if self._rock_leader() else 'følger vennens kule'}")
                    break
            if not st.get('act'):
                return
        act, x8 = st['act'], st['x8']
        if not pad.actor_alive(p, act):
            st.pop('act', None); return
        h = p.base + x8 + 0x1D0
        # v0.94.318: lederen må ha en kule som er på banen. Ligger egen kule utenfor (ødelagt), følg vennen – det reparerer
        # den. Sender vennen ingen kule på 2 s (vennens er ødelagt), ta over.
        mine = p.f32(act + 0x31C, 3)
        ok_mine = bool(mine) and not self._arena_outside(mine)
        fr0 = (self.friend or {}).get('rock')
        if isinstance(fr0, list) and len(fr0) == 15:
            st['fr_seen_t'] = now
        lead = self._rock_leader()
        if not ok_mine:
            lead = False
        elif not lead and now - st.get('fr_seen_t', now - 99) > 2.0:
            lead = True
        if lead != st.get('lead'):
            st['lead'] = lead
            log(f"kule: {'jeg styrer kula' if lead else 'følger vennens kule'} (egen kule {'på banen' if ok_mine else 'utenfor'}: "
                f"{[round(v, 1) for v in mine] if mine else None})")
        if lead:
            # v0.94.318: aktørens egen posisjon/rotasjon (+0x31C/+0x328). Fysikk-kroppens matrise (x8+0x1D0) var tom
            # for kula (0,0,0) – følgeren flyttet da sin kule til origo.
            pos = p.f32(act + 0x31C, 3); r9 = p.f32(act + 0x328, 9)
            if not pos or abs(pos[0]) + abs(pos[1]) + abs(pos[2]) < 1.0:
                self._my_rock = None
                return
            m = (r9[0], r9[1], r9[2], pos[0], r9[3], r9[4], r9[5], pos[1], r9[6], r9[7], r9[8], pos[2])
            prev = st.get('prev')
            vel = ([(pos[i] - prev[1][i]) / (now - prev[0]) for i in range(3)]
                   if prev and 0.01 < now - prev[0] < 0.5 else [0.0, 0.0, 0.0])
            st['prev'] = (now, pos)
            self._my_rock = [round(v, 3) for v in m] + [round(v, 2) for v in vel]
            return
        self._my_rock = None
        fr = (self.friend or {}).get('rock')
        if (not isinstance(fr, list) or len(fr) != 15 or now - getattr(self, 'friend_t', 0) > 1.0
                or pad.friend_banc != pad.cur_banc):
            if now - st.get('why_t', 0) > 15:
                st['why_t'] = now
                log(f"kule: følger ikke – vennens kule={type(fr).__name__}{'/' + str(len(fr)) if isinstance(fr, list) else ''} "
                    f"alder={now - getattr(self, 'friend_t', 0):.1f}s sone venn={pad.friend_banc} meg={pad.cur_banc} "
                    f"nøkler={sorted((self.friend or {}).keys())[:60]}")
            return
        dt = min(0.25, max(0.0, now - getattr(self, '_rock_rx_t', now)))
        if fr is not st.get('last_fr'):
            st['last_fr'] = fr; self._rock_rx_t = now; dt = 0.0
        m = [float(v) for v in fr[:12]]
        m[3] += fr[12] * dt; m[7] += fr[13] * dt; m[11] += fr[14] * dt
        if not all(math.isfinite(v) and abs(v) < 1e5 for v in m) or abs(m[3]) + abs(m[7]) + abs(m[11]) < 1.0:
            return
        # v0.94.319: myk korreksjon. Egen kule fortsetter å rulle selv; vi trekker den en brøkdel mot vennens posisjon
        # hvert tick i stedet for å hoppe dit (det hakket når kulene kom ut av takt). Bare stort avvik (>ROCK_SNAP m) hopper.
        cur = struct.unpack('<3f', p.read(p.base + act + 0x31C, 12))
        err = (m[3] - cur[0], m[7] - cur[1], m[11] - cur[2])
        d = math.sqrt(err[0] ** 2 + err[1] ** 2 + err[2] ** 2)
        snap = d > self.ROCK_SNAP
        if d < 0.03:
            pass
        elif snap:
            st['snaps'] = st.get('snaps', 0) + 1
            body = struct.unpack('<12f', p.read(h, 48))
            if abs(body[3]) + abs(body[7]) + abs(body[11]) > 1.0:   # bare hvis kroppen faktisk bærer posisjonen
                p.write(h, struct.pack('<12f', *m))
                w = struct.unpack('<I', p.read(p.base + x8 + 0x228, 4))[0]
                p.write(p.base + x8 + 0x228, struct.pack('<I', w | 7))
            p.write(p.base + act + 0x31C, struct.pack('<3f', m[3], m[7], m[11]))
            p.write(p.base + act + 0x328, struct.pack('<9f', m[0], m[1], m[2], m[4], m[5], m[6], m[8], m[9], m[10]))
        else:
            k = self.ROCK_PULL
            p.write(p.base + act + 0x31C, struct.pack('<3f', cur[0] + err[0] * k, cur[1] + err[1] * k, cur[2] + err[2] * k))
        st['err_max'] = max(st.get('err_max', 0.0), d)
        if now - st.get('log_t', 0) > 30:
            st['log_t'] = now
            mine = struct.unpack('<3f', p.read(p.base + act + 0x31C, 12))
            log(f'kule: følger vennens kule ({m[3]:.1f}, {m[7]:.1f}, {m[11]:.1f}), egen nå {[round(v, 1) for v in mine]}'
                f" – største avvik {st.get('err_max', 0.0):.2f} m, hopp {st.get('snaps', 0)} siste 30 s")
            st['err_max'] = 0.0; st['snaps'] = 0

    def _arena_outside(self, me):
        """Utenfor brettets grenser (høyde, og for sverd-banen et x/z-rektangel)?"""
        y0, y1 = getattr(self, 'PVP_ARENA_Y', (40.0, 65.0))
        if not y0 < me[1] < y1:
            return True
        box = getattr(self, 'PVP_ARENA_BOX', None)
        return bool(box) and not (box[0] < me[0] < box[1] and box[2] < me[2] < box[3])

    def _pvp_early_exit(self, now):
        """Ta PvP-spilleren ut før native bossdør kan vise «Cannot exit right now».
        Utgangen armes først inne i rommet slik at arena-spawn ved x≈7 ikke utløser den."""
        # v0.94.315: av som standard. Den kastet spilleren ut ved døra og gjeninngangen hentet ham rett inn igjen (sett 14:33).
        # «Cannot exit»-meldingen kommer ikke lenger: SystemTextNPC fjernes i PvP-arenaen. Slå på med /cfg pvp_early_exit true.
        if not self.cfg.get('pvp_early_exit', False) or getattr(self, '_arena_cur', 'gohma') != 'gohma':
            return False
        if (getattr(self, '_pvp_travel_busy', False)
                or getattr(self.pad, 'cur_banc', None) != self.PVP_BANC
                or now - getattr(self, '_pvp_exit_t', 0) <= 5.0):
            return False
        try:
            me = self.pad.my_apos(self.p)
            if not me:
                return False
            in_room = 40 < me[1] < 65 and 55 < me[2] < 80
            if not in_room:
                self._pvp_exit_armed = False
                return False
            if me[0] > 10.0:
                self._pvp_exit_armed = True
            # Etter første utgang er _pvp_in_arena False. En senere fysisk gjeninngang
            # må derfor fortsatt kunne bruke utgangen, selv om arming ikke har skjedd.
            if me[0] < 8.0 and (getattr(self, '_pvp_exit_armed', False)
                                or not getattr(self, '_pvp_in_arena', False)):
                self._pvp_exit_t = now; self._pvp_in_arena = False; self._pvp_exit_armed = False
                result = self.pad.teleport_player(self.p, self.PVP_EXIT)
                log(f'pvp: tidlig egen utgang før Cannot exit-meldingen -> {result}')
                self._append_chat_sys('🚪 Left the PvP arena')
                return result
        except Exception as e:  # noqa: BLE001
            log(f'pvp: utgang feilet {e!r}')
        return False

    def _pvp_tick(self, now):
        """v0.73 PvP: fiender i nærheten på AI-pause, mål-patch av, startpunkt, poeng."""
        if getattr(self, 'mode', 'Story') != 'PvP' or not (self.p and self.ready):
            self._counter_set_open(False)
            self._pvp_hp_shadow = None
            self._pvp_restore_lobby_bgm(restart_market=bool(self.p and self.ready and getattr(self.pad, 'cur_banc', None) == self.PVP_LOBBY_BANC), async_worker=True)
            if getattr(self, '_pvp_held', None):
                self._pvp_held = None
                self.pad.set_ai_hold(self.p, []) if self.p else None
                log('pvp: av – fiende-pause opphevet')
            return
        try:   # v0.94.88: kjør hvert tick (~20 Hz) for å hindre miljøskade/fall fra å senke PvP-liv til 0.
            pc_, _pm_ = self.pad._player_sv(self.p)
            if pc_ is not None:
                cur_hp = self.p.u32(pc_)
                shadow = getattr(self, '_pvp_hp_shadow', None)
                if shadow is None and cur_hp >= 1:
                    self._pvp_hp_shadow = cur_hp
                    shadow = cur_hp
                down = now < getattr(self, '_pvp_down_until', 0)
                want = 1 if down else (shadow if (shadow is not None and shadow >= 4) else 1)
                if cur_hp < want:
                    self.p.write(self.p.base + pc_, struct.pack('<I', want))
                    if now - getattr(self, '_pvp_hp_guard_log', 0) > 2.0:
                        self._pvp_hp_guard_log = now
                        log(f'pvp: livvakt gjenopprettet ikke-PvP skade {cur_hp} -> {want}')
        except Exception:  # noqa: BLE001
            pass
        if self._game_mode == 'ctf':
            self._ctf_tick(now)
        try:
            self._rock_tick(now)
        except Exception as e:  # noqa: BLE001
            if now - getattr(self, '_rock_err_t', 0) > 10:
                self._rock_err_t = now; log(f'kule: feil {e!r}')
        if now - getattr(self, '_pvp_hit_t', 0) > 0.1:
            self._pvp_hit_t = now
            self._pvp_early_exit(now)
            self._apply_friend_hits()   # Bruker egen PvP-teller; Story bruker fortsatt fiendeskade via l2d.
            self._pvp_swing(now)   # Begge rapporterer kun egne treff – også gjestens slag må telles.
            self._pvp_inv_watch(now)
            self._counter_tick(now)
            self._pvp_sync_lobby_bgm(now=now, async_worker=True)
            if getattr(self, '_pvp_in_arena', False) and now - getattr(self, '_pvp_ammo_t', 0) > 1.0 and getattr(self, 'rupees', None):   # v0.94.13: uendelig pinner og frø i PvP-arenaen
                self._pvp_ammo_t = now
                try:
                    pp, off = self.p, self.rupees.off
                    for rel, cap_rel, dflt in ((0x938, 0x208, 10), (0x910, 0x1E0, 30)):
                        cap = pp.u32(off + cap_rel)
                        cap = cap if 0 < cap <= 99 else dflt
                        if pp.u32(off + rel) < cap:
                            pp.write(pp.base + off + rel, struct.pack('<I', cap))
                except Exception:  # noqa: BLE001
                    pass
            if getattr(self, '_pvp_in_arena', False):   # v0.94.6: sperre foran døra (vest, x < 3) – før «Cannot exit» rekker å komme
                try:
                    me_ = self.pad.my_apos(self.p)
                    sp = getattr(self, '_pvp_spawn', None)
                    if False and me_ and sp and me_[0] < 3.0:   # v0.94.22: døra skal være åpen i PvP (ingen sperre)
                        self._pvp_door_t = now
                        self.pad.teleport_player(self.p, [sp[0] + 1.0, sp[1], sp[2]])
                        log(f'pvp: for nær døra {[round(v, 1) for v in me_]} – tilbake')
                except Exception:  # noqa: BLE001
                    pass
            if getattr(self, '_pvp_in_arena', False):   # v0.85: spillet låser bossdørene igjen (ShutIn) – hold dem åpne i lobbyen
                try:
                    pd = self.pad
                    if getattr(pd, 'h_bools', None) is None:
                        pd.read_bools(self.p)   # v0.90: flagg-ticken er av i PvP – finn tabellen her
                    if getattr(pd, 'h_bools', None) is not None:
                        for i in ((8595, 8594) + tuple(self.cfg.get('pvp_flags', [10771, 11111, 11139, 10848]))
                                  if self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('boss_door', True) else ()):   # v0.94.23: dør + valgbare boss-flagg (finn hvilket som gir «Cannot exit»)
                            b = self.p.read(self.p.base + pd.h_bools + i * 0x18 + 0x16, 1)
                            if b and b[0]:
                                pd.clear_bool(self.p, i)
                                if now - getattr(self, '_pvp_door_log', 0) > 10:
                                    self._pvp_door_log = now; log(f'pvp: spillet låste bossdøra (flagg {i}) – åpnet igjen')
                except Exception:  # noqa: BLE001
                    pass
        if now - getattr(self, '_pvp_t', 0) < 2.0:
            return
        self._pvp_t = now
        p, pad = self.p, self.pad
        if getattr(self, '_pvp_social_lobby', False) and pad.cur_banc == self.PVP_LOBBY_BANC:
            me_ = pad.my_apos(p)
            sp = getattr(self, '_pvp_spawn', None)
            if (me_ and sp and math.dist(me_, self.PVP_LOBBY_CENTER) > self.PVP_LOBBY_RADIUS
                    and now - getattr(self, '_pvp_back_t', 0) > 3.0 and now - getattr(pad, '_tp_t', 0) > 3.0):
                self._pvp_back_t = now
                log(f'pvp: utenfor Bombchu safe zone {[round(v, 1) for v in me_]} – tilbake -> {pad.teleport_player(p, sp)}')
        if getattr(self, '_pvp_in_arena', False) and pad.cur_banc == self.PVP_BANC:
            me_ = pad.my_apos(p)
            if me_ and self._arena_outside(me_):
                sp = getattr(self, '_pvp_spawn', None)
                if sp and now - getattr(self, '_pvp_back_t', 0) > 3.0 and now - getattr(pad, '_tp_t', 0) > 3.0:
                    self._pvp_back_t = now
                    log(f'pvp: utenfor arenaen {[round(v, 1) for v in me_]} – tilbake -> {pad.teleport_player(p, sp)}')
        if (not getattr(self, '_pvp_lobby_done', False) and not getattr(self, '_pvp_travel_busy', False)
                and now >= getattr(self, '_pvp_travel_retry', 0) and now - getattr(self, '_pvp_lobby_try_t', 0) > 5.0
                and pad.p_act is not None and pad.cur_banc and now - getattr(pad, '_banc_since', 0) > 8.0):
            self._pvp_lobby_try_t = now
            threading.Thread(target=self._pvp_go_lobby, daemon=True, name='AutoLobby').start()
        me = pad.my_apos(p)
        if me and getattr(self, '_pvp_spawn', None) is None:
            self._pvp_spawn = list(me); log(f'pvp: startpunkt {[round(v, 1) for v in me]}')
        fm = (self.friend or {}).get('mode')
        if fm and fm != 'PvP' and now - getattr(self, '_pvp_warn', 0) > 20:
            self._pvp_warn = now; self._append_chat_sys('⚠️ Your friend is not in PvP mode')
        try:
            if pad.hR is not None:
                p.write(p.base + pad.hR + pad.TARGET_MBOX_R, struct.pack('<Q', 0))   # fiender velger ikke Link 2
        except OSError:
            pass
        in_lobby = bool(getattr(self, '_pvp_social_lobby', False) and pad.cur_banc == self.PVP_LOBBY_BANC)
        if getattr(self, '_pvp_scan_busy', False) and now - getattr(self, '_pvp_scan_t', 0) > 25.0:
            log('pvp: aktørrydding hang i over 25 s – starter på nytt'); self._pvp_scan_busy = False
        if getattr(self, '_pvp_in_arena', False) and now - getattr(self, '_pvp_scan_why_t', 0) > 30 and now - getattr(self, '_pvp_scan_t', 0) > 20:
            self._pvp_scan_why_t = now
            log(f"pvp: aktørrydding venter – banc={pad.cur_banc}/{self.PVP_BANC} me={bool(me)} spawning={getattr(pad, '_spawning', False)} "
                f"tun={getattr(pad, '_tun_busy', False)} busy={getattr(self, '_pvp_scan_busy', False)} "
                f"banc_age={now - getattr(pad, '_banc_since', 0):.0f} tp_age={now - getattr(pad, '_tp_t', 0):.0f}")
        if (((getattr(self, '_pvp_in_arena', False) and pad.cur_banc == self.PVP_BANC) or in_lobby)
                and now - getattr(self, '_pvp_scan_t', 0) > (1.5 if (not in_lobby and self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('clear_radius', 0) > 200) else 5.0) and me
                and not getattr(pad, '_spawning', False) and not getattr(pad, '_tun_busy', False)
                and not getattr(self, '_pvp_scan_busy', False)
                and now - getattr(pad, '_banc_since', 0) > 10.0 and now - getattr(pad, '_tp_t', 0) > 8.0):
            self._pvp_scan_t = now
            def run():
                # Arenaen: fiender, NPC-er og triggere. Lobby/by (v0.94.98): bare NPC-er, unntatt butikk-NPC-en på bordet.
                generation = getattr(self, '_mode_generation', 0)
                def cancelled():
                    return (generation != getattr(self, '_mode_generation', 0) or self.mode != 'PvP'
                            or not (getattr(self, '_pvp_social_lobby', False) if in_lobby else getattr(self, '_pvp_in_arena', False)))
                try:
                    if cancelled():
                        return
                    allm = {}; pad._scan_full_t = 0
                    found = pad._scan_actors_raw(p, allm) or {}
                    allm.update({a_: v_[0] for a_, v_ in found.items()})   # Enemy_* kommer i returverdien, Npc_* i _diag_all
                    if not in_lobby and self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('no_stalchild'):
                        # v0.94.322: spillets egne «ingen Stalchild»-soner – én følger Link (se _stal_follow)
                        self._stal_areas = sorted(a_ for a_, n_ in allm.items() if n_ == 'ForbidStalchildDivingArea')
                    gone = self.__dict__.setdefault('_pvp_gone', set())
                    if False and in_lobby and self.PVP_VENDOR not in allm.values() and time.time() - getattr(self, '_vendor_try', 0) > 20:   # av: tegnes ikke
                        self._vendor_try = time.time()
                        r_ = pad.create_actor(p, self.PVP_VENDOR, self.PVP_SHOP_POS)
                        log(f'pvp: laget butikk-NPC {self.PVP_VENDOR} ved {self.PVP_SHOP_POS} -> {r_}')
                    n = 0
                    for a, nm in sorted(allm.items()):
                        if cancelled():
                            log('pvp: aktørrydding avbrutt ved modusbytte')
                            return
                        trig = nm in ('Area', 'EventRequestActor', 'Dm_Locator', 'Obj_WarpPoint_A_01', 'Obj_Heart_Container', 'SystemTextNPC')   # v0.94.30: cutscene-triggere og bossrester
                        if not (nm.startswith('Enemy_') or nm.startswith('Npc_') or trig) or nm == 'Npc_Navi' or (a in gone and not nm.startswith('Enemy_')):   # v0.94.322: ny fiende kan få samme adresse (Stalchild)
                            continue
                        if in_lobby and not nm.startswith('Npc_'):
                            continue
                        if in_lobby and (nm in self.PVP_SHOP_NAMES or self._shop_near(p, a)):
                            if nm == 'Npc_Hylia_038_Child':
                                try:
                                    # Spillet setter henne inaktiv (status 5) selv om modellen finnes.
                                    if p.u32(a + 0x2C) != 4 and pad.actor_x8(p, a):
                                        p.write(p.base + a + 0x2C, struct.pack('<I', 4))
                                        log('pvp: butikk-NPC 038 vekket')
                                except OSError:
                                    pass
                            kept = self.__dict__.setdefault('_shop_kept', set())
                            if nm not in kept:
                                kept.add(nm)
                                log(f'pvp: butikk-NPC beholdt: {nm}')
                            gone.add(a)
                            continue
                        if False:
                            continue
                        if 'Egg' in nm or 'Larva' in nm:   # Gohma-unger: skjules ikke ved sletting i løkke – ta dem til slutt
                            pass
                        try:
                            pos = p.f32(a + 0x31C, 3)
                            if math.dist(pos, me) > (400 if in_lobby else self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('clear_radius', 120)):   # lobby = hele byen
                                continue
                        except OSError:
                            continue
                        gone.add(a)
                        r = pad.delete_actor(p, a)
                        if not r:   # v0.94.322: mislykket sletting (f.eks. Peahat-larve -> 0) – prøv igjen neste runde
                            gone.discard(a)
                            if nm.startswith('Enemy_') and self._pvp_bury(p, a, nm):
                                gone.add(a)
                        log(f'pvp: fjernet {nm} -> {r}')
                        n += 1
                        if n >= (6 if in_lobby or self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('clear_radius', 0) <= 200 else 25):   # v0.94.322: feltet – Stalchild dukker opp hele tiden om natta
                            break
                except Exception as e:  # noqa: BLE001
                    log(f'pvp: feil {e!r}')
                finally:
                    self._pvp_scan_busy = False
            self._pvp_scan_busy = True
            threading.Thread(target=run, daemon=True).start()

    PVP_SHOP_NPC = 'Npc_Hylia_038_Child'   # (navnet stemte ikke – se PVP_SHOP_POS)
    PVP_SHOP_NAMES = (
        'Npc_Hylia_082_Child',          # jenta på bordet; modellen hennes kan mangle (ingen transform)
        'Npc_Hylia_038_Child',          # samme bord, har modell, spillet setter henne inaktiv
        'Npc_Hylia_067_Shop_Child',     # synlig butikk-NPC ved disken, like utenfor 4 m
    )
    PVP_VENDOR = 'CoopVendor_Hylia'   # romfs-aktør bygget av tools/tunic_pack.py (kopi av Npc_Hylia_082_Child)
    PVP_SHOP_POS = (-28.0, 100.3, 14.3)   # midt i NPC-klyngen ved bordet
    PVP_SHOP_RANGE = 3.5
    PVP_COUNTER = (
        ('sticks', 'Sticks', 10, 5),
        ('nuts', 'Nuts', 15, 5),
        ('seeds', 'Seeds', 10, 10),
        ('bombs', 'Bombs', 30, 5),
        ('potion', 'Potion', 25, 1),
    )
    RED_POTION = 0xEABA6067
    PVP_POUCH = (('bombs', 0x708), ('bombbag', 0x780), ('potion_num', 0x550))

    def _death_tick(self, now):
        """Story deler dødsanimasjon; PvP bruker kun egen 5-sekunders knockout/respawn."""
        if getattr(self, 'mode', 'Story') == 'PvP':
            self._my_death_an = None
            self._death_want = None   # En venn som er knockout skal ikke drepe/låse vår Link 2.
            return
        if now - getattr(self, '_death_t', 0) < 0.25 or not (self.p and self.ready):
            return
        self._death_t = now
        p, pad = self.p, self.pad
        # egen død: send animasjonsnavnet (Die, LandDead, Die_Lava …)
        mh = getattr(self, '_my_hearts_last', None)
        if mh and mh[0] == 0 and pad.p_act is not None:
            try:
                self._my_death_an = pad.read_anim(p, pad.p_act)[0]
            except Exception:  # noqa: BLE001
                self._my_death_an = None
        else:
            self._my_death_an = None
        fr = self.friend or {}
        fh = fr.get('hearts')
        dead = bool(self.friend and now - self.friend_t < 2 and isinstance(fh, list) and fh and fh[0] == 0)
        if dead and pad.c_act is not None:
            want = fr.get('dan') or 'Die'
            if 'Die' not in want and 'Dead' not in want:
                want = getattr(self, '_death_want', None) or 'Die'
            try:
                cur = pad.read_anim(p, pad.c_act)[0]
            except Exception:  # noqa: BLE001
                cur = None
            if cur != want and now - getattr(self, '_death_play_t', 0) > 1.0:
                self._death_play_t = now
                r = pad.play_anim(p, pad.c_act, want)
                if want != getattr(self, '_death_want', None):
                    log(f'død: vennen døde – Link 2 spiller {want} (var {cur}) -> {r}')
                    self._append_chat_sys(f'💀 {fr.get("name", "Friend")} is down!')
            self._death_want = want
        elif getattr(self, '_death_want', None):
            log('død: vennen lever igjen'); self._death_want = None

    def _weapon_name_for_slot(self, slot):
        """Navnet på våpenet i en slot, hvis stykkets egen navn-peker ikke kan leses.

        På noen PC-er (peeren) ligger stykkets navn-peker utenfor hovedheapen, så
        actor_piece_name gir None. Da tar vi navnet fra våpen-aktørene som henger
        på min egen Link (wa_m) i stedet – samme streng som sendes i 'wp'.
        """
        pref = {0: 'Weapon_Sword', 4: 'Weapon_Shield'}.get(slot)
        if not pref:
            return None
        for nm in sorted(getattr(self, '_wp_addr_me', {}) or {}):
            if nm.startswith(pref) and 'Sheath' not in nm:
                return nm
        return None

    def _own_equip_states(self, p, now):
        """Spillets egen tilstand for min egen Links sverd (slot 0) og skjold (slot 4).

        Returnerer {slot: (tilstand, navn)} der 1 = i hånda, 2 = vekk, 0 = tomt.

        v0.94.151: aktørens egen tilstand (+0x2C = 4) betyr bare "til stede" og
        kan ikke skille sverd i hånda fra sverd på ryggen, så den gamle
        heuristikken i _weapon_tick tok feil. Her spilles spillets egen lesing
        (0xCE7AB0), én slot per kall (round-robin) som i coop-modens egen
        Director::OwnState.
        """
        eq = self.__dict__.setdefault('_own_eq_states', {})
        if now < getattr(self, '_eq_pause_t', 0) or now - getattr(self, '_own_eq_t', 0) < 1.0 or not (self.p and self.ready):
            return eq
        self._own_eq_t = now
        pad = self.pad
        if pad.p_act is None:
            return eq
        slots = (0, 4, 5)
        idx = getattr(self, '_own_eq_i', 0) % len(slots)
        slot = slots[idx]
        self._own_eq_i = idx + 1
        st = pad.actor_equip_state_read(p, pad.p_act, slot)
        if st is None:
            self._eq_pause_t = now + 15.0
            self._gear_pause_t = max(getattr(self, '_gear_pause_t', 0), now + 15.0)
            return eq
        piece, _sid = pad.actor_equip_slot(p, pad.p_act, slot)
        nm = pad.actor_piece_name(p, piece) if piece else None
        if not nm:
            nm = self._weapon_name_for_slot(slot)
        old = eq.get(slot)
        eq[slot] = (int(st), nm)
        if not old or old[0] != int(st):
            log(f'egen utstyr: slot {slot} ({nm!r}) er '
                f'{"i hånda" if int(st) == 1 else "vekk" if int(st) == 2 else "tombort"}')
        return eq

    def _weapon_tick(self, now):
        """Måler (bare lesing): hvilke våpen-aktører som henger på min Link og på Link 2. Logger endringer."""
        if now - getattr(self, '_wp_t', 0) < 0.3 or not (self.p and self.ready):
            return
        self._wp_t = now
        p, pad = self.p, self.pad
        ws = getattr(pad, '_weapons', None)
        me = pad.my_apos(p)
        if not ws or not me:
            return
        try:
            l2 = p.f32(pad.c_act + 0x31C, 3) if pad.c_act is not None else None
        except OSError:
            l2 = None
        mine, theirs = [], []; wa_m, wa_2 = {}, {}
        for a, (nm, t) in list(ws.items()):
            if now - t > 20.0:
                ws.pop(a, None); continue
            try:
                pos = p.f32(a + 0x31C, 3)
            except OSError:
                continue
            dm = math.dist(pos, me); d2 = math.dist(pos, l2) if l2 else 1e9
            if min(dm, d2) > 2.5:
                continue
            (mine if dm <= d2 else theirs).append(nm)
            (wa_m if dm <= d2 else wa_2)[nm] = a
        mine.sort(); theirs.sort()
        # Aktiv ting (Link+0x1D8: f.eks. 11 = Deku-pinne, 12 = sprettert) – sendes, og vennens settes på Link 2
        try:
            self._my_item = struct.unpack('<I', p.read(p.base + pad.p_act + 0x1D8, 4))[0] if pad.p_act is not None else None
            fit = (self.friend or {}).get('it')
            pad.friend_item = fit if (self.friend and now - self.friend_t < 2) else None
            if False and isinstance(fit, int) and 0 < fit < 64 and pad.c_act is not None:
                cur_it = struct.unpack('<I', p.read(p.base + pad.c_act + 0x1D8, 4))[0]
                if cur_it != fit and cur_it < 64:
                    p.write(p.base + pad.c_act + 0x1D8, struct.pack('<I', fit))
                    if now - getattr(self, '_it_log', 0) > 2:
                        self._it_log = now; log(f'ting: satte Link 2 sin aktive ting {cur_it} -> {fit}')
        except OSError:
            pass
        self._wp_addr_me, self._wp_addr_l2 = wa_m, wa_2
        dr = []
        wd = []
        for nm, a in wa_m.items():
            try:
                st = struct.unpack('<I', p.read(p.base + a + 0x2C, 4))[0]
            except OSError:
                continue
            if 'DekuStick' in nm or 'SlingShot' in nm:
                if st == 4:
                    dr.append(nm)
        # v0.94.151: sverd/skjold – spillets egen tilstandslesing (0xCE7AB0).
        # Aktørens tilstand 4 betyr bare "til stede", så den gamle testen
        # (st == 4) kunne ikke skille sverd i hånda fra sverd på ryggen.
        own = self._own_equip_states(p, now)
        for slot in (0, 4):
            st, nm = own.get(slot, (0, None))
            if st == 1 and nm:
                wd.append(nm)   # sverd/skjold i hånda (spillets egen tilstand)
        self._my_drawn = dr or None
        self._my_wdrawn = wd or None
        prev_dr = getattr(self, '_dr_prev', [])
        db = self.__dict__.setdefault('_draw_btn', dict(self.cfg.get('draw_btn', {})))
        if dr != prev_dr:
            log(f'ting: framme hos meg {dr} (knapper sist: {[(round(now - t, 2), hex(b)) for t, b in getattr(pad, "_btn_hist", [])[-4:]]})')
        for nm in dr:
            if nm not in prev_dr:           # nettopp tatt fram: hvilken knapp ble trykket rett før?
                cand = [b for t, b in getattr(pad, '_btn_hist', []) if now - t < 0.8 and b & ~0x3]
                if cand:
                    bit = cand[-1] & ~0x3
                    bit = bit & -bit        # laveste bit
                    if db.get(nm) != bit:
                        db[nm] = bit; self.cfg['draw_btn'] = db; save_cfg(self.cfg)
                        log(f'ting: lærte at {nm} tas fram med knapp 0x{bit:X}')
        self._dr_prev = dr
        l2dr = []
        for nm, a in wa_2.items():
            if 'DekuStick' in nm or 'SlingShot' in nm:
                try:
                    if struct.unpack('<I', p.read(p.base + a + 0x2C, 4))[0] == 4:
                        l2dr.append(nm)
                except OSError:
                    pass
        pad.l2_drawn = l2dr
        # Vis på Link 2 det vennen har framme (bare utseende: +0x2C 4 = i hånda, 6 = gjemt; +0x30 = skjult-flagg)
        fdr = (self.friend or {}).get('dr') if (self.friend and now - self.friend_t < 2) else None
        fdr = fdr or []
        forced = self.__dict__.setdefault('_wp_forced', set())
        for nm, a in wa_2.items():
            if not ('DekuStick' in nm or 'SlingShot' in nm):
                continue
            want = nm in fdr
            continue   # av: bryteren alene viser ikke tingen i hånda
            try:
                st = struct.unpack('<2I', p.read(p.base + a + 0x2C, 8))
                if want and st != (4, 0):
                    p.write(p.base + a + 0x2C, struct.pack('<2I', 4, 0)); forced.add(a)
                    log(f'ting: viser {nm} på Link 2 (vennen har den framme)')
                elif not want and a in forced and st == (4, 0):
                    p.write(p.base + a + 0x2C, struct.pack('<2I', 6, 1)); forced.discard(a)
                    log(f'ting: gjemmer {nm} på Link 2')
            except OSError:
                pass
        if now - getattr(self, '_wp_dump', 0) > 10:
            self._wp_dump = now
            try:
                json.dump({'me': wa_m, 'l2': wa_2, 'hR': pad.hR, 'delta': pad.delta, 'p_act': pad.p_act, 'c_act': pad.c_act}, open(os.path.join(APP_DIR, 'logs', f'weapons_{PC}.json'), 'w'))
            except OSError:
                pass
        self._my_wp = mine
        if mine != getattr(self, '_wp_mine', None):
            self._wp_mine = mine; log(f'våpen: min Link har {mine}')
        if theirs != getattr(self, '_wp_l2', None):
            self._wp_l2 = theirs; log(f'våpen: Link 2 har {theirs}')
        fw = (self.friend or {}).get('wp')
        if fw is not None and fw != getattr(self, '_wp_friend', None):
            self._wp_friend = fw; log(f'våpen: vennen sier hans Link har {fw}')

    def _navi_tick(self, now):
        """v0.94.114: ekstra Navi til speil-Linken er av. Spawn og flytting hang spilltråden.
        Spillerens egen Navi er spillets og røres ikke."""
        if not getattr(self, '_nv_off_logged', False):
            self._nv_off_logged = True
            log('navi: ekstra fe er av (spawn og flytting hang spillet)')
        self._navi2 = None
        if getattr(self.pad, 'navi2', None) is not None:
            self.pad.navi2 = None

    EQUIP_IDX = (59, 65, 68, 74)   # item-knappene i enum-tabellen (verdi = navnekode for tingen)

    def _equip_tick(self, now):
        """Hver sitt knappeoppsett. Vi sender vårt (de 4 knappe-postene); PadLink-løkka låner vennens kort mens Link 2 bruker en ting."""
        if now - getattr(self, '_eq_t', 0) < 0.25 or not (self.p and self.ready):
            return
        self._eq_t = now
        p, pad = self.p, self.pad
        he = getattr(pad, 'h_enum', None)
        if he is None:
            pad.read_door(p); return
        try:
            ok = all(struct.unpack('<I', p.read(p.base + he + k * 0x38 + 0x28, 4))[0] == 0x37 for k in self.EQUIP_IDX)
            cur = [struct.unpack('<I', p.read(p.base + he + k * 0x38 + 0x1C, 4))[0] for k in self.EQUIP_IDX]
        except OSError:
            return
        if not ok:
            if now - getattr(self, '_eq_warn', 0) > 60:
                self._eq_warn = now; log('knapper: fant ikke knappe-postene (uventet tabell)')
            pad.eq_ok = False
            return
        pad.eq_ok = True; pad.eq_idx = self.EQUIP_IDX
        # Delt knappeoppsett: den som byttet sist bestemmer for begge
        prev = getattr(self, '_eq_prev', None)
        if prev is not None and cur != prev and cur != getattr(self, '_eq_wrote', None):
            self._eq_ver = getattr(self, '_eq_ver', 0) + 1
            log(f'knapper: du byttet {prev} -> {cur}')
        self._eq_prev = cur
        self._my_eq = cur
        self._my_eqv = getattr(self, '_eq_ver', 0)
        fresh = bool(self.friend and now - self.friend_t < 2)
        fe = (self.friend or {}).get('eq') if fresh else None
        fv = (self.friend or {}).get('eqv') if fresh else None
        pad.friend_eq = None   # lån er av – oppsettet deles i stedet
        frb = (self.friend or {}).get('rb') if fresh else None
        if isinstance(frb, int):
            if getattr(self, '_rb_seen', None) is not None and frb > self._rb_seen:
                self._do_resetboss()
            self._rb_seen = frb
        if fe and len(fe) == len(self.EQUIP_IDX) and fe != cur and all(isinstance(v, int) for v in fe):
            last_fv = getattr(self, '_eq_fv', None)
            first = last_fv is None and not self._time_host()      # ved oppstart: gjesten tar vertens oppsett
            if first or (last_fv is not None and fv != last_fv):
                try:
                    for k, v in zip(self.EQUIP_IDX, fe):
                        p.write(p.base + he + k * 0x38 + 0x1C, struct.pack('<2I', v, v))
                    self._eq_wrote = list(fe); self._eq_prev = list(fe)
                    log(f'knapper: tok vennens oppsett {fe}')
                except OSError:
                    pass
        self._eq_fv = fv
        pad.friend_drawn = bool((self.friend or {}).get('dr')) if fresh else False
        pad.friend_dr = list((self.friend or {}).get('dr') or []) if fresh else []
        pad.friend_db = dict((self.friend or {}).get('db') or {}) if fresh else {}

    BOX_KEYS = ('MovableBox', 'PushBlock')

    def _box_tick(self, now):
        """Dyttbare bokser: den som flyttet boksen sist bestemmer. Par kjennes igjen på startposisjonen."""
        if now - getattr(self, '_bx_t', 0) < 0.05 or not (self.p and self.ready):
            return
        self._bx_t = now
        p, pad = self.p, self.pad
        moved = self.__dict__.setdefault('_bx_moved', {})     # adresse -> (siste pos, tid sist flyttet her)
        written = self.__dict__.setdefault('_bx_written', {}) # adresse -> pos vi selv skrev (ikke regn som egen flytting)
        mine = []
        me = pad.my_apos(p)
        try:
            l2 = p.f32(pad.c_act + 0x31C, 3) if pad.c_act is not None else None
        except OSError:
            l2 = None
        for a, (nm, first, _l) in list(getattr(self, '_ac_track', {}).items()):
            if not any(k in nm for k in self.BOX_KEYS):
                continue
            try:
                pos = p.f32(a + 0x31C, 3); rot = p.f32(a + 0x328, 9)
            except OSError:
                continue
            last, tm = moved.get(a, (pos, 0.0))
            if math.dist(last, pos) > 0.02 and not (a in written and math.dist(written[a], pos) < 0.05):
                written.pop(a, None)
                me_d = math.dist(me, pos) if me else 1e9
                l2_d = math.dist(l2, pos) if l2 else 1e9
                if me_d <= l2_d:        # bare min egen Link teller – Link 2 som dytter her er vennens dytt
                    tm = now
            moved[a] = (pos, tm)
            mine.append((a, nm, first, pos, rot, tm))
        self._my_boxes = [[nm, [round(v, 2) for v in first], [round(v, 3) for v in pos], [round(v, 4) for v in rot], round(now - tm, 2) if tm else 9999]
                          for _a, nm, first, pos, rot, tm in mine] or None
        fresh = bool(self.friend and now - self.friend_t < 2)
        theirs = (self.friend or {}).get('box') if (fresh and pad.friend_banc == pad.cur_banc) else None
        if not theirs or not mine:
            return
        for ent in theirs:
            if len(ent) < 5:
                continue
            nm, f0, pos, rot, their_t = ent[:5]
            c = [(math.dist(first, f0), a, mp, tm) for a, n2, first, mp, _r, tm in mine if n2 == nm]
            if not c:
                continue
            d0, a, mp, tm = min(c)
            my_age = now - tm if tm else 9999
            their_age = their_t
            if d0 > 2.0 or their_age >= 9999 or their_age >= my_age - 0.5 or math.dist(mp, pos) < 0.1:
                continue
            x8 = self.__dict__.setdefault('_bx_x8', {}).get(a) or pad.actor_x8(p, a)
            if x8:
                self._bx_x8[a] = x8
                pad.move_actor(p, a, x8, pos, rot)
                written[a] = tuple(pos)
                if now - getattr(self, '_bx_log', 0) > 3:
                    self._bx_log = now; log(f'boks: flyttet {nm} til vennens posisjon {[round(v, 1) for v in pos]}')

    FLOOR_KEYS = ('MoveFloor', 'Obj_Lift', 'FallingFloor', 'FallingLadder')

    def _deku_web_tick(self, now):
        """Broadcast local landings and play the peer's landing once on the same web."""
        p, pad = self.p, self.pad
        if not (p and self.ready and self.mode == 'Story' and pad.cur_banc == 'InsideTheDekuTree'):
            self._web_sample = self._web_out = None
            self._web_landing_armed = False
            self._web_local_on = self._web_friend_on = False
            self._web_render_sample = self._web_render_pulse = None
            return
        tracked = getattr(self, '_ac_track', {})
        web = next(((a, root) for a, (name, root, _) in list(tracked.items())
                    if name == 'Obj_InsideTheDekuTree_SpiderWeb_A_01'
                    and math.dist(root, (-0.05, 99.84, -0.03)) < 0.5), None)
        if web is None:
            # Fallback: raask aktorscan. Web-aktoren kan mangle i synk-lista
            # naar den lokale spilleren staar langt unna, og da ville servoen
            # aldri startet.
            if now - getattr(self, '_web_scan_t', 0) > 2.0:
                self._web_scan_t = now
                try:
                    found = pad._list_actors_raw(p, prefix='Obj_InsideTheDekuTree_SpiderWeb_A_01') or {}
                except Exception:  # noqa: BLE001
                    found = {}
                best = None
                for a, (nm, pos) in found.items():
                    d = math.dist(pos, (-0.05, 99.84, -0.03))
                    if best is None or d < best[1]:
                        best = (a, d, pos)
                self._web_found = best
            f = getattr(self, '_web_found', None)
            if f and f[1] < 0.5:
                web = (f[0], f[2])
        if web is None or not pad.actor_alive(p, web[0]):
            self._web_sample = self._web_out = None
            self._web_landing_armed = False
            self._web_local_on = self._web_friend_on = False
            self._web_render_sample = self._web_render_pulse = None
            return
        actor, root = web
        self._web_actor = actor
        pos = pad.my_apos(p)
        prev = getattr(self, '_web_sample', None)
        self._web_sample = (p, actor, now, pos) if pos else None
        if pos and prev and prev[:2] == (p, actor) and 0.01 < now - prev[2] < 1.25:
            x, y, z = pos
            old = prev[3]
            inside = math.hypot(x - root[0], z - root[2]) < 3.7
            entered = math.hypot(old[0] - root[0], old[2] - root[2]) >= 3.7
            speed = (old[1] - y) / (now - prev[2])
            last_impact = max(getattr(self, '_web_local_t', 0), getattr(self, '_web_remote_t', 0))
            # Native rebounds and servo corrections can both lift a player;
            # only a new approach from outside the web can start another landing.
            armed = getattr(self, '_web_landing_armed', False)
            if math.hypot(x - root[0], z - root[2]) >= 3.9:
                armed = True
            landed = inside and root[1] - 1.8 < y < root[1] - 0.12 and (entered or old[1] >= root[1] - 0.12)
            self._web_landing_armed = armed
            if armed and landed and (entered or speed > 0.4) and now - last_impact > 1.3:
                self._web_landing_armed = False
                speed = max(0.0, speed)
                impulse = round(min(540.0, 120.0 + 65.0 * speed))
                self._web_local_t = now
                self._web_seq = getattr(self, '_web_seq', 0) + 1
                self._web_out = [self._web_seq, now, impulse]
                log(f'vev: lokal landing #{self._web_seq}, impuls {impulse}')
        if now - getattr(self, '_web_local_t', 0) > 1.0:
            self._web_out = None

        friend = self.friend or {}
        # v0.94.194: baade lokal og fjern spiller kan staa paa vevet. Servoen i
        # _web_load_loop bruker disse flaggene + senderens fjaerhoyde ("wy").
        self._web_root = root
        self._web_local_on = False
        if pos:
            lx, ly, lz = pos
            if (math.hypot(lx - root[0], lz - root[2]) < 3.7
                    and root[1] - 1.8 < ly < root[1] - 0.12):
                self._web_local_on = True
        self._web_friend_on = False
        fpos = friend.get('apos')
        spring = friend.get('wt' if self._web_local_on else 'wy')
        if (pad.friend_banc == pad.cur_banc and friend.get('mode') == 'Story'
                and now - self.friend_t <= 0.35 and isinstance(fpos, list) and len(fpos) == 3
                and all(type(v) in (int, float) and math.isfinite(v) for v in fpos)
                and type(spring) in (int, float) and math.isfinite(spring)
                and math.hypot(fpos[0] - root[0], fpos[2] - root[2]) < 3.7
                and abs(fpos[1] - root[1]) < 2.0):
            # The native mesh starts at -4 m on each axis and has 0.34782 m cells.
            column = (fpos[0] - root[0] + 4.0) / 0.34782
            row = (fpos[2] - root[2] + 4.0) / 0.34782
            delta = max(-1.8, min(0.4, float(spring) - root[1]))
            self._web_render_sample = (p, self.friend_t, column, row, delta)
        else:
            self._web_render_sample = None
        if (now - self.friend_t <= 0.6 and isinstance(fpos, list) and len(fpos) == 3
                and all(isinstance(v, (int, float)) for v in fpos)):
            fx, fy, fz = (float(v) for v in fpos)
            if (math.hypot(fx - root[0], fz - root[2]) < 3.7
                    and root[1] - 1.8 < fy < root[1] - 0.12):
                self._web_friend_on = True
        self._ensure_web_load_thread()
        event = friend.get('web')
        if (pad.friend_banc != pad.cur_banc or friend.get('mode') != 'Story'
                or now - self.friend_t > 0.6 or getattr(self, '_web_busy', False)
                or not isinstance(event, list) or len(event) != 3):
            return
        seq, stamp, impulse = event
        sent = friend.get('pt')
        if (type(seq) is not int or seq <= 0 or type(impulse) is not int or not 120 <= impulse <= 540
                or type(stamp) not in (int, float) or type(sent) not in (int, float)
                or not 0 <= sent - stamp < 1.05):
            return
        session = friend.get('s')
        visual_session, visual_seq = getattr(self, '_web_render_seen', (None, 0))
        if self._web_render_sample is not None and (session != visual_session or seq > visual_seq):
            self._web_render_seen = (session, seq)
            self._web_render_pulse = (now, impulse / 540.0, self._web_render_sample)
        last_session, last_seq = getattr(self, '_web_seen', (None, 0))
        if session == last_session and seq <= last_seq:
            return
        if now - getattr(pad, '_tp_t', 0) < CALL_TELEPORT_COOLDOWN:
            return
        self._web_seen = (session, seq)
        self._web_remote_t = now
        occupied = bool(pos and math.hypot(pos[0] - root[0], pos[2] - root[2]) < 3.7
                        and root[1] - 1.8 < pos[1] < root[1] - 0.12)
        # An unloaded web needs more impulse to match a native landing. With local Link
        # already on the web, use the smaller measured response to limit the combined load.
        if pos and math.hypot(pos[0] - root[0], pos[2] - root[2]) < 3.7:
            self._web_landing_armed = False
        force = round(impulse * (900 if occupied else 1800) / 540)
        # v0.94.192: landingen gaar gjennom last-traaden, ellers nuller 10 Hz-lasten
        # ut landingsimpulsen i samme fysikkramme (0x38BF1C0 setter hastigheten).
        self._web_land = (time.time(), float(force))
        log(f'vev: fjernlanding #{seq}, impuls {force}, lokal belastning={occupied}')
        self._web_busy = False

    def _deku_web_render_input(self, p, now):
        sample = getattr(self, '_web_render_sample', None)
        if sample is not None and sample[0] is p and now - sample[1] <= 0.35:
            return sample
        pulse = getattr(self, '_web_render_pulse', None)
        if pulse and pulse[2][0] is p and 0.0 <= now - pulse[0] < 1.4:
            return pulse[2]
        return None

    def _deku_web_visual_delta(self, delta, now):
        pulse = getattr(self, '_web_render_pulse', None)
        if pulse is not None:
            age = max(0.0, now - pulse[0])
            if age < 1.4:
                oscillation = 1.7 * pulse[1] * math.exp(-2.0 * age) * math.sin(8.8 * age)
                blend = min(1.0, age / 0.16, (1.4 - age) / 0.35)
                blend *= blend * (3.0 - 2.0 * blend)
                delta += blend * (-self.WEB_DEPTH_DEFAULT - oscillation - delta)
        return max(-1.8, min(0.4, delta))

    def _deku_web_puppet_contact(self, p, zone, actor, position, now):
        sample = self._deku_web_render_input(p, now)
        root = getattr(self, '_web_root', None)
        pulse = getattr(self, '_web_render_pulse', None)
        if self.mode != 'Story' or zone != 'InsideTheDekuTree' or self.pad.friend_banc != zone:
            self._web_puppet_vertical = None
            return position
        x, y, z = position
        state = getattr(self, '_web_puppet_vertical', None)
        if state is not None and (state[0] != (p, actor) or not 0.0 < now - state[1] < 0.75):
            state = None
        target = y
        contact = False
        if root and sample and pulse:
            age = now - pulse[0]
            radius = math.hypot(x - root[0], z - root[2])
            if 0.0 <= age < 1.4 and radius < 3.7 and (y >= root[1] - 2.0 or state is not None):
                height = self._deku_web_visual_delta(sample[4], now)
                strength = min(1.0, age / 0.16, (1.4 - age) / 0.35, (3.7 - radius) / 0.5)
                strength *= strength * (3.0 - 2.0 * strength)
                target += max(0.0, root[1] + height - 0.29 - y) * strength
                contact = True
        if state is None:
            if contact:
                self._web_puppet_vertical = ((p, actor), now, y, 0.0)
            else:
                self._web_puppet_vertical = None
            return position
        _, previous_time, height, velocity = state
        dt = min(now - previous_time, 0.033)
        # Exact critically damped spring step for a fixed target over this frame.
        # It preserves velocity through contact, packet gaps, and release.
        omega = 32.0
        error = height - target
        slope = velocity + omega * error
        decay = math.exp(-omega * dt)
        height = target + (error + slope * dt) * decay
        velocity = (velocity - omega * slope * dt) * decay
        self._web_puppet_vertical = ((p, actor), now, height, velocity)
        if not contact and abs(height - y) < 0.01 and abs(velocity) < 0.15:
            self._web_puppet_vertical = None
            return position
        return x, height, z

    def _render_deku_web(self, p, now):
        """Play the remote impact at the fast-loop cadence and expire stale render state."""
        if p is None or self.pad.hR is None:
            return
        sample = self._deku_web_render_input(p, now)
        if (sample is not None and self.mode == 'Story'
                and self.pad.cur_banc == self.pad.friend_banc == 'InsideTheDekuTree'):
            _, _, column, row, delta = sample
            data = struct.pack('<3fI', column, row, self._deku_web_visual_delta(delta, now), 12)
        elif getattr(self, '_web_render_live', False):
            data = bytes(16)
        else:
            return
        try:
            p.write(p.base + self.pad.hR + 0xEE0, data)
            self._web_render_live = data != bytes(16)
        except OSError:
            self._web_render_live = False

    WEB_LOAD_IMPULSE = 380.0    # v0.94.192: 10 Hz -> 0,385 m senking = vekten av en staaende spiller
    WEB_LOAD_PERIOD = 0.1       # v0.94.192: intervall mellom last-impulsene
    WEB_CFG_NAME = 'web_servo.json'
    WEB_DEPTH_DEFAULT = 0.387   # dybde (m) en staaende spiller gir paa vevet (kalibrert)
    WEB_LOAD_K = 9870.0         # fjaerstivhet (impuls/m per meter) kalibrert fra 380@10Hz -> 0,385 m

    def _web_cfg(self, now):
        """Les servo-konfig fra web_servo.json (runtime-tunbar, ingen ny bygging).

        Nokler: mode (off|fixed|servo), kp, ki, deadband, rate, max_impulse,
        min_impulse, max_step, i_max, tau_local, target_offset, fixed_impulse.
        """
        if now - getattr(self, '_web_cfg_t', 0) < 1.0:
            return getattr(self, '_web_cfg_v', None) or {}
        self._web_cfg_t = now
        cfg = {'mode': 'servo', 'kp': 300.0, 'ki': 150.0, 'deadband': 0.01,
               'rate': 0.04, 'max_impulse': 900.0, 'min_impulse': 20.0,
               'max_step': 40.0, 'i_max': 2.0, 'tau_local': 1.0,
               'target_offset': 0.0, 'fixed_impulse': self.WEB_LOAD_IMPULSE}
        for folder in (os.path.dirname(sys.executable or ''), os.getcwd()):
            if not folder:
                continue
            try:
                with open(os.path.join(folder, self.WEB_CFG_NAME), 'r', encoding='utf-8') as fh:
                    data = json.load(fh)
                if isinstance(data, dict):
                    cfg.update({k: data[k] for k in list(cfg) if k in data})
                break
            except (OSError, ValueError):
                continue
        self._web_cfg_v = cfg
        return cfg

    def _ensure_web_load_thread(self):
        thr = getattr(self, '_web_load_thr', None)
        if thr is not None and thr.is_alive():
            return
        thr = threading.Thread(target=self._web_load_loop, daemon=True, name='DekuWebServo')
        self._web_load_thr = thr
        thr.start()

    def _web_body(self, p, actor, now):
        """Cachaet foerelse til fjaerlegemet (spill-VA)."""
        va = getattr(self, '_web_body_va', None)
        if (va and getattr(self, '_web_body_actor', None) == actor
                and now - getattr(self, '_web_body_t', 0) < 5.0):
            return va
        va = self.pad.deku_web_body(p, actor)
        self._web_body_va = va
        self._web_body_actor = actor
        self._web_body_t = now
        return va

    def _web_load_loop(self):
        """v0.94.194: lukket regulering av fjaerlegemet mot senderens fjaerhoyde.

        En ekte landing er ikke et stoet: spillerens vekt ligger paa vevet i
        over et sekund, saa vevet svinger og spilleren hopper. Paa observatoeren
        maa vi derfor baere fjernspillerens vekt, ellers blir vevet 0,4-0,7 m
        hoeyere enn paa avsendersiden og dukken staar nedsunket.

        v0.94.192 brukte en fast 10 Hz-last (380 per kall). Det ga to problemer:
        +- vipping (+-13 cm) fordi hvert kall dytter fjærlegemet med et diskret
          støt, og
        +- 9 cm hvileavvik fordi moddens faktiske kallrate er lavere enn 10 Hz
          (kallene tar 200-800 ms), slik at lasten blir svakere.
        +- 10 kall/s fylte delingslaasen for spillkall (pakkerate 23 -> 7/s).

        v0.94.194: senderen melder sin fjaerhoyde ("wy") i tilstandspakken, og
        observatoeren regulerer mot den med proporsjon + integral, med
        doedbaand. I likevekt blir det ingen spillkall i det hele tatt, og
        vippingen forsvinner fordi vi ikke dytter naar avviket er under
        doedbaandet. Integral-leddet tar bort 9 cm-avviket.
        """
        pad = self.pad
        last = time.time()
        integ = 0.0
        push = 0.0
        while True:
            time.sleep(0.02)
            try:
                now = time.time()
                cfg = self._web_cfg(now)
                if now - getattr(self, '_web_dbg_t', 0) > 1.0:
                    self._web_dbg_t = now
                    fr = self.friend or {}
                    log(f'vev-dbg: akt={getattr(self, "_web_actor", None)} '
                        f'local_on={getattr(self, "_web_local_on", None)} '
                        f'friend_on={getattr(self, "_web_friend_on", None)} '
                        f'apos={fr.get("apos")} alder={now - self.friend_t:.2f} '
                        f'min_wy={fr.get("wy")} min_wt={fr.get("wt")} '
                        f'min_y={getattr(self, "_my_web_y", None)} '
                        f'egen_y={getattr(self, "_web_y_f", None)}')
                period = max(0.02, float(cfg.get('rate') or 0.04))
                if now - last < period:
                    continue
                dt = now - last
                last = now
                p = self.p
                actor = getattr(self, '_web_actor', None)
                if (not p or not self.ready or self.mode != 'Story'
                        or pad.cur_banc != 'InsideTheDekuTree' or actor is None
                        or not pad.actor_alive(p, actor)):
                    integ = 0.0
                    continue
                body = self._web_body(p, actor, now)
                y = pad.deku_web_y(p, body) if body else None
                if y is None:
                    continue
                # Filtrert hoyde: gjor at servoen ikke jakter paa spillerens
                # naturlige bobbing paa vevet.
                tau = max(0.1, float(cfg.get('tau_local') or 1.0))
                a = min(1.0, dt / tau)
                filt = getattr(self, '_web_y_f', None)
                self._web_y_f = y if filt is None else filt + a * (y - filt)
                yf = self._web_y_f
                local_on = bool(getattr(self, '_web_local_on', False))
                friend_on = bool(getattr(self, '_web_friend_on', False))
                self._my_web_y = round(yf, 3)
                # The controller origin and per-player depth were calibrated
                # unloaded. An airborne player can leave both flags false
                # while the web still carries energy from the landing.
                rest = self._web_root[1]
                depth = self.WEB_DEPTH_DEFAULT
                target = rest - depth * (int(local_on) + int(friend_on))
                self._my_web_target = round(target, 3)

                land = getattr(self, '_web_land', None)
                if land and now - land[0] < 1.0:
                    self._web_land = None
                    push = 0.0
                    pad.deku_web_impulse(p, actor, land[1], body)
                    continue
                mode = str(cfg.get('mode') or 'servo')
                if mode == 'off':
                    integ = 0.0
                    push = 0.0
                    continue
                if not friend_on:
                    integ = 0.0
                    push = 0.0
                    continue
                if mode == 'fixed':
                    pad.deku_web_impulse(p, actor, float(cfg.get('fixed_impulse') or self.WEB_LOAD_IMPULSE), body)
                    continue
                target += float(cfg.get('target_offset') or 0.0)
                err = yf - target
                db = float(cfg.get('deadband') or 0.01)
                step = float(cfg.get('max_step') or 40.0)
                # Faktisk kallrate (ikke den vi onsker): feedforwarden skal
                # bruke den vi faktisk far.
                if now - getattr(self, '_web_imp_t', 0) >= 1.0:
                    n = getattr(self, '_web_imp_n', 0) - getattr(self, '_web_imp_n0', 0)
                    dt = now - getattr(self, '_web_imp_t', 0)
                    if dt > 0.2 and n > 0:
                        r = n / dt
                        cur = getattr(self, '_web_rate', 0.0) or r
                        self._web_rate = cur + 0.3 * (r - cur)
                    self._web_imp_n0 = getattr(self, '_web_imp_n', 0)
                    self._web_imp_t = now
                rate = getattr(self, '_web_rate', 0.0) or (1.0 / period)
                # Feedforward: den statiske vekten som mangler, regnet ut fra
                # fjaerstivheten (9870 impuls/m) og den faktiske kallraten.
                d_total = max(0.0, rest - target)
                d_emul = max(0.0, d_total - (depth if local_on else 0.0))
                ff = self.WEB_LOAD_K * d_emul / max(1.0, rate)
                if err > db:
                    integ = min(float(cfg.get('i_max') or 2.0), integ + (err - db) * dt)
                    want = ff + (float(cfg.get('kp') or 300.0) * err
                                 + float(cfg.get('ki') or 150.0) * integ)
                    want = max(0.0, min(float(cfg.get('max_impulse') or 900.0), want))
                    push = max(push - step, min(push + step, want))
                    if push >= float(cfg.get('min_impulse') or 20.0):
                        pad.deku_web_impulse(p, actor, push, body)
                        self._web_imp_n = getattr(self, '_web_imp_n', 0) + 1
                        last = time.time()
                else:
                    integ = max(0.0, integ - 0.5 * dt)
                    want = ff
                    push = max(push - step, min(push + step, want))
                    if push >= float(cfg.get('min_impulse') or 20.0):
                        pad.deku_web_impulse(p, actor, push, body)
                        self._web_imp_n = getattr(self, '_web_imp_n', 0) + 1
                        last = time.time()
                if now - getattr(self, '_web_log_t', 0) > 1.0:
                    self._web_log_t = now
                    log(f'vev-servo: y={y:.3f} filtrert={yf:.3f} maal={target:.3f} '
                        f'avvik={err:+.3f} push={push:.0f} ff={ff:.0f} rate={rate:.1f} '
                        f'integ={integ:.2f} mod={mode}')
            except Exception as exc:  # noqa: BLE001
                # Logg stille feil: ellers forsvinner de i det stille, og
                # regulatoren ser ut til aa vaere "koblet fra".
                if now - getattr(self, '_web_err_t', 0) > 30:
                    self._web_err_t = now
                    log(f'vev-feil: {exc!r}')

    def _floor_tick(self, now):
        """Bevegelige plattformer: verten (lavest IP) sender sine, den andre flytter sine like plattformer dit."""
        if now - getattr(self, '_fl2_t', 0) < 0.08 or not (self.p and self.ready):
            return
        self._fl2_t = now
        p, pad = self.p, self.pad
        track = getattr(self, '_ac_track', {})
        mine = []
        for a, (nm, _f, _l) in list(track.items()):
            if any(k in nm for k in self.FLOOR_KEYS):
                try:
                    an = None
                    if 'FallingLadder' in nm or 'WaterGate' in nm:
                        a_n, _fr = pad.read_anim(p, a)
                        if a_n and a_n.isascii() and a_n[0].isalpha():
                            an = a_n
                    mine.append((a, nm, p.f32(a + 0x31C, 3), p.f32(a + 0x328, 9), an))
                except OSError:
                    pass
        host = self._time_host()
        self._my_floors = [[nm, [round(v, 3) for v in pos], [round(v, 4) for v in rot], an] for _a, nm, pos, rot, an in mine] if mine else None
        fresh = bool(self.friend and now - self.friend_t < 2)
        theirs = (self.friend or {}).get('flr') if (fresh and pad.friend_banc == pad.cur_banc) else None
        if not theirs or not mine:
            return
        pair = self.__dict__.setdefault('_fl2_pair', {})
        last_mv = self.__dict__.setdefault('_fl2_mv_t', {})
        last_an = self.__dict__.setdefault('_fl2_an_t', {})
        used = set()
        for k, ent in enumerate(theirs):
            if len(ent) < 3:
                continue
            nm, pos, rot = ent[:3]
            t_an = ent[3] if len(ent) >= 4 else None
            cands = [(math.dist(mp, pos), a, mp, ma) for a, n2, mp, _r, ma in mine if n2 == nm and a not in used]
            if not cands:
                continue
            prev = pair.get((nm, k))
            chosen = next((c for c in cands if c[1] == prev), None) or min(cands)
            drift, a, _mp, my_an = chosen
            pair[(nm, k)] = a; used.add(a)
            me_p = pad.my_apos(p)
            if me_p and math.dist(_mp, me_p) > 35.0:
                continue
            if (isinstance(t_an, str) and t_an.startswith(('On', 'Open', 'Fall'))
                    and isinstance(my_an, str) and my_an.startswith(('Off', 'Close', 'Wait'))
                    and now - last_an.get(a, 0) >= 1.0):
                last_an[a] = now
                r_an = pad.play_anim(p, a, t_an)
                log(f'plattform: synket anim {nm} {my_an} -> {t_an} -> {r_an}')
            if not host and drift > 0.15 and now - last_mv.get(a, 0) >= 0.08:
                last_mv[a] = now
                pad.move_actor_real(p, a, pos, rot)
                if now - getattr(self, '_fl2_log', 0) > 5:
                    self._fl2_log = now
                    log(f'plattform: synket {nm} drift={drift:.2f}m -> {[round(v, 2) for v in pos]}')

    def _friend_damage_delta(self):
        """Hent nye skadekvartaler. PvP har egen teller og tåler at motspilleren starter på nytt."""
        f = self.friend or {}
        pvp = getattr(self, 'mode', 'Story') == 'PvP'
        state = getattr(self, '_server_state', {}) if pvp else {}
        lobby = state.get('lobby') or {}
        if lobby.get('capacity') in (20, 50) and lobby.get('game_mode') == 'deathmatch':
            started_at = lobby.get('started_at')
            total = state.get('damage_total')
            if (started_at is None or not getattr(self, '_pvp_in_arena', False)
                    or self.pad.cur_banc != 'HyruleField_Child' or type(total) is not int):
                return 0
            match = (lobby.get('id'), started_at)
            previous_match, previous_total = getattr(self, '_pvp_server_damage', (None, 0))
            if previous_match and previous_match[0] == match[0] and started_at < previous_match[1]:
                return 0
            if match != previous_match:
                previous_total = 0
            if total <= previous_total:
                return 0
            self._pvp_server_damage = (match, total)
            return total - previous_total
        key = 'pvph' if pvp else 'l2d'
        tot = f.get(key)
        if not isinstance(tot, int) or tot < 0:
            return 0
        if pvp:
            session = f.get('s')
            previous_session = getattr(self, '_pvph_session', None)
            if session != previous_session:
                # Ikke spill av gamle treff ved første tilkobling. En ny økt derimot starter på 0,
                # slik at første slag etter omstart ikke blir blokkert av den gamle summen.
                self._pvph_seen = tot if previous_session is None else 0
                self._pvph_session = session
            seen = getattr(self, '_pvph_seen', tot)
            self._pvph_seen = tot
        else:
            seen = getattr(self, '_l2d_seen', None)
            self._l2d_seen = tot
            if seen is None:
                return 0
        if tot < seen:   # Ekstra sikring mot nullstilt teller.
            seen = 0
        return tot - seen if 0 < tot - seen <= 80 else 0

    def _apply_friend_hits(self):
        """Bruk nye PvP-treff eller Story-fiendeskade på egen Link; aldri i PvP-lobbyen."""
        if (getattr(self, 'mode', 'Story') == 'PvP' and getattr(self, '_pvp_social_lobby', False)
                and getattr(self.pad, 'cur_banc', None) == self.PVP_LOBBY_BANC):
            return
        previous_damage = getattr(self, '_pvp_server_damage', (None, 0))
        dmg = self._friend_damage_delta()
        if not dmg:
            return
        hp_written = False
        try:
            pc, _pm = self.pad._player_sv(self.p)
            if pc is None:
                return
            hp = struct.unpack("<I", self.p.read(self.p.base + pc, 4))[0]
            if getattr(self, 'mode', 'Story') == 'PvP':
                if time.time() < getattr(self, '_pvp_down_until', 0):
                    return
                ko = hp - dmg <= 0
                amt = (hp - 1) if ko else dmg
                target = max(1, hp - amt)
                lobby = (getattr(self, '_server_state', {}).get('lobby') or {})
                from_server = lobby.get('capacity') in (20, 50) and lobby.get('game_mode') == 'deathmatch'
                # The native damage record is applied after the HP write,
                # so server damage uses only the cosmetic reaction.
                r = False if from_server else self.pad.hit_replay(
                    self.p, self.pad.p_act, self.pad.c_act or self._nearest_opp_puppet(), max(1, amt), heavy=ko)
                # Skriving i Life-komponenten betyr ikke at spillerens HP faktisk endret seg.
                # HP er derfor alltid autoritativ her, også når hit replay returnerer True.
                # v0.94.307: hit replay legger også inn spillets egen skade (trekkes i Life-steget etter skrivingen) –
                # før ble skaden trukket to ganger (HP 4 -> 0, livvakta reddet). Når replay virket: skriv target + amt,
                # så spillets eget trekk lander på target; etter 0,5 s rettes HP til target hvis spillet ikke trakk.
                self.p.write(self.p.base + pc, struct.pack("<I", target + amt if r else target))
                hp_written = True
                self._pvp_hp_shadow = target
                if r:
                    proc_, pc_t = self.p, pc

                    def _settle(proc_=proc_, pc_t=pc_t, target=target):
                        try:
                            if self.p is proc_:
                                now_hp = struct.unpack("<I", proc_.read(proc_.base + pc_t, 4))[0]
                                if now_hp != target:
                                    proc_.write(proc_.base + pc_t, struct.pack("<I", target))
                                    log(f'skade: spillet trakk ikke selv ({now_hp}) – HP satt til {target}')
                                    # v0.94.309: spillet tok ikke treffet -> ingen egen reaksjon; vis i det minste skade-animasjonen
                                    self.ui(lambda: self.pad.play_anim(self.p, self.pad.p_act, 'Damage'))
                        except Exception:  # noqa: BLE001
                            pass
                    threading.Timer(0.5, _settle).start()
                log(f"skade: PvP-treff -{dmg} kvartaler ({hp} -> {target}){' – SLÅTT NED' if ko else ''} (hit replay {r})")
                if ko:
                    self._pvp_down_until = time.time() + 5.0
                    self._pvp_deaths = getattr(self, '_pvp_deaths', 0) + 1
                    tm = self._active_pvp_team() if hasattr(self, '_active_pvp_team') else getattr(self, 'look', None)
                    if not from_server and getattr(self, '_game_mode', 'ctf') == 'deathmatch' and tm in ('Red', 'Blue'):
                        self._server_cmd('eliminated', team=tm)
                    self._append_chat_sys(f'💥 You were knocked down! ({self._pvp_deaths}) – up again in 5 s')
                    match = getattr(self, '_pvp_large_match', None)
                    proc = self.p

                    def respawn():
                        if from_server and (self.mode != 'PvP' or self.p is not proc
                                            or getattr(self, '_pvp_large_match', None) != match):
                            return
                        self._pvp_respawn(pc, _pm, False)

                    threading.Timer(5.0, lambda: self.ui(respawn)).start()
                if not r:
                    self.pad.play_anim(self.p, self.pad.p_act, 'Damage')
                return
            new = max(1, hp - dmg)
            if new != hp:
                self.p.write(self.p.base + pc, struct.pack("<I", new))
            log(f"skade: fiende traff meg på vennens skjerm: -{dmg} kvartaler ({hp} -> {new})")
        except Exception as e:  # noqa: BLE001
            log(f"skade: feil {e!r}")
        finally:
            if not hp_written and getattr(self, '_pvp_server_damage', previous_damage) != previous_damage:
                self._pvp_server_damage = previous_damage

    def _enemy_tick(self, now):
        """Fiender deles begge veier. Hver PC sender sine fiender nær egen Link (med avstand). Mangler en hos den andre,
        lages en kopi der. Finnes den hos begge, styrer PC-en som har Link nærmest fienden posisjonen, den andre følger."""
        if now - getattr(self, '_en_tick', 0) < 0.1 or getattr(self, '_en_busy', False) or not (self.p and self.ready):
            return
        self._en_tick = now; self._en_busy = True
        self._mv_budget = 0
        fresh = bool(self.friend and now - self.friend_t < 2)
        same = fresh and self.pad.cur_banc and self.pad.friend_banc == self.pad.cur_banc
        if now - getattr(self.pad, '_banc_since', 0) < 5.0:   # rommet lastes ennå: ikke lag/slett aktører (spillet kan henge)
            same = False
        theirs = (self.friend or {}).get('enem') if same else None
        self._apply_friend_hits()
        try:
            if self._boss_near(25.0):   # v0.94.214: 25 m (var 60 m, som slo av mål-patchen ved inngangen pga Gohma-egg 60 m unna)
                if not getattr(self, '_tgt_boss_off', False):
                    self._tgt_boss_off = True; log('mål-patch: av (boss i nærheten)')
                h_ = self.p.base + self.pad.hR + self.pad.TARGET_MBOX_R
                self.p.write(h_, struct.pack('<Q', 0))
            else:
                if getattr(self, '_tgt_boss_off', False):
                    self._tgt_boss_off = False; log('mål-patch: på igjen')
                self.pad.set_target_link2(self.p, getattr(self, 'target_mode', 0))
        except Exception:  # noqa: BLE001
            pass
        if now - getattr(self, '_en_dbg2', 0) > 10:
            self._en_dbg2 = now
            st_ = self.pad.target_stats(self.p)
            if st_:
                log(f"mål-patch: kall={st_[0]} Link2-valgt={st_[1]} | AI-pause-treff={st_[2]}")
            log(f"fiende-status: fersk={fresh} samme sone={bool(same)} (her {self.pad.cur_banc}, venn {self.pad.friend_banc}) venn-liste={'None' if theirs is None else len(theirs)} min-liste={'None' if getattr(self, '_my_enem', None) is None else len(self._my_enem)} par={len(getattr(self, '_en_map', {}))} følger={sum(1 for v in getattr(self, '_en_follow', {}).values() if v)}")
        def run():
            try:
                pad, p = self.pad, self.p
                track = getattr(self, '_ac_track', {})
                me = pad.my_apos(p)
                host_t = self._time_host()   # verten (lavest IP) eier skjelettene
                if not (same and me):
                    self._my_enem = None
                    return
                m = self.__dict__.setdefault('_en_map', {})          # vennens id -> (min adresse, x8)
                driven = {v[0] for hid, v in m.items() if self.__dict__.get('_en_follow', {}).get(hid)}
                lst = []
                for a, (nm, first, last) in list(track.items()):
                    if not nm.startswith('Enemy_') or 'Boss' in nm or 'Stalchild' in nm or 'Scrub_Business' in nm or 'Scrub_Deku_Brothers' in nm or 'Scrub_Deku_Leaf' in nm or 'Skulltula_Gold' in nm or a in driven:   # skjeletter: hver PC sine (vert-eierskap ga kaos)   # bosser synkes ikke (mellomscener/faser); kopier jeg styrer sendes ikke tilbake
                        continue
                    if any(cn == nm and now - ct < 30 and math.dist(cp, last) < 4.0 for cn, cp, ct in self.__dict__.get('_en_created', [])):
                        continue   # nylig laget kopi som ennå ikke er koblet – ikke send den tilbake (ville gitt dobbel)
                    try:
                        pos = p.f32(a + 0x31C, 3); rot = p.f32(a + 0x328, 9)
                    except OSError:
                        continue
                    dd = math.dist(pos, me)
                    if dd < 60 and all(math.isfinite(v) for v in pos):
                        hp, mx = self._actor_hp(p, a)
                        an, frame = pad.read_anim(p, a) if dd < 30 else (None, None)
                        if frame is not None and not math.isfinite(frame):
                            frame = None
                        aim = pad.read_deku_aim(p, a) if ('Dekubaba' in nm and 'Drop' not in nm and dd < 30) else None
                        aim = round(aim, 3) if (aim is not None and math.isfinite(aim)) else None
                        lst.append((dd, [a, nm, [round(v, 2) for v in pos], [round(v, 3) for v in rot], round(dd, 1), hp, mx, an, frame, aim]))
                lst.sort(key=lambda t: t[0])
                self._my_enem = [x for _d, x in lst[:24]]
                t0 = self.__dict__.setdefault('_en_ready_t', now)
                if now - t0 < 15 or now - getattr(pad, '_banc_since', 0) < 15:
                    self._my_enem = None   # har ikke sett seg rundt ennå – en tom liste ville fått vennen til å slette alt
                if theirs is None:   # tom liste = vennen har ingen fiender nær seg (opprydding skal fortsatt kjøre)
                    return
                follow = self.__dict__.setdefault('_en_follow', {})
                seen = self.__dict__.setdefault('_en_seen', {})
                friend_claims = set((self.friend or {}).get('tk') or [])   # mine adresser som vennen har tatt over
                # Forleng eierskap mens fienden er i kamp med min Link (nær, ikke i hvile, og ikke mye lenger unna enn vennen)
                cl = self.__dict__.setdefault('_en_claims', {}); ca = self.__dict__.setdefault('_claim_addr', {})
                for h, t in list(cl.items()):
                    a_c = ca.get(h)
                    if t < now - 30:
                        cl.pop(h, None); ca.pop(h, None); continue
                    if t > now and a_c is not None and pad.actor_alive(p, a_c):
                        try:
                            ec_pos = p.f32(a_c + 0x31C, 3)
                            my_dc = math.dist(ec_pos, me)
                            f_pos = (self.friend or {}).get('apos')
                            th_dc = math.dist(ec_pos, f_pos) if f_pos and len(f_pos) == 3 else 1e9
                            if my_dc < 10.0 and my_dc <= th_dc + 1.0:
                                an_c, _f = pad.read_anim(p, a_c)
                                if an_c and not an_c.startswith(('Wait', 'Sleep')):
                                    cl[h] = now + 4.0
                        except OSError:
                            pass
                used = {v[0] for v in m.values()}
                ids = set()
                for ent in theirs:
                    if len(ent) < 5:
                        continue
                    hid, nm, pos, rot, their_d = ent[:5]
                    if 'Gohma' in nm or 'Boss' in nm:   # v0.59: bosser og deres egg/larver styres bare av boss-synken (dobbel styring hang spillet)
                        continue
                    t_hp, t_mx = (ent[5], ent[6]) if len(ent) >= 7 else (None, None)
                    t_an = ent[7] if len(ent) >= 8 else None
                    t_frame = ent[8] if len(ent) >= 9 else None
                    t_aim = ent[9] if len(ent) >= 10 else None
                    ids.add(hid); seen[hid] = now
                    cur = m.get(hid)
                    if cur and not pad.actor_alive(p, cur[0]):
                        m.pop(hid); used.discard(cur[0]); cur = None
                    free = []
                    if cur is None:
                        free = [(math.dist(last, pos), a) for a, (n2, first, last) in track.items() if n2 == nm and a not in used]
                        free.sort()
                        n_host = sum(1 for x in theirs if x[1] == nm)
                        if free and free[0][0] <= 6.0:   # samme grense ved kobling og løpende validering
                            x8 = pad.actor_x8(p, free[0][1])
                            if x8:
                                m[hid] = (free[0][1], x8); used.add(free[0][1]); cur = m[hid]
                        elif not any(n3 == nm and math.dist(l3, pos) < 40 for _a3, (n3, _f3, l3) in track.items()) and 'Boss' not in nm and 'Gohma' not in nm \
                                and now - getattr(self, '_en_spawn_t', 0) > 1.0 and math.dist(pos, me) < 80 \
                                and hid not in self.__dict__.setdefault('_en_pend', {}):
                            self._en_spawn_t = now; self._en_pend[hid] = now
                            r = pad.create_actor(p, nm, pos)
                            cr = self.__dict__.setdefault('_en_created', []); cr.append((nm, tuple(pos), now)); del cr[:-40]
                            follow[hid] = True
                            log(f'fiende: laget {nm} hos meg (finnes hos vennen) -> {r}')
                    if cur:
                        try:
                            cpos = p.f32(cur[0] + 0x31C, 3)
                        except OSError:
                            continue
                        drift = math.dist(cpos, pos)
                        if drift > 6.0:
                            # To like fiender kan bytte plass. Forkast paret før liv og animasjon kopieres.
                            m.pop(hid, None)
                            follow.pop(hid, None)
                            used.discard(cur[0])
                            continue
                        claims = self.__dict__.setdefault('_en_claims', {})   # vennens id -> utløp: jeg eier fienden (den angriper min Link)
                        # Treff: livet på min kopi er lavere enn eierens -> jeg slo den -> jeg tar over
                        try:
                            if t_hp is not None:
                                mh, _mm = self._actor_hp(p, cur[0])
                                if mh is not None and mh < t_hp and follow.get(hid):
                                    if claims.get(hid, 0) < now:
                                        log(f'eierskap: tar {nm} (jeg traff den: {mh} < {t_hp})')
                                    claims[hid] = now + 6.0; self.__dict__.setdefault('_claim_addr', {})[hid] = cur[0]
                        except Exception:  # noqa: BLE001
                            pass
                        self._share_hp(p, cur[0], nm, t_hp, t_mx)
                        my_d = math.dist(cpos, me)
                        # Hysterese: bytt styrer bare når den andre er > 3 m nærmere, og hold valget minst 2 s
                        # (ellers vipper styringen frem og tilbake når begge står like langt unna og fienden «henger»).
                        sw = self.__dict__.setdefault('_en_sw', {})
                        prev = follow.get(hid)
                        # v0.50: den som står nærmest styrer (fienden biter styrerens egen Link). Før styrte verten alltid
                        # innen 3 m, så planten bet verten selv om vennen sto nærmere. Liten hysterese (0,75 m) mot vipping.
                        if prev is None and abs(their_d - my_d) <= 0.75:
                            want = not host_t
                        elif prev is None:
                            want = their_d < my_d
                        else:
                            want = (their_d + 0.75 < my_d) if not prev else not (my_d + 0.75 < their_d)
                        if prev is None or (want != prev and now - sw.get(hid, 0) > 1.0):
                            follow[hid] = want; sw[hid] = now
                        if claims.get(hid, 0) > now:
                            follow[hid] = False          # jeg har tatt den over
                        elif cur[0] in friend_claims:
                            follow[hid] = True           # vennen har tatt den over – jeg følger
                        if 'Stalchild' in nm and not host_t:
                            follow[hid] = True   # vertens skjeletter: gjesten følger alltid
                        if follow[hid]:
                            f_apos_ = (self.friend or {}).get('apos')
                            if f_apos_ and len(f_apos_) == 3:
                                self.__dict__.setdefault('_follow_slot0_acts', {})[cur[0]] = now
                                pad.sync_enemy_slot0_pos(p, cur[0], f_apos_)
                            if t_an and getattr(self, '_mv_budget', 0) < 10:   # samme animasjon som eierens (angrep, fall …)
                                my_an, my_frame = pad.read_anim(p, cur[0])
                                if my_an == t_an and type(t_frame) in (int, float) and 0 <= t_frame <= 10000:
                                    frame_times = self.__dict__.setdefault('_en_anim_frame_t', {})
                                    if my_frame is not None and abs(my_frame - t_frame) > 4 and now - frame_times.get(cur[0], 0) > 0.35:
                                        frame_times[cur[0]] = now
                                        pad.set_anim_frame(p, cur[0], t_frame + 1)
                                if my_an and my_an != t_an and not t_an.startswith(('Wait', 'Turn', 'Sleep', 'Idle')) and now - self.__dict__.setdefault('_an_t', {}).get(cur[0], 0) > 0.08 and claims.get(hid, 0) < now:
                                    self._an_t[cur[0]] = now; self._mv_budget += 1
                                    r_an = pad.play_anim(p, cur[0], t_an)
                                    if now - getattr(self, '_an_log', 0) > 2:
                                        self._an_log = now; log(f'animasjon: {nm} {my_an} -> {t_an} -> {r_an}')
                            if drift > 0.6:   # v0.94.220: strammere posisjonssynk (0,6 m) for Skulltula-fall, Skullwalltula og jagende fiender
                                k = 0.35   # glid mot målet i stedet for å hoppe
                                tgt = [c + (t - c) * k for c, t in zip(cpos, pos)]
                                lastm = self.__dict__.setdefault('_mv_t', {})
                                if now - lastm.get(cur[0], 0) >= 0.25 and getattr(self, '_mv_budget', 0) < 6:
                                    lastm[cur[0]] = now; self._mv_budget = getattr(self, '_mv_budget', 0) + 1
                                    pad.move_actor_real(p, cur[0], tgt, rot)   # spillets egen setter – holder (testmove: 0,00 m)
                                else:
                                    pad.move_actor(p, cur[0], cur[1], tgt, rot)
                            elif rot and len(rot) == 9:   # stasjonær fiende (f.eks. Dekubaba): synk rotasjon fra eieren via move_actor_real
                                try:
                                    cur_rot = p.f32(cur[0] + 0x328, 9)
                                    if sum(abs(a - b) for a, b in zip(cur_rot, rot)) > 0.08:
                                        lastm = self.__dict__.setdefault('_mv_t', {})
                                        if now - lastm.get(cur[0], 0) >= 0.20 and getattr(self, '_mv_budget', 0) < 6:
                                            lastm[cur[0]] = now; self._mv_budget = getattr(self, '_mv_budget', 0) + 1
                                            pad.move_actor_real(p, cur[0], cpos, rot)
                                        else:
                                            pad.move_actor(p, cur[0], cur[1], cpos, rot)
                                except OSError:
                                    pass
                if False and not host_t:   # avslått: slettet også egne kopier
                    used2 = {v[0] for v in m.values()}
                    for a, (nm, first, last) in list(track.items()):
                        if 'Stalchild' not in nm or a in used2:
                            continue
                        if any(cn == nm and now - ct < 30 and math.dist(cp, last) < 4.0 for cn, cp, ct in self.__dict__.get('_en_created', [])):
                            continue
                        track.pop(a, None); pad.delete_actor(p, a)
                        log(f'fiende: fjernet eget {nm} (verten eier skjelettene)')
                for hid in list(m):
                    if hid not in ids and now - seen.get(hid, 0) > 3.0:
                        a, _x = m.pop(hid)
                        if follow.pop(hid, False) and pad.actor_alive(p, a) and math.dist(track.get(a, ('', (0, 0, 0), (0, 0, 0)))[2], me) > 30:
                            pad.delete_actor(p, a); log('fiende: slettet kopi (vennen har den ikke lenger)')
                # Opprydding: vennen står nær en fiende vi har, men har den ikke -> den er drept der (drapet gikk tapt)
                fpos = (self.friend or {}).get('pos')
                miss = self.__dict__.setdefault('_en_miss', {})
                if False and now - getattr(self, '_en_dbg', 0) > 15:
                    self._en_dbg = now
                    log(f"fiende-debug: venn pos {fpos and [round(v) for v in fpos]}, venn har {[(x[1][6:], [round(v) for v in x[2]]) for x in theirs][:10]}, jeg har {[(n[6:], [round(v) for v in l]) for _a, (n, _f, l) in track.items() if n.startswith('Enemy_')][:12]}, par {len(m)}")
                if False and fpos and len(theirs) < 24:   # AV: fjernet levende fiender (vennens liste er ikke komplett)
                    used_m = {v[0] for v in m.values()}
                    # Par vennens fiender med mine (samme navn, nærmeste innenfor 12 m, én-til-én) – bevegelse gir ulik plass
                    matched = set()
                    pairs = sorted((math.dist(x[2], l), id(x), a) for x in theirs for a, (n, _f, l) in track.items() if n == x[1] and math.dist(x[2], l) < 12)
                    tk = set()
                    for _d, xi, a in pairs:
                        if xi in tk or a in matched:
                            continue
                        tk.add(xi); matched.add(a)
                    for a, (nm, _f, last) in list(track.items()):
                        if (not nm.startswith('Enemy_') or 'Boss' in nm or 'Gohma' in nm or 'Stalchild' in nm or 'Scrub_Business' in nm or 'Scrub_Deku_Brothers' in nm or 'Scrub_Deku_Leaf' in nm or 'Skulltula_Gold' in nm
                                or a in used_m or math.dist(last, fpos) > 20 or math.dist(last, me) < 4):
                            miss.pop(a, None); continue
                        if a in matched:
                            miss.pop(a, None); continue
                        if any(cn == nm and now - ct < 20 for cn, _cp, ct in self.__dict__.get('_en_created', [])):
                            continue
                        t0 = miss.setdefault(a, now)
                        if now - t0 > 6.0:
                            miss.pop(a, None); track.pop(a, None)
                            r = pad.delete_actor(p, a)
                            log(f'fiende: fjernet {nm} ved {[round(v) for v in last]} – vennen står der og har den ikke (drept) -> {r}')
                # AI-pause: kopier vi følger (vennen eier dem) får hjernen satt på pause, så de bare viser eierens bevegelse/animasjon
                if getattr(self, 'ai_hold_on', True):
                    cand = []
                    for hid_, v_ in m.items():
                        if follow.get(hid_) and self.__dict__.get('_en_claims', {}).get(hid_, 0) < now:
                            try:
                                d_ = math.dist(track[v_[0]][2], me)
                            except (KeyError, TypeError, ValueError, IndexError):
                                d_ = 1e9
                            cand.append((d_, v_[0]))
                    bl_ = [a_ for d_, a_ in sorted(cand)[:8]] if getattr(self, 'blind_on', False) else []
                    if bl_ != getattr(self, '_blind_prev', None):
                        self._blind_prev = bl_
                        pad.set_blind(p, bl_)
                        log(f'blind (følger eierens angrep): {len(bl_)} fiender')
                    held = []
                    for d_, a_ in sorted(cand):            # nærmeste først (tabellen har plass til 30)
                        c_ = pad.bsa_comp(p, a_)
                        if c_:
                            held.append(c_)
                        if len(held) >= pad.AIHOLD_MAX:
                            break
                    if held != getattr(self, '_held_prev', None):
                        self._held_prev = held
                        ok_ = pad.set_ai_hold(p, list(getattr(self, '_boss_comps', [])) + held)
                        if now - getattr(self, '_held_log', 0) > 10:
                            bit = None
                            try:
                                if held:
                                    bit = struct.unpack('<H', p.read(p.base + held[0] - pad.delta + 0xC4, 2))[0] & 1
                            except OSError:
                                pass
                            self._held_log = now; log(f'AI-pause: {len(held)} kopier på pause -> {ok_} (hopp-bit på første: {bit} – 1 betyr at patchen virker)')
                elif getattr(self, '_held_prev', None):
                    self._held_prev = []; pad.set_ai_hold(p, list(getattr(self, '_boss_comps', [])))
                # Fjern ekstra synk-kopi hvis vårt eget spill også spawnet samme fiende
                used_a = {v[0] for v in m.values()}
                for a, (nm, _f, last) in list(track.items()):
                    if a in used_a or 'Boss' in nm or 'Stalchild' in nm:
                        continue
                    n_mine = sum(1 for _a, (n3, _f3, _l3) in track.items() if n3 == nm and math.dist(_l3, last) < 3.0)
                    n_theirs = sum(1 for x in theirs if x[1] == nm and math.dist(x[2], last) < 3.0)
                    if n_mine > max(1, n_theirs) and any(cn == nm and now - ct < 60 and math.dist(cp, last) < 6.0 for cn, cp, ct in self.__dict__.get('_en_created', [])):
                        track.pop(a, None); pad.delete_actor(p, a)
                        log(f'fiende: slettet ekstra kopi {nm} (har {n_mine}, vennen {n_theirs})')
            except Exception as e:  # noqa: BLE001
                log(f'fiende: feil {e!r}')
            finally:
                self._en_busy = False
        threading.Thread(target=run, daemon=True).start()

    def _actor_tick(self, now):
        """Borte hos én = borte hos begge: fiender, krukker, steiner … som forsvinner sendes til vennen, som sletter sin."""
        if now - getattr(self, '_ac_tick', 0) < 1.0 or getattr(self, '_ac_busy', False) or not (self.p and self.ready):
            return
        if now - getattr(self.pad, '_banc_since', 0) < 10.0:   # rommet lastes ennå
            return
        self._ac_tick = now; self._ac_busy = True
        fresh = bool(self.friend and now - self.friend_t < 2)
        same = fresh and self.pad.cur_banc and self.pad.friend_banc == self.pad.cur_banc
        their_gone = list((self.friend or {}).get('gone') or []) if same else []
        def run():
            try:
                pad, p = self.pad, self.p
                banc = pad.cur_banc
                cur = pad.scan_actors(p)
                if cur is None:
                    return
                track = self.__dict__.setdefault('_ac_track', {})
                if getattr(self, '_ac_banc', None) != banc:
                    track.clear(); self._ac_banc = banc   # ny sone: start på nytt, ikke send noe
                else:
                    out = self.__dict__.setdefault('gone_out', [])
                    gone_now = [a for a in list(track) if a not in cur and not pad.actor_alive(p, a)]
                    mass = len(gone_now) > 4
                    if mass:
                        log(f'aktør: {len(gone_now)} forsvant samtidig (omlasting/død) – sender ikke')
                    copies = {v[0] for v in getattr(self, '_en_map', {}).values()}
                    created = getattr(self, '_en_created', [])
                    for a in gone_now:
                        nm, first, last = track.pop(a)
                        if 'Scrub_Deku_Brothers' in nm or 'Scrub_Deku_Leaf' in nm or 'Gohma' in nm:
                            continue   # puslespill-scrubs gjemmer seg og kommer tilbake – ikke død
                        if a in copies or any(cn == nm and math.dist(cp, first) < 6.0 for cn, cp, ct in created):
                            continue   # vår egen kopi forsvant (f.eks. skjelett som graver seg ned) – ikke slett vennens ekte
                        if True:
                            if same and not mass and a not in pad.__dict__.get('self_deleted', ()):
                                self._gone_seq = getattr(self, '_gone_seq', 0) + 1
                                out.append([self._gone_seq, banc, nm, [round(v, 1) for v in last]])
                                del out[:-30]
                                log(f'aktør: {nm} borte her ved {tuple(round(v) for v in last)} – sender til vennen')
                # v0.94.268: vår kopi ble drept fordi vennen drepte fienden -> spillet ruller sin egen drop her også.
                # Vennens drop er den ekte (plukkes den opp, deles beløpet via de delte tellerne). Slett vår ekstra.
                kz = self.__dict__.setdefault('_kill_zones', [])
                kz[:] = [z for z in kz if now - z[1] < 8.0 and z[2] == banc]
                if kz:
                    for a, (nm, pos) in list(cur.items()):
                        if a in track or nm not in pad.DROP_NAMES:
                            continue
                        if any(math.dist(pos, z[0]) < 4.0 for z in kz):
                            r_ = pad.delete_actor(p, a); cur.pop(a, None)
                            log(f'loot: slettet ekstra {nm} ved synket drap (vennen har den ekte) -> {r_}')
                for a, (nm, pos) in cur.items():
                    if a in track:
                        track[a] = (nm, track[a][1], pos)
                    else:
                        track[a] = (nm, pos, pos)
                done = self.__dict__.setdefault('_gone_done', set())
                for seq, gbanc, nm, gpos in their_gone:
                    key = (self.friend_session, seq)
                    if key in done or gbanc != banc:
                        continue
                    done.add(key)
                    best = None
                    for a, (n2, first, last) in track.items():
                        if n2 == nm:
                            dd = min(math.dist(first, gpos), math.dist(last, gpos))
                            if dd < 6.0 and (best is None or dd < best[0]):
                                best = (dd, a)
                    if best:
                        ad = self._actor_hp_addr(p, best[1]) if nm.startswith('Enemy_') else None
                        if ad:   # drep med liv 0: spillets egen død (dropp, animasjon) – tryggere enn sletting
                            try:
                                p.write(p.base + ad[0], struct.pack('<I', 0)); r = 'liv 0'
                                self.__dict__.setdefault('_kill_zones', []).append((tuple(track[best[1]][2]), now, banc))
                            except OSError:
                                r = pad.delete_actor(p, best[1])
                        else:
                            r = pad.delete_actor(p, best[1])
                        track.pop(best[1], None)
                        log(f'aktør: fjernet {nm} ({best[0]:.1f} m unna) fordi den er borte hos vennen -> {r}')
            except Exception as e:  # noqa: BLE001
                log(f'aktør: feil {e!r}')
            finally:
                self._ac_busy = False
        threading.Thread(target=run, daemon=True).start()

    def _ensure_server_clock(self):
        """PvP-klokken må ikke vente på en blokkert Tk-nett-tick."""
        worker = getattr(self, '_server_clock_worker', None)
        if worker and worker.is_alive():
            return
        def loop():
            while getattr(self, 'mode', 'Story') == 'PvP':
                try:
                    srv = getattr(self, '_server_day_clock', None)
                    if srv and self.p and self.ready and self.pad.hR is not None:
                        day, received = srv
                        fw = int(day + max(0, time.time() - received) * 120) % 86400
                        ft_ = self._pvp_forced_time()
                        if ft_ is not None:
                            fw = ft_
                        self.p.write(self.p.base + self.pad.hR + 0xEF0, struct.pack('<II', fw, 0x4CBE))
                        if self.pad.write_time(self.p, fw):
                            if not getattr(self, '_server_clock_active', False):
                                log(f'tid: World server aktivert {fw // 3600:02d}:{fw % 3600 // 60:02d}')
                            self._server_clock_active = True
                        elif time.time() - getattr(self, '_server_clock_warn', 0) > 30:
                            self._server_clock_warn = time.time()
                            log('tid: kunne ikke skrive serverklokken')
                except Exception as e:  # noqa: BLE001
                    if time.time() - getattr(self, '_server_clock_warn', 0) > 30:
                        self._server_clock_warn = time.time()
                        log(f'tid: servertråd feil {e!r}')
                time.sleep(1.0)
            self._server_clock_active = False
            try:
                if self.p and self.pad.hR is not None:
                    self.p.write(self.p.base + self.pad.hR + 0xEF4, bytes(4))
            except Exception:
                pass
        self._server_clock_worker = threading.Thread(target=loop, daemon=True, name='PvPServerClock')
        self._server_clock_worker.start()

    SERVER_TIME_SCALE = 120   # = TIME_SCALE i server.py

    def _pvp_forced_time(self):
        """v0.94.322: fast klokkeslett (spillsekunder) i arenaer med 'night' – None ellers."""
        if getattr(self, 'mode', 'Story') != 'PvP' or not getattr(self, '_pvp_in_arena', False):
            return None
        t = self.ARENAS.get(getattr(self, '_arena_cur', 'gohma'), {}).get('night')
        if t is None or getattr(self.pad, 'cur_banc', None) != self.PVP_BANC:
            return None
        return int(t) % 86400

    def _time_tick(self, now):
        pvp = getattr(self, 'mode', 'Story') == 'PvP'
        # v0.94.54: PvP-bakgrunnsskriving er midlertidig rullet tilbake etter gjentatt heng på begge PC-er.
        if now - getattr(self, '_wt_tick', 0) < 2.0 or getattr(self, '_wt_busy', False) or not (self.p and self.ready):
            return
        self._wt_tick = now; self._wt_busy = True
        host = False if pvp else self._time_host()
        fresh = bool(self.friend and now - self.friend_t < 2)
        srv_st = getattr(self, '_server_state', None) or {}
        srv_dt = srv_st.get('day_time') if now - getattr(self, '_server_seen', 0) < 5.0 else None
        # v0.94.303: serverklokka går 120 spillsek. per ekte sek. – regn verdien fram til nå (før kunne den være 1–3 s
        # gammel = 2–6 spillminutter bak, og klokka ble «rettet» med et hopp hvert 15. s)
        srv_time = (int(float(srv_dt) + max(0.0, min(5.0, now - getattr(self, '_server_seen', now))) * self.SERVER_TIME_SCALE) % 86400
                    if isinstance(srv_dt, (int, float)) else None)
        srv_ww = srv_st.get('weather') if now - getattr(self, '_server_seen', 0) < 5.0 else None
        srv_ww = int(srv_ww) if isinstance(srv_ww, int) and 0 <= srv_ww < len(PadLink.WEATHERS) else None
        fw = srv_time if srv_time is not None else ((self.friend or {}).get('wtime') if fresh and not pvp else None)
        if pvp and self._pvp_forced_time() is not None:   # v0.94.322: natt-arena
            srv_time = fw = self._pvp_forced_time()
        fww = srv_ww if srv_ww is not None else ((self.friend or {}).get('wweather') if fresh and not pvp else None)
        def run():
            try:
                if self.pad.hR is not None and not pvp:
                    self.p.write(self.p.base + self.pad.hR + 0xEF4, bytes(4))
                    self._server_clock_active = False
                mine = self.pad.read_time(self.p); self._my_wtime = mine
                mw = self.pad.read_weather(self.p); self._my_wweather = mw
                # v0.94.290: innendørs (f.eks. Deku-treet) setter spillet været tilbake rett etter at vi skrev det. Å skrive
                # på nytt hvert 15. s ga en evig 5 s lysovergang (Link/dukker «flimret»). Etter 2 tilbakestillinger i
                # samme sone lar vi været være til neste sonebytte.
                zone_ = getattr(self.pad, 'cur_banc', None)
                wr_ = self.__dict__.setdefault('_ww_revert', {'zone': None, 'n': 0, 'last': None})
                if wr_['zone'] != zone_:
                    wr_.update(zone=zone_, n=0, last=None)
                if wr_['last'] is not None and mw != wr_['last'] and fww != mw:
                    wr_['n'] += 1; wr_['last'] = None
                    if wr_['n'] == 2:
                        log(f'vær: spillet setter {PadLink.WEATHERS[mw]} i {zone_} (innendørs?) – slutter å skrive vær her')
                if (srv_ww is not None or not host) and fww is not None and mw is not None and fww != mw and wr_['n'] < 2 and time.time() - getattr(self, '_ww_set_t', 0) > 15:
                    self._ww_set_t = time.time(); wr_['last'] = fww
                    first = not getattr(self, '_ww_synced', False); self._ww_synced = True
                    if self.pad.write_weather(self.p, fww, 0 if first else 5):
                        log(f'vær: satt til {"serverens" if srv_ww is not None else "vertens"} {PadLink.WEATHERS[fww]} (var {PadLink.WEATHERS[mw]})')
                if mine is not None:
                    vtxt = {0: 'sunny', 1: 'rain', 2: 'snow', 3: 'storm', 4: 'cloudy'}.get(mw, '?')
                    self.set_check('clock', 'ok', f'{mine // 3600:02d}:{mine % 3600 // 60:02d} {vtxt}')
                else:
                    self.set_check('clock', 'off', 'unknown')
                fw_ = fw
                if fw_ is not None and mine is not None and (srv_time is not None or (not pvp and not host)):
                    if srv_time is not None:   # tiden som har gått siden avlesningen over (spillkall kan ta litt tid)
                        fw_ = (fw_ + int((time.time() - now) * self.SERVER_TIME_SCALE)) % 86400
                    d = abs(fw_ - mine); d = min(d, 86400 - d)
                    if d > 120:   # v0.94.303: små rettinger (før 300 = 5 spillmin. hopp); logg bare store / et sammendrag
                        if self.pad.write_time(self.p, fw_):
                            src = 'serverens' if srv_time is not None else 'vertens'
                            st_ = self.__dict__.setdefault('_wt_stat', [0, 0, time.time()])
                            st_[0] += 1; st_[1] = max(st_[1], d)
                            if d > 900:
                                log(f'tid: satt til {src} {fw_ // 3600:02d}:{fw_ % 3600 // 60:02d} (var {mine // 3600:02d}:{mine % 3600 // 60:02d})')
                            elif time.time() - st_[2] > 300:
                                log(f'tid: {st_[0]} små rettinger mot {src} klokke siste {int(time.time() - st_[2])} s (størst {st_[1]} spillsek.)')
                                st_[:] = [0, 0, time.time()]
            except Exception as e:  # noqa: BLE001
                log(f'tid: feil {e!r}')
            finally:
                self._wt_busy = False
        threading.Thread(target=run, daemon=True).start()

    def _flagbits_due(self):
        b = getattr(self, '_fl_bits', None); now = time.time()
        if b and (b != getattr(self, '_fl_sent_b', None) or now - getattr(self, '_fl_sent_t', 0) > 5.0):
            self._fl_sent_b = b; self._fl_sent_t = now
            return b
        return None

    def _ensure_puppet_smoother(self):
        if getattr(self, '_puppet_smoother_thr', None) is None:
            thr = threading.Thread(target=self._puppet_smooth_loop, daemon=True, name='PuppetSmooth60Hz')
            self._puppet_smoother_thr = thr
            thr.start()
        if getattr(self, '_puppet_anim_thr', None) is None:
            athr = threading.Thread(target=self._puppet_anim_loop, daemon=True, name='PuppetAnim60Hz')
            self._puppet_anim_thr = athr
            athr.start()

    def _puppet_anim_loop(self):
        """Ren 60 Hz skjelett-oppdatering (0 game_call) – blokkeres aldri av PUPPET_STEP."""
        _clock = getattr(time, 'perf_counter', time.time)
        next_t = _clock()
        while True:
            next_t += 1.0 / 60.0
            rem = next_t - _clock()
            if rem < -0.1:
                next_t = _clock()
                rem = 1.0 / 60.0
            time.sleep(max(0.001, rem))
            try:
                ctx = getattr(self, '_puppet_smooth_ctx', None)
                if not ctx or not getattr(self, 'ready', False):
                    continue
                p, zone, assigned, _parked, targets = ctx
                if self.p is not p:
                    continue
                pad = self.pad
                now = time.time()
                if (not zone or getattr(pad, 'cur_banc', None) != zone
                        or now - getattr(pad, '_banc_since', now) < 3
                        or now < getattr(pad, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN):
                    pad.publish_puppet_pose_owners(p, ())
                    continue
                fr = getattr(self, 'friend', None)
                f_apos_60 = fr.get('apos') if isinstance(fr, dict) and now - getattr(self, 'friend_t', 0) < 2.0 else None
                if isinstance(f_apos_60, list) and len(f_apos_60) == 3:
                    for fa_, (fnm_, _f1, _fl) in list(getattr(self, '_ac_track', {}).items()):
                        if fnm_.startswith('Enemy_') and 'Drop' not in fnm_ and 'Boss' not in fnm_ and 'Gohma' not in fnm_:
                            pad.sync_enemy_slot0_pos(p, fa_, f_apos_60)
                # v0.94.230: glattet 60 Hz boss-pin (pos + rot) med streng vt+state==4 sjekk
                b_smooth = self.__dict__.setdefault('_boss_pin_smooth', {})
                b_rsmooth = self.__dict__.setdefault('_boss_rot_smooth', {})
                act_vt_60 = ((pad.main + pad.ACT_VT) & 0xFFFFFFFFFFFFFFFF) if pad.main is not None else None
                for ba_, (bx8_, bpos_, brot_, bt_) in list(getattr(self, '_boss_pins', {}).items()):
                    if now - bt_ < 0.5 and act_vt_60 is not None:
                        try:
                            hdr_ = p.read(p.base + ba_, 0x30)
                            if len(hdr_) != 0x30 or struct.unpack_from('<Q', hdr_, 0)[0] != act_vt_60 or struct.unpack_from('<I', hdr_, 0x2C)[0] != 4:
                                b_smooth.pop(ba_, None); b_rsmooth.pop(ba_, None); continue
                        except OSError:
                            b_smooth.pop(ba_, None); b_rsmooth.pop(ba_, None); continue
                        prev_p = b_smooth.get(ba_)
                        if prev_p is None or math.dist(prev_p, bpos_) > 4.0:
                            sp = bpos_
                        else:
                            sp = (prev_p[0] + (bpos_[0] - prev_p[0]) * 0.28,
                                  prev_p[1] + (bpos_[1] - prev_p[1]) * 0.28,
                                  prev_p[2] + (bpos_[2] - prev_p[2]) * 0.28)
                        b_smooth[ba_] = sp
                        sr = brot_
                        if brot_ and len(brot_) == 9:
                            prev_r = b_rsmooth.get(ba_)
                            if prev_r is not None:
                                rr = [prev_r[i] + (brot_[i] - prev_r[i]) * 0.28 for i in range(9)]
                                # Re-normaliser de tre 3D-radene
                                sr_list = []
                                for r0 in (0, 3, 6):
                                    n_ = math.sqrt(rr[r0] * rr[r0] + rr[r0 + 1] * rr[r0 + 1] + rr[r0 + 2] * rr[r0 + 2])
                                    if n_ > 1e-4:
                                        sr_list.extend((rr[r0] / n_, rr[r0 + 1] / n_, rr[r0 + 2] / n_))
                                    else:
                                        sr_list.extend(brot_[r0:r0 + 3])
                                sr = tuple(sr_list)
                            b_rsmooth[ba_] = sr
                        pad.move_actor(p, ba_, bx8_, sp, sr)
                    else:
                        b_smooth.pop(ba_, None); b_rsmooth.pop(ba_, None)
                fr_name = fr.get('name') if isinstance(fr, dict) and now - getattr(self, 'friend_t', 0) < 2.0 else None
                server_seen, server_frames = getattr(self, '_server_peer_frames', (0.0, {}))
                if now - server_seen > 0.5:
                    server_frames = {}
                active_entries = []
                owners = []
                for name, actor in assigned.items():
                    t = targets.get(name)
                    if not t:
                        continue
                    pos, _yaw, anim, bones = t
                    peer = server_frames.get((name, zone), {})
                    if isinstance(peer.get('bones'), str):
                        bones = peer['bones'] or bones
                    if name == fr_name:
                        f_apos = fr.get('apos')
                        f_bones = fr.get('bones')
                        if isinstance(f_apos, list) and len(f_apos) == 3:
                            pos = f_apos
                        if isinstance(f_bones, str) and f_bones:
                            bones = f_bones
                    active_entries.append((name, actor, pos, anim, bones))
                    if isinstance(bones, str) and len(bones) == pad.PUPPET_FULL_POSE_LEN:
                        decoded = pad._decode_pose(bones)
                        if decoded is not None and len(decoded[0]) > len(pad.PUPPET_SYNC_BONES):
                            skeleton = pad.actor_bones_host(p, actor)
                            if skeleton is not None:
                                owners.append(skeleton)
                # v0.94.229: 60 Hz skjelett-synk for Gohma – kun når aktøren lever (vt+state==4)!
                b_sp = getattr(self, '_boss_skel_pin', None)
                if b_sp and now - b_sp[3] < 0.5 and isinstance(fr, dict) and act_vt_60 is not None:
                    bb_pkt = fr.get('bb')
                    if isinstance(bb_pkt, list) and len(bb_pkt) == 2 and bb_pkt[0] == b_sp[2]:
                        ba_, b_bh_, b_cnt_, _ = b_sp
                        b_alive = False
                        try:
                            hdr_b = p.read(p.base + ba_, 0x30)
                            b_alive = (len(hdr_b) == 0x30
                                       and struct.unpack_from('<Q', hdr_b, 0)[0] == act_vt_60
                                       and struct.unpack_from('<I', hdr_b, 0x2C)[0] == 4)
                        except OSError:
                            b_alive = False
                        if b_alive:
                            owners.append(b_bh_)
                            b_bases = self.__dict__.setdefault('_boss_skel_bases', {})
                            base_b = b_bases.get(ba_)
                            if base_b is None or len(base_b) != b_cnt_ * 0x60:
                                try:
                                    base_b = p.read(p.base + b_bh_, b_cnt_ * 0x60)
                                    b_bases[ba_] = base_b
                                except OSError:
                                    base_b = None
                            if base_b is not None:
                                posed_b = pad.apply_generic_skeleton(base_b, b_cnt_, bb_pkt[1])
                                if posed_b is not None:
                                    posed_b = pad.smooth_generic_skeleton(ba_, posed_b, b_cnt_, w=0.25)
                                    try:
                                        p.write(p.base + b_bh_, posed_b)
                                    except OSError:
                                        pass
                pad.publish_puppet_pose_owners(p, tuple(owners[:pad.PUPPET_MAX]))
                try:   # v0.94.284: også uten aktive dukker – ellers ble feen hengende i lufta der spilleren forsvant
                    self._coop_fairies(p, now, active_entries, zone)
                except Exception as e_f:  # noqa: BLE001
                    if now - getattr(self, '_fairy_err_t', 0) > 10:
                        self._fairy_err_t = now; log(f'fe: feil {e_f!r}')
                try:   # v0.94.307: Z-sikte-mål på motstanderne
                    self._coop_targets(p, now, active_entries, zone)
                except Exception as e_t:  # noqa: BLE001
                    if now - getattr(self, '_ztgt_err_t', 0) > 10:
                        self._ztgt_err_t = now; log(f'z-mål: feil {e_t!r}')
                try:   # v0.94.291: navneskilt over dukkene
                    self._coop_nameplates(p, now, active_entries, zone)
                except Exception as e_g:  # noqa: BLE001
                    if now - getattr(self, '_glyph_err_t', 0) > 10:
                        self._glyph_err_t = now; log(f'navneskilt: feil {e_g!r}')
                if active_entries:
                    self._animate_puppets(p, now, active_entries, {})
                    # v0.94.244: 3D rød lav-HP-blinking på alle 24 MaterialObj-buffere (+ dirty-flagg 0x0101) på CoopPuppet når spilleren har <= 1 hjerte
                    prev_low_map = self.__dict__.setdefault('_pup_low_hp_prev_map', {})
                    for _it in active_entries:
                        _p_name, _p_act = _it[0], _it[1]
                        _p_peer = server_frames.get((_p_name, zone), {})
                        _fh = _p_peer.get('hearts') if isinstance(_p_peer, dict) else None
                        if _fh is None and _p_name == fr_name and isinstance(fr, dict):
                            _fh = fr.get('hearts')
                        _f_low = isinstance(_fh, (list, tuple)) and len(_fh) >= 2 and isinstance(_fh[0], (int, float)) and 0 < _fh[0] <= 4
                        _prev_low = prev_low_map.get(_p_act, False)
                        if _f_low or _prev_low:
                            prev_low_map[_p_act] = _f_low
                            _blink_due = self.__dict__.setdefault('_pup_blink_due', {})
                            # v0.94.259: egen tråd skriver ~120 Hz (spillet skriver tilbake hvert bilde -> 10 Hz ga flimmer)
                            pad.blink_set_target(p, _p_act, False)   # v0.94.267: 3D lav-HP-blink på dukker droppet (brukeren) – nullstill bare
            except Exception:  # noqa: BLE001
                pass

    # ---------------------------------------------------------------
    # Puppet sample buffer (v0.94.147): tidsbasert interpolasjon
    # ---------------------------------------------------------------
    # Tidligere ble hver ny nettpose behandlet som en ny 33 ms-blende:
    #   old=target, target=ny, alpha=0 -> dukken viste alltid *forrige*
    #   pakke i diskrete hopp (særlig synlig ved 10-20 Hz serverposer).
    # Nå lagres prøver (t, pos, yaw, bones) og gjengis paa en fast
    # "render-tid" = now - forsinkelse, interpolert mellom to proever.
    PUPPET_POSE_BUF_MAX = 32
    PUPPET_POSE_DELAY_MIN = 0.065
    PUPPET_POSE_DELAY_MAX = 0.300
    PUPPET_POSE_DELAY_FACTOR = 1.60

    def _puppet_buf(self):
        # NB:Ikke kall attributten "_puppet_buf" - den skygger metoden.
        return self.__dict__.setdefault('_puppet_buf_data', {})

    def _puppet_buf_lock(self):
        lk = self.__dict__.get('_puppet_buf_lk')
        if lk is None:
            lk = self.__dict__['_puppet_buf_lk'] = threading.Lock()
        return lk

    def _puppet_ingest(self, entries, now):
        """entries: (actor, ident, t_arrival, pos, yaw, bones). Kun nye innhold lagres."""
        buf = self._puppet_buf()
        with self._puppet_buf_lock():
            for actor, ident, t, pos, yaw, bones in entries:
                lst = buf.get(actor)
                if lst is None or (lst and lst[-1][5] != ident):
                    lst = []
                    buf[actor] = lst
                key = (bones or '',
                       round(float(pos[0]), 3), round(float(pos[1]), 3), round(float(pos[2]), 3),
                       round(float(yaw), 4))
                if lst and lst[-1][4] == key:
                    continue
                lst.append((float(t), tuple(float(v) for v in pos), float(yaw), bones or '', key, ident))
                if len(lst) > self.PUPPET_POSE_BUF_MAX:
                    del lst[0]

    def _puppet_delay(self, actor):
        """Adaptiv forsinkelse: ~2.2 x median ankomstintervall (klemt)."""
        buf = self._puppet_buf()
        with self._puppet_buf_lock():
            lst = list(buf.get(actor) or [])
        ints = [lst[i][0] - lst[i - 1][0] for i in range(1, len(lst))]
        ints = [x for x in ints if 0.004 <= x <= 1.5]
        if not ints:
            return self.PUPPET_POSE_DELAY_MIN
        ints.sort()
        med = ints[len(ints) // 2]
        p90 = ints[int((len(ints) - 1) * 0.90)]
        raw_d = max(med * self.PUPPET_POSE_DELAY_FACTOR, p90 * 1.15)
        return max(self.PUPPET_POSE_DELAY_MIN,
                   min(self.PUPPET_POSE_DELAY_MAX, raw_d))

    def _puppet_sample_at(self, actor, rt):
        """Returnerer (forrige, neste, alpha) rundt render-tiden rt."""
        buf = self._puppet_buf()
        with self._puppet_buf_lock():
            lst = list(buf.get(actor) or [])
        if not lst:
            return None
        prev = None
        nxt = None
        for s in lst:
            if s[0] <= rt:
                prev = s
            else:
                nxt = s
                break
        if prev is None:
            return lst[0], lst[0], 0.0
        if nxt is None:
            return prev, prev, 0.0
        span = nxt[0] - prev[0]
        alpha = 0.0 if span <= 1e-6 else (rt - prev[0]) / span
        return prev, nxt, max(0.0, min(1.0, alpha))

    def _puppet_render(self, actor, now):
        """Interpolert (pos, yaw, bones_a, bones_b, alpha, vel, rt) for en dukke."""
        rt = now - self._puppet_delay(actor)
        pair = self._puppet_sample_at(actor, rt)
        if pair is None:
            return None
        prev, nxt, alpha = pair
        pos = tuple(a + (b - a) * alpha for a, b in zip(prev[1], nxt[1]))
        d = ((nxt[2] - prev[2] + math.pi) % (2.0 * math.pi)) - math.pi
        yaw = prev[2] + d * alpha
        span = nxt[0] - prev[0]
        if span > 1e-6:
            vel = tuple((nxt[1][i] - prev[1][i]) / span for i in range(3))
        else:
            vel = (0.0, 0.0, 0.0)
        return pos, yaw, prev[3], nxt[3], alpha, vel, rt

    def _puppet_smooth_loop(self):
        """60 Hz interpolasjon av CoopPuppet_* (posisjon, yaw og 28-beins skjelett) uavhengig av Tkinter-timeren."""
        _clock = getattr(time, 'perf_counter', time.time)
        next_t = _clock()
        while True:
            next_t += 1.0 / 60.0
            rem = next_t - _clock()
            if rem < -0.1:
                next_t = _clock()
                rem = 1.0 / 60.0
            time.sleep(max(0.001, rem))
            try:
                ctx = getattr(self, '_puppet_smooth_ctx', None)
                if not ctx or not getattr(self, 'ready', False):
                    continue
                p, zone, assigned, parked, targets = ctx
                if self.p is not p or not assigned:
                    continue
                pad = self.pad
                now = time.time()
                if (not zone or getattr(pad, 'cur_banc', None) != zone
                        or now - getattr(pad, '_banc_since', now) < 3
                        or now < getattr(pad, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN):
                    continue
                # Hent ferskeste 60 Hz P2P-data fra friend hvis i samme sone
                fr = getattr(self, 'friend', None)
                fr_name = fr.get('name') if isinstance(fr, dict) and now - getattr(self, 'friend_t', 0) < 2.0 else None
                batch = []
                server_seen, server_frames = getattr(self, '_server_peer_frames', (0.0, {}))
                if now - server_seen > 0.5:
                    server_frames = {}
                ingest = []
                render_frames = {}
                for name, actor in assigned.items():
                    t = targets.get(name)
                    if not t:
                        continue
                    pos, yaw, _anim, bones = t
                    stamp = now
                    peer = server_frames.get((name, zone), {})
                    fresh_pos, fresh_yaw = peer.get('pos'), peer.get('yaw')
                    peer_bones = peer.get('bones')
                    if (isinstance(fresh_pos, list) and len(fresh_pos) == 3
                            and all(isinstance(v, (int, float)) and abs(v) <= 1e5 for v in fresh_pos)):
                        pos = fresh_pos
                    if isinstance(fresh_yaw, (int, float)) and abs(fresh_yaw) < 1e5:
                        yaw = fresh_yaw
                    if isinstance(peer_bones, str) and peer_bones:
                        bones = peer_bones
                        stamp = server_seen
                    if name == fr_name:
                        f_apos = fr.get('apos')
                        f_arot = fr.get('arot')
                        f_bones = fr.get('bones')
                        if isinstance(f_apos, list) and len(f_apos) == 3:
                            pos = f_apos
                        if isinstance(f_arot, list) and len(f_arot) >= 3:
                            yaw = math.atan2(f_arot[2], f_arot[0])
                        # v0.94.153: prøvenes tid er senderens (lokal tid), ikke ankomsttiden.
                        stamp = getattr(self, '_friend_sample_t', None) or now
                        if isinstance(f_bones, str) and f_bones:
                            bones = f_bones
                    cur_pos = (float(pos[0]), float(pos[1]), float(pos[2]))
                    cur_yaw = float(yaw)
                    ingest.append((actor, (p, zone, name), stamp, cur_pos, cur_yaw, bones or ''))
                # Ny prøve-liste -> interpolasjon paa fast render-tid
                self._puppet_ingest(ingest, now)
                for name, actor in assigned.items():
                    r = self._puppet_render(actor, now)
                    if r is None:
                        continue
                    render_frames[(name, actor)] = r
                    shown_pos, yaw, _ba, _bb, _al, vel, rt = r
                    if self._puppet_follower_on():
                        fols = getattr(self, '_puppet_followers', None)
                        if fols is None:
                            fols = self._puppet_followers = {}
                        fol = fols.get(actor)
                        if fol is None:
                            fol = fols[actor] = PuppetFollower()
                        # v0.94.160: jeger-modellen (CoopFollow::Follower) i stedet for
                        # a skrive raat posisjonen hvert bilde.
                        shown_pos = fol.step(shown_pos, vel, rt * 1000.0, now * 1000.0)
                        yaw = fol.step_yaw(yaw, now * 1000.0)
                    if name == fr_name:
                        shown_pos = self._deku_web_puppet_contact(p, zone, actor, shown_pos, now)
                    batch.append((actor, shown_pos, yaw))
                for actor in parked:
                    batch.append((actor, (0.0, -2000.0, 0.0), 0.0))
                self._puppet_render_frames = (p, zone, now, render_frames)
                force_mtx = self._puppet_force_mtx()
                if batch and pad.write_puppet_batch(p, [(*entry, force_mtx) for entry in batch]):
                    if force_mtx or not hasattr(pad, 'write_puppet_transforms_direct'):
                        pad.game_call(p, pad.PUPPET_STEP, timeout=0.25)
                    else:
                        pad.write_puppet_transforms_direct(p, batch)
            except Exception:  # noqa: BLE001
                pass

    def _pvp_puppet_tick(self, p, now, peers, zone):
        """Prototype pool. Run on the PadTick worker after the local actor is resolved."""
        pad = self.pad
        if now - getattr(self, '_puppet_tick_t', 0) < 0.03:
            return
        self._puppet_tick_t = now
        if getattr(self, '_puppet_call_proc', None) is not p:
            if not pad.puppet_batch_armed(p):
                return
            self._puppet_call_proc = p
        pool = getattr(self, '_puppet_actors', {})
        owner = (p, zone)
        if getattr(self, '_puppet_owner', None) != owner:
            self._puppet_owner = owner
            self._puppet_scan_t = 0
            self._puppet_spawn_t = 0
            self._puppet_pending_spawn = None
            self._puppet_actors = pool = {}
            self._puppet_assignments = {}
            self._puppet_pose_state = {}
            self._puppet_last_pos = {}
            self._puppet_gear_state = {}      # v0.94.149: ny sone = nytt utstyrsgrunnlag
            self._puppet_gear_pend = {}
            self._puppet_followers = {}       # v0.94.160: ny sone = nye CoopFollow-jegere
            self._puppet_spawn_fails = 0      # v0.94.153: ny sone = ny opprettelses teller
            self._puppet_unconfirmed = {}     # v0.94.314: ny sone = nye forsøk
            self._puppet_unc_logged = set()
            pad.__dict__.get('_bones_cache', {}).clear()
        if (not zone or now - getattr(pad, '_banc_since', now) < 3
                or now < getattr(pad, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN):
            return
        pending = self._puppet_pending_spawn
        scan_interval = 0.25 if pending else 1.0
        if now - self._puppet_scan_t >= scan_interval and (peers or pool):
            self._puppet_scan_t = now
            found = pad._list_actors_raw(p, prefix='CoopPuppet_')
            if found is not None:
                self._puppet_actors = pool = {actor: data[0] for actor, data in found.items()}
                if pending:
                    model, previous_actors = pending[0], pending[1]
                    if any(pool[actor] == model for actor in pool.keys() - previous_actors):
                        self._puppet_pending_spawn = None
                        self._puppet_spawn_t = now
                        self._puppet_spawn_fails = 0      # v0.94.153: bekreftet -> nullstill feil teller

        live = {actor: model for actor, model in pool.items() if pad.actor_alive(p, actor)}
        previous = self._puppet_assignments
        assigned = {
            item[0]: previous[item[0]] for item in peers
            if item[0] in previous and live.get(previous[item[0]]) == item[1]
        }
        reserved = set(assigned.values())
        available = {}
        for actor, model in live.items():
            if actor not in reserved:
                available.setdefault(model, []).append(actor)
        batch = []
        active_entries = []
        missing = None
        for item in peers:
            name, model, pos, yaw = item[0], item[1], item[2], item[3]
            anim = item[4] if len(item) > 4 else ''
            bones = item[5] if len(item) > 5 else ''
            actor = assigned.get(name)
            if actor is None and available.get(model):
                assigned[name] = actor = available[model].pop()
            if actor is not None:
                batch.append((actor, pos, yaw))
                active_entries.append((name, actor, pos, anim, bones))
            elif missing is None:
                missing = (model, pos)
        self._puppet_assignments = assigned
        self._puppet_gear_tick(p, assigned, now)
        # Park unused puppets below the scene rather than destroying actors.
        for slots in available.values():
            batch.extend((actor, (0.0, -2000.0, 0.0), 0.0) for actor in slots)
        self._puppet_smooth_ctx = (p, zone, dict(assigned), [a for slots in available.values() for a in slots],
                                   {item[0]: (item[2], item[3], item[4] if len(item) > 4 else '', item[5] if len(item) > 5 else '')
                                    for item in peers})
        smoother_active = getattr(self, '_puppet_smoother_thr', None) is not None
        if hasattr(self, '_ensure_puppet_smoother'):
            self._ensure_puppet_smoother()
        if not smoother_active:
            wlk = self.__dict__.setdefault('_puppet_write_lk', threading.Lock())
            with wlk:
                if pool or peers:
                    if pad.write_puppet_batch(p, [(*entry, self._puppet_force_mtx()) for entry in batch]):
                        pad.game_call(p, pad.PUPPET_STEP, timeout=0.75)
                if hasattr(self, '_animate_puppets') and getattr(self, '_puppet_anim_thr', None) is None:
                    self._animate_puppets(p, now, active_entries, available)
        if not missing or now < self._puppet_spawn_t:
            return
        if len(pool) < pad.PUPPET_MAX:
            unconfirmed = self._puppet_pending_spawn
            # v0.94.311: vent på at forrige dukke av samme modell dukker opp (maks 10 s) før en ny lages. Før ventet bare
            # Hyrule Field; ellers ble en ny laget etter 3 s og begge ble stående (ekstra Link på GAMER ved fargebytte).
            if (zone != 'HyruleField_Child' and unconfirmed and unconfirmed[0] == missing[0] and len(unconfirmed) > 3
                    and now - unconfirmed[3] < 10.0):   # Hyrule Field: prøver reservepunktet (bro) etter vanlig ventetid
                return
            self._puppet_pending_spawn = None
            model, spawn_pos = missing
            # v0.94.314: GAMER2 fant ikke de nye dukkene i aktørlista (levende=0) og laget en ny hvert 10. s – hver ble stående
            # som en ekstra Link. Maks 2 ubekreftede per modell og sone; deretter ingen nye før sonebytte.
            unc = self.__dict__.setdefault('_puppet_unconfirmed', {})
            ukey = (zone, model)
            if any(m_ == model for m_ in pool.values()):
                unc.pop(ukey, None)
            elif unc.get(ukey, 0) >= 2:
                if not self.__dict__.setdefault('_puppet_unc_logged', set()) & {ukey}:
                    self._puppet_unc_logged.add(ukey)
                    log(f'dukkepool: {model} laget {unc[ukey]} ganger i {zone} uten å dukke opp i aktørlista – lager ikke flere her '
                        f'(liste: {getattr(pad, "_list_why", "-")}, lengde {getattr(pad, "_list_len", "-")})')
                return
            # The bridge entrance previously materialized 49 puppets. Alternate
            # to it if a request at the peer's position didn't materialize.
            fallback = (198.18, 163.38, 309.63)
            alternate = (zone == 'HyruleField_Child' and unconfirmed and unconfirmed[0] == model
                         and unconfirmed[2] != fallback)
            if alternate:
                spawn_pos = fallback
            result = pad.create_actor(p, model, spawn_pos)
            if result and zone != 'HyruleField_Child':
                unc[ukey] = unc.get(ukey, 0) + 1
            if result:
                self._puppet_pending_spawn = (model, set(pool.keys()), spawn_pos, now)
            # v0.94.153: begrens opprettelsesløkka. Uten bekreftelse blir hvert
            # opprettelseskall et tregt spillkall (flere sekunder), og modden henger
            # (nett-tikken falt til 0.3/s). Nå går vi 3 s -> 10 s -> 30 s -> 60 s.
            self._puppet_spawn_fails = (getattr(self, '_puppet_spawn_fails', 0) or 0) + 1
            fails = self._puppet_spawn_fails
            delay = 3.0 if fails <= 2 else (10.0 if fails <= 4 else (30.0 if fails <= 6 else 60.0))
            self._puppet_spawn_t = time.time() + (delay if result else max(delay, 15.0))
            log(f'dukkepool: {missing[0]} oppretting={result!r}, '
                f'levende={len(live)}, pool={len(pool)}, mål={len(peers)}, reservepunkt={bool(alternate)}, '
                f'spawn=({spawn_pos[0]:.1f},{spawn_pos[1]:.1f},{spawn_pos[2]:.1f}), sone={zone}, '
                f'feil={fails}, neste om {self._puppet_spawn_t - time.time():.0f} s, '
                f'spillkall={getattr(pad, "_last_call_err", None)}')
        else:
            # Wait for the actor list to confirm removal before creating a replacement.
            victim = next((slots[-1] for slots in available.values() if slots), None)
            if victim is not None:
                result = pad.delete_actor(p, victim)
                self._puppet_spawn_t = time.time() + (3.0 if result else 15.0)
                log(f'dukkepool: frigjør ledig {live[victim]} for {missing[0]}: {result!r}')

    def _peer_gear(self):
        """Utstyr per spiller fra P2P-pakken: 'wp' = navn på våpen-aktørene, 'wd' = de i hånda.

        EquipmentUser-kindene (docs/puppet.md): 0 = våpen (sverd), 6 = skjold, 11 = verktøy.
        Håndslot: 0 = sverd, 4 = skjold.
        """
        out = {}
        fr = getattr(self, 'friend', None)
        if not isinstance(fr, dict):
            return out
        name = fr.get('name')
        names = fr.get('wp')
        if not isinstance(name, str) or not name or not isinstance(names, (list, tuple)):
            return out
        drawn = fr.get('wd') if isinstance(fr.get('wd'), (list, tuple)) else []
        sword = shield = stick = None
        for nm in names:
            if not isinstance(nm, str) or 'Sheath' in nm or 'Bundle' in nm:
                continue
            if nm.startswith('Weapon_Sword'):
                sword = nm
            elif nm.startswith('Weapon_Shield'):
                shield = nm
            elif 'DekuStick' in nm or nm.startswith('Item_DekuStick'):
                stick = nm
        items = []
        if sword:
            items.append((0, 0, sword, sword in drawn))
        elif stick:
            items.append((0, 0, stick, stick in drawn))
        if shield:
            items.append((6, 4, shield, shield in drawn))
        if stick and sword:
            items.append((11, 5, stick, stick in drawn))
        if items:
            out[name] = items
        return out

    def _puppet_gear_tick(self, p, assigned, now):
        """Vekter dukkenes sverd/skjold i hånda (EquipmentUser-tilstand).

        v0.94.149: stykket ligger allerede i dukkenes slotter (EquipmentUserRef i pakken),
        men i tilstand 'lagt vekk' (byte 0x04). Før v0.94.149 ble equip()-kallet brukt,
        men det avvises (retur 0) når stykket allerede er på.

        v0.94.150: **equip()-kallet (0x2df7b20) er fjernet helt.** Gjentatte kall mot
        dukkenes EquipmentUser hang begge PC-ene (lokal frøs etter ~20 min, peer etter
        ~10 min, begge ganske nær en rom-omlasting). Spillet fryser med status=1 i
        kall-kassen, 0 FPS og svart skjerm. Dukken bærer uansett EquipmentUserParam sine
        egne stykker (sverd i slot 0, skjold i slot 4), så det eneste som mangler er
        tilstanden 'i hånda' – og den settes med 0xE34C40, som er trygg.

        Alle spillkall er vakket av: aktørens levende-status, gyldig eu, avstand til siste
        rom-omlasting, og en pause hvis spillet ikke svarer.

        v0.94.151: tilstanden leses med spillets egen lesing (0xCE7AB0) i stedet for
        request-byten på eu+0x13BC. Byten er bare et flyktig ønske som spillet nuller
        straks det er utført (docs/puppet.md), så den viste «i hånda» selv når
        stykket lå på ryggen. Nå spør vi bare om endring når spillet faktisk er
        i en annen tilstand enn det vi vil ha – én slot per runde.
        """
        if now - getattr(self, '_puppet_gear_t', 0) < 0.6:
            return
        self._puppet_gear_t = now
        gear = self._peer_gear()
        if not gear or not assigned:
            return
        pad = self.pad
        # Rom-omlasting river ut EquipmentUser-en: ikke rør dukkenes utstyr i overgangsvinduet.
        if now - getattr(self, '_last_reload_t', 0) < 8.0:
            return
        if now - getattr(pad, '_banc_since', now) < 3.0:
            return
        if now < getattr(pad, '_tp_t', 0) + CALL_TELEPORT_COOLDOWN:
            return
        if now < getattr(self, '_gear_pause_t', 0):
            return
        state = self.__dict__.setdefault('_puppet_gear_state', {})
        pending = []
        for peer_name, actor in assigned.items():
            items = gear.get(peer_name)
            if not items:
                continue
            if not pad.actor_alive(p, actor):
                continue
            if not pad.actor_equipment_user(p, actor):
                continue
            for kind, slot, nm, drawn in items:
                key = (actor, slot)
                want = 1 if drawn else 2
                piece, sid = pad.actor_equip_slot(p, actor, slot)
                if not piece:
                    # Sloten er tom: ingenting å flytte (og intet å kalle på).
                    if state.get(key) != ('tom', None):
                        state[key] = ('tom', None)
                        log(f'dukke-utstyr: {peer_name} slot {slot} er tom (ville hatt {nm})')
                    continue
                pending.append((peer_name, actor, slot, want, nm, key))
        if not pending:
            return
        # v0.94.151: Én slot per runde (spillkall er dyre), og den der ønsket
        # tilstand nettopp endret seg prioriteres. Tilstanden leses med spillets
        # egen lesing (0xCE7AB0) – request-byten er bare et flyktig ønske.
        best = None
        best_due = None
        for item in pending:
            _pn, _ac, _sl, want, _nm, key = item
            last = state.get(key)
            changed = bool(last) and last[0] != want
            checked = last[2] if (last and len(last) > 2) else 0.0
            due = 0.0 if changed else checked + 2.0
            if best_due is None or due < best_due:
                best_due = due
                best = item
        if best is None or best_due > now:
            return
        peer_name, actor, slot, want, nm, key = best
        last = state.get(key)
        st = pad.actor_equip_state_read(p, actor, slot)
        if st is None:
            self._gear_pause_t = now + 5.0
            return
        if st == want:
            state[key] = (want, last[1] if last else now, now)
            return
        r = pad.actor_equip_state(p, actor, slot, want)
        if r is None:
            self._gear_pause_t = now + 10.0
            log(f'dukke-utstyr: spillet svarer ikke ({getattr(pad, "_last_call_err", None)}) – utstyr pauses i 10 s')
            return
        piece, _sid = pad.actor_equip_slot(p, actor, slot)
        cur = pad.actor_piece_name(p, piece)
        pstate = pad.actor_piece_state(p, piece)
        log(f'dukke-utstyr: {peer_name} slot {slot} -> {"i hånda" if want == 1 else "vekk"} '
            f'(spillets tilstand {st}, stykke {cur!r} tilstand {pstate})')
        state[key] = (want, now, now - 1.5)

    def _animate_puppets(self, p, now, active_entries, available):
        """Oppdater skjelettet (309 * 0x60 LocalMtx) på CoopPuppet_* med spillets egne bein (eller fallback) uten game_call."""
        pad = self.pad
        frames = pad.ensure_puppet_anim_frames(p)
        if frames is None:
            return
        wait_frame, run_frames, attack_frames = frames
        pose_state = self.__dict__.setdefault('_puppet_pose_state', {})
        last_pos = self.__dict__.setdefault('_puppet_last_pos', {})
        for item in active_entries:
            name, actor, pos = item[0], item[1], item[2]
            anim = item[3] if len(item) > 3 else ''
            bones_b64 = item[4] if len(item) > 4 else ''
            bh = pad.actor_bones_host(p, actor)
            if bh is None:
                continue
            if bones_b64:
                # v0.94.147: tidsbasert interpolasjon fra sample-bufferen.
                # (Tidligere: 33 ms 'restart-blend' per pakke -> diskrete hopp.)
                render = getattr(self, '_puppet_render_frames', None)
                r = None
                if render is not None and render[0] is p and render[1] == pad.cur_banc and abs(now - render[2]) < 0.12:
                    r = render[3].get((name, actor))
                if r is None and hasattr(self, '_puppet_render'):
                    r = self._puppet_render(actor, now)
                if r is not None:
                    _rpos, _ryaw, old_b, target_b, alpha = r[0], r[1], r[2], r[3], r[4]
                    old_b = old_b or bones_b64
                    target_b = target_b or bones_b64
                else:
                    old_b = target_b = bones_b64
                    alpha = 1.0
                key = ('bones', name, bh, target_b, round(alpha, 2))
                st = pose_state.get(actor)
                if st is not None and st[0] == key and now - st[1] < 2.0:
                    continue
                if hasattr(pad, 'apply_interpolated_pose'):
                    real_frame = pad.apply_interpolated_pose(wait_frame, old_b, target_b, alpha)
                else:
                    real_frame = pad.apply_packed_pose(wait_frame, bones_b64)
                if real_frame is not None:
                    if hasattr(pad, 'smooth_puppet_skeleton'):
                        real_frame = pad.smooth_puppet_skeleton(actor, real_frame)
                    try:
                        p.write(p.base + bh, real_frame)
                        pose_state[actor] = (key, now)
                        continue
                    except OSError:
                        pass
            prev = last_pos.get(name)
            moved = False
            if prev is not None:
                prev_pos, prev_t, prev_move_t = prev
                dist = math.hypot(pos[0] - prev_pos[0], pos[2] - prev_pos[2])
                dy_climb = abs(pos[1] - prev_pos[1])
                if dist > 0.04 or dy_climb > 0.03:
                    moved = True
                    last_pos[name] = (pos, now, now)
                else:
                    moved = (now - prev_move_t) < 0.32
                    last_pos[name] = (prev_pos, now, prev_move_t)
            else:
                last_pos[name] = (pos, now, 0.0)
            an_low = (anim or '').lower()
            is_attack = any(k.lower() in an_low for k in self.PVP_SWING)
            is_run = moved or ('run' in an_low or 'walk' in an_low or 'move' in an_low or 'dash' in an_low)
            if is_attack:
                idx = int((now * 16.0) + (actor & 7)) % len(attack_frames)
                key = ('attack', idx)
                frame = attack_frames[idx]
            elif is_run:
                idx = int((now * 14.0) + (actor & 15)) % len(run_frames)
                key = ('run', idx)
                frame = run_frames[idx]
            else:
                key = ('wait', 0)
                frame = wait_frame
            st = pose_state.get(actor)
            if st is None or st[0] != key or (now - st[1]) >= 2.0:
                try:
                    p.write(p.base + bh, frame)
                    pose_state[actor] = (key, now)
                except OSError:
                    pass
        # Sørg også for at ledige dukker i poolen får hvile-skjelett én gang slik at de aldri starter i T-pose.
        init_budget = 2
        for slots in available.values():
            for actor in slots:
                if init_budget <= 0:
                    return
                if actor in pose_state:
                    continue
                bh = pad.actor_bones_host(p, actor)
                if bh is None:
                    continue
                try:
                    p.write(p.base + bh, wait_frame)
                    pose_state[actor] = (('wait', 0), now)
                    init_budget -= 1
                except OSError:
                    pass

    def _pad_tick_async(self, now, alive):
        """PadLink inneholder native spillkall og må aldri blokkere Tk-nett-ticken."""
        if self.p is None or getattr(self, '_pad_tick_busy', False):
            return
        self._pad_tick_busy = True
        p = self.p
        puppets = bool(getattr(self, 'cfg', {}).get('pvp_puppet_pool', True))
        zone = getattr(self.pad, 'cur_banc', None) if puppets else None
        peers = []
        is_pvp = getattr(self, 'mode', 'Story') == 'PvP'
        match = (getattr(self, '_server_state', {}).get('lobby') or {}) if puppets else {}
        p2p_alive = alive
        if puppets:
            alive = False  # Bruk 50-spiller CoopPuppet_* + 28-beins animasjon for alle spillere (Story + PvP).
            if getattr(self.pad, 'c_act', None) is not None and not getattr(self.pad, '_deleting', False) and now - getattr(self.pad, '_last_del_try', 0) > 3.0:
                self.pad._delete_link2(p)
        friend_obj = (getattr(self, 'friend', None) or {}) if p2p_alive else {}
        friend_name = friend_obj.get('name')
        friend_bones = friend_obj.get('bones')
        friend_apos = friend_obj.get('apos')
        friend_arot = friend_obj.get('arot')
        friend_yaw = math.atan2(friend_arot[2], friend_arot[0]) if (isinstance(friend_arot, list) and len(friend_arot) >= 3) else None
        seen = {getattr(self, 'name', None)}
        if puppets and now - getattr(self, '_server_seen', 0) < 5:
            lobby = match.get('id') if is_pvp else None
            for peer in getattr(self, 'pvp_peers', ()):
                name = peer.get('name') if isinstance(peer, dict) else None
                if not isinstance(name, str) or not name or name in seen:
                    continue
                if (is_pvp and (lobby is None or peer.get('lobby') != lobby)) or peer.get('zone') != zone:
                    continue
                pos, yaw = peer.get('pos'), peer.get('yaw')
                if name == friend_name and isinstance(friend_apos, list) and len(friend_apos) == 3:
                    pos = friend_apos
                if name == friend_name and friend_yaw is not None:
                    yaw = friend_yaw
                if not (isinstance(pos, list) and len(pos) == 3 and
                        all(isinstance(v, (int, float)) and abs(v) <= 1e5 for v in pos)):
                    continue
                color = (peer.get('team') if is_pvp else None) or peer.get('model')
                model = color if color in LOOKS else 'Green'
                anim = peer.get('anim') if isinstance(peer.get('anim'), str) else ''
                bones = peer.get('bones') if isinstance(peer.get('bones'), str) else ''
                if name == friend_name and isinstance(friend_bones, str) and friend_bones:
                    bones = friend_bones
                entry = (name, f'CoopPuppet_{model}', tuple(pos),
                         yaw if isinstance(yaw, (int, float)) and abs(yaw) < 1e5 else 0.0)
                if bones:
                    peers.append((*entry, anim, bones))
                elif anim:
                    peers.append((*entry, anim))
                else:
                    peers.append(entry)
                seen.add(name)
                if len(peers) >= self.pad.PUPPET_MAX - 1:
                    break
        server_fresh = now - getattr(self, '_server_seen', 0) < 5
        channel_names = (getattr(self, '_server_state', {}) or {}).get('present') or []
        if (puppets and not is_pvp and zone and friend_obj.get('banc') == zone
                and (not server_fresh or friend_name in channel_names)
                and isinstance(friend_name, str) and friend_name and friend_name not in seen
                and isinstance(friend_apos, list) and len(friend_apos) == 3
                and all(isinstance(v, (int, float)) and abs(v) <= 1e5 for v in friend_apos)
                and len(peers) < self.pad.PUPPET_MAX - 1):
            model = friend_obj.get('look')
            if model not in LOOKS:
                model = 'Green'
            anim = friend_obj.get('anim')
            peers.append((friend_name, f'CoopPuppet_{model}', tuple(friend_apos), friend_yaw or 0.0,
                          anim if isinstance(anim, str) else '',
                          friend_bones if isinstance(friend_bones, str) else ''))
        def run():
            try:
                self.pad.tick(p, now, alive=alive)
                if hasattr(self.pad, 'read_my_packed_pose'):
                    b64 = self.pad.read_my_packed_pose(p)
                    if b64:
                        self._my_bones_b64 = b64
                if (puppets and self.p is p and zone and getattr(self.pad, 'cur_banc', None) == zone
                        and not getattr(self, '_pvp_travel_busy', False)):
                    self._pvp_puppet_tick(p, now, peers, zone)
            except Exception as e:  # noqa: BLE001
                import traceback
                log(f'pad-tick: feil {e!r}\n{traceback.format_exc()}')
            finally:
                self._pad_tick_busy = False
        threading.Thread(target=run, daemon=True, name='PadTick').start()

    def _net_tick(self):
        now = time.time()
        self._ctf_server_tick(now)
        self._deku_web_tick(now)
        sk = SKIP | ({'ammo', 'equip', 'flag', 'actor', 'enemy', 'floor', 'boss', 'box'} if getattr(self, 'mode', 'Story') == 'PvP' else set())
        for nm in ('time', 'ammo', 'equip', 'flag', 'actor'):
            if nm not in sk:
                getattr(self, f'_{nm}_tick')(now)
        try:
            r_ = self.pad.sync_l2_perception(self.p) if 'perc' not in sk else None
            if r_ != getattr(self, '_perc_last', 'x'):
                self._perc_last = r_; log(f'sanse-posisjon for Link 2: {"oppdateres" if r_ else ("fant ikke komponenten" if r_ is False else "ingen kopi")}')
        except Exception:  # noqa: BLE001
            pass
        if 'boss' not in sk:
            self._boss_tick_async(now)
        self._self_tunic_tick(now)
        self._story_inv_tick(now)
        try:
            self._safe_start_tick(now)
        except Exception as e_ss:  # noqa: BLE001
            log(f'trygg start: feil {e_ss!r}')
        for nm in ('enemy', 'floor', 'box', 'weapon', 'death', 'pvp', 'bot', 'remote'):
            if nm not in sk or nm == 'remote':
                getattr(self, f'_{nm}_tick')(now)
        if getattr(self, 'mode', 'Story') == 'PvP':
            self._navi_tick(now)
        # v0.94.245: Cutscene Sync – når en spiller i samme sone starter en story-cutscene (f.eks. ugla), start samme event her
        if (getattr(self, 'mode', 'Story') == 'Story' and self.peer and self.p and self.ready
                and isinstance(self.friend, dict) and now - getattr(self, 'friend_t', 0) < 3.0
                and self.pad.cur_banc and self.pad.cur_banc == self.pad.friend_banc):
            f_ev = self.friend.get("ev")
            if isinstance(f_ev, str) and len(f_ev) >= 4 and not f_ev.startswith(self.pad.SYNC_EVENT_SKIP_PREFIXES) and not any(x_ in f_ev for x_ in ('BancChange', 'GameOver', 'Death', 'Dead')):   # v0.94.288: Delayed_GameOver hos den som døde ble startet hos vennen
                ev_hist = self.__dict__.setdefault("_ev_sync_hist", {})
                if now - ev_hist.get(f_ev, 0.0) > 25.0 and not getattr(self, "_ev_sync_busy", False):
                    if self.pad.event_busy(self.p) is None:
                        ev_hist[f_ev] = now
                        self._ev_sync_busy = True
                        _p_ev, _ev_nm = self.p, f_ev
                        def _run_ev_sync():
                            try:
                                if self.pad.start_event(_p_ev, _ev_nm):
                                    self.ui(self._append_chat_sys, f"🎬 Cutscene sync: {_ev_nm}")
                            finally:
                                self._ev_sync_busy = False
                        threading.Thread(target=_run_ev_sync, daemon=True).start()
        # v0.94.245: deaktivert automatisk _auto_tvang så ingen teleporteres ufrivillig mellom soner (bruk FOLLOW-knapp/dør)
        if False and (self.tvang and getattr(self, 'mode', 'Story') == 'Story' and self.peer and self.p and self.ready
                and now - getattr(self.pad, "f_time", 0) < 3.0
                and self.pad.cur_banc and self.pad.friend_banc and self.pad.cur_banc != self.pad.friend_banc
                and self.pad.friend_banc in self.pad.START_POS
                and now - getattr(self.pad, "_banc_since", 0) > 8.0
                and now - getattr(self, "_last_tvang_t", 0) > 12.0):
            self._last_tvang_t = now
            _p, _tb = self.p, self.pad.friend_banc
            def _auto_tvang():
                if self.pad.change_banc(_p, _tb):
                    self.pad.suppress_warp_until = time.time() + 20
                    self.ui(self._append_chat_sys, f"🌀 TVANG: følger etter til {_tb} …")
            threading.Thread(target=_auto_tvang, daemon=True).start()
        if getattr(self.pad, 'learned_new', False):
            self.pad.learned_new = False
            self.cfg['start_pos'] = {k: v for k, v in self.pad.START_POS.items() if PadLink.START_POS.get(k) != v}
            save_cfg(self.cfg)
            self._append_chat_sys(f'📍 Now knows {len(self.pad.START_POS)} zones for FOLLOW / /tp')
        try:   # vakthund: henger hovedtråden > 8 s, skriv alle trådenes stakker til logs/<PC>-heng.txt
            import faulthandler
            if getattr(self, "_stall_f", None) is None:
                self._stall_f = open(os.path.join(APP_DIR, "logs", f"{PC}-heng.txt"), "a")
            faulthandler.cancel_dump_traceback_later()
            faulthandler.dump_traceback_later(8, repeat=False, file=self._stall_f)
        except Exception:
            pass
        if now - self.last_hello > 1:
            self.last_hello = now
            hello = json.dumps({"t": "hello", "s": self.session, "name": self.name, "v": VERSION,
                                "color": self.hat_color, "banc": self.pad.cur_banc or "",
                                "look": getattr(self, "look", "") or ""}).encode()
            for dst in ("255.255.255.255",):
                try:
                    self.ds.sendto(hello, (dst, self.dport))
                except OSError:
                    pass
        while True:
            try:
                data, addr = self.ds.recvfrom(2048)
            except OSError:
                break
            try:
                m = json.loads(data)
            except ValueError:
                continue
            if m.get("t") == "hello" and m.get("s") != self.session:
                self.players[addr[0]] = (m.get("name", "?"), now, m.get("s"), m.get("color"),
                                         m.get("banc") or "", m.get("look") or "")
        # auto-tilkobling: én annen spiller og ingen valgt ennå
        live = {ip: v for ip, v in self.players.items() if now - v[1] < 4}
        if self.peer is None and len(live) == 1:
            self.connect(next(iter(live)))
        live = dict(sorted(live.items()))
        self._live_ips = list(live)
        items = [connected_line(v[0], v[4] if len(v) > 4 else "", v[5] if len(v) > 5 else "", mode=getattr(self, "mode", "Story")) for v in live.values()]
        items.append(connected_line(self.name, self.pad.cur_banc, getattr(self, "look", ""), you=True, mode=getattr(self, "mode", "Story")))
        srv_list = None
        if now - getattr(self, "_server_seen", 0) < 5:
            srv_list = (getattr(self, "_server_state", None) or {}).get("present")
        if srv_list is not None:   # PvP/Story: serveren er sannheten om hvem som er koblet til
            friend = self.friend or {}
            peers = {}
            if friend.get("name"):
                peers[friend["name"]] = {
                    "zone": friend.get("banc") or "",
                    "model": friend.get("look") or "",
                    "mode": getattr(self, "mode", "Story"),
                    "hearts": friend.get("hearts"),
                }
            roster = (getattr(self, "_server_state", None) or {}).get("roster")
            items = connected_items(srv_list, roster, self.name, self.pad.cur_banc, getattr(self, "look", ""), peers,
                                    self_mode=getattr(self, "mode", "Story"),
                                    self_hearts=getattr(self, "_my_hearts_last", None))
            t = f"Connected ({len(srv_list)})"
        else:
            t = "Connected"
        # v0.94.234: oppdater Story-modus Boss-HP-boks (0 ekstra minnelesing)
        if getattr(self, "mode", "Story") != "PvP" and hasattr(self, "boss_name_lbl"):
            b_ent = None
            for src in (getattr(self, "_my_boss", None) or (), ((self.friend or {}).get("boss") or ())):
                for ent in src:
                    if isinstance(ent, (list, tuple)) and len(ent) >= 5:
                        bnm = str(ent[0])
                        if "Boss" in bnm and "Egg" not in bnm and "Larva" not in bnm and "Child" not in bnm:
                            b_ent = ent; break
                if b_ent:
                    break
            if b_ent:
                bnm, bhp, bmx = str(b_ent[0]), b_ent[3], b_ent[4]
                nice_map = {"Enemy_DungeonBoss_Gohma": "Queen Gohma", "Enemy_DungeonBoss_KingDodongo": "King Dodongo"}
                nice = nice_map.get(bnm) or bnm.replace("Enemy_DungeonBoss_", "").replace("Enemy_", "").replace("_", " ")
                hp_i = max(0, int(bhp)) if isinstance(bhp, (int, float)) else 0
                mx_i = max(1, int(bmx)) if isinstance(bmx, (int, float)) and bmx > 0 else max(1, hp_i)
                if hp_i > 0:
                    self._boss_dead_t = None
                elif getattr(self, "_boss_dead_t", None) is None:
                    self._boss_dead_t = now
                hide_dead = (hp_i == 0 and getattr(self, "_boss_dead_t", None) is not None and now - self._boss_dead_t >= 5.0)
                if hide_dead:
                    if getattr(self, "_boss_card_shown", False):
                        self._boss_card_shown = False; self._boss_ui_last = None
                        self.boss_outer.pack_forget()
                else:
                    if not getattr(self, "_boss_card_shown", False):
                        self.boss_outer.pack(fill="x", padx=14, pady=4, before=self._status_row)
                        self._boss_card_shown = True
                    frac = max(0.0, min(1.0, hp_i / mx_i))
                    tgt = getattr(self, "_boss_aggro_name", None) or (self.name if self._time_host() else ((self.friend or {}).get("name") or ""))
                    tgt_s = f"   ·   🎯 {tgt}" if (hp_i > 0 and tgt) else ""
                    state_key = (nice, hp_i, mx_i, tgt_s)
                    if state_key != getattr(self, "_boss_ui_last", None):
                        self._boss_ui_last = state_key
                        self.boss_name_lbl.config(text=f"👑 {nice}", fg=GOLD if hp_i > 0 else MUTED)
                        self.boss_hp_lbl.config(text=(f"{hp_i} / {mx_i} HP{tgt_s}" if hp_i > 0 else "Defeated!"),
                                                fg=HEART if hp_i > 0 else "#65c97a")
                    bw = max(1, self.boss_bar.winfo_width())
                    self.boss_bar.coords(self._boss_bar_rect, 0, 0, int(bw * frac), 14)
            elif getattr(self, "_boss_card_shown", False):
                self._boss_card_shown = False
                self._boss_ui_last = None
                self._boss_dead_t = None
                self.boss_outer.pack_forget()
        if self._conn_title.cget("text") != t:
            self._conn_title.config(text=t)
        if list(self.plist.get(0, "end")) != items:
            self.plist.delete(0, "end")
            for it in items:
                self.plist.insert("end", it)
        # v0.94.239: blink rødt i Connected-lista når en spiller har <= 1 hjerte (hearts[0] <= 4)
        blink_on = (int(now * 2.5) % 2) == 0
        if srv_list is not None:
            for idx_i, nm_i in enumerate(srv_list):
                if idx_i >= self.plist.size():
                    break
                h_i = getattr(self, "_my_hearts_last", None) if nm_i == self.name else (peers.get(nm_i) or {}).get("hearts")
                low_hp = isinstance(h_i, (list, tuple)) and len(h_i) >= 2 and isinstance(h_i[0], (int, float)) and 0 < h_i[0] <= 4
                self.plist.itemconfig(idx_i, foreground=("#ff4444" if (low_hp and blink_on) else (HEART if low_hp else FG)))
        else:
            for i, v in enumerate(live.values()):
                self.plist.itemconfig(i, foreground=HAT_COLORS.get(v[3] if len(v) > 3 else None, FG))
            self.plist.itemconfig(len(live), foreground=HAT_COLORS.get(getattr(self, "hat_color", None), FG))
        if getattr(self, "conn_popup_list", None) is not None:
            try:
                if self.conn_popup_title is not None and self.conn_popup_title.cget("text") != t:
                    self.conn_popup_title.config(text=t)
                if list(self.conn_popup_list.get(0, "end")) != items:
                    self.conn_popup_list.delete(0, "end")
                    for i in range(self.plist.size()):
                        self.conn_popup_list.insert("end", self.plist.get(i))
                        self.conn_popup_list.itemconfig(i, foreground=self.plist.itemcget(i, "foreground") or FG)
            except tk.TclError:
                pass

        me = None
        my_hearts = None
        if self.ready:
            try:
                apos = self.pad.my_apos(self.p)
                arot = self.pad.my_arot(self.p)
                if apos and arot:
                    me = (apos[0], apos[1] + 0.56, apos[2], arot[6], arot[8])
                else:
                    fx, _, fz = self.p.f32(self.pos_off - 16, 3)
                    me = (*self.p.f32(self.pos_off, 3), fx, fz)
                if getattr(self, 'mode', 'Story') == 'PvP':   # v0.93: eget inventar i PvP – ingen telling/deling
                    vals, bag_vals, bag_cums = {}, {}, {}
                else:
                    vals = {n: c.tick() for n, c in self.syncs.items()}
                    bag_vals, bag_cums = self.bag.tick(now) if getattr(self, "bag", None) else ({}, {})
                try:
                    h_cur = self.p.u32(self.rupees.off + 0x28)
                    h_max = self.p.u32(self.rupees.off + 0x50)
                    if 0 <= h_cur <= 80 and 4 <= h_max <= 80:
                        my_hearts = [h_cur, h_max]
                        self._my_hearts_last = my_hearts
                except OSError:
                    pass
                if now - getattr(self, "_learn_t", 0) > 0.5:
                    self._learn_t = now
                    learn_table(self.p, self.rupees.off, self.learn_state, now)
            except OSError:
                self.ready = False
        my_cam_a = self.pad.my_cam_angle(self.p, self.cam_off) if self.p is not None else None
        if self.peer and me:
            _rx = getattr(self, "_rx_pt", None)
            _pe = [_rx[0], round(time.time() - _rx[1], 4)] if _rx else None   # ekko av vennens tidsstempel + hvor lenge vi holdt det
            msg = {"t": "state", "s": self.session, "pt": round(time.time(), 4), "pe": _pe, "name": self.name, "color": self.hat_color, "banc": self.pad.cur_banc,
                   "pos": list(me[:3]), "face": list(me[3:]),
                   "apos": self.pad.my_apos(self.p), "arot": self.pad.my_arot(self.p), "cam_a": my_cam_a,
                   "hearts": my_hearts,
                   "follow": bool(getattr(self, 'tvang', False)),
                   "ev": self.pad.read_active_event(self.p) if getattr(self, 'mode', 'Story') == 'Story' else None,
                   "dan": getattr(self, '_my_death_an', None),
                   "mode": getattr(self, 'mode', 'Story'),
                   "bot": getattr(self, '_my_bot', None),
                   "pvpd": getattr(self, '_pvp_deaths', 0),
                   "ctfl": [t for t, lit in getattr(self, '_ctf_lit', {}).items() if lit],
                   "cum": self.rupees.my_cum, "rupees": vals.get("rupees"),   # v0.4-kompatibelt
                   "cums": {n: c.my_cum for n, c in self.syncs.items()}, "vals": vals, "ce": getattr(self, 'cnt_epoch', 0),
                   "bag": bag_vals, "bag_cums": bag_cums,
                   "bag_delta": sorted(self.bag.delta) if getattr(self, "bag", None) else [],
                   "bag_ignored": sorted(self.bag.ignored) if getattr(self, "bag", None) else [],
                   "pad": self.pad.my_pad(self.p),
                   "wtime": getattr(self, '_my_wtime', None) if self._time_host() else None,
                   "wweather": getattr(self, '_my_wweather', None) if self._time_host() else None,
                   "look": getattr(self, 'look', 'No tunic'),
                   "gone": getattr(self, 'gone_out', [])[-30:],
                   "enem": getattr(self, '_my_enem', None),
                   "flr": getattr(self, '_my_floors', None),
                   "web": getattr(self, '_web_out', None),
                   "wy": getattr(self, '_my_web_y', None),
                   "wt": getattr(self, '_my_web_target', None),
                   "box": getattr(self, '_my_boxes', None),
                   "boss": getattr(self, '_my_boss', None),
                   "bt": getattr(self, '_my_boss_target', None) if self._time_host() else None,
                   "bb": getattr(self, '_my_boss_bones', None),
                   "bst": getattr(self, '_my_bst', None),
                   "eq": getattr(self, '_my_eq', None),
                   "eqv": getattr(self, '_my_eqv', 0),
                   "wp": getattr(self, '_my_wp', None),
                   "wd": getattr(self, '_my_wdrawn', None),
                   "hm": getattr(self, 'host_mode', 'auto'),
                   "bf": self._in_boss_fight(),
                   "rb": getattr(self, '_rb_ver', 0),
                   "l2d": getattr(self.pad, 'l2_dmg_total', 0),
                   "pvph": getattr(self, '_pvp_hit_total', 0),
                   "rock": getattr(self, '_my_rock', None),   # v0.94.316: sverd-banens kule (leder -> følger)
                   "tk": [h for h, t in getattr(self, '_en_claims', {}).items() if t > time.time()][:24],
                   "it": getattr(self, '_my_item', None),
                   "dr": getattr(self, '_my_drawn', None),
                   "db": getattr(self, '_draw_btn', None),
                   "bones": getattr(self, '_my_bones_b64', None),
                   "chat": list(self.chat_out)}
            _fb = self._flagbits_due()
            if _fb:
                msg["flagbits"] = _fb   # bare når den er ny eller hvert 5. s (vennen beholder forrige)
            # v0.94.303: mindre state-pakker. (1) Posisjon/rotasjon/bein/kontroller går allerede 60 Hz i «fast» – mottakeren
            # ignorerer dem i state når fast er fersk, så de sendes ikke her da. (2) Bare endrede felt; full pakke hvert
            # 1. s (mottakeren slår sammen med dict.update, så manglende felt beholder forrige verdi; tapt pakke rettes innen 1 s).
            if time.time() - getattr(self, '_fast_sent_t', 0) < 0.3:
                for k_ in ('pos', 'face', 'apos', 'arot', 'cam_a', 'pad', 'bones'):
                    msg.pop(k_, None)
            last_ = getattr(self, '_st_last', None)
            full_ = last_ is None or now - getattr(self, '_st_full_t', 0) >= 1.0 or last_.get('s') != msg.get('s')
            self._st_last = dict(msg)
            if full_:
                self._st_full_t = now
            else:
                msg = {k_: v_ for k_, v_ in msg.items() if k_ in ('t', 's', 'pt', 'pe', 'name') or last_.get(k_, msg) != v_}
            try:
                _pk = json.dumps(msg, separators=(',', ':')).encode(); self.gs.sendto(_pk, self.peer)
                perf_add('state-B', len(_pk))
            except OSError:
                pass
        self._drain_udp(now)
        alive = bool(self.friend and now - self.friend_t < 2) and self._server_says_friend_present(now)
        roster = (getattr(self, '_server_state', None) or {}).get('roster') or []
        follow_locked = follow_locked_by_peer(self.friend if alive else None, roster, self.name)
        if bool(self.names_var.get()) != bool(self.cfg.get('nameplates', True)):
            self.names_var.set(bool(self.cfg.get('nameplates', True)))
        if follow_locked != getattr(self, '_follow_remote_locked', None):
            self._follow_remote_locked = follow_locked
            self.follow_cb.config(state=('disabled' if follow_locked else 'normal'),
                                  disabledforeground=MUTED, fg=(MUTED if follow_locked else FG))
            if follow_locked:
                log('FOLLOW: låst fordi en annen spiller har aktivert det')
        if alive:
            self._maybe_send_assets()
        if self.p is not None and 'pad' not in SKIP:
            self._pad_tick_async(now, alive)
        if alive != getattr(self, '_was_alive', False):
            self._was_alive = alive
            fname = self.friend.get('name') if self.friend else '?'
            log(f"venn {'tilkoblet' if alive else 'mistet'}: {fname} {self.peer}")
            self._append_chat_sys(f"{fname} {'connected!' if alive else 'disconnected.'}")
        if self.peer:
            self.set_check("net", "ok" if alive else "work",
                           f"{self.friend.get('name')} ({self.peer[0]})" if alive else f"waiting for {self.peer[0]} …")
        return me, alive

    # ------------------------------------------------------------ hovedløkke
    def _tick(self):
        try:
            self._tick_body()
        except Exception as e:  # noqa: BLE001 – hovedløkka skal aldri dø
            if time.time() - getattr(self, '_tick_err_t', 0) > 10:
                self._tick_err_t = time.time()
                log(f'hovedløkke-feil: {e!r}\n{traceback.format_exc()}')
            self.root.after(33, self._tick)

    def _tick_body(self):
        while not self.ui_q.empty():
            fn, a = self.ui_q.get_nowait()
            try:   # v0.94.307: en feil i en UI-jobb (f.eks. /here uten venn) stoppet hele hovedløkka for godt
                fn(*a)
            except Exception as e:  # noqa: BLE001
                log(f'ui-jobb feilet: {e!r}\n{traceback.format_exc()}')
        _t0 = time.perf_counter()
        try:
            me, alive = self._net_tick()
        except Exception as e:  # noqa: BLE001
            if time.time() - getattr(self, '_net_tick_err_t', 0) > 10:
                self._net_tick_err_t = time.time()
                log(f'nett-tick feilet: {e!r}\n{traceback.format_exc()}')
            self.root.after(33, self._tick)
            return
        perf_add('nett-tick', time.perf_counter() - _t0)
        try:
          if 'figure' not in SKIP:
            self.figure.tick(self.p if self.ready else None, self.friend, alive, time.time(), me,
                             bool(self.cfg.get("figur_folg_meg")))
        except Exception as e:  # noqa: BLE001 – figuren skal aldri ta ned resten
            if not getattr(self, "_fig_err", None):
                log(f"figur-feil: {e!r}")
            self._fig_err = True
        _t1 = time.perf_counter()
        self._draw(me, alive)
        try:
            self._overlay_tick(me, alive)
        except Exception as e:  # noqa: BLE001 – markøren skal aldri ta ned resten
            if not getattr(self, "_ov_err", None):
                log(f"markør-feil: {e!r}")
            self._ov_err = True
        perf_add('tegning+markør', time.perf_counter() - _t1)
        perf_report()
        self.root.after(33, self._tick)

    def _overlay_tick(self, me, alive):
        if self.overlay is None:
            self.overlay = Overlay(self.root)
        ov = self.overlay
        ov.clear()
        reason = self._overlay_draw(ov, me, alive)
        # Diagnose i loggen hvert 15. s mens en venn er tilkoblet (for feilsøking på begge PC-er)
        now = time.time()
        if alive and now - getattr(self, "_ov_log_t", 0) > 15:
            self._ov_log_t = now
            log(f"markør: {reason}")

    def _overlay_draw(self, ov, me, alive):
        """Tegner markøren. Returnerer en kort tekst om hva som skjedde (til loggen)."""
        if not self.marker_var.get():
            return "slått av i vinduet"
        now = time.time()
        peers = ()
        if now - getattr(self, "_server_seen", 0) < 5:
            peers = getattr(self, "pvp_peers", ())
        if not ((alive or peers) and me and self.ready and self.p):
            return "venter på venn/spill"
        if self.cam_off is None:
            return "kamera ikke funnet ennå" + (" (søker)" if self.cam_scanning else "")
        if self.lwin is None or now - self.lwin_t > 2:
            self.lwin, self.lwin_t = lichii_window(self.p.pid), now
        if not self.lwin:
            return "fant ikke Lichii-vinduet"
        if u32w.IsIconic(self.lwin):
            return "Lichii er minimert"
        fg = u32w.GetForegroundWindow()
        if fg != self.lwin and fg != u32w.GetParent(self.root.winfo_id()):
            return "Lichii er ikke aktivt vindu (tegner ikke over andre programmer)"
        rect = game_rect(self.lwin)
        if not rect:
            return "ugyldig vindusstørrelse"
        cam = read_cam(self.p, self.cam_off)
        friend = self.friend if alive else None
        friend_name = friend.get("name") if friend else None
        for peer in peers:
            pname = peer.get("name")
            ppos = peer.get("pos")
            if not pname or pname in (self.name, friend_name) or not (isinstance(ppos, list) and len(ppos) == 3):
                continue
            pdist = math.dist(me[:3], ppos)
            pcol = {"Blue": "#4a90e2", "Red": "#e25555"}.get(peer.get("team")) or HAT_COLORS.get(peer.get("color"), ACC)
            psx, psy, pon = project(cam, (ppos[0], ppos[1] + MARKER_HEIGHT, ppos[2]), rect)
            ov.draw_friend(psx, psy, pon, pname, pdist, hat_hex=pcol)
        if not friend:
            return "tegnet spillere fra PvP-serveren"
        fp = self.friend["pos"]
        dist = math.dist(me[:3], fp)
        name = self.friend.get("name", "venn")
        f_col = HAT_COLORS.get(self.friend.get("color"), ACC)
        if self.ghost_var.get():
            ff = self.friend.get("face") or [0.0, 1.0]
            fn = math.hypot(ff[0], ff[1]) or 1.0
            sf = project(cam, (fp[0], fp[1], fp[2]), rect)
            sh = project(cam, (fp[0], fp[1] + GHOST_HEIGHT, fp[2]), rect)
            if sf[2] and sh[2] and sf[1] - sh[1] > 6:
                sd = project(cam, (fp[0] + ff[0] / fn * 0.9, fp[1], fp[2] + ff[1] / fn * 0.9), rect)
                ov.draw_ghost(sf, sh, sd if sd[2] else None, name, dist, hat_hex=f_col)
                return (f"skyggefigur ({sf[0]:.0f},{sf[1]:.0f}), høyde {sf[1] - sh[1]:.0f} px, {dist:.0f} m, "
                        f"spillbilde {tuple(round(v) for v in rect)}, kamera guest+0x{self.cam_off:X}")
        sx, sy, on = project(cam, (fp[0], fp[1] + MARKER_HEIGHT, fp[2]), rect)
        ov.draw_friend(sx, sy, on, name, dist, hat_hex=f_col)
        return (f"tegnet {'på skjermen' if on else 'i kanten'} ({sx:.0f},{sy:.0f}), {dist:.0f} m, "
                f"spillbilde {tuple(round(v) for v in rect)}, kamera guest+0x{self.cam_off:X}")

    def _draw_net(self, alive):
        """Nettverkspanelet: status, venn, ping, pakker/s, sone."""
        if not hasattr(self, "net_lbls"):
            return
        now = time.time()
        if now - getattr(self, "_net_draw_t", 0) < 0.5:
            return
        dt = now - getattr(self, "_net_draw_t", now - 0.5); self._net_draw_t = now
        rate = (getattr(self, "_rx_count", 0) - getattr(self, "_rx_count_last", 0)) / max(dt, 0.1)
        self._rx_count_last = getattr(self, "_rx_count", 0)
        L = self.net_lbls
        pvp = getattr(self, 'mode', 'Story') == 'PvP'
        srv_label = SERVER_URL.replace('https://', '').replace('http://', '').strip('/') if SERVER_URL else f"{SERVER_ADDR[0]}:{SERVER_ADDR[1]}"
        self.net_key_lbls["ip"].config(text="Server")
        L["ip"].config(text=srv_label, fg=FG)
        srv_alive = (now - getattr(self, "_server_seen", 0) < 5)
        if alive or srv_alive:
            L["state"].config(text="● Connected", fg=OK)
        elif self.peer:
            L["state"].config(text="● Waiting for reply", fg=WARN)
        else:
            L["state"].config(text="● Not connected", fg=MUTED)
        pm = getattr(self, "ping_ms", None)
        if alive and pm is not None:
            L["ping"].config(text=f"{pm:.0f} ms", fg=OK if pm < 30 else (WARN if pm < 100 else "#ff6b6b"))
        else:
            L["ping"].config(text="–", fg=MUTED)
        L["rate"].config(text=f"{rate:.0f} in/s", fg=FG if alive else MUTED)
        hm = {"auto": "Auto", "me": "Me", "friend": "Friend"}[getattr(self, "host_mode", "auto")]
        host_row = getattr(self, "net_rows", {}).get("host")
        if pvp:
            # Server-raden viser allerede .121. Kampverten står i lobbykortet.
            if host_row is not None and host_row.winfo_manager():
                host_row.grid_remove()
        else:
            if host_row is not None and not host_row.winfo_manager():
                host_row.grid()
        if not pvp and alive:
            who = "You" if self._time_host() else ((self.friend or {}).get("name") or "Friend")
            L["host"].config(text=f"{who}  ({hm} – click to change)", fg=GOLD)
        elif not pvp:
            L["host"].config(text=f"–  ({hm} – click to change)", fg=MUTED)
        if "zone" in L:
            z = self.pad.cur_banc or "–"
            fz = self.pad.friend_banc
            same = bool(fz and z == fz)
            L["zone"].config(text=(z.replace("_Child", "").replace("_Adult", "") + (" (same)" if same else (" (friend: other)" if fz else ""))),
                             fg=OK if same else FG)

    def _draw(self, me, alive):
        lines = []
        self._draw_net(alive)
        self._draw_lobby()
        if alive and self.friend:
            f = self.friend
            fcol = f.get("color", "Blå")
            self.peer_color_lbl.config(text=f"● {f.get('name', 'Friend')} ({COLOR_EN.get(fcol, fcol)})", fg=HAT_COLORS.get(fcol, ACC))
            if me and f.get("pos"):
                x, y, z = me[:3]
                dx, dy, dz = f["pos"][0] - x, f["pos"][1] - y, f["pos"][2] - z
                dist = math.hypot(dx, dz)
                lines.append(f"Distance to {f.get('name')}: {dist:.1f} m ({'above' if dy > 0 else 'below'} you by {abs(dy):.1f} m)")
        else:
            self.peer_color_lbl.config(text="Offline", fg=MUTED)

        if self.ready:
            # Liv / Hjerter (Deg)
            try:
                h_cur = self.p.u32(self.rupees.off + 0x28)
                h_max = self.p.u32(self.rupees.off + 0x50)
                if 0 <= h_cur <= 80 and 4 <= h_max <= 80:
                    full_h = max(1, round(h_max / 4))
                    cur_h = max(0.0, min(float(full_h), h_cur / 4.0))
                    bars = "♥" * int(round(cur_h)) + "♡" * max(0, full_h - int(round(cur_h)))
                    self.hearts_lbl.config(text=f"♥ You: {bars} ({cur_h:g}/{full_h})", fg="#5cdb5c" if cur_h > 1 else "#ff5c5c")
                else:
                    self.hearts_lbl.config(text="♥ You: ♥♥♥♥", fg="#5cdb5c")
            except OSError:
                pass

            # Liv / Hjerter (Venn)
            if alive and self.friend:
                fh = self.friend.get("hearts")
                fname = self.friend.get("name", "Venn")
                if fh and len(fh) == 2 and 0 <= fh[0] <= 80 and 4 <= fh[1] <= 80:
                    f_full = max(1, round(fh[1] / 4))
                    f_cur = max(0.0, min(float(f_full), fh[0] / 4.0))
                    f_bars = "♥" * int(round(f_cur)) + "♡" * max(0, f_full - int(round(f_cur)))
                    warn = " ⚠️" if f_cur <= 1.0 else ""
                    self.friend_hearts_lbl.config(text=f"♥ {fname}: {f_bars} ({f_cur:g}/{f_full}){warn}",
                                                  fg="#ff3b3b" if f_cur <= 1.0 else "#5cdb5c")
                else:
                    self.friend_hearts_lbl.config(text=f"♥ {fname}: connected", fg="#5cdb5c")
            else:
                self.friend_hearts_lbl.config(text="♥ Friend: offline", fg=MUTED)

            fv = (self.friend.get("vals") or {"rupees": self.friend.get("rupees")}) if (alive and self.friend) else {}
            item_parts = []
            for name, _rel, _cap, label in ITEMS:
                if name in self.syncs:
                    c = self.syncs[name]
                    extra = f" (friend: {fv[name]})" if name in fv else ""
                    item_parts.append(f"{label}: {c.expected}/{c.cap()}{extra}")
            lines.extend(item_parts)
            if getattr(self, "bag", None):
                lines.append(f"Shared inventory: {self.bag.owned()} items/upgrades ({len(self.bag.delta)} consumables)")
        else:
            self.hearts_lbl.config(text="♥ Life: waiting for game …")
            if not lines:
                lines.append("Start Lichii and load your save file to sync.")
        if getattr(self, 'mode', 'Story') == 'PvP':
            sc = getattr(self, '_server_score', {'Blue': 0, 'Red': 0})
            online = time.time() - getattr(self, '_server_seen', 0) < 4.0
            srv_label = SERVER_URL.replace('https://', '').replace('http://', '').strip('/') if SERVER_URL else f"{SERVER_ADDR[0]}:{SERVER_ADDR[1]}"
            srv = f'connected to {srv_label}  ·  round {getattr(self, "_server_round", 1)}' if online else f'server offline  ·  {srv_label}'
            lines.insert(0, f'🔥 Capture the Flame  Blue {sc["Blue"]} – {sc["Red"]} Red\n🌐 {srv}')
            fk = (self.friend or {}).get('pvpd', 0) if self.friend else 0
            lines.insert(0, f"⚔️ PvP  You {fk} – {getattr(self, '_pvp_deaths', 0)} {(self.friend or {}).get('name', 'Friend')}")
        self.status.config(text="\n".join(lines))


def main():
    try:
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        k32.CreateMutexW.restype = wt.HANDLE
        _mtx = k32.CreateMutexW(None, False, "OoTCoop_OoTMultiplayerGUI_v1")
        if ctypes.get_last_error() == 183:
            log("avslutter: annen OoT_Multiplayer-instans kjører allerede")
            return
    except (AttributeError, OSError):
        _mtx = None
    try:
        u32w.SetProcessDPIAware()   # ekte piksler, så markøren treffer på skjermer med skalering
    except (AttributeError, OSError):
        pass
    root = tk.Tk()
    # v0.94.307: Tk-feil gikk til stderr (finnes ikke i exe-en) – nå til loggen
    root.report_callback_exception = lambda et, ev, tb: log('tk-feil: ' + ''.join(traceback.format_exception(et, ev, tb)))
    try:
        _app = App(root)
        def _close():
            try:
                _app._server_bye()
            finally:
                root.destroy()
        root.protocol('WM_DELETE_WINDOW', _close)
    except OSError as e:
        tk.messagebox.showerror("Zelda Multiplayer", f"Kunne ikke starte: {e}\nKjører programmet allerede?")
        return
    root.mainloop()


if __name__ == "__main__":
    main()
