#!/usr/bin/env python3
"""hypderive.py WORK LIB OUT [--tag NAME]: derive every DIFFERS value of OUT/hyplist[-TAG].tsv (hyplist.py) from the
target image and the unit's own definitions, and look for image-dependent donor values kept in hypothesis positions.
proves no function (kind: measurement). Read-only for WORK, LIB and the images.

Per DIFFERS row the first rule that applies decides (each rule's text is written into the row):
  KNOWN          a value the owner already decided (table KNOWN below); recorded, not re-decided
  SHWIN          SH_LO / SH_HI of a format-string shadow window: the unit's own rule `hull_zero rd x n` (window =
                 [shadow(x)/8*8, shadow(x+n-1)/8*8+8)) with x = the unit's FMT and n = the length the unit's lemma passes to
                 hull_zero; shadow(a) = a/8 + 0x7fff8000
  SHSPAN         the length of the image's shadow, (page-up image top - 0x10000) / 8, next to its base shadow(0x10000)
  COUNT          a count of start-up image regions: length IMG_REGIONS of the start-up file LIB/A/AD2j.v (+ 2 for
                 PM_tailL): OK / WRONG when LIB's file reads the pin e89be137db17, else NEEDS-STARTUP (a stand-in)
  CONTENT        the value a memory fact states for a file-backed read-only target address (lit1/lit4/lit8, flit*, lits8,
                 mkChunk A (CVal N (SLit V)), val_mem _ _ A N V, (A, n, [(off, w%N, V)])): the N bytes of the target image
                 at the written address; for a relative jump-table entry the destination (table base + entry) is named in
                 both images
  ADDRESS        imgs.derive: an image quantity (IMAGE-QTY: a bound or size, or it / 8 or / 4096) or donor symbol +
                 offset -> target symbol + offset (BOUND, GOT, SYMBOL, SYMBOL-ALIGNED, SYMBOL-RANK, BYTES, JTABLE; shadow
                 addresses through unshadow)
  NEW            no donor position: decided by hand (table NEWHAND, each with its derivation); a numeral below 0x10000
                 (no address) on a line a G patch added (EV/g-*.patch, env EV) -> OK, rule GPATCH; else OPEN
A row no rule decides is OPEN (reported, never guessed).
SAME rows: a value in the donor image's range [0x10000, page-up top] or the donor image's shadow, or equal to a donor
image size (>= 0x1000), is derived as an address; when the target value differs it is KEPT-IMAGE unless the table
CONST below (decided by hand, each with its reason) names it as a constant by role, or it is a RISC-V instruction word
(`Definition NAME : bv 32 := V`). CONTENT is also checked on SAME rows.
Output: OUT/differs[-TAG].tsv, OUT/kept[-TAG].tsv, OUT/content[-TAG].tsv, OUT/hypvalues[-TAG].txt.
"""
import collections
import csv
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import imgs  # noqa: E402

# the four images, relative to the named image trees TIMG (fuzz_transport: stripped/, unstripped/) and PG (fuzz_grant:
# bin/, unstripped/); HV_<key> gives one image directly. No host path is written here.
PINS = {
    "T": (("TIMG", "stripped/fuzz_transport.asan"), "e89be137db17"),
    "TT": (("TIMG", "unstripped/fuzz_transport.asan"), "86efc3a80314"),
    "D": (("PG", "bin/fuzz_grant/fuzz_grant.asan"), "c2c7559b29bd"),
    "DT": (("PG", "unstripped/fuzz_grant/fuzz_grant.asan"), "57c26f993615"),
}

# decided by the owner (the task brief); recorded as such, not re-decided
KNOWN = [
    (lambda r: r["written"] in ("0x800b9c00", "2148244480") and r["donor"] in ("0x80050000",),
     "KNOWN (owner): the CZONE bound 0x800b9c00 = kLowShadowBeg 0x7fff7000 (Reusable/YG0f.v:22) + IMG_TOP 0x616000 / 8, the "
     "least shadow start of the secondary map that map_facts SM1 (A/AFjm.v:305) allows; the goal of A/AFju.v:663 needs it; "
     "above the highest constant shadow end 0x800b663c"),
    (lambda r: r["file"] == "A/AFek.v" and r["written"] == "131072",
     "KNOWN (owner): (aTOT, mkAF 2 131072 0) is kept as cgif's slack range; it holds the post-store value TOT + length tr "
     "+ 1 <= 127039 (tr_len A/AFem.v:122, store A/AFem.v:1247)"),
    (lambda r: r["file"] == "A/AFem.v" and r["written"] == "127008",
     "KNOWN (owner): A/AFem.v TOT_range 127008 is a goal, not a hypothesis"),
]

# NEW rows (no donor position) decided by hand: (file, written) -> (verdict, derivation)
NEWHAND = {
    ("A/AF0l.v", "0x3dd04"): ("OK", "pc_stack_malloc entry of class 5 (A/AF0l.v:13; the file's notice, line 4, says the side-stack "
                                    "entries were added): the target's __asan_stack_malloc_5 starts at 0x3dd04 (size 0x20c); the "
                                    "donor has no __asan_stack_malloc_5; the other entries follow the same rule cid k -> "
                                    "__asan_stack_malloc_k (0x3d698, 0x3d80c, 0x3d99c, 0x3db38 = classes 0, 1, 2, 4)"),
    ("A/AF0l.v", "5"): ("OK", "the class id of that entry (cid =? 5 -> __asan_stack_malloc_5)"),
}


def g_added():
    """file -> {line the G patches (EV/g-<f>.patch, env EV) add (trailing blanks dropped): the patch}"""
    out = {}
    ev = os.environ.get("EV")
    if not ev or not os.path.isdir(ev):
        return out
    for p in sorted(os.listdir(ev)):
        if not (p.startswith("g-") and p.endswith(".patch")):
            continue
        cur = None
        for ln in open(os.path.join(ev, p), errors="replace").read().split("\n"):
            if ln.startswith("+++ "):
                cur = ln[4:].split("\t")[0].strip()
                out.setdefault(cur, {})
            elif cur and ln.startswith("+"):
                out[cur][ln[1:].rstrip()] = p
    return out


GADD = g_added()

# SAME values in the donor image's range that are constants by role (decided by hand from each listed row's text)
CONST = {
    65538: "arithmetic bound of clz_index (18 <= p <= 65538, a range of the lemma's variable p); no image address",
    73728: "allocator size bound (aMS, mkAF 73728 ...): 0x12000 bytes; an allocator constant of the model",
    100000: "a list-length bound / fuel (length P < 100000, do_recycle 100000%nat)",
    131071: "string-length bound 2^17 - 1 of the printf/write leaf specs (length p <= 131071)",
    131072: "2^17: a model size (quarantine / depot mapping QSv + 131072, chunk-size atom rCSZ <= 131072, "
            "kPtrArrayCommit); equal to the donor's load0 page size only by chance (aTOT row: KNOWN)",
    201364: "allocator-model label (mcheck b pc / FCheck pc / ISpin pc, Reusable/YG00.v:110,116,184): the same text in "
            "every core file and the donor; labels are compared only with labels (aspins, YG00.v:618-622)",
    201376: "allocator-model label, as 201364",
    202260: "allocator-model label, as 201364",
    219184: "allocator-model label, as 201364",
    449860: "allocator-model label, as 201364",
    262144: "2^18: kUserMapSize / kFreeArrayMapSize and the allocator's map-size bounds",
    1048575: "2^20 - 1: an atom range bound of the allocator model",
    1048576: "2^20: kMaxNumChunks / kQuarantineCacheMax / kNodesBlockSize / map sizes",
    0x100022: "Linux mmap flags MAP_FIXED_NOREPLACE | MAP_ANONYMOUS | MAP_PRIVATE (noreplace_core)",
    0x100032: "Linux mmap flags MAP_FIXED_NOREPLACE | MAP_ANONYMOUS | MAP_FIXED | MAP_PRIVATE (noreplace_core)",
    0x104022: "Linux mmap flags MAP_FIXED_NOREPLACE | MAP_NORESERVE | MAP_ANONYMOUS | MAP_PRIVATE (FLR)",
    0x104032: "Linux mmap flags MAP_FIXED_NOREPLACE | MAP_NORESERVE | MAP_ANONYMOUS | MAP_FIXED | MAP_PRIVATE (node_mmap2g)",
    0x20112D: "the model's range bound for the hardware-capability word V_HW (KRange (EVar V_HW) 0x112D 0x20112D, Reusable/YA01.v)",
    280000: "the model's range bound KRange (EVar V_W) 0 280000 (Reusable/YK09.v init_kn_with)",
    4194304: "Linux PID_MAX (2^22, Reusable/YK09.v)",
    0x80000000: "2^31: BRK_ASLR (Linux brk randomisation span, Reusable/YK09.v) / the sign bound of sx32 (Reusable/YK0c.v)",
    209280: "allocator-model label, as 201364",
    210276: "allocator-model label, as 201364",
    212388: "allocator-model label, as 201364",
    213516: "allocator-model label, as 201364",
    221048: "allocator-model label, as 201364",
    222820: "allocator-model label, as 201364",
    391236: "allocator-model label, as 201364",
    460508: "allocator-model label, as 201364",
    469488: "allocator-model label, as 201364",
    3727360: "a runtime mapping size of the asan allocator (AMETA_SIZE, Reusable/YE00.v:23; mk e254 3727360 in "
             "TFIB_TAIL12): an mmap length, not an image address or bound",
    4194303: "2^22 - 1: a bound on a register value (1 <= bv_unsigned (ew E 8) <= 4194303)",
    0x7FFFFFF0: "the run-to sentinel PC of runtoC / runtoD (no instruction there); not a shadow address of the image",
}

NUM = r"(0x[0-9a-fA-F]+|\d+)"
CONTENT_RX = [
    ("lit", re.compile(r"\bf?lit([1248])\s+" + NUM + r"\s+" + NUM + r"(?![0-9a-fA-Fx])")),
    ("chunk", re.compile(r"mkChunk\s+" + NUM + r"\s+\(CVal\s+(\d+)\s+\(SLit\s+" + NUM + r"\)\)")),
    ("val_mem", re.compile(r"\bval_mem\s+\w+\s+(?:\((?:[^()]|\([^()]*\))*\)|\w+)\s+" + NUM + r"\s+(\d+)\s+" + NUM + r"(?![0-9a-fA-Fx])")),
]
TUPLE_RX = re.compile(r"\(" + NUM + r",\s*(\d+),\s*\[((?:\(\d+,\s*\d+%N,\s*(?:0x[0-9a-fA-F]+|\d+|\w+)\);?\s*)+)\]\)")
ITEM_RX = re.compile(r"\((\d+),\s*(\d+)%N,\s*(0x[0-9a-fA-F]+|\d+)\)")
LITS_RX = re.compile(r"\bf?lits8\s+" + NUM + r"\s+(\[[^\]]*\]|\w+)")


def iv(x):
    x = x.replace("_", "")
    return int(x, 16) if x.lower().startswith("0x") else int(x)


def pin(key):
    (env, rel), want = PINS[key]
    p = os.environ.get("HV_" + key) or (os.path.join(os.environ[env], rel) if os.environ.get(env) else None)
    if not p:
        raise SystemExit("set %s (or HV_%s) for image %s" % (env, key, key))
    got = imgs.sha12(p)
    if got != want:
        raise SystemExit("pin mismatch %s: %s is %s, want %s" % (key, p, got, want))
    return p, got


def file_backed_ro(T, a, n):
    """('ro', bytes) for a read-only file-backed range of the target; ('rw', bytes) for writable file-backed; None else."""
    for name, lo, z in T.secs:
        if lo <= a and a + n <= lo + z:
            if name in (".bss", ".tbss", ".relro_padding"):
                return None
            b = T.rd(a, n)
            return ("rw" if name in (".data", "asan_globals") else "ro", b)
    return None


def content_facts(text):
    """[(line, addr_text, nbytes, value_text, form)] of the memory facts with literal address and value in text."""
    out = []
    for i, l in enumerate(text.split("\n"), 1):
        for form, rx in CONTENT_RX:
            for m in rx.finditer(l):
                if form == "lit":                   # lit<N> A V
                    n, a, v = m.group(1), m.group(2), m.group(3)
                else:                               # mkChunk A (CVal N (SLit V)) / val_mem _ _ A N V
                    a, n, v = m.group(1), m.group(2), m.group(3)
                out.append((i, a, int(n), v, form))
        for m in TUPLE_RX.finditer(l):
            base = iv(m.group(1))
            for it in ITEM_RX.finditer(m.group(3)):
                out.append((i, "%#x" % (base + int(it.group(1))), int(it.group(2)), it.group(3), "rodata-tuple@%s+%s" % (m.group(1), it.group(1))))
    return out


def lists_facts(text, defs_text):
    """lits8 A [v; ...] / lits8 A NAME: [(line, addr, values)]."""
    out = []
    for i, l in enumerate(text.split("\n"), 1):
        for m in LITS_RX.finditer(l):
            a, vs = m.group(1), m.group(2)
            if vs.startswith("["):
                vals = [x.strip() for x in vs.strip("[]").split(";") if x.strip()]
            else:
                dm = re.search(r"Definition\s+%s\s*:[^:]*:=\s*\[([^\]]*)\]" % re.escape(vs), defs_text, re.S)
                vals = [x.strip() for x in dm.group(1).split(";") if x.strip()] if dm else None
            out.append((i, a, vs, vals))
    return out


def jt_dest(I, a):
    """for a relative 4-byte jump-table entry at a: (base, destination, function, offset) with the base the lowest 4-aligned
    address from which every entry up to a, added to the base, lands in one function."""
    o = a & ~3
    if I.sec(o) != ".rodata":
        return None
    w = int.from_bytes(I.rd(o, 4), "little", signed=True)
    best = None
    for k in range(0, 256):
        b = o - 4 * k
        if I.sec(b) != ".rodata":
            break
        r = I.resolve(b + w)
        if r[0] != "in" or I.sec(b + w) != ".text":
            continue
        ok = True
        for j in range(k + 1):
            wj = int.from_bytes(I.rd(b + 4 * j, 4), "little", signed=True)
            rj = I.resolve(b + wj)
            if rj[0] != "in" or rj[1] != r[1]:
                ok = False
                break
        if ok:
            best = (b, b + w, sorted(r[1])[0], r[2])
    return best


def redzones(I):
    """memory ranges whose shadow is not zero once asan registers the image's globals: for each __asan_global (8 words:
    beg, size, size_with_redzone, ...) of section asan_globals, [beg + size / 8 * 8, beg + size_with_redzone)."""
    a, z = I.secd["asan_globals"]
    b = I.rd(a, z)
    out = []
    for k in range(0, z - z % 64, 64):
        beg, size, szr = (int.from_bytes(b[k + 8 * i:k + 8 * i + 8], "little") for i in range(3))
        out.append((beg + size // 8 * 8, beg + szr))
    return out


def word_witness(D, T, d, w):
    """an 8-byte word of the target's .data / .data.rel.ro / .got that holds w, at the same symbol + offset as a donor word
    that holds d: the image's own pointer to the value (text, or '')."""
    out = []
    for sec in (".data", ".data.rel.ro", ".got"):
        if sec not in T.secd or sec not in D.secd:
            continue
        a, z = T.secd[sec]
        b = T.rd(a, z)
        for k in range(0, z - 7, 8):
            if int.from_bytes(b[k:k + 8], "little") != w:
                continue
            r = T.resolve(a + k)
            if r[0] != "in":
                continue
            for n in sorted(r[1]):
                for da, dz in D.byname.get(n, []):
                    if dz == r[4] and D.q(da + r[2]) == d:
                        out.append("%s+%#x holds %#x in the target and %#x in the donor" % (n, r[2], w, d))
    return ("; confirmed by the image words: " + "; ".join(sorted(set(out)))) if out else ""


def shwin(so_root, r, T):
    """SH_LO / SH_HI rows: (expected, how) by the unit's hull_zero rule."""
    f = r["file"]
    text = open(os.path.join(so_root, f)).read()
    L = text.split("\n")
    m = re.search(r"Definition FMT : Z := (0x[0-9a-fA-F]+|\d+)\.", text)
    hz = [i + 1 for i, l in enumerate(L) if l.startswith("Definition hull_zero")]
    use = [(i + 1, mm) for i, l in enumerate(L) for mm in re.finditer(r"hull_zero \(aview (?:[^()]|\([^()]*\))*\) (\w+) (\d+) ->", l)]
    if not m or not hz or not use:
        return None, "SHWIN: FMT / hull_zero / its use not found in %s" % f
    fmt = iv(m.group(1))
    fl = text[:m.start()].count("\n") + 1
    ul, um = use[0]
    n = int(um.group(2))
    lo = ((fmt // 8 + imgs.SHADOW_OFF) // 8) * 8
    hi = (((fmt + n - 1) // 8 + imgs.SHADOW_OFF) // 8) * 8 + 8
    want = lo if r["name"] == "SH_LO" else hi
    mlo, mhi = (lo - imgs.SHADOW_OFF) * 8, (hi - imgs.SHADOW_OFF) * 8
    rz = redzones(T)
    ov = [(x, y) for x, y in rz if x < mhi and mlo < y]
    tail = ("; the window's memory [%#x, %#x) holds %s of the target's %d registered asan globals' redzones (asan_globals)"
            % (mlo, mhi, "none" if not ov else "PART (%s)" % ", ".join("[%#x, %#x)" % o for o in ov), len(rz)))
    return want, ("SHWIN: FMT = %#x (%s:%d), n = %d (hull_zero ... %s %d, %s:%d), rule %s:%d: window [shadow(FMT)/8*8, "
                  "shadow(FMT+n-1)/8*8+8) = [%#x, %#x); %s = %#x" % (fmt, f, fl, n, um.group(1), n, f, ul, f, hz[0], lo, hi,
                                                                    r["name"], want)) + tail


def startup_count(lib):
    p = os.path.join(lib, "A", "AD2j.v")
    if not os.path.exists(p):
        return None, "LIB has no A/AD2j.v"
    t = open(p).read()
    m = re.search(r"Definition IMG_REGIONS : smem := \[([^\]]*)\]", t)
    rf = re.search(r"Read from: fuzz_transport\.asan[^\n]*?sha256 ([0-9a-f]{12})", t)
    ln = t[:m.start()].count("\n") + 1 if m else 0
    n = len([x for x in m.group(1).split(";") if x.strip()]) if m else None
    return n, "LIB/A/AD2j.v:%d IMG_REGIONS has %s regions; that file reads fuzz_transport.asan %s (%s)" % (
        ln, n, rf.group(1) if rf else "?", "the OLD-pin stand-in" if rf and rf.group(1) != "e89be137db17" else "the pin")


def main():
    args = sys.argv[1:]
    tag = ""
    if "--tag" in args:
        k = args.index("--tag")
        tag = "-" + args[k + 1]
        del args[k:k + 2]
    if len(args) != 3:
        raise SystemExit("usage: hypderive.py WORK LIB OUT [--tag NAME]")
    work, lib, out = args
    so_root = os.path.join(work, "stage-out")
    pins = {k: pin(k) for k in PINS}
    D = imgs.Img(pins["D"][0], pins["DT"][0], "donor")
    T = imgs.Img(pins["T"][0], pins["TT"][0], "target")
    rows = list(csv.DictReader(open(os.path.join(out, "hyplist%s.tsv" % tag)), delimiter="\t"))
    texts = {}

    def text(f):
        if f not in texts:
            texts[f] = open(os.path.join(so_root, f)).read()
        return texts[f]

    # memory facts per (file, line)
    cfacts = collections.defaultdict(list)
    for f in sorted({r["file"] for r in rows}):
        for ln, a, n, v, form in content_facts(text(f)):
            cfacts[(f, ln)].append((a, n, v, form))
    nimg, nimg_why = startup_count(lib)

    def content_rule(r):
        for a, n, v, form in cfacts.get((r["file"], int(r["line"])), []):
            if v != r["written"]:
                continue
            fb = file_backed_ro(T, iv(a), n)
            if fb is None:
                return None
            kind, b = fb
            val = int.from_bytes(b, "little")
            vv = iv(v) & ((1 << (8 * n)) - 1)
            how = "CONTENT: %s fact at %s, %d byte(s) (%s, %s): the target image holds %#x there" % (
                form, a, n, T.sec(iv(a)), "read-only" if kind == "ro" else "writable: start value", val)
            jd = jt_dest(T, iv(a)) if n == 4 and T.sec(iv(a)) == ".rodata" else None
            if jd:
                how += "; as a relative jump-table entry: target base %#x + %#x = %#x = %s+%#x" % (jd[0], val, jd[1], jd[2], jd[3])
            return ("OK" if val == vv else ("WRONG" if kind == "ro" else "RUNTIME")), "CONTENT", "%#x" % val, how
        return None

    def donor_jt(r):
        """for a CONTENT row of a jump-table entry: the donor's entry and destination, from the paired donor line."""
        m = re.match(r"(.+):(\d+)$", r["donor_at"])
        if not m:
            return ""
        dl = open(os.path.join(work, "stage", m.group(1))).read().split("\n")[int(m.group(2)) - 1]
        for form, rx in CONTENT_RX:
            for mm in rx.finditer(dl):
                a, v = (mm.group(2), mm.group(3)) if form == "lit" else (mm.group(1), mm.group(3))
                if v == r["donor"] and form == "lit" and mm.group(1) == "4":
                    jd = jt_dest(D, iv(a))
                    if jd:
                        return "; donor: entry %s at %s, base %#x + %s = %#x = %s+%#x" % (v, a, jd[0], v, jd[1], jd[2], jd[3])
        return ""

    drows = []
    for r in rows:
        if r["decision"] == "SAME":
            continue
        verdict = rule = exp = how = None
        for pred, why in KNOWN:
            if pred(r):
                verdict, rule, exp, how = "KNOWN", "KNOWN", r["written"], why
                break
        if verdict is None and r["name"] in ("SH_LO", "SH_HI"):
            e, how = shwin(so_root, r, T)
            if e is not None:
                verdict, rule, exp = ("OK" if e == iv(r["written"]) else "WRONG"), "SHWIN", "%#x" % e
            else:
                verdict, rule, exp = "OPEN", "SHWIN", "-"
        if verdict is None and "img_sh_present" == r["name"] and iv(r["donor"]) == (D.top_up - 0x10000) // 8:
            e = (T.top_up - 0x10000) // 8
            verdict, rule, exp = ("OK" if e == iv(r["written"]) else "WRONG"), "SHSPAN", "%#x" % e
            how = ("SHSPAN: the lemma's range starts at shadow(0x10000) = 0x7fffa000; its length is the image span / 8: "
                   "target (%#x - 0x10000) / 8 = %#x (donor (%#x - 0x10000) / 8 = %#x)" % (T.top_up, e, D.top_up, iv(r["donor"])))
        if verdict is None and r["name"] in ("IMG_E", "IMG_B", "PM_tailL"):
            add = 0 if r["name"] != "PM_tailL" else 2
            exp = "length IMG_REGIONS%s" % (" + 2" if add else "")
            at_pin = nimg is not None and nimg_why.endswith("(the pin)")
            rule = "COUNT"
            verdict = ("OK" if nimg + add == iv(r["written"]) else "WRONG") if at_pin else "NEEDS-STARTUP"
            lay = ""
            ad2f = os.path.join(so_root, "A", "AD2f.v")
            if os.path.exists(ad2f):
                for k, l in enumerate(open(ad2f), 1):
                    if l.startswith("Lemma S_Pm_layout"):
                        mm = re.search(r"firstn (\d+) \(skipn 3 \(ss_mem S_Pm\)\) = IMG_REGIONS", l)
                        lay = ("; the unit's own lemma A/AD2f.v:%d S_Pm_layout (`firstn %s (skipn 3 (ss_mem S_Pm)) = "
                               "IMG_REGIONS`, vm_compute) checks it at build" % (k, mm.group(1) if mm else "?"))
                        break
            how = ("COUNT: %s = %s (the image regions of the start-up state%s); %s; %s + %d = %s against the written "
                   "%s%s" % (
                       r["written"], exp, ": firstn 2 of S_Pm then IMG_E (A/AD2e.v PM_tailL_unfold)" if add else "",
                       nimg_why, nimg, add, (nimg + add) if nimg is not None else "?", r["written"], lay))
        if verdict is None:
            c = content_rule(r)
            if c:
                verdict, rule, exp, how = c
                how += donor_jt(r)
        if verdict is None:
            if r["donor"] == "-":
                hv = NEWHAND.get((r["file"], r["written"]))
                tr = T.resolve(iv(r["written"])) if iv(r["written"]) >= 0x10000 else None
                tn = ("; the target holds %s %s+%#x there" % (tr[0], "|".join(sorted(tr[1])[:2]), tr[2])) if tr and tr[0] != "none" else ""
                sl = (text(r["file"]).split("\n")[int(r["line"]) - 1]).rstrip()
                gp = GADD.get(r["file"], {}).get(sl)
                if hv:
                    verdict, rule, exp, how = hv[0], "NEW", r["written"], "decided by hand: " + hv[1] + tn
                elif gp and iv(r["written"]) < 0x10000 and re.search(
                        r"(?<![\w.])%s(?![\w.])" % re.escape(r["written"]), sl):
                    verdict, rule, exp, how = "OK", "GPATCH", r["written"], (
                        "a line %s added (the G form, records/ghunks/GHUNKS-A-rec3.md); %s is below the image base "
                        "0x10000, no address of either image: `%s`" % (gp, r["written"], sl.strip()[:120]))
                else:
                    verdict, rule, exp, how = "OPEN", "NEW", "-", "no donor position" + tn
            else:
                v, rl, e, h = imgs.derive(D, T, iv(r["donor"]), iv(r["written"]))
                verdict, rule, exp, how = v, rl, ("%#x" % e if e is not None else "-"), h
        if rule == "SYMBOL-RANK" and verdict == "OK":
            how += word_witness(D, T, iv(r["donor"]), iv(r["written"]))
        drows.append((r, verdict, rule, exp, how))

    # SAME rows: image-dependent donor values kept
    krows = []
    for r in rows:
        if r["decision"] != "SAME":
            continue
        try:
            v = iv(r["written"])
        except ValueError:
            continue
        exp = rule = how = None
        if imgs.in_image(D, v):
            e, rule, how = imgs.expect_addr(D, T, v)
            exp = e
        elif imgs.is_shadow(v) and imgs.in_image(D, (v - imgs.SHADOW_OFF) * 8):
            u = (v - imgs.SHADOW_OFF) * 8
            e, rule, how = imgs.expect_addr(D, T, u)
            exp = (e // 8 + imgs.SHADOW_OFF) if e is not None else None
            rule, how = "SHADOW-" + rule, "unshadow(%#x) = %#x; %s" % (v, u, how)
        elif v >= 0x1000 and v in D.sizes:
            qs = D.sizes[v]
            tv = sorted(t for t, q in T.sizes.items() if q & qs)
            if tv and all(t != v for t in tv):
                exp, rule, how = tv[0], "SIZE", "donor %s = %#x; target %#x" % ("/".join(sorted(qs)), v, tv[0])
            else:
                continue
        else:
            continue
        if exp == v:
            krows.append((r, "SAME-IN-BOTH", rule, "%#x" % exp, how))
            continue
        known = [why for pred, why in KNOWN if pred(r)]
        if known:
            krows.append((r, "KNOWN", rule, "-" if exp is None else "%#x" % exp, known[0]))
        elif re.search(r"Definition \w+ : bv 32 := %s\." % re.escape(r["written"]), text(r["file"]).split("\n")[int(r["line"]) - 1]):
            krows.append((r, "CONST", rule, "-" if exp is None else "%#x" % exp,
                          "decided by rule: a RISC-V instruction word (Definition NAME : bv 32 := V) of a code pattern the "
                          "proof compares with fetched words (as an address it would read: %s)" % how))
        elif v in CONST:
            krows.append((r, "CONST", rule, "-" if exp is None else "%#x" % exp,
                          "decided by hand: %s (as an address it would read: %s)" % (CONST[v], how)))
        else:
            krows.append((r, "KEPT-IMAGE", rule, "-" if exp is None else "%#x" % exp, how))

    # CONTENT on every listed row that is the value of a memory fact (SAME rows too)
    crows = []
    listed = {(r["file"], int(r["line"]), r["written"]): r for r in rows}
    for (f, ln), facts in sorted(cfacts.items()):
        for a, n, v, form in facts:
            r = listed.get((f, ln, v))
            if r is None:
                continue
            if iv(a) < 0x10000:
                crows.append((r, a, n, form, "-", "RELATIVE (an offset in a based region, not an image address)"))
                continue
            fb = file_backed_ro(T, iv(a), n)
            if fb is None:
                crows.append((r, a, n, form, "-", "RUNTIME (.bss or no file bytes: a run-time value)"))
                continue
            kind, b = fb
            val = int.from_bytes(b, "little")
            ok = val == (iv(v) & ((1 << (8 * n)) - 1))
            crows.append((r, a, n, form, "%#x" % val, "OK" if ok else ("WRONG" if kind == "ro" else "RUNTIME (writable; start value differs)")))
    for f in sorted({r["file"] for r in rows}):
        t = text(f)
        for ln, a, nm, vals in lists_facts(t, t):
            if vals is None:
                continue
            for k, x in enumerate(vals):
                try:
                    xv = iv(x)
                except ValueError:
                    continue
                aa = iv(a) + 8 * k
                fb = file_backed_ro(T, aa, 8)
                r = listed.get((f, ln, a)) or {"file": f, "line": str(ln), "written": a, "class": "-", "decision": "-"}
                if fb is None:
                    crows.append((r, "%#x" % aa, 8, "lits8 %s[%d]" % (nm, k), "-", "RUNTIME (.bss / no file bytes)"))
                    continue
                val = int.from_bytes(fb[1], "little")
                crows.append((r, "%#x" % aa, 8, "lits8 %s[%d] = %s" % (nm, k, x), "%#x" % val,
                              "OK" if val == xv else ("WRONG" if fb[0] == "ro" else "RUNTIME (writable; start value differs)")))

    # information only: the same address rules on the DIFFERS numerals outside hypothesis positions (hyplist's
    # unlisted-differs.tsv: proof bodies, lemma conclusions, computed states, other definitions, tactics)
    urows = []
    up = os.path.join(out, "unlisted-differs%s.tsv" % tag)
    if os.path.exists(up):
        for r in csv.DictReader(open(up), delimiter="\t"):
            if r["donor"] == "-":
                urows.append((r, "NEW", "-", "-", "no donor position"))
                continue
            try:
                v, rl, e, h = imgs.derive(D, T, iv(r["donor"]), iv(r["written"]))
            except ValueError:
                v, rl, e, h = "OPEN", "NOT-NUMBER", None, "-"
            urows.append((r, v, rl, "%#x" % e if e is not None else "-", h))
        with open(os.path.join(out, "unlisted-derived%s.tsv" % tag), "w") as o:
            o.write("file:line\tplace\tkeyword\tname\tdonor\twritten\tverdict\trule\tright\tderivation\n")
            for r, v, rl, e, h in urows:
                o.write("\t".join((r["file"] + ":" + r["line"], r["place"], r["keyword"], r["name"], r["donor"], r["written"], v, rl,
                                   e, h)) + "\n")

    with open(os.path.join(out, "differs%s.tsv" % tag), "w") as o:
        o.write("file:line\tcol\tclass\tname\tdonor\twritten\tverdict\trule\tright\tderivation\n")
        for r, verdict, rule, exp, how in drows:
            o.write("\t".join((r["file"] + ":" + r["line"], r["col"], r["class"], r["name"], r["donor"], r["written"], verdict,
                               rule, exp, how)) + "\n")
    with open(os.path.join(out, "kept%s.tsv" % tag), "w") as o:
        o.write("file:line\tcol\tclass\tname\tvalue\tdecision\trule\ttarget_value\twhy\n")
        for r, dec, rule, exp, how in krows:
            o.write("\t".join((r["file"] + ":" + r["line"], r["col"], r["class"], r["name"], r["written"], dec, rule or "-", exp,
                               how or "-")) + "\n")
    with open(os.path.join(out, "content%s.tsv" % tag), "w") as o:
        o.write("file:line\tclass\tdecision\taddress\tbytes\tform\tvalue\ttarget_bytes\tverdict\n")
        for r, a, n, form, tb, ver in crows:
            o.write("\t".join((r["file"] + ":" + r["line"], r["class"], r["decision"], a, str(n), form, r["written"], tb, ver)) + "\n")

    vc = collections.Counter(x[1] for x in drows)
    kc = collections.Counter(x[1] for x in krows)
    cc = collections.Counter(x[5].split(" ")[0] for x in crows)
    nd = sum(1 for r in rows if r["decision"] != "SAME")
    lines = []
    lines.append("hypderive.py %s %s %s%s" % (work, lib, out, (" --tag " + tag[1:]) if tag else ""))
    lines.append("images: " + ", ".join("%s %s %s" % (k, pins[k][1], pins[k][0]) for k in PINS))
    lines.append("listed %d; differs-from-donor %d (DIFFERS %d, DIFFERS-FORM %d, NEW %d)" % (
        len(rows), nd, sum(r["decision"] == "DIFFERS" for r in rows), sum(r["decision"] == "DIFFERS-FORM" for r in rows),
        sum(r["decision"] == "NEW" for r in rows)))
    lines.append("DIFFERS rows derived: OK %d, WRONG %d, NEEDS-STARTUP %d, KNOWN %d, RUNTIME %d, OPEN %d" % (
        vc["OK"], vc["WRONG"], vc["NEEDS-STARTUP"], vc["KNOWN"], vc["RUNTIME"], vc["OPEN"]))
    lines.append("DIFFERS rules: " + ", ".join("%s %d" % (k, v) for k, v in sorted(collections.Counter(x[2] for x in drows).items())))
    lines.append("SAME rows that name a donor image value: %d: SAME-IN-BOTH %d, CONST (by hand / the bv-32 rule) %d, KNOWN %d, "
                 "KEPT-IMAGE %d" % (len(krows), kc["SAME-IN-BOTH"], kc["CONST"], kc["KNOWN"], kc["KEPT-IMAGE"]))
    lines.append("CONTENT (memory facts of listed rows with literal address and value): %d: OK %d, WRONG %d, RUNTIME %d, "
                 "RELATIVE %d" % (len(crows), cc["OK"], cc["WRONG"], cc["RUNTIME"], cc["RELATIVE"]))
    uc = collections.Counter(x[1] for x in urows)
    lines.append("information only, DIFFERS outside hypothesis positions (unlisted-derived%s.tsv): %d: %s" % (
        tag, len(urows), ", ".join("%s %d" % kv for kv in sorted(uc.items()))))
    for r, verdict, rule, exp, how in drows:
        if verdict in ("WRONG", "OPEN", "NEEDS-STARTUP"):
            lines.append("%s\t%s:%s\twritten %s\tright %s\tdonor %s\t%s\t%s" % (verdict, r["file"], r["line"], r["written"], exp,
                                                                         r["donor"], rule, how))
    for r, dec, rule, exp, how in krows:
        if dec == "KEPT-IMAGE":
            lines.append("KEPT-IMAGE\t%s:%s\tvalue %s\ttarget %s\t%s\t%s" % (r["file"], r["line"], r["written"], exp, rule, how))
    for r, a, n, form, tb, ver in crows:
        if ver == "WRONG":
            lines.append("CONTENT-WRONG\t%s:%s\t%s at %s (%d bytes)\twritten %s\timage %s" % (r["file"], r["line"], form, a, n,
                                                                                         r["written"], tb))
    open(os.path.join(out, "hypvalues%s.txt" % tag), "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
