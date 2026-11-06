#!/usr/bin/env python3
"""compcheck.py WORK LIB OUT [--tag NAME]: item 4 of the TCA value lane, the four compensating checks of the registry entry
'port_core d9e0589898fd SCORED' (the tool registry's README.md, sha256 05596ed48d98; internal record): port_core d9e0589898fd is adopted only with
  (a) every KEPT image-derived count recomputed from the target's own headers / symbols and compared with stage-out,
  (b) every GOT[0] cell checked (OK-GOT0),
  (c) every shadow offset and model constant checked BY ROLE,
  (d) every 'no twin' drop confirmed against the target symtab.
Read-only. proves no function (kind: measurement). Each numeral of WORK/stage-out/{A,Reusable}/*.v is aligned with its
donor token in WORK/stage (decval.py's alignment, numerals masked); comment numerals are left out (port_core edits none).

(a) A quantity Q is a named image quantity computed the same way in both images (symbol size / size/2 /4 /8, extent to
    the next symbol, section size / size/2 /4 /8 and its ceilings, section and PT_LOAD bounds / 8 and page numbers, PT_LOAD
    memsz / filesz / page span / page count, image top (page-up), top / 8, image span, rw_lo, rw_len, top - X for a
    section or a named object X, and the same / 8). DIFF = the quantities whose value differs between the two images.
    a1  every KEPT numeral k on a line where another numeral MOVED: for each moved partner p (donor pd -> written pt) with
        pd + k an item of the donor image, the written span must be the target's: twin(pd + k) - pt == k; for two moved
        partners p, q with qd - pd == k, qt - pt must be k. A failure is a candidate.
    a2  every KEPT numeral >= 0x100 that is a DIFF quantity of the donor (Q(D) == k != Q(T)) and no quantity of the
        target; every KEPT numeral in [0x10, 0x100) that is a DIFF section / segment / data-object quantity of the donor
        on a line that moved a numeral, or in a definition whose name says count / length / size / words / pages / span.
    a3  port_core's own derived counts (WORK/geometry.tsv, decimals.tsv `derived` rows): the written value recomputed
        from the target (hull = [0x10000, page-up top), segN = PT_LOAD N, quotients as the row states).
(b) GOT[0]: the target .got start, its word (0 with no .dynamic), and every numeral equal to it (a .got start bound).
(c) c1 every numeral whose donor value is at or above 0x7fff0000: a SHADOW ADDRESS of the donor image when it lies in
        [K + 0x10000/8, K + donor top/8] (K = 0x7fff8000): the written value must be a shadow form (s, s & ~7, (s & ~7) + 8)
        of the twin of a donor byte whose same form is the donor value (bytes within 64 of 8 * (d - K)); else a MODEL
        CONSTANT, which must be byte-identical to the donor's. The CZONE bound the owner overrides is listed as known.
    c1w the format-string shadow windows (a file that defines FMT, SH_LO, SH_HI): SH_LO = floor8(shadow(FMT)), SH_HI =
        floor8(shadow(FMT + len - 1)) + 8 for the NUL-terminated string at FMT, in the donor text / image and in stage-out /
        the target image.
    c2  every numeral that is the right operand of a divisor / modulus / mask / shift (`/ N`, `mod N`, `Z.modulo _ N`,
        `Z.div _ N`, `Z.land _ N`, `Z.shiftr _ N`, `Z.shiftl _ N`, `^ N`): byte-identical to the donor's; the right operand
        of `*` likewise, unless it is the same image quantity in both images (`4096 * 1558`, the image top's page count).
    c3  check.tsv's `arithmetic-constant` rows (port_core's model constants): old == new and stage-out holds it.
    c4  Reusable/YG0f.v (the allocator model's constants; there is no AsanCtrl file in this unit): every numeral equal to
        the donor's.
(d) the donor function-table rows of A/AB1w.v (tfib_A_<name>) absent from stage-out's, and every source_name of
    WORK/no-twin.tsv: a FUNC / OBJECT symbol of that name in the target (exact, or with the leading underscores or an
    `__interceptor_` / `___interceptor_` prefix removed on either side) is a finding unless stage-out still holds the row
    with the target symbol's own start and end.
Output: OUT/compcheck[-TAG].tsv (every row checked and its decision), OUT/compcheck[-TAG].txt (result lines, every
candidate / finding).
"""
import bisect
import collections
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import decval as DV  # noqa: E402
from symoff import Res, lab, decide  # noqa: E402
from elftools.elf.elffile import ELFFile  # noqa: E402

K = 0x7FFF8000
COUNTNAME = re.compile(r"Definition\s+\w*(?:len|LEN|Len|count|COUNT|Count|_N\b|_n\b|size|SIZE|Size|SZ|words|WORDS|pages|PAGES|span|SPAN|bytes|BYTES|cnt|CNT|nent|NENT)\w*\s*:")
OPS = re.compile(r"(?:(?<![\\A-Za-z0-9_])/(?!\\)|\bmod\b|\bZ\.modulo\b|\bZ\.div\b|\bZ\.land\b|\bZ\.shiftr\b|\bZ\.shiftl\b|\^)\s*\(?\s*$")
MUL = re.compile(r"(?<![A-Za-z0-9_])\*(?!\))\s*\(?\s*$")
KNOWN_C = {0x800BAC00: "KNOWN to the owner: the CZONE bound 0x800bac00 is an override row (overrides.tsv), not a relocation"}

_INV = {}


def on_line(L, ln, val, f=None, cfg=None, win=40):
    """the stage-out line that holds val for a tool row at donor (stage/) line ln. With f and cfg: the stage-out line the
    numeral-masked alignment pairs with stage/ line ln, which must hold val; a donor line with no aligned stage-out line
    (changed by a --patch) is looked for within win lines and the result is negative (-line). Without them: ln + 1 or ln.
    Returns the 1-based stage-out line number (negative: found by the window), or 0."""
    hold = lambda x: 0 < x <= len(L) and val in {DV.val(t) for t in DV.toks(L[x - 1])}
    if f is not None:
        if f not in _INV:
            _, _, pr = DV.align(os.path.join(cfg["dont"], f), os.path.join(cfg["core"], f))
            _INV[f] = {i: j for j, i in pr.items()}
        j = _INV[f].get(ln - 1)
        if j is not None:
            return j + 1 if hold(j + 1) else 0
        for dx in range(0, win + 1):
            for x in (ln + 1 + dx, ln + 1 - dx):
                if hold(x):
                    return -x
        return 0
    for x in (ln + 1, ln):
        if hold(x):
            return x
    return 0


def quantities(R, symp):
    """{name: value} of the named image quantities of one image (see (a))."""
    e = ELFFile(open(symp, "rb"))
    syms, cnt = [], collections.Counter()
    for s in e.get_section_by_name(".symtab").iter_symbols():
        n, t, sh = s.name, s["st_info"]["type"], s["st_shndx"]
        if not n or n.startswith("$") or not isinstance(sh, int) or t in ("STT_SECTION", "STT_FILE", "STT_TLS"):
            continue
        syms.append((s["st_value"], s["st_size"], n, t))
        cnt[n] += 1
    starts = sorted({a for a, z, n, t in syms})
    q, kind = {}, {}

    def put(k, v, kd):
        q[k], kind[k] = v, kd
    for a, z, n, t in syms:
        if cnt[n] != 1:
            continue
        kd = "object" if t in ("STT_OBJECT", "STT_NOTYPE") else "func"
        if z:
            put("size(%s)" % n, z, kd)
            for k in (2, 4, 8):
                if z % k == 0:
                    put("size(%s)/%d" % (n, k), z // k, kd)
        i = bisect.bisect_right(starts, a)
        if i < len(starts):
            ext = starts[i] - a
            put("extent(%s)" % n, ext, kd)
            for k in (2, 4, 8):
                if ext % k == 0:
                    put("extent(%s)/%d" % (n, k), ext // k, kd)
        if a >= 0x10000 and kd == "object":
            put("addr(%s)/8" % n, a // 8, "quotient")
            if z:
                put("end(%s)/8" % n, (a + z) // 8, "quotient")
            put("top_up-addr(%s)" % n, R.top_up - a, "span")
            put("(top_up-addr(%s))/8" % n, (R.top_up - a) // 8, "quotient")
    for n, a, z in R.secs:
        put("secsize(%s)" % n, z, "section")
        for k in (2, 4, 8):
            put("secsize(%s)/%d" % (n, k), z // k, "section")
            put("ceil(secsize(%s)/%d)" % (n, k), -(-z // k), "section")
        put("pages(%s)" % n, (z + 0xFFF) >> 12, "section")
        put("seclo(%s)/8" % n, a // 8, "section")
        put("sechi(%s)/8" % n, (a + z) // 8, "section")
        put("seclo(%s)>>12" % n, a >> 12, "section")
        put("sechi(%s)>>12" % n, (a + z + 0xFFF) >> 12, "section")
        put("top_up-seclo(%s)" % n, R.top_up - a, "section")
        put("top_up-sechi(%s)" % n, R.top_up - a - z, "section")
        put("(top_up-seclo(%s))/8" % n, (R.top_up - a) // 8, "section")
        put("(top_up-sechi(%s))/8" % n, (R.top_up - a - z) // 8, "section")
    for i, (v, m, d) in enumerate(R.loads):
        lp, hp = v & ~0xFFF, (v + m + 0xFFF) & ~0xFFF
        for k, x in (("memsz", m), ("filesz", len(d)), ("span", hp - lp), ("pages", (hp - lp) >> 12), ("lo>>12", v >> 12),
                     ("hi>>12", hp >> 12), ("lo/8", v // 8), ("hi/8", (v + m) // 8), ("hipage/8", hp // 8),
                     ("lo_page", lp), ("hi_page", hp)):
            put("load%d.%s" % (i, k), x, "segment")
    rlo = [a + z for n, a, z in R.secs if n == ".relro_padding"][0]
    for k, x in (("top_up", R.top_up), ("top_up/8", R.top_up // 8), ("top_up>>12", R.top_up >> 12),
                 ("img_span", R.top_up - 0x10000), ("img_span/8", (R.top_up - 0x10000) // 8),
                 ("(top_up-1)/8", (R.top_up - 1) // 8), ("rw_lo", rlo), ("rw_len", R.top_up - rlo), ("rw_len/8", (R.top_up - rlo) // 8)):
        put(k, x, "segment")
    return q, kind


def twin(DR, TR, a):
    """the target address of the donor byte a by role: the same image quantity, the same symbol + offset, the same string
    at the same offset (found once), or the code-formed base + offset; None when none applies."""
    g = {n for n in DR.geo.get(a, set()) if n in ("img_top_up", "rw_lo") or n.endswith((".lo", ".hi", ".lo_page", ".hi_page"))}
    for n in sorted(g):
        for v, ns in TR.geo.items():
            if n in ns:
                return v
    fs = DR.forms(a)
    for n, off in sorted(fs):
        base = n[:-4] if n.endswith(".end") else n
        for v in TR.at_name.get(base, ()):
            if n.endswith(".end"):
                z = TR.size_of.get((base, v))
                if z:
                    return v + z
            else:
                z = TR.size_of.get((base, v), 0)
                if off < max(z, 1):
                    return v + off
    s = DR.string_at(a)
    if s and len(s[0]) > 2 and TR.rob.count(s[0]) == 1:
        return TR.ro[0] + TR.rob.find(s[0]) + s[1]
    i = bisect.bisect_right(DR.refkeys, a) - 1
    if i >= 0 and a - DR.refkeys[i] < 0x1000 and DR.sec(a) == ".rodata":
        b = DR.refkeys[i]
        for site in sorted(DR.refs[b]):
            for b2 in TR.refs_at.get(site, ()):
                return b2 + (a - b)
    return None


def main():
    a = sys.argv[1:]
    if len(a) < 3:
        sys.exit("usage: compcheck.py WORK LIB OUT [--tag NAME] [--decided TSV]")
    work, lib, out = a[:3]
    tag = ("-" + a[a.index("--tag") + 1]) if "--tag" in a else ""
    # rows decided by hand on an earlier run (part, at, written value, decision, reason): a CANDIDATE / AMBIGUOUS row at
    # the same place with the same written value takes that decision; any other row stays open
    decided = {}
    if "--decided" in a:
        for l in open(a[a.index("--decided") + 1]).read().splitlines()[1:]:
            p = l.split("\t")
            decided[(p[0], p[1], p[2])] = (p[3], p[4])
    cfg = DV.setup([work])
    TR, DR = Res(cfg["tgt_syms"], cfg["tgt_bytes"]), Res(cfg["don_syms"], cfg["don_bytes"])
    for R, p in ((TR, cfg["tgt_syms"]), (DR, cfg["don_syms"])):
        R.at_name, R.size_of = collections.defaultdict(set), {}
        for s in ELFFile(open(p, "rb")).get_section_by_name(".symtab").iter_symbols():
            if s.name and isinstance(s["st_shndx"], int) and s["st_info"]["type"] not in ("STT_TLS", "STT_SECTION", "STT_FILE"):
                R.at_name[s.name].add(s["st_value"])
                R.size_of[(s.name, s["st_value"])] = max(R.size_of.get((s.name, s["st_value"]), 0), s["st_size"])
    QD, KD = quantities(DR, cfg["don_syms"])
    QT, KT = quantities(TR, cfg["tgt_syms"])
    common = set(QD) & set(QT)
    diff = {k for k in common if QD[k] != QT[k]}
    dval = collections.defaultdict(list)
    for k in diff:
        dval[QD[k]].append(k)
    tval = collections.defaultdict(list)
    for k in common:
        tval[QT[k]].append(k)
    rows, lines, cnt = [], [], collections.Counter()
    finds = []

    def note(part, dec, at, d, v, ev, src=""):
        if dec in ("CANDIDATE", "AMBIGUOUS") and (part, at, str(v)) in decided:
            dd, why = decided[(part, at, str(v))]
            dec, ev = dd, ev + " | decided by hand: " + why
        rows.append((part, dec, at, d, v, ev, src[:160]))
        cnt[(part, dec)] += 1
        if dec.startswith(("CANDIDATE", "FINDING")):
            finds.append(rows[-1])

    # ---- every numeral, aligned
    rel = DV.file_list(cfg)
    nums = []   # (file, line, idx, tok, v, dtok, d, line text, role)
    for t, dp in rel:
        dd, cc, pr = DV.align(dp, os.path.join(cfg["core"], t))
        depth = 0
        for j, line in enumerate(cc):
            incom = depth > 0
            depth = max(0, depth + line.count("(*") - line.count("*)"))
            role = DV.role(line)
            if incom or role == "comment":
                continue
            tk = DV.toks(line)
            if not tk:
                continue
            dtk = DV.toks(dd[pr[j]]) if j in pr else None
            al = dtk is not None and len(dtk) == len(tk)
            for i, s in enumerate(tk):
                nums.append((t, j + 1, i, s, DV.val(s), dtk[i] if al else None, DV.val(dtk[i]) if al else None, line, role))
    bylinemap = collections.defaultdict(list)
    for n in nums:
        bylinemap[(n[0], n[1])].append(n)
    code = [n for n in nums if n[8] not in ("fetch", "word", "decode")]
    lines.append("# numerals: %d in code lines of %d files (%d aligned with a donor token); quantities: donor %d, target %d, "
                 "common %d, differing %d" % (len(nums), len(rel), sum(1 for n in nums if n[6] is not None), len(QD), len(QT),
                                              len(common), len(diff)))

    # ---- (a1) partner spans on lines that moved a numeral
    def is_bound(R, x):
        """an exact boundary of the image: a symbol start or end, a section / PT_LOAD bound, the page-up top"""
        return bool(R.at.get(x)) or bool(R.ends.get(x)) or any(n.endswith((".lo", ".hi", ".lo_page", ".hi_page")) or n in ("img_top_up", "rw_lo")
                                                              for n in R.geo.get(x, ()))

    def is_addr(R, x):
        return 0x10000 <= x <= R.top_up and (R.isdata(x) or x == R.top_up or any(n.startswith(("sec:", "load")) for n in R.geo.get(x, ())))
    a1 = 0
    for key, ns in bylinemap.items():
        ns = [n for n in ns if n[6] is not None and n[8] not in ("fetch", "word", "decode")]
        mv = [n for n in ns if n[4] != n[6]]
        kp = [n for n in ns if n[4] == n[6] and n[4] >= 2]
        if not mv or not kp:
            continue
        for k in kp:
            kv = k[4]
            # two moved partners whose donor difference is k: the written difference must be k too
            pairs = [(p, q) for p in mv for q in mv if q is not p and q[6] - p[6] == kv and is_addr(DR, p[6]) and is_addr(DR, q[6])]
            for p, q in pairs:
                a1 += 1
                if q[4] - p[4] != kv:
                    note("a1", "CANDIDATE", "%s:%d" % key, k[5], k[3], "kept %s = %s - %s in the donor; the written partners %s - %s = %#x" % (
                        k[3], q[5], p[5], q[3], p[3], q[4] - p[4]), k[7])
                else:
                    note("a1", "SPAN-SAME", "%s:%d" % key, k[5], k[3], "kept %s = %s - %s in the donor and %s - %s in the target" % (
                        k[3], q[5], p[5], q[3], p[3]), k[7])
            if any(q[4] - p[4] == kv for p, q in pairs):
                continue
            # a moved base whose donor value + k is an exact boundary of the donor image: the target span from the
            # written base to that boundary's twin must be k
            for p in mv:
                if not (is_addr(DR, p[6]) and is_bound(DR, p[6])):
                    continue
                e = p[6] + kv
                if is_addr(DR, e) and is_bound(DR, e):
                    te = twin(DR, TR, e)
                    a1 += 1
                    if te is not None and te - p[4] != kv:
                        note("a1", "CANDIDATE", "%s:%d" % key, k[5], k[3], "kept length %s from moved base %s -> %s: the donor's end %#x "
                             "(%s) is %#x in the target, so the target span is %#x" % (k[3], p[5], p[3], e, lab(DR.resolve(e)), te, te - p[4]), k[7])
                    else:
                        note("a1", "SPAN-SAME" if te is not None else "SPAN-NO-TWIN", "%s:%d" % key, k[5], k[3],
                             "base %s -> %s, end twin %s" % (p[5], p[3], "%#x" % te if te is not None else "-"), k[7])
    lines.append("(a1) kept lengths beside moved partners: %d pairs checked; %s" % (a1, dict((d, c) for (p, d), c in cnt.items() if p == "a1")))

    # ---- (a1b) code ranges stated as (start, word count): `(0xPC, N%nat)` and `build_table tfibsegs 0xPC N%nat`
    rng = re.compile(r"\((0x[0-9a-fA-F]+),\s*(\d+)%nat\)|build_table\s+tfibsegs\s+(0x[0-9a-fA-F]+)\s+(\d+)%nat")
    nb = 0
    for t, dp in rel:
        if not rng.search(open(os.path.join(cfg["core"], t)).read()):
            continue
        dd, cc, pr = DV.align(dp, os.path.join(cfg["core"], t))
        for j, line in enumerate(cc):
            ms = list(rng.finditer(line))
            md = list(rng.finditer(dd[pr[j]])) if j in pr else []
            if not ms:
                continue
            if len(ms) != len(md):
                for m in ms:
                    note("a1b", "CANDIDATE", "%s:%d" % (t, j + 1), "-", m.group(0), "a (start, word count) range with no aligned donor range", line)
                continue
            for m, n in zip(ms, md):
                pt, ct = int(m.group(1) or m.group(3), 16), int(m.group(2) or m.group(4))
                pd, cd = int(n.group(1) or n.group(3), 16), int(n.group(2) or n.group(4))
                nb += 1
                st = twin(DR, TR, pd)
                st_ok = st == pt or bool(DR.forms(pd) & TR.forms(pt))   # a static with several copies: the same form
                ends = DR.forms(pd + 4 * cd) & TR.forms(pt + 4 * ct)
                ok = st_ok and cd == ct and bool(ends)
                note("a1b", "RANGE-SAME" if ok else "CANDIDATE", "%s:%d" % (t, j + 1), "(%#x, %d)" % (pd, cd), "(%#x, %d)" % (pt, ct),
                     "start twin %s; end %#x (%s) / %#x (%s); count %s" % (
                         "%#x" % st if st is not None else "-", pd + 4 * cd, lab(DR.resolve(pd + 4 * cd)), pt + 4 * ct,
                         lab(TR.resolve(pt + 4 * ct)), "kept" if cd == ct else "CHANGED %d -> %d" % (cd, ct)), line)
    lines.append("(a1b) code ranges (start, word count): %d checked; %s" % (nb, dict((d, c) for (p, d), c in cnt.items() if p == "a1b")))

    # ---- (a2) kept numerals that are differing donor quantities
    datak = lambda k: KD.get(k) in ("section", "segment", "object", "span")
    for n in code:
        if n[6] is None or n[4] != n[6]:
            continue
        kv = n[4]
        ks = dval.get(kv, [])
        if not ks:
            continue
        movedline = any(m[6] is not None and m[4] != m[6] for m in bylinemap[(n[0], n[1])])
        named = bool(COUNTNAME.search(n[7]))
        if kv >= 0x100 or (kv >= 0x10 and (movedline or named) and any(datak(k) for k in ks)):
            # sorted, so that the examples a row names are the same on every run (set order varies with the hash seed)
            ks2 = sorted(ks if kv >= 0x100 else [k for k in ks if datak(k)])
            tq = sorted(tval.get(kv, []))
            dec = "CANDIDATE" if not tq else "AMBIGUOUS"
            note("a2", dec, "%s:%d" % (n[0], n[1]), n[5], n[3], "%s in the donor (target %s); %s" % (
                ", ".join(ks2[:3]), ", ".join("%#x" % QT[k] for k in ks2[:3]),
                ("the value is also the target's %s" % ", ".join(tq[:2])) if tq else "no target quantity has this value"), n[7])
    lines.append("(a2) kept numerals that are a differing donor quantity: %s" % dict((d, c) for (p, d), c in cnt.items() if p == "a2"))

    # ---- (a3) port_core's derived counts
    seg = [(v, m) for v, m, d in TR.loads]
    G = {"hull.size": TR.top_up - 0x10000, "hull.size/8": (TR.top_up - 0x10000) // 8, "hull.page": TR.top_up >> 12,
         "hull.hi/8": TR.top_up // 8, "hull.hi": TR.top_up, "hull.lo": 0x10000}
    for i, (v, m) in enumerate(seg):
        lp, hp = v & ~0xFFF, (v + m + 0xFFF) & ~0xFFF
        G["seg%d.size" % i] = hp - lp      # the page-rounded span, as the (base, size) rows state it
        G["seg%d.base" % i] = lp
        G["seg%d.end" % i] = hp
    gp = os.path.join(work, "geometry.tsv")
    for r in ([l.rstrip("\n").split("\t") for l in open(gp).read().splitlines()[1:]] if os.path.exists(gp) else []):
        f, ln, old, new, rl = r[0], int(r[1]), r[2], r[3], r[4]
        if not (DV.NUM.fullmatch(old) and DV.NUM.fullmatch(new)):
            note("a3", "NOT-A-NUMERAL", "%s:%d" % (f, ln + 1), old[:40], new[:60], "%s: not a numeral row (the class map; atable / codeptr gates)" % rl)
            continue
        L = open(os.path.join(cfg["core"], f)).read().splitlines()
        present = on_line(L, ln, DV.val(new), f, cfg)
        base = rl.split(" ")[0]
        want = G.get(base)
        if want is None:
            m = re.match(r"(seg\d)\.size", base)
            want = G.get(m.group(0)) if m else None
        if want is None:
            # remap geometry / derived / section-end: the twin quantity of the donor value, or the twin of donor value * k
            # divided by k (k = 8, 4, 4096: a quotient of an image address)
            dq = [k for k in common if QD[k] == DV.val(old)]
            tw_ = {QT[k] for k in dq}
            for kk in (1, 8, 4, 4096):
                tq = twin(DR, TR, DV.val(old) * kk)
                if tq is not None and tq % kk == 0:
                    tw_.add(tq // kk)
                    dq.append("twin(%s * %d) / %d" % (old, kk, kk) if kk > 1 else "twin(%s) = %s" % (old, lab(DR.resolve(DV.val(old)))))
            if DV.val(old) >= K:   # a shadow address: shadow(twin(the donor byte it shadows))
                xb = (DV.val(old) - K) * 8
                tq = twin(DR, TR, xb)
                if tq is not None:
                    tw_.add((tq >> 3) + K)
                    dq.append("shadow(twin(%#x)) = shadow(%#x)" % (xb, tq))
            ok = DV.val(new) in tw_ or DV.val(new) == DV.val(old) and not dq
            note("a3", ("GEO-SAME" if ok else "CANDIDATE") if present else "CANDIDATE", "%s:%d" % (f, ln + 1), old, new,
                 "%s: donor %s is %s; the target's same quantity %s; on the stage-out line: %s" % (
                     rl, old, ", ".join(dq[:2]) or "no named quantity", ", ".join("%#x" % x for x in sorted(tw_)[:2]) or "-", present))
        else:
            ok = DV.val(new) == want and present
            note("a3", "GEO-SAME" if ok else "CANDIDATE", "%s:%d" % (f, ln + 1), old, new,
                 "%s recomputed from the target = %#x; on the stage-out line: %s" % (base, want, present))
    dp_ = os.path.join(work, "decimals.tsv")
    for r in ([l.rstrip("\n").split("\t") for l in open(dp_).read().splitlines()[1:]] if os.path.exists(dp_) else []):
        if r[0] != "derived":
            continue
        m = re.match(r"(0x[0-9a-f]+) / (\d+)", r[7])
        num_, den = int(m.group(1), 16), int(m.group(2))
        tnum = twin(DR, TR, num_)
        ok = tnum is not None and int(r[4]) == tnum // den
        note("a3", "DERIVED-SAME" if ok else "CANDIDATE", "%s:%s" % (r[1], int(r[2]) + 1), r[3], r[4],
             "decimals.tsv derived: the donor's %s (%s) = %s; the numerator's twin %s / %d = %s, written %s" % (
                 r[7], lab(DR.resolve(num_)), r[3], "%#x" % tnum if tnum is not None else "-", den,
                 tnum // den if tnum is not None else "-", r[4]))
    lines.append("(a3) port_core's derived counts recomputed: %s" % dict((d, c) for (p, d), c in cnt.items() if p == "a3"))

    # ---- (b) GOT[0]: by value (every numeral equal to the target .got start) and by role (every numeral whose donor token
    # is the donor's .got start, i.e. the cell GOT[0] / a .got start bound: it must be the target's .got start)
    glo = [x for n, x, z in TR.secs if n == ".got"][0]
    dlo = [x for nn, x, z in DR.secs if nn == ".got"][0]
    w0, dw0 = TR.q(glo), DR.q(dlo)
    g0 = [n for n in nums if n[4] == glo]
    r0 = [n for n in nums if n[6] == dlo]
    bad0 = [n for n in r0 if n[4] != glo] + [n for n in g0 if n[6] != dlo]
    okb = w0 == 0 and dw0 == 0 and not bad0
    note("b", "OK-GOT0" if okb else "FINDING", " ".join("%s:%d" % (n[0], n[1]) for n in bad0) or "-", "%#x" % dlo, "%#x" % glo,
         "target .got start %#x, word %#x; donor's %#x, word %#x (neither image has .dynamic: OK-GOT0 wants 0); numerals "
         "naming the donor's GOT[0] %d, written as the target's .got start %d; numerals equal to the target's .got start %d%s" % (
             glo, w0, dlo, dw0, len(r0), sum(1 for n in r0 if n[4] == glo), len(g0),
             ("; NOT the target's GOT[0]: " + " ".join("%s:%d %s -> %s" % (n[0], n[1], n[5], n[3]) for n in bad0)) if bad0 else ""))
    lines.append("(b) GOT[0]: %s" % rows[-1][5])

    # ---- (c1) shadow addresses and model constants at or above 0x7fff0000
    shlo, shhi = K + (0x10000 >> 3), K + (DR.top_up >> 3)
    forms = (("s", lambda x: (x >> 3) + K), ("s&~7", lambda x: ((x >> 3) + K) & ~7), ("(s&~7)+8", lambda x: (((x >> 3) + K) & ~7) + 8))
    for n in code:
        if n[6] is None or n[6] < 0x7FFF0000:
            continue
        d, v = n[6], n[4]
        if shlo - 16 <= d <= shhi + 16:
            x0 = (d - K) * 8
            hit, mapped = None, []
            for b in range(max(0x10000, x0 - 64), min(DR.top_up + 1, x0 + 72)):
                for fn, f in forms:
                    if f(b) != d:
                        continue
                    tb = twin(DR, TR, b)
                    if tb is not None and (DR.isdata(b) or b == DR.top_up):
                        mapped.append((fn, b, tb))
                    if tb is not None and f(tb) == v:
                        hit = (fn, b, tb)
                        break
                if hit:
                    break
            if hit:
                note("c1", "SHADOW-SAME" if v != d else "SHADOW-SAME (kept)", "%s:%d" % (n[0], n[1]), n[5], n[3],
                     "%s of the donor byte %#x (%s) is the donor value; the same form of its twin %#x (%s) is the written value" % (
                         hit[0], hit[1], lab(DR.resolve(hit[1])), hit[2], lab(TR.resolve(hit[2]))), n[7])
            elif v in KNOWN_C:
                note("c1", "KNOWN", "%s:%d" % (n[0], n[1]), n[5], n[3], KNOWN_C[v], n[7])
            elif mapped:
                fn, b, tb = mapped[0]
                note("c1", "CANDIDATE", "%s:%d" % (n[0], n[1]), n[5], n[3],
                     "the donor value is %s of the data byte %#x (%s), whose twin %#x gives %#x, not the written value" % (
                         fn, b, lab(DR.resolve(b)), tb, dict(forms)[fn](tb)), n[7])
            elif v == d:
                note("c1", "CONST-SAME", "%s:%d" % (n[0], n[1]), n[5], n[3], "in the numeric range of the image's shadow, but the granule "
                     "%#x is no data byte of the donor (%s): a model constant, byte-identical" % (x0, DR.sec(x0) or "outside the sections"), n[7])
            else:
                note("c1", "FINDING", "%s:%d" % (n[0], n[1]), n[5], n[3], "moved, and no donor data byte in the granule %#x maps to it" % x0, n[7])
        else:
            if v == d:
                note("c1", "CONST-SAME", "%s:%d" % (n[0], n[1]), n[5], n[3], "model constant / shadow bound outside the donor image's shadow: byte-identical", n[7])
            elif v in KNOWN_C:
                note("c1", "KNOWN", "%s:%d" % (n[0], n[1]), n[5], n[3], KNOWN_C[v], n[7])
            else:
                note("c1", "FINDING", "%s:%d" % (n[0], n[1]), n[5], n[3], "a model constant moved", n[7])
    lines.append("(c1) numerals at or above 0x7fff0000: %s" % dict((d, c) for (p, d), c in cnt.items() if p == "c1"))

    # ---- (c1w) the format-string shadow windows, by their own rule: a file that defines FMT, SH_LO and SH_HI zeroes the
    # shadow hull of the NUL-terminated string at FMT (its hull_zero): SH_LO = floor8(shadow(FMT)), SH_HI =
    # floor8(shadow(FMT + len - 1)) + 8, len counting the NUL, the string read in the image; checked in the donor text
    # against the donor image (the rule is the donor's) and in stage-out against the target image
    sh = lambda x: (x >> 3) + K
    for t, dp in rel:
        txt = open(os.path.join(cfg["core"], t)).read()
        if "Definition SH_LO" not in txt or "Definition FMT :" not in txt:
            continue
        res = []
        for R, path in ((DR, dp), (TR, os.path.join(cfg["core"], t))):
            tx = open(path).read()
            g = lambda nm: re.search(r"Definition %s : Z := (0x[0-9a-fA-F]+|\d+)\." % nm, tx)
            fm, lo, hi = (DV.val(g(x).group(1)) if g(x) else None for x in ("FMT", "SH_LO", "SH_HI"))
            b = R.rd(fm, 512) if fm else None
            ln_ = b.index(b"\0") + 1 if b and b"\0" in b else None
            want = (sh(fm) & ~7, (sh(fm + ln_ - 1) & ~7) + 8) if ln_ else None
            res.append((fm, lo, hi, want, b[:ln_] if ln_ else None))
        (dfm, dlo_, dhi_, dwant, ds), (tfm, tlo_, thi_, twant, ts) = res
        ok = twant is not None and (tlo_, thi_) == twant
        shl = next(i + 1 for i, l in enumerate(txt.splitlines()) if "Definition SH_LO" in l)
        note("c1w", "WINDOW-SAME" if ok else "FINDING", "%s:%d" % (t, shl), "[%#x, %#x)" % (dlo_ or 0, dhi_ or 0), "[%#x, %#x)" % (tlo_ or 0, thi_ or 0),
             "FMT %#x %r: the rule gives [%#x, %#x) (donor: FMT %#x, the rule gives [%#x, %#x), the donor text %s)" % (
                 tfm or 0, ts, *(twant or (0, 0)), dfm or 0, *(dwant or (0, 0)),
                 "agrees" if dwant == (dlo_, dhi_) else "DISAGREES"))
    lines.append("(c1w) format-string shadow windows (FMT, SH_LO, SH_HI): %s" % dict((d, c) for (p, d), c in cnt.items() if p == "c1w"))

    # ---- (c2) divisors / multipliers / moduli / masks / shift counts
    for (f, ln), ns in bylinemap.items():
        L = ns[0][7]
        idx = 0
        for m in DV.NUM.finditer(L):
            n = ns[idx]
            idx += 1
            if n[8] in ("fetch", "word", "decode") or n[6] is None:
                continue
            if OPS.search(L[:m.start()]):
                if n[4] == n[6]:
                    cnt[("c2", "OP-SAME")] += 1
                else:
                    note("c2", "FINDING", "%s:%d" % (f, ln), n[5], n[3], "the right operand of %r moved" % L[max(0, m.start() - 12):m.start()].strip(), L)
            elif MUL.search(L[:m.start()]):
                # `A * B`: either side may be the multiplier; a moved right operand is listed, decided by its role below
                if n[4] == n[6]:
                    cnt[("c2", "MUL-SAME")] += 1
                else:
                    q = [k for k in common if QD[k] == n[6] and QT[k] == n[4]]
                    note("c2", "MUL-MOVED-AS-QUANTITY" if q else "FINDING", "%s:%d" % (f, ln), n[5], n[3],
                         "the right operand of %r moved%s" % (L[max(0, m.start() - 12):m.start()].strip(),
                                                             (": it is the image quantity %s in both images" % q[0]) if q else ""), L)
    lines.append("(c2) right operands of / mod Z.modulo Z.div Z.land Z.shiftr Z.shiftl ^ (and of *): %s" % dict((d, c) for (p, d), c in cnt.items() if p == "c2"))

    # ---- (c3) check.tsv arithmetic-constant rows
    ck = os.path.join(work, "check.tsv")
    so = {}
    for r in ([l.rstrip("\n").split("\t") for l in open(ck).read().splitlines()[1:]] if os.path.exists(ck) else []):
        if not r[4].startswith("arithmetic-constant"):
            continue
        if r[0] not in so:
            so[r[0]] = open(os.path.join(cfg["core"], r[0])).read().splitlines()
        L, ln = so[r[0]], int(r[1])
        present = on_line(L, ln, DV.val(r[3]), r[0], cfg)
        ok = r[2] == r[3] and present
        if ok:
            cnt[("c3", "CONST-SAME")] += 1
        else:
            note("c3", "FINDING", "%s:%d" % (r[0], ln + 1), r[2], r[3], "arithmetic-constant row: old %s new %s, on the stage-out line: %s" % (r[2], r[3], present))
    lines.append("(c3) check.tsv arithmetic-constant rows: %s" % dict((d, c) for (p, d), c in cnt.items() if p == "c3"))

    # ---- (c4) YG0f.v
    for n in nums:
        if n[0] != "Reusable/YG0f.v":
            continue
        if n[6] is not None and n[4] == n[6]:
            cnt[("c4", "CONST-SAME")] += 1
        else:
            note("c4", "FINDING", "%s:%d" % (n[0], n[1]), n[5] or "-", n[3], "a YG0f.v model constant differs from the donor's (or has no aligned donor token)", n[7])
    yg = [n for n in nums if n[0] == "Reusable/YG0f.v" and "kImgEnd" in n[7]]
    if yg:
        ie = yg[0][4]
        note("c4", "NOTE", "Reusable/YG0f.v:%d" % yg[0][1], yg[0][5], yg[0][3], "kImgEnd %#x: the donor image top %#x, the target's %#x; kImgEnd >= "
             "the target top: %s" % (ie, DR.top_up, TR.top_up, ie >= TR.top_up), yg[0][7])
    lines.append("(c4) Reusable/YG0f.v numerals: %s" % dict((d, c) for (p, d), c in cnt.items() if p == "c4"))

    # ---- (d) no-twin drops
    rx = re.compile(r"Definition tfib_A_([A-Za-z0-9_$]+?) : Z := (0x[0-9a-fA-F]+|\d+)\.")
    rxe = re.compile(r"Definition tfib_E_([A-Za-z0-9_$]+?) : Z := (0x[0-9a-fA-F]+|\d+)\.")
    dn = {m.group(1) for m in rx.finditer(open(os.path.join(cfg["dont"], "A/AB1w.v")).read())}
    so_t = open(os.path.join(cfg["core"], "A/AB1w.v")).read()
    tn = {m.group(1): DV.val(m.group(2)) for m in rx.finditer(so_t)}
    te = {m.group(1): DV.val(m.group(2)) for m in rxe.finditer(so_t)}
    dropped = sorted(dn - set(tn))
    nt = os.path.join(work, "no-twin.tsv")
    ntn = sorted({r.split("\t")[5] for r in open(nt).read().splitlines()[1:]} if os.path.exists(nt) else set())
    tsyms = collections.defaultdict(set)
    for s in ELFFile(open(cfg["tgt_syms"], "rb")).get_section_by_name(".symtab").iter_symbols():
        if s.name and s["st_info"]["type"] in ("STT_FUNC", "STT_OBJECT") and isinstance(s["st_shndx"], int):
            tsyms[s.name].add((s["st_value"], s["st_size"]))
    norm = lambda x: re.sub(r"^_+", "", re.sub(r"^_*interceptor_", "", x))
    tnorm = collections.defaultdict(set)
    for k in tsyms:
        tnorm[norm(k)].add(k)
    for nm in sorted(set(dropped) | set(ntn)):
        hits = sorted(({nm} if nm in tsyms else set()) | tnorm.get(norm(nm), set()))
        how = "dropped from stage-out's function table" if nm in dropped else "kept in stage-out's table"
        if not hits:
            note("d", "ABSENT", "A/AB1w.v", nm, "-", "%s; source_name in no-twin.tsv: %s; no FUNC / OBJECT symbol of that name in the target" % (how, nm in ntn))
            continue
        ok = []
        for h in hits:
            for (st, sz) in tsyms[h]:
                if tn.get(nm) == st and te.get(nm) == st + sz:
                    ok.append("stage-out holds tfib_A_/E_%s = %#x / %#x, the target symbol %s's start / end" % (nm, st, st + sz, h))
        if ok:
            note("d", "PRESENT-AS-TARGET-ROW", "A/AB1w.v", nm, "-", "%s as a donor pair; %s" % (how, ok[0]))
        else:
            note("d", "FINDING", "A/AB1w.v", nm, "-", "%s, but the target links %s (%s)" % (
                how, ", ".join(hits), ", ".join("%#x+%#x" % x for h in hits for x in sorted(tsyms[h]))))
    lines.append("(d) function-table rows dropped (donor tfib_A_ names absent from stage-out): %d; no-twin.tsv source names: %d; %s" % (
        len(dropped), len(ntn), dict((d, c) for (p, d), c in cnt.items() if p == "d")))

    for x in finds:
        lines.append("%s\t%s\t%s\t%s -> %s\t%s\t| %s" % (x[1], x[0], x[2], x[3], x[4], x[5], x[6]))
    nf = sum(1 for x in finds if x[1] == "FINDING")
    nc = sum(1 for x in finds if x[1] == "CANDIDATE")
    na = sum(1 for x in rows if x[1] == "AMBIGUOUS")
    nd = sum(1 for x in rows if x[1].startswith("DECIDED"))
    lines.append("result: FINDING rows %d; open CANDIDATE rows %d; open AMBIGUOUS rows %d; rows decided by hand (--decided) %d" % (nf, nc, na, nd))
    with open(os.path.join(out, "compcheck%s.tsv" % tag), "w") as f:
        f.write("part\tdecision\tat\tdonor\twritten\tevidence\tsource\n")
        for x in rows:
            f.write("\t".join(map(str, x)) + "\n")
    open(os.path.join(out, "compcheck%s.txt" % tag), "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
