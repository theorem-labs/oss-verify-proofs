#!/usr/bin/env python3
"""Second-stage evidence for the fuzz_uci by-value check (read-only).

Reads decval.py's TSV and decides, with image evidence, every row that decval's decision tree leaves to a
by-hand look:

  1. the method's DONOR-STALE rows                -> same bytes at that address in both images, or a constant
  2. every fetch / word row                       -> re-read from the target image in every lemma form
  3. every MOVED row (value changed from donor)   -> the new value is the donor value's twin in the target
                                                     (same symbol + same offset, same bytes, or a derived quantity)
  4. every UNMOVED, non-comment row that is not a target or shared value
                                                  -> context category (constant, mask, label, instruction word,
                                                     address in the byte-identical .rodata prefix)
  5. comment numerals that are donor image values
  6. the tfib_A_ / tfib_E_ table against every (duplicate-named) target symbol
  7. sweeps for fuzz_grant's / cgif's / fuzz_uci's start-up values and gp

  usage: decval_extra.py A.tsv [--core <tree>]
"""
import bisect
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import decval as DV  # noqa: E402

FL2 = re.compile(r"fetch_(?:word|half)\s+\S+\s*\(Z_to_bv 64 \(([A-Za-z0-9_']+)\s*\+\s*(0x[0-9a-fA-F]+|\d+)\)\)\s*=\s*Some \((0x[0-9a-fA-F]+)%bv : bv (\d+)\)")
FL3 = re.compile(r"fetch_(?:word|half)\s+\S+\s*\(Z_to_bv 64 ([A-Za-z_][A-Za-z0-9_']*)\)\s*=\s*Some \((0x[0-9a-fA-F]+)%bv : bv (\d+)\)")
FL4 = re.compile(r"fetch_(?:word|half)\s+\S+\s*\((0x[0-9a-fA-F]+)%bv : word\)\s*=\s*Some \((0x[0-9a-fA-F]+)%bv : bv (\d+)\)")
FL5 = re.compile(r"fetch_(?:word|half)\s+\S+\s*\(Z_to_bv 64 \((0x[0-9a-fA-F]+|\d+)\s*\+\s*(0x[0-9a-fA-F]+|\d+)\)\)\s*=\s*Some \((0x[0-9a-fA-F]+)%bv : bv (\d+)\)")
FL6 = re.compile(r"fetch_(?:word|half)\s+\S+\s*\(Z_to_bv 64 (0x[0-9a-fA-F]+)\)\s*=\s*Some \((0x[0-9a-fA-F]+)%bv : bv (\d+)\)")
ZDEF = re.compile(r"^Definition ([A-Za-z0-9_']+) : Z := (0x[0-9a-fA-F]+|\d+)\.")
LST = re.compile(r"Definition (\w+) : list \(bv 32\) :=\s*\[([^\]]*)\]", re.S)


def main():
    tsv = sys.argv[1]
    cfg = dict(DV.CFG)
    if "--core" in sys.argv:
        cfg["core"] = sys.argv[sys.argv.index("--core") + 1]
    core = cfg["core"]
    tgt = DV.Img(cfg["tgt_syms"], cfg["tgt_bytes"])
    don = DV.Img(cfg["don_syms"], cfg["don_bytes"])
    rel = DV.file_list(cfg)
    rows = [l.rstrip("\n").split("\t") for l in open(tsv)][1:]
    out_tsv = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else None
    dec = {}  # row index -> (stage-2 decision, evidence)
    cache = {}

    def line(t, n):
        if t not in cache:
            cache[t] = open(os.path.join(core, t)).read().splitlines()
        return cache[t][n - 1]

    def rd(img, a, n):
        for v, m, d in img.loads:
            if v <= a < v + m:
                return d[a - v: a - v + n]
        return None

    seg0 = lambda img: [d for v, m, d in img.loads if v == 0x10000][0]
    a0, b0 = seg0(tgt), seg0(don)
    k = 0x2E0
    while k < min(len(a0), len(b0)) and a0[k] == b0[k]:
        k += 1
    PREFIX = (0x102E0, 0x10000 + k)  # .rodata bytes identical in both images
    print("identical .rodata prefix of the two images: [%s, %s)" % tuple(map(hex, PREFIX)))

    # definitions in the whole core tree (W words, Z constants, word lists)
    wdef, zdef, lists = {}, collections.defaultdict(set), {}
    for dp, _, fns in os.walk(os.path.join(core, "lib")):
        for fn in sorted(fns):
            if not fn.endswith(".v"):
                continue
            txt = open(os.path.join(dp, fn), errors="ignore").read()
            for l in txt.splitlines():
                s = l.strip()
                m = DV.WDEF.match(s)
                if m:
                    wdef.setdefault(m.group(1), (int(m.group(3), 16), int(m.group(2))))
                m = ZDEF.match(s)
                if m:
                    zdef[m.group(1)].add(DV.val(m.group(2)))
            for m in LST.finditer(txt):
                lists[(fn, m.group(1))] = [x.strip() for x in m.group(2).replace("\n", " ").split(";") if x.strip()]

    text = [(v, d) for v, m, d in tgt.loads if v == min(x for x, _, _ in tgt.loads if x > 0x10000)][0]

    def findseq(words):
        v, d = text
        b = b"".join(w.to_bytes(4, "little") for w in words)
        out, i = [], d.find(b)
        while i != -1:
            out.append(v + i)
            i = d.find(b, i + 1)
        return out

    # ---- 2. fetch / word rows
    def wordok(a, w, bits):
        got = tgt.word(a)
        return got is not None and got & (0xFFFF if bits == 16 else 0xFFFFFFFF) == w

    def verify_fetch(l):
        res = []
        for m in DV.FLEM.finditer(l):
            if m.group(2) in wdef:
                w, bits = wdef[m.group(2)]
                res.append(wordok(int(m.group(1), 16), w, bits))
        for rx, f in ((FL2, lambda m: (zdef.get(m.group(1)), DV.val(m.group(2)), m.group(3), m.group(4))),
                      (FL3, lambda m: (zdef.get(m.group(1)), 0, m.group(2), m.group(3))),
                      (FL4, lambda m: ({int(m.group(1), 16)}, 0, m.group(2), m.group(3))),
                      (FL5, lambda m: ({DV.val(m.group(1))}, DV.val(m.group(2)), m.group(3), m.group(4))),
                      (FL6, lambda m: ({int(m.group(1), 16)}, 0, m.group(2), m.group(3)))):
            for m in rx.finditer(l):
                base, off, w, bits = f(m)
                res.append(bool(base) and len(base) == 1 and wordok(list(base)[0] + off, int(w, 16), int(bits)))
        return res

    w_ok = set()
    for t, dp in rel:
        for l in open(os.path.join(core, t)).read().splitlines():
            for m in DV.FLEM.finditer(l):
                if m.group(2) in wdef and wordok(int(m.group(1), 16), *wdef[m.group(2)]):
                    w_ok.add(m.group(2))
    list_ok = {}
    for key, names in lists.items():
        if all(n in wdef for n in names):
            list_ok[key] = findseq([wdef[n][0] for n in names])
    inlist = {n: key for key, names in lists.items() for n in names if len(list_ok.get(key, [])) == 1}
    fstat, wstat, wbad = collections.Counter(), collections.Counter(), []
    word_runs = {}
    for ri, r in enumerate(rows):
        ro = DV.role(r[8])
        if ro == "fetch":
            res = verify_fetch(line(r[0], int(r[1])))
            fstat["verified" if res and all(res) else "NOT VERIFIED"] += 1
            dec[ri] = ("TARGET", "fetch lemma re-read from the target image" if res and all(res) else "FETCH NOT VERIFIED")
            if not (res and all(res)):
                wbad.append(r)
        elif ro == "word":
            m = DV.WDEF.match(r[8])
            name = m.group(1) if m else r[8].split()[1]
            if name in w_ok:
                why = "word: fetch pair verified"
            elif name in inlist:
                why = "word: its list %s found once in the target .text, at %s" % (
                    inlist[name][1], hex(list_ok[inlist[name]][0]))
            else:
                # a run of consecutive definitions in the same file, found as a sequence in the target .text
                if r[0] not in word_runs:
                    defs = [DV.WDEF.match(x.strip()) or re.match(r"^Definition (\w+) : bv 32 := (0x[0-9a-fA-F]+)\.", x.strip())
                            for x in open(os.path.join(core, r[0])).read().splitlines()]
                    word_runs[r[0]] = [(d.group(1), int(d.group(3) if d.lastindex == 3 else d.group(2), 16)) for d in defs if d]
                run = [w for n, w in word_runs[r[0]] if n not in w_ok and n not in inlist]
                names = [n for n, w in word_runs[r[0]] if n not in w_ok and n not in inlist]
                # split into maximal groups by name prefix (W_c9..., PW...)
                pre = re.sub(r"[0-9a-f]{3}$|\d$", "", name)
                grp = [w for n, w in zip(names, run) if re.sub(r"[0-9a-f]{3}$|\d$", "", n) == pre]
                hits = findseq(grp)
                if len(hits) == 1:
                    why = "word: unpaired run %s* (%d words) found once in the target .text, at %s" % (
                        pre, len(grp), hex(hits[0]))
                else:
                    why = "word: NOT VERIFIED"
                    wbad.append(r)
            wstat[why] += 1
            dec[ri] = ("TARGET" if "NOT" not in why else "WORD NOT VERIFIED", why)
    print("fetch rows:", dict(fstat))
    print("word rows:", dict(wstat))
    for r in wbad:
        print("UNVERIFIED\t%s:%s\t%s" % (r[0], r[1], r[8][:120]))

    # ---- symbol twins (moved rows)
    def pseudo(img):
        out = []
        for i, (v, m, d) in enumerate(sorted(img.loads)):
            lp, hp = v & ~0xFFF, (v + m + 0xFFF) & ~0xFFF
            out += [("PT_LOAD%d.lo" % i, v, 0), ("PT_LOAD%d.hi" % i, v + m, 0), ("PT_LOAD%d.lo_page" % i, lp, 0),
                    ("PT_LOAD%d.hi_page" % i, hp, 0), ("PT_LOAD%d.pagesize" % i, hp - lp, 0)]
        out += [("img_top_up", img.top_up, 0), ("img_span", img.top_up - 0x10000, 0)]
        for n, lo, sz in img.secs:
            out += [("sec:" + n, lo, sz), ("sec:" + n + ".hi", lo + sz, 0)]
        return out

    tmm = collections.defaultdict(set)
    for a, s, n in tgt.allsyms:
        if not n.startswith("$"):
            tmm[n].add((a, s))
    for n, a, s in pseudo(tgt):
        tmm[n].add((a, s))
    dn = sorted([(a, s, n) for a, s, n in don.allsyms if not n.startswith("$")] + [(a, s, n) for n, a, s in pseudo(don)])
    ds = [a for a, s, n in dn]

    def twin(d, v):
        i = bisect.bisect_right(ds, d)
        j, k = i - 1, 0
        while j >= 0:
            a, s, n = dn[j]
            if d - a > 0x600000:
                break
            if (a <= d <= a + s and (s > 0 or a == d)) or (k < 40 and 0 <= d - a < 0x4000):
                for ta, ts in tmm.get(n, ()):
                    if ta + (d - a) == v:
                        return "%s+0x%x" % (n, d - a)
                    if s and ts and a + s == d and ta + ts == v:
                        return "%s.end" % n
            j -= 1
            k += 1
        return None

    def cstart(img, a):
        s = a
        while s > 0x102E0 and rd(img, s - 1, 1) not in (b"\0", None):
            s -= 1
        e = a
        while rd(img, e, 1) not in (b"\0", None):
            e += 1
        return s, rd(img, s, e - s + 1)

    def twin_full(d, v, src):
        t = twin(d, v)
        if t:
            return "symbol", t
        for s, add, lab in ((1, 0x10000, "x-0x10000"), (4, 0, "x/4"), (8, 0, "x/8"), (8, 0x80000, "(x-0x10000)/8"),
                            (8, 8, "x/8-1"), (1, 1, "x-1")):
            t = twin(d * s + add, v * s + add)
            if t:
                return "derived", "%s of %s" % (lab, t)
        a, b = rd(don, d - 8, 16), rd(tgt, v - 8, 16)
        if a and b and len(a) == 16 and a == b and any(a):
            return "bytes", "16 bytes around the address equal"
        if PREFIX[0] <= d < 0x30000 and PREFIX[0] <= v < 0x30000:
            sd, bd = cstart(don, d)
            sv, bv = cstart(tgt, v)
            if bd and bd == bv and d - sd == v - sv and len(bd) > 2:
                return "string", "inside the string %r (donor 0x%x, target 0x%x), same offset" % (bd[:40], sd, sv)
            # jump-table entry (a 32-bit offset from the table base) or the end of one: the entry's address plus
            # the entry it holds lands at the same symbol + offset in both images
            for dd, vv, lab in ((d, v, "address"), (d - 4, v - 4, "end")):
                ed = int.from_bytes(rd(don, dd, 4), "little", signed=True)
                ev = int.from_bytes(rd(tgt, vv, 4), "little", signed=True)
                t = twin(dd + ed, vv + ev)
                if t and not t.startswith(("sec:", "PT_LOAD", "img_")):
                    return "jumptable", "jump-table entry %s: its address + the entry it holds lands at %s in both images" % (lab, t)
        # value held in memory at a stated address: lit4 / lit8 / flit8 A V, val_mem .. A n V
        cands = [(m.group(1), m.group(2), 8 if m.group(0).startswith(("lit8", "flit8")) else 4)
                 for m in re.finditer(r"(?:lit4|lit8|flit8)\s+(0x[0-9a-fA-F]+)\s+(0x[0-9a-fA-F]+)", src)]
        if "val_mem" in src:
            cands += [(m.group(1), m.group(3), int(m.group(2)))
                      for m in re.finditer(r"(0x[0-9a-fA-F]+)\s+([1248])\s+(0x[0-9a-fA-F]+)", src)]
        for at, vt, n in cands:
            addr, vtok = int(at, 16), int(vt, 16)
            if vtok == v and int.from_bytes(rd(tgt, addr, n) or b"", "little") == v:
                return "memory", "the target image holds 0x%x at 0x%x" % (v, addr)
        # zero-shadow length / 8: (img_top_up - __stop_asan_globals) / 8
        sg_d, sg_t = don.syms.get("__stop_asan_globals"), tgt.syms.get("__stop_asan_globals")
        if sg_d and sg_t and d == (don.top_up - sg_d[0]) // 8 and v == (tgt.top_up - sg_t[0]) // 8:
            return "derived", "(img_top_up - __stop_asan_globals) / 8"
        return None, None

    depth_at = {}

    def in_comment(t, n):
        """True when line n of t starts inside an open (* ... *) comment."""
        if t not in depth_at:
            ds, dep = [], 0
            for l in open(os.path.join(core, t)).read().splitlines():
                ds.append(dep)
                dep = max(0, dep + l.count("(*") - l.count("*)"))
            depth_at[t] = ds
        return depth_at[t][n - 1] > 0

    def bullet(r):
        """decval's role() reads a line starting with '*' as a comment; outside a comment block it is a Coq bullet."""
        s = r[8].lstrip()
        return r[5].startswith("comment") and s.startswith("*") and not s.startswith("*)") and not in_comment(r[0], int(r[1]))

    moved = [(ri, r) for ri, r in enumerate(rows) if r[6] == "False"]
    mstat, mfail, mby = collections.Counter(), [], collections.defaultdict(collections.Counter)
    for ri, r in moved:
        kind, why = twin_full(DV.val(r[7]), int(r[3]), line(r[0], int(r[1])))
        code = DV.role(r[8]) not in ("comment", "decode") or bullet(r)
        if code and (ri not in dec or DV.role(r[8]) not in ("fetch", "word")):
            dec[ri] = ("TARGET" if kind else "MOVED, NO TWIN", "moved: %s %s" % (kind or "", why or ""))
        mstat[(r[4], kind or "NO TWIN")] += 1
        if kind not in (None, "symbol"):
            mby[kind][why if kind != "symbol" else ""] += 1
        if not kind:
            mfail.append(r)
    print("moved rows (value changed from the donor's):", len(moved))
    for k_, c in sorted(mstat.items()):
        print("  %-8s %-10s %d" % (k_[0], k_[1], c))
    for kind in ("derived", "bytes", "string", "jumptable", "memory"):
        for why, c in sorted(mby[kind].items()):
            print("  %s: %s  x%d" % (kind, why, c))
    for r in mfail:
        print("NO-TWIN\t%s:%s\t%s -> %s\t%s" % (r[0], r[1], r[7], r[2], r[8][:110]))

    # ---- 1 + 4. unmoved / unaligned rows that are not target, shared, comment or decoded
    CTX = [
        ("instruction-word literal handed to icpt_ld8", r"icpt_ld8"),
        ("instruction word or field (decode lemma / Z_to_bv word / table lookup of a word)",
         r"decode_any|decode_c|replace \(0x[0-9a-f]+%bv : bv 32\)|tbl_ok 0x[0-9a-f]+ 0x[0-9a-f]{8}"),
        ("model label of the kernel's allocator model (mcheck / fail / spin / ISpin pc; Reusable/YG00.v holds the same)", r"\b(mcheck|FCheck|spin|ISpin)\b"),
        ("allocator / trace constant (sizes in KMmap / Malloc / Realloc / LMem traces)", r"KMmap|KMremap|KMunmap|KBrk|Malloc|Realloc|LMem"),
    ]
    MAPFLAGS = {0x100022, 0x100032, 0x104022, 0x104032}
    nb = collections.Counter((r[6], DV.val(r[2]) in tgt.values and DV.val(r[2]) in don.values) for r in rows if bullet(r))
    print("rows decval's role() calls comment that are Coq bullets (code), by unmoved / shared-value:", dict(nb))
    unm = [(ri, r) for ri, r in enumerate(rows) if r[6] != "False"
           and ((r[4] in ("OTHER", "DONOR-STALE") and not r[5].startswith(("comment", "decoded"))) or bullet(r))]
    ustat, uvals = collections.Counter(), collections.defaultdict(collections.Counter)
    for ri, r in unm:
        v, src = int(r[3]), line(r[0], int(r[1]))
        if bullet(r) and v in tgt.values and v in don.values:
            cat = "SHARED: same value in both images (a Coq bullet line decval reads as a comment)"
        elif in_comment(r[0], int(r[1])):
            cat = "inside a multi-line comment (a line that does not start with the comment opener)"
        elif PREFIX[0] <= v < PREFIX[1] and v not in (0x11000, 0x12000) and rd(tgt, v, 8) == rd(don, v, 8):
            cat = "SHARED by bytes: address in the byte-identical .rodata prefix"
        elif v in MAPFLAGS:
            cat = "Linux mmap flag sum (MAP_FIXED_NOREPLACE|MAP_NORESERVE|MAP_ANONYMOUS|MAP_PRIVATE and neighbours)"
        else:
            cat = "constant / size / mask / bound / arithmetic (no address role)"
            for lab, rx in CTX:
                if re.search(rx, src):
                    cat = lab
                    break
        ustat[(r[4], cat)] += 1
        uvals[cat][v] += 1
        dec[ri] = ("SHARED" if cat.startswith("SHARED") else "OTHER", cat)
    print("unmoved / unaligned non-comment rows outside TARGET and SHARED:", len(unm))
    for k_, c in sorted(ustat.items()):
        print("  %-11s %-100s %d" % (k_[0], k_[1], c))
    for cat, vs in sorted(uvals.items()):
        print("  values [%s]: %s" % (cat[:40], " ".join("%s(%d)x%d" % (hex(v), v, c) for v, c in sorted(vs.items()))))

    # ---- 5. comment numerals that are donor image values (and not target values)
    print("comment numerals that are donor image values and not target values:")
    for r in rows:
        if r[5].startswith("comment"):
            v = int(r[3])
            if v in don.values and v not in tgt.values:
                print("  %s:%s\t%s\t%s" % (r[0], r[1], r[2], ",".join(sorted(x for x in don.why.get(v, ()) if not x.startswith("$"))[:2])))

    # ---- 6. tfib table against every target symbol (duplicates included)
    starts = {a for a, s, n in tgt.allsyms}
    ends = {a + s for a, s, n in tgt.allsyms} | starts
    tf = collections.Counter()
    for i, l in enumerate(open(os.path.join(core, "lib/A/AB1w.v")).read().splitlines()):
        for m in DV.TFIB.finditer(l):
            v = int(m.group(3), 0)
            ok = v in starts if m.group(1) == "A" else v in ends
            tf[(m.group(1), "target symbol start" if m.group(1) == "A" else "target symbol end or next start") if ok else (m.group(1), "OTHER")] += 1
    print("tfib table:", dict(tf))

    # ---- 7. sweeps over every numeral of the relocated files (any range)
    sweep = [("fuzz_grant builtin_tls", don.syms["builtin_tls"][0]), ("fuzz_grant tp", don.syms["builtin_tls"][0] + 200),
             ("fuzz_grant builtin_tls as decode's DECIMAL-VALUES.md quotes it", 0x5D7A48),
             ("fuzz_grant tp as decode's DECIMAL-VALUES.md quotes it", 0x5D7B10),
             ("fuzz_grant image top", don.top_up), ("fuzz_grant rw_lo", don.rw_lo), ("fuzz_grant entry", 0x307DC),
             ("fuzz_grant last PT_LOAD end", don.top), ("cgif builtin_tls", 0x5D8EC8), ("cgif tp", 0x5D8F90),
             ("cgif image top", 0x5FB000), ("cgif rw_lo", 0x9F000), ("cgif entry", 0x3030C),
             ("gp shifted as a data address (decode TAGSCAN)", 0x10818), ("__global_pointer$ (both)", tgt.syms["__global_pointer$"][0]),
             ("fuzz_uci builtin_tls", tgt.syms["builtin_tls"][0]), ("fuzz_uci tp", tgt.syms["builtin_tls"][0] + 200),
             ("fuzz_uci image top", tgt.top_up), ("fuzz_uci rw_lo", tgt.rw_lo), ("fuzz_uci entry", 0x2FBF0)]
    hits = collections.defaultdict(list)
    gpwin = collections.Counter()
    want = {v for _, v in sweep}
    for t, dp in rel:
        for i, l in enumerate(open(os.path.join(core, t)).read().splitlines()):
            for m in DV.NUM.finditer(l):
                v = DV.val(m.group(0))
                if v in want:
                    hits[v].append("%s:%d" % (t, i + 1))
                if 0x10800 - 0x800 <= v < 0x10800 + 0x800:
                    gpwin[v] += 1
    for lab, v in sweep:
        h = hits[v]
        print("sweep %-62s %-9s %-8d %3d  %s" % (lab, hex(v), v, len(h), " ".join(h[:6])))
    print("numerals in the gp-relative window [gp-0x800, gp+0x800) = [0x10000, 0x11000):",
          " ".join("%s x%d%s" % (hex(v), c, "" if (v < 0x102E0 or rd(tgt, v, 8) == rd(don, v, 8)) else " BYTES-DIFFER")
                   for v, c in sorted(gpwin.items())))


    if out_tsv:
        with open(out_tsv, "w") as f:
            f.write("file\tline\ttoken\tvalue\tmethod_class\tunmoved\tdonor_token\tstage2\tevidence\tsource\n")
            for ri, r in enumerate(rows):
                k, why = dec.get(ri, (r[4], r[5]))
                f.write("\t".join([r[0], r[1], r[2], r[3], r[4], r[6], r[7], k, why, r[8]]) + "\n")


if __name__ == "__main__":
    main()
