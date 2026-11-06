#!/usr/bin/env python3
"""Evidence for the rows of the libdiginet/fuzz_transport by-value check that are decided by reading the TARGET ELF, not by
a tool's class (read-only; libdiginet/fuzz_decode's decval_hand.py of D9 (sha256 1052fb862c8a; internal record) with the pins and trees changed and
sections 4 and 5 added). Reads decval_extra.py's TSV and prints, per row:

  1. .got cells: every numeral whose value lies in the target's .got. The cell must be 8-byte aligned; the 8 bytes the
     target image holds there are read and named by the unstripped twin's symbols; the donor token the row was relocated
     from is read the same way in the donor image. GOT-SAME = both cells hold the same symbol (or both 0); else GOT-DIFF.
     A value the text states for a .got cell (`mkChunk A (CVal 8 (SLit V))`, `lit8 A V`) must be the cell's bytes.
  2. constants: every row the two stages leave as OTHER with no address role (constant / size / mask / bound, mmap
     flags, instruction-word literals, model labels) and the stage-1 DONOR-STALE rows decided as a constant. The row
     must be UNCHANGED from the donor text: the aligned donor token holds the same value, or (no alignment) the donor
     file holds the same token. Per value: the definitions of the run's text that name it, where it lies in the target.
  3. the stage-1 DONOR-STALE rows: the 16 bytes at the address in both images and the symbol there.
  4. the stage-2 MOVED, NO TWIN rows: the 8 bytes AT the address (a constant-pool entry, named by its own value) or the 8
     bytes BEFORE it (the end of one) in both images; SAME-8 when equal, nonzero and found once in the target's .rodata.
  5. comment numerals that are donor image values and not target values: each must lie in the donor's notice block (the
     lines above port_core's provenance line, which port_core keeps byte for byte by design).

  usage: decval_hand.py <rundir> <decval-stage2.tsv> [--out <tsv>]   (env P, PG, EV as decval.py)
"""
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import decval as DV  # noqa: E402

CONST = ("constant / size / mask / bound / arithmetic", "Linux mmap flag sum", "instruction-word literal handed to icpt_ld8",
         "instruction word or field", "model label of the kernel's allocator model")
CHUNK = re.compile(r"mkChunk (0x[0-9a-fA-F]+) \(CVal 8 \(SLit (0x[0-9a-fA-F]+|\d+)\)\)|\blit8 (0x[0-9a-fA-F]+) (0x[0-9a-fA-F]+|\d+)")


class Elf:
    def __init__(self, img):
        self.img = img
        self.sec = {n: (a, z) for n, a, z in img.secs}

    def q(self, a):
        return self.img.word(a, 8)

    def name(self, a):
        if not a:
            return "0"
        c = [(x, z, n) for x, z, n in self.img.allsyms if x <= a < x + max(z, 1) and not n.startswith("$")]
        if not c:
            return "%#x (no symbol)" % a
        x, z, n = min(c, key=lambda t: (t[0] != a, t[1]))
        return n if x == a else "%s+%#x" % (n, a - x)

    def where(self, v):
        s = [n for n, (a, z) in self.sec.items() if a <= v < a + z]
        return s[0] if s else ("in a PT_LOAD" if any(a <= v < a + m for a, m, _ in self.img.loads) else "outside the image")


def main():
    cfg = DV.setup(sys.argv[1:])
    tsv = sys.argv[2]
    out_tsv = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else None
    core = cfg["core"]
    tgt = DV.Img(cfg["tgt_syms"], cfg["tgt_bytes"])
    don = DV.Img(cfg["don_syms"], cfg["don_bytes"])
    T, D = Elf(tgt), Elf(don)
    rows = [l.rstrip("\n").split("\t") for l in open(tsv)][1:]
    srcs = dict(DV.file_list(cfg))
    cache = {}

    def text(path):
        if path not in cache:
            cache[path] = open(path).read()
        return cache[path]
    out = []

    # ---- 1. .got cells
    glo, gsz = T.sec[".got"]
    dlo, dsz = D.sec[".got"]
    print(".got: target [%#x, %#x), donor [%#x, %#x)" % (glo, glo + gsz, dlo, dlo + dsz))
    cells, gst = {}, collections.Counter()
    for r in rows:
        v = int(r[3])
        if not glo <= v < glo + gsz:
            continue
        tv = T.q(v)
        d = DV.val(r[6]) if r[6] else None
        dv = D.q(d) if d is not None and dlo <= d < dlo + dsz else None
        tn, dn = T.name(tv), (D.name(dv) if dv is not None else "no aligned donor .got token")
        ok = v % 8 == 0 and dv is not None and tn == dn
        dec = "GOT-SAME" if ok else "GOT-DIFF"
        gst[dec] += 1
        cells.setdefault(v, (tv, tn, set()))[2].add("%s:%s" % (r[0], r[1]))
        out.append((dec, r[0], r[1], r[2], "target cell %#x holds %#x = %s; donor cell %s holds %s = %s" % (
            v, tv, tn, r[6] or "-", "%#x" % dv if dv is not None else "-", dn), r[9][:160]))
        if not ok:
            print("GOT-DIFF\t%s:%s\t%s" % (r[0], r[1], out[-1][4]))
    print(".got rows: %d %s; %d distinct cells:" % (sum(gst.values()), dict(gst), len(cells)))
    for v in sorted(cells):
        tv, tn, at = cells[v]
        print("  cell %#x (.got+%#x) holds %#x = %s  x%d" % (v, v - glo, tv, tn, len(at)))
    nst = collections.Counter()
    for t, dp in DV.file_list(cfg):
        for i, l in enumerate(text(os.path.join(core, t)).splitlines()):
            for m in CHUNK.finditer(l):
                a, s = (m.group(1), m.group(2)) if m.group(1) else (m.group(3), m.group(4))
                a, s = int(a, 16), DV.val(s)
                if glo <= a < glo + gsz:
                    ok = T.q(a) == s
                    nst["stated value = cell bytes" if ok else "STATED VALUE DIFFERS"] += 1
                    if not ok:
                        print("GOT-STATED-DIFF\t%s:%d\tcell %#x states %#x, the image holds %#x" % (t, i + 1, a, s, T.q(a)))
    print(".got cell values stated by the text (mkChunk A (CVal 8 (SLit V)) / lit8 A V):", dict(nst))

    # ---- 2. constants
    defs = collections.defaultdict(set)
    for t, dp in DV.file_list(cfg):
        for m in re.finditer(r"Definition (\w+) : (?:Z|nat|N) := (0x[0-9a-fA-F]+|\d+)(?:%\w+)?\.", text(os.path.join(core, t))):
            defs[DV.val(m.group(2))].add("%s (%s)" % (m.group(1), t))
    cst, perv = collections.Counter(), collections.defaultdict(collections.Counter)
    for r in rows:
        if not ((r[7] == "OTHER" and r[8].startswith(CONST)) or (r[4] == "DONOR-STALE" and r[8].startswith(CONST[0]))):
            continue
        v = int(r[3])
        if r[5] == "True":
            same = "UNCHANGED (aligned donor token %s)" % r[6]
        elif r[5] == "None":
            dtoks = {DV.val(x) for x in DV.NUM.findall(text(srcs[r[0]]))}
            same = "UNCHANGED (no alignment; the donor file holds %s)" % r[2] if v in dtoks else "CHANGED (the donor file does not hold it)"
        else:
            same = "CHANGED (donor token %s)" % r[6]
        cst[same.split(" ")[0]] += 1
        perv[v][same.split(" ")[0]] += 1
        out.append(("CONST-" + same.split(" ")[0], r[0], r[1], r[2], "%s; %s" % (same, r[8]), r[9][:160]))
        if not same.startswith("UNCHANGED"):
            print("CONST-CHANGED\t%s:%s\t%s\t%s" % (r[0], r[1], r[2], r[9][:120]))
    print("constant rows: %d %s; per value (count, the run's definitions of it, where it lies in the target):" % (
        sum(cst.values()), dict(cst)))
    for v in sorted(perv):
        print("  %#x (%d) x%d %s; defined as %s; target: %s" % (
            v, v, sum(perv[v].values()), dict(perv[v]), ", ".join(sorted(defs.get(v, ()))[:3]) or "-", T.where(v)))

    # ---- 3. stage-1 DONOR-STALE rows: the bytes at the address in both images
    for r in rows:
        if r[4] != "DONOR-STALE":
            continue
        v = int(r[3])
        bt, bd = ((img.word(v, 16) or 0).to_bytes(16, "little") for img in (tgt, don))
        print("DONOR-STALE\t%s:%s\t%#x\ttarget %s %r [%s] %s; donor %s %r [%s] %s; stage 2: %s" % (
            r[0], r[1], v, bt.hex(), bt.split(b"\0")[0], T.where(v), T.name(v), bd.hex(), bd.split(b"\0")[0], D.where(v),
            D.name(v), r[8]))

    # ---- 4. stage-2 MOVED, NO TWIN rows: the 8 bytes at (or before) the address in both images
    ro_lo, ro_sz = T.sec[".rodata"]
    ro = tgt.word(ro_lo, ro_sz).to_bytes(ro_sz, "little")
    nt = collections.Counter()
    for r in rows:
        if r[7] != "MOVED, NO TWIN":
            continue
        v, d = int(r[3]), DV.val(r[6])
        dec, notes = "NO-TWIN", []
        for lab, dt, vt in (("the 8 bytes at the address", d, v), ("the 8 bytes before the address (an end)", d - 8, v - 8)):
            wd, wt = don.word(dt, 8), tgt.word(vt, 8)
            if wd is None or wt is None:
                # an address outside its image's loaded bytes has no bytes to compare: the row stays open, with the reason
                notes.append("%s: %s outside its image's loaded bytes" % (lab, " and ".join(
                    s for s, w in (("donor %#x" % dt, wd), ("target %#x" % vt, wt)) if w is None)))
                continue
            bd, bt = wd.to_bytes(8, "little"), wt.to_bytes(8, "little")
            n = ro.count(bt)
            if bd == bt and any(bt) and n == 1:
                dec, ev = "SAME-8", "%s: donor %#x and target %#x both hold %s, found once in the target .rodata" % (
                    lab, dt, vt, bt.hex())
                break
        if dec == "NO-TWIN":
            ev = "no 8-byte match" + ("; " + "; ".join(notes) if notes else "")
        nt[dec] += 1
        out.append((dec, r[0], r[1], r[2], "donor token %s -> %s; %s" % (r[6], r[2], ev), r[9][:160]))
        print("%s\t%s:%s\t%s -> %s\t%s" % (dec, r[0], r[1], r[6], r[2], ev))
    print("stage-2 NO TWIN rows: %d %s" % (sum(nt.values()), dict(nt)))

    # ---- 5. comment numerals that are donor image values and not target values: in the donor's notice block?
    def prov_line(t):
        """1-based line number of port_core's provenance line: the first line where stage-out differs from stage."""
        a = text(os.path.join(core, t)).splitlines()
        b = text(os.path.join(cfg["dont"], t)).splitlines()
        for i, (x, y) in enumerate(zip(a, b)):
            if x != y:
                return i + 1
        return len(b) + 1
    cs = collections.Counter()
    for r in rows:
        if not r[8].startswith("comment"):
            continue
        v = int(r[3])
        if v in don.values and v not in tgt.values:
            pl = prov_line(r[0])
            dec = "NOTICE" if int(r[1]) < pl and r[5] == "True" else "COMMENT-DONOR-VALUE"
            cs[dec] += 1
            out.append((dec, r[0], r[1], r[2], "donor image value in a comment; port_core's provenance line is %s:%d; "
                        "unmoved from the donor text: %s" % (r[0], pl, r[5]), r[9][:160]))
            print("%s\t%s:%s\t%s\tprovenance line %d, unmoved %s" % (dec, r[0], r[1], r[2], pl, r[5]))
    print("comment numerals that are donor image values and not target values: %d %s" % (sum(cs.values()), dict(cs)))
    if out_tsv:
        with open(out_tsv, "w") as f:
            f.write("decision\tfile\tline\ttoken\tevidence\tsource\n")
            for x in out:
                f.write("\t".join(x) + "\n")


if __name__ == "__main__":
    main()
