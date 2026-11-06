#!/usr/bin/env python3
"""g10_triage.py -- every row port_addr_check 0d24592683b6 changes against 3d2eee813cce on the gates-Y file set, each
row triaged by a measured rule.

Usage: g10_triage.py --run NAME:OLD.tsv:NEW.tsv:G1OUT.tsv [--run ...] --pac PORT_ADDR_CHECK.py --lib BASE_LIB \\
                     --cgif-lib CGIF_LIB --pin K=PIN --twin K=TWIN (K = A, B, P) --cgif-pin P=PIN --cgif-twin P=TWIN \\
                     --out OUT.tsv

OLD.tsv / NEW.tsv are the --out tables of 3d2eee813cce and 0d24592683b6 with the same arguments (G10-address-check-0d24.md
gives the commands); G1OUT.tsv is g1_triage.py's output on NEW.tsv. BASE_LIB is proofs/libreac/fuzz_disco/lib at the
series base, CGIF_LIB proofs/cgif/cgif_file_fuzzer/lib at the donor commit. The pins and their unstripped twins (.symtab)
are fuzz_disco's images A / B / P and cgif's image P. The flagged classes are read from the tool (`--list-flag-classes`).

Method. The rows of a table are its lines that do not start with `#`, after the header. A row's key is (src_file,
src_line, dst_file, dst_line, sentence, idx, kind, src_value, dst_value) with its occurrence number; the two tables must
hold the same keys (the pairing did not change), and a row DIFFERS when any column differs. A differing row whose
verdict is the same is NOTE-ONLY. A row whose verdict moved gets the FIRST rule (RULES, in order) that holds; a rule
reads the numeral's role from its line and makes the measurement it names on the pins, twins and lib trees, and holds
only when the measurement agrees. A moved row no rule takes is UNTRIAGED. Every row g1_triage.py leaves UNTRIAGED in
NEW.tsv must be a moved row triaged here. Exit 0 only when that holds and no row is UNTRIAGED.

Output: one row per differing row, per run in key order: run, old_verdict, new_verdict, image, where (port file:line),
sentence, idx, src_value, dst_value, rule, detail.
"""
import argparse
import bisect
import collections
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from g1_triage import Img, Twin  # noqa: E402

RULES = collections.OrderedDict([
    ("NOTE-ONLY", "the verdict is unchanged; only the note text differs (the detail gives the text removed and added)"),
    ("ALLOC-MAP-SIZE", "262144 = 2^18, the ASan primary allocator's map unit (YG00 kUserMapSize / kFreeArrayMapSize), a "
                       "LENGTH: the line names the constant, or pins the register the allocator code sets with it, or "
                       "states it as the length register a1 of an mmap ecall (a7 = 222); measured: the image's pin holds "
                       "`lui rX, 0x40` in SizeClassAllocator64::PopulateFreeArray and ::EnsureFreeArraySpace (twin "
                       ".symtab); it is no address, the checker's code-pointer reading of 0x40000 is a coincidence"),
    ("CAPACITY-DOUBLING", "a capacity of the input read loop, 2 * the previous capacity, compared with dlen data in the "
                          "same Qed proof (RPX_closed): a byte count of the program model, no image quantity"),
    ("FOOTPRINT-LENGTH", "the length paired with LMem (SP k 0) in a footprint list: measured = the user block (SP k o, n) "
                         "of the same Example rounded up to 4096 bytes; the kernel checks the Example (vm_compute)"),
    ("FAKESTACK-OFFSET", "FS_FROFF, the offset of size class CID's frames in the ASan fake stack, added to the fake "
                         "stack's base ly_F (a runtime mapping; Lemma frame_addr_cid, Qed); measured by the kernel on "
                         "the image's own code: s1C1_eq (vm_compute over the image B code, Qed) forms base + FS_FROFF"),
    ("LOOSE-ENTRY-BOUND", "an upper bound on the end of every icpt_rodata entry, proved entry by entry (cbn; lia; Qed); "
                          "measured: the highest entry (YE2y.v) ends below it; the bound names no object"),
    ("JAL-SAME-CALLEE", "an instruction word whose fetch pc the previous lemma states (FS_<n>: fetch_word at "
                        "src0_A_<f> + off): measured: the pin's word at the twin's <f> + off is this word and its jal "
                        "target is the function cgif's word at cgif's <f> + off calls (both twins' .symtab)"),
    ("STARTUP-CELL-VALUE", "the 8-byte value of a start-up cell, stated in YF0m's Tfib_const_abs, which G4 (ifchk: every "
                           "cell at all 50 hand-off states) and G5 (cellcheck / shadowcheck / ownedcheck / covcheck) "
                           "check; a value, not an address; a REG0 `flit8 a v` row restates a YF0m cell (measured)"),
    ("RUNTIME-BLOCK-SIZE", "kNodesBlockSize, the size of the stack depot's node block: measured: the image's pin holds "
                           "`lui rX, 0x100` (0x100000) in TwoLevelMap<StackDepotNode, ...>::Create (twin .symtab)"),
    ("ABORTED-GOAL", "the numeral sits in a `Goal ... Abort.` block over the section variable segs: a check of the "
                     "stepping tactics on an abstract segment map; nothing is proved and no image is read"),
    ("SIZE0-END-NEXT-CELL", "src0_E_<f> of a size-0 symbol <f> (twin .symtab): the regenerator ends the cell at the next "
                            "cell of the table (measured, as in cgif's own table); the checker expects the next "
                            "function's start; no file of the lib reads src0_E_<f> (measured)"),
    ("UNTRIAGED", "no rule took the row"),
])

KEY = slice(3, 12)


def table(path):
    lines = [l for l in open(path).read().split("\n") if l and not l.startswith("#")]
    hdr = lines[0].split("\t")
    rows, occ = collections.OrderedDict(), collections.Counter()
    for l in lines[1:]:
        r = l.split("\t")
        k = tuple(r[KEY])
        occ[k] += 1
        rows[k + (occ[k],)] = r
    return hdr, rows


def ival(s):
    try:
        return int(s, 0)
    except (TypeError, ValueError):
        return None


def lui_sites(img, imm):
    """addresses of `lui rd, imm` words in the image's executable PT_LOAD (the second one)."""
    va, fs, _, _ = img.segs[1]
    return [a for a in range(va, va + fs, 4) if (img.word(a) & 0xFFFFF07F) == ((imm << 12) | 0x37)]


class Fn:
    def __init__(self, twin):
        self.f = sorted((a, s, n) for a, s, n in twin.funcs if s > 0)
        self.k = [a for a, s, n in self.f]

    def at(self, a):
        i = bisect.bisect_right(self.k, a) - 1
        if i >= 0 and self.f[i][0] <= a < self.f[i][0] + self.f[i][1]:
            return self.f[i]
        return None


def jal_target(pc, w):
    if w & 0x7F != 0x6F:
        return None
    imm = (((w >> 31) & 1) << 20) | (((w >> 12) & 0xFF) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3FF) << 1)
    return pc + imm - ((w >> 31) << 21)


class Ctx:
    def __init__(self, a):
        self.lib, self.clib = a.lib, a.cgif_lib
        kv = lambda xs: dict(x.split("=", 1) for x in xs)
        self.pin = {k: Img(v) for k, v in kv(a.pin).items()}
        self.twin = {k: Twin(v) for k, v in kv(a.twin).items()}
        self.fn = {k: Fn(t) for k, t in self.twin.items()}
        self.cpin = {k: Img(v) for k, v in kv(a.cgif_pin).items()}
        self.ctwin = {k: Twin(v) for k, v in kv(a.cgif_twin).items()}
        self.text, self.memo = {}, {}

    def lines(self, root, rel):
        p = os.path.join(root, rel)
        if p not in self.text:
            self.text[p] = open(p).read().split("\n")
        return self.text[p]

    def lui_fns(self, k, imm):
        if (k, imm) not in self.memo:
            out = collections.defaultdict(list)
            for s in lui_sites(self.pin[k], imm):
                f = self.fn[k].at(s)
                if f:
                    out[f[2]].append(s)
            self.memo[(k, imm)] = out
        return self.memo[(k, imm)]

    def readers(self, name):
        """lines of the lib, outside the cell's own definition, that name `name`."""
        if ("readers", name) not in self.memo:
            pat, hits = re.compile(r"\b%s\b" % re.escape(name)), []
            for d, _, fs in os.walk(self.lib):
                for f in fs:
                    if f.endswith(".v"):
                        for i, l in enumerate(open(os.path.join(d, f), errors="replace"), 1):
                            if pat.search(l) and not re.search(r"Definition %s :" % re.escape(name), l):
                                hits.append("%s:%d" % (os.path.relpath(os.path.join(d, f), self.lib), i))
            self.memo[("readers", name)] = hits
        return self.memo[("readers", name)]


def decl_start(L, l):
    """index (1-based) of the declaration line that encloses line l."""
    for i in range(l, 0, -1):
        if re.match(r"(Lemma|Theorem|Example|Definition|Fact|Corollary|Goal)\b", L[i - 1]):
            return i
    return 1


def rule_of(d, old_v, c):
    v, img, f, l = d["verdict"], d["image"], d["dst_file"], ival(d["dst_line"]) or 0
    dv, sv = ival(d["dst_value"]), ival(d["src_value"])
    L = c.lines(c.lib, f)
    line = L[l - 1] if l else ""
    sent = re.sub(r" / sentence \d+$", "", d["sentence"])
    if v == old_v:
        return None
    # ALLOC-MAP-SIZE
    if dv == sv == 262144 and img in c.pin:
        lf = c.lui_fns(img, 0x40)
        pfa = sorted((s, n) for n, ss in lf.items() for s in ss if "SizeClassAllocator64" in n and "PopulateFreeArray" in n)
        efa = sorted((s, n) for n, ss in lf.items() for s in ss if "SizeClassAllocator64" in n and "EnsureFreeArraySpace" in n)
        if pfa and efa:
            meas = ("image %s pin: lui rX,0x40 at %#x (SizeClassAllocator64::PopulateFreeArray) and %#x "
                    "(::EnsureFreeArraySpace), twin .symtab" % (img, pfa[0][0], efa[0][0]))
            scope = "\n".join(L[decl_start(L, l) - 1:l])
            why = None
            m = re.search(r"pin \(runto (0x[0-9a-f]+) \w+\) (\d+)%bv \(SLit 262144\)", line)
            win = "\n".join(L[max(0, l - 5):l + 3])
            st = re.search(r"sr_get \(ss_regs (\w+)\) 11%bv = SLit 262144", line)
            if m:
                fpc = c.fn[img].at(int(m.group(1), 16))
                if fpc and "SizeClassAllocator64" in fpc[2] and re.search("PopulateFreeArray|EnsureFreeArraySpace", fpc[2]):
                    why = ("register x%s pinned to the allocator's map size at pc %s, inside %s+%#x" %
                           (m.group(2), m.group(1), "PopulateFreeArray" if "Populate" in fpc[2] else
                            "EnsureFreeArraySpace", int(m.group(1), 16) - fpc[0]))
            elif st and re.search(r"sr_get \(ss_regs %s\) 17%%bv = SLit 222\b" % st.group(1), win):
                pcs = sorted(set(re.findall(r"ss_pc %s = (0x[0-9a-f]+)" % st.group(1), win)))
                ok = all(c.pin[img].word(int(p, 16)) == 0x73 and "internal_mmap" in (c.fn[img].at(int(p, 16)) or
                                                                                      (0, 0, ""))[2] for p in pcs)
                if ok:
                    why = "the length register a1 of an mmap ecall (a7 = 222) in state %s" % st.group(1) + (
                        "; the pin word at %s is ecall, in internal_mmap" % ", ".join(pcs) if pcs else "")
            elif re.search(r"\b(kUserMapSize|kFreeArrayMapSize)\b", scope):
                n = re.findall(r"\b(kUserMapSize|kFreeArrayMapSize)\b", scope)[-1]
                why = ("the definition of %s" % n if re.match(r"Definition %s :" % n, line) else
                       "%s, unfolded in this proof (%s)" % (n, sent))
            if why:
                return "ALLOC-MAP-SIZE", "%s; %s" % (why, meas)
    # CAPACITY-DOUBLING
    if dv is not None and dv == sv and dv % 2 == 0:
        scope = "\n".join(L[decl_start(L, l) - 1:l])
        if ("replace (2 * %d) with %d by reflexivity" % (dv // 2, dv)) in scope and "dlen data" in scope and \
                re.search(r"\b%d\b" % dv, line):
            return "CAPACITY-DOUBLING", "2 * %d = %d, compared with dlen data (%s, checked in the kernel)" % (dv // 2, dv, sent)
    # FOOTPRINT-LENGTH
    m = re.search(r"\(LMem \(SP (\d+) 0\), %d\)" % (dv or -1), line)
    if m and dv == sv:
        blk = re.search(r"\(SP %s (\d+), (\d+)\)" % m.group(1), "\n".join(L[max(0, l - 4):l]))
        if blk:
            o, n = int(blk.group(1)), int(blk.group(2))
            if (o + n + 4095) // 4096 * 4096 == dv:
                return "FOOTPRINT-LENGTH", ("user block (SP %s %d, %d): %d + %d = %d bytes, rounded up to 4096 = %d (%s, "
                                            "vm_compute)" % (m.group(1), o, n, o, n, o + n, dv, sent))
    # FAKESTACK-OFFSET
    if sent.endswith("Definition FS_FROFF") and dv == sv:
        txt = "\n".join(L)
        fa = "Lemma frame_addr_cid : forall ly pos, frame_addr ly CID pos = ly_F ly + FS_FROFF + pos * FS_B." in txt
        s1 = re.search(r"Lemma s1C1_eq : s1C1 = SAlu ALU_ADD \(SOff aF (\d+)\) .*Qed\.", txt)
        ent = re.search(r"Definition FS_ENTRY : Z := (0x[0-9a-f]+)\.", txt)
        if fa and s1 and int(s1.group(1)) == dv and ent:
            return "FAKESTACK-OFFSET", ("frame_addr_cid (Qed); s1C1_eq (Qed): the image B code from FS_ENTRY %s forms "
                                       "SOff aF %s = base + %#x" % (ent.group(1), s1.group(1), dv))
    # LOOSE-ENTRY-BOUND
    if dv == sv and re.search(r"fst \(fst e\) \+ snd \(fst e\) <= %#x\)" % (dv or 0), line):
        ye2y = "\n".join(c.lines(c.lib, "Reusable/YE2y.v"))
        blk = re.search(r"Definition icpt_rodata : [^\n]*:=\n(.*?)\]\.\n", ye2y, re.S)
        ent = [(int(a, 16), int(n)) for a, n in re.findall(r"\((0x[0-9a-f]+), (\d+), \[", blk.group(1))] if blk else []
        if ent and max(a + n for a, n in ent) <= dv:
            hi = max(ent, key=lambda e: e[0] + e[1])
            return "LOOSE-ENTRY-BOUND", ("icpt_rodata (YE2y.v): %d entries, the highest [%#x, %#x) ends below %#x; %s" %
                                         (len(ent), hi[0], hi[0] + hi[1], dv, sent))
    # JAL-SAME-CALLEE
    m = re.match(r"Lemma DS_(\w+) : decode_any \((0x[0-9a-f]+)%bv : bv 32\) = Some \(Jal 1 \d+, 4%Z\)\.", line)
    if v == "INSN-CHANGED" and m and img in c.pin and img in c.cpin:
        n, w = m.group(1), int(m.group(2), 16)

        def callee(root, rel, pin, twin, word):
            fs = re.compile(r"Lemma FS_%s : fetch_word src0segs \(Z_to_bv 64 \(src0_A_(\w+) \+ (0x[0-9a-f]+)\)\) = Some "
                            r"\((0x[0-9a-f]+)%%bv : bv 32\)\." % n)
            for ln in c.lines(root, rel):
                q = fs.match(ln)
                if q and int(q.group(3), 16) == word:
                    st = twin.start(q.group(1))
                    if st is None:
                        return None
                    pc = st + int(q.group(2), 16)
                    t = jal_target(pc, pin.word(pc)) if pin.word(pc) == word else None
                    tn = [nm for a, s, nm in twin.funcs if a == t and s > 0]
                    return (q.group(1), q.group(2), pc, t, tn[0] if tn else None)
            return None
        dn = callee(c.lib, f, c.pin[img], c.twin[img], w)
        cn = callee(c.clib, d["src_file"], c.cpin[img], c.ctwin[img], sv)
        if dn and cn and dn[4] and dn[4] == cn[4]:
            return "JAL-SAME-CALLEE", ("pin %s word at %s+%s = %#x is %#x: jal ra -> %#x = %s; cgif's at %#x is %#x: jal "
                                       "ra -> %#x = %s" % (img, dn[0], dn[1], dn[2], w, dn[3], dn[4], cn[2], sv, cn[3], cn[4]))
    # STARTUP-CELL-VALUE
    if dv == sv and dv is not None:
        yf0m = "\n".join(c.lines(c.lib, "Reusable/YF0m.v"))
        abs_blk = re.search(r"Definition Tfib_const_abs : list acell :=(.*?)\]\.", yf0m, re.S)
        cells = re.findall(r"z8 \(ANum (0x[0-9a-f]+)\) (0x[0-9a-f]+)", abs_blk.group(1)) if abs_blk else []
        if f == "Reusable/YF0m.v" and sent.endswith("Tfib_const_abs"):
            hit = [a for a, x in cells if int(x, 16) == dv and "z8 (ANum %s) %s" % (a, x) in line]
        else:
            hit = [a for a, x in re.findall(r"flit8 (0x[0-9a-f]+) (0x[0-9a-f]+)", line)
                   if int(x, 16) == dv and (a, x) in cells]
        if hit:
            a = int(hit[0], 16)
            obj = [(s, n) for s, sz, n, t in c.twin["B"].syms if s <= a < s + sz and n and not n.startswith("$")]
            return "STARTUP-CELL-VALUE", ("YF0m's Tfib_const_abs cell z8 (ANum %s) %s%s" % (
                hit[0], d["dst_value"], ", inside %s + %#x (image B twin)" % (obj[0][1], a - obj[0][0]) if obj else ""))
    # RUNTIME-BLOCK-SIZE
    if sent.endswith("Definition kNodesBlockSize") and dv == sv == 0x100000 and img in c.pin:
        hits = sorted((s, n) for n, ss in c.lui_fns(img, 0x100).items() for s in ss
                      if "TwoLevelMap" in n and "StackDepotNode" in n and "Create" in n)
        if hits:
            tl = re.search(r"TwoLevelMapINS_14StackDepotNodeELy(\d+)ELy(\d+)E", hits[0][1])
            return "RUNTIME-BLOCK-SIZE", ("image %s pin: lui rX,0x100 at %#x in TwoLevelMap<StackDepotNode, %s, %s>::Create "
                                          "(twin .symtab)" % (img, hits[0][0], tl.group(1) if tl else "?",
                                                              tl.group(2) if tl else "?"))
    # ABORTED-GOAL
    if l:
        g = next((i for i in range(l, 0, -1) if re.match(r"(Goal|Lemma|Theorem|Example|Definition)\b", L[i - 1])), None)
        e = next((i for i in range(l, len(L) + 1) if re.match(r"(Abort|Qed|Defined|Admitted)\.", L[i - 1].strip())), None)
        if g and e and L[g - 1].startswith("Goal ") and L[e - 1].strip() == "Abort." and \
                re.search(r"\bsegs\b", "\n".join(L[g - 1:e])):
            return "ABORTED-GOAL", "Goal at line %d, Abort. at line %d, over segs" % (g, e)
    # SIZE0-END-NEXT-CELL
    m = re.search(r"Definition src0_E_(\w+) : Z := (0x[0-9a-f]+)\.", line)
    if m and f.endswith("YH03.v") and int(m.group(2), 16) == dv and img in c.twin and img in c.ctwin:
        name = m.group(1)

        def size0(lines, twin):
            txt = "\n".join(lines)
            A = {n: int(x, 16) for n, x in re.findall(r"Definition src0_A_(\w+) : Z := (0x[0-9a-f]+)\.", txt)}
            E = {n: int(x, 16) for n, x in re.findall(r"Definition src0_E_(\w+) : Z := (0x[0-9a-f]+)\.", txt)}
            if name not in A or name not in E:
                return None
            fs = [s for a, s, n in twin.funcs if a == A[name]]
            starts = sorted(A.values())
            i = bisect.bisect_right(starts, A[name])
            nxt = starts[i] if i < len(starts) else None
            if fs and all(s == 0 for s in fs) and E[name] == nxt:
                return A[name], E[name], twin.next_start(A[name])
            return None
        dz = size0(L, c.twin[img])
        cz = size0(c.lines(c.clib, d["src_file"]), c.ctwin[img])
        rd = c.readers("src0_E_" + name)
        if dz and cz and not rd:
            return "SIZE0-END-NEXT-CELL", ("%s size 0 at %#x (twin): E = next cell %#x, next function %#x; cgif: size 0 at "
                                           "%#x, E = next cell %#x, next function %#x; readers of src0_E_%s: none" %
                                           (name, dz[0], dz[1], dz[2], cz[0], cz[1], cz[2], name))
    return None


def note_change(a, b):
    p = 0
    while p < min(len(a), len(b)) and a[p] == b[p]:
        p += 1
    s = 0
    while s < min(len(a), len(b)) - p and a[len(a) - 1 - s] == b[len(b) - 1 - s]:
        s += 1
    cut = lambda x: x if len(x) <= 90 else x[:90] + ".."
    return "note: removed %r, added %r" % (cut(a[p:len(a) - s]), cut(b[p:len(b) - s]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", action="append", required=True)
    for k in ("pac", "lib", "cgif-lib", "out"):
        ap.add_argument("--" + k, required=True)
    for k in ("pin", "twin", "cgif-pin", "cgif-twin"):
        ap.add_argument("--" + k, action="append", required=True)
    a = ap.parse_args()
    flags = set(subprocess.run([sys.executable, a.pac, "--list-flag-classes"], capture_output=True, text=True,
                               check=True).stdout.split())
    grp = lambda v: "FLAG" if v in flags else ("UNMEASURED" if v.startswith("UNMEASURED") or v.endswith("UNMEASURED")
                                               else "OK")
    c = Ctx(a)
    out, bad = [], 0
    for spec in a.run:
        name, old, new, g1 = spec.split(":")
        ho, O = table(old)
        hn, N = table(new)
        if ho != hn or set(O) != set(N):
            sys.exit("g10_triage: %s: the two tables do not hold the same rows (header or keys differ)" % name)
        H = {h: i for i, h in enumerate(hn)}
        cnt, moves, covered = collections.Counter(), collections.Counter(), set()
        ndiff = 0
        for k in O:
            o, n = O[k], N[k]
            if o == n:
                continue
            ndiff += 1
            d = dict(zip(hn, n))
            ov = o[H["verdict"]]
            if ov == d["verdict"]:
                rule, det = "NOTE-ONLY", note_change(o[H["note"]], d["note"])
            else:
                moves[(grp(ov), grp(d["verdict"]))] += 1
                rd = rule_of(d, ov, c)
                rule, det = rd if rd else ("UNTRIAGED", "")
                if rule == "UNTRIAGED":
                    bad += 1
                sent = re.sub(r" / sentence \d+$", "", d["sentence"])
                covered.add(("%s:%s" % (d["dst_file"], d["dst_line"]), sent[:60], d["idx"], d["src_value"],
                             d["dst_value"]))
            cnt[rule] += 1
            out.append("\t".join([name, ov, d["verdict"], d["image"], "%s:%s" % (d["dst_file"], d["dst_line"]),
                                  re.sub(r" / sentence \d+$", "", d["sentence"])[:60], d["idx"], d["src_value"],
                                  d["dst_value"], rule, det.replace("\t", " ")]))
        g1u = [r.split("\t") for r in open(g1).read().split("\n")[1:] if r]
        g1u = [(r[3], r[4], r[5], r[6], r[7]) for r in g1u if r[8] == "UNTRIAGED"]
        miss = [u for u in g1u if u not in covered]
        bad += len(miss)
        print("# %s: %d rows each; %d differ; verdict moves %d (%s); g1_triage UNTRIAGED %d, all triaged here: %s" %
              (name, len(N), ndiff, sum(moves.values()),
               ", ".join("%s->%s %d" % (x, y, m) for (x, y), m in sorted(moves.items())), len(g1u),
               "yes" if not miss else "NO (%d missing)" % len(miss)), file=sys.stderr)
        for r in RULES:
            if cnt[r]:
                print("  %-20s %4d" % (r, cnt[r]), file=sys.stderr)
        for u in miss[:20]:
            print("  NOT TRIAGED HERE\t" + "\t".join(u), file=sys.stderr)
    with open(a.out, "w") as fo:
        fo.write("\t".join(["run", "old_verdict", "new_verdict", "image", "where", "sentence", "idx", "src_value",
                            "dst_value", "rule", "detail"]) + "\n")
        fo.write("\n".join(out) + "\n")
    for r in out:
        if "\tUNTRIAGED\t" in r:
            print("UNTRIAGED\t" + r, file=sys.stderr)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
