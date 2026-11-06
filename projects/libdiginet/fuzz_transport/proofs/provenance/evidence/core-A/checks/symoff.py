#!/usr/bin/env python3
"""symoff.py WORK LIB OUT [--tsv STAGE2.TSV] [--tag NAME]: the symbol + offset sweep of the libdiginet/fuzz_transport
image-A core relocation (row TCA; the rule of the registry's 'KNOWN LIMIT, ALL RELOCATION TOOLS' entry, the tool
registry's README.md (sha256 05596ed48d98; internal record), 19:51Z): for every relocated numeral that names a data object, the donor value's symbol
+ offset on the donor image and the written value's symbol + offset on the pin are resolved and compared; a value that
lands in .got / .got.plt, or on a symbol other than the donor's twin, is a finding. Read-only.

Input rows: decval_extra.py's stage-2 TSV (every numeral of WORK/stage-out in [0x10000, page-up top], aligned with its
donor token in WORK/stage). Default OUT/decval/A-stage2.tsv (decval-A.sh WORK LIB OUT/decval writes it); --tsv overrides.
A row is in the sweep when its donor value or its written value lies in a DATA area of its image (.rodata, .tbss,
.init_array, .fini_array, .preinit_array, .data.rel.ro, .got, .got.plt, .relro_padding, .data, asan_globals, .bss, or one
past the end of one) and it is not an instruction word / decoded field, a comment numeral (port_core edits no comment), a
constant by role (stage 2's categories) or a derived quantity (x/8 ... of an object; item 4 checks those).

Decision per row (the first that applies):
  GOT-CELL   donor value and written value both in .got: 8-byte aligned, at the same offset from .got's start, and the
             two words hold the same symbol + offset (or the same value below 0x10000)
  GOT        written value in .got / .got.plt otherwise                                            -> FINDING
  GEOMETRY   the donor value is an image quantity of the donor (img_top_up, img_span, rw_lo, rw_len, a PT_LOAD's lo /
             hi / page bounds / page size, a section's lo / hi / size) and the written value is the SAME quantity of
             the target
  SYMBOL     both resolve to a sized symbol (the smallest that holds the address), the same name (any alias at that
             start), the same offset; or both are the same symbol's start / end
  BOUND      both are the same section / PT_LOAD boundary
  BYTES      no symbol holds the address in either image (unnamed .rodata data): the NUL-terminated string holding it
             is the same and at the same offset, or the 16 bytes around it are equal, or the 8 bytes at it (a constant
             pool entry) or before it (its end) are equal; and that content is found ONCE in the target .rodata, or the
             nearest preceding symbol + offset is the same in both images
  OTHER-SYM  anything else: a different symbol, offset or content                                   -> FINDING
Output: OUT/symoff[-TAG].tsv (every swept row and its decision), OUT/symoff[-TAG].txt (counts, every finding).
"""
import bisect
import collections
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import decval as DV  # noqa: E402
from elftools.elf.elffile import ELFFile  # noqa: E402

DATA = {".rodata", ".tbss", ".init_array", ".fini_array", ".preinit_array", ".data.rel.ro", ".got", ".got.plt",
        ".relro_padding", ".data", "asan_globals", ".bss"}
CONST = ("constant / size", "Linux mmap flag", "instruction-word literal", "instruction word or field", "model label",
         "inside a multi-line comment", "no address role")
# rows the owner already handles (the lane brief: not reported again); matched by file and definition name
KNOWN = {("A/AB1w.v", "tfib_rodata_hi"): "KNOWN to the owner: the final run writes 0x22b4c (.rodata's end; an override row "
                                         "added after work2); port_core's rule bound-released-elsewhere kept the donor's -0x40"}


class Res:
    def __init__(self, symp, bytp):
        e = ELFFile(open(symp, "rb"))
        self.secs = [(x.name, x["sh_addr"], x["sh_size"]) for x in e.iter_sections() if x["sh_addr"] and x["sh_flags"] & 2]
        self.objs, self.at = [], collections.defaultdict(set)
        for sym in e.get_section_by_name(".symtab").iter_symbols():
            n, t, sh = sym.name, sym["st_info"]["type"], sym["st_shndx"]
            if not n or n.startswith("$") or not isinstance(sh, int) or t in ("STT_TLS", "STT_SECTION", "STT_FILE"):
                continue
            a, z = sym["st_value"], sym["st_size"]
            self.at[a].add(n)
            if z:
                self.objs.append((a, a + z, n))
        self.objs.sort()
        self.starts = [o[0] for o in self.objs]
        self.ends = collections.defaultdict(set)
        for a, b, n in self.objs:
            self.ends[b].add(n)
        eb = ELFFile(open(bytp, "rb"))
        self.loads = sorted((sg["p_vaddr"], sg["p_memsz"], sg.data()) for sg in eb.iter_segments() if sg["p_type"] == "PT_LOAD")
        self.top = max(v + m for v, m, d in self.loads)
        self.top_up = (self.top + 0xFFF) & ~0xFFF
        self.rw_lo = self.loads[-2][0] + self.loads[-2][1]
        self.rw_lo = (self.rw_lo + 0xFFF) & ~0xFFF if False else self.rw_lo
        self.geo = collections.defaultdict(set)   # value -> quantity names
        g = self.geo
        g[self.top_up].add("img_top_up")
        g[self.top_up - 0x10000].add("img_span")
        rlo = [x for x in self.secs if x[0] == ".relro_padding"]
        if rlo:
            g[rlo[0][1] + rlo[0][2]].add("rw_lo")
            g[self.top_up - (rlo[0][1] + rlo[0][2])].add("rw_len")
        for i, (v, m, d) in enumerate(self.loads):
            lp, hp = v & ~0xFFF, (v + m + 0xFFF) & ~0xFFF
            for x, w in ((v, "lo"), (v + m, "hi"), (lp, "lo_page"), (hp, "hi_page"), (hp - lp, "pagesize"), (m, "memsz")):
                g[x].add("load%d.%s" % (i, w))
        for n, a, z in self.secs:
            g[a].add("sec:%s.lo" % n)
            g[a + z].add("sec:%s.hi" % n)
            g[z].add("sec:%s.size" % n)
        self.ro = [(a, z) for n, a, z in self.secs if n == ".rodata"][0]
        self.rob = self.rd(self.ro[0], self.ro[1])
        self.refs = coderefs(symp, bytp)
        self.refkeys = sorted(self.refs)
        self.refs_at = collections.defaultdict(set)
        for x, sites in self.refs.items():
            for s in sites:
                self.refs_at[s].add(x)

    def sec(self, a):
        for n, lo, z in self.secs:
            if lo <= a < lo + z:
                return n
        return None

    def isdata(self, a):
        if self.sec(a) in DATA:
            return True
        return any(a == lo + z and n in DATA for n, lo, z in self.secs)

    def rd(self, a, n):
        for v, m, d in self.loads:
            if v <= a < v + m:
                b = d[a - v: a - v + n]
                return b + b"\0" * (n - len(b))
        return None

    def q(self, a):
        b = self.rd(a, 8)
        return None if b is None else int.from_bytes(b, "little")

    def resolve(self, a):
        """('in', names, off) for the smallest sized symbol holding a; ('at', names, 0) a size-0 label; ('end', names, 0)
        one past a sized symbol; ('none', (), 0)."""
        i = bisect.bisect_right(self.starts, a)
        c = [o for o in self.objs[max(0, i - 4000):i] if o[0] <= a < o[1]]
        if c:
            m = min(hi - lo for lo, hi, n in c)
            lo = [x for x in c if x[1] - x[0] == m][0][0]
            return ("in", frozenset({n for l, h, n in c if l == lo and h - l == m} | (self.at[a] if a == lo else set())), a - lo)
        if self.at.get(a):
            return ("at", frozenset(self.at[a]), 0)
        if self.ends.get(a):
            return ("end", frozenset(self.ends[a]), 0)
        return ("none", frozenset(), 0)

    def anchor(self, a):
        """nearest symbol start at or below a (any symbol), and the offset."""
        ks = sorted(k for k in self.at if k <= a)
        if not ks:
            return None
        k = ks[-1]
        return (frozenset(self.at[k]), a - k)

    def forms(self, a):
        """every (name, offset) form of a: the smallest sized symbol holding it, each label at it (offset 0), each sized
        symbol ending at it (name.end); two values name the same object when their form sets intersect."""
        out = set()
        k, names, off = self.resolve(a)
        if k == "in":
            out |= {(n, off) for n in names}
        out |= {(n, 0) for n in self.at.get(a, ())}
        out |= {(n + ".end", 0) for n in self.ends.get(a, ())}
        return out

    def string_at(self, a):
        lo, z = self.ro
        if not lo <= a < lo + z:
            return None
        i = a - lo
        s = i
        while s > 0 and self.rob[s - 1] != 0:
            s -= 1
        e = self.rob.find(b"\0", i)
        return (self.rob[s:e + 1], i - s) if e > s else None


def lab(r):
    k, names, off = r
    if k == "none":
        return "-"
    n = sorted(names, key=lambda x: (x.startswith("_"), len(x), x))[0]
    return {"in": "%s+%#x" % (n, off), "at": n, "end": "%s.end" % n}[k]


def same_obj(DR, dw, TR, tw):
    """True when the donor word dw and the target word tw name the same object: both below 0x10000 and equal, their
    (name, offset) form sets intersect, or neither names any symbol and the two values are equal (e.g. -0x800)."""
    if dw < 0x10000 or tw < 0x10000:
        return dw == tw
    fd, ft = DR.forms(dw), TR.forms(tw)
    return bool(fd & ft) or (not fd and not ft and dw == tw)


def decide(DR, TR, d, v):
    """(decision, donor form, target form, evidence)"""
    tgot, dgot = TR.sec(v) in (".got", ".got.plt"), DR.sec(d) in (".got", ".got.plt")
    if tgot or dgot:
        if tgot and dgot:
            tl, dl = [(a, z) for n, a, z in TR.secs if n == TR.sec(v)][0], [(a, z) for n, a, z in DR.secs if n == DR.sec(d)][0]
            cd, ct = DR.q(d - d % 8), TR.q(v - v % 8)
            nd = lab(DR.resolve(cd)) if cd >= 0x10000 else "value %#x" % cd
            nt = lab(TR.resolve(ct)) if ct >= 0x10000 else "value %#x" % ct
            if d % 8 == 0 and v % 8 == 0 and d - dl[0] == v - tl[0] and same_obj(DR, cd, TR, ct):
                return ("GOT-CELL", "%s .got+%#x holds %s" % (DR.sec(d), d - dl[0], nd),
                        "%s .got+%#x holds %s" % (TR.sec(v), v - tl[0], nt), "same cell, same content")
            return ("GOT", "%s %#x holds %s" % (DR.sec(d), d, nd), "%s %#x holds %s" % (TR.sec(v), v, nt), "a .got cell that does not twin")
        return ("GOT", lab(DR.resolve(d)), "%s %#x" % (TR.sec(v) or DR.sec(d), v), "the written value lands in .got" if tgot else "the donor value is a .got cell, the written value is not")
    gq = DR.geo.get(d, set()) & TR.geo.get(v, set())
    if gq:
        return ("GEOMETRY", sorted(gq)[0], sorted(gq)[0], "the same image quantity")
    rd_, rt = DR.resolve(d), TR.resolve(v)
    fs = DR.forms(d) & TR.forms(v)
    if fs:
        n, o = sorted(fs, key=lambda x: (x[0].startswith("_"), len(x[0]), x))[0]
        return ("SYMBOL", lab(rd_), lab(rt), "same symbol + offset (%s+%#x)" % (n, o))
    if rd_[0] == "none" and rt[0] == "none":
        ev = None
        sd, st = DR.string_at(d), TR.string_at(v)
        cands = []
        if sd and st and sd == st and len(sd[0]) > 2:
            cands.append(("the string %r at offset %d" % (sd[0][:40], sd[1]), sd[0]))
        bd, bt = DR.rd(d - 8, 16), TR.rd(v - 8, 16)
        if bd and bd == bt and any(bd):
            cands.append(("the 16 bytes around it", bt))
        for w, o in (("the 8 bytes at it", 0), ("the 8 bytes before it (an end)", -8)):
            bd, bt = DR.rd(d + o, 8), TR.rd(v + o, 8)
            if bd and bd == bt and any(bd):
                cands.append((w, bt))
        ad, at = DR.anchor(d), TR.anchor(v)
        same_anchor = ad and at and ad[0] & at[0] and ad[1] == at[1]
        for w, b in cands:
            n = TR.rob.count(b)
            if n == 1 or same_anchor:
                ev = "%s equal%s%s" % (w, "; found once in the target .rodata" if n == 1 else "; found %d times" % n,
                                      "; nearest symbol + offset %s+%#x in both" % (sorted(at[0])[0], at[1]) if same_anchor else "")
                break
        if ev:
            return ("BYTES", "unnamed %s %#x" % (DR.sec(d), d), "unnamed %s %#x" % (TR.sec(v), v), ev)
        # the base the code forms: the nearest address at or below d that an auipc / lui + lo12 pair of a donor
        # function forms; the target's same function forms its base at the same offset, and v sits as far above it
        cr = coderef_match(DR, TR, d, v)
        if cr:
            return ("CODEREF", "unnamed %s %#x" % (DR.sec(d), d), "unnamed %s %#x" % (TR.sec(v), v), cr)
        return ("OTHER-SYM", "unnamed %s %#x" % (DR.sec(d), d), "unnamed %s %#x" % (TR.sec(v), v),
                "no symbol, and no content / anchor / code-reference match" + (" (candidates %s)" % [w for w, b in cands] if cands else ""))
    return ("OTHER-SYM", lab(rd_), lab(rt), "a different symbol or offset")


def coderef_match(DR, TR, d, v):
    """evidence string when the nearest code-formed base b <= d (d - b < 0x1000) of the donor is formed at a site
    (function, offset) whose target twin forms b' with v - b' == d - b; else None."""
    i = bisect.bisect_right(DR.refkeys, d) - 1
    if i < 0 or d - DR.refkeys[i] >= 0x1000:
        return None
    b = DR.refkeys[i]
    for fn, off in sorted(DR.refs[b]):
        for b2 in TR.refs_at.get((fn, off), ()):
            if v - b2 == d - b:
                return "%s+%#x forms %#x in the donor and %#x in the target; the value is base + %#x in both" % (fn, off, b, b2, d - b)
    return None


def _sext(x, b):
    return x - (1 << b) if x & (1 << (b - 1)) else x


def coderefs(symp, bytp):
    """address -> {(function, offset of the lo12 instruction)}: every address an auipc (pc + imm) or lui (imm) followed by
    addi / load / store with that register as base forms, per sized FUNC symbol, decoding the .text linearly (2- and
    4-byte parcels; a compressed instruction that writes a tracked register drops it)."""
    e = ELFFile(open(symp, "rb"))
    funcs = sorted({(s["st_value"], s["st_size"], s.name) for s in e.get_section_by_name(".symtab").iter_symbols()
                    if s["st_info"]["type"] == "STT_FUNC" and s["st_size"] and s.name})
    tx = ELFFile(open(bytp, "rb")).get_section_by_name(".text")
    base, data = tx["sh_addr"], tx.data()
    refs, done = collections.defaultdict(set), set()
    for a, z, n in funcs:
        if (a, z) in done or not base <= a < base + len(data):
            continue
        done.add((a, z))
        k, end, hi = a - base, min(a - base + z, len(data)), {}
        while k < end:
            h = int.from_bytes(data[k:k + 2], "little")
            if h & 3 != 3:
                q, f3 = h & 3, h >> 13
                if (q == 1 and f3 in (0, 1, 2, 3)) or (q == 2 and f3 in (0, 2, 4)):
                    hi.pop((h >> 7) & 31, None)
                elif q == 1 and f3 == 4:
                    hi.pop(8 + ((h >> 7) & 7), None)
                k += 2
                continue
            w = int.from_bytes(data[k:k + 4], "little")
            op, rd, rs1, f3 = w & 0x7F, (w >> 7) & 31, (w >> 15) & 31, (w >> 12) & 7
            if op in (0x17, 0x37):
                imm = _sext(w & 0xFFFFF000, 32)
                hi[rd] = (base + k + imm) if op == 0x17 else imm
            else:
                lo = None
                if (op == 0x13 and f3 == 0) or op in (0x03, 0x07):
                    lo = _sext(w >> 20, 12)
                elif op in (0x23, 0x27):
                    lo = _sext(((w >> 25) << 5) | ((w >> 7) & 31), 12)
                if lo is not None and rs1 and rs1 in hi:
                    refs[(hi[rs1] + lo) & 0xFFFFFFFFFFFFFFFF].add((n, base + k - a))
                if op not in (0x23, 0x27, 0x63):
                    hi.pop(rd, None)
            k += 4
    return refs


def main():
    a = sys.argv[1:]
    if len(a) < 3:
        sys.exit("usage: symoff.py WORK LIB OUT [--tsv STAGE2.TSV] [--tag NAME]")
    work, lib, out = a[:3]
    tsv = a[a.index("--tsv") + 1] if "--tsv" in a else os.path.join(out, "decval", "A-stage2.tsv")
    tag = ("-" + a[a.index("--tag") + 1]) if "--tag" in a else ""
    cfg = DV.setup([work])
    TR, DR = Res(cfg["tgt_syms"], cfg["tgt_bytes"]), Res(cfg["don_syms"], cfg["don_bytes"])
    rows = [l.rstrip("\n").split("\t") for l in open(tsv)][1:]
    stat, res, find = collections.Counter(), [], []
    for r in rows:
        f, ln, tok, v = r[0], r[1], r[2], int(r[3])
        role, ev = DV.role(r[9]), r[8]
        if r[6] == "":
            if TR.isdata(v):
                stat["UNALIGNED (no donor token), written value in a data area"] += 1
                res.append(("UNALIGNED", f, ln, "-", tok, "-", lab(TR.resolve(v)), "no aligned donor token"))
                find.append(res[-1])
            else:
                stat["skip: unaligned, not a data address"] += 1
            continue
        d = DV.val(r[6])
        if not (DR.isdata(d) or TR.isdata(v)):
            stat["skip: neither value in a data area"] += 1
            continue
        if role in ("fetch", "word", "decode"):
            stat["skip: instruction word / decoded field"] += 1
            continue
        if ev.startswith("comment") or ev.startswith("inside a multi-line comment"):
            stat["skip: comment numeral (port_core edits no comment)"] += 1
            continue
        if ev.startswith(CONST):
            stat["skip: constant by role (stage 2)"] += 1
            continue
        if ev.startswith("moved: derived"):
            stat["skip: derived quantity (x/8 ... ; item 4)"] += 1
            continue
        dec, fd, ft, why = decide(DR, TR, d, v)
        kn = [why_k for (kf, kdef), why_k in KNOWN.items() if kf == f and re.search(r"\b%s\s*:\s*Z\s*:=\s*%s\b" % (kdef, re.escape(tok)), r[9])]
        if dec in ("GOT", "OTHER-SYM") and kn:
            dec, why = "KNOWN", why + "; " + kn[0]
        stat[dec] += 1
        res.append((dec, f, ln, r[6], tok, fd, ft, why))
        if dec in ("GOT", "OTHER-SYM", "KNOWN"):
            find.append(res[-1])
    with open(os.path.join(out, "symoff%s.tsv" % tag), "w") as fo:
        fo.write("decision\tfile\tline\tdonor\twritten\tdonor_symoff\ttarget_symoff\tevidence\n")
        for x in res:
            fo.write("\t".join(map(str, x)) + "\n")
    sw = sum(c for k, c in stat.items() if not k.startswith("skip"))
    lines = ["# symoff.py %s: rows %d (stage-2 TSV %s); swept %d" % (tag or "(run)", len(rows), tsv, sw)]
    for k, c in sorted(stat.items(), key=lambda x: (x[0].startswith("skip"), -x[1])):
        lines.append("  %-62s %d" % (k, c))
    by = collections.Counter((x[0], x[5] if x[0] == "GEOMETRY" else "") for x in res if x[0] in ("GEOMETRY",))
    lines.append("  GEOMETRY quantities: " + ", ".join("%s x%d" % (k[1], c) for k, c in sorted(by.items())))
    for x in find:
        lines.append("FINDING\t%s\t%s:%s\t%s -> %s\tdonor %s\ttarget %s\t%s" % (x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]))
    nk = sum(1 for x in find if x[0] == "KNOWN")
    lines.append("result: rows that land in .got / .got.plt or on a symbol other than the donor's twin: %d (%d of them known to "
                 "the owner and handled, %d new)" % (len(find), nk, len(find) - nk))
    open(os.path.join(out, "symoff%s.txt" % tag), "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
