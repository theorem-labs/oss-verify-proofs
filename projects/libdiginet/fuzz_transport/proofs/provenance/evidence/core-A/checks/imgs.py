#!/usr/bin/env python3
"""imgs.py: the two images of the TCA hypothesis-value audit and the address derivation (donor symbol + offset ->
target symbol + offset). proves no function (kind: measurement). Imported by hypderive.py; reads only.

Img(bytes_path, twin_path): PT_LOAD bytes from the stripped image, sections and .symtab from the unstripped twin.
derive_addr(D, T, d, w) -> (verdict, how): the value the target must hold for the donor value d, and whether the written
value w is it. Rules, first that applies:
  BOUND     d is a donor section start / end, PT_LOAD start / end / page bound, or the page-up image top, and w is the
            same quantity of the target
  GOT       d in donor .got: the 8-byte word at d names symbol + offset (or a value below 0x10000); the expected cell is
            the target .got cell at the same offset from .got whose word names the same symbol + offset
  SYMBOL    the smallest sized symbol holding d (any alias at that start), or a size-0 label at d, or one past a sized
            symbol; the target symbol of the same name (unique among sized symbols of the same section; local duplicates
            are told apart by size) + the same offset. For code (.text) the instruction at the target address must have
            the donor instruction's normalised form (opcode, rd, funct3, rs1, rs2; immediates dropped; compressed
            instructions by quadrant + funct3); if the function's code changed above the offset, the address is mapped
            through an alignment of the two functions' normalised instruction sequences (SYMBOL-ALIGNED)
  BYTES     no symbol holds d (unnamed .rodata): the NUL-terminated string holding d, at the same offset, found once in the
            target .rodata; or the 16 bytes from d found once there
IMAGE-QTY (checked first) d is a donor image quantity (section / PT_LOAD bound or size, page-up top, span) or it / 8 or
            / 4096, and w is the same quantity of the target divided the same way
A shadow address (0x7fff8000 <= v < 0x10007fff8000) is mapped as shadow(derive(unshadow(v))) with unshadow(v) =
(v - 0x7fff8000) * 8, the asan x86/riscv64 mapping (shadow = a / 8 + 0x7fff8000, kLowShadowBeg 0x7fff8000).
"""
import bisect
import collections
import difflib
import hashlib

from elftools.elf.elffile import ELFFile

SHADOW_OFF = 0x7FFF8000


def sha12(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()[:12]


class Img:
    def __init__(self, bytp, symp, label):
        self.label = label
        e = ELFFile(open(symp, "rb"))
        self.secs = [(s.name, s["sh_addr"], s["sh_size"]) for s in e.iter_sections() if s["sh_addr"] and s["sh_flags"] & 2]
        self.secd = {n: (a, z) for n, a, z in self.secs}
        self.objs = []
        self.byname = collections.defaultdict(list)
        self.at = collections.defaultdict(set)
        for sym in e.get_section_by_name(".symtab").iter_symbols():
            n, t, sh = sym.name, sym["st_info"]["type"], sym["st_shndx"]
            if not n or n.startswith("$") or not isinstance(sh, int) or t in ("STT_TLS", "STT_SECTION", "STT_FILE"):
                continue
            a, z = sym["st_value"], sym["st_size"]
            self.at[a].add(n)
            self.byname[n].append((a, z))
            if z:
                self.objs.append((a, a + z, n))
        self.objs.sort()
        self.starts = [o[0] for o in self.objs]
        self.ends = collections.defaultdict(set)
        for a, b, n in self.objs:
            self.ends[b].add(n)
        self.atkeys = sorted(self.at)
        eb = ELFFile(open(bytp, "rb"))
        self.loads = sorted((sg["p_vaddr"], sg["p_memsz"], sg.data()) for sg in eb.iter_segments() if sg["p_type"] == "PT_LOAD")
        self.top = max(v + m for v, m, d in self.loads)
        self.top_up = (self.top + 0xFFF) & ~0xFFF
        self.geo = collections.defaultdict(set)
        g = self.geo
        g[self.top_up].add("img_top_up")
        for i, (v, m, d) in enumerate(self.loads):
            lp, hp = v & ~0xFFF, (v + m + 0xFFF) & ~0xFFF
            for x, w in ((v, "lo"), (v + m, "hi"), (lp, "lo_page"), (hp, "hi_page")):
                g[x].add("load%d.%s" % (i, w))
        for n, a, z in self.secs:
            g[a].add("sec:%s.lo" % n)
            g[a + z].add("sec:%s.hi" % n)
        self.sizes = collections.defaultdict(set)
        for i, (v, m, d) in enumerate(self.loads):
            lp, hp = v & ~0xFFF, (v + m + 0xFFF) & ~0xFFF
            self.sizes[hp - lp].add("load%d.pagesize" % i)
            self.sizes[m].add("load%d.memsz" % i)
        for n, a, z in self.secs:
            self.sizes[z].add("sec:%s.size" % n)
        self.sizes[self.top_up - 0x10000].add("img_span")
        self.quant = {}                     # quantity name -> value (bounds and sizes)
        for v, ns in list(self.geo.items()) + list(self.sizes.items()):
            for n in ns:
                self.quant[n] = v
        self.ro = self.secd[".rodata"]
        self.rob = self.rd(self.ro[0], self.ro[1])

    def sec(self, a):
        for n, lo, z in self.secs:
            if lo <= a < lo + z:
                return n
        return None

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
        i = bisect.bisect_right(self.starts, a)
        c = [o for o in self.objs[max(0, i - 4000):i] if o[0] <= a < o[1]]
        if c:
            m = min(hi - lo for lo, hi, n in c)
            lo, hi = [(x[0], x[1]) for x in c if x[1] - x[0] == m][0]
            names = frozenset({n for l, h, n in c if l == lo and h == hi})
            return ("in", names, a - lo, lo, hi - lo)
        if self.at.get(a):
            return ("at", frozenset(self.at[a]), 0, a, 0)
        if self.ends.get(a):
            return ("end", frozenset(self.ends[a]), 0, a, 0)
        return ("none", frozenset(), 0, None, 0)

    def anchor(self, a):
        k = bisect.bisect_right(self.atkeys, a) - 1
        if k < 0:
            return None
        s = self.atkeys[k]
        return (frozenset(self.at[s]), a - s, s)

    def name_of(self, v):
        """symbol + offset naming value v (for .got words)."""
        if v < 0x10000:
            return ("lit", v)
        r = self.resolve(v)
        if r[0] == "none":
            an = self.anchor(v)
            return ("anchor", tuple(sorted(an[0])), an[1]) if an else ("raw", v)
        return (r[0], tuple(sorted(r[1])), r[2])

    def insns(self, lo, hi):
        """[(addr, length, word)] decoded as RISC-V (2-byte compressed when the low bits are not 11)."""
        out, a = [], lo
        b = self.rd(lo, hi - lo)
        while a < hi:
            h = int.from_bytes(b[a - lo:a - lo + 2], "little")
            if h & 3 == 3:
                w = int.from_bytes(b[a - lo:a - lo + 4], "little")
                out.append((a, 4, w))
                a += 4
            else:
                out.append((a, 2, h))
                a += 2
        return out


def norm(insn):
    a, n, w = insn
    if n == 2:
        return (w & 0xE003,)
    op = w & 0x7F
    rd, f3, rs1, rs2 = (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31, (w >> 20) & 31
    if op in (0x37, 0x17, 0x6F):          # lui auipc jal: rd only
        return (op, rd)
    if op == 0x63:                         # branch
        return (op, f3, rs1, rs2)
    if op == 0x23 or op == 0x27:           # store
        return (op, f3, rs1, rs2)
    if op in (0x03, 0x07, 0x13, 0x1B, 0x67):   # loads, op-imm, jalr: drop imm
        return (op, rd, f3, rs1)
    return (op, w >> 7)


def target_syms(T, names, size_hint, sec_hint, D=None):
    # a name of the donor's alias set that is unique among the target's symbols decides
    uniq = {(T.byname[n][0][0], T.byname[n][0][1], n) for n in names if len(T.byname.get(n, [])) == 1}
    if len({(a, z) for a, z, n in uniq}) == 1:
        return [sorted(uniq)[0]]
    cands = set()
    for n in names:
        for a, z in T.byname.get(n, []):
            cands.add((a, z, n))
    if not cands:
        return []
    if len({(a, z) for a, z, n in cands}) == 1:
        return [sorted(cands)[0]]
    # several: keep those in the hinted section, then those of the donor's size
    c2 = [x for x in cands if T.sec(x[0]) == sec_hint] or list(cands)
    if len({(a, z) for a, z, n in c2}) > 1 and size_hint is not None:
        c3 = [x for x in c2 if x[1] == size_hint]
        if c3:
            c2 = c3
    return sorted({(a, z, n) for a, z, n in c2})


def got_cell(D, T, d):
    dg = D.secd.get(".got")
    tg = T.secd.get(".got")
    if not dg or not tg or not (dg[0] <= d < dg[0] + dg[1]):
        return None
    off = d - dg[0]
    cell = off & ~7
    dn = D.name_of(D.q(dg[0] + cell))
    want_same_off = tg[0] + cell
    tn = T.name_of(T.q(want_same_off)) if cell < tg[1] else None
    if tn == dn:
        return want_same_off + (off & 7), "GOT", "donor .got+%#x holds %s; target .got+%#x holds the same" % (cell, fmt_name(dn), cell)
    hits = [c for c in range(0, tg[1], 8) if T.name_of(T.q(tg[0] + c)) == dn]
    if len(hits) == 1:
        return tg[0] + hits[0] + (off & 7), "GOT", "donor .got+%#x holds %s; target .got+%#x holds it" % (cell, fmt_name(dn), hits[0])
    return None, "GOT?", "donor .got+%#x holds %s; target cells holding it: %d" % (cell, fmt_name(dn), len(hits))


def fmt_name(n):
    if n[0] == "lit":
        return "the value %#x" % n[1]
    if n[0] == "raw":
        return "raw %#x" % n[1]
    return "%s %s+%#x" % (n[0], "|".join(n[1][:3]), n[2])


def expect_addr(D, T, d):
    """(expected target value or None, rule, derivation text) for donor address d."""
    if d in D.geo:
        for q in sorted(D.geo[d]):
            for tv, qs in T.geo.items():
                if q in qs:
                    return tv, "BOUND", "donor %s = %#x; target %s = %#x" % (q, d, q, tv)
    g = got_cell(D, T, d)
    if g:
        return g
    r = D.resolve(d)
    sec = D.sec(d) or D.sec(d - 1)
    if r[0] != "none":
        kind, names, off, lo, size = r
        ts = target_syms(T, names, size if kind == "in" else None, sec)
        if len(ts) == 1:
            ta, tz, tn = ts[0]
            if kind == "end":
                exp = ta + tz
                return exp, "SYMBOL", "donor %#x = the end of %s (%s); target %s [%#x, +%#x) ends at %#x" % (
                    d, "|".join(sorted(names)[:3]), sec, tn, ta, tz, exp)
            exp = ta + off
            how = "donor %#x = %s+%#x (size %#x, %s); target %s at %#x (size %#x) + %#x = %#x" % (
                d, "|".join(sorted(names)[:3]), off, size, sec, tn, ta, tz, off, exp)
            if sec == ".text" and kind == "in" and size and tz:
                di = D.insns(lo, lo + size)
                ti = T.insns(ta, ta + tz)
                dmap = {x[0]: k for k, x in enumerate(di)}
                if d in dmap:
                    k = dmap[d]
                    tk = [x for x in ti if x[0] == exp]
                    if tk and norm(tk[0]) == norm(di[k]) and len(di) == len(ti) and \
                            all(norm(a) == norm(b) for a, b in zip(di, ti)):
                        return exp, "SYMBOL", how + "; the two functions' normalised instruction sequences are equal"
                    sm = difflib.SequenceMatcher(None, [norm(x) for x in di], [norm(x) for x in ti], autojunk=False)
                    for op, i1, i2, j1, j2 in sm.get_opcodes():
                        if op == "equal" and i1 <= k < i2:
                            e2 = ti[j1 + k - i1][0]
                            return e2, "SYMBOL-ALIGNED", (
                                "donor %#x = %s+%#x, instruction %d of %d; the normalised instruction sequences of the "
                                "two functions align it to target instruction %d of %d at %s+%#x = %#x" % (
                                    d, "|".join(sorted(names)[:3]), off, k, len(di), j1 + k - i1, len(ti), tn, e2 - ta, e2))
                    return None, "CODE?", how + "; the instruction at the offset is not in an aligned run"
                if d == lo + size:
                    return ta + tz, "SYMBOL", how
                return exp, "SYMBOL", how + " (mid-instruction offset)"
            return exp, "SYMBOL", how
        if len(ts) > 1:
            # same name and size several times (e.g. musl's static `buf`s): the donor symbol's rank among them by address
            dl = sorted(a for n in names for a, z in D.byname.get(n, []) if z == size)
            dl = sorted(set(dl))
            tl = sorted({a for a, z, n in ts if z == size})
            if kind == "in" and lo in dl and len(dl) == len(tl):
                k = dl.index(lo)
                exp = tl[k] + off
                dn, tn2 = neighbours(D, lo), neighbours(T, tl[k])
                if dn != tn2:
                    return None, "AMBIG", ("donor %#x = %s+%#x, copy %d of %d; the target copy %d has other neighbours (%s / %s)" % (
                        d, "|".join(sorted(names)[:3]), off, k + 1, len(dl), k + 1, dn, tn2))
                return exp, "SYMBOL-RANK", ("donor %#x = %s+%#x (size %#x, %s), the %d-th of %d symbols of that name and size; "
                                            "the %d-th target one is at %#x -> %#x; both copies lie between %s and %s" % (
                                                d, "|".join(sorted(names)[:3]), off, size, sec, k + 1, len(dl), k + 1, tl[k], exp,
                                                dn[0], dn[1]))
            return None, "AMBIG", "donor %#x = %s+%#x; %d target symbols of that name" % (d, "|".join(sorted(names)[:3]), off, len(ts))
        return None, "NO-TWIN", "donor %#x = %s %s+%#x; no target symbol of that name" % (d, kind, "|".join(sorted(names)[:3]), off)
    if D.ro[0] <= d < D.ro[0] + D.ro[1]:
        rob, o = D.rob, d - D.ro[0]
        s = rob.rfind(b"\0", 0, o) + 1
        e = rob.find(b"\0", o)
        if e > s:
            st = rob[s:e + 1]
            dh = string_starts(D.rob, st)
            th = string_starts(T.rob, st)
            if s in dh and len(dh) == len(th):
                k = dh.index(s)
                exp = T.ro[0] + th[k] + (o - s)
                return exp, "BYTES", ("donor %#x is byte %d of the string %r at %#x, the %d-th of %d copies; the %d-th target "
                                      "copy is at %#x -> %#x" % (d, o - s, st[:40], D.ro[0] + s, k + 1, len(dh), k + 1,
                                                                 T.ro[0] + th[k], exp))
        w16 = rob[o:o + 16]
        dh, th = occurrences(D.rob, w16), occurrences(T.rob, w16)
        if o in dh and len(dh) == len(th) and len(dh) <= 16:
            k = dh.index(o)
            return T.ro[0] + th[k], "BYTES", ("the 16 bytes at donor %#x (%s), copy %d of %d; the target's copy %d of %d is at %#x" % (
                d, w16.hex(), k + 1, len(dh), k + 1, len(th), T.ro[0] + th[k]))
        jt = jtable(D, T, d)
        if jt:
            return jt
    an = D.anchor(d)
    return None, "NONE", "donor %#x in %s; nearest symbol %s" % (d, sec, ("%s+%#x" % ("|".join(sorted(an[0])[:3]), an[1])) if an else "-")


def neighbours(I, a):
    """names of the sized symbols just before and just after the symbol at a."""
    i = bisect.bisect_left(I.starts, a)
    j = i - 1
    while j >= 0 and I.objs[j][0] >= a:
        j -= 1
    k = i
    while k < len(I.objs) and I.objs[k][0] <= a:
        k += 1
    prev = "|".join(sorted({o[2] for o in I.objs if j >= 0 and o[0] == I.objs[j][0]})[:2]) if j >= 0 else "-"
    nxt = "|".join(sorted({o[2] for o in I.objs if k < len(I.objs) and o[0] == I.objs[k][0]})[:2]) if k < len(I.objs) else "-"
    return (prev, nxt)


def string_starts(rob, st):
    out, i = [], rob.find(st)
    while i >= 0:
        if i == 0 or rob[i - 1] == 0:
            out.append(i)
        i = rob.find(st, i + 1)
    return out


def occurrences(rob, b):
    out, i = [], rob.find(b)
    while i >= 0 and len(out) < 64:
        out.append(i)
        i = rob.find(b, i + 1)
    return out


def jtable(D, T, d):
    """a 4-byte-entry table (e.g. a relative jump table): the consecutive differences of the 4-byte words around d (signed)
    found at exactly one 4-aligned place of the target .rodata."""
    o = d & ~3
    def words(I, a, lo, hi):
        return [int.from_bytes(I.rd(a + 4 * k, 4), "little", signed=True) for k in range(lo, hi)]
    for lo, hi in ((-8, 9), (-6, 7), (-4, 5), (-3, 4), (-1, 6), (-5, 2)):
        if not (D.ro[0] <= o + 4 * lo and o + 4 * hi <= D.ro[0] + D.ro[1]):
            continue
        dw = words(D, o, lo, hi)
        sig = [b - a for a, b in zip(dw, dw[1:])]
        if not any(sig):
            continue
        n = len(T.rob) // 4
        tws = [int.from_bytes(T.rob[4 * i:4 * i + 4], "little", signed=True) for i in range(n)] if not hasattr(T, "_w4") else T._w4
        T._w4 = tws
        base0 = (T.ro[0] + 3) & ~3
        if base0 != T.ro[0]:
            return None
        hits = []
        for i in range(-lo, n - hi):
            if all(tws[i + lo + k + 1] - tws[i + lo + k] == sig[k] for k in range(len(sig))):
                hits.append(i)
                if len(hits) > 1:
                    break
        if len(hits) == 1:
            p = T.ro[0] + 4 * hits[0]
            return p + (d - o), "JTABLE", ("the 4-byte words at donor %#x+4*[%d,%d) (%s) and at target %#x+4*[%d,%d) differ "
                                           "pairwise by the same amounts (found once in the target .rodata; donor word %#x, "
                                           "target word %#x) -> %#x" % (o, lo, hi, " ".join("%#x" % (w & 0xffffffff) for w in dw[:4]),
                                                                          p, lo, hi, dw[-lo] & 0xffffffff, tws[hits[0]] & 0xffffffff,
                                                                          p + (d - o)))
    return None


def in_image(I, v):
    return 0x10000 <= v <= I.top_up


def is_shadow(v):
    return SHADOW_OFF <= v < SHADOW_OFF + (1 << 44)


def size_match(D, T, d, w):
    """d is a donor image quantity (a bound or size: section, PT_LOAD, page-up top, span) or that quantity / 8 or / 4096,
    and w is the same quantity of the target, divided the same way: the derivation text, else None."""
    for n, dv in sorted(D.quant.items()):
        tv = T.quant.get(n)
        if tv is None:
            continue
        for k, lab in ((1, ""), (8, " / 8"), (4096, " / 4096")):
            if dv % k == 0 and tv % k == 0 and dv // k == d and tv // k == w and d >= 64:
                if not lab:
                    return "donor %s = %#x; target %s = %#x" % (n, d, n, w)
                return "donor %s = %#x%s = %#x; target %s = %#x%s = %#x" % (n, dv, lab, d, n, tv, lab, w)
    return None


def derive(D, T, d, w):
    """(verdict OK/WRONG/OPEN, rule, expected, how) for donor value d and written value w."""
    sz = size_match(D, T, d, w)
    if sz:
        return "OK", "IMAGE-QTY", w, sz
    if is_shadow(d) and is_shadow(w):
        ud = (d - SHADOW_OFF) * 8
        exp, rule, how = expect_addr(D, T, ud)
        if exp is None:
            return "OPEN", "SHADOW-" + rule, None, "unshadow(%#x) = %#x: %s" % (d, ud, how)
        ex = exp // 8 + SHADOW_OFF
        exc = (exp + 7) // 8 + SHADOW_OFF
        ok = w in (ex, exc)
        return ("OK" if ok else "WRONG"), "SHADOW-" + rule, (w if ok else ex), \
            "unshadow(%#x) = %#x; %s; shadow(%#x) = %#x%s" % (d, ud, how, exp, ex, (" (ceil %#x)" % exc) if exc != ex else "")
    if in_image(D, d):
        exp, rule, how = expect_addr(D, T, d)
        if exp is None:
            return "OPEN", rule, None, how
        return ("OK" if exp == w else "WRONG"), rule, exp, how
    return "OPEN", "NOT-ADDRESS", None, "donor value %#x is not an address of the donor image" % d
