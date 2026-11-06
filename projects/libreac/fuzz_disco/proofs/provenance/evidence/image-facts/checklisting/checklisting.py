#!/usr/bin/env python3
"""Independent re-check of a position-abstract listing (mklisting.py + emit_rocq.py) against the ELF.

Parses <Name>List.v, <Name>Addr.v and <Name>Syms.v (no code shared with mklisting.py) and checks, for
every slot, what PaTable.v's `pi_slot_check` checks, with val A_TEXT = <p>_text,
val (A_OBJ i) = <p>_obj i, val (A_HI j) = <p>_hi j, sigma = <p>_sigma (p = --prefix):
  PW w                         fetch(pc) = w
  PCall s rd                   word is a 4-byte jal rd' imm, rd = rd' <> 0, canon(pc + imm) = sigma s
  PTail s                      word is a 4-byte jal x0 imm, canon(pc + imm) = sigma s
  PHi rd j                     word is a 4-byte auipc rd imm, canon(pc + sext32(imm << 12)) = <p>_hi j
  PAddHi rd rs j a off         word is addi rd, rs, imm and <p>_hi j + imm = val a + off
  PLdHi rd rs j a off sz sg    word is the load of size sz and sign sg, rd, rs, same address equation
where pc = <p>_text + 4 * index. The decoder follows LinuxProcessSemantics Riscv/Decode.v and
DecodeC.decode_any (a word whose low two bits are not 11 is a 2-byte instruction, so it fails).

It also checks: the slot count against <p>_nslots and the [<p>_text, end) range; the functions:
every function symbol (nm type t/T/w/W) whose address is in the range has an AF_<fn>, and every
AF_<fn> puts <fn> at its symbol address; every constructor has a <p>_sigma entry, and
<p>_sigma s against the symbol address of the name s stands for; every PAddHi/PLdHi is paired with
the auipc that last wrote its base register on straight-line code that no jump enters; every
object lies in a PT_LOAD. <p>_obj/<p>_hi may be a `match` or a list read by `nth`.

usage: checklisting.py --prog DIR --elf IMAGE --nm SYMS [--name Grant] [--prefix grant]
                       [--jtable ADDR,COUNT,rel32]...
  SYMS: the `nm -S` symbol file, or an ELF with a symbol table (the .debug twin) read through
  elfsyms.py.
"""
import argparse
import os
import re
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

MASK64 = (1 << 64) - 1


def symbol_lines(path):
    """The `addr size type name` lines of a symbol file, or of an ELF through elfsyms.py."""
    with open(path, "rb") as fh:
        is_elf = fh.read(4) == b"\x7fELF"
    if is_elf:
        import elfsyms
        return elfsyms.symbol_lines(path)
    return open(path).read().split("\n")


def sext(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


def strip_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i):
            depth += 1; i += 2
        elif depth and s.startswith("*)", i):
            depth -= 1; i += 2
        else:
            if not depth:
                out.append(s[i])
            i += 1
    return "".join(out)


def zint(tok):
    tok = tok.strip()
    neg = tok.startswith("-")
    if neg:
        tok = tok[1:]
    v = int(tok, 16) if tok.lower().startswith("0x") else int(tok)
    return -v if neg else v


def parse_match(text, name):
    """Definition NAME (x : T) : Z := match x with | K => V ... | _ => D end."""
    m = re.search(r"Definition\s+%s\b.*?:=\s*match\s+\w+\s+with(.*?)\bend\s*\." % re.escape(name), text, re.S)
    if not m:
        sys.exit("cannot find Definition %s" % name)
    table, default = {}, None
    for k, v in re.findall(r"\|\s*([^|=]+?)\s*=>\s*([-0-9a-fA-Fx]+)", m.group(1)):
        k = k.strip()
        if k == "_":
            default = zint(v)
            continue
        k = re.sub(r"%nat$", "", k)
        if k in table:
            sys.exit("%s: duplicate case %s" % (name, k))
        table[int(k) if k.isdigit() else k] = zint(v)
    return table, default


def parse_table(text, name):
    """NAME as a `match` (parse_match), or as `Definition NAME (i : nat) : Z := nth i NAMEs 0.` over
    `Definition NAMEs : list Z := [v; ...].`; returns (table, default)."""
    if re.search(r"Definition\s+%s\b[^.]*?:=\s*match\b" % re.escape(name), text):
        return parse_match(text, name)
    m = re.search(r"Definition\s+%s\s*\(\s*\w+\s*:\s*nat\s*\)\s*:\s*Z\s*:=\s*nth\s+\w+\s+(\w+)\s+"
                  r"([-0-9a-fA-Fx]+)\s*\." % re.escape(name), text)
    if not m:
        sys.exit("cannot find Definition %s (match or nth over a list)" % name)
    lm = re.search(r"Definition\s+%s\s*:\s*list\s+Z\s*:=\s*\[(.*?)\]\s*\." % re.escape(m.group(1)), text, re.S)
    if not lm:
        sys.exit("cannot find Definition %s : list Z" % m.group(1))
    vals = [zint(v) for v in lm.group(1).split(";") if v.strip()]
    return dict(enumerate(vals)), zint(m.group(2))


def parse_count(text, name, table):
    """NAME : nat := N%nat, or := length L (the table's size)."""
    if re.search(r"Definition\s+%s\s*:\s*nat\s*:=\s*length\b" % re.escape(name), text):
        return len(table)
    return parse_def_z(text, name)


def parse_def_z(text, name):
    m = re.search(r"Definition\s+%s\s*:\s*\w+\s*:=\s*([-0-9a-fA-Fx]+)(%%nat)?\s*\." % re.escape(name), text)
    if not m:
        sys.exit("cannot find Definition %s" % name)
    return zint(m.group(1))


class Elf:
    def __init__(self, path):
        self.b = open(path, "rb").read()
        b = self.b
        if b[:4] != b"\x7fELF" or b[4] != 2 or b[5] != 1:
            sys.exit("%s: not a 64-bit little-endian ELF" % path)
        if struct.unpack_from("<H", b, 18)[0] != 243:
            sys.exit("%s: not RISC-V" % path)
        phoff, = struct.unpack_from("<Q", b, 32)
        phentsize, phnum = struct.unpack_from("<HH", b, 54)
        self.segs = []
        self.loads = []     # (vaddr, memsz): every PT_LOAD, for the objects-in-image check
        for i in range(phnum):
            o = phoff + i * phentsize
            p_type, p_flags, p_offset, p_vaddr, _pa, p_filesz, p_memsz, _al = struct.unpack_from("<IIQQQQQQ", b, o)
            if p_type == 1:
                self.segs.append((p_vaddr, p_filesz, p_offset, p_flags))
                self.loads.append((p_vaddr, p_memsz))

    def fetch(self, a):
        """The 4-byte word at a, from an executable PT_LOAD's file bytes; None if not there."""
        for va, fsz, off, fl in self.segs:
            if fl & 1 and va <= a and a + 4 <= va + fsz:
                return struct.unpack_from("<I", self.b, off + a - va)[0]
        return None

    def in_load(self, a):
        return any(va <= a < va + msz for va, msz in self.loads)

    def read(self, a, n):
        for va, fsz, off, _fl in self.segs:
            if va <= a and a + n <= va + fsz:
                return self.b[off + a - va: off + a - va + n]
        return None

    def jump_targets(self):
        """Every address a branch or direct jump of the image's code sends control to, and the set of
        instruction starts. Each executable PT_LOAD is decoded from its first byte by instruction
        length (low two bits 11: 4 bytes, else 2), which is exact for a segment that holds only
        code (fuzz_grant: the one executable segment is .text)."""
        targets, starts = {}, set()
        for va, fsz, off, fl in self.segs:
            if not fl & 1:
                continue
            a = va
            while a + 2 <= va + fsz:
                starts.add(a)
                h = struct.unpack_from("<H", self.b, off + a - va)[0]
                if h & 3 == 3:
                    if a + 4 > va + fsz:
                        break
                    w = struct.unpack_from("<I", self.b, off + a - va)[0]
                    opc = w & 0x7f
                    if opc == 0x63:
                        imm = (((w >> 31) & 1) << 12) | (((w >> 7) & 1) << 11) | \
                              (((w >> 25) & 0x3f) << 5) | (((w >> 8) & 0xf) << 1)
                        targets.setdefault((a + sext(imm, 13)) & MASK64, a)
                    elif opc == 0x6F:
                        targets.setdefault((a + decode(w)[2]) & MASK64, a)
                    a += 4
                else:
                    q, f3 = h & 3, h >> 13
                    if q == 1 and f3 == 5:                  # c.j
                        imm = (((h >> 12) & 1) << 11) | (((h >> 11) & 1) << 4) | (((h >> 9) & 3) << 8) | \
                              (((h >> 8) & 1) << 10) | (((h >> 7) & 1) << 6) | (((h >> 6) & 1) << 7) | \
                              (((h >> 3) & 7) << 1) | (((h >> 2) & 1) << 5)
                        targets.setdefault((a + sext(imm, 12)) & MASK64, a)
                    elif q == 1 and f3 in (6, 7):           # c.beqz, c.bnez
                        imm = (((h >> 12) & 1) << 8) | (((h >> 10) & 3) << 3) | (((h >> 5) & 3) << 6) | \
                              (((h >> 3) & 3) << 1) | (((h >> 2) & 1) << 5)
                        targets.setdefault((a + sext(imm, 9)) & MASK64, a)
                    a += 2
        return targets, starts


def writes_x(w):
    """The integer register a 4-byte instruction writes, or None (branches, stores, fences, and
    floating-point results go to no x register)."""
    opc, rd = w & 0x7f, (w >> 7) & 31
    if opc in (0x63, 0x23, 0x27, 0x0F, 0x07, 0x43, 0x47, 0x4B, 0x4F):
        return None
    if opc == 0x53 and (w >> 27) not in (0x14, 0x18, 0x1C):   # only compares, fcvt.int, fmv.x/fclass
        return None
    return rd or None


LOADS = {0: ("SZ1", True), 1: ("SZ2", True), 2: ("SZ4", True), 3: ("SZ8", True),
         4: ("SZ1", False), 5: ("SZ2", False), 6: ("SZ4", False)}


def decode(w):
    """The instructions pi_slot_check can match, per LPS Decode.v; ('other',) for the rest."""
    if w & 3 != 3:
        return ("c16",)
    opc, rd, f3, rs1 = w & 0x7f, (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31
    if opc == 0x6F:
        imm = (((w >> 31) & 1) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3ff) << 1)
        return ("jal", rd, sext(imm, 21))
    if opc == 0x17:
        return ("auipc", rd, sext(w & 0xfffff000, 32))
    if opc == 0x13 and f3 == 0:
        return ("addi", rd, rs1, sext(w >> 20, 12))
    if opc == 0x03 and f3 in LOADS:
        sz, sg = LOADS[f3]
        return ("load", rd, rs1, sext(w >> 20, 12), sz, sg)
    return ("other",)


REG = r"\((\d+)%bv\s*:\s*reg\)"
NUM = r"(-?(?:0x[0-9a-fA-F]+|\d+))"
SLOT_RES = [
    ("PW", re.compile(r"^PW\s+" + NUM + r"$")),
    ("PCall", re.compile(r"^PCall\s+([A-Z]S_\w+)\s+" + REG + r"$")),
    ("PTail", re.compile(r"^PTail\s+([A-Z]S_\w+)$")),
    ("PHi", re.compile(r"^PHi\s+" + REG + r"\s+(\d+)$")),
    ("PAddHi", re.compile(r"^PAddHi\s+" + REG + r"\s+" + REG + r"\s+(\d+)\s+\(A_OBJ\s+(\d+)\)\s+" + NUM + r"$")),
    ("PLdHi", re.compile(r"^PLdHi\s+" + REG + r"\s+" + REG + r"\s+(\d+)\s+\(A_OBJ\s+(\d+)\)\s+" + NUM
                         + r"\s+(SZ[1248])\s+(true|false)$")),
]


def parse_slot(s):
    s = " ".join(s.split())
    for kind, rx in SLOT_RES:
        m = rx.match(s)
        if m:
            return (kind,) + m.groups()
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prog", required=True, help="the directory of <Name>List.v, <Name>Addr.v, <Name>Syms.v")
    ap.add_argument("--elf", required=True, help="the pinned image")
    ap.add_argument("--nm", required=True, help="the symbol file (nm -S lines) or the .debug ELF")
    ap.add_argument("--name", default="Grant", help="file prefix (emit_rocq --name)")
    ap.add_argument("--prefix", default="grant", help="identifier prefix (emit_rocq --prefix)")
    ap.add_argument("--jtable", action="append", default=[],
                    help="ADDR,COUNT,KIND (repeatable): a jump table whose entries are jump targets; "
                         "KIND rel32 = COUNT signed 4-byte offsets from ADDR "
                         "(fuzz_grant: 0x20ff4,10,rel32, ctrl_lay_block's table)")
    a = ap.parse_args()
    N, P = a.name, a.prefix
    ty = P[0].lower() + "sym"

    lst = strip_comments(open(os.path.join(a.prog, N + "List.v")).read())
    adr = strip_comments(open(os.path.join(a.prog, N + "Addr.v")).read())
    syms_t = strip_comments(open(os.path.join(a.prog, N + "Syms.v")).read())

    m = re.search(r"Inductive\s+%s\s*:\s*Type\s*:=(.*?)\." % ty, syms_t, re.S)
    gsyms = [x.strip() for x in m.group(1).split("|") if x.strip()]
    text = parse_def_z(adr, P + "_text")
    sigma, sig_def = parse_match(adr, P + "_sigma")
    obj, obj_def = parse_table(adr, P + "_obj")
    hi, hi_def = parse_table(adr, P + "_hi")
    nobj, nhi = parse_count(adr, P + "_nobj", obj), parse_count(adr, P + "_nhi", hi)
    nslots = parse_def_z(lst, P + "_nslots")
    obj_v = lambda i: obj.get(i, obj_def)
    hi_v = lambda j: hi.get(j, hi_def)

    problems = []
    if len(set(gsyms)) != len(gsyms):
        problems.append("%sSyms: duplicate constructor" % N)
    if sig_def is None and set(sigma) != set(gsyms):
        problems.append("%s_sigma cases differ from %s: %s" % (P, ty, sorted(set(sigma) ^ set(gsyms))))
    if set(obj) != set(range(nobj)):
        problems.append("%s_obj cases are not 0..%s_nobj-1" % (P, P))
    if set(hi) != set(range(nhi)):
        problems.append("%s_hi cases are not 0..%s_nhi-1" % (P, P))

    af = dict((n, zint(v)) for n, v in re.findall(r"Definition\s+AF_(\S+)\s*:\s*Z\s*:=\s*" + NUM + r"\s*\.", lst))
    bad_ident = [n for n in af if not re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", n)]

    m = re.search(r"Definition\s+%s_listing\s*:\s*ptable\s+%s\s*:=\s*\[(.*)\]\s*\." % (P, ty), lst, re.S)
    raw = [x.strip() for x in m.group(1).split(";")]
    if raw and raw[-1] == "":
        raw.pop()

    elf = Elf(a.elf)
    nm, fstart = {}, {}
    for line in symbol_lines(a.nm):
        p = line.split()
        if len(p) >= 4:
            nm.setdefault(p[3], []).append(int(p[0], 16))
            if p[2] in "tTwW":
                fstart.setdefault(int(p[0], 16), p[3])

    fails = []
    used_obj, used_hi = set(), set()
    kinds = {}
    for k, s in enumerate(raw):
        pc = text + 4 * k
        e = parse_slot(s)
        w = elf.fetch(pc)
        if e is None:
            fails.append((k, pc, s, w, "slot does not parse"))
            continue
        kinds[e[0]] = kinds.get(e[0], 0) + 1
        if w is None:
            fails.append((k, pc, s, w, "no executable bytes at pc"))
            continue
        kind = e[0]
        if kind == "PW":
            ok = w == zint(e[1]) & 0xffffffff and 0 <= zint(e[1]) <= 0xffffffff
            why = "word differs"
        else:
            d = decode(w)
            ok, why = False, "word decodes as %s" % (d[0],)
            if kind == "PCall" and d[0] == "jal":
                sname, rd = e[1], int(e[2])
                tgt = (pc + d[2]) & MASK64
                ok = rd == d[1] and d[1] != 0 and sname in sigma and tgt == sigma[sname]
                why = "jal x%d -> %#x, slot wants x%d -> %s = %s" % (d[1], tgt, rd, sname, hex(sigma[sname]) if sname in sigma else "?")
            elif kind == "PTail" and d[0] == "jal":
                sname = e[1]
                tgt = (pc + d[2]) & MASK64
                ok = d[1] == 0 and sname in sigma and tgt == sigma[sname]
                why = "jal x%d -> %#x, slot wants x0 -> %s = %s" % (d[1], tgt, sname, hex(sigma[sname]) if sname in sigma else "?")
            elif kind == "PHi" and d[0] == "auipc":
                rd, j = int(e[1]), int(e[2])
                used_hi.add(j)
                v = (pc + d[2]) & MASK64
                ok = rd == d[1] and hi_v(j) is not None and v == hi_v(j)
                why = "auipc x%d = %#x, slot wants x%d, %s_hi %d = %s" % (d[1], v, rd, P, j, hi_v(j))
            elif kind == "PAddHi" and d[0] == "addi":
                rd, rs, j, i, off = int(e[1]), int(e[2]), int(e[3]), int(e[4]), zint(e[5])
                used_hi.add(j); used_obj.add(i)
                ok = rd == d[1] and rs == d[2] and hi_v(j) is not None and obj_v(i) is not None \
                    and hi_v(j) + d[3] == obj_v(i) + off
                why = "addi x%d,x%d,%d; %s_hi %d + imm = %s, %s_obj %d + off = %s" % (
                    d[1], d[2], d[3], P, j, hex(hi_v(j) + d[3]) if hi_v(j) is not None else "?", P, i,
                    hex(obj_v(i) + off) if obj_v(i) is not None else "?")
            elif kind == "PLdHi" and d[0] == "load":
                rd, rs, j, i, off, sz, sg = int(e[1]), int(e[2]), int(e[3]), int(e[4]), zint(e[5]), e[6], e[7] == "true"
                used_hi.add(j); used_obj.add(i)
                ok = rd == d[1] and rs == d[2] and sz == d[4] and sg == d[5] and hi_v(j) is not None \
                    and obj_v(i) is not None and hi_v(j) + d[3] == obj_v(i) + off
                why = "load %s %s x%d,%d(x%d); %s_hi %d + imm = %s, %s_obj %d + off = %s" % (
                    d[4], d[5], d[1], d[3], d[2], P, j, hex(hi_v(j) + d[3]) if hi_v(j) is not None else "?", P, i,
                    hex(obj_v(i) + off) if obj_v(i) is not None else "?")
        if not ok:
            fails.append((k, pc, s, w, why))

    end = text + 4 * len(raw)
    print("slots parsed: %d (%s_nslots %d), range %#x .. %#x" % (len(raw), P, nslots, text, end))
    print("slot kinds: %s" % ", ".join("%s %d" % kv for kv in sorted(kinds.items())))
    if len(raw) != nslots:
        problems.append("listing has %d slots, %s_nslots is %d" % (len(raw), P, nslots))
    print("slot checks failing: %d" % len(fails))
    for k, pc, s, w, why in fails[:20]:
        print("  FAIL index %d pc %#x slot `%s` ELF word %s: %s" % (k, pc, s, "%#010x" % w if w is not None else None, why))
    if used_obj - set(obj) or used_hi - set(hi):
        problems.append("listing uses objects %s / hi values %s with no table entry" % (sorted(used_obj - set(obj)), sorted(used_hi - set(hi))))

    # The pairs: each PAddHi/PLdHi uses the hi value of the auipc that last wrote its base register,
    # on straight-line code. From that auipc to the use: no branch/jal/jalr, and nothing anywhere in
    # the image (branch, jump, jump-table entry, function symbol) sends control into (auipc, use].
    targets, starts = elf.jump_targets()
    for spec in a.jtable:
        ta, cnt, kind = spec.split(",")
        ta, cnt = int(ta, 16), int(cnt, 0)
        if kind != "rel32":
            sys.exit("--jtable %s: unknown kind %s (known: rel32)" % (spec, kind))
        tb = elf.read(ta, 4 * cnt)
        if tb is None:
            sys.exit("--jtable %s: the table is not in the image's file bytes" % spec)
        for q in range(cnt):
            targets.setdefault((ta + struct.unpack_from("<i", tb, 4 * q)[0]) & MASK64, "jtable %#x[%d]" % (ta, q))
    for fa, fn in fstart.items():
        targets.setdefault(fa, "symbol " + fn)
    misaligned = [text + 4 * k for k in range(len(raw)) if text + 4 * k not in starts]
    if misaligned:
        problems.append("the image's linear decode does not start an instruction at %d listing pcs (first %#x)"
                        % (len(misaligned), misaligned[0]))
    pair_fails, npairs = [], 0
    for k, s in enumerate(raw):
        e = parse_slot(s)
        if e is None or e[0] not in ("PAddHi", "PLdHi"):
            continue
        npairs += 1
        pc, rs, j, i = text + 4 * k, int(e[2]), int(e[3]), int(e[4])
        whys = []
        if not elf.in_load(obj_v(i) if obj_v(i) is not None else -1):
            whys.append("object %d = %s lies in no PT_LOAD" % (i, obj_v(i)))
        h = k - 1
        while h >= 0 and (elf.fetch(text + 4 * h) is None or writes_x(elf.fetch(text + 4 * h)) != rs):
            h -= 1
        eh = parse_slot(raw[h]) if h >= 0 else None
        if h < 0:
            whys.append("no earlier slot writes x%d" % rs)
        elif eh is None or eh[0] != "PHi" or int(eh[1]) != rs or int(eh[2]) != j:
            whys.append("x%d was last written at index %d by `%s`, not by PHi x%d %d" % (rs, h, raw[h], rs, j))
        else:
            hpc = text + 4 * h
            for q in range(h + 1, k):
                if elf.fetch(text + 4 * q) & 0x7f in (0x63, 0x6F, 0x67):
                    whys.append("control flow at %#x between the auipc %#x and the use" % (text + 4 * q, hpc))
                    break
            into = sorted(t for t in targets if hpc < t <= pc)
            if into:
                src = targets[into[0]]
                whys.append("%#x (from %s) is a jump target in (auipc %#x, use]"
                            % (into[0], src if isinstance(src, str) else "%#x" % src, hpc))
        if whys:
            pair_fails.append((k, pc, s, "; ".join(whys)))
    print("pairs (PAddHi/PLdHi): %d, failing the auipc-to-use straight-line or object-in-image checks: %d"
          % (npairs, len(pair_fails)))
    for k, pc, s, why in pair_fails[:20]:
        print("  FAIL index %d pc %#x slot `%s`: %s" % (k, pc, s, why))
    fails += [(k, pc, s, elf.fetch(pc), why) for k, pc, s, why in pair_fails]
    for i in sorted(obj):
        if not elf.in_load(obj[i]):
            problems.append("%s_obj %d = %#x lies in no PT_LOAD of the image" % (P, i, obj[i]))

    print("AF_ definitions: %d" % len(af))
    for n, off in af.items():
        # A symbol whose name is not a Rocq identifier (asan.module_ctor) gets '.' -> '_' in AF_.
        got = nm.get(n) or nm.get(next((k for k in nm if k.replace(".", "_") == n), None))
        if got is None:
            problems.append("AF_%s: no symbol %s in nm" % (n, n))
        elif text + off not in got:
            problems.append("AF_%s = %#x: %s_text + AF = %#x, nm has %s" % (n, off, P, text + off, [hex(x) for x in got]))
    for n in bad_ident:
        problems.append("AF_%s: `AF_%s` is not a valid Rocq identifier (contains '.')" % (n, n))

    # the functions: every function symbol in the range has its AF_ (the name made a Rocq
    # identifier), at a slot, and AF_ gives the symbol's address
    infuncs = {}
    for line in symbol_lines(a.nm):
        p = line.split()
        if len(p) >= 4 and p[2] in "tTwW" and text <= int(p[0], 16) < end:
            infuncs.setdefault(p[3], set()).add(int(p[0], 16))
    print("function symbols in the range: %d" % len(infuncs))
    for n, addrs in sorted(infuncs.items()):
        rn = "".join(c if (c.isalnum() or c == "_") else "_" for c in n)
        for addr in sorted(addrs):
            if (addr - text) % 4:
                problems.append("%s %#x does not start at a slot" % (n, addr))
        if af.get(rn) is None:
            problems.append("%s (in the range at %s) has no AF_%s" % (n, [hex(x) for x in sorted(addrs)], rn))
        elif text + af[rn] not in addrs:
            problems.append("AF_%s gives %#x, the symbol file has %s at %s" % (rn, text + af[rn], n, [hex(x) for x in sorted(addrs)]))

    notes = []
    for s in gsyms:
        name = s[3:]
        cand = [name, name.replace("___interceptor_trampoline_", "__interceptor_trampoline_")]
        cand += [name.replace("GS_", "")]
        got = next((nm[c] for c in cand if c in nm), None)
        if s not in sigma:
            continue
        if got is None:
            notes.append("%s_sigma %s = %#x: no nm symbol named %s" % (P, s, sigma[s], name))
        elif sigma[s] not in got:
            problems.append("%s_sigma %s = %#x, nm has %s at %s" % (P, s, sigma[s], name, [hex(x) for x in got]))

    print("other problems: %d" % len(problems))
    for p in problems:
        print("  PROBLEM " + p)
    for n in notes:
        print("  NOTE " + n)
    return 1 if fails or problems else 0


if __name__ == "__main__":
    sys.exit(main())
