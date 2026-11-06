#!/usr/bin/env python3
"""numeral_map.py --map map.json [--image-old OLD.v --image-new NEW.v] (--report | --rewrite OUTDIR) FILES...

Find every address-like number in Rocq .v files and move it with an elf_symbols.py
map (OLD binary -> NEW binary).

Every numeric literal (hex 0x..., decimal) is classified against the OLD
binary: exec / data / bss / tls (inside a section), func-entry (an OLD function
start whose NEW function start, from both binaries' FDE tables, is not where
the code map puts it), return-addr (the instruction after a call in the same
function: it moves with the call, map(call) + the NEW call's length),
section-end, geometry (an exact image constant: entry, segment base/end/size,
hull bounds and size, hull.hi >> 3 and its shadow byte), brk-relative and
brk-aslr (just past the image end, alone or plus the brk ASLR window), shadow
(the ASan shadow byte of a data/bss address), page-index (an image constant
>> 12), image-pad, complement (~v maps as an address: review only), or
not-an-address.  D in `change (EXPR) with D`, EXPR closed arithmetic equal to D
in OLD, is recomputed from the rewritten EXPR (class derived).

A literal is rewritten only when its class gives one unambiguous new value.
Never rewritten, listed for review instead:
  * values inside deleted/inserted/ambiguous regions of the map,
  * decimals below --small (sizes/counts), page indices, decimal values that
    fall in code, code addresses that are not an instruction start, decimal
    data/bss/tls/shadow values that no code/pointer reference anchors,
  * values at an object boundary outside an interval context (as an address
    or as one past the object below?), and values equal to an OLD auipc
    result (`auipc-result?`, with the rc.2 auipc result as a candidate),
  * opcode literals (`Z_to_bv 32 0x...`, `bv 32 := 0x...`): opcode-check-needed,
  * arguments of decoded-instruction terms (`decode_any W = Some (Jal 1 2044, 4%Z)`):
    decode-check-needed,
  * hex embedded in identifiers and file names: status `ident-mapped` (the new
    value a consumer may rename to) only for address-named identifiers matching
    an --ident-addr pattern (`W_1380c`, `Ref_code_1380c_14000.v`, `img_38c18_8`),
    `ident-review` for every other identifier (`u_add64`).
Kept as constants: ZOracle table keys (goal hashes compared against in
`Ltac2 Set ...zor_* := fun k => ... Int.equal k N`) and size/length arguments
of known constructors (SIZE_ARGS: MSplit's bounds, KDisj's lengths, ...).
The end of a half-open interval (KImg lo hi, `lo <= x < hi`, sorted lists of
(lo, hi) pairs, `(hi - lo)`) maps as map(hi - 1) + 1.
Literals inside comments are rewritten too and counted separately; literals
inside strings are only reported.
"""

import argparse
import bisect
import json
import os
import re
import struct
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rvelf  # noqa: E402

LIT_RE = re.compile(r"(?<![A-Za-z0-9_'])(0[xX][0-9a-fA-F]+|[0-9]+)(?![A-Za-z0-9_'])")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
OPCODE_CTX_RE = re.compile(r"(?:Z_to_bv\s+(?:16|32)|\bbv\s+(?:16|32)\s*:=)\s*\(?\s*$")
DECODE_RE = re.compile(r"decode_any\s+(?P<w>\([^()]*\)|[^\s=]+)\s*=\s*Some\s*\(\s*(?P<ctor>[A-Z][A-Za-z0-9_]*)"
                       r"(?P<args>(?:[^,()]|\([^()]*\))*),")
# Constructors whose immediate moves with code/data (PC-relative, or an absolute high part).
ADDR_CTORS = {"Auipc", "Jal", "Branch", "Lui"}
REWRITABLE = {"exec", "func-entry", "return-addr", "data", "bss", "tls", "section-end", "geometry", "brk-relative",
              "brk-aslr", "shadow", "tls-cell", "tls-shadow", "derived"}
# geometry values derived from another geometry value: a collision with an address reading is decided per use site
DERIVED_GEOMETRY = ("hull.hi>>shadow_scale", "shadow(hull.hi)")
# `change (EXPR) with D` where EXPR is closed integer arithmetic: D is EXPR's value, recomputed after a rewrite
CHANGE_WITH_RE = re.compile(r"change\s+\((?P<e>[0-9a-fA-Fx+\-*/()\s]+)\)\s+with\s+(?P<d>0[xX][0-9a-fA-F]+|[0-9]+)"
                            r"(?![A-Za-z0-9_'])")
U64_MAX = (1 << 64) - 1
DTP_OFFSET = 0x800  # riscv TLS: dtv[1] = tp + 0x800
# Runtime constants that fall inside mapped ranges (directly, or as a shadow byte of an image address) and
# must never move. Matched by value, so hex and decimal spellings alike.
NOT_ADDRESS = (
    0x100022, 0x100032, 0x104022, 0x104032,  # mmap flag words (MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE|...)
    0x7FFFF000,                              # MAX_RW_COUNT (Linux read/write clamp)
    0x800B9400,                              # = 2148242432, an ASan FakeStack offset constant (port-18 K/A/Z11.v:398,655)
)
# Constants written in decimal that must never move, matched only in their decimal spelling: the same value in hex
# can be a real address (0x61a80 is a plausible PC).
NOT_ADDRESS_DECIMAL = (
    400000,  # checker fuel (myanmar AsStartA/BsStartB/AdCertMH/AdCertMBH, plan-myanmar via port-13)
)
# A decimal literal in these classes is rewritten only when a code or pointer reference anchors that exact address
# (for a shadow byte, the address it shadows); hex literals, and classes whose new value is an exact image constant
# (geometry, section ends, brk) or the code-anchored TLS layout (tls-cell), keep their rules.
ANCHORED_CLASSES = {"data", "bss", "tls", "shadow"}
# Classes where a value that starts an object can also be read as one past the end of the object below.
BOUNDARY_CLASSES = {"data", "bss", "tls", "tls-cell"}
# Size/length/count argument positions (0-based) of plan, knowledge and node constructors, from the engine files'
# signatures (coturn/opendnp3/mosquitto SymExec2/3, AxSymExec3, AsanPlan, AsanPlanCore, AsanNodes*; mosh Common/Ax,
# CJ/Lib): a literal there (bare, `N%Z`, or `(ELit N)`) is a size, never an address.
SIZE_ARGS = {
    "KWr": (1,), "KZero": (1,), "KBlob": (1,), "KFill": (1,), "KUnk": (1,), "KDisj": (1, 3),
    "SCFlat": (1,), "SCDisj": (1, 3), "SCInside": (1, 3), "SCDisjoint": (1, 3), "SCStoreOk": (1,), "SCReadBase": (1,),
    "PShDisj": (1, 3), "PJoin": (2,), "PReadWord": (2,), "PDropRange": (1,), "PGhost": (1,), "PUnvis": (1,),
    "PAbstractCell": (1,), "PVisAbsorb": (1,), "PFreshCell": (1,), "PFreshCellK": (1,), "PVisSplit": (1,),
    "PVisRespell": (1, 3), "PMapRespell": (1, 3), "PDisjNth": (1,), "PFog": (1,), "PFogNew": (1,), "PLoop": (1,),
    "PUnion": (2,), "PZeroSub": (1,), "PFdRespell": (0,), "FdFile": (1,),
    "NRead": (2,), "NMmap": (1,), "NMunmap": (1,), "NMprotect": (1,), "EMmap": (1,), "EMunmap": (1,), "EMprotect": (1,),
    "MWindow": (1,), "MWindowAt": (2,), "MStackLift": (2,), "MStackMerge": (2,), "MShWindowAt": (2,), "MMergeAt": (2,),
    "MCanonCls": (2, 3), "CCharge": (2,), "CChargeSh": (2,), "CChargeP": (3,), "CChargePSh": (3,), "CForget": (2,),
    "ZUnwIns": (4,),
    "MSplit": (2, 3), "MSplitK": (2, 3),  # mosh memop `MSplit r sh lo hi`: size bounds (only with a bool at position 1)
}
BOOL_AT_1 = {"MSplit", "MSplitK"}  # coturn's `MSplit q mid le gt` (an mtree) has no bool there and is left alone
# Half-open [lo, hi) interval argument positions: hi is one past the last byte.
HALF_OPEN = {"KImg": (0, 1), "PMemRespell": (1, 2)}
# Address positions: the engines type these fields as addresses (a base expression b/b1/b2/b', an addr/buf, an
# image range), so a decimal literal there is an address and needs no reference anchor.  Positions as in SIZE_ARGS.
ADDR_ARGS = {
    "KImg": (0, 1), "RImg": (0, 1), "RR_img": (0, 1),
    "PShDisj": (0, 2), "PDropRange": (0,), "PGhost": (0,), "PUnvis": (0,), "PAbstractCell": (0,), "PVisAbsorb": (0,),
    "PFreshCell": (0,), "PFreshCellK": (0,), "PVisSplit": (0,), "PVisRespell": (0, 2), "PMapRespell": (0, 2),
    "PMemRespell": (0, 3), "PDisjNth": (0,), "PUnion": (1,), "PZeroSub": (0,), "PCaseDisj": (0, 1),
    "PCaseDisjJ": (0, 1), "PVisHead": (0,), "PUnvisHead": (0,),
    "NRead": (1,), "NMmap": (0,), "NMunmap": (0,), "NMprotect": (0,), "EMmap": (0,), "EMunmap": (0,), "EMprotect": (0,),
}
# List-of-address positions: every `ELit N` in that list argument is an address (`PHavocWords (bs : list expr)`).
LIST_ADDR_ARGS = {"PHavocWords": 0}
ELIT_RE = re.compile(r"\bELit\s+\(?\s*(0[xX][0-9a-fA-F]+|\d+)")
# Offsets that are addresses when their base is (ELit 0): PJoin/PReadWord `b off`, PMemRespell `b lo hi`.
BASE_OFF = {"PJoin": (0, (1,)), "PReadWord": (0, (1,)), "PMemRespell": (0, (1, 2))}
_LIT = r"(?:0[xX][0-9a-fA-F]+|\d+)"
_B = r"(?<![A-Za-z0-9_'])"
CTOR_RE = re.compile(_B + r"(" + "|".join(sorted(set(SIZE_ARGS) | set(HALF_OPEN) | set(ADDR_ARGS) | set(BASE_OFF) |
                                                 set(LIST_ADDR_ARGS), key=len, reverse=True)) + r")(?![\w'])")
ARG_LIT_RE = re.compile(r"\(*\s*(?:ELit\s+)?\(?\s*(" + _LIT + r")(?:%\w+)?\s*\)*")
ZERO_BASE_RE = re.compile(r"\(?\s*ELit\s+\(?\s*0\s*\)?\s*\)?")
# `SA (ELit 0) k` and `{| a_base := ELit 0; a_off := k |}`: an absolute address k
ABS_ADDR_RE = re.compile(r"(?:\bSA\s+\(\s*ELit\s+0\s*\)\s+|\ba_base\s*:=\s*\(?\s*ELit\s+0\s*\)?\s*;\s*a_off\s*:=\s*)"
                         r"\(?\s*(" + _LIT + r")")
_PAIR = r"\(\s*" + _LIT + r"\s*,\s*" + _LIT + r"\s*\)"
PAIR_RE = re.compile(r"\(\s*(" + _LIT + r")\s*,\s*(" + _LIT + r")\s*\)")
PAIR_LIST_RE = re.compile(r"\[\s*" + _PAIR + r"(?:\s*;\s*" + _PAIR + r")*\s*\]")
HALF_OPEN_CMP_RE = re.compile(_B + r"(" + _LIT + r")\s*<=\s*[A-Za-z_][\w']*\s*<\s*(" + _LIT + r")(?![\w'])")
SPAN_SUB_RE = re.compile(r"\(\s*(" + _LIT + r")\s*-\s*(" + _LIT + r")\s*\)")
BRACKET_HALF_RE = re.compile(r"\[\s*(" + _LIT + r")\s*,\s*(" + _LIT + r")\s*\)")
# Address-named identifiers: an identifier that fully matches one of these carries addresses (hex) in its named
# groups; every other identifier's hex-looking runs are not addresses (`u_add64`, `already_added`).
IDENT_ADDR = (
    r"[WFDE]_(?P<pc>[0-9a-f]{4,})",                                         # fetch/decode/exec facts at a pc
    r"[A-Za-z][A-Za-z0-9]*_code_(?P<lo>[0-9a-f]{4,})_(?P<hi>[0-9a-f]{4,})",  # Ref_code_/Ub_code_/P0_code_ tables
    r"img_(?P<addr>[0-9a-f]{4,})_[0-9]+",                                   # image facts img_<addr>_<size>
)
# ZOracle tables (`Ltac2 Set ...ZOracle.zor_fail := fun k => (if Ltac2.Int.lt k 495591490 then ... Int.equal k N`):
# the integers compared against k, k2 or kind are goal hashes and codes, never addresses.
ZOR_SET_RE = re.compile(r"Ltac2\s+Set\s+[\w.']*\bzor_\w*\s*:=")
ZOR_ARG_RE = re.compile(r"\bInt\.\w+\s+[A-Za-z_][\w']*\s+\(?\s*-?(\d+)")
CMD_END_RE = re.compile(r"\.(?=\s|$)")
HEX4_RE = re.compile(r"[0-9a-fA-F]{4}")  # an identifier without 4 hex-digit characters in a row carries no hex part


class IdentHex:
    """Hex embedded in identifiers.  An identifier that fully matches an --ident-addr pattern is address-named: its
    named groups are addresses.  In any other identifier only --ident-hex runs are found, and they are reported for
    review, never as addresses."""

    def __init__(self, addr_pats, hex_re):
        self.addr = [re.compile(p) for p in addr_pats]
        for p in self.addr:
            if not p.groupindex:
                raise SystemExit(f"--ident-addr {p.pattern!r}: name the address parts with (?P<name>...) groups")
        self.hex = re.compile(hex_re)

    def parts(self, ident):
        """(address-named?, [(start, end, value)]) for the hex parts of one identifier."""
        for p in self.addr:
            m = p.fullmatch(ident)
            if m:
                return True, [(m.start(g), m.end(g), int(m.group(g), 16)) for g in p.groupindex if m.group(g)]
        return False, [(h.start(), h.end(), int(h.group(0), 16)) for h in self.hex.finditer(ident)]

    def sites(self, text):
        """The addresses named by the address-named identifiers in text, in order."""
        out = []
        for idm in IDENT_RE.finditer(text):
            named, ps = self.parts(idm.group(0))
            if named:
                out += [v for _, _, v in ps]
        return out


def num(s):
    return None if s.lower() == "none" else int(s, 0)


# ----------------------------------------------------------------------------------
# Rocq lexing: which character ranges are comments / strings
# ----------------------------------------------------------------------------------

def lex_regions(text):
    """Sorted [(start, end, kind)] for comment and string spans (kind 'comment'/'string')."""
    out = []
    i, n = 0, len(text)
    depth, cstart = 0, None
    while i < n:
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            if depth == 0:
                out.append((i, j + 1, "string"))
            i = j + 1
            continue
        if text.startswith("(*", i):
            if depth == 0:
                cstart = i
            depth += 1
            i += 2
            continue
        if depth and text.startswith("*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                out.append((cstart, i, "comment"))
            continue
        i += 1
    if depth:
        out.append((cstart, n, "comment"))
    return out


class Ctx:
    def __init__(self, text):
        self.regions = lex_regions(text)
        self.starts = [r[0] for r in self.regions]
        self.line_starts = [0] + [m.end() for m in re.finditer(r"\n", text)]

    def kind(self, pos):
        k = bisect.bisect_right(self.starts, pos) - 1
        if k >= 0 and pos < self.regions[k][1]:
            return self.regions[k][2]
        return "code"

    def line_col(self, pos):
        ln = bisect.bisect_right(self.line_starts, pos) - 1
        return ln + 1, pos - self.line_starts[ln] + 1


# ----------------------------------------------------------------------------------
# the map
# ----------------------------------------------------------------------------------

def parse_image(path):
    t = open(path).read()
    segs = [{"base": int(b, 0), "size": int(s, 0), "perms": p} for b, s, p in re.findall(
        r'seg_base\s*:=\s*(0[xX][0-9a-fA-F]+|\d+)%N;\s*seg_size\s*:=\s*(0[xX][0-9a-fA-F]+|\d+)%N;\s*'
        r'seg_perms\s*:=\s*"([^"]*)"', t)]
    pc = re.search(r"_init_pc\s*:\s*N\s*:=\s*(0[xX][0-9a-fA-F]+|\d+)%N", t)
    if not segs or not pc:
        raise SystemExit(f"{path}: no seg_base/seg_size/seg_perms records or init_pc found")
    return segs, int(pc.group(1), 0)


class Spans:
    """Sorted, non-overlapping [lo, hi) spans with payloads."""

    def __init__(self, items):
        self.items = sorted(items, key=lambda x: x[0])
        self.los = [x[0] for x in self.items]

    def find(self, v):
        k = bisect.bisect_right(self.los, v) - 1
        if k >= 0 and v < self.items[k][1]:
            return self.items[k]
        return None


def fde_table(elf):
    """Sorted [(start, size)] of every function in elf's .eh_frame_hdr search table (version 1; eh_frame_ptr pcrel
    sdata4, count udata4, table datarel sdata4; each FDE's pc_begin pcrel sdata4, checked against the table)."""
    hdr = next((r for r in elf.sections if r.name == ".eh_frame_hdr"), None)
    if hdr is None:
        raise SystemExit(f"{elf.path}: no .eh_frame_hdr section (numeral_map.py reads function starts from it)")
    b = elf.region_bytes(hdr)
    if tuple(b[:4]) != (1, 0x1B, 0x03, 0x3B):
        raise SystemExit(f"{elf.path}: .eh_frame_hdr version/encodings {[hex(x) for x in b[:4]]}, "
                         f"expected ['0x1', '0x1b', '0x3', '0x3b']")
    out = []
    for i in range(struct.unpack_from("<I", b, 8)[0]):
        loc, fde = (hdr.vaddr + x for x in struct.unpack_from("<ii", b, 12 + 8 * i))
        _, _, pc_begin, size = struct.unpack("<IIiI", elf.read(fde, 16))
        if fde + 8 + pc_begin != loc:
            raise SystemExit(f"{elf.path}: FDE {fde:#x} begins at {fde + 8 + pc_begin:#x}, but its .eh_frame_hdr "
                             f"entry says {loc:#x}")
        out.append((loc, size))
    return sorted(out)


def same_function(fns, a, b):
    """Whether a < b lie in one function of the sorted FDE list fns [(start, size)], b not being its start."""
    k = bisect.bisect_right(fns, (a, float("inf"))) - 1
    return k >= 0 and fns[k][0] <= a < b < fns[k][0] + fns[k][1]


def split_at(fns, starts, lo, hi):
    """[(function start or None, a, b)]: [lo, hi) cut at the bounds of the sorted functions fns [(start, size)]."""
    out, k = [], max(bisect.bisect_right(starts, lo) - 1, 0)
    while lo < hi:
        while k < len(fns) and fns[k][0] + fns[k][1] <= lo:
            k += 1
        if k < len(fns) and fns[k][0] <= lo:
            b = min(hi, fns[k][0] + fns[k][1])
            out.append((fns[k][0], lo, b))
        else:
            b = min(hi, fns[k][0]) if k < len(fns) else hi
            out.append((None, lo, b))
        lo = b
    return out


def pair_functions(code, old_fns, new_fns):
    """({OLD function start: NEW function start}, {OLD function start: why it pairs with none}).  code: matched code
    [(old_lo, old_hi, delta)].  An OLD function pairs with a NEW function when all of its matched code lands in that
    one NEW function and no other matched code (another OLD function's, or code outside every OLD function) does."""
    ostarts, nstarts = [s for s, _ in old_fns], [s for s, _ in new_fns]
    into, outof = defaultdict(set), defaultdict(set)  # OLD function -> the NEW functions its code lands in, and back
    for lo, hi, d in code:
        for o, a, b in split_at(old_fns, ostarts, lo, hi):
            for n, _, _ in split_at(new_fns, nstarts, a + d, b + d):
                if o is not None:
                    into[o].add(n)
                if n is not None:
                    outof[n].add(o)

    def names(xs, side):
        return ", ".join(f"{side} {x:#x}" if x is not None else f"code outside every {side} function"
                         for x in sorted(xs, key=lambda x: -1 if x is None else x))
    pairs, why = {}, {}
    for o in ostarts:
        ns = into.get(o)
        if not ns:
            why[o] = "none of its code is matched"
        elif len(ns) > 1 or None in ns:
            why[o] = "its code lands in " + names(ns, "NEW")
        elif outof[next(iter(ns))] != {o}:
            n = next(iter(ns))
            why[o] = f"NEW {n:#x} also holds code of " + names(outof[n] - {o}, "OLD")
        else:
            pairs[o] = next(iter(ns))
    return pairs, why


class Map:
    def __init__(self, m, args, label="the map"):
        if m.get("tool") != "elf_symbols":
            raise SystemExit(f"{label}: not an elf_symbols.py map")
        self.m = m
        self.runs = Spans([(r["old_lo"], r["old_hi"], r) for r in m["runs"]])
        self.amb = Spans([(r["old_lo"], r["old_hi"], r) for r in m["ambiguous"]])
        self.dele = Spans([(r["old_lo"], r["old_hi"], r) for r in m["deleted"]])
        self.osecs = Spans([(s["vaddr"], s["vaddr"] + s["size"], s) for s in m["old"]["sections"]])
        self.osegs = [(s["base"], s["base"] + s["size"], n, s["perms"])
                      for n, s in enumerate(m["old"]["image_segments"])]
        self.small = args.small
        self.shadow_off, self.shadow_scale = args.shadow_offset, args.shadow_scale
        self.brk_aslr, self.brk_window = args.brk_aslr, args.brk_window
        self.reach = args.reach
        self.tls = m.get("tls_anchor")
        # exact old addresses a code or pointer reference anchors (an object provably lives there)
        self.anchor_addrs = {a for s in m["data_sections"] for a, _ in s["anchor_points"]}
        # evidence per data section: anchors (and the section start), content-matched spans
        self.evidence = {}
        for s in m["data_sections"]:
            pts = sorted({s["old_vaddr"]} | {a for a, _ in s["anchor_points"]})
            self.evidence[(s["name"], s["old_vaddr"])] = (
                pts, Spans([(c["old_lo"], c["old_hi"], c) for c in s["content_runs"]]))
        # paired sections (name, order) for section-end mapping
        newsecs = defaultdict(list)
        for s in m["new"]["sections"]:
            newsecs[s["name"]].append(s)
        self.sec_end = {}
        seen = Counter()
        for s in m["old"]["sections"]:
            k = seen[s["name"]]
            seen[s["name"]] += 1
            if k < len(newsecs[s["name"]]):
                t = newsecs[s["name"]][k]
                self.sec_end.setdefault(s["vaddr"] + s["size"], set()).add(t["vaddr"] + t["size"])
        # geometry: exact values, and page indices of page-aligned ones
        self.geo = defaultdict(set)
        self.page = defaultdict(set)
        hull_lo, hull_hi = m["old"]["hull"]
        self.hull_hi, self.new_hull_hi = hull_hi, m["new"]["hull"][1]
        geo = list(m["geometry"])
        if self.brk_aslr is not None:
            geo.append({"name": "brk_aslr+hull.hi", "old": self.brk_aslr + hull_hi,
                        "new": self.brk_aslr + self.new_hull_hi})
        # values derived from the image geometry: the shadow length of the hull, the shadow-scaled image end and its
        # shadow byte (`SEGTOP / 8` bounds, the shadow of one past the image), and each segment's .hex string length
        # (elf-snapshot writes two characters per byte)
        for g in list(geo):
            if g["name"] == "hull.size" and self.shadow_off is not None:
                geo.append({"name": "hull.size>>shadow_scale", "old": g["old"] >> self.shadow_scale,
                            "new": g["new"] >> self.shadow_scale})
            if g["name"] == "hull.hi" and self.shadow_off is not None:
                geo.append({"name": "hull.hi>>shadow_scale", "old": g["old"] >> self.shadow_scale,
                            "new": g["new"] >> self.shadow_scale})
                geo.append({"name": "shadow(hull.hi)", "old": self.shadow_off + (g["old"] >> self.shadow_scale),
                            "new": self.shadow_off + (g["new"] >> self.shadow_scale)})
            if g["name"].endswith(".size") and g["name"].startswith("seg"):
                geo.append({"name": g["name"][:-5] + ".hexlen", "old": 2 * g["old"], "new": 2 * g["new"]})
        self.constants = set(args.not_address)
        self.dec_constants = set(args.not_address_decimal)
        for g in geo:
            if g["old"] >= self.small:
                self.geo[g["old"]].add((g["name"], g["new"]))
            if g["old"] % rvelf.PAGE == 0 and g["new"] % rvelf.PAGE == 0 and not g["name"].endswith(".size") \
                    and g["old"] >> 12:
                self.page[g["old"] >> 12].add((g["name"], g["new"] >> 12))
        # the binaries themselves: instruction starts, words at fetch sites
        self.old_elf = rvelf.Elf(args.old_elf or m["old"]["path"])
        self.new_elf = rvelf.Elf(args.new_elf or m["new"]["path"])
        for e, d in ((self.old_elf, m["old"]), (self.new_elf, m["new"])):
            if rvelf.sha256(e.path) != d["sha256"]:
                raise SystemExit(f"{e.path}: sha256 differs from the one recorded in {label}")
        self.old_code = [rvelf.Code(self.old_elf.region_bytes(r), r.vaddr)
                         for r in self.old_elf.sections if r.kind == "exec"]
        self._word_sites = None
        self._auipc = None
        self._new_code = None
        # function starts from both FDE tables; each OLD function paired with a NEW one through the matched code (the
        # code runs, and the single-candidate isolated matches elf_symbols lists as ambiguous code)
        self.old_fns, self.new_fns = fde_table(self.old_elf), fde_table(self.new_elf)
        exec_secs = Spans([(s["old_vaddr"], s["old_vaddr"] + s["old_size"], s) for s in m["exec_sections"]])
        code = [(r["old_lo"], r["old_hi"], r["delta"]) for r in m["runs"] if r["kind"] == "code"]
        code += [(r["old_lo"], r["old_hi"], r["candidates"][0]) for r in m["ambiguous"]
                 if len(r["candidates"]) == 1 and exec_secs.find(r["old_lo"])]
        self.func_new, self.func_unpaired = pair_functions(code, self.old_fns, self.new_fns)

    def check_images(self, img_old, img_new):
        for (segs, pc), side in ((img_old, "old"), (img_new, "new")):
            if segs is None:
                continue
            mine = [{"base": s["base"], "size": s["size"], "perms": s["perms"]}
                    for s in self.m[side]["image_segments"]]
            if segs != mine or pc != self.m[side]["entry"]:
                raise SystemExit(f"--image-{side} does not describe the map's {side} binary:\n  image {segs} "
                                 f"init_pc {pc:#x}\n  ELF   {mine} entry {self.m[side]['entry']:#x}")

    # ---- address lookup ------------------------------------------------------------
    def old_code_at(self, pc):
        for c in self.old_code:
            k = c.index_of(pc)
            if k is not None:
                return c, k
        return None, None

    def map_addr(self, v):
        """('mapped', new) | ('ambiguous', why) | ('unmappable', why) | None if not in a mapped section."""
        r = self.runs.find(v)
        if r:
            return "mapped", v + r[2]["delta"], r[2]["kind"]
        a = self.amb.find(v)
        if a:
            return "ambiguous", None, (f"ambiguous region {a[0]:#x}..{a[1]:#x}, candidate deltas "
                                       f"{[hex(c) for c in a[2]['candidates']]}: {a[2]['why']}")
        d = self.dele.find(v)
        if d:
            rep = d[2].get("replaced_by")
            return "unmappable", None, (f"deleted code {d[0]:#x}..{d[1]:#x}" +
                                        (f" (replaced by NEW {rep[0]:#x}..{rep[1]:#x})" if rep else ""))
        return None

    def func_entry(self, v, today, why):
        """None, or (class func-entry, status, NEW function start, note) for an OLD function start v whose NEW start
        differs from `today`, the code map's value for v (None when it gives none; why: its reason)."""
        n = self.func_new.get(v)
        if n is None or n == today:
            return None
        note = f"OLD function {v:#x} -> NEW function {n:#x} (FDE starts); the code map gives " + (
            f"{today:#x}, where OLD's first instruction moved ({why} run)" if today is not None else f"no value: {why}")
        if v % rvelf.PAGE == 0 and n % rvelf.PAGE:
            return "func-entry", "review", n, ("page-aligned value whose NEW function start is not page-aligned: a "
                                               "page/chunk boundary rather than an address?; " + note)
        return "func-entry", "mapped", n, note

    def segment(self, v):
        for lo, hi, n, perms in self.osegs:
            if lo <= v < hi:
                return f"seg{n}:{perms}"
        return ""

    def classify(self, v, radix, boundary=True, addr=False):
        """-> (cls, status, new_value, note).  status: mapped | review | unmappable | ambiguous | none.
        boundary=False: v is known to START an interval, so it is not also read as one past the object below.
        addr=True: v sits in a field the engines type as an address (ADDR_ARGS, ...): a decimal needs no anchor, and
        v is the address itself, not one past the object below."""
        if radix == 10 and v in self.dec_constants:
            return "constant", "kept", None, "listed in --not-address-decimal: a decimal constant, never relocated"
        small = radix == 10 and v < self.small
        res = self._classify(v)
        cls, status, new, note = res
        if small and cls != "not-address":
            return cls, "review", new, f"decimal below --small {self.small:#x} (size/count?); " + note
        if status != "mapped":
            return res
        if radix == 10 and new != v and not addr and cls in ANCHORED_CLASSES and not self.anchored(v, cls):
            return cls, "review", new, ("decimal with no code/pointer reference anchoring this exact address: sizes, "
                                        "counts and bounds are written in decimal; " + note)
        if boundary and not addr and cls in BOUNDARY_CLASSES:
            prev = self.map_addr(v - 1)
            if prev and prev[0] == "mapped" and prev[1] + 1 != new:
                return cls, "review", new, (f"at an object boundary: as an address -> {new:#x}; as one past the end of "
                                            f"the object below (an interval end) -> {prev[1] + 1:#x}; " + note)
        return res

    def classify_end(self, v, radix, addr=False):
        """Classification of v as the END of a half-open interval: one past OLD v - 1, so it moves with the object it
        closes, map(v - 1) + 1, never with the object that starts at v."""
        start = self.classify(v, radix, boundary=False, addr=addr)
        if start[0] in ("geometry", "section-end", "brk-relative", "brk-aslr", "constant", "not-address"):
            return start  # exact image constants (hull.hi, section ends) already are one-past values
        cls, status, new, note = self.classify(v - 1, radix, boundary=False, addr=addr)
        if cls == "not-address":
            return start
        got = self.map_addr(v - 1)
        if cls == "exec" and got and got[0] == "mapped":  # a code range end: v - 1 is inside the last instruction
            return cls, "mapped", got[1] + 1, f"interval end: one past OLD {v - 1:#x} -> {got[1] + 1:#x}"
        if new is None:
            return cls, status, None, f"interval end (one past OLD {v - 1:#x}): " + note
        return cls, status, new + 1, f"interval end: one past OLD {v - 1:#x} -> {new + 1:#x}; " + note

    def auipc_result(self, v):
        """None, or (OLD pcs of the auipc instructions whose result pc + hi20<<12 is v, the set of results of the
        rc.2 auipc at each mapped pc; None where the pc does not map to an auipc writing the same register)."""
        if self._auipc is None:
            self._auipc = defaultdict(list)
            for c in self.old_code:
                for pc, raw, ln in zip(c.pcs, c.raws, c.lens):
                    if ln == 4 and raw & 0x7F == rvelf.OP_AUIPC:
                        self._auipc[(pc + rvelf.sext(raw & 0xFFFFF000, 32)) % (1 << 64)].append((pc, (raw >> 7) & 31))
        sites = self._auipc.get(v)
        if not sites:
            return None
        news = set()
        for pc, rd in sites:
            got, nr = self.map_addr(pc), None
            if got and got[0] == "mapped":
                c, k = self._new_code_at(got[1])
                if c is not None:
                    raw = c.raws[k]
                    if c.lens[k] == 4 and raw & 0x7F == rvelf.OP_AUIPC and (raw >> 7) & 31 == rd:
                        nr = (got[1] + rvelf.sext(raw & 0xFFFFF000, 32)) % (1 << 64)
            news.add(nr)
        return [pc for pc, _ in sites], news

    def anchored(self, v, cls):
        """Whether a code or pointer reference anchors an object at exactly v (for a shadow byte: at the address
        it shadows)."""
        if cls in ("shadow", "tls-shadow"):
            v = (v - self.shadow_off) << self.shadow_scale
        return v in self.anchor_addrs

    def _classify(self, v):
        if v in self.constants:
            return "constant", "kept", None, "listed in --not-address: a constant, never relocated"
        dtp = self.dtp_window(v)
        alt = self.map_addr(v) if dtp is not None else None
        if dtp is not None and not (alt and alt[0] == "mapped" and alt[1] == dtp[1]):
            # a DTP-biased TLS pointer (dtv[1] = tp + 0x800, ASan's thread TLS begin/end, ...) moves with td,
            # but an ordinary .bss object can sit at the same old address and move with the .bss run.  A code or
            # pointer reference to that address proves the object exists, not what a given literal means
            # (opendnp3 both 0x715680 is a code-referenced object AND the TLS pointer that moves to 0x7154c8),
            # so the use site decides, always.  When both readings give the same NEW value there is nothing to
            # decide and the literal is classified as usual.
            off, nt = dtp
            run = f"{alt[1]:#x} = {alt[1]} ({alt[2]} run)" if alt and alt[0] == "mapped" else \
                (alt[2] if alt else "no map entry")
            obj = "; a code/pointer reference anchors an object at exactly this address" \
                if v in self.anchor_addrs else "; no reference anchors an object here"
            return "tls-dtp", "ambiguous", None, (
                f"OLD td + {DTP_OFFSET:#x} + {off:#x} (DTP-biased TLS window; tp = td + {self.tls['tp_offset']:#x}): "
                f"as a TLS pointer (moves with tp) -> {nt:#x} = {nt}; as a plain .bss address -> {run}{obj}; "
                f"decide by the use site")
        geo = self.geo.get(v)
        addr = self.osecs.find(v)
        if geo:
            news = {n for _, n in geo}
            names = ",".join(sorted(n for n, _ in geo))
            if len(news) > 1:
                return "geometry", "ambiguous", None, f"{names} move differently: {sorted(hex(x) for x in news)}"
            new = news.pop()
            note = names
            if addr:
                alt = self.map_addr(v)
                if alt and alt[0] == "mapped" and alt[1] != new:
                    if any(n in DERIVED_GEOMETRY for n, _ in geo):
                        # a value derived from the image end can coincide with a code/data address: never pick one
                        return "geometry", "ambiguous", None, (
                            f"{names} -> {new:#x}; ALSO an address in {addr[2]['name']} that maps to {alt[1]:#x}: "
                            f"decide per use site (a `/ 8` bound or a shadow formula is the geometry reading)")
                    note += f"; ALSO an address in {addr[2]['name']} that would map to {alt[1]:#x}"
            return "geometry", "mapped", new, note
        pg = self.page.get(v)
        if pg and any(n != v for _, n in pg):  # a page index that does not move needs no attention
            news = sorted({n for _, n in pg})
            return "page-index", "review", news[0] if len(news) == 1 else None, \
                f"page index of {','.join(sorted(n for n, _ in pg))} -> {[hex(x) for x in news]}"
        if addr:
            sec = addr[2]
            cls = sec["kind"]
            got = self.map_addr(v)
            if got is None:
                return cls, "unmappable", None, f"{sec['name']}: no map entry"
            status, new, why = got
            if why == "tls-object":
                return "tls-cell", "mapped", new, self.tls_note(v)
            if cls == "exec":
                c, k = self.old_code_at(v)
                if c is None:
                    return cls, "review", new, f"{sec['name']}: not an instruction start in OLD"
                entry = self.func_entry(v, new, why)
                if entry:
                    return entry
                ret = self.return_slot(v, c, k)
                if ret and ret[0] != new:
                    return "return-addr", "mapped", ret[0], ret[1] + (
                        f"; the code map gives {new:#x} ({why} run), the NEW instruction that OLD's moved to"
                        if new is not None else f"; the code map gives no value: {why}")
            if status == "mapped":
                if v % rvelf.PAGE == 0 and new % rvelf.PAGE:
                    return cls, "review", new, (f"{sec['name']}: page-aligned value whose mapped value is not "
                                                f"page-aligned: a page/chunk boundary rather than an address?")
                if cls != "exec":
                    far = self.too_far(sec, v)
                    if far:
                        return cls, "review", new, f"{sec['name']} ({why}): {far}"
                # only a data/bss section ending where this data/bss section starts competes
                # (a __stop_<section> symbol); code or TLS template ends do not
                prev = self.osecs.find(v - 1)
                ends = self.sec_end.get(v, set()) - {new} \
                    if cls in ("data", "bss") and prev and prev[2]["kind"] in ("data", "bss") else set()
                if ends:
                    return cls, "ambiguous", None, (
                        f"{sec['name']} start maps to {new:#x}, but the value is also one past the end of the "
                        f"preceding OLD section, which maps to {sorted(hex(e) for e in ends)}: decide per use site")
                return cls, "mapped", new, f"{sec['name']} ({why})"
            return cls, status, None, f"{sec['name']}: {why}"
        if v in self.sec_end:
            news = self.sec_end[v]
            if len(news) == 1:
                return "section-end", "mapped", next(iter(news)), "one past the end of an OLD section"
            return "section-end", "ambiguous", None, "ends of several sections"
        if self.hull_hi <= v < self.hull_hi + self.brk_window:
            return "brk-relative", "mapped", self.new_hull_hi + (v - self.hull_hi), \
                f"image end {self.hull_hi:#x} + {v - self.hull_hi:#x}"
        if self.brk_aslr is not None:
            x = v - self.brk_aslr
            if self.hull_hi <= x < self.hull_hi + self.brk_window:
                return "brk-aslr", "mapped", self.brk_aslr + self.new_hull_hi + (x - self.hull_hi), \
                    f"brk ASLR {self.brk_aslr:#x} + image end + {x - self.hull_hi:#x}"
        if self.shadow_off is not None and v >= self.shadow_off:
            a = (v - self.shadow_off) << self.shadow_scale
            sec = self.osecs.find(a)
            if sec and sec[2]["kind"] != "exec":
                g = 1 << self.shadow_scale
                lo, hi = self.map_addr(a), self.map_addr(a + g - 1)
                if lo and hi and lo[0] == hi[0] == "mapped" and lo[1] - a == hi[1] - a - g + 1 \
                        and (lo[1] - a) % g == 0:
                    if lo[2] == "tls-object":
                        return "tls-shadow", "mapped", v + ((lo[1] - a) >> self.shadow_scale), \
                            f"shadow of {a:#x}: {self.tls_note(a)}"
                    far = self.too_far(sec[2], a)
                    if far:
                        return "shadow", "review", v + ((lo[1] - a) >> self.shadow_scale), \
                            f"shadow of {a:#x} ({sec[2]['name']}): {far}"
                    return "shadow", "mapped", v + ((lo[1] - a) >> self.shadow_scale), \
                        f"shadow of {a:#x} ({sec[2]['name']})"
                return "shadow", "ambiguous", None, \
                    f"shadow of {a:#x} ({sec[2]['name']}): granule not mapped by one multiple-of-{g} delta"
        seg = self.segment(v)
        if seg:
            return "image-pad", "review", None, f"inside {seg} but outside every section"
        if U64_MAX >= v >= 1 << 63:
            # ~a = 2^64-1-a, as in a `2^64-1-T` bound a compiler folds; a 2^k-1 complement is a mask, not an address
            a = U64_MAX - v
            if a >= self.small and a & (a + 1):
                cls, status, new, note = self._classify(a)
                if status == "mapped" and new is not None and new != a:
                    return "complement", "review", U64_MAX - new, (
                        f"64-bit complement ~{a:#x} of {cls} {a:#x} -> ~{new:#x}; or a mask/constant: decide per use "
                        f"site; {note}")
        return "not-address", "none", None, ""

    def _new_code_at(self, pc):
        if self._new_code is None:
            self._new_code = [rvelf.Code(self.new_elf.region_bytes(r), r.vaddr)
                              for r in self.new_elf.sections if r.kind == "exec"]
        for c in self._new_code:
            k = c.index_of(pc)
            if k is not None:
                return c, k
        return None, None

    def return_slot(self, v, c, k):
        """None, or (NEW return address, note) when OLD v is the instruction right after a call (jal/jalr/c.jalr
        writing ra) inside the same function: a return address moves with the call, map(call) + its length, even where
        NEW inserts code right after the call (a check on the returned value) and OLD's next instruction moved further
        down.  A function that starts right after a call (a noreturn call ending the function before) is not a return
        address, in OLD or in NEW."""
        if k == 0 or c.pcs[k - 1] + c.lens[k - 1] != v or not is_call(c.raws[k - 1], c.lens[k - 1]):
            return None
        call = c.pcs[k - 1]
        if not same_function(self.old_fns, call, v):
            return None
        got = self.map_addr(call)
        if not got or got[0] != "mapped":
            return None
        nc, nk = self._new_code_at(got[1])
        if nc is None or not is_call(nc.raws[nk], nc.lens[nk]):
            return None
        ret = got[1] + nc.lens[nk]
        if not same_function(self.new_fns, got[1], ret):
            return None
        return ret, f"return address after the call at OLD {call:#x} -> NEW call {got[1]:#x} + {nc.lens[nk]} = {ret:#x}"

    def dtp_window(self, v):
        """(offset from td + 0x800, NEW value) if v is a possible DTP-biased TLS pointer, else None.
        elf_symbols's tls_anchor.dtp: the window [td + 0x800, tp + 0x800 + PT_TLS memsz], end included (tp + 0x800 + memsz
        is the one-past-end TLS pointer, ASan's thread TLS end, opendnp3 asan 0x719354; td + 0x800 is ASan's thread
        TLS begin, opendnp3 asan 0x719278 / both 0x7155b8), and the delta of tp, which these pointers move with
        (dtv[1] = tp + 0x800: NEW tp + 0x800, not NEW builtin_tls + 0x800 + 200 when td = builtin_tls + 8).
        Everything in it is flagged, never rewritten, so the wider bounds only add review rows."""
        if not self.tls:
            return None
        if "dtp" not in self.tls:
            raise SystemExit("the map's tls_anchor has no dtp window (made before td and builtin_tls were told "
                             "apart): regenerate it with the current elf_symbols.py")
        w = self.tls["dtp"]
        if w and w["old_lo"] <= v <= w["old_hi_incl"]:
            return v - w["old_lo"], v + w["delta"]
        return None

    def tls_note(self, v):
        """Which musl TLS cell v is, from elf_symbols's tls_anchor layout, e.g. `td+0xc8 = tp+0x0 (struct pthread)`."""
        o = self.tls["old"]
        blk = o["static_block"]
        if blk <= v < blk + 0x38:  # elf_symbols TLS_BLOCK
            return f"static block (__thread_list_lock, main_tls) +{v - blk:#x}"
        mem = o["builtin_tls"]
        if o["in_builtin"]:
            img = o["tp"] + o["tls_offset"]
            if o["td"] <= v < o["tp"]:
                return f"td+{v - o['td']:#x} = tp{v - o['tp']:+#x} (struct pthread; moves with td)"
            if img <= v < img + o["tls_memsz"]:
                return f"tp+{v - o['tp']:#x} (TLS image byte {v - img:#x}; follows the PT_TLS template's map)"
            if o["dtv"] <= v < o["dtv"] + 8 * (o["tls_cnt"] + 1):
                return f"dtv+{v - o['dtv']:#x} (dtv[{(v - o['dtv']) // 8}] at builtin_tls + tls_size - " \
                       f"{8 * (o['tls_cnt'] + 1):#x}; moves with the dtv)"
            if v == o["tp"]:
                return "tp (the thread pointer; moves with td)"
        return f"builtin_tls+{v - mem:#x}"

    def too_far(self, sec, v):
        """Why an interpolated data mapping is too weak to apply, or None.  Content-matched bytes and
        addresses within --reach above a code/pointer reference (or the section start) are fine;
        anything deeper inside an unreferenced stretch may be a size that only looks like an address."""
        ev = self.evidence.get((sec["name"], sec["vaddr"]))
        if ev is None:
            return None
        pts, content = ev
        if content.find(v):
            return None
        k = bisect.bisect_right(pts, v) - 1
        d = v - pts[k]
        if d <= self.reach:
            return None
        return (f"interpolated {d:#x} bytes past the nearest reference ({pts[k]:#x}), beyond --reach "
                f"{self.reach:#x}: may be a size, not an address")

    # ---- fetch-site words ------------------------------------------------------------
    def word_sites(self, w):
        if self._word_sites is None:
            self._word_sites = defaultdict(list)
            for c in self.old_code:
                for pc, raw in zip(c.pcs, c.raws):
                    self._word_sites[raw].append(pc)
        return self._word_sites.get(w, [])

    def site_check(self, pc, length):
        """Describe old/new words at an OLD fetch site."""
        ow = self.old_elf.read(pc, length)
        got = self.map_addr(pc)
        if not got or got[0] != "mapped":
            return None, f"site {pc:#x}: {got[2] if got else 'not in a mapped region'}"
        npc = got[1]
        nw = self.new_elf.read(npc, length)
        o = int.from_bytes(ow, "little") if ow else None
        n = int.from_bytes(nw, "little") if nw else None
        return (o, n), f"site {pc:#x}->{npc:#x}: word {o:#0{2 + 2 * length}x} -> {n:#0{2 + 2 * length}x}" + \
            (" SAME" if o == n else " CHANGED")


# ----------------------------------------------------------------------------------
# scanning
# ----------------------------------------------------------------------------------

def is_call(raw, length):
    """jal ra / jalr ra (4 bytes) or c.jalr (2 bytes): the instructions that write a return address into ra."""
    if length == 4:
        return raw & 0x7F in (rvelf.OP_JAL, rvelf.OP_JALR) and (raw >> 7) & 31 == 1
    return raw & 0xF07F == 0x9002 and bool(raw & 0x0F80)


def eval_closed(expr):
    """Value of a closed integer expression over hex/decimal literals, + - * / and parentheses (`/` is Z.div:
    floor division), or None when it is anything else."""
    if not re.fullmatch(r"[0-9a-fA-FxX+\-*/()\s]+", expr) or \
            re.search(r"[a-fA-FxX]", re.sub(r"0[xX][0-9a-fA-F]+", "", expr)):
        return None
    try:
        v = eval(expr.replace("/", "//"), {"__builtins__": {}})  # noqa: S307 -- the regex admits only arithmetic
    except (SyntaxError, ZeroDivisionError, TypeError, NameError):
        return None
    return v if isinstance(v, int) else None


def change_with(path, text, ctx, edits, rows, stats):
    """`change (EXPR) with D`, EXPR closed arithmetic and D its value in OLD: D is recomputed from EXPR after this
    file's rewrites (D itself is rarely an address; written in decimal it is never rewritten on its own).  Replaces
    any edit and report row of D's literal; returns the edits sorted by position."""
    out = list(edits)
    for m in CHANGE_WITH_RE.finditer(text):
        if ctx.kind(m.start()) != "code":
            continue
        lit_d = m.group("d")
        old_e, old_d = eval_closed(m.group("e")), lit_value(lit_d)
        if old_e is None or old_e != old_d:
            continue
        es, ee = m.span("e")
        parts, last = [], es
        for s, e, new in sorted(x for x in out if es <= x[0] < ee):
            parts += [text[last:s], new]
            last = e
        new_e = eval_closed("".join(parts) + text[last:ee])
        if new_e is None or new_e == old_d:
            continue
        ds, de = m.span("d")
        newlit = fmt_like(lit_d, new_e)
        out = [x for x in out if x[0] != ds] + [(ds, de, newlit)]
        ln, col = ctx.line_col(ds)
        rows[:] = [r for r in rows if not (r[0] == path and r[1] == ln and r[2] == col)]
        rows.append((path, ln, col, "code", lit_d, f"{old_d:#x}", "derived", "mapped", newlit,
                     f"value of `{' '.join(m.group('e').split())}` after rewriting its literals"))
        stats["class:derived"] += 1
        stats["rewritten:code"] += 1
    return sorted(out)


def fmt_like(orig, new):
    if orig[:2].lower() == "0x":
        digits = orig[2:]
        upper = any(c in "ABCDEF" for c in digits)
        s = f"{new:X}" if upper else f"{new:x}"
        if len(digits) > len(f"{int(digits, 16):x}"):  # zero-padded original keeps its width
            s = s.rjust(len(digits), "0")
        return orig[:2] + s
    return str(new)


def term_args(text, pos, k):
    """[(start, end)] of up to k Rocq application arguments after pos: a balanced (), [] or {} group, or a token."""
    out, n, i = [], len(text), pos
    while len(out) < k:
        while i < n and text[i] in " \t\r\n":
            i += 1
        if i >= n or text[i] in ")]};,|":
            break
        j = i
        if text[i] in "([{":
            depth = 0
            while j < n:
                if text[j] in "([{":
                    depth += 1
                elif text[j] in ")]}":
                    depth -= 1
                    if depth == 0:
                        j += 1
                        break
                j += 1
        else:
            while j < n and text[j] not in " \t\r\n()[]{};,":
                j += 1
        out.append((i, j))
        i = j
    return out


def lit_value(s):
    return int(s, 16) if s[:2].lower() == "0x" else int(s)


def literal_roles(text, ctx):
    """({position of a literal: (role, where)}, {positions of literals in address positions}).  Role `size` for a
    size/length argument of a known constructor (SIZE_ARGS), `start`/`end` for the bounds of a half-open interval:
    KImg/PMemRespell, `lo <= x < hi`, `[lo, hi)`, `(hi - lo)` and each pair in a sorted list of disjoint (lo, hi)
    pairs (PRISTINE lists).  Address positions: ADDR_ARGS, BASE_OFF offsets on an (ELit 0) base, `SA (ELit 0) k`,
    `a_base := ELit 0; a_off := k`."""
    roles, addrs = {}, set()
    for m in CTOR_RE.finditer(text):
        if ctx.kind(m.start()) != "code":
            continue
        name = m.group(1)
        size, half, addr = SIZE_ARGS.get(name, ()), HALF_OPEN.get(name, ()), ADDR_ARGS.get(name, ())
        base, offs = BASE_OFF.get(name, (None, ()))
        lpos = LIST_ADDR_ARGS.get(name)
        args = term_args(text, m.end(), max(size + half + addr + offs + ((base,) if base is not None else ()) +
                                            ((lpos,) if lpos is not None else ())) + 1)
        if lpos is not None and lpos < len(args):
            addrs.update(e.start(1) for e in ELIT_RE.finditer(text, *args[lpos]))
        if name in BOOL_AT_1 and (len(args) < 2 or text[args[1][0]:args[1][1]] not in ("true", "false")):
            continue
        lits = []
        for a, b in args:
            if text[b - 1] == "." and b - 1 > a:  # the command's final `.` sticks to a last bare token
                b -= 1
            lm = ARG_LIT_RE.fullmatch(text, a, b)
            lits.append((lm.start(1), lit_value(lm.group(1))) if lm else None)
        for i in size:
            if i < len(lits) and lits[i]:
                roles[lits[i][0]] = ("size", name)
        for i in addr:
            if i < len(lits) and lits[i]:
                addrs.add(lits[i][0])
        if base is not None and base < len(args) and ZERO_BASE_RE.fullmatch(text, *args[base]):
            addrs.update(lits[i][0] for i in offs if i < len(lits) and lits[i])
        if half and max(half) < len(lits):
            lo, hi = lits[half[0]], lits[half[1]]
            if lo and hi and lo[1] < hi[1]:
                roles[lo[0]] = ("start", name)
                roles[hi[0]] = ("end", name)
    for m in ABS_ADDR_RE.finditer(text):
        addrs.add(m.start(1))
    for m in PAIR_LIST_RE.finditer(text):
        pairs = [(lit_value(p.group(1)), lit_value(p.group(2)), p.start(1), p.start(2))
                 for p in PAIR_RE.finditer(text, m.start(), m.end())]
        if all(lo < hi for lo, hi, _, _ in pairs) and all(a[1] <= b[0] for a, b in zip(pairs, pairs[1:])):
            for _, _, p, q in pairs:
                roles[p] = ("start", "a sorted list of disjoint (lo, hi) intervals")
                roles[q] = ("end", "a sorted list of disjoint (lo, hi) intervals")
    for m in HALF_OPEN_CMP_RE.finditer(text):
        roles[m.start(1)] = ("start", "lo <= x < hi")
        roles[m.start(2)] = ("end", "lo <= x < hi")
    for m in BRACKET_HALF_RE.finditer(text):
        if lit_value(m.group(1)) < lit_value(m.group(2)):
            roles[m.start(1)] = ("start", "[lo, hi)")
            roles[m.start(2)] = ("end", "[lo, hi)")
    for m in SPAN_SUB_RE.finditer(text):
        if lit_value(m.group(1)) > lit_value(m.group(2)):
            roles.setdefault(m.start(1), ("end", "(hi - lo)"))
            roles.setdefault(m.start(2), ("start", "(hi - lo)"))
    return roles, addrs


def scan_file(path, text, mp, args, ih, rows, stats):
    ctx = Ctx(text)
    decode_spans = []
    for m in DECODE_RE.finditer(text):
        if ctx.kind(m.start()) != "code":
            continue
        decode_spans.append((m.start("args"), m.end("args")))
        ctor, w = m.group("ctor"), m.group("w")
        named = ih.sites(w)
        site = named[-1] if named else None
        ln, col = ctx.line_col(m.start("ctor"))
        note = ""
        need = ctor in ADDR_CTORS
        if site is not None:
            c, k = mp.old_code_at(site)
            if c is None:
                note = f"site {site:#x} is not an OLD instruction start"
                need = True
            else:
                sens = c.sens[k]
                words, desc = mp.site_check(site, c.lens[k])
                note = desc + (f"; OLD insn is address-dependent ({sens[0]})" if sens else "")
                if sens or words is None or words[0] != words[1]:
                    need = True
        else:
            note = "fetch site not named by the term"
        stats["decode-terms"] += 1
        if need:
            rows.append((path, ln, col, "code", f"{ctor}{m.group('args')}", "", "decode-arg",
                         "decode-check-needed", "", note))
            stats["decode-check-needed"] += 1
    decode_spans.sort()
    dstarts = [s for s, _ in decode_spans]

    def in_decode(pos):
        k = bisect.bisect_right(dstarts, pos) - 1
        return k >= 0 and pos < decode_spans[k][1]

    zor = set()  # positions of ZOracle table keys
    for m in ZOR_SET_RE.finditer(text):
        if ctx.kind(m.start()) != "code":
            continue
        end = next((e.start() for e in CMD_END_RE.finditer(text, m.end()) if ctx.kind(e.start()) == "code"),
                   len(text))
        zor.update(a.start(1) for a in ZOR_ARG_RE.finditer(text, m.end(), end))
    roles, addr_pos = literal_roles(text, ctx)
    edits = []
    auipc_line = {}  # line start -> whether the line mentions auipc (lines can be 700 KB long: scan each once)
    line_sites = {}  # line start -> the addresses its address-named identifiers name

    def has_auipc(ls, ln):
        if ls not in auipc_line:
            auipc_line[ls] = "auipc" in text[ls:ctx.line_starts[ln] if ln < len(ctx.line_starts) else len(text)]
        return auipc_line[ls]

    for m in LIT_RE.finditer(text):
        lit = m.group(1)
        pos = m.start(1)
        kind = ctx.kind(pos)
        v = int(lit, 16) if lit[:2].lower() == "0x" else int(lit)
        radix = 16 if lit[:2].lower() == "0x" else 10
        ln, col = ctx.line_col(pos)
        stats[f"literals:{kind}"] += 1
        if in_decode(pos):
            continue  # reported once per decode term
        line_start = ctx.line_starts[ln - 1]
        if OPCODE_CTX_RE.search(text, max(line_start, pos - 64), pos):
            if line_start not in line_sites:
                line_sites[line_start] = ih.sites(text[line_start:ctx.line_starts[ln] if ln < len(ctx.line_starts)
                                                       else len(text)])
            note = opcode_note(line_sites[line_start], v, mp)
            rows.append((path, ln, col, kind, lit, f"{v:#x}", "opcode", "opcode-check-needed", "", note))
            stats["opcode-check-needed"] += 1
            continue
        if radix == 10 and len(lit) > 1 and lit[0] == "0":
            continue  # zero-padded digits (objdump words in comments such as `00077517`), not a decimal number
        role, addr = roles.get(pos), pos in addr_pos
        cls, status, new, note = (mp.classify_end(v, radix, addr) if role and role[0] == "end" else
                                  mp.classify(v, radix, boundary=not (role and role[0] == "start"), addr=addr))
        if cls == "not-address":
            continue
        size = role and role[0] == "size" and cls != "geometry"  # a size can be an image size (hull.size): recomputed
        if pos in zor or size:
            what = ("ZOracle table key (a goal hash compared in an Ltac2 zor_* table)" if pos in zor else
                    f"size/length argument of {role[1]}")
            rows.append((path, ln, col, kind, lit, f"{v:#x}", "zor-key" if pos in zor else "size", "kept", "",
                         f"{what}, never an address; read as an address it would be {cls} {status}"
                         + (f" -> {new:#x}" if new is not None else "")))
            stats[f"kept:{kind}"] += 1
            stats["class:" + ("zor-key" if pos in zor else "size")] += 1
            continue
        if role and role[0] != "size":
            note = f"{role[0]} of a half-open interval ({role[1]}); " + note
        elif role:
            note = f"size/length argument of {role[1]}, equal to an image size constant; " + note
        if addr:
            note = "in an address field; " + note
        # an address field names a memory cell or range, never a page value held in a register
        au = mp.auipc_result(v) if cls != "constant" and not addr else None
        if au and not (status == "mapped" and au[1] == {new}):
            pcs, news = au
            known = sorted(x for x in news if x is not None)
            note = (f"equals the OLD auipc result (pc + hi20<<12) of {len(pcs)} auipc(s) (first at {pcs[0]:#x}): as "
                    f"that auipc's result -> {', '.join(hex(x) for x in known) or 'no rc.2 auipc at the mapped pc'}"
                    f"{' or unmapped' if None in news and known else ''}; as {cls} ({status}"
                    + (f" -> {new:#x}" if new is not None else "") + f"): {note}; decide per use")
            cls, status, new = "auipc-result?", "review", (known[0] if len(known) == 1 and None not in news else None)
        if status == "mapped" and cls in REWRITABLE:
            if kind == "string":
                status = "review"
                note = "inside a string literal; " + note
            elif radix == 10 and cls in ("exec", "func-entry", "return-addr"):
                status = "review"
                note = "decimal value inside code (PCs are written in hex); " + note
            elif new != v and (v & (v + 1) == 0 or v & (v - 1) == 0):
                status = "review"
                note = "2^k or 2^k-1: more likely a mask/size than an address; " + note
            elif kind == "code" and has_auipc(line_start, ln):
                status = "review"
                note = "on an auipc step: likely the auipc result pc+hi20<<12, which moves with the auipc; " + note
        newlit = fmt_like(lit, new) if new is not None else ""
        if status == "mapped":
            if new != v:
                edits.append((m.start(1), m.end(1), newlit))
                stats[f"rewritten:{kind}"] += 1
            else:
                stats[f"unchanged:{kind}"] += 1
        else:
            stats[f"{status}:{kind}"] += 1
        stats[f"class:{cls}"] += 1
        rows.append((path, ln, col, kind, lit, f"{v:#x}", cls, status, newlit, note))
    # identifiers carrying hex: only address-named ones carry addresses
    for idm in IDENT_RE.finditer(text):
        if HEX4_RE.search(idm.group(0)):
            rows += ident_rows(path, idm.group(0), ctx.kind(idm.start()), mp, ih, stats,
                               lambda s, base=idm.start(): ctx.line_col(base + s))
    return change_with(path, text, ctx, edits, rows, stats)


def ident_rows(path, ident, kind, mp, ih, stats, line_col):
    """Report rows for the hex parts of one identifier (or file name).  An address-named identifier's parts are
    classified as addresses (`ident-mapped` = the value a consumer may rename to); any other identifier's
    hex-looking parts are only `ident-review`."""
    out = []
    named, parts = ih.parts(ident)
    for s, _, v in parts:
        cls, status, new, note = mp.classify(v, 16)
        if cls == "not-address":
            continue
        if not named:
            status = "review"
            note = ("the identifier matches no --ident-addr pattern (not address-named): its hex-looking part is not "
                    "an address; " + note)
        ln, col = line_col(s)
        out.append((path, ln, col, kind, ident, f"{v:#x}", "ident:" + cls, "ident-" + status,
                    f"{new:x}" if new is not None else "", note))
        stats["ident"] += 1
        stats[f"ident:{status}"] += 1
    return out


def opcode_note(line_sites, v, mp):
    for site in line_sites:
        c, k = mp.old_code_at(site)
        if c is not None:
            words, desc = mp.site_check(site, c.lens[k])
            ok = "" if words is None or words[0] == v else f" (literal {v:#x} != OLD word!)"
            return desc + ok
    sites = mp.word_sites(v)
    if not sites:
        return "word not found at any OLD instruction start"
    same = changed = unm = 0
    for pc in sites:
        got = mp.map_addr(pc)
        if not got or got[0] != "mapped":
            unm += 1
            continue
        nw = mp.new_elf.read(got[1], 4 if v & 3 == 3 else 2)
        if nw is not None and int.from_bytes(nw, "little") == v:
            same += 1
        else:
            changed += 1
    return (f"site not named on the line; word occurs at {len(sites)} OLD insn starts"
            f" (first {sites[0]:#x}): same at mapped NEW pc {same}, changed {changed}, unmappable {unm}")


def collect(paths):
    out = []
    for p in paths:
        if os.path.isdir(p):
            for d, _, fs in os.walk(p):
                out += [os.path.join(d, f) for f in sorted(fs) if f.endswith(".v")]
        else:
            out.append(p)
    return sorted(set(out))


def make_parser():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+", help=".v files or directories (searched for *.v)")
    ap.add_argument("--map", required=True, help="map JSON from elf_symbols.py OLD NEW")
    ap.add_argument("--image-old", help="OLD image .v (elf-snapshot); checked against the map's OLD segments")
    ap.add_argument("--image-new", help="NEW image .v; checked against the map's NEW segments")
    ap.add_argument("--old-elf", help="OLD ELF path if it moved since elf_symbols ran (sha256 still checked)")
    ap.add_argument("--new-elf", help="NEW ELF path if it moved since elf_symbols ran (sha256 still checked)")
    ap.add_argument("--report", nargs="?", const="-", metavar="TSV",
                    help="write the TSV report (default stdout)")
    ap.add_argument("--rewrite", metavar="OUTDIR", help="write rewritten copies under OUTDIR")
    ap.add_argument("--root", help="path the copies under OUTDIR are relative to (default: common dir of FILES)")
    ap.add_argument("--small", type=lambda s: int(s, 0), default=0x10000,
                    help="decimal literals below this are treated as sizes/counts: never rewritten (default 0x10000)")
    ap.add_argument("--ident-addr", action="append", metavar="REGEX",
                    help="an address-named identifier: a regex that must match the whole identifier, with a named "
                         "group (?P<name>...) around each hex address part (at least 4 digits); repeat for several. "
                         "Only these identifiers get `ident-mapped` rows (default: IDENT_ADDR in numeral_map.py: "
                         + "; ".join(IDENT_ADDR) + "; giving the flag replaces the list, so pass the defaults too to "
                         "extend it)")
    ap.add_argument("--ident-hex", default=r"(?<=_)[0-9a-f]{4,}(?![0-9A-Za-z])",
                    help="regex for hex-looking runs inside any other identifier or file name, reported as "
                         "`ident-review` (default: an underscore-led run of >=4 lowercase hex digits)")
    ap.add_argument("--shadow-offset", type=num, default=0x7fff8000,
                    help="ASan shadow offset (default 0x7fff8000; 'none' disables the shadow class)")
    ap.add_argument("--shadow-scale", type=int, default=3)
    ap.add_argument("--brk-aslr", type=num, default=0x80000000,
                    help="brk ASLR window added to the image end (default 0x80000000; 'none' disables)")
    ap.add_argument("--brk-window", type=lambda s: int(s, 0), default=0x10000,
                    help="values up to this far past the image end (or brk ASLR + image end) move with the end")
    ap.add_argument("--not-address", type=lambda s: [int(x, 0) for x in s.split(",") if x],
                    default=list(NOT_ADDRESS),
                    help="comma-separated values that are constants, never addresses, even when they fall in a "
                         "section or look like a shadow byte (default: NOT_ADDRESS in numeral_map.py: "
                         + ",".join(f"{v:#x}" for v in NOT_ADDRESS) + "; pass the full list to extend it)")
    ap.add_argument("--not-address-decimal", type=lambda s: [int(x) for x in s.split(",") if x],
                    default=list(NOT_ADDRESS_DECIMAL),
                    help="comma-separated constants that are never addresses when written in decimal (the same "
                         "value in hex is classified as usual; default: NOT_ADDRESS_DECIMAL in numeral_map.py: "
                         + ",".join(str(v) for v in NOT_ADDRESS_DECIMAL) + "; pass the full list to extend it)")
    ap.add_argument("--reach", type=lambda s: int(s, 0), default=0x1000,
                    help="a data/bss address mapped by interpolation (no content match) is only rewritten when it "
                         "lies at most this far above a code/pointer reference or its section start "
                         "(default 0x1000); deeper ones are listed for review")
    return ap


def main():
    ap = make_parser()
    args = ap.parse_args()
    if not args.report and not args.rewrite:
        ap.error("give --report and/or --rewrite")
    mp = Map(json.load(open(args.map)), args, args.map)
    mp.check_images(parse_image(args.image_old) if args.image_old else (None, None),
                    parse_image(args.image_new) if args.image_new else (None, None))
    ih = IdentHex(args.ident_addr or IDENT_ADDR, args.ident_hex)
    files = collect(args.files)
    root = args.root or (os.path.commonpath([os.path.dirname(os.path.abspath(f)) for f in files]))
    rows, stats = [], Counter()
    for f in files:
        text = open(f, encoding="utf-8").read()
        rel = os.path.relpath(os.path.abspath(f), root)
        for idm in IDENT_RE.finditer(os.path.basename(f)):
            got = ident_rows(rel, idm.group(0), "filename", mp, ih, Counter(), lambda s: (0, 0))
            stats["filename"] += len(got)
            rows += got
        edits = scan_file(rel, text, mp, args, ih, rows, stats)
        if args.rewrite:
            out = []
            last = 0
            for s, e, new in edits:
                out.append(text[last:s])
                out.append(new)
                last = e
            out.append(text[last:])
            dst = os.path.join(args.rewrite, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            with open(dst, "w", encoding="utf-8") as fh:
                fh.write("".join(out))
    if args.report:
        fh = sys.stdout if args.report == "-" else open(args.report, "w")
        print("file\tline\tcol\tcontext\tliteral\tvalue\tclass\tstatus\tnew\tnote", file=fh)
        for r in rows:
            print("\t".join(str(x) for x in r), file=fh)
        if fh is not sys.stdout:
            fh.close()
    print_summary(stats, rows, len(files), sys.stderr if args.report == "-" else sys.stdout, mp)


def print_summary(stats, rows, nfiles, out, mp):
    p = lambda *a: print(*a, file=out)  # noqa: E731
    p(f"remap: {nfiles} files")
    lits = {k.split(':')[1]: v for k, v in stats.items() if k.startswith("literals:")}
    p(f"  numeric literals scanned: {lits}")
    for ctxk in ("code", "comment", "string"):
        parts = [f"{s} {stats[f'{s}:{ctxk}']}"
                 for s in ("rewritten", "unchanged", "kept", "review", "ambiguous", "unmappable")
                 if stats[f"{s}:{ctxk}"]]
        if parts:
            p(f"  in {ctxk}: " + ", ".join(parts))
    p("  by class: " + ", ".join(f"{k[6:]} {v}" for k, v in sorted(stats.items()) if k.startswith("class:")))
    moved = sum(1 for o, n in mp.func_new.items() if (mp.map_addr(o) or (None, None))[1] != n)
    p(f"  function starts (FDE tables): {len(mp.old_fns)} OLD, {len(mp.func_new)} paired with a NEW function, {moved} "
      f"of those not where the code map puts them (class func-entry); {len(mp.func_unpaired)} unpaired (the code "
      f"map's reading kept)" + "".join(f"\n    unpaired OLD {o:#x}: {w}" for o, w in sorted(mp.func_unpaired.items())))
    p(f"  opcode-check-needed {stats['opcode-check-needed']}, decode terms {stats['decode-terms']} "
      f"(decode-check-needed {stats['decode-check-needed']}), identifier-embedded hex {stats['ident']} "
      f"({', '.join(f'{k[6:]} {v}' for k, v in sorted(stats.items()) if k.startswith('ident:'))}), "
      f"file names {stats['filename']}")
    review = [r for r in rows if r[7] in ("review", "ambiguous", "unmappable")]
    if review:
        p(f"  needs a human ({len(review)}):")
        for r in review[:60]:
            p(f"    {r[0]}:{r[1]}:{r[2]} [{r[3]}] {r[4]} {r[6]} {r[7]} {r[8]}  {r[9]}")
        if len(review) > 60:
            p(f"    ... {len(review) - 60} more in the report")


if __name__ == "__main__":
    main()
