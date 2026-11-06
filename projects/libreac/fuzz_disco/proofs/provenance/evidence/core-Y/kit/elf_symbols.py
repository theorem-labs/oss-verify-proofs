#!/usr/bin/env python3
"""elf_symbols.py OLD.elf NEW.elf -o map.json

Align two builds of the same statically linked RISC-V (RV64GC) program and
write an old->new address map.

Code: the executable sections are decoded by linear sweep and diffed as
instruction sequences.  Before the diff every address-dependent immediate is
masked (auipc/jal/branch/c.j/c.beqz/c.bnez offsets and the 12-bit immediate of
an auipc's %pcrel_lo partner), so code that only moved compares equal.
Matched instructions become constant-delta runs; unmatched old instructions are
deleted regions, unmatched new ones inserted regions.

Data: sections are paired by name.  PROGBITS content is diffed byte-wise with
8-byte pointer words masked.  Every matched auipc+lo12 pair and every matched
data pointer is an exact old->new anchor; bss/tbss (no content) is mapped by
interpolating between anchors, and an address range is only mapped when its
content and the anchors around it agree on one delta.  Everything else is
reported as ambiguous with the candidate deltas.

Writes JSON (-o) and prints a human summary on stdout.
"""

import argparse
import bisect
import difflib
import json
import os
import struct
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rvelf  # noqa: E402

sys.setrecursionlimit(10000)

SMALL_GAP = 400_000       # gaps up to la*lb this size go straight to difflib
MIN_CODE_RUN = 3          # shorter matched code blocks whose delta matches no neighbour are "weak"
MIN_DATA_RUN = 16         # content blocks shorter than this many bytes are ignored
PTR_SENTINEL = b"\xa5P\x7fT\x00R\xc3\x99"


# ----------------------------------------------------------------------------------
# sequence alignment: patience diff on unique k-grams, difflib for small gaps
# ----------------------------------------------------------------------------------

def _unique_kgram_pairs(A, alo, ahi, B, blo, bhi, k):
    ca, pa = Counter(), {}
    for i in range(alo, ahi - k + 1):
        g = A[i:i + k]
        ca[g] += 1
        pa[g] = i
    cb, pb = Counter(), {}
    for j in range(blo, bhi - k + 1):
        g = B[j:j + k]
        if g in ca and ca[g] == 1:
            cb[g] += 1
            pb[g] = j
    return sorted((pa[g], pb[g]) for g, c in cb.items() if c == 1)


def _lis(pairs):
    """Longest chain of pairs increasing in both coordinates (pairs sorted by i)."""
    tails, tails_idx, prev = [], [], [None] * len(pairs)
    for n, (_, j) in enumerate(pairs):
        p = bisect.bisect_left(tails, j)
        if p == len(tails):
            tails.append(j)
            tails_idx.append(n)
        else:
            tails[p] = j
            tails_idx[p] = n
        prev[n] = tails_idx[p - 1] if p else None
    out, n = [], tails_idx[-1] if tails_idx else None
    while n is not None:
        out.append(pairs[n])
        n = prev[n]
    return out[::-1]


def _align(A, alo, ahi, B, blo, bhi, ks, out):
    n = 0
    while alo + n < ahi and blo + n < bhi and A[alo + n] == B[blo + n]:
        n += 1
    if n:
        out.append((alo, blo, n))
        alo += n
        blo += n
    m = 0
    while ahi - m > alo and bhi - m > blo and A[ahi - m - 1] == B[bhi - m - 1]:
        m += 1
    tail = (ahi - m, bhi - m, m) if m else None
    ahi -= m
    bhi -= m
    la, lb = ahi - alo, bhi - blo
    if la and lb:
        if la * lb <= SMALL_GAP:
            sm = difflib.SequenceMatcher(None, A[alo:ahi], B[blo:bhi], autojunk=False)
            for i, j, c in sm.get_matching_blocks():
                if c:
                    out.append((alo + i, blo + j, c))
        else:
            for k in ks:
                if k > min(la, lb):
                    continue
                chain = _lis(_unique_kgram_pairs(A, alo, ahi, B, blo, bhi, k))
                if chain:
                    ca, cb = alo, blo
                    for i, j in chain:
                        if i < ca or j < cb:
                            continue
                        _align(A, ca, i, B, cb, j, ks, out)
                        out.append((i, j, k))
                        ca, cb = i + k, j + k
                    _align(A, ca, ahi, B, cb, bhi, ks, out)
                    break
    if tail:
        out.append(tail)


def align(A, B, ks):
    """Matching blocks [(i, j, n)] in increasing order, adjacent blocks merged."""
    raw = []
    _align(A, 0, len(A), B, 0, len(B), ks, raw)
    merged = []
    for i, j, n in raw:
        if merged and merged[-1][0] + merged[-1][2] == i and merged[-1][1] + merged[-1][2] == j:
            pi, pj, pn = merged[-1]
            merged[-1] = (pi, pj, pn + n)
        else:
            merged.append((i, j, n))
    return merged


# ----------------------------------------------------------------------------------
# code
# ----------------------------------------------------------------------------------

def pair_regions(old_regs, new_regs):
    """Pair regions by name (in order for repeated names)."""
    by_name = defaultdict(list)
    for r in new_regs:
        by_name[r.name].append(r)
    pairs, used = [], set()
    for r in old_regs:
        cands = [x for x in by_name.get(r.name, []) if id(x) not in used]
        if cands:
            used.add(id(cands[0]))
            pairs.append((r, cands[0]))
        else:
            pairs.append((r, None))
    unpaired_new = [r for r in new_regs if id(r) not in used]
    return pairs, unpaired_new


def fill_equal_gaps(blocks, ta, tb):
    """Match a gap whose old and new sides have the same length and the same masked tokens.

    The identity pass can leave such gaps: an unchanged `jal f` whose target f now starts
    with inserted code resolves to different identities on the two sides, yet it is the
    same instruction at the same place.  It is matched here and its target disagreement
    shows up in the xref check instead."""
    out = []
    ai = bj = 0
    for i, j, n in blocks + [(len(ta), len(tb), 0)]:
        if i - ai == j - bj > 0 and ta[ai:i] == tb[bj:j]:
            out.append((ai, bj, i - ai))
        if n:
            out.append((i, j, n))
        ai, bj = i + n, j + n
    merged = []
    for i, j, n in out:
        if merged and merged[-1][0] + merged[-1][2] == i and merged[-1][1] + merged[-1][2] == j:
            merged[-1] = (merged[-1][0], merged[-1][1], merged[-1][2] + n)
        else:
            merged.append((i, j, n))
    return merged


CODE_TARGET_KINDS = ("jal", "branch", "c.j", "c.bxxz", "lo12")


def identity_tokens(code, resolve):
    """Tokens where a code-pointing instruction also carries the identity of
    its target (resolve(target) -> NEW address, or None to keep it masked)."""
    tok = list(code.tok)
    for k, s in enumerate(code.sens):
        if s is not None and s[0] in CODE_TARGET_KINDS:
            ident = resolve(s[1])
            if ident is not None:
                tok[k] |= (ident + 1) << 41
    return tuple(tok)


def map_code(old_elf, new_elf, res, prev=None):
    """Align every executable region pair.  Fills res; returns per-region state.

    prev: the code runs of an earlier pass.  When given, jumps, branches and
    auipc pairs that point into code must also agree on WHICH code they point
    to (old target mapped through prev == new target), which keeps repetitive
    instrumented code (rows of `jal __asan_report_*`) from aligning to the
    wrong copy."""
    states = []
    olds = [r for r in old_elf.sections if r.kind == "exec"]
    news = [r for r in new_elf.sections if r.kind == "exec"]
    pairs, unpaired_new = pair_regions(olds, news)
    for r in unpaired_new:
        res["inserted"].append({"new_lo": r.vaddr, "new_hi": r.end, "section": r.name,
                                "bytes": r.size, "why": "section only in NEW"})
    if prev is not None:
        fwd = Lookup(prev)
        image = Lookup([{"old_lo": r["new_lo"], "old_hi": r["new_lo"] + r["old_hi"] - r["old_lo"], "delta": 0}
                        for r in prev])
    for ro, rn in pairs:
        co = rvelf.Code(old_elf.region_bytes(ro), ro.vaddr)
        if rn is None:
            res["deleted"].append({"old_lo": ro.vaddr, "old_hi": ro.end, "section": ro.name,
                                   "bytes": ro.size, "insns": len(co.pcs), "why": "section only in OLD"})
            continue
        cn = rvelf.Code(new_elf.region_bytes(rn), rn.vaddr)
        if prev is None:
            ta, tb = tuple(co.tok), tuple(cn.tok)
        else:
            ta, tb = identity_tokens(co, fwd), identity_tokens(cn, image)
        blocks = fill_equal_gaps(align(ta, tb, (16, 8, 4, 2, 1)), co.tok, cn.tok)
        states.append((ro, rn, co, cn, blocks))
        # weak blocks: short, with a delta neither neighbour has
        deltas = [cn.pcs[j] - co.pcs[i] for i, j, _ in blocks]
        weak = set()
        for b, (i, j, n) in enumerate(blocks):
            nb = [deltas[x] for x in (b - 1, b + 1) if 0 <= x < len(blocks)]
            if n < MIN_CODE_RUN and deltas[b] not in nb:
                weak.add(b)
        ai = bj = 0
        for b, (i, j, n) in enumerate(blocks + [(len(co.pcs), len(cn.pcs), 0)]):
            gap_o = (ai, i)
            gap_n = (bj, j)
            if gap_o[0] < gap_o[1] or gap_n[0] < gap_n[1]:
                ol = co.pcs[gap_o[0]] if gap_o[0] < len(co.pcs) else ro.end
                oh = co.pcs[gap_o[1]] if gap_o[1] < len(co.pcs) else ro.end
                nl = cn.pcs[gap_n[0]] if gap_n[0] < len(cn.pcs) else rn.end
                nh = cn.pcs[gap_n[1]] if gap_n[1] < len(cn.pcs) else rn.end
                if oh > ol:
                    res["deleted"].append({"old_lo": ol, "old_hi": oh, "section": ro.name, "bytes": oh - ol,
                                           "insns": gap_o[1] - gap_o[0], "new_at": nl,
                                           "replaced_by": [nl, nh] if nh > nl else None})
                if nh > nl:
                    res["inserted"].append({"new_lo": nl, "new_hi": nh, "section": rn.name, "bytes": nh - nl,
                                            "insns": gap_n[1] - gap_n[0], "old_at": ol,
                                            "replaces": [ol, oh] if oh > ol else None})
            if n:
                lo = co.pcs[i]
                hi = co.pcs[i + n - 1] + co.lens[i + n - 1]
                run = {"old_lo": lo, "old_hi": hi, "new_lo": cn.pcs[j], "delta": cn.pcs[j] - lo,
                       "kind": "code", "section": ro.name, "insns": n}
                if b in weak:
                    run["kind"] = "code-weak"
                    res["ambiguous"].append({"old_lo": lo, "old_hi": hi, "section": ro.name,
                                             "candidates": [cn.pcs[j] - lo],
                                             "why": f"isolated {n}-instruction match inside changed code"})
                else:
                    res["runs"].append(run)
            ai, bj = i + n, j + n
    return states


SLOT_SECTIONS = (".got", ".data.rel.ro")   # address tables: a slot loaded by code holds an address
LD = (0x3, 3)                               # opcode LOAD, funct3 3: ld


def code_anchors_and_changes(states, res, old_elf, new_elf):
    """Collect old->new address anchors from matched address-forming
    instructions and list instructions whose encoding changed.

    A matched `auipc; ld rd, %pcrel_lo(slot)` pair whose slot lies in .got or .data.rel.ro also anchors the
    slot's contents: the old word -> the new word (kind "got").  The code map pairs the slots, so this works
    where the byte-diff of a table of masked pointers cannot."""
    anchors = []
    oslots = [r for r in old_elf.sections if r.name in SLOT_SECTIONS and r.offset is not None]
    nslots = [r for r in new_elf.sections if r.name in SLOT_SECTIONS and r.offset is not None]
    (ohl, ohh), (nhl, nhh) = old_elf.hull(), new_elf.hull()

    def slot_word(elf, regions, addr):
        if addr % 8 or not any(r.vaddr <= addr and addr + 8 <= r.end for r in regions):
            return None
        return struct.unpack("<Q", elf.read(addr, 8))[0]

    seen_slots = set()
    for ro, rn, co, cn, blocks in states:
        for i, j, n in blocks:
            for x in range(n):
                a, b = i + x, j + x
                so, sn = co.sens[a], cn.sens[b]
                if so is None or sn is None or so[0] != sn[0]:
                    continue
                if so[0] not in ("auipc", "lo12x"):  # a lone auipc gives only a page; lo12x targets are unproven
                    anchors.append((so[1], sn[1], so[0], co.pcs[a]))
                w = co.raws[a]
                if so[0] == "lo12" and co.lens[a] == 4 and (w & 0x7F, (w >> 12) & 7) == LD \
                        and (so[1], sn[1]) not in seen_slots:
                    seen_slots.add((so[1], sn[1]))
                    wo, wn = slot_word(old_elf, oslots, so[1]), slot_word(new_elf, nslots, sn[1])
                    if wo is not None and wn is not None and ohl <= wo < ohh and nhl <= wn < nhh:
                        anchors.append((wo, wn, "got", co.pcs[a]))
                if co.raws[a] != cn.raws[b]:
                    # an auipc's own value is pc + (hi20 << 12), a page that carries the pc's low bits, not
                    # an object address: it is recorded as old_page/new_page so it is never read as a target
                    # (the object is the partner's lo12 entry, whose partner_pc names this auipc)
                    tk = ("old_page", "new_page") if so[0] == "auipc" else ("old_target", "new_target")
                    res["pcrel_changed"].append({
                        "old_pc": co.pcs[a], "new_pc": cn.pcs[b], "kind": so[0],
                        "old_word": co.raws[a], "new_word": cn.raws[b], "len": co.lens[a],
                        tk[0]: so[1], tk[1]: sn[1],
                        "partner_pc": co.pcs[co.partner[a]] if co.partner[a] is not None else None})
    return anchors


# ----------------------------------------------------------------------------------
# data
# ----------------------------------------------------------------------------------

def masked_bytes(elf, r, hull):
    blob = bytearray(elf.region_bytes(r))
    lo, hi = hull
    ptrs = []
    start = (-r.vaddr) % 8
    for o in range(start, len(blob) - 7, 8):
        v = struct.unpack_from("<Q", blob, o)[0]
        if lo <= v < hi:
            blob[o:o + 8] = PTR_SENTINEL
            ptrs.append((o, v))
    return bytes(blob), dict(ptrs)


def map_data(old_elf, new_elf, res, code_anchors):
    olds = [r for r in old_elf.sections if r.kind != "exec"]
    news = [r for r in new_elf.sections if r.kind != "exec"]
    pairs, unpaired_new = pair_regions(olds, news)
    for r in unpaired_new:
        res["inserted"].append({"new_lo": r.vaddr, "new_hi": r.end, "section": r.name, "bytes": r.size,
                                "why": "section only in NEW"})
    ohull, nhull = old_elf.hull(), new_elf.hull()
    content = {}  # old region name -> [(old_lo, old_hi, delta)]
    anchors = list(code_anchors)
    for ro, rn in pairs:
        if rn is None or ro.offset is None or rn.offset is None:
            continue
        a, pa = masked_bytes(old_elf, ro, ohull)
        b, pb = masked_bytes(new_elf, rn, nhull)
        runs = []
        for i, j, n in align(a, b, (32, 16, 8)):
            if n < MIN_DATA_RUN:
                continue
            runs.append((ro.vaddr + i, ro.vaddr + i + n, (rn.vaddr + j) - (ro.vaddr + i)))
            for o in range(i + ((-(ro.vaddr + i)) % 8), i + n - 7, 8):
                if o in pa and (o - i + j) in pb:
                    anchors.append((pa[o], pb[o - i + j], "ptr", ro.vaddr + o))
        content[id(ro)] = runs

    # Code anchors (auipc+lo12 targets) are exact.  A matched "pointer" word may be an integer that
    # merely looks like an address, so pointer anchors are only admitted where they confirm the
    # code-anchor map or pick one of its candidate deltas.
    code_by_addr, ptr_by_addr = defaultdict(set), defaultdict(set)
    for old, new, kind, site in anchors:
        (ptr_by_addr if kind == "ptr" else code_by_addr)[old].add(new - old)
    res["anchor_stats"] = Counter()
    res["anchor_conflicts"] = []

    def points(ro, table, evidence):
        """Single-delta anchor points of one section.  An address whose references disagree is dropped and
        recorded: evidence "code" (code lo12 targets / code-paired .got slots disagree: a real conflict) or
        "pointer" (content-diff pointer words disagree; decided_by is the code delta there, if any)."""
        pts = []
        for addr in sorted(x for x in table if ro.vaddr <= x < ro.end):
            ds = table[addr]
            if len(ds) > 1:
                c = {"old": addr, "deltas": sorted(ds), "section": ro.name, "evidence": evidence}
                if evidence == "pointer":
                    cd = code_by_addr.get(addr, set())
                    c["decided_by"] = next(iter(cd)) if len(cd) == 1 else None
                res["anchor_conflicts"].append(c)
                continue
            pts.append((addr, next(iter(ds))))
        return pts

    for ro, rn in pairs:
        if rn is None:
            res["deleted"].append({"old_lo": ro.vaddr, "old_hi": ro.end, "section": ro.name,
                                   "bytes": ro.size, "why": "section only in OLD"})
            continue
        cruns = content.get(id(ro), [])
        cpts = points(ro, code_by_addr, "code")
        stage1 = section_intervals(ro, rn, cpts, cruns)
        s1 = Spans1(stage1)
        code_at = dict(cpts)
        ppts, rejected = [], 0
        for addr, d in points(ro, ptr_by_addr, "pointer"):
            if addr in code_at:
                continue
            iv = s1.find(addr)
            if iv and ((iv[2] == "mapped" and iv[3] == d) or (iv[2] == "ambiguous" and d in iv[5])):
                ppts.append((addr, d))
            else:
                rejected += 1
        pts = sorted(cpts + ppts)
        res["anchor_stats"][ro.name] = {"code": len(cpts), "pointer": len(ppts), "pointer_rejected": rejected}
        intervals = section_intervals(ro, rn, pts, cruns)
        for lo, hi, status, delta, kind, cands, why in intervals:
            if status == "mapped":
                res["runs"].append({"old_lo": lo, "old_hi": hi, "new_lo": lo + delta, "delta": delta,
                                    "kind": kind, "section": ro.name})
            else:
                res["ambiguous"].append({"old_lo": lo, "old_hi": hi, "section": ro.name,
                                         "candidates": sorted(cands), "why": why})
        # an address whose code references disagree means two things (typically the end of one object and the
        # start of the next, separated in NEW): the value itself is ambiguous, the bytes after it follow the map
        for c in res["anchor_conflicts"]:
            if c["evidence"] == "code" and ro.vaddr <= c["old"] < ro.end:
                res["runs"] = carve(res["runs"], c["old"], c["old"] + 1)
                res["ambiguous"] = carve(res["ambiguous"], c["old"], c["old"] + 1)
                res["ambiguous"].append({"old_lo": c["old"], "old_hi": c["old"] + 1, "section": ro.name,
                                         "candidates": c["deltas"],
                                         "why": "code references disagree on this address (CONFLICT)"})
        res["data_sections"].append({
            "name": ro.name, "kind": ro.kind, "old_vaddr": ro.vaddr, "old_size": ro.size,
            "new_vaddr": rn.vaddr, "new_size": rn.size, "shift": rn.vaddr - ro.vaddr,
            "content_runs": [{"old_lo": a, "old_hi": b, "delta": d} for a, b, d in cruns],
            "anchors": len(pts), "anchor_points": [[a, d] for a, d in pts]})


class Spans1:
    """Interval lookup over section_intervals() output."""

    def __init__(self, ivs):
        self.ivs = ivs
        self.los = [iv[0] for iv in ivs]

    def find(self, v):
        k = bisect.bisect_right(self.los, v) - 1
        if k >= 0 and v < self.ivs[k][1]:
            return self.ivs[k]
        return None


def section_intervals(ro, rn, pts, cruns):
    """Decide a delta (or ambiguity) for every old address of one section."""
    start_d, end_d = rn.vaddr - ro.vaddr, rn.end - ro.end
    real = pts  # [(addr, delta)] sorted
    raddrs = [a for a, _ in real]
    brk = {ro.vaddr, ro.end}
    for a, _ in real:
        brk.add(a)
        brk.add(a + 1)
    for a, b, _ in cruns:
        brk.add(a)
        brk.add(b)
    brk = sorted(x for x in brk if ro.vaddr <= x <= ro.end)
    crun_starts = [a for a, _, _ in cruns]
    anchor_at = dict(real)
    out = []
    for p, q in zip(brk, brk[1:]):
        if p in anchor_at:
            out.append((p, q, "mapped", anchor_at[p], "data-anchor", None, None))
            continue
        k = bisect.bisect_right(crun_starts, p) - 1
        dc = cruns[k][2] if k >= 0 and cruns[k][0] <= p and q <= cruns[k][1] else None
        x = bisect.bisect_right(raddrs, p) - 1
        y = bisect.bisect_left(raddrs, q)
        r_lo = real[x][1] if x >= 0 else None
        r_hi = real[y][1] if y < len(real) else None
        if dc is not None:
            if (r_lo is None and r_hi is None) or dc in (r_lo, r_hi):
                out.append((p, q, "mapped", dc, "data-content", None, None))
            else:
                out.append((p, q, "ambiguous", None, None, {dc, r_lo, r_hi} - {None},
                            "content delta disagrees with the code/pointer references around it"))
            continue
        d_lo = r_lo if r_lo is not None else start_d
        d_hi = r_hi if r_hi is not None else end_d
        if d_lo == d_hi:
            kind = "data-interp" if (r_lo is not None or r_hi is not None) else "section-shift"
            out.append((p, q, "mapped", d_lo, kind, None, None))
        elif x >= 0 and p == real[x][0] + 1 and real[x][0] % 8 == 0 and q % 8 == 0 and q - real[x][0] <= 8:
            # the rest of the 8-byte word that starts at a referenced address, up to the next referenced
            # (or section-ending) word: the same object as the reference below it
            out.append((p, q, "mapped", d_lo, "data-word", None, None))
        else:
            out.append((p, q, "ambiguous", None, None, {d_lo, d_hi},
                        "delta changes between the references below and above"))
    # merge neighbours with identical outcome
    merged = []
    for iv in out:
        if merged:
            m = merged[-1]
            if m[1] == iv[0] and m[2] == iv[2] and m[3] == iv[3] and (m[2] == "mapped" or m[5] == iv[5]):
                kind = m[4] if m[4] == iv[4] else "data-mixed"
                merged[-1] = (m[0], iv[1], m[2], m[3], kind, m[5], m[6])
                continue
        merged.append(iv)
    return merged


# ----------------------------------------------------------------------------------
# cross-checks, geometry, output
# ----------------------------------------------------------------------------------

class Lookup:
    def __init__(self, runs):
        self.runs = sorted(runs, key=lambda r: r["old_lo"])
        self.los = [r["old_lo"] for r in self.runs]

    def __call__(self, addr):
        k = bisect.bisect_right(self.los, addr) - 1
        if k >= 0 and addr < self.runs[k]["old_hi"]:
            return addr + self.runs[k]["delta"]
        return None


def xref_check(res, anchors):
    look = Lookup([r for r in res["runs"] if r["kind"] == "code"])
    exec_ranges = [(s["old_vaddr"], s["old_vaddr"] + s["old_size"]) for s in res["exec_sections"]]
    stats = Counter()
    bad = []
    for old, new, kind, site in anchors:
        if kind == "got" or not any(a <= old < b for a, b in exec_ranges):
            continue  # the check covers instruction references; slot contents are anchors only
        m = look(old)
        if m is None:
            stats["target-unmapped"] += 1
        elif m == new:
            stats["consistent"] += 1
        else:
            stats["INCONSISTENT"] += 1
            bad.append({"site": site, "kind": kind, "old_target": old, "new_target": new, "map": m})
    res["xref_check"] = {"counts": dict(stats), "inconsistent": bad}


def geometry(old_elf, new_elf):
    g = [{"name": "entry", "old": old_elf.entry, "new": new_elf.entry}]
    if old_elf.phdr_addr is not None and new_elf.phdr_addr is not None:
        g.append({"name": "phdr", "old": old_elf.phdr_addr, "new": new_elf.phdr_addr})
    so, sn = old_elf.image_segments(), new_elf.image_segments()
    if len(so) != len(sn):
        raise SystemExit(f"PT_LOAD count differs: {len(so)} vs {len(sn)}")
    for n, (a, b) in enumerate(zip(so, sn)):
        if a["perms"] != b["perms"]:
            raise SystemExit(f"PT_LOAD {n} permissions differ: {a['perms']} vs {b['perms']}")
        g.append({"name": f"seg{n}.base", "old": a["base"], "new": b["base"]})
        g.append({"name": f"seg{n}.end", "old": a["base"] + a["size"], "new": b["base"] + b["size"]})
        g.append({"name": f"seg{n}.size", "old": a["size"], "new": b["size"]})
    (ol, oh), (nl, nh) = old_elf.hull(), new_elf.hull()
    g += [{"name": "hull.lo", "old": ol, "new": nl}, {"name": "hull.hi", "old": oh, "new": nh},
          {"name": "hull.size", "old": oh - ol, "new": nh - nl}]
    return g


def describe(elf):
    return {"path": os.path.abspath(elf.path), "sha256": rvelf.sha256(elf.path), "entry": elf.entry,
            "phdr": elf.phdr_addr, "image_segments": elf.image_segments(),
            "load_segments": [{k: s[k] for k in ("vaddr", "filesz", "memsz", "flags")} for s in elf.segments],
            "sections": [r.to_json() for r in elf.sections], "hull": list(elf.hull())}


MAX_PASSES = 4


# ----------------------------------------------------------------------------------
# musl TLS object anchor
# ----------------------------------------------------------------------------------

# musl's static_init_tls, located by its builtin_tls bound (the same rule as the kit's scratch findtls.py and
# musltls/tools/gen_tls_walk.py find_tls):
#   v26:  addi a3, zero, 0x151                    builtin_tls is 0x150 bytes at static block + 0x38
#   rc.2: lui a1, 0x20 ... addiw a3, a1, 0xd1      builtin_tls is 0x200d0 bytes, its own .bss object
V26_BOUND = 0x15100693
RC2_LUI, RC2_ADDIW = 0x000205B7, 0x0D15869B
V26_MEM = 0x03860593         # addi a1, a2, 0x38: mem = builtin_tls = static block + 0x38
RET = 0x00008067
TLS_BLOCK = 0x38             # __thread_list_lock (8) + struct tls_module main_tls (48), as musltls/tools/tls_objmap.py
BTLS_SIZE = {"v26": 0x150, "rc2": 0x200D0}
BASE_REG = {"v26": 12, "rc2": 11}   # gen_tls_walk.py: the register holding the static block in the prologue
PTHREAD_SIZE = 200           # sizeof(struct pthread): tp = td + 200 (gen_tls_walk.py: tp - td)
MIN_TLS_ALIGN = 8            # musl: offsetof(struct builtin_tls, pt)
DTP_OFFSET = 0x800           # riscv: dtv[1] = tp + main_tls.offset + 0x800


def find_musl_tls(elf, codes):
    """static_init_tls's addresses from its auipc pairs: entry, static block, libc, builtin_tls (mem).
    None if the binary has no musl static_init_tls."""
    writable = [r for r in elf.sections if r.kind in ("data", "bss") and r.flags & rvelf.SHF_WRITE]
    hits = []
    for code in codes:
        raws = code.raws
        for k, w in enumerate(raws):
            if w == V26_BOUND:
                hits.append((code, k, "v26"))
            elif w == RC2_ADDIW and RC2_LUI in raws[max(0, k - 4):k]:
                hits.append((code, k, "rc2"))
    if not hits:
        return None
    found, why = [], []
    for code, kb, variant in hits:
        r = _musl_tls_at(code, kb, variant, writable)
        (found if isinstance(r, dict) else why).append(r)
    if len(found) != 1:
        raise SystemExit(f"{elf.path}: {len(found)} static_init_tls bound matches pass the structure check "
                         f"(candidates {[hex(c.pcs[k]) for c, k, _ in hits]}; rejected: {why})")
    return found[0]


def _musl_tls_at(code, kb, variant, writable):
    """The static_init_tls record for the bound at code index kb, or a reason string when the code around it is
    not static_init_tls (an unrelated `addi a3, zero, 0x151`, e.g. a call argument, also matches the v26 bound)."""
    ke = kb
    while ke >= 0 and not (code.lens[ke] == 4 and code.raws[ke] & 0xFFFFF == 0x10113 and code.raws[ke] >> 31):
        ke -= 1  # nearest preceding addi sp, sp, -N
    kr = kb
    while kr < len(code.raws) and code.raws[kr] != RET:
        kr += 1
    if ke < 0 or kr == len(code.raws):
        return f"{code.pcs[kb]:#x}: no prologue/ret"

    def addi_targets(lo, hi):
        for k in range(lo, hi):
            s, w = code.sens[k], code.raws[k]
            if s and s[0] == "lo12" and code.lens[k] == 4 and w & 0x707F == 0x13:  # addi rd, rX, %pcrel_lo
                yield k, (w >> 7) & 31, s[1]

    pro = list(addi_targets(ke, kb))
    base = next((t for _, rd, t in pro if rd == BASE_REG[variant]), None)
    libc = next((t for _, rd, t in pro if rd == 9), None)
    if base is None or libc is None:
        return f"{code.pcs[kb]:#x}: no static block / libc auipc pair after the prologue at {code.pcs[ke]:#x}"
    if variant == "v26":
        if V26_MEM not in code.raws[kb:kr]:
            return f"{code.pcs[kb]:#x}: v26 bound without `addi a1, a2, 0x38`"
        mem, mem_site = base + TLS_BLOCK, "addi a1, a2, 0x38 (static block + 0x38)"
    else:
        mem = next(((t, k) for k, rd, t in addi_targets(kb, kr)
                    if t not in (base, libc) and any(r.vaddr <= t < r.end for r in writable)), None)
        if mem is None:
            return f"{code.pcs[kb]:#x}: rc.2 bound without a builtin_tls auipc pair"
        mem, k = mem
        mem_site = f"auipc {code.pcs[code.partner[k]]:#x} + addi {code.pcs[k]:#x}"
    return {"variant": variant, "entry": code.pcs[ke], "end": code.pcs[kr] + 4, "bound_pc": code.pcs[kb],
            "static_block": base, "main_tls": base + 8, "libc": libc, "builtin_tls": mem,
            "builtin_tls_size": BTLS_SIZE[variant], "builtin_tls_from": mem_site}


def musl_tls_layout(x, elf):
    """Add the main thread's TLS layout to a find_musl_tls record: musl's static_init_tls and __copy_tls
    (TLS_ABOVE_TP, GAP_ABOVE_TP = 0) applied to the binary's PT_TLS, the formulas of the kit's survey params.py:
      tls_size = 2*8 + sizeof(struct pthread) + offset + size + align, rounded up to 8
      td  = mem + (-(mem + 200) & (align - 1))   mem = builtin_tls; td = mem unless tls_align > 8 (mosh: p_align 16)
      tp  = td + 200; the TLS image is copied to tp + offset; dtv[1] = tp + offset + 0x800
      dtv = mem + tls_size - 8 * (tls_cnt + 1)     hangs off mem and tls_size, not off td
    When tls_size exceeds builtin_tls, musl takes the block from mmap (v26) or refuses to start (rc.2): td, tp and
    dtv then have no image address (None)."""
    t = elf.tls
    image, memsz, palign = (t["vaddr"], t["memsz"], t["align"]) if t else (0, 0, 0)
    mask = (palign - 1) % (1 << 64)  # main_tls.align - 1, taken before musl raises the alignment to MIN_TLS_ALIGN
    size = (memsz + ((-memsz - image) & mask)) % (1 << 64)
    offset = image & mask
    align = max(palign, MIN_TLS_ALIGN)
    cnt = 1 if t else 0
    tls_size = (2 * 8 + PTHREAD_SIZE + offset + size + align + MIN_TLS_ALIGN - 1) & -MIN_TLS_ALIGN
    x.update(tls_vaddr=image, tls_memsz=memsz, tls_p_align=palign, tls_offset=offset, tls_image_size=size,
             tls_align=align, tls_cnt=cnt, tls_size=tls_size, in_builtin=tls_size <= x["builtin_tls_size"])
    mem = x["builtin_tls"]
    if x["in_builtin"]:
        td = mem + (-(mem + PTHREAD_SIZE) & (align - 1))
        x.update(td=td, tp=td + PTHREAD_SIZE, dtv=mem + tls_size - 8 * (cnt + 1))
    else:
        x.update(td=None, tp=None, dtv=None)
    return x


def paint(segs, lo, hi, val):
    """segs: sorted, contiguous [(lo, hi, val)]; returns them with [lo, hi) (clipped to segs) set to val."""
    lo, hi = max(lo, segs[0][0]), min(hi, segs[-1][1])
    if lo >= hi:
        return segs
    out = [s for a, b, v in segs for s in ((a, min(b, lo), v), (max(a, hi), b, v)) if s[0] < s[1]]
    return sorted(out + [(lo, hi, val)], key=lambda s: s[0])


def value_at(segs, v):
    return next(val for a, b, val in segs if a <= v < b)


def carve(items, lo, hi):
    """items with [lo, hi) cut out of their old ranges."""
    out = []
    for r in items:
        if r["old_hi"] <= lo or r["old_lo"] >= hi:
            out.append(r)
            continue
        if r["old_lo"] < lo:
            out.append(dict(r, old_hi=lo))
        if r["old_hi"] > hi:
            right = dict(r, old_lo=hi)
            if "delta" in r:
                right["new_lo"] = hi + r["delta"]
            out.append(right)
    return out


def tls_anchor(old_elf, new_elf, states, res):
    """Map musl's TLS objects cell by cell, overriding .bss interpolation (in v26 musl builtin_tls sits inside the
    static block at +0x38; in rc.2 it is its own .bss object: no .bss delta covers either).
    - The static block (__thread_list_lock, main_tls) moves as one object.
    - The old builtin_tls window holds cells that hang off different bases (musl_tls_layout): struct pthread at
      [td, tp) and the TLS image at tp + offset move with td; the dtv moves with mem + tls_size; the bytes past
      tls_size with the block end.  Each takes its own delta.  With tls_align 8 and an unchanged PT_TLS all of these
      agree and the whole window moves by one delta; with tls_align 16 (mosh) td = mem + 8 on one side only.
    - The image cell at tp + offset + j is the copy of template byte PT_TLS vaddr + j: it follows the template's map.
    - mem and tp are also pointer values, not only cells.  An address that is two things in OLD (mem = td when
      the old alignment pad is 0) whose readings separate in NEW is left ambiguous with both deltas.
    - Bytes that are no musl cell (alignment pad, slack) are ambiguous, unless every cell agrees on one delta.
    - When OLD took the mmap path (tls_size > builtin_tls: igraph, libpcap, nccl in v26), OLD's td, tp, dtv and
      DTP-biased pointers live in an mmap'd page outside the image and OLD's builtin_tls is an unused .bss buffer:
      no builtin_tls run and no DTP window; those addresses keep the ordinary .bss map."""
    ot = find_musl_tls(old_elf, [co for _, _, co, _, _ in states])
    nt = find_musl_tls(new_elf, [cn for _, _, _, cn, _ in states])
    if ot is None and nt is None:
        return None
    if ot is None or nt is None:
        raise SystemExit(f"musl static_init_tls found in only one binary: old {ot}, new {nt}")
    musl_tls_layout(ot, old_elf)
    musl_tls_layout(nt, new_elf)
    before = Lookup(res["runs"])
    before_amb = list(res["ambiguous"])
    pts = {a: d for s in res["data_sections"] for a, d in s["anchor_points"]}
    mem_o, mem_n = ot["builtin_tls"], nt["builtin_tls"]
    w_lo, w_hi = mem_o, mem_o + min(ot["builtin_tls_size"], nt["builtin_tls_size"])
    blk = ot["static_block"]
    deltas = {"static_block": nt["static_block"] - blk}
    res["runs"] = carve(res["runs"], blk, blk + TLS_BLOCK)
    res["ambiguous"] = carve(res["ambiguous"], blk, blk + TLS_BLOCK)
    windows = [("static-block", "static block (__thread_list_lock, main_tls)", blk, blk + TLS_BLOCK,
                deltas["static_block"])]
    res["runs"].append({"old_lo": blk, "old_hi": blk + TLS_BLOCK, "new_lo": nt["static_block"],
                        "delta": deltas["static_block"], "kind": "tls-object", "object": windows[0][1],
                        "section": next(r.name for r in old_elf.sections if r.vaddr <= blk < r.end)})
    conflicts, amb = [], []
    if not ot["in_builtin"]:
        windows.append(("builtin_tls", "builtin_tls (mem), unused in OLD (TLS block mmap'd)", w_lo, w_hi, None))
    else:
        deltas["builtin_tls"] = mem_n - mem_o
        windows.append(("builtin_tls", "builtin_tls (mem) object", w_lo, w_hi, deltas["builtin_tls"]))
        segs = [(w_lo, w_hi, (None, "builtin_tls bytes that are no musl cell (alignment pad or slack)", None))]
        if nt["in_builtin"]:
            td_d, dtv_d, mem_d = nt["td"] - ot["td"], nt["dtv"] - ot["dtv"], deltas["builtin_tls"]
            deltas.update(td=td_d, dtv=dtv_d)
            segs = paint(segs, mem_o, mem_o + min(ot["td"] - mem_o, nt["td"] - mem_n),
                         (mem_d, "builtin_tls head: alignment pad below td", None))
            segs = paint(segs, ot["td"], ot["tp"], (td_d, "td: struct pthread, td+0 .. tp", None))
            img_o, img_n = ot["tp"] + ot["tls_offset"], nt["tp"] + nt["tls_offset"]
            img = []
            for j in range(ot["tls_memsz"]):
                t = before(ot["tls_vaddr"] + j)
                if t is None or not nt["tls_vaddr"] <= t < nt["tls_vaddr"] + nt["tls_memsz"]:
                    continue
                d = img_n + (t - nt["tls_vaddr"]) - (img_o + j)
                if img and img[-1][1] == img_o + j and img[-1][2] == d:
                    img[-1][1] += 1
                else:
                    img.append([img_o + j, img_o + j + 1, d])
            for a, b, d in img:
                segs = paint(segs, a, b, (d, "TLS image at tp + offset (follows the PT_TLS template's map)", None))
            ncnt = min(ot["tls_cnt"], nt["tls_cnt"])
            segs = paint(segs, ot["dtv"], ot["dtv"] + 8 * (ncnt + 1),
                         (dtv_d, "dtv[0..tls_cnt] at builtin_tls + tls_size - 8*(tls_cnt+1)", None))
            end_o, end_n = mem_o + ot["tls_size"], mem_n + nt["tls_size"]
            tail = min(ot["builtin_tls_size"] - ot["tls_size"], nt["builtin_tls_size"] - nt["tls_size"])
            segs = paint(segs, end_o, end_o + tail,
                         (end_n - end_o, "builtin_tls past tls_size: unused, moves with the TLS block end", None))
            for v, d, what in ((ot["tp"], td_d, "tp (the thread pointer)"),
                               (mem_o, mem_d, "builtin_tls itself (mem, the __copy_tls argument)")):
                cur = value_at(segs, v)
                if cur[0] is None:  # no cell here: the address can only mean that pointer
                    segs = paint(segs, v, v + 1, (d, what, None))
                elif cur[0] != d:
                    why = f"OLD {v:#x} is {what} and also {cur[1]}; NEW separates them: decide per use site"
                    conflicts.append({"old": v, "deltas": sorted({d, cur[0]}), "why": why})
                    segs = paint(segs, v, v + 1, (None, why, sorted({d, cur[0]})))
            windows += [("td", "td: struct pthread (td .. tp)", ot["td"], ot["tp"], td_d),
                        ("tls-image", "TLS image at tp + offset", img_o, img_o + ot["tls_memsz"],
                         td_d if img == [[img_o, img_o + ot["tls_memsz"], td_d]] or not ot["tls_memsz"] else None),
                        ("dtv", "dtv[0..tls_cnt]", ot["dtv"], ot["dtv"] + 8 * (ot["tls_cnt"] + 1), dtv_d)]
            same_shape = all(ot[k] == nt[k] for k in ("tls_memsz", "tls_offset", "tls_image_size", "tls_size",
                                                      "tls_cnt"))
            painted = {v[0] for _, _, v in segs if v[0] is not None}
            if same_shape and not conflicts and len(painted) == 1:
                d = painted.pop()
                segs = [(a, b, v if v[0] is not None else (d, "builtin_tls bytes that are no musl cell (every cell "
                                                              "moves by this delta)", None)) for a, b, v in segs]
        else:
            segs = [(w_lo, w_hi, (None, "NEW takes its TLS block from mmap (tls_size > builtin_tls): OLD's td, tp "
                                        "and dtv cells have no NEW image address", None))]
        merged = []
        for a, b, v in segs:
            if merged and merged[-1][1] == a and merged[-1][2] == v:
                merged[-1] = (merged[-1][0], b, v)
            else:
                merged.append((a, b, v))
        cands = sorted({v[0] for _, _, v in merged if v[0] is not None} | {deltas["builtin_tls"]})
        sec = next(r.name for r in old_elf.sections if r.vaddr <= w_lo < r.end)
        res["runs"] = carve(res["runs"], w_lo, w_hi)
        res["ambiguous"] = carve(res["ambiguous"], w_lo, w_hi)
        for a, b, (d, label, cs) in merged:
            if d is None:
                amb.append({"old_lo": a, "old_hi": b, "section": sec, "candidates": cs or cands, "why": label})
            else:
                res["runs"].append({"old_lo": a, "old_hi": b, "new_lo": a + d, "delta": d, "kind": "tls-object",
                                    "section": sec, "object": label})
        res["ambiguous"] += amb
    out = []
    for kind, name, lo, hi, d in windows:
        prior = before(lo)
        if prior is not None:
            prior_txt = sd(prior - lo)
        else:
            a = next((a for a in before_amb if a["old_lo"] <= lo < a["old_hi"]), None)
            prior_txt = f"ambiguous {[sd(c) for c in a['candidates']]}" if a else "unmapped"
        inside = {hex(a): x for a, x in pts.items() if lo <= a < hi}
        anchored = not (kind == "builtin_tls" and not ot["in_builtin"])
        out.append({"kind": kind, "name": name, "anchored": anchored, "old_lo": lo, "old_hi": hi, "delta": d,
                    "new_lo": None if d is None else lo + d, "map_before_anchor": prior_txt,
                    "anchors_inside": len(inside),
                    "anchors_disagreeing": {a: x for a, x in inside.items() if anchored and x != d}})
    dtp = None
    if ot["in_builtin"] and nt["in_builtin"]:
        # DTP-biased TLS pointers (dtv[1] = tp + 0x800, ASan's thread TLS begin td + 0x800 and end) move with tp
        dtp = {"old_lo": ot["td"] + DTP_OFFSET, "old_hi_incl": ot["tp"] + DTP_OFFSET + ot["tls_memsz"],
               "delta": nt["tp"] - ot["tp"]}
    return {"old": ot, "new": nt, "deltas": deltas, "objects": out, "ambiguous": amb, "conflicts": conflicts,
            "dtp": dtp, "tp_offset": PTHREAD_SIZE, "dtp_offset": DTP_OFFSET}


def build(old_path, new_path):
    old_elf, new_elf = rvelf.Elf(old_path), rvelf.Elf(new_path)
    old_desc, new_desc, geo = describe(old_elf), describe(new_elf), geometry(old_elf, new_elf)
    prev = None
    for npass in range(1, MAX_PASSES + 1):
        res = {"tool": "elf_symbols", "format": 1, "old": old_desc, "new": new_desc,
               "geometry": geo, "runs": [], "inserted": [], "deleted": [],
               "ambiguous": [], "pcrel_changed": [], "exec_sections": [], "data_sections": []}
        states = map_code(old_elf, new_elf, res, prev)
        code_runs = [r for r in res["runs"] if r["kind"] == "code"]
        if code_runs == prev:
            break
        prev = code_runs
    res["code_passes"] = npass
    for ro, rn, co, cn, blocks in states:
        res["exec_sections"].append({"name": ro.name, "old_vaddr": ro.vaddr, "old_size": ro.size,
                                     "new_vaddr": rn.vaddr, "new_size": rn.size, "shift": rn.vaddr - ro.vaddr,
                                     "old_insns": len(co.pcs), "new_insns": len(cn.pcs),
                                     "matched_insns": sum(n for _, _, n in blocks)})
    anchors = code_anchors_and_changes(states, res, old_elf, new_elf)
    xref_check(res, anchors)
    map_data(old_elf, new_elf, res, anchors)
    res["tls_anchor"] = tls_anchor(old_elf, new_elf, states, res)
    for k in ("runs", "ambiguous", "deleted"):
        res[k].sort(key=lambda r: r["old_lo"])
    res["inserted"].sort(key=lambda r: r["new_lo"])
    pc_ok = Counter()
    look_all = Lookup(res["runs"])
    for c in res["pcrel_changed"]:
        if c["kind"] in ("auipc", "lo12x"):  # a page (pc + hi20<<12) or an unproven target: nothing to check
            c["target_consistent"] = "n/a"
        else:
            m = look_all(c["old_target"])
            c["target_consistent"] = (m == c["new_target"]) if m is not None else None
        pc_ok[c["target_consistent"]] += 1
    res["pcrel_changed_consistency"] = {str(k): v for k, v in pc_ok.items()}
    res["anchor_stats"] = dict(res["anchor_stats"])
    # Every code-grade reference into data (code lo12 targets, code-paired .got/.data.rel.ro slots) checked
    # against the final map, TLS object overrides included: a map that moves a referenced object by a delta
    # other than its references' is wrong, whatever produced it.
    data_ranges = [(r.vaddr, r.end) for r in old_elf.sections if r.kind != "exec"]
    rc, bad = Counter(), []
    for old, new, kind, site in anchors:
        if kind not in ("lo12", "got") or not any(a <= old < b for a, b in data_ranges):
            continue
        m = look_all(old)
        if m is None:
            rc["unmapped"] += 1
        elif m == new:
            rc["agree"] += 1
        else:
            rc["DISAGREE"] += 1
            bad.append({"site": site, "kind": kind, "old": old, "new": new, "map": m})
    res["reference_check"] = {"counts": dict(rc), "disagree": bad}
    return res, old_elf, new_elf


# ----------------------------------------------------------------------------------
# human summary
# ----------------------------------------------------------------------------------

def h(x):
    return "-" if x is None else f"{x:#x}"


def sd(x):
    return f"{'+' if x >= 0 else '-'}{abs(x):#x}"


def summary(res, old_elf, new_elf, disasm_ctx, out):
    p = lambda *a: print(*a, file=out)  # noqa: E731
    p(f"OLD {res['old']['path']}  sha256 {res['old']['sha256'][:16]}")
    p(f"NEW {res['new']['path']}  sha256 {res['new']['sha256'][:16]}")
    p("\n== geometry (page-rounded PT_LOADs, as the image .v files use them)")
    for g in res["geometry"]:
        flag = "" if g["old"] == g["new"] else f"  ({sd(g['new'] - g['old'])})"
        p(f"  {g['name']:<10} {h(g['old']):>10} -> {h(g['new']):<10}{flag}")
    p("\n== sections (old vaddr/size -> new vaddr/size, shift of the start)")
    for s in res["exec_sections"]:
        p(f"  {s['name']:<16} exec {h(s['old_vaddr'])}/{h(s['old_size'])} -> {h(s['new_vaddr'])}/{h(s['new_size'])}"
          f"  shift {sd(s['shift'])}  insns {s['old_insns']} -> {s['new_insns']}, matched {s['matched_insns']}")
    for s in res["data_sections"]:
        p(f"  {s['name']:<16} {s['kind']:<4} {h(s['old_vaddr'])}/{h(s['old_size'])} -> "
          f"{h(s['new_vaddr'])}/{h(s['new_size'])}  shift {sd(s['shift'])}  anchors {s['anchors']}"
          + (f"  content runs {len(s['content_runs'])}" if s["content_runs"] else ""))
    t = res.get("tls_anchor")
    if t:
        p("\n== musl TLS object anchor (static_init_tls auipc pairs + musl's TLS layout; overrides .bss interpolation)")
        for side in ("old", "new"):
            x = t[side]
            p(f"  {side.upper()} {x['variant']}: static_init_tls {h(x['entry'])}..{h(x['end'])}  static block "
              f"{h(x['static_block'])}  main_tls {h(x['main_tls'])}  libc {h(x['libc'])}  builtin_tls (mem) "
              f"{h(x['builtin_tls'])} [{x['builtin_tls_from']}]  builtin_tls size {x['builtin_tls_size']:#x}")
            where = (f"td {h(x['td'])}  tp {h(x['tp'])}  dtv {h(x['dtv'])}" if x["in_builtin"] else
                     "td/tp/dtv in an mmap'd block (tls_size > builtin_tls)")
            p(f"      PT_TLS vaddr {h(x['tls_vaddr'])} memsz {x['tls_memsz']:#x} p_align {x['tls_p_align']}  "
              f"tls_align {x['tls_align']}  offset {x['tls_offset']:#x}  tls_cnt {x['tls_cnt']}  "
              f"tls_size {x['tls_size']:#x}  {where}")
        p("  deltas: " + "  ".join(f"{k} {sd(v)}" for k, v in t["deltas"].items()))
        for o in t["objects"]:
            mv = (f"-> NEW {h(o['new_lo'])}  delta {sd(o['delta'])}" if o["delta"] is not None else
                  "mixed deltas" if o["anchored"] else "not anchored")
            prior = "the map without this anchor" if o["anchored"] else "the ordinary map"
            p(f"  {o['name']}: OLD {h(o['old_lo'])}..{h(o['old_hi'])} {mv}  ({prior}: {o['map_before_anchor']}; "
              f"{o['anchors_inside']} code/pointer anchors inside, disagreeing {o['anchors_disagreeing'] or 'none'})")
        for r in sorted((r for r in res["runs"] if r["kind"] == "tls-object"), key=lambda r: r["old_lo"]):
            p(f"    run OLD {h(r['old_lo'])}..{h(r['old_hi'])} delta {sd(r['delta'])}  {r['object']}")
        for a in t["ambiguous"]:
            p(f"    AMBIGUOUS OLD {h(a['old_lo'])}..{h(a['old_hi'])} {[sd(c) for c in a['candidates']]}  {a['why']}")
        if t["dtp"]:
            d = t["dtp"]
            p(f"  DTP-biased TLS pointer window OLD [{h(d['old_lo'])}, {h(d['old_hi_incl'])}] (td + 0x800 .. "
              f"tp + 0x800 + memsz): as TLS pointers they move {sd(d['delta'])} (with tp)")
        else:
            p("  no DTP-biased TLS pointer window: OLD's or NEW's TLS block is mmap'd, outside the image")
    code = [r for r in res["runs"] if r["kind"] == "code"]
    p(f"\n== code runs: {len(code)} constant-delta runs")
    for r in code:
        p(f"  {h(r['old_lo'])}..{h(r['old_hi'])} -> {h(r['new_lo'])}  delta {sd(r['delta'])}  "
          f"({r['insns']} insns, {r['section']})")
    ins = [r for r in res["inserted"] if "insns" in r]
    dels = [r for r in res["deleted"] if "insns" in r]
    p(f"\n== inserted code regions in NEW: {len(ins)}, {sum(r['bytes'] for r in ins):#x} bytes, "
      f"{sum(r['insns'] for r in ins)} insns")
    for r in ins:
        rep = f" replacing OLD {h(r['replaces'][0])}..{h(r['replaces'][1])}" if r.get("replaces") else \
            f" (pure insertion before OLD {h(r['old_at'])})"
        p(f"  NEW {h(r['new_lo'])}..{h(r['new_hi'])}  {r['bytes']:#x} bytes, {r['insns']} insns{rep}")
    p(f"\n== deleted code regions in OLD: {len(dels)}, {sum(r['bytes'] for r in dels):#x} bytes, "
      f"{sum(r['insns'] for r in dels)} insns")
    for r in dels:
        rep = f" replaced by NEW {h(r['replaced_by'][0])}..{h(r['replaced_by'][1])}" if r.get("replaced_by") else \
            f" (pure deletion, NEW continues at {h(r['new_at'])})"
        p(f"  OLD {h(r['old_lo'])}..{h(r['old_hi'])}  {r['bytes']:#x} bytes, {r['insns']} insns{rep}")
    other = [r for r in res["inserted"] + res["deleted"] if "insns" not in r]
    for r in other:
        p(f"  {r.get('why')}: {r['section']}")
    pc = res["pcrel_changed"]
    kinds = Counter(c["kind"] for c in pc)
    p(f"\n== instructions whose encoding changed only in a PC-relative / auipc-paired immediate: {len(pc)}"
      f"  by kind {dict(kinds)}")
    p(f"   target consistent with the map: {res['pcrel_changed_consistency']}")
    for c in pc[:40]:
        where = (f"page {h(c['old_page'])} -> {h(c['new_page'])} (not an object address)" if c["kind"] == "auipc"
                 else f"target {h(c['old_target'])} -> {h(c['new_target'])}")
        p(f"  {h(c['old_pc'])} -> {h(c['new_pc'])}  {c['kind']:<7} {c['old_word']:0{c['len'] * 2}x} -> "
          f"{c['new_word']:0{c['len'] * 2}x}  {where}"
          + ("" if c["target_consistent"] else f"  [target consistent={c['target_consistent']}]"))
    if len(pc) > 40:
        p(f"  ... {len(pc) - 40} more in the JSON (pcrel_changed)")
    rc = res["reference_check"]
    p(f"\n== code references into data (lo12 targets, code-paired .got/.data.rel.ro slots) against the final "
      f"data map: {rc['counts']}")
    for b in rc["disagree"][:40]:
        p(f"  DISAGREE {b['kind']} at {h(b['site'])}: OLD {h(b['old'])} -> NEW {h(b['new'])}, the map says {h(b['map'])}")
    p(f"\n== cross-check of matched code->code references against the code map: {res['xref_check']['counts']}")
    tg = Counter((b["old_target"], b["map"], b["new_target"]) for b in res["xref_check"]["inconsistent"])
    for (ot, mt, nt), c in sorted(tg.items()):
        p(f"  {c:4} matched references to OLD {h(ot)}: the map says {h(mt)}, the NEW references go to {h(nt)}"
          f" ({sd(nt - mt)})")
    data = [r for r in res["runs"] if r["kind"] != "code"]
    p(f"\n== data runs: {len(data)}")
    for r in data:
        p(f"  {h(r['old_lo'])}..{h(r['old_hi'])} -> {h(r['new_lo'])}  delta {sd(r['delta'])}  {r['kind']}  ({r['section']})")
    p(f"\n== ambiguous OLD ranges (never mapped): {len(res['ambiguous'])}")
    for r in res["ambiguous"]:
        p(f"  {h(r['old_lo'])}..{h(r['old_hi'])}  {r['section']}  candidates "
          f"{[sd(c) for c in r['candidates']]}  {r['why']}")
    code_c = [a for a in res["anchor_conflicts"] if a["evidence"] == "code"]
    ptr_c = [a for a in res["anchor_conflicts"] if a["evidence"] == "pointer"]
    p(f"\n== CODE-REFERENCE CONFLICTS (code lo12 targets / code-paired .got slots disagree on one object; "
      f"the object is left unanchored): {len(code_c)}")
    for a in code_c:
        p(f"  CONFLICT {h(a['old'])} deltas {[sd(d) for d in a['deltas']]} ({a['section']})")
    if ptr_c:
        p(f"\n== content-pointer conflicts (dropped; a code reference decides where it exists): {len(ptr_c)}")
        for a in ptr_c[:20]:
            dec = "undecided" if a["decided_by"] is None else f"decided by code: {sd(a['decided_by'])}"
            p(f"  {h(a['old'])} deltas {[sd(d) for d in a['deltas']]} ({a['section']}; {dec})")
    if disasm_ctx:
        show_disasm(res, old_elf, new_elf, disasm_ctx, p)


def show_disasm(res, old_elf, new_elf, ctx, p):
    p("\n== disassembly of changed code regions (capstone)")
    for r in res["deleted"] + res["inserted"]:
        if "insns" not in r:
            continue
        if "old_lo" in r:
            sides = [("OLD", old_elf, r["old_lo"], r["old_hi"])]
            if r.get("replaced_by"):
                sides.append(("NEW", new_elf, *r["replaced_by"]))
        else:
            if r.get("replaces"):
                continue  # shown with its deleted counterpart
            sides = [("NEW", new_elf, r["new_lo"], r["new_hi"]), ("OLD", old_elf, r["old_at"], r["old_at"])]
        p(f"\n-- {r['section']} {', '.join(f'{n} {s:#x}..{e:#x}' for n, _, s, e in sides)}")
        for name, elf, lo, hi in sides:
            sec = next(s for s in elf.sections if s.kind == "exec" and s.vaddr <= lo <= s.end)
            code = rvelf.Code(elf.region_bytes(sec), sec.vaddr)
            k0 = bisect.bisect_left(code.pcs, lo)
            k1 = bisect.bisect_left(code.pcs, hi)
            a, b = max(0, k0 - ctx), min(len(code.pcs), k1 + ctx)
            lo_pc = code.pcs[a]
            hi_pc = code.pcs[b - 1] + code.lens[b - 1]
            lines = rvelf.disasm(elf.read(lo_pc, hi_pc - lo_pc), lo_pc)
            if lines is None:
                p("  (capstone not importable: run with tools/.venv/bin/python for disassembly)")
                return
            p(f"  [{name}]")
            for pc, hx, text in lines:
                mark = ">" if lo <= pc < hi else " "
                p(f"  {mark} {pc:#x}: {hx:<8}  {text}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("old", help="OLD ELF (the binary the proofs were written against)")
    ap.add_argument("new", help="NEW ELF")
    ap.add_argument("-o", "--output", required=True, help="map JSON to write")
    ap.add_argument("--disasm", type=int, default=0, metavar="N",
                    help="also print capstone disassembly of every inserted/deleted code region "
                         "with N instructions of context (needs capstone, e.g. tools/.venv/bin/python)")
    ap.add_argument("--summary", help="write the human summary to this file instead of stdout")
    args = ap.parse_args()
    res, old_elf, new_elf = build(args.old, args.new)
    with open(args.output, "w") as f:
        json.dump(res, f, indent=1)
    if args.summary:
        with open(args.summary, "w") as f:
            summary(res, old_elf, new_elf, args.disasm, f)
    else:
        summary(res, old_elf, new_elf, args.disasm, sys.stdout)


if __name__ == "__main__":
    main()
