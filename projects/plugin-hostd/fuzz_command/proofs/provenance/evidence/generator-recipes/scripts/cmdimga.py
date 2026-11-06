#!/usr/bin/env python3
"""Build the donor -> ASan image symbol map for the GXA (ASan printf core) instance of plugin-hostd/fuzz_command,
and emit lib/A/RT_IImgA.v (image A, fuzz_command.asan) or lib/B/RT_IImgA.v (image B, fuzz_command.asan-ubsan).

Composition: the released IImgP map carries a donor address to fuzz_manifest.plain; this script
carries plain -> asan by one of four rules, and writes the rule and its evidence next to the row.

  SYMBOL   the plain address lies in a named symbol the ASan image also has; the offset inside the
           symbol is kept.
  CODEREF  the object is named by the SAME instruction (same byte offset inside a function of the
           chain, same opcode) in both images: auipc/addi, auipc/ld or jal.  This is what pairs the
           anonymous .rodata tables and, in an ASan build, the interceptor trampolines that musl's
           calls to memcpy / memset / strnlen / wctomb / strerror actually jump to.
  CONTENT  the plain object's bytes occur exactly once in the ASan .rodata.
  GEOMETRY an image bound (the last PT_LOAD end, rounded to a page).

Nothing is paired by value and nothing by a uniform delta.  RT_IImgA_ok.v checks against the pinned image (CodeAtT /
RoB / RelCode / RelSym / RelNear / ZFact, by vm_compute) the rows its lemmas name; its header lists exactly which rows
those are and which rows it does not check.

Copy of record of the two generators that wrote lib/A/RT_IImgA.v (generator sha256 40b21479f19c...) and
lib/B/RT_IImgA.v (generator sha256 09c09529949d...).  Those two are fuzz_manifest's generator
(analyses/rtprintf/rtp-gxa/gen/fmimga.py, git blob 0b84e3becf07 at commit 3e35620c52e4) pointed at fuzz_command's
images, with one rule change (CODEREF also reads `auipc rX; addi rY, rX, imm` with rY <> rX: printf_core+0x5ec forms
"(null)" so); they differ from each other only in the ASan image and the core module.  This copy takes those as
arguments, reads its inputs and writes its output at the paths its arguments give, and writes its own provenance line
(line N+1 of --out, after the N lines that --keep-head keeps), which names this file, the generator it is adapted from,
the twins, the published images (by the first 8 hex digits of their sha256, as the earlier hand-written line did), its
other inputs, the core module and the CODEREF rule change.  Its other lines are the earlier generators' output with
three changes (2026-10-31): a bound row (a key equal to the END of an IImgP interval) is not paired by CONTENT either -
the earlier generators paired donor 0x102a8, the printf model's A_FMT_emit, with the plain object that starts at that
interval's end (0x10300), whose bytes are not the model's string; the comment over the OPEN rows says what IImgP does
with each such key instead of calling every one of them a bound; and the header no longer says that every row is
checked again by RT_IImgA_ok.v, which never held, but points to the rows that file checks.

  cmdimga.py --plain P --asan A --plain-name NAME --image-name NAME --iimgp IImgP.v --gxa DIR
             --prefix COQ_PREFIX --core LIBDIR.MODULE --out FILE [--keep-head N] [--map-json FILE]

P and A are path prefixes: P.debug (the unstripped twin), P.nm.txt (its `nm -S` symbol listing) and P.readelf.txt
(its readelf listing; the section headers are read) are read, and the same for A.
"""
import argparse
import glob
import hashlib
import json
import os
import re
import struct
import sys

# donor addresses that GXA's own files never spell: pop_arg's jump table and the builtin
# __extenddftf2, named by G/G_pop_arg.v and GX/G_pop_arg_x.v, whose contracts GXA takes as
# SPEC_pop_arg / SPEC_pop_arg_x.  Without these rows tsym falls back to the identity.
EXTRA = [0x10984, 0x1af98, 0x19534]

# musl vfprintf: GXA's closure (G_vfprintf_snf_closed.v) walks musl vfprintf's BODY at both of these
# donor addresses, so the CODEREF rule may not move them onto the interceptor.  The jal inside musl
# vsnprintf does go to the interceptor; that single address is what the SECOND instance (A_img_vsn)
# carries, and the interceptor's own walk is what joins the two.
NO_CODEREF = {0x18554, 0x7f000400}
VSN_CALL_DONOR = 0x7f000400

# functions of the chain, by donor address, used for the CODEREF rule
CHAIN = {
    0x18704: "printf_core",
    0x19534: "pop_arg",
    0x19668: "pad",
    0x17d50: "__fwritex",
    0x1973c: "fmt_fp",
    0x7f000200: "vsnprintf",
    0x7f000300: "sn_write",
    0x7f000400: "vfprintf",
}


def parse_iimgp(path):
    txt = open(path).read()
    ex, iv = [], []
    mex = re.search(r"Definition N_exact[^=]*:=\s*\[(.*?)\]\.", txt, re.S)
    for a, b in re.findall(r"KV\s+(0x[0-9a-f]+)\s+(0x[0-9a-f]+)", mex.group(1)):
        ex.append((int(a, 16), int(b, 16)))
    miv = re.search(r"Definition N_iv[^=]*:=\s*\[(.*?)\]\.", txt, re.S)
    for a, b, d in re.findall(r"KV3\s+(0x[0-9a-f]+)\s+(0x[0-9a-f]+)\s+\((-?\d+)\)", miv.group(1)):
        iv.append((int(a, 16), int(b, 16), int(d)))
    return ex, iv


def syms(nmpath):
    by_name, lst = {}, []
    for line in open(nmpath):
        p = line.split()
        if len(p) < 4:
            continue
        try:
            a = int(p[0], 16)
            sz = int(p[1], 16)
        except ValueError:
            continue
        if sz == 0:
            continue
        lst.append((a, sz, p[3], p[2]))
        if p[3] not in by_name:
            by_name[p[3]] = (a, sz, p[2])
    lst.sort()
    return by_name, lst


def cover(lst, a):
    lo, hi, best = 0, len(lst) - 1, None
    while lo <= hi:
        mid = (lo + hi) // 2
        if lst[mid][0] <= a:
            best = lst[mid]
            lo = mid + 1
        else:
            hi = mid - 1
    if best and best[0] <= a < best[0] + best[1]:
        return best
    return None


def loads(path):
    d = open(path, "rb").read()
    e_phoff = struct.unpack_from("<Q", d, 0x20)[0]
    phentsize, phnum = struct.unpack_from("<HH", d, 0x36)
    segs = []
    for i in range(phnum):
        t, fl, off, va, pa, fsz, msz, al = struct.unpack_from("<IIQQQQQQ", d, e_phoff + i * phentsize)
        if t == 1:
            segs.append((va, off, fsz, msz, fl))
    return d, segs


def rd(d, segs, a, n):
    for va, off, fsz, msz, fl in segs:
        if va <= a and a + n <= va + fsz:
            return d[off + a - va:off + a - va + n]
    return None


def sect(path, name):
    for line in open(path + ".readelf.txt"):
        m = re.match(r"\s*\[\s*\d+\]\s+(\S+)\s+(\S+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)", line)
        if m and m.group(1) == name:
            return int(m.group(3), 16), int(m.group(5), 16)
    return None


def refs(d, segs, lo, hi):
    """Every (instruction offset inside [lo,hi), kind, target) this code forms:
    auipc+addi / auipc+load / auipc+store pairs and jal.  The offset is the offset of the
    SECOND instruction (the one that completes the address), which is what the two images share."""
    out, hiv = [], {}
    a = lo
    while a < hi:
        w = rd(d, segs, a, 4)
        if not w:
            a += 4
            continue
        w = struct.unpack("<I", w)[0]
        if (w & 3) != 3:            # 16-bit compressed instruction
            a += 2
            continue
        op = w & 0x7F
        rdn = (w >> 7) & 0x1F
        if op == 0x17:              # auipc
            hiv[rdn] = (a, w & 0xFFFFF000)
        elif op == 0x6F:            # jal
            imm = (((w >> 31) & 1) << 20) | (((w >> 12) & 0xFF) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3FF) << 1)
            if imm >= 0x100000:
                imm -= 0x200000
            out.append((a - lo, "jal", a + imm))
        elif op == 0x13 and ((w >> 12) & 7) == 0:   # addi
            rs1 = (w >> 15) & 0x1F
            if rs1 in hiv:
                # (cmdimga: also `auipc a0; addi s7, a0, imm`, rd != rs1: musl printf_core forms "(null)" so)
                imm = w >> 20
                if imm >= 0x800:
                    imm -= 0x1000
                base_a, up = hiv.pop(rs1) if rs1 == rdn else hiv[rs1]
                out.append((a - lo, "auipc+addi", base_a + ((up ^ 0x80000000) - 0x80000000) + imm))
        elif op in (0x03, 0x23):    # load / store
            rs1 = (w >> 15) & 0x1F
            if rs1 in hiv:
                imm = (w >> 20) if op == 0x03 else (((w >> 25) << 5) | ((w >> 7) & 0x1F))
                if imm >= 0x800:
                    imm -= 0x1000
                base_a, up = hiv.pop(rs1)
                out.append((a - lo, "auipc+%s" % ("ld" if op == 0x03 else "st"),
                            base_a + ((up ^ 0x80000000) - 0x80000000) + imm))
        a += 4
    return out


def donor_to_plain(ex, iv, k):
    for a, b in ex:
        if a == k:
            return b, "exact"
    for lo, hi, d in iv:
        if lo <= k < hi:
            return k + d, "iv[%s,%s)%+d" % (hex(lo), hex(hi), d)
    return None, "unmapped"


def gxa_needs(gxa):
    pats = [re.compile(r"\bsym\s+(0x[0-9a-fA-F]+)"),
            re.compile(r"\bGLRN\s+(0x[0-9a-fA-F]+)\s+(0x[0-9a-fA-F]+)"),
            re.compile(r"\bGLRS\s+(0x[0-9a-fA-F]+)")]
    need = {}
    for f in glob.glob(gxa + "/*.v"):
        t = open(f).read()
        for p in pats:
            for m in p.findall(t):
                for x in (m if isinstance(m, tuple) else (m,)):
                    need[int(x, 16)] = need.get(int(x, 16), 0) + 1
    for k in EXTRA:
        need.setdefault(k, 0)
    return need


def sha256_file(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def gxa_digest(gxa):
    """sha256 of what `sha256sum *.v` prints in the directory (names in byte order)."""
    lines = "".join("%s  %s\n" % (sha256_file(f), os.path.basename(f))
                    for f in sorted(glob.glob(gxa + "/*.v"), key=lambda f: os.path.basename(f).encode()))
    return hashlib.sha256(lines.encode()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--plain", required=True, help="path prefix of the plain image's unstripped twin")
    ap.add_argument("--asan", required=True, help="path prefix of the ASan image's unstripped twin")
    ap.add_argument("--plain-name", required=True, help="the plain image's name, e.g. fuzz_command.plain")
    ap.add_argument("--image-name", required=True, help="the ASan image's name, e.g. fuzz_command.asan")
    ap.add_argument("--iimgp", required=True, help="the unit's lib/CJ/RL/I/IImgP.v")
    ap.add_argument("--gxa", required=True, help="the directory of GXA's .v files")
    ap.add_argument("--prefix", required=True, help="the unit's Coq prefix, e.g. OssFuzzTheorems.Proofs.plugin_hostd.fuzz_command")
    ap.add_argument("--core", required=True, help="the image's core module that holds tfibsegs, e.g. lib.A.AB1v")
    ap.add_argument("--plain-published", required=True, help="the published plain image (its sha256 is named in line N+1)")
    ap.add_argument("--image-published", required=True, help="the published ASan image (its sha256 is named in line N+1)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--keep-head", type=int, default=0, help="keep the first N lines of the existing --out")
    ap.add_argument("--map-json")
    opt = ap.parse_args()
    PLAIN, ASAN = opt.plain, opt.asan
    ex, iv = parse_iimgp(opt.iimgp)
    need = gxa_needs(opt.gxa)
    pn, pl = syms(PLAIN + ".nm.txt")
    an, al = syms(ASAN + ".nm.txt")
    pd, ps = loads(PLAIN + ".debug")
    ad, asg = loads(ASAN + ".debug")
    pro, aro = sect(PLAIN, ".rodata"), sect(ASAN, ".rodata")
    arob = rd(ad, asg, aro[0], aro[1])

    # per-chain-function reference tables, keyed by instruction offset inside the function
    pref, aref = {}, {}
    for donor, nm in CHAIN.items():
        if nm not in pn or nm not in an:
            continue
        pa, psz, _ = pn[nm]
        aa, asz, _ = an[nm]
        pref[nm] = {o: (k, t) for o, k, t in refs(pd, ps, pa, pa + psz)}
        aref[nm] = {o: (k, t) for o, k, t in refs(ad, asg, aa, aa + asz)}

    top_a = max(va + msz for va, off, fsz, msz, fl in asg)
    page = (top_a + 0xFFF) & ~0xFFF

    rows = []
    for k in sorted(need):
        plain, how = donor_to_plain(ex, iv, k)
        r = {"donor": k, "uses": need[k], "plain": plain, "how": how,
             "sym": None, "asan": None, "rule": None, "ev": None}
        if plain is None:
            for lo, hi, d in iv:
                if k == hi:
                    # a key equal to an interval's END lies outside it (IImgP's intervals are half-open):
                    # carry hi + d as a bound, but never pair it with whatever object happens to start
                    # there - neither CODEREF nor CONTENT below pairs a bound row.
                    r["plain"] = hi + d
                    r["how"] = "interval-end of [%s,%s)%+d" % (hex(lo), hex(hi), d)
                    r["bound"] = True
                    break
        if plain is not None:
            s = cover(pl, plain)
            if s:
                pa, psz, nm, t = s
                r["sym"] = nm
                if nm in an:
                    aa, asz, _ = an[nm]
                    r["asan"] = aa + (plain - pa)
                    r["rule"] = "SYMBOL"
                    r["ev"] = "symbol %s+0x%x (plain size %d, asan size %d)" % (nm, plain - pa, psz, asz)
        rows.append(r)

    # CODEREF: the same instruction, at the same offset inside the same function, in both images.
    # This OVERRIDES a SYMBOL row when musl's call is intercepted: in the ASan build the jal inside
    # musl's own code goes to the interceptor trampoline, not to musl's body, and GXA's call
    # contract has to sit on the object the code really jumps to.
    for r in rows:
        if r["plain"] is None or r.get("bound") or r["donor"] in NO_CODEREF:
            continue
        hits = []
        for nm in sorted(pref):
            for off, (kind, tgt) in pref[nm].items():
                if tgt != r["plain"]:
                    continue
                if off not in aref[nm] or aref[nm][off][0] != kind:
                    continue
                hits.append((nm, off, kind, aref[nm][off][1]))
        if not hits:
            continue
        tgts = {h[3] for h in hits}
        if len(tgts) != 1:
            r["coderef_conflict"] = [(h[0], hex(h[1]), h[2], hex(h[3])) for h in hits]
            continue
        a = hits[0][3]
        where = ", ".join("%s+0x%x" % (h[0], h[1]) for h in hits)
        if r["rule"] == "SYMBOL" and a == r["asan"]:
            r["ev"] += "; CODEREF agrees (%s %s)" % (hits[0][2], where)
            continue
        asym = cover(al, a)
        r["asan"], r["rule"] = a, "CODEREF"
        r["ev"] = "%s at %s in both images -> %s%s" % (
            hits[0][2], where, hex(a),
            (" = " + asym[2] + ("+0x%x" % (a - asym[0]) if a != asym[0] else "")) if asym else "")

    # CONTENT and GEOMETRY for what is left
    for r in rows:
        if r["asan"] is not None or r["plain"] is None or r.get("bound"):
            if r["asan"] is None and r["rule"] is None:
                r["rule"] = "OPEN"
            continue
        if r["donor"] == 0x35000:
            r["asan"], r["rule"] = page, "GEOMETRY"
            r["ev"] = "last PT_LOAD end %s rounded to a page" % hex(top_a)
            continue
        p = r["plain"]
        if not (pro[0] <= p < pro[0] + pro[1]):
            r["rule"] = "OPEN"
            continue
        for ln in (256, 128, 64, 32, 24, 16, 12, 10, 7):
            nb = rd(pd, ps, p, ln)
            if nb is None:
                continue
            hits, i = [], arob.find(nb)
            while i != -1 and len(hits) < 3:
                hits.append(aro[0] + i)
                i = arob.find(nb, i + 1)
            if len(hits) == 1:
                r["asan"], r["rule"] = hits[0], "CONTENT"
                r["ev"] = "unique in asan .rodata on %d bytes" % ln
                break
        if r["asan"] is None:
            r["rule"] = "OPEN"

    if opt.map_json:
        json.dump(rows, open(opt.map_json, "w"), indent=1)
    print("%-12s %5s %-10s %-10s %-9s %s" % ("donor", "uses", "plain", "asan", "rule", "evidence"))
    for r in rows:
        print("%-12s %5d %-10s %-10s %-9s %s" % (
            hex(r["donor"]), r["uses"], hex(r["plain"]) if r["plain"] else "-",
            hex(r["asan"]) if r["asan"] else "-", r["rule"], (r["ev"] or r["how"])[:96]))
        if "coderef_conflict" in r:
            print("       CONFLICT", r["coderef_conflict"])
    byrule = {}
    for r in rows:
        byrule[r["rule"]] = byrule.get(r["rule"], 0) + 1
    print("summary:", byrule)

    # the vfprintf call target of musl vsnprintf, for the second instance
    vsn_call = aref["vsnprintf"][[o for o, (k, t) in pref["vsnprintf"].items()
                                 if t == pn["vfprintf"][0] and k == "jal"][0]][1]
    vsn_sym = cover(al, vsn_call)
    head = []
    if opt.keep_head:
        with open(opt.out) as f:
            head = [next(f).rstrip("\n") for _ in range(opt.keep_head)]
    me = os.path.realpath(__file__)
    prov = ("(* Generated by %s (sha256 %s), adapted from omx-clap-core/fuzz_manifest's image table generator, from the"
            " unstripped twins of %s and %s (sha256 %s / %s; the published images are sha256 %s / %s),"
            " lib/CJ/RL/I/IImgP.v (sha256 %s) and fuzz_manifest's lib/CJ/RL/GXA (sha256 %s of its sha256sum list),"
            " with the core module %s; its CODEREF rule also reads `auipc rX; addi rY, rX, imm` with rY <> rX"
            " (printf_core+0x5ec forms \"(null)\" so); do not edit. *)" % (
                os.path.basename(me), sha256_file(me), opt.plain_name, opt.image_name,
                sha256_file(PLAIN + ".debug"), sha256_file(ASAN + ".debug"),
                sha256_file(opt.plain_published)[:8], sha256_file(opt.image_published)[:8],
                sha256_file(opt.iimgp), gxa_digest(opt.gxa), opt.core))
    emit(rows, iv, pn, an, vsn_call, vsn_sym[2] if vsn_sym else "?", opt, head + [prov])
    return rows


def emit(rows, iv, pn, an, vsn_call, vsn_name, opt, top):
    exact = [(r["donor"], r["asan"], r["rule"], r["ev"] or "") for r in rows if r["asan"] is not None]
    ivs = set()
    for r in rows:
        if r["rule"] != "SYMBOL" or r["sym"] is None:
            continue
        pa, psz, _ = pn[r["sym"]]
        aa = an[r["sym"]][0]
        for lo, hi, dd in iv:
            if pa <= lo + dd < pa + psz:
                # clip to the symbol's own extent: outside it the delta is another object's, and a
                # cross-image row must be keyed on SYMBOL + OFFSET, never on the bare address.
                hi_clipped = min(hi, lo + (pa + psz - (lo + dd)))
                ivs.add((lo, hi_clipped, aa + (lo + dd - pa) - lo, r["sym"]))
    ivs = sorted(ivs)
    OUT = opt.out
    L = list(top)
    L.append("(* The RImg instance of the ASan printf core (lib/CJ/RL/GXA) on the pinned %s." % opt.image_name)
    L.append("   GXA is general in the format (printf_core_a_stmt quantifies fmt and args) and proved (Qed,")
    L.append("   GXA/G_printf_core.v:1028 printf_core_a_proof, GXA/G_vfprintf_snf_closed.v:109")
    L.append("   vfprintf_snf_a_closed).  This file instantiates its image record on %s." % opt.image_name)
    L.append("")
    L.append("   HOW EACH ROW WAS DECIDED (never by value, never by a uniform delta):")
    L.append("     SYMBOL   the donor address is carried to fuzz_command.plain by the released IImgP map, and")
    L.append("              the plain address lies in a named symbol that the ASan image also has; the row keeps")
    L.append("              the offset inside the symbol.  The plain and ASan sizes agree on every such row.")
    L.append("              The interval rows below are clipped to the symbol's own extent for the same reason:")
    L.append("              a cross-image row is keyed on SYMBOL + OFFSET, never on the bare address, because")
    L.append("              .text, .rodata and .bss shift by different deltas between two builds.")
    L.append("     CODEREF  the object is named by the SAME instruction - same byte offset inside the same")
    L.append("              function of the chain, same opcode - in both images (auipc/addi, auipc/ld or jal).")
    L.append("     CONTENT  the plain object's bytes occur exactly once in the ASan .rodata.")
    L.append("     GEOMETRY an image bound (the last PT_LOAD end, rounded to a page).")
    L.append("   RT_IImgA_ok.v checks against the image (CodeAtT / RoB / RelCode / RelSym / RelNear / ZFact, by")
    L.append("   vm_compute) the rows its lemmas name; its header lists exactly which rows those are and which")
    L.append("   rows it does not check.")
    L.append("")
    L.append("   THE ASAN TRAP THIS FILE ENCODES: in an ASan build musl does not call musl.  The jal inside")
    L.append("   sn_write, __fwritex, printf_core, pad and fmt_fp goes to the link-time wrapper, so the rows")
    L.append("   for memcpy, memset, strnlen, wctomb and strerror name __wrap_* and GXA's CopyCall / SetCall /")
    L.append("   StrnlenCall contracts sit on the object the code really jumps to. *)")
    L.append("From Stdlib Require Import ZArith NArith List Lia Bool.")
    L.append("From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.")
    core_dir, core_mod = opt.core.rsplit(".", 1)
    L.append("From %s.lib.CJ.RL.Reloc Require Import RStep." % opt.prefix)
    L.append("From %s.%s Require Import %s." % (opt.prefix, core_dir, core_mod))
    L.append("From %s.lib.CJ.RL.I Require Export IInst." % opt.prefix)
    L.append("Import ListNotations.")
    L.append("Open Scope Z_scope.")
    L.append("")
    L.append("Notation KV a b := (a, b) (only parsing).")
    L.append("Notation KV3 a b c := (a, b, c) (only parsing).")
    L.append("")
    L.append("Definition A_exact : list (Z * Z) := [")
    for i, (d, a, rule, ev) in enumerate(sorted(exact)):
        L.append("  KV 0x%x 0x%x%s   (* %s: %s *)" % (d, a, ";" if i < len(exact) - 1 else "].", rule, ev[:110]))
    L.append("")
    L.append("Definition A_iv : list (Z * Z * Z) := [")
    for i, (lo, hi, d, nm) in enumerate(ivs):
        L.append("  KV3 0x%x 0x%x (%d)%s   (* %s *)" % (lo, hi, d, ";" if i < len(ivs) - 1 else "].", nm))
    L.append("")
    L.append("Definition A_sym (k : Z) : Z := tsym A_exact A_iv k.")
    L.append("Definition A_img : RImg := {| img_segs := tfibsegs; sym := A_sym |}.")
    L.append("")
    L.append("(* THE SECOND INSTANCE.  GXA's G_vsnprintf.v uses `sym 0x7f000400` as the call target of musl")
    L.append("   vsnprintf, and G_vfprintf_snf_closed.v uses the same symbol for musl vfprintf's body.  In an")
    L.append("   ASan image these are two objects: musl vsnprintf's jal goes to %s 0x%x (measured" % (vsn_name, vsn_call))
    L.append("   at vsnprintf's own call site), and the vfprintf interceptor runs before musl vfprintf's body.")
    L.append("   Both GXA sections are parametric in IMG, so vsnprintf is instantiated at A_img_vsn and the")
    L.append("   vfprintf body at A_img; the two agree on every other row (A_sym_vsn_agree), and the")
    L.append("   interceptor's own walk is what joins vsnprintf's hypothesis to the closed body. *)")
    L.append("Definition A_exact_vsn : list (Z * Z) := (0x7f000400, 0x%x) :: A_exact." % vsn_call)
    L.append("Definition A_sym_vsn (k : Z) : Z := tsym A_exact_vsn A_iv k.")
    L.append("Definition A_img_vsn : RImg := {| img_segs := tfibsegs; sym := A_sym_vsn |}.")
    L.append("Lemma A_sym_vsn_agree : forall k, k <> 0x7f000400 -> A_sym_vsn k = A_sym k.")
    L.append("Proof. intros k Hk. unfold A_sym_vsn, A_sym, tsym, A_exact_vsn. cbn [zlookup]. "
             "destruct (Z.eqb_spec k 0x7f000400); [contradiction | reflexivity]. Qed.")
    L.append("")
    L.append("(* The keys no rule pairs, left on the identity.  Each line says how IImgP treats the key: the")
    L.append("   END of an IImgP interval [lo,hi) (the intervals are half-open, so the key lies outside it, and")
    L.append("   the plain address hi + d is not paired with whatever object starts there), unmapped (IImgP has")
    L.append("   no row for it), or an interval no rule carries on to this image.  None is named by any image")
    L.append("   fact of the closure, which RT_IImgA_ok.v checks. *)")
    for r in rows:
        if r["asan"] is None:
            L.append("(* OPEN donor 0x%x (%d uses): %s *)" % (r["donor"], r["uses"], (r["ev"] or r["how"])[:100]))
    open(OUT, "w").write("\n".join(L) + "\n")
    print("wrote %s: %d exact rows, %d interval rows, %d open"
          % (OUT, len(exact), len(ivs), sum(1 for r in rows if r["asan"] is None)))


if __name__ == "__main__":
    main()
