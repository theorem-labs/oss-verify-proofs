#!/usr/bin/env python3
"""By-value check of reac-repacer/fuzz_wire's image-B __asan_memmove files (lib/B/Rt/MemmoveDef.v, MemmoveIm.v,
MemmoveK.v, MemmovePaths.v, Memmove.v).

fuzz_uci's stackmalloc1-B/gates/decval-sm1.py (itself core-B's gates/decval-B.py, the image-B core's check of record)
with only the inputs changed; the decision tree per numeral is unchanged:

  target image  fuzz_wire.asan-ubsan  (sha256 af4534831a45; symbols from the unstripped twin 51eb4bef2425, bytes from
                the stripped image of record)
  donor image   fuzz_pcap.asan-ubsan  (sha256 9e66f771f22a; symbols from the unstripped twin c969d83cdd59)
  donor text    fuzz_pcap's released lib/B/Rt/Memmove*.v (recipes 5098883da0b) with its module paths renamed
                (run-gates.sh's DON tree: --don <dir>/B/Rt/<name>.v)
  relocated     the five files, read from --lib <dir>/B/Rt/<name>.v (the committed files, or a planted copy)
  environment   WIRE_BIN (fuzz_wire.asan-ubsan and .unstripped), PCAP_PIN / PCAP_TWIN (fuzz_pcap.asan-ubsan pin /
                twin); --core-lib is the unit's lib (projects/reac-repacer/fuzz_wire/proofs/lib), read for every
                `Definition W_x` (the fetch-pair check) and lib/B/YB1w.v (the tfib table), with the five files
                taken from --lib instead

The option --declare VALUE:REGEX=REASON (decval-sm1.py's) names a numeral that is no address; the run of record
declares none.

For every numeral (decimal or hex) in the relocated files whose value lies in [0x10000, donor image top),
decide whether the value is the TARGET image's (decode's class "DECODE"), the DONOR's, the same in both
(SHARED), or not an address (OTHER).  Read-only: nothing is written to any checkout.

  usage: decval-mm.py --lib <dir> --don <dir> --core-lib <lib> [--out <tsv>] [--review <tsv>] [--declare ...]

Evidence used, per occurrence (as the decode script):
  * donor-file alignment  - the donor file the core file was relocated from, aligned line by line after
    masking every numeral; a numeral is UNMOVED when the aligned donor token holds the same value.
  * image bytes           - every `Definition W_x : bv N := 0x..` / `fetch_word .. (0xA : word) = Some W_x`
    pair is read out of the target ELF and compared.
  * symbol / section / segment values of both ELFs (st_value, st_value+st_size, section and PT_LOAD bounds
    and their page roundings, PT_PHDR vaddr, __global_pointer$, builtin_tls and builtin_tls+200 = tp).

Added for this pass (they never change a class; they list rows for a by-hand decision):
  * every row whose value is a donor image value and not a target image value, whatever its class;
  * every unmoved non-comment row whose value lies strictly inside a sized donor symbol whose same-named
    twin in the target sits at a different address (a possible donor interior address);
  * the fetch/word rows whose pair is not verified in the relocated set.
"""
import bisect
import difflib
import os
import re
import sys
from collections import Counter, defaultdict

from elftools.elf.elffile import ELFFile

FIVE = ["MemmoveDef", "MemmoveIm", "MemmoveK", "MemmovePaths", "Memmove"]
CFG = dict(
    tgt_syms=os.environ["WIRE_BIN"] + "/fuzz_wire.asan-ubsan.unstripped",
    tgt_bytes=os.environ["WIRE_BIN"] + "/fuzz_wire.asan-ubsan",
    don_syms=os.environ["PCAP_TWIN"] + "/fuzz_pcap.asan-ubsan",
    don_bytes=os.environ["PCAP_PIN"] + "/fuzz_pcap.asan-ubsan",
    lib="",
    donlib="",
    corelib="",
)

NUM = re.compile(r"(?<![A-Za-z0-9_])(?:0x[0-9a-fA-F]+|\d+)(?![A-Za-z0-9_])")
WDEF = re.compile(r"^Definition (W[A-Za-z0-9_]*) : bv (\d+) := (0x[0-9a-fA-F]+)\.")
FLEM = re.compile(r"fetch_(?:word|half)\s+\S+\s*\((0x[0-9a-fA-F]+) : word\) = Some (W[A-Za-z0-9_]*)")
TFIB = re.compile(r"Definition tfib_([AE])_([A-Za-z0-9_$]+?) : Z := (0x[0-9a-fA-F]+|\d+)\.")
ADDRROLE = re.compile(
    r"(a_entry|rw_lo|rw_len|img_hi|img_lo|shadow_off|x_[a-z_]+|sniff_tab|sniff_cell"
    r"|stops_more|ph_addr_z|TEXT_LO)\s*:=|Definition\s+\w+\s*:\s*(?:Z|list Z)\s*:="
)


DECLARED = []  # (value, line regex, reason) from --declare


class Img:
    def __init__(self, sympath, bytepath):
        with open(sympath, "rb") as f:
            e = ELFFile(f)
            self.syms = {}
            self.allsyms = []  # (value, size, name) for reporting
            for sec in (".symtab", ".dynsym"):
                s = e.get_section_by_name(sec)
                if s is None:
                    continue
                for sym in s.iter_symbols():
                    if sym.name and sym["st_value"]:
                        self.syms.setdefault(sym.name, (sym["st_value"], sym["st_size"]))
                        self.allsyms.append((sym["st_value"], sym["st_size"], sym.name))
            self.secs = [(s.name, s["sh_addr"], s["sh_size"]) for s in e.iter_sections() if s["sh_addr"]]
            self.phdr = None
            loads = []
            for sg in e.iter_segments():
                if sg["p_type"] == "PT_LOAD":
                    loads.append((sg["p_vaddr"], sg["p_memsz"]))
                elif sg["p_type"] == "PT_PHDR":
                    self.phdr = sg["p_vaddr"]
        with open(bytepath, "rb") as f:
            e = ELFFile(f)
            self.loads = [(sg["p_vaddr"], sg["p_memsz"], sg.data()) for sg in e.iter_segments()
                          if sg["p_type"] == "PT_LOAD"]
        assert [(v, m) for v, m, d in self.loads] == loads, "stripped / unstripped PT_LOAD differ"
        self.lo = min(v for v, m, d in self.loads)
        self.top = max(v + m for v, m, d in self.loads)
        self.values = set()
        self.why = defaultdict(set)  # value -> how it is an image value (for the report)
        for n, (a, sz) in self.syms.items():
            self.values.add(a)
            self.values.add(a + sz)
        for a, sz, n in self.allsyms:
            self.why[a].add(n)
            if sz:
                self.why[a + sz].add(n + "+size")
        for n, a, sz in self.secs:
            self.values.add(a)
            self.values.add(a + sz)
            self.why[a].add("sec:" + n + ".lo")
            self.why[a + sz].add("sec:" + n + ".hi")
        for i, (v, m, d) in enumerate(sorted(self.loads)):
            for x, w in ((v, "lo"), (v + m, "hi"), (v & ~0xFFF, "lo&~fff"), ((v + m + 0xFFF) & ~0xFFF, "hi-pageup")):
                self.values.add(x)
                self.why[x].add("PT_LOAD%d.%s" % (i, w))
        top_up = (self.top + 0xFFF) & ~0xFFF
        rw_lo = sorted((v, m) for v, m, d in self.loads)[-2]
        rw_lo = rw_lo[0] + rw_lo[1]
        self.top_up, self.rw_lo = top_up, rw_lo
        self.values.update({top_up, rw_lo, top_up - rw_lo})
        self.why[top_up].add("img_top(pageup)")
        self.why[rw_lo].add("rw_lo")
        self.why[top_up - rw_lo].add("rw_len=img_top-rw_lo")
        if self.phdr:
            self.values.add(self.phdr)
            self.why[self.phdr].add("PT_PHDR")
        bt = self.syms.get("builtin_tls")
        self.tls = bt
        if bt:
            self.values.update({bt[0], bt[0] + 200})
            self.why[bt[0] + 200].add("tp=builtin_tls+200")
        self.sized = sorted((a, sz, n) for a, sz, n in self.allsyms if sz)
        self.sized_starts = [a for a, sz, n in self.sized]

    def word(self, addr, n=4):
        for v, m, d in self.loads:
            if v <= addr < v + m:
                b = d[addr - v: addr - v + n]
                return int.from_bytes(b + b"\0" * (n - len(b)), "little")
        return None

    def inside(self, v):
        """sized symbols with st_value < v < st_value+st_size (strict interior)."""
        out = []
        i = bisect.bisect_left(self.sized_starts, v)
        # look back over symbols that may cover v
        j = i - 1
        while j >= 0 and j > i - 400:
            a, sz, n = self.sized[j]
            if a < v < a + sz:
                out.append((n, a, sz))
            j -= 1
        return out


def toks(line):
    return [m.group(0) for m in NUM.finditer(line)]


def val(s):
    return int(s, 16) if s.startswith("0x") else int(s)


def align(dpath, cpath):
    d = open(dpath).read().splitlines()
    c = open(cpath).read().splitlines()
    sm = difflib.SequenceMatcher(None, [NUM.sub("#", x) for x in d], [NUM.sub("#", x) for x in c], autojunk=False)
    pairs = {}
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            for k in range(i2 - i1):
                pairs[j1 + k] = i1 + k
    return d, c, pairs


def file_list(cfg):
    """(path in the unit's tree, path of the donor file it was relocated from)."""
    out = [("lib/B/Rt/%s.v" % n, os.path.join(cfg["donlib"], "B/Rt/%s.v" % n)) for n in FIVE]
    for t, d in out:
        assert os.path.exists(cpath(cfg, t)), t
        assert os.path.exists(d), d
    return out


def cpath(cfg, t):
    """the file read for unit path t: one of the five from --lib, any other from --core-lib."""
    if t in {"lib/B/Rt/%s.v" % n for n in FIVE}:
        return os.path.join(cfg["lib"], t[len("lib/"):])
    return os.path.join(cfg["corelib"], t[len("lib/"):])


def role(line):
    s = line.strip()
    if s.startswith("(*") or s.startswith("*"):
        return "comment"
    if "fetch_word" in line or "fetch_half" in line:
        return "fetch"
    if re.search(r"bv \d+ := 0x", line):
        return "word"
    if "decode_any" in line or "decode_c" in line:
        return "decode"
    return "other"


def main():
    cfg = dict(CFG)
    args = sys.argv[1:]
    for opt, key in (("--lib", "lib"), ("--don", "donlib"), ("--core-lib", "corelib")):
        cfg[key] = args[args.index(opt) + 1]
    out_tsv = args[args.index("--out") + 1] if "--out" in args else None
    rev_tsv = args[args.index("--review") + 1] if "--review" in args else None
    for k, a in enumerate(args):
        if a == "--declare":
            # --declare VALUE:REGEX=REASON (added for this slice; the decision tree is unchanged): a numeral of VALUE on a
            # non-comment line matching REGEX is no address; the row is classed OTHER with the reason, and counted
            spec, why = args[k + 1].split("=", 1)
            v_, rx = spec.split(":", 1)
            DECLARED.append((int(v_, 0), re.compile(rx), why))
    tgt, don = Img(cfg["tgt_syms"], cfg["tgt_bytes"]), Img(cfg["don_syms"], cfg["don_bytes"])
    rel = file_list(cfg)
    nA = sum(1 for t, d in rel if t.startswith("lib/B/"))

    # 1. every Definition W_x / fetch_word pair, read out of the target image
    wmap = {}
    vfiles = []
    for dirpath, _, fns in os.walk(cfg["corelib"]):
        for fn in sorted(fns):
            if fn.endswith(".v"):
                vfiles.append("lib/" + os.path.relpath(os.path.join(dirpath, fn), cfg["corelib"]))
    for t in vfiles:
        for l in open(cpath(cfg, t), errors="ignore"):
            m = WDEF.match(l.strip())
            if m:
                wmap.setdefault(m.group(1), (int(m.group(3), 16), int(m.group(2))))
    pairs = bad_pairs = 0
    fetch_ok = set()   # (file, line) whose every fetch pair verified
    fetch_bad = set()
    w_ok = set()       # W names with a verified pair
    for t, dp in rel:
        for i, l in enumerate(open(cpath(cfg, t)).read().splitlines()):
            for m in FLEM.finditer(l):
                if m.group(2) not in wmap:
                    continue
                w, bits = wmap[m.group(2)]
                got = tgt.word(int(m.group(1), 16))
                pairs += 1
                if got is None or got & (0xFFFF if bits == 16 else 0xFFFFFFFF) != w:
                    bad_pairs += 1
                    fetch_bad.add((t, i + 1))
                    print("FETCH-MISMATCH\t%s:%d\t%s\t%s" % (t, i + 1, m.group(1), hex(w)))
                else:
                    fetch_ok.add((t, i + 1))
                    w_ok.add(m.group(2))

    # 2. the tfib_A_ / tfib_E_ symbol table (B/YB1w.v)
    tf = Counter()
    tfbad, tfint = [], []
    tbl = cpath(cfg, "lib/B/YB1w.v")
    dstart = {a for a, sz in tgt.syms.values()}
    dend = {a + sz for a, sz in tgt.syms.values()}
    ostart = {a for a, sz in don.syms.values()}
    oend = {a + sz for a, sz in don.syms.values()}
    for i, l in enumerate(open(tbl).read().splitlines()):
        for m in TFIB.finditer(l):
            v = int(m.group(3), 0)
            want, other = (dstart, ostart) if m.group(1) == "A" else (dend, oend)
            if v in want:
                tf["tgt"] += 1
            elif v in other:
                tf["DONOR"] += 1
                tfbad.append((i + 1, m.group(0)))
            else:
                tf["interior"] += 1
                tfint.append((i + 1, m.group(0)))

    # 3. every numeral in the donor's address range
    rows = []
    review = []
    for t, dp in rel:
        d, c, pr = align(dp, cpath(cfg, t))
        for j, line in enumerate(c):
            tk = toks(line)
            if not tk:
                continue
            dtk = toks(d[pr[j]]) if j in pr else None
            for idx, s in enumerate(tk):
                v = val(s)
                if not (don.lo <= v < don.top):
                    continue
                unmoved = (val(dtk[idx]) == v) if (dtk is not None and len(dtk) == len(tk)) else None
                donor_tok = dtk[idx] if (dtk is not None and len(dtk) == len(tk)) else ""
                r = role(line)
                de, dn = v in tgt.values, v in don.values
                if r in ("word", "fetch"):
                    cls, why = "TARGET", "fetch/word pair verified against the target image"
                elif r == "decode":
                    cls, why = "OTHER", "decoded field of a verified instruction word"
                elif r == "comment":
                    cls = "OTHER"
                    why = "comment numeral, names the donor value by design" if dn else "comment numeral"
                elif any(v == dv_ and dre.search(line) for dv_, dre, _ in DECLARED):
                    cls = "OTHER"
                    why = "declared not an address: " + next(w for dv_, dre, w in DECLARED if v == dv_ and dre.search(line))
                elif de and dn and unmoved is not False:
                    cls, why = "SHARED", "same value in both images"
                elif de:
                    cls, why = "TARGET", "target symbol/section/segment value" + (
                        "; coincides with a donor value but the relocation moved it here" if dn else "")
                elif dn and unmoved:
                    cls, why = "DONOR-STALE", "donor image value, unmoved from the donor file"
                elif unmoved and s.startswith("0x") and ADDRROLE.search(line):
                    cls, why = "DONOR-STALE", "address-role field, unmoved from the donor file, no target value"
                else:
                    cls, why = "OTHER", "no address role (constant / count / label / instruction word)"
                row = (t, j + 1, s, v, cls, why, unmoved, donor_tok, line.strip()[:200])
                rows.append(row)
                # by-hand review lists (never change the class)
                if cls != "DONOR-STALE":
                    if dn and not de:
                        review.append(("donor-value-not-target",) + row)
                    elif r == "fetch" and (t, j + 1) not in fetch_ok:
                        review.append(("fetch-line-not-verified",) + row)
                    elif r == "word":
                        m = WDEF.match(line.strip())
                        if m and m.group(1) not in w_ok:
                            review.append(("word-without-verified-pair",) + row)
                    elif r != "comment" and unmoved and not de:
                        ins = don.inside(v)
                        moved = [(n, a, sz) for n, a, sz in ins
                                 if n in tgt.syms and tgt.syms[n][0] != a]
                        if moved:
                            n, a, sz = min(moved, key=lambda x: x[2])
                            review.append(("donor-interior-unmoved:%s+0x%x(sz 0x%x)->tgt 0x%x" % (
                                n, v - a, sz, tgt.syms[n][0]),) + row)

    print("relocated files: %d (lib/B %d, other %d); %d numerals in [%s, %s)" % (
        len(rel), nA, len(rel) - nA, len(rows), hex(don.lo), hex(don.top)))
    print("target top %s (page-up %s, rw_lo %s); donor top %s (page-up %s, rw_lo %s)" % (
        hex(tgt.top), hex(tgt.top_up), hex(tgt.rw_lo), hex(don.top), hex(don.top_up), hex(don.rw_lo)))
    print("fetch/word pairs verified against the target image: %d, mismatches %d" % (pairs, bad_pairs))
    print("tfib_A_/tfib_E_ rows: %s" % dict(tf), "donor rows:", tfbad)
    print("tfib interior rows:", tfint)
    print("classes:", dict(Counter(r[4] for r in rows)))
    print("reasons:", dict(Counter((r[4], r[5]) for r in rows)))
    print("review rows:", dict(Counter(x[0].split(":")[0] for x in review)))
    print("declared rows:", sum(1 for r in rows if r[5].startswith("declared")))
    for r in rows:
        if r[5].startswith("declared"):
            print("DECLARED\t%s:%d\t%s\t%s" % (r[0], r[1], r[2], r[8][:110]))
    for r in rows:
        if r[4] == "DONOR-STALE":
            print("DONOR-STALE\t%s:%d\t%s\t%s" % (r[0], r[1], r[2], r[8][:110]))
    if out_tsv:
        with open(out_tsv, "w") as f:
            f.write("file\tline\ttoken\tvalue\tclass\treason\tunmoved\tdonor_token\tsource\n")
            for r in rows:
                f.write("\t".join(str(x) for x in r) + "\n")
    if rev_tsv:
        with open(rev_tsv, "w") as f:
            f.write("review\tfile\tline\ttoken\tvalue\tclass\treason\tunmoved\tdonor_token\tsource\n")
            for r in review:
                f.write("\t".join(str(x) for x in r) + "\n")


if __name__ == "__main__":
    main()
