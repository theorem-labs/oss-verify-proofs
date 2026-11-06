#!/usr/bin/env python3
"""By-value check of libdiginet/fuzz_transport's relocated image-A core files (row TCA, new asan pin e89be137db17).

libdiginet/fuzz_decode's decval.py (sha256 b0b5ced070ea; internal record), itself
libdiginet/fuzz_frame's, reac-repacer/fuzz_uci's, adapted from libreac/fuzz_decode's decval.py (sha256 43527d3edbc2).
The decision tree per numeral is that script's, unchanged; only the inputs and the range differ:

  target image  fuzz_transport.asan (the libdiginet build; sha256 e89be137db17...; symbols from the
                unstripped twin 86efc3a80314..., bytes from the stripped image of record)
  donor image   fuzz_grant.asan (the libreac build; sha256 c2c7559b...; symbols from the unstripped twin)
  donor text    the run directory's stage/ (fuzz_grant's released text, module paths renamed; same file names)
  relocated     the staged files of a port_core run directory: <rundir>/stage-out/A/*.v and
                <rundir>/stage-out/Reusable/*.v, minus EV/not-relocated-startup-layer.txt (EV, required) and
                EV/taken-by-path.txt when present

For every numeral (decimal or hex) in the relocated files whose value lies in [0x10000, max(donor, target page-up top)]
(the target image ends ABOVE the donor's, 0x6153d0 against 0x5f93b0, so D9's donor range [0x10000, 0x5f93b0) would leave
target-only values unchecked), decide whether the value is the TARGET image's, the DONOR's, the same in both (SHARED), or
not an address (OTHER).  Read-only: nothing is written to the run directory or any checkout.


  usage: decval.py <rundir> [--out <tsv>] [--review <tsv>]   (env P, PG, EV required: no host path is written here)

  P     fuzz_transport's images (result/bin/fuzz_transport/, unstripped/fuzz_transport/), pin e89be137db17
  PG    fuzz_grant's ORIGINAL images (bin/ and unstripped/), pin c2c7559b29bd
  CORE  the tree read: <rundir>/stage-out (A/, Reusable/); DONT the donor text: <rundir>/stage

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
import hashlib
import os
import re
import sys
from collections import Counter, defaultdict

from elftools.elf.elffile import ELFFile

def _need(name):
    v = os.environ.get(name)
    if not v:
        sys.exit("decval: set %s (P, PG and EV are required)" % name)
    return v


P = _need("P")
PG = _need("PG")
CFG = dict(
    tgt_syms=os.path.join(P, "unstripped/fuzz_transport/fuzz_transport.asan"),
    tgt_bytes=os.path.join(P, "result/bin/fuzz_transport/fuzz_transport.asan"),
    don_syms=os.path.join(PG, "unstripped/fuzz_grant/fuzz_grant.asan"),
    don_bytes=os.path.join(PG, "bin/fuzz_grant/fuzz_grant.asan"),
    core=os.environ.get("CORE", ""),
    dont=os.environ.get("DONT", ""),
    ev=_need("EV"),
)
PINS = {"tgt_syms": "86efc3a80314", "tgt_bytes": "e89be137db17", "don_syms": "57c26f993615", "don_bytes": "c2c7559b29bd"}


def setup(args):
    """CFG with CORE / DONT taken from a leading <rundir> argument (its stage-out/ and stage/); images checked against PINS."""
    cfg = dict(CFG)
    if args and not args[0].startswith("--"):
        cfg["core"] = os.path.join(args[0], "stage-out")
        cfg["dont"] = os.path.join(args[0], "stage")
    for k in ("core", "dont"):
        assert cfg[k] and os.path.isdir(cfg[k]), "%s is not a directory: %r (give <rundir>)" % (k, cfg[k])
    for k, want in PINS.items():
        got = hashlib.sha256(open(cfg[k], "rb").read()).hexdigest()[:12]
        assert got == want, "%s is %s, not the pinned %s" % (cfg[k], got, want)
    return cfg


NUM = re.compile(r"(?<![A-Za-z0-9_])(?:0x[0-9a-fA-F]+|\d+)(?![A-Za-z0-9_])")
WDEF = re.compile(r"^Definition (W[A-Za-z0-9_]*) : bv (\d+) := (0x[0-9a-fA-F]+)\.")
FLEM = re.compile(r"fetch_(?:word|half)\s+\S+\s*\((0x[0-9a-fA-F]+) : word\) = Some (W[A-Za-z0-9_]*)")
TFIB = re.compile(r"Definition tfib_([AE])_([A-Za-z0-9_$]+?) : Z := (0x[0-9a-fA-F]+|\d+)\.")
ADDRROLE = re.compile(
    r"(a_entry|rw_lo|rw_len|img_hi|img_lo|shadow_off|x_[a-z_]+|sniff_tab|sniff_cell"
    r"|stops_more|ph_addr_z|TEXT_LO)\s*:=|Definition\s+\w+\s*:\s*(?:Z|list Z)\s*:="
)


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
    """(path in the core tree, path of the donor file it was relocated from): every staged A/*.v and Reusable/*.v of
    the run's stage-out (port_core --apply's rule copies them to lib/A and lib/Reusable), minus the start-up layer and
    the files taken by path; the donor text of X is the run's stage/X (fuzz_grant's text, module paths renamed)."""
    core, ev = cfg["core"], cfg["ev"]
    rd = lambda p: [l.strip() for l in open(p) if l.strip() and not l.startswith("#")] if os.path.exists(p) else []
    skip = set(rd(ev + "/not-relocated-startup-layer.txt")) | set(rd(ev + "/taken-by-path.txt"))
    skip |= {"Reusable/" + s for s in skip if not s.startswith(("A/", "Reusable/"))}
    out = []
    for sub in ("A", "Reusable"):
        for fn in sorted(os.listdir(os.path.join(core, sub))):
            if fn.endswith(".v") and sub + "/" + fn not in skip:
                out.append((sub + "/" + fn, os.path.join(cfg["dont"], sub, fn)))
    for t, d in out:
        assert os.path.exists(os.path.join(core, t)), t
        assert os.path.exists(d), d
    return out


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
    args = sys.argv[1:]
    cfg = setup(args)
    out_tsv = args[args.index("--out") + 1] if "--out" in args else None
    rev_tsv = args[args.index("--review") + 1] if "--review" in args else None
    tgt, don = Img(cfg["tgt_syms"], cfg["tgt_bytes"]), Img(cfg["don_syms"], cfg["don_bytes"])
    rel = file_list(cfg)
    nA = sum(1 for t, d in rel if t.startswith("A/"))
    # the range: every value from the first loaded byte up to both images' page-rounded tops (included)
    LO, HI = min(don.lo, tgt.lo), max(don.top_up, tgt.top_up) + 1

    # 1. every Definition W_x / fetch_word pair, read out of the target image
    wmap = {}
    for dirpath, _, fns in os.walk(cfg["core"]):
        for fn in sorted(fns):
            if fn.endswith(".v"):
                for l in open(os.path.join(dirpath, fn), errors="ignore"):
                    m = WDEF.match(l.strip())
                    if m:
                        wmap.setdefault(m.group(1), (int(m.group(3), 16), int(m.group(2))))
    pairs = bad_pairs = 0
    fetch_ok = set()   # (file, line) whose every fetch pair verified
    fetch_bad = set()
    w_ok = set()       # W names with a verified pair
    for t, dp in rel:
        for i, l in enumerate(open(os.path.join(cfg["core"], t)).read().splitlines()):
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

    # 2. the tfib_A_ / tfib_E_ symbol table (A/AB1w.v)
    tf = Counter()
    tfbad, tfint = [], []
    tbl = os.path.join(cfg["core"], "A/AB1w.v")
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
        d, c, pr = align(dp, os.path.join(cfg["core"], t))
        for j, line in enumerate(c):
            tk = toks(line)
            if not tk:
                continue
            dtk = toks(d[pr[j]]) if j in pr else None
            for idx, s in enumerate(tk):
                v = val(s)
                if not (LO <= v < HI):
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

    print("relocated files: %d (A %d, Reusable %d); %d numerals in [%s, %s) (in D9's donor range [%s, %s): %d)" % (
        len(rel), nA, len(rel) - nA, len(rows), hex(LO), hex(HI), hex(don.lo), hex(don.top),
        sum(1 for r in rows if don.lo <= r[3] < don.top)))
    print("target top %s (page-up %s, rw_lo %s); donor top %s (page-up %s, rw_lo %s)" % (
        hex(tgt.top), hex(tgt.top_up), hex(tgt.rw_lo), hex(don.top), hex(don.top_up), hex(don.rw_lo)))
    print("fetch/word pairs verified against the target image: %d, mismatches %d" % (pairs, bad_pairs))
    print("tfib_A_/tfib_E_ rows: %s" % dict(tf), "donor rows:", tfbad)
    print("tfib interior rows:", tfint)
    print("classes:", dict(Counter(r[4] for r in rows)))
    print("reasons:", dict(Counter((r[4], r[5]) for r in rows)))
    print("review rows:", dict(Counter(x[0].split(":")[0] for x in review)))
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
