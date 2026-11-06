#!/usr/bin/env python3
"""Regenerate the per-row tool outputs and the derived tables of this directory that are kept outside the repository.

Usage, from the repository root:  reproduce.py PINNED TWINS TOOLS OUT
  PINNED  the pinned (stripped) images fuzz_boxreg.plain / fuzz_boxreg.ubsan (sha256 in README.md)
  TWINS   their unstripped twins fuzz_boxreg.plain / fuzz_boxreg.ubsan (sha256 in README.md)
  TOOLS   one directory per tools-registry directory tools/yh03check/<dir>/, each with its yh03check.py and
          yh03regen.py: e5d7cbda4e27 (v6.3), 5e92f52b8caa, ca63d81d7725, 09f5eb289e5e
  OUT     an empty directory; the files are written under OUT/yh03/ with the names README.md lists
Needs pyelftools for the tools. Each run works on the YH03.v files of the commit README.md names, taken with
`git archive` into a scratch tree under OUT/trees/, and is run from that tree's root, so the file labels in the
outputs are repository paths. Prints the sha256 of each file written.
"""
import hashlib
import io
import os
import re
import shutil
import subprocess
import sys
import tarfile

UNIT = "proofs/libreac/fuzz_boxreg"
FILES = {"plain": f"{UNIT}/lib/Reusable/YH03.v", "ubsan": f"{UNIT}/lib/U/Reusable/YH03.v"}
TAGS = {"plain": "lib/Reusable/YH03.v", "ubsan": "lib/U/Reusable/YH03.v"}
GOT = {"plain": "0x1d260", "ubsan": "0x1d660"}   # gotfix.<side>.diff
BEFORE, SUPERSEDED, RECORD, RELEASED = "b5dd72116a44", "0dbfaec69fb2", "a60f6b380c99", "b2e59f3b3308"


def sh(cmd, cwd=None, out=None):
    with open(out, "wb") if out else open(os.devnull, "wb") as o:
        subprocess.run(cmd, cwd=cwd, stdout=o, stderr=subprocess.DEVNULL, check=False)


def git(*args):
    return subprocess.run(["git", *args], check=True, capture_output=True).stdout


def tree(base, name, rev, paths):
    d = os.path.join(base, "trees", name)
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d)
    with tarfile.open(fileobj=io.BytesIO(git("archive", rev, "--", *paths))) as t:
        t.extractall(d)
    return d


def small(base, name, rev):
    return tree(base, name, rev, [f"projects/libreac/fuzz_boxreg/harness.yaml", *FILES.values()])


def main():
    pinned, twins, tools, out = (os.path.abspath(a) for a in sys.argv[1:5])
    o = os.path.join(out, "yh03")
    os.makedirs(os.path.join(o, "4e9a57e74cac"), exist_ok=True)
    py = sys.executable
    tool = lambda d, f: os.path.join(tools, d, f)
    pin = lambda s: f"{pinned}/fuzz_boxreg.{s}"
    twin = lambda s: f"{twins}/fuzz_boxreg.{s}"
    written = []

    def w(rel):
        written.append(rel)
        return os.path.join(o, rel)

    before, superseded, record = small(out, "before", BEFORE), small(out, "superseded", SUPERSEDED), small(out, "record", RECORD)
    for s, f in FILES.items():
        # v6.3: checks before / after, the regen of record, its readers run
        for when, d in (("before", before), ("after", record)):
            sh([py, tool("e5d7cbda4e27", "yh03check.py"), "--pinned", pin(s), twin(s), f], d, w(f"check-e5d7cbda4e27.{when}.{s}.rows"))
        g = small(out, f"gotfixed-{s}", BEFORE)
        p = os.path.join(g, f)
        t = open(p).read()
        t2 = re.sub(r"(Definition src0_D_got_DYNAMIC_reserved : Z := )0x1ed90\.", rf"\g<1>{GOT[s]}.", t)
        assert t2 != t
        open(p, "w").write(t2)
        sh([py, tool("e5d7cbda4e27", "yh03regen.py"), "/dev/null", f, "--syms-elf", twin(s), "--pinned", pin(s), "--elf", pin(s),
            "--unchecked-ok", "--write", "--report", w(f"regen-f357a8df6e49.{s}.report.tsv")], g)
        assert open(p, "rb").read() == git("show", f"{RECORD}:{f}"), f"regen of record output differs from {RECORD}: {f}"
        r = tree(out, f"readers-{s}", RECORD, [UNIT, "projects/libreac/fuzz_boxreg"])
        sh([py, tool("e5d7cbda4e27", "yh03regen.py"), "/dev/null", f, "--syms-elf", twin(s), "--pinned", pin(s), "--elf", pin(s),
            "--unchecked-ok", "--proofs", UNIT, "--report", w(f"regen-f357a8df6e49-readers.{s}.report.tsv")], r)
        # 4e9a57e74cac/: the superseded run's checks and regens
        for chk in ("5e92f52b8caa", "ca63d81d7725", "09f5eb289e5e"):
            pre = ["--pinned", pin(s)] if chk == "5e92f52b8caa" else []
            for when, d in (("before", before), ("after", superseded)):
                sh([py, tool(chk, "yh03check.py"), *pre, twin(s), f], d, w(f"4e9a57e74cac/check-{chk}.{when}.{s}.rows"))
        for d_, ver in (("5e92f52b8caa", "4e9a57e74cac"), ("09f5eb289e5e", "b05e25845c37")):
            g = small(out, f"regen-{ver}-{s}", BEFORE)
            pre = ["--pinned", pin(s)] if ver == "4e9a57e74cac" else []   # b05e25845c37 has no --pinned
            sh([py, tool(d_, "yh03regen.py"), "/dev/null", f, "--elf", pin(s), "--syms-elf", twin(s), *pre,
                "--zero-absent", "--unchecked-ok", "--write", "--report", w(f"4e9a57e74cac/regen-{ver}.{s}.report.tsv")], g)
    derived(o, w)
    for rel in written:
        print(hashlib.sha256(open(os.path.join(o, rel), "rb").read()).hexdigest(), rel)


def cellvals(text):
    return {m.group(1): m.group(2) for m in re.finditer(r"Definition (src0_[ADE]_\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.", text)}


def table(path):
    d = {}
    for line in open(path):
        p = line.rstrip("\n").split("\t")
        if len(p) >= 3:
            d[p[1]] = p
    return d


def read_cells(rev, s):
    """Cells of rev's YH03.v (the first definition on each line) that a .v other than the two YH03.v names."""
    defs = set()
    for line in git("show", f"{rev}:{FILES[s]}").decode().splitlines():
        m = re.search(r"Definition (src0_[ADE]_[A-Za-z0-9_]+)", line)
        if m:
            defs.add(m.group(1))
    used = set()
    out = subprocess.run(["git", "grep", "-h", "-o", "-w", "-E", r"src0_[ADE]_[A-Za-z0-9_]+", rev, "--", f"{UNIT}/*.v",
                          f":!{FILES['plain']}", f":!{FILES['ubsan']}"], capture_output=True, text=True).stdout
    for line in out.splitlines():
        used.add(line.split(":", 1)[1] if line.startswith(rev + ":") else line)
    return defs & used


def readers(rev, name):
    out = subprocess.run(["git", "grep", "-n", "-w", name, rev, "--", f"{UNIT}/*.v", f":!{FILES['plain']}",
                          f":!{FILES['ubsan']}"], capture_output=True, text=True).stdout
    return [l.split(":")[1] + ":" + l.split(":")[2] for l in out.splitlines() if l.strip()]


def derived(o, w):
    # diff-vs-0dbfaec69fb2.diff
    d = b""
    for s in ("plain", "ubsan"):
        a, b = os.path.join(o, f".a.{s}"), os.path.join(o, f".b.{s}")
        open(a, "wb").write(git("show", f"{SUPERSEDED}:{FILES[s]}"))
        open(b, "wb").write(git("show", f"{RECORD}:{FILES[s]}"))
        d += subprocess.run(["diff", "-u", "--label", f"{TAGS[s]} at {SUPERSEDED} (yh03regen 4e9a57e74cac)", "--label",
                             f"{TAGS[s]} (this commit)", a, b], capture_output=True).stdout
        os.remove(a)
        os.remove(b)
    open(w("diff-vs-0dbfaec69fb2.diff"), "wb").write(d)
    # 4e9a57e74cac/read-cells.tsv
    lines = ["side\tcell\tread_before_port\tread_after_port\tvalue_before\tvalue_after\tcheck_5e92f52b8caa_before\tcheck_5e92f52b8caa_after"]
    for s in ("plain", "ubsan"):
        vb = cellvals(git("show", f"{BEFORE}:{FILES[s]}").decode())
        va = cellvals(git("show", f"{SUPERSEDED}:{FILES[s]}").decode())
        readb, reada = read_cells(RELEASED, s), read_cells(BEFORE, s)
        b = table(os.path.join(o, f"4e9a57e74cac/check-5e92f52b8caa.before.{s}.rows"))
        a = table(os.path.join(o, f"4e9a57e74cac/check-5e92f52b8caa.after.{s}.rows"))
        rb = table(os.path.join(o, f"4e9a57e74cac/regen-4e9a57e74cac.{s}.report.tsv"))

        def v(t, c):
            x = c[7:]
            if c.startswith("src0_D_str"):
                k = "str_" + c[11:] if c != "src0_D_str" else "str"
                return "string cell: regen " + (rb[k][2] if k in rb else "KEEP?")
            k = ("D_" + x) if c[5] == "D" else x
            return t[k][2] if k in t else "NOROW"

        for c in sorted(readb | reada, key=lambda c: (c[5], c)):
            lines.append("\t".join([s, c, "yes" if c in readb else "no", "yes" if c in reada else "no", vb[c], va[c], v(b, c), v(a, c)]))
    open(w("4e9a57e74cac/read-cells.tsv"), "w").write("\n".join(lines) + "\n")
    # hand-decisions.tsv
    hd = ["file\tcell\tvalue\tcategory\twhy outside the tool's evidence or not written\treaders (.v, both builds, YH03.v excluded)"]
    for s in ("plain", "ubsan"):
        allv = {m.group(1): m.group(2) for m in re.finditer(r"Definition (src0_\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.",
                                                              git("show", f"{RECORD}:{FILES[s]}").decode())}

        def add(cell, cat, why):
            rd = readers(RECORD, cell)
            hd.append("\t".join([TAGS[s], cell, allv.get(cell, "?"), cat, why, "; ".join(rd) if rd else "none"]))

        for line in open(os.path.join(o, f"regen-f357a8df6e49-readers.{s}.report.tsv")):
            r = line.rstrip("\n").split("\t")
            if len(r) < 3:
                continue
            x, v = r[1], r[2]
            if v == "OMITTED":
                for k in ("A", "E"):
                    add(f"src0_{k}_{x}", "ABSENT A/E (not evidence)", "the image links no function of the name; v6.3 with --proofs would remove the definitions (no reader); kept as written")
            elif v == "ABSENT":
                add(f"src0_D_{x}", "string, no image string (known-wrong-unused)", "value not 0, the image holds no string for its slug; kept as written")
            elif v == "UNCHECKED":
                add(f"src0_D_{x}", "string, no slug (UNCHECKED, never judged)", "no slug: whether the image holds its string is not known; kept as written")
            elif v == "NOSYM":
                add(f"src0_{x}", "NOSYM (not checked)", "no symbol carries the name; kept as written, not derived")
            elif v == "KEEP-SIZE0":
                add(f"src0_E_{x}", "E of a size-0 function (not evidence)", "the symbol has size 0: no computable end; A checked (OK SIZE0), E kept as written")
        for c in ("src0_data_rel_ro_lo", "src0_data_rel_ro_hi", "src0_bss_lo", "src0_bss_hi", "src0_debruijn_len"):
            add(c, "no tool checks it", "not a cell kind the tools check")
    open(w("hand-decisions.tsv"), "w").write("\n".join(hd) + "\n")


if __name__ == "__main__":
    main()
