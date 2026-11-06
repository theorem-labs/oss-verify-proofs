#!/usr/bin/env python3
"""secbounds.py WORK LIB OUT: every section-bound cell of the relocated core (`Definition tfib_<section>_lo / _hi : Z := V`
in WORK/stage-out/A/AB1w.v, and any `<name>_lo` / `<name>_hi` definition elsewhere in stage-out whose name is a section's)
against the TARGET pin's own section header (the registry's 'port_core KNOWN LIMIT, ALL SCORED TAGS' entry: "every
section-bound cell ... is checked against the TARGET pin's section header"). A planted control is built in: the same
check on a copy of the cells with tfib_data_hi set to the donor's value must report exactly that cell.
Read-only. Output: OUT/secbounds.txt.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import decval as DV  # noqa: E402
from elftools.elf.elffile import ELFFile  # noqa: E402

SEC = {"rodata": ".rodata", "text": ".text", "init_array": ".init_array", "fini_array": ".fini_array",
       "preinit_array": ".preinit_array", "data_rel_ro": ".data.rel.ro", "got": ".got", "data": ".data",
       "asan_globals": "asan_globals", "bss": ".bss", "tbss": ".tbss", "eh_frame": ".eh_frame",
       "eh_frame_hdr": ".eh_frame_hdr", "relro_padding": ".relro_padding"}
KNOWN = {"tfib_rodata_hi": "KNOWN to the owner: the final run writes 0x22b4c (an override row added after work2)"}
DEF = re.compile(r"Definition ((?:tfib_)?(\w+?)_(lo|hi)) : Z := (0x[0-9a-fA-F]+|\d+)\.")


def cells(core):
    out = []
    for sub in ("A", "Reusable"):
        for fn in sorted(os.listdir(os.path.join(core, sub))):
            if not fn.endswith(".v"):
                continue
            for i, l in enumerate(open(os.path.join(core, sub, fn)).read().splitlines()):
                for m in DEF.finditer(l):
                    if m.group(2) in SEC:
                        out.append(("%s/%s" % (sub, fn), i + 1, m.group(1), SEC[m.group(2)], m.group(3), DV.val(m.group(4))))
    return out


def judge(cs, secs):
    res = []
    for f, ln, name, sec, side, v in cs:
        if sec not in secs:
            res.append(("NO-SECTION", f, ln, name, v, None))
            continue
        a, z = secs[sec]
        want = a if side == "lo" else a + z
        dec = "OK" if v == want else ("KNOWN" if name in KNOWN else "DIFF")
        res.append((dec, f, ln, name, v, want))
    return res


def main():
    work, lib, out = sys.argv[1:4]
    cfg = DV.setup([work])
    e = ELFFile(open(cfg["tgt_syms"], "rb"))
    secs = {s.name: (s["sh_addr"], s["sh_size"]) for s in e.iter_sections() if s["sh_addr"]}
    de = ELFFile(open(cfg["don_syms"], "rb"))
    dsecs = {s.name: (s["sh_addr"], s["sh_size"]) for s in de.iter_sections() if s["sh_addr"]}
    cs = cells(cfg["core"])
    res = judge(cs, secs)
    lines = ["# secbounds.py: %d section-bound cells in stage-out, against %s's section headers" % (len(cs), os.path.basename(cfg["tgt_bytes"]))]
    for r in res:
        lines.append("%s\t%s:%d\t%s = %#x\tsection %s\t%s" % (r[0], r[1], r[2], r[3], r[4], "header %#x" % r[5] if r[5] is not None else "-",
                                                         KNOWN.get(r[3], "") if r[0] == "KNOWN" else ""))
    bad = [r for r in res if r[0] in ("DIFF", "NO-SECTION")]
    lines.append("result: section-bound cells %d: OK %d, KNOWN %d, DIFF %d" % (
        len(res), sum(r[0] == "OK" for r in res), sum(r[0] == "KNOWN" for r in res), len(bad)))
    # control: tfib_data_hi set to the donor's .data end
    dval = dsecs[".data"][0] + dsecs[".data"][1]
    pc = [(f, ln, n, s, sd, dval if n == "tfib_data_hi" else v) for f, ln, n, s, sd, v in cs]
    pr = [r for r in judge(pc, secs) if r[0] in ("DIFF", "NO-SECTION")]
    ok = len(pr) == len(bad) + 1 and any(r[3] == "tfib_data_hi" and r[4] == dval for r in pr)
    lines.append("control: tfib_data_hi -> %#x (the donor's .data end): DIFF rows %d -> %d (%s): %s" % (
        dval, len(bad), len(pr), ", ".join("%s %#x" % (r[3], r[4]) for r in pr), "PASS" if ok else "FAIL"))
    open(os.path.join(out, "secbounds.txt"), "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
