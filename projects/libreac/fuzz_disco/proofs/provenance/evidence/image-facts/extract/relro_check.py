#!/usr/bin/env python3
"""relro_check.py -- checks the read-only-after-relocation bounds written in a proof file against an image's facts.

FACTS is an image_facts.py table; its `relro LO HI` line is .data.rel.ro start .. .got end of the pinned image.
VFILE is a proof file; LO_RE and HI_RE are regular expressions whose first group captures the hex literal of the
low and the high bound in VFILE. The literals must occur, and each must equal the facts' value.
Prints one line per bound and exits 1 on any mismatch.

Usage: relro_check.py FACTS VFILE LO_RE HI_RE
"""
import re
import sys


def main():
    if len(sys.argv) != 5:
        sys.exit(__doc__)
    facts, vfile, lo_re, hi_re = sys.argv[1:]
    rl = [line.split() for line in open(facts) if line.startswith("relro ")]
    if len(rl) != 1:
        sys.exit("%s: no single relro line" % facts)
    want = {"lo": int(rl[0][1], 16), "hi": int(rl[0][2], 16)}
    text = open(vfile).read()
    bad = 0
    for side, rx in (("lo", lo_re), ("hi", hi_re)):
        found = [int(m.group(1), 16) for m in re.finditer(rx, text)]
        ok = bool(found) and all(v == want[side] for v in found)
        bad += not ok
        print("%s %s: image 0x%x, file %s: %s" % (
            vfile.rsplit("/", 1)[-1], side, want[side], ",".join("0x%x" % v for v in found) or "none",
            "equal" if ok else "DIFFERENT"))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
