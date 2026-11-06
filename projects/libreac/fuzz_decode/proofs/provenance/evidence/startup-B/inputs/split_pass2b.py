#!/usr/bin/env python3
"""split_pass2b.py SRC PART1 PART2 -- split the cleaned pass-2 log into two plain-text parts at a line boundary.

SRC, PART1 and PART2 are paths relative to this slice (provenance/evidence/startup-B/, the parent of this file's
directory), whatever the current directory is; an absolute path or a `..` component is refused. SRC is the cleaned
copy of the pass-2 log that inputs/scrub_input.py wrote (sha256 SHA256 below; `cat PART1 PART2 > pass2b.log` in the
slice gives it back). The run that wrote the committed parts:

    python3 inputs/split_pass2b.py pass2b.log inputs/pass2b.log.part1 inputs/pass2b.log.part2

The cut is the end of a line (after a newline byte) such that each part is below the lint cap of 5 MiB (5242880 bytes);
of those cuts, the one nearest the middle of SRC (the earlier one on a tie). Every byte of SRC is kept, in order:
`cat PART1 PART2` gives SRC. The script refuses (exit 1, nothing written) unless the sha256 of PART1 + PART2 is that of
the cleaned copy, SHA256 below; it also refuses when no cut fits under the cap, or when PART1 or PART2 exists already.
On success it writes both parts (each through a temporary file in its directory, then a link to its name) and prints
one line per part: its name, size and sha256.
"""
import hashlib
import os
import sys
import tempfile

SHA256 = "5592b5596ceccd1e4c58af1bd0376fbc48f9bacbaa772b8869a3fb31607a7dbc"
CAP = 5 << 20
SLICE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def refuse(msg):
    print(f"split_pass2b: {msg}; nothing written", file=sys.stderr)
    sys.exit(1)


def slice_path(rel):
    if os.path.isabs(rel) or ".." in rel.split("/") or rel in ("", "."):
        refuse(f"{rel!r} is not a path relative to the slice")
    return os.path.join(SLICE, rel)


def cut_at(data):
    n = len(data)
    best = None
    i = data.find(b"\n")
    while i != -1:
        k = i + 1
        if 0 < n - k and k < CAP and n - k < CAP:
            if best is None or abs(2 * k - n) < abs(2 * best - n):
                best = k
        i = data.find(b"\n", k)
    return best


def write_new(path, data):
    fd, tmp = tempfile.mkstemp(dir=os.path.dirname(path) or ".", prefix=".split_pass2b.")
    try:
        with os.fdopen(fd, "wb") as f:
            os.fchmod(f.fileno(), 0o644)
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.link(tmp, path)
    finally:
        os.unlink(tmp)


def main(argv):
    if len(argv) != 4:
        print("usage: split_pass2b.py SRC PART1 PART2 (paths relative to the slice)", file=sys.stderr)
        return 2
    src, out1, out2 = (slice_path(a) for a in argv[1:])
    names = argv[2:]
    for rel, p in zip(names, (out1, out2)):
        if os.path.lexists(p):
            refuse(f"{rel} exists already")
    with open(src, "rb") as f:
        data = f.read()
    k = cut_at(data)
    if k is None:
        refuse(f"{argv[1]}: no line boundary leaves both parts below {CAP} bytes")
    parts = (data[:k], data[k:])
    got = hashlib.sha256(parts[0] + parts[1]).hexdigest()
    if got != SHA256:
        refuse(f"sha256 of PART1 + PART2 is {got}, not {SHA256}")
    written = []
    try:
        for p, part in zip((out1, out2), parts):
            write_new(p, part)
            written.append(p)
    except OSError as e:
        for p in written:
            os.unlink(p)
        refuse(f"cannot write the parts ({e.strerror})")
    for rel, part in zip(names, parts):
        print(f"{rel} {len(part)} {hashlib.sha256(part).hexdigest()}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
