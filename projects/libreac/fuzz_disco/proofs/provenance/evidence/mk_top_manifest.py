#!/usr/bin/env python3
"""Write provenance/evidence/MANIFEST for libreac/fuzz_disco.

Usage: python3 mk_top_manifest.py [EVIDENCE_DIR]   (default: the directory of this script)

The top MANIFEST names every regular file that sits directly in EVIDENCE_DIR (this script included) as
`<path> <kind> <sha256> <role>`. Each slice directory has its own MANIFEST, written by that slice's own
script, which names the slice's files; the top MANIFEST lists each slice in a comment line with its file
count and the sha256 of its MANIFEST. Running the script twice gives the same bytes.
"""
import hashlib
import os
import sys

ROLES = {
    "mk_top_manifest.py": ("script", "writes this MANIFEST from the files of this directory and the slice MANIFESTs"),
    "README.md": ("doc", "what this directory holds, and the note on internal commit ids in its run records"),
    "lane-comments.tsv": ("table", "comment lines removed from files copied from the delivered proofs, one row per line, written by the lane-comments tool"),
    "untime-removed.tsv": ("table", "timeout tokens removed from proof tactics and their marker comments, one row per site, written by the untime tool"),
    "licence-removed.tsv": ("table", "licence notice lines replaced by the licence tool, verbatim, one row per line, written by the licence-lines tool"),
}
SLICES = {
    "core-A": "image A (fuzz_disco.asan) runtime and allocator core, lib/A",
    "core-Y": "image B (fuzz_disco.asan-ubsan) runtime and allocator core, lib/Reusable",
    "startup-A": "image A start-up data",
    "startup-Y": "image B start-up data",
    "image-facts": "program listings and read-only ranges of both ASan images",
    "g9-gxa": "relocated formatted-output layer and memory-interceptor layers, both ASan images",
    "yh03": "address tables of the plain and ubsan builds",
    "gates-A": "gate records on image A, re-run against its pin",
    "gates-Y": "gate records on image B, re-run against its pin",
    "gates-tree": "whole-tree records: settings check, per-segment image match, start-up overlap check",
}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def main():
    ev = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
    lines = [
        "# provenance/evidence/ of libreac/fuzz_disco: what a reader needs to re-derive the numbers of the shipped proofs.",
        "# Form: <path> <kind> <sha256> <role>; kind = script | input | table | gate. Each slice directory has its own MANIFEST.",
    ]
    names = sorted(os.listdir(ev))
    for name in names:
        p = os.path.join(ev, name)
        if os.path.isdir(p):
            m = os.path.join(p, "MANIFEST")
            if not os.path.isfile(m):
                sys.exit("slice %s has no MANIFEST" % name)
            count = sum(len(fs) for _, _, fs in os.walk(p))
            lines.append("# slice %s/ (%d files, MANIFEST sha256 %s): %s" % (name, count, sha256(m), SLICES.get(name, "see its MANIFEST")))
    for name in names:
        p = os.path.join(ev, name)
        if os.path.isfile(p) and name != "MANIFEST":
            if name not in ROLES:
                sys.exit("no role for top-level file %s" % name)
            kind, role = ROLES[name]
            lines.append("%s %s %s %s" % (name, kind, sha256(p), role))
    with open(os.path.join(ev, "MANIFEST"), "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
