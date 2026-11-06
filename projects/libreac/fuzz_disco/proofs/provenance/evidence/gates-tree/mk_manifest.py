#!/usr/bin/env python3
"""Write this directory's MANIFEST: one line `<path> <kind> <sha256> <role>` per file, from the ROLES table below.

Usage: mk_manifest.py [DIR]   (default: this script's directory). Refuses a file in DIR that ROLES does not name, and a
name in ROLES with no file, so the MANIFEST always lists exactly the files present.
"""
import hashlib
import os
import sys

BASE = "b1afc3e80791"
ROLES = [
    ("run.sh", "script",
     "re-runs the three gate records below on the series base, each with a planted control; arguments REPO REF PIN_DIR "
     "SETTINGS_DIR KIMG SNAPSHOT (OUT optional); two runs give the three records byte for byte"),
    ("segment_match.py", "script",
     "checker written for this record: the four ELFs of projects/libreac/fuzz_disco/harness.yaml (bytes, sha256) and "
     "every PT_LOAD of each against the hex image the snapshot tool makes of it, byte for byte at its page-span offset"),
    ("settings_digest.py", "script",
     "reduces a settings-check run to its TOOL / selftest / control lines, its KERNEL and UNMEASURED rows and its "
     "SUMMARY, with the run's temporary directory written as <work>"),
    ("mk_manifest.py", "script", "writes this MANIFEST from the files present"),
    ("settings-v10.txt", "gate",
     "settings check v10 (global_settings.py, cited by sha256 439f8e3bd463, not copied) over all 3765 .v files of "
     "proofs/libreac/fuzz_disco at " + BASE + ": exit 0, KERNEL 0; control (Unset Guard Checking added to a copy of "
     "lib/A/AB01.v) exit 5; covers every .v file of the unit"),
    ("segments.txt", "gate",
     "the four pins of projects/libreac/fuzz_disco/harness.yaml at " + BASE + " (plain, ubsan, asan, asan-ubsan) match "
     "by bytes and sha256, and all 16 PT_LOAD segments of the images that projects/libreac/fuzz_disco/images/dune builds "
     "(snapshot tool of the semantics commit release.yaml names, sha256 a7f4d38c861c) match the ELFs byte for byte; "
     "controls: one flipped hex byte (15/16) and one flipped pin byte (3/4); covers projects/libreac/fuzz_disco/Images.v"),
    ("kimg-overlap.txt", "gate",
     "kimg_overlap (cited by sha256 5db341e3cd62, not copied) on proofs/libreac/fuzz_disco/lib/A/AB01.v, AB03.v, AD2j.v "
     "at " + BASE + " against fuzz_disco.asan: 0 contradicting bytes, 0 duplicate states, 0 range findings; control (one "
     "KImg range widened over a KWord) exit 1"),
]


def main():
    d = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    present = sorted(f for f in os.listdir(d) if f != "MANIFEST" and os.path.isfile(os.path.join(d, f)))
    named = [p for p, _, _ in ROLES]
    extra, missing = sorted(set(present) - set(named)), sorted(set(named) - set(present))
    if extra or missing:
        sys.exit("REFUSED: not in ROLES: %s; no file: %s" % (extra, missing))
    lines = ["# gates-tree: whole-tree gate records of proofs/libreac/fuzz_disco on the series base " + BASE,
             "# <path> <kind> <sha256> <role>"]
    for p, kind, role in ROLES:
        sha = hashlib.sha256(open(os.path.join(d, p), "rb").read()).hexdigest()
        lines.append("%s %s %s %s" % (p, kind, sha, role))
    open(os.path.join(d, "MANIFEST"), "w").write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
