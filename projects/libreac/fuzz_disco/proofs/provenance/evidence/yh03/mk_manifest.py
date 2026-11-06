#!/usr/bin/env python3
"""mk_manifest.py [SLICE_DIR] -- write SLICE_DIR/MANIFEST (default: this script's directory): one line per file,
`<path> <kind> <sha256> <role>`, kind = script | input | table | gate. The roles are the table below; a file of the
slice that the table does not name, or a named file that is absent, stops the run."""
import hashlib
import os
import sys

U = "proofs/libreac/fuzz_disco"
P, B = U + "/lib/Reusable/YH03.v", U + "/lib/U/Reusable/YH03.v"
CHECK = ("the address-table checker v6.4 of record yh03check.py sha256 fb3bfbc1eea8 (with the yh03regen.py "
         "1254e5c96a44 it imports; cited, not copied)")
REGEN = "the address-table re-derivation tool v6.4 of record yh03regen.py sha256 1254e5c96a44 (cited, not copied)"
ROLES = [
    ("run.sh", "script", "Re-runs every script below from this slice's files and cmps each output with the shipped "
     "file; arguments: the unstripped twins' directory, the pins' directory, the checker's directory, a scratch "
     "directory (the checker's directory holds tools v6.4). Covers %s and %s." % (P, B)),
    ("mk_manifest.py", "script", "Writes this MANIFEST (roles and sha256 of every slice file)."),
    ("scripts/apply_table.py", "script", "Applies a fix table to the address table it was measured on (FIX "
     "replaces the committed value, DELETE removes the Definition, KEEP changes nothing) and inserts the fix's one "
     "comment line; run.sh shows the result equals %s and %s byte for byte." % (P, B)),
    ("scripts/elf_reader.py", "script", "ELF64 reader (PT_LOADs, section headers, symbols, bytes at an address); "
     "`loads PIN TWIN` gives the twin-vs-pin records. The fix's reader under a neutral name, code unchanged."),
    ("scripts/delete_users.py", "script", "Counts the uses of every DELETE cell name of the two tables in the "
     "unit's .v files: all 0 in the fixed tree."),
    ("inputs/header-plain.txt", "input", "The one comment line the fix added to %s (line 5); a comment, not "
     "derivable from the table, taken from the shipped file." % P),
    ("inputs/header-ubsan.txt", "input", "The one comment line the fix added to %s (line 5); a comment, not "
     "derivable from the table, taken from the shipped file." % B),
    ("gates/regen-old-plain.out", "gate", "%s, --pinned, --elf the unit-identity-checked plain twin, --proofs the fixed "
     "unit tree, on a scratch copy of inputs/old-plain.v.txt: self-test 163 known answers OK, section bounds 18 of 18, "
     "unit identity with the plain pin; it refuses to write because the old file's D_stderr is a section boundary and "
     "D_got_DYNAMIC_reserved is not GOT[0] (both corrected or deleted by the fix)." % REGEN),
    ("gates/regen-old-ubsan.out", "gate", "The same run on inputs/old-ubsan.v.txt against the ubsan twin and pin."),
    ("gates/regen-fixed-plain.out", "gate", "%s, --pinned, --elf the unit-identity-checked plain twin, --proofs the "
     "unit tree, on %s itself (no --write; the file is the same at the series head): self-test 163 known answers OK, "
     "section bounds 18 of 18, unit identity; every cell judged with no FIX, no ABSENT, no OMITTED, no REFUSED and no "
     "UNCHECKED row: --proofs lists no ABSENT cell; D_stderr is KEEP at the value the old file's refusal named." % (REGEN, P)),
    ("gates/regen-fixed-ubsan.out", "gate", "The same run on %s against the ubsan twin and pin: same result." % B),
    ("gates/twin-pin-plain.txt", "gate", "Plain unstripped twin (sha256 115e0dcb29bc5963) against the plain pin "
     "(sha256 04988e3ab3134196): PT_LOAD 2-4 headers and bytes equal; PT_LOAD 1 differs only in the ELF section-header "
     "fields and the build-id, so the twin's symbols describe the pin."),
    ("gates/twin-pin-ubsan.txt", "gate", "Ubsan twin (sha256 e2a41feb2f469916) against the ubsan pin (sha256 "
     "56121de6ba4cff85): same result."),
    ("gates/delete-users.txt", "gate", "delete_users.py on the fixed tree: 74 deleted names, 0 uses each."),
]


def main(argv):
    d = argv[1] if len(argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    named = {p for p, _, _ in ROLES}
    have = set()
    for root, _, fs in os.walk(d):
        for fn in fs:
            rel = os.path.relpath(os.path.join(root, fn), d)
            if rel != "MANIFEST" and "__pycache__" not in rel:
                have.add(rel)
    if have != named:
        sys.exit("mk_manifest: not named %s; absent %s" % (sorted(have - named), sorted(named - have)))
    out = ["# fuzz_disco evidence, slice yh03: the two YH03 address tables as fixed. path kind sha256 role",
           "# 19 files of this slice (its fix tables, the old address tables, nosym_check.py, nosym_read.py, "
           "regen_compare.py, and the per-cell reports and checker outputs they gave) were removed from the shipped tree on 2026-11-04 (internal record; in git history)."]
    for p, k, role in ROLES:
        with open(os.path.join(d, p), "rb") as f:
            out.append("%s %s %s %s" % (p, k, hashlib.sha256(f.read()).hexdigest(), role))
    with open(os.path.join(d, "MANIFEST"), "w") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main(sys.argv)
