#!/usr/bin/env python3
"""history.py: the headerless proof files of libreac/fuzz_scene that their history shows were made as a copy or a
relocation of a file with Anthropic's licence lines, whatever they share with such a file today.

Usage (in a clone of this repository that has the branches the unit was built on; run from its top):
  python3 projects/libreac/fuzz_scene/proofs/provenance/evidence/licence/history.py REF OUT.tsv

For each .v file under projects/libreac/fuzz_scene/proofs/lib/ at REF with no licence lines or only `Modified by`
lines (made_from.py's `headerless` and `modified_only`), the commit that first added it is the earliest commit (by commit time), on any ref, that adds it at
projects/libreac/fuzz_scene/proofs/lib/<path> or, before the per-project layout, proofs/libreac/fuzz_scene/lib/<path>.  The
file counts when
  (h1) the file as that commit added it carried Anthropic's copyright line in its first 10 lines, or
  (h2) that commit's message names a fuzz target the file was copied or relocated from (one of DONORS, each named
       in a message by its harness name), and that fuzz target's file at the same path in its proof library, in
       the commit's first parent, carried Anthropic's copyright line in its first 10 lines.
OUT gets one row per file that counts: path, source, rule, commit.  The source is the file of libreac/fuzz_scene at the
same path when (h1) holds, and for (h2) the donor's file, spelled proofs/<p>/<h>/lib/<path>.  Files that do not count
are not listed: made_from.py decides them on what they share today.
"""
import collections
import re
import subprocess
import sys

LIB_NEW, LIB_OLD = "projects/libreac/fuzz_scene/proofs/lib/", "proofs/libreac/fuzz_scene/lib/"
ANTHROPIC = re.compile(r"Copyright \d{4} Anthropic PBC")
LICENCE = re.compile(r"\(\* (?:Copyright \d{4} |SPDX-License-Identifier:|Modified by )")
PROGRAM = re.compile(r"^\(\* (?:Machine-generated data computed|This file states or restates instruction words)", re.M)
# the fuzz targets whose proof files commits of the unit's history copied or relocated (their messages name each by
# its harness name: "libreac/fuzz_grant's frame", "fuzz_pcap's lib/A", "from cgif_file_fuzzer", ...).  The same list
# made_from.py's DONORS holds, measured from the paths the unit's own licence lines and header comments cite.
DONORS = ("cgif/cgif_file_fuzzer", "libreac/fuzz_grant", "varnish/esi_parse_fuzzer", "openssl/ct",
          "cgif/cgif_rgb_fuzzer", "libreac/fuzz_decode", "libreac/fuzz_ctrl", "boost-beast/http_request",
          "libreac/fuzz_boxreg", "jsoncons/fuzz_ubjson_encoder", "jsoncons/fuzz_bigint",
          "libreac/fuzz_pcap", "libreac/fuzz_disco", "zlib/checksum_fuzzer")


def git(*args):
    return subprocess.run(("git",) + args, capture_output=True, check=True).stdout


def head(text):
    return "\n".join(text.split("\n")[:10])


def blob(commit, path):
    r = subprocess.run(["git", "show", "%s:%s" % (commit, path)], capture_output=True)
    return r.stdout.decode("utf-8", "replace") if r.returncode == 0 else None


def main():
    ref, out = sys.argv[1:3]
    names = [p for p in git("ls-tree", "-r", "--name-only", ref, "--", LIB_NEW).decode().split("\n")
             if p.endswith(".v")]
    heads = []
    for p in names:
        h = head(git("show", "%s:%s" % (ref, p)).decode("utf-8", "replace"))
        lic = [x for x in h.split("\n") if LICENCE.match(x)]
        modified_only = lic and all(x.startswith("(* Modified by ") for x in lic)
        if not ANTHROPIC.search(h) and not PROGRAM.search(h) and (not LICENCE.search(h) or modified_only):
            heads.append(p[len(LIB_NEW):])
    first = {}
    cur = None
    log = git("log", "--all", "--diff-filter=A", "--name-only", "--format=C %H %ct", "--", LIB_NEW, LIB_OLD).decode()
    for line in log.split("\n"):
        if line.startswith("C "):
            _, c, t = line.split()
            cur = (int(t), c)
        elif line.startswith((LIB_NEW, LIB_OLD)):
            rel = line[len(LIB_NEW):] if line.startswith(LIB_NEW) else line[len(LIB_OLD):]
            if rel not in first or cur < first[rel][0]:
                first[rel] = (cur, line)
    rows, counts = [], collections.Counter()
    msgs = {}
    for rel in sorted(heads):
        if rel not in first:
            counts["no add commit"] += 1
            continue
        (_, c), path = first[rel]
        text = blob(c, path)
        if text is not None and ANTHROPIC.search(head(text)):
            rows.append((rel, "proofs/libreac/fuzz_scene/lib/" + rel, "h1", c))
            counts["h1"] += 1
            continue
        if c not in msgs:
            msgs[c] = git("log", "-1", "--format=%B", c).decode()
        donors = [d for d in DONORS if re.search(r"\b%s\b" % d.split("/")[1], msgs[c])]
        hit = None
        for d in dict.fromkeys(donors):
            p, h = d.split("/", 1)
            for cand in ("projects/%s/%s/proofs/lib/%s" % (p, h, rel), "proofs/%s/%s/lib/%s" % (p, h, rel)):
                t = blob(c + "^", cand)
                if t is not None:
                    if ANTHROPIC.search(head(t)):
                        hit = "proofs/%s/%s/lib/%s" % (p, h, rel)
                    break
            if hit:
                break
        if hit:
            rows.append((rel, hit, "h2", c))
            counts["h2"] += 1
        else:
            counts["not shown by history"] += 1
    with open(out, "w", encoding="utf-8") as f:
        f.write("path\tsource\trule\tcommit\n" + "".join("\t".join(r) + "\n" for r in rows))
    print("headerless files at %s: %d; %s" % (ref, len(heads), "; ".join("%s: %d" % kv for kv in sorted(counts.items()))))


if __name__ == "__main__":
    main()
