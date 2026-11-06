#!/usr/bin/env python3
"""Comment-stripped code compare of a merge against the integration it merged into.

The merge dad326edc436 of the comment, citation and evidence work done after the re-pin into the integration
3439a53faa11 must not move one token of proof code.  This reads every .v file of both trees, removes the
Rocq comments (nested (* *), with "..." strings and the escape '"' honoured), drops what a removed comment
leaves behind (trailing blanks, then the lines that are now empty), and compares the two byte strings.

    python3 merge_codecmp.py [--base <rev>] [--rev <rev>] [--root <path>]

Prints one line per differing file and ends with "<n> differ" over "<m> .v files compared".
Exit status 0 when nothing differs.
"""

import argparse
import subprocess
import sys


def strip_comments(text: str) -> str:
    """Remove Rocq comments.  (* *) nests; a comment opener inside a string is not one."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        c = text[i]
        if depth == 0:
            if c == '"':
                j = i + 1
                while j < n:
                    if text[j] == '"':
                        if j + 1 < n and text[j + 1] == '"':
                            j += 2
                            continue
                        break
                    j += 1
                out.append(text[i:min(j + 1, n)])
                i = j + 1
                continue
            if c == '(' and i + 1 < n and text[i + 1] == '*':
                depth = 1
                i += 2
                continue
            out.append(c)
            i += 1
            continue
        # inside a comment: only the nesting and the string literals it may hold matter
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            i = j + 1
            continue
        if c == '(' and i + 1 < n and text[i + 1] == '*':
            depth += 1
            i += 2
            continue
        if c == '*' and i + 1 < n and text[i + 1] == ')':
            depth -= 1
            i += 2
            continue
        i += 1
    return "".join(out)


def code_of(text: str) -> str:
    lines = [ln.rstrip() for ln in strip_comments(text).split("\n")]
    return "\n".join(ln for ln in lines if ln)


def tree_files(rev: str, root: str) -> dict:
    names = subprocess.run(["git", "ls-tree", "-r", "--name-only", "-z", rev, "--", root],
                           check=True, capture_output=True, text=True).stdout.split("\0")
    return {p: None for p in names if p.endswith(".v")}


def blob(rev: str, path: str) -> str:
    return subprocess.run(["git", "show", f"{rev}:{path}"], check=True,
                          capture_output=True).stdout.decode("utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default="3439a53faa11", help="the integration the merge must not move")
    ap.add_argument("--rev", default="", help="revision to compare; empty = the working tree")
    ap.add_argument("--root", default="proofs/libdiginet/fuzz_transport")
    a = ap.parse_args()

    base = tree_files(a.base, a.root)
    head_rev = a.rev if a.rev else "HEAD"
    now = tree_files(head_rev, a.root) if a.rev else None
    if now is None:
        names = subprocess.run(["git", "ls-files", "-z", "--", a.root], check=True,
                               capture_output=True, text=True).stdout.split("\0")
        now = {p: None for p in names if p.endswith(".v")}

    differ = []
    for path in sorted(set(base) | set(now)):
        if path not in base:
            differ.append(f"{path}: added by the merge")
            continue
        if path not in now:
            differ.append(f"{path}: removed by the merge")
            continue
        old = code_of(blob(a.base, path))
        new = code_of(blob(a.rev, path) if a.rev else open(path, encoding="utf-8").read())
        if old != new:
            differ.append(f"{path}: code differs")
    for line in differ:
        print(line)
    print(f"{len(differ)} differ of {len(set(base) | set(now))} .v files compared"
          f" ({a.base} -> {a.rev or 'working tree'})")
    return 1 if differ else 0


if __name__ == "__main__":
    sys.exit(main())
