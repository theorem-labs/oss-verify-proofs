#!/usr/bin/env python3
"""Reduce one run of the settings check (global_settings.py v10) to the lines a reader needs to judge it.

Usage: settings_digest.py RUN_OUTPUT WORK_PREFIX > digest

Keeps, in their order: the TOOL, selftest, control and `INPUT wt` lines; every row at level KERNEL or UNMEASURED, each
under the `read <file>:` line of the file it belongs to; the SUMMARY and REFUSE lines. Drops the per-file INPUT lines
(sha256 and blob of each file: the commit fixes them) and the ESCAPES / PLAIN rows of levels TACTIC and OPTION, which
never change the exit code; their counts stay in the SUMMARY line. WORK_PREFIX (the temporary directory of the run)
is written as `<work>` so the digest is the same on every machine.
"""
import sys

KEEP_PREFIX = ("TOOL ", "selftest:", "control:", "INPUT wt ", "SUMMARY:", "REFUSE")


def main():
    path, prefix = sys.argv[1], sys.argv[2].rstrip("/")
    out, last_read, shown = [], None, None
    for line in open(path, encoding="utf-8", errors="replace").read().splitlines():
        line = line.replace(prefix + "/", "<work>/").replace(prefix, "<work>")
        if line.startswith(KEEP_PREFIX):
            out.append(line)
        elif line.startswith("read "):
            last_read = line
        elif line.startswith("   :") and (" KERNEL" in line or " UNMEASURED " in line):
            if shown is not last_read:
                out.append(last_read)
                shown = last_read
            out.append(line)
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
