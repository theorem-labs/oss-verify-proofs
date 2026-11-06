#!/usr/bin/env python3
"""Gates of provenance/OBLIGATIONS.md (rows 29-31, 41, 271, 272) on Print All Dependencies of the 7 tops.

Usage: deps-gate.py DIR > deps-gate.txt
DIR holds sinkdeps-<top>.names for the 7 tops: the fully qualified names of `Print All Dependencies` of
lib.Theorems.libreac_fuzz_boxreg_<top> under `Set Printing Fully Qualified` (build/SinkDepsAudit.v.txt writes each
output with Redirect; the names are its lines `^NAME :`, sorted, unique; build/README.md gives the commands).
For each top this prints the number of dependencies, every dependency in YI14 / YI5b / YI5c / YI5cSat / YH03 / YK09 /
AsanRT (both copies), the gate counts, and YK09's names grouped by their first component (the gate names only
YK09.asan_init and YK09.ASAN of YK09).
"""
import os
import re
import sys

U = "OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib."
TOPS = ["plain_halts", "ubsan_halts", "ubsan_agrees", "asan_halts", "asan_agrees", "asan_ubsan_halts",
        "asan_ubsan_agrees"]
MODS = ["Reusable.YI14", "Reusable.YI5b", "Reusable.YI5c", "Reusable.YI5cSat", "Reusable.YH03", "Reusable.YK09",
        "A.AsanRT", "B.AsanRT"]
# YI14 constants that state FILE-sink facts (row 41's five, and the restatement's new FILE constants)
FILE_CONSTS = ["stdio_env", "sink_at", "file_sink_at", "file_static", "file_at", "file_env", "file_window",
               "sink_laws", "fopen_spec", "unlink_spec", "fwrite_spec", "fclose_spec"]
FILE_FIELDS = ["sk_read", "sk_write", "sk_seek", "sk_close", "sk_path_addr", "sk_mode_addr", "sk_trailer_addr",
               "sk_rwa_addr"]
RULED_ROWS = ["src0_A_stdio_read", "src0_E_stdio_read", "src0_A_stdio_seek", "src0_E_stdio_seek", "src0_D_str_wb",
              "src0_D_str_tmp_out_gif", "src0_D_str_3", "src0_D_str_rwa"]


def in_mod(d, mod):
    return d.startswith(U + mod + ".") or d.startswith(U + "U." + mod + ".")


def main():
    base = sys.argv[1]
    for t in TOPS:
        p = os.path.join(base, f"sinkdeps-{t}.names")
        deps = sorted({l.strip() for l in open(p) if l.strip()})
        print(f"## {t}: {len(deps)} dependencies")
        for mod in MODS:
            hit = [d[len(U):] for d in deps if in_mod(d, mod)]
            print(f"  {mod} (both copies): {len(hit)}" + (": " + ", ".join(hit) if hit else ""))
        fc = [d[len(U):] for d in deps if in_mod(d, "Reusable.YI14") and d.rsplit(".", 1)[-1] in FILE_CONSTS]
        asan = [d for d in deps if re.search(r"\.YK09\.(asan_init|ASAN)($|\.)", d) or in_mod(d, "A.AsanRT")
                or in_mod(d, "B.AsanRT") or re.search(r"(^|\.)AITAB($|\.)", d)]
        yk = {}
        for d in deps:
            if in_mod(d, "Reusable.YK09"):
                sub = d.split(".YK09.", 1)[1].split(".")[0]
                yk[sub] = yk.get(sub, 0) + 1
        fields = [d[len(U):] for d in deps if in_mod(d, "Reusable.YI14") and d.rsplit(".", 1)[-1] in FILE_FIELDS]
        rows = [d[len(U):] for d in deps if in_mod(d, "Reusable.YH03") and d.rsplit(".", 1)[-1] in RULED_ROWS]
        print(f"  gate FILE constants of YI14 ({' / '.join(FILE_CONSTS)}): {len(fc)}" + (": " + ", ".join(fc) if fc else ""))
        print(f"  gate YK09.asan_init / YK09.ASAN / AITAB / AsanRT (asan_cf_cells, AsanRTInv, RT): {len(asan)}"
              + (": " + ", ".join(asan) if asan else ""))
        print("  YK09 names by first component: " + (", ".join(f"YK09.{k} {v}" for k, v in sorted(yk.items())) or "none"))
        print(f"  file_sink_syms fields ({' / '.join(FILE_FIELDS)}): {len(fields)}" + (": " + ", ".join(fields) if fields else ""))
        print(f"  the 8 ruled YH03 sink rows: {len(rows)}" + (": " + ", ".join(rows) if rows else ""))


if __name__ == "__main__":
    main()
