# provenance/evidence/pack-checks: the checks of the fuzz_uci ASan pack before its release check

The evidence index check, the build and assumptions, the name scan and the comparison-kit scans of the tree this slice is
added to. Start with RECORD.md.

| file | role |
|---|---|
| MANIFEST.md | this list |
| RECORD.md | the record: what each check ran on and its result |
| checker.txt | evidence_manifest_check.py on the parent commit: its sha256, the command, the output, rc |
| sha256sum-c.txt | `sha256sum -c` of every MANIFEST line's sha256 field on the parent commit's tree: rc and counts |
| control-checker-line.txt | planted control: one MANIFEST line deleted; the checker refuses |
| control-checker-sha.txt | planted control: one sha256 field zeroed; the checker refuses |
| control-sha256.txt | planted control: one byte appended to one file; `sha256sum -c` refuses |
| binscan-lines.tsv | every line with a blocking name-scan row, with the released file that has the same line |
| kitscan-table.md | per record: functions compared, luiscan and ambiscan results, lui hand-trace counts and verdicts |
| ambig-settle-uci-b-alloc.tsv | uci-b-alloc's ambiscan AMBIG rows, one per row: both images' copy and its callers, MATCH / MISMATCH |
| ambig-settle-uci-b-alloc.md | how the AMBIG rows were tied to addresses, and the check that the record cites none of its earlier/ outputs |
