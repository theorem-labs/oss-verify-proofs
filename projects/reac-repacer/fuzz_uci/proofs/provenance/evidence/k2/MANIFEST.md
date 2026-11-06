# k2/

| file | role |
|---|---|
| k2_relocate.py | the script of record: copies libreac/fuzz_decode's released lib (K1), moves every image value to this unit's binaries (K2), adds second-donor libc walks when linked (K3); its docstring states each step and control |
| k2-values.tsv | every value it changed: file, line, old, new, how (and each file it did not copy, with the reason) |
| k2-conflicts.tsv | hex values the address tool also classes NON-ADDRESS, left to the decimal table (see gate/GATE.md) |
| k2-cells.tsv | every kept per-image YH03 cell, by file and line, with the rule and the measurement that decided its value (e.g. the stdio read cell = the image FILE's read slot 0; four sink string cells kept because their strings occur in no image) |
