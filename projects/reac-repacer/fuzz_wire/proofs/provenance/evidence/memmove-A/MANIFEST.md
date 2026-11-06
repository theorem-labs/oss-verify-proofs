# provenance/evidence/memmove-A: fuzz_wire image-A __asan_memmove contract, gate record

The files a reader needs to re-run the gates of lib/A/Rt/{MemmoveDef,MemmoveIm,MemmoveK,MemmovePaths,Memmove}.v and to
check their numbers. The relocation itself is ../memmove-reloc/ (run.sh, adapt_memmove.py, asan-resolve-A.txt and
asan-resolve-A.why.txt). Environment of the scripts: as gates/run-gates.sh lists it (each tool and image by sha).

| file | role |
|---|---|
| GATES.md | the gate numbers, each with its planted control and the measured reasons |
| gates/run-gates.sh | every gate and control over the committed files; raw outputs to a scratch directory |
| gates/measure-mm.py | reads out of both images every value a triage reason cites |
| gates/triage-mm.py | the flag gate's triage: any flagged / GENERATOR-FILL row is unexplained (exit 1); checks the expected classes of the 60 resolved rows |
| gates/codeptr-notaddr-mm.tsv | codeptr's five non-address declarations, each with its measured reason |
| gates/decval-mm.py | the by-value check (the image-B record's decval-mm.py with image A's inputs) |
| gates/records-mm.py | writes records/ from the raw outputs, with role names for paths |
| records/measure.out | measure-mm.py's output |
| records/flag-gate.txt, records/flag-triage.tsv | port_addr_check efa19b81e92b: the record run and the two planted runs; the triage rows |
| records/codeptr.txt, records/codeptr-occurrences.tsv | codeptr per file, per run (base, declared, donor, plant, plant-declared); every occurrence of a declaration |
| records/atable.txt | atable N/A: the name scan and keyset check over the five files |
| records/byvalue.txt, records/byvalue-rows.tsv, records/byvalue-review.tsv | the by-value check: summaries (record, control), per-numeral rows, review rows |
| records/settings-count.txt | v10 counts of the five files, of fuzz_pcap's released counterparts and of the control |
