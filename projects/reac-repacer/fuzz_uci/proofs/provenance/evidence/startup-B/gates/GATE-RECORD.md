# Gate record: fuzz_uci image B start-up set

Written by scripts/mk_evidence.py gate_record() from the gate runs' own output (the lane's gate logs, which stay on the proof-attempt branch with the generation logs): every RESULT line and the summary lines of each gate, in run order. A machine path is replaced by the variable that names it (env.example.sh), or cut to `<path>/` and its last two components; a build-machine name is replaced by `<build VM>`; a proof-attempt branch name by `<branch>` (the commit sha beside it stays). Harness: scripts/gates/run_gates.sh.

## FINAL: full run on the 19 committed files, port_addr_check e165063a0081 included (G0-G12)

```
RESULT G1 kimg acfd CONTROL cgif YB01/YB03 rc=0
25e3d17bdb50:proofs/cgif/cgif_file_fuzzer/lib/YB01.v  overlapping write bytes 0  contradicting bytes 0
    states: 50, aliases 0, duplicate states 0
25e3d17bdb50:proofs/cgif/cgif_file_fuzzer/lib/YB03.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
RESULT G1 kimg acfd CONTROL cgif counterparts rc=0
FILE:cgif/YB01.v  overlapping write bytes 0  contradicting bytes 0
    states: 50, aliases 0, duplicate states 0
FILE:cgif/YB03.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB05.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB12.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB13.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB1h.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB1k.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB1l.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB1m.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB1v.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YCej.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YD1k.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YD1y.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YD2i.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YD2j.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YE23.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YE37.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YE3i.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YF0m.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
RESULT G1 kimg acfd uciB rc=0
FILE:gen/YB01.v  overlapping write bytes 0  contradicting bytes 0
    states: 50, aliases 0, duplicate states 0
FILE:gen/YB03.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB05.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB12.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB13.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB1h.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB1k.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB1l.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB1m.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB1v.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YCej.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YD1k.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YD1y.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YD2i.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YD2j.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YE23.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YE37.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YE3i.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YF0m.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
RESULT G1b kimg 5db3 CONTROL rc=0
25e3d17bdb50:proofs/cgif/cgif_file_fuzzer/lib/YB01.v  overlapping write bytes 0  contradicting bytes 0
    states: 50, aliases 0, duplicate states 0
    KImg ranges: 140, findings 0
25e3d17bdb50:proofs/cgif/cgif_file_fuzzer/lib/YB03.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
    KImg ranges: 67, findings 0
RESULT G1b kimg 5db3 uciB rc=0
FILE:gen/YB01.v  overlapping write bytes 0  contradicting bytes 0
    states: 50, aliases 0, duplicate states 0
    KImg ranges: 139, findings 0
FILE:gen/YB03.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
    KImg ranges: 66, findings 0
RESULT G2a codeptr-controls rc=0
  YF0m.v       29 code (1 function starts, 1 return pcs, 27 other instruction starts),  254 data, 88 at or above the image top 0x5f8378, 279 FINDINGS: 0x10101, 0x103b8, 0x10428, 0x10430, 0x10438, 0x10440, 0x10448, 0x10450, 0x10458, 0x10460, 0x10528, 0x10530 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIB/YF0m.v: 279
codeptr-controls: PASS (must-find paired on all 6 files; must-not-flag 0x8065e)
RESULT G2b codeptr POSITIVE control (tool rc must be 1) rc=1
YD1k.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   25 data, 3 at or above the image top 0x5f3970, 22 FINDINGS: 0x103c0, 0x10468, 0x10568, 0x1cccb, 0x1cce0, 0x20b40, 0x20b44, 0x20dc0, 0x20dc8, 0x20de0, 0x20e40, 0x20e80 [stale 
YD2i.v        2 code (0 function starts, 0 return pcs, 2 other instruction starts),    5 data, 5 at or above the image top 0x5f3970, 7 FINDINGS: 0x10800, 0x80020, 0x8d178, 0x9d000, 0x3fffff, 0x5d9210, 0x5fb000 [stale against cgif_file_fuzzer.asan-ubsan, donor 
YD2j.v        3 code (0 function starts, 0 return pcs, 3 other instruction starts),   71 data, 43 at or above the image top 0x5f3970, 108 FINDINGS: 0x103b8, 0x103c0, 0x10428, 0x10468, 0x10528, 0x10568, 0x1cccb, 0x1cce0, 0x20b40, 0x20b44, 0x20dcd, 0x20de0 [stal
=== G2c PASS 1: every file, each paired with cgif's donor file of the same name, no declaration ===
RESULT G2c codeptr pass 1 rc=1
YB01.v       17 code (12 function starts, 3 return pcs, 2 other instruction starts),  415 data, 99 at or above the image top 0x5f3970, 6 FINDINGS: 0x10800, 0x20000, 0x71c00, 0x100000, 0x161200, 0x38e000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB01.v: 6 STALE (0x10800, 0x20000, 0x71c00, 0x100000, 0x161200, 0x38e000), 1 donor-file li
YB03.v       21 code (9 function starts, 10 return pcs, 2 other instruction starts),  303 data, 64 at or above the image top 0x5f3970, 9 FINDINGS: 0x10101, 0x10800, 0x1ffff, 0x445c0, 0x71c00, 0x100000, 0x100018, 0x38e000, 0x3fffff [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB03.v: 9 STALE (0x10101, 0x10800, 0x1ffff, 0x445c0, 0x71c00, 
YB05.v       37 code (4 function starts, 22 return pcs, 11 other instruction starts),    4 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB05.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YB12.v       25 code (8 function starts, 0 return pcs, 17 other instruction starts),    5 data, 2 at or above the image top 0x5f3970, 1 FINDINGS: 0x55c000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB12.v: 1 STALE (0x55c000), 2 donor-file literals with the same meaning in both images]
YB13.v        1 code (0 function starts, 0 return pcs, 1 other instruction starts),    8 data, 1 at or above the image top 0x5f3970, 1 FINDINGS: 0x55c000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB13.v: 1 STALE (0x55c000), 1 donor-file literals with the same meaning in both images]
YB1h.v        2 code (0 function starts, 0 return pcs, 1 other instruction starts),    8 data, 7 at or above the image top 0x5f3970, 2 FINDINGS: 0x158593, 0x55c000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1h.v: 2 STALE (0x158593, 0x55c000), 1 donor-file literals with the same meaning in both images]
YB1k.v       49 code (1 function starts, 0 return pcs, 46 other instruction starts),    6 data, 43 at or above the image top 0x5f3970, 6 FINDINGS: 0x155593, 0x155793, 0x255513, 0x255793, 0x455593, 0x455793 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1k.v: 6 STALE (0x155593, 0x155793, 0x255513, 0x255793, 0x455593, 0x455793), 0 donor-f
YB1l.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1m.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1v.v        2 code (2 function starts, 0 return pcs, 0 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1v.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YCej.v       21 code (1 function starts, 14 return pcs, 6 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YCej.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YD1k.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   25 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1k.v: 0 STALE (-), 5 donor-file literals with the same meaning in both images]
YD1y.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   13 data, 1 at or above the image top 0x5f3970, 1 FINDINGS: 0x3fffff [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1y.v: 1 STALE (0x3fffff), 1 donor-file literals with the same meaning in both images]
YD2i.v        2 code (1 function starts, 1 return pcs, 0 other instruction starts),    5 data, 5 at or above the image top 0x5f3970, 2 FINDINGS: 0x10800, 0x3fffff [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2i.v: 2 STALE (0x10800, 0x3fffff), 1 donor-file literals with the same meaning in both images]
YD2j.v        3 code (3 function starts, 0 return pcs, 0 other instruction starts),  109 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2j.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YE23.v        9 code (7 function starts, 2 return pcs, 0 other instruction starts),   44 data, 5 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE23.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YE37.v        1 code (1 function starts, 0 return pcs, 0 other instruction starts),   24 data, 9 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE37.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YE3i.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   26 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE3i.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YF0m.v       28 code (15 function starts, 11 return pcs, 2 other instruction starts),  230 data, 61 at or above the image top 0x5f3970, 3 FINDINGS: 0x10101, 0x10800, 0x100000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YF0m.v: 3 STALE (0x10101, 0x10800, 0x100000), 7 donor-file literals with the same meaning in both images]
codeptr: UNMEASURED: 2 of 19 file(s) hold no address literal in range
RESULT G2e declaration evidence rc=0
=== G2d PASS 2: the same + 38 declaration arguments (codeptr-decl.sh) ===
RESULT G2d codeptr pass 2 rc=2
YB01.v       15 code (12 function starts, 3 return pcs, 0 other instruction starts),  407 data, 99 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB01.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x520
YB03.v       19 code (9 function starts, 10 return pcs, 0 other instruction starts),  297 data, 64 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB03.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x520
YB05.v       37 code (4 function starts, 22 return pcs, 11 other instruction starts),    4 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB05.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YB12.v       25 code (8 function starts, 0 return pcs, 17 other instruction starts),    4 data, 2 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB12.v: 0 STALE (-), 2 donor-file literals with the same meaning in both images]
YB13.v        1 code (0 function starts, 0 return pcs, 1 other instruction starts),    7 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB13.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YB1h.v        2 code (0 function starts, 0 return pcs, 1 other instruction starts),    6 data, 7 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1h.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YB1k.v       49 code (1 function starts, 0 return pcs, 46 other instruction starts),    0 data, 43 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1k.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YB1l.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1m.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1v.v        2 code (2 function starts, 0 return pcs, 0 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1v.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YCej.v       21 code (1 function starts, 14 return pcs, 6 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YCej.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YD1k.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   25 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1k.v: 0 STALE (-), 5 donor-file literals with the same meaning in both images]
YD1y.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   12 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1y.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YD2i.v        2 code (1 function starts, 1 return pcs, 0 other instruction starts),    4 data, 5 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2i.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x520 (
YD2j.v        3 code (3 function starts, 0 return pcs, 0 other instruction starts),  109 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2j.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YE23.v        9 code (7 function starts, 2 return pcs, 0 other instruction starts),   44 data, 5 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE23.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YE37.v        1 code (1 function starts, 0 return pcs, 0 other instruction starts),   24 data, 9 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE37.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YE3i.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   26 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE3i.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YF0m.v       28 code (15 function starts, 11 return pcs, 2 other instruction starts),  228 data, 61 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YF0m.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x52
codeptr: UNMEASURED: 2 of 19 file(s) hold no address literal in range
RESULT G3 port_addr_check CONTROL cgif A->B rc=0
DIFFERENT-SYMBOL	12	FLAG
RESULT G3 port_addr_check cgif B -> uci B rc=0
DIFFERENT-SYMBOL	147	kernel 11	FLAG
RESULT G3 pac_table rc=0
| file | numerals (uci / ctl) | uci B flags | control flags (cgif A -> B) | flag classes only in uci B |
| YB01.v | 17633 / 17631 | 1581: DIFFERENT-SYMBOL 79, GEOMETRY-CHANGED 24, KIND-CHANGED 3, NON-ADDRESS-CHANGED 1418, UNPAIRED-PORTED 2, UNPAIRED-SOURCE 54, UNRESOLVED 1 | 325: DIFFERENT-SYMBOL 12, KIND-CHANGED 3, NON-ADDRESS-CHANGED 307, UNRESOLVED 3 | GEOMETRY-CHANGED, UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YB03.v | 2886 / 2886 | 200: DIFFERENT-SYMBOL 33, KIND-CHANGED 1, NON-ADDRESS-CHANGED 164, UNPAIRED-SOURCE 2 | 160: KIND-CHANGED 1, NON-ADDRESS-CHANGED 159 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YCej.v | 1690 / 1678 | 1670: DIFFERENT-SYMBOL 14, NO-COUNTERPART 3, UNPAIRED-PORTED 12, UNPAIRED-SOURCE 1640, UNRESOLVED 1 | 1128: NON-ADDRESS-CHANGED 285, UNPAIRED-PORTED 69, UNRESOLVED 774 | DIFFERENT-SYMBOL, NO-COUNTERPART, UNPAIRED-SOURCE |
| YD1k.v | 206 / 206 | 28: DIFFERENT-SYMBOL 7, KIND-CHANGED 2, NON-ADDRESS-CHANGED 14, UNPAIRED-SOURCE 4, UNRESOLVED 1 | 15: KIND-CHANGED 1, NON-ADDRESS-CHANGED 14 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE, UNRESOLVED |
| YD2j.v | 325 / 325 | 67: DIFFERENT-SYMBOL 1, KIND-CHANGED 2, NON-ADDRESS-CHANGED 48, UNPAIRED-SOURCE 12, UNRESOLVED 4 | 53: KIND-CHANGED 2, NON-ADDRESS-CHANGED 48, UNRESOLVED 3 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE23.v | 1463 / 1463 | 28: DIFFERENT-SYMBOL 1, KIND-CHANGED 1, NON-ADDRESS-CHANGED 18, UNPAIRED-SOURCE 4, UNRESOLVED 4 | 25: KIND-CHANGED 3, NON-ADDRESS-CHANGED 18, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE37.v | 287 / 281 | 96: DIFFERENT-SYMBOL 5, IDENT-MISMATCH 4, KIND-CHANGED 1, NON-ADDRESS-CHANGED 9, UNPAIRED-PORTED 6, UNPAIRED-SOURCE 71 | 12: IDENT-MISMATCH 4, KIND-CHANGED 6, NON-ADDRESS-CHANGED 2 | DIFFERENT-SYMBOL, UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YE3i.v | 50 / 50 | 14: DIFFERENT-SYMBOL 2, KIND-CHANGED 3, NON-ADDRESS-CHANGED 1, UNPAIRED-SOURCE 6, UNRESOLVED 2 | 9: KIND-CHANGED 1, NON-ADDRESS-CHANGED 4, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YF0m.v | 711 / 664 | 213: DIFFERENT-SYMBOL 5, KIND-CHANGED 12, NO-COUNTERPART 3, NON-ADDRESS-CHANGED 16, STALE-DONOR-CODE-POINTER 3, UNPAIRED-PORTED 47, UNPAIRED-SOURCE 70, UNRESOLVED 57 | 86: NON-ADDRESS-CHANGED 8, UNRESOLVED 78 | DIFFERENT-SYMBOL, KIND-CHANGED, NO-COUNTERPART, STALE-DONOR-CODE-POINTER, UNPAIRED-PORTED, UNPAIRED-SOURCE |
uci B verdicts: {'DIFFERENT-SYMBOL': 147, 'GEOMETRY-CHANGED': 24, 'IDENT-MISMATCH': 4, 'IMAGE-EXTENT-SAME': 29, 'INSN-SAME': 114, 'KIND-CHANGED': 26, 'NO-COUNTERPART': 6, 'NON-ADDRESS-CHANGED': 1691, 'NON-ADDRESS-SAME': 18283, 'ROUND-CONSTANT-SAME': 30, 'SAME-CONTENT': 6, 'SAME-GEOMETRY': 3936, 'SAME-SYMBOL': 2329, 'STALE-DONOR-CODE-POINTER': 3, 'UNPAIRED-PORTED': 68, 'UNPAIRED-SOURCE': 1889, 'UNR
control verdicts: {'DIFFERENT-SYMBOL': 12, 'GEOMETRY-CHANGED': 1, 'IDENT-MISMATCH': 4, 'IMAGE-EXTENT-SAME': 32, 'INSN-SAME': 114, 'KIND-CHANGED': 17, 'NON-ADDRESS-CHANGED': 860, 'NON-ADDRESS-SAME': 19556, 'ROUND-CONSTANT-SAME': 82, 'SAME-CONTENT': 41, 'SAME-GEOMETRY': 3966, 'SAME-SYMBOL': 2967, 'UNPAIRED-PORTED': 69, 'UNRESOLVED': 867}
uci B rows of the classes STALE-DONOR-CODE-POINTER / NO-COUNTERPART / IDENT-MISMATCH / GEOMETRY-CHANGED (distinct by file, definition, source value, ported value; count of rows):
  IDENT-MISMATCH x1  YE37.v Lemma zi8_14ea00  src YE37.v:176 0x14ea00 -> dst line 169 0x14ea00  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x168c0[data] in the donor but __sanitizer::useCounts+0x1da40 in the target; same symbol __sanitizer::useCounts, offset 0x168c0 vs 0x1da40; expected 0x14
  IDENT-MISMATCH x1  YE37.v Lemma zi8_14f970  src YE37.v:177 0x14f970 -> dst line 170 0x14f970  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x17830[data] in the donor but __sanitizer::useCounts+0x1e9b0 in the target; same symbol __sanitizer::useCounts, offset 0x17830 vs 0x1e9b0; expected 0x14
  IDENT-MISMATCH x1  YE37.v Theorem x2_realizes / sentence 35  src YE37.v:204 0x14ea00 -> dst line 197 0x14ea00  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x168c0[data] in the donor but __sanitizer::useCounts+0x1da40 in the target; same symbol __sanitizer::useCounts, offset 0x168c0 vs 0x1da40; expected 0x14
  IDENT-MISMATCH x1  YE37.v Theorem x2_realizes / sentence 44  src YE37.v:208 0x14f970 -> dst line 201 0x14f970  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x17830[data] in the donor but __sanitizer::useCounts+0x1e9b0 in the target; same symbol __sanitizer::useCounts, offset 0x17830 vs 0x1e9b0; expected 0x14
  16f8a030c869 has no GENERATOR-FILL class (added in 0767e70e074a); rows with that verdict: control 0, uci B 0
RESULT G3b port_addr_check cb0e CONTROL cgif A->B rc=0
GENERATOR-FILL	506	REPORTED
DIFFERENT-SYMBOL	12	FLAG
FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
RESULT G3b port_addr_check cb0e cgif B -> uci B rc=0
GENERATOR-FILL	45	kernel 37	REPORTED
DIFFERENT-SYMBOL	147	kernel 11	FLAG
FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
RESULT G3b pac_table (cb0e) rc=0
| file | numerals (uci / ctl) | uci B flags | control flags (cgif A -> B) | flag classes only in uci B |
| YB01.v | 17633 / 17631 | 1271: DIFFERENT-SYMBOL 79, KIND-CHANGED 3, NON-ADDRESS-CHANGED 1132, UNPAIRED-PORTED 2, UNPAIRED-SOURCE 54, UNRESOLVED 1 | 38: DIFFERENT-SYMBOL 12, KIND-CHANGED 3, NON-ADDRESS-CHANGED 19, UNRESOLVED 4 | UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YB03.v | 2886 / 2886 | 43: DIFFERENT-SYMBOL 33, KIND-CHANGED 1, NON-ADDRESS-CHANGED 7, UNPAIRED-SOURCE 2 | 2: KIND-CHANGED 1, NON-ADDRESS-CHANGED 1 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YCej.v | 1690 / 1678 | 1670: DIFFERENT-SYMBOL 14, NO-COUNTERPART 3, UNPAIRED-PORTED 12, UNPAIRED-SOURCE 1640, UNRESOLVED 1 | 565: NON-ADDRESS-CHANGED 128, UNPAIRED-PORTED 69, UNRESOLVED 368 | DIFFERENT-SYMBOL, NO-COUNTERPART, UNPAIRED-SOURCE |
| YD1k.v | 206 / 206 | 26: DIFFERENT-SYMBOL 7, KIND-CHANGED 2, NON-ADDRESS-CHANGED 12, UNPAIRED-SOURCE 4, UNRESOLVED 1 | 13: KIND-CHANGED 1, NON-ADDRESS-CHANGED 12 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE, UNRESOLVED |
| YD2j.v | 325 / 325 | 28: DIFFERENT-SYMBOL 1, KIND-CHANGED 2, NON-ADDRESS-CHANGED 9, UNPAIRED-SOURCE 12, UNRESOLVED 4 | 14: KIND-CHANGED 2, NON-ADDRESS-CHANGED 9, UNRESOLVED 3 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE23.v | 1463 / 1463 | 10: DIFFERENT-SYMBOL 1, KIND-CHANGED 1, UNPAIRED-SOURCE 4, UNRESOLVED 4 | 7: KIND-CHANGED 3, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE37.v | 287 / 281 | 92: DIFFERENT-SYMBOL 5, KIND-CHANGED 1, NON-ADDRESS-CHANGED 9, UNPAIRED-PORTED 6, UNPAIRED-SOURCE 71 | 9: KIND-CHANGED 6, NON-ADDRESS-CHANGED 2, UNRESOLVED 1 | DIFFERENT-SYMBOL, UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YE3i.v | 50 / 50 | 13: DIFFERENT-SYMBOL 2, KIND-CHANGED 3, UNPAIRED-SOURCE 6, UNRESOLVED 2 | 8: KIND-CHANGED 1, NON-ADDRESS-CHANGED 3, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YF0m.v | 711 / 664 | 168: DIFFERENT-SYMBOL 5, KIND-CHANGED 6, NON-ADDRESS-CHANGED 8, UNPAIRED-PORTED 39, UNPAIRED-SOURCE 70, UNRESOLVED 40 | 86: NON-ADDRESS-CHANGED 7, UNRESOLVED 79 | DIFFERENT-SYMBOL, KIND-CHANGED, UNPAIRED-PORTED, UNPAIRED-SOURCE |
uci B verdicts: {'DIFFERENT-SYMBOL': 147, 'GENERATOR-FILL': 45, 'IDENT-NAME': 4, 'IMAGE-EXTENT-SAME': 13, 'INSN-SAME': 114, 'KIND-CHANGED': 19, 'NO-COUNTERPART': 3, 'NON-ADDRESS-CHANGED': 1180, 'NON-ADDRESS-SAME': 18366, 'ROUND-CONSTANT-SAME': 30, 'SAME-CONTENT': 6, 'SAME-GEOMETRY': 3938, 'SAME-SYMBOL': 2788, 'UNPAIRED-PORTED': 60, 'UNPAIRED-SOURCE': 1889, 'UNRESOLVED': 54}
control verdicts: {'DIFFERENT-SYMBOL': 12, 'GENERATOR-FILL': 506, 'GEOMETRY-CHANGED': 1, 'IDENT-NAME': 4, 'IMAGE-EXTENT-SAME': 32, 'INSN-SAME': 114, 'KIND-CHANGED': 17, 'NON-ADDRESS-CHANGED': 195, 'NON-ADDRESS-SAME': 19640, 'ROUND-CONSTANT-SAME': 82, 'SAME-CONTENT': 41, 'SAME-GEOMETRY': 3888, 'SAME-SYMBOL': 3523, 'UNPAIRED-PORTED': 69, 'UNRESOLVED': 464}
uci B rows of the classes STALE-DONOR-CODE-POINTER / NO-COUNTERPART / IDENT-MISMATCH / GEOMETRY-CHANGED (distinct by file, definition, source value, ported value; count of rows):
=== G3c GENERATOR-FILL triage (tools/pac_fill.py): every row a measured reason; CONTROL cgif A -> B first ===
RESULT G3c fill triage CONTROL cgif A->B rc=1
GENERATOR-FILL rows: 506, on 236 ported lines: {'YCej.v': 236}
  UNEXPLAINED YCej.v:30 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:32 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:34 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:36 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:38 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:46 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:48 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:50 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:52 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:85 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:87 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:89 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:91 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:94 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:96 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:98 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:100 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:102 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:104 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:106 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:108 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:110 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:112 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:114 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:116 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:118 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:120 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:122 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:124 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:129 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:134 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:136 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:138 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:140 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:146 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:148 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:150 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:152 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:154 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:156 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:161 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:163 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:165 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:167 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:169 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:171 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:173 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:175 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:177 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:179 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:187 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:189 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:191 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:193 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:195 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:197 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:205 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:207 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:209 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:211 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:217 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:220 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:222 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:225 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:227 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:230 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:232 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:234 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:236 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:238 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:240 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:243 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:245 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:247 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:249 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:252 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:253 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:255 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:257 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:258 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:260 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:262 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:263 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:265 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:267 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:268 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:270 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:272 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:273 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:275 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:277 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:278 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:280 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:282 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:283 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:285 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:287 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:288 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:290 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:292 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:293 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:295 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:297 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:298 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:300 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:302 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:303 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:305 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:307 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:308 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:310 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:312 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:313 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:315 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:317 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:318 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:320 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:322 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:323 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:325 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:327 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:328 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:330 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:332 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:333 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:335 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:337 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:338 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:340 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:342 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:343 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:345 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:351 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:355 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:357 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:361 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:363 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:381 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:383 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:385 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:387 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:389 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:391 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:393 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:395 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:397 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:399 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:401 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:403 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:405 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:407 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:409 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:411 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:413 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:415 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:417 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:419 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:421 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:423 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:425 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:427 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:429 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:431 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:432 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:434 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:436 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:437 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:439 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:441 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:442 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:444 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:446 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:447 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:449 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:451 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:452 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:454 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:456 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:457 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:459 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:461 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:462 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:464 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:466 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:467 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:469 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:471 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:472 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:474 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:476 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:477 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:479 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:481 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:489 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:491 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:493 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:495 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:497 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:499 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:501 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:503 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:505 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:507 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:509 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:511 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:513 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:515 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:517 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:519 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:521 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:522 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:524 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:526 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:527 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:529 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:531 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:532 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:534 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:536 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:537 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:539 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:541 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:542 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:544 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:546 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:547 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:549 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:551 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:552 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:554 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:556 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:557 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:559 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:561 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:562 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:564 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
pac_fill: 236 of 236 ported lines UNEXPLAINED (506 GENERATOR-FILL rows)
RESULT G3c fill triage uci B rc=0
GENERATOR-FILL rows: 45, on 24 ported lines: {'YF0m.v': 24}
  YF0m.v:126 row 86 `z8 (ANum 0x97e10) 0xfffffffffffff800  ;` not an af0m FILL: unit image word at 0x97e10 (.got) = 0xfffffffffffff800; donor slot 0x9ef08 holds 0xfffffffffffff800 in cgif's image (.got), the same link-time word, a tp offset (negative), not an address; other unit rows with this cell or value: lines [] -> ACCEPTED
pac_fill: 0 of 24 ported lines UNEXPLAINED (45 GENERATOR-FILL rows)
RESULT G3e port_addr_check e165 CONTROL cgif A->B (4 = findings, as cb0e) rc=4
GENERATOR-FILL	506	REPORTED
FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
FLAGGED 758 rows in 6 classes: DIFFERENT-SYMBOL=12 GEOMETRY-CHANGED=1 KIND-CHANGED=17 NON-ADDRESS-CHANGED=195 UNPAIRED-PORTED=69 UNRESOLVED=464
RESULT G3e port_addr_check e165 cgif B -> uci B (4 = findings) rc=4
GENERATOR-FILL	45	kernel 37	REPORTED
FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
FLAGGED 3348 rows in 7 classes: DIFFERENT-SYMBOL=147 KIND-CHANGED=19 NO-COUNTERPART=3 NON-ADDRESS-CHANGED=1180 UNPAIRED-PORTED=58 UNPAIRED-SOURCE=1887 UNRESOLVED=54
RESULT G3e port_addr_check cb0e same inputs (4 = findings) rc=4
GENERATOR-FILL	45	kernel 37	REPORTED
FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
FLAGGED 3352 rows in 7 classes: DIFFERENT-SYMBOL=147 KIND-CHANGED=19 NO-COUNTERPART=3 NON-ADDRESS-CHANGED=1180 UNPAIRED-PORTED=60 UNPAIRED-SOURCE=1889 UNRESOLVED=54
RESULT G3e triage rc=0
TRIAGE port_addr_check e165063a0081 vs cb0e067e3bae on the final 19 files (pac_moved.py: rows keyed by file, line, sentence, index, values)
MOVED rows (same key, another verdict): 0
GONE rows (old run only): 4
  GONE UNPAIRED-SOURCE src YE37.v:146 dst YE37.v: `Lemma shbytes_present / sentence 17` idx  0x1 ->  | sentence missing in ported file
  GONE UNPAIRED-SOURCE src YE37.v:147 dst YE37.v: `Lemma shbytes_present / sentence 18` idx  0x0 ->  | sentence missing in ported file
  GONE UNPAIRED-PORTED src YE37.v: dst YE37.v:147 `Lemma shbyte_present / sentence 18` idx   -> 0x1 | sentence missing in source file
  GONE UNPAIRED-PORTED src YE37.v: dst YE37.v:148 `Lemma shbyte_present / sentence 19` idx   -> 0x0 | sentence missing in source file
NEW rows (new run only): 2
  NEW  NON-ADDRESS-SAME src YE37.v:146 dst YE37.v:147 `Lemma shbytes_present / sentence 17` idx 0 0x1 -> 0x1 | 
  NEW  NON-ADDRESS-SAME src YE37.v:147 dst YE37.v:148 `Lemma shbytes_present / sentence 18` idx 0 0x0 -> 0x0 | 
GENERATOR-FILL rows of the new run: 45, basis: {'positional, donor object absent from the target': 36, 'generator mark': 1, 'in-place copy, no donor row': 8}
TRIAGE YH03 rows in this run: 0 (YH03.v is not one of the 19 files)
TRIAGE GENERATOR-FILL rows of e165, each with a measured reason (pac_fill.py; CONTROL first on cgif A->B):
TRIAGE pac_fill CONTROL cgif A->B rc=1 (1 = it refuses the 236 YCej lines outside its YF0m rules: fails closed)
pac_fill: 236 of 236 ported lines UNEXPLAINED (506 GENERATOR-FILL rows)
TRIAGE pac_fill uci B rc=0
GENERATOR-FILL rows: 45, on 24 ported lines: {'YF0m.v': 24}
  YF0m.v:126 row 86 `z8 (ANum 0x97e10) 0xfffffffffffff800  ;` not an af0m FILL: unit image word at 0x97e10 (.got) = 0xfffffffffffff800; donor slot 0x9ef08 holds 0xfffffffffffff800 in cgif's image (.got), the same link-time word, a tp offset (negative), not an address; other unit rows with this cell or value: lines [] -> ACCEPTED
pac_fill: 0 of 24 ported lines UNEXPLAINED (45 GENERATOR-FILL rows)
TRIAGE independent .symtab check of every symbol-named definition (symname_check.py; CONTROL first: 1 right + 2 planted wrong):
TRIAGE symname CONTROL rc=1 (1 = the two planted rows caught)
TRIAGE symname uci B rc=0
=== G4 CONTROL FIRST: planted copy (plant_uciB.py), .text end + 4 = 0x95b94 in CODE cells must be flagged, in a DATA cell not ===
RESULT G4 plant rc=0
planted P1-CODE YF0m.v:105  z8 (ANum 0x98f80) 0x90458 -> z8 (ANum 0x98f80) 0x95b94
planted P2-CODE YF0m.v:22  [[0x51a24; 0x7ee9c] -> [[0x95b94; 0x7ee9c]
planted P3-CODE YB12.v:15  x_memset := 0x9085c -> x_memset := 0x95b94
planted P4-CODE YB01.v:22  SS 519752 [ELit 0; ELit 550212; -> SS 519752 [ELit 0; ELit 613268;
planted D1-DATA YF0m.v:74  z8 (ANum 0x9c8f8) 0x100ffffffff -> z8 (ANum 0x9c8f8) 0x95b94
RESULT G4 classify PLANTED (must be rc 1) rc=1
== uciB.planted: image fuzz_uci.asan-ubsan sha256 a1b86e424add; .text [0x2fbf0, 0x95b90) = 104424 words; image [0x10000, 0x5f4000); objdump source = twin: True
   files $UCIB_GATEWORK/classify/planted: 23745 literals, 4185 >= .text end (1808 inside the image, 2377 past it)
   FINDINGS (CODE role, value not in .text): 4 (of them >= .text end: 4)
  PLANTED CONTROL: PASS
RESULT G4 planted control verdict rc=0
RESULT G4 classify uciB rc=0
   FINDINGS (CODE role, value not in .text): 0 (of them >= .text end: 0)
RESULT G4 coverage report rc=0
RESULT G5 recount rc=0
cgifB-control states 50 kn lists 50 aliases 0 duplicate state bodies 0 duplicate kn bodies 0 arrival SS values ['524320'] all == main 0x80020 True
uciB states 50 kn lists 50 aliases 0 duplicate state bodies 0 duplicate kn bodies 0 arrival SS values ['519752'] all == main 0x7ee48 True
RESULT G6 keyed scan rc=0
== fuzz_uci B own __asan_stack_malloc_* symbols (twin .symtab $UCIB_UBS)
   0x3c1b8 __asan_stack_malloc_1 size 400 STT_FUNC
   classes defined (STT_FUNC): 1  -> T0.4 item 1 (one class, __asan_stack_malloc_1 @0x3c1b8): True
   A/AF0l.v  forbidden-literal hits 2: [('AF0l.v', 11, '0x3c8a4', 'cgif A __asan_stack_malloc_1'), ('AF0l.v', 11, '0x3ca34', 'cgif A __asan_stack_malloc_2')]
   A/AF0l.v  stack_malloc lines 1: [(11, 'pc_stack_malloc := fun cid => if cid =? 1 then 0x3c8a4 else if cid =? 2 then 0x3ca34 else 0;')]
   YF0l.v    forbidden-literal hits 2: [('YF0l.v', 11, '0x3c8d4', 'cgif B __asan_stack_malloc_1'), ('YF0l.v', 11, '0x3ca64', 'cgif B __asan_stack_malloc_2')]
   YF0l.v    stack_malloc lines 1: [(11, 'pc_stack_malloc := fun cid => if cid =? 1 then 0x3c8d4 else if cid =? 2 then 0x3ca64 else 0;')]
   YB01   forbidden 0  stack_malloc lines 0   
   YB03   forbidden 0  stack_malloc lines 0   
   YB05   forbidden 0  stack_malloc lines 0   
   YB12   forbidden 0  stack_malloc lines 0   
   YB13   forbidden 0  stack_malloc lines 0   
   YB1h   forbidden 0  stack_malloc lines 0   
   YB1k   forbidden 0  stack_malloc lines 0   
   YB1l   forbidden 0  stack_malloc lines 0   
   YB1m   forbidden 0  stack_malloc lines 0   
   YB1v   forbidden 0  stack_malloc lines 0   
   YCej   forbidden 0  stack_malloc lines 0   
   YD1k   forbidden 0  stack_malloc lines 0   
   YD1y   forbidden 0  stack_malloc lines 0   
   YD2i   forbidden 0  stack_malloc lines 0   
   YD2j   forbidden 0  stack_malloc lines 0   
   YE23   forbidden 0  stack_malloc lines 0   
   YE37   forbidden 0  stack_malloc lines 0   
   YE3i   forbidden 0  stack_malloc lines 0   
   YF0m   forbidden 0  stack_malloc lines 0   
   TOTAL forbidden literals in 19 files: 0 -> PASS
RESULT G7a pins check rc=0
RESULT G7b stamp YB01 (file Read-from line: line 5; stamp writes it at line 10, text EQUAL; every other line EQUAL) rc=0
RESULT G7b stamp YB03 (file Read-from line: line 5; stamp writes it at line 8, text EQUAL; every other line EQUAL) rc=0
RESULT G7b stamp YB05 (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB12 (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YB12.v atable image fields (key = field): 3 rows, exactly the set fuzz_uci.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS YB12.v stops_more (key = self-loop site): 13 rows, exactly the set fuzz_uci.asan-ubsan (13 self-loops, in .text) defines
RESULT G7b stamp YB13 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YB1h (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB1k (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
RESULT G7b stamp YB1l (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB1m (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YB1v (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YCej (file Read-from line: line 6; stamp writes it at line 6, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD1k (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD1y (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YD2i (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD2j (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YD2j.v regions (key = region name): 31 rows, exactly the set the region definitions of YD2j.v defines
PASS YD2j.v anchor roles (key = role, present iff the image defines its object): 16 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
RESULT G7b stamp YE23 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YE37 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YE3i (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YF0m (file Read-from line: line 6; stamp writes it at line 6, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=2
PASS YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
pins: NOT STAMPED $UCIB_GATEWORK/stamp/YF0m.v: an AF0m / YF0m is checked with the OTHER image's table (keyset realset: the __interception::real_* rows of A and B must agree), and this run has no --pair: the REAL rows are UNMEASURED. Give --pair <the other image's F0m> --pair-syms <its symbol table>
RESULT G7c stamp YF0m --pair (stamped copy BYTE-EQUAL; the same multiset of lines: True (only line order in the header moves)) rc=1
PASS YF0m.pair.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS YF0m.pair.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE YF0m.pair.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
RESULT G7d emitcheck rc=0
RESULT G7e keyset CONTROL cgif released YB12 rc=1
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YB12.v atable image fields (key = field): 3 rows, exactly the set cgif_file_fuzzer.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS cgif/YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the names of record cgif/YB1w.v defines
keyset: REFUSED cgif/YB12.v stops_more (key = self-loop site)
keyset: REFUSED
RESULT G7e keyset CONTROL cgif released YF0m rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 35 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 5 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) and the PT_LOAD hull defines
PASS cgif/YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 4 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 24 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
NOTE cgif/YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
keyset: PASS for the per-file row sets (measured: 1 file(s), 5 sub-checks, 70 rows); REAL() rows of 1 AF0m / YF0m UNMEASURED (single files: run `keyset.py realset` on the A+B pair)
RESULT G7e keyset CONTROL cgif released YD2j rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YD2j.v regions (key = region name): 33 rows, exactly the set the region definitions of $UCIB_GATEWORK/in/cgif/YD2j.v defines
UNMEASURED cgif/YD2j.v: no twin, so the anchor roles (gen_ad2.ANCHOR_NAMES) are not checked by symbol
keyset: PASS for the measured sub-checks (measured: 1 file(s), 1 sub-checks, 33 rows); UNMEASURED sub-checks (see the UNMEASURED lines) in: cgif/YD2j.v
RESULT G7e keyset CONTROL cgif released YB1k rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the names of record cgif/YB1w.v defines
keyset: PASS (measured: 1 file(s), 1 sub-checks, 3 rows)
RESULT G7e keyset CONTROL cgif YB12 (atable re-emitted) rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS $WK/ctl/YB12.cgif.v atable image fields (key = field): 3 rows, exactly the set cgif_file_fuzzer.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS $WK/ctl/YB12.cgif.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the names of record cgif/YB1w.v defines
PASS $WK/ctl/YB12.cgif.v stops_more (key = self-loop site): 13 rows, exactly the set cgif_file_fuzzer.asan-ubsan (13 self-loops, in .text) defines
keyset: PASS (measured: 1 file(s), 3 sub-checks, 27 rows)
RESULT G7e keyset uciB rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS gen/YB12.v atable image fields (key = field): 3 rows, exactly the set fuzz_uci.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS gen/YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS gen/YB12.v stops_more (key = self-loop site): 13 rows, exactly the set fuzz_uci.asan-ubsan (13 self-loops, in .text) defines
PASS gen/YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS gen/YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE gen/YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
PASS gen/YD2j.v regions (key = region name): 31 rows, exactly the set the region definitions of $UCIB_GATEWORK/in/gen/YD2j.v defines
PASS gen/YD2j.v anchor roles (key = role, present iff the image defines its object): 16 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS gen/YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
keyset: PASS for the per-file row sets (measured: 4 file(s), 11 sub-checks, 103 rows); REAL() rows of 1 AF0m / YF0m UNMEASURED (single files: run `keyset.py realset` on the A+B pair)
RESULT G8 ifchk CONTROL cgif B rc=0
ifchk: 267 cells (sym 22, abs 210, shadow 35) x 50 states: 13350 = stated, 0 different, 0 undetermined (None), 0 inexpressible
RESULT G8 ifchk no-states (want 2) rc=2
ifchk: REFUSED: no states named HS_tfib_N in $UCIB_GATEWORK/ctl/empty.YB01.v
RESULT G8 ifchk --nholes 49 (want 2) rc=2
ifchk: REFUSED: $UCIB_GATEWORK/in/raw/YB01.v holds 50 hand-off states, expected 49 (--nholes); a check over 50 states proves nothing about the others
planted: 'z8 (ANum 0x130c28) 0x1 ' -> 'z8 (ANum 0x130c28) 0x2 '
RESULT G8 plant rc=0
RESULT G8 ifchk PLANTED (want 1) rc=1
RESULT G8 ifchk uciB rc=0
ifchk: 250 cells (sym 22, abs 217, shadow 11) x 50 states: 12500 = stated, 0 different, 0 undetermined (None), 0 inexpressible
RESULT G9 selftest 542898b2/4161c861 rc=0
SELFTEST PASS shadowcheck 542898b23954d1fc ownedcheck 4161c861b0d991bb
RESULT G9 ownedcheck-352fb92f CONTROL rc=0
owned ranges 37, const cells 245, UNOWNED 0, OVERCLAIM 0, UNPARSED 0
RESULT G9 ownedcheck-352fb92f uciB rc=0
owned ranges 35, const cells 228, UNOWNED 0, OVERCLAIM 0, UNPARSED 0
RESULT G9 ownedcheck-4161c861 CONTROL rc=0
owned ranges 37, const cells 245, UNOWNED 0, OVERCLAIM 0, UNPARSED 0
RESULT G9 ownedcheck-4161c861 uciB rc=0
owned ranges 35, const cells 228, UNOWNED 0, OVERCLAIM 0, UNPARSED 0
RESULT G9 shadowcheck-e04173f5 CONTROL rc=0
Tfib_const_shadow: 35 cells, 0 wrong
RESULT G9 shadowcheck-e04173f5 uciB rc=0
Tfib_const_shadow: 11 cells, 0 wrong
RESULT G9 shadowcheck-6dccc6f9 CONTROL rc=0
Tfib_const_shadow: 35 cells, 0 wrong
RESULT G9 shadowcheck-6dccc6f9 uciB rc=0
Tfib_const_shadow: 11 cells, 0 wrong
RESULT G9 shadowcheck-542898b2 CONTROL rc=0
Tfib_const_shadow: 35 cells, 0 wrong
RESULT G9 shadowcheck-542898b2 uciB rc=0
Tfib_const_shadow: 11 cells, 0 wrong
=== G10 lowbeg.py with gen_ad1k of bundle 8cd7 (814c81b8966e, YD1k's generator): CONTROL cgif B first, then fuzz_uci B ===
RESULT G10 lowbeg (8cd7) rc=0
$UCIB_CB sha256=1c29845fe605 descriptors=3 lowest_beg=0x20dc0 mod64=0 hull_bound=0x20dc0 aligned (unchanged)
$UCIB_UB sha256=a1b86e424add descriptors=1 lowest_beg=0x20ca0 mod64=32 hull_bound=0x20c80 AFFECTED (old NHULL = beg is wrong)
=== G10 lowbeg.py with gen_ad1k of bundle dbb5 (43a0cf0abc67): CONTROL cgif B first, then fuzz_uci B ===
RESULT G10 lowbeg (dbb5) rc=0
$UCIB_CB sha256=1c29845fe605 descriptors=3 lowest_beg=0x20dc0 mod64=0 hull_bound=0x20dc0 aligned (unchanged)
$UCIB_UB sha256=a1b86e424add descriptors=1 lowest_beg=0x20ca0 mod64=32 hull_bound=0x20c80 AFFECTED (old NHULL = beg is wrong)
  cgif B (control)  lowbeg hull_bound 0x20dc0; YD1k `p + n <= ...` bounds ['0x20dc0'] at lines [212, 226] -> EQUAL
  fuzz_uci B        lowbeg hull_bound 0x20c80; YD1k `p + n <= ...` bounds ['0x20c80'] at lines [214, 228] -> EQUAL
RESULT G10 YD1k hull text = lowbeg hull (cgif control + uci) rc=0
=== G11a gen_exitB.py --af0m WK/raw/YF0m.v (its own controls C1.. run first inside; rodata_chk / cellr / shbyte_chk / DRVW_not_owned) ===
RESULT G11a gen_exitB --af0m rc=0
  C3b decode B   __asan_unregister_globals 0x3ef00: addi a1,a0,1 @0x3f0a8; bgeu a1,s2 @0x3f0ac -> 0x3f170 `sb zero, 0(a0)`; s2 = 2 @['0x3f080'] (capstone 5.0.7): PASS
  C3b fuzz_uci B __asan_unregister_globals 0x3e9d8: addi a1,a0,1 @0x3eb80; bgeu a1,s2 @0x3eb84 -> 0x3ec48 `sb zero, 0(a0)`; s2 = 2 @['0x3eb58'] (capstone 5.0.7): PASS
     F_STDOUT     YE23 0x9b7c8    unit 0x9b7c8    PASS
     F_STDERR     YE23 0x9b6d8    unit 0x9b6d8    PASS
     A_GOT_canary YE23 0x97db0    unit 0x97db0    PASS
     A_canary     YE23 0x5f20d0   unit 0x5f20d0   PASS
     A_GOT_CANARY (YE22) 0x97db0 = A_GOT_canary: PASS
     [0x9b690, 0x9b9d0) = oft_arg0 .. asan_globals PASS
     [0x9ba48, 0x9ba90) = __do_init.__initialized .. __do_fini.__finalized PASS
     [0x5d1750, 0x5d2038) = target_run.initialized .. builtin_tls+112 PASS
     [0x5f20e0, 0x5f2300) = finished_atexit .. exit.exit_lock PASS
     X1 YD1y 0xa2bc8   -> 0x9ba48   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YD1y 0xa2c10   -> 0x9ba90   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YD1y 0x5d88d0  -> 0x5d1750  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YD1y 0x5f9260  -> 0x5f20e0  cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YD1y 0x5f9480  -> 0x5f2300  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9e1d8   -> 0x970f8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9e1e0   -> 0x97100   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9e1e8   -> 0x97108   cgif refs 77 (moved 77) == uci refs 77: PASS
     X1 YE23 0x9eea8   -> 0x97db0   cgif refs 51 (moved 50, not identical code ['0x92c58']) == uci refs 50: PASS
     X1 YE23 0x9eed8   -> 0x97de0   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9eee0   -> 0x97de8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9eee8   -> 0x97df0   cgif refs 3 (moved 3) == uci refs 3: PASS
     X1 YE23 0xa27e8   -> 0x9b6d8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0xa28d0   -> 0x9b7c0   cgif refs 4 (moved 4) == uci refs 4: PASS
     X1 YE23 0xa28d8   -> 0x9b7c8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0xa29c0   -> 0x9b8b0   cgif refs 4 (moved 4) == uci refs 4: PASS
     X1 YE23 0xa2ab0   -> 0x9b9a0   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0xa2ab8   -> 0x9b9a8   cgif refs 3 (moved 3) == uci refs 3: PASS
     X1 YE23 0xa2bc0   -> 0x9ba40   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0xa2bc8   -> 0x9ba48   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0xa2c10   -> 0x9ba90   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0x5d88d4  -> 0x5d1754  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x5f9260  -> 0x5f20e0  cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0x5f9480  -> 0x5f2300  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x5f94a3  -> 0x5f2323  cgif refs 4 (moved 4) == uci refs 4: PASS
     X1 YE23 0x5f94a4  -> 0x5f2324  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x5f9900  -> 0x5f2780  cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE37 0x103a0   -> 0x103a0   cgif refs 36 (moved 36) == uci refs 36: PASS
     X1 YE37 0x9e1e8   -> 0x97108   cgif refs 77 (moved 77) == uci refs 77: PASS
     X1 YE37 0x9ee98   -> 0x97da0   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE37 0xa0098   -> 0x98f88   cgif refs 2 (moved 1, not identical code ['0x51b3c']) == uci refs 1: PASS
     X1 YE37 0xa00d0   -> 0x98fc0   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE37 0xa2bc0   -> 0x9ba40   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE37 0xa5adc   -> 0x9e95c   cgif refs 3 (moved 3) == uci refs 3: PASS
     X1 YE37 0xa6f58   -> 0x9fdd8   cgif refs 8 (moved 8) == uci refs 8: PASS
     X1 YE37 0xa6f60   -> 0x9fde0   cgif refs 3 (moved 3) == uci refs 3: PASS
  --af0m $UCIB_GATEWORK/in/raw/YF0m.v: rodata_chk / cellr / shbyte_chk misses 0 []; DRVW_not_owned overlaps 0 []
PASS
  re-generated YE23.v DIFFERS from $UCIB_EXITWORK/out/YE23.v
  YE23.v: with every `From .. Require ..` sentence removed and TfibSyms -> UciSyms (the module-path / record rewrite), the re-generated (donor-namespace) text and WK/gen are DIFFERENT (1664 / 1664 non-blank lines)
  re-generated YD1y.v DIFFERS from $UCIB_EXITWORK/out/YD1y.v
  YD1y.v: with every `From .. Require ..` sentence removed and TfibSyms -> UciSyms (the module-path / record rewrite), the re-generated (donor-namespace) text and WK/gen are DIFFERENT (357 / 357 non-blank lines)
  re-generated YE37.v DIFFERS from $UCIB_EXITWORK/out/YE37.v
  YE37.v: with every `From .. Require ..` sentence removed and TfibSyms -> UciSyms (the module-path / record rewrite), the re-generated (donor-namespace) text and WK/gen are DIFFERENT (223 / 223 non-blank lines)
cgif EQUAL
RESULT G11b XW2 cgif rc=0
uciB EQUAL
RESULT G11b XW2 uciB rc=0
  logs/ab1hk.control.log:3:control YB1h: EQUAL
  logs/ab1hk.control.log:4:control YB1k: EQUAL
  logs/boxb1.control.B.log:4:boxb1 control YB1v.v: EQUAL
  logs/boxb1.control.B.log:5:boxb1 control YB1h.v: EQUAL
  logs/boxb1.control.B.log:6:boxb1 control YB1k.v: EQUAL
  logs/run_restB.gen2.log:13:PASS YB12.v atable image fields (key = field): 3 rows, exactly the set fuzz_uci.asan-ubsan (e_entry, PT_LOAD hull) defines
  logs/run_restB.gen2.log:14:PASS YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
  logs/run_restB.gen2.log:15:PASS YB12.v stops_more (key = self-loop site): 13 rows, exactly the set fuzz_uci.asan-ubsan (13 self-loops, in .text) defines
  logs/run_restB.gen2.log:19:atable planted control (regen == file; planted x_memset +4 caught: 2 diff lines) rc=0
  logs/run_restB.gen2.log:22:control YD2i BYTE-EQUAL rc=0
  logs/run_restB.gen2.log:23:control YD2j BYTE-EQUAL rc=0
  logs/run_restB.gen2.log:58:PASS YD2j.v regions (key = region name): 31 rows, exactly the set the region definitions of YD2j.v defines
  logs/run_restB.gen2.log:59:PASS YD2j.v anchor roles (key = role, present iff the image defines its object): 16 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
  logs/run_restB.gen2.log:65:control YD1k BYTE-EQUAL rc=0
  logs/run_restB.gen2.log:75:control BYTE-EQUAL to cgif's YE3i.v rc=0
  logs/run_restB.gen2.log:79:IMG_RO [0x10000, 0x2ebf0) = RO PT_LOAD file range [0x10000, 0x2ebf0); 13 chunks; recomputed region minus owned: EQUAL
  logs/run_restB.gen2.log:83:nsB YB12.v: Require (dir, module) set EQUAL to fuzz_grant B lib/B/YB12.v at 4f87de75d67 (2 modules)
  logs/run_restB.gen2.log:86:nsB YD2i.v: Require (dir, module) set EQUAL to fuzz_grant B lib/B/YD2i.v at 4f87de75d67 (29 modules)
  logs/run_restB.gen2.log:89:nsB YD2j.v: Require (dir, module) set EQUAL to fuzz_grant B lib/B/YD2j.v at 4f87de75d67 (3 modules)
  logs/run_restB.gen2.log:92:nsB YD1k.v: Require (dir, module) set EQUAL to fuzz_grant B lib/B/YD1k.v at 4f87de75d67 (55 modules)
  logs/run_restB.gen2.log:95:nsB YE3i.v: Require (dir, module) set EQUAL to fuzz_grant B lib/B/YE3i.v at 4f87de75d67 (22 modules)
  logs/af0m/run_af0mB.gen2.log:4:CONTROL cgif B (--names none): BYTE-EQUAL
  logs/af0m/run_af0mB.gen2.log:6:CONTROL cgif B (cgif nm, TFIB_TR0 / TFIB_HASH derived): BYTE-EQUAL
  logs/af0m/run_af0mB.gen2.log:31:redzone-tail self-check: PASS (1 read-only tails, 24 bytes, each covered at its full descriptor length: (0x20ca8, 0x18))
  logs/af0m/run_af0mB.gen2.log:50:index gate: PASS (178 kept base rows at their base index; 217 output rows)
  logs/af0m/run_af0mB.gen2.log:51:xowned gate: PASS (217 const_abs cells, 11 shadow cells, all inside Tfib_owned_static or its shadow)
  logs/af0m/run_af0mB.gen2.log:52:am_const gate: PASS (every byte of all 217 Tfib_const_abs cells pinned by all 50 states; 761 bytes come from the image module's .bss zero fill under a KImg range)
  logs/af0m/run_af0mB.gen2.log:54:symbol gate PASS: _ZN6__asanL19malloc_context_sizeE (0x9fdfc) = [30] in all 50 states
  logs/af0m/run_af0mB.gen2.log:55:symbol gate PASS: _ZN6__asanL11asan_initedE (0x9fdd8) = [1] in all 50 states
  logs/af0m/run_af0mB.gen2.log:59:PASS YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
  logs/af0m/run_af0mB.gen2.log:60:PASS YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
  logs/af0m/run_af0mB.gen2.log:61:PASS YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
  logs/af0m/run_af0mB.gen2.log:62:PASS YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
  logs/af0m/run_af0mB.gen2.log:63:PASS YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
```

## FINAL: G7 re-run after the harness fix of its pins --pair input (G0 reads image A's AF0m from core f47e2a8927b9)

```
RESULT G7a pins check rc=0
RESULT G7b stamp YB01 (file Read-from line: line 5; stamp writes it at line 10, text EQUAL; every other line EQUAL) rc=0
RESULT G7b stamp YB03 (file Read-from line: line 5; stamp writes it at line 8, text EQUAL; every other line EQUAL) rc=0
RESULT G7b stamp YB05 (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB12 (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YB12.v atable image fields (key = field): 3 rows, exactly the set fuzz_uci.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS YB12.v stops_more (key = self-loop site): 13 rows, exactly the set fuzz_uci.asan-ubsan (13 self-loops, in .text) defines
RESULT G7b stamp YB13 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YB1h (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB1k (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
RESULT G7b stamp YB1l (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB1m (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YB1v (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YCej (file Read-from line: line 6; stamp writes it at line 6, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD1k (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD1y (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YD2i (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD2j (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YD2j.v regions (key = region name): 31 rows, exactly the set the region definitions of YD2j.v defines
PASS YD2j.v anchor roles (key = role, present iff the image defines its object): 16 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
RESULT G7b stamp YE23 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YE37 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YE3i (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YF0m (file Read-from line: line 6; stamp writes it at line 6, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=2
PASS YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
pins: NOT STAMPED $UCIB_GATEWORK/stamp/YF0m.v: an AF0m / YF0m is checked with the OTHER image's table (keyset realset: the __interception::real_* rows of A and B must agree), and this run has no --pair: the REAL rows are UNMEASURED. Give --pair <the other image's F0m> --pair-syms <its symbol table>
RESULT G7c stamp YF0m --pair (stamped copy DIFFERS; the same multiset of lines: True (only line order in the header moves)) rc=0
PASS YF0m.pair.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS YF0m.pair.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE YF0m.pair.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
PASS REAL rows, A == B (key = N of __interception::real_N): 14 rows, exactly the set A (fuzz_uci.asan) defines
PASS donor REAL rows, A == B (each keyed by the donor image's own symbol table): 16 rows, exactly the set donor A (cgif_file_fuzzer.asan.nm) defines
PASS REAL rows, donor subset of ours (A): donor 16 ['__tls_get_addr', 'atoll', 'bcmp', 'fclose', 'fflush', 'fopen', 'fwrite', 'memchr', 'memcmp', 'memcpy', 'memset', 'read', 'strchr', 'strnlen', 'vfprintf', 'vprintf']; 13 of them this image defines real_N for, all present; not in this image (no real
PASS REAL rows, donor subset of ours (B): donor 16 ['__tls_get_addr', 'atoll', 'bcmp', 'fclose', 'fflush', 'fopen', 'fwrite', 'memchr', 'memcmp', 'memcpy', 'memset', 'read', 'strchr', 'strnlen', 'vfprintf', 'vprintf']; 13 of them this image defines real_N for, all present; not in this image (no real
RESULT G7d emitcheck rc=0
RESULT G7e keyset CONTROL cgif released YB12 rc=1
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YB12.v atable image fields (key = field): 3 rows, exactly the set cgif_file_fuzzer.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS cgif/YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the names of record cgif/YB1w.v defines
keyset: REFUSED cgif/YB12.v stops_more (key = self-loop site)
keyset: REFUSED
RESULT G7e keyset CONTROL cgif released YF0m rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 35 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 5 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) and the PT_LOAD hull defines
PASS cgif/YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 4 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 24 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
NOTE cgif/YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
keyset: PASS for the per-file row sets (measured: 1 file(s), 5 sub-checks, 70 rows); REAL() rows of 1 AF0m / YF0m UNMEASURED (single files: run `keyset.py realset` on the A+B pair)
RESULT G7e keyset CONTROL cgif released YD2j rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YD2j.v regions (key = region name): 33 rows, exactly the set the region definitions of $UCIB_GATEWORK/in/cgif/YD2j.v defines
UNMEASURED cgif/YD2j.v: no twin, so the anchor roles (gen_ad2.ANCHOR_NAMES) are not checked by symbol
keyset: PASS for the measured sub-checks (measured: 1 file(s), 1 sub-checks, 33 rows); UNMEASURED sub-checks (see the UNMEASURED lines) in: cgif/YD2j.v
RESULT G7e keyset CONTROL cgif released YB1k rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the names of record cgif/YB1w.v defines
keyset: PASS (measured: 1 file(s), 1 sub-checks, 3 rows)
RESULT G7e keyset CONTROL cgif YB12 (atable re-emitted) rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS $WK/ctl/YB12.cgif.v atable image fields (key = field): 3 rows, exactly the set cgif_file_fuzzer.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS $WK/ctl/YB12.cgif.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the names of record cgif/YB1w.v defines
PASS $WK/ctl/YB12.cgif.v stops_more (key = self-loop site): 13 rows, exactly the set cgif_file_fuzzer.asan-ubsan (13 self-loops, in .text) defines
keyset: PASS (measured: 1 file(s), 3 sub-checks, 27 rows)
RESULT G7e keyset uciB rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS gen/YB12.v atable image fields (key = field): 3 rows, exactly the set fuzz_uci.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS gen/YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS gen/YB12.v stops_more (key = self-loop site): 13 rows, exactly the set fuzz_uci.asan-ubsan (13 self-loops, in .text) defines
PASS gen/YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS gen/YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE gen/YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
PASS gen/YD2j.v regions (key = region name): 31 rows, exactly the set the region definitions of $UCIB_GATEWORK/in/gen/YD2j.v defines
PASS gen/YD2j.v anchor roles (key = role, present iff the image defines its object): 16 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS gen/YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
keyset: PASS for the per-file row sets (measured: 4 file(s), 11 sub-checks, 103 rows); REAL() rows of 1 AF0m / YF0m UNMEASURED (single files: run `keyset.py realset` on the A+B pair)
```

## FINAL: port_addr_check e165063a0081 vs cb0e067e3bae, moved / new / gone rows, GENERATOR-FILL triage, .symtab check

```
TRIAGE port_addr_check e165063a0081 vs cb0e067e3bae on the final 19 files (pac_moved.py: rows keyed by file, line, sentence, index, values)
MOVED rows (same key, another verdict): 0
GONE rows (old run only): 4
  GONE UNPAIRED-SOURCE src YE37.v:146 dst YE37.v: `Lemma shbytes_present / sentence 17` idx  0x1 ->  | sentence missing in ported file
  GONE UNPAIRED-SOURCE src YE37.v:147 dst YE37.v: `Lemma shbytes_present / sentence 18` idx  0x0 ->  | sentence missing in ported file
  GONE UNPAIRED-PORTED src YE37.v: dst YE37.v:147 `Lemma shbyte_present / sentence 18` idx   -> 0x1 | sentence missing in source file
  GONE UNPAIRED-PORTED src YE37.v: dst YE37.v:148 `Lemma shbyte_present / sentence 19` idx   -> 0x0 | sentence missing in source file
NEW rows (new run only): 2
  NEW  NON-ADDRESS-SAME src YE37.v:146 dst YE37.v:147 `Lemma shbytes_present / sentence 17` idx 0 0x1 -> 0x1 | 
  NEW  NON-ADDRESS-SAME src YE37.v:147 dst YE37.v:148 `Lemma shbytes_present / sentence 18` idx 0 0x0 -> 0x0 | 
GENERATOR-FILL rows of the new run: 45, basis: {'positional, donor object absent from the target': 36, 'generator mark': 1, 'in-place copy, no donor row': 8}
TRIAGE YH03 rows in this run: 0 (YH03.v is not one of the 19 files)
TRIAGE GENERATOR-FILL rows of e165, each with a measured reason (pac_fill.py; CONTROL first on cgif A->B):
TRIAGE pac_fill CONTROL cgif A->B rc=1 (1 = it refuses the 236 YCej lines outside its YF0m rules: fails closed)
pac_fill: 236 of 236 ported lines UNEXPLAINED (506 GENERATOR-FILL rows)
TRIAGE pac_fill uci B rc=0
GENERATOR-FILL rows: 45, on 24 ported lines: {'YF0m.v': 24}
  YF0m.v:108 row 68 `z8 (ANum 0x98e40) 0x90428` FILL 68 = duplicate of row 67 (line 107 `z8 (ANum 0x98e40) 0x90428  ;`): identical and not a fill itself: True; row 67 by name: cell _ZN14__interception11real_memcmpE+0x0, value memcmp+0x0; donor row with the same cell + value names: cgif line 96 `z8 (ANum 0x9ff38) 0x974d8  ;`; donor slot 0x9ff40 = cgif _ZN14__interception9real_bcmpE+0x0; this image 
  YF0m.v:126 row 86 `z8 (ANum 0x97e10) 0xfffffffffffff800  ;` not an af0m FILL: unit image word at 0x97e10 (.got) = 0xfffffffffffff800; donor slot 0x9ef08 holds 0xfffffffffffff800 in cgif's image (.got), the same link-time word, a tp offset (negative), not an address; other unit rows with this cell or value: lines [] -> ACCEPTED
  YF0m.v:204 row 164 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 164 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b20 = cgif asan_globals+0x40 (descriptor 1 
  YF0m.v:205 row 165 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 165 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b28 = cgif asan_globals+0x48 (descriptor 1 
  YF0m.v:206 row 166 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 166 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b30 = cgif asan_globals+0x50 (descriptor 1 
  YF0m.v:207 row 167 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 167 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b38 = cgif asan_globals+0x58 (descriptor 1 
  YF0m.v:208 row 168 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 168 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b40 = cgif asan_globals+0x60 (descriptor 1 
  YF0m.v:209 row 169 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 169 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b48 = cgif asan_globals+0x68 (descriptor 1 
  YF0m.v:210 row 170 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 170 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b50 = cgif asan_globals+0x70 (descriptor 1 
  YF0m.v:211 row 171 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 171 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b58 = cgif asan_globals+0x78 (descriptor 1 
  YF0m.v:212 row 172 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 172 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b60 = cgif asan_globals+0x80 (descriptor 2 
  YF0m.v:213 row 173 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 173 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b68 = cgif asan_globals+0x88 (descriptor 2 
  YF0m.v:214 row 174 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 174 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b70 = cgif asan_globals+0x90 (descriptor 2 
  YF0m.v:215 row 175 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 175 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b78 = cgif asan_globals+0x98 (descriptor 2 
  YF0m.v:216 row 176 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 176 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b80 = cgif asan_globals+0xa0 (descriptor 2 
  YF0m.v:217 row 177 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 177 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b88 = cgif asan_globals+0xa8 (descriptor 2 
  YF0m.v:218 row 178 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 178 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b90 = cgif asan_globals+0xb0 (descriptor 2 
  YF0m.v:219 row 179 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 179 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b98 = cgif asan_globals+0xb8 (descriptor 2 
  YF0m.v:242 row 202 `z8 (ANum 0x98ec8) 0x8c4a4` FILL 202 = duplicate of row 201 (line 241 `z8 (ANum 0x98ec8) 0x8c4a4  ;`): identical and not a fill itself: True; row 201 by name: cell _ZN14__interception11real_fflushE+0x0, value fflush+0x0; donor row with the same cell + value names: cgif line 230 `z8 (ANum 0x9ffd0) 0x93380  ;`; donor slot 0x9ffd8 = cgif _ZN14__interception11real_fcloseE+0x0; thi
  YF0m.v:243 row 203 `z8 (ANum 0x98ec8) 0x8c4a4` FILL 203 = duplicate of row 201 (line 241 `z8 (ANum 0x98ec8) 0x8c4a4  ;`): identical and not a fill itself: True; row 201 by name: cell _ZN14__interception11real_fflushE+0x0, value fflush+0x0; donor row with the same cell + value names: cgif line 230 `z8 (ANum 0x9ffd0) 0x93380  ;`; donor slot 0x9ffc8 = cgif _ZN14__interception10real_fopenE+0x0; this
  YF0m.v:245 row 205 `z8 (ANum 0x98e38) 0x90954` FILL 205 = duplicate of row 204 (line 244 `z8 (ANum 0x98e38) 0x90954  ;`): identical and not a fill itself: True; row 204 by name: cell _ZN14__interception11real_strchrE+0x0, value strchr+0x0; donor row with the same cell + value names: cgif line 233 `z8 (ANum 0x9ff30) 0x97a04  ;`; donor slot 0x20e23 (from the af0m comment) = byte 3 of cgif global [
  YF0m.v:246 row 206 `z8 (ANum 0x98e38) 0x90954` FILL 206 = duplicate of row 204 (line 244 `z8 (ANum 0x98e38) 0x90954  ;`): identical and not a fill itself: True; row 204 by name: cell _ZN14__interception11real_strchrE+0x0, value strchr+0x0; donor row with the same cell + value names: cgif line 233 `z8 (ANum 0x9ff30) 0x97a04  ;`; donor slot 0x20e24 (from the af0m comment) = byte 4 of cgif global [
  YF0m.v:247 row 207 `z8 (ANum 0x98e38) 0x90954` FILL 207 = duplicate of row 204 (line 244 `z8 (ANum 0x98e38) 0x90954  ;`): identical and not a fill itself: True; row 204 by name: cell _ZN14__interception11real_strchrE+0x0, value strchr+0x0; donor row with the same cell + value names: cgif line 233 `z8 (ANum 0x9ff30) 0x97a04  ;`; donor slot 0x20e25 (from the af0m comment) = byte 5 of cgif global [
  YF0m.v:248 row 208 `z8 (ANum 0x98e38) 0x90954` FILL 208 = duplicate of row 204 (line 244 `z8 (ANum 0x98e38) 0x90954  ;`): identical and not a fill itself: True; row 204 by name: cell _ZN14__interception11real_strchrE+0x0, value strchr+0x0; donor row with the same cell + value names: cgif line 233 `z8 (ANum 0x9ff30) 0x97a04  ;`; donor slot 0x20e26 (from the af0m comment) = byte 6 of cgif global [
pac_fill: 0 of 24 ported lines UNEXPLAINED (45 GENERATOR-FILL rows)
TRIAGE independent .symtab check of every symbol-named definition (symname_check.py; CONTROL first: 1 right + 2 planted wrong):
TRIAGE symname CONTROL rc=1 (1 = the two planted rows caught)
TRIAGE symname uci B rc=0
```

## FINAL: the relocation gate re-run on port_addr_check efa19b81e92b, control first (G3g)

```
RESULT G3g port_addr_check efa1 CONTROL cgif A->B (4 = findings, as e165) rc=4
GENERATOR-FILL	506	REPORTED
FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
FLAGGED 758 rows in 6 classes: DIFFERENT-SYMBOL=12 GEOMETRY-CHANGED=1 KIND-CHANGED=17 NON-ADDRESS-CHANGED=195 UNPAIRED-PORTED=69 UNRESOLVED=464
RESULT G3g port_addr_check efa1 cgif B -> uci B (4 = findings) rc=4
GENERATOR-FILL	45	kernel 37	REPORTED
FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
FLAGGED 3348 rows in 7 classes: DIFFERENT-SYMBOL=147 KIND-CHANGED=19 NO-COUNTERPART=3 NON-ADDRESS-CHANGED=1180 UNPAIRED-PORTED=58 UNPAIRED-SOURCE=1887 UNRESOLVED=54
RESULT G3g triage rc=0
TRIAGE port_addr_check e165063a0081 -> efa19b81e92b on the final 19 files (pac_moved.py: rows keyed by file, line, sentence, index, values)
MOVED rows (same key, another verdict): 0
GONE rows (old run only): 0
NEW rows (new run only): 0
GENERATOR-FILL rows of the new run: 45, basis: {'positional, donor object absent from the target': 36, 'generator mark': 1, 'in-place copy, no donor row': 8}
TRIAGE CONTROL cgif A -> B, e165 -> efa1 (the same join on the control):
MOVED rows (same key, another verdict): 0
GONE rows (old run only): 0
NEW rows (new run only): 0
GENERATOR-FILL rows of the new run: 506, basis: {'positional, donor object absent from the target': 506}
TRIAGE GENERATOR-FILL rows of efa1, each with a measured reason (pac_fill.py; CONTROL first on cgif A->B):
TRIAGE pac_fill CONTROL cgif A->B rc=1 (1 = it refuses the 236 YCej lines outside its YF0m rules: fails closed)
pac_fill: 236 of 236 ported lines UNEXPLAINED (506 GENERATOR-FILL rows)
TRIAGE pac_fill uci B rc=0
GENERATOR-FILL rows: 45, on 24 ported lines: {'YF0m.v': 24}
  YF0m.v:126 row 86 `z8 (ANum 0x97e10) 0xfffffffffffff800  ;` not an af0m FILL: unit image word at 0x97e10 (.got) = 0xfffffffffffff800; donor slot 0x9ef08 holds 0xfffffffffffff800 in cgif's image (.got), the same link-time word, a tp offset (negative), not an address; other unit rows with this cell or value: lines [] -> ACCEPTED
pac_fill: 0 of 24 ported lines UNEXPLAINED (45 GENERATOR-FILL rows)
TRIAGE independent .symtab check of every symbol-named definition (symname_check.py; CONTROL first: 1 right + 2 planted wrong):
TRIAGE symname CONTROL rc=1 (1 = the two planted rows caught)
TRIAGE symname uci B rc=0
```

## FINAL: port_addr_check e165063a0081 vs efa19b81e92b, moved / new / gone rows, GENERATOR-FILL triage, .symtab check

```
TRIAGE port_addr_check e165063a0081 -> efa19b81e92b on the final 19 files (pac_moved.py: rows keyed by file, line, sentence, index, values)
MOVED rows (same key, another verdict): 0
GONE rows (old run only): 0
NEW rows (new run only): 0
GENERATOR-FILL rows of the new run: 45, basis: {'positional, donor object absent from the target': 36, 'generator mark': 1, 'in-place copy, no donor row': 8}
TRIAGE CONTROL cgif A -> B, e165 -> efa1 (the same join on the control):
MOVED rows (same key, another verdict): 0
GONE rows (old run only): 0
NEW rows (new run only): 0
GENERATOR-FILL rows of the new run: 506, basis: {'positional, donor object absent from the target': 506}
TRIAGE GENERATOR-FILL rows of efa1, each with a measured reason (pac_fill.py; CONTROL first on cgif A->B):
TRIAGE pac_fill CONTROL cgif A->B rc=1 (1 = it refuses the 236 YCej lines outside its YF0m rules: fails closed)
pac_fill: 236 of 236 ported lines UNEXPLAINED (506 GENERATOR-FILL rows)
TRIAGE pac_fill uci B rc=0
GENERATOR-FILL rows: 45, on 24 ported lines: {'YF0m.v': 24}
  YF0m.v:108 row 68 `z8 (ANum 0x98e40) 0x90428` FILL 68 = duplicate of row 67 (line 107 `z8 (ANum 0x98e40) 0x90428  ;`): identical and not a fill itself: True; row 67 by name: cell _ZN14__interception11real_memcmpE+0x0, value memcmp+0x0; donor row with the same cell + value names: cgif line 96 `z8 (ANum 0x9ff38) 0x974d8  ;`; donor slot 0x9ff40 = cgif _ZN14__interception9real_bcmpE+0x0; this image 
  YF0m.v:126 row 86 `z8 (ANum 0x97e10) 0xfffffffffffff800  ;` not an af0m FILL: unit image word at 0x97e10 (.got) = 0xfffffffffffff800; donor slot 0x9ef08 holds 0xfffffffffffff800 in cgif's image (.got), the same link-time word, a tp offset (negative), not an address; other unit rows with this cell or value: lines [] -> ACCEPTED
  YF0m.v:204 row 164 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 164 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b20 = cgif asan_globals+0x40 (descriptor 1 
  YF0m.v:205 row 165 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 165 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b28 = cgif asan_globals+0x48 (descriptor 1 
  YF0m.v:206 row 166 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 166 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b30 = cgif asan_globals+0x50 (descriptor 1 
  YF0m.v:207 row 167 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 167 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b38 = cgif asan_globals+0x58 (descriptor 1 
  YF0m.v:208 row 168 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 168 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b40 = cgif asan_globals+0x60 (descriptor 1 
  YF0m.v:209 row 169 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 169 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b48 = cgif asan_globals+0x68 (descriptor 1 
  YF0m.v:210 row 170 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 170 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b50 = cgif asan_globals+0x70 (descriptor 1 
  YF0m.v:211 row 171 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 171 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b58 = cgif asan_globals+0x78 (descriptor 1 
  YF0m.v:212 row 172 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 172 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b60 = cgif asan_globals+0x80 (descriptor 2 
  YF0m.v:213 row 173 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 173 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b68 = cgif asan_globals+0x88 (descriptor 2 
  YF0m.v:214 row 174 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 174 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b70 = cgif asan_globals+0x90 (descriptor 2 
  YF0m.v:215 row 175 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 175 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b78 = cgif asan_globals+0x98 (descriptor 2 
  YF0m.v:216 row 176 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 176 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b80 = cgif asan_globals+0xa0 (descriptor 2 
  YF0m.v:217 row 177 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 177 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b88 = cgif asan_globals+0xa8 (descriptor 2 
  YF0m.v:218 row 178 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 178 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b90 = cgif asan_globals+0xb0 (descriptor 2 
  YF0m.v:219 row 179 `z8 (ANum 0x9ba08) 0xffffffffffffffff` FILL 179 = duplicate of row 163 (line 203 `z8 (ANum 0x9ba08) 0xffffffffffffffff  ;`): identical and not a fill itself: True; row 163 by name: cell asan_globals+0x38, value a datum; donor row with the same cell + value names: cgif line 192 `z8 (ANum 0xa2b18) 0xffffffffffffffff  ;`; donor slot 0xa2b98 = cgif asan_globals+0xb8 (descriptor 2 
  YF0m.v:242 row 202 `z8 (ANum 0x98ec8) 0x8c4a4` FILL 202 = duplicate of row 201 (line 241 `z8 (ANum 0x98ec8) 0x8c4a4  ;`): identical and not a fill itself: True; row 201 by name: cell _ZN14__interception11real_fflushE+0x0, value fflush+0x0; donor row with the same cell + value names: cgif line 230 `z8 (ANum 0x9ffd0) 0x93380  ;`; donor slot 0x9ffd8 = cgif _ZN14__interception11real_fcloseE+0x0; thi
  YF0m.v:243 row 203 `z8 (ANum 0x98ec8) 0x8c4a4` FILL 203 = duplicate of row 201 (line 241 `z8 (ANum 0x98ec8) 0x8c4a4  ;`): identical and not a fill itself: True; row 201 by name: cell _ZN14__interception11real_fflushE+0x0, value fflush+0x0; donor row with the same cell + value names: cgif line 230 `z8 (ANum 0x9ffd0) 0x93380  ;`; donor slot 0x9ffc8 = cgif _ZN14__interception10real_fopenE+0x0; this
  YF0m.v:245 row 205 `z8 (ANum 0x98e38) 0x90954` FILL 205 = duplicate of row 204 (line 244 `z8 (ANum 0x98e38) 0x90954  ;`): identical and not a fill itself: True; row 204 by name: cell _ZN14__interception11real_strchrE+0x0, value strchr+0x0; donor row with the same cell + value names: cgif line 233 `z8 (ANum 0x9ff30) 0x97a04  ;`; donor slot 0x20e23 (from the af0m comment) = byte 3 of cgif global [
  YF0m.v:246 row 206 `z8 (ANum 0x98e38) 0x90954` FILL 206 = duplicate of row 204 (line 244 `z8 (ANum 0x98e38) 0x90954  ;`): identical and not a fill itself: True; row 204 by name: cell _ZN14__interception11real_strchrE+0x0, value strchr+0x0; donor row with the same cell + value names: cgif line 233 `z8 (ANum 0x9ff30) 0x97a04  ;`; donor slot 0x20e24 (from the af0m comment) = byte 4 of cgif global [
  YF0m.v:247 row 207 `z8 (ANum 0x98e38) 0x90954` FILL 207 = duplicate of row 204 (line 244 `z8 (ANum 0x98e38) 0x90954  ;`): identical and not a fill itself: True; row 204 by name: cell _ZN14__interception11real_strchrE+0x0, value strchr+0x0; donor row with the same cell + value names: cgif line 233 `z8 (ANum 0x9ff30) 0x97a04  ;`; donor slot 0x20e25 (from the af0m comment) = byte 5 of cgif global [
  YF0m.v:248 row 208 `z8 (ANum 0x98e38) 0x90954` FILL 208 = duplicate of row 204 (line 244 `z8 (ANum 0x98e38) 0x90954  ;`): identical and not a fill itself: True; row 204 by name: cell _ZN14__interception11real_strchrE+0x0, value strchr+0x0; donor row with the same cell + value names: cgif line 233 `z8 (ANum 0x9ff30) 0x97a04  ;`; donor slot 0x20e26 (from the af0m comment) = byte 6 of cgif global [
pac_fill: 0 of 24 ported lines UNEXPLAINED (45 GENERATOR-FILL rows)
TRIAGE independent .symtab check of every symbol-named definition (symname_check.py; CONTROL first: 1 right + 2 planted wrong):
TRIAGE symname CONTROL rc=1 (1 = the two planted rows caught)
TRIAGE symname uci B rc=0
```

## FINAL: global_settings v10 439f8e3bd463 over the 19 files

```
TOOL $LT/gs10v/tools/global_settings/439f8e3bd463/global_settings.py sha256=439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/AB14-41193e1fb22.v sha256=9fb76682e17c315e7b9f01fef3a7d6237fb57537d0c21722ba36024b6b688ac1 blob=0253327ea5dcd66d6ba46c503d53ecc6fb73a879 (6223 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/F20F-d91a1b23270.v sha256=9bcdcabace9bcabf37944fa3079a5e36e15bdb8dd001e0d53b2758bd2a282cb0 blob=c7c3dec9d577d5b3728a9585e1763834733a8abe (13916 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/LiaTwx2-41193e1fb22.v sha256=2b4ecada9deed64da11c4ce29731dfabd3fef9938453f3487ec77cfc40f8d68c blob=391b43bc25a10bd8ed391a13b5d2a36cf8be454f (7639 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/AndN-41193e1fb22.v sha256=578ab3dd1a07993bb1cdea62258a7d8e41b55c135d6d246b50fc4fc93fa8ff43 blob=442450988b77b33098abea06be23f845c704be54 (89929 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/YA09-77b2702c17c.v sha256=41d98b977cd45b5b4e426bfd1c4c017ec59b4f568e6f745902926e44fcea7895 blob=187adbdd694af088b9f08ecb3482b3e5a518c438 (260546 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/scene-b069d3e1516/lib/Reusable/YA09.v sha256=a999bbac6d984363581203f55320ba6cebcea8ea1b534f1266148b84b08629a1 blob=500d346c88105f92e728f885cbe16001c654d249 (260586 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/scene-b069d3e1516/lib/Reusable/YA0e.v sha256=8b1ad2de9b1615ff403d852be5abe66a3ff8cf407de146b03420578c64bdb61b blob=339b9e6baa5a8622e52a03f940da2ac5662e554e (304559 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/boxreg-f7e88c4793c/lib/Reusable/YA09.v sha256=09a43a08e62c26754dc11b781c5279c953846204bfaa4e2a10cc2b4d894b5bf8 blob=1181f23ca61ba0712068a0df2eaa16a9c7847d8b (260558 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/boxreg-f7e88c4793c/lib/Reusable/YA0e.v sha256=574ac09f8c1a3cc38b5e7f1c912c2c9c0cfea6094d179be888905a5faef7bfca blob=9dc53efe8cd9e9c7ff13f5758f3b02388e81d5dd (304529 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/<build VM>/lib/Reusable/YA09.v sha256=11e36a764ec393936f9a5ffdcac5426a20567e0810bb5873695d0f2d56caa163 blob=e4eaa44dfa6088f50c20cd7c4cafc0c8a7a85e6f (260552 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/<build VM>/lib/Reusable/YA0e.v sha256=a807d6454c249c0fdee8465e7449cacefb05d959d5eeeeb83a607fc51147a46e blob=bef72ff5928383cfe7e1d5203ef52f830fb6469f (304525 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/grantB-9198a8522ec/lib/Reusable/YA09.v sha256=8feacbe9b1c4c12d021a706766c83e3f329cddc1b44d8a899ce5404a51794141 blob=f7abf1cf2e5e1ebd57bcd5d2b3a831838e40852f (260552 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/grantB-9198a8522ec/lib/Reusable/YA0e.v sha256=97c65150e276eac2582ef90c419d414584bdc688101aceb89bb581ff7eb03051 blob=0520553bff0041ae6a9d32fa14d9eda9e5eaa3d0 (304525 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/ctrl-77b2702c17c/lib/Reusable/YA09.v sha256=41d98b977cd45b5b4e426bfd1c4c017ec59b4f568e6f745902926e44fcea7895 blob=187adbdd694af088b9f08ecb3482b3e5a518c438 (260546 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/ctrl-77b2702c17c/lib/Reusable/YA0e.v sha256=1c4d1a321f4af2005bc4265bcf4e42069d75edd523d642728b07f7205272dfbd blob=d92a2a5fa9b6dddc6e52c75b905fde875bcaece0 (304521 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YM03.v sha256=f3c9133ecc2b6f69d05bc384a98f340c0b03d2c573c8cd4f4c9b54ef30019930 blob=3ca2843b708f5fa41bc2a111f9285db04367cc45 (8703 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YM05.v sha256=0ca34185e42a685a4a8746625e7d2427fc11a125fb77491c9adb6c4bdd284749 blob=95df478a2491c332ff7776d04195b70e95e557f4 (6737 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YK0c.v sha256=7d15f2b51d7098d1e7a75f3da4a55a1d8d577f4b408712a1001a2569b2a737b9 blob=717b295f756cdd8bc990776e6acf45e859e7be65 (105997 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YQ04.v sha256=b57f45c448c025bd3cd4dc4455fa7cdacdcbdd603e943461459bcaea007d6ca6 blob=e0c140305007687d72b43fda817c0d7255e3d67d (15505 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/pwglue-ea39002e512/lib/A/Prog/PaSym.v sha256=a6e7d5b754c5bf077f03a90efaae57779ac8052ba9ff0dc3cab0123a4425623b blob=701a71a74db49177a908f93811f891fb498b33dd (7177 bytes)
selftest: 45 synthetic setting cases and 11 synthetic hint cases (each text starts its case on line 4; v8: 16 bullet / brace must-FLAG cases, 2 of them on line 5), v9: 32 level cases, 66 kernel-level cases (8 forms x plain / Local / Global / Export / #[local] / #[global] / bullet / brace / after a `}` / in a proof, plus 4 must-not incl. v10's 2 coq-prog-args strings), 11 whole-run cases (9 kernel 
control: 20 real-file known answers (copies in $LT/gs10v/tools/global_settings/439f8e3bd463, sha256 pinned): AB14-41193e1fb22.v :12 PLAIN, :12 PLAIN, :14 ESCAPES, :139 ESCAPES [levels ESCAPES TACTIC x2, PLAIN TACTIC x2]; F20F-d91a1b23270.v :37 ESCAPES [levels ESCAPES TACTIC x1]; LiaTwx2-41193e1fb22.v contains :18 ESCAPES [levels ESCAPES OPTION x1, ESCAPES TACTIC x6]; AndN-41193e1fb22.v :4 PLAIN, :
INPUT wt $TR (a directory; 19 FILE arguments, each read relative to it)
INPUT file target $TLIB/B/YB01.v sha256=6fdf86aa459ae2e15ad7a3fb9fe685398b9033902b67fbc1289be770cff7b843 blob=a376229964c881d8c9be76c3e963fa1628d67f9c (393530 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB01.v: 2 reported
   :16 PLAIN TACTIC: Unset Lia Cache.
   :16 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YB03.v sha256=218296010faab87b30bcbadef48f238d705038ba915e38abf9d956b502b8ef19 blob=d3a60e48c878a14a20aefb1b21370d41fdbaa18d (59569 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB03.v: 2 reported
   :14 PLAIN TACTIC: Unset Lia Cache.
   :14 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YB05.v sha256=84a6a44d01aeea2e72485426418c05dff3e9af8182f874639a1126d8d0d8ae0f blob=c5784754dddb59d97d7e3ae7264fbaa98e2f42dd (37901 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB05.v: 2 reported
   :13 PLAIN TACTIC: Unset Lia Cache.
   :13 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YB12.v sha256=4d589aabf62fdd842cb09b5e2b9e1ac0dd136c4032053e3109cb72ab0cec7735 blob=607675cb39d086731340a4e92f1b421fde21d16d (1956 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB12.v: 2 reported
   :9 PLAIN TACTIC: Unset Lia Cache.
   :9 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YB13.v sha256=3124b194843c80bf3a69b0abe8d1518b1e5a30a173ed14599b0c5c92291f4028 blob=f021560c0208773039e1729b0269eb43421c94c2 (10594 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB13.v: 2 reported
   :13 PLAIN TACTIC: Unset Lia Cache.
   :13 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YB1h.v sha256=85ee13fd8e616c548d6cf64990a3ffb0d886bc29fa8c98c0a09b2ddc1521f3b1 blob=b6defb5714426811965ee009f69324b82aefe5aa (10150 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB1h.v: 2 reported
   :14 PLAIN TACTIC: Unset Lia Cache.
   :14 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YB1k.v sha256=7e92ef41344c6bf30c47a85261ea8e40d5eb37006b3661bf1f017d5c1da2ca90 blob=703433ebbcef2e16a6f1ab4d4edbdc8d7b8c8e73 (26757 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB1k.v: 2 reported
   :13 PLAIN TACTIC: Unset Lia Cache.
   :13 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YB1l.v sha256=82ef2229003ff9571d3d9ccb913e66aa8f37d7fc0a8687f60df9699e3de357b5 blob=7923c029230a31652df65ad56c0abbe8af572ccb (5642 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB1l.v: 2 reported
   :18 PLAIN TACTIC: Unset Lia Cache.
   :18 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YB1m.v sha256=307d18a9509b8b75bf727fc5580a2181a40460844843ec30589e6260e34a1cbe blob=2881c54d32ea4268ec2e9e73008013c9f7eb84ca (4777 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB1m.v: 2 reported
   :19 PLAIN TACTIC: Unset Lia Cache.
   :19 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YB1v.v sha256=8db628a795edfd13203cdf2b5e7ecea916b8ce5dc939e4bb74d2adde932b29db blob=4ab9e2aeef1560868a44cf643f1dbff796e43d3d (2143 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB1v.v: 2 reported
   :11 PLAIN TACTIC: Unset Lia Cache.
   :11 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YCej.v sha256=fabe9de00769cbb2cfe5f743b351af74514f7e7cb4e385020ef9b2cbc9dd1b30 blob=01fb42e6ad789c9ffaf2f24b40b5a242a2f86533 (7610 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YCej.v: 0 reported
INPUT file target $TLIB/B/YD1k.v sha256=cf8c8fa5ad81178489da754d3ae2fe2b9731ac51e62abe525d71c399eb1ced46 blob=7770f6b693595ba528b6c08afd2e6c9636a60b01 (25223 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YD1k.v: 2 reported
   :15 PLAIN TACTIC: Unset Lia Cache.
   :15 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YD1y.v sha256=68dec40355aa335fda51e63550a002048bca60598d562f870d5e80c978cc383d blob=99aeb9ae8ba945427544280c04782f957ab85497 (25588 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YD1y.v: 2 reported
   :18 PLAIN TACTIC: Unset Lia Cache.
   :18 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YD2i.v sha256=694a828f54b3dc771c34760e967b0a2dca3922c56722a849c06ee13959be8325 blob=eca25c65ad1e8cc2d89ece81ac5477294d883cc6 (55380 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YD2i.v: 2 reported
   :16 PLAIN TACTIC: Unset Lia Cache.
   :16 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YD2j.v sha256=4344efb5441fa35205febf035c0b083d945c072d946c0a4b602528aacacb92b5 blob=3ad56f5db987915e38d8071f941c70c503674d99 (5827 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YD2j.v: 0 reported
INPUT file target $TLIB/B/YE23.v sha256=d52b59347a3e4fc874395e9ab8d4574207ae0e42ac32e28bddb839629f0a6658 blob=c8577cd00a6a6633559ad1c05fd0996c62efe259 (144046 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YE23.v: 2 reported
   :25 PLAIN TACTIC: Unset Lia Cache.
   :25 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YE37.v sha256=80a9d76be9285a41c883c915b29b0b0a13e883ec69f4f44e772f693788158d54 blob=3769bae26b0b4c5d2410d8a97cab0d01d4f9fd06 (17969 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YE37.v: 2 reported
   :24 PLAIN TACTIC: Unset Lia Cache.
   :24 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YE3i.v sha256=2a84cd9cbc8a9e42d42b16160cb05ccbc20dc800dd9a92903e7fa28c89c84fba blob=f912f6905152b633e74f54c1ddd58671b7db2dd8 (6021 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YE3i.v: 2 reported
   :18 PLAIN TACTIC: Unset Lia Cache.
   :18 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $TLIB/B/YF0m.v sha256=64bd6a0235ee0b8bd275a1a6039f8231434a170647d8de6d248d36f0696dd430 blob=5f0bfc88368210cf789df234464f687e935c708a (17337 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YF0m.v: 2 reported
   :12 PLAIN TACTIC: Unset Lia Cache.
   :12 PLAIN TACTIC: Unset Nia Cache.
SUMMARY: 19 files read of 19 given; ESCAPES 0; PLAIN 34; UNMEASURED 0; KERNEL 0; levels TACTIC 34, OPTION 0; HINTS 0 (report only, tactic-level)
```

## FINAL: global_settings v10 over the core's lib/Reusable YA0e.v + YA09.v (09ea58a92a88)

```
TOOL $LT/gs10v/tools/global_settings/439f8e3bd463/global_settings.py sha256=439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/AB14-41193e1fb22.v sha256=9fb76682e17c315e7b9f01fef3a7d6237fb57537d0c21722ba36024b6b688ac1 blob=0253327ea5dcd66d6ba46c503d53ecc6fb73a879 (6223 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/F20F-d91a1b23270.v sha256=9bcdcabace9bcabf37944fa3079a5e36e15bdb8dd001e0d53b2758bd2a282cb0 blob=c7c3dec9d577d5b3728a9585e1763834733a8abe (13916 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/LiaTwx2-41193e1fb22.v sha256=2b4ecada9deed64da11c4ce29731dfabd3fef9938453f3487ec77cfc40f8d68c blob=391b43bc25a10bd8ed391a13b5d2a36cf8be454f (7639 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/AndN-41193e1fb22.v sha256=578ab3dd1a07993bb1cdea62258a7d8e41b55c135d6d246b50fc4fc93fa8ff43 blob=442450988b77b33098abea06be23f845c704be54 (89929 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/YA09-77b2702c17c.v sha256=41d98b977cd45b5b4e426bfd1c4c017ec59b4f568e6f745902926e44fcea7895 blob=187adbdd694af088b9f08ecb3482b3e5a518c438 (260546 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/scene-b069d3e1516/lib/Reusable/YA09.v sha256=a999bbac6d984363581203f55320ba6cebcea8ea1b534f1266148b84b08629a1 blob=500d346c88105f92e728f885cbe16001c654d249 (260586 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/scene-b069d3e1516/lib/Reusable/YA0e.v sha256=8b1ad2de9b1615ff403d852be5abe66a3ff8cf407de146b03420578c64bdb61b blob=339b9e6baa5a8622e52a03f940da2ac5662e554e (304559 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/boxreg-f7e88c4793c/lib/Reusable/YA09.v sha256=09a43a08e62c26754dc11b781c5279c953846204bfaa4e2a10cc2b4d894b5bf8 blob=1181f23ca61ba0712068a0df2eaa16a9c7847d8b (260558 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/boxreg-f7e88c4793c/lib/Reusable/YA0e.v sha256=574ac09f8c1a3cc38b5e7f1c912c2c9c0cfea6094d179be888905a5faef7bfca blob=9dc53efe8cd9e9c7ff13f5758f3b02388e81d5dd (304529 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/<build VM>/lib/Reusable/YA09.v sha256=11e36a764ec393936f9a5ffdcac5426a20567e0810bb5873695d0f2d56caa163 blob=e4eaa44dfa6088f50c20cd7c4cafc0c8a7a85e6f (260552 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/<build VM>/lib/Reusable/YA0e.v sha256=a807d6454c249c0fdee8465e7449cacefb05d959d5eeeeb83a607fc51147a46e blob=bef72ff5928383cfe7e1d5203ef52f830fb6469f (304525 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/grantB-9198a8522ec/lib/Reusable/YA09.v sha256=8feacbe9b1c4c12d021a706766c83e3f329cddc1b44d8a899ce5404a51794141 blob=f7abf1cf2e5e1ebd57bcd5d2b3a831838e40852f (260552 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/grantB-9198a8522ec/lib/Reusable/YA0e.v sha256=97c65150e276eac2582ef90c419d414584bdc688101aceb89bb581ff7eb03051 blob=0520553bff0041ae6a9d32fa14d9eda9e5eaa3d0 (304525 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/ctrl-77b2702c17c/lib/Reusable/YA09.v sha256=41d98b977cd45b5b4e426bfd1c4c017ec59b4f568e6f745902926e44fcea7895 blob=187adbdd694af088b9f08ecb3482b3e5a518c438 (260546 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/ctrl-77b2702c17c/lib/Reusable/YA0e.v sha256=1c4d1a321f4af2005bc4265bcf4e42069d75edd523d642728b07f7205272dfbd blob=d92a2a5fa9b6dddc6e52c75b905fde875bcaece0 (304521 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YM03.v sha256=f3c9133ecc2b6f69d05bc384a98f340c0b03d2c573c8cd4f4c9b54ef30019930 blob=3ca2843b708f5fa41bc2a111f9285db04367cc45 (8703 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YM05.v sha256=0ca34185e42a685a4a8746625e7d2427fc11a125fb77491c9adb6c4bdd284749 blob=95df478a2491c332ff7776d04195b70e95e557f4 (6737 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YK0c.v sha256=7d15f2b51d7098d1e7a75f3da4a55a1d8d577f4b408712a1001a2569b2a737b9 blob=717b295f756cdd8bc990776e6acf45e859e7be65 (105997 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YQ04.v sha256=b57f45c448c025bd3cd4dc4455fa7cdacdcbdd603e943461459bcaea007d6ca6 blob=e0c140305007687d72b43fda817c0d7255e3d67d (15505 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/pwglue-ea39002e512/lib/A/Prog/PaSym.v sha256=a6e7d5b754c5bf077f03a90efaae57779ac8052ba9ff0dc3cab0123a4425623b blob=701a71a74db49177a908f93811f891fb498b33dd (7177 bytes)
selftest: 45 synthetic setting cases and 11 synthetic hint cases (each text starts its case on line 4; v8: 16 bullet / brace must-FLAG cases, 2 of them on line 5), v9: 32 level cases, 66 kernel-level cases (8 forms x plain / Local / Global / Export / #[local] / #[global] / bullet / brace / after a `}` / in a proof, plus 4 must-not incl. v10's 2 coq-prog-args strings), 11 whole-run cases (9 kernel 
control: 20 real-file known answers (copies in $LT/gs10v/tools/global_settings/439f8e3bd463, sha256 pinned): AB14-41193e1fb22.v :12 PLAIN, :12 PLAIN, :14 ESCAPES, :139 ESCAPES [levels ESCAPES TACTIC x2, PLAIN TACTIC x2]; F20F-d91a1b23270.v :37 ESCAPES [levels ESCAPES TACTIC x1]; LiaTwx2-41193e1fb22.v contains :18 ESCAPES [levels ESCAPES OPTION x1, ESCAPES TACTIC x6]; AndN-41193e1fb22.v :4 PLAIN, :
INPUT wt $LT/bcore09ea (a directory; 2 FILE arguments, each read relative to it)
INPUT file target $UCIB_BCORE_LIB/Reusable/YA0e.v sha256=6301785c80f0b271ed6fe718a105fbfa8210df9c3912c72ed9b781c89af608f1 blob=4d7fcb99e799a6c8c1af2a3dae3c48d75fa702b0 (305098 bytes)
read proofs/reac-repacer/fuzz_uci/lib/Reusable/YA0e.v: 2 reported
   :16 PLAIN TACTIC: Unset Lia Cache.
   :16 PLAIN TACTIC: Unset Nia Cache.
INPUT file target $UCIB_BCORE_LIB/Reusable/YA09.v sha256=9a0ec5185751b9d765296e38fb2697170a734e6ba752bdb56c029ba8cf5a10cc blob=b4e142c26129a6bd5fa265946e1ceefa820d185c (261017 bytes)
read proofs/reac-repacer/fuzz_uci/lib/Reusable/YA09.v: 2 reported
   :21 PLAIN TACTIC: Unset Lia Cache.
   :21 PLAIN TACTIC: Unset Nia Cache.
SUMMARY: 2 files read of 2 given; ESCAPES 0; PLAIN 4; UNMEASURED 0; KERNEL 0; levels TACTIC 4, OPTION 0; HINTS 0 (report only, tactic-level)
```

## FINAL: global_settings v10 control, grant's released lib/Reusable YA0e.v + YA09.v (4f87de75d67)

```
TOOL $LT/gs10v/tools/global_settings/439f8e3bd463/global_settings.py sha256=439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/AB14-41193e1fb22.v sha256=9fb76682e17c315e7b9f01fef3a7d6237fb57537d0c21722ba36024b6b688ac1 blob=0253327ea5dcd66d6ba46c503d53ecc6fb73a879 (6223 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/F20F-d91a1b23270.v sha256=9bcdcabace9bcabf37944fa3079a5e36e15bdb8dd001e0d53b2758bd2a282cb0 blob=c7c3dec9d577d5b3728a9585e1763834733a8abe (13916 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/LiaTwx2-41193e1fb22.v sha256=2b4ecada9deed64da11c4ce29731dfabd3fef9938453f3487ec77cfc40f8d68c blob=391b43bc25a10bd8ed391a13b5d2a36cf8be454f (7639 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/AndN-41193e1fb22.v sha256=578ab3dd1a07993bb1cdea62258a7d8e41b55c135d6d246b50fc4fc93fa8ff43 blob=442450988b77b33098abea06be23f845c704be54 (89929 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/YA09-77b2702c17c.v sha256=41d98b977cd45b5b4e426bfd1c4c017ec59b4f568e6f745902926e44fcea7895 blob=187adbdd694af088b9f08ecb3482b3e5a518c438 (260546 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/scene-b069d3e1516/lib/Reusable/YA09.v sha256=a999bbac6d984363581203f55320ba6cebcea8ea1b534f1266148b84b08629a1 blob=500d346c88105f92e728f885cbe16001c654d249 (260586 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/scene-b069d3e1516/lib/Reusable/YA0e.v sha256=8b1ad2de9b1615ff403d852be5abe66a3ff8cf407de146b03420578c64bdb61b blob=339b9e6baa5a8622e52a03f940da2ac5662e554e (304559 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/boxreg-f7e88c4793c/lib/Reusable/YA09.v sha256=09a43a08e62c26754dc11b781c5279c953846204bfaa4e2a10cc2b4d894b5bf8 blob=1181f23ca61ba0712068a0df2eaa16a9c7847d8b (260558 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/boxreg-f7e88c4793c/lib/Reusable/YA0e.v sha256=574ac09f8c1a3cc38b5e7f1c912c2c9c0cfea6094d179be888905a5faef7bfca blob=9dc53efe8cd9e9c7ff13f5758f3b02388e81d5dd (304529 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/<build VM>/lib/Reusable/YA09.v sha256=11e36a764ec393936f9a5ffdcac5426a20567e0810bb5873695d0f2d56caa163 blob=e4eaa44dfa6088f50c20cd7c4cafc0c8a7a85e6f (260552 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/<build VM>/lib/Reusable/YA0e.v sha256=a807d6454c249c0fdee8465e7449cacefb05d959d5eeeeb83a607fc51147a46e blob=bef72ff5928383cfe7e1d5203ef52f830fb6469f (304525 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/grantB-9198a8522ec/lib/Reusable/YA09.v sha256=8feacbe9b1c4c12d021a706766c83e3f329cddc1b44d8a899ce5404a51794141 blob=f7abf1cf2e5e1ebd57bcd5d2b3a831838e40852f (260552 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/grantB-9198a8522ec/lib/Reusable/YA0e.v sha256=97c65150e276eac2582ef90c419d414584bdc688101aceb89bb581ff7eb03051 blob=0520553bff0041ae6a9d32fa14d9eda9e5eaa3d0 (304525 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/ctrl-77b2702c17c/lib/Reusable/YA09.v sha256=41d98b977cd45b5b4e426bfd1c4c017ec59b4f568e6f745902926e44fcea7895 blob=187adbdd694af088b9f08ecb3482b3e5a518c438 (260546 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/ctrl-77b2702c17c/lib/Reusable/YA0e.v sha256=1c4d1a321f4af2005bc4265bcf4e42069d75edd523d642728b07f7205272dfbd blob=d92a2a5fa9b6dddc6e52c75b905fde875bcaece0 (304521 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YM03.v sha256=f3c9133ecc2b6f69d05bc384a98f340c0b03d2c573c8cd4f4c9b54ef30019930 blob=3ca2843b708f5fa41bc2a111f9285db04367cc45 (8703 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YM05.v sha256=0ca34185e42a685a4a8746625e7d2427fc11a125fb77491c9adb6c4bdd284749 blob=95df478a2491c332ff7776d04195b70e95e557f4 (6737 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YK0c.v sha256=7d15f2b51d7098d1e7a75f3da4a55a1d8d577f4b408712a1001a2569b2a737b9 blob=717b295f756cdd8bc990776e6acf45e859e7be65 (105997 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/knock-0a89620d3fa/lib/Reusable/YQ04.v sha256=b57f45c448c025bd3cd4dc4455fa7cdacdcbdd603e943461459bcaea007d6ca6 blob=e0c140305007687d72b43fda817c0d7255e3d67d (15505 bytes)
INPUT file control $LT/gs10v/tools/global_settings/439f8e3bd463/ctl/pwglue-ea39002e512/lib/A/Prog/PaSym.v sha256=a6e7d5b754c5bf077f03a90efaae57779ac8052ba9ff0dc3cab0123a4425623b blob=701a71a74db49177a908f93811f891fb498b33dd (7177 bytes)
selftest: 45 synthetic setting cases and 11 synthetic hint cases (each text starts its case on line 4; v8: 16 bullet / brace must-FLAG cases, 2 of them on line 5), v9: 32 level cases, 66 kernel-level cases (8 forms x plain / Local / Global / Export / #[local] / #[global] / bullet / brace / after a `}` / in a proof, plus 4 must-not incl. v10's 2 coq-prog-args strings), 11 whole-run cases (9 kernel 
control: 20 real-file known answers (copies in $LT/gs10v/tools/global_settings/439f8e3bd463, sha256 pinned): AB14-41193e1fb22.v :12 PLAIN, :12 PLAIN, :14 ESCAPES, :139 ESCAPES [levels ESCAPES TACTIC x2, PLAIN TACTIC x2]; F20F-d91a1b23270.v :37 ESCAPES [levels ESCAPES TACTIC x1]; LiaTwx2-41193e1fb22.v contains :18 ESCAPES [levels ESCAPES OPTION x1, ESCAPES TACTIC x6]; AndN-41193e1fb22.v :4 PLAIN, :
INPUT wt $LT/gsgrant (a directory; 2 FILE arguments, each read relative to it)
INPUT file target $LT/gsgrant/proofs/libreac/fuzz_grant/lib/Reusable/YA0e.v sha256=97c65150e276eac2582ef90c419d414584bdc688101aceb89bb581ff7eb03051 blob=0520553bff0041ae6a9d32fa14d9eda9e5eaa3d0 (304525 bytes)
read proofs/libreac/fuzz_grant/lib/Reusable/YA0e.v: 74 reported
   :15 PLAIN TACTIC: Unset Lia Cache.
   :15 PLAIN TACTIC: Unset Nia Cache.
   :21 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :26 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :27 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :36 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :244 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :246 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :253 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :256 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :287 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :299 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :882 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :883 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1058 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1063 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1090 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1095 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1102 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1104 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1108 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1110 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1125 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1126 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1150 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1155 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1168 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1170 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1175 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1176 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1266 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1271 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1296 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1301 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1308 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1310 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1314 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1316 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1331 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1332 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1356 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1361 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1374 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1376 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1381 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1382 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1444 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1446 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1460 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1462 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1476 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1479 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1482 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1497 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1767 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1771 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1789 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1800 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2197 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2199 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2208 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2211 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2267 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2273 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2766 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2770 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :3393 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :3398 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :3471 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :3473 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :3518 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :3519 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :3743 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :3758 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
INPUT file target $LT/gsgrant/proofs/libreac/fuzz_grant/lib/Reusable/YA09.v sha256=8feacbe9b1c4c12d021a706766c83e3f329cddc1b44d8a899ce5404a51794141 blob=f7abf1cf2e5e1ebd57bcd5d2b3a831838e40852f (260552 bytes)
read proofs/libreac/fuzz_grant/lib/Reusable/YA09.v: 55 reported
   :20 PLAIN TACTIC: Unset Lia Cache.
   :20 PLAIN TACTIC: Unset Nia Cache.
   :24 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :268 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :271 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :278 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :279 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :286 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :287 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1368 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1370 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1459 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1461 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1463 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1465 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1645 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :1646 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2041 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2043 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2123 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2129 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2162 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2163 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2202 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2204 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2213 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2215 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2225 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2227 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2250 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2253 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2290 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2292 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2380 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2381 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2400 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2407 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2730 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2735 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2745 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2746 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2757 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2758 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2800 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2805 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2815 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2816 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2827 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2828 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2873 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2875 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2877 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :2879 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :3339 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
   :3341 ESCAPES TACTIC: Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
SUMMARY: 2 files read of 2 given; ESCAPES 125; PLAIN 4; UNMEASURED 0; KERNEL 0; levels TACTIC 129, OPTION 0; HINTS 0 (report only, tactic-level)
```

## FINAL: global_settings v8 7897f5fb9f8f over the 19 files

```
TOOL $LT/gs10/tools/global_settings/7897f5fb9f8f/global_settings.py sha256=7897f5fb9f8fc36cb3feff5fd86ce12551c99ec48d799898742decd5376bea4f
INPUT file control $LT/gs10/tools/global_settings/7897f5fb9f8f/AB14-41193e1fb22.v sha256=9fb76682e17c315e7b9f01fef3a7d6237fb57537d0c21722ba36024b6b688ac1 blob=0253327ea5dcd66d6ba46c503d53ecc6fb73a879 (6223 bytes)
INPUT file control $LT/gs10/tools/global_settings/7897f5fb9f8f/F20F-d91a1b23270.v sha256=9bcdcabace9bcabf37944fa3079a5e36e15bdb8dd001e0d53b2758bd2a282cb0 blob=c7c3dec9d577d5b3728a9585e1763834733a8abe (13916 bytes)
INPUT file control $LT/gs10/tools/global_settings/7897f5fb9f8f/LiaTwx2-41193e1fb22.v sha256=2b4ecada9deed64da11c4ce29731dfabd3fef9938453f3487ec77cfc40f8d68c blob=391b43bc25a10bd8ed391a13b5d2a36cf8be454f (7639 bytes)
INPUT file control $LT/gs10/tools/global_settings/7897f5fb9f8f/AndN-41193e1fb22.v sha256=578ab3dd1a07993bb1cdea62258a7d8e41b55c135d6d246b50fc4fc93fa8ff43 blob=442450988b77b33098abea06be23f845c704be54 (89929 bytes)
INPUT file control $LT/gs10/tools/global_settings/7897f5fb9f8f/YA09-77b2702c17c.v sha256=41d98b977cd45b5b4e426bfd1c4c017ec59b4f568e6f745902926e44fcea7895 blob=187adbdd694af088b9f08ecb3482b3e5a518c438 (260546 bytes)
selftest: 45 synthetic setting cases and 11 synthetic hint cases (each text starts its case on line 4; v8: 16 bullet / brace must-FLAG cases, 2 of them on line 5), 6 partial-parse cases, 8 input cases (non-UTF-8, unreadable, partly parsed, absolute FILE, FILE leaving WT, FILE a directory, no FILE, no argument), 5 count cases (1 file, 3 files, a duplicate, a non-directory WT, an absent file); moved
control: 5 real-file known answers (copies in $LT/gs10/tools/global_settings/7897f5fb9f8f, sha256 pinned): AB14-41193e1fb22.v :12 PLAIN, :12 PLAIN, :14 ESCAPES, :139 ESCAPES; F20F-d91a1b23270.v :37 ESCAPES; LiaTwx2-41193e1fb22.v contains :18 ESCAPES; AndN-41193e1fb22.v :4 PLAIN, :4 PLAIN, :4 PLAIN, :5 PLAIN, :132 PLAIN; YA09-77b2702c17c.v :20 PLAIN, :20 PLAIN, :24 ESCAPES, :268 ESCAPES, :271 ESCAP
INPUT wt $TR (a directory; 19 FILE arguments, each read relative to it)
INPUT file target $TLIB/B/YB01.v sha256=6fdf86aa459ae2e15ad7a3fb9fe685398b9033902b67fbc1289be770cff7b843 blob=a376229964c881d8c9be76c3e963fa1628d67f9c (393530 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB01.v: 2 reported
   :16 PLAIN: Unset Lia Cache.
   :16 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YB03.v sha256=218296010faab87b30bcbadef48f238d705038ba915e38abf9d956b502b8ef19 blob=d3a60e48c878a14a20aefb1b21370d41fdbaa18d (59569 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB03.v: 2 reported
   :14 PLAIN: Unset Lia Cache.
   :14 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YB05.v sha256=84a6a44d01aeea2e72485426418c05dff3e9af8182f874639a1126d8d0d8ae0f blob=c5784754dddb59d97d7e3ae7264fbaa98e2f42dd (37901 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB05.v: 2 reported
   :13 PLAIN: Unset Lia Cache.
   :13 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YB12.v sha256=4d589aabf62fdd842cb09b5e2b9e1ac0dd136c4032053e3109cb72ab0cec7735 blob=607675cb39d086731340a4e92f1b421fde21d16d (1956 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB12.v: 2 reported
   :9 PLAIN: Unset Lia Cache.
   :9 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YB13.v sha256=3124b194843c80bf3a69b0abe8d1518b1e5a30a173ed14599b0c5c92291f4028 blob=f021560c0208773039e1729b0269eb43421c94c2 (10594 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB13.v: 2 reported
   :13 PLAIN: Unset Lia Cache.
   :13 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YB1h.v sha256=85ee13fd8e616c548d6cf64990a3ffb0d886bc29fa8c98c0a09b2ddc1521f3b1 blob=b6defb5714426811965ee009f69324b82aefe5aa (10150 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB1h.v: 2 reported
   :14 PLAIN: Unset Lia Cache.
   :14 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YB1k.v sha256=7e92ef41344c6bf30c47a85261ea8e40d5eb37006b3661bf1f017d5c1da2ca90 blob=703433ebbcef2e16a6f1ab4d4edbdc8d7b8c8e73 (26757 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB1k.v: 2 reported
   :13 PLAIN: Unset Lia Cache.
   :13 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YB1l.v sha256=82ef2229003ff9571d3d9ccb913e66aa8f37d7fc0a8687f60df9699e3de357b5 blob=7923c029230a31652df65ad56c0abbe8af572ccb (5642 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB1l.v: 2 reported
   :18 PLAIN: Unset Lia Cache.
   :18 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YB1m.v sha256=307d18a9509b8b75bf727fc5580a2181a40460844843ec30589e6260e34a1cbe blob=2881c54d32ea4268ec2e9e73008013c9f7eb84ca (4777 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB1m.v: 2 reported
   :19 PLAIN: Unset Lia Cache.
   :19 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YB1v.v sha256=8db628a795edfd13203cdf2b5e7ecea916b8ce5dc939e4bb74d2adde932b29db blob=4ab9e2aeef1560868a44cf643f1dbff796e43d3d (2143 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YB1v.v: 2 reported
   :11 PLAIN: Unset Lia Cache.
   :11 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YCej.v sha256=fabe9de00769cbb2cfe5f743b351af74514f7e7cb4e385020ef9b2cbc9dd1b30 blob=01fb42e6ad789c9ffaf2f24b40b5a242a2f86533 (7610 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YCej.v: 0 reported
INPUT file target $TLIB/B/YD1k.v sha256=cf8c8fa5ad81178489da754d3ae2fe2b9731ac51e62abe525d71c399eb1ced46 blob=7770f6b693595ba528b6c08afd2e6c9636a60b01 (25223 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YD1k.v: 2 reported
   :15 PLAIN: Unset Lia Cache.
   :15 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YD1y.v sha256=68dec40355aa335fda51e63550a002048bca60598d562f870d5e80c978cc383d blob=99aeb9ae8ba945427544280c04782f957ab85497 (25588 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YD1y.v: 2 reported
   :18 PLAIN: Unset Lia Cache.
   :18 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YD2i.v sha256=694a828f54b3dc771c34760e967b0a2dca3922c56722a849c06ee13959be8325 blob=eca25c65ad1e8cc2d89ece81ac5477294d883cc6 (55380 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YD2i.v: 2 reported
   :16 PLAIN: Unset Lia Cache.
   :16 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YD2j.v sha256=4344efb5441fa35205febf035c0b083d945c072d946c0a4b602528aacacb92b5 blob=3ad56f5db987915e38d8071f941c70c503674d99 (5827 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YD2j.v: 0 reported
INPUT file target $TLIB/B/YE23.v sha256=d52b59347a3e4fc874395e9ab8d4574207ae0e42ac32e28bddb839629f0a6658 blob=c8577cd00a6a6633559ad1c05fd0996c62efe259 (144046 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YE23.v: 2 reported
   :25 PLAIN: Unset Lia Cache.
   :25 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YE37.v sha256=80a9d76be9285a41c883c915b29b0b0a13e883ec69f4f44e772f693788158d54 blob=3769bae26b0b4c5d2410d8a97cab0d01d4f9fd06 (17969 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YE37.v: 2 reported
   :24 PLAIN: Unset Lia Cache.
   :24 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YE3i.v sha256=2a84cd9cbc8a9e42d42b16160cb05ccbc20dc800dd9a92903e7fa28c89c84fba blob=f912f6905152b633e74f54c1ddd58671b7db2dd8 (6021 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YE3i.v: 2 reported
   :18 PLAIN: Unset Lia Cache.
   :18 PLAIN: Unset Nia Cache.
INPUT file target $TLIB/B/YF0m.v sha256=64bd6a0235ee0b8bd275a1a6039f8231434a170647d8de6d248d36f0696dd430 blob=5f0bfc88368210cf789df234464f687e935c708a (17337 bytes)
read proofs/reac-repacer/fuzz_uci/lib/B/YF0m.v: 2 reported
   :12 PLAIN: Unset Lia Cache.
   :12 PLAIN: Unset Nia Cache.
SUMMARY: 19 files read of 19 given; ESCAPES 0; PLAIN 34; UNMEASURED 0; HINTS 0 (report only)
```

## FINAL: Required modules present in the merged tree (09ea58a92a88 + the 19 files)

```
YB01.v: 5 unit modules Required, 0 missing in the trunk: -
YB03.v: 5 unit modules Required, 0 missing in the trunk: -
YB05.v: 6 unit modules Required, 0 missing in the trunk: -
YB12.v: 2 unit modules Required, 0 missing in the trunk: -
YB13.v: 6 unit modules Required, 0 missing in the trunk: -
YB1h.v: 16 unit modules Required, 0 missing in the trunk: -
YB1k.v: 16 unit modules Required, 0 missing in the trunk: -
YB1l.v: 25 unit modules Required, 0 missing in the trunk: -
YB1m.v: 28 unit modules Required, 0 missing in the trunk: -
YB1v.v: 2 unit modules Required, 0 missing in the trunk: -
YCej.v: 2 unit modules Required, 0 missing in the trunk: -
YD1k.v: 55 unit modules Required, 0 missing in the trunk: -
YD1y.v: 40 unit modules Required, 0 missing in the trunk: -
YD2i.v: 29 unit modules Required, 0 missing in the trunk: -
YD2j.v: 3 unit modules Required, 0 missing in the trunk: -
YE23.v: 61 unit modules Required, 0 missing in the trunk: -
YE37.v: 58 unit modules Required, 0 missing in the trunk: -
YE3i.v: 22 unit modules Required, 0 missing in the trunk: -
YF0m.v: 5 unit modules Required, 0 missing in the trunk: -
UNION 0 missing modules: 
```

## FINAL: the layer is built in the image-B core: core head, merge, build record, shared MANIFEST.md (core_check.py)

```
ls-remote <branch> = f47e2a8927b9d2cb9a2eb868cebcc195abe79bfd (want f47e2a8927b9...): True
layer 89a444c41f23 is an ancestor of core head f47e2a8927b9: True
merge commit(s) bringing 89a444c41f23 in: ["7614ed99fc1f 0b57b40b465e 89a444c41f23 proofs: reac-repacer fuzz_uci: merge the image-B start-up layer's YA0e / YA09 routing (89a444c41f23)"]
files the core head changes after merge 7614ed99fc1f outside provenance/: 0 []
core build record (core-B/GATES.md section 0 at f47e2a8927b9): - `cb build` of commit 7614ed99fc1: rc 0, 0 failed (75 compiled, 1978 from the cache); pins of all four images PINNED
provenance/evidence/MANIFEST.md at f47e2a8927b9 vs the generator copy at that head (startup-B/scripts/mk_top_manifest.py; mk_top_manifest: 5 slice(s), 100 files): BYTE-EQUAL
the same vs this lane's current mk_top_manifest.py (mk_top_manifest: 5 slice(s), 101 files): differs
  lines only the current generator writes: ['Files directly under provenance/evidence/ (in no slice): `mkmanifest.py`', '| `mkmanifest.py` | `2e6b0a7efca1d946c0b6a32f28779fc333cedcc961786a08390fd0dc4fac09be` |'] (loose top-level files: ['mkmanifest.py'])
core_check: PASS
```

## Earlier: full run on the 19 files before the Require-map changes (G0-G12)

```
RESULT G1 kimg acfd CONTROL cgif YB01/YB03 rc=0
25e3d17bdb50:proofs/cgif/cgif_file_fuzzer/lib/YB01.v  overlapping write bytes 0  contradicting bytes 0
    states: 50, aliases 0, duplicate states 0
25e3d17bdb50:proofs/cgif/cgif_file_fuzzer/lib/YB03.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
RESULT G1 kimg acfd CONTROL cgif counterparts rc=0
FILE:cgif/YB01.v  overlapping write bytes 0  contradicting bytes 0
    states: 50, aliases 0, duplicate states 0
FILE:cgif/YB03.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB05.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB12.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB13.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB1h.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB1k.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB1l.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB1m.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YB1v.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YCej.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YD1k.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YD1y.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YD2i.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YD2j.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YE23.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YE37.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YE3i.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:cgif/YF0m.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
RESULT G1 kimg acfd uciB rc=0
FILE:gen/YB01.v  overlapping write bytes 0  contradicting bytes 0
    states: 50, aliases 0, duplicate states 0
FILE:gen/YB03.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB05.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB12.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB13.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB1h.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB1k.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB1l.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB1m.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YB1v.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YCej.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YD1k.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YD1y.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YD2i.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YD2j.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YE23.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YE37.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YE3i.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
FILE:gen/YF0m.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
RESULT G1b kimg 5db3 CONTROL rc=0
25e3d17bdb50:proofs/cgif/cgif_file_fuzzer/lib/YB01.v  overlapping write bytes 0  contradicting bytes 0
    states: 50, aliases 0, duplicate states 0
    KImg ranges: 140, findings 0
25e3d17bdb50:proofs/cgif/cgif_file_fuzzer/lib/YB03.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
    KImg ranges: 67, findings 0
RESULT G1b kimg 5db3 uciB rc=0
FILE:gen/YB01.v  overlapping write bytes 0  contradicting bytes 0
    states: 50, aliases 0, duplicate states 0
    KImg ranges: 139, findings 0
FILE:gen/YB03.v  overlapping write bytes 0  contradicting bytes 0
    states: 0, aliases 0, duplicate states 0
    KImg ranges: 66, findings 0
RESULT G2a codeptr-controls rc=0
  YF0m.v       29 code (1 function starts, 1 return pcs, 27 other instruction starts),  254 data, 88 at or above the image top 0x5f8378, 279 FINDINGS: 0x10101, 0x103b8, 0x10428, 0x10430, 0x10438, 0x10440, 0x10448, 0x10450, 0x10458, 0x10460, 0x10528, 0x10530 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIB/YF0m.v: 279
codeptr-controls: PASS (must-find paired on all 6 files; must-not-flag 0x8065e)
RESULT G2b codeptr POSITIVE control (tool rc must be 1) rc=1
YD1k.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   25 data, 3 at or above the image top 0x5f3970, 22 FINDINGS: 0x103c0, 0x10468, 0x10568, 0x1cccb, 0x1cce0, 0x20b40, 0x20b44, 0x20dc0, 0x20dc8, 0x20de0, 0x20e40, 0x20e80 [stale 
YD2i.v        2 code (0 function starts, 0 return pcs, 2 other instruction starts),    5 data, 5 at or above the image top 0x5f3970, 7 FINDINGS: 0x10800, 0x80020, 0x8d178, 0x9d000, 0x3fffff, 0x5d9210, 0x5fb000 [stale against cgif_file_fuzzer.asan-ubsan, donor 
YD2j.v        3 code (0 function starts, 0 return pcs, 3 other instruction starts),   71 data, 43 at or above the image top 0x5f3970, 108 FINDINGS: 0x103b8, 0x103c0, 0x10428, 0x10468, 0x10528, 0x10568, 0x1cccb, 0x1cce0, 0x20b40, 0x20b44, 0x20dcd, 0x20de0 [stal
=== G2c PASS 1: every file, each paired with cgif's donor file of the same name, no declaration ===
RESULT G2c codeptr pass 1 rc=1
YB01.v       17 code (12 function starts, 3 return pcs, 2 other instruction starts),  415 data, 99 at or above the image top 0x5f3970, 6 FINDINGS: 0x10800, 0x20000, 0x71c00, 0x100000, 0x161200, 0x38e000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB01.v: 6 STALE (0x10800, 0x20000, 0x71c00, 0x100000, 0x161200, 0x38e000), 1 donor-file li
YB03.v       21 code (9 function starts, 10 return pcs, 2 other instruction starts),  303 data, 64 at or above the image top 0x5f3970, 9 FINDINGS: 0x10101, 0x10800, 0x1ffff, 0x445c0, 0x71c00, 0x100000, 0x100018, 0x38e000, 0x3fffff [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB03.v: 9 STALE (0x10101, 0x10800, 0x1ffff, 0x445c0, 0x71c00, 
YB05.v       37 code (4 function starts, 22 return pcs, 11 other instruction starts),    4 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB05.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YB12.v       25 code (8 function starts, 0 return pcs, 17 other instruction starts),    5 data, 2 at or above the image top 0x5f3970, 1 FINDINGS: 0x55c000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB12.v: 1 STALE (0x55c000), 2 donor-file literals with the same meaning in both images]
YB13.v        1 code (0 function starts, 0 return pcs, 1 other instruction starts),    8 data, 1 at or above the image top 0x5f3970, 1 FINDINGS: 0x55c000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB13.v: 1 STALE (0x55c000), 1 donor-file literals with the same meaning in both images]
YB1h.v        2 code (0 function starts, 0 return pcs, 1 other instruction starts),    8 data, 7 at or above the image top 0x5f3970, 2 FINDINGS: 0x158593, 0x55c000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1h.v: 2 STALE (0x158593, 0x55c000), 1 donor-file literals with the same meaning in both images]
YB1k.v       49 code (1 function starts, 0 return pcs, 46 other instruction starts),    6 data, 43 at or above the image top 0x5f3970, 6 FINDINGS: 0x155593, 0x155793, 0x255513, 0x255793, 0x455593, 0x455793 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1k.v: 6 STALE (0x155593, 0x155793, 0x255513, 0x255793, 0x455593, 0x455793), 0 donor-f
YB1l.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1m.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1v.v        2 code (2 function starts, 0 return pcs, 0 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1v.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YCej.v       21 code (1 function starts, 14 return pcs, 6 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YCej.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YD1k.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   25 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1k.v: 0 STALE (-), 5 donor-file literals with the same meaning in both images]
YD1y.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   13 data, 1 at or above the image top 0x5f3970, 1 FINDINGS: 0x3fffff [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1y.v: 1 STALE (0x3fffff), 1 donor-file literals with the same meaning in both images]
YD2i.v        2 code (1 function starts, 1 return pcs, 0 other instruction starts),    5 data, 5 at or above the image top 0x5f3970, 2 FINDINGS: 0x10800, 0x3fffff [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2i.v: 2 STALE (0x10800, 0x3fffff), 1 donor-file literals with the same meaning in both images]
YD2j.v        3 code (3 function starts, 0 return pcs, 0 other instruction starts),  109 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2j.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YE23.v        9 code (7 function starts, 2 return pcs, 0 other instruction starts),   44 data, 5 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE23.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YE37.v        1 code (1 function starts, 0 return pcs, 0 other instruction starts),   23 data, 9 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE37.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YE3i.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   26 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE3i.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YF0m.v       28 code (15 function starts, 11 return pcs, 2 other instruction starts),  230 data, 61 at or above the image top 0x5f3970, 3 FINDINGS: 0x10101, 0x10800, 0x100000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YF0m.v: 3 STALE (0x10101, 0x10800, 0x100000), 7 donor-file literals with the same meaning in both images]
codeptr: UNMEASURED: 2 of 19 file(s) hold no address literal in range
RESULT G2e declaration evidence rc=0
=== G2d PASS 2: the same + 38 declaration arguments (codeptr-decl.sh) ===
RESULT G2d codeptr pass 2 rc=2
YB01.v       15 code (12 function starts, 3 return pcs, 0 other instruction starts),  407 data, 99 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB01.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x520
YB03.v       19 code (9 function starts, 10 return pcs, 0 other instruction starts),  297 data, 64 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB03.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x520
YB05.v       37 code (4 function starts, 22 return pcs, 11 other instruction starts),    4 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB05.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YB12.v       25 code (8 function starts, 0 return pcs, 17 other instruction starts),    4 data, 2 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB12.v: 0 STALE (-), 2 donor-file literals with the same meaning in both images]
YB13.v        1 code (0 function starts, 0 return pcs, 1 other instruction starts),    7 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB13.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YB1h.v        2 code (0 function starts, 0 return pcs, 1 other instruction starts),    6 data, 7 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1h.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YB1k.v       49 code (1 function starts, 0 return pcs, 46 other instruction starts),    0 data, 43 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1k.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YB1l.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1m.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1v.v        2 code (2 function starts, 0 return pcs, 0 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1v.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YCej.v       21 code (1 function starts, 14 return pcs, 6 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YCej.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YD1k.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   25 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1k.v: 0 STALE (-), 5 donor-file literals with the same meaning in both images]
YD1y.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   12 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1y.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YD2i.v        2 code (1 function starts, 1 return pcs, 0 other instruction starts),    4 data, 5 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2i.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x520 (
YD2j.v        3 code (3 function starts, 0 return pcs, 0 other instruction starts),  109 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2j.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YE23.v        9 code (7 function starts, 2 return pcs, 0 other instruction starts),   44 data, 5 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE23.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YE37.v        1 code (1 function starts, 0 return pcs, 0 other instruction starts),   23 data, 9 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE37.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YE3i.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   26 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE3i.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YF0m.v       28 code (15 function starts, 11 return pcs, 2 other instruction starts),  228 data, 61 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YF0m.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x52
codeptr: UNMEASURED: 2 of 19 file(s) hold no address literal in range
RESULT G3 port_addr_check CONTROL cgif A->B rc=0
DIFFERENT-SYMBOL	12	FLAG
RESULT G3 port_addr_check cgif B -> uci B rc=0
DIFFERENT-SYMBOL	147	kernel 11	FLAG
RESULT G3 pac_table rc=0
| file | numerals (uci / ctl) | uci B flags | control flags (cgif A -> B) | flag classes only in uci B |
| YB01.v | 17633 / 17631 | 1581: DIFFERENT-SYMBOL 79, GEOMETRY-CHANGED 24, KIND-CHANGED 3, NON-ADDRESS-CHANGED 1418, UNPAIRED-PORTED 2, UNPAIRED-SOURCE 54, UNRESOLVED 1 | 325: DIFFERENT-SYMBOL 12, KIND-CHANGED 3, NON-ADDRESS-CHANGED 307, UNRESOLVED 3 | GEOMETRY-CHANGED, UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YB03.v | 2886 / 2886 | 200: DIFFERENT-SYMBOL 33, KIND-CHANGED 1, NON-ADDRESS-CHANGED 164, UNPAIRED-SOURCE 2 | 160: KIND-CHANGED 1, NON-ADDRESS-CHANGED 159 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YCej.v | 1690 / 1678 | 1670: DIFFERENT-SYMBOL 14, NO-COUNTERPART 3, UNPAIRED-PORTED 12, UNPAIRED-SOURCE 1640, UNRESOLVED 1 | 1128: NON-ADDRESS-CHANGED 285, UNPAIRED-PORTED 69, UNRESOLVED 774 | DIFFERENT-SYMBOL, NO-COUNTERPART, UNPAIRED-SOURCE |
| YD1k.v | 206 / 206 | 28: DIFFERENT-SYMBOL 7, KIND-CHANGED 2, NON-ADDRESS-CHANGED 14, UNPAIRED-SOURCE 4, UNRESOLVED 1 | 15: KIND-CHANGED 1, NON-ADDRESS-CHANGED 14 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE, UNRESOLVED |
| YD2j.v | 325 / 325 | 67: DIFFERENT-SYMBOL 1, KIND-CHANGED 2, NON-ADDRESS-CHANGED 48, UNPAIRED-SOURCE 12, UNRESOLVED 4 | 53: KIND-CHANGED 2, NON-ADDRESS-CHANGED 48, UNRESOLVED 3 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE23.v | 1463 / 1463 | 28: DIFFERENT-SYMBOL 1, KIND-CHANGED 1, NON-ADDRESS-CHANGED 18, UNPAIRED-SOURCE 4, UNRESOLVED 4 | 25: KIND-CHANGED 3, NON-ADDRESS-CHANGED 18, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE37.v | 287 / 281 | 93: DIFFERENT-SYMBOL 5, IDENT-MISMATCH 4, NON-ADDRESS-CHANGED 4, UNPAIRED-PORTED 6, UNPAIRED-SOURCE 74 | 12: IDENT-MISMATCH 4, KIND-CHANGED 6, NON-ADDRESS-CHANGED 2 | DIFFERENT-SYMBOL, UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YE3i.v | 50 / 50 | 14: DIFFERENT-SYMBOL 2, KIND-CHANGED 3, NON-ADDRESS-CHANGED 1, UNPAIRED-SOURCE 6, UNRESOLVED 2 | 9: KIND-CHANGED 1, NON-ADDRESS-CHANGED 4, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YF0m.v | 711 / 664 | 213: DIFFERENT-SYMBOL 5, KIND-CHANGED 12, NO-COUNTERPART 3, NON-ADDRESS-CHANGED 16, STALE-DONOR-CODE-POINTER 3, UNPAIRED-PORTED 47, UNPAIRED-SOURCE 70, UNRESOLVED 57 | 86: NON-ADDRESS-CHANGED 8, UNRESOLVED 78 | DIFFERENT-SYMBOL, KIND-CHANGED, NO-COUNTERPART, STALE-DONOR-CODE-POINTER, UNPAIRED-PORTED, UNPAIRED-SOURCE |
uci B verdicts: {'DIFFERENT-SYMBOL': 147, 'GEOMETRY-CHANGED': 24, 'IDENT-MISMATCH': 4, 'IMAGE-EXTENT-SAME': 29, 'INSN-SAME': 114, 'KIND-CHANGED': 25, 'NO-COUNTERPART': 6, 'NON-ADDRESS-CHANGED': 1686, 'NON-ADDRESS-SAME': 18286, 'ROUND-CONSTANT-SAME': 30, 'SAME-CONTENT': 6, 'SAME-GEOMETRY': 3936, 'SAME-SYMBOL': 2329, 'STALE-DONOR-CODE-POINTER': 3, 'UNPAIRED-PORTED': 68, 'UNPAIRED-SOURCE': 1892, 'UNR
control verdicts: {'DIFFERENT-SYMBOL': 12, 'GEOMETRY-CHANGED': 1, 'IDENT-MISMATCH': 4, 'IMAGE-EXTENT-SAME': 32, 'INSN-SAME': 114, 'KIND-CHANGED': 17, 'NON-ADDRESS-CHANGED': 860, 'NON-ADDRESS-SAME': 19556, 'ROUND-CONSTANT-SAME': 82, 'SAME-CONTENT': 41, 'SAME-GEOMETRY': 3966, 'SAME-SYMBOL': 2967, 'UNPAIRED-PORTED': 69, 'UNRESOLVED': 867}
uci B rows of the classes STALE-DONOR-CODE-POINTER / NO-COUNTERPART / IDENT-MISMATCH / GEOMETRY-CHANGED (distinct by file, definition, source value, ported value; count of rows):
  IDENT-MISMATCH x1  YE37.v Lemma zi8_14ea00  src YE37.v:176 0x14ea00 -> dst line 169 0x14ea00  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x168c0[data] in the donor but __sanitizer::useCounts+0x1da40 in the target; same symbol __sanitizer::useCounts, offset 0x168c0 vs 0x1da40; expected 0x14
  IDENT-MISMATCH x1  YE37.v Lemma zi8_14f970  src YE37.v:177 0x14f970 -> dst line 170 0x14f970  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x17830[data] in the donor but __sanitizer::useCounts+0x1e9b0 in the target; same symbol __sanitizer::useCounts, offset 0x17830 vs 0x1e9b0; expected 0x14
  IDENT-MISMATCH x1  YE37.v Theorem x2_realizes / sentence 35  src YE37.v:204 0x14ea00 -> dst line 197 0x14ea00  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x168c0[data] in the donor but __sanitizer::useCounts+0x1da40 in the target; same symbol __sanitizer::useCounts, offset 0x168c0 vs 0x1da40; expected 0x14
  IDENT-MISMATCH x1  YE37.v Theorem x2_realizes / sentence 44  src YE37.v:208 0x14f970 -> dst line 201 0x14f970  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x17830[data] in the donor but __sanitizer::useCounts+0x1e9b0 in the target; same symbol __sanitizer::useCounts, offset 0x17830 vs 0x1e9b0; expected 0x14
  16f8a030c869 has no GENERATOR-FILL class (added in 0767e70e074a); rows with that verdict: control 0, uci B 0
RESULT G3b port_addr_check cb0e CONTROL cgif A->B rc=0
GENERATOR-FILL	506	REPORTED
DIFFERENT-SYMBOL	12	FLAG
FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
RESULT G3b port_addr_check cb0e cgif B -> uci B rc=0
GENERATOR-FILL	45	kernel 37	REPORTED
DIFFERENT-SYMBOL	147	kernel 11	FLAG
FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
RESULT G3b pac_table (cb0e) rc=0
| file | numerals (uci / ctl) | uci B flags | control flags (cgif A -> B) | flag classes only in uci B |
| YB01.v | 17633 / 17631 | 1271: DIFFERENT-SYMBOL 79, KIND-CHANGED 3, NON-ADDRESS-CHANGED 1132, UNPAIRED-PORTED 2, UNPAIRED-SOURCE 54, UNRESOLVED 1 | 38: DIFFERENT-SYMBOL 12, KIND-CHANGED 3, NON-ADDRESS-CHANGED 19, UNRESOLVED 4 | UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YB03.v | 2886 / 2886 | 43: DIFFERENT-SYMBOL 33, KIND-CHANGED 1, NON-ADDRESS-CHANGED 7, UNPAIRED-SOURCE 2 | 2: KIND-CHANGED 1, NON-ADDRESS-CHANGED 1 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YCej.v | 1690 / 1678 | 1670: DIFFERENT-SYMBOL 14, NO-COUNTERPART 3, UNPAIRED-PORTED 12, UNPAIRED-SOURCE 1640, UNRESOLVED 1 | 565: NON-ADDRESS-CHANGED 128, UNPAIRED-PORTED 69, UNRESOLVED 368 | DIFFERENT-SYMBOL, NO-COUNTERPART, UNPAIRED-SOURCE |
| YD1k.v | 206 / 206 | 26: DIFFERENT-SYMBOL 7, KIND-CHANGED 2, NON-ADDRESS-CHANGED 12, UNPAIRED-SOURCE 4, UNRESOLVED 1 | 13: KIND-CHANGED 1, NON-ADDRESS-CHANGED 12 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE, UNRESOLVED |
| YD2j.v | 325 / 325 | 28: DIFFERENT-SYMBOL 1, KIND-CHANGED 2, NON-ADDRESS-CHANGED 9, UNPAIRED-SOURCE 12, UNRESOLVED 4 | 14: KIND-CHANGED 2, NON-ADDRESS-CHANGED 9, UNRESOLVED 3 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE23.v | 1463 / 1463 | 10: DIFFERENT-SYMBOL 1, KIND-CHANGED 1, UNPAIRED-SOURCE 4, UNRESOLVED 4 | 7: KIND-CHANGED 3, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE37.v | 287 / 281 | 89: DIFFERENT-SYMBOL 5, NON-ADDRESS-CHANGED 4, UNPAIRED-PORTED 6, UNPAIRED-SOURCE 74 | 9: KIND-CHANGED 6, NON-ADDRESS-CHANGED 2, UNRESOLVED 1 | DIFFERENT-SYMBOL, UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YE3i.v | 50 / 50 | 13: DIFFERENT-SYMBOL 2, KIND-CHANGED 3, UNPAIRED-SOURCE 6, UNRESOLVED 2 | 8: KIND-CHANGED 1, NON-ADDRESS-CHANGED 3, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YF0m.v | 711 / 664 | 168: DIFFERENT-SYMBOL 5, KIND-CHANGED 6, NON-ADDRESS-CHANGED 8, UNPAIRED-PORTED 39, UNPAIRED-SOURCE 70, UNRESOLVED 40 | 86: NON-ADDRESS-CHANGED 7, UNRESOLVED 79 | DIFFERENT-SYMBOL, KIND-CHANGED, UNPAIRED-PORTED, UNPAIRED-SOURCE |
uci B verdicts: {'DIFFERENT-SYMBOL': 147, 'GENERATOR-FILL': 45, 'IDENT-NAME': 4, 'IMAGE-EXTENT-SAME': 13, 'INSN-SAME': 114, 'KIND-CHANGED': 18, 'NO-COUNTERPART': 3, 'NON-ADDRESS-CHANGED': 1175, 'NON-ADDRESS-SAME': 18369, 'ROUND-CONSTANT-SAME': 30, 'SAME-CONTENT': 6, 'SAME-GEOMETRY': 3938, 'SAME-SYMBOL': 2788, 'UNPAIRED-PORTED': 60, 'UNPAIRED-SOURCE': 1892, 'UNRESOLVED': 54}
control verdicts: {'DIFFERENT-SYMBOL': 12, 'GENERATOR-FILL': 506, 'GEOMETRY-CHANGED': 1, 'IDENT-NAME': 4, 'IMAGE-EXTENT-SAME': 32, 'INSN-SAME': 114, 'KIND-CHANGED': 17, 'NON-ADDRESS-CHANGED': 195, 'NON-ADDRESS-SAME': 19640, 'ROUND-CONSTANT-SAME': 82, 'SAME-CONTENT': 41, 'SAME-GEOMETRY': 3888, 'SAME-SYMBOL': 3523, 'UNPAIRED-PORTED': 69, 'UNRESOLVED': 464}
uci B rows of the classes STALE-DONOR-CODE-POINTER / NO-COUNTERPART / IDENT-MISMATCH / GEOMETRY-CHANGED (distinct by file, definition, source value, ported value; count of rows):
=== G3c GENERATOR-FILL triage (tools/pac_fill.py): every row a measured reason; CONTROL cgif A -> B first ===
RESULT G3c fill triage CONTROL cgif A->B rc=1
GENERATOR-FILL rows: 506, on 236 ported lines: {'YCej.v': 236}
  UNEXPLAINED YCej.v:30 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:32 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:34 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:36 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:38 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:46 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:48 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:50 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:52 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:85 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:87 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:89 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:91 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:94 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:96 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:98 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:100 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:102 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:104 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:106 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:108 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:110 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:112 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:114 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:116 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:118 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:120 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:122 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:124 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:129 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:134 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:136 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:138 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:140 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:146 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:148 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:150 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:152 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:154 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:156 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:161 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:163 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:165 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:167 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:169 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:171 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:173 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:175 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:177 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:179 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:187 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:189 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:191 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:193 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:195 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:197 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:205 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:207 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:209 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:211 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:217 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:220 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:222 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:225 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:227 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:230 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:232 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:234 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:236 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:238 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:240 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:243 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:245 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:247 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:249 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:252 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:253 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:255 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:257 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:258 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:260 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:262 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:263 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:265 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:267 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:268 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:270 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:272 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:273 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:275 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:277 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:278 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:280 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:282 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:283 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:285 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:287 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:288 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:290 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:292 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:293 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:295 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:297 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:298 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:300 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:302 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:303 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:305 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:307 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:308 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:310 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:312 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:313 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:315 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:317 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:318 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:320 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:322 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:323 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:325 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:327 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:328 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:330 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:332 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:333 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:335 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:337 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:338 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:340 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:342 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:343 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:345 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:351 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:355 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:357 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:361 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:363 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:381 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:383 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:385 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:387 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:389 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:391 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:393 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:395 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:397 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:399 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:401 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:403 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:405 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:407 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:409 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:411 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:413 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:415 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:417 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:419 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:421 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:423 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:425 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:427 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:429 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:431 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:432 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:434 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:436 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:437 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:439 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:441 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:442 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:444 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:446 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:447 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:449 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:451 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:452 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:454 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:456 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:457 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:459 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:461 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:462 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:464 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:466 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:467 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:469 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:471 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:472 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:474 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:476 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:477 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:479 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:481 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:489 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:491 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:493 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:495 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:497 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:499 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:501 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:503 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:505 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:507 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:509 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:511 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:513 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:515 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:517 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:519 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:521 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:522 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:524 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:526 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:527 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:529 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:531 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:532 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:534 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:536 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:537 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:539 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:541 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:542 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:544 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:546 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:547 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:549 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:551 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:552 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:554 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:556 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:557 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:559 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:561 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:562 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:564 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
pac_fill: 236 of 236 ported lines UNEXPLAINED (506 GENERATOR-FILL rows)
RESULT G3c fill triage uci B rc=0
GENERATOR-FILL rows: 45, on 24 ported lines: {'YF0m.v': 24}
  YF0m.v:126 row 86 `z8 (ANum 0x97e10) 0xfffffffffffff800  ;` not an af0m FILL: unit image word at 0x97e10 (.got) = 0xfffffffffffff800; donor slot 0x9ef08 holds 0xfffffffffffff800 in cgif's image (.got), the same link-time word, a tp offset (negative), not an address; other unit rows with this cell or value: lines [] -> ACCEPTED
pac_fill: 0 of 24 ported lines UNEXPLAINED (45 GENERATOR-FILL rows)
=== G4 CONTROL FIRST: planted copy (plant_uciB.py), .text end + 4 = 0x95b94 in CODE cells must be flagged, in a DATA cell not ===
RESULT G4 plant rc=0
planted P1-CODE YF0m.v:105  z8 (ANum 0x98f80) 0x90458 -> z8 (ANum 0x98f80) 0x95b94
planted P2-CODE YF0m.v:22  [[0x51a24; 0x7ee9c] -> [[0x95b94; 0x7ee9c]
planted P3-CODE YB12.v:15  x_memset := 0x9085c -> x_memset := 0x95b94
planted P4-CODE YB01.v:22  SS 519752 [ELit 0; ELit 550212; -> SS 519752 [ELit 0; ELit 613268;
planted D1-DATA YF0m.v:74  z8 (ANum 0x9c8f8) 0x100ffffffff -> z8 (ANum 0x9c8f8) 0x95b94
RESULT G4 classify PLANTED (must be rc 1) rc=1
== uciB.planted: image fuzz_uci.asan-ubsan sha256 a1b86e424add; .text [0x2fbf0, 0x95b90) = 104424 words; image [0x10000, 0x5f4000); objdump source = twin: True
   files $UCIB_GATEWORK/classify/planted: 23745 literals, 4185 >= .text end (1808 inside the image, 2377 past it)
   FINDINGS (CODE role, value not in .text): 4 (of them >= .text end: 4)
  PLANTED CONTROL: PASS
RESULT G4 planted control verdict rc=0
RESULT G4 classify uciB rc=0
   FINDINGS (CODE role, value not in .text): 0 (of them >= .text end: 0)
RESULT G4 coverage report rc=0
RESULT G5 recount rc=0
cgifB-control states 50 kn lists 50 aliases 0 duplicate state bodies 0 duplicate kn bodies 0 arrival SS values ['524320'] all == main 0x80020 True
uciB states 50 kn lists 50 aliases 0 duplicate state bodies 0 duplicate kn bodies 0 arrival SS values ['519752'] all == main 0x7ee48 True
RESULT G6 keyed scan rc=0
== fuzz_uci B own __asan_stack_malloc_* symbols (twin .symtab $UCIB_UBS)
   0x3c1b8 __asan_stack_malloc_1 size 400 STT_FUNC
   classes defined (STT_FUNC): 1  -> T0.4 item 1 (one class, __asan_stack_malloc_1 @0x3c1b8): True
   A/AF0l.v  forbidden-literal hits 2: [('AF0l.v', 11, '0x3c8a4', 'cgif A __asan_stack_malloc_1'), ('AF0l.v', 11, '0x3ca34', 'cgif A __asan_stack_malloc_2')]
   A/AF0l.v  stack_malloc lines 1: [(11, 'pc_stack_malloc := fun cid => if cid =? 1 then 0x3c8a4 else if cid =? 2 then 0x3ca34 else 0;')]
   YF0l.v    forbidden-literal hits 2: [('YF0l.v', 11, '0x3c8d4', 'cgif B __asan_stack_malloc_1'), ('YF0l.v', 11, '0x3ca64', 'cgif B __asan_stack_malloc_2')]
   YF0l.v    stack_malloc lines 1: [(11, 'pc_stack_malloc := fun cid => if cid =? 1 then 0x3c8d4 else if cid =? 2 then 0x3ca64 else 0;')]
   YB01   forbidden 0  stack_malloc lines 0   
   YB03   forbidden 0  stack_malloc lines 0   
   YB05   forbidden 0  stack_malloc lines 0   
   YB12   forbidden 0  stack_malloc lines 0   
   YB13   forbidden 0  stack_malloc lines 0   
   YB1h   forbidden 0  stack_malloc lines 0   
   YB1k   forbidden 0  stack_malloc lines 0   
   YB1l   forbidden 0  stack_malloc lines 0   
   YB1m   forbidden 0  stack_malloc lines 0   
   YB1v   forbidden 0  stack_malloc lines 0   
   YCej   forbidden 0  stack_malloc lines 0   
   YD1k   forbidden 0  stack_malloc lines 0   
   YD1y   forbidden 0  stack_malloc lines 0   
   YD2i   forbidden 0  stack_malloc lines 0   
   YD2j   forbidden 0  stack_malloc lines 0   
   YE23   forbidden 0  stack_malloc lines 0   
   YE37   forbidden 0  stack_malloc lines 0   
   YE3i   forbidden 0  stack_malloc lines 0   
   YF0m   forbidden 0  stack_malloc lines 0   
   TOTAL forbidden literals in 19 files: 0 -> PASS
RESULT G7a pins check rc=0
RESULT G7b stamp YB01 (file Read-from line: line 5; stamp writes it at line 10, text EQUAL; every other line EQUAL) rc=0
RESULT G7b stamp YB03 (file Read-from line: line 5; stamp writes it at line 8, text EQUAL; every other line EQUAL) rc=0
RESULT G7b stamp YB05 (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB12 (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YB12.v atable image fields (key = field): 3 rows, exactly the set fuzz_uci.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS YB12.v stops_more (key = self-loop site): 13 rows, exactly the set fuzz_uci.asan-ubsan (13 self-loops, in .text) defines
RESULT G7b stamp YB13 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YB1h (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB1k (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
RESULT G7b stamp YB1l (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB1m (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YB1v (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YCej (file Read-from line: line 6; stamp writes it at line 6, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD1k (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD1y (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YD2i (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD2j (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YD2j.v regions (key = region name): 31 rows, exactly the set the region definitions of YD2j.v defines
PASS YD2j.v anchor roles (key = role, present iff the image defines its object): 16 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
RESULT G7b stamp YE23 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YE37 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YE3i (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YF0m (file Read-from line: line 6; stamp writes it at line 6, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=2
PASS YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
pins: NOT STAMPED $UCIB_GATEWORK/stamp/YF0m.v: an AF0m / YF0m is checked with the OTHER image's table (keyset realset: the __interception::real_* rows of A and B must agree), and this run has no --pair: the REAL rows are UNMEASURED. Give --pair <the other image's F0m> --pair-syms <its symbol table>
RESULT G7c stamp YF0m --pair (stamped copy DIFFERS; the same multiset of lines: True (only line order in the header moves)) rc=0
PASS YF0m.pair.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS YF0m.pair.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE YF0m.pair.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
PASS REAL rows, A == B (key = N of __interception::real_N): 14 rows, exactly the set A (fuzz_uci.asan) defines
PASS donor REAL rows, A == B (each keyed by the donor image's own symbol table): 16 rows, exactly the set donor A (cgif_file_fuzzer.asan.nm) defines
PASS REAL rows, donor subset of ours (A): donor 16 ['__tls_get_addr', 'atoll', 'bcmp', 'fclose', 'fflush', 'fopen', 'fwrite', 'memchr', 'memcmp', 'memcpy', 'memset', 'read', 'strchr', 'strnlen', 'vfprintf', 'vprintf']; 13 of them this image defines real_N for, all present; not in this image (no real
PASS REAL rows, donor subset of ours (B): donor 16 ['__tls_get_addr', 'atoll', 'bcmp', 'fclose', 'fflush', 'fopen', 'fwrite', 'memchr', 'memcmp', 'memcpy', 'memset', 'read', 'strchr', 'strnlen', 'vfprintf', 'vprintf']; 13 of them this image defines real_N for, all present; not in this image (no real
RESULT G7d emitcheck rc=0
RESULT G7e keyset CONTROL cgif released YB12 rc=1
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YB12.v atable image fields (key = field): 3 rows, exactly the set cgif_file_fuzzer.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS cgif/YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the names of record cgif/YB1w.v defines
keyset: REFUSED cgif/YB12.v stops_more (key = self-loop site)
keyset: REFUSED
RESULT G7e keyset CONTROL cgif released YF0m rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 35 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 5 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) and the PT_LOAD hull defines
PASS cgif/YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 4 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 24 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
NOTE cgif/YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
keyset: PASS for the per-file row sets (measured: 1 file(s), 5 sub-checks, 70 rows); REAL() rows of 1 AF0m / YF0m UNMEASURED (single files: run `keyset.py realset` on the A+B pair)
RESULT G7e keyset CONTROL cgif released YD2j rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YD2j.v regions (key = region name): 33 rows, exactly the set the region definitions of $UCIB_GATEWORK/in/cgif/YD2j.v defines
UNMEASURED cgif/YD2j.v: no twin, so the anchor roles (gen_ad2.ANCHOR_NAMES) are not checked by symbol
keyset: PASS for the measured sub-checks (measured: 1 file(s), 1 sub-checks, 33 rows); UNMEASURED sub-checks (see the UNMEASURED lines) in: cgif/YD2j.v
RESULT G7e keyset CONTROL cgif released YB1k rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the names of record cgif/YB1w.v defines
keyset: PASS (measured: 1 file(s), 1 sub-checks, 3 rows)
RESULT G7e keyset CONTROL cgif YB12 (atable re-emitted) rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS $WK/ctl/YB12.cgif.v atable image fields (key = field): 3 rows, exactly the set cgif_file_fuzzer.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS $WK/ctl/YB12.cgif.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the names of record cgif/YB1w.v defines
PASS $WK/ctl/YB12.cgif.v stops_more (key = self-loop site): 13 rows, exactly the set cgif_file_fuzzer.asan-ubsan (13 self-loops, in .text) defines
keyset: PASS (measured: 1 file(s), 3 sub-checks, 27 rows)
RESULT G7e keyset uciB rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS gen/YB12.v atable image fields (key = field): 3 rows, exactly the set fuzz_uci.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS gen/YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS gen/YB12.v stops_more (key = self-loop site): 13 rows, exactly the set fuzz_uci.asan-ubsan (13 self-loops, in .text) defines
PASS gen/YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS gen/YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE gen/YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
PASS gen/YD2j.v regions (key = region name): 31 rows, exactly the set the region definitions of $UCIB_GATEWORK/in/gen/YD2j.v defines
PASS gen/YD2j.v anchor roles (key = role, present iff the image defines its object): 16 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS gen/YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
keyset: PASS for the per-file row sets (measured: 4 file(s), 11 sub-checks, 103 rows); REAL() rows of 1 AF0m / YF0m UNMEASURED (single files: run `keyset.py realset` on the A+B pair)
RESULT G8 ifchk CONTROL cgif B rc=0
ifchk: 267 cells (sym 22, abs 210, shadow 35) x 50 states: 13350 = stated, 0 different, 0 undetermined (None), 0 inexpressible
RESULT G8 ifchk no-states (want 2) rc=2
ifchk: REFUSED: no states named HS_tfib_N in $UCIB_GATEWORK/ctl/empty.YB01.v
RESULT G8 ifchk --nholes 49 (want 2) rc=2
ifchk: REFUSED: $UCIB_GATEWORK/in/raw/YB01.v holds 50 hand-off states, expected 49 (--nholes); a check over 50 states proves nothing about the others
planted: 'z8 (ANum 0x130c28) 0x1 ' -> 'z8 (ANum 0x130c28) 0x2 '
RESULT G8 plant rc=0
RESULT G8 ifchk PLANTED (want 1) rc=1
RESULT G8 ifchk uciB rc=0
ifchk: 250 cells (sym 22, abs 217, shadow 11) x 50 states: 12500 = stated, 0 different, 0 undetermined (None), 0 inexpressible
RESULT G9 selftest 542898b2/4161c861 rc=0
SELFTEST PASS shadowcheck 542898b23954d1fc ownedcheck 4161c861b0d991bb
RESULT G9 ownedcheck-352fb92f CONTROL rc=0
owned ranges 37, const cells 245, UNOWNED 0, OVERCLAIM 0, UNPARSED 0
RESULT G9 ownedcheck-352fb92f uciB rc=0
owned ranges 35, const cells 228, UNOWNED 0, OVERCLAIM 0, UNPARSED 0
RESULT G9 ownedcheck-4161c861 CONTROL rc=0
owned ranges 37, const cells 245, UNOWNED 0, OVERCLAIM 0, UNPARSED 0
RESULT G9 ownedcheck-4161c861 uciB rc=0
owned ranges 35, const cells 228, UNOWNED 0, OVERCLAIM 0, UNPARSED 0
RESULT G9 shadowcheck-e04173f5 CONTROL rc=0
Tfib_const_shadow: 35 cells, 0 wrong
RESULT G9 shadowcheck-e04173f5 uciB rc=0
Tfib_const_shadow: 11 cells, 0 wrong
RESULT G9 shadowcheck-6dccc6f9 CONTROL rc=0
Tfib_const_shadow: 35 cells, 0 wrong
RESULT G9 shadowcheck-6dccc6f9 uciB rc=0
Tfib_const_shadow: 11 cells, 0 wrong
RESULT G9 shadowcheck-542898b2 CONTROL rc=0
Tfib_const_shadow: 35 cells, 0 wrong
RESULT G9 shadowcheck-542898b2 uciB rc=0
Tfib_const_shadow: 11 cells, 0 wrong
=== G10 lowbeg.py with gen_ad1k of bundle 8cd7 (814c81b8966e, YD1k's generator): CONTROL cgif B first, then fuzz_uci B ===
RESULT G10 lowbeg (8cd7) rc=0
$UCIB_CB sha256=1c29845fe605 descriptors=3 lowest_beg=0x20dc0 mod64=0 hull_bound=0x20dc0 aligned (unchanged)
$UCIB_UB sha256=a1b86e424add descriptors=1 lowest_beg=0x20ca0 mod64=32 hull_bound=0x20c80 AFFECTED (old NHULL = beg is wrong)
=== G10 lowbeg.py with gen_ad1k of bundle dbb5 (43a0cf0abc67): CONTROL cgif B first, then fuzz_uci B ===
RESULT G10 lowbeg (dbb5) rc=0
$UCIB_CB sha256=1c29845fe605 descriptors=3 lowest_beg=0x20dc0 mod64=0 hull_bound=0x20dc0 aligned (unchanged)
$UCIB_UB sha256=a1b86e424add descriptors=1 lowest_beg=0x20ca0 mod64=32 hull_bound=0x20c80 AFFECTED (old NHULL = beg is wrong)
  cgif B (control)  lowbeg hull_bound 0x20dc0; YD1k `p + n <= ...` bounds ['0x20dc0'] at lines [212, 226] -> EQUAL
  fuzz_uci B        lowbeg hull_bound 0x20c80; YD1k `p + n <= ...` bounds ['0x20c80'] at lines [214, 228] -> EQUAL
RESULT G10 YD1k hull text = lowbeg hull (cgif control + uci) rc=0
=== G11a gen_exitB.py --af0m WK/raw/YF0m.v (its own controls C1.. run first inside; rodata_chk / cellr / shbyte_chk / DRVW_not_owned) ===
RESULT G11a gen_exitB --af0m rc=0
  C3b decode B   __asan_unregister_globals 0x3ef00: addi a1,a0,1 @0x3f0a8; bgeu a1,s2 @0x3f0ac -> 0x3f170 `sb zero, 0(a0)`; s2 = 2 @['0x3f080'] (capstone 5.0.7): PASS
  C3b fuzz_uci B __asan_unregister_globals 0x3e9d8: addi a1,a0,1 @0x3eb80; bgeu a1,s2 @0x3eb84 -> 0x3ec48 `sb zero, 0(a0)`; s2 = 2 @['0x3eb58'] (capstone 5.0.7): PASS
     F_STDOUT     YE23 0x9b7c8    unit 0x9b7c8    PASS
     F_STDERR     YE23 0x9b6d8    unit 0x9b6d8    PASS
     A_GOT_canary YE23 0x97db0    unit 0x97db0    PASS
     A_canary     YE23 0x5f20d0   unit 0x5f20d0   PASS
     A_GOT_CANARY (YE22) 0x97db0 = A_GOT_canary: PASS
     [0x9b690, 0x9b9d0) = oft_arg0 .. asan_globals PASS
     [0x9ba48, 0x9ba90) = __do_init.__initialized .. __do_fini.__finalized PASS
     [0x5d1750, 0x5d2038) = target_run.initialized .. builtin_tls+112 PASS
     [0x5f20e0, 0x5f2300) = finished_atexit .. exit.exit_lock PASS
     X1 YD1y 0xa2bc8   -> 0x9ba48   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YD1y 0xa2c10   -> 0x9ba90   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YD1y 0x5d88d0  -> 0x5d1750  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YD1y 0x5f9260  -> 0x5f20e0  cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YD1y 0x5f9480  -> 0x5f2300  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9e1d8   -> 0x970f8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9e1e0   -> 0x97100   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9e1e8   -> 0x97108   cgif refs 77 (moved 77) == uci refs 77: PASS
     X1 YE23 0x9eea8   -> 0x97db0   cgif refs 51 (moved 50, not identical code ['0x92c58']) == uci refs 50: PASS
     X1 YE23 0x9eed8   -> 0x97de0   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9eee0   -> 0x97de8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9eee8   -> 0x97df0   cgif refs 3 (moved 3) == uci refs 3: PASS
     X1 YE23 0xa27e8   -> 0x9b6d8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0xa28d0   -> 0x9b7c0   cgif refs 4 (moved 4) == uci refs 4: PASS
     X1 YE23 0xa28d8   -> 0x9b7c8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0xa29c0   -> 0x9b8b0   cgif refs 4 (moved 4) == uci refs 4: PASS
     X1 YE23 0xa2ab0   -> 0x9b9a0   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0xa2ab8   -> 0x9b9a8   cgif refs 3 (moved 3) == uci refs 3: PASS
     X1 YE23 0xa2bc0   -> 0x9ba40   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0xa2bc8   -> 0x9ba48   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0xa2c10   -> 0x9ba90   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0x5d88d4  -> 0x5d1754  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x5f9260  -> 0x5f20e0  cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0x5f9480  -> 0x5f2300  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x5f94a3  -> 0x5f2323  cgif refs 4 (moved 4) == uci refs 4: PASS
     X1 YE23 0x5f94a4  -> 0x5f2324  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x5f9900  -> 0x5f2780  cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE37 0x103a0   -> 0x103a0   cgif refs 36 (moved 36) == uci refs 36: PASS
     X1 YE37 0x9e1e8   -> 0x97108   cgif refs 77 (moved 77) == uci refs 77: PASS
     X1 YE37 0x9ee98   -> 0x97da0   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE37 0xa0098   -> 0x98f88   cgif refs 2 (moved 1, not identical code ['0x51b3c']) == uci refs 1: PASS
     X1 YE37 0xa00d0   -> 0x98fc0   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE37 0xa2bc0   -> 0x9ba40   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE37 0xa5adc   -> 0x9e95c   cgif refs 3 (moved 3) == uci refs 3: PASS
     X1 YE37 0xa6f58   -> 0x9fdd8   cgif refs 8 (moved 8) == uci refs 8: PASS
     X1 YE37 0xa6f60   -> 0x9fde0   cgif refs 3 (moved 3) == uci refs 3: PASS
  --af0m $UCIB_GATEWORK/in/raw/YF0m.v: rodata_chk / cellr / shbyte_chk misses 0 []; DRVW_not_owned overlaps 0 []
PASS
  re-generated YE23.v BYTE-EQUAL to the exitdrv sub-lane's own output $UCIB_EXITWORK/out/YE23.v
  YE23.v: with every `From .. Require ..` sentence removed and TfibSyms -> UciSyms (the module-path / record rewrite), the re-generated (donor-namespace) text and WK/gen are EQUAL (1664 / 1664 non-blank lines)
  re-generated YD1y.v BYTE-EQUAL to the exitdrv sub-lane's own output $UCIB_EXITWORK/out/YD1y.v
  YD1y.v: with every `From .. Require ..` sentence removed and TfibSyms -> UciSyms (the module-path / record rewrite), the re-generated (donor-namespace) text and WK/gen are EQUAL (357 / 357 non-blank lines)
  re-generated YE37.v BYTE-EQUAL to the exitdrv sub-lane's own output $UCIB_EXITWORK/out/YE37.v
  YE37.v: with every `From .. Require ..` sentence removed and TfibSyms -> UciSyms (the module-path / record rewrite), the re-generated (donor-namespace) text and WK/gen are EQUAL (223 / 223 non-blank lines)
cgif EQUAL
RESULT G11b XW2 cgif rc=0
uciB EQUAL
RESULT G11b XW2 uciB rc=0
  logs/ab1hk.control.log:3:control YB1h: EQUAL
  logs/ab1hk.control.log:4:control YB1k: EQUAL
  logs/boxb1.control.B.log:4:boxb1 control YB1v.v: EQUAL
  logs/boxb1.control.B.log:5:boxb1 control YB1h.v: EQUAL
  logs/boxb1.control.B.log:6:boxb1 control YB1k.v: EQUAL
  logs/run_restB.gen2.log:13:PASS YB12.v atable image fields (key = field): 3 rows, exactly the set fuzz_uci.asan-ubsan (e_entry, PT_LOAD hull) defines
  logs/run_restB.gen2.log:14:PASS YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
  logs/run_restB.gen2.log:15:PASS YB12.v stops_more (key = self-loop site): 13 rows, exactly the set fuzz_uci.asan-ubsan (13 self-loops, in .text) defines
  logs/run_restB.gen2.log:19:atable planted control (regen == file; planted x_memset +4 caught: 2 diff lines) rc=0
  logs/run_restB.gen2.log:22:control YD2i BYTE-EQUAL rc=0
  logs/run_restB.gen2.log:23:control YD2j BYTE-EQUAL rc=0
  logs/run_restB.gen2.log:58:PASS YD2j.v regions (key = region name): 31 rows, exactly the set the region definitions of YD2j.v defines
  logs/run_restB.gen2.log:59:PASS YD2j.v anchor roles (key = role, present iff the image defines its object): 16 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
  logs/run_restB.gen2.log:65:control YD1k BYTE-EQUAL rc=0
  logs/run_restB.gen2.log:75:control BYTE-EQUAL to cgif's YE3i.v rc=0
  logs/run_restB.gen2.log:79:IMG_RO [0x10000, 0x2ebf0) = RO PT_LOAD file range [0x10000, 0x2ebf0); 13 chunks; recomputed region minus owned: EQUAL
  logs/run_restB.gen2.log:83:nsB YB12.v: Require (dir, module) set EQUAL to fuzz_grant B lib/B/YB12.v at 4f87de75d67 (2 modules)
  logs/run_restB.gen2.log:86:nsB YD2i.v: Require (dir, module) set EQUAL to fuzz_grant B lib/B/YD2i.v at 4f87de75d67 (29 modules)
  logs/run_restB.gen2.log:89:nsB YD2j.v: Require (dir, module) set EQUAL to fuzz_grant B lib/B/YD2j.v at 4f87de75d67 (3 modules)
  logs/run_restB.gen2.log:92:nsB YD1k.v: Require (dir, module) set EQUAL to fuzz_grant B lib/B/YD1k.v at 4f87de75d67 (55 modules)
  logs/run_restB.gen2.log:95:nsB YE3i.v: Require (dir, module) set EQUAL to fuzz_grant B lib/B/YE3i.v at 4f87de75d67 (22 modules)
  logs/af0m/run_af0mB.gen2.log:4:CONTROL cgif B (--names none): BYTE-EQUAL
  logs/af0m/run_af0mB.gen2.log:6:CONTROL cgif B (cgif nm, TFIB_TR0 / TFIB_HASH derived): BYTE-EQUAL
  logs/af0m/run_af0mB.gen2.log:31:redzone-tail self-check: PASS (1 read-only tails, 24 bytes, each covered at its full descriptor length: (0x20ca8, 0x18))
  logs/af0m/run_af0mB.gen2.log:50:index gate: PASS (178 kept base rows at their base index; 217 output rows)
  logs/af0m/run_af0mB.gen2.log:51:xowned gate: PASS (217 const_abs cells, 11 shadow cells, all inside Tfib_owned_static or its shadow)
  logs/af0m/run_af0mB.gen2.log:52:am_const gate: PASS (every byte of all 217 Tfib_const_abs cells pinned by all 50 states; 761 bytes come from the image module's .bss zero fill under a KImg range)
  logs/af0m/run_af0mB.gen2.log:54:symbol gate PASS: _ZN6__asanL19malloc_context_sizeE (0x9fdfc) = [30] in all 50 states
  logs/af0m/run_af0mB.gen2.log:55:symbol gate PASS: _ZN6__asanL11asan_initedE (0x9fdd8) = [1] in all 50 states
  logs/af0m/run_af0mB.gen2.log:59:PASS YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
  logs/af0m/run_af0mB.gen2.log:60:PASS YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
  logs/af0m/run_af0mB.gen2.log:61:PASS YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
  logs/af0m/run_af0mB.gen2.log:62:PASS YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
  logs/af0m/run_af0mB.gen2.log:63:PASS YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
```

## Earlier: re-run of the gates touching YE37 after the 8-word change (G2 G3 G4 G7 G8 G11)

```
RESULT G2a codeptr-controls rc=0
  YF0m.v       29 code (1 function starts, 1 return pcs, 27 other instruction starts),  254 data, 88 at or above the image top 0x5f8378, 279 FINDINGS: 0x10101, 0x103b8, 0x10428, 0x10430, 0x10438, 0x10440, 0x10448, 0x10450, 0x10458, 0x10460, 0x10528, 0x10530 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIB/YF0m.v: 279
codeptr-controls: PASS (must-find paired on all 6 files; must-not-flag 0x8065e)
RESULT G2b codeptr POSITIVE control (tool rc must be 1) rc=1
YD1k.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   25 data, 3 at or above the image top 0x5f3970, 22 FINDINGS: 0x103c0, 0x10468, 0x10568, 0x1cccb, 0x1cce0, 0x20b40, 0x20b44, 0x20dc0, 0x20dc8, 0x20de0, 0x20e40, 0x20e80 [stale 
YD2i.v        2 code (0 function starts, 0 return pcs, 2 other instruction starts),    5 data, 5 at or above the image top 0x5f3970, 7 FINDINGS: 0x10800, 0x80020, 0x8d178, 0x9d000, 0x3fffff, 0x5d9210, 0x5fb000 [stale against cgif_file_fuzzer.asan-ubsan, donor 
YD2j.v        3 code (0 function starts, 0 return pcs, 3 other instruction starts),   71 data, 43 at or above the image top 0x5f3970, 108 FINDINGS: 0x103b8, 0x103c0, 0x10428, 0x10468, 0x10528, 0x10568, 0x1cccb, 0x1cce0, 0x20b40, 0x20b44, 0x20dcd, 0x20de0 [stal
=== G2c PASS 1: every file, each paired with cgif's donor file of the same name, no declaration ===
RESULT G2c codeptr pass 1 rc=1
YB01.v       17 code (12 function starts, 3 return pcs, 2 other instruction starts),  415 data, 99 at or above the image top 0x5f3970, 6 FINDINGS: 0x10800, 0x20000, 0x71c00, 0x100000, 0x161200, 0x38e000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB01.v: 6 STALE (0x10800, 0x20000, 0x71c00, 0x100000, 0x161200, 0x38e000), 1 donor-file li
YB03.v       21 code (9 function starts, 10 return pcs, 2 other instruction starts),  303 data, 64 at or above the image top 0x5f3970, 9 FINDINGS: 0x10101, 0x10800, 0x1ffff, 0x445c0, 0x71c00, 0x100000, 0x100018, 0x38e000, 0x3fffff [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB03.v: 9 STALE (0x10101, 0x10800, 0x1ffff, 0x445c0, 0x71c00, 
YB05.v       37 code (4 function starts, 22 return pcs, 11 other instruction starts),    4 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB05.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YB12.v       25 code (8 function starts, 0 return pcs, 17 other instruction starts),    5 data, 2 at or above the image top 0x5f3970, 1 FINDINGS: 0x55c000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB12.v: 1 STALE (0x55c000), 2 donor-file literals with the same meaning in both images]
YB13.v        1 code (0 function starts, 0 return pcs, 1 other instruction starts),    8 data, 1 at or above the image top 0x5f3970, 1 FINDINGS: 0x55c000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB13.v: 1 STALE (0x55c000), 1 donor-file literals with the same meaning in both images]
YB1h.v        2 code (0 function starts, 0 return pcs, 1 other instruction starts),    8 data, 7 at or above the image top 0x5f3970, 2 FINDINGS: 0x158593, 0x55c000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1h.v: 2 STALE (0x158593, 0x55c000), 1 donor-file literals with the same meaning in both images]
YB1k.v       49 code (1 function starts, 0 return pcs, 46 other instruction starts),    6 data, 43 at or above the image top 0x5f3970, 6 FINDINGS: 0x155593, 0x155793, 0x255513, 0x255793, 0x455593, 0x455793 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1k.v: 6 STALE (0x155593, 0x155793, 0x255513, 0x255793, 0x455593, 0x455793), 0 donor-f
YB1l.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1m.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1v.v        2 code (2 function starts, 0 return pcs, 0 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1v.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YCej.v       21 code (1 function starts, 14 return pcs, 6 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YCej.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YD1k.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   25 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1k.v: 0 STALE (-), 5 donor-file literals with the same meaning in both images]
YD1y.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   13 data, 1 at or above the image top 0x5f3970, 1 FINDINGS: 0x3fffff [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1y.v: 1 STALE (0x3fffff), 1 donor-file literals with the same meaning in both images]
YD2i.v        2 code (1 function starts, 1 return pcs, 0 other instruction starts),    5 data, 5 at or above the image top 0x5f3970, 2 FINDINGS: 0x10800, 0x3fffff [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2i.v: 2 STALE (0x10800, 0x3fffff), 1 donor-file literals with the same meaning in both images]
YD2j.v        3 code (3 function starts, 0 return pcs, 0 other instruction starts),  109 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2j.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YE23.v        9 code (7 function starts, 2 return pcs, 0 other instruction starts),   44 data, 5 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE23.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YE37.v        1 code (1 function starts, 0 return pcs, 0 other instruction starts),   24 data, 9 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE37.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YE3i.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   26 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE3i.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YF0m.v       28 code (15 function starts, 11 return pcs, 2 other instruction starts),  230 data, 61 at or above the image top 0x5f3970, 3 FINDINGS: 0x10101, 0x10800, 0x100000 [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YF0m.v: 3 STALE (0x10101, 0x10800, 0x100000), 7 donor-file literals with the same meaning in both images]
codeptr: UNMEASURED: 2 of 19 file(s) hold no address literal in range
RESULT G2e declaration evidence rc=0
=== G2d PASS 2: the same + 38 declaration arguments (codeptr-decl.sh) ===
RESULT G2d codeptr pass 2 rc=2
YB01.v       15 code (12 function starts, 3 return pcs, 0 other instruction starts),  407 data, 99 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB01.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x520
YB03.v       19 code (9 function starts, 10 return pcs, 0 other instruction starts),  297 data, 64 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB03.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x520
YB05.v       37 code (4 function starts, 22 return pcs, 11 other instruction starts),    4 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB05.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YB12.v       25 code (8 function starts, 0 return pcs, 17 other instruction starts),    4 data, 2 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB12.v: 0 STALE (-), 2 donor-file literals with the same meaning in both images]
YB13.v        1 code (0 function starts, 0 return pcs, 1 other instruction starts),    7 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB13.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YB1h.v        2 code (0 function starts, 0 return pcs, 1 other instruction starts),    6 data, 7 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1h.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YB1k.v       49 code (1 function starts, 0 return pcs, 46 other instruction starts),    0 data, 43 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1k.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YB1l.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1m.v     UNMEASURED: no address literal in [0x10000, 0x5f3970) - nothing checked
YB1v.v        2 code (2 function starts, 0 return pcs, 0 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YB1v.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YCej.v       21 code (1 function starts, 14 return pcs, 6 other instruction starts),    0 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YCej.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YD1k.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   25 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1k.v: 0 STALE (-), 5 donor-file literals with the same meaning in both images]
YD1y.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   12 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD1y.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YD2i.v        2 code (1 function starts, 1 return pcs, 0 other instruction starts),    4 data, 5 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2i.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x520 (
YD2j.v        3 code (3 function starts, 0 return pcs, 0 other instruction starts),  109 data, 1 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YD2j.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YE23.v        9 code (7 function starts, 2 return pcs, 0 other instruction starts),   44 data, 5 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE23.v: 0 STALE (-), 0 donor-file literals with the same meaning in both images]
YE37.v        1 code (1 function starts, 0 return pcs, 0 other instruction starts),   24 data, 9 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE37.v: 0 STALE (-), 1 donor-file literals with the same meaning in both images]
YE3i.v        0 code (0 function starts, 0 return pcs, 0 other instruction starts),   26 data, 0 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YE3i.v: 0 STALE (-), 9 donor-file literals with the same meaning in both images]
YF0m.v       28 code (15 function starts, 11 return pcs, 2 other instruction starts),  228 data, 61 at or above the image top 0x5f3970, 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan, donor file $DLIBC/YF0m.v: 0 STALE (-), DECLARED the same in both images: 0x10800 (SYMBOL __global_pointer$ (gp) of fuzz_uci B (twin .symtab) and cgif B .rodata+0x52
codeptr: UNMEASURED: 2 of 19 file(s) hold no address literal in range
RESULT G3 port_addr_check CONTROL cgif A->B rc=0
DIFFERENT-SYMBOL	12	FLAG
RESULT G3 port_addr_check cgif B -> uci B rc=0
DIFFERENT-SYMBOL	147	kernel 11	FLAG
RESULT G3 pac_table rc=0
| file | numerals (uci / ctl) | uci B flags | control flags (cgif A -> B) | flag classes only in uci B |
| YB01.v | 17633 / 17631 | 1581: DIFFERENT-SYMBOL 79, GEOMETRY-CHANGED 24, KIND-CHANGED 3, NON-ADDRESS-CHANGED 1418, UNPAIRED-PORTED 2, UNPAIRED-SOURCE 54, UNRESOLVED 1 | 325: DIFFERENT-SYMBOL 12, KIND-CHANGED 3, NON-ADDRESS-CHANGED 307, UNRESOLVED 3 | GEOMETRY-CHANGED, UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YB03.v | 2886 / 2886 | 200: DIFFERENT-SYMBOL 33, KIND-CHANGED 1, NON-ADDRESS-CHANGED 164, UNPAIRED-SOURCE 2 | 160: KIND-CHANGED 1, NON-ADDRESS-CHANGED 159 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YCej.v | 1690 / 1678 | 1670: DIFFERENT-SYMBOL 14, NO-COUNTERPART 3, UNPAIRED-PORTED 12, UNPAIRED-SOURCE 1640, UNRESOLVED 1 | 1128: NON-ADDRESS-CHANGED 285, UNPAIRED-PORTED 69, UNRESOLVED 774 | DIFFERENT-SYMBOL, NO-COUNTERPART, UNPAIRED-SOURCE |
| YD1k.v | 206 / 206 | 28: DIFFERENT-SYMBOL 7, KIND-CHANGED 2, NON-ADDRESS-CHANGED 14, UNPAIRED-SOURCE 4, UNRESOLVED 1 | 15: KIND-CHANGED 1, NON-ADDRESS-CHANGED 14 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE, UNRESOLVED |
| YD2j.v | 325 / 325 | 67: DIFFERENT-SYMBOL 1, KIND-CHANGED 2, NON-ADDRESS-CHANGED 48, UNPAIRED-SOURCE 12, UNRESOLVED 4 | 53: KIND-CHANGED 2, NON-ADDRESS-CHANGED 48, UNRESOLVED 3 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE23.v | 1463 / 1463 | 28: DIFFERENT-SYMBOL 1, KIND-CHANGED 1, NON-ADDRESS-CHANGED 18, UNPAIRED-SOURCE 4, UNRESOLVED 4 | 25: KIND-CHANGED 3, NON-ADDRESS-CHANGED 18, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE37.v | 287 / 281 | 96: DIFFERENT-SYMBOL 5, IDENT-MISMATCH 4, KIND-CHANGED 1, NON-ADDRESS-CHANGED 9, UNPAIRED-PORTED 6, UNPAIRED-SOURCE 71 | 12: IDENT-MISMATCH 4, KIND-CHANGED 6, NON-ADDRESS-CHANGED 2 | DIFFERENT-SYMBOL, UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YE3i.v | 50 / 50 | 14: DIFFERENT-SYMBOL 2, KIND-CHANGED 3, NON-ADDRESS-CHANGED 1, UNPAIRED-SOURCE 6, UNRESOLVED 2 | 9: KIND-CHANGED 1, NON-ADDRESS-CHANGED 4, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YF0m.v | 711 / 664 | 213: DIFFERENT-SYMBOL 5, KIND-CHANGED 12, NO-COUNTERPART 3, NON-ADDRESS-CHANGED 16, STALE-DONOR-CODE-POINTER 3, UNPAIRED-PORTED 47, UNPAIRED-SOURCE 70, UNRESOLVED 57 | 86: NON-ADDRESS-CHANGED 8, UNRESOLVED 78 | DIFFERENT-SYMBOL, KIND-CHANGED, NO-COUNTERPART, STALE-DONOR-CODE-POINTER, UNPAIRED-PORTED, UNPAIRED-SOURCE |
uci B verdicts: {'DIFFERENT-SYMBOL': 147, 'GEOMETRY-CHANGED': 24, 'IDENT-MISMATCH': 4, 'IMAGE-EXTENT-SAME': 29, 'INSN-SAME': 114, 'KIND-CHANGED': 26, 'NO-COUNTERPART': 6, 'NON-ADDRESS-CHANGED': 1691, 'NON-ADDRESS-SAME': 18283, 'ROUND-CONSTANT-SAME': 30, 'SAME-CONTENT': 6, 'SAME-GEOMETRY': 3936, 'SAME-SYMBOL': 2329, 'STALE-DONOR-CODE-POINTER': 3, 'UNPAIRED-PORTED': 68, 'UNPAIRED-SOURCE': 1889, 'UNR
control verdicts: {'DIFFERENT-SYMBOL': 12, 'GEOMETRY-CHANGED': 1, 'IDENT-MISMATCH': 4, 'IMAGE-EXTENT-SAME': 32, 'INSN-SAME': 114, 'KIND-CHANGED': 17, 'NON-ADDRESS-CHANGED': 860, 'NON-ADDRESS-SAME': 19556, 'ROUND-CONSTANT-SAME': 82, 'SAME-CONTENT': 41, 'SAME-GEOMETRY': 3966, 'SAME-SYMBOL': 2967, 'UNPAIRED-PORTED': 69, 'UNRESOLVED': 867}
uci B rows of the classes STALE-DONOR-CODE-POINTER / NO-COUNTERPART / IDENT-MISMATCH / GEOMETRY-CHANGED (distinct by file, definition, source value, ported value; count of rows):
  IDENT-MISMATCH x1  YE37.v Lemma zi8_14ea00  src YE37.v:176 0x14ea00 -> dst line 169 0x14ea00  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x168c0[data] in the donor but __sanitizer::useCounts+0x1da40 in the target; same symbol __sanitizer::useCounts, offset 0x168c0 vs 0x1da40; expected 0x14
  IDENT-MISMATCH x1  YE37.v Lemma zi8_14f970  src YE37.v:177 0x14f970 -> dst line 170 0x14f970  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x17830[data] in the donor but __sanitizer::useCounts+0x1e9b0 in the target; same symbol __sanitizer::useCounts, offset 0x17830 vs 0x1e9b0; expected 0x14
  IDENT-MISMATCH x1  YE37.v Theorem x2_realizes / sentence 35  src YE37.v:204 0x14ea00 -> dst line 197 0x14ea00  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x168c0[data] in the donor but __sanitizer::useCounts+0x1da40 in the target; same symbol __sanitizer::useCounts, offset 0x168c0 vs 0x1da40; expected 0x14
  IDENT-MISMATCH x1  YE37.v Theorem x2_realizes / sentence 44  src YE37.v:208 0x14f970 -> dst line 201 0x14f970  | value unchanged (a copied literal?); SAME-VALUE-DIFFERENT-OBJECT: the value denotes __sanitizer::useCounts+0x17830[data] in the donor but __sanitizer::useCounts+0x1e9b0 in the target; same symbol __sanitizer::useCounts, offset 0x17830 vs 0x1e9b0; expected 0x14
  16f8a030c869 has no GENERATOR-FILL class (added in 0767e70e074a); rows with that verdict: control 0, uci B 0
RESULT G3b port_addr_check cb0e CONTROL cgif A->B rc=0
GENERATOR-FILL	506	REPORTED
DIFFERENT-SYMBOL	12	FLAG
FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
RESULT G3b port_addr_check cb0e cgif B -> uci B rc=0
GENERATOR-FILL	45	kernel 37	REPORTED
DIFFERENT-SYMBOL	147	kernel 11	FLAG
FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
RESULT G3b pac_table (cb0e) rc=0
| file | numerals (uci / ctl) | uci B flags | control flags (cgif A -> B) | flag classes only in uci B |
| YB01.v | 17633 / 17631 | 1271: DIFFERENT-SYMBOL 79, KIND-CHANGED 3, NON-ADDRESS-CHANGED 1132, UNPAIRED-PORTED 2, UNPAIRED-SOURCE 54, UNRESOLVED 1 | 38: DIFFERENT-SYMBOL 12, KIND-CHANGED 3, NON-ADDRESS-CHANGED 19, UNRESOLVED 4 | UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YB03.v | 2886 / 2886 | 43: DIFFERENT-SYMBOL 33, KIND-CHANGED 1, NON-ADDRESS-CHANGED 7, UNPAIRED-SOURCE 2 | 2: KIND-CHANGED 1, NON-ADDRESS-CHANGED 1 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YCej.v | 1690 / 1678 | 1670: DIFFERENT-SYMBOL 14, NO-COUNTERPART 3, UNPAIRED-PORTED 12, UNPAIRED-SOURCE 1640, UNRESOLVED 1 | 565: NON-ADDRESS-CHANGED 128, UNPAIRED-PORTED 69, UNRESOLVED 368 | DIFFERENT-SYMBOL, NO-COUNTERPART, UNPAIRED-SOURCE |
| YD1k.v | 206 / 206 | 26: DIFFERENT-SYMBOL 7, KIND-CHANGED 2, NON-ADDRESS-CHANGED 12, UNPAIRED-SOURCE 4, UNRESOLVED 1 | 13: KIND-CHANGED 1, NON-ADDRESS-CHANGED 12 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE, UNRESOLVED |
| YD2j.v | 325 / 325 | 28: DIFFERENT-SYMBOL 1, KIND-CHANGED 2, NON-ADDRESS-CHANGED 9, UNPAIRED-SOURCE 12, UNRESOLVED 4 | 14: KIND-CHANGED 2, NON-ADDRESS-CHANGED 9, UNRESOLVED 3 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE23.v | 1463 / 1463 | 10: DIFFERENT-SYMBOL 1, KIND-CHANGED 1, UNPAIRED-SOURCE 4, UNRESOLVED 4 | 7: KIND-CHANGED 3, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YE37.v | 287 / 281 | 92: DIFFERENT-SYMBOL 5, KIND-CHANGED 1, NON-ADDRESS-CHANGED 9, UNPAIRED-PORTED 6, UNPAIRED-SOURCE 71 | 9: KIND-CHANGED 6, NON-ADDRESS-CHANGED 2, UNRESOLVED 1 | DIFFERENT-SYMBOL, UNPAIRED-PORTED, UNPAIRED-SOURCE |
| YE3i.v | 50 / 50 | 13: DIFFERENT-SYMBOL 2, KIND-CHANGED 3, UNPAIRED-SOURCE 6, UNRESOLVED 2 | 8: KIND-CHANGED 1, NON-ADDRESS-CHANGED 3, UNRESOLVED 4 | DIFFERENT-SYMBOL, UNPAIRED-SOURCE |
| YF0m.v | 711 / 664 | 168: DIFFERENT-SYMBOL 5, KIND-CHANGED 6, NON-ADDRESS-CHANGED 8, UNPAIRED-PORTED 39, UNPAIRED-SOURCE 70, UNRESOLVED 40 | 86: NON-ADDRESS-CHANGED 7, UNRESOLVED 79 | DIFFERENT-SYMBOL, KIND-CHANGED, UNPAIRED-PORTED, UNPAIRED-SOURCE |
uci B verdicts: {'DIFFERENT-SYMBOL': 147, 'GENERATOR-FILL': 45, 'IDENT-NAME': 4, 'IMAGE-EXTENT-SAME': 13, 'INSN-SAME': 114, 'KIND-CHANGED': 19, 'NO-COUNTERPART': 3, 'NON-ADDRESS-CHANGED': 1180, 'NON-ADDRESS-SAME': 18366, 'ROUND-CONSTANT-SAME': 30, 'SAME-CONTENT': 6, 'SAME-GEOMETRY': 3938, 'SAME-SYMBOL': 2788, 'UNPAIRED-PORTED': 60, 'UNPAIRED-SOURCE': 1889, 'UNRESOLVED': 54}
control verdicts: {'DIFFERENT-SYMBOL': 12, 'GENERATOR-FILL': 506, 'GEOMETRY-CHANGED': 1, 'IDENT-NAME': 4, 'IMAGE-EXTENT-SAME': 32, 'INSN-SAME': 114, 'KIND-CHANGED': 17, 'NON-ADDRESS-CHANGED': 195, 'NON-ADDRESS-SAME': 19640, 'ROUND-CONSTANT-SAME': 82, 'SAME-CONTENT': 41, 'SAME-GEOMETRY': 3888, 'SAME-SYMBOL': 3523, 'UNPAIRED-PORTED': 69, 'UNRESOLVED': 464}
uci B rows of the classes STALE-DONOR-CODE-POINTER / NO-COUNTERPART / IDENT-MISMATCH / GEOMETRY-CHANGED (distinct by file, definition, source value, ported value; count of rows):
=== G3c GENERATOR-FILL triage (tools/pac_fill.py): every row a measured reason; CONTROL cgif A -> B first ===
RESULT G3c fill triage CONTROL cgif A->B rc=1
GENERATOR-FILL rows: 506, on 236 ported lines: {'YCej.v': 236}
  UNEXPLAINED YCej.v:30 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:32 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:34 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:36 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:38 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:46 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:48 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:50 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:52 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:85 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:87 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:89 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:91 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:94 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:96 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:98 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:100 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:102 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:104 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:106 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:108 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:110 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:112 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:114 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:116 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:118 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:120 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:122 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:124 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:129 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:134 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:136 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:138 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:140 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:146 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:148 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:150 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:152 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:154 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:156 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:161 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:163 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:165 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:167 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:169 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:171 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:173 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:175 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:177 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:179 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:187 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:189 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:191 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:193 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:195 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:197 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:205 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:207 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:209 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:211 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:217 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:220 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:222 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:225 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:227 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:230 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:232 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:234 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:236 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:238 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:240 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:243 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:245 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:247 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:249 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:252 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:253 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:255 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:257 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:258 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:260 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:262 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:263 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:265 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:267 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:268 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:270 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:272 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:273 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:275 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:277 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:278 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:280 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:282 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:283 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:285 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:287 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:288 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:290 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:292 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:293 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:295 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:297 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:298 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:300 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:302 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:303 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:305 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:307 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:308 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:310 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:312 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:313 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:315 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:317 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:318 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:320 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:322 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:323 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:325 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:327 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:328 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:330 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:332 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:333 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:335 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:337 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:338 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:340 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:342 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:343 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:345 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:351 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:355 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:357 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:361 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:363 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:381 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:383 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:385 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:387 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:389 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:391 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:393 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:395 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:397 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:399 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:401 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:403 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:405 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:407 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:409 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:411 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:413 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:415 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:417 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:419 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:421 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:423 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:425 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:427 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:429 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:431 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:432 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:434 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:436 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:437 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:439 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:441 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:442 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:444 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:446 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:447 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:449 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:451 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:452 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:454 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:456 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:457 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:459 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:461 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:462 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:464 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:466 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:467 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:469 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:471 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:472 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:474 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:476 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:477 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:479 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:481 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:489 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:491 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:493 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:495 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:497 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:499 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:501 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:503 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:505 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:507 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:509 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:511 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:513 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:515 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:517 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:519 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:521 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:522 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:524 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:526 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:527 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:529 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:531 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:532 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:534 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:536 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:537 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:539 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:541 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:542 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:544 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:546 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:547 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:549 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:551 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:552 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:554 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:556 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:557 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:559 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:561 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:562 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
  UNEXPLAINED YCej.v:564 (not a Tfib_const_abs row of YF0m.v): ['index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte', 'index-preserving duplicate (positional): the ported row repeats an earlier porte']
pac_fill: 236 of 236 ported lines UNEXPLAINED (506 GENERATOR-FILL rows)
RESULT G3c fill triage uci B rc=0
GENERATOR-FILL rows: 45, on 24 ported lines: {'YF0m.v': 24}
  YF0m.v:126 row 86 `z8 (ANum 0x97e10) 0xfffffffffffff800  ;` not an af0m FILL: unit image word at 0x97e10 (.got) = 0xfffffffffffff800; donor slot 0x9ef08 holds 0xfffffffffffff800 in cgif's image (.got), the same link-time word, a tp offset (negative), not an address; other unit rows with this cell or value: lines [] -> ACCEPTED
pac_fill: 0 of 24 ported lines UNEXPLAINED (45 GENERATOR-FILL rows)
=== G4 CONTROL FIRST: planted copy (plant_uciB.py), .text end + 4 = 0x95b94 in CODE cells must be flagged, in a DATA cell not ===
RESULT G4 plant rc=0
planted P1-CODE YF0m.v:105  z8 (ANum 0x98f80) 0x90458 -> z8 (ANum 0x98f80) 0x95b94
planted P2-CODE YF0m.v:22  [[0x51a24; 0x7ee9c] -> [[0x95b94; 0x7ee9c]
planted P3-CODE YB12.v:15  x_memset := 0x9085c -> x_memset := 0x95b94
planted P4-CODE YB01.v:22  SS 519752 [ELit 0; ELit 550212; -> SS 519752 [ELit 0; ELit 613268;
planted D1-DATA YF0m.v:74  z8 (ANum 0x9c8f8) 0x100ffffffff -> z8 (ANum 0x9c8f8) 0x95b94
RESULT G4 classify PLANTED (must be rc 1) rc=1
== uciB.planted: image fuzz_uci.asan-ubsan sha256 a1b86e424add; .text [0x2fbf0, 0x95b90) = 104424 words; image [0x10000, 0x5f4000); objdump source = twin: True
   files $UCIB_GATEWORK/classify/planted: 23745 literals, 4185 >= .text end (1808 inside the image, 2377 past it)
   FINDINGS (CODE role, value not in .text): 4 (of them >= .text end: 4)
  PLANTED CONTROL: PASS
RESULT G4 planted control verdict rc=0
RESULT G4 classify uciB rc=0
   FINDINGS (CODE role, value not in .text): 0 (of them >= .text end: 0)
RESULT G4 coverage report rc=0
RESULT G7a pins check rc=0
RESULT G7b stamp YB01 (file Read-from line: line 5; stamp writes it at line 10, text EQUAL; every other line EQUAL) rc=0
RESULT G7b stamp YB03 (file Read-from line: line 5; stamp writes it at line 8, text EQUAL; every other line EQUAL) rc=0
RESULT G7b stamp YB05 (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB12 (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YB12.v atable image fields (key = field): 3 rows, exactly the set fuzz_uci.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS YB12.v stops_more (key = self-loop site): 13 rows, exactly the set fuzz_uci.asan-ubsan (13 self-loops, in .text) defines
RESULT G7b stamp YB13 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YB1h (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB1k (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
RESULT G7b stamp YB1l (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YB1m (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YB1v (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YCej (file Read-from line: line 6; stamp writes it at line 6, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD1k (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD1y (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YD2i (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YD2j (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
PASS YD2j.v regions (key = region name): 31 rows, exactly the set the region definitions of YD2j.v defines
PASS YD2j.v anchor roles (key = role, present iff the image defines its object): 16 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
RESULT G7b stamp YE23 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YE37 (file Read-from line: line 5; stamp writes it at line 5, text DIFFERENT (the same pin + twin sha256 a1b86e424add / 8d07ffcf5948, other wording); every other line EQUAL) rc=0
RESULT G7b stamp YE3i (file Read-from line: line 5; stamp writes it at line 5, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=0
RESULT G7b stamp YF0m (file Read-from line: line 6; stamp writes it at line 6, text EQUAL; every other line EQUAL; copy BYTE-EQUAL) rc=2
PASS YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
pins: NOT STAMPED $UCIB_GATEWORK/stamp/YF0m.v: an AF0m / YF0m is checked with the OTHER image's table (keyset realset: the __interception::real_* rows of A and B must agree), and this run has no --pair: the REAL rows are UNMEASURED. Give --pair <the other image's F0m> --pair-syms <its symbol table>
RESULT G7c stamp YF0m --pair (stamped copy DIFFERS; the same multiset of lines: True (only line order in the header moves)) rc=0
PASS YF0m.pair.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS YF0m.pair.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS YF0m.pair.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE YF0m.pair.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
PASS REAL rows, A == B (key = N of __interception::real_N): 14 rows, exactly the set A (fuzz_uci.asan) defines
PASS donor REAL rows, A == B (each keyed by the donor image's own symbol table): 16 rows, exactly the set donor A (cgif_file_fuzzer.asan.nm) defines
PASS REAL rows, donor subset of ours (A): donor 16 ['__tls_get_addr', 'atoll', 'bcmp', 'fclose', 'fflush', 'fopen', 'fwrite', 'memchr', 'memcmp', 'memcpy', 'memset', 'read', 'strchr', 'strnlen', 'vfprintf', 'vprintf']; 13 of them this image defines real_N for, all present; not in this image (no real
PASS REAL rows, donor subset of ours (B): donor 16 ['__tls_get_addr', 'atoll', 'bcmp', 'fclose', 'fflush', 'fopen', 'fwrite', 'memchr', 'memcmp', 'memcpy', 'memset', 'read', 'strchr', 'strnlen', 'vfprintf', 'vprintf']; 13 of them this image defines real_N for, all present; not in this image (no real
RESULT G7d emitcheck rc=0
RESULT G7e keyset CONTROL cgif released YB12 rc=1
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YB12.v atable image fields (key = field): 3 rows, exactly the set cgif_file_fuzzer.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS cgif/YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the names of record cgif/YB1w.v defines
keyset: REFUSED cgif/YB12.v stops_more (key = self-loop site)
keyset: REFUSED
RESULT G7e keyset CONTROL cgif released YF0m rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 35 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 5 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) and the PT_LOAD hull defines
PASS cgif/YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 4 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 24 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
PASS cgif/YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set cgif_file_fuzzer.asan-ubsan asan_globals (3 descriptors at 0xa2ae0) defines
NOTE cgif/YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
keyset: PASS for the per-file row sets (measured: 1 file(s), 5 sub-checks, 70 rows); REAL() rows of 1 AF0m / YF0m UNMEASURED (single files: run `keyset.py realset` on the A+B pair)
RESULT G7e keyset CONTROL cgif released YD2j rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YD2j.v regions (key = region name): 33 rows, exactly the set the region definitions of $UCIB_GATEWORK/in/cgif/YD2j.v defines
UNMEASURED cgif/YD2j.v: no twin, so the anchor roles (gen_ad2.ANCHOR_NAMES) are not checked by symbol
keyset: PASS for the measured sub-checks (measured: 1 file(s), 1 sub-checks, 33 rows); UNMEASURED sub-checks (see the UNMEASURED lines) in: cgif/YD2j.v
RESULT G7e keyset CONTROL cgif released YB1k rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS cgif/YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the names of record cgif/YB1w.v defines
keyset: PASS (measured: 1 file(s), 1 sub-checks, 3 rows)
RESULT G7e keyset CONTROL cgif YB12 (atable re-emitted) rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS $WK/ctl/YB12.cgif.v atable image fields (key = field): 3 rows, exactly the set cgif_file_fuzzer.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS $WK/ctl/YB12.cgif.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the names of record cgif/YB1w.v defines
PASS $WK/ctl/YB12.cgif.v stops_more (key = self-loop site): 13 rows, exactly the set cgif_file_fuzzer.asan-ubsan (13 self-loops, in .text) defines
keyset: PASS (measured: 1 file(s), 3 sub-checks, 27 rows)
RESULT G7e keyset uciB rc=0
keyset: self-test 7 known answers (kind by name and contents; a keyed table under an unkeyed name is UNMEASURED); 14 known answers (stops gate 5, self-loop decode 9)
PASS gen/YB12.v atable image fields (key = field): 3 rows, exactly the set fuzz_uci.asan-ubsan (e_entry, PT_LOAD hull) defines
PASS gen/YB12.v atable x_* fields (key = field, row = the symbol it names): 11 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS gen/YB12.v stops_more (key = self-loop site): 13 rows, exactly the set fuzz_uci.asan-ubsan (13 self-loops, in .text) defines
PASS gen/YF0m.v Tfib_const_shadow (key = shadow cell of a descriptor's redzone or of the metadata): 11 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v Tfib_zero_shadow (key = fragment start; the hull cut at every stated shadow granule): 3 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) and the PT_LOAD hull defines
PASS gen/YF0m.v Tfib_owned_static descriptor rows (key = global / descriptor array): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v Tfib_const_abs descriptor words (key = 8-byte word of asan_globals): 8 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
PASS gen/YF0m.v depot-trace rows (present iff the image registers a descriptor): 2 rows, exactly the set fuzz_uci.asan-ubsan asan_globals (1 descriptors at 0x9b9d0) defines
NOTE gen/YF0m.v REAL() interceptor rows: UNMEASURED by this single-file check - they are keyed against the other image's table by `keyset.py realset` / `pins.py stamp --pair`
PASS gen/YD2j.v regions (key = region name): 31 rows, exactly the set the region definitions of $UCIB_GATEWORK/in/gen/YD2j.v defines
PASS gen/YD2j.v anchor roles (key = role, present iff the image defines its object): 16 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
PASS gen/YB1k.v sealed-top text range (key = GetMaxUserVirtualAddress): 3 rows, exactly the set the twin fuzz_uci/fuzz_uci.asan-ubsan defines
keyset: PASS for the per-file row sets (measured: 4 file(s), 11 sub-checks, 103 rows); REAL() rows of 1 AF0m / YF0m UNMEASURED (single files: run `keyset.py realset` on the A+B pair)
RESULT G8 ifchk CONTROL cgif B rc=0
ifchk: 267 cells (sym 22, abs 210, shadow 35) x 50 states: 13350 = stated, 0 different, 0 undetermined (None), 0 inexpressible
RESULT G8 ifchk no-states (want 2) rc=2
ifchk: REFUSED: no states named HS_tfib_N in $UCIB_GATEWORK/ctl/empty.YB01.v
RESULT G8 ifchk --nholes 49 (want 2) rc=2
ifchk: REFUSED: $UCIB_GATEWORK/in/raw/YB01.v holds 50 hand-off states, expected 49 (--nholes); a check over 50 states proves nothing about the others
planted: 'z8 (ANum 0x130c28) 0x1 ' -> 'z8 (ANum 0x130c28) 0x2 '
RESULT G8 plant rc=0
RESULT G8 ifchk PLANTED (want 1) rc=1
RESULT G8 ifchk uciB rc=0
ifchk: 250 cells (sym 22, abs 217, shadow 11) x 50 states: 12500 = stated, 0 different, 0 undetermined (None), 0 inexpressible
=== G11a gen_exitB.py --af0m WK/raw/YF0m.v (its own controls C1.. run first inside; rodata_chk / cellr / shbyte_chk / DRVW_not_owned) ===
RESULT G11a gen_exitB --af0m rc=1
cgif EQUAL
RESULT G11b XW2 cgif rc=0
uciB EQUAL
RESULT G11b XW2 uciB rc=0
```

## Earlier: G11 re-run with a9's control texts read from its core commit

```
=== G11a gen_exitB.py --af0m WK/raw/YF0m.v (its own controls C1.. run first inside; rodata_chk / cellr / shbyte_chk / DRVW_not_owned) ===
RESULT G11a gen_exitB --af0m rc=0
  C3b decode B   __asan_unregister_globals 0x3ef00: addi a1,a0,1 @0x3f0a8; bgeu a1,s2 @0x3f0ac -> 0x3f170 `sb zero, 0(a0)`; s2 = 2 @['0x3f080'] (capstone 5.0.7): PASS
  C3b fuzz_uci B __asan_unregister_globals 0x3e9d8: addi a1,a0,1 @0x3eb80; bgeu a1,s2 @0x3eb84 -> 0x3ec48 `sb zero, 0(a0)`; s2 = 2 @['0x3eb58'] (capstone 5.0.7): PASS
     F_STDOUT     YE23 0x9b7c8    unit 0x9b7c8    PASS
     F_STDERR     YE23 0x9b6d8    unit 0x9b6d8    PASS
     A_GOT_canary YE23 0x97db0    unit 0x97db0    PASS
     A_canary     YE23 0x5f20d0   unit 0x5f20d0   PASS
     A_GOT_CANARY (YE22) 0x97db0 = A_GOT_canary: PASS
     [0x9b690, 0x9b9d0) = oft_arg0 .. asan_globals PASS
     [0x9ba48, 0x9ba90) = __do_init.__initialized .. __do_fini.__finalized PASS
     [0x5d1750, 0x5d2038) = target_run.initialized .. builtin_tls+112 PASS
     [0x5f20e0, 0x5f2300) = finished_atexit .. exit.exit_lock PASS
     X1 YD1y 0xa2bc8   -> 0x9ba48   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YD1y 0xa2c10   -> 0x9ba90   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YD1y 0x5d88d0  -> 0x5d1750  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YD1y 0x5f9260  -> 0x5f20e0  cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YD1y 0x5f9480  -> 0x5f2300  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9e1d8   -> 0x970f8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9e1e0   -> 0x97100   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9e1e8   -> 0x97108   cgif refs 77 (moved 77) == uci refs 77: PASS
     X1 YE23 0x9eea8   -> 0x97db0   cgif refs 51 (moved 50, not identical code ['0x92c58']) == uci refs 50: PASS
     X1 YE23 0x9eed8   -> 0x97de0   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9eee0   -> 0x97de8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x9eee8   -> 0x97df0   cgif refs 3 (moved 3) == uci refs 3: PASS
     X1 YE23 0xa27e8   -> 0x9b6d8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0xa28d0   -> 0x9b7c0   cgif refs 4 (moved 4) == uci refs 4: PASS
     X1 YE23 0xa28d8   -> 0x9b7c8   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0xa29c0   -> 0x9b8b0   cgif refs 4 (moved 4) == uci refs 4: PASS
     X1 YE23 0xa2ab0   -> 0x9b9a0   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0xa2ab8   -> 0x9b9a8   cgif refs 3 (moved 3) == uci refs 3: PASS
     X1 YE23 0xa2bc0   -> 0x9ba40   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0xa2bc8   -> 0x9ba48   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0xa2c10   -> 0x9ba90   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0x5d88d4  -> 0x5d1754  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x5f9260  -> 0x5f20e0  cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE23 0x5f9480  -> 0x5f2300  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x5f94a3  -> 0x5f2323  cgif refs 4 (moved 4) == uci refs 4: PASS
     X1 YE23 0x5f94a4  -> 0x5f2324  cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE23 0x5f9900  -> 0x5f2780  cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE37 0x103a0   -> 0x103a0   cgif refs 36 (moved 36) == uci refs 36: PASS
     X1 YE37 0x9e1e8   -> 0x97108   cgif refs 77 (moved 77) == uci refs 77: PASS
     X1 YE37 0x9ee98   -> 0x97da0   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE37 0xa0098   -> 0x98f88   cgif refs 2 (moved 1, not identical code ['0x51b3c']) == uci refs 1: PASS
     X1 YE37 0xa00d0   -> 0x98fc0   cgif refs 1 (moved 1) == uci refs 1: PASS
     X1 YE37 0xa2bc0   -> 0x9ba40   cgif refs 2 (moved 2) == uci refs 2: PASS
     X1 YE37 0xa5adc   -> 0x9e95c   cgif refs 3 (moved 3) == uci refs 3: PASS
     X1 YE37 0xa6f58   -> 0x9fdd8   cgif refs 8 (moved 8) == uci refs 8: PASS
     X1 YE37 0xa6f60   -> 0x9fde0   cgif refs 3 (moved 3) == uci refs 3: PASS
  --af0m $UCIB_GATEWORK/in/raw/YF0m.v: rodata_chk / cellr / shbyte_chk misses 0 []; DRVW_not_owned overlaps 0 []
PASS
  re-generated YE23.v BYTE-EQUAL to the exitdrv sub-lane's own output $UCIB_EXITWORK/out/YE23.v
  YE23.v: with every `From .. Require ..` sentence removed and TfibSyms -> UciSyms (the module-path / record rewrite), the re-generated (donor-namespace) text and WK/gen are EQUAL (1664 / 1664 non-blank lines)
  re-generated YD1y.v BYTE-EQUAL to the exitdrv sub-lane's own output $UCIB_EXITWORK/out/YD1y.v
  YD1y.v: with every `From .. Require ..` sentence removed and TfibSyms -> UciSyms (the module-path / record rewrite), the re-generated (donor-namespace) text and WK/gen are EQUAL (357 / 357 non-blank lines)
  re-generated YE37.v BYTE-EQUAL to the exitdrv sub-lane's own output $UCIB_EXITWORK/out/YE37.v
  YE37.v: with every `From .. Require ..` sentence removed and TfibSyms -> UciSyms (the module-path / record rewrite), the re-generated (donor-namespace) text and WK/gen are EQUAL (223 / 223 non-blank lines)
cgif EQUAL
RESULT G11b XW2 cgif rc=0
uciB EQUAL
RESULT G11b XW2 uciB rc=0
```
