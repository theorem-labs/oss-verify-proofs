# rt-reusable: value-gate triage of lib/Reusable and the relocated runtime files (plugin-hostd/fuzz_command)

rule 24: no function proved. No .v file was edited, nothing was built or committed.

Scope: every flagged row of the value gate (port_addr_check 3d2eee813cce, wrapper pac.sh) for
(1) the runtime files lib/A/Rt and lib/B/Rt whose header says they were copied, made or moved from a donor file, and
(2) lib/Reusable (run RU, already done: cgif_file_fuzzer root Y*.v -> our lib/Reusable/Y*.v, key B, 1957 flagged rows).
Trees: ours at plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record) (proofs/plugin-hostd/fuzz_command/lib), cgif_file_fuzzer at c8557374ad2e.

Result: **0 FINDINGs** (code: none, comment: none). 8252 flagged rows: 6735 OK by a measured rule, 1517
OK-out-of-scope (pre-port lib/Reusable files, owner ruling), 0 OPEN. No STOP-rule message was needed.

## Images (role, sha256 of pin / of the unstripped twin that gives the symbols)

| role | pin | twin |
|---|---|---|
| fuzz_command.asan (ours A) | c0661b96b5bd | 68db792d5fa7 |
| fuzz_command.asan-ubsan (ours B) | bbe55d24d096 | 658cefbe806b |
| fuzz_command.plain (ours P) | a20873dc7f0e | fbe3a48ad296 |
| cgif_file_fuzzer.asan / .asan-ubsan | 7093581aab04 / 1c29845fe605 | 488e39500746 / ce511d541cda |
| cgif_file_fuzzer.plain | 19dedd1bc682 | 6ab540c43108 |
| libreac fuzz_disco.asan | 5e39150dd810 | ec656cf105cb |
| libreac fuzz_grant.asan | c2c7559b29bd | 57c26f993615 |
| omx-clap-core fuzz_preset.asan | d83eb25dbf0d | f0d2e8d40c7e |

Each twin was checked against its pin (check_twin.py, work/twin-check.out): equal PT_LOAD headers, the only differing
loaded bytes are 5 bytes of the ELF header (e_shoff, e_shnum, e_shstrndx) and .note.gnu.build-id.
The fuzz_preset donor files name their own image in their text (FCimg.v and the gen_ae37 block of AE37.v: ELF sha256
f0d2e8d40c7e); that is the twin of pin d83eb25dbf0d, not the release pin 93f1eb0975d9. A first run with 93f1eb0975d9
(runs/superseded/RtPreset.image93f1eb) gave 23 DIFFERENT-SYMBOL rows in RtDtorExit.v; with the right image 1.

## Donors of the runtime files

find_donor.py ranks every version of a candidate donor path in the git history by changed lines against our file
(work/find/*.out). The headers name the first donor of a chain; the immediate donor is the closest version:

| our file (lib/A/Rt) | immediate donor (commit:path, unit-relative) | changed lines |
|---|---|---|
| Strnlen, StrnlenChk, StrnlenMusl | libreac/fuzz_disco lib/A/Rt/Strnlen.v (file sha256 286ff995df6d; donor not released), libreac/fuzz_disco lib/A/Rt/StrnlenChk.v (file sha256 359ec34cd1e1; donor not released), libreac/fuzz_disco lib/A/Rt/StrnlenMusl.v (file sha256 dffa10905023; donor not released) libreac/fuzz_disco lib/A/Rt/<same name> | 64 / 142 / 32 |
| Memchr, MemchrChk, MemchrMusl | libreac/fuzz_disco lib/A/Rt/Memchr.v (file sha256 ddef3ac73e5b; donor not released), libreac/fuzz_disco lib/A/Rt/MemchrChk.v (file sha256 d4a1f6879789; donor not released), libreac/fuzz_disco lib/A/Rt/MemchrMusl.v (file sha256 cce24fcd2d45; donor not released) libreac/fuzz_disco lib/A/Rt/<same name> | 58 / 138 / 14 |
| RtSM3 / RtSM3T | libreac/fuzz_disco lib/A/Rt/StackMalloc3.v (file sha256 e7016b729aac; donor not released) / b5cf457a8820 libreac/fuzz_disco lib/A/Rt/StackMalloc3(Tbl).v | 162 / 53 |
| RtStrcmp, ChkX, ChkY, Loop, Tbl | libreac/fuzz_grant lib/A/Rt/Strcmp.v (file sha256 2589fff6e1c6; donor not released), libreac/fuzz_grant lib/A/Rt/StrcmpChkX.v (file sha256 6ac978ef4ba9; donor not released), libreac/fuzz_grant lib/A/Rt/StrcmpChkY.v (file sha256 0b8c7ceea8b0; donor not released), libreac/fuzz_grant lib/A/Rt/StrcmpLoop.v (file sha256 df262e182c54; donor not released), libreac/fuzz_grant lib/A/Rt/StrcmpTbl.v (file sha256 cd94185b81fd; donor not released) libreac/fuzz_grant lib/A/Rt/Strcmp*.v | 89 .. 135 |
| RtSM5T / RtSMxA / RtDtorExit | omx-clap-core/fuzz_preset lib/A/FCm3r.v (file sha256 03046e7ffa94; donor not released) FCm3r.v / 4cda83dac850 FCxA.v / omx-clap-core/fuzz_preset lib/A/AE37.v (file sha256 1a56c76e4ad3; donor not released) AE37.v of omx-clap-core/fuzz_preset lib/A | 92 / 21 / 188 |
| RtSIstrlen, RtSM7Fm, RtDtorExit, Strnlen*, MemchrChk, RtD04d, RtD04n | cgif_file_fuzzer lib/A/AE38, AFfm, AE37, AE7d/e/f, AE6y, root YCbq.v (the headers' named donors) | 15 .. 255 |

StrcmpTbl: libreac/fuzz_grant lib/A/Rt/StrcmpTbl.v (file sha256 265250074da7; donor not released) ranks 54 lines, libreac/fuzz_grant lib/A/Rt/StrcmpTbl.v (file sha256 cd94185b81fd; donor not released) 57; only libreac/fuzz_grant lib/A/Rt/StrcmpTbl.v (file sha256 cd94185b81fd; donor not released) holds the sentence sc_rodata that our file
carries, so it is the donor (the run on the other version is not shipped).
lib/B/Rt files: their headers say "moved from this harness's lib/A/Rt/<file>" (the A-to-B address map), so their
donor is our lib/A/Rt twin (run RtRelay); the cgif root Y twins are run too (RtCgifB). donors.tsv lists every pair with
the sha256 of both files.

## Runs (runs/<NAME>/{full.tsv, summary.out, stderr.txt, rc})

| run | src -> dst, images | files paired | flagged |
|---|---|---|---|
| RtDisco | fuzz_disco lib/A/Rt -> our lib/A/Rt (8 files), disco.asan -> ours A | 8 | 103 |
| RtCgifA | cgif lib/A + YCbq -> our lib/A/Rt (9 files), cgif A -> ours A | 9 | 2743 |
| RtCgifB | cgif root Y + YCbq -> our lib/B/Rt (9 files), cgif B -> ours B | 9 | 2743 |
| RtGrant | fuzz_grant lib/A/Rt -> our lib/A/Rt (5 files), grant.asan -> ours A | 5 | 6 |
| RtPreset | fuzz_preset lib/A -> our lib/A/Rt (3 files), preset.asan d83eb25dbf0d -> ours A | 3 | 587 |
| RtRelay | our lib/A/Rt -> our lib/B/Rt (every twin), ours A -> ours B (key B both sides, as run RAB) | 132 | 113 |
| RUP | cgif root Y*.v -> our lib/Reusable/Y*.v, cgif plain -> ours plain (key P) | 400 | 1243 |

Donor-on-donor controls (one donor file, its own image on both sides): CtlDisco, CtlGrant, CtlPreset, CtlCmdA (ours A
as the relay's donor image), CtlCgifP (the plain pair): 0 flagged rows each. The cgif A/B pairs have the controls CA/CB
of record.

RtCgifA / RtCgifB pair our files with the donor's donor (two hops) or with a "made from" donor; most of their flags are
structure (UNPAIRED-SOURCE 1892 each, settled NO-PORTED-VALUE). Their two counts are equal because lib/B/Rt files are
lib/A/Rt files with B addresses (same numeral count, 12535).

## Triage

1. base_triage.py of record on each run (triage/<RUN>.{settled,open}.tsv): PROOF-STEP, KERNEL-FACT, NO-PORTED-VALUE.
2. triage_rtru.py (rules and their measurements in its docstring) judges every OPEN row; output triage-rows.tsv (all
   runs, a `# run NAME` line before each block; the run row's 16 columns + reason, measurement, result, finding_kind,
   new_value, read_by) and triage-rows.<RUN>.tsv. dst_file is relative to lib/Reusable (RU), lib/B/Rt (RtRelay, RtCgifB)
   or lib/A/Rt (other runs); src_file of RtCgifA/B/RtDisco/RtGrant/RtPreset is the donor file renamed to our name
   (donors.tsv maps it).
3. controls.tsv: each value-checking rule re-judged on its own rows with the value + 4 and with the donor's value.

### lib/Reusable (run RU, 1957 rows)

git log of the series head: 425 of lib/Reusable's 565 `.v` files were added 2026-10-27 in 84b1ffc6d7d (the plain
build's proofs; 421 directly in lib/Reusable, 4 in its sub-directories R/ and Z/); one of them, YK1a.v, was changed
2026-10-28 in f0e6eb38667 (its two `timeout 30` removed) and none of the 425 changed after that. 140 were added
2026-10-30 in 6b559e1f018 (5 of them, YD2n.v, YG00.v, YG03.v, YG06.v and YG0k.v, touched again in the commit after which the unit tree is plugin-hostd/fuzz_command tree (git tree 7676a6b422e5; internal record)). Only the 140
were added by the port. Owner ruling: pre-port rows are OUT-OF-SCOPE-PREPORT, result OK-out-of-scope, with the plain-image
measurement; lib/Reusable/YH03.v is covered by the YH03 procedure of record (adjacent.tsv, one line).

| family | rows | reasons |
|---|---|---|
| pre-port (plain build) | 1517 | OUT-OF-SCOPE-PREPORT. The plain-image run RUP judges 411 of the 822 open ones OK (RU read them against image B); YH03.v has 379 rows (adjacent.tsv). The 309 other open rows RUP still flags were measured: 291 numerals below the image base in sentences the donor lacks; YL0k.v's 6 numerals are plain-image cells (record.spill, the RELRO start, the .got slots around the &__stack_chk_guard slot); of the 12 changed constants, the Jal immediates equal the 21-bit field of their words, YN0g's hull equals fuzz_command.plain's base 0x10000 and page-rounded end 0x55000, and the others are model constants (alignments, powers of two, library table sizes). None is a value wrong for fuzz_command.plain, so adjacent.tsv carries no (b) row. |
| added by the port (140 files) | 440 | PROOF-STEP 159, NO-PORTED-VALUE 60, KERNEL-FACT 4, SIBLING-LINE 81, NEW-NONADDR 75, UNREAD-FOREIGN-TABLE 44, ABI-MMAP-FLAGS 8, PHDR-VADDR 5, ABI-HWCAP 2, MODEL-CHANGE-DOCUMENTED 2 |

Details of the 140 files added by the port: YK09.v's APC.ASAN / APC.BOTH tables (44 rows) are byte-equal to cgif's lines, describe an image with
end 0x671000 (neither cgif's 0x5fb000 nor ours 0x606000) and are read only by asan_init / both_init, which nothing reads
(by-use grep). YA01.v's mmap words decompose into MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED|MAP_NORESERVE|MAP_FIXED_NOREPLACE
with no remainder; 0x112D / 0x20112D are the AT_HWCAP letter sets IMAFDC / IMAFDCV. 0x10040 (YK09, YK0j) is the
program header vaddr of both images. YA02.v's argH0 offsets are usp-relative; header line 4 documents the change and
argH0_range / not_argH0 (Qed) restate them.
The values HAND.md #12 / #25 changed: YCbq.v:1085 and YCe5.v:673 off_img 0x606000 are IMAGE-EXTENT-SAME in RU;
YG0f.v:19 kImgEnd 0x606000 is a KERNEL-FACT row. Both images end below it: last PT_LOAD end 0x605e78 (A) and 0x6059f8
(B), each page-rounded to 0x606000.

### Runtime files (Rt runs, 6295 rows)

| run | rows | reasons |
|---|---|---|
| RtDisco | 103 | PROOF-STEP 44, NO-PORTED-VALUE 51, NEW-NONADDR 7, KERNEL-FACT 1 |
| RtCgifA | 2743 | NO-PORTED-VALUE 1892, PROOF-STEP 578, IMMEDIATE-DONOR-OK 184, NEW-NONADDR 53, KERNEL-FACT 16, ASAN-GLOBAL-LAYOUT 14, ODR-INDICATOR-BYTES 4, SYMBOL-NAMED 2 |
| RtCgifB | 2743 | NO-PORTED-VALUE 1892, PROOF-STEP 578, IMMEDIATE-DONOR-OK 237, KERNEL-FACT 16, ASAN-GLOBAL-LAYOUT 14, ODR-INDICATOR-BYTES 4, SYMBOL-NAMED 2 |
| RtGrant | 6 | PROOF-STEP 5, KERNEL-FACT 1 |
| RtPreset | 587 | NO-PORTED-VALUE 469, DONOR-TUPLE-MATCH 52, PROOF-STEP 40, KERNEL-FACT 7, CODE-POINT-PAIRED 5, NEW-NONADDR 5, ODR-INDICATOR-BYTES 4, FILE-DEFINITION-NAMED 2, WHOLE-FUNCTION-RANGE 2, SHADOW-STORE-COUNT 1 |
| RtRelay | 113 | PROOF-STEP 85, NO-PORTED-VALUE 21, NEW-NONADDR 3, KERNEL-FACT 2, SYMBOL-NAMED 2 |

Per file: counts.tsv has run x reason; triage-rows.<RUN>.tsv has the rows.

What the measured rules show for the known mis-map classes:
- GOT cells (class A): RtStrcmpTbl.v sc_rodata's .got slot 0xa63e0 holds 0x142be8 = common_flags_dont_use, the
  same symbol the donor's slot 0x9c860 holds in fuzz_grant.asan; RtSM5T.v's eight read-only cells are formed by the
  same instruction (function + offset) in our image and in the donor's (xref.py: auipc pairs in the walked ranges);
  the four .got slots among them hold the same pointee symbols or the same constants (0x1, 0x8).
- Counts and sizes: RtSM5T.v (0x3ff84, 131) is the whole body of __asan_stack_malloc_5 (524 bytes); its eight callee
  ranges are the donor's FS_CALLEE_RANGES by symbol + offset with equal word counts; its five walk pcs sit at the
  donor's class-3 offsets with equal words modulo immediates; 32 shadow stores = the `sd zero` stores in the class-5
  body (class 3: 8). RtDtorExit.v: asan_globals holds 180 records of 64 bytes in both images (A 0xaad00..0xada00,
  B 0xaa860..0xad560) with beg / size / size_with_redzone / name / module / dynamic-init / location / odr fields at
  +0..+56 in all 180; x2_odr (addr, 3) and (addr, 1) are the four 1-byte __odr_asan_gen_* symbols of each image.
- Moved constants (class B): no flagged row holds a small model constant moved into the image range; NEW-NONADDR
  refuses every one of its rows with the value moved by 0x10000 (controls.tsv).

### Controls (controls.tsv)

Every value-checking rule refuses all of its rows with value + 4 (SYMBOL-NAMED, FILE-DEFINITION-NAMED, PHDR-VADDR,
ABI-MMAP-FLAGS, ABI-HWCAP, ODR-INDICATOR-BYTES, CODE-POINT-PAIRED, SHADOW-STORE-COUNT, WHOLE-FUNCTION-RANGE,
ASAN-GLOBAL-LAYOUT, DONOR-TUPLE-MATCH, IMMEDIATE-DONOR-OK, SIBLING-LINE), and every row that has a different donor
value with the donor's value (IMMEDIATE-DONOR-OK 5 + 5, SHADOW-STORE-COUNT 1). NEW-NONADDR judges a class (below the
image base, no donor value), not a value: it accepts value + 4 on its 143 rows by design and refuses all 143 with the
value moved into the image range.

## Commands (from the slice dir; tree and image locations are environment variables in the scripts)

```
python3 find_donor.py GITDIR <our file> <candidate donor path>...      # work/find/*.out
python3 check_twin.py <pin> <twin> ...                                 # work/twin-check.out
./rt_runs.sh prep                                                      # work/rt/<RUN>/{src,dst}, donors
./rt_runs.sh run RtDisco RtCgifA RtCgifB RtGrant RtPreset RtRelay CtlDisco CtlGrant CtlPreset CtlCmdA
./ru_runs.sh RUP CtlCgifP
python3 base_triage.py runs/<RUN>/full.tsv <dst dir> flag-classes.txt triage/gen-none.txt triage/<RUN>   # (RU: lib/Reusable, triage/gen-RU.txt)
python3 triage_rtru.py .                                               # triage-rows*.tsv, controls.tsv, counts.tsv, adjacent.tsv, donors.tsv
```
RtPreset, CtlPreset and RtGrant were re-run on the build VM with the same wrapper (REL=RUNDIR=<dir> rt_runs.sh run ..).
SIBLING-LINE reads work/sib: lib/Reusable of the 11 released sibling units of 781f46bc05cd (`git archive 781f46bc05cd
proofs/<project>/<unit>/lib/Reusable`). work/reusable_history.txt (series head: the commit whose unit tree is plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record)) is `git log --name-status <series head> --
proofs/plugin-hostd/fuzz_command/lib/Reusable`.

## Files

Scripts: find_donor.py, check_twin.py, rt_runs.sh, ru_runs.sh, img.py (image queries), xref.py (auipc pairs),
byuse.py (by-use grep), triage_rtru.py. Results: triage-rows.tsv, triage-rows.<RUN>.tsv, controls.tsv, counts.tsv,
adjacent.tsv, donors.tsv. Raw: runs/ (gate output, with the run's own INPUTS USED block), runs/superseded/, triage/
(base pass), work/ (run inputs, images, donor rankings, sibling extracts).
