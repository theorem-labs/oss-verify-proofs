# port_core d9e0589898fd dry re-run — libreac/fuzz_identity, B core

Ruling: a lane 19:10Z — for a port_core output whose inputs are re-runnable, "run d9e0 --dry on those inputs, diff
stage-out by sha256, classify provenance-only / patched / VALUE; a VALUE row is fixed as a MEASURED ROW through
measured-rows". Amended 19:13Z, corrected 19:31Z: the value checks of record are port_addr_check `3d2eee813cce` with
its limits, roundconst-gate v2 `32b39f3b34e9` ("run v2 once per relocated unit") and the count recompute. Known limit
recorded 19:51Z: "a relocated numeral that names an object is derived as target symbol + offset from the donor's
symbol + offset; a value landing in .got / .got.plt or on a different symbol REFUSES". Donor defect 19:55Z: "Each
cgif-derived unit checks its tfib_rodata_hi against its own pin's .rodata end".

The B core is the 422 files of `lib/ReusableB/` (port_core's `--reusable-dir ReusableB`). `lib/B/` holds the unit's
own composition files, which no port_core run writes, so they are not in the diff.

## Inputs, all verified re-runnable

| input | path | state |
| --- | --- | --- |
| tool | `tools/pg-reloc/d9e0589898fd/` at the relocation tools branch `4cc81ff763b` | `port_core.py` sha256 `d9e0589898fd`; vendored files as `check_vendored()` requires |
| donor text | `proofs/cgif/cgif_file_fuzzer/lib` of the relocation lane's branch (last change `9a7a69740fa6`, 10-27) | 2468 files, git blob for blob equal to `<the acceptance lane's workspace>/port/core/src/proofs/cgif/cgif_file_fuzzer/lib` |
| donor image | `<the relocation lane's workspace>/bin/cgif/cgif_file_fuzzer/cgif_file_fuzzer.asan-ubsan` | sha256 `1c29845fe605` = `builds.asan-ubsan` of cgif's `harness.yaml` |
| donor twin | `<redacted: see the internal record>bin/cgif-twins/cgif_file_fuzzer/cgif_file_fuzzer.asan-ubsan` | sha256 `ce511d541cda`; PT_LOAD table and allocated sections equal to the pin |
| donor names | `<redacted: see the internal record><a recovery cache; see the internal record> (`--old-syms`) | sha256 `5dfc9244b543`, keyed by the donor image's own hash |
| target lib | `proofs/libreac/fuzz_identity/lib` of the B-core tag (its 625-file list `B-core-files.txt`, sha256 `1d5c942ac07d`, is not preserved; the 147 files d9e0 kept ARE the shipped `lib/B` and `lib/ReusableB`) | no `ReusableB/`; d9e0 keeps 147 files from it, as the run of record did (run 18: "147 kept from the target") |
| target image | `<redacted: see the internal record>bin/libreac/asan-ubsan/fuzz_identity` (the run of record's own `--target-elf` path) | sha256 `baf1a4d065e0` = `builds.asan-ubsan` of the unit's `harness.yaml` at `70952e1c8c9`; same bytes as `<redacted: see the internal record>bin/pau-libreac-v190/libreac/bin/fuzz_identity/fuzz_identity.asan-ubsan` |
| target twin | `<redacted: see the internal record>bin/libreac/asan-ubsan/fuzz_identity.debug` (`--target-syms`); `<redacted: see the internal record>bin/libreac-v190/x/unstripped/fuzz_identity/fuzz_identity.asan-ubsan` (sweeps) | sha256 `43b44d50be8a` / `4eac57e0fceb`; both have the pin's section layout and the same 2200 FUNC/OBJECT symbols |
| file list | `<the B-core lane's workspace>/bcore-rel3/B-core-files.txt` | sha256 `1d5c942ac07d`; 625 entries, the entry set of the tag's `core-files-Y.txt` |
| overrides | `<the B-core lane's workspace>/bcore-rel4/overrides-B-full.tsv` | 64 rows, sha256 `34df46258062` = `overrides_sha256` of the run's `compose-B-rec.json` |
| patches | `<the B-core lane's workspace>/bcore-rel4/patches/01..16-*.patch`, in the record's order | each sha256 equal to `patches_sha256` of `compose-B-rec.json` |
| other image | `<redacted: see the internal record>bin/libreac/asan/fuzz_identity` (`--known-elf`) | sha256 `c954b804786c` = `builds.asan` |

The run of record was port_core `53ec3af2afc9`, run 18. Its log keeps the paths of the donor image, the target image
and the staged files, but not its command line. The worktrees it used for the donor text and the target lib no
longer exist. The donor text is the same tree: cgif's lib on the relocation lane's branch has not changed since 10-27. For the
target lib, the B-core tag was cut one minute before the B file list was written, and d9e0 keeps the
same 147 files from it. `--rename TfibB=IdentB` comes from the shipped files' own notice ("names TfibB -> IdentB").

Command (`scripts/run-d9e0-dry.sh`): `port_core.py --src-lib <donor lib> --old-elf <donor image> --old-prog
804c0:86e40 --old-syms <donor names> --target-lib <B-core tag lib> --target-mod
OssFuzzTheorems.Proofs.libreac.fuzz_identity.lib --target-images OssFuzzTheorems.libreac.fuzz_identity.images
--target-name libreac/fuzz_identity --target-elf <pinned asan-ubsan> --target-syms <twin> --files B-core-files.txt
--remap-images --reusable-dir ReusableB --kernel-dir Reusable --rename TfibB=IdentB --known-elf <asan pin> --override
overrides-B-full.tsv --patch <16 patches> --work <work dir>` (no `--apply`, so this is the dry run).
Result `rc=3`, 13 min, **symbol gate: explained 3147, info 885, review 252 — PASS**, 155 values with no rule.

The tool applied 62 override rows. It refused 2 rows as `override-ambiguous` because the ledger has no OCCURRENCE
column: `YD1j.v:119` and `YFk9.v:113`, which is a no-op row. It applied 9 of the 16 patches. Of the 7 that failed,
3 are "previously applied": d9e0 now writes those fixes itself (04, 05 kept-subdir prefix, 10). The other 4 failed
because d9e0's text around the hunk changed (07, 08, 06, 16). The other FAIL rows are refused markers and
`kept-refused-definition` (12 files), `row-address` (the YF0m / YD2j slots, by design) and `partner-left` YD1u.v:109
(its start 0x10000 is IMG_LO on both images) (`d9e0/pc-dry.log`, `d9e0/review.tsv`).

## The classified diff, against the SHIPPED tree

Shipped = `lib/ReusableB/` at `70952e1c8c9`, the merge of PR #399. origin/ossv/recipes has not changed this unit since.
The comparison is sentence by sentence on comment-free code (`scripts/classify-defs.py`, `classify/classify-B.tsv`).

| class | count | disposition |
| --- | --- | --- |
| files agreeing byte for byte | 295 of 422 | — |
| files differing in comments only (the notice line) | 3 (YA05, YA09, YE3e) | provenance-only |
| files differing only in `From … Require` lines | 92 | provenance-only (module layout; 107 files differ in Requires in all) |
| generated slots (d9e0 stages cgif's text, numerals untouched; the shipped file is the start-up collector's) | 11 (+ YB1m, Requires only) | slot, no d9e0 value to compare |
| `ReusableB/YImgTop.v` (d9e0 only) | 1 | provenance-only: IMG_LO 0x10000 / IMG_TOP 0x5fa000, the same as the shared `Reusable/YImgTop.v` the shipped files Require |
| `ReusableB/YCbq.v` | 1 | patched: retired to a stub by the run's patch 08 (one ajournal), which no longer applies to d9e0's text |
| files differing in code | 19 | below |
| `port_core_refused_*` markers | 53 sentences in 12 files | d9e0 declines to decide; the shipped value stands |
| symbolic vs literal, same value | 33 sentences in 5 files | `IMG_TOP` vs `0x5fa000`, `0xa0d38` vs `658744`; provenance-only |
| rename form | 4 (YD2l) | d9e0 also renames `_` parts (`TfibB_ok` -> `IdentB_ok`); provenance-only |
| patched | 19 (YD1q) | the run's patches 06 / 08 (`lib_shape` context, two `*_has_nil` lemmas) |
| function-table rows | 10 (YB1w) | d9e0 adds 8 alias rows (`tfib_A_asan_stack_malloc_N`, `..._hash_helper`) and reorders `LLVMFuzzerTestOneInput`; all 1149 shipped definitions are equal by name and value |
| start-up proof text | 22 (YE37) | the shipped YE37 is the start-up branch's file (another proof), not port_core's output; no value pair |
| **REAL value differences** | **8 definitions** | **2 ACCEPTED, 6 REJECTED — see below** |

## Every REAL row, arbitrated against the pin and its twin

| file | definition | shipped | d9e0 | what the image says | verdict |
| --- | --- | --- | --- | --- | --- |
| `ReusableB/YFem.v:128` | `TOT_range : 2 <= TOT <= N` | `127443` | `127008` | The bound is the unit's own count: TOT <= 31 + 1 + 31 * 4096 = 127008 (DEPOT_MAX at lib/Reusable/YG01.v:141). Its terms are `lo_tr0` ≤ 31 and `depot_frames_bound` ≤ 31·len, with `Definition DEPOT_MAX : Z := 4096.` The donor twin's line says 127008 already (cgif_file_fuzzer `lib/YFem.v:127` at `70952e1c8c9`). 127443 = `0x1f1d3` = the pin's `.rodata` string "CIE start does not match"+22, and 127008 = `0x1f020` is the same string+22 in the donor. The run of record moved a count as a string address. port_addr_check 3d2e: NON-ADDRESS-CHANGED. d9e0's row is how this was found, not the source of the value | **ACCEPTED** |
| `ReusableB/YFem.v:206` | `zone_facts` (`2 <= TOT <= N`) | `127443` | `127008` | the same bound, TOT <= 31 + 1 + 31 * 4096 = 127008 (the donor twin's `lib/YFem.v:205` says 127008) | **ACCEPTED** |
| `ReusableB/YE34.v:20` | `musl_sel_ranges` | `(0x905f8,125); (0x907ec,258)` | `(0x905f8,383)` | the same words. Both start at `__stdio_write` and end at `__stdio_exit+0x1c`, as cgif's `(0x92f60,435)` does. The shipped list splits at `__lockfile`'s start | REJECTED |
| `ReusableB/YE34.v:23` | `icpt_ranges` | `(0x421f4,24); (0x42254,1); (0x42258,11)` | `(0x421f4,36)` | the same words, to `___interceptor_strlen`'s start. The shipped list splits at the trampolines `0x42254` / `0x42258` | REJECTED |
| `ReusableB/YE3i.v:25` | `IMG_RO_HI` | `0x2fa20` | `0x2f8c0` | shipped = the pin's `.eh_frame` **end** = PT_LOAD0 end. d9e0's value lies inside `.eh_frame` with no symbol. It is cgif's `0x2f1ac` (0x160 below cgif's own end) carried over | REJECTED |
| `ReusableB/YF0m.v:848` | `Tfib_const_shadow` | identity's cells | cgif's cells verbatim | d9e0 keeps the generated classes at the donor's values by design. None of its 35 z1 cells agrees with the shadow derived from identity B's 51 `asan_globals` descriptors; 318 of the 726 shipped cells do, the rest lie outside that model | REJECTED |
| `ReusableB/YF0m.v:1576` | `Tfib_zero_shadow` | identity's holes | cgif's (`… 0xa2ae0 …`, `0x5fb000`) | d9e0's values are cgif's `asan_globals` start and image top | REJECTED |
| `ReusableB/YF0m.v:1578` | `Tfib_owned_static` | `(0x9e388,…); (0xa0f40,0xcc0); (0xa1c00,8)…` | `(0x9ff18,…); (0xa2ae0,0xc0); (0xa2bc0,8)…` | shipped = the pin's `.data` start, `asan_globals` start and size, `.bss` start. d9e0's values are cgif's | REJECTED |

**Verdict: 2 rows ACCEPTED, 6 REJECTED.** The ACCEPTED pair is one stale numeral at two lines of `ReusableB/YFem.v`:
127443 -> 127008. The value is TOT <= 31 + 1 + 31 * 4096 = 127008 (DEPOT_MAX at lib/Reusable/YG01.v:141), and the
donor twin's own line agrees. It does not come from d9e0: on scene-derived routes d9e0 keeps 127070 here. The shipped statement is true but weaker (TOT ≤ 127008 ≤
127443), and the tree builds, so no proof is false. It is fixed in the series' code commit (B:
`ReusableB/YFem.v:128`, `:206`). The six REJECTED rows are d9e0's errors on this core: merged code runs that cover
the same words, an `.eh_frame` interior point, and generated classes left at cgif's values.

## roundconst-gate v2 (32b39f3b34e9)

port_addr_check `3d2eee813cce` ran a full table (d9e0's `stage/ReusableB` vs the shipped `lib/ReusableB`; images keyed
B with both unstripped twins; 421 files paired, 206625 numerals). roundconst v2 ran over it. Every file was checked
against its SHA256SUMS (`roundconst/`).

```
selected 130190 kept rows equal to a donor quantity
  MISMATCH 499 (NON-ADDRESS-SAME) | MIXED 5781 (940 NON-ADDRESS-SAME, 4841 SAME-GEOMETRY) | SAME 123910
control 1, donor on donor            : 0 non-SAME rows (0 expected) — PASS
plant, image extent kept (v1 class)  : YD1g.v:746 0x5ea000 -> 0x5eb000      — CAUGHT (MISMATCH)
plant, a /8 span kept                : YD1o.v:101 700544 -> 700556 (0xab08c) — CAUGHT (MISMATCH)
gap control (below 0x100)            : YF0m.v:1579 0xcc0 -> 0xc0 (asan_globals size, also the
                                       lsan suppression_placeholder extent on identity) — SAME, as the README predicts
rows only in the plant: exactly the 2 planted rows
```

None of the core's moved small or word-count positions can carry a v2-only positive plant. The README requires a
plant whose value equals the donor numeral at that position. At every such position the donor value is also an
agreeing identity quantity, so the plant reads SAME (the gap).

**Every one of the 6280 MISMATCH / MIXED rows has a decision; all are NOT-THE-QUANTITY. HITs: 0**
(`roundconst/roundconst-v2-verdicts.tsv`):
- 125 MISMATCH rows: cgif's own image-A twin text (`A/A<x>.v`) states the same value at the paired line, while
  cgif-asan's value of every name the row has differs. So the number is not that quantity in the donor's own text.
  Decided by `roundconst/rc-twin.py`.
- The other 6155 rows carry 22 distinct values, each read by role from the lines `roles.py` lists. 4096 / 8192 / 1024 /
  2048 are page-size and run-time constants (5776 rows; MIXED, so each is also an identity-B quantity). 109 / 166 /
  86 / 83 / 172 are environment or step indices (`EVar 109`, `SOff 166`, `xafterD 86`). 320 / 332 / 334 / 344 / 640 /
  644 / 652 / 668 / 860 / 980 are instruction offsets inside musl memcpy (vm_compute `fetch_word` facts) and stack
  offsets. 4152 is an `a_off`. 108 is a string byte. 1194 is a code-word count: `[0x3366c, +1194·4)` runs from
  `Quarantine::Drain` to the start of `SizeClassAllocator64::EnsureFreeArraySpace` on the pin, as cgif's
  `[0x32f58, +1194·4)` does.

Named gaps stay as the README states them: a kept small donor value equal to a right target quantity reads SAME;
unnamed unpaired runs and function sizes are not gated; changed values are port_addr_check's own `*-CHANGED`
verdicts (the TOT rows above are NON-ADDRESS-CHANGED).

## Symbol + offset sweep, paired with the donor

The gate is `symoff-check.py` of the frame B-core branch (`…/core-B/b-core/gates/`, sha256 `ad6c4f3fd7de`),
with the one change the A sweep (`provenance/evidence/symoff-A.md` of the series tree) made: `SIDE` names the side (here
`ReusableB`) and the `YImgTop.v` skip is by suffix. The result, `symoff/symoff-B.py` (sha256 `fce36a5f1cd1`), is
byte-identical to the A sweep's copy; `symoff/symoff-B.py.diff` shows the change. `DONOR_ELF` / `DONOR_TWIN` are the
cgif asan-ubsan pin and twin above. `FRAME_ELF` / `FRAME_TWIN` are identity's pin and its `x/unstripped` twin.
`STAGE` is d9e0's `stage/`, and `CORE` is
the shipped lib.

```
checked 9135 numerals
  EQUAL (target symbol + offset, as the rule requires)   7281   | GOT-EQUAL 210 | EMITTED-EQUAL 35
  DIFFER 1279 + GOT-DIFFER 10                            1289
  NO-COUNTERPART 180 | AMBIGUOUS 90 | GOT-NO-COUNTERPART 28 | GOT-ZERO-WORD 8 | GOT-AMBIGUOUS 4 | EMITTED-NO-SYMBOL 10
  NO-SYMBOL 1583 (bounds, gaps: not checked here) | UNPAIRED-LINE 2697 (2148 of them in start-up files)
  flags: C_IN_GOT 0 | C_OTHER_SYMBOL 611
```

| the 1289 DIFFER rows | count | what they are |
| --- | --- | --- |
| committed value **equals the donor's** | 1054 | not a move. 525 instruction words / decodes, 19 labels, and run-time constants that fall inside a huge `.bss` object (262144, 1048576, mmap flags 0x104022, 1446400). 260 of them are in start-up files |
| moved, in start-up files (the 12 slots + YB13, YE3i, YF0m, YE23, YE37) | 163 | the collector's values paired with another donor row (YB01, YCej, YD2j region lists; all 10 GOT-DIFFER are YD2j). 57 carry one of the core value pairs below |
| **moved, in port_core's files** | **72** | **11 value pairs, each checked by hand, all RIGHT** (`symoff/symoff-B-moved-roles.tsv`) |

| value pair | rows | role, measured on the two pins |
| --- | --- | --- |
| `0x5eb000 -> 0x5ea000` | 37 | image hull length: 0x5fb000 − 0x10000 vs 0x5fa000 − 0x10000 |
| `0xbf600 -> 0xbf400` | 21 | image end / 8 |
| `0xbd600 -> 0xbd400` | 4 | hull length / 8 (length of the image shadow) |
| `0xbf5ff -> 0xbf3ff` | 1 | (top − 1) / 8 |
| `0xab08c -> 0xab080` | 1 | (top − asan_globals end) / 8: (0x5fb000 − 0xa2ba0)/8 vs (0x5fa000 − 0xa1c00)/8 |
| `0x9dca8 -> 0x9b070` | 1 | `tfib_preinit_array_hi` = `.preinit_array` end |
| `0x45fc0 -> 0x460a4` | 2 | relative jump-table entry: the pin's word at 0x20d10; cell + entry = `VSNPrintf+944` on both images |
| `0x6ba3c -> 0x689b0` | 2 | relative jump-table entry: the pin's word at 0x21d04; cell + entry = `sysconf+532` on both |
| `0x1fabe4 -> 0x1fadbc`, `0x1fab5c -> 0x1fad34` | 2 | decoded jal immediates of the instruction word on the same line (0xdbdfa0ef, 0xd35fa0ef) |
| `0x62056 -> 0x61c66` | 1 | a data address / 4: 4·401494 and 4·400486 are both `theDepot+0` |

The non-EQUAL rows in port_core's files that the symbol rule cannot decide were checked one by one, and each one is
consistent. 54 NO-COUNTERPART rows are kept instruction words. 10 are function-table ends and section ends at the
next identity function start or section bound (cgif-only names such as `fopen`, `cgif_newgif`). 23 AMBIGUOUS rows have
the same name and offset on both images (`buf+8`, `MemToShadow+0x1c`). 20 GOT rows are `.got` cells that hold the same
word on both images. No numeral enters `.got`. The sweep has no cross-check table for identity B (no alreloc run of
this core exists), so `symoff-verdict.py` is not run. This record claims only the checks above.

## tfib_rodata_lo / _hi against the B pin

| definition | shipped | d9e0 | B pin `.rodata` | donor YB1w.v | cgif asan-ubsan `.rodata` |
| --- | --- | --- | --- | --- | --- |
| `tfib_rodata_lo` | `0x102e0` | `0x102e0` | start `0x102e0` | `0x102e0` | `0x102e0` |
| `tfib_rodata_hi` | `0x2308c` | `0x2308c` | **end `0x2308c`** | `0x2278c` | **end `0x2278c`** |

The 19:55Z donor defect does not reach the B twin. cgif's `0x2278c` is wrong only for its asan image (`.rodata` end
`0x227cc`); it is the right end for cgif's asan-ubsan image. So the B relocation carries a correct end, and both d9e0
and the shipped cell equal the B pin's `.rodata` end. All 22 section bounds of `ReusableB/YB1w.v` equal the pin's
section headers (`rodata/section-bounds-YB1w.tsv`), as do `tfib_img_lo` / `_hi` (0x10000 / 0x5fa000) and
`tfib_entry` = e_entry `0x30a20`.

## CZONE bound: two values in the B core

| files | shipped HI of `0x7fff8000 <= a < HI` | how it got there | port_addr_check 3d2e |
| --- | --- | --- | --- |
| `ReusableB/YFix.v:284, :288`, `YFjb.v:283, :287`, `YFju.v:574, :584`, `YFkm.v:1296` | `0x8004fe08` | the run of record's shadow rule moved cgif's `0x80050000` down by `0xfc0 / 8` (the B data shift) | UNRESOLVED, 7 positions ("shadow of 0x2c0000 (seg3:.bss): no object starts there") |
| `ReusableB/YFhn.v:418`, `YFkz.v:892` | `0x80050000` | kept by two `--override` rows of the ledger | ROUND-CONSTANT-SAME |

cgif's A and Y twins both state `0x80050000`, so the bound does not depend on the image. The tag README's item 86
says a CZONE bound "is kept or refused, never moved as a shadow address". d9e0 refuses all positions here
(`czone-unverified`: the target lib holds no YF0m), so no d9e0 value exists. Both shipped values are above identity
B's highest constant shadow cell, which ends at `0x8000c380`, so every cell is inside either zone and no proof is
false.

Ruling. Under a lane 19:10Z this is not a VALUE row: a refused marker gives no d9e0 value, and the shipped value
stands (as in the A record). The two `0x80050000` positions are relocation-tool input rows, which stand under the
19:29Z clarification (2). The value checks of record (19:13Z, corrected 19:31Z) do judge the other seven:
port_addr_check `3d2eee813cce` flags all seven UNRESOLVED. Restoring `0x80050000` there would change text committed
to a shipped tree, which makes it a measured row (19:29Z). Whether to restore it is the unit owner's call; this
record does not make it.

## Observations outside the VALUE rows

- **The A core carries the TOT defect too.** Shipped `A/AFem.v:128` and `:206` hold `127436` = `0x1f1cc` = the
  same string+22 in identity's asan image. The same bound, TOT <= 31 + 1 + 31 * 4096 = 127008, holds there. The
  donor's own `A/AFem.v:127` holds 127070 = the string+22 in cgif's asan image, so that line carries the same
  artefact. The A record does not list it.

## Files beside this README

`d9e0/` (the run log, versions, override outcomes, patches.log, gate.tsv / gate.log, review.tsv, required.tsv),
`classify/` (sha256 by file, the sentence classification, the full stage-out diff), `roundconst/` (both
port_addr_check tables, rc-B / dd / plant outputs, roles.out, the twin decision and the verdicts), `symoff/` (the
script and its one-change diff, the sweep TSV, the moved-row roles), `rodata/`, `scripts/`.
