# libreac/fuzz_decode, image A alloc-reloc: section 8 re-run on cmpkit 4bbd3a74be89 (DATE, WORKER)

Why: AGENT's order of TIME DATE. The record of DATE (WORKER decode/ALLOC-PATTERN.md section 8,
"Re-check of every funcpair verdict with bytecmp of record") was made with bytecmp c487b3618415 and, for the ecall /
AMO / LR / SC words, bytecmp 475ff6314d3c and 7daa0e2a03d9. All three are superseded by cmpkit 4bbd3a74be89, the
version of record for every "same code up to pc-relative fields" verdict. This file re-runs that record's claims on
the kit and states what changed. It changes no .v file and no theorem; it is provenance only.

## 1. Tools

| what | sha256 (12) | where |
| cmpkit (the kit id = first 12 of sha256(SHA256SUMS)) | 4bbd3a74be89 | hub HUB, commit 3c3e62ee2786af6133699ff6684d17d66adcb03c (BRANCH), tools/cmpkit/4bbd3a74be89/ |
| strictcmp2.py (THE one compare: tcmp / tsame) | 16982e3ef42b | kit member |
| drvcmp.py (loader; `twins`) | 4d70e90bc1fa | kit member |
| bytecmp-1480ca2faea0.py (words / auipc dataflow / cmp) | 1480ca2faea0 | kit member |
| repin_check-4c05cadaeba3.py (shared Img; used by drvcmp and by controls/negctl.py) | 4c05cadaeba3 | kit member |
| repin_check e5487165abb8 (the OLD tool controls/negctl.py compares against) | e5487165abb8 | same BRANCH commit, tools/repin_check/e5487165abb8/repin_check.py |

The kit was extracted into one directory holding exactly its seven files (`git -C <hub> archive 3c3e62ee2786 …`);
`sha256sum -c SHA256SUMS` OK for all seven, and sha256(SHA256SUMS)[:12] = 4bbd3a74be89.
controls/negctl.py loads the old repin_check from a fixed path, NEGCTL_ROOT/tools/
repin_check/e5487165abb8/repin_check.py; that lane's worktree is gone, so the file was written there from the same
BRANCH commit (sha256 e5487165abb8dfb7…, the registered one). Nothing else outside this record was touched.

Superseded comparers of the old record: bytecmp c487b3618415, 475ff6314d3c, 7daa0e2a03d9 (and funcpair over elfdis
caa79a10662e, which the old record used for its EQUAL column).

## 2. Binaries, and the twin proofs

The kit's compare needs .symtab on BOTH sides, so both sides are the unstripped twins of the pinned binaries.

| side | file | sha256 (12) |
| donor pin (cgif asan-ubsan, LANE's frozen chain) | <hub>/projects/cgif/bin/cgif_file_fuzzer/cgif_file_fuzzer.asan-ubsan | 1c29845fe605 |
| donor twin, C | DONOR_TWIN | ce511d541cda |
| decode A pin (projects/libreac/fuzz_decode/harness.yaml builds.asan.sha256 5973b76807d8d2e1…) | DECODE_A_PIN | 5973b76807d8 |
| decode A twin, A | DECODE_A_TWIN | 4cb0a852e826 |

`drvcmp.py twins` (out/twins.out), both pairs: PT_LOAD layout equal True, and every differing loadable byte lies in
the ELF header [0x10000,0x10040) or .note.gnu.build-id [0x102a8,0x102cc) — 25 bytes, none outside. The twins are the
pinned images up to those two regions.

## 3. Controls, run before the comparison

- `python3 cmpkit-4bbd3a74be89/controls/negctl.py cmpkit-4bbd3a74be89` (out/negctl-mine.out): byte-identical to the
  kit's own controls/repin-negctl.out (`diff` reports nothing). Natural FA:DP 11 target differences, baseline FA:DA 0,
  planted DA main+0x50 `jal __wrap_malloc -> __wrap_free` caught, under the old tool and the kit's. PASS.
- `python3 ownctl.py cmpkit-4bbd3a74be89` (out/ownctl.out): three planted defects on THIS run's own inputs (an
  in-memory Img.segs patch of the decode A twin, as negctl.py does; no image is written):
  - PLANT 1, the first jal of Allocate re-pointed (0x5819c -> 0x581b4): new difference at +0x50
    (`_ZN6__asan10AsanInitedEv+0x0` vs `__asan_report_load1+0x0`, kind names). CAUGHT.
  - PLANT 2, the first compared ld target of Allocate moved 8 bytes (0x103c8 -> 0x103d0): new difference at +0xc4.
    CAUGHT.
  - PLANT 3, one memset body word changed `addi 00300713 -> andi 00307713` (same registers): verdict EQUAL ->
    DIFFERENT, real 1. CAUGHT.
  All three PASS.

## 4. The run of record

```
FNS=$(awk -F'\t' 'NR>1{printf "%s%s",(NR>2?",":""),$1}' <old>/out/pairs.tsv)       # the 7 names of the old record
python3 cmpkit-4bbd3a74be89/strictcmp2.py cmp "$FNS" C=<donor twin> A=<decode A twin> C:A > out/run-strictcmp2.out
python3 symcheck.py cmpkit-4bbd3a74be89 <old>/out/pairs.tsv                         > out/symcheck.out
python3 numerals.py cmpkit-4bbd3a74be89 <old>/out/numerals.tsv <old>/out/pairs.tsv \
        <donor twin> <decode A twin> out/numerals-kit.tsv                           > out/numerals-kit.out
python3 probe_tbl.py cmpkit-4bbd3a74be89                                            > out/probe_tbl.out
```
(run.sh beside this file runs all of it, including the kit extraction, the twin proofs and the controls. `<old>` =
OLD_RECORD, the DATE record's own outputs.)

### 4.1 The 7 function pairs, old verdict vs new

All addresses are donor -> decode A and are the ones the old record names; strictcmp2 found each function by name and
both sides agree on size, so no pair was re-selected.

| function | donor -> decode A | size | OLD (bytecmp c487b3618415: pcrel, real, unmeasured) | NEW (strictcmp2 16982e3ef42b) | target pass (new; the old comparer had none) |
| __asan::Allocator::Allocate | 0x31550 -> 0x3124c | 2440 | EQUAL-mod-pcrel (81, 0, 0) | EQUAL-mod-pcrel (81, 0, 0) | 22 targets accepted (2 full-bytes, 20 C-string); 1 reported row at +0xdc, see 4.2 |
| __sanitizer::CombinedAllocator<…>::Allocate | 0x359e4 -> 0x357c0 | 728 | EQUAL-mod-pcrel (16, 0, 0) | EQUAL-mod-pcrel (16, 0, 0) | 8 C-string acceptances; 0 differences |
| __sanitizer::SizeClassAllocator64LocalCache<…>::Refill | 0x36134 -> 0x35f10 | 256 | EQUAL (0, 0, 0) | EQUAL (0, 0, 0) | 0 targets, 0 differences |
| __asan::PoisonShadow | 0x53800 -> 0x53040 | 1276 | EQUAL-mod-pcrel (61, 0, 0) | EQUAL-mod-pcrel (61, 0, 0) | 12 accepted (1 GD/.got value `fake_stack_tls+0x1@tls`, 11 C-string); 0 differences |
| __sanitizer::internal_mmap | 0x64198 -> 0x63d3c | 12 | EQUAL (0, 0, 0) | EQUAL (0, 0, 0) | 0 targets, 0 differences |
| __sanitizer::StackDepotPut | 0x724e0 -> 0x72084 | 32 | EQUAL-mod-pcrel (2, 0, 0) | EQUAL-mod-pcrel (2, 0, 0) | 0 targets, 0 differences |
| memset | 0x9790c -> 0x92474 | 248 | EQUAL (0, 0, 0) | EQUAL (0, 0, 0) | 0 targets, 0 differences |

0 DIFFERENT, 0 UNMEASURED, on both comparers. Every per-word count (pcrel, real, unmeasured) is the old one.

Selection (out/symcheck.out): in each image each of the 7 names carries exactly ONE symbol, at the address above, all
STT_FUNC and of the size above — so the kit's name lookup cannot have taken another copy. This re-measures, on the
twins, what the old record measured on decode A's .symtab + .dynsym.

### 4.2 The one row the kit reports, and its by-hand acceptance

Allocator::Allocate +0xdc, `(.rodata)` vs `(.rodata)`, data-differs. This is the kit's own KNOWN FALSE-DIFFERENCE
class (cmpkit README:153-160): an unnamed .rodata target read through a bounded index is compared on its whole region
to the next FUNC / OBJECT symbol, and the regions differ in size (66360 B in the donor, 66236 B in decode A).

Measured by hand (out/probe_tbl.out, same strictcmp2 16982e3ef42b): the target is 0x10428 in the donor and 0x10438 in
decode A; the 64 bytes at it are byte-identical in the two images
(`00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a`,
the De Bruijn ctz table). The code that reads it is `and`, `mul` by the De Bruijn constant, `srli …,58`
(`0xcc:00d5f5b3 0xd0:02c585b3 0xd4:auipc 0xd8:03a5d593 0xdc:addi 0xe0:00b605b3 add 0xe4:0005c583 lbu`), so the index
is in [0,63] and only those 64 bytes can be read. A listed by-hand acceptance with its own measurement, never a kit
EQUAL — the same acceptance WORKER made for the same donor table (its kitrerun/RESULT.md, DATE).
This word is not one of the 417 relocated numerals (no numeral row has a target difference, 4.3).

Kit verdict and settled verdict, side by side (AGENT's rule of TIME: a `data-differs` on an unnamed read-only
target is not a real difference until a named measurement says so; a real difference is a differing instruction
word, a differing NAMED target, or a table entry whose symbol + offset differs):

| row | kit verdict (strictcmp2 16982e3ef42b) | what it is | measurement that settles it | settled verdict |
| Allocate +0xdc, C:A | `data-differs` on the unnamed `(.rodata)` target 0x10428 / 0x10438 (region 66360 B vs 66236 B) | a 64-byte int table (the De Bruijn ctz table), read by `neg / and / mul / srli 58 / addi / add / lbu`, so only indices 0..63 | out/probe_tbl.out: the 64 bytes the code can read are byte-identical in the two images; the 65th byte is 00 on both sides; the reading words are the same instructions, the two that hold an address (the `auipc`/`ld` of the constant K at +0xc0/+0xc4 and the `addi` of the table at +0xdc) differing pc-relatively only, and the index bound does not depend on K | SAME, no difference |

No other row of this re-run is of that class: every other target is a name, a C-string acceptance, a .got value or
a GD tls_index, and no row is `target unmeasured`. There is no differing instruction word and no differing named
target anywhere in the 7 pairs, so nothing had to be escalated.

FULL LIST, not the printed output (AGENT TIME: cmpkit's closure_strict2.py:88 and paircl.py:67 print only the
first 2 differing targets per function, so a settlement read off printed lines can hide the rest). fulldiff.py
calls strictcmp2's `tcmp` directly for each of the 7 pairs and prints the whole `diff` list it returns
(out/fulldiff.out). What tcmp returned in full, per row:

| pair | entries in tcmp's full diff list | each accounted for |
| Allocate | 1 (`data-differs` at +0xdc) | settled above |
| CombinedAllocator::Allocate | 0 | - |
| SizeClassAllocator64LocalCache::Refill | 0 | - |
| PoisonShadow | 0 | - |
| internal_mmap | 0 | - |
| StackDepotPut | 0 | - |
| memset | 0 | - |

Total over the 7 pairs: ONE entry, the settled +0xdc row; 0 entries of kind `unmeasured`, `got-unreadable` or
`one-side`. No target of this run is left unmeasured, and no real difference hides behind a truncated printout.

INDEPENDENT AUDIT, ACCEPT (fresh reviewer, AGENT TIME; re-derived from the binaries WITHOUT the kit: capstone
5.0.7, pyelftools 0.33, the same twins ce511d541cda / 4cb0a852e826, both pins equal at every address read). Its
method and numbers: the reader is `auipc` / `ld` of K = 0x0218a392cd3d5dbf at +0xc0 / +0xc4, then `neg` / `and`
(x & -x), `mul`, `srli 58` (funct3 5, imm[11:6] = 0, so logical), `addi` to the table, `add`, `lbu 0`; the extent
read is [T, T+64), 64 bytes, equal in both images; the 64 six-bit windows of K are distinct and T is the
permutation with T[(K << i) >> 58] = i, so T is the ctz table; no branch, jal or indirect jump lands in
(+0xd4, +0xe4]; a2 is not reused for a second read; no symbol overlaps the extent; and the first difference inside
the kit's wider region is at offset 5903, in unrelated strings, unreachable from this read.

### 4.2b The 39 C-string acceptances, audited

The kit accepts an unnamed read-only target as a C string only when every byte before the first NUL is printable and
that NUL is inside the target's region, and it prints one CSTR row per acceptance for exactly this audit (cmpkit
README:149-152, AGENT's ruling). This run has 39: 20 in Allocator::Allocate, 8 in CombinedAllocator::Allocate,
11 in PoisonShadow (the CSTR rows of out/run-strictcmp2.out).

The same fresh reviewer audited all 39 against both images: each string address goes straight into a call argument,
with no branch between the address and the call and with the register never overwritten, and every consumer reads
only up to the NUL — so the rule the kit applied is the rule the code uses.

| consumer | argument | acceptances |
| `CheckFailed` file | a0 | 17 |
| `CheckFailed` condition | a2 | 17 |
| `Report` format | a0 | 2 |
| `RawWrite` message | a0 | 3 |

All 39 stand; none is a listed exception.

### 4.3 The 417 code numerals

out/numerals-kit.tsv re-classifies the word at each numeral's `donor symbol + offset` in the decode copy with bytecmp
1480ca2faea0's own per-word rule (loaded through drvcmp, which sha-checks the bytecmp file), and adds strictcmp2's
verdict for the words that are compared targets.

| | OLD (bytecmp c487b3618415) | NEW (cmpkit 4bbd3a74be89) |
| numerals checked | 417 | 417 |
| word identical in both copies | 390 | 390 |
| word pc-relative only | 27 | 27 |
| real difference | 0 | 0 |
| unmeasured | 0 | 0 |
| strictcmp2 target difference at the numeral's word | (not measurable: no target pass) | 0 |

0 of the 417 classifications changed (out/numerals-kit.out: `changed 0`).

Word counts over the whole 7 functions (same file): Allocate 529 same / 81 pcrel, CombinedAllocator::Allocate 166 /
16, Refill 64 / 0, PoisonShadow 258 / 61, internal_mmap 3 / 0, StackDepotPut 6 / 2, memset 62 / 0; no `real`, no
`unmeasured` word anywhere.

Every numeral's CONSUMER (owner's addition of TIME; columns `consumes_donor_value` / `consumes_decode_value` of
out/numerals-kit.tsv): what the image holds at the numeral's own address, so a size or a mask constant can never be
counted as an address. All 417 land on an instruction of an executable section in BOTH images — branch 196, addi 70,
op-imm 37, jal 22, op 17, jalr 15, fence 14, ld 13, ecall/ebreak/csr 8, lw 8, auipc 5, lbu 4, sb 4, lwu 4 — and none
resolves outside a section or into a data object.

### 4.4 The ecall / AMO / LR / SC words the old record singled out

The old record checked these with bytecmp 475ff6314d3c (ecall / ebreak drop a0 / a1) and 7daa0e2a03d9 (AMO / LR / SC
and FP-to-integer words kill rd). On the kit no such variant is needed: every one of those words is byte-identical in
the two copies (out/numerals-kit.out):

| word | donor | decode A | class |
| Allocate +0x328 `lr` | 1406272f | 1406272f | identical |
| Allocate +0x33c `sc` | 18f627af | 18f627af | identical |
| CombinedAllocator::Allocate +0x1d8 `amo` | 00c5b02f | 00c5b02f | identical |
| internal_mmap +0x4 `ecall` | 00000073 | 00000073 | identical |

Old verdict on all three variant comparers: same verdict, 382 numerals identical or pc-relative only. New: the same,
with no variant rule in play.

## 5. Duplicated names in the two images (funcpair.py d37a0f9a14fb keeps only the FIRST symtab entry per name)

Measured here, not quoted (out/dupnames.out, out/dupzone.out; .symtab AND .dynsym of both images):

| name | donor (cgif twin) STT_FUNC copies | decode A twin STT_FUNC copies | unique? |
| __asan::Allocator::Allocate | 1: 0x31550/2440 | 1: 0x3124c/2440 | yes |
| __sanitizer::CombinedAllocator<…>::Allocate | 1: 0x359e4/728 | 1: 0x357c0/728 | yes |
| __sanitizer::SizeClassAllocator64LocalCache<…>::Refill | 1: 0x36134/256 | 1: 0x35f10/256 | yes |
| __asan::PoisonShadow | 1: 0x53800/1276 | 1: 0x53040/1276 | yes |
| __sanitizer::internal_mmap | 1: 0x64198/12 | 1: 0x63d3c/12 | yes |
| __sanitizer::StackDepotPut | 1: 0x724e0/32 | 1: 0x72084/32 | yes |
| memset (STB_WEAK) | 1: 0x9790c/248 | 1: 0x92474/248 | yes |

Neither image has a .dynsym (both are static), so .symtab is the whole table; no other symbol type carries any of
the 7 names. For every name there is exactly ONE same-size candidate in decode A, so there is nothing to choose
between: strictcmp2 at that candidate gives the verdicts of 4.1 (and for Allocate the one settled row of 4.2). Two
EQUAL candidates cannot arise here.

Decode A does have duplicated STT_FUNC names, and they are listed so the funcpair defect can be bounded:
`_ZN6__asanL11MemToShadowEm` at 0x3aff4 / 0x3c824 / 0x51cb8 / 0x5353c / 0x5c678 (all 316 B — same size, so a
first-entry lookup could take the wrong one) and `dummy` at 0x87e38 / 0x88808 / 0x8dc18 / 0x94694 / 0x94cd0 (4 B);
the donor has the same two names duplicated (MemToShadow x5, dummy x6). NO numeral of this record lies in any of
those 10 decode-A ranges: neither any of the 417 re-run numerals (45 distinct placed values) nor any of the 532
citations of the 47 released headers (59 distinct decode values) (out/dupzone.out). The funcpair name-table defect
therefore cannot have mis-selected a copy for anything this record covers.

FUNCPAIR NAME CHECK: unique 7 / duplicated 0 ()

## 6. Every numeral the 47 released headers cite (hub 88154566652a)

Scope: at commit 88154566652a (Merge pull request #412: Pau proofs (libreac/fuzz_decode)) 47 shipped .v files say
`its N image addresses moved by code-verified function pairs (N port_addr_check 0767e70e074a MAPS predictions, each
code one re-derived by funcpair.py; K code pcs the tool read as sizes, by funcpair.py)`, and some add `and C pcs
named in comments`. The addresses themselves are the changed numerals of the file, with file:line, in the
relocation's own numdiff table (allocreloc/numdiff.tsv). out/resolve-kit.tsv lists ALL 532 of them, one row per
citation: file, src_line, donor value, decode value, kind, whether a proof term or a comment reads it, the symbol +
offset each value resolves to in its OWN image's .symtab, how many symbols of decode A carry that name, the class of
the instruction word at the two addresses, whether this re-run's funcpair numeral set covers it, and the category.

Checks applied to each (out/resolve-kit.out):
- resolve both values in their own image's .symtab (smallest containing FUNC / OBJECT symbol) and require the SAME
  symbol + offset on both sides;
- for a code pc, read the instruction word at both addresses and require identical or pc-relative-only (the word the
  proof's own site reads);
- for a value with no symbol: an ASan shadow address must be shadow(x) = x / 8 + 0x7fff8000 of a decode-A boundary
  (shadow_off, img_lo 0x10000 and img_hi 0x5f6000 are decode A's own, lib/A/AB12.v's TFIB record at this commit), and
  a segment extent must be a decode-A PT_LOAD boundary;
- flag any numeral inside a function whose name decode A carries more than once (section 5).

Result over the 532 citations (code 375, data 96, extent 16, non-address 8, comment 37):

| category | count |
| (a) used by a proof term and RIGHT | 495 |
| (b) used by a proof term and WRONG | 0 |
| (c) not read by any proof term (comment only) | 37 |
| in a function whose name has several copies in decode A | 0 |

No numeral is wrong. The two values that needed the shadow rule are `0x80050000 -> 0x800b6c00` (AGif0cgif.v:64 and
AGix.v:44, the upper bound of the shadow band in `CZONE` and `abs_cell_ok`): 0x800b6c00 = 0x5f6000 / 8 + 0x7fff8000,
the shadow of decode A's own image top 0x5f6000, which is the bound used in the same disjunct — right. (The
relocation's own numdiff line carries a different MAPS prediction, 0x8004f568, for them: the prediction anchored on
shadow(theDepot+0x137ea8), the writer used shadow(img_hi). The placed value is the correct one for the term.)

Coverage by this re-run's function-pair pass: of the 495 cited addresses read by a term, 383 are numerals the
relocation mapped through one of the 7 function pairs, i.e. they are in the 417 re-checked here. The other 112 are
not function-pair numerals and are covered by the resolution check above instead: 84 data addresses
(`__sanitizer::stackStore+0x0` 38+2, `__sanitizer::useCounts+0x30008` 18, `read_stage+0x0` 12+4, `builtin_tls+0xd8`
4, `__pthread_tsd_main+0x0` 4, `InitializeCommonInterceptors::metadata_mem+0x8` 4, `__asan::kSuppressionTypes+0x0` 2,
`__asan::asan_flags_dont_use_directly+0x28` 2), 16 segment extents (`EXTENT(val:image.top, val:seg3.hi)` 9,
`EXTENT(val:seg1.hi)` 7), 8 non-address values (the 2 shadow bounds above and the 4 `builtin_tls` TFIB_TP decimals
plus 2 further decimal literals). Not one of the 112 is a code pc, so the headers' claim `each code one re-derived
by funcpair.py` is fully inside what this re-run re-checked.

### 6.1 The 37 citations NO proof term reads (category (c))

These are image addresses inside `(* … *)` comments of the shipped files. A wrong value there is a false RECORD, not
a false theorem: each proof is Qed against decode A's own image, so a comment numeral is never read by a term. All
37 resolve correctly here as well, so nothing needs fixing; if one ever does, the fix is comments-only and belongs to
the file's writer (WORKER) in fuzz_decode's DATE post-ship series — this record changes no shipped file.

By file (line numbers are the shipped files' own): AGc0:6,8,9x3,10,11,31,32,41 (10); AGc1:6,8x2,9,171x2,180x2 (8);
AGc2:6,8x2,166x2 (5); AGi0:37x2,38 (3); AGi2:78x2 (2); AGif0cgif:57x3 (3); AGir:613 (1); AGj4:558 (1); AGj9:279 (1);
AGtop:6,58 (2); AllocGcgif:1 (1). The values are the Allocate-chain pcs 0x31bf4/0x31bf8/0x31be8/0x31c30/0x31cc0 and
the function start 0x31550 (moved to 0x318f0 / 0x318f4 / 0x318e4 / 0x3192c / 0x319bc / 0x3124c), and AGif0cgif:57's
three cgif globals 0xa0098 / 0xa3aa0 / 0xa2c18 (moved to 0x9abc0 / 0x9e5e0 / 0x9d758).

One bookkeeping mismatch, prose only: AGif0cgif.v's header says 0 pcs named in comments while numdiff lists 3 (the
line-57 globals). The prose fix that moved them (provenance/alloc-reloc/A/fix_prose.py, 1e58b7cb018) ran after the
header sentence was written. No term is affected.

## 7. Verdict

VERDICT CHANGED: no

- Every one of the 7 pair verdicts is the old one (3 EQUAL, 4 EQUAL-mod-pcrel), with the same pcrel / real /
  unmeasured counts; 0 DIFFERENT, 0 UNMEASURED.
- All 417 numeral classifications are the old ones (390 identical, 27 pc-relative only); 0 real, 0 unmeasured, 0
  target differences; every one of them consumes a real instruction in both images.
- The 4 singled-out ecall / AMO / LR / SC words are byte-identical, as before.
- All 495 term-read addresses the 47 released headers cite are right; 37 comment-only citations are right too; no
  numeral lies in a duplicated-name function.
- New, and not a verdict change: the kit has a target pass the old comparer did not, and it reports ONE row,
  Allocate +0xdc, of its own KNOWN FALSE-DIFFERENCE class. It is settled by hand in 4.2 with a separate measurement
  (the 64-byte De Bruijn table is byte-identical and the index is bounded to it); it is not counted as a kit EQUAL.

No proof file, theorem or axiom set is touched by this re-run.

FUNCPAIR NAME CHECK: unique 7 / duplicated 0 ()

## 8. By NAME or by ADDRESS (AGENT TIME: `strictcmp2 cmp` looks a function up by name and, for a local name
with several copies, silently takes the LOWEST address)

The run of record passed the 7 pairs BY NAME (`strictcmp2.py cmp FNLIST C=.. A=.. C:A`). Measured again from the
binaries, not from this file's prose (out/nmcount.out; this host has no binutils, so the .symtab is read with
pyelftools and every symbol of the exact name is counted, any type, as `nm IMG | grep -c ' NAME$'` would):

| name | entries in the donor twin ce511d541cda | entries in the decode A twin 4cb0a852e826 | addresses | by-NAME verdict | by-ADDRESS verdict |
| __asan::Allocator::Allocate | 1 | 1 | 0x31550 / 0x3124c | EQUAL-mod-pcrel (81,0,0), 1 settled row | identical |
| __sanitizer::CombinedAllocator<…>::Allocate | 1 | 1 | 0x359e4 / 0x357c0 | EQUAL-mod-pcrel (16,0,0), 0 | identical |
| __sanitizer::SizeClassAllocator64LocalCache<…>::Refill | 1 | 1 | 0x36134 / 0x35f10 | EQUAL, 0 | identical |
| __asan::PoisonShadow | 1 | 1 | 0x53800 / 0x53040 | EQUAL-mod-pcrel (61,0,0), 0 | identical |
| __sanitizer::internal_mmap | 1 | 1 | 0x64198 / 0x63d3c | EQUAL, 0 | identical |
| __sanitizer::StackDepotPut | 1 | 1 | 0x724e0 / 0x72084 | EQUAL-mod-pcrel (2,0,0), 0 | identical |
| memset | 1 | 1 | 0x9790c / 0x92474 | EQUAL, 0 | identical |

Every count is 1 on BOTH sides, so the lowest-address rule never chose anything: the name lookup returns exactly the
addresses of record, and no pair needed a by-address re-run. It was run anyway, with strictcmp2's own tcmp at the
record addresses: every by-ADDRESS verdict equals its by-NAME verdict, counts included. NO VERDICT CHANGES.

## 9. Files here

- run.sh — the whole re-run, from extracting the kit to the last check.
- symcheck.py, numerals.py, probe_tbl.py, ownctl.py, dupnames.py, headers.py, resolve.py, dupzone.py, nmcount.py,
  fulldiff.py — the steps that are not a bare kit invocation.
- out/twins.out, out/negctl-mine.out, out/ownctl.out, out/run-strictcmp2.out, out/symcheck.out, out/numerals-kit.out,
  out/numerals-kit.tsv, out/probe_tbl.out, out/dupnames.out, out/dupzone.out, out/headers.out, out/resolve-kit.out,
  out/resolve-kit.tsv, out/nmcount.out, out/fulldiff.out — this run's outputs.
