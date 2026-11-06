# fuzz_state code values: evidence (vet-clean form)

Unit-relative paths (lib/...). Images: fuzz_state.asan sha256 64b53ff86172..., fuzz_state.asan-ubsan 5ac5ce0954f8...,
each read through its unstripped twin's .symtab (PT_LOAD bytes equal to the pin except the ELF header and build-id).

## tbl_icpt range counts (lib/A/AE34.v:22, :26; lib/B/YE34.v:22, :26)

Each range `(lo, n%nat)` covers n code words from lo. Two ranges kept the donor's word counts:
- A/AE34.v:22 `(0x92204, 435%nat)` -> `(0x92204, 383%nat)`: the range runs from `__stdio_write` to 28 bytes into
  `__stdio_exit`, as in the donor (donor range `(0x92cec, 435)`, same end function and offset); in image A that end is
  0x92204 + 4 * 383.
- A/AE34.v:26 `(0x42654, 38%nat)` -> `(0x42654, 36%nat)`: the range ends at the start of
  `___interceptor_strlen` (alias `__interceptor_strlen`) in both images; in image A that is 0x42654 + 4 * 36.
- B/YE34.v:22 and :26: the same two ranges at image B's addresses (0x92720, 383) and (0x426c4, 36).
Every other `(lo, n%nat)` code range of the relocated files was recomputed the same way: 124 equal, 5 not linkable by
name and read by hand (whole functions or ranges ending at a function end).

## Depot TOT bound (lib/A/AFem.v:118, :196; lib/B/YFem.v:115, :193)

`2 <= TOT <= 634974` -> `2 <= TOT <= 634912`, where 634912 = 31 + 1 + 31 * DEPOT_CAP:
- TOT := Z.of_nat (length (ly_tr0 ly)) + 1 + depot_frames S (A/AFem.v:89; B/YFem.v the same text);
- length (ly_tr0 ly) <= 31 (Reusable/YG0f.v:324, lo_tr0);
- depot_frames <= 31 * length d (Reusable/YG01.v:177, depot_inv_frames);
- length d <= DEPOT_CAP (Reusable/YG01.v:175, depot_inv_cap), DEPOT_CAP := 20480 (Reusable/YG01.v:150).
The old 634974 (= 32 + 31 * 20482) was true but weaker. A goal position: the TOT_range proofs check the new value.

## aTOT atom range (lib/A/AFek.v:35, lib/B/YFek.v:35): kept

aTOT `mkAF 2 634974 0` (A/AFek.v:35, B/YFek.v:35) is kept byte-equal to the donor. It is TRUE: the atom is env slot 34
(aTOT, K_D = 42, A/AFek.v:28 / :30), which denotes TOT (U34, A/AFem.v:240; envD fixes slots below K_D, :230, kept
across havocs, :232-233), and 2 <= TOT <= 634912 by TOT_range (A/AFem.v:118). It is BUILD-CHECKED: discharged from
TOT's bound by lia at A/AFem.v:259, :358, :398 (B/YFem.v:256, :355, :395).
Separately, the memory cell R_TOT (A/AFek.v:47, cell8 TFIB_STORE aTOT) receives TOT + length tr + 1 at the store
(A/AFem.v:1236 / B/YFem.v:1233; tr_len A/AFem.v:112 / B/YFem.v:109), at most 634943: a bound on the memory word only.

## All atom ranges of lib/A/AFek.v and lib/B/YFek.v (both files identical row for row)

23 `mkAF` occurrences per file: the definition of u64f (:31, `mkAF 0 (2 ^ 64 - 1) 0`) and 22 ranged atom rows. With
the 26 atom rows that use u64f, that is 48 atom rows, in 7 fact lists:

| list (A/AFek.v line) | ranged rows | u64f rows | discharged in (A/AFem.v; B/YFem.v) |
|---|---|---|---|
| DF_fixed (:33-36) | 12: atoms 2, 10, 11, aNB, aSB, aTOT, aN, aS2, aHD, aSTD, aNDN, aSLOT | 1: aHASH | FACTS_fixed :386-410; :383-407 |
| HATOMS (:67) | 2: dP, dE | 4: dW, dH, 46, 47 | reabs_H :615 (dP :646, dE :648); :612 (:643, :645) |
| BATOMS (:80) | 0 | 6: 42-47 | reabs_B :667; :664 |
| FLATOMS (:90) | 1: aID | 5: 46-50 | reabs_FL :786 (aID :806); :783 (:803) |
| FATOMS (:93) | 3: aID, aND, aNL | 4: aNH, 46, 47, 48 | reabs_FN :836 (:862-866); :833 (:859-863) |
| MCATOMS (:129) | 4: aSC, aDC, aME, aBY | 2: 46, 48 | reabs_MC :1326 (:1357-1360); :1323 (:1354-1357) |
| ENDF (:146) | 0 | 4: 42-45 | reabs_END :1245; :1242 |

- (1) Proved at both ends from fs's own facts: 48 of 48. Each ranged row is a proof obligation closed by `AFo ... lia`:
  DF_fixed from zone_facts (A/AFem.v:190-197: length tr <= 30, 1 <= nD <= 20481, 2 <= TOT <= 634912, 0 <= bkt <
  1048576, 0 <= HDv <= nD, 0 <= STD < 2 ^ 32, the NB / SB / sp / buf bounds and alignments); HATOMS' dP / dE from the
  buf bounds and alignment (zone_facts) with i < length tr; FLATOMS' aID from reabs_FL's premise 0 <= cur <= 20481;
  FATOMS' rows from 1 <= cur <= nD and the NB bounds; MCATOMS' rows from 0 <= j < 8 * length tr and the buf / SLOT
  bounds. Each u64f row (the full 64-bit range) is closed by JKf (A/AFem.v:583, B/YFem.v the same lemma) from
  u64_range, which holds for every 64-bit word; aHASH by AFo from 0 <= HSH < 2 ^ 64. The tops that use these walks are
  closed (Print Assumptions: allowed axioms only), so a range excluding a reachable value would fail the build.
- (2) Relocated address bounds checked by symbol: 0 in these rows (their bounds are named constants: kHighMemBeg,
  kHighMemEnd, CEIL_MAX, TFIB_DEPOT, DEP_STK, the block sizes).
- (3) Not checkable from a lemma: 0.
lib/B/YFek.v holds the same 48 rows on the same lines. Every row is byte-equal to the shipped tree (none changed).

## YH03 cells (lib/Reusable/YH03.v, lib/U/Reusable/YH03.v), with the FILE-sink restatement

Dropped, each false and unread after the restatement: src0_A/E_stdio_read (neither image has `__stdio_read`; the pair
had E below A), src0_D_str_wb, src0_D_str_tmp_out_gif, src0_D_str_3, src0_D_str_rwa (the bytes at those addresses in
both images are other strings). Kept, each true and unread: src0_A/E_stdio_write, _stdio_seek, _stdio_close (each equals
the named function's st_value / st_value + st_size in its image's own unstripped ELF). yh03check v6.4 fb3bfbc1eea8
--pinned on both copies: rc 0, `# rows checked: 105; rows not OK: 0`, 18 of 18 section cells.
