# Triage of the e165 symbol-gate rows: reac-repacer/fuzz_uci image-A core relocation

role: check. rule 24: no function proved. Read-only re-run of the gate and diff against the cb0e record. Nothing outside this directory was changed.

## Result

- Gate: port_addr_check.py sha256 e165063a00810b376b9f65ef3da645c11eed0e22e6b50b2ae10db97ccc6b2d3b (`--paired-only --fail-on-flags --summary`, fresh cache). Its summary lines: `gate-e165-flagged.txt`. Exit 4 (flags present).
- `FLAGGED 306 rows in 9 classes: DIFFERENT-SYMBOL=1 GEOMETRY-CHANGED=9 KIND-CHANGED=9 NO-COUNTERPART=1 NON-ADDRESS-CHANGED=174 STALE-DONOR-CODE-POINTER=1 UNPAIRED-PORTED=19 UNPAIRED-SOURCE=84 UNRESOLVED=8`
- FLAG-CLASSES 575d398c6022 (the same set as the cb0e run).
- GENERATOR-FILL: 6 (REPORTED, not counted by `--fail-on-flags`); the same 6 rows as cb0e.
- **DEFECTS: none.** No new row and no moved row has an address role; no flagged row has a wrong dst value.
- Against the cb0e record (`gate-cb0e-TRIAGE.md` sha256 18266ed2dcc6, `gate-cb0e-triage-rows.tsv` sha256 fd098d9c8fb3): 302 flagged rows and 6 GENERATOR-FILL rows unchanged, 4 new, 0 moved, 66 gone.
- One row per line (unchanged, new and gone, with reason id): `gate-e165-triage-rows.tsv` in this directory. `e165_raw_line` is the line in this run's `raw.tsv`, `cb0e_raw_line` the line in the cb0e `raw.tsv`.

| class | cb0e FLAGGED | e165 FLAGGED | unchanged | new | moved | gone |
|---|---:|---:|---:|---:|---:|---:|
| DIFFERENT-SYMBOL | 1 | 1 | 1 | 0 | 0 | 0 |
| GEOMETRY-CHANGED | 9 | 9 | 9 | 0 | 0 | 0 |
| KIND-CHANGED | 9 | 9 | 9 | 0 | 0 | 0 |
| NO-COUNTERPART | 1 | 1 | 1 | 0 | 0 | 0 |
| NON-ADDRESS-CHANGED | 174 | 174 | 174 | 0 | 0 | 0 |
| SAME-VALUE-DIFFERENT-OBJECT | 20 | 0 | 0 | 0 | 0 | 20 |
| STALE-DONOR-CODE-POINTER | 1 | 1 | 1 | 0 | 0 | 0 |
| UNPAIRED-PORTED | 40 | 19 | 15 | 4 | 0 | 25 |
| UNPAIRED-SOURCE | 105 | 84 | 84 | 0 | 0 | 21 |
| UNRESOLVED | 8 | 8 | 8 | 0 | 0 | 0 |
| total flagged | 368 | 306 | 302 | 4 | 0 | 66 |
| GENERATOR-FILL (REPORTED) | 6 | 6 | 6 | 0 | 0 | 0 |

## How the two runs were compared

- Row key: (src file, src line, dst file, dst line, sentence, idx, kind, src value, dst value), matched as a multiset (15 cb0e keys and 7 e165 keys occur more than once; rows with the same class pair first). NEW = an e165 flagged row whose key has no cb0e row. MOVED = same key, other class. GONE = a cb0e flagged row whose key has no e165 row, or whose e165 row has an unflagged class (none of the second kind).
- Line numbers are comparable. The cb0e run read `work10/stage` and `work10/stage-out`; this run read `work16/stage` and `work16/stage-out`. Measured (diff):
  - src: every file of `work10/stage/A` is byte-identical in `work16/stage/A`. `work16/stage` adds `A/AD1q.v` and has no `Reusable/` (206 files that cb0e read).
  - dst: every file of `work10/stage-out/A` equals its `work16/stage-out/A` twin once the date is taken out of the `Modified by Theorem Labs` notices (same line count). `work16/stage-out` adds `A/AD1q.v` and has no `Reusable/`.
  - dst = the committed lib: all 364 `.v` files of `work16/stage-out/A` have the git blob id of `proofs/reac-repacer/fuzz_uci/lib/A/<file>` at commit 7f39d662ad6c (git hash-object against git ls-tree). The 20 other files of that lib/A (AB01, AB03, AB05, AB12, AB13, AB1h, AB1k, AB1l, AB1m, AB1v, ACej, AD1k, AD1y, AD2i, AD2j, AE23, AE37, AE3i, AF0m, RelimCut) are the start-up layer, not staged, as in cb0e.
  - Text listing ids (sha256 of the sorted `<git blob id>\t<file name>` lines): stage 45c940f0a4a8, stage-out e2f712164819.
- Images: the same as cb0e. src `fuzz_grant.asan` sha256 c2c7559b29bd (symbols recovered from 28 donors; the same recovery counts), dst `fuzz_uci.asan` sha256 6ea017c24525 (symtab of the unstripped twin 56822e263d76). 1980 / 1965 symbols on both runs.
- Control run (same tool, same images; text = the record's A/ plus `Reusable/`: src from `work10/stage/Reusable`, dst = the committed `lib/Reusable/` files at 7f39d662ad6c of the same 206 names): `FLAGGED 326 rows in 10 classes: DIFFERENT-SYMBOL=1 GEOMETRY-CHANGED=9 KIND-CHANGED=9 NO-COUNTERPART=1 NON-ADDRESS-CHANGED=174 SAME-VALUE-DIFFERENT-OBJECT=20 STALE-DONOR-CODE-POINTER=1 UNPAIRED-PORTED=19 UNPAIRED-SOURCE=84 UNRESOLVED=8`. Its 157909 A/ rows are equal, key and class, to this run's 157909 rows; its Reusable/ flagged rows are the cb0e run's 20 SAME-VALUE-DIFFERENT-OBJECT rows, key for key. So:
  - the 20 gone SAME-VALUE-DIFFERENT-OBJECT rows are gone because the record stages A/ only, not because of the tool change;
  - this run reads 0 constructor field-role declarations (cb0e and the control read 187, all in Reusable/), and that changes no A/ row.

## What changed in the tool, and which rows it touched

- Sentences anchored on identical text (`pair_sentences`: difflib over the sentence texts first, the (kind, name, occurrence) key only for what no anchor placed). It changes rows in three files only, all inside hunks of zero-shadow-forallb.patch: A/AFex.v, A/AFfl.v, A/AFjy.v. It removes 46 PATCH-ZS rows (21 UNPAIRED-SOURCE, 25 UNPAIRED-PORTED) and adds 4 UNPAIRED-PORTED rows (below).
- Positional GENERATOR-FILL only where the donor row's named object is absent from the target: the same 6 rows stay GENERATOR-FILL (observation below).
- A definition named after a target symbol must carry that symbol's address: no row of this tree changes class (no MOVED row, and no unflagged row of A/ changes class either).

## NEW rows (4)

Reason: PATCH-ZS (zero-shadow-forallb.patch, the reason of gate-cb0e-TRIAGE.md). The patch replaces the 15-way `destruct Hr` case split of grant (15 Tfib_zero_shadow ranges) with one `forallb` check over fuzz_uci's 3 ranges.

| e165 raw line | class | dst file:line | sentence (idx) | dst value | reason | measurement |
|---:|---|---|---|---|---|---|
| 120 | UNPAIRED-PORTED | A/AFex.v:940 | Lemma zshadow' / sentence 36 (-) | 0x8 | PATCH-ZS | dst A/AFex.v:940 is `{ assert (CK : forallb (fun r0 : Z * Z => andb (andb (Z.eqb (fst r0 mod 8) 0) ...) Tfib_zero_shadow = true) by (vm_compute; reflexivity).`, a + line of zero-shadow-forallb.patch (sha256 8865b6699d8d); no line of the src file has this text. Literal 8 (the shadow granule in `fst r0 mod 8`): no address role. cb0e paired this sentence by key with src 938 (`assert (R8 : ... lo mod 8 = 0 ...)`, another text) and called it NON-ADDRESS-SAME; e165 pairs src 938 with dst 939, its identical text, so dst 940 has no partner |
| 121 | UNPAIRED-PORTED | A/AFex.v:940 | Lemma zshadow' / sentence 36 (-) | 0x0 | PATCH-ZS | dst A/AFex.v:940 is `{ assert (CK : forallb (fun r0 : Z * Z => andb (andb (Z.eqb (fst r0 mod 8) 0) ...) Tfib_zero_shadow = true) by (vm_compute; reflexivity).`, a + line of zero-shadow-forallb.patch (sha256 8865b6699d8d); no line of the src file has this text. Literal 0 (the remainder in `Z.eqb (fst r0 mod 8) 0`): no address role. cb0e paired this sentence by key with src 938 (`assert (R8 : ... lo mod 8 = 0 ...)`, another text) and called it NON-ADDRESS-SAME; e165 pairs src 938 with dst 939, its identical text, so dst 940 has no partner |
| 128 | UNPAIRED-PORTED | A/AFfl.v:830 | Lemma zshadow' / sentence 36 (-) | 0x8 | PATCH-ZS | dst A/AFfl.v:830 is `{ assert (CK : forallb (fun r0 : Z * Z => andb (andb (Z.eqb (fst r0 mod 8) 0) ...) Tfib_zero_shadow = true) by (vm_compute; reflexivity).`, a + line of zero-shadow-forallb.patch (sha256 8865b6699d8d); no line of the src file has this text. Literal 8 (the shadow granule in `fst r0 mod 8`): no address role. cb0e paired this sentence by key with src 828 (`assert (R8 : ... lo mod 8 = 0 ...)`, another text) and called it NON-ADDRESS-SAME; e165 pairs src 828 with dst 829, its identical text, so dst 830 has no partner |
| 129 | UNPAIRED-PORTED | A/AFfl.v:830 | Lemma zshadow' / sentence 36 (-) | 0x0 | PATCH-ZS | dst A/AFfl.v:830 is `{ assert (CK : forallb (fun r0 : Z * Z => andb (andb (Z.eqb (fst r0 mod 8) 0) ...) Tfib_zero_shadow = true) by (vm_compute; reflexivity).`, a + line of zero-shadow-forallb.patch (sha256 8865b6699d8d); no line of the src file has this text. Literal 0 (the remainder in `Z.eqb (fst r0 mod 8) 0`): no address role. cb0e paired this sentence by key with src 828 (`assert (R8 : ... lo mod 8 = 0 ...)`, another text) and called it NON-ADDRESS-SAME; e165 pairs src 828 with dst 829, its identical text, so dst 830 has no partner |

The cb0e run had these 4 numerals as NON-ADDRESS-SAME (cb0e raw lines 99180, 99181 for A/AFex.v; 105742, 105743 for A/AFfl.v), paired with the R8 line two lines up in the src. That pairing was the key rule's, between two different texts; the new pairing is the correct one, and the values have no address role either way.

## MOVED rows (0)

No row keeps its key and changes class: none of the flagged rows, none of the GENERATOR-FILL rows, and none of the other rows of A/ whose key both runs have (157876 rows in all keep their class).

## GONE rows (66)

### PATCH-ZS rows now paired by identical text (46: UNPAIRED-SOURCE 21, UNPAIRED-PORTED 25)

cb0e's reason for each: `same text, sentence index shifted` (the patch adds sentences, so the key rule could not pair these lines). e165 pairs each with its identical line and classes it NON-ADDRESS-SAME (8 = 8, 0 = 0). Each cb0e UNPAIRED-SOURCE row and the cb0e UNPAIRED-PORTED row of its identical dst line became one paired row; the 4 UNPAIRED-PORTED rows of dst A/AFex.v:939 and A/AFfl.v:829 pair with src 938 / 828.

| cb0e raw line | cb0e class | file | src line | dst line | sentence | value | cb0e reason | e165 (measured) |
|---:|---|---|---:|---:|---|---|---|---|
| 120 | UNPAIRED-SOURCE | A/AFex.v | 942 | - | Lemma zshadow' / sentence 42 | 0x8 | PATCH-ZS | now paired by identical text: src 942 = dst 945 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 99124; literal 8 |
| 121 | UNPAIRED-SOURCE | A/AFex.v | 943 | - | Lemma zshadow' / sentence 45 | 0x8 | PATCH-ZS | now paired by identical text: src 943 = dst 946 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99125, 99126, 99127; literal 8 |
| 122 | UNPAIRED-SOURCE | A/AFex.v | 943 | - | Lemma zshadow' / sentence 45 | 0x8 | PATCH-ZS | now paired by identical text: src 943 = dst 946 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99125, 99126, 99127; literal 8 |
| 123 | UNPAIRED-SOURCE | A/AFex.v | 943 | - | Lemma zshadow' / sentence 45 | 0x8 | PATCH-ZS | now paired by identical text: src 943 = dst 946 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99125, 99126, 99127; literal 8 |
| 124 | UNPAIRED-SOURCE | A/AFex.v | 944 | - | Lemma zshadow' / sentence 49 | 0x8 | PATCH-ZS | now paired by identical text: src 944 = dst 947 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 99128; literal 8 |
| 125 | UNPAIRED-SOURCE | A/AFex.v | 946 | - | Lemma zshadow' / sentence 52 | 0x8 | PATCH-ZS | now paired by identical text: src 946 = dst 949 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99129, 99130, 99131, 99132; literal 8 |
| 126 | UNPAIRED-SOURCE | A/AFex.v | 946 | - | Lemma zshadow' / sentence 52 | 0x8 | PATCH-ZS | now paired by identical text: src 946 = dst 949 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99129, 99130, 99131, 99132; literal 8 |
| 127 | UNPAIRED-SOURCE | A/AFex.v | 946 | - | Lemma zshadow' / sentence 52 | 0x8 | PATCH-ZS | now paired by identical text: src 946 = dst 949 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99129, 99130, 99131, 99132; literal 8 |
| 128 | UNPAIRED-SOURCE | A/AFex.v | 946 | - | Lemma zshadow' / sentence 52 | 0x8 | PATCH-ZS | now paired by identical text: src 946 = dst 949 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99129, 99130, 99131, 99132; literal 8 |
| 129 | UNPAIRED-PORTED | A/AFex.v | - | 939 | Lemma zshadow' / sentence 35 | 0x8 | PATCH-ZS | now paired by identical text: src 938 = dst 939 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 99122; literal 8 |
| 130 | UNPAIRED-PORTED | A/AFex.v | - | 939 | Lemma zshadow' / sentence 35 | 0x0 | PATCH-ZS | now paired by identical text: src 938 = dst 939 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 99123; literal 0 |
| 131 | UNPAIRED-PORTED | A/AFex.v | - | 945 | Lemma zshadow' / sentence 50 | 0x8 | PATCH-ZS | now paired by identical text: src 942 = dst 945 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 99124; literal 8 |
| 132 | UNPAIRED-PORTED | A/AFex.v | - | 946 | Lemma zshadow' / sentence 53 | 0x8 | PATCH-ZS | now paired by identical text: src 943 = dst 946 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99125, 99126, 99127; literal 8 |
| 133 | UNPAIRED-PORTED | A/AFex.v | - | 946 | Lemma zshadow' / sentence 53 | 0x8 | PATCH-ZS | now paired by identical text: src 943 = dst 946 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99125, 99126, 99127; literal 8 |
| 134 | UNPAIRED-PORTED | A/AFex.v | - | 946 | Lemma zshadow' / sentence 53 | 0x8 | PATCH-ZS | now paired by identical text: src 943 = dst 946 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99125, 99126, 99127; literal 8 |
| 135 | UNPAIRED-PORTED | A/AFex.v | - | 947 | Lemma zshadow' / sentence 57 | 0x8 | PATCH-ZS | now paired by identical text: src 944 = dst 947 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 99128; literal 8 |
| 136 | UNPAIRED-PORTED | A/AFex.v | - | 949 | Lemma zshadow' / sentence 60 | 0x8 | PATCH-ZS | now paired by identical text: src 946 = dst 949 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99129, 99130, 99131, 99132; literal 8 |
| 137 | UNPAIRED-PORTED | A/AFex.v | - | 949 | Lemma zshadow' / sentence 60 | 0x8 | PATCH-ZS | now paired by identical text: src 946 = dst 949 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99129, 99130, 99131, 99132; literal 8 |
| 138 | UNPAIRED-PORTED | A/AFex.v | - | 949 | Lemma zshadow' / sentence 60 | 0x8 | PATCH-ZS | now paired by identical text: src 946 = dst 949 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99129, 99130, 99131, 99132; literal 8 |
| 139 | UNPAIRED-PORTED | A/AFex.v | - | 949 | Lemma zshadow' / sentence 60 | 0x8 | PATCH-ZS | now paired by identical text: src 946 = dst 949 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 99129, 99130, 99131, 99132; literal 8 |
| 146 | UNPAIRED-SOURCE | A/AFfl.v | 832 | - | Lemma zshadow' / sentence 42 | 0x8 | PATCH-ZS | now paired by identical text: src 832 = dst 835 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 105695; literal 8 |
| 147 | UNPAIRED-SOURCE | A/AFfl.v | 833 | - | Lemma zshadow' / sentence 45 | 0x8 | PATCH-ZS | now paired by identical text: src 833 = dst 836 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105696, 105697, 105698; literal 8 |
| 148 | UNPAIRED-SOURCE | A/AFfl.v | 833 | - | Lemma zshadow' / sentence 45 | 0x8 | PATCH-ZS | now paired by identical text: src 833 = dst 836 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105696, 105697, 105698; literal 8 |
| 149 | UNPAIRED-SOURCE | A/AFfl.v | 833 | - | Lemma zshadow' / sentence 45 | 0x8 | PATCH-ZS | now paired by identical text: src 833 = dst 836 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105696, 105697, 105698; literal 8 |
| 150 | UNPAIRED-SOURCE | A/AFfl.v | 834 | - | Lemma zshadow' / sentence 49 | 0x8 | PATCH-ZS | now paired by identical text: src 834 = dst 837 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 105699; literal 8 |
| 151 | UNPAIRED-SOURCE | A/AFfl.v | 836 | - | Lemma zshadow' / sentence 52 | 0x8 | PATCH-ZS | now paired by identical text: src 836 = dst 839 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105700, 105701, 105702, 105703; literal 8 |
| 152 | UNPAIRED-SOURCE | A/AFfl.v | 836 | - | Lemma zshadow' / sentence 52 | 0x8 | PATCH-ZS | now paired by identical text: src 836 = dst 839 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105700, 105701, 105702, 105703; literal 8 |
| 153 | UNPAIRED-SOURCE | A/AFfl.v | 836 | - | Lemma zshadow' / sentence 52 | 0x8 | PATCH-ZS | now paired by identical text: src 836 = dst 839 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105700, 105701, 105702, 105703; literal 8 |
| 154 | UNPAIRED-SOURCE | A/AFfl.v | 836 | - | Lemma zshadow' / sentence 52 | 0x8 | PATCH-ZS | now paired by identical text: src 836 = dst 839 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105700, 105701, 105702, 105703; literal 8 |
| 155 | UNPAIRED-PORTED | A/AFfl.v | - | 829 | Lemma zshadow' / sentence 35 | 0x8 | PATCH-ZS | now paired by identical text: src 828 = dst 829 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 105693; literal 8 |
| 156 | UNPAIRED-PORTED | A/AFfl.v | - | 829 | Lemma zshadow' / sentence 35 | 0x0 | PATCH-ZS | now paired by identical text: src 828 = dst 829 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 105694; literal 0 |
| 157 | UNPAIRED-PORTED | A/AFfl.v | - | 835 | Lemma zshadow' / sentence 50 | 0x8 | PATCH-ZS | now paired by identical text: src 832 = dst 835 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 105695; literal 8 |
| 158 | UNPAIRED-PORTED | A/AFfl.v | - | 836 | Lemma zshadow' / sentence 53 | 0x8 | PATCH-ZS | now paired by identical text: src 833 = dst 836 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105696, 105697, 105698; literal 8 |
| 159 | UNPAIRED-PORTED | A/AFfl.v | - | 836 | Lemma zshadow' / sentence 53 | 0x8 | PATCH-ZS | now paired by identical text: src 833 = dst 836 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105696, 105697, 105698; literal 8 |
| 160 | UNPAIRED-PORTED | A/AFfl.v | - | 836 | Lemma zshadow' / sentence 53 | 0x8 | PATCH-ZS | now paired by identical text: src 833 = dst 836 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105696, 105697, 105698; literal 8 |
| 161 | UNPAIRED-PORTED | A/AFfl.v | - | 837 | Lemma zshadow' / sentence 57 | 0x8 | PATCH-ZS | now paired by identical text: src 834 = dst 837 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw line 105699; literal 8 |
| 162 | UNPAIRED-PORTED | A/AFfl.v | - | 839 | Lemma zshadow' / sentence 60 | 0x8 | PATCH-ZS | now paired by identical text: src 836 = dst 839 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105700, 105701, 105702, 105703; literal 8 |
| 163 | UNPAIRED-PORTED | A/AFfl.v | - | 839 | Lemma zshadow' / sentence 60 | 0x8 | PATCH-ZS | now paired by identical text: src 836 = dst 839 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105700, 105701, 105702, 105703; literal 8 |
| 164 | UNPAIRED-PORTED | A/AFfl.v | - | 839 | Lemma zshadow' / sentence 60 | 0x8 | PATCH-ZS | now paired by identical text: src 836 = dst 839 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105700, 105701, 105702, 105703; literal 8 |
| 165 | UNPAIRED-PORTED | A/AFfl.v | - | 839 | Lemma zshadow' / sentence 60 | 0x8 | PATCH-ZS | now paired by identical text: src 836 = dst 839 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 105700, 105701, 105702, 105703; literal 8 |
| 175 | UNPAIRED-SOURCE | A/AFjy.v | 1597 | - | Lemma zshadow_final / sentence 47 | 0x8 | PATCH-ZS | now paired by identical text: src 1597 = dst 1600 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 145176, 145177, 145178; literal 8 |
| 176 | UNPAIRED-SOURCE | A/AFjy.v | 1597 | - | Lemma zshadow_final / sentence 48 | 0x8 | PATCH-ZS | now paired by identical text: src 1597 = dst 1600 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 145176, 145177, 145178; literal 8 |
| 177 | UNPAIRED-SOURCE | A/AFjy.v | 1597 | - | Lemma zshadow_final / sentence 49 | 0x8 | PATCH-ZS | now paired by identical text: src 1597 = dst 1600 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 145176, 145177, 145178; literal 8 |
| 178 | UNPAIRED-PORTED | A/AFjy.v | - | 1600 | Lemma zshadow_final / sentence 51 | 0x8 | PATCH-ZS | now paired by identical text: src 1597 = dst 1600 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 145176, 145177, 145178; literal 8 |
| 179 | UNPAIRED-PORTED | A/AFjy.v | - | 1600 | Lemma zshadow_final / sentence 52 | 0x8 | PATCH-ZS | now paired by identical text: src 1597 = dst 1600 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 145176, 145177, 145178; literal 8 |
| 180 | UNPAIRED-PORTED | A/AFjy.v | - | 1600 | Lemma zshadow_final / sentence 53 | 0x8 | PATCH-ZS | now paired by identical text: src 1597 = dst 1600 (byte-identical line), e165 class NON-ADDRESS-SAME, e165 raw lines 145176, 145177, 145178; literal 8 |

### SAME-VALUE-DIFFERENT-OBJECT rows of Reusable/ not in the staged text (20)

Reasons SV-MMAP (18) and SV-HWCAP (2), as in gate-cb0e-TRIAGE.md (ABI constants: mmap flag sums and the AT_HWCAP range; they never relocate). This run does not judge them because `work16/stage` has no Reusable/. The control run flags each again with the same key and class.

| cb0e raw line | file:line | dst line | sentence (idx) | src value | dst value | cb0e reason | control raw line |
|---:|---|---:|---|---|---|---|---:|
| 182 | Reusable/YA01.v:299 | 300 | Definition node_mmap2g (11) | 0x104022 | 0x104022 | SV-MMAP | 140 |
| 183 | Reusable/YA01.v:299 | 300 | Definition node_mmap2g (13) | 0x104032 | 0x104032 | SV-MMAP | 141 |
| 184 | Reusable/YA01.v:300 | 301 | Definition node_mmap2g (17) | 0x100022 | 0x100022 | SV-MMAP | 142 |
| 185 | Reusable/YA01.v:300 | 301 | Definition node_mmap2g (19) | 0x100032 | 0x100032 | SV-MMAP | 143 |
| 186 | Reusable/YA01.v:301 | 302 | Definition node_mmap2g (23) | 0x104022 | 0x104022 | SV-MMAP | 144 |
| 187 | Reusable/YA01.v:301 | 302 | Definition node_mmap2g (25) | 0x104032 | 0x104032 | SV-MMAP | 145 |
| 188 | Reusable/YA01.v:302 | 303 | Definition node_mmap2g (29) | 0x100022 | 0x100022 | SV-MMAP | 146 |
| 189 | Reusable/YA01.v:302 | 303 | Definition node_mmap2g (31) | 0x100032 | 0x100032 | SV-MMAP | 147 |
| 190 | Reusable/YA01.v:715 | 716 | Definition init_kn_g (3) | 0x20112d | 0x20112d | SV-HWCAP | 148 |
| 191 | Reusable/YA02.v:741 | 742 | Lemma hw_facts_ok (1) | 0x20112d | 0x20112d | SV-HWCAP | 149 |
| 192 | Reusable/YA09.v:1271 | 1272 | Lemma ff_class_100022 (1) | 0x100022 | 0x100022 | SV-MMAP | 150 |
| 193 | Reusable/YA09.v:1272 | 1273 | Lemma ff_class_100032 (1) | 0x100032 | 0x100032 | SV-MMAP | 151 |
| 194 | Reusable/YA09.v:1273 | 1274 | Lemma ff_class_104022 (1) | 0x104022 | 0x104022 | SV-MMAP | 152 |
| 195 | Reusable/YA09.v:1274 | 1275 | Lemma ff_class_104032 (1) | 0x104032 | 0x104032 | SV-MMAP | 153 |
| 385 | Reusable/YA09.v:402 | 403 | Lemma mmap_noreserve_b_100022 (2) | 0x100022 | 0x100022 | SV-MMAP | 343 |
| 386 | Reusable/YA09.v:403 | 404 | Lemma mmap_noreserve_b_100032 (2) | 0x100032 | 0x100032 | SV-MMAP | 344 |
| 387 | Reusable/YA09.v:404 | 405 | Lemma mmap_noreserve_b_104022 (2) | 0x104022 | 0x104022 | SV-MMAP | 345 |
| 388 | Reusable/YA09.v:405 | 406 | Lemma mmap_noreserve_b_104032 (2) | 0x104032 | 0x104032 | SV-MMAP | 346 |
| 389 | Reusable/YA09.v:430 | 431 | Definition noreplace_core (0) | 0x100022 | 0x100022 | SV-MMAP | 347 |
| 390 | Reusable/YA09.v:430 | 431 | Definition noreplace_core (1) | 0x100032 | 0x100032 | SV-MMAP | 348 |

## What did not change

- 302 flagged rows have the same key and class as in cb0e, so each keeps its cb0e reason (by reference: `gate-e165-triage-rows.tsv` gives the cb0e raw line of each). Reasons of the unchanged rows per class:
  - DIFFERENT-SYMBOL 1: FMTWIN (1)
  - GEOMETRY-CHANGED 9: G-6128 (9)
  - KIND-CHANGED 9: FMTWIN (5), K-TLS (2), K-ABSENT0 (2)
  - NO-COUNTERPART 1: THUNK (1)
  - NON-ADDRESS-CHANGED 174: N-FMTPTR (113), N-REGCNT (44), N-RANGES (3), N-RA3 (3), FMTWIN (2), N-CELLPATCH (2), N-IAL (2), N-INST (1), N-AD1o-TOP (1), N-AD1o-ZLEN (1), N-DEPOT (1), N-AD1o-BSS20 (1)
  - STALE-DONOR-CODE-POINTER 1: THUNK (1)
  - UNPAIRED-PORTED 15: P-UCIPROG (10), PATCH-ZS (5)
  - UNPAIRED-SOURCE 84: S-GRANTPROG (44), PATCH-ZS (18), S-ABSENTRT (12), S-AF0L (6), THUNK (4)
  - UNRESOLVED 8: U-TLSSH (2), FMTWIN (2), U-JT (1), U-UNMAP (1), U-PHDR (1), U-STDIN (1)
- The 6 GENERATOR-FILL rows (A/AD2e.v:69 idx 3 and 5, A/AD2f.v:184 idx 3, A/AD2f.v:196 idx 5, A/AE3m.v:955 idx 3, A/AE3m.v:1444 idx 6) have the same key; their measured reasons in the GENERATOR-FILL table of gate-cb0e-TRIAGE.md hold.
- Of the 157909 numerals, 157876 have a cb0e row with the same key and class. The other 33: the 4 NEW rows; 25 NON-ADDRESS-SAME rows that are the new identical-text pairings in A/AFex.v, A/AFfl.v, A/AFjy.v (8 = 8 or 0 = 0); and the 4 rows of A/AD1q.v, a file cb0e did not read (3 SAME-SYMBOL: the format strings "cli: cannot open %s\n" 0x1d7b0 -> 0x1d5e6, "cli: read error on %s\n" 0x1d7c5 -> 0x1d5fb, "usage: %s INPUT\n" 0x15905 -> 0x157cd, the same addresses FMTWIN measured; 1 NON-ADDRESS-SAME 5 = 5). A/AD1q.v has no flagged row.
- The cb0e observations still hold at commit 7f39d662ad6c, re-measured: fuzz_uci's program rows are on lib/A/AB1w.v line 87 (starting `tfib_A_check_no_overread := 0x7f4fc`); a `git grep -w` over proofs/reac-repacer/fuzz_uci/ at that commit finds tfib_rodata_hi, tfib_text_hi, tfib_tbss_lo, tfib_E_set_thread_area and tfib_at_ph_addr_z in no .v file but lib/A/AB1w.v, their definitions (the other hits are evidence text); the U-TLSSH margin rests on unchanged values.

## Observation that is not a defect

- e165's note on each GENERATOR-FILL row says "the object the donor row names is in no symbol of the target". For these 6 rows the donor value names no object: 4 are region counts or indices (src class `below image base (decimal)`) and 2 are interior string offsets (`str:"%d\n"+2`, `+3`), so the new condition (no `sym:NAME+0x0` label of a name the target has) holds trivially. What makes the rows right is the measurement in the cb0e GENERATOR-FILL table (the donor sentence carries the same duplicate at the same positions; each dst value is fuzz_uci's own count or string address), not the tool's note.

No defect. FLAGGED 306 rows in 9 classes: DIFFERENT-SYMBOL=1 GEOMETRY-CHANGED=9 KIND-CHANGED=9 NO-COUNTERPART=1 NON-ADDRESS-CHANGED=174 STALE-DONOR-CODE-POINTER=1 UNPAIRED-PORTED=19 UNPAIRED-SOURCE=84 UNRESOLVED=8 (FLAG-CLASSES 575d398c6022); GENERATOR-FILL 6.
