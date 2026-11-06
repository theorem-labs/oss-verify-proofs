# G3: codeptr on the image B start-up files (gate record)

Proves no function (kind: measurement). Re-run 2026-10-30 on the series base b1afc3e80791 (`run.sh g3`).

## Tool
- codeptr.py, the codeptr of record: sha256 `12348302dfd2e419748bc3ad20e67b246d21b576c9c6d7887a33854785e146dd`,
  run as `frozen-run.sh startup-set-2026-10-30d.tsv codeptr.py ...` from the start-up set of record 2026-10-30d
  (`sha256sum -c SHA256SUMS`: 50 OK; frozen-run.sh `40cd8a4bf5bf355c4a8f506bcc1503e9c7ec4a1331831204bd36ef22a8915ab4`,
  set bundle `startup-set-2026-10-30d.tsv` `bde9702390640d7bfc5a23702de239154ed4130e863e475ca109455c2648dbab`).
- Each run prints `codeptr: self-test: 27 known answers (the stale decision 7, the slot 3, the type rule 12 with 2
  sentence-final decimals, the names reader 3, --not-address 2)`.

## Inputs
- `$PIN_B` = fuzz_disco.asan-ubsan, sha256 `cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146`.
- `$TWIN_B` = its unstripped twin (host binary, not shipped), sha256
  `ead714913acd1e81835e08e021456cebcb35c09af2f87f4e7e2b6891f1b92489`. PT_LOAD 2..4 of twin and pin are byte-equal
  (0x30f24 +0x6e324, 0xa0248 +0x1360, 0xa25a8 +0x37f8, measured; PT_LOAD 1 differs only as the twin carries the
  section table). The twin is read only for names (`--names`).
- `$CGIF_B` = cgif_file_fuzzer.asan-ubsan, the cgif pin of the same build, sha256
  `1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef`; `$CGIF_NM` = its recovered names (nm text),
  `tools/startup/syms/cgif_file_fuzzer.asan-ubsan.nm` at commit b351f103e888, sha256
  `5b5f81784ea1ed5e8d35ab9bd5b01277536c10addbe4b545ca3f223045c95a75`.
- `$CLIB` = cgif's released lib at c8557374ad2e (`proofs/cgif/cgif_file_fuzzer/lib`); every checked file has its donor
  file there (`--stale-dir`), so each line names its paired donor file.
- `$LIB/Reusable/<F>.v` = the base's `proofs/libreac/fuzz_disco/lib/Reusable/<F>.v`.

## Control of record first (known answers)
`bash codeptr-controls.sh "$STARTUP_SET/startup-set-2026-10-30d.tsv" <root holding cgif's lib and pins>`, the script
`tools/startup/codeptr-controls.sh` at commit b351f103e888 (sha256
`25c012a65b96fe16406ee979efb146b6bd266770739bbedfc3b57f5fd54e3c03`), through the same set: rc 0.
- MUST FIND, image A, cgif's own unrelocated files against fuzz_scene's images: AD1k 22, AD2i 6, AD2j 107 FINDINGS;
  image B: YD1k 22, YD2i 6, YD2j 107 FINDINGS; each line names its paired donor file.
- MUST NOT FLAG: cgif YF0m.v lists `0xec9a4 (969124)` and `0x8065e (525918)` as NOT read as addresses (the result list
  of a `mod`), and 0x8065e is not among its 279 findings.
- Last line: `codeptr-controls: PASS (must-find paired on all 6 files; must-not-flag 0x8065e)`.

## Command (one run per file, with that file's declarations)
```
frozen-run.sh startup-set-2026-10-30d.tsv codeptr.py --image "$PIN_B" --names "$TWIN_B" \
  --stale-image "$CGIF_B" --stale-names "$CGIF_NM" --stale-dir "$CLIB" <declarations of F> "$LIB/Reusable/<F>.v"
```
F = YB01 YB03 YB05 YB12 YD1k YD2i YD2j YF0m YCej YB13 YB1q YF0l. run.sh holds each declaration with its full reason.

## Verdict: PASS, 0 findings on all 12 files (rc 0 each)

| file | code (fn starts / return pcs / other insn) | data | at or above top 0x5fdcf0 | findings | stale | donor literals same meaning | declared |
|---|---|---|---|---|---|---|---|
| YB01 | 16 (12 / 3 / 1) | 459 | 209 | 0 | 0 | 1 | same 0x10800; not-address 0x20000 0x71c00 0x100000 0x161200 0x38e000 |
| YB03 | 19 (9 / 10 / 0) | 297 | 64 | 0 | 0 | 3 | same 0x10800; not-address 0x10101 0x1ffff 0x445c0 0x71c00 0x100000 0x38e000 0x100018 0x3fffff |
| YB05 | 37 (4 / 22 / 11) | 4 | 1 | 0 | 0 | 0 | none (0x1b8c9 112841 read as a %nat literal by type) |
| YB12 | 24 (8 / 0 / 16) | 5 | 2 | 0 | 0 | 0 | none (TFIB_TEXT_N 112841 read as nat by type) |
| YD1k | 0 | 72 | 1 | 0 | 0 | 2 | same 0x10310 |
| YD2i | 2 (1 / 1 / 0) | 4 | 5 | 0 | 0 | 1 | same 0x10800; not-address 0x3fffff |
| YD2j | 3 (3 / 0 / 0) | 209 | 1 | 0 | 0 | 4 | same 0x10310 |
| YF0m | 29 (16 / 11 / 2) | 976 | 637 | 0 | 0 | 4 | same 0x10800; not-address 0x10101 (and 0xcecee / 0x415f1 read as `mod` results by type) |
| YCej | 20 (0 / 20 / 0) | 0 | 0 | 0 | 0 | 0 | none |
| YB13 | 1 (0 / 0 / 1) | 6 | 1 | 0 | 0 | 2 | not-address 0x20000 0x55c000 |
| YB1q | 43 (43 / 0 / 0) | 0 | 0 | 0 | 0 | 0 | none |
| YF0l | 29 (23 / 2 / 4) | 0 | 0 | 0 | 0 | 0 | none |

## Triage of the 23 raw findings the declarations answer
Without declarations, one run over all 12 files (same command, no declarations) gives 23 findings, rc 1: YB01 6, YB03 9,
YD1k 1, YD2i 2, YD2j 1, YF0m 2, YB13 2.
Each is the same value in the cgif donor file, read in the file's own text as below; none is a stale cgif address.

| value | files: where | class | why it is right |
|---|---|---|---|
| 0x10800 (67584) | YB01: 50 lines (16, 33, 51, ...: one per hand-off state, `ELit 67584` after the stack-pointer term), YB03:13, YD2i:60 (register list, x3 `SLit 67584`), YF0m:16 (`TFIB_GP := 0x10800`) | `--same` | gp: `__global_pointer$` = 0x10800 in the image B twin .symtab; cgif links gp at 0x10800 too. Kept as an ADDRESS claim: the code and section checks still ran on it. |
| 0x10310 (66320) | YD1k:252 (`CH R_A1c 66320 40`), YD2j:18-19 (`mkRegion None 66320 66360`, `mkChunk 66320 (CImg 40)`) | `--same` | the start of the image B region [0x10310, 0x10338) in .rodata (0x102e0 + 48), from the image B collector run; its length 40 differs from cgif's 24 there, so the value is the image's own. |
| 0x20000, 0x71c00, 0x161200 | YB01 lines 15, 105, 459, 498, 515, 552, 569 (0x20000, 24 times); 15, 117, 121 (0x71c00, 20 times; 0x161200, 19 times); YB03:13 (0x71c00, 9 times): all KDisj lengths | `--not-address` | the length argument after a KDisj region base: an ASan region length. |
| 0x100000 (1048576) | YB01: 171 times on 65 lines (15, 16, 33, ...), YB03:13 (8 times): KDisj lengths, `am_len := ELit 1048576`, (base, length) mapping-list entries, and the 8-byte KWord value at __asan::instance+808 (0xa6140) | `--not-address` | a length / size, never an address operand. |
| 0x38e000 (3727360) | YB01: 125 times on 53 lines (15, 16, 33, ...), YB03:13 (16 times): KDisj lengths, `am_len`, mapping-list lengths | `--not-address` | a mapping length. |
| 0x10101 (65793) | YB03:13 (4-byte KWord value at a_off 683240), YF0m:78 (`z8 (ANum 0xa6ce8) 0x10101`) | `--not-address` | the content of __asan::asan_flags_dont_use_directly+112 (0xa6ce8): three bool flag bytes 01 01 01. |
| 0x1ffff, 0x445c0 | YB03:13 (`KRange (EVar 3) 0 131071`, `KRange (EVar 7) 0 131071`, `KRange (EVar 4) 0 280000`) | `--not-address` | value bounds on symbolic variables. |
| 0x100018 (1048600) | YB03:13 (`KZero ... (ELit 1048600)`, twice) | `--not-address` | a zeroed length. |
| 0x3fffff (4194303) | YB03:13 (`KRange (EVar 43) 1 4194303`), YD2i:140, 226, 234, 236, 754 (`KRange (EVar TIDV) 1 4194303`, `Lemma tid_range`, `mkAF 1 4194303`) | `--not-address` | the thread-id bound. |
| 0x20000, 0x55c000 | YB13: 0x20000 on 9 lines (4, 89, 109, 122, 126, 136, 138, 147, ...), 0x55c000 on 7 lines (4, 27, 31, 47, 92, 94, 120): the header's segment page spans, `scanN AsanUbsan_seg_bytes_003 64 0 5619712`, `65536 + 131072` bounds | `--not-address` | the page spans of PT_LOAD 1 (0x10000..0x30000) and PT_LOAD 4 (0xa2000..0x5fe000) of the image B pin, measured on the pin; cgif's spans are equal. |

## Planted control: fired
A copy of `lib/Reusable/YF0m.v` outside the tree with line 16 `Definition TFIB_MAIN : Z := 0x80b1c.` changed to cgif's
`0x80020` (a moved address: cgif's main), same command and YF0m's declarations: rc 1,
`YF0m.v 29 code (15 function starts, 11 return pcs, 3 other instruction starts), 976 data, 637 at or above the image top
0x5fdcf0, 1 FINDINGS: 0x80020 [stale against cgif_file_fuzzer.asan-ubsan, donor file $CLIB/YF0m.v: 1 STALE (0x80020),
DECLARED the same in both images: 0x10800 (...), 4 donor-file literals with the same meaning in both images]`.
