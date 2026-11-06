# G10: the address checker 0d24592683b6 over the image B files (gate record)

Proves no function (kind: measurement). Run 2026-10-31 on the series base b1afc3e80791 (`run.sh g7 g10`). Its owner
installed port_addr_check 0d24592683b6 at 2026-10-30 23:46Z; the G7 (3d2eee813cce) and G1 (efa19b81e92b) records stand
beside this one, unchanged.

## Tool
port_addr_check.py, sha256 `0d24592683b610123346567302caf1bf97e5ac9354cf05799dc7cfc21dc0f4fa`, run from its version
directory: before the run, run.sh checks it and the five files beside it against its SHA256SUMS (inputs_used.py
`3ed6c0c79f05...`, scan_literals.py `f0ec1e108ff8...`, insn-targets/insn_targets.py `efdf3951d4bb...`,
identity-quotients/qscan.py `7baa52331b8c...`, identity-quotients/imgquant.json `7bd088dd7fed...`). Images keyed A / B
/ P / U, `--fail-on-flags`. Its `--list-flag-classes` output is byte-equal to 3d2eee813cce's (27 classes;
`FLAG-CLASSES 575d398c6022` in both summaries).

## Commands
(1) The gate: G1's command with the tool replaced, every other argument the same:
```
python3 "$PAC0D" --git "$GIT" --donors-from "$DONORS" --summary --fail-on-flags \
  --src c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib --dst b1afc3e80791:proofs/libreac/fuzz_disco/lib \
  --paired-only --map A/=A/ --map =Reusable/ \
  --src-image A="$CGIF_BIN/cgif_file_fuzzer.asan" --src-image B="$CGIF_BIN/cgif_file_fuzzer.asan-ubsan" \
  --src-image P="$CGIF_BIN/cgif_file_fuzzer.plain" --src-image U="$CGIF_BIN/cgif_file_fuzzer.ubsan" \
  --dst-image A="$PIN_DIR/fuzz_disco.asan" --dst-image B="$PIN_DIR/fuzz_disco.asan-ubsan" \
  --dst-image P="$PIN_DIR/fuzz_disco.plain" --dst-image U="$PIN_DIR/fuzz_disco.ubsan" \
  --assign '**=auto' --include 'Y*.v' --cache "$WORK/g10/cache" --out "$WORK/g10/pac0d-Y.tsv"
```
(2) The same with each `--dst-image K="$PIN_DIR/fuzz_disco.<build>:$TWIN_DIR/fuzz_disco.<build>"` (the unstripped
twins' `.symtab` instead of recovered symbols), cache `$WORK/g10/cache-t`. (3) 3d2eee813cce (`"$PAC3"`) with the
arguments of (2), cache `$WORK/g10/cache-3t`, the baseline of (2). Every cache starts empty: (1) cache hits 0, misses 8;
(2) and (3) hits 0, misses 4 (the four donor images; the twins name the target's symbols).

## Result (about 10 min a run): rc 4; count files paired 836; 397413 numerals

| finding class | 3d2eee813cce (G7) | 0d24592683b6 (1) | 3d2eee813cce PIN:TWIN (3) | 0d24592683b6 PIN:TWIN (2) |
|---|---|---|---|---|
| UNPAIRED-PORTED | 16038 | 16038 | 16038 | 16038 |
| UNPAIRED-SOURCE | 7282 | 7282 | 7282 | 7282 |
| NON-ADDRESS-CHANGED | 2595 | 2595 | 2593 | 2593 |
| KIND-CHANGED | 942 | 954 | 944 | 956 |
| DIFFERENT-SYMBOL | 415 | 415 | 435 | 436 |
| UNRESOLVED | 190 | 190 | 170 | 170 |
| SAME-VALUE-DIFFERENT-OBJECT | 51 | 55 | 51 | 55 |
| STALE-DONOR-CODE-POINTER | 15 | 26 | 15 | 26 |
| STALE-DONOR-DATA-POINTER | 5 | 5 | 5 | 5 |
| STALE-DONOR-ROUNDED | 4 | 4 | 4 | 4 |
| GEOMETRY-CHANGED | 3 | 3 | 3 | 3 |
| IMAGE-EXTENT-CHANGED | 2 | 2 | 2 | 2 |
| NO-COUNTERPART | 2 | 2 | 2 | 2 |
| INSN-CHANGED | 0 | 1 | 0 | 1 |
| FLAGGED (classes) | 27544 (13) | 27572 (14) | 27544 (13) | 27573 (14) |

`UNMEASURED`: (1) 2923 rows in 2 classes (UNMEASURED-NAME 1, YB1w.v:1311, as in G7; UNPAIRED-FILE-UNMEASURED 2922);
(2) and (3) 2922 rows (UNPAIRED-FILE-UNMEASURED).

## Diff against 3d2eee813cce on the same file set (g10_triage.py, row by row)
Rows are keyed by (src_file, src_line, dst_file, dst_line, sentence, idx, kind, src_value, dst_value) and occurrence.
Both versions give the same 397413 keys; 0d24592683b6 writes them in another order, so the tables differ as files.
- (1) against G7's table: **129 rows differ**. 91 in the note only (83 ROUND-CONSTANT-SAME rows gain "and inside no
  named symbol"; 8 IDENT-NAME rows give the instruction that loads the cell instead of the page-multiple text). 38 in
  the verdict: 28 passes become findings (ROUND-CONSTANT-SAME -> KIND-CHANGED 12, -> STALE-DONOR-CODE-POINTER 11, ->
  SAME-VALUE-DIFFERENT-OBJECT 4; INSN-SAME -> INSN-CHANGED 1) and 10 passes stay passes (ROUND-CONSTANT-SAME ->
  SAME-SYMBOL 6, -> ABSTRACT-GOAL 4). No finding becomes a pass and no row moves between finding classes.
- (2) against (3): 130 rows differ: the same 129, and YH03.v:18 `src0_E_start` SAME-SYMBOL -> DIFFERENT-SYMBOL (the
  named-symbol rule, absolute where the target's symbols are the image's own: expected 0x12cac).

## Triage: 0 untriaged, 0 defects
- `g1_triage.py` (this directory, `--pac "$PAC0D"`) on table (1): every row G7 flags gets its G1 rule with the same
  detail (those rows, sorted, are byte-equal to `G1-flagged-rows.tsv` sorted); its only UNTRIAGED rows are the 28 rows
  0d24592683b6 newly flags (29 on table (2)), so it exits 1 there by design.
- `g10_triage.py` (this directory) writes `G10-rows.tsv`, one row per changed row of both runs (259), and exits 0: each
  of the 77 verdict moves has a measured rule, and each UNTRIAGED row of g1_triage.py is one of them.

| rule | (1) | (2) | measured |
|---|---|---|---|
| NOTE-ONLY | 91 | 91 | the verdict is unchanged; the detail gives the note text removed and added |
| ALLOC-MAP-SIZE | 20 | 20 | 262144 = 2^18, the primary allocator's map unit (YG00 kUserMapSize / kFreeArrayMapSize, unfolded in the proof; a register the YFk8 / YFk9 run pins at 0x37214 / 0x34ea4 inside PopulateFreeArray / EnsureFreeArraySpace; a1 of the mmap ecall at 0x64c98, in internal_mmap, a7 = 222): a length. Each pin holds `lui rX,0x40` in SizeClassAllocator64::PopulateFreeArray and ::EnsureFreeArraySpace (A 0x3718c / 0x34dc8, B 0x37204 / 0x34e40) |
| CAPACITY-DOUBLING | 2 | 2 | YO01 RPX_closed: 2 * 131072 = 262144, the read loop's capacity compared with dlen data (Qed) |
| FOOTPRINT-LENGTH | 1 | 1 | YO0f st1_blocks: block (SP 3 64, 200000) rounded up to 4096 = 200704 (vm_compute) |
| FAKESTACK-OFFSET | 2 | 2 | YF0r / YF0t FS_FROFF: frame offset in the ASan fake stack (frame_addr_cid, Qed); s1C1_eq (Qed) shows the image B code forms base + 0x109000 / 0x209000 |
| LOOSE-ENTRY-BOUND | 2 | 2 | YE30 / YE6k entD_ro: every icpt_rodata entry ends below 0x200000 (highest [0xaa160, 0xaa178)) |
| JAL-SAME-CALLEE | 1 | 1 | YN3i DS_020: the plain pin's word at strnlen + 0x20 (FS_020's pc) is 0x959ff0ef, jal ra -> 0x1e378 memchr; cgif's 0x024000ef at its strnlen + 0x20 calls its memchr 0x1d8a4 |
| STARTUP-CELL-VALUE | 4 | 4 | the value 0x100000 of YF0m's cell z8 (ANum 0xa6140) (inside __asan::instance + 0x328), restated by YFgi / YFgm / YFgn REG0; G4 / G5 check the cell |
| RUNTIME-BLOCK-SIZE | 2 | 2 | YG0f kNodesBlockSize 0x100000: each pin holds `lui rX,0x100` in TwoLevelMap<StackDepotNode, 32768, 65536>::Create (A 0x73808, B 0x73880) |
| ABORTED-GOAL | 4 | 4 | YK1a lines 900-919: `Goal ... Abort.` over the section variable segs |
| SIZE0-END-NEXT-CELL | 0 | 1 | YH03.v:18: `_start` has size 0 (plain twin); the regenerator ends a size-0 cell at the next cell (0x12cd8 = src0_A_do_init), as cgif's table does (0x127e4 size 0, E 0x1282c); the checker expects the next function, `_start_c` 0x12cac; no file reads src0_E_start |

## Planted control: fired
G1's plant (a copy of `lib/Reusable/YE23.v` with line 474's `Z_to_bv 64 6277920` moved to `6277936`) run with `--dst
<dir holding that copy> --include 'YE23.v'`, the images of (1) and its cache: rc 4, `count files paired: 1`, `FLAGGED
19 rows` (the run above flags 18 in YE23.v), the new one `NON-ADDRESS-CHANGED 0x5f9920 -> 0x5fcb30` at YE23.v:474.

## Limits of this checker, as its owner lists them (its version record: Limits, and the 0d24592683b6 entry)
1. The named-symbol rule is absolute only where the target's symbols are the image's own (an unstripped twin). With
   recovered symbols (stripped pins: command (1)) the donor must still corroborate, so a value the donor already had
   wrong passes. Command (2) lifts this; its one extra row is YH03.v:18 above.
2. SAME-CONTENT, and predict mode's MAPS-STRING, still decide by string content where neither side names a symbol.
3. Instruction words are compared modulo relocation immediates, not re-decoded against the target image; a jal that
   no stated fetch pc places is INSN-CHANGED only when the two words differ.
4. ROUND-CONSTANT-SAME still passes a page-multiple value in no geometry slot and inside no named symbol (G8, roundconst
   v2, reads it by value).
5. Address versus size is decided by name and context; a NON-ADDRESS numeral is compared by value only; an in-range
   decimal is an address only as a symbol start, boundary, GOT slot, xref, jump-table cell, call return site or decimal
   copy of a hex code address of the same file.
6. A donor object no symbolised build carries, or an END whose preceding object the donors cannot name, is UNRESOLVED.
7. SLID-TO-NEIGHBOUR covers single cells and windows of at most 0x100 bytes.
8. `--assign '**=auto'` marks a tie between the two ASan images AMBIGUOUS.
9. Run from its read-only version directory it needs `--cache` (every command here passes one).
