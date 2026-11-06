# .got cells and codeptr 12348302dfd2 on plugin-hostd/fuzz_command's port_core core

Two checks that cover what the value gate port_addr_check 3d2eee813cce does not:

1. Every numeral that lies inside an image's `.got` is checked against the 8-byte GOT word it names. The gate's planted
   control shows that the gate passes a `.got` cell moved to the next word (SAME-SYMBOL-ROUNDED).
2. codeptr 12348302dfd2 (the version of record) runs on the start-up and table files of both images, with its controls
   and with a check of its registered limit.

Result: no FINDING. Nothing goes to the code list or to the measured-rows TSV.

## Inputs

- Unit tree: plugin-hostd/fuzz_command at the series head plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record) (`lib/`).
- Donor tree: cgif/cgif_file_fuzzer at c8557374ad2e (`lib/A` = image A, root `Y*.v` = image B).
- Images (by role, sha256 first 12):
  - fuzz_command.asan c0661b96b5bd and its twin 68db792d5fa7
  - fuzz_command.asan-ubsan bbe55d24d096 and its twin 658cefbe806b
  - cgif_file_fuzzer.asan 7093581aab04 and its twin 488e39500746
  - cgif_file_fuzzer.asan-ubsan 1c29845fe605 and its twin ce511d541cda
  - codeptr control images: fuzz_scene.asan 43654a025fd0 (twin 6ed872f7cc8c), fuzz_scene.asan-ubsan e98b1ed286c1 (twin
    ef0b41158fe0)
- Value-gate runs of record (port_addr_check 3d2eee813cce, `full.tsv`): A (cgif `lib/A` -> `lib/A`), B (cgif `lib` ->
  `lib/B`), R (cgif `lib` -> `lib/Reusable`), and the planted-control runs (base and plant copies of A and B).

## Part 1: `.got` cells (`gotcheck.py`, `gottriage.py`)

### What gotcheck.py measures

- `.got`: A [0xa6390, 0xa7108) (431 words), B [0xa5ef0, 0xa6c68) (431 words). The tool refuses to run if the pin's and the
  twin's `.got` bytes differ. They are equal for all four images.
- GOT layout, both images: our GOT[i] has the same pointee as cgif's GOT[i] for i < 411, and as cgif's GOT[i-1] for
  i >= 415 (the same symbol or alias set, or the same value at the same place; 0 exceptions). Only the program's own
  words differ: ours has 4 (`g_rec`, `rec_ncodes`, `rec_codes`, `g_quitting`, GOT[411..414]); cgif has 3
  (`cgif_newgif`, `cgif_raw_newgif`, `cgif_raw_addframe`, GOT[411..413]).
- Scanned: `lib/A/A*.v`, `lib/B/Y*.v`, `lib/A/Rt/*.v`, `lib/B/Rt/*.v`, `lib/Reusable/*.v` (1612 files). Image by
  directory. `lib/Reusable` files have no Require of `lib.A` or `lib.B`, so they get image B (the gate's key for
  `lib/Reusable`). They hold 0 numerals in either `.got`.
- Found: 858 numerals inside the image's `.got`: `lib/A` 268, `lib/A/Rt` 149, `lib/B` 267, `lib/B/Rt` 174. Of these,
  124 are in comments.
- Pointee of a GOT word: the twin's symbol table (the alias set at one address). A word that is not in a symbol (zero,
  a TLS offset, a small constant) is named by its value and its place: the distance in words from the nearest earlier
  word that names a symbol. GOT[0] is named GOT[0] (`_DYNAMIC` is undefined, value 0).
- Checks, per numeral:
  - donor: the gate row at the same file:line with the same value (the k-th occurrence goes with the k-th row) gives the
    donor numeral. Its GOT word in cgif's image must name the same pointee.
  - name: where the definition name names a symbol (`GOT_x`, `D_GOT_x`, `got_x`, `D_x_musl`, `real_x`, `X_GOT` for an
    alias), the pointee must carry that name. The aliases are listed in the script, each with its reason (`uar`,
    `shadow`, `canary`, `ssp`, `cflags`, `environ`).
  - stated: where the text states the word (`lit8 V W`, `val_mem .. V 8 W`, `(V, 8, [(0, 8%N, W)])`, a block list
    `(V, n, [(off, 8%N, W); ...])`, `(ANum V) W`, `CVal 8 (SLit W)`, `[V] = W`, `V -> W`, `word_mem/RO8/C8 .. V W`), W
    must equal the image word.
  - twin: the other image's twin file (`lib/B/Yxxx.v` and `lib/A/Axxx.v`, `lib/B/Rt/X.v` and `lib/A/Rt/X.v`) must
    hold the same multiset of pointees in the same-named definition.
  - comment: the comment writes the word after the numeral (WORD), names the pointee in the numeral's own clause
    (NAME), or names a pc whose auipc + ld|addi computes the numeral (DISASM). The twin file can have the same comment
    line with the same pointee at the same place (TWIN-LINE), or the same value can be an accepted code numeral of the
    same file (CODE-SAME-FILE).
  - quantities: an `(ELit n)` length of a KZero/KFill write, a `CImg`/`CVal` length, a `%nat` literal, and a walk's
    register value after an auipc (`svx S_pc DS_pc (Z_to_bv 64 V)` where the instruction at pc is an auipc that gives
    V) are not cells (NOT-ADDRESS).
- Status: OK when no check disagrees and at least one agrees. Otherwise FLAG or UNCHECKED.

### Results (gotcheck.out, got-triage.out)

| status from gotcheck | A | B |
|---|---|---|
| OK | 411 | 439 |
| FLAG | 1 | 1 |
| UNCHECKED | 2 | 0 |
| NOT-ADDRESS | 3 | 1 |

Checks: donor SAME 520 (DIFF 0; DONOR-NOT-GOT 2; gate row without a donor value 8; no gate row 328, which are the
comments and the Rt files). Name MATCH 20, ALIAS 14, MISMATCH 0. Stated OK 530, MISMATCH 0. Twin SAME 728, SET-DIFF 0.
Comment WORD 75, TWIN-LINE 16, CODE-SAME-FILE 14, DISASM 11, NAME 6.

gottriage.py gives every row a reason (the triage columns of `got-cells.tsv`). All 858 rows are OK:

| reason | rows | what was measured |
|---|---|---|
| CHECKED | 795 | the checks above, and +4 / +8 / -8 / the donor value are refused (control below) |
| CHECKED-TWIN+SAME-FILE | 25 | twin only, and the same file states the word for this value at another line |
| CHECKED-TWIN+SIBLING-STATED | 13 | twin only, and `lib/*/Rt/RtSM0T.v` states this cell with the image's word |
| CHECKED-TWIN+FIELD-NAME | 4 | twin only, and the record field `as_got_shadow` / `as_got_uar` names the pointee |
| CHECKED-TWIN+PROGRAM-BOUND | 4 | `lib/A/AD2l.v:125`, `lib/B/YD2l.v:126`: the bound pair is the program's own GOT words |
| CHECKED-TWIN+NAMED-CONST | 2 | `RtDtorExit.v:61`: the words at V and V+8 are `A_ASAN_GLOBALS` and `A_ASAN_GLOBALS + A_ASAN_GLOBALS_SZ` of `RtDtorTbl.v` |
| CHECKED-TWIN+GOTW-BOUND | 2 | `RtFSnprintf.v`: the auipc + ld at the pc that `RtPFCmd.v` names computes V, and the word points at `__stack_chk_guard` |
| PROGRAM-GOT-BLOCK | 3 | see below |
| GOT-BLOCK-START | 4 | comments that name a GOT block: MemToShadow, at the pc the line names, loads by auipc + ld exactly the 5 words of the list `(V, 40, [...])` that the file states |
| GOT-CELL-NAMED | 1 | `lib/B/Rt/RtSF5.v:5` 0xa5f50: "the shadow-base .got word"; the word is 0xb0c38 = `__asan_shadow_memory_dynamic_address`, which the comment writes as the shadow-base cell |
| COMMENT-QUOTES-PREMISE | 1 | `lib/A/Rt/RtNumber.v:100` `[0xa63e0, 0x142cde)` quotes the premise of `lib/A/Bz/A/I_strtolw.v:99` and `I_strtolfix.v:421`. The word at 0xa63e0 is 0x142be8 = `common_flags_dont_use`, and 0x142cde is that object + 0xf6 |
| AUIPC-VALUE | 2 | `lib/A/Rt/RtDStrndupP.v:92` 0xa6770 and `RtDStrndupS.v:279` 0xa6810: the image's instruction at 0x45770 / 0x45810 is an auipc that gives this value. The next ld reads 0xa63e0 / 0xa63f0. In image B the same auipc gives 0xa57bc / 0xa585c, which lie outside `.got` |
| NOT-ADDRESS-LENGTH | 2 | `lib/A/AB01.v:14` 683040 and `lib/B/YB01.v:14` 683044: the `(ELit n)` length of a KZero write |

"Twin only" means the rows that the twin agreement alone accepted (50 rows). The A-to-B relay copies a pointee by its
name, so a twin agreement cannot see an error that was made before the relay. Each of these rows has a second check that
measures this image's word or name.

PROGRAM-GOT-BLOCK (`lib/A/ACeg.v:25` `lib_const_addr := (0xa7068 <= a < 0xa7088)`, `lib/B/YCeg.v:26`, and the comment
`lib/A/ACeg.v:4`): the range [0xa7068, 0xa7088) holds exactly the GOT words whose pointee is in no word of cgif's GOT.
These are `g_rec`, `rec_ncodes`, `rec_codes` and `g_quitting`, the program's own objects. The donor line `lib/A/ACeg.v:24`
is `(0x103b0 <= a < 0x103b8) \/ (0x9ec10 <= a < 0x9ec28)`. Its second range is cgif's own program GOT block (3 words),
and both ranges end at the GOT word of `__start_asan_globals`. The gate paired our first numeral with the donor's first
numeral (a `.rodata` range that our line does not have), so its row shows DIFFERENT-SYMBOL.

### Controls (got-control.txt)

- Planted control: `got-control.sh` on the gate's planted copies. The two planted `.got` cells (`ACeg.v:21` 0xa6450,
  `YCeg.v:22` 0xa5fb0) are FLAG by donor and name. Their base cells are OK, and the planted copies have no other new
  flag. PASS.
- Perturbation on the real tree: 850 accepted rows were judged again with the value perturbed. Still accepted: +4: 0;
  +8: 4; -8: 1; the donor's value: 0. The 5 rows are block comments, and the hand rule GOT-BLOCK-START (or
  GOT-CELL-NAMED) settles them. The per-rule counts are in got-control.txt.
- Hand rules and supplements: each was judged again with +4 / +8 / -8, and all were refused (59 rows).

## Part 2: codeptr 12348302dfd2

### Tool and controls

- `inputs/tool/codeptr.py`: sha256 12348302dfd2, byte-equal to `tools/codeptr/12348302dfd2/codeptr.py` (registry).
  `pautrlen/` from `tools/startup-set/2026-10-30d/pautrlen/`: absint 5acaf718a245, base d3f7ec3c6fa4, compose
  7bf620a82573, names eb031db5a107, rvdis acc3b31392a5. It needs capstone 5.0.7.
- The codeptr README does not give the usage or the controls. Usage is from the tool's docstring. The controls are the
  control pair of record, `tools/codeptr/c0ce606ed1fa/codeptr-controls.sh` (the registry cites it for 12348302dfd2),
  rewritten for local inputs as `codeptr/codeptr-controls.sh`. Output: `codeptr/codeptr-controls.out`, rc 0, PASS:
  - must-find on fuzz_scene: AD1k 22, AD2i 5, AD2j 107, YD1k 22, YD2i 5, YD2j 107 findings. Each line names its paired
    donor file. codeptr c0ce606ed1fa on the same inputs gives the same counts. The registry's record has AD2i / YD2i 6:
    on this fuzz_scene build, 0x9d000 is the end of the PT_LOAD [0x9b178, 0x9d000). In cgif's image, 0x9d000 is the page
    floor of the PT_LOAD at 0x9da00. Both are segment bounds, so codeptr gives them the same meaning and does not count
    0x9d000 as stale.
  - must-find on fuzz_command's images (cgif's unrelocated AD1k / AD2i / AD2j against fuzz_command): 21 / 6 / 106
    findings (A), 21 / 6 / 106 (B). Each line names its paired donor file.
  - must-not-flag: cgif `YF0m.v:289` 0x8065e (525918) is listed as NOT read as an address and is not a finding. This
    holds on fuzz_scene's and on fuzz_command's image B.
- Registered limit (registry: "CELL accepts a different symbol when the value equals the pin word"; the registry's
  false-equal audit gives this version's rows H12, H13 and H14):
  - H12: equal 16 bytes override two different names (codeptr.py:428-431).
  - H13: a donor literal in another slot of the same definition is not judged (:434).
  - H14: `--same` skips the check. This run declares nothing.

  `codeptr/cplimit.py` imports this codeptr (sha checked) and judges those literals again by name. H12: 0 rows (A, B).
  H13: 26 (A), 25 (B). All are triaged below.

### Runs (codeptr/codeptr-run.sh)

Files: AB01 AB03 AB05 AB12 AB1h AB1k AB1w ACej AD1k AD2i AD2j AE3i AF0m (`lib/A`) and their `Y` twins (`lib/B`). These
are the start-up generators' outputs (AF0m, AB12, AD1k, AD2i/AD2j, AB1h/AB1k, AB01/AB03), the unit's generated files and
the tables. Each image's file is checked against its own image and stale-checked against cgif's image, paired with
cgif's own file. No `--same` and no `--not-address` were used.

| image | rc | FINDINGS | of these STALE | UNMEASURED |
|---|---|---|---|---|
| A (codeptr-A.out) | 1 | 25 | 24 | 0 |
| B (codeptr-B.out) | 1 | 26 | 25 | 0 |

### Triage (codeptr-triage.tsv, codeptr/cptriage.py, codeptr/cptriage.out)

102 rows: 51 codeptr findings and 51 cplimit rows. All are OK, and there is no FINDING. Each occurrence of the value in
our file gets a role from the file's own text, and the role's fact is measured:

| role | rows | measured |
|---|---|---|
| K-LENGTH, K-RANGE, RECORD-FIELD | 38 (+4 shared with CELL-VALUE) | a length / bound / size (the tid bound 4194303 in AD2i, the rest in the start-up traces AB01/AB03). The donor file holds it after the same text. For AB01/AB03 also: every other released unit's AB01/AB03 that has the same place (12 units, other images) holds the same value. A kept image count would differ there: the control below shows that the brk page bounds and the rw span differ per unit |
| CELL-VALUE | 8 (+4) | a cell's value. File-backed cells: the image holds it. NOBITS cells written at start-up (0x10101 at `asan_flags_dont_use_directly`+0x70, 0x100000 at `__asan::instance`+0x328): the donor's cell at the same place is the same object + offset in cgif's image |
| INSN-WORD | 14 | AB1h/AB1k instruction words `(W%bv : bv 32)`. Where the file fetches W at a literal address, our image holds W there |
| INSN-FIELD | 2 | AB1k `decode_any (0x333336b7) = Some (Lui 13 209715)`: 209715 = 0x33333 is the lui immediate of the word |
| ROW-START | 14 | AB1w/YB1w rows: V starts a symbol of our image, and the donor's same-named row holds another number (not a copy) |
| RO-CHUNK, RO-CHUNK-END, ZERO-SHADOW | 12 | 0x10330 (AD1k, AD2j, AE3i): the chunk [0x10330, 0x10340) lies between two owned statics of our AF0m list (one ends at its start, one starts at its end; none inside). Chunk ends: an owned static starts there, or our asan_globals descriptor gives the size. The zero-shadow end is the end of the global's full 8-byte granules |
| CELL-ADDR, OWN-STATIC | 7 | `zN (ANum V) W`: our image holds W at V. 0x103b8 is an owned static whose word 0x218a392cd3d5dbf our image holds |
| K-ADDR | 2 | YB01/YB03 0xa7000: the page floor of image B's PT_LOAD at 0xa7c68 |
| IDENT | 1 | YB1w 0x65c98 is part of the identifier `tfib_A_MmapFixedNoAccess_3_insn_arg_shim_0x65c98`. cgif's A and B files have the same identifier, so it is a name, not an address of either image. Nothing reads it (the only hit in `lib/` is its own Definition) |

Controls of the triage rules (cptriage.out):
- The rules were run on the must-find findings (cgif's unrelocated files against our images). They settle 4 of the 60
  values shown, and none of the 4 is wrong in our image:
  - 0x3fffff, the tid bound 4194303, a KRange of the thread id.
  - 0x103b8, the end of the chunk [0x103b0, 0x103b8). Our owned static starts at 0x103b8, and our AD2j has the same
    chunk.
- The quantity rule was run on known image quantities of our `lib/A/AB03.v`. It refuses all three: the brk page bounds
  1542 and 525830 (12 other values in 12 units) and the first rw KWr length 781312 (12 other values).

## Commands

GOT (light; the full run took about 45 s and was run on the build machine):

```
python3 gotcheck.py --lib <unit>/lib --relto <unit> \
  --img A=<asan pin>:<asan twin> --img B=<asan-ubsan pin>:<asan-ubsan twin> \
  --donor-img A=<cgif asan pin>:<twin> --donor-img B=<cgif asan-ubsan pin>:<twin> \
  --gate A=<gate run A>/full.tsv --gate B=<gate run B>/full.tsv --gate R=<gate run R>/full.tsv \
  --out got-cells.raw.tsv --perturb > gotcheck.out
python3 gottriage.py --raw got-cells.raw.tsv --lib <unit>/lib --donor-lib <cgif>/lib \
  --img A=... --img B=... --donor-img A=... --donor-img B=... --out got-cells.tsv > got-triage.out
bash got-control.sh <plant copies> <gate runs> <images> control
```

codeptr (from `inputs/work`, which holds `tool/ c0ce/ ctlimg/ ours/ cgif/ img/`; capstone 5.0.7 on PYTHONPATH):

```
bash ../../codeptr/codeptr-controls.sh > ../../codeptr/codeptr-controls.out
bash ../../codeptr/codeptr-run.sh ../../codeptr A ; bash ../../codeptr/codeptr-run.sh ../../codeptr B
python3 ../../codeptr/cptriage.py --cpdir ../../codeptr --out ../../codeptr-triage.tsv \
  --control ../../codeptr/codeptr-controls.out > ../../codeptr/cptriage.out
```

`inputs/` is not part of the record. It holds the tool copies, the control images, `xunit/` (the other units' `AB01.v`
/ `AB03.v` from `git show repository tree (git tree 1c3596a429a4; internal record):proofs/<project>/<unit>/lib/A/AB0{1,3}.v`), capstone, and the working links.

## Files

- `got-cells.tsv`: one row per `.got` numeral. Columns: file, line, value, pointee (ours), donor_value, donor_pointee,
  name_check, status, then image, in_comment, definition, word, got_index, donor, stated, twin, comment, disagree, qty,
  control, then the triage columns reason, measurement, result, finding_kind, new_value, read_by.
- `got-cells.raw.tsv`: gotcheck's output without the triage columns. A second run on the build machine was byte-equal.
- `codeptr-triage.tsv`: image, file, value, source (codeptr FINDING kind, or cplimit H13 with the two meanings), roles,
  reason, measurement, result, finding_kind, new_value, read_by.
- `control/`: the planted-control runs. `codeptr/`: the codeptr scripts and outputs.
