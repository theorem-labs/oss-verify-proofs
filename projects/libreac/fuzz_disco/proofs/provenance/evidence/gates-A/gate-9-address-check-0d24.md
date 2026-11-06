# Gate 9 — address checker port_addr_check 0d24592683b6, image A (fuzz_disco.asan)

Kind: measurement; proves no function. `port_addr_check` 0d24592683b6 was installed after 3d2eee813cce. Gate 1
(efa19b81e92b) and gate 6 (3d2eee813cce) stand unchanged; this gate re-runs their command on the same file set with
the newer version, and records its counts, the row-by-row difference from gate 6, the triage of every flagged row and
of every row whose verdict moved, and gate 1's planted control.

## Command (run.sh `addr0d24`, every path a variable; no host path)

```
port_addr_check.py --git $HUB --donors-from $DONORS --summary --fail-on-flags \
  --src $CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib --dst $BASE:proofs/libreac/fuzz_disco/lib \
  --paired-only --map A/=A/ --map =Reusable/ \
  --src-image A=$CGIF_BIN.asan --src-image B=$CGIF_BIN.asan-ubsan --src-image P=$CGIF_BIN.plain --src-image U=$CGIF_BIN.ubsan \
  --dst-image A=$PIN_A:$TWIN_A --dst-image B=$PINS/fuzz_disco.asan-ubsan:$TWINS/fuzz_disco.asan-ubsan \
  --dst-image P=$PINS/fuzz_disco.plain:$TWINS/fuzz_disco.plain --dst-image U=$PINS/fuzz_disco.ubsan:$TWINS/fuzz_disco.ubsan \
  --assign '**=auto' --include 'A/**' --cache $OUT/addr0d24/cache --out $OUT/addr0d24/pac-A.tsv
```

The arguments are gate 1's and gate 6's, keyed by build letter A / B / P / U; only the tool (`$PAC0D24`) and the
cache / output paths differ. The run started from an empty cache. cgif's four pins are the ones its harness.yaml
names (sha256 7093581aab04 / 1c29845fe605 / 19dedd1bc682 / 44a34d2e23b6, checked against harness.yaml at `$CGIF_REF`).

## Tool (cited by name + sha256, not copied)

`port_addr_check.py` sha256 `0d24592683b610123346567302caf1bf97e5ac9354cf05799dc7cfc21dc0f4fa`, run from its versioned
directory: the SHA256SUMS beside that directory lists six files (port_addr_check.py, scan_literals.py, inputs_used.py,
insn-targets/insn_targets.py, identity-quotients/qscan.py and imgquant.json) and `sha256sum -c` passes for all six. Its
finding classes (`--list-flag-classes`, 27 classes, FLAG-CLASSES 575d398c6022) are byte-equal to 3d2eee813cce's.

Its owner's notes list seven measured changes against 3d2eee813cce. Five of them close the limits gate 6 names: a value
inside a named symbol is no round constant; SAME-CONTENT and predict mode's MAPS-STRING do not apply where a side names
a symbol; a `jal` whose fetch pc the proof does not state, with two different words, is INSN-CHANGED; the named-symbol
rule is absolute where the target's symbols are the image's own (here all four target images carry their twins'
symbols). The other two: a kept page-round value in a geometry slot (`rw` / `rx` / `ro` / `wx` / `exec`) is judged
against the target's own quantity, and SAME-SYMBOL-ROUNDED never applies inside `.got` (a moved GOT cell is
SLID-TO-NEIGHBOUR). The limits its owner lists for this version are in the MANIFEST role of this file.

## Verdict

Exit 4 (findings present). Scope: 395 files paired, 206806 numerals. `FLAGGED 12517 rows in 12 classes`;
`UNMEASURED 3363` (UNPAIRED-FILE-UNMEASURED). Images: A `5e39150dd810`, B `cee6f04ad3d4`, P `04988e3ab313`,
U `56121de6ba4c`; cgif A `7093581aab04`, B `1c29845fe605`, P `19dedd1bc682`, U `44a34d2e23b6`.

| class | 0d24592683b6 | 3d2eee813cce (gate 6) |
|---|---|---|
| UNPAIRED-PORTED | 7697 | 7697 |
| UNPAIRED-SOURCE | 2959 | 2959 |
| NON-ADDRESS-CHANGED | 1386 | 1386 |
| DIFFERENT-SYMBOL | 212 | 212 |
| UNRESOLVED | 114 | 114 |
| KIND-CHANGED | 105 | 41 |
| GEOMETRY-CHANGED | 15 | 15 |
| SAME-VALUE-DIFFERENT-OBJECT | 11 | 7 |
| STALE-DONOR-CODE-POINTER | 10 | 0 |
| STALE-DONOR-ROUNDED | 4 | 4 |
| NO-COUNTERPART | 3 | 3 |
| IMAGE-EXTENT-CHANGED | 1 | 1 |
| **flagged** | **12517 in 12 classes** | **12439 in 11 classes** |

Of the passing classes only two moved: ROUND-CONSTANT-SAME 143 -> 61 and SAME-SYMBOL 8780 -> 8784.

## Difference from gate 6 (3d2eee813cce, same file set and arguments)

`addr/run_diff.py $OUT/addr3/pac-A.tsv $OUT/addr0d24/pac-A.tsv` (run.sh `addr0d24/diff`). This version writes the
rows in another order, so run_diff.py now pairs rows by their identity (the numeral's file, line, sentence, index, kind
and both values), not by text position; on gate 6's pair it still prints 7 rows, `dst_res` only, verdicts identical.

206806 rows on each side, every identity on both sides. **145 rows differ: 82 verdicts moved, 63 rows differ in the
note only.** Every moved row left ROUND-CONSTANT-SAME (owner's change: a value inside a named symbol is no round
constant): -> KIND-CHANGED 64, -> STALE-DONOR-CODE-POINTER 10, -> SAME-VALUE-DIFFERENT-OBJECT 4 (78 rows from a pass to a
finding), -> SAME-SYMBOL 4 (a pass to a pass). The 63 note-only rows: 61 ROUND-CONSTANT-SAME rows whose note adds "and
inside no named symbol", and 2 IDENT-NAME rows (`A/AFes.v`, `A/AFet.v`) whose note now names the instruction that
loads the cell. No other column differs. No row moved into ROUND-CONSTANT-SAME, SAME-GEOMETRY or NON-ADDRESS-SAME, so
the kept rows gate 7 reads are gate 6's less those 82, with the same values.

## Per-row triage

`addr/addr_triage.py` with gate 1's hand table (`addr/hand-triage.tsv`, unchanged) on this table, the moved rows given
with `--also` (run.sh `addr0d24/triage`): **12517 flagged, 12517 triaged, 12517 right, 0 DEFECT**, 75 hand rows
matching 78 flagged rows; **82 moved rows (78 findings, 4 not findings), 82 triaged, 82 right, 0 DEFECT**. By class:
STARTUP 6785, SYMTAB 2504, NO-PORTED-VALUE 1362, IMAGE-BYTES 1124, SMALL-QUANTITY 181, KERNEL 179, AE3I 148, MAP-SIZE 74,
IDENT 48, SHADOW-SET 30, SEGMENT-TABLE 24, IMAGE-SPAN 21, DERIVED 9, AF0M-CELL 8, REGION-COUNT 6, SYMBOL 6, DECODE 2,
FAKESTACK-OFFSET 2, LOOSE-BOUND 2, OVER-COVER 1, SIZE 1. The OVER-COVER row is `lib/A/AB1v.v:14`, which gate 6 corrects
to a DEFECT fixed in the series code commit ac99185f1f10; read it so here too.

The rules of gates 1 and 6 gave no class to 40 of the moved rows and only the general KERNEL class to 38. Four rules
were added to addr_triage.py for them; each measures its fact before it gives a class, and on the tables of gates 1
and 6 the script's per-row triage is byte-equal to its output before the change (cmp):

| rule | rows | measured fact |
|---|---|---|
| MAP-SIZE | 74 (KIND-CHANGED 64, STALE-DONOR-CODE-POINTER 10): `A/AFk6.v` 2, `AFk8.v` 6, `AFk9.v` 8, `AFkb.v` 3, `AFkd.v` 4, `AFke.v` 12, `AFkh.v` 2, `AFki.v` 2, `AFkk.v` 4, `AFkn.v` 28, `AFkx.v` 2, `AFfg.v` 1; value 262144 | `Reusable/YG00.v` (each file requires it): kUserMapSize = kFreeArrayMapSize = 262144 = 2^18, the sanitizer allocator's map size. The A pin forms 262144 as `lui rd, 0x40` at 11 sites, among them SizeClassAllocator64::PopulateFreeArray 0x3718c (x19, the register `R3_M3` sets at 0x3719c), ::EnsureFreeArraySpace 0x34dc8 and internal_allocator 0x5e9c0 (x12, the memset length; `AFfg.v`'s `do_stretch … len` with return pc 0x5e9d0). The numerals are register values and arguments of that size (`sr_get … 11%bv = SLit 262144`, at `R3_NU` with x12 = 3 and x13 = 50 beside it: the length, protection and flags of an mmap), `page_round_up_Z 262144`, `replace (2 ^ 18) with 262144`, `mkAF 262144 …`. The checker reads the decimal as a code address: in the A pin 0x40000 is a call return site inside `__asan_register_globals` (+0xae8), so 64 rows read as an address on that side only (KIND-CHANGED); in 10 rows both sides read it as a pc, cgif's `UnpoisonBeforeMain+0x80`, and the checker expects 0x410d4 (STALE-DONOR-CODE-POINTER) |
| FAKESTACK-OFFSET | 2 (SAME-VALUE-DIFFERENT-OBJECT): `A/AF0r.v:41` 0x109000, `A/AF0t.v:42` 0x209000 | `FS_FROFF` = kFakeFramesOff + (CID << kStackSizeLog) = 0x9000 + (1 << 20) and 0x9000 + (2 << 20), with `Reusable/YG0f.v` kFakeFramesOff = 4096 + 32768, `Reusable/YG00.v` kStackSizeLog = 20 and each file's own CID (1, 2). Each file's Lemma `frame_addr_cid` adds it to the fake-stack base (frame_addr = ly_F + FS_FROFF + pos * FS_B). The checker read the values as interiors of `internal_alloc_placeholder` / `theDepot` |
| LOOSE-BOUND | 2 (SAME-VALUE-DIFFERENT-OBJECT): `A/AE30.v:1395`, `A/AE6k.v:1388` 0x200000 | Lemma `entD_ro`'s `fst (fst e) + snd (fst e) <= 0x200000` over every entry of `A/AE2y.v` icpt_rodata (7 entries, proved entry by entry): the largest entry end is 0xa9db8, and 0x200000 < kHighMemBeg 0x10007fff8000 (`Reusable/YG0f.v`), which the lemma then shows each entry lies below. A bound, not `theDepot+0x75068` |
| AF0M-CELL | 3 (not findings, ROUND-CONSTANT-SAME -> SAME-SYMBOL): `A/AFgi.v:110`, `A/AFgm.v:98`, `A/AFgn.v:73` | `flit8 0xa5d80 0x100000` equals AF0m.v's const cell at 0xa5d80, width 8 (gate 4 checks every AF0m const cell in every collected state). The fourth moved pass, `A/AF0m.v:132`, is that cell itself (STARTUP) |

## Planted control (must fire)

Gate 1's plant on this version: a copy of `lib/A/AE2k.v` outside the branch with `FF_mask` moved from `0x103b8` to
`0x30eac` (`_start`, a code symbol). Re-run over that one file: exit 4, `FLAGGED 19 rows in 3 classes`, and the row
reads `DIFFERENT-SYMBOL 0x103a0 -> 0x30eac`, `expected 0x103b8` (`_start+0x0; BND(load1.lo,.text.lo)`). Recorded
`FIRED`.

## Re-run

run.sh `addr addr3 addr0d24` re-run into a second, empty output directory (the same pins and tools by sha256): every
verdict line PASS / FIRED, and the tables row-identical to the first runs (comment lines, which name the run's own
paths, aside): gate 1 `0c24d48f870cb6e5…`, gate 6 `9420c907209e1fd5…`, gate 9 `ee4d1927859706a3…` (sha256 of the
non-comment lines, first 16 hex); this gate's moved-row list and per-row triage table are byte-equal (cmp).
