# Gate 6 — address checker of record now (port_addr_check 3d2eee813cce), image A (fuzz_disco.asan)

Kind: measurement; proves no function. The address checker of record is now `port_addr_check` 3d2eee813cce. Gate 1
(efa19b81e92b, `gate-1-address-check.md`) stands unchanged; this gate re-runs the same command on the same file set with
the newer version, records its counts, the row-by-row difference from gate 1, its planted control, and the triage.

## Command (run.sh `addr3`, every path a variable; no host path)

```
port_addr_check.py --git $HUB --donors-from $DONORS --summary --fail-on-flags \
  --src $CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib --dst $BASE:proofs/libreac/fuzz_disco/lib \
  --paired-only --map A/=A/ --map =Reusable/ \
  --src-image A=$CGIF_BIN.asan --src-image B=$CGIF_BIN.asan-ubsan --src-image P=$CGIF_BIN.plain --src-image U=$CGIF_BIN.ubsan \
  --dst-image A=$PIN_A:$TWIN_A --dst-image B=$PINS/fuzz_disco.asan-ubsan:$TWINS/fuzz_disco.asan-ubsan \
  --dst-image P=$PINS/fuzz_disco.plain:$TWINS/fuzz_disco.plain --dst-image U=$PINS/fuzz_disco.ubsan:$TWINS/fuzz_disco.ubsan \
  --assign '**=auto' --include 'A/**' --cache $OUT/addr3/cache --out $OUT/addr3/pac-A.tsv
```

The arguments are gate 1's, keyed by build letter A / B / P / U; only the tool (`$PAC3`) and the cache / output paths
differ. The destination images carry their unstripped twins as symbol source (twin-check.txt: PT_LOAD 2..4 byte-equal).

## Tool of record (cited by name + sha256, not copied)

`port_addr_check.py` sha256 `3d2eee813cce41c92be6131e56292d73e473d2582156655895ff2a1ce5c73b82`. Its finding classes
(`--list-flag-classes`, 27 classes) are byte-equal to efa19b81e92b's.

Registered limits of this version (classes that can read EQUAL where the values differ in meaning): SAME-CONTENT
accepts two different symbols whose string contents agree up to the NUL (the `str:` label compare); INSN-SAME on a jal /
auipc / lui word compares opcode + rd only (`coarse()` keeps the low 12 bits), not the target; ROUND-CONSTANT-SAME
passes a page-multiple value equal on both sides without reading it; predict mode's MAPS-STRING maps a value by string
content alone; and the named-symbol rule depends on the donor's symbols (recovered here by donor matching, 28 donors).
Gate 7 (roundconst v2) re-reads the ROUND-CONSTANT-SAME / NON-ADDRESS-SAME / SAME-GEOMETRY rows by value.

## Verdict

Exit 4 (findings present). Scope: 395 files paired, 206806 numerals. `FLAGGED 12439 rows in 11 classes`;
`UNMEASURED 3363` (UNPAIRED-FILE-UNMEASURED: a file with no donor twin). Per class: UNPAIRED-PORTED 7697,
UNPAIRED-SOURCE 2959, NON-ADDRESS-CHANGED 1386, DIFFERENT-SYMBOL 212, UNRESOLVED 114, KIND-CHANGED 41,
GEOMETRY-CHANGED 15, SAME-VALUE-DIFFERENT-OBJECT 7, STALE-DONOR-ROUNDED 4, NO-COUNTERPART 3, IMAGE-EXTENT-CHANGED 1.
Images: A `5e39150dd810`, B `cee6f04ad3d4`, P `04988e3ab313`, U `56121de6ba4c`; cgif A `7093581aab04`,
B `1c29845fe605`, P `19dedd1bc682`, U `44a34d2e23b6`.

## Difference from gate 1 (efa19b81e92b, same file set and arguments)

`addr/run_diff.py $OUT/addr/pac-A.tsv $OUT/addr3/pac-A.tsv` (run.sh `addr3/diff`): 206806 rows on each side; **7 rows
differ, all in the `dst_res` column only; every verdict count is identical** (`verdicts identical: yes`). The 7 rows are
UNPAIRED-PORTED rows of `lib/A/AB1w.v` (lines 22, 1077, 1078, 1109, 1265, 1266, 1267: `tfib_E__start`,
`tfib_E__ZN9libunwind15Registers_riscv6jumptoEv`, `tfib_E_unw_getcontext`, `tfib_E_dlsym`, `tfib_E___set_thread_area`,
`tfib_E___unmapself`, `tfib_E___clone`): the newer version names the zero-size symbol whose end each value is ("the end
of _start at 0x30eac, a symbol of size 0, which ends where the next symbol starts") where efa19b81e92b wrote "no object
ends here". Values, verdicts and classes are unchanged.

## Per-row triage

`addr/addr_triage.py` with gate 1's hand table (`addr/hand-triage.tsv`) on this table (run.sh `addr3/triage`):
**12439 flagged, 12439 triaged, 12439 right, 0 DEFECT**, 75 hand rows matching 78 flagged rows, every measurement of the
script true (AB1w 2570 of 2570 function rows; AE37 x2_rodata 415 cells, 0 differ; shadow sets cover all 586 nonzero
start-up shadow bytes; AE3i 129280 bytes). The per-row triage table is byte-equal (comment lines aside) to gate 1's.

**Correction of gate 1's hand row for `lib/A/AB1v.v:14`** (hand-triage.tsv line 78, class OVER-COVER, `right`): that row
is a **DEFECT, fixed in the series**. `tfibmusl_text_count` 16403 is cgif's value kept by the relocation; the file's own
rule (.text end − `tfibmusl_text_start`) / 4 on the A pin gives (0x9eea8 − 0x8f310) / 4 = 16102 (gate 8,
`counts/counts-A.tsv`), the value image B's `lib/Reusable/YB1v.v:10` ships by the same rule. The unit owner ruled it a
defect; the series code commit ac99185f1f10 sets 16102 (build check pending). Gate 1's record and hand table are left
as they were; read their OVER-COVER row as this DEFECT.

## Planted control (must fire)

Gate 1's plant on this version: a copy of `lib/A/AE2k.v` outside the branch with `FF_mask` moved from `0x103b8` to
`0x30eac` (`_start`, a code symbol). Re-run over that one file: exit 4 and the row reads
`DIFFERENT-SYMBOL 0x103a0 -> 0x30eac`, `expected 0x103b8` (`_start+0x0; BND(load1.lo,.text.lo)`). Recorded `FIRED`.

## Re-run on a second machine

run.sh `addr addr3` re-run on a second machine (the same pins and tools by sha256) gave tables row-identical to the
first runs (comment lines, which name the run's own paths, aside): gate 1 `0c24d48f870cb6e5…`, gate 6
`9420c907209e1fd5…` (sha256 of the non-comment lines, first 16 hex).
