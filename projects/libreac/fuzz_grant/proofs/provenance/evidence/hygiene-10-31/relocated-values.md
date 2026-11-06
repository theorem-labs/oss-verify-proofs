# Values that were carried from the donor as if they were addresses

This unit's proofs were ported from a donor fuzz target. A few numbers were carried over or relocated wrongly: a
count written as though it were an address, a section bound taken from the donor, a table cell naming a function the
image does not hold there. This series corrects or removes them. Each was measured against the image the file is
about, never against the donor and never by hand.

## 1. Two range lengths in image A (`lib/A/AE34.v`)

| line | list | entry | was | now |
|---|---|---|---|---|
| 22 | `musl_sel_ranges` | 0x91724 | 435 | 383 |
| 26 | `icpt_ranges` | 0x42130 | 38 | 36 |

Both were measured on image A's debug twin: the instruction count from 0x91724 to the start of the next function
(`__stdio_exit_needed + 28`) is 383, and the wrapper at 0x42130 is 36 instructions. An independent disassembly of the
same two ranges agreed. Image B's values were already right. Every file that depends on `AE34.v` is recompiled by the
unit build.

## 2. The start-up table cells (`lib/A/AB1w.v`, `lib/B/YB1w.v`)

A cell `tfib_A_<X>` / `tfib_E_<X>` is true by name exactly when its value is the start or the end of the symbol `<X>`
names in that image's own symbol table. Per image, 235 cells are false by that test (142 name another symbol, 50 are
interceptor trampolines, 43 other) and 2 cannot be verified (the end of a size-0 symbol: `tfib_E_start`,
`tfib_E_set_thread_area`). All of them are removed: image A 239 removed and 924 kept, image B 237 removed and 930
kept. Every removed name had no reader: `git grep -nw` found only its own definition before the removal and nothing
after.

`lib/A/AB1w.v` also loses two false section bounds:

- `tfib_rodata_hi` 0x22c0c — `.rodata` ends at 0x22c4c;
- `tfib_text_hi` 0x9b168 — `.text` ends at 0x9b164, and 0x9b168 is where `.tbss` starts.

Image B's two bounds are true of image B and stay. Both files' remaining section cells were checked against their own
image's section headers: every `_lo` equals `sh_addr` and every `_hi` equals `sh_addr + sh_size` of the named section.

## 3. The TOT bound in image A (`lib/A/AFem.v`)

`TOT_range` at line 128 (and the conjunct at line 206) read `2 <= TOT <= 127070`. 127070 = 0x1f05e is an address in
image A's `.rodata`, 8 bytes into the string ` was created by `: the donor's count 127436 relocated as if it were an
address. The tight bound comes from this unit's own definitions:

    TOT = length (ly_tr0 ly) + 1 + depot_frames S          (lib/A/AFem.v:98, lib/B/YFem.v:98)
    lo_tr0 : 1 <= length (ly_tr0 ly) <= 31                 (lib/Reusable/YG0f.v:325)
    depot_frames <= 31 * length d                          (lib/A/AFem.v:38-39)
    DEPOT_MAX = 4096                                       (lib/Reusable/YG01.v:141)
    => TOT <= 31 + 1 + 31 * 4096 = 127008

which is what image B already stated. The old bound was true but weaker, so no proof was false. After the change both
copies read 127008 with the same proof text, and the proved lemma `TOT_range` is itself the evidence for the bound.

## 4. A dead tactic arm in both images (`lib/A/AD1g.v:1069`, `lib/B/YD1g.v:1069`)

Each line ended `apply Z_mod_mult || (change N with (1482 * 4096); apply Z_mod_mult)`, with N = 6201344 in image A and
6205440 in image B. The arm is dead twice over: the first `apply Z_mod_mult` always succeeds there, and the `change`
could not have, since 1482 * 4096 = 6070272, neither N. Both lines now end `apply Z_mod_mult.`

## Values that were checked and KEPT

- `src0_debruijn_len = 124`: the end of the read-only window, not the table's length.
- `src0_vmlock = None`: neither build has a lock symbol; the wait routine is a bare `ret`.
- `tfibmusl_text_count = 16105` (`lib/B/YB1v.v:15`, `lib/A/AB1v.v:14`): true under its own definition, which counts
  4-byte table slots over the range the table builder walks. The 3 slots past `.text` are the 12 bytes the model's
  page-rounded r-x mapping covers, not code. The donor carries the same +3, so this value was recomputed here rather
  than carried.
- The atom range `(aTOT, mkAF 2 131072 0)` (`lib/A/AFek.v:34`, `lib/B/YFek.v:32`): kept byte-equal to the donor's
  line. It is true, and `FACTS_fixed` (`AFem.v:396`) discharges it at `:408` from this unit's own TOT bound, so the
  build checks it. The memory cell at that atom is a different object, written back with `TOT + length tr + 1`, whose
  own maximum is 127008 + 30 + 1 = 127039 (`tr_len` at `AFem.v:121`).
- The atom range `(aN, mkAF 1 4097 0)`: `aN` denotes `nD`, the depot's distinct-id count (`EaN` at `AFem.v:226`, the
  field `U35` at `:251`), and this unit's own `nD_range` (`AFem.v:123`, `YFem.v:123`) is `1 <= nD <= 4097`. Both ends
  of the donor's range equal this unit's lemma.
- `lib/B/Prog/GrantBClose.v:96-97`, on the two non-writable PT_LOADs ending at 0x2f984 and 0x9bfc8: true of the
  image's segment ends, and the check it describes runs over page-rounded records that still lie below the ceiling.
