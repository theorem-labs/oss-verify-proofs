# Image-B class-1 stack_malloc contract for fuzz_uci: the route

core-B's route (../core-B/METHOD.md) for three files; only the file list, one override and one patch differ.

## Donor

fuzz_grant's RELEASED files at recipes 4f87de75d67 (the same release core-B ports): lib/B/Rt/YF0r.v (the code table,
the symbolic runs, the probe loop), lib/B/Rt/YF0s.v (tfib_stack_malloc_at and the corollary stack_malloc1_contract,
line 515) and lib/Reusable/YF0v.v (own_free_frame / own_free_frame_shadow, which YF0s.v uses). The released-proof lookup
found no fuzz_uci class-1 contract (released or in flight), so the grant-B proof is ported. `../core-B/mkdon.sh
4f87de75d67 fuzz_grant B` normalises the donor (lib/B/Rt/* -> Rt/*, lib/Reusable/* -> root).

## Bodies first

Before the relocation every body the two proofs step through was compared instruction by instruction with fuzz_grant's
(bytecmp.py, BYTECMP.md): the code table's rows and every callee of the class-1 code, 13 bodies, all equal up to
relocation. fuzz_grant's table also covers __asan_stack_malloc_0 / _2 / _4, which fuzz_uci does not link.

## Tool and inputs

`run.sh`: port_core 0e4e065eab9f in image-B mode (`--remap-images --reusable-dir B --kernel-dir Reusable`), core-B's
`--old-syms`, `--old-prog 80a3c:86640`, rename set (`GrantB=UciB GrantSyms=UciSyms GrantB_syms=UciB_syms
GrantB_ok=UciB_ok`), `--no-stage` list and `--kernel-image` / `--known-elf` images; `--files files-sm1.txt`. Target lib =
this branch's lib (image A's core, the image-B start-up layer and the image-B core): every module the three files
Require is KEPT from it except YF0v, which the unit's lib/Reusable lacks and which the run stages once, into
lib/Reusable (it states no image value).

## Values no rule decides, and the one structural change

- `overrides-sm1.tsv`, one value: YF0s.v:255 the low-shadow bound kLowShadowBeg + IMG_TOP / 8 = 2148227072
  (`measure-sm1.py`, `measure-sm1.out`: the same rule on fuzz_grant.asan-ubsan prints the donor's 2148230656). port_core
  read the donor value as the shadow of a .bss address and wrote 2148227312, which the proof cannot use.
- `B-fs-ranges.patch`: YF0r.v's code table without fuzz_grant's __asan_stack_malloc_0 / _2 / _4 rows, which port_core
  refuses (code-no-counterpart): fuzz_uci links class 1 only (keyset classes), and the class-1 code calls none of them.

## Apply and headers

`apply-sm1.sh` copies the stage-out by --apply's rule (nothing overwritten; applied.txt), because of core-B's known
FAIL row `rename-new-undeclared UciSyms`. `header-sm1.py` (comments only; code bytes checked unchanged): the donor's
Copyright, SPDX and Modified lines stay, undated and without the branch name they cited; port_core's line is replaced
by one notice naming the donor file at its release commit, the donor image and the target image.
`header-sm1-restore.py LIB HUB` then applies the corrected header rule (the repository's docs/adding-a-proof.md
requirement 7): every inherited licence line (Copyright, SPDX, each donor `Modified by` line) is restored byte for byte
from the donor blob at recipes 4f87de75d67, with only the release scrub table applied to it (a cold branch name becomes
`a working branch`). That puts back the donor's dates, and undoes port_core's rename inside inherited notice text
(`TfibSyms renamed GrantSyms`). Our added line gets the head `Modified by Theorem Labs, 2026-10:`. Code bytes are
checked unchanged, and no cold branch, host path or agent name is left in any comment.

## Gates

GATES.md: the flag gate, codeptr, keyset and the range-table check in place of atable, the by-value check, v10,
yh03check (N/A) and the build, each with a planted control (`gates/run-gates.sh`, records in records/).
