# fuzz_transport fake-stack class 5: how the relocation is made, and what it waits on

Proves no function (kind: measurement). No relocated .v file is committed: every donor file Requires this unit's image
core, which does not exist yet (see "Waits on").

## One command

    run.sh WT HUB DONOR_DIR TARGET_DIR ALRELOC            # check + dry run, writes nothing in WT
    RECORD_A=<A record> RECORD_B=<B record> run.sh WT HUB DONOR_DIR TARGET_DIR ALRELOC --write

WT = this unit's worktree, HUB = the git hub holding origin/ossv/recipes 781f46bc05cd, DONOR_DIR / TARGET_DIR = the
pipeline directories of plugin-hostd and libdiginet (bin/ or result/bin/, and unstripped/), ALRELOC = alreloc of record
a5c53bb2bed4 (it reads align/keep-numerals.txt beside itself). Nothing in run.sh or class5cmp.py names a fuzz_transport
address: the pins come from WT's harness.yaml, every target value from the images. A re-pin is the same command.

Per image (A = asan, B = asan-ubsan) run.sh:
1. checks each image file against its pin (fuzz_command's at 781f46bc05cd, fuzz_transport's in WT);
2. class5cmp.py: pairs every range of the donor's code tables (RtSM5T.v fs_ranges, RtSF5.v sf_ranges) with the target
   (by function name, or by the class-5 body's call when the name has several copies), compares each walked range and
   its whole function with the comparison kit of record cmpkit 4bbd3a74be89 (strictcmp2 16982e3ef42b; copy in
   tools/cmpkit-4bbd3a74be89/, SHA256SUMS checked, twins proved by its drvcmp.py twins; BYTECMP-cmpkit.md), and writes
   the resolve lines (resolve-<I>.txt);
3. controls: the donor against itself passes and moves no value; one planted word (`or` for the first `and` of
   __asan_stack_malloc_5) in a copy of the target is caught;
4. alreloc with those resolve lines on lib/<I>/Rt/{RtSM5T,RtSM5,RtSF5,RtSMxA,RtStack}.v;
5. checkrep.py: every row of alreloc's per-numeral report checked against the two ELFs, not by alreloc's rules: a
   symbol / function / object row must name the same symbol + offset on both sides, a .got-slot row two cells holding
   the same symbol + offset, a derived image bound the two images' page-rounded ends (or / 8); a `gap` row is refused;
   every value moved by its offset inside a symbol is listed for a reader to confirm it is an address. Controls: on
   alreloc's report made without the resolve lines it refuses the four `gap` rows per image and lists FS_FROFF 0x509000,
   0x309000 and 0x600000 as moved; on an empty report it fails;
6. with --write: the donor's leading comment block is put back byte for byte, CmdBSyms becomes the record outside it,
   and one `(* Modified by Theorem Labs, 2026-10: ... *)` notice is added.

Result on the current pins (out/run.log, dry run on this worktree; out/write-test.log, --write into a scratch copy):
both images PASS (11 ranges each, 0 real, 0 differing targets), both controls hold, alreloc 0 UNMAPPED, checkrep 0
wrong rows; the one value moved inside a symbol is common_flags_dont_use + 0x89 (A 0x142c71 -> 0x13e5b1, B 0x1427f1 ->
0x13e231), the flag byte the walk reads (a cell of RtSM5T.v fsA_rodata): an address.

## Why the resolve lines exist (alreloc a5c53bb2bed4, measured on the current pins)

- .got cells read by the walked code: alreloc's `gap` rule maps a cell by its offset in .got, which is wrong when the two
  .got sections differ in layout. Image A: 0xa70f0 -> 0xa4d90 and 0xa7100 -> 0xa4da0, both past fuzz_transport.asan's
  .got end 0xa4d88; the cells holding the same values (0x1, 0x8), read by the paired instructions, are 0xa4d70 /
  0xa4d80. Image B: 0xa6c50 -> 0xa4a10 and 0xa6c60 -> 0xa4a20 against 0xa49f0 / 0xa4a00. class5cmp takes every such
  value from the paired instruction.
- Model constants: the symbol rule maps FS_FROFF 0x509000 (RtSM5T.v `Definition FS_FROFF`) to 0x504940 (theDepot +
  0x376068 of the target) with no flag, and the comment values 0x309000 (class 3's FS_FROFF) and 0x600000 (preset's
  image top) the same way; it reports 82496 and 1441792 UNMAPPED. All are kept (MODEL in class5cmp.py).
- An anonymous .rodata constant read by __asan_stack_free_5 (donor 0x10340): its target is the paired auipc's
  (A 0x10338, B 0x10348).
- The jal to the MemToShadow copy (OFFSET-UNSURE): the paired call's target.
- Header and notice lines are inherited byte for byte; RtStack.v's numerals are all in a comment that names the donor
  image it was measured on: kept.

## Donor closure (plugin-hostd/fuzz_command, origin/ossv/recipes 781f46bc05cd)

Relocated per image: lib/<I>/Rt/RtSM5T.v (class-5 code table and walk stages), RtSM5.v (cmd_stack_malloc5_contract),
RtSF5.v (cmd_stack_free5_contract), RtSMxA.v, RtStack.v (astack_free_cls_realizes). Not relocated: RtSM1T.v, the donor's
class-1 walk (its code table lists the donor's classes 0 1 3 4 5 7); RtSF5.v uses only its add_fact, st_ok_add_fact and
aview_of_val_mem, which the class-1 walk this unit adopts provides (grant's YF0r.v defines the same three).
The image core they Require: A/{AB1q,AB1v,AB1w,AE20,AE2y,AE34,AF0l,AF0m,AF0x}.v, B/{YB1q,YB1v,YB1w,YE20,YE2y,YE34,
YF0l,YF0m,YF0x}.v and 43 ASan files of lib/Reusable; the one premise beyond AR_laws / fs_iface is the core's symbol
record (fields ts_code, ts_tp, ts_tsd, ts_const). The walk reads these cells, which must be rows of the core's
Tfib_const: the 8 runtime cells of RtSM5T.v fsA_rodata, TP - 88, TP - 8, *(TP - 8) + 8, and the AT 48 / AT 56 cells.

## Waits on

This unit's image-A and image-B core (start-up layer and core port). Then: run.sh --write with the record names, point
RtSF5.v's three RtSM1T lemmas at the adopted class-1 walk, cb build with 4 PINNED, and the gates of reac-repacer/fuzz_uci's
stackmalloc1-B record (flag gate, codeptr, rangetab / keyset, by-value).
