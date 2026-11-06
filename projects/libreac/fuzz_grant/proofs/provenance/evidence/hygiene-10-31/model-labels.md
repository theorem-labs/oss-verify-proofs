# The allocator model's labels are tags 1..14, not addresses

The allocator model in `lib/Reusable/YG00.v` names its check and spin sites with 14 numbers: the `pc` of
`mcheck b pc`, which fails with `FCheck pc`, the `pc` of `spin pc`, and the `pc` of `fail (FCheck pc)`. Before this
series they were written as 14 decimal numbers that look like code addresses (201364 ... 469488). They are labels,
and this series writes them as the tags 1 to 14.

## The map

| tag | old value | hex | YG00.v line | form | definition | sites (Reusable / A / B) |
|---|---|---|---|---|---|---|
| 1 | 201364 | 0x31294 | 552 | mcheck | `free` | 12 (4/4/4) |
| 2 | 201376 | 0x312a0 | 550 | FCheck | `free` | 12 (4/4/4) |
| 3 | 202260 | 0x31614 | 414 | mcheck | `malloc` | 5 (1/2/2) |
| 4 | 209280 | 0x33180 | 537 | mcheck | `maybe_drain` | 3 (1/1/1) |
| 5 | 210276 | 0x33564 | 499 | mcheck | `recycle_chunk` | 1 (1/0/0) |
| 6 | 212388 | 0x33da4 | 268 | mcheck | `ensure_free_array` | 1 (1/0/0) |
| 7 | 213516 | 0x3420c | 279 | spin | `ensure_free_array` | 2 (2/0/0) |
| 8 | 219184 | 0x35830 | 449 | spin | `enqueue` | 3 (1/1/1) |
| 9 | 221048 | 0x35f78 | 359 | mcheck | `sec_alloc` | 3 (1/1/1) |
| 10 | 222820 | 0x36664 | 286 | mcheck | `map_more_user` | 1 (1/0/0) |
| 11 | 391236 | 0x5f844 | 364 | spin | `sec_alloc` | 3 (1/1/1) |
| 12 | 449860 | 0x6dd44 | 426, 480 | spin | `malloc`, `sec_dealloc` | 9 (3/3/3) |
| 13 | 460508 | 0x706dc | 409 | mcheck | `depot_put` | 3 (1/1/1) |
| 14 | 469488 | 0x729f0 | 408 | mcheck | `depot_put` | 3 (1/1/1) |

The 14 values were read by position from `lib/Reusable/YG00.v`, the unit's own model file. Every occurrence in code
is a model form (`mcheck ... N ;;`, `spin N`, `ISpin N` or `fail (FCheck N)`): 61 sites in 19 files (lib/Reusable 23,
lib/A 19, lib/B 19, lib/U 0). No comment carried one of the values.

## Why they were wrong as addresses

- In both of this unit's images every value lands inside an unrelated function; for example 201364 is
  `Allocator::FindHeapChunkByAddress+0xe0` in image A and `Allocator::ReInitialize+0x47c` in image B.
- The model is shared by the two images, which place the same code at different addresses (`Allocator::Deallocate`
  at 0x3170c in A and 0x318b4 in B; `TryMemCpy` at 0x6deb8 and 0x6e244). So one number cannot be the address of the
  same site in both images.
- The values do not fit the donor's images either (cgif_file_fuzzer, unstripped asan sha256 488e39500746 and
  asan-ubsan sha256 ce511d541cda): most land on an unrelated instruction there too.

The defect was one of fidelity, not soundness: no statement reads a label.

## No statement reads them

1. `FCheck pc` appears only under `IFail _`, and `asafe` maps every `IFail _` to False (`lib/Reusable/YG00.v:608`).
2. `ISpin pc` appears only under `ISpin _`, and every matcher ignores the pc: `atok` (`lib/Reusable/YG01.v:52`),
   `is_spin` (`lib/Reusable/YG01.v:37`) and `srealizes` (`lib/Reusable/YG0d.v:73`).
3. The only functions that read a label are `aspins` (`YG00.v:617`), which nothing uses, and `irun` (`YG00.v:623`),
   which only the Examples `run_malloc`, `run_free`, `secondary_cycle` and `big_cycle` use (`YG00.v:643-670`).
4. Those Examples map every `ISpin` or `IFail` result to one default, and `vm_compute` proves each equal to a success
   value, so the path they walk carries no label.

The pcs at `lib/A/Rt/AF0r.v:274` (249892) and `lib/B/Rt/YF0t.v:272` (250716) are not labels of this model: they are
each image's own `FS_FOUND` (`__asan_stack_malloc_1 + 0x10c` in A, `__asan_stack_malloc_2 + 0x10c` in B), checked
against their definition by `reflexivity`, and they stay.

## The check

The rewrite was made by `model_tags.py` (sha256 e1cb9c4fb27f; internal record), which reads the 14 values by position,
classifies every code occurrence and refuses an unclassified one. Its `--check` run reported `census: equal`, and
after the rewrite:

    git grep -n -w -E '201364|201376|202260|209280|210276|212388|213516|219184|221048|222820|391236|449860|460508|469488' \
      -- ':(glob)projects/libreac/fuzz_grant/proofs/**/*.v' ':(glob,exclude)projects/libreac/fuzz_grant/proofs/**/provenance/**'

lists no line (61 lines in 19 files before). The unit build is the check that every rewritten site still proves.
