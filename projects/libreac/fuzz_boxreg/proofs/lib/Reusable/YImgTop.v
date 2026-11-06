(* libreac/fuzz_boxreg's image range, one named place for every file that states it.
   Both pinned ASan images (index/binaries.tsv at c8557374ad2e: fuzz_boxreg.asan eacfa205..., fuzz_boxreg.asan-ubsan
   7620eb05...) load from 0x10000; their last loaded segments end at 0x5f57f0 (asan) and 0x5f5c30 (asan-ubsan), which
   both round up to the page 0x5f6000. Notations, not definitions, so that lia and vm_compute see the numerals in every
   proof that uses them. *)
From Stdlib Require Import ZArith.
Notation IMG_LO := 0x10000%Z (only parsing).
Notation IMG_TOP := 0x5f6000%Z (only parsing).
