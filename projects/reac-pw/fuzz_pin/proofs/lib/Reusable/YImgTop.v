(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YImgTop.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_pin; IMG_TOP set to fuzz_pin's image top. *)
(* IMG_TOP = page_up of the end of the last PT_LOAD, the same in both ASan pins of reac-pw/fuzz_pin: fuzz_pin.asan
   3e4859aed23f (last PT_LOAD 0x9ad48 + memsz 0x55b130 = 0x5f5e78) and fuzz_pin.asan-ubsan d6f83d301522 (ends at
   0x5f5f78); both page_up to 0x5f6000. fuzz_knock's value was 0x5f3000. *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Definition IMG_LO : Z := 0x10000.
Definition IMG_TOP : Z := 0x5f6000.
