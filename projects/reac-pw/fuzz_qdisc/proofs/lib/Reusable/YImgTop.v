(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YImgTop.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_qdisc. *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Definition IMG_LO : Z := 0x10000.
Definition IMG_TOP : Z := 0x5f3000.
