(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YImgTop.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_role. *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

(* The NOTATION form of libreac/fuzz_scene's and fuzz_identity's YImgTop.v, which role's A layer is written in: 173
   `unfold ... off_img` sites in 104 scene-route files then call lia, and lia cannot see through a Definition. Both
   values are role's own image: measured on the pinned fuzz_role.asan 614cffc0864c and fuzz_role.asan-ubsan
   b255d4935da5. *)
Notation IMG_LO := 0x10000%Z (only parsing).
(* IMG_TOP = page_up of the end of the last PT_LOAD (vaddr + memsz), the same in both ASan pins of reac-pw/fuzz_role:
   fuzz_role.asan ends at 0x5f7c70 and fuzz_role.asan-ubsan at 0x5f7ef0; both page_up to 0x5f8000. fuzz_knock's (and
   fuzz_qdisc's) value was 0x5f3000. *)
Notation IMG_TOP := 0x5f8000%Z (only parsing).
