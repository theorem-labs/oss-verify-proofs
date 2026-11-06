(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/Reusable/YImgTop.v at ca77675ebeb (itself proofs/libreac/fuzz_knock/lib/Reusable/YImgTop.v at origin/ossv/recipes 6ebe35ba632, fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_headamp; IMG_TOP set for fuzz_headamp; both bounds in the parsing-only notation form of role's d69ff7857e0. *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

(* The NOTATION form of libreac/fuzz_scene's and fuzz_identity's YImgTop.v, which headamp's A layer is written in (fuzz_role's
   core, relocated): `unfold ... off_img` sites in the scene-route files then call lia, and lia cannot see through a
   Definition. Both values are headamp's own image: measured on the pinned fuzz_headamp.asan f3e0669d2819 and
   fuzz_headamp.asan-ubsan 53edda9bdeeb. *)
Notation IMG_LO := 0x10000%Z (only parsing).
(* IMG_TOP = page_up of the end of the last PT_LOAD (vaddr + memsz), the same in both ASan pins of reac-pw/fuzz_headamp:
   fuzz_headamp.asan ends at 0x5f9630 and fuzz_headamp.asan-ubsan at 0x5f9ab0; both page_up to 0x5fa000. fuzz_knock's (and
   fuzz_qdisc's) value was 0x5f3000. *)
Notation IMG_TOP := 0x5fa000%Z (only parsing).
