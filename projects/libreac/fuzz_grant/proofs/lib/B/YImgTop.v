(* The image of this unit's ASan+UBSan build (image B; the twin of lib/Reusable/YImgTop.v, which is image A), for the files of the shared core that bound the image: the lowest mapped
   address and the page-rounded top of the last PT_LOAD of fuzz_grant.asan-ubsan (pin fde52226dc48; its last segment ends at 0x5fa1f0, so the
   top is 0x5fb000; image A's top is 0x5fa000, one page lower). One place per unit: a unit that copies the core changes these two numbers and nothing else.
   They are parsing-only notations, not definitions, so that the many proofs that unfold off_img and close the goal
   with lia keep seeing the numbers. *)
From Stdlib Require Import ZArith.

Notation IMG_LO := 0x10000%Z (only parsing).
Notation IMG_TOP := 0x5fb000%Z (only parsing).
