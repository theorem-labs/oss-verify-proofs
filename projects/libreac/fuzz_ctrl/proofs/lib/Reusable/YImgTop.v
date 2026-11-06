(* The image of this unit's ASan builds, for the files of the shared core that bound the image: the lowest mapped
   address and the page-rounded top of the last PT_LOAD. fuzz_ctrl v1.9.0: fuzz_ctrl.asan's last PT_LOAD ends at
   0x5fd0f0 and fuzz_ctrl.asan-ubsan's at 0x5fdf30, so the top is 0x5fe000 for both images. Same form as
   a working branch's lib/Reusable/YImgTop.v (c8e8b0fa5ec): one place per unit; parsing-only notations so that the
   proofs that unfold off_img and close with lia keep seeing the numbers. *)
From Stdlib Require Import ZArith.

Notation IMG_LO := 0x10000%Z (only parsing).
Notation IMG_TOP := 0x5fe000%Z (only parsing).
