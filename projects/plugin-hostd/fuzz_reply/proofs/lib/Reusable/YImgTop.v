(* The image bounds of fuzz_reply's two ASan builds, from each build's own PT_LOADs (page-rounded):
   fuzz_reply.asan       last PT_LOAD [0x9f6e0, 0x5fad50)  -> IMG_TOP_A = 0x5fb000
   fuzz_reply.asan-ubsan last PT_LOAD [0x9fc60, 0x5fb2d0)  -> IMG_TOP_B = 0x5fc000
   first PT_LOAD of both at 0x10000 -> IMG_LO.
   The shared core's off_img (Reusable/YCbq.v, Reusable/YCe5.v) cites IMG_LO and IMG_TOP_A; lib/B's instantiation of
   the same files (lib/B/YCbq.v, lib/B/YCe5.v) cites IMG_TOP_B.  Each build's check against its own segments is in its
   side's tree (lib/B/BImgTopChk.v for the ASan+UBSan image).  Form of proofs/libreac/fuzz_disco/lib/Reusable/YImgTop.v
   (a0d2491b460), with one top per build because fuzz_reply's two tops differ.  The bounds are abbreviations, so a
   citing definition unfolds to the number itself and the donor's `unfold off_img; lia` steps go through unchanged. *)
From Stdlib Require Import ZArith.

Abbreviation IMG_LO := 0x10000%Z.
Abbreviation IMG_TOP_A := 0x5fb000%Z.
Abbreviation IMG_TOP_B := 0x5fc000%Z.
