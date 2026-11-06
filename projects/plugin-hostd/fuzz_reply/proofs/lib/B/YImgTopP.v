(* fuzz_reply image B's bounds as DEFINITIONS, under the names fuzz_preset's Reusable/YImgTop.v gives them (IMG_LO,
   IMG_TOP), for the relocated malloc body walk (WrapMallocABodyCall.v), which unfolds them. One source of truth: the
   values are reply's own Reusable/YImgTop.v abbreviations (IMG_LO; IMG_TOP_B, the page-rounded end of image B's last
   PT_LOAD, 0x9fc60 + 0x55b670 = 0x5fb2d0 -> 0x5fc000), which is what preset's IMG_TOP means for its own image. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Definition IMG_LO : Z := YImgTop.IMG_LO.
Definition IMG_TOP : Z := YImgTop.IMG_TOP_B.
