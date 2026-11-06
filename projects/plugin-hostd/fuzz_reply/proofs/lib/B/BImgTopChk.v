(* The ASan+UBSan image's own bounds: every loaded segment of fuzz_reply.asan-ubsan lies in
   [YImgTop.IMG_LO, YImgTop.IMG_TOP_B), and IMG_TOP_B is its page-rounded top (some segment ends in the last page), so
   lib/B's off_img (lib/B/YCbq.v, lib/B/YCe5.v) classifies no image byte off-image and no non-image byte above the
   image in. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YImgTop.
Local Open Scope Z_scope.

Lemma b_segs_in_img :
  forallb (fun seg => (IMG_LO <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? IMG_TOP_B))%bool
    AsanUbsan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.

Lemma b_top_tight :
  existsb (fun seg => (IMG_TOP_B - 4096 <? Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool
    AsanUbsan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.

Lemma b_lo_tight :
  existsb (fun seg => (Z.of_N (seg_base seg) <? IMG_LO + 4096))%bool AsanUbsan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.
