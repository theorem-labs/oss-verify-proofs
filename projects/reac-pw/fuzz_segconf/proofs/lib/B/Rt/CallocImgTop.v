(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/CallocImgTop.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* reac-pw/fuzz_segconf image B: the image-bound facts the calloc walk (lib/A/DecodeCallocSeed.v, DecodeCallocWrap.v,
   DecodeCallocEntry.v, DecodeCallocTop.v and lib/Lib/DecodeCallocKit.v) cites, under the names libreac/fuzz_decode's
   lib/Reusable/YImgTop.v gives them there: IMG_LO, IMG_TOP, IMG_LO_val, IMG_TOP_val, seg_lo, seg_hi, segs_in,
   segs_in_asan.  This unit's kit has no YImgTop.v; its image bounds are lib/Reusable/YG0f.v kImgLo and kImgEnd (the
   numeral in code), which layout_ok's lo_img conjunct uses, so IMG_LO and IMG_TOP are those two.  segs_in_asan is
   decided by vm_compute against this unit's image module: every loaded segment of fuzz_segconf.asan lies in
   [IMG_LO, IMG_TOP). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.reac_pw.fuzz_segconf.images Require AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0f.
Import ListNotations.
Local Open Scope Z_scope.

Definition seg_lo (s : Segment) : Z := Z.of_N (seg_base s).
Definition seg_hi (s : Segment) : Z := Z.of_N (seg_base s) + Z.of_N (seg_size s).

Definition IMG_LO : Z := YG0f.kImgLo.
Definition IMG_TOP : Z := YG0f.kImgEnd.

Lemma IMG_LO_val : IMG_LO = 0x10000.
Proof. reflexivity. Qed.
Lemma IMG_TOP_val : IMG_TOP = 0x602000.
Proof. reflexivity. Qed.

Definition segs_in (l : list Segment) : bool :=
forallb (fun s => (IMG_LO <=? seg_lo s) && (seg_hi s <=? IMG_TOP)) l.
Lemma segs_in_asan : segs_in AsanUbsan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.
