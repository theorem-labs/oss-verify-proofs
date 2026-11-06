(* reac-pw/fuzz_link image A: the image-bound facts the calloc walks cite (lib/A/DecodeCallocSeed.v, DecodeCallocWrap.v,
   DecodeCallocEntry.v, DecodeCallocTop.v, DecodeARowsRt.v).  In the donor (libreac/fuzz_decode) they are part of
   lib/Reusable/YImgTop.v, which there computes IMG_LO / IMG_TOP from both ASan images; link's lib/Reusable/YImgTop.v
   states the two bounds as literals (frame file), so the facts the walks need are here, under the donor's names:
   IMG_LO_val, IMG_TOP_val, seg_lo, seg_hi, segs_in, segs_in_asan.  segs_in_asan is decided by vm_compute against
   link's image module: every loaded segment of fuzz_link.asan lies in [IMG_LO, IMG_TOP) = [0x10000, 0x654000)
   (its last PT_LOAD ends at 0x6534f0). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YImgTop.
Import ListNotations.
Local Open Scope Z_scope.

Definition seg_lo (s : Segment) : Z := Z.of_N (seg_base s).
Definition seg_hi (s : Segment) : Z := Z.of_N (seg_base s) + Z.of_N (seg_size s).

Lemma IMG_LO_val : IMG_LO = 0x10000.
Proof. reflexivity. Qed.
Lemma IMG_TOP_val : IMG_TOP = 0x654000.
Proof. reflexivity. Qed.

Definition segs_in (l : list Segment) : bool :=
forallb (fun s => (IMG_LO <=? seg_lo s) && (seg_hi s <=? IMG_TOP)) l.
Lemma segs_in_asan : segs_in Asan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.
