(* The image bounds of libreac/fuzz_decode's two ASan images, COMPUTED from the images themselves rather than
   copied: [IMG_LO] is the lowest loaded address and [IMG_TOP] the page above the highest, over the loaded
   segments of both images (the ASan statements are about fuzz_decode.asan, the ASan+UBSan ones about
   fuzz_decode.asan-ubsan, and one bound serves both).  Files that need the image's extent cite these two names;
   the measured values appear only in the checks below, which [vm_compute] decides against the image modules.

   Same role as proofs/libreac/fuzz_disco/lib/Reusable/YImgTop.v (origin/ossv/recipes a0d2491b460), which
   fuzz_disco's YCbq.v and YCe5.v cite in off_img; this file computes its two values instead of stating them, so
   no range literal is written by hand anywhere outside the checks.

   The two ASan images' last loaded bytes, read with readelf from the ORIGINAL unstripped binaries
   (fuzz_decode.asan and fuzz_decode.asan-ubsan), are 0x5f5638 (asan) and
   0x5f5bb8 (asan-ubsan); [IMG_TOP_val] below checks the page above both, from the image modules themselves. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.libreac.fuzz_decode.images Require Asan AsanUbsan.
Import ListNotations.
Local Open Scope Z_scope.

Definition seg_lo (s : Segment) : Z := Z.of_N (seg_base s).
Definition seg_hi (s : Segment) : Z := Z.of_N (seg_base s) + Z.of_N (seg_size s).
Definition img_lo_of (l : list Segment) : Z := fold_right (fun s acc => Z.min (seg_lo s) acc) (2 ^ 64) l.
Definition img_hi_of (l : list Segment) : Z := fold_right (fun s acc => Z.max (seg_hi s) acc) 0 l.
Definition page_up (x : Z) : Z := (x + 4095) / 4096 * 4096.

Definition IMG_LO : Z :=
Z.min (img_lo_of Asan.M.loaded_segments) (img_lo_of AsanUbsan.M.loaded_segments).
Definition IMG_TOP : Z :=
page_up (Z.max (img_hi_of Asan.M.loaded_segments) (img_hi_of AsanUbsan.M.loaded_segments)).

(* The checks.  These are the only places in the unit's proofs where the two values are written. *)
Lemma IMG_LO_val : IMG_LO = 0x10000.
Proof. vm_compute. reflexivity. Qed.
Lemma IMG_TOP_val : IMG_TOP = 0x5f6000.
Proof. vm_compute. reflexivity. Qed.

(* Both bounds are page-aligned, and every loaded segment of either image lies inside [IMG_LO, IMG_TOP). *)
Lemma IMG_LO_page : IMG_LO mod 4096 = 0.
Proof. vm_compute. reflexivity. Qed.
Lemma IMG_TOP_page : IMG_TOP mod 4096 = 0.
Proof. vm_compute. reflexivity. Qed.
Definition segs_in (l : list Segment) : bool :=
forallb (fun s => (IMG_LO <=? seg_lo s) && (seg_hi s <=? IMG_TOP)) l.
Lemma segs_in_asan : segs_in Asan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.
Lemma segs_in_asan_ubsan : segs_in AsanUbsan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.
Lemma IMG_lt : IMG_LO < IMG_TOP.
Proof. rewrite IMG_LO_val, IMG_TOP_val. lia. Qed.

(* Each image's own bounds.  [IMG_LO] and [IMG_TOP] range over the loaded segments of BOTH images, so a term about
   one image that uses them also reads the other image's segments.  These four checks show that each bound equals
   the bound computed from one image's loaded segments alone (image A: fuzz_decode.asan, image B:
   fuzz_decode.asan-ubsan); each is decided by [vm_compute] on a closed goal. *)
Lemma img_lo_A : IMG_LO = img_lo_of Asan.M.loaded_segments.
Proof. vm_compute. reflexivity. Qed.
Lemma img_lo_B : IMG_LO = img_lo_of AsanUbsan.M.loaded_segments.
Proof. vm_compute. reflexivity. Qed.
Lemma img_top_A : IMG_TOP = page_up (img_hi_of Asan.M.loaded_segments).
Proof. vm_compute. reflexivity. Qed.
Lemma img_top_B : IMG_TOP = page_up (img_hi_of AsanUbsan.M.loaded_segments).
Proof. vm_compute. reflexivity. Qed.
