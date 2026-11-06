(* The image bounds of libdiginet/fuzz_transport's ASan image, COMPUTED from the image itself rather than copied:
   [IMG_LO] is the lowest loaded address and [IMG_TOP] the page above the highest, over the loaded segments of
   fuzz_transport.asan (image A).  Files that need the image's extent cite these two names; the measured values appear
   only in the checks below, which [vm_compute] decides against the image module.

   The form is libreac/fuzz_decode's lib/Reusable/YImgTop.v over image A alone; this file computes its two values
   instead of stating them, so no range literal is written by hand anywhere outside the checks.

   The image's last PT_LOAD, read from the program headers of the ORIGINAL binary fuzz_transport.asan (vaddr 0xa5d88,
   memsz 0x56f648), ends at 0x6153d0; [IMG_TOP_val] below checks the page above it, from the image module
   itself. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.libdiginet.fuzz_transport.images Require Asan.
Import ListNotations.
Local Open Scope Z_scope.

Definition seg_lo (s : Segment) : Z := Z.of_N (seg_base s).
Definition seg_hi (s : Segment) : Z := Z.of_N (seg_base s) + Z.of_N (seg_size s).
Definition img_lo_of (l : list Segment) : Z := fold_right (fun s acc => Z.min (seg_lo s) acc) (2 ^ 64) l.
Definition img_hi_of (l : list Segment) : Z := fold_right (fun s acc => Z.max (seg_hi s) acc) 0 l.
Definition page_up (x : Z) : Z := (x + 4095) / 4096 * 4096.

Definition IMG_LO : Z :=
img_lo_of Asan.M.loaded_segments.
Definition IMG_TOP : Z :=
page_up (img_hi_of Asan.M.loaded_segments).

(* The checks.  These are the only places in the unit's proofs where the two values are written. *)
Lemma IMG_LO_val : IMG_LO = 0x10000.
Proof. vm_compute. reflexivity. Qed.
Lemma IMG_TOP_val : IMG_TOP = 0x616000.
Proof. vm_compute. reflexivity. Qed.

(* Both bounds are page-aligned, and every loaded segment of the image lies inside [IMG_LO, IMG_TOP). *)
Lemma IMG_LO_page : IMG_LO mod 4096 = 0.
Proof. vm_compute. reflexivity. Qed.
Lemma IMG_TOP_page : IMG_TOP mod 4096 = 0.
Proof. vm_compute. reflexivity. Qed.
Definition segs_in (l : list Segment) : bool :=
forallb (fun s => (IMG_LO <=? seg_lo s) && (seg_hi s <=? IMG_TOP)) l.
Lemma segs_in_asan : segs_in Asan.M.loaded_segments = true.
Proof. vm_compute. reflexivity. Qed.
Lemma IMG_lt : IMG_LO < IMG_TOP.
Proof. rewrite IMG_LO_val, IMG_TOP_val. lia. Qed.

(* The image's own bounds, stated as the bound computed from its loaded segments; each is decided by [vm_compute]
   on a closed goal. *)
Lemma img_lo_A : IMG_LO = img_lo_of Asan.M.loaded_segments.
Proof. vm_compute. reflexivity. Qed.
Lemma img_top_A : IMG_TOP = page_up (img_hi_of Asan.M.loaded_segments).
Proof. vm_compute. reflexivity. Qed.
