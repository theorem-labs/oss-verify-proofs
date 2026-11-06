(* Theorem Labs, 2026-10: image facts of preset's pinned asan image (A) about alloc.c's five statics prh_pst
   (lib/A/PRH_Base.v :206, at the generated prh_img_A of lib/A/PRH_Img.v), proved by computation on the concrete
   segments rsegs (lib/A/Img0.v, images.Asan) and the relro range of the whole-program listing instance
   (lib/A/PAImg_prog.v A_prog_relro_lo / A_prog_relro_hi = PI_prog_A's pa_relro_lo / pa_relro_hi, so a goal over
   PI_prog_A's fields is this statement by unfolding the instance):
     pst_writable_A : every static byte is writable_at rsegs m, for EVERY m (wview falls back to the writable
                      segment's own byte when m has none, so the fact does not depend on m);
     pst_in_img_A   : every static byte is an image byte (in_img rsegs);
     pst_not_ro_A   : no static byte is read-only (in_roP over rsegs and the relro range).
   Shape: port-fm's FMW_fuzz_alloc_base.v (origin/cold/port-fm-g1 f261040a641) fma_rw :62-65 and fma_in_img
   :107-114, and cgif's YB13.v tfib_rw_window :25-45, whose writability is wview <> None; here the window is not a
   typed address range but alloc.c's statics themselves, checked byte by byte by vm_compute (pst_allb).
   The image-free checkers (wv_b, in_img_b, in_ro_b, pst_allb) and their soundness lemmas now live in
   lib/A/Prog/S1ImgCheck.v (Required Export here, so this file's statements read as before, and B' files can use
   them without loading image A). No numeral is typed: every address is prh_img_A's or the segments'. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09 YP08 YL0b YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Export S1ImgCheck.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- image A ---- *)
Lemma pst_wv_A : pst_allb (wv_b rsegs) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pst_img_b_A : pst_allb (in_img_b rsegs) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pst_ro_b_A :
  pst_allb (fun a => negb (in_ro_b rsegs PAImg_prog.A_prog_relro_lo PAImg_prog.A_prog_relro_hi a)) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pst_writable_A : forall (m : word -> option byte) a,
  Exists (in_zr a) (@prh_pst prh_img_A) -> writable_at rsegs m a.
Proof. intros m a Ha. apply writable_of_wv_b. exact (pst_allb_sound _ _ a pst_wv_A Ha). Qed.

Lemma pst_in_img_A : forall a, Exists (in_zr a) (@prh_pst prh_img_A) -> in_img rsegs a.
Proof. intros a Ha. apply in_img_b_sound. exact (pst_allb_sound _ _ a pst_img_b_A Ha). Qed.

Lemma pst_not_ro_A : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  ~ in_roP rsegs PAImg_prog.A_prog_relro_lo PAImg_prog.A_prog_relro_hi a.
Proof.
intros a Ha Hro. pose proof (pst_allb_sound _ _ a pst_ro_b_A Ha) as H. cbv beta in H.
rewrite (in_ro_b_complete _ _ _ _ Hro) in H. discriminate.
Qed.
