(* Theorem Labs, 2026-10: the twins for preset's pinned asan-ubsan image (B) of lib/A/Prog/S1ImgA.v: alloc.c's five
   statics prh_pst (lib/A/PRH_Base.v :206) at the generated prh_img_B (lib/B/PRH_ImgB.v), checked by computation on
   the concrete segments rsegs (lib/B/Img0.v, images.AsanUbsan) and the relro range of the whole-program listing
   instance (lib/B/PAImg_prog.v B_prog_relro_lo / B_prog_relro_hi = PI_prog_B's pa_relro_lo / pa_relro_hi). The checkers and their
   soundness lemmas are S1ImgCheck's (image-free). This file does NOT Require S1ImgA, so image A's instances stay out of B' scope.
   No numeral is typed: every address is prh_img_B's or the segments'. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09 YP08 YL0b YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_prog.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pst_wv_B : pst_allb (wv_b rsegs) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pst_img_b_B : pst_allb (in_img_b rsegs) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pst_ro_b_B :
  pst_allb (fun a => negb (in_ro_b rsegs PAImg_prog.B_prog_relro_lo PAImg_prog.B_prog_relro_hi a)) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pst_writable_B : forall (m : word -> option byte) a,
  Exists (in_zr a) (@prh_pst prh_img_B) -> writable_at rsegs m a.
Proof. intros m a Ha. apply writable_of_wv_b. exact (pst_allb_sound _ _ a pst_wv_B Ha). Qed.

Lemma pst_in_img_B : forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> in_img rsegs a.
Proof. intros a Ha. apply in_img_b_sound. exact (pst_allb_sound _ _ a pst_img_b_B Ha). Qed.

Lemma pst_not_ro_B : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  ~ in_roP rsegs PAImg_prog.B_prog_relro_lo PAImg_prog.B_prog_relro_hi a.
Proof.
intros a Ha Hro. pose proof (pst_allb_sound _ _ a pst_ro_b_B Ha) as H. cbv beta in H.
rewrite (in_ro_b_complete _ _ _ _ Hro) in H. discriminate.
Qed.
