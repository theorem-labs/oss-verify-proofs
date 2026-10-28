(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Cells Step Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import HMLib HM AHeapR AH0Spec0 AH0Facts AH0Base AH0Layout AH0Mem1.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition partials_okb : bool :=
  forallb (fun gk => bv_eqb (img_shb (0x7fff8000 + fst gk)) (Z_to_bv 8 (snd gk))) img_partials.
Lemma partials_ok : partials_okb = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma zero_ok : nz_clear img_shadow0 CELLS_lowshadow = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma prist_in : forall x, rtc_prist x -> (0x10000 <= x < 0xf7d10) \/ (0xf7d2c <= x < 0x106340).
Proof.
  intros x H. unfold rtc_prist, rtc_pristine in H. unfold AGLOB_LO, AGLOB_HI in H.
  repeat (apply Exists_cons in H as [H|H]; [cbn in H; lia|]). apply Exists_nil in H. destruct H.
Qed.

Section XR0.
  Context {hAR : arun}.
  Variable mem : word -> option byte.
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  Hypothesis HCOM : Forall (cell_ok ASEGS mem) (cells_common p).
  Let HF := HF mem p HCOM.
  Local Ltac zdec := repeat match goal with |- _ /\ _ => split end;
    first [ apply Z.leb_le; vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity | apply Z.eqb_eq; vm_compute; reflexivity ].
  Local Ltac orc :=
    lazymatch goal with |- ro_cells asegs ?m ?A ?cs =>
      apply (chk_ro_cells m p CT_COMMON HF QLit A cs);
      [ vm_compute; reflexivity | cbn; repeat split; reflexivity | zdec | zdec ] end.

  (* [comment removed for export] *)
  #[using="HCOM"] Lemma HF_low : Forall (cell_ok ASEGS mem) (cells_lowshadow p).
  Proof.
    apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) HCOM c). unfold cells_common. rewrite !in_app_iff. tauto.
  Qed.
  #[using="p HCOM HF"] Lemma HF_img1 : AsanMainEntryKit.cell_ok ASEGS mem (CImg 0x10000 0xf7d10).
  Proof. exact (proj1 (Forall_forall _ _) HF (CImg 0x10000 0xf7d10) ltac:(apply in_map_iff; exists (TImg 0x10000 0xf7d10); split; [reflexivity | unfold CT_COMMON; rewrite !in_app_iff; left; cbn; tauto])). Qed.
  #[using="p HCOM HF"] Lemma HF_img2 : AsanMainEntryKit.cell_ok ASEGS mem (CImg 0xf7d2c 0x106340).
  Proof. exact (proj1 (Forall_forall _ _) HF (CImg 0xf7d2c 0x106340) ltac:(apply in_map_iff; exists (TImg 0xf7d2c 0x106340); split; [reflexivity | unfold CT_COMMON; rewrite !in_app_iff; left; cbn; tauto])). Qed.

  #[using="p HCOM HF"] Theorem h0_asan_rtc : asan_rtc mem.
  Proof.
    split.
    - unfold rtc_cells. repeat (apply Forall_cons; [unfold rtc_holds, rtc_mkcell; orc|]). apply Forall_nil.
    - intros a Ha. unfold wa. destruct (prist_in a Ha) as [H|H]; [exact (HF_img1 a H) | exact (HF_img2 a H)].
  Qed.

  #[using="p HCOM"] Theorem h0_img_shadow_ok : img_shadow_ok asegs AL0 mem.
  Proof.
    intros g Hg NR. pose proof Hg as Hg'. unfold IMG_GLO, IMG_GHI in Hg'. unfold shadow_of, AL0. cbn [al_sb]. rewrite (Z.mul_comm 8 g), Z.div_mul by lia.
    assert (B1 : forall b, mem (Z_to_bv 64 (2147450880 + g)) = Some b -> bytes_at asegs mem (2147450880 + g) [b]).
    { intros b Hb. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace i with 0%nat by lia.
      cbn [nth_error]. rewrite Z.add_0_r. rewrite asegs_ASEGS. unfold mrd, wa. rewrite Hb. reflexivity. }
    destruct (Z.eq_dec (img_shval g) 0) as [Z0|NZ].
    - rewrite Z0. apply B1. apply (me_img_shadow_zero img_shadow0 zero_ok mem p HF_low g); [unfold img_shadow0; rewrite Z0; reflexivity | lia].
    - apply B1. pose proof (img_shval_partial g NZ NR) as IN.
      pose proof (proj1 (forallb_forall _ _) partials_ok (g, img_shval g) IN) as E. cbn [fst snd] in E. apply AVmLib.bv_eqb_eq in E.
      rewrite <- E. apply (me_img_shadow_granule mem p HF_low). lia.
  Qed.

  #[using="p HCOM HF"] Theorem h0_xf_cells : xf_cells mem.
  Proof. unfold xf_cells. orc. Qed.

  #[using="p HCOM HF"] Theorem h0_XR : XR mem.
  Proof. split; [exact h0_asan_rtc | split; [exact h0_img_shadow_ok | exact h0_xf_cells]]. Qed.
End XR0.
