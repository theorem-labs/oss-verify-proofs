(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C6_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br_not := step; let K0 := fresh "K0" in if_cases K0; zify_cond K0; [kill K0|]; clear K0.

  (* [comment removed for export] *)
  Local Ltac acc_facts BC BOK ST :=
    unfold BIOACC_STACK, FR_BIO_set_data, BIO_SIZE in *;
    let BB := fresh "BB" in
    pose proof (rw_cells_bound _ _ _ _ BC) as BB; unfold bio_cells in BB; cbn [cells_size csize Nat.add] in BB;
    unfold bio_ok in BOK;
    unfold bio_cells, wz in BC.

  Lemma biogetdata_spec : biogetdata_stmt.
  Proof.
    unfold biogetdata_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO ST LO MI RAE; subst a0 a1.
    acc_facts BC BOK ST. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_get_data.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. st1. do 4 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma biosetdata_spec : biosetdata_stmt.
  Proof.
    unfold biosetdata_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO ST LO MI RAE; subst a0 a1.
    acc_facts BC BOK ST. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_set_data.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. st1. do 4 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  Lemma biosetinit_spec : biosetinit_stmt.
  Proof.
    unfold biosetinit_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO ST LO MI RAE; subst a0 a1.
    acc_facts BC BOK ST. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_set_init.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. st1. do 4 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma land_lnot64 : forall f x, 0 <= f < 2^64 -> 0 <= x < 2^64 ->
    Z.land f (Z.lxor x 18446744073709551615) = Z.land f (Z.lnot x).
  Proof.
    intros f x Hf Hx. apply Z.bits_inj'. intros n Hn.
    rewrite !Z.land_spec, Z.lxor_spec, Z.lnot_spec by lia.
    change 18446744073709551615 with (Z.ones 64).
    destruct (Z.ltb_spec n 64) as [L|L].
    - rewrite Z.ones_spec_low by lia. rewrite Bool.xorb_true_r. reflexivity.
    - assert (T : Z.testbit f n = false).
      { destruct (Z.eq_dec f 0) as [->|NZ]; [apply Z.testbit_0_l|].
        apply Z.bits_above_log2; [lia|]. apply (proj1 (Z.log2_lt_pow2 f n ltac:(lia))).
        apply (Z.lt_le_trans _ (2^64)); [lia|]. apply Z.pow_le_mono_r; lia. }
      rewrite T. reflexivity.
  Qed.

  Lemma lxor_ones64_range : forall x, 0 <= x < 2^64 -> 0 <= Z.lxor x 18446744073709551615 < 2^64.
  Proof.
    intros x Hx.
    assert (NN : 0 <= Z.lxor x 18446744073709551615) by (apply (proj2 (Z.lxor_nonneg _ _)); lia).
    split; [exact NN|].
    destruct (Z.eq_dec (Z.lxor x 18446744073709551615) 0) as [E|NE]; [rewrite E; lia|].
    apply (proj2 (Z.log2_lt_pow2 (Z.lxor x 18446744073709551615) 64 ltac:(lia))).
    assert (L63 : Z.log2 18446744073709551615 = 63) by reflexivity.
    eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
    apply Z.max_lub_lt; [| reflexivity].
    destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia))). lia.
  Qed.

  Lemma bioclearflags_spec : bioclearflags_stmt.
  Proof.
    unfold bioclearflags_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO ST LO MI RAE; subst a0 a1.
    acc_facts BC BOK ST. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_clear_flags.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. st1. step. step.
    rewrite (sx32_lit (bio_flags B)) by lia. rewrite (unsigned_lit (bio_flags B)) by lia. rewrite (unsigned_lit x) by lia.
    rewrite (unsigned_lit (Z.lxor x _)) by (apply lxor_ones64_range; lia).
    rewrite land_lnot64 by lia.
    change (Z_to_bv 64 (Z.land (bio_flags B) (Z.lnot x))) with (wz (Z.land (bio_flags B) (Z.lnot x))).
    st1. do 4 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  Lemma biosetflags_spec : biosetflags_stmt.
  Proof.
    unfold biosetflags_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO ST LO MI RAE; subst a0 a1.
    acc_facts BC BOK ST. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_set_flags.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. st1. step.
    rewrite (sx32_lit (bio_flags B)) by lia. rewrite (unsigned_lit (bio_flags B)) by lia. rewrite (unsigned_lit x) by lia.
    change (Z_to_bv 64 (Z.lor (bio_flags B) x)) with (wz (Z.lor (bio_flags B) x)).
    st1. do 4 step.
    release_frame FR ST (bv_unsigned sp). finish. all: match goal with |- ?G => idtac "SETF:" G end.
  Qed.

  Lemma biotestflags_spec : biotestflags_stmt.
  Proof.
    unfold biotestflags_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO ST LO MI RAE; subst a0 a1.
    acc_facts BC BOK ST. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_test_flags.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. st1. step.
    rewrite (sx32_lit (bio_flags B)) by lia. rewrite (unsigned_lit (bio_flags B)) by lia. rewrite (unsigned_lit x) by lia.
    do 4 step.
    release_frame FR ST (bv_unsigned sp). finish. all: match goal with |- ?G => idtac "TESTF:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma bionext_spec : bionext_stmt.
  Proof.
    unfold bionext_stmt. intros until B; intros A0 APOS BC BOK ALO ST LO MI RAE; subst a0.
    acc_facts BC BOK ST. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_next.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. br_not. st1. do 4 step.
    release_frame FR ST (bv_unsigned sp). finish. all: match goal with |- ?G => idtac "NEXT:" G end.
  Qed.

  Lemma biofb64_spec : biofb64_stmt.
  Proof.
    unfold biofb64_stmt. intros until lo; intros ST LO MI RAE.
    unfold BIOACC_STACK, FR_BIO_set_data, P_BIO_f_base64, A_b64_method in *.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. step. step. do 4 step.
    release_frame FR ST (bv_unsigned sp). finish. all: match goal with |- ?G => idtac "FB64:" G end.
  Qed.
End S.