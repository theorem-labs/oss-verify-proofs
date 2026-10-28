(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AKit ECH_AsKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.   (* [comment removed for export] *)

  Lemma ACONST_stack_frame6 : forall m m' lo hi, ACONST m -> munch [(lo, hi)] m m' -> wmono asegs m m' -> aceil <= lo -> ACONST m'.
  Proof.
    intros m m' lo hi AC MU WM CE. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    constructor; [| constructor]. apply aconst_ok_high; cbn [fst snd]; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia.
  Qed.
  Lemma ACONST_stack_obj6 : forall m m' lo hi a n, ACONST m -> munch [(lo, hi); (a, a + n)] m m' -> wmono asegs m m' -> aceil <= lo ->
    aapp a n -> 0 <= n -> ACONST m'.
  Proof.
    intros m m' lo hi a n AC MU WM CE AP NN. eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    constructor; [apply aconst_ok_high; cbn [fst snd]; acb; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    constructor; [| constructor]. eapply aconst_ok_aapp; [exact AP| cbn; lia| cbn; lia].
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

  Lemma sx32_lit : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
  Proof. intros x Hx. apply (sx32_wz x Hx). Qed.

  (* [comment removed for export] *)
  Local Ltac acc_open m a sp lo BC BOK SH BR AC :=
    unfold BIO_ranges, BIOACC_STACK, FR_BIO_set_data, BIO_SIZE in *; acb;
    let BB := fresh "BB" in
    pose proof (rw_cells_bound _ _ _ _ BC) as BB; unfold bio_cells in BB; cbn [cells_size csize Nat.add] in BB;
    unfold bio_ok in BOK; unfold bio_cells, wz in BC;
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB;
    let AP1 := fresh "AP1" in let NS1 := fresh "NS1" in let AH1 := fresh "AH1" in let APOS := fresh "APOS" in let AL16 := fresh "AL16" in
    pose proof BR as (APOS & AL16 & _ & _ & _ & _ & AP1); pose proof (aapp_not_shadowland _ _ AP1) as NS1;
    pose proof (aapp_bounds _ _ AP1 ltac:(lia)) as (_ & _ & AH1 & _); unfold AAPP_HI in AH1;
    assert (ACC' : id (accessible m a 128)) by (unfold id; eapply addressable_accessible; [exact SH| lia| lia| unfold AAPP_HI; lia]);
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (a, a + 128)])
      by (constructor; [cbn; unfold AHI_LO in *; lia| constructor; [cbn; exact NS1| constructor]]).
  Local Ltac acc_reacc a ACC' MU NSW :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 128) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW]) end; clear ACC'.
  Local Ltac acc_close FR ST AC MU WM CEIL :=
    lazymatch type of ST with stk _ _ _ (bv_unsigned ?sp + _) => release_frame FR ST (bv_unsigned sp) end;
    unfold bioacc_post; finish;
    try (lazymatch goal with |- ACONST _ => eapply ACONST_stack_obj6; [exact AC| exact MU| exact WM| exact CEIL| assumption| lia] end).
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br_not := step; let K0 := fresh "K0" in if_cases K0; zify_cond K0; [kill K0|]; clear K0.
  Local Ltac ubchk AL := br_not; step; ubal_by AL; step; if_lit.

  Lemma abiogetdata_spec : biogetdata_stmt H.
  Proof.
    unfold biogetdata_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO SH BR AC ST CEIL LO MI RAE; subst a0 a1.
    acc_open m a sp lo BC BOK SH BR AC. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_get_data.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. acc_reacc a ACC' MU NSW. ubchk AL16.
    (* [comment removed for export] *)
    step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 64).
    st1. do 4 step.
    acc_close FR ST AC MU WM CEIL.
  Qed.

  Lemma abiosetdata_spec : biosetdata_stmt H.
  Proof.
    unfold biosetdata_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO SH BR AC ST CEIL LO MI RAE; subst a0 a1.
    acc_open m a sp lo BC BOK SH BR AC. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_set_data, O_BIO_PTR.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. acc_reacc a ACC' MU NSW. ubchk AL16.
    step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 64).
    st1. do 4 step.
    acc_close FR ST AC MU WM CEIL.
  Qed.

  Lemma abiosetinit_spec : biosetinit_stmt H.
  Proof.
    unfold biosetinit_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO SH BR AC ST CEIL LO MI RAE; subst a0 a1.
    acc_open m a sp lo BC BOK SH BR AC. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_set_init, O_BIO_INIT.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. acc_reacc a ACC' MU NSW. ubchk AL16.
    step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 40).
    st1. do 4 step.
    acc_close FR ST AC MU WM CEIL.
  Qed.

  Lemma abioclearflags_spec : bioclearflags_stmt H.
  Proof.
    unfold bioclearflags_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO SH BR AC ST CEIL LO MI RAE; subst a0 a1.
    acc_open m a sp lo BC BOK SH BR AC. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_clear_flags, O_BIO_FLAGS.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. acc_reacc a ACC' MU NSW. ubchk AL16.
    step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 48).
    (* [comment removed for export] *)
    st1. step. step.
    rewrite (sx32_lit (bio_flags B)) by lia. rewrite (unsigned_lit (bio_flags B)) by lia. rewrite (unsigned_lit x) by lia.
    rewrite (unsigned_lit (Z.lxor x _)) by (apply lxor_ones64_range; lia).
    rewrite land_lnot64 by lia.
    change (Z_to_bv 64 (Z.land (bio_flags B) (Z.lnot x))) with (wz (Z.land (bio_flags B) (Z.lnot x))).
    st1. do 4 step.
    acc_close FR ST AC MU WM CEIL.
  Qed.

  Lemma abiosetflags_spec : biosetflags_stmt H.
  Proof.
    unfold biosetflags_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO SH BR AC ST CEIL LO MI RAE; subst a0 a1.
    acc_open m a sp lo BC BOK SH BR AC. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_set_flags, O_BIO_FLAGS.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. acc_reacc a ACC' MU NSW. ubchk AL16.
    step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 48).
    (* [comment removed for export] *)
    st1. step.
    rewrite (sx32_lit (bio_flags B)) by lia. rewrite (unsigned_lit (bio_flags B)) by lia. rewrite (unsigned_lit x) by lia.
    change (Z_to_bv 64 (Z.lor (bio_flags B) x)) with (wz (Z.lor (bio_flags B) x)).
    st1. do 4 step.
    acc_close FR ST AC MU WM CEIL. all: match goal with |- ?G => idtac "SETF:" G end.
  Qed.

  Lemma abiotestflags_spec : biotestflags_stmt H.
  Proof.
    unfold biotestflags_stmt, bioacc_stmt_at. intros until B; intros A0 A1 XR BC BOK ALO SH BR AC ST CEIL LO MI RAE; subst a0 a1.
    acc_open m a sp lo BC BOK SH BR AC. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_test_flags, O_BIO_FLAGS.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. acc_reacc a ACC' MU NSW. ubchk AL16.
    step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 48).
    (* [comment removed for export] *)
    st1. step.
    rewrite (sx32_lit (bio_flags B)) by lia. rewrite (unsigned_lit (bio_flags B)) by lia. rewrite (unsigned_lit x) by lia.
    do 4 step.
    acc_close FR ST AC MU WM CEIL. all: match goal with |- ?G => idtac "TESTF:" G end.
  Qed.

  Lemma abionext_spec : bionext_stmt H.
  Proof.
    unfold bionext_stmt. intros until B; intros A0 APOS0 BC BOK ALO SH BR AC ST CEIL LO MI RAE; subst a0.
    acc_open m a sp lo BC BOK SH BR AC. destruct BOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold P_BIO_next.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. acc_reacc a ACC' MU NSW.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. ubal_by AL16. step. if_lit.
    step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 72).
    st1. do 4 step.
    acc_close FR ST AC MU WM CEIL. all: match goal with |- ?G => idtac "NEXT:" G end.
  Qed.

  Lemma abiofb64_spec : biofb64_stmt.
  Proof.
    unfold biofb64_stmt. intros until lo; intros AC ST CEIL LO MI RAE.
    unfold BIOACC_STACK, FR_BIO_set_data, P_BIO_f_base64, A_b64_method in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. step. step. do 4 step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: try (eapply ACONST_stack_frame6; [exact AC| exact MU| exact WM| exact CEIL]).
    all: match goal with |- ?G => idtac "FB64:" G end.
  Qed.
End S.
