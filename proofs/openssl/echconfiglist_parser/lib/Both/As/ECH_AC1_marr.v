(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1
  ECH_AKit ECH_AC1_malloc ECH_AC1_zalloc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Local Ltac prep_statics IM GM :=
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_realloc_impl, A_free_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_aligned_alloc,
      P_CRYPTO_realloc, P_CRYPTO_free, wz in IM, GM.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma acmalloc0_spec : cmalloc0_stmt.
  Proof.
    unfold cmalloc0_stmt, cmalloc0_stmt_at. intros until lo. intros ST CEIL LO MI AC IM GM. acb.
    unfold P_CRYPTO_malloc, FR_CRYPTO_malloc in *. prep_statics IM GM. destruct IM as (IM1 & IM2 & IM3).
    pose proof (aword_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    do 15 step. if_true. step. if_true. do 8 step.
    release_frame FR ST (bv_unsigned sp).
    unfold cmalloc0_post. finish.
    eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor].
  Qed.

  (* [comment removed for export] *)
  Lemma acmalloc_array0_spec : cmalloc_array0_stmt.
  Proof.
    unfold cmalloc_array0_stmt, cmalloc0_stmt_at. intros until lo. intros ST CEIL LO MI AC IM GM. acb.
    unfold P_CRYPTO_malloc_array, FR_CRYPTO_array, FR_CRYPTO_malloc in *. prep_statics IM GM. destruct IM as (IM1 & IM2 & IM3).
    pose proof (aword_range sp) as SPR. pose proof (aword_range a1) as A1R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    do 7 step. zstep. rewrite Z.mul_0_l. change (Z.shiftr 0 64) with 0.
    step. step. if_true.
    zstep. rewrite Z.mul_0_l. do 8 step.
    release_frame FR ST (bv_unsigned sp).
    pose proof acmalloc0_spec as C0. unfold cmalloc0_stmt, cmalloc0_stmt_at, P_CRYPTO_malloc, FR_CRYPTO_malloc in C0.
    eapply evt_mono.
    { eapply C0; [exact ST| exact CEIL| lia| exact MI| | |].
      - eapply ACONST_frame; [exact AC| exact MU| exact WM|]. constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor].
      - unfold IMPL_mem, A_malloc_impl, A_realloc_impl, A_free_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz. auto.
      - unfold GOT_mem, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_aligned_alloc, P_CRYPTO_realloc, P_CRYPTO_free, wz. auto. }
    intros ms' PO. unfold cmalloc0_post in *. destruct PO as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & MU' & WM' & MI' & AC' & ST').
    do 15 eexists. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU']|].
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    split; [exact MI'|]. split; [exact AC'| exact ST'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma acarr_malloc_prefix :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (num size lo : Z),
      0 <= num < 2^32 -> 0 <= size < 2^32 -> 1 <= num * size <= 2^28 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (acarr_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc P_CRYPTO_malloc (num * size) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 num) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_malloc_array) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros HN HS HNS ST CEIL LO MI. acb. unfold P_CRYPTO_malloc_array, P_CRYPTO_malloc.
    pose proof (aword_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    do 7 step; zstep; rewrite (Z.shiftr_div_pow2 _ 64), Z.div_small by lia.
    step; step; if_true; zstep; do 8 step.
    lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => release_frame FR ST (bv_unsigned sp) end. unfold acarr_post. finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma cmalloc_post_back : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc s LB n lo B m m1 mo c,
    xpres H LB (bv_unsigned sp) memflag_foot m m1 ->
    cmalloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m1 mo c ->
    cmalloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo c.
  Proof.
    intros until c. intros XP PO. unfold cmalloc_post in *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p & s' & E & REST).
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, junk, p, s'. split; [exact E|].
    repeat match goal with |- _ /\ _ => split end; try tauto.
    eapply xpres_trans; [exact XP| tauto].
  Qed.

  Lemma acmalloc_array_spec : cmalloc_array_stmt H.
  Proof.
    unfold cmalloc_array_stmt. intros until CH.
    intros VIS A0 A1 HN HS HNS HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL MF IM GM.
    unfold CARRAY_STACK, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK in LO.
    acb. subst a0 a1 tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply acarr_malloc_prefix; [exact HN| exact HS| exact HNS| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [left; cbn; lia| constructor]. }
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (XP1 : xpres H LB (bv_unsigned sp) memflag_foot m m1).
    { eapply (xpres_of_munch H s LB _ memflag_foot _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    pose proof (acmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    eapply (ah_mono H HH).
    { eapply CM with (v := v) (CH := CH) (lo := lo) (B := B) (LB := LB) (s := s) (n := num * size); [exact VIS1| reflexivity| ..].
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]
           | |- as_chain _ _ _ _ => eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]
           | |- forall fp' ra', In _ _ -> _ => exact CHS
           | |- pf_ok _ _ _ _ => exact PF
           | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
           | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
           | |- _ => first [assumption | lia | unfold CMALLOC_STACK, FR_CRYPTO_malloc, AMALLOC_STACK; lia
                              | match goal with |- ?G => idtac "LEFT:" G end]
           end. }
    intros c PO. eapply cmalloc_post_back; [exact XP1|].
    unfold cmalloc_post in PO |- *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p & s' & E & K2 & MP2 & REST).
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, junk, p, s'. split; [exact E|]. split; [exact K2|].
    split; [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]| exact REST].
  Qed.
End W.
