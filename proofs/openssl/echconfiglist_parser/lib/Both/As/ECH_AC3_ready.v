(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AKit ECH_AsKit
  ECH_AStmt_C0 ECH_AC0_locks ECH_AStmt_C2 ECH_AC2_small ECH_AStmt_C3.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition GD_RA1 : Z := 0x1f7258.  Definition GD_RA2 : Z := 0x1f727c.  Definition GD_RA3 : Z := 0x1f7298.
Definition GG_RA : Z := 0x1f7654.   Definition GL_RA1 : Z := 0x1fd25c.  Definition GL_RA2 : Z := 0x1fd268.  Definition GL_JOIN : Z := 0x1fd26c.

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.

Ltac unfold_ctx_addrs := unfold wz, A_defctx_global, A_defctx_inited, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once,
  A_defctx_once_ret, A_defctx_exlock, A_defctx_exmeth_bio, A_td_tsd, A_tsd_main, A_defctx, A_destructor_key, A_base_inited, A_stopped,
  A_in_init_config_key, A_base_once, A_base_ret, A_optsdone_lock, A_init_lock, A_keys, LIBKEY0 in *.
(* [comment removed for export] *)
Ltac ctx_statics_back :=
  unfold CTX_statics; unfold wz, A_defctx_global, A_defctx_inited, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once,
    A_defctx_once_ret, A_defctx_exlock, A_defctx_exmeth_bio, A_td_tsd, A_tsd_main, A_defctx, A_destructor_key, A_base_inited, A_stopped,
    A_in_init_config_key, A_base_once, A_base_ret, A_optsdone_lock, A_init_lock, A_keys, LIBKEY0;
  repeat match goal with |- _ /\ _ => split end; try assumption.

Ltac show_goal := match goal with |- ?g => idtac "GOAL:" g end.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Local Ltac land_c2 MU WM ST MI :=
    let PO := fresh "PO" in let MU' := fresh "MU'" in let WM' := fresh "WM'" in let MI' := fresh "MI'" in let ST' := fresh "ST'" in
    intros ? PO; unfold c2_post in PO;
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU' & WM' & MI' & ST' & ?);
    ret_lit_any; rewrite ?unsigned_lit in MU', ST' by lia; carry MU' WM'; extend_munch MU WM MU' WM';
    clear MI ST; rename MI' into MI; rename ST' into ST.

  Lemma getdefctx_ready_spec : getdefctx_ready_stmt.
  Proof.
    unfold getdefctx_ready_stmt. intros until lo. intros TP CS AC ST CEIL LO MI RAE.
    unfold P_get_default_context, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, CRUNONCE_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]).
    pose proof CS as CS0. unfold CTX_statics in CS.
    destruct CS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19).
    (* [comment removed for export] *)
    assert (ACK0 : accessible m A_defctx_tlkey 4).
    { assert (IN : In (0xbdd240, 4, 8) aglobals) by (unfold aglobals; cbn; tauto).
      pose proof (ACONST_global_addressable m 0xbdd240 4 8 AC IN ltac:(lia)) as AD.
      unfold A_defctx_tlkey. eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
    assert (TD0 : rw_cells asegs m A_td_tsd [C8 (wz A_tsd_main)]) by (apply (ACONST_cell m _ _ AC); unfold aconst_cells; cbn; tauto).
    change (id (accessible m A_defctx_tlkey 4)) in ACK0.
    unfold_ctx_addrs.
    carve_frame 16%nat ST.
    do 3 st1. step. step. step. step. step. step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { pose proof crunonce_spec as Q; hnf in Q; eapply Q with (lo := lo) (rest := []); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold CRUNONCE_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia). }
    land_c2 MU WM ST MI.
    (* [comment removed for export] *)
    step. try if_lit. step. st1. rewrite ?sx32_lit by lia. step. try if_lit. step. step. step. step. step.
    eapply evt_cut.
    { pose proof crunonce_spec as Q; hnf in Q; eapply Q with (lo := lo) (rest := []); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold CRUNONCE_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia).
      }
    land_c2 MU WM ST MI.
    (* [comment removed for export] *)
    step. try if_lit. step. st1. rewrite ?sx32_lit by lia. step. try if_lit. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACx : ACONST mx) by (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]);
      assert (ACK : accessible mx 0xbdd240 4) by (unfold id in ACK0; eapply accessible_across; [exact ACK0| exact MU| exact NSW]) end.
    eapply evt_cut.
    { pose proof cgetlocal_spec as Q; hnf in Q; eapply Q with (lo := lo) (rest := []) (k := 1) (v := 0); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, ALOWSH_LO, AHI_LO; lia); try reflexivity. }
    clear ACx ACK.
    land_c2 MU WM ST MI.
    (* [comment removed for export] *)
    step. try if_lit. step. st1. step. step. step. step.
    do 2 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: try reflexivity.
    all: try (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]).
    all: try ctx_statics_back.
  Qed.

  (* [comment removed for export] *)
  Local Ltac land_c3 MU WM ST MI :=
    let PO := fresh "PO" in let MU' := fresh "MU'" in let WM' := fresh "WM'" in let MI' := fresh "MI'" in let ST' := fresh "ST'" in
    intros ? PO; unfold c3_post in PO;
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & -> & MU' & WM' & MI' & ? & ST' & ?);
    ret_lit_any; rewrite ?unsigned_lit in MU', ST' by lia; carry MU' WM'; extend_munch MU WM MU' WM';
    clear MI ST; rename MI' into MI; rename ST' into ST.

  Lemma getglobal_ready_spec : getglobal_ready_stmt.
  Proof.
    unfold getglobal_ready_stmt. intros until lo. intros A0 TP CS AC ST CEIL LO MI RAE. subst a0.
    unfold P_ossl_lib_ctx_get_ex_data_global, GETGLOBAL_READY_STACK, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context,
      CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof CS as CS0. unfold CTX_statics in CS.
    destruct CS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19).
    unfold_ctx_addrs.
    carve_frame 16%nat ST. do 3 st1. step. step. try if_lit. step.
    eapply evt_cut.
    { pose proof getdefctx_ready_spec as Q; hnf in Q; eapply Q with (lo := lo) (x := x); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia);
        try (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]); try ctx_statics_back. }
    land_c3 MU WM ST MI.
    (* [comment removed for export] *)
    st1. if_lit. do 2 st1. if_lit. do 4 st1. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: try (unfold A_defctx_global, A_defctx; apply bv_eq; vm_compute; reflexivity).
    all: try (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]).
  Qed.

  Lemma getandlock_spec : getandlock_stmt.
  Proof.
    unfold getandlock_stmt. intros until lo. cbv zeta. intros A0 A1 A2 RD CS EX XLO AC ST CEIL LO MI RAE. subst a0 a1 a2.
    unfold P_get_and_lock, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CRYPTO_EX_INDEX_BIO in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ((lo, bv_unsigned sp) :: mutex_foot (blk_addr (cx_exlock x))) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold mutex_foot in MU.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]).
    pose proof CS as CS0. unfold CTX_statics in CS.
    destruct CS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19).
    destruct EX as (XI & XZ & XR & XM). unfold MUTEX, MUTEX_SIZE in *. unfold arange in XR.
    destruct (cx_exlock x) as [[xp xa] xn] eqn:Hx. cbn [blk_addr blk_size fst snd] in *.
    pose proof (rw_cells_bound _ _ _ _ XM) as XB. cbn [cells_size csize Nat.add length] in XB.
    assert (XLO' : xa + 40 <= lo) by (destruct XLO as [[Q1 Q2]|[Q1 Q2]]; unfold ALOWSH_LO, AHI_LO in *; lia).
    (* [comment removed for export] *)
    assert (ACpost : forall m', munch [(lo, bv_unsigned sp); (xa + 4, xa + 8)] m m' -> wmono asegs m m' -> ACONST m').
    { intros m' MU' WM'. eapply ACONST_frame; [exact AC| exact MU'| exact WM'|].
      apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
      apply Forall_cons; [eapply aconst_ok_aapp; [exact XLO| lia| lia]| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    assert (ACG0 : accessible m 0xbdd0a0 328).
    { assert (IN : In (0xbdd0a0, 328, 328) aglobals) by (unfold aglobals; cbn; tauto).
      pose proof (ACONST_global_addressable m 0xbdd0a0 328 328 AC IN ltac:(lia)) as AD.
      eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
    change (id (accessible m 0xbdd0a0 328)) in ACG0.
    unfold_ctx_addrs. unfold AIMG_TOP in XR.
    carve_frame 32%nat ST. do 5 st1. st1.
    (* [comment removed for export] *)
    do 3 st1. if_lit. do 3 st1. if_lit. do 5 st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACG : accessible mx 0xbdd0a0 328) by (unfold id in ACG0; eapply accessible_across; [exact ACG0| exact MU0| exact NSW]) end.
    ck8_check_lit ACG 0xbdd0a8. clear ACG MU0 NSW ACG0.
    st1. step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      step.
      eapply evt_cut.
      { pose proof cwrite_lock_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold MUTEX_SIZE, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *; lia). }
      land_c2 MU WM ST MI.
      st1. if_lit. do 4 st1. if_lit. do 7 st1. step.
      release_frame FR ST (bv_unsigned sp). finish.
      all: try (unfold A_defctx_exmeth_bio, A_defctx_global, A_defctx; reflexivity).
      all: try (apply ACpost; assumption).
      all: try (unfold MUTEX, MUTEX_HELD, wz in *; assumption).
      all: try (unfold CTX_statics; rewrite Hx; cbn [blk_addr fst snd]; ctx_statics_back).
    - (* [comment removed for export] *)
      step.
      eapply evt_cut.
      { pose proof cread_lock_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold MUTEX_SIZE, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *; lia). }
      land_c2 MU WM ST MI.
      st1. if_lit. do 4 st1. if_lit. do 7 st1. step.
      release_frame FR ST (bv_unsigned sp). finish.
      all: try (unfold A_defctx_exmeth_bio, A_defctx_global, A_defctx; reflexivity).
      all: try (apply ACpost; assumption).
      all: try (unfold MUTEX, MUTEX_HELD, wz in *; assumption).
      all: try (unfold CTX_statics; rewrite Hx; cbn [blk_addr fst snd]; ctx_statics_back).
  Qed.
End S.
