(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_LibState ECH_C0_stmt ECH_C0_locks ECH_C1_stmt ECH_C1_free ECH_C2_stmt ECH_C2_small ECH_C5_stmt ECH_C5_small ECH_C3_stmt ECH_C3_ready ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma cnewex_ready_spec : cnewex_ready_stmt.
  Proof.
    unfold cnewex_ready_stmt. intros until lo. cbv zeta. intros A0 A1 A2 TP ADP ADAL AD ADLO OFF CS EX SEP ST CEIL LO MI IM GM RAE. subst a0 a1 a2.
    unfold P_CRYPTO_new_ex_data, CNEWEX_READY_STACK, FR_CRYPTO_new_ex_data, FR_ossl_crypto_new_ex_data_ex, FR_ossl_lib_ctx_get_ex_data_global,
      GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK,
      FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CRYPTO_EX_INDEX_BIO in *. hcb.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (ad, ad + 16) :: mutex_foot (blk_addr (cx_exlock x))) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold mutex_foot in MU.
    pose proof CS as CS0. unfold CTX_statics in CS. destruct CS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12).
    pose proof EX as EX0. destruct EX as (XI & XZ & XR & XM). unfold MUTEX, MUTEX_SIZE in *. unfold rblock_range in XR.
    destruct (cx_exlock x) as [[xp xa] xn] eqn:Hx. cbn [blk_addr blk_size fst snd] in *.
    pose proof (rw_cells_bound _ _ _ _ XM) as XB. cbn [cells_size csize Nat.add length] in XB.
    pose proof (rw_cells_bound _ _ _ _ AD) as ADB. cbn [cells_size csize Nat.add length] in ADB.
    unfold off_image, IMG_LO, IMG_HI in OFF.
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free in IM, GM.
    unfold_ctx_addrs.
    (* [comment removed for export] *)
    carve_frame 16%nat ST. do 3 st1. step. step. step. step. step. do 2 st1. step.
    release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 192%nat ST. do 14 st1. step. step. step. step. step. step.
    eapply evt_cut.
    { pose proof getglobal_ready_spec as Q; hnf in Q; eapply Q with (lo := lo) (x := x); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold GETGLOBAL_READY_STACK, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia); try (unfold CTX_statics; rewrite Hx; cbn [blk_addr fst snd]; ctx_statics_back). }
    land MU WM.
    unfold A_defctx_global, A_defctx in *.
    (* [comment removed for export] *)
    step. try if_false. step. step. step. step.
    eapply evt_cut.
    { pose proof getandlock_spec as Q; hnf in Q; eapply Q with (lo := lo) (x := x) (LB := LB) (rd := 1); clear Q; cbv zeta;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        try (unfold GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia).
      rewrite Hx. unfold EXLOCK. cbn [blk_addr blk_size fst snd]. split; [exact XI|]. split; [exact XZ|]. split; [unfold rblock_range, MUTEX_SIZE; lia| exact XM]. }
    intros ms_ PO_; rewrite Hx in PO_; cbn [blk_addr fst snd] in PO_; unfold mutex_foot in PO_; revert ms_ PO_.
    land MU WM.
    match goal with K : MUTEX _ _ _ |- _ => unfold MUTEX, MUTEX_HELD in K; rename K into XM end.
    (* [comment removed for export] *)
    unfold A_defctx_exmeth_bio in *.
    step. if_lit. step. ub_dead_by (clear - ADP). step. step. ubal_by ADAL. step. if_lit. step. st1. st1. step. try if_lit. st1. step.
    eapply evt_cut.
    { pose proof sk_num_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    (* [comment removed for export] *)
    step. step. try if_lit. step. step. step. try if_lit. st1. step.
    eapply evt_cut.
    { pose proof cunlock_spec as Q; hnf in Q; eapply Q with (lo := lo) (M := xa) (lk := 16); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        try (unfold MUTEX_SIZE, CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *; lia). }
    land MU WM.
    match goal with K : MUTEX _ _ _ |- _ => unfold MUTEX in K; rename K into XM end.
    (* [comment removed for export] *)
    step. try if_lit. step. try if_lit. step. step. step.
    if_cases K0; zify_cond K0; [kill K0|]; clear K0. step. step. step. step. step.
    eapply evt_cut.
    { pose proof cfree_null_evt_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        first [ unfold IMPL_mem, A_malloc_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; exact IM
              | unfold GOT_mem, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; exact GM ]. }
    land MU WM.
    (* [comment removed for export] *)
    step. step. do 13 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    - reflexivity.
    - unfold CTX_statics; rewrite Hx; cbn [blk_addr fst snd]; ctx_statics_back.
    - unfold EXLOCK. cbn [blk_addr blk_size fst snd]. split; [exact XI|]. split; [exact XZ|]. split; [unfold rblock_range, MUTEX_SIZE; lia| exact XM].
  Qed.

  Lemma cfreeex_spec : cfreeex_stmt.
  Proof.
    unfold cfreeex_stmt. intros until lo. cbv zeta. intros A0 A1 A2 TP ADP ADAL AD ADLO OFF CS EX SEP ST CEIL LO MI IM GM RAE. subst a0 a1 a2.
    unfold P_CRYPTO_free_ex_data, CFREEEX_STACK, FR_CRYPTO_free_ex_data, GETGLOBAL_READY_STACK, FR_ossl_lib_ctx_get_ex_data_global,
      GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, CUNLOCK_STACK,
      FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CRYPTO_EX_INDEX_BIO in *. hcb.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (ad, ad + 16) :: mutex_foot (blk_addr (cx_exlock x))) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold mutex_foot in MU.
    pose proof CS as CS0. unfold CTX_statics in CS. destruct CS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12).
    pose proof EX as EX0. destruct EX as (XI & XZ & XR & XM). unfold MUTEX, MUTEX_SIZE in *. unfold rblock_range in XR.
    destruct (cx_exlock x) as [[xp xa] xn] eqn:Hx. cbn [blk_addr blk_size fst snd] in *.
    pose proof (rw_cells_bound _ _ _ _ XM) as XB. cbn [cells_size csize Nat.add length] in XB.
    pose proof (rw_cells_bound _ _ _ _ AD) as ADB. cbn [cells_size csize Nat.add length] in ADB.
    unfold off_image, IMG_LO, IMG_HI in OFF.
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free in IM, GM.
    unfold_ctx_addrs.
    (* [comment removed for export] *)
    carve_frame 272%nat ST. do 14 st1. step. st1. step. ub_dead_by (clear - ADP). step. step. step. ubal_by ADAL. step. if_lit. st1. step.
    eapply evt_cut.
    { pose proof getglobal_ready_spec as Q; hnf in Q; eapply Q with (lo := lo) (x := x); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold GETGLOBAL_READY_STACK, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia); try (unfold CTX_statics; rewrite Hx; cbn [blk_addr fst snd]; ctx_statics_back). }
    land MU WM.
    unfold A_defctx_global, A_defctx in *.
    (* [comment removed for export] *)
    step. try if_false. step. step. step. step.
    eapply evt_cut.
    { pose proof getandlock_spec as Q; hnf in Q; eapply Q with (lo := lo) (x := x) (LB := LB) (rd := 1); clear Q; cbv zeta;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        try (unfold GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia).
      rewrite Hx. unfold EXLOCK. cbn [blk_addr blk_size fst snd]. split; [exact XI|]. split; [exact XZ|]. split; [unfold rblock_range, MUTEX_SIZE; lia| exact XM]. }
    intros ms_ PO_; rewrite Hx in PO_; cbn [blk_addr fst snd] in PO_; unfold mutex_foot in PO_; revert ms_ PO_.
    land MU WM.
    match goal with K : MUTEX _ _ _ |- _ => unfold MUTEX, MUTEX_HELD in K; rename K into XM end.
    (* [comment removed for export] *)
    unfold A_defctx_exmeth_bio in *.
    step. if_lit. step. step. step. try if_lit. st1. step.
    eapply evt_cut.
    { pose proof sk_num_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    (* [comment removed for export] *)
    step. step. try if_lit. step. step. step. try if_lit. st1. step.
    eapply evt_cut.
    { pose proof cunlock_spec as Q; hnf in Q; eapply Q with (lo := lo) (M := xa) (lk := 16); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        try (unfold MUTEX_SIZE, CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *; lia). }
    land MU WM.
    match goal with K : MUTEX _ _ _ |- _ => unfold MUTEX in K; rename K into XM end.
    (* [comment removed for export] *)
    step. try if_lit. step. step. if_cases K0; zify_cond K0; [kill K0|]; clear K0. step. step. step. step. step.
    eapply evt_cut.
    { pose proof cfree_null_evt_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        first [ unfold IMPL_mem, A_malloc_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; exact IM
              | unfold GOT_mem, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; exact GM ]. }
    land MU WM.
    (* [comment removed for export] *)
    st1. step.
    eapply evt_cut.
    { pose proof sk_free_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    land MU WM.
    (* [comment removed for export] *)
    st1. st1. do 13 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    - reflexivity.
    - unfold CTX_statics; rewrite Hx; cbn [blk_addr fst snd]; ctx_statics_back.
    - unfold EXLOCK. cbn [blk_addr blk_size fst snd]. split; [exact XI|]. split; [exact XZ|]. split; [unfold rblock_range, MUTEX_SIZE; lia| exact XM].
  Qed.
End S.
