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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C0_stmt ECH_C0_locks ECH_C1_stmt ECH_C1_free ECH_C2_stmt ECH_C2_small ECH_C5_stmt ECH_C5_small ECH_C3_stmt ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition GD_RA1 : Z := 0xe7308.  Definition GD_RA2 : Z := 0xe732c. (* [comment removed for export] *)  Definition GD_RA3 : Z := 0xe7348.

Ltac unfold_ctx_addrs := unfold wz, A_defctx_global, A_defctx_inited, A_defctx_exlock, A_defctx_exmeth_bio, A_td_tsd, A_tsd_main, A_defctx,
  A_destructor_key, A_base_inited, A_stopped, A_in_init_config_key, A_base_once, A_optsdone_lock, A_keys in *.
(* [comment removed for export] *)
Ltac ctx_statics_back :=
  unfold CTX_statics; unfold wz, A_defctx_inited, A_defctx_exlock, A_defctx_exmeth_bio, A_td_tsd, A_tsd_main, A_defctx,
    A_destructor_key, A_base_inited, A_stopped, A_in_init_config_key, A_base_once, A_optsdone_lock, A_keys;
  repeat match goal with |- _ /\ _ => split end; try assumption; join_cells.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma getdefctx_ready_spec : getdefctx_ready_stmt.
  Proof.
    unfold getdefctx_ready_stmt. intros until lo. intros TP CS ST CEIL LO MI RAE.
    unfold P_get_default_context, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *. hcb.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof CS as CS0. unfold CTX_statics in CS. destruct CS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12).
    unfold_ctx_addrs.
    (* [comment removed for export] *)
    split_head D1 D1a. split_head D1 D1b. split_head D1 D1c. split_head D1 D1d. split_head D1 D1e. rename D1 into D1f.
    carve_frame 32%nat ST.
    do 5 st1. step. step. step. step. step. step.
    eapply evt_cut.
    { eapply crunonce_spec with (lo := lo) (rest := []); try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold CRUNONCE_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia); try reflexivity. }
    land MU WM.
    (* [comment removed for export] *)
    step. step. step. try if_false. st1. rewrite ?sx32_lit by lia. step. try if_false. step. step. step. step.
    eapply evt_cut.
    { eapply crunonce_spec with (lo := lo) (rest := []); try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold CRUNONCE_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia); try reflexivity. }
    land MU WM.
    (* [comment removed for export] *)
    step. step. step. try if_false. st1. rewrite ?sx32_lit by lia. step. try if_false. step. step.
    eapply evt_cut.
    { eapply cgetlocal_spec with (lo := lo) (rest := []) (k := 0); try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia); try reflexivity. }
    land MU WM.
    (* [comment removed for export] *)
    st1. unfold wz. step. step. step. try if_false. step.
    do 3 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish. reflexivity. ctx_statics_back.
  Qed.
  Lemma getglobal_ready_spec : getglobal_ready_stmt.
  Proof.
    unfold getglobal_ready_stmt. intros until lo. intros A0 TP CS ST CEIL LO MI RAE. subst a0.
    unfold P_ossl_lib_ctx_get_ex_data_global, GETGLOBAL_READY_STACK, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context,
      CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *. hcb.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof CS as CS0. unfold CTX_statics in CS. destruct CS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12).
    unfold_ctx_addrs.
    step. try if_false.
    carve_frame 16%nat ST. do 4 st1. step.
    eapply evt_cut.
    { eapply getdefctx_ready_spec with (lo := lo) (x := x); try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia); try ctx_statics_back. }
    land MU WM.
    (* [comment removed for export] *)
    do 3 step. step. try if_lit. step. step. try if_lit. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: try (unfold A_defctx_global, A_defctx; reflexivity).
  Qed.
  Lemma getandlock_spec : getandlock_stmt.
  Proof.
    unfold getandlock_stmt. intros until lo. cbv zeta. intros A0 A1 A2 RD CS EX ST CEIL LO MI RAE. subst a0 a1 a2.
    unfold P_get_and_lock, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CRYPTO_EX_INDEX_BIO in *. hcb.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ((lo, bv_unsigned sp) :: mutex_foot (blk_addr (cx_exlock x))) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold mutex_foot in MU.
    pose proof CS as CS0. unfold CTX_statics in CS. destruct CS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12).
    destruct EX as (XI & XZ & XR & XM). unfold MUTEX, MUTEX_SIZE in *. unfold rblock_range in XR.
    destruct (cx_exlock x) as [[xp xa] xn] eqn:Hx. cbn [blk_addr blk_size fst snd] in *.
    pose proof (rw_cells_bound _ _ _ _ XM) as XB. cbn [cells_size csize Nat.add length] in XB.
    unfold_ctx_addrs.
    carve_frame 32%nat ST. do 5 st1.
    (* [comment removed for export] *)
    step. step. step. step. try if_lit. step. step. step. try if_lit. st1.
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      step.
      eapply evt_cut.
      { eapply cwrite_lock_spec with (lo := lo); try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold MUTEX_SIZE, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *; lia). }
      land MU WM.
      (* [comment removed for export] *)
      step. if_lit. step. step. step. ubnot. step. try if_lit. step. step. do 4 st1. step. step.
      release_frame FR ST (bv_unsigned sp). finish.
      all: try (unfold A_defctx_exmeth_bio, A_defctx_global, A_defctx; reflexivity).
      all: first [ unfold CTX_statics; rewrite Hx; cbn [blk_addr fst snd]; ctx_statics_back
                 | unfold MUTEX, MUTEX_HELD, wz in *; assumption ].
    - (* [comment removed for export] *)
      step.
      eapply evt_cut.
      { eapply cread_lock_spec with (lo := lo); try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold MUTEX_SIZE, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *; lia). }
      land MU WM.
      (* [comment removed for export] *)
      step. if_lit. step. step. step. ubnot. step. try if_lit. step. step. do 4 st1. step. step.
      release_frame FR ST (bv_unsigned sp). finish.
      all: try (unfold A_defctx_exmeth_bio, A_defctx_global, A_defctx; reflexivity).
      all: first [ unfold CTX_statics; rewrite Hx; cbn [blk_addr fst snd]; ctx_statics_back
                 | unfold MUTEX, MUTEX_HELD, wz in *; assumption ].
  Qed.
End S.
