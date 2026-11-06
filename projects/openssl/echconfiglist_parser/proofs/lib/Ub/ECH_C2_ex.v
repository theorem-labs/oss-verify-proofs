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
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C0_stmt ECH_C0_locks ECH_C2_stmt ECH_C2_small ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition GX_RA1 : Z := 0xe1578.  Definition GX_RA2 : Z := 0xe158c.  Definition IC_RA1 : Z := 0xf1430.  Definition IC_RA2 : Z := 0xf145c.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Lemma cgetlocalex_spec : cgetlocalex_stmt.
  Proof.
    unfold cgetlocalex_stmt. intros until c. intros exl lo A0 A1 TP CS ES EC CB ST CEIL LO MI RAE. subst a0 a1.
    unfold P_CRYPTO_THREAD_get_local_ex, CGETLOCALEX_STACK, FR_get_local_ex, FR_CRYPTO_THREAD_get_local_ex, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock,
      CRYPTO_THREAD_LOCAL_ERR_KEY, CRYPTO_THREAD_NO_CONTEXT in *. hcb.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof CS as CS0. pose proof ES as ES0. pose proof EC as EC0.
    unfold CTX_statics in CS. destruct CS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12).
    unfold ERR_statics in ES. destruct ES as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14).
    unfold ERR_chain, sa_cells in EC. destruct EC as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
    pose proof (Forall_inv RR) as R2. pose proof (Forall_inv (Forall_inv_tail RR)) as R3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RR))) as R4. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RR)))) as R5.
    clear RR. unfold rblock_range in R2, R3, R4, R5. unfold chain_below, ERRST_SIZE in CB.
    destruct (ec_mkey c) as [[p2 mk] n2] eqn:Hmk. destruct (ec_sa c) as [[p3 sa] n3] eqn:Hsa. destruct (ec_nodes c) as [[p4 nd] n4] eqn:Hnd. destruct (ec_es c) as [[p5 es] n5] eqn:Hes.
    cbn [blk_addr blk_size fst snd] in *. subst n2 n3 n4 n5.
    unfold wz, O_MKEY_ERR, A_master_once_ret, A_tsd_main, A_stopped, A_base_once, A_load_strings_once, A_optsdone, A_destructor_key, A_err_string_once, A_tevent_once, A_keys, A_next_key, A_key_lock, A_td_cancelbuf, A_td_tsd_used, A_base_inited, A_in_init_config_key, A_optsdone_lock,
      A_defctx_inited, A_defctx_exlock, A_defctx_exmeth_bio, A_td_tsd in *.
    (* [comment removed for export] *)
    change ([C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 3)]) with ([C4 (Z_to_bv 64 1)] ++ ([C4 (Z_to_bv 64 2)] ++ [C4 (Z_to_bv 64 3)])) in E1.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in E1. destruct E1 as [E1a E1]. apply (proj1 (rw_cells_app _ _ _ _ _)) in E1. destruct E1 as [E1b E1c].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in E1b, E1c.
    carve_frame 48%nat ST.
    do 7 st1.
    (* [comment removed for export] *)
    step. step. step. try if_true. step. step. step. step. step. step. step.
    eapply evt_cut.
    { eapply crunonce_spec with (lo := lo) (rest := []);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold CRUNONCE_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia); try reflexivity. }
    intros ms' PO. unfold c2_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & ST' & _).
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI ST. rename MI' into MI. rename ST' into ST.
    (* [comment removed for export] *)
    step. step. try if_false. step. try if_false. step. step.
    eapply evt_cut.
    { eapply cgetlocal_spec with (lo := lo) (rest := []) (k := 3);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try exact E2;
        try (unfold CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia); try reflexivity. }
    intros ms' PO. unfold c2_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'' & -> & MU'' & WM'' & MI'' & ST'' & _).
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU'', ST'' by lia. carry MU'' WM''. extend_munch MU WM MU'' WM''. clear MI ST. rename MI'' into MI. rename ST'' into ST.
   
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. step.
    step. ub_dead_by (clear - R2 HCEILB). step. ubal_by R2. step. if_lit.
    change (Z.shiftl 3 3) with 24. st1.
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. ub_dead_by (clear - R2 HCEILB).
    step. do 5 st1. step. step.
    (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    carve_frame 16%nat ST.
    do 4 st1.
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. ubal_by R3. step. if_lit.
    st1. step. try if_lit.
    st1. step. try if_true.
    st1. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). step. step. try if_lit.
    st1. step. if_cases K0; zify_cond K0; [kill K0|]; clear K0. step. try if_lit.
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. step. step. ubnot. step. ub_dead_by (clear - R4 HCEILB).
    step. step. ubal_by R4. step. if_lit. st1.
    do 4 step.
    release_frame FR ST (bv_unsigned sp). finish.
    all: unfold CTX_statics, ERR_statics, ERR_chain, sa_cells; rewrite ?Hmk, ?Hsa, ?Hnd, ?Hes;
         unfold wz, O_MKEY_ERR, ERRST_SIZE, A_master_once_ret, A_tsd_main, A_stopped, A_base_once, A_load_strings_once, A_optsdone, A_destructor_key, A_err_string_once, A_tevent_once, A_keys, A_next_key, A_key_lock, A_td_cancelbuf, A_td_tsd_used, A_base_inited, A_in_init_config_key, A_optsdone_lock,
           A_defctx_inited, A_defctx_exlock, A_defctx_exmeth_bio, A_td_tsd; cbn [blk_addr blk_size fst snd];
         repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
   
    change [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 3)] with ([C4 (Z_to_bv 64 1)] ++ ([C4 (Z_to_bv 64 2)] ++ [C4 (Z_to_bv 64 3)])).
    apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact E1a|]. apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact E1b| exact E1c].
    destruct EC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RR'). exact RR'.
  Qed.


  Lemma cinitcrypto_spec : cinitcrypto_stmt.
  Proof.
    unfold cinitcrypto_stmt. intros until c. intros lo A0 A1 ES ST CEIL LO MI RAE. subst a0 a1.
    unfold P_OPENSSL_init_crypto, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, OPENSSL_INIT_BASE_ONLY in *. hcb.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold ERR_statics in ES. destruct ES as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14).
    unfold wz, A_master_once_ret, A_tsd_main, A_stopped, A_base_once, A_load_strings_once, A_optsdone, A_destructor_key, A_err_string_once, A_tevent_once, A_keys, A_next_key, A_key_lock, A_td_cancelbuf, A_td_tsd_used, A_base_inited, A_in_init_config_key, A_optsdone_lock in *.
    carve_frame 80%nat ST.
    do 10 st1.
    st1. st1. st1.
    (* [comment removed for export] *)
    st1. unfold wz. step. step. try if_false.
    (* [comment removed for export] *)
    step. step. step. step. step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 4 st1. st1. step. step. st1.
    st1. st1. step. step. release_frame FR0 ST (bv_unsigned sp + -80).
    (* [comment removed for export] *)
    step. step. try if_false. st1. step. step. try if_true.
    (* [comment removed for export] *)
    step. step. step. step.
    eapply evt_cut.
    { eapply crunonce_spec with (lo := lo) (rest := [C4 (Z_to_bv 64 1)]);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try (unfold CRUNONCE_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia); try reflexivity. }
    intros ms' PO. unfold c2_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & ST' & _).
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI. rename MI' into MI.
    (* [comment removed for export] *)
    step. step. try if_false. st1. step. try if_false. step. step. step.
    match goal with |- context [bv_lts ?x ?y] => replace (bv_lts x y) with true by (vm_compute; reflexivity) end. cbv iota.
    clear ST.
    (* [comment removed for export] *)
    step. do 8 st1. step. step.
    release_frame FR ST' (bv_unsigned sp). finish.
    unfold ERR_statics. unfold wz, A_master_once_ret, A_tsd_main, A_stopped, A_base_once, A_load_strings_once, A_optsdone, A_destructor_key, A_err_string_once, A_tevent_once, A_keys, A_next_key, A_key_lock, A_td_cancelbuf, A_td_tsd_used, A_base_inited, A_in_init_config_key, A_optsdone_lock.
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  Theorem C2_spec : C2_stmts.
  Proof.
    exact (conj cread_lock_spec (conj cwrite_lock_spec (conj cunlock_spec (conj crunonce_spec
          (conj cgetlocal_spec (conj cgetlocalex_spec cinitcrypto_spec)))))).
  Qed.
End S.
