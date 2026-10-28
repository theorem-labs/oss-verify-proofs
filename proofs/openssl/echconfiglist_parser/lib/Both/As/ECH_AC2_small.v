(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AKit ECH_AsKit
  ECH_AStmt_C0 ECH_AC0_locks ECH_AStmt_C2.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition RL_RA : Z := 0x1f5a58.  Definition WL_RA : Z := 0x1f5a84.  Definition UL_RA : Z := 0x1f5ab0.  Definition RO_RA : Z := 0x1f5b38.
Lemma sx32_lit : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. apply sx32_wz. exact Hx. Qed.

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.
Ltac sub_fp_tac := intros x Hx; unfold outside in *; cbn in *; first [tauto | lia].

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma cread_lock_spec : cread_lock_stmt.
  Proof.
    unfold cread_lock_stmt, crwlock_stmt_at.
    intros until M. intros lo A0 MX AL MLO ST LO MI RAE. subst a0.
    unfold P_CRYPTO_THREAD_read_lock, P_CRYPTO_THREAD_write_lock, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, MUTEX_SIZE in *.
    pose proof (rw_cells_bound _ _ _ _ MX) as MB. unfold MUTEX in MB. cbn [cells_size csize Nat.add length] in MB.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ((lo, bv_unsigned sp) :: mutex_foot M) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold mutex_foot in MU.
    unfold MUTEX in MX.
    carve_frame 16%nat ST.
    do 4 st1. step. step.
    eapply evt_cut. { eapply mutex_lock_spec; [reflexivity | exact MX | exact AL | exact MI]. }
    intros ms' PO. cbv beta in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & MX').
    ret_lit_any. unfold mutex_foot in MU'.
    assert (FR' : rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |]; cbn; clear - MLO LO SPR; lia).
    assert (ST' : stk asegs m' lo (bv_unsigned sp + -16))
      by (eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' |]; cbn; clear - MLO LO SPR LO0; lia).
    assert (MU2 : munch [(lo, bv_unsigned sp); (M + 4, M + 8)] m m')
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU']; sub_fp_tac).
    pose proof (wmono_trans _ _ _ _ WM WM') as WM2.
    clear MU WM FR ST MI MX. rename MI' into MI.
    unfold MUTEX, MUTEX_HELD, wz in MX'.
    do 5 step.
    release_frame FR' ST' (bv_unsigned sp). finish.
  Qed.
  Lemma cwrite_lock_spec : cwrite_lock_stmt.
  Proof.
    unfold cwrite_lock_stmt, crwlock_stmt_at.
    intros until M. intros lo A0 MX AL MLO ST LO MI RAE. subst a0.
    unfold P_CRYPTO_THREAD_read_lock, P_CRYPTO_THREAD_write_lock, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, MUTEX_SIZE in *.
    pose proof (rw_cells_bound _ _ _ _ MX) as MB. unfold MUTEX in MB. cbn [cells_size csize Nat.add length] in MB.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ((lo, bv_unsigned sp) :: mutex_foot M) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold mutex_foot in MU.
    unfold MUTEX in MX.
    carve_frame 16%nat ST.
    do 4 st1. step. step.
    eapply evt_cut. { eapply mutex_lock_spec; [reflexivity | exact MX | exact AL | exact MI]. }
    intros ms' PO. cbv beta in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & MX').
    ret_lit_any. unfold mutex_foot in MU'.
    assert (FR' : rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |]; cbn; clear - MLO LO SPR; lia).
    assert (ST' : stk asegs m' lo (bv_unsigned sp + -16))
      by (eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' |]; cbn; clear - MLO LO SPR LO0; lia).
    assert (MU2 : munch [(lo, bv_unsigned sp); (M + 4, M + 8)] m m')
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU']; sub_fp_tac).
    pose proof (wmono_trans _ _ _ _ WM WM') as WM2.
    clear MU WM FR ST MI MX. rename MI' into MI.
    unfold MUTEX, MUTEX_HELD, wz in MX'.
    do 5 step.
    release_frame FR' ST' (bv_unsigned sp). finish.
  Qed.

  Lemma cunlock_spec : cunlock_stmt.
  Proof.
    unfold cunlock_stmt. intros until lk. intros lo A0 MX LK AL MLO ST LO MI TP RAE. subst a0.
    unfold P_CRYPTO_THREAD_unlock, CUNLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_mutex_unlock, FR_pthread_mutex_unlock, MUTEX_SIZE in *.
    pose proof (rw_cells_bound _ _ _ _ MX) as MB. unfold MUTEX in MB. cbn [cells_size csize Nat.add length] in MB.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ((lo, bv_unsigned sp) :: mutex_foot M) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold mutex_foot in MU.
    unfold MUTEX in MX.
    carve_frame 16%nat ST.
    do 4 st1. step. step.
    eapply evt_cut.
    { eapply mutex_unlock_spec with (lo := lo); try eassumption; try reflexivity.
      all: try (rewrite unsigned_lit by lia); try eassumption; try (unfold MUTEX_SIZE, FR_mutex_unlock, FR_pthread_mutex_unlock; lia). }
    intros ms' PO. cbv beta in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & ST' & MX').
    ret_lit 0x1f5ab0. unfold mutex_foot in MU'. rewrite unsigned_lit in MU', ST' by lia.
    assert (FR' : rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |]; cbn; clear - MLO LO SPR; lia).
    assert (MU2 : munch [(lo, bv_unsigned sp); (M + 4, M + 8)] m m')
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU']; sub_fp_tac).
    pose proof (wmono_trans _ _ _ _ WM WM') as WM2.
    clear MU WM FR ST MI MX. rename MI' into MI.
    unfold MUTEX, wz in MX'.
    do 5 step.
    release_frame FR' ST' (bv_unsigned sp). finish.
  Qed.

  Lemma crunonce_spec : crunonce_stmt.
  Proof.
    unfold crunonce_stmt. intros until lo. intros rest A0 CX CLO ST LO MI RAE. subst a0.
    unfold P_CRYPTO_THREAD_run_once, CRUNONCE_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *.
    pose proof (rw_cells_bound _ _ _ _ CX) as CB0.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    change (C4 (wz 2) :: rest) with ([C4 (wz 2)] ++ rest) in CX. apply (proj1 (rw_cells_app _ _ _ _ _)) in CX. destruct CX as [CX _].
    unfold wz in CX.
    carve_frame 16%nat ST.
    do 4 st1. step. step.
    eapply evt_cut.
    { eapply once_spec with (rest := []); [reflexivity | exact CX | exact MI]. }
    intros ms' PO. cbv beta in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
    ret_lit 0x1f5b38.
    do 5 step.
    release_frame FR ST (bv_unsigned sp). finish. exact I.
  Qed.

  Lemma cgetlocal_spec : cgetlocal_stmt.
  Proof.
    unfold cgetlocal_stmt. intros until lo. intros rest A0 KX KR KLO ACC0 NSK K4 KNZ AC TP TD TS ST CEIL LO MI RAE. subst a0.
    assert (K8 : K mod 8 + 4 <= 8) by (clear - K4; Z.div_mod_to_equations; lia).
    unfold P_CRYPTO_THREAD_get_local, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]).
    change (C4 (wz k) :: rest) with ([C4 (wz k)] ++ rest) in KX. apply (proj1 (rw_cells_app _ _ _ _ _)) in KX. destruct KX as [KX _].
    unfold wz, A_td_tsd, A_tsd_main in *.
    pose proof (rw_cells_bound _ _ _ _ KX) as KB. pose proof (rw_cells_bound _ _ _ _ TS) as TB. cbn [cells_size csize Nat.add length] in KB, TB.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m K 4)) in ACC'.
    carve_frame 16%nat ST.
    do 4 st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx K 4) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW]) end.
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0. step. ubal_by K4. step. if_lit.
    (* [comment removed for export] *)
    step. step. step. zstep. zstep. ck4_load ACC K sv V1 V2 HK. clear ACC.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mx _) =>
    assert (FIN : forall a2x : word,
      evt asegs P
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp s1
                 (Z_to_bv 64 K) (Z_to_bv 64 sv) a2x a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f5bb0) fc None mx (seg_rom asegs))) end.
    { intros a2x. st1. rewrite ?sx32_lit by lia.
      do 3 step. step. step.
      release_frame FR ST (bv_unsigned sp).
      eapply evt_cut. { eapply tssget_spec; [reflexivity | exact KR | exact TP | exact TD | exact TS | exact MI]. }
      intros ms' PO. cbv beta in PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
      finish. exact I. }
    ck4_branch_blt K sv V1 V2 HK FIN.
  Qed.
End S.
