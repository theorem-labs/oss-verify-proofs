(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsAtomics ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AKit ECH_AStmt_C0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma sx32_lit : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. apply sx32_wz. exact Hx. Qed.

Section S.
  Context {HCEIL : HeapCeil}.

  Lemma mutex_lock_spec : mutex_lock_stmt.
  Proof.
    unfold mutex_lock_stmt. intros until M. intros A0 MX AL MI. subst a0. unfold P_pthread_mutex_lock. unfold MUTEX, MUTEX_HELD, wz in *.
    pose proof (rw_cells_bound _ _ _ _ MX) as MB. cbn [cells_size csize Nat.add length] in MB.
    pose proof (munch_refl (mutex_foot M) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold mutex_foot in MU.
    (* [comment removed for export] *)
    st1. st1. unfold wz. change (Z.land 0 15) with 0. step. if_false.
    (* [comment removed for export] *)
    step. step.
    astep. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    (* [comment removed for export] *)
    step. if_false.
    astep.
    step. if_false. step. step. try if_true. step. step.
    finish.
  Qed.

  Lemma mutex_unlock_spec : mutex_unlock_stmt.
  Proof.
    unfold mutex_unlock_stmt. intros until lk. intros lo A0 MX LK AL MLO ST LO MI TP. subst a0.
    unfold P_pthread_mutex_unlock, FR_mutex_unlock, FR_pthread_mutex_unlock in *. unfold MUTEX, MUTEX_SIZE, wz in *.
    pose proof (rw_cells_bound _ _ _ _ MX) as MB. cbn [cells_size csize Nat.add length] in MB.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ((lo, bv_unsigned sp) :: mutex_foot M) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold mutex_foot in MU.
    carve_frame 96%nat ST.
    (* [comment removed for export] *)
    do 12 st1.
    (* [comment removed for export] *)
    st1. st1. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    st1. st1. change (Z.land 0 15) with 0. change (Z.land 0 128) with 0.
    st1. step. try if_true.
    (* [comment removed for export] *)
    step. step.
    (* [comment removed for export] *)
    st1. rewrite ?sx32_lit by lia.
    astep. rewrite ?sx32_lit by lia.
    step. try if_false.
    astep.
    step. try if_false.
    step. rewrite ?sx32_lit by lia.
    replace (bv_swrap 32 (bv_unsigned (Z_to_bv 64 lk) + 0)) with lk
      by (rewrite unsigned_lit by lia; rewrite Z.add_0_r, swrap32_small by lia; reflexivity).
    step. try if_false.
    (* [comment removed for export] *)
    step. change (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    step. replace (v_slti (Z_to_bv 64 lk) 0) with (Z_to_bv 64 0)
      by (unfold v_slti, zsig; rewrite signed_lit by lia; destruct (Z.ltb_spec lk 0); [lia| reflexivity]).
    step.
    step. try if_true. step. try if_true.
    (* [comment removed for export] *)
    step. do 11 step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  Lemma once_spec : once_stmt.
  Proof.
    unfold once_stmt. intros until C. intros rest A0 CX MI. subst a0. unfold P_pthread_once. unfold wz in *.
    step. change (sx32 (Z_to_bv 64 2)) with (Z_to_bv 64 2). step. step. try if_false. step. step. step.
    finish.
  Qed.

  Lemma tssget_spec : tssget_stmt.
  Proof.
    unfold tssget_stmt. intros until v. intros A0 K TP TD TS MI. subst a0 tp. unfold P_pthread_getspecific. unfold wz, A_td_tsd, A_tsd_main in *.
    unfold ATP. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.shiftr ?e 29)] => replace (Z.shiftr e 29) with (8 * k) end.
    2:{ rewrite (unsigned_lit k) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. lia. }
    step. set (Q := 12595256 + 8 * k) in *. step. subst Q. step. finish.
  Qed.

  Lemma errnoloc_spec : errnoloc_stmt.
  Proof.
    unfold errnoloc_stmt. intros until m. intros TP MI. subst tp. unfold P_errno_location.
    unfold ATP. step. step. step. finish.
  Qed.

  Theorem AC0_spec : C0_stmts.
  Proof. exact (conj mutex_lock_spec (conj mutex_unlock_spec (conj once_spec (conj tssget_spec errnoloc_spec)))). Qed.
End S.
