(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface4 D_defs D_kit Sj_acps Sj_hkit RT_state RT_rep RT_facts RT_artfacts RT_cli TopA_iodefs RT_stackmalloc3w RT_stackmalloc1z Pj_rtkA Pj_defsA Pj_cpsA Pj_hdefsA Pj_os_defsA Pj_os_dtorA Pj_growA Pj_sfA Pj_tocharsA Pj_ser_defsA Pj_ser_objkA Pj_ser_okey1A Pj_ser_okey2A Pj_ser_closedA Imp_hdefsA Imp_ifaceA Imp_rtkA Imp_oss_defsA Imp_str_growA Imp_sb_overflowA Imp_xsputnA Imp_padA Imp_putA Imp_strA Imp_oss_dtorA Imp_oss_ctorA Imp_okarmA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.
Open Scope Z_scope.

Definition okA_af : art_facts RTA := rta_art_facts.
Definition okA_rc : rt_contracts RTA := imp_RC.
Definition okA_rc2 : rt_contracts2 RTA := imp_RC2.

Lemma rta_imp_rows : forall Σ m, ART RTA Σ m -> imp_rowsA m.
Proof.
  intros Σ m HA. pose proof (rta_cli_ro Σ m HA) as CR.
  unfold imp_rowsA, OSS_GOT_VT_A, OSS_VTT_A, OSS_SB_VPTR_A, OSS_SBB_VPTR_A, OSS_VBOFF_A, OSS_OS_VPTR_A, OSS_OS_CVPTR_A, OSS_IOS_CVPTR_A, OSS_IOS_VPTR_A,
         OSS_SBVT_A, OSS_XSPUTN_A, OSS_OVERFLOW_A, PJ_WIDEN_SLOT_A, PJ_DO_WIDEN_A, PJ_GOT_CTYPE_ID_A, PJ_CTYPE_ID_A.
  replace (0x17d740 - 16) with 0x17d730 by reflexivity. replace (0x17d500 - 16) with 0x17d4f0 by reflexivity.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); (apply (cli_ro_at m); [exact CR| cli_in]).
Qed.

Definition rta_growI : forall PMc, fdfs_only PMc -> mat_stable PMc -> grow_cpsA RTA PMc := grow_okA RTA okA_af okA_rc.
Definition rta_okey1I : forall PMc, fdfs_only PMc -> mat_stable PMc -> okey1_stmtA RTA PMc :=
  fun PMc FDO MST => okey1_okA RTA okA_af okA_rc PMc FDO MST (rta_growI PMc FDO MST).
Definition rta_okey2I : forall PMc, fdfs_only PMc -> mat_stable PMc -> okey2_stmtA RTA PMc :=
  fun PMc FDO MST => okey2_okA RTA okA_af okA_rc PMc FDO MST (rta_growI PMc FDO MST).
Definition rta_tocharsI : forall PMc, tochars_cpsA RTA PMc := tochars_okA RTA okA_af okA_rc rta_stack_malloc_1z.
Theorem rta_serI : forall PMc, ser_cpsA RTA PMc TAPE_MAX_DEPTH.
Proof.
  intros PMc. pose proof (fun FDO MST => ser_closedA RTA okA_af okA_rc okA_rc2 rta_stack_malloc_3w rta_stack_malloc_1z PMc FDO MST
                                          (rta_growI PMc FDO MST) (rta_tocharsI PMc) (rta_okey1I PMc FDO MST) (rta_okey2I PMc FDO MST) TAPE_MAX_DEPTH) as H.
  unfold ser_cpsA in *. intros; eapply H; eassumption.
Qed.

Theorem rta_push_back : forall PMc, push_backA_cps RTA PMc.
Proof. intros PMc. pose proof (push_backA_proof RTA okA_af okA_rc okA_rc2 PMc) as H. unfold push_backA_cps in *. intros; eapply H; eassumption. Qed.
Theorem rta_overflow : forall PMc, overflowA_cps RTA PMc.
Proof. intros PMc. pose proof (fun FDO MST => overflowA_proof RTA okA_af okA_rc okA_rc2 PMc FDO MST (rta_push_back PMc)) as H. unfold overflowA_cps in *. intros; eapply H; eassumption. Qed.
Theorem rta_xsputn : forall PMc, xsputnA_cps RTA PMc.
Proof. intros PMc. pose proof (fun FDO MST => xsputnA_proof RTA okA_af okA_rc okA_rc2 PMc FDO MST rta_imp_rows (rta_overflow PMc)) as H. unfold xsputnA_cps in *. intros; eapply H; eassumption. Qed.
Theorem rta_pad : forall PMc, padI_cps RTA PMc.
Proof. intros PMc. pose proof (fun FDO MST => pad_okI RTA okA_af okA_rc okA_rc2 PMc FDO MST rta_imp_rows (rta_xsputn PMc)) as H. unfold padI_cps in *. intros; eapply H; eassumption. Qed.
Theorem rta_put : forall PMc, putA_cps RTA PMc.
Proof. intros PMc. pose proof (fun FDO MST => put_okI RTA okA_af okA_rc okA_rc2 PMc FDO MST rta_imp_rows (rta_pad PMc)) as H. unfold putA_cps in *. intros; eapply H; eassumption. Qed.
Theorem rta_oss_ctor : forall PMc, oss_ctorA_cps RTA PMc.
Proof. intros PMc. pose proof (fun FDO MST => oss_ctorA_proof RTA okA_af okA_rc PMc FDO MST rta_imp_rows) as H. unfold oss_ctorA_cps in *. intros; eapply H; eassumption. Qed.
Theorem rta_str : forall PMc, strA_cps RTA PMc.
Proof. intros PMc. pose proof (strA_proof RTA okA_af okA_rc okA_rc2 PMc) as H. unfold strA_cps in *. intros; eapply H; eassumption. Qed.
Theorem rta_ios_dtor : forall PMc, ios_dtorA_cps RTA PMc.
Proof. intros PMc. pose proof (ios_dtorA_proof RTA okA_af okA_rc PMc) as H. unfold ios_dtorA_cps in *. intros; eapply H; eassumption. Qed.

Theorem rta_imp_okarm : forall PMc, imp_okarm_cpsA RTA PMc.
Proof.
  intros PMc. pose proof (fun FDO MST => imp_okarm_okA RTA okA_af okA_rc okA_rc2 PMc FDO MST rta_imp_rows (rta_oss_ctor PMc) (rta_serI PMc) (rta_put PMc)
                                          (rta_str PMc) locdtor_evtA_proof (rta_ios_dtor PMc)) as H.
  unfold imp_okarm_cpsA in *. intros; eapply H; eassumption.
Qed.
