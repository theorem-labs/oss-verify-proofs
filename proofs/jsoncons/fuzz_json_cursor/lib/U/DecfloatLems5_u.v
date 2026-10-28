(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import DecLemTac DecRingLems. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import DecfloatLems5a_u DecfloatLems5b_u DecfloatLems5c_u DecfloatLems5d_u DecfloatLems5e_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutCert Require Import Pm10CutKitD_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_decfloat5_csrc_u.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma Forall_split : forall (A : Type) (P : A -> Prop) (n : nat) (l : list A), Forall P (firstn n l) -> Forall P (skipn n l) -> Forall P l.
Proof. intros A P n l H1 H2. rewrite <- (firstn_skipn n l). apply Forall_app. split; assumption. Qed.
Lemma lems_ok : LEMS_OK.
Proof.
  unfold LEMS_OK, CXD.LEMS_OK.
  apply (Forall_split _ _ 43%nat); [exact DecfloatLems5a_u.lems_ok_a|].
  apply (Forall_split _ _ 1%nat); [exact DecfloatLems5b_u.lems_ok_b|].
  apply (Forall_split _ _ 1%nat); [exact DecfloatLems5c_u.lems_ok_c|].
  apply (Forall_split _ _ 55%nat); [exact DecfloatLems5d_u.lems_ok_d|].
  exact DecfloatLems5e_u.lems_ok_e.
Qed.

Definition plans_ok := plans lems_ok.
