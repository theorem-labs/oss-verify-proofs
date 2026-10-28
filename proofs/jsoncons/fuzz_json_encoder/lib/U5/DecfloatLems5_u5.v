(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import DecLemTac DecRingLems. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecfloatLems5a_u5 DecfloatLems5b_u5 DecfloatLems5c_u5 DecfloatLems5d_u5 DecfloatLems5e_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_decfloat5_xsrc_u5.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma Forall_split : forall (A : Type) (P : A -> Prop) (n : nat) (l : list A), Forall P (firstn n l) -> Forall P (skipn n l) -> Forall P l.
Proof. intros A P n l H1 H2. rewrite <- (firstn_skipn n l). apply Forall_app. split; assumption. Qed.
Lemma lems_ok : LEMS_OK.
Proof.
  unfold LEMS_OK, CXD.LEMS_OK.
  apply (Forall_split _ _ 43%nat); [exact DecfloatLems5a_u5.lems_ok_a|].
  apply (Forall_split _ _ 1%nat); [exact DecfloatLems5b_u5.lems_ok_b|].
  apply (Forall_split _ _ 1%nat); [exact DecfloatLems5c_u5.lems_ok_c|].
  apply (Forall_split _ _ 55%nat); [exact DecfloatLems5d_u5.lems_ok_d|].
  exact DecfloatLems5e_u5.lems_ok_e.
Qed.
(* [comment removed for export] *)
Definition plans_ok := plans lems_ok.
