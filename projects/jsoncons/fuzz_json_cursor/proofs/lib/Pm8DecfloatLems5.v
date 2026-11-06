(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit DecLemTacM DecRingLemsM Pm8DecfloatLems5a Pm8DecfloatLems5b Pm8DecfloatLems5c Pm8DecfloatLems5d Pm8DecfloatLems5e.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm8CutKitD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_decfloat5_casan.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma Forall_split : forall (A : Type) (P : A -> Prop) (n : nat) (l : list A), Forall P (firstn n l) -> Forall P (skipn n l) -> Forall P l.
Proof. intros A P n l H1 H2. rewrite <- (firstn_skipn n l). apply Forall_app. split; assumption. Qed.
Lemma lems_ok : LEMS_OK.
Proof.
  unfold LEMS_OK, CXD.LEMS_OK.
  apply (Forall_split _ _ 43%nat); [exact Pm8DecfloatLems5a.lems_ok_a|].
  apply (Forall_split _ _ 1%nat); [exact Pm8DecfloatLems5b.lems_ok_b|].
  apply (Forall_split _ _ 1%nat); [exact Pm8DecfloatLems5c.lems_ok_c|].
  apply (Forall_split _ _ 55%nat); [exact Pm8DecfloatLems5d.lems_ok_d|].
  exact Pm8DecfloatLems5e.lems_ok_e.
Qed.

Definition plans_ok := plans lems_ok.
