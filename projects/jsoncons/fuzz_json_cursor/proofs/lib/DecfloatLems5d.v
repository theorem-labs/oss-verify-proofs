(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit DecLemTac DecRingLems.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm10CutKitD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutGen Require Import Cut_decfloat5_csrc.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma lems_ok_d : Forall (fun pl => CXD.lemma_ok RSEGS (fst pl) (snd pl)) (firstn 55%nat (skipn 45%nat LEMS)).
Proof.
  let l := eval vm_compute in (firstn 55%nat (skipn 45%nat LEMS)) in change (Forall (fun pl => CXD.lemma_ok RSEGS (fst pl) (snd pl)) l).
  repeat (apply Forall_cons; [cbn [fst snd]; DRL.ring_lem |]); apply Forall_nil.
Qed.
