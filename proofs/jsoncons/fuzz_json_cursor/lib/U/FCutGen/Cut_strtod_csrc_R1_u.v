(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutCert Require Import Pm10CutKitD_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import StrtodAssume.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_strtod_csrc_T_u Cut_strtod_csrc_R0_u.

Definition rt1 := Eval vm_compute in (SAS.ret_fs 8672 878428 (APC.eadd (EVar 10) (EVar 33))) t0 BL0 (CC.cp_nx t0) (nth 0 (map fst (CAD.po_leaves o0)) (SR.PS 0 [] [] [])).
Definition t1 : CC.cutpoint := Eval vm_compute in match rt1 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL1 : CAD.blocks := Eval vm_compute in match rt1 with Some cb => snd cb | None => [] end.
Definition hints1 : list (nat * CC.subst) := hints0.
Eval vm_compute in (5001, CC.cp_pc t1, CC.cp_nx t1, length (CC.cp_know t1)).
Definition o1 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t1 hints1 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1001, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4001, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
