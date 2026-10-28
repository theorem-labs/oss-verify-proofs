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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_fsinf_csrc_T_u Cut_fsinf_csrc_R0_u Cut_fsinf_csrc_R1_u Cut_fsinf_csrc_R2_u Cut_fsinf_csrc_R3_u.

Definition rt14 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 739324 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t12 BL12 (CC.cp_nx t12) (nth 0 (map fst (CAD.po_leaves o12)) (SR.PS 0 [] [] [])).
Definition t14 : CC.cutpoint := Eval vm_compute in match rt14 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL14 : CAD.blocks := Eval vm_compute in match rt14 with Some cb => snd cb | None => [] end.
Definition hints14 : list (nat * CC.subst) := hints12.
Eval vm_compute in (5014, CC.cp_pc t14, CC.cp_nx t14, length (CC.cp_know t14)).
Definition o14 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t14 hints14 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1014, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4014, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt15 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 739324 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t13 BL13 (CC.cp_nx t13) (nth 0 (map fst (CAD.po_leaves o13)) (SR.PS 0 [] [] [])).
Definition t15 : CC.cutpoint := Eval vm_compute in match rt15 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL15 : CAD.blocks := Eval vm_compute in match rt15 with Some cb => snd cb | None => [] end.
Definition hints15 : list (nat * CC.subst) := hints13.
Eval vm_compute in (5015, CC.cp_pc t15, CC.cp_nx t15, length (CC.cp_know t15)).
Definition o15 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t15 hints15 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1015, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4015, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
