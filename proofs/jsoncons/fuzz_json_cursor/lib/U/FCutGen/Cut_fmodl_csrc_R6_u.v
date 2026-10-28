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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import FmodlAssume.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_fmodl_csrc_T_u Cut_fmodl_csrc_R0_u Cut_fmodl_csrc_R1_u Cut_fmodl_csrc_R2_u Cut_fmodl_csrc_R3_u Cut_fmodl_csrc_R4_u Cut_fmodl_csrc_R5_u.

Definition rt26 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 739324 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t23 BL23 (CC.cp_nx t23) (nth 0 (map fst (CAD.po_leaves o23)) (SR.PS 0 [] [] [])).
Definition t26 : CC.cutpoint := Eval vm_compute in match rt26 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL26 : CAD.blocks := Eval vm_compute in match rt26 with Some cb => snd cb | None => [] end.
Definition hints26 : list (nat * CC.subst) := hints23.
Eval vm_compute in (5026, CC.cp_pc t26, CC.cp_nx t26, length (CC.cp_know t26)).
Definition o26 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t26 hints26 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1026, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4026, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt27 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 739324 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t24 BL24 (CC.cp_nx t24) (nth 0 (map fst (CAD.po_leaves o24)) (SR.PS 0 [] [] [])).
Definition t27 : CC.cutpoint := Eval vm_compute in match rt27 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL27 : CAD.blocks := Eval vm_compute in match rt27 with Some cb => snd cb | None => [] end.
Definition hints27 : list (nat * CC.subst) := hints24.
Eval vm_compute in (5027, CC.cp_pc t27, CC.cp_nx t27, length (CC.cp_know t27)).
Definition o27 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t27 hints27 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1027, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4027, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt28 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 721872 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t25 BL25 (CC.cp_nx t25) (nth 0 (map fst (CAD.po_leaves o25)) (SR.PS 0 [] [] [])).
Definition t28 : CC.cutpoint := Eval vm_compute in match rt28 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL28 : CAD.blocks := Eval vm_compute in match rt28 with Some cb => snd cb | None => [] end.
Definition hints28 : list (nat * CC.subst) := hints25.
Eval vm_compute in (5028, CC.cp_pc t28, CC.cp_nx t28, length (CC.cp_know t28)).
Definition o28 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t28 hints28 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1028, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4028, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
