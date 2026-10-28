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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_fmodl_csrc_T_u Cut_fmodl_csrc_R0_u Cut_fmodl_csrc_R1_u Cut_fmodl_csrc_R2_u Cut_fmodl_csrc_R3_u Cut_fmodl_csrc_R4_u Cut_fmodl_csrc_R5_u Cut_fmodl_csrc_R6_u.

Definition rt29 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 720080 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t26 BL26 (CC.cp_nx t26) (nth 0 (map fst (CAD.po_leaves o26)) (SR.PS 0 [] [] [])).
Definition t29 : CC.cutpoint := Eval vm_compute in match rt29 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL29 : CAD.blocks := Eval vm_compute in match rt29 with Some cb => snd cb | None => [] end.
Definition hints29 : list (nat * CC.subst) := hints26.
Eval vm_compute in (5029, CC.cp_pc t29, CC.cp_nx t29, length (CC.cp_know t29)).
Definition o29 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t29 hints29 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1029, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4029, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt30 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 720080 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t27 BL27 (CC.cp_nx t27) (nth 0 (map fst (CAD.po_leaves o27)) (SR.PS 0 [] [] [])).
Definition t30 : CC.cutpoint := Eval vm_compute in match rt30 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL30 : CAD.blocks := Eval vm_compute in match rt30 with Some cb => snd cb | None => [] end.
Definition hints30 : list (nat * CC.subst) := hints27.
Eval vm_compute in (5030, CC.cp_pc t30, CC.cp_nx t30, length (CC.cp_know t30)).
Definition o30 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t30 hints30 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1030, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4030, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt31 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 720080 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t28 BL28 (CC.cp_nx t28) (nth 0 (map fst (CAD.po_leaves o28)) (SR.PS 0 [] [] [])).
Definition t31 : CC.cutpoint := Eval vm_compute in match rt31 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL31 : CAD.blocks := Eval vm_compute in match rt31 with Some cb => snd cb | None => [] end.
Definition hints31 : list (nat * CC.subst) := hints28.
Eval vm_compute in (5031, CC.cp_pc t31, CC.cp_nx t31, length (CC.cp_know t31)).
Definition o31 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t31 hints31 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1031, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4031, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
