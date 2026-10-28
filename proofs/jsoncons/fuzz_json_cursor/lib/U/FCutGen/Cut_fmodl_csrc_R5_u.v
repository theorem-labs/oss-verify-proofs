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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_fmodl_csrc_T_u Cut_fmodl_csrc_R0_u Cut_fmodl_csrc_R1_u Cut_fmodl_csrc_R2_u Cut_fmodl_csrc_R3_u Cut_fmodl_csrc_R4_u.

Definition rt23 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 740168 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t22 BL22 (CC.cp_nx t22) (nth 0 (map fst (CAD.po_leaves o22)) (SR.PS 0 [] [] [])).
Definition t23 : CC.cutpoint := Eval vm_compute in match rt23 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL23 : CAD.blocks := Eval vm_compute in match rt23 with Some cb => snd cb | None => [] end.
Definition hints23 : list (nat * CC.subst) := hints22.
Eval vm_compute in (5023, CC.cp_pc t23, CC.cp_nx t23, length (CC.cp_know t23)).
Definition o23 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t23 hints23 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1023, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4023, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt24 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 740016 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t22 BL22 (CC.cp_nx t22) (nth 1 (map fst (CAD.po_leaves o22)) (SR.PS 0 [] [] [])).
Definition t24 : CC.cutpoint := Eval vm_compute in match rt24 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL24 : CAD.blocks := Eval vm_compute in match rt24 with Some cb => snd cb | None => [] end.
Definition hints24 : list (nat * CC.subst) := hints22.
Eval vm_compute in (5024, CC.cp_pc t24, CC.cp_nx t24, length (CC.cp_know t24)).
Definition o24 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t24 hints24 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1024, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4024, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt25 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 719692 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t22 BL22 (CC.cp_nx t22) (nth 3 (map fst (CAD.po_leaves o22)) (SR.PS 0 [] [] [])).
Definition t25 : CC.cutpoint := Eval vm_compute in match rt25 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL25 : CAD.blocks := Eval vm_compute in match rt25 with Some cb => snd cb | None => [] end.
Definition hints25 : list (nat * CC.subst) := hints22.
Eval vm_compute in (5025, CC.cp_pc t25, CC.cp_nx t25, length (CC.cp_know t25)).
Definition o25 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t25 hints25 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1025, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4025, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
