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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_subtf3_csrc_T_u Cut_subtf3_csrc_R0_u.

Definition rt36 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 724148 (fun _ => []) (fun _ => Some (ELit 0)) (fun _ _ => []) (fun _ => None) false (Some (4, [])) 0 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t30 BL30 (CC.cp_nx t30) (nth 0 (map fst (CAD.po_leaves o30)) (SR.PS 0 [] [] [])).
Definition t36 : CC.cutpoint := Eval vm_compute in match rt36 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL36 : CAD.blocks := Eval vm_compute in match rt36 with Some cb => snd cb | None => [] end.
Definition hints36 : list (nat * CC.subst) := hints30.
Eval vm_compute in (5036, CC.cp_pc t36, CC.cp_nx t36, length (CC.cp_know t36)).
Definition o36 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t36 hints36 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1036, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4036, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt37 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 724196 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t34 BL34 (CC.cp_nx t34) (nth 0 (map fst (CAD.po_leaves o34)) (SR.PS 0 [] [] [])).
Definition t37 : CC.cutpoint := Eval vm_compute in match rt37 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL37 : CAD.blocks := Eval vm_compute in match rt37 with Some cb => snd cb | None => [] end.
Definition hints37 : list (nat * CC.subst) := hints34.
Eval vm_compute in (5037, CC.cp_pc t37, CC.cp_nx t37, length (CC.cp_know t37)).
Definition o37 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t37 hints37 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1037, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4037, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
