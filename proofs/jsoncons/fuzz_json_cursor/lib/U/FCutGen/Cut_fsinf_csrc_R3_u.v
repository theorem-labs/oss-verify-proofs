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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_fsinf_csrc_T_u Cut_fsinf_csrc_R0_u Cut_fsinf_csrc_R1_u Cut_fsinf_csrc_R2_u.

Definition rt12 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 733816 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t8 BL8 (CC.cp_nx t8) (nth 0 (map fst (CAD.po_leaves o8)) (SR.PS 0 [] [] [])).
Definition t12 : CC.cutpoint := Eval vm_compute in match rt12 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL12 : CAD.blocks := Eval vm_compute in match rt12 with Some cb => snd cb | None => [] end.
Definition hints12 : list (nat * CC.subst) := hints8.
Eval vm_compute in (5012, CC.cp_pc t12, CC.cp_nx t12, length (CC.cp_know t12)).
Definition o12 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t12 hints12 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1012, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4012, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt13 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 733816 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t9 BL9 (CC.cp_nx t9) (nth 0 (map fst (CAD.po_leaves o9)) (SR.PS 0 [] [] [])).
Definition t13 : CC.cutpoint := Eval vm_compute in match rt13 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL13 : CAD.blocks := Eval vm_compute in match rt13 with Some cb => snd cb | None => [] end.
Definition hints13 : list (nat * CC.subst) := hints9.
Eval vm_compute in (5013, CC.cp_pc t13, CC.cp_nx t13, length (CC.cp_know t13)).
Definition o13 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t13 hints13 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1013, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4013, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
