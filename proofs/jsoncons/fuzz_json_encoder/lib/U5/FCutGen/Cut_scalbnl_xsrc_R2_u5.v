(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_scalbnl_xsrc_T_u5 Cut_scalbnl_xsrc_R0_u5 Cut_scalbnl_xsrc_R1_u5.
(* [comment removed for export] *)
Definition rt8 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 746628 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t5 BL5 (CC.cp_nx t5) (nth 1 (map fst (CAD.po_leaves o5)) (SR.PS 0 [] [] [])).
Definition t8 : CC.cutpoint := Eval vm_compute in match rt8 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL8 : CAD.blocks := Eval vm_compute in match rt8 with Some cb => snd cb | None => [] end.
Definition hints8 : list (nat * CC.subst) := hints5.   (* [comment removed for export] *)
Eval vm_compute in (5008, CC.cp_pc t8, CC.cp_nx t8, length (CC.cp_know t8)).
Definition o8 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t8 hints8 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1008, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4008, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
(* [comment removed for export] *)
Definition rt9 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 746628 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t6 BL6 (CC.cp_nx t6) (nth 1 (map fst (CAD.po_leaves o6)) (SR.PS 0 [] [] [])).
Definition t9 : CC.cutpoint := Eval vm_compute in match rt9 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL9 : CAD.blocks := Eval vm_compute in match rt9 with Some cb => snd cb | None => [] end.
Definition hints9 : list (nat * CC.subst) := hints6.   (* [comment removed for export] *)
Eval vm_compute in (5009, CC.cp_pc t9, CC.cp_nx t9, length (CC.cp_know t9)).
Definition o9 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t9 hints9 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1009, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4009, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
(* [comment removed for export] *)
Definition rt10 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 746628 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t7 BL7 (CC.cp_nx t7) (nth 0 (map fst (CAD.po_leaves o7)) (SR.PS 0 [] [] [])).
Definition t10 : CC.cutpoint := Eval vm_compute in match rt10 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL10 : CAD.blocks := Eval vm_compute in match rt10 with Some cb => snd cb | None => [] end.
Definition hints10 : list (nat * CC.subst) := hints7.   (* [comment removed for export] *)
Eval vm_compute in (5010, CC.cp_pc t10, CC.cp_nx t10, length (CC.cp_know t10)).
Definition o10 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t10 hints10 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1010, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4010, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
