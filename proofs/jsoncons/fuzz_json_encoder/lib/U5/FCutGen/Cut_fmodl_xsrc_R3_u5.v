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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import FmodlAssume.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_fmodl_xsrc_T_u5 Cut_fmodl_xsrc_R0_u5 Cut_fmodl_xsrc_R1_u5 Cut_fmodl_xsrc_R2_u5.
(* [comment removed for export] *)
Definition rt20 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 745956 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t15 BL15 (CC.cp_nx t15) (nth 1 (map fst (CAD.po_leaves o15)) (SR.PS 0 [] [] [])).
Definition t20 : CC.cutpoint := Eval vm_compute in match rt20 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL20 : CAD.blocks := Eval vm_compute in match rt20 with Some cb => snd cb | None => [] end.
Definition hints20 : list (nat * CC.subst) := hints15.   (* [comment removed for export] *)
Eval vm_compute in (5020, CC.cp_pc t20, CC.cp_nx t20, length (CC.cp_know t20)).
Definition o20 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t20 hints20 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1020, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4020, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
(* [comment removed for export] *)
Definition rt21 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 746628 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t19 BL19 (CC.cp_nx t19) (nth 0 (map fst (CAD.po_leaves o19)) (SR.PS 0 [] [] [])).
Definition t21 : CC.cutpoint := Eval vm_compute in match rt21 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL21 : CAD.blocks := Eval vm_compute in match rt21 with Some cb => snd cb | None => [] end.
Definition hints21 : list (nat * CC.subst) := hints19.   (* [comment removed for export] *)
Eval vm_compute in (5021, CC.cp_pc t21, CC.cp_nx t21, length (CC.cp_know t21)).
Definition o21 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t21 hints21 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1021, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4021, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
