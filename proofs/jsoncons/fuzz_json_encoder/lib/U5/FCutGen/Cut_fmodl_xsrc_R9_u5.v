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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_fmodl_xsrc_T_u5 Cut_fmodl_xsrc_R0_u5 Cut_fmodl_xsrc_R1_u5 Cut_fmodl_xsrc_R2_u5 Cut_fmodl_xsrc_R3_u5 Cut_fmodl_xsrc_R4_u5 Cut_fmodl_xsrc_R5_u5 Cut_fmodl_xsrc_R6_u5 Cut_fmodl_xsrc_R7_u5 Cut_fmodl_xsrc_R8_u5.
(* [comment removed for export] *)
Definition rt33 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 765872 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t32 BL32 (CC.cp_nx t32) (nth 0 (map fst (CAD.po_leaves o32)) (SR.PS 0 [] [] [])).
Definition t33 : CC.cutpoint := Eval vm_compute in match rt33 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL33 : CAD.blocks := Eval vm_compute in match rt33 with Some cb => snd cb | None => [] end.
Definition hints33 : list (nat * CC.subst) := hints32.   (* [comment removed for export] *)
Eval vm_compute in (5033, CC.cp_pc t33, CC.cp_nx t33, length (CC.cp_know t33)).
Definition o33 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t33 hints33 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1033, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4033, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
