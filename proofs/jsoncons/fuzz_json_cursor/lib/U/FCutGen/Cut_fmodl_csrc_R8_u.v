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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_fmodl_csrc_T_u Cut_fmodl_csrc_R0_u Cut_fmodl_csrc_R1_u Cut_fmodl_csrc_R2_u Cut_fmodl_csrc_R3_u Cut_fmodl_csrc_R4_u Cut_fmodl_csrc_R5_u Cut_fmodl_csrc_R6_u Cut_fmodl_csrc_R7_u.

Definition rt32 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 740016 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t29 BL29 (CC.cp_nx t29) (nth 0 (map fst (CAD.po_leaves o29)) (SR.PS 0 [] [] [])).
Definition t32 : CC.cutpoint := Eval vm_compute in match rt32 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL32 : CAD.blocks := Eval vm_compute in match rt32 with Some cb => snd cb | None => [] end.
Definition hints32 : list (nat * CC.subst) := hints29.
Eval vm_compute in (5032, CC.cp_pc t32, CC.cp_nx t32, length (CC.cp_know t32)).
Definition o32 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t32 hints32 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1032, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4032, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
