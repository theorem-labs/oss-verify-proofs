(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm10CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import FmodlAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutGen Require Import Cut_fmodl_csrc_T Cut_fmodl_csrc_R0 Cut_fmodl_csrc_R1 Cut_fmodl_csrc_R2 Cut_fmodl_csrc_R3 Cut_fmodl_csrc_R4 Cut_fmodl_csrc_R5 Cut_fmodl_csrc_R6 Cut_fmodl_csrc_R7.

Definition rt32 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 732252 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t29 BL29 (CC.cp_nx t29) (nth 0 (map fst (CAD.po_leaves o29)) (SR.PS 0 [] [] [])).
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
