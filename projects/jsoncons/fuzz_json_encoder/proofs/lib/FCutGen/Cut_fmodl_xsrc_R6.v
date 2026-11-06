(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm6CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import FmodlAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutGen Require Import Cut_fmodl_xsrc_T Cut_fmodl_xsrc_R0 Cut_fmodl_xsrc_R1 Cut_fmodl_xsrc_R2 Cut_fmodl_xsrc_R3 Cut_fmodl_xsrc_R4 Cut_fmodl_xsrc_R5.
(* [comment removed for export] *)
Definition rt26 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 751044 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t23 BL23 (CC.cp_nx t23) (nth 0 (map fst (CAD.po_leaves o23)) (SR.PS 0 [] [] [])).
Definition t26 : CC.cutpoint := Eval vm_compute in match rt26 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL26 : CAD.blocks := Eval vm_compute in match rt26 with Some cb => snd cb | None => [] end.
Definition hints26 : list (nat * CC.subst) := hints23.   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition rt27 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 751044 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t24 BL24 (CC.cp_nx t24) (nth 0 (map fst (CAD.po_leaves o24)) (SR.PS 0 [] [] [])).
Definition t27 : CC.cutpoint := Eval vm_compute in match rt27 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL27 : CAD.blocks := Eval vm_compute in match rt27 with Some cb => snd cb | None => [] end.
Definition hints27 : list (nat * CC.subst) := hints24.   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition rt28 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 733592 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t25 BL25 (CC.cp_nx t25) (nth 0 (map fst (CAD.po_leaves o25)) (SR.PS 0 [] [] [])).
Definition t28 : CC.cutpoint := Eval vm_compute in match rt28 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL28 : CAD.blocks := Eval vm_compute in match rt28 with Some cb => snd cb | None => [] end.
Definition hints28 : list (nat * CC.subst) := hints25.   (* [comment removed for export] *)
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
