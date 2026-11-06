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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutGen Require Import Cut_fsinf_csrc_T Cut_fsinf_csrc_R0 Cut_fsinf_csrc_R1 Cut_fsinf_csrc_R2.

Definition rt12 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 726052 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t8 BL8 (CC.cp_nx t8) (nth 0 (map fst (CAD.po_leaves o8)) (SR.PS 0 [] [] [])).
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

Definition rt13 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 726052 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t9 BL9 (CC.cp_nx t9) (nth 0 (map fst (CAD.po_leaves o9)) (SR.PS 0 [] [] [])).
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
