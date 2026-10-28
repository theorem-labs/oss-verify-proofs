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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_scalbn_csrc_T_u Cut_scalbn_csrc_R0_u.

Definition rt2 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 700868 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t0 BL0 (CC.cp_nx t0) (nth 1 (map fst (CAD.po_leaves o0)) (SR.PS 0 [] [] [])).
Definition t2 : CC.cutpoint := Eval vm_compute in match rt2 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL2 : CAD.blocks := Eval vm_compute in match rt2 with Some cb => snd cb | None => [] end.
Definition hints2 : list (nat * CC.subst) := hints0.
Eval vm_compute in (5002, CC.cp_pc t2, CC.cp_nx t2, length (CC.cp_know t2)).
Definition o2 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t2 hints2 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1002, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4002, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt3 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 700812 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t0 BL0 (CC.cp_nx t0) (nth 2 (map fst (CAD.po_leaves o0)) (SR.PS 0 [] [] [])).
Definition t3 : CC.cutpoint := Eval vm_compute in match rt3 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL3 : CAD.blocks := Eval vm_compute in match rt3 with Some cb => snd cb | None => [] end.
Definition hints3 : list (nat * CC.subst) := hints0.
Eval vm_compute in (5003, CC.cp_pc t3, CC.cp_nx t3, length (CC.cp_know t3)).
Definition o3 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t3 hints3 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1003, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4003, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt4 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 700932 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t1 BL1 (CC.cp_nx t1) (nth 0 (map fst (CAD.po_leaves o1)) (SR.PS 0 [] [] [])).
Definition t4 : CC.cutpoint := Eval vm_compute in match rt4 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL4 : CAD.blocks := Eval vm_compute in match rt4 with Some cb => snd cb | None => [] end.
Definition hints4 : list (nat * CC.subst) := hints1.
Eval vm_compute in (5004, CC.cp_pc t4, CC.cp_nx t4, length (CC.cp_know t4)).
Definition o4 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t4 hints4 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1004, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4004, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
