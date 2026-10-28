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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_fsinf_csrc_T_u Cut_fsinf_csrc_R0_u.

Definition rt4 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 733804 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t0 BL0 (CC.cp_nx t0) (nth 0 (map fst (CAD.po_leaves o0)) (SR.PS 0 [] [] [])).
Definition t4 : CC.cutpoint := Eval vm_compute in match rt4 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL4 : CAD.blocks := Eval vm_compute in match rt4 with Some cb => snd cb | None => [] end.
Definition hints4 : list (nat * CC.subst) := hints0.
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

Definition rt5 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 733804 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t1 BL1 (CC.cp_nx t1) (nth 0 (map fst (CAD.po_leaves o1)) (SR.PS 0 [] [] [])).
Definition t5 : CC.cutpoint := Eval vm_compute in match rt5 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL5 : CAD.blocks := Eval vm_compute in match rt5 with Some cb => snd cb | None => [] end.
Definition hints5 : list (nat * CC.subst) := hints1.
Eval vm_compute in (5005, CC.cp_pc t5, CC.cp_nx t5, length (CC.cp_know t5)).
Definition o5 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t5 hints5 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1005, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4005, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt6 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 733220 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t2 BL2 (CC.cp_nx t2) (nth 0 (map fst (CAD.po_leaves o2)) (SR.PS 0 [] [] [])).
Definition t6 : CC.cutpoint := Eval vm_compute in match rt6 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL6 : CAD.blocks := Eval vm_compute in match rt6 with Some cb => snd cb | None => [] end.
Definition hints6 : list (nat * CC.subst) := hints2.
Eval vm_compute in (5006, CC.cp_pc t6, CC.cp_nx t6, length (CC.cp_know t6)).
Definition o6 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t6 hints6 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1006, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4006, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.

Definition rt7 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 733220 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t3 BL3 (CC.cp_nx t3) (nth 0 (map fst (CAD.po_leaves o3)) (SR.PS 0 [] [] [])).
Definition t7 : CC.cutpoint := Eval vm_compute in match rt7 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL7 : CAD.blocks := Eval vm_compute in match rt7 with Some cb => snd cb | None => [] end.
Definition hints7 : list (nat * CC.subst) := hints3.
Eval vm_compute in (5007, CC.cp_pc t7, CC.cp_nx t7, length (CC.cp_know t7)).
Definition o7 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t7 hints7 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1007, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4007, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
