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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_fmodl_xsrc_T_u5 Cut_fmodl_xsrc_R0_u5.
(* [comment removed for export] *)
Definition rt10 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 748420 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t0 BL0 (CC.cp_nx t0) (nth 0 (map fst (CAD.po_leaves o0)) (SR.PS 0 [] [] [])).
Definition t10 : CC.cutpoint := Eval vm_compute in match rt10 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL10 : CAD.blocks := Eval vm_compute in match rt10 with Some cb => snd cb | None => [] end.
Definition hints10 : list (nat * CC.subst) := hints0.   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition rt11 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 746628 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t1 BL1 (CC.cp_nx t1) (nth 0 (map fst (CAD.po_leaves o1)) (SR.PS 0 [] [] [])).
Definition t11 : CC.cutpoint := Eval vm_compute in match rt11 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL11 : CAD.blocks := Eval vm_compute in match rt11 with Some cb => snd cb | None => [] end.
Definition hints11 : list (nat * CC.subst) := hints1.   (* [comment removed for export] *)
Eval vm_compute in (5011, CC.cp_pc t11, CC.cp_nx t11, length (CC.cp_know t11)).
Definition o11 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t11 hints11 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1011, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4011, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
(* [comment removed for export] *)
Definition rt12 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 748420 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t3 BL3 (CC.cp_nx t3) (nth 2 (map fst (CAD.po_leaves o3)) (SR.PS 0 [] [] [])).
Definition t12 : CC.cutpoint := Eval vm_compute in match rt12 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL12 : CAD.blocks := Eval vm_compute in match rt12 with Some cb => snd cb | None => [] end.
Definition hints12 : list (nat * CC.subst) := hints3.   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition rt13 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 748420 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t4 BL4 (CC.cp_nx t4) (nth 1 (map fst (CAD.po_leaves o4)) (SR.PS 0 [] [] [])).
Definition t13 : CC.cutpoint := Eval vm_compute in match rt13 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL13 : CAD.blocks := Eval vm_compute in match rt13 with Some cb => snd cb | None => [] end.
Definition hints13 : list (nat * CC.subst) := hints4.   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Definition rt14 := Eval vm_compute in CAD.ret_tmpl HDECL (CAD.cs_inline 766960 4 []) (APC.img_lo A0) (APC.img_hi A0) APART t7 BL7 (CC.cp_nx t7) (nth 1 (map fst (CAD.po_leaves o7)) (SR.PS 0 [] [] [])).
Definition t14 : CC.cutpoint := Eval vm_compute in match rt14 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL14 : CAD.blocks := Eval vm_compute in match rt14 with Some cb => snd cb | None => [] end.
Definition hints14 : list (nat * CC.subst) := hints7.   (* [comment removed for export] *)
Eval vm_compute in (5014, CC.cp_pc t14, CC.cp_nx t14, length (CC.cp_know t14)).
Definition o14 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t14 hints14 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1014, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4014, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
