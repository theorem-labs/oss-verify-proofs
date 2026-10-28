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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_fmodl_xsrc_T_u5 Cut_fmodl_xsrc_R0_u5 Cut_fmodl_xsrc_R1_u5.
(* [comment removed for export] *)
Definition rt15 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 746240 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t10 BL10 (CC.cp_nx t10) (nth 0 (map fst (CAD.po_leaves o10)) (SR.PS 0 [] [] [])).
Definition t15 : CC.cutpoint := Eval vm_compute in match rt15 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL15 : CAD.blocks := Eval vm_compute in match rt15 with Some cb => snd cb | None => [] end.
Definition hints15 : list (nat * CC.subst) := hints10.   (* [comment removed for export] *)
Eval vm_compute in (5015, CC.cp_pc t15, CC.cp_nx t15, length (CC.cp_know t15)).
Definition o15 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t15 hints15 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1015, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4015, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
(* [comment removed for export] *)
Definition rt16 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 751308 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 112 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t11 BL11 (CC.cp_nx t11) (nth 0 (map fst (CAD.po_leaves o11)) (SR.PS 0 [] [] [])).
Definition t16 : CC.cutpoint := Eval vm_compute in match rt16 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL16 : CAD.blocks := Eval vm_compute in match rt16 with Some cb => snd cb | None => [] end.
Definition hints16 : list (nat * CC.subst) := hints11.   (* [comment removed for export] *)
Eval vm_compute in (5016, CC.cp_pc t16, CC.cp_nx t16, length (CC.cp_know t16)).
Definition o16 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t16 hints16 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1016, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4016, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
(* [comment removed for export] *)
Definition rt17 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 746628 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t12 BL12 (CC.cp_nx t12) (nth 0 (map fst (CAD.po_leaves o12)) (SR.PS 0 [] [] [])).
Definition t17 : CC.cutpoint := Eval vm_compute in match rt17 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL17 : CAD.blocks := Eval vm_compute in match rt17 with Some cb => snd cb | None => [] end.
Definition hints17 : list (nat * CC.subst) := hints12.   (* [comment removed for export] *)
Eval vm_compute in (5017, CC.cp_pc t17, CC.cp_nx t17, length (CC.cp_know t17)).
Definition o17 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t17 hints17 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1017, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4017, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
(* [comment removed for export] *)
Definition rt18 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 746628 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 80 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t13 BL13 (CC.cp_nx t13) (nth 0 (map fst (CAD.po_leaves o13)) (SR.PS 0 [] [] [])).
Definition t18 : CC.cutpoint := Eval vm_compute in match rt18 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL18 : CAD.blocks := Eval vm_compute in match rt18 with Some cb => snd cb | None => [] end.
Definition hints18 : list (nat * CC.subst) := hints13.   (* [comment removed for export] *)
Eval vm_compute in (5018, CC.cp_pc t18, CC.cp_nx t18, length (CC.cp_know t18)).
Definition o18 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t18 hints18 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1018, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4018, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
(* [comment removed for export] *)
Definition rt19 := Eval vm_compute in CAD.ret_tmpl HDECL ((CAD.CSUM 765872 (fun _ => []) (fun _ => None) (fun _ _ => []) (fun _ => None) false None 16 false false)) (APC.img_lo A0) (APC.img_hi A0) APART t14 BL14 (CC.cp_nx t14) (nth 0 (map fst (CAD.po_leaves o14)) (SR.PS 0 [] [] [])).
Definition t19 : CC.cutpoint := Eval vm_compute in match rt19 with Some cb => fst cb | None => CAD.dummy_cp end.
Definition BL19 : CAD.blocks := Eval vm_compute in match rt19 with Some cb => snd cb | None => [] end.
Definition hints19 : list (nat * CC.subst) := hints14.   (* [comment removed for export] *)
Eval vm_compute in (5019, CC.cp_pc t19, CC.cp_nx t19, length (CC.cp_know t19)).
Definition o19 : CAD.pout.
Proof.
  let x := eval vm_compute in (EXPL t19 hints19 false) in
  let o := eval vm_compute in (CAD.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1019, CAD.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CAD.stucks x)) in
  let d4 := eval vm_compute in (4019, map (fun l => tagcode (snd l)) (CAD.po_leaves o)) in
  idtac "=" d1; idtac "=" d4;
  exact o.
Defined.
