(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm10CutKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_cwd_csrc_T.
Definition o0 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t0 hints0 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1000, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4000, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6000, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o1 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t1 hints1 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1001, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4001, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6001, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o2 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t2 hints2 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1002, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4002, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6002, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o3 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t3 hints3 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1003, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4003, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6003, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o4 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t4 hints4 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1004, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4004, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6004, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o5 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t5 hints5 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1005, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4005, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6005, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o6 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t6 hints6 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1006, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4006, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6006, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o7 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t7 hints7 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1007, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4007, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6007, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o8 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t8 hints8 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1008, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4008, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6008, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o9 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t9 hints9 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1009, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4009, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6009, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o10 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t10 hints10 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1010, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4010, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6010, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o11 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t11 hints11 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1011, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4011, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6011, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o12 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t12 hints12 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1012, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4012, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6012, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o13 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t13 hints13 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1013, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4013, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6013, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o14 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t14 hints14 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1014, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4014, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6014, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o15 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t15 hints15 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1015, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4015, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6015, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o16 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t16 hints16 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1016, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4016, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6016, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o17 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t17 hints17 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1017, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4017, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6017, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o18 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t18 hints18 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1018, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4018, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6018, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o19 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t19 hints19 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1019, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4019, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6019, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o20 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t20 hints20 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1020, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4020, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6020, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o21 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t21 hints21 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1021, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4021, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6021, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o22 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t22 hints22 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1022, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4022, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6022, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o23 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t23 hints23 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1023, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4023, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6023, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o24 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t24 hints24 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1024, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4024, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6024, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o25 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t25 hints25 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1025, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4025, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6025, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o26 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t26 hints26 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1026, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4026, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6026, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o27 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t27 hints27 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1027, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4027, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6027, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o28 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t28 hints28 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1028, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4028, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6028, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o29 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t29 hints29 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1029, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4029, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6029, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o30 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t30 hints30 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1030, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4030, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6030, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o31 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t31 hints31 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1031, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4031, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6031, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o32 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t32 hints32 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1032, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4032, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6032, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o33 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t33 hints33 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1033, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4033, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6033, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o34 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t34 hints34 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1034, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4034, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6034, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o35 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t35 hints35 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1035, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4035, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6035, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o36 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t36 hints36 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1036, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4036, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6036, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o37 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t37 hints37 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1037, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4037, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6037, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o38 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t38 hints38 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1038, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4038, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6038, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o39 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t39 hints39 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1039, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4039, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6039, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o40 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t40 hints40 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1040, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4040, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6040, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o41 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t41 hints41 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1041, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4041, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6041, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o42 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t42 hints42 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1042, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4042, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6042, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o43 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t43 hints43 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1043, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4043, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6043, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o44 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t44 hints44 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1044, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4044, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6044, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o45 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t45 hints45 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1045, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4045, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6045, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o46 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t46 hints46 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1046, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4046, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6046, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o47 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t47 hints47 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1047, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4047, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6047, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o48 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t48 hints48 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1048, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4048, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6048, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
Definition o49 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t49 hints49 true) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1049, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4049, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6049, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
