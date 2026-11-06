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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_cwd_csrc_T Cut_cwd_csrc_R0.

Definition rt50 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t5 BL5 (CC.cp_nx t5) (nth 0 (map fst (CA.po_leaves o5)) (SR.PS 0 [] [] [])).
Definition t50 : CC.cutpoint := Eval vm_compute in match rt50 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL50 : CA.blocks := Eval vm_compute in match rt50 with Some cb => snd cb | None => [] end.
Definition hints50 : list (nat * CC.subst) := hints5.
Eval vm_compute in (5050, CC.cp_pc t50, CC.cp_nx t50, length (CC.cp_know t50)).
Definition o50 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t50 hints50 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1050, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4050, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6050, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt51 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t10 BL10 (CC.cp_nx t10) (nth 0 (map fst (CA.po_leaves o10)) (SR.PS 0 [] [] [])).
Definition t51 : CC.cutpoint := Eval vm_compute in match rt51 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL51 : CA.blocks := Eval vm_compute in match rt51 with Some cb => snd cb | None => [] end.
Definition hints51 : list (nat * CC.subst) := hints10.
Eval vm_compute in (5051, CC.cp_pc t51, CC.cp_nx t51, length (CC.cp_know t51)).
Definition o51 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t51 hints51 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1051, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4051, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6051, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt52 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t14 BL14 (CC.cp_nx t14) (nth 0 (map fst (CA.po_leaves o14)) (SR.PS 0 [] [] [])).
Definition t52 : CC.cutpoint := Eval vm_compute in match rt52 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL52 : CA.blocks := Eval vm_compute in match rt52 with Some cb => snd cb | None => [] end.
Definition hints52 : list (nat * CC.subst) := hints14.
Eval vm_compute in (5052, CC.cp_pc t52, CC.cp_nx t52, length (CC.cp_know t52)).
Definition o52 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t52 hints52 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1052, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4052, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6052, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt53 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t15 BL15 (CC.cp_nx t15) (nth 0 (map fst (CA.po_leaves o15)) (SR.PS 0 [] [] [])).
Definition t53 : CC.cutpoint := Eval vm_compute in match rt53 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL53 : CA.blocks := Eval vm_compute in match rt53 with Some cb => snd cb | None => [] end.
Definition hints53 : list (nat * CC.subst) := hints15.
Eval vm_compute in (5053, CC.cp_pc t53, CC.cp_nx t53, length (CC.cp_know t53)).
Definition o53 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t53 hints53 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1053, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4053, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6053, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt54 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t19 BL19 (CC.cp_nx t19) (nth 0 (map fst (CA.po_leaves o19)) (SR.PS 0 [] [] [])).
Definition t54 : CC.cutpoint := Eval vm_compute in match rt54 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL54 : CA.blocks := Eval vm_compute in match rt54 with Some cb => snd cb | None => [] end.
Definition hints54 : list (nat * CC.subst) := hints19.
Eval vm_compute in (5054, CC.cp_pc t54, CC.cp_nx t54, length (CC.cp_know t54)).
Definition o54 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t54 hints54 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1054, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4054, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6054, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt55 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t24 BL24 (CC.cp_nx t24) (nth 0 (map fst (CA.po_leaves o24)) (SR.PS 0 [] [] [])).
Definition t55 : CC.cutpoint := Eval vm_compute in match rt55 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL55 : CA.blocks := Eval vm_compute in match rt55 with Some cb => snd cb | None => [] end.
Definition hints55 : list (nat * CC.subst) := hints24.
Eval vm_compute in (5055, CC.cp_pc t55, CC.cp_nx t55, length (CC.cp_know t55)).
Definition o55 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t55 hints55 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1055, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4055, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6055, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt56 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t25 BL25 (CC.cp_nx t25) (nth 0 (map fst (CA.po_leaves o25)) (SR.PS 0 [] [] [])).
Definition t56 : CC.cutpoint := Eval vm_compute in match rt56 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL56 : CA.blocks := Eval vm_compute in match rt56 with Some cb => snd cb | None => [] end.
Definition hints56 : list (nat * CC.subst) := hints25.
Eval vm_compute in (5056, CC.cp_pc t56, CC.cp_nx t56, length (CC.cp_know t56)).
Definition o56 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t56 hints56 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1056, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4056, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6056, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt57 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t33 BL33 (CC.cp_nx t33) (nth 0 (map fst (CA.po_leaves o33)) (SR.PS 0 [] [] [])).
Definition t57 : CC.cutpoint := Eval vm_compute in match rt57 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL57 : CA.blocks := Eval vm_compute in match rt57 with Some cb => snd cb | None => [] end.
Definition hints57 : list (nat * CC.subst) := hints33.
Eval vm_compute in (5057, CC.cp_pc t57, CC.cp_nx t57, length (CC.cp_know t57)).
Definition o57 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t57 hints57 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1057, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4057, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6057, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt58 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t35 BL35 (CC.cp_nx t35) (nth 0 (map fst (CA.po_leaves o35)) (SR.PS 0 [] [] [])).
Definition t58 : CC.cutpoint := Eval vm_compute in match rt58 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL58 : CA.blocks := Eval vm_compute in match rt58 with Some cb => snd cb | None => [] end.
Definition hints58 : list (nat * CC.subst) := hints35.
Eval vm_compute in (5058, CC.cp_pc t58, CC.cp_nx t58, length (CC.cp_know t58)).
Definition o58 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t58 hints58 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1058, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4058, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6058, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt59 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t37 BL37 (CC.cp_nx t37) (nth 0 (map fst (CA.po_leaves o37)) (SR.PS 0 [] [] [])).
Definition t59 : CC.cutpoint := Eval vm_compute in match rt59 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL59 : CA.blocks := Eval vm_compute in match rt59 with Some cb => snd cb | None => [] end.
Definition hints59 : list (nat * CC.subst) := hints37.
Eval vm_compute in (5059, CC.cp_pc t59, CC.cp_nx t59, length (CC.cp_know t59)).
Definition o59 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t59 hints59 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1059, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4059, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6059, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt60 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t39 BL39 (CC.cp_nx t39) (nth 0 (map fst (CA.po_leaves o39)) (SR.PS 0 [] [] [])).
Definition t60 : CC.cutpoint := Eval vm_compute in match rt60 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL60 : CA.blocks := Eval vm_compute in match rt60 with Some cb => snd cb | None => [] end.
Definition hints60 : list (nat * CC.subst) := hints39.
Eval vm_compute in (5060, CC.cp_pc t60, CC.cp_nx t60, length (CC.cp_know t60)).
Definition o60 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t60 hints60 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1060, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4060, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6060, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt61 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t41 BL41 (CC.cp_nx t41) (nth 2 (map fst (CA.po_leaves o41)) (SR.PS 0 [] [] [])).
Definition t61 : CC.cutpoint := Eval vm_compute in match rt61 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL61 : CA.blocks := Eval vm_compute in match rt61 with Some cb => snd cb | None => [] end.
Definition hints61 : list (nat * CC.subst) := hints41.
Eval vm_compute in (5061, CC.cp_pc t61, CC.cp_nx t61, length (CC.cp_know t61)).
Definition o61 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t61 hints61 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1061, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4061, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6061, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt62 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t43 BL43 (CC.cp_nx t43) (nth 0 (map fst (CA.po_leaves o43)) (SR.PS 0 [] [] [])).
Definition t62 : CC.cutpoint := Eval vm_compute in match rt62 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL62 : CA.blocks := Eval vm_compute in match rt62 with Some cb => snd cb | None => [] end.
Definition hints62 : list (nat * CC.subst) := hints43.
Eval vm_compute in (5062, CC.cp_pc t62, CC.cp_nx t62, length (CC.cp_know t62)).
Definition o62 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t62 hints62 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1062, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4062, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6062, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt63 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t45 BL45 (CC.cp_nx t45) (nth 0 (map fst (CA.po_leaves o45)) (SR.PS 0 [] [] [])).
Definition t63 : CC.cutpoint := Eval vm_compute in match rt63 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL63 : CA.blocks := Eval vm_compute in match rt63 with Some cb => snd cb | None => [] end.
Definition hints63 : list (nat * CC.subst) := hints45.
Eval vm_compute in (5063, CC.cp_pc t63, CC.cp_nx t63, length (CC.cp_know t63)).
Definition o63 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t63 hints63 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1063, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4063, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6063, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt64 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_malloc 684944) (APC.img_lo A0) (APC.img_hi A0) APART t47 BL47 (CC.cp_nx t47) (nth 0 (map fst (CA.po_leaves o47)) (SR.PS 0 [] [] [])).
Definition t64 : CC.cutpoint := Eval vm_compute in match rt64 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL64 : CA.blocks := Eval vm_compute in match rt64 with Some cb => snd cb | None => [] end.
Definition hints64 : list (nat * CC.subst) := hints47.
Eval vm_compute in (5064, CC.cp_pc t64, CC.cp_nx t64, length (CC.cp_know t64)).
Definition o64 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t64 hints64 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1064, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4064, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6064, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
