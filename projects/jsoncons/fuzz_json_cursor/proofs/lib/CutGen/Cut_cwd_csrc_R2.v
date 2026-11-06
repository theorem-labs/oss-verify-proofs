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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_cwd_csrc_T Cut_cwd_csrc_R0 Cut_cwd_csrc_R1.

Definition rt65 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t50 BL50 (CC.cp_nx t50) (nth 0 (map fst (CA.po_leaves o50)) (SR.PS 0 [] [] [])).
Definition t65 : CC.cutpoint := Eval vm_compute in match rt65 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL65 : CA.blocks := Eval vm_compute in match rt65 with Some cb => snd cb | None => [] end.
Definition hints65 : list (nat * CC.subst) := hints50.
Eval vm_compute in (5065, CC.cp_pc t65, CC.cp_nx t65, length (CC.cp_know t65)).
Definition o65 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t65 hints65 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1065, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4065, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6065, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt66 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t51 BL51 (CC.cp_nx t51) (nth 0 (map fst (CA.po_leaves o51)) (SR.PS 0 [] [] [])).
Definition t66 : CC.cutpoint := Eval vm_compute in match rt66 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL66 : CA.blocks := Eval vm_compute in match rt66 with Some cb => snd cb | None => [] end.
Definition hints66 : list (nat * CC.subst) := hints51.
Eval vm_compute in (5066, CC.cp_pc t66, CC.cp_nx t66, length (CC.cp_know t66)).
Definition o66 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t66 hints66 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1066, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4066, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6066, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt67 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t52 BL52 (CC.cp_nx t52) (nth 0 (map fst (CA.po_leaves o52)) (SR.PS 0 [] [] [])).
Definition t67 : CC.cutpoint := Eval vm_compute in match rt67 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL67 : CA.blocks := Eval vm_compute in match rt67 with Some cb => snd cb | None => [] end.
Definition hints67 : list (nat * CC.subst) := hints52.
Eval vm_compute in (5067, CC.cp_pc t67, CC.cp_nx t67, length (CC.cp_know t67)).
Definition o67 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t67 hints67 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1067, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4067, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6067, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt68 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t53 BL53 (CC.cp_nx t53) (nth 0 (map fst (CA.po_leaves o53)) (SR.PS 0 [] [] [])).
Definition t68 : CC.cutpoint := Eval vm_compute in match rt68 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL68 : CA.blocks := Eval vm_compute in match rt68 with Some cb => snd cb | None => [] end.
Definition hints68 : list (nat * CC.subst) := hints53.
Eval vm_compute in (5068, CC.cp_pc t68, CC.cp_nx t68, length (CC.cp_know t68)).
Definition o68 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t68 hints68 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1068, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4068, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6068, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt69 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t54 BL54 (CC.cp_nx t54) (nth 0 (map fst (CA.po_leaves o54)) (SR.PS 0 [] [] [])).
Definition t69 : CC.cutpoint := Eval vm_compute in match rt69 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL69 : CA.blocks := Eval vm_compute in match rt69 with Some cb => snd cb | None => [] end.
Definition hints69 : list (nat * CC.subst) := hints54.
Eval vm_compute in (5069, CC.cp_pc t69, CC.cp_nx t69, length (CC.cp_know t69)).
Definition o69 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t69 hints69 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1069, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4069, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6069, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt70 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t55 BL55 (CC.cp_nx t55) (nth 0 (map fst (CA.po_leaves o55)) (SR.PS 0 [] [] [])).
Definition t70 : CC.cutpoint := Eval vm_compute in match rt70 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL70 : CA.blocks := Eval vm_compute in match rt70 with Some cb => snd cb | None => [] end.
Definition hints70 : list (nat * CC.subst) := hints55.
Eval vm_compute in (5070, CC.cp_pc t70, CC.cp_nx t70, length (CC.cp_know t70)).
Definition o70 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t70 hints70 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1070, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4070, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6070, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt71 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t56 BL56 (CC.cp_nx t56) (nth 0 (map fst (CA.po_leaves o56)) (SR.PS 0 [] [] [])).
Definition t71 : CC.cutpoint := Eval vm_compute in match rt71 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL71 : CA.blocks := Eval vm_compute in match rt71 with Some cb => snd cb | None => [] end.
Definition hints71 : list (nat * CC.subst) := hints56.
Eval vm_compute in (5071, CC.cp_pc t71, CC.cp_nx t71, length (CC.cp_know t71)).
Definition o71 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t71 hints71 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1071, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4071, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6071, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt72 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t57 BL57 (CC.cp_nx t57) (nth 0 (map fst (CA.po_leaves o57)) (SR.PS 0 [] [] [])).
Definition t72 : CC.cutpoint := Eval vm_compute in match rt72 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL72 : CA.blocks := Eval vm_compute in match rt72 with Some cb => snd cb | None => [] end.
Definition hints72 : list (nat * CC.subst) := hints57.
Eval vm_compute in (5072, CC.cp_pc t72, CC.cp_nx t72, length (CC.cp_know t72)).
Definition o72 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t72 hints72 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1072, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4072, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6072, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt73 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t58 BL58 (CC.cp_nx t58) (nth 0 (map fst (CA.po_leaves o58)) (SR.PS 0 [] [] [])).
Definition t73 : CC.cutpoint := Eval vm_compute in match rt73 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL73 : CA.blocks := Eval vm_compute in match rt73 with Some cb => snd cb | None => [] end.
Definition hints73 : list (nat * CC.subst) := hints58.
Eval vm_compute in (5073, CC.cp_pc t73, CC.cp_nx t73, length (CC.cp_know t73)).
Definition o73 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t73 hints73 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1073, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4073, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6073, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt74 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t59 BL59 (CC.cp_nx t59) (nth 0 (map fst (CA.po_leaves o59)) (SR.PS 0 [] [] [])).
Definition t74 : CC.cutpoint := Eval vm_compute in match rt74 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL74 : CA.blocks := Eval vm_compute in match rt74 with Some cb => snd cb | None => [] end.
Definition hints74 : list (nat * CC.subst) := hints59.
Eval vm_compute in (5074, CC.cp_pc t74, CC.cp_nx t74, length (CC.cp_know t74)).
Definition o74 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t74 hints74 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1074, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4074, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6074, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt75 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t60 BL60 (CC.cp_nx t60) (nth 0 (map fst (CA.po_leaves o60)) (SR.PS 0 [] [] [])).
Definition t75 : CC.cutpoint := Eval vm_compute in match rt75 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL75 : CA.blocks := Eval vm_compute in match rt75 with Some cb => snd cb | None => [] end.
Definition hints75 : list (nat * CC.subst) := hints60.
Eval vm_compute in (5075, CC.cp_pc t75, CC.cp_nx t75, length (CC.cp_know t75)).
Definition o75 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t75 hints75 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1075, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4075, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6075, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt76 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t61 BL61 (CC.cp_nx t61) (nth 0 (map fst (CA.po_leaves o61)) (SR.PS 0 [] [] [])).
Definition t76 : CC.cutpoint := Eval vm_compute in match rt76 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL76 : CA.blocks := Eval vm_compute in match rt76 with Some cb => snd cb | None => [] end.
Definition hints76 : list (nat * CC.subst) := hints61.
Eval vm_compute in (5076, CC.cp_pc t76, CC.cp_nx t76, length (CC.cp_know t76)).
Definition o76 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t76 hints76 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1076, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4076, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6076, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt77 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t62 BL62 (CC.cp_nx t62) (nth 0 (map fst (CA.po_leaves o62)) (SR.PS 0 [] [] [])).
Definition t77 : CC.cutpoint := Eval vm_compute in match rt77 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL77 : CA.blocks := Eval vm_compute in match rt77 with Some cb => snd cb | None => [] end.
Definition hints77 : list (nat * CC.subst) := hints62.
Eval vm_compute in (5077, CC.cp_pc t77, CC.cp_nx t77, length (CC.cp_know t77)).
Definition o77 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t77 hints77 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1077, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4077, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6077, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt78 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t63 BL63 (CC.cp_nx t63) (nth 0 (map fst (CA.po_leaves o63)) (SR.PS 0 [] [] [])).
Definition t78 : CC.cutpoint := Eval vm_compute in match rt78 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL78 : CA.blocks := Eval vm_compute in match rt78 with Some cb => snd cb | None => [] end.
Definition hints78 : list (nat * CC.subst) := hints63.
Eval vm_compute in (5078, CC.cp_pc t78, CC.cp_nx t78, length (CC.cp_know t78)).
Definition o78 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t78 hints78 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1078, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4078, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6078, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.

Definition rt79 := Eval vm_compute in CA.ret_tmpl HDECL (CA.cs_copy 745028) (APC.img_lo A0) (APC.img_hi A0) APART t64 BL64 (CC.cp_nx t64) (nth 0 (map fst (CA.po_leaves o64)) (SR.PS 0 [] [] [])).
Definition t79 : CC.cutpoint := Eval vm_compute in match rt79 with Some cb => fst cb | None => CA.dummy_cp end.
Definition BL79 : CA.blocks := Eval vm_compute in match rt79 with Some cb => snd cb | None => [] end.
Definition hints79 : list (nat * CC.subst) := hints64.
Eval vm_compute in (5079, CC.cp_pc t79, CC.cp_nx t79, length (CC.cp_know t79)).
Definition o79 : CA.pout.
Proof.
  let x := eval vm_compute in (EXPL t79 hints79 false) in
  let o := eval vm_compute in (CA.plan_of x 0 0 0) in
  let d1 := eval vm_compute in (1079, CA.size x, map (fun cs => (fst cs, s_pc (snd cs))) (CA.stucks x)) in
  let d4 := eval vm_compute in (4079, map (fun l => tagcode (snd l)) (CA.po_leaves o)) in
  let d6 := eval vm_compute in (6079, map (fun l => match nth 1 (CA.ps_reglist (fst l)) (ELit 0) with ELit _ => 1 | _ => 0 end) (CA.po_leaves o)) in
  idtac "=" d1; idtac "=" d4; idtac "=" d6;
  exact o.
Defined.
