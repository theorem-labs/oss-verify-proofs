(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_pr_xsrc_T_u5 Cut_pr_xsrc_R0_u5 Cut_pr_xsrc_R1_u5 Cut_pr_xsrc_R2_u5 Cut_pr_xsrc_R3_u5.
Definition cp0 : CC.cutpoint := Eval vm_compute in mkcp t0 o0.
Definition cp1 : CC.cutpoint := Eval vm_compute in mkcp t1 o1.
Definition cp2 : CC.cutpoint := Eval vm_compute in mkcp t2 o2.
Definition cp3 : CC.cutpoint := Eval vm_compute in mkcp t3 o3.
Definition cp4 : CC.cutpoint := Eval vm_compute in mkcp t4 o4.
Definition cp5 : CC.cutpoint := Eval vm_compute in mkcp t5 o5.
Definition cp6 : CC.cutpoint := Eval vm_compute in mkcp t6 o6.
Definition cp7 : CC.cutpoint := Eval vm_compute in mkcp t7 o7.
Definition cp8 : CC.cutpoint := Eval vm_compute in mkcp t8 o8.
Definition cp9 : CC.cutpoint := Eval vm_compute in mkcp t9 o9.
Definition cp10 : CC.cutpoint := Eval vm_compute in mkcp t10 o10.
Definition cp11 : CC.cutpoint := Eval vm_compute in mkcp t11 o11.
Definition cp12 : CC.cutpoint := Eval vm_compute in mkcp t12 o12.
Definition cp13 : CC.cutpoint := Eval vm_compute in mkcp t13 o13.
Definition cp14 : CC.cutpoint := Eval vm_compute in mkcp t14 o14.
Definition cp15 : CC.cutpoint := Eval vm_compute in mkcp t15 o15.
Definition cp16 : CC.cutpoint := Eval vm_compute in mkcp t16 o16.
Definition cp17 : CC.cutpoint := Eval vm_compute in mkcp t17 o17.
Definition cp18 : CC.cutpoint := Eval vm_compute in mkcp t18 o18.
Definition cp19 : CC.cutpoint := Eval vm_compute in mkcp t19 o19.
Definition cp20 : CC.cutpoint := Eval vm_compute in mkcp t20 o20.
Definition cp21 : CC.cutpoint := Eval vm_compute in mkcp t21 o21.
Definition cp22 : CC.cutpoint := Eval vm_compute in mkcp t22 o22.
Definition cp23 : CC.cutpoint := Eval vm_compute in mkcp t23 o23.
Definition cp24 : CC.cutpoint := Eval vm_compute in mkcp t24 o24.
Definition cp25 : CC.cutpoint := Eval vm_compute in mkcp t25 o25.
Definition cp26 : CC.cutpoint := Eval vm_compute in mkcp t26 o26.
Definition cp27 : CC.cutpoint := Eval vm_compute in mkcp t27 o27.
Definition cp28 : CC.cutpoint := Eval vm_compute in mkcp t28 o28.
Definition cp29 : CC.cutpoint := Eval vm_compute in mkcp t29 o29.
Definition cp30 : CC.cutpoint := Eval vm_compute in mkcp t30 o30.
Definition cp31 : CC.cutpoint := Eval vm_compute in mkcp t31 o31.
Definition cp32 : CC.cutpoint := Eval vm_compute in mkcp t32 o32.
Definition cp33 : CC.cutpoint := Eval vm_compute in mkcp t33 o33.
Definition cp34 : CC.cutpoint := Eval vm_compute in mkcp t34 o34.
Definition cp35 : CC.cutpoint := Eval vm_compute in mkcp t35 o35.
Definition cp36 : CC.cutpoint := Eval vm_compute in mkcp t36 o36.
Definition cp37 : CC.cutpoint := Eval vm_compute in mkcp t37 o37.
Definition cp38 : CC.cutpoint := Eval vm_compute in mkcp t38 o38.
Definition cp39 : CC.cutpoint := Eval vm_compute in mkcp t39 o39.
Definition cp40 : CC.cutpoint := Eval vm_compute in mkcp t40 o40.
Definition cp41 : CC.cutpoint := Eval vm_compute in mkcp t41 o41.
Definition cp42 : CC.cutpoint := Eval vm_compute in mkcp t42 o42.
Definition cp43 : CC.cutpoint := Eval vm_compute in mkcp t43 o43.
Definition cp44 : CC.cutpoint := Eval vm_compute in mkcp t44 o44.
Definition cp45 : CC.cutpoint := Eval vm_compute in mkcp t45 o45.
Definition cp46 : CC.cutpoint := Eval vm_compute in mkcp t46 o46.
Definition CPS : list CC.cutpoint := [cp0; cp1; cp2; cp3; cp4; cp5; cp6; cp7; cp8; cp9; cp10; cp11; cp12; cp13; cp14; cp15; cp16; cp17; cp18; cp19; cp20; cp21; cp22; cp23; cp24; cp25; cp26; cp27; cp28; cp29; cp30; cp31; cp32; cp33; cp34; cp35; cp36; cp37; cp38; cp39; cp40; cp41; cp42; cp43; cp44; cp45; cp46].
Definition TAGS : list (list CC.tag) := Eval vm_compute in [map snd (CA.po_leaves o0); map snd (CA.po_leaves o1); map snd (CA.po_leaves o2); map snd (CA.po_leaves o3); map snd (CA.po_leaves o4); map snd (CA.po_leaves o5); map snd (CA.po_leaves o6); map snd (CA.po_leaves o7); map snd (CA.po_leaves o8); map snd (CA.po_leaves o9); map snd (CA.po_leaves o10); map snd (CA.po_leaves o11); map snd (CA.po_leaves o12); map snd (CA.po_leaves o13); map snd (CA.po_leaves o14); map snd (CA.po_leaves o15); map snd (CA.po_leaves o16); map snd (CA.po_leaves o17); map snd (CA.po_leaves o18); map snd (CA.po_leaves o19); map snd (CA.po_leaves o20); map snd (CA.po_leaves o21); map snd (CA.po_leaves o22); map snd (CA.po_leaves o23); map snd (CA.po_leaves o24); map snd (CA.po_leaves o25); map snd (CA.po_leaves o26); map snd (CA.po_leaves o27); map snd (CA.po_leaves o28); map snd (CA.po_leaves o29); map snd (CA.po_leaves o30); map snd (CA.po_leaves o31); map snd (CA.po_leaves o32); map snd (CA.po_leaves o33); map snd (CA.po_leaves o34); map snd (CA.po_leaves o35); map snd (CA.po_leaves o36); map snd (CA.po_leaves o37); map snd (CA.po_leaves o38); map snd (CA.po_leaves o39); map snd (CA.po_leaves o40); map snd (CA.po_leaves o41); map snd (CA.po_leaves o42); map snd (CA.po_leaves o43); map snd (CA.po_leaves o44); map snd (CA.po_leaves o45); map snd (CA.po_leaves o46)].
Definition BLS : list CA.blocks := [BL0; BL1; BL2; BL3; BL4; BL5; BL6; BL7; BL8; BL9; BL10; BL11; BL12; BL13; BL14; BL15; BL16; BL17; BL18; BL19; BL20; BL21; BL22; BL23; BL24; BL25; BL26; BL27; BL28; BL29; BL30; BL31; BL32; BL33; BL34; BL35; BL36; BL37; BL38; BL39; BL40; BL41; BL42; BL43; BL44; BL45; BL46].
Definition HDECL := Cut_pr_xsrc_T_u5.HDECL.
(* [comment removed for export] *)
Definition RETS : list (nat * nat * nat * Z) := [(14%nat, 2%nat, 0%nat, 436872); (15%nat, 3%nat, 0%nat, 436872); (16%nat, 3%nat, 1%nat, 436872); (17%nat, 3%nat, 2%nat, 436872); (18%nat, 4%nat, 0%nat, 436872); (19%nat, 4%nat, 1%nat, 436872); (20%nat, 5%nat, 0%nat, 436872); (21%nat, 6%nat, 0%nat, 436872); (22%nat, 7%nat, 0%nat, 436872); (23%nat, 8%nat, 0%nat, 436872); (24%nat, 9%nat, 0%nat, 436872); (25%nat, 10%nat, 0%nat, 436872); (26%nat, 11%nat, 0%nat, 436872); (27%nat, 12%nat, 0%nat, 436872); (28%nat, 13%nat, 0%nat, 436872); (29%nat, 13%nat, 1%nat, 436872); (30%nat, 13%nat, 2%nat, 436872); (31%nat, 14%nat, 0%nat, 436872); (32%nat, 15%nat, 0%nat, 436872); (33%nat, 16%nat, 0%nat, 436872); (34%nat, 17%nat, 0%nat, 436872); (35%nat, 18%nat, 0%nat, 436872); (36%nat, 19%nat, 0%nat, 436872); (37%nat, 20%nat, 1%nat, 436872); (38%nat, 21%nat, 0%nat, 436872); (39%nat, 22%nat, 0%nat, 436872); (40%nat, 26%nat, 0%nat, 436872); (41%nat, 27%nat, 0%nat, 436872); (42%nat, 30%nat, 0%nat, 436872); (43%nat, 33%nat, 0%nat, 436872); (44%nat, 35%nat, 0%nat, 436872); (45%nat, 40%nat, 0%nat, 436872); (46%nat, 41%nat, 0%nat, 436872)].
Lemma cert0 : src0_cut_cert ITR BF cp0 (CA.po_ops o0) (CA.po_ops2 o0) (CA.po_plan o0) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert1 : src0_cut_cert ITR BF cp1 (CA.po_ops o1) (CA.po_ops2 o1) (CA.po_plan o1) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert2 : src0_cut_cert ITR BF cp2 (CA.po_ops o2) (CA.po_ops2 o2) (CA.po_plan o2) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert3 : src0_cut_cert ITR BF cp3 (CA.po_ops o3) (CA.po_ops2 o3) (CA.po_plan o3) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert4 : src0_cut_cert ITR BF cp4 (CA.po_ops o4) (CA.po_ops2 o4) (CA.po_plan o4) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert5 : src0_cut_cert ITR BF cp5 (CA.po_ops o5) (CA.po_ops2 o5) (CA.po_plan o5) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert6 : src0_cut_cert ITR BF cp6 (CA.po_ops o6) (CA.po_ops2 o6) (CA.po_plan o6) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert7 : src0_cut_cert ITR BF cp7 (CA.po_ops o7) (CA.po_ops2 o7) (CA.po_plan o7) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert8 : src0_cut_cert ITR BF cp8 (CA.po_ops o8) (CA.po_ops2 o8) (CA.po_plan o8) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert9 : src0_cut_cert ITR BF cp9 (CA.po_ops o9) (CA.po_ops2 o9) (CA.po_plan o9) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert10 : src0_cut_cert ITR BF cp10 (CA.po_ops o10) (CA.po_ops2 o10) (CA.po_plan o10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert11 : src0_cut_cert ITR BF cp11 (CA.po_ops o11) (CA.po_ops2 o11) (CA.po_plan o11) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert12 : src0_cut_cert ITR BF cp12 (CA.po_ops o12) (CA.po_ops2 o12) (CA.po_plan o12) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert13 : src0_cut_cert ITR BF cp13 (CA.po_ops o13) (CA.po_ops2 o13) (CA.po_plan o13) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert14 : src0_cut_cert ITR BF cp14 (CA.po_ops o14) (CA.po_ops2 o14) (CA.po_plan o14) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert15 : src0_cut_cert ITR BF cp15 (CA.po_ops o15) (CA.po_ops2 o15) (CA.po_plan o15) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert16 : src0_cut_cert ITR BF cp16 (CA.po_ops o16) (CA.po_ops2 o16) (CA.po_plan o16) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert17 : src0_cut_cert ITR BF cp17 (CA.po_ops o17) (CA.po_ops2 o17) (CA.po_plan o17) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert18 : src0_cut_cert ITR BF cp18 (CA.po_ops o18) (CA.po_ops2 o18) (CA.po_plan o18) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert19 : src0_cut_cert ITR BF cp19 (CA.po_ops o19) (CA.po_ops2 o19) (CA.po_plan o19) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert20 : src0_cut_cert ITR BF cp20 (CA.po_ops o20) (CA.po_ops2 o20) (CA.po_plan o20) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert21 : src0_cut_cert ITR BF cp21 (CA.po_ops o21) (CA.po_ops2 o21) (CA.po_plan o21) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert22 : src0_cut_cert ITR BF cp22 (CA.po_ops o22) (CA.po_ops2 o22) (CA.po_plan o22) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert23 : src0_cut_cert ITR BF cp23 (CA.po_ops o23) (CA.po_ops2 o23) (CA.po_plan o23) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert24 : src0_cut_cert ITR BF cp24 (CA.po_ops o24) (CA.po_ops2 o24) (CA.po_plan o24) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert25 : src0_cut_cert ITR BF cp25 (CA.po_ops o25) (CA.po_ops2 o25) (CA.po_plan o25) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert26 : src0_cut_cert ITR BF cp26 (CA.po_ops o26) (CA.po_ops2 o26) (CA.po_plan o26) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert27 : src0_cut_cert ITR BF cp27 (CA.po_ops o27) (CA.po_ops2 o27) (CA.po_plan o27) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert28 : src0_cut_cert ITR BF cp28 (CA.po_ops o28) (CA.po_ops2 o28) (CA.po_plan o28) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert29 : src0_cut_cert ITR BF cp29 (CA.po_ops o29) (CA.po_ops2 o29) (CA.po_plan o29) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert30 : src0_cut_cert ITR BF cp30 (CA.po_ops o30) (CA.po_ops2 o30) (CA.po_plan o30) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert31 : src0_cut_cert ITR BF cp31 (CA.po_ops o31) (CA.po_ops2 o31) (CA.po_plan o31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert32 : src0_cut_cert ITR BF cp32 (CA.po_ops o32) (CA.po_ops2 o32) (CA.po_plan o32) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert33 : src0_cut_cert ITR BF cp33 (CA.po_ops o33) (CA.po_ops2 o33) (CA.po_plan o33) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert34 : src0_cut_cert ITR BF cp34 (CA.po_ops o34) (CA.po_ops2 o34) (CA.po_plan o34) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert35 : src0_cut_cert ITR BF cp35 (CA.po_ops o35) (CA.po_ops2 o35) (CA.po_plan o35) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert36 : src0_cut_cert ITR BF cp36 (CA.po_ops o36) (CA.po_ops2 o36) (CA.po_plan o36) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert37 : src0_cut_cert ITR BF cp37 (CA.po_ops o37) (CA.po_ops2 o37) (CA.po_plan o37) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert38 : src0_cut_cert ITR BF cp38 (CA.po_ops o38) (CA.po_ops2 o38) (CA.po_plan o38) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert39 : src0_cut_cert ITR BF cp39 (CA.po_ops o39) (CA.po_ops2 o39) (CA.po_plan o39) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert40 : src0_cut_cert ITR BF cp40 (CA.po_ops o40) (CA.po_ops2 o40) (CA.po_plan o40) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert41 : src0_cut_cert ITR BF cp41 (CA.po_ops o41) (CA.po_ops2 o41) (CA.po_plan o41) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert42 : src0_cut_cert ITR BF cp42 (CA.po_ops o42) (CA.po_ops2 o42) (CA.po_plan o42) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert43 : src0_cut_cert ITR BF cp43 (CA.po_ops o43) (CA.po_ops2 o43) (CA.po_plan o43) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert44 : src0_cut_cert ITR BF cp44 (CA.po_ops o44) (CA.po_ops2 o44) (CA.po_plan o44) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert45 : src0_cut_cert ITR BF cp45 (CA.po_ops o45) (CA.po_ops2 o45) (CA.po_plan o45) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert46 : src0_cut_cert ITR BF cp46 (CA.po_ops o46) (CA.po_ops2 o46) (CA.po_plan o46) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma tags_ok : CC.tags_chk CPS TAGS NF = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma plans : forall i c, nth_error CPS i = Some c -> CC.plan_sound RSEGS c.
Proof.
  intros i c H.
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert0)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert1)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert2)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert3)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert4)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert5)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert6)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert7)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert8)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert9)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert10)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert11)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert12)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert13)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert14)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert15)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert16)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert17)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert18)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert19)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert20)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert21)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert22)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert23)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert24)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert25)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert26)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert27)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert28)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert29)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert30)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert31)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert32)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert33)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert34)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert35)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert36)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert37)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert38)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert39)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert40)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert41)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert42)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert43)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert44)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert45)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cut_plan_sound _ _ _ _ _ _ cert46)|].
  destruct i; discriminate H.
Qed.
Lemma NF_le : forall i c, nth_error CPS i = Some c -> (NF <= CC.cp_nx c)%nat.
Proof.
  assert (X : CC.cps_all CPS (fun _ c => Nat.leb NF (CC.cp_nx c)) = true) by (vm_cast_no_check (@eq_refl bool true)).
  intros i c H. apply Nat.leb_le. exact (CC.cps_all_sound _ _ X i c H).
Qed.
