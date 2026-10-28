(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_harness_xsrc_T_u5 Cut_harness_xsrc_R0_u5.
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
Definition CPS : list CC.cutpoint := [cp0; cp1; cp2; cp3; cp4; cp5; cp6; cp7; cp8; cp9; cp10; cp11; cp12; cp13; cp14; cp15].
Definition TAGS : list (list CC.tag) := Eval vm_compute in [map snd (CA.po_leaves o0); map snd (CA.po_leaves o1); map snd (CA.po_leaves o2); map snd (CA.po_leaves o3); map snd (CA.po_leaves o4); map snd (CA.po_leaves o5); map snd (CA.po_leaves o6); map snd (CA.po_leaves o7); map snd (CA.po_leaves o8); map snd (CA.po_leaves o9); map snd (CA.po_leaves o10); map snd (CA.po_leaves o11); map snd (CA.po_leaves o12); map snd (CA.po_leaves o13); map snd (CA.po_leaves o14); map snd (CA.po_leaves o15)].
Definition BLS : list CA.blocks := [BL0; BL1; BL2; BL3; BL4; BL5; BL6; BL7; BL8; BL9; BL10; BL11; BL12; BL13; BL14; BL15].
Definition HDECL := Cut_harness_xsrc_T_u5.HDECL.
(* [comment removed for export] *)
Definition RETS : list (nat * nat * nat * Z) := [].
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
  destruct i; discriminate H.
Qed.
Lemma NF_le : forall i c, nth_error CPS i = Some c -> (NF <= CC.cp_nx c)%nat.
Proof.
  assert (X : CC.cps_all CPS (fun _ c => Nat.leb NF (CC.cp_nx c)) = true) by (vm_cast_no_check (@eq_refl bool true)).
  intros i c H. apply Nat.leb_le. exact (CC.cps_all_sound _ _ X i c H).
Qed.
