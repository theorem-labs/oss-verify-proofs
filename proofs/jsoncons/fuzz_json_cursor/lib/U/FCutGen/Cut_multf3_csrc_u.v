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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_multf3_csrc_T_u Cut_multf3_csrc_R0_u.
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
Definition CPS : list CC.cutpoint := [cp0; cp1; cp2; cp3; cp4; cp5; cp6; cp7; cp8; cp9; cp10; cp11; cp12; cp13; cp14; cp15; cp16; cp17; cp18; cp19; cp20; cp21; cp22; cp23; cp24; cp25; cp26; cp27].
Definition TAGS : list (list CC.tag) := Eval vm_compute in [map snd (CAD.po_leaves o0); map snd (CAD.po_leaves o1); map snd (CAD.po_leaves o2); map snd (CAD.po_leaves o3); map snd (CAD.po_leaves o4); map snd (CAD.po_leaves o5); map snd (CAD.po_leaves o6); map snd (CAD.po_leaves o7); map snd (CAD.po_leaves o8); map snd (CAD.po_leaves o9); map snd (CAD.po_leaves o10); map snd (CAD.po_leaves o11); map snd (CAD.po_leaves o12); map snd (CAD.po_leaves o13); map snd (CAD.po_leaves o14); map snd (CAD.po_leaves o15); map snd (CAD.po_leaves o16); map snd (CAD.po_leaves o17); map snd (CAD.po_leaves o18); map snd (CAD.po_leaves o19); map snd (CAD.po_leaves o20); map snd (CAD.po_leaves o21); map snd (CAD.po_leaves o22); map snd (CAD.po_leaves o23); map snd (CAD.po_leaves o24); map snd (CAD.po_leaves o25); map snd (CAD.po_leaves o26); map snd (CAD.po_leaves o27)].
Definition BLS : list CAD.blocks := [BL0; BL1; BL2; BL3; BL4; BL5; BL6; BL7; BL8; BL9; BL10; BL11; BL12; BL13; BL14; BL15; BL16; BL17; BL18; BL19; BL20; BL21; BL22; BL23; BL24; BL25; BL26; BL27].
Definition HDECL := Cut_multf3_csrc_T_u.HDECL.

Definition RETS : list (nat * nat * nat * Z) := [].

Definition LEMS : list (list kentry * kentry) := Eval vm_compute in CXD.lem_dedup (CXD.lemmas_of (CAD.po_ops o0) ++ CXD.lemmas_of (CAD.po_ops o1) ++ CXD.lemmas_of (CAD.po_ops o2) ++ CXD.lemmas_of (CAD.po_ops o3) ++ CXD.lemmas_of (CAD.po_ops o4) ++ CXD.lemmas_of (CAD.po_ops o5) ++ CXD.lemmas_of (CAD.po_ops o6) ++ CXD.lemmas_of (CAD.po_ops o7) ++ CXD.lemmas_of (CAD.po_ops o8) ++ CXD.lemmas_of (CAD.po_ops o9) ++ CXD.lemmas_of (CAD.po_ops o10) ++ CXD.lemmas_of (CAD.po_ops o11) ++ CXD.lemmas_of (CAD.po_ops o12) ++ CXD.lemmas_of (CAD.po_ops o13) ++ CXD.lemmas_of (CAD.po_ops o14) ++ CXD.lemmas_of (CAD.po_ops o15) ++ CXD.lemmas_of (CAD.po_ops o16) ++ CXD.lemmas_of (CAD.po_ops o17) ++ CXD.lemmas_of (CAD.po_ops o18) ++ CXD.lemmas_of (CAD.po_ops o19) ++ CXD.lemmas_of (CAD.po_ops o20) ++ CXD.lemmas_of (CAD.po_ops o21) ++ CXD.lemmas_of (CAD.po_ops o22) ++ CXD.lemmas_of (CAD.po_ops o23) ++ CXD.lemmas_of (CAD.po_ops o24) ++ CXD.lemmas_of (CAD.po_ops o25) ++ CXD.lemmas_of (CAD.po_ops o26) ++ CXD.lemmas_of (CAD.po_ops o27)).
Definition LEMS_OK : Prop := CXD.LEMS_OK RSEGS LEMS.
Lemma lsub0 : CXD.lems_chk LEMS (CAD.po_ops o0) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert0 : src0_cutd_cert ITR BF cp0 (CAD.po_ops o0) (CAD.po_ops2 o0) (CAD.po_plan o0) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub1 : CXD.lems_chk LEMS (CAD.po_ops o1) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert1 : src0_cutd_cert ITR BF cp1 (CAD.po_ops o1) (CAD.po_ops2 o1) (CAD.po_plan o1) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub2 : CXD.lems_chk LEMS (CAD.po_ops o2) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert2 : src0_cutd_cert ITR BF cp2 (CAD.po_ops o2) (CAD.po_ops2 o2) (CAD.po_plan o2) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub3 : CXD.lems_chk LEMS (CAD.po_ops o3) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert3 : src0_cutd_cert ITR BF cp3 (CAD.po_ops o3) (CAD.po_ops2 o3) (CAD.po_plan o3) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub4 : CXD.lems_chk LEMS (CAD.po_ops o4) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert4 : src0_cutd_cert ITR BF cp4 (CAD.po_ops o4) (CAD.po_ops2 o4) (CAD.po_plan o4) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub5 : CXD.lems_chk LEMS (CAD.po_ops o5) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert5 : src0_cutd_cert ITR BF cp5 (CAD.po_ops o5) (CAD.po_ops2 o5) (CAD.po_plan o5) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub6 : CXD.lems_chk LEMS (CAD.po_ops o6) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert6 : src0_cutd_cert ITR BF cp6 (CAD.po_ops o6) (CAD.po_ops2 o6) (CAD.po_plan o6) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub7 : CXD.lems_chk LEMS (CAD.po_ops o7) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert7 : src0_cutd_cert ITR BF cp7 (CAD.po_ops o7) (CAD.po_ops2 o7) (CAD.po_plan o7) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub8 : CXD.lems_chk LEMS (CAD.po_ops o8) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert8 : src0_cutd_cert ITR BF cp8 (CAD.po_ops o8) (CAD.po_ops2 o8) (CAD.po_plan o8) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub9 : CXD.lems_chk LEMS (CAD.po_ops o9) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert9 : src0_cutd_cert ITR BF cp9 (CAD.po_ops o9) (CAD.po_ops2 o9) (CAD.po_plan o9) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub10 : CXD.lems_chk LEMS (CAD.po_ops o10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert10 : src0_cutd_cert ITR BF cp10 (CAD.po_ops o10) (CAD.po_ops2 o10) (CAD.po_plan o10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub11 : CXD.lems_chk LEMS (CAD.po_ops o11) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert11 : src0_cutd_cert ITR BF cp11 (CAD.po_ops o11) (CAD.po_ops2 o11) (CAD.po_plan o11) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub12 : CXD.lems_chk LEMS (CAD.po_ops o12) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert12 : src0_cutd_cert ITR BF cp12 (CAD.po_ops o12) (CAD.po_ops2 o12) (CAD.po_plan o12) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub13 : CXD.lems_chk LEMS (CAD.po_ops o13) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert13 : src0_cutd_cert ITR BF cp13 (CAD.po_ops o13) (CAD.po_ops2 o13) (CAD.po_plan o13) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub14 : CXD.lems_chk LEMS (CAD.po_ops o14) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert14 : src0_cutd_cert ITR BF cp14 (CAD.po_ops o14) (CAD.po_ops2 o14) (CAD.po_plan o14) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub15 : CXD.lems_chk LEMS (CAD.po_ops o15) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert15 : src0_cutd_cert ITR BF cp15 (CAD.po_ops o15) (CAD.po_ops2 o15) (CAD.po_plan o15) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub16 : CXD.lems_chk LEMS (CAD.po_ops o16) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert16 : src0_cutd_cert ITR BF cp16 (CAD.po_ops o16) (CAD.po_ops2 o16) (CAD.po_plan o16) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub17 : CXD.lems_chk LEMS (CAD.po_ops o17) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert17 : src0_cutd_cert ITR BF cp17 (CAD.po_ops o17) (CAD.po_ops2 o17) (CAD.po_plan o17) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub18 : CXD.lems_chk LEMS (CAD.po_ops o18) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert18 : src0_cutd_cert ITR BF cp18 (CAD.po_ops o18) (CAD.po_ops2 o18) (CAD.po_plan o18) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub19 : CXD.lems_chk LEMS (CAD.po_ops o19) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert19 : src0_cutd_cert ITR BF cp19 (CAD.po_ops o19) (CAD.po_ops2 o19) (CAD.po_plan o19) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub20 : CXD.lems_chk LEMS (CAD.po_ops o20) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert20 : src0_cutd_cert ITR BF cp20 (CAD.po_ops o20) (CAD.po_ops2 o20) (CAD.po_plan o20) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub21 : CXD.lems_chk LEMS (CAD.po_ops o21) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert21 : src0_cutd_cert ITR BF cp21 (CAD.po_ops o21) (CAD.po_ops2 o21) (CAD.po_plan o21) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub22 : CXD.lems_chk LEMS (CAD.po_ops o22) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert22 : src0_cutd_cert ITR BF cp22 (CAD.po_ops o22) (CAD.po_ops2 o22) (CAD.po_plan o22) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub23 : CXD.lems_chk LEMS (CAD.po_ops o23) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert23 : src0_cutd_cert ITR BF cp23 (CAD.po_ops o23) (CAD.po_ops2 o23) (CAD.po_plan o23) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub24 : CXD.lems_chk LEMS (CAD.po_ops o24) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert24 : src0_cutd_cert ITR BF cp24 (CAD.po_ops o24) (CAD.po_ops2 o24) (CAD.po_plan o24) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub25 : CXD.lems_chk LEMS (CAD.po_ops o25) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert25 : src0_cutd_cert ITR BF cp25 (CAD.po_ops o25) (CAD.po_ops2 o25) (CAD.po_plan o25) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub26 : CXD.lems_chk LEMS (CAD.po_ops o26) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert26 : src0_cutd_cert ITR BF cp26 (CAD.po_ops o26) (CAD.po_ops2 o26) (CAD.po_plan o26) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub27 : CXD.lems_chk LEMS (CAD.po_ops o27) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert27 : src0_cutd_cert ITR BF cp27 (CAD.po_ops o27) (CAD.po_ops2 o27) (CAD.po_plan o27) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma tags_ok : CC.tags_chk CPS TAGS NF = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma plans : LEMS_OK -> forall i c, nth_error CPS i = Some c -> CC.plan_sound RSEGS c.
Proof.
  intros HL i c H.
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub0 HL) cert0)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub1 HL) cert1)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub2 HL) cert2)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub3 HL) cert3)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub4 HL) cert4)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub5 HL) cert5)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub6 HL) cert6)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub7 HL) cert7)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub8 HL) cert8)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub9 HL) cert9)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub10 HL) cert10)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub11 HL) cert11)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub12 HL) cert12)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub13 HL) cert13)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub14 HL) cert14)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub15 HL) cert15)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub16 HL) cert16)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub17 HL) cert17)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub18 HL) cert18)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub19 HL) cert19)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub20 HL) cert20)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub21 HL) cert21)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub22 HL) cert22)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub23 HL) cert23)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub24 HL) cert24)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub25 HL) cert25)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub26 HL) cert26)|].
  destruct i as [|i]; [injection H as <-; exact (src0_cutd_plan_sound _ _ _ _ _ _ (CXD.lems_sub RSEGS LEMS _ lsub27 HL) cert27)|].
  destruct i; discriminate H.
Qed.
Lemma NF_le : forall i c, nth_error CPS i = Some c -> (NF <= CC.cp_nx c)%nat.
Proof.
  assert (X : CC.cps_all CPS (fun _ c => Nat.leb NF (CC.cp_nx c)) = true) by (vm_cast_no_check (@eq_refl bool true)).
  intros i c H. apply Nat.leb_le. exact (CC.cps_all_sound _ _ X i c H).
Qed.
