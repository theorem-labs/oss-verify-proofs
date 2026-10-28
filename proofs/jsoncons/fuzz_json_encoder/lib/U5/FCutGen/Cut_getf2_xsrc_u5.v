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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_getf2_xsrc_T_u5 Cut_getf2_xsrc_R0_u5.
Definition cp0 : CC.cutpoint := Eval vm_compute in mkcp t0 o0.
Definition cp1 : CC.cutpoint := Eval vm_compute in mkcp t1 o1.
Definition cp2 : CC.cutpoint := Eval vm_compute in mkcp t2 o2.
Definition cp3 : CC.cutpoint := Eval vm_compute in mkcp t3 o3.
Definition cp4 : CC.cutpoint := Eval vm_compute in mkcp t4 o4.
Definition CPS : list CC.cutpoint := [cp0; cp1; cp2; cp3; cp4].
Definition TAGS : list (list CC.tag) := Eval vm_compute in [map snd (CAD.po_leaves o0); map snd (CAD.po_leaves o1); map snd (CAD.po_leaves o2); map snd (CAD.po_leaves o3); map snd (CAD.po_leaves o4)].
Definition BLS : list CAD.blocks := [BL0; BL1; BL2; BL3; BL4].
Definition HDECL := Cut_getf2_xsrc_T_u5.HDECL.
(* [comment removed for export] *)
Definition RETS : list (nat * nat * nat * Z) := [].
(* [comment removed for export] *)
Definition LEMS : list (list kentry * kentry) := Eval vm_compute in CXD.lem_dedup (CXD.lemmas_of (CAD.po_ops o0) ++ CXD.lemmas_of (CAD.po_ops o1) ++ CXD.lemmas_of (CAD.po_ops o2) ++ CXD.lemmas_of (CAD.po_ops o3) ++ CXD.lemmas_of (CAD.po_ops o4)).
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
  destruct i; discriminate H.
Qed.
Lemma NF_le : forall i c, nth_error CPS i = Some c -> (NF <= CC.cp_nx c)%nat.
Proof.
  assert (X : CC.cps_all CPS (fun _ c => Nat.leb NF (CC.cp_nx c)) = true) by (vm_cast_no_check (@eq_refl bool true)).
  intros i c H. apply Nat.leb_le. exact (CC.cps_all_sound _ _ X i c H).
Qed.
