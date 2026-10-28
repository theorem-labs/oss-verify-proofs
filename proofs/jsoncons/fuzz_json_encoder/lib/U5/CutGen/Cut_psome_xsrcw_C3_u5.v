(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5 ParseSums2X_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX SmallKnX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_psome_xsrcw_T_u5 Cut_psome_xsrcw_R0_u5 Cut_psome_xsrcw_R1p0_u5 Cut_psome_xsrcw_R1p1_u5 Cut_psome_xsrcw_R1p2_u5 Cut_psome_xsrcw_R1p3_u5 Cut_psome_xsrcw_R1p4_u5 Cut_psome_xsrcw_R2_u5 Cut_psome_xsrcw_R3_u5 Cut_psome_xsrcw_D_u5.
Lemma cert120 : src0_cut_cert ITR BF cp120 (CA.po_ops o120) (CA.po_ops2 o120) (CA.po_plan o120) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert121 : src0_cut_cert ITR BF cp121 (CA.po_ops o121) (CA.po_ops2 o121) (CA.po_plan o121) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert122 : src0_cut_cert ITR BF cp122 (CA.po_ops o122) (CA.po_ops2 o122) (CA.po_plan o122) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert123 : src0_cut_cert ITR BF cp123 (CA.po_ops o123) (CA.po_ops2 o123) (CA.po_plan o123) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert124 : src0_cut_cert ITR BF cp124 (CA.po_ops o124) (CA.po_ops2 o124) (CA.po_plan o124) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert125 : src0_cut_cert ITR BF cp125 (CA.po_ops o125) (CA.po_ops2 o125) (CA.po_plan o125) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert126 : src0_cut_cert ITR BF cp126 (CA.po_ops o126) (CA.po_ops2 o126) (CA.po_plan o126) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert127 : src0_cut_cert ITR BF cp127 (CA.po_ops o127) (CA.po_ops2 o127) (CA.po_plan o127) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert128 : src0_cut_cert ITR BF cp128 (CA.po_ops o128) (CA.po_ops2 o128) (CA.po_plan o128) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert129 : src0_cut_cert ITR BF cp129 (CA.po_ops o129) (CA.po_ops2 o129) (CA.po_plan o129) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert130 : src0_cut_cert ITR BF cp130 (CA.po_ops o130) (CA.po_ops2 o130) (CA.po_plan o130) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert131 : src0_cut_cert ITR BF cp131 (CA.po_ops o131) (CA.po_ops2 o131) (CA.po_plan o131) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert132 : src0_cut_cert ITR BF cp132 (CA.po_ops o132) (CA.po_ops2 o132) (CA.po_plan o132) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert133 : src0_cut_cert ITR BF cp133 (CA.po_ops o133) (CA.po_ops2 o133) (CA.po_plan o133) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert134 : src0_cut_cert ITR BF cp134 (CA.po_ops o134) (CA.po_ops2 o134) (CA.po_plan o134) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert135 : src0_cut_cert ITR BF cp135 (CA.po_ops o135) (CA.po_ops2 o135) (CA.po_plan o135) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert136 : src0_cut_cert ITR BF cp136 (CA.po_ops o136) (CA.po_ops2 o136) (CA.po_plan o136) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert137 : src0_cut_cert ITR BF cp137 (CA.po_ops o137) (CA.po_ops2 o137) (CA.po_plan o137) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert138 : src0_cut_cert ITR BF cp138 (CA.po_ops o138) (CA.po_ops2 o138) (CA.po_plan o138) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert139 : src0_cut_cert ITR BF cp139 (CA.po_ops o139) (CA.po_ops2 o139) (CA.po_plan o139) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert140 : src0_cut_cert ITR BF cp140 (CA.po_ops o140) (CA.po_ops2 o140) (CA.po_plan o140) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert141 : src0_cut_cert ITR BF cp141 (CA.po_ops o141) (CA.po_ops2 o141) (CA.po_plan o141) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert142 : src0_cut_cert ITR BF cp142 (CA.po_ops o142) (CA.po_ops2 o142) (CA.po_plan o142) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert143 : src0_cut_cert ITR BF cp143 (CA.po_ops o143) (CA.po_ops2 o143) (CA.po_plan o143) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert144 : src0_cut_cert ITR BF cp144 (CA.po_ops o144) (CA.po_ops2 o144) (CA.po_plan o144) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert145 : src0_cut_cert ITR BF cp145 (CA.po_ops o145) (CA.po_ops2 o145) (CA.po_plan o145) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert146 : src0_cut_cert ITR BF cp146 (CA.po_ops o146) (CA.po_ops2 o146) (CA.po_plan o146) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert147 : src0_cut_cert ITR BF cp147 (CA.po_ops o147) (CA.po_ops2 o147) (CA.po_plan o147) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert148 : src0_cut_cert ITR BF cp148 (CA.po_ops o148) (CA.po_ops2 o148) (CA.po_plan o148) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert149 : src0_cut_cert ITR BF cp149 (CA.po_ops o149) (CA.po_ops2 o149) (CA.po_plan o149) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert150 : src0_cut_cert ITR BF cp150 (CA.po_ops o150) (CA.po_ops2 o150) (CA.po_plan o150) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert151 : src0_cut_cert ITR BF cp151 (CA.po_ops o151) (CA.po_ops2 o151) (CA.po_plan o151) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert152 : src0_cut_cert ITR BF cp152 (CA.po_ops o152) (CA.po_ops2 o152) (CA.po_plan o152) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert153 : src0_cut_cert ITR BF cp153 (CA.po_ops o153) (CA.po_ops2 o153) (CA.po_plan o153) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert154 : src0_cut_cert ITR BF cp154 (CA.po_ops o154) (CA.po_ops2 o154) (CA.po_plan o154) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert155 : src0_cut_cert ITR BF cp155 (CA.po_ops o155) (CA.po_ops2 o155) (CA.po_plan o155) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert156 : src0_cut_cert ITR BF cp156 (CA.po_ops o156) (CA.po_ops2 o156) (CA.po_plan o156) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert157 : src0_cut_cert ITR BF cp157 (CA.po_ops o157) (CA.po_ops2 o157) (CA.po_plan o157) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert158 : src0_cut_cert ITR BF cp158 (CA.po_ops o158) (CA.po_ops2 o158) (CA.po_plan o158) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert159 : src0_cut_cert ITR BF cp159 (CA.po_ops o159) (CA.po_ops2 o159) (CA.po_plan o159) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
