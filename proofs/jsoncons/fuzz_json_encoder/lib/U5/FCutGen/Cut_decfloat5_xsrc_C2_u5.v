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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_decfloat5_xsrc_T_u5 Cut_decfloat5_xsrc_R0p0_u5 Cut_decfloat5_xsrc_R0p1_u5 Cut_decfloat5_xsrc_R0p2_u5 Cut_decfloat5_xsrc_R0p3_u5 Cut_decfloat5_xsrc_R1p0_u5 Cut_decfloat5_xsrc_R1p1_u5 Cut_decfloat5_xsrc_R2_u5 Cut_decfloat5_xsrc_R3_u5 Cut_decfloat5_xsrc_R4_u5 Cut_decfloat5_xsrc_R5_u5 Cut_decfloat5_xsrc_R6_u5 Cut_decfloat5_xsrc_R7_u5 Cut_decfloat5_xsrc_R8_u5 Cut_decfloat5_xsrc_R9_u5 Cut_decfloat5_xsrc_R10_u5 Cut_decfloat5_xsrc_R11_u5 Cut_decfloat5_xsrc_D_u5.
Lemma lsub120 : CXD.lems_chk LEMS (CAD.po_ops o120) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert120 : src0_cutd_cert ITR BF cp120 (CAD.po_ops o120) (CAD.po_ops2 o120) (CAD.po_plan o120) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub121 : CXD.lems_chk LEMS (CAD.po_ops o121) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert121 : src0_cutd_cert ITR BF cp121 (CAD.po_ops o121) (CAD.po_ops2 o121) (CAD.po_plan o121) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub122 : CXD.lems_chk LEMS (CAD.po_ops o122) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert122 : src0_cutd_cert ITR BF cp122 (CAD.po_ops o122) (CAD.po_ops2 o122) (CAD.po_plan o122) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub123 : CXD.lems_chk LEMS (CAD.po_ops o123) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert123 : src0_cutd_cert ITR BF cp123 (CAD.po_ops o123) (CAD.po_ops2 o123) (CAD.po_plan o123) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub124 : CXD.lems_chk LEMS (CAD.po_ops o124) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert124 : src0_cutd_cert ITR BF cp124 (CAD.po_ops o124) (CAD.po_ops2 o124) (CAD.po_plan o124) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub125 : CXD.lems_chk LEMS (CAD.po_ops o125) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert125 : src0_cutd_cert ITR BF cp125 (CAD.po_ops o125) (CAD.po_ops2 o125) (CAD.po_plan o125) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub126 : CXD.lems_chk LEMS (CAD.po_ops o126) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert126 : src0_cutd_cert ITR BF cp126 (CAD.po_ops o126) (CAD.po_ops2 o126) (CAD.po_plan o126) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub127 : CXD.lems_chk LEMS (CAD.po_ops o127) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert127 : src0_cutd_cert ITR BF cp127 (CAD.po_ops o127) (CAD.po_ops2 o127) (CAD.po_plan o127) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub128 : CXD.lems_chk LEMS (CAD.po_ops o128) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert128 : src0_cutd_cert ITR BF cp128 (CAD.po_ops o128) (CAD.po_ops2 o128) (CAD.po_plan o128) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub129 : CXD.lems_chk LEMS (CAD.po_ops o129) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert129 : src0_cutd_cert ITR BF cp129 (CAD.po_ops o129) (CAD.po_ops2 o129) (CAD.po_plan o129) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub130 : CXD.lems_chk LEMS (CAD.po_ops o130) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert130 : src0_cutd_cert ITR BF cp130 (CAD.po_ops o130) (CAD.po_ops2 o130) (CAD.po_plan o130) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub131 : CXD.lems_chk LEMS (CAD.po_ops o131) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert131 : src0_cutd_cert ITR BF cp131 (CAD.po_ops o131) (CAD.po_ops2 o131) (CAD.po_plan o131) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub132 : CXD.lems_chk LEMS (CAD.po_ops o132) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert132 : src0_cutd_cert ITR BF cp132 (CAD.po_ops o132) (CAD.po_ops2 o132) (CAD.po_plan o132) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub133 : CXD.lems_chk LEMS (CAD.po_ops o133) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert133 : src0_cutd_cert ITR BF cp133 (CAD.po_ops o133) (CAD.po_ops2 o133) (CAD.po_plan o133) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub134 : CXD.lems_chk LEMS (CAD.po_ops o134) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert134 : src0_cutd_cert ITR BF cp134 (CAD.po_ops o134) (CAD.po_ops2 o134) (CAD.po_plan o134) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub135 : CXD.lems_chk LEMS (CAD.po_ops o135) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert135 : src0_cutd_cert ITR BF cp135 (CAD.po_ops o135) (CAD.po_ops2 o135) (CAD.po_plan o135) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub136 : CXD.lems_chk LEMS (CAD.po_ops o136) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert136 : src0_cutd_cert ITR BF cp136 (CAD.po_ops o136) (CAD.po_ops2 o136) (CAD.po_plan o136) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub137 : CXD.lems_chk LEMS (CAD.po_ops o137) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert137 : src0_cutd_cert ITR BF cp137 (CAD.po_ops o137) (CAD.po_ops2 o137) (CAD.po_plan o137) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub138 : CXD.lems_chk LEMS (CAD.po_ops o138) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert138 : src0_cutd_cert ITR BF cp138 (CAD.po_ops o138) (CAD.po_ops2 o138) (CAD.po_plan o138) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub139 : CXD.lems_chk LEMS (CAD.po_ops o139) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert139 : src0_cutd_cert ITR BF cp139 (CAD.po_ops o139) (CAD.po_ops2 o139) (CAD.po_plan o139) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub140 : CXD.lems_chk LEMS (CAD.po_ops o140) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert140 : src0_cutd_cert ITR BF cp140 (CAD.po_ops o140) (CAD.po_ops2 o140) (CAD.po_plan o140) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub141 : CXD.lems_chk LEMS (CAD.po_ops o141) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert141 : src0_cutd_cert ITR BF cp141 (CAD.po_ops o141) (CAD.po_ops2 o141) (CAD.po_plan o141) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub142 : CXD.lems_chk LEMS (CAD.po_ops o142) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert142 : src0_cutd_cert ITR BF cp142 (CAD.po_ops o142) (CAD.po_ops2 o142) (CAD.po_plan o142) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub143 : CXD.lems_chk LEMS (CAD.po_ops o143) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert143 : src0_cutd_cert ITR BF cp143 (CAD.po_ops o143) (CAD.po_ops2 o143) (CAD.po_plan o143) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub144 : CXD.lems_chk LEMS (CAD.po_ops o144) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert144 : src0_cutd_cert ITR BF cp144 (CAD.po_ops o144) (CAD.po_ops2 o144) (CAD.po_plan o144) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub145 : CXD.lems_chk LEMS (CAD.po_ops o145) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert145 : src0_cutd_cert ITR BF cp145 (CAD.po_ops o145) (CAD.po_ops2 o145) (CAD.po_plan o145) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub146 : CXD.lems_chk LEMS (CAD.po_ops o146) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert146 : src0_cutd_cert ITR BF cp146 (CAD.po_ops o146) (CAD.po_ops2 o146) (CAD.po_plan o146) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub147 : CXD.lems_chk LEMS (CAD.po_ops o147) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert147 : src0_cutd_cert ITR BF cp147 (CAD.po_ops o147) (CAD.po_ops2 o147) (CAD.po_plan o147) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub148 : CXD.lems_chk LEMS (CAD.po_ops o148) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert148 : src0_cutd_cert ITR BF cp148 (CAD.po_ops o148) (CAD.po_ops2 o148) (CAD.po_plan o148) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub149 : CXD.lems_chk LEMS (CAD.po_ops o149) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert149 : src0_cutd_cert ITR BF cp149 (CAD.po_ops o149) (CAD.po_ops2 o149) (CAD.po_plan o149) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub150 : CXD.lems_chk LEMS (CAD.po_ops o150) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert150 : src0_cutd_cert ITR BF cp150 (CAD.po_ops o150) (CAD.po_ops2 o150) (CAD.po_plan o150) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub151 : CXD.lems_chk LEMS (CAD.po_ops o151) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert151 : src0_cutd_cert ITR BF cp151 (CAD.po_ops o151) (CAD.po_ops2 o151) (CAD.po_plan o151) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub152 : CXD.lems_chk LEMS (CAD.po_ops o152) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert152 : src0_cutd_cert ITR BF cp152 (CAD.po_ops o152) (CAD.po_ops2 o152) (CAD.po_plan o152) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub153 : CXD.lems_chk LEMS (CAD.po_ops o153) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert153 : src0_cutd_cert ITR BF cp153 (CAD.po_ops o153) (CAD.po_ops2 o153) (CAD.po_plan o153) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub154 : CXD.lems_chk LEMS (CAD.po_ops o154) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert154 : src0_cutd_cert ITR BF cp154 (CAD.po_ops o154) (CAD.po_ops2 o154) (CAD.po_plan o154) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub155 : CXD.lems_chk LEMS (CAD.po_ops o155) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert155 : src0_cutd_cert ITR BF cp155 (CAD.po_ops o155) (CAD.po_ops2 o155) (CAD.po_plan o155) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub156 : CXD.lems_chk LEMS (CAD.po_ops o156) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert156 : src0_cutd_cert ITR BF cp156 (CAD.po_ops o156) (CAD.po_ops2 o156) (CAD.po_plan o156) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub157 : CXD.lems_chk LEMS (CAD.po_ops o157) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert157 : src0_cutd_cert ITR BF cp157 (CAD.po_ops o157) (CAD.po_ops2 o157) (CAD.po_plan o157) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub158 : CXD.lems_chk LEMS (CAD.po_ops o158) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert158 : src0_cutd_cert ITR BF cp158 (CAD.po_ops o158) (CAD.po_ops2 o158) (CAD.po_plan o158) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub159 : CXD.lems_chk LEMS (CAD.po_ops o159) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert159 : src0_cutd_cert ITR BF cp159 (CAD.po_ops o159) (CAD.po_ops2 o159) (CAD.po_plan o159) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub160 : CXD.lems_chk LEMS (CAD.po_ops o160) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert160 : src0_cutd_cert ITR BF cp160 (CAD.po_ops o160) (CAD.po_ops2 o160) (CAD.po_plan o160) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub161 : CXD.lems_chk LEMS (CAD.po_ops o161) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert161 : src0_cutd_cert ITR BF cp161 (CAD.po_ops o161) (CAD.po_ops2 o161) (CAD.po_plan o161) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub162 : CXD.lems_chk LEMS (CAD.po_ops o162) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert162 : src0_cutd_cert ITR BF cp162 (CAD.po_ops o162) (CAD.po_ops2 o162) (CAD.po_plan o162) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub163 : CXD.lems_chk LEMS (CAD.po_ops o163) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert163 : src0_cutd_cert ITR BF cp163 (CAD.po_ops o163) (CAD.po_ops2 o163) (CAD.po_plan o163) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub164 : CXD.lems_chk LEMS (CAD.po_ops o164) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert164 : src0_cutd_cert ITR BF cp164 (CAD.po_ops o164) (CAD.po_ops2 o164) (CAD.po_plan o164) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub165 : CXD.lems_chk LEMS (CAD.po_ops o165) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert165 : src0_cutd_cert ITR BF cp165 (CAD.po_ops o165) (CAD.po_ops2 o165) (CAD.po_plan o165) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub166 : CXD.lems_chk LEMS (CAD.po_ops o166) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert166 : src0_cutd_cert ITR BF cp166 (CAD.po_ops o166) (CAD.po_ops2 o166) (CAD.po_plan o166) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub167 : CXD.lems_chk LEMS (CAD.po_ops o167) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert167 : src0_cutd_cert ITR BF cp167 (CAD.po_ops o167) (CAD.po_ops2 o167) (CAD.po_plan o167) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub168 : CXD.lems_chk LEMS (CAD.po_ops o168) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert168 : src0_cutd_cert ITR BF cp168 (CAD.po_ops o168) (CAD.po_ops2 o168) (CAD.po_plan o168) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub169 : CXD.lems_chk LEMS (CAD.po_ops o169) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert169 : src0_cutd_cert ITR BF cp169 (CAD.po_ops o169) (CAD.po_ops2 o169) (CAD.po_plan o169) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub170 : CXD.lems_chk LEMS (CAD.po_ops o170) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert170 : src0_cutd_cert ITR BF cp170 (CAD.po_ops o170) (CAD.po_ops2 o170) (CAD.po_plan o170) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub171 : CXD.lems_chk LEMS (CAD.po_ops o171) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert171 : src0_cutd_cert ITR BF cp171 (CAD.po_ops o171) (CAD.po_ops2 o171) (CAD.po_plan o171) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub172 : CXD.lems_chk LEMS (CAD.po_ops o172) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert172 : src0_cutd_cert ITR BF cp172 (CAD.po_ops o172) (CAD.po_ops2 o172) (CAD.po_plan o172) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub173 : CXD.lems_chk LEMS (CAD.po_ops o173) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert173 : src0_cutd_cert ITR BF cp173 (CAD.po_ops o173) (CAD.po_ops2 o173) (CAD.po_plan o173) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub174 : CXD.lems_chk LEMS (CAD.po_ops o174) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert174 : src0_cutd_cert ITR BF cp174 (CAD.po_ops o174) (CAD.po_ops2 o174) (CAD.po_plan o174) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub175 : CXD.lems_chk LEMS (CAD.po_ops o175) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert175 : src0_cutd_cert ITR BF cp175 (CAD.po_ops o175) (CAD.po_ops2 o175) (CAD.po_plan o175) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub176 : CXD.lems_chk LEMS (CAD.po_ops o176) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert176 : src0_cutd_cert ITR BF cp176 (CAD.po_ops o176) (CAD.po_ops2 o176) (CAD.po_plan o176) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub177 : CXD.lems_chk LEMS (CAD.po_ops o177) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert177 : src0_cutd_cert ITR BF cp177 (CAD.po_ops o177) (CAD.po_ops2 o177) (CAD.po_plan o177) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub178 : CXD.lems_chk LEMS (CAD.po_ops o178) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert178 : src0_cutd_cert ITR BF cp178 (CAD.po_ops o178) (CAD.po_ops2 o178) (CAD.po_plan o178) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub179 : CXD.lems_chk LEMS (CAD.po_ops o179) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert179 : src0_cutd_cert ITR BF cp179 (CAD.po_ops o179) (CAD.po_ops2 o179) (CAD.po_plan o179) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
