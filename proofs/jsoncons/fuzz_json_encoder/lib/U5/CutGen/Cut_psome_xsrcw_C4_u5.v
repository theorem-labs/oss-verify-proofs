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
Lemma cert160 : src0_cut_cert ITR BF cp160 (CA.po_ops o160) (CA.po_ops2 o160) (CA.po_plan o160) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert161 : src0_cut_cert ITR BF cp161 (CA.po_ops o161) (CA.po_ops2 o161) (CA.po_plan o161) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert162 : src0_cut_cert ITR BF cp162 (CA.po_ops o162) (CA.po_ops2 o162) (CA.po_plan o162) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert163 : src0_cut_cert ITR BF cp163 (CA.po_ops o163) (CA.po_ops2 o163) (CA.po_plan o163) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert164 : src0_cut_cert ITR BF cp164 (CA.po_ops o164) (CA.po_ops2 o164) (CA.po_plan o164) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert165 : src0_cut_cert ITR BF cp165 (CA.po_ops o165) (CA.po_ops2 o165) (CA.po_plan o165) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert166 : src0_cut_cert ITR BF cp166 (CA.po_ops o166) (CA.po_ops2 o166) (CA.po_plan o166) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert167 : src0_cut_cert ITR BF cp167 (CA.po_ops o167) (CA.po_ops2 o167) (CA.po_plan o167) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert168 : src0_cut_cert ITR BF cp168 (CA.po_ops o168) (CA.po_ops2 o168) (CA.po_plan o168) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert169 : src0_cut_cert ITR BF cp169 (CA.po_ops o169) (CA.po_ops2 o169) (CA.po_plan o169) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert170 : src0_cut_cert ITR BF cp170 (CA.po_ops o170) (CA.po_ops2 o170) (CA.po_plan o170) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert171 : src0_cut_cert ITR BF cp171 (CA.po_ops o171) (CA.po_ops2 o171) (CA.po_plan o171) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert172 : src0_cut_cert ITR BF cp172 (CA.po_ops o172) (CA.po_ops2 o172) (CA.po_plan o172) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert173 : src0_cut_cert ITR BF cp173 (CA.po_ops o173) (CA.po_ops2 o173) (CA.po_plan o173) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert174 : src0_cut_cert ITR BF cp174 (CA.po_ops o174) (CA.po_ops2 o174) (CA.po_plan o174) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert175 : src0_cut_cert ITR BF cp175 (CA.po_ops o175) (CA.po_ops2 o175) (CA.po_plan o175) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert176 : src0_cut_cert ITR BF cp176 (CA.po_ops o176) (CA.po_ops2 o176) (CA.po_plan o176) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert177 : src0_cut_cert ITR BF cp177 (CA.po_ops o177) (CA.po_ops2 o177) (CA.po_plan o177) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert178 : src0_cut_cert ITR BF cp178 (CA.po_ops o178) (CA.po_ops2 o178) (CA.po_plan o178) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert179 : src0_cut_cert ITR BF cp179 (CA.po_ops o179) (CA.po_ops2 o179) (CA.po_plan o179) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert180 : src0_cut_cert ITR BF cp180 (CA.po_ops o180) (CA.po_ops2 o180) (CA.po_plan o180) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert181 : src0_cut_cert ITR BF cp181 (CA.po_ops o181) (CA.po_ops2 o181) (CA.po_plan o181) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert182 : src0_cut_cert ITR BF cp182 (CA.po_ops o182) (CA.po_ops2 o182) (CA.po_plan o182) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert183 : src0_cut_cert ITR BF cp183 (CA.po_ops o183) (CA.po_ops2 o183) (CA.po_plan o183) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert184 : src0_cut_cert ITR BF cp184 (CA.po_ops o184) (CA.po_ops2 o184) (CA.po_plan o184) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert185 : src0_cut_cert ITR BF cp185 (CA.po_ops o185) (CA.po_ops2 o185) (CA.po_plan o185) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert186 : src0_cut_cert ITR BF cp186 (CA.po_ops o186) (CA.po_ops2 o186) (CA.po_plan o186) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert187 : src0_cut_cert ITR BF cp187 (CA.po_ops o187) (CA.po_ops2 o187) (CA.po_plan o187) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert188 : src0_cut_cert ITR BF cp188 (CA.po_ops o188) (CA.po_ops2 o188) (CA.po_plan o188) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert189 : src0_cut_cert ITR BF cp189 (CA.po_ops o189) (CA.po_ops2 o189) (CA.po_plan o189) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert190 : src0_cut_cert ITR BF cp190 (CA.po_ops o190) (CA.po_ops2 o190) (CA.po_plan o190) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert191 : src0_cut_cert ITR BF cp191 (CA.po_ops o191) (CA.po_ops2 o191) (CA.po_plan o191) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert192 : src0_cut_cert ITR BF cp192 (CA.po_ops o192) (CA.po_ops2 o192) (CA.po_plan o192) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert193 : src0_cut_cert ITR BF cp193 (CA.po_ops o193) (CA.po_ops2 o193) (CA.po_plan o193) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert194 : src0_cut_cert ITR BF cp194 (CA.po_ops o194) (CA.po_ops2 o194) (CA.po_plan o194) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert195 : src0_cut_cert ITR BF cp195 (CA.po_ops o195) (CA.po_ops2 o195) (CA.po_plan o195) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert196 : src0_cut_cert ITR BF cp196 (CA.po_ops o196) (CA.po_ops2 o196) (CA.po_plan o196) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert197 : src0_cut_cert ITR BF cp197 (CA.po_ops o197) (CA.po_ops2 o197) (CA.po_plan o197) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert198 : src0_cut_cert ITR BF cp198 (CA.po_ops o198) (CA.po_ops2 o198) (CA.po_plan o198) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert199 : src0_cut_cert ITR BF cp199 (CA.po_ops o199) (CA.po_ops2 o199) (CA.po_plan o199) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
