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
Lemma lsub300 : CXD.lems_chk LEMS (CAD.po_ops o300) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert300 : src0_cutd_cert ITR BF cp300 (CAD.po_ops o300) (CAD.po_ops2 o300) (CAD.po_plan o300) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub301 : CXD.lems_chk LEMS (CAD.po_ops o301) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert301 : src0_cutd_cert ITR BF cp301 (CAD.po_ops o301) (CAD.po_ops2 o301) (CAD.po_plan o301) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub302 : CXD.lems_chk LEMS (CAD.po_ops o302) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert302 : src0_cutd_cert ITR BF cp302 (CAD.po_ops o302) (CAD.po_ops2 o302) (CAD.po_plan o302) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub303 : CXD.lems_chk LEMS (CAD.po_ops o303) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert303 : src0_cutd_cert ITR BF cp303 (CAD.po_ops o303) (CAD.po_ops2 o303) (CAD.po_plan o303) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub304 : CXD.lems_chk LEMS (CAD.po_ops o304) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert304 : src0_cutd_cert ITR BF cp304 (CAD.po_ops o304) (CAD.po_ops2 o304) (CAD.po_plan o304) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub305 : CXD.lems_chk LEMS (CAD.po_ops o305) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert305 : src0_cutd_cert ITR BF cp305 (CAD.po_ops o305) (CAD.po_ops2 o305) (CAD.po_plan o305) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub306 : CXD.lems_chk LEMS (CAD.po_ops o306) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert306 : src0_cutd_cert ITR BF cp306 (CAD.po_ops o306) (CAD.po_ops2 o306) (CAD.po_plan o306) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub307 : CXD.lems_chk LEMS (CAD.po_ops o307) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert307 : src0_cutd_cert ITR BF cp307 (CAD.po_ops o307) (CAD.po_ops2 o307) (CAD.po_plan o307) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub308 : CXD.lems_chk LEMS (CAD.po_ops o308) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert308 : src0_cutd_cert ITR BF cp308 (CAD.po_ops o308) (CAD.po_ops2 o308) (CAD.po_plan o308) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub309 : CXD.lems_chk LEMS (CAD.po_ops o309) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert309 : src0_cutd_cert ITR BF cp309 (CAD.po_ops o309) (CAD.po_ops2 o309) (CAD.po_plan o309) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub310 : CXD.lems_chk LEMS (CAD.po_ops o310) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert310 : src0_cutd_cert ITR BF cp310 (CAD.po_ops o310) (CAD.po_ops2 o310) (CAD.po_plan o310) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub311 : CXD.lems_chk LEMS (CAD.po_ops o311) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert311 : src0_cutd_cert ITR BF cp311 (CAD.po_ops o311) (CAD.po_ops2 o311) (CAD.po_plan o311) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub312 : CXD.lems_chk LEMS (CAD.po_ops o312) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert312 : src0_cutd_cert ITR BF cp312 (CAD.po_ops o312) (CAD.po_ops2 o312) (CAD.po_plan o312) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub313 : CXD.lems_chk LEMS (CAD.po_ops o313) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert313 : src0_cutd_cert ITR BF cp313 (CAD.po_ops o313) (CAD.po_ops2 o313) (CAD.po_plan o313) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub314 : CXD.lems_chk LEMS (CAD.po_ops o314) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert314 : src0_cutd_cert ITR BF cp314 (CAD.po_ops o314) (CAD.po_ops2 o314) (CAD.po_plan o314) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub315 : CXD.lems_chk LEMS (CAD.po_ops o315) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert315 : src0_cutd_cert ITR BF cp315 (CAD.po_ops o315) (CAD.po_ops2 o315) (CAD.po_plan o315) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub316 : CXD.lems_chk LEMS (CAD.po_ops o316) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert316 : src0_cutd_cert ITR BF cp316 (CAD.po_ops o316) (CAD.po_ops2 o316) (CAD.po_plan o316) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub317 : CXD.lems_chk LEMS (CAD.po_ops o317) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert317 : src0_cutd_cert ITR BF cp317 (CAD.po_ops o317) (CAD.po_ops2 o317) (CAD.po_plan o317) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub318 : CXD.lems_chk LEMS (CAD.po_ops o318) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert318 : src0_cutd_cert ITR BF cp318 (CAD.po_ops o318) (CAD.po_ops2 o318) (CAD.po_plan o318) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub319 : CXD.lems_chk LEMS (CAD.po_ops o319) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert319 : src0_cutd_cert ITR BF cp319 (CAD.po_ops o319) (CAD.po_ops2 o319) (CAD.po_plan o319) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub320 : CXD.lems_chk LEMS (CAD.po_ops o320) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert320 : src0_cutd_cert ITR BF cp320 (CAD.po_ops o320) (CAD.po_ops2 o320) (CAD.po_plan o320) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub321 : CXD.lems_chk LEMS (CAD.po_ops o321) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert321 : src0_cutd_cert ITR BF cp321 (CAD.po_ops o321) (CAD.po_ops2 o321) (CAD.po_plan o321) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub322 : CXD.lems_chk LEMS (CAD.po_ops o322) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert322 : src0_cutd_cert ITR BF cp322 (CAD.po_ops o322) (CAD.po_ops2 o322) (CAD.po_plan o322) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub323 : CXD.lems_chk LEMS (CAD.po_ops o323) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert323 : src0_cutd_cert ITR BF cp323 (CAD.po_ops o323) (CAD.po_ops2 o323) (CAD.po_plan o323) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub324 : CXD.lems_chk LEMS (CAD.po_ops o324) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert324 : src0_cutd_cert ITR BF cp324 (CAD.po_ops o324) (CAD.po_ops2 o324) (CAD.po_plan o324) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub325 : CXD.lems_chk LEMS (CAD.po_ops o325) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert325 : src0_cutd_cert ITR BF cp325 (CAD.po_ops o325) (CAD.po_ops2 o325) (CAD.po_plan o325) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub326 : CXD.lems_chk LEMS (CAD.po_ops o326) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert326 : src0_cutd_cert ITR BF cp326 (CAD.po_ops o326) (CAD.po_ops2 o326) (CAD.po_plan o326) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub327 : CXD.lems_chk LEMS (CAD.po_ops o327) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert327 : src0_cutd_cert ITR BF cp327 (CAD.po_ops o327) (CAD.po_ops2 o327) (CAD.po_plan o327) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub328 : CXD.lems_chk LEMS (CAD.po_ops o328) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert328 : src0_cutd_cert ITR BF cp328 (CAD.po_ops o328) (CAD.po_ops2 o328) (CAD.po_plan o328) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub329 : CXD.lems_chk LEMS (CAD.po_ops o329) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert329 : src0_cutd_cert ITR BF cp329 (CAD.po_ops o329) (CAD.po_ops2 o329) (CAD.po_plan o329) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub330 : CXD.lems_chk LEMS (CAD.po_ops o330) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert330 : src0_cutd_cert ITR BF cp330 (CAD.po_ops o330) (CAD.po_ops2 o330) (CAD.po_plan o330) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub331 : CXD.lems_chk LEMS (CAD.po_ops o331) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert331 : src0_cutd_cert ITR BF cp331 (CAD.po_ops o331) (CAD.po_ops2 o331) (CAD.po_plan o331) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub332 : CXD.lems_chk LEMS (CAD.po_ops o332) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert332 : src0_cutd_cert ITR BF cp332 (CAD.po_ops o332) (CAD.po_ops2 o332) (CAD.po_plan o332) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
