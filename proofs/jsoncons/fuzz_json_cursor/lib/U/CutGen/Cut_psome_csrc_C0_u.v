(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u ParseSums2C_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import VisitSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_psome_csrc_T_u Cut_psome_csrc_R0_u Cut_psome_csrc_R1p0_u Cut_psome_csrc_R1p1_u Cut_psome_csrc_R1p2_u Cut_psome_csrc_R1p3_u Cut_psome_csrc_R1p4_u Cut_psome_csrc_R2_u Cut_psome_csrc_R3_u Cut_psome_csrc_D_u.
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
