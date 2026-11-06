(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_psome_casan_T Cut_psome_casan_R0p0 Cut_psome_casan_R0p1 Cut_psome_casan_R0p2 Cut_psome_casan_R0p3 Cut_psome_casan_R1p0 Cut_psome_casan_R1p1 Cut_psome_casan_R1p2 Cut_psome_casan_R1p3 Cut_psome_casan_R1p4 Cut_psome_casan_R1p5 Cut_psome_casan_R1p6 Cut_psome_casan_R1p7 Cut_psome_casan_R1p8 Cut_psome_casan_R1p9 Cut_psome_casan_R1p10 Cut_psome_casan_R1p11 Cut_psome_casan_R1p12 Cut_psome_casan_R1p13 Cut_psome_casan_R1p14 Cut_psome_casan_R1p15 Cut_psome_casan_R1p16 Cut_psome_casan_R2p0 Cut_psome_casan_R2p1 Cut_psome_casan_R2p2 Cut_psome_casan_R2p3 Cut_psome_casan_R2p4 Cut_psome_casan_R2p5 Cut_psome_casan_R3p0 Cut_psome_casan_R3p1 Cut_psome_casan_D.
Lemma cert130 : as0_cut_cert ITR BF cp130 (CA.po_ops o130) (CA.po_ops2 o130) (CA.po_plan o130) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert131 : as0_cut_cert ITR BF cp131 (CA.po_ops o131) (CA.po_ops2 o131) (CA.po_plan o131) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert132 : as0_cut_cert ITR BF cp132 (CA.po_ops o132) (CA.po_ops2 o132) (CA.po_plan o132) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert133 : as0_cut_cert ITR BF cp133 (CA.po_ops o133) (CA.po_ops2 o133) (CA.po_plan o133) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert134 : as0_cut_cert ITR BF cp134 (CA.po_ops o134) (CA.po_ops2 o134) (CA.po_plan o134) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert135 : as0_cut_cert ITR BF cp135 (CA.po_ops o135) (CA.po_ops2 o135) (CA.po_plan o135) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert136 : as0_cut_cert ITR BF cp136 (CA.po_ops o136) (CA.po_ops2 o136) (CA.po_plan o136) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert137 : as0_cut_cert ITR BF cp137 (CA.po_ops o137) (CA.po_ops2 o137) (CA.po_plan o137) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert138 : as0_cut_cert ITR BF cp138 (CA.po_ops o138) (CA.po_ops2 o138) (CA.po_plan o138) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert139 : as0_cut_cert ITR BF cp139 (CA.po_ops o139) (CA.po_ops2 o139) (CA.po_plan o139) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
