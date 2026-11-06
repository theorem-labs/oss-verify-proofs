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
Lemma cert260 : as0_cut_cert ITR BF cp260 (CA.po_ops o260) (CA.po_ops2 o260) (CA.po_plan o260) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert261 : as0_cut_cert ITR BF cp261 (CA.po_ops o261) (CA.po_ops2 o261) (CA.po_plan o261) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert262 : as0_cut_cert ITR BF cp262 (CA.po_ops o262) (CA.po_ops2 o262) (CA.po_plan o262) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert263 : as0_cut_cert ITR BF cp263 (CA.po_ops o263) (CA.po_ops2 o263) (CA.po_plan o263) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert264 : as0_cut_cert ITR BF cp264 (CA.po_ops o264) (CA.po_ops2 o264) (CA.po_plan o264) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert265 : as0_cut_cert ITR BF cp265 (CA.po_ops o265) (CA.po_ops2 o265) (CA.po_plan o265) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert266 : as0_cut_cert ITR BF cp266 (CA.po_ops o266) (CA.po_ops2 o266) (CA.po_plan o266) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert267 : as0_cut_cert ITR BF cp267 (CA.po_ops o267) (CA.po_ops2 o267) (CA.po_plan o267) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert268 : as0_cut_cert ITR BF cp268 (CA.po_ops o268) (CA.po_ops2 o268) (CA.po_plan o268) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert269 : as0_cut_cert ITR BF cp269 (CA.po_ops o269) (CA.po_ops2 o269) (CA.po_plan o269) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
