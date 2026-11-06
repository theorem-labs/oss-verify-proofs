(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_psome_cboth_T Cut_psome_cboth_R0p0 Cut_psome_cboth_R0p1 Cut_psome_cboth_R0p2 Cut_psome_cboth_R0p3 Cut_psome_cboth_R1p0 Cut_psome_cboth_R1p1 Cut_psome_cboth_R1p2 Cut_psome_cboth_R1p3 Cut_psome_cboth_R1p4 Cut_psome_cboth_R1p5 Cut_psome_cboth_R1p6 Cut_psome_cboth_R1p7 Cut_psome_cboth_R1p8 Cut_psome_cboth_R1p9 Cut_psome_cboth_R1p10 Cut_psome_cboth_R1p11 Cut_psome_cboth_R1p12 Cut_psome_cboth_R1p13 Cut_psome_cboth_R1p14 Cut_psome_cboth_R1p15 Cut_psome_cboth_R1p16 Cut_psome_cboth_R2p0 Cut_psome_cboth_R2p1 Cut_psome_cboth_R2p2 Cut_psome_cboth_R2p3 Cut_psome_cboth_R2p4 Cut_psome_cboth_R2p5 Cut_psome_cboth_R3p0 Cut_psome_cboth_R3p1 Cut_psome_cboth_D.
Lemma cert240 : as0_cut_cert ITR BF cp240 (CA.po_ops o240) (CA.po_ops2 o240) (CA.po_plan o240) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert241 : as0_cut_cert ITR BF cp241 (CA.po_ops o241) (CA.po_ops2 o241) (CA.po_plan o241) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert242 : as0_cut_cert ITR BF cp242 (CA.po_ops o242) (CA.po_ops2 o242) (CA.po_plan o242) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert243 : as0_cut_cert ITR BF cp243 (CA.po_ops o243) (CA.po_ops2 o243) (CA.po_plan o243) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert244 : as0_cut_cert ITR BF cp244 (CA.po_ops o244) (CA.po_ops2 o244) (CA.po_plan o244) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert245 : as0_cut_cert ITR BF cp245 (CA.po_ops o245) (CA.po_ops2 o245) (CA.po_plan o245) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert246 : as0_cut_cert ITR BF cp246 (CA.po_ops o246) (CA.po_ops2 o246) (CA.po_plan o246) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert247 : as0_cut_cert ITR BF cp247 (CA.po_ops o247) (CA.po_ops2 o247) (CA.po_plan o247) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert248 : as0_cut_cert ITR BF cp248 (CA.po_ops o248) (CA.po_ops2 o248) (CA.po_plan o248) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert249 : as0_cut_cert ITR BF cp249 (CA.po_ops o249) (CA.po_ops2 o249) (CA.po_plan o249) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
