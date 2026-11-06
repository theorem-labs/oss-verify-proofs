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
Lemma cert80 : as0_cut_cert ITR BF cp80 (CA.po_ops o80) (CA.po_ops2 o80) (CA.po_plan o80) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert81 : as0_cut_cert ITR BF cp81 (CA.po_ops o81) (CA.po_ops2 o81) (CA.po_plan o81) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert82 : as0_cut_cert ITR BF cp82 (CA.po_ops o82) (CA.po_ops2 o82) (CA.po_plan o82) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert83 : as0_cut_cert ITR BF cp83 (CA.po_ops o83) (CA.po_ops2 o83) (CA.po_plan o83) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert84 : as0_cut_cert ITR BF cp84 (CA.po_ops o84) (CA.po_ops2 o84) (CA.po_plan o84) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert85 : as0_cut_cert ITR BF cp85 (CA.po_ops o85) (CA.po_ops2 o85) (CA.po_plan o85) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert86 : as0_cut_cert ITR BF cp86 (CA.po_ops o86) (CA.po_ops2 o86) (CA.po_plan o86) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert87 : as0_cut_cert ITR BF cp87 (CA.po_ops o87) (CA.po_ops2 o87) (CA.po_plan o87) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert88 : as0_cut_cert ITR BF cp88 (CA.po_ops o88) (CA.po_ops2 o88) (CA.po_plan o88) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert89 : as0_cut_cert ITR BF cp89 (CA.po_ops o89) (CA.po_ops2 o89) (CA.po_plan o89) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
