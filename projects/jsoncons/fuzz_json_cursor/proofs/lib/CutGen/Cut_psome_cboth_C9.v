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
Lemma cert90 : as0_cut_cert ITR BF cp90 (CA.po_ops o90) (CA.po_ops2 o90) (CA.po_plan o90) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert91 : as0_cut_cert ITR BF cp91 (CA.po_ops o91) (CA.po_ops2 o91) (CA.po_plan o91) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert92 : as0_cut_cert ITR BF cp92 (CA.po_ops o92) (CA.po_ops2 o92) (CA.po_plan o92) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert93 : as0_cut_cert ITR BF cp93 (CA.po_ops o93) (CA.po_ops2 o93) (CA.po_plan o93) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert94 : as0_cut_cert ITR BF cp94 (CA.po_ops o94) (CA.po_ops2 o94) (CA.po_plan o94) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert95 : as0_cut_cert ITR BF cp95 (CA.po_ops o95) (CA.po_ops2 o95) (CA.po_plan o95) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert96 : as0_cut_cert ITR BF cp96 (CA.po_ops o96) (CA.po_ops2 o96) (CA.po_plan o96) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert97 : as0_cut_cert ITR BF cp97 (CA.po_ops o97) (CA.po_ops2 o97) (CA.po_plan o97) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert98 : as0_cut_cert ITR BF cp98 (CA.po_ops o98) (CA.po_ops2 o98) (CA.po_plan o98) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert99 : as0_cut_cert ITR BF cp99 (CA.po_ops o99) (CA.po_ops2 o99) (CA.po_plan o99) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
