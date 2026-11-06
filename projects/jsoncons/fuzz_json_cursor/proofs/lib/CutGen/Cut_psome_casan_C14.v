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
Lemma cert140 : as0_cut_cert ITR BF cp140 (CA.po_ops o140) (CA.po_ops2 o140) (CA.po_plan o140) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert141 : as0_cut_cert ITR BF cp141 (CA.po_ops o141) (CA.po_ops2 o141) (CA.po_plan o141) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert142 : as0_cut_cert ITR BF cp142 (CA.po_ops o142) (CA.po_ops2 o142) (CA.po_plan o142) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert143 : as0_cut_cert ITR BF cp143 (CA.po_ops o143) (CA.po_ops2 o143) (CA.po_plan o143) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert144 : as0_cut_cert ITR BF cp144 (CA.po_ops o144) (CA.po_ops2 o144) (CA.po_plan o144) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert145 : as0_cut_cert ITR BF cp145 (CA.po_ops o145) (CA.po_ops2 o145) (CA.po_plan o145) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert146 : as0_cut_cert ITR BF cp146 (CA.po_ops o146) (CA.po_ops2 o146) (CA.po_plan o146) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert147 : as0_cut_cert ITR BF cp147 (CA.po_ops o147) (CA.po_ops2 o147) (CA.po_plan o147) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert148 : as0_cut_cert ITR BF cp148 (CA.po_ops o148) (CA.po_ops2 o148) (CA.po_plan o148) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert149 : as0_cut_cert ITR BF cp149 (CA.po_ops o149) (CA.po_ops2 o149) (CA.po_plan o149) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
