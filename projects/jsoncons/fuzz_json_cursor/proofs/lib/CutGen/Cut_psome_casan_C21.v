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
Lemma cert210 : as0_cut_cert ITR BF cp210 (CA.po_ops o210) (CA.po_ops2 o210) (CA.po_plan o210) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert211 : as0_cut_cert ITR BF cp211 (CA.po_ops o211) (CA.po_ops2 o211) (CA.po_plan o211) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert212 : as0_cut_cert ITR BF cp212 (CA.po_ops o212) (CA.po_ops2 o212) (CA.po_plan o212) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert213 : as0_cut_cert ITR BF cp213 (CA.po_ops o213) (CA.po_ops2 o213) (CA.po_plan o213) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert214 : as0_cut_cert ITR BF cp214 (CA.po_ops o214) (CA.po_ops2 o214) (CA.po_plan o214) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert215 : as0_cut_cert ITR BF cp215 (CA.po_ops o215) (CA.po_ops2 o215) (CA.po_plan o215) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert216 : as0_cut_cert ITR BF cp216 (CA.po_ops o216) (CA.po_ops2 o216) (CA.po_plan o216) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert217 : as0_cut_cert ITR BF cp217 (CA.po_ops o217) (CA.po_ops2 o217) (CA.po_plan o217) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert218 : as0_cut_cert ITR BF cp218 (CA.po_ops o218) (CA.po_ops2 o218) (CA.po_plan o218) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert219 : as0_cut_cert ITR BF cp219 (CA.po_ops o219) (CA.po_ops2 o219) (CA.po_plan o219) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
