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
Lemma cert110 : as0_cut_cert ITR BF cp110 (CA.po_ops o110) (CA.po_ops2 o110) (CA.po_plan o110) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert111 : as0_cut_cert ITR BF cp111 (CA.po_ops o111) (CA.po_ops2 o111) (CA.po_plan o111) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert112 : as0_cut_cert ITR BF cp112 (CA.po_ops o112) (CA.po_ops2 o112) (CA.po_plan o112) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert113 : as0_cut_cert ITR BF cp113 (CA.po_ops o113) (CA.po_ops2 o113) (CA.po_plan o113) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert114 : as0_cut_cert ITR BF cp114 (CA.po_ops o114) (CA.po_ops2 o114) (CA.po_plan o114) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert115 : as0_cut_cert ITR BF cp115 (CA.po_ops o115) (CA.po_ops2 o115) (CA.po_plan o115) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert116 : as0_cut_cert ITR BF cp116 (CA.po_ops o116) (CA.po_ops2 o116) (CA.po_plan o116) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert117 : as0_cut_cert ITR BF cp117 (CA.po_ops o117) (CA.po_ops2 o117) (CA.po_plan o117) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert118 : as0_cut_cert ITR BF cp118 (CA.po_ops o118) (CA.po_ops2 o118) (CA.po_plan o118) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert119 : as0_cut_cert ITR BF cp119 (CA.po_ops o119) (CA.po_ops2 o119) (CA.po_plan o119) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
