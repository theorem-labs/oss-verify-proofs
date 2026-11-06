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
Lemma cert50 : as0_cut_cert ITR BF cp50 (CA.po_ops o50) (CA.po_ops2 o50) (CA.po_plan o50) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert51 : as0_cut_cert ITR BF cp51 (CA.po_ops o51) (CA.po_ops2 o51) (CA.po_plan o51) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert52 : as0_cut_cert ITR BF cp52 (CA.po_ops o52) (CA.po_ops2 o52) (CA.po_plan o52) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert53 : as0_cut_cert ITR BF cp53 (CA.po_ops o53) (CA.po_ops2 o53) (CA.po_plan o53) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert54 : as0_cut_cert ITR BF cp54 (CA.po_ops o54) (CA.po_ops2 o54) (CA.po_plan o54) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert55 : as0_cut_cert ITR BF cp55 (CA.po_ops o55) (CA.po_ops2 o55) (CA.po_plan o55) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert56 : as0_cut_cert ITR BF cp56 (CA.po_ops o56) (CA.po_ops2 o56) (CA.po_plan o56) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert57 : as0_cut_cert ITR BF cp57 (CA.po_ops o57) (CA.po_ops2 o57) (CA.po_plan o57) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert58 : as0_cut_cert ITR BF cp58 (CA.po_ops o58) (CA.po_ops2 o58) (CA.po_plan o58) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert59 : as0_cut_cert ITR BF cp59 (CA.po_ops o59) (CA.po_ops2 o59) (CA.po_plan o59) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
