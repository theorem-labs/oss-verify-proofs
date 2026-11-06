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
Lemma cert250 : as0_cut_cert ITR BF cp250 (CA.po_ops o250) (CA.po_ops2 o250) (CA.po_plan o250) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert251 : as0_cut_cert ITR BF cp251 (CA.po_ops o251) (CA.po_ops2 o251) (CA.po_plan o251) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert252 : as0_cut_cert ITR BF cp252 (CA.po_ops o252) (CA.po_ops2 o252) (CA.po_plan o252) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert253 : as0_cut_cert ITR BF cp253 (CA.po_ops o253) (CA.po_ops2 o253) (CA.po_plan o253) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert254 : as0_cut_cert ITR BF cp254 (CA.po_ops o254) (CA.po_ops2 o254) (CA.po_plan o254) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert255 : as0_cut_cert ITR BF cp255 (CA.po_ops o255) (CA.po_ops2 o255) (CA.po_plan o255) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert256 : as0_cut_cert ITR BF cp256 (CA.po_ops o256) (CA.po_ops2 o256) (CA.po_plan o256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert257 : as0_cut_cert ITR BF cp257 (CA.po_ops o257) (CA.po_ops2 o257) (CA.po_plan o257) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert258 : as0_cut_cert ITR BF cp258 (CA.po_ops o258) (CA.po_ops2 o258) (CA.po_plan o258) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert259 : as0_cut_cert ITR BF cp259 (CA.po_ops o259) (CA.po_ops2 o259) (CA.po_plan o259) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
