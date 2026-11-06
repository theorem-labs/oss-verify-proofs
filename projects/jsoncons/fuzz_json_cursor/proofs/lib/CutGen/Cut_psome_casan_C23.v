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
Lemma cert230 : as0_cut_cert ITR BF cp230 (CA.po_ops o230) (CA.po_ops2 o230) (CA.po_plan o230) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert231 : as0_cut_cert ITR BF cp231 (CA.po_ops o231) (CA.po_ops2 o231) (CA.po_plan o231) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert232 : as0_cut_cert ITR BF cp232 (CA.po_ops o232) (CA.po_ops2 o232) (CA.po_plan o232) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert233 : as0_cut_cert ITR BF cp233 (CA.po_ops o233) (CA.po_ops2 o233) (CA.po_plan o233) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert234 : as0_cut_cert ITR BF cp234 (CA.po_ops o234) (CA.po_ops2 o234) (CA.po_plan o234) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert235 : as0_cut_cert ITR BF cp235 (CA.po_ops o235) (CA.po_ops2 o235) (CA.po_plan o235) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert236 : as0_cut_cert ITR BF cp236 (CA.po_ops o236) (CA.po_ops2 o236) (CA.po_plan o236) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert237 : as0_cut_cert ITR BF cp237 (CA.po_ops o237) (CA.po_ops2 o237) (CA.po_plan o237) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert238 : as0_cut_cert ITR BF cp238 (CA.po_ops o238) (CA.po_ops2 o238) (CA.po_plan o238) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert239 : as0_cut_cert ITR BF cp239 (CA.po_ops o239) (CA.po_ops2 o239) (CA.po_plan o239) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
