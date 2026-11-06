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
Lemma cert220 : as0_cut_cert ITR BF cp220 (CA.po_ops o220) (CA.po_ops2 o220) (CA.po_plan o220) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert221 : as0_cut_cert ITR BF cp221 (CA.po_ops o221) (CA.po_ops2 o221) (CA.po_plan o221) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert222 : as0_cut_cert ITR BF cp222 (CA.po_ops o222) (CA.po_ops2 o222) (CA.po_plan o222) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert223 : as0_cut_cert ITR BF cp223 (CA.po_ops o223) (CA.po_ops2 o223) (CA.po_plan o223) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert224 : as0_cut_cert ITR BF cp224 (CA.po_ops o224) (CA.po_ops2 o224) (CA.po_plan o224) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert225 : as0_cut_cert ITR BF cp225 (CA.po_ops o225) (CA.po_ops2 o225) (CA.po_plan o225) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert226 : as0_cut_cert ITR BF cp226 (CA.po_ops o226) (CA.po_ops2 o226) (CA.po_plan o226) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert227 : as0_cut_cert ITR BF cp227 (CA.po_ops o227) (CA.po_ops2 o227) (CA.po_plan o227) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert228 : as0_cut_cert ITR BF cp228 (CA.po_ops o228) (CA.po_ops2 o228) (CA.po_plan o228) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert229 : as0_cut_cert ITR BF cp229 (CA.po_ops o229) (CA.po_ops2 o229) (CA.po_plan o229) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
