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
Lemma cert100 : as0_cut_cert ITR BF cp100 (CA.po_ops o100) (CA.po_ops2 o100) (CA.po_plan o100) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert101 : as0_cut_cert ITR BF cp101 (CA.po_ops o101) (CA.po_ops2 o101) (CA.po_plan o101) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert102 : as0_cut_cert ITR BF cp102 (CA.po_ops o102) (CA.po_ops2 o102) (CA.po_plan o102) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert103 : as0_cut_cert ITR BF cp103 (CA.po_ops o103) (CA.po_ops2 o103) (CA.po_plan o103) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert104 : as0_cut_cert ITR BF cp104 (CA.po_ops o104) (CA.po_ops2 o104) (CA.po_plan o104) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert105 : as0_cut_cert ITR BF cp105 (CA.po_ops o105) (CA.po_ops2 o105) (CA.po_plan o105) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert106 : as0_cut_cert ITR BF cp106 (CA.po_ops o106) (CA.po_ops2 o106) (CA.po_plan o106) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert107 : as0_cut_cert ITR BF cp107 (CA.po_ops o107) (CA.po_ops2 o107) (CA.po_plan o107) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert108 : as0_cut_cert ITR BF cp108 (CA.po_ops o108) (CA.po_ops2 o108) (CA.po_plan o108) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert109 : as0_cut_cert ITR BF cp109 (CA.po_ops o109) (CA.po_ops2 o109) (CA.po_plan o109) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
