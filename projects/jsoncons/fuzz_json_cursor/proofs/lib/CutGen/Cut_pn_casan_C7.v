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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_pn_casan_T Cut_pn_casan_R0p0 Cut_pn_casan_R0p1 Cut_pn_casan_R0p2 Cut_pn_casan_R0p3 Cut_pn_casan_R0p4 Cut_pn_casan_R0p5 Cut_pn_casan_R1p0 Cut_pn_casan_R1p1 Cut_pn_casan_R1p2 Cut_pn_casan_R2p0 Cut_pn_casan_R2p1 Cut_pn_casan_D.
Lemma cert56 : as0_cut_cert ITR BF cp56 (CA.po_ops o56) (CA.po_ops2 o56) (CA.po_plan o56) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert57 : as0_cut_cert ITR BF cp57 (CA.po_ops o57) (CA.po_ops2 o57) (CA.po_plan o57) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert58 : as0_cut_cert ITR BF cp58 (CA.po_ops o58) (CA.po_ops2 o58) (CA.po_plan o58) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert59 : as0_cut_cert ITR BF cp59 (CA.po_ops o59) (CA.po_ops2 o59) (CA.po_plan o59) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert60 : as0_cut_cert ITR BF cp60 (CA.po_ops o60) (CA.po_ops2 o60) (CA.po_plan o60) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert61 : as0_cut_cert ITR BF cp61 (CA.po_ops o61) (CA.po_ops2 o61) (CA.po_plan o61) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert62 : as0_cut_cert ITR BF cp62 (CA.po_ops o62) (CA.po_ops2 o62) (CA.po_plan o62) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert63 : as0_cut_cert ITR BF cp63 (CA.po_ops o63) (CA.po_ops2 o63) (CA.po_plan o63) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
