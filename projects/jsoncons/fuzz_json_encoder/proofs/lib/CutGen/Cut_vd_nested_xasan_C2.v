(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vd_nested_xasan_T Cut_vd_nested_xasan_R0 Cut_vd_nested_xasan_R1 Cut_vd_nested_xasan_R2 Cut_vd_nested_xasan_R3 Cut_vd_nested_xasan_R4 Cut_vd_nested_xasan_R5 Cut_vd_nested_xasan_R6 Cut_vd_nested_xasan_R7 Cut_vd_nested_xasan_R8 Cut_vd_nested_xasan_R9 Cut_vd_nested_xasan_R10 Cut_vd_nested_xasan_R11 Cut_vd_nested_xasan_D.
Lemma cert16 : as0_cut_cert ITR BF cp16 (CA.po_ops o16) (CA.po_ops2 o16) (CA.po_plan o16) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert17 : as0_cut_cert ITR BF cp17 (CA.po_ops o17) (CA.po_ops2 o17) (CA.po_plan o17) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert18 : as0_cut_cert ITR BF cp18 (CA.po_ops o18) (CA.po_ops2 o18) (CA.po_plan o18) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert19 : as0_cut_cert ITR BF cp19 (CA.po_ops o19) (CA.po_ops2 o19) (CA.po_plan o19) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert20 : as0_cut_cert ITR BF cp20 (CA.po_ops o20) (CA.po_ops2 o20) (CA.po_plan o20) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert21 : as0_cut_cert ITR BF cp21 (CA.po_ops o21) (CA.po_ops2 o21) (CA.po_plan o21) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert22 : as0_cut_cert ITR BF cp22 (CA.po_ops o22) (CA.po_ops2 o22) (CA.po_plan o22) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert23 : as0_cut_cert ITR BF cp23 (CA.po_ops o23) (CA.po_ops2 o23) (CA.po_plan o23) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
