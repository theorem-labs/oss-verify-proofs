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
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_ps_xasanw_T Cut_ps_xasanw_R0p0 Cut_ps_xasanw_R0p1 Cut_ps_xasanw_R0p2 Cut_ps_xasanw_R0p3 Cut_ps_xasanw_R1p0 Cut_ps_xasanw_R1p1 Cut_ps_xasanw_R1p2 Cut_ps_xasanw_R1p3 Cut_ps_xasanw_R1p4 Cut_ps_xasanw_R2p0 Cut_ps_xasanw_R2p1 Cut_ps_xasanw_R2p2 Cut_ps_xasanw_D.
Lemma cert48 : as0_cut_cert ITR BF cp48 (CA.po_ops o48) (CA.po_ops2 o48) (CA.po_plan o48) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert49 : as0_cut_cert ITR BF cp49 (CA.po_ops o49) (CA.po_ops2 o49) (CA.po_plan o49) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
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
