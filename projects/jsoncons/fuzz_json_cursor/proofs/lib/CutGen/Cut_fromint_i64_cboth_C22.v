(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_fromint_i64_cboth_T Cut_fromint_i64_cboth_R0p0 Cut_fromint_i64_cboth_R0p1 Cut_fromint_i64_cboth_R0p2 Cut_fromint_i64_cboth_R0p3 Cut_fromint_i64_cboth_R0p4 Cut_fromint_i64_cboth_R0p5 Cut_fromint_i64_cboth_R0p6 Cut_fromint_i64_cboth_R0p7 Cut_fromint_i64_cboth_R0p8 Cut_fromint_i64_cboth_R0p9 Cut_fromint_i64_cboth_R0p10 Cut_fromint_i64_cboth_R0p11 Cut_fromint_i64_cboth_R0p12 Cut_fromint_i64_cboth_R0p13 Cut_fromint_i64_cboth_R0p14 Cut_fromint_i64_cboth_R1p0 Cut_fromint_i64_cboth_R1p1 Cut_fromint_i64_cboth_R1p2 Cut_fromint_i64_cboth_R1p3 Cut_fromint_i64_cboth_R1p4 Cut_fromint_i64_cboth_R1p5 Cut_fromint_i64_cboth_R1p6 Cut_fromint_i64_cboth_R1p7 Cut_fromint_i64_cboth_R1p8 Cut_fromint_i64_cboth_R1p9 Cut_fromint_i64_cboth_D.
Lemma cert88 : as0_cut_cert ITR BF cp88 (CA.po_ops o88) (CA.po_ops2 o88) (CA.po_plan o88) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert89 : as0_cut_cert ITR BF cp89 (CA.po_ops o89) (CA.po_ops2 o89) (CA.po_plan o89) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert90 : as0_cut_cert ITR BF cp90 (CA.po_ops o90) (CA.po_ops2 o90) (CA.po_plan o90) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert91 : as0_cut_cert ITR BF cp91 (CA.po_ops o91) (CA.po_ops2 o91) (CA.po_plan o91) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
