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
Lemma cert76 : as0_cut_cert ITR BF cp76 (CA.po_ops o76) (CA.po_ops2 o76) (CA.po_plan o76) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert77 : as0_cut_cert ITR BF cp77 (CA.po_ops o77) (CA.po_ops2 o77) (CA.po_plan o77) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert78 : as0_cut_cert ITR BF cp78 (CA.po_ops o78) (CA.po_ops2 o78) (CA.po_plan o78) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert79 : as0_cut_cert ITR BF cp79 (CA.po_ops o79) (CA.po_ops2 o79) (CA.po_plan o79) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
