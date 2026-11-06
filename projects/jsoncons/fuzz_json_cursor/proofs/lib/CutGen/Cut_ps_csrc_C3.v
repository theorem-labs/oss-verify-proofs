(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm10CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSums ParseSums3C.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_ps_csrc_T Cut_ps_csrc_R0 Cut_ps_csrc_R1p0 Cut_ps_csrc_R1p1 Cut_ps_csrc_R2 Cut_ps_csrc_R3 Cut_ps_csrc_R4 Cut_ps_csrc_D.
Lemma cert120 : src0_cut_cert ITR BF cp120 (CA.po_ops o120) (CA.po_ops2 o120) (CA.po_plan o120) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert121 : src0_cut_cert ITR BF cp121 (CA.po_ops o121) (CA.po_ops2 o121) (CA.po_plan o121) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert122 : src0_cut_cert ITR BF cp122 (CA.po_ops o122) (CA.po_ops2 o122) (CA.po_plan o122) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
