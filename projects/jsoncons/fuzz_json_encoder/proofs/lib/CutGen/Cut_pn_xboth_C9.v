(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_pn_xboth_T Cut_pn_xboth_R0p0 Cut_pn_xboth_R0p1 Cut_pn_xboth_R0p2 Cut_pn_xboth_R0p3 Cut_pn_xboth_R0p4 Cut_pn_xboth_R0p5 Cut_pn_xboth_R1p0 Cut_pn_xboth_R1p1 Cut_pn_xboth_R1p2 Cut_pn_xboth_R2p0 Cut_pn_xboth_R2p1 Cut_pn_xboth_D.
Lemma cert72 : as0_cut_cert ITR BF cp72 (CA.po_ops o72) (CA.po_ops2 o72) (CA.po_plan o72) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert73 : as0_cut_cert ITR BF cp73 (CA.po_ops o73) (CA.po_ops2 o73) (CA.po_plan o73) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
