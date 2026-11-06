(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSums ParseSums2 ParseSums2X ParseSomeKn.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX SmallKnX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_psome_xsrcw_T Cut_psome_xsrcw_R0 Cut_psome_xsrcw_R1p0 Cut_psome_xsrcw_R1p1 Cut_psome_xsrcw_R1p2 Cut_psome_xsrcw_R1p3 Cut_psome_xsrcw_R1p4 Cut_psome_xsrcw_R2 Cut_psome_xsrcw_R3 Cut_psome_xsrcw_D.
Lemma cert200 : src0_cut_cert ITR BF cp200 (CA.po_ops o200) (CA.po_ops2 o200) (CA.po_plan o200) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert201 : src0_cut_cert ITR BF cp201 (CA.po_ops o201) (CA.po_ops2 o201) (CA.po_plan o201) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
