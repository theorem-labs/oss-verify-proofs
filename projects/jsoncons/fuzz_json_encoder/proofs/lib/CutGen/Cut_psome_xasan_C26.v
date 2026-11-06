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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_psome_xasan_T Cut_psome_xasan_R0p0 Cut_psome_xasan_R0p1 Cut_psome_xasan_R0p2 Cut_psome_xasan_R0p3 Cut_psome_xasan_R0p4 Cut_psome_xasan_R0p5 Cut_psome_xasan_R0p6 Cut_psome_xasan_R0p7 Cut_psome_xasan_R1p0 Cut_psome_xasan_R1p1 Cut_psome_xasan_R1p2 Cut_psome_xasan_R1p3 Cut_psome_xasan_R1p4 Cut_psome_xasan_R1p5 Cut_psome_xasan_R1p6 Cut_psome_xasan_R1p7 Cut_psome_xasan_R1p8 Cut_psome_xasan_R1p9 Cut_psome_xasan_R1p10 Cut_psome_xasan_R1p11 Cut_psome_xasan_R1p12 Cut_psome_xasan_R1p13 Cut_psome_xasan_R1p14 Cut_psome_xasan_R1p15 Cut_psome_xasan_R1p16 Cut_psome_xasan_R1p17 Cut_psome_xasan_R1p18 Cut_psome_xasan_R1p19 Cut_psome_xasan_R1p20 Cut_psome_xasan_R1p21 Cut_psome_xasan_R1p22 Cut_psome_xasan_R1p23 Cut_psome_xasan_R1p24 Cut_psome_xasan_R1p25 Cut_psome_xasan_R1p26 Cut_psome_xasan_R1p27 Cut_psome_xasan_R1p28 Cut_psome_xasan_R1p29 Cut_psome_xasan_R1p30 Cut_psome_xasan_R1p31 Cut_psome_xasan_R1p32 Cut_psome_xasan_R1p33 Cut_psome_xasan_R2p0 Cut_psome_xasan_R2p1 Cut_psome_xasan_R2p2 Cut_psome_xasan_R2p3 Cut_psome_xasan_R2p4 Cut_psome_xasan_R2p5 Cut_psome_xasan_R2p6 Cut_psome_xasan_R2p7 Cut_psome_xasan_R2p8 Cut_psome_xasan_R2p9 Cut_psome_xasan_R2p10 Cut_psome_xasan_R2p11 Cut_psome_xasan_R3p0 Cut_psome_xasan_R3p1 Cut_psome_xasan_R3p2 Cut_psome_xasan_D.
Lemma cert130 : as0_cut_cert ITR BF cp130 (CA.po_ops o130) (CA.po_ops2 o130) (CA.po_plan o130) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert131 : as0_cut_cert ITR BF cp131 (CA.po_ops o131) (CA.po_ops2 o131) (CA.po_plan o131) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert132 : as0_cut_cert ITR BF cp132 (CA.po_ops o132) (CA.po_ops2 o132) (CA.po_plan o132) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert133 : as0_cut_cert ITR BF cp133 (CA.po_ops o133) (CA.po_ops2 o133) (CA.po_plan o133) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert134 : as0_cut_cert ITR BF cp134 (CA.po_ops o134) (CA.po_ops2 o134) (CA.po_plan o134) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
