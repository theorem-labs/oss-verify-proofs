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
Lemma cert190 : as0_cut_cert ITR BF cp190 (CA.po_ops o190) (CA.po_ops2 o190) (CA.po_plan o190) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert191 : as0_cut_cert ITR BF cp191 (CA.po_ops o191) (CA.po_ops2 o191) (CA.po_plan o191) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert192 : as0_cut_cert ITR BF cp192 (CA.po_ops o192) (CA.po_ops2 o192) (CA.po_plan o192) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert193 : as0_cut_cert ITR BF cp193 (CA.po_ops o193) (CA.po_ops2 o193) (CA.po_plan o193) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert194 : as0_cut_cert ITR BF cp194 (CA.po_ops o194) (CA.po_ops2 o194) (CA.po_plan o194) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert195 : as0_cut_cert ITR BF cp195 (CA.po_ops o195) (CA.po_ops2 o195) (CA.po_plan o195) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert196 : as0_cut_cert ITR BF cp196 (CA.po_ops o196) (CA.po_ops2 o196) (CA.po_plan o196) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert197 : as0_cut_cert ITR BF cp197 (CA.po_ops o197) (CA.po_ops2 o197) (CA.po_plan o197) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert198 : as0_cut_cert ITR BF cp198 (CA.po_ops o198) (CA.po_ops2 o198) (CA.po_plan o198) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert199 : as0_cut_cert ITR BF cp199 (CA.po_ops o199) (CA.po_ops2 o199) (CA.po_plan o199) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
