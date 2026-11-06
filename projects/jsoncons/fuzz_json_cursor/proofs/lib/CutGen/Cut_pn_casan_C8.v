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
Lemma cert64 : as0_cut_cert ITR BF cp64 (CA.po_ops o64) (CA.po_ops2 o64) (CA.po_plan o64) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert65 : as0_cut_cert ITR BF cp65 (CA.po_ops o65) (CA.po_ops2 o65) (CA.po_plan o65) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert66 : as0_cut_cert ITR BF cp66 (CA.po_ops o66) (CA.po_ops2 o66) (CA.po_plan o66) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert67 : as0_cut_cert ITR BF cp67 (CA.po_ops o67) (CA.po_ops2 o67) (CA.po_plan o67) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert68 : as0_cut_cert ITR BF cp68 (CA.po_ops o68) (CA.po_ops2 o68) (CA.po_plan o68) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert69 : as0_cut_cert ITR BF cp69 (CA.po_ops o69) (CA.po_ops2 o69) (CA.po_plan o69) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert70 : as0_cut_cert ITR BF cp70 (CA.po_ops o70) (CA.po_ops2 o70) (CA.po_plan o70) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert71 : as0_cut_cert ITR BF cp71 (CA.po_ops o71) (CA.po_ops2 o71) (CA.po_plan o71) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
