(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums3C_u.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_ps_csrc_T_u Cut_ps_csrc_R0_u Cut_ps_csrc_R1p0_u Cut_ps_csrc_R1p1_u Cut_ps_csrc_R2_u Cut_ps_csrc_R3_u Cut_ps_csrc_R4_u Cut_ps_csrc_D_u.
Lemma cert40 : src0_cut_cert ITR BF cp40 (CA.po_ops o40) (CA.po_ops2 o40) (CA.po_plan o40) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert41 : src0_cut_cert ITR BF cp41 (CA.po_ops o41) (CA.po_ops2 o41) (CA.po_plan o41) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert42 : src0_cut_cert ITR BF cp42 (CA.po_ops o42) (CA.po_ops2 o42) (CA.po_plan o42) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert43 : src0_cut_cert ITR BF cp43 (CA.po_ops o43) (CA.po_ops2 o43) (CA.po_plan o43) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert44 : src0_cut_cert ITR BF cp44 (CA.po_ops o44) (CA.po_ops2 o44) (CA.po_plan o44) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert45 : src0_cut_cert ITR BF cp45 (CA.po_ops o45) (CA.po_ops2 o45) (CA.po_plan o45) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert46 : src0_cut_cert ITR BF cp46 (CA.po_ops o46) (CA.po_ops2 o46) (CA.po_plan o46) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert47 : src0_cut_cert ITR BF cp47 (CA.po_ops o47) (CA.po_ops2 o47) (CA.po_plan o47) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert48 : src0_cut_cert ITR BF cp48 (CA.po_ops o48) (CA.po_ops2 o48) (CA.po_plan o48) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert49 : src0_cut_cert ITR BF cp49 (CA.po_ops o49) (CA.po_ops2 o49) (CA.po_plan o49) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert50 : src0_cut_cert ITR BF cp50 (CA.po_ops o50) (CA.po_ops2 o50) (CA.po_plan o50) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert51 : src0_cut_cert ITR BF cp51 (CA.po_ops o51) (CA.po_ops2 o51) (CA.po_plan o51) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert52 : src0_cut_cert ITR BF cp52 (CA.po_ops o52) (CA.po_ops2 o52) (CA.po_plan o52) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert53 : src0_cut_cert ITR BF cp53 (CA.po_ops o53) (CA.po_ops2 o53) (CA.po_plan o53) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert54 : src0_cut_cert ITR BF cp54 (CA.po_ops o54) (CA.po_ops2 o54) (CA.po_plan o54) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert55 : src0_cut_cert ITR BF cp55 (CA.po_ops o55) (CA.po_ops2 o55) (CA.po_plan o55) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert56 : src0_cut_cert ITR BF cp56 (CA.po_ops o56) (CA.po_ops2 o56) (CA.po_plan o56) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert57 : src0_cut_cert ITR BF cp57 (CA.po_ops o57) (CA.po_ops2 o57) (CA.po_plan o57) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert58 : src0_cut_cert ITR BF cp58 (CA.po_ops o58) (CA.po_ops2 o58) (CA.po_plan o58) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert59 : src0_cut_cert ITR BF cp59 (CA.po_ops o59) (CA.po_ops2 o59) (CA.po_plan o59) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert60 : src0_cut_cert ITR BF cp60 (CA.po_ops o60) (CA.po_ops2 o60) (CA.po_plan o60) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert61 : src0_cut_cert ITR BF cp61 (CA.po_ops o61) (CA.po_ops2 o61) (CA.po_plan o61) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert62 : src0_cut_cert ITR BF cp62 (CA.po_ops o62) (CA.po_ops2 o62) (CA.po_plan o62) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert63 : src0_cut_cert ITR BF cp63 (CA.po_ops o63) (CA.po_ops2 o63) (CA.po_plan o63) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert64 : src0_cut_cert ITR BF cp64 (CA.po_ops o64) (CA.po_ops2 o64) (CA.po_plan o64) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert65 : src0_cut_cert ITR BF cp65 (CA.po_ops o65) (CA.po_ops2 o65) (CA.po_plan o65) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert66 : src0_cut_cert ITR BF cp66 (CA.po_ops o66) (CA.po_ops2 o66) (CA.po_plan o66) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert67 : src0_cut_cert ITR BF cp67 (CA.po_ops o67) (CA.po_ops2 o67) (CA.po_plan o67) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert68 : src0_cut_cert ITR BF cp68 (CA.po_ops o68) (CA.po_ops2 o68) (CA.po_plan o68) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert69 : src0_cut_cert ITR BF cp69 (CA.po_ops o69) (CA.po_ops2 o69) (CA.po_plan o69) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert70 : src0_cut_cert ITR BF cp70 (CA.po_ops o70) (CA.po_ops2 o70) (CA.po_plan o70) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert71 : src0_cut_cert ITR BF cp71 (CA.po_ops o71) (CA.po_ops2 o71) (CA.po_plan o71) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert72 : src0_cut_cert ITR BF cp72 (CA.po_ops o72) (CA.po_ops2 o72) (CA.po_plan o72) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert73 : src0_cut_cert ITR BF cp73 (CA.po_ops o73) (CA.po_ops2 o73) (CA.po_plan o73) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert74 : src0_cut_cert ITR BF cp74 (CA.po_ops o74) (CA.po_ops2 o74) (CA.po_plan o74) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert75 : src0_cut_cert ITR BF cp75 (CA.po_ops o75) (CA.po_ops2 o75) (CA.po_plan o75) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert76 : src0_cut_cert ITR BF cp76 (CA.po_ops o76) (CA.po_ops2 o76) (CA.po_plan o76) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert77 : src0_cut_cert ITR BF cp77 (CA.po_ops o77) (CA.po_ops2 o77) (CA.po_plan o77) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert78 : src0_cut_cert ITR BF cp78 (CA.po_ops o78) (CA.po_ops2 o78) (CA.po_plan o78) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert79 : src0_cut_cert ITR BF cp79 (CA.po_ops o79) (CA.po_ops2 o79) (CA.po_plan o79) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
