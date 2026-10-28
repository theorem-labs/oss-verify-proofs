(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u ParseSums2C_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import VisitSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_psome_csrc_T_u Cut_psome_csrc_R0_u Cut_psome_csrc_R1p0_u Cut_psome_csrc_R1p1_u Cut_psome_csrc_R1p2_u Cut_psome_csrc_R1p3_u Cut_psome_csrc_R1p4_u Cut_psome_csrc_R2_u Cut_psome_csrc_R3_u Cut_psome_csrc_D_u.
Lemma cert80 : src0_cut_cert ITR BF cp80 (CA.po_ops o80) (CA.po_ops2 o80) (CA.po_plan o80) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert81 : src0_cut_cert ITR BF cp81 (CA.po_ops o81) (CA.po_ops2 o81) (CA.po_plan o81) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert82 : src0_cut_cert ITR BF cp82 (CA.po_ops o82) (CA.po_ops2 o82) (CA.po_plan o82) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert83 : src0_cut_cert ITR BF cp83 (CA.po_ops o83) (CA.po_ops2 o83) (CA.po_plan o83) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert84 : src0_cut_cert ITR BF cp84 (CA.po_ops o84) (CA.po_ops2 o84) (CA.po_plan o84) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert85 : src0_cut_cert ITR BF cp85 (CA.po_ops o85) (CA.po_ops2 o85) (CA.po_plan o85) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert86 : src0_cut_cert ITR BF cp86 (CA.po_ops o86) (CA.po_ops2 o86) (CA.po_plan o86) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert87 : src0_cut_cert ITR BF cp87 (CA.po_ops o87) (CA.po_ops2 o87) (CA.po_plan o87) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert88 : src0_cut_cert ITR BF cp88 (CA.po_ops o88) (CA.po_ops2 o88) (CA.po_plan o88) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert89 : src0_cut_cert ITR BF cp89 (CA.po_ops o89) (CA.po_ops2 o89) (CA.po_plan o89) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert90 : src0_cut_cert ITR BF cp90 (CA.po_ops o90) (CA.po_ops2 o90) (CA.po_plan o90) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert91 : src0_cut_cert ITR BF cp91 (CA.po_ops o91) (CA.po_ops2 o91) (CA.po_plan o91) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert92 : src0_cut_cert ITR BF cp92 (CA.po_ops o92) (CA.po_ops2 o92) (CA.po_plan o92) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert93 : src0_cut_cert ITR BF cp93 (CA.po_ops o93) (CA.po_ops2 o93) (CA.po_plan o93) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert94 : src0_cut_cert ITR BF cp94 (CA.po_ops o94) (CA.po_ops2 o94) (CA.po_plan o94) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert95 : src0_cut_cert ITR BF cp95 (CA.po_ops o95) (CA.po_ops2 o95) (CA.po_plan o95) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert96 : src0_cut_cert ITR BF cp96 (CA.po_ops o96) (CA.po_ops2 o96) (CA.po_plan o96) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert97 : src0_cut_cert ITR BF cp97 (CA.po_ops o97) (CA.po_ops2 o97) (CA.po_plan o97) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert98 : src0_cut_cert ITR BF cp98 (CA.po_ops o98) (CA.po_ops2 o98) (CA.po_plan o98) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert99 : src0_cut_cert ITR BF cp99 (CA.po_ops o99) (CA.po_ops2 o99) (CA.po_plan o99) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert100 : src0_cut_cert ITR BF cp100 (CA.po_ops o100) (CA.po_ops2 o100) (CA.po_plan o100) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert101 : src0_cut_cert ITR BF cp101 (CA.po_ops o101) (CA.po_ops2 o101) (CA.po_plan o101) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert102 : src0_cut_cert ITR BF cp102 (CA.po_ops o102) (CA.po_ops2 o102) (CA.po_plan o102) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert103 : src0_cut_cert ITR BF cp103 (CA.po_ops o103) (CA.po_ops2 o103) (CA.po_plan o103) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert104 : src0_cut_cert ITR BF cp104 (CA.po_ops o104) (CA.po_ops2 o104) (CA.po_plan o104) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert105 : src0_cut_cert ITR BF cp105 (CA.po_ops o105) (CA.po_ops2 o105) (CA.po_plan o105) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert106 : src0_cut_cert ITR BF cp106 (CA.po_ops o106) (CA.po_ops2 o106) (CA.po_plan o106) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert107 : src0_cut_cert ITR BF cp107 (CA.po_ops o107) (CA.po_ops2 o107) (CA.po_plan o107) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert108 : src0_cut_cert ITR BF cp108 (CA.po_ops o108) (CA.po_ops2 o108) (CA.po_plan o108) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert109 : src0_cut_cert ITR BF cp109 (CA.po_ops o109) (CA.po_ops2 o109) (CA.po_plan o109) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert110 : src0_cut_cert ITR BF cp110 (CA.po_ops o110) (CA.po_ops2 o110) (CA.po_plan o110) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert111 : src0_cut_cert ITR BF cp111 (CA.po_ops o111) (CA.po_ops2 o111) (CA.po_plan o111) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert112 : src0_cut_cert ITR BF cp112 (CA.po_ops o112) (CA.po_ops2 o112) (CA.po_plan o112) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert113 : src0_cut_cert ITR BF cp113 (CA.po_ops o113) (CA.po_ops2 o113) (CA.po_plan o113) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert114 : src0_cut_cert ITR BF cp114 (CA.po_ops o114) (CA.po_ops2 o114) (CA.po_plan o114) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert115 : src0_cut_cert ITR BF cp115 (CA.po_ops o115) (CA.po_ops2 o115) (CA.po_plan o115) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert116 : src0_cut_cert ITR BF cp116 (CA.po_ops o116) (CA.po_ops2 o116) (CA.po_plan o116) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert117 : src0_cut_cert ITR BF cp117 (CA.po_ops o117) (CA.po_ops2 o117) (CA.po_plan o117) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert118 : src0_cut_cert ITR BF cp118 (CA.po_ops o118) (CA.po_ops2 o118) (CA.po_plan o118) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert119 : src0_cut_cert ITR BF cp119 (CA.po_ops o119) (CA.po_ops2 o119) (CA.po_plan o119) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
