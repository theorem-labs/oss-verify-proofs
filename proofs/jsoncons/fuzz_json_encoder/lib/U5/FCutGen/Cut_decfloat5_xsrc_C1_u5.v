(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_decfloat5_xsrc_T_u5 Cut_decfloat5_xsrc_R0p0_u5 Cut_decfloat5_xsrc_R0p1_u5 Cut_decfloat5_xsrc_R0p2_u5 Cut_decfloat5_xsrc_R0p3_u5 Cut_decfloat5_xsrc_R1p0_u5 Cut_decfloat5_xsrc_R1p1_u5 Cut_decfloat5_xsrc_R2_u5 Cut_decfloat5_xsrc_R3_u5 Cut_decfloat5_xsrc_R4_u5 Cut_decfloat5_xsrc_R5_u5 Cut_decfloat5_xsrc_R6_u5 Cut_decfloat5_xsrc_R7_u5 Cut_decfloat5_xsrc_R8_u5 Cut_decfloat5_xsrc_R9_u5 Cut_decfloat5_xsrc_R10_u5 Cut_decfloat5_xsrc_R11_u5 Cut_decfloat5_xsrc_D_u5.
Lemma lsub60 : CXD.lems_chk LEMS (CAD.po_ops o60) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert60 : src0_cutd_cert ITR BF cp60 (CAD.po_ops o60) (CAD.po_ops2 o60) (CAD.po_plan o60) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub61 : CXD.lems_chk LEMS (CAD.po_ops o61) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert61 : src0_cutd_cert ITR BF cp61 (CAD.po_ops o61) (CAD.po_ops2 o61) (CAD.po_plan o61) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub62 : CXD.lems_chk LEMS (CAD.po_ops o62) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert62 : src0_cutd_cert ITR BF cp62 (CAD.po_ops o62) (CAD.po_ops2 o62) (CAD.po_plan o62) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub63 : CXD.lems_chk LEMS (CAD.po_ops o63) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert63 : src0_cutd_cert ITR BF cp63 (CAD.po_ops o63) (CAD.po_ops2 o63) (CAD.po_plan o63) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub64 : CXD.lems_chk LEMS (CAD.po_ops o64) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert64 : src0_cutd_cert ITR BF cp64 (CAD.po_ops o64) (CAD.po_ops2 o64) (CAD.po_plan o64) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub65 : CXD.lems_chk LEMS (CAD.po_ops o65) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert65 : src0_cutd_cert ITR BF cp65 (CAD.po_ops o65) (CAD.po_ops2 o65) (CAD.po_plan o65) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub66 : CXD.lems_chk LEMS (CAD.po_ops o66) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert66 : src0_cutd_cert ITR BF cp66 (CAD.po_ops o66) (CAD.po_ops2 o66) (CAD.po_plan o66) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub67 : CXD.lems_chk LEMS (CAD.po_ops o67) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert67 : src0_cutd_cert ITR BF cp67 (CAD.po_ops o67) (CAD.po_ops2 o67) (CAD.po_plan o67) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub68 : CXD.lems_chk LEMS (CAD.po_ops o68) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert68 : src0_cutd_cert ITR BF cp68 (CAD.po_ops o68) (CAD.po_ops2 o68) (CAD.po_plan o68) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub69 : CXD.lems_chk LEMS (CAD.po_ops o69) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert69 : src0_cutd_cert ITR BF cp69 (CAD.po_ops o69) (CAD.po_ops2 o69) (CAD.po_plan o69) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub70 : CXD.lems_chk LEMS (CAD.po_ops o70) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert70 : src0_cutd_cert ITR BF cp70 (CAD.po_ops o70) (CAD.po_ops2 o70) (CAD.po_plan o70) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub71 : CXD.lems_chk LEMS (CAD.po_ops o71) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert71 : src0_cutd_cert ITR BF cp71 (CAD.po_ops o71) (CAD.po_ops2 o71) (CAD.po_plan o71) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub72 : CXD.lems_chk LEMS (CAD.po_ops o72) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert72 : src0_cutd_cert ITR BF cp72 (CAD.po_ops o72) (CAD.po_ops2 o72) (CAD.po_plan o72) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub73 : CXD.lems_chk LEMS (CAD.po_ops o73) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert73 : src0_cutd_cert ITR BF cp73 (CAD.po_ops o73) (CAD.po_ops2 o73) (CAD.po_plan o73) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub74 : CXD.lems_chk LEMS (CAD.po_ops o74) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert74 : src0_cutd_cert ITR BF cp74 (CAD.po_ops o74) (CAD.po_ops2 o74) (CAD.po_plan o74) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub75 : CXD.lems_chk LEMS (CAD.po_ops o75) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert75 : src0_cutd_cert ITR BF cp75 (CAD.po_ops o75) (CAD.po_ops2 o75) (CAD.po_plan o75) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub76 : CXD.lems_chk LEMS (CAD.po_ops o76) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert76 : src0_cutd_cert ITR BF cp76 (CAD.po_ops o76) (CAD.po_ops2 o76) (CAD.po_plan o76) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub77 : CXD.lems_chk LEMS (CAD.po_ops o77) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert77 : src0_cutd_cert ITR BF cp77 (CAD.po_ops o77) (CAD.po_ops2 o77) (CAD.po_plan o77) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub78 : CXD.lems_chk LEMS (CAD.po_ops o78) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert78 : src0_cutd_cert ITR BF cp78 (CAD.po_ops o78) (CAD.po_ops2 o78) (CAD.po_plan o78) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub79 : CXD.lems_chk LEMS (CAD.po_ops o79) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert79 : src0_cutd_cert ITR BF cp79 (CAD.po_ops o79) (CAD.po_ops2 o79) (CAD.po_plan o79) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub80 : CXD.lems_chk LEMS (CAD.po_ops o80) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert80 : src0_cutd_cert ITR BF cp80 (CAD.po_ops o80) (CAD.po_ops2 o80) (CAD.po_plan o80) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub81 : CXD.lems_chk LEMS (CAD.po_ops o81) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert81 : src0_cutd_cert ITR BF cp81 (CAD.po_ops o81) (CAD.po_ops2 o81) (CAD.po_plan o81) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub82 : CXD.lems_chk LEMS (CAD.po_ops o82) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert82 : src0_cutd_cert ITR BF cp82 (CAD.po_ops o82) (CAD.po_ops2 o82) (CAD.po_plan o82) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub83 : CXD.lems_chk LEMS (CAD.po_ops o83) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert83 : src0_cutd_cert ITR BF cp83 (CAD.po_ops o83) (CAD.po_ops2 o83) (CAD.po_plan o83) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub84 : CXD.lems_chk LEMS (CAD.po_ops o84) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert84 : src0_cutd_cert ITR BF cp84 (CAD.po_ops o84) (CAD.po_ops2 o84) (CAD.po_plan o84) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub85 : CXD.lems_chk LEMS (CAD.po_ops o85) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert85 : src0_cutd_cert ITR BF cp85 (CAD.po_ops o85) (CAD.po_ops2 o85) (CAD.po_plan o85) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub86 : CXD.lems_chk LEMS (CAD.po_ops o86) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert86 : src0_cutd_cert ITR BF cp86 (CAD.po_ops o86) (CAD.po_ops2 o86) (CAD.po_plan o86) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub87 : CXD.lems_chk LEMS (CAD.po_ops o87) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert87 : src0_cutd_cert ITR BF cp87 (CAD.po_ops o87) (CAD.po_ops2 o87) (CAD.po_plan o87) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub88 : CXD.lems_chk LEMS (CAD.po_ops o88) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert88 : src0_cutd_cert ITR BF cp88 (CAD.po_ops o88) (CAD.po_ops2 o88) (CAD.po_plan o88) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub89 : CXD.lems_chk LEMS (CAD.po_ops o89) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert89 : src0_cutd_cert ITR BF cp89 (CAD.po_ops o89) (CAD.po_ops2 o89) (CAD.po_plan o89) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub90 : CXD.lems_chk LEMS (CAD.po_ops o90) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert90 : src0_cutd_cert ITR BF cp90 (CAD.po_ops o90) (CAD.po_ops2 o90) (CAD.po_plan o90) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub91 : CXD.lems_chk LEMS (CAD.po_ops o91) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert91 : src0_cutd_cert ITR BF cp91 (CAD.po_ops o91) (CAD.po_ops2 o91) (CAD.po_plan o91) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub92 : CXD.lems_chk LEMS (CAD.po_ops o92) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert92 : src0_cutd_cert ITR BF cp92 (CAD.po_ops o92) (CAD.po_ops2 o92) (CAD.po_plan o92) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub93 : CXD.lems_chk LEMS (CAD.po_ops o93) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert93 : src0_cutd_cert ITR BF cp93 (CAD.po_ops o93) (CAD.po_ops2 o93) (CAD.po_plan o93) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub94 : CXD.lems_chk LEMS (CAD.po_ops o94) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert94 : src0_cutd_cert ITR BF cp94 (CAD.po_ops o94) (CAD.po_ops2 o94) (CAD.po_plan o94) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub95 : CXD.lems_chk LEMS (CAD.po_ops o95) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert95 : src0_cutd_cert ITR BF cp95 (CAD.po_ops o95) (CAD.po_ops2 o95) (CAD.po_plan o95) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub96 : CXD.lems_chk LEMS (CAD.po_ops o96) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert96 : src0_cutd_cert ITR BF cp96 (CAD.po_ops o96) (CAD.po_ops2 o96) (CAD.po_plan o96) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub97 : CXD.lems_chk LEMS (CAD.po_ops o97) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert97 : src0_cutd_cert ITR BF cp97 (CAD.po_ops o97) (CAD.po_ops2 o97) (CAD.po_plan o97) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub98 : CXD.lems_chk LEMS (CAD.po_ops o98) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert98 : src0_cutd_cert ITR BF cp98 (CAD.po_ops o98) (CAD.po_ops2 o98) (CAD.po_plan o98) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub99 : CXD.lems_chk LEMS (CAD.po_ops o99) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert99 : src0_cutd_cert ITR BF cp99 (CAD.po_ops o99) (CAD.po_ops2 o99) (CAD.po_plan o99) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub100 : CXD.lems_chk LEMS (CAD.po_ops o100) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert100 : src0_cutd_cert ITR BF cp100 (CAD.po_ops o100) (CAD.po_ops2 o100) (CAD.po_plan o100) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub101 : CXD.lems_chk LEMS (CAD.po_ops o101) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert101 : src0_cutd_cert ITR BF cp101 (CAD.po_ops o101) (CAD.po_ops2 o101) (CAD.po_plan o101) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub102 : CXD.lems_chk LEMS (CAD.po_ops o102) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert102 : src0_cutd_cert ITR BF cp102 (CAD.po_ops o102) (CAD.po_ops2 o102) (CAD.po_plan o102) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub103 : CXD.lems_chk LEMS (CAD.po_ops o103) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert103 : src0_cutd_cert ITR BF cp103 (CAD.po_ops o103) (CAD.po_ops2 o103) (CAD.po_plan o103) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub104 : CXD.lems_chk LEMS (CAD.po_ops o104) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert104 : src0_cutd_cert ITR BF cp104 (CAD.po_ops o104) (CAD.po_ops2 o104) (CAD.po_plan o104) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub105 : CXD.lems_chk LEMS (CAD.po_ops o105) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert105 : src0_cutd_cert ITR BF cp105 (CAD.po_ops o105) (CAD.po_ops2 o105) (CAD.po_plan o105) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub106 : CXD.lems_chk LEMS (CAD.po_ops o106) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert106 : src0_cutd_cert ITR BF cp106 (CAD.po_ops o106) (CAD.po_ops2 o106) (CAD.po_plan o106) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub107 : CXD.lems_chk LEMS (CAD.po_ops o107) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert107 : src0_cutd_cert ITR BF cp107 (CAD.po_ops o107) (CAD.po_ops2 o107) (CAD.po_plan o107) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub108 : CXD.lems_chk LEMS (CAD.po_ops o108) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert108 : src0_cutd_cert ITR BF cp108 (CAD.po_ops o108) (CAD.po_ops2 o108) (CAD.po_plan o108) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub109 : CXD.lems_chk LEMS (CAD.po_ops o109) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert109 : src0_cutd_cert ITR BF cp109 (CAD.po_ops o109) (CAD.po_ops2 o109) (CAD.po_plan o109) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub110 : CXD.lems_chk LEMS (CAD.po_ops o110) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert110 : src0_cutd_cert ITR BF cp110 (CAD.po_ops o110) (CAD.po_ops2 o110) (CAD.po_plan o110) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub111 : CXD.lems_chk LEMS (CAD.po_ops o111) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert111 : src0_cutd_cert ITR BF cp111 (CAD.po_ops o111) (CAD.po_ops2 o111) (CAD.po_plan o111) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub112 : CXD.lems_chk LEMS (CAD.po_ops o112) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert112 : src0_cutd_cert ITR BF cp112 (CAD.po_ops o112) (CAD.po_ops2 o112) (CAD.po_plan o112) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub113 : CXD.lems_chk LEMS (CAD.po_ops o113) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert113 : src0_cutd_cert ITR BF cp113 (CAD.po_ops o113) (CAD.po_ops2 o113) (CAD.po_plan o113) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub114 : CXD.lems_chk LEMS (CAD.po_ops o114) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert114 : src0_cutd_cert ITR BF cp114 (CAD.po_ops o114) (CAD.po_ops2 o114) (CAD.po_plan o114) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub115 : CXD.lems_chk LEMS (CAD.po_ops o115) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert115 : src0_cutd_cert ITR BF cp115 (CAD.po_ops o115) (CAD.po_ops2 o115) (CAD.po_plan o115) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub116 : CXD.lems_chk LEMS (CAD.po_ops o116) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert116 : src0_cutd_cert ITR BF cp116 (CAD.po_ops o116) (CAD.po_ops2 o116) (CAD.po_plan o116) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub117 : CXD.lems_chk LEMS (CAD.po_ops o117) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert117 : src0_cutd_cert ITR BF cp117 (CAD.po_ops o117) (CAD.po_ops2 o117) (CAD.po_plan o117) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub118 : CXD.lems_chk LEMS (CAD.po_ops o118) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert118 : src0_cutd_cert ITR BF cp118 (CAD.po_ops o118) (CAD.po_ops2 o118) (CAD.po_plan o118) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub119 : CXD.lems_chk LEMS (CAD.po_ops o119) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert119 : src0_cutd_cert ITR BF cp119 (CAD.po_ops o119) (CAD.po_ops2 o119) (CAD.po_plan o119) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
