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
Lemma lsub0 : CXD.lems_chk LEMS (CAD.po_ops o0) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert0 : src0_cutd_cert ITR BF cp0 (CAD.po_ops o0) (CAD.po_ops2 o0) (CAD.po_plan o0) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub1 : CXD.lems_chk LEMS (CAD.po_ops o1) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert1 : src0_cutd_cert ITR BF cp1 (CAD.po_ops o1) (CAD.po_ops2 o1) (CAD.po_plan o1) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub2 : CXD.lems_chk LEMS (CAD.po_ops o2) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert2 : src0_cutd_cert ITR BF cp2 (CAD.po_ops o2) (CAD.po_ops2 o2) (CAD.po_plan o2) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub3 : CXD.lems_chk LEMS (CAD.po_ops o3) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert3 : src0_cutd_cert ITR BF cp3 (CAD.po_ops o3) (CAD.po_ops2 o3) (CAD.po_plan o3) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub4 : CXD.lems_chk LEMS (CAD.po_ops o4) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert4 : src0_cutd_cert ITR BF cp4 (CAD.po_ops o4) (CAD.po_ops2 o4) (CAD.po_plan o4) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub5 : CXD.lems_chk LEMS (CAD.po_ops o5) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert5 : src0_cutd_cert ITR BF cp5 (CAD.po_ops o5) (CAD.po_ops2 o5) (CAD.po_plan o5) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub6 : CXD.lems_chk LEMS (CAD.po_ops o6) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert6 : src0_cutd_cert ITR BF cp6 (CAD.po_ops o6) (CAD.po_ops2 o6) (CAD.po_plan o6) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub7 : CXD.lems_chk LEMS (CAD.po_ops o7) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert7 : src0_cutd_cert ITR BF cp7 (CAD.po_ops o7) (CAD.po_ops2 o7) (CAD.po_plan o7) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub8 : CXD.lems_chk LEMS (CAD.po_ops o8) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert8 : src0_cutd_cert ITR BF cp8 (CAD.po_ops o8) (CAD.po_ops2 o8) (CAD.po_plan o8) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub9 : CXD.lems_chk LEMS (CAD.po_ops o9) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert9 : src0_cutd_cert ITR BF cp9 (CAD.po_ops o9) (CAD.po_ops2 o9) (CAD.po_plan o9) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub10 : CXD.lems_chk LEMS (CAD.po_ops o10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert10 : src0_cutd_cert ITR BF cp10 (CAD.po_ops o10) (CAD.po_ops2 o10) (CAD.po_plan o10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub11 : CXD.lems_chk LEMS (CAD.po_ops o11) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert11 : src0_cutd_cert ITR BF cp11 (CAD.po_ops o11) (CAD.po_ops2 o11) (CAD.po_plan o11) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub12 : CXD.lems_chk LEMS (CAD.po_ops o12) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert12 : src0_cutd_cert ITR BF cp12 (CAD.po_ops o12) (CAD.po_ops2 o12) (CAD.po_plan o12) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub13 : CXD.lems_chk LEMS (CAD.po_ops o13) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert13 : src0_cutd_cert ITR BF cp13 (CAD.po_ops o13) (CAD.po_ops2 o13) (CAD.po_plan o13) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub14 : CXD.lems_chk LEMS (CAD.po_ops o14) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert14 : src0_cutd_cert ITR BF cp14 (CAD.po_ops o14) (CAD.po_ops2 o14) (CAD.po_plan o14) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub15 : CXD.lems_chk LEMS (CAD.po_ops o15) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert15 : src0_cutd_cert ITR BF cp15 (CAD.po_ops o15) (CAD.po_ops2 o15) (CAD.po_plan o15) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub16 : CXD.lems_chk LEMS (CAD.po_ops o16) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert16 : src0_cutd_cert ITR BF cp16 (CAD.po_ops o16) (CAD.po_ops2 o16) (CAD.po_plan o16) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub17 : CXD.lems_chk LEMS (CAD.po_ops o17) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert17 : src0_cutd_cert ITR BF cp17 (CAD.po_ops o17) (CAD.po_ops2 o17) (CAD.po_plan o17) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub18 : CXD.lems_chk LEMS (CAD.po_ops o18) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert18 : src0_cutd_cert ITR BF cp18 (CAD.po_ops o18) (CAD.po_ops2 o18) (CAD.po_plan o18) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub19 : CXD.lems_chk LEMS (CAD.po_ops o19) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert19 : src0_cutd_cert ITR BF cp19 (CAD.po_ops o19) (CAD.po_ops2 o19) (CAD.po_plan o19) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub20 : CXD.lems_chk LEMS (CAD.po_ops o20) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert20 : src0_cutd_cert ITR BF cp20 (CAD.po_ops o20) (CAD.po_ops2 o20) (CAD.po_plan o20) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub21 : CXD.lems_chk LEMS (CAD.po_ops o21) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert21 : src0_cutd_cert ITR BF cp21 (CAD.po_ops o21) (CAD.po_ops2 o21) (CAD.po_plan o21) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub22 : CXD.lems_chk LEMS (CAD.po_ops o22) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert22 : src0_cutd_cert ITR BF cp22 (CAD.po_ops o22) (CAD.po_ops2 o22) (CAD.po_plan o22) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub23 : CXD.lems_chk LEMS (CAD.po_ops o23) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert23 : src0_cutd_cert ITR BF cp23 (CAD.po_ops o23) (CAD.po_ops2 o23) (CAD.po_plan o23) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub24 : CXD.lems_chk LEMS (CAD.po_ops o24) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert24 : src0_cutd_cert ITR BF cp24 (CAD.po_ops o24) (CAD.po_ops2 o24) (CAD.po_plan o24) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub25 : CXD.lems_chk LEMS (CAD.po_ops o25) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert25 : src0_cutd_cert ITR BF cp25 (CAD.po_ops o25) (CAD.po_ops2 o25) (CAD.po_plan o25) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub26 : CXD.lems_chk LEMS (CAD.po_ops o26) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert26 : src0_cutd_cert ITR BF cp26 (CAD.po_ops o26) (CAD.po_ops2 o26) (CAD.po_plan o26) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub27 : CXD.lems_chk LEMS (CAD.po_ops o27) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert27 : src0_cutd_cert ITR BF cp27 (CAD.po_ops o27) (CAD.po_ops2 o27) (CAD.po_plan o27) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub28 : CXD.lems_chk LEMS (CAD.po_ops o28) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert28 : src0_cutd_cert ITR BF cp28 (CAD.po_ops o28) (CAD.po_ops2 o28) (CAD.po_plan o28) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub29 : CXD.lems_chk LEMS (CAD.po_ops o29) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert29 : src0_cutd_cert ITR BF cp29 (CAD.po_ops o29) (CAD.po_ops2 o29) (CAD.po_plan o29) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub30 : CXD.lems_chk LEMS (CAD.po_ops o30) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert30 : src0_cutd_cert ITR BF cp30 (CAD.po_ops o30) (CAD.po_ops2 o30) (CAD.po_plan o30) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub31 : CXD.lems_chk LEMS (CAD.po_ops o31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert31 : src0_cutd_cert ITR BF cp31 (CAD.po_ops o31) (CAD.po_ops2 o31) (CAD.po_plan o31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub32 : CXD.lems_chk LEMS (CAD.po_ops o32) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert32 : src0_cutd_cert ITR BF cp32 (CAD.po_ops o32) (CAD.po_ops2 o32) (CAD.po_plan o32) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub33 : CXD.lems_chk LEMS (CAD.po_ops o33) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert33 : src0_cutd_cert ITR BF cp33 (CAD.po_ops o33) (CAD.po_ops2 o33) (CAD.po_plan o33) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub34 : CXD.lems_chk LEMS (CAD.po_ops o34) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert34 : src0_cutd_cert ITR BF cp34 (CAD.po_ops o34) (CAD.po_ops2 o34) (CAD.po_plan o34) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub35 : CXD.lems_chk LEMS (CAD.po_ops o35) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert35 : src0_cutd_cert ITR BF cp35 (CAD.po_ops o35) (CAD.po_ops2 o35) (CAD.po_plan o35) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub36 : CXD.lems_chk LEMS (CAD.po_ops o36) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert36 : src0_cutd_cert ITR BF cp36 (CAD.po_ops o36) (CAD.po_ops2 o36) (CAD.po_plan o36) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub37 : CXD.lems_chk LEMS (CAD.po_ops o37) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert37 : src0_cutd_cert ITR BF cp37 (CAD.po_ops o37) (CAD.po_ops2 o37) (CAD.po_plan o37) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub38 : CXD.lems_chk LEMS (CAD.po_ops o38) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert38 : src0_cutd_cert ITR BF cp38 (CAD.po_ops o38) (CAD.po_ops2 o38) (CAD.po_plan o38) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub39 : CXD.lems_chk LEMS (CAD.po_ops o39) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert39 : src0_cutd_cert ITR BF cp39 (CAD.po_ops o39) (CAD.po_ops2 o39) (CAD.po_plan o39) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub40 : CXD.lems_chk LEMS (CAD.po_ops o40) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert40 : src0_cutd_cert ITR BF cp40 (CAD.po_ops o40) (CAD.po_ops2 o40) (CAD.po_plan o40) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub41 : CXD.lems_chk LEMS (CAD.po_ops o41) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert41 : src0_cutd_cert ITR BF cp41 (CAD.po_ops o41) (CAD.po_ops2 o41) (CAD.po_plan o41) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub42 : CXD.lems_chk LEMS (CAD.po_ops o42) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert42 : src0_cutd_cert ITR BF cp42 (CAD.po_ops o42) (CAD.po_ops2 o42) (CAD.po_plan o42) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub43 : CXD.lems_chk LEMS (CAD.po_ops o43) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert43 : src0_cutd_cert ITR BF cp43 (CAD.po_ops o43) (CAD.po_ops2 o43) (CAD.po_plan o43) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub44 : CXD.lems_chk LEMS (CAD.po_ops o44) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert44 : src0_cutd_cert ITR BF cp44 (CAD.po_ops o44) (CAD.po_ops2 o44) (CAD.po_plan o44) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub45 : CXD.lems_chk LEMS (CAD.po_ops o45) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert45 : src0_cutd_cert ITR BF cp45 (CAD.po_ops o45) (CAD.po_ops2 o45) (CAD.po_plan o45) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub46 : CXD.lems_chk LEMS (CAD.po_ops o46) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert46 : src0_cutd_cert ITR BF cp46 (CAD.po_ops o46) (CAD.po_ops2 o46) (CAD.po_plan o46) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub47 : CXD.lems_chk LEMS (CAD.po_ops o47) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert47 : src0_cutd_cert ITR BF cp47 (CAD.po_ops o47) (CAD.po_ops2 o47) (CAD.po_plan o47) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub48 : CXD.lems_chk LEMS (CAD.po_ops o48) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert48 : src0_cutd_cert ITR BF cp48 (CAD.po_ops o48) (CAD.po_ops2 o48) (CAD.po_plan o48) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub49 : CXD.lems_chk LEMS (CAD.po_ops o49) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert49 : src0_cutd_cert ITR BF cp49 (CAD.po_ops o49) (CAD.po_ops2 o49) (CAD.po_plan o49) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub50 : CXD.lems_chk LEMS (CAD.po_ops o50) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert50 : src0_cutd_cert ITR BF cp50 (CAD.po_ops o50) (CAD.po_ops2 o50) (CAD.po_plan o50) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub51 : CXD.lems_chk LEMS (CAD.po_ops o51) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert51 : src0_cutd_cert ITR BF cp51 (CAD.po_ops o51) (CAD.po_ops2 o51) (CAD.po_plan o51) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub52 : CXD.lems_chk LEMS (CAD.po_ops o52) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert52 : src0_cutd_cert ITR BF cp52 (CAD.po_ops o52) (CAD.po_ops2 o52) (CAD.po_plan o52) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub53 : CXD.lems_chk LEMS (CAD.po_ops o53) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert53 : src0_cutd_cert ITR BF cp53 (CAD.po_ops o53) (CAD.po_ops2 o53) (CAD.po_plan o53) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub54 : CXD.lems_chk LEMS (CAD.po_ops o54) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert54 : src0_cutd_cert ITR BF cp54 (CAD.po_ops o54) (CAD.po_ops2 o54) (CAD.po_plan o54) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub55 : CXD.lems_chk LEMS (CAD.po_ops o55) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert55 : src0_cutd_cert ITR BF cp55 (CAD.po_ops o55) (CAD.po_ops2 o55) (CAD.po_plan o55) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub56 : CXD.lems_chk LEMS (CAD.po_ops o56) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert56 : src0_cutd_cert ITR BF cp56 (CAD.po_ops o56) (CAD.po_ops2 o56) (CAD.po_plan o56) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub57 : CXD.lems_chk LEMS (CAD.po_ops o57) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert57 : src0_cutd_cert ITR BF cp57 (CAD.po_ops o57) (CAD.po_ops2 o57) (CAD.po_plan o57) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub58 : CXD.lems_chk LEMS (CAD.po_ops o58) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert58 : src0_cutd_cert ITR BF cp58 (CAD.po_ops o58) (CAD.po_ops2 o58) (CAD.po_plan o58) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub59 : CXD.lems_chk LEMS (CAD.po_ops o59) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert59 : src0_cutd_cert ITR BF cp59 (CAD.po_ops o59) (CAD.po_ops2 o59) (CAD.po_plan o59) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
