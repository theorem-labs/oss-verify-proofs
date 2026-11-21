(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the certificates are stated once per CONFIG_RSEQ layout (modules R1 and R0), against hand-off, join and loop states that MainRegen's collector computes in the build from the computed start-up hand-off state, in place of the recorded hole states. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO AsanPlanImages AsanInit AsanMainLib AsanMainDefs
  AsanMainTree AsanNodesRP AsanMainCertLib AsanMainItab StartupHSAsan AsanMainCertP5h0 PlanRegen MainRegen.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanMainCertKWS_1 AsanMainCertKWS_2 AsanMainCertKWS_3 AsanMainCertKWS_4 AsanMainCertKW_1 AsanMainCertKW_2 AsanMainCertKW_3 AsanMainCertKW_4.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanMainCertKWTree.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require AsanMainCertKWPay_1 AsanMainCertKWPay_2 AsanMainCertKWPay_2b AsanMainCertKWPay_3 AsanMainCertKWPay_4 AsanMainCertKWPay_5 AsanMainCertKWPay_6 AsanMainCertKWPay_7 AsanMainCertKWPay_8 AsanMainCertKWPay_9 AsanMainCertKWPay_10.
Module R1.
Import AsanMainCertKWPay_1.R1.
Import AsanMainCertKWPay_10.R1.
Import AsanMainCertKWPay_2.R1.
Import AsanMainCertKWPay_2b.R1.
Import AsanMainCertKWPay_3.R1.
Import AsanMainCertKWPay_4.R1.
Import AsanMainCertKWPay_5.R1.
Import AsanMainCertKWPay_6.R1.
Import AsanMainCertKWPay_7.R1.
Import AsanMainCertKWPay_8.R1.
Import AsanMainCertKWPay_9.R1.
Import AsanMainCertKWTree.R1.
Import AsanMainCertKW_1.R1.
Import AsanMainCertKW_2.R1.
Import AsanMainCertKW_3.R1.
Import AsanMainCertKW_4.R1.
Import AsanMainCertP5h0.R1.

Definition KWT : mtree := KWT0 AsanMainCertKWPay_1.R1.TREE_PAY_1_h0 AsanMainCertKWPay_2.R1.TREE_PAY_2_h0 AsanMainCertKWPay_2b.R1.TREE_PAY_2b_h0 AsanMainCertKWPay_3.R1.TREE_PAY_3_h0 AsanMainCertKWPay_4.R1.TREE_PAY_4_h0 AsanMainCertKWPay_5.R1.TREE_PAY_5_h0 AsanMainCertKWPay_6.R1.TREE_PAY_6_h0 AsanMainCertKWPay_7.R1.TREE_PAY_7_h0 AsanMainCertKWPay_8.R1.TREE_PAY_8_h0 AsanMainCertKWPay_9.R1.TREE_PAY_9_h0 AsanMainCertKWPay_10.R1.TREE_PAY_10_h0.

Lemma KW_ok : mtree_ok 1 KCm BFUELm FUELm ITmD 1 1 pp_sP5h0_S_h0 CKW KWT = true.
Proof. exact (KW_ok0 _ AsanMainCertKWPay_1.R1.ok_PAY_1_h0 _ AsanMainCertKWPay_2.R1.ok_PAY_2_h0 _ AsanMainCertKWPay_2b.R1.ok_PAY_2b_h0 _ AsanMainCertKWPay_3.R1.ok_PAY_3_h0 _ AsanMainCertKWPay_4.R1.ok_PAY_4_h0 _ AsanMainCertKWPay_5.R1.ok_PAY_5_h0 _ AsanMainCertKWPay_6.R1.ok_PAY_6_h0 _ AsanMainCertKWPay_7.R1.ok_PAY_7_h0 _ AsanMainCertKWPay_8.R1.ok_PAY_8_h0 _ AsanMainCertKWPay_9.R1.ok_PAY_9_h0 _ AsanMainCertKWPay_10.R1.ok_PAY_10_h0). Qed.
End R1.
Module R0.
Import AsanMainCertKWPay_1.R0.
Import AsanMainCertKWPay_10.R0.
Import AsanMainCertKWPay_2.R0.
Import AsanMainCertKWPay_2b.R0.
Import AsanMainCertKWPay_3.R0.
Import AsanMainCertKWPay_4.R0.
Import AsanMainCertKWPay_5.R0.
Import AsanMainCertKWPay_6.R0.
Import AsanMainCertKWPay_7.R0.
Import AsanMainCertKWPay_8.R0.
Import AsanMainCertKWPay_9.R0.
Import AsanMainCertKWTree.R0.
Import AsanMainCertKW_1.R0.
Import AsanMainCertKW_2.R0.
Import AsanMainCertKW_3.R0.
Import AsanMainCertKW_4.R0.
Import AsanMainCertP5h0.R0.

Definition KWT : mtree := KWT0 AsanMainCertKWPay_1.R0.TREE_PAY_1_h0 AsanMainCertKWPay_2.R0.TREE_PAY_2_h0 AsanMainCertKWPay_2b.R0.TREE_PAY_2b_h0 AsanMainCertKWPay_3.R0.TREE_PAY_3_h0 AsanMainCertKWPay_4.R0.TREE_PAY_4_h0 AsanMainCertKWPay_5.R0.TREE_PAY_5_h0 AsanMainCertKWPay_6.R0.TREE_PAY_6_h0 AsanMainCertKWPay_7.R0.TREE_PAY_7_h0 AsanMainCertKWPay_8.R0.TREE_PAY_8_h0 AsanMainCertKWPay_9.R0.TREE_PAY_9_h0 AsanMainCertKWPay_10.R0.TREE_PAY_10_h0.

Lemma KW_ok : mtree_ok 0 KCm BFUELm FUELm ITmD 1 1 pp_sP5h0_S_h0 CKW KWT = true.
Proof. exact (KW_ok0 _ AsanMainCertKWPay_1.R0.ok_PAY_1_h0 _ AsanMainCertKWPay_2.R0.ok_PAY_2_h0 _ AsanMainCertKWPay_2b.R0.ok_PAY_2b_h0 _ AsanMainCertKWPay_3.R0.ok_PAY_3_h0 _ AsanMainCertKWPay_4.R0.ok_PAY_4_h0 _ AsanMainCertKWPay_5.R0.ok_PAY_5_h0 _ AsanMainCertKWPay_6.R0.ok_PAY_6_h0 _ AsanMainCertKWPay_7.R0.ok_PAY_7_h0 _ AsanMainCertKWPay_8.R0.ok_PAY_8_h0 _ AsanMainCertKWPay_9.R0.ok_PAY_9_h0 _ AsanMainCertKWPay_10.R0.ok_PAY_10_h0). Qed.
End R0.
