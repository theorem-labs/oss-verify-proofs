(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO AsanPlanImages AsanInit AsanMainLib AsanMainDefs
  AsanMainTree AsanNodesRP AsanMainCertLib AsanMainItab StartupHSAsan AsanMainCertP5h0.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanMainCertKWS_1 AsanMainCertKWS_2 AsanMainCertKWS_3 AsanMainCertKWS_4 AsanMainCertKW_1 AsanMainCertKW_2 AsanMainCertKW_3 AsanMainCertKW_4.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanMainCertKWTree.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require AsanMainCertKWPay_1 AsanMainCertKWPay_2 AsanMainCertKWPay_2b AsanMainCertKWPay_3 AsanMainCertKWPay_4 AsanMainCertKWPay_5 AsanMainCertKWPay_6 AsanMainCertKWPay_7 AsanMainCertKWPay_8 AsanMainCertKWPay_9 AsanMainCertKWPay_10.
Definition KWT : mtree := KWT0 AsanMainCertKWPay_1.TREE_PAY_1_h0 AsanMainCertKWPay_2.TREE_PAY_2_h0 AsanMainCertKWPay_2b.TREE_PAY_2b_h0 AsanMainCertKWPay_3.TREE_PAY_3_h0 AsanMainCertKWPay_4.TREE_PAY_4_h0 AsanMainCertKWPay_5.TREE_PAY_5_h0 AsanMainCertKWPay_6.TREE_PAY_6_h0 AsanMainCertKWPay_7.TREE_PAY_7_h0 AsanMainCertKWPay_8.TREE_PAY_8_h0 AsanMainCertKWPay_9.TREE_PAY_9_h0 AsanMainCertKWPay_10.TREE_PAY_10_h0.
Lemma KW_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 pp_sP5h0_S_h0 CKW KWT = true.
Proof. exact (KW_ok0 _ AsanMainCertKWPay_1.ok_PAY_1_h0 _ AsanMainCertKWPay_2.ok_PAY_2_h0 _ AsanMainCertKWPay_2b.ok_PAY_2b_h0 _ AsanMainCertKWPay_3.ok_PAY_3_h0 _ AsanMainCertKWPay_4.ok_PAY_4_h0 _ AsanMainCertKWPay_5.ok_PAY_5_h0 _ AsanMainCertKWPay_6.ok_PAY_6_h0 _ AsanMainCertKWPay_7.ok_PAY_7_h0 _ AsanMainCertKWPay_8.ok_PAY_8_h0 _ AsanMainCertKWPay_9.ok_PAY_9_h0 _ AsanMainCertKWPay_10.ok_PAY_10_h0). Qed.
