(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO BothAsanPlanImages AsanInit AsanMainLib AsanMainHooksBoth AsanMainDefsBoth
  AsanMainTreeBoth AsanNodesRP AsanMainCertLibBoth AsanMainItabBoth StartupHSBoth AsanMainCertP5h0Both.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanMainCertKWS_1Both AsanMainCertKWS_2Both AsanMainCertKWS_3Both AsanMainCertKWS_4Both AsanMainCertKW_1Both AsanMainCertKW_2Both AsanMainCertKW_3Both AsanMainCertKW_4Both.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanMainCertKWTreeBoth.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require AsanMainCertKWPay_1Both AsanMainCertKWPay_2Both AsanMainCertKWPay_2bBoth AsanMainCertKWPay_3Both AsanMainCertKWPay_4Both AsanMainCertKWPay_5Both AsanMainCertKWPay_6Both AsanMainCertKWPay_7Both AsanMainCertKWPay_8Both AsanMainCertKWPay_9Both AsanMainCertKWPay_10Both.
Definition KWT : mtree := KWT0 AsanMainCertKWPay_1Both.TREE_PAY_1_h0 AsanMainCertKWPay_2Both.TREE_PAY_2_h0 AsanMainCertKWPay_2bBoth.TREE_PAY_2b_h0 AsanMainCertKWPay_3Both.TREE_PAY_3_h0 AsanMainCertKWPay_4Both.TREE_PAY_4_h0 AsanMainCertKWPay_5Both.TREE_PAY_5_h0 AsanMainCertKWPay_6Both.TREE_PAY_6_h0 AsanMainCertKWPay_7Both.TREE_PAY_7_h0 AsanMainCertKWPay_8Both.TREE_PAY_8_h0 AsanMainCertKWPay_9Both.TREE_PAY_9_h0 AsanMainCertKWPay_10Both.TREE_PAY_10_h0.
Lemma KW_ok : mtree_ok KCm BFUELm FUELm ITmD 1 1 pp_sP5h0_S_h0 CKW KWT = true.
Proof. exact (KW_ok0 _ AsanMainCertKWPay_1Both.ok_PAY_1_h0 _ AsanMainCertKWPay_2Both.ok_PAY_2_h0 _ AsanMainCertKWPay_2bBoth.ok_PAY_2b_h0 _ AsanMainCertKWPay_3Both.ok_PAY_3_h0 _ AsanMainCertKWPay_4Both.ok_PAY_4_h0 _ AsanMainCertKWPay_5Both.ok_PAY_5_h0 _ AsanMainCertKWPay_6Both.ok_PAY_6_h0 _ AsanMainCertKWPay_7Both.ok_PAY_7_h0 _ AsanMainCertKWPay_8Both.ok_PAY_8_h0 _ AsanMainCertKWPay_9Both.ok_PAY_9_h0 _ AsanMainCertKWPay_10Both.ok_PAY_10_h0). Qed.
