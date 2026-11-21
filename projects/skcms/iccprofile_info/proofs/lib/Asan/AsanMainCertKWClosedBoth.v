(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the certificates are stated once per CONFIG_RSEQ layout (modules R1 and R0), against hand-off, join and loop states that MainRegen's collector computes in the build from the computed start-up hand-off state, in place of the recorded hole states. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO BothAsanPlanImages AsanInit AsanMainLib AsanMainHooksBoth AsanMainDefsBoth
  AsanMainTreeBoth AsanNodesRP AsanMainCertLibBoth AsanMainItabBoth StartupHSBoth AsanMainCertP5h0Both PlanRegen MainRegenBoth.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanMainCertKWS_1Both AsanMainCertKWS_2Both AsanMainCertKWS_3Both AsanMainCertKWS_4Both AsanMainCertKW_1Both AsanMainCertKW_2Both AsanMainCertKW_3Both AsanMainCertKW_4Both.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanMainCertKWTreeBoth.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require AsanMainCertKWPay_1Both AsanMainCertKWPay_2Both AsanMainCertKWPay_2bBoth AsanMainCertKWPay_3Both AsanMainCertKWPay_4Both AsanMainCertKWPay_5Both AsanMainCertKWPay_6Both AsanMainCertKWPay_7Both AsanMainCertKWPay_8Both AsanMainCertKWPay_9Both AsanMainCertKWPay_10Both.
Module R1.
Import AsanMainCertKWPay_1Both.R1.
Import AsanMainCertKWPay_10Both.R1.
Import AsanMainCertKWPay_2Both.R1.
Import AsanMainCertKWPay_2bBoth.R1.
Import AsanMainCertKWPay_3Both.R1.
Import AsanMainCertKWPay_4Both.R1.
Import AsanMainCertKWPay_5Both.R1.
Import AsanMainCertKWPay_6Both.R1.
Import AsanMainCertKWPay_7Both.R1.
Import AsanMainCertKWPay_8Both.R1.
Import AsanMainCertKWPay_9Both.R1.
Import AsanMainCertKWTreeBoth.R1.
Import AsanMainCertKW_1Both.R1.
Import AsanMainCertKW_2Both.R1.
Import AsanMainCertKW_3Both.R1.
Import AsanMainCertKW_4Both.R1.
Import AsanMainCertP5h0Both.R1.

Definition KWT : mtree := KWT0 AsanMainCertKWPay_1Both.R1.TREE_PAY_1_h0 AsanMainCertKWPay_2Both.R1.TREE_PAY_2_h0 AsanMainCertKWPay_2bBoth.R1.TREE_PAY_2b_h0 AsanMainCertKWPay_3Both.R1.TREE_PAY_3_h0 AsanMainCertKWPay_4Both.R1.TREE_PAY_4_h0 AsanMainCertKWPay_5Both.R1.TREE_PAY_5_h0 AsanMainCertKWPay_6Both.R1.TREE_PAY_6_h0 AsanMainCertKWPay_7Both.R1.TREE_PAY_7_h0 AsanMainCertKWPay_8Both.R1.TREE_PAY_8_h0 AsanMainCertKWPay_9Both.R1.TREE_PAY_9_h0 AsanMainCertKWPay_10Both.R1.TREE_PAY_10_h0.

Lemma KW_ok : mtree_ok 1 KCm BFUELm FUELm ITmD 1 1 pp_sP5h0_S_h0 CKW KWT = true.
Proof. exact (KW_ok0 _ AsanMainCertKWPay_1Both.R1.ok_PAY_1_h0 _ AsanMainCertKWPay_2Both.R1.ok_PAY_2_h0 _ AsanMainCertKWPay_2bBoth.R1.ok_PAY_2b_h0 _ AsanMainCertKWPay_3Both.R1.ok_PAY_3_h0 _ AsanMainCertKWPay_4Both.R1.ok_PAY_4_h0 _ AsanMainCertKWPay_5Both.R1.ok_PAY_5_h0 _ AsanMainCertKWPay_6Both.R1.ok_PAY_6_h0 _ AsanMainCertKWPay_7Both.R1.ok_PAY_7_h0 _ AsanMainCertKWPay_8Both.R1.ok_PAY_8_h0 _ AsanMainCertKWPay_9Both.R1.ok_PAY_9_h0 _ AsanMainCertKWPay_10Both.R1.ok_PAY_10_h0). Qed.
End R1.
Module R0.
Import AsanMainCertKWPay_1Both.R0.
Import AsanMainCertKWPay_10Both.R0.
Import AsanMainCertKWPay_2Both.R0.
Import AsanMainCertKWPay_2bBoth.R0.
Import AsanMainCertKWPay_3Both.R0.
Import AsanMainCertKWPay_4Both.R0.
Import AsanMainCertKWPay_5Both.R0.
Import AsanMainCertKWPay_6Both.R0.
Import AsanMainCertKWPay_7Both.R0.
Import AsanMainCertKWPay_8Both.R0.
Import AsanMainCertKWPay_9Both.R0.
Import AsanMainCertKWTreeBoth.R0.
Import AsanMainCertKW_1Both.R0.
Import AsanMainCertKW_2Both.R0.
Import AsanMainCertKW_3Both.R0.
Import AsanMainCertKW_4Both.R0.
Import AsanMainCertP5h0Both.R0.

Definition KWT : mtree := KWT0 AsanMainCertKWPay_1Both.R0.TREE_PAY_1_h0 AsanMainCertKWPay_2Both.R0.TREE_PAY_2_h0 AsanMainCertKWPay_2bBoth.R0.TREE_PAY_2b_h0 AsanMainCertKWPay_3Both.R0.TREE_PAY_3_h0 AsanMainCertKWPay_4Both.R0.TREE_PAY_4_h0 AsanMainCertKWPay_5Both.R0.TREE_PAY_5_h0 AsanMainCertKWPay_6Both.R0.TREE_PAY_6_h0 AsanMainCertKWPay_7Both.R0.TREE_PAY_7_h0 AsanMainCertKWPay_8Both.R0.TREE_PAY_8_h0 AsanMainCertKWPay_9Both.R0.TREE_PAY_9_h0 AsanMainCertKWPay_10Both.R0.TREE_PAY_10_h0.

Lemma KW_ok : mtree_ok 0 KCm BFUELm FUELm ITmD 1 1 pp_sP5h0_S_h0 CKW KWT = true.
Proof. exact (KW_ok0 _ AsanMainCertKWPay_1Both.R0.ok_PAY_1_h0 _ AsanMainCertKWPay_2Both.R0.ok_PAY_2_h0 _ AsanMainCertKWPay_2bBoth.R0.ok_PAY_2b_h0 _ AsanMainCertKWPay_3Both.R0.ok_PAY_3_h0 _ AsanMainCertKWPay_4Both.R0.ok_PAY_4_h0 _ AsanMainCertKWPay_5Both.R0.ok_PAY_5_h0 _ AsanMainCertKWPay_6Both.R0.ok_PAY_6_h0 _ AsanMainCertKWPay_7Both.R0.ok_PAY_7_h0 _ AsanMainCertKWPay_8Both.R0.ok_PAY_8_h0 _ AsanMainCertKWPay_9Both.R0.ok_PAY_9_h0 _ AsanMainCertKWPay_10Both.R0.ok_PAY_10_h0). Qed.
End R0.
