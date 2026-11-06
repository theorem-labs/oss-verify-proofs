(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO BothAsanPlanImages AsanInit AsanMainLib AsanMainHooksBoth AsanMainDefsBoth
  AsanMainTreeBoth AsanMainCertLibBoth AsanMainItabBoth StartupHSBoth CertRefl AsanMainCertRSEGh0Both AsanMainCertXJSBoth AsanMainCertXJTHIh0Both AsanMainCertXJTLOh0Both AsanMainCertXJTQBh0Both.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanMainCertBIGR1h0Both AsanMainCertBIGR2h0Both AsanMainCertBIGR3h0Both AsanMainCertBIGR4h0Both.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Definition TREE_BIGR_h0 : mtree := TREE_BIGR1_h0 (TREE_BIGR2_h0 (TREE_BIGR3_h0 TREE_BIGR4_h0)).
Lemma TREE_BIGR4_h0_lvl : lvl_shape TREE_BIGR4_h0 = LNode 1. Proof. reflexivity. Qed.
Lemma TREE_BIGR3_h0_lvl : lvl_shape (TREE_BIGR3_h0 TREE_BIGR4_h0) = LNode 1. Proof. reflexivity. Qed.
Lemma TREE_BIGR2_h0_lvl : lvl_shape (TREE_BIGR2_h0 (TREE_BIGR3_h0 TREE_BIGR4_h0)) = LNode 1. Proof. reflexivity. Qed.
Lemma TREE_BIGR_h0_lvl : lvl_shape TREE_BIGR_h0 = LNode 1. Proof. reflexivity. Qed.
Lemma ok_BIGR_h0 : mtree_ok KCm BFUELm FUELm ITmD 1 1 (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi pp_sRSEGh0r_S_h0 (esub (esub pp_sRSEGh0r_F_h0 (ELit 6)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1))) 0) (esub (esub pp_sRSEGh0r_F_h0 (ELit 6)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1))) 7) (esub (esub pp_sRSEGh0r_F_h0 (ELit 6)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1))) 8) (esub (esub pp_sRSEGh0r_F_h0 (ELit 6)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1))) 16) (esub (esub pp_sRSEGh0r_F_h0 (ELit 6)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1))) 48) (esub (esub pp_sRSEGh0r_F_h0 (ELit 6)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1))) 64) ((((((root_class 5) ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QFlen, QMIN, 65535)]) ++ [(QRoom, QMIN, 65529)]) TREE_BIGR_h0 = true.
Proof.
  unfold TREE_BIGR_h0.
  apply ok_BIGR1_h0; [exact TREE_BIGR2_h0_lvl|].
  apply ok_BIGR2_h0; [exact TREE_BIGR3_h0_lvl|].
  apply ok_BIGR3_h0; [exact TREE_BIGR4_h0_lvl|].
  exact ok_BIGR4_h0.
Qed.
