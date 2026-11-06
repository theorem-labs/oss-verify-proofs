(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainHSBoth MainItabBoth PlanFormsBoth K1BDx_8 K1BG3Sx K1BDx_10 K1BCertG3x K1BDx_9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Definition C_hi8x : class := [(QLook,4,4); (QFlen,8388608,16777215); (QRoom,8355835,16777209)].
Definition HT_hi8x : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_hi8x_201))].
Definition C_hi9x : class := [(QLook,4,4); (QFlen,16777216,33554431); (QRoom,16744443,33554425)].
Definition HT_hi9x : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_hi9x_201))].
Definition C_hi10x : class := [(QLook,4,4); (QFlen,33554432,67108863); (QRoom,33521659,67108857)].
Definition HT_hi10x : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_hi10x_201))].
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma k1p_hi8x_head_ok : segb KCm BFUELm FUELm BITm TT HS_ht8x C_hi8x HT_hi8x 2%nat (k1p_hi8x JSraw_p_hi8x_2 JSraw_p_hi8x_10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1g3_hi8x_ok : segb KCm BFUELm FUELm BITm TT HS_p_hi8x_201 C_hi8x HTG3x 3%nat (g3_hi8x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition TG_hi8x : mtree := MPre 3 g3_hi8x HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))].
Lemma TG_hi8x_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 3 HS_p_hi8x_201 C_hi8x TG_hi8x = true.
Proof.
  unfold TG_hi8x. apply (segb_tree KCm BFUELm FUELm BITm TT 2 3 HS_p_hi8x_201 C_hi8x 3 g3_hi8x HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))] eq_refl (k1g3_hi8x_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 3 HTG3x C_hi8x 301%nat (MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))) [] 3 HS_g3x eq_refl eq_refl).
  - apply (mtree_ok_class KCm BFUELm FUELm BITm TT 3%nat 3%nat HS_g3x C_hi8x C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))); [vm_compute; reflexivity | exact (payb_leaf KCm BFUELm FUELm BITm TT 3 3 HS_g3x C_G3x 3 _ eq_refl (k1g3tx_ok TT))].
  - apply mforest_ok_nil.
Qed.
Definition T_hi8x : mtree := MPre 2 (k1p_hi8x JSraw_p_hi8x_2 JSraw_p_hi8x_10) HT_hi8x [(201%nat, TG_hi8x)].
Lemma T_hi8x_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 HS_ht8x C_hi8x T_hi8x = true.
Proof.
  unfold T_hi8x. apply (segb_tree KCm BFUELm FUELm BITm TT 2 2 HS_ht8x C_hi8x 2 (k1p_hi8x JSraw_p_hi8x_2 JSraw_p_hi8x_10) HT_hi8x [(201%nat, TG_hi8x)] eq_refl (k1p_hi8x_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 HT_hi8x C_hi8x 201%nat TG_hi8x [] 3 HS_p_hi8x_201 eq_refl eq_refl TG_hi8x_ok). apply mforest_ok_nil.
Qed.
Lemma k1p_hi9x_head_ok : segb KCm BFUELm FUELm BITm TT HS_ht9x C_hi9x HT_hi9x 2%nat (k1p_hi9x JSraw_p_hi9x_2 JSraw_p_hi9x_10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1g3_hi9x_ok : segb KCm BFUELm FUELm BITm TT HS_p_hi9x_201 C_hi9x HTG3x 3%nat (g3_hi9x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition TG_hi9x : mtree := MPre 3 g3_hi9x HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))].
Lemma TG_hi9x_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 3 HS_p_hi9x_201 C_hi9x TG_hi9x = true.
Proof.
  unfold TG_hi9x. apply (segb_tree KCm BFUELm FUELm BITm TT 2 3 HS_p_hi9x_201 C_hi9x 3 g3_hi9x HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))] eq_refl (k1g3_hi9x_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 3 HTG3x C_hi9x 301%nat (MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))) [] 3 HS_g3x eq_refl eq_refl).
  - apply (mtree_ok_class KCm BFUELm FUELm BITm TT 3%nat 3%nat HS_g3x C_hi9x C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))); [vm_compute; reflexivity | exact (payb_leaf KCm BFUELm FUELm BITm TT 3 3 HS_g3x C_G3x 3 _ eq_refl (k1g3tx_ok TT))].
  - apply mforest_ok_nil.
Qed.
Definition T_hi9x : mtree := MPre 2 (k1p_hi9x JSraw_p_hi9x_2 JSraw_p_hi9x_10) HT_hi9x [(201%nat, TG_hi9x)].
Lemma T_hi9x_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 HS_ht9x C_hi9x T_hi9x = true.
Proof.
  unfold T_hi9x. apply (segb_tree KCm BFUELm FUELm BITm TT 2 2 HS_ht9x C_hi9x 2 (k1p_hi9x JSraw_p_hi9x_2 JSraw_p_hi9x_10) HT_hi9x [(201%nat, TG_hi9x)] eq_refl (k1p_hi9x_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 HT_hi9x C_hi9x 201%nat TG_hi9x [] 3 HS_p_hi9x_201 eq_refl eq_refl TG_hi9x_ok). apply mforest_ok_nil.
Qed.
Lemma k1p_hi10x_head_ok : segb KCm BFUELm FUELm BITm TT HS_ht10x C_hi10x HT_hi10x 2%nat (k1p_hi10x JSraw_p_hi10x_2 JSraw_p_hi10x_10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1g3_hi10x_ok : segb KCm BFUELm FUELm BITm TT HS_p_hi10x_201 C_hi10x HTG3x 3%nat (g3_hi10x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition TG_hi10x : mtree := MPre 3 g3_hi10x HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))].
Lemma TG_hi10x_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 3 HS_p_hi10x_201 C_hi10x TG_hi10x = true.
Proof.
  unfold TG_hi10x. apply (segb_tree KCm BFUELm FUELm BITm TT 2 3 HS_p_hi10x_201 C_hi10x 3 g3_hi10x HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))] eq_refl (k1g3_hi10x_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 3 HTG3x C_hi10x 301%nat (MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))) [] 3 HS_g3x eq_refl eq_refl).
  - apply (mtree_ok_class KCm BFUELm FUELm BITm TT 3%nat 3%nat HS_g3x C_hi10x C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))); [vm_compute; reflexivity | exact (payb_leaf KCm BFUELm FUELm BITm TT 3 3 HS_g3x C_G3x 3 _ eq_refl (k1g3tx_ok TT))].
  - apply mforest_ok_nil.
Qed.
Definition T_hi10x : mtree := MPre 2 (k1p_hi10x JSraw_p_hi10x_2 JSraw_p_hi10x_10) HT_hi10x [(201%nat, TG_hi10x)].
Lemma T_hi10x_ok : mtree_ok KCm BFUELm FUELm BITm TT 2 2 HS_ht10x C_hi10x T_hi10x = true.
Proof.
  unfold T_hi10x. apply (segb_tree KCm BFUELm FUELm BITm TT 2 2 HS_ht10x C_hi10x 2 (k1p_hi10x JSraw_p_hi10x_2 JSraw_p_hi10x_10) HT_hi10x [(201%nat, TG_hi10x)] eq_refl (k1p_hi10x_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm BITm TT 2 HT_hi10x C_hi10x 201%nat TG_hi10x [] 3 HS_p_hi10x_201 eq_refl eq_refl TG_hi10x_ok). apply mforest_ok_nil.
Qed.
End TTS.
