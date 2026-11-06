(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainHSAsan MainItab PlanForms K1Dx_1 K1Dx_2 K1Dx_3 K1Dx_4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Definition C_sec1x : class := [(QLook,4,4); (QFlen,65536,131071); (QRoom,64513,131065)].
Definition HT_sec1x : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_sec1x_201))].
Definition C_sec2x : class := [(QLook,4,4); (QFlen,131072,262143); (QRoom,98299,262137)].
Definition HT_sec2x : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_sec2x_201))].
Definition C_sec3x : class := [(QLook,4,4); (QFlen,262144,524287); (QRoom,229371,524281)].
Definition HT_sec3x : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_sec3x_201))].
Definition C_sec4x : class := [(QLook,4,4); (QFlen,524288,1048575); (QRoom,491515,1048569)].
Definition HT_sec4x : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_sec4x_201))].
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma k1p_sec1x_head_ok : segb KCm BFUELm FUELm ITm TT HS_ht1x C_sec1x HT_sec1x 2%nat (k1p_sec1x JSraw_p_sec1x_2 JSraw_p_sec1x_10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1p_sec1x_t201_ok : payb KCm BFUELm FUELm ITm TT HS_p_sec1x_201 C_sec1x 3%nat (k1p_sec1x_tail JSraw_xj_sec1x_31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition T_sec1x : mtree := MPre 2 (k1p_sec1x JSraw_p_sec1x_2 JSraw_p_sec1x_10) HT_sec1x [(201%nat, MLeaf 3 (k1p_sec1x_tail JSraw_xj_sec1x_31))].
Lemma T_sec1x_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 HS_ht1x C_sec1x T_sec1x = true.
Proof.
  unfold T_sec1x. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 HS_ht1x C_sec1x 2 (k1p_sec1x JSraw_p_sec1x_2 JSraw_p_sec1x_10) HT_sec1x [(201%nat, MLeaf 3 (k1p_sec1x_tail JSraw_xj_sec1x_31))] eq_refl (k1p_sec1x_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_sec1x C_sec1x 201%nat (MLeaf 3 (k1p_sec1x_tail JSraw_xj_sec1x_31)) [] 3 HS_p_sec1x_201 eq_refl eq_refl (payb_leaf KCm BFUELm FUELm ITm TT 2 3 HS_p_sec1x_201 C_sec1x 3 _ eq_refl k1p_sec1x_t201_ok)).
  apply mforest_ok_nil.
Qed.
Lemma k1p_sec2x_head_ok : segb KCm BFUELm FUELm ITm TT HS_ht2x C_sec2x HT_sec2x 2%nat (k1p_sec2x JSraw_p_sec2x_2 JSraw_p_sec2x_10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1p_sec2x_t201_ok : payb KCm BFUELm FUELm ITm TT HS_p_sec2x_201 C_sec2x 3%nat (k1p_sec2x_tail JSraw_xj_sec2x_31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition T_sec2x : mtree := MPre 2 (k1p_sec2x JSraw_p_sec2x_2 JSraw_p_sec2x_10) HT_sec2x [(201%nat, MLeaf 3 (k1p_sec2x_tail JSraw_xj_sec2x_31))].
Lemma T_sec2x_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 HS_ht2x C_sec2x T_sec2x = true.
Proof.
  unfold T_sec2x. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 HS_ht2x C_sec2x 2 (k1p_sec2x JSraw_p_sec2x_2 JSraw_p_sec2x_10) HT_sec2x [(201%nat, MLeaf 3 (k1p_sec2x_tail JSraw_xj_sec2x_31))] eq_refl (k1p_sec2x_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_sec2x C_sec2x 201%nat (MLeaf 3 (k1p_sec2x_tail JSraw_xj_sec2x_31)) [] 3 HS_p_sec2x_201 eq_refl eq_refl (payb_leaf KCm BFUELm FUELm ITm TT 2 3 HS_p_sec2x_201 C_sec2x 3 _ eq_refl k1p_sec2x_t201_ok)).
  apply mforest_ok_nil.
Qed.
Lemma k1p_sec3x_head_ok : segb KCm BFUELm FUELm ITm TT HS_ht3x C_sec3x HT_sec3x 2%nat (k1p_sec3x JSraw_p_sec3x_2 JSraw_p_sec3x_10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1p_sec3x_t201_ok : payb KCm BFUELm FUELm ITm TT HS_p_sec3x_201 C_sec3x 3%nat (k1p_sec3x_tail JSraw_xj_sec3x_31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition T_sec3x : mtree := MPre 2 (k1p_sec3x JSraw_p_sec3x_2 JSraw_p_sec3x_10) HT_sec3x [(201%nat, MLeaf 3 (k1p_sec3x_tail JSraw_xj_sec3x_31))].
Lemma T_sec3x_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 HS_ht3x C_sec3x T_sec3x = true.
Proof.
  unfold T_sec3x. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 HS_ht3x C_sec3x 2 (k1p_sec3x JSraw_p_sec3x_2 JSraw_p_sec3x_10) HT_sec3x [(201%nat, MLeaf 3 (k1p_sec3x_tail JSraw_xj_sec3x_31))] eq_refl (k1p_sec3x_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_sec3x C_sec3x 201%nat (MLeaf 3 (k1p_sec3x_tail JSraw_xj_sec3x_31)) [] 3 HS_p_sec3x_201 eq_refl eq_refl (payb_leaf KCm BFUELm FUELm ITm TT 2 3 HS_p_sec3x_201 C_sec3x 3 _ eq_refl k1p_sec3x_t201_ok)).
  apply mforest_ok_nil.
Qed.
Lemma k1p_sec4x_head_ok : segb KCm BFUELm FUELm ITm TT HS_ht4x C_sec4x HT_sec4x 2%nat (k1p_sec4x JSraw_p_sec4x_2 JSraw_p_sec4x_10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1p_sec4x_t201_ok : payb KCm BFUELm FUELm ITm TT HS_p_sec4x_201 C_sec4x 3%nat (k1p_sec4x_tail JSraw_xj_sec4x_31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition T_sec4x : mtree := MPre 2 (k1p_sec4x JSraw_p_sec4x_2 JSraw_p_sec4x_10) HT_sec4x [(201%nat, MLeaf 3 (k1p_sec4x_tail JSraw_xj_sec4x_31))].
Lemma T_sec4x_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 HS_ht4x C_sec4x T_sec4x = true.
Proof.
  unfold T_sec4x. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 HS_ht4x C_sec4x 2 (k1p_sec4x JSraw_p_sec4x_2 JSraw_p_sec4x_10) HT_sec4x [(201%nat, MLeaf 3 (k1p_sec4x_tail JSraw_xj_sec4x_31))] eq_refl (k1p_sec4x_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_sec4x C_sec4x 201%nat (MLeaf 3 (k1p_sec4x_tail JSraw_xj_sec4x_31)) [] 3 HS_p_sec4x_201 eq_refl eq_refl (payb_leaf KCm BFUELm FUELm ITm TT 2 3 HS_p_sec4x_201 C_sec4x 3 _ eq_refl k1p_sec4x_t201_ok)).
  apply mforest_ok_nil.
Qed.
End TTS.
