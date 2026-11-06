(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainHSAsan MainItab PlanForms K1Dx_5 K1G3Sx K1Dx_10 K1CertG3x K1Dx_6 K1Dx_7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Definition C_hi5ax : class := [(QLook,4,4); (QFlen,1048576,2097151); (QRoom,1015803,1040384)].
Definition HT_hi5ax : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_hi5ax_201))].
Definition C_hi5bx : class := [(QLook,4,4); (QFlen,1048576,2097151); (QRoom,1040385,2097145)].
Definition HT_hi5bx : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_hi5bx_201))].
Definition C_hi6x : class := [(QLook,4,4); (QFlen,2097152,4194303); (QRoom,2064379,4194297)].
Definition HT_hi6x : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_hi6x_201))].
Definition C_hi7x : class := [(QLook,4,4); (QFlen,4194304,8388607); (QRoom,4161531,8388601)].
Definition HT_hi7x : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_hi7x_201))].
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma k1p_hi5ax_head_ok : segb KCm BFUELm FUELm ITm TT HS_ht5x C_hi5ax HT_hi5ax 2%nat (k1p_hi5ax JSraw_p_hi5ax_2 JSraw_p_hi5ax_10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1p_hi5ax_t201_ok : payb KCm BFUELm FUELm ITm TT HS_p_hi5ax_201 C_hi5ax 3%nat (k1p_hi5ax_tail JSraw_xj_hi5ax_31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition T_hi5ax : mtree := MPre 2 (k1p_hi5ax JSraw_p_hi5ax_2 JSraw_p_hi5ax_10) HT_hi5ax [(201%nat, MLeaf 3 (k1p_hi5ax_tail JSraw_xj_hi5ax_31))].
Lemma T_hi5ax_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 HS_ht5x C_hi5ax T_hi5ax = true.
Proof.
  unfold T_hi5ax. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 HS_ht5x C_hi5ax 2 (k1p_hi5ax JSraw_p_hi5ax_2 JSraw_p_hi5ax_10) HT_hi5ax [(201%nat, MLeaf 3 (k1p_hi5ax_tail JSraw_xj_hi5ax_31))] eq_refl (k1p_hi5ax_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_hi5ax C_hi5ax 201%nat (MLeaf 3 (k1p_hi5ax_tail JSraw_xj_hi5ax_31)) [] 3 HS_p_hi5ax_201 eq_refl eq_refl (payb_leaf KCm BFUELm FUELm ITm TT 2 3 HS_p_hi5ax_201 C_hi5ax 3 _ eq_refl k1p_hi5ax_t201_ok)).
  apply mforest_ok_nil.
Qed.
Lemma k1p_hi5bx_head_ok : segb KCm BFUELm FUELm ITm TT HS_ht5x C_hi5bx HT_hi5bx 2%nat (k1p_hi5bx JSraw_p_hi5bx_2 JSraw_p_hi5bx_10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1g3_hi5bx_ok : segb KCm BFUELm FUELm ITm TT HS_p_hi5bx_201 C_hi5bx HTG3x 3%nat (g3_hi5bx) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition TG_hi5bx : mtree := MPre 3 g3_hi5bx HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))].
Lemma TG_hi5bx_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 3 HS_p_hi5bx_201 C_hi5bx TG_hi5bx = true.
Proof.
  unfold TG_hi5bx. apply (segb_tree KCm BFUELm FUELm ITm TT 2 3 HS_p_hi5bx_201 C_hi5bx 3 g3_hi5bx HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))] eq_refl (k1g3_hi5bx_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 3 HTG3x C_hi5bx 301%nat (MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))) [] 3 HS_g3x eq_refl eq_refl).
  - apply (mtree_ok_class KCm BFUELm FUELm ITm TT 3%nat 3%nat HS_g3x C_hi5bx C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))); [vm_compute; reflexivity | exact (payb_leaf KCm BFUELm FUELm ITm TT 3 3 HS_g3x C_G3x 3 _ eq_refl (k1g3tx_ok TT))].
  - apply mforest_ok_nil.
Qed.
Definition T_hi5bx : mtree := MPre 2 (k1p_hi5bx JSraw_p_hi5bx_2 JSraw_p_hi5bx_10) HT_hi5bx [(201%nat, TG_hi5bx)].
Lemma T_hi5bx_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 HS_ht5x C_hi5bx T_hi5bx = true.
Proof.
  unfold T_hi5bx. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 HS_ht5x C_hi5bx 2 (k1p_hi5bx JSraw_p_hi5bx_2 JSraw_p_hi5bx_10) HT_hi5bx [(201%nat, TG_hi5bx)] eq_refl (k1p_hi5bx_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_hi5bx C_hi5bx 201%nat TG_hi5bx [] 3 HS_p_hi5bx_201 eq_refl eq_refl TG_hi5bx_ok). apply mforest_ok_nil.
Qed.
Lemma k1p_hi6x_head_ok : segb KCm BFUELm FUELm ITm TT HS_ht6x C_hi6x HT_hi6x 2%nat (k1p_hi6x JSraw_p_hi6x_2 JSraw_p_hi6x_10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1g3_hi6x_ok : segb KCm BFUELm FUELm ITm TT HS_p_hi6x_201 C_hi6x HTG3x 3%nat (g3_hi6x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition TG_hi6x : mtree := MPre 3 g3_hi6x HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))].
Lemma TG_hi6x_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 3 HS_p_hi6x_201 C_hi6x TG_hi6x = true.
Proof.
  unfold TG_hi6x. apply (segb_tree KCm BFUELm FUELm ITm TT 2 3 HS_p_hi6x_201 C_hi6x 3 g3_hi6x HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))] eq_refl (k1g3_hi6x_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 3 HTG3x C_hi6x 301%nat (MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))) [] 3 HS_g3x eq_refl eq_refl).
  - apply (mtree_ok_class KCm BFUELm FUELm ITm TT 3%nat 3%nat HS_g3x C_hi6x C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))); [vm_compute; reflexivity | exact (payb_leaf KCm BFUELm FUELm ITm TT 3 3 HS_g3x C_G3x 3 _ eq_refl (k1g3tx_ok TT))].
  - apply mforest_ok_nil.
Qed.
Definition T_hi6x : mtree := MPre 2 (k1p_hi6x JSraw_p_hi6x_2 JSraw_p_hi6x_10) HT_hi6x [(201%nat, TG_hi6x)].
Lemma T_hi6x_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 HS_ht6x C_hi6x T_hi6x = true.
Proof.
  unfold T_hi6x. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 HS_ht6x C_hi6x 2 (k1p_hi6x JSraw_p_hi6x_2 JSraw_p_hi6x_10) HT_hi6x [(201%nat, TG_hi6x)] eq_refl (k1p_hi6x_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_hi6x C_hi6x 201%nat TG_hi6x [] 3 HS_p_hi6x_201 eq_refl eq_refl TG_hi6x_ok). apply mforest_ok_nil.
Qed.
Lemma k1p_hi7x_head_ok : segb KCm BFUELm FUELm ITm TT HS_ht7x C_hi7x HT_hi7x 2%nat (k1p_hi7x JSraw_p_hi7x_2 JSraw_p_hi7x_10) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1g3_hi7x_ok : segb KCm BFUELm FUELm ITm TT HS_p_hi7x_201 C_hi7x HTG3x 3%nat (g3_hi7x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition TG_hi7x : mtree := MPre 3 g3_hi7x HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))].
Lemma TG_hi7x_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 3 HS_p_hi7x_201 C_hi7x TG_hi7x = true.
Proof.
  unfold TG_hi7x. apply (segb_tree KCm BFUELm FUELm ITm TT 2 3 HS_p_hi7x_201 C_hi7x 3 g3_hi7x HTG3x [(301%nat, MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31)))] eq_refl (k1g3_hi7x_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 3 HTG3x C_hi7x 301%nat (MClass C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))) [] 3 HS_g3x eq_refl eq_refl).
  - apply (mtree_ok_class KCm BFUELm FUELm ITm TT 3%nat 3%nat HS_g3x C_hi7x C_G3x (MLeaf 3 (k1p_hi10x_tail JSraw_xj_g3x_31))); [vm_compute; reflexivity | exact (payb_leaf KCm BFUELm FUELm ITm TT 3 3 HS_g3x C_G3x 3 _ eq_refl (k1g3tx_ok TT))].
  - apply mforest_ok_nil.
Qed.
Definition T_hi7x : mtree := MPre 2 (k1p_hi7x JSraw_p_hi7x_2 JSraw_p_hi7x_10) HT_hi7x [(201%nat, TG_hi7x)].
Lemma T_hi7x_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 HS_ht7x C_hi7x T_hi7x = true.
Proof.
  unfold T_hi7x. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 HS_ht7x C_hi7x 2 (k1p_hi7x JSraw_p_hi7x_2 JSraw_p_hi7x_10) HT_hi7x [(201%nat, TG_hi7x)] eq_refl (k1p_hi7x_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_hi7x C_hi7x 201%nat TG_hi7x [] 3 HS_p_hi7x_201 eq_refl eq_refl TG_hi7x_ok). apply mforest_ok_nil.
Qed.
End TTS.
