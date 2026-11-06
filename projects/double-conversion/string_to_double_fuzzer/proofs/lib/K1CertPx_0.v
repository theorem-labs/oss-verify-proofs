(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainHSAsan MainItab PlanForms K1Dx_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Definition C_p48xa : class := [(QLook,4,4); (QFlen,65536,131071); (QRoom,32763,48128)].
Definition HT_p48xa : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_p48xa_201))].
Definition C_p48xb : class := [(QLook,4,4); (QFlen,65536,131071); (QRoom,32763,48128)].
Definition HT_p48xb : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_p48xb_201))].
Definition C_p64xa : class := [(QLook,4,4); (QFlen,65536,131071); (QRoom,48129,64512)].
Definition HT_p64xa : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_p64xa_201))].
Definition C_p64xb : class := [(QLook,4,4); (QFlen,65536,131071); (QRoom,48129,64512)].
Definition HT_p64xb : list (nat * (nat * acs)) := [(201%nat, (3%nat, HS_p_p64xb_201))].
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma k1p_p48xa_head_ok : segb KCm BFUELm FUELm ITm TT (mcase_lo HS_ht1x e_r 4046) C_p48xa HT_p48xa 2%nat (k1p_p48xa JSraw_p_p48xa_2 JSraw_p_p48xa_10 JSraw_p_p48xa_11 JSraw_p_p48xa_12 JSraw_p_p48xa_13) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1p_p48xa_t201_ok : payb KCm BFUELm FUELm ITm TT HS_p_p48xa_201 C_p48xa 3%nat (k1p_p48xa_tail JSraw_xj_p48xa_31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition T_p48xa : mtree := MPre 2 (k1p_p48xa JSraw_p_p48xa_2 JSraw_p_p48xa_10 JSraw_p_p48xa_11 JSraw_p_p48xa_12 JSraw_p_p48xa_13) HT_p48xa [(201%nat, MLeaf 3 (k1p_p48xa_tail JSraw_xj_p48xa_31))].
Lemma T_p48xa_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 (mcase_lo HS_ht1x e_r 4046) C_p48xa T_p48xa = true.
Proof.
  unfold T_p48xa. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 (mcase_lo HS_ht1x e_r 4046) C_p48xa 2 (k1p_p48xa JSraw_p_p48xa_2 JSraw_p_p48xa_10 JSraw_p_p48xa_11 JSraw_p_p48xa_12 JSraw_p_p48xa_13) HT_p48xa [(201%nat, MLeaf 3 (k1p_p48xa_tail JSraw_xj_p48xa_31))] eq_refl (k1p_p48xa_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_p48xa C_p48xa 201%nat (MLeaf 3 (k1p_p48xa_tail JSraw_xj_p48xa_31)) [] 3 HS_p_p48xa_201 eq_refl eq_refl (payb_leaf KCm BFUELm FUELm ITm TT 2 3 HS_p_p48xa_201 C_p48xa 3 _ eq_refl k1p_p48xa_t201_ok)).
  apply mforest_ok_nil.
Qed.
Lemma k1p_p48xb_head_ok : segb KCm BFUELm FUELm ITm TT (mcase_hi HS_ht1x e_r 4046) C_p48xb HT_p48xb 2%nat (k1p_p48xb JSraw_p_p48xb_2 JSraw_p_p48xb_10 JSraw_p_p48xb_11 JSraw_p_p48xb_12 JSraw_p_p48xb_13) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1p_p48xb_t201_ok : payb KCm BFUELm FUELm ITm TT HS_p_p48xb_201 C_p48xb 3%nat (k1p_p48xb_tail JSraw_xj_p48xb_31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition T_p48xb : mtree := MPre 2 (k1p_p48xb JSraw_p_p48xb_2 JSraw_p_p48xb_10 JSraw_p_p48xb_11 JSraw_p_p48xb_12 JSraw_p_p48xb_13) HT_p48xb [(201%nat, MLeaf 3 (k1p_p48xb_tail JSraw_xj_p48xb_31))].
Lemma T_p48xb_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 (mcase_hi HS_ht1x e_r 4046) C_p48xb T_p48xb = true.
Proof.
  unfold T_p48xb. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 (mcase_hi HS_ht1x e_r 4046) C_p48xb 2 (k1p_p48xb JSraw_p_p48xb_2 JSraw_p_p48xb_10 JSraw_p_p48xb_11 JSraw_p_p48xb_12 JSraw_p_p48xb_13) HT_p48xb [(201%nat, MLeaf 3 (k1p_p48xb_tail JSraw_xj_p48xb_31))] eq_refl (k1p_p48xb_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_p48xb C_p48xb 201%nat (MLeaf 3 (k1p_p48xb_tail JSraw_xj_p48xb_31)) [] 3 HS_p_p48xb_201 eq_refl eq_refl (payb_leaf KCm BFUELm FUELm ITm TT 2 3 HS_p_p48xb_201 C_p48xb 3 _ eq_refl k1p_p48xb_t201_ok)).
  apply mforest_ok_nil.
Qed.
Definition T_p48x : mtree := MCase e_r 4046 T_p48xa T_p48xb.
Lemma T_p48x_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 HS_ht1x C_p48xa T_p48x = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT 2%nat 2%nat HS_ht1x C_p48xa e_r 4046 T_p48xa T_p48xb eq_refl T_p48xa_ok T_p48xb_ok). Qed.
Lemma k1p_p64xa_head_ok : segb KCm BFUELm FUELm ITm TT (mcase_lo HS_ht1x e_r 4046) C_p64xa HT_p64xa 2%nat (k1p_p64xa JSraw_p_p64xa_2 JSraw_p_p64xa_10 JSraw_p_p64xa_11 JSraw_p_p64xa_12 JSraw_p_p64xa_13) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1p_p64xa_t201_ok : payb KCm BFUELm FUELm ITm TT HS_p_p64xa_201 C_p64xa 3%nat (k1p_p64xa_tail JSraw_xj_p64xa_31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition T_p64xa : mtree := MPre 2 (k1p_p64xa JSraw_p_p64xa_2 JSraw_p_p64xa_10 JSraw_p_p64xa_11 JSraw_p_p64xa_12 JSraw_p_p64xa_13) HT_p64xa [(201%nat, MLeaf 3 (k1p_p64xa_tail JSraw_xj_p64xa_31))].
Lemma T_p64xa_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 (mcase_lo HS_ht1x e_r 4046) C_p64xa T_p64xa = true.
Proof.
  unfold T_p64xa. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 (mcase_lo HS_ht1x e_r 4046) C_p64xa 2 (k1p_p64xa JSraw_p_p64xa_2 JSraw_p_p64xa_10 JSraw_p_p64xa_11 JSraw_p_p64xa_12 JSraw_p_p64xa_13) HT_p64xa [(201%nat, MLeaf 3 (k1p_p64xa_tail JSraw_xj_p64xa_31))] eq_refl (k1p_p64xa_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_p64xa C_p64xa 201%nat (MLeaf 3 (k1p_p64xa_tail JSraw_xj_p64xa_31)) [] 3 HS_p_p64xa_201 eq_refl eq_refl (payb_leaf KCm BFUELm FUELm ITm TT 2 3 HS_p_p64xa_201 C_p64xa 3 _ eq_refl k1p_p64xa_t201_ok)).
  apply mforest_ok_nil.
Qed.
Lemma k1p_p64xb_head_ok : segb KCm BFUELm FUELm ITm TT (mcase_hi HS_ht1x e_r 4046) C_p64xb HT_p64xb 2%nat (k1p_p64xb JSraw_p_p64xb_2 JSraw_p_p64xb_10 JSraw_p_p64xb_11 JSraw_p_p64xb_12 JSraw_p_p64xb_13) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma k1p_p64xb_t201_ok : payb KCm BFUELm FUELm ITm TT HS_p_p64xb_201 C_p64xb 3%nat (k1p_p64xb_tail JSraw_xj_p64xb_31) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition T_p64xb : mtree := MPre 2 (k1p_p64xb JSraw_p_p64xb_2 JSraw_p_p64xb_10 JSraw_p_p64xb_11 JSraw_p_p64xb_12 JSraw_p_p64xb_13) HT_p64xb [(201%nat, MLeaf 3 (k1p_p64xb_tail JSraw_xj_p64xb_31))].
Lemma T_p64xb_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 (mcase_hi HS_ht1x e_r 4046) C_p64xb T_p64xb = true.
Proof.
  unfold T_p64xb. apply (segb_tree KCm BFUELm FUELm ITm TT 2 2 (mcase_hi HS_ht1x e_r 4046) C_p64xb 2 (k1p_p64xb JSraw_p_p64xb_2 JSraw_p_p64xb_10 JSraw_p_p64xb_11 JSraw_p_p64xb_12 JSraw_p_p64xb_13) HT_p64xb [(201%nat, MLeaf 3 (k1p_p64xb_tail JSraw_xj_p64xb_31))] eq_refl (k1p_p64xb_head_ok) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 HT_p64xb C_p64xb 201%nat (MLeaf 3 (k1p_p64xb_tail JSraw_xj_p64xb_31)) [] 3 HS_p_p64xb_201 eq_refl eq_refl (payb_leaf KCm BFUELm FUELm ITm TT 2 3 HS_p_p64xb_201 C_p64xb 3 _ eq_refl k1p_p64xb_t201_ok)).
  apply mforest_ok_nil.
Qed.
Definition T_p64x : mtree := MCase e_r 4046 T_p64xa T_p64xb.
Lemma T_p64x_ok : mtree_ok KCm BFUELm FUELm ITm TT 2 2 HS_ht1x C_p64xa T_p64x = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT 2%nat 2%nat HS_ht1x C_p64xa e_r 4046 T_p64xa T_p64xb eq_refl T_p64xa_ok T_p64xb_ok). Qed.
End TTS.
