(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainItab PlanForms K0HS_jc K0HS_jt K0HS_jt2 K0Defs K0TailDefs K0TailAll K0CertTail K0CertArms0 K0CertArms1 K0CertArms2 K0CertArms3 K0CertArms4 K0Arm_a00001 K0Arm_a00008 K0Arm_a00009 K0Arm_a00017 K0Arm_a00049 K0Arm_a00065 K0Arm_a00097 K0Arm_a00129 K0Arm_a00161 K0Arm_a00193 K0Arm_a00225 K0Arm_a00257 K0Arm_a00289 K0Arm_a00321 K0Arm_a00353 K0Arm_a00385 K0Arm_a00417 K0Arm_a00449 K0Arm_a00641 K0Arm_a00889 K0Arm_a00897 K0Arm_a01409 K0Arm_a01913 K0Arm_a01921 K0Arm_a02945 K0Arm_a03961 K0Arm_a03969 K0Arm_a04096 K0Arm_a04097 K0Arm_a07937 K0Arm_a12033 K0Arm_a16121 K0Arm_a16129 K0Arm_a24065 K0Arm_a32249 K0Arm_a32257 K0Arm_a48129 K0Arm_a64505 K0SegMc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Section K0JC.
Variable T_batch : mtree.
Hypothesis T_batch_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a05889 K0_C_W T_batch = true.
Hypothesis T_batch_lvl : lvl_shape T_batch = LNode 2%nat.
Definition T_JT2 : mtree := MLeaf 3 K0_TAILP.
Lemma T_JT2_ok3 : mtree_ok KCm BFUELm FUELm ITm TT_r5 3 3 HS_jt2 K0_C_W T_JT2 = true.
Proof. exact (payb_leaf KCm BFUELm FUELm ITm TT_r5 3%nat 3%nat HS_jt2 K0_C_W 3%nat K0_TAILP eq_refl (tail_p_ok TT_r5)). Qed.
Lemma T_JT2_ok2 : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 3 HS_jt2 K0_C_W T_JT2 = true.
Proof. exact (payb_leaf KCm BFUELm FUELm ITm TT_r5 2%nat 3%nat HS_jt2 K0_C_W 3%nat K0_TAILP eq_refl (tail_p_ok TT_r5)). Qed.
Definition T_JT : mtree := MPre 3 seg_mcbf K0_HT_mc [(72%nat, T_JT2)].
Lemma T_JT_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 3 HS_jt K0_C_W T_JT = true.
Proof. unfold T_JT. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 3%nat HS_jt K0_C_W 3%nat seg_mcbf K0_HT_mc [(72%nat, T_JT2)] eq_refl (seg_mcbf_ok TT_r5) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 3%nat K0_HT_mc K0_C_W 72%nat T_JT2 [] 3%nat HS_jt2 eq_refl eq_refl T_JT2_ok3). apply mforest_ok_nil. Qed.
Definition T_a00001 : mtree := MPre 2 armf_a00001 K0_HT_quick [(72%nat, T_JT2)].
Lemma T_a00001_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00001 K0_C_W T_a00001 = true.
Proof. unfold T_a00001. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00001 K0_C_W 2%nat armf_a00001 K0_HT_quick [(72%nat, T_JT2)] eq_refl armf_a00001_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_quick K0_C_W 72%nat T_JT2 [] 3%nat HS_jt2 eq_refl eq_refl T_JT2_ok2). apply mforest_ok_nil. Qed.
Definition T_a00008 : mtree := MPre 2 armf_a00008 K0_HT_quick [(72%nat, T_JT2)].
Lemma T_a00008_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00008 K0_C_W T_a00008 = true.
Proof. unfold T_a00008. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00008 K0_C_W 2%nat armf_a00008 K0_HT_quick [(72%nat, T_JT2)] eq_refl armf_a00008_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_quick K0_C_W 72%nat T_JT2 [] 3%nat HS_jt2 eq_refl eq_refl T_JT2_ok2). apply mforest_ok_nil. Qed.
Definition T_a00009 : mtree := MPre 2 armf_a00009 K0_HT_quick [(72%nat, T_JT2)].
Lemma T_a00009_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00009 K0_C_W T_a00009 = true.
Proof. unfold T_a00009. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00009 K0_C_W 2%nat armf_a00009 K0_HT_quick [(72%nat, T_JT2)] eq_refl armf_a00009_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_quick K0_C_W 72%nat T_JT2 [] 3%nat HS_jt2 eq_refl eq_refl T_JT2_ok2). apply mforest_ok_nil. Qed.
Definition T_a00017 : mtree := MPre 2 armf_a00017 K0_HT_quick [(72%nat, T_JT2)].
Lemma T_a00017_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00017 K0_C_W T_a00017 = true.
Proof. unfold T_a00017. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00017 K0_C_W 2%nat armf_a00017 K0_HT_quick [(72%nat, T_JT2)] eq_refl armf_a00017_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_quick K0_C_W 72%nat T_JT2 [] 3%nat HS_jt2 eq_refl eq_refl T_JT2_ok2). apply mforest_ok_nil. Qed.
Definition T_a00049 : mtree := MPre 2 armf_a00049 K0_HT_quick [(72%nat, T_JT2)].
Lemma T_a00049_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00049 K0_C_W T_a00049 = true.
Proof. unfold T_a00049. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00049 K0_C_W 2%nat armf_a00049 K0_HT_quick [(72%nat, T_JT2)] eq_refl armf_a00049_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_quick K0_C_W 72%nat T_JT2 [] 3%nat HS_jt2 eq_refl eq_refl T_JT2_ok2). apply mforest_ok_nil. Qed.
Definition T_a00065 : mtree := MPre 2 armf_a00065 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00065_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00065 K0_C_W T_a00065 = true.
Proof. unfold T_a00065. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00065 K0_C_W 2%nat armf_a00065 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00065_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00097 : mtree := MPre 2 armf_a00097 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00097_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00097 K0_C_W T_a00097 = true.
Proof. unfold T_a00097. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00097 K0_C_W 2%nat armf_a00097 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00097_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00129 : mtree := MPre 2 armf_a00129 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00129_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00129 K0_C_W T_a00129 = true.
Proof. unfold T_a00129. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00129 K0_C_W 2%nat armf_a00129 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00129_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00161 : mtree := MPre 2 armf_a00161 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00161_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00161 K0_C_W T_a00161 = true.
Proof. unfold T_a00161. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00161 K0_C_W 2%nat armf_a00161 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00161_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00193 : mtree := MPre 2 armf_a00193 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00193_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00193 K0_C_W T_a00193 = true.
Proof. unfold T_a00193. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00193 K0_C_W 2%nat armf_a00193 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00193_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00225 : mtree := MPre 2 armf_a00225 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00225_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00225 K0_C_W T_a00225 = true.
Proof. unfold T_a00225. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00225 K0_C_W 2%nat armf_a00225 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00225_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00257 : mtree := MPre 2 armf_a00257 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00257_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00257 K0_C_W T_a00257 = true.
Proof. unfold T_a00257. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00257 K0_C_W 2%nat armf_a00257 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00257_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00289 : mtree := MPre 2 armf_a00289 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00289_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00289 K0_C_W T_a00289 = true.
Proof. unfold T_a00289. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00289 K0_C_W 2%nat armf_a00289 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00289_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00321 : mtree := MPre 2 armf_a00321 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00321_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00321 K0_C_W T_a00321 = true.
Proof. unfold T_a00321. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00321 K0_C_W 2%nat armf_a00321 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00321_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00353 : mtree := MPre 2 armf_a00353 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00353_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00353 K0_C_W T_a00353 = true.
Proof. unfold T_a00353. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00353 K0_C_W 2%nat armf_a00353 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00353_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00385 : mtree := MPre 2 armf_a00385 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00385_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00385 K0_C_W T_a00385 = true.
Proof. unfold T_a00385. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00385 K0_C_W 2%nat armf_a00385 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00385_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00417 : mtree := MPre 2 armf_a00417 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00417_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00417 K0_C_W T_a00417 = true.
Proof. unfold T_a00417. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00417 K0_C_W 2%nat armf_a00417 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00417_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00449 : mtree := MPre 2 armf_a00449 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00449_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00449 K0_C_W T_a00449 = true.
Proof. unfold T_a00449. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00449 K0_C_W 2%nat armf_a00449 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00449_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00641 : mtree := MPre 2 armf_a00641 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00641_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00641 K0_C_W T_a00641 = true.
Proof. unfold T_a00641. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00641 K0_C_W 2%nat armf_a00641 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00641_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00889 : mtree := MPre 2 armf_a00889 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00889_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00889 K0_C_W T_a00889 = true.
Proof. unfold T_a00889. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00889 K0_C_W 2%nat armf_a00889 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00889_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a00897 : mtree := MPre 2 armf_a00897 K0_HT_big [(70%nat, T_JT)].
Lemma T_a00897_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a00897 K0_C_W T_a00897 = true.
Proof. unfold T_a00897. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a00897 K0_C_W 2%nat armf_a00897 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a00897_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a01409 : mtree := MPre 2 armf_a01409 K0_HT_big [(70%nat, T_JT)].
Lemma T_a01409_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a01409 K0_C_W T_a01409 = true.
Proof. unfold T_a01409. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a01409 K0_C_W 2%nat armf_a01409 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a01409_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a01913 : mtree := MPre 2 armf_a01913 K0_HT_big [(70%nat, T_JT)].
Lemma T_a01913_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a01913 K0_C_W T_a01913 = true.
Proof. unfold T_a01913. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a01913 K0_C_W 2%nat armf_a01913 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a01913_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a01921 : mtree := MPre 2 armf_a01921 K0_HT_big [(70%nat, T_JT)].
Lemma T_a01921_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a01921 K0_C_W T_a01921 = true.
Proof. unfold T_a01921. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a01921 K0_C_W 2%nat armf_a01921 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a01921_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a02945 : mtree := MPre 2 armf_a02945 K0_HT_big [(70%nat, T_JT)].
Lemma T_a02945_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a02945 K0_C_W T_a02945 = true.
Proof. unfold T_a02945. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a02945 K0_C_W 2%nat armf_a02945 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a02945_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a03961 : mtree := MPre 2 armf_a03961 K0_HT_big [(70%nat, T_JT)].
Lemma T_a03961_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a03961 K0_C_W T_a03961 = true.
Proof. unfold T_a03961. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a03961 K0_C_W 2%nat armf_a03961 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a03961_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a03969 : mtree := MPre 2 armf_a03969 K0_HT_big [(70%nat, T_JT)].
Lemma T_a03969_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a03969 K0_C_W T_a03969 = true.
Proof. unfold T_a03969. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a03969 K0_C_W 2%nat armf_a03969 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a03969_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a04096 : mtree := MPre 2 armf_a04096 K0_HT_big [(70%nat, T_JT)].
Lemma T_a04096_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a04096 K0_C_W T_a04096 = true.
Proof. unfold T_a04096. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a04096 K0_C_W 2%nat armf_a04096 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a04096_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a04097 : mtree := MPre 2 armf_a04097 K0_HT_big [(70%nat, T_JT)].
Lemma T_a04097_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a04097 K0_C_W T_a04097 = true.
Proof. unfold T_a04097. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a04097 K0_C_W 2%nat armf_a04097 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a04097_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a07937 : mtree := MPre 2 armf_a07937 K0_HT_big [(70%nat, T_JT)].
Lemma T_a07937_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a07937 K0_C_W T_a07937 = true.
Proof. unfold T_a07937. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a07937 K0_C_W 2%nat armf_a07937 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a07937_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a12033 : mtree := MPre 2 armf_a12033 K0_HT_big [(70%nat, T_JT)].
Lemma T_a12033_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a12033 K0_C_W T_a12033 = true.
Proof. unfold T_a12033. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a12033 K0_C_W 2%nat armf_a12033 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a12033_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a16121 : mtree := MPre 2 armf_a16121 K0_HT_big [(70%nat, T_JT)].
Lemma T_a16121_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a16121 K0_C_W T_a16121 = true.
Proof. unfold T_a16121. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a16121 K0_C_W 2%nat armf_a16121 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a16121_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a16129 : mtree := MPre 2 armf_a16129 K0_HT_big [(70%nat, T_JT)].
Lemma T_a16129_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a16129 K0_C_W T_a16129 = true.
Proof. unfold T_a16129. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a16129 K0_C_W 2%nat armf_a16129 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a16129_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a24065 : mtree := MPre 2 armf_a24065 K0_HT_big [(70%nat, T_JT)].
Lemma T_a24065_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a24065 K0_C_W T_a24065 = true.
Proof. unfold T_a24065. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a24065 K0_C_W 2%nat armf_a24065 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a24065_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a32249 : mtree := MPre 2 armf_a32249 K0_HT_big [(70%nat, T_JT)].
Lemma T_a32249_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a32249 K0_C_W T_a32249 = true.
Proof. unfold T_a32249. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a32249 K0_C_W 2%nat armf_a32249 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a32249_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a32257 : mtree := MPre 2 armf_a32257 K0_HT_big [(70%nat, T_JT)].
Lemma T_a32257_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a32257 K0_C_W T_a32257 = true.
Proof. unfold T_a32257. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a32257 K0_C_W 2%nat armf_a32257 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a32257_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a48129 : mtree := MPre 2 armf_a48129 K0_HT_big [(70%nat, T_JT)].
Lemma T_a48129_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a48129 K0_C_W T_a48129 = true.
Proof. unfold T_a48129. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a48129 K0_C_W 2%nat armf_a48129 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a48129_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_a64505 : mtree := MPre 2 armf_a64505 K0_HT_big [(70%nat, T_JT)].
Lemma T_a64505_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a64505 K0_C_W T_a64505 = true.
Proof. unfold T_a64505. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat K0_ST_a64505 K0_C_W 2%nat armf_a64505 K0_HT_big [(70%nat, T_JT)] eq_refl armf_a64505_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_big K0_C_W 70%nat T_JT [] 3%nat HS_jt eq_refl eq_refl T_JT_ok). apply mforest_ok_nil. Qed.
Definition T_n1 : mtree := MCase (EVar 14) 7 T_a00001 T_a00008.
Lemma T_n1_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_lo (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 8) K0_C_W T_n1 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_lo (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 8) K0_C_W (EVar 14) 7 T_a00001 T_a00008 eq_refl T_a00001_ok T_a00008_ok). Qed.
Definition T_n2 : mtree := MCase (EVar 14) 16 T_a00009 T_a00017.
Lemma T_n2_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_lo (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 8) K0_C_W T_n2 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_lo (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 8) K0_C_W (EVar 14) 16 T_a00009 T_a00017 eq_refl T_a00009_ok T_a00017_ok). Qed.
Definition T_n3 : mtree := MCase (EVar 14) 8 T_n1 T_n2.
Lemma T_n3_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) K0_C_W T_n3 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) K0_C_W (EVar 14) 8 T_n1 T_n2 eq_refl T_n1_ok T_n2_ok). Qed.
Definition T_n4 : mtree := MCase (EVar 14) 64 T_a00049 T_a00065.
Lemma T_n4_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_hi (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 96) K0_C_W T_n4 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_hi (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 96) K0_C_W (EVar 14) 64 T_a00049 T_a00065 eq_refl T_a00049_ok T_a00065_ok). Qed.
Definition T_n5 : mtree := MCase (EVar 14) 128 T_a00097 T_a00129.
Lemma T_n5_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_hi (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 96) K0_C_W T_n5 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_hi (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 96) K0_C_W (EVar 14) 128 T_a00097 T_a00129 eq_refl T_a00097_ok T_a00129_ok). Qed.
Definition T_n6 : mtree := MCase (EVar 14) 96 T_n4 T_n5.
Lemma T_n6_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) K0_C_W T_n6 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) K0_C_W (EVar 14) 96 T_n4 T_n5 eq_refl T_n4_ok T_n5_ok). Qed.
Definition T_n7 : mtree := MCase (EVar 14) 48 T_n3 T_n6.
Lemma T_n7_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) K0_C_W T_n7 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) K0_C_W (EVar 14) 48 T_n3 T_n6 eq_refl T_n3_ok T_n6_ok). Qed.
Definition T_n8 : mtree := MCase (EVar 14) 192 T_a00161 T_a00193.
Lemma T_n8_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_lo (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 224) K0_C_W T_n8 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_lo (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 224) K0_C_W (EVar 14) 192 T_a00161 T_a00193 eq_refl T_a00161_ok T_a00193_ok). Qed.
Definition T_n9 : mtree := MCase (EVar 14) 256 T_a00225 T_a00257.
Lemma T_n9_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_lo (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 224) K0_C_W T_n9 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_lo (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 224) K0_C_W (EVar 14) 256 T_a00225 T_a00257 eq_refl T_a00225_ok T_a00257_ok). Qed.
Definition T_n10 : mtree := MCase (EVar 14) 224 T_n8 T_n9.
Lemma T_n10_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) K0_C_W T_n10 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) K0_C_W (EVar 14) 224 T_n8 T_n9 eq_refl T_n8_ok T_n9_ok). Qed.
Definition T_n11 : mtree := MCase (EVar 14) 320 T_a00289 T_a00321.
Lemma T_n11_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_hi (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 352) K0_C_W T_n11 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_hi (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 352) K0_C_W (EVar 14) 320 T_a00289 T_a00321 eq_refl T_a00289_ok T_a00321_ok). Qed.
Definition T_n12 : mtree := MCase (EVar 14) 384 T_a00353 T_a00385.
Lemma T_n12_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_hi (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 352) K0_C_W T_n12 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_hi (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 352) K0_C_W (EVar 14) 384 T_a00353 T_a00385 eq_refl T_a00353_ok T_a00385_ok). Qed.
Definition T_n13 : mtree := MCase (EVar 14) 352 T_n11 T_n12.
Lemma T_n13_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) K0_C_W T_n13 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) K0_C_W (EVar 14) 352 T_n11 T_n12 eq_refl T_n11_ok T_n12_ok). Qed.
Definition T_n14 : mtree := MCase (EVar 14) 288 T_n10 T_n13.
Lemma T_n14_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) K0_C_W T_n14 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) K0_C_W (EVar 14) 288 T_n10 T_n13 eq_refl T_n10_ok T_n13_ok). Qed.
Definition T_n15 : mtree := MCase (EVar 14) 160 T_n7 T_n14.
Lemma T_n15_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo HS_jc (EVar 14) 416) K0_C_W T_n15 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo HS_jc (EVar 14) 416) K0_C_W (EVar 14) 160 T_n7 T_n14 eq_refl T_n7_ok T_n14_ok). Qed.
Definition T_n16 : mtree := MCase (EVar 14) 448 T_a00417 T_a00449.
Lemma T_n16_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 640) K0_C_W T_n16 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 640) K0_C_W (EVar 14) 448 T_a00417 T_a00449 eq_refl T_a00417_ok T_a00449_ok). Qed.
Definition T_s641 : mtree := MCase (EVar 14) 888 T_a00641 T_a00889.
Lemma T_s641_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_hi (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 640) (EVar 14) 896) K0_C_W T_s641 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_hi (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 640) (EVar 14) 896) K0_C_W (EVar 14) 888 T_a00641 T_a00889 eq_refl T_a00641_ok T_a00889_ok). Qed.
Definition T_n18 : mtree := MCase (EVar 14) 896 T_s641 T_a00897.
Lemma T_n18_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 640) K0_C_W T_n18 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 640) K0_C_W (EVar 14) 896 T_s641 T_a00897 eq_refl T_s641_ok T_a00897_ok). Qed.
Definition T_n19 : mtree := MCase (EVar 14) 640 T_n16 T_n18.
Lemma T_n19_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) K0_C_W T_n19 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) K0_C_W (EVar 14) 640 T_n16 T_n18 eq_refl T_n16_ok T_n18_ok). Qed.
Definition T_s1409 : mtree := MCase (EVar 14) 1912 T_a01409 T_a01913.
Lemma T_s1409_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_lo (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) (EVar 14) 1920) K0_C_W T_s1409 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_lo (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) (EVar 14) 1920) K0_C_W (EVar 14) 1912 T_a01409 T_a01913 eq_refl T_a01409_ok T_a01913_ok). Qed.
Definition T_n21 : mtree := MCase (EVar 14) 1920 T_s1409 T_a01921.
Lemma T_n21_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) K0_C_W T_n21 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) K0_C_W (EVar 14) 1920 T_s1409 T_a01921 eq_refl T_s1409_ok T_a01921_ok). Qed.
Definition T_s2945 : mtree := MCase (EVar 14) 3960 T_a02945 T_a03961.
Lemma T_s2945_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_hi (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) (EVar 14) 3968) K0_C_W T_s2945 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_hi (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) (EVar 14) 3968) K0_C_W (EVar 14) 3960 T_a02945 T_a03961 eq_refl T_a02945_ok T_a03961_ok). Qed.
Definition T_n23 : mtree := MCase (EVar 14) 3968 T_s2945 T_a03969.
Lemma T_n23_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) K0_C_W T_n23 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) K0_C_W (EVar 14) 3968 T_s2945 T_a03969 eq_refl T_s2945_ok T_a03969_ok). Qed.
Definition T_n24 : mtree := MCase (EVar 14) 2944 T_n21 T_n23.
Lemma T_n24_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) K0_C_W T_n24 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) K0_C_W (EVar 14) 2944 T_n21 T_n23 eq_refl T_n21_ok T_n23_ok). Qed.
Definition T_n25 : mtree := MCase (EVar 14) 1408 T_n19 T_n24.
Lemma T_n25_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) K0_C_W T_n25 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) K0_C_W (EVar 14) 1408 T_n19 T_n24 eq_refl T_n19_ok T_n24_ok). Qed.
Definition T_n26 : mtree := MCase (EVar 14) 4096 T_a04096 T_a04097.
Lemma T_n26_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_lo (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 5888) K0_C_W T_n26 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_lo (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 5888) K0_C_W (EVar 14) 4096 T_a04096 T_a04097 eq_refl T_a04096_ok T_a04097_ok). Qed.
Definition T_n27 : mtree := MCase (EVar 14) 7936 T_batch T_a07937.
Lemma T_n27_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_lo (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 5888) K0_C_W T_n27 = true.
Proof. apply (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_lo (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 5888) K0_C_W (EVar 14) 7936 T_batch T_a07937); [unfold T_a07937; cbn [lvl_shape]; rewrite T_batch_lvl; reflexivity | exact T_batch_ok | exact T_a07937_ok]. Qed.
Definition T_n28 : mtree := MCase (EVar 14) 5888 T_n26 T_n27.
Lemma T_n28_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) K0_C_W T_n28 = true.
Proof. apply (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) K0_C_W (EVar 14) 5888 T_n26 T_n27); [unfold T_n26, T_a04096, T_n27; cbn [lvl_shape]; rewrite T_batch_lvl; reflexivity | exact T_n26_ok | exact T_n27_ok]. Qed.
Definition T_s12033 : mtree := MCase (EVar 14) 16120 T_a12033 T_a16121.
Lemma T_s12033_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_lo (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 16128) K0_C_W T_s12033 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_lo (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 16128) K0_C_W (EVar 14) 16120 T_a12033 T_a16121 eq_refl T_a12033_ok T_a16121_ok). Qed.
Definition T_n30 : mtree := MCase (EVar 14) 16128 T_s12033 T_a16129.
Lemma T_n30_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) K0_C_W T_n30 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) K0_C_W (EVar 14) 16128 T_s12033 T_a16129 eq_refl T_s12033_ok T_a16129_ok). Qed.
Definition T_s24065 : mtree := MCase (EVar 14) 32248 T_a24065 T_a32249.
Lemma T_s24065_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_lo (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 32256) K0_C_W T_s24065 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_lo (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 32256) K0_C_W (EVar 14) 32248 T_a24065 T_a32249 eq_refl T_a24065_ok T_a32249_ok). Qed.
Definition T_s48129 : mtree := MCase (EVar 14) 64504 T_a48129 T_a64505.
Lemma T_s48129_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 32256) (EVar 14) 48128) K0_C_W T_s48129 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 32256) (EVar 14) 48128) K0_C_W (EVar 14) 64504 T_a48129 T_a64505 eq_refl T_a48129_ok T_a64505_ok). Qed.
Definition T_n33 : mtree := MCase (EVar 14) 48128 T_a32257 T_s48129.
Lemma T_n33_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 32256) K0_C_W T_n33 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 32256) K0_C_W (EVar 14) 48128 T_a32257 T_s48129 eq_refl T_a32257_ok T_s48129_ok). Qed.
Definition T_n34 : mtree := MCase (EVar 14) 32256 T_s24065 T_n33.
Lemma T_n34_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) K0_C_W T_n34 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) K0_C_W (EVar 14) 32256 T_s24065 T_n33 eq_refl T_s24065_ok T_n33_ok). Qed.
Definition T_n35 : mtree := MCase (EVar 14) 24064 T_n30 T_n34.
Lemma T_n35_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) K0_C_W T_n35 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) K0_C_W (EVar 14) 24064 T_n30 T_n34 eq_refl T_n30_ok T_n34_ok). Qed.
Definition T_n36 : mtree := MCase (EVar 14) 12032 T_n28 T_n35.
Lemma T_n36_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) K0_C_W T_n36 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) K0_C_W (EVar 14) 12032 T_n28 T_n35 eq_refl T_n28_ok T_n35_ok). Qed.
Definition T_n37 : mtree := MCase (EVar 14) 4095 T_n25 T_n36.
Lemma T_n37_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 (mcase_hi HS_jc (EVar 14) 416) K0_C_W T_n37 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat (mcase_hi HS_jc (EVar 14) 416) K0_C_W (EVar 14) 4095 T_n25 T_n36 eq_refl T_n25_ok T_n36_ok). Qed.
Definition T_n38 : mtree := MCase (EVar 14) 416 T_n15 T_n37.
Lemma T_n38_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 HS_jc K0_C_W T_n38 = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat HS_jc K0_C_W (EVar 14) 416 T_n15 T_n37 eq_refl T_n15_ok T_n37_ok). Qed.
Definition T_JC : mtree := T_n38.
Lemma T_JC_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 HS_jc K0_C_W T_JC = true.
Proof. exact T_n38_ok. Qed.
End K0JC.
