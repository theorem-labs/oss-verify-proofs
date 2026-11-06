(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainItabBoth PlanFormsBoth BK0HS_jc BK0HS_jt BK0HS_jt2 BK0Defs BK0B_HS_jtb BK0B_HS_jt2b BK0TailDefs BK0BTailDefs BK0TailAll BK0B_arm BK0B_arm2 BK0B_mcb BK0B_tail BK0B_tail_js.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Definition K0B_HT_arm : list (nat * (nat * acs)) := [(900%nat, (3%nat, HS_jtb))].
Definition K0B_HT_mc : list (nat * (nat * acs)) := [(901%nat, (3%nat, HS_jt2b))].
Definition K0B_TAIL : plan := tail_b JSraw_tail_bj_11.
Lemma armf_a05889_ok : segb KCm BFUELm FUELm BITm TT_r5 (mcase_lo K0_ST_a05889 (EVar 14) 7928) K0_C_W K0B_HT_arm 2 armf_a05889 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a07929_ok : segb KCm BFUELm FUELm BITm TT_r5 (mcase_hi K0_ST_a05889 (EVar 14) 7928) K0_C_W K0B_HT_arm 2 armf_a07929 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma seg_mcbbf_ok : segb KCm BFUELm FUELm BITm TT_r5 HS_jtb K0_C_W K0B_HT_mc 3 seg_mcbbf = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma tail_b_ok : payb KCm BFUELm FUELm BITm TT_r5 HS_jt2b K0_C_W 3 K0B_TAIL = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition T_batch_mc : mtree := MPre 3 seg_mcbbf K0B_HT_mc [(901%nat, MLeaf 3 K0B_TAIL)].
Lemma T_batch_mc_ok : mtree_ok KCm BFUELm FUELm BITm TT_r5 2 3 HS_jtb K0_C_W T_batch_mc = true.
Proof.
  unfold T_batch_mc. apply (segb_tree KCm BFUELm FUELm BITm TT_r5 2 3 HS_jtb K0_C_W 3 seg_mcbbf K0B_HT_mc [(901%nat, MLeaf 3 K0B_TAIL)] eq_refl seg_mcbbf_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm BITm TT_r5 3 K0B_HT_mc K0_C_W 901%nat (MLeaf 3 K0B_TAIL) [] 3 HS_jt2b eq_refl eq_refl).
  - exact (payb_leaf KCm BFUELm FUELm BITm TT_r5 3 3 HS_jt2b K0_C_W 3 K0B_TAIL eq_refl tail_b_ok).
  - apply mforest_ok_nil.
Qed.
Definition T_b_a05889 : mtree := MPre 2 armf_a05889 K0B_HT_arm [(900%nat, T_batch_mc)].
Lemma T_b_a05889_ok : mtree_ok KCm BFUELm FUELm BITm TT_r5 2 2 (mcase_lo K0_ST_a05889 (EVar 14) 7928) K0_C_W T_b_a05889 = true.
Proof.
  unfold T_b_a05889. apply (segb_tree KCm BFUELm FUELm BITm TT_r5 2 2 (mcase_lo K0_ST_a05889 (EVar 14) 7928) K0_C_W 2 armf_a05889 K0B_HT_arm [(900%nat, T_batch_mc)] eq_refl armf_a05889_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm BITm TT_r5 2 K0B_HT_arm K0_C_W 900%nat T_batch_mc [] 3 HS_jtb eq_refl eq_refl).
  - exact T_batch_mc_ok.
  - apply mforest_ok_nil.
Qed.
Definition T_b_a07929 : mtree := MPre 2 armf_a07929 K0B_HT_arm [(900%nat, T_batch_mc)].
Lemma T_b_a07929_ok : mtree_ok KCm BFUELm FUELm BITm TT_r5 2 2 (mcase_hi K0_ST_a05889 (EVar 14) 7928) K0_C_W T_b_a07929 = true.
Proof.
  unfold T_b_a07929. apply (segb_tree KCm BFUELm FUELm BITm TT_r5 2 2 (mcase_hi K0_ST_a05889 (EVar 14) 7928) K0_C_W 2 armf_a07929 K0B_HT_arm [(900%nat, T_batch_mc)] eq_refl armf_a07929_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm BITm TT_r5 2 K0B_HT_arm K0_C_W 900%nat T_batch_mc [] 3 HS_jtb eq_refl eq_refl).
  - exact T_batch_mc_ok.
  - apply mforest_ok_nil.
Qed.
Definition T_batch : mtree := MCase (EVar 14) 7928 T_b_a05889 T_b_a07929.
Lemma T_batch_ok : mtree_ok KCm BFUELm FUELm BITm TT_r5 2 2 K0_ST_a05889 K0_C_W T_batch = true.
Proof. exact (mtree_ok_case KCm BFUELm FUELm BITm TT_r5 2%nat 2%nat K0_ST_a05889 K0_C_W (EVar 14) 7928 T_b_a05889 T_b_a07929 eq_refl T_b_a05889_ok T_b_a07929_ok). Qed.
Lemma T_batch_lvl : lvl_shape T_batch = LNode 2%nat.
Proof. reflexivity. Qed.
