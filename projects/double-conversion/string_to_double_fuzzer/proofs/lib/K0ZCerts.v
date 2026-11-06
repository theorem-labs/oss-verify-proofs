(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainHSAsan MainItab ArgFragsAsan PlanForms K0HS_p5 K0Z_HS_zj K0Z_fa K0Z_fb K0Z_fa_js K0Z_fb_js K0Z_cont K0Z_cont_js.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Definition K0Z_ZCONT : plan := zcont JSraw_zcontj_11.
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Definition C_K0Z_za : class := [(QLook,4,4); (QFlen,6,64); (QRoom,0,0)].
Definition C_K0Z_zb : class := [(QLook,4,4); (QFlen,65,65535); (QRoom,0,0)].
Definition K0Z_C_ZW : class := [(QLook,4,4); (QFlen,6,65535); (QRoom,0,0)].
Definition K0Z_HT : list (nat * (nat * acs)) := [(920%nat, (2%nat, HS_zj))].
Lemma K0Z_fa_ok : segb KCm BFUELm FUELm ITm TT HS_p5 C_K0Z_za K0Z_HT 2 (zf_af JSraw_zfa_al_2) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma K0Z_fb_ok : segb KCm BFUELm FUELm ITm TT HS_p5 C_K0Z_zb K0Z_HT 2 (zf_bf JSraw_zfb_al_2) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma K0Z_cont_ok : payb KCm BFUELm FUELm ITm TT HS_zj K0Z_C_ZW 2 K0Z_ZCONT = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition T_zcont : mtree := MLeaf 2 K0Z_ZCONT.
Definition T_za : mtree := MPre 2 (zf_af JSraw_zfa_al_2) K0Z_HT [(920%nat, MClass K0Z_C_ZW T_zcont)].
Lemma T_za_ok : mtree_ok KCm BFUELm FUELm ITm TT 0 2 HS_p5 C_K0Z_za T_za = true.
Proof.
  unfold T_za. apply (segb_tree KCm BFUELm FUELm ITm TT 0 2 HS_p5 C_K0Z_za 2 (zf_af JSraw_zfa_al_2) K0Z_HT [(920%nat, MClass K0Z_C_ZW T_zcont)] eq_refl K0Z_fa_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 K0Z_HT C_K0Z_za 920%nat (MClass K0Z_C_ZW T_zcont) [] 2 HS_zj eq_refl eq_refl).
  - apply (mtree_ok_class KCm BFUELm FUELm ITm TT 2 2 HS_zj C_K0Z_za K0Z_C_ZW T_zcont eq_refl).
    exact (payb_leaf KCm BFUELm FUELm ITm TT 2 2 HS_zj K0Z_C_ZW 2 K0Z_ZCONT eq_refl K0Z_cont_ok).
  - apply mforest_ok_nil.
Qed.
Lemma T_za_lvl : lvl_shape T_za = LNode 2%nat.
Proof. reflexivity. Qed.
Definition T_zb : mtree := MPre 2 (zf_bf JSraw_zfb_al_2) K0Z_HT [(920%nat, MClass K0Z_C_ZW T_zcont)].
Lemma T_zb_ok : mtree_ok KCm BFUELm FUELm ITm TT 0 2 HS_p5 C_K0Z_zb T_zb = true.
Proof.
  unfold T_zb. apply (segb_tree KCm BFUELm FUELm ITm TT 0 2 HS_p5 C_K0Z_zb 2 (zf_bf JSraw_zfb_al_2) K0Z_HT [(920%nat, MClass K0Z_C_ZW T_zcont)] eq_refl K0Z_fb_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT 2 K0Z_HT C_K0Z_zb 920%nat (MClass K0Z_C_ZW T_zcont) [] 2 HS_zj eq_refl eq_refl).
  - apply (mtree_ok_class KCm BFUELm FUELm ITm TT 2 2 HS_zj C_K0Z_zb K0Z_C_ZW T_zcont eq_refl).
    exact (payb_leaf KCm BFUELm FUELm ITm TT 2 2 HS_zj K0Z_C_ZW 2 K0Z_ZCONT eq_refl K0Z_cont_ok).
  - apply mforest_ok_nil.
Qed.
Lemma T_zb_lvl : lvl_shape T_zb = LNode 2%nat.
Proof. reflexivity. Qed.
End TTS.
