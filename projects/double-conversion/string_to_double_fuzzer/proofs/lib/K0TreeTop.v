(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainItab PlanForms MainHSAsan ArgFragsAsan K0HS_p5 K0HS_jc K0HS_jt K0HS_jt2 K0Defs K0TailDefs K0TailAll K0CertFront K0TreeJC K0PreP5 K0PreJcA K0PreJcB K0JS_jca_al K0JS_jcb_al K0E_empty K0E_short K0E_ovra K0E_ovrb K0ECerts K0ZCerts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Section K0TOP.
Variable T_batch : mtree.
Hypothesis T_batch_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 K0_ST_a05889 K0_C_W T_batch = true.
Hypothesis T_batch_lvl : lvl_shape T_batch = LNode 2%nat.
Definition C_K0S : class := [(QLook,4,4); (QFlen,65,65535); (QRoom,64513,65529)].
Variable T_sec : mtree.
Hypothesis T_sec_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 C_K0S T_sec = true.
Definition T_u3 : mtree := MLeaf 2 K0E_empty.err_empty.
Lemma T_u3_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 (K0_C_FILE ++ [(QFlen, QMIN, 0)]) T_u3 = true.
Proof. exact (payb_leaf KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 (K0_C_FILE ++ [(QFlen, QMIN, 0)]) 2%nat K0E_empty.err_empty eq_refl K0E_empty_ok). Qed.
Definition T_u6 : mtree := MLeaf 2 K0E_short.err_short.
Lemma T_u6_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 C_K0E_short T_u6 = true.
Proof. exact (payb_leaf KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 C_K0E_short 2%nat K0E_short.err_short eq_refl K0E_short_ok). Qed.
Definition T_u5 : mtree := MClass C_K0E_short T_u6.
Lemma T_u5_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 ((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, QMIN, 5)]) T_u5 = true.
Proof. apply (mtree_ok_class KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 ((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, QMIN, 5)]) C_K0E_short T_u6); [vm_compute; reflexivity | exact T_u6_ok]. Qed.
Definition T_u10 : mtree := MLeaf 2 K0E_ovra.err_ovra.
Lemma T_u10_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 C_K0E_ovra T_u10 = true.
Proof. exact (payb_leaf KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 C_K0E_ovra 2%nat K0E_ovra.err_ovra eq_refl K0E_ovra_ok). Qed.
Definition T_u9 : mtree := MClass C_K0E_ovra T_u10.
Lemma T_u9_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 ((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, QMIN, (-1))]) T_u9 = true.
Proof. apply (mtree_ok_class KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 ((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, QMIN, (-1))]) C_K0E_ovra T_u10); [vm_compute; reflexivity | exact T_u10_ok]. Qed.
Definition T_u12 : mtree := MClass C_K0Z_za T_za.
Lemma T_u12_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 (((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, QMIN, 0)]) T_u12 = true.
Proof. apply (mtree_ok_class KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 (((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, QMIN, 0)]) C_K0Z_za T_za); [vm_compute; reflexivity | exact (T_za_ok TT_r5)]. Qed.
Definition T_u17 : mtree := MClass K0_C_W (T_JC T_batch).
Lemma T_u17_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 HS_jc K0_C_A T_u17 = true.
Proof. apply (mtree_ok_class KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat HS_jc K0_C_A K0_C_W (T_JC T_batch)); [vm_compute; reflexivity | exact (T_JC_ok T_batch T_batch_ok T_batch_lvl)]. Qed.
Definition T_u16 : mtree := MPre 2 (pre_jcaf JSraw_jca_al_2) K0_HT_jc [(52%nat, T_u17)].
Lemma T_u16_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 K0_C_A T_u16 = true.
Proof. unfold T_u16. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 K0_C_A 2%nat (pre_jcaf JSraw_jca_al_2) K0_HT_jc [(52%nat, T_u17)] eq_refl (pre_jcaf_ok TT_r5) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_jc K0_C_A 52%nat T_u17 [] 2%nat HS_jc eq_refl eq_refl T_u17_ok). apply mforest_ok_nil. Qed.
Definition T_u15 : mtree := MClass K0_C_A T_u16.
Lemma T_u15_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 ((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 58)]) T_u15 = true.
Proof. apply (mtree_ok_class KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 ((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 58)]) K0_C_A T_u16); [vm_compute; reflexivity | exact T_u16_ok]. Qed.
Definition T_u19 : mtree := MEmpty 2.
Lemma T_u19_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 ((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 58 + 1, QMAX)]) T_u19 = true.
Proof. apply (mtree_ok_empty KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 ((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 58 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
Definition T_u14 : mtree := MSplit QRoom 58 T_u15 T_u19.
Lemma T_u14_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 (((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) T_u14 = true.
Proof. exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 (((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) QRoom 58 T_u15 T_u19 T_u15_ok T_u19_ok). Qed.
Definition T_u11 : mtree := MSplit QRoom 0 T_u12 T_u14.
Lemma T_u11_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 ((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, (-1) + 1, QMAX)]) T_u11 = true.
Proof. exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 ((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) ++ [(QRoom, (-1) + 1, QMAX)]) QRoom 0 T_u12 T_u14 T_u12_ok T_u14_ok). Qed.
Definition T_u8 : mtree := MSplit QRoom (-1) T_u9 T_u11.
Lemma T_u8_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 (((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) T_u8 = true.
Proof. exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 (((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, QMIN, 64)]) QRoom (-1) T_u9 T_u11 T_u9_ok T_u11_ok). Qed.
Definition T_u22 : mtree := MLeaf 2 K0E_ovrb.err_ovrb.
Lemma T_u22_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 C_K0E_ovrb T_u22 = true.
Proof. exact (payb_leaf KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 C_K0E_ovrb 2%nat K0E_ovrb.err_ovrb eq_refl K0E_ovrb_ok). Qed.
Definition T_u21 : mtree := MClass C_K0E_ovrb T_u22.
Lemma T_u21_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 ((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, QMIN, (-1))]) T_u21 = true.
Proof. apply (mtree_ok_class KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 ((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, QMIN, (-1))]) C_K0E_ovrb T_u22); [vm_compute; reflexivity | exact T_u22_ok]. Qed.
Definition T_u24 : mtree := MClass C_K0Z_zb T_zb.
Lemma T_u24_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 (((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, QMIN, 0)]) T_u24 = true.
Proof. apply (mtree_ok_class KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 (((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, QMIN, 0)]) C_K0Z_zb T_zb); [vm_compute; reflexivity | exact (T_zb_ok TT_r5)]. Qed.
Definition T_u29 : mtree := MClass K0_C_W (T_JC T_batch).
Lemma T_u29_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 2 2 HS_jc K0_C_B T_u29 = true.
Proof. apply (mtree_ok_class KCm BFUELm FUELm ITm TT_r5 2%nat 2%nat HS_jc K0_C_B K0_C_W (T_JC T_batch)); [vm_compute; reflexivity | exact (T_JC_ok T_batch T_batch_ok T_batch_lvl)]. Qed.
Definition T_u28 : mtree := MPre 2 (pre_jcbf JSraw_jcb_al_2) K0_HT_jc [(52%nat, T_u29)].
Lemma T_u28_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 K0_C_B T_u28 = true.
Proof. unfold T_u28. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 K0_C_B 2%nat (pre_jcbf JSraw_jcb_al_2) K0_HT_jc [(52%nat, T_u29)] eq_refl (pre_jcbf_ok TT_r5) eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 2%nat K0_HT_jc K0_C_B 52%nat T_u29 [] 2%nat HS_jc eq_refl eq_refl T_u29_ok). apply mforest_ok_nil. Qed.
Definition T_u27 : mtree := MClass K0_C_B T_u28.
Lemma T_u27_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 ((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) T_u27 = true.
Proof. apply (mtree_ok_class KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 ((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) K0_C_B T_u28); [vm_compute; reflexivity | exact T_u28_ok]. Qed.
Definition T_u32 : mtree := MClass C_K0S T_sec.
Lemma T_u32_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 (((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) T_u32 = true.
Proof. apply (mtree_ok_class KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 (((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) C_K0S T_sec); [vm_compute; reflexivity | exact T_sec_ok]. Qed.
Definition T_u34 : mtree := MEmpty 2.
Lemma T_u34_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 (((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, 65529 + 1, QMAX)]) T_u34 = true.
Proof. apply (mtree_ok_empty KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 (((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, 65529 + 1, QMAX)]) 2%nat); [reflexivity | vm_compute; reflexivity]. Qed.
Definition T_u31 : mtree := MSplit QRoom 65529 T_u32 T_u34.
Lemma T_u31_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 ((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) T_u31 = true.
Proof. exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 ((((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) QRoom 65529 T_u32 T_u34 T_u32_ok T_u34_ok). Qed.
Definition T_u26 : mtree := MSplit QRoom 64512 T_u27 T_u31.
Lemma T_u26_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 (((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) T_u26 = true.
Proof. exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 (((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) QRoom 64512 T_u27 T_u31 T_u27_ok T_u31_ok). Qed.
Definition T_u23 : mtree := MSplit QRoom 0 T_u24 T_u26.
Lemma T_u23_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 ((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) T_u23 = true.
Proof. exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 ((((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) QRoom 0 T_u24 T_u26 T_u24_ok T_u26_ok). Qed.
Definition T_u20 : mtree := MSplit QRoom (-1) T_u21 T_u23.
Lemma T_u20_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 (((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) T_u20 = true.
Proof. exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 (((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QFlen, 64 + 1, QMAX)]) QRoom (-1) T_u21 T_u23 T_u21_ok T_u23_ok). Qed.
Definition T_u7 : mtree := MSplit QFlen 64 T_u8 T_u20.
Lemma T_u7_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 ((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) T_u7 = true.
Proof. exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 ((K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) ++ [(QFlen, 5 + 1, QMAX)]) QFlen 64 T_u8 T_u20 T_u8_ok T_u20_ok). Qed.
Definition T_u4 : mtree := MSplit QFlen 5 T_u5 T_u7.
Lemma T_u4_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 (K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) T_u4 = true.
Proof. exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 (K0_C_FILE ++ [(QFlen, 0 + 1, QMAX)]) QFlen 5 T_u5 T_u7 T_u5_ok T_u7_ok). Qed.
Definition T_u2 : mtree := MSplit QFlen 0 T_u3 T_u4.
Lemma T_u2_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 2 HS_p5 K0_C_FILE T_u2 = true.
Proof. exact (mtree_ok_split KCm BFUELm FUELm ITm TT_r5 0%nat 2%nat HS_p5 K0_C_FILE QFlen 0 T_u3 T_u4 T_u3_ok T_u4_ok). Qed.
Definition T_K0 : mtree := MPre 0 pre_p5f K0_HT_p5 [(42%nat, T_u2)].
Lemma T_K0_ok : mtree_ok KCm BFUELm FUELm ITm TT_r5 0 0 (HSA HS_main 0) K0_C_FILE T_K0 = true.
Proof. unfold T_K0. apply (segb_tree KCm BFUELm FUELm ITm TT_r5 0%nat 0%nat (HSA HS_main 0) K0_C_FILE 0%nat pre_p5f K0_HT_p5 [(42%nat, T_u2)] eq_refl pre_p5f_ok eq_refl).
  apply (mforest_ok_cons KCm BFUELm FUELm ITm TT_r5 0%nat K0_HT_p5 K0_C_FILE 42%nat T_u2 [] 2%nat HS_p5 eq_refl eq_refl T_u2_ok). apply mforest_ok_nil. Qed.
End K0TOP.
