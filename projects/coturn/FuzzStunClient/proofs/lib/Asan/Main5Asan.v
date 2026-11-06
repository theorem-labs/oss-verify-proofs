(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue StartupHSMainAsan ItabAsan W0Lib W0States1 W0States2 W0Plans ArgleafTmplAsan ArgleafContOAllAsan ContOAll5Asan Main5AsanDefs Main5AsanCerts0 Main5AsanCerts1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Section Tree5.
  Variable TPH1 : mtree.
  Hypothesis TPH1_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat HG1_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) TPH1 = true.
Definition t_1 : mtree := (MLeaf 2%nat leaf_s).
Definition t_2 : mtree := (MLeaf 2%nat leaf_v).
Definition t_3 : mtree := (MLeaf 2%nat p0z7).
Definition r_4 : rtree := (RLeaf t_k30).
Definition r_5 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_4).
Definition r_6 : rtree := (RLeaf t_d30lt).
Definition r_7 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_6).
Definition r_8 : rtree := (RLeaf t_k31lt).
Definition r_9 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_8).
Definition r_10 : rtree := (RLeaf t_d31lt).
Definition r_11 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_10).
Definition r_12 : rtree := (RLeaf tsl).
Definition r_13 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 1, 64512)]) r_12).
Definition t_14 : mtree := (MPreS 2%nat p0lt6 HR_5 [(2001%nat, r_7); (2007%nat, r_11); (2100%nat, r_13)]).
Definition r_15 : rtree := (RLeaf t_k30eq).
Definition r_16 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_15).
Definition r_17 : rtree := (RLeaf td30eq).
Definition r_18 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_17).
Definition r_19 : rtree := (RLeaf tk31eq).
Definition r_20 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_19).
Definition r_21 : rtree := (RLeaf td31eq).
Definition r_22 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_21).
Definition r_23 : rtree := (RLeaf tse6).
Definition r_24 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 5889, 7936)]) r_23).
Definition t_25 : mtree := (MPreS 2%nat p0eq6 HR_6 [(2003%nat, r_18); (2009%nat, r_22); (2101%nat, r_24)]).
Definition r_26 : rtree := (RLeaf td30gt).
Definition r_27 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_26).
Definition r_28 : rtree := (RLeaf tk31gt).
Definition r_29 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_28).
Definition r_30 : rtree := (RLeaf td31gt).
Definition r_31 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_30).
Definition t_32 : mtree := (MPreS 2%nat p0gt6 HR_7 [(2002%nat, r_27); (2008%nat, r_31); (2100%nat, r_13)]).
Definition r_33 : rtree := (RLeaf tn_sec).
Definition r_34 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_33).
Definition r_35 : rtree := (RLeaf tssec).
Definition r_36 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 64513, 65529)]) r_35).
Definition t_37 : mtree := (MPreS 2%nat p0sec6 HR_8 [(2011%nat, r_34); (2102%nat, r_36)]).
Definition t_38 : mtree := (MEmpty 2%nat).
Definition t_39 : mtree := (MSplit QRoom 65529 t_37 t_38).
Definition t_40 : mtree := (MSplit QRoom 64512 t_32 t_39).
Definition t_41 : mtree := (MSplit QRoom 7936 t_25 t_40).
Definition t_42 : mtree := (MSplit QRoom 5888 t_14 t_41).
Definition t_43 : mtree := (MSplit QRoom 0 t_3 t_42).
Definition t_44 : mtree := (MSplit QRoom (-1) t_2 t_43).
Definition t_45 : mtree := (MSplit QFlen 5 t_1 t_44).
Definition r_46 : rtree := (RLeaf rep26).
Definition r_47 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_46).
Definition t_48 : mtree := (MPreX 1%nat w0r HT_3 [(10%nat, t_45)] HR_4 [(26%nat, r_47)]).
Definition t_49 : mtree := (MPreX 1%nat w1r HT_9 [(12%nat, TPH1)] HR_4 [(26%nat, r_47)]).
Definition t_50 : mtree := (MSplit QFlen 65535 t_48 t_49).
Definition r_51 : rtree := (RLeaf cont_o_all_asan).
Definition r_52 : rtree := (RClass (C_o_asan) r_51).
Definition t_53 : mtree := (MPreX 0%nat root_opent HT_1 [(1%nat, t_50)] HR_2 [(3%nat, r_52)]).
Lemma seg_13 : class_seg_ok (lv_of HT_1) 0%nat (root_class 5) (subst_holes (rs_ofX HT_1 HR_2) s_12) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_14 : mcover HT_1 [(1%nat, t_50)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_19 : class_seg_ok (lv_of HT_3) 1%nat ((root_class 5) ++ [(QFlen, QMIN, 65535)]) (subst_holes (rs_ofX HT_3 HR_4) s_18) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_20 : mcover HT_3 [(10%nat, t_45)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_25 : class_pay_ok 2%nat (((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, QMIN, 5)]) s_24 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_30 : class_pay_ok 2%nat ((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, QMIN, (-1))]) s_29 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_35 : class_pay_ok 2%nat (((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, QMIN, 0)]) s_34 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_40 : class_pay_ok 2%nat ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) (subst_holes (rs_of HR_5) s_39) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_41 : mcoverS HR_5 [(2001%nat, r_7); (2007%nat, r_11); (2100%nat, r_13)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_43 : class_le ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 1, 64512)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_47 : shape_eqb s_46 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vl_48 : shape_vars_lt NX0 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_50 : class_le ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_54 : shape_eqb s_53 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vl_55 : shape_vars_lt NX0 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_60 : shape_eqb s_59 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_65 : shape_eqb s_64 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_70 : shape_eqb s_69 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_76 : class_pay_ok 2%nat (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) (subst_holes (rs_of HR_6) s_75) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_77 : mcoverS HR_6 [(2003%nat, r_18); (2009%nat, r_22); (2101%nat, r_24)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_79 : class_le (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 5889, 7936)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_83 : shape_eqb s_82 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_85 : class_le (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_89 : shape_eqb s_88 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_94 : shape_eqb s_93 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_99 : shape_eqb s_98 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_104 : shape_eqb s_103 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_110 : class_pay_ok 2%nat ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) (subst_holes (rs_of HR_7) s_109) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_111 : mcoverS HR_7 [(2002%nat, r_27); (2008%nat, r_31); (2100%nat, r_13)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_113 : class_le ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 1, 64512)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_115 : class_le ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_119 : shape_eqb s_118 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_124 : shape_eqb s_123 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_129 : shape_eqb s_128 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_136 : class_pay_ok 2%nat (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) (subst_holes (rs_of HR_8) s_135) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_137 : mcoverS HR_8 [(2011%nat, r_34); (2102%nat, r_36)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_139 : class_le (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 64513, 65529)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_143 : shape_eqb s_142 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_145 : class_le (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_149 : shape_eqb s_148 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_152 : class_empty (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, 65529 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_154 : mcoverS HR_4 [(26%nat, r_47)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_156 : class_le ((root_class 5) ++ [(QFlen, QMIN, 65535)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_160 : shape_eqb s_159 (SNil) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vl_161 : shape_vars_lt NX0 (SNil) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma hf_163 : hr_hole_free HR_4 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_167 : class_seg_ok (lv_of HT_9) 1%nat ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) (subst_holes (rs_ofX HT_9 HR_4) s_166) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_168 : mcover HT_9 [(12%nat, TPH1)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_171 : class_le ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_174 : mcoverS HR_2 [(3%nat, r_52)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_176 : class_le (root_class 5) (C_o_asan) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma hf_179 : hr_hole_free HR_2 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma nd_22 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, QMIN, 5)]) t_1 = true.
Proof. exact (mtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, QMIN, 5)]) 2%nat leaf_s _ eq_refl c_23 pay_25). Qed.
Lemma nd_27 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, QMIN, (-1))]) t_2 = true.
Proof. exact (mtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, QMIN, (-1))]) 2%nat leaf_v _ eq_refl c_28 pay_30). Qed.
Lemma nd_32 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, QMIN, 0)]) t_3 = true.
Proof. exact (mtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, QMIN, 0)]) 2%nat p0z7 _ eq_refl c_33 pay_35). Qed.
Lemma rn_44 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) H2100 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 1, 64512)]) r_12 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_2) H2100 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 1, 64512)]) tsl _ c_45 eq_47 vl_48). Qed.
Lemma rn_42 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) H2100 ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) r_13 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) H2100 ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 1, 64512)]) _ le_43 rn_44). Qed.
Lemma rn_51 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2007 ([(QLook, 4, 4); (QArgc, 2, 2)]) r_10 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2007 ([(QLook, 4, 4); (QArgc, 2, 2)]) t_d31lt _ c_52 eq_54 vl_55). Qed.
Lemma rn_49 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2007 ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) r_11 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2007 ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) _ le_50 rn_51). Qed.
Lemma rn_62 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2001 ([(QLook, 4, 4); (QArgc, 2, 2)]) r_6 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2001 ([(QLook, 4, 4); (QArgc, 2, 2)]) t_d30lt _ c_63 eq_65 vl_55). Qed.
Lemma rn_61 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2001 ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) r_7 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2001 ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) _ le_50 rn_62). Qed.
Lemma rf_71 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_5 ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) [(2001%nat, r_7); (2007%nat, r_11); (2100%nat, r_13)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_5 ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) 2001%nat r_7 _ (rsh_1) H2001 eq_refl rn_61 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_5 ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) 2007%nat r_11 _ (rsh_1) H2007 eq_refl rn_49 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_5 ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) 2100%nat r_13 _ (rsh_2) H2100 eq_refl rn_42 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_5 ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]))))). Qed.
Lemma nd_37 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) t_14 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, QMIN, 5888)]) 2%nat p0lt6 HR_5 [(2001%nat, r_7); (2007%nat, r_11); (2100%nat, r_13)] _ eq_refl c_38 pay_40 covs_41 rf_71). Qed.
Lemma rn_80 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) H2101 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 5889, 7936)]) r_23 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_2) H2101 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 5889, 7936)]) tse6 _ c_81 eq_83 vl_48). Qed.
Lemma rn_78 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) H2101 (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) r_24 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) H2101 (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 5889, 7936)]) _ le_79 rn_80). Qed.
Lemma rn_86 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2009 ([(QLook, 4, 4); (QArgc, 2, 2)]) r_21 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2009 ([(QLook, 4, 4); (QArgc, 2, 2)]) td31eq _ c_87 eq_89 vl_55). Qed.
Lemma rn_84 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2009 (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) r_22 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2009 (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) _ le_85 rn_86). Qed.
Lemma rn_96 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2003 ([(QLook, 4, 4); (QArgc, 2, 2)]) r_17 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2003 ([(QLook, 4, 4); (QArgc, 2, 2)]) td30eq _ c_97 eq_99 vl_55). Qed.
Lemma rn_95 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2003 (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) r_18 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2003 (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) _ le_85 rn_96). Qed.
Lemma rf_105 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_6 (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) [(2003%nat, r_18); (2009%nat, r_22); (2101%nat, r_24)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_6 (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) 2003%nat r_18 _ (rsh_1) H2003 eq_refl rn_95 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_6 (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) 2009%nat r_22 _ (rsh_1) H2009 eq_refl rn_84 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_6 (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) 2101%nat r_24 _ (rsh_2) H2101 eq_refl rn_78 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_6 (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]))))). Qed.
Lemma nd_73 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) t_25 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, QMIN, 7936)]) 2%nat p0eq6 HR_6 [(2003%nat, r_18); (2009%nat, r_22); (2101%nat, r_24)] _ eq_refl c_74 pay_76 covs_77 rf_105). Qed.
Lemma rn_112 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) H2100 ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) r_13 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) H2100 ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 1, 64512)]) _ le_113 rn_44). Qed.
Lemma rn_116 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2008 ([(QLook, 4, 4); (QArgc, 2, 2)]) r_30 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2008 ([(QLook, 4, 4); (QArgc, 2, 2)]) td31gt _ c_117 eq_119 vl_55). Qed.
Lemma rn_114 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2008 ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) r_31 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2008 ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) _ le_115 rn_116). Qed.
Lemma rn_126 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2002 ([(QLook, 4, 4); (QArgc, 2, 2)]) r_26 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2002 ([(QLook, 4, 4); (QArgc, 2, 2)]) td30gt _ c_127 eq_129 vl_55). Qed.
Lemma rn_125 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2002 ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) r_27 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) H2002 ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) _ le_115 rn_126). Qed.
Lemma rf_131 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_7 ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) [(2002%nat, r_27); (2008%nat, r_31); (2100%nat, r_13)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_7 ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) 2002%nat r_27 _ (rsh_1) H2002 eq_refl rn_125 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_7 ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) 2008%nat r_31 _ (rsh_1) H2008 eq_refl rn_114 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_7 ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) 2100%nat r_13 _ (rsh_2) H2100 eq_refl rn_112 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_7 ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]))))). Qed.
Lemma nd_107 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) t_32 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, QMIN, 64512)]) 2%nat p0gt6 HR_7 [(2002%nat, r_27); (2008%nat, r_31); (2100%nat, r_13)] _ eq_refl c_108 pay_110 covs_111 rf_131). Qed.
Lemma rn_140 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) HSEC_S ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 64513, 65529)]) r_35 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_2) HSEC_S ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 64513, 65529)]) tssec _ c_141 eq_143 vl_48). Qed.
Lemma rn_138 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) HSEC_S (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) r_36 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) HSEC_S (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 64513, 65529)]) _ le_139 rn_140). Qed.
Lemma rn_146 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) HSEC_N ([(QLook, 4, 4); (QArgc, 2, 2)]) r_33 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_1) HSEC_N ([(QLook, 4, 4); (QArgc, 2, 2)]) tn_sec _ c_147 eq_149 vl_55). Qed.
Lemma rn_144 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) HSEC_N (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) r_34 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) HSEC_N (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) _ le_145 rn_146). Qed.
Lemma rf_150 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_8 (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) [(2011%nat, r_34); (2102%nat, r_36)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_8 (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) 2011%nat r_34 _ (rsh_1) HSEC_N eq_refl rn_144 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_8 (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) 2102%nat r_36 _ (rsh_2) HSEC_S eq_refl rn_138 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_8 (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)])))). Qed.
Lemma nd_133 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) t_37 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]) 2%nat p0sec6 HR_8 [(2011%nat, r_34); (2102%nat, r_36)] _ eq_refl c_134 pay_136 covs_137 rf_150). Qed.
Lemma nd_151 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, 65529 + 1, QMAX)]) t_38 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, 65529 + 1, QMAX)]) 2%nat eq_refl emp_152). Qed.
Lemma nd_132 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) t_39 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) QRoom 65529 t_37 t_38 nd_133 nd_151). Qed.
Lemma nd_106 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) t_40 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) QRoom 64512 t_32 t_39 nd_107 nd_132). Qed.
Lemma nd_72 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) t_41 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) QRoom 7936 t_25 t_40 nd_73 nd_106). Qed.
Lemma nd_36 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) t_42 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) QRoom 5888 t_14 t_41 nd_37 nd_72). Qed.
Lemma nd_31 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) t_43 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) QRoom 0 t_3 t_42 nd_32 nd_36). Qed.
Lemma nd_26 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) t_44 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s (((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) QRoom (-1) t_2 t_43 nd_27 nd_31). Qed.
Lemma nd_21 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((root_class 5) ++ [(QFlen, QMIN, 65535)]) t_45 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat AR0_s ((root_class 5) ++ [(QFlen, QMIN, 65535)]) QFlen 5 t_1 t_44 nd_22 nd_26). Qed.
Lemma fo_153 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_3 ((root_class 5) ++ [(QFlen, QMIN, 65535)]) [(10%nat, t_45)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_3 ((root_class 5) ++ [(QFlen, QMIN, 65535)]) 10%nat t_45 _ 2%nat AR0_s eq_refl nd_21 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_3 ((root_class 5) ++ [(QFlen, QMIN, 65535)]))). Qed.
Lemma rn_157 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (SNil) REP_s ([(QLook, 4, 4); (QArgc, 2, 2)]) r_46 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (SNil) REP_s ([(QLook, 4, 4); (QArgc, 2, 2)]) rep26 _ c_158 eq_160 vl_161). Qed.
Lemma rn_155 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (SNil) REP_s ((root_class 5) ++ [(QFlen, QMIN, 65535)]) r_47 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (SNil) REP_s ((root_class 5) ++ [(QFlen, QMIN, 65535)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) _ le_156 rn_157). Qed.
Lemma rf_162 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_4 ((root_class 5) ++ [(QFlen, QMIN, 65535)]) [(26%nat, r_47)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_4 ((root_class 5) ++ [(QFlen, QMIN, 65535)]) 26%nat r_47 _ (SNil) REP_s eq_refl rn_155 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_4 ((root_class 5) ++ [(QFlen, QMIN, 65535)]))). Qed.
Lemma nd_16 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat HO_s ((root_class 5) ++ [(QFlen, QMIN, 65535)]) t_48 = true.
Proof. exact (mtree_ok_preX 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat HO_s ((root_class 5) ++ [(QFlen, QMIN, 65535)]) 1%nat w0r HT_3 [(10%nat, t_45)] HR_4 [(26%nat, r_47)] _ eq_refl c_17 seg_19 cov_20 fo_153 covs_154 rf_162 hf_163). Qed.
Lemma fo_169 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_9 ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) [(12%nat, TPH1)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_9 ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) 12%nat TPH1 _ 1%nat HG1_s eq_refl TPH1_ok (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_9 ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]))). Qed.
Lemma rn_170 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (SNil) REP_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) r_47 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (SNil) REP_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2)]) _ le_171 rn_157). Qed.
Lemma rf_172 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_4 ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) [(26%nat, r_47)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_4 ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) 26%nat r_47 _ (SNil) REP_s eq_refl rn_170 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_4 ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]))). Qed.
Lemma nd_164 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat HO_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) t_49 = true.
Proof. exact (mtree_ok_preX 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat HO_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) 1%nat w1r HT_9 [(12%nat, TPH1)] HR_4 [(26%nat, r_47)] _ eq_refl c_165 seg_167 cov_168 fo_169 covs_154 rf_172 hf_163). Qed.
Lemma nd_15 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat HO_s (root_class 5) t_50 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 0%nat 1%nat HO_s (root_class 5) QFlen 65535 t_48 t_49 nd_16 nd_164). Qed.
Lemma fo_173 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat HT_1 (root_class 5) [(1%nat, t_50)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 0%nat HT_1 (root_class 5) 1%nat t_50 _ 1%nat HO_s eq_refl nd_15 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 0%nat HT_1 (root_class 5))). Qed.
Lemma rn_177 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan (C_o_asan) r_51 = true.
Proof. exact (o_leaf_ok). Qed.
Lemma rn_175 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan (root_class 5) r_52 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (cont_o_all_asan_s) TO_asan (root_class 5) (C_o_asan) _ le_176 rn_177). Qed.
Lemma rf_178 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_2 (root_class 5) [(3%nat, r_52)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_2 (root_class 5) 3%nat r_52 _ (cont_o_all_asan_s) TO_asan eq_refl rn_175 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_2 (root_class 5))). Qed.
Lemma nd_10 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 5) t_53 = true.
Proof. exact (mtree_ok_preX 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 5) 0%nat root_opent HT_1 [(1%nat, t_50)] HR_2 [(3%nat, r_52)] _ eq_refl c_11 seg_13 cov_14 fo_173 covs_174 rf_178 hf_179). Qed.
Definition TREE5 : mtree := t_53.
Lemma TREE5_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 5) TREE5 = true.
Proof. exact nd_10. Qed.
End Tree5.
