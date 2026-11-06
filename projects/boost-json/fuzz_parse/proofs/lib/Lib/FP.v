(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv3h5LinuxProcessSemantics5Riscv7Preludek19bvmap_setk15bvmap37Corelib4Init5Logicnb2eqhfbbv_unsigned01Z37Corelib4Init9Datatypesq54boolq55falsek16bv_eqb3h5LinuxProcessSemantics5Riscv3Semt57reg_get46Stdlib6ZArith6BinInt1Zhg14landhg16shiftr3h5LinuxProcessSemantics5Riscv3Fpuhib5rmodeq54Someq56optionhib3RNEhibermode_of_fieldt56c_fcsrt54coret56frm_of79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~hp84frm0hibarmode_of_Zhf7Z_to_bvhibbfflags_bitsnb3andhib6fflagshg12lehg12lthg13lorhg13pownb3iffhg17testbithg16modulot59slice_sett59slice_getq54prodhib6format3h5LinuxProcessSemantics5Riscv5Instrime6fariophib6fp_addhib6fp_divhib6fp_mulhib6fp_subime6fcmpophib5fp_eqhib5fp_lehib5fp_ltq53fsthibafmt_doublehp86fadd_dhp86fdiv_dhp86fmul_dhp86fsub_dhib7fp_sqrthp85feq_dhp85fle_dhp85flt_dt57unbox_shibafmt_singlet57nan_boxhp86fadd_shp86fdiv_shp86fmul_shp86fsub_shp85feq_shp85fle_shp85flt_sq54truehib9fp_to_intk14sexthib9fp_of_inthibafp_converthg14oneshg14lxorq53sndhp88fari_semhp88fcmp_semt54fgetime5FMT_Dime4Fcmpt55EDonet56accruet54c_pct53efft54exect54rsett57with_pchp85bwordhp86fcmp_dhp87fcmp_flhf6bv_addime5FMT_Shp86fcmp_sime4Farit54fsethp86fari_dhp87fari_flhp86fari_sime5Fsqrthp87fsqrt_dime9fminmaxophib9fp_minmaxime7Fminmaxime4FC_Dime4FC_Wime4Fcvthp88fcvt_w_dime5FC_WUhp89fcvt_wu_dime4FC_Lhp88fcvt_l_dime5FC_LUhp89fcvt_lu_dt54rgethp88fcvt_d_whp89fcvt_d_wuhp88fcvt_d_lhp89fcvt_d_luime4FC_Shp88fcvt_s_whp89fcvt_s_wuhp88fcvt_d_shp88fcvt_s_dq54pairt59csr_slicet5h1csr_write_illegalime5csropq54negbt55is_x0ime3Csrt59with_fcsrhf6bv_andhf6bv_nothf5bv_orhg13eqbime4CsrIk14zextime6fsgnopq54xorbt58sgnj_valhp89sgnj_signhg16shiftlq54andbime6F_SGNJime7F_SGNJXhp86fabs_dime7F_SGNJNhp86fneg_dt55low3279OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mt24sx3201N" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tset_tset_same {A} (p : positive) (x y : A) t : tset p x (tset p y t) = tset p x t.
Proof. revert t; induction p; intros [|l v r]; cbn; try rewrite IHp; reflexivity. Qed.

Lemma tset_tset_comm {A} (p q : positive) (x y : A) t :
  p <> q -> tset p x (tset q y t) = tset q y (tset p x t).
Proof.
  revert q t; induction p; intros [q|q|] [|l v r] Hne; cbn; try reflexivity; try congruence;
  try (rewrite IHp by congruence; reflexivity).
Qed.

Lemma bvmap_set_set_same : ltac2:(zQ "50!h9!jc!m7!n3!of>1k@1$1@1$0#5>1x@1$1@1$0#k0>1y@1$1@1$0#k0>1F@2$3@1$0#5@1$1@1$0#k0@3$4@2$3@1$0#5@1$1@1$0#k0@5$2@1$0#5@1$1@1$0#k0^4^3@5$2@1$0#5@1$1@1$0#k0^4^2^1@5$2@1$0#5@1$1@1$0#k0^4^3^1").
Proof. intros. unfold bvmap_set. apply tset_tset_same. Qed.

(* [comment removed for export] *)
Lemma bvmap_set_set_same' : ltac2:(zQ "70!h9!jc!m7!of!n3!p4!q2>1k@1$1@1$0#5>2k'@1$1@1$0#5>1x@1$1@1$0#k0>1y@1$1@1$0#k0>1F@2$4@1$0#5@1$1@1$0#k0>0@3$3$6@2$5@1$0#5^5@2$5@1$0#5^4@3$3@2$4@1$0#5@1$1@1$0#k0@5$2@1$0#5@1$1@1$0#k0^6^4@5$2@1$0#5@1$1@1$0#k0^5^3^2@5$2@1$0#5@1$1@1$0#k0^6^4^2").
Proof. intros k k' x y F H. replace k' with k by (apply bv_eq; exact H). apply bvmap_set_set_same. Qed.

Lemma bvmap_set_set_comm : ltac2:(zQ "80!h9!jc!m7!of!n3!rd!s4!sc>1k@1$1@1$0#5>2k'@1$1@1$0#5>1x@1$1@1$0#k0>1y@1$1@1$0#k0>1F@2$4@1$0#5@1$1@1$0#k0>0@3$3$5@3$7@1$0#5^5^4$6@3$3@2$4@1$0#5@1$1@1$0#k0@5$2@1$0#5@1$1@1$0#k0^6^4@5$2@1$0#5@1$1@1$0#k0^5^3^2@5$2@1$0#5@1$1@1$0#k0^5^3@5$2@1$0#5@1$1@1$0#k0^6^4^2").
Proof.
  intros k k' x y F H. unfold bvmap_set. apply tset_tset_comm.
  intros E. unfold bv_eqb in H. apply Z.eqb_neq in H. apply H.
  pose proof (bv_key_inj k k' E). congruence.
Qed.

Lemma freg_get_same : ltac2:(zQ "80!h9!jc!of!p4!q2!n3!m7!v7>1F@2$5@1$0#5@1$1@1$0#k0>1k@1$1@1$0#5>1r@1$1@1$0#5>1v@1$1@1$0#k0>0@3$2$4@2$3@1$0#5^3@2$3@1$0#5^2@3$2@1$1@1$0#k0@2$7@5$6@1$0#5@1$1@1$0#k0^4^2^5^3^2").
Proof. intros F k r v H. replace r with k by (apply bv_eq; exact H). apply reg_get_set_same. Qed.

Lemma freg_get_other : ltac2:(zQ "90!h9!jc!of!v7!rd!s4!sc!n3!m7>1F@2$7@1$0#5@1$1@1$0#k0>1k@1$1@1$0#5>1r@1$1@1$0#5>1v@1$1@1$0#k0>0@3$2$4@3$6@1$0#5^3^2$5@3$2@1$1@1$0#k0@2$3@5$8@1$0#5@1$1@1$0#k0^4^2^5^3@2$3^5^3").
Proof.
  intros F k r v H. apply reg_get_set_other. unfold bv_eqb in H. apply Z.eqb_neq in H.
  intros E. apply H. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition frm0 : ltac2:(zQ "20!h9!jc>2fc@1$1@1$0#i0P") := ltac2:(zQ "70!h9!of!q2!hh9!hi1!jc!p4\2fc@1$5@1$0#i0@3$1$2@2$3@2$4@2$6@1$0#i0^1+5+7Z").

Lemma rmode_dyn : ltac2:(zQ "e0!h9!of!hkd!p4!hl6!hld!q2!hm6!hmd!hnf!ho8!hof!ht1!jc>2rm@1$d@1$0#3>1c$a>0@3$1$6@2$3@1$0#3^2+7>0@1$c@1$9^2@3$1@1$5$2@2$8@2$3@1$0#3^4@1$b^3@2$4$2$7").
Proof. intros rm c Hrm H. unfold rmode_of_field, frm_of. rewrite Hrm. cbn [Z.eqb Pos.eqb]. unfold frm0 in H. rewrite H. reflexivity. Qed.

Lemma rmode_static : ltac2:(zQ "f0!h9!hkd!of!hl6!hld!p4!rd!s4!ht9!hmd!sc!ho8!hof!hu7!jc>2rm@1$e@1$0#3>1c$b>2md$1>0@3$2$6@3$a@1$0#3^3@2$d@1$0#3+7$7>0@3$2@1$4$1@1$8@2$5@1$0#3^4@2$3$1^2@3$2@1$4$1@2$9@2$5@1$0#3^5@1$c^4@2$3$1^3").
Proof.
  intros rm c md H Hmd. unfold rmode_of_field. unfold bv_eqb in H.
  change (bv_unsigned (Z_to_bv 3 7)) with 7%Z in H. rewrite H. exact Hmd.
Qed.

Lemma fflags_bits_range : ltac2:(zQ "50!hv1!ig0!ig6!ih0!ih6>2fl$2@2$1@2$3Z@1$0^1@2$4@1$0^1+i0").
Proof. intros [[] [] [] [] []]; cbv; split; congruence. Qed.

Lemma land_shiftr_lor_low : ltac2:(zQ "90!q2!ih0!hh9!hi1!ig0!of!ihc!ih6!ii3>1a$0>1b$0>1k$0>1n$0>0@2$1Z^4>0@2$4@2$1Z^4@2$7^4@2$8+2^3>0@2$1Z^4>0@2$1Z^4@3$5$0@2$2@2$3@2$6^8^7^6^5@2$2@2$3^8^6^5").
Proof.
  intros a b k n Ha Hb Hk Hn. apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, !Z.shiftr_spec, Z.lor_spec by lia.
  replace (Z.testbit b (i + k)) with false. { rewrite orb_false_r. reflexivity. }
  symmetry. destruct (Z.eq_dec b 0). { subst. apply Z.bits_0. }
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma Z_lor_lt_pow2 : ltac2:(zQ "60!ig0!q2!ih0!ih6!ii3!ihc>1a$1>1b$1>1n$1>0@2$0@2$2Z^3@2$3^3@2$4+2^1>0@2$0@2$2Z^3@2$3^3@2$4+2^2@2$0@2$2Z@2$5^5^4@2$3@2$5^5^4@2$4+2^3").
Proof.
  intros a b n Ha Hb.
  assert (Hn : (0 <= n)%Z). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  split. { apply Z.lor_nonneg; lia. }
  destruct (Z.eq_dec a 0). { subst. rewrite Z.lor_0_l. lia. }
  destruct (Z.eq_dec b 0). { subst. rewrite Z.lor_0_r. lia. }
  assert (Hp : (0 < Z.lor a b)%Z). { pose proof (Z.lor_nonneg a b). destruct (Z.eq_dec (Z.lor a b) 0); [|lia]. apply Z.lor_eq_0_iff in e. lia. }
  apply Z.log2_lt_pow2; [exact Hp|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma frm0_accrue : ltac2:(zQ "80!h9!ht1!ig6!hv1!ihc!hu7!jc!p4>2fc@1$6@1$0#i0>2fl$2>0@1$1^2@1$1@2$5@1$0#i0@2$4@2$7@1$0#i0^3@1$3^2").
Proof.
  intros fc fl H. unfold frm0 in *.
  pose proof (bv_unsigned_in_range 32 fc) as Hf. unfold bv_modulus in Hf.
  pose proof (fflags_bits_range fl) as Hb.
  assert (HR : (0 <= Z.lor (bv_unsigned fc) (fflags_bits fl) < 2^32)%Z).
  { apply Z_lor_lt_pow2; lia. }
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  rewrite land_shiftr_lor_low by lia. exact H.
Qed.

Lemma land7_shiftr5_zero_iff : ltac2:(zQ "a0!q2!ih0!of!rd!s4!ig0!iia!hh9!hi1!ij0>1z$0>0@2$1Z^1@2$6@3$2$0@2$7@2$8^2+5+7Z>1i$0>0@2$5@2$1+5^1@2$1^1+7@3$2$3@2$9^4^2$4").
Proof.
  intros z Hz. change 7%Z with (Z.ones 3) at 1. split.
  - intros H i Hi. apply (f_equal (fun x => Z.testbit x (i - 5))) in H.
    rewrite Z.bits_0, Z.land_spec, Z.shiftr_spec, Z.ones_spec_low in H by lia.
    rewrite andb_true_r in H. replace (i - 5 + 5)%Z with i in H by lia. exact H.
  - intros H. apply Z.bits_inj'. intros j Hj. rewrite Z.bits_0, Z.land_spec, Z.shiftr_spec by lia.
    destruct (Z.ltb_spec0 j 3).
    + rewrite H by lia. reflexivity.
    + rewrite Z.ones_spec_high by lia. apply andb_false_r.
Qed.

Lemma testbit_mod_pow2_low : ltac2:(zQ "90!q2!ij0!rd!ig0!of!ih0!ih6!ijb!ii3>1z$0>1n$0>1i$0>0@2$3@2$5Z^1@2$6^1^2@3$4$2@2$1@2$7^4@2$8+2^3^2@2$1^4^2").
Proof. intros. rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_low by lia. apply andb_true_r. Qed.

(* [comment removed for export] *)
Lemma frm0_slice_set_fflags : ltac2:(zQ "40!h9!ht1!jc!ik5>2fc@1$2@1$0#i0>1v@1$2@1$0#k0>0@1$1^2@1$1@4$3^3Z+5^2").
Proof.
  intros fc v H. unfold frm0, slice_set in *.
  pose proof (bv_unsigned_in_range 32 fc) as Hf. unfold bv_modulus in Hf.
  rewrite Z_to_bv_unsigned. change (bv_wrap 32 ?x) with (x mod 2^32)%Z.
  apply land7_shiftr5_zero_iff. { apply Z.mod_pos_bound. lia. }
  pose proof (proj1 (land7_shiftr5_zero_iff (bv_unsigned fc) ltac:(lia)) H) as H'.
  intros i Hi. rewrite testbit_mod_pow2_low by lia.
  change (Z.shiftl (Z.ones 5) 0) with 31%Z.
  rewrite Z.lor_spec, !Z.land_spec, Z.lnot_spec by lia. rewrite H' by lia.
  change 31%Z with (Z.ones 5). rewrite Z.ones_spec_high by lia. cbn. apply andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma frm0_slice_get : ltac2:(zQ "60!h9!jc!of!il1!ht1!hu7>2fc@1$1@1$0#i0>0@1$4^1@3$2@1$1@1$0#k0@3$3^2+5+3@2$5@1$0#k0Z").
Proof. intros fc H. unfold slice_get. change (Z.ones 3) with 7%Z. unfold frm0 in H. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fari_sem : ltac2:(zQ "60!q2!ild!ig6!im4!hkd!ip2>2op$5>0$3>0$4>0$0>0$0@2$1$0$2") := ltac2:(zQ "a0!q2!ip2!ild!ig6!im4!ipc!iq6!ir0!ira!hkd\2op$1M1\2op$1>0$4>0$9>0$0>0$0@2$2$0$3^1$5$8$7$6").
Definition fcmp_sem : ltac2:(zQ "60!q2!rd!ild!ig6!im4!is4>2op$5>0$4>0$0>0$0@2$2$1$3") := ltac2:(zQ "90!is4!q2!rd!ild!ig6!im4!ise!it7!iu0\2op$0M0\2op$0>0$5>0$1>0$1@2$3$2$4^1$6$8$7").

(* [comment removed for export] *)
Definition fadd_d : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "a0!h9!jc!p4!iu9!q2!ig6!iuf!ipc!hkd!hu7\2md$8\1a@1$1@1$0#k0\1b@1$1@1$0#k0@2$9@1$0#k0@3$3$4$5@4$7$6^3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition fsub_d : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "a0!h9!jc!p4!iu9!q2!ig6!iuf!ira!hkd!hu7\2md$8\1a@1$1@1$0#k0\1b@1$1@1$0#k0@2$9@1$0#k0@3$3$4$5@4$7$6^3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition fmul_d : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "a0!h9!jc!p4!iu9!q2!ig6!iuf!ir0!hkd!hu7\2md$8\1a@1$1@1$0#k0\1b@1$1@1$0#k0@2$9@1$0#k0@3$3$4$5@4$7$6^3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition fdiv_d : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "a0!h9!jc!p4!iu9!q2!ig6!iuf!iq6!hkd!hu7\2md$8\1a@1$1@1$0#k0\1b@1$1@1$0#k0@2$9@1$0#k0@3$3$4$5@4$7$6^3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition fari_d : ltac2:(zQ "40!h9!jc!hkd!ip2>2op$3>0$2>0@1$1@1$0#k0>0@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "80!h9!ip2!jc!hkd!ivd!jg7!jh1!jhb\2op$1M1\2op$1>0$3>0@1$2@1$0#k0>0@1$2@1$0#k0@1$2@1$0#k0^1$4$7$6$5").
Definition fsqrt_d : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "a0!h9!iu9!q2!ig6!iuf!ji5!hkd!hu7!jc!p4\2md$6\1a@1$8@1$0#k0@2$7@1$0#k0@3$1$2$3@3$5$4^2@2$9@1$0#k0^1").

Definition feq_d : ltac2:(zQ "30!h9!jc!rd>1a@1$1@1$0#k0>1b@1$1@1$0#k0$2") := ltac2:(zQ "80!h9!jc!p4!rd!iu9!ig6!iuf!ise\1a@1$1@1$0#k0\1b@1$1@1$0#k0@3$4$3$5@3$7$6@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition flt_d : ltac2:(zQ "30!h9!jc!rd>1a@1$1@1$0#k0>1b@1$1@1$0#k0$2") := ltac2:(zQ "80!h9!jc!p4!rd!iu9!ig6!iuf!iu0\1a@1$1@1$0#k0\1b@1$1@1$0#k0@3$4$3$5@3$7$6@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition fle_d : ltac2:(zQ "30!h9!jc!rd>1a@1$1@1$0#k0>1b@1$1@1$0#k0$2") := ltac2:(zQ "80!h9!jc!p4!rd!iu9!ig6!iuf!it7\1a@1$1@1$0#k0\1b@1$1@1$0#k0@3$4$3$5@3$7$6@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition fcmp_d : ltac2:(zQ "40!h9!jc!rd!is4>2op$3>0@1$1@1$0#k0>0@1$1@1$0#k0$2") := ltac2:(zQ "70!is4!h9!jc!rd!jj0!jj9!jk2\2op$0M0\2op$0>0@1$2@1$1#k0>0@1$2@1$1#k0$3^1$4$6$5").

(* [comment removed for export] *)
Definition fadd_s : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "c0!h9!jkb!jc!p4!iu9!q2!ig6!jl5!ipc!hkd!jm3!hu7\2md$9\1a@1$2@1$0#k0\1b@1$2@1$0#k0@1$a@2$b@1$0#i0@3$4$5$6@4$8$7^3@2$3@1$0#i0@1$1^2@2$3@1$0#i0@1$1^1").
Definition fsub_s : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "c0!h9!jkb!jc!p4!iu9!q2!ig6!jl5!ira!hkd!jm3!hu7\2md$9\1a@1$2@1$0#k0\1b@1$2@1$0#k0@1$a@2$b@1$0#i0@3$4$5$6@4$8$7^3@2$3@1$0#i0@1$1^2@2$3@1$0#i0@1$1^1").
Definition fmul_s : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "c0!h9!jkb!jc!p4!iu9!q2!ig6!jl5!ir0!hkd!jm3!hu7\2md$9\1a@1$2@1$0#k0\1b@1$2@1$0#k0@1$a@2$b@1$0#i0@3$4$5$6@4$8$7^3@2$3@1$0#i0@1$1^2@2$3@1$0#i0@1$1^1").
Definition fdiv_s : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0>1b@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "c0!h9!jkb!jc!p4!iu9!q2!ig6!jl5!iq6!hkd!jm3!hu7\2md$9\1a@1$2@1$0#k0\1b@1$2@1$0#k0@1$a@2$b@1$0#i0@3$4$5$6@4$8$7^3@2$3@1$0#i0@1$1^2@2$3@1$0#i0@1$1^1").
Definition fari_s : ltac2:(zQ "40!h9!jc!hkd!ip2>2op$3>0$2>0@1$1@1$0#k0>0@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "80!h9!ip2!jc!hkd!jmd!jn7!jo1!job\2op$1M1\2op$1>0$3>0@1$2@1$0#k0>0@1$2@1$0#k0@1$2@1$0#k0^1$4$7$6$5").
Definition feq_s : ltac2:(zQ "30!h9!jc!rd>1a@1$1@1$0#k0>1b@1$1@1$0#k0$2") := ltac2:(zQ "90!h9!jkb!jc!p4!rd!iu9!ig6!jl5!ise\1a@1$2@1$0#k0\1b@1$2@1$0#k0@3$5$4$6@3$8$7@2$3@1$0#i0@1$1^2@2$3@1$0#i0@1$1^1").
Definition flt_s : ltac2:(zQ "30!h9!jc!rd>1a@1$1@1$0#k0>1b@1$1@1$0#k0$2") := ltac2:(zQ "90!h9!jkb!jc!p4!rd!iu9!ig6!jl5!iu0\1a@1$2@1$0#k0\1b@1$2@1$0#k0@3$5$4$6@3$8$7@2$3@1$0#i0@1$1^2@2$3@1$0#i0@1$1^1").
Definition fle_s : ltac2:(zQ "30!h9!jc!rd>1a@1$1@1$0#k0>1b@1$1@1$0#k0$2") := ltac2:(zQ "90!h9!jkb!jc!p4!rd!iu9!ig6!jl5!it7\1a@1$2@1$0#k0\1b@1$2@1$0#k0@3$5$4$6@3$8$7@2$3@1$0#i0@1$1^2@2$3@1$0#i0@1$1^1").
Definition fcmp_s : ltac2:(zQ "40!h9!jc!rd!is4>2op$3>0@1$1@1$0#k0>0@1$1@1$0#k0$2") := ltac2:(zQ "70!is4!h9!jc!rd!jp5!jpe!jq7\2op$0M0\2op$0>0@1$2@1$1#k0>0@1$2@1$1#k0$3^1$4$6$5").

(* [comment removed for export] *)
Definition bword : ltac2:(zQ "30!rd!h9!jc>1b$0@1$2@1$1#k0") := ltac2:(zQ "40!rd!h9!hu7!jc\1b$0M0\1b$0@1$3@1$1#k0^1@2$2@1$1#k0+1@2$2@1$1#k0Z").

(* [comment removed for export] *)
Definition fcvt_w_d : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "c0!h9!iu9!jr0!q2!ig6!iuf!jr7!hkd!js4!hu7!jc!p4\2md$7\1a@1$a@1$0#k0@3$8@1$0#i0@1$0#k0@2$9@1$0#i0@3$1$3$4@5$6$5^2$2+i0@2$b@1$0#k0^1").
Definition fcvt_wu_d : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "c0!h9!s4!iu9!q2!ig6!iuf!jr7!hkd!js4!hu7!jc!p4\2md$7\1a@1$a@1$0#k0@3$8@1$0#i0@1$0#k0@2$9@1$0#i0@3$2$3$4@5$6$5^2$1+i0@2$b@1$0#k0^1").
Definition fcvt_l_d : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "b0!h9!iu9!jr0!q2!ig6!iuf!jr7!hkd!hu7!jc!p4\2md$7\1a@1$9@1$0#k0@2$8@1$0#k0@3$1$3$4@5$6$5^2$2+k0@2$a@1$0#k0^1").
Definition fcvt_lu_d : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "b0!h9!s4!iu9!q2!ig6!iuf!jr7!hkd!hu7!jc!p4\2md$7\1a@1$9@1$0#k0@2$8@1$0#k0@3$2$3$4@5$6$5^2$1+k0@2$a@1$0#k0^1").
(* [comment removed for export] *)
Definition fcvt_d_w : ltac2:(zQ "30!h9!jc!hkd>2md$2>1x@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "b0!h9!iu9!jr0!q2!ig6!iuf!jsb!hkd!hu7!jc!p4\2md$7\1x@1$9@1$0#k0@2$8@1$0#k0@3$1$3$4@5$6$5^2$2+i0@2$a@1$0#k0^1").
Definition fcvt_d_wu : ltac2:(zQ "30!h9!jc!hkd>2md$2>1x@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "b0!h9!s4!iu9!q2!ig6!iuf!jsb!hkd!hu7!jc!p4\2md$7\1x@1$9@1$0#k0@2$8@1$0#k0@3$2$3$4@5$6$5^2$1+i0@2$a@1$0#k0^1").
Definition fcvt_d_l : ltac2:(zQ "30!h9!jc!hkd>2md$2>1x@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "b0!h9!iu9!jr0!q2!ig6!iuf!jsb!hkd!hu7!jc!p4\2md$7\1x@1$9@1$0#k0@2$8@1$0#k0@3$1$3$4@5$6$5^2$2+k0@2$a@1$0#k0^1").
Definition fcvt_d_lu : ltac2:(zQ "30!h9!jc!hkd>2md$2>1x@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "b0!h9!s4!iu9!q2!ig6!iuf!jsb!hkd!hu7!jc!p4\2md$7\1x@1$9@1$0#k0@2$8@1$0#k0@3$2$3$4@5$6$5^2$1+k0@2$a@1$0#k0^1").
Definition fcvt_s_w : ltac2:(zQ "30!h9!jc!hkd>2md$2>1x@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "c0!h9!iu9!jr0!q2!ig6!jl5!jsb!hkd!jm3!hu7!jc!p4\2md$7\1x@1$a@1$0#k0@1$8@2$9@1$0#i0@3$1$3$4@5$6$5^2$2+i0@2$b@1$0#k0^1").
Definition fcvt_s_wu : ltac2:(zQ "30!h9!jc!hkd>2md$2>1x@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "c0!h9!s4!iu9!q2!ig6!jl5!jsb!hkd!jm3!hu7!jc!p4\2md$7\1x@1$a@1$0#k0@1$8@2$9@1$0#i0@3$2$3$4@5$6$5^2$1+i0@2$b@1$0#k0^1").
(* [comment removed for export] *)
Definition fcvt_d_s : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "c0!h9!iu9!q2!ig6!iuf!jl5!jt8!hkd!jkb!hu7!jc!p4\2md$7\1a@1$a@1$0#k0@2$9@1$0#k0@3$1$2$3@4$6$5$4^2@2$b@1$0#i0@1$8^1").
Definition fcvt_s_d : ltac2:(zQ "30!h9!jc!hkd>2md$2>1a@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "c0!h9!iu9!q2!ig6!iuf!jl5!jt8!hkd!jm3!hu7!jc!p4\2md$7\1a@1$a@1$0#k0@1$8@2$9@1$0#i0@3$1$2$3@4$6$4$5^2@2$b@1$0#k0^1").

(* [comment removed for export] *)
Definition fabs_d : ltac2:(zQ "20!h9!jc>1a@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!hh9!ju6!hu7!jc!p4\1a@1$4@1$0#k0@2$3@1$0#k0@2$1@2$5@1$0#k0^1@1$2+jf").
Definition fneg_d : ltac2:(zQ "20!h9!jc>1a@1$1@1$0#k0@1$1@1$0#k0") := ltac2:(zQ "60!h9!jue!ii3!hu7!jc!p4\1a@1$4@1$0#k0@2$3@1$0#k0@2$1@2$5@1$0#k0^1@2$2+2+jf").

(* [comment removed for export] *)
Definition fari_fl : ltac2:(zQ "50!q2!ig6!im4!hkd!ip2>2op$4>1f$2>2md$3>1a$0>1b$0$1") := ltac2:(zQ "70!q2!jv6!ig6!im4!hkd!ip2!jvc\2op$5\1f$3\2md$4\1a$0\1b$0@3$1$0$2@5$6^5^4^3^2^1").
Definition fcmp_fl : ltac2:(zQ "40!q2!ig6!im4!is4>2op$3>1f$2>1a$0>1b$0$1") := ltac2:(zQ "70!q2!rd!jv6!ig6!im4!is4!kg8\2op$5\1f$4\1a$0\1b$0@3$2$1$3@4$6^4^3^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma exec_fcmp_d : ltac2:(zQ "h50!h9!kh4!jc!p4!of!iuf!khb!ki4!is4!kic!kj4!kjd!ho8!kk4!kka!kl1!kl8!km2!kmb!kn5!ko0>2sz@1$2@1$0#k0>2op$8>2rd@1$2@1$0#5>3rs1@1$2@1$0#5>3rs2@1$2@1$0#5>1c$c@3$4$d@3$e^6@5$7^5$6^4^3^2^1@1$9@3$f^4@1$h1@3$h2^5@2$1^1^3@2$1^1^2@2$a@4$h3^5$5@2$3@1$0#k0@2$1^1^3@2$3@1$0#k0@2$1^1^2@2$h0@3$h4@1$0#k0@1$b^1^6^1").
Proof.
  intros. unfold exec. cbn [fp_format fread].
  unfold fcmp_d, fcmp_fl, feq_d, flt_d, fle_d, fcmp_sem, bword.
  destruct op; [destruct (fp_eq _ _ _)|destruct (fp_lt _ _ _)|destruct (fp_le _ _ _)]; reflexivity.
Qed.

Lemma exec_fcmp_s : ltac2:(zQ "h60!h9!kh4!jc!jkb!p4!of!jl5!ko9!ki4!is4!kic!kj4!kjd!ho8!kk4!kka!kl1!kl8!km2!kn5!kp2!ko0>2sz@1$2@1$0#k0>2op$9>2rd@1$2@1$0#5>3rs1@1$2@1$0#5>3rs2@1$2@1$0#5>1c$d@3$5$e@3$f^6@5$8^5$7^4^3^2^1@1$a@3$h0^4@1$h2@3$h4^5@2$1^1^3@2$1^1^2@2$b@4$h3^5$6@2$4@1$0#i0@1$3@2$1^1^3@2$4@1$0#i0@1$3@2$1^1^2@2$h1@3$h5@1$0#k0@1$c^1^6^1").
Proof.
  intros. unfold exec. cbn [fp_format fread].
  unfold fcmp_s, fcmp_fl, feq_s, flt_s, fle_s, fcmp_sem, bword.
  destruct op; [destruct (fp_eq _ _ _)|destruct (fp_lt _ _ _)|destruct (fp_le _ _ _)]; reflexivity.
Qed.

Lemma exec_fari_d : ltac2:(zQ "h90!h9!jc!kh4!hkd!p4!of!hl6!hld!iuf!hmd!khb!kpc!ip2!kic!kj4!kjd!ho8!kk4!kka!hof!kq4!kl8!kqb!kr5!ko0>2sz@1$1@1$0#k0>2op$c>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>2rm@1$1@1$0#3>1c$h0>2md$3>0@3$5@1$7$3@2$9@2$4@1$0#3^3@1$h3^2@2$6$3^1@3$5$h1@3$h2^9@6$b^8$a^7^6^5^4^3@1$d@3$h4^7@4$h6^8^2@2$2^3^6@2$2^3^5@2$e@5$h7^8$8^2@2$4@1$0#k0@2$2^3^6@2$4@1$0#k0@2$2^3^5@2$h5@3$h8@1$0#k0@1$f^3^9^3").
Proof.
  intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
  cbn [fp_format fread fwrite].
  unfold fari_d, fari_fl, fadd_d, fsub_d, fmul_d, fdiv_d, fari_sem.
  destruct op; [destruct (fp_add _ _ _ _)|destruct (fp_sub _ _ _ _)|destruct (fp_mul _ _ _ _)|destruct (fp_div _ _ _ _)]; reflexivity.
Qed.

Lemma exec_fari_s : ltac2:(zQ "ha0!h9!jc!kh4!hkd!p4!of!jkb!hl6!hld!jl5!hmd!ko9!kpc!ip2!kic!kj4!kjd!ho8!kk4!kka!hof!kq4!kl8!kr5!ks0!ko0>2sz@1$1@1$0#k0>2op$d>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>2rm@1$1@1$0#3>1c$h1>2md$3>0@3$5@1$8$3@2$a@2$4@1$0#3^3@1$h4^2@2$7$3^1@3$5$h2@3$h3^9@6$c^8$b^7^6^5^4^3@1$e@3$h5^7@4$h8^8^2@2$2^3^6@2$2^3^5@2$f@5$h7^8$9^2@2$4@1$0#i0@1$6@2$2^3^6@2$4@1$0#i0@1$6@2$2^3^5@2$h6@3$h9@1$0#k0@1$h0^3^9^3").
Proof.
  intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
  cbn [fp_format fread fwrite].
  unfold fari_s, fari_fl, fadd_s, fsub_s, fmul_s, fdiv_s, fari_sem.
  destruct op; [destruct (fp_add _ _ _ _)|destruct (fp_sub _ _ _ _)|destruct (fp_mul _ _ _ _)|destruct (fp_div _ _ _ _)]; reflexivity.
Qed.

Lemma exec_fsqrt_d : ltac2:(zQ "hb0!h9!jc!hkd!of!kh4!p4!hl6!hld!jv6!q2!ig6!iuf!ji5!hmd!khb!ksa!kic!kj4!kjd!ho8!kk4!kka!hof!kq4!kl8!kt3!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h3>2md$2>0@3$3@1$7$2@2$d@2$5@1$0#3^3@1$h6^2@2$6$2^1@3$3$h4@3$h5^7@4$f$e^6^5^4^3@1$h0@3$h7^6@2$h9^2@2$4^3^5@2$h1@3$8$9$a@3$c$b^2@2$5@1$0#k0@2$4^3^5@2$h8@3$ha@1$0#k0@1$h2^3^7^3").
Proof.
  intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
  cbn [fp_format fread fwrite]. unfold fsqrt_d. destruct (fp_sqrt _ _ _); reflexivity.
Qed.

Lemma exec_fminmax_d : ltac2:(zQ "hc0!h9!jc!q2!ig6!kte!kh4!p4!rd!s4!iu9!ild!jv6!jr0!of!iuf!kub!khb!kv8!kic!kj4!kjd!ho8!kk4!kka!kq4!kl8!hu7!ko0>2sz@1$1@1$0#k0>2op$4>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3rs2@1$1@1$0#5>1c$h5@3$d$h6@3$h7^6@5$h1^5$h0^4^3^2^1=1r@2$a$2$3@4$f$eM4\2op$4$7^5$8$c@2$6@1$0#k0@2$5^1^3@2$6@1$0#k0@2$5^1^2@1$h2@3$h8^5@2$ha@1$0#k0@3$9$2$3^1@2$h3@3$b$2$3^1@2$h9@3$hb@1$0#k0@1$h4^2^7^2").
Proof. intros. unfold exec. cbn [fp_format fread fwrite]. destruct (fp_minmax _ _ _ _); reflexivity. Qed.

(* [comment removed for export] *)
Ltac fcvt_tac H :=
  unfold exec, resolve_rm; unfold frm_of in *; cbn [c_fcsr with_pc]; rewrite H;
  cbn [fp_format fread fwrite Z.eqb Pos.eqb];
  first [ destruct (fp_to_int _ _ _ _ _); reflexivity
        | destruct (fp_of_int _ _ _ _ _); reflexivity
        | destruct (fp_convert _ _ _ _); reflexivity ].

Lemma exec_fcvt_w_d : ltac2:(zQ "hd0!h9!jc!hkd!of!kh4!p4!hl6!hld!jv6!jr0!q2!ig6!iuf!jr7!hmd!lg3!lgb!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kl1!kl8!lhb!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$7$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$h0$f^6^5^4^3@1$h2@3$h9^6@2$hb^2@2$4^3^5@2$h3@3$8$a$b@5$d$c^2$9+i0@2$5@1$0#k0@2$4^3^5@2$ha@3$hc@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_w_d. fcvt_tac H. Qed.
Lemma exec_fcvt_wu_d : ltac2:(zQ "hd0!h9!jc!hkd!of!kh4!p4!hl6!s4!hld!jv6!q2!ig6!iuf!jr7!hmd!lg3!li7!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kl1!kl8!lj0!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$8$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$h0$f^6^5^4^3@1$h2@3$h9^6@2$hb^2@2$4^3^5@2$h3@3$9$a$b@5$d$c^2$7+i0@2$5@1$0#k0@2$4^3^5@2$ha@3$hc@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_wu_d. fcvt_tac H. Qed.
Lemma exec_fcvt_l_d : ltac2:(zQ "hd0!h9!jc!hkd!of!kh4!p4!hl6!hld!jv6!jr0!q2!ig6!iuf!jr7!hmd!lg3!ljd!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kl1!kl8!lk5!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$7$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$h0$f^6^5^4^3@1$h2@3$h9^6@2$hb^2@2$4^3^5@2$h3@3$8$a$b@5$d$c^2$9+k0@2$5@1$0#k0@2$4^3^5@2$ha@3$hc@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_l_d. fcvt_tac H. Qed.
Lemma exec_fcvt_lu_d : ltac2:(zQ "hd0!h9!jc!hkd!of!kh4!p4!hl6!s4!hld!jv6!q2!ig6!iuf!jr7!hmd!lg3!ll1!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kl1!kl8!lla!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$8$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$h0$f^6^5^4^3@1$h2@3$h9^6@2$hb^2@2$4^3^5@2$h3@3$9$a$b@5$d$c^2$7+k0@2$5@1$0#k0@2$4^3^5@2$ha@3$hc@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_lu_d. fcvt_tac H. Qed.
Lemma exec_fcvt_d_w : ltac2:(zQ "hd0!h9!jc!hkd!of!lm7!p4!hl6!hld!jv6!jr0!q2!ig6!iuf!jsb!hmd!lg3!lgb!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kq4!kl8!lme!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$7$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$f$h0^6^5^4^3@1$h2@3$h9^6@2$hb^2@2$4^3^5@2$h3@3$8$a$b@5$d$c^2$9+i0@2$5@1$0#k0@2$4^3^5@2$ha@3$hc@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_d_w. fcvt_tac H. Qed.
Lemma exec_fcvt_d_wu : ltac2:(zQ "hd0!h9!jc!hkd!of!lm7!p4!hl6!s4!hld!jv6!q2!ig6!iuf!jsb!hmd!lg3!li7!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kq4!kl8!lna!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$8$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$f$h0^6^5^4^3@1$h2@3$h9^6@2$hb^2@2$4^3^5@2$h3@3$9$a$b@5$d$c^2$7+i0@2$5@1$0#k0@2$4^3^5@2$ha@3$hc@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_d_wu. fcvt_tac H. Qed.
Lemma exec_fcvt_d_l : ltac2:(zQ "hd0!h9!jc!hkd!of!lm7!p4!hl6!hld!jv6!jr0!q2!ig6!iuf!jsb!hmd!lg3!ljd!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kq4!kl8!lo7!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$7$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$f$h0^6^5^4^3@1$h2@3$h9^6@2$hb^2@2$4^3^5@2$h3@3$8$a$b@5$d$c^2$9+k0@2$5@1$0#k0@2$4^3^5@2$ha@3$hc@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_d_l. fcvt_tac H. Qed.
Lemma exec_fcvt_d_lu : ltac2:(zQ "hd0!h9!jc!hkd!of!lm7!p4!hl6!s4!hld!jv6!q2!ig6!iuf!jsb!hmd!lg3!ll1!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kq4!kl8!lp3!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$8$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$f$h0^6^5^4^3@1$h2@3$h9^6@2$hb^2@2$4^3^5@2$h3@3$9$a$b@5$d$c^2$7+k0@2$5@1$0#k0@2$4^3^5@2$ha@3$hc@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_d_lu. fcvt_tac H. Qed.
Lemma exec_fcvt_s_w : ltac2:(zQ "hd0!h9!jc!hkd!of!lm7!p4!hl6!hld!jv6!jr0!q2!ig6!jl5!jsb!hmd!lq0!lgb!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kq4!kl8!lq8!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$7$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$f$h0^6^5^4^3@1$h2@3$h9^6@2$hb^2@2$4^3^5@2$h3@3$8$a$b@5$d$c^2$9+i0@2$5@1$0#k0@2$4^3^5@2$ha@3$hc@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_s_w. fcvt_tac H. Qed.
Lemma exec_fcvt_s_wu : ltac2:(zQ "hd0!h9!jc!hkd!of!lm7!p4!hl6!s4!hld!jv6!q2!ig6!jl5!jsb!hmd!lq0!li7!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kq4!kl8!lr4!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$8$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$f$h0^6^5^4^3@1$h2@3$h9^6@2$hb^2@2$4^3^5@2$h3@3$9$a$b@5$d$c^2$7+i0@2$5@1$0#k0@2$4^3^5@2$ha@3$hc@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_s_wu. fcvt_tac H. Qed.
Lemma exec_fcvt_d_s : ltac2:(zQ "he0!h9!jc!hkd!of!kh4!p4!hl6!hld!jv6!q2!ig6!iuf!jl5!jt8!hmd!lg3!lq0!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kq4!jkb!kl8!ls1!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$7$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$f$h0^6^5^4^3@1$h2@3$h9^6@2$hc^2@2$4^3^5@2$h3@3$8$9$a@4$d$c$b^2@2$5@1$0#i0@1$ha@2$4^3^5@2$hb@3$hd@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_d_s. fcvt_tac H. Qed.
Lemma exec_fcvt_s_d : ltac2:(zQ "hd0!h9!jc!hkd!of!kh4!p4!hl6!hld!jv6!q2!ig6!iuf!jl5!jt8!hmd!lg3!lq0!lh3!kic!kj4!kjd!ho8!kk4!kka!hof!kq4!kl8!lsd!ko0>2sz@1$1@1$0#k0>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>2rm@1$1@1$0#3>1c$h5>2md$2>0@3$3@1$7$2@2$e@2$5@1$0#3^3@1$h8^2@2$6$2^1@3$3$h6@3$h7^7@5$h1$h0$f^6^5^4^3@1$h2@3$h9^6@2$hb^2@2$4^3^5@2$h3@3$8$9$a@4$d$b$c^2@2$5@1$0#k0@2$4^3^5@2$ha@3$hc@1$0#k0@1$h4^3^7^3").
Proof. intros until md; intros H. unfold fcvt_s_d. fcvt_tac H. Qed.

(* [comment removed for export] *)
Lemma csr_write_illegal_slice : ltac2:(zQ "c0!q2!rd!ild!of!hl6!s4!hld!lt9!h9!lu0!luc!jc>6writes$1>3csr@1$b@1$8#c>2lo$0>3len$0>0@3$3@1$6@2$2$0$0@1$9^3@2$4@2$2$0$0@4$7$0$0^2^1@3$3$1@2$a^5^4$5").
Proof.
  intros writes csr lo len H. unfold csr_write_illegal.
  destruct writes; [|reflexivity]. cbn.
  destruct (csr_read_only csr) eqn:E; [|reflexivity].
  rewrite (csr_read_only_unimplemented csr E) in H. discriminate H.
Qed.

(* [comment removed for export] *)
Lemma exec_csr_rw : ltac2:(zQ "hf1!h9!jc!q2!mg1!rd!mga!ild!of!kjd!ho8!mh1!kl8!ko0!hl6!hld!lt9!jr0!mh9!kic!hnf!lu0!kk4!kka!lm7!kl1!il1!ik5!mi0!mic!mj5!mje&@2$b@3$c@1$0#k0@1$8^9^e^9>2sz@1$1@1$0#k0>2op$3>2rd@1$1@1$0#5>3rs1@1$1@1$0#5>3csr@1$1@1$0#c>1c$9>2lo$2>3len$2>0@3$7@1$e@2$6$2$2@1$h4^4@2$d@2$6$2$2@4$f$2$2^2^1@3$7$h5@3$h6^9@4$h1^8^7^6^5^4=1f@1$1@1$0#i0@1$h3^4=3old@1$1@1$0#k0@3$h9^1^4^3=7operand@1$1@1$0#k0@2$h7^6^8=4newv@1$1@1$0#k0M3\2op$3@1$1@1$0#k0^b^1@3$he@1$0#k0^2^1@3$hc@1$0#k0^2@2$hd@1$0#k0^1=6writes$4M3\2op$3$4^c$h0@1$5@1$a^a@1$5@1$a^a@1$h2@3$h8^c^4M4\6writes$4$9^1@2$hb@4$ha^5^8^7^2~0~0").
Proof. intros. unfold exec. rewrite (csr_write_illegal_slice _ _ _ _ H). unfold Sem.exec_csr. rewrite H. reflexivity. Qed.

Lemma exec_csri_rw : ltac2:(zQ "i01!h9!jc!q2!mg1!rd!mga!ild!of!kjd!ho8!kl8!mk6!ko0!p4!hl6!hld!lt9!jr0!mkd!ml5!kic!hnf!lu0!kk4!kka!kl1!il1!ik5!mi0!mic!mj5!mje&@2$a@3$c@1$0#k0@1$8^9^e^9>2sz@1$1@1$0#k0>2op$3>2rd@1$1@1$0#5>4uimm@1$1@1$0#5>3csr@1$1@1$0#c>1c$9>2lo$2>3len$2>0@3$7@1$f@2$6$2$2@1$h6^4@2$e@2$6$2$2@4$h0$2$2^2^1@3$7$h7@3$h8^9@4$h2^8^7^6^5^4=1f@1$1@1$0#i0@1$h5^4=3old@1$1@1$0#k0@3$ha^1^4^3=7operand@1$1@1$0#k0@3$h3@1$0#5@1$0#k0^8=4newv@1$1@1$0#k0M3\2op$3@1$1@1$0#k0^b^1@3$hf@1$0#k0^2^1@3$hd@1$0#k0^2@2$he@1$0#k0^1=6writes$4M3\2op$3$4^c$h1@1$5@2$b@2$d@1$0#5^aZ@1$5@2$b@2$d@1$0#5^aZ@1$h4@3$h9^c^4M4\6writes$4$9^1@2$hc@4$hb^5^8^7^2~0~0").
Proof. intros. unfold exec. rewrite (csr_write_illegal_slice _ _ _ _ H). unfold Sem.exec_csr. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sgnj_sign : ltac2:(zQ "40!h9!jc!rd!mlc>2op$3>1a@1$1@1$0#k0>1b@1$1@1$0#k0$2") := ltac2:(zQ "80!h9!rd!mlc!ij0!jc!p4!mga!mm6\2op$2\1a@1$4@1$0#k0\1b@1$4@1$0#k0=2sa$1@2$3@2$5@1$0#k0^2+jf=2sb$1@2$3@2$5@1$0#k0^2+jfM2\2op$2$1^5^1@1$6^1@2$7^2^1").

Lemma sgnj_val_unsigned : ltac2:(zQ "d0!h9!rd!q2!jc!p4!of!mlc!mmd!mn8!ihc!ijb!ii3!mo5>2op$6>1a@1$3@1$0#k0>1b@1$3@1$0#k0@3$5$2@2$4@1$0#k0@4$7@1$0#k0^3^2^1@2$9@2$cM1\0$1$2@3$8^3^2^1+1Z+jf@2$a@2$4@1$0#k0^2@2$b+2+jf").
Proof.
  intros op a b. unfold sgnj_val, bit, sgnj_sign. change (Z.of_N (64-1)) with 63%Z.
  rewrite bv_concat_unsigned by reflexivity.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
  change (Z.of_N (64-1)) with 63%Z.
  destruct (match op with F_SGNJ => _ | _ => _ end); reflexivity.
Qed.

Lemma testbit_sign63 : ltac2:(zQ "80!rd!q2!mof!of!mk6!ih0!mo5!ij0>1c$0>1i$1>0@2$5Z^1@3$3$0@2$7@2$6M0\1c$0$1^3+1Z+jf^2@2$2^3@2$4^2+jf").
Proof.
  intros c i Hi. destruct (Z.lt_ge_cases i 63).
  - rewrite Z.shiftl_spec_low by lia. destruct c; cbn; [|reflexivity]. symmetry. apply Z.eqb_neq. lia.
  - rewrite Z.shiftl_spec_high by lia. destruct c.
    + destruct (Z.eqb_spec i 63). { subst. reflexivity. } cbn. apply Z.bits_above_log2; cbn; lia.
    + rewrite Z.bits_0. reflexivity.
Qed.

Lemma testbit_word_high : ltac2:(zQ "90!h9!rd!s4!of!q2!ih0!ij0!jc!p4>1a@1$7@1$0#k0>1i$4>0@2$5+k0^1@3$3$1@2$6@2$8@1$0#k0^3^2$2").
Proof.
  intros a i Hi. pose proof (bv_unsigned_in_range 64 a) as Hr. unfold bv_modulus in Hr.
  destruct (Z.eq_dec (bv_unsigned a) 0) as [E|E]. { rewrite E. apply Z.bits_0. }
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Ltac sgnj_bits a :=
  apply bv_eq; rewrite sgnj_val_unsigned; unfold sgnj_sign, fabs_d, fneg_d; rewrite ?Z_to_bv_unsigned;
  pose proof (bv_unsigned_in_range 64 a);
  try (rewrite bv_wrap_small; [| unfold bv_modulus in *;
        solve [ rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound (bv_unsigned a) (2^63)); lia
              | apply Z_lxor_range; lia ] ]);
  apply Z.bits_inj'; intros i Hi;
  rewrite ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec, ?testbit_sign63, <- ?Z.land_ones, ?Z.land_spec by lia;
  destruct (Z.lt_ge_cases i 63);
  [ rewrite ?Z.ones_spec_low, ?(Z.pow2_bits_false 63) by lia; replace (Z.eqb i 63) with false by (symmetry; apply Z.eqb_neq; lia)
  | rewrite ?Z.ones_spec_high by lia;
    destruct (Z.eqb_spec i 63); [subst; rewrite ?Z.pow2_bits_true by lia | rewrite ?(testbit_word_high a i), ?(Z.pow2_bits_false 63 i) by lia] ];
  repeat match goal with |- context [Z.testbit ?x ?k] => destruct (Z.testbit x k) end; reflexivity.

Lemma sgnj_self : ltac2:(zQ "50!h9!jc!of!mp6!mmd>1a@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^1^1^1").
Proof. intros a. sgnj_bits a. Qed.
Lemma sgnjx_self : ltac2:(zQ "60!h9!jc!of!mq0!mmd!mqb>1a@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^1^1@1$5^1").
Proof. intros a. sgnj_bits a. Qed.
Lemma sgnjn_self : ltac2:(zQ "60!h9!jc!of!mr5!mmd!ms0>1a@1$1@1$0#k0@3$2@1$1@1$0#k0@4$4@1$0#k0$3^1^1@1$5^1").
Proof. intros a. sgnj_bits a. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fmv_x_w_val : ltac2:(zQ "60!h9!jc!of!js4!msa!ngc>1f@1$1@1$0#k0@3$2@1$1@1$0#k0@3$3@1$0#i0@1$0#k0@1$4^1@1$5^1").
Proof. intros f. exact (b_lw_val f). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bv_lit_eq : ltac2:(zQ "60!of!q2!jc!nh4!hu7!p4>1n$3>1x@1$2^1>1z$1>0@3$0$1@2$5^3^2^1@3$0@1$2^4^3@2$4^4^2").
Proof. intros n x z E. subst z. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity| apply bv_unsigned_in_range]. Qed.

(* [comment removed for export] *)
