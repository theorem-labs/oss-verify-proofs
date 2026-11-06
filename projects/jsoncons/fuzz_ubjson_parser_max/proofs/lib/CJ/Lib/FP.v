(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_FP () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Fpu."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.FP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1false"; "1fst"; "1negb"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2iff"; "3N"; "3Z"; "0F"]; ["4RNE"; "4fflags"; "4fflags_bits"; "4fmt_double"; "4fmt_single"; "4fp_convert"; "4fp_of_int"; "4fp_sqrt"; "4fp_to_int"; "4rmode"; "4rmode_of_Z"; "4rmode_of_field"; "5FC_D"; "5FC_L"; "5FC_LU"; "5FC_S"]; ["5FC_W"; "5FC_WU"; "5FMT_D"; "5FMT_S"; "5F_SGNJ"; "5F_SGNJN"; "5F_SGNJX"; "5Fari"; "5Fcmp"; "5Fcvt"; "5Fsqrt"; "5fariop"; "5fcmpop"; "6bv_eqb"; "6bvmap"; "6bvmap_set"]; ["6sext"; "7Core"; "7EDone"; "7accrue"; "7c_fcsr"; "7c_pc"; "7core"; "7csr_slice"; "7csr_write_illegal"; "7eff"; "7exec"; "7fget"; "7frm_of"; "7fset"; "7low32"; "7nan_box"]; ["7reg_get"; "7rget"; "7rset"; "7sgnj_val"; "7slice_get"; "7slice_set"; "7unbox_s"; "7with_pc"; "0R"; "8bword"; "8fabs_d"; "8fari_d"; "8fari_fl"; "8fari_s"; "8fcmp_d"; "8fcmp_fl"]; ["8fcmp_s"; "8fcvt_d_l"; "8fcvt_d_lu"; "8fcvt_d_s"; "8fcvt_d_w"; "8fcvt_d_wu"; "8fcvt_l_d"; "8fcvt_lu_d"; "8fcvt_s_d"; "8fcvt_s_w"; "8fcvt_s_wu"; "8fcvt_w_d"; "8fcvt_wu_d"; "8fneg_d"; "8frm0"; "8fsqrt_d"]; ["9sx32"; ":land"; ":le"; ":lor"; ":lt"; ":modulo"; ":pow"; ":shiftr"; ":testbit"; "0a"; "0b"; "0c"; "0csr"; "0f"; "0fc"; "0fl"]; ["0i"; "0k"; "0k'"; "0len"; "0lo"; "0md"; "0n"; "0op"; "0pc"; "0r"; "0rd"; "0rm"; "0rs1"; "0rs2"; "0rv"; ";Z_to_bv"]; [";bv"; ";bv_add"; ";bv_swrap"; ";bv_unsigned"; "0sz"; "0v"; "0w"; "0x"; "0y"; "0z"]]).
Lemma tset_tset_same {A} (p : positive) (x y : A) t : tset p x (tset p y t) = tset p x t.
Proof. revert t; induction p; intros [|l v r]; cbn; try rewrite IHp; reflexivity. Qed.
Lemma tset_tset_comm {A} (p q : positive) (x y : A) t :
p <> q -> tset p x (tset q y t) = tset q y (tset p x t).
Proof.
revert q t; induction p; intros [q|q|] [|l v r] Hne; cbn; try reflexivity; try congruence;
try (rewrite IHp by congruence; reflexivity).
Qed.
Lemma bvmap_set_set_same : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "E'T0y5%211yR0%411&Q>%1252';&Q?r4r3r2r1%55<9421%65=:541%75>;653%93:21pQ0;1pXB>1pX@?1pW4B1").
Proof. intros. unfold bvmap_set. apply tset_tset_same. Qed.
Lemma bvmap_set_set_same' : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "M'T0y5%211yR0%411&Q>%1252';'>&T3r5%22:1r4%42<1%73631&Q?r6r3r2%45B?921%55C@481%65DA593%?3@21p091pQ0B1pXBE1pX@F1pW6I1pW4J1").
Proof. intros k k' x y F H. replace k' with k by (apply bv_eq; exact H). apply bvmap_set_set_same. Qed.
Lemma bvmap_set_set_comm : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "N'T0y5%211yR0%411&Q>%1252';'1&Q=r5r4%33;21(2%73621&Q?r6r3r2%45B?921%55C@491%65DA5:3%75EB<51%@3A31p0:1pQ0C1pXBF1pX@G1pW6J1pW4K1").
Proof.
intros k k' x y F H. unfold bvmap_set. apply tset_tset_comm.
intros E. unfold bv_eqb in H. apply Z.eqb_neq in H. apply H.
pose proof (bv_key_inj k k' E). congruence.
Qed.
Lemma freg_get_same : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "K&Q>y5'T0yR0%211%5241%415';'>&T3r3%22:1r2%42<1%73631&R0&Q?r4r5%35B?271%521:%>3A19p081pX<C1pWDB1pW4C1pQ0E1").
Proof. intros F k r v H. replace r with k by (apply bv_eq; exact H). apply reg_get_set_same. Qed.
Lemma freg_get_other : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "L&Q>y5'T0yR0%211%5241%415';'1&Q=r3r2%33;21(2%73621&R0&Q?r4r5%35B?281%521:%623;%?3B21p091pX<D1pWDC1pW4D1pQ0F1").
Proof.
intros F k r v H. apply reg_get_set_other. unfold bv_eqb in H. apply Z.eqb_neq in H.
intros E. apply H. rewrite E. reflexivity.
Qed.
Definition frm0 (fc : bv 32) : Prop := Z.land (Z.shiftr (bv_unsigned fc) 5) 7 = 0%Z.
Lemma frm0_frm_of : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "O&Q>y5'T0yR0%211%5241yQ0%511'5%115&RNr2%211';'>&QL(QAr6r5r4r3%554321:%711z%;3:21p0=1pWNA1pVND1pWBH1pQ0H1pTBI1").
Proof. intros. exact H. Qed.
Lemma rmode_dyn : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "Q1'T0y3%211'QF';'>&T3r2%2271+7%63521&RN&QD%116%311'5'I%211&Kr4%>2C1&QLr3%211%6241(0(@%22;1%H3;41p0?1p0D1pVHL1pWHN1").
Proof. intros rm c Hrm H. unfold rmode_of_field, frm_of. rewrite Hrm. cbn [Z.eqb Pos.eqb]. unfold frm0 in H. rewrite H. reflexivity. Qed.
Lemma rmode_static : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "Q7'T0y3%211'QF'I';'1&Q=r3&SO+7%22:1%53;41(2%93821'5%11<&J&T3r4%22C1%411(0r2%22D1%D3941&Kr5%:2K1&QL%11;%5231%:2LH%L3A21p091p0E1pW<Q01pVHQ21pWHQ41").
Proof.
intros rm c md H Hmd. unfold rmode_of_field. unfold bv_eqb in H.
change (bv_unsigned (Z_to_bv 3 7)) with 7%Z in H. rewrite H. exact Hmd.
Qed.
Lemma fflags_bits_range : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "='A':&S2z&Br1%211%5241&S4+Q0%2241%:241pW0<1").
Proof. intros [[] [] [] [] []]; cbv; split; congruence. Qed.
Lemma land_shiftr_lor_low : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "Q3'>&S2zr4%3221':&S4&S6+2r3%3221%5281%7281';&S1&S7&S3r8r7%3221r6%6221r5%9221%9274%;213%=3J31p0G1p0H1p0A1p0J1pW>O1pW4Q01pVFQ11pVDQ21").
Proof.
intros a b k n Ha Hb Hk Hn. apply Z.bits_inj'. intros i Hi.
rewrite !Z.land_spec, !Z.shiftr_spec, Z.lor_spec by lia.
replace (Z.testbit b (i + k)) with false. { rewrite orb_false_r. reflexivity. }
symmetry. destruct (Z.eq_dec b 0). { subst. apply Z.bits_0. }
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma Z_lor_lt_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "N'>':&S2zr3%3221&S4&S6+2r1%3221%5271%;271r2%7261%92;1%?2;1&S3r5r4%3221%C2B1%?2>B%A231%G231p091p0>1pW>K1pVFL1pVDM1").
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
Lemma frm0_accrue : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "D'T0yQ0%211'A&RNr2%211&SO&S3&T3r3%22:1&B%118%6231%82>1%<11p0;1pW0?1pVNA1").
Proof.
intros fc fl H. unfold frm0 in *.
pose proof (bv_unsigned_in_range 32 fc) as Hf. unfold bv_modulus in Hf.
pose proof (fflags_bits_range fl) as Hb.
assert (HR : (0 <= Z.lor (bv_unsigned fc) (fflags_bits fl) < 2^32)%Z).
{ apply Z_lor_lt_pow2; lia. }
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
rewrite land_shiftr_lor_low by lia. exact H.
Qed.
Lemma land7_shiftr5_zero_iff : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "N'>&S2zr1%3221&<';&S1&S7r2+5%3221+7%6221%83>1<':%?26=%@2>5%3221'1&S8r4%221=(2%B3521p071pW2J1%F2=1p0H1pXDM1").
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
Lemma testbit_mod_pow2_low : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "K'>':&S2zr1%3221&S4r2%2241%8241';'1&S8&S5r4&S6+2r3%3221%6251%821=%927>%<3;21p0>1pW2H1pW>I1pXDJ1").
Proof. intros. rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_low by lia. apply andb_true_r. Qed.
Lemma frm0_slice_set_fflags : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "A'T0yQ0%211yR0%411&RNr2%211&R5r3z+5%443216%811p071pX<;1pVN>1").
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
Lemma frm0_slice_get : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "D'T0yQ0%211&RNr1%211';yR0%811&R4r2+5+3%43321&SOz%2291%;3941p0=1pVNA1").
Proof. intros fc H. unfold slice_get. change (Z.ones 3) with 7%Z. unfold frm0 in H. rewrite H. reflexivity. Qed.
Definition fari_sem (op : fariop) : format -> rmode -> Z -> Z -> Z * fflags :=
match op with F_ADD => fp_add | F_SUB => fp_sub | F_MUL => fp_mul | F_DIV => fp_div end.
Definition fcmp_sem (op : fcmpop) : format -> Z -> Z -> bool * fflags :=
match op with F_EQ => fp_eq | F_LT => fp_lt | F_LE => fp_le end.
Definition fadd_d (md : rmode) (a b : word) : word := Z_to_bv 64 (fst (fp_add fmt_double md (bv_unsigned a) (bv_unsigned b))).
Definition fsub_d (md : rmode) (a b : word) : word := Z_to_bv 64 (fst (fp_sub fmt_double md (bv_unsigned a) (bv_unsigned b))).
Definition fmul_d (md : rmode) (a b : word) : word := Z_to_bv 64 (fst (fp_mul fmt_double md (bv_unsigned a) (bv_unsigned b))).
Definition fdiv_d (md : rmode) (a b : word) : word := Z_to_bv 64 (fst (fp_div fmt_double md (bv_unsigned a) (bv_unsigned b))).
Definition fari_d (op : fariop) : rmode -> word -> word -> word :=
match op with F_ADD => fadd_d | F_SUB => fsub_d | F_MUL => fmul_d | F_DIV => fdiv_d end.
Definition fsqrt_d (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_sqrt fmt_double md (bv_unsigned a))).
Definition feq_d (a b : word) : bool := fst (fp_eq fmt_double (bv_unsigned a) (bv_unsigned b)).
Definition flt_d (a b : word) : bool := fst (fp_lt fmt_double (bv_unsigned a) (bv_unsigned b)).
Definition fle_d (a b : word) : bool := fst (fp_le fmt_double (bv_unsigned a) (bv_unsigned b)).
Definition fcmp_d (op : fcmpop) : word -> word -> bool :=
match op with F_EQ => feq_d | F_LT => flt_d | F_LE => fle_d end.
Definition fadd_s (md : rmode) (a b : word) : word := nan_box (Z_to_bv 32 (fst (fp_add fmt_single md (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))))).
Definition fsub_s (md : rmode) (a b : word) : word := nan_box (Z_to_bv 32 (fst (fp_sub fmt_single md (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))))).
Definition fmul_s (md : rmode) (a b : word) : word := nan_box (Z_to_bv 32 (fst (fp_mul fmt_single md (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))))).
Definition fdiv_s (md : rmode) (a b : word) : word := nan_box (Z_to_bv 32 (fst (fp_div fmt_single md (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))))).
Definition fari_s (op : fariop) : rmode -> word -> word -> word :=
match op with F_ADD => fadd_s | F_SUB => fsub_s | F_MUL => fmul_s | F_DIV => fdiv_s end.
Definition feq_s (a b : word) : bool := fst (fp_eq fmt_single (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))).
Definition flt_s (a b : word) : bool := fst (fp_lt fmt_single (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))).
Definition fle_s (a b : word) : bool := fst (fp_le fmt_single (bv_unsigned (unbox_s a)) (bv_unsigned (unbox_s b))).
Definition fcmp_s (op : fcmpop) : word -> word -> bool :=
match op with F_EQ => feq_s | F_LT => flt_s | F_LE => fle_s end.
Definition bword (b : bool) : word := if b then Z_to_bv 64 1 else Z_to_bv 64 0.
Definition fcvt_w_d (md : rmode) (a : word) : word := sext 64 (Z_to_bv 32 (fst (fp_to_int fmt_double md true 32 (bv_unsigned a)))).
Definition fcvt_wu_d (md : rmode) (a : word) : word := sext 64 (Z_to_bv 32 (fst (fp_to_int fmt_double md false 32 (bv_unsigned a)))).
Definition fcvt_l_d (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_to_int fmt_double md true 64 (bv_unsigned a))).
Definition fcvt_lu_d (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_to_int fmt_double md false 64 (bv_unsigned a))).
Definition fcvt_d_w (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md true 32 (bv_unsigned x))).
Definition fcvt_d_wu (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md false 32 (bv_unsigned x))).
Definition fcvt_d_l (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md true 64 (bv_unsigned x))).
Definition fcvt_d_lu (md : rmode) (x : word) : word := Z_to_bv 64 (fst (fp_of_int fmt_double md false 64 (bv_unsigned x))).
Definition fcvt_s_w (md : rmode) (x : word) : word := nan_box (Z_to_bv 32 (fst (fp_of_int fmt_single md true 32 (bv_unsigned x)))).
Definition fcvt_s_wu (md : rmode) (x : word) : word := nan_box (Z_to_bv 32 (fst (fp_of_int fmt_single md false 32 (bv_unsigned x)))).
Definition fcvt_d_s (md : rmode) (a : word) : word := Z_to_bv 64 (fst (fp_convert fmt_single fmt_double md (bv_unsigned (unbox_s a)))).
Definition fcvt_s_d (md : rmode) (a : word) : word := nan_box (Z_to_bv 32 (fst (fp_convert fmt_double fmt_single md (bv_unsigned a)))).
Definition fabs_d (a : word) : word := Z_to_bv 64 (Z.land (bv_unsigned a) (Z.ones 63)).
Definition fneg_d (a : word) : word := Z_to_bv 64 (Z.lxor (bv_unsigned a) (2^63)).
Definition fari_fl (op : fariop) (f : format) (md : rmode) (a b : Z) : fflags := snd (fari_sem op f md a b).
Definition fcmp_fl (op : fcmpop) (f : format) (a b : Z) : fflags := snd (fcmp_sem op f a b).
Lemma exec_fcmp_d : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "QD'T0yR0%211'Q<y5%511'QF';'QI&QJr6(Q8r5(Q2r4r3r2%6554321r1%:3921(QB&R2&R9&R>&QK%127:%228:%43?21%611&QC&R?&C&T3%12Q08%22Q18%54G421&R7&T1&QE%11E%33Q71N%521G%=271%F3M?1%H11%Q63Q5J1pVHQ81pWLQ:1pWJQ;1pWFQ<1pW@Q?1pX:QA1").
Proof.
intros. unfold exec. cbn [fp_format fread].
unfold fcmp_d, fcmp_fl, feq_d, flt_d, fle_d, fcmp_sem, bword.
destruct op; [destruct (fp_eq _ _ _)|destruct (fp_lt _ _ _)|destruct (fp_le _ _ _)]; reflexivity.
Qed.
Lemma exec_fcmp_s : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "QH'T0yR0%211'Q<y5%511'QF';'QI&QJr6(Q8r5(Q3r4r3r2%6554321r1%:3921(QB&R2&R9&R@&QK%127:%228:%43?21%611&QC&R?&D&T3yQ0&R6%11:%4231%31;%6251%94K831&R7&T1&QE%11I%33Q;1Q2%521K%A271%J3Q1C1%L11%Q:3Q9N1pVHQ<1pWLQ>1pWJQ?1pWFQ@1pW@QC1pX:QE1").
Proof.
intros. unfold exec. cbn [fp_format fread].
unfold fcmp_s, fcmp_fl, feq_s, flt_s, fle_s, fcmp_sem, bword.
destruct op; [destruct (fp_eq _ _ _)|destruct (fp_lt _ _ _)|destruct (fp_le _ _ _)]; reflexivity.
Qed.
Lemma exec_fari_d : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R5'T0yR0%211'Q;y5%511y3%711'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr9(Q7r8(Q2r7r6r5r4%76654321%:391E(QB&QM&R;&QK%12J9%22K9%44>I21&QC&R<&C%Q12Q>6%Q22Q?6%45D3O21&R7&T1&QE%11Q6%33QE1K%521Q8%<271%C3J>1%E11%QA3Q2G1p0Q41pW<QD1pVHQF1pWHQH1pWLQK1pWJQL1pWFQM1pW@R01pX:R21").
Proof.
intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
cbn [fp_format fread fwrite].
unfold fari_d, fari_fl, fadd_d, fsub_d, fmul_d, fdiv_d, fari_sem.
destruct op; [destruct (fp_add _ _ _ _)|destruct (fp_sub _ _ _ _)|destruct (fp_mul _ _ _ _)|destruct (fp_div _ _ _ _)]; reflexivity.
Qed.
Lemma exec_fari_s : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R9'T0yR0%211'Q;y5%511y3%711'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr9(Q7r8(Q3r7r6r5r4%76654321%:391E(QB&QM&R=&QK%12J9%22K9%44>I21&QC&R<&DyQ0&R6%118%Q4231%319%Q6251%85H7Q331&R7&T1&QE%11Q:%33QI1O%521Q<%@271%G3NB1%I11%QE3Q6K1p0Q81pW<QH1pVHQJ1pWHQL1pWLQO1pWJR01pWFR11pW@R41pX:R61").
Proof.
intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
cbn [fp_format fread fwrite].
unfold fari_s, fari_fl, fadd_s, fsub_s, fmul_s, fdiv_s, fari_sem.
destruct op; [destruct (fp_add _ _ _ _)|destruct (fp_sub _ _ _ _)|destruct (fp_mul _ _ _ _)|destruct (fp_div _ _ _ _)]; reflexivity.
Qed.
Lemma exec_fsqrt_d : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R2'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q:(Q2r6r5r4%544321%8371C(QB&QM&RO&QK%12H8%32F1&QC&8'>'A&G&C%Q12Q=8%332N1%73651&R7&T1&QE%11Q6%33QD1K%521Q8%?271%E3KA1%G11%QA3Q2I1p0Q41pW<QD1pVHQF1pWHQH1pWJQK1pWFQL1pX:QO1").
Proof.
intros until md. intros H. unfold exec, resolve_rm. unfold frm_of in *. cbn [c_fcsr with_pc]. rewrite H.
cbn [fp_format fread fwrite]. unfold fsqrt_d. destruct (fp_sqrt _ _ _); reflexivity.
Qed.
Lemma exec_fminmax_d : forall sz op rd rs1 rs2 c,
exec sz (Fminmax op FMT_D rd rs1 rs2) c =
let r := fp_minmax fmt_double (match op with F_MIN => false | F_MAX => true end) (bv_unsigned (fget c rs1)) (bv_unsigned (fget c rs2)) in
EDone (fset rd (Z_to_bv 64 (fst r)) (accrue (snd r) (with_pc (c_pc c + sz) c))).
Proof. intros. unfold exec. cbn [fp_format fread fwrite]. destruct (fp_minmax _ _ _ _); reflexivity. Qed.
Ltac fcvt_tac H :=
unfold exec, resolve_rm; unfold frm_of in *; cbn [c_fcsr with_pc]; rewrite H;
cbn [fp_format fread fwrite Z.eqb Pos.eqb];
first [ destruct (fp_to_int _ _ _ _ _); reflexivity
| destruct (fp_of_int _ _ _ _ _); reflexivity
| destruct (fp_convert _ _ _ _); reflexivity ].
Lemma exec_fcvt_w_d : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R5'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(Q0(Lr6r5r4%6554321%9381D(QB&R2&RK&QK%12I8%32G1&QC&8'>'A&H&C(9+Q0%Q42Q@:%554Q1321%93871&R7&T1&QE%11Q9%33QG1N%521Q;%A271%G3MC1%I11%QD3Q5K1p0Q71pW<QG1pVHQI1pWHQK1pWJQN1pWFQO1pX:R21").
Proof. intros until md; intros H. unfold fcvt_w_d. fcvt_tac H. Qed.
Lemma exec_fcvt_wu_d : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R5'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(Q1(Lr6r5r4%6554321%9381D(QB&R2&RL&QK%12I8%32G1&QC&8'>'A&H&C(2+Q0%Q42Q@:%554Q1321%93871&R7&T1&QE%11Q9%33QG1N%521Q;%A271%G3MC1%I11%QD3Q5K1p0Q71pW<QG1pVHQI1pWHQK1pWJQN1pWFQO1pX:R21").
Proof. intros until md; intros H. unfold fcvt_wu_d. fcvt_tac H. Qed.
Lemma exec_fcvt_l_d : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R5'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(M(Lr6r5r4%6554321%9381D(QB&R2&RF&QK%12I8%32G1&QC&8'>'A&H&C(9+R0%Q42Q@:%554Q1321%93871&R7&T1&QE%11Q9%33QG1N%521Q;%A271%G3MC1%I11%QD3Q5K1p0Q71pW<QG1pVHQI1pWHQK1pWJQN1pWFQO1pX:R21").
Proof. intros until md; intros H. unfold fcvt_l_d. fcvt_tac H. Qed.
Lemma exec_fcvt_lu_d : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R5'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(N(Lr6r5r4%6554321%9381D(QB&R2&RG&QK%12I8%32G1&QC&8'>'A&H&C(2+R0%Q42Q@:%554Q1321%93871&R7&T1&QE%11Q9%33QG1N%521Q;%A271%G3MC1%I11%QD3Q5K1p0Q71pW<QG1pVHQI1pWHQK1pWJQN1pWFQO1pX:R21").
Proof. intros until md; intros H. unfold fcvt_lu_d. fcvt_tac H. Qed.
Lemma exec_fcvt_d_w : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R5'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(L(Q0r6r5r4%6554321%9381D(QB&QM&RD&R1%12I8%32G1&QC&8'>'A&F&C(9+Q0%Q42Q@:%554Q1321%93871&R7&T1&QE%11Q9%33QG1N%521Q;%A271%G3MC1%I11%QD3Q5K1p0Q71pW<QG1pVHQI1pWHQK1pWJQN1pWFQO1pX:R21").
Proof. intros until md; intros H. unfold fcvt_d_w. fcvt_tac H. Qed.
Lemma exec_fcvt_d_wu : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R5'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(L(Q1r6r5r4%6554321%9381D(QB&QM&RE&R1%12I8%32G1&QC&8'>'A&F&C(2+Q0%Q42Q@:%554Q1321%93871&R7&T1&QE%11Q9%33QG1N%521Q;%A271%G3MC1%I11%QD3Q5K1p0Q71pW<QG1pVHQI1pWHQK1pWJQN1pWFQO1pX:R21").
Proof. intros until md; intros H. unfold fcvt_d_wu. fcvt_tac H. Qed.
Lemma exec_fcvt_d_l : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R5'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(L(Mr6r5r4%6554321%9381D(QB&QM&RA&R1%12I8%32G1&QC&8'>'A&F&C(9+R0%Q42Q@:%554Q1321%93871&R7&T1&QE%11Q9%33QG1N%521Q;%A271%G3MC1%I11%QD3Q5K1p0Q71pW<QG1pVHQI1pWHQK1pWJQN1pWFQO1pX:R21").
Proof. intros until md; intros H. unfold fcvt_d_l. fcvt_tac H. Qed.
Lemma exec_fcvt_d_lu : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R5'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(L(Nr6r5r4%6554321%9381D(QB&QM&RB&R1%12I8%32G1&QC&8'>'A&F&C(2+R0%Q42Q@:%554Q1321%93871&R7&T1&QE%11Q9%33QG1N%521Q;%A271%G3MC1%I11%QD3Q5K1p0Q71pW<QG1pVHQI1pWHQK1pWJQN1pWFQO1pX:R21").
Proof. intros until md; intros H. unfold fcvt_d_lu. fcvt_tac H. Qed.
Lemma exec_fcvt_s_w : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R5'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(O(Q0r6r5r4%6554321%9381D(QB&QM&RI&R1%12I8%32G1&QC&8'>'A&F&D(9+Q0%Q42Q@:%554Q1321%93871&R7&T1&QE%11Q9%33QG1N%521Q;%A271%G3MC1%I11%QD3Q5K1p0Q71pW<QG1pVHQI1pWHQK1pWJQN1pWFQO1pX:R21").
Proof. intros until md; intros H. unfold fcvt_s_w. fcvt_tac H. Qed.
Lemma exec_fcvt_s_wu : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R5'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(O(Q1r6r5r4%6554321%9381D(QB&QM&RJ&R1%12I8%32G1&QC&8'>'A&F&D(2+Q0%Q42Q@:%554Q1321%93871&R7&T1&QE%11Q9%33QG1N%521Q;%A271%G3MC1%I11%QD3Q5K1p0Q71pW<QG1pVHQI1pWHQK1pWJQN1pWFQO1pX:R21").
Proof. intros until md; intros H. unfold fcvt_s_wu. fcvt_tac H. Qed.
Lemma exec_fcvt_d_s : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R7'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(L(Or6r5r4%6554321%9381D(QB&QM&RC&QK%12I8%32G1&QC&8'>'A&E&D&CyQ0&R6%11;%Q6231%7465Q31%;3:91&R7&T1&QE%11Q;%33QI1Q0%521Q=%C271%I3OE1%K11%QF3Q7M1p0Q91pW<QI1pVHQK1pWHQM1pWJR01pWFR11pX:R41").
Proof. intros until md; intros H. unfold fcvt_d_s. fcvt_tac H. Qed.
Lemma exec_fcvt_s_d : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "R4'T0yR0%211y5%411y3%611'QF'I';'5%113&K&T3r3%22:1&QLr2%211%7241(0r1%22>1%>3<41'QI&QJr7(Q9(O(Lr6r5r4%6554321%9381D(QB&QM&RH&QK%12I8%32G1&QC&8'>'A&E&C&D%Q32Q?9%4432Q01%83761&R7&T1&QE%11Q8%33QF1M%521Q:%@271%F3LB1%H11%QC3Q4J1p0Q61pW<QF1pVHQH1pWHQJ1pWJQM1pWFQN1pX:R11").
Proof. intros until md; intros H. unfold fcvt_s_d. fcvt_tac H. Qed.
Lemma csr_write_illegal_of_slice : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "O'1'T0y<%211'>';'5'7%1244%311&QGr3%211(0(6r2r1%34==21%52:1%>3:71&QHr5r4%3221(2%D3I21p071pW8G1pW:H1pVJJ1pX>N1").
Proof.
intros w csr lo len H. unfold csr_write_illegal. destruct w; [|reflexivity]. cbn [andb].
destruct (csr_read_only csr) eqn:E; [|reflexivity].
apply csr_read_only_unimplemented in E. congruence.
Qed.
Lemma exec_csr_rw : forall sz op rd rs1 csr c lo len,
csr_slice csr = Some (lo, len) ->
exec sz (Csr op rd rs1 csr) c =
let f := c_fcsr c in
let old := slice_get f lo len in
let operand := rget c rs1 in
let newv := match op with CSR_RW => operand | CSR_RS => bv_or old operand | CSR_RC => bv_and old (bv_not operand) end in
let writes := match op with CSR_RW => true | _ => negb (is_x0 rs1) end in
EDone (rset rd old (if writes then with_fcsr (slice_set f lo len newv) (with_pc (c_pc c + sz) c) else with_pc (c_pc c + sz) c)).
Proof. intros. unfold exec. rewrite (csr_write_illegal_of_slice _ _ _ _ H). unfold Sem.exec_csr. rewrite H. reflexivity. Qed.
Lemma exec_csri_rw : forall sz op rd uimm csr c lo len,
csr_slice csr = Some (lo, len) ->
exec sz (CsrI op rd uimm csr) c =
let f := c_fcsr c in
let old := slice_get f lo len in
let operand := zext 64 uimm in
let newv := match op with CSR_RW => operand | CSR_RS => bv_or old operand | CSR_RC => bv_and old (bv_not operand) end in
let writes := match op with CSR_RW => true | _ => negb (Z.eqb (bv_unsigned uimm) 0) end in
EDone (rset rd old (if writes then with_fcsr (slice_set f lo len newv) (with_pc (c_pc c + sz) c) else with_pc (c_pc c + sz) c)).
Proof. intros. unfold exec. rewrite (csr_write_illegal_of_slice _ _ _ _ H). unfold Sem.exec_csr. rewrite H. reflexivity. Qed.
Definition sgnj_sign (op : fsgnop) (a b : word) : bool :=
let sa := Z.testbit (bv_unsigned a) 63 in
let sb := Z.testbit (bv_unsigned b) 63 in
match op with F_SGNJ => sb | F_SGNJN => negb sb | F_SGNJX => xorb sa sb end.
Lemma sgnj_val_unsigned : forall op (a b : word),
bv_unsigned (sgnj_val op a b) = Z.lor (Z.shiftl (if sgnj_sign op a b then 1 else 0) 63) (bv_unsigned a mod 2^63)%Z.
Proof.
intros op a b. unfold sgnj_val, bit, sgnj_sign. change (Z.of_N (64-1)) with 63%Z.
rewrite bv_concat_unsigned by reflexivity.
rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
change (Z.of_N (64-1)) with 63%Z.
destruct (match op with F_SGNJ => _ | _ => _ end); reflexivity.
Qed.
Lemma testbit_sign63 : forall (c : bool) i, (0 <= i)%Z ->
Z.testbit (Z.shiftl (if c then 1 else 0) 63) i = (c && Z.eqb i 63)%bool.
Proof.
intros c i Hi. destruct (Z.lt_ge_cases i 63).
- rewrite Z.shiftl_spec_low by lia. destruct c; cbn; [|reflexivity]. symmetry. apply Z.eqb_neq. lia.
- rewrite Z.shiftl_spec_high by lia. destruct c.
+ destruct (Z.eqb_spec i 63). { subst. reflexivity. } cbn. apply Z.bits_above_log2; cbn; lia.
+ rewrite Z.bits_0. reflexivity.
Qed.
Lemma testbit_word_high : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "E'T0yR0%211'>&S2+R0r1%3221';'1&S8&T3r3%22<1r2%5221(2%93821p0;1pW2@1pVDB1").
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
Lemma sgnj_self : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP ":'T0yR0%211';&R3(Q4r1%346211%53612pVD71").
Proof. intros a. sgnj_bits a. Qed.
Lemma sgnjx_self : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "<'T0yR0%211';&R3(Q6r1%346211&R:%113%73831pVD91").
Proof. intros a. sgnj_bits a. Qed.
Lemma sgnjn_self : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "<'T0yR0%211';&R3(Q5r1%346211&RM%113%73831pVD91").
Proof. intros a. sgnj_bits a. Qed.
Lemma unbox_nan_box : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP ";'T0yQ0%211';&R6&QOr1%211%411%63713pX<81").
Proof.
intros v. unfold unbox_s, nan_box, low32.
pose proof (bv_unsigned_in_range 32 v) as Hv. unfold bv_modulus in Hv.
assert (E : bv_unsigned (bv_concat 64 (Z_to_bv 32 (-1)) v) = (Z.lor (Z.shiftl (2^32 - 1) 32) (bv_unsigned v))%Z).
{ rewrite bv_concat_unsigned by reflexivity. reflexivity. }
assert (Hhi : bv_unsigned (bv_extract 32 32 (bv_concat 64 (Z_to_bv 32 (-1)) v)) = Z.ones 32).
{ rewrite bv_extract_unsigned, E. apply Z.bits_inj'. intros i Hi.
change (bv_wrap 32 ?x) with (x mod 2^32)%Z. change (Z.of_N 32) with 32%Z.
destruct (Z.lt_ge_cases i 32).
- rewrite testbit_mod_pow2_low, Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec, Z.ones_spec_low by lia.
replace (i + 32 - 32)%Z with i by lia. change (2^32 - 1)%Z with (Z.ones 32). rewrite Z.ones_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high by lia. apply andb_false_r. }
rewrite Hhi, Z.eqb_refl.
apply bv_eq. rewrite bv_extract_unsigned, E, Z.shiftr_0_r. change (bv_wrap 32 ?x) with (x mod 2^32)%Z.
apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i 32).
- rewrite testbit_mod_pow2_low, Z.lor_spec, Z.shiftl_spec_low by lia. reflexivity.
- rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high, andb_false_r by lia.
symmetry. destruct (Z.eq_dec (bv_unsigned v) 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma low32_nan_box : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP ";'T0yQ0%211';&QN&QOr1%211%411%63713pX<81").
Proof.
intros v. unfold nan_box, low32. apply bv_eq. rewrite bv_extract_unsigned, bv_concat_unsigned, Z.shiftr_0_r by reflexivity.
change (bv_wrap 32 ?x) with (x mod 2^32)%Z. pose proof (bv_unsigned_in_range 32 v) as Hv. unfold bv_modulus in Hv.
change (Z.of_N 32) with 32%Z in *.
apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i 32).
- rewrite testbit_mod_pow2_low, Z.lor_spec, Z.shiftl_spec_low by lia. reflexivity.
- rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high, andb_false_r by lia.
symmetry. destruct (Z.eq_dec (bv_unsigned v) 0) as [E|E]; [rewrite E; apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32%Z; [apply Z.log2_lt_pow2; lia| lia].
Qed.
Lemma fmv_x_w_val : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP ">'T0yR0%211';&Q@yQ0&QNr1%211%53481&S0%114%93:31pVL;1").
Proof. intros f. exact (b_lw_val f). Qed.
Lemma sext32_lit : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "@'>';'T0yR0%211&Q@yQ0&SOr1%2231%53471&T2%1264%62:1%=3:41pX<?1").
Proof. intros v. rewrite sext_small. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned. apply bv_swrap_wrap'. Qed.
Lemma fcvt_w_d_eq : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "L'I'T0yR0%211';&RKr2r1%3221&SO&T2yQ0&3'>'A&H&C(9+Q0&T3%12B=%655?431%:3981%=2<1%?2F1%E3FA1pVDG1pW<K1").
Proof. intros. unfold fcvt_w_d. apply sext32_lit. Qed.
Lemma bword_unsigned : forall b, bv_unsigned (bword b) = (if b then 1 else 0)%Z.
Proof. intros [|]; reflexivity. Qed.
Lemma bword_eqb0 : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "?'1';&Q=yR0&R9r1%211&SOz%2261%83741&4%117%<3=31pVF>1").
Proof. intros [|]; reflexivity. Qed.
Lemma bword_if : forall b : bool, (if b then w1 else w0) = bword b.
Proof. intros [|]; reflexivity. Qed.
Lemma bv_lit_eq : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "D'='T0r1%211'>';&T3r3r2%3221%53618r4%;11&SO%1236%:3381p061pXD=1pX@?1pW>C1").
Proof. intros n x z E. subst z. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity| apply bv_unsigned_in_range]. Qed.
Lemma bword_nez : ltac2:(TCodec.tc2 tcn__CJ_Lib_FP "?'1';&4&Q=yR0&R9r1%211&SOz%2261%83741%:11%<3=17pVF>1").
Proof. intros [|]; reflexivity. Qed.
