(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import BigModel.
Import ListNotations.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__BigFactsBase () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel.W."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["0A"; "0B"; "1O"; "1S"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "2and"; "2eq"; "2not"; "3sub"]; ["4le"; "4lt"; "5firstn"; "5skipn"; "6Z"; "7val"; "7wordZ"; "7words_ok"; "8DDproduct"; "9M"; "9add"; "9b2z"; "9divu"; "9half"; "9l_bit"; "9l_mask"]; ["9land"; "9lor"; "9ltu"; "9max_word"; "9mul"; "9r_mask"; "9remu"; "9shl"; "9shr"; "9sub"; "9wrap"; "8nth_w"; "8upd"; "8words"; "8zeros"; ":last"]; [":removelast"; ";add"; ";div"; ";le"; ";lt"; ";modulo"; ";mul"; ";of_nat"; ";ones"; ";pow"; ";sub"; "0a"; "0b"; "0i"; "0j"; "0k"]; ["0n"; "0t"; "0v"; "0w"; "0ws"; "0z"]]).
Ltac bdall := repeat match goal with
| |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
| |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
| |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
end.
Definition wordZ (w : Z) : Prop := 0 <= w < W.M.
Definition words_ok (ws : words) : Prop := Forall wordZ ws.
Lemma M_pos : ltac2:(TCodec.tc2 tcn__BigFactsBase "4&QDz&I%3221"). Proof. reflexivity. Qed.
Lemma M_val : ltac2:(TCodec.tc2 tcn__BigFactsBase "5'='D&I+`PPPPPPPPPPP0%43321"). Proof. reflexivity. Qed.
Lemma half_val : ltac2:(TCodec.tc2 tcn__BigFactsBase "5'='D&M+TPPPPP0%43321"). Proof. reflexivity. Qed.
Lemma M_half : ltac2:(TCodec.tc2 tcn__BigFactsBase "7'='D&I&QF&M%2211%63541"). Proof. reflexivity. Qed.
Lemma max_word_val : ltac2:(TCodec.tc2 tcn__BigFactsBase "5'='D&Q3+_oooooooooooO%43321"). Proof. reflexivity. Qed.
Lemma r_mask_val : ltac2:(TCodec.tc2 tcn__BigFactsBase "5'='D&Q5+SoooooO%43321"). Proof. reflexivity. Qed.
Lemma l_mask_val : ltac2:(TCodec.tc2 tcn__BigFactsBase "5'='D&O+_ooooolPPPPP0%43321"). Proof. reflexivity. Qed.
Lemma l_bit_val : ltac2:(TCodec.tc2 tcn__BigFactsBase "5'='D&N+XPPPPPPPPPPP0%43321"). Proof. reflexivity. Qed.
Lemma r_mask_ones : ltac2:(TCodec.tc2 tcn__BigFactsBase "7'='D&Q5&QH+Q0%211%63541"). Proof. reflexivity. Qed.
Global Opaque W.M W.half W.max_word W.r_mask W.l_mask W.l_bit.
Arguments W.M : simpl never.
Arguments W.half : simpl never.
Lemma wrap_range : ltac2:(TCodec.tc2 tcn__BigFactsBase "7'D&F&Q:r1%211%411pT<61").
Proof. intros z. unfold wordZ, W.wrap. pose proof M_pos. split; [apply Z.mod_pos_bound|apply Z.mod_pos_bound]; lia. Qed.
Lemma wrap_id : ltac2:(TCodec.tc2 tcn__BigFactsBase ";'D&Fr1%211'=&Q:r2%211%43812p061pT<:1").
Proof. intros z. unfold wordZ, W.wrap. intros. apply Z.mod_small. lia. Qed.
Lemma add_range : ltac2:(TCodec.tc2 tcn__BigFactsBase "9'D&F&Jr2r1%3221%511pSJ71pSH81"). Proof. intros a b. apply wrap_range. Qed.
Lemma sub_range : ltac2:(TCodec.tc2 tcn__BigFactsBase "9'D&F&Q9r2r1%3221%511pSJ71pSH81"). Proof. intros a b. apply wrap_range. Qed.
Lemma mul_range : ltac2:(TCodec.tc2 tcn__BigFactsBase "9'D&F&Q4r2r1%3221%511pSJ71pSH81"). Proof. intros a b. apply wrap_range. Qed.
Lemma shl_range : ltac2:(TCodec.tc2 tcn__BigFactsBase "9'D&F&Q7r2r1%3221%511pT071pSH81"). Proof. intros a k. apply wrap_range. Qed.
Lemma b2z_range : ltac2:(TCodec.tc2 tcn__BigFactsBase "<'5'<&QCz&Kr1%211%5241+1%7231%9231pSJ;1"). Proof. intros b. destruct b; simpl; lia. Qed.
Lemma shr_range : ltac2:(TCodec.tc2 tcn__BigFactsBase "@'D&Fr2%211&QCz%2214&Q8r4r3%3221%:11p061p0:1pT0>1pSH?1").
Proof. intros a k. unfold wordZ, W.shr. intros. pose proof (Z.pow_pos_nonneg 2 k).
split. apply Z.div_pos; lia. apply Z.le_lt_trans with a. 2: lia.
apply Z.div_le_upper_bound. lia. nia. Qed.
Lemma land_range : ltac2:(TCodec.tc2 tcn__BigFactsBase "='D&Fr2%211&Q0r4r3%3221%711p061p071pSJ;1pSH<1").
Proof. intros a b. unfold wordZ, W.land. rewrite M_val. intros. change 18446744073709551616 with (2^64) in *. split. apply Z.land_nonneg; lia.
destruct (Z.eq_dec (Z.land a b) 0). lia.
assert (Hp: 0 < Z.land a b) by (pose proof (Z.land_nonneg a b); lia).
destruct (Z.eq_dec a 0). subst. rewrite Z.land_0_l in n. lia.
assert (Z.log2 (Z.land a b) <= Z.log2 a). { pose proof (Z.log2_land a b). lia. }
assert (Z.log2 a < 64). { apply Z.log2_lt_pow2; lia. }
assert (H3: Z.log2 (Z.land a b) < 64) by lia.
apply Z.log2_lt_pow2 in H3. lia. lia. Qed.
Lemma lor_range : ltac2:(TCodec.tc2 tcn__BigFactsBase "='D&Fr2%211&Q1r4r3%3221%711p061p071pSJ;1pSH<1").
Proof. intros a b. unfold wordZ, W.lor. rewrite M_val. intros. change 18446744073709551616 with (2^64) in *. split. apply Z.lor_nonneg; lia.
destruct (Z.eq_dec a 0). subst. rewrite Z.lor_0_l. lia.
destruct (Z.eq_dec b 0). subst. rewrite Z.lor_0_r. lia.
assert (Hp: 0 < Z.lor a b). { pose proof (Z.lor_nonneg a b). assert (Z.lor a b <> 0). { intro E. apply Z.lor_eq_0_iff in E. lia. } lia. }
apply Z.log2_lt_pow2. lia. rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia. Qed.
Lemma divu_range : ltac2:(TCodec.tc2 tcn__BigFactsBase "='D&Fr2%211&Lr4r3%3221%711p061p071pSJ;1pSH<1").
Proof. intros a b. unfold wordZ, W.divu. rewrite max_word_val, M_val. intros. bdall. lia. split. apply Z.div_pos; lia.
apply Z.le_lt_trans with a. apply Z.div_le_upper_bound; nia. lia. Qed.
Lemma remu_range : ltac2:(TCodec.tc2 tcn__BigFactsBase "='D&Fr2%211&Q6r4r3%3221%711p061p071pSJ;1pSH<1").
Proof. intros a b. unfold wordZ, W.remu. intros. bdall. lia. pose proof (Z.mod_pos_bound a b). lia. Qed.
Lemma words_ok_nil : ltac2:(TCodec.tc2 tcn__BigFactsBase "5&G(;'D%211%411"). Proof. constructor. Qed.
Lemma words_ok_cons : ltac2:(TCodec.tc2 tcn__BigFactsBase "@'D&Q=&Fr2%211&G%113(6r4r3%33:21%611p061p091pT:=1pT8?1"). Proof. intros w ws. intros; constructor; auto. Qed.
Lemma words_ok_app : ltac2:(TCodec.tc2 tcn__BigFactsBase ">&Q=&Gr2%211&4'Dr4r3%43321%811p071p081pSJ<1pSH=1").
Proof. intros a b. unfold words_ok. intros. apply Forall_app; auto. Qed.
Lemma words_ok_app_inv : ltac2:(TCodec.tc2 tcn__BigFactsBase "A'9'D%211&G&4r2r1%33621%511'<r3%811%917%4221p061pSJ=1pSH>1").
Proof. intros a b. unfold words_ok. intros H. apply Forall_app in H. exact H. Qed.
Lemma words_ok_zeros : ltac2:(TCodec.tc2 tcn__BigFactsBase "7':&G&Q>r1%211%411pT261").
Proof. intros n. unfold zeros, words_ok. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. unfold wordZ. pose proof M_pos. lia. Qed.
Lemma words_ok_firstn : ltac2:(TCodec.tc2 tcn__BigFactsBase ">':&Q=&Gr1%211&B'Dr3r2%43321%811p071pT:;1pT2=1").
Proof. intros n ws. intros. rewrite <- (firstn_skipn n ws) in H. apply words_ok_app_inv in H. tauto. Qed.
Lemma words_ok_skipn : ltac2:(TCodec.tc2 tcn__BigFactsBase ">':&Q=&Gr1%211&C'Dr3r2%43321%811p071pT:;1pT2=1").
Proof. intros n ws. intros. rewrite <- (firstn_skipn n ws) in H. apply words_ok_app_inv in H. tauto. Qed.
Lemma words_ok_nth : ltac2:(TCodec.tc2 tcn__BigFactsBase "=&Q=':&Gr2%211&F&Q;r3%2215%411p061pSL:1pT:<1").
Proof. intros ws i. unfold nth_w, words_ok. intros. destruct (Nat.lt_ge_cases i (length ws)).
apply Forall_nth; auto. rewrite nth_overflow by lia. unfold wordZ; pose proof M_pos; lia. Qed.
Lemma upd_length : ltac2:(TCodec.tc2 tcn__BigFactsBase "@&Q=':'D'=&8&Q<r3r2r1%43321%6281%7295%93;21pT6;1pSL=1pT:?1").
Proof. intros ws i v. revert i; induction ws; destruct i; simpl; auto. Qed.
Lemma upd_nth ws i v j : nth_w (upd ws i v) j = if (Nat.eqb i j && (j <? length ws))%nat then v else nth_w ws j.
Proof. unfold nth_w. revert i j; induction ws as [|w ws IH]; intros [|i] [|j]; simpl; auto.
all: try (destruct (Nat.eqb i j); reflexivity).
all: try (rewrite IH; destruct (Nat.eqb i j) eqn:E; simpl; auto). Qed.
Lemma upd_nth_same : ltac2:(TCodec.tc2 tcn__BigFactsBase "E'9'D%211':&Ar2&8r3%2271%5241'=&Q;&Q<r4%23179%4218%63?1;p081pT6A1pSL@1pT:B1").
Proof. intros ws i v. intros. rewrite upd_nth. rewrite Nat.eqb_refl. destruct (Nat.ltb_spec i (length ws)); simpl; auto; lia. Qed.
Lemma upd_nth_other : ltac2:(TCodec.tc2 tcn__BigFactsBase "G&Q=':'D&>'=r3r1%33621%511&Q;&Q<r5r4%33218r2%6221%7252%=3?21p0:1pSNB1pT6B1pSLD1pT:F1").
Proof. intros ws i v j. intros. rewrite upd_nth. destruct (Nat.eqb_spec i j); simpl; auto; lia. Qed.
Lemma upd_words_ok : ltac2:(TCodec.tc2 tcn__BigFactsBase "C&Q=':'D&Gr3%211&Fr2%211&Q<r5r4%33218%:11p061p0:1pT6>1pSL@1pT:B1").
Proof. intros ws i v. revert i; induction ws; destruct i; simpl; intros; auto; inversion H; subst; constructor; auto. apply IHws; auto. Qed.
Lemma upd_app_l : ltac2:(TCodec.tc2 tcn__BigFactsBase "J'9'D%211':&Ar2&8r4%2271%5241'=&Q=&Q<&4r5%23>18r3%5321<%6342=%63B1<%:3931p0<1pT6E1pSLD1pSJF1pSHG1").
Proof. intros a b i v. revert i; induction a; intros [|i]; simpl; intros; try lia; auto. rewrite IHa; auto; lia. Qed.
Lemma upd_app_r : ltac2:(TCodec.tc2 tcn__BigFactsBase "M'9'D%211':'@&8r4%2261r2%5221'=&Q=&Q<&4r5%23>19r3%53219&?%>2B5%2241%93?1=%93E81%=3<61p0?1pT6H1pSLG1pSJI1pSHJ1").
Proof. intros a b i v. revert i; induction a; intros [|i]; simpl; intros; try lia; auto. rewrite IHa; auto; lia. Qed.
Lemma upd_overflow : ltac2:(TCodec.tc2 tcn__BigFactsBase "D'9'D%211':'@&8r3%2261r2%5221'=&Q=&Q<r4%23186%53412p071pT6@1pSL?1pT:A1").
Proof. intros ws i v. revert i; induction ws; destruct i; simpl; intros; auto; try lia. rewrite IHws; auto; lia. Qed.
Lemma nth_w_app_l : ltac2:(TCodec.tc2 tcn__BigFactsBase "G'9'D%211':&Ar1&8r3%2271%5241'=&Q;&4r4%23=17r2%5221%6242%83A21p0:1pSLA1pSJC1pSHD1").
Proof. intros a b i. intros; unfold nth_w; apply app_nth1; auto. Qed.
Lemma nth_w_app_r : ltac2:(TCodec.tc2 tcn__BigFactsBase "J'9'D%211':'@&8r3%2261r1%5221'=&Q;&4r4%23=18r2%5221&?%=2A5%2241%92>1%;3D51p0=1pSLD1pSJF1pSHG1").
Proof. intros a b i. intros; unfold nth_w; apply app_nth2; auto. Qed.
Lemma nth_w_overflow : ltac2:(TCodec.tc2 tcn__BigFactsBase "C'9'D%211':'@&8r2%2261r1%5221'=&Q;r3%2217z%53>21p071pSL>1pT:@1").
Proof. intros ws i. intros; unfold nth_w; apply nth_overflow; auto. Qed.
Lemma nth_w_zeros : ltac2:(TCodec.tc2 tcn__BigFactsBase "=':'='D&Q;&Q>r2%211r1%5221z%93821pSL;1pT2<1").
Proof. intros n i. unfold nth_w, zeros. destruct (Nat.lt_ge_cases i n). apply nth_repeat. rewrite nth_overflow; auto. rewrite repeat_length; auto. Qed.
Lemma zeros_length : ltac2:(TCodec.tc2 tcn__BigFactsBase ":':'=&8'D&Q>r1%211%5241%73813pT291"). Proof. intros n. apply repeat_length. Qed.
Fixpoint val (ws : words) : Z := match ws with [] => 0 | w :: t => w + W.M * val t end.
Lemma val_nil : ltac2:(TCodec.tc2 tcn__BigFactsBase "8'='D&E(;%113%311z%73621"). Proof. reflexivity. Qed.
Lemma val_cons : ltac2:(TCodec.tc2 tcn__BigFactsBase "C'D'9%112'=&E(6r2r1%33821%511&QA&QF&I%916%3221%5291%=3@71pT4?1pT8B1"). Proof. intros w t. reflexivity. Qed.
Lemma val_app : ltac2:(TCodec.tc2 tcn__BigFactsBase "J'9'D%211'=&E&4r2r1%33721%511&QA%715&QF&QI&I&QG&8%12@;%311%6251%@1=%9221%<2;1%D3F>1pSJF1pSHG1").
Proof. intros a b. induction a as [|w a IH]. simpl app; simpl length; simpl Z.of_nat. rewrite Z.pow_0_r, val_nil. lia.
simpl app; simpl length. rewrite !val_cons, IH. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.
Lemma val_zeros : ltac2:(TCodec.tc2 tcn__BigFactsBase ";':'='D&E&Q>r1%211%411z%83721pT2:1").
Proof. intros n. unfold zeros; induction n. reflexivity. simpl repeat. rewrite val_cons, IHn. lia. Qed.
Lemma val_bound : ltac2:(TCodec.tc2 tcn__BigFactsBase "H&Q=&Gr1%211'<&QCz&Er2%211%5241&QD&QI&I&QG&8'D%2219%411%7261%92;1%A2;1p0C1pT:G1").
Proof. intros ws. induction ws as [|w ws IH]; intros. rewrite val_nil. simpl. lia. inversion H; subst. specialize (IH H3). unfold wordZ in H2.
rewrite val_cons. simpl length. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. pose proof M_pos. nia. Qed.
Lemma val_nonneg : ltac2:(TCodec.tc2 tcn__BigFactsBase "<&Q=&Gr1%211&QCz&Er2%211%5241p071pT:;1"). Proof. intros ws. intros H; apply val_bound in H; lia. Qed.
Lemma val_upd : ltac2:(TCodec.tc2 tcn__BigFactsBase "Q3'9'D%211':&Ar2&8r3%2271%5241'=&E&Q<r4%23179%411&QA%614&QF&QJ&Q;%128>%32A1&QI&I&QG%11C%4231%:261%=2<1%D3M?1p0F1pT6O1pSLN1pT:Q01").
Proof. intros ws i v. revert i; induction ws as [|w ws IH]; intros [|i]; simpl length; simpl upd; intros; try lia. rewrite !val_cons. unfold nth_w; simpl nth. rewrite Z.pow_0_r. lia.
rewrite !val_cons. rewrite IH by lia. unfold nth_w; simpl nth. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.
Lemma val_firstn_skipn : ltac2:(TCodec.tc2 tcn__BigFactsBase "L':&Q='='D&Er1%211&QA&Br2%23715%711&QF&QI&I&QG&8%12>7%311%6251&C%13B<@%B11%;241%A2=1%G3FC1pT:I1pT2K1").
Proof. intros n ws. rewrite <- (firstn_skipn n ws) at 1. apply val_app. Qed.
Lemma val_cons_nth : ltac2:(TCodec.tc2 tcn__BigFactsBase "L'9'D%211&>'=r1(;%116%43631%611&Er2%211&QA&Q;(2%2251&QF&I&Cu1%23D1:%<11%6251%;281%E3H=1p0A1pT:I1").
Proof. intros ws. destruct ws; intros. congruence. reflexivity. Qed.
Lemma val_single_nth : ltac2:(TCodec.tc2 tcn__BigFactsBase "Q7'9'D%211':&Ar1&8r2%2271%5241'=&Er3%211&QA&B%13?94%611&QF&QI&I&QG%11?%4231&Q;%12=B&C(3%11E%33L1A%C11%=2;1%B271%?2:1%D2A1%I3Q2F1p0K1pSLQ21pT:Q41").
Proof. intros ws i. intros. rewrite (val_firstn_skipn i ws) at 1. rewrite length_firstn, Nat.min_l by lia.
f_equal. f_equal. rewrite (val_cons_nth (skipn i ws)). 2:{ intro E. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. simpl in E. lia. }
unfold nth_w. rewrite nth_skipn, Nat.add_0_r. rewrite skipn_skipn. f_equal. Qed.
Lemma val_removelast : ltac2:(TCodec.tc2 tcn__BigFactsBase "Q4'9'D%211&>'=r1(;%116%43631%611&Er2%211&QA&Q@%12>4%611&QF&Q?z%23C91&QI&I&QJ&QG&8%12I?%311+1%6221%9281%>2;1%C2@1%M3Q0E1p0I1pT:Q11").
Proof. intros ws. intros H. assert (E := app_removelast_last 0 H).
assert (L: length ws = S (length (removelast ws))). { rewrite E at 1. rewrite length_app. simpl. lia. }
rewrite E at 1. rewrite val_app, val_cons, val_nil, L. rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat (length (removelast ws))) - 1) with (Z.of_nat (length (removelast ws))) by lia. lia. Qed.
Lemma add_carry : ltac2:(TCodec.tc2 tcn__BigFactsBase "H'D&Fr2%211'=&QA&Jr4r3%3221&QF&I&K&Q2%1257%311%6251%<281%=2;:%?3C21p0A1p0B1pSJF1pSHG1").
Proof. intros a b. unfold wordZ, W.add, W.wrap, W.ltu, W.b2z. intros.
destruct (Z_lt_le_dec (a + b) W.M).
- rewrite Z.mod_small by lia. bdall; lia.
- replace ((a + b) mod W.M) with (a + b - W.M). bdall; lia.
apply Z.mod_unique with 1; lia. Qed.
Lemma add_carry' : ltac2:(TCodec.tc2 tcn__BigFactsBase "H'D&Fr2%211'=&QA&Jr4r3%3221&QF&I&K&Q2%1256%311%6251%<281%=2;:%?3C21p0A1p0B1pSJF1pSHG1").
Proof. intros a b. intros. replace (W.add a b) with (W.add b a). rewrite add_carry; auto; lia. unfold W.add; f_equal; lia. Qed.
Lemma sub_borrow : ltac2:(TCodec.tc2 tcn__BigFactsBase "I'D&Fr2%211'=&Q9r4r3%3221&QA&QJ%1254&QF&I&K&Q2%12:9%311%6251%:281%@3D<1p0B1p0C1pSJG1pSHH1").
Proof. intros a b. unfold wordZ, W.sub, W.wrap, W.ltu, W.b2z. intros. bdall.
- symmetry. apply Z.mod_unique with (-1); lia.
- rewrite Z.mod_small; lia. Qed.
Lemma sub_borrow_test : ltac2:(TCodec.tc2 tcn__BigFactsBase "B'D&Fr2%211'='5&Q2r4&Q9r3%2231%5241%6253%93821p0;1p0<1pSJ@1pSHA1").
Proof. intros a b. intros. pose proof (sub_borrow a b H H0). unfold W.ltu, W.b2z in *. unfold wordZ in *.
destruct (Z.ltb_spec a b); bdall; auto; lia. Qed.
Lemma add_small : ltac2:(TCodec.tc2 tcn__BigFactsBase "F'D&Fr2%211&QD&QAr4r3%3221&I%6221'=&Jr5%2218%:229%53@21p071p0?1p0@1pSJD1pSHE1").
Proof. intros a b. intros. unfold W.add. apply wrap_id. unfold wordZ in *. lia. Qed.
Lemma sub_small : ltac2:(TCodec.tc2 tcn__BigFactsBase "D'D&Fr2%211&QCr3r4%3221'=&Q9r5%2215&QJ%1237%63>31p081p0=1p0>1pSJB1pSHC1").
Proof. intros a b. intros. rewrite sub_borrow by auto. unfold W.ltu, W.b2z. bdall; lia. Qed.
Lemma mul_small : ltac2:(TCodec.tc2 tcn__BigFactsBase "G'D&QCzr2%3221&QD&QFr4r3%3221&I%6221'=&Q4r5%2218%:229%53A21p071p0?1p0@1pSJE1pSHF1").
Proof. intros a b. intros. unfold W.mul. apply wrap_id. unfold wordZ. nia. Qed.
Lemma halves : ltac2:(TCodec.tc2 tcn__BigFactsBase "Q0'D&Fr1%211'<'=r2&QA&QF&Q8+Q0%2251&M%5221&Q0&Q5%22:1%:241%=3B<1&QCz%221:&QD%12<;%D231%6259%42:>%G221%H241%I2;1p0K1pSHO1").
Proof. intros a. unfold wordZ, W.shr, W.land. rewrite r_mask_ones. intros. rewrite Z.land_ones by lia.
change (2^32) with 4294967296.
rewrite half_val in *. rewrite M_val in *. split. rewrite Z.mul_comm. apply Z_div_mod_eq_full.
split. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. apply Z.mod_pos_bound; lia. Qed.
Lemma shl32 : ltac2:(TCodec.tc2 tcn__BigFactsBase "A'D&Fr1%211'=&Q7r2+Q0%3221&QF&QE&M%2261%4212%:3>61p0<1pSH@1").
Proof. intros a. unfold wordZ, W.shl, W.wrap. intros. change (2^32) with 4294967296. rewrite M_half, half_val.
rewrite Z.mul_mod_distr_r. reflexivity. lia. lia. Qed.
Lemma shr32 : ltac2:(TCodec.tc2 tcn__BigFactsBase ";'D'=&Q8r1+Q0%3221&QB&M%2251%83941pSH:1"). Proof. intros a. rewrite half_val. reflexivity. Qed.
Theorem DDproduct_correct A B : wordZ A -> wordZ B ->
let (hi, lo) := DDproduct A B in wordZ hi /\ wordZ lo /\ hi * W.M + lo = A * B.
Proof.
intros HA HB. unfold DDproduct.
destruct (halves A HA) as (EA & RA1 & RA2). destruct (halves B HB) as (EB & RB1 & RB2).
set (ah := W.shr A 32) in *. set (al := W.land A W.r_mask) in *.
set (bh := W.shr B 32) in *. set (bl := W.land B W.r_mask) in *.
rewrite half_val in *. rewrite M_val.
assert (Hll: W.mul al bl = al * bl) by (apply mul_small; rewrite ?M_val; nia).
assert (Hhh: W.mul ah bh = ah * bh) by (apply mul_small; rewrite ?M_val; nia).
assert (Hlh: W.mul al bh = al * bh) by (apply mul_small; rewrite ?M_val; nia).
assert (Hhl: W.mul ah bl = ah * bl) by (apply mul_small; rewrite ?M_val; nia).
rewrite Hll, Hhh, Hlh, Hhl.
set (m1 := al * bh). set (m2 := ah * bl). set (lo0 := al * bl). set (hi0 := ah * bh).
assert (W1: wordZ m1) by (unfold wordZ, m1; rewrite M_val; nia).
assert (W2: wordZ m2) by (unfold wordZ, m2; rewrite M_val; nia).
assert (W0: wordZ lo0) by (unfold wordZ, lo0; rewrite M_val; nia).
assert (Wh: wordZ hi0) by (unfold wordZ, hi0; rewrite M_val; nia).
rewrite (shl32 m1 W1), (shl32 m2 W2). rewrite !shr32. rewrite half_val.
pose proof (Z_div_mod_eq_full m1 4294967296) as Dm1. pose proof (Z.mod_pos_bound m1 4294967296) as Bm1.
pose proof (Z_div_mod_eq_full m2 4294967296) as Dm2. pose proof (Z.mod_pos_bound m2 4294967296) as Bm2.
assert (D1: 0 <= m1 / 4294967296 < 4294967296). { split. apply Z.div_pos; unfold wordZ in W1; lia. apply Z.div_lt_upper_bound. lia. unfold m1; nia. }
assert (D2: 0 <= m2 / 4294967296 < 4294967296). { split. apply Z.div_pos; unfold wordZ in W2; lia. apply Z.div_lt_upper_bound. lia. unfold m2; nia. }
set (s1 := m1 mod 4294967296 * 4294967296). assert (Ws1: wordZ s1) by (unfold wordZ, s1; rewrite M_val; nia).
set (s2 := m2 mod 4294967296 * 4294967296). assert (Ws2: wordZ s2) by (unfold wordZ, s2; rewrite M_val; nia).
pose proof (add_carry lo0 s1 W0 Ws1) as C1.
set (lo1 := W.add lo0 s1) in *. set (c1 := W.b2z (W.ltu lo1 lo0)) in *.
assert (Wlo1: wordZ lo1) by apply add_range.
pose proof (add_carry lo1 s2 Wlo1 Ws2) as C2.
set (lo2 := W.add lo1 s2) in *. set (c2 := W.b2z (W.ltu lo2 lo1)) in *.
assert (Wlo2: wordZ lo2) by apply add_range.
pose proof (b2z_range (W.ltu lo1 lo0)). pose proof (b2z_range (W.ltu lo2 lo1)). fold c1 in H. fold c2 in H0.
assert (KEY: (hi0 + (c1 + m1 / 4294967296) + (c2 + m2 / 4294967296)) * 18446744073709551616 + lo2 = A * B).
{ rewrite EA, EB. rewrite M_val in C1, C2. unfold hi0. unfold lo0 in C1. nia. }
assert (Bhi: 0 <= hi0 + (c1 + m1 / 4294967296) + (c2 + m2 / 4294967296) < 18446744073709551616).
{ unfold wordZ in HA, HB, Wlo2. rewrite M_val in *. split. unfold hi0. nia.
assert (A * B <= 18446744073709551615 * 18446744073709551615) by nia. nia. }
assert (E1: W.add c1 (m1 / 4294967296) = c1 + m1 / 4294967296). { apply add_small; unfold wordZ; rewrite ?M_val; lia. }
rewrite E1.
assert (E2: W.add hi0 (c1 + m1 / 4294967296) = hi0 + (c1 + m1 / 4294967296)). { apply add_small; unfold wordZ in *; rewrite ?M_val in *; clear - Bhi D1 D2 H H0 Wh; lia. }
rewrite E2.
assert (E3: W.add c2 (m2 / 4294967296) = c2 + m2 / 4294967296). { apply add_small; unfold wordZ; rewrite ?M_val; lia. }
rewrite E3.
assert (E4: W.add (hi0 + (c1 + m1 / 4294967296)) (c2 + m2 / 4294967296) = hi0 + (c1 + m1 / 4294967296) + (c2 + m2 / 4294967296)).
{ apply add_small; unfold wordZ in *; rewrite ?M_val in *; clear - Bhi D1 D2 H H0 Wh; lia. }
rewrite E4. split. unfold wordZ; rewrite M_val; lia. split. exact Wlo2. exact KEY.
Qed.
Lemma DDproduct_hi_bound : ltac2:(TCodec.tc2 tcn__BigFactsBase "D'D&Fr2%211&QC&7&Hr4r3%3221%53::1&QJ&I+2%3221%;251p0=1p0>1p4B1p2C1").
Proof. intros A B. intros. pose proof (DDproduct_correct A B H H0). destruct (DDproduct A B) as [hi lo]. simpl.
destruct H1 as (Wh & Wl & E). unfold wordZ in *. rewrite M_val in *.
assert (A * B <= 18446744073709551615 * 18446744073709551615) by nia. nia. Qed.
