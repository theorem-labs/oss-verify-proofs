(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_Bytes () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Bytes."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1bool"; "1false"; "1length"; "1list"; "1nat"; "2and"; "2eq"; "2iff"; "2not"; "3map"; "4Z"; "0D"; "0H"; "5bytes_le_to_Z"; "5le_bytes_to_word"; "0M"]; ["6HIGHS64b"; "6ONES64b"; "6bytes_ok"; "6highs"; "6le_val"; "6ones"; "7In"; "8add"; "8land"; "8le"; "8lnot"; "8lor"; "8lt"; "8lxor"; "8modulo"; "8mul"]; ["8of_nat"; "8pow"; "8shiftl"; "8sub"; "8testbit"; "0a"; "0b"; "0bs"; "0i"; "0n"; "9Z_to_bv"; "9bv"; "9bv_extract"; "9bv_unsigned"; "0w"; "0x"]; ["0x'"; "0y"; "0y'"]]).
Fixpoint le_val (bs : list Z) : Z :=
match bs with [] => 0 | b :: bs' => b + 256 * le_val bs' end.
Fixpoint ones (n : nat) : Z := match n with O => 0 | S n' => 1 + 256 * ones n' end.
Definition highs (n : nat) : Z := 128 * ones n.
Definition bytes_ok (bs : list Z) : Prop := Forall (fun b => 0 <= b < 256) bs.
Lemma le_val_range : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "I'3':%211&Br1%211'5&Iz&Dr2%211%5241&L&Q1+X0&Q0&2%12A8%311%6251%82:1%@2:1p0B1pR@F1").
Proof.
induction bs as [|b bs IH]; intros H; cbn [le_val length]; [lia|].
inversion H; subst. specialize (IH ltac:(assumption)).
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.
Lemma split_mod : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "O':'5&Izr3%3221&L+X0%2241%8241r2%5281'6&N&Gr5&Or4%22;1%5241%42=@%8221%925B%72@1%:291%=3I41p0?1p0B1pQ0L1pS4M1pS0N1").
Proof.
intros x y M Hx HM. rewrite Z.rem_mul_r by lia.
rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia.
rewrite Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.
Lemma testbit_split : forall x y i, 0 <= x < 256 -> 0 <= i ->
Z.testbit (x + 256 * y) i = if i <? 8 then Z.testbit x i else Z.testbit y (i - 8).
Proof.
intros x y i Hx Hi. destruct (Z.ltb_spec0 i 8).
- rewrite <- (Z.mod_pow2_bits_low _ 8) by lia. change (2^8) with 256.
rewrite (Z.mul_comm 256 y), Z.mod_add, Z.mod_small by lia. reflexivity.
- replace i with ((i - 8) + 8) at 1 by lia. rewrite <- Z.div_pow2_bits by lia. change (2^8) with 256.
rewrite (Z.mul_comm 256 y), Z.div_add, Z.div_small, Z.add_0_l by lia. reflexivity.
Qed.
Lemma land_lt_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "J':'5&Izr3%3221&L&Q1+2r1%3221%5271%;271&Hr5r4%3221%?2>1%;2:>%=231%C231p0@1p0:1pRDG1pR>H1pR<I1").
Proof.
intros a b n Ha Hb.
assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
pose proof (Z.land_nonneg a b) as Hnn. split; [lia|].
destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]. { apply Z.pow_pos_nonneg; lia. }
destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. apply Z.pow_pos_nonneg; lia. }
apply (proj2 (Z.log2_lt_pow2 (Z.land a b) n ltac:(lia))).
pose proof (Z.log2_land a b ltac:(lia) Hb). assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma lor_lt_pow2 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "N':'5&Izr3%3221&L&Q1+2r1%3221%5271%;271r2%7261%92;1%?2;1&Kr5r4%3221%C2B1%?2>B%A231%G231p091p0>1pRDK1pR>L1pR<M1").
Proof.
intros a b n Ha Hb.
assert (Hn : 0 <= n). { destruct (Z.le_gt_cases 0 n); [assumption|]. rewrite Z.pow_neg_r in Ha by lia. lia. }
pose proof (Z.lor_nonneg a b) as Hnn. split; [lia|].
destruct (Z.eq_dec a 0) as [->|]. { rewrite Z.lor_0_l. lia. }
destruct (Z.eq_dec b 0) as [->|]. { rewrite Z.lor_0_r. lia. }
assert (Hp : 0 < Z.lor a b). { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n Hp)). rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.
Lemma land_split : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "Q4':'5&Izr4%3221&L+X0%2241%8241r3%9281%6225%<221'6&H&Gr6&Or5%22=1%5241%42?<%72C1%9231%:28E%;27@%92D1%<231%?3M51p0A1p0F1pS6Q01pS2Q11pS4Q21pS0Q31").
Proof.
intros x y x' y' Hx Hx'.
pose proof (land_lt_pow2 x x' 8 ltac:(cbn; lia) ltac:(lia)) as Hl. change (2^8) with 256 in Hl.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !testbit_split by lia.
destruct (i <? 8); rewrite Z.land_spec; reflexivity.
Qed.
Lemma lor_split : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "Q4':'5&Izr4%3221&L+X0%2241%8241r3%9281%6225%<221'6&K&Gr6&Or5%22=1%5241%42?<%72C1%9231%:28E%;27@%92D1%<231%?3M51p0A1p0F1pS6Q01pS2Q11pS4Q21pS0Q31").
Proof.
intros x y x' y' Hx Hx'.
pose proof (lor_lt_pow2 x x' 8 ltac:(cbn; lia) ltac:(cbn; lia)) as Hl. change (2^8) with 256 in Hl.
apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, !testbit_split by lia.
destruct (i <? 8); rewrite Z.lor_spec; reflexivity.
Qed.
Lemma lnot_split : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "D':'6&J&Gr2&O+X0r1%3221%6251%811&Q3+WO%2219%<17%:291%=231%@3A71pRNB1pR>C1").
Proof. intros. unfold Z.lnot. lia. Qed.
Lemma byte_fact1 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "H':'5&I+1r1%3221&L+X0%2241%8241'6&H&Q3r2%221;+WO%4213%6231+T0%8221z%;3E21p0=1pR>G1").
Proof.
intros b Hb.
assert (C : forallb (fun b => Z.land (Z.land (b - 1) (255 - b)) 128 =? 0) (map Z.of_nat (seq 1 255)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. apply Z.eqb_eq, C. apply in_map_iff. exists (Z.to_nat b). split; [lia|]. apply in_seq. lia.
Qed.
Theorem haszero_iff : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "Q='3':%211&Br1%211'4&2r2%2281&Dr3%211&7&8'6&H&N&Q3&E%11<%32A1&Q1+X0&Q0%11A%4231%:261&J%11I%>231&C%11H%A231z%D3Q221%F11&Fr4%23Q651%K241tRNQ8M1tRDQ4Q11p0Q61pR@Q:1").
Proof.
induction bs as [|b bs IH]; intros H; cbn [length le_val ones highs].
- cbn. split; [|intros []]. intros C; apply C. reflexivity.
- inversion H as [|b' bs' Hb Hbs]; subst. specialize (IH Hbs). cbn zeta in IH.
unfold highs in *. cbn [ones].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
pose proof (Z.pow_pos_nonneg 256 (Z.of_nat (length bs)) ltac:(lia) ltac:(lia)) as HM.
rewrite lnot_split.
replace (128 * (1 + 256 * ones (length bs))) with (128 + 256 * (128 * ones (length bs))) by lia.
destruct (Z.eq_dec b 0) as [->|Hb0].
+ replace (0 + 256 * le_val bs - (1 + 256 * ones (length bs))) with (255 + 256 * (le_val bs - ones (length bs) - 1)) by lia.
rewrite split_mod by lia. rewrite land_split by lia. change (Z.land 255 (255 - 0)) with 255.
rewrite land_split by lia. change (Z.land 255 128) with 128.
split; [intros; left; reflexivity| intros _]. lia.
+ replace (b + 256 * le_val bs - (1 + 256 * ones (length bs))) with ((b - 1) + 256 * (le_val bs - ones (length bs))) by lia.
rewrite split_mod by lia.
rewrite land_split by lia.
rewrite land_split. 2:{ pose proof (land_lt_pow2 (b-1) (255-b) 8 ltac:(cbn; lia) ltac:(lia)). cbn in *. lia. }
2:{ lia. }
rewrite byte_fact1 by lia.
split.
* intros Hnz. right. apply IH. lia.
* intros [Hz|Hin]; [lia|]. apply IH in Hin. lia.
Qed.
Definition ONES64b : Z := 0x0101010101010101.
Definition HIGHS64b : Z := 0x8080808080808080.
Lemma ones_8 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "7'6':&Eu8%211&A%63521"). Proof. reflexivity. Qed.
Lemma highs_8 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "7'6':&Cu8%211&@%63521"). Proof. reflexivity. Qed.
Lemma testbit_high_false : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "K':'5&Izr3%3221&L&Q1+2r2%3221%5271%;271%;294%=291'6'0&Q4r5%221?(1%63521p081p0;1pRBH1pRDI1pS0J1").
Proof.
intros x n i Hx Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with n; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma land_mod_pow2_r : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "N':'5&Izr3%3221&L&Q1+2r1%3221%5271%;271r2%<2;1'6&Hr5&Nr4%=2<@%3221%6251%7264%93H21p0;1p0>1pRDK1pR>L1pR<M1").
Proof.
intros a b n Ha Hn. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i n).
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite (testbit_high_false a n i) by lia. reflexivity.
Qed.
Lemma lnot_mod64 : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "I':'5&Izr1%3221&L&Q1+2+R0%3221%5271%;271'6&Mr2+_oooooooooooO%3221&N&J%115%321;%93F51p0;1pRNH1").
Proof.
intros w Hw. change 18446744073709551615 with (Z.ones 64). rewrite <- Z.land_ones by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
destruct (Z.eq_dec w 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Theorem haszero64_gcc : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "Q:'3':%211&Br1%211'6'4&2r2%2291u8%63521&Dr3%211&7&H&N&G+_mognoko_mogO%22A1+`PPPPPPPPPPP0%5221&M+_oooooooooooO%22F1%:241+XQPTP`RPXQPT0%<221z%I3N21&8&Fr4%23Q251%411%E261tRNQ5G1p0K1p0Q31pR@Q71").
Proof.
intros bs Hok Hlen w. change 18446744073709551616 with (2^64).
pose proof (le_val_range bs Hok) as Hw. rewrite Hlen in Hw. change (256 ^ Z.of_nat 8) with (2^64) in Hw.
pose proof (haszero_iff bs Hok) as HZ. rewrite Hlen in HZ. cbn zeta in HZ. fold w in HZ, Hw.
change (256 ^ Z.of_nat 8) with (2^64) in HZ. rewrite ones_8, highs_8 in HZ. unfold ONES64b, HIGHS64b in HZ.
replace ((w + 18374403900871474943) mod 2 ^ 64) with ((w - 72340172838076673) mod 2^64).
2:{ replace (w + 18374403900871474943) with ((w - 72340172838076673) + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity. }
rewrite lnot_mod64 by lia. rewrite land_mod_pow2_r by (try lia; apply Z.mod_pos_bound; lia).
destruct HZ as [HZ1 HZ2]. split.
- intros E I. apply HZ2 in I. apply I. exact E.
- intros NI. match goal with |- ?x = 0 => destruct (Z.eq_dec x 0) as [E|NE] end; [assumption|].
exfalso. apply NI. apply HZ1. exact NE.
Qed.
Lemma demorgan_highs : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "Q6':'5&Izr3%3221&L&Q1+2+R0%3221%5271%;271&7'6&H&K&Mr6+_oooooooooooO%3221r5%6221r4%9221%;3I12&J%116%=2:1%>216%@3N1K%B261p0D1p0E1p0F1pJQ31pRNQ41pHQ51").
Proof.
intros D w H HD Hw HH. change 18446744073709551615 with (Z.ones 64).
assert (HI : forall x, 0 <= x < 2^64 -> forall i, 64 <= i -> Z.testbit x i = false).
{ intros x Hx i Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia]. }
split; intros E; apply Z.bits_inj'; intros i Hi.
- rewrite Z.bits_0, !Z.land_spec, Z.lnot_spec by lia.
apply (f_equal (fun x => Z.testbit x i)) in E. rewrite Z.land_spec, Z.lor_spec, Z.lxor_spec in E.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.ones_spec_low in E by lia.
destruct (Z.testbit D i), (Z.testbit w i), (Z.testbit H i); cbn in *; congruence.
+ rewrite (HI D) by lia. reflexivity.
- apply (f_equal (fun x => Z.testbit x i)) in E. rewrite Z.bits_0, !Z.land_spec, Z.lnot_spec in E by lia.
rewrite Z.land_spec, Z.lor_spec, Z.lxor_spec.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.ones_spec_low by lia.
destruct (Z.testbit D i), (Z.testbit w i), (Z.testbit H i); cbn in *; congruence.
+ rewrite (HI H) by lia. apply andb_false_r.
Qed.
Theorem haszero64_clang : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "Q8'3':%211&Br1%211'6'4&2r2%2291u8%63521&Dr3%211&7&H&K&N&Q3+RPXQPTP`RPX0%221B+`PPPPPPPPPPP0%5221%721E+XQPTP`RPXQPT0%:221%F3K12&8&Fzr4%33Q021%511%C271tRNQ3E1p0I1p0Q11pR@Q51").
Proof.
intros bs Hok Hlen w. change 18446744073709551616 with (2^64).
pose proof (le_val_range bs Hok) as Hw. rewrite Hlen in Hw. change (256 ^ Z.of_nat 8) with (2^64) in Hw.
pose proof (haszero_iff bs Hok) as HZ. rewrite Hlen in HZ. cbn zeta in HZ. fold w in HZ, Hw.
change (256 ^ Z.of_nat 8) with (2^64) in HZ. rewrite ones_8, highs_8 in HZ. unfold ONES64b, HIGHS64b in HZ.
set (D := (w - 72340172838076673) mod 2 ^ 64) in HZ.
assert (HD : 0 <= D < 2^64) by (apply Z.mod_pos_bound; lia).
replace ((72340172838076672 - w) mod 2 ^ 64) with (Z.lxor D 18446744073709551615).
2:{ rewrite lnot_mod64 by lia. unfold Z.lnot. subst D. Z.div_mod_to_equations. lia. }
rewrite demorgan_highs by lia.
destruct HZ as [HZ1 HZ2]. split.
- intros E I. apply HZ2 in I. apply I. exact E.
- intros NI. match goal with |- ?x = 0 => destruct (Z.eq_dec x 0) as [E|NE] end; [assumption|].
exfalso. apply NI. apply HZ1. exact NE.
Qed.
Lemma lor_shiftl8_add : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "K':'5&Izr2%3221&L+X0%2241%8241'6&Kr4&Q2r3+8%3221%6251&G&O%12=6%3291%<3F51p0B1p0?1pS4I1pS0J1").
Proof.
intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
rewrite <- Z.lxor_lor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia]. }
symmetry. replace (256 * y) with (y * 256) by lia. apply Z.add_nocarry_lxor.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
replace (y * 256) with (0 + 256 * y) by lia. rewrite (testbit_split 0 y i) by lia.
destruct (Z.ltb_spec0 i 8). { rewrite Z.bits_0. apply andb_false_r. }
rewrite (Z.bits_above_log2 x i); [reflexivity|lia|].
destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 8; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma bytes_ok_map : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes ">'3'Q;y8%211%411&B&9':&Q=%117r1%548421%711pR@91").
Proof.
induction bs as [|b bs IH]; cbn; constructor; [|exact IH].
pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.
Lemma bytes_le_to_Z_le_val : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "B'3'Q;y8%211%411'6':&=r1%211&D&9&Q=%11;%34;816%511%;3:71pR@=1").
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z le_val map]; [reflexivity|].
rewrite IH. apply lor_shiftl8_add.
- pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *. lia.
- pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)). lia.
Qed.
Lemma load8_le_val : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "N'3'Q;y8%211%411'6'4&2r1%2261u8%63521':&Q=yR0&Q<w&>r2%211%546461%8271&D&9%;1F%24F=17%411%F3?61p0A1pR@I1").
Proof.
intros bs Hlen. unfold le_bytes_to_word. rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
rewrite bytes_le_to_Z_le_val.
pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr. rewrite length_map, Hlen in Hr.
change (256 ^ Z.of_nat 8) with (2^64) in Hr.
rewrite (bv_wrap_small 64 (le_val _)) by (change (bv_modulus 64) with (2^64); lia).
apply bv_wrap_small. change (bv_modulus 64) with (2^64); lia.
Qed.
Lemma In0_map_unsigned : ltac2:(TCodec.tc2 tcn__CJ_Lib_Bytes "D'3'Q;y8%211%411&7&F':z&9&Q=%119r1%44:621%83761&Q:%12>8%;3>15%=241pR@?1").
Proof.
intros bs. rewrite in_map_iff. split.
- intros (b & Hb & Hin). replace (Z_to_bv 8 0) with b; [exact Hin|]. apply bv_eq. rewrite Hb. reflexivity.
- intros Hin. exists (Z_to_bv 8 0). split; [reflexivity|exact Hin].
Qed.
