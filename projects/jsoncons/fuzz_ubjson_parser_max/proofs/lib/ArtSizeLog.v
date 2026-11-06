(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import As0Tables.
Import ListNotations.
Import AsanTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ArtSizeLog () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtSizeLog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1bool"; "1true"; "2and"; "2eq"; "3Z"; "0L"; "4C0F"; "4C33"; "4C55"; "4lxor63_ok"; "4slpop"; "4slpop_ok"; "4sm_spec"; "4smear"; "5zrange"; "6forallb"]; ["7add"; "7div"; "7land"; "7le"; "7log2"; "7lor"; "7lt"; "7lxor"; "7mul"; "7pow"; "7sub"; "0a"; "0b"; "0k"; "0s"; "0t10"]; ["0t2"; "0t3"; "0t7"; "0t9"; "0w"; "0x"; "0y"]]).
Lemma lor_range64 : ltac2:(TCodec.tc2 tcn__ArtSizeLog "H'4'2&Czr2%3221&F&I+2+R0%3221%5271%;271&Er4r3%3221%?2>1%<228%B221p081p091pQJF1pQHG1").
Proof.
intros a b Ha Hb. split. apply Z.lor_nonneg; lia.
destruct (Z.eq_dec (Z.lor a b) 0) as [E|NZ]; [rewrite E; lia|].
assert (Hl : Z.log2 (Z.lor a b) < 64).
{ rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
- destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
apply Z.log2_lt_pow2 in Hl; [exact Hl|]. pose proof (Z.lor_nonneg a b). lia.
Qed.
Lemma land_le_l : ltac2:(TCodec.tc2 tcn__ArtSizeLog "<'4&Czr2%3221&Br3%2214%7212p051pQJ:1pQH;1").
Proof.
intros a b Ha. pose proof (Z.lor_ldiff_and a b) as E. pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as E2.
rewrite E in E2.
replace (Z.land (Z.ldiff a b) (Z.land a b)) with 0 in E2
by (rewrite (Z.land_comm a b), Z.land_assoc, Z.land_ldiff, Z.land_0_l; reflexivity).
assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia). lia.
Qed.
Lemma land_range64 : ltac2:(TCodec.tc2 tcn__ArtSizeLog "H'4'2&Czr2%3221&F&I+2+R0%3221%5271%;271&Br4r3%3221%?2>1%<228%B221p0?1p091pQJF1pQHG1").
Proof. intros a b Ha Hb. pose proof (land_le_l a b ltac:(lia)). assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia). lia. Qed.
Definition smear1 (x : Z) : Z := Z.lor x (x / 2 ^ 1).
Definition smear2 (x : Z) : Z := let s := smear1 x in Z.lor s (s / 2 ^ 2).
Definition smear3 (x : Z) : Z := let s := smear2 x in Z.lor s (s / 2 ^ 4).
Definition smear4 (x : Z) : Z := let s := smear3 x in Z.lor s (s / 2 ^ 8).
Definition smear5 (x : Z) : Z := let s := smear4 x in Z.lor s (s / 2 ^ 16).
Definition smear (x : Z) : Z := let s := smear5 x in Z.lor s (s / 2 ^ 32).
Definition sm_spec (x w s : Z) : Prop := forall i, 0 <= i -> (Z.testbit s i = true <-> exists j, i <= j <= i + w - 1 /\ Z.testbit x j = true).
Lemma sm_spec_0 : ltac2:(TCodec.tc2 tcn__ArtSizeLog "6'4&<r1+1%33212pR<51").
Proof. intros x i Hi. split; [intros H; exists i; split; [lia|exact H] | intros (j & Hj & H); replace i with j by lia; exact H]. Qed.
Lemma sm_spec_step : ltac2:(TCodec.tc2 tcn__ArtSizeLog "I'4&Fzr2%3221&<r4r3%33215r5&H+2%2216&E&A&I%125:%32:1%52;1%>3:71p0<1p0A1pQNF1pR:G1pR<H1").
Proof.
intros x w s Hw P i Hi. rewrite Z.lor_spec, Z.div_pow2_bits by lia. rewrite Bool.orb_true_iff.
rewrite (P i Hi), (P (i + w)%Z ltac:(lia)).
split.
- intros [(j & Hj & H)|(j & Hj & H)]; exists j; (split; [lia|exact H]).
- intros (j & Hj & H). destruct (Z.lt_ge_cases j (i + w)) as [L|R].
+ left. exists j. split; [lia|exact H].
+ right. exists j. split; [lia|exact H].
Qed.
Lemma smear_spec : ltac2:(TCodec.tc2 tcn__ArtSizeLog "8'4&<r1+R0&=%113%53431pR<71").
Proof.
intros x. unfold smear, smear5, smear4, smear3, smear2, smear1. cbv zeta.
change 64 with (2 * 32). apply sm_spec_step; [lia|].
change 32 with (2 * 16). apply sm_spec_step; [lia|].
change 16 with (2 * 8). apply sm_spec_step; [lia|].
change 8 with (2 * 4). apply sm_spec_step; [lia|].
change 4 with (2 * 2) at 1. apply sm_spec_step; [lia|].
change 2 with (2 * 1) at 1. apply sm_spec_step; [lia|]. apply sm_spec_0.
Qed.
Lemma smear_nonneg_aux : ltac2:(TCodec.tc2 tcn__ArtSizeLog "A'4&Czr2%3221&Er3&A&I+2%2217%4251%7261%<2;1p0:1pQL?1pQH@1").
Proof. intros a k Ha. apply Z.lor_nonneg. split; [lia|]. destruct (Z.le_gt_cases 0 k). apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]. rewrite Z.pow_neg_r by lia. rewrite Z.div_0_r. lia. Qed.
Lemma smear_nonneg : ltac2:(TCodec.tc2 tcn__ArtSizeLog ";'4&Czr1%3221&=r2%211%7261p051pR<:1").
Proof.
intros x Hx. unfold smear, smear5, smear4, smear3, smear2, smear1. cbv zeta.
repeat (apply smear_nonneg_aux). lia.
Qed.
Theorem smear_eq : ltac2:(TCodec.tc2 tcn__ArtSizeLog "K'4'2&Fzr1%3221&I+2+R0%3221%8261%:261'3&=r2%211&J&@&D%115+1%4221%@2?1%7213%<3H91p0>1pR<J1").
Proof.
intros x Hx. pose proof (smear_spec x) as P. pose proof (smear_nonneg x ltac:(lia)) as NN.
assert (HL : 0 <= Z.log2 x) by (apply Z.log2_nonneg).
assert (HL' : Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia).
replace (2 ^ (Z.log2 x + 1) - 1) with (Z.ones (Z.log2 x + 1)) by (unfold Z.ones; rewrite Z.shiftl_1_l, <- Z.sub_1_r; reflexivity).
apply Z.bits_inj'. intros i Hi.
rewrite Z.testbit_ones_nonneg by lia.
destruct (Z.lt_ge_cases i (Z.log2 x + 1)) as [Lo|Hi'].
- replace (i <? Z.log2 x + 1) with true by (symmetry; apply Z.ltb_lt; lia).
apply (proj2 (P i Hi)). exists (Z.log2 x). split; [lia|]. apply Z.bit_log2. lia.
- replace (i <? Z.log2 x + 1) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.testbit (smear x) i) eqn:E; [|reflexivity]. exfalso.
apply (proj1 (P i Hi)) in E. destruct E as (j & Hj & Hb). rewrite Z.bits_above_log2 in Hb by lia. discriminate.
Qed.
Lemma smear_range64 : ltac2:(TCodec.tc2 tcn__ArtSizeLog "E'4'2&Fzr1%3221&I+2+R0%3221%8261%:261&C&=r2%211%42=1%?228%A221p081pR<D1").
Proof.
intros x Hx. rewrite smear_eq by lia. assert (HL' : Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). pose proof (Z.log2_nonneg x).
split. assert (0 < 2 ^ (Z.log2 x + 1)) by (apply Z.pow_pos_nonneg; lia). lia.
assert (2 ^ (Z.log2 x + 1) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Definition C55 : Z := 6148914691236517205.
Definition C33 : Z := 3689348814741910323.
Definition C0F : Z := 1085102592571150095.
Definition C01 : Z := 72340172838076673.
Definition slpop (y : Z) : Z :=
let t2 := Z.land (y / 2 ^ 1) C55 in
let t3 := y - t2 in
let t7 := Z.land t3 C33 + Z.land (t3 / 2 ^ 2) C33 in
let t9 := t7 + t7 / 2 ^ 4 in
let t10 := Z.land t9 C0F in
(t10 * C01) mod 2 ^ 64 / 2 ^ 56.
Definition slpop_ok (L : Z) : bool := slpop (2 ^ 64 - 1 - (2 ^ (L + 1) - 1)) =? 63 - L.
Lemma slpop_ok_all : ltac2:(TCodec.tc2 tcn__ArtSizeLog "<'3'0&?'4&;&>z+R0%3221%73651(1%;3:21").
Proof. vm_compute. reflexivity. Qed.
Theorem slpop_tab : ltac2:(TCodec.tc2 tcn__ArtSizeLog "M'4'2&Czr1%3221+QO%5231%7231'3&:&J&I+2+R0%3221+1%6221&@r2%2214%9281%;216%<261%>11%>2C6%A3J21p0C1p<L1").
Proof.
intros L HL. assert (Hin : In L (zrange 0 64)) by (unfold zrange; apply in_ziota; lia).
pose proof slpop_ok_all as H. rewrite forallb_forall in H. specialize (H L Hin). unfold slpop_ok in H. apply Z.eqb_eq in H. exact H.
Qed.
Definition lxor63_ok (a : Z) : bool := Z.lxor a 63 =? 63 - a.
Lemma lxor63_all : ltac2:(TCodec.tc2 tcn__ArtSizeLog "<'3'0&?'4&9&>z+R0%3221%73651(1%;3:21").
Proof. vm_compute. reflexivity. Qed.
Theorem lxor_63 : ltac2:(TCodec.tc2 tcn__ArtSizeLog "B'4'2&Czr1%3221+QO%5231%7231'3&Gr2%2216&J%1283%63?31p081pQHA1").
Proof.
intros a Ha. assert (Hin : In a (zrange 0 64)) by (unfold zrange; apply in_ziota; lia).
pose proof lxor63_all as H. rewrite forallb_forall in H. specialize (H a Hin). unfold lxor63_ok in H. apply Z.eqb_eq in H. exact H.
Qed.
Lemma slpop_ranges : ltac2:(TCodec.tc2 tcn__ArtSizeLog "RJ'4'2&Czr1%3221&F&I+2+R0%3221%5271%;271&B&Ar2+1%:291%4231&8%7221&Jr3%221C&@&7%=2F1%D2CC%>2H1%@214%6241+4%I2H1%C2M1%:2N1&6%G2Q01r5%Q42Q31r7%J21G%Q7241%Q9241%Q92Q83%Q624Q2%Q<221r4%Q=2Q<1%Q:22Q6%Q@221%Q424G%QA2Q@1%Q>22Q:%QD221%Q928M%QE2QD1%QF22O%QH221%Q=28Q1%QI2QH1%QJ22Q3%QL221%QL2QKQ8+QO%QI2QH1%QK2Q;1%R1241%QE2Q=Q3%R22R11%R322Q?%R5221%R52R4QH%R22QIQN%R8221%R921QN%R:251%R;2:1%R<2@1%R=2E1%R>2J1%R?2O1%R@2Q41%RA2Q81tR0RCQ?1tR8RDQB1tR6REQG1tR4RFQO1tR2RGR31p0R<1pR>RI1").
Proof.
intros y Hy. cbv zeta. unfold C33, C55, C0F. change (2 ^ 1) with 2. change (2 ^ 2) with 4. change (2 ^ 4) with 16.
pose proof (Z.div_mod y 2 ltac:(lia)). pose proof (Z.mod_pos_bound y 2 ltac:(lia)).
set (y2 := y / 2) in *.
assert (A : 0 <= Z.land y2 6148914691236517205 <= y2).
{ split. apply Z.land_nonneg; lia. apply land_le_l. lia. }
set (t2 := Z.land y2 6148914691236517205) in *.
pose proof (Z.div_mod (y - t2) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (y - t2) 4 ltac:(lia)).
set (t34 := (y - t2) / 4) in *.
assert (B1 : 0 <= Z.land (y - t2) 3689348814741910323 <= 3689348814741910323).
{ split. apply Z.land_nonneg; lia. rewrite Z.land_comm. apply land_le_l. lia. }
assert (B2 : 0 <= Z.land t34 3689348814741910323 <= 3689348814741910323).
{ split. apply Z.land_nonneg; lia. rewrite Z.land_comm. apply land_le_l. lia. }
set (t5 := Z.land (y - t2) 3689348814741910323) in *. set (t6 := Z.land t34 3689348814741910323) in *.
pose proof (Z.div_mod (t5 + t6) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (t5 + t6) 16 ltac:(lia)).
set (t8 := (t5 + t6) / 16) in *.
assert (Cc : 0 <= Z.land (t5 + t6 + t8) 1085102592571150095 <= 1085102592571150095).
{ split. apply Z.land_nonneg; lia. rewrite Z.land_comm. apply land_le_l. lia. }
lia.
Qed.
