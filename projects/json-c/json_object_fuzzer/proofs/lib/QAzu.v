(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith.
Open Scope Z_scope.

Definition APE_ERRMEM : Z := 0x99530.
Definition APE_ERRMEM2 : Z := 0x99340.
End Mq0.
From Stdlib Require Bool Lia Floats.SpecFloat.
From LinuxProcessSemantics.Riscv Require Fpu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import Stdlib.Floats.SpecFloat.
Import LinuxProcessSemantics.Riscv.Fpu.
Open Scope Z_scope.

Section SF.
Implicit Types (d : spec_float).

Lemma sf_flip : forall a b c, SFcompare a b = Some c -> SFcompare b a = Some (CompOpp c).
Proof.
intros a b c H.
destruct a as [sa|sa| |sa ma ea], b as [sb|sb| |sb mb eb]; cbn in H |- *; try discriminate;
try (destruct sa); try (destruct sb); cbn in H |- *; try (injection H as <-; reflexivity); try discriminate.
all: rewrite (Z.compare_antisym ea eb); destruct (ea ?= eb) eqn:E; cbn in H |- *; try (injection H as <-; reflexivity).
all: injection H as <-.
all: rewrite (Pos.compare_cont_antisym ma mb Eq); cbn; destruct (Pos.compare_cont Eq mb ma); reflexivity.
Qed.

Lemma sf_total : forall a b, a <> S754_nan -> b <> S754_nan -> exists c, SFcompare a b = Some c.
Proof.
intros a b Ha Hb. destruct a as [sa|sa| |sa ma ea], b as [sb|sb| |sb mb eb]; cbn; try congruence; eauto;
try (destruct sa); try (destruct sb); eauto.
Qed.

Lemma sf_not_le_lt : forall K d, d <> S754_nan -> K <> S754_nan ->
SFcompare K d <> Some Lt -> SFcompare K d <> Some Eq -> SFcompare d K = Some Lt.
Proof.
intros K d Hd HK H1 H2. destruct (sf_total K d HK Hd) as [c Hc].
destruct c; try congruence. apply sf_flip in Hc. exact Hc.
Qed.

Lemma sf_lo_neg : forall (mK mU : positive) (e : Z) d, (mK < mU)%positive -> d <> S754_nan ->
SFcompare d (S754_finite true mK e) <> Some Lt -> SFcompare (S754_finite true mU e) d = Some Lt.
Proof.
intros mK mU e d HM Hd H.
destruct d as [s|s| |s m ed]; cbn in H |- *; try congruence.
- destruct s; cbn in H |- *; congruence.
- destruct s; cbn in H |- *; [| reflexivity].
rewrite (Z.compare_antisym ed e). destruct (ed ?= e) eqn:E; cbn in H |- *; try reflexivity; try congruence.
apply Z.compare_eq_iff in E. subst ed.
rewrite !Pos.compare_cont_spec in H |- *. cbn in H |- *.
destruct (m ?= mK)%positive eqn:C; cbn in H; try congruence.
+ apply Pos.compare_eq_iff in C. subst m. rewrite (proj2 (Pos.compare_gt_iff mU mK)) by lia. reflexivity.
+ rewrite Pos.compare_lt_iff in C. rewrite (proj2 (Pos.compare_gt_iff mU m)) by lia. reflexivity.
Qed.

Lemma sf_hi_pos : forall (mK mU : positive) (eK eU : Z) d, eK < eU -> d <> S754_nan ->
SFcompare (S754_finite false mK eK) d <> Some Lt -> SFcompare d (S754_finite false mU eU) = Some Lt.
Proof.
intros mK mU eK eU d HE Hd H.
destruct d as [s|s| |s m ed]; cbn in H |- *; try congruence.
- destruct s; cbn in H |- *; congruence.
- destruct s; cbn in H |- *; [reflexivity |].
destruct (eK ?= ed) eqn:E; cbn in H; try congruence.
+ apply Z.compare_eq_iff in E. subst ed. rewrite (proj2 (Z.compare_lt_iff eK eU) HE). reflexivity.
+ apply Z.compare_gt_iff in E. rewrite (proj2 (Z.compare_lt_iff ed eU)) by lia. reflexivity.
Qed.

Lemma sf_lo_zero : forall (mU : positive) (eU : Z) (sz : bool) d, d <> S754_nan ->
SFcompare d (S754_zero sz) <> Some Lt -> SFcompare (S754_finite true mU eU) d = Some Lt.
Proof.
intros mU eU sz d Hd H.
destruct d as [s|s| |s m ed]; cbn in H |- *; try congruence; destruct s; cbn in H |- *; congruence.
Qed.
End SF.

Definition D64 := fmt_double.

Lemma land_ones_nonneg : forall x n, 0 <= n -> 0 <= Z.land x (Z.ones n).
Proof. intros. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma fp_decode_nan_is_nan : forall x, 0 <= x -> fp_decode D64 x = S754_nan -> fp_is_nan D64 x = true.
Proof.
intros x Hx H. unfold fp_decode, fp_is_nan in *.
set (e := fp_exp_field D64 x) in *. set (m := fp_man_field D64 x) in *.
assert (Hm : 0 <= m) by (unfold m, fp_man_field; apply land_ones_nonneg; cbn; lia).
destruct (e =? 0) eqn:E0.
- destruct m; try discriminate; lia.
- destruct (e =? Z.ones (fp_ew D64)) eqn:E1.
+ destruct (m =? 0) eqn:M; [discriminate | reflexivity].
+ exfalso. change (Z.shiftl 1 (fp_mw D64)) with 4503599627370496 in H.
destruct (4503599627370496 + m) eqn:Q; try discriminate; lia.
Qed.

Lemma nan_test_clear : forall x, 0 <= x < 2^64 -> x mod 2^63 < 9218868437227405313 -> fp_is_nan D64 x = false.
Proof.
intros x Hx Ht. unfold fp_is_nan, fp_exp_field, fp_man_field.
change (fp_mw D64) with 52. change (fp_ew D64) with 11.
rewrite !Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
change (Z.ones 11) with 2047.
destruct (x / 2 ^ 52 mod 2 ^ 11 =? 2047) eqn:E; [| reflexivity].
destruct (x mod 2 ^ 52 =? 0) eqn:M; [reflexivity |]. exfalso.
apply Z.eqb_eq in E. apply Z.eqb_neq in M.
pose proof (Z.mod_pos_bound x (2^52) ltac:(lia)). pose proof (Z.mod_pos_bound x (2^63) ltac:(lia)).
assert (E2 : x mod 2^63 = (x / 2^52) mod 2^11 * 2^52 + x mod 2^52).
{ rewrite (Z.div_mod x (2^63)) at 2 3 by lia. Z.div_mod_to_equations. nia. }
lia.
Qed.

Definition flt (a b : Z) : bool := fst (fp_lt D64 a b).
Definition fle (a b : Z) : bool := fst (fp_le D64 a b).

Lemma flt_sf : forall a b, flt a b = match SFcompare (fp_decode D64 a) (fp_decode D64 b) with Some Lt => true | _ => false end.
Proof. reflexivity. Qed.
Lemma fle_sf : forall a b, fle a b = match SFcompare (fp_decode D64 a) (fp_decode D64 b) with Some Lt | Some Eq => true | _ => false end.
Proof. reflexivity. Qed.

Lemma not_nan_decode : forall x, 0 <= x -> fp_is_nan D64 x = false -> fp_decode D64 x <> S754_nan.
Proof. intros x Hx H E. rewrite (fp_decode_nan_is_nan x Hx E) in H. discriminate. Qed.

Definition B_I32MIN  : Z := 0xC1E0000000000000.
Definition B_I32MINU : Z := 0xC1E0000000200000.
Definition B_I32MAX  : Z := 0x41DFFFFFFFC00000.
Definition B_I32MAXU : Z := 0x41E0000000000000.
Definition B_I64MIN  : Z := 0xC3E0000000000000.
Definition B_I64MINU : Z := 0xC3E0000000000001.
Definition B_I64MAX  : Z := 0x43E0000000000000.
Definition B_U64MAX  : Z := 0x43F0000000000000.
Definition B_M1      : Z := 0xBFF0000000000000.

Section Facts.
Variable x : Z.
Hypothesis X : 0 <= x < 2^64.
Hypothesis NN : fp_is_nan D64 x = false.
Let DX : fp_decode D64 x <> S754_nan := not_nan_decode x (proj1 X) NN.

Lemma ub_i32_lo : flt x B_I32MIN = false -> flt B_I32MINU x = true.
Proof.
rewrite !flt_sf. change (fp_decode D64 B_I32MIN) with (S754_finite true 4503599627370496 (-21)).
change (fp_decode D64 B_I32MINU) with (S754_finite true 4503599629467648 (-21)). intros H.
rewrite (sf_lo_neg 4503599627370496 4503599629467648 (-21) _ ltac:(reflexivity) DX); [reflexivity |].
intros E; rewrite E in H; discriminate.
Qed.

Lemma ub_i32_hi : flt B_I32MAX x = false -> flt x B_I32MAXU = true.
Proof.
rewrite !flt_sf. change (fp_decode D64 B_I32MAX) with (S754_finite false 9007199250546688 (-22)).
change (fp_decode D64 B_I32MAXU) with (S754_finite false 4503599627370496 (-21)). intros H.
rewrite (sf_hi_pos 9007199250546688 4503599627370496 (-22) (-21) _ ltac:(reflexivity) DX); [reflexivity |].
intros E; rewrite E in H; discriminate.
Qed.

Lemma ub_i64_lo : flt x B_I64MIN = false -> flt B_I64MINU x = true.
Proof.
rewrite !flt_sf. change (fp_decode D64 B_I64MIN) with (S754_finite true 4503599627370496 11).
change (fp_decode D64 B_I64MINU) with (S754_finite true 4503599627370497 11). intros H.
rewrite (sf_lo_neg 4503599627370496 4503599627370497 11 _ ltac:(reflexivity) DX); [reflexivity |].
intros E; rewrite E in H; discriminate.
Qed.

Lemma ub_i64_hi : fle B_I64MAX x = false -> flt x B_I64MAX = true.
Proof.
rewrite fle_sf, flt_sf. change (fp_decode D64 B_I64MAX) with (S754_finite false 4503599627370496 11). intros H.
assert (NK : S754_finite false 4503599627370496 11 <> S754_nan) by discriminate.
rewrite (sf_not_le_lt _ _ DX NK); [reflexivity | |]; intros E; rewrite E in H; discriminate.
Qed.

Lemma ub_u64_hi : fle B_U64MAX x = false -> flt x B_U64MAX = true.
Proof.
rewrite fle_sf, flt_sf. change (fp_decode D64 B_U64MAX) with (S754_finite false 4503599627370496 12). intros H.
assert (NK : S754_finite false 4503599627370496 12 <> S754_nan) by discriminate.
rewrite (sf_not_le_lt _ _ DX NK); [reflexivity | |]; intros E; rewrite E in H; discriminate.
Qed.

Lemma ub_u64_lo : flt x 0 = false -> flt B_M1 x = true.
Proof.
rewrite !flt_sf. change (fp_decode D64 0) with (S754_zero false).
change (fp_decode D64 B_M1) with (S754_finite true 4503599627370496 (-52)). intros H.
rewrite (sf_lo_zero 4503599627370496 (-52) false _ DX); [reflexivity |].
intros E; rewrite E in H; discriminate.
Qed.
End Facts.
End Mq1.

From Stdlib Require Import ZArith List Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Definition ub_ins_list : list Z := [
0x926cc; 0x926d0; 0x92710; 0x92dbc; 0x92dc0; 0x92dc4; 0x92dc8; 0x92dcc; 0x92dd0; 0x92edc; 0x92ee0; 0x92ee4; 0x92ee8; 0x92eec; 0x92ef0; 0x93310;
0x93314; 0x9385c; 0x93860; 0x93864; 0x93868; 0x9386c; 0x9937c; 0x99380; 0x99384; 0x9b2f4; 0x9b2f8; 0x9b42c; 0x9b430; 0x9b544; 0x9b548; 0x9b54c;
0x9b578; 0x9b57c; 0x9b580; 0x9b584; 0x9b590; 0x9b594; 0x9b598; 0x9b5d0; 0x9b5d4; 0x9b5d8; 0x9b5dc; 0x9b5e0; 0x9b5e4; 0x9b618; 0x9b61c; 0x9b620;
0x9b6f0; 0x9b6f4; 0x9b6f8; 0x9b6fc; 0x9b700; 0x9b724; 0x9b728; 0x9b72c; 0x9b730; 0x9b734; 0x9b738; 0x9b73c; 0x9b740; 0x9b794; 0x9b798; 0x9b79c;
0x9b7a0; 0x9b7a4; 0x9b7a8; 0x9b7ac; 0x9b7b0; 0x9b7b4; 0x9bb5c; 0x9bb60; 0x9bb64; 0x9bb68; 0x9bb6c; 0x9bb70; 0x9bb74; 0x9bb78; 0x9bb7c; 0x9bc5c;
0x9bc60; 0x9bc64; 0x9bc88; 0x9bcfc; 0x9bd00; 0x9bd68; 0x9bd6c; 0x9be90; 0x9be94; 0x9be98; 0x9bef4; 0x9bef8; 0x9befc; 0x9bf7c; 0x9bf80; 0x9bf84;
0x9c060; 0x9c064; 0x9c4c4; 0x9c4c8; 0x9c550; 0x9c554; 0x9c558; 0x9c8e0; 0x9c8e4; 0x9c8e8; 0x9ca68; 0x9cac4; 0x9cac8; 0x9ceb8; 0x9cebc; 0x9d068;
0x9d06c; 0x9d394; 0x9d398; 0x9d480; 0x9d484; 0x9d488; 0x9d534; 0x9d538; 0x9d53c; 0x9d5f4; 0x9d5f8; 0x9d694; 0x9d698; 0x9d6c0; 0x9d724; 0x9d728;
0x9d854; 0x9d858; 0x9d984; 0x9d988; 0x9db5c; 0x9db60; 0x9dc08; 0x9dc0c; 0x9de4c; 0x9de50; 0x9de54; 0x9de70; 0x9de74; 0x9e1dc; 0x9e1e0; 0x9e288;
0x9e28c; 0x9e354; 0x9e358; 0x9e590; 0x9e594; 0x9e598; 0x9e5b4; 0x9e5b8; 0x9e9c8; 0x9e9cc; 0x9e9d0; 0x9e9ec; 0x9e9f0; 0x9ed18; 0x9ed1c; 0x9f2fc;
0x9f300; 0x9f324; 0x9f370; 0x9f374; 0x9f400; 0x9f404; 0x9f584; 0x9f588; 0x9f6dc; 0x9f6e0; 0x9f6e4; 0x9f7e0; 0x9f7e4; 0x9f7e8; 0x9f7ec; 0x9f870;
0x9f874; 0x9f878; 0x9f87c; 0x9f9f4; 0x9f9f8; 0x9fd60; 0x9fd64; 0x9fd68; 0x9fd6c; 0x9fd70; 0x9fd74; 0x9fd78; 0x9fd7c; 0x9fdb4; 0x9fdb8; 0x9fdbc;
0x9ff04; 0x9ff08; 0xa01ac; 0xa01b0; 0xa026c; 0xa0270; 0xa0364; 0xa0368; 0xa036c; 0xa0400; 0xa0404; 0xa04f0; 0xa04f4; 0xa067c; 0xa0680; 0xa0684;
0xa0688; 0xa068c; 0xa0690; 0xa0778; 0xa077c; 0xa08c0; 0xa08c4; 0xa0938; 0xa093c; 0xa0940; 0xa0984; 0xa0988; 0xa098c; 0xa09d0; 0xa09d4; 0xa09d8;
0xa0a20; 0xa0a24; 0xa0a28; 0xa0b20; 0xa0b24; 0xa0d14; 0xa0d18; 0xa1004; 0xa1008; 0xa1078; 0xa107c; 0xa1504; 0xa1508; 0xa1528; 0xa152c; 0xa1530;
0xa178c; 0xa1790; 0xa1794; 0xa1878; 0xa187c; 0xa1880; 0xa1944; 0xa1948; 0xa194c; 0xa19f4; 0xa19f8; 0xa19fc; 0xa1ef8; 0xa1efc; 0xa1f00; 0xa1f04;
0xa1f08; 0xa1f0c; 0xa1f10; 0xa1f14; 0xa1f18; 0xa1fcc; 0xa1fd0; 0xa1fd4; 0xa1fd8; 0xa1fdc; 0xa1fe0; 0xa1fe4; 0xa1fe8; 0xa2038; 0xa203c; 0xa2040;
0xa2044; 0xa2048; 0xa204c; 0xa2050; 0xa2054; 0xa2058; 0xa22a8; 0xa22ac; 0xa2420; 0xa2424; 0xa24e8; 0xa24ec; 0xa24f0; 0xa2538; 0xa253c; 0xa2540;
0xa2544; 0xa2548; 0xa254c; 0xa2550; 0xa2554; 0xa2558; 0xa255c; 0xa2560; 0xa2564; 0xa25c0; 0xa25c4; 0xa25c8; 0xa271c; 0xa2720; 0xa2724; 0xa276c;
0xa2770; 0xa2774; 0xa2778; 0xa277c; 0xa2780; 0xa2784; 0xa2788; 0xa278c; 0xa2790; 0xa2794; 0xa2798; 0xa2810; 0xa2814; 0xa2818; 0xa28f4; 0xa28f8;
0xa28fc; 0xa2900; 0xa2904; 0xa2908; 0xa290c; 0xa2910; 0xa2914; 0xa2918; 0xa291c; 0xa2920; 0xa29cc; 0xa29d0; 0xa29d4; 0xa2a5c; 0xa2a60; 0xa2a64;
0xa2b04; 0xa2b08; 0xa2b0c; 0xa2b10; 0xa2b14; 0xa2b18; 0xa2b1c; 0xa2b20; 0xa2b24; 0xa2b28; 0xa2d9c; 0xa2da0; 0xa2da4; 0xa2f24; 0xa2f28; 0xa2f40;
0xa2f44; 0xa2f48; 0xa3094; 0xa3098; 0xa309c; 0xa30a0; 0xa30a4; 0xa30a8; 0xa3100; 0xa3104; 0xa3108; 0xa339c; 0xa33a0; 0xa33c0; 0xa33c4; 0xa33c8;
0xa33ec; 0xa3444; 0xa3488; 0xa348c; 0xa3490; 0xa34b4; 0xa34b8; 0xa34bc; 0xa34e0; 0xa34e4; 0xa34e8; 0xa3510; 0xa3514; 0xa3530; 0xa3534; 0xa3538;
0xa3588; 0xa358c; 0xa3590; 0xa35dc; 0xa35e0; 0xa35e4; 0xa3660; 0xa3680; 0xa3684; 0xa3688; 0xa36ac; 0xa36b0; 0xa36b4; 0xa36dc; 0xa36e0; 0xa3700;
0xa3704; 0xa3708; 0xa370c; 0xa3710; 0xa3714; 0xa3718; 0xa371c; 0xa3758; 0xa375c; 0xa3760; 0xa3764; 0xa377c; 0xa3780; 0xa3784; 0xa3788; 0xa378c;
0xa37d0; 0xa37d4; 0xa37f4; 0xa37f8; 0xa37fc; 0xa3848; 0xa384c; 0xa3850; 0xa3870; 0xa3874; 0xa3878; 0xa38a0; 0xa38a4; 0xa38a8; 0xa38ac; 0xa38c4;
0xa38c8; 0xa38cc; 0xa38d0; 0xa38d4; 0xa3900; 0xa3904; 0xa3908; 0xa390c; 0xa3910; 0xa3968; 0xa396c; 0xa3970; 0xa3974; 0xa3988; 0xa398c; 0xa3990;
0xa3998; 0xa399c; 0xa39b8; 0xa39bc; 0xa39c0; 0xa39c4; 0xa39c8; 0xa39f4; 0xa39f8; 0xa39fc; 0xa3a00; 0xa3a60; 0xa3a64; 0xa3a84; 0xa3a88; 0xa3a8c;
0xa3a90; 0xa3a94; 0xa3aa8; 0xa3aac; 0xa3ab0; 0xa3ab8; 0xa3abc; 0xa3ad4; 0xa3ad8; 0xa3adc; 0xa3ae0; 0xa3ae4; 0xa3b34; 0xa3b38; 0xa3b58; 0xa3b5c;
0xa3b60; 0xa3b80; 0xa3b84; 0xa3ba8; 0xa3bac; 0xa3bb0; 0xa3bb4; 0xa3bb8; 0xa3bcc; 0xa3bd0; 0xa3bd4; 0xa3bd8; 0xa3bdc; 0xa3c24; 0xa3c28; 0xa3c44;
0xa3c48; 0xa3c4c; 0xa3c50; 0xa3c54; 0xa4178; 0xa417c; 0xa4388; 0xa438c; 0xa449c; 0xa44a0; 0xa47bc; 0xa47c0; 0xa47c4; 0xa48c0; 0xa48c4; 0xa48c8;
0xa48cc; 0xa48d0; 0xa48d4; 0xa48d8; 0xa48dc; 0xa48e0; 0xa48e4; 0xa48e8; 0xa48ec; 0xa48f0; 0xa48f4; 0xa48f8; 0xa49f4; 0xa49f8; 0xa49fc; 0xa4bc4;
0xa4bc8; 0xa4bcc; 0xa4bd0; 0xa4d58; 0xa4d5c; 0xa4d60; 0xa4d64; 0xa4d68; 0xa4d6c; 0xa4d70; 0xa4d74; 0xa4d78; 0xa4d7c; 0xa4d80; 0xa4d84; 0xa4e4c;
0xa4e50; 0xa4e54; 0xa4e58; 0xa4e5c; 0xa4e60; 0xa4f08; 0xa4f0c; 0xa4f10; 0xa4f14; 0xa4f18; 0xa4f1c; 0xa4f20; 0xa4f24; 0xa4fc0; 0xa4fc4; 0xa4fc8;
0xa4fcc; 0xa4fd0; 0xa4fd4; 0xa4fd8; 0xa4fdc; 0xa514c; 0xa5150; 0xa5154; 0xa53a4; 0xa53a8; 0xa53ac; 0xa5574; 0xa5578; 0xa557c; 0xa5b78; 0xa5b7c;
0xa5bdc; 0xa5be0; 0xa6168; 0xa6170; 0xa6174; 0xa61a8; 0xa61ac; 0xa61b0; 0xa63f4; 0xa63fc; 0xa6400; 0xa6490; 0xa6494; 0xa6498; 0xa688c; 0xa6890;
0xa6894; 0xa68cc; 0xa68d0].
Definition ub_ins (pc : Z) : bool := existsb (Z.eqb pc) ub_ins_list.
