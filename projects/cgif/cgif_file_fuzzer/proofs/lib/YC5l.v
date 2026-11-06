(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5r.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Lemma land_pow2 : forall x n, 0 <= n -> Z.land x (2 ^ n) = 2 ^ n * Z.b2z (Z.testbit x n).
Proof.
intros x n Hn. apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
destruct (Z.testbit x n) eqn:T.
- cbn [Z.b2z]. rewrite Z.mul_1_r, Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec n m) as [<-|Hne]; [rewrite T; reflexivity | apply andb_false_r].
- cbn [Z.b2z]. rewrite Z.mul_0_r, Z.bits_0. destruct (Z.eqb_spec n m) as [<-|Hne]; [rewrite T; reflexivity | apply andb_false_r].
Qed.
Lemma raw_attr_bits : forall x, 0 <= x ->
Z.lor ((x / 2) mod 2) (Z.land (x / 8) 2) = raw_attr_of x.
Proof.
intros x Hx. unfold raw_attr_of, YO07.flag.
assert (B1 : (x / 2) mod 2 = Z.b2z (Z.testbit x 1)).
{ rewrite Z.testbit_spec' by lia. reflexivity. }
assert (B4 : Z.land (x / 8) 2 = 2 * Z.b2z (Z.testbit x 4)).
{ change 8 with (2 ^ 3). change 2 with (2 ^ 1) at 2. rewrite land_pow2 by lia. rewrite Z.div_pow2_bits by lia. reflexivity. }
assert (L2 : Z.land x 2 = 2 * Z.b2z (Z.testbit x 1)) by (change 2 with (2 ^ 1) at 1; rewrite land_pow2 by lia; reflexivity).
assert (L16 : Z.land x 16 = 16 * Z.b2z (Z.testbit x 4)) by (change 16 with (2 ^ 4) at 1; rewrite land_pow2 by lia; reflexivity).
rewrite L2, L16, B1, B4. destruct (Z.testbit x 1), (Z.testbit x 4); reflexivity.
Qed.
Lemma ng_rattr_model : forall attr, 0 <= attr -> ng_rattr attr = raw_attr_of attr.
Proof.
intros attr Ha. unfold ng_rattr. rewrite <- (raw_attr_bits attr Ha). f_equal.
change (2 ^ 64) with (4 * 2 ^ 62). rewrite Z.mul_mod_distr_r by lia.
change (2 ^ 63) with (2 * 2 ^ 62). rewrite Z.div_mul_cancel_r by lia.
pose proof (Z.div_mod attr 4 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound attr 4 ltac:(lia)) as M4.
pose proof (Z.div_mod (attr / 2) 2 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (attr / 2) 2 ltac:(lia)) as M2.
pose proof (Z.div_mod attr 2 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound attr 2 ltac:(lia)) as M1.
assert (E : attr mod 4 = 2 * ((attr / 2) mod 2) + attr mod 2).
{ symmetry. apply (Z.mod_unique attr 4 ((attr / 2) / 2)); lia. }
rewrite E. symmetry. apply (Z.div_unique (2 * ((attr / 2) mod 2) + attr mod 2) 2 ((attr / 2) mod 2) (attr mod 2)); lia.
Qed.
Lemma np2_aux_ge : forall f n p, 0 <= p -> n <= 2 ^ (p + Z.of_nat f) -> n <= 2 ^ YO07.np2_aux f n p /\ p <= YO07.np2_aux f n p <= p + Z.of_nat f.
Proof.
induction f as [|f IH]; intros n p Hp Hn; cbn [YO07.np2_aux].
- rewrite Z.add_0_r in Hn. lia.
- destruct (Z.ltb_spec (2 ^ p) n) as [Hl|Hl].
+ assert (Hn' : n <= 2 ^ (p + 1 + Z.of_nat f)) by (replace (p + 1 + Z.of_nat f) with (p + Z.of_nat (S f)) by lia; exact Hn).
pose proof (IH n (p + 1) ltac:(lia) Hn'). lia.
+ lia.
Qed.
Lemma pal_pow_bounds : forall n, 0 <= n <= 256 -> n <= 2 ^ YO07.pal_pow n /\ 1 <= YO07.pal_pow n <= 8.
Proof.
intros n Hn. unfold YO07.pal_pow, YO07.calcNextPower2Ex.
pose proof (np2_aux_ge 17 n 0 ltac:(lia) ltac:(cbn; lia)) as [G1 G2].
assert (G3 : forall f p, 0 <= p <= 8 -> YO07.np2_aux f n p <= 8).
{ induction f as [|f IH]; intros p Hp; cbn [YO07.np2_aux]; [lia|].
destruct (Z.ltb_spec (2 ^ p) n) as [Hl|Hl]; [|lia].
assert (p < 8) by (destruct (Z.eq_dec p 8) as [->|]; [change (2 ^ 8) with 256 in Hl; lia | lia]).
apply IH. lia. }
pose proof (G3 17%nat 0 ltac:(lia)).
split; [| lia]. eapply Z.le_trans; [exact G1|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma raw_header_length : forall W H sgct gct rattr loops, 0 <= sgct <= 256 ->
Z.of_nat (length (YO07.raw_header W H sgct gct rattr loops)) <= 800.
Proof.
intros W H sgct gct rattr loops Hs. unfold YO07.raw_header, YO07.u16le, YO07.zeros.
rewrite !length_app.
assert (P : Z.of_nat (length (if sgct =? 0 then [] else firstn (Z.to_nat (sgct * 3)) gct ++ repeat 0 (Z.to_nat (((2 ^ YO07.pal_pow sgct - sgct) * 3) mod 65536)))) <= 768).
{ destruct (Z.eqb_spec sgct 0) as [->|Hnz]; [cbn; lia|].
rewrite length_app, repeat_length. pose proof (firstn_le_length (Z.to_nat (sgct * 3)) gct) as F.
destruct (pal_pow_bounds sgct Hs) as [T1 PP].
assert (T : 2 ^ YO07.pal_pow sgct <= 256) by (change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia).
rewrite Z.mod_small by lia. lia. }
assert (Q : Z.of_nat (length (if YO07.flag rattr 1 && negb (YO07.flag rattr 2)
then [33; 255; 11; 78; 69; 84; 83; 67; 65; 80; 69; 50; 46; 48; 3; 1] ++ [loops mod 256; loops / 256 mod 256] ++ [0] else [])) <= 19).
{ destruct (YO07.flag rattr 1 && negb (YO07.flag rattr 2)); cbn; lia. }
cbn [length] in *. lia.
Qed.
