(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require G.T_pe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1.
Open Scope Z_scope.

Local Notation d_fl := G.T_printf.d_fl.
Local Notation d_w := G.T_printf.d_w.
Local Notation d_p := G.T_printf.d_p.
Local Notation d_xp := G.T_printf.d_xp.
Local Notation d_t := G.T_printf.d_t.
Local Notation d_ty := G.T_printf.d_ty.

Lemma Zrange_forallb : forall (P : Z -> bool) (lo : Z) (n : nat),
forallb P (map (fun k => lo + Z.of_nat k) (seq 0 n)) = true ->
forall c, lo <= c < lo + Z.of_nat n -> P c = true.
Proof.
intros P lo n H c Hc. rewrite forallb_forall in H. apply H.
apply in_map_iff. exists (Z.to_nat (c - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Notation M64 := 18446744073709551615.

Lemma digit_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
Bool.eqb (Z.land (c + -48) M64 <=? 9) (is_digit c) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma digit_test : forall c, 0 <= c < 256 -> (Z.land (c + -48) M64 <= 9 <-> is_digit c = true).
Proof.
intros c Hc. pose proof (digit_testb c ltac:(cbn; lia)) as E.
destruct (Z.leb_spec0 (Z.land (c + -48) M64) 9); destruct (is_digit c); cbn in E; try discriminate.
all: split; intros; first [reflexivity | assumption | discriminate | lia].
Qed.
Lemma digit_range : forall c, is_digit c = true <-> 48 <= c <= 57.
Proof. intros c. unfold is_digit. rewrite andb_true_iff, !Z.leb_le. lia. Qed.

Lemma sp_testb : forall c, 0 <= c < 0 + Z.of_nat 256 ->
Bool.eqb (Z.land (c + -32) M64 <? 32) ((32 <=? c) && (c <? 64)) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma sp_test : forall c, 0 <= c < 256 -> (Z.land (c + -32) M64 < 32 <-> 32 <= c < 64).
Proof.
intros c Hc. pose proof (sp_testb c ltac:(cbn; lia)) as E.
destruct (Z.ltb_spec0 (Z.land (c + -32) M64) 32); destruct (Z.leb_spec0 32 c); destruct (Z.ltb_spec0 c 64); cbn in E; try discriminate; lia.
Qed.

Definition flagw (c : Z) : Z := Z.land (bv_swrap 32 (Z.shiftl 1 ((c + -32) mod 32))) M64.
Lemma flag_someb : forall c, 32 <= c < 32 + Z.of_nat 32 ->
match flag_bit c with None => true | Some b => (flagw c =? b) && (0 <=? b) && (b <? 131072) end = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma flag_some : forall c b, 32 <= c < 64 -> flag_bit c = Some b -> flagw c = b /\ 0 <= b < 131072.
Proof.
intros c b Hc Hb. pose proof (flag_someb c ltac:(cbn; lia)) as E. rewrite Hb in E.
rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3]. apply Z.eqb_eq in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3. lia.
Qed.
Lemma flag_bit_range : forall c, flag_bit c <> None -> 32 <= c < 64.
Proof.
intros c H. unfold flag_bit in H.
destruct (Z.leb_spec0 32 c); destruct (Z.ltb_spec0 c 64); cbn in H; try lia; exfalso; apply H; reflexivity.
Qed.

Lemma lor_bound17 : forall a b, 0 <= a < 131072 -> 0 <= b < 131072 -> 0 <= Z.lor a b < 131072.
Proof.
intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
change 131072 with (2^17) in *.
destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.lor_0_l; lia|].
destruct (Z.eq_dec b 0) as [->|]; [rewrite Z.lor_0_r; lia|].
apply Z.log2_lt_cancel. rewrite Z.log2_lor by lia. rewrite Z.log2_pow2 by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma parse_flags_cons_some : forall c s fl b, flag_bit c = Some b -> parse_flags (c :: s) fl = parse_flags s (Z.lor fl b).
Proof. intros c s fl b H. cbn. rewrite H. reflexivity. Qed.
Lemma parse_flags_cons_none : forall c s fl, flag_bit c = None -> parse_flags (c :: s) fl = (fl, c :: s).
Proof. intros c s fl H. cbn. rewrite H. reflexivity. Qed.
Lemma parse_flags_range : forall s fl, 0 <= fl < 131072 -> 0 <= fst (parse_flags s fl) < 131072.
Proof.
induction s as [|c s IH]; intros fl Hfl; cbn; [exact Hfl|].
destruct (flag_bit c) as [b|] eqn:E; [|exact Hfl].
apply IH. pose proof (flag_some c b (flag_bit_range c ltac:(congruence)) E) as [_ Hb]. apply lor_bound17; lia.
Qed.

Lemma getint_cons_digit : forall c s i, is_digit c = true ->
getint (c :: s) i = if (214748364 <? i) || (INT_MAX - 10 * i <? c - 48) then None else getint s (10 * i + (c - 48)).
Proof. intros c s i H. cbn [getint]. rewrite H. reflexivity. Qed.
Lemma getint_cons_nondigit : forall c s i, is_digit c = false -> getint (c :: s) i = Some (i, c :: s).
Proof. intros c s i H. cbn [getint]. rewrite H. reflexivity. Qed.
Lemma getint_some_range : forall s i w s', 0 <= i <= INT_MAX -> getint s i = Some (w, s') -> 0 <= w <= INT_MAX.
Proof.
induction s as [|c s IH]; intros i w s' Hi H; cbn [getint] in H.
- inversion H; subst. exact Hi.
- destruct (is_digit c) eqn:D.
+ destruct (214748364 <? i) eqn:E1; [discriminate|]. destruct (INT_MAX - 10 * i <? c - 48) eqn:E2; [discriminate|]. cbn in H.
apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. apply digit_range in D. unfold INT_MAX in *. eapply IH; [|exact H]. lia.
+ inversion H; subst. exact Hi.
Qed.

Lemma lxor_imax : forall x, 0 <= x <= 2147483647 -> Z.lxor x 2147483647 = 2147483647 - x.
Proof.
intros x Hx. change 2147483647 with (Z.ones 31).
assert (E : Z.lxor x (Z.ones 31) = (Z.lnot x) mod 2^31).
{ rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 31).
- rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 31; [apply Z.log2_lt_pow2; cbn in *; lia|lia]. }
rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2^31)) with (2^31 - 1).
replace (Z.lnot x) with (-x - 1) by (unfold Z.lnot; lia).
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by (cbn in *; lia). lia.
Qed.

Lemma parse_dir_shape : forall s d rest, parse_dir s = Some (d, rest) ->
match s with c0 :: c0b :: _ => is_digit c0 && (c0b =? 36) = false | [c0] => is_digit c0 = false | [] => True end /\
let (fl, s1) := parse_flags s 0 in
d_fl d = fl /\
exists c1 s1b, s1 = c1 :: s1b /\ c1 <> 42 /\
exists s2, getint s1 0 = Some (d_w d, s2) /\
exists c2 s2b, s2 = c2 :: s2b /\
( (c2 <> 46 /\ d_p d = -1 /\ d_xp d = false /\ tyspec (c2 :: s2b) = Some (d_ty d, d_t d, rest))
\/ (c2 = 46 /\ d_xp d = true /\ exists c3 s3b, s2b = c3 :: s3b /\ c3 <> 42 /\
exists s3, getint s2b 0 = Some (d_p d, s3) /\ tyspec s3 = Some (d_ty d, d_t d, rest)) ).
Proof.
intros s d rest H. unfold parse_dir in H.
split. { destruct s as [|c0 [|c0b s0]]; try exact I. { destruct (is_digit c0); [discriminate|reflexivity]. } destruct (is_digit c0 && (c0b =? 36)); [discriminate|reflexivity]. }
match type of H with (if ?pp then None else _) = _ => destruct pp; [discriminate|] end.
destruct (parse_flags s 0) as [fl s1].
destruct s1 as [|c1 s1b]; [discriminate|].
destruct (Z.eqb_spec c1 42) as [E42|N42]; [discriminate|].
destruct (getint (c1 :: s1b) 0) as [[w s2]|] eqn:G; [|discriminate].
destruct s2 as [|c2 s2b]; [discriminate|].
destruct (Z.eqb_spec c2 46) as [E46|N46].
- destruct s2b as [|c3 s3b]; [discriminate|]. destruct (Z.eqb_spec c3 42) as [E42'|N42']; [discriminate|].
destruct (getint (c3 :: s3b) 0) as [[p s3]|] eqn:G2; [|discriminate].
destruct s3 as [|t s4]; [discriminate|]. destruct (tyspec (t :: s4)) as [[[ty t'] s5]|] eqn:TS; [|discriminate].
injection H as <- <-. cbn. split; [reflexivity|]. exists c1, s1b. split; [reflexivity|]. split; [exact N42|].
exists (c2 :: c3 :: s3b). split; [first [reflexivity | exact G]|]. exists c2, (c3 :: s3b). split; [reflexivity|].
right. split; [exact E46|]. split; [reflexivity|]. exists c3, s3b. split; [reflexivity|]. split; [exact N42'|].
exists (t :: s4). split; [first [reflexivity | exact G2]|]. exact TS.
- destruct (tyspec (c2 :: s2b)) as [[[ty t'] s5]|] eqn:TS; [|discriminate]. injection H as <- <-. cbn.
split; [reflexivity|]. exists c1, s1b. split; [reflexivity|]. split; [exact N42|].
exists (c2 :: s2b). split; [first [reflexivity | exact G]|]. exists c2, s2b. split; [reflexivity|].
left. split; [exact N46|]. repeat split; first [reflexivity | exact TS].
Qed.

Lemma tyspec_shape : forall s ty t rest, tyspec s = Some (ty, t, rest) ->
(s = t :: rest /\ t <> 108 /\ conv_type t = Some ty) \/ (s = 108 :: t :: rest /\ conv_type_l t = Some ty).
Proof.
intros s ty t rest H. unfold tyspec in H. destruct s as [|c s4]; [discriminate|].
destruct (Z.eqb_spec c 108) as [E|N].
- destruct s4 as [|t2 s5]; [discriminate|]. destruct (conv_type_l t2) as [ty'|] eqn:CT; [|discriminate].
injection H as <- <- <-. right. subst c. split; [reflexivity | exact CT].
- destruct (conv_type c) as [ty'|] eqn:CT; [|discriminate]. injection H as <- <- <-. left. repeat split; assumption.
Qed.
Lemma conv_type_l_ty : forall t ty, conv_type_l t = Some ty -> (ty = T_LONG /\ (t = 100 \/ t = 105)) \/ (ty = T_ULONG /\ t = 117).
Proof.
intros t ty H. unfold conv_type_l in H.
destruct (Z.eqb_spec t 100); [injection H as <-; left; split; [reflexivity|left; assumption]|].
destruct (Z.eqb_spec t 105); [injection H as <-; left; split; [reflexivity|right; assumption]|].
cbn in H. destruct (Z.eqb_spec t 117); [injection H as <-; right; split; [reflexivity|assumption]|]. discriminate.
Qed.
Lemma conv_type_l_conv_type : forall t ty, conv_type_l t = Some ty -> exists ty0, conv_type t = Some ty0.
Proof.
intros t ty H. destruct (conv_type_l_ty t ty H) as [[_ [-> | ->]] | [_ ->]]; eexists; reflexivity.
Qed.

Definition STATES1 : list Z :=
[25; 0; 0; 0; 25; 25; 25; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 14; 0; 0; 0; 0; 0; 0; 0; 0; 25; 0; 11; 13; 25; 25; 25; 0; 13; 0; 0; 2; 0; 9; 14; 0; 0; 0; 9; 0; 14; 0; 0; 14; 0; 0].
Lemma states1_conv : forall t ty, conv_type_l t = Some ty -> znth STATES1 (t - 65) = ty.
Proof. intros t ty H. destruct (conv_type_l_ty t ty H) as [[-> [-> | ->]] | [-> ->]]; reflexivity. Qed.
Lemma parse_dir_ty_ok : forall s d rest, parse_dir s = Some (d, rest) -> dir_ty_ok d.
Proof.
intros s d rest PD. destruct (parse_dir_shape _ _ _ PD) as (_ & SH). destruct (parse_flags s 0) as [fl0 s1'].
destruct SH as (_ & c1 & s1b & _ & _ & s2 & _ & c2 & s2b & _ & PX).
assert (TS : exists s3, tyspec s3 = Some (d_ty d, d_t d, rest)).
{ destruct PX as [(_ & _ & _ & TS) | (_ & _ & c3 & s3b & _ & _ & s3 & _ & TS)]; eexists; exact TS. }
destruct TS as [s3 TS]. unfold dir_ty_ok, d_ps.
destruct (tyspec_shape _ _ _ _ TS) as [(_ & _ & CT) | (_ & CT)].
- left. split; [exact CT|]. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL, T_LONG, T_ULONG in *.
repeat match type of CT with (if ?c then _ else _) = _ => destruct c; [injection CT as E; rewrite <- E; reflexivity|] end. discriminate.
- right. split; [exact CT|]. destruct (conv_type_l_ty _ _ CT) as [[-> _] | [-> _]]; reflexivity.
Qed.

Lemma parse_flags_suffix : forall s acc fl s1, parse_flags s acc = (fl, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof.
induction s as [|c s IH]; intros acc fl s1 H; cbn in H.
- injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
- destruct (flag_bit c) as [b|].
+ destruct (IH _ _ _ H) as (n & -> & Hn). exists (S n). split; [reflexivity | cbn; lia].
+ injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
Qed.
Lemma getint_suffix : forall s acc w s1, getint s acc = Some (w, s1) -> exists n, s1 = skipn n s /\ (n <= length s)%nat.
Proof.
induction s as [|c s IH]; intros acc w s1 H; cbn [getint] in H.
- injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
- destruct (is_digit c).
+ destruct (_ || _); [discriminate|]. destruct (IH _ _ _ H) as (n & -> & Hn). exists (S n). split; [reflexivity | cbn; lia].
+ injection H as _ <-. exists 0%nat. split; [reflexivity | cbn; lia].
Qed.

Definition STATES0 : list Z :=
[25; 0; 11; 0; 25; 25; 25; 0; 0; 0; 0; 5; 0; 0; 0; 0; 0; 0; 9; 0; 0; 0; 0; 11; 0; 0; 0; 0; 0; 0; 0; 0; 25; 0; 10; 10; 25; 25; 25; 3; 10; 7; 0; 1; 27; 9; 11; 24; 0; 0; 9; 6; 11; 0; 0; 11; 0; 6].
Lemma conv_type_range : forall t ty, conv_type t = Some ty -> 65 <= t <= 122.
Proof.
intros t ty H. unfold conv_type in H.
repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [try (injection H as <-)|] end; try discriminate;
repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end; try lia.
Qed.
Lemma states0_conv : forall t ty, conv_type t = Some ty -> znth STATES0 (t - 65) = ty.
Proof.
intros t ty H. unfold conv_type in H.
repeat match type of H with (if ?c then _ else _) = _ => destruct c eqn:?; [injection H as <-|] end; try discriminate;
repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E; subst; reflexivity | E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] end.
Qed.

Lemma conv_type_ty : forall t ty, conv_type t = Some ty -> ty = 9 \/ ty = 10 \/ ty = 11 \/ ty = 25.
Proof.
intros t ty H. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in H.
repeat match type of H with (if ?c then _ else _) = _ => destruct c; [injection H as <-; lia|] end. discriminate.
Qed.

Lemma land_M64_neg : forall x, - 2^64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2^64.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma land_bound : forall a m, 0 <= a -> 0 <= m -> 0 <= Z.land a m <= a.
Proof.
intros a m Ha Hm. split; [apply Z.land_nonneg; left; exact Ha|].
pose proof (Z.sub_land_same_l a m) as E.
assert (0 <= Z.land a (Z.lnot m))%Z by (apply Z.land_nonneg; left; exact Ha).
lia.
Qed.

Section G.

Local Definition gw_tbl_0 := tt.

#[using="Type"] Lemma gw_all : True. Proof. exact I. Qed.

#[using="Type"] Lemma flag_noneb : forall c, 32 <= c < 32 + Z.of_nat 32 ->
Bool.eqb (Z.land (flagw c) 75913 =? 0) (match flag_bit c with None => true | Some _ => false end) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma flag_none : forall c, 32 <= c < 64 -> (Z.land (flagw c) 75913 = 0 <-> flag_bit c = None).
Proof.
intros c Hc. pose proof (flag_noneb c ltac:(cbn; lia)) as E.
destruct (Z.eqb_spec (Z.land (flagw c) 75913) 0); destruct (flag_bit c); cbn in E; try discriminate.
all: split; intros; first [reflexivity | assumption | discriminate | congruence | lia].
Qed.

#[using="Type"] Lemma nzmask_bits : forall n, 0 <= n < 0 + Z.of_nat 64 -> Bool.eqb (Z.testbit 18446744073709486079 n) (negb (Z.testbit 65536 n)) = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma nzmask_eq : forall fl, 0 <= fl < 131072 -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
Proof.
intros fl Hfl. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases n 64).
- pose proof (nzmask_bits n ltac:(cbn; lia)) as E. destruct (Z.testbit 18446744073709486079 n), (Z.testbit 65536 n); cbn in E; try discriminate; reflexivity.
- replace (Z.testbit fl n) with false; [reflexivity|]. symmetry.
destruct (Z.eq_dec fl 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply Z.lt_le_trans with 17%Z; [apply Z.log2_lt_pow2; cbn in *; lia|lia].
Qed.

End G.
