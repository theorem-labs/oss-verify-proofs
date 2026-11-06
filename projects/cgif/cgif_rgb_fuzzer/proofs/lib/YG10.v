(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition shadow_of_addr (B a : Z) : Z := B + a / 8.
Lemma shadow_of_addr_granule : forall B a, shadow_of_addr B a = shadow_of_addr B (8 * (a / 8)).
Proof. intros B a. unfold shadow_of_addr. f_equal. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.

Lemma shadow_of_addr_aligned_off : forall B p c,
p mod 8 = 0 -> shadow_of_addr B (p + c) = shadow_of_addr B p + c / 8.
Proof.
intros B p c Hp. unfold shadow_of_addr. rewrite <- Z.add_assoc. f_equal.
rewrite (Z.div_mod p 8) at 1 by lia. rewrite Hp, Z.add_0_r.
replace (8 * (p / 8) + c) with (c + (p / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.
Lemma shadow_of_addr_same_granule : forall B x e,
8 * (x / 8) <= e <= 8 * (x / 8) + 7 -> shadow_of_addr B e = shadow_of_addr B x.
Proof.
intros B x e He. rewrite (shadow_of_addr_granule B e), (shadow_of_addr_granule B x). f_equal. f_equal.
symmetry. apply Z.div_unique with (r := e - 8 * (x / 8)); lia.
Qed.
Definition saddr_ok (x s : Z) : Prop := s = 0 \/ (x mod 8 < s /\ s < 8).
Section b.
Variable rd : Z -> option Z.
Variable B : Z.
Definition range_addressable (a len : Z) : Prop :=
forall x, a <= x < a + len -> exists s, rd (shadow_of_addr B x) = Some s /\ saddr_ok x s.
Definition zero_shadow (a len : Z) : Prop :=
forall i, 0 <= i < len / 8 -> rd (shadow_of_addr B a + i) = Some 0.
Definition block_shadow (p n : Z) : Prop :=
p mod 8 = 0 /\ 0 <= n /\
forall i, 0 <= i < (n + 7) / 8 ->
rd (shadow_of_addr B p + i) = Some (if i <? n / 8 then 0 else n mod 8).
Definition shadow_cells (a : Z) (vs : list Z) : Prop :=
forall i, (i < length vs)%nat -> rd (shadow_of_addr B a + Z.of_nat i) = nth_error vs i.
Lemma range_addressable_sub : forall a len a' len',
range_addressable a len -> a <= a' -> a' + len' <= a + len -> range_addressable a' len'.
Proof. intros a len a' len' H H1 H2 x Hx. apply H. lia. Qed.
Lemma range_addressable_nil : forall a len, len <= 0 -> range_addressable a len.
Proof. intros a len H x Hx. lia. Qed.
Lemma range_addressable_app : forall a len1 len2,
0 <= len1 -> range_addressable a len1 -> range_addressable (a + len1) len2 ->
range_addressable a (len1 + len2).
Proof.
intros a len1 len2 H0 H1 H2 x Hx. destruct (Z_lt_dec x (a + len1)); [apply H1 | apply H2]; lia.
Qed.
Lemma zero_shadow_range : forall a len,
a mod 8 = 0 -> len mod 8 = 0 -> zero_shadow a len -> range_addressable a len.
Proof.
intros a len Ha Hl Hz x Hx. exists 0. split; [|left; reflexivity].
replace x with (a + (x - a)) by lia. rewrite shadow_of_addr_aligned_off by exact Ha. apply Hz.
pose proof (Z.div_mod len 8 ltac:(lia)).
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Theorem block_shadow_range : forall p n a len,
block_shadow p n -> p <= a -> a + len <= p + n -> range_addressable a len.
Proof.
intros p n a len (Hp & Hn & Hc) Hpa Hal x Hx.
pose proof (Z.div_mod n 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hmb.
pose proof (Z.div_mod (x - p) 8 ltac:(lia)) as Hxd. pose proof (Z.mod_pos_bound (x - p) 8 ltac:(lia)) as Hxm.
pose proof (Z.div_mod p 8 ltac:(lia)) as Hpd.
set (i := (x - p) / 8) in *.
assert (Hxmod : x mod 8 = (x - p) mod 8).
{ replace x with ((x - p) + (p / 8) * 8) at 1 by lia. rewrite Z.mod_add by lia. reflexivity. }
assert (Hi : 0 <= i < (n + 7) / 8).
{ split; [subst i; apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|].
pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). nia. }
exists (if i <? n / 8 then 0 else n mod 8). split.
- replace x with (p + (x - p)) by lia. rewrite shadow_of_addr_aligned_off by exact Hp. exact (Hc i Hi).
- destruct (i <? n / 8) eqn:Hlt; [left; reflexivity | right].
apply Z.ltb_ge in Hlt.
assert (Hieq : i = n / 8).
{ apply Z.le_antisymm; [|exact Hlt].
assert ((n + 7) / 8 < n / 8 + 2).
{ apply Z.div_lt_upper_bound; [lia|]. lia. }
lia. }
rewrite Hxmod. nia.
Qed.
Theorem check_passes_lb : forall a len x sz s,
range_addressable a len -> a <= x -> x + sz <= a + len -> 1 <= sz ->
rd (shadow_of_addr B x) = Some s ->
s = 0 \/ (x mod 8 + sz - 1 < s /\ 0 < s < 8).
Proof.
intros a len x sz s Hr Hlo Hhi Hsz Hs.
pose proof (Z.div_mod x 8 ltac:(lia)) as Hx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hxm.
set (e := Z.min (x + sz - 1) (8 * (x / 8) + 7)).
assert (He : a <= e < a + len) by (subst e; lia).
destruct (Hr e He) as (s' & Hs' & Hok).
rewrite (shadow_of_addr_same_granule B x e) in Hs' by (subst e; lia).
rewrite Hs in Hs'. injection Hs' as <-.
destruct Hok as [H0 | [H1 H2]]; [left; exact H0 | right].
assert (Hem : e mod 8 = e - 8 * (x / 8)).
{ rewrite (Z.mod_eq e 8) by lia. replace (e / 8) with (x / 8); [lia|].
apply Z.div_unique with (r := e - 8 * (x / 8)); subst e; lia. }
subst e. rewrite (Z.mod_eq x 8) by lia.
destruct (Z.min_spec (x + sz - 1) (8 * (x / 8) + 7)) as [[_ Hmn]|[_ Hmn]]; rewrite Hmn in *; lia.
Qed.
Theorem check_passes_whole : forall a len x sz s,
range_addressable a len -> a <= x -> x + sz <= a + len -> 8 * (x / 8) + 8 <= x + sz ->
rd (shadow_of_addr B x) = Some s -> s = 0.
Proof.
intros a len x sz s Hr Hlo Hhi Hfull Hs.
pose proof (Z.div_mod x 8 ltac:(lia)) as Hx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hxm.
set (e := 8 * (x / 8) + 7).
assert (He : a <= e < a + len) by (subst e; lia).
destruct (Hr e He) as (s' & Hs' & Hok).
rewrite (shadow_of_addr_same_granule B x e) in Hs' by (subst e; lia).
rewrite Hs in Hs'. injection Hs' as <-.
destruct Hok as [H0 | [H1 H2]]; [exact H0|].
assert (Hem : e mod 8 = 7).
{ rewrite (Z.mod_eq e 8) by lia. replace (e / 8) with (x / 8); [subst e; lia|].
apply Z.div_unique with (r := 7); subst e; lia. }
lia.
Qed.
Lemma range_addressable_present : forall a len x,
range_addressable a len -> a <= x < a + len -> exists s, rd (shadow_of_addr B x) = Some s.
Proof. intros a len x H Hx. destruct (H x Hx) as (s & Hs & _). exists s. exact Hs. Qed.
End b.
Definition rd_ext (rd rd' : Z -> option Z) : Prop :=
forall c v, rd c = Some v -> rd' c = Some v.



Lemma zero_shadow_ext : forall rd rd' B a len,
rd_ext rd rd' -> zero_shadow rd B a len -> zero_shadow rd' B a len.
Proof. intros rd rd' B a len He H i Hi. apply He, H, Hi. Qed.


Lemma range_addressable_agree : forall (rd rd' : Z -> option Z) B a len,
(forall x, a <= x < a + len -> rd' (shadow_of_addr B x) = rd (shadow_of_addr B x)) ->
range_addressable rd B a len -> range_addressable rd' B a len.
Proof.
intros rd rd' B a len Heq H x Hx. destruct (H x Hx) as (s & Hs & Hok).
exists s. rewrite (Heq x Hx). auto.
Qed.

