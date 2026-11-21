(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Btauto.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

Definition POLY : Z := 3988292384.

Definition xt (c : Z) : Z := Z.lxor (Z.shiftr c 1) (if Z.odd c then POLY else 0).

Fixpoint xtn (n : nat) (c : Z) : Z :=
  match n with O => c | S k => xtn k (xt c) end.

Lemma lxor_bound32 : forall a b,
  0 <= a < 4294967296 -> 0 <= b < 4294967296 -> 0 <= Z.lxor a b < 4294967296.
Proof.
  intros a b Ha Hb.
  assert (Hn : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [exact Hn|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|Hz]; [rewrite E; lia|].
  replace 4294967296 with (2 ^ 32) by reflexivity.
  apply (proj2 (Z.log2_lt_pow2 (Z.lxor a b) 32 ltac:(lia))).
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [E|Ha0]; [rewrite E; cbn; lia|].
    apply (proj1 (Z.log2_lt_pow2 a 32 ltac:(lia))). cbn. lia.
  - destruct (Z.eq_dec b 0) as [E|Hb0]; [rewrite E; cbn; lia|].
    apply (proj1 (Z.log2_lt_pow2 b 32 ltac:(lia))). cbn. lia.
Qed.

Lemma xt_range : forall c, 0 <= c < 4294967296 -> 0 <= xt c < 4294967296.
Proof.
  intros c Hc. unfold xt.
  assert (H1 : 0 <= Z.shiftr c 1 < 4294967296).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with c; [apply Z.div_le_upper_bound; lia | lia]. }
  destruct (Z.odd c).
  - apply lxor_bound32; [exact H1 | unfold POLY; lia].
  - rewrite Z.lxor_0_r. exact H1.
Qed.

Lemma xtn_range : forall n c, 0 <= c < 4294967296 -> 0 <= xtn n c < 4294967296.
Proof.
  induction n as [|n IH]; intros c Hc; cbn; [exact Hc | apply IH, xt_range, Hc].
Qed.

Definition byteZ (c : Z) (k : nat) : Z :=
  Z.land (Z.shiftr c (8 * Z.of_nat k)) 255.

Definition crc_tab (n : Z) : Z := xtn 8 n.

Definition crc_step (c b : Z) : Z := xtn 8 (Z.lxor c b).

Definition crc_fold (c : Z) (bs : list Z) : Z := fold_left crc_step bs c.

Definition MASK32 : Z := 4294967295.
Definition crc32_model (init : Z) (bs : list Z) : Z :=
  Z.lxor (crc_fold (Z.lxor init MASK32) bs) MASK32.

Lemma crc_fold_cons : forall c b bs, crc_fold c (b :: bs) = crc_fold (crc_step c b) bs.
Proof. reflexivity. Qed.

Lemma crc_fold_range : forall bs c, 0 <= c < 4294967296 ->
  (forall b, In b bs -> 0 <= b < 256) -> 0 <= crc_fold c bs < 4294967296.
Proof.
  induction bs as [|b bs IH]; intros c Hc Hb; [exact Hc|].
  rewrite crc_fold_cons. apply IH.
  - unfold crc_step. apply xtn_range. apply lxor_bound32; [exact Hc|].
    assert (Hb0 : 0 <= b < 256) by (apply Hb; left; reflexivity). lia.
  - intros x Hx. apply Hb. right. exact Hx.
Qed.

Definition wordLE (b0 b1 b2 b3 : Z) : Z :=
  Z.lxor b0 (Z.lxor (Z.shiftl b1 8) (Z.lxor (Z.shiftl b2 16) (Z.shiftl b3 24))).

Definition braid_tab (k : nat) (i : Z) : Z := xtn ((23 - k) * 8) (Z.shiftl i 24).

Definition braid_round4 (b0 b1 b2 b3 : Z) : Z :=
  Z.lxor (braid_tab 0 b0)
    (Z.lxor (braid_tab 1 b1) (Z.lxor (braid_tab 2 b2) (braid_tab 3 b3))).

Definition absorb4 (c w : Z) : Z := xtn 32 (Z.lxor c w).

Lemma testbit_high : forall v n m, 0 <= v < 2 ^ n -> 0 <= n <= m ->
  Z.testbit v m = false.
Proof.
  intros v n m Hv Hm.
  destruct (Z.eq_dec v 0) as [E|Hv0]; [rewrite E; apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 v < n) by (apply (proj1 (Z.log2_lt_pow2 v n ltac:(lia))); lia).
  lia.
Qed.

Lemma land_shiftl_disj : forall x y k, 0 <= x < 2 ^ k -> 0 <= k -> 0 <= y ->
  Z.land x (Z.shiftl y k) = 0.
Proof.
  intros x y k Hx Hk Hy. apply Z.bits_inj'. intros m Hm.
  rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec m k) as [Hlt|Hge].
  - rewrite (Z.testbit_neg_r y (m - k)) by lia. apply Bool.andb_false_r.
  - rewrite (testbit_high x k m Hx) by lia. reflexivity.
Qed.

Definition ABASE : Z := 65521.
Definition NMAX : Z := 5552.

Fixpoint adl (bs : list Z) (s1 s2 : Z) : Z * Z :=
  match bs with
  | [] => (s1, s2)
  | b :: r => let s1' := (s1 + b) mod ABASE in
              adl r s1' ((s2 + s1') mod ABASE)
  end.

Fixpoint adl_raw (bs : list Z) (s1 s2 : Z) : Z * Z :=
  match bs with
  | [] => (s1, s2)
  | b :: r => let s1' := s1 + b in adl_raw r s1' (s2 + s1')
  end.

Definition adler32_model (init : Z) (bs : list Z) : Z :=
  let s1 := Z.land init 65535 in
  let s2 := Z.land (Z.shiftr init 16) 65535 in
  let (a, b) := adl bs (s1 mod ABASE) (s2 mod ABASE) in
  Z.lxor (Z.shiftl b 16) a.

Lemma adl_raw_mod : forall bs s1 s2,
  adl bs (s1 mod ABASE) (s2 mod ABASE)
  = (fst (adl_raw bs s1 s2) mod ABASE, snd (adl_raw bs s1 s2) mod ABASE).
Proof.
  induction bs as [|b bs IH]; intros s1 s2; cbn [adl adl_raw fst snd].
  - reflexivity.
  - replace ((s1 mod ABASE + b) mod ABASE) with ((s1 + b) mod ABASE)
      by (rewrite Zplus_mod_idemp_l; reflexivity).
    replace ((s2 mod ABASE + (s1 + b) mod ABASE) mod ABASE)
      with ((s2 + (s1 + b)) mod ABASE)
      by (rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r; reflexivity).
    apply IH.
Qed.

Lemma adl_canon : forall bs s1 s2,
  0 <= s1 < ABASE -> 0 <= s2 < ABASE ->
  0 <= fst (adl bs s1 s2) < ABASE /\ 0 <= snd (adl bs s1 s2) < ABASE.
Proof.
  induction bs as [|b bs IH]; intros s1 s2 H1 H2; cbn [adl fst snd].
  - split; assumption.
  - apply IH; apply Z.mod_pos_bound; unfold ABASE; lia.
Qed.

Definition AMAGIC : Z := 983265 * 4294967296 + 221234637.

Definition mulhu (x y : Z) : Z := (x * y) / 18446744073709551616.

Definition mdiv (x : Z) : Z :=
  let q := mulhu x AMAGIC in
  Z.shiftr (q + Z.shiftr (x - q) 1) 15.

Definition mrem (x : Z) : Z := x - ABASE * mdiv x.

Definition mdiv_correct_S : Prop :=
  forall x, 0 <= x < 1099511627776 -> mdiv x = x / ABASE.

Definition mrem_correct_S : Prop :=
  forall x, 0 <= x < 1099511627776 -> mrem x = x mod ABASE.

Definition CHECK_BYTES : list Z := [49;50;51;52;53;54;55;56;57].

