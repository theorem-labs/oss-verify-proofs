(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition lsh_cy (lb x : Z) : Z := if lb =? 0 then 0 else shrw x (64 - lb).

(* [comment removed for export] *)
Definition lsh_at_g (f : list Z) (lb m0 : Z) (i : nat) : Z :=
  Z.lor (if (i <? length f)%nat then shlw (nth i f 0) lb else 0) (match i with O => m0 | S j => lsh_cy lb (nth j f 0) end).
Definition lsh_at (f : list Z) (lb : Z) (i : nat) : Z := lsh_at_g f lb 0 i.

Lemma lshift_limbs_seq_g : forall f lb m0,
  fst (lshift_limbs f lb m0) ++ [snd (lshift_limbs f lb m0)] = map (lsh_at_g f lb m0) (seq 0 (S (length f))).
Proof.
  induction f as [|x l IH]; intros lb m0.
  - cbn. reflexivity.
  - cbn [lshift_limbs]. specialize (IH lb (if lb =? 0 then 0 else shrw x (64 - lb))).
    destruct (lshift_limbs l lb (if lb =? 0 then 0 else shrw x (64 - lb))) as [r mo]. cbn [fst snd] in *.
    cbn [length]. rewrite <- cons_seq, <- seq_shift. cbn [map app]. f_equal.
    rewrite IH, map_map. apply map_ext_in. intros j Hj. apply in_seq in Hj.
    unfold lsh_at_g. cbn [length nth]. f_equal.
    destruct j as [|j']; reflexivity.
Qed.

Lemma lshift_limbs_seq : forall f lb,
  fst (lshift_limbs f lb 0) ++ [snd (lshift_limbs f lb 0)] = map (lsh_at f lb) (seq 0 (S (length f))).
Proof. intros. apply lshift_limbs_seq_g. Qed.

(* [comment removed for export] *)
Lemma lsh_cy_machine : forall lb x, 0 <= lb < 64 -> 0 <= x < 18446744073709551616 ->
  Z.land (Z.shiftr x ((64 - lb) mod 64)) (if lb =? 0 then 0 else 18446744073709551615) = lsh_cy lb x.
Proof.
  intros lb x LB Hx. unfold lsh_cy. destruct (Z.eqb_spec lb 0) as [E|NE]; [apply Z.land_0_r|].
  rewrite (Z.mod_small (64 - lb)) by lia.
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold shrw. rewrite Z.shiftr_div_pow2 by lia. apply Z.mod_small.
  assert (0 < 2 ^ (64 - lb)) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. change (2 ^ 64) with 18446744073709551616.
  assert (x / 2 ^ (64 - lb) <= x); [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma shlw_machine : forall lb x, 0 <= lb < 64 -> (Z.shiftl x (lb mod 64)) mod 18446744073709551616 = shlw x lb.
Proof. intros lb x LB. rewrite (Z.mod_small lb 64) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma lsh_cy_lit : forall lb x, 0 <= lb < 64 -> 0 <= x < 18446744073709551616 -> 0 <= lsh_cy lb x < 18446744073709551616.
Proof.
  intros lb x LB Hx. unfold lsh_cy, shrw. destruct (lb =? 0); [lia|].
  assert (0 < 2 ^ (64 - lb)) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. assert (x / 2 ^ (64 - lb) <= x); [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Lemma lsh_at_top : forall f lb, lsh_at f lb (length f) = match length f with O => 0 | S j => lsh_cy lb (nth j f 0) end.
Proof. intros f lb. unfold lsh_at, lsh_at_g. rewrite Nat.ltb_irrefl. rewrite Z.lor_0_l. reflexivity. Qed.

Lemma lsh_at_mid : forall f lb j, (S j < length f)%nat ->
  lsh_at f lb (S j) = Z.lor (lsh_cy lb (nth j f 0)) (shlw (nth (S j) f 0) lb).
Proof.
  intros f lb j H. unfold lsh_at, lsh_at_g. destruct (Nat.ltb_spec (S j) (length f)); [|lia]. apply Z.lor_comm.
Qed.

Lemma lsh_at_0 : forall f lb, (0 < length f)%nat -> lsh_at f lb 0 = shlw (nth 0 f 0) lb.
Proof. intros f lb H. unfold lsh_at, lsh_at_g. destruct (Nat.ltb_spec 0 (length f)); [|lia]. apply Z.lor_0_r. Qed.

(* [comment removed for export] *)
Definition rsh_hi (rb : Z) (l' : list Z) : Z := match l' with [] => 0 | m :: _ => if rb =? 0 then 0 else shlw m (64 - rb) end.

Lemma rshift_limbs_cons : forall n l' rb, rshift_limbs (n :: l') rb = Z.lor (shrw n rb) (rsh_hi rb l') :: rshift_limbs l' rb.
Proof. reflexivity. Qed.

Lemma rsh_hi_machine : forall rb m, 0 <= rb < 64 -> 
  Z.land ((Z.shiftl m ((64 - rb) mod 64)) mod 18446744073709551616) (if rb =? 0 then 0 else 18446744073709551615) =
  (if rb =? 0 then 0 else shlw m (64 - rb)).
Proof.
  intros rb m RB. destruct (Z.eqb_spec rb 0) as [E|NE]; [apply Z.land_0_r|].
  rewrite (Z.mod_small (64 - rb)) by lia.
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2 by lia. unfold shlw. change (2 ^ 64) with BW. apply Z.mod_mod. unfold BW. lia.
Qed.

Lemma shrw_machine : forall rb x, 0 <= rb < 64 -> Z.shiftr x (rb mod 64) = shrw x rb.
Proof. intros rb x RB. rewrite (Z.mod_small rb 64) by lia. unfold shrw. apply Z.shiftr_div_pow2. lia. Qed.

(* [comment removed for export] *)
Definition rmask_m (rb : Z) : Z := Z.lor (Z.shiftr ((0 - rb) mod 18446744073709551616) 8) ((0 - rb) mod 18446744073709551616).
Lemma rmask_chk : forallb (fun n => rmask_m ((64 - n) mod 64) =? (if n =? 0 then 0 else 18446744073709551615)) (map Z.of_nat (seq 0 64)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rmask_m_eq : forall n, 0 <= n < 64 -> rmask_m ((64 - n) mod 64) = if n =? 0 then 0 else 18446744073709551615.
Proof.
  intros n H. pose proof rmask_chk as A. rewrite forallb_forall in A. specialize (A n). rewrite Z.eqb_eq in A. apply A.
  apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Definition rsh_at (f : list Z) (rb : Z) (i : nat) : Z :=
  Z.lor (shrw (nth i f 0) rb) (if (S i <? length f)%nat then (if rb =? 0 then 0 else shlw (nth (S i) f 0) (64 - rb)) else 0).

Lemma rshift_limbs_seq : forall f rb, rshift_limbs f rb = map (rsh_at f rb) (seq 0 (length f)).
Proof.
  induction f as [|x l IH]; intros rb; [reflexivity|].
  rewrite rshift_limbs_cons. cbn [length]. rewrite <- cons_seq, <- seq_shift. cbn [map]. f_equal.
  - unfold rsh_at, rsh_hi. cbn [nth length]. destruct l as [|y l']; [reflexivity|]. cbn [length nth].
    destruct (Nat.ltb_spec 1 (S (S (length l')))); [reflexivity | lia].
  - rewrite IH, map_map. apply map_ext_in. intros j Hj. unfold rsh_at. cbn [nth length].
    replace (S (S j) <? S (length l))%nat with (S j <? length l)%nat; [reflexivity|].
    destruct (Nat.ltb_spec (S j) (length l)), (Nat.ltb_spec (S (S j)) (S (length l))); try reflexivity; lia.
Qed.

Lemma rsh_at_mid : forall f rb i, (S i < length f)%nat ->
  rsh_at f rb i = Z.lor (if rb =? 0 then 0 else shlw (nth (S i) f 0) (64 - rb)) (shrw (nth i f 0) rb).
Proof. intros f rb i H. unfold rsh_at. destruct (Nat.ltb_spec (S i) (length f)); [|lia]. apply Z.lor_comm. Qed.

Lemma rsh_at_last : forall f rb i, length f = S i -> rsh_at f rb i = shrw (nth i f 0) rb.
Proof. intros f rb i H. unfold rsh_at. destruct (Nat.ltb_spec (S i) (length f)); [lia|]. apply Z.lor_0_r. Qed.
