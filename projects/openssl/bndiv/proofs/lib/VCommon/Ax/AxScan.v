(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLin AxVal AxBytes AxMem AxZZ.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition in_keys (k0 k1 : Z) (k : Z) : bool := (k0 <=? k) && (k <=? k1).

Fixpoint iall_key {X : Type} (f : Z -> X -> bool) (t : itrie X) (acc wgt : Z) : bool :=
  match t with
  | IEmpty => true
  | ILeaf v => f acc v
  | INode l r => iall_key f l acc (2 * wgt) && iall_key f r (acc + wgt) (2 * wgt)
  end.

Lemma iall_key_iget {X : Type} (f : Z -> X -> bool) (d : nat) : forall (t : itrie X) (acc wgt : Z) (k : int) (v : X),
  iall_key f t acc wgt = true -> iget d t k = Some v -> f (acc + wgt * (to_Z k mod 2 ^ Z.of_nat d)) v = true.
Proof.
  induction d as [|d IH]; intros t acc wgt k v H Hg; destruct t as [| w | l r]; cbn [iget iall_key] in *; try discriminate.
  - injection Hg as <-. change (2 ^ Z.of_nat 0) with 1. rewrite Z.mod_1_r, Z.mul_0_r, Z.add_0_r. exact H.
  - apply andb_prop in H as [Hl Hr]. pose proof (to_Z_bounded k) as Hk. rewrite mod_pow2_succ by lia. rewrite <- phi_half.
    pose proof (Z.mod_pos_bound (to_Z k) 2 ltac:(lia)).
    destruct (iodd k) eqn:Eo; rewrite iodd_spec in Eo.
    + apply Z.eqb_eq in Eo. rewrite Eo. pose proof (IH r (acc + wgt) (2 * wgt) (k >> 1)%uint63 v Hr Hg) as Y.
      replace (acc + wgt * (2 * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d) + 1))
        with (acc + wgt + 2 * wgt * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d)) by ring. exact Y.
    + apply Z.eqb_neq in Eo. replace (to_Z k mod 2) with 0 by lia. pose proof (IH l acc (2 * wgt) (k >> 1)%uint63 v Hl Hg) as Y.
      replace (acc + wgt * (2 * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d) + 0))
        with (acc + 2 * wgt * (to_Z (k >> 1)%uint63 mod 2 ^ Z.of_nat d)) by ring. exact Y.
Qed.

Definition cell_is0 (c : cell) : bool := forallb (fun i => xb_is0 (cbyte c i)) (seq 0 8).

Lemma cell_is0_byte (c : cell) (i : nat) : cell_is0 c = true -> (i < 8)%nat -> cbyte c i = BL 0%uint63.
Proof.
  intros H Hi. unfold cell_is0 in H. rewrite forallb_forall in H. pose proof (H i ltac:(apply in_seq; lia)) as Y.
  destruct (cbyte c i) as [b| |]; cbn [xb_is0] in Y; try discriminate. apply Uint63.eqb_spec in Y. subst b. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Fixpoint fill_from (d : nat) (t : itrie cell) (k : int) (cnt : nat) (c : cell) : itrie cell :=
  match cnt with
  | O => t
  | S cnt' => fill_from d (iset d t k c) (k + 1)%uint63 cnt' c
  end.

Lemma iget_fill_from (d : nat) (c : cell) : forall (cnt : nat) (t : itrie cell) (k j : int),
  (d <= 44)%nat -> to_Z k + Z.of_nat cnt <= 2 ^ Z.of_nat d -> to_Z j < 2 ^ Z.of_nat d ->
  iget d (fill_from d t k cnt c) j =
  if (to_Z k <=? to_Z j) && (to_Z j <? to_Z k + Z.of_nat cnt) then Some c else iget d t j.
Proof.
  induction cnt as [|cnt IH]; intros t k j Hd Hk Hj; cbn [fill_from].
  - replace ((to_Z k <=? to_Z j) && (to_Z j <? to_Z k + Z.of_nat 0)) with false; [reflexivity|].
    symmetry. apply andb_false_iff. destruct (Z.leb_spec (to_Z k) (to_Z j)); [right; apply Z.ltb_ge; lia | left; reflexivity].
  - pose proof (to_Z_bounded k) as Hkb. pose proof (to_Z_bounded j) as Hjb. change wB with (2 ^ 63) in *.
    assert (Hp : 2 ^ Z.of_nat d <= 2 ^ 44) by (apply Z.pow_le_mono_r; lia).
    assert (Hk1 : to_Z (k + 1)%uint63 = to_Z k + 1).
    { rewrite add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. change wB with (2 ^ 63). lia. }
    rewrite IH by (try assumption; rewrite Hk1; lia). rewrite Hk1. rewrite iget_iset.
    rewrite (Z.mod_small (to_Z k)) by lia. rewrite (Z.mod_small (to_Z j)) by lia.
    destruct (Z.eqb_spec (to_Z k) (to_Z j)) as [E|E].
    + rewrite E. rewrite Z.leb_refl. cbn [andb].
      replace (to_Z j <? to_Z j + Z.of_nat (S cnt)) with true by (symmetry; apply Z.ltb_lt; lia).
      destruct ((to_Z j + 1 <=? to_Z j) && (to_Z j <? to_Z j + 1 + Z.of_nat cnt)); reflexivity.
    + replace ((to_Z k <=? to_Z j) && (to_Z j <? to_Z k + Z.of_nat (S cnt)))
        with ((to_Z k + 1 <=? to_Z j) && (to_Z j <? to_Z k + 1 + Z.of_nat cnt)); [reflexivity|].
      destruct (Z.leb_spec (to_Z k + 1) (to_Z j)), (Z.ltb_spec (to_Z j) (to_Z k + 1 + Z.of_nat cnt)),
               (Z.leb_spec (to_Z k) (to_Z j)), (Z.ltb_spec (to_Z j) (to_Z k + Z.of_nat (S cnt))); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma of_Z_succ (k : Z) : (of_Z k + 1)%uint63 = of_Z (k + 1).
Proof.
  apply to_Z_inj. rewrite add_spec, !of_Z_spec. change (to_Z 1%uint63) with 1. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma fill_from_fold (d : nat) (c : cell) : forall (cnt : nat) (t : itrie cell) (k0 : Z),
  fill_from d t (of_Z k0) cnt c = fold_left (fun t0 k => iset d t0 (of_Z k) c) (map (fun i => k0 + Z.of_nat i) (seq 0 cnt)) t.
Proof.
  induction cnt as [|cnt IH]; intros t k0; [reflexivity|].
  cbn [fill_from seq map fold_left]. rewrite Z.add_0_r. rewrite of_Z_succ, IH. f_equal.
  rewrite <- seq_shift, map_map. apply map_ext. intros i. lia.
Qed.

Lemma havoc_fast_eq (R : region) (k0 k1 : Z) :
  with_cells R (fill_from (rg_d R) (rg_cells R) (of_Z k0) (Z.to_nat (k1 - k0 + 1)) (CB (repeat BT 8))) = havoc_cells R k0 k1.
Proof. unfold havoc_cells, havoc_keys. rewrite fill_from_fold. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma iset_same {X : Type} (d : nat) : forall (t : itrie X) (k : int) (v : X), iget d t k = Some v -> iset d t k v = t.
Proof.
  induction d as [|d IH]; intros t k v H; destruct t as [|w|l r]; cbn [iget iset] in *; try discriminate.
  - injection H as <-. reflexivity.
  - destruct (iodd k); rewrite (IH _ _ _ H); reflexivity.
Qed.

Definition BTC : cell := CB (repeat BT 8).

Definition is_bt_cell (c : cell) : bool :=
  match c with CB [BT; BT; BT; BT; BT; BT; BT; BT] => true | _ => false end.

Lemma is_bt_cell_eq (c : cell) : is_bt_cell c = true -> c = BTC.
Proof.
  unfold is_bt_cell, BTC. destruct c as [w|l]; [discriminate|].
  repeat (destruct l as [|[| |] l]; try discriminate). intros _. reflexivity.
Qed.

(* [comment removed for export] *)
Definition iset_bt (d : nat) (t : itrie cell) (k : int) : itrie cell :=
  match iget d t k with
  | Some c => if is_bt_cell c then t else iset d t k BTC
  | None => iset d t k BTC
  end.

Lemma iset_bt_eq (d : nat) (t : itrie cell) (k : int) : iset_bt d t k = iset d t k BTC.
Proof.
  unfold iset_bt. destruct (iget d t k) as [c|] eqn:E; [|reflexivity].
  destruct (is_bt_cell c) eqn:Eb; [|reflexivity]. apply is_bt_cell_eq in Eb. subst c. symmetry. apply iset_same. exact E.
Qed.

Fixpoint fill_bt (d : nat) (t : itrie cell) (k : int) (cnt : nat) : itrie cell :=
  match cnt with
  | O => t
  | S cnt' => fill_bt d (iset_bt d t k) (k + 1)%uint63 cnt'
  end.

Lemma fill_bt_eq (d : nat) : forall (cnt : nat) (t : itrie cell) (k : int), fill_bt d t k cnt = fill_from d t k cnt BTC.
Proof. induction cnt as [|cnt IH]; intros t k; cbn [fill_bt fill_from]; [reflexivity|]. rewrite iset_bt_eq. apply IH. Qed.

Lemma havoc_bt_eq (R : region) (k0 k1 : Z) :
  with_cells R (fill_bt (rg_d R) (rg_cells R) (of_Z k0) (Z.to_nat (k1 - k0 + 1))) = havoc_cells R k0 k1.
Proof. rewrite fill_bt_eq. apply havoc_fast_eq. Qed.
