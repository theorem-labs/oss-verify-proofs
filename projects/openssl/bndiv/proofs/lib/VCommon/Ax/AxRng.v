(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Fixpoint all_rng {X : Type} (f : Z -> X -> bool) (d : nat) (t : itrie X) (lo hi acc w : int) : bool :=
  if (hi <=? lo)%uint63 then true else
  match t with
  | IEmpty => true
  | ILeaf v => match d with O => if (lo =? 0)%uint63 then f (to_Z acc) v else true | S _ => true end
  | INode l r => match d with
                 | O => true
                 | S d' => all_rng f d' l ((lo + 1) >> 1)%uint63 ((hi + 1) >> 1)%uint63 acc (w << 1)%uint63
                           &&& all_rng f d' r (lo >> 1)%uint63 (hi >> 1)%uint63 (acc + w)%uint63 (w << 1)%uint63
                 end
  end.

Lemma rng_odd_lt (lo hi j : Z) : 0 <= lo -> 0 <= hi -> 0 <= j -> j mod 2 = 1 -> lo <= j < hi -> lo / 2 <= j / 2 < hi / 2.
Proof.
  intros Hl Hh Hj Ho H. assert (N2 : 2 <> 0) by discriminate. assert (P2 : 0 < 2) by reflexivity.
  pose proof (Z.div_mod j 2 N2). pose proof (Z.div_mod lo 2 N2). pose proof (Z.div_mod hi 2 N2).
  pose proof (Z.mod_pos_bound lo 2 P2). pose proof (Z.mod_pos_bound hi 2 P2). lia.
Qed.

Lemma rng_even_lt (lo hi j : Z) : 0 <= lo -> 0 <= hi -> 0 <= j -> j mod 2 = 0 -> lo <= j < hi -> (lo + 1) / 2 <= j / 2 < (hi + 1) / 2.
Proof.
  intros Hl Hh Hj Ho H. assert (N2 : 2 <> 0) by discriminate. assert (P2 : 0 < 2) by reflexivity.
  pose proof (Z.div_mod j 2 N2). pose proof (Z.div_mod (lo + 1) 2 N2). pose proof (Z.div_mod (hi + 1) 2 N2).
  pose proof (Z.mod_pos_bound (lo + 1) 2 P2). pose proof (Z.mod_pos_bound (hi + 1) 2 P2). lia.
Qed.

Lemma all_rng_iget {X : Type} (f : Z -> X -> bool) : forall (d : nat) (t : itrie X) (lo hi acc w j : int) (v : X) (i : Z),
  all_rng f d t lo hi acc w = true -> 0 <= i -> i + Z.of_nat d <= 61 -> to_Z w = 2 ^ i -> to_Z acc < 2 ^ i ->
  to_Z hi < 2 ^ 62 -> to_Z j < 2 ^ Z.of_nat d -> to_Z lo <= to_Z j < to_Z hi -> iget d t j = Some v ->
  f (to_Z acc + 2 ^ i * to_Z j) v = true.
Proof.
  induction d as [|d IH]; intros t lo hi acc w j v i H Hi Hid Hw Hacc Hhi Hj Hr Hg;
    pose proof (to_Z_bounded j) as Hjb; pose proof (to_Z_bounded lo) as Hlb; pose proof (to_Z_bounded hi) as Hhb;
    pose proof (to_Z_bounded acc) as Hab; change wB with (2 ^ 63) in *;
    cbn [all_rng] in H;
    (destruct (hi <=? lo)%uint63 eqn:E1; [apply Uint63.leb_spec in E1; lia|]).
  - change (2 ^ Z.of_nat 0) with 1 in Hj. assert (Ej : to_Z j = 0) by lia.
    destruct t as [|u|l r]; cbn [iget] in Hg; try discriminate. injection Hg as ->.
    assert (El : lo = 0%uint63) by (apply to_Z_inj; change (to_Z 0%uint63) with 0; lia). subst lo. rewrite Uint63.eqb_refl in H.
    rewrite Ej, Z.mul_0_r, Z.add_0_r. exact H.
  - destruct t as [|u|l r]; cbn [iget] in Hg; try discriminate.
    apply land_true in H as [Hl Hrr].
    assert (Hp : 2 ^ (i + 1) = 2 * 2 ^ i) by (rewrite Z.pow_add_r by lia; lia).
    assert (Hpi : 0 < 2 ^ i) by (apply Z.pow_pos_nonneg; lia).
    assert (Hpi61 : 2 ^ i <= 2 ^ 61) by (apply Z.pow_le_mono_r; lia).
    assert (Hw1 : to_Z (w << 1)%uint63 = 2 ^ (i + 1)).
    { rewrite lsl_spec, Hw. change (to_Z 1%uint63) with 1. rewrite Z.pow_1_r. rewrite Z.mod_small by (change wB with (2 ^ 63); lia). lia. }
    assert (Hl1 : to_Z ((lo + 1) >> 1)%uint63 = (to_Z lo + 1) / 2).
    { rewrite lsr_spec, add_spec. change (to_Z 1%uint63) with 1. rewrite Z.mod_small by (change wB with (2 ^ 63); lia). reflexivity. }
    assert (Hh1 : to_Z ((hi + 1) >> 1)%uint63 = (to_Z hi + 1) / 2).
    { rewrite lsr_spec, add_spec. change (to_Z 1%uint63) with 1. rewrite Z.mod_small by (change wB with (2 ^ 63); lia). reflexivity. }
    assert (Hl0 : to_Z (lo >> 1)%uint63 = to_Z lo / 2) by (rewrite lsr_spec; reflexivity).
    assert (Hh0 : to_Z (hi >> 1)%uint63 = to_Z hi / 2) by (rewrite lsr_spec; reflexivity).
    assert (Hj1 : to_Z (j >> 1)%uint63 = to_Z j / 2) by (rewrite lsr_spec; reflexivity).
    assert (Hj2 : to_Z (j >> 1)%uint63 < 2 ^ Z.of_nat d).
    { rewrite Hj1. apply Z.div_lt_upper_bound; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hj by lia. lia. }
    pose proof (Z.mod_pos_bound (to_Z j) 2 ltac:(lia)) as Mj. pose proof (Z.div_mod (to_Z j) 2 ltac:(lia)) as Dj.
    destruct (iodd j) eqn:Eo; rewrite iodd_spec in Eo.
    + apply Z.eqb_eq in Eo.
      assert (Hacc1 : to_Z (acc + w)%uint63 = to_Z acc + 2 ^ i) by (rewrite add_spec, Hw; apply Z.mod_small; change wB with (2 ^ 63); lia).
      pose proof (rng_odd_lt (to_Z lo) (to_Z hi) (to_Z j) ltac:(lia) ltac:(lia) ltac:(lia) Eo Hr) as Hr'.
      pose proof (IH r (lo >> 1)%uint63 (hi >> 1)%uint63 (acc + w)%uint63 (w << 1)%uint63 (j >> 1)%uint63 v (i + 1) Hrr ltac:(lia)
                    ltac:(rewrite Nat2Z.inj_succ in Hid; lia) Hw1 ltac:(rewrite Hacc1, Hp; lia)
                    ltac:(rewrite Hh0; apply Z.div_lt_upper_bound; lia) Hj2 ltac:(rewrite Hl0, Hh0, Hj1; exact Hr') Hg) as Y.
      rewrite Hacc1, Hj1, Hp in Y. replace (to_Z acc + 2 ^ i * to_Z j) with (to_Z acc + 2 ^ i + 2 * 2 ^ i * (to_Z j / 2)) by nia. exact Y.
    + apply Z.eqb_neq in Eo. assert (Eo' : to_Z j mod 2 = 0) by lia.
      pose proof (rng_even_lt (to_Z lo) (to_Z hi) (to_Z j) ltac:(lia) ltac:(lia) ltac:(lia) Eo' Hr) as Hr'.
      pose proof (IH l ((lo + 1) >> 1)%uint63 ((hi + 1) >> 1)%uint63 acc (w << 1)%uint63 (j >> 1)%uint63 v (i + 1) Hl ltac:(lia)
                    ltac:(rewrite Nat2Z.inj_succ in Hid; lia) Hw1 ltac:(rewrite Hp; lia)
                    ltac:(rewrite Hh1; apply Z.div_lt_upper_bound; lia) Hj2 ltac:(rewrite Hl1, Hh1, Hj1; exact Hr') Hg) as Y.
      rewrite Hj1, Hp in Y. replace (to_Z acc + 2 ^ i * to_Z j) with (to_Z acc + 2 * 2 ^ i * (to_Z j / 2)) by nia. exact Y.
Qed.

(* [comment removed for export] *)
Definition rng_all {X : Type} (f : Z -> X -> bool) (d : nat) (t : itrie X) (k0 k1 : Z) : bool :=
  (0 <=? k0) &&& (k1 <? 2305843009213693952) &&& Nat.leb d 61 &&& all_rng f d t (of_Z k0) (of_Z (k1 + 1)) 0%uint63 1%uint63.

Lemma rng_all_iget {X : Type} (f : Z -> X -> bool) (d : nat) (t : itrie X) (k0 k1 : Z) (k : int) (v : X) :
  rng_all f d t k0 k1 = true -> k0 <= to_Z k <= k1 -> to_Z k < 2 ^ Z.of_nat d -> iget d t k = Some v -> f (to_Z k) v = true.
Proof.
  intros H Hk Hd Hg. unfold rng_all in H. apply land_true in H as [H Ha]. apply land_true in H as [H Hd61]. apply land_true in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Nat.leb_le in Hd61.
  assert (E0 : to_Z (of_Z k0) = k0) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
  assert (E1 : to_Z (of_Z (k1 + 1)) = k1 + 1) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
  pose proof (all_rng_iget f d t (of_Z k0) (of_Z (k1 + 1)) 0%uint63 1%uint63 k v 0 Ha ltac:(lia) ltac:(lia) eq_refl ltac:(reflexivity)
                ltac:(rewrite E1; lia) Hd ltac:(rewrite E0, E1; lia) Hg) as Y.
  change (to_Z 0%uint63) with 0 in Y. rewrite Z.pow_0_r, Z.mul_1_l, Z.add_0_l in Y. exact Y.
Qed.
