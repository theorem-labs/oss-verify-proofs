(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac RBSafe RBOrder.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition ascii_lower (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.

(* [comment removed for export] *)
Lemma ascii_lower_machine c :
  0 <= c < 256 →
  ascii_lower c = c + Z.shiftl (if (c - 65) mod 2^64 <? 26 then 1 else 0) 5.
Proof.
  intros Hc. unfold ascii_lower.
  assert (S1 : Z.shiftl 1 5 = 32) by reflexivity. assert (S0 : Z.shiftl 0 5 = 0) by reflexivity.
  destruct (Z.leb_spec 65 c); destruct (Z.leb_spec c 90); cbn [andb].
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec (c - 65) 26); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec (c - 65) 26); lia.
  - replace ((c - 65) mod 2 ^ 64) with (c - 65 + 2^64).
    + destruct (Z.ltb_spec (c - 65 + 2^64) 26); lia.
    + symmetry. rewrite <-(Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia.
  - lia.
Qed.

(* [comment removed for export] *)
Fixpoint ilex (a b : list Z) : bool :=
  match b with
  | [] => false
  | y :: b' =>
      match a with
      | [] => true
      | x :: a' =>
          if ascii_lower x <? ascii_lower y then true
          else if ascii_lower y <? ascii_lower x then false
          else ilex a' b'
      end
  end.

(* [comment removed for export] *)
Definition key_lt (a b : list Z) : bool :=
  if (Z.of_nat (length a) <? Z.of_nat (length b)) then true
  else if (Z.of_nat (length b) <? Z.of_nat (length a)) then false
  else ilex a b.

(* [comment removed for export] *)
Fixpoint ieq_bytes (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (ascii_lower x =? ascii_lower y) && ieq_bytes a' b'
  | _, _ => false
  end.
Definition ieq (a b : list Z) : bool :=
  (Z.of_nat (length a) =? Z.of_nat (length b)) && ieq_bytes a b.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ilex_asym a b : ilex a b = true → ilex b a = false.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; cbn; try done.
  destruct (Z.ltb_spec (ascii_lower x) (ascii_lower y));
  destruct (Z.ltb_spec (ascii_lower y) (ascii_lower x)); try lia; auto.
Qed.

Lemma ilex_neg_trans a b c : ilex a b = false → ilex b c = false → ilex a c = false.
Proof.
  revert b c; induction a as [|x a IH]; intros [|y b] [|z c]; cbn; try done.
  destruct (Z.ltb_spec (ascii_lower x) (ascii_lower y));
  destruct (Z.ltb_spec (ascii_lower y) (ascii_lower x));
  destruct (Z.ltb_spec (ascii_lower y) (ascii_lower z));
  destruct (Z.ltb_spec (ascii_lower z) (ascii_lower y));
  destruct (Z.ltb_spec (ascii_lower x) (ascii_lower z));
  destruct (Z.ltb_spec (ascii_lower z) (ascii_lower x)); try lia; try done.
  apply IH.
Qed.

Lemma ilex_SWO : StrictWeakOrder ilex.
Proof. split; [apply ilex_asym|apply ilex_neg_trans]. Qed.

Lemma key_lt_SWO : StrictWeakOrder key_lt.
Proof.
  split.
  - intros a b. unfold key_lt.
    destruct (Z.ltb_spec (Z.of_nat (length a)) (Z.of_nat (length b)));
    destruct (Z.ltb_spec (Z.of_nat (length b)) (Z.of_nat (length a))); try lia; try done.
    apply ilex_asym.
  - intros a b c. unfold key_lt.
    destruct (Z.ltb_spec (Z.of_nat (length a)) (Z.of_nat (length b)));
    destruct (Z.ltb_spec (Z.of_nat (length b)) (Z.of_nat (length a)));
    destruct (Z.ltb_spec (Z.of_nat (length b)) (Z.of_nat (length c)));
    destruct (Z.ltb_spec (Z.of_nat (length c)) (Z.of_nat (length b)));
    destruct (Z.ltb_spec (Z.of_nat (length a)) (Z.of_nat (length c)));
    destruct (Z.ltb_spec (Z.of_nat (length c)) (Z.of_nat (length a))); try lia; try done.
    apply ilex_neg_trans.
Qed.

(* [comment removed for export] *)
Lemma ilex_eqv_bytes a b :
  length a = length b → (negb (ilex a b) && negb (ilex b a)) = ieq_bytes a b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b] Hl; cbn in *; try done.
  destruct (Z.ltb_spec (ascii_lower x) (ascii_lower y));
  destruct (Z.ltb_spec (ascii_lower y) (ascii_lower x));
  destruct (Z.eqb_spec (ascii_lower x) (ascii_lower y)); cbn; try lia.
  apply IH. lia.
Qed.

(* [comment removed for export] *)
Theorem key_eqv_ieq a b : eqv key_lt a b = ieq a b.
Proof.
  unfold eqv, key_lt, ieq.
  destruct (Z.ltb_spec (Z.of_nat (length a)) (Z.of_nat (length b)));
  destruct (Z.ltb_spec (Z.of_nat (length b)) (Z.of_nat (length a)));
  destruct (Z.eqb_spec (Z.of_nat (length a)) (Z.of_nat (length b))); cbn; try lia.
  apply ilex_eqv_bytes. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ieq_bytes_refl a : ieq_bytes a a = true.
Proof. induction a; cbn; [done|]. by rewrite Z.eqb_refl. Qed.

Lemma ieq_refl a : ieq a a = true.
Proof. unfold ieq. by rewrite Z.eqb_refl, ieq_bytes_refl. Qed.

Lemma ieq_sym a b : ieq a b = ieq b a.
Proof. rewrite <-!key_eqv_ieq. apply (eqv_sym key_lt). Qed.

Lemma ieq_bytes_length a b : ieq_bytes a b = true → length a = length b.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; cbn; try done.
  rewrite andb_true_iff. intros [_ H]. by rewrite (IH b H).
Qed.

Lemma ieq_bytes_app a1 a2 b1 b2 :
  length a1 = length b1 → ieq_bytes (a1 ++ a2) (b1 ++ b2) = ieq_bytes a1 b1 && ieq_bytes a2 b2.
Proof.
  revert b1; induction a1 as [|x a1 IH]; intros [|y b1] Hl; cbn in *; try done.
  rewrite IH by lia. by rewrite andb_assoc.
Qed.

(* [comment removed for export] *)
Lemma ieq_bytes_skip p a2 b2 : ieq_bytes (p ++ a2) (p ++ b2) = ieq_bytes a2 b2.
Proof. rewrite ieq_bytes_app by done. by rewrite ieq_bytes_refl. Qed.

(* [comment removed for export] *)
Lemma ieq_bytes_lookup a b :
  ieq_bytes a b = true ↔
  length a = length b ∧ ∀ i x y, a !! i = Some x → b !! i = Some y → ascii_lower x = ascii_lower y.
Proof.
  revert b; induction a as [|x a IH]; intros [|y b]; cbn.
  - split; [intros _; split; [done|intros i x y Hx; done]|done].
  - split; [done|intros [H _]; done].
  - split; [done|intros [H _]; done].
  - rewrite andb_true_iff, IH. split.
    + intros [Hxy%Z.eqb_eq [Hl Hi]]. split; [by rewrite Hl|].
      intros [|i] x' y' Hx Hy; cbn in *; [congruence|by eapply Hi].
    + intros [Hl Hi]. repeat split.
      * apply Z.eqb_eq. by apply (Hi O).
      * lia.
      * intros i x' y' Hx Hy. by apply (Hi (S i)).
Qed.

(* [comment removed for export] *)
Lemma ascii_lower_range c : 0 <= c < 256 → 0 <= ascii_lower c < 256.
Proof.
  unfold ascii_lower. destruct (Z.leb_spec 65 c), (Z.leb_spec c 90); cbn; lia.
Qed.
