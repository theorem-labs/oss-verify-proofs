(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Counts.
Context {ptr : Type}.

Definition cntr (lo hi : Z) (X : list (ptr * Z)) : Z :=
  Z.of_nat (length (filter (fun xb => (lo <=? snd xb) && (snd xb <=? hi)) X)).
Definition C31 (X : list (ptr * Z)) : Z := cntr 5437 8172 X.
Definition C40 (X : list (ptr * Z)) : Z := cntr 32749 37436 X.
Definition C44 (X : list (ptr * Z)) : Z := cntr 65517 74876 X.

Definition FPRE (X : list (ptr * Z)) (k n : Z) : Prop :=
  0 <= k <= 98
  /\ (5437 <= n <= 8172 -> C31 X <= 7)
  /\ (32749 <= n <= 37436 -> C40 X <= 55)
  /\ (36845 <= n <= 37436 -> C40 X <= 5)
  /\ (65517 <= n <= 74876 -> C44 X <= 55)
  /\ (73709 <= n <= 74876 -> C44 X <= 5).

Definition KREQ (n : Z) : Prop := n = 5968 \/ n = 65536 \/ n = 7176 \/ n = 32768.

Lemma cntr_nil lo hi : cntr lo hi [] = 0.
Proof. reflexivity. Qed.
Lemma cntr_cons lo hi p n X : cntr lo hi ((p, n) :: X) = (if (lo <=? n) && (n <=? hi) then 1 else 0) + cntr lo hi X.
Proof. unfold cntr. cbn [filter snd]. destruct (_ && _); cbn [length]; lia. Qed.
Lemma cntr_cons_le lo hi p n X : cntr lo hi ((p, n) :: X) <= 1 + cntr lo hi X.
Proof. rewrite cntr_cons. destruct (_ && _); lia. Qed.
Lemma cntr_cons_out lo hi p n X : n < lo \/ hi < n -> cntr lo hi ((p, n) :: X) = cntr lo hi X.
Proof.
  intros H. rewrite cntr_cons. destruct (Z.leb_spec lo n); destruct (Z.leb_spec n hi); cbn [andb]; lia.
Qed.
Lemma cntr_app lo hi X Y : cntr lo hi (X ++ Y) = cntr lo hi X + cntr lo hi Y.
Proof. unfold cntr. rewrite filter_app, length_app. lia. Qed.
End Counts.

Lemma cntr_map {A B} (g : A * Z -> B * Z) lo hi (X : list (A * Z)) : (forall x, snd (g x) = snd x) -> cntr lo hi (map g X) = cntr lo hi X.
Proof.
  intros Hg. unfold cntr. induction X as [|x X IH]; [reflexivity|]. cbn [map filter]. rewrite Hg. destruct (_ && _); cbn [length]; lia.
Qed.
Lemma FPRE_map {A B} (g : A * Z -> B * Z) (X : list (A * Z)) k n : (forall x, snd (g x) = snd x) -> FPRE (map g X) k n <-> FPRE X k n.
Proof. intros Hg. unfold FPRE, C31, C40, C44. rewrite !(cntr_map g) by exact Hg. tauto. Qed.
