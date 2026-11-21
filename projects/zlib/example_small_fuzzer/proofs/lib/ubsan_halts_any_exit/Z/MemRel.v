(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition franges : Type := list (Z * Z).

Fixpoint in_franges (F : franges) (x : Z) : Prop :=
  match F with
  | [] => False
  | (lo, n) :: F' => (lo <= x < lo + n) \/ in_franges F' x
  end.

Definition disj_franges (F : franges) (a n : Z) : Prop :=
  forall x, a <= x < a + n -> ~ in_franges F x.

Definition sub_franges (F : franges) (a n : Z) : Prop :=
  forall x, a <= x < a + n -> in_franges F x.

Lemma disj_franges_nil : forall a n, disj_franges [] a n.
Proof. intros a n x _ H. exact H. Qed.

Lemma disj_franges_cons : forall lo len F a n,
  (a + n <= lo \/ lo + len <= a) -> disj_franges F a n -> disj_franges ((lo, len) :: F) a n.
Proof.
  intros lo len F a n Hd HF x Hx [H|H]; [lia|]. exact (HF x Hx H).
Qed.

Lemma sub_franges_here : forall lo len F a n,
  lo <= a -> a + n <= lo + len -> sub_franges ((lo, len) :: F) a n.
Proof. intros lo len F a n H1 H2 x Hx. left. lia. Qed.

Lemma sub_franges_later : forall r F a n,
  sub_franges F a n -> sub_franges (r :: F) a n.
Proof. intros [lo len] F a n H x Hx. right. exact (H x Hx). Qed.

Lemma in_franges_app : forall F G x, in_franges (F ++ G) x <-> in_franges F x \/ in_franges G x.
Proof.
  intros F G x. induction F as [|[lo n] F IH]; cbn; [tauto|]. rewrite IH. tauto.
Qed.

Section WithSegs.

Fixpoint layout_within (L : list (Z * nat)) (size : Z) : bool :=
  match L with
  | [] => true
  | (o, w) :: L' => (0 <=? o) && (o + Z.of_nat w <=? size) && layout_within L' size
  end.

Fixpoint layout_others_disjoint (L : list (Z * nat)) (k : nat) (o : Z) (w : nat) (j : nat) : bool :=
  match L with
  | [] => true
  | (o', w') :: L' =>
      (Nat.eqb j k || (o + Z.of_nat w <=? o') || (o' + Z.of_nat w' <=? o))
      && layout_others_disjoint L' k o w (S j)
  end.

Fixpoint list_upd {A} (l : list A) (k : nat) (v : A) : list A :=
  match l, k with
  | [], _ => []
  | _ :: t, O => v :: t
  | x :: t, S k' => x :: list_upd t k' v
  end.

End WithSegs.

Ltac cells_range_auto :=
  first [ lia
        | match goal with
          | Hb : forall j, _ -> 0 <= ?f j < _ |- 0 <= ?f _ < _ => apply Hb; lia
          end ].
