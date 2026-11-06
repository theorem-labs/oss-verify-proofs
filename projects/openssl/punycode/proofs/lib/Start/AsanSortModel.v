(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module HSM.

(* [comment removed for export] *)
Definition rec := (Z * Z)%type.
Definition key (e : rec) : Z := let k := fst e mod 2 ^ 32 in if k <? 2 ^ 31 then k else k + (2 ^ 64 - 2 ^ 32).
Definition dflt : rec := (0, 0).
Definition get (a : list rec) (i : Z) : rec := nth (Z.to_nat i) a dflt.
Fixpoint upd (a : list rec) (i : nat) (v : rec) : list rec :=
  match a, i with
  | [], _ => []
  | _ :: r, O => v :: r
  | x :: r, S i' => x :: upd r i' v
  end.
Definition swap (a : list rec) (i j : Z) : list rec :=
  let x := get a i in let y := get a j in upd (upd a (Z.to_nat i) y) (Z.to_nat j) x.

(* [comment removed for export] *)
Fixpoint sift_up (fuel : nat) (a : list rec) (j k : Z) : list rec :=
  match fuel with
  | O => a
  | S f => let p := (j - 1) / 2 in
           if key (get a p) >=? k then a
           else let a' := swap a p j in if 1 <? j - 1 then sift_up f a' p k else a'
  end.

(* [comment removed for export] *)
Fixpoint build (cnt : nat) (a : list rec) (i : Z) : list rec :=
  match cnt with
  | O => a
  | S c => build c (sift_up (Z.to_nat i + 1) a i (key (get a i))) (i + 1)
  end.

(* [comment removed for export] *)
Fixpoint sift_down (fuel : nat) (a : list rec) (cur size : Z) : list rec :=
  match fuel with
  | O => a
  | S f => let l := 2 * cur + 1 in let r := 2 * cur + 2 in
           let b1 := if (l <? size) && (key (get a cur) <? key (get a l)) then l else cur in
           let b := if (r <? size) && (key (get a b1) <? key (get a r)) then r else b1 in
           if b =? cur then a else sift_down f (swap a b cur) b size
  end.

(* [comment removed for export] *)
Fixpoint drain (cnt : nat) (a : list rec) (last : Z) : list rec :=
  match cnt with
  | O => a
  | S c => drain c (sift_down (Z.to_nat last + 1) (swap a 0 last) 0 last) (last - 1)
  end.

(* [comment removed for export] *)
Definition hsort (es : list rec) : list rec :=
  let n := Z.of_nat (length es) in
  if n <? 2 then es else drain (Z.to_nat (n - 1)) (build (Z.to_nat (n - 1)) es 1) (n - 1).

Lemma upd_length : forall a i v, length (upd a i v) = length a.
Proof. induction a as [|x r IH]; intros i v; [reflexivity|]. destruct i; cbn [upd length]; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma swap_length : forall a i j, length (swap a i j) = length a.
Proof. intros. unfold swap. rewrite !upd_length. reflexivity. Qed.
Lemma sift_up_length : forall f a j k, length (sift_up f a j k) = length a.
Proof.
  induction f as [|f IH]; intros a j k; cbn [sift_up]; [reflexivity|]. destruct (key (get a ((j - 1) / 2)) >=? k); [reflexivity|].
  destruct (1 <? j - 1); [rewrite IH|]; apply swap_length.
Qed.
Lemma build_length : forall c a i, length (build c a i) = length a.
Proof. induction c as [|c IH]; intros a i; cbn [build]; [reflexivity|]. rewrite IH. apply sift_up_length. Qed.
Lemma sift_down_length : forall f a cur size, length (sift_down f a cur size) = length a.
Proof.
  induction f as [|f IH]; intros a cur size; cbn [sift_down]; [reflexivity|]. cbv zeta.
  match goal with |- length (if ?c then _ else _) = _ => destruct c end; [reflexivity|]. rewrite IH. apply swap_length.
Qed.
Lemma drain_length : forall c a last, length (drain c a last) = length a.
Proof. induction c as [|c IH]; intros a last; cbn [drain]; [reflexivity|]. rewrite IH, sift_down_length. apply swap_length. Qed.
Lemma hsort_length : forall es, length (hsort es) = length es.
Proof. intros es. unfold hsort. destruct (Z.of_nat (length es) <? 2); [reflexivity|]. rewrite drain_length. apply build_length. Qed.

End HSM.
