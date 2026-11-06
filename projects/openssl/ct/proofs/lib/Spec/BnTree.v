(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnKara BnModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive btree (ptr : Type) (A : Type) : Type :=
| TRet (a : A)
| TUnr
| TMalloc (n : Z) (k : option ptr -> btree ptr A)
| TFree (p : ptr) (k : btree ptr A).
Arguments TRet {ptr A} a.
Arguments TUnr {ptr A}.
Arguments TMalloc {ptr A} n k.
Arguments TFree {ptr A} p k.

Fixpoint tbind {ptr A B} (m : btree ptr A) (f : A -> btree ptr B) : btree ptr B :=
  match m with
  | TRet a => f a
  | TUnr => TUnr
  | TMalloc n k => TMalloc n (fun r => tbind (k r) f)
  | TFree p k => TFree p (tbind k f)
  end.

Definition tree_ops (ptr : Type) : bn_ops (btree ptr) ptr :=
  mkBnOps (fun A (a : A) => TRet a)
          (fun A B m f => tbind m f)
          (fun A => TUnr)
          (fun n => TMalloc n (fun r => TRet r))
          (fun p => TFree p (TRet tt)).

(* [comment removed for export] *)
Definition bn_one {ptr} (ls : lstate ptr) (d : list Z) : btree ptr (lstate ptr * Z) :=
  tbind (fuzz_one (tree_ops ptr) d ls) (fun p => TRet (snd p, fst p)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive bevent : Type := EvMalloc (n : Z) (p : nat) | EvFree (p : nat).

Fixpoint run_tree {A} (t : btree nat A) (next : nat) (acc : list bevent) : list bevent * nat * option A :=
  match t with
  | TRet a => (rev acc, next, Some a)
  | TUnr => (rev acc, next, None)
  | TMalloc n k => run_tree (k (Some next)) (S next) (EvMalloc n next :: acc)
  | TFree p k => run_tree k next (EvFree p :: acc)
  end.

(* [comment removed for export] *)
Fixpoint run_calls (payloads : list (list Z)) (ls : lstate nat) (next : nat)
  : list (list bevent) * option (lstate nat) :=
  match payloads with
  | [] => ([], Some ls)
  | d :: rest =>
      match run_tree (bn_one ls d) next [] with
      | (evs, next', Some (ls', _)) => let '(e, r) := run_calls rest ls' next' in (evs :: e, r)
      | (evs, _, None) => ([evs], None)
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import Permutation.

Definition BSZ : Z := 524288.
Definition NBLK : nat := 11.

Section WP.
Context {ptr : Type}.

(* [comment removed for export] *)
Definition blocks := list (ptr * Z).

(* [comment removed for export] *)
Definition ok_bn (X : blocks) (n : Z) : Prop :=
  (length X < NBLK)%nat /\ 0 <= n <= BSZ /\ Forall (fun xb => 0 <= snd xb <= BSZ) X.

(* [comment removed for export] *)
Fixpoint wp {A} (t : btree ptr A) (X : blocks) (Q : A -> blocks -> Prop) : Prop :=
  match t with
  | TRet a => Q a X
  | TUnr => False
  | TMalloc n k => ok_bn X n /\ k None = TUnr /\ forall p, ~ In p (map fst X) -> wp (k (Some p)) ((p, n) :: X) Q
  | TFree p k => exists m X', Permutation X ((p, m) :: X') /\ wp k X' Q
  end.

Lemma wp_mono : forall {A} (t : btree ptr A) X (Q Q' : A -> blocks -> Prop),
  wp t X Q -> (forall a X', Q a X' -> Q' a X') -> wp t X Q'.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q Q' H HQ; cbn [wp] in *.
  - apply HQ. exact H.
  - exact H.
  - destruct H as (Hn & Hk & H). split; [exact Hn|]. split; [exact Hk|]. intros q Hq. eapply IH; [apply H; exact Hq|exact HQ].
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. eapply IH; [exact H|exact HQ].
Qed.

Lemma wp_bind : forall {A B} (m : btree ptr A) (f : A -> btree ptr B) X Q,
  wp m X (fun a X' => wp (f a) X' Q) -> wp (tbind m f) X Q.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH]; intros f X Q H; cbn [wp tbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & Hk & H). split; [exact Hn|]. split; [rewrite Hk; reflexivity|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Fixpoint leaves {A} (t : btree ptr A) (phi : A -> Prop) : Prop :=
  match t with
  | TRet a => phi a
  | TUnr => True
  | TMalloc n k => forall r, leaves (k r) phi
  | TFree p k => leaves k phi
  end.

Lemma leaves_bind : forall {A B} (m : btree ptr A) (f : A -> btree ptr B) (phi : B -> Prop),
  (forall a, leaves (f a) phi) -> leaves (tbind m f) phi.
Proof.
  intros A B m f phi H. induction m as [a| |n k IH|p k IH]; cbn [leaves tbind]; auto.
Qed.

Lemma leaves_bind' : forall {A B} (m : btree ptr A) (f : A -> btree ptr B) (phi : B -> Prop),
  leaves m (fun a => leaves (f a) phi) -> leaves (tbind m f) phi.
Proof.
  intros A B m f phi. induction m as [a| |n k IH|p k IH]; cbn [leaves tbind]; auto.
Qed.

End WP.
