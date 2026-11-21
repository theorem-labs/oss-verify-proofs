(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.


Inductive beh : Type :=
| BExit (code : Z)
| BOut (bs : list byte) (k : beh)
| BAlt (onfail onsucc : beh).


Inductive M (A : Type) : Type :=
| MRet (a : A)
| MOut (bs : list byte) (k : M A)
| MExit (code : Z)
| MTry (k : bool -> M A).

Arguments MRet {A} a.
Arguments MOut {A} bs k.
Arguments MExit {A} code.
Arguments MTry {A} k.

Fixpoint mbind {A B : Type} (m : M A) (f : A -> M B) : M B :=
  match m with
  | MRet a => f a
  | MOut bs k => MOut bs (mbind k f)
  | MExit c => MExit c
  | MTry k => MTry (fun b => mbind (k b) f)
  end.

Declare Scope mprog_scope.
Notation "'do' x <- m ; k" := (mbind m (fun x => k))
  (at level 200, x name, m at level 100, k at level 200, only parsing) : mprog_scope.
Notation "m ;;; k" := (mbind m (fun _ => k))
  (at level 100, right associativity, only parsing) : mprog_scope.
Local Open Scope mprog_scope.

Definition out (bs : list byte) : M unit := MOut bs (MRet tt).
Definition exit_ (code : Z) : M unit := MExit code.
Definition try_ : M bool := MTry (fun b => MRet b).

Fixpoint to_beh (m : M unit) : beh :=
  match m with
  | MRet _ => BExit 0
  | MOut bs k => BOut bs (to_beh k)
  | MExit c => BExit c
  | MTry k => BAlt (to_beh (k false)) (to_beh (k true))
  end.

Lemma mbind_ret_l : forall {A B} (a : A) (f : A -> M B), mbind (MRet a) f = f a.
Proof. reflexivity. Qed.

Lemma mbind_assoc : forall {A B C} (m : M A) (f : A -> M B) (g : B -> M C),
  (forall (h1 h2 : bool -> M C), (forall b, h1 b = h2 b) -> MTry h1 = MTry h2) ->
  mbind (mbind m f) g = mbind m (fun a => mbind (f a) g).
Proof.
  intros A B C m f g Hext. induction m as [a|bs k IH|c|k IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - apply Hext. intro b. apply IH.
Qed.


Definition blk := N.

Inductive mtree (S : Type) : Type :=
| MTDone (s : S) (r : option blk)
| MTSys (onfail onsucc : mtree S).

Arguments MTDone {S} s r.
Arguments MTSys {S} onfail onsucc.

Record MallocModel : Type := mkMallocModel {
  mm_state : Type;
  mm_init : mm_state;
  mm_malloc : mm_state -> Z -> mtree mm_state;
  mm_free : mm_state -> blk -> mm_state
}.

Section WithMalloc.
  Variable MM : MallocModel.

  Fixpoint mtree_M (t : mtree (mm_state MM)) : M (mm_state MM * option blk) :=
    match t with
    | MTDone s r => MRet (s, r)
    | MTSys f k => MTry (fun granted => if granted then mtree_M k else mtree_M f)
    end.

  Definition malloc_M (s : mm_state MM) (n : Z) : M (mm_state MM * option blk) :=
    mtree_M (mm_malloc MM s n).

  Definition free_M (s : mm_state MM) (b : option blk) : mm_state MM :=
    match b with None => s | Some b => mm_free MM s b end.
End WithMalloc.
