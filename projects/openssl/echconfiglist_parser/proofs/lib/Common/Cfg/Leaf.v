(* SPDX-License-Identifier: MIT *)
(* Leaves of a walk.  [SpinAlg.srealizes] and [ShapeCfg.realizes_cfg] have a fourth constructor,
   a leaf: a fact [lf segs c T] of the class [Leaf] in scope, which the walk does not prove.  The
   default class [leaf_none] has no leaf ([False]), so a walk at [leaf_none] is a whole walk.  A
   walk over a binary's own segments whose continuations are stated over a larger segment list
   ends in leaves that [LeafLift] lifts to that list.  Every theorem that reads traces off a walk
   asks [NoLeaf] of its class. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
Import ListNotations.

Class Leaf := {
  lf : list Segment -> config -> (list event -> Prop) -> Prop ;
  lf_ne : forall s c T, lf s c T -> T []
}.

#[global] Instance leaf_none : Leaf :=
  {| lf := fun _ _ _ => False ; lf_ne := fun _ _ _ H => False_ind _ H |}.

Class NoLeaf (LF : Leaf) : Prop := no_leaf : forall s c T, ~ @lf LF s c T.

#[global] Instance noleaf_none : NoLeaf leaf_none := fun _ _ _ H => H.

(** a leaf of a class without leaves *)
Lemma leaf_absurd {LF : Leaf} {NL : NoLeaf LF} : forall s c T, @lf LF s c T -> False.
Proof. intros s c T H. exact (@no_leaf LF NL s c T H). Qed.
