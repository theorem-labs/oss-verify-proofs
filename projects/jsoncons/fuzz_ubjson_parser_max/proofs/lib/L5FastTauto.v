(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Lists.List.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control List Std.
Set Default Proof Mode "Classic".
Ltac2 rec eq_disj (t : constr) : bool :=
lazy_match! t with
| ?a \/ ?b => if eq_disj a then eq_disj b else false
| @eq _ _ _ => true
| False => true
| True => true
| _ => false
end.
Ltac2 rec goal_leaves (t : constr) (acc : constr list) : constr list :=
lazy_match! t with
| ?a \/ ?b => goal_leaves a (goal_leaves b acc)
| ?a /\ ?b => goal_leaves a (goal_leaves b acc)
| ?a <-> ?b => goal_leaves a (goal_leaves b acc)
| ~ ?a => goal_leaves a acc
| ?a -> ?b => goal_leaves a (goal_leaves b acc)
| _ => t :: acc
end.
Ltac2 prune_eqdisj () : unit :=
let leaves := goal_leaves (Control.goal ()) [] in
let keepit (ty : constr) : bool := if eq_disj ty then true else List.exist (fun l => Constr.equal l ty) leaves in
let hs := List.fold_right (fun (id, _, ty) acc => if keepit ty then id :: acc else acc) (Control.hyps ()) [] in
Std.keep hs.
Ltac prune_eqdisj := ltac2:(prune_eqdisj ()).
Ltac pin_disj := solve [ repeat first [ left; reflexivity | right ]; reflexivity ].
Ltac ptauto0 := first [ pin_disj | solve [ prune_eqdisj; tauto ] ].
Ltac ptauto := first [ ptauto0 | tauto ].
Ltac ptauto_dbg := first [ ptauto0 | idtac "PTAUTO-FALLBACK"; tauto ].
Goal forall (j : nat) (P Q : Prop), P /\ Q -> (P -> Q \/ P) -> 3 = j \/ 4 = j \/ False -> 4 = j \/ 7 = j \/ 3 = j \/ False.
Proof. intros j P Q H1 H2 Hj. ptauto0. Qed.
Goal forall (b : nat) (l1 l2 : list nat) (P : Prop), P /\ P -> Stdlib.Lists.List.In b l2 -> Stdlib.Lists.List.In b l1 \/ Stdlib.Lists.List.In b l2.
Proof. intros b l1 l2 P H Hb. ptauto0. Qed.
Goal exists x : nat, 3 = 4 \/ 5 = x \/ 6 = x \/ False.
Proof. eexists. ptauto0. Qed.
Goal forall (P Q : Prop), P /\ Q -> Q.
Proof. intros P Q H. Fail ptauto0. ptauto. Qed.
