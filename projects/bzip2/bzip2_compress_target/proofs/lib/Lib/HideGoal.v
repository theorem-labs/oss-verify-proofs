(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require Ltac1 Control Constr Ident Int.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".

Ltac hidegoal_run tac :=
  lazymatch goal with
  | |- ?G =>
      let GH := fresh "GOALH" in
      pose (GH := G);
      change_no_check GH;
      tac;
      lazymatch goal with
      | |- ?g => let g' := eval cbv delta [GH] in g in change_no_check g'
      end;
      clear GH
  end.
Tactic Notation "hidegoal" tactic3(t) := hidegoal_run ltac:(idtac; t).

(* [comment removed for export] *)
Ltac2 Type exn ::= [ HG_res ((constr * (ident * constr option * constr) list) list) ].
Ltac2 rec hg_hyps_same (a : (ident * constr option * constr) list) (b : (ident * constr option * constr) list) : bool :=
  match a with
  | [] => match b with [] => true | _ :: _ => false end
  | (i1, _, t1) :: r1 =>
    match b with
    | [] => false
    | (i2, _, t2) :: r2 => if Ident.equal i1 i2 then if Constr.equal t1 t2 then hg_hyps_same r1 r2 else false else false
    end
  end.
Ltac2 hg_snapshot () : (constr * (ident * constr option * constr) list) list :=
  let acc := { contents := [] } in
  Control.enter (fun () => acc.(contents) := (Control.goal (), Control.hyps ()) :: acc.(contents));
  acc.(contents).
Ltac2 rec hg_same (a : (constr * (ident * constr option * constr) list) list) (b : (constr * (ident * constr option * constr) list) list) : bool :=
  match a with
  | [] => match b with [] => true | _ :: _ => false end
  | (g1, h1) :: r1 =>
    match b with
    | [] => false
    | (g2, h2) :: r2 => if Constr.equal g1 g2 then if hg_hyps_same h1 h2 then hg_same r1 r2 else false else false
    end
  end.
Ltac2 hg_dual (plain : unit -> unit) (hidden : unit -> unit) : unit :=
  Control.enter (fun () =>
    let r := Control.plus
      (fun () => Control.once plain; Control.zero (HG_res (hg_snapshot ())))
      (fun e => match e with HG_res l => Some l | _ => None end) in
    match r with
    | None => printf "HIDEGOAL-PLAINFAIL"; hidden ()
    | Some l =>
      let l2 := Control.plus (fun () => Control.once hidden; Control.zero (HG_res (hg_snapshot ())))
                             (fun e => match e with HG_res l => Some l | _ => None end) in
      match l2 with
      | Some l' => if hg_same l l' then (printf "HIDEGOAL-OK"; hidden ()) else (printf "HIDEGOAL-MISMATCH"; plain ())
      | None => printf "HIDEGOAL-HIDDENFAIL"; plain ()
      end
    end).
Ltac hidegoal_dual_l1 p h := let f := ltac2:(p h |- hg_dual (fun () => Ltac1.run p) (fun () => Ltac1.run h)) in f p h.
Tactic Notation "hidegoal_dual" tactic3(t) := hidegoal_dual_l1 ltac:(idtac; t) ltac:(idtac; hidegoal_run ltac:(idtac; t)).
Tactic Notation "hidegoal_dual" string(site) tactic3(t) := idtac "HIDEGOAL-SITE" site; hidegoal_dual_l1 ltac:(idtac; t) ltac:(idtac; hidegoal_run ltac:(idtac; t)).

(* [comment removed for export] *)
Goal forall (P Q R : Prop) (G : nat -> Prop) n, P /\ Q /\ R -> G n -> G n.
Proof. intros P Q R G n H K. hidegoal (destruct H as (A & B & C)). exact K. Qed.
Goal forall (P Q : Prop) (G : nat -> Prop) n m, P /\ n = m /\ Q -> G m -> G n.
Proof. intros P Q G n m H K. hidegoal (destruct H as (A & -> & C)). exact K. Qed.
Goal forall (P Q : Prop) (G : nat -> Prop) n, P \/ Q -> (P -> G n) -> (Q -> G n) -> G n.
Proof. intros P Q G n H K1 K2. hidegoal_dual (destruct H as [A | B]). - exact (K1 A). - exact (K2 B). Qed.
