(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Ltac1 Control Constr Ident Int.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 Type exn ::= [ NoCast_goal (constr) | NoCast_fallback ].

Ltac2 nocast_hyps_same (h1 : (ident * constr option * constr) list) (h2 : (ident * constr option * constr) list) : bool :=
  let rec go a b :=
    match a with
    | [] => match b with [] => true | _ :: _ => false end
    | (i1, b1, t1) :: r1 =>
      match b with
      | [] => false
      | (i2, b2, t2) :: r2 =>
        if Ident.equal i1 i2 then
          if Constr.equal t1 t2 then
            (match b1 with
             | None => (match b2 with None => go r1 r2 | Some _ => false end)
             | Some x1 => (match b2 with None => false | Some x2 => if Constr.equal x1 x2 then go r1 r2 else false end)
             end)
          else false
        else false
      end
    end in
  go h1 h2.

Ltac2 nocast_run (tac : unit -> unit) : unit :=
  Control.enter (fun () =>       (* [comment removed for export] *)
  let h0 := Control.hyps () in
  let r := Control.plus
    (fun () =>
       Control.once tac;   (* [comment removed for export] *)
       if Int.equal (Control.numgoals ()) 1 then
         (let g := Control.goal () in
          if nocast_hyps_same h0 (Control.hyps ()) then Control.zero (NoCast_goal g) else Control.zero NoCast_fallback)
       else Control.zero NoCast_fallback)
    (fun e => match e with
              | NoCast_goal g => Some g
              | _ => None
              end) in
  match r with
  | Some g => ltac1:(g |- change_no_check g) (Ltac1.of_constr g)
  | None => tac ()
  end).

Set Default Proof Mode "Classic".
Ltac nocast_l1 t := let f := ltac2:(t |- nocast_run (fun () => Ltac1.run t)) in f t.
(* [comment removed for export] *)
Tactic Notation "nocast" tactic3(t) := nocast_l1 t.

(* [comment removed for export] *)
Goal forall n : nat, (fun x => x + 0) n = n + 0.
Proof.
  intros n. nocast (cbv beta). nocast (idtac). nocast (unfold Nat.add). nocast (fold Nat.add). nocast (cbn). nocast (simpl).
  lazymatch goal with |- n + 0 = n + 0 => idtac end. reflexivity.
Qed.
Goal forall n : nat, (fun x => x) n = n -> (fun x => x + 0) n = n + 0.
Proof. intros n H. nocast (cbv beta in * ). lazymatch type of H with n = n => idtac end. reflexivity. Qed.
Goal True /\ True.
Proof. nocast (split). all: exact I. Qed.
Goal True.
Proof. Fail nocast (fail). nocast (exact I). Qed.
Goal forall n : nat, (fun x => x + 0) n = n + 0 /\ (fun x => x) n = n.
Proof. intros n. split; nocast (cbv beta); reflexivity. Qed.
Ltac nocast_selftest_red x := lazymatch goal with |- _ => cbv beta end.
Goal forall n : nat, (fun x => x + 0) n = n + 0.
Proof.
  intros n. nocast (idtac; nocast_selftest_red n).
  lazymatch goal with |- n + 0 = n + 0 => idtac end. reflexivity.
Qed.
