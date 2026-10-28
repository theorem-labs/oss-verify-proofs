(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.

From Ltac2 Require Ltac2.
Inductive cx_nf {A : Type} (c : A) (n : nat) : Prop := CxNf.
Module CxMemoL2.
Import Ltac2.
Ltac2 cx_ind () : inductive := match reference:(cx_nf) with Std.IndRef i => i | _ => Control.throw Not_found end.
Ltac2 cx_marker_args (t : constr) : (constr * constr) option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f a =>
     match Constr.Unsafe.kind f with
     | Constr.Unsafe.Ind i _ => if Ind.equal i (cx_ind ()) then (if Int.equal (Array.length a) 3 then Some (Array.get a 1, Array.get a 2) else None) else None
     | _ => None end
  | _ => None end.
Ltac2 rec cx_nat (n : int) (acc : constr) : constr :=
  if Int.le n 0 then acc else cx_nat (Int.sub n 1) (Constr.Unsafe.make (Constr.Unsafe.App 'S (Array.make 1 acc))).
Ltac2 cx_count () : constr :=
  let hs := Control.hyps () in
  let n := List.fold_left (fun k h => let (_, _, ty) := h in match cx_marker_args ty with Some _ => k | None => Int.add k 1 end) 0 hs in
  cx_nat n 'O.

Ltac2 cx_guard2 (c : constr) : unit :=
  let n := cx_count () in
  let hs := Control.hyps () in
  if List.exist (fun h => let (_, _, ty) := h in
                   match cx_marker_args ty with
                   | Some (c', n') => if Constr.equal c c' then Constr.equal n n' else false
                   | None => false end) hs
  then Control.zero (Tactic_failure None) else ().

Ltac2 cx_note2 (c : constr) : unit :=
  let hs := Control.hyps () in
  let old := List.map_filter (fun h => let (id, _, ty) := h in
                   match cx_marker_args ty with
                   | Some (c', _) => if Constr.equal c c' then Some id else None
                   | None => None end) hs in
  (match old with [] => () | _ :: _ => Std.clear old end);
  let n := cx_count () in
  ltac1:(c n |- let H := fresh "CXM" in pose proof (@CxNf _ c n) as H) (Ltac1.of_constr c) (Ltac1.of_constr n).
End CxMemoL2.
Ltac cx_guard := ltac2:(c |- CxMemoL2.cx_guard2 (Option.get (Ltac1.to_constr c))).
Ltac cx_note := ltac2:(c |- CxMemoL2.cx_note2 (Option.get (Ltac1.to_constr c))).

Tactic Notation "cx_memo" constr(c) tactic3(tac) := cx_guard c; first [ tac | cx_note c ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module CxPS.
Import Ltac2.
Ltac2 nhyps () : int := List.length (Control.hyps ()).
Ltac2 posed (tac : unit -> unit) : unit :=
  let n0 := nhyps () in tac (); let n1 := nhyps () in
  if Int.equal n0 n1 then Control.zero (Tactic_failure None) else ().
End CxPS.
Ltac cx_posed_something2 := ltac2:(tac |- CxPS.posed (fun () => Ltac1.run tac)).
