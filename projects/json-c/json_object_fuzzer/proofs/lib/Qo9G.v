(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr Ltac1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[global] Set Default Proof Mode "Classic".

Ltac2 rec ts_prune (c : constr) : constr :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.LetIn b v body =>
let body' := ts_prune body in
if Constr.Unsafe.noccurn 1 body'
then Constr.Unsafe.substnl [v] 0 body'
else Constr.Unsafe.make (Constr.Unsafe.LetIn b v body')
| Constr.Unsafe.Lambda b body => Constr.Unsafe.make (Constr.Unsafe.Lambda b (ts_prune body))
| Constr.Unsafe.Cast c0 k t => Constr.Unsafe.make (Constr.Unsafe.Cast (ts_prune c0) k t)
| Constr.Unsafe.App f args =>
let n := Array.length args in
if Int.equal n 0 then c else
let last' := ts_prune (Array.get args (Int.sub n 1)) in
let args' := Array.copy args in
Array.set args' (Int.sub n 1) last';
Constr.Unsafe.make (Constr.Unsafe.App f args')
| _ => c
end.

Ltac2 ts_strip_cast (c : constr) : constr :=
match Constr.Unsafe.kind c with Constr.Unsafe.Cast c0 _ _ => c0 | _ => c end.

Ltac2 ts_is_secvar (id : ident) : bool :=
match Env.get [id] with Some _ => true | None => false end.
Ltac2 rec ts_secvars (acc : ident list ref) (c : constr) : unit :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Var id =>
if ts_is_secvar id then
(if List.exist (Ident.equal id) (acc.(contents)) then () else acc.(contents) := id :: acc.(contents))
else ()
| _ => Constr.Unsafe.iter (ts_secvars acc) c
end.
Ltac2 ts_keep_var (id : ident) (c : constr) : constr :=
let v := Constr.Unsafe.make (Constr.Unsafe.Var id) in
Constr.Unsafe.make (Constr.Unsafe.LetIn (Constr.Binder.make None (Constr.type v)) v (Constr.Unsafe.liftn 1 1 c)).

Ltac2 term_slim2 (tac : Ltac1.t) : unit :=
Control.enter (fun () =>
let g := Control.goal () in
let c := ts_strip_cast constr:(ltac2:(Ltac1.run tac) : $g) in
let c' := ts_prune c in
let before := { contents := [] } in
let after := { contents := [] } in
ts_secvars before c; ts_secvars after c';
let lost := List.filter (fun id => Bool.neg (List.exist (Ident.equal id) (after.(contents)))) (before.(contents)) in
let c'' := List.fold_left (fun t id => ts_keep_var id t) c' lost in
exact $c'').

Ltac term_slim tac := let f := ltac2:(tac |- term_slim2 tac) in f tac.
