(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Ltac2 Require Import Ltac2 Constr Control Env.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".

Ltac2 gw_rw_in_ref (h : ident) (r : Std.reference) : unit :=
let c := Env.instantiate r in
ltac1:(c h |- rewrite ?c in h) (Ltac1.of_constr c) (Ltac1.of_ident h).

Ltac2 rec gw_rw_in_group (h : ident) (g : ident list) : unit :=
match g with
| [] => ()
| id :: rest =>
match Env.expand [id] with
| [] => gw_rw_in_group h rest
| rs => List.iter (fun r => Control.plus (fun () => gw_rw_in_ref h r) (fun _ => ())) rs
end
end.

Ltac2 gw_rw_in (h : ident) (gs : ident list list) : unit := List.iter (gw_rw_in_group h) gs.
