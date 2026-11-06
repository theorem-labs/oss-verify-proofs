(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Ltac2 Require Import Ltac2 Constr Control Env Ref.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".

Ltac2 gw_rw_ref (r : Std.reference) : unit :=
let c := Env.instantiate r in
ltac1:(c |- rewrite ?c) (Ltac1.of_constr c).

Ltac2 rec gw_rw_group (g : ident list) : unit :=
match g with
| [] => ()
| id :: rest =>
match Env.expand [id] with
| [] => gw_rw_group rest
| rs => List.iter (fun r => Control.plus (fun () => gw_rw_ref r) (fun _ => ())) rs
end
end.

Ltac2 gw_rw (gs : ident list list) : unit := List.iter gw_rw_group gs.

Definition gw_nohdr : unit := tt.
Ltac2 gw_mod_of (rep : constr) : ident list :=
match Constr.Unsafe.kind rep with
| Constr.Unsafe.Constant k _ => let p := Env.path (Std.ConstRef k) in List.firstn (Int.sub (List.length p) 1) p
| _ => Control.throw (Tactic_failure (Some (Message.of_string "gw_fact_ty: the module locator must be a constant of the image module")))
end.

Ltac2 gw_occurs (c : constr) (t : constr) : bool :=
let found := Ref.ref false in
let rec go (u : constr) : constr := if Constr.equal u c then (Ref.set found true; u) else Constr.Unsafe.map go u in
let _ := go t in
Ref.get found.

Ltac2 rec gw_fact_ty_go (m : ident list) (target : ident) (ty : constr) : constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
if Ident.equal id target then
let t := Constr.Binder.type b in
if gw_occurs 'gw_nohdr t then
Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "gw_fact_ty: the fact depends on a header name without a constant in the image module: ") (Message.of_ident target))))
else t
else
match Env.get (List.append m [id]) with
| Some r => gw_fact_ty_go m target (Constr.Unsafe.substnl [Env.instantiate r] 0 rest)
| None => gw_fact_ty_go m target (Constr.Unsafe.substnl ['gw_nohdr] 0 rest)
end
| None => Control.throw (Tactic_failure (Some (Message.of_string "gw_fact_ty: anonymous binder in the witness")))
end
| _ => Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "gw_fact_ty: not a header name of the witness: ") (Message.of_ident target))))
end.

Ltac2 gw_fact_ty (rep : constr) (w : constr) (target : ident) : unit :=
let t := gw_fact_ty_go (gw_mod_of rep) target (Constr.type w) in
Control.refine (fun () => t).

