(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Ltac2 Require Ltac2.

Module LDce2.
Import Ltac2.
Ltac2 is_secvar (id : ident) : bool := match Env.get [id] with Some _ => true | None => false end.

Ltac2 rec split_at (n : int) (l : ident list) : ident list * ident list :=
if Int.equal n 0 then ([], l) else
match l with [] => ([], []) | x :: l' => let (a, b) := split_at (Int.sub n 1) l' in (x :: a, b) end.
Ltac2 rec occ_set (c : constr) (lo : int) (ids : ident list) (n : int) : ident list :=
if Int.equal n 0 then [] else
if Constr.Unsafe.noccur_between lo n c then [] else
if Int.equal n 1 then ids else
let h := Int.div n 2 in
let (l1, l2) := split_at h ids in
List.append (occ_set c lo l1 h) (occ_set c (Int.add lo h) l2 (Int.sub n h)).
Ltac2 secvars (c : constr) : ident list :=
let ids := List.map_filter (fun (h : ident * constr option * constr) => let (id, _, _) := h in if is_secvar id then Some id else None) (Control.hyps ()) in
match ids with
| [] => []
| _ :: _ => occ_set (Constr.Unsafe.closenl ids 1 c) 1 ids (List.length ids)
end.

Ltac2 rec dce (t : constr) : constr * bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.LetIn b v body =>
let (body', ch) := dce body in
if Constr.Unsafe.noccurn 1 body' then (Constr.Unsafe.substnl [v] 0 body', true)
else if ch then (Constr.Unsafe.make (Constr.Unsafe.LetIn b v body'), true) else (t, false)
| Constr.Unsafe.Cast c k ty =>
let (c', ch) := dce c in
if ch then (Constr.Unsafe.make (Constr.Unsafe.Cast c' k ty), true) else (t, false)
| Constr.Unsafe.App f args =>
(match Constr.Unsafe.kind f with
| Constr.Unsafe.Lambda b body =>
let n := Array.length args in
let a0 := Array.get args 0 in
let rest := Array.sub args 1 (Int.sub n 1) in

let (body', ch) := dce body in
let inner :=
if Constr.Unsafe.noccurn 1 body' then Some (Constr.Unsafe.substnl [a0] 0 body')
else None in
(match inner with
| Some i =>
if Int.equal n 1 then (i, true)
else (let (i', _) := dce (Constr.Unsafe.make (Constr.Unsafe.App i rest)) in (i', true))
| None =>
if ch then
(let f' := Constr.Unsafe.make (Constr.Unsafe.Lambda b body') in
(Constr.Unsafe.make (Constr.Unsafe.App f' args), true))
else (t, false)
end)
| _ => (t, false)
end)
| _ => (t, false)
end.

Ltac2 keep_alive (s0 : ident list) (pf : constr) : constr :=
let s1 := secvars pf in
List.fold_left (fun acc id =>
if List.exist (Ident.equal id) s1 then acc
else
let v := Constr.Unsafe.make (Constr.Unsafe.Var id) in
Constr.Unsafe.make (Constr.Unsafe.LetIn (Constr.Binder.make None (Constr.type v)) v (Constr.Unsafe.liftn 1 1 acc)))
pf s0.

Ltac2 strip_top (pf : constr) : constr :=
match Constr.Unsafe.kind pf with
| Constr.Unsafe.Cast c k _ => if Constr.Cast.equal k Constr.Cast.default then c else pf
| _ => pf
end.
Ltac2 diet (pf0 : constr) : constr :=
let pf := strip_top pf0 in
let (pf', ch) := dce pf in
if ch then keep_alive (secvars pf) pf' else pf.
Ltac2 install (pf : constr) : unit :=
let pf' := diet pf in
ltac1:(p |- exact_no_check p) (Ltac1.of_constr pf').

Ltac2 ctx_has_evar () : bool :=
List.exist (fun (h : ident * constr option * constr) => let (_, b, ty) := h in
if Constr.has_evar ty then true else match b with Some v => Constr.has_evar v | None => false end) (Control.hyps ()).
Ltac2 no_ctx_evar () : unit := if ctx_has_evar () then Control.zero Not_found else ().
End LDce2.
Ltac ldce_no_ctx_evar := ltac2:(LDce2.no_ctx_evar ()).

Ltac ldce_install pf := let f := ltac2:(pf |- LDce2.install (Option.get (Ltac1.to_constr pf))) in f pf.

Ltac ldce tac := idtac;
lazymatch goal with
| |- ?G => tryif has_evar G then tac
else tryif ldce_no_ctx_evar then (let pf := constr:(ltac:(tac) : G) in ldce_install pf)
else tac
end.

Module LDce3.
Import Ltac2.
Ltac2 install_keep (pf0 : constr) (pf1 : constr) : unit :=
let p := LDce2.keep_alive (LDce2.secvars (LDce2.strip_top pf0)) (LDce2.strip_top pf1) in
ltac1:(p |- exact_no_check p) (Ltac1.of_constr p).
End LDce3.
Ltac ldce_keep_install pf0 pf1 :=
let f := ltac2:(a b |- LDce3.install_keep (Option.get (Ltac1.to_constr a)) (Option.get (Ltac1.to_constr b))) in f pf0 pf1.
