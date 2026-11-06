(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
From stdpp.bitvector Require Import definitions.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxOB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxOB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq1.

Module KL.
Import Ltac2.

Ltac2 arith_type (ty : constr) : bool :=
lazy_match! ty with
| Z => true | nat => true | N => true | positive => true
| _ => match Constr.Unsafe.kind ty with
| Constr.Unsafe.App f _ => lazy_match! f with @bv => true | _ => false end
| _ => false
end
end.

Ltac2 keep_links (links : ident list) (vs : ident list) : ident list :=
List.filter (fun v => List.exist (Ident.equal v) links) vs.

Ltac2 cone_of (rounds : int) (verbose : bool) : (ident * ident list) list * ident list :=
let hs := Control.hyps () in
let links := List.map_filter (fun h => let (id, _, ty) := h in if arith_type ty then Some id else None) hs in
let facts := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some b => if arith_type ty then Some (id, id :: keep_links links (SF2.vars_of [] b)) else None
| None => if SF2.arith_logic ty then Some (id, keep_links links (SF2.vars_of [] ty)) else None
end) hs in
let rec sat (n : int) (s : ident list) :=
if Int.le n 0 then s else
let s' := List.fold_left (fun acc f => let (id, vs) := f in
if SF2.meets vs s then
(if verbose then Message.print (Message.concat (Message.of_string "add ") (Message.of_ident id)) else ();
List.append vs acc)
else acc) s facts in
sat (Int.sub n 1) s' in
let g := keep_links links (SF2.vars_of [] (Control.goal ())) in
(if verbose then List.iter (fun id => Message.print (Message.concat (Message.of_string "goalvar ") (Message.of_ident id))) g else ());
(facts, sat rounds g).

Ltac2 cone_prune (rounds : int) : unit :=
let (facts, cone) := cone_of rounds false in
let ids := List.map_filter (fun f => let (id, vs) := f in

match Constr.Unsafe.kind (Control.hyp id) with
| Constr.Unsafe.Var _ =>
let (_, body, _) := List.find (fun h => let (i, _, _) := h in Ident.equal i id) (Control.hyps ()) in
match body with Some _ => None | None => match vs with [] => None | _ :: _ => if SF2.meets (id :: vs) cone then None else Some id end end
| _ => None
end) facts in
match ids with [] => () | _ :: _ => Std.clear ids end.

Ltac2 cone_prune1 (n : int) : unit := Control.enter (fun () => cone_prune n).

Ltac2 dbg_cone (rounds : int) : unit :=
let (facts, cone) := cone_of rounds true in
Message.print (Message.concat (Message.of_string "nfacts=") (Message.of_int (List.length facts)));
List.iter (fun id => Message.print (Message.concat (Message.of_string "cone ") (Message.of_ident id))) cone.
End KL.

Ltac klia_dbg1 := ltac2:(Control.enter (fun () => KL.dbg_cone 1)).
Ltac klia_prune1 := ltac2:(KL.cone_prune1 1).
Ltac klia_prune2 := ltac2:(KL.cone_prune1 2).
Ltac klia_prune3 := ltac2:(KL.cone_prune1 3).
Ltac klia1 := first [ klia_prune1; lia | lia ].
Ltac klia2 := first [ klia_prune2; lia | lia ].
Ltac klia3 := first [ klia_prune3; lia | lia ].

Ltac klia := first [ klia_prune1; lia | klia_prune2; lia | lia ].

Goal forall a b c d e : Z, (a <= b)%Z -> (b <= c)%Z -> (d <= e)%Z -> (e <= d + 1)%Z -> (a <= c)%Z.
Proof. intros a b c d e H1 H2 H3 H4. klia1. Qed.
