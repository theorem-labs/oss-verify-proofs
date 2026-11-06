(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith.
From Ltac2 Require Ltac2.
Module SatV2.
Import Ltac2.
Ltac2 rec mem_id (x : ident) (l : ident list) : bool :=
match l with [] => false | y :: r => if Ident.equal x y then true else mem_id x r end.
Ltac2 find_hyp_conv (ty : constr) : constr option :=
let hs := List.rev (Control.hyps ()) in
let rec syn (l : (ident * constr option * constr) list) :=
match l with
| [] => None
| h :: rest => let (id, _, hty) := h in if Constr.equal hty ty then Some (Control.hyp id) else syn rest
end in
match syn hs with
| Some c => Some c
| None =>
let rec cv (l : (ident * constr option * constr) list) :=
match l with
| [] => None
| h :: rest => let (id, _, hty) := h in
if Constr.equal (Constr.type hty) constr:(Prop)
then (if Unification.conv_full hty ty then Some (Control.hyp id) else cv rest)
else cv rest
end in cv hs
end.
Ltac2 hyp_named (x : ident) : constr option :=
let rec go (hs : (ident * constr option * constr) list) :=
match hs with
| [] => None
| h :: rest => let (id, body, _) := h in
if Ident.equal id x then (match body with Some v => Some v | None => Some (Control.hyp id) end) else go rest
end in go (Control.hyps ()).
Ltac2 rec sat2 (t : constr) (allow : ident list) : constr :=
match Constr.Unsafe.kind (Constr.type t) with
| Constr.Unsafe.Prod b _ =>
let bty := Constr.Binder.type b in
if Constr.equal (Constr.type bty) constr:(Prop) then
match find_hyp_conv bty with
| Some h => sat2 (Constr.Unsafe.make (Constr.Unsafe.App t [|h|])) allow
| None => t
end
else
match Constr.Binder.name b with
| None => t
| Some id =>
if mem_id id allow then
match hyp_named id with
| Some h => if Unification.conv_full (Constr.type h) bty
then sat2 (Constr.Unsafe.make (Constr.Unsafe.App t [|h|])) allow else t
| None => t
end
else t
end
| _ => t
end.
Ltac2 sat_pose2 (t : constr) (allow : ident list) (h : ident) : unit :=
let r := sat2 t allow in
Std.assert (Std.AssertType (Some (Std.IntroNaming (Std.IntroIdentifier h))) (Constr.type r)
(Some (fun () => Control.refine (fun () => r)))).
Ltac2 Notation "satv" t(constr) "with" allow(list0(ident)) "as" h(ident) := sat_pose2 t allow h.
Ltac2 Notation "satvl" t(constr) "using" allow(tactic(0)) "as" h(ident) := sat_pose2 t allow h.
End SatV2.
Export SatV2.
Ltac sat_pose t H :=
let T := type of t in
lazymatch T with
| ?A -> _ =>
lazymatch type of A with
| Prop => first [ let t' := constr:(t ltac:(assumption)) in sat_pose t' H | pose proof t as H ]
| _ => pose proof t as H
end
| _ => pose proof t as H
end.
Tactic Notation "sat" constr(t) "as" ident(H) := sat_pose t H.
