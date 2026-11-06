(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Ltac2 Init Constr FSet Control Std List Array Bool Ident Int Env.
Import Ltac2.Init.
Ltac2 lf_is_hub (id : ident) : bool :=
match Env.expand [@YM05; @RunCeil] with
| r :: _ => Constr.equal (Constr.type (Control.hyp id)) (Env.instantiate r)
| [] => false
end.
Ltac2 rec lf_vars_of (acc : ident FSet.t) (c : constr) : ident FSet.t :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Var id => if lf_is_hub id then acc else FSet.add id acc
| Constr.Unsafe.App f args => Array.fold_left lf_vars_of (lf_vars_of acc f) args
| Constr.Unsafe.Prod b c => lf_vars_of (lf_vars_of acc (Constr.Binder.type b)) c
| Constr.Unsafe.Lambda b c => lf_vars_of (lf_vars_of acc (Constr.Binder.type b)) c
| Constr.Unsafe.LetIn b v c => lf_vars_of (lf_vars_of (lf_vars_of acc (Constr.Binder.type b)) v) c
| Constr.Unsafe.Cast c _ _ => lf_vars_of acc c
| Constr.Unsafe.Proj _ _ c => lf_vars_of acc c
| Constr.Unsafe.Case _ _ _ x bl => Array.fold_left lf_vars_of (lf_vars_of acc x) bl
| Constr.Unsafe.Fix _ _ bs cs =>
Array.fold_left lf_vars_of (Array.fold_left (fun a b => lf_vars_of a (Constr.Binder.type b)) acc bs) cs
| _ => acc
end.
Ltac2 rec lf_foreign (keep : ident FSet.t) (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Var id => if FSet.mem id keep then false else Bool.neg (lf_is_hub id)
| Constr.Unsafe.App f args =>
if lf_foreign keep f then true else Array.exist (lf_foreign keep) args
| Constr.Unsafe.Prod b c =>
if lf_foreign keep (Constr.Binder.type b) then true else lf_foreign keep c
| Constr.Unsafe.Lambda b c =>
if lf_foreign keep (Constr.Binder.type b) then true else lf_foreign keep c
| Constr.Unsafe.LetIn b v c =>
if lf_foreign keep (Constr.Binder.type b) then true
else if lf_foreign keep v then true else lf_foreign keep c
| Constr.Unsafe.Cast c _ _ => lf_foreign keep c
| Constr.Unsafe.Proj _ _ c => lf_foreign keep c
| Constr.Unsafe.Case _ _ _ x bl =>
if lf_foreign keep x then true else Array.exist (lf_foreign keep) bl
| _ => false
end.
Ltac2 lf_empty () : ident FSet.t := FSet.empty FSet.Tags.ident_tag.
Ltac2 lf_goal_vars (hs : (ident * constr option * constr) list) : ident FSet.t :=
List.fold_left
(fun acc h =>
let (id, body, _) := h in
match body with
| None => acc
| Some b => if FSet.mem id acc then lf_vars_of acc b else acc
end)
(lf_vars_of (lf_empty ()) (Control.goal ())) (List.rev hs).
Ltac2 lf_is_arith_type (t : constr) : bool :=
List.exist (fun c => Constr.equal t c) [ 'Z; 'nat; 'N; 'positive ].
Ltac2 lf_is_arith_head (ty : constr) : bool :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.App f args =>
if Constr.equal f '@eq then
(if Int.lt 0 (Array.length args) then lf_is_arith_type (Array.get args 0) else false)
else
List.exist (fun c => Constr.equal f c)
[ '@Z.le; '@Z.lt; '@Z.ge; '@Z.gt; '@and; '@or; '@iff; '@not; '@le; '@lt; '@ge; '@gt;
'@N.le; '@N.lt; '@Pos.le; '@Pos.lt; '@Z.divide ]
| _ => false
end.
Ltac2 lf_small_facts (hs : (ident * constr option * constr) list) : (ident FSet.t) list :=
List.fold_left
(fun acc h =>
let (_, _, ty) := h in
if lf_is_arith_head ty then
let vs := lf_vars_of (lf_empty ()) ty in
if Int.le (FSet.cardinal vs) 2 then vs :: acc else acc
else acc)
[] hs.
Ltac2 rec lf_chain (keep : ident FSet.t) (facts : (ident FSet.t) list) (fuel : int) : ident FSet.t :=
if Int.le fuel 0 then keep else
let keep' := List.fold_left
(fun acc vs => if FSet.is_empty (FSet.inter vs acc) then acc else FSet.union vs acc)
keep facts in
if Int.equal (FSet.cardinal keep') (FSet.cardinal keep) then keep else lf_chain keep' facts (Int.sub fuel 1).
Ltac2 lf_is_section (id : ident) : bool :=
match Env.get [id] with Some _ => true | None => false end.
Ltac2 rec lf_mentions_arith (ty : constr) : bool :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.App f args =>
if lf_is_arith_head ty then
(if List.exist (fun c => Constr.equal f c) [ '@and; '@or; '@iff; '@not ]
then Array.exist lf_mentions_arith args
else true)
else false
| Constr.Unsafe.Prod b c =>
if Constr.Unsafe.noccurn 1 c
then (if lf_mentions_arith (Constr.Binder.type b) then true else lf_mentions_arith c)
else false
| _ => Constr.equal ty 'False
end.
Ltac2 lf_section_has_arith (hs : (ident * constr option * constr) list) : bool :=
List.exist
(fun h =>
let (id, body, ty) := h in
if lf_is_section id then
match body with
| Some _ => if lf_is_arith_type ty then true else lf_mentions_arith ty
| None => lf_mentions_arith ty
end
else false)
hs.
Ltac2 lf_try_clear1 (id : ident) (n : int) : int :=
Control.once (fun () => Control.plus (fun () => Std.clear [id]; Int.add n 1) (fun _ => n)).
Ltac2 lf_clear_list (ids : ident list) : int :=
match ids with
| [] => 0
| _ :: _ =>
Control.once (fun () =>
Control.plus (fun () => Std.clear ids; List.length ids)
(fun _ => List.fold_left (fun n id => lf_try_clear1 id n) 0 ids))
end.
Ltac2 lf_is_prop (ty : constr) : bool :=
match Constr.Unsafe.kind (Constr.type ty) with
| Constr.Unsafe.Sort _ => Constr.equal (Constr.type ty) 'Prop
| _ => false
end.
Ltac2 rec lf_has_var (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Var _ => true
| Constr.Unsafe.App f args => if lf_has_var f then true else Array.exist lf_has_var args
| Constr.Unsafe.Prod b c => if lf_has_var (Constr.Binder.type b) then true else lf_has_var c
| Constr.Unsafe.Lambda b c => if lf_has_var (Constr.Binder.type b) then true else lf_has_var c
| Constr.Unsafe.LetIn b v c =>
if lf_has_var (Constr.Binder.type b) then true else if lf_has_var v then true else lf_has_var c
| Constr.Unsafe.Cast c _ _ => lf_has_var c
| Constr.Unsafe.Proj _ _ c => lf_has_var c
| Constr.Unsafe.Case _ _ _ x bl => if lf_has_var x then true else Array.exist lf_has_var bl
| _ => false
end.
Ltac2 lf_prune_to (keep : ident FSet.t) (hs : (ident * constr option * constr) list) : unit :=
let (ids, total) := List.fold_left
(fun (acc : ident list * int) h =>
let (ids, total) := acc in
let (id, body, ty) := h in
if lf_is_section id then acc
else
let total := Int.add total 1 in
if FSet.mem id keep then (ids, total)
else
let foreign :=
if lf_foreign keep ty then true
else match body with None => false | Some b => lf_foreign keep b end in
if foreign then (id :: ids, total)
else if lf_has_var ty then (ids, total)
else if lf_is_prop ty then (ids, total)
else (id :: ids, total)                       )
([], 0) hs in
let n := List.length ids in
if Int.lt n 2 then Control.zero (Tactic_failure None)
else if Int.lt (Int.mul 4 n) total then Control.zero (Tactic_failure None)
else
let m := lf_clear_list ids in
if Int.lt m 1 then Control.zero (Tactic_failure None) else ().
Ltac2 lf_guard_arith_sections () : bool := false.
Ltac2 lf_guard (hs : (ident * constr option * constr) list) : unit :=
if lf_guard_arith_sections () then
(if lf_section_has_arith hs then Control.zero (Tactic_failure None) else ())
else ().
Ltac2 lf_prune0 () : unit :=
let hs := Control.hyps () in lf_guard hs; lf_prune_to (lf_goal_vars hs) hs.
Ltac2 lf_prune1 () : unit :=
let hs := Control.hyps () in
lf_guard hs;
let k0 := lf_goal_vars hs in
let k1 := lf_chain k0 (lf_small_facts hs) 64 in
if Int.equal (FSet.cardinal k1) (FSet.cardinal k0) then Control.zero (Tactic_failure None)
else lf_prune_to k1 hs.
Ltac2 lf_arith_goal () : unit :=
if lf_is_arith_head (Control.goal ()) then () else Control.zero (Tactic_failure None).
Ltac lf_prune0 := ltac2:(Control.enter lf_prune0).
Ltac lf_prune1 := ltac2:(Control.enter lf_prune1).
Ltac lf_lia_orig := Zify.zify; xlia zchecker.
Ltac lf_nia_orig := Zify.zify; xnia zchecker.
Ltac lf_arith_goal := ltac2:(Control.enter lf_arith_goal).
Ltac Lia.lia ::=
tryif lf_arith_goal
then first [ solve [lf_prune0; lf_lia_orig] | solve [lf_prune1; lf_lia_orig] | lf_lia_orig ]
else first [ solve [lf_prune0; lf_lia_orig] | lf_lia_orig ].
Ltac Lia.nia ::=
tryif lf_arith_goal
then first [ solve [lf_prune0; lf_nia_orig] | solve [lf_prune1; lf_nia_orig] | lf_nia_orig ]
else first [ solve [lf_prune0; lf_nia_orig] | lf_nia_orig ].
Ltac2 lf_apply_nnpp () : unit :=
match Env.get [@Stdlib; @Logic; @Classical_Prop; @NNPP] with
| Some r =>
let c := Env.instantiate r in
Std.apply true false [fun () => (c, Std.NoBindings)] None
| None => Control.zero (Tactic_failure None)
end.
Ltac lf_apply_nnpp := ltac2:(Control.enter lf_apply_nnpp).
Ltac lf_tauto_int := intuition fail.
Ltac lf_tauto_orig := first [ lf_tauto_int | lf_apply_nnpp; lf_tauto_int ].
Ltac Corelib.Init.Tauto.tauto ::= first [ solve [lf_prune0; lf_tauto_int] | lf_tauto_orig ].
