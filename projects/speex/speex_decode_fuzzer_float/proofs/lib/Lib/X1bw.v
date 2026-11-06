(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Ltac2.
Module LL2.
Import Ltac2.
Ltac2 is_ctor (f : constr) : bool :=
match Constr.Unsafe.kind f with Constr.Unsafe.Constructor _ _ => true | _ => false end.

Ltac2 rec has_var (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Var _ => true
| Constr.Unsafe.App f args => if has_var f then true else Array.exist has_var args
| Constr.Unsafe.Cast c _ _ => has_var c
| _ => false
end.
Ltac2 add_atom (t : constr) (acc : constr list) : constr list :=
if has_var t then (if List.exist (Constr.equal t) acc then acc else t :: acc) else acc.

Ltac2 spine () : constr list :=
[constr:(Z.add); constr:(Z.sub); constr:(Z.mul); constr:(Z.opp); constr:(Z.of_nat); constr:(Z.to_nat); constr:(Z.succ); constr:(Z.pred);
constr:(Z.modulo); constr:(Z.div); constr:(Z.max); constr:(Z.min); constr:(Z.abs); constr:(Z.b2z);
constr:(andb); constr:(orb); constr:(negb); constr:(implb); constr:(Z.ltb); constr:(Z.leb); constr:(Z.eqb); constr:(Z.gtb); constr:(Z.geb);
constr:(Z.le); constr:(Z.lt); constr:(Z.ge); constr:(Z.gt); constr:(le); constr:(lt); constr:(ge); constr:(gt);
constr:(Nat.add); constr:(Nat.sub); constr:(Nat.mul); constr:(@eq); constr:(and); constr:(or); constr:(iff); constr:(not)].
Ltac2 rec atoms (sp : constr list) (acc : constr list) (t : constr) : constr list :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f args =>
if List.exist (Constr.equal f) sp then Array.fold_left (atoms sp) acc args
else if is_ctor f then (if has_var t then Array.fold_left (atoms sp) acc args else acc)
else add_atom t acc
| Constr.Unsafe.Prod b body => atoms sp (atoms sp acc (Constr.Binder.type b)) body
| Constr.Unsafe.Var _ => t :: acc
| Constr.Unsafe.Cast c _ _ => atoms sp acc c
| _ => acc
end.

Ltac2 logic () : constr list := [constr:(and); constr:(or); constr:(iff); constr:(not)].
Ltac2 rels () : constr list := [constr:(Z.le); constr:(Z.lt); constr:(Z.ge); constr:(Z.gt); constr:(le); constr:(lt); constr:(ge); constr:(gt); constr:(Z.divide)].
Ltac2 rec arith (lg : constr list) (rl : constr list) (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f args =>
if List.exist (Constr.equal f) lg then Array.for_all (arith lg rl) args
else if List.exist (Constr.equal f) rl then true
else if Constr.equal f constr:(@eq) then
(let ty := Array.get args 0 in
if Constr.equal ty constr:(Z) then true else if Constr.equal ty constr:(nat) then true
else Constr.equal ty constr:(bool))
else false
| Constr.Unsafe.Prod b body => if arith lg rl (Constr.Binder.type b) then arith lg rl body else false
| _ => if Constr.equal t constr:(True) then true else Constr.equal t constr:(False)
end.

Ltac2 rec arith_leaf (lg : constr list) (rl : constr list) (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f args =>
if List.exist (Constr.equal f) lg then Array.exist (arith_leaf lg rl) args
else if List.exist (Constr.equal f) rl then true
else if Constr.equal f constr:(@eq) then
(let ty := Array.get args 0 in
if Constr.equal ty constr:(Z) then true else if Constr.equal ty constr:(nat) then true
else Constr.equal ty constr:(bool))
else false
| Constr.Unsafe.Prod b body => if arith_leaf lg rl (Constr.Binder.type b) then true else arith_leaf lg rl body
| _ => false
end.
Ltac2 rec meets (xs : constr list) (ys : constr list) : bool :=
match xs with
| [] => false
| x :: xs' => if List.exist (Constr.equal x) ys then true else meets xs' ys
end.

Ltac2 table () : (ident * constr list) list :=
let sp := spine () in let lg := logic () in let rl := rels () in
List.map_filter (fun (h : ident * constr option * constr) =>
let (id, body, ty) := h in
match body with
| Some _ => None
| None => if arith lg rl ty then Some (id, atoms sp [] ty) else None
end) (Control.hyps ()).
Ltac2 select_pass (ga : constr list) (already : ident list) (tb : (ident * constr list) list) : ident list * constr list :=
List.fold_left (fun (acc : ident list * constr list) (e : ident * constr list) =>
let (sel, g) := acc in let (id, ats) := e in
if List.exist (Ident.equal id) already then acc
else if meets ats ga then (id :: sel, List.append ats g) else acc) (already, ga) tb.

Ltac2 rec select_n (n : int) (ga : constr list) (sel : ident list) (tb : (ident * constr list) list) : ident list :=
if Int.le n 0 then sel else
let (s1, g1) := select_pass ga sel tb in
if Int.equal (List.length s1) (List.length sel) then s1 else select_n (Int.sub n 1) g1 s1 tb.

Ltac2 defs () : (constr * constr list) list :=
let sp := spine () in
List.map_filter (fun (h : ident * constr option * constr) =>
let (id, body, _) := h in
match body with
| Some b => Some (Control.hyp id, atoms sp [] b)
| None => None
end) (Control.hyps ()).
Ltac2 expand_defs (ds : (constr * constr list) list) (ga : constr list) : constr list :=
List.fold_left (fun (acc : constr list) (d : constr * constr list) =>
let (x, ats) := d in if List.exist (Constr.equal x) ga then List.append ats acc else acc) ga ds.
Ltac2 lean_revert_n (n : int) : unit :=
let tb := table () in
let ds := defs () in
let ga := expand_defs ds (expand_defs ds (atoms (spine ()) [] (Control.goal ()))) in
let s := select_n n ga [] tb in
match s with [] => () | _ :: _ => Std.revert s end.
Ltac2 lean_revert () : unit := lean_revert_n 2.

Ltac2 goal_has_atoms () : unit :=
match atoms (spine ()) [] (Control.goal ()) with [] => Control.zero (Tactic_failure None) | _ :: _ => () end.

Ltac2 rec vars_of (acc : ident list) (c : constr) : ident list :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.Var id => if List.exist (Ident.equal id) acc then acc else id :: acc
| Constr.Unsafe.App f args => Array.fold_left vars_of (vars_of acc f) args
| Constr.Unsafe.Prod b body => vars_of (vars_of acc (Constr.Binder.type b)) body
| Constr.Unsafe.Lambda b body => vars_of (vars_of acc (Constr.Binder.type b)) body
| Constr.Unsafe.LetIn b v body => vars_of (vars_of (vars_of acc (Constr.Binder.type b)) v) body
| Constr.Unsafe.Cast c _ _ => vars_of acc c
| Constr.Unsafe.Case _ _ _ x bl => Array.fold_left vars_of (vars_of acc x) bl
| _ => acc
end.

Ltac2 dep_closure (hs : (ident * constr option * constr) list) (keep0 : ident list) : ident list :=
let rec close (keep : ident list) (n : int) :=
if Int.le n 0 then keep else
let keep' := List.fold_left (fun (k : ident list) (h : ident * constr option * constr) =>
let (id, body, ty) := h in
if List.exist (Ident.equal id) k then
(let k1 := vars_of k ty in match body with Some b => vars_of k1 b | None => k1 end)
else k) keep hs in
if Int.equal (List.length keep') (List.length keep) then keep' else close keep' (Int.sub n 1) in
close keep0 8.

Ltac2 keep_only (sel : ident list) : unit :=
let hs := Control.hyps () in
let keep := dep_closure hs (List.append sel (vars_of [] (Control.goal ()))) in
let cl := List.map_filter (fun (h : ident * constr option * constr) => let (id, _, _) := h in
if List.exist (Ident.equal id) keep then None else Some id) hs in
match cl with [] => () | _ :: _ => Std.clear cl end.

Ltac2 lean_keep_n (n : int) : unit :=
let tb := table () in
let ds := defs () in
let ga := expand_defs ds (expand_defs ds (atoms (spine ()) [] (Control.goal ()))) in
keep_only (select_n n ga [] tb).
Ltac2 lean_clear () : unit := keep_only [].

Ltac2 false_lia_newest () : unit :=
let tb := table () in
let ds := defs () in
match List.rev tb with
| [] => Control.zero (Tactic_failure None)
| cd :: _ =>
let (id, ats) := cd in
keep_only (select_n 6 (expand_defs ds (expand_defs ds ats)) [id] tb);
ltac1:(Zify.zify; xlia zchecker)
end.

Ltac2 closed_hyp_false () : unit :=
let tb := table () in
let rec go (cands : (ident * constr list) list) : unit :=
match cands with
| [] => Control.zero (Tactic_failure None)
| cd :: rest =>
let (id, _) := cd in
Control.plus (fun () => Control.once (fun () => keep_only [id]; ltac1:(exfalso; Zify.zify; xlia zchecker)))
(fun _ => go rest)
end in
go (List.rev tb).

Ltac2 small_ctx_false () : unit :=
let tb := table () in
if Int.le (List.length tb) 30
then (keep_only (List.map (fun (e : ident * constr list) => let (id, _) := e in id) tb); ltac1:(Zify.zify; xlia zchecker))
else Control.zero (Tactic_failure None).

Ltac2 goal_arith () : unit :=
if arith (logic ()) (rels ()) (Control.goal ()) then () else Control.zero (Tactic_failure None).

Ltac2 goal_liable () : unit :=
if arith_leaf (logic ()) (rels ()) (Control.goal ()) then () else Control.zero (Tactic_failure None).
Ltac2 lean_revert1 () : unit := Control.enter lean_revert.
Ltac2 lean_clear1 () : unit := Control.enter lean_clear.
Ltac2 goal_arith1 () : unit := Control.enter goal_arith.
Ltac2 goal_liable1 () : unit := Control.enter goal_liable.
Ltac2 lean_revert6 () : unit := Control.enter (fun () => lean_revert_n 6).
Ltac2 lean_keep2 () : unit := Control.enter (fun () => lean_keep_n 2).
Ltac2 lean_keep6 () : unit := Control.enter (fun () => lean_keep_n 6).
Ltac2 goal_has_atoms1 () : unit := Control.enter goal_has_atoms.
Ltac2 false_lia_newest1 () : unit := Control.enter false_lia_newest.
Ltac2 closed_hyp_false1 () : unit := Control.enter closed_hyp_false.
Ltac2 small_ctx_false1 () : unit := Control.enter small_ctx_false.
End LL2.

Ltac lean_revert := ltac2:(LL2.lean_revert1 ()).
Ltac lean_revert6 := ltac2:(LL2.lean_revert6 ()).
Ltac lean_clear := ltac2:(LL2.lean_clear1 ()).
Ltac goal_arith := ltac2:(LL2.goal_arith1 ()).
Ltac goal_liable := ltac2:(LL2.goal_liable1 ()).
Ltac goal_has_atoms := ltac2:(LL2.goal_has_atoms1 ()).
Ltac clear_all_hyps := repeat match goal with H : _ |- _ => clear H end.

Ltac lia1 := Zify.zify; xlia zchecker.
Ltac lean_keep := ltac2:(LL2.lean_keep2 ()).
Ltac lean_keep6 := ltac2:(LL2.lean_keep6 ()).

Ltac llia := lean_keep; Zify.zify; xlia zchecker.
Ltac cllia := lean_keep6; Zify.zify; xlia zchecker.

Ltac false_lia := lazymatch goal with |- False => ltac2:(LL2.false_lia_newest1 ()) end.

Ltac lean_refuted := lazymatch goal with |- ?g => let N := fresh in assert (N : ~ g) by (lean_keep6; intro; Zify.zify; xlia zchecker); clear N end.

Ltac any_hyp_false := ltac2:(LL2.closed_hyp_false1 ()).

Ltac small_ctx_false := ltac2:(LL2.small_ctx_false1 ()).

Ltac fat_lia :=
lazymatch goal with
| |- False => first [ false_lia | any_hyp_false | small_ctx_false ]
| |- _ => tryif (goal_liable; goal_has_atoms)
then (tryif lean_refuted then fail else (Zify.zify; xlia zchecker))
else (exfalso; first [ false_lia | any_hyp_false | small_ctx_false ])
end.

Ltac disj_lia :=
lazymatch goal with
| |- _ \/ _ => first [ left; disj_lia | right; disj_lia ]
| |- _ => first [ llia | cllia ]
end.

Ltac lean_lia unf :=
lazymatch goal with
| |- _ \/ _ \/ _ => first [ disj_lia | unf; first [ disj_lia | cllia | fat_lia ] ]
| |- _ => first [ llia | unf; first [ llia | disj_lia | cllia | false_lia | fat_lia ] ]
end.
