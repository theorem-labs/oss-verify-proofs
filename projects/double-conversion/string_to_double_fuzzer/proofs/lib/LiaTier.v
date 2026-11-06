(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Std List Array Int FSet Ident.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module LTier.

(* [comment removed for export] *)
Ltac2 rec vars_of (acc : ident FSet.t) (t : constr) : ident FSet.t :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id => FSet.add id acc
  | Constr.Unsafe.App f args => Array.fold_left vars_of (vars_of acc f) args
  | Constr.Unsafe.Prod _ b => vars_of acc b
  | Constr.Unsafe.Lambda _ b => vars_of acc b
  | Constr.Unsafe.LetIn _ v b => vars_of (vars_of acc v) b
  | Constr.Unsafe.Cast c _ _ => vars_of acc c
  | Constr.Unsafe.Proj _ _ c => vars_of acc c
  | _ => acc
  end.

Ltac2 meets (a : ident FSet.t) (b : ident FSet.t) : bool := Bool.neg (FSet.is_empty (FSet.inter a b)).

(* [comment removed for export] *)
Ltac2 relevant (strict : bool) : ident list :=
  let e := LiaFast.LFast.mkenv () in
  let cands := List.fold_right
    (fun (id, _, ty) acc => if LiaFast.LFast.prop_ok e strict ty then (id, vars_of (FSet.empty FSet.Tags.ident_tag) ty) :: acc else acc)
    (Control.hyps ()) [] in
  let rec close (vs : ident FSet.t) (kept : ident list) (rest : (ident * ident FSet.t) list) :=
    let (hit, miss) := List.partition (fun (_, hv) => meets vs hv) rest in
    match hit with
    | [] => kept
    | _ => close (List.fold_left (fun s (_, hv) => FSet.union s hv) vs hit) (List.append (List.map (fun (id, _) => id) hit) kept) miss
    end in
  close (vars_of (FSet.empty FSet.Tags.ident_tag) (Control.goal ())) [] cands.

(* [comment removed for export] *)
Ltac2 rprune0 () :=
  let e := LiaFast.LFast.mkenv () in
  let g := Control.goal () in
  let gok := if Constr.equal g constr:(False) then true else LiaFast.LFast.prop_ok e true g in
  if gok then Std.keep (relevant true) else Control.zero (Tactic_failure None).
(* [comment removed for export] *)
Ltac2 rprune1 () := Std.keep (relevant false).

End LTier.

Ltac rprune0 := ltac2:(LTier.rprune0 ()).
Ltac rprune1 := ltac2:(LTier.rprune1 ()).
Ltac lia_fast2 :=
  lazymatch goal with
  | _ : lf_pruned |- _ => lia_stock
  | |- False => lia_fast      (* [comment removed for export] *)
  | _ => first [ solve [ rprune0; lia_stock ] | solve [ rprune1; lia_stock ] | lia_stock ]
  end.
