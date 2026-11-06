(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith Lia.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module WFR.
  Import Ltac2.

  Ltac2 mem (id : ident) (l : ident list) : bool := List.mem Ident.equal id l.

  (* [comment removed for export] *)
  Ltac2 rec fv (bodies : (ident * constr) list) (c : constr) (acc : ident list) : ident list :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Var id =>
        if mem id acc then acc else
        let acc := id :: acc in
        (match List.assoc_opt Ident.equal id bodies with
         | Some b => fv bodies b acc
         | None => acc
         end)
    | Constr.Unsafe.App f args => Array.fold_left (fun a x => fv bodies x a) (fv bodies f acc) args
    | Constr.Unsafe.Cast c _ t => fv bodies t (fv bodies c acc)
    | Constr.Unsafe.Prod b c => fv bodies c (fv bodies (Constr.Binder.type b) acc)
    | Constr.Unsafe.Lambda b c => fv bodies c (fv bodies (Constr.Binder.type b) acc)
    | Constr.Unsafe.LetIn b v c => fv bodies c (fv bodies v (fv bodies (Constr.Binder.type b) acc))
    | Constr.Unsafe.Proj _ _ c => fv bodies c acc
    | _ => acc
    end.

  (* [comment removed for export] *)
  Ltac2 head_ref (c : constr) : Std.reference option :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Constant k _ => Some (Std.ConstRef k)
    | Constr.Unsafe.Ind i _ => Some (Std.IndRef i)
    | _ => None
    end.
  Ltac2 ref_eq (a : Std.reference) (b : Std.reference) : bool :=
    match a with
    | Std.ConstRef x => (match b with Std.ConstRef y => Constant.equal x y | _ => false end)
    | Std.IndRef x => (match b with Std.IndRef y => Ind.equal x y | _ => false end)
    | _ => false
    end.
  Ltac2 ref_in (r : Std.reference) (l : Std.reference list) : bool := List.exist (ref_eq r) l.
  Ltac2 rel_refs () : Std.reference list :=
    [reference:(Z.le); reference:(Z.lt); reference:(Z.ge); reference:(Z.gt);
     reference:(Peano.le); reference:(Peano.lt); reference:(Peano.ge); reference:(Peano.gt);
     reference:(N.le); reference:(N.lt); reference:(N.ge); reference:(N.gt)].
  Ltac2 num_refs () : Std.reference list := [reference:(Z); reference:(nat); reference:(N); reference:(positive)].
  Ltac2 bin_refs () : Std.reference list := [reference:(and); reference:(or); reference:(iff)].

  Ltac2 rec arith_prop (ty : constr) : bool :=
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.App f args =>
        (match head_ref f with
         | None => false
         | Some r =>
             if ref_eq r reference:(eq) then
               (match head_ref (Array.get args 0) with Some t => ref_in t (num_refs ()) | None => false end)
             else if ref_in r (rel_refs ()) then true
             else if ref_in r (bin_refs ()) then
               (if Int.equal (Array.length args) 2 then Bool.and (arith_prop (Array.get args 0)) (arith_prop (Array.get args 1)) else false)
             else if ref_eq r reference:(not) then
               (if Int.equal (Array.length args) 1 then arith_prop (Array.get args 0) else false)
             else false
         end)
    | _ => (match head_ref ty with
            | Some r => if ref_eq r reference:(True) then true else ref_eq r reference:(False)
            | None => false
            end)
    end.
  Ltac2 is_false (ty : constr) : bool :=
    match head_ref ty with Some r => ref_eq r reference:(False) | None => false end.

  (* [comment removed for export] *)
  Ltac2 in_free (s : Fresh.Free.t) (v : ident) : bool := Bool.neg (Ident.equal (Fresh.fresh s v) v).

  (* [comment removed for export] *)
  Ltac2 keep_relevant () : unit :=
    let g := Control.goal () in
    let _ := if Bool.and (arith_prop g) (Bool.neg (is_false g)) then () else Control.zero (Tactic_failure None) in
    let hs := Control.hyps () in
    let bodies := List.flat_map (fun (h : ident * constr option * constr) =>
                     let (id, b, _) := h in match b with Some v => [(id, v)] | None => [] end) hs in
    let rel0 := fv bodies g [] in
    match rel0 with
    | [] => Std.keep []
    | _ :: _ =>
      let cands := List.flat_map (fun (h : ident * constr option * constr) =>
                       let (id, b, ty) := h in
                       match b with
                       | Some _ => []
                       | None => if arith_prop ty then [(id, ty, Fresh.Free.of_constr ty)] else []
                       end) hs in
      let rec close (rel : ident list) (kept : ident list) (rest : (ident * constr * Fresh.Free.t) list) : ident list :=
        let (hit, miss) := List.partition (fun (p : ident * constr * Fresh.Free.t) =>
                               let (_, _, s) := p in List.exist (in_free s) rel) rest in
        match hit with
        | [] => kept
        | _ :: _ =>
            let rel := List.fold_left (fun r (p : ident * constr * Fresh.Free.t) => let (_, ty, _) := p in fv bodies ty r) rel hit in
            let kept := List.fold_left (fun k (p : ident * constr * Fresh.Free.t) => let (id, _, _) := p in id :: k) kept hit in
            close rel kept miss
        end in
      Std.keep (close rel0 [] cands)
    end.
End WFR.

Ltac wfr_keep_relevant := ltac2:(Ltac2.Control.enter WFR.keep_relevant).

Ltac lia_rel :=
  first [ solve [ wfr_keep_relevant; wf_clear_bignat; Zify.zify; xlia zchecker ]
        | Zify.zify; xlia zchecker ].
