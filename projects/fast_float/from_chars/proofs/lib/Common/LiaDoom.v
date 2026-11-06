(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
From Ltac2 Require FSet Constant Ind.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require LiaFast.
#[local] Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac2 lf_arith_ops () : constant FSet.t :=
  List.fold_left (fun s r => FSet.add (LiaFast.lf_const r) s) (FSet.empty FSet.Tags.constant_tag)
    [reference:(Z.add); reference:(Z.sub); reference:(Z.mul); reference:(Z.opp); reference:(Z.succ); reference:(Z.pred);
     reference:(Z.of_nat); reference:(Z.to_nat); reference:(Z.of_N); reference:(Z.to_N); reference:(Z.pow);
     reference:(Z.div); reference:(Z.modulo); reference:(Z.max); reference:(Z.min); reference:(Z.abs);
     reference:(Nat.add); reference:(Nat.sub); reference:(Nat.mul); reference:(Nat.pred);
     reference:(N.add); reference:(N.sub); reference:(N.mul)].
(* [comment removed for export] *)
Ltac2 rec lf_count (a : constr) (l : (constr * int) list) : (constr * int) list :=
  match l with
  | [] => [(a, 1)]
  | p :: r => let (b, n) := p in if Constr.equal a b then (b, Int.add n 1) :: r else p :: lf_count a r
  end.
Ltac2 rec lf_atoms (ops : constant FSet.t) (t : constr) (acc : (constr * int) list) : (constr * int) list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ =>
          if FSet.mem c ops then Array.fold_left (fun a x => lf_atoms ops x a) acc args else lf_count t acc
      | Constr.Unsafe.Constructor _ _ => acc                 (* [comment removed for export] *)
      | _ => lf_count t acc
      end
  | Constr.Unsafe.Constructor _ _ => acc
  | Constr.Unsafe.Var _ => acc                               (* [comment removed for export] *)
  | Constr.Unsafe.Cast c _ _ => lf_atoms ops c acc
  | _ => acc
  end.
Ltac lf_occurs_in_hyps a :=
  lazymatch goal with
  | _ : context [a] |- _ => idtac
  | _ := context [a] |- _ => idtac
  end.
Ltac2 lf_doomed () : unit :=
  let g := Control.goal () in
  match Constr.Unsafe.kind g with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Ind i _ =>
          if Bool.and (Ind.equal i (LiaFast.lf_ind reference:(eq))) (Int.equal (Array.length args) 3) then
            (if LiaFast.lf_is_arith_type (Array.get args 0) then
               let ops := lf_arith_ops () in
               let ats := lf_atoms ops (Array.get args 2) (lf_atoms ops (Array.get args 1) []) in
               let fresh_once (p : constr * int) : bool :=
                 let (a, n) := p in
                 if Int.equal n 1 then
                   (if Constr.has_evar a then false
                    else match Control.case (fun () => ltac1:(a |- lf_occurs_in_hyps a) (Ltac1.of_constr a)) with
                         | Val _ => false
                         | Err _ => true
                         end)
                 else false in
               if List.exist fresh_once ats then () else Control.zero (Tactic_failure None)
             else Control.zero (Tactic_failure None))
          else Control.zero (Tactic_failure None)
      | _ => Control.zero (Tactic_failure None)
      end
  | _ => Control.zero (Tactic_failure None)
  end.
Ltac lf_doomed := ltac2:(Control.enter lf_doomed).

