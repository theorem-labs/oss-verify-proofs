(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Std List Array Int FSet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition lf_pruned : Prop := True.
Lemma lf_pruned_I : lf_pruned. Proof. exact I. Qed.

Module LFast.

Ltac2 Type env := {
  ar : constant FSet.t;
  bad : constant FSet.t;
  pw : constant FSet.t;
  cmpz : constant FSet.t;
  cmpo : constant FSet.t;
  cmpi : inductive FSet.t;
  con : inductive FSet.t;
  tys : inductive FSet.t;
  eqi : inductive;
  zi : inductive;
  inc : constant;
  mark : constant }.

Ltac2 cst (c : constr) : constant :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant k _ => k
  | _ => Control.throw (Tactic_failure None)
  end.
Ltac2 ind (c : constr) : inductive :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Ind k _ => k
  | _ => Control.throw (Tactic_failure None)
  end.
Ltac2 cset (l : constr list) : constant FSet.t :=
  List.fold_left (fun s c => FSet.add (cst c) s) (FSet.empty FSet.Tags.constant_tag) l.
Ltac2 iset (l : constr list) : inductive FSet.t :=
  List.fold_left (fun s c => FSet.add (ind c) s) (FSet.empty FSet.Tags.inductive_tag) l.

Ltac2 mkenv () : env := {
  ar := cset [constr:(Z.add); constr:(Z.sub); constr:(Z.mul); constr:(Z.opp)];
  bad := cset [constr:(Z.modulo); constr:(Z.div); constr:(Z.land); constr:(Z.lor); constr:(Z.lxor); constr:(Z.shiftl);
               constr:(Z.shiftr); constr:(Z.abs); constr:(Z.max); constr:(Z.min); constr:(Z.quot); constr:(Z.rem);
               constr:(Z.log2); constr:(Z.sqrt); constr:(Z.gcd); constr:(Z.b2z); constr:(Z.sgn); constr:(Z.succ); constr:(Z.pred)];
  pw := cset [constr:(Z.pow); constr:(Z.of_nat); constr:(Z.to_nat); constr:(Z.of_N); constr:(Z.to_N); constr:(Z.to_pos)];
  cmpz := cset [constr:(Z.le); constr:(Z.lt); constr:(Z.ge); constr:(Z.gt)];
  cmpo := cset [constr:(lt); constr:(ge); constr:(gt); constr:(N.le); constr:(N.lt); constr:(N.ge); constr:(N.gt);
                constr:(Pos.le); constr:(Pos.lt); constr:(Pos.ge); constr:(Pos.gt)];
  cmpi := iset [constr:(le)];
  con := iset [constr:(and); constr:(or)];
  tys := iset [constr:(Z); constr:(nat); constr:(N); constr:(positive); constr:(bool)];
  eqi := ind constr:(@eq);
  zi := ind constr:(Z);
  inc := cst constr:(@List.In);
  mark := cst constr:(lf_pruned) }.

(* [comment removed for export] *)
Ltac2 rec is_lit (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constructor _ _ => Array.for_all is_lit args
      | _ => false
      end
  | Constr.Unsafe.Constructor _ _ => true
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec term_ok (e : env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constructor _ _ => true
      | Constr.Unsafe.Constant c _ =>
          if FSet.mem c (e.(ar)) then Array.for_all (term_ok e) args
          else if FSet.mem c (e.(pw)) then Array.for_all is_lit args
          else if FSet.mem c (e.(bad)) then false
          else Array.for_all (term_ok e) args
      | _ => Array.for_all (term_ok e) args
      end
  | Constr.Unsafe.Prod _ _ => false
  | Constr.Unsafe.Lambda _ _ => false
  | Constr.Unsafe.LetIn _ _ _ => false
  | _ => true
  end.

Ltac2 is_ind (i : inductive) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Ind j _ => Ind.equal i j
  | _ => false
  end.
Ltac2 in_inds (s : inductive FSet.t) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Ind j _ => FSet.mem j s
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec prop_ok (e : env) (strict : bool) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      let n := Array.length args in
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Ind i _ =>
          if Int.equal n 3 then
            (if Ind.equal i (e.(eqi)) then
               (if strict then
                  (if is_ind (e.(zi)) (Array.get args 0) then
                     (if term_ok e (Array.get args 1) then term_ok e (Array.get args 2) else false)
                   else false)
                else in_inds (e.(tys)) (Array.get args 0))
             else false)
          else if Int.equal n 2 then
            (if FSet.mem i (e.(con)) then
               (if prop_ok e strict (Array.get args 0) then prop_ok e strict (Array.get args 1) else false)
             else if strict then false else FSet.mem i (e.(cmpi)))
          else false
      | Constr.Unsafe.Constant c _ =>
          if Int.equal n 2 then
            (if FSet.mem c (e.(cmpz)) then
               (if strict then (if term_ok e (Array.get args 0) then term_ok e (Array.get args 1) else false) else true)
             else if strict then false else FSet.mem c (e.(cmpo)))
          else if Int.equal n 1 then prop_ok e strict (Array.get args 0)
          else false
      | _ => false
      end
  | _ => false
  end.

Ltac2 is_in (e : env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constant c _ => Constant.equal c (e.(inc))
      | _ => false
      end
  | Constr.Unsafe.Constant c _ => Constant.equal c (e.(mark))
  | _ => false
  end.

Ltac2 keep_hyps (e : env) (strict : bool) (withmem : bool) : unit :=
  let keep := List.fold_right
    (fun (id, _, ty) acc =>
       if prop_ok e strict ty then id :: acc
       else if withmem then (if is_in e ty then id :: acc else acc)
       else acc) (Control.hyps ()) [] in
  Std.keep keep.

(* [comment removed for export] *)
Ltac2 zprune0 () :=
  let e := mkenv () in
  let g := Control.goal () in
  let gok := if Constr.equal g constr:(False) then true else prop_ok e true g in
  if gok then keep_hyps e true false else Control.zero (Tactic_failure None).
(* [comment removed for export] *)
Ltac2 zprune1 () := keep_hyps (mkenv ()) false false.
(* [comment removed for export] *)
Ltac2 zprune_in0 () := keep_hyps (mkenv ()) true true.
Ltac2 zprune_in1 () := keep_hyps (mkenv ()) false true.

End LFast.

Ltac zprune := ltac2:(LFast.zprune0 ()).
Ltac zprune1 := ltac2:(LFast.zprune1 ()).
Ltac zprune_in0 := ltac2:(LFast.zprune_in0 ()); let H := fresh "LFp" in pose proof lf_pruned_I as H.
Ltac zprune_in1 := ltac2:(LFast.zprune_in1 ()); let H := fresh "LFp" in pose proof lf_pruned_I as H.
(* [comment removed for export] *)
Ltac lia_stock := Zify.zify; xlia zchecker.
Ltac lia_fast :=
  lazymatch goal with
  | _ : lf_pruned |- _ => lia_stock
  | _ => first [ solve [ zprune; lia_stock ] | solve [ zprune1; lia_stock ] | lia_stock ]
  end.
(* [comment removed for export] *)
Ltac lf_once tac :=
  lazymatch goal with
  | _ : lf_pruned |- _ => tac
  | _ => first [ solve [ zprune_in0; tac ] | solve [ zprune_in1; tac ] | tac ]
  end.
