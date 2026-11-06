(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 Type pa_env := { pk_and : inductive; pk_or : inductive; pk_eq : inductive; pk_le : inductive; pk_False : inductive;
  pk_True : inductive; pk_ex : inductive; pk_Z : inductive; pk_nat : inductive; pk_N : inductive; pk_pos : inductive; pk_bool : inductive;
  pc_iff : constant; pc_not : constant; pc_Zle : constant; pc_Zlt : constant; pc_Zge : constant; pc_Zgt : constant;
  pc_lt : constant; pc_ge : constant; pc_gt : constant;
  p_ops : constant FSet.t; p_lits : constructor FSet.t; p_succ : constructor }.
Ltac2 pa_i (r : Std.reference) : inductive := match r with Std.IndRef i => i | _ => Control.throw Not_found end.
Ltac2 pa_c (r : Std.reference) : constant := match r with Std.ConstRef c => c | _ => Control.throw Not_found end.
Ltac2 pa_k (r : Std.reference) : constructor := match r with Std.ConstructRef c => c | _ => Control.throw Not_found end.
Ltac2 pa_cset (l : constant list) : constant FSet.t := List.fold_left (fun s c => FSet.add c s) (FSet.empty FSet.Tags.constant_tag) l.
Ltac2 pa_kset (l : constructor list) : constructor FSet.t := List.fold_left (fun s c => FSet.add c s) (FSet.empty FSet.Tags.constructor_tag) l.
Ltac2 pa_mk_env () : pa_env :=
  { pk_and := pa_i reference:(and); pk_or := pa_i reference:(or); pk_eq := pa_i reference:(eq); pk_le := pa_i reference:(Peano.le);
    pk_False := pa_i reference:(False); pk_True := pa_i reference:(True); pk_ex := pa_i reference:(ex); pk_Z := pa_i reference:(Z);
    pk_nat := pa_i reference:(nat); pk_N := pa_i reference:(N); pk_pos := pa_i reference:(positive); pk_bool := pa_i reference:(bool);
    pc_iff := pa_c reference:(iff); pc_not := pa_c reference:(not); pc_Zle := pa_c reference:(Z.le); pc_Zlt := pa_c reference:(Z.lt);
    pc_Zge := pa_c reference:(Z.ge); pc_Zgt := pa_c reference:(Z.gt); pc_lt := pa_c reference:(Peano.lt);
    pc_ge := pa_c reference:(Peano.ge); pc_gt := pa_c reference:(Peano.gt);
    p_ops := pa_cset
             [pa_c reference:(Z.add); pa_c reference:(Z.sub); pa_c reference:(Z.mul); pa_c reference:(Z.opp);
              pa_c reference:(Z.pow); pa_c reference:(Z.succ); pa_c reference:(Z.pred); pa_c reference:(Z.of_nat);
              pa_c reference:(Z.to_nat); pa_c reference:(Z.div); pa_c reference:(Z.modulo); pa_c reference:(Z.max);
              pa_c reference:(Z.min); pa_c reference:(Z.abs); pa_c reference:(Z.quot); pa_c reference:(Z.rem);
              pa_c reference:(Z.eqb); pa_c reference:(Z.leb); pa_c reference:(Z.ltb); pa_c reference:(Z.geb); pa_c reference:(Z.gtb);
              pa_c reference:(Nat.add); pa_c reference:(Nat.sub); pa_c reference:(Nat.mul); pa_c reference:(Nat.pred);
              pa_c reference:(Nat.div); pa_c reference:(Nat.modulo); pa_c reference:(Nat.max); pa_c reference:(Nat.min);
              pa_c reference:(Nat.eqb); pa_c reference:(Nat.leb); pa_c reference:(Nat.ltb);
              pa_c reference:(andb); pa_c reference:(orb); pa_c reference:(negb);
              pa_c reference:(Z.of_N); pa_c reference:(Z.to_N); pa_c reference:(N.of_nat); pa_c reference:(N.to_nat);
              pa_c reference:(Z.double); pa_c reference:(Z.pos_sub)];
    p_lits := pa_kset
             [pa_k reference:(Z0); pa_k reference:(Zpos); pa_k reference:(Zneg); pa_k reference:(xI); pa_k reference:(xO);
              pa_k reference:(xH); pa_k reference:(N0); pa_k reference:(Npos); pa_k reference:(O); pa_k reference:(true);
              pa_k reference:(false)];
    p_succ := pa_k reference:(S) }.

(* [comment removed for export] *)
Ltac2 Type pa_tbl := { mutable t_vars : (ident, int) FMap.t; mutable t_apps : (constant, (constr * int) list) FMap.t;
                       mutable t_other : (constr * int) list; mutable t_n : int }.
Ltac2 pa_new_tbl () : pa_tbl := { t_vars := FMap.empty FSet.Tags.ident_tag; t_apps := FMap.empty FSet.Tags.constant_tag;
                                   t_other := []; t_n := 0 }.
Ltac2 rec pa_find (t : constr) (l : (constr * int) list) : int option :=
  match l with [] => None | p :: r => let (a, i) := p in if Constr.equal a t then Some i else pa_find t r end.
Ltac2 pa_fresh (tb : pa_tbl) : int := let n := tb.(t_n) in tb.(t_n) := Int.add n 1; n.
Ltac2 pa_id (tb : pa_tbl) (t : constr) : int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id =>
      (match FMap.find_opt id (tb.(t_vars)) with
       | Some i => i
       | None => let n := pa_fresh tb in tb.(t_vars) := FMap.add id n (tb.(t_vars)); n end)
  | Constr.Unsafe.App f _ =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant c _ =>
           let bk := match FMap.find_opt c (tb.(t_apps)) with Some l => l | None => [] end in
           (match pa_find t bk with
            | Some i => i
            | None => let n := pa_fresh tb in tb.(t_apps) := FMap.add c ((t, n) :: bk) (tb.(t_apps)); n end)
       | _ =>
           (match pa_find t (tb.(t_other)) with
            | Some i => i
            | None => let n := pa_fresh tb in tb.(t_other) := (t, n) :: tb.(t_other); n end)
       end)
  | _ =>
      (match pa_find t (tb.(t_other)) with
       | Some i => i
       | None => let n := pa_fresh tb in tb.(t_other) := (t, n) :: tb.(t_other); n end)
  end.

(* [comment removed for export] *)
Ltac2 rec pa_tatoms (e : pa_env) (tb : pa_tbl) (t : constr) (acc : int list) : int list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant c _ =>
           if FSet.mem c (e.(p_ops)) then Array.fold_left (fun a x => pa_tatoms e tb x a) acc args
           else pa_id tb t :: acc
       | Constr.Unsafe.Constructor k _ =>
           if Constructor.equal k (e.(p_succ)) then Array.fold_left (fun a x => pa_tatoms e tb x a) acc args
           else if FSet.mem k (e.(p_lits)) then acc
           else pa_id tb t :: acc
       | _ => pa_id tb t :: acc
       end)
  | Constr.Unsafe.Constructor k _ => if FSet.mem k (e.(p_lits)) then acc else pa_id tb t :: acc
  | _ => pa_id tb t :: acc
  end.

(* [comment removed for export] *)
Ltac2 rec pa_patoms (e : pa_env) (tb : pa_tbl) (t : constr) (acc : int list) : int list option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Ind i _ =>
           if Ind.equal i (e.(pk_and)) then pa_pat2 e tb args acc
           else if Ind.equal i (e.(pk_or)) then pa_pat2 e tb args acc
           else if Ind.equal i (e.(pk_le)) then Some (pa_tatoms e tb (Array.get args 1) (pa_tatoms e tb (Array.get args 0) acc))
           else if Ind.equal i (e.(pk_eq)) then
             (match Constr.Unsafe.kind (Array.get args 0) with
              | Constr.Unsafe.Ind j _ =>
                  if (if Ind.equal j (e.(pk_Z)) then true else if Ind.equal j (e.(pk_nat)) then true
                      else if Ind.equal j (e.(pk_N)) then true else if Ind.equal j (e.(pk_pos)) then true
                      else Ind.equal j (e.(pk_bool)))
                  then Some (pa_tatoms e tb (Array.get args 2) (pa_tatoms e tb (Array.get args 1) acc)) else None
              | _ => None end)
           else None
       | Constr.Unsafe.Constant c _ =>
           if (if Constant.equal c (e.(pc_Zle)) then true else if Constant.equal c (e.(pc_Zlt)) then true
               else if Constant.equal c (e.(pc_Zge)) then true else if Constant.equal c (e.(pc_Zgt)) then true
               else if Constant.equal c (e.(pc_lt)) then true else if Constant.equal c (e.(pc_ge)) then true
               else Constant.equal c (e.(pc_gt)))
           then Some (pa_tatoms e tb (Array.get args 1) (pa_tatoms e tb (Array.get args 0) acc))
           else if Constant.equal c (e.(pc_not)) then pa_patoms e tb (Array.get args 0) acc
           else if Constant.equal c (e.(pc_iff)) then pa_pat2 e tb args acc
           else None
       | _ => None
       end)
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then
        (match pa_patoms e tb (Constr.Binder.type b) acc with
         | Some a1 => pa_patoms e tb c a1
         | None => None end)
      else None
  | Constr.Unsafe.Ind i _ => if Ind.equal i (e.(pk_False)) then Some acc else if Ind.equal i (e.(pk_True)) then Some acc else None
  | _ => None
  end
with pa_pat2 (e : pa_env) (tb : pa_tbl) (args : constr array) (acc : int list) : int list option :=
  match pa_patoms e tb (Array.get args 0) acc with
  | Some a1 => pa_patoms e tb (Array.get args 1) a1
  | None => None
  end.

(* [comment removed for export] *)
Ltac2 rec pa_disj (e : pa_env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Ind i _ =>
           if Ind.equal i (e.(pk_or)) then true
           else if Ind.equal i (e.(pk_and)) then (if pa_disj e (Array.get args 0) then true else pa_disj e (Array.get args 1))
           else false
       | Constr.Unsafe.Constant c _ =>
           if Constant.equal c (e.(pc_not)) then true else Constant.equal c (e.(pc_iff))
       | _ => false
       end)
  | Constr.Unsafe.Prod _ _ => true
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec pa_arity_prop (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ c => pa_arity_prop c
  | Constr.Unsafe.Sort _ => Constr.equal t 'Prop
  | _ => false
  end.
Ltac2 Type pa_hc := { mutable hc_l : (constr * bool) list }.
Ltac2 pa_head_prop (hc : pa_hc) (f : constr) : bool :=
  let rec find l := match l with [] => None | p :: r => let (a, b) := p in if Constr.equal a f then Some b else find r end in
  match find (hc.(hc_l)) with
  | Some b => b
  | None => let b := pa_arity_prop (Constr.type f) in hc.(hc_l) := (f, b) :: hc.(hc_l); b
  end.
Ltac2 pa_is_prop (e : pa_env) (hc : pa_hc) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Ind i _ =>
           if Ind.equal i (e.(pk_eq)) then true else if Ind.equal i (e.(pk_and)) then true
           else if Ind.equal i (e.(pk_or)) then true else if Ind.equal i (e.(pk_ex)) then true
           else pa_head_prop hc f
       | Constr.Unsafe.Constant c _ =>
           if Constant.equal c (e.(pc_not)) then true else if Constant.equal c (e.(pc_iff)) then true
           else pa_head_prop hc f
       | _ => false
       end)
  | _ => false
  end.

Ltac2 pa_rounds := 8.
Ltac2 rec pa_dedup (l : int list) (acc : int list) : int list :=
  match l with [] => acc | x :: r => if List.exist (fun y => Int.equal x y) acc then pa_dedup r acc else pa_dedup r (x :: acc) end.
Ltac2 pa_clear (ids : ident list) :=
  Control.plus (fun () => Std.clear ids) (fun _ => List.iter (fun h => try (Std.clear [h])) ids).

(* [comment removed for export] *)
Ltac2 pa_analyze (all : bool) : ident list * ident list * ident list * ident list :=
  let e := pa_mk_env () in
  let tb := pa_new_tbl () in
  let hc := { hc_l := [] } in
  let hs := Control.hyps () in
  let gat0 := match pa_patoms e tb (Control.goal ()) [] with Some a => pa_dedup a [] | None => [] end in
  (* [comment removed for export] *)
  let (arith, other) := List.fold_left (fun (ar, ot) (h, b, t) =>
        match b with
        | Some _ => (ar, ot)
        | None =>
          match pa_patoms e tb t [] with
          | Some a => ((h, pa_dedup a [], pa_disj e t) :: ar, ot)
          | None => if all then (if pa_is_prop e hc t then (ar, h :: ot) else (ar, ot)) else (ar, ot)
          end
        end) ([], []) hs in
  let gat := match gat0 with
             | [] => (match List.find_opt (fun (_, a, _) => match a with [] => false | _ => true end) arith with
                      | Some (_, a, _) => a | None => [] end)
             | _ => gat0 end in
  let n := tb.(t_n) in
  let strong := Array.make n false in
  let reached := Array.make n false in
  let isg := Array.make n false in
  List.iter (fun i => Array.set reached i true; Array.set strong i true; Array.set isg i true) gat;
  let arr := Array.of_list arith in
  let na := Array.length arr in
  let kept := Array.make na false in
  let rec round k :=
    if Int.equal k 0 then () else
    let news := Ref.ref [] in
    let rec scan j :=
      if Int.equal j na then () else
      ((if Array.get kept j then () else
          let (_, a, d) := Array.get arr j in
          if d then () else
          if List.exist (fun i => Array.get strong i) a then
            (Array.set kept j true; List.iter (fun i => Array.set reached i true; Ref.set news (i :: Ref.get news)) a)
          else ());
       scan (Int.add j 1)) in
    scan 0;
    match Ref.get news with
    | [] => ()
    | l => List.iter (fun i => Array.set strong i true) l; round (Int.sub k 1)
    end in
  round pa_rounds;
  let rec fin j :=
    if Int.equal j na then () else
    ((if Array.get kept j then () else
        let (_, a, d) := Array.get arr j in
        if d then () else
        if List.for_all (fun i => Array.get reached i) a then Array.set kept j true else ());
     fin (Int.add j 1)) in
  fin 0;
  let base := Ref.ref other in
  let disj := Ref.ref [] in
  let near := Ref.ref [] in
  let conn := Ref.ref [] in
  (* [comment removed for export] *)
  let rec coll j :=
    if Int.lt j 0 then () else
    (let (h, a, d) := Array.get arr j in
     (if d then
        (Ref.set disj (h :: Ref.get disj);
         if List.exist (fun i => Array.get isg i) a then Ref.set near (h :: Ref.get near)
         else if List.exist (fun i => Array.get reached i) a then Ref.set conn (h :: Ref.get conn) else ())
      else if Array.get kept j then () else Ref.set base (h :: Ref.get base));
     coll (Int.sub j 1)) in
  coll (Int.sub na 1);
  (Ref.get base, Ref.get disj, Ref.get near, Ref.get conn).

(* [comment removed for export] *)
Ltac2 Type pa4_env := { e_and : inductive; e_or : inductive; e_eq : inductive; e_le : inductive; e_False : inductive; e_True : inductive;
  e_ex : inductive; e_not : constant; e_iff : constant; e_cmp : constant FSet.t; e_ty : inductive FSet.t;
  e_ops : constant FSet.t; e_lits : constructor FSet.t; e_succ : constructor }.
Ltac2 pa4_i (r : Std.reference) : inductive := match r with Std.IndRef i => i | _ => Control.throw Not_found end.
Ltac2 pa4_c (r : Std.reference) : constant := match r with Std.ConstRef c => c | _ => Control.throw Not_found end.
Ltac2 pa4_k (r : Std.reference) : constructor := match r with Std.ConstructRef c => c | _ => Control.throw Not_found end.
Ltac2 pa4_cset (l : constant list) : constant FSet.t := List.fold_left (fun s c => FSet.add c s) (FSet.empty FSet.Tags.constant_tag) l.
Ltac2 pa4_iset (l : inductive list) : inductive FSet.t := List.fold_left (fun s c => FSet.add c s) (FSet.empty FSet.Tags.inductive_tag) l.
Ltac2 pa4_kset (l : constructor list) : constructor FSet.t := List.fold_left (fun s c => FSet.add c s) (FSet.empty FSet.Tags.constructor_tag) l.
Ltac2 pa4_mk_env () : pa4_env :=
  { e_and := pa4_i reference:(and); e_or := pa4_i reference:(or); e_eq := pa4_i reference:(eq); e_le := pa4_i reference:(Peano.le);
    e_False := pa4_i reference:(False); e_True := pa4_i reference:(True); e_ex := pa4_i reference:(ex);
    e_not := pa4_c reference:(not); e_iff := pa4_c reference:(iff);
    e_cmp := pa4_cset [pa4_c reference:(Z.le); pa4_c reference:(Z.lt); pa4_c reference:(Z.ge); pa4_c reference:(Z.gt);
                        pa4_c reference:(Peano.lt); pa4_c reference:(Peano.ge); pa4_c reference:(Peano.gt)];
    e_ty := pa4_iset [pa4_i reference:(Z); pa4_i reference:(nat); pa4_i reference:(N); pa4_i reference:(positive); pa4_i reference:(bool)];
    e_ops := pa4_cset
             [pa4_c reference:(Z.add); pa4_c reference:(Z.sub); pa4_c reference:(Z.mul); pa4_c reference:(Z.opp);
              pa4_c reference:(Z.pow); pa4_c reference:(Z.succ); pa4_c reference:(Z.pred); pa4_c reference:(Z.of_nat);
              pa4_c reference:(Z.to_nat); pa4_c reference:(Z.div); pa4_c reference:(Z.modulo); pa4_c reference:(Z.max);
              pa4_c reference:(Z.min); pa4_c reference:(Z.abs); pa4_c reference:(Z.quot); pa4_c reference:(Z.rem);
              pa4_c reference:(Z.eqb); pa4_c reference:(Z.leb); pa4_c reference:(Z.ltb); pa4_c reference:(Z.geb); pa4_c reference:(Z.gtb);
              pa4_c reference:(Nat.add); pa4_c reference:(Nat.sub); pa4_c reference:(Nat.mul); pa4_c reference:(Nat.pred);
              pa4_c reference:(Nat.div); pa4_c reference:(Nat.modulo); pa4_c reference:(Nat.max); pa4_c reference:(Nat.min);
              pa4_c reference:(Nat.eqb); pa4_c reference:(Nat.leb); pa4_c reference:(Nat.ltb);
              pa4_c reference:(andb); pa4_c reference:(orb); pa4_c reference:(negb);
              pa4_c reference:(Z.of_N); pa4_c reference:(Z.to_N); pa4_c reference:(N.of_nat); pa4_c reference:(N.to_nat);
              pa4_c reference:(Z.double); pa4_c reference:(Z.pos_sub)];
    e_lits := pa4_kset
             [pa4_k reference:(Z0); pa4_k reference:(Zpos); pa4_k reference:(Zneg); pa4_k reference:(xI); pa4_k reference:(xO);
              pa4_k reference:(xH); pa4_k reference:(N0); pa4_k reference:(Npos); pa4_k reference:(O); pa4_k reference:(true);
              pa4_k reference:(false)];
    e_succ := pa4_k reference:(S) }.
(* [comment removed for export] *)
Ltac2 Type pa4_st := {
  mutable s_vars : (ident, int) FMap.t; mutable s_consts : (constant, int) FMap.t; mutable s_appv : (ident, (constr * int) list) FMap.t;
  mutable s_apps : (constant, (constr * int) list) FMap.t; mutable s_other : (constr * int) list; mutable s_n : int;
  mutable s_pc : (constant, bool) FMap.t; mutable s_pi : (inductive, bool) FMap.t;
  mutable s_dj : bool; mutable s_na : bool }.
Ltac2 pa4_new () : pa4_st :=
  { s_vars := FMap.empty FSet.Tags.ident_tag; s_consts := FMap.empty FSet.Tags.constant_tag;
    s_appv := FMap.empty FSet.Tags.ident_tag; s_apps := FMap.empty FSet.Tags.constant_tag; s_other := []; s_n := 0;
    s_pc := FMap.empty FSet.Tags.constant_tag; s_pi := FMap.empty FSet.Tags.inductive_tag; s_dj := false; s_na := false }.
Ltac2 rec pa4_find (t : constr) (l : (constr * int) list) : int :=
  match l with [] => -1 | p :: r => let (a, i) := p in if Constr.equal a t then i else pa4_find t r end.
Ltac2 pa4_fresh (st : pa4_st) : int := let n := st.(s_n) in st.(s_n) := Int.add n 1; n.
Ltac2 pa4_other_id (st : pa4_st) (t : constr) : int :=
  let i := pa4_find t (st.(s_other)) in
  if Int.le 0 i then i else let n := pa4_fresh st in st.(s_other) := (t, n) :: st.(s_other); n.
(* [comment removed for export] *)
Ltac2 pa4_app_id (st : pa4_st) (t : constr) (f : constr) (args : constr array) : int :=
  match Constr.Unsafe.kind (Array.get args (Int.sub (Array.length args) 1)) with
  | Constr.Unsafe.Var v =>
      let bk := match FMap.find_opt v (st.(s_appv)) with Some l => l | None => [] end in
      let i := pa4_find t bk in
      if Int.le 0 i then i else let n := pa4_fresh st in st.(s_appv) := FMap.add v ((t, n) :: bk) (st.(s_appv)); n
  | _ =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constant c _ =>
          let bk := match FMap.find_opt c (st.(s_apps)) with Some l => l | None => [] end in
          let i := pa4_find t bk in
          if Int.le 0 i then i else let n := pa4_fresh st in st.(s_apps) := FMap.add c ((t, n) :: bk) (st.(s_apps)); n
      | _ => pa4_other_id st t
      end
  end.
Ltac2 pa4_leaf_id (st : pa4_st) (t : constr) : int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id =>
      (match FMap.find_opt id (st.(s_vars)) with
       | Some i => i
       | None => let n := pa4_fresh st in st.(s_vars) := FMap.add id n (st.(s_vars)); n end)
  | Constr.Unsafe.Constant c _ =>
      (match FMap.find_opt c (st.(s_consts)) with
       | Some i => i
       | None => let n := pa4_fresh st in st.(s_consts) := FMap.add c n (st.(s_consts)); n end)
  | _ => pa4_other_id st t
  end.
(* [comment removed for export] *)
Ltac2 rec pa4_tat (e : pa4_env) (st : pa4_st) (t : constr) (acc : int list) : int list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant c _ =>
           if FSet.mem c (e.(e_ops)) then pa4_targs e st args 0 (Array.length args) acc
           else pa4_app_id st t f args :: acc
       | Constr.Unsafe.Constructor k _ =>
           if FSet.mem k (e.(e_lits)) then acc
           else if Constructor.equal k (e.(e_succ)) then pa4_tat e st (Array.get args 0) acc
           else pa4_app_id st t f args :: acc
       | _ => pa4_app_id st t f args :: acc
       end)
  | Constr.Unsafe.Constructor k _ => if FSet.mem k (e.(e_lits)) then acc else pa4_leaf_id st t :: acc
  | _ => pa4_leaf_id st t :: acc
  end
with pa4_targs (e : pa4_env) (st : pa4_st) (args : constr array) (i : int) (n : int) (acc : int list) : int list :=
  if Int.equal i n then acc else pa4_targs e st args (Int.add i 1) n (pa4_tat e st (Array.get args i) acc).
(* [comment removed for export] *)
Ltac2 rec pa4_pat (e : pa4_env) (st : pa4_st) (t : constr) (acc : int list) : int list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Ind i _ =>
           if Ind.equal i (e.(e_and)) then pa4_pat e st (Array.get args 1) (pa4_pat e st (Array.get args 0) acc)
           else if Ind.equal i (e.(e_eq)) then
             (match Constr.Unsafe.kind (Array.get args 0) with
              | Constr.Unsafe.Ind j _ =>
                  if FSet.mem j (e.(e_ty)) then pa4_tat e st (Array.get args 2) (pa4_tat e st (Array.get args 1) acc)
                  else (st.(s_na) := true; acc)
              | _ => st.(s_na) := true; acc end)
           else if Ind.equal i (e.(e_or)) then (st.(s_dj) := true; pa4_pat e st (Array.get args 1) (pa4_pat e st (Array.get args 0) acc))
           else if Ind.equal i (e.(e_le)) then pa4_tat e st (Array.get args 1) (pa4_tat e st (Array.get args 0) acc)
           else (st.(s_na) := true; acc)
       | Constr.Unsafe.Constant c _ =>
           if FSet.mem c (e.(e_cmp)) then pa4_tat e st (Array.get args 1) (pa4_tat e st (Array.get args 0) acc)
           else if Constant.equal c (e.(e_not)) then (st.(s_dj) := true; pa4_pat e st (Array.get args 0) acc)
           else if Constant.equal c (e.(e_iff)) then (st.(s_dj) := true; pa4_pat e st (Array.get args 1) (pa4_pat e st (Array.get args 0) acc))
           else (st.(s_na) := true; acc)
       | _ => st.(s_na) := true; acc
       end)
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then (st.(s_dj) := true; pa4_pat e st c (pa4_pat e st (Constr.Binder.type b) acc))
      else (st.(s_na) := true; acc)
  | Constr.Unsafe.Ind i _ => if Ind.equal i (e.(e_False)) then acc else if Ind.equal i (e.(e_True)) then acc else (st.(s_na) := true; acc)
  | _ => st.(s_na) := true; acc
  end.
Ltac2 rec pa4_arity_prop (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ c => pa4_arity_prop c
  | Constr.Unsafe.Sort _ => Constr.equal t 'Prop
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 pa4_headp (e : pa4_env) (st : pa4_st) (f : constr) : bool :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Ind i _ =>
      if Ind.equal i (e.(e_eq)) then true else if Ind.equal i (e.(e_and)) then true else if Ind.equal i (e.(e_or)) then true
      else if Ind.equal i (e.(e_ex)) then true
      else (match FMap.find_opt i (st.(s_pi)) with
            | Some b => b
            | None => let b := pa4_arity_prop (Constr.type f) in st.(s_pi) := FMap.add i b (st.(s_pi)); b end)
  | Constr.Unsafe.Constant c _ =>
      if Constant.equal c (e.(e_not)) then true else if Constant.equal c (e.(e_iff)) then true
      else (match FMap.find_opt c (st.(s_pc)) with
            | Some b => b
            | None => let b := pa4_arity_prop (Constr.type f) in st.(s_pc) := FMap.add c b (st.(s_pc)); b end)
  | _ => false
  end.
Ltac2 pa4_rounds := 8.
(* [comment removed for export] *)
Ltac2 pa4_analyze (all : bool) (badf : constr -> bool) : ident list * ident list * ident list * ident list * ident list :=
  let e := pa4_mk_env () in
  let st := pa4_new () in
  let hs := Control.hyps () in
  let ga := pa4_pat e st (Control.goal ()) [] in
  let gat0 := (if st.(s_na) then [] else ga) in
  (* [comment removed for export] *)
  let rec pass hs arith other :=
    match hs with
    | [] => (arith, other)
    | x :: r =>
        let (h, b, t) := x in
        match b with
        | Some _ => pass r arith other
        | None =>
            st.(s_na) := false; st.(s_dj) := false;
            let a := pa4_pat e st t [] in
            if st.(s_na) then
              (if all then
                 (match Constr.Unsafe.kind t with
                  | Constr.Unsafe.App f _ => if pa4_headp e st f then pass r arith (h :: other) else pass r arith other
                  | _ => pass r arith other
                  end)
               else pass r arith other)
            else pass r ((h, a, st.(s_dj), badf t) :: arith) other
        end
    end in
  let (arl, other) := pass hs [] [] in
  let gat := match gat0 with
             | [] => (match List.find_opt (fun (_, a, _, _) => match a with [] => false | _ => true end) arl with
                      | Some (_, a, _, _) => a | None => [] end)
             | _ => gat0 end in
  let n := st.(s_n) in
  let reached := Array.make n false in
  let isg := Array.make n false in
  let arr := Array.of_list arl in
  let na := Array.length arr in
  let kept := Array.make na false in
  let occ := Array.make n [] in
  (* [comment removed for export] *)
  let rec mkocc j := if Int.lt j 0 then () else
      (let (_, a, d, _) := Array.get arr j in
       (if d then () else List.iter (fun i => Array.set occ i (j :: Array.get occ i)) a);
       mkocc (Int.sub j 1)) in
  mkocc (Int.sub na 1);
  List.iter (fun i => Array.set reached i true; Array.set isg i true) gat;
  let rec bfs k (front : int list) :=
    if Int.equal k 0 then () else
    match front with [] => () | _ =>
      let next := List.fold_left (fun acc i =>
          List.fold_left (fun acc2 j =>
              if Array.get kept j then acc2 else
              (Array.set kept j true;
               let (_, a, _, _) := Array.get arr j in
               List.fold_left (fun acc3 x => if Array.get reached x then acc3 else (Array.set reached x true; x :: acc3)) acc2 a))
            acc (Array.get occ i)) [] front in
      bfs (Int.sub k 1) next
    end in
  bfs pa4_rounds gat;
  (* [comment removed for export] *)
  let rec coll j base disj near conn kbad :=
    if Int.lt j 0 then (base, disj, near, conn, kbad) else
    let (h, a, d, bd) := Array.get arr j in
    if d then
      (if List.exist (fun i => Array.get isg i) a then coll (Int.sub j 1) base (h :: disj) (h :: near) conn kbad
       else if List.exist (fun i => Array.get reached i) a then coll (Int.sub j 1) base (h :: disj) near (h :: conn) kbad
       else coll (Int.sub j 1) base (h :: disj) near conn kbad)
    else if (if Array.get kept j then true else List.for_all (fun i => Array.get reached i) a) then
      (if bd then coll (Int.sub j 1) base disj near conn (h :: kbad) else coll (Int.sub j 1) base disj near conn kbad)
    else coll (Int.sub j 1) (h :: base) disj near conn kbad in
  coll (Int.sub na 1) other [] [] [] [].
Ltac2 pa_analyze_v4 (all : bool) : ident list * ident list * ident list * ident list :=
  let (b, d, nr, c, _) := pa4_analyze all (fun _ => false) in (b, d, nr, c).
Ltac2 pa_minus (l : ident list) (r : ident list) : ident list := List.filter (fun h => Bool.neg (List.exist (fun k => Ident.equal k h) r)) l.
Ltac2 pa_run (clr : ident list) (tac : Ltac1.t) () := Control.once (fun () => pa_clear clr; Ltac1.run tac).
Ltac2 pa_fail () := Control.zero (Tactic_failure None).
Ltac2 rec pa_each (base : ident list) (disj : ident list) (cands : ident list) (tac : Ltac1.t) :=
  match cands with
  | [] => pa_fail ()
  | d :: r => Control.plus (pa_run (List.append base (pa_minus disj [d])) tac) (fun _ => pa_each base disj r tac)
  end.
Ltac2 pa_max_each := 8.
Ltac2 pa_gate := 40.
(* [comment removed for export] *)
Ltac2 pa_big_goal () := if Int.lt (List.length (Control.hyps ())) pa_gate then pa_fail () else ().
Ltac2 rec pa_firstn (k : int) (l : 'a list) : 'a list :=
  if Int.equal k 0 then [] else match l with [] => [] | x :: r => x :: pa_firstn (Int.sub k 1) r end.
(* [comment removed for export] *)
Ltac2 pa_tiers_gen (all : bool) (withA : bool) (tac : Ltac1.t) () :=
  (* [comment removed for export] *)
  if Constr.has_evar (Control.goal ()) then pa_fail () else
  (* [comment removed for export] *)
  if Int.lt (List.length (Control.hyps ())) pa_gate then pa_fail () else
  let (base, disj, near, conn) := pa_analyze_v4 all in
  let tierA () := pa_run (List.append base disj) tac () in
  let tierB1 () := match near with [] => pa_fail () | _ => pa_run (List.append base (pa_minus disj near)) tac () end in
  let tierB2 () := pa_each base disj (pa_firstn pa_max_each (List.append near conn)) tac in
  let b () := Control.plus tierB1 (fun _ => tierB2 ()) in
  if withA then Control.plus tierA (fun _ => b ()) else b ().
Ltac2 pa_tiers_goal (tac : Ltac1.t) () := pa_tiers_gen true true tac ().
Ltac2 pa_tierB_goal (tac : Ltac1.t) () := pa_tiers_gen true false tac ().
Ltac2 pa_msg (l : (string * int) list) : unit :=
  Message.print (List.fold_left (fun m (k, v) => Message.concat m (Message.concat (Message.of_string k) (Message.of_int v)))
                                (Message.of_string "PA") l).
Ltac2 pa_count_goal () :=
  let (base, disj, near, conn) := pa_analyze_v4 true in
  pa_msg [(" hyps=", List.length (Control.hyps ())); (" base=", List.length base); (" disj=", List.length disj);
          (" near=", List.length near); (" conn=", List.length conn)].

(* [comment removed for export] *)
Ltac pa_tiers := ltac2:(tac |- Control.enter (pa_tiers_goal tac)).
Ltac pa_tierB := ltac2:(tac |- Control.enter (pa_tierB_goal tac)).
Ltac pa_big := idtac; ltac2:(Control.enter pa_big_goal).
Ltac pa_count_dbg := idtac; ltac2:(Control.enter pa_count_goal).
(* [comment removed for export] *)
Ltac2 rec pa_concl (t : constr) : constr :=
  match Constr.Unsafe.kind t with Constr.Unsafe.Prod _ c => pa_concl c | _ => t end.
Ltac2 pa_arith_concl_goal () :=
  let e := pa_mk_env () in
  let tb := pa_new_tbl () in
  match pa_patoms e tb (pa_concl (Control.goal ())) [] with Some _ => () | None => pa_fail () end.
Ltac pa_arith_concl := idtac; ltac2:(Control.enter pa_arith_concl_goal).
