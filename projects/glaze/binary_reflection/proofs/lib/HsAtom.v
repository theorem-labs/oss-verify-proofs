(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 Type ha_env := { qk_and : inductive; qk_or : inductive; qk_eq : inductive; qk_le : inductive; qk_False : inductive;
  qk_True : inductive; qk_ex : inductive; qk_Z : inductive; qk_nat : inductive; qk_N : inductive; qk_pos : inductive; qk_bool : inductive;
  qc_iff : constant; qc_not : constant; qc_Zle : constant; qc_Zlt : constant; qc_Zge : constant; qc_Zgt : constant;
  qc_lt : constant; qc_ge : constant; qc_gt : constant;
  q_ops : constant FSet.t; q_lits : constructor FSet.t; q_succ : constructor }.
Ltac2 ha_i (r : Std.reference) : inductive := match r with Std.IndRef i => i | _ => Control.throw Not_found end.
Ltac2 ha_c (r : Std.reference) : constant := match r with Std.ConstRef c => c | _ => Control.throw Not_found end.
Ltac2 ha_k (r : Std.reference) : constructor := match r with Std.ConstructRef c => c | _ => Control.throw Not_found end.
Ltac2 ha_cset (l : constant list) : constant FSet.t := List.fold_left (fun s c => FSet.add c s) (FSet.empty FSet.Tags.constant_tag) l.
Ltac2 ha_kset (l : constructor list) : constructor FSet.t := List.fold_left (fun s c => FSet.add c s) (FSet.empty FSet.Tags.constructor_tag) l.
Ltac2 ha_mk_env () : ha_env :=
  { qk_and := ha_i reference:(and); qk_or := ha_i reference:(or); qk_eq := ha_i reference:(eq); qk_le := ha_i reference:(Peano.le);
    qk_False := ha_i reference:(False); qk_True := ha_i reference:(True); qk_ex := ha_i reference:(ex); qk_Z := ha_i reference:(Z);
    qk_nat := ha_i reference:(nat); qk_N := ha_i reference:(N); qk_pos := ha_i reference:(positive); qk_bool := ha_i reference:(bool);
    qc_iff := ha_c reference:(iff); qc_not := ha_c reference:(not); qc_Zle := ha_c reference:(Z.le); qc_Zlt := ha_c reference:(Z.lt);
    qc_Zge := ha_c reference:(Z.ge); qc_Zgt := ha_c reference:(Z.gt); qc_lt := ha_c reference:(Peano.lt);
    qc_ge := ha_c reference:(Peano.ge); qc_gt := ha_c reference:(Peano.gt);
    q_ops := ha_cset
             [ha_c reference:(Z.add); ha_c reference:(Z.sub); ha_c reference:(Z.mul); ha_c reference:(Z.opp);
              ha_c reference:(Z.pow); ha_c reference:(Z.succ); ha_c reference:(Z.pred); ha_c reference:(Z.of_nat);
              ha_c reference:(Z.to_nat); ha_c reference:(Z.div); ha_c reference:(Z.modulo); ha_c reference:(Z.max);
              ha_c reference:(Z.min); ha_c reference:(Z.abs); ha_c reference:(Z.quot); ha_c reference:(Z.rem);
              ha_c reference:(Z.eqb); ha_c reference:(Z.leb); ha_c reference:(Z.ltb); ha_c reference:(Z.geb); ha_c reference:(Z.gtb);
              ha_c reference:(Nat.add); ha_c reference:(Nat.sub); ha_c reference:(Nat.mul); ha_c reference:(Nat.pred);
              ha_c reference:(Nat.div); ha_c reference:(Nat.modulo); ha_c reference:(Nat.max); ha_c reference:(Nat.min);
              ha_c reference:(Nat.eqb); ha_c reference:(Nat.leb); ha_c reference:(Nat.ltb);
              ha_c reference:(andb); ha_c reference:(orb); ha_c reference:(negb);
              ha_c reference:(Z.of_N); ha_c reference:(Z.to_N); ha_c reference:(N.of_nat); ha_c reference:(N.to_nat);
              ha_c reference:(Z.double); ha_c reference:(Z.pos_sub)];
    q_lits := ha_kset
             [ha_k reference:(Z0); ha_k reference:(Zpos); ha_k reference:(Zneg); ha_k reference:(xI); ha_k reference:(xO);
              ha_k reference:(xH); ha_k reference:(N0); ha_k reference:(Npos); ha_k reference:(O); ha_k reference:(true);
              ha_k reference:(false)];
    q_succ := ha_k reference:(S) }.

Ltac2 Type ha_tbl := { mutable qt_vars : (ident, int) FMap.t; mutable qt_consts : (constant, int) FMap.t;
                       mutable qt_appv : (ident, (constr * int) list) FMap.t; mutable qt_apps : (constant, (constr * int) list) FMap.t;
                       mutable qt_other : (constr * int) list; mutable qt_n : int }.
Ltac2 ha_new_tbl () : ha_tbl := { qt_vars := FMap.empty FSet.Tags.ident_tag; qt_consts := FMap.empty FSet.Tags.constant_tag;
                                   qt_appv := FMap.empty FSet.Tags.ident_tag; qt_apps := FMap.empty FSet.Tags.constant_tag;
                                   qt_other := []; qt_n := 0 }.
Ltac2 rec ha_find (t : constr) (l : (constr * int) list) : int option :=
  match l with [] => None | p :: r => let (a, i) := p in if Constr.equal a t then Some i else ha_find t r end.
Ltac2 ha_fresh (tb : ha_tbl) : int := let n := tb.(qt_n) in tb.(qt_n) := Int.add n 1; n.
(* [comment removed for export] *)
Ltac2 ha_other_id (tb : ha_tbl) (t : constr) : int :=
  match ha_find t (tb.(qt_other)) with
  | Some i => i
  | None => let n := ha_fresh tb in tb.(qt_other) := (t, n) :: tb.(qt_other); n end.
Ltac2 ha_id (tb : ha_tbl) (t : constr) : int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id =>
      (match FMap.find_opt id (tb.(qt_vars)) with
       | Some i => i
       | None => let n := ha_fresh tb in tb.(qt_vars) := FMap.add id n (tb.(qt_vars)); n end)
  | Constr.Unsafe.Constant c _ =>
      (match FMap.find_opt c (tb.(qt_consts)) with
       | Some i => i
       | None => let n := ha_fresh tb in tb.(qt_consts) := FMap.add c n (tb.(qt_consts)); n end)
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind (Array.get args (Int.sub (Array.length args) 1)) with
       | Constr.Unsafe.Var v =>
           let bk := match FMap.find_opt v (tb.(qt_appv)) with Some l => l | None => [] end in
           (match ha_find t bk with
            | Some i => i
            | None => let n := ha_fresh tb in tb.(qt_appv) := FMap.add v ((t, n) :: bk) (tb.(qt_appv)); n end)
       | _ =>
           (match Constr.Unsafe.kind f with
            | Constr.Unsafe.Constant c _ =>
                let bk := match FMap.find_opt c (tb.(qt_apps)) with Some l => l | None => [] end in
                (match ha_find t bk with
                 | Some i => i
                 | None => let n := ha_fresh tb in tb.(qt_apps) := FMap.add c ((t, n) :: bk) (tb.(qt_apps)); n end)
            | _ => ha_other_id tb t
            end)
       end)
  | _ => ha_other_id tb t
  end.

(* [comment removed for export] *)
Ltac2 rec ha_tatoms (e : ha_env) (tb : ha_tbl) (t : constr) (acc : int list) : int list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant c _ =>
           if FSet.mem c (e.(q_ops)) then Array.fold_left (fun a x => ha_tatoms e tb x a) acc args
           else ha_id tb t :: acc
       | Constr.Unsafe.Constructor k _ =>
           if Constructor.equal k (e.(q_succ)) then Array.fold_left (fun a x => ha_tatoms e tb x a) acc args
           else if FSet.mem k (e.(q_lits)) then acc
           else ha_id tb t :: acc
       | _ => ha_id tb t :: acc
       end)
  | Constr.Unsafe.Constructor k _ => if FSet.mem k (e.(q_lits)) then acc else ha_id tb t :: acc
  | _ => ha_id tb t :: acc
  end.

(* [comment removed for export] *)
Ltac2 rec ha_disj (e : ha_env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Ind i _ =>
           if Ind.equal i (e.(qk_or)) then true
           else if Ind.equal i (e.(qk_and)) then (if ha_disj e (Array.get args 0) then true else ha_disj e (Array.get args 1))
           else false
       | Constr.Unsafe.Constant c _ =>
           if Constant.equal c (e.(qc_not)) then true else Constant.equal c (e.(qc_iff))
       | _ => false
       end)
  | Constr.Unsafe.Prod _ _ => true
  | _ => false
  end.

Ltac2 rec ha_arity_prop (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ c => ha_arity_prop c
  | Constr.Unsafe.Sort _ => Constr.equal t 'Prop
  | _ => false
  end.
Ltac2 ha_rounds := 8.
Ltac2 rec ha_dedup (l : int list) (acc : int list) : int list :=
  match l with [] => acc | x :: r => if List.exist (fun y => Int.equal x y) acc then ha_dedup r acc else ha_dedup r (x :: acc) end.
Ltac2 ha_clear (ids : ident list) :=
  Control.plus (fun () => Std.clear ids) (fun _ => List.iter (fun h => try (Std.clear [h])) ids).

(* [comment removed for export] *)
Ltac2 Type ha_hd := { zc : (constant, int) FMap.t; zi : (inductive, int) FMap.t; zty : inductive FSet.t }.
(* [comment removed for export] *)
Ltac2 ha_mk_hd (e : ha_env) : ha_hd :=
  let zc := List.fold_left (fun m (c, k) => FMap.add c k m) (FMap.empty FSet.Tags.constant_tag)
             [(e.(qc_Zle), 1); (e.(qc_Zlt), 1); (e.(qc_Zge), 1); (e.(qc_Zgt), 1); (e.(qc_lt), 1); (e.(qc_ge), 1); (e.(qc_gt), 1);
              (e.(qc_not), 2); (e.(qc_iff), 3)] in
  let zi := List.fold_left (fun m (c, k) => FMap.add c k m) (FMap.empty FSet.Tags.inductive_tag)
             [(e.(qk_and), 1); (e.(qk_or), 2); (e.(qk_le), 3); (e.(qk_eq), 4); (e.(qk_ex), 5); (e.(qk_False), 6); (e.(qk_True), 7)] in
  let zty := List.fold_left (fun s c => FSet.add c s) (FSet.empty FSet.Tags.inductive_tag)
             [e.(qk_Z); e.(qk_nat); e.(qk_N); e.(qk_pos); e.(qk_bool)] in
  { zc := zc; zi := zi; zty := zty }.
Ltac2 rec ha_patoms (e : ha_env) (hd : ha_hd) (tb : ha_tbl) (t : constr) (acc : int list) : int list option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Ind i _ =>
           (match FMap.find_opt i (hd.(zi)) with
            | Some k =>
                if Int.le k 2 then ha_pat2 e hd tb args acc
                else if Int.equal k 3 then Some (ha_tatoms e tb (Array.get args 1) (ha_tatoms e tb (Array.get args 0) acc))
                else if Int.equal k 4 then
                  (match Constr.Unsafe.kind (Array.get args 0) with
                   | Constr.Unsafe.Ind j _ =>
                       if FSet.mem j (hd.(zty)) then Some (ha_tatoms e tb (Array.get args 2) (ha_tatoms e tb (Array.get args 1) acc)) else None
                   | _ => None end)
                else None
            | None => None end)
       | Constr.Unsafe.Constant c _ =>
           (match FMap.find_opt c (hd.(zc)) with
            | Some k =>
                if Int.equal k 1 then Some (ha_tatoms e tb (Array.get args 1) (ha_tatoms e tb (Array.get args 0) acc))
                else if Int.equal k 2 then ha_patoms e hd tb (Array.get args 0) acc
                else ha_pat2 e hd tb args acc
            | None => None end)
       | _ => None
       end)
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then
        (match ha_patoms e hd tb (Constr.Binder.type b) acc with
         | Some a1 => ha_patoms e hd tb c a1
         | None => None end)
      else None
  | Constr.Unsafe.Ind i _ =>
      (match FMap.find_opt i (hd.(zi)) with Some k => if Int.le 6 k then Some acc else None | None => None end)
  | _ => None
  end
with ha_pat2 (e : ha_env) (hd : ha_hd) (tb : ha_tbl) (args : constr array) (acc : int list) : int list option :=
  match ha_patoms e hd tb (Array.get args 0) acc with
  | Some a1 => ha_patoms e hd tb (Array.get args 1) a1
  | None => None
  end.
(* [comment removed for export] *)
Ltac2 Type ha_hc := { mutable qc2 : (constant, bool) FMap.t; mutable qi2 : (inductive, bool) FMap.t; mutable qo2 : (constr * bool) list }.
Ltac2 ha_is_prop (hd : ha_hd) (hc : ha_hc) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Ind i _ =>
           (match FMap.find_opt i (hd.(zi)) with
            | Some k => if Int.equal k 3 then ha_arity_prop (Constr.type f) else true
            | None =>
                (match FMap.find_opt i (hc.(qi2)) with
                 | Some b => b
                 | None => let b := ha_arity_prop (Constr.type f) in hc.(qi2) := FMap.add i b (hc.(qi2)); b end) end)
       | Constr.Unsafe.Constant c _ =>
           (match FMap.find_opt c (hd.(zc)) with
            | Some k => if Int.equal k 1 then true else true
            | None =>
                (match FMap.find_opt c (hc.(qc2)) with
                 | Some b => b
                 | None => let b := ha_arity_prop (Constr.type f) in hc.(qc2) := FMap.add c b (hc.(qc2)); b end) end)
       | _ => false
       end)
  | _ => false
  end.
Ltac2 ha_analyze (all : bool) (wbad : bool) : ident list * ident list * ident list * ident list * ident list :=
  let e := ha_mk_env () in
  let ae := am_mk_env () in
  let hd := ha_mk_hd e in
  let tb := ha_new_tbl () in
  let hc := { qc2 := FMap.empty FSet.Tags.constant_tag; qi2 := FMap.empty FSet.Tags.inductive_tag; qo2 := [] } in
  let hs := Control.hyps () in
  let gat0 := match ha_patoms e hd tb (Control.goal ()) [] with Some a => ha_dedup a [] | None => [] end in
  let (arith, other) := List.fold_left (fun (ar, ot) (h, b, t) =>
        match b with
        | Some _ => (ar, ot)
        | None =>
          match ha_patoms e hd tb t [] with
          | Some a => ((h, ha_dedup a [], ha_disj e t, if wbad then am_bad ae t else false) :: ar, ot)
          | None => if all then (if ha_is_prop hd hc t then (ar, h :: ot) else (ar, ot)) else (ar, ot)
          end
        end) ([], []) hs in
  let gat := match gat0 with
             | [] => (match List.find_opt (fun (_, a, _, _) => match a with [] => false | _ => true end) arith with
                      | Some (_, a, _, _) => a | None => [] end)
             | _ => gat0 end in
  let n := tb.(qt_n) in
  let reached := Array.make n false in
  let isg := Array.make n false in
  let arr := Array.of_list arith in
  let na := Array.length arr in
  let kept := Array.make na false in
  (* [comment removed for export] *)
  let occ := Array.make n [] in
  let rec mkocc j := if Int.lt j 0 then () else
      (let (_, a, d, _) := Array.get arr j in
       (if d then () else List.iter (fun i => Array.set occ i (j :: Array.get occ i)) a);
       mkocc (Int.sub j 1)) in
  mkocc (Int.sub na 1);
  List.iter (fun i => Array.set reached i true; Array.set isg i true) gat;
  (* [comment removed for export] *)
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
  bfs ha_rounds gat;
  let rec fin j :=
    if Int.equal j na then () else
    ((if Array.get kept j then () else
        let (_, a, d, _) := Array.get arr j in
        if d then () else
        if List.for_all (fun i => Array.get reached i) a then Array.set kept j true else ());
     fin (Int.add j 1)) in
  fin 0;
  let base := Ref.ref other in
  let disj := Ref.ref [] in
  let near := Ref.ref [] in
  let conn := Ref.ref [] in
  let kbad := Ref.ref [] in
  let rec coll j :=
    if Int.lt j 0 then () else
    (let (h, a, d, bd) := Array.get arr j in
     (if d then
        (Ref.set disj (h :: Ref.get disj);
         if List.exist (fun i => Array.get isg i) a then Ref.set near (h :: Ref.get near)
         else if List.exist (fun i => Array.get reached i) a then Ref.set conn (h :: Ref.get conn) else ())
      else if Array.get kept j then (if bd then Ref.set kbad (h :: Ref.get kbad) else ()) else Ref.set base (h :: Ref.get base));
     coll (Int.sub j 1)) in
  coll (Int.sub na 1);
  (Ref.get base, Ref.get disj, Ref.get near, Ref.get conn, Ref.get kbad).

(* [comment removed for export] *)
Ltac2 Type ha4_env := { e_and : inductive; e_or : inductive; e_eq : inductive; e_le : inductive; e_False : inductive; e_True : inductive;
  e_ex : inductive; e_not : constant; e_iff : constant; e_cmp : constant FSet.t; e_ty : inductive FSet.t;
  e_ops : constant FSet.t; e_lits : constructor FSet.t; e_succ : constructor }.
Ltac2 ha4_i (r : Std.reference) : inductive := match r with Std.IndRef i => i | _ => Control.throw Not_found end.
Ltac2 ha4_c (r : Std.reference) : constant := match r with Std.ConstRef c => c | _ => Control.throw Not_found end.
Ltac2 ha4_k (r : Std.reference) : constructor := match r with Std.ConstructRef c => c | _ => Control.throw Not_found end.
Ltac2 ha4_cset (l : constant list) : constant FSet.t := List.fold_left (fun s c => FSet.add c s) (FSet.empty FSet.Tags.constant_tag) l.
Ltac2 ha4_iset (l : inductive list) : inductive FSet.t := List.fold_left (fun s c => FSet.add c s) (FSet.empty FSet.Tags.inductive_tag) l.
Ltac2 ha4_kset (l : constructor list) : constructor FSet.t := List.fold_left (fun s c => FSet.add c s) (FSet.empty FSet.Tags.constructor_tag) l.
Ltac2 ha4_mk_env () : ha4_env :=
  { e_and := ha4_i reference:(and); e_or := ha4_i reference:(or); e_eq := ha4_i reference:(eq); e_le := ha4_i reference:(Peano.le);
    e_False := ha4_i reference:(False); e_True := ha4_i reference:(True); e_ex := ha4_i reference:(ex);
    e_not := ha4_c reference:(not); e_iff := ha4_c reference:(iff);
    e_cmp := ha4_cset [ha4_c reference:(Z.le); ha4_c reference:(Z.lt); ha4_c reference:(Z.ge); ha4_c reference:(Z.gt);
                        ha4_c reference:(Peano.lt); ha4_c reference:(Peano.ge); ha4_c reference:(Peano.gt)];
    e_ty := ha4_iset [ha4_i reference:(Z); ha4_i reference:(nat); ha4_i reference:(N); ha4_i reference:(positive); ha4_i reference:(bool)];
    e_ops := ha4_cset
             [ha4_c reference:(Z.add); ha4_c reference:(Z.sub); ha4_c reference:(Z.mul); ha4_c reference:(Z.opp);
              ha4_c reference:(Z.pow); ha4_c reference:(Z.succ); ha4_c reference:(Z.pred); ha4_c reference:(Z.of_nat);
              ha4_c reference:(Z.to_nat); ha4_c reference:(Z.div); ha4_c reference:(Z.modulo); ha4_c reference:(Z.max);
              ha4_c reference:(Z.min); ha4_c reference:(Z.abs); ha4_c reference:(Z.quot); ha4_c reference:(Z.rem);
              ha4_c reference:(Z.eqb); ha4_c reference:(Z.leb); ha4_c reference:(Z.ltb); ha4_c reference:(Z.geb); ha4_c reference:(Z.gtb);
              ha4_c reference:(Nat.add); ha4_c reference:(Nat.sub); ha4_c reference:(Nat.mul); ha4_c reference:(Nat.pred);
              ha4_c reference:(Nat.div); ha4_c reference:(Nat.modulo); ha4_c reference:(Nat.max); ha4_c reference:(Nat.min);
              ha4_c reference:(Nat.eqb); ha4_c reference:(Nat.leb); ha4_c reference:(Nat.ltb);
              ha4_c reference:(andb); ha4_c reference:(orb); ha4_c reference:(negb);
              ha4_c reference:(Z.of_N); ha4_c reference:(Z.to_N); ha4_c reference:(N.of_nat); ha4_c reference:(N.to_nat);
              ha4_c reference:(Z.double); ha4_c reference:(Z.pos_sub)];
    e_lits := ha4_kset
             [ha4_k reference:(Z0); ha4_k reference:(Zpos); ha4_k reference:(Zneg); ha4_k reference:(xI); ha4_k reference:(xO);
              ha4_k reference:(xH); ha4_k reference:(N0); ha4_k reference:(Npos); ha4_k reference:(O); ha4_k reference:(true);
              ha4_k reference:(false)];
    e_succ := ha4_k reference:(S) }.
(* [comment removed for export] *)
Ltac2 Type ha4_st := {
  mutable s_vars : (ident, int) FMap.t; mutable s_consts : (constant, int) FMap.t; mutable s_appv : (ident, (constr * int) list) FMap.t;
  mutable s_apps : (constant, (constr * int) list) FMap.t; mutable s_other : (constr * int) list; mutable s_n : int;
  mutable s_pc : (constant, bool) FMap.t; mutable s_pi : (inductive, bool) FMap.t;
  mutable s_dj : bool; mutable s_na : bool }.
Ltac2 ha4_new () : ha4_st :=
  { s_vars := FMap.empty FSet.Tags.ident_tag; s_consts := FMap.empty FSet.Tags.constant_tag;
    s_appv := FMap.empty FSet.Tags.ident_tag; s_apps := FMap.empty FSet.Tags.constant_tag; s_other := []; s_n := 0;
    s_pc := FMap.empty FSet.Tags.constant_tag; s_pi := FMap.empty FSet.Tags.inductive_tag; s_dj := false; s_na := false }.
Ltac2 rec ha4_find (t : constr) (l : (constr * int) list) : int :=
  match l with [] => -1 | p :: r => let (a, i) := p in if Constr.equal a t then i else ha4_find t r end.
Ltac2 ha4_fresh (st : ha4_st) : int := let n := st.(s_n) in st.(s_n) := Int.add n 1; n.
Ltac2 ha4_other_id (st : ha4_st) (t : constr) : int :=
  let i := ha4_find t (st.(s_other)) in
  if Int.le 0 i then i else let n := ha4_fresh st in st.(s_other) := (t, n) :: st.(s_other); n.
(* [comment removed for export] *)
Ltac2 ha4_app_id (st : ha4_st) (t : constr) (f : constr) (args : constr array) : int :=
  match Constr.Unsafe.kind (Array.get args (Int.sub (Array.length args) 1)) with
  | Constr.Unsafe.Var v =>
      let bk := match FMap.find_opt v (st.(s_appv)) with Some l => l | None => [] end in
      let i := ha4_find t bk in
      if Int.le 0 i then i else let n := ha4_fresh st in st.(s_appv) := FMap.add v ((t, n) :: bk) (st.(s_appv)); n
  | _ =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constant c _ =>
          let bk := match FMap.find_opt c (st.(s_apps)) with Some l => l | None => [] end in
          let i := ha4_find t bk in
          if Int.le 0 i then i else let n := ha4_fresh st in st.(s_apps) := FMap.add c ((t, n) :: bk) (st.(s_apps)); n
      | _ => ha4_other_id st t
      end
  end.
Ltac2 ha4_leaf_id (st : ha4_st) (t : constr) : int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id =>
      (match FMap.find_opt id (st.(s_vars)) with
       | Some i => i
       | None => let n := ha4_fresh st in st.(s_vars) := FMap.add id n (st.(s_vars)); n end)
  | Constr.Unsafe.Constant c _ =>
      (match FMap.find_opt c (st.(s_consts)) with
       | Some i => i
       | None => let n := ha4_fresh st in st.(s_consts) := FMap.add c n (st.(s_consts)); n end)
  | _ => ha4_other_id st t
  end.
(* [comment removed for export] *)
Ltac2 rec ha4_tat (e : ha4_env) (st : ha4_st) (t : constr) (acc : int list) : int list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant c _ =>
           if FSet.mem c (e.(e_ops)) then ha4_targs e st args 0 (Array.length args) acc
           else ha4_app_id st t f args :: acc
       | Constr.Unsafe.Constructor k _ =>
           if FSet.mem k (e.(e_lits)) then acc
           else if Constructor.equal k (e.(e_succ)) then ha4_tat e st (Array.get args 0) acc
           else ha4_app_id st t f args :: acc
       | _ => ha4_app_id st t f args :: acc
       end)
  | Constr.Unsafe.Constructor k _ => if FSet.mem k (e.(e_lits)) then acc else ha4_leaf_id st t :: acc
  | _ => ha4_leaf_id st t :: acc
  end
with ha4_targs (e : ha4_env) (st : ha4_st) (args : constr array) (i : int) (n : int) (acc : int list) : int list :=
  if Int.equal i n then acc else ha4_targs e st args (Int.add i 1) n (ha4_tat e st (Array.get args i) acc).
(* [comment removed for export] *)
Ltac2 rec ha4_pat (e : ha4_env) (st : ha4_st) (t : constr) (acc : int list) : int list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Ind i _ =>
           if Ind.equal i (e.(e_and)) then ha4_pat e st (Array.get args 1) (ha4_pat e st (Array.get args 0) acc)
           else if Ind.equal i (e.(e_eq)) then
             (match Constr.Unsafe.kind (Array.get args 0) with
              | Constr.Unsafe.Ind j _ =>
                  if FSet.mem j (e.(e_ty)) then ha4_tat e st (Array.get args 2) (ha4_tat e st (Array.get args 1) acc)
                  else (st.(s_na) := true; acc)
              | _ => st.(s_na) := true; acc end)
           else if Ind.equal i (e.(e_or)) then (st.(s_dj) := true; ha4_pat e st (Array.get args 1) (ha4_pat e st (Array.get args 0) acc))
           else if Ind.equal i (e.(e_le)) then ha4_tat e st (Array.get args 1) (ha4_tat e st (Array.get args 0) acc)
           else (st.(s_na) := true; acc)
       | Constr.Unsafe.Constant c _ =>
           if FSet.mem c (e.(e_cmp)) then ha4_tat e st (Array.get args 1) (ha4_tat e st (Array.get args 0) acc)
           else if Constant.equal c (e.(e_not)) then (st.(s_dj) := true; ha4_pat e st (Array.get args 0) acc)
           else if Constant.equal c (e.(e_iff)) then (st.(s_dj) := true; ha4_pat e st (Array.get args 1) (ha4_pat e st (Array.get args 0) acc))
           else (st.(s_na) := true; acc)
       | _ => st.(s_na) := true; acc
       end)
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then (st.(s_dj) := true; ha4_pat e st c (ha4_pat e st (Constr.Binder.type b) acc))
      else (st.(s_na) := true; acc)
  | Constr.Unsafe.Ind i _ => if Ind.equal i (e.(e_False)) then acc else if Ind.equal i (e.(e_True)) then acc else (st.(s_na) := true; acc)
  | _ => st.(s_na) := true; acc
  end.
Ltac2 rec ha4_arity_prop (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ c => ha4_arity_prop c
  | Constr.Unsafe.Sort _ => Constr.equal t 'Prop
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 ha4_headp (e : ha4_env) (st : ha4_st) (f : constr) : bool :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Ind i _ =>
      if Ind.equal i (e.(e_eq)) then true else if Ind.equal i (e.(e_and)) then true else if Ind.equal i (e.(e_or)) then true
      else if Ind.equal i (e.(e_ex)) then true
      else (match FMap.find_opt i (st.(s_pi)) with
            | Some b => b
            | None => let b := ha4_arity_prop (Constr.type f) in st.(s_pi) := FMap.add i b (st.(s_pi)); b end)
  | Constr.Unsafe.Constant c _ =>
      if Constant.equal c (e.(e_not)) then true else if Constant.equal c (e.(e_iff)) then true
      else (match FMap.find_opt c (st.(s_pc)) with
            | Some b => b
            | None => let b := ha4_arity_prop (Constr.type f) in st.(s_pc) := FMap.add c b (st.(s_pc)); b end)
  | _ => false
  end.
Ltac2 ha4_rounds := 8.
(* [comment removed for export] *)
Ltac2 ha4_analyze (all : bool) (badf : constr -> bool) : ident list * ident list * ident list * ident list * ident list :=
  let e := ha4_mk_env () in
  let st := ha4_new () in
  let hs := Control.hyps () in
  let ga := ha4_pat e st (Control.goal ()) [] in
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
            let a := ha4_pat e st t [] in
            if st.(s_na) then
              (if all then
                 (match Constr.Unsafe.kind t with
                  | Constr.Unsafe.App f _ => if ha4_headp e st f then pass r arith (h :: other) else pass r arith other
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
  bfs ha4_rounds gat;
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
Ltac2 ha_analyze_v4 (all : bool) (wbad : bool) : ident list * ident list * ident list * ident list * ident list :=
  if wbad then (let ae := am_mk_env () in ha4_analyze all (fun t => am_bad ae t)) else ha4_analyze all (fun _ => false).
Ltac2 ha_minus (l : ident list) (r : ident list) : ident list := List.filter (fun h => Bool.neg (List.exist (fun k => Ident.equal k h) r)) l.
Ltac2 ha_run (clr : ident list) (tac : Ltac1.t) () := Control.once (fun () => ha_clear clr; Ltac1.run tac).
Ltac2 ha_fail () := Control.zero (Tactic_failure None).
Ltac2 rec ha_each (base : ident list) (disj : ident list) (cands : ident list) (tac : Ltac1.t) :=
  match cands with
  | [] => ha_fail ()
  | d :: r => Control.plus (ha_run (List.append base (ha_minus disj [d])) tac) (fun _ => ha_each base disj r tac)
  end.
Ltac2 ha_gate := 40.
Ltac2 rec ha_firstn (k : int) (l : 'a list) : 'a list :=
  if Int.equal k 0 then [] else match l with [] => [] | x :: r => x :: ha_firstn (Int.sub k 1) r end.
(* [comment removed for export] *)
Ltac ha_flag_on := lazymatch Zify.zify_convert_to_euclidean_division_equations_flag with true => idtac | _ => fail end.
Ltac2 ha_divflag () : bool := match Control.case (fun () => ltac1:(ha_flag_on)) with Val _ => true | Err _ => false end.
Ltac2 ha_tiers_gen (mx : int) (tac : Ltac1.t) () :=
  if Constr.has_evar (Control.goal ()) then ha_fail () else
  if Int.lt (List.length (Control.hyps ())) ha_gate then ha_fail () else
  let dv := ha_divflag () in
  let (base, disj, near, conn, kbad) := ha_analyze_v4 true dv in
  let tierA () := ha_run (List.append base disj) tac () in
  let tierA0 () := match kbad with
                   | [] => tierA ()
                   | _ => if am_goal_bad (am_mk_env ()) (Control.goal ()) then tierA ()
                          else Control.plus (ha_run (List.append kbad (List.append base disj)) tac) (fun _ => tierA ()) end in
  let tierB1 () := match near with [] => ha_fail () | _ => ha_run (List.append base (ha_minus disj near)) tac () end in
  let tierB2 () := ha_each base disj (ha_firstn mx (List.append near conn)) tac in
  Control.plus tierA0 (fun _ => Control.plus tierB1 (fun _ => tierB2 ())).
Ltac2 ha_max_each := 3.
Ltac2 ha_tiers_goal (tac : Ltac1.t) () := ha_tiers_gen ha_max_each tac ().

(* [comment removed for export] *)
Ltac ha_lia0 := Zify.zify; xlia zchecker.
Ltac ha_tiers := ltac2:(tac |- Control.enter (ha_tiers_goal tac)).
Ltac2 ha_first_goal () := Control.plus (fun () => Control.once (ha_tiers_goal ltac1val:(ha_lia0))) (fun _ => ltac1:(am_lia)).
Ltac ha_first_lia := idtac; ltac2:(Control.enter ha_first_goal).
