(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 Type am_head := [ AHother | AHand | AHor | AHeq | AHFalse | AHTrue | AHle | AHiff | AHnot | AHcmp ].
Ltac2 Type am_env := { k_and : inductive; k_or : inductive; k_eq : inductive; k_le : inductive; k_False : inductive;
  k_True : inductive; k_Z : inductive; k_nat : inductive; c_iff : constant; c_not : constant; c_Zle : constant; c_Zlt : constant;
  c_Zge : constant; c_Zgt : constant; c_lt : constant; c_mod : constant; c_div : constant; c_max : constant; c_min : constant;
  c_quot : constant; c_rem : constant;
  m_hi : (inductive, am_head) FMap.t; m_hc : (constant, am_head) FMap.t; m_badop : constant FSet.t }.
Ltac2 am_i (r : Std.reference) : inductive := match r with Std.IndRef i => i | _ => Control.throw Not_found end.
Ltac2 am_c (r : Std.reference) : constant := match r with Std.ConstRef c => c | _ => Control.throw Not_found end.
Ltac2 am_mk_env () : am_env :=
  { k_and := am_i reference:(and); k_or := am_i reference:(or); k_eq := am_i reference:(eq); k_le := am_i reference:(Peano.le);
    k_False := am_i reference:(False); k_True := am_i reference:(True); k_Z := am_i reference:(Z); k_nat := am_i reference:(nat);
    c_iff := am_c reference:(iff); c_not := am_c reference:(not); c_Zle := am_c reference:(Z.le); c_Zlt := am_c reference:(Z.lt);
    c_Zge := am_c reference:(Z.ge); c_Zgt := am_c reference:(Z.gt); c_lt := am_c reference:(Peano.lt);
    c_mod := am_c reference:(Z.modulo); c_div := am_c reference:(Z.div); c_max := am_c reference:(Z.max);
    c_min := am_c reference:(Z.min); c_quot := am_c reference:(Z.quot); c_rem := am_c reference:(Z.rem);
    m_hi := List.fold_left (fun m (i, k) => FMap.add i k m) (FMap.empty FSet.Tags.inductive_tag)
              [(am_i reference:(and), AHand); (am_i reference:(or), AHor); (am_i reference:(eq), AHeq); (am_i reference:(Peano.le), AHle);
               (am_i reference:(False), AHFalse); (am_i reference:(True), AHTrue)];
    m_hc := List.fold_left (fun m (c, k) => FMap.add c k m) (FMap.empty FSet.Tags.constant_tag)
              [(am_c reference:(Z.le), AHcmp); (am_c reference:(Z.lt), AHcmp); (am_c reference:(not), AHnot); (am_c reference:(iff), AHiff);
               (am_c reference:(Z.ge), AHcmp); (am_c reference:(Z.gt), AHcmp); (am_c reference:(Peano.lt), AHcmp)];
    m_badop := List.fold_left (fun m c => FSet.add c m) (FSet.empty FSet.Tags.constant_tag)
              [am_c reference:(Z.modulo); am_c reference:(Z.div); am_c reference:(Z.max); am_c reference:(Z.min);
               am_c reference:(Z.quot); am_c reference:(Z.rem)] }.

(* [comment removed for export] *)
Ltac2 am_head_of (e : am_env) (f : constr) : am_head :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Ind i _ => (match FMap.find_opt i (e.(m_hi)) with Some k => k | None => AHother end)
  | Constr.Unsafe.Constant c _ => (match FMap.find_opt c (e.(m_hc)) with Some k => k | None => AHother end)
  | _ => AHother
  end.
Ltac2 am_code (k : am_head) : int :=
  match k with
  | AHother => 0 | AHand => 1 | AHor => 2 | AHeq => 3 | AHFalse => 4 | AHTrue => 5 | AHle => 8 | AHiff => 10 | AHnot => 11 | AHcmp => 12
  end.
Ltac2 am_pcode (e : am_env) (f : constr) : int := am_code (am_head_of e f).
Ltac2 am_in (x : int) (lo : int) (hi : int) : bool := if Int.lt x lo then false else Bool.neg (Int.lt hi x).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec am_arith_bad (e : am_env) (d : int) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant c _ =>
           if FSet.mem c (e.(m_badop)) then true
           else if Int.equal d 0 then false else am_arith_bad_args e (Int.sub d 1) args 0 (Array.length args)
       | _ => false
       end)
  | _ => false
  end
with am_arith_bad_args (e : am_env) (d : int) (args : constr array) (i : int) (n : int) : bool :=
  if Int.equal i n then false else if am_arith_bad e d (Array.get args i) then true else am_arith_bad_args e d args (Int.add i 1) n.
Ltac2 am_depth := 4.
(* [comment removed for export] *)
Ltac2 am_cmp_bad (e : am_env) (k : int) (args : constr array) : bool :=
  if Int.equal k 3 then
    (match Constr.Unsafe.kind (Array.get args 0) with
     | Constr.Unsafe.Ind i _ =>
         if Ind.equal i (e.(k_Z)) then (if am_arith_bad e am_depth (Array.get args 1) then true else am_arith_bad e am_depth (Array.get args 2))
         else if Ind.equal i (e.(k_nat)) then (if am_arith_bad e am_depth (Array.get args 1) then true else am_arith_bad e am_depth (Array.get args 2))
         else false
     | _ => false end)
  else am_arith_bad_args e am_depth args 0 (Array.length args).
(* [comment removed for export] *)
Ltac2 am_eq_bad (e : am_env) (args : constr array) : bool :=
  match Constr.Unsafe.kind (Array.get args 0) with
  | Constr.Unsafe.Ind i _ =>
      if Ind.equal i (e.(k_Z)) then (if am_arith_bad e am_depth (Array.get args 1) then true else am_arith_bad e am_depth (Array.get args 2))
      else if Ind.equal i (e.(k_nat)) then (if am_arith_bad e am_depth (Array.get args 1) then true else am_arith_bad e am_depth (Array.get args 2))
      else false
  | _ => false
  end.
Ltac2 am_ord_bad (e : am_env) (args : constr array) : bool := am_arith_bad_args e am_depth args 0 (Array.length args).
(* [comment removed for export] *)
Ltac2 am_is_propish (e : am_env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => (match am_head_of e f with AHother => false | _ => true end)
  | Constr.Unsafe.Ind i _ => if Ind.equal i (e.(k_False)) then true else Ind.equal i (e.(k_True))
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 am_neg_bad (e : am_env) (a : constr) : bool :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.App g _ =>
      (match am_head_of e g with AHand => true | AHor => true | AHeq => true | AHiff => true | AHnot => true | _ => false end)
  | Constr.Unsafe.Prod _ _ => true
  | _ => false
  end.
Ltac2 rec am_bad (e : am_env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match am_head_of e f with
       | AHother => false
       | AHand => if am_bad e (Array.get args 0) then true else am_bad e (Array.get args 1)
       | AHor => true
       | AHiff => true
       | AHnot => am_neg_bad e (Array.get args 0)
       | AHeq => am_eq_bad e args
       | AHle => am_ord_bad e args
       | AHcmp => am_ord_bad e args
       | AHFalse => false
       | AHTrue => false
       end)
  | Constr.Unsafe.Prod _ c => if Constr.Unsafe.noccurn 1 c then am_is_propish e c else false
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec am_goal_bad (e : am_env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match am_head_of e f with
       | AHand => if am_goal_bad e (Array.get args 0) then true else am_goal_bad e (Array.get args 1)
       | AHor => if am_goal_bad e (Array.get args 0) then true else am_goal_bad e (Array.get args 1)
       | AHiff => if am_goal_bad e (Array.get args 0) then true else am_goal_bad e (Array.get args 1)
       | AHnot => am_goal_bad e (Array.get args 0)
       | AHeq => am_eq_bad e args
       | AHle => am_ord_bad e args
       | AHcmp => am_ord_bad e args
       | _ => false
       end)
  | Constr.Unsafe.Prod b c => if Constr.Unsafe.noccurn 1 c then (if am_goal_bad e (Constr.Binder.type b) then true else am_goal_bad e c) else false
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 am_gate := 30.
Ltac2 am_clear (ids : ident list) :=
  Control.plus (fun () => Std.clear ids) (fun _ => List.iter (fun h => try (Std.clear [h])) ids).

(* [comment removed for export] *)
Ltac am_lia0 := Zify.zify; xlia zchecker.
(* [comment removed for export] *)
Ltac am_inner := am_lia0.
Ltac2 am_lia_goal () :=
  let hs := Control.hyps () in
  if Int.lt (List.length hs) am_gate then ltac1:(am_inner) else
  let e := am_mk_env () in
  if am_goal_bad e (Control.goal ()) then ltac1:(am_inner) else
  let bad := List.filter (fun (_, b, t) => match b with Some _ => false | None => am_bad e t end) hs in
  match bad with
  | [] => ltac1:(am_inner)
  | _ => Control.plus (fun () => Control.once (fun () => am_clear (List.map (fun (h, _, _) => h) bad); ltac1:(am_inner)))
                      (fun _ => ltac1:(am_inner))
  end.

(* [comment removed for export] *)
Ltac2 rec am_mem (x : constr) (l : constr list) : bool :=
  match l with [] => false | y :: r => if Constr.equal x y then true else am_mem x r end.
Ltac2 am_add (t : constr) (acc : constr list) : constr list := if am_mem t acc then acc else t :: acc.
Ltac2 rec am_patoms (e : am_env) (t : constr) (acc : constr list) : constr list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      let k := am_pcode e f in
      if am_in k 1 2 then am_patoms e (Array.get args 1) (am_patoms e (Array.get args 0) acc)
      else if Int.equal k 10 then am_patoms e (Array.get args 1) (am_patoms e (Array.get args 0) acc)
      else if Int.equal k 11 then am_patoms e (Array.get args 0) acc
      else am_add t acc
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then am_patoms e c (am_patoms e (Constr.Binder.type b) acc) else am_add t acc
  | Constr.Unsafe.Ind i _ => if Ind.equal i (e.(k_False)) then acc else if Ind.equal i (e.(k_True)) then acc else am_add t acc
  | _ => am_add t acc
  end.
Ltac2 rec am_shares (l : constr list) (g : constr list) : bool :=
  match l with [] => false | x :: r => if am_mem x g then true else am_shares r g end.
Ltac2 rec am_union (l : constr list) (g : constr list) : constr list :=
  match l with [] => g | x :: r => am_union r (am_add x g) end.
(* [comment removed for export] *)
Ltac2 rec am_close (seeds : constr list) (cands : (ident * constr list) list) (kept : ident list) : ident list :=
  let (inn, out) := List.partition (fun (_, a) => am_shares a seeds) cands in
  match inn with
  | [] => kept
  | _ => am_close (List.fold_left (fun s (_, a) => am_union a s) seeds inn) out
                  (List.append (List.map (fun (h, _) => h) inn) kept)
  end.
(* [comment removed for export] *)
Ltac2 rec am_newest_prop_atoms (e : am_env) (rhs : (ident * constr option * constr) list) : constr list :=
  match rhs with
  | [] => []
  | (_, b, t) :: r =>
      match b with
      | Some _ => am_newest_prop_atoms e r
      | None => if am_is_propish e t then am_patoms e t []
                else if Constr.equal (Constr.type t) 'Prop then am_patoms e t [] else am_newest_prop_atoms e r
      end
  end.
Ltac2 am_tauto_goal () :=
  let hs := Control.hyps () in
  if Int.lt (List.length hs) am_gate then ltac1:(tauto) else
  let e := am_mk_env () in
  let props := List.filter (fun (_, b, t) => match b with Some _ => false | None => am_is_propish e t end) hs in
  let seeds0 := am_patoms e (Control.goal ()) [] in
  let seeds := match seeds0 with
               | [] => am_newest_prop_atoms e (List.rev hs)
               | _ => seeds0 end in
  match seeds with [] => ltac1:(tauto) | _ =>
    let kept := am_close seeds (List.map (fun (h, _, t) => (h, am_patoms e t [])) props) [] in
    let drop := List.filter (fun (h, _, _) => Bool.neg (List.exist (fun k => Ident.equal k h) kept)) props in
    match kept with [] => ltac1:(tauto) | _ =>     (* [comment removed for export] *)
    match drop with
    | [] => ltac1:(tauto)
    | _ => Control.plus (fun () => Control.once (fun () => am_clear (List.map (fun (h, _, _) => h) drop); ltac1:(tauto)))
                        (fun _ => ltac1:(tauto))
    end end
  end.

(* [comment removed for export] *)
Ltac2 Type am_wmc_env := { w_or : inductive; w_and : inductive; w_iff : constant }.
Ltac2 am_wmc_mk () : am_wmc_env := { w_or := am_i reference:(or); w_and := am_i reference:(and); w_iff := am_c reference:(iff) }.
(* [comment removed for export] *)
Ltac2 rec am_has_or (e : am_wmc_env) (both : bool) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Ind i _ =>
           if Ind.equal i (e.(w_or)) then true
           else if Ind.equal i (e.(w_and)) then (if am_has_or e both (Array.get args 0) then true else am_has_or e both (Array.get args 1))
           else false
       | Constr.Unsafe.Constant c _ =>
           if Constant.equal c (e.(w_iff)) then (if am_has_or e both (Array.get args 0) then true else am_has_or e both (Array.get args 1))
           else false
       | _ => false
       end)
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then
        (if both then (if am_has_or e both (Constr.Binder.type b) then true else am_has_or e both c) else am_has_or e both c)
      else false
  | _ => false
  end.
Ltac2 rec am_wmc_slow (e : am_wmc_env) (both : bool) () : unit :=
  let cands := List.fold_left (fun acc (h, _, t) => if am_has_or e both t then h :: acc else acc) [] (Control.hyps ()) in
  let prog := List.fold_left (fun p h => match Control.case (fun () => Std.clear [h]) with Val _ => true | Err _ => p end) false cands in
  if prog then am_wmc_slow e both () else ().
Ltac2 am_wmc_clear (both : bool) () : unit :=
  let e := am_wmc_mk () in
  let cands := List.fold_left (fun acc (h, _, t) => if am_has_or e both t then h :: acc else acc) [] (Control.hyps ()) in
  match cands with
  | [] => ()
  | _ => Control.once (fun () => Control.plus (fun () => Std.clear cands) (fun _ => am_wmc_slow e both ()))
  end.
Ltac am_wm_clear_disj := ltac2:(Control.enter (am_wmc_clear true)).
Ltac am_wc_clear_disj := ltac2:(Control.enter (am_wmc_clear false)).

(* [comment removed for export] *)
Ltac am_lia := idtac; ltac2:(Control.enter am_lia_goal).
Ltac am_tauto := idtac; ltac2:(Control.enter am_tauto_goal).
