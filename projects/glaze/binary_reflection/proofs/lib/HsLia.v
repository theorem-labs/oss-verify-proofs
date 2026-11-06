(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 Type hs_env := { hk_and : inductive; hk_or : inductive; hk_eq : inductive; hk_le : inductive; hk_False : inductive;
                       hk_True : inductive; hk_ex : inductive; hk_Z : inductive; hk_nat : inductive; hk_N : inductive; hk_pos : inductive;
                       hc_Zle : constant; hc_Zlt : constant; hc_Zge : constant; hc_Zgt : constant; hc_not : constant;
                       hc_iff : constant; hc_lt : constant; hc_ge : constant; hc_gt : constant }.
Ltac2 hs_i (r : Std.reference) : inductive := match r with Std.IndRef i => i | _ => Control.throw Not_found end.
Ltac2 hs_c (r : Std.reference) : constant := match r with Std.ConstRef c => c | _ => Control.throw Not_found end.
Ltac2 hs_mk_env () : hs_env :=
  { hk_and := hs_i reference:(and); hk_or := hs_i reference:(or); hk_eq := hs_i reference:(eq); hk_le := hs_i reference:(le);
    hk_False := hs_i reference:(False); hk_True := hs_i reference:(True); hk_ex := hs_i reference:(ex); hk_Z := hs_i reference:(Z); hk_nat := hs_i reference:(nat); hk_N := hs_i reference:(N); hk_pos := hs_i reference:(positive);
    hc_Zle := hs_c reference:(Z.le); hc_Zlt := hs_c reference:(Z.lt); hc_Zge := hs_c reference:(Z.ge); hc_Zgt := hs_c reference:(Z.gt);
    hc_not := hs_c reference:(not); hc_iff := hs_c reference:(iff); hc_lt := hs_c reference:(lt); hc_ge := hs_c reference:(ge);
    hc_gt := hs_c reference:(gt) }.

(* [comment removed for export] *)
Ltac2 rec hs_propish (e : hs_env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Ind i _ =>
           if Ind.equal i (e.(hk_and)) then true else if Ind.equal i (e.(hk_or)) then true
           else if Ind.equal i (e.(hk_eq)) then true else if Ind.equal i (e.(hk_le)) then true
           else Ind.equal i (e.(hk_ex))
       | Constr.Unsafe.Constant c _ =>
           if Constant.equal c (e.(hc_Zle)) then true else if Constant.equal c (e.(hc_Zlt)) then true
           else if Constant.equal c (e.(hc_Zge)) then true else if Constant.equal c (e.(hc_Zgt)) then true
           else if Constant.equal c (e.(hc_not)) then true else if Constant.equal c (e.(hc_iff)) then true
           else if Constant.equal c (e.(hc_lt)) then true else if Constant.equal c (e.(hc_ge)) then true
           else Constant.equal c (e.(hc_gt))
       | _ => false
       end)
  | Constr.Unsafe.Prod _ c => hs_propish e c
  | Constr.Unsafe.Ind i _ => if Ind.equal i (e.(hk_False)) then true else Ind.equal i (e.(hk_True))
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 hs_touch (vl : ident list) (n : int) (t : constr) : bool :=
  Bool.neg (Constr.Unsafe.noccur_between 1 n (Constr.Unsafe.closenl vl 1 t)).

Ltac2 hs_clear (ids : ident list) :=
  Control.plus (fun () => Std.clear ids) (fun _ => List.iter (fun h => try (Std.clear [h])) ids).

Ltac2 hs_rare := 3.
Ltac2 hs_gate := 60.
(* [comment removed for export] *)
Ltac2 hs_junk_eq (e : hs_env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Ind i _ =>
           if Ind.equal i (e.(hk_eq)) then
             (match Constr.Unsafe.kind (Array.get args 0) with
              | Constr.Unsafe.Ind j _ =>
                  if Ind.equal j (e.(hk_Z)) then false else if Ind.equal j (e.(hk_nat)) then false
                  else if Ind.equal j (e.(hk_N)) then false else Bool.neg (Ind.equal j (e.(hk_pos)))
              | _ => true end)
           else false
       | _ => false end)
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 hs_rel_goal_gen (need_bad : bool) () :=
  let e := hs_mk_env () in
  let g := Control.goal () in
  (* [comment removed for export] *)
  if Bool.neg (hs_propish e g) then Control.zero (Tactic_failure None) else
  if hs_junk_eq e g then Control.zero (Tactic_failure None) else
  let hs := Control.hyps () in
  (* [comment removed for export] *)
  if Int.lt (List.length hs) hs_gate then Control.zero (Tactic_failure None) else
  (* [comment removed for export] *)
  let props0 := List.map_filter (fun (h, b, t) => match b with
                  | Some _ => None
                  | None => if hs_propish e t then Some (h, t) else None end) hs in
  let props := List.filter (fun (_, t) => Bool.neg (hs_junk_eq e t)) props0 in
  let tvs := List.map_filter (fun (h, b, t) => match b with
                  | Some _ => Some h
                  | None => if hs_propish e t then None else Some h end) hs in
  let gvl := List.filter (fun v => hs_touch [v] 1 g) tvs in
  (match gvl with [] => Control.zero (Tactic_failure None) | _ => () end);
  let ng := List.length gvl in
  let touched := List.filter (fun (_, t) => hs_touch gvl ng t) props in
  let extra := List.fold_left (fun acc v =>
      let occ := List.filter (fun (_, t) => hs_touch [v] 1 t) touched in
      if Int.le (List.length occ) hs_rare then
        (match occ with
         | [] => acc
         | _ =>
           let big := Constr.Unsafe.make (Constr.Unsafe.App 'I (Array.of_list (List.map (fun (_, t) => t) occ))) in
           List.append (List.filter (fun w => if List.mem Ident.equal w gvl then false
                                              else if List.mem Ident.equal w acc then false
                                              else hs_touch [w] 1 big) tvs) acc
         end)
      else acc) [] gvl in
  let vl := List.append gvl extra in
  let m := List.length vl in
  (* [comment removed for export] *)
  let keep := List.map_filter (fun (h, t) => if Int.equal m 0 then None
                                             else if hs_touch vl m t then Some (h, t) else None) props in
  (if need_bad then
     (let ae := am_mk_env () in
      if List.exist (fun (_, t) => am_bad ae t) keep then () else Control.zero (Tactic_failure None))
   else ());
  (* [comment removed for export] *)
  let terms := List.append (List.map (fun (_, t) => t) keep) [g] in
  let round (known : ident list) (ts : constr list) :=
    let big := Constr.Unsafe.make (Constr.Unsafe.App 'I (Array.of_list ts)) in
    List.append (List.filter (fun w => if List.mem Ident.equal w known then false else hs_touch [w] 1 big) tvs) known in
  let k1 := round vl terms in
  let defs := List.flat_map (fun (h, b, t) => if List.mem Ident.equal h k1 then (match b with Some c => [c; t] | None => [t] end) else []) hs in
  let k2 := match defs with [] => k1 | _ => round k1 defs end in
  let defs2 := List.flat_map (fun (h, b, t) => if List.mem Ident.equal h k2 then (match b with Some c => [c; t] | None => [t] end) else []) hs in
  let k3 := match defs2 with [] => k2 | _ => round k2 defs2 end in
  let kept := List.append (List.map (fun (h, _) => h) keep) k3 in
  hs_clear (List.map_filter (fun (h, _, _) => if List.mem Ident.equal h kept then None else Some h) hs).

Ltac2 hs_rel_goal () := hs_rel_goal_gen false ().
Ltac hs_rel := idtac; ltac2:(Control.enter hs_rel_goal).
Ltac hs_lia0 := Zify.zify; xlia zchecker.
Ltac hs_lia := first [ solve [ hs_rel; hs_lia0 ] | lia ].

(* [comment removed for export] *)
Ltac hs_inner := am_inner.
Ltac2 hs_am_goal () :=
  let hs := Control.hyps () in
  if Int.lt (List.length hs) am_gate then ltac1:(hs_inner) else
  let e := am_mk_env () in
  let tier2 nb := Control.plus (fun () => Control.once (fun () => hs_rel_goal_gen nb (); ltac1:(hs_lia0))) (fun _ => ltac1:(hs_inner)) in
  if am_goal_bad e (Control.goal ()) then tier2 false else
  let bad := List.filter (fun (_, b, t) => match b with Some _ => false | None => am_bad e t end) hs in
  match bad with
  | [] => tier2 false
  | _ => Control.plus (fun () => Control.once (fun () => am_clear (List.map (fun (h, _, _) => h) bad); ltac1:(hs_inner)))
                      (fun _ => tier2 true)
  end.
Ltac hs_am_lia := idtac; ltac2:(Control.enter hs_am_goal).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hs_assum := match goal with H : ?G |- ?G' => constr_eq G G'; exact H end.
(* [comment removed for export] *)
Ltac hs_arith_goal := lazymatch goal with
  | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- (_ <= _)%nat => idtac | |- (_ < _)%nat => idtac
  | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac | |- False => idtac | |- _ <-> _ => idtac
  end.
