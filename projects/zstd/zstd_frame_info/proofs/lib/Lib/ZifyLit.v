(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Env Ind.
Unset Lia Cache.
Unset Nia Cache.
Set Default Proof Mode "Classic".

Ltac2 zl_kof (r : Std.reference) : constant :=
  match r with Std.ConstRef k => k | _ => Control.throw (Tactic_failure (Some (Message.of_string "ZifyLit: not a constant"))) end.
Ltac2 zl_cof (r : Std.reference) : constructor :=
  match r with Std.ConstructRef k => k | _ => Control.throw (Tactic_failure (Some (Message.of_string "ZifyLit: not a constructor"))) end.
Ltac2 zl_iof (r : Std.reference) : inductive :=
  match r with Std.IndRef k => k | _ => Control.throw (Tactic_failure (Some (Message.of_string "ZifyLit: not an inductive"))) end.

Ltac2 Type zl_ctx := { zl_ofnat : constant; zl_S : constructor; zl_O : constructor;
                       zl_add : constant; zl_sub : constant; zl_mul : constant; zl_opp : constant; zl_max : constant; zl_min : constant;
                       zl_zle : constant; zl_zlt : constant; zl_zge : constant; zl_zgt : constant; zl_not : constant; zl_iff : constant;
                       zl_eq : inductive; zl_and : inductive; zl_or : inductive; zl_Z : inductive;
                       mutable zl_hits : int }.

Ltac2 zl_new () : zl_ctx :=
  { zl_ofnat := zl_kof reference:(Z.of_nat); zl_S := zl_cof reference:(S); zl_O := zl_cof reference:(O);
    zl_add := zl_kof reference:(Z.add); zl_sub := zl_kof reference:(Z.sub); zl_mul := zl_kof reference:(Z.mul);
    zl_opp := zl_kof reference:(Z.opp); zl_max := zl_kof reference:(Z.max); zl_min := zl_kof reference:(Z.min);
    zl_zle := zl_kof reference:(Z.le); zl_zlt := zl_kof reference:(Z.lt); zl_zge := zl_kof reference:(Z.ge); zl_zgt := zl_kof reference:(Z.gt);
    zl_not := zl_kof reference:(not); zl_iff := zl_kof reference:(iff);
    zl_eq := zl_iof reference:(eq); zl_and := zl_iof reference:(and); zl_or := zl_iof reference:(or); zl_Z := zl_iof reference:(Z);
    zl_hits := 0 }.

(* [comment removed for export] *)
Ltac2 rec zl_nat_lit (x : zl_ctx) (t : constr) (acc : int) : int option :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Constructor c _ => if Constructor.equal c (x.(zl_O)) then Some acc else None
  | Constr.Unsafe.App f a =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constructor c _ =>
          if Constructor.equal c (x.(zl_S)) then
            (if Int.equal (Array.length a) 1 then zl_nat_lit x (Array.get a 0) (Int.add acc 1) else None)
          else None
      | _ => None
      end
  | _ => None
  end.

Ltac2 rec zl_pos (n : int) : constr :=
  if Int.le n 1 then constr:(xH)
  else
    let h := zl_pos (Int.div n 2) in
    Constr.Unsafe.make (Constr.Unsafe.App (if Int.equal (Int.mod n 2) 0 then constr:(xO) else constr:(xI)) (Array.make 1 h)).
Ltac2 zl_z (n : int) : constr :=
  if Int.equal n 0 then constr:(Z0) else Constr.Unsafe.make (Constr.Unsafe.App constr:(Zpos) (Array.make 1 (zl_pos n))).

Ltac2 zl_arith_op (x : zl_ctx) (k : constant) : bool :=
  if Constant.equal k (x.(zl_add)) then true else if Constant.equal k (x.(zl_zle)) then true
  else if Constant.equal k (x.(zl_sub)) then true else if Constant.equal k (x.(zl_zlt)) then true
  else if Constant.equal k (x.(zl_mul)) then true else if Constant.equal k (x.(zl_not)) then true
  else if Constant.equal k (x.(zl_zge)) then true else if Constant.equal k (x.(zl_zgt)) then true
  else if Constant.equal k (x.(zl_opp)) then true else if Constant.equal k (x.(zl_max)) then true
  else if Constant.equal k (x.(zl_min)) then true else Constant.equal k (x.(zl_iff)).

Ltac2 zl_is_Z (x : zl_ctx) (t : constr) : bool :=
  match Constr.Unsafe.kind t with Constr.Unsafe.Ind j _ => Ind.equal (x.(zl_Z)) j | _ => false end.

(* [comment removed for export] *)
Ltac2 rec zl_tr (x : zl_ctx) (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f a =>
      let descend () :=
        let h0 := x.(zl_hits) in
        let a' := Array.map (zl_tr x) a in
        if Int.equal h0 (x.(zl_hits)) then t else Constr.Unsafe.make (Constr.Unsafe.App f a') in
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constant k _ =>
          if Constant.equal k (x.(zl_ofnat)) then
            (if Int.equal (Array.length a) 1 then
               (match zl_nat_lit x (Array.get a 0) 0 with
                | Some n => x.(zl_hits) := Int.add (x.(zl_hits)) 1; zl_z n
                | None => t
                end)
             else t)
          else if zl_arith_op x k then descend ()
          else t
      | Constr.Unsafe.Ind i _ =>
          if Ind.equal i (x.(zl_and)) then descend ()
          else if Ind.equal i (x.(zl_or)) then descend ()
          else if Ind.equal i (x.(zl_eq)) then
            (if Int.equal (Array.length a) 3 then (if zl_is_Z x (Array.get a 0) then descend () else t) else t)
          else t
      | _ => t
      end
  | Constr.Unsafe.Prod b c =>
      let h0 := x.(zl_hits) in
      let ty' := zl_tr x (Constr.Binder.type b) in
      let c' := zl_tr x c in
      if Int.equal h0 (x.(zl_hits)) then t
      else Constr.Unsafe.make (Constr.Unsafe.Prod (Constr.Binder.unsafe_make (Constr.Binder.name b) (Constr.Binder.relevance b) ty') c')
  | _ => t
  end.

(* [comment removed for export] *)
Ltac2 zl_is_local (id : ident) : bool :=
  match Env.get [id] with None => true | Some _ => false end.

Ltac2 zl_try (f : unit -> unit) : unit := Control.once (fun () => Control.plus f (fun _ => ())).

Ltac2 zify_lit_all () : unit :=
  let x := zl_new () in
  let g := Control.goal () in
  x.(zl_hits) := 0;
  let g' := zl_tr x g in
  (if Int.equal (x.(zl_hits)) 0 then ()
   else zl_try (fun () => Std.change None (fun _ => g') { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }));
  List.iter (fun (id, body, ty) =>
    match body with
    | Some _ => ()
    | None =>
        x.(zl_hits) := 0;
        let ty' := zl_tr x ty in
        if Int.equal (x.(zl_hits)) 0 then ()
        else if zl_is_local id then
          zl_try (fun () => Std.change None (fun _ => ty') { Std.on_hyps := Some [(id, Std.AllOccurrences, Std.InHypTypeOnly)]; Std.on_concl := Std.NoOccurrences })
        else ()
    end) (Control.hyps ()).
(* [comment removed for export] *)
Ltac zify_lit_all := ltac2:(Control.enter (fun () => zl_try zify_lit_all)).   (* [comment removed for export] *)

Ltac2 zify_lit_goal () : unit :=
  let x := zl_new () in
  let g := Control.goal () in
  x.(zl_hits) := 0;
  let g' := zl_tr x g in
  if Int.equal (x.(zl_hits)) 0 then ()
  else zl_try (fun () => Std.change None (fun _ => g') { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }).
Ltac zify_lit := ltac2:(Control.enter (fun () => zl_try zify_lit_goal)).       (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zify_pre_extra := idtac.
Ltac zify_lit_hook := zify_pre_extra; zify_lit.

(* [comment removed for export] *)
Goal forall (f : Z -> Z) (a sp : Z), (a + Z.of_nat 24 <= sp)%Z -> (f (Z.of_nat 3) = 0)%Z -> (a + Z.of_nat 8 <= sp \/ sp + Z.of_nat 2 <= a - f (Z.of_nat 3))%Z.
Proof.
  intros f a sp H F. zify_lit.
  lazymatch goal with H : (a + Z.of_nat 24 <= sp)%Z, F : (f (Z.of_nat 3) = 0)%Z |- (a + 8 <= sp \/ sp + 2 <= a - f (Z.of_nat 3))%Z => idtac end.
  zify_lit_all.
  lazymatch goal with H : (a + 24 <= sp)%Z, F : (f (Z.of_nat 3) = 0)%Z |- (a + 8 <= sp \/ sp + 2 <= a - f (Z.of_nat 3))%Z => idtac end.
  lia.
Qed.
