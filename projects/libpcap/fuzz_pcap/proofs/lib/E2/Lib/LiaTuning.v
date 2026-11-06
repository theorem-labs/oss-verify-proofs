(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".
(* [comment removed for export] *)
From stdpp.bitvector Require Import tactics.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[global] Unset Lia Cache.
#[global] Unset Nia Cache.
#[global] Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac dmte_abstract e q :=
  tryif (match goal with H := context [e] |- _ => idtac end) then set (q := e) in *
  else (pose (q := e);
        (match reverse goal with H : context [e] |- _ => move q before H | _ => idtac end);
        repeat match goal with H : context [e] |- _ => change e with q in H end;
        try change e with q).
Ltac Z.div_mod_to_equations_generalize x y ::=
  pose proof (Stdlib.ZArith.BinInt.Z.div_mod x y);
  pose proof (Stdlib.ZArith.BinInt.Z.mod_pos_bound x y);
  pose proof (Stdlib.ZArith.BinInt.Z.mod_neg_bound x y);
  pose proof (Stdlib.omega.PreOmega.Z.div_0_r_ext x y);
  pose proof (Stdlib.omega.PreOmega.Z.mod_0_r_ext x y);
  let q := fresh "q" in
  let r := fresh "r" in
  dmte_abstract (x / y)%Z q;
  dmte_abstract (x mod y)%Z r;
  clearbody q r.
(* [comment removed for export] *)
Ltac rmx_set t x := dmte_abstract t x; clearbody x.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zify_done (x y : Z) : Prop := True.
Definition zify_done_qr (x y : Z) : Prop := True.

Ltac zify_new_dm x y :=
  lazymatch goal with
  | _ : zify_done x y |- _ => fail
  | _ => pose proof (Z.div_mod x y); pose proof (Z.mod_pos_bound x y); pose proof (Z.mod_neg_bound x y);
         pose proof (Z.div_0_r_ext x y); pose proof (Z.mod_0_r_ext x y);
         pose proof (I : zify_done x y)
  end.

Ltac zify_new_qr x y :=
  lazymatch goal with
  | _ : zify_done_qr x y |- _ => fail
  | _ => pose proof (Z.quot_rem' x y); pose proof (Z.rem_bound_pos_pos x y); pose proof (Z.rem_bound_pos_neg x y);
         pose proof (Z.rem_bound_neg_pos x y); pose proof (Z.rem_bound_neg_neg x y);
         pose proof (Z.quot_0_r_ext x y); pose proof (Z.rem_0_r_ext x y);
         pose proof (I : zify_done_qr x y)
  end.

(* [comment removed for export] *)
Ltac zify_dm_step :=
  match goal with
  | |- context [Z.div ?x ?y] => zify_new_dm x y
  | |- context [Z.modulo ?x ?y] => zify_new_dm x y
  | _ : context [Z.div ?x ?y] |- _ => zify_new_dm x y
  | _ : context [Z.modulo ?x ?y] |- _ => zify_new_dm x y
  end.

Ltac zify_qr_step :=
  match goal with
  | |- context [Z.quot ?x ?y] => zify_new_qr x y
  | |- context [Z.rem ?x ?y] => zify_new_qr x y
  | _ : context [Z.quot ?x ?y] |- _ => zify_new_qr x y
  | _ : context [Z.rem ?x ?y] |- _ => zify_new_qr x y
  end.

(* [comment removed for export] *)
Ltac zify_arith_prop T :=
  lazymatch T with
  | @eq Z _ _ => idtac | Z.lt _ _ => idtac | Z.le _ _ => idtac | Z.gt _ _ => idtac | Z.ge _ _ => idtac
  | @eq nat _ _ => idtac | Peano.lt _ _ => idtac | Peano.le _ _ => idtac
  | not ?P => zify_arith_prop P
  | ?A /\ ?B => first [ zify_arith_prop A | zify_arith_prop B ]
  | ?A \/ ?B => first [ zify_arith_prop A | zify_arith_prop B ]
  | _ => fail
  end.
Ltac zify_spec_premise H T :=
  lazymatch type of T with
  | Prop => first [ specialize (H (@eq_refl _ _ : T))
                  | tryif zify_arith_prop T then fail else specialize (H ltac:(assumption)) ]
  end.
Ltac zify_spec_premise2 H A T :=
  lazymatch type of T with
  | Prop => first [ specialize (fun a : A => H a (@eq_refl _ _ : T))
                  | tryif zify_arith_prop T then fail else
                      (let h := fresh "zh" in assert (h : T) by assumption; specialize (fun a : A => H a h); clear h) ]
  end.
Ltac zify_spec_hyp H :=
  lazymatch type of H with
  | ?T -> _ => first [ zify_spec_premise H T
                     | lazymatch type of H with ?A -> ?B -> _ => zify_spec_premise2 H A B end ]
  end.
Ltac zify_spec_trivial := repeat match goal with H : _ -> _ |- _ => zify_spec_hyp H end.

(* [comment removed for export] *)
Ltac2 zt_is_local (id : ident) : bool :=
  match Env.get [id] with None => true | Some _ => false end.

Ltac2 zt_split_section_ranges () : unit :=
  List.iter (fun h => let (id, body, ty) := h in
    match body with
    | Some _ => ()
    | None =>
        if zt_is_local id then () else
        lazy_match! ty with
        | (0 <= _ < _)%Z => let c := Control.hyp id in ltac1:(c |- destruct c; try clear c) (Ltac1.of_constr c)
        | _ => ()
        end
    end) (Control.hyps ()).
Ltac zify_split_ranges := ltac2:(Control.enter zt_split_section_ranges).

(* [comment removed for export] *)
Ltac zify_cheap_cleanup := zify_split_ranges.
Ltac Z.euclidean_division_equations_cleanup ::= zify_cheap_cleanup.

Ltac zify_fast_euclid :=
  Z.divide_to_equations';
  first [ progress (repeat zify_dm_step; repeat zify_qr_step); cbv beta | idtac ];
  Z.euclidean_division_equations_cleanup.

(* [comment removed for export] *)
Ltac Zify.zify_internal_to_euclidean_division_equations ::= zify_fast_euclid.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 lt_is_ref (t : constr) (r : Std.reference) : bool :=
  match r with
  | Std.ConstRef c => (match Constr.Unsafe.kind t with Constr.Unsafe.Constant c' _ => Constant.equal c c' | _ => false end)
  | Std.IndRef i => (match Constr.Unsafe.kind t with Constr.Unsafe.Ind i' _ => Ind.equal i i' | _ => false end)
  | Std.ConstructRef k => (match Constr.Unsafe.kind t with Constr.Unsafe.Constructor k' _ => Constructor.equal k k' | _ => false end)
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 zt_plain_consts () : constant FSet.t :=
  List.fold_left (fun s r => match r with Std.ConstRef c => FSet.add c s | _ => s end) (FSet.empty FSet.Tags.constant_tag)
    [reference:(Z.le); reference:(Z.lt); reference:(Z.ge); reference:(Z.gt); reference:(lt); reference:(ge);
     reference:(gt); reference:(N.le); reference:(N.lt); reference:(Z.divide)].
Ltac2 rec zt_plain_arith_s (cs : constant FSet.t) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ => FSet.mem c cs
      | Constr.Unsafe.Ind _ _ =>
          if lt_is_ref h reference:(and) then (if zt_plain_arith_s cs (Array.get args 0) then zt_plain_arith_s cs (Array.get args 1) else false)
          else if lt_is_ref h reference:(eq) then true else if lt_is_ref h reference:(le) then true
          else false
      | _ => false
      end
  | Constr.Unsafe.Ind _ _ => if lt_is_ref t reference:(True) then true else lt_is_ref t reference:(False)
  | _ => false
  end.

Ltac2 rec zt_plain_arith (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if lt_is_ref h reference:(Z.le) then true else if lt_is_ref h reference:(Z.lt) then true
          else if lt_is_ref h reference:(Z.ge) then true else if lt_is_ref h reference:(Z.gt) then true
          else if lt_is_ref h reference:(lt) then true else if lt_is_ref h reference:(ge) then true
          else if lt_is_ref h reference:(gt) then true else if lt_is_ref h reference:(N.le) then true
          else if lt_is_ref h reference:(N.lt) then true else if lt_is_ref h reference:(Z.divide) then true
          else false
      | Constr.Unsafe.Ind _ _ =>
          if lt_is_ref h reference:(and) then (if zt_plain_arith (Array.get args 0) then zt_plain_arith (Array.get args 1) else false)
          else if lt_is_ref h reference:(eq) then true else if lt_is_ref h reference:(le) then true
          else false
      | _ => false
      end
  | Constr.Unsafe.Ind _ _ => if lt_is_ref t reference:(True) then true else lt_is_ref t reference:(False)
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec zt_codomain (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ b => zt_codomain b
  | Constr.Unsafe.LetIn _ _ b => zt_codomain b
  | Constr.Unsafe.Cast c _ _ => zt_codomain c
  | _ => t
  end.
Ltac2 rec zt_head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => zt_head f
  | Constr.Unsafe.Cast c _ _ => zt_head c
  | _ => t
  end.
(* [comment removed for export] *)
Ltac2 zt_sort_is_prop (ty : constr) : bool := Constr.equal (zt_codomain ty) 'Prop.
Ltac2 zt_is_prop (ty : constr) : bool :=
  let h := zt_head (zt_codomain ty) in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant _ _ => zt_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Ind _ _ => zt_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Var _ => zt_sort_is_prop (Constr.type h)
  | _ => false
  end.

Ltac2 zt_is_prop_some (ty : constr) (id : ident) : ident option := if zt_is_prop ty then Some id else None.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 Type zt_memo := { mutable zmc : (constant, bool) FMap.t; mutable zmi : (inductive, bool) FMap.t }.
Ltac2 zt_memo_new () : zt_memo := { zmc := FMap.empty FSet.Tags.constant_tag; zmi := FMap.empty FSet.Tags.inductive_tag }.
Ltac2 zt_is_prop_m (m : zt_memo) (ty : constr) : bool :=
  let h := zt_head (zt_codomain ty) in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant c _ =>
      (match FMap.find_opt c (m.(zmc)) with
       | Some b => b
       | None => let b := zt_sort_is_prop (Constr.type h) in m.(zmc) := FMap.add c b (m.(zmc)); b end)
  | Constr.Unsafe.Ind i _ =>
      (match FMap.find_opt i (m.(zmi)) with
       | Some b => b
       | None => let b := zt_sort_is_prop (Constr.type h) in m.(zmi) := FMap.add i b (m.(zmi)); b end)
  | Constr.Unsafe.Var _ => zt_sort_is_prop (Constr.type h)
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 zt_prune () : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let mm := zt_memo_new () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if zt_is_local id then (if zt_plain_arith_s cs ty then None else if zt_is_prop_m mm ty then Some id else None) else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.

Ltac zify_prune := ltac2:(Control.enter zt_prune).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec zn_is_numeral (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 1 then
        (if Constr.equal f constr:(S) then zn_is_numeral (Array.get args 0) else false)
      else false
  | Constr.Unsafe.Constructor _ _ => Constr.equal c constr:(O)
  | _ => false
  end.
Ltac2 zn_check (n : Ltac1.t) : unit :=
  match Ltac1.to_constr n with
  | Some c => if zn_is_numeral c then () else Control.zero (Tactic_failure None)
  | None => Control.zero (Tactic_failure None)
  end.
Ltac zn_natlit n := let f := ltac2:(n |- zn_check n) in f n.
Ltac zn_goal := repeat match goal with |- context [Z.of_nat ?n] => zn_natlit n; let z := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with z end.
Ltac rawx_on := idtac.
Ltac rawx_pre := zn_goal; try (rawx_on; xlia zchecker).
Ltac zify_noeuclid :=
  intros; rawx_pre; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook.
(* [comment removed for export] *)
Ltac Zify.zify ::= intros; rawx_pre; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate;
                   Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                            | Zify.zify; xlia zchecker ]
        | Zify.zify; xlia zchecker ].
