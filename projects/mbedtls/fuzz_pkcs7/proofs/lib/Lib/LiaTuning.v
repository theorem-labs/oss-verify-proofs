(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2 FSet FMap.
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

Ltac zify_cheap_cleanup := zify_split_ranges; zify_spec_trivial.
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
Ltac2 rec zt_plain_arith (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
          else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
          else if Constr.equal h '@lt then true else if Constr.equal h '@ge then true
          else if Constr.equal h '@gt then true else if Constr.equal h '@N.le then true
          else if Constr.equal h '@N.lt then true else if Constr.equal h '@Z.divide then true
          else false
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h '@and then (if zt_plain_arith (Array.get args 0) then zt_plain_arith (Array.get args 1) else false)
          else if Constr.equal h '@eq then true else if Constr.equal h '@le then true
          else false
      | _ => false
      end
  | Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then true else Constr.equal t 'False
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
Ltac2 zt_sort_is_prop (ty : constr) : bool :=
  lazy_match! zt_codomain ty with Prop => true | _ => false end.
Ltac2 zt_is_prop (ty : constr) : bool :=
  let h := zt_head (zt_codomain ty) in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant _ _ => zt_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Ind _ _ => zt_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Var _ => zt_sort_is_prop (Constr.type h)
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 zt_prune () : unit :=
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if zt_plain_arith ty then None
                          else if Bool.and (zt_is_local id) (zt_is_prop ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 zf_const (c : constr) : constant :=
  match Constr.Unsafe.kind c with Constr.Unsafe.Constant k _ => k | _ => Control.throw Not_found end.
Ltac2 zf_ind (c : constr) : inductive :=
  match Constr.Unsafe.kind c with Constr.Unsafe.Ind k _ => k | _ => Control.throw Not_found end.

(* [comment removed for export] *)
Ltac2 zf_arith_consts () : constant FSet.t :=
  List.fold_left (fun s c => FSet.add (zf_const c) s) (FSet.empty FSet.Tags.constant_tag)
    ['@Z.le; '@Z.lt; '@Z.ge; '@Z.gt; '@lt; '@ge; '@gt; '@N.le; '@N.lt; '@Z.divide].

Ltac2 Type zf_env := { zf_cs : constant FSet.t; zf_and : inductive; zf_eq : inductive; zf_le : inductive;
                       zf_true : inductive; zf_false : inductive }.
Ltac2 zf_mkenv () : zf_env :=
  { zf_cs := zf_arith_consts (); zf_and := zf_ind '@and; zf_eq := zf_ind '@eq; zf_le := zf_ind '@le;
    zf_true := zf_ind 'True; zf_false := zf_ind 'False }.

(* [comment removed for export] *)
Ltac2 rec zf_plain_arith (e : zf_env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ => FSet.mem c (e.(zf_cs))
      | Constr.Unsafe.Ind i _ =>
          if Ind.equal i (e.(zf_eq)) then true
          else if Ind.equal i (e.(zf_and)) then
            (if zf_plain_arith e (Array.get args 0) then zf_plain_arith e (Array.get args 1) else false)
          else Ind.equal i (e.(zf_le))
      | _ => false
      end
  | Constr.Unsafe.Ind i _ => if Ind.equal i (e.(zf_true)) then true else Ind.equal i (e.(zf_false))
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 Type zf_cache := { zc_c : (constant, bool) FMap.t; zc_i : (inductive, bool) FMap.t }.
Ltac2 zf_is_prop (cache : zf_cache) (ty : constr) : bool * zf_cache :=
  let h := zt_head (zt_codomain ty) in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant c _ =>
      match FMap.find_opt c (cache.(zc_c)) with
      | Some b => (b, cache)
      | None => let b := zt_sort_is_prop (Constr.type h) in (b, { cache with zc_c := FMap.add c b (cache.(zc_c)) })
      end
  | Constr.Unsafe.Ind i _ =>
      match FMap.find_opt i (cache.(zc_i)) with
      | Some b => (b, cache)
      | None => let b := zt_sort_is_prop (Constr.type h) in (b, { cache with zc_i := FMap.add i b (cache.(zc_i)) })
      end
  | Constr.Unsafe.Var _ => (zt_sort_is_prop (Constr.type h), cache)
  | _ => (false, cache)
  end.

(* [comment removed for export] *)
Ltac2 zf_streak () : int := 12.

(* [comment removed for export] *)
Ltac2 zf_prop_of_const (cache : zf_cache) (c : constant) (h : constr) : bool * zf_cache :=
  match FMap.find_opt c (cache.(zc_c)) with
  | Some b => (b, cache)
  | None => let b := zt_sort_is_prop (Constr.type h) in (b, { cache with zc_c := FMap.add c b (cache.(zc_c)) })
  end.
Ltac2 zf_prop_of_ind (cache : zf_cache) (i : inductive) (h : constr) : bool * zf_cache :=
  match FMap.find_opt i (cache.(zc_i)) with
  | Some b => (b, cache)
  | None => let b := zt_sort_is_prop (Constr.type h) in (b, { cache with zc_i := FMap.add i b (cache.(zc_i)) })
  end.
Ltac2 zf_classify (e : zf_env) (cache : zf_cache) (ty : constr) : bool * zf_cache :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ =>
          if FSet.mem c (e.(zf_cs)) then (false, cache) else zf_prop_of_const cache c h
      | Constr.Unsafe.Ind i _ =>
          if Ind.equal i (e.(zf_eq)) then (false, cache)
          else if Ind.equal i (e.(zf_le)) then (false, cache)
          else if Ind.equal i (e.(zf_and)) then
            (if (if zf_plain_arith e (Array.get args 0) then zf_plain_arith e (Array.get args 1) else false)
             then (false, cache) else zf_prop_of_ind cache i h)
          else zf_prop_of_ind cache i h
      | _ => zf_is_prop cache ty
      end
  | Constr.Unsafe.Ind i _ =>
      if Ind.equal i (e.(zf_true)) then (false, cache)
      else if Ind.equal i (e.(zf_false)) then (false, cache)
      else zf_prop_of_ind cache i ty
  | Constr.Unsafe.Constant c _ => zf_prop_of_const cache c ty
  | _ => zf_is_prop cache ty
  end.

Ltac2 zf_prune () : unit :=
  let e := zf_mkenv () in
  let hs := Control.hyps () in
  let (ids, _, _) := List.fold_left (fun acc h =>
      let (ids, cache, streak) := acc in
      let (id, body, ty) := h in
      match body with
      | Some _ => acc
      | None =>
          let (p, cache) := zf_classify e cache ty in
          if p then
            (if Int.ge streak (zf_streak ()) then (id :: ids, cache, streak)
             else if zt_is_local id then (id :: ids, cache, Int.add streak 1) else (ids, cache, 0))
          else (ids, cache, streak)
      end) ([], { zc_c := FMap.empty FSet.Tags.constant_tag; zc_i := FMap.empty FSet.Tags.inductive_tag }, 0) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.

(* [comment removed for export] *)
Ltac2 zf_is_range (e : zf_env) (zle : constant) (zlt : constant) (ty : constr) : bool :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Ind i _ =>
          if Ind.equal i (e.(zf_and)) then
            match Constr.Unsafe.kind (Array.get args 0) with
            | Constr.Unsafe.App h1 _ =>
                match Constr.Unsafe.kind h1 with
                | Constr.Unsafe.Constant c1 _ =>
                    if Constant.equal c1 zle then
                      match Constr.Unsafe.kind (Array.get args 1) with
                      | Constr.Unsafe.App h2 _ =>
                          match Constr.Unsafe.kind h2 with
                          | Constr.Unsafe.Constant c2 _ => Constant.equal c2 zlt
                          | _ => false
                          end
                      | _ => false
                      end
                    else false
                | _ => false
                end
            | _ => false
            end
          else false
      | _ => false
      end
  | _ => false
  end.

Ltac2 zf_split_section_ranges () : unit :=
  let e := zf_mkenv () in
  let zle := zf_const '@Z.le in let zlt := zf_const '@Z.lt in
  let _ := List.fold_left (fun streak h =>
    let (id, body, ty) := h in
    match body with
    | Some _ => streak
    | None =>
        if Int.ge streak (zf_streak ()) then streak
        else if zf_is_range e zle zlt ty then
          (if zt_is_local id then Int.add streak 1
           else (lazy_match! ty with
                 | (0 <= _ < _)%Z => let c := Control.hyp id in ltac1:(c |- destruct c; try clear c) (Ltac1.of_constr c)
                 | _ => ()
                 end; 0))
        else streak
    end) 0 (Control.hyps ()) in ().

Ltac zify_prune := ltac2:(Control.enter zf_prune).
Ltac zify_prune_ref := ltac2:(Control.enter zt_prune).
Ltac zify_split_ranges_ref := ltac2:(Control.enter zt_split_section_ranges).
Ltac zify_split_ranges ::= ltac2:(Control.enter zf_split_section_ranges).

(* [comment removed for export] *)
Ltac2 zf_keep_goal_vars () : unit :=
  let rec vars (acc : ident list) (t : constr) : ident list :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Var id => id :: acc
    | Constr.Unsafe.App f args => Array.fold_left vars (vars acc f) args
    | Constr.Unsafe.Cast c _ _ => vars acc c
    | Constr.Unsafe.Prod b c => vars (vars acc (Constr.Binder.type b)) c
    | Constr.Unsafe.Lambda b c => vars (vars acc (Constr.Binder.type b)) c
    | Constr.Unsafe.LetIn b v c => vars (vars (vars acc (Constr.Binder.type b)) v) c
    | Constr.Unsafe.Proj _ _ c => vars acc c
    | _ => acc
    end in
  let e := zf_mkenv () in
  let zle := zf_const '@Z.le in let zlt := zf_const '@Z.lt in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, streak) := acc in
      let (id, body, ty) := h in
      match body with
      | Some _ => acc
      | None =>
          if Int.ge streak (zf_streak ()) then acc
          else if zf_is_range e zle zlt ty then
            (if zt_is_local id then (ids, Int.add streak 1) else (id :: ids, 0))
          else acc
      end) (vars [] (Control.goal ()), 0) (Control.hyps ()) in
  Std.keep ids.
Ltac zify_keep_goal_vars := ltac2:(Control.enter zf_keep_goal_vars).


(* [comment removed for export] *)
Ltac zify_noeuclid :=
  intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook.

(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune;                      (* [comment removed for export] *)
          first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                | Zify.zify; xlia zchecker ]
        | Zify.zify; xlia zchecker ].
