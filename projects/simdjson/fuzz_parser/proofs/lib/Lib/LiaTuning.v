(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
From Ltac2 Require FSet FMap.
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

Ltac zify_prune := ltac2:(Control.enter zt_prune).

(* [comment removed for export] *)
Ltac zify_noeuclid :=
  intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec rv_vars_f (fuel : int array) (t : constr) (acc : ident list) : ident list :=
  if Int.le (Array.get fuel 0) 0 then acc else
  (Array.set fuel 0 (Int.sub (Array.get fuel 0) 1);
   match Constr.Unsafe.kind t with
   | Constr.Unsafe.Var id => id :: acc
   | Constr.Unsafe.App f args => Array.fold_left (fun a x => rv_vars_f fuel x a) (rv_vars_f fuel f acc) args
   | Constr.Unsafe.Prod b c => rv_vars_f fuel c (rv_vars_f fuel (Constr.Binder.type b) acc)
   | Constr.Unsafe.Lambda b c => rv_vars_f fuel c (rv_vars_f fuel (Constr.Binder.type b) acc)
   | Constr.Unsafe.LetIn b v c => rv_vars_f fuel c (rv_vars_f fuel v (rv_vars_f fuel (Constr.Binder.type b) acc))
   | Constr.Unsafe.Cast c _ _ => rv_vars_f fuel c acc
   | _ => acc
   end).
Ltac2 rv_vars (t : constr) (acc : ident list) : ident list := rv_vars_f (Array.make 1 400) t acc.
Ltac2 rv_goal_vars () : ident list := rv_vars_f (Array.make 1 3000) (Control.goal ()) [].
Ltac2 rv_mem (x : ident) (l : ident list) : bool := List.exist (fun y => Ident.equal x y) l.
Ltac2 rv_inter (a : ident list) (b : ident list) : bool := List.exist (fun x => rv_mem x b) a.
Ltac2 rv_step (hs : (ident * constr option * constr) list) (r : ident list) : ident list :=
  List.fold_left (fun r h => let (id, body, ty) := h in
     match body with
     | Some b => if rv_mem id r then List.append (rv_vars b (rv_vars ty [])) r else r
     | None => if zt_plain_arith ty then (let vs := rv_vars ty [] in if rv_inter vs r then List.append vs r else r) else r
     end) r hs.
(* [comment removed for export] *)
Ltac2 rv_newest (hs : (ident * constr option * constr) list) : ident list :=
  List.fold_left (fun acc h => let (id, body, ty) := h in
     match body with
     | Some _ => acc
     | None => if zt_is_local id then (if zt_plain_arith ty then rv_vars ty [] else acc) else acc
     end) [] hs.
(* [comment removed for export] *)
Ltac2 rv_section_free (hs : (ident * constr option * constr) list) : bool :=
  List.for_all (fun h => let (id, body, ty) := h in
     if zt_is_local id then true
     else match body with Some _ => false | None => Bool.neg (zt_is_prop ty) end) hs.
(* [comment removed for export] *)
Ltac2 rv_ref_ids (hs : (ident * constr option * constr) list) : ident list :=
  let r0 := List.append (rv_goal_vars ()) (rv_newest hs) in
  let r := rv_step hs (rv_step hs (rv_step hs r0)) in
  List.map_filter (fun h => let (id, body, ty) := h in
     match body with
     | Some _ => None
     | None => if zt_is_local id then
                 (if zt_is_prop ty then (if zt_plain_arith ty then (if rv_inter (rv_vars ty []) r then None else Some id) else Some id) else None)
               else None
     end) hs.

(* [comment removed for export] *)
Ltac2 Type rv_iset := ident FSet.t.
Ltac2 rvs_e () : rv_iset := FSet.empty FSet.Tags.ident_tag.
Ltac2 rec rvs_vars_f (fuel : int array) (t : constr) (acc : rv_iset) : rv_iset :=
  if Int.le (Array.get fuel 0) 0 then acc else
  (Array.set fuel 0 (Int.sub (Array.get fuel 0) 1);
   match Constr.Unsafe.kind t with
   | Constr.Unsafe.Var id => FSet.add id acc
   | Constr.Unsafe.App f args => Array.fold_left (fun a x => rvs_vars_f fuel x a) (rvs_vars_f fuel f acc) args
   | Constr.Unsafe.Prod b c => rvs_vars_f fuel c (rvs_vars_f fuel (Constr.Binder.type b) acc)
   | Constr.Unsafe.Lambda b c => rvs_vars_f fuel c (rvs_vars_f fuel (Constr.Binder.type b) acc)
   | Constr.Unsafe.LetIn b v c => rvs_vars_f fuel c (rvs_vars_f fuel v (rvs_vars_f fuel (Constr.Binder.type b) acc))
   | Constr.Unsafe.Cast c _ _ => rvs_vars_f fuel c acc
   | _ => acc
   end).
Ltac2 rvs_vars (t : constr) (acc : rv_iset) : rv_iset := rvs_vars_f (Array.make 1 400) t acc.
(* [comment removed for export] *)
Ltac2 Type rv_hrec := { rvh_id : ident; rvh_kind : int; rvh_vs : rv_iset; rvh_body : constr option; rvh_ty : constr }.
Ltac2 rvs_info (hs : (ident * constr option * constr) list) : rv_hrec list :=
  List.map (fun h => let (id, body, ty) := h in
    match body with
    | Some _ => { rvh_id := id; rvh_kind := 0; rvh_vs := rvs_e (); rvh_body := body; rvh_ty := ty }
    | None => if zt_plain_arith ty then { rvh_id := id; rvh_kind := 1; rvh_vs := rvs_vars ty (rvs_e ()); rvh_body := None; rvh_ty := ty }
              else { rvh_id := id; rvh_kind := 2; rvh_vs := rvs_e (); rvh_body := None; rvh_ty := ty }
    end) hs.
Ltac2 rvs_meets (a : rv_iset) (b : rv_iset) : bool := Bool.neg (FSet.is_empty (FSet.inter a b)).
(* [comment removed for export] *)
Ltac2 rvs_step (hi : rv_hrec list) (r : rv_iset) : rv_iset :=
  List.fold_left (fun r h =>
     if Int.equal (h.(rvh_kind)) 1 then (if rvs_meets (h.(rvh_vs)) r then FSet.union (h.(rvh_vs)) r else r)
     else if Int.equal (h.(rvh_kind)) 0 then
       (if FSet.mem (h.(rvh_id)) r then
          (match h.(rvh_body) with
           | Some b => FSet.union (rvs_vars b (rvs_vars (h.(rvh_ty)) (rvs_e ()))) r
           | None => r end)
        else r)
     else r) r hi.
(* [comment removed for export] *)
Ltac2 rvs_newest (hi : rv_hrec list) : rv_iset :=
  List.fold_left (fun acc h => if Int.equal (h.(rvh_kind)) 1 then (if zt_is_local (h.(rvh_id)) then h.(rvh_vs) else acc) else acc) (rvs_e ()) hi.
Ltac2 rvs_ids (hs : (ident * constr option * constr) list) : ident list :=
  let hi := rvs_info hs in
  let r0 := FSet.union (rvs_vars_f (Array.make 1 3000) (Control.goal ()) (rvs_e ())) (rvs_newest hi) in
  let r := rvs_step hi (rvs_step hi (rvs_step hi r0)) in
  List.map_filter (fun h =>
     if Int.equal (h.(rvh_kind)) 0 then None
     else if zt_is_local (h.(rvh_id)) then
       (if zt_is_prop (h.(rvh_ty)) then
          (if Int.equal (h.(rvh_kind)) 1 then (if rvs_meets (h.(rvh_vs)) r then None else Some (h.(rvh_id))) else Some (h.(rvh_id)))
        else None)
     else None) hi.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec rv4_nc_find (t : constr) (l : (constr * int) list) : int option :=
  match l with
  | [] => None
  | p :: l' => let (c, k) := p in if Constr.equal t c then Some k else rv4_nc_find t l'
  end.
(* [comment removed for export] *)
Ltac2 rec rv4_count (t : constr) (k : int) : int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 1 then
        (match Constr.Unsafe.kind h with
         | Constr.Unsafe.Constructor _ _ => rv4_count (Array.get args 0) (Int.add k 2)
         | _ => Int.sub 0 1
         end)
      else Int.sub 0 1
  | Constr.Unsafe.Constructor _ _ => Int.add k 1
  | _ => Int.sub 0 1
  end.
Ltac2 rec rv4_vars_f (nc : (constr * int) list ref) (fuel : int array) (t : constr) (acc : rv_iset) : rv_iset :=
  let f0 := Array.get fuel 0 in
  if Int.equal (Int.compare f0 1) -1 then acc else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id => Array.set fuel 0 (Int.sub f0 1); FSet.add id acc
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constructor _ _ =>
          if Int.equal (Array.length args) 1 then rv4_chain nc fuel (Array.get args 0) 2 acc
          else (Array.set fuel 0 (Int.sub f0 2); rv4_args nc fuel args 0 (Array.length args) acc)
      | Constr.Unsafe.Constant _ _ =>
          Array.set fuel 0 (Int.sub f0 2);
          let n := Array.length args in
          if Int.equal n 2 then rv4_vars_f nc fuel (Array.get args 1) (rv4_vars_f nc fuel (Array.get args 0) acc)
          else if Int.equal n 1 then rv4_vars_f nc fuel (Array.get args 0) acc
          else rv4_args nc fuel args 0 n acc
      | Constr.Unsafe.Ind _ _ => Array.set fuel 0 (Int.sub f0 2); rv4_args nc fuel args 0 (Array.length args) acc
      | _ => Array.set fuel 0 (Int.sub f0 1); rv4_args nc fuel args 0 (Array.length args) (rv4_vars_f nc fuel h acc)
      end
  | Constr.Unsafe.Prod b c => Array.set fuel 0 (Int.sub f0 1); rv4_vars_f nc fuel c (rv4_vars_f nc fuel (Constr.Binder.type b) acc)
  | Constr.Unsafe.Lambda b c => Array.set fuel 0 (Int.sub f0 1); rv4_vars_f nc fuel c (rv4_vars_f nc fuel (Constr.Binder.type b) acc)
  | Constr.Unsafe.LetIn b v c =>
      Array.set fuel 0 (Int.sub f0 1); rv4_vars_f nc fuel c (rv4_vars_f nc fuel v (rv4_vars_f nc fuel (Constr.Binder.type b) acc))
  | Constr.Unsafe.Cast c _ _ => Array.set fuel 0 (Int.sub f0 1); rv4_vars_f nc fuel c acc
  | _ => Array.set fuel 0 (Int.sub f0 1); acc
  end
with rv4_args (nc : (constr * int) list ref) (fuel : int array) (args : constr array) (i : int) (n : int) (acc : rv_iset) : rv_iset :=
  if Int.equal i n then acc else rv4_args nc fuel args (Int.add i 1) n (rv4_vars_f nc fuel (Array.get args i) acc)
(* [comment removed for export] *)
with rv4_chain (nc : (constr * int) list ref) (fuel : int array) (t : constr) (n : int) (acc : rv_iset) : rv_iset :=
  if Int.equal n 12 then
    (match rv4_nc_find t (nc.(contents)) with
     | Some k => Array.set fuel 0 (Int.sub (Array.get fuel 0) (Int.add n k)); acc
     | None =>
         let k := rv4_count t 0 in
         if Int.equal (Int.compare k 0) -1 then rv4_chain_nc nc fuel t n acc
         else (nc.(contents) := (t, k) :: nc.(contents); Array.set fuel 0 (Int.sub (Array.get fuel 0) (Int.add n k)); acc)
     end)
  else rv4_chain_nc nc fuel t n acc
(* [comment removed for export] *)
with rv4_chain_nc (nc : (constr * int) list ref) (fuel : int array) (t : constr) (n : int) (acc : rv_iset) : rv_iset :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 1 then
        (match Constr.Unsafe.kind h with
         | Constr.Unsafe.Constructor _ _ =>
             let n' := Int.add n 2 in
             if Int.equal n' 12 then rv4_chain nc fuel (Array.get args 0) n' acc else rv4_chain_nc nc fuel (Array.get args 0) n' acc
         | _ => Array.set fuel 0 (Int.sub (Array.get fuel 0) n); rv4_vars_f nc fuel t acc
         end)
      else (Array.set fuel 0 (Int.sub (Array.get fuel 0) n); rv4_vars_f nc fuel t acc)
  | Constr.Unsafe.Constructor _ _ => Array.set fuel 0 (Int.sub (Array.get fuel 0) (Int.add n 1)); acc
  | _ => Array.set fuel 0 (Int.sub (Array.get fuel 0) n); rv4_vars_f nc fuel t acc
  end.

(* [comment removed for export] *)
Ltac2 Type rv4_refs := { f_zle : constr; f_zlt : constr; f_zge : constr; f_zgt : constr; f_lt : constr; f_ge : constr; f_gt : constr;
                         f_nle : constr; f_nlt : constr; f_zdiv : constr; f_and : constr; f_eq : constr; f_le : constr; f_prop : constr }.
Ltac2 rv4_mkrefs () : rv4_refs :=
  { f_zle := Env.instantiate reference:(Z.le); f_zlt := Env.instantiate reference:(Z.lt); f_zge := Env.instantiate reference:(Z.ge);
    f_zgt := Env.instantiate reference:(Z.gt); f_lt := Env.instantiate reference:(lt); f_ge := Env.instantiate reference:(ge);
    f_gt := Env.instantiate reference:(gt); f_nle := Env.instantiate reference:(N.le); f_nlt := Env.instantiate reference:(N.lt);
    f_zdiv := Env.instantiate reference:(Z.divide); f_and := Env.instantiate reference:(and); f_eq := Env.instantiate reference:(eq);
    f_le := Env.instantiate reference:(le); f_prop := Constr.type (Env.instantiate reference:(True)) }.
Ltac2 Type rv4_hrec := { r4_id : ident; r4_kind : int; r4_loc : bool; r4_body : constr option; r4_ty : constr;
                         r4_prop : int;                      (* [comment removed for export] *)
                         mutable r4_vs : rv_iset option;     (* [comment removed for export] *)
                         mutable r4_abs : bool;              (* [comment removed for export] *)
                         mutable r4_stamp : int }.           (* [comment removed for export] *)
Ltac2 Type rv4_st := { mutable s_r : rv_iset; mutable s_n : int;                (* [comment removed for export] *)
                       mutable s_l : ident list; mutable s_ln : int;           (* [comment removed for export] *)
                       mutable s_pc : (constant, constr * bool) FMap.t; mutable s_pi : (inductive, constr * bool) FMap.t;    (* [comment removed for export] *)
                       mutable s_cc : (constant, constr * int * bool) FMap.t; mutable s_ci : (inductive, constr * int * bool) FMap.t;   (* [comment removed for export] *)
                       s_nc : (constr * int) list ref; s_f : rv4_refs }.                                          (* [comment removed for export] *)
Ltac2 rv4_new () : rv4_st :=
  { s_r := rvs_e (); s_n := 0; s_l := []; s_ln := 0;
    s_pc := FMap.empty FSet.Tags.constant_tag; s_pi := FMap.empty FSet.Tags.inductive_tag;
    s_cc := FMap.empty FSet.Tags.constant_tag; s_ci := FMap.empty FSet.Tags.inductive_tag; s_nc := { contents := [] }; s_f := rv4_mkrefs () }.

(* [comment removed for export] *)
Ltac2 rv4_const_plain (f : rv4_refs) (h : constr) : bool :=
  if Constr.equal h (f.(f_zle)) then true else if Constr.equal h (f.(f_zlt)) then true
  else if Constr.equal h (f.(f_zge)) then true else if Constr.equal h (f.(f_zgt)) then true
  else if Constr.equal h (f.(f_lt)) then true else if Constr.equal h (f.(f_ge)) then true
  else if Constr.equal h (f.(f_gt)) then true else if Constr.equal h (f.(f_nle)) then true
  else if Constr.equal h (f.(f_nlt)) then true else if Constr.equal h (f.(f_zdiv)) then true
  else false.
(* [comment removed for export] *)
Ltac2 rv4_ind_code (f : rv4_refs) (h : constr) : int :=
  if Constr.equal h (f.(f_and)) then 2 else if Constr.equal h (f.(f_eq)) then 1 else if Constr.equal h (f.(f_le)) then 1 else 0.
(* [comment removed for export] *)
Ltac2 rv4_sort_is_prop (f : rv4_refs) (ty : constr) : bool := Constr.equal (zt_codomain ty) (f.(f_prop)).
(* [comment removed for export] *)
Ltac2 rv4_head_c (st : rv4_st) (c : constant) (h : constr) : int * bool :=
  match FMap.find_opt c (st.(s_cc)) with
  | Some p => let (h0, k, b) := p in
              if Constr.equal h h0 then (k, b) else ((if rv4_const_plain (st.(s_f)) h then 1 else 0), rv4_sort_is_prop (st.(s_f)) (Constr.type h))
  | None => let k := if rv4_const_plain (st.(s_f)) h then 1 else 0 in let b := rv4_sort_is_prop (st.(s_f)) (Constr.type h) in
            st.(s_cc) := FMap.add c (h, k, b) (st.(s_cc)); (k, b)
  end.
Ltac2 rv4_head_i (st : rv4_st) (i : inductive) (h : constr) : int * bool :=
  match FMap.find_opt i (st.(s_ci)) with
  | Some p => let (h0, k, b) := p in
              if Constr.equal h h0 then (k, b) else (rv4_ind_code (st.(s_f)) h, rv4_sort_is_prop (st.(s_f)) (Constr.type h))
  | None => let k := rv4_ind_code (st.(s_f)) h in let b := rv4_sort_is_prop (st.(s_f)) (Constr.type h) in
            st.(s_ci) := FMap.add i (h, k, b) (st.(s_ci)); (k, b)
  end.
(* [comment removed for export] *)
Ltac2 rec rv4_plain (st : rv4_st) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ => let (k, _) := rv4_head_c st c h in Int.equal k 1
      | Constr.Unsafe.Ind i _ =>
          let (k, _) := rv4_head_i st i h in
          if Int.equal k 2 then (if rv4_plain st (Array.get args 0) then rv4_plain st (Array.get args 1) else false) else Int.equal k 1
      | _ => false
      end
  | Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then true else Constr.equal t 'False
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 rv4_class (st : rv4_st) (t : constr) : bool * int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ => let (k, b) := rv4_head_c st c h in (Int.equal k 1, (if b then 1 else 0))
      | Constr.Unsafe.Ind i _ =>
          let (k, b) := rv4_head_i st i h in
          ((if Int.equal k 2 then (if rv4_plain st (Array.get args 0) then rv4_plain st (Array.get args 1) else false) else Int.equal k 1),
           (if b then 1 else 0))
      | _ => (false, 2)
      end
  | Constr.Unsafe.Ind _ _ => ((if Constr.equal t 'True then true else Constr.equal t 'False), 2)
  | _ => (false, 2)
  end.
(* [comment removed for export] *)
Ltac2 rv4_is_prop (st : rv4_st) (ty : constr) : bool :=
  let h := zt_head (zt_codomain ty) in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant c _ =>
      (match FMap.find_opt c (st.(s_pc)) with
       | Some p => let (h0, b) := p in if Constr.equal h h0 then b else rv4_sort_is_prop (st.(s_f)) (Constr.type h)
       | None => let b := rv4_sort_is_prop (st.(s_f)) (Constr.type h) in st.(s_pc) := FMap.add c (h, b) (st.(s_pc)); b
       end)
  | Constr.Unsafe.Ind i _ =>
      (match FMap.find_opt i (st.(s_pi)) with
       | Some p => let (h0, b) := p in if Constr.equal h h0 then b else rv4_sort_is_prop (st.(s_f)) (Constr.type h)
       | None => let b := rv4_sort_is_prop (st.(s_f)) (Constr.type h) in st.(s_pi) := FMap.add i (h, b) (st.(s_pi)); b
       end)
  | Constr.Unsafe.Var _ => rv4_sort_is_prop (st.(s_f)) (Constr.type h)
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec rv4_info (st : rv4_st) (guarded : bool) (hs : (ident * constr option * constr) list) : rv4_hrec list :=
  match hs with
  | [] => []
  | h :: hs' =>
      let (id, body, ty) := h in
      let loc := zt_is_local id in
      let (pl, pr) := match body with Some _ => (false, 2) | None => rv4_class st ty end in
      (if loc then () else if guarded then
         (match body with
          | Some _ => Control.zero (Tactic_failure None)
          | None => if (if Int.equal pr 2 then rv4_is_prop st ty else Int.equal pr 1) then Control.zero (Tactic_failure None) else ()
          end) else ());
      let k := match body with Some _ => 0 | None => if pl then 1 else 2 end in
      let r := { r4_id := id; r4_kind := k; r4_loc := loc; r4_body := body; r4_ty := ty; r4_prop := pr;
                 r4_vs := None; r4_abs := false; r4_stamp := Int.sub 0 1 } in
      let rest := rv4_info st guarded hs' in
      r :: rest
  end.
Ltac2 rv4_union (st : rv4_st) (s : rv_iset) : unit :=
  let r := FSet.union s (st.(s_r)) in st.(s_r) := r; st.(s_n) := FSet.cardinal r.
Ltac2 rv4_rlist (st : rv4_st) : ident list :=
  if Int.equal (st.(s_ln)) (st.(s_n)) then st.(s_l)
  else (let l := FSet.elements (st.(s_r)) in st.(s_l) := l; st.(s_ln) := st.(s_n); l).
Ltac2 rv4_vars (st : rv4_st) (t : constr) (acc : rv_iset) : rv_iset := rv4_vars_f (st.(s_nc)) (Array.make 1 400) t acc.
Ltac2 rv4_force (st : rv4_st) (h : rv4_hrec) : rv_iset :=
  match h.(r4_vs) with
  | Some s => s
  | None => let s := rv4_vars st (h.(r4_ty)) (rvs_e ()) in h.(r4_vs) := Some s; s
  end.
(* [comment removed for export] *)
Ltac2 rv4_test (st : rv4_st) (h : rv4_hrec) : bool :=
  if h.(r4_abs) then true
  else if Int.equal (h.(r4_stamp)) (st.(s_n)) then false
  else
    let maybe := match h.(r4_vs) with
                 | Some _ => true
                 | None => Bool.neg (Constr.Unsafe.is_closed (Constr.Unsafe.closenl (rv4_rlist st) 1 (h.(r4_ty))))
                 end in
    if maybe then
      (if rvs_meets (rv4_force st h) (st.(s_r)) then (h.(r4_abs) := true; true) else (h.(r4_stamp) := st.(s_n); false))
    else (h.(r4_stamp) := st.(s_n); false).
(* [comment removed for export] *)
Ltac2 rv4_round (st : rv4_st) (hi : rv4_hrec list) : unit :=
  List.iter (fun h =>
    if h.(r4_abs) then ()
    else if Int.equal (h.(r4_kind)) 1 then (if rv4_test st h then rv4_union st (rv4_force st h) else ())
    else (* [comment removed for export] *)
      (if FSet.mem (h.(r4_id)) (st.(s_r)) then
         (match h.(r4_body) with
          | Some b => h.(r4_abs) := true; rv4_union st (rv4_vars st b (rv4_vars st (h.(r4_ty)) (rvs_e ())))
          | None => ()
          end)
       else ())) hi.
(* [comment removed for export] *)
Ltac2 rv4_ids (guarded : bool) (hs : (ident * constr option * constr) list) : ident list :=
  let st := rv4_new () in
  let hi := rv4_info st guarded hs in
  let hi01 := List.filter (fun h => Bool.neg (Int.equal (h.(r4_kind)) 2)) hi in
  (* [comment removed for export] *)
  let newest := List.fold_left (fun acc h => if Int.equal (h.(r4_kind)) 1 then (if h.(r4_loc) then Some h else acc) else acc) None hi01 in
  rv4_union st (rv4_vars_f (st.(s_nc)) (Array.make 1 3000) (Control.goal ()) (rvs_e ()));
  (match newest with Some h => rv4_union st (rv4_force st h) | None => () end);
  (* [comment removed for export] *)
  let n0 := st.(s_n) in
  rv4_round st hi01;
  (if Int.equal n0 (st.(s_n)) then () else
     (let n1 := st.(s_n) in
      rv4_round st hi01;
      if Int.equal n1 (st.(s_n)) then () else rv4_round st hi01));
  List.map_filter (fun h =>
     if Int.equal (h.(r4_kind)) 0 then None
     else if h.(r4_loc) then
       (if (if Int.equal (h.(r4_prop)) 2 then rv4_is_prop st (h.(r4_ty)) else Int.equal (h.(r4_prop)) 1) then
          (if Int.equal (h.(r4_kind)) 1 then (if rv4_test st h then None else Some (h.(r4_id))) else Some (h.(r4_id)))
        else None)
     else None) hi.

Ltac2 rv_prune0 () : unit := match rv4_ids true (Control.hyps ()) with [] => () | ids => Std.clear ids end.
(* [comment removed for export] *)
Ltac zify_prune_relevant := ltac2:(Control.enter rv_prune0).

(* [comment removed for export] *)
Ltac zify_noeuclid_nosat :=
  intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.

(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune_relevant; zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec zt_prune_keep_ids (k : int) (hs : (ident * constr option * constr) list) : ident list :=
  if Int.equal (Int.compare k 1) -1 then [] else
  match hs with
  | [] => []
  | h :: hs' =>
      let (id, body, ty) := h in
      let rest := zt_prune_keep_ids (Int.sub k 1) hs' in
      match body with
      | Some _ => rest
      | None => if zt_plain_arith ty then rest else if Bool.and (zt_is_local id) (zt_is_prop ty) then id :: rest else rest
      end
  end.
Ltac2 zt_prune_keep (n : int) : unit :=
  let hs := Control.hyps () in
  match zt_prune_keep_ids (Int.sub (List.length hs) n) hs with [] => () | ids => Std.clear ids end.
Ltac zify_prune_keep1 := ltac2:(Control.enter (fun () => zt_prune_keep 1)).
Ltac zify_prune_keep2 := ltac2:(Control.enter (fun () => zt_prune_keep 2)).
Ltac zify_prune_keep3 := ltac2:(Control.enter (fun () => zt_prune_keep 3)).
Ltac zify_prune_keep4 := ltac2:(Control.enter (fun () => zt_prune_keep 4)).
Ltac lia_keep1 := first [ zify_prune_keep1; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | lia ].
Ltac lia_keep2 := first [ zify_prune_keep2; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | lia ].
Ltac lia_keep3 := first [ zify_prune_keep3; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | lia ].
Ltac lia_keep4 := first [ zify_prune_keep4; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 zt_clear_local_disj () : unit :=
  let o := '@or in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => (match Constr.Unsafe.kind ty with
                 | Constr.Unsafe.App hd _ => if Constr.equal hd o then (if zt_is_local id then Some id else None) else None
                 | _ => None
                 end)
      end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac lia_clear_disj := ltac2:(Control.enter zt_clear_local_disj).
(* [comment removed for export] *)
Ltac dlia1 :=
  first [ zify_prune_relevant; zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker ].
Ltac dlia :=
  first [ match goal with H : ?T |- ?T => exact H end
        | lia_clear_disj; dlia1
        | match goal with D : _ \/ _ |- _ => generalize D; lia_clear_disj; dlia1 end
        | match goal with D1 : _ \/ _ |- _ => match goal with D2 : _ \/ _ |- _ => generalize D1 D2; lia_clear_disj; dlia1 end end
        | lia ].

(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Export ZifyLit.
Ltac Zify.zify_pre_hook ::= zify_lit_hook.
