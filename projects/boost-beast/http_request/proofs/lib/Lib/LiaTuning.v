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
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec zt_twoway (t : constr) : bool :=
  lazy_match! t with
  | ?a \/ ?b => Bool.and (zt_twoway a) (zt_twoway b)
  | ?a /\ ?b => Bool.and (zt_twoway a) (zt_twoway b)
  | not ?a => zt_twoway a
  | _ => zt_plain_arith t
  end.

(* [comment removed for export] *)
Ltac2 zt_twoway_hyps () : ident list :=
  List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if zt_plain_arith ty then None
                else if Bool.and (zt_is_local id) (Bool.and (zt_is_prop ty) (zt_twoway ty)) then Some id else None
      end) (Control.hyps ()).

(* [comment removed for export] *)
Ltac2 zt_prune_but (keep : ident -> constr -> bool) : unit :=
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if zt_plain_arith ty then None
                else if keep id ty then None
                else if Bool.and (zt_is_local id) (zt_is_prop ty) then Some id else None
      end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.

Ltac2 rec zt_first_of (ids : ident list) (k : ident -> unit) : unit :=
  match ids with
  | [] => Control.zero (Tactic_failure None)
  | i :: rest => Control.plus (fun () => k i) (fun _ => zt_first_of rest k)
  end.

(* [comment removed for export] *)
Ltac xlia_noeuclid := zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.

Ltac2 zt_lia_oneway () : unit :=
  let ids := List.rev (zt_twoway_hyps ()) in
  match ids with
  | [] => Control.zero (Tactic_failure None)
  | _ :: _ => Control.once (fun () => zt_first_of ids (fun i => zt_prune_but (fun id _ => Ident.equal id i); ltac1:(xlia_noeuclid)))
  end.
Ltac lia_oneway := ltac2:(Control.enter zt_lia_oneway).
Ltac zify_prune_twoway := ltac2:(Control.enter (fun () => zt_prune_but (fun _ ty => zt_twoway ty))).

Ltac lia2w :=
  first [ zify_prune; xlia_noeuclid
        | lia_oneway
        | zify_prune_twoway; xlia_noeuclid
        | zify_prune; Zify.zify; xlia zchecker
        | zify_prune_twoway; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac2 zt_local_hyp (c : constr) : unit :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id => if zt_is_local id then () else Control.zero (Tactic_failure None)
  | _ => Control.zero (Tactic_failure None)
  end.
Ltac is_local_hyp H := let f := ltac2:(c |- zt_local_hyp (Option.get (Ltac1.to_constr c))) in f H.

(* [comment removed for export] *)
Ltac slia_nrange :=
  lazymatch goal with
  | |- ~ _ =>
      let R := fresh "R" in intro R;
      repeat match goal with K : (~ _) /\ _ |- _ => is_local_hyp K; destruct K as [? ?] end;
      match goal with K : ~ _ |- _ => is_local_hyp K; apply K; split; zify_prune; xlia_noeuclid end
  end.
Ltac slia2w_atom := first [ exact I | slia_nrange | lia2w ].
Ltac slia2w := first [ exact I | lazymatch goal with |- _ /\ _ => split; [slia2w_atom | slia2w] end | slia2w_atom ].
