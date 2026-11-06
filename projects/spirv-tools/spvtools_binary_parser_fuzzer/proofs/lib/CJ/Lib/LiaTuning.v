(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
#[global] Set Default Proof Mode "Classic".

From stdpp.bitvector Require Import tactics.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition zify_done (x y : Z) : Prop := True.
Definition zify_done_qr (x y : Z) : Prop := True.
End AC_1.

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

Ltac Zify.zify_internal_to_euclidean_division_equations ::= zify_fast_euclid.

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

Ltac zify_noeuclid :=
  intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook.

Ltac2 rec zt_plain_arith2 (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if Constr.equal h '@not then zt_plain_arith2 (Array.get args 0) else zt_plain_arith t
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h '@and then (if zt_plain_arith2 (Array.get args 0) then zt_plain_arith2 (Array.get args 1) else false)
          else if Constr.equal h '@or then (if zt_plain_arith2 (Array.get args 0) then zt_plain_arith2 (Array.get args 1) else false)
          else zt_plain_arith t
      | _ => false
      end
  | _ => zt_plain_arith t
  end.

Ltac2 zt_is_arith_head (h : constr) : bool :=
  if Constr.equal h '@Z.add then true else if Constr.equal h '@Z.sub then true
  else if Constr.equal h '@Z.mul then true else if Constr.equal h '@Z.opp then true
  else if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
  else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
  else if Constr.equal h '@not then true else if Constr.equal h '@and then true
  else if Constr.equal h '@or then true else if Constr.equal h '@eq then true
  else if Constr.equal h '@Z.of_nat then true else false.

Ltac2 rec zt_atoms (t : constr) (acc : constr list) : constr list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if zt_is_arith_head h then Array.fold_right (fun a acc => zt_atoms a acc) args acc
      else (match Constr.Unsafe.kind h with
            | Constr.Unsafe.Constructor _ _ => acc
            | _ => t :: acc end)
  | Constr.Unsafe.Var _ => t :: acc
  | _ => acc
  end.
Ltac2 zt_shares (a : constr list) (b : constr list) : bool :=
  List.exist (fun x => List.exist (fun y => Constr.equal x y) b) a.
Ltac2 zt_prune_rel () : unit :=
  let goal_atoms := zt_atoms (Control.goal ()) [] in
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if zt_plain_arith ty then None
                          else if Bool.and (zt_plain_arith2 ty) (zt_shares (zt_atoms ty []) goal_atoms) then None
                          else if Bool.and (zt_is_local id) (zt_is_prop ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zify_prune_rel := ltac2:(Control.enter zt_prune_rel).

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | zify_prune_rel; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
