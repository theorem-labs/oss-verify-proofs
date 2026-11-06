(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[global] Set Default Proof Mode "Classic".
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo9G.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Qo9G.

From stdpp.bitvector Require Import tactics.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[global] Unset Lia Cache.
#[global] Unset Nia Cache.
#[global] Unset Nra Cache.

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

Ltac zify_not_eqlike T :=
lazymatch T with
| Z.le _ _ => idtac | Z.ge _ _ => idtac | N.le _ _ => idtac | N.ge _ _ => idtac | not _ => idtac
| and _ _ => idtac | or _ _ => idtac | iff _ _ => idtac | True => idtac | False => idtac
| Peano.le _ _ => idtac | Peano.lt _ _ => idtac | Peano.ge _ _ => idtac | Peano.gt _ _ => idtac
| forall _, _ => idtac
end.
Ltac zify_spec_premise H T :=
lazymatch type of T with
| Prop => first [ tryif zify_not_eqlike T then fail else specialize (H (@eq_refl _ _ : T))
| tryif zify_arith_prop T then fail else specialize (H ltac:(assumption)) ]
end.
Ltac zify_spec_premise2 H A T :=
lazymatch type of T with
| Prop => first [ tryif zify_not_eqlike T then fail else specialize (fun a : A => H a (@eq_refl _ _ : T))
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
Ltac Z.euclidean_division_equations_cleanup ::= zify_cheap_cleanup. Ltac mkr__euclidean_division_equations_cleanup_4 := zify_cheap_cleanup.

Ltac zify_fast_euclid :=
Z.divide_to_equations';
first [ progress (repeat zify_dm_step; repeat zify_qr_step); cbv beta | idtac ];
Z.euclidean_division_equations_cleanup.

Ltac Zify.zify_internal_to_euclidean_division_equations ::= zify_fast_euclid. Ltac mkr__zify_internal_to_euclidean_division_equations_5 := zify_fast_euclid.

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

Ltac2 Type zk := { k_zle : constr; k_zlt : constr; k_zge : constr; k_zgt : constr; k_lt : constr; k_ge : constr; k_gt : constr;
k_nle : constr; k_nlt : constr; k_zdiv : constr; k_and : constr; k_eq : constr; k_le : constr;
k_true : constr; k_false : constr; k_prop : constr }.
Ltac2 zk_mk () : zk := { k_zle := '@Z.le; k_zlt := '@Z.lt; k_zge := '@Z.ge; k_zgt := '@Z.gt; k_lt := '@lt; k_ge := '@ge; k_gt := '@gt;
k_nle := '@N.le; k_nlt := '@N.lt; k_zdiv := '@Z.divide; k_and := '@and; k_eq := '@eq; k_le := '@le;
k_true := 'True; k_false := 'False; k_prop := 'Prop }.
Ltac2 rec zt_pa (kk : zk) (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h args =>
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ =>
if Constr.equal h (kk.(k_zle)) then true else if Constr.equal h (kk.(k_zlt)) then true
else if Constr.equal h (kk.(k_zge)) then true else if Constr.equal h (kk.(k_zgt)) then true
else if Constr.equal h (kk.(k_lt)) then true else if Constr.equal h (kk.(k_ge)) then true
else if Constr.equal h (kk.(k_gt)) then true else if Constr.equal h (kk.(k_nle)) then true
else if Constr.equal h (kk.(k_nlt)) then true else if Constr.equal h (kk.(k_zdiv)) then true
else false
| Constr.Unsafe.Ind _ _ =>
if Constr.equal h (kk.(k_and)) then (if zt_pa kk (Array.get args 0) then zt_pa kk (Array.get args 1) else false)
else if Constr.equal h (kk.(k_eq)) then true else if Constr.equal h (kk.(k_le)) then true
else false
| _ => false
end
| Constr.Unsafe.Ind _ _ => if Constr.equal t (kk.(k_true)) then true else Constr.equal t (kk.(k_false))
| _ => false
end.
Ltac2 zt_is_prop_k (kk : zk) (ty : constr) : bool :=
let h := zt_head (zt_codomain ty) in
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ => Constr.equal (zt_codomain (Constr.type h)) (kk.(k_prop))
| Constr.Unsafe.Ind _ _ => Constr.equal (zt_codomain (Constr.type h)) (kk.(k_prop))
| Constr.Unsafe.Var _ => Constr.equal (zt_codomain (Constr.type h)) (kk.(k_prop))
| _ => false
end.

Ltac2 zt_prune () : unit :=
let kk := zk_mk () in
let hs := Control.hyps () in
let ids := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None => if zt_pa kk ty then None
else if zt_is_local id then (if zt_is_prop_k kk ty then Some id else None) else None
end) hs in
match ids with [] => () | _ :: _ => Std.clear ids end.

Ltac zify_prune := ltac2:(Control.enter zt_prune).

Ltac zify_noeuclid :=
intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook.

Ltac zify_has_divmod :=
match goal with
| |- context [Z.div _ _] => idtac
| |- context [Z.modulo _ _] => idtac
| |- context [Z.quot _ _] => idtac
| |- context [Z.rem _ _] => idtac
| |- context [Z.divide _ _] => idtac
| |- context [Z.div2 _] => idtac
| |- context [Z.quot2 _] => idtac
| |- context [N.div _ _] => idtac
| |- context [N.div2 _] => idtac
| |- context [N.modulo _ _] => idtac
| |- context [Nat.div _ _] => idtac
| |- context [Nat.div2 _] => idtac
| |- context [Nat.modulo _ _] => idtac
| _ : context [Z.div _ _] |- _ => idtac
| _ : context [Z.modulo _ _] |- _ => idtac
| _ : context [Z.quot _ _] |- _ => idtac
| _ : context [Z.rem _ _] |- _ => idtac
| _ : context [Z.divide _ _] |- _ => idtac
| _ : context [Z.div2 _] |- _ => idtac
| _ : context [Z.quot2 _] |- _ => idtac
| _ : context [N.div _ _] |- _ => idtac
| _ : context [N.div2 _] |- _ => idtac
| _ : context [N.modulo _ _] |- _ => idtac
| _ : context [Nat.div _ _] |- _ => idtac
| _ : context [Nat.div2 _] |- _ => idtac
| _ : context [Nat.modulo _ _] |- _ => idtac
| _ := context [Z.div _ _] |- _ => idtac
| _ := context [Z.modulo _ _] |- _ => idtac
| _ := context [Z.quot _ _] |- _ => idtac
| _ := context [Z.rem _ _] |- _ => idtac
| _ := context [Z.divide _ _] |- _ => idtac
| _ := context [Z.div2 _] |- _ => idtac
| _ := context [Z.quot2 _] |- _ => idtac
| _ := context [N.div _ _] |- _ => idtac
| _ := context [N.div2 _] |- _ => idtac
| _ := context [N.modulo _ _] |- _ => idtac
| _ := context [Nat.div _ _] |- _ => idtac
| _ := context [Nat.div2 _] |- _ => idtac
| _ := context [Nat.modulo _ _] |- _ => idtac
end.
Ltac lia ::= term_slim ltac:(
first [ zify_prune;
first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
| zify_has_divmod; Zify.zify; xlia zchecker ]
| Zify.zify; xlia zchecker ]). Ltac mkr__lia_6 := term_slim ltac:(
first [ zify_prune;
first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
| zify_has_divmod; Zify.zify; xlia zchecker ]
| Zify.zify; xlia zchecker ]).
