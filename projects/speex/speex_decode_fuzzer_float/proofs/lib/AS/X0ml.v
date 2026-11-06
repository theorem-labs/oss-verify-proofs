(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[global] Set Default Proof Mode "Classic".

Definition zify_done (x y : Z) : Prop := True.
Definition zify_done_qr (x y : Z) : Prop := True.

Ltac zify_new_dm x y :=
lazymatch goal with
| _ : zify_done x y |- _ => fail
| _ => first [

let Hp := constr:(@eq_refl comparison Lt : (0 < y)%Z) in
pose proof (Z.div_mod x y);
pose proof (Z.mod_pos_bound x y Hp);
pose proof (I : zify_done x y)
| pose proof (Z.div_mod x y); pose proof (Z.mod_pos_bound x y); pose proof (Z.mod_neg_bound x y);
pose proof (Z.div_0_r_ext x y); pose proof (Z.mod_0_r_ext x y);
pose proof (I : zify_done x y) ]
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

Ltac zify_fast_euclid :=
Z.divide_to_equations';
first [ progress (repeat zify_dm_step; repeat zify_qr_step); cbv beta | idtac ];
Z.euclidean_division_equations_cleanup.

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

Ltac lia_tuned :=
first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
| zify_prune; Zify.zify; xlia zchecker
| Zify.zify; xlia zchecker ].

Local Open Scope Z_scope.
Ltac stock_euclid_cleanup :=
repeat
(repeat match goal with
| [ H : 0 <= ?x < _ |- _ ] =>
destruct H;
try (lazymatch type of H with
| 0 <= x < _ => clear H
end)

end;
repeat match goal with
| [ H : ?x <> ?x -> _ |- _ ] => clear H
| [ H : ?x < ?x -> _ |- _ ] => clear H
| [ H : ?T -> _, H' : ~?T |- _ ] => clear H
| [ H : ~?T -> _, H' : ?T |- _ ] => clear H
| [ H : ?A -> ?x <> ?x -> _ |- _ ] => clear H
| [ H : ?A -> ?x < ?x -> _ |- _ ] => clear H
| [ H : ?A -> ?B -> _, H' : ~?B |- _ ] => clear H
| [ H : ?A -> ~?B -> _, H' : ?B |- _ ] => clear H
| [ H : 0 < ?x -> _, H' : ?x < 0 |- _ ] => clear H
| [ H : ?x < 0 -> _, H' : 0 < ?x |- _ ] => clear H
| [ H : ?A -> 0 < ?x -> _, H' : ?x < 0 |- _ ] => clear H
| [ H : ?A -> ?x < 0 -> _, H' : 0 < ?x |- _ ] => clear H
| [ H : 0 <= ?x -> _, H' : ?x < 0 |- _ ] => clear H
| [ H : ?x <= 0 -> _, H' : 0 < ?x |- _ ] => clear H
| [ H : ?A -> 0 <= ?x -> _, H' : ?x < 0 |- _ ] => clear H
| [ H : ?A -> ?x <= 0 -> _, H' : 0 < ?x |- _ ] => clear H
| [ H : 0 < ?x -> _, H' : ?x <= 0 |- _ ] => clear H
| [ H : ?x < 0 -> _, H' : 0 <= ?x |- _ ] => clear H
| [ H : ?A -> 0 < ?x -> _, H' : ?x <= 0 |- _ ] => clear H
| [ H : ?A -> ?x < 0 -> _, H' : 0 <= ?x |- _ ] => clear H
| [ H : ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
| [ H : ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
| [ H : ?A -> ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
| [ H : ?A -> ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
| [ H : ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
| [ H : ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
| [ H : ?A -> ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
| [ H : ?A -> ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
end;
repeat match goal with
| [ H : ?x = ?x -> ?Q |- _ ] => specialize (H eq_refl)
| [ H : ?T -> ?Q, H' : ?T |- _ ] => specialize (H H')
| [ H : ?A -> ?x = ?x -> ?Q |- _ ] => specialize (fun a => H a eq_refl)
| [ H : ?A -> ?B -> ?Q, H' : ?B |- _ ] => specialize (fun a => H a H')
| [ H : 0 <= ?x -> ?Q, H' : ?x <= 0 |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x (eq_sym pf)))
| [ H : ?A -> 0 <= ?x -> ?Q, H' : ?x <= 0 |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl 0 x (eq_sym pf)))
| [ H : ?x <= 0 -> ?Q, H' : 0 <= ?x |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x pf))
| [ H : ?A -> ?x <= 0 -> ?Q, H' : 0 <= ?x |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl x 0 pf))
end).
