(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.CJ.Lib Require Export Ceil.
From Ltac2 Require Import Ltac2.
From Ltac2 Require FSet.
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
Ltac2 Type zt_heads := { zh_rel : constant list; zh_not : constant; zh_iff : constant;
                         zh_and : inductive; zh_or : inductive; zh_ex : inductive; zh_eq : inductive; zh_le : inductive;
                         zh_true : inductive; zh_false : inductive }.
Ltac2 zt_cref (r : Std.reference) : constant := match r with Std.ConstRef c => c | _ => Control.throw Not_found end.
Ltac2 zt_iref (r : Std.reference) : inductive := match r with Std.IndRef c => c | _ => Control.throw Not_found end.
Ltac2 zt_mk_heads () : zt_heads :=
  { zh_rel := [zt_cref reference:(Z.le); zt_cref reference:(Z.lt); zt_cref reference:(Z.ge); zt_cref reference:(Z.gt);
               zt_cref reference:(lt); zt_cref reference:(ge); zt_cref reference:(gt);
               zt_cref reference:(N.le); zt_cref reference:(N.lt); zt_cref reference:(Z.divide)];
    zh_not := zt_cref reference:(not); zh_iff := zt_cref reference:(iff);
    zh_and := zt_iref reference:(and); zh_or := zt_iref reference:(or); zh_ex := zt_iref reference:(ex);
    zh_eq := zt_iref reference:(eq); zh_le := zt_iref reference:(le);
    zh_true := zt_iref reference:(True); zh_false := zt_iref reference:(False) }.
Ltac2 rec zt_cls (hd : zt_heads) (t : constr) : int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ =>
          if List.exist (Constant.equal c) (hd.(zh_rel)) then 2
          else if Constant.equal c (hd.(zh_not)) then 0 else if Constant.equal c (hd.(zh_iff)) then 0
          else 1
      | Constr.Unsafe.Ind i _ =>
          if Ind.equal i (hd.(zh_and)) then
            (let a := zt_cls hd (Array.get args 0) in
             if Int.equal a 0 then 0 else
             let b := zt_cls hd (Array.get args 1) in
             if Int.equal b 0 then 0 else if Int.equal a 2 then 2 else b)
          else if Ind.equal i (hd.(zh_eq)) then 2 else if Ind.equal i (hd.(zh_le)) then 2
          else if Ind.equal i (hd.(zh_or)) then 0 else if Ind.equal i (hd.(zh_ex)) then 0
          else 1
      | Constr.Unsafe.Var _ => 1
      | _ => 0
      end
  | Constr.Unsafe.Ind i _ => if Ind.equal i (hd.(zh_true)) then 2 else if Ind.equal i (hd.(zh_false)) then 2 else 1
  | Constr.Unsafe.Constant _ _ => 1
  | Constr.Unsafe.Var _ => 1
  | _ => 0
  end.
Ltac2 zt_plain_mixed (hd : zt_heads) (t : constr) : bool := Int.equal (zt_cls hd t) 2.

(* [comment removed for export] *)
Ltac2 zt_prune () : unit :=
  let hd := zt_mk_heads () in
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if zt_plain_mixed hd ty then None
                          else if Bool.and (zt_is_local id) (zt_is_prop ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.

Ltac zify_prune := ltac2:(Control.enter zt_prune).

(* [comment removed for export] *)
Ltac zify_noeuclid :=
  intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module LC0.
Import Ltac2.

Ltac2 Type vset := ident FSet.t.
Ltac2 vempty () : vset := FSet.empty FSet.Tags.ident_tag.
Ltac2 Type budget := { mutable left : int }.
Ltac2 rec vars_acc_b (num : constr list) (bg : budget) (acc : vset) (t : constr) : vset :=
  if Int.le (bg.(left)) 0 then acc else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id => FSet.add id acc
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constructor _ _ => if List.exist (Constr.equal f) num then acc
           else (bg.(left) := Int.sub (bg.(left)) 1; Array.fold_left (vars_acc_b num bg) acc args)
       | _ => (bg.(left) := Int.sub (bg.(left)) 1; Array.fold_left (vars_acc_b num bg) (vars_acc_b num bg acc f) args)
       end)
  | Constr.Unsafe.Prod b c => vars_acc_b num bg (vars_acc_b num bg acc (Constr.Binder.type b)) c
  | Constr.Unsafe.Lambda b c => vars_acc_b num bg (vars_acc_b num bg acc (Constr.Binder.type b)) c
  | Constr.Unsafe.LetIn b v c => vars_acc_b num bg (vars_acc_b num bg (vars_acc_b num bg acc (Constr.Binder.type b)) v) c
  | Constr.Unsafe.Cast c _ ty => vars_acc_b num bg (vars_acc_b num bg acc c) ty
  | Constr.Unsafe.Case _ _ _ scr brs => Array.fold_left (vars_acc_b num bg) (vars_acc_b num bg acc scr) brs
  | Constr.Unsafe.Proj _ _ c => vars_acc_b num bg acc c
  | _ => acc
  end.
Ltac2 numerals () : constr list := ['Zpos; 'Zneg; 'Npos; 'xI; 'xO].
Ltac2 vars_acc_n (num : constr list) (acc : vset) (t : constr) : vset := vars_acc_b num { left := 300 } acc t.

Ltac2 Type heads := { h_rel : constr list; h_not : constr; h_iff : constr;
                      h_and : constr; h_or : constr; h_eq : constr; h_le : constr;
                      h_true : constr; h_false : constr; h_types : constr list }.
Ltac2 mk_heads () : heads :=
  { h_rel := ['@Z.le; '@Z.lt; '@Z.ge; '@Z.gt; '@lt; '@ge; '@gt; '@N.le; '@N.lt; '@Z.divide];
    h_not := '@not; h_iff := '@iff; h_and := '@and; h_or := '@or; h_eq := '@eq; h_le := '@le;
    h_true := 'True; h_false := 'False; h_types := ['Z; 'nat; 'N; 'bool] }.
Ltac2 cmem (c : constr) (l : constr list) : bool := List.exist (Constr.equal c) l.

(* [comment removed for export] *)
Ltac2 rec fast_al (hd : heads) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if cmem h (hd.(h_rel)) then true
          else if Constr.equal h (hd.(h_not)) then fast_al hd (Array.get args 0)
          else if Constr.equal h (hd.(h_iff)) then (if fast_al hd (Array.get args 0) then fast_al hd (Array.get args 1) else false)
          else false
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h (hd.(h_and)) then (if fast_al hd (Array.get args 0) then fast_al hd (Array.get args 1) else false)
          else if Constr.equal h (hd.(h_or)) then (if fast_al hd (Array.get args 0) then fast_al hd (Array.get args 1) else false)
          else if Constr.equal h (hd.(h_eq)) then cmem (Array.get args 0) (hd.(h_types))
          else Constr.equal h (hd.(h_le))
      | _ => false
      end
  | Constr.Unsafe.Prod b c => if fast_al hd (Constr.Binder.type b) then fast_al hd c else false
  | Constr.Unsafe.Ind _ _ => if Constr.equal t (hd.(h_true)) then true else Constr.equal t (hd.(h_false))
  | _ => false
  end.

Ltac2 meets (a : vset) (b : vset) : bool := Bool.neg (FSet.is_empty (FSet.inter a b)).

(* [comment removed for export] *)
Ltac2 rec closure (vs : vset) (cands : (ident * vset) list) (fuel : int) : vset :=
  if Int.le fuel 0 then vs else
  let (vs2, rest, changed) := List.fold_left (fun (acc : vset * (ident * vset) list * bool) (c : ident * vset) =>
      let (vs1, rest1, ch) := acc in
      let (id, hv) := c in
      if (if FSet.mem id vs1 then true else meets hv vs1)
      then (FSet.add id (FSet.union hv vs1), rest1, true)
      else (vs1, c :: rest1, ch)) (vs, [], false) cands in
  if changed then closure vs2 rest (Int.sub fuel 1) else vs2.

(* [comment removed for export] *)
Ltac2 prune_logic () : unit :=
  let hd := mk_heads () in
  let zhd := zt_mk_heads () in
  let fast_plain (_ : heads) (t : constr) := zt_plain_mixed zhd t in
  let num := numerals () in
  let vars (t : constr) := vars_acc_n num (vempty ()) t in
  let hs := Control.hyps () in
  let vg := vars (Control.goal ()) in
  let lc := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if fast_plain hd ty then None else if fast_al hd ty then
                  (let hv := vars ty in if meets hv vg then Some (id, hv) else None) else None
      end) hs in
  match lc with
  | [] => Control.zero (Tactic_failure None)
  | _ :: _ =>
  let pc := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some b => if cmem ty (hd.(h_types)) then Some (id, vars b) else None
      | None => if fast_plain hd ty then Some (id, vars ty) else None
      end) hs in
  let vl := List.fold_left (fun (acc : vset) (c : ident * vset) => let (_, hv) := c in FSet.union hv acc) vg lc in
  let vs := closure vl pc 50 in
  let closed := List.map_filter (fun (c : ident * vset) => let (i, hv) := c in if FSet.is_empty hv then Some i else None) pc in
  let keep (id : ident) := if FSet.mem id vs then true
    else if List.exist (fun (c : ident * vset) => let (i, _) := c in Ident.equal i id) lc then true
    else List.exist (Ident.equal id) closed in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if keep id then None
                else if zt_is_local id then (if zt_is_prop ty then Some id else None)
                else None
      end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end
  end.
End LC0.
Ltac zify_prune_closure := ltac2:(Control.enter LC0.prune_logic).

(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune;                                        (* [comment removed for export] *)
          first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                | Zify.zify; xlia zchecker ]
        | zify_prune_closure; Zify.zify; xlia zchecker       (* [comment removed for export] *)
        | Zify.zify; xlia zchecker ].


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition natZ (z : Z) : nat := Z.to_nat z.
Lemma natZ_pos (p : positive) : Z.of_nat (natZ (Z.pos p)) = Z.pos p.
Proof. unfold natZ. apply Z2Nat.id. apply Pos2Z.is_nonneg. Qed.

(* [comment removed for export] *)
Ltac is_pos_lit p := lazymatch p with xI ?q => is_pos_lit q | xO ?q => is_pos_lit q | xH => idtac end.
(* [comment removed for export] *)
Ltac natlit_z l k :=
  lazymatch l with
  | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))))))))))))))))))))) =>
      let z := eval vm_compute in (Z.of_nat l) in
      lazymatch z with Zpos ?p => is_pos_lit p; k z p end
  end.
Ltac note_natZ z p :=
  lazymatch goal with
  | _ : Z.of_nat (natZ z) = _ |- _ => idtac
  | _ => pose proof (natZ_pos p : Z.of_nat (natZ z) = z)
  end.
Ltac nat_diet_step :=
  match goal with
  | H : @eq nat ?a ?l |- _ => natlit_z l ltac:(fun z p => change (@eq nat a (natZ z)) in H; note_natZ z p)
  | H : @eq nat ?l ?a |- _ => natlit_z l ltac:(fun z p => change (@eq nat (natZ z) a) in H; note_natZ z p)
  | H : le ?a ?l |- _ => natlit_z l ltac:(fun z p => change (le a (natZ z)) in H; note_natZ z p)
  | H : le ?l ?a |- _ => natlit_z l ltac:(fun z p => change (le (natZ z) a) in H; note_natZ z p)
  | H : lt ?a ?l |- _ => natlit_z l ltac:(fun z p => change (lt a (natZ z)) in H; note_natZ z p)
  | H : lt ?l ?a |- _ => natlit_z l ltac:(fun z p => change (lt (natZ z) a) in H; note_natZ z p)
  | |- @eq nat ?a ?l => natlit_z l ltac:(fun z p => change (@eq nat a (natZ z)); note_natZ z p)
  | |- @eq nat ?l ?a => natlit_z l ltac:(fun z p => change (@eq nat (natZ z) a); note_natZ z p)
  | |- le ?a ?l => natlit_z l ltac:(fun z p => change (le a (natZ z)); note_natZ z p)
  | |- le ?l ?a => natlit_z l ltac:(fun z p => change (le (natZ z) a); note_natZ z p)
  | |- lt ?a ?l => natlit_z l ltac:(fun z p => change (lt a (natZ z)); note_natZ z p)
  | |- lt ?l ?a => natlit_z l ltac:(fun z p => change (lt (natZ z) a); note_natZ z p)
  | H : context C [Z.of_nat ?l] |- _ => natlit_z l ltac:(fun z p => let T := context C [z] in change T in H)
  | |- context C [Z.of_nat ?l] => natlit_z l ltac:(fun z p => let T := context C [z] in change T)
  end.
Ltac nat_diet := repeat nat_diet_step.

(* [comment removed for export] *)
Ltac Zify.zify_pre_hook ::= nat_diet; ceil_saturate.

(* [comment removed for export] *)
Ltac zify_noceil_diet := intros; nat_diet; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate;
  Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Ltac Lia.nia ::= first [ zify_noceil_diet; xnia zchecker | Zify.zify; xnia zchecker ].
