(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".

From stdpp.bitvector Require Import tactics.

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
        | (0 <= _ < _)%Z =>

            let c := Control.hyp id in ltac1:(c |- generalize c; intros _) (Ltac1.of_constr c)
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

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Module LR.
  Import Ltac2.
  Ltac2 kof (r : Std.reference) : constant := match r with Std.ConstRef k => k | _ => Control.throw Not_found end.
  Ltac2 iof (r : Std.reference) : inductive := match r with Std.IndRef k => k | _ => Control.throw Not_found end.
  Ltac2 is_cmp_head (h : constr) : bool :=
    match Constr.Unsafe.kind h with
    | Constr.Unsafe.Constant k _ =>
        if Constant.equal k (kof reference:(Z.le)) then true else if Constant.equal k (kof reference:(Z.lt)) then true
        else if Constant.equal k (kof reference:(Z.ge)) then true else if Constant.equal k (kof reference:(Z.gt)) then true
        else if Constant.equal k (kof reference:(lt)) then true else if Constant.equal k (kof reference:(ge)) then true
        else if Constant.equal k (kof reference:(gt)) then true else if Constant.equal k (kof reference:(N.le)) then true
        else if Constant.equal k (kof reference:(N.lt)) then true else Constant.equal k (kof reference:(Z.divide))
    | Constr.Unsafe.Ind i _ => Ind.equal i (iof reference:(le))
    | _ => false
    end.
  Ltac2 is_ind (r : Std.reference) (h : constr) : bool :=
    match Constr.Unsafe.kind h with
    | Constr.Unsafe.Ind i _ => Ind.equal i (iof r)
    | _ => false
    end.

  Ltac2 is_arith_ty (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Ind i _ =>
        if Ind.equal i (iof reference:(Z)) then true else if Ind.equal i (iof reference:(nat)) then true
        else if Ind.equal i (iof reference:(N)) then true else if Ind.equal i (iof reference:(positive)) then true
        else Ind.equal i (iof reference:(bool))
    | _ => false
    end.

  Ltac2 is_atom (h : constr) (args : constr array) : bool :=
    if is_cmp_head h then true
    else if is_ind reference:(eq) h then (if Int.equal (Array.length args) 3 then is_arith_ty (Array.get args 0) else false)
    else false.

  Ltac2 rec alogic (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args =>
        if is_atom h args then true
        else if is_ind reference:(and) h then (if alogic (Array.get args 0) then alogic (Array.get args 1) else false)
        else if is_ind reference:(or) h then (if alogic (Array.get args 0) then alogic (Array.get args 1) else false)
        else if (match Constr.Unsafe.kind h with Constr.Unsafe.Constant k _ => Constant.equal k (kof reference:(iff)) | _ => false end) then (if alogic (Array.get args 0) then alogic (Array.get args 1) else false)
        else if (match Constr.Unsafe.kind h with Constr.Unsafe.Constant k _ => Constant.equal k (kof reference:(not)) | _ => false end) then alogic (Array.get args 0)
        else false
    | Constr.Unsafe.Prod b body =>

        if Constr.Unsafe.noccur_between 1 1 body then
          (if alogic (Constr.Binder.type b) then alogic body else false)
        else false
    | Constr.Unsafe.Ind i _ => if Ind.equal i (iof reference:(True)) then true else Ind.equal i (iof reference:(False))
    | _ => false
    end.

  Ltac2 is_local (id : ident) : bool :=
    match Env.get [id] with None => true | Some _ => false end.

  Ltac2 rec has_var (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Var _ => true
    | Constr.Unsafe.Constant _ _ =>
        (match Constr.Unsafe.kind (Constr.type c) with
         | Constr.Unsafe.Sort _ => false
         | Constr.Unsafe.Prod _ _ => false
         | _ => true
         end)
    | Constr.Unsafe.App f args =>
        if (match Constr.Unsafe.kind f with
            | Constr.Unsafe.Constant _ _ => false
            | Constr.Unsafe.Constructor _ _ => false
            | Constr.Unsafe.Ind _ _ => false
            | _ => has_var f
            end) then true
        else has_var_arr args 0 (Array.length args)
    | Constr.Unsafe.Prod b body => if has_var (Constr.Binder.type b) then true else has_var body
    | Constr.Unsafe.Lambda b body => if has_var (Constr.Binder.type b) then true else has_var body
    | Constr.Unsafe.LetIn _ v body => if has_var v then true else has_var body
    | Constr.Unsafe.Cast c' _ _ => has_var c'
    | Constr.Unsafe.Case _ _ _ scr brs => if has_var scr then true else has_var_arr brs 0 (Array.length brs)
    | Constr.Unsafe.Proj _ _ c' => has_var c'
    | _ => false
    end
  with has_var_arr (a : constr array) (i : int) (n : int) : bool :=
    if Int.ge i n then false
    else if has_var (Array.get a i) then true
    else has_var_arr a (Int.add i 1) n.

  Ltac2 classify (id : ident) (ty : constr) : int :=
    if zt_plain_arith ty then 1
    else if alogic ty then (if has_var ty then 2 else 0)
    else if is_local id then (if zt_is_prop ty then 3 else 0)
    else 0.

  Ltac2 prune_a0 () : unit :=
    let ids := List.fold_left (fun acc h => let (id, body, ty) := h in
        match body with
        | Some _ => acc
        | None => let k := classify id ty in if Int.le 2 k then id :: acc else acc
        end) [] (Control.hyps ()) in
    match ids with [] => () | _ :: _ => Std.clear ids end.

  Ltac2 clear_props () : unit :=
    let ids := List.fold_left (fun acc h => let (id, body, ty) := h in
        match body with
        | Some _ => acc
        | None => if zt_plain_arith ty then id :: acc else if alogic ty then id :: acc
                  else if zt_is_prop ty then id :: acc else acc
        end) [] (Control.hyps ()) in
    match ids with [] => () | _ :: _ => Std.clear ids end.
  Ltac2 clear_props_1 () : unit := Control.enter clear_props.

  Ltac2 rec concl (c : constr) : constr :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Prod _ body => concl body
    | Constr.Unsafe.LetIn _ _ body => concl body
    | Constr.Unsafe.Cast c' _ _ => concl c'
    | _ => c
    end.

  Ltac2 rec arith_premise (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Prod b body => if alogic (Constr.Binder.type b) then true else arith_premise body
    | Constr.Unsafe.LetIn _ _ body => arith_premise body
    | Constr.Unsafe.Cast c' _ _ => arith_premise c'
    | _ => false
    end.
  Ltac2 goal_arith () : unit :=
    let g := Control.goal () in
    if alogic g then () else if alogic (concl g) then () else if arith_premise g then ()
    else Control.zero (Tactic_failure None).

  Ltac2 rec b1_collect (si : ident FSet.t ref) (c : constr) : unit :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Var id => si.(contents) := FSet.add id (si.(contents))
    | Constr.Unsafe.App f args => b1_collect si f; Array.iter (b1_collect si) args
    | Constr.Unsafe.Prod b body => b1_collect si (Constr.Binder.type b); b1_collect si body
    | Constr.Unsafe.Lambda b body => b1_collect si (Constr.Binder.type b); b1_collect si body
    | Constr.Unsafe.LetIn b v body => b1_collect si v; b1_collect si body
    | Constr.Unsafe.Cast c' _ _ => b1_collect si c'
    | Constr.Unsafe.Case _ _ _ scr brs => b1_collect si scr; Array.iter (b1_collect si) brs
    | Constr.Unsafe.Proj _ _ c' => b1_collect si c'
    | _ => ()
    end.
  Ltac2 rec b1_mentions (gi : ident FSet.t) (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Var id => FSet.mem id gi
    | Constr.Unsafe.App f args => if b1_mentions gi f then true else b1_mentions_arr gi args 0 (Array.length args)
    | Constr.Unsafe.Prod b body => if b1_mentions gi (Constr.Binder.type b) then true else b1_mentions gi body
    | Constr.Unsafe.Lambda b body => if b1_mentions gi (Constr.Binder.type b) then true else b1_mentions gi body
    | Constr.Unsafe.LetIn _ v body => if b1_mentions gi v then true else b1_mentions gi body
    | Constr.Unsafe.Cast c' _ _ => b1_mentions gi c'
    | Constr.Unsafe.Case _ _ _ scr brs => if b1_mentions gi scr then true else b1_mentions_arr gi brs 0 (Array.length brs)
    | Constr.Unsafe.Proj _ _ c' => b1_mentions gi c'
    | _ => false
    end
  with b1_mentions_arr (gi : ident FSet.t) (a : constr array) (i : int) (n : int) : bool :=
    if Int.ge i n then false else if b1_mentions gi (Array.get a i) then true else b1_mentions_arr gi a (Int.add i 1) n.
  Ltac2 b1_poison_set () : constant FSet.t :=
    List.fold_left (fun s r => match r with Std.ConstRef k => FSet.add k s | _ => s end)
      (FSet.empty FSet.Tags.constant_tag)
      [reference:(Z.to_nat); reference:(Z.min); reference:(Z.max); reference:(Z.abs); reference:(Nat.sub);
       reference:(Nat.min); reference:(Nat.max)].
  Ltac2 rec b1_has_poison (ps : constant FSet.t) (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if (match Constr.Unsafe.kind f with Constr.Unsafe.Constant k _ => FSet.mem k ps | _ => false end) then true
        else b1_has_poison_arr ps args 0 (Array.length args)
    | _ => false
    end
  with b1_has_poison_arr (ps : constant FSet.t) (a : constr array) (i : int) (n : int) : bool :=
    if Int.ge i n then false else if b1_has_poison ps (Array.get a i) then true else b1_has_poison_arr ps a (Int.add i 1) n.

  Ltac2 prune_b1d () : unit :=
    let g := Control.goal () in
    let gi := { contents := FSet.empty FSet.Tags.ident_tag } in
    (if alogic g then b1_collect gi g else ());

    (if FSet.is_empty (gi.(contents)) then
       (let rec seed (n : int) (l : (ident * constr option * constr) list) : unit :=
          if Int.le n 0 then () else
          match l with
          | [] => ()
          | h :: l' =>
              let (id, body, ty) := h in
              (match body with
               | Some _ => seed n l'
               | None => if (if is_local id then alogic ty else false) then (b1_collect gi ty; seed (Int.sub n 1) l') else seed n l'
               end)
          end in
        seed 4 (List.rev (Control.hyps ())))
     else ());
    let ps := b1_poison_set () in
    let kept := { contents := false } in
    let nkept := { contents := 0 } in
    let ids := List.fold_left (fun acc h => let (id, body, ty) := h in
        match body with
        | Some _ => acc
        | None =>
            let k := classify id ty in
            if Int.equal k 3 then id :: acc
            else if Int.equal k 2 then (if b1_mentions (gi.(contents)) ty then (kept.(contents) := true; nkept.(contents) := Int.add 1 (nkept.(contents)); acc) else id :: acc)
            else if Int.equal k 1 then
              (if alogic ty then
                 (if b1_has_poison ps ty then (if b1_mentions (gi.(contents)) ty then (kept.(contents) := true; nkept.(contents) := Int.add 1 (nkept.(contents)); acc) else id :: acc) else acc)
               else acc)
            else acc
        end) [] (Control.hyps ()) in
    (if kept.(contents) then () else Control.zero (Tactic_failure None));

    (if Int.lt 5 (nkept.(contents)) then Control.zero (Tactic_failure None) else ());
    match ids with [] => () | _ :: _ => Std.clear ids end.
  Ltac2 prune_b1d_1 () : unit := Control.enter prune_b1d.
  Ltac2 prune_a0_1 () : unit := Control.enter prune_a0.
End LR.

Module LRS.
  Import Ltac2.
  Ltac2 is_prop_ty (t : constr) : bool :=
    match Control.case (fun () => Constr.type t) with
    | Val (ty, _) => (match Constr.Unsafe.kind ty with Constr.Unsafe.Sort _ => Constr.equal ty 'Prop | _ => false end)
    | Err _ => false
    end.
  Ltac2 spec_cand (ty : constr) : bool :=
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.Prod b body =>
        if Constr.Unsafe.noccur_between 1 1 body then
          (if is_prop_ty (Constr.Binder.type b) then true else
           match Constr.Unsafe.kind body with
           | Constr.Unsafe.Prod b2 body2 =>
               if Constr.Unsafe.noccur_between 1 1 body2 then is_prop_ty (Constr.Binder.type b2) else false
           | _ => false
           end)
        else false
    | _ => false
    end.
  Ltac2 rec spec_loop () : unit :=
    let cs := List.rev (List.map_filter (fun h => let (id, _, ty) := h in if spec_cand ty then Some id else None) (Control.hyps ())) in
    let rec go (l : ident list) : bool :=
      match l with
      | [] => false
      | id :: l' =>
          let c := Control.hyp id in
          match Control.case (fun () => ltac1:(h |- zify_spec_hyp h) (Ltac1.of_constr c)) with
          | Val _ => true
          | Err _ => go l'
          end
      end in
    if go cs then spec_loop () else ().
  Ltac2 spec_loop1 () : unit := Control.enter spec_loop.
End LRS.
Ltac zify_spec_trivial ::= ltac2:(LRS.spec_loop1 ()).

Ltac zify_prune_a0 := ltac2:(LR.prune_a0_1 ()).

Ltac zify_clear_poison :=
  repeat match goal with
  | H : context [Z.to_nat _] |- _ => clear H
  | H : context [Nat.sub _ _] |- _ => clear H
  | H : context [Nat.min _ _] |- _ => clear H
  | H : context [Nat.max _ _] |- _ => clear H
  | H : context [Z.min _ _] |- _ => clear H
  | H : context [Z.max _ _] |- _ => clear H
  | H : context [Z.abs _] |- _ => clear H
  end.
Ltac lia_a0 := zify_prune_a0; zify_clear_poison; Z.euclidean_division_equations_cleanup; zify_noeuclid; xlia zchecker.
Ltac lia_old1 := zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac lia_old2 := zify_prune; Zify.zify; xlia zchecker.
Ltac lia_tiers3 := first [ lia_old1 | lia_old2 | Zify.zify; xlia zchecker ].
Ltac zify_clear_props := ltac2:(LR.clear_props_1 ()).
Ltac lia_goal_arith0 := ltac2:(Control.enter LR.goal_arith).

Ltac lia_goal_arith := first [ lia_goal_arith0 | assert_succeeds (intros; cbv beta; lia_goal_arith0) ].
Ltac lia_absurd :=
  lia_goal_arith;
  lazymatch goal with |- ?G => assert_succeeds (assert (~ G) by (zify_clear_props; intro; zify_noeuclid; xlia zchecker)) end.

Ltac plia_cheap := first [ lia_a0 | lia_old1 | lia_old2 ].
Ltac lia_b1d := ltac2:(LR.prune_b1d_1 ()); Z.euclidean_division_equations_cleanup; zify_noeuclid; xlia zchecker.

Ltac lia_v1 := first [ lia_a0 | lia_old1 | lia_old2 | Zify.zify; xlia zchecker ].
Ltac lia ::= first [ lia_a0 | lia_b1d | lia_old1 | lia_old2 | Zify.zify; xlia zchecker ].

Ltac alia := lia_goal_arith; lia.

Ltac ctauto :=
  first [ solve [ repeat (first [ exact I | assumption | timeout 2 reflexivity | split ]) ]   (* timeout-ok: fast tier: expiry takes the later arm (split or right) of this repeat-first *)
        | solve [ repeat (first [ left; timeout 2 reflexivity | right ]) ]   (* timeout-ok: fast tier: expiry takes the later arm (split or right) of this repeat-first *)
        | tauto ].
