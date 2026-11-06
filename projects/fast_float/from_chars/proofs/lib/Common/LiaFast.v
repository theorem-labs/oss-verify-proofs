(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify.
From Ltac2 Require Import Ltac2.
From Ltac2 Require FSet FMap Constant Ind.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive U : Set := u0.
Definition lf_all : U := u0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition lf_pinned (A : Type) (a : A) : Prop := True.
Lemma lf_pinned_intro : forall (A : Type) (a : A), lf_pinned A a.
Proof. intros A a. exact I. Qed.
(* [comment removed for export] *)
#[global] Arguments lf_pinned : simpl never.
#[global] Opaque lf_pinned.
(* [comment removed for export] *)
Ltac lf_pins f := let H := fresh "__lf_pins" in pose proof (lf_pinned_intro _ f) as H.

Ltac2 lf_const (r : Std.reference) : constant :=
  match r with Std.ConstRef c => c | _ => Control.throw Not_found end.
Ltac2 lf_ind (r : Std.reference) : inductive :=
  match r with Std.IndRef i => i | _ => Control.throw Not_found end.

(* [comment removed for export] *)
Ltac2 lf_rel_consts () : constant FSet.t :=
  List.fold_left (fun s r => FSet.add (lf_const r) s) (FSet.empty FSet.Tags.constant_tag)
    [reference:(Z.le); reference:(Z.lt); reference:(Z.ge); reference:(Z.gt);
     reference:(Peano.lt); reference:(Peano.ge); reference:(Peano.gt);
     reference:(N.le); reference:(N.lt); reference:(N.ge); reference:(N.gt);
     reference:(Pos.le); reference:(Pos.lt); reference:(Pos.ge); reference:(Pos.gt);
     reference:(Z.divide)].
(* [comment removed for export] *)
Ltac2 lf_is_arith_type (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Ind i _ =>
      if Ind.equal i (lf_ind reference:(Z)) then true else if Ind.equal i (lf_ind reference:(nat)) then true
      else if Ind.equal i (lf_ind reference:(N)) then true else if Ind.equal i (lf_ind reference:(positive)) then true
      else if Ind.equal i (lf_ind reference:(bool)) then true else Ind.equal i (lf_ind reference:(comparison))
  | _ => false
  end.

Ltac2 rec lf_arith_shape (rels : constant FSet.t) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ =>
          if FSet.mem c rels then true
          else if Constant.equal c (lf_const reference:(not)) then lf_arith_shape rels (Array.get args 0)
          else if Constant.equal c (lf_const reference:(iff)) then
            (if lf_arith_shape rels (Array.get args 0) then lf_arith_shape rels (Array.get args 1) else false)
          else false
      | Constr.Unsafe.Ind i _ =>
          if Ind.equal i (lf_ind reference:(and)) then
            (if lf_arith_shape rels (Array.get args 0) then lf_arith_shape rels (Array.get args 1) else false)
          else if Ind.equal i (lf_ind reference:(or)) then
            (if lf_arith_shape rels (Array.get args 0) then lf_arith_shape rels (Array.get args 1) else false)
          else if Ind.equal i (lf_ind reference:(eq)) then lf_is_arith_type (Array.get args 0)
          else Ind.equal i (lf_ind reference:(Peano.le))
      | _ => false
      end
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then
        (if lf_arith_shape rels (Constr.Binder.type b) then lf_arith_shape rels c else false)
      else false
  | Constr.Unsafe.Ind i _ =>
      if Ind.equal i (lf_ind reference:(True)) then true else Ind.equal i (lf_ind reference:(False))
  | _ => false
  end.

Ltac2 rec lf_codomain (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ b => lf_codomain b
  | Constr.Unsafe.LetIn _ _ b => lf_codomain b
  | Constr.Unsafe.Cast c _ _ => lf_codomain c
  | _ => t
  end.
Ltac2 rec lf_head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => lf_head f
  | Constr.Unsafe.Cast c _ _ => lf_head c
  | _ => t
  end.
(* [comment removed for export] *)
Ltac2 lf_is_prop (ty : constr) : bool :=
  let h := lf_head (lf_codomain ty) in
  let sort_is_prop (t : constr) : bool := lazy_match! lf_codomain t with Prop => true | _ => false end in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant _ _ => sort_is_prop (Constr.type h)
  | Constr.Unsafe.Ind _ _ => sort_is_prop (Constr.type h)
  | Constr.Unsafe.Var _ => sort_is_prop (Constr.type h)
  | _ => false
  end.
Ltac2 lf_is_local (id : ident) : bool :=
  match Env.get [id] with None => true | Some _ => false end.

Ltac2 rec lf_binder_names (f : constr) (acc : ident FSet.t) : ident FSet.t :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Lambda b body =>
      lf_binder_names body (match Constr.Binder.name b with Some id => FSet.add id acc | None => acc end)
  | _ => acc
  end.
(* [comment removed for export] *)
Ltac2 lf_marker (ty : constr) : constr option :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ => if Constant.equal c (lf_const reference:(lf_pinned)) then Some (Array.get args 1) else None
      | _ => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Ltac2 Type lf_state := {
  st_n : int;
  st_xs : ident list;
  st_bodies : constr option array;          (* [comment removed for export] *)
  st_inv : bool array;                       (* [comment removed for export] *)
}.
Ltac2 lf_pack (ts : constr list) : constr :=
  match ts with
  | [t] => t
  | _ => Constr.Unsafe.make (Constr.Unsafe.App constr:(@pair) (Array.of_list ts))    (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Ltac2 lf_new_vars (st : lf_state) (t' : constr) (acc : int list) : int list :=
  let rec go (i : int) (acc : int list) : int list :=
    if Int.gt i (st.(st_n)) then acc
    else if Array.get (st.(st_inv)) i then go (Int.add i 1) acc
    else if Constr.Unsafe.noccurn i t' then go (Int.add i 1) acc
    else (Array.set (st.(st_inv)) i true; go (Int.add i 1) (i :: acc)) in
  go 1 acc.
(* [comment removed for export] *)
Ltac2 rec lf_expand (st : lf_state) (news : int list) (acc : int list) : int list :=
  match news with
  | [] => acc
  | i :: r =>
      match Array.get (st.(st_bodies)) (Int.sub i 1) with
      | None => lf_expand st r (i :: acc)
      | Some b => lf_expand st (lf_new_vars st (Constr.Unsafe.closenl (st.(st_xs)) 1 b) r) (i :: acc)
      end
  end.
Ltac2 lf_mentions (news : int list) (p : ident * constr) : bool :=
  let (_, t') := p in List.exist (fun i => Bool.neg (Constr.Unsafe.noccurn i t')) news.

(* [comment removed for export] *)
Ltac2 lf_plan1 () : lf_state * (ident * constr) list * (ident * constr) list :=
  let hs := Control.hyps () in
  let g := Control.goal () in
  let rels := lf_rel_consts () in
  let empty := FSet.empty FSet.Tags.ident_tag in
  let allowed := List.fold_left (fun acc h => let (_, _, ty) := h in
                   match lf_marker ty with Some f => lf_binder_names f acc | None => acc end) empty hs in
  let allowed_all := List.exist (fun h => let (_, _, ty) := h in
                   match lf_marker ty with
                   | Some f => (match Constr.Unsafe.kind f with
                                | Constr.Unsafe.Constant c _ => Constant.equal c (lf_const reference:(lf_all))
                                | _ => false end)
                   | None => false end) hs in
  (* [comment removed for export] *)
  let marked := List.exist (fun h => let (_, _, ty) := h in match lf_marker ty with Some _ => true | None => false end) hs in
  if (if marked then false
      else List.exist (fun h => let (id, body, ty) := h in
                         match body with Some _ => false | None => if lf_is_local id then false else lf_is_prop ty end) hs)
  then Control.zero (Tactic_failure None) else
  (* [comment removed for export] *)
  let (arith, decls) :=
    List.fold_left (fun acc h =>
      let (ar, ds) := acc in
      let (id, body, ty) := h in
      match body with
      | Some b => (ar, (id, Some b) :: ds)
      | None =>
          if lf_arith_shape rels ty then
            (if (if lf_is_local id then true else if allowed_all then true else FSet.mem id allowed)
             then ((id, ty) :: ar, ds) else acc)
          else (ar, (id, None) :: ds)
      end) ([], []) hs in
  let xs := List.map (fun p => let (i, _) := p in i) decls in
  let n := List.length xs in
  let st := { st_n := n; st_xs := xs;
              st_bodies := Array.of_list (List.map (fun p => let (_, b) := p in b) decls);
              st_inv := Array.make (Int.add n 1) false } in
  let news0 := lf_expand st (lf_new_vars st (Constr.Unsafe.closenl xs 1 g) []) [] in
  let arith' := List.map (fun p => let (id, ty) := p in (id, Constr.Unsafe.closenl xs 1 ty)) arith in
  let (hit1, miss1) := List.partition (lf_mentions news0) arith' in
  (st, hit1, miss1).
(* [comment removed for export] *)
Ltac2 lf_plan2 (st : lf_state) (hit1 : (ident * constr) list) (miss1 : (ident * constr) list) : (ident * constr) list option :=
  let rec closure (hits : (ident * constr) list) (kept : (ident * constr) list) (rest : (ident * constr) list) (grown : bool) :=
    match hits with
    | [] => (kept, grown)
    | _ :: _ =>
        match rest with
        | [] => (kept, grown)
        | _ :: _ =>
            let news := lf_expand st (lf_new_vars st (lf_pack (List.map (fun p => let (_, t') := p in t') hits)) []) [] in
            match news with
            | [] => (kept, grown)
            | _ :: _ =>
                let (h, m) := List.partition (lf_mentions news) rest in
                match h with
                | [] => (kept, grown)
                | _ :: _ => closure h (List.append h kept) m true
                end
            end
        end
    end in
  let (kept, grown) := closure hit1 hit1 miss1 false in
  if grown then Some kept else None.

Ltac lf_zify_noeuclid :=
  Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook.
(* [comment removed for export] *)
Ltac lf_is_natlit n := lazymatch n with O => idtac | S ?k => lf_is_natlit k end.
Ltac lf_fold_ofnat :=
  repeat match goal with
  | |- context [Z.of_nat ?n] => lf_is_natlit n; let v := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with v in *
  | _ : context [Z.of_nat ?n] |- _ => lf_is_natlit n; let v := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with v in *
  end.
Ltac lf_close := lf_fold_ofnat; lf_zify_noeuclid; xlia zchecker.

Ltac2 lf_keep (l : (ident * constr) list) : unit := Std.keep (List.map (fun p => let (i, _) := p in i) l).
Ltac2 lf_tiers () : unit :=
  let g := Control.goal () in
  let rels := lf_rel_consts () in
  (* [comment removed for export] *)
  if Bool.neg (lf_arith_shape rels g) then Control.zero (Tactic_failure None) else
  let (st, hit1, miss1) := lf_plan1 () in
  Control.plus
    (fun () => lf_keep hit1; ltac1:(lf_close))
    (fun _ => match lf_plan2 st hit1 miss1 with
              | None => Control.zero (Tactic_failure None)
              | Some kept => lf_keep kept; ltac1:(lf_close)
              end).
(* [comment removed for export] *)
Ltac lia_fast_tiers := solve [ intros; ltac2:(Control.enter lf_tiers) ].
