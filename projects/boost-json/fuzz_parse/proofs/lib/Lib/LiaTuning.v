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
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc4True" s.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[global] Unset Lia Cache.
#[global] Unset Nia Cache.
#[global] Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zify_done : ltac2:(zQ "10!h9>1x$0>1y$0P") := ltac2:(zQ "20!h9!j0\1x$0\1y$0$1").
Definition zify_done_qr : ltac2:(zQ "10!h9>1x$0>1y$0P") := ltac2:(zQ "20!h9!j0\1x$0\1y$0$1").

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

(* [comment removed for export] *)
Ltac zsp_refl H T := specialize (H (@eq_refl _ _ : T)).
Ltac zsp_asm H := specialize (H ltac:(assumption)).
Ltac zsp2_refl H A T := specialize (fun a : A => H a (@eq_refl _ _ : T)).
Ltac zsp2_asm H A T := let h := fresh "zh" in assert (h : T) by assumption; specialize (fun a : A => H a h); clear h.
Ltac zsp_isprop T := lazymatch type of T with Prop => idtac end.
Ltac zsp_arith T := zify_arith_prop T.
Ltac2 rec zsp_arith2 (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
      else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
      else if Constr.equal h '@Peano.lt then true else if Constr.equal h '@le then true
      else if Constr.equal h '@eq then
        (let a := Array.get args 0 in if Constr.equal a 'Z then true else Constr.equal a 'nat)
      else if Constr.equal h '@not then zsp_arith2 (Array.get args 0)
      else if Constr.equal h '@and then (if zsp_arith2 (Array.get args 0) then true else zsp_arith2 (Array.get args 1))
      else if Constr.equal h '@or then (if zsp_arith2 (Array.get args 0) then true else zsp_arith2 (Array.get args 1))
      else false
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 zsp_class (t : constr) : int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h _ =>
      if Constr.equal h '@Z.le then 0 else if Constr.equal h '@Z.ge then 0
      else if Constr.equal h '@le then 0 else if Constr.equal h '@Peano.lt then 0
      else if Constr.equal h '@not then (if zsp_arith2 t then 0 else 2)
      else if Constr.equal h '@and then (if zsp_arith2 t then 0 else 2)
      else if Constr.equal h '@or then (if zsp_arith2 t then 0 else 2)
      else if Constr.equal h '@Z.lt then 1 else if Constr.equal h '@Z.gt then 1
      else if Constr.equal h '@eq then (if zsp_arith2 t then 1 else 2)
      else 2
  | _ => 2
  end.
Ltac2 zsp_try (f : unit -> unit) : bool :=
  Control.once (fun () => Control.plus (fun () => f (); true) (fun _ => false)).
Ltac2 zsp_hyp1 (id : ident) : bool :=
  let h := Control.hyp id in
  let ty := Constr.type h in
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.Prod b1 r1 =>
      if Bool.neg (Constr.Unsafe.closedn 0 r1) then false else
      let t := Constr.Binder.type b1 in
      let c := zsp_class t in
      let first_ok :=
        if Int.equal c 0 then false
        else if Int.equal c 1 then zsp_try (fun () => ltac1:(h t |- zsp_refl h t) (Ltac1.of_constr h) (Ltac1.of_constr t))
        else if zsp_try (fun () => ltac1:(t |- zsp_isprop t) (Ltac1.of_constr t)) then
          (if zsp_try (fun () => ltac1:(h t |- zsp_refl h t) (Ltac1.of_constr h) (Ltac1.of_constr t)) then true
           else if zsp_try (fun () => ltac1:(t |- zsp_arith t) (Ltac1.of_constr t)) then false
           else zsp_try (fun () => ltac1:(h |- zsp_asm h) (Ltac1.of_constr h)))
        else false in
      if first_ok then true else
      match Constr.Unsafe.kind r1 with
      | Constr.Unsafe.Prod b2 r2 =>
          if Bool.neg (Constr.Unsafe.closedn 0 r2) then false else
          let t2 := Constr.Binder.type b2 in
          if Bool.neg (Constr.Unsafe.closedn 0 t2) then false else
          let c2 := zsp_class t2 in
          if Int.equal c2 0 then false
          else if Int.equal c2 1 then zsp_try (fun () => ltac1:(h a t |- zsp2_refl h a t) (Ltac1.of_constr h) (Ltac1.of_constr t) (Ltac1.of_constr t2))
          else if zsp_try (fun () => ltac1:(t |- zsp_isprop t) (Ltac1.of_constr t2)) then
            (if zsp_try (fun () => ltac1:(h a t |- zsp2_refl h a t) (Ltac1.of_constr h) (Ltac1.of_constr t) (Ltac1.of_constr t2)) then true
             else if zsp_try (fun () => ltac1:(t |- zsp_arith t) (Ltac1.of_constr t2)) then false
             else zsp_try (fun () => ltac1:(h a t |- zsp2_asm h a t) (Ltac1.of_constr h) (Ltac1.of_constr t) (Ltac1.of_constr t2)))
          else false
      | _ => false
      end
  | _ => false
  end.
Ltac2 rec zsp_hyp (id : ident) (n : int) : bool :=
  if Int.le n 0 then false else
  if zsp_hyp1 id then (let _ := zsp_hyp id (Int.sub n 1) in true) else false.
Ltac2 rec zsp_rounds (n : int) : unit :=
  if Int.le n 0 then () else
  let ids := List.map (fun h => let (id, _, _) := h in id) (Control.hyps ()) in
  let prog := List.fold_left (fun acc id =>
                 let p := Control.once (fun () => Control.plus (fun () => zsp_hyp id 8) (fun _ => false)) in
                 if p then true else acc) false (List.rev ids) in
  if prog then zsp_rounds (Int.sub n 1) else ().
Ltac zify_spec_trivial_fast := ltac2:(Control.enter (fun () => Control.once (fun () => zsp_rounds 6))).
Ltac zify_spec_trivial := zify_spec_trivial_fast.

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
