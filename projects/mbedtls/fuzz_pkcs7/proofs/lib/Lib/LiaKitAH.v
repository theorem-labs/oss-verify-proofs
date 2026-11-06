(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2 FSet FMap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaTuning.
Set Default Proof Mode "Classic".

Ltac2 zf_disj_cap () : int := 6.

(* [comment removed for export] *)
Ltac2 rec zf_arith_formula (e : zf_env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ =>
          if FSet.mem c (e.(zf_cs)) then true
          else if Constr.equal h '@not then zf_arith_formula e (Array.get args 0)
          else false
      | Constr.Unsafe.Ind i _ =>
          if Ind.equal i (e.(zf_eq)) then true
          else if Ind.equal i (e.(zf_le)) then true
          else if Ind.equal i (e.(zf_and)) then
            (if zf_arith_formula e (Array.get args 0) then zf_arith_formula e (Array.get args 1) else false)
          else if Constr.equal h '@or then
            (if zf_arith_formula e (Array.get args 0) then zf_arith_formula e (Array.get args 1) else false)
          else false
      | _ => false
      end
  | Constr.Unsafe.Ind i _ => if Ind.equal i (e.(zf_true)) then true else Ind.equal i (e.(zf_false))
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 zf_keep_disj (e : zf_env) (ty : constr) : bool :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.App h _ =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Ind i _ => if Ind.equal i (e.(zf_and)) then false else zf_arith_formula e ty
      | Constr.Unsafe.Constant _ _ => if Constr.equal h '@not then zf_arith_formula e ty else false
      | _ => false
      end
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 zf_split_arith_conj () : unit :=
  let e := zf_mkenv () in
  let rec loop (n : int) :=
    if Int.le n 0 then () else
    let cands := List.map_filter (fun h => let (id, body, ty) := h in
       match body with
       | Some _ => None
       | None =>
         match Constr.Unsafe.kind ty with
         | Constr.Unsafe.App hd _ =>
             (match Constr.Unsafe.kind hd with
              | Constr.Unsafe.Ind i _ =>
                  if Ind.equal i (e.(zf_and)) then
                    (if zf_arith_formula e ty then (if zt_is_local id then Some id else None) else None)
                  else None
              | _ => None
              end)
         | _ => None
         end
       end) (Control.hyps ()) in
    match cands with
    | [] => ()
    | _ :: _ => List.iter (fun id => let c := Control.hyp id in
                   (* [comment removed for export] *)
                   Control.once (fun () => Control.plus (fun () => ltac1:(c |- destruct c as [? ?]) (Ltac1.of_constr c)) (fun _ => ()))) cands;
                loop (Int.sub n 1)
    end in loop 8.
Ltac zify_split_arith_conj := ltac2:(Control.enter zf_split_arith_conj).

(* [comment removed for export] *)
Ltac2 zf_prune_keep_disj () : unit :=
  let e := zf_mkenv () in
  let hs := Control.hyps () in
  let (ids, _, _, kept) := List.fold_left (fun acc h =>
      let (ids, cache, streak, kept) := acc in
      let (id, body, ty) := h in
      match body with
      | Some _ => acc
      | None =>
          let (p, cache) := zf_classify e cache ty in
          if p then
            (if zf_keep_disj e ty then (ids, cache, streak, Int.add kept 1)
             else if Int.ge streak (zf_streak ()) then (id :: ids, cache, streak, kept)
             else if zt_is_local id then (id :: ids, cache, Int.add streak 1, kept) else (ids, cache, 0, kept))
          else (ids, cache, streak, kept)
      end) ([], { zc_c := FMap.empty FSet.Tags.constant_tag; zc_i := FMap.empty FSet.Tags.inductive_tag }, 0, 0) hs in
  if Int.gt kept (zf_disj_cap ()) then Control.zero (Tactic_failure None) else
  if Int.equal kept 0 then Control.zero (Tactic_failure None) else
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zify_prune_keep_disj := zify_split_arith_conj; ltac2:(Control.enter zf_prune_keep_disj).

(* [comment removed for export] *)
Ltac zify_sat_premise := first [ assumption | exact I | apply Z.leb_le; reflexivity | apply Z.ltb_lt; reflexivity ].
Ltac zify_sat_one H :=
  first [ specialize (H ltac:(zify_sat_premise) ltac:(zify_sat_premise))
        | specialize (H ltac:(zify_sat_premise))
        | clear H ].
(* [comment removed for export] *)
Ltac2 zf_sat_cheap () : unit :=
  let n0 := List.length (Control.hyps ()) in
  ltac1:(Zify.zify_saturate);
  let added := List.skipn n0 (Control.hyps ()) in
  List.iter (fun h => let (id, _, ty) := h in
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.Prod _ _ => let c := Control.hyp id in ltac1:(c |- zify_sat_one c) (Ltac1.of_constr c)
    | _ => ()
    end) added.
Ltac zify_saturate_cheap := ltac2:(Control.enter zf_sat_cheap).

(* [comment removed for export] *)
Ltac zify_lite :=
  intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); zify_saturate_cheap; Zify.zify_post_hook.
Ltac zify_lite_euclid :=
  zify_lite; Zify.zify_to_euclidean_division_equations.

(* [comment removed for export] *)
Ltac zify_has_div :=
  match goal with
  | |- context [Z.div _ _] => idtac      | |- context [Z.modulo _ _] => idtac
  | _ : context [Z.div _ _] |- _ => idtac | _ : context [Z.modulo _ _] |- _ => idtac
  | _ := context [Z.div _ _] |- _ => idtac | _ := context [Z.modulo _ _] |- _ => idtac
  | |- context [Z.quot _ _] => idtac     | |- context [Z.rem _ _] => idtac
  | _ : context [Z.quot _ _] |- _ => idtac | _ : context [Z.rem _ _] |- _ => idtac
  | _ := context [Z.quot _ _] |- _ => idtac | _ := context [Z.rem _ _] |- _ => idtac
  end.

(* [comment removed for export] *)
Ltac2 rec zf_vars (acc : ident list) (t : constr) : ident list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id => id :: acc
  | Constr.Unsafe.App f args => Array.fold_left zf_vars (zf_vars acc f) args
  | Constr.Unsafe.Cast c _ _ => zf_vars acc c
  | Constr.Unsafe.Prod b c => zf_vars (zf_vars acc (Constr.Binder.type b)) c
  | Constr.Unsafe.Lambda b c => zf_vars (zf_vars acc (Constr.Binder.type b)) c
  | Constr.Unsafe.LetIn b v c => zf_vars (zf_vars (zf_vars acc (Constr.Binder.type b)) v) c
  | _ => acc
  end.
Ltac2 rec zf_mentions (vs : ident list) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id => List.exist (fun v => Ident.equal v id) vs
  | Constr.Unsafe.App f args => if zf_mentions vs f then true else Array.exist (fun a => zf_mentions vs a) args
  | Constr.Unsafe.Cast c _ _ => zf_mentions vs c
  | Constr.Unsafe.Prod b c => if zf_mentions vs (Constr.Binder.type b) then true else zf_mentions vs c
  | Constr.Unsafe.Lambda b c => if zf_mentions vs (Constr.Binder.type b) then true else zf_mentions vs c
  | _ => false
  end.
Ltac2 zf_goal_vars () : ident list :=
  let hs := Control.hyps () in
  let rec close (todo : ident list) (seen : ident list) :=
    match todo with
    | [] => seen
    | v :: rest =>
        if List.exist (fun s => Ident.equal s v) seen then close rest seen
        else
          let extra := match List.find_opt (fun h => let (id, _, _) := h in Ident.equal id v) hs with
                       | Some h => let (_, body, _) := h in (match body with Some b => zf_vars [] b | None => [] end)
                       | None => [] end in
          close (List.append extra rest) (v :: seen)
    end in
  close (zf_vars [] (Control.goal ())) [].
Ltac2 zf_prune_far () : unit :=
  let gv := zf_goal_vars () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
     match body with
     | Some _ => None
     | None => if zf_mentions gv ty then None
               else if zt_is_prop ty then (if zt_is_local id then Some id else None) else None
     end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zify_prune_far := ltac2:(Control.enter zf_prune_far).
(* [comment removed for export] *)
Ltac2 zf_prune_far_sec () : unit :=
  let gv := zf_goal_vars () in
  let (locals, secs) := List.fold_left (fun acc h => let (ls, ss) := acc in let (id, body, ty) := h in
     match body with
     | Some _ => acc
     | None => if zf_mentions gv ty then acc
               else if zt_is_prop ty then (if zt_is_local id then (id :: ls, ss) else (ls, id :: ss)) else acc
     end) ([], []) (Control.hyps ()) in
  (match locals with [] => () | _ :: _ => Std.clear locals end);
  List.iter (fun id => Control.once (fun () => Control.plus (fun () => Std.clear [id]) (fun _ => ()))) secs.
Ltac zify_prune_far_sec := ltac2:(Control.enter zf_prune_far_sec).

(* [comment removed for export] *)
Ltac zify_dm_step_goal :=
  match goal with
  | |- context [Z.div ?x ?y] => zify_new_dm x y
  | |- context [Z.modulo ?x ?y] => zify_new_dm x y
  end.
Ltac zify_qr_step_goal :=
  match goal with
  | |- context [Z.quot ?x ?y] => zify_new_qr x y
  | |- context [Z.rem ?x ?y] => zify_new_qr x y
  end.
Ltac zify_goal_euclid :=
  Z.divide_to_equations'; first [ progress (repeat zify_dm_step_goal; repeat zify_qr_step_goal); cbv beta | idtac ];
  Z.euclidean_division_equations_cleanup.
Ltac zify_goal_has_div :=
  match goal with
  | |- context [Z.div _ _] => idtac | |- context [Z.modulo _ _] => idtac
  | |- context [Z.quot _ _] => idtac | |- context [Z.rem _ _] => idtac
  end.

(* [comment removed for export] *)
Ltac lia_ah :=
  first [ zify_prune;
          first [ zify_lite; Z.euclidean_division_equations_cleanup; xlia zchecker
                | zify_goal_has_div; zify_lite; zify_goal_euclid; xlia zchecker
                | zify_has_div; zify_lite_euclid; xlia zchecker ]
        | zify_prune_keep_disj;
          first [ zify_lite; Z.euclidean_division_equations_cleanup; xlia zchecker
                | zify_goal_has_div; zify_lite; zify_goal_euclid; xlia zchecker
                | zify_has_div; zify_lite_euclid; xlia zchecker ]
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac lia_ahx :=
  first [ zify_prune;
          first [ zify_prune_far_sec; zify_lite; Z.euclidean_division_equations_cleanup; xlia zchecker
                | zify_prune_far; zify_lite; Z.euclidean_division_equations_cleanup; xlia zchecker
                | zify_lite; Z.euclidean_division_equations_cleanup; xlia zchecker
                | zify_goal_has_div; zify_lite; zify_goal_euclid; xlia zchecker
                | zify_has_div; zify_lite_euclid; xlia zchecker ]
        | zify_prune_keep_disj;
          first [ zify_lite; Z.euclidean_division_equations_cleanup; xlia zchecker
                | zify_goal_has_div; zify_lite; zify_goal_euclid; xlia zchecker
                | zify_has_div; zify_lite_euclid; xlia zchecker ]
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac nia_ah :=
  first [ zify_lite_euclid; xnia zchecker
        | Zify.zify; xnia zchecker ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 sassumption0 () :=
  let g := Control.goal () in
  let rec go hs := match hs with
    | [] => Control.zero (Tactic_failure (Some (Message.of_string "sassumption: no hypothesis has exactly this type")))
    | h :: rest => let (id, _, ty) := h in
        if Constr.equal ty g then Control.refine (fun () => Control.hyp id) else go rest
    end in go (List.rev (Control.hyps ())).
Ltac sassumption := ltac2:(Control.enter sassumption0).
(* [comment removed for export] *)
Ltac cassumption := match goal with H : ?T |- ?T => exact H end.

(* [comment removed for export] *)
Ltac2 rec sx_head_of (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => sx_head_of f
  | Constr.Unsafe.Cast c _ _ => sx_head_of c
  | _ => t
  end.
Ltac2 hassumption0 () :=
  let g := Control.goal () in
  let hg := sx_head_of g in
  let rec go hs := match hs with
    | [] => Control.zero (Tactic_failure (Some (Message.of_string "hassumption: no hypothesis with this head fits")))
    | h :: rest => let (id, _, ty) := h in
        if Constr.equal (sx_head_of ty) hg
        then Control.plus (fun () => Control.refine (fun () => Control.hyp id)) (fun _ => go rest)
        else go rest
    end in Control.once (fun () => go (List.rev (Control.hyps ()))).
Ltac hassumption := ltac2:(Control.enter hassumption0).
