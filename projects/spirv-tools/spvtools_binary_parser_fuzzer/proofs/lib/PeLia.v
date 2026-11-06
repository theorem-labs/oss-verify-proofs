(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec.
From Ltac2 Require Import Ltac2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Set Default Proof Mode "Classic".
Ltac2 pe_is_local (id : ident) : bool :=
  match Env.get [id] with None => true | Some _ => false end.
Ltac2 rec pe_codomain (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ b => pe_codomain b
  | Constr.Unsafe.LetIn _ _ b => pe_codomain b
  | Constr.Unsafe.Cast c _ _ => pe_codomain c
  | _ => t
  end.
Ltac2 rec pe_head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => pe_head f
  | Constr.Unsafe.Cast c _ _ => pe_head c
  | _ => t
  end.
Ltac2 pe_sort_is_prop (ty : constr) : bool :=
  lazy_match! pe_codomain ty with Prop => true | _ => false end.
Ltac2 pe_is_prop (ty : constr) : bool :=
  let h := pe_head (pe_codomain ty) in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant _ _ => pe_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Ind _ _ => pe_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Var _ => pe_sort_is_prop (Constr.type h)
  | _ => false
  end.
Ltac2 pe_bad (ty : constr) : bool :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.Prod _ _ => pe_is_prop ty
  | Constr.Unsafe.App h _ =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Ind _ _ => Constr.equal h '@or
      | Constr.Unsafe.Constant _ _ => if Constr.equal h '@not then true else Constr.equal h '@iff
      | _ => false
      end
  | _ => false
  end.
Ltac2 pe_prune () : unit :=
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Bool.and (pe_is_local id) (pe_bad ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac pe_zify_prune := ltac2:(Control.enter pe_prune).
Ltac pe_lia :=
  tryif noncert_goal_has_var then
    first [ pe_zify_prune; Zify.zify; xlia zchecker
          | Zify.zify; xlia zchecker ]
  else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].

Ltac2 rec pe3_plain_arith (t : constr) : bool :=
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
          if Constr.equal h '@and then (if pe3_plain_arith (Array.get args 0) then pe3_plain_arith (Array.get args 1) else false)
          else if Constr.equal h '@eq then true else if Constr.equal h '@le then true
          else false
      | _ => false
      end
  | Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then true else Constr.equal t 'False
  | _ => false
  end.
Ltac2 rec pe3_codomain (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ b => pe3_codomain b
  | Constr.Unsafe.LetIn _ _ b => pe3_codomain b
  | Constr.Unsafe.Cast c _ _ => pe3_codomain c
  | _ => t
  end.
Ltac2 rec pe3_head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => pe3_head f
  | Constr.Unsafe.Cast c _ _ => pe3_head c
  | _ => t
  end.
Ltac2 pe3_sort_is_prop (ty : constr) : bool :=
  lazy_match! pe3_codomain ty with Prop => true | _ => false end.
Ltac2 pe3_is_prop (ty : constr) : bool :=
  let h := pe3_head (pe3_codomain ty) in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant _ _ => pe3_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Ind _ _ => pe3_sort_is_prop (Constr.type h)
  | Constr.Unsafe.Var _ => pe3_sort_is_prop (Constr.type h)
  | _ => false
  end.
Ltac2 pe3_is_local (id : ident) : bool :=
  match Env.get [id] with None => true | Some _ => false end.
Ltac2 rec pe3_plain_arith2 (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if Constr.equal h '@not then pe3_plain_arith2 (Array.get args 0) else pe3_plain_arith t
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h '@and then (if pe3_plain_arith2 (Array.get args 0) then pe3_plain_arith2 (Array.get args 1) else false)
          else if Constr.equal h '@or then (if pe3_plain_arith2 (Array.get args 0) then pe3_plain_arith2 (Array.get args 1) else false)
          else pe3_plain_arith t
      | _ => false
      end
  | _ => pe3_plain_arith t
  end.
Ltac2 pe3_is_arith_head (h : constr) : bool :=
  if Constr.equal h '@Z.add then true else if Constr.equal h '@Z.sub then true
  else if Constr.equal h '@Z.mul then true else if Constr.equal h '@Z.opp then true
  else if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
  else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
  else if Constr.equal h '@not then true else if Constr.equal h '@and then true
  else if Constr.equal h '@or then true else if Constr.equal h '@eq then true
  else if Constr.equal h '@Z.of_nat then true else false.
Ltac2 rec pe3_atoms (t : constr) (acc : constr list) : constr list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if pe3_is_arith_head h then Array.fold_right (fun a acc => pe3_atoms a acc) args acc
      else (match Constr.Unsafe.kind h with
            | Constr.Unsafe.Constructor _ _ => acc
            | _ => t :: acc end)
  | Constr.Unsafe.Var _ => t :: acc
  | _ => acc
  end.
Ltac2 pe3_shares (a : constr list) (b : constr list) : bool :=
  List.exist (fun x => List.exist (fun y => Constr.equal x y) b) a.
Ltac2 pe3_prune_rel () : unit :=
  let goal_atoms := pe3_atoms (Control.goal ()) [] in
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if pe3_plain_arith ty then None
                          else if Bool.and (pe3_plain_arith2 ty) (pe3_shares (pe3_atoms ty []) goal_atoms) then None
                          else if Bool.and (pe3_is_local id) (pe3_is_prop ty) then Some id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac pe3_zify_prune_rel := ltac2:(Control.enter pe3_prune_rel).
Ltac pe3_lia :=
  tryif noncert_goal_has_var then
    first [ pe_zify_prune; Zify.zify; xlia zchecker
          | pe3_zify_prune_rel; Zify.zify; xlia zchecker
          | Zify.zify; xlia zchecker ]
  else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].

From Stdlib Require Import Zify.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Ltac zify_noelim := intros; Zify.zify_pre_hook; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate;
                    Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Ltac ne_lia :=
  tryif noncert_goal_has_var then first [ zify_noelim; xlia zchecker | Zify.zify; xlia zchecker ]
  else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
Ltac ne_pe_lia :=
  tryif noncert_goal_has_var then
    first [ pe_zify_prune; zify_noelim; xlia zchecker | pe_zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ]
  else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
