(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[global] Set Default Proof Mode "Classic".
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac2 zt_prune_keep_or () : unit :=
  let hs := Control.hyps () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if LiaTuning.zt_plain_arith ty then None
                          else if Bool.and (LiaTuning.zt_is_local id) (LiaTuning.zt_is_prop ty)
                               then (if LiaTuning.zt_arith_like ty then None else Some id) else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zify_prune_keep_or := ltac2:(Control.enter zt_prune_keep_or).

(* [comment removed for export] *)
Ltac liaA :=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac lia_probe :=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Ltac lia_probe_or :=
  first [ lia_probe | zify_prune_keep_or; Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require StoreFast ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac policy_lia := liaA.

Ltac2 rec pp_codomain (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod _ b => pp_codomain b
  | Constr.Unsafe.LetIn _ _ b => pp_codomain b
  | Constr.Unsafe.Cast c _ _ => pp_codomain c
  | _ => t
  end.
Ltac2 rec pp_head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f _ => pp_head f
  | Constr.Unsafe.Cast c _ _ => pp_head c
  | _ => t
  end.
(* [comment removed for export] *)
Ltac2 pp_vars (p : constr) (t : constr) : ident list :=
  let vs := StoreFast.SF2.vars_of [] t in
  match Constr.Unsafe.kind p with
  | Constr.Unsafe.Var pid => List.filter (fun x => Bool.neg (Ident.equal x pid)) vs
  | _ => vs
  end.
(* [comment removed for export] *)
Ltac2 pp_candidates () : ident list :=
  let g := Control.goal () in
  let p := pp_head g in
  let av := match Constr.Unsafe.kind g with
            | Constr.Unsafe.App _ args =>
                let n := Array.length args in
                if Int.lt 0 n then pp_vars p (Array.get args (Int.sub n 1)) else []
            | _ => []
            end in
  let lit := match av with [] => true | _ :: _ => false end in
  let hs := List.rev (Control.hyps ()) in
  let cands := List.map_filter (fun h => let (id, _, ty) := h in
                 if Constr.equal (pp_head (pp_codomain ty)) p then
                   (let hv := pp_vars p ty in
                    let score := if StoreFast.SF2.meets hv av then 0
                                 else if Bool.and lit (match hv with [] => true | _ :: _ => false end) then 1
                                 else 2 in
                    Some (id, score))
                 else None) hs in
  let pick := fun k => List.map_filter (fun c => let (id, sc) := c in if Int.equal sc k then Some id else None) cands in
  List.append (pick 0) (List.append (pick 1) (pick 2)).
(* [comment removed for export] *)
Ltac2 pp_try (close1 : Ltac1.t) : unit :=
  let ids := pp_candidates () in
  let rec go ids := match ids with
    | [] => Control.zero (Tactic_failure None)
    | id :: rest =>
        Control.plus (fun () => Ltac1.apply close1 [Ltac1.of_constr (Control.hyp id)] (fun t => Ltac1.run t))
                     (fun _ => go rest)
    end in
  Control.once (fun () => go ids).
Ltac policy_close1 H := eapply H; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; solve [ eauto | policy_lia | ZBridge.zsimp; policy_lia ].
Ltac policy_pick := ltac2:(Control.enter (fun () => pp_try ltac1val:(fun H => policy_close1 H))).

(* [comment removed for export] *)
Goal forall (x s : Z) (Q : nat -> Prop), (x + 10 <= s \/ s + 5 <= x) -> Q 3%nat -> 0 <= x -> ~ (s <= x + 2 < s + 5).
Proof. intros. zify_prune_keep_or. lazymatch goal with H : Q _ |- _ => fail "not pruned" | _ => idtac end. liaA. Qed.
