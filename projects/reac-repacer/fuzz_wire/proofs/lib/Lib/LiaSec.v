(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[global] Set Default Proof Mode "Classic".
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import LiaTwx2.

(* [comment removed for export] *)
Ltac2 rec zt_has_arith (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
          else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
          else if Constr.equal h '@lt then true else if Constr.equal h '@ge then true
          else if Constr.equal h '@gt then true else if Constr.equal h '@N.le then true
          else if Constr.equal h '@N.lt then true else if Constr.equal h '@Z.divide then true
          else if Constr.equal h '@not then zt_has_arith (Array.get args 0)
          else if Constr.equal h '@iff then (if zt_has_arith (Array.get args 0) then true else zt_has_arith (Array.get args 1))
          else false
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal h '@and then (if zt_has_arith (Array.get args 0) then true else zt_has_arith (Array.get args 1))
          else if Constr.equal h '@or then (if zt_has_arith (Array.get args 0) then true else zt_has_arith (Array.get args 1))
          else if Constr.equal h '@le then true
          else if Constr.equal h '@eq then
            (let ty := Array.get args 0 in
             if Constr.equal ty 'Z then true else if Constr.equal ty 'nat then true else if Constr.equal ty 'N then true else Constr.equal ty 'positive)
          else false
      | _ => false
      end
  | Constr.Unsafe.Prod _ b =>
      (* [comment removed for export] *)
      if Constr.Unsafe.closedn 0 b then
        (match Constr.Unsafe.kind t with
         | Constr.Unsafe.Prod bd _ => if zt_has_arith (Constr.Binder.type bd) then true else zt_has_arith b
         | _ => false end)
      else false
  | _ => false
  end.

Ltac2 zt_sec_trigger () : bool :=
  List.exist (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => false
                | None => if zt_is_local id then false else if zt_plain_arith ty then false else if zt_is_prop ty then zt_has_arith ty else false
                end) (Control.hyps ()).
Ltac2 zt_prune_sec () : unit :=
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if zt_plain_arith ty then None else if zt_is_prop ty then Some id else None
                end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zt_if_trigger := ltac2:(Control.enter (fun () => if zt_sec_trigger () then () else Control.zero (Tactic_failure None))).
Ltac zify_prune_sec := ltac2:(Control.enter zt_prune_sec).
Ltac lia_T0 := zify_prune_sec; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac lia_T1 := zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac lia_T2 := zify_prune; Zify.zify; xlia zchecker.
Ltac lia_T3 := Zify.zify; xlia zchecker.
Ltac lia_sec := tryif zt_if_trigger then first [ lia_T0 | lia_T3 ] else first [ lia_T1 | lia_T2 | lia_T3 ].
