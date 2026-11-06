(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec am_bad_kd (e : am_env) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match am_head_of e f with
       | AHother => false
       | AHand => if am_bad_kd e (Array.get args 0) then true else am_bad_kd e (Array.get args 1)
       | AHor => false
       | AHiff => false
       | AHnot => am_neg_bad e (Array.get args 0)
       | AHeq => am_eq_bad e args
       | AHle => am_ord_bad e args
       | AHcmp => am_ord_bad e args
       | AHFalse => false
       | AHTrue => false
       end)
  | Constr.Unsafe.Prod _ c => if Constr.Unsafe.noccurn 1 c then am_is_propish e c else false
  | _ => false
  end.

Ltac2 am_lia_goal_kd () :=
  let hs := Control.hyps () in
  if Int.lt (List.length hs) am_gate then ltac1:(am_inner) else
  let e := am_mk_env () in
  if am_goal_bad e (Control.goal ()) then ltac1:(am_inner) else
  let bad := List.filter (fun (_, b, t) => match b with Some _ => false | None => am_bad_kd e t end) hs in
  match bad with
  | [] => ltac1:(am_inner)
  | _ => Control.plus (fun () => Control.once (fun () => am_clear (List.map (fun (h, _, _) => h) bad); ltac1:(am_inner)))
                      (fun _ => ltac1:(am_inner))
  end.

(* [comment removed for export] *)
Ltac am_lia_kd := idtac; ltac2:(Control.enter am_lia_goal_kd).
