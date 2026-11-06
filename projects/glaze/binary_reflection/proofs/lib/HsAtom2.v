(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 ha_rank (near : ident list) : ident list :=
  let e := ha_mk_env () in
  let hd := ha_mk_hd e in
  let tb := ha_new_tbl () in
  let gat := match ha_patoms e hd tb (Control.goal ()) [] with Some a => ha_dedup a [] | None => [] end in
  let hs := Control.hyps () in
  let sc := List.map (fun h =>
      let a := match List.find_opt (fun (x, _, _) => Ident.equal x h) hs with
               | Some (_, _, t) => (match ha_patoms e hd tb t [] with Some a => ha_dedup a [] | None => [] end)
               | None => [] end in
      (h, List.length (List.filter (fun x => List.exist (fun y => Int.equal x y) gat) a))) near in
  let mx := List.fold_left (fun m (_, s) => if Int.lt m s then s else m) 0 sc in
  let rec go k acc := if Int.lt k 0 then acc else
      go (Int.sub k 1) (List.append acc (List.map (fun (h, _) => h) (List.filter (fun (_, s) => Int.equal s k) sc))) in
  go mx [].
Ltac2 ha_tiersR_goal (tac : Ltac1.t) () :=
  if Constr.has_evar (Control.goal ()) then ha_fail () else
  if Int.lt (List.length (Control.hyps ())) ha_gate then ha_fail () else
  let dv := ha_divflag () in
  let (base, disj, near, conn, kbad) := ha_analyze_v4 true dv in   (* [comment removed for export] *)
  let tierA () := ha_run (List.append base disj) tac () in
  let tierA0 () := match kbad with
                   | [] => tierA ()
                   | _ => if am_goal_bad (am_mk_env ()) (Control.goal ()) then tierA ()
                          else Control.plus (ha_run (List.append kbad (List.append base disj)) tac) (fun _ => tierA ()) end in
  let tierB2 () := ha_each base disj (ha_firstn 3 (List.append (ha_rank near) conn)) tac in
  let tierB1 () := match near with [] => ha_fail () | _ => ha_run (List.append base (ha_minus disj near)) tac () end in
  Control.plus tierA0 (fun _ => Control.plus tierB2 (fun _ => tierB1 ())).
Ltac ha_tiersR := ltac2:(tac |- Control.enter (ha_tiersR_goal tac)).
