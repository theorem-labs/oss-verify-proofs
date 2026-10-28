(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import RangeFast.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 is_ref (c : constant) (r : Std.reference) : bool :=
  match r with Std.ConstRef c' => Constant.equal c c' | _ => false end.
(* [comment removed for export] *)
Ltac2 env_atom_facts (a : constr) : (constr * constr) list :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constant c _ =>
          if Int.equal (Array.length args) 1 then
            let i := Array.get args 0 in
            if is_ref c reference:(p_bs) then (let pf := constr:(@p_bs_rng $i) in [(pf, Constr.type pf)])
            else if is_ref c reference:(alloc_ceiling) then (let pf := constr:(@alloc_ceiling_range $i) in [(pf, Constr.type pf)])
            else if is_ref c reference:(p_wf) then (let pf := constr:(@p_wf_rng $i) in [(pf, Constr.type pf)])
            else if is_ref c reference:(budget_q) then (let pf := constr:(@budget_q_rng $i) in [(pf, Constr.type pf)])
            else if is_ref c reference:(run_guard) then (let pf := constr:(@run_guard_range $i) in [(pf, Constr.type pf)])
            else if is_ref c reference:(run_secret) then (let pf := constr:(@run_secret_range $i) in [(pf, Constr.type pf)])
            else []
          else []
      | _ => []
      end
  | _ => []
  end.
