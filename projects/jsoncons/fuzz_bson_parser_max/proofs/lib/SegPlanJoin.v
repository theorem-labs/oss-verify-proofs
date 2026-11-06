(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module SGJ.
Fixpoint join_regs (lo : nat) (i : nat) (rs : list expr) (others : list (list expr)) : list expr * nat :=
  match rs with
  | [] => ([], lo)
  | e :: r =>
      let '(tl, lo') := join_regs lo (S i) r others in
      if forallb (fun o => expr_eqb (nth i o (ELit 0)) e) others then (e :: tl, lo')
      else (EVar lo' :: tl, S lo')
  end.
Definition join_of (lo : nat) (arms : list sym_state) : sym_state :=
  match arms with
  | [] => SS 0 [] [] [] lo
  | a :: rest =>
      let '(regs, nx) := join_regs lo 0 (s_regs a) (map s_regs rest) in
      let kn := List.filter (fun K => forallb (fun o => existsb (APC.kentry_eqb K) (s_know o)) rest) (s_know a) in
      SS (s_pc a) regs [] kn nx
  end.
End SGJ.
