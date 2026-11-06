(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Exec Step.
Import ListNotations.
Unset Lia Cache.

Ltac abs_junk H :=
  repeat match type of H with
  | context [CB _ ?E] =>
      lazymatch E with firstn _ _ => idtac | skipn _ _ => idtac end;
      let j := fresh "jk" in
      revert H; generalize E; intros j H
  end.

(* [comment removed for export] *)
Ltac split_for_access_abs H segs m A cs kn n :=
  let ok := eval_cb_split_ok cs kn n in
  lazymatch ok with
  | true =>
      let cs2 := eval_cb_split cs kn n in
      lazymatch cs2 with
      | cs => idtac
      | _ => first [ apply (rw_cells_cb_split segs m A cs cs2 kn n) in H
                   | apply (ro_cells_cb_split segs m A cs cs2 kn n) in H ];
             [ | cells_cbv; reflexivity | cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app]; reflexivity ];
             abs_junk H
      end
  end.
