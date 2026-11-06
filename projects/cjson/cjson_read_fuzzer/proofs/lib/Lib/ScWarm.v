(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac sc_warm1 A S A2 X :=
  tryif constr_eq A A2 then fail else
  lazymatch goal with
  | _ : sc_dj A S A2 X |- _ => fail
  | _ : sc_no A S A2 X |- _ => fail
  | _ => sc_dj_ensure A S A2 X ltac:(fun _ => idtac) ltac:(idtac)
  end.

Ltac sc_prewarm HT :=
  lazymatch type of HT with
  | rw_cells ?segs ?m ?A ?cs =>
      let S := sc_key constr:(Z.of_nat (cells_size cs)) in
      repeat match goal with
      | H : bytes_at segs m ?A2 ?bs2 |- _ => let X := sc_key constr:(Z.of_nat (length bs2)) in sc_warm1 A S A2 X
      | H : rw_cells segs m ?A2 ?cs2 |- _ => let X := sc_key constr:(Z.of_nat (cells_size cs2)) in sc_warm1 A S A2 X
      | H : ro_cells segs m ?A2 ?cs2 |- _ => let X := sc_key constr:(Z.of_nat (cells_size cs2)) in sc_warm1 A S A2 X
      | H : u8arr segs m ?A2 ?xs |- _ => let X := constr:(Z.of_nat (length xs)) in sc_warm1 A S A2 X
      end;
      sc_unhide
  end.
