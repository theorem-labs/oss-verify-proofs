(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Definition ISREP6 (m : word -> option byte) (S ZP WB : Z) (s : inflate_state) : Prop :=
  is6_scalars m S (ISP ZP WB) s
  /\ cells s6u_segs m (S + 168) 2 2 320 (arr_get (is_lens s))
  /\ cells s6u_segs m (S + 808) 2 2 288 (arr_get (is_work s))
  /\ cells s6u_segs m (S + 1384) 4 4 1444 (arr_get (is_codes s))
  /\ (WB <> 0 -> cells s6u_segs m WB 1 1 (arr_len (is_window s)) (arr_get (is_window s)))
  /\ (WB = 0 <-> is_window_blk s = None)
  /\ (WB <> 0 -> arr_len (is_window s) = 32768).
End FXG.
