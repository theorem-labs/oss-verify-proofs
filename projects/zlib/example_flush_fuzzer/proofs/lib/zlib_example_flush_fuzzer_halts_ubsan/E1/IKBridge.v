(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Fs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.IK Require Import TSet ZStep ZMem ZArr ZRegKeys IGlue.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.






Section Mem.
Variable segs : list Segment.

Lemma mem_u64_cell : forall M a v, mem_u64 segs M a v <-> cell segs M a 8 v.
Proof. intros. unfold mem_u64, mem_is, cell. rewrite length_Z_to_le_bytes'. reflexivity. Qed.
Lemma mem_u32_cell : forall M a v, mem_u32 segs M a v <-> cell segs M a 4 v.
Proof. intros. unfold mem_u32, mem_is, cell. rewrite length_Z_to_le_bytes'. reflexivity. Qed.

Lemma mem_arr_cells : forall k M base n f,
  mem_arr k segs M base n f -> cells segs M base k (Z.to_nat k) n f.
Proof.
  intros k M base n f (Hb & Hn & Hk & Hbn & H) i Hi. unfold cell.
  specialize (H i Hi). unfold mem_is in H. rewrite length_Z_to_le_bytes' in H. exact H.
Qed.

Lemma cells_mem_arr : forall k M base n f,
  0 <= base -> 0 <= n -> 0 < k -> base + k * n <= 2 ^ 64 ->
  cells segs M base k (Z.to_nat k) n f -> mem_arr k segs M base n f.
Proof.
  intros k M base n f Hb Hn Hk Hbn H. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. unfold mem_is. rewrite length_Z_to_le_bytes'. exact (H i Hi).
Qed.

Lemma mapped_mem_wr : forall M a n, 0 <= a -> a + n <= 2 ^ 64 -> mapped M a n -> mem_wr segs M a n.
Proof.
  intros M a n Ha Han H i Hi. unfold wview.
  assert (Hx : M (w64 (a + i)) <> None).
  { apply H. rewrite w64_unsigned, mod_small_u64 by lia. lia. }
  destruct (M (w64 (a + i))); [discriminate | exfalso; apply Hx; reflexivity].
Qed.


End Mem.






End FXG.
