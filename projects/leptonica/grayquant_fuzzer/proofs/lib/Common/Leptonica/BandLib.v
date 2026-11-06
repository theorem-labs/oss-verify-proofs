(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec SeqExec CatSim StepTac Hoare StoreOk MemSplit StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive RefPrintfLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac DitherLib2 DitherTac2.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma dl_qbitword_w : forall line j, 0 <= j < 2 ^ 31 ->
  alu64 ALU_ADD (Z_to_bv 64 line) (mul_div M_MUL (Z_to_bv 64 4) (sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 j)) (low32 (Z_to_bv 64 3)))))
  = Z_to_bv 64 (line + 4 * (j / 8)).
Proof.
  intros line j Hj. rewrite dl_srlw_small by lia. change (2 ^ 3) with 8.
  assert (D : 0 <= j / 8 < 2 ^ 29) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite dl_mul4 by lia. apply alu_add_Z.
Qed.

Ltac dl_an_pass_q := dl_an_pass; rewrite ?dl_qbitword_w by lia.
Ltac dl_an ::= repeat (progress dl_an_pass_q).
