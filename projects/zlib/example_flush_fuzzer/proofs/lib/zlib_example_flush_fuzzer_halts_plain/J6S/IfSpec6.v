(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflRod6 InflCtx6 InffastModel InffastCtx InffastSafe IfSpec.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Definition A6_INFLATE_FAST : Z := 0x1f8c0.

Definition inflate_fast_spec6 : Prop :=
  inflate_fast_spec_at s6_segs is6_LENFIX is6_DISTFIX ROD6_LO ROD6_HI IMG6_TOP A6_INFLATE_FAST msg6_addr.

Lemma if6_RO : 0 <= ROD6_LO /\ ROD6_LO <= is6_DISTFIX /\ is6_DISTFIX + 128 <= ROD6_HI /\ ROD6_LO <= is6_LENFIX /\ is6_LENFIX + 2048 <= ROD6_HI /\ ROD6_HI <= IMG6_TOP.
Proof. unfold ROD6_LO, ROD6_HI, is6_DISTFIX, is6_LENFIX, IMG6_TOP. lia. Qed.
End FXG.
