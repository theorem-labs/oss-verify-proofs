(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import Image Tac InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.BothW Require Import BImg ABase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.BothW Require Import AKit FsKit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

End CANSEC1.
