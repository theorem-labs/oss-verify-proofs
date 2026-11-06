(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence FinInput.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StackInit.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP SI.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module InitClf.

Definition PB_CLF (b : int -> list byte) : Prop :=
  exists (a0 : list byte) (eptrs : list word),
    b 1%uint63 = a0 ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) a0 /\ Z.of_nat (length a0) <= 131071 /\
    b 2%uint63 = flat_map word_le8 eptrs ++ word_le8 (Z_to_bv 64 0) /\ Z.of_nat (length eptrs) <= 256 /\
    Forall (fun p => 0 < bv_unsigned p) eptrs /\
    b 8%uint63 = Z_to_le_bytes 8 (8 * Z.of_nat (length eptrs) + 8) /\
    b 9%uint63 = Z_to_le_bytes 8 (Z.of_nat (length a0) + 1).

End InitClf.
