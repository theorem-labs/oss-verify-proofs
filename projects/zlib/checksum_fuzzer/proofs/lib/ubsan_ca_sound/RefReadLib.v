(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Frame RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).











Lemma rdn_wbytes_self : forall segs m (a : word) bs,
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  rdn segs (wbytes m a bs) a (length bs) = Some bs.
Proof. intros. apply rdn_wbytes_hit. assumption. Qed.







Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
