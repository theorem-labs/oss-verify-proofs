(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Ubsan Require Import UImg F_syscalls StdioFiles Stdio_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Definition ios_cells (m : mem) : Prop := True.
Definition ios_addr (a : Z) : Prop := False.
Lemma ios_cells_any : forall m, ios_cells m.
Proof. intros; exact I. Qed.
Lemma ios_cells_magree : forall (P : Z -> Prop) m m',
  magree usegs P m m' -> (forall a, ios_addr a -> P a) -> ios_cells m -> ios_cells m'.
Proof. intros; exact I. Qed.
Lemma ios_cells_munch : forall W m m', ios_cells m -> munch W m m' -> wmono usegs m m' ->
  (forall a, ios_addr a -> outside W a) -> ios_cells m'.
Proof. intros; exact I. Qed.
