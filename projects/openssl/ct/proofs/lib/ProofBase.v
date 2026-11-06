(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.openssl.ct.lib Require Import TopLevel Obligations.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prog ModelInv ProgDetIface ProgDet ProgNoEnomem. (* [comment removed for export] *)

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)





(* [comment removed for export] *)


(* [comment removed for export] *)



(* [comment removed for export] *)
