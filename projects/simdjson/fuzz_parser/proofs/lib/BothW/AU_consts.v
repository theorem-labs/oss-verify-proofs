(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AFUZZ_ENTRY : Z := 0x95600.   (* [comment removed for export] *)
Definition ATRUN_RET : Z := 0x954fc.     (* [comment removed for export] *)
Definition AEMPTY : Z := 0x64dce0.       (* [comment removed for export] *)
Definition ANEWH : Z := 0x64deb0.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AACTIVE : Z := 0x64dd80.
Definition AACTIVE_GUARD : Z := 0x64dda0.
Definition AFALLBACK : Z := 0x64de20.
Definition AFALLBACK_GUARD : Z := 0x64de80.
Definition AFALLBACK_VT : Z := 0x10f610. (* [comment removed for export] *)
Definition AFALLBACK_NAME : Z := 0x27bc0.   (* [comment removed for export] *)
Definition AFALLBACK_DESC : Z := 0x27dc0.   (* [comment removed for export] *)
Definition AOPNEW_RET : Z := 0x10e0d4.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AHARNESS_STACK : Z := 16384.

Definition w0 : word := Z_to_bv 64 0.
Definition guard0 : list cell := [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Definition guard1 : list cell := [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition fallback_cells : list cell :=
  [C8 (Z_to_bv 64 AFALLBACK_VT); C8 (Z_to_bv 64 AFALLBACK_NAME); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 AFALLBACK_DESC); C8 (Z_to_bv 64 0x1f); C4 w0].
End CANSEC1.
