(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AFUZZ_ENTRY : Z := 0xb11b4.   (* [comment removed for export] *)
Definition ATRUN_RET : Z := 0xb0d54.     (* [comment removed for export] *)
Definition AEMPTY : Z := 0x6a2a20.       (* [comment removed for export] *)
Definition ANEWH : Z := 0x6a2c50.        (* [comment removed for export] *)
Definition AVEC : Z := 0x6a2a40.         (* [comment removed for export] *)
Definition AVEC_GUARD : Z := 0x6a2a80.   (* [comment removed for export] *)
Definition AFALLBACK : Z := 0x6a2bc0.    (* [comment removed for export] *)
Definition AFALLBACK_VT : Z := 0x161350. (* [comment removed for export] *)
Definition ADTOR_THUNK : Z := 0xb1194.   (* [comment removed for export] *)
Definition AATCXA : Z := 0x76950.        (* [comment removed for export] *)
Definition AOPNEW_RET : Z := 0x15fb58.   (* [comment removed for export] *)
Definition AVECDEL_RET : Z := 0xb11a8.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AHARNESS_STACK : Z := 16384.

Definition w0 : word := Z_to_bv 64 0.
Definition guard0 : list cell := [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Definition guard1 : list cell := [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].   (* [comment removed for export] *)
End CANSEC1.
