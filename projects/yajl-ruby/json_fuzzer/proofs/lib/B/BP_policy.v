(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition A_CEIL : Z := (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608).        (* [comment removed for export] *)
Definition A_STK_HI : Z := 0x800000000000.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_HSH_LO : Z := (0x7fff8000 + Z.shiftr A_CEIL 3) - (0x7fff8000 + Z.shiftr A_CEIL 3) mod 8.
Definition A_HSH_HI : Z := 0x10007fff8000.      (* [comment removed for export] *)

End RC__1.
Notation POL_STACK P := (forall (a : Z) (k : nat), (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= a -> a + Z.of_nat k <= 0x800000000000 -> P (Z_to_bv 64 a, k)).
Notation POL_IMG P := (forall (a : Z) (k : nat), 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)).
Notation POL_HSH P := (forall (a : Z) (k : nat), A_HSH_LO <= a -> a + Z.of_nat k <= A_HSH_HI -> P (Z_to_bv 64 a, k)).   (* [comment removed for export] *)
Notation POL_LSH P := (forall (a : Z) (k : nat), 0x7fff7000 <= a -> a + Z.of_nat k <= 0x8fff7000 -> P (Z_to_bv 64 a, k)).
Notation POL_NUL P := (forall (a : Z), P (Z_to_bv 64 a, 0%nat)).
