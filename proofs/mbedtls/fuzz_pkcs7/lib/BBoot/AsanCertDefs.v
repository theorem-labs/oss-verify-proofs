(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan AsanExtNodes AsanNoReplaceNode.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition ASEGS := AsanUbsan.M.loaded_segments.
(* [comment removed for export] *)
Definition ALIMIT : Z := target_alloc_limit.

Definition KC0 : nat := 0.
Definition BFUEL : nat := 400000.
Definition FUEL : nat := 3000.

(* [comment removed for export] *)
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XN_A (nx : nat) : nat -> list expr -> acs -> option acs := XN_asan ASEGS nx.
Definition XB_A : nat -> list expr -> acs -> option (acs * acs) := XB_nr ASEGS BOTH ALIMIT.

(* [comment removed for export] *)
Notation s1_check IT HS p :=
  (check ASEGS IT BOTH NX0 ALIMIT (XN_A NX0) XE0 XB_A HS KC0 BFUEL FUEL None both_init p) (only parsing).
Notation s2_check nx1 IT HS cs1 p :=
  (check ASEGS IT BOTH nx1 ALIMIT (XN_A nx1) XE0 XB_A HS KC0 BFUEL FUEL None cs1 p) (only parsing).
(* [comment removed for export] *)
