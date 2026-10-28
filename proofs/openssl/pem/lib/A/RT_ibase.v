(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SEGTOP_A : Z := 0xbc6000.
(* [comment removed for export] *)
Definition USTACK_TOP : Z := 0x800000000000.
Definition STACK_WIN : Z := 0x800000.
(* [comment removed for export] *)
Definition RT_STACK : Z := 0x10000.
