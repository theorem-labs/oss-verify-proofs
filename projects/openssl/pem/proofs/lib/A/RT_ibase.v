(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the write-certified stack window). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
(* [StoreOk] is Required and not Imported: this file only needs the one number, and the
   D_* files downstream must keep seeing [stack_window_reach] as an opaque atom. *)
From OSSVerify.Proofs.openssl.pem.lib.Common Require StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SEGTOP_A : Z := 0xbc6000.
(* [comment removed for export] *)
Definition USTACK_TOP : Z := 0x800000000000.
Definition STACK_WIN : Z := 0x800000.
(* [comment removed for export] *)
Definition RT_STACK : Z := 0x10000.
(* The write-certified sub-window inside the stack mapping.  [STACK_WIN] is the MAPPING
   (8 MiB, unchanged at the revision); the kernel model only certifies stores over
   [MemSplit.in_win] = [wok_lo sp0, sp0) with [wok_lo sp0 = sp0 + stack_window_reach -
   stack_max_size], so the floor the D_* contracts may assume is [sp0 - STACK_WOK].
   Spelled against [StoreOk.stack_window_reach] rather than its value so that the number
   lives in exactly one place -- the model's own definition. *)
Definition STACK_WOK : Z := STACK_WIN - StoreOk.stack_window_reach.
