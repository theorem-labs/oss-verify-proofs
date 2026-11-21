(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
Definition SEGTOP_A : Z := 0xbf8000.
(* [comment removed for export] *)
Definition USTACK_TOP : Z := 0x800000000000.
Definition STACK_WIN : Z := 0x800000.
(* [comment removed for export] *)
Definition RT_STACK : Z := 0x10000.
(* The write-certified sub-window inside the stack mapping; see A/RT_ibase.v.  [STACK_WIN]
   is the MAPPING and is unchanged; [STACK_WOK] is the depth the kernel model certifies
   stores over, spelled against [StoreOk.stack_window_reach] so the number lives in exactly
   one place -- the model's own definition. *)
Definition STACK_WOK : Z := STACK_WIN - StoreOk.stack_window_reach.
