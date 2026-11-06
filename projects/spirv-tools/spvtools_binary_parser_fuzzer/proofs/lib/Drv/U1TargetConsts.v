(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x65cdc.
Definition EMPTY_OBJ : Z := 0x100260.
Definition TD_LOCALE : Z := 0x1023e8.
Definition GLOBAL_LOCALE : Z := 0x1226e0.
