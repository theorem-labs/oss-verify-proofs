(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition capk (k : Z) : Z := 65536 * 2 ^ k.            (* [comment removed for export] *)
Definition nbk (k : Z) : Z := capk k + 4096.             (* [comment removed for export] *)
Definition offk (k : Z) : Z := 16 * (k + 2).             (* [comment removed for export] *)
Definition Wk (k : Z) : Z := nbk k + 4064.               (* [comment removed for export] *)
Definition resk (k : Z) : Z := 4060 - 16 * k.            (* [comment removed for export] *)
(* [comment removed for export] *)
Definition slotC (k area : Z) : Z := area + 24 + 40 * (k mod 2).
Definition slotF (k area : Z) : Z := area + 64 - 40 * (k mod 2).
