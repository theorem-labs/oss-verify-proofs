(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition NHELDc : Z := 13.
Definition NUSERc : Z := 2^27.

Lemma NHELDc_val : NHELDc = 13. Proof. reflexivity. Qed.
Lemma NUSERc_val : NUSERc = 134217728. Proof. reflexivity. Qed.
