(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition pstage : Z := 0x2d9309.
Definition ustage : Z := 0x31f799.

(* [comment removed for export] *)
Definition RSTAGE_LEN : Z := 65536.

Lemma pstage_range : 0x2d8000 <= pstage /\ pstage + RSTAGE_LEN <= 0x30e000.
Proof. unfold pstage, RSTAGE_LEN. split; reflexivity || (vm_compute; discriminate) || easy. Qed.

Lemma ustage_range : 0x31e000 <= ustage /\ ustage + RSTAGE_LEN <= 0x354000.
Proof. unfold ustage, RSTAGE_LEN. split; reflexivity || (vm_compute; discriminate) || easy. Qed.
