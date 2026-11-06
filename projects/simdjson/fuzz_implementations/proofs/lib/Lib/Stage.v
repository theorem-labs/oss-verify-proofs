(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition pstage : Z := 0xd7ae9.
Definition ustage : Z := 0xe3299.

Definition RSTAGE_LEN : Z := 65536.

Lemma pstage_range : 0xd7000 <= pstage /\ pstage + RSTAGE_LEN <= 0x10b000.
Proof. unfold pstage, RSTAGE_LEN. split; reflexivity || (vm_compute; discriminate) || easy. Qed.

Lemma ustage_range : 0xe2000 <= ustage /\ ustage + RSTAGE_LEN <= 0x117000.
Proof. unfold ustage, RSTAGE_LEN. split; reflexivity || (vm_compute; discriminate) || easy. Qed.
