(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition pstage : Z := 0x2d92c9.  (* [comment removed for export] *)
Definition ustage : Z := 0x31fe99.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition RSTAGE_LEN : Z := 65536.

Lemma pstage_range : 0x2d8000 <= pstage /\ pstage + RSTAGE_LEN <= 0x2ee000.
Proof. unfold pstage, RSTAGE_LEN. split; reflexivity || (vm_compute; discriminate) || easy. Qed.

Lemma ustage_range : 0x31f000 <= ustage /\ ustage + RSTAGE_LEN <= 0x335000.
Proof. unfold ustage, RSTAGE_LEN. split; reflexivity || (vm_compute; discriminate) || easy. Qed.
