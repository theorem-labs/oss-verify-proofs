(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Lemma page_round_up_Z_aligned : forall z,
(page_round_up_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.
Lemma page_round_up_Z_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
intro z. unfold page_round_up_Z, page_size.
pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
lia.
Qed.
