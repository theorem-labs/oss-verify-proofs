(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma land_mask2 : forall a, Z.land a 4095 = a mod 4096.
Proof. intros a. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.
