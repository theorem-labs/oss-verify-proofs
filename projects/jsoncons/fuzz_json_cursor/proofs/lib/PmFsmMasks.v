(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma land_mask0 : forall a, Z.land a 16383 = a mod 16384.
Proof. intros a. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_mask4 : forall a, Z.land a 1023 = a mod 1024.
Proof. intros a. change 1023 with (Z.ones 10). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_mask5 : forall a, Z.land a 511 = a mod 512.
Proof. intros a. change 511 with (Z.ones 9). rewrite Z.land_ones by lia. reflexivity. Qed.
