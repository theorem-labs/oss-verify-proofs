(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Definition Band (a x : Z) : Prop := a <= 2147446784 \/ 17594333495296 <= x.

Lemma band_bigM : forall a x, Band a x -> 0 <= x -> a <= 2^64 ->
  exists b : Z, 0 <= b <= 1 /\ a <= 2147446784 + b * 36893488147419103232 /\ 17594333495296 * b <= x.
Proof. intros a x [H|H] H0 H1; [exists 0| exists 1]; lia. Qed.

Ltac bandM :=
  repeat match goal with
  | H : context [?a <= 2147446784 \/ 17594333495296 <= ?x] |- _ =>
      let D := fresh "BDsel" in let b := fresh "bMsel" in let BM := fresh "BMf" in
      assert (D : Band a x) by (unfold Band; clear - H; tauto);
      destruct (band_bigM a x D ltac:(lia) ltac:(lia)) as (b & BM); clear D;
      change (a <= 2147446784 \/ 17594333495296 <= x) with (Band a x) in H
  end.
