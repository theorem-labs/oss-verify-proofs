(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition fhold (P : Prop) : Prop := P.
Lemma fhold_in : forall P : Prop, P -> fhold P.
Proof. intros P H. exact H. Qed.
Lemma fhold_out : forall P : Prop, fhold P -> P.
Proof. intros P H. exact H. Qed.
