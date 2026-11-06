(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition CAP_NODE  : Z := 2 ^ 24.
Definition CAP_SMALL : Z := 64.
Definition LIB_BIGCAP : Z := 2 ^ 31.
Definition LIB_STACK : Z := 65536.
Definition LIB_NMAX  : Z := 2 ^ 28.

Definition lib_caps (c : Z) : Z := if c <? 4 then CAP_NODE else CAP_SMALL.

Lemma lib_caps_node : forall c, 0 <= c < 4 -> lib_caps c = CAP_NODE.
Proof. intros c Hc. unfold lib_caps. destruct (Z.ltb_spec c 4); [reflexivity|lia]. Qed.
Lemma lib_caps_small : forall c, 4 <= c -> lib_caps c = CAP_SMALL.
Proof. intros c Hc. unfold lib_caps. destruct (Z.ltb_spec c 4); [lia|reflexivity]. Qed.
Lemma lib_caps_ge_small : forall c, CAP_SMALL <= lib_caps c.
Proof. intros c. unfold lib_caps, CAP_NODE, CAP_SMALL. destruct (c <? 4); simpl; lia. Qed.
