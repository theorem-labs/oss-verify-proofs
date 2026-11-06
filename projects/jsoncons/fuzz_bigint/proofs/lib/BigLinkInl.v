(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BIL.
Lemma In_of_existsb (i : nat) (l : list nat) : existsb (Nat.eqb i) l = true -> In i l.
Proof. intros H. apply existsb_exists in H as (x & Hx & E). apply Nat.eqb_eq in E. subst. exact Hx. Qed.
End BIL.
