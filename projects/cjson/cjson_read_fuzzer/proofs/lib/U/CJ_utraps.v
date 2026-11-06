(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.

Lemma land7_mod8 : forall p, Z.land p 7 = p mod 8.
Proof. intros p. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma align8_land7 : forall p, p mod 8 = 0 -> Z.land p 7 = 0.
Proof. intros p H. rewrite land7_mod8. exact H. Qed.

Lemma align16_mod8 : forall p, p mod 16 = 0 -> p mod 8 = 0.
Proof.
  intros p H. rewrite <- (Z.mod_mod_divide p 16 8 ltac:(exists 2; reflexivity)), H. reflexivity.
Qed.

Lemma align16_land7 : forall p, p mod 16 = 0 -> Z.land p 7 = 0.
Proof. intros p H. apply align8_land7, align16_mod8, H. Qed.

(* [comment removed for export] *)
Lemma align8_add : forall p k, p mod 8 = 0 -> k mod 8 = 0 -> (p + k) mod 8 = 0.
Proof. intros p k Hp Hk. rewrite Z.add_mod, Hp, Hk by lia. reflexivity. Qed.

Lemma align16_add8_land7 : forall p k, p mod 16 = 0 -> k mod 8 = 0 -> Z.land (p + k) 7 = 0.
Proof. intros p k Hp Hk. apply align8_land7, align8_add; [apply align16_mod8, Hp| exact Hk]. Qed.
