(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma mf_mod16_8 : forall p, p mod 16 = 0 -> p mod 8 = 0.
Proof. intros p H. apply Z.mod_divide in H; [| discriminate]. apply Z.mod_divide; [discriminate|]. destruct H as [q ->]. exists (q * 2). ring. Qed.
Lemma mf_mod4096_8 : forall p, p mod 4096 = 0 -> p mod 8 = 0.
Proof. intros p H. apply Z.mod_divide in H; [| discriminate]. apply Z.mod_divide; [discriminate|]. destruct H as [q ->]. exists (q * 512). ring. Qed.
Lemma mf_add_mod8 : forall p c, p mod 8 = 0 -> c mod 8 = 0 -> (p + c) mod 8 = 0.
Proof. intros p c Hp Hc. rewrite Z.add_mod by discriminate. rewrite Hp, Hc. reflexivity. Qed.
Lemma mf_mod8_le : forall a k, k <= 1 -> a mod 8 + k <= 8.
Proof. intros a k Hk. pose proof (Z.mod_pos_bound a 8 eq_refl). lia. Qed.
Lemma mf_mod8_0_le : forall a k, a mod 8 = 0 -> k <= 8 -> a mod 8 + k <= 8.
Proof. intros a k Ha Hk. rewrite Ha. exact Hk. Qed.

Ltac mf_mod8 :=
  lazymatch goal with
  | |- ?p mod 8 = 0 =>
      first [ assumption
            | match goal with H : p mod 16 = 0 |- _ => exact (mf_mod16_8 p H) | H : p mod 4096 = 0 |- _ => exact (mf_mod4096_8 p H) end
            | lazymatch p with ?q + ?c => apply (mf_add_mod8 q c); [ mf_mod8 | reflexivity ] end ]
  end.
Ltac mf_le_lit := apply Z.leb_le; reflexivity.
Ltac mlia_fast :=
  lazymatch goal with
  | |- _ mod 8 = 0 => mf_mod8
  | |- ?a mod 8 + ?k <= 8 => first [ apply (mf_mod8_le a k); mf_le_lit | apply (mf_mod8_0_le a k); [ mf_mod8 | mf_le_lit ] ]
  end.
