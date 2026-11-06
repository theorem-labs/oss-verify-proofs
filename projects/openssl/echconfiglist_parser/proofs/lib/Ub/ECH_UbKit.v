(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import ECH_Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma land_7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_15 : forall x, Z.land x 15 = x mod 16.
Proof. intros x. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma al8 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. rewrite land_7. exact H. Qed.
Lemma al4 : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x H. rewrite land_3. exact H. Qed.
Lemma al2 : forall x, x mod 2 = 0 -> Z.land x 1 = 0.
Proof. intros x H. rewrite land_1. exact H. Qed.
Lemma al8u : forall x, x mod 8 = 0 -> 0 <= x < 2^64 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof. intros x H R. rewrite unsigned_lit by lia. apply al8, H. Qed.
Lemma al4u : forall x, x mod 4 = 0 -> 0 <= x < 2^64 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 3 = 0.
Proof. intros x H R. rewrite unsigned_lit by lia. apply al4, H. Qed.

(* [comment removed for export] *)
Ltac ubal_solve := first [assumption | lia].
Ltac ubal :=
  repeat match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] => rewrite (al8u x) by ubal_solve
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (al4u x) by ubal_solve
  | |- context [Z.land ?x 7] => rewrite (al8 x) by ubal_solve
  | |- context [Z.land ?x 3] => rewrite (al4 x) by ubal_solve
  | |- context [Z.land ?x 1] => rewrite (al2 x) by ubal_solve
  end.
(* [comment removed for export] *)
Ltac ubal_by H :=
  match goal with
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] => rewrite (al8u x) by (first [exact H | revert H; clear; intros H; lia | lia])
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (al4u x) by (first [exact H | revert H; clear; intros H; lia | lia])
  | |- context [Z.land ?x 7] => rewrite (al8 x) by (first [exact H | revert H; clear; intros H; lia | lia])
  | |- context [Z.land ?x 3] => rewrite (al4 x) by (first [exact H | revert H; clear; intros H; lia | lia])
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ub_dead :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU;
  [ exfalso; revert KU; rewrite ?unsigned_lit, ?signed_lit by lia; intros KU; lia
  | clear KU ].
Tactic Notation "ub_dead_by" tactic(tac) :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU;
  [ exfalso; revert KU; rewrite ?unsigned_lit, ?signed_lit by lia; tac; intros KU; lia
  | clear KU ].
(* [comment removed for export] *)
Ltac ub_dead2 :=
  let KU := fresh "KU" in
  if_cases KU; zify_cond KU;
  [ clear KU
  | exfalso; revert KU; rewrite ?unsigned_lit, ?signed_lit by lia; intros KU; lia ].

(* [comment removed for export] *)
Lemma al_add : forall a k n, a mod n = 0 -> k mod n = 0 -> n <> 0 -> (a + k) mod n = 0.
Proof. intros a k n Ha Hk Hn. rewrite Z.add_mod, Ha, Hk by lia. rewrite Z.mod_0_l by lia. reflexivity. Qed.
Lemma al16_8 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof. intros a H. lia. Qed.
Lemma al_sp : forall s k, s mod 16 = 0 -> k mod 8 = 0 -> (s + k) mod 8 = 0.
Proof. intros s k Hs Hk. lia. Qed.

(* [comment removed for export] *)
Ltac ubnot :=
  repeat match goal with
  | |- context [Z.lxor (bv_unsigned (Z_to_bv 64 ?x)) 18446744073709551615] => rewrite (unsigned_lit x) by lia
  end;
  rewrite ?zb_lxor_ones by lia.

(* [comment removed for export] *)
Lemma ub_nullcons : forall d x, 0 < d -> 0 < x -> Z.lxor (Z.b2z (0 <? d)) (Z.b2z (x <? 1)) = 1.
Proof.
  intros d x Hd Hx. replace (0 <? d) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ub_ltb_pos : forall d, 0 < d -> (0 <? d) = true.
Proof. intros d H. apply Z.ltb_lt. lia. Qed.
Lemma ub_ltb1_false : forall x, 0 < x -> (x <? 1) = false.
Proof. intros x H. apply Z.ltb_ge. lia. Qed.
Lemma ub_ltb_false : forall x y, y <= x -> (x <? y) = false.
Proof. intros x y H. apply Z.ltb_ge. lia. Qed.
Lemma ub_ltb_true : forall x y, x < y -> (x <? y) = true.
Proof. intros x y H. apply Z.ltb_lt. lia. Qed.
Lemma ub_eqb_false : forall x y, x <> y -> (x =? y) = false.
Proof. intros x y H. apply Z.eqb_neq. lia. Qed.
(* [comment removed for export] *)
Ltac ub_b2z :=
  rewrite ?zb_lxor_sign by lia;      (* [comment removed for export] *)
  repeat match goal with
  | |- context [Z.b2z ((?x + 9223372036854775808) mod 18446744073709551616 <? ?y)] =>
      first [ rewrite (ub_ltb_true ((x + 9223372036854775808) mod 18446744073709551616) y) by (rewrite Z.mod_small by lia; lia)
            | rewrite (ub_ltb_false ((x + 9223372036854775808) mod 18446744073709551616) y) by (rewrite Z.mod_small by lia; lia) ]; cbn [Z.b2z]
  | |- context [Z.b2z (?x <? ?y)] =>
      first [ rewrite (ub_ltb_true x y) by lia | rewrite (ub_ltb_false x y) by lia ]; cbn [Z.b2z]
  | |- context [Z.b2z (?x =? ?y)] =>
      first [ rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (ub_eqb_false x y) by lia ]; cbn [Z.b2z]
  | |- context [Z.b2z (negb ?b)] => cbn [negb Z.b2z]
  end.
