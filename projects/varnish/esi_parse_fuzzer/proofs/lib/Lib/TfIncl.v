(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
#[global] Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma incl_l0 : forall B : Z, B <= B.
Proof. intros; apply Z.le_refl. Qed.
Lemma incl_l1 : forall B k : Z, (0 <=? k) = true -> B <= B + k.
Proof. intros B k H. apply Z.leb_le in H. lia. Qed.
Lemma incl_r0 : forall B n S : Z, (n <=? S) = true -> B + n <= B + S.
Proof. intros B n S H. apply Z.leb_le in H. lia. Qed.
Lemma incl_r1 : forall B k n S : Z, (k + n <=? S) = true -> B + k + n <= B + S.
Proof. intros B k n S H. apply Z.leb_le in H. lia. Qed.
Lemma incl_lit : forall x y : Z, (x <=? y) = true -> x <= y.
Proof. intros x y H. apply Z.leb_le in H. exact H. Qed.

(* [comment removed for export] *)
Ltac is_zlit t := lazymatch t with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Ltac incl_by_lit :=
  match goal with
  | |- ?B <= ?B => exact (incl_l0 B)
  | |- ?B <= ?B + ?k => exact (incl_l1 B k (@eq_refl bool true))
  | |- ?B + ?n <= ?B + ?S => exact (incl_r0 B n S (@eq_refl bool true))
  | |- ?B + ?k + ?n <= ?B + ?S => exact (incl_r1 B k n S (@eq_refl bool true))
  (* [comment removed for export] *)
  | |- ?x + ?n <= ?y + ?S => is_zlit x; is_zlit n; is_zlit y; is_zlit S; exact (incl_lit (x + n) (y + S) (@eq_refl bool true))
  | |- ?x <= ?y => is_zlit x; is_zlit y; exact (incl_lit x y (@eq_refl bool true))
  end.

(* [comment removed for export] *)
Ltac tf_with_region_fast B S a n :=
  let I1 := fresh "INS" in let I2 := fresh "INS" in
  assert (I1 : B <= a) by (first [ incl_by_lit | tf_cfree_lia | tf_lia ]);
  assert (I2 : a + n <= B + S) by (first [ incl_by_lit | tf_cfree_lia | tf_lia ]);
  pose proof (I : tf_reg_found B S).
