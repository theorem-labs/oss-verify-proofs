(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.

Lemma qh_t2h : forall x w, 0 <= x < M64 -> 0 <= w < M64 ->
  Z.shiftr ((Z.shiftr x 32 * (w mod 4294967296) + Z.land x 4294967295 * Z.shiftr w 32) mod M64) 32
  + Z.shiftr x 32 * Z.shiftr w 32
  + Z.shiftl (Z.b2z ((Z.shiftr x 32 * (w mod 4294967296) + Z.land x 4294967295 * Z.shiftr w 32) mod M64 <? (Z.shiftr x 32 * (w mod 4294967296)) mod M64)) 32
  + Z.b2z ((x * w) mod M64 <? (Z.shiftl ((Z.shiftr x 32 * (w mod 4294967296) + Z.land x 4294967295 * Z.shiftr w 32) mod M64) 32) mod M64)
  = (x * w) / M64.
Proof. intros x w Hx Hw. mul64_solve x w Hx Hw. Qed.

Lemma qhat_corr_exit0 : forall f q rem t2l t2h n2 d0 d1,
  t2h < rem -> qhat_corr f q rem t2l t2h n2 d0 d1 = q.
Proof.
  intros [|f] q rem t2l t2h n2 d0 d1 H; cbn [qhat_corr]; [reflexivity|].
  destruct (Z.ltb_spec t2h rem); [reflexivity | lia].
Qed.

Lemma qhat_corr_exit1 : forall f q rem t2l t2h n2 d0 d1,
  t2h = rem -> t2l <= n2 -> qhat_corr f q rem t2l t2h n2 d0 d1 = q.
Proof.
  intros [|f] q rem t2l t2h n2 d0 d1 H1 H2; cbn [qhat_corr]; [reflexivity|].
  destruct (Z.eqb_spec t2h rem); [|lia]. destruct (Z.leb_spec t2l n2); [|lia].
  rewrite orb_true_r. reflexivity.
Qed.

Lemma qhat_corr_exit2 : forall f q rem t2l t2h n2 d0 d1,
  rem <= t2h -> (t2h <> rem \/ n2 < t2l) -> addw rem d0 < d0 ->
  qhat_corr (S f) q rem t2l t2h n2 d0 d1 = subw q 1.
Proof.
  intros f q rem t2l t2h n2 d0 d1 H1 H2 H3. cbn [qhat_corr].
  destruct (Z.ltb_spec t2h rem); [lia|]. cbn [orb].
  assert (E : (t2h =? rem) && (t2l <=? n2) = false).
  { destruct (Z.eqb_spec t2h rem); [|reflexivity]. destruct (Z.leb_spec t2l n2); [lia | reflexivity]. }
  rewrite E. destruct (Z.ltb_spec (addw rem d0) d0); [reflexivity | lia].
Qed.

Lemma qhat_corr_cont : forall f q rem t2l t2h n2 d0 d1,
  rem <= t2h -> (t2h <> rem \/ n2 < t2l) -> d0 <= addw rem d0 ->
  qhat_corr (S f) q rem t2l t2h n2 d0 d1 =
  qhat_corr f (subw q 1) (addw rem d0) (subw t2l d1) (if t2l <? d1 then subw t2h 1 else t2h) n2 d0 d1.
Proof.
  intros f q rem t2l t2h n2 d0 d1 H1 H2 H3. cbn [qhat_corr].
  destruct (Z.ltb_spec t2h rem); [lia|]. cbn [orb].
  assert (E : (t2h =? rem) && (t2l <=? n2) = false).
  { destruct (Z.eqb_spec t2h rem); [|reflexivity]. destruct (Z.leb_spec t2l n2); [lia | reflexivity]. }
  rewrite E. destruct (Z.ltb_spec (addw rem d0) d0); [lia | reflexivity].
Qed.

Lemma subw_lit : forall a b, 0 <= subw a b < 18446744073709551616. Proof. intros. apply subw_limb. Qed.
Lemma addw_lit : forall a b, 0 <= addw a b < 18446744073709551616. Proof. intros. apply addw_limb. Qed.
Lemma t2h_step_lit : forall t2l t2h d1, 0 <= t2h < 18446744073709551616 ->
  0 <= (if t2l <? d1 then subw t2h 1 else t2h) < 18446744073709551616.
Proof. intros. destruct (t2l <? d1); [apply subw_lit | assumption]. Qed.
Lemma mul_hi_lit : forall x w, 0 <= x < 18446744073709551616 -> 0 <= w < 18446744073709551616 ->
  0 <= (x * w) / BW < 18446744073709551616.
Proof.
  intros x w Hx Hw. rewrite BW_lit. assert (0 <= x * w <= 18446744073709551615 * 18446744073709551615) by nia.
  Z.div_mod_to_equations; lia.
Qed.
Lemma mod_BW_lit : forall x, 0 <= x mod BW < 18446744073709551616. Proof. intros. apply limb_mod. Qed.

Lemma qhat_corr_lit : forall f q rem t2l t2h n2 d0 d1, 0 <= q < 18446744073709551616 ->
  0 <= qhat_corr f q rem t2l t2h n2 d0 d1 < 18446744073709551616.
Proof.
  induction f as [|f IH]; intros q rem t2l t2h n2 d0 d1 Hq; cbn [qhat_corr]; [exact Hq|].
  destruct ((t2h <? rem) || ((t2h =? rem) && (t2l <=? n2))); [exact Hq|].
  destruct (addw rem d0 <? d0); [apply subw_lit|]. apply IH. apply subw_lit.
Qed.
