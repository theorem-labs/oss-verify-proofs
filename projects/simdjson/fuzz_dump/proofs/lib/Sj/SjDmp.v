(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition dmp_next (t w i : Z) : Z :=
  if 32 <? (t - 91) mod 2^64 then i + 1
  else if Z.testbit 0x4020200 (t - 91) then i + 2
  else if Z.testbit 0x100000001 (t - 91) then w mod 2^32
  else i + 1.

Lemma mask2_bits : forall k, 0 <= k <= 32 -> Z.testbit 0x4020200 k = ((k =? 9) || (k =? 17) || (k =? 26))%bool.
Proof.
  intros k Hk.
  assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16
              \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32) by lia.
  repeat (destruct C as [->|C]; [reflexivity|]). subst k. reflexivity.
Qed.

Lemma maskc_bits : forall k, 0 <= k <= 32 -> Z.testbit 0x100000001 k = ((k =? 0) || (k =? 32))%bool.
Proof.
  intros k Hk.
  assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16
              \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32) by lia.
  repeat (destruct C as [->|C]; [reflexivity|]). subst k. reflexivity.
Qed.

Lemma ltu32_iff : forall t, 0 <= t < 256 -> (32 <? (t - 91) mod 2^64) = true <-> (t < 91 \/ 123 < t).
Proof.
  intros t Ht. rewrite Z.ltb_lt.
  destruct (Z_lt_le_dec t 91) as [L|G].
  - replace ((t - 91) mod 2^64) with (t - 91 + 2^64) by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; apply Z.mod_small; lia). lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

Lemma dmp_next_after : forall (T : Z -> Z) i, 0 <= T i < 2^64 -> dmp_next (ttype (T i)) (T i) i = after T i.
Proof.
  intros T i Hw.
  assert (TR : 0 <= ttype (T i) < 256) by (unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  unfold dmp_next, after, ty, tnext, t_arr, t_obj, t_i64, t_u64, t_dbl. set (t := ttype (T i)) in *. clearbody t.
  destruct (32 <? (t - 91) mod 2^64) eqn:LT.
  - apply (proj1 (ltu32_iff t TR)) in LT.
    replace (t =? 91) with false by (symmetry; apply Z.eqb_neq; lia). replace (t =? 123) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (t =? 108) with false by (symmetry; apply Z.eqb_neq; lia). replace (t =? 117) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (t =? 100) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - assert (R : 91 <= t <= 123).
    { destruct (Z_lt_le_dec t 91) as [L|G]; [exfalso| destruct (Z_lt_le_dec 123 t) as [L2|G2]; [exfalso| lia]];
        (assert (X : (32 <? (t - 91) mod 2^64) = true) by (apply (proj2 (ltu32_iff t TR)); lia); rewrite X in LT; discriminate). }
    rewrite (mask2_bits (t - 91)) by lia. rewrite (maskc_bits (t - 91)) by lia.
    replace (t - 91 =? 9) with (t =? 100) by (apply eq_true_iff_eq; rewrite !Z.eqb_eq; lia).
    replace (t - 91 =? 17) with (t =? 108) by (apply eq_true_iff_eq; rewrite !Z.eqb_eq; lia).
    replace (t - 91 =? 26) with (t =? 117) by (apply eq_true_iff_eq; rewrite !Z.eqb_eq; lia).
    replace (t - 91 =? 0) with (t =? 91) by (apply eq_true_iff_eq; rewrite !Z.eqb_eq; lia).
    replace (t - 91 =? 32) with (t =? 123) by (apply eq_true_iff_eq; rewrite !Z.eqb_eq; lia).
    destruct (t =? 91) eqn:E91; [apply Z.eqb_eq in E91; subst t; reflexivity|].
    destruct (t =? 123) eqn:E123; [apply Z.eqb_eq in E123; subst t; reflexivity|].
    cbn [orb]. destruct (t =? 100) eqn:E100; destruct (t =? 108) eqn:E108; destruct (t =? 117) eqn:E117; cbn [orb]; reflexivity.
Qed.
