(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import SoftFloat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma lo64_range : forall y, (0 <= lo64 y < 2^64)%Z.
Proof. intros y. unfold lo64. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall y, (0 <= hi64 y < 2^64)%Z.
Proof. intros y. unfold hi64. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma lo64_hi64 : forall y, (0 <= y < 2^128)%Z -> (lo64 y + 2^64 * hi64 y)%Z = y.
Proof.
  intros y Hy. unfold lo64, hi64. rewrite !wrap64_mod. rewrite Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small (y / 2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; change (2^64 * 2^64)%Z with (2^128)%Z; lia]).
  pose proof (Z.div_mod y (2^64) ltac:(lia)). lia.
Qed.

Section Ranges128.
  Local Open Scope Z_scope.
  Lemma mk128_range : forall hi lo, 0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= mk128 hi lo < 2^128.
  Proof.
    intros hi lo Hh Hl. unfold mk128. apply Bytes.lor_lt_pow2; [|lia].
    rewrite Z.shiftl_mul_pow2 by lia. change (2^128) with (2^64 * 2^64). nia.
  Qed.
  Lemma shr64_range64 : forall a k, 0 <= a < 2^64 -> 0 <= k -> 0 <= Z.shiftr a k < 2^64.
  Proof. intros. apply PropExec.Z_shiftr_range; lia. Qed.
  Lemma sra63_range : forall x, 0 <= sra63 x < 2^64.
  Proof. intros x. unfold sra63, ONES64. destruct (is_neg64 x); cbn; lia. Qed.
  Lemma f128_of_d_range : forall d, 0 <= f128_of_d d < 2^128.
  Proof.
    intros d. unfold f128_of_d.
    set (aRep := lo64 d). set (aExp := Z.shiftr (shl64 aRep 1) 53). set (aSig := Z.shiftr (shl64 aRep 12) 12).
    set (signHi := shl64 (Z.shiftr aRep 63) 63).
    assert (RaRep : 0 <= aRep < 2^64) by (subst aRep; unfold lo64; apply wrap64_range).
    assert (RaSig : 0 <= aSig < 2^64) by (subst aSig; apply shr64_range64; [apply wrap64_range | lia]).
    assert (RsignHi : 0 <= signHi < 2^64) by (subst signHi; apply wrap64_range).
    assert (RINF : 0 <= INF_HI < 2^64) by (unfold INF_HI; lia).
    assert (RIMP : 0 <= IMPLICIT_HI < 2^64) by (unfold IMPLICIT_HI; lia).
    assert (G : forall e s, 0 <= e < 2^64 -> 0 <= s < 2^64 -> 0 <= Z.lor (Z.lor e s) signHi < 2^64).
    { intros e s He Hs. apply PropExec.Z_lor_range; [apply PropExec.Z_lor_range|]; lia. }
    cbv zeta.
    destruct (negb (aExp =? 0)).
    - destruct (negb (aExp =? 2047)); apply mk128_range; try apply wrap64_range;
        apply G; try apply wrap64_range; try (apply shr64_range64; lia). exact RINF.
    - destruct (aSig =? 0).
      + apply mk128_range; [|lia]. apply G; [apply wrap64_range | lia].
      + apply mk128_range.
        * apply G; [apply wrap64_range|]. apply PropExec.Z_lxor_range; [|exact RIMP].
          destruct (negb (is_neg64 _)); [apply wrap64_range|]. apply shr64_range64; [|apply Z.land_nonneg; lia].
          apply shr64_range64; lia.
        * apply Bytes.land_lt_pow2; [apply sra63_range|].
          pose proof (wrap64_range (Z.shiftl aSig (Z.land (add64 (clz64_mirror aSig) 49) 63))). unfold shl64. lia.
  Qed.
End Ranges128.
