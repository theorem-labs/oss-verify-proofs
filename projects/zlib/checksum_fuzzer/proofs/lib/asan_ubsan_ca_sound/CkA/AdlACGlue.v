(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.cks Require Import CkTables CkModel CkMathAdler CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.CkA Require Import AdlAGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PURE.
  Variables (adler1 adler2 len2 : Z).

  Definition c_lo1 : Z := lo16 adler1.
  Definition c_lo2 : Z := lo16 adler2.
  Definition c_hi1 : Z := hi16 adler1.
  Definition c_hi2 : Z := hi16 adler2.
  Definition c_rem : Z := len2 - amag_q len2 * 65521.
  Definition c_pr : Z := c_rem * c_lo1.
  Definition c_q2 : Z := Z.shiftr (c_pr * 2147975281) 47.
  Definition c_s2m : Z := c_pr - c_q2 * 65521.
  Definition c_S1 : Z := c_lo1 + c_lo2 + 65520.
  Definition c_S2 : Z := c_hi1 + c_hi2 + 65535 - c_rem + c_s2m - 14.
  Definition c_c1 : Z := if 65520 <? c_S1 then c_S1 - 65521 else c_S1.
  Definition c_f1 : Z := if 65520 <? c_c1 then c_c1 - 65521 else c_c1.
  Definition c_c2 : Z := if 131041 <? c_S2 then c_S2 - 131042 else c_S2.
  Definition c_f2 : Z := if 65520 <? c_c2 then c_c2 - 65521 else c_c2.
  Definition adlc_val : Z := Z.lor (c_f2 * 65536) c_f1.

  Lemma c_lo1_range : 0 <= c_lo1 < 65536.  Proof. apply lo16_range. Qed.
  Lemma c_lo2_range : 0 <= c_lo2 < 65536.  Proof. apply lo16_range. Qed.
  Lemma c_hi1_range : 0 <= c_hi1 < 65536.  Proof. apply hi16_range. Qed.
  Lemma c_hi2_range : 0 <= c_hi2 < 65536.  Proof. apply hi16_range. Qed.

  Section HYPS.
  Hypothesis Hn : 0 <= len2 < 2^63.

  Lemma c_rem_val : c_rem = len2 mod BASE.
  Proof. unfold c_rem. apply amag_mod. lia. Qed.

  Lemma c_rem_range : 0 <= c_rem < 65521.
  Proof. rewrite c_rem_val. apply Z.mod_pos_bound. unfold BASE. lia. Qed.

  Lemma c_pr_range : 0 <= c_pr < 65521 * 65536.
  Proof. unfold c_pr. pose proof c_rem_range. pose proof c_lo1_range. nia. Qed.

  Lemma c_q2_val : c_q2 = c_pr / BASE.
  Proof. unfold c_q2. change 2147975281 with AMAGIC2. apply adler_magic2_div. pose proof c_pr_range. lia. Qed.

  Lemma c_s2m_val : c_s2m = c_pr mod BASE.
  Proof. unfold c_s2m. rewrite c_q2_val. change 65521 with BASE. apply mod_BASE_sub. Qed.

  Lemma c_s2m_range : 0 <= c_s2m < 65521.
  Proof. rewrite c_s2m_val. apply Z.mod_pos_bound. unfold BASE. lia. Qed.

  Lemma c_prA_range : 0 <= c_pr * 2147975281 < 2^64.
  Proof. pose proof c_pr_range. nia. Qed.

  Lemma c_q2_range : 0 <= c_q2 * 65521 <= c_pr.
  Proof.
    rewrite c_q2_val. pose proof c_pr_range. unfold BASE. Z.div_mod_to_equations. lia.
  Qed.

  Lemma csub_if : forall x, csub x = (if 65520 <? x then x - 65521 else x).
  Proof. intros x. unfold csub, BASE. destruct (Z.leb_spec 65521 x), (Z.ltb_spec 65520 x); lia. Qed.

  Lemma csub2_if : forall x, (if 2 * BASE <=? x then x - 2 * BASE else x) = (if 131041 <? x then x - 131042 else x).
  Proof. intros x. unfold BASE. destruct (Z.leb_spec (2 * 65521) x), (Z.ltb_spec 131041 x); lia. Qed.

  Theorem adlc_val_model : adlc_val = adler32_combine_model adler1 adler2 len2.
  Proof.
    unfold adler32_combine_model.
    destruct (Z.ltb_spec len2 0); [lia|].
    cbv zeta. rewrite <- c_rem_val.
    change (Z.land adler1 65535) with c_lo1. change (Z.land adler2 65535) with c_lo2.
    change (Z.land (Z.shiftr adler1 16) 65535) with c_hi1. change (Z.land (Z.shiftr adler2 16) 65535) with c_hi2.
    change (c_rem * c_lo1) with c_pr. rewrite <- c_s2m_val.
    rewrite !csub_if, csub2_if.
    unfold adlc_val, adler_comb, c_f1, c_c1, c_f2, c_c2, c_S1, c_S2.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. unfold BASE. change (2 ^ 16) with 65536.
    replace (c_lo1 + (c_lo2 + 65521 - 1)) with (c_lo1 + c_lo2 + 65520) by lia.
    replace (c_s2m + (c_hi1 + c_hi2 + 65521 - c_rem)) with (c_hi1 + c_hi2 + 65535 - c_rem + c_s2m - 14) by lia.
    reflexivity.
  Qed.
  End HYPS.
End PURE.

Lemma zext_swrap32_small : forall x, 0 <= x < 2^31 -> (bv_swrap 32 x mod 18446744073709551616) mod 4294967296 = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Lemma add_neg_mach : forall x K k, K + k = 18446744073709551616 -> Z_to_bv 64 (x + K) = Z_to_bv 64 (x - k).
Proof.
  intros x K k HK. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace (x + K) with (x - k + 1 * 18446744073709551616) by lia. apply Z.mod_add. lia.
Qed.

Lemma csel_mach : forall x T K k, 0 <= K < 2^64 -> K + k = 18446744073709551616 ->
  Z_to_bv 64 (x + Z.land ((0 - Z.b2z (T <? x)) mod 18446744073709551616) K) = Z_to_bv 64 (if T <? x then x - k else x).
Proof.
  intros x T K k HK HS. rewrite land_negflag by lia. destruct (T <? x).
  - apply add_neg_mach. exact HS.
  - rewrite Z.add_0_r. reflexivity.
Qed.
