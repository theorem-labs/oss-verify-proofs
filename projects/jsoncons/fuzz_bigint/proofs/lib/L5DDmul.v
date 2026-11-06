(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5DDM.
Definition K : Z := 4294967296.          (* [comment removed for export] *)
Definition MM : Z := 2 ^ 64.

Lemma K_val : K = 2 ^ 32. Proof. reflexivity. Qed.
Lemma MM_KK : 2 ^ 64 = K * K. Proof. reflexivity. Qed.
Lemma land_mask32 a : 0 <= a -> Z.land a 4294967295 = a mod K.
Proof. intros Ha. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.

Section it.
  Variables dg hv lv c : Z.
  Hypothesis Hdg : 0 <= dg < 2 ^ 64.
  Hypothesis Hhv : 0 <= hv < K.
  Hypothesis Hlv : 0 <= lv < K.
  Hypothesis Hc : 0 <= c < 2 ^ 64.

  Let hiA := dg / K.
  Let loA := dg mod K.
  Let P1 := hiA * lv.      (* [comment removed for export] *)
  Let P2 := loA * hv.      (* [comment removed for export] *)
  Let P3 := loA * lv.      (* [comment removed for export] *)

  Lemma hiA_rng : 0 <= hiA < K.
  Proof using dg hv lv Hdg. subst hiA. split. apply Z.div_pos; unfold K; lia. apply Z.div_lt_upper_bound. unfold K; lia. rewrite <- MM_KK. lia. Qed.
  Lemma loA_rng : 0 <= loA < K.
  Proof using dg hv lv. subst loA. apply Z.mod_pos_bound. unfold K; lia. Qed.
  Lemma P1_rng : 0 <= P1 < 2 ^ 64. Proof. pose proof hiA_rng. subst P1. rewrite MM_KK. unfold K in *. nia. Qed.
  Lemma P2_rng : 0 <= P2 < 2 ^ 64. Proof. pose proof loA_rng. subst P2. rewrite MM_KK. unfold K in *. nia. Qed.
  Lemma P3_rng : 0 <= P3 < 2 ^ 64. Proof. pose proof loA_rng. subst P3. rewrite MM_KK. unfold K in *. nia. Qed.
  Lemma dg_split : dg = hiA * K + loA.
  Proof using dg hv lv. subst hiA loA. rewrite (Z.mul_comm _ K). apply Z.div_mod. unfold K; lia. Qed.
  Lemma prod_split : dg * (hv * K + lv) + c = (c + K * P1 + K * P2 + P3) + (hiA * hv) * 2 ^ 64.
  Proof. rewrite dg_split at 1. subst P1 P2 P3. rewrite MM_KK. nia. Qed.
  Lemma prod_rng : 0 <= dg * (hv * K + lv) + c < 2 ^ 64 * 2 ^ 64.
  Proof.
    assert (Hy: 0 <= hv * K + lv < 2 ^ 64) by (rewrite MM_KK; unfold K in *; nia).
    split. nia. assert (dg * (hv * K + lv) <= (2 ^ 64 - 1) * (2 ^ 64 - 1)) by nia. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma lo_eq :
    (c + ((K * ((dg / K * lv) mod 2 ^ 64)) mod 2 ^ 64
          + ((K * ((Z.land dg 4294967295 * hv) mod 2 ^ 64)) mod 2 ^ 64 + (Z.land dg 4294967295 * lv) mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64
    = (dg * (hv * K + lv) + c) mod 2 ^ 64.
  Proof.
    rewrite !land_mask32 by lia. fold hiA loA P1 P2 P3. fold P1. fold P2. fold P3.
    change (dg / K * lv) with P1. change (loA * hv) with P2. change (loA * lv) with P3.
    rewrite (Z.mod_small P1) by apply P1_rng. rewrite (Z.mod_small P2) by apply P2_rng. rewrite (Z.mod_small P3) by apply P3_rng.
    rewrite (Z.add_mod_idemp_l (K * P2)) by lia. rewrite (Z.add_mod_idemp_l (K * P1)) by lia. rewrite (Z.add_mod_idemp_r (K * P1)) by lia.
    rewrite Z.add_mod_idemp_r by lia. rewrite prod_split. rewrite Z_mod_plus_full. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hi_eq :
    let T1 := (K * ((dg / K * lv) mod 2 ^ 64)) mod 2 ^ 64 in
    let T2 := (K * ((Z.land dg 4294967295 * hv) mod 2 ^ 64)) mod 2 ^ 64 in
    let P3m := (Z.land dg 4294967295 * lv) mod 2 ^ 64 in
    let T23 := (T2 + P3m) mod 2 ^ 64 in
    let LF := (T1 + T23) mod 2 ^ 64 in
    ((if (c + LF) mod 2 ^ 64 <? LF then 1 else 0)
     + ((if LF <? T23 then 1 else 0)
        + ((if T23 <? T2 then 1 else 0)
           + (((dg / K * lv) mod 2 ^ 64) / K
              + (((Z.land dg 4294967295 * hv) mod 2 ^ 64) / K + (dg / K * hv) mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64
    = (dg * (hv * K + lv) + c) / 2 ^ 64.
  Proof.
    rewrite !land_mask32 by lia.
    change (dg / K * lv) with P1. change (dg mod K * hv) with P2. change (dg mod K * lv) with P3. change (dg / K * hv) with (hiA * hv).
    pose proof P1_rng as R1. pose proof P2_rng as R2. pose proof P3_rng as R3. pose proof hiA_rng as RA.
    rewrite (Z.mod_small P1) by lia. rewrite (Z.mod_small P2) by lia. rewrite (Z.mod_small P3) by lia.
    assert (HHr: 0 <= hiA * hv < 2 ^ 64) by (rewrite MM_KK; unfold K in *; nia). rewrite (Z.mod_small (hiA * hv)) by lia.
    cbv zeta.
    set (T1 := (K * P1) mod 2 ^ 64). set (T2 := (K * P2) mod 2 ^ 64).
    assert (T1r: 0 <= T1 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). assert (T2r: 0 <= T2 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    set (T23 := (T2 + P3) mod 2 ^ 64). assert (T23r: 0 <= T23 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    set (LF := (T1 + T23) mod 2 ^ 64). assert (LFr: 0 <= LF < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    assert (B1: (if (c + LF) mod 2 ^ 64 <? LF then 1 else 0) = (c + LF) / 2 ^ 64).
    { destruct (Z_lt_le_dec (c + LF) (2 ^ 64)).
      - rewrite Z.mod_small, Z.div_small by lia. destruct (Z.ltb_spec (c + LF) LF); lia.
      - rewrite <- (Z_mod_plus_full (c + LF) (-1)) by lia. rewrite Z.mod_small by lia.
        replace ((c + LF) / 2 ^ 64) with 1. destruct (Z.ltb_spec (c + LF + -1 * 2 ^ 64) LF); lia.
        apply (Z.div_unique_pos _ _ 1 (c + LF - 2 ^ 64)); lia. }
    assert (B2: (if LF <? T23 then 1 else 0) = (T1 + T23) / 2 ^ 64).
    { subst LF. destruct (Z_lt_le_dec (T1 + T23) (2 ^ 64)).
      - rewrite Z.mod_small, Z.div_small by lia. destruct (Z.ltb_spec (T1 + T23) T23); lia.
      - rewrite <- (Z_mod_plus_full (T1 + T23) (-1)) by lia. rewrite Z.mod_small by lia.
        replace ((T1 + T23) / 2 ^ 64) with 1. destruct (Z.ltb_spec (T1 + T23 + -1 * 2 ^ 64) T23); lia.
        apply (Z.div_unique_pos _ _ 1 (T1 + T23 - 2 ^ 64)); lia. }
    assert (B3: (if T23 <? T2 then 1 else 0) = (T2 + P3) / 2 ^ 64).
    { subst T23. destruct (Z_lt_le_dec (T2 + P3) (2 ^ 64)).
      - rewrite Z.mod_small, Z.div_small by lia. destruct (Z.ltb_spec (T2 + P3) T2); lia.
      - rewrite <- (Z_mod_plus_full (T2 + P3) (-1)) by lia. rewrite Z.mod_small by lia.
        replace ((T2 + P3) / 2 ^ 64) with 1. destruct (Z.ltb_spec (T2 + P3 + -1 * 2 ^ 64) T2); lia.
        apply (Z.div_unique_pos _ _ 1 (T2 + P3 - 2 ^ 64)); lia. }
    rewrite B1, B2, B3.
    set (q1 := (c + LF) / 2 ^ 64). set (q2 := (T1 + T23) / 2 ^ 64). set (q3 := (T2 + P3) / 2 ^ 64).
    (* [comment removed for export] *)
    pose proof (Z.div_mod (c + LF) (2 ^ 64) ltac:(lia)) as E1. fold q1 in E1.
    pose proof (Z.div_mod (T1 + T23) (2 ^ 64) ltac:(lia)) as E2. fold q2 in E2. fold LF in E2.
    pose proof (Z.div_mod (T2 + P3) (2 ^ 64) ltac:(lia)) as E3. fold q3 in E3. fold T23 in E3.
    assert (E4: K * P1 = 2 ^ 64 * (P1 / K) + T1).
    { subst T1. rewrite MM_KK at 2. rewrite Z.mul_mod_distr_l by (unfold K; lia).
      pose proof (Z.div_mod P1 K ltac:(unfold K; lia)). rewrite MM_KK. nia. }
    assert (E5: K * P2 = 2 ^ 64 * (P2 / K) + T2).
    { subst T2. rewrite MM_KK at 2. rewrite Z.mul_mod_distr_l by (unfold K; lia).
      pose proof (Z.div_mod P2 K ltac:(unfold K; lia)). rewrite MM_KK. nia. }
    assert (q1r: 0 <= q1 < 2). { subst q1. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; [lia|]. lia. }
    assert (q2r: 0 <= q2 < 2). { subst q2. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; [lia|]. lia. }
    assert (q3r: 0 <= q3 < 2). { subst q3. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; [lia|]. lia. }
    assert (D1: 0 <= P1 / K < K). { split. apply Z.div_pos; unfold K in *; lia. apply Z.div_lt_upper_bound; [unfold K; lia|]. rewrite <- MM_KK. lia. }
    assert (D2: 0 <= P2 / K < K). { split. apply Z.div_pos; unfold K in *; lia. apply Z.div_lt_upper_bound; [unfold K; lia|]. rewrite <- MM_KK. lia. }
    set (stored := (c + LF) mod 2 ^ 64) in *. assert (Sr: 0 <= stored < 2 ^ 64) by (subst stored; apply Z.mod_pos_bound; lia).
    set (T := q1 + (q2 + (q3 + (P1 / K + (P2 / K + hiA * hv))))).
    assert (KEY: dg * (hv * K + lv) + c = 2 ^ 64 * T + stored). { rewrite prod_split. subst T. nia. }
    assert (Tval: (dg * (hv * K + lv) + c) / 2 ^ 64 = T).
    { symmetry. apply (Z.div_unique_pos _ _ T stored); lia. }
    assert (Tr: 0 <= T < 2 ^ 64).
    { pose proof prod_rng as PR. rewrite KEY in PR. clear - PR Sr. lia. }
    rewrite Tval. subst T.
    (* [comment removed for export] *)
    rewrite (Z.mod_small (P2 / K + hiA * hv)) by lia. rewrite (Z.mod_small (P1 / K + _)) by lia.
    rewrite (Z.mod_small (q3 + _)) by lia. rewrite (Z.mod_small (q2 + _)) by lia. rewrite (Z.mod_small (q1 + _)) by lia. reflexivity.
  Qed.
End it.

(* [comment removed for export] *)
Lemma hv_rng y : 0 <= y < 2 ^ 64 -> 0 <= y / K < K.
Proof. intros. split. apply Z.div_pos; unfold K; lia. apply Z.div_lt_upper_bound. unfold K; lia. rewrite <- MM_KK; lia. Qed.
Lemma lv_eq y : 0 <= y < 2 ^ 64 -> (K * y) mod 2 ^ 64 / K = y mod K.
Proof.
  intros Hy. rewrite MM_KK. rewrite Z.mul_mod_distr_l by (unfold K; lia). rewrite Z.mul_comm. apply Z.div_mul. unfold K; lia.
Qed.
Lemma lv_rng y : 0 <= y mod K < K.
Proof. apply Z.mod_pos_bound. unfold K; lia. Qed.
Lemma y_split y : 0 <= y -> y = y / K * K + y mod K.
Proof. intros. rewrite (Z.mul_comm _ K). apply Z.div_mod. unfold K; lia. Qed.
End L5DDM.
