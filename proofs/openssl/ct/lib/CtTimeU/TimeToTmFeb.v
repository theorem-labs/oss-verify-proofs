(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition febW (y : Z) : Z := (y - 1900 + 1900) * 18446744072678759465 + 85899344.
(* [comment removed for export] *)
Definition feb_rot (y k : Z) : Z :=
  Z.lor (Z.land (bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.land (febW y) 18446744073709551615)) k)) 18446744073709551615)
        (Z.land (bv_swrap 32 (Z.shiftl (Z.land (febW y) 18446744073709551615) (32 - k))) 18446744073709551615).
(* [comment removed for export] *)
Definition feb_md2 (y : Z) : Z :=
  bv_swrap 32 (Z.land (Z.b2z (Z.land (Z.land (y - 1900) 18446744073709551615) 3 <? 1)) (Z.b2z (42949672 <? feb_rot y 2)) + 28).
Definition feb_md (y : Z) : Z := if feb_rot y 4 <? 10737419 then 29 else feb_md2 y.

Definition feb_md_checkf (y : Z) : bool := feb_md y =? days_in_month y 2.
Lemma feb_md_check_all : check_from feb_md_checkf (Z.to_nat 10000) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma feb_md_ok : forall y, 0 <= y <= 9999 -> feb_md y = days_in_month y 2.
Proof.
  intros y Hy. apply Z.eqb_eq. apply (check_from_ok feb_md_checkf (Z.to_nat 10000) 0); [exact feb_md_check_all| rewrite Z2Nat.id by lia; lia].
Qed.

Lemma feb_cases : forall y, 0 <= y <= 9999 ->
  (feb_rot y 4 < 10737419 /\ days_in_month y 2 = 29) \/ (10737419 <= feb_rot y 4 /\ feb_md2 y = days_in_month y 2).
Proof.
  intros y Hy. pose proof (feb_md_ok y Hy) as E. unfold feb_md in E.
  destruct (Z.ltb_spec (feb_rot y 4) 10737419); [left| right]; split; lia.
Qed.

Lemma lor_range64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof.
  intros Ha Hb. pose proof (Z.lor_nonneg a b) as N. split; [apply N; lia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [->|NZ]; [lia|].
  apply Z.log2_lt_pow2; [assert (0 <= Z.lor a b) by (apply N; lia); lia|].
  rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [E|E]; [rewrite E; cbn; lia| apply Z.log2_lt_pow2; lia].
  - destruct (Z.eq_dec b 0) as [E|E]; [rewrite E; cbn; lia| apply Z.log2_lt_pow2; lia].
Qed.
Lemma feb_rot_range y k : 0 <= feb_rot y k < 2^64.
Proof.
  unfold feb_rot. apply lor_range64.
  - change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
  - change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
Lemma feb_rot_land y k : Z.land (feb_rot y k) 18446744073709551615 = feb_rot y k.
Proof. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. apply feb_rot_range. Qed.
