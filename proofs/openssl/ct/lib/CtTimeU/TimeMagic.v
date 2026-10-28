(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import MagicDiv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma smagic_neg : forall y m d K e, 0 < d -> 0 < e -> 0 <= K -> m * d = 2^K + e -> 0 < y -> y * e <= 2^K ->
  (- y * m) / 2^K = - (y / d) - 1.
Proof.
  intros y m d K e Hd He HK Hm Hy Hye.
  set (P := 2^K) in *. assert (HP : 0 < P) by (subst P; apply Z.pow_pos_nonneg; lia).
  set (q := y / d). set (r := y mod d).
  assert (Hyqr : y = d * q + r) by (subst q r; apply Z.div_mod; lia).
  assert (Hr : 0 <= r < d) by (subst r; apply Z.mod_pos_bound; lia).
  assert (Hq : 0 <= q) by (subst q; apply Z.div_pos; lia).
  assert (Hm0 : 0 < m) by nia.
  symmetry. apply Z.div_unique_pos with (r := (q + 1) * P - y * m); [| lia].
  split.
  - (* [comment removed for export] *)
    assert (y * m * d <= (q + 1) * P * d) by nia. nia.
  - (* [comment removed for export] *)
    assert (q * P * d < y * m * d) by nia. nia.
Qed.

(* [comment removed for export] *)
Lemma smagic_div : forall x m d K e B, 0 < d -> 0 < e -> 0 <= K -> m * d = 2^K + e -> 0 <= B -> B * e < 2^K -> - B <= x <= B ->
  (x * m) / 2^K + (if x <? 0 then 1 else 0) = Z.quot x d.
Proof.
  intros x m d K e B Hd He HK Hm HB HBe Hx.
  destruct (Z.ltb_spec x 0) as [NEG|POS].
  - assert ((- x) * e <= B * e) by (apply Z.mul_le_mono_nonneg_r; lia).
    replace (x * m) with (- (- x) * m) by lia. rewrite (smagic_neg (- x) m d K e) by lia.
    rewrite <- (Z.opp_involutive x) at 2. rewrite Z.quot_opp_l by lia. rewrite Z.quot_div_nonneg by lia. lia.
  - rewrite Z.add_0_r. rewrite Z.quot_div_nonneg by lia.
    destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.mul_0_l, !Z.div_0_l; lia|].
    assert (x * e <= B * e) by (apply Z.mul_le_mono_nonneg_r; lia).
    apply (magic_div x m d K e); lia.
Qed.

(* [comment removed for export] *)
Lemma nmagic_div : forall x m d K e B, 0 < d -> 0 < e -> 0 <= K -> m * d = 2^K + e -> 0 <= B -> B * e <= 2^K -> 0 <= x <= B ->
  (x * - m) / 2^K + (if 0 <? x then 1 else 0) = - (x / d).
Proof.
  intros x m d K e B Hd He HK Hm HB HBe Hx.
  destruct (Z.ltb_spec 0 x) as [P|Z0].
  - assert (x * e <= B * e) by (apply Z.mul_le_mono_nonneg_r; lia).
    replace (x * - m) with (- x * m) by lia. rewrite (smagic_neg x m d K e) by lia. lia.
  - assert (x = 0) by lia. subst x. rewrite Z.mul_0_l, !Z.div_0_l; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition M86400 : Z := 1749024623285053783.     (* [comment removed for export] *)

Lemma div86400_magic t : - 2^40 <= t <= 2^40 -> (t * M86400) / 2^77 + (if t <? 0 then 1 else 0) = Z.quot t 86400.
Proof. intros. apply (smagic_div t M86400 86400 77 12928 (2^40)); unfold M86400; lia. Qed.

Lemma div146097_magic x : - 2^31 <= x <= 2^31 -> (x * 963315389) / 2^47 + (if x <? 0 then 1 else 0) = Z.quot x 146097.
Proof. intros. apply (smagic_div x 963315389 146097 47 31405 (2^31)); lia. Qed.

Lemma ndiv1460_magic x : 0 <= x <= 2^20 -> (x * - 3012360625) / 2^42 + (if 0 <? x then 1 else 0) = - (x / 1460).
Proof. intros. apply (nmagic_div x 3012360625 1460 42 1396 (2^20)); lia. Qed.

Lemma div36524_magic x : 0 <= x <= 2^20 -> (x * 3853287931) / 2^47 = x / 36524.
Proof. intros. apply (magic_div x 3853287931 36524 47 36516); nia. Qed.

Lemma ndiv146096_magic x : 0 <= x <= 2^20 -> (x * - 3853287931) / 2^49 + (if 0 <? x then 1 else 0) = - (x / 146096).
Proof. intros. apply (nmagic_div x 3853287931 146096 49 146064 (2^20)); lia. Qed.

Lemma div365_magic x : 0 <= x <= 2^20 -> (x * 3012360625) / 2^40 = x / 365.
Proof. intros. apply (magic_div x 3012360625 365 40 349); nia. Qed.

Lemma div36500_magic x : 0 <= x <= 2^20 -> (x * 120494425) / 2^42 = x / 36500.
Proof. intros. apply (magic_div x 120494425 36500 42 1396); nia. Qed.

Lemma div153_magic x : 0 <= x <= 2^20 -> (x * 3593175255) / 2^39 = x / 153.
Proof. intros. apply (magic_div x 3593175255 153 39 127); nia. Qed.

Lemma ndiv5_magic x : 0 <= x <= 2^20 -> (x * - 1717986919) / 2^33 + (if 0 <? x then 1 else 0) = - (x / 5).
Proof. intros. apply (nmagic_div x 1717986919 5 33 3 (2^20)); lia. Qed.

Lemma div3600_magic x : 0 <= x <= 2^20 -> (x * 2443359173) / 2^43 = x / 3600.
Proof. intros. apply (magic_div x 2443359173 3600 43 592); nia. Qed.

Lemma div60_magic x : 0 <= x <= 2^12 -> (x * 34953) / 2^21 = x / 60.
Proof. intros. apply (magic_div x 34953 60 21 28); nia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.

Definition QT (t : Z) : Z := Z.quot t 86400.
Definition RT (t : Z) : Z := Z.rem t 86400.
Definition SG (t : Z) : Z := if RT t <? 0 then -1 else 0.
Definition DAYS (t : Z) : Z := QT t + SG t.
Definition DS (t : Z) : Z := DAYS t + 719468.
Definition ADJ (t : Z) : Z := if RT t <? 0 then 86400 else 0.
Definition ERA_ARG (t : Z) : Z := if 0 <? DS t then DS t else DS t - 146096.
Definition SECS (t : Z) : Z := RT t + ADJ t.
Definition ERA (t : Z) : Z := Z.quot (ERA_ARG t) 146097.
Definition DOE (t : Z) : Z := DS t - ERA t * 146097.
Definition YN (t : Z) : Z := DOE t - DOE t / 1460 + DOE t / 36524 - DOE t / 146096.
Definition YOE (t : Z) : Z := YN t / 365.
Definition DOY (t : Z) : Z := DOE t + YN t / 36500 - YN t / 1460 - 365 * YOE t.
Definition MOY (t : Z) : Z := (5 * DOY t + 2) / 153.
Definition M3 (t : Z) : Z := if DOY t <? 306 then 3 else -9.
Definition MON (t : Z) : Z := MOY t + M3 t.
Definition YR (t : Z) : Z := ERA t * 400 + YOE t + (if MON t <? 3 then 1 else 0).
Definition MDAY (t : Z) : Z := DOY t + - ((153 * MOY t + 2) / 5) + 1.
Definition HH (t : Z) : Z := SECS t / 3600.
Definition S2 (t : Z) : Z := SECS t - HH t * 3600.
Definition MI (t : Z) : Z := S2 t / 60.
Definition SS (t : Z) : Z := S2 t - MI t * 60.

Lemma QR_facts t : MIN_POSIX_TIME <= t <= MAX_POSIX_TIME ->
  t = 86400 * QT t + RT t /\ - 86400 < RT t < 86400 /\ (0 <= t -> 0 <= RT t) /\ (t < 0 -> RT t <= 0) /\ - 719529 <= QT t <= 2932896
  /\ -60 <= DS t <= 3652365.
Proof.
  unfold MIN_POSIX_TIME, MAX_POSIX_TIME, DS, DAYS, SG, QT, RT. intros Ht.
  assert (E : t = 86400 * (t ÷ 86400) + Z.rem t 86400) by (apply Z.quot_rem'; lia).
  pose proof (Z.rem_bound_abs t 86400 ltac:(lia)) as B.
  assert (P : 0 <= t -> 0 <= Z.rem t 86400) by (intros; apply Z.rem_nonneg; lia).
  assert (N : t < 0 -> Z.rem t 86400 <= 0) by (intros; apply Z.rem_nonpos; lia).
  destruct (Z.ltb_spec (Z.rem t 86400) 0); lia.
Qed.

Ltac mlia := Z.to_euclidean_division_equations; lia.

Lemma ERA_facts t : MIN_POSIX_TIME <= t <= MAX_POSIX_TIME -> -1 <= ERA t <= 24 /\ 0 <= DOE t <= 146096 /\ - 146156 <= ERA_ARG t <= 3652365.
Proof.
  intros Ht. pose proof (QR_facts t Ht) as (_ & _ & _ & _ & _ & HDS). unfold DOE, ERA, ERA_ARG.
  destruct (Z.ltb_spec 0 (DS t)) as [P|N].
  - rewrite Z.quot_div_nonneg by lia. mlia.
  - destruct (Z.eq_dec (DS t) 0) as [E|NE].
    + rewrite E. change ((0 - 146096) ÷ 146097) with 0. lia.
    + replace ((DS t - 146096) ÷ 146097) with (-1); [lia|].
      rewrite <- (Z.opp_involutive (DS t - 146096)), Z.quot_opp_l by lia. rewrite Z.quot_div_nonneg by lia. mlia.
Qed.

Lemma SECS_facts t : MIN_POSIX_TIME <= t <= MAX_POSIX_TIME -> 0 <= SECS t < 86400 /\ 0 <= HH t <= 23 /\ 0 <= S2 t < 3600 /\ 0 <= MI t <= 59 /\ 0 <= SS t <= 59.
Proof.
  intros Ht. pose proof (QR_facts t Ht) as (_ & HR & _ & _ & _ & _). unfold SS, MI, S2, HH, SECS, ADJ.
  destruct (RT t <? 0) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; mlia.
Qed.

(* [comment removed for export] *)
Definition doe_okb (doe : Z) : bool :=
  let yn := doe - doe / 1460 + doe / 36524 - doe / 146096 in
  let yoe := yn / 365 in
  let doy := doe + yn / 36500 - yn / 1460 - 365 * yoe in
  let moy := (5 * doy + 2) / 153 in
  let m := moy + (if doy <? 306 then 3 else -9) in
  let d := doy + - ((153 * moy + 2) / 5) + 1 in
  (0 <=? yn) && (yn <=? doe) && (0 <=? doy) && (doy <=? 365) && (0 <=? moy) && (moy <=? 11) && (1 <=? m) && (m <=? 12) && (1 <=? d) && (d <=? 31).
Lemma doe_okb_all : check_from doe_okb 146097%nat 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma DOE_facts t : MIN_POSIX_TIME <= t <= MAX_POSIX_TIME ->
  0 <= YN t <= DOE t /\ 0 <= DOY t <= 365 /\ 0 <= MOY t <= 11 /\ 1 <= MON t <= 12 /\ 1 <= MDAY t <= 31 /\ 0 <= YOE t <= 400.
Proof.
  intros Ht. pose proof (ERA_facts t Ht) as (_ & HDOE & _).
  pose proof (check_from_ok doe_okb 146097%nat 0 (DOE t) doe_okb_all ltac:(change (Z.of_nat 146097%nat) with 146097; lia)) as C.
  unfold doe_okb in C. cbv zeta in C. unfold MDAY, MON, M3, MOY, DOY, YOE, YN in *.
  repeat (apply andb_prop in C; destruct C as [C ?X]).
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
  repeat split; try lia. all: mlia.
Qed.

(* [comment removed for export] *)
Definition U_days0 (t : Z) : Z := Z.quot t SECS_PER_DAY.
Definition U_secs0 (t : Z) : Z := Z.rem t SECS_PER_DAY.
Definition U_days1 (t : Z) : Z := if U_secs0 t <? 0 then U_days0 t - 1 else U_days0 t.
Definition U_secs (t : Z) : Z := if U_secs0 t <? 0 then U_secs0 t + SECS_PER_DAY else U_secs0 t.
Definition U_days (t : Z) : Z := U_days1 t + 719468.
Definition U_era (t : Z) : Z := Z.quot (if 0 <? U_days t then U_days t else U_days t - 146096) 146097.
Definition U_doe (t : Z) : Z := U_days t - U_era t * 146097.
Definition U_yoe (t : Z) : Z := Z.quot (U_doe t - Z.quot (U_doe t) 1460 + Z.quot (U_doe t) 36524 - Z.quot (U_doe t) 146096) 365.
Definition U_y (t : Z) : Z := U_yoe t + U_era t * 400.
Definition U_doy (t : Z) : Z := U_doe t - (365 * U_yoe t + Z.quot (U_yoe t) 4 - Z.quot (U_yoe t) 100).
Definition U_moy (t : Z) : Z := Z.quot (5 * U_doy t + 2) 153.
Definition U_m (t : Z) : Z := if U_moy t <? 10 then U_moy t + 3 else U_moy t - 9.
Definition U_y2 (t : Z) : Z := if U_m t <=? 2 then U_y t + 1 else U_y t.
Definition U_d (t : Z) : Z := U_doy t - Z.quot (153 * U_moy t + 2) 5 + 1.
Definition U_h (t : Z) : Z := Z.quot (U_secs t) SECS_PER_HOUR.
Definition U_secs2 (t : Z) : Z := Z.rem (U_secs t) SECS_PER_HOUR.
Definition U_mi (t : Z) : Z := Z.quot (U_secs2 t) 60.
Definition U_s (t : Z) : Z := Z.rem (U_secs2 t) 60.

Lemma utc_unfold t : utc_from_posix t =
  if (t <? MIN_POSIX_TIME) || (MAX_POSIX_TIME <? t) then None else Some (mkTM (U_y2 t) (U_m t) (U_d t) (U_h t) (U_mi t) (U_s t)).
Proof.
  unfold utc_from_posix, U_s, U_mi, U_secs2, U_h, U_d, U_y2, U_m, U_moy, U_doy, U_y, U_yoe, U_doe, U_era, U_days, U_secs, U_days1, U_secs0, U_days0.
  destruct ((t <? MIN_POSIX_TIME) || (MAX_POSIX_TIME <? t)); [reflexivity|].
  destruct (Z.rem t SECS_PER_DAY <? 0); reflexivity.
Qed.

(* [comment removed for export] *)
Section Agree.
Variable t : Z.
Hypothesis Ht : MIN_POSIX_TIME <= t <= MAX_POSIX_TIME.

Lemma U_days_eq : U_days t = DS t /\ U_secs t = SECS t.
Proof. unfold U_days, U_secs, U_days1, U_secs0, U_days0, DS, SECS, ADJ, DAYS, SG, QT, RT, SECS_PER_DAY. destruct (Z.rem t 86400 <? 0); lia. Qed.
Lemma U_era_eq : U_era t = ERA t /\ U_doe t = DOE t.
Proof. unfold U_doe, U_era, DOE, ERA, ERA_ARG. rewrite (proj1 U_days_eq). split; reflexivity. Qed.
Lemma U_yoe_eq : U_yoe t = YOE t.
Proof.
  pose proof (ERA_facts t Ht) as (_ & HDOE & _). pose proof (DOE_facts t Ht) as (HYN & _).
  unfold U_yoe. rewrite (proj2 U_era_eq). unfold YOE, YN in *. rewrite !(Z.quot_div_nonneg (DOE t)) by lia. apply Z.quot_div_nonneg; lia.
Qed.
Lemma U_doy_eq : U_doy t = DOY t.
Proof.
  pose proof (ERA_facts t Ht) as (_ & HDOE & _). pose proof (DOE_facts t Ht) as (HYN & _ & _ & _ & _ & HYOE).
  unfold U_doy. rewrite U_yoe_eq, (proj2 U_era_eq). unfold DOY. unfold YOE in *.
  rewrite !Z.quot_div_nonneg by lia. rewrite !Z.div_div by lia. change (365 * 4) with 1460. change (365 * 100) with 36500. lia.
Qed.
Lemma U_moy_eq : U_moy t = MOY t.
Proof. pose proof (DOE_facts t Ht) as (_ & HDOY & _). unfold U_moy, MOY. rewrite U_doy_eq. apply Z.quot_div_nonneg; lia. Qed.
Lemma U_m_eq : U_m t = MON t.
Proof.
  pose proof (DOE_facts t Ht) as (_ & HDOY & HMOY & _). unfold U_m, MON, M3. rewrite U_moy_eq. unfold MOY in *.
  destruct (Z.ltb_spec ((5 * DOY t + 2) / 153) 10); destruct (Z.ltb_spec (DOY t) 306); mlia.
Qed.
Lemma U_y2_eq : U_y2 t = YR t.
Proof.
  unfold U_y2, YR, U_y. rewrite U_m_eq, U_yoe_eq, (proj1 U_era_eq). destruct (Z.leb_spec (MON t) 2); destruct (Z.ltb_spec (MON t) 3); lia.
Qed.
Lemma U_d_eq : U_d t = MDAY t.
Proof. pose proof (DOE_facts t Ht) as (_ & _ & HMOY & _). unfold U_d, MDAY. rewrite U_doy_eq, U_moy_eq. rewrite Z.quot_div_nonneg by lia. lia. Qed.
Lemma U_hms_eq : U_h t = HH t /\ U_mi t = MI t /\ U_s t = SS t.
Proof.
  pose proof (SECS_facts t Ht) as (HS & _). unfold U_s, U_mi, U_secs2, U_h, SS, MI, S2, HH, SECS_PER_HOUR. rewrite (proj2 U_days_eq).
  rewrite (Z.rem_mod_nonneg (SECS t) 3600) by lia. rewrite !Z.quot_div_nonneg by mlia. rewrite Z.rem_mod_nonneg by mlia. mlia.
Qed.

Lemma p2tm_agree : utc_from_posix t = Some (mkTM (YR t) (MON t) (MDAY t) (HH t) (MI t) (SS t)).
Proof.
  rewrite utc_unfold. unfold MIN_POSIX_TIME, MAX_POSIX_TIME in *.
  replace ((t <? -62167219200) || (253402300799 <? t)) with false by (symmetry; apply orb_false_intro; apply Z.ltb_ge; lia).
  destruct U_hms_eq as (A & B & C). rewrite U_y2_eq, U_m_eq, U_d_eq, A, B, C. reflexivity.
Qed.
End Agree.
