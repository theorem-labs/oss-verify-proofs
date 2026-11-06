(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint check_from (f : Z -> bool) (fuel : nat) (i : Z) : bool :=
  match fuel with O => true | S fuel' => if f i then check_from f fuel' (i + 1) else false end.
Lemma check_from_ok f : forall fuel i x, check_from f fuel i = true -> i <= x < i + Z.of_nat fuel -> f x = true.
Proof.
  induction fuel as [|fu IH]; intros i x H Hx; [lia|]. cbn [check_from] in H.
  destruct (f i) eqn:E; [|discriminate].
  destruct (Z.eq_dec x i) as [->|NE]; [exact E|]. apply (IH (i + 1)); [exact H| rewrite Nat2Z.inj_succ in Hx; lia].
Qed.

Definition SECS_PER_HOUR : Z := 3600.
Definition SECS_PER_DAY : Z := 86400.
Definition MS_PER_DAY : Z := 86400000.
Definition MIN_POSIX_TIME : Z := -62167219200.      (* [comment removed for export] *)
Definition MAX_POSIX_TIME : Z := 253402300799.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition leap_year (y : Z) : bool := (y mod 400 =? 0) || (negb (y mod 100 =? 0) && (y mod 4 =? 0)).
Definition days_in_month (y m : Z) : Z :=
  if (m =? 1) || (m =? 3) || (m =? 5) || (m =? 7) || (m =? 8) || (m =? 10) || (m =? 12) then 31
  else if (m =? 4) || (m =? 6) || (m =? 9) || (m =? 11) then 30
  else if m =? 2 then (if leap_year y then 29 else 28)
  else 0.

(* [comment removed for export] *)
Record tm6 : Type := mkTM { t_year : Z; t_mon : Z; t_mday : Z; t_hour : Z; t_min : Z; t_sec : Z }.

(* [comment removed for export] *)
Definition utc_from_posix (t : Z) : option tm6 :=
  if (t <? MIN_POSIX_TIME) || (MAX_POSIX_TIME <? t) then None
  else
    let days := Z.quot t SECS_PER_DAY in
    let secs := Z.rem t SECS_PER_DAY in
    let '(days, secs) := if secs <? 0 then (days - 1, secs + SECS_PER_DAY) else (days, secs) in
    let days := days + 719468 in
    let era := Z.quot (if 0 <? days then days else days - 146096) 146097 in
    let doe := days - era * 146097 in
    let yoe := Z.quot (doe - Z.quot doe 1460 + Z.quot doe 36524 - Z.quot doe 146096) 365 in
    let y := yoe + era * 400 in
    let doy := doe - (365 * yoe + Z.quot yoe 4 - Z.quot yoe 100) in
    let moy := Z.quot (5 * doy + 2) 153 in
    let m := if moy <? 10 then moy + 3 else moy - 9 in
    let y := if m <=? 2 then y + 1 else y in
    let d := doy - Z.quot (153 * moy + 2) 5 + 1 in
    let h := Z.quot secs SECS_PER_HOUR in
    let secs := Z.rem secs SECS_PER_HOUR in
    let mi := Z.quot secs 60 in
    let s := Z.rem secs 60 in
    Some (mkTM y m d h mi s).

(* [comment removed for export] *)
Definition valid_date (y m d : Z) : bool :=
  (1 <=? d) && (0 <=? y) && (y <=? 9999) && (1 <=? m) && (m <=? 12) && (d <=? days_in_month y m).
Definition valid_time (h mi s : Z) : bool :=
  (0 <=? h) && (0 <=? mi) && (0 <=? s) && (h <=? 23) && (mi <=? 59) && (s <=? 59).

(* [comment removed for export] *)
Definition posix_from_utc (y m d h mi s : Z) : option Z :=
  if negb (valid_date y m d && valid_time h mi s) then None
  else
    let y := if m <=? 2 then y - 1 else y in
    let era := Z.quot (if 0 <=? y then y else y - 399) 400 in
    let yoe := y - era * 400 in
    let doy := Z.quot (153 * (if 2 <? m then m - 3 else m + 9) + 2) 5 + d - 1 in
    let doe := yoe * 365 + Z.quot yoe 4 - Z.quot yoe 100 + doy in
    let pdays := era * 146097 + doe - 719468 in
    Some (pdays * SECS_PER_DAY + h * SECS_PER_HOUR + mi * 60 + s).

(* [comment removed for export] *)
Definition epoch_tm : tm6 := mkTM 1970 1 1 0 0 0.
Lemma utc_from_posix_0 : utc_from_posix 0 = Some epoch_tm.
Proof. vm_compute. reflexivity. Qed.
Lemma posix_from_utc_epoch : posix_from_utc 1970 1 1 0 0 0 = Some 0.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sint32 (x : Z) : Z := let w := x mod 2^32 in if w <? 2^31 then w else w - 2^32.

Definition ts_day (ts : Z) : Z := sint32 (ts / MS_PER_DAY).        (* [comment removed for export] *)
Definition ts_sec (ts : Z) : Z := (ts mod MS_PER_DAY) / 1000.      (* [comment removed for export] *)
Definition ts_ms (ts : Z) : Z := ts mod 1000.                      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition gentime_adj (ts : Z) : option tm6 :=
  let day := ts_day ts in
  let sec := ts_sec ts in
  if (day =? 0) && (sec =? 0) then Some epoch_tm
  else utc_from_posix (day * SECS_PER_DAY + sec).

Definition printable (ts : Z) : bool := match gentime_adj ts with Some _ => true | None => false end.

(* [comment removed for export] *)
Lemma printable_iff ts : 0 <= ts ->
  printable ts = true <-> (ts_day ts = 0 /\ ts_sec ts = 0) \/ (-719528 <= ts_day ts <= 2932896).
Proof.
  intros Hts. unfold printable, gentime_adj.
  assert (Hs : 0 <= ts_sec ts <= 86399).
  { unfold ts_sec, MS_PER_DAY. pose proof (Z.mod_pos_bound ts 86400000 ltac:(lia)).
    assert (ts mod 86400000 / 1000 < 86400) by (apply Z.div_lt_upper_bound; lia). split; [apply Z.div_pos; lia| lia]. }
  destruct (Z.eqb_spec (ts_day ts) 0) as [E0|N0]; destruct (Z.eqb_spec (ts_sec ts) 0) as [E1|N1]; cbn [andb].
  - split; [intros _; left; auto| reflexivity].
  - unfold utc_from_posix, MIN_POSIX_TIME, MAX_POSIX_TIME, SECS_PER_DAY. rewrite E0.
    destruct (Z.ltb_spec (0 * 86400 + ts_sec ts) (-62167219200)); [lia|]. destruct (Z.ltb_spec 253402300799 (0 * 86400 + ts_sec ts)); [lia|].
    cbn [orb]. split; [intros _; right; lia| intros _]. destruct (Z.rem _ _ <? 0); reflexivity.
  - unfold utc_from_posix, MIN_POSIX_TIME, MAX_POSIX_TIME, SECS_PER_DAY.
    destruct (Z.ltb_spec (ts_day ts * 86400 + ts_sec ts) (-62167219200)) as [L|L]; cbn [orb].
    + split; [discriminate| intros [[? ?]|?]; lia].
    + destruct (Z.ltb_spec 253402300799 (ts_day ts * 86400 + ts_sec ts)) as [U|U]; cbn [orb].
      * split; [discriminate| intros [[? ?]|?]; lia].
      * split; [intros _; right; lia| intros _]. destruct (Z.rem _ _ <? 0); reflexivity.
  - unfold utc_from_posix, MIN_POSIX_TIME, MAX_POSIX_TIME, SECS_PER_DAY.
    destruct (Z.ltb_spec (ts_day ts * 86400 + ts_sec ts) (-62167219200)) as [L|L]; cbn [orb].
    + split; [discriminate| intros [[? ?]|?]; lia].
    + destruct (Z.ltb_spec 253402300799 (ts_day ts * 86400 + ts_sec ts)) as [U|U]; cbn [orb].
      * split; [discriminate| intros [[? ?]|?]; lia].
      * split; [intros _; right; lia| intros _]. destruct (Z.rem _ _ <? 0); reflexivity.
Qed.

Lemma ts_day_range ts : -2^31 <= ts_day ts < 2^31.
Proof. unfold ts_day, sint32. pose proof (Z.mod_pos_bound (ts / MS_PER_DAY) (2^32) ltac:(lia)). destruct (Z.ltb_spec ((ts / MS_PER_DAY) mod 2 ^ 32) (2 ^ 31)); lia. Qed.
Lemma ts_sec_range ts : 0 <= ts_sec ts <= 86399.
Proof.
  unfold ts_sec, MS_PER_DAY. pose proof (Z.mod_pos_bound ts 86400000 ltac:(lia)).
  assert (ts mod 86400000 / 1000 < 86400) by (apply Z.div_lt_upper_bound; lia). split; [apply Z.div_pos; lia| lia].
Qed.
Lemma ts_ms_range ts : 0 <= ts_ms ts <= 999.
Proof. unfold ts_ms. pose proof (Z.mod_pos_bound ts 1000 ltac:(lia)). lia. Qed.
(* [comment removed for export] *)
Lemma ts_day_small ts : 0 <= ts < 2^31 * MS_PER_DAY -> ts_day ts = ts / MS_PER_DAY.
Proof.
  intros H. unfold ts_day, sint32, MS_PER_DAY in *.
  assert (0 <= ts / 86400000 < 2^31) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small by lia. destruct (Z.ltb_spec (ts / 86400000) (2^31)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CH_0 : Z := 48. Definition CH_DOT : Z := 46. Definition CH_Z : Z := 90.
Definition digit (k : Z) : Z := CH_0 + k.
(* [comment removed for export] *)
Definition dec2 (n : Z) : list Z := [digit (n / 10); digit (n mod 10)].
Definition dec3 (n : Z) : list Z := [digit (n / 100); digit ((n / 10) mod 10); digit (n mod 10)].
Definition dec4 (n : Z) : list Z := [digit (n / 1000); digit ((n / 100) mod 10); digit ((n / 10) mod 10); digit (n mod 10)].

(* [comment removed for export] *)
Definition gen15 (t : tm6) : list Z :=
  dec4 (t_year t) ++ dec2 (t_mon t) ++ dec2 (t_mday t) ++ dec2 (t_hour t) ++ dec2 (t_min t) ++ dec2 (t_sec t) ++ [CH_Z].
Lemma gen15_length t : length (gen15 t) = 15%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition str_null : list Z := [40; 110; 117; 108; 108; 41].

(* [comment removed for export] *)
Definition genstr (ts : Z) : list Z :=
  match gentime_adj ts with
  | Some t => firstn 14 (gen15 t) ++ [CH_DOT] ++ dec3 (ts_ms ts) ++ [CH_Z]
  | None => str_null ++ [CH_DOT] ++ dec3 (ts_ms ts) ++ [CH_Z]
  end.
Lemma genstr_length ts : length (genstr ts) = if printable ts then 19%nat else 11%nat.
Proof. unfold genstr, printable. destruct (gentime_adj ts); reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tm_valid (t : tm6) : Prop :=
  0 <= t_year t <= 9999 /\ 1 <= t_mon t <= 12 /\ 1 <= t_mday t <= days_in_month (t_year t) (t_mon t)
  /\ 0 <= t_hour t <= 23 /\ 0 <= t_min t <= 59 /\ 0 <= t_sec t <= 59.

(* [comment removed for export] *)
Definition date_of_daynum (dn : Z) : Z * Z * Z :=
  let era := dn / 146097 in
  let doe := dn - era * 146097 in
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 in
  let y := yoe + era * 400 in
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100) in
  let moy := (5 * doy + 2) / 153 in
  let m := if moy <? 10 then moy + 3 else moy - 9 in
  let y := if m <=? 2 then y + 1 else y in
  let d := doy - (153 * moy + 2) / 5 + 1 in
  (y, m, d).

(* [comment removed for export] *)
Definition doe_check (doe : Z) : bool :=
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 in
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100) in
  let moy := (5 * doy + 2) / 153 in
  let m := if moy <? 10 then moy + 3 else moy - 9 in
  let y1 := if m <=? 2 then yoe + 1 else yoe in
  let d := doy - (153 * moy + 2) / 5 + 1 in
  (0 <=? yoe) && (yoe <=? 399) && (0 <=? doy) && (1 <=? m) && (m <=? 12) && (1 <=? d) && (d <=? days_in_month y1 m)
  && ((146036 <? doe) || (y1 <=? 399))          (* [comment removed for export] *)
  && ((doe <=? 146036) || (y1 =? 400)).         (* [comment removed for export] *)

Lemma doe_check_all : check_from doe_check (Z.to_nat 146097) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma doe_check_ok doe : 0 <= doe < 146097 -> doe_check doe = true.
Proof. intros H. apply (check_from_ok doe_check (Z.to_nat 146097) 0); [exact doe_check_all| rewrite Z2Nat.id by lia; lia]. Qed.

Lemma leap_year_add400 y k : leap_year (y + k * 400) = leap_year y.
Proof.
  unfold leap_year.
  replace ((y + k * 400) mod 400) with (y mod 400) by (rewrite Z.add_mod, Z.mod_mul, Z.add_0_r, Z.mod_mod by lia; reflexivity).
  replace ((y + k * 400) mod 100) with (y mod 100).
  2: { replace (k * 400) with ((4 * k) * 100) by lia. rewrite Z.add_mod, Z.mod_mul, Z.add_0_r, Z.mod_mod by lia. reflexivity. }
  replace ((y + k * 400) mod 4) with (y mod 4).
  2: { replace (k * 400) with ((100 * k) * 4) by lia. rewrite Z.add_mod, Z.mod_mul, Z.add_0_r, Z.mod_mod by lia. reflexivity. }
  reflexivity.
Qed.
Lemma days_in_month_add400 y k m : days_in_month (y + k * 400) m = days_in_month y m.
Proof. unfold days_in_month. rewrite leap_year_add400. reflexivity. Qed.

(* [comment removed for export] *)
Lemma doe_check_sound doe : doe_check doe = true ->
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 in
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100) in
  let moy := (5 * doy + 2) / 153 in
  let m := if moy <? 10 then moy + 3 else moy - 9 in
  let y1 := if m <=? 2 then yoe + 1 else yoe in
  let d := doy - (153 * moy + 2) / 5 + 1 in
  0 <= yoe <= 399 /\ 0 <= doy /\ 1 <= m <= 12 /\ 1 <= d <= days_in_month y1 m /\ (146036 < doe \/ y1 <= 399) /\ (doe <= 146036 \/ y1 = 400).
Proof.
  unfold doe_check. cbn zeta. intros C.
  apply andb_prop in C as [C C9]. apply andb_prop in C as [C C8]. apply andb_prop in C as [C C7]. apply andb_prop in C as [C C6]. apply andb_prop in C as [C C5].
  apply andb_prop in C as [C C4]. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2. apply Z.leb_le in C3. apply Z.leb_le in C4. apply Z.leb_le in C5. apply Z.leb_le in C6. apply Z.leb_le in C7.
  apply orb_true_iff in C8. apply orb_true_iff in C9.
  repeat split; try assumption;
    first [ destruct C8 as [K|K]; [left; apply Z.ltb_lt in K; exact K| right; apply Z.leb_le in K; exact K]
          | destruct C9 as [K|K]; [left; apply Z.leb_le in K; exact K| right; apply Z.eqb_eq in K; exact K] ].
Qed.

Lemma date_of_daynum_valid dn : -60 <= dn <= 3652364 ->
  let '(y, m, d) := date_of_daynum dn in 0 <= y <= 9999 /\ 1 <= m <= 12 /\ 1 <= d <= days_in_month y m.
Proof.
  intros Hdn. unfold date_of_daynum.
  set (era := dn / 146097). set (doe := dn - era * 146097).
  assert (Hera : -1 <= era <= 24).
  { subst era. split; [apply Z.div_le_lower_bound; lia| assert (dn / 146097 < 25) by (apply Z.div_lt_upper_bound; lia); lia]. }
  assert (Hdoe : 0 <= doe < 146097) by (subst doe era; pose proof (Z.div_mod dn 146097 ltac:(lia)); pose proof (Z.mod_pos_bound dn 146097 ltac:(lia)); lia).
  assert (Hlast : era = 24 -> doe <= 146036) by (intros E; subst doe; rewrite E; lia).
  assert (Hfirst : era = -1 -> 146036 < doe) by (intros E; subst doe; rewrite E; lia).
  pose proof (doe_check_sound doe (doe_check_ok doe Hdoe)) as C. cbn zeta in C.
  set (yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365) in *.
  set (doy := doe - (365 * yoe + yoe / 4 - yoe / 100)) in *.
  set (moy := (5 * doy + 2) / 153) in *.
  set (m := if moy <? 10 then moy + 3 else moy - 9) in *.
  set (d := doy - (153 * moy + 2) / 5 + 1) in *.
  destruct C as (C1 & C2 & C3 & C4 & C5 & C6).
  assert (E400 : forall k, days_in_month (k + era * 400) m = days_in_month k m) by (intros k; apply days_in_month_add400).
  assert (Hy : 0 <= (if m <=? 2 then yoe + 1 else yoe) + era * 400 <= 9999).
  { assert (era = -1 \/ (0 <= era <= 23) \/ era = 24) as [E|[E|E]] by lia.
    - destruct C6 as [K|K]; [specialize (Hfirst E); lia|]. rewrite K, E. lia.
    - destruct (m <=? 2); lia.
    - destruct C5 as [K|K]; [specialize (Hlast E); lia| destruct (m <=? 2); lia]. }
  destruct (m <=? 2).
  - replace (yoe + era * 400 + 1) with ((yoe + 1) + era * 400) by lia. rewrite E400. lia.
  - rewrite E400. lia.
Qed.

(* [comment removed for export] *)
Lemma quot_nonneg a b : 0 <= a -> 0 < b -> Z.quot a b = a / b.
Proof. intros. apply Z.quot_div_nonneg; lia. Qed.
Lemma rem_nonneg a b : 0 <= a -> 0 < b -> Z.rem a b = a mod b.
Proof. intros. apply Z.rem_mod_nonneg; lia. Qed.

(* [comment removed for export] *)
Lemma daysecs_floor t :
  (let days := Z.quot t SECS_PER_DAY in let secs := Z.rem t SECS_PER_DAY in
   if secs <? 0 then (days - 1, secs + SECS_PER_DAY) else (days, secs)) = (t / SECS_PER_DAY, t mod SECS_PER_DAY).
Proof.
  cbn zeta. unfold SECS_PER_DAY.
  pose proof (Z.quot_rem' t 86400) as QR. pose proof (Z.div_mod t 86400 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound t 86400 ltac:(lia)) as MB.
  pose proof (Z.rem_bound_abs t 86400 ltac:(lia)) as RB.
  destruct (Z.ltb_spec (Z.rem t 86400) 0) as [N|P].
  - assert (t / 86400 = Z.quot t 86400 - 1) by nia. f_equal; lia.
  - assert (t / 86400 = Z.quot t 86400) by nia. f_equal; lia.
Qed.

Theorem utc_from_posix_valid t tm : utc_from_posix t = Some tm -> tm_valid tm.
Proof.
  unfold utc_from_posix. destruct ((t <? MIN_POSIX_TIME) || (MAX_POSIX_TIME <? t)) eqn:R; [discriminate|].
  apply orb_false_iff in R as [R1 R2]. apply Z.ltb_ge in R1. apply Z.ltb_ge in R2. unfold MIN_POSIX_TIME, MAX_POSIX_TIME in R1, R2.
  rewrite daysecs_floor. unfold SECS_PER_DAY, SECS_PER_HOUR.
  set (days := t / 86400). set (secs := t mod 86400).
  assert (Hd : -719528 <= days <= 2932896) by (subst days; split; [apply Z.div_le_lower_bound; lia| assert (t / 86400 < 2932897) by (apply Z.div_lt_upper_bound; lia); lia]).
  assert (Hs : 0 <= secs < 86400) by (subst secs; apply Z.mod_pos_bound; lia).
  set (dn := days + 719468).
  assert (Hdn : -60 <= dn <= 3652364) by (subst dn; lia).
  replace (Z.quot (if 0 <? dn then dn else dn - 146096) 146097) with (dn / 146097).
  2: { destruct (Z.ltb_spec 0 dn) as [P|NP]; [rewrite quot_nonneg by lia; reflexivity|].
       destruct (Z.eq_dec dn 0) as [E|NE]; [rewrite E; reflexivity|].
       (* [comment removed for export] *)
       rewrite <- (Z.div_unique dn 146097 (-1) (dn + 146097)) by lia.
       rewrite <- (Z.opp_involutive (dn - 146096)), Z.quot_opp_l by lia.
       rewrite <- (Z.quot_unique (- (dn - 146096)) 146097 1 (- (dn - 146096) - 146097)) by lia. reflexivity. }
  set (era := dn / 146097). set (doe := dn - era * 146097).
  assert (Hera : -1 <= era <= 24) by (subst era; split; [apply Z.div_le_lower_bound; lia| assert (dn / 146097 < 25) by (apply Z.div_lt_upper_bound; lia); lia]).
  assert (Hdoe : 0 <= doe < 146097) by (subst doe era; pose proof (Z.div_mod dn 146097 ltac:(lia)); pose proof (Z.mod_pos_bound dn 146097 ltac:(lia)); lia).
  rewrite !(quot_nonneg doe) by lia.
  assert (Hy0 : 0 <= doe - doe / 1460 + doe / 36524 - doe / 146096).
  { pose proof (Z.mul_div_le doe 1460 ltac:(lia)). pose proof (Z.mul_div_le doe 146096 ltac:(lia)).
    pose proof (Z.div_pos doe 36524 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos doe 146096 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos doe 1460 ltac:(lia) ltac:(lia)). lia. }
  rewrite (quot_nonneg (doe - _ + _ - _)) by lia.
  set (yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365).
  pose proof (date_of_daynum_valid dn Hdn) as DV. unfold date_of_daynum in DV. fold era in DV. fold doe in DV. fold yoe in DV.
  pose proof (doe_check_sound doe (doe_check_ok doe Hdoe)) as C. cbn zeta in C. fold yoe in C. destruct C as (C1 & C2 & _).
  rewrite !(quot_nonneg yoe) by lia.
  set (doy := doe - (365 * yoe + yoe / 4 - yoe / 100)) in *.
  rewrite (quot_nonneg (5 * doy + 2)) by lia.
  set (moy := (5 * doy + 2) / 153) in *.
  assert (Hmoy : 0 <= moy) by (subst moy; apply Z.div_pos; lia).
  rewrite (quot_nonneg (153 * moy + 2)) by lia.
  rewrite !(quot_nonneg secs), !(rem_nonneg secs) by lia.
  pose proof (Z.mod_pos_bound secs 3600 ltac:(lia)) as M1.
  rewrite (quot_nonneg (secs mod 3600)), (rem_nonneg (secs mod 3600)) by lia.
  intros E. injection E as <-. unfold tm_valid. cbn [t_year t_mon t_mday t_hour t_min t_sec].
  destruct DV as (V1 & V2 & V3).
  split; [exact V1|]. split; [exact V2|]. split; [exact V3|].
  assert (secs / 3600 < 24) by (apply Z.div_lt_upper_bound; lia).
  split; [split; [apply Z.div_pos; lia| lia]|].
  pose proof (Z.mod_pos_bound (secs mod 3600) 60 ltac:(lia)).
  assert (secs mod 3600 / 60 < 60) by (apply Z.div_lt_upper_bound; lia).
  split; [split; [apply Z.div_pos; lia| lia]| lia].
Qed.

Corollary gentime_adj_valid ts tm : gentime_adj ts = Some tm -> tm_valid tm.
Proof.
  unfold gentime_adj. destruct ((ts_day ts =? 0) && (ts_sec ts =? 0)).
  - intros E. injection E as <-. unfold tm_valid, epoch_tm. cbn. lia.
  - apply utc_from_posix_valid.
Qed.

(* [comment removed for export] *)
Lemma digit_range k : 0 <= k <= 9 -> 48 <= digit k <= 57.
Proof. unfold digit, CH_0. lia. Qed.
