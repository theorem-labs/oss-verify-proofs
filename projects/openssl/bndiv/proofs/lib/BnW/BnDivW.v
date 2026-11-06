(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.definitions.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnDivWords.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition dwQ (h l d : Z) : Z := (h * 4294967296 + l / 4294967296) / d.
Definition dwR (h l d : Z) : Z := h * 18446744073709551616 + l - dwQ h l d * d * 4294967296.
Definition dwH2 (h l d : Z) : Z :=
  (dwR h l d / 18446744073709551616 * 4294967296) mod 18446744073709551616 + (dwR h l d mod 18446744073709551616) / 4294967296.
Definition dwL2 (h l d : Z) : Z :=
  ((dwR h l d mod 18446744073709551616) mod 4294967296 * 4294967296) mod 18446744073709551616.

Lemma shr32 : forall x, Z.shiftr x 32 = x / 4294967296.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shl32 : forall x, Z.shiftl x 32 = x * 4294967296.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lor_hi_lo : forall t l, 0 <= l < 18446744073709551616 ->
  Z.lor ((Z.shiftl t 32) mod 18446744073709551616) (Z.shiftr l 32) = (t * 4294967296) mod 18446744073709551616 + l / 4294967296.
Proof.
  intros t l Hl. rewrite shl32, shr32. apply (lor_disjoint _ _ 32); [lia| |].
  - change (2 ^ 32) with 4294967296. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
  - change (2 ^ 32) with 4294967296. change 18446744073709551616 with (4294967296 * 4294967296).
    rewrite Z.mul_mod_distr_r by lia. apply Z.mod_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma dw_split : forall d, 9223372036854775808 <= d < 18446744073709551616 ->
  d = Z.shiftr d 32 * 4294967296 + d mod 4294967296 /\
  2147483648 <= Z.shiftr d 32 < 4294967296 /\ 0 <= d mod 4294967296 < 4294967296.
Proof. intros d Hd. rewrite shr32. Z.div_mod_to_equations. lia. Qed.

Section Round.
Variables h l d dh dl : Z.
Hypothesis Hd : d = dh * 4294967296 + dl.
Hypothesis Hdh : 2147483648 <= dh < 4294967296.
Hypothesis Hdl : 0 <= dl < 4294967296.
Hypothesis Hh : 0 <= h < d.
Hypothesis Hl : 0 <= l < 18446744073709551616.

Local Lemma Hdh' : 2 ^ 31 <= dh < HW. Proof. unfold HW. lia. Qed.

Notation Q := (dwQ h l d).
Notation U := (h * 4294967296 + l / 4294967296).

Lemma dwm_U : 0 <= U /\ U < d * 4294967296 /\ 0 < d < 18446744073709551616 /\ Q * d <= U < Q * d + d.
Proof using All.
  pose proof (dw_U_bounds h l d dh dl Hd Hdh' Hdl Hh Hl) as (U0 & U1 & _). unfold HW in U0, U1.
  split; [exact U0|]. split; [exact U1|]. split; [lia|]. unfold dwQ.
  pose proof (Z.div_mod U d ltac:(lia)). pose proof (Z.mod_pos_bound U d ltac:(lia)). lia.
Qed.

Lemma dwm_Q_range : 0 <= Q < 4294967296 /\ 0 <= Q * dh <= h /\ 0 <= Q * dl < 18446744073709551616.
Proof using All.
  pose proof (dw_U_bounds h l d dh dl Hd Hdh' Hdl Hh Hl) as (U0 & U1 & U2). unfold HW in U0, U1, U2.
  pose proof dwm_U as (_ & _ & Hdd & HQ). fold Q in U2.
  pose proof (dw_l_hi h l Hl) as LH. unfold HW in LH.
  set (q := Q) in *.
  split; [exact U2|]. split.
  - split; [apply Z.mul_nonneg_nonneg; lia|].
    assert (0 <= q * dl) by (apply Z.mul_nonneg_nonneg; lia).
    assert (q * d = q * dh * 4294967296 + q * dl) by (rewrite Hd; ring).
    assert (Hx : q * dh * 4294967296 < (h + 1) * 4294967296) by lia.
    apply Z.mul_lt_mono_pos_r in Hx; lia.
  - apply (mul_lt_BW q dl); unfold HW; lia.
Qed.

(* [comment removed for export] *)
Lemma dwm_q0 : forall q0, (Z.shiftr h 32 = dh -> q0 = 4294967295) -> (Z.shiftr h 32 <> dh -> q0 = h / dh) ->
  Q <= q0 < 4294967296 /\ 0 <= q0 * dh <= h /\ 0 <= q0 * dl < 18446744073709551616.
Proof using All.
  intros q0 E1 E2. pose proof (dw_q0 h l d dh dl Hd Hdh' Hdl Hh Hl) as X. cbv zeta in X.
  rewrite shr32 in E1, E2.
  assert (Eq : (if h / HW =? dh then HW - 1 else h / dh) = q0).
  { unfold HW. destruct (Z.eqb_spec (h / 4294967296) dh) as [E|E]; [rewrite (E1 E); reflexivity | symmetry; exact (E2 E)]. }
  rewrite Eq in X. destruct X as ((X1 & X2) & X3 & X4 & X5). unfold HW in X1, X2. unfold mulw in X4, X5.
  pose proof (Z.mod_pos_bound (q0 * dh) BW BW_pos) as B1. rewrite X4 in B1.
  pose proof (Z.mod_pos_bound (dl * q0) BW BW_pos) as B2. rewrite X5 in B2. unfold BW in B1, B2.
  unfold dwQ. lia.
Qed.

(* [comment removed for export] *)
Lemma dwm_test : forall q, 0 <= q < 4294967296 -> 0 <= q * dh <= h ->
  (Z.shiftr (h - q * dh) 32 <> 0 \/
   q * dl <= Z.lor ((Z.shiftl (h - q * dh) 32) mod 18446744073709551616) (Z.shiftr l 32)) <-> q * d <= U.
Proof using All.
  intros q Hq Hqh. pose proof (dw_exit_iff h l d dh dl Hd Hdh' Hdl Hh Hl q Hq ltac:(lia)) as X. unfold HW, BW in X.
  rewrite lor_hi_lo by exact Hl. rewrite shr32. rewrite <- X.
  destruct (Z.eqb_spec ((h - q * dh) / 4294967296) 0) as [E|E]; cbn [negb orb].
  - rewrite Z.leb_le. split; [intros [H|H]; [contradiction|exact H] | intros H; right; exact H].
  - split; [reflexivity | intros _; left; exact E].
Qed.

Lemma dwm_exit_hi : forall q, Q <= q < 4294967296 -> 0 <= q * dh <= h -> Z.shiftr (h - q * dh) 32 <> 0 -> q = Q.
Proof using All.
  intros q Hq Hqh T. pose proof dwm_U as (U0 & U1 & Hdd & HQ). pose proof dwm_Q_range as (RQ & _).
  assert (X : q * d <= U) by (apply (dwm_test q); [lia | exact Hqh | left; exact T]).
  assert (q <= Q) by (unfold dwQ; apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma dwm_exit_lo : forall q, Q <= q < 4294967296 -> 0 <= q * dh <= h ->
  q * dl <= Z.lor ((Z.shiftl (h - q * dh) 32) mod 18446744073709551616) (Z.shiftr l 32) -> q = Q.
Proof using All.
  intros q Hq Hqh T. pose proof dwm_U as (U0 & U1 & Hdd & HQ). pose proof dwm_Q_range as (RQ & _).
  assert (X : q * d <= U) by (apply (dwm_test q); [lia | exact Hqh | right; exact T]).
  assert (q <= Q) by (unfold dwQ; apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma dwm_cont : forall q, Q <= q < 4294967296 -> 0 <= q * dh <= h -> Z.shiftr (h - q * dh) 32 = 0 ->
  Z.lor ((Z.shiftl (h - q * dh) 32) mod 18446744073709551616) (Z.shiftr l 32) < q * dl ->
  Q <= q - 1 /\ 1 <= q /\ dh <= q * dh /\ dl <= q * dl.
Proof using All.
  intros q Hq Hqh T1 T2. pose proof dwm_U as (U0 & U1 & Hdd & HQ). pose proof dwm_Q_range as (RQ & _).
  assert (X : ~ q * d <= U).
  { intros X. apply (dwm_test q) in X; [|lia|exact Hqh]. destruct X as [X|X]; [contradiction|lia]. }
  assert (Hlt : Q < q).
  { destruct (Z.lt_ge_cases Q q) as [|Hge]; [assumption|exfalso]. assert (q = Q) by lia. subst q. lia. }
  split; [lia|]. split; [lia|]. split.
  - replace (q * dh) with (dh + (q - 1) * dh) by ring. assert (0 <= (q - 1) * dh) by (apply Z.mul_nonneg_nonneg; lia). lia.
  - replace (q * dl) with (dl + (q - 1) * dl) by ring. assert (0 <= (q - 1) * dl) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma dwm_tail :
  let tl2 := (Z.shiftl (Q * dl) 32) mod 18446744073709551616 in
  let th2 := Z.shiftr (Q * dl) 32 + Q * dh + Z.b2z (l <? tl2) in
  0 <= th2 <= h /\ h - th2 = dwR h l d / 18446744073709551616 /\
  (l - tl2) mod 18446744073709551616 = dwR h l d mod 18446744073709551616 /\
  0 <= dwR h l d < d * 4294967296.
Proof using All.
  cbv zeta. rewrite shl32, shr32.
  pose proof dwm_U as (U0 & U1 & Hdd & HQ). pose proof dwm_Q_range as (RQ & RQh & RQl).
  pose proof (dw_l_hi h l Hl) as LH. unfold HW in LH.
  unfold dwR. set (q := Q) in *.
  set (t := q * dl / 4294967296).
  assert (Etl : (q * dl * 4294967296) mod 18446744073709551616 = (q * dl) mod 4294967296 * 4294967296).
  { change 18446744073709551616 with (4294967296 * 4294967296). apply Z.mul_mod_distr_r; lia. }
  rewrite Etl. set (tl2 := (q * dl) mod 4294967296 * 4294967296).
  pose proof (Z.div_mod (q * dl) 4294967296 ltac:(lia)) as Edm. fold t in Edm.
  pose proof (Z.mod_pos_bound (q * dl) 4294967296 ltac:(lia)) as Hmb.
  assert (Ht : 0 <= t) by (subst t; apply Z.div_pos; lia).
  assert (Eqd : q * d = q * dh * 4294967296 + q * dl) by (rewrite Hd; ring).
  assert (EP : q * d * 4294967296 = (q * dh + t) * 18446744073709551616 + tl2) by (subst tl2; lia).
  pose proof (Z.div_mod l 4294967296 ltac:(lia)) as Eldm.
  pose proof (Z.mod_pos_bound l 4294967296 ltac:(lia)) as Hlmb.
  assert (HN : q * d * 4294967296 <= h * 18446744073709551616 + l) by lia.
  assert (HR : 0 <= h * 18446744073709551616 + l - q * d * 4294967296 < d * 4294967296) by lia.
  assert (Htl2 : 0 <= tl2 < 18446744073709551616) by (subst tl2; lia).
  assert (Hth2 : q * dh + t <= h) by lia.
  destruct (Z.ltb_spec l tl2) as [Hlt|Hge]; cbn [Z.b2z].
  - assert (Hth3 : q * dh + t + 1 <= h) by lia.
    assert (ER : h * 18446744073709551616 + l - q * d * 4294967296
                 = 18446744073709551616 * (h - (t + q * dh + 1)) + (l - tl2 + 18446744073709551616)) by lia.
    split; [lia|]. split; [|split].
    + apply (Z.div_unique _ _ _ (l - tl2 + 18446744073709551616)); [left; lia | exact ER].
    + rewrite ER. rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia.
      rewrite <- (Z.mod_add (l - tl2) 1) by lia. f_equal; lia.
    + exact HR.
  - assert (ER : h * 18446744073709551616 + l - q * d * 4294967296
                 = 18446744073709551616 * (h - (t + q * dh + 0)) + (l - tl2)) by lia.
    split; [lia|]. split; [|split].
    + apply (Z.div_unique _ _ _ (l - tl2)); [left; lia | exact ER].
    + rewrite ER. rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. reflexivity.
    + exact HR.
Qed.

(* [comment removed for export] *)
Lemma dwm_next :
  let tl2 := (Z.shiftl (Q * dl) 32) mod 18446744073709551616 in
  let th2 := Z.shiftr (Q * dl) 32 + Q * dh + Z.b2z (l <? tl2) in
  Z.lor ((Z.shiftl ((bv_swrap 32 (h - th2) + Z.land 0 d) mod 18446744073709551616) 32) mod 18446744073709551616)
        (Z.shiftr ((l - tl2) mod 18446744073709551616) 32) = dwH2 h l d /\
  (Z.shiftl l 32) mod 18446744073709551616 = dwL2 h l d /\
  0 <= dwH2 h l d < d /\ 0 <= dwL2 h l d < 18446744073709551616.
Proof using All.
  pose proof dwm_tail as T. cbv zeta in *. destruct T as (T1 & T2 & T3 & T4).
  pose proof dwm_U as (U0 & U1 & Hdd & HQ).
  unfold dwH2, dwL2. set (R := dwR h l d) in *.
  set (tl2 := (Z.shiftl (Q * dl) 32) mod 18446744073709551616) in *.
  set (th2 := Z.shiftr (Q * dl) 32 + Q * dh + Z.b2z (l <? tl2)) in *.
  rewrite T2, T3. set (h1 := R / 18446744073709551616). set (l1 := R mod 18446744073709551616).
  assert (Hh1 : 0 <= h1 < 4294967296).
  { subst h1. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  assert (Hl1 : 0 <= l1 < 18446744073709551616) by (subst l1; apply Z.mod_pos_bound; lia).
  assert (ER : R = 18446744073709551616 * h1 + l1) by (subst h1 l1; apply Z.div_mod; lia).
  assert (Eh : (Z.shiftl ((bv_swrap 32 h1 + Z.land 0 d) mod 18446744073709551616) 32) mod 18446744073709551616
               = h1 * 4294967296).
  { rewrite Z.land_0_l, shl32. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
    clear - Hh1. Z.div_mod_to_equations. lia. }
  rewrite Eh. rewrite (Z.mod_small (h1 * 4294967296)) by lia. rewrite !shr32, shl32.
  assert (Hl1h : 0 <= l1 / 4294967296 < 4294967296).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  split.
  { apply (lor_disjoint _ _ 32); [lia | exact Hl1h | apply Z.mod_mul; lia]. }
  (* [comment removed for export] *)
  assert (Etl : tl2 = (Q * dl) mod 4294967296 * 4294967296).
  { subst tl2. rewrite shl32. change 18446744073709551616 with (4294967296 * 4294967296). apply Z.mul_mod_distr_r; lia. }
  assert (El : l1 mod 4294967296 = l mod 4294967296).
  { subst l1. rewrite <- T3. rewrite Etl. clear. Z.div_mod_to_equations. lia. }
  rewrite El.
  pose proof (Z.mod_pos_bound l 4294967296 ltac:(lia)) as Hlm.
  pose proof (Z.div_mod l1 4294967296 ltac:(lia)) as El1. pose proof (Z.mod_pos_bound l1 4294967296 ltac:(lia)) as Hl1m.
  split.
  { rewrite (Z.mod_small (l mod 4294967296 * 4294967296)) by lia.
    change 18446744073709551616 with (4294967296 * 4294967296). apply Z.mul_mod_distr_r; lia. }
  split; [|apply Z.mod_pos_bound; lia].
  lia.
Qed.
End Round.

(* [comment removed for export] *)
Lemma div_words_rounds : forall h l d,
  9223372036854775808 <= d < 18446744073709551616 -> 0 <= h < d -> 0 <= l < 18446744073709551616 ->
  div_words h l d = Z.lor (dwQ (dwH2 h l d) (dwL2 h l d) d) ((Z.shiftl (dwQ h l d) 32) mod 18446744073709551616).
Proof.
  intros h l d Hd Hh Hl.
  assert (Hd' : 2 ^ 63 <= d < BW) by (unfold BW; lia).
  unfold div_words. destruct (Z.eqb_spec d 0) as [E|_]; [lia|].
  rewrite (num_bits_word_norm d Hd'). change (64 - 64) with 0. rewrite Z.eqb_refl.
  destruct (Z.leb_spec d h) as [Hle|_]; [lia|].
  set (dh := d / HW). set (dl := d mod HW).
  assert (Ed : d = dh * 4294967296 + dl) by (subst dh dl; unfold HW; pose proof (Z.div_mod d 4294967296 ltac:(lia)); lia).
  assert (Hdl : 0 <= dl < 4294967296) by (subst dl; unfold HW; apply Z.mod_pos_bound; lia).
  assert (Hdh : 2147483648 <= dh < 4294967296).
  { subst dh. unfold HW. split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (Hdh' : 2 ^ 31 <= dh < HW) by (unfold HW; lia).
  pose proof (dw_round_spec h l d dh dl Ed Hdh' Hdl Hh Hl) as H1. cbv zeta in H1. destruct H1 as (E1 & HR1 & Hq1).
  rewrite E1.
  pose proof (dwm_next h l d dh dl Ed Hdh Hdl Hh Hl) as N. cbv zeta in N. destruct N as (_ & _ & Hh2 & Hl2).
  change (dw_round _ _ d dh dl) with (dw_round (dwH2 h l d) (dwL2 h l d) d dh dl).
  pose proof (dw_round_spec (dwH2 h l d) (dwL2 h l d) d dh dl Ed Hdh' Hdl Hh2 Hl2) as H2. cbv zeta in H2.
  destruct H2 as (E2 & _ & _). rewrite E2.
  rewrite Z.lor_comm, shl32. reflexivity.
Qed.
