(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import Prog ZIface InflateState Inftrees ModelRel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ItCovBits ItCovPre ItCovMath ItCovStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma land_pow2m1 : forall h r, 0 <= r -> Z.land h (2 ^ r - 1) = h mod 2 ^ r.
Proof. intros h r Hr. rewrite <- (Z.land_ones h r) by exact Hr. f_equal. unfold Z.ones. rewrite Z.shiftl_1_l. lia. Qed.

Lemma it_huff_next_eq' : forall huff len, 1 <= len <= 16 ->
  (if negb (it_incr_back huff len =? 0) then Z.land huff (it_incr_back huff len - 1) + it_incr_back huff len else 0)
  = it_rev_incr huff len.
Proof. intros. apply it_huff_next_eq. assumption. Qed.

Lemma andb_true_l : forall b, true && b = b.  Proof. reflexivity. Qed.
Lemma andb_false_l : forall b, false && b = false.  Proof. reflexivity. Qed.

Section Loop.
  Variables (ty : codetype) (lens : arr) (lens_ofs codes : Z).
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall s, 0 <= s < codes -> 0 <= arr_get lens (lens_ofs + s) <= 15.
  Local Notation Nn := (N lens lens_ofs codes).
  Local Notation Wl := (W lens lens_ofs codes).
  Local Notation mx := (max lens lens_ofs codes).
  Local Notation mn := (min lens lens_ofs codes).
  Local Notation Lg := (Lf lens lens_ofs codes).
  Hypothesis Hmax : 1 <= mx.
  Hypothesis Hcomplete : kraft lens lens_ofs codes 15 = 2 ^ 15.
  Variable root : Z.
  Hypothesis Hroot : mn <= root <= 15.
  Variable table : Z.
  Hypothesis Htable : 0 <= table.

  Lemma CN : 1 <= Nn.  Proof. apply (N_pos lens lens_ofs codes Hcodes Hlens Hmax). Qed.
  Lemma CL : forall i, 0 <= i < Nn -> 1 <= Lg i <= 15.  Proof. apply (Lf_range lens lens_ofs codes Hcodes). Qed.
  Lemma CS : forall i j, 0 <= i <= j -> j < Nn -> Lg i <= Lg j.  Proof. apply (Lf_sorted lens lens_ofs codes Hcodes). Qed.
  Lemma CR : 1 <= root <= 15.
  Proof. destruct (min_spec lens lens_ofs codes Hcodes Hlens Hmax) as (A & _). lia. Qed.
  Lemma CRm : Lg 0 <= root.
  Proof. rewrite (Lf_first lens lens_ofs codes Hcodes Hlens Hmax). lia. Qed.
  Lemma CC : SK Lg Nn = 2 ^ 15.
  Proof. rewrite (SK_kraft lens lens_ofs codes Hcodes). exact Hcomplete. Qed.

  Local Notation mC := (m Nn Lg root).
  Local Notation hfj := (hf Lg).
  Local Notation remj := (remf Nn Lg).
  Local Notation ppj := (pp Lg root).
  Local Notation Dj := (D Lg root).
  Local Notation isblk := (is_block Nn Lg root).
  Local Notation kpq := (kp Nn Lg root).
  Local Notation Dq := (Dp Nn Lg root).
  Local Notation SBq := (SB Nn Lg root).
  Local Notation Bq := (B root).

  Local Ltac canon := first [exact CN | exact CL | exact CS | exact CR | exact CRm | exact CC].
  Lemma Lm : 1 <= mC <= Nn /\ (forall i, 0 <= i < mC -> Lg i <= root) /\ (forall i, mC <= i < Nn -> root < Lg i).
  Proof. apply m_spec; canon. Qed.
  Lemma Lhf_range : forall i, 0 <= i < Nn -> 0 <= hfj i < 2 ^ Lg i.
  Proof. intros. apply (hf_range Nn); try canon. assumption. Qed.
  Lemma Lhf_succ : forall i, 0 <= i -> i + 1 < Nn -> it_rev_incr (hfj i) (Lg i) = hfj (i + 1).
  Proof. intros. apply (hf_succ Nn); try canon; assumption. Qed.
  Lemma Lhf_last : it_rev_incr (hfj (Nn - 1)) (Lg (Nn - 1)) = 0.
  Proof. apply (hf_last Nn); canon. Qed.
  Lemma Lhf_low : forall j, mC <= j < Nn -> hfj j mod 2 ^ root = brv (Z.to_nat root) (ppj j).
  Proof. intros. apply (hf_low Nn); try canon. assumption. Qed.
  Lemma Lpp_m : SK Lg mC = ppj mC * Bq.
  Proof. apply (pp_m Nn); canon. Qed.
  Lemma Lpp_mono : forall i j, 0 <= i <= j -> ppj i <= ppj j.
  Proof. intros. apply pp_mono; try canon. assumption. Qed.
  Lemma Lpp_range : forall j, mC <= j < Nn -> ppj mC <= ppj j < 2 ^ root.
  Proof. intros. apply (pp_range Nn); try canon. assumption. Qed.
  Lemma Lpp_step : forall j, mC <= j -> j + 1 < Nn ->
    (ppj (j + 1) = ppj j /\ SK Lg (j + 1) < (ppj j + 1) * Bq) \/ (ppj (j + 1) = ppj j + 1 /\ SK Lg (j + 1) = (ppj j + 1) * Bq).
  Proof. intros. apply (pp_step Nn); try canon; assumption. Qed.
  Lemma Lpp_last : mC < Nn -> ppj (Nn - 1) = 2 ^ root - 1.
  Proof. intros. apply (pp_last Nn); try canon; assumption. Qed.
  Lemma Lkp_spec : forall p, mC <= kpq p <= Nn /\ (forall k, mC <= k < kpq p -> ppj k < p) /\ (forall k, kpq p <= k < Nn -> p <= ppj k).
  Proof. intros. apply kp_spec; canon. Qed.
  Lemma Lkp_block : forall p, ppj mC <= p < 2 ^ root -> mC < Nn -> isblk (kpq p) (kpq (p + 1)).
  Proof. intros. apply kp_block; try canon; assumption. Qed.
  Lemma Lkp_of_pp : forall j, mC <= j < Nn -> kpq (ppj j) <= j < kpq (ppj j + 1).
  Proof. intros. apply kp_of_pp; try canon; assumption. Qed.
  Lemma LDp_range : forall p, ppj mC <= p < 2 ^ root -> mC < Nn -> 1 <= Dq p <= 15 - root.
  Proof. intros. apply Dp_range; try canon; assumption. Qed.
  Lemma LSB_first : SBq (ppj mC) = 0.
  Proof. apply SB_first. Qed.
  Lemma LSB_step : forall p, ppj mC <= p -> SBq (p + 1) = SBq p + 2 ^ Dq p.
  Proof. intros. apply SB_step. assumption. Qed.
  Lemma LSB_nonneg : forall p, 0 <= SBq p.
  Proof. intros. apply SB_nonneg. Qed.
  Lemma LSB_bound : forall p, ppj mC <= p <= 2 ^ root -> mC < Nn -> SBq p <= (p - ppj mC) * Bq.
  Proof. intros. apply SB_bound; try canon; assumption. Qed.
  Lemma Ldsub_range : forall a e k, isblk a e -> a <= k < e -> 1 <= Lg k - root <= Dj e.
  Proof. intros. apply (dsub_range Nn Lg root CN CS CRm a e H k H0). Qed.
  Lemma Lsubsz : forall a e count, isblk a e -> (forall l, 1 <= l <= 15 -> arr_get count l = remj a l) ->
    it_subtable_curr count (Lg a) root mx = Dj e.
  Proof.
    intros. eapply (subsz_spec Nn Lg root); try canon; try eassumption.
    symmetry. apply (Lf_last lens lens_ofs codes Hcodes Hlens Hmax).
  Qed.
  Lemma Lremf_step : forall a l, 0 <= a < Nn -> remj (a + 1) l = remj a l - (if Lg a =? l then 1 else 0).
  Proof. intros. apply remf_step. assumption. Qed.
  Lemma Lremf_pos_self : forall a, 0 <= a < Nn -> 1 <= remj a (Lg a).
  Proof. intros. apply remf_pos_self; assumption. Qed.
  Lemma Lremf_zero_next : forall a, 0 <= a -> a + 1 < Nn -> remj (a + 1) (Lg a) = 0 -> Lg a < Lg (a + 1).
  Proof. intros. apply (remf_zero_next Nn Lg CS); assumption. Qed.
  Lemma Lremf_pos_next : forall a, 0 <= a -> a + 1 < Nn -> remj (a + 1) (Lg a) <> 0 -> Lg (a + 1) = Lg a.
  Proof. intros. apply (remf_pos_next Nn Lg CS); assumption. Qed.
  Lemma Lremf_N : forall l, remj Nn l = 0.
  Proof. intros. apply remf_N. Qed.
  Lemma Lremf_bound : forall a l, 0 <= a <= Nn -> 0 <= remj a l <= 288.
  Proof.
    intros. pose proof (remf_nonneg Nn Lg a l). pose proof (remf_le Nn Lg a l H).
    pose proof (N_range lens lens_ofs codes Hcodes Hlens). lia.
  Qed.
  Lemma LLast : Lg (Nn - 1) = mx.
  Proof. apply (Lf_last lens lens_ofs codes Hcodes Hlens Hmax). Qed.
  Lemma LWr : forall i, 0 <= i < Nn -> 0 <= znth 0 Wl i < codes.
  Proof. intros. apply (W_range lens lens_ofs codes Hcodes). assumption. Qed.
  Lemma LNn : Nn <= codes.
  Proof. pose proof (N_range lens lens_ofs codes Hcodes Hlens). lia. Qed.
  Lemma Lpp0 : 0 <= ppj mC.
  Proof.
    pose proof Lpp_m as E. pose proof (B_pos root CR) as BP. pose proof Lm as (Lm1 & _ & _).
    pose proof (S_nonneg Lg mC ltac:(lia)). nia.
  Qed.
  Lemma P15 : 2 ^ root <= 2 ^ 15.
  Proof. apply Z.pow_le_mono_r; [lia|]. pose proof CR; lia. Qed.
  Lemma Lbrv_pp : forall j, mC <= j < Nn -> 0 <= brv (Z.to_nat root) (ppj j) < 2 ^ root.
  Proof.
    intros j Hj. pose proof (brv_range (Z.to_nat root) (ppj j)) as BR. rewrite Z2Nat.id in BR by (pose proof CR; lia). exact BR.
  Qed.


  Definition dr (j : Z) : Z := if j <? mC then 0 else root.
  Definition cu (j : Z) : Z := if j <? mC then root else Dq (ppj j).
  Definition nx (j : Z) : Z := if j <? mC then table else table + 2 ^ root + SBq (ppj j).
  Definition us (j : Z) : Z := if j <? mC then 2 ^ root else 2 ^ root + SBq (ppj j) + 2 ^ Dq (ppj j).
  Definition lo (j : Z) : Z := if j <? mC then 4294967295 else brv (Z.to_nat root) (ppj j).
  Definition newblk (k : Z) : bool := (mC <=? k) && ((k =? mC) || negb (ppj k =? ppj (k - 1))).
  Definition NF (k : Z) : bool := newblk k && it_not_enough ty (us k).

  Lemma newblk_eq : forall k, newblk k = (mC <=? k) && ((k =? mC) || negb (ppj k =? ppj (k - 1))).  Proof. reflexivity. Qed.
  Lemma NF_eq : forall k, NF k = newblk k && it_not_enough ty (us k).  Proof. reflexivity. Qed.

  Definition ent_op (w : Z) : Z :=
    if w + 1 <? it_match ty then 0
    else if it_match ty <=? w then
      wrap8 (match ty with CODES => 0 | LENS => arr_get lext_a (w - 257) | DISTS => arr_get dext_a w end)
    else 96.
  Definition ent_val (w : Z) : Z :=
    if w + 1 <? it_match ty then w
    else if it_match ty <=? w then
      (match ty with CODES => 0 | LENS => arr_get lbase_a (w - 257) | DISTS => arr_get dbase_a w end)
    else 0.
  Definition HV (j : Z) : Z := code_pack (ent_op (znth 0 Wl j)) (Lg j - dr j) (ent_val (znth 0 Wl j)).
  Definition LINK (k : Z) : Z := code_pack (cu k) root (nx k - table).
  Definition FILL (j : Z) (t : arr) : arr :=
    it_fill (HV j) (2 ^ (Lg j - dr j)) (hfj j) (dr j) (nx j) (2 ^ cu j) t.

  Hypothesis HtyC : ty = CODES -> codes <= 19.

  Lemma hereof_HV : forall (work : arr) j drop, 0 <= j < Nn ->
    (forall i, 0 <= i < Nn -> arr_get work i = znth 0 Wl i) ->
    (let w := arr_get work j in
     let '(here_op, here_val) :=
       if w + 1 <? it_match ty then (0, w)
       else if it_match ty <=? w then (wrap8 (it_extra ty work (w - it_match ty)), it_base ty work (w - it_match ty))
       else (96, 0) in
     code_pack here_op (Lg j - drop) here_val)
    = code_pack (ent_op (znth 0 Wl j)) (Lg j - drop) (ent_val (znth 0 Wl j)).
  Proof.
    intros work j drop Hj Hwork. cbv zeta. rewrite Hwork by exact Hj. unfold ent_op, ent_val.
    pose proof (LWr j Hj) as Wr.
    destruct ty.
    -
      pose proof (HtyC eq_refl). cbn [it_match].
      replace (znth 0 Wl j + 1 <? 20) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - cbn [it_match it_extra it_base]. destruct (znth 0 Wl j + 1 <? 257); [reflexivity|].
      destruct (257 <=? znth 0 Wl j); reflexivity.
    - cbn [it_match it_extra it_base]. destruct (znth 0 Wl j + 1 <? 0); [reflexivity|].
      destruct (0 <=? znth 0 Wl j) eqn:E; [|reflexivity]. rewrite Z.sub_0_r. reflexivity.
  Qed.

  Lemma ent_pair : forall (work : arr) j, 0 <= j < Nn ->
    (forall i, 0 <= i < Nn -> arr_get work i = znth 0 Wl i) ->
    (if arr_get work j + 1 <? it_match ty then (0, arr_get work j)
     else if it_match ty <=? arr_get work j
     then (wrap8 (it_extra ty work (arr_get work j - it_match ty)), it_base ty work (arr_get work j - it_match ty))
     else (96, 0)) = (ent_op (znth 0 Wl j), ent_val (znth 0 Wl j)).
  Proof.
    intros work j Hj Hwork. rewrite Hwork by exact Hj. unfold ent_op, ent_val.
    pose proof (LWr j Hj) as Wr.
    destruct ty.
    - pose proof (HtyC eq_refl). cbn [it_match].
      replace (znth 0 Wl j + 1 <? 20) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - cbn [it_match it_extra it_base]. destruct (znth 0 Wl j + 1 <? 257); [reflexivity|].
      destruct (257 <=? znth 0 Wl j); reflexivity.
    - cbn [it_match it_extra it_base]. destruct (znth 0 Wl j + 1 <? 0); [reflexivity|].
      destruct (0 <=? znth 0 Wl j) eqn:E; [|reflexivity]. rewrite Z.sub_0_r. reflexivity.
  Qed.


  Definition IS (j : Z) (st : ItSt) : Prop :=
    t_sym st = j /\ t_len st = Lg j /\ t_huff st = hfj j
    /\ arr_len (t_count st) = 16 /\ (forall l, 1 <= l <= 15 -> arr_get (t_count st) l = remj j l)
    /\ (forall i, 0 <= i < Nn -> arr_get (t_work st) i = znth 0 Wl i)
    /\ t_drop st = dr j /\ t_curr st = cu j /\ t_next st = nx j /\ t_used st = us j /\ t_low st = lo j
    /\ it_not_enough ty (us j) = false /\ 0 <= t_min st <= 2 ^ 15.

  Definition trip_post (j : Z) (st : ItSt) (r : ItStep) : Prop :=
    match r with
    | ItBreak st' =>
        j + 1 = Nn /\ t_tbl st' = FILL j (t_tbl st) /\ t_work st' = t_work st /\ t_huff st' = 0
        /\ t_next st' = nx j /\ t_used st' = us j /\ t_drop st' = dr j /\ t_len st' = Lg j /\ t_curr st' = cu j
    | ItCont st' =>
        j + 1 < Nn /\ NF (j + 1) = false /\ IS (j + 1) st' /\ t_work st' = t_work st
        /\ t_tbl st' = (if newblk (j + 1) then arr_set (FILL j (t_tbl st)) (table + lo (j + 1)) (LINK (j + 1))
                        else FILL j (t_tbl st))
    | ItFail st' =>
        j + 1 < Nn /\ NF (j + 1) = true /\ t_work st' = t_work st
    end.


  Lemma phase_facts : forall j, 0 <= j < Nn ->
    0 <= dr j <= root /\ 1 <= Lg j - dr j <= cu j /\ cu j <= 15 /\ table <= nx j
    /\ 2 ^ root <= us j /\ us j = nx j - table + 2 ^ cu j /\ us j <= 2 ^ root + 2 ^ 15.
  Proof.
    intros j Hj. pose proof Lm as (Lm1 & Lm2 & Lm3). pose proof CR as HR. pose proof (CL j Hj) as HL.
    pose proof (pow2_pos root ltac:(lia)) as PR.
    unfold dr, cu, nx, us. destruct (Z.ltb_spec j mC).
    - pose proof (Lm2 j ltac:(lia)). lia.
    - pose proof (Lm3 j ltac:(lia)) as L3. pose proof (Lpp_range j ltac:(lia)) as PPR.
      pose proof (Lkp_block (ppj j) ltac:(lia) ltac:(lia)) as HB. pose proof (Lkp_of_pp j ltac:(lia)) as KJ.
      pose proof (LDp_range (ppj j) ltac:(lia) ltac:(lia)) as DR.
      pose proof (Ldsub_range _ _ j HB KJ) as DS. unfold Dp in *.
      pose proof (LSB_nonneg (ppj j)) as SB0. pose proof (LSB_bound (ppj j + 1) ltac:(lia) ltac:(lia)) as SB1.
      rewrite LSB_step in SB1 by lia. unfold Dp in SB1.
      assert (E15 : 2 ^ 15 = 2 ^ root * Bq) by (unfold B; rewrite <- pow2_split by lia; f_equal; lia).
      pose proof (B_pos root CR) as BP. pose proof Lpp0.
      pose proof (pow2_pos (Dj (kpq (ppj j + 1))) ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. nia.
  Qed.

  Lemma newblk_true_facts : forall j, 0 <= j -> j + 1 < Nn -> newblk (j + 1) = true ->
    mC <= j + 1 /\ kpq (ppj (j + 1)) = j + 1
    /\ nx (j + 1) = nx j + 2 ^ cu j /\ us (j + 1) = us j + 2 ^ cu (j + 1) /\ dr (j + 1) = root
    /\ cu (j + 1) = Dq (ppj (j + 1)) /\ lo (j + 1) = brv (Z.to_nat root) (ppj (j + 1)).
  Proof.
    intros j Hj HjN Hnb. pose proof Lm as (Lm1 & Lm2 & Lm3). pose proof CR as HR.
    rewrite newblk_eq in Hnb. apply andb_prop in Hnb. destruct Hnb as [A Bb]. apply Z.leb_le in A.
    apply Bool.orb_true_iff in Bb. replace (j + 1 - 1) with j in Bb by lia.
    assert (CASE : j + 1 = mC \/ (mC <= j /\ ppj (j + 1) = ppj j + 1)).
    { destruct Bb as [Bb|Bb]; [left; apply Z.eqb_eq in Bb; exact Bb|].
      apply negb_true_iff in Bb. apply Z.eqb_neq in Bb.
      destruct (Z.eq_dec (j + 1) mC); [left; assumption | right].
      destruct (Lpp_step j ltac:(lia) HjN) as [[X _]|[X _]]; [exfalso; exact (Bb X) | split; [lia | exact X]]. }
    assert (KP : kpq (ppj (j + 1)) = j + 1).
    { unfold kp. apply findZ_unique; [lia | intros _; apply Z.leb_refl |].
      intros k Hk. apply Z.leb_gt. destruct CASE as [E|[M E]]; [lia|].
      pose proof (Lpp_mono k j ltac:(lia)). lia. }
    split; [exact A|]. split; [exact KP|].
    unfold nx, us, dr, cu, lo.
    replace (j + 1 <? mC) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct CASE as [E|[M E]].
    - replace (j <? mC) with true by (symmetry; apply Z.ltb_lt; lia). rewrite E, LSB_first.
      repeat split; lia.
    - replace (j <? mC) with false by (symmetry; apply Z.ltb_ge; lia). rewrite E.
      rewrite LSB_step by (pose proof (Lpp_range j ltac:(lia)); lia).
      repeat split; lia.
  Qed.

  Lemma newblk_false_facts : forall j, 0 <= j -> j + 1 < Nn -> newblk (j + 1) = false ->
    nx (j + 1) = nx j /\ us (j + 1) = us j /\ dr (j + 1) = dr j /\ cu (j + 1) = cu j /\ lo (j + 1) = lo j
    /\ (mC <= j + 1 -> mC <= j /\ ppj (j + 1) = ppj j).
  Proof.
    intros j Hj HjN Hnb. pose proof Lm as (Lm1 & Lm2 & Lm3).
    rewrite newblk_eq in Hnb. replace (j + 1 - 1) with j in Hnb by lia.
    destruct (Z.leb_spec mC (j + 1)) as [A|A].
    - rewrite andb_true_l in Hnb. apply Bool.orb_false_iff in Hnb. destruct Hnb as [B1 B2].
      apply Z.eqb_neq in B1. apply negb_false_iff in B2. apply Z.eqb_eq in B2.
      unfold nx, us, dr, cu, lo.
      replace (j + 1 <? mC) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (j <? mC) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite B2. repeat split; try reflexivity; try lia.
    - unfold nx, us, dr, cu, lo.
      replace (j + 1 <? mC) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (j <? mC) with true by (symmetry; apply Z.ltb_lt; lia).
      repeat split; try reflexivity; intros; lia.
  Qed.

  Lemma test_is_newblk : forall j, 0 <= j -> j + 1 < Nn ->
    (root <? Lg (j + 1)) && negb (hfj (j + 1) mod 2 ^ root =? lo j) = newblk (j + 1).
  Proof.
    intros j Hj HjN. pose proof Lm as (Lm1 & Lm2 & Lm3). pose proof CR as HR.
    rewrite newblk_eq. unfold lo. destruct (Z.ltb_spec root (Lg (j + 1))) as [L|L].
    - destruct (Z_lt_le_dec (j + 1) mC). { exfalso. pose proof (Lm2 (j + 1) ltac:(lia)). lia. }
      rewrite Lhf_low by lia. replace (mC <=? j + 1) with true by (symmetry; apply Z.leb_le; lia).
      rewrite andb_true_l. pose proof (Lbrv_pp (j + 1) ltac:(lia)) as BR1. pose proof P15.
      destruct (Z.ltb_spec j mC).
      + replace (j + 1 =? mC) with true by (symmetry; apply Z.eqb_eq; lia). cbn [orb].
        destruct (Z.eqb_spec (brv (Z.to_nat root) (ppj (j + 1))) 4294967295); [lia|reflexivity].
      + replace (j + 1 =? mC) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb].
        replace (j + 1 - 1) with j by lia. pose proof (Lpp_range j ltac:(lia)). pose proof (Lpp_range (j + 1) ltac:(lia)). pose proof Lpp0.
        destruct (Z.eqb_spec (ppj (j + 1)) (ppj j)) as [E|E].
        * rewrite E, Z.eqb_refl. reflexivity.
        * destruct (Z.eqb_spec (brv (Z.to_nat root) (ppj (j + 1))) (brv (Z.to_nat root) (ppj j))) as [E'|E']; [|reflexivity].
          exfalso. apply E. apply (brv_inj (Z.to_nat root)); try (rewrite Z2Nat.id by lia; lia). exact E'.
    - destruct (Z.leb_spec mC (j + 1)); [|reflexivity]. exfalso. pose proof (Lm3 (j + 1) ltac:(lia)). lia.
  Qed.


  Lemma trip : forall j st, 0 <= j < Nn -> IS j st -> trip_post j st (it_step (mkItCtx ty lens lens_ofs table root mx (2 ^ root - 1)) st).
  Proof.
    intros j st Hj HIS.
    pose proof Lm as (Lm1 & Lm2 & Lm3). pose proof CR as HR. pose proof (CL j Hj) as HLj.
    pose proof (phase_facts j Hj) as (Fdr & Fld & Fcu & Fnx & Fus1 & Fus2 & Fus3).
    destruct st as [huff sym len next curr drop low used mn0 count tbl work].
    unfold IS in HIS; cbn [t_sym t_len t_huff t_count t_work t_drop t_curr t_next t_used t_low t_min] in HIS.
    destruct HIS as (Hsym & Hlen & Hhuff & Hclen & Hcnt & Hwork & Hdrop & Hcurr & Hnext & Hused & Hlow & Hoku & Hmin).
    subst sym len huff drop curr next used low.
    unfold trip_post, FILL, HV. cbn [t_tbl t_work].
    rewrite <- (hereof_HV work j (dr j) Hj Hwork).
    cbv beta iota zeta delta [it_step t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work
                              x_ty x_lens x_lens_ofs x_table x_root x_max x_mask].
    rewrite it_huff_next_eq' by lia.
    rewrite (wrap32_id (j + 1)) by (pose proof LNn; lia).
    assert (Ecnt : wrap16 (arr_get count (Lg j) - 1) = remj (j + 1) (Lg j)).
    { rewrite Hcnt by lia. rewrite (Lremf_step j (Lg j)) by lia. rewrite Z.eqb_refl.
      pose proof (Lremf_pos_self j ltac:(lia)). pose proof (Lremf_bound j (Lg j) ltac:(lia)). apply wrap16_id. lia. }
    rewrite Ecnt.
    rewrite (wrap8_id (Lg j - dr j)) by lia.
    change (shl32 1 (cu j)) with (itm_used (cu j)). rewrite (itm_used_pow2 (cu j)) by lia.
    change (shl32 1 (Lg j - dr j)) with (itm_used (Lg j - dr j)). rewrite (itm_used_pow2 (Lg j - dr j)) by lia.
    destruct (if arr_get work j + 1 <? it_match ty then (0, arr_get work j)
              else if it_match ty <=? arr_get work j
              then (wrap8 (it_extra ty work (arr_get work j - it_match ty)), it_base ty work (arr_get work j - it_match ty))
              else (96, 0)) as [here_op here_val].
    set (here := code_pack here_op (Lg j - dr j) here_val). clearbody here.
    assert (Hcnt' : forall l, 1 <= l <= 15 -> arr_get (arr_set count (Lg j) (remj (j + 1) (Lg j))) l = remj (j + 1) l).
    { intros l Hl. rewrite arr_get_set. unfold arr_inb. rewrite Hclen.
      destruct (Z.eqb_spec (Lg j) l) as [<-|Hne].
      - replace ((0 <=? Lg j) && (Lg j <? 16)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia). reflexivity.
      - rewrite Hcnt by lia. rewrite (Lremf_step j l) by lia. replace (Lg j =? l) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [andb]. lia. }
    destruct (Z.eq_dec (j + 1) Nn) as [HjN|HjN].
    -
      assert (E1 : remj (j + 1) (Lg j) = 0) by (rewrite HjN; apply Lremf_N).
      assert (E2 : Lg j = mx) by (replace j with (Nn - 1) by lia; apply LLast).
      rewrite E1. rewrite <- E2, (Z.eqb_refl (Lg j)). cbn [Z.eqb andb negb].
      cbn [t_tbl t_work t_huff t_next t_used t_drop t_len t_curr].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [replace j with (Nn - 1) by lia; apply Lhf_last|].
      repeat split; reflexivity.
    -
      assert (HjN' : j + 1 < Nn) by lia.
      pose proof (CS j (j + 1) ltac:(lia) ltac:(lia)) as Hs01. pose proof (CS (j + 1) (Nn - 1) ltac:(lia) ltac:(lia)) as Hs1N.
      rewrite LLast in Hs1N. pose proof (CL (j + 1) ltac:(lia)) as HL1.
      assert (Ebrk : (remj (j + 1) (Lg j) =? 0) && (Lg j =? mx) = false).
      { destruct (Z.eqb_spec (Lg j) mx) as [E|E]; [|apply andb_false_r].
        destruct (Z.eqb_spec (remj (j + 1) (Lg j)) 0) as [E0|E0]; [|reflexivity]. exfalso.
        pose proof (Lremf_zero_next j ltac:(lia) HjN' E0). lia. }
      rewrite Ebrk.
      assert (Elen : (if (remj (j + 1) (Lg j) =? 0) && negb (Lg j =? mx) then arr_get lens (lens_ofs + arr_get work (j + 1)) else Lg j) = Lg (j + 1)).
      { destruct (Z.eqb_spec (remj (j + 1) (Lg j)) 0) as [E0|E0].
        - pose proof (Lremf_zero_next j ltac:(lia) HjN' E0).
          destruct (Z.eqb_spec (Lg j) mx); [lia|]. cbn [andb negb]. rewrite Hwork by lia. reflexivity.
        - cbn [andb]. symmetry. apply Lremf_pos_next; lia. }
      rewrite Elen. rewrite (Lhf_succ j) by lia. rewrite land_pow2m1 by lia.
      rewrite (test_is_newblk j) by lia.
      destruct (newblk (j + 1)) eqn:Enb.
      +
        destruct (newblk_true_facts j ltac:(lia) HjN' Enb) as (HmC1 & KP & Enx & Eus & Edr & Ecu & Elo).
        replace (if dr j =? 0 then root else dr j) with root
          by (unfold dr; destruct (j <? mC); [reflexivity| destruct (Z.eqb_spec root 0); [lia|reflexivity]]).
        pose proof (Lpp_range (j + 1) ltac:(lia)) as PR1.
        pose proof (Lkp_block (ppj (j + 1)) ltac:(lia) ltac:(lia)) as HB'. rewrite KP in HB'.
        rewrite (Lhf_low (j + 1)) by lia.
        rewrite (Lsubsz (j + 1) _ _ HB' Hcnt'). fold (Dq (ppj (j + 1))). rewrite <- Ecu.
        rewrite Z.shiftl_1_l.
        pose proof (phase_facts (j + 1) ltac:(lia)) as (Fdr1 & Fld1 & Fcu1 & Fnx1 & Fus11 & Fus21 & Fus31).
        assert (PC1 : 0 < 2 ^ cu (j + 1) <= 2 ^ 15) by (split; [apply pow2_pos; lia | apply Z.pow_le_mono_r; lia]).
        pose proof P15 as P15'.
        rewrite (wrap32_id (us j + 2 ^ cu (j + 1))) by (change (2 ^ 32) with (65536 * 65536); lia).
        rewrite <- Eus. rewrite <- Enx. rewrite <- Elo. fold (LINK (j + 1)).
        change (newblk (j + 1) && it_not_enough ty (us (j + 1))) with (NF (j + 1)).
        destruct (it_not_enough ty (us (j + 1))) eqn:Ene.
        *
          cbn [t_work]. split; [lia|]. split; [rewrite NF_eq, Enb, Ene; reflexivity|]. reflexivity.
        *
          cbn [t_tbl t_work]. split; [lia|]. split; [rewrite NF_eq, Enb, Ene; reflexivity|].
          split; [| split; reflexivity].
          unfold IS; cbn [t_sym t_len t_huff t_count t_work t_drop t_curr t_next t_used t_low t_min].
          split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
          split; [rewrite arr_len_set; exact Hclen|]. split; [exact Hcnt'|]. split; [exact Hwork|].
          split; [symmetry; exact Edr|]. assert (PCj : 0 < 2 ^ cu j <= 2 ^ 15) by (split; [apply pow2_pos; lia | apply Z.pow_le_mono_r; lia]).
          repeat split; try reflexivity; try lia. exact Ene.
      +
        destruct (newblk_false_facts j ltac:(lia) HjN' Enb) as (Enx & Eus & Edr & Ecu & Elo & _).
        cbn [t_tbl t_work]. split; [lia|]. split; [rewrite NF_eq, Enb; reflexivity|].
        split; [| split; reflexivity].
        unfold IS; cbn [t_sym t_len t_huff t_count t_work t_drop t_curr t_next t_used t_low t_min].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [rewrite arr_len_set; exact Hclen|]. split; [exact Hcnt'|]. split; [exact Hwork|].
        rewrite Enx, Eus, Edr, Ecu, Elo. assert (PCj : 0 < 2 ^ cu j <= 2 ^ 15) by (split; [apply pow2_pos; lia | apply Z.pow_le_mono_r; lia]).
        repeat split; try reflexivity; try lia. exact Hoku.
  Qed.


  Local Notation X := (mkItCtx ty lens lens_ofs table root mx (2 ^ root - 1)).

  Definition STEP (j : Z) (t : arr) : arr :=
    if (j + 1 <? Nn) && newblk (j + 1) then arr_set (FILL j t) (table + lo (j + 1)) (LINK (j + 1)) else FILL j t.
  Fixpoint UPD (n : nat) (j : Z) (t : arr) : arr :=
    match n with O => t | S n' => UPD n' (j + 1) (STEP j t) end.

  Definition FIN (st : ItSt) (work t : arr) : Prop :=
    t_tbl st = t /\ t_work st = work /\ t_huff st = 0 /\ t_next st = nx (Nn - 1) /\ t_used st = us (Nn - 1)
    /\ t_drop st = dr (Nn - 1) /\ t_len st = Lg (Nn - 1) /\ t_curr st = cu (Nn - 1).

  Lemma UPD_S : forall n j t, UPD (S n) j t = UPD n (j + 1) (STEP j t).
  Proof. reflexivity. Qed.

  Lemma loop_ok : forall (n : nat) j st, 0 <= j < Nn -> IS j st -> Nn - j <= Z.of_nat n ->
    (forall k, j < k < Nn -> NF k = false) ->
    exists stF, it_loop_n X (Z.of_nat n) st = inl stF /\ FIN stF (t_work st) (UPD (Z.to_nat (Nn - j)) j (t_tbl st)).
  Proof.
    induction n as [|n IH]; intros j st Hj HIS Hn HNF; [lia|].
    rewrite it_loop_n_step by lia. pose proof (trip j st Hj HIS) as TP.
    destruct (it_step X st) as [st'|st'|st']; unfold trip_post in TP.
    - destruct TP as (HjN & HNF1 & HIS' & Hw & Ht).
      replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
      destruct (IH (j + 1) st' ltac:(lia) HIS' ltac:(lia) ltac:(intros k Hk; apply HNF; lia)) as (stF & E & F).
      exists stF. split; [exact E|]. rewrite Hw, Ht in F.
      replace (Z.to_nat (Nn - j)) with (S (Z.to_nat (Nn - (j + 1)))) by lia. rewrite UPD_S.
      unfold STEP. replace (j + 1 <? Nn) with true by (symmetry; apply Z.ltb_lt; lia). exact F.
    - destruct TP as (HjN & Ht & Hw & Hh & Hnx & Hus & Hdr & Hlen & Hcu).
      exists st'. split; [reflexivity|].
      replace (Z.to_nat (Nn - j)) with 1%nat by lia. cbn [UPD]. unfold STEP.
      replace (j + 1 <? Nn) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_l.
      unfold FIN. replace (Nn - 1) with j by lia. repeat split; assumption.
    - destruct TP as (HjN & HNF1 & _). rewrite (HNF (j + 1)) in HNF1 by lia. discriminate.
  Qed.

  Lemma loop_fail : forall (n : nat) j st k, 0 <= j < k -> k < Nn -> IS j st -> k - j <= Z.of_nat n ->
    NF k = true -> (forall k', j < k' < k -> NF k' = false) ->
    exists stF, it_loop_n X (Z.of_nat n) st = inr stF /\ t_work stF = t_work st.
  Proof.
    induction n as [|n IH]; intros j st k Hjk Hk HIS Hn HNFk HNF; [lia|].
    rewrite it_loop_n_step by lia. pose proof (trip j st ltac:(lia) HIS) as TP.
    destruct (it_step X st) as [st'|st'|st']; unfold trip_post in TP.
    - destruct TP as (HjN & HNF1 & HIS' & Hw & Ht).
      assert (j + 1 <> k) by (intros E; rewrite E in HNF1; rewrite HNFk in HNF1; discriminate).
      replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
      destruct (IH (j + 1) st' k ltac:(lia) Hk HIS' ltac:(lia) HNFk ltac:(intros k' Hk'; apply HNF; lia)) as (stF & E & F).
      exists stF. split; [exact E|]. rewrite F. exact Hw.
    - destruct TP as (HjN & _). lia.
    - destruct TP as (HjN & HNF1 & Hw). exists st'. split; [reflexivity | exact Hw].
  Qed.


  Hypothesis Hroot_fits : it_not_enough ty (2 ^ root) = false.

  Lemma hf0 : hfj 0 = 0.
  Proof.
    unfold hf. replace (cc Lg 0) with 0; [apply brv_0|].
    unfold cc, cw. rewrite (T_a Lg 0 15). rewrite Z.div_0_l; [reflexivity|]. apply Z.pow_nonzero; [lia|].
    pose proof (CL 0 ltac:(pose proof CN; lia)). lia.
  Qed.

  Lemma IS0 : forall tbl work, Nn <= arr_len work ->
    IS 0 (mkItSt 0 0 mn table root 0 4294967295 (2 ^ root) 0 (count lens lens_ofs codes) tbl
               (snd (it_sort lens lens_ofs codes (offs lens lens_ofs codes, work)))).
  Proof.
    intros tbl work Hw. pose proof Lm as (Lm1 & _ & _).
    assert (T0 : (0 <? mC) = true) by (apply Z.ltb_lt; lia).
    unfold IS; cbn [t_sym t_len t_huff t_count t_work t_drop t_curr t_next t_used t_low t_min].
    split; [reflexivity|]. split; [symmetry; apply (Lf_first lens lens_ofs codes Hcodes Hlens Hmax)|].
    split; [symmetry; apply hf0|].
    split; [apply (count_len lens lens_ofs codes Hcodes Hlens)|].
    split; [intros l Hl; rewrite (count_spec lens lens_ofs codes Hcodes Hlens) by lia; symmetry; apply (remf_cnt lens lens_ofs codes Hcodes); exact Hl|].
    split; [intros i Hi; apply (proj1 (proj2 (sort_spec lens lens_ofs codes Hcodes Hlens work Hw))); exact Hi|].
    unfold dr, cu, nx, us, lo. rewrite T0. repeat split; try reflexivity; try lia. exact Hroot_fits.
  Qed.


  Definition hitsF (j i : Z) : bool :=
    fill_hits (nx j + Z.shiftr (hfj j) (dr j)) (2 ^ (Lg j - dr j)) (2 ^ (cu j - (Lg j - dr j))) i.
  Definition STEPW (j i : Z) : option Z :=
    if (j + 1 <? Nn) && newblk (j + 1) && (i =? table + lo (j + 1)) then Some (LINK (j + 1))
    else if hitsF j i then Some (HV j) else None.
  Fixpoint LW (n : nat) (j i : Z) : option Z :=
    match n with
    | O => None
    | S n' => match LW n' (j + 1) i with Some v => Some v | None => STEPW j i end
    end.

  Definition usF : Z := us (Nn - 1).

  Lemma usF_eq : usF = 2 ^ root + SBq (2 ^ root).
  Proof.
    unfold usF, us. pose proof Lm as (Lm1 & _ & _). destruct (Z.ltb_spec (Nn - 1) mC).
    -
      assert (mC = Nn) as E by lia.
      unfold SB. rewrite sumZ_nil; [lia|].
      unfold pp. rewrite E, CC. unfold B. pose proof CR.
      replace (2 ^ 15) with (2 ^ root * 2 ^ (15 - root)) by (rewrite <- pow2_split by lia; f_equal; lia).
      rewrite Z.div_mul by (apply Z.pow_nonzero; lia). lia.
    - rewrite Lpp_last by lia. rewrite <- Z.add_assoc, <- LSB_step.
      + f_equal. f_equal. lia.
      + pose proof (Lpp_range mC ltac:(lia)). lia.
  Qed.

  Lemma us_le_usF : forall j, 0 <= j < Nn -> us j <= usF.
  Proof.
    intros j Hj. rewrite usF_eq. pose proof Lm as (Lm1 & _ & _). pose proof CR as HR. unfold us. destruct (Z.ltb_spec j mC).
    - pose proof (LSB_nonneg (2 ^ root)). lia.
    - pose proof (Lpp_range j ltac:(lia)) as PR. rewrite <- Z.add_assoc, <- LSB_step by lia.
      pose proof (SB_mono Nn Lg root (ppj j + 1) (2 ^ root) ltac:(lia)). lia.
  Qed.

  Lemma fill_hits_inv : forall base incr q x, 0 < incr -> fill_hits base incr q x = true ->
    exists t, 0 <= t < q /\ x = base + t * incr.
  Proof.
    intros base incr q x Hi H. unfold fill_hits in H.
    apply andb_prop in H. destruct H as [H1 H3]. apply andb_prop in H1. destruct H1 as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3.
    exists ((x - base) / incr). pose proof (Z.div_mod (x - base) incr ltac:(lia)) as DM. rewrite H3 in DM.
    split; [|lia]. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia.
  Qed.

  Lemma hitsF_range : forall j i, 0 <= j < Nn -> hitsF j i = true -> nx j <= i < nx j + 2 ^ cu j.
  Proof.
    intros j i Hj H. pose proof (phase_facts j Hj) as (Fdr & Fld & Fcu & Fnx & _).
    pose proof (Lhf_range j Hj) as HR.
    assert (Hh : 0 <= Z.shiftr (hfj j) (dr j) < 2 ^ (Lg j - dr j)).
    { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply pow2_pos; lia]|].
      apply Z.div_lt_upper_bound; [apply pow2_pos; lia|]. rewrite <- pow2_split by lia.
      replace (dr j + (Lg j - dr j)) with (Lg j) by lia. lia. }
    unfold hitsF in H. apply fill_hits_inv in H; [|apply pow2_pos; lia]. destruct H as (t & Ht & ->).
    assert (E : 2 ^ cu j = 2 ^ (cu j - (Lg j - dr j)) * 2 ^ (Lg j - dr j)) by (rewrite <- pow2_split by lia; f_equal; lia).
    pose proof (pow2_pos (Lg j - dr j) ltac:(lia)). nia.
  Qed.

  Lemma STEPW_range : forall j i v, 0 <= j < Nn -> STEPW j i = Some v -> table <= i < table + usF.
  Proof.
    intros j i v Hj H. pose proof (us_le_usF j Hj) as U. pose proof (phase_facts j Hj) as (Fdr & Fld & Fcu & Fnx & Fus1 & Fus2 & Fus3).
    unfold STEPW in H.
    destruct ((j + 1 <? Nn) && newblk (j + 1) && (i =? table + lo (j + 1))) eqn:E.
    - apply andb_prop in E. destruct E as [E1 E3]. apply andb_prop in E1. destruct E1 as [E1 E2].
      apply Z.ltb_lt in E1. apply Z.eqb_eq in E3.
      destruct (newblk_true_facts j ltac:(lia) E1 E2) as (HmC1 & _ & _ & _ & _ & _ & Elo).
      pose proof (Lbrv_pp (j + 1) ltac:(lia)). lia.
    - destruct (hitsF j i) eqn:F; [|discriminate]. pose proof (hitsF_range j i Hj F). lia.
  Qed.

  Lemma LW_range : forall n j i v, 0 <= j -> j + Z.of_nat n <= Nn -> LW n j i = Some v -> table <= i < table + usF.
  Proof.
    induction n as [|n IH]; intros j i v Hj Hn H; cbn [LW] in H; [discriminate|].
    destruct (LW n (j + 1) i) eqn:E.
    - eapply (IH (j + 1)); [lia | lia | exact E].
    - eapply STEPW_range; [| exact H]. lia.
  Qed.

  Variable TN : Z.
  Hypothesis Hinb : table + usF <= TN.

  Lemma STEP_spec : forall j t i, 0 <= j < Nn -> arr_len t = TN ->
    arr_len (STEP j t) = TN /\ arr_get (STEP j t) i = match STEPW j i with Some v => v | None => arr_get t i end.
  Proof.
    intros j t i Hj Hlen. pose proof (phase_facts j Hj) as (Fdr & Fld & Fcu & Fnx & Fus1 & Fus2 & Fus3).
    destruct (it_fill_spec (HV j) (Lg j - dr j) (cu j) (hfj j) (dr j) (nx j) t ltac:(lia) ltac:(lia)) as [L G].
    fold (FILL j t) in L, G. rewrite Hlen in L.
    assert (GF : arr_get (FILL j t) i = if hitsF j i then HV j else arr_get t i).
    { rewrite G. unfold hitsF. destruct (fill_hits _ _ _ i) eqn:F; [|reflexivity].
      pose proof (hitsF_range j i Hj F). pose proof (us_le_usF j Hj).
      unfold arr_inb. rewrite Hlen. replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
      replace (i <? TN) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    unfold STEP, STEPW.
    destruct ((j + 1 <? Nn) && newblk (j + 1)) eqn:E.
    - rewrite arr_len_set. split; [exact L|]. rewrite andb_true_l.
      apply andb_prop in E. destruct E as [E1 E2]. apply Z.ltb_lt in E1.
      destruct (newblk_true_facts j ltac:(lia) E1 E2) as (HmC1 & _ & _ & _ & _ & _ & Elo).
      pose proof (Lbrv_pp (j + 1) ltac:(lia)). pose proof (us_le_usF j Hj).
      destruct (Z.eqb_spec i (table + lo (j + 1))) as [->|NE].
      + apply arr_get_set_same. rewrite L. lia.
      + rewrite arr_get_set_other by (intros X; apply NE; symmetry; exact X). rewrite GF. destruct (hitsF j i); reflexivity.
    - rewrite andb_false_l. split; [exact L | rewrite GF; destruct (hitsF j i); reflexivity].
  Qed.

  Lemma UPD_spec : forall n j t i, 0 <= j -> j + Z.of_nat n <= Nn -> arr_len t = TN ->
    arr_len (UPD n j t) = TN /\ arr_get (UPD n j t) i = match LW n j i with Some v => v | None => arr_get t i end.
  Proof.
    induction n as [|n IH]; intros j t i Hj Hn Hlen; cbn [UPD LW]; [split; [exact Hlen|reflexivity]|].
    destruct (STEP_spec j t i ltac:(lia) Hlen) as [L1 G1].
    destruct (IH (j + 1) (STEP j t) i ltac:(lia) ltac:(lia) L1) as [L2 G2].
    split; [exact L2|]. rewrite G2. destruct (LW n (j + 1) i); [reflexivity | exact G1].
  Qed.


  Lemma fill_hits_mod : forall base incr q h x, 0 < incr -> 0 <= h < incr -> 0 <= x < q * incr ->
    x mod incr = h -> fill_hits (base + h) incr q (base + x) = true.
  Proof.
    intros base incr q h x Hi Hh Hx Hm. pose proof (Z.div_mod x incr ltac:(lia)) as DM. rewrite Hm in DM.
    pose proof (Z.div_pos x incr ltac:(lia) Hi) as DP.
    unfold fill_hits. apply andb_true_intro; split; [apply andb_true_intro; split|].
    - apply Z.leb_le. lia.
    - apply Z.ltb_lt. lia.
    - apply Z.eqb_eq. replace (base + x - (base + h)) with (incr * (x / incr)) by lia. rewrite Z.mul_comm. apply Z.mod_mul. lia.
  Qed.

  Lemma LW_hit : forall n j i j', 0 <= j -> j <= j' < j + Z.of_nat n -> STEPW j' i <> None -> LW n j i <> None.
  Proof.
    induction n as [|n IH]; intros j i j' Hj Hj' H; [lia|]. cbn [LW].
    destruct (LW n (j + 1) i) eqn:E; [discriminate|].
    destruct (Z.eq_dec j' j) as [->|NE]; [exact H|].
    exfalso. apply (IH (j + 1) i j' ltac:(lia) ltac:(lia) H). exact E.
  Qed.

  Lemma STEPW_fill : forall j i, hitsF j i = true -> STEPW j i <> None.
  Proof. intros j i H. unfold STEPW. rewrite H. destruct (_ && _ && _); discriminate. Qed.

  Lemma T_root_m : T Lg 0 root mC = ppj mC.
  Proof.
    pose proof Lm as (Lm1 & _ & _). pose proof (S_short Nn Lg root CN CL CS CR CRm mC ltac:(lia)) as E.
    rewrite Lpp_m in E. pose proof (B_pos root CR). nia.
  Qed.

  Lemma cover_root : forall i, table <= i < table + 2 ^ root -> LW (Z.to_nat Nn) 0 i <> None.
  Proof.
    intros i Hi. pose proof Lm as (Lm1 & Lm2 & Lm3). pose proof CR as HR. pose proof CN.
    set (x := i - table). assert (Hx : 0 <= x < 2 ^ root) by lia.
    destruct (Z_lt_le_dec (brv (Z.to_nat root) x) (T Lg 0 root mC)) as [LT|GE].
    -
      destruct (root_fill_cover Nn Lg root CN CL CS CR CRm CC x Hx LT) as (k & Hk & E).
      pose proof (CL k ltac:(lia)) as HLk. pose proof (Lm2 k Hk). pose proof (Lhf_range k ltac:(lia)).
      apply (LW_hit _ 0 i k); [lia | lia |]. apply STEPW_fill.
      unfold hitsF, nx, dr, cu. replace (k <? mC) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite Z.shiftr_0_r, Z.sub_0_r. replace i with (table + x) by lia.
      apply fill_hits_mod; [apply pow2_pos; lia | lia | | exact E].
      rewrite <- pow2_split by lia. replace (root - Lg k + Lg k) with root by lia. lia.
    -
      rewrite T_root_m in GE.
      assert (HmN : mC < Nn).
      { destruct (Z.eq_dec mC Nn) as [E|]; [|lia]. exfalso.
        pose proof (brv_range (Z.to_nat root) x) as BR. rewrite Z2Nat.id in BR by lia.
        assert (P : ppj mC = 2 ^ root); [|lia].
        unfold pp. rewrite E, CC. unfold B.
        replace (2 ^ 15) with (2 ^ root * 2 ^ (15 - root)) by (rewrite <- pow2_split by lia; f_equal; lia).
        apply Z.div_mul. apply Z.pow_nonzero; lia. }
      set (y := brv (Z.to_nat root) x) in *.
      pose proof (brv_range (Z.to_nat root) x) as BR. rewrite Z2Nat.id in BR by lia. fold y in BR.
      pose proof (kp_lt_N Nn Lg root CN CL CS CR CRm CC y HmN ltac:(lia)) as KN.
      destruct (kp_start Nn Lg root CN CL CS CR CRm CC y ltac:(lia) KN) as [PK _].
      destruct (Lkp_spec y) as (R & P & Q).
      set (k := kpq y) in *.
      assert (NB : newblk k = true).
      { rewrite newblk_eq. apply andb_true_intro; split; [apply Z.leb_le; lia|].
        destruct (Z.eq_dec k mC) as [->|NE]; [rewrite Z.eqb_refl; reflexivity|].
        apply Bool.orb_true_iff; right. apply negb_true_iff. apply Z.eqb_neq.
        pose proof (P (k - 1) ltac:(lia)). lia. }
      apply (LW_hit _ 0 i (k - 1)); [lia | lia |].
      unfold STEPW. replace (k - 1 + 1) with k by lia. rewrite NB.
      replace (k <? Nn) with true by (symmetry; apply Z.ltb_lt; lia).
      unfold lo. replace (k <? mC) with false by (symmetry; apply Z.ltb_ge; lia). rewrite PK.
      unfold y. rewrite brv_brv by (rewrite Z2Nat.id by lia; lia).
      replace (i =? table + x) with true by (symmetry; apply Z.eqb_eq; lia). discriminate.
  Qed.

  Lemma cover_sub : forall i, table + 2 ^ root <= i < table + usF -> LW (Z.to_nat Nn) 0 i <> None.
  Proof.
    intros i Hi. rewrite usF_eq in Hi. pose proof Lm as (Lm1 & Lm2 & Lm3). pose proof CR as HR. pose proof CN.
    set (off := i - table - 2 ^ root).
    assert (HmN : mC < Nn).
    { destruct (Z.eq_dec mC Nn) as [E|]; [|lia]. exfalso.
      assert (P : ppj mC = 2 ^ root).
      { unfold pp. rewrite E, CC. unfold B.
        replace (2 ^ 15) with (2 ^ root * 2 ^ (15 - root)) by (rewrite <- pow2_split by lia; f_equal; lia).
        apply Z.div_mul. apply Z.pow_nonzero; lia. }
      unfold SB in Hi. rewrite sumZ_nil in Hi by lia. lia. }
    pose proof (Lpp_range mC ltac:(lia)) as PR.
    destruct (step_over SBq (ppj mC) (2 ^ root) off ltac:(lia) ltac:(rewrite LSB_first; lia)) as (p & Hp & Hoff).
    rewrite LSB_step in Hoff by lia.
    pose proof (Lkp_block p Hp HmN) as HB.
    pose proof (LDp_range p Hp HmN) as DR.
    set (a := kpq p) in *. set (e := kpq (p + 1)) in *.
    assert (ED : Dq p = Dj e) by reflexivity.
    set (x := off - SBq p).
    assert (Hx : 0 <= x < 2 ^ Dj e) by (rewrite <- ED; lia).
    pose proof (brv_range (Z.to_nat (Dj e)) x) as BR. rewrite Z2Nat.id in BR by lia.
    pose proof (T_sub_full Nn Lg root CN CL CS CRm a e HB) as TF.
    destruct HB as (B1 & B2 & B3 & B4 & B5) eqn:EHB. clear EHB.
    destruct (sub_fill_cover Nn Lg root CN CL CS CR CRm CC a e HB e x ltac:(lia) Hx ltac:(rewrite TF; lia)) as (k & Hk & E).
    pose proof (CL k ltac:(lia)) as HLk. pose proof (Lm3 k ltac:(lia)). pose proof (Lhf_range k ltac:(lia)) as HFR.
    pose proof (Ldsub_range a e k HB Hk) as DS.
    destruct (kp_start Nn Lg root CN CL CS CR CRm CC p ltac:(lia) ltac:(lia)) as [PK _]. fold a in PK.
    assert (PPk : ppj k = p) by (rewrite (B4 k Hk); exact PK).
    apply (LW_hit _ 0 i k); [lia | lia |]. apply STEPW_fill.
    unfold hitsF, nx, dr, cu. replace (k <? mC) with false by (symmetry; apply Z.ltb_ge; lia). rewrite PPk, ED.
    replace i with (table + 2 ^ root + SBq p + x) by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    apply fill_hits_mod.
    - apply pow2_pos; lia.
    - split; [apply Z.div_pos; [lia | apply pow2_pos; lia]|].
      apply Z.div_lt_upper_bound; [apply pow2_pos; lia|]. rewrite <- pow2_split by lia. replace (root + (Lg k - root)) with (Lg k) by lia. lia.
    - rewrite <- pow2_split by lia. replace (Dj e - (Lg k - root) + (Lg k - root)) with (Dj e) by lia. lia.
    - unfold dsub in E. exact E.
  Qed.

  Theorem cover : forall i, table <= i < table + usF -> LW (Z.to_nat Nn) 0 i <> None.
  Proof.
    intros i Hi. destruct (Z_lt_le_dec i (table + 2 ^ root)); [apply cover_root; lia | apply cover_sub; lia].
  Qed.


  Definition WK (i v : Z) : Prop :=
    (exists j, 0 <= j < mC /\ v = HV j /\ dr j = 0 /\ cu j = root /\ nx j = table /\ hitsF j i = true
               /\ table <= i < table + 2 ^ root)
    \/ (exists k, mC <= k < Nn /\ newblk k = true /\ v = LINK k /\ i = table + lo k
               /\ table <= i < table + 2 ^ root
               /\ 1 <= cu k <= 15 - root /\ 2 ^ root <= nx k - table /\ nx k - table + 2 ^ cu k <= usF)
    \/ (exists j, mC <= j < Nn /\ v = HV j /\ dr j = root /\ 1 <= cu j <= 15 - root /\ hitsF j i = true
               /\ table + 2 ^ root <= nx j /\ nx j <= i < nx j + 2 ^ cu j /\ nx j + 2 ^ cu j <= table + usF).

  Lemma STEPW_kind : forall j i v, 0 <= j < Nn -> STEPW j i = Some v -> WK i v.
  Proof.
    intros j i v Hj H. pose proof Lm as (Lm1 & Lm2 & Lm3). pose proof CR as HR.
    pose proof (phase_facts j Hj) as (Fdr & Fld & Fcu & Fnx & Fus1 & Fus2 & Fus3). pose proof (us_le_usF j Hj) as U.
    unfold STEPW in H.
    destruct ((j + 1 <? Nn) && newblk (j + 1) && (i =? table + lo (j + 1))) eqn:E.
    -
      apply andb_prop in E. destruct E as [E1 E3]. apply andb_prop in E1. destruct E1 as [E1 E2].
      apply Z.ltb_lt in E1. apply Z.eqb_eq in E3. injection H as <-.
      destruct (newblk_true_facts j ltac:(lia) E1 E2) as (HmC1 & KP & Enx & Eus & Edr & Ecu & Elo).
      pose proof (Lbrv_pp (j + 1) ltac:(lia)) as BR.
      pose proof (phase_facts (j + 1) ltac:(lia)) as (Fdr1 & Fld1 & Fcu1 & Fnx1 & Fus11 & Fus21 & Fus31).
      pose proof (us_le_usF (j + 1) ltac:(lia)) as U1.
      pose proof (Lpp_range (j + 1) ltac:(lia)) as PR1. pose proof (LDp_range (ppj (j + 1)) ltac:(lia) ltac:(lia)) as DR1.
      right; left. exists (j + 1).
      split; [lia|]. split; [exact E2|]. split; [reflexivity|]. split; [exact E3|]. split; [lia|].
      split; [rewrite Ecu; exact DR1|].
      rewrite Enx. pose proof (pow2_pos (cu j) ltac:(lia)). split; [lia|]. rewrite <- Enx. lia.
    - destruct (hitsF j i) eqn:F; [|discriminate]. injection H as <-.
      pose proof (hitsF_range j i Hj F) as IR.
      destruct (Z_lt_le_dec j mC) as [Hjm|Hjm].
      + left. exists j. unfold dr, cu, nx in *.
        replace (j <? mC) with true in * by (symmetry; apply Z.ltb_lt; lia).
        repeat split; try lia. exact F.
      + right; right. exists j.
        pose proof (Lpp_range j ltac:(lia)) as PR. pose proof (LDp_range (ppj j) ltac:(lia) ltac:(lia)) as DR.
        assert (Edr : dr j = root) by (unfold dr; replace (j <? mC) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        assert (Ecu : cu j = Dq (ppj j)) by (unfold cu; replace (j <? mC) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        assert (Enx : nx j = table + 2 ^ root + SBq (ppj j)) by (unfold nx; replace (j <? mC) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        pose proof (LSB_nonneg (ppj j)).
        split; [lia|]. split; [reflexivity|]. split; [exact Edr|]. split; [rewrite Ecu; exact DR|]. split; [exact F|].
        split; [rewrite Enx; lia|]. split; [exact IR|]. lia.
  Qed.

  Lemma LW_kind : forall n j i v, 0 <= j -> j + Z.of_nat n <= Nn -> LW n j i = Some v -> WK i v.
  Proof.
    induction n as [|n IH]; intros j i v Hj Hn H; cbn [LW] in H; [discriminate|].
    destruct (LW n (j + 1) i) eqn:E.
    - injection H as <-. eapply (IH (j + 1)); [lia | lia | exact E].
    - eapply STEPW_kind; [| exact H]. lia.
  Qed.


  Variables WN LN : Z.
  Hypothesis HWN : codes <= WN.
  Hypothesis Hofs : 0 <= lens_ofs.
  Hypothesis HLN : lens_ofs + codes <= LN.
  Hypothesis HtyD : ty = DISTS -> codes <= 32.

  Lemma usF_lt : usF < 65536.
  Proof.
    rewrite usF_eq. pose proof Lm as (Lm1 & Lm2 & Lm3). pose proof CR as HR.
    destruct (Z.eq_dec mC Nn) as [E|NE].
    - assert (P : ppj mC = 2 ^ root).
      { unfold pp. rewrite E, CC. unfold B.
        replace (2 ^ 15) with (2 ^ root * 2 ^ (15 - root)) by (rewrite <- pow2_split by lia; f_equal; lia).
        apply Z.div_mul. apply Z.pow_nonzero; lia. }
      unfold SB. rewrite sumZ_nil by lia. pose proof P15. change (2 ^ 15) with 32768 in *. lia.
    - pose proof (LSB_bound (2 ^ root) ltac:(pose proof (Lpp_range mC ltac:(lia)); lia) ltac:(lia)) as SBB.
      pose proof Lpp0. pose proof (B_pos root CR).
      assert (E15 : 2 ^ 15 = 2 ^ root * Bq) by (unfold B; rewrite <- pow2_split by lia; f_equal; lia).
      pose proof (Lm3 mC ltac:(lia)). pose proof (CL mC ltac:(lia)).
      assert (2 ^ root <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
      change (2 ^ 15) with 32768 in *. change (2 ^ 14) with 16384 in *. nia.
  Qed.

  Hypothesis Hfits : forall j, 0 <= j < Nn -> it_not_enough ty (us j) = false -> table + us j <= TN.

  Lemma trip_ok : forall j st, 0 <= j < Nn -> IS j st -> it_trip_ok X WN LN TN st = true.
  Proof.
    clear Hinb. intros j st Hj HIS. pose proof (trip j st Hj HIS) as TP.
    pose proof Lm as (Lm1 & Lm2 & Lm3). pose proof CR as HR. pose proof (CL j Hj) as HLj. pose proof LNn.
    pose proof (phase_facts j Hj) as (Fdr & Fld & Fcu & Fnx & Fus1 & Fus2 & Fus3). pose proof (us_le_usF j Hj) as U.
    pose proof usF_lt as UF. pose proof (Lhf_range j Hj) as HFR. pose proof (LWr j Hj) as WR.
    assert (HL15 : 2 ^ Lg j <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
    destruct st as [huff sym len next curr drop low used mn0 count tbl work].
    unfold IS in HIS; cbn [t_sym t_len t_huff t_count t_work t_drop t_curr t_next t_used t_low t_min] in HIS.
    destruct HIS as (Hsym & Hlen & Hhuff & Hclen & Hcnt & Hwork & Hdrop & Hcurr & Hnext & Hused & Hlow & Hoku & Hmin).
    pose proof (Hfits j Hj Hoku) as FIT.
    subst sym len huff drop curr next used low.
    unfold it_trip_ok. cbn [t_sym t_len t_huff t_count t_work t_drop t_curr t_next t_used t_low t_min x_ty x_lens x_lens_ofs x_table x_max].
    rewrite Hwork by lia.
    assert (Hh : 0 <= Z.shiftr (hfj j) (dr j) < 2 ^ (Lg j - dr j)).
    { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply pow2_pos; lia]|].
      apply Z.div_lt_upper_bound; [apply pow2_pos; lia|]. rewrite <- pow2_split by lia.
      replace (dr j + (Lg j - dr j)) with (Lg j) by lia. lia. }
    rewrite !Z.shiftl_1_l.
    repeat match goal with |- (?a && ?b) = true => apply andb_true_intro; split end;
      try (apply Z.leb_le; lia); try (apply Z.ltb_lt; lia).
    -
      destruct ty; cbn [it_match it_ext_len].
      + pose proof (HtyC eq_refl). replace (znth 0 Wl j + 1 <? 20) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + destruct (Z.ltb_spec (znth 0 Wl j + 1) 257); [reflexivity|]. destruct (Z.leb_spec 257 (znth 0 Wl j)); [|reflexivity]. apply Z.ltb_lt. lia.
      + pose proof (HtyD eq_refl). destruct (Z.ltb_spec (znth 0 Wl j + 1) 0); [reflexivity|]. destruct (Z.leb_spec 0 (znth 0 Wl j)); [|reflexivity]. apply Z.ltb_lt. lia.
    -
      destruct (Z.eq_dec (j + 1) Nn) as [E|NE].
      + rewrite Hcnt by lia.
        assert (E0 : remj j (Lg j) = 1).
        { pose proof (Lremf_step j (Lg j) ltac:(lia)) as St. rewrite Z.eqb_refl in St. rewrite E, Lremf_N in St. lia. }
        rewrite E0. change (wrap16 (1 - 1) =? 0) with true.
        replace (Lg j =? mx) with true by (symmetry; apply Z.eqb_eq; replace j with (Nn - 1) by lia; apply LLast). reflexivity.
      + rewrite Hwork by lia. pose proof (LWr (j + 1) ltac:(lia)) as WR1. pose proof (CL (j + 1) ltac:(lia)) as HL1.
        unfold Lf, L in HL1.
        destruct (_ && negb _); [|reflexivity].
        repeat match goal with |- (?a && ?b) = true => apply andb_true_intro; split end;
          try (apply Z.leb_le; lia); try (apply Z.ltb_lt; lia).
    -
      destruct (it_step X _) as [st'|st'|st']; unfold trip_post in TP; cbn [t_tbl t_work] in TP; try reflexivity.
      destruct TP as (HjN & HNF1 & HIS' & Hw & Ht).
      unfold IS in HIS'. destruct HIS' as (_ & _ & _ & _ & _ & _ & Hdrop' & Hcurr' & Hnext' & Hused' & Hlow' & _).
      rewrite Hlow', Hnext', Hcurr'.
      destruct (newblk (j + 1)) eqn:Enb.
      + destruct (newblk_true_facts j ltac:(lia) HjN Enb) as (HmC1 & KP & Enx & Eus & Edr & Ecu & Elo).
        pose proof (Lbrv_pp (j + 1) ltac:(lia)). pose proof (Lpp_range (j + 1) ltac:(lia)).
        pose proof (LDp_range (ppj (j + 1)) ltac:(lia) ltac:(lia)). pose proof (pow2_pos (cu j) ltac:(lia)).
        destruct (negb _ || negb _); [|reflexivity].
        repeat match goal with |- (?a && ?b) = true => apply andb_true_intro; split end;
          try (apply Z.leb_le; lia); try (apply Z.ltb_lt; lia).
      + destruct (newblk_false_facts j ltac:(lia) HjN Enb) as (Enx & Eus & Edr & Ecu & Elo & _).
        rewrite Elo, Enx, !Z.eqb_refl. reflexivity.
  Qed.

  Lemma safe_from : forall (n : nat) j st, 0 <= j < Nn -> IS j st -> Nn - j <= Z.of_nat n ->
    it_loop_ok n X WN LN TN st = true.
  Proof.
    clear Hinb. induction n as [|n IH]; intros j st Hj HIS Hn; [lia|].
    rewrite it_loop_ok_S. rewrite (trip_ok j st Hj HIS), andb_true_l.
    pose proof (trip j st Hj HIS) as TP.
    destruct (it_step X st) as [st'|st'|st']; unfold trip_post in TP.
    - destruct TP as (HjN & _ & HIS' & _). apply (IH (j + 1)); [lia | exact HIS' | lia].
    - destruct TP as (_ & _ & _ & Hh & _). rewrite Hh. reflexivity.
    - reflexivity.
  Qed.


  Lemma kp_newblk : forall p, ppj mC <= p < 2 ^ root -> mC < Nn -> newblk (kpq p) = true /\ mC <= kpq p < Nn /\ ppj (kpq p) = p.
  Proof.
    intros p Hp HmN. pose proof Lm as (Lm1 & _ & _). pose proof CR as HR.
    pose proof (kp_lt_N Nn Lg root CN CL CS CR CRm CC p HmN ltac:(lia)) as KN.
    destruct (kp_start Nn Lg root CN CL CS CR CRm CC p ltac:(lia) KN) as [PK _].
    destruct (Lkp_spec p) as (R & P & Q).
    split; [|split; [lia | exact PK]].
    rewrite newblk_eq. apply andb_true_intro; split; [apply Z.leb_le; lia|].
    destruct (Z.eq_dec (kpq p) mC) as [->|NE]; [rewrite Z.eqb_refl; reflexivity|].
    apply Bool.orb_true_iff; right. apply negb_true_iff. apply Z.eqb_neq.
    pose proof (P (kpq p - 1) ltac:(lia)). lia.
  Qed.

  Lemma us_block : forall j, mC <= j < Nn -> us j = us (kpq (ppj j)).
  Proof.
    intros j Hj. pose proof Lm as (Lm1 & _ & _). pose proof CR as HR. pose proof (Lpp_range j Hj) as PR.
    destruct (kp_newblk (ppj j) ltac:(lia) ltac:(lia)) as (NB & KR & PK).
    unfold us. rewrite PK. replace (j <? mC) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (kpq (ppj j) <? mC) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.

  Lemma us_fits_all : (forall k, 0 < k < Nn -> NF k = false) ->
    forall j, 0 <= j < Nn -> it_not_enough ty (us j) = false.
  Proof.
    intros HNF j Hj. pose proof Lm as (Lm1 & _ & _). pose proof CR as HR.
    destruct (Z_lt_le_dec j mC) as [L|L].
    - unfold us. replace (j <? mC) with true by (symmetry; apply Z.ltb_lt; lia). exact Hroot_fits.
    - pose proof (Lpp_range j ltac:(lia)) as PR.
      destruct (kp_newblk (ppj j) ltac:(lia) ltac:(lia)) as (NB & KR & PK).
      pose proof (HNF (kpq (ppj j)) ltac:(lia)) as F. rewrite NF_eq, NB, andb_true_l in F.
      rewrite (us_block j) by lia. exact F.
  Qed.
End Loop.
