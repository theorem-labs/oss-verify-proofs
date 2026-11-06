(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnDivCorrect BnDivLoop BnInv BnSpecs BnSpecs2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma div_values : forall m v0 sh, 0 <= m -> 0 < v0 -> 0 <= sh ->
  (m * 2 ^ sh) / (v0 * 2 ^ sh) = m / v0 /\ ((m * 2 ^ sh) mod (v0 * 2 ^ sh)) / 2 ^ sh = m mod v0.
Proof.
  intros m v0 sh Hm Hv Hsh. assert (Hp : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_mul_cancel_r; lia|]. rewrite Z.mul_mod_distr_r by lia. apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma div_top_cond : forall snum loop div_n top1 v,
  limbs snum -> (loop + div_n <= length snum)%nat -> (1 <= div_n)%nat -> (top1 <= loop + div_n - 1)%nat ->
  lval (firstn (loop + div_n) snum) < Bp top1 * 2 ^ 63 -> Bp (div_n - 1) * 2 ^ 63 <= v ->
  lval (slice snum loop div_n) < v.
Proof.
  intros snum loop div_n top1 v Hs Hlen Hdn Htop HN Hv.
  assert (E : lval (firstn (loop + div_n) snum) = lval (firstn loop snum) + Bp loop * lval (slice snum loop div_n)).
  { rewrite firstn_add, lval_app, firstn_length_le by lia. reflexivity. }
  pose proof (lval_nonneg _ (limbs_firstn loop snum Hs)) as Hlo.
  pose proof (lval_nonneg _ (slice_limbs snum loop div_n Hs)) as Hhi.
  pose proof (Bp_mono top1 (loop + div_n - 1) Htop) as Hm.
  assert (EB : Bp (loop + div_n - 1) = Bp loop * Bp (div_n - 1)) by (rewrite <- Bp_add; f_equal; lia).
  pose proof (Bp_pos loop) as Hbl. pose proof (Bp_pos (div_n - 1)) as Hbd.
  set (hi := lval (slice snum loop div_n)) in *.
  assert (Hx : Bp loop * hi < Bp loop * (Bp (div_n - 1) * 2 ^ 63)).
  { assert (Bp top1 * 2 ^ 63 <= Bp (loop + div_n - 1) * 2 ^ 63) by (apply Z.mul_le_mono_nonneg_r; lia).
    rewrite EB in H. lia. }
  apply Z.mul_lt_mono_pos_l in Hx; lia.
Qed.

(* [comment removed for export] *)
Lemma firstn_pad_zeros : forall (buf : list Z) m k, (m + k <= length buf)%nat ->
  firstn (m + k) (splice buf m (repeat 0 k)) = firstn m buf ++ repeat 0 k.
Proof.
  intros buf m k H. rewrite firstn_add. rewrite firstn_splice_below by lia. f_equal.
  change (firstn k (skipn m (splice buf m (repeat 0 k)))) with (slice (splice buf m (repeat 0 k)) m k).
  apply slice_splice_eq; [apply repeat_length|lia].
Qed.

Lemma valid_ref_pool : forall {ptr} i j (s : lstate ptr), valid_ref (RPool i) s -> (j < 3)%nat -> valid_ref (RPool j) s.
Proof. intros ptr i j s [_ H] Hj. split; assumption. Qed.

Section DivSpec.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Ltac other := rewrite ?getbn_setbn_other by congruence.

Lemma bn_div_fixed_top_spec : forall s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> ctx_rest (ls_ctx s) ->
  bn_norm (getbn RB2 s) -> (1 <= bn_top (getbn RB2 s))%nat ->
  Z.of_nat (bn_top (getbn RB1 s)) <= 32000 -> Z.of_nat (bn_top (getbn RB2 s)) <= 32000 ->
  (forall s' X', st_ok s' -> own s' X' -> ctx_rest (ls_ctx s') ->
     getbn RB1 s' = getbn RB1 s -> getbn RB2 s' = getbn RB2 s -> getbn RB5 s' = getbn RB5 s ->
     let b1 := getbn RB1 s in let b2 := getbn RB2 s in
     let q := getbn RB3 s' in let r := getbn RB4 s' in
     bn_mag q = bn_mag b1 / bn_mag b2 -> bn_mag r = bn_mag b1 mod bn_mag b2 ->
     bn_neg q = xorb (bn_neg b1) (bn_neg b2) -> bn_neg r = bn_neg b1 ->
     Z.of_nat (bn_top q) + Z.of_nat (bn_top b2) <= Z.max (Z.of_nat (bn_top b1)) (Z.of_nat (bn_top b2)) + 1 ->
     (bn_top r <= bn_top b2)%nat ->
     Q tt s' X') ->
  bwp (bn_div_fixed_top ops RB3 RB4 RB1 RB2) s X Q.
Proof.
  intros s X Q Hs Ho Hrest Hn2 Htop2 Ht1 Ht2 HQ. unfold bn_div_fixed_top.
  set (b1 := getbn RB1 s) in *. set (b2 := getbn RB2 s) in *.
  pose proof (st_ok_getbn RB1 s Hs I) as Hb1. fold b1 in Hb1.
  pose proof (st_ok_getbn RB2 s Hs I) as Hb2. fold b2 in Hb2.
  (* [comment removed for export] *)
  apply bwp_bind. apply BN_CTX_start_spec; try assumption.
  intros s0 X0 F0 Hs0 Ho0 Hw0 Hfr0 Hu0.
  apply bwp_bind. apply (BN_CTX_get_spec s0 X0 0%nat); try assumption; try lia.
  intros sa Xa Hva _ Fa Hsa Hoa Hwa Hfra Hua.
  apply bwp_bind. apply (BN_CTX_get_spec sa Xa 1%nat); try assumption; try lia.
  intros sb Xb Hvb _ Fb Hsb Hob Hwb Hfrb Hub.
  apply bwp_bind. apply (BN_CTX_get_spec sb Xb 2%nat); try assumption; try lia.
  intros sc Xc Hvc _ Fc Hsc Hoc Hwc Hfrc Huc.
  assert (Eb1 : getbn RB1 sc = b1) by (rewrite Fc, Fb, Fa, F0 by congruence; reflexivity).
  assert (Eb2 : getbn RB2 sc = b2) by (rewrite Fc, Fb, Fa, F0 by congruence; reflexivity).
  assert (Eb5 : getbn RB5 sc = getbn RB5 s) by (rewrite Fc, Fb, Fa, F0 by congruence; reflexivity).
  assert (Hv0c : valid_ref (RPool 0) sc) by (eapply valid_ref_pool; [exact Hvc|lia]).
  assert (Hv1c : valid_ref (RPool 1) sc) by (eapply valid_ref_pool; [exact Hvc|lia]).
  (* [comment removed for export] *)
  apply bwp_bind. apply BN_copy_spec; try assumption; try exact I; [congruence|].
  intros sd1 X1. rewrite Eb2. cbv zeta. intros Hsd1 Etop1 Eneg1 _ Efn1 Hs1 Ho1.
  set (s1 := setbn (RPool 2) sd1 sc) in *.
  assert (Hv2_1 : valid_ref (RPool 2) s1) by (apply valid_ref_setbn; exact Hvc).
  (* [comment removed for export] *)
  assert (Hmag1 : bn_mag sd1 = bn_mag b2) by (unfold bn_mag; rewrite Etop1, Efn1; reflexivity).
  assert (Hnorm1 : bn_norm sd1).
  { right. rewrite Etop1. destruct Hn2 as [|Hn2]; [lia|].
    assert (E : nth (bn_top b2 - 1) (bn_buf sd1) 0 = nth (bn_top b2 - 1) (firstn (bn_top b2) (bn_buf sd1)) 0).
    { rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top b2 - 1) (bn_top b2)); [reflexivity|lia]. }
    rewrite E, Efn1, nth_firstn. destruct (Nat.ltb_spec (bn_top b2 - 1) (bn_top b2)); [exact Hn2|lia]. }
  apply bwp_bind. apply bn_left_align_spec; try assumption;
    [subst s1; rewrite getbn_setbn_same by assumption; exact Hnorm1
    |subst s1; rewrite getbn_setbn_same by assumption; lia|].
  intros sd2 sh. subst s1. rewrite getbn_setbn_same by assumption. cbv zeta.
  intros Hsh Hsd2 Etop2 Eneg2 Efl2 Emag2 Hd0 Hs2 Ho2. rewrite setbn_setbn_same in Hs2, Ho2 |- *.
  set (s2 := setbn (RPool 2) sd2 sc) in *.
  assert (Hv2_2 : valid_ref (RPool 2) s2) by (apply valid_ref_setbn; exact Hvc).
  (* [comment removed for export] *)
  apply bwp_bind. apply bwp_bind, bwp_get. subst s2. rewrite getbn_setbn_same by assumption.
  set (sd3 := bn_with_neg sd2 false).
  assert (Hsd3 : bn_ok sd3) by (destruct Hsd2 as (A1 & A2 & A3 & A4); unfold bn_ok, bn_dmax in *; subst sd3; cbn [bn_with_neg bn_buf bn_top bn_flags]; tauto).
  apply bwp_update; try assumption; [rewrite getbn_setbn_same by assumption; reflexivity|].
  rewrite setbn_setbn_same. intros Hs3 Ho3. set (s3 := setbn (RPool 2) sd3 sc) in *.
  assert (Hv2_3 : valid_ref (RPool 2) s3) by (apply valid_ref_setbn; exact Hvc).
  assert (Hv1_3 : valid_ref (RPool 1) s3) by (apply valid_ref_setbn; exact Hv1c).
  assert (Hv0_3 : valid_ref (RPool 0) s3) by (apply valid_ref_setbn; exact Hv0c).
  (* [comment removed for export] *)
  apply bwp_bind. apply bn_lshift_fixed_top_spec; try assumption; try exact I; [congruence| |].
  { subst s3. other. rewrite Eb1. unfold DMAX_MAX. lia. }
  intros sn1 X4. subst s3. other. rewrite Eb1. cbv zeta. intros Hsn1 Etsn1 Ensn1 _ Emsn1 Hs4 Ho4.
  set (s4 := setbn (RPool 1) sn1 (setbn (RPool 2) sd3 sc)) in *.
  assert (Hv2_4 : valid_ref (RPool 2) s4) by (apply valid_ref_setbn; exact Hv2_3).
  assert (Hv1_4 : valid_ref (RPool 1) s4) by (apply valid_ref_setbn; exact Hv1_3).
  assert (Hv0_4 : valid_ref (RPool 0) s4) by (apply valid_ref_setbn; exact Hv0_3).
  apply bwp_bind, bwp_get. apply bwp_bind, bwp_get.
  assert (Eg2 : getbn (RPool 2) s4 = sd3) by (subst s4; other; apply getbn_setbn_same; assumption).
  assert (Eg1 : getbn (RPool 1) s4 = sn1) by (subst s4; apply getbn_setbn_same; assumption).
  rewrite Eg2, Eg1. change (bn_top sd3) with (bn_top sd2). rewrite Etop2, Etop1.
  set (div_n := bn_top b2) in *.
  (* [comment removed for export] *)
  apply bwp_bind.
  assert (Hpad : forall (Q' : unit -> LS -> blocks -> Prop),
     (forall sn2 s5 X5, st_ok s5 -> own s5 X5 -> s5 = setbn (RPool 1) sn2 (setbn (RPool 2) sd3 sc) ->
        bn_ok sn2 -> bn_mag sn2 = bn_mag b1 * 2 ^ sh -> bn_top sn2 = Nat.max (bn_top b1 + 1) (div_n + 1) ->
        Q' tt s5 X5) ->
     bwp (if (bn_top sn1 <=? div_n)%nat
          then bbind ops (bn_wexpand ops (RPool 1) (div_n + 1))
                 (fun _ => bbind ops (bget ops (RPool 1))
                    (fun sn' => bset ops (RPool 1)
                       (mkBN (bn_d sn') (splice (bn_buf sn') (bn_top sn1) (repeat 0 (div_n - bn_top sn1 + 1)))
                             (div_n + 1) (bn_neg sn') (bn_flags sn'))))
          else bret ops tt) s4 X4 Q').
  { intros Q' HQ'. destruct (Nat.leb_spec (bn_top sn1) div_n) as [Hle|Hgt].
    - apply bwp_bind. apply bn_wexpand_spec; try assumption; [rewrite Eg1; exact Hsn1|unfold DMAX_MAX; lia|].
      intros sn' X5 Hexp Hs5 Ho5. rewrite Eg1 in Hexp. destruct Hexp as (E1 & E2 & E3 & E4 & Hsn' & E5 & E6).
      subst s4. rewrite setbn_setbn_same in Hs5, Ho5 |- *.
      set (s5 := setbn (RPool 1) sn' (setbn (RPool 2) sd3 sc)) in *.
      assert (Hv1_5 : valid_ref (RPool 1) s5) by (apply valid_ref_setbn; exact Hv1_3).
      apply bwp_bind, bwp_get. subst s5. rewrite getbn_setbn_same by assumption.
      destruct Hsn' as (A1 & A2 & A3 & A4). destruct Hsn1 as (B1 & B2 & B3 & B4). unfold bn_dmax in *.
      set (k := (div_n - bn_top sn1 + 1)%nat).
      assert (Hk : (bn_top sn1 + k = div_n + 1)%nat) by lia.
      set (sn2 := mkBN (bn_d sn') (splice (bn_buf sn') (bn_top sn1) (repeat 0 k)) (div_n + 1) (bn_neg sn') (bn_flags sn')).
      assert (L2 : length (bn_buf sn2) = length (bn_buf sn')).
      { subst sn2. cbn [bn_buf]. apply splice_length. rewrite repeat_length. lia. }
      assert (Hsn2 : bn_ok sn2).
      { unfold bn_ok, bn_dmax. rewrite L2. subst sn2. cbn [bn_buf bn_top bn_flags].
        split; [apply splice_limbs; [exact A1|apply limbs_repeat; exact limb_0]|]. repeat split; try assumption; lia. }
      apply bwp_update; try assumption; [rewrite getbn_setbn_same by assumption; apply bn_blocks_same; [reflexivity|exact L2]|].
      rewrite setbn_setbn_same. intros Hs6 Ho6. eapply HQ'; try eassumption; try reflexivity.
      + unfold bn_mag at 1. subst sn2. cbn [bn_buf bn_top]. rewrite <- Hk, firstn_pad_zeros by lia.
        rewrite lval_app, lval_repeat0, Z.mul_0_r, Z.add_0_r. rewrite <- Emsn1. unfold bn_mag.
        rewrite E4. destruct (Nat.leb_spec (div_n + 1) (length (bn_buf sn1))) as [Hfit|Hnf].
        * reflexivity.
        * rewrite firstn_app, firstn_firstn, Nat.min_id. rewrite firstn_length_le by lia.
          rewrite Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. reflexivity.
      + subst sn2. cbn [bn_top]. lia.
    - apply bwp_ret. eapply HQ'; try eassumption; try reflexivity. lia. }
  apply Hpad. clear Hpad. intros sn2 s5 X5 Hs5 Ho5 Es5 Hsn2 Emsn2 Etsn2.
  assert (Hv2_5 : valid_ref (RPool 2) s5) by (subst s5; apply valid_ref_setbn; exact Hv2_3).
  assert (Hv1_5 : valid_ref (RPool 1) s5) by (subst s5; apply valid_ref_setbn; exact Hv1_3).
  assert (Hv0_5 : valid_ref (RPool 0) s5) by (subst s5; apply valid_ref_setbn; exact Hv0_3).
  assert (Eg1_5 : getbn (RPool 1) s5 = sn2) by (subst s5; apply getbn_setbn_same; assumption).
  assert (Eg2_5 : getbn (RPool 2) s5 = sd3) by (subst s5; other; apply getbn_setbn_same; assumption).
  apply bwp_bind, bwp_get. rewrite Eg1_5. rewrite Etsn2.
  set (num_n := Nat.max (bn_top b1 + 1) (div_n + 1)) in *.
  set (loop := (num_n - div_n)%nat).
  assert (Hloop : (1 <= loop)%nat /\ num_n = (loop + div_n)%nat) by (subst loop num_n; lia).
  (* [comment removed for export] *)
  apply bwp_bind. apply bn_wexpand_spec; try assumption; try exact I; [apply st_ok_getbn; [assumption|exact I]|unfold DMAX_MAX; lia|].
  intros q1 X6 Hexp6 Hs6 Ho6. destruct Hexp6 as (Q1 & Q2 & Q3 & Q4 & Hq1 & Q5 & Q6).
  set (s6 := setbn RB3 q1 s5) in *.
  apply bwp_bind, bwp_get. apply bwp_bind, bwp_get.
  assert (Eg_b1 : getbn RB1 s6 = b1) by (subst s6 s5; other; exact Eb1).
  assert (Eg_b2 : getbn RB2 s6 = b2) by (subst s6 s5; other; exact Eb2).
  rewrite Eg_b1, Eg_b2.
  apply bwp_bind. apply bwp_bind, bwp_get. subst s6. rewrite getbn_setbn_same by (try assumption; exact I).
  set (q2 := mkBN (bn_d q1) (bn_buf q1) loop (xorb (bn_neg b1) (bn_neg b2)) (bn_flags q1)).
  assert (Hq2 : bn_ok q2).
  { destruct Hq1 as (A1 & A2 & A3 & A4). unfold bn_ok, bn_dmax in *. subst q2. cbn [bn_buf bn_top bn_flags]. repeat split; try assumption; lia. }
  apply bwp_update; try assumption; try exact I; [rewrite getbn_setbn_same by (try assumption; exact I); reflexivity|].
  rewrite setbn_setbn_same. intros Hs7 Ho7. set (s7 := setbn RB3 q2 s5) in *.
  assert (Hv0_7 : valid_ref (RPool 0) s7) by (subst s7; apply valid_ref_setbn; exact Hv0_5).
  assert (Hv1_7 : valid_ref (RPool 1) s7) by (subst s7; apply valid_ref_setbn; exact Hv1_5).
  (* [comment removed for export] *)
  apply bwp_bind. apply bn_wexpand_spec; try assumption; [apply st_ok_getbn; assumption|unfold DMAX_MAX; lia|].
  intros tm1 X8 Hexp8 Hs8 Ho8. destruct Hexp8 as (T1 & T2 & T3 & T4 & Htm1 & T5 & T6).
  set (s8 := setbn (RPool 0) tm1 s7) in *.
  assert (Hv0_8 : valid_ref (RPool 0) s8) by (subst s8; apply valid_ref_setbn; exact Hv0_7).
  assert (Hv1_8 : valid_ref (RPool 1) s8) by (subst s8; apply valid_ref_setbn; exact Hv1_7).
  apply bwp_bind, bwp_get. apply bwp_bind, bwp_get. apply bwp_bind, bwp_get.
  assert (Eg1_8 : getbn (RPool 1) s8 = sn2) by (subst s8 s7; other; exact Eg1_5).
  assert (Eg0_8 : getbn (RPool 0) s8 = tm1) by (subst s8; apply getbn_setbn_same; assumption).
  assert (Eg3_8 : getbn RB3 s8 = q2) by (subst s8 s7; other; apply getbn_setbn_same; [assumption|exact I]).
  rewrite Eg1_8, Eg0_8, Eg3_8.
  (* [comment removed for export] *)
  destruct Hsn2 as (N1 & N2 & N3 & N4). destruct Htm1 as (M1 & M2 & M3 & M4). destruct Hq1 as (R1 & R2 & R3 & R4).
  destruct Hsd2 as (D1 & D2 & D3 & D4). unfold bn_dmax in *.
  assert (Hd0' : nth (div_n - 1) (bn_buf sd3) 0 = nth (div_n - 1) (bn_buf sd2) 0) by reflexivity.
  assert (Hvge : Bp (div_n - 1) * 2 ^ 63 <= lval (firstn div_n (bn_buf sd3))).
  { change (bn_buf sd3) with (bn_buf sd2).
    set (l := firstn div_n (bn_buf sd2)). assert (Hl : limbs l) by (apply limbs_firstn; exact D1).
    assert (Hll : length l = div_n) by (apply firstn_length_le; lia).
    pose proof (nth_limb_val l (div_n - 1) Hl ltac:(lia)) as E.
    assert (En : nth (div_n - 1) l 0 = nth (div_n - 1) (bn_buf sd2) 0).
    { subst l. rewrite nth_firstn. destruct (Nat.ltb_spec (div_n - 1) div_n); [reflexivity|lia]. }
    rewrite En in E. rewrite Etop1 in Hd0. fold div_n in Hd0.
    pose proof (lval_nonneg _ (limbs_firstn (div_n - 1) l Hl)). pose proof (lval_nonneg _ (limbs_skipn (S (div_n - 1)) l Hl)).
    pose proof (Bp_pos (div_n - 1)). pose proof (Bp_pos (S (div_n - 1))). nia. }
  assert (HN0 : lval (firstn num_n (bn_buf sn2)) = bn_mag b1 * 2 ^ sh) by (rewrite <- Emsn2; unfold bn_mag; rewrite Etsn2; reflexivity).
  assert (Htopc : lval (slice (bn_buf sn2) loop div_n) < lval (firstn div_n (bn_buf sd3))).
  { apply (div_top_cond (bn_buf sn2) loop div_n (bn_top b1)); try assumption; try lia.
    destruct Hloop as [_ El]. rewrite <- El, HN0.
    pose proof (bn_mag_lt b1 Hb1). pose proof (bn_mag_nonneg b1 Hb1).
    assert (2 ^ sh <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
    assert (0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia). pose proof (Bp_pos (bn_top b1)). nia. }
  pose proof (div_loop_spec (bn_buf sd3) div_n loop num_n (nth (div_n - 1) (bn_buf sd3) 0)
                (if (div_n =? 1)%nat then 0 else nth (div_n - 2) (bn_buf sd3) 0)
                D1 ltac:(lia) ltac:(change (bn_buf sd3) with (bn_buf sd2); lia) (proj2 Hloop) eq_refl eq_refl
                ltac:(rewrite Hd0'; rewrite Etop1 in Hd0; exact Hd0)
                (bn_buf sn2) (bn_buf tm1) (bn_buf q2) N1 M1 R1 ltac:(lia) ltac:(lia) ltac:(subst q2; cbn [bn_buf]; lia) Htopc) as Hloopspec.
  cbv zeta in Hloopspec.
  destruct (div_loop (bn_buf sd3) div_n loop num_n _ _ loop 0 (bn_buf sn2, bn_buf tm1, bn_buf q2)) as [[snb tmb] rb].
  destruct Hloopspec as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  rewrite HN0 in L7, L8.
  (* [comment removed for export] *)
  apply bwp_bind. apply bwp_update; try assumption;
    [unfold bn_ok, bn_dmax; cbn [bn_with_buf bn_buf bn_top bn_flags]; rewrite L4; repeat split; try assumption; lia
    |rewrite Eg0_8; apply bn_blocks_same; [reflexivity|exact L4]|].
  intros Hs9 Ho9. set (s9 := setbn (RPool 0) (bn_with_buf tm1 tmb) s8) in *.
  assert (Hv1_9 : valid_ref (RPool 1) s9) by (subst s9; apply valid_ref_setbn; exact Hv1_8).
  assert (Eg3_9 : getbn RB3 s9 = q2) by (subst s9; other; exact Eg3_8).
  set (q3 := bn_with_buf q2 rb).
  assert (Hq3 : bn_ok q3).
  { unfold bn_ok, bn_dmax. subst q3 q2. cbn [bn_with_buf bn_buf bn_top bn_flags] in *. rewrite L6. repeat split; try assumption; lia. }
  apply bwp_bind. apply bwp_update; try assumption; try exact I;
    [rewrite Eg3_9; apply bn_blocks_same; [reflexivity|subst q3 q2; cbn [bn_with_buf bn_buf] in *; exact L6]|].
  intros Hs10 Ho10. set (s10 := setbn RB3 q3 s9) in *.
  assert (Hv1_10 : valid_ref (RPool 1) s10) by (subst s10; apply valid_ref_setbn; exact Hv1_9).
  assert (Eg1_10 : getbn (RPool 1) s10 = sn2) by (subst s10 s9; other; exact Eg1_8).
  set (sn3 := mkBN (bn_d sn2) snb div_n (bn_neg b1) (bn_flags sn2)).
  assert (Hsn3 : bn_ok sn3).
  { unfold bn_ok, bn_dmax. subst sn3. cbn [bn_buf bn_top bn_flags]. rewrite L2. repeat split; try assumption; lia. }
  apply bwp_bind. apply bwp_update; try assumption;
    [rewrite Eg1_10; apply bn_blocks_same; [reflexivity|subst sn3; cbn [bn_buf]; exact L2]|].
  intros Hs11 Ho11. set (s11 := setbn (RPool 1) sn3 s10) in *.
  assert (Hv1_11 : valid_ref (RPool 1) s11) by (subst s11; apply valid_ref_setbn; exact Hv1_10).
  assert (Eg1_11 : getbn (RPool 1) s11 = sn3) by (subst s11; apply getbn_setbn_same; assumption).
  (* [comment removed for export] *)
  apply bwp_bind. apply bn_rshift_fixed_top_spec; try assumption; try exact I; [congruence|rewrite Eg1_11; subst sn3; cbn [bn_top]; lia|].
  intros rm1 X12. rewrite Eg1_11. cbv zeta. intros Hrm1 Etrm Enrm _ Emrm Hs12 Ho12.
  set (s12 := setbn RB4 rm1 s11) in *.
  (* [comment removed for export] *)
  assert (Hctx12 : ctx_same (ls_ctx sc) (ls_ctx s12)).
  { subst s12 s11 s10 s9 s8 s7 s5. repeat (eapply ctx_same_trans; [|apply ctx_same_setbn]). apply ctx_same_refl. }
  apply BN_CTX_end_spec; try assumption.
  { eapply ctx_wf_same; [exact Hctx12|exact Hwc]. }
  { destruct Hctx12 as (_ & _ & _ & _ & _ & E & _). rewrite E. exact Hfrc. }
  intros s' Fend Hs' Ho' Hrest'.
  assert (V0 : 0 < bn_mag b2).
  { pose proof (bn_mag_ge b2 Hb2 Hn2 ltac:(lia)). pose proof (Bp_pos (bn_top b2 - 1)). lia. }
  assert (Hvmag : lval (firstn div_n (bn_buf sd3)) = bn_mag b2 * 2 ^ sh).
  { change (bn_buf sd3) with (bn_buf sd2). rewrite <- Hmag1, <- Emag2. unfold bn_mag. rewrite Etop2, Etop1. reflexivity. }
  rewrite Hvmag in L7, L8.
  destruct (div_values (bn_mag b1) (bn_mag b2) sh (bn_mag_nonneg b1 Hb1) V0 ltac:(lia)) as [DV1 DV2].
  apply HQ; try assumption.
  - rewrite Fend. subst s12 s11 s10 s9 s8 s7 s5. other. exact Eb1.
  - rewrite Fend. subst s12 s11 s10 s9 s8 s7 s5. other. exact Eb2.
  - rewrite Fend. subst s12 s11 s10 s9 s8 s7 s5. other. exact Eb5.
  - rewrite Fend. subst s12 s11 s10. other. rewrite getbn_setbn_same by (try assumption; exact I).
    unfold bn_mag. subst q3 q2. cbn [bn_with_buf bn_buf bn_top]. rewrite L7. exact DV1.
  - rewrite Fend. subst s12. rewrite getbn_setbn_same by (try assumption; exact I).
    rewrite Emrm. unfold bn_mag at 1. subst sn3. cbn [bn_buf bn_top]. rewrite L8. exact DV2.
  - rewrite Fend. subst s12 s11 s10. other. rewrite getbn_setbn_same by (try assumption; exact I). reflexivity.
  - rewrite Fend. subst s12. rewrite getbn_setbn_same by (try assumption; exact I). rewrite Enrm. reflexivity.
  - rewrite Fend. subst s12 s11 s10. other. rewrite getbn_setbn_same by (try assumption; exact I).
    subst q3 q2. cbn [bn_with_buf bn_top]. subst loop num_n. lia.
  - rewrite Fend. subst s12. rewrite getbn_setbn_same by (try assumption; exact I). rewrite Etrm. subst sn3. cbn [bn_top]. subst div_n. lia.
Qed.

Lemma BN_div_spec : forall s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> ctx_rest (ls_ctx s) ->
  bn_norm (getbn RB2 s) -> (1 <= bn_top (getbn RB2 s))%nat ->
  Z.of_nat (bn_top (getbn RB1 s)) <= 32000 -> Z.of_nat (bn_top (getbn RB2 s)) <= 32000 ->
  (forall s' X', st_ok s' -> own s' X' -> ctx_rest (ls_ctx s') ->
     getbn RB1 s' = getbn RB1 s -> getbn RB2 s' = getbn RB2 s -> getbn RB5 s' = getbn RB5 s ->
     let b1 := getbn RB1 s in let b2 := getbn RB2 s in
     let q := getbn RB3 s' in let r := getbn RB4 s' in
     bn_canon q -> bn_canon r ->
     bn_mag q = bn_mag b1 / bn_mag b2 -> bn_mag r = bn_mag b1 mod bn_mag b2 ->
     bn_neg q = (xorb (bn_neg b1) (bn_neg b2) && negb (bn_top q =? 0)%nat) ->
     bn_neg r = (bn_neg b1 && negb (bn_top r =? 0)%nat) ->
     Z.of_nat (bn_top q) + Z.of_nat (bn_top b2) <= Z.max (Z.of_nat (bn_top b1)) (Z.of_nat (bn_top b2)) + 1 ->
     (bn_top r <= bn_top b2)%nat ->
     Q tt s' X') ->
  bwp (BN_div ops RB3 RB4 RB1 RB2) s X Q.
Proof.
  intros s X Q Hs Ho Hrest Hn2 Htop2 Ht1 Ht2 HQ. unfold BN_div.
  apply bwp_bind, bwp_get. destruct (Nat.eqb_spec (bn_top (getbn RB2 s)) 0) as [|_]; [lia|].
  destruct Hn2 as [Hz|Hnz]; [lia|]. destruct (Z.eqb_spec (nth (bn_top (getbn RB2 s) - 1) (bn_buf (getbn RB2 s)) 0) 0) as [E|_]; [contradiction|].
  apply bwp_bind. apply bn_div_fixed_top_spec; try assumption; [right; exact Hnz|].
  intros s1 X1 Hs1 Ho1 Hr1 E1 E2 E5. cbv zeta. intros Mq Mr Nq Nr Tq Tr.
  (* [comment removed for export] *)
  apply bwp_bind. apply bwp_bind, bwp_get.
  destruct (bn_correct_top_ok (getbn RB3 s1) (st_ok_getbn RB3 s1 Hs1 I)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  apply bwp_update; try assumption; try exact I; [apply bn_blocks_same; [exact C6|rewrite C5; reflexivity]|].
  intros Hs2 Ho2. set (s2 := setbn RB3 (bn_correct_top_pure (getbn RB3 s1)) s1) in *.
  (* [comment removed for export] *)
  apply bwp_bind, bwp_get.
  assert (Eg4 : getbn RB4 s2 = getbn RB4 s1) by (subst s2; apply getbn_setbn_other; congruence).
  rewrite Eg4.
  destruct (bn_correct_top_ok (getbn RB4 s1) (st_ok_getbn RB4 s1 Hs1 I)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  apply bwp_update; try assumption; try exact I; [rewrite Eg4; apply bn_blocks_same; [exact D6|rewrite D5; reflexivity]|].
  intros Hs3 Ho3. set (s3 := setbn RB4 (bn_correct_top_pure (getbn RB4 s1)) s2) in *.
  assert (Ectx : ctx_same (ls_ctx s1) (ls_ctx s3)).
  { subst s3 s2. eapply ctx_same_trans; apply ctx_same_setbn. }
  assert (Hrest3 : ctx_rest (ls_ctx s3)).
  { destruct Hr1 as [W F]. split; [eapply ctx_wf_same; [exact Ectx|exact W]|].
    destruct Ectx as (_ & _ & _ & _ & _ & E & _). rewrite E. exact F. }
  assert (G3 : getbn RB3 s3 = bn_correct_top_pure (getbn RB3 s1)) by reflexivity.
  assert (G4 : getbn RB4 s3 = bn_correct_top_pure (getbn RB4 s1)) by reflexivity.
  apply HQ; try assumption; rewrite ?G3, ?G4; try assumption.
  - rewrite C3. exact Mq.
  - rewrite D3. exact Mr.
  - rewrite C8, Nq. reflexivity.
  - rewrite D8, Nr. reflexivity.
  - lia.
  - lia.
Qed.

End DivSpec.
