(** * BtItem6 — [gen_bitlen]'s output histogram meets the Kraft budget EXACTLY,
      and IS the leaf-length histogram, on both overflow branches.

    OWNER: an earlier development run.  The composition of BtPass1 (the clamped depth walk),
    BtLevels (level equations + telescope), BtAdjust (the repair chain) and
    BtPass2 (the redistribution): at [gen_bitlen]'s own call shape, with the
    parked-window package from BtCensus5 as the single structural premise.

    The output is stated POSITION-side (sums over the parked window); the
    symbol-side [bl_count]/[BlcOf]/[ValidLengths] forms follow in BtItem6b via
    the window census (every live symbol parks exactly once). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus1 BtCensus2 BtCensus3 BtCensus4 BtCensus5
  BtPass1 BtLevels BtAdjust BtPass2 GenBitlen KraftAdjust.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** The passes never touch frequencies *)

Lemma gb_pass1_fc : forall fuel k hp maxc maxlen base extra stree h t blc
                           ol sl ov,
  tr_fc (gb1_tree (gb_pass1 fuel k hp maxc maxlen base extra stree
                            h t blc ol sl ov))
  = tr_fc t.
Proof.
  induction fuel as [|f IH];
    intros k hp maxc maxlen base extra stree h t blc ol sl ov.
  - reflexivity.
  - cbn [gb_pass1].
    destruct (Z.leb HEAP_SIZE h); [reflexivity|].
    destruct (Z.ltb maxc (hp h)); rewrite IH; reflexivity.
Qed.

Lemma gb_pass2_fc : forall fuel hp maxc t blc bits n h ol,
  tr_fc (fst (gb_pass2 fuel hp maxc t blc bits n h ol)) = tr_fc t.
Proof.
  induction fuel as [|f IH]; intros hp maxc t blc bits n h ol.
  - reflexivity.
  - cbn [gb_pass2].
    destruct (Z.eqb n 0).
    + destruct (Z.leb bits 1); [reflexivity | apply IH].
    + destruct (Z.ltb maxc (hp (h - 1))); [apply IH|].
      destruct (Z.eqb (t_len t (hp (h - 1))) bits); [apply IH|].
      rewrite IH. reflexivity.
Qed.

(** ** The histogram total is the leaf count

    Both sides count the window's leaves: the histogram slices them by
    length, and every leaf's length lands in [1 .. M]. *)
Lemma blc_total : forall (maxc1 M : Z) (hp3 : zarr) (hmaxf : Z)
                         (t2 : Tree) (blc1 : zarr),
  1 <= M <= 15 ->
  (forall b, 0 <= b <= 15 ->
   blc1 b = BtPass2.hist maxc1 hp3 t2 b (hmaxf + 1)
              (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))) ->
  (forall p, hmaxf + 1 <= p < HEAP_SIZE -> hp3 p <= maxc1 ->
   1 <= t_len t2 (hp3 p) <= M) ->
  hmaxf + 1 <= HEAP_SIZE ->
  wsum blc1 1 (Z.to_nat M)
  = BtPass2.lcnt maxc1 hp3 t2 (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1))).
Proof.
  intros maxc1 M hp3 hmaxf t2 blc1 HM Hblc Hrng Hwin.
  rewrite (wsum_ext blc1
             (fun b => BtPass2.hist maxc1 hp3 t2 b (hmaxf + 1)
                         (Z.to_nat (HEAP_SIZE - (hmaxf + 1))))
             1 (Z.to_nat M))
    by (intros b Hb; apply Hblc; rewrite Z2Nat.id in Hb by lia; lia).
  unfold BtPass2.hist, BtPass2.lcnt.
  rewrite (wsum_swap
             (fun b p => ind ((hp3 p <=? maxc1)
                              && (Z.eqb (t_len t2 (hp3 p)) b)))
             1 (Z.to_nat M)
             (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))).
  apply wsum_ext. intros p Hp.
  rewrite Z2Nat.id in Hp by lia.
  destruct (Z.leb (hp3 p) maxc1) eqn:El.
  - apply Z.leb_le in El.
    cbn [andb ind].
    assert (Hr : 1 <= t_len t2 (hp3 p) <= M) by (apply Hrng; [lia | exact El]).
    rewrite (wsum_ext
               (fun b => ind (Z.eqb (t_len t2 (hp3 p)) b))
               (fun b => ind (Z.eqb b (t_len t2 (hp3 p))))
               1 (Z.to_nat M))
      by (intros b _; rewrite (Z.eqb_sym (t_len t2 (hp3 p)) b); reflexivity).
    apply wsum_ind_eqb_one.
    rewrite Z2Nat.id by lia. lia.
  - cbn [andb ind].
    apply wsum_zero.
Qed.

Print Assumptions gb_pass1_fc.
Print Assumptions gb_pass2_fc.
Print Assumptions blc_total.

(** ** THE COMPOSITION at [gen_bitlen]'s call shape *)

Theorem gen_bitlen_out :
  forall k s1 elems maxc1 M t1 tf hp3 hmaxf ndf hlen1,
  BtParked elems maxc1 t1 tf hp3 hmaxf ndf ->
  1 <= M <= 15 ->
  0 <= hmaxf ->
  sd_max_length k = M ->
  ts_heap s1 = hp3 ->
  ts_heapmax s1 = hmaxf ->
  ts_trees s1 k = tf ->
  ts_maxcode s1 k = maxc1 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s1 b = 0) ->
  ndf - elems = hlen1 - 1 ->
  2 <= hlen1 ->
  4 * (hlen1 - 1) < 2 ^ M ->
  zksum M (ts_blcount (gen_bitlen k s1)) = 2 ^ M
  /\ (forall b, 0 <= b <= 15 ->
      ts_blcount (gen_bitlen k s1) b
      = BtPass2.hist maxc1 hp3 (ts_trees (gen_bitlen k s1) k) b
          (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1))))
  /\ (forall b, b < 1 \/ M < b -> ts_blcount (gen_bitlen k s1) b = 0)
  /\ (forall p, hmaxf + 1 <= p < HEAP_SIZE -> hp3 p <= maxc1 ->
      1 <= t_len (ts_trees (gen_bitlen k s1) k) (hp3 p) <= M)
  /\ (forall y, pcount hp3 hmaxf y = 0 ->
      tr_dl (ts_trees (gen_bitlen k s1) k) y = tr_dl t1 y)
  /\ (forall i, t_freq (ts_trees (gen_bitlen k s1) k) i = t_freq tf i).
Proof.
  intros k s1 elems maxc1 M t1 tf hp3 hmaxf ndf hlen1
         Hpk HM Hmf0 EM Ehp Ehm Etf Emc Hblout Ecen Hh2 HK.
  pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk) as Hwlt.
  pose proof (bp_hmax _ _ _ _ _ _ _ Hpk) as Hhm.
  pose proof (bp_root _ _ _ _ _ _ _ Hpk) as Hroot.
  unfold gen_bitlen.
  rewrite EM, Ehp, Ehm, Etf, Emc, Hroot.
  set (blc0 := arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s1)) in *.
  assert (Hblc0 : forall b, blc0 b = 0).
  { intro b. unfold blc0.
    destruct (Z_le_gt_dec 0 b) as [Hb0|Hb0].
    - destruct (Z_le_gt_dec b 15) as [Hb15|Hb15].
      + apply arr_zero_in.
        change (Z.of_nat (Z.to_nat MAX_BITS + 1)) with 16. lia.
      + rewrite arr_zero_out
          by (change (Z.of_nat (Z.to_nat MAX_BITS + 1)) with 16; lia).
        apply Hblout. lia.
    - rewrite arr_zero_out
        by (change (Z.of_nat (Z.to_nat MAX_BITS + 1)) with 16; lia).
      apply Hblout. lia. }
  pose proof (pass1_entry elems maxc1 M t1 tf hp3 hmaxf ndf Hpk blc0 Hblc0)
    as Hinv0.
  pose proof (pass1_walk elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM Hmf0
                k (sd_extra_base k) (sd_extra k) (sd_stree k)
                (Z.to_nat HEAP_SIZE + 1) (hmaxf + 1)
                (t_setlen tf (ndf - 1) 0) blc0
                (ts_optlen s1) (ts_statlen s1) 0
                ltac:(lia)
                ltac:(rewrite Nat2Z.inj_add, Z2Nat.id
                        by (unfold HEAP_SIZE; lia);
                      change (Z.of_nat 1) with 1; lia)
                Hinv0) as Hw1.
  destruct (gb_pass1 (Z.to_nat HEAP_SIZE + 1) k hp3 maxc1 M
              (sd_extra_base k) (sd_extra k) (sd_stree k) (hmaxf + 1)
              (t_setlen tf (ndf - 1) 0) blc0
              (ts_optlen s1) (ts_statlen s1) 0)
    as [[[[t2 blc1] ol1] sl1] ov] eqn:E1.
  pose proof Hw1 as Hfin. clear Hw1.
  pose proof (pass1_kraft elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM
                t2 blc1 ov Hfin) as [Hzk [Hov [HbM [HW0 HV0]]]].
  set (V := VIc elems hp3 hmaxf t2 M) in *.
  set (W := VIc elems hp3 hmaxf t2 (M - 1)) in *.
  (* shared facts *)
  assert (HNWpos : 0 <= HEAP_SIZE - (hmaxf + 1)) by lia.
  assert (Hrng1 : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
                  1 <= t_len t2 (hp3 p) <= M)
    by (intros p Hp; exact (p1_rng _ _ _ _ _ _ _ _ _ _ Hfin p Hp)).
  assert (Hblc1 : forall b, 0 <= b <= 15 ->
                  blc1 b = BtPass2.hist maxc1 hp3 t2 b (hmaxf + 1)
                             (Z.to_nat (HEAP_SIZE - (hmaxf + 1))))
    by (intros b Hb; exact (p1_blc _ _ _ _ _ _ _ _ _ _ Hfin b Hb)).
  assert (Hz1 : forall b, b < 1 \/ M < b -> blc1 b = 0).
  { intros b [Hb|Hb].
    - exact (p1_zero _ _ _ _ _ _ _ _ _ _ Hfin b (or_introl Hb)).
    - destruct (Z_le_gt_dec b 15) as [Hb15|Hb15].
      + exact (lv_blc_high elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM
                 t2 blc1 ov Hfin b (conj Hb Hb15)).
      + assert (Hb15' : 15 < b) by lia.
        exact (p1_zero _ _ _ _ _ _ _ _ _ _ Hfin b (or_intror Hb15')). }
  assert (Hble : forall b, 0 <= b <= 15 ->
                 0 <= blc1 b <= 2 * (hlen1 - 1)).
  { intros b Hb. rewrite (Hblc1 b Hb).
    unfold BtPass2.hist.
    split; [apply wsum_nonneg; intros i _; apply ind_0_1|].
    pose proof (wsum_ind_ub
      (fun p => (hp3 p <=? maxc1) && (Z.eqb (t_len t2 (hp3 p)) b))
      (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))) as HB.
    rewrite Z2Nat.id in HB by lia. lia. }
  assert (Hp1out : forall y, pcount hp3 hmaxf y = 0 ->
                   tr_dl t2 y = tr_dl t1 y).
  { intros y Hy.
    rewrite (p1_out _ _ _ _ _ _ _ _ _ _ Hfin y Hy).
    assert (Hyr : y <> ndf - 1).
    { intro He. subst y.
      pose proof (pcount_member hp3 hmaxf hmaxf ltac:(lia)) as Hm.
      rewrite Hroot in Hm. lia. }
    unfold t_setlen. cbn [tr_dl]. rewrite zset_other by exact Hyr.
    apply (bp_dlf _ _ _ _ _ _ _ Hpk y Hy). }
  assert (Hfc1 : tr_fc t2 = tr_fc tf).
  { pose proof (gb_pass1_fc (Z.to_nat HEAP_SIZE + 1) k hp3 maxc1 M
                  (sd_extra_base k) (sd_extra k) (sd_stree k) (hmaxf + 1)
                  (t_setlen tf (ndf - 1) 0) blc0
                  (ts_optlen s1) (ts_statlen s1) 0) as HF.
    rewrite E1 in HF. cbn [gb1_tree] in HF. exact HF. }
  destruct (Z.eqb ov 0) eqn:Eov.
  - (* no overflow: the pass-1 histogram already lands on the budget *)
    apply Z.eqb_eq in Eov.
    assert (HV : V = 0) by lia.
    unfold set_statlen, set_optlen, set_blcount, set_tree, set_trees.
    cbn [ts_blcount ts_trees].
    rewrite Z.eqb_refl.
    split; [|split; [|split; [|split; [|split]]]].
    + lia.
    + exact Hblc1.
    + exact Hz1.
    + intros p Hp _. apply Hrng1. exact Hp.
    + exact Hp1out.
    + intro i. unfold t_freq. rewrite Hfc1. reflexivity.
  - (* overflow: adjust exactly, then redistribute exactly *)
    apply Z.eqb_neq in Eov.
    assert (HV1 : 1 <= V) by lia.
    assert (Hovle : ov <= 2 * (hlen1 - 1)).
    { rewrite (p1_ov _ _ _ _ _ _ _ _ _ _ Hfin).
      pose proof (wsum_ind_ub
        (fun p => Z.eqb (t_len t2 (t_dad tf (hp3 p))) M)
        (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))) as HB.
      rewrite Z2Nat.id in HB by lia. lia. }
    assert (HVle : V <= hlen1 - 1) by lia.
    replace (Z.to_nat ov + 1)%nat with (S (Z.to_nat ov)) by lia.
    rewrite Hov.
    set (K := 4 * (hlen1 - 1)) in *.
    assert (Hbnd : forall b, 0 <= blc1 b <= K - 2 * V).
    { intro b.
      destruct (Z_le_gt_dec 0 b) as [Hb0|Hb0];
        [destruct (Z_le_gt_dec b 15) as [Hb15|Hb15]|].
      - pose proof (Hble b ltac:(lia)). unfold K. lia.
      - rewrite (Hz1 b) by lia. unfold K. lia.
      - rewrite (Hz1 b) by lia. unfold K. lia. }
    assert (Hfuel : 1 <= V <= Z.of_nat (Z.to_nat (2 * V)))
      by (rewrite Z2Nat.id by lia; lia).
    pose proof (adjust_exact (Z.to_nat (2 * V)) M K blc1 V HM
                  ltac:(unfold K; lia) Hfuel Hzk ltac:(lia) Hz1 Hbnd)
      as Hzk2.
    destruct (adjust_facts (Z.to_nat (2 * V)) M K blc1 V HM
                ltac:(unfold K; lia) Hfuel Hzk ltac:(lia) Hz1 Hbnd)
      as [Hnn2 [Hz2 Hsum2]].
    set (blc2 := gb_adjust (S (Z.to_nat (2 * V))) M blc1 (2 * V)) in *.
    (* the total leaf balance survives the adjust *)
    assert (Htot : BtPass2.lcnt maxc1 hp3 t2 (hmaxf + 1)
                     (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))
                   = BtPass2.bsumr blc2 (Z.to_nat M) 1).
    { rewrite (BtPass2.bsumr_is_wsum blc2).
      rewrite Hsum2.
      symmetry.
      apply (blc_total maxc1 M hp3 hmaxf t2 blc1 HM Hblc1); [|lia].
      intros p Hp _. apply Hrng1. exact Hp. }
    pose proof (pass2_entry elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM
                  t2 blc2 Hnn2) as Hq0.
    pose proof (pass2_walk elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM
                  t2 blc2 Hnn2 Htot
                  (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)%nat
                  M (blc2 M) HEAP_SIZE t2 ol1
                  ltac:(rewrite !Nat2Z.inj_add, Nat2Z.inj_mul, !Z2Nat.id
                          by (unfold HEAP_SIZE, MAX_BITS; lia);
                        change (Z.of_nat 2) with 2;
                        change (Z.of_nat 4) with 4;
                        unfold HEAP_SIZE, MAX_BITS in *; lia)
                  Hq0) as Hw2.
    destruct (gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                hp3 maxc1 t2 blc2 M (blc2 M) HEAP_SIZE ol1)
      as [t3 ol2] eqn:E2.
    destruct Hw2 as [h' Hfin2].
    destruct (pass2_exit elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM
                t2 blc2 Hrng1 Htot h' t3 Hfin2)
      as [Hhist3 [Hrng3 [Hint3 Hout3]]].
    unfold set_statlen, set_optlen, set_blcount, set_tree, set_trees.
    cbn [ts_blcount ts_trees].
    rewrite Z.eqb_refl.
    assert (Hfc2 : tr_fc t3 = tr_fc t2).
    { pose proof (gb_pass2_fc
                    (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                    hp3 maxc1 t2 blc2 M (blc2 M) HEAP_SIZE ol1) as HF.
      rewrite E2 in HF. exact HF. }
    split; [|split; [|split; [|split; [|split]]]].
    + exact Hzk2.
    + intros b Hb.
      destruct (Z_le_gt_dec b 0) as [Hb0|Hb0].
      * assert (Hbe : b = 0) by lia. subst b.
        rewrite (Hz2 0 ltac:(lia)).
        symmetry.
        unfold BtPass2.hist.
        transitivity (wsum (fun _ : Z => 0) (hmaxf + 1)
                        (Z.to_nat (HEAP_SIZE - (hmaxf + 1))));
          [|apply wsum_zero].
        apply wsum_ext. intros p Hp.
        rewrite Z2Nat.id in Hp by lia.
        destruct (Z.leb (hp3 p) maxc1) eqn:El; [|reflexivity].
        apply Z.leb_le in El.
        assert (1 <= t_len t3 (hp3 p) <= M)
          by (apply Hrng3; [lia | exact El]).
        replace (Z.eqb (t_len t3 (hp3 p)) 0) with false
          by (symmetry; apply Z.eqb_neq; lia).
        rewrite andb_false_r. reflexivity.
      * destruct (Z_le_gt_dec b M) as [HbM'|HbM'].
        -- symmetry. exact (Hhist3 b ltac:(lia)).
        -- rewrite (Hz2 b ltac:(lia)).
           symmetry.
           unfold BtPass2.hist.
           transitivity (wsum (fun _ : Z => 0) (hmaxf + 1)
                           (Z.to_nat (HEAP_SIZE - (hmaxf + 1))));
             [|apply wsum_zero].
           apply wsum_ext. intros p Hp.
           rewrite Z2Nat.id in Hp by lia.
           destruct (Z.leb (hp3 p) maxc1) eqn:El; [|reflexivity].
           apply Z.leb_le in El.
           assert (1 <= t_len t3 (hp3 p) <= M)
             by (apply Hrng3; [lia | exact El]).
           replace (Z.eqb (t_len t3 (hp3 p)) b) with false
             by (symmetry; apply Z.eqb_neq; lia).
           rewrite andb_false_r. reflexivity.
    + exact Hz2.
    + exact Hrng3.
    + intros y Hy. rewrite (Hout3 y Hy). apply Hp1out. exact Hy.
    + intro i. unfold t_freq. rewrite Hfc2, Hfc1. reflexivity.
Qed.

Print Assumptions gen_bitlen_out.
