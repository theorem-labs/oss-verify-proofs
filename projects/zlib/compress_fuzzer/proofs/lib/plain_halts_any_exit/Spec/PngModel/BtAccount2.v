(** * BtAccount2 — [gen_bitlen] computes [opt_len]/[static_len] as the
      frequency-weighted length sums of its OUTPUT tree.

    OWNER: an earlier development run.  Composition of BtAccount's two walks at [gen_bitlen]'s
    call shape, re-deriving the adjust-side conditions exactly as
    BtItem6.gen_bitlen_out does (kept additive: that theorem is landed and
    consumed, so it is not edited).

    The recombination is pointwise: the pass-1 term counts
    [freq * (len_p1 + xbits)] and the pass-2 correction adds
    [freq * (len_final - len_p1)]; their sum is the final term. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus1 BtCensus2 BtCensus3 BtCensus4 BtCensus5
  BtPass1 BtLevels BtAdjust BtPass2 BtItem6 BtItem6b BtAccount BuildTree
  GenBitlen HuffGenCodes KraftAdjust.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Lemma ol_statlen : forall v s, ts_optlen (set_statlen v s) = ts_optlen s.
Proof. reflexivity. Qed.
Lemma ol_optlen : forall v s, ts_optlen (set_optlen v s) = v.
Proof. reflexivity. Qed.
Lemma sl_statlen : forall v s, ts_statlen (set_statlen v s) = v.
Proof. reflexivity. Qed.

Theorem gen_bitlen_account :
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
  ts_optlen s1 = u64 (ts_optlen s1) ->
  ts_statlen s1 = u64 (ts_statlen s1) ->
  ts_optlen (gen_bitlen k s1)
  = u64 (ts_optlen s1
         + wsum (olterm maxc1 tf hp3 (sd_extra_base k) (sd_extra k)
                        (ts_trees (gen_bitlen k s1) k))
                (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1))))
  /\ ts_statlen (gen_bitlen k s1)
     = match sd_stree k with
       | None => ts_statlen s1
       | Some st =>
           u64 (ts_statlen s1
                + wsum (slterm maxc1 tf hp3 (sd_extra_base k) (sd_extra k) st)
                       (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1))))
       end.
Proof.
  intros k s1 elems maxc1 M t1 tf hp3 hmaxf ndf hlen1
         Hpk HM Hmf0 EM Ehp Ehm Etf Emc Hblout Ecen Hh2 HK Holu Hslu.
  pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk) as Hwlt.
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
  pose proof (acc_entry elems maxc1 M t1 tf hp3 hmaxf ndf Hpk
                (sd_extra_base k) (sd_extra k) (sd_stree k)
                (ts_optlen s1) (ts_statlen s1) Holu Hslu blc0 Hblc0)
    as Hacc0.
  pose proof (acc_walk elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM Hmf0
                k (sd_extra_base k) (sd_extra k) (sd_stree k)
                (ts_optlen s1) (ts_statlen s1)
                (Z.to_nat HEAP_SIZE + 1) (hmaxf + 1)
                (t_setlen tf (ndf - 1) 0) blc0
                (ts_optlen s1) (ts_statlen s1) 0
                ltac:(lia)
                ltac:(rewrite Nat2Z.inj_add, Z2Nat.id
                        by (unfold HEAP_SIZE; lia);
                      change (Z.of_nat 1) with 1; lia)
                Hacc0) as Hw1.
  destruct (gb_pass1 (Z.to_nat HEAP_SIZE + 1) k hp3 maxc1 M
              (sd_extra_base k) (sd_extra k) (sd_stree k) (hmaxf + 1)
              (t_setlen tf (ndf - 1) 0) blc0
              (ts_optlen s1) (ts_statlen s1) 0)
    as [[[[t2 blc1] ol1] sl1] ov] eqn:E1.
  destruct Hw1 as [Hfin Hfc Hol1 Hsl1].
  pose proof (pass1_kraft elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM
                t2 blc1 ov Hfin) as [Hzk [Hov [HbM [HW0 HV0]]]].
  set (V := VIc elems hp3 hmaxf t2 M) in *.
  set (W := VIc elems hp3 hmaxf t2 (M - 1)) in *.
  destruct (Z.eqb ov 0) eqn:Eov.
  - (* no overflow: the pass-1 sums ARE the answer *)
    rewrite ol_statlen, ol_optlen, sl_statlen.
    cbn [ts_trees set_statlen set_optlen set_blcount set_tree set_trees].
    rewrite Z.eqb_refl.
    split; [exact Hol1 | exact Hsl1].
  - (* overflow: the correction walk rides on top *)
    apply Z.eqb_neq in Eov.
    assert (HV1 : 1 <= V) by lia.
    (* the adjust side conditions, exactly as in gen_bitlen_out *)
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
      pose proof (bp_hmax _ _ _ _ _ _ _ Hpk) as Hhm.
      split; [apply wsum_nonneg; intros i _; apply ind_0_1|].
      pose proof (wsum_ind_ub
        (fun p => (hp3 p <=? maxc1) && (Z.eqb (t_len t2 (hp3 p)) b))
        (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))) as HB.
      rewrite Z2Nat.id in HB by lia. lia. }
    assert (Hovle : ov <= 2 * (hlen1 - 1)).
    { rewrite (p1_ov _ _ _ _ _ _ _ _ _ _ Hfin).
      pose proof (bp_hmax _ _ _ _ _ _ _ Hpk) as Hhm.
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
    destruct (adjust_facts (Z.to_nat (2 * V)) M K blc1 V HM
                ltac:(unfold K; lia) Hfuel Hzk ltac:(lia) Hz1 Hbnd)
      as [Hnn2 [Hz2 Hsum2]].
    set (blc2 := gb_adjust (S (Z.to_nat (2 * V))) M blc1 (2 * V)) in *.
    assert (Htot : BtPass2.lcnt maxc1 hp3 t2 (hmaxf + 1)
                     (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))
                   = BtPass2.bsumr blc2 (Z.to_nat M) 1).
    { rewrite (BtPass2.bsumr_is_wsum blc2).
      rewrite Hsum2.
      symmetry.
      apply (blc_total maxc1 M hp3 hmaxf t2 blc1 HM Hblc1); [|lia].
      intros p Hp _. apply Hrng1. exact Hp. }
    assert (Hol1u : ol1 = u64 ol1)
      by (rewrite Hol1; unfold u64; rewrite Z.mod_mod by lia; reflexivity).
    assert (Hfc2 : forall x, t_freq t2 x = t_freq tf x) by exact Hfc.
    pose proof (acc2_entry elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM
                  t2 blc2 Hnn2 ol1 Hol1u Hfc2) as Hq0.
    pose proof (acc2_walk elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM
                  t2 blc2 Hnn2 Htot ol1
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
    destruct Hw2 as [h' Hacc2].
    destruct Hacc2 as [Hinv2 Hfc3 Hol2].
    rewrite ol_statlen, ol_optlen, sl_statlen.
    cbn [ts_trees set_statlen set_optlen set_blcount set_tree set_trees].
    rewrite Z.eqb_refl.
    split; [|exact Hsl1].
    (* extend the correction window to the full one: no leaves below h' *)
    pose proof (q2_h _ _ _ _ _ _ _ _ _ _ Hinv2) as Hh'.
    pose proof (q2_bal _ _ _ _ _ _ _ _ _ _ Hinv2) as Hbal2.
    pose proof (q2_lo _ _ _ _ _ _ _ _ _ _ Hinv2) as Hlo2.
    assert (Hsplit : Z.to_nat (HEAP_SIZE - (hmaxf + 1))
                     = (Z.to_nat (h' - (hmaxf + 1))
                        + Z.to_nat (HEAP_SIZE - h'))%nat)
      by (rewrite <- Z2Nat.inj_add by lia; f_equal; lia).
    assert (Hlow0 : BtPass2.lcnt maxc1 hp3 t2 (hmaxf + 1)
                      (Z.to_nat (h' - (hmaxf + 1))) = 0).
    { pose proof Htot as Ht.
      rewrite Hsplit in Ht.
      unfold BtPass2.lcnt in *.
      rewrite wsum_app in Ht.
      rewrite Z2Nat.id in Ht by lia.
      replace (hmaxf + 1 + (h' - (hmaxf + 1))) with h' in Ht by lia.
      assert (Hbs : BtPass2.bsumr blc2 (Z.to_nat M) 1
                    = blc2 1 + BtPass2.bsumr blc2 (Z.to_nat (M - 1)) (1 + 1)).
      { replace (Z.to_nat M) with (S (Z.to_nat (M - 1)))
          by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
        cbn [BtPass2.bsumr]. reflexivity. }
      unfold BtPass2.lcnt in Hbal2. lia. }
    assert (Hnoleaf : forall p, hmaxf + 1 <= p < h' ->
            (hp3 p <=? maxc1) = false).
    { intros p Hp.
      destruct (Z.leb (hp3 p) maxc1) eqn:E; [|reflexivity].
      exfalso.
      pose proof (wsum_one_point (fun q => ind (hp3 q <=? maxc1))
                    (hmaxf + 1) (Z.to_nat (h' - (hmaxf + 1))) p) as HP.
      cbn beta in HP.
      rewrite E in HP. cbn [ind] in HP.
      unfold BtPass2.lcnt in Hlow0.
      assert (1 <= wsum (fun q => ind (hp3 q <=? maxc1)) (hmaxf + 1)
                     (Z.to_nat (h' - (hmaxf + 1)))); [|lia].
      apply HP.
      - intros i _. apply ind_0_1.
      - rewrite Z2Nat.id by lia. lia. }
    rewrite Hol2, Hol1, u64_add_l.
    f_equal.
    rewrite <- Z.add_assoc.
    f_equal.
    (* both sums live on the full window *)
    assert (Hext : wsum (corrterm maxc1 tf hp3 t2 t3) h'
                        (Z.to_nat (HEAP_SIZE - h'))
                   = wsum (corrterm maxc1 tf hp3 t2 t3) (hmaxf + 1)
                          (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))).
    { symmetry.
      rewrite Hsplit, wsum_app.
      rewrite Z2Nat.id by lia.
      replace (hmaxf + 1 + (h' - (hmaxf + 1))) with h' by lia.
      assert (Hz0 : wsum (corrterm maxc1 tf hp3 t2 t3) (hmaxf + 1)
                         (Z.to_nat (h' - (hmaxf + 1))) = 0).
      { transitivity (wsum (fun _ : Z => 0) (hmaxf + 1)
                        (Z.to_nat (h' - (hmaxf + 1))));
          [|apply wsum_zero].
        apply wsum_ext. intros p Hp.
        rewrite Z2Nat.id in Hp by lia.
        unfold corrterm.
        rewrite (Hnoleaf p ltac:(lia)). cbn [ind]. lia. }
      rewrite Hz0. lia. }
    rewrite Hext.
    rewrite <- wsum_add.
    apply wsum_ext. intros p Hp.
    rewrite Z2Nat.id in Hp by lia.
    unfold olterm, corrterm.
    destruct (Z.leb (hp3 p) maxc1) eqn:El; cbn [ind]; lia.
Qed.



(** ** [bt_force2]'s counters, and the [build_tree]-level composition *)

Definition f2_ol (r : Tree * zarr * zarr * Z * Z * Z * Z) : Z :=
  match r with (_, _, _, _, _, ol, _) => ol end.
Definition f2_sl (r : Tree * zarr * zarr * Z * Z * Z * Z) : Z :=
  match r with (_, _, _, _, _, _, sl) => sl end.

Lemma u64_sub_l : forall a b, u64 (u64 a - b) = u64 (a - b).
Proof.
  intros a b. unfold u64.
  rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

(** The forced trips decrement [opt_len] once each; [static_len] loses the
    forced nodes' static lengths (untouched when there is no static tree). *)
Lemma bt_force2_account : forall stree t hp dep hlen maxc ol sl,
  0 <= hlen ->
  (hlen >= 2
   /\ f2_ol (bt_force2 3%nat stree t hp dep hlen maxc ol sl) = ol
   /\ f2_sl (bt_force2 3%nat stree t hp dep hlen maxc ol sl) = sl)
  \/ (hlen = 1
      /\ f2_ol (bt_force2 3%nat stree t hp dep hlen maxc ol sl)
         = u64 (ol - 1)
      /\ f2_sl (bt_force2 3%nat stree t hp dep hlen maxc ol sl)
         = match stree with
           | None => sl
           | Some st => u64 (sl - t_len st (if Z.ltb maxc 2
                                            then maxc + 1 else 0))
           end)
  \/ (hlen = 0
      /\ f2_ol (bt_force2 3%nat stree t hp dep hlen maxc ol sl)
         = u64 (ol - 2)).
Proof.
  intros stree t hp dep hlen maxc ol sl Hh.
  destruct (Z_le_gt_dec 2 hlen) as [H2|H2].
  { left. split; [lia|].
    cbn [bt_force2].
    replace (Z.leb 2 hlen) with true by (symmetry; apply Z.leb_le; lia).
    split; reflexivity. }
  destruct (Z.eq_dec hlen 1) as [->|H1].
  { right. left. split; [reflexivity|].
    cbn [bt_force2].
    replace (Z.leb 2 1) with false by reflexivity.
    replace (Z.leb 2 (1 + 1)) with true by reflexivity.
    split; [reflexivity|].
    destruct stree as [st|]; reflexivity. }
  assert (H0 : hlen = 0) by lia. subst hlen.
  right. right. split; [reflexivity|].
  cbn [bt_force2].
  replace (Z.leb 2 0) with false by reflexivity.
  replace (Z.leb 2 (0 + 1)) with false by reflexivity.
  replace (Z.leb 2 (0 + 1 + 1)) with true by reflexivity.
  cbn [f2_ol].
  rewrite u64_sub_l. f_equal. lia.
Qed.

Lemma s1_optlen : forall k maxc1 stf ol1 sl1 s,
  ts_optlen (s1_of k maxc1 stf ol1 sl1 s) = ol1.
Proof. reflexivity. Qed.
Lemma s1_statlen : forall k maxc1 stf ol1 sl1 s,
  ts_statlen (s1_of k maxc1 stf ol1 sl1 s) = sl1.
Proof. reflexivity. Qed.
Lemma ol_settree : forall k t s, ts_optlen (set_tree k t s) = ts_optlen s.
Proof. reflexivity. Qed.
Lemma sl_settree : forall k t s, ts_statlen (set_tree k t s) = ts_statlen s.
Proof. reflexivity. Qed.

(** The full [build_tree] accounting: the output counters are the entry
    counters plus the frequency-weighted length sums of the OUTPUT tree,
    minus one [opt_len] tick (and the static length) per forced code. *)
Theorem build_tree_account :
  forall k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf,
  3 <= sd_elems k <= L_CODES ->
  1 <= sd_max_length k <= 15 ->
  4 * (hlen1 - 1) < 2 ^ sd_max_length k ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  ol1 = u64 ol1 -> sl1 = u64 sl1 ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k) (ts_heap s)
          (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1;
             b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                                  (hlen1 / 2);
             b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
             b_node := sd_elems k |}
    = Some stf ->
  ts_optlen (build_tree k s)
  = u64 (ol1
         + wsum (olterm maxc1 t1
                   (zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1))
                   (sd_extra_base k) (sd_extra k)
                   (ts_trees (build_tree k s) k))
                (b_hmax stf - 1 + 1)
                (Z.to_nat (HEAP_SIZE - (b_hmax stf - 1 + 1))))
  /\ ts_statlen (build_tree k s)
     = match sd_stree k with
       | None => sl1
       | Some st =>
           u64 (sl1
                + wsum (slterm maxc1 t1
                          (zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1))
                          (sd_extra_base k) (sd_extra k) st)
                       (b_hmax stf - 1 + 1)
                       (Z.to_nat (HEAP_SIZE - (b_hmax stf - 1 + 1))))
       end.
Proof.
  intros k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
         Hel HM HK Hbl0 Holu Hslu E0 E2 Eloop.
  destruct (build_tree_parked k s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2))
              stf Hel E0 E2 eq_refl Eloop)
    as [Hpk [Hout1 [Hsz [Hcen Hfr0]]]].
  set (hp3 := zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1)) in *.
  set (hmaxf := b_hmax stf - 1) in *.
  set (ndf := b_node stf) in *.
  set (M := sd_max_length k) in *.
  pose proof (bp_hmax _ _ _ _ _ _ _ Hpk) as Hhm.
  assert (Hmf0 : 0 <= hmaxf)
    by (unfold HEAP_SIZE in Hhm; unfold L_CODES in Hsz; lia).
  unfold build_tree. cbv zeta.
  rewrite E0. cbv beta match.
  rewrite E2. cbv beta match.
  rewrite Eloop. cbv beta match.
  fold (s1_of k maxc1 stf ol1 sl1 s).
  set (s2 := gen_bitlen k (s1_of k maxc1 stf ol1 sl1 s)) in *.
  rewrite ol_settree, sl_settree, set_tree_same.
  destruct (gen_bitlen_account k (s1_of k maxc1 stf ol1 sl1 s)
              (sd_elems k) maxc1 M t1 (b_tree stf) hp3 hmaxf ndf hlen1
              Hpk HM Hmf0 eq_refl
              (s1_heap k maxc1 stf ol1 sl1 s)
              (s1_heapmax k maxc1 stf ol1 sl1 s)
              (s1_trees k maxc1 stf ol1 sl1 s)
              (s1_maxcode k maxc1 stf ol1 sl1 s)
              ltac:(intros b Hb; rewrite s1_blcount; apply Hbl0; exact Hb)
              Hcen ltac:(lia) HK
              ltac:(rewrite s1_optlen; exact Holu)
              ltac:(rewrite s1_statlen; exact Hslu))
    as [Gol Gsl].
  fold s2 in Gol, Gsl.
  rewrite s1_optlen in Gol. rewrite s1_statlen in Gsl.
  (* the last line writes codes: lengths (hence the sums) are untouched *)
  assert (Hsum_eq : forall tX,
    tX = ts_trees s2 k ->
    wsum (olterm maxc1 t1 hp3 (sd_extra_base k) (sd_extra k)
            (gen_codes (ts_trees s2 k) maxc1 (ts_blcount s2)))
         (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))
    = wsum (olterm maxc1 t1 hp3 (sd_extra_base k) (sd_extra k)
              (ts_trees s2 k))
           (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))).
  { intros _ _. apply wsum_ext. intros p Hp.
    unfold olterm. rewrite gen_codes_len. reflexivity. }
  rewrite (Hsum_eq (ts_trees s2 k) eq_refl).
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as Hmcb.
  split.
  - (* Gol's terms read [tf]-frequencies, the statement reads [t1]'s; the
       leaf guard confines both to symbols below [elems], where they agree *)
    rewrite Gol.
    f_equal. f_equal.
    apply wsum_ext. intros p Hp.
    unfold olterm.
    destruct (Z.leb (hp3 p) maxc1) eqn:El; cbn [ind]; [|lia].
    apply Z.leb_le in El.
    rewrite (bp_frq _ _ _ _ _ _ _ Hpk (hp3 p)) by lia.
    reflexivity.
  - rewrite Gsl.
    destruct (sd_stree k) as [st|]; [|reflexivity].
    f_equal. f_equal.
    apply wsum_ext. intros p Hp.
    unfold slterm.
    destruct (Z.leb (hp3 p) maxc1) eqn:El; cbn [ind]; [|lia].
    apply Z.leb_le in El.
    rewrite (bp_frq _ _ _ _ _ _ _ Hpk (hp3 p)) by lia.
    reflexivity.
Qed.

Print Assumptions gen_bitlen_account.
Print Assumptions bt_force2_account.
Print Assumptions build_tree_account.

(** ** [build_bl_tree]'s own bill: the header-cost constant *)

Lemma bbl_optlen : forall s,
  ts_optlen (snd (build_bl_tree s))
  = u64 (ts_optlen (build_tree TK_BL
           (set_tree TK_BL
              (snd (scan_tree (ts_trees (set_tree TK_BL
                     (snd (scan_tree (ts_trees s TK_L) (ts_maxcode s TK_L)
                             (ts_trees s TK_BL)))
                     (set_tree TK_L
                        (fst (scan_tree (ts_trees s TK_L)
                                (ts_maxcode s TK_L) (ts_trees s TK_BL))) s))
                     TK_D)
                 (ts_maxcode s TK_D)
                 (ts_trees (set_tree TK_BL
                     (snd (scan_tree (ts_trees s TK_L) (ts_maxcode s TK_L)
                             (ts_trees s TK_BL)))
                     (set_tree TK_L
                        (fst (scan_tree (ts_trees s TK_L)
                                (ts_maxcode s TK_L) (ts_trees s TK_BL))) s))
                     TK_BL)))
              (set_tree TK_D
                 (fst (scan_tree (ts_trees (set_tree TK_BL
                        (snd (scan_tree (ts_trees s TK_L) (ts_maxcode s TK_L)
                                (ts_trees s TK_BL)))
                        (set_tree TK_L
                           (fst (scan_tree (ts_trees s TK_L)
                                   (ts_maxcode s TK_L) (ts_trees s TK_BL)))
                           s)) TK_D)
                         (ts_maxcode s TK_D)
                         (ts_trees (set_tree TK_BL
                        (snd (scan_tree (ts_trees s TK_L) (ts_maxcode s TK_L)
                                (ts_trees s TK_BL)))
                        (set_tree TK_L
                           (fst (scan_tree (ts_trees s TK_L)
                                   (ts_maxcode s TK_L) (ts_trees s TK_BL)))
                           s)) TK_BL)))
                 (set_tree TK_BL
                    (snd (scan_tree (ts_trees s TK_L) (ts_maxcode s TK_L)
                            (ts_trees s TK_BL)))
                    (set_tree TK_L
                       (fst (scan_tree (ts_trees s TK_L) (ts_maxcode s TK_L)
                               (ts_trees s TK_BL))) s)))))
         + 3 * (fst (build_bl_tree s) + 1) + 5 + 5 + 4).
Proof.
  intro s. unfold build_bl_tree. cbv zeta. cbn [snd fst].
  rewrite ol_optlen. reflexivity.
Qed.

Print Assumptions bbl_optlen.
