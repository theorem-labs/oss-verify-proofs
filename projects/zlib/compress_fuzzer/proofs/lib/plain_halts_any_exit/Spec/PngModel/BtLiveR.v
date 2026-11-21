(** * BtLiveR — the [build_bl_tree_mbi3] liveness chain at the R39 canon.

    OWNER: an earlier development run.  q5-emitter's composition sweep (2026-08-20) found ONE
    residual whole-array consumption site their ZR_BlfAll weakening leaves
    red: [BtLive.build_bl_tree_mbi3]'s premise [Hfb] quantifies BL-frequency
    bounds over the WHOLE array, but at reachable snapshots the indices
    >= 19 carry [bt_loop] internal-node residue (the R39 population), so
    only the [0,19) restriction is available.  This file is the additive
    [_r] mirror — the restriction closes on itself because the u16-headroom
    budget [frq_ok] is consumed ONLY through [frq_ok_bump] at [t_setfreq]
    sites, and [scan_go] writes exactly {curlen in [0,15], REP_3_6=16,
    REPZ_3_10=17, REPZ_11_138=18}; the liveness payoff reads [0,15]; and
    [bt_init] consumes [sd_elems TK_BL] = 19 cells.  The whole-array
    monotonicity conjuncts are bound-free and stay as landed.

    Originals in [BtLive] are RETAINED (retention convention; refutation
    targets).  Nothing here re-proves the build layers — [build_tree_live],
    [build_tree_parked], [bbl_scan_spec] are consumed from [BtLive] as-is. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus2 BtCensus4 BtCensus5 BtPass1 BtItem6 BtItem6b BtAccount2
  BuildTree HuffGenCodes ScanCount BtBlSide KraftAdjust BtLive.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** The range-restricted u16-headroom budget *)

Definition frq_ok_r (B : Z) (bl : Tree) : Prop :=
  forall v, 0 <= v < 19 -> 0 <= t_freq bl v /\ t_freq bl v + B <= 65535.

Lemma frq_ok_mono_r : forall B' B bl, B' <= B -> frq_ok_r B bl -> frq_ok_r B' bl.
Proof. intros B' B bl Hle Hb v Hv. destruct (Hb v Hv). split; lia. Qed.

(** One frequency bump at an IN-RANGE index: the budget pays for it, the
    monotonicity export stays whole-array (bound-free). *)
Lemma frq_ok_bump_r : forall B add bl idx,
  0 <= add <= B ->
  frq_ok_r B bl ->
  0 <= idx < 19 ->
  frq_ok_r (B - add) (t_setfreq bl idx (t_freq bl idx + add))
  /\ (forall v, t_freq bl v <= t_freq (t_setfreq bl idx (t_freq bl idx + add)) v)
  /\ t_freq (t_setfreq bl idx (t_freq bl idx + add)) idx = t_freq bl idx + add.
Proof.
  intros B add bl idx Ha Hb Hidx.
  assert (Hid : t_freq (t_setfreq bl idx (t_freq bl idx + add)) idx
                = t_freq bl idx + add).
  { rewrite t_freq_setfreq_same. apply u16_id. destruct (Hb idx Hidx). lia. }
  split; [|split; [|exact Hid]].
  - intros v Hv. destruct (Z.eq_dec v idx) as [->|Hne].
    + rewrite Hid. destruct (Hb idx Hidx). split; lia.
    + rewrite t_freq_setfreq_other by exact Hne.
      destruct (Hb v Hv). split; lia.
  - intro v. destruct (Z.eq_dec v idx) as [->|Hne].
    + rewrite Hid. destruct (Hb idx Hidx). lia.
    + rewrite t_freq_setfreq_other by exact Hne. lia.
Qed.

Lemma scan_go_inv_r :
  forall fuel t maxc slack n prevlen nextlen count maxcnt mincnt bl,
  0 <= count ->
  0 <= slack ->
  n <= maxc + 1 ->
  frq_ok_r (3 * (maxc + 2 - n) + count + slack) bl ->
  (maxc < n \/
   (nextlen = t_len t n
    /\ maxc + 1 - n < Z.of_nat fuel
    /\ (forall i, n <= i <= maxc -> 0 <= t_len t i <= 15)
    /\ t_len t (maxc + 1) = 65535)) ->
  (forall v, t_freq bl v
     <= t_freq (scan_go fuel t maxc n prevlen nextlen count maxcnt mincnt bl) v)
  /\ frq_ok_r slack (scan_go fuel t maxc n prevlen nextlen count maxcnt mincnt bl)
  /\ (((exists q, n <= q <= maxc /\ t_len t q <> 0
         /\ (forall i, n <= i < q -> t_len t i = 0))
       /\ (prevlen = -1 \/ prevlen = 0))
      \/ (exists v, 0 <= v <= 15 /\ 1 <= t_freq bl v)
      -> exists v, 0 <= v <= 15
           /\ 1 <= t_freq (scan_go fuel t maxc n prevlen nextlen count
                             maxcnt mincnt bl) v).
Proof.
  induction fuel as [|f IH];
    intros t maxc slack n prevlen nextlen count maxcnt mincnt bl
           Hc Hs Hn Hb Hst.
  - cbn [scan_go].
    split; [intro v; lia|]. split.
    + intros v Hv. destruct (Hb v Hv). split; lia.
    + intros [[ [q [Hq1 _]] _ ] | [v [Hv H1]]].
      * exfalso. destruct Hst as [Hlt | (_ & Hfu & _ & _)]; [lia|].
        cbn in Hfu. lia.
      * exists v. exact (conj Hv H1).
  - cbn [scan_go]. cbv zeta.
    destruct (Z.ltb maxc n) eqn:Hmn.
    + apply Z.ltb_lt in Hmn. cbv beta match.
      split; [intro v; lia|]. split.
      * intros v Hv. destruct (Hb v Hv). split; lia.
      * intros [[ [q [Hq1 _]] _ ] | [v [Hv H1]]]; [lia|].
        exists v. exact (conj Hv H1).
    + apply Z.ltb_ge in Hmn.
      destruct Hst as [Hlt | (Hnl & Hfu & Hrng & Hgd)]; [lia|].
      rewrite Nat2Z.inj_succ in Hfu.
      pose proof (Hrng n ltac:(lia)) as Hcur.
      assert (Hst' : maxc < n + 1 \/
              (t_len t (n + 1) = t_len t (n + 1)
               /\ maxc + 1 - (n + 1) < Z.of_nat f
               /\ (forall i, n + 1 <= i <= maxc -> 0 <= t_len t i <= 15)
               /\ t_len t (maxc + 1) = 65535)).
      { destruct (Z_le_gt_dec (n + 1) maxc) as [Hle|Hgt]; [right|left; lia].
        split; [reflexivity|]. split; [lia|].
        split; [intros i Hi; apply Hrng; lia | exact Hgd]. }
      destruct ((count + 1 <? maxcnt) && (nextlen =? t_len t (n + 1)))
        eqn:Hcont.
      * (* the run continues *)
        cbv beta match.
        apply andb_prop in Hcont. destruct Hcont as [_ Hpeq].
        apply Z.eqb_eq in Hpeq.
        assert (Hb' : frq_ok_r (3 * (maxc + 2 - (n + 1)) + (count + 1) + slack)
                        bl).
        { intros w Hw. destruct (Hb w Hw). split; lia. }
        destruct (IH t maxc slack (n + 1) prevlen (t_len t (n + 1)) (count + 1)
                     maxcnt mincnt bl ltac:(lia) Hs ltac:(lia) Hb'
                     ltac:(exact Hst')) as (IHm & IHb & IHe).
        split; [exact IHm|]. split; [exact IHb|].
        intros Hcase. apply IHe.
        destruct Hcase as [[ [q [Hq1 [Hq2 Hq3]]] Hprev ] | Hbump];
          [|right; exact Hbump].
        left. split; [|exact Hprev].
        destruct (Z.eq_dec n q) as [He|Hne].
        -- subst q.
           assert (Hn1 : n < maxc).
           { destruct (Z.eq_dec n maxc) as [He2|]; [|lia].
             exfalso. subst n. rewrite Hgd in Hpeq. lia. }
           exists (n + 1). split; [lia|]. split.
           { rewrite <- Hpeq. rewrite Hnl. exact Hq2. }
           { intros i Hi. lia. }
        -- exists q. split; [lia|]. split; [exact Hq2|].
           intros i Hi. apply Hq3. lia.
      * (* the run emits *)
        destruct (Z.ltb (count + 1) mincnt) eqn:Hbr1.
        -- (* freq[curlen] += count+1, and curlen = t_len t n is in [0,15] *)
           cbv beta match.
           destruct (frq_ok_bump_r (3 * (maxc + 2 - n) + count + slack)
                       (count + 1) bl nextlen ltac:(lia) Hb ltac:(lia))
             as (HbB & HmB & HeB).
           assert (HbB' : frq_ok_r (3 * (maxc + 2 - (n + 1)) + 0 + slack)
                     (t_setfreq bl nextlen (t_freq bl nextlen + (count + 1)))).
           { eapply frq_ok_mono_r; [|exact HbB]. lia. }
           destruct (IH t maxc slack (n + 1) nextlen (t_len t (n + 1)) 0
                        (if t_len t (n + 1) =? 0 then 138
                         else if nextlen =? t_len t (n + 1) then 6 else 7)
                        (if t_len t (n + 1) =? 0 then 3
                         else if nextlen =? t_len t (n + 1) then 3 else 4)
                        (t_setfreq bl nextlen
                           (t_freq bl nextlen + (count + 1)))
                        ltac:(lia) Hs ltac:(lia) HbB' ltac:(exact Hst'))
             as (IHm & IHb & IHe).
           split; [intro w; specialize (HmB w); specialize (IHm w); lia|].
           split; [exact IHb|].
           intros Hcase. apply IHe. right.
           destruct Hcase as [[ [q [Hq1 [Hq2 Hq3]]] Hprev ] | [w [Hw H1]]].
           ++ exists nextlen. destruct (Hb nextlen ltac:(lia)) as [Hb1 _].
              split; [lia|]. rewrite HeB. lia.
           ++ exists w. split; [exact Hw|]. specialize (HmB w). lia.
        -- destruct (negb (nextlen =? 0)) eqn:Hbr2.
           ++ (* a nonzero run: freq[curlen]++ if the value changed, REP++ *)
              apply negb_true_iff, Z.eqb_neq in Hbr2.
              destruct (negb (nextlen =? prevlen)) eqn:Hbr3.
              ** cbv beta match.
                 destruct (frq_ok_bump_r (3 * (maxc + 2 - n) + count + slack) 1
                             bl nextlen ltac:(lia) Hb ltac:(lia)) as (HbB1 & HmB1 & HeB1).
                 destruct (frq_ok_bump_r
                             (3 * (maxc + 2 - n) + count + slack - 1) 1
                             (t_setfreq bl nextlen (t_freq bl nextlen + 1))
                             REP_3_6 ltac:(lia) HbB1 ltac:(unfold REP_3_6; lia)) as (HbB2 & HmB2 & HeB2).
                 assert (HbB2' : frq_ok_r (3 * (maxc + 2 - (n + 1)) + 0 + slack)
                           (t_setfreq
                              (t_setfreq bl nextlen (t_freq bl nextlen + 1))
                              REP_3_6
                              (t_freq (t_setfreq bl nextlen
                                         (t_freq bl nextlen + 1)) REP_3_6
                               + 1))).
                 { eapply frq_ok_mono_r; [|exact HbB2]. lia. }
                 destruct (IH t maxc slack (n + 1) nextlen (t_len t (n + 1)) 0
                              (if t_len t (n + 1) =? 0 then 138
                               else if nextlen =? t_len t (n + 1) then 6
                                    else 7)
                              (if t_len t (n + 1) =? 0 then 3
                               else if nextlen =? t_len t (n + 1) then 3
                                    else 4)
                              (t_setfreq
                                 (t_setfreq bl nextlen
                                    (t_freq bl nextlen + 1)) REP_3_6
                                 (t_freq (t_setfreq bl nextlen
                                            (t_freq bl nextlen + 1)) REP_3_6
                                  + 1))
                              ltac:(lia) Hs ltac:(lia) HbB2'
                              ltac:(exact Hst')) as (IHm & IHb & IHe).
                 split.
                 { intro w. specialize (HmB1 w). specialize (HmB2 w).
                   specialize (IHm w). lia. }
                 split; [exact IHb|].
                 intros Hcase. apply IHe. right.
                 destruct Hcase as [[ [q [Hq1 [Hq2 Hq3]]] Hprev ]
                                   | [w [Hw H1]]].
                 --- exists nextlen. split; [lia|].
                     rewrite t_freq_setfreq_other
                       by (unfold REP_3_6; lia).
                     rewrite HeB1. destruct (Hb nextlen ltac:(lia)) as [Hb1 _]. lia.
                 --- exists w. split; [exact Hw|].
                     specialize (HmB1 w). specialize (HmB2 w). lia.
              ** (* same value as the previous run: only REP++ — but then
                    the first nonzero run cannot be the one emitting *)
                 apply negb_false_iff, Z.eqb_eq in Hbr3.
                 cbv beta match.
                 destruct (frq_ok_bump_r (3 * (maxc + 2 - n) + count + slack) 1
                             bl REP_3_6 ltac:(lia) Hb ltac:(unfold REP_3_6; lia)) as (HbB & HmB & HeB).
                 assert (HbB' : frq_ok_r (3 * (maxc + 2 - (n + 1)) + 0 + slack)
                           (t_setfreq bl REP_3_6 (t_freq bl REP_3_6 + 1))).
                 { eapply frq_ok_mono_r; [|exact HbB]. lia. }
                 destruct (IH t maxc slack (n + 1) nextlen (t_len t (n + 1)) 0
                              (if t_len t (n + 1) =? 0 then 138
                               else if nextlen =? t_len t (n + 1) then 6
                                    else 7)
                              (if t_len t (n + 1) =? 0 then 3
                               else if nextlen =? t_len t (n + 1) then 3
                                    else 4)
                              (t_setfreq bl REP_3_6 (t_freq bl REP_3_6 + 1))
                              ltac:(lia) Hs ltac:(lia) HbB'
                              ltac:(exact Hst')) as (IHm & IHb & IHe).
                 split;
                   [intro w; specialize (HmB w); specialize (IHm w); lia|].
                 split; [exact IHb|].
                 intros Hcase. apply IHe.
                 destruct Hcase as [[ [q [Hq1 [Hq2 Hq3]]] Hprev ]
                                   | [w [Hw H1]]].
                 --- exfalso. destruct Hprev as [Hpm1|Hp0]; lia.
                 --- right. exists w. split; [exact Hw|].
                     specialize (HmB w). lia.
           ++ (* a zero run: REPZ++, the pending nonzero position survives *)
              apply negb_false_iff, Z.eqb_eq in Hbr2.
              destruct (Z.leb (count + 1) 10) eqn:Hbr4.
              ** cbv beta match.
                 destruct (frq_ok_bump_r (3 * (maxc + 2 - n) + count + slack) 1
                             bl REPZ_3_10 ltac:(lia) Hb ltac:(unfold REPZ_3_10; lia)) as (HbB & HmB & HeB).
                 assert (HbB' : frq_ok_r (3 * (maxc + 2 - (n + 1)) + 0 + slack)
                           (t_setfreq bl REPZ_3_10
                              (t_freq bl REPZ_3_10 + 1))).
                 { eapply frq_ok_mono_r; [|exact HbB]. lia. }
                 destruct (IH t maxc slack (n + 1) nextlen (t_len t (n + 1)) 0
                              (if t_len t (n + 1) =? 0 then 138
                               else if nextlen =? t_len t (n + 1) then 6
                                    else 7)
                              (if t_len t (n + 1) =? 0 then 3
                               else if nextlen =? t_len t (n + 1) then 3
                                    else 4)
                              (t_setfreq bl REPZ_3_10
                                 (t_freq bl REPZ_3_10 + 1))
                              ltac:(lia) Hs ltac:(lia) HbB'
                              ltac:(exact Hst')) as (IHm & IHb & IHe).
                 split;
                   [intro w; specialize (HmB w); specialize (IHm w); lia|].
                 split; [exact IHb|].
                 intros Hcase. apply IHe.
                 destruct Hcase as [[ [q [Hq1 [Hq2 Hq3]]] Hprev ]
                                   | [w [Hw H1]]].
                 --- left.
                     assert (Hqn : n < q).
                     { destruct (Z.eq_dec n q) as [He|]; [|lia].
                       exfalso. apply Hq2. rewrite <- He, <- Hnl.
                       exact Hbr2. }
                     split; [|right; exact Hbr2].
                     exists q. split; [lia|]. split; [exact Hq2|].
                     intros i Hi. apply Hq3. lia.
                 --- right. exists w. split; [exact Hw|].
                     specialize (HmB w). lia.
              ** cbv beta match.
                 destruct (frq_ok_bump_r (3 * (maxc + 2 - n) + count + slack) 1
                             bl REPZ_11_138 ltac:(lia) Hb ltac:(unfold REPZ_11_138; lia))
                   as (HbB & HmB & HeB).
                 assert (HbB' : frq_ok_r (3 * (maxc + 2 - (n + 1)) + 0 + slack)
                           (t_setfreq bl REPZ_11_138
                              (t_freq bl REPZ_11_138 + 1))).
                 { eapply frq_ok_mono_r; [|exact HbB]. lia. }
                 destruct (IH t maxc slack (n + 1) nextlen (t_len t (n + 1)) 0
                              (if t_len t (n + 1) =? 0 then 138
                               else if nextlen =? t_len t (n + 1) then 6
                                    else 7)
                              (if t_len t (n + 1) =? 0 then 3
                               else if nextlen =? t_len t (n + 1) then 3
                                    else 4)
                              (t_setfreq bl REPZ_11_138
                                 (t_freq bl REPZ_11_138 + 1))
                              ltac:(lia) Hs ltac:(lia) HbB'
                              ltac:(exact Hst')) as (IHm & IHb & IHe).
                 split;
                   [intro w; specialize (HmB w); specialize (IHm w); lia|].
                 split; [exact IHb|].
                 intros Hcase. apply IHe.
                 destruct Hcase as [[ [q [Hq1 [Hq2 Hq3]]] Hprev ]
                                   | [w [Hw H1]]].
                 --- left.
                     assert (Hqn : n < q).
                     { destruct (Z.eq_dec n q) as [He|]; [|lia].
                       exfalso. apply Hq2. rewrite <- He, <- Hnl.
                       exact Hbr2. }
                     split; [|right; exact Hbr2].
                     exists q. split; [lia|]. split; [exact Hq2|].
                     intros i Hi. apply Hq3. lia.
                 --- right. exists w. split; [exact Hw|].
                     specialize (HmB w). lia.
Qed.

Lemma scan_tree_inv_r : forall t maxc bl slack,
  -1 <= maxc <= 285 ->
  0 <= slack ->
  frq_ok_r (3 * (maxc + 2) + slack) bl ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  (forall v, t_freq bl v <= t_freq (snd (scan_tree t maxc bl)) v)
  /\ frq_ok_r slack (snd (scan_tree t maxc bl))
  /\ (forall p, 0 <= p <= maxc -> t_len t p <> 0 ->
      exists v, 0 <= v <= 15 /\ 1 <= t_freq (snd (scan_tree t maxc bl)) v).
Proof.
  intros t maxc bl slack Hmc Hs Hb Hrng.
  unfold scan_tree. cbv zeta. cbn [snd].
  set (tg := t_setlen t (maxc + 1) 65535).
  destruct (Z_le_gt_dec 0 maxc) as [Hge|Hlt].
  - assert (Hgd : t_len tg (maxc + 1) = 65535).
    { unfold tg, t_setlen, t_len. cbn [tr_dl]. rewrite zset_same.
      reflexivity. }
    assert (Hlen : forall i, 0 <= i <= maxc -> t_len tg i = t_len t i).
    { intros i Hi. unfold tg, t_setlen, t_len. cbn [tr_dl].
      apply zset_other. lia. }
    rewrite <- (Hlen 0 ltac:(lia)).
    destruct (scan_go_inv_r (Z.to_nat L_CODES + 3) tg maxc slack 0 (-1)
                (t_len tg 0) 0
                (if t_len tg 0 =? 0 then 138 else 7)
                (if t_len tg 0 =? 0 then 3 else 4) bl
                ltac:(lia) Hs ltac:(lia)
                ltac:(eapply frq_ok_mono_r; [|exact Hb]; lia))
      as (Hm & Hok & He).
    { right. split; [reflexivity|]. split.
      { replace (Z.of_nat (Z.to_nat L_CODES + 3)) with 289 by reflexivity.
        lia. }
      split; [intros i Hi; rewrite Hlen by lia; apply Hrng; lia | exact Hgd]. }
    split; [exact Hm|]. split; [exact Hok|].
    intros p Hp Hnz.
    assert (Hnz' : t_len tg p <> 0) by (rewrite Hlen by lia; exact Hnz).
    destruct (least_nonzero (t_len tg) (Z.to_nat (p - 0)) p 0 eq_refl
                ltac:(lia) Hnz') as [q [Hq1 [Hq2 Hq3]]].
    apply He. left. split; [|left; reflexivity].
    exists q. split; [lia|]. split; [exact Hq2|].
    intros i Hi. apply Hq3. lia.
  - rewrite scan_go_neg by lia.
    split; [intro v; lia|]. split.
    + eapply frq_ok_mono_r; [|exact Hb]. lia.
    + intros p Hp Hnz. lia.
Qed.

Theorem build_bl_tree_mbi3_r :
  forall s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf p,
  0 <= p <= ts_maxcode s TK_L ->
  t_len (ts_trees s TK_L) p <> 0 ->
  ts_maxcode s TK_L <= 285 ->
  -1 <= ts_maxcode s TK_D <= 285 ->
  (forall i, 0 <= i <= ts_maxcode s TK_L ->
   0 <= t_len (ts_trees s TK_L) i <= 15) ->
  (forall i, 0 <= i <= ts_maxcode s TK_D ->
   0 <= t_len (ts_trees s TK_D) i <= 15) ->
  (forall x, 0 <= x < 19 -> 0 <= t_freq (ts_trees s TK_BL) x <= 60000) ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL)
          (snd (scan_tree (ts_trees s TK_D) (ts_maxcode s TK_D)
                  (snd (scan_tree (ts_trees s TK_L) (ts_maxcode s TK_L)
                          (ts_trees s TK_BL)))))
          (ts_heap s) (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1;
             b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                                  (hlen1 / 2);
             b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
             b_node := sd_elems TK_BL |} = Some stf ->
  3 <= fst (build_bl_tree s).
Proof.
  intros s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf p
         Hp Hpnz HmcL HmcD HrngL HrngD Hfb Hbl0 E0 E2 Eloop.
  set (bl2 := snd (scan_tree (ts_trees s TK_L) (ts_maxcode s TK_L)
                     (ts_trees s TK_BL))) in *.
  set (bl3 := snd (scan_tree (ts_trees s TK_D) (ts_maxcode s TK_D) bl2))
    in *.
  (* the L scan makes some symbol in [0,15] live; the D scan keeps it *)
  destruct (scan_tree_inv_r (ts_trees s TK_L) (ts_maxcode s TK_L)
              (ts_trees s TK_BL) (3 * (ts_maxcode s TK_D + 2))
              ltac:(lia) ltac:(lia)
              ltac:(intros w Hw; destruct (Hfb w Hw); split; lia)
              HrngL) as (_ & Hok2 & He2).
  fold bl2 in Hok2, He2.
  destruct (He2 p Hp Hpnz) as [v [Hv Hlive2]].
  destruct (scan_tree_inv_r (ts_trees s TK_D) (ts_maxcode s TK_D) bl2 0
              ltac:(lia) ltac:(lia)
              ltac:(eapply frq_ok_mono_r; [|exact Hok2]; lia)
              HrngD) as (Hm3 & _ & _).
  fold bl3 in Hm3.
  assert (Hlive : 1 <= t_freq bl3 v) by (specialize (Hm3 v); lia).
  (* open build_bl_tree and normalise the inner state to the canonical form *)
  unfold build_bl_tree. cbv zeta. cbn [fst].
  rewrite (set_tree_other TK_BL _ _ TK_D)
    by (unfold TK_D, TK_BL; lia).
  rewrite (set_tree_other TK_L _ _ TK_D)
    by (unfold TK_L, TK_D; lia).
  rewrite !mc_settree.
  rewrite (set_tree_same TK_BL).
  fold bl2. fold bl3.
  match goal with |- context [build_tree TK_BL ?X] => set (sI := X) end.
  assert (HtI : ts_trees sI TK_BL = bl3) by (unfold sI; apply set_tree_same).
  assert (HhI : ts_heap sI = ts_heap s)
    by (unfold sI; rewrite !hp_settree; reflexivity).
  assert (HdI : ts_depth sI = ts_depth s)
    by (unfold sI; rewrite !dp_settree; reflexivity).
  assert (HoI : ts_optlen sI = ts_optlen s)
    by (unfold sI; rewrite !ol_settree; reflexivity).
  assert (HsI2 : ts_statlen sI = ts_statlen s)
    by (unfold sI; rewrite !sl_settree; reflexivity).
  assert (HbI : forall b, b < 0 \/ 15 < b -> ts_blcount sI b = 0)
    by (intros b Hb; unfold sI; rewrite !blc_settree; apply Hbl0; exact Hb).
  assert (Hel19 : sd_elems TK_BL = 19) by reflexivity.
  (* the BL alphabet is small, so the K < 2^M slack bound is automatic *)
  destruct (build_tree_parked TK_BL sI t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2))
              stf ltac:(rewrite Hel19; unfold L_CODES; lia)
              ltac:(rewrite HtI, HhI, HdI; exact E0)
              ltac:(rewrite HoI, HsI2; exact E2)
              eq_refl Eloop)
    as [_ [HoutI _]].
  assert (Hh19 : hlen1 <= 19).
  { pose proof (io_total _ _ _ _ _ HoutI) as Ht.
    unfold live_total in Ht.
    pose proof (wsum_ind_ub (fun s' => live_b t1 maxc1 s') 0
                  (Z.to_nat (sd_elems TK_BL))) as HB.
    cbn beta in HB.
    rewrite Hel19 in Ht, HB.
    change (Z.of_nat (Z.to_nat 19)) with 19 in HB. lia. }
  assert (HKbl : 4 * (hlen1 - 1) < 2 ^ sd_max_length TK_BL).
  { replace (sd_max_length TK_BL) with 7 by reflexivity.
    replace (2 ^ 7) with 128 by reflexivity. lia. }
  pose proof (build_tree_live TK_BL sI t0 hp0 dep0 hlen0 maxc0
                t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf v
                ltac:(rewrite Hel19; unfold L_CODES; lia)
                ltac:(replace (sd_max_length TK_BL) with 7 by reflexivity;
                      lia)
                HKbl HbI
                ltac:(rewrite HtI, HhI, HdI; exact E0)
                ltac:(rewrite HoI, HsI2; exact E2)
                Eloop
                ltac:(rewrite Hel19; lia)
                ltac:(rewrite HtI; lia))
    as HLL.
  (* now read the answer off bbl_scan *)
  destruct (bl_order_inv v Hv) as [j [Hj Hbj]].
  replace (BL_CODES - 1) with 18 by reflexivity.
  destruct (bbl_scan_spec (Z.to_nat BL_CODES + 1)
              (ts_trees (build_tree TK_BL sI) TK_BL) 18
              ltac:(vm_compute; reflexivity) ltac:(lia))
    as [HrB [HzB HnB]].
  set (mbi := bbl_scan (Z.to_nat BL_CODES + 1)
                (ts_trees (build_tree TK_BL sI) TK_BL) 18) in *.
  destruct (Z_lt_ge_dec mbi 3) as [Hlt3|Hge3]; [exfalso|lia].
  pose proof (HzB j ltac:(lia)) as Hzj.
  rewrite Hbj in Hzj. lia.
Qed.

Print Assumptions scan_go_inv_r.
Print Assumptions scan_tree_inv_r.
Print Assumptions build_bl_tree_mbi3_r.
