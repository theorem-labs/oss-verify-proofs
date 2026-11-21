(** * BtLive — the dynamic BL header always keeps [max_blindex >= 3].

    OWNER: an earlier development run.  The one liveness fact the N5 packages cannot express:
    scanning a tree that has ANY nonzero length bumps some [bl_tree]
    frequency at a symbol in [0,15] — and every such symbol sits at a
    [bl_order] position >= 3 (positions 0-2 hold 16,17,18).  Through the BL
    build that symbol keeps a nonzero length, so [bbl_scan] stops at >= 3.

    Three layers:
    - [scan_go_inv]: one induction giving monotonicity, no-wrap bounds, and
      the bump-existence for [scan_go].  The key case analysis: the FIRST
      maximal nonzero-length run always emits with [prevlen] in {-1,0}
      (everything before it is a zero run), so the [curlen <> prevlen] test
      passes and [freq[curlen]]++ fires; a short run emits [+= count] which
      also lands on [curlen]; only pure REP/REPZ emissions miss [0,15], and
      those never resolve the first nonzero run.
    - [build_tree_live]: entry-live symbols get a nonzero length from
      [build_tree] (the missing direction of [build_tree_out]'s dead-zero).
    - [build_bl_tree_mbi3]: the consumer-facing fact, with the same TK_BL
      pipeline equations [bl_cl_pack] consumes plus raw-range facts about
      the L/D trees and BL frequency bounds (all zero after [init_block]). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus2 BtCensus4 BtCensus5 BtPass1 BtItem6 BtItem6b BtAccount2
  BuildTree HuffGenCodes ScanCount BtBlSide KraftAdjust.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** State-record projections across [set_tree] *)

Lemma hp_settree : forall k t s, ts_heap (set_tree k t s) = ts_heap s.
Proof. reflexivity. Qed.

Lemma dp_settree : forall k t s, ts_depth (set_tree k t s) = ts_depth s.
Proof. reflexivity. Qed.

Lemma blc_settree : forall k t s, ts_blcount (set_tree k t s) = ts_blcount s.
Proof. reflexivity. Qed.

(** ** Frequency-array bounds: enough headroom that every [u16] is exact *)

Definition frq_ok (B : Z) (bl : Tree) : Prop :=
  forall v, 0 <= t_freq bl v /\ t_freq bl v + B <= 65535.

Lemma frq_ok_mono : forall B' B bl, B' <= B -> frq_ok B bl -> frq_ok B' bl.
Proof. intros B' B bl Hle Hb v. destruct (Hb v). split; lia. Qed.

(** One frequency bump, exact modulo nothing: the budget pays for it. *)
Lemma frq_ok_bump : forall B add bl idx,
  0 <= add <= B ->
  frq_ok B bl ->
  frq_ok (B - add) (t_setfreq bl idx (t_freq bl idx + add))
  /\ (forall v, t_freq bl v <= t_freq (t_setfreq bl idx (t_freq bl idx + add)) v)
  /\ t_freq (t_setfreq bl idx (t_freq bl idx + add)) idx = t_freq bl idx + add.
Proof.
  intros B add bl idx Ha Hb.
  assert (Hid : t_freq (t_setfreq bl idx (t_freq bl idx + add)) idx
                = t_freq bl idx + add).
  { rewrite t_freq_setfreq_same. apply u16_id. destruct (Hb idx). lia. }
  split; [|split; [|exact Hid]].
  - intro v. destruct (Z.eq_dec v idx) as [->|Hne].
    + rewrite Hid. destruct (Hb idx). split; lia.
    + rewrite t_freq_setfreq_other by exact Hne. destruct (Hb v). split; lia.
  - intro v. destruct (Z.eq_dec v idx) as [->|Hne].
    + rewrite Hid. lia.
    + rewrite t_freq_setfreq_other by exact Hne. lia.
Qed.

(** ** The least nonzero position below a witness *)

Lemma least_nonzero : forall (f : Z -> Z) m p lo,
  Z.to_nat (p - lo) = m -> lo <= p -> f p <> 0 ->
  exists q, lo <= q <= p /\ f q <> 0 /\ (forall i, lo <= i < q -> f i = 0).
Proof.
  intros f m. induction m as [|m IHm]; intros p lo Hm Hlo Hf.
  - assert (Hpl : p = lo).
    { pose proof (Z2Nat.id (p - lo) ltac:(lia)) as Hid.
      rewrite Hm in Hid. cbn in Hid. lia. }
    exists p. split; [lia|]. split; [exact Hf|]. intros i Hi. lia.
  - pose proof (Z2Nat.id (p - lo) ltac:(lia)) as Hid.
    rewrite Hm in Hid. rewrite Nat2Z.inj_succ in Hid.
    pose proof (Nat2Z.is_nonneg m).
    destruct (Z.eq_dec (f lo) 0) as [Hz|Hnz].
    + destruct (IHm p (lo + 1)
                  ltac:(replace (p - (lo + 1)) with (Z.of_nat m) by lia;
                        apply Nat2Z.id)
                  ltac:(lia) Hf) as [q [Hq1 [Hq2 Hq3]]].
      exists q. split; [lia|]. split; [exact Hq2|].
      intros i Hi. destruct (Z.eq_dec i lo) as [->|]; [exact Hz|].
      apply Hq3. lia.
    + exists lo. split; [lia|]. split; [exact Hnz|]. intros i Hi. lia.
Qed.

(** ** [scan_go] below its window is the identity *)

Lemma scan_go_neg : forall fuel t maxc n prevlen nextlen count maxcnt mincnt bl,
  maxc < n ->
  scan_go fuel t maxc n prevlen nextlen count maxcnt mincnt bl = bl.
Proof.
  destruct fuel; intros t maxc n prevlen nextlen count maxcnt mincnt bl H;
    cbn [scan_go]; [reflexivity|].
  replace (Z.ltb maxc n) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(** ** The one induction over [scan_go]

    Conclusions: pointwise monotonicity, the no-wrap bound with the caller's
    [slack] left intact, and: if the window still holds a nonzero length
    whose prefix is all zeros while [prevlen] is -1 or 0 (the entry state,
    preserved by zero-run emissions), or some symbol in [0,15] is already
    live, then some symbol in [0,15] is live at exit. *)

Lemma scan_go_inv :
  forall fuel t maxc slack n prevlen nextlen count maxcnt mincnt bl,
  0 <= count ->
  0 <= slack ->
  n <= maxc + 1 ->
  frq_ok (3 * (maxc + 2 - n) + count + slack) bl ->
  (maxc < n \/
   (nextlen = t_len t n
    /\ maxc + 1 - n < Z.of_nat fuel
    /\ (forall i, n <= i <= maxc -> 0 <= t_len t i <= 15)
    /\ t_len t (maxc + 1) = 65535)) ->
  (forall v, t_freq bl v
     <= t_freq (scan_go fuel t maxc n prevlen nextlen count maxcnt mincnt bl) v)
  /\ frq_ok slack (scan_go fuel t maxc n prevlen nextlen count maxcnt mincnt bl)
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
    + intro v. destruct (Hb v). split; lia.
    + intros [[ [q [Hq1 _]] _ ] | [v [Hv H1]]].
      * exfalso. destruct Hst as [Hlt | (_ & Hfu & _ & _)]; [lia|].
        cbn in Hfu. lia.
      * exists v. exact (conj Hv H1).
  - cbn [scan_go]. cbv zeta.
    destruct (Z.ltb maxc n) eqn:Hmn.
    + apply Z.ltb_lt in Hmn. cbv beta match.
      split; [intro v; lia|]. split.
      * intro v. destruct (Hb v). split; lia.
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
        assert (Hb' : frq_ok (3 * (maxc + 2 - (n + 1)) + (count + 1) + slack)
                        bl).
        { intro w. destruct (Hb w). split; lia. }
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
           destruct (frq_ok_bump (3 * (maxc + 2 - n) + count + slack)
                       (count + 1) bl nextlen ltac:(lia) Hb)
             as (HbB & HmB & HeB).
           assert (HbB' : frq_ok (3 * (maxc + 2 - (n + 1)) + 0 + slack)
                     (t_setfreq bl nextlen (t_freq bl nextlen + (count + 1)))).
           { eapply frq_ok_mono; [|exact HbB]. lia. }
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
           ++ exists nextlen. destruct (Hb nextlen) as [Hb1 _].
              split; [lia|]. rewrite HeB. lia.
           ++ exists w. split; [exact Hw|]. specialize (HmB w). lia.
        -- destruct (negb (nextlen =? 0)) eqn:Hbr2.
           ++ (* a nonzero run: freq[curlen]++ if the value changed, REP++ *)
              apply negb_true_iff, Z.eqb_neq in Hbr2.
              destruct (negb (nextlen =? prevlen)) eqn:Hbr3.
              ** cbv beta match.
                 destruct (frq_ok_bump (3 * (maxc + 2 - n) + count + slack) 1
                             bl nextlen ltac:(lia) Hb) as (HbB1 & HmB1 & HeB1).
                 destruct (frq_ok_bump
                             (3 * (maxc + 2 - n) + count + slack - 1) 1
                             (t_setfreq bl nextlen (t_freq bl nextlen + 1))
                             REP_3_6 ltac:(lia) HbB1) as (HbB2 & HmB2 & HeB2).
                 assert (HbB2' : frq_ok (3 * (maxc + 2 - (n + 1)) + 0 + slack)
                           (t_setfreq
                              (t_setfreq bl nextlen (t_freq bl nextlen + 1))
                              REP_3_6
                              (t_freq (t_setfreq bl nextlen
                                         (t_freq bl nextlen + 1)) REP_3_6
                               + 1))).
                 { eapply frq_ok_mono; [|exact HbB2]. lia. }
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
                     rewrite HeB1. destruct (Hb nextlen) as [Hb1 _]. lia.
                 --- exists w. split; [exact Hw|].
                     specialize (HmB1 w). specialize (HmB2 w). lia.
              ** (* same value as the previous run: only REP++ — but then
                    the first nonzero run cannot be the one emitting *)
                 apply negb_false_iff, Z.eqb_eq in Hbr3.
                 cbv beta match.
                 destruct (frq_ok_bump (3 * (maxc + 2 - n) + count + slack) 1
                             bl REP_3_6 ltac:(lia) Hb) as (HbB & HmB & HeB).
                 assert (HbB' : frq_ok (3 * (maxc + 2 - (n + 1)) + 0 + slack)
                           (t_setfreq bl REP_3_6 (t_freq bl REP_3_6 + 1))).
                 { eapply frq_ok_mono; [|exact HbB]. lia. }
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
                 destruct (frq_ok_bump (3 * (maxc + 2 - n) + count + slack) 1
                             bl REPZ_3_10 ltac:(lia) Hb) as (HbB & HmB & HeB).
                 assert (HbB' : frq_ok (3 * (maxc + 2 - (n + 1)) + 0 + slack)
                           (t_setfreq bl REPZ_3_10
                              (t_freq bl REPZ_3_10 + 1))).
                 { eapply frq_ok_mono; [|exact HbB]. lia. }
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
                 destruct (frq_ok_bump (3 * (maxc + 2 - n) + count + slack) 1
                             bl REPZ_11_138 ltac:(lia) Hb)
                   as (HbB & HmB & HeB).
                 assert (HbB' : frq_ok (3 * (maxc + 2 - (n + 1)) + 0 + slack)
                           (t_setfreq bl REPZ_11_138
                              (t_freq bl REPZ_11_138 + 1))).
                 { eapply frq_ok_mono; [|exact HbB]. lia. }
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

(** ** [scan_tree]: the packaged corollary *)

Lemma scan_tree_inv : forall t maxc bl slack,
  -1 <= maxc <= 285 ->
  0 <= slack ->
  frq_ok (3 * (maxc + 2) + slack) bl ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  (forall v, t_freq bl v <= t_freq (snd (scan_tree t maxc bl)) v)
  /\ frq_ok slack (snd (scan_tree t maxc bl))
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
    destruct (scan_go_inv (Z.to_nat L_CODES + 3) tg maxc slack 0 (-1)
                (t_len tg 0) 0
                (if t_len tg 0 =? 0 then 138 else 7)
                (if t_len tg 0 =? 0 then 3 else 4) bl
                ltac:(lia) Hs ltac:(lia)
                ltac:(eapply frq_ok_mono; [|exact Hb]; lia))
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
    + eapply frq_ok_mono; [|exact Hb]. lia.
    + intros p Hp Hnz. lia.
Qed.

(** ** Where a symbol in [0,15] sits in [bl_order]: always at position >= 3 *)

Lemma bl_order_inv : forall v, 0 <= v <= 15 ->
  exists j, 3 <= j <= 18 /\ bl_order j = v.
Proof.
  intros v Hv.
  destruct (Z.eq_dec v 0) as [->|].
  { exists 3. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 1) as [->|].
  { exists 17. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 2) as [->|].
  { exists 15. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 3) as [->|].
  { exists 13. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 4) as [->|].
  { exists 11. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 5) as [->|].
  { exists 9. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 6) as [->|].
  { exists 7. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 7) as [->|].
  { exists 5. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 8) as [->|].
  { exists 4. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 9) as [->|].
  { exists 6. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 10) as [->|].
  { exists 8. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 11) as [->|].
  { exists 10. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 12) as [->|].
  { exists 12. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 13) as [->|].
  { exists 14. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 14) as [->|].
  { exists 16. split; [lia|]. vm_compute. reflexivity. }
  destruct (Z.eq_dec v 15) as [->|].
  { exists 18. split; [lia|]. vm_compute. reflexivity. }
  lia.
Qed.

(** ** Entry-live symbols keep a nonzero length through [build_tree]

    The missing direction of [build_tree_out]'s dead-zero conclusion. *)

Theorem build_tree_live :
  forall k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf v,
  3 <= sd_elems k <= L_CODES ->
  1 <= sd_max_length k <= 15 ->
  4 * (hlen1 - 1) < 2 ^ sd_max_length k ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
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
  0 <= v < sd_elems k ->
  t_freq (ts_trees s k) v <> 0 ->
  1 <= t_len (ts_trees (build_tree k s) k) v <= sd_max_length k.
Proof.
  intros k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf v
         Hel HM HK Hbl0 E0 E2 Eloop Hv Hfv.
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
  (* the symbol is still live after bt_init and bt_force2 *)
  assert (Hft1 : t_freq t1 v <> 0).
  { intro Hz. apply Hfv. rewrite <- (Hfr0 v).
    apply (bt_force2_freq0 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
             (ts_optlen s) (ts_statlen s) v).
    rewrite E2. exact Hz. }
  assert (Hvmc : v <= maxc1).
  { destruct (Z_le_gt_dec v maxc1) as [Hle|Hgt]; [exact Hle|].
    exfalso. apply Hft1. apply (io_gapz _ _ _ _ _ Hout1). lia. }
  destruct (gen_bitlen_out k (s1_of k maxc1 stf ol1 sl1 s) (sd_elems k) maxc1
              M t1 (b_tree stf) hp3 hmaxf ndf hlen1
              Hpk HM Hmf0 eq_refl
              (s1_heap k maxc1 stf ol1 sl1 s)
              (s1_heapmax k maxc1 stf ol1 sl1 s)
              (s1_trees k maxc1 stf ol1 sl1 s)
              (s1_maxcode k maxc1 stf ol1 sl1 s)
              ltac:(intros b Hb; rewrite s1_blcount; apply Hbl0; exact Hb)
              Hcen ltac:(lia) HK)
    as [G1 [G2 [G3 [G4 [G5 G6]]]]].
  unfold build_tree. cbv zeta.
  rewrite E0. cbv beta match.
  rewrite E2. cbv beta match.
  rewrite Eloop. cbv beta match.
  fold (s1_of k maxc1 stf ol1 sl1 s).
  set (s2 := gen_bitlen k (s1_of k maxc1 stf ol1 sl1 s)) in *.
  rewrite set_tree_same.
  rewrite gen_codes_len.
  exact (sym_live_range (sd_elems k) maxc1 M t1 (b_tree stf) hp3 hmaxf ndf
           Hpk (ts_trees s2 k) G4 v (conj (proj1 Hv) Hvmc) Hft1).
Qed.

(** ** The consumer theorem: [build_bl_tree] returns [max_blindex >= 3]

    Premises are the same TK_BL pipeline equations [bl_cl_pack] consumes
    (stated over the post-scan BL tree), plus: one nonzero length in the L
    tree (END_BLOCK's, in practice), the raw ranges both builds export, and
    BL-frequency bounds (frequencies are zero straight after [init_block],
    and nothing before [build_bl_tree] touches the BL tree). *)

Theorem build_bl_tree_mbi3 :
  forall s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf p,
  0 <= p <= ts_maxcode s TK_L ->
  t_len (ts_trees s TK_L) p <> 0 ->
  ts_maxcode s TK_L <= 285 ->
  -1 <= ts_maxcode s TK_D <= 285 ->
  (forall i, 0 <= i <= ts_maxcode s TK_L ->
   0 <= t_len (ts_trees s TK_L) i <= 15) ->
  (forall i, 0 <= i <= ts_maxcode s TK_D ->
   0 <= t_len (ts_trees s TK_D) i <= 15) ->
  (forall x, 0 <= t_freq (ts_trees s TK_BL) x <= 60000) ->
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
  destruct (scan_tree_inv (ts_trees s TK_L) (ts_maxcode s TK_L)
              (ts_trees s TK_BL) (3 * (ts_maxcode s TK_D + 2))
              ltac:(lia) ltac:(lia)
              ltac:(intro w; destruct (Hfb w); split; lia)
              HrngL) as (_ & Hok2 & He2).
  fold bl2 in Hok2, He2.
  destruct (He2 p Hp Hpnz) as [v [Hv Hlive2]].
  destruct (scan_tree_inv (ts_trees s TK_D) (ts_maxcode s TK_D) bl2 0
              ltac:(lia) ltac:(lia)
              ltac:(eapply frq_ok_mono; [|exact Hok2]; lia)
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

Print Assumptions scan_go_inv.
Print Assumptions scan_tree_inv.
Print Assumptions build_tree_live.
Print Assumptions build_bl_tree_mbi3.
