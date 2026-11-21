(** * BtAccount — [opt_len]/[static_len] are the frequency-weighted length
      sums, threaded through both passes.

    OWNER: an earlier development run (G6's accounting face).  Additive over the landed walks:
    [Pass1Acc]/[Pass2Acc] CARRY the landed invariants as fields and add only
    the accumulator clauses, so nothing already proved is touched.

    All equalities are mod [2^64] ([u64]) because the model's counters are:
    [bt_force2] can drive [opt_len] through zero (the only-END_BLOCK corner)
    and the C wraps. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus1 BtCensus2 BtCensus3 BtCensus4 BtPass1 BtPass2 BtLevels
  GenBitlen.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Lemma u64_add_l : forall a b, u64 (u64 a + b) = u64 (a + b).
Proof.
  intros a b. unfold u64.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Section Acc1.

Variables (elems maxc1 M : Z) (t1 tf : Tree) (hp3 : zarr) (hmaxf ndf : Z).
Hypothesis Hpk : BtParked elems maxc1 t1 tf hp3 hmaxf ndf.
Hypothesis HM : 1 <= M <= 15.
Hypothesis Hmf0 : 0 <= hmaxf.
Variables (k base : Z) (extra : zarr) (stree : option Tree).
Variables (ol0 sl0 : Z).
Hypothesis Hol0 : ol0 = u64 ol0.
Hypothesis Hsl0 : sl0 = u64 sl0.

Definition xbits (n : Z) : Z :=
  if Z.leb base n then extra (n - base) else 0.

Definition olterm (t : Tree) (p : Z) : Z :=
  ind (hp3 p <=? maxc1)
  * (t_freq tf (hp3 p) * (t_len t (hp3 p) + xbits (hp3 p))).

Definition slterm (st : Tree) (p : Z) : Z :=
  ind (hp3 p <=? maxc1)
  * (t_freq tf (hp3 p) * (t_len st (hp3 p) + xbits (hp3 p))).

Record Pass1Acc (h : Z) (t : Tree) (blc : zarr) (ov ol sl : Z) : Prop :=
mkPass1Acc {
  pa_inv : Pass1Inv maxc1 M tf hp3 hmaxf ndf h t blc ov;
  pa_fc  : forall x, t_freq t x = t_freq tf x;
  pa_ol  : ol = u64 (ol0 + wsum (olterm t) (hmaxf + 1)
                             (Z.to_nat (h - (hmaxf + 1))));
  pa_sl  : sl = match stree with
                | None => sl0
                | Some st =>
                    u64 (sl0 + wsum (slterm st) (hmaxf + 1)
                                 (Z.to_nat (h - (hmaxf + 1))))
                end
}.

Lemma acc_entry : forall blc0,
  (forall b, blc0 b = 0) ->
  Pass1Acc (hmaxf + 1) (t_setlen tf (ndf - 1) 0) blc0 0 ol0 sl0.
Proof.
  intros blc0 Hb0.
  constructor.
  - exact (pass1_entry elems maxc1 M t1 tf hp3 hmaxf ndf Hpk blc0 Hb0).
  - intro x. reflexivity.
  - replace (hmaxf + 1 - (hmaxf + 1)) with 0 by lia.
    cbn [Z.to_nat wsum]. rewrite Z.add_0_r. exact Hol0.
  - destruct stree as [st|]; [|reflexivity].
    replace (hmaxf + 1 - (hmaxf + 1)) with 0 by lia.
    cbn [Z.to_nat wsum]. rewrite Z.add_0_r. exact Hsl0.
Qed.

Lemma acc_step : forall h t blc ov ol sl blc' ol' sl' bits,
  hmaxf + 1 <= h < HEAP_SIZE ->
  Pass1Acc h t blc ov ol sl ->
  bits = Z.min (t_len t (t_dad tf (hp3 h)) + 1) M ->
  ((maxc1 < hp3 h /\ blc' = blc /\ ol' = ol /\ sl' = sl)
   \/ (hp3 h <= maxc1
       /\ blc' = zset blc bits (u16 (blc bits + 1))
       /\ ol' = u64 (ol + t_freq t (hp3 h) * (bits + xbits (hp3 h)))
       /\ sl' = match stree with
                | None => sl
                | Some st =>
                    u64 (sl + t_freq t (hp3 h)
                              * (t_len st (hp3 h) + xbits (hp3 h)))
                end)) ->
  Pass1Acc (h + 1) (t_setlen t (hp3 h) bits) blc'
           (ov + ind (Z.eqb (t_len t (t_dad tf (hp3 h))) M)) ol' sl'.
Proof.
  intros h t blc ov ol sl blc' ol' sl' bits Hh Hacc Ebits Hcase.
  destruct Hacc as [Hinv Hfc Hol Hsl].
  pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk) as Hwlt.
  set (x := hp3 h) in *.
  assert (Hxvis : forall p, hmaxf <= p < h -> hp3 p <> x)
    by (intros p Hp; apply (pk_distinct _ _ _ _ _ _ _ Hpk); lia).
  assert (Wlen_other : forall y, y <> x ->
          t_len (t_setlen t x bits) y = t_len t y)
    by (intros y Hy; apply t_len_setlen_other'; exact Hy).
  assert (Hbits : 1 <= bits <= M).
  { pose proof (pass1_dad_len _ _ _ _ _ _ _ _ Hpk HM h t blc ov
                  ltac:(lia) Hinv) as HD.
    fold x in HD. lia. }
  assert (Wlen_same : t_len (t_setlen t x bits) x = bits).
  { rewrite t_len_setlen_same'. unfold u16. apply Z.mod_small. lia. }
  assert (Hszs : Z.to_nat (h + 1 - (hmaxf + 1))
                 = S (Z.to_nat (h - (hmaxf + 1))))
    by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
  assert (Hpos : hmaxf + 1 + Z.of_nat (Z.to_nat (h - (hmaxf + 1))) = h)
    by (rewrite Z2Nat.id by lia; lia).
  assert (Htail : wsum (olterm (t_setlen t x bits)) (hmaxf + 1)
                       (Z.to_nat (h - (hmaxf + 1)))
                  = wsum (olterm t) (hmaxf + 1)
                         (Z.to_nat (h - (hmaxf + 1)))).
  { apply wsum_ext. intros p Hp. unfold olterm.
    rewrite (Wlen_other (hp3 p) (Hxvis p ltac:(lia))). reflexivity. }
  constructor.
  - apply (pass1_step elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM Hmf0
             h t blc ov blc' bits ltac:(lia) Hinv Ebits).
    destruct Hcase as [[Hi [Hb _]]|[Hl [Hb _]]]; [left|right]; auto.
  - intro y.
    change (t_freq (t_setlen t x bits) y) with (t_freq t y).
    apply Hfc.
  - rewrite Hszs, wsum_split_last, Hpos, Htail.
    destruct Hcase as [[Hi [_ [-> _]]]|[Hl [_ [-> _]]]].
    + assert (Hterm : olterm (t_setlen t x bits) h = 0).
      { unfold olterm. fold x.
        replace (x <=? maxc1) with false by (symmetry; apply Z.leb_gt; lia).
        cbn [ind]. lia. }
      rewrite Hterm, Hol. f_equal. lia.
    + assert (Hterm : olterm (t_setlen t x bits) h
                      = t_freq tf x * (bits + xbits x)).
      { unfold olterm. fold x.
        replace (x <=? maxc1) with true by (symmetry; apply Z.leb_le; lia).
        cbn [ind]. rewrite Wlen_same. lia. }
      rewrite (Hfc x), Hterm, Hol, u64_add_l. f_equal. lia.
  - destruct stree as [st|] eqn:Est.
    + assert (Hszt : wsum (slterm st) (hmaxf + 1)
                          (Z.to_nat (h + 1 - (hmaxf + 1)))
                     = wsum (slterm st) (hmaxf + 1)
                            (Z.to_nat (h - (hmaxf + 1))) + slterm st h)
        by (rewrite Hszs, wsum_split_last, Hpos; reflexivity).
      rewrite Hszt.
      destruct Hcase as [[Hi [_ [_ ->]]]|[Hl [_ [_ ->]]]].
      * assert (Hterm : slterm st h = 0).
        { unfold slterm. fold x.
          replace (x <=? maxc1) with false
            by (symmetry; apply Z.leb_gt; lia).
          cbn [ind]. lia. }
        rewrite Hterm, Hsl. f_equal. lia.
      * assert (Hterm : slterm st h
                        = t_freq tf x * (t_len st x + xbits x)).
        { unfold slterm. fold x.
          replace (x <=? maxc1) with true
            by (symmetry; apply Z.leb_le; lia).
          cbn [ind]. lia. }
        rewrite (Hfc x), Hterm, Hsl, u64_add_l. f_equal. lia.
    + destruct Hcase as [[Hi [_ [_ ->]]]|[Hl [_ [_ ->]]]]; exact Hsl.
Qed.


Lemma acc_walk : forall fuel h t blc ol sl ov,
  hmaxf + 1 <= h <= HEAP_SIZE ->
  HEAP_SIZE - h <= Z.of_nat fuel ->
  Pass1Acc h t blc ov ol sl ->
  match gb_pass1 fuel k hp3 maxc1 M base extra stree h t blc ol sl ov with
  | (t2, blc2, ol2, sl2, ov2) => Pass1Acc HEAP_SIZE t2 blc2 ov2 ol2 sl2
  end.
Proof.
  induction fuel as [|f IH]; intros h t blc ol sl ov Hh Hf Hacc.
  - cbn [gb_pass1]. cbn [Z.of_nat] in Hf.
    replace HEAP_SIZE with h by lia. exact Hacc.
  - cbn [gb_pass1].
    destruct (Z.leb HEAP_SIZE h) eqn:Eg.
    + apply Z.leb_le in Eg. replace HEAP_SIZE with h by lia. exact Hacc.
    + apply Z.leb_gt in Eg.
      rewrite Nat2Z.inj_succ in Hf.
      pose proof (pa_inv _ _ _ _ _ _ Hacc) as Hinv.
      assert (Hdx : t_dad t (hp3 h) = t_dad tf (hp3 h))
        by (apply (p1_dadk _ _ _ _ _ _ _ _ _ _ Hinv); lia).
      rewrite Hdx.
      rewrite !if_ltb_min.
      pose proof (pass1_dad_len _ _ _ _ _ _ _ _ Hpk HM h t blc ov
                    ltac:(lia) Hinv) as Hdl.
      assert (Eov : (if Z.ltb M (t_len t (t_dad tf (hp3 h)) + 1)
                     then ov + 1 else ov)
                    = ov + ind (Z.eqb (t_len t (t_dad tf (hp3 h))) M)).
      { destruct (Z.ltb M (t_len t (t_dad tf (hp3 h)) + 1)) eqn:E.
        - apply Z.ltb_lt in E.
          replace (Z.eqb (t_len t (t_dad tf (hp3 h))) M) with true
            by (symmetry; apply Z.eqb_eq; lia).
          cbn [ind]. reflexivity.
        - apply Z.ltb_ge in E.
          replace (Z.eqb (t_len t (t_dad tf (hp3 h))) M) with false
            by (symmetry; apply Z.eqb_neq; lia).
          cbn [ind]. lia. }
      rewrite Eov.
      destruct (Z.ltb maxc1 (hp3 h)) eqn:El.
      * apply Z.ltb_lt in El.
        apply IH; [lia | lia |].
        eapply acc_step; [lia | exact Hacc | reflexivity |].
        left. repeat split; auto.
      * apply Z.ltb_ge in El.
        apply IH; [lia | lia |].
        eapply acc_step; [lia | exact Hacc | reflexivity |].
        right. repeat split; auto.
Qed.

End Acc1.

Print Assumptions acc_entry.
Print Assumptions acc_step.
Print Assumptions acc_walk.

(** ** Pass 2: the correction sum *)

Section Acc2.

Variables (elems maxc1 M : Z) (t1 tf : Tree) (hp3 : zarr) (hmaxf ndf : Z).
Hypothesis Hpk : BtParked elems maxc1 t1 tf hp3 hmaxf ndf.
Hypothesis HM : 1 <= M <= 15.
Variables (t2 : Tree) (blc2 : zarr).
Hypothesis Hrng2 : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
                   1 <= t_len t2 (hp3 p) <= M.
Hypothesis Hnn2 : forall b, 0 <= blc2 b.
Hypothesis Htot :
  BtPass2.lcnt maxc1 hp3 t2 (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))
  = BtPass2.bsumr blc2 (Z.to_nat M) 1.
Variable (ol1 : Z).
Hypothesis Hol1 : ol1 = u64 ol1.
Hypothesis Hfc2 : forall x, t_freq t2 x = t_freq tf x.

Definition corrterm (t : Tree) (p : Z) : Z :=
  ind (hp3 p <=? maxc1)
  * (t_freq tf (hp3 p) * (t_len t (hp3 p) - t_len t2 (hp3 p))).

Record Pass2Acc (bits n h : Z) (t : Tree) (ol : Z) : Prop :=
mkPass2Acc {
  qa_inv : Pass2Inv maxc1 M hp3 hmaxf t2 blc2 bits n h t;
  qa_fc  : forall x, t_freq t x = t_freq tf x;
  qa_ol  : ol = u64 (ol1 + wsum (corrterm t) h (Z.to_nat (HEAP_SIZE - h)))
}.

Lemma acc2_entry : Pass2Acc M (blc2 M) HEAP_SIZE t2 ol1.
Proof.
  constructor.
  - exact (pass2_entry elems maxc1 M t1 tf hp3 hmaxf ndf Hpk HM
             t2 blc2 Hnn2).
  - exact Hfc2.
  - replace (HEAP_SIZE - HEAP_SIZE) with 0 by lia.
    cbn [Z.to_nat wsum]. rewrite Z.add_0_r. exact Hol1.
Qed.

Lemma acc2_walk : forall fuel bits n h t ol,
  (h - hmaxf) + bits + 1 <= Z.of_nat fuel ->
  Pass2Acc bits n h t ol ->
  match gb_pass2 fuel hp3 maxc1 t blc2 bits n h ol with
  | (t3, ol2) => exists h', Pass2Acc 1 0 h' t3 ol2
  end.
Proof.
  induction fuel as [|f IH]; intros bits n h t ol Hf Hacc.
  - pose proof (q2_h _ _ _ _ _ _ _ _ _ _ (qa_inv _ _ _ _ _ Hacc)).
    pose proof (q2_bits _ _ _ _ _ _ _ _ _ _ (qa_inv _ _ _ _ _ Hacc)).
    cbn [Z.of_nat] in Hf. lia.
  - rewrite Nat2Z.inj_succ in Hf.
    destruct Hacc as [Hinv Hfc Hol].
    pose proof (q2_h _ _ _ _ _ _ _ _ _ _ Hinv) as Hhr.
    pose proof (q2_bits _ _ _ _ _ _ _ _ _ _ Hinv) as Hbr.
    pose proof (q2_n _ _ _ _ _ _ _ _ _ _ Hinv) as Hnr.
    cbn [gb_pass2].
    destruct (Z.eqb n 0) eqn:En.
    + apply Z.eqb_eq in En. subst n.
      destruct (Z.leb bits 1) eqn:Eb.
      * apply Z.leb_le in Eb.
        assert (E1 : bits = 1) by lia. subst bits.
        exists h. constructor; assumption.
      * apply Z.leb_gt in Eb.
        apply IH; [lia|].
        constructor; [| exact Hfc | exact Hol].
        apply (pass2_step_group maxc1 M hp3 hmaxf t2 blc2 Hnn2 bits h t
                 Hinv ltac:(lia)).
    + apply Z.eqb_neq in En.
      assert (Hn1 : 1 <= n) by lia.
      destruct (Z.ltb maxc1 (hp3 (h - 1))) eqn:Em.
      * apply Z.ltb_lt in Em.
        assert (Hinv' : Pass2Inv maxc1 M hp3 hmaxf t2 blc2 bits n (h - 1) t)
          by (apply (pass2_step_skip elems maxc1 M t1 tf hp3 hmaxf ndf Hpk
                       t2 blc2 Hnn2 Htot bits n h t Hinv Hn1 Em)).
        pose proof (q2_h _ _ _ _ _ _ _ _ _ _ Hinv') as Hh1'.
        apply IH; [lia|].
        constructor; [exact Hinv' | exact Hfc |].
        rewrite Hol.
        f_equal. f_equal.
        replace (Z.to_nat (HEAP_SIZE - (h - 1)))
          with (S (Z.to_nat (HEAP_SIZE - h)))
          by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
        rewrite wsum_split_first.
        replace (h - 1 + 1) with h by lia.
        unfold corrterm at 2.
        replace (hp3 (h - 1) <=? maxc1) with false
          by (symmetry; apply Z.leb_gt; lia).
        cbn [ind]. lia.
      * apply Z.ltb_ge in Em.
        destruct (Z.eqb (t_len t (hp3 (h - 1))) bits) eqn:El.
        -- apply Z.eqb_eq in El.
           assert (Hinv' : Pass2Inv maxc1 M hp3 hmaxf t2 blc2
                             bits (n - 1) (h - 1) t)
             by (apply (pass2_step_take elems maxc1 M t1 tf hp3 hmaxf ndf
                          Hpk HM t2 blc2 bits n h t t);
                 [exact Hinv | exact Hn1 | exact Em | left; auto]).
           pose proof (q2_h _ _ _ _ _ _ _ _ _ _ Hinv') as Hh1'.
           apply IH; [lia|].
           constructor; [exact Hinv' | exact Hfc |].
           rewrite Hol.
           f_equal. f_equal.
           replace (Z.to_nat (HEAP_SIZE - (h - 1)))
             with (S (Z.to_nat (HEAP_SIZE - h)))
             by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
           rewrite wsum_split_first.
           replace (h - 1 + 1) with h by lia.
           unfold corrterm at 2.
           rewrite (q2_lo _ _ _ _ _ _ _ _ _ _ Hinv (h - 1) ltac:(lia)) in El.
           replace (hp3 (h - 1) <=? maxc1) with true
             by (symmetry; apply Z.leb_le; lia).
           cbn [ind]. rewrite El.
           rewrite (q2_lo _ _ _ _ _ _ _ _ _ _ Hinv (h - 1) ltac:(lia)).
           lia.
        -- assert (Hinv' : Pass2Inv maxc1 M hp3 hmaxf t2 blc2
                             bits (n - 1) (h - 1)
                             (t_setlen t (hp3 (h - 1)) bits))
             by (apply (pass2_step_take elems maxc1 M t1 tf hp3 hmaxf ndf
                          Hpk HM t2 blc2 bits n h t
                          (t_setlen t (hp3 (h - 1)) bits));
                 [exact Hinv | exact Hn1 | exact Em | right; reflexivity]).
           pose proof (q2_h _ _ _ _ _ _ _ _ _ _ Hinv') as Hh1'.
           pose proof (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk) as Hwlt.
           set (m := hp3 (h - 1)) in *.
           assert (Hmvis : forall p, h <= p < HEAP_SIZE -> hp3 p <> m)
             by (intros p Hp; apply (pk_distinct _ _ _ _ _ _ _ Hpk); lia).
           apply IH; [lia|].
           constructor; [exact Hinv' | |].
           ++ intro y.
              change (t_freq (t_setlen t m bits) y) with (t_freq t y).
              apply Hfc.
           ++ rewrite Hol.
              rewrite u64_add_l. f_equal.
              replace (Z.to_nat (HEAP_SIZE - (h - 1)))
                with (S (Z.to_nat (HEAP_SIZE - h)))
                by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
              rewrite wsum_split_first.
              replace (h - 1 + 1) with h by lia.
              assert (Htail :
                wsum (corrterm (t_setlen t m bits)) h
                     (Z.to_nat (HEAP_SIZE - h))
                = wsum (corrterm t) h (Z.to_nat (HEAP_SIZE - h))).
              { apply wsum_ext. intros p Hp.
                unfold corrterm.
                rewrite t_len_setlen_other';
                  [reflexivity|].
                apply Hmvis.
                split; [lia|].
                destruct Hp as [_ Hp2].
                rewrite Z2Nat.id in Hp2 by lia. lia. }
              rewrite Htail.
              assert (Hterm : corrterm (t_setlen t m bits) (h - 1)
                              = t_freq tf m * (bits - t_len t2 m)).
              { unfold corrterm. fold m.
                replace (m <=? maxc1) with true
                  by (symmetry; apply Z.leb_le; lia).
                cbn [ind].
                assert (Hsame : t_len (t_setlen t m bits) m = bits).
                { rewrite t_len_setlen_same'. unfold u16.
                  apply Z.mod_small.
                  pose proof (q2_bits _ _ _ _ _ _ _ _ _ _ Hinv). lia. }
                rewrite Hsame. lia. }
              rewrite Hterm.
              pose proof (q2_lo _ _ _ _ _ _ _ _ _ _ Hinv (h - 1)
                            ltac:(lia)) as Hlo1.
              fold m in Hlo1.
              rewrite Hlo1, (Hfc m). lia.
Qed.

End Acc2.

Print Assumptions acc2_entry.
Print Assumptions acc2_walk.
