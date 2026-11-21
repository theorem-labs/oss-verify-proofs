(** * BtPass1 — [gb_pass1] computes dad-chain depths, clamped at [maxlen].

    OWNER: an earlier development run.

    The walk order is the whole trick (and [trees.c]'s own comment): heap
    positions ascend from [heap_max]+1, dads park strictly below their
    children (BtCensus4.bp_ord), and [tr_dl] is a union — so when position
    [h]'s node is visited, its own [dl] slot still holds its DAD (nobody
    visited it before: parked values are distinct), while its dad's [dl]
    slot already holds the dad's final LEN.  The pass therefore computes

        len x = min (len (dad x) + 1, maxlen)

    pointwise, keeps the root at 0, histograms the LEAF lengths into
    [bl_count], and counts in [overflow] exactly the nodes whose dad sits at
    level [maxlen].  Everything downstream (the level equations, the Kraft
    telescope) reads these four pointwise facts off the FINAL tree; no sums
    are carried through the walk except the histogram itself. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus1 BtCensus2 BtCensus3 BtCensus4 GenBitlen.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Generic helpers *)

Lemma wsum_const1 : forall lo n, wsum (fun _ => 1) lo n = Z.of_nat n.
Proof.
  intros lo n; revert lo.
  induction n as [|k IH]; intro lo; cbn [wsum]; [reflexivity|].
  rewrite IH. lia.
Qed.

Lemma wsum_ind_ub : forall (f : Z -> bool) lo n,
  wsum (fun i => ind (f i)) lo n <= Z.of_nat n.
Proof.
  intros f lo n.
  rewrite <- (wsum_const1 lo n).
  apply wsum_le. intros i _. apply ind_0_1.
Qed.

Lemma if_ltb_min : forall b0 M,
  (if Z.ltb M b0 then M else b0) = Z.min b0 M.
Proof.
  intros b0 M. destruct (Z.ltb M b0) eqn:E.
  - apply Z.ltb_lt in E. rewrite Z.min_r by lia. reflexivity.
  - apply Z.ltb_ge in E. rewrite Z.min_l by lia. reflexivity.
Qed.

Lemma arr_zero_out : forall n i a j,
  (j < i \/ i + Z.of_nat n <= j) -> arr_zero n i a j = a j.
Proof.
  induction n as [|k IH]; intros i a j Hj.
  - reflexivity.
  - rewrite Nat2Z.inj_succ in Hj. cbn [arr_zero].
    rewrite IH by lia.
    apply zset_other. lia.
Qed.

Lemma arr_zero_in : forall n i a j,
  i <= j < i + Z.of_nat n -> arr_zero n i a j = 0.
Proof.
  induction n as [|k IH]; intros i a j Hj.
  - cbn [Z.of_nat] in Hj. lia.
  - rewrite Nat2Z.inj_succ in Hj. cbn [arr_zero].
    destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite arr_zero_out by lia. apply zset_same.
    + apply IH. lia.
Qed.

(** ** The parked package, projected for the walk *)

Section Pass1.

Variables (elems maxc1 M : Z) (t1 tf : Tree) (hp3 : zarr) (hmaxf ndf : Z).
Hypothesis Hpk : BtParked elems maxc1 t1 tf hp3 hmaxf ndf.
Hypothesis HM : 1 <= M <= 15.
Hypothesis Hmf0 : 0 <= hmaxf.
Variables (k base : Z) (extra : zarr) (stree : option Tree).

Let W := Z.to_nat (HEAP_SIZE - hmaxf).

Lemma pk_hmaxf_lt : hmaxf < HEAP_SIZE.
Proof.
  pose proof (bp_hmax _ _ _ _ _ _ _ Hpk) as Hh.
  pose proof (bp_ndf _ _ _ _ _ _ _ Hpk) as Hn.
  unfold HEAP_SIZE in *. lia.
Qed.

Lemma pk_window_hi : hmaxf + Z.of_nat W <= HEAP_SIZE.
Proof.
  pose proof pk_hmaxf_lt as Hlt.
  unfold W. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma pk_distinct : forall p q,
  hmaxf <= p < HEAP_SIZE -> hmaxf <= q < HEAP_SIZE -> p <> q ->
  hp3 p <> hp3 q.
Proof.
  pose proof (bp_cnt _ _ _ _ _ _ _ Hpk) as Hcnt.
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as Hmc.
  intros p q Hp Hq Hne.
  apply (wcount_le1_distinct hp3 hmaxf W).
  - intro x. unfold W. fold (pcount hp3 hmaxf x). rewrite Hcnt.
    apply total_le_1. lia.
  - unfold W. rewrite Z2Nat.id by lia. lia.
  - unfold W. rewrite Z2Nat.id by lia. lia.
  - exact Hne.
Qed.

Lemma pk_member_class : forall p, hmaxf <= p < HEAP_SIZE ->
  (0 <= hp3 p <= maxc1 /\ t_freq t1 (hp3 p) <> 0) \/ (elems <= hp3 p < ndf).
Proof.
  pose proof (bp_cnt _ _ _ _ _ _ _ Hpk) as Hcnt.
  intros p Hp.
  pose proof (pcount_member hp3 hmaxf p Hp) as Hm.
  rewrite Hcnt in Hm.
  destruct (live_b t1 maxc1 (hp3 p)) eqn:El.
  - left. unfold live_b in El.
    apply andb_prop in El as [El1 El2].
    apply andb_prop in El1 as [El1 El3].
    apply Z.leb_le in El1. apply Z.leb_le in El3.
    apply negb_true_iff, Z.eqb_neq in El2.
    auto.
  - right. cbn [ind] in Hm.
    destruct ((elems <=? hp3 p) && (hp3 p <? ndf)) eqn:Ec; [|cbn in Hm; lia].
    apply andb_prop in Ec as [Ec1 Ec2].
    apply Z.leb_le in Ec1. apply Z.ltb_lt in Ec2. auto.
Qed.

(** ** The walk invariant *)

Record Pass1Inv (h : Z) (t : Tree) (blc : zarr) (ov : Z) : Prop :=
mkPass1Inv {
  p1_len  : forall p, hmaxf + 1 <= p < h ->
            t_len t (hp3 p) = Z.min (t_len t (t_dad tf (hp3 p)) + 1) M;
  p1_root : t_len t (ndf - 1) = 0;
  p1_dadk : forall p, h <= p < HEAP_SIZE ->
            t_dad t (hp3 p) = t_dad tf (hp3 p);
  p1_rng  : forall p, hmaxf + 1 <= p < h -> 1 <= t_len t (hp3 p) <= M;
  p1_blc  : forall b, 0 <= b <= 15 ->
            blc b = wsum (fun p => ind ((hp3 p <=? maxc1)
                                        && (Z.eqb (t_len t (hp3 p)) b)))
                         (hmaxf + 1) (Z.to_nat (h - (hmaxf + 1)));
  p1_ov   : ov = wsum (fun p => ind (Z.eqb (t_len t (t_dad tf (hp3 p))) M))
                      (hmaxf + 1) (Z.to_nat (h - (hmaxf + 1)));
  p1_out  : forall y, pcount hp3 hmaxf y = 0 ->
            tr_dl t y = tr_dl (t_setlen tf (ndf - 1) 0) y;
  p1_zero : forall b, b < 1 \/ 15 < b -> blc b = 0
}.

Lemma pass1_entry : forall blc0,
  (forall b, blc0 b = 0) ->
  Pass1Inv (hmaxf + 1) (t_setlen tf (ndf - 1) 0) blc0 0.
Proof.
  intros blc0 Hb0.
  pose proof (bp_root _ _ _ _ _ _ _ Hpk) as Hroot.
  pose proof pk_hmaxf_lt as Hlt.
  constructor.
  - intros p Hp. lia.
  - unfold t_len, t_setlen. cbn [tr_dl]. rewrite zset_same. reflexivity.
  - intros p Hp.
    unfold t_dad, t_setlen. cbn [tr_dl].
    rewrite zset_other; [reflexivity|].
    rewrite <- Hroot. apply pk_distinct; lia.
  - intros p Hp. lia.
  - intros b Hb.
    replace (hmaxf + 1 - (hmaxf + 1)) with 0 by lia.
    cbn [Z.to_nat wsum]. apply Hb0.
  - replace (hmaxf + 1 - (hmaxf + 1)) with 0 by lia.
    cbn [Z.to_nat wsum]. reflexivity.
  - intros y _. reflexivity.
  - intros b _. apply Hb0.
Qed.


(** ** One visit *)

Lemma pass1_step : forall h t blc ov blc' bits,
  hmaxf + 1 <= h < HEAP_SIZE ->
  Pass1Inv h t blc ov ->
  bits = Z.min (t_len t (t_dad tf (hp3 h)) + 1) M ->
  ((maxc1 < hp3 h /\ blc' = blc)
   \/ (hp3 h <= maxc1
       /\ blc' = zset blc bits (u16 (blc bits + 1)))) ->
  Pass1Inv (h + 1) (t_setlen t (hp3 h) bits) blc'
           (ov + ind (Z.eqb (t_len t (t_dad tf (hp3 h))) M)).
Proof.
  intros h t blc ov blc' bits Hh Hinv Ebits Hcase.
  destruct Hinv as [Hlen Hroot Hdadk Hrng Hblc Hov Hout Hzero].
  pose proof pk_hmaxf_lt as Hwlt.
  set (x := hp3 h) in *.
  set (d := t_dad tf x) in *.
  (* the dad is parked strictly below, at a settled length *)
  destruct (bp_ord _ _ _ _ _ _ _ Hpk h ltac:(lia)) as [Hdr [p' [Hp' Hp'eq]]].
  fold x d in Hdr, Hp'eq.
  assert (Hdl : 0 <= t_len t d <= M).
  { destruct (Z.eq_dec p' hmaxf) as [Ehm|Hne].
    - rewrite <- Hp'eq, Ehm, (bp_root _ _ _ _ _ _ _ Hpk), Hroot. lia.
    - assert (1 <= t_len t (hp3 p') <= M) by (apply Hrng; lia).
      rewrite <- Hp'eq. lia. }
  assert (Hbits : 1 <= bits <= M) by (rewrite Ebits; lia).
  assert (Hdx : d <> x).
  { rewrite <- Hp'eq. apply pk_distinct; lia. }
  assert (Hxvis : forall p, hmaxf <= p < h -> hp3 p <> x)
    by (intros p Hp; apply pk_distinct; lia).
  assert (Hxafter : forall p, h + 1 <= p < HEAP_SIZE -> hp3 p <> x)
    by (intros p Hp; apply pk_distinct; lia).
  (* dads of any window node are parked below it, hence never equal to x
     unless x itself is that dad -- excluded position-wise for p < h *)
  assert (Hdadvis : forall p, hmaxf + 1 <= p < h -> t_dad tf (hp3 p) <> x).
  { intros p Hp.
    destruct (bp_ord _ _ _ _ _ _ _ Hpk p ltac:(lia)) as [_ [q [Hq Hqeq]]].
    rewrite <- Hqeq. apply pk_distinct; lia. }
  (* the write, seen through the two readers *)
  assert (Wlen_same : t_len (t_setlen t x bits) x = bits).
  { rewrite t_len_setlen_same'. unfold u16. apply Z.mod_small. lia. }
  assert (Wlen_other : forall y, y <> x -> t_len (t_setlen t x bits) y = t_len t y)
    by (intros y Hy; apply t_len_setlen_other'; exact Hy).
  assert (Wdad_other : forall y, y <> x -> t_dad (t_setlen t x bits) y = t_dad t y)
    by (intros y Hy; apply t_dad_setdad_other; exact Hy).
  (* window sizes *)
  assert (Hszs : Z.to_nat (h + 1 - (hmaxf + 1))
                 = S (Z.to_nat (h - (hmaxf + 1)))).
  { replace (h + 1 - (hmaxf + 1)) with (Z.succ (h - (hmaxf + 1))) by lia.
    rewrite Z2Nat.inj_succ by lia. reflexivity. }
  assert (Hpos : hmaxf + 1 + Z.of_nat (Z.to_nat (h - (hmaxf + 1))) = h)
    by (rewrite Z2Nat.id by lia; lia).
  constructor.
  - (* p1_len *)
    intros p Hp.
    destruct (Z.eq_dec p h) as [->|Hne].
    + fold x. fold d. rewrite Wlen_same, (Wlen_other d Hdx). exact Ebits.
    + assert (Hpw : hmaxf + 1 <= p < h) by lia.
      rewrite (Wlen_other (hp3 p) (Hxvis p ltac:(lia))).
      rewrite (Wlen_other (t_dad tf (hp3 p)) (Hdadvis p Hpw)).
      apply Hlen. exact Hpw.
  - (* p1_root *)
    assert (Hrx : ndf - 1 <> x).
    { rewrite <- (bp_root _ _ _ _ _ _ _ Hpk). apply pk_distinct; lia. }
    rewrite (Wlen_other _ Hrx). exact Hroot.
  - (* p1_dadk *)
    intros p Hp.
    rewrite (Wdad_other (hp3 p) (Hxafter p ltac:(lia))).
    apply Hdadk. lia.
  - (* p1_rng *)
    intros p Hp.
    destruct (Z.eq_dec p h) as [->|Hne].
    + fold x. rewrite Wlen_same. exact Hbits.
    + rewrite (Wlen_other (hp3 p) (Hxvis p ltac:(lia))). apply Hrng. lia.
  - (* p1_blc *)
    intros b Hb.
    rewrite Hszs, wsum_split_last, Hpos.
    assert (Htail :
      wsum (fun p => ind ((hp3 p <=? maxc1)
                          && (Z.eqb (t_len (t_setlen t x bits) (hp3 p)) b)))
           (hmaxf + 1) (Z.to_nat (h - (hmaxf + 1)))
      = wsum (fun p => ind ((hp3 p <=? maxc1)
                            && (Z.eqb (t_len t (hp3 p)) b)))
             (hmaxf + 1) (Z.to_nat (h - (hmaxf + 1)))).
    { apply wsum_ext. intros p Hp.
      rewrite (Wlen_other (hp3 p) (Hxvis p ltac:(lia))). reflexivity. }
    rewrite Htail, <- (Hblc b Hb).
    fold x. rewrite Wlen_same.
    destruct Hcase as [[Hint ->]|[Hleaf ->]].
    + (* internal: the new term vanishes *)
      replace (x <=? maxc1) with false
        by (symmetry; apply Z.leb_gt; lia).
      cbn [andb ind]. lia.
    + (* leaf: the new term is the write *)
      replace (x <=? maxc1) with true
        by (symmetry; apply Z.leb_le; lia).
      cbn [andb].
      assert (Hub : blc bits <= 573).
      { rewrite (Hblc bits ltac:(lia)).
        pose proof (wsum_ind_ub
          (fun p => (hp3 p <=? maxc1) && (Z.eqb (t_len t (hp3 p)) bits))
          (hmaxf + 1) (Z.to_nat (h - (hmaxf + 1)))) as HB.
        assert (Z.of_nat (Z.to_nat (h - (hmaxf + 1))) <= 573)
          by (rewrite Z2Nat.id by lia; unfold HEAP_SIZE in *; lia).
        lia. }
      assert (Hlb : 0 <= blc bits).
      { rewrite (Hblc bits ltac:(lia)).
        apply wsum_nonneg. intros i _. apply ind_0_1. }
      destruct (Z.eq_dec b bits) as [->|Hne].
      * rewrite zset_same. unfold u16. rewrite Z.mod_small by lia.
        rewrite Z.eqb_refl. cbn [ind]. lia.
      * rewrite zset_other by (auto using not_eq_sym).
        replace (Z.eqb bits b) with false
          by (symmetry; apply Z.eqb_neq; auto using not_eq_sym).
        cbn [ind]. lia.
  - (* p1_ov *)
    rewrite Hszs, wsum_split_last, Hpos.
    assert (Htail :
      wsum (fun p => ind (Z.eqb (t_len (t_setlen t x bits)
                                        (t_dad tf (hp3 p))) M))
           (hmaxf + 1) (Z.to_nat (h - (hmaxf + 1)))
      = wsum (fun p => ind (Z.eqb (t_len t (t_dad tf (hp3 p))) M))
             (hmaxf + 1) (Z.to_nat (h - (hmaxf + 1)))).
    { apply wsum_ext. intros p Hp.
      rewrite (Wlen_other (t_dad tf (hp3 p)) (Hdadvis p ltac:(lia))).
      reflexivity. }
    rewrite Htail, <- Hov.
    fold x d. rewrite (Wlen_other d Hdx). reflexivity.
  - (* p1_out *)
    intros y Hy.
    assert (Hyx : y <> x).
    { intro He. subst y.
      pose proof (pcount_member hp3 hmaxf h ltac:(lia)) as Hm.
      fold x in Hm. lia. }
    unfold t_setlen. cbn [tr_dl]. rewrite zset_other by exact Hyx.
    apply Hout. exact Hy.
  - (* p1_zero: the one histogram write lands inside [1, 15] *)
    intros b Hb.
    destruct Hcase as [[Hint ->]|[Hleaf ->]].
    + apply Hzero. exact Hb.
    + rewrite zset_other by lia. apply Hzero. exact Hb.
Qed.


Lemma pass1_dad_len : forall h t blc ov,
  hmaxf + 1 <= h < HEAP_SIZE ->
  Pass1Inv h t blc ov ->
  0 <= t_len t (t_dad tf (hp3 h)) <= M.
Proof.
  intros h t blc ov Hh Hinv.
  pose proof pk_hmaxf_lt as Hwlt.
  destruct Hinv as [Hlen Hroot Hdadk Hrng Hblc Hov Hout Hzero].
  destruct (bp_ord _ _ _ _ _ _ _ Hpk h ltac:(lia)) as [Hdr [p' [Hp' Hp'eq]]].
  destruct (Z.eq_dec p' hmaxf) as [Ehm|Hne].
  - rewrite <- Hp'eq, Ehm, (bp_root _ _ _ _ _ _ _ Hpk), Hroot. lia.
  - assert (1 <= t_len t (hp3 p') <= M) by (apply Hrng; lia).
    rewrite <- Hp'eq. lia.
Qed.

(** ** The walk *)

Lemma pass1_walk : forall fuel h t blc ol sl ov,
  hmaxf + 1 <= h <= HEAP_SIZE ->
  HEAP_SIZE - h <= Z.of_nat fuel ->
  Pass1Inv h t blc ov ->
  match gb_pass1 fuel k hp3 maxc1 M base extra stree h t blc ol sl ov with
  | (t2, blc2, ol2, sl2, ov2) => Pass1Inv HEAP_SIZE t2 blc2 ov2
  end.
Proof.
  induction fuel as [|f IH]; intros h t blc ol sl ov Hh Hf Hinv.
  - cbn [gb_pass1]. cbn [Z.of_nat] in Hf.
    replace HEAP_SIZE with h by lia. exact Hinv.
  - cbn [gb_pass1].
    destruct (Z.leb HEAP_SIZE h) eqn:Eg.
    + apply Z.leb_le in Eg. replace HEAP_SIZE with h by lia. exact Hinv.
    + apply Z.leb_gt in Eg.
      rewrite Nat2Z.inj_succ in Hf.
      assert (Hdx : t_dad t (hp3 h) = t_dad tf (hp3 h))
        by (apply (p1_dadk h t blc ov Hinv); lia).
      rewrite Hdx.
      rewrite !if_ltb_min.
      pose proof (pass1_dad_len h t blc ov ltac:(lia) Hinv) as Hdl.
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
        eapply pass1_step; [lia | exact Hinv | reflexivity |].
        left. auto.
      * apply Z.ltb_ge in El.
        apply IH; [lia | lia |].
        eapply pass1_step; [lia | exact Hinv | reflexivity |].
        right. auto.
Qed.

End Pass1.

Print Assumptions pass1_entry.
Print Assumptions pass1_step.
Print Assumptions pass1_walk.
