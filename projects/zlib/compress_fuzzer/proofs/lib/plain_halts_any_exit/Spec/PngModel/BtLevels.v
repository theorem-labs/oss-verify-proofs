(** * BtLevels — per-level counts of the built tree satisfy the binary-tree
      recurrences, and the histogram Kraft sum lands at [2^M + overflow/2].

    OWNER: an earlier development run.

    The walk (BtPass1) left four POINTWISE facts on the final tree: each
    node's length is [min (len dad + 1, M)], the root sits at 0, the
    histogram counts the leaves, and [overflow] counts the nodes whose dad
    sits at level [M].  This file turns those into LEVEL EQUATIONS by one
    Fubini step over the parked window — "sum over nodes of [dad at level c]"
    equals "sum over internals at level c of their child count", and the
    child count is the census's exactly-two — and then telescopes:

        zksum M blc = 2^M + VI(M),   ov = 2*VI(M),   blc M = 2*VI(M-1) + VI(M)

    where [VI(b)] counts internal nodes at level [b].  The [ov = 0] branch is
    the same statement with [VI(M) = 0]: Kraft EQUALITY either way after
    [gb_adjust] removes exactly [VI(M)] (KraftAdjust, ported). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus1 BtCensus2 BtCensus3 BtCensus4 BtPass1 KraftAdjust.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Sum algebra *)

Lemma wsum_zero : forall lo n, wsum (fun _ : Z => 0) lo n = 0.
Proof.
  intros lo n; revert lo.
  induction n as [|k IH]; intro lo; cbn [wsum]; [reflexivity|].
  rewrite IH. lia.
Qed.

Lemma wsum_add : forall f g lo n,
  wsum (fun i => f i + g i) lo n = wsum f lo n + wsum g lo n.
Proof.
  intros f g lo n; revert lo.
  induction n as [|k IH]; intro lo; cbn [wsum]; [lia|].
  rewrite IH. lia.
Qed.

Lemma wsum_scale_r : forall f c lo n,
  wsum (fun i => f i * c) lo n = wsum f lo n * c.
Proof.
  intros f c lo n; revert lo.
  induction n as [|k IH]; intro lo; cbn [wsum]; [lia|].
  rewrite IH. lia.
Qed.

Lemma wsum_swap : forall (f : Z -> Z -> Z) lo1 n1 lo2 n2,
  wsum (fun p => wsum (fun q => f p q) lo2 n2) lo1 n1
  = wsum (fun q => wsum (fun p => f p q) lo1 n1) lo2 n2.
Proof.
  intros f lo1 n1; revert lo1.
  induction n1 as [|k IH]; intros lo1 lo2 n2.
  - cbn [wsum]. symmetry. apply wsum_zero.
  - cbn [wsum].
    rewrite (IH (lo1 + 1) lo2 n2).
    rewrite <- wsum_add.
    apply wsum_ext. intros q _. cbn [wsum]. reflexivity.
Qed.

(** Collapsing a sum against a value that occurs EXACTLY ONCE. *)
Lemma wsum_pick : forall (a : zarr) lo n (d gv : Z) (g : Z -> Z),
  wcount a lo n d = 1 ->
  (forall p, lo <= p < lo + Z.of_nat n -> a p = d -> g p = gv) ->
  wsum (fun p => ind (Z.eqb (a p) d) * g p) lo n = gv.
Proof.
  intros a lo n; revert lo.
  induction n as [|k IH]; intros lo d gv g Hc Hg.
  - unfold wcount in Hc. cbn [wsum] in *. lia.
  - unfold wcount in Hc. cbn [wsum] in *.
    fold (wcount a (lo + 1) k d) in Hc.
    rewrite Nat2Z.inj_succ in Hg.
    destruct (Z.eqb (a lo) d) eqn:Ed.
    + apply Z.eqb_eq in Ed.
      cbn [ind] in *.
      assert (Htail0 : wcount a (lo + 1) k d = 0) by lia.
      assert (Hz : wsum (fun p => ind (Z.eqb (a p) d) * g p) (lo + 1) k = 0).
      { rewrite <- (wsum_zero (lo + 1) k).
        apply wsum_ext. intros p Hp.
        destruct (Z.eqb (a p) d) eqn:Ep.
        - apply Z.eqb_eq in Ep. exfalso.
          pose proof (wcount_of_member a (lo + 1) k d p Hp Ep). lia.
        - cbn [ind]. lia. }
      rewrite Hz, (Hg lo ltac:(lia) Ed). lia.
    + cbn [ind] in *.
      rewrite (IH (lo + 1) d gv g ltac:(lia)
                 (fun p Hp => Hg p ltac:(lia))).
      lia.
Qed.

(** ** The list side: [zksum_over] over an append *)

Lemma zksum_over_app : forall M blc l1 l2,
  zksum_over M blc (l1 ++ l2) = zksum_over M blc l1 + zksum_over M blc l2.
Proof.
  intros M blc l1 l2.
  induction l1 as [|a l1 IH]; cbn [app].
  - rewrite zksum_over_nil. lia.
  - rewrite !zksum_over_cons, IH. lia.
Qed.

(** ** The telescope *)

Lemma kraft_telescope : forall (Iv : Z -> Z) (M : Z) (blc : zarr),
  1 <= M ->
  (forall b, 1 <= b <= M - 1 -> blc b + Iv b = 2 * Iv (b - 1)) ->
  Iv 0 = 1 ->
  blc M = 2 * Iv (M - 1) + Iv M ->
  zksum M blc = 2 ^ M + Iv M.
Proof.
  intros Iv M blc HM Heq H0 HbM.
  assert (Hpart : forall j : nat, Z.of_nat j <= M - 1 ->
    zksum_over M blc (seq 1 j) + Iv (Z.of_nat j) * 2 ^ (M - Z.of_nat j)
    = 2 ^ M).
  { induction j as [|j IH]; intro Hj.
    - cbn [seq]. rewrite zksum_over_nil.
      cbn [Z.of_nat]. rewrite H0, Z.sub_0_r. lia.
    - rewrite Nat2Z.inj_succ in *.
      rewrite seq_S, zksum_over_app, zksum_over_cons, zksum_over_nil.
      cbn [Z.of_nat].
      replace (Z.of_nat (1 + j)) with (Z.succ (Z.of_nat j)) by lia.
      specialize (IH ltac:(lia)).
      specialize (Heq (Z.succ (Z.of_nat j)) ltac:(lia)).
      replace (Z.succ (Z.of_nat j) - 1) with (Z.of_nat j) in Heq by lia.
      assert (Hpow : 2 ^ (M - Z.of_nat j)
                     = 2 * 2 ^ (M - Z.succ (Z.of_nat j))).
      { replace (M - Z.of_nat j) with (1 + (M - Z.succ (Z.of_nat j))) by lia.
        rewrite Z.pow_add_r by lia. lia. }
      rewrite Hpow in IH. nia. }
  unfold zksum.
  assert (HtoM : Z.to_nat M = S (Z.to_nat (M - 1)))
    by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
  rewrite HtoM, seq_S, zksum_over_app, zksum_over_cons, zksum_over_nil.
  specialize (Hpart (Z.to_nat (M - 1)) ltac:(rewrite Z2Nat.id by lia; lia)).
  rewrite Z2Nat.id in Hpart by lia.
  replace (Z.of_nat (1 + Z.to_nat (M - 1))) with M
    by (rewrite Nat2Z.inj_add, Z2Nat.id by lia; lia).
  replace (M - (M - 1)) with 1 in Hpart by lia.
  replace (2 ^ 1) with 2 in Hpart by reflexivity.
  rewrite HbM.
  replace (M - M) with 0 by lia.
  replace (2 ^ 0) with 1 by reflexivity.
  lia.
Qed.

Print Assumptions wsum_swap.
Print Assumptions wsum_pick.
Print Assumptions kraft_telescope.

(** ** The level counts of the built tree *)

Section Levels.

Variables (elems maxc1 M : Z) (t1 tf : Tree) (hp3 : zarr) (hmaxf ndf : Z).
Hypothesis Hpk : BtParked elems maxc1 t1 tf hp3 hmaxf ndf.
Hypothesis HM : 1 <= M <= 15.
Hypothesis Hmf0 : 0 <= hmaxf.
Variables (t2 : Tree) (blc1 : zarr) (ov : Z).
Hypothesis Hfin : Pass1Inv maxc1 M tf hp3 hmaxf ndf HEAP_SIZE t2 blc1 ov.

(** Internal (= created) nodes at level [b], root included. *)
Definition VIc (b : Z) : Z :=
  wsum (fun p => ind ((elems <=? hp3 p) && (Z.eqb (t_len t2 (hp3 p)) b)))
       hmaxf (Z.to_nat (HEAP_SIZE - hmaxf)).

Let NW := Z.to_nat (HEAP_SIZE - (hmaxf + 1)).

Lemma lv_hlt : hmaxf < HEAP_SIZE.
Proof. exact (pk_hmaxf_lt _ _ _ _ _ _ _ Hpk). Qed.

Lemma lv_size : Z.to_nat (HEAP_SIZE - hmaxf) = S NW.
Proof.
  pose proof lv_hlt.
  unfold NW.
  replace (HEAP_SIZE - hmaxf) with (Z.succ (HEAP_SIZE - (hmaxf + 1))) by lia.
  rewrite Z2Nat.inj_succ by lia. reflexivity.
Qed.

Lemma lv_nw_hi : hmaxf + 1 + Z.of_nat NW = HEAP_SIZE.
Proof. pose proof lv_hlt. unfold NW. rewrite Z2Nat.id by lia. lia. Qed.

(** Per-node facts on the non-root window. *)
Lemma lv_q_facts : forall q, hmaxf + 1 <= q < HEAP_SIZE ->
  elems <= t_dad tf (hp3 q) < ndf
  /\ wcount hp3 hmaxf (S NW) (t_dad tf (hp3 q)) = 1
  /\ t_len t2 (hp3 q) = Z.min (t_len t2 (t_dad tf (hp3 q)) + 1) M
  /\ 0 <= t_len t2 (t_dad tf (hp3 q)) <= M.
Proof.
  intros q Hq.
  pose proof lv_hlt as Hlt.
  destruct Hfin as [Hlen Hroot Hdadk Hrng Hblc Hov Hout Hzero].
  destruct (bp_ord _ _ _ _ _ _ _ Hpk q ltac:(lia)) as [Hdr [p' [Hp' Hp'eq]]].
  split; [exact Hdr|]. split.
  - rewrite <- lv_size.
    fold (pcount hp3 hmaxf (t_dad tf (hp3 q))).
    rewrite (bp_cnt _ _ _ _ _ _ _ Hpk (t_dad tf (hp3 q))).
    rewrite (live_b_false_high t1 maxc1 (t_dad tf (hp3 q)))
      by (pose proof (bp_maxc _ _ _ _ _ _ _ Hpk); lia).
    replace ((elems <=? t_dad tf (hp3 q)) && (t_dad tf (hp3 q) <? ndf))
      with true
      by (symmetry; apply andb_true_intro;
          split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
    reflexivity.
  - split.
    + apply Hlen. lia.
    + destruct (Z.eq_dec p' hmaxf) as [Ehm|Hne].
      * rewrite <- Hp'eq, Ehm, (bp_root _ _ _ _ _ _ _ Hpk), Hroot. lia.
      * assert (1 <= t_len t2 (hp3 p') <= M) by (apply Hrng; lia).
        rewrite <- Hp'eq. lia.
Qed.

(** The Fubini step: children of level-[c] internals, counted two ways. *)
Lemma lv_SC : forall c,
  wsum (fun q => ind (Z.eqb (t_len t2 (t_dad tf (hp3 q))) c))
       (hmaxf + 1) NW
  = 2 * VIc c.
Proof.
  intro c.
  pose proof lv_hlt as Hlt.
  set (g := fun p => ind ((elems <=? hp3 p) && (Z.eqb (t_len t2 (hp3 p)) c))).
  (* each summand is a pick over the full window *)
  assert (Hpt : forall q, hmaxf + 1 <= q < hmaxf + 1 + Z.of_nat NW ->
    ind (Z.eqb (t_len t2 (t_dad tf (hp3 q))) c)
    = wsum (fun p => ind (Z.eqb (hp3 p) (t_dad tf (hp3 q))) * g p)
           hmaxf (S NW)).
  { intros q Hq.
    rewrite lv_nw_hi in Hq.
    destruct (lv_q_facts q Hq) as [Hdr [Hone [_ _]]].
    symmetry.
    apply (wsum_pick hp3 hmaxf (S NW) (t_dad tf (hp3 q))
             (ind (Z.eqb (t_len t2 (t_dad tf (hp3 q))) c)) g Hone).
    intros p Hp Heq. unfold g. rewrite Heq.
    replace (elems <=? t_dad tf (hp3 q)) with true
      by (symmetry; apply Z.leb_le; lia).
    reflexivity. }
  rewrite (wsum_ext _ _ (hmaxf + 1) NW Hpt).
  rewrite (wsum_swap (fun q p => ind (Z.eqb (hp3 p) (t_dad tf (hp3 q))) * g p)
             (hmaxf + 1) NW hmaxf (S NW)).
  (* at each window slot, the inner sum is the census times the level flag *)
  assert (Hin : forall p, hmaxf <= p < hmaxf + Z.of_nat (S NW) ->
    wsum (fun q => ind (Z.eqb (hp3 p) (t_dad tf (hp3 q))) * g p)
         (hmaxf + 1) NW
    = g p * 2 * ind ((elems <=? hp3 p) && (hp3 p <? ndf))).
  { intros p Hp.
    rewrite (wsum_ext _ (fun q => ind (Z.eqb (t_dad tf (hp3 q)) (hp3 p)) * g p)
               (hmaxf + 1) NW)
      by (intros q _; rewrite (Z.eqb_sym (hp3 p)); reflexivity).
    rewrite wsum_scale_r.
    unfold NW.
    rewrite (bp_dad _ _ _ _ _ _ _ Hpk (hp3 p)).
    lia. }
  rewrite (wsum_ext _ _ hmaxf (S NW) Hin).
  (* collapse the created flag into g *)
  assert (Hcol : forall p, hmaxf <= p < hmaxf + Z.of_nat (S NW) ->
    g p * 2 * ind ((elems <=? hp3 p) && (hp3 p <? ndf)) = g p * 2).
  { intros p Hp.
    assert (Hp' : hmaxf <= p < HEAP_SIZE)
      by (rewrite <- lv_size in Hp; rewrite Z2Nat.id in Hp by lia; lia).
    destruct (pk_member_class _ _ _ _ _ _ _ Hpk p Hp') as [[Hlv _]|Hcr].
    - unfold g.
      replace (elems <=? hp3 p) with false
        by (symmetry; apply Z.leb_gt;
            pose proof (bp_maxc _ _ _ _ _ _ _ Hpk); lia).
      cbn [andb ind]. lia.
    - replace ((elems <=? hp3 p) && (hp3 p <? ndf)) with true
        by (symmetry; apply andb_true_intro;
            split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
      cbn [ind]. lia. }
  rewrite (wsum_ext _ _ hmaxf (S NW) Hcol).
  rewrite (wsum_ext (fun p => g p * 2) (fun p => g p + g p) hmaxf (S NW))
    by (intros; lia).
  rewrite wsum_add.
  unfold VIc, g. rewrite lv_size. lia.
Qed.

(** Root split and the low levels. *)
Lemma lv_VIc0 : VIc 0 = 1.
Proof.
  pose proof lv_hlt as Hlt.
  destruct Hfin as [Hlen Hroot Hdadk Hrng Hblc Hov Hout Hzero].
  unfold VIc. rewrite lv_size, wsum_split_first.
  rewrite (bp_root _ _ _ _ _ _ _ Hpk), Hroot.
  replace (elems <=? ndf - 1) with true
    by (symmetry; apply Z.leb_le;
        pose proof (bp_ndf _ _ _ _ _ _ _ Hpk); lia).
  rewrite Z.eqb_refl. cbn [andb ind].
  assert (Hz : wsum (fun p => ind ((elems <=? hp3 p)
                                   && (Z.eqb (t_len t2 (hp3 p)) 0)))
                    (hmaxf + 1) NW = 0).
  { transitivity (wsum (fun _ : Z => 0) (hmaxf + 1) NW);
      [apply wsum_ext | apply wsum_zero].
    intros p Hp.
    rewrite lv_nw_hi in Hp.
    assert (1 <= t_len t2 (hp3 p) <= M) by (apply Hrng; lia).
    replace (Z.eqb (t_len t2 (hp3 p)) 0) with false
      by (symmetry; apply Z.eqb_neq; lia).
    rewrite andb_false_r. reflexivity. }
  rewrite Hz. lia.
Qed.

Lemma lv_VIc_pos : forall b, 1 <= b ->
  VIc b = wsum (fun p => ind ((elems <=? hp3 p)
                              && (Z.eqb (t_len t2 (hp3 p)) b)))
               (hmaxf + 1) NW.
Proof.
  intros b Hb.
  pose proof lv_hlt as Hlt.
  destruct Hfin as [Hlen Hroot Hdadk Hrng Hblc Hov Hout Hzero].
  unfold VIc. rewrite lv_size, wsum_split_first.
  rewrite (bp_root _ _ _ _ _ _ _ Hpk), Hroot.
  replace (Z.eqb 0 b) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite andb_false_r. cbn [ind]. lia.
Qed.

Lemma lv_VIc_nonneg : forall b, 0 <= VIc b.
Proof.
  intro b. unfold VIc. apply wsum_nonneg. intros i _. apply ind_0_1.
Qed.


(** The class split: every window node is a leaf or an internal, never both. *)
Lemma lv_N_split : forall b, 0 <= b <= 15 ->
  wsum (fun q => ind (Z.eqb (t_len t2 (hp3 q)) b)) (hmaxf + 1) NW
  = blc1 b
    + wsum (fun q => ind ((elems <=? hp3 q)
                          && (Z.eqb (t_len t2 (hp3 q)) b)))
           (hmaxf + 1) NW.
Proof.
  intros b Hb.
  pose proof lv_hlt as Hlt.
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as Hmc.
  destruct Hfin as [Hlen Hroot Hdadk Hrng Hblc Hov Hout Hzero].
  rewrite (Hblc b Hb).
  fold NW.
  rewrite <- wsum_add.
  apply wsum_ext. intros q Hq.
  rewrite lv_nw_hi in Hq.
  assert (Hq' : hmaxf <= q < HEAP_SIZE) by lia.
  destruct (pk_member_class _ _ _ _ _ _ _ Hpk q Hq') as [[Hlv _]|Hcr].
  - replace (hp3 q <=? maxc1) with true by (symmetry; apply Z.leb_le; lia).
    replace (elems <=? hp3 q) with false by (symmetry; apply Z.leb_gt; lia).
    cbn [andb ind]. lia.
  - replace (hp3 q <=? maxc1) with false by (symmetry; apply Z.leb_gt; lia).
    replace (elems <=? hp3 q) with true by (symmetry; apply Z.leb_le; lia).
    cbn [andb ind]. lia.
Qed.

(** The two level equations. *)
Lemma lv_level_eq : forall b, 1 <= b <= M - 1 ->
  blc1 b + VIc b = 2 * VIc (b - 1).
Proof.
  intros b Hb.
  pose proof (lv_SC (b - 1)) as H1.
  pose proof (lv_VIc_pos b ltac:(lia)) as HV.
  pose proof (lv_N_split b ltac:(lia)) as HS.
  assert (HN : wsum (fun q => ind (Z.eqb (t_len t2 (hp3 q)) b))
                    (hmaxf + 1) NW
               = wsum (fun q => ind (Z.eqb (t_len t2 (t_dad tf (hp3 q)))
                                           (b - 1)))
                      (hmaxf + 1) NW).
  { apply wsum_ext. intros q Hq.
    rewrite lv_nw_hi in Hq.
    destruct (lv_q_facts q ltac:(lia)) as [_ [_ [Hmin Hld]]].
    destruct (Z.eq_dec (t_len t2 (t_dad tf (hp3 q))) (b - 1)) as [Ea|Ea].
    - replace (Z.eqb (t_len t2 (hp3 q)) b) with true
        by (symmetry; apply Z.eqb_eq; lia).
      replace (Z.eqb (t_len t2 (t_dad tf (hp3 q))) (b - 1)) with true
        by (symmetry; apply Z.eqb_eq; lia).
      reflexivity.
    - replace (Z.eqb (t_len t2 (hp3 q)) b) with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.eqb (t_len t2 (t_dad tf (hp3 q))) (b - 1)) with false
        by (symmetry; apply Z.eqb_neq; lia).
      reflexivity. }
  lia.
Qed.

Lemma lv_level_eqM :
  blc1 M + VIc M = 2 * VIc (M - 1) + 2 * VIc M.
Proof.
  pose proof (lv_SC (M - 1)) as H1.
  pose proof (lv_SC M) as H2.
  pose proof (lv_VIc_pos M ltac:(lia)) as HV.
  pose proof (lv_N_split M ltac:(lia)) as HS.
  assert (HN : wsum (fun q => ind (Z.eqb (t_len t2 (hp3 q)) M))
                    (hmaxf + 1) NW
               = wsum (fun q => ind (Z.eqb (t_len t2 (t_dad tf (hp3 q)))
                                           (M - 1)))
                      (hmaxf + 1) NW
                 + wsum (fun q => ind (Z.eqb (t_len t2 (t_dad tf (hp3 q))) M))
                        (hmaxf + 1) NW).
  { rewrite <- wsum_add. apply wsum_ext. intros q Hq.
    rewrite lv_nw_hi in Hq.
    destruct (lv_q_facts q ltac:(lia)) as [_ [_ [Hmin Hld]]].
    destruct (Z.eq_dec (t_len t2 (t_dad tf (hp3 q))) (M - 1)) as [Ea|Ea];
      destruct (Z.eq_dec (t_len t2 (t_dad tf (hp3 q))) M) as [Eb|Eb].
    - lia.
    - replace (Z.eqb (t_len t2 (hp3 q)) M) with true
        by (symmetry; apply Z.eqb_eq; lia).
      replace (Z.eqb (t_len t2 (t_dad tf (hp3 q))) (M - 1)) with true
        by (symmetry; apply Z.eqb_eq; lia).
      replace (Z.eqb (t_len t2 (t_dad tf (hp3 q))) M) with false
        by (symmetry; apply Z.eqb_neq; lia).
      cbn [ind]. lia.
    - replace (Z.eqb (t_len t2 (hp3 q)) M) with true
        by (symmetry; apply Z.eqb_eq; lia).
      replace (Z.eqb (t_len t2 (t_dad tf (hp3 q))) (M - 1)) with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.eqb (t_len t2 (t_dad tf (hp3 q))) M) with true
        by (symmetry; apply Z.eqb_eq; lia).
      cbn [ind]. lia.
    - replace (Z.eqb (t_len t2 (hp3 q)) M) with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.eqb (t_len t2 (t_dad tf (hp3 q))) (M - 1)) with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.eqb (t_len t2 (t_dad tf (hp3 q))) M) with false
        by (symmetry; apply Z.eqb_neq; lia).
      cbn [ind]. lia. }
  lia.
Qed.

Lemma lv_ov : ov = 2 * VIc M.
Proof.
  destruct Hfin as [Hlen Hroot Hdadk Hrng Hblc Hov Hout Hzero].
  rewrite Hov. fold NW. apply lv_SC.
Qed.

(** Histogram bounds, for the adjust chain. *)
Lemma lv_blc_bounds : forall b, 0 <= b <= 15 -> 0 <= blc1 b <= 573.
Proof.
  intros b Hb.
  pose proof lv_hlt as Hlt.
  destruct Hfin as [Hlen Hroot Hdadk Hrng Hblc Hov Hout Hzero].
  rewrite (Hblc b Hb).
  split.
  - apply wsum_nonneg. intros i _. apply ind_0_1.
  - pose proof (wsum_ind_ub
      (fun p => (hp3 p <=? maxc1) && (Z.eqb (t_len t2 (hp3 p)) b))
      (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))) as HB.
    assert (Z.of_nat (Z.to_nat (HEAP_SIZE - (hmaxf + 1))) <= 573)
      by (rewrite Z2Nat.id by lia; unfold HEAP_SIZE in *; lia).
    lia.
Qed.

Lemma lv_blc_high : forall b, M < b <= 15 -> blc1 b = 0.
Proof.
  intros b Hb.
  pose proof lv_hlt as Hlt.
  destruct Hfin as [Hlen Hroot Hdadk Hrng Hblc Hov Hout Hzero].
  rewrite (Hblc b ltac:(lia)).
  transitivity (wsum (fun _ : Z => 0) (hmaxf + 1)
                  (Z.to_nat (HEAP_SIZE - (hmaxf + 1))));
    [apply wsum_ext | apply wsum_zero].
  intros p Hp.
  assert (Hpw : hmaxf + 1 <= p < HEAP_SIZE).
  { split; [lia|]. destruct Hp as [_ Hp2].
    rewrite Z2Nat.id in Hp2 by lia. lia. }
  assert (1 <= t_len t2 (hp3 p) <= M) by (apply Hrng; lia).
  replace (Z.eqb (t_len t2 (hp3 p)) b) with false
    by (symmetry; apply Z.eqb_neq; lia).
  rewrite andb_false_r. reflexivity.
Qed.

(** ** THE KRAFT SUM AT [gb_pass1]'s EXIT *)

Theorem pass1_kraft :
  zksum M blc1 = 2 ^ M + VIc M
  /\ ov = 2 * VIc M
  /\ blc1 M = 2 * VIc (M - 1) + VIc M
  /\ 0 <= VIc (M - 1) /\ 0 <= VIc M.
Proof.
  assert (HbM : blc1 M = 2 * VIc (M - 1) + VIc M)
    by (pose proof lv_level_eqM; lia).
  repeat split; try apply lv_VIc_nonneg; try exact HbM; try exact lv_ov.
  apply (kraft_telescope VIc M blc1); [lia | | exact lv_VIc0 | exact HbM].
  exact lv_level_eq.
Qed.

End Levels.

Print Assumptions lv_SC.
Print Assumptions lv_level_eq.
Print Assumptions lv_level_eqM.
Print Assumptions pass1_kraft.
