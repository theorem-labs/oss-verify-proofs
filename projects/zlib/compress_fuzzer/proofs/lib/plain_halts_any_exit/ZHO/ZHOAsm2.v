(** * ZHOAsm2 — level census of the parked forest (L4 delta grind, leg alpha).

    OWNER: huffman-opt (fork).

    From the delta lemma's own premise set (BtParked's binarity bp_dad +
    census bp_cnt/bp_ord/bp_root + pass 1's min-chain len equation), the
    per-level census identity

        blc1 j + I j = 2 * I (j-1)      (1 <= j <= 14, I 0 = 1)

    where [I b] counts parked INTERNAL nodes of len b, its telescoped
    Kraft form, and the internal-witness fact I j >= 1 whenever a len-15
    leaf exists.  These kill every shallow-tail case of the walk (the
    mod-2^(15-ltr) granularity argument in ZHODELTA-PLAN.md).

    TRUST BOUNDARY: pure Gallina over the model + Stdlib. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees BtWin BtCensus2 BtCensus3 BtCensus4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ZHO Require Import ZHOCT ZHODelta ZHOAsm.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Section ZHOCensus.

Variables (elems maxc1 : Z) (tE tL t2 : Tree) (hp3 : zarr)
          (hmaxf ndf : Z) (blc1 : zarr).
Hypothesis Hpk : BtParked elems maxc1 tE tL hp3 hmaxf ndf.
Hypothesis Hel : 0 < elems <= L_CODES.
Hypothesis Hmc : maxc1 < elems.
Hypothesis Hmf0 : 0 <= hmaxf.
Hypothesis Hp1len : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
  t_len t2 (hp3 p) = Z.min (t_len t2 (t_dad tL (hp3 p)) + 1) 15.
Hypothesis Hp1root : t_len t2 (ndf - 1) = 0.
Hypothesis Hp1rng : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
  1 <= t_len t2 (hp3 p) <= 15.
Hypothesis Hblc : forall b, 0 <= b <= 15 ->
  blc1 b = wsum (fun p => ind ((hp3 p <=? maxc1)
                               && (Z.eqb (t_len t2 (hp3 p)) b)))
             (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1))).

(** parked internals (created nodes) of len [b], over the FULL window
    including the root slot *)
Definition zc_I (b : Z) : Z :=
  wsum (fun q => ind ((maxc1 <? hp3 q) && (Z.eqb (t_len t2 (hp3 q)) b)))
    hmaxf (Z.to_nat (HEAP_SIZE - hmaxf)).

Lemma zc_hmaxf_ub : hmaxf + 1 < HEAP_SIZE.
Proof.
  pose proof (bp_hmax _ _ _ _ _ _ _ Hpk).
  pose proof (bp_ndf _ _ _ _ _ _ _ Hpk).
  unfold HEAP_SIZE, L_CODES in *. lia.
Qed.

Lemma zc_root : hp3 hmaxf = ndf - 1.
Proof. exact (bp_root _ _ _ _ _ _ _ Hpk). Qed.

(** window value classification *)
Lemma zc_class : forall p, hmaxf <= p < HEAP_SIZE ->
  (0 <= hp3 p <= maxc1) \/ (elems <= hp3 p < ndf).
Proof.
  intros p Hp.
  pose proof (pcount_member hp3 hmaxf p Hp) as Hm.
  pose proof (bp_cnt _ _ _ _ _ _ _ Hpk (hp3 p)) as Hc.
  destruct (live_b tE maxc1 (hp3 p)) eqn:El.
  - unfold live_b in El.
    apply andb_prop in El as [El1 _].
    apply andb_prop in El1 as [El1 El2].
    apply Z.leb_le in El1. apply Z.leb_le in El2. left. lia.
  - cbn [ind] in Hc.
    destruct ((elems <=? hp3 p) && (hp3 p <? ndf)) eqn:Ec;
      [|cbn [ind] in Hc; lia].
    apply andb_prop in Ec as [Ec1 Ec2].
    apply Z.leb_le in Ec1. apply Z.ltb_lt in Ec2. right. lia.
Qed.

(** dads of window children are parked created values, at an earlier
    slot; and their lens are nonnegative *)
Lemma zc_dad_facts : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
  elems <= t_dad tL (hp3 p) < ndf
  /\ 0 <= t_len t2 (t_dad tL (hp3 p)).
Proof.
  intros p Hp.
  destruct (bp_ord _ _ _ _ _ _ _ Hpk p Hp) as (Hdr & q & Hq & Eq).
  split; [exact Hdr|].
  destruct (Z.eqb_spec q hmaxf) as [->|Hne].
  - rewrite <- Eq, zc_root, Hp1root. lia.
  - rewrite <- Eq. pose proof (Hp1rng q ltac:(lia)). lia.
Qed.

(** the created value at a slot has pcount 1 *)
Lemma zc_pcount_created : forall c, elems <= c < ndf ->
  pcount hp3 hmaxf c = 1.
Proof.
  intros c Hc.
  pose proof (bp_cnt _ _ _ _ _ _ _ Hpk c) as H.
  unfold live_b in H.
  replace (c <=? maxc1) with false in H
    by (symmetry; apply Z.leb_gt; lia).
  rewrite andb_false_r in H. cbn [andb ind] in H.
  replace ((elems <=? c) && (c <? ndf)) with true in H
    by (symmetry; apply andb_true_iff;
        split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
  cbn [ind] in H. lia.
Qed.

(** I 0 = 1: the root and only the root *)
Lemma zc_I0 : zc_I 0 = 1.
Proof.
  unfold zc_I.
  pose proof zc_hmaxf_ub as Hub.
  pose proof (bp_ndf _ _ _ _ _ _ _ Hpk) as Hndf.
  replace (Z.to_nat (HEAP_SIZE - hmaxf))
    with (S (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))) by lia.
  rewrite zct_wsum_S. cbv beta.
  rewrite zc_root.
  replace (maxc1 <? ndf - 1) with true
    by (symmetry; apply Z.ltb_lt; lia).
  rewrite Hp1root. cbn [andb Z.eqb ind].
  rewrite (wsum_ext
             (fun q => ind ((maxc1 <? hp3 q) && (t_len t2 (hp3 q) =? 0)))
             (fun _ => 0) (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1))));
    [rewrite zct_wsum_zero; lia|].
  intros q Hq.
  rewrite Z2Nat.id in Hq by lia.
  destruct (Z.ltb_spec maxc1 (hp3 q)) as [Hcr|]; cbn [andb];
    [|reflexivity].
  destruct (Z.eqb_spec (t_len t2 (hp3 q)) 0) as [E0|]; cbn [ind];
    [|reflexivity].
  exfalso. pose proof (Hp1rng q ltac:(lia)). lia.
Qed.

(** the level-census identity *)
Lemma zc_level : forall j, 1 <= j <= 14 ->
  blc1 j + zc_I j = 2 * zc_I (j - 1).
Proof.
  intros j Hj.
  pose proof zc_hmaxf_ub as Hub.
  pose proof (bp_ndf _ _ _ _ _ _ _ Hpk) as Hndf.
  set (W := Z.to_nat (HEAP_SIZE - (hmaxf + 1))).
  (* the child-window node count at len j, split leaf/created *)
  assert (EN : wsum (fun p => ind (Z.eqb (t_len t2 (hp3 p)) j))
                 (hmaxf + 1) W
               = blc1 j
                 + wsum (fun p => ind ((maxc1 <? hp3 p)
                                       && (Z.eqb (t_len t2 (hp3 p)) j)))
                     (hmaxf + 1) W).
  { rewrite (Hblc j ltac:(lia)). fold W.
    rewrite <- (zct_wsum_add'
                  (fun p => ind (Z.eqb (t_len t2 (hp3 p)) j))
                  (fun p => ind ((hp3 p <=? maxc1)
                                 && (Z.eqb (t_len t2 (hp3 p)) j)))
                  (fun p => ind ((maxc1 <? hp3 p)
                                 && (Z.eqb (t_len t2 (hp3 p)) j)))
                  (hmaxf + 1) W); [reflexivity|].
    intros i Hi.
    destruct (Z.leb_spec (hp3 i) maxc1) as [Hle|Hgt];
      destruct (Z.ltb_spec maxc1 (hp3 i)) as [Hlt|Hge]; try lia;
      cbn [andb];
      destruct (Z.eqb (t_len t2 (hp3 i)) j); cbn [ind]; lia. }
  (* I j over the full window = its child-window part (root has len 0) *)
  assert (EI : zc_I j
               = wsum (fun p => ind ((maxc1 <? hp3 p)
                                     && (Z.eqb (t_len t2 (hp3 p)) j)))
                   (hmaxf + 1) W).
  { unfold zc_I.
    replace (Z.to_nat (HEAP_SIZE - hmaxf)) with (S W) by lia.
    rewrite zct_wsum_S. cbv beta.
    rewrite zc_root, Hp1root.
    replace (Z.eqb 0 j) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite andb_false_r. cbn [ind]. lia. }
  (* node-at-j = dad-at-(j-1), pointwise via the min-chain *)
  assert (EA : wsum (fun p => ind (Z.eqb (t_len t2 (hp3 p)) j))
                 (hmaxf + 1) W
               = wsum (fun p => ind (Z.eqb (t_len t2 (t_dad tL (hp3 p)))
                                       (j - 1)))
                 (hmaxf + 1) W).
  { apply wsum_ext. intros p Hp.
    assert (HpW : hmaxf + 1 <= p < HEAP_SIZE)
      by (unfold W in Hp; rewrite Z2Nat.id in Hp by lia; lia).
    rewrite (Hp1len p HpW).
    destruct (zc_dad_facts p HpW) as (_ & Hdnn).
    set (x := t_len t2 (t_dad tL (hp3 p))) in *.
    destruct (Z.eqb_spec (Z.min (x + 1) 15) j) as [E1|N1];
      destruct (Z.eqb_spec x (j - 1)) as [E2|N2]; try reflexivity; lia. }
  (* the exchange: dads-at-(j-1) = 2 * created-at-(j-1) *)
  assert (EX : wsum (fun p => ind (Z.eqb (t_len t2 (t_dad tL (hp3 p)))
                                     (j - 1)))
                 (hmaxf + 1) W
               = 2 * zc_I (j - 1)).
  { (* per child p: the indicator equals the parked-slot sum *)
    assert (Eper : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
              ind (Z.eqb (t_len t2 (t_dad tL (hp3 p))) (j - 1))
              = wsum (fun q => ind ((Z.eqb (hp3 q) (t_dad tL (hp3 p)))
                                    && (maxc1 <? hp3 q)
                                    && (Z.eqb (t_len t2 (hp3 q)) (j - 1))))
                  hmaxf (Z.to_nat (HEAP_SIZE - hmaxf))).
    { intros p Hp.
      destruct (zc_dad_facts p Hp) as (Hdr & _).
      set (c := t_dad tL (hp3 p)) in *.
      rewrite (wsum_ext
                 (fun q => ind ((Z.eqb (hp3 q) c)
                                && (maxc1 <? hp3 q)
                                && (Z.eqb (t_len t2 (hp3 q)) (j - 1))))
                 (fun q => ind (Z.eqb (hp3 q) c)
                           * ind ((maxc1 <? c)
                                  && (Z.eqb (t_len t2 c) (j - 1))))
                 hmaxf (Z.to_nat (HEAP_SIZE - hmaxf))).
      2:{ intros q Hq.
          destruct (Z.eqb_spec (hp3 q) c) as [Ee|Hne].
          - rewrite Ee. cbn [andb ind]. lia.
          - cbn [andb ind]. lia. }
      rewrite (za_wsum_const_ind (fun q => Z.eqb (hp3 q) c)
                 (ind ((maxc1 <? c) && (Z.eqb (t_len t2 c) (j - 1))))
                 hmaxf (Z.to_nat (HEAP_SIZE - hmaxf))).
      assert (Epc : wsum (fun q => ind (Z.eqb (hp3 q) c)) hmaxf
                      (Z.to_nat (HEAP_SIZE - hmaxf)) = 1)
        by (exact (zc_pcount_created c Hdr)).
      rewrite Epc.
      replace (maxc1 <? c) with true
        by (symmetry; apply Z.ltb_lt; lia).
      cbn [andb]. lia. }
    rewrite (wsum_ext
               (fun p => ind (Z.eqb (t_len t2 (t_dad tL (hp3 p))) (j - 1)))
               (fun p => wsum
                  (fun q => ind ((Z.eqb (hp3 q) (t_dad tL (hp3 p)))
                                 && (maxc1 <? hp3 q)
                                 && (Z.eqb (t_len t2 (hp3 q)) (j - 1))))
                  hmaxf (Z.to_nat (HEAP_SIZE - hmaxf)))
               (hmaxf + 1) W).
    2:{ intros p Hp. apply Eper.
        unfold W in Hp. rewrite Z2Nat.id in Hp by lia. lia. }
    rewrite (za_wsum_swap
               (fun p q => ind ((Z.eqb (hp3 q) (t_dad tL (hp3 p)))
                                && (maxc1 <? hp3 q)
                                && (Z.eqb (t_len t2 (hp3 q)) (j - 1))))
               (hmaxf + 1) W hmaxf (Z.to_nat (HEAP_SIZE - hmaxf))).
    unfold zc_I.
    rewrite <- (za_wsum_const_ind
                  (fun q => (maxc1 <? hp3 q)
                            && (Z.eqb (t_len t2 (hp3 q)) (j - 1)))
                  2 hmaxf (Z.to_nat (HEAP_SIZE - hmaxf))).
    apply wsum_ext. intros q Hq.
    (* inner: sum over children p of [hp3 q = dad_p] = bp_dad at hp3 q *)
    assert (Einner : wsum (fun p => ind ((Z.eqb (hp3 q) (t_dad tL (hp3 p)))
                                         && (maxc1 <? hp3 q)
                                         && (Z.eqb (t_len t2 (hp3 q))
                                               (j - 1))))
                       (hmaxf + 1) W
                     = ind ((maxc1 <? hp3 q)
                            && (Z.eqb (t_len t2 (hp3 q)) (j - 1)))
                       * wsum (fun p => ind (Z.eqb (t_dad tL (hp3 p))
                                               (hp3 q)))
                           (hmaxf + 1) W).
    { rewrite <- (za_wsum_const_ind
                    (fun p => Z.eqb (t_dad tL (hp3 p)) (hp3 q))
                    (ind ((maxc1 <? hp3 q)
                          && (Z.eqb (t_len t2 (hp3 q)) (j - 1))))
                    (hmaxf + 1) W).
      apply wsum_ext. intros p Hp.
      destruct (Z.eqb_spec (hp3 q) (t_dad tL (hp3 p))) as [Ee|Hne];
        destruct (Z.eqb_spec (t_dad tL (hp3 p)) (hp3 q)) as [Ee'|Hne'];
        try congruence; cbn [andb ind]; lia. }
    rewrite Einner.
    pose proof (bp_dad _ _ _ _ _ _ _ Hpk (hp3 q)) as Hbd.
    unfold W. rewrite Hbd.
    (* created-range test agrees with the (maxc1 <) test on window values *)
    assert (HqW : hmaxf <= q < HEAP_SIZE)
      by (rewrite Z2Nat.id in Hq by lia; lia).
    destruct (zc_class q HqW) as [Hleaf|Hcr].
    - replace (maxc1 <? hp3 q) with false
        by (symmetry; apply Z.ltb_ge; lia).
      replace ((elems <=? hp3 q) && (hp3 q <? ndf)) with false
        by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      cbn [andb ind]. lia.
    - replace (maxc1 <? hp3 q) with true
        by (symmetry; apply Z.ltb_lt; lia).
      replace ((elems <=? hp3 q) && (hp3 q <? ndf)) with true
        by (symmetry; apply andb_true_iff;
            split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
      cbn [andb ind]. lia. }
  rewrite EI, <- EN, EA, EX. lia.
Qed.

(** ** The Kraft telescope of the shallow profile *)

Lemma zc_telescope : forall (m : nat), (m <= 14)%nat ->
  wsum (fun j => blc1 j * 2 ^ (15 - j)) 1 m
  = 2 ^ 15 - zc_I (Z.of_nat m) * 2 ^ (15 - Z.of_nat m).
Proof.
  induction m as [|m IH]; intro Hm.
  - cbn [wsum Z.of_nat]. rewrite zc_I0.
    replace (15 - 0) with 15 by lia. lia.
  - rewrite wsum_split_last.
    rewrite IH by lia.
    pose proof (zc_level (Z.of_nat (S m)) ltac:(lia)) as HL.
    rewrite Nat2Z.inj_succ in HL |- *.
    replace (Z.succ (Z.of_nat m) - 1) with (Z.of_nat m) in HL by lia.
    replace (1 + Z.of_nat m) with (Z.succ (Z.of_nat m)) by lia.
    assert (E2 : 2 ^ (15 - Z.of_nat m)
                 = 2 * 2 ^ (15 - Z.succ (Z.of_nat m))).
    { replace (15 - Z.of_nat m) with (1 + (15 - Z.succ (Z.of_nat m)))
        by lia.
      rewrite Z.pow_add_r by lia. lia. }
    rewrite E2. nia.
Qed.

(** ** Internal witnesses at every level below a deep leaf *)

Lemma zc_internal_at : forall (fuel : nat) p j,
  (Z.to_nat (p - hmaxf) <= fuel)%nat ->
  hmaxf + 1 <= p < HEAP_SIZE ->
  1 <= j <= 14 ->
  j + 1 <= t_len t2 (hp3 p) ->
  1 <= zc_I j.
Proof.
  induction fuel as [|fuel IH]; intros p j Hf Hp Hj Hlen.
  - lia.
  - destruct (bp_ord _ _ _ _ _ _ _ Hpk p Hp) as (Hdr & q & Hq & Eq).
    assert (Hdlen : j <= t_len t2 (t_dad tL (hp3 p))).
    { rewrite (Hp1len p Hp) in Hlen. lia. }
    destruct (Z.eqb_spec (t_len t2 (t_dad tL (hp3 p))) j) as [Ej|Hne].
    + unfold zc_I.
      rewrite (za_wsum_split
                 (fun q' => ind ((maxc1 <? hp3 q')
                                 && (Z.eqb (t_len t2 (hp3 q')) j)))
                 hmaxf (Z.to_nat (q - hmaxf)) (Z.to_nat (HEAP_SIZE - hmaxf))
                 ltac:(lia)).
      replace (hmaxf + Z.of_nat (Z.to_nat (q - hmaxf))) with q by lia.
      replace (Z.to_nat (HEAP_SIZE - hmaxf) - Z.to_nat (q - hmaxf))%nat
        with (S (Z.to_nat (HEAP_SIZE - (q + 1)))) by lia.
      rewrite zct_wsum_S. cbv beta.
      assert (Hterm : ind ((maxc1 <? hp3 q)
                           && (Z.eqb (t_len t2 (hp3 q)) j)) = 1).
      { rewrite Eq.
        replace (maxc1 <? t_dad tL (hp3 p)) with true
          by (symmetry; apply Z.ltb_lt; lia).
        replace (Z.eqb (t_len t2 (t_dad tL (hp3 p))) j) with true
          by (symmetry; apply Z.eqb_eq; exact Ej).
        reflexivity. }
      rewrite Hterm.
      assert (HnnL : 0 <= wsum
                (fun q' => ind ((maxc1 <? hp3 q')
                                && (Z.eqb (t_len t2 (hp3 q')) j)))
                hmaxf (Z.to_nat (q - hmaxf))).
      { apply wsum_nonneg. intros i _.
        pose proof (ind_0_1 ((maxc1 <? hp3 i)
                             && (Z.eqb (t_len t2 (hp3 i)) j))). lia. }
      assert (HnnR : 0 <= wsum
                (fun q' => ind ((maxc1 <? hp3 q')
                                && (Z.eqb (t_len t2 (hp3 q')) j)))
                (q + 1) (Z.to_nat (HEAP_SIZE - (q + 1)))).
      { apply wsum_nonneg. intros i _.
        pose proof (ind_0_1 ((maxc1 <? hp3 i)
                             && (Z.eqb (t_len t2 (hp3 i)) j))). lia. }
      lia.
    + assert (Hql : hmaxf + 1 <= q < HEAP_SIZE).
      { destruct (Z.eqb_spec q hmaxf) as [->|]; [|lia].
        exfalso.
        rewrite <- Eq, zc_root, Hp1root in Hdlen. lia. }
      apply (IH q j); [lia|exact Hql|exact Hj|].
      rewrite <- Eq in Hdlen, Hne. lia.
Qed.

Lemma zc_I_pos : forall j, 1 <= j <= 14 -> 1 <= blc1 15 -> 1 <= zc_I j.
Proof.
  intros j Hj H15.
  rewrite (Hblc 15 ltac:(lia)) in H15.
  destruct (za_wsum_pos_ex
              (fun p => ind ((hp3 p <=? maxc1)
                             && (Z.eqb (t_len t2 (hp3 p)) 15)))
              (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))
              ltac:(lia)) as (p0 & Hp0 & Hind).
  rewrite Z2Nat.id in Hp0 by (pose proof zc_hmaxf_ub; lia).
  revert Hind.
  destruct (hp3 p0 <=? maxc1); cbn [andb]; [|cbn [ind]; lia].
  destruct (Z.eqb_spec (t_len t2 (hp3 p0)) 15) as [E15|]; cbn [ind];
    intro; [|lia].
  apply (zc_internal_at (Z.to_nat (p0 - hmaxf)) p0 j);
    [lia|lia|exact Hj|lia].
Qed.

(** ** Counting: the histogram totals the leaf census, which is at most
    [elems] *)

Lemma zc_blc_nn : forall b, 0 <= b <= 15 -> 0 <= blc1 b.
Proof.
  intros b Hb. rewrite (Hblc b Hb).
  apply wsum_nonneg. intros i _.
  pose proof (ind_0_1 ((hp3 i <=? maxc1)
                       && (Z.eqb (t_len t2 (hp3 i)) b))). lia.
Qed.

Lemma zc_hist_total : wsum (fun b => blc1 b) 1 15
  = wsum (fun p => ind (hp3 p <=? maxc1))
      (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1))).
Proof.
  set (W := Z.to_nat (HEAP_SIZE - (hmaxf + 1))).
  rewrite (wsum_ext (fun b => blc1 b)
             (fun b => wsum (fun p => ind ((hp3 p <=? maxc1)
                                           && (Z.eqb (t_len t2 (hp3 p)) b)))
                         (hmaxf + 1) W) 1 15).
  2:{ intros b Hb. apply Hblc. cbn [Z.of_nat] in Hb. lia. }
  rewrite (za_wsum_swap
             (fun b p => ind ((hp3 p <=? maxc1)
                              && (Z.eqb (t_len t2 (hp3 p)) b)))
             1 15 (hmaxf + 1) W).
  apply wsum_ext. intros p Hp.
  assert (HpW : hmaxf + 1 <= p < HEAP_SIZE)
    by (unfold W in Hp; rewrite Z2Nat.id in Hp
          by (pose proof zc_hmaxf_ub; lia); lia).
  destruct (hp3 p <=? maxc1) eqn:El; cbn [andb].
  - rewrite (wsum_ext
               (fun b => ind (Z.eqb (t_len t2 (hp3 p)) b))
               (fun b => if Z.eq_dec b (t_len t2 (hp3 p)) then 1 else 0)
               1 15).
    2:{ intros b _.
        destruct (Z.eqb_spec (t_len t2 (hp3 p)) b) as [->|Hne]; cbn [ind].
        - destruct (Z.eq_dec b b); [reflexivity|congruence].
        - destruct (Z.eq_dec b (t_len t2 (hp3 p))); [congruence|reflexivity]. }
    rewrite zct_wsum_spike.
    pose proof (Hp1rng p HpW).
    replace ((1 <=? t_len t2 (hp3 p))
             && (t_len t2 (hp3 p) <? 1 + Z.of_nat 15)) with true
      by (symmetry; apply andb_true_iff;
          split; [apply Z.leb_le; lia
                 |apply Z.ltb_lt; cbn [Z.of_nat]; lia]).
    reflexivity.
  - rewrite (wsum_ext (fun b => ind false) (fun _ => 0) 1 15)
      by (intros; reflexivity).
    rewrite zct_wsum_zero. reflexivity.
Qed.

Lemma zc_leafcount_le :
  wsum (fun p => ind (hp3 p <=? maxc1))
    (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1))) <= elems.
Proof.
  set (W := Z.to_nat (HEAP_SIZE - (hmaxf + 1))).
  pose proof zc_hmaxf_ub as Hub.
  (* pointwise domination by the value-spike sum over [0, elems) *)
  assert (Hdom : wsum (fun p => ind (hp3 p <=? maxc1)) (hmaxf + 1) W
                 <= wsum (fun p => wsum (fun x => ind (Z.eqb (hp3 p) x))
                                     0 (Z.to_nat elems)) (hmaxf + 1) W).
  { apply wsum_le. intros p Hp.
    assert (HpW : hmaxf <= p < HEAP_SIZE)
      by (unfold W in Hp; rewrite Z2Nat.id in Hp by lia; lia).
    destruct (Z.leb_spec (hp3 p) maxc1) as [Hle|]; cbn [ind].
    - destruct (zc_class p HpW) as [Hrng|Hcr]; [|lia].
      rewrite (wsum_ext (fun x => ind (Z.eqb (hp3 p) x))
                 (fun x => if Z.eq_dec x (hp3 p) then 1 else 0)
                 0 (Z.to_nat elems)).
      2:{ intros x _.
          destruct (Z.eqb_spec (hp3 p) x) as [->|Hne]; cbn [ind].
          - destruct (Z.eq_dec x x); [reflexivity|congruence].
          - destruct (Z.eq_dec x (hp3 p)); [congruence|reflexivity]. }
      rewrite zct_wsum_spike.
      replace ((0 <=? hp3 p) && (hp3 p <? 0 + Z.of_nat (Z.to_nat elems)))
        with true
        by (symmetry; apply andb_true_iff;
            split; [apply Z.leb_le; lia
                   |apply Z.ltb_lt; rewrite Z2Nat.id; lia]).
      lia.
    - apply wsum_nonneg. intros x _.
      pose proof (ind_0_1 (Z.eqb (hp3 p) x)). lia. }
  eapply Z.le_trans; [exact Hdom|].
  rewrite (za_wsum_swap (fun p x => ind (Z.eqb (hp3 p) x))
             (hmaxf + 1) W 0 (Z.to_nat elems)).
  (* per value x < elems: the child-window count <= pcount x <= 1 *)
  eapply Z.le_trans with
    (m := wsum (fun _ => 1) 0 (Z.to_nat elems)).
  - apply wsum_le. intros x Hx.
    pose proof (bp_cnt _ _ _ _ _ _ _ Hpk x) as Hc.
    assert (Hpc : wsum (fun p => ind (Z.eqb (hp3 p) x)) (hmaxf + 1) W
                  <= pcount hp3 hmaxf x).
    { unfold pcount, wcount.
      replace (Z.to_nat (HEAP_SIZE - hmaxf)) with (S W) by lia.
      rewrite zct_wsum_S. cbv beta.
      pose proof (ind_0_1 (Z.eqb (hp3 hmaxf) x)). lia. }
    rewrite Z2Nat.id in Hx by lia.
    replace ((elems <=? x) && (x <? ndf)) with false in Hc
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    cbn [ind] in Hc.
    pose proof (ind_0_1 (live_b tE maxc1 x)). lia.
  - rewrite (wsum_ext (fun _ => 1)
               (fun x => ind ((0 <=? x) && (0 <=? x)) * 1 + 0)
               0 (Z.to_nat elems)).
    2:{ intros x Hx. rewrite Z2Nat.id in Hx by lia.
        replace (0 <=? x) with true
          by (symmetry; apply Z.leb_le; lia).
        reflexivity. }
    rewrite (wsum_ext
               (fun x => ind ((0 <=? x) && (0 <=? x)) * 1 + 0)
               (fun _ => 1) 0 (Z.to_nat elems)).
    2:{ intros x Hx. rewrite Z2Nat.id in Hx by lia.
        replace (0 <=? x) with true
          by (symmetry; apply Z.leb_le; lia).
        reflexivity. }
    (* wsum of the constant 1 *)
    assert (Hone : forall (m : nat) (l : Z),
              wsum (fun _ => 1) l m = Z.of_nat m).
    { induction m as [|m IHm]; intro l; [reflexivity|].
      rewrite zct_wsum_S, IHm, Nat2Z.inj_succ. lia. }
    rewrite Hone. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma zc_blc_ub : forall b, 1 <= b <= 15 ->
  blc1 b <= elems.
Proof.
  intros b Hb.
  assert (Hsplit : wsum (fun j => blc1 j) 1 15
                   = wsum (fun j => blc1 j) 1 (Z.to_nat (b - 1))
                     + wsum (fun j => blc1 j) b
                         (15 - Z.to_nat (b - 1))).
  { rewrite (za_wsum_split (fun j => blc1 j) 1 (Z.to_nat (b - 1)) 15
               ltac:(lia)).
    replace (1 + Z.of_nat (Z.to_nat (b - 1))) with b by lia.
    reflexivity. }
  assert (HnnL : 0 <= wsum (fun j => blc1 j) 1 (Z.to_nat (b - 1))).
  { apply wsum_nonneg. intros i Hi.
    apply zc_blc_nn. rewrite Z2Nat.id in Hi by lia. lia. }
  assert (Hbterm : (15 - Z.to_nat (b - 1))%nat
                   = S (Z.to_nat (15 - b))) by lia.
  rewrite Hbterm in Hsplit.
  assert (Hterm : wsum (fun j => blc1 j) b (S (Z.to_nat (15 - b)))
                  = blc1 b + wsum (fun j => blc1 j) (b + 1)
                               (Z.to_nat (15 - b))).
  { rewrite zct_wsum_S. reflexivity. }
  rewrite Hterm in Hsplit.
  assert (HnnR : 0 <= wsum (fun j => blc1 j) (b + 1) (Z.to_nat (15 - b))).
  { apply wsum_nonneg. intros i Hi.
    apply zc_blc_nn. rewrite Z2Nat.id in Hi by lia. lia. }
  pose proof zc_hist_total as HT.
  pose proof zc_leafcount_le as HL.
  lia.
Qed.

End ZHOCensus.
