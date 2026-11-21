(** * ZHOFubini — the capped telescope: the pass-1 weighted length sum is
      at most the created-node freq sum.

    OWNER: huffman-opt.  The model-side half of L2/L3 (STRATEGY-MEMO §3):
    with SIM-A this gives  sum_live f*len_p1 <= sum f*C  for any Kraft C
    with NO slack, uniformly in the overflow count (the telescope only
    needs len(x) <= len(dad x) + 1, which pass 1's cap preserves).

    THE TELESCOPE, over the non-root parked window [hmaxf+1, HEAP_SIZE):
      A := Sum_p freq(hp3 p) * tlen(hp3 p)
        <= Sum_p freq(hp3 p) * (tlen(dad(hp3 p)) + 1)          [Hlen]
         = Sum_p freq + Sum_{i in [elems,ndf)} tlen i *
                          (Sum_{p : dad(hp3 p) = i} freq(hp3 p))  [Fubini]
         = Sum_p freq + Sum_i tlen i * freq i                  [Hchld]
         = Sum_p freq + Sum_{created positions} freq * tlen    [census+Hroot]
      so  Sum_{sym positions} freq*tlen <= Sum_{p in window} freq
        = sym mass + created-except-root mass
        = freq(root) + created-except-root mass                [Hroottot]
        = Sum_{i in [elems, ndf)} freq i.
    The position-sum <-> symbol-sum conversions ride the census facts
    (BtParked: bp_cnt count-1 per member, bp_root, bp_ord, bp_frq).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus2 BtCensus3 BtCensus4 BtPass1.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Window-algebra helpers (additions to BtWin's kit) *)

Lemma zho_wsum_zero : forall lo n, wsum (fun _ => 0) lo n = 0.
Proof.
  intros lo n; revert lo; induction n as [|k IH]; intro lo; cbn [wsum]; [lia|].
  rewrite IH; lia.
Qed.

(** pointwise-split additivity, stated premise-side so no higher-order
    rewriting is ever needed at use sites *)
Lemma zho_wsum_add' : forall (h f g : Z -> Z) lo n,
  (forall i, lo <= i < lo + Z.of_nat n -> h i = f i + g i) ->
  wsum h lo n = wsum f lo n + wsum g lo n.
Proof.
  intros h f g lo n; revert lo; induction n as [|k IH]; intros lo H;
    cbn [wsum]; [lia|].
  rewrite (H lo) by lia.
  rewrite (IH (lo + 1)) by (intros; apply H; lia).
  lia.
Qed.

(** the value-range sum of [ind (Z.eqb c i) * g i] collapses to [g c] *)
Lemma zho_wsum_ind_point : forall (g : Z -> Z) (c lo : Z) (n : nat),
  lo <= c < lo + Z.of_nat n ->
  wsum (fun i => ind (Z.eqb c i) * g i) lo n = g c.
Proof.
  intros g c lo n; revert lo; induction n as [|k IH]; intros lo Hc.
  - cbn [Z.of_nat] in Hc; lia.
  - rewrite Nat2Z.inj_succ in Hc. cbn [wsum]. cbv beta.
    destruct (Z.eqb_spec c lo) as [->|Hne].
    + cbn [ind].
      assert (E : wsum (fun i => ind (Z.eqb lo i) * g i) (lo + 1) k = 0).
      { etransitivity; [apply (wsum_ext _ (fun _ => 0))|
                        apply (zho_wsum_zero (lo + 1) k)].
        intros i Hi.
        replace (Z.eqb lo i) with false
          by (symmetry; apply Z.eqb_neq; lia).
        cbn [ind]; lia. }
      rewrite E; lia.
    + cbn [ind]. rewrite (IH (lo + 1)) by lia. lia.
Qed.

(** a value absent from the window contributes nothing *)
Lemma zho_wsum_count0 : forall (g : Z -> Z) (a : zarr) (c lo : Z) (n : nat),
  wcount a lo n c = 0 ->
  wsum (fun p => ind (Z.eqb (a p) c) * g (a p)) lo n = 0.
Proof.
  intros g a c lo n; revert lo; induction n as [|k IH]; intros lo Hc;
    [reflexivity|].
  unfold wcount in Hc. cbn [wsum] in Hc |- *. cbv beta. cbv beta in Hc.
  fold (wcount a (lo + 1) k c) in Hc.
  pose proof (wcount_nonneg a (lo + 1) k c).
  pose proof (ind_0_1 (Z.eqb (a lo) c)).
  assert (Ei : ind (Z.eqb (a lo) c) = 0) by lia.
  rewrite Ei, (IH (lo + 1)) by lia. lia.
Qed.

(** a value hit exactly once contributes exactly its term *)
Lemma zho_wsum_ind_value : forall (g : Z -> Z) (a : zarr) (c lo : Z) (n : nat),
  wcount a lo n c = 1 ->
  wsum (fun p => ind (Z.eqb (a p) c) * g (a p)) lo n = g c.
Proof.
  intros g a c lo n; revert lo; induction n as [|k IH]; intros lo Hc.
  - unfold wcount in Hc; cbn [wsum] in Hc; lia.
  - unfold wcount in Hc. cbn [wsum] in Hc |- *. cbv beta. cbv beta in Hc.
    fold (wcount a (lo + 1) k c) in Hc.
    pose proof (wcount_nonneg a (lo + 1) k c).
    pose proof (ind_0_1 (Z.eqb (a lo) c)).
    destruct (Z.eqb (a lo) c) eqn:E; cbn [ind] in Hc |- *.
    + apply Z.eqb_eq in E.
      assert (Ht : wcount a (lo + 1) k c = 0) by lia.
      rewrite (zho_wsum_count0 g a c (lo + 1) k Ht).
      rewrite E. lia.
    + rewrite (IH (lo + 1)) by lia. lia.
Qed.

(** splitting a half-open Z-range indicator at its low end *)
Lemma zho_ind_range_split : forall (lo x : Z) (k : nat),
  ind ((lo <=? x) && (x <? lo + Z.of_nat (S k)))
  = ind (Z.eqb x lo) + ind ((lo + 1 <=? x) && (x <? lo + 1 + Z.of_nat k)).
Proof.
  intros lo x k.
  rewrite Nat2Z.inj_succ.
  destruct (Z.leb_spec lo x);
    destruct (Z.ltb_spec x (lo + Z.succ (Z.of_nat k)));
    destruct (Z.eqb_spec x lo);
    destruct (Z.leb_spec (lo + 1) x);
    destruct (Z.ltb_spec x (lo + 1 + Z.of_nat k));
    cbn [andb ind]; lia.
Qed.

(** reindexing: a value-range sum, gated by a selector matching the window
    counts, equals the corresponding position sum *)
Lemma zho_wsum_reindex_sel :
  forall (g : Z -> Z) (sel : Z -> bool) (a : zarr) (lo : Z) (n : nat)
         (m : nat) (lo' : Z),
  (forall v, lo' <= v < lo' + Z.of_nat m -> wcount a lo n v = ind (sel v)) ->
  wsum (fun v => ind (sel v) * g v) lo' m
  = wsum (fun p => ind ((lo' <=? a p) && (a p <? lo' + Z.of_nat m)) * g (a p))
         lo n.
Proof.
  intros g sel a lo n m; induction m as [|k IH]; intros lo' Hcnt.
  - cbn [wsum]. symmetry.
    etransitivity; [apply (wsum_ext _ (fun _ => 0))|
                    apply (zho_wsum_zero lo n)].
    intros p Hp.
    replace ((lo' <=? a p) && (a p <? lo' + Z.of_nat 0)) with false.
    2:{ symmetry. apply andb_false_iff.
        destruct (Z.leb_spec lo' (a p)) as [Hle|Hgt].
        - right. apply Z.ltb_ge. cbn [Z.of_nat]. lia.
        - left. reflexivity. }
    cbn [ind]; lia.
  - cbn [wsum]. cbv beta.
    rewrite (IH (lo' + 1))
      by (intros v Hv; apply Hcnt; rewrite Nat2Z.inj_succ; lia).
    assert (Hh : wsum (fun p => ind (Z.eqb (a p) lo') * g (a p)) lo n
                 = ind (sel lo') * g lo').
    { assert (Hc0 : wcount a lo n lo' = ind (sel lo'))
        by (apply Hcnt; rewrite Nat2Z.inj_succ; lia).
      destruct (sel lo') eqn:Es; cbn [ind] in Hc0 |- *.
      - rewrite (zho_wsum_ind_value g a lo' lo n Hc0). lia.
      - rewrite (zho_wsum_count0 g a lo' lo n Hc0). lia. }
    rewrite <- Hh.
    symmetry.
    etransitivity.
    { apply (zho_wsum_add'
               (fun p => ind ((lo' <=? a p) && (a p <? lo' + Z.of_nat (S k)))
                         * g (a p))
               (fun p => ind (Z.eqb (a p) lo') * g (a p))
               (fun p => ind ((lo' + 1 <=? a p)
                              && (a p <? lo' + 1 + Z.of_nat k)) * g (a p))
               lo n).
      intros p Hp.
      rewrite zho_ind_range_split. ring. }
    reflexivity.
Qed.

(** ** The telescope *)

Section ZHOFubini.

Variables (elems maxc1 : Z) (t1 tf : Tree) (hp3 : zarr) (hmaxf ndf : Z).
Hypothesis Hpk : BtParked elems maxc1 t1 tf hp3 hmaxf ndf.
Hypothesis Hel : 0 < elems <= L_CODES.
Hypothesis Hmc : maxc1 < elems.
Hypothesis Hmf0 : 0 <= hmaxf.

(** the pass-1 length reading, abstracted to a function of the node index *)
Variable tlen : Z -> Z.
Hypothesis Hlen : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
  tlen (hp3 p) <= tlen (t_dad tf (hp3 p)) + 1.
Hypothesis Hlen_nn : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
  0 <= tlen (hp3 p).
Hypothesis Hroot : tlen (ndf - 1) = 0.

(** freqs: entry freqs on symbols, loop sums on created nodes *)
Hypothesis Hfrq_nn : forall x, 0 <= t_freq tf x.
Hypothesis Hchld : forall i, elems <= i < ndf ->
  t_freq tf i
  = wsum (fun p => ind (Z.eqb (t_dad tf (hp3 p)) i) * t_freq tf (hp3 p))
         (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1))).
Hypothesis Hroottot : t_freq tf (ndf - 1)
  = wsum (fun n => ind (live_b t1 maxc1 n) * t_freq t1 n)
         0 (Z.to_nat elems).

Local Notation Wn := (Z.to_nat (HEAP_SIZE - (hmaxf + 1))).

Lemma zho_geo :
  0 <= HEAP_SIZE - (hmaxf + 1)
  /\ hmaxf + 1 + Z.of_nat Wn = HEAP_SIZE
  /\ elems + 1 <= ndf.
Proof.
  pose proof (bp_hmax _ _ _ _ _ _ _ Hpk) as H1.
  pose proof (bp_ndf _ _ _ _ _ _ _ Hpk) as H2.
  unfold HEAP_SIZE in *.
  rewrite Z2Nat.id by lia.
  repeat split; lia.
Qed.

Lemma zho_wincnt : forall x,
  wcount hp3 (hmaxf + 1) Wn x
  = ind (live_b t1 maxc1 x) + ind ((elems <=? x) && (x <? ndf))
    - ind (Z.eqb (ndf - 1) x).
Proof.
  intro x.
  destruct zho_geo as (Hg1 & Hg2 & Hg3).
  pose proof (bp_cnt _ _ _ _ _ _ _ Hpk x) as Hc.
  pose proof (bp_root _ _ _ _ _ _ _ Hpk) as Hr.
  unfold pcount in Hc.
  assert (En : Z.to_nat (HEAP_SIZE - hmaxf) = S Wn).
  { rewrite <- Z2Nat.inj_succ by lia. f_equal. lia. }
  rewrite En in Hc.
  unfold wcount in Hc. cbn [wsum] in Hc. cbv beta in Hc.
  rewrite Hr in Hc.
  fold (wcount hp3 (hmaxf + 1) Wn x) in Hc.
  lia.
Qed.

Lemma zho_root_absent : forall p,
  hmaxf + 1 <= p < HEAP_SIZE -> hp3 p <> ndf - 1.
Proof.
  destruct zho_geo as (Hg1 & Hg2 & Hg3).
  intros p Hp Heq.
  assert (H1 : 1 <= wcount hp3 (hmaxf + 1) Wn (ndf - 1)).
  { apply (wcount_of_member hp3 (hmaxf + 1) Wn (ndf - 1) p);
      [lia | exact Heq]. }
  rewrite zho_wincnt in H1.
  replace (live_b t1 maxc1 (ndf - 1)) with false in H1.
  2:{ symmetry. unfold live_b. apply andb_false_iff. left.
      apply andb_false_iff. right. apply Z.leb_gt. lia. }
  replace ((elems <=? ndf - 1) && (ndf - 1 <? ndf)) with true in H1.
  2:{ symmetry. apply andb_true_iff.
      split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
  rewrite Z.eqb_refl in H1. cbn [ind] in H1. lia.
Qed.

Lemma zho_member_class : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
  ind (live_b t1 maxc1 (hp3 p))
  + ind ((elems <=? hp3 p) && (hp3 p <? ndf)) = 1.
Proof.
  destruct zho_geo as (Hg1 & Hg2 & Hg3).
  intros p Hp.
  assert (H1 : 1 <= wcount hp3 (hmaxf + 1) Wn (hp3 p)).
  { apply (wcount_of_member hp3 (hmaxf + 1) Wn (hp3 p) p);
      [lia | reflexivity]. }
  rewrite zho_wincnt in H1.
  pose proof (zho_root_absent p Hp) as Hnr.
  assert (Er : ind (Z.eqb (ndf - 1) (hp3 p)) = 0).
  { destruct (Z.eqb (ndf - 1) (hp3 p)) eqn:E; cbn [ind]; [|reflexivity].
    apply Z.eqb_eq in E. exfalso. apply Hnr. lia. }
  rewrite Er in H1.
  pose proof (ind_0_1 ((elems <=? hp3 p) && (hp3 p <? ndf))).
  destruct (live_b t1 maxc1 (hp3 p)) eqn:El; cbn [ind] in *.
  - unfold live_b in El.
    apply andb_true_iff in El as [El1 _].
    apply andb_true_iff in El1 as [_ El2].
    apply Z.leb_le in El2.
    replace ((elems <=? hp3 p) && (hp3 p <? ndf)) with false; [cbn [ind]; lia|].
    symmetry. apply andb_false_iff. left. apply Z.leb_gt. lia.
  - lia.
Qed.

(** the Fubini swap: group the window's dad-weighted terms by dad value *)
Lemma zho_swap : forall (n : nat) (lo : Z),
  (forall p, lo <= p < lo + Z.of_nat n -> elems <= t_dad tf (hp3 p) < ndf) ->
  wsum (fun i => tlen i
        * wsum (fun p => ind (Z.eqb (t_dad tf (hp3 p)) i) * t_freq tf (hp3 p))
               lo n)
       elems (Z.to_nat (ndf - elems))
  = wsum (fun p => t_freq tf (hp3 p) * tlen (t_dad tf (hp3 p))) lo n.
Proof.
  destruct zho_geo as (Hg1 & Hg2 & Hg3).
  induction n as [|k IH]; intros lo Hdr.
  - cbn [wsum].
    etransitivity; [apply (wsum_ext _ (fun _ => 0))|
                    apply (zho_wsum_zero elems (Z.to_nat (ndf - elems)))].
    intros i Hi. cbn [wsum]. lia.
  - cbn [wsum]. cbv beta.
    etransitivity.
    { apply (zho_wsum_add'
        (fun i => tlen i
           * (ind (Z.eqb (t_dad tf (hp3 lo)) i) * t_freq tf (hp3 lo)
              + wsum (fun p => ind (Z.eqb (t_dad tf (hp3 p)) i)
                               * t_freq tf (hp3 p)) (lo + 1) k))
        (fun i => ind (Z.eqb (t_dad tf (hp3 lo)) i)
                  * (tlen i * t_freq tf (hp3 lo)))
        (fun i => tlen i
           * wsum (fun p => ind (Z.eqb (t_dad tf (hp3 p)) i)
                            * t_freq tf (hp3 p)) (lo + 1) k)
        elems (Z.to_nat (ndf - elems))).
      intros i Hi. ring. }
    f_equal.
    + etransitivity.
      { apply (zho_wsum_ind_point
                 (fun i => tlen i * t_freq tf (hp3 lo))
                 (t_dad tf (hp3 lo)) elems (Z.to_nat (ndf - elems))).
        rewrite Z2Nat.id by lia.
        destruct (Hdr lo ltac:(lia)) as [Hd1 Hd2]. lia. }
      apply Z.mul_comm.
    + apply (IH (lo + 1)).
      intros p Hp. apply Hdr. lia.
Qed.

Theorem zho_capped_telescope :
  wsum (fun n => ind (live_b t1 maxc1 n) * t_freq t1 n * tlen n)
       0 (Z.to_nat elems)
  <= wsum (fun i => t_freq tf i) elems (Z.to_nat (ndf - elems)).
Proof.
  destruct zho_geo as (Hg1 & Hg2 & Hg3).
  pose proof (bp_ord _ _ _ _ _ _ _ Hpk) as Hord.
  pose proof (bp_frq _ _ _ _ _ _ _ Hpk) as Hfrq1.

  (* [1] generic split of a window sum into sym + created parts *)
  assert (Hsplit : forall (g : Z -> Z),
    wsum (fun p => g (hp3 p)) (hmaxf + 1) Wn
    = wsum (fun p => ind (live_b t1 maxc1 (hp3 p)) * g (hp3 p))
           (hmaxf + 1) Wn
      + wsum (fun p => ind ((elems <=? hp3 p) && (hp3 p <? ndf)) * g (hp3 p))
             (hmaxf + 1) Wn).
  { intro g.
    apply (zho_wsum_add' (fun p => g (hp3 p))
             (fun p => ind (live_b t1 maxc1 (hp3 p)) * g (hp3 p))
             (fun p => ind ((elems <=? hp3 p) && (hp3 p <? ndf)) * g (hp3 p))).
    intros p Hp.
    pose proof (zho_member_class p ltac:(lia)) as Hm1.
    destruct (live_b t1 maxc1 (hp3 p));
      destruct ((elems <=? hp3 p) && (hp3 p <? ndf));
      cbn [ind] in *; lia. }

  (* [2] sym-side reindex, generic g *)
  assert (Hsym : forall (g : Z -> Z),
    wsum (fun v => ind (live_b t1 maxc1 v) * g v) 0 (Z.to_nat elems)
    = wsum (fun p => ind (live_b t1 maxc1 (hp3 p)) * g (hp3 p))
           (hmaxf + 1) Wn).
  { intro g.
    etransitivity.
    { apply (zho_wsum_reindex_sel g (live_b t1 maxc1) hp3 (hmaxf + 1) Wn
               (Z.to_nat elems) 0).
      intros v Hv. rewrite Z2Nat.id in Hv by lia.
      rewrite zho_wincnt.
      replace ((elems <=? v) && (v <? ndf)) with false
        by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
      replace (Z.eqb (ndf - 1) v) with false
        by (symmetry; apply Z.eqb_neq; lia).
      cbn [ind]. lia. }
    apply wsum_ext. intros p Hp.
    assert (Hp' : hmaxf + 1 <= p < HEAP_SIZE) by lia.
    pose proof (zho_member_class p Hp') as Hm1.
    destruct (live_b t1 maxc1 (hp3 p)) eqn:El.
    - assert (Hb : 0 <= hp3 p <= maxc1).
      { unfold live_b in El. apply andb_true_iff in El as [E1 _].
        apply andb_true_iff in E1 as [E1 E2].
        apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
      replace ((0 <=? hp3 p) && (hp3 p <? 0 + Z.of_nat (Z.to_nat elems)))
        with true.
      2:{ symmetry. apply andb_true_iff.
          split; [apply Z.leb_le; lia|].
          apply Z.ltb_lt. rewrite Z2Nat.id by lia. lia. }
      reflexivity.
    - cbn [ind] in Hm1.
      assert (Hcx : elems <= hp3 p).
      { destruct ((elems <=? hp3 p) && (hp3 p <? ndf)) eqn:Ec;
          cbn [ind] in Hm1; [|lia].
        apply andb_true_iff in Ec as [Ec _]. apply Z.leb_le in Ec. lia. }
      replace ((0 <=? hp3 p) && (hp3 p <? 0 + Z.of_nat (Z.to_nat elems)))
        with false.
      2:{ symmetry. apply andb_false_iff. right. apply Z.ltb_ge.
          rewrite Z2Nat.id by lia. lia. }
      reflexivity. }

  (* [3] created-side reindex (non-root values), generic g *)
  assert (Hcr : forall (g : Z -> Z),
    wsum g elems (Z.to_nat (ndf - 1 - elems))
    = wsum (fun p => ind ((elems <=? hp3 p) && (hp3 p <? ndf)) * g (hp3 p))
           (hmaxf + 1) Wn).
  { intro g.
    etransitivity.
    { etransitivity.
      { apply (wsum_ext g (fun v => ind ((fun _ : Z => true) v) * g v)).
        intros i Hi. cbn [ind]. lia. }
      apply (zho_wsum_reindex_sel g (fun _ => true) hp3 (hmaxf + 1) Wn
               (Z.to_nat (ndf - 1 - elems)) elems).
      intros v Hv. rewrite Z2Nat.id in Hv by lia.
      rewrite zho_wincnt.
      replace (live_b t1 maxc1 v) with false.
      2:{ symmetry. unfold live_b. apply andb_false_iff. left.
          apply andb_false_iff. right. apply Z.leb_gt. lia. }
      replace ((elems <=? v) && (v <? ndf)) with true
        by (symmetry; apply andb_true_iff;
            split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
      replace (Z.eqb (ndf - 1) v) with false
        by (symmetry; apply Z.eqb_neq; lia).
      cbn [ind]. lia. }
    apply wsum_ext. intros p Hp.
    assert (Hp' : hmaxf + 1 <= p < HEAP_SIZE) by lia.
    pose proof (zho_root_absent p Hp') as Hnr.
    assert (EM : elems + Z.of_nat (Z.to_nat (ndf - 1 - elems)) = ndf - 1)
      by (rewrite Z2Nat.id by lia; lia).
    rewrite EM.
    destruct (Z.leb_spec elems (hp3 p));
      destruct (Z.ltb_spec (hp3 p) (ndf - 1));
      destruct (Z.ltb_spec (hp3 p) ndf);
      cbn [andb ind]; try reflexivity; lia. }

  (* [4] A <= Afr + Adad *)
  assert (HAle :
    wsum (fun p => t_freq tf (hp3 p) * tlen (hp3 p)) (hmaxf + 1) Wn
    <= wsum (fun p => t_freq tf (hp3 p)) (hmaxf + 1) Wn
       + wsum (fun p => t_freq tf (hp3 p) * tlen (t_dad tf (hp3 p)))
              (hmaxf + 1) Wn).
  { etransitivity.
    { apply (wsum_le (fun p => t_freq tf (hp3 p) * tlen (hp3 p))
        (fun p => t_freq tf (hp3 p)
                  + t_freq tf (hp3 p) * tlen (t_dad tf (hp3 p)))).
      intros p Hp.
      assert (Hp' : hmaxf + 1 <= p < HEAP_SIZE) by lia.
      pose proof (Hlen p Hp'). pose proof (Hfrq_nn (hp3 p)). nia. }
    apply Z.eq_le_incl.
    apply (zho_wsum_add'
             (fun p => t_freq tf (hp3 p)
                       + t_freq tf (hp3 p) * tlen (t_dad tf (hp3 p)))
             (fun p => t_freq tf (hp3 p))
             (fun p => t_freq tf (hp3 p) * tlen (t_dad tf (hp3 p)))).
    intros; lia. }

  (* [5] Adad = the created value sum, weighted by tlen *)
  assert (HAdad :
    wsum (fun p => t_freq tf (hp3 p) * tlen (t_dad tf (hp3 p)))
         (hmaxf + 1) Wn
    = wsum (fun i => tlen i * t_freq tf i) elems (Z.to_nat (ndf - elems))).
  { etransitivity.
    { symmetry. apply (zho_swap Wn (hmaxf + 1)).
      intros p Hp. destruct (Hord p ltac:(lia)) as [Hd _]. exact Hd. }
    apply wsum_ext. intros i Hi.
    rewrite Z2Nat.id in Hi by lia.
    rewrite <- (Hchld i) by lia.
    reflexivity. }

  (* [6] that value sum equals the created-position part of A *)
  assert (HB :
    wsum (fun i => tlen i * t_freq tf i) elems (Z.to_nat (ndf - elems))
    = wsum (fun p => ind ((elems <=? hp3 p) && (hp3 p <? ndf))
                     * (t_freq tf (hp3 p) * tlen (hp3 p)))
           (hmaxf + 1) Wn).
  { assert (EN : Z.to_nat (ndf - elems) = S (Z.to_nat (ndf - 1 - elems)))
      by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
    rewrite EN, wsum_split_last.
    assert (EM : elems + Z.of_nat (Z.to_nat (ndf - 1 - elems)) = ndf - 1)
      by (rewrite Z2Nat.id by lia; lia).
    rewrite EM. cbv beta. rewrite Hroot, Z.mul_0_l, Z.add_0_r.
    etransitivity.
    { apply (wsum_ext _ (fun i => t_freq tf i * tlen i)).
      intros; ring. }
    pose proof (Hcr (fun x => t_freq tf x * tlen x)) as Hc1.
    cbv beta in Hc1. exact Hc1. }

  (* [7] the sym part of Afr is the root freq *)
  assert (HsymFr :
    wsum (fun p => ind (live_b t1 maxc1 (hp3 p)) * t_freq tf (hp3 p))
         (hmaxf + 1) Wn
    = t_freq tf (ndf - 1)).
  { etransitivity; [symmetry; apply (Hsym (fun v => t_freq tf v))|].
    etransitivity; [|symmetry; exact Hroottot].
    apply wsum_ext. intros v Hv.
    rewrite Z2Nat.id in Hv by lia.
    rewrite (Hfrq1 v) by lia.
    reflexivity. }

  (* [8] Afr equals the theorem's RHS *)
  assert (HAfr :
    wsum (fun p => t_freq tf (hp3 p)) (hmaxf + 1) Wn
    = wsum (fun i => t_freq tf i) elems (Z.to_nat (ndf - elems))).
  { pose proof (Hsplit (fun x => t_freq tf x)) as Hs0. cbv beta in Hs0.
    pose proof (Hcr (fun v => t_freq tf v)) as Hc0. cbv beta in Hc0.
    assert (EN : Z.to_nat (ndf - elems) = S (Z.to_nat (ndf - 1 - elems)))
      by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
    rewrite EN, wsum_split_last.
    assert (EM : elems + Z.of_nat (Z.to_nat (ndf - 1 - elems)) = ndf - 1)
      by (rewrite Z2Nat.id by lia; lia).
    rewrite EM. cbv beta.
    rewrite Hs0, HsymFr, <- Hc0. lia. }

  (* [9] the theorem's LHS is the sym part of A *)
  assert (HL :
    wsum (fun n => ind (live_b t1 maxc1 n) * t_freq t1 n * tlen n)
         0 (Z.to_nat elems)
    = wsum (fun p => ind (live_b t1 maxc1 (hp3 p))
                     * (t_freq tf (hp3 p) * tlen (hp3 p)))
           (hmaxf + 1) Wn).
  { etransitivity; [|apply (Hsym (fun v => t_freq tf v * tlen v))].
    apply wsum_ext. intros v Hv.
    rewrite Z2Nat.id in Hv by lia.
    rewrite (Hfrq1 v) by lia.
    ring. }

  (* assemble *)
  pose proof (Hsplit (fun x => t_freq tf x * tlen x)) as HsA. cbv beta in HsA.
  rewrite HL, <- HAfr. lia.
Qed.

End ZHOFubini.
