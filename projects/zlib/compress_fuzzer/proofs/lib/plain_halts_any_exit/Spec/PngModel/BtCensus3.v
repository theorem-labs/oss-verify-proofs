(** * BtCensus3 — the combine loop's dad-edge census.

    OWNER: an earlier development run.

    What [gb_pass1]'s Kraft walk needs from [bt_loop], as one invariant:

    - CONSERVATION: live count + parked count of every value x is exactly
      [x is a live symbol] + [x is a created node] — which caps every count at
      ONE.  Distinctness of parked values is a corollary, and it is
      load-bearing: [tr_dl] is a union, so a value parked twice would have its
      dad destroyed by [gb_pass1]'s len write before its own visit.
    - DAD CENSUS: summed over the parked window, every created node is the dad
      of EXACTLY TWO parked nodes, and nothing else is the dad of any.
    - DAD ORDER: every parked node's dad is a created node that is either
      still live (it will park strictly below everything parked so far) or
      already parked at a strictly lower position.  This is the walk-order
      fact that lets [gen_bitlen] read [tree[tree[n].Dad].Len] after
      overwriting Dad with Len in heap order.
    - LEAF FREQS: the loop writes frequencies only at created nodes, so leaf
      frequencies still agree with the tallied tree.

    The step proof follows BtStep.v's shape discipline: every intermediate
    array is a parameter with its defining equation, so index side conditions
    stay visible. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus1 BtCensus2 BtStep.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** Parked-window count: positions [hm .. HEAP_SIZE). *)
Definition pcount (hp : zarr) (hm x : Z) : Z :=
  wcount hp hm (Z.to_nat (HEAP_SIZE - hm)) x.

(** ** Window micro-algebra *)

Lemma lcount_shrink : forall hp hl x,
  1 <= hl ->
  lcount hp hl x = lcount hp (hl - 1) x + ind (Z.eqb (hp hl) x).
Proof.
  intros hp hl x Hl. unfold lcount.
  replace (Z.to_nat hl) with (S (Z.to_nat (hl - 1)))
    by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
  rewrite wcount_grow_high.
  rewrite Z2Nat.id by lia.
  replace (1 + (hl - 1)) with hl by lia.
  reflexivity.
Qed.

Lemma lcount_ext : forall hp hp' hl x,
  0 <= hl ->
  (forall i, 1 <= i <= hl -> hp' i = hp i) ->
  lcount hp' hl x = lcount hp hl x.
Proof.
  intros hp hp' hl x Hl H. unfold lcount.
  apply wcount_ext_window. intros i Hi.
  apply H. rewrite Z2Nat.id in Hi by lia. lia.
Qed.

Lemma pcount_ext : forall hp hp' hm x,
  (forall p, hm <= p < HEAP_SIZE -> hp' p = hp p) ->
  pcount hp' hm x = pcount hp hm x.
Proof.
  intros hp hp' hm x H. unfold pcount.
  apply wcount_ext_window. intros i Hi.
  apply H.
  destruct (Z_le_gt_dec hm HEAP_SIZE) as [Hle|Hgt].
  - rewrite Z2Nat.id in Hi by lia. lia.
  - replace (Z.to_nat (HEAP_SIZE - hm)) with O in Hi by lia.
    cbn [Z.of_nat] in Hi. lia.
Qed.

(** Growing the parked window one slot down. *)
Lemma pcount_grow : forall hp hm x,
  hm <= HEAP_SIZE ->
  pcount hp (hm - 1) x = ind (Z.eqb (hp (hm - 1)) x) + pcount hp hm x.
Proof.
  intros hp hm x Hm. unfold pcount.
  replace (HEAP_SIZE - (hm - 1)) with (HEAP_SIZE - hm + 1) by lia.
  replace (Z.to_nat (HEAP_SIZE - hm + 1)) with (S (Z.to_nat (HEAP_SIZE - hm)))
    by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
  rewrite wcount_grow_low.
  reflexivity.
Qed.

Lemma pcount_member : forall hp hm p,
  hm <= p < HEAP_SIZE ->
  1 <= pcount hp hm (hp p).
Proof.
  intros hp hm p Hp. unfold pcount.
  apply (wcount_of_member hp hm _ (hp p) p); [|reflexivity].
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma lcount_member : forall hp hl i,
  1 <= i <= hl ->
  1 <= lcount hp hl (hp i).
Proof.
  intros hp hl i Hi. unfold lcount.
  apply (wcount_of_member hp 1 _ (hp i) i); [|reflexivity].
  rewrite Z2Nat.id by lia. lia.
Qed.

(** ** Dad reads through the trip's tree writes *)

Lemma t_dad_setfreq : forall t i v x, t_dad (t_setfreq t i v) x = t_dad t x.
Proof. reflexivity. Qed.

Lemma t_freq_setdad : forall t i v x, t_freq (t_setdad t i v) x = t_freq t x.
Proof. reflexivity. Qed.

Lemma t_dad_setdad_same : forall t i v,
  0 <= v < 65536 -> t_dad (t_setdad t i v) i = v.
Proof.
  intros t i v Hv. unfold t_setdad, t_dad. cbn [tr_dl].
  rewrite zset_same. unfold u16. apply Z.mod_small. lia.
Qed.

Lemma t_dad_setdad_other : forall t i v x,
  x <> i -> t_dad (t_setdad t i v) x = t_dad t x.
Proof.
  intros t i v x Hx. unfold t_setdad, t_dad. cbn [tr_dl].
  apply zset_other. exact Hx.
Qed.

(** The trip's tree: dads of [n] and [m] become [node], all else unchanged. *)
Lemma trip_dad : forall t n m node fv x,
  n <> m -> 0 <= node < 65536 ->
  t_dad (t_setdad (t_setdad (t_setfreq t node fv) m node) n node) x
  = if Z.eqb x n then node else if Z.eqb x m then node else t_dad t x.
Proof.
  intros t n m node fv x Hnm Hnode.
  destruct (Z.eqb x n) eqn:En.
  - apply Z.eqb_eq in En. subst x. apply t_dad_setdad_same. exact Hnode.
  - apply Z.eqb_neq in En.
    rewrite t_dad_setdad_other by exact En.
    destruct (Z.eqb x m) eqn:Em.
    + apply Z.eqb_eq in Em. subst x. apply t_dad_setdad_same. exact Hnode.
    + apply Z.eqb_neq in Em.
      rewrite t_dad_setdad_other by exact Em.
      apply t_dad_setfreq.
Qed.

Lemma trip_freq : forall t n m node fv x,
  x <> node ->
  t_freq (t_setdad (t_setdad (t_setfreq t node fv) m node) n node) x
  = t_freq t x.
Proof.
  intros t n m node fv x Hx.
  rewrite !t_freq_setdad.
  unfold t_setfreq, t_freq. cbn [tr_fc]. apply zset_other. exact Hx.
Qed.

(** ** The invariant *)

Record CensusInv (elems maxc1 : Z) (t1 : Tree) (hlen1 : Z) (st : BtSt) : Prop :=
mkCensusInv {
  cv_nd   : elems <= b_node st;
  cv_hm   : b_hmax st = HEAP_SIZE - 2 * (b_node st - elems);
  cv_hl   : b_hlen st = hlen1 - (b_node st - elems);
  cv_cons : forall x,
      lcount (b_heap st) (b_hlen st) x + pcount (b_heap st) (b_hmax st) x
      = ind (live_b t1 maxc1 x)
        + ind ((elems <=? x) && (x <? b_node st));
  cv_dad  : forall c,
      wsum (fun p => ind (Z.eqb (t_dad (b_tree st) (b_heap st p)) c))
           (b_hmax st) (Z.to_nat (HEAP_SIZE - b_hmax st))
      = 2 * ind ((elems <=? c) && (c <? b_node st));
  cv_ord  : forall p, b_hmax st <= p < HEAP_SIZE ->
      elems <= t_dad (b_tree st) (b_heap st p) < b_node st
      /\ (1 <= lcount (b_heap st) (b_hlen st)
                      (t_dad (b_tree st) (b_heap st p))
          \/ exists p', b_hmax st <= p' < p
               /\ b_heap st p' = t_dad (b_tree st) (b_heap st p));
  cv_frq  : forall x, x < elems -> t_freq (b_tree st) x = t_freq t1 x;
  cv_dlf  : forall y,
      lcount (b_heap st) (b_hlen st) y + pcount (b_heap st) (b_hmax st) y = 0 ->
      tr_dl (b_tree st) y = tr_dl t1 y
}.

(** Mutual exclusion of the two right-hand indicators. *)
Lemma total_le_1 : forall elems maxc1 t1 nd x,
  maxc1 < elems ->
  ind (live_b t1 maxc1 x) + ind ((elems <=? x) && (x <? nd)) <= 1.
Proof.
  intros elems maxc1 t1 nd x Hme.
  destruct (Z_le_gt_dec elems x) as [Hx|Hx].
  - rewrite (live_b_false_high t1 maxc1 x) by lia. cbn [ind].
    pose proof (ind_0_1 ((elems <=? x) && (x <? nd))). lia.
  - replace ((elems <=? x) && (x <? nd)) with false
      by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
    cbn [ind]. pose proof (ind_0_1 (live_b t1 maxc1 x)). lia.
Qed.

(** Extending the created range by its fresh top. *)
Lemma created_extend : forall elems node c,
  0 <= elems <= node ->
  ind (Z.eqb node c) + ind ((elems <=? c) && (c <? node))
  = ind ((elems <=? c) && (c <? node + 1)).
Proof.
  intros elems node c He.
  destruct (Z.eqb node c) eqn:Ec.
  - apply Z.eqb_eq in Ec. subst c.
    replace ((elems <=? node) && (node <? node)) with false
      by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia).
    replace ((elems <=? node) && (node <? node + 1)) with true
      by (symmetry; apply andb_true_intro;
          split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
    reflexivity.
  - apply Z.eqb_neq in Ec.
    destruct (Z.ltb c node) eqn:El.
    + apply Z.ltb_lt in El.
      replace (Z.ltb c (node + 1)) with true
        by (symmetry; apply Z.ltb_lt; lia).
      reflexivity.
    + apply Z.ltb_ge in El.
      replace (Z.ltb c (node + 1)) with false
        by (symmetry; apply Z.ltb_ge; lia).
      reflexivity.
Qed.

(** One [pq_down] level with the no-room guard, fuel kept VARIABLE — a [cbn]
    on literal fuel unfolds every level and duplicates the array term
    exponentially (measured: hung this file's build). *)
Lemma pq_down_norec : forall f t dep hp hlen v k,
  Z.leb (2 * k) hlen = false ->
  pq_down (S f) t dep hp hlen v k = zset hp k v.
Proof.
  intros f t dep hp hlen v k Hg. cbn [pq_down]. rewrite Hg. reflexivity.
Qed.

(** The sift on a one-element heap fixes slot 1. *)
Lemma pqdownheap_singleton : forall t dep hp,
  pqdownheap t dep hp 1 1 1 = hp 1.
Proof.
  intros t dep hp. unfold pqdownheap.
  change 12%nat with (S 11)%nat.
  rewrite pq_down_norec by reflexivity.
  apply zset_same.
Qed.

(** ** One trip, on the shape

    Every intermediate array is a parameter with its defining equation
    (BtStep.v's discipline).  [fv] is the combined frequency and [dep'] the
    depth write — neither is constrained: counts and dads do not read them. *)
Section TripShape.

Variables (elems maxc1 : Z) (t1 : Tree) (hlen1 : Z).
Variables (t : Tree) (dep : zarr) (hp : zarr) (hl hm node : Z).
Variables (n m : Z) (A1 A2 A3 A4 A5 A6 : zarr) (t' : Tree) (fv : Z)
          (dep' : zarr).

Hypothesis Hme  : maxc1 < elems.
Hypothesis Hel  : 0 < elems <= L_CODES.
Hypothesis Hh1  : hlen1 <= L_CODES.
Hypothesis Hhl2 : 2 <= hl.
Hypothesis Hgap : 2 * hl + 1 <= hm.
Hypothesis Hhm  : hm <= HEAP_SIZE.
Hypothesis Hnd  : elems <= node.
Hypothesis Ehm  : hm = HEAP_SIZE - 2 * (node - elems).
Hypothesis Ehl  : hl = hlen1 - (node - elems).
Hypothesis Hcons : forall x,
  lcount hp hl x + pcount hp hm x
  = ind (live_b t1 maxc1 x) + ind ((elems <=? x) && (x <? node)).

Hypothesis En  : n = hp 1.
Hypothesis EA1 : A1 = zset hp 1 (hp hl).
Hypothesis EA2 : A2 = pqdownheap t dep A1 (hl - 1) 1.
Hypothesis Em  : m = A2 1.
Hypothesis EA3 : A3 = zset A2 (hm - 1) n.
Hypothesis EA4 : A4 = zset A3 (hm - 2) m.
Hypothesis Et' : t' = t_setdad (t_setdad (t_setfreq t node fv) m node) n node.
Hypothesis EA5 : A5 = zset A4 1 node.
Hypothesis EA6 : A6 = pqdownheap t' dep' A5 (hl - 1) 1.

(** The removed value's count, through the removal and the sift. *)
Lemma ts_lcount_A2 : forall x,
  lcount A2 (hl - 1) x = lcount hp hl x - ind (Z.eqb n x).
Proof.
  intro x.
  rewrite EA2, pqdownheap_count by lia.
  rewrite EA1, lcount_zset by lia.
  rewrite (lcount_shrink hp hl x) by lia.
  rewrite En. lia.
Qed.

Lemma ts_n_live : lcount hp hl n = 1 /\ pcount hp hm n = 0.
Proof.
  pose proof (Hcons n) as Hc.
  pose proof (total_le_1 elems maxc1 t1 node n Hme) as Hle.
  assert (Hmem : 1 <= lcount hp hl n)
    by (rewrite En; apply lcount_member; lia).
  pose proof (wcount_nonneg hp hm (Z.to_nat (HEAP_SIZE - hm)) n) as Hp0.
  unfold pcount in *. lia.
Qed.

Lemma ts_nm : n <> m /\ lcount hp hl m = 1 /\ pcount hp hm m = 0.
Proof.
  pose proof (Hcons m) as Hc.
  pose proof (total_le_1 elems maxc1 t1 node m Hme) as Hle.
  assert (Hmem : 1 <= lcount A2 (hl - 1) m)
    by (rewrite Em; apply lcount_member; lia).
  rewrite ts_lcount_A2 in Hmem.
  pose proof (wcount_nonneg hp hm (Z.to_nat (HEAP_SIZE - hm)) m) as Hp0.
  pose proof (ind_0_1 (Z.eqb n m)) as Hi.
  assert (Hne : n <> m).
  { intro Heq.
    rewrite <- Heq in Hmem, Hc, Hle, Hp0.
    rewrite Z.eqb_refl in Hmem. cbn [ind] in Hmem.
    unfold pcount in *. lia. }
  replace (Z.eqb n m) with false in Hmem
    by (symmetry; apply Z.eqb_neq; exact Hne).
  cbn [ind] in Hmem.
  unfold pcount in *. split; [exact Hne | lia].
Qed.

Lemma ts_node_fresh :
  lcount hp hl node = 0 /\ pcount hp hm node = 0
  /\ n <> node /\ m <> node.
Proof.
  pose proof (Hcons node) as Hc.
  rewrite (live_b_false_high t1 maxc1 node) in Hc by lia.
  replace ((elems <=? node) && (node <? node)) with false in Hc
    by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia).
  cbn [ind] in Hc.
  pose proof (wcount_nonneg hp 1 (Z.to_nat hl) node) as Hl0.
  pose proof (wcount_nonneg hp hm (Z.to_nat (HEAP_SIZE - hm)) node) as Hp0.
  unfold lcount, pcount in *.
  destruct ts_n_live as [Hn1 _]. destruct ts_nm as [_ [Hm1 _]].
  unfold lcount, pcount in *.
  split; [lia|]. split; [lia|].
  split; intro Heq; rewrite Heq in *; lia.
Qed.

Lemma ts_node_bound : 0 <= node < 65536.
Proof. unfold L_CODES in *. lia. Qed.

(** Old parked window: positions and values untouched. *)
Lemma ts_parked_frozen : forall p, hm <= p < HEAP_SIZE -> A6 p = hp p.
Proof.
  intros p Hp.
  rewrite EA6, pqdownheap_outside by lia.
  rewrite EA5, zset_other by lia.
  rewrite EA4, zset_other by lia.
  rewrite EA3, zset_other by lia.
  rewrite EA2, pqdownheap_outside by lia.
  rewrite EA1, zset_other by lia.
  reflexivity.
Qed.

Lemma ts_new_slots : A6 (hm - 1) = n /\ A6 (hm - 2) = m.
Proof.
  split.
  - rewrite EA6, pqdownheap_outside by lia.
    rewrite EA5, zset_other by lia.
    rewrite EA4, zset_other by lia.
    rewrite EA3, zset_same. reflexivity.
  - rewrite EA6, pqdownheap_outside by lia.
    rewrite EA5, zset_other by lia.
    rewrite EA4, zset_same. reflexivity.
Qed.

(** Live counts at trip exit. *)
Lemma ts_lcount_A6 : forall x,
  lcount A6 (hl - 1) x
  = lcount hp hl x - ind (Z.eqb n x) - ind (Z.eqb m x) + ind (Z.eqb node x).
Proof.
  intro x.
  rewrite EA6, pqdownheap_count by lia.
  assert (HA41 : A4 1 = m).
  { rewrite EA4, zset_other by lia. rewrite EA3, zset_other by lia.
    rewrite Em. reflexivity. }
  rewrite EA5, lcount_zset by lia.
  rewrite HA41.
  assert (HA4l : lcount A4 (hl - 1) x = lcount A2 (hl - 1) x).
  { apply lcount_ext; [lia|]. intros i Hi.
    rewrite EA4, zset_other by lia. rewrite EA3, zset_other by lia.
    reflexivity. }
  rewrite HA4l, ts_lcount_A2.
  rewrite (Z.eqb_sym m x), (Z.eqb_sym node x). lia.
Qed.

(** Parked counts at trip exit: the two fresh slots, then the frozen window. *)
Lemma ts_pcount_A6 : forall x,
  pcount A6 (hm - 2) x
  = pcount hp hm x + ind (Z.eqb n x) + ind (Z.eqb m x).
Proof.
  intro x.
  destruct ts_new_slots as [Hn1 Hm2].
  replace (hm - 2) with (hm - 1 - 1) by lia.
  rewrite (pcount_grow A6 (hm - 1) x) by lia.
  rewrite (pcount_grow A6 hm x) by lia.
  replace (hm - 1 - 1) with (hm - 2) by lia.
  rewrite Hn1, Hm2.
  rewrite (pcount_ext hp A6 hm x ts_parked_frozen).
  rewrite (Z.eqb_sym m x), (Z.eqb_sym n x). lia.
Qed.


(** Old parked values are neither of the two just-removed live values. *)
Lemma ts_parked_not_nm : forall p, hm <= p < HEAP_SIZE ->
  hp p <> n /\ hp p <> m.
Proof.
  intros p Hp.
  destruct ts_n_live as [_ Hpn]. destruct ts_nm as [_ [_ Hpm]].
  split; intro Heq.
  - pose proof (pcount_member hp hm p Hp) as H. rewrite Heq in H.
    unfold pcount in *. lia.
  - pose proof (pcount_member hp hm p Hp) as H. rewrite Heq in H.
    unfold pcount in *. lia.
Qed.

Hypothesis Hdad : forall c,
  wsum (fun p => ind (Z.eqb (t_dad t (hp p)) c)) hm (Z.to_nat (HEAP_SIZE - hm))
  = 2 * ind ((elems <=? c) && (c <? node)).
Hypothesis Hord : forall p, hm <= p < HEAP_SIZE ->
  elems <= t_dad t (hp p) < node
  /\ (1 <= lcount hp hl (t_dad t (hp p))
      \/ exists p', hm <= p' < p /\ hp p' = t_dad t (hp p)).
Hypothesis Hfrq : forall x, x < elems -> t_freq t x = t_freq t1 x.
Hypothesis Hdlf : forall y, lcount hp hl y + pcount hp hm y = 0 ->
                  tr_dl t y = tr_dl t1 y.

Lemma ts_dad_A6 : forall c,
  wsum (fun p => ind (Z.eqb (t_dad t' (A6 p)) c))
       (hm - 2) (Z.to_nat (HEAP_SIZE - (hm - 2)))
  = 2 * ind ((elems <=? c) && (c <? node + 1)).
Proof.
  intro c.
  destruct ts_new_slots as [Hn1 Hm2].
  destruct ts_nm as [Hnm _].
  pose proof ts_node_bound as Hnb.
  assert (Hsz : Z.to_nat (HEAP_SIZE - (hm - 2))
                = S (S (Z.to_nat (HEAP_SIZE - hm)))).
  { replace (HEAP_SIZE - (hm - 2)) with (Z.succ (Z.succ (HEAP_SIZE - hm)))
      by lia.
    rewrite !Z2Nat.inj_succ by lia. reflexivity. }
  rewrite Hsz.
  rewrite (wsum_split_first _ (hm - 2)).
  rewrite (wsum_split_first _ (hm - 2 + 1)).
  replace (hm - 2 + 1) with (hm - 1) by lia.
  replace (hm - 1 + 1) with hm by lia.
  rewrite Hn1, Hm2.
  rewrite Et'.
  rewrite (trip_dad t n m node fv m Hnm Hnb).
  rewrite (trip_dad t n m node fv n Hnm Hnb).
  replace (Z.eqb m n) with false by (symmetry; apply Z.eqb_neq; auto).
  rewrite !Z.eqb_refl.
  assert (Htail : wsum (fun p => ind (Z.eqb
              (t_dad (t_setdad (t_setdad (t_setfreq t node fv) m node) n node)
                     (A6 p)) c))
            hm (Z.to_nat (HEAP_SIZE - hm))
          = wsum (fun p => ind (Z.eqb (t_dad t (hp p)) c))
              hm (Z.to_nat (HEAP_SIZE - hm))).
  { apply wsum_ext. intros p Hp.
    assert (Hp' : hm <= p < HEAP_SIZE).
    { split; [lia|].
      destruct Hp as [_ Hp2]. rewrite Z2Nat.id in Hp2 by lia. lia. }
    rewrite (ts_parked_frozen p Hp').
    destruct (ts_parked_not_nm p Hp') as [Hpn Hpm].
    rewrite (trip_dad t n m node fv (hp p) Hnm Hnb).
    replace (Z.eqb (hp p) n) with false by (symmetry; apply Z.eqb_neq; auto).
    replace (Z.eqb (hp p) m) with false by (symmetry; apply Z.eqb_neq; auto).
    reflexivity. }
  rewrite Htail, (Hdad c).
  (* the created-range indicator extends by exactly the fresh node *)
  destruct (Z.eqb node c) eqn:Ec.
  - apply Z.eqb_eq in Ec. subst c.
    replace ((elems <=? node) && (node <? node)) with false
      by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia).
    replace ((elems <=? node) && (node <? node + 1)) with true
      by (symmetry; apply andb_true_intro;
          split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
    cbn [ind]. lia.
  - apply Z.eqb_neq in Ec.
    replace ((elems <=? c) && (c <? node + 1))
      with ((elems <=? c) && (c <? node)); [cbn [ind]; lia|].
    destruct (Z.ltb c node) eqn:El.
    + apply Z.ltb_lt in El.
      replace (Z.ltb c (node + 1)) with true
        by (symmetry; apply Z.ltb_lt; lia).
      reflexivity.
    + apply Z.ltb_ge in El.
      replace (Z.ltb c (node + 1)) with false
        by (symmetry; apply Z.ltb_ge; lia).
      reflexivity.
Qed.

Lemma ts_ord_A6 : forall p, hm - 2 <= p < HEAP_SIZE ->
  elems <= t_dad t' (A6 p) < node + 1
  /\ (1 <= lcount A6 (hl - 1) (t_dad t' (A6 p))
      \/ exists p', hm - 2 <= p' < p /\ A6 p' = t_dad t' (A6 p)).
Proof.
  intros p Hp.
  destruct ts_new_slots as [Hn1 Hm2].
  destruct ts_nm as [Hnm _].
  pose proof ts_node_bound as Hnb.
  destruct ts_node_fresh as [Hln [Hpn [Hnn Hmn]]].
  assert (Hnodecount : lcount A6 (hl - 1) node = 1).
  { rewrite ts_lcount_A6.
    replace (Z.eqb n node) with false by (symmetry; apply Z.eqb_neq; auto).
    replace (Z.eqb m node) with false by (symmetry; apply Z.eqb_neq; auto).
    rewrite Z.eqb_refl. cbn [ind]. lia. }
  destruct (Z.eq_dec p (hm - 2)) as [->|Hp2].
  { rewrite Hm2, Et', (trip_dad t n m node fv m Hnm Hnb).
    replace (Z.eqb m n) with false by (symmetry; apply Z.eqb_neq; auto).
    rewrite Z.eqb_refl.
    split; [lia|]. left. lia. }
  destruct (Z.eq_dec p (hm - 1)) as [->|Hp1].
  { rewrite Hn1, Et', (trip_dad t n m node fv n Hnm Hnb).
    rewrite Z.eqb_refl.
    split; [lia|]. left. lia. }
  assert (Hpw : hm <= p < HEAP_SIZE) by lia.
  rewrite (ts_parked_frozen p Hpw).
  destruct (ts_parked_not_nm p Hpw) as [Hxn Hxm].
  rewrite Et', (trip_dad t n m node fv (hp p) Hnm Hnb).
  replace (Z.eqb (hp p) n) with false by (symmetry; apply Z.eqb_neq; auto).
  replace (Z.eqb (hp p) m) with false by (symmetry; apply Z.eqb_neq; auto).
  destruct (Hord p Hpw) as [Hrange Hdisj].
  split; [lia|].
  set (d := t_dad t (hp p)) in *.
  destruct (Z.eq_dec d n) as [->|Hdn].
  { right. exists (hm - 1). split; [lia|]. exact Hn1. }
  destruct (Z.eq_dec d m) as [->|Hdm].
  { right. exists (hm - 2). split; [lia|]. exact Hm2. }
  destruct Hdisj as [Hlive|[p' [Hp' Heq]]].
  - left. rewrite ts_lcount_A6.
    replace (Z.eqb n d) with false
      by (symmetry; apply Z.eqb_neq; auto using not_eq_sym).
    replace (Z.eqb m d) with false
      by (symmetry; apply Z.eqb_neq; auto using not_eq_sym).
    pose proof (ind_0_1 (Z.eqb node d)). cbn [ind]. lia.
  - right. exists p'. split; [lia|].
    assert (Hp'w : hm <= p' < HEAP_SIZE) by lia.
    rewrite (ts_parked_frozen p' Hp'w). exact Heq.
Qed.

Lemma ts_frq_A6 : forall x, x < elems -> t_freq t' x = t_freq t1 x.
Proof.
  intros x Hx. rewrite Et', trip_freq by lia. apply Hfrq. exact Hx.
Qed.

Lemma ts_dlf_A6 : forall y,
  lcount A6 (hl - 1) y + pcount A6 (hm - 2) y = 0 ->
  tr_dl t' y = tr_dl t1 y.
Proof.
  intros y Htot0.
  rewrite ts_lcount_A6, ts_pcount_A6 in Htot0.
  pose proof (wcount_nonneg hp 1 (Z.to_nat hl) y) as Hl0.
  pose proof (wcount_nonneg hp hm (Z.to_nat (HEAP_SIZE - hm)) y) as Hp0.
  pose proof (ind_0_1 (Z.eqb node y)) as Hbn.
  destruct ts_n_live as [Hn1 _]. destruct ts_nm as [Hnm [Hm1 _]].
  unfold lcount, pcount in *.
  assert (Hyn : y <> n) by (intro He; rewrite <- He in Hn1; lia).
  assert (Hym : y <> m) by (intro He; rewrite <- He in Hm1; lia).
  rewrite Et'.
  unfold t_setdad. cbn [tr_dl].
  rewrite zset_other by exact Hyn.
  rewrite zset_other by exact Hym.
  change (tr_dl (t_setfreq t node fv) y) with (tr_dl t y).
  apply Hdlf. lia.
Qed.

(** The whole invariant at the successor state, assembled. *)
Lemma ts_census_out :
  CensusInv elems maxc1 t1 hlen1
    {| b_tree := t'; b_heap := A6; b_dep := dep';
       b_hlen := hl - 1; b_hmax := hm - 2; b_node := node + 1 |}.
Proof.
  constructor; cbn [b_tree b_heap b_dep b_hlen b_hmax b_node].
  - lia.
  - lia.
  - lia.
  - intro x.
    rewrite ts_lcount_A6, ts_pcount_A6.
    pose proof (Hcons x) as Hc.
    pose proof (created_extend elems node x ltac:(lia)) as Hext. lia.
  - exact ts_dad_A6.
  - exact ts_ord_A6.
  - exact ts_frq_A6.
  - exact ts_dlf_A6.
Qed.

(** The final trip's singleton sift leaves the fresh node at slot 1. *)
Lemma ts_done_slot : hl = 2 -> A6 1 = node.
Proof.
  intro H2.
  rewrite EA6, H2.
  replace (2 - 1) with 1 by lia.
  rewrite pqdownheap_singleton.
  rewrite EA5. apply zset_same.
Qed.

End TripShape.


(** ** The step and the loop, on [BtSt] *)

Lemma census_step : forall elems maxc1 t1 hlen1 st st',
  maxc1 < elems -> 0 < elems <= L_CODES -> hlen1 <= L_CODES ->
  2 <= b_hlen st -> Gap st -> b_hmax st <= HEAP_SIZE ->
  (bt_step st = BtCont st' \/ bt_step st = BtDone st') ->
  CensusInv elems maxc1 t1 hlen1 st ->
  CensusInv elems maxc1 t1 hlen1 st'
  /\ b_hlen st' = b_hlen st - 1
  /\ b_hmax st' = b_hmax st - 2
  /\ b_node st' = b_node st + 1
  /\ (b_hlen st = 2 -> b_heap st' 1 = b_node st).
Proof.
  intros elems maxc1 t1 hlen1 st st' Hme Hel Hh1 Hhl2 Hgap Hhm Hst Hinv.
  destruct Hinv as [Hnd Ehm Ehl Hcons Hdad Hord Hfrq Hdlf].
  unfold Gap in Hgap.
  unfold bt_step, SMALLEST in Hst. cbv zeta in Hst.
  destruct (Z.leb 2 (b_hlen st - 1));
    destruct Hst as [Hst|Hst]; try discriminate;
    inversion Hst; subst st'; cbn [b_tree b_heap b_dep b_hlen b_hmax b_node];
    replace (b_hmax st - 1 - 1) with (b_hmax st - 2) by lia;
    (split;
     [ eapply ts_census_out; try reflexivity; try assumption; lia
     | split; [reflexivity | split; [reflexivity | split; [reflexivity|]]];
       intro H2; eapply ts_done_slot; try reflexivity; exact H2 ]).
Qed.

Lemma census_loop : forall fuel elems maxc1 t1 hlen1 st,
  maxc1 < elems -> 0 < elems <= L_CODES -> hlen1 <= L_CODES ->
  2 <= b_hlen st -> Gap st -> b_hmax st <= HEAP_SIZE ->
  CensusInv elems maxc1 t1 hlen1 st ->
  match bt_loop fuel st with
  | Some stf => CensusInv elems maxc1 t1 hlen1 stf
                /\ b_hlen stf = 1
                /\ b_heap stf 1 = b_node stf - 1
  | None => True
  end.
Proof.
  induction fuel as [|f IH];
    intros elems maxc1 t1 hlen1 st Hme Hel Hh1 Hhl2 Hgap Hhm Hinv.
  - exact I.
  - cbn [bt_loop].
    destruct (bt_step st) as [st'|st'] eqn:Est.
    + assert (Hor : bt_step st = BtCont st' \/ bt_step st = BtDone st')
        by (left; exact Est).
      destruct (census_step elems maxc1 t1 hlen1 st st'
                  Hme Hel Hh1 Hhl2 Hgap Hhm Hor Hinv)
        as [Hinv' [Ehl' [Ehm' [End' Hdone]]]].
      assert (Hlen' : 2 <= b_hlen st').
      { unfold bt_step, SMALLEST in Est. cbv zeta in Est.
        destruct (Z.leb 2 (b_hlen st - 1)) eqn:E2; [|discriminate].
        apply Z.leb_le in E2. lia. }
      assert (Hgap' : Gap st') by (unfold Gap in *; lia).
      assert (Hhm' : b_hmax st' <= HEAP_SIZE) by lia.
      exact (IH elems maxc1 t1 hlen1 st' Hme Hel Hh1 Hlen' Hgap' Hhm' Hinv').
    + assert (Hor : bt_step st = BtCont st' \/ bt_step st = BtDone st')
        by (right; exact Est).
      destruct (census_step elems maxc1 t1 hlen1 st st'
                  Hme Hel Hh1 Hhl2 Hgap Hhm Hor Hinv)
        as [Hinv' [Ehl' [Ehm' [End' Hdone]]]].
      assert (H2 : b_hlen st = 2).
      { unfold bt_step, SMALLEST in Est. cbv zeta in Est.
        destruct (Z.leb 2 (b_hlen st - 1)) eqn:E2; [discriminate|].
        apply Z.leb_gt in E2. lia. }
      split; [exact Hinv'|]. split; [lia|].
      rewrite (Hdone H2). lia.
Qed.

Print Assumptions census_step.
Print Assumptions census_loop.
