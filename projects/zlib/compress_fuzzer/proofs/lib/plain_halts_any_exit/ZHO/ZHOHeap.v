(** * ZHOHeap — the heap ORDER side: zlib's priority queue extracts the
      (freq, depth)-lex minima.

    OWNER: huffman-opt.  The landed corpus (PqDown/BtCensus1) has the
    MULTISET side (lcount preservation); nothing anywhere orders the heap.
    This file adds exactly that: [smaller] is a total transitive preorder,
    [HeapOkFrom] is the array-heap property, [bt_heapify] establishes it,
    the two [pqdownheap] calls inside [bt_step] restore it, and therefore
    each combine-loop trip pops the two lex-minimal live elements.

    This is L1 of the cost-optimality architecture (STRATEGY-MEMO §3):
    L2 consumes [bt_step_minima] to inhabit Théry's [one_step].

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtStep BtCensus1.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 0. Helpers (window counts, tree-projection frames, div facts) *)

Lemma zho_div2_lt : forall j, 1 <= j -> j / 2 < j.
Proof. intros j Hj. apply Z.div_lt; lia. Qed.

Lemma zho_div2_ge1 : forall j, 2 <= j -> 1 <= j / 2.
Proof. intros j Hj. apply Z.div_le_lower_bound; lia. Qed.

Lemma zho_child_of : forall j k, 2 <= j -> j / 2 = k -> j = 2 * k \/ j = 2 * k + 1.
Proof.
  intros j k Hj Hd.
  pose proof (Z.div_mod j 2 ltac:(lia)) as He.
  pose proof (Z.mod_pos_bound j 2 ltac:(lia)) as Hm.
  lia.
Qed.

Lemma zho_mul2_div : forall k, (2 * k) / 2 = k.
Proof. intro k. rewrite Z.mul_comm. apply Z.div_mul. lia. Qed.

Lemma zho_mul2p1_div : forall k, (2 * k + 1) / 2 = k.
Proof.
  intro k. replace (2 * k + 1) with (1 + k * 2) by ring.
  rewrite Z.div_add by lia.
  rewrite Z.div_small by lia. ring.
Qed.

Lemma t_freq_setfreq_other : forall t i v j,
  j <> i -> t_freq (t_setfreq t i v) j = t_freq t j.
Proof.
  intros t i v j H. unfold t_freq, t_setfreq. cbn [tr_fc].
  apply zset_other. exact H.
Qed.

Lemma t_freq_setdad : forall t i v j,
  t_freq (t_setdad t i v) j = t_freq t j.
Proof. reflexivity. Qed.

Lemma lcount_split_last : forall a hlen x,
  1 <= hlen ->
  lcount a hlen x = lcount a (hlen - 1) x + ind (Z.eqb (a hlen) x).
Proof.
  intros a hlen x H. unfold lcount, wcount.
  replace (Z.to_nat hlen) with (S (Z.to_nat (hlen - 1))) by lia.
  rewrite wsum_split_last.
  replace (1 + Z.of_nat (Z.to_nat (hlen - 1))) with hlen by lia.
  reflexivity.
Qed.

Lemma lcount_zset_out : forall a hlen i v x,
  hlen < i ->
  lcount (zset a i v) hlen x = lcount a hlen x.
Proof.
  intros a hlen i v x H. unfold lcount. apply wcount_ext_window.
  intros j Hj. apply zset_other. lia.
Qed.

Lemma lcount_pos_inv : forall a hlen x,
  1 <= lcount a hlen x -> exists i, 1 <= i <= hlen /\ a i = x.
Proof.
  intros a hlen x H.
  destruct (wcount_pos_inv a 1 (Z.to_nat hlen) x H) as (i & Hi & Hx).
  exists i. split; [lia | exact Hx].
Qed.

Lemma lcount_of_member : forall a hlen i,
  1 <= i <= hlen -> 1 <= lcount a hlen (a i).
Proof.
  intros a hlen i Hi.
  apply (wcount_of_member a 1 (Z.to_nat hlen) (a i) i); [lia | reflexivity].
Qed.

(** ** 1. [smaller] is a total transitive preorder *)

Lemma smaller_total : forall t dep n m,
  smaller t dep n m = true \/ smaller t dep m n = true.
Proof.
  intros t dep n m. unfold smaller.
  destruct (Z.ltb_spec (t_freq t n) (t_freq t m));
    destruct (Z.ltb_spec (t_freq t m) (t_freq t n));
    destruct (Z.eqb_spec (t_freq t n) (t_freq t m));
    destruct (Z.eqb_spec (t_freq t m) (t_freq t n));
    destruct (Z.leb_spec (dep n) (dep m));
    destruct (Z.leb_spec (dep m) (dep n));
    cbn [orb andb]; auto; lia.
Qed.

Lemma smaller_trans : forall t dep a b c,
  smaller t dep a b = true -> smaller t dep b c = true ->
  smaller t dep a c = true.
Proof.
  intros t dep a b c Hab Hbc. unfold smaller in *.
  apply orb_true_iff in Hab. apply orb_true_iff in Hbc.
  apply orb_true_iff.
  destruct Hab as [Hab|Hab]; destruct Hbc as [Hbc|Hbc].
  - left. apply Z.ltb_lt in Hab. apply Z.ltb_lt in Hbc.
    apply Z.ltb_lt. lia.
  - apply andb_true_iff in Hbc as [He Hd]. apply Z.eqb_eq in He.
    left. apply Z.ltb_lt in Hab. apply Z.ltb_lt. lia.
  - apply andb_true_iff in Hab as [He Hd]. apply Z.eqb_eq in He.
    left. apply Z.ltb_lt in Hbc. apply Z.ltb_lt. lia.
  - apply andb_true_iff in Hab as [He1 Hd1].
    apply andb_true_iff in Hbc as [He2 Hd2].
    apply Z.eqb_eq in He1. apply Z.eqb_eq in He2.
    apply Z.leb_le in Hd1. apply Z.leb_le in Hd2.
    right. apply andb_true_iff. split.
    + apply Z.eqb_eq. lia.
    + apply Z.leb_le. lia.
Qed.

Lemma smaller_refl : forall t dep n, smaller t dep n n = true.
Proof.
  intros t dep n. unfold smaller.
  rewrite Z.eqb_refl, Z.leb_refl, andb_true_r, orb_true_r.
  reflexivity.
Qed.

(** [smaller] reads only [t_freq] and [dep] at its two indices: frame. *)
Lemma smaller_frame : forall t t' dep dep' a b,
  t_freq t a = t_freq t' a -> t_freq t b = t_freq t' b ->
  dep a = dep' a -> dep b = dep' b ->
  smaller t dep a b = smaller t' dep' a b.
Proof.
  intros t t' dep dep' a b H1 H2 H3 H4. unfold smaller.
  rewrite H1, H2, H3, H4. reflexivity.
Qed.

(** ** 2. The array-heap property *)

(** All parent-child pairs with parent slot [>= n] are ordered.  The full
    heap property is [HeapOkFrom .. 1]; [bt_heapify]'s loop invariant is
    [HeapOkFrom .. (n+1)]; "heap with a fresh root" is [HeapOkFrom .. 2]. *)
Definition HeapOkFrom (t : Tree) (dep hp : zarr) (hlen n : Z) : Prop :=
  forall j, 2 <= j <= hlen -> n <= j / 2 ->
    smaller t dep (hp (j / 2)) (hp j) = true.

Lemma heapokfrom_vacuous : forall t dep hp hlen n,
  hlen < 2 * n -> HeapOkFrom t dep hp hlen n.
Proof.
  intros t dep hp hlen n Hlt j Hj Hn. exfalso.
  assert (j / 2 < n) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(** the root of a heap is lex-minimal over the window *)
Theorem heap_root_min : forall t dep hp hlen j,
  HeapOkFrom t dep hp hlen 1 -> 1 <= j <= hlen ->
  smaller t dep (hp 1) (hp j) = true.
Proof.
  intros t dep hp hlen j Hok.
  remember (Z.to_nat j) as nj eqn:Enj. revert j Enj.
  induction nj as [nj IH] using Wf_nat.lt_wf_ind; intros j Enj Hj.
  destruct (Z.eqb_spec j 1) as [->|Hne]; [apply smaller_refl|].
  assert (Hd1 : 1 <= j / 2) by (apply zho_div2_ge1; lia).
  assert (Hdlt : j / 2 < j) by (apply zho_div2_lt; lia).
  eapply smaller_trans.
  - apply (IH (Z.to_nat (j / 2))); [lia | reflexivity | lia].
  - apply Hok; lia.
Qed.

(** ** 3. Sift-down: [pqdownheap] at [n] extends the heap region by one *)

(** [pq_down]'s slots below [k] are never written. *)
Lemma pq_down_below : forall fuel t dep hp hlen v k p,
  1 <= p < k -> pq_down fuel t dep hp hlen v k p = hp p.
Proof.
  induction fuel as [|f IH]; intros t dep hp hlen v k p Hp.
  - cbn [pq_down]. apply zset_other. lia.
  - cbn [pq_down].
    destruct (Z.leb (2 * k) hlen) eqn:E2k;
      [apply Z.leb_le in E2k | apply zset_other; lia].
    remember (if (Z.ltb (2 * k) hlen)
                 && smaller t dep (hp (2 * k + 1)) (hp (2 * k))
              then 2 * k + 1 else 2 * k) as j' eqn:Ej'.
    assert (Hkj : k < j').
    { subst j'.
      destruct ((Z.ltb (2 * k) hlen)
                  && smaller t dep (hp (2 * k + 1)) (hp (2 * k))); lia. }
    destruct (smaller t dep v (hp j')) eqn:Es.
    + apply zset_other. lia.
    + rewrite IH by lia. apply zset_other. lia.
Qed.

(** The generalized sift-down invariant.  The hole is at slot [k]; [v] is
    the value descending; (A') = all in-region pairs not touching the hole;
    (B') = if the hole has an in-region parent, that parent beats [v] AND
    both of the hole's children (the values the promotion can move up). *)
Lemma pq_down_heapok : forall fuel t dep hp hlen v k n,
  1 <= n -> n <= k <= hlen ->
  2 ^ Z.of_nat fuel * k > hlen ->
  (forall j, 2 <= j <= hlen -> n <= j / 2 -> j / 2 <> k -> j <> k ->
     smaller t dep (hp (j / 2)) (hp j) = true) ->
  (2 <= k -> n <= k / 2 ->
     smaller t dep (hp (k / 2)) v = true
     /\ (2 * k <= hlen -> smaller t dep (hp (k / 2)) (hp (2 * k)) = true)
     /\ (2 * k + 1 <= hlen ->
           smaller t dep (hp (k / 2)) (hp (2 * k + 1)) = true)) ->
  HeapOkFrom t dep (pq_down fuel t dep hp hlen v k) hlen n.
Proof.
  induction fuel as [|f IH]; intros t dep hp hlen v k n Hn Hk Hfuel HA HB.
  - exfalso.
    change (Z.of_nat 0) with 0 in Hfuel.
    rewrite Z.pow_0_r in Hfuel. lia.
  - cbn [pq_down].
    destruct (Z.leb_spec (2 * k) hlen) as [Hch|Hch].
    + (* children exist *)
      remember (if (Z.ltb (2 * k) hlen)
                   && smaller t dep (hp (2 * k + 1)) (hp (2 * k))
                then 2 * k + 1 else 2 * k) as j' eqn:Ej'.
      assert (Hj'w : 2 * k <= j' <= hlen).
      { subst j'.
        destruct ((Z.ltb (2 * k) hlen)
                    && smaller t dep (hp (2 * k + 1)) (hp (2 * k))) eqn:Eb;
          [|lia].
        apply andb_prop in Eb as [Hlt _]. apply Z.ltb_lt in Hlt. lia. }
      assert (Hj'or : j' = 2 * k \/ j' = 2 * k + 1).
      { subst j'.
        destruct ((Z.ltb (2 * k) hlen)
                    && smaller t dep (hp (2 * k + 1)) (hp (2 * k))); lia. }
      assert (Hj'd : j' / 2 = k).
      { destruct Hj'or as [->| ->];
          [apply zho_mul2_div | apply zho_mul2p1_div]. }
      (* j' is a lex-least child *)
      assert (Hminc : forall c, c = 2 * k \/ c = 2 * k + 1 -> c <= hlen ->
                smaller t dep (hp j') (hp c) = true).
      { intros c Hc Hcw. subst j'.
        destruct ((Z.ltb (2 * k) hlen)
                    && smaller t dep (hp (2 * k + 1)) (hp (2 * k))) eqn:Eb.
        - apply andb_prop in Eb as [_ Hs].
          destruct Hc as [->| ->]; [exact Hs | apply smaller_refl].
        - destruct Hc as [->| ->]; [apply smaller_refl|].
          apply andb_false_iff in Eb as [Hlt | Hs].
          + apply Z.ltb_ge in Hlt. lia.
          + destruct (smaller_total t dep (hp (2 * k)) (hp (2 * k + 1)))
              as [Hx|Hx]; [exact Hx | congruence]. }
      destruct (smaller t dep v (hp j')) eqn:Estop.
      * (* STOP: write v at k *)
        intros j Hjw Hjn.
        destruct (Z.eqb_spec j k) as [->|Hjk].
        { (* pair (k/2, k): parent slot untouched, k now holds v *)
          assert (Hkd : k / 2 < k) by (apply zho_div2_lt; lia).
          rewrite zset_same, zset_other by lia.
          destruct (HB ltac:(lia) ltac:(lia)) as [HB1 _]. exact HB1. }
        destruct (Z.eqb_spec (j / 2) k) as [Hpk|Hpk].
        { (* pair (k, child of k): parent now v, child untouched *)
          rewrite Hpk, zset_same, zset_other by lia.
          assert (Hjc : j = 2 * k \/ j = 2 * k + 1)
            by (apply zho_child_of; [lia | exact Hpk]).
          eapply smaller_trans; [exact Estop|].
          apply Hminc; [exact Hjc | lia]. }
        { (* untouched pair *)
          rewrite zset_other by lia. rewrite zset_other by lia.
          apply HA; [lia | exact Hjn | exact Hpk | exact Hjk]. }
      * (* DESCEND: promote hp j' into k, hole moves to j' *)
        assert (Hj'v : smaller t dep (hp j') v = true).
        { destruct (smaller_total t dep v (hp j')) as [Hx|Hx];
            [congruence | exact Hx]. }
        apply IH.
        { exact Hn. }
        { lia. }
        { rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hfuel by lia.
          assert (0 < 2 ^ Z.of_nat f)
            by (apply Z.pow_pos_nonneg; lia).
          nia. }
        { (* A' for the new hole j' *)
          intros j Hjw Hjn Hpj' Hjj'.
          destruct (Z.eqb_spec j k) as [->|Hjk].
          { (* pair (k/2, k): k now holds hp j', a child of the old hole *)
            assert (Hkd : k / 2 < k) by (apply zho_div2_lt; lia).
            rewrite zset_same, zset_other by lia.
            destruct (HB ltac:(lia) ltac:(lia)) as [_ [HB2 HB3]].
            destruct Hj'or as [Ej2|Ej2]; rewrite Ej2.
            - apply HB2; lia.
            - apply HB3; lia. }
          destruct (Z.eqb_spec (j / 2) k) as [Hpk|Hpk].
          { (* pair (k, other child): parent now holds hp j' *)
            rewrite Hpk, zset_same, zset_other by lia.
            assert (Hjc : j = 2 * k \/ j = 2 * k + 1)
              by (apply zho_child_of; [lia | exact Hpk]).
            apply Hminc; [exact Hjc | lia]. }
          { rewrite zset_other by lia. rewrite zset_other by lia.
            apply HA; [lia | exact Hjn | exact Hpk | exact Hjk]. }
        }
        { (* B' for the new hole j': its parent slot is k, holding hp j' *)
          intros H2j' Hnj'2.
          rewrite Hj'd, zset_same.
          split; [|split].
          - exact Hj'v.
          - intro Hw. rewrite zset_other by lia.
            assert (E : (2 * j') / 2 = j') by apply zho_mul2_div.
            specialize (HA (2 * j') ltac:(lia)).
            rewrite E in HA. apply HA; lia.
          - intro Hw. rewrite zset_other by lia.
            assert (E : (2 * j' + 1) / 2 = j') by apply zho_mul2p1_div.
            specialize (HA (2 * j' + 1) ltac:(lia)).
            rewrite E in HA. apply HA; lia.
        }
    + (* no children: write v at k *)
      intros j Hjw Hjn.
      destruct (Z.eqb_spec j k) as [->|Hjk].
      { assert (Hkd : k / 2 < k) by (apply zho_div2_lt; lia).
        rewrite zset_same, zset_other by lia.
        destruct (HB ltac:(lia) ltac:(lia)) as [HB1 _]. exact HB1. }
      destruct (Z.eqb_spec (j / 2) k) as [Hpk|Hpk].
      { exfalso.
        assert (Hjc : j = 2 * k \/ j = 2 * k + 1)
          by (apply zho_child_of; [lia | exact Hpk]).
        lia. }
      { rewrite zset_other by lia. rewrite zset_other by lia.
        apply HA; [lia | exact Hjn | exact Hpk | exact Hjk]. }
Qed.

Theorem pqdownheap_extend : forall t dep hp hlen n,
  1 <= n <= hlen -> hlen <= 573 ->
  HeapOkFrom t dep hp hlen (n + 1) ->
  HeapOkFrom t dep (pqdownheap t dep hp hlen n) hlen n.
Proof.
  intros t dep hp hlen n Hn Hcap Hok.
  unfold pqdownheap.
  apply pq_down_heapok.
  - lia.
  - lia.
  - assert (E : 2 ^ Z.of_nat 12 = 4096) by reflexivity. nia.
  - intros j Hj Hn2 Hne _. apply Hok; [lia | lia].
  - intros H2 Hle. exfalso.
    assert (n / 2 < n) by (apply zho_div2_lt; lia). lia.
Qed.

(** ** 4. [bt_heapify] establishes the heap property *)

Theorem bt_heapify_heapok : forall fuel t dep hp hlen n,
  Z.of_nat fuel >= n -> 0 <= n <= hlen -> hlen <= 573 ->
  HeapOkFrom t dep hp hlen (n + 1) ->
  HeapOkFrom t dep (bt_heapify fuel t dep hp hlen n) hlen 1.
Proof.
  induction fuel as [|f IH]; intros t dep hp hlen n Hf Hn Hcap Hok.
  - cbn [bt_heapify]. assert (n = 0) by lia. subst n.
    replace 1 with (0 + 1) by lia. exact Hok.
  - cbn [bt_heapify].
    destruct (Z.ltb_spec n 1) as [Hlt|Hge].
    + assert (n = 0) by lia. subst n.
      replace 1 with (0 + 1) by lia. exact Hok.
    + apply IH; [lia | lia | lia |].
      replace (n - 1 + 1) with n by lia.
      apply pqdownheap_extend; [lia | lia | exact Hok].
Qed.

(** ** 5. One [bt_step] trip pops the two lex-minima *)

(** live indices sit strictly below the node counter (freshness), so the
    trip's [t_setfreq]/[t_setdad]/[dep] writes at [node]/[n]/[m] cannot
    alias a surviving live slot.  Discharged at integration from the
    landed census invariant. *)
Record StepPre (st : BtSt) : Prop := mkStepPre {
  sp_hlen  : 2 <= b_hlen st;
  sp_cap   : 2 * b_hlen st + 1 <= b_hmax st /\ b_hmax st <= HEAP_SIZE;
  sp_heap  : HeapOkFrom (b_tree st) (b_dep st) (b_heap st) (b_hlen st) 1;
  sp_fresh : forall p, 1 <= p <= b_hlen st -> b_heap st p < b_node st
}.

(** the two pqremove results, named as [bt_step] computes them *)
Definition zho_n (st : BtSt) : Z := b_heap st SMALLEST.
Definition zho_hp2 (st : BtSt) : zarr :=
  pqdownheap (b_tree st) (b_dep st)
             (zset (b_heap st) SMALLEST (b_heap st (b_hlen st)))
             (b_hlen st - 1) SMALLEST.
Definition zho_m (st : BtSt) : Z := zho_hp2 st SMALLEST.

(** the successor record, mirroring [bt_step]'s let-chain verbatim so that
    [bt_step_eq] holds by conversion *)
Definition zho_succ (st : BtSt) : BtSt :=
  let n     := b_heap st SMALLEST in
  let hp1   := zset (b_heap st) SMALLEST (b_heap st (b_hlen st)) in
  let hlen1 := b_hlen st - 1 in
  let hp2   := pqdownheap (b_tree st) (b_dep st) hp1 hlen1 SMALLEST in
  let m     := hp2 SMALLEST in
  let hmax1 := b_hmax st - 1 in
  let hp3   := zset hp2 hmax1 n in
  let hmax2 := hmax1 - 1 in
  let hp4   := zset hp3 hmax2 m in
  let node  := b_node st in
  let t1    := t_setfreq (b_tree st) node
                 (t_freq (b_tree st) n + t_freq (b_tree st) m) in
  let dep1  := zset (b_dep st) node
                 (u8 ((if Z.leb (b_dep st m) (b_dep st n)
                       then b_dep st n else b_dep st m) + 1)) in
  let t2    := t_setdad (t_setdad t1 m node) n node in
  let hp5   := zset hp4 SMALLEST node in
  let hp6   := pqdownheap t2 dep1 hp5 hlen1 SMALLEST in
  {| b_tree := t2; b_heap := hp6; b_dep := dep1;
     b_hlen := hlen1; b_hmax := hmax2; b_node := node + 1 |}.

Lemma bt_step_eq : forall st,
  bt_step st = if Z.leb 2 (b_hlen st - 1)
               then BtCont (zho_succ st) else BtDone (zho_succ st).
Proof. reflexivity. Qed.

Lemma bt_step_succ : forall st st',
  bt_step st = BtCont st' \/ bt_step st = BtDone st' -> st' = zho_succ st.
Proof.
  intros st st' H. rewrite bt_step_eq in H.
  destruct (Z.leb 2 (b_hlen st - 1));
    destruct H as [H|H]; try discriminate; now inversion H.
Qed.

Theorem bt_step_minima : forall st,
  StepPre st ->
  (* (i) n is lex-minimal over the live window *)
  (forall j, 1 <= j <= b_hlen st ->
     smaller (b_tree st) (b_dep st) (zho_n st) (b_heap st j) = true)
  (* (ii) m is lex-minimal over the remainder *)
  /\ (forall j, 1 <= j <= b_hlen st - 1 ->
     smaller (b_tree st) (b_dep st) (zho_m st) (zho_hp2 st j) = true)
  (* (iii) the remainder is the live multiset minus one occurrence of n *)
  /\ (forall x, lcount (zho_hp2 st) (b_hlen st - 1) x
       = lcount (b_heap st) (b_hlen st) x - ind (Z.eqb (zho_n st) x))
  (* (iv) the successor state: multiset = remainder minus m plus node,
          and StepPre is preserved when the loop continues *)
  /\ (forall st', bt_step st = BtCont st' \/ bt_step st = BtDone st' ->
        b_node st' = b_node st + 1
        /\ b_hlen st' = b_hlen st - 1
        /\ (forall x, lcount (b_heap st') (b_hlen st') x
             = lcount (zho_hp2 st) (b_hlen st - 1) x
               - ind (Z.eqb (zho_m st) x) + ind (Z.eqb (b_node st) x))
        /\ (2 <= b_hlen st' -> StepPre st')).
Proof.
  intros st Hpre.
  destruct Hpre as [Hhl Hcap Hheap Hfresh].
  destruct Hcap as [Hgap Hhs].
  assert (Hlen286 : b_hlen st <= 286) by (unfold HEAP_SIZE in Hhs; lia).
  unfold zho_n, zho_m, zho_hp2, SMALLEST.
  (* the remainder heap: root replaced by the last slot, then sifted *)
  assert (Hok2' : HeapOkFrom (b_tree st) (b_dep st)
                    (zset (b_heap st) 1 (b_heap st (b_hlen st)))
                    (b_hlen st - 1) 2).
  { intros j Hj Hn.
    pose proof (Z.mul_div_le j 2 ltac:(lia)) as Hmd.
    assert (Hjge : 4 <= j) by lia.
    assert (Hjd1 : 1 <= j / 2) by (apply zho_div2_ge1; lia).
    rewrite zset_other by lia.
    rewrite zset_other by lia.
    apply Hheap; lia. }
  assert (Hokr : HeapOkFrom (b_tree st) (b_dep st)
                   (pqdownheap (b_tree st) (b_dep st)
                      (zset (b_heap st) 1 (b_heap st (b_hlen st)))
                      (b_hlen st - 1) 1)
                   (b_hlen st - 1) 1).
  { apply pqdownheap_extend; [lia | lia |].
    replace (1 + 1) with 2 by lia. exact Hok2'. }
  set (hp2 := pqdownheap (b_tree st) (b_dep st)
                (zset (b_heap st) 1 (b_heap st (b_hlen st)))
                (b_hlen st - 1) 1) in *.
  assert (Hcnt : forall x, lcount hp2 (b_hlen st - 1) x
       = lcount (b_heap st) (b_hlen st) x - ind (Z.eqb (b_heap st 1) x)).
  { intro x. unfold hp2.
    rewrite pqdownheap_count by lia.
    rewrite lcount_zset by lia.
    rewrite (lcount_split_last (b_heap st) (b_hlen st) x) by lia.
    lia. }
  assert (Hfresh2 : forall p, 1 <= p <= b_hlen st - 1 -> hp2 p < b_node st).
  { intros p Hp.
    assert (H1 : 1 <= lcount hp2 (b_hlen st - 1) (hp2 p))
      by (apply lcount_of_member; lia).
    rewrite Hcnt in H1.
    pose proof (ind_0_1 (Z.eqb (b_heap st 1) (hp2 p))).
    assert (H2 : 1 <= lcount (b_heap st) (b_hlen st) (hp2 p)) by lia.
    destruct (lcount_pos_inv _ _ _ H2) as (i & Hi & Hx).
    rewrite <- Hx. apply Hfresh. exact Hi. }
  split; [|split; [|split]].
  - (* (i) *)
    intros j Hj.
    apply (heap_root_min _ _ _ (b_hlen st)); [exact Hheap | exact Hj].
  - (* (ii) *)
    intros j Hj.
    apply (heap_root_min _ _ _ (b_hlen st - 1)); [exact Hokr | exact Hj].
  - exact Hcnt.
  - (* (iv) *)
    intros st' Hst.
    apply bt_step_succ in Hst. subst st'.
    unfold zho_succ, SMALLEST. cbv zeta.
    cbn [b_tree b_heap b_dep b_hlen b_hmax b_node].
    fold hp2.
    set (n0 := b_heap st 1) in *.
    set (m0 := hp2 1) in *.
    set (node0 := b_node st) in *.
    set (t1' := t_setfreq (b_tree st) node0
                  (t_freq (b_tree st) n0 + t_freq (b_tree st) m0)) in *.
    set (dep1 := zset (b_dep st) node0
                   (u8 ((if Z.leb (b_dep st m0) (b_dep st n0)
                         then b_dep st n0 else b_dep st m0) + 1))) in *.
    set (t2' := t_setdad (t_setdad t1' m0 node0) n0 node0) in *.
    set (hp4 := zset (zset hp2 (b_hmax st - 1) n0)
                  (b_hmax st - 1 - 1) m0) in *.
    set (hp5 := zset hp4 1 node0) in *.
    set (hp6 := pqdownheap t2' dep1 hp5 (b_hlen st - 1) 1) in *.
    assert (Ehp41 : hp4 1 = m0).
    { unfold hp4. rewrite zset_other by lia.
      rewrite zset_other by lia. reflexivity. }
    assert (Hcnt6 : forall x, lcount hp6 (b_hlen st - 1) x
                = lcount hp2 (b_hlen st - 1) x
                  - ind (Z.eqb m0 x) + ind (Z.eqb node0 x)).
    { intro x. unfold hp6.
      rewrite pqdownheap_count by lia.
      unfold hp5.
      rewrite lcount_zset by lia.
      rewrite Ehp41.
      unfold hp4.
      rewrite lcount_zset_out by lia.
      rewrite lcount_zset_out by lia.
      lia. }
    assert (Hfresh6 : forall p, 1 <= p <= b_hlen st - 1 ->
              hp6 p < node0 + 1).
    { intros p Hp.
      assert (H1 : 1 <= lcount hp6 (b_hlen st - 1) (hp6 p))
        by (apply lcount_of_member; lia).
      rewrite Hcnt6 in H1.
      destruct (Z.eqb_spec node0 (hp6 p)) as [Heq|Hne]; [lia|].
      cbn [ind] in H1.
      pose proof (ind_0_1 (Z.eqb m0 (hp6 p))).
      assert (H2 : 1 <= lcount hp2 (b_hlen st - 1) (hp6 p)) by lia.
      destruct (lcount_pos_inv _ _ _ H2) as (i & Hi & Hx).
      rewrite <- Hx.
      assert (hp2 i < b_node st) by (apply Hfresh2; exact Hi).
      unfold node0. lia. }
    assert (Hheap6 : HeapOkFrom t2' dep1 hp6 (b_hlen st - 1) 1).
    { unfold hp6. apply pqdownheap_extend; [lia | lia |].
      replace (1 + 1) with 2 by lia.
      intros j Hj Hn2.
      pose proof (Z.mul_div_le j 2 ltac:(lia)) as Hmd.
      assert (Hjge : 4 <= j) by lia.
      assert (Hjd1 : 1 <= j / 2) by (apply zho_div2_ge1; lia).
      unfold hp5.
      rewrite zset_other by lia.
      rewrite zset_other by lia.
      unfold hp4.
      rewrite zset_other by lia. rewrite zset_other by lia.
      rewrite zset_other by lia. rewrite zset_other by lia.
      assert (Hv1 : hp2 (j / 2) < node0) by (apply Hfresh2; lia).
      assert (Hv2 : hp2 j < node0) by (apply Hfresh2; lia).
      rewrite (smaller_frame t2' (b_tree st) dep1 (b_dep st)).
      - apply Hokr; lia.
      - unfold t2'. rewrite !t_freq_setdad.
        apply t_freq_setfreq_other. lia.
      - unfold t2'. rewrite !t_freq_setdad.
        apply t_freq_setfreq_other. lia.
      - unfold dep1. apply zset_other. lia.
      - unfold dep1. apply zset_other. lia. }
    split; [reflexivity | split; [reflexivity | split]].
    + intro x. apply Hcnt6.
    + intro Hhl'.
      constructor; cbn [b_tree b_heap b_dep b_hlen b_hmax b_node].
      * exact Hhl'.
      * split; lia.
      * exact Hheap6.
      * exact Hfresh6.
Qed.
