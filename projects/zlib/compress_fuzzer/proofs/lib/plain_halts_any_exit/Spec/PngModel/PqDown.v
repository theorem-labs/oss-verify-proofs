(** * PqDown — the residual named in §HUFFID-BTCOVER, and it is CHEAPER than I
      priced it, because (B-lower) does not need "permutes".

    OWNER: huffman-id.  Continues BtCover.v.

    WHAT I POSTED AS THE RESIDUAL: "[pqdownheap] is a PERMUTATION of [hp] on
    [1 .. heap_len]".  That is TRUE and it is what the algorithm does, but it is
    NOT what (B-lower) consumes, and pricing it as the obligation overcharged the
    job.  (B-lower) needs every nonzero-frequency symbol to STILL BE SOMEWHERE in
    the window; it never needs multiplicities, and it never needs that nothing was
    duplicated.  So the obligation is MEMBERSHIP PRESERVATION:

        InHeap hp 1 hlen s  ->  InHeap (pqdownheap t dep hp hlen k) 1 hlen s

    and that avoids multiset machinery entirely.  Stating the strong version cost
    nothing here, but had I handed it off as "prove pqdownheap permutes", whoever
    took it would have built a multiset development for a corollary that needs
    none.  **Name the obligation the CONSUMER has, not the property the code has.**

    AND A SECOND SAVING THAT FALLS OUT OF THE SAME READING: membership
    preservation is INDEPENDENT OF [smaller].  The comparison decides WHERE
    elements move, never WHETHER they survive, so both branches of every
    [smaller] test are discharged the same way and the proof needs nothing about
    frequencies, depths, [t_freq], [dep] or the heap ORDER.  That is why this file
    has no arithmetic about frequencies in it at all.  A "heap invariant" that
    turns out not to mention the heap order is worth noticing.

    THE INVARIANT, which is the only subtle part.  [pq_down] carries a value [v]
    read once at entry ([trees.c:508]) and sifts a HOLE downward: each trip does
    [heap[k] = heap[j']] and then [k = j'], and the final [heap[k] = v] closes the
    hole.  So mid-flight the array is NOT a permutation of the original — one
    element is missing from it and held in [v].  Membership must therefore be
    stated up to [v]:

        (forall s, s was in hp  ->  s is in hp now  \/  s = v)

    but that alone does not survive a trip, because the trip OVERWRITES [hp k]
    and the value there is not [v] after the first trip.  What saves it is that
    from the first trip onward the value at the hole is DUPLICATED elsewhere
    (trip 1 copied [hp j'] into [hp k], so it sits at both [k] and [j']).  Hence
    [HoleDup] below, a disjunction: the hole holds [v], or the hole's value also
    lives at another index.  Third time in this lane that the missing piece of an
    unprovable-looking statement was a clause naming what is PRESERVED rather
    than what is achieved. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import BtCover.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** The hole at [k] either holds the held value [v], or its content is duplicated
    at some other live index.  This is what lets a trip overwrite [hp k]. *)
Definition HoleDup (hp : zarr) (lo hi k v : Z) : Prop :=
  hp k = v \/ exists i, lo <= i <= hi /\ i <> k /\ hp i = hp k.

(** Writing ANY value into the hole preserves "still present, up to [v]".  This is
    the one step used by both the recursive trip and the three exit branches, so
    it is factored out above the induction rather than repeated four times. *)
Lemma disj_zset : forall hp hlen k v w s,
  1 <= k <= hlen ->
  HoleDup hp 1 hlen k v ->
  (InHeap hp 1 hlen s \/ s = v) ->
  (InHeap (zset hp k w) 1 hlen s \/ s = v).
Proof.
  intros hp hlen k v w s Hk Hhd [[j0 [Hj0 Heq]]|Hv]; [|right; exact Hv].
  destruct (Z.eq_dec j0 k) as [->|Hne].
  - (* the element we were tracking IS the one being overwritten *)
    destruct Hhd as [Hkv|[i [Hi [Hik Hieq]]]].
    + right. rewrite <- Heq. exact Hkv.
    + left. exists i. split; [exact Hi|].
      rewrite zset_other by exact Hik. rewrite Hieq. exact Heq.
  - left. exists j0. split; [exact Hj0|].
    rewrite zset_other by exact Hne. exact Heq.
Qed.

(** Closing the hole with [v] makes membership unconditional: the [s = v] case now
    has a witness, namely [k] itself. *)
Lemma zset_back_preserves : forall hp hlen k v s,
  1 <= k <= hlen ->
  HoleDup hp 1 hlen k v ->
  (InHeap hp 1 hlen s \/ s = v) ->
  InHeap (zset hp k v) 1 hlen s.
Proof.
  intros hp hlen k v s Hk Hhd Hdisj.
  destruct (disj_zset hp hlen k v v s Hk Hhd Hdisj) as [Hin|Hv]; [exact Hin|].
  exists k. split; [exact Hk|]. rewrite zset_same. symmetry. exact Hv.
Qed.

(** ** The sift-down preserves membership

    Note what is NOT used: nothing about [smaller], [t_freq] or [dep].  Both
    branches of both comparisons are discharged identically. *)
Lemma pq_down_preserves : forall fuel t dep hp hlen v k s,
  1 <= k <= hlen ->
  HoleDup hp 1 hlen k v ->
  (InHeap hp 1 hlen s \/ s = v) ->
  InHeap (pq_down fuel t dep hp hlen v k) 1 hlen s.
Proof.
  induction fuel as [|f IH]; intros t dep hp hlen v k s Hk Hhd Hdisj.
  - cbn [pq_down]. apply zset_back_preserves; assumption.
  - cbn [pq_down].
    destruct (Z.leb (2 * k) hlen) eqn:Ej;
      [apply Z.leb_le in Ej | apply zset_back_preserves; assumption].
    (* name the child index once; its two forms differ only in the bound proof *)
    remember (if (Z.ltb (2 * k) hlen)
                 && smaller t dep (hp (2 * k + 1)) (hp (2 * k))
              then 2 * k + 1 else 2 * k) as j' eqn:Ejp.
    assert (Hj' : 1 <= j' <= hlen /\ j' <> k).
    { subst j'.
      destruct ((Z.ltb (2 * k) hlen)
                  && smaller t dep (hp (2 * k + 1)) (hp (2 * k))) eqn:Eb.
      - apply andb_prop in Eb as [Hlt _]. apply Z.ltb_lt in Hlt. lia.
      - lia. }
    destruct Hj' as [Hj'r Hj'k].
    destruct (smaller t dep v (hp j')) eqn:Es.
    + (* the C's [break], then [heap[k] = v] *)
      apply zset_back_preserves; assumption.
    + (* [heap[k] = heap[j']; k = j'] — the hole moves down *)
      apply IH.
      * exact Hj'r.
      * (* the NEW hole's value is duplicated at the OLD hole: that is exactly
           what this trip just did, and it is why the invariant survives *)
        right. exists k. split; [exact Hk|]. split; [intro Hx; apply Hj'k; auto|].
        rewrite zset_same. rewrite zset_other by exact Hj'k. reflexivity.
      * apply disj_zset with (v := v); assumption.
Qed.

(** ** [pqdownheap] preserves membership

    [pqdownheap] is [pq_down] started with [v = hp k], so the hole trivially holds
    [v] at entry and the [HoleDup] side condition is [reflexivity]. *)
Theorem pqdownheap_preserves : forall t dep hp hlen k s,
  1 <= k <= hlen ->
  InHeap hp 1 hlen s ->
  InHeap (pqdownheap t dep hp hlen k) 1 hlen s.
Proof.
  intros t dep hp hlen k s Hk Hin. unfold pqdownheap.
  apply pq_down_preserves with (v := hp k).
  - exact Hk.
  - left. reflexivity.
  - left. exact Hin.
Qed.

(** ** [bt_heapify] preserves membership

    The heapify loop is [pqdownheap] at [n = hlen/2 .. 1], so this is
    [pqdownheap_preserves] threaded through the descending walk. *)
Lemma bt_heapify_preserves : forall fuel t dep hp hlen n s,
  n <= hlen ->
  InHeap hp 1 hlen s ->
  InHeap (bt_heapify fuel t dep hp hlen n) 1 hlen s.
Proof.
  induction fuel as [|f IH]; intros t dep hp hlen n s Hn Hin.
  - cbn [bt_heapify]. exact Hin.
  - cbn [bt_heapify].
    destruct (Z.ltb n 1) eqn:E1; [exact Hin|].
    apply Z.ltb_ge in E1.
    apply IH; [lia|].
    apply pqdownheap_preserves; [lia | exact Hin].
Qed.

(** ** The composition BtCover was missing

    [bt_init] puts every nonzero-frequency symbol in the live heap (BtCover), and
    heapifying keeps it there (here).  So the whole prefix of [build_tree] up to
    the combine loop preserves coverage — which is (B-lower) minus [bt_force2]
    (append-only, the [bt_init] argument again) and the combine loop itself. *)
Corollary bt_init_then_heapify_covers : forall elems t hp dep maxc fuel n,
  0 <= elems ->
  match bt_init (Z.to_nat elems) 0 elems t hp dep 0 maxc with
  | (_, hp1, dep1, hlen1, _) =>
      n <= hlen1 ->
      forall s, 0 <= s < elems -> t_freq t s <> 0 ->
        InHeap (bt_heapify fuel t dep1 hp1 hlen1 n) 1 hlen1 s
  end.
Proof.
  intros elems t hp dep maxc fuel n He.
  pose proof (bt_init_covers_all elems t hp dep maxc He) as H.
  destruct (bt_init (Z.to_nat elems) 0 elems t hp dep 0 maxc)
    as [[[[t1 hp1] dep1] hlen1] maxc1].
  intros Hn s Hs Hfr.
  apply bt_heapify_preserves; [exact Hn|].
  apply H; [exact Hs | exact Hfr].
Qed.

(** WHAT IS LEFT OF (B-lower) AFTER THIS FILE, stated precisely so the next hand
    is exact:
      - [bt_force2]: append-only, at [heap[++heap_len]].  Same shape as
        [bt_init_covers]; the only new wrinkle is that it also mutates [t_freq]
        (it forces a symbol's frequency to 1), so the statement must quantify over
        the tree rather than fix it.  Cheap.
      - [bt_step] / the combine loop: needs the DISJOINT-UNION invariant from
        §HUFFID-BTLOWER-STATEMENT, i.e. membership in
        [heap[1 .. heap_len] UNION heap[heap_max .. HEAP_SIZE-1]].  Both
        [pqdownheap] calls in [bt_step] are covered by
        [pqdownheap_preserves] above; what remains is the bookkeeping for the two
        parked writes and the [heap_len]/[heap_max] motion.
    Neither needs a permutation argument, and neither needs the heap ORDER. *)

Print Assumptions disj_zset.
Print Assumptions pq_down_preserves.
Print Assumptions pqdownheap_preserves.
Print Assumptions bt_heapify_preserves.
Print Assumptions bt_init_then_heapify_covers.
