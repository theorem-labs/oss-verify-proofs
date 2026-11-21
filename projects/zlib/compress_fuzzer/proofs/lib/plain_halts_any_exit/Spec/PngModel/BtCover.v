(** * BtCover — (B-lower)'s FIRST half, and the exact statement of the second.

    OWNER: huffman-id.  Continues [GenBitlen.v], which proved (B-upper) and named
    (B-lower) as "a heap invariant over five functions".  Having named it I read
    it, and it splits AGAIN — unevenly, the same way (B) did.

    WHAT (B-lower) NEEDS, stated against the code rather than in the abstract.
    [gen_bitlen] assigns a length to every symbol [gb_pass1] VISITS, and it visits
    [heap[heap_max+1 .. HEAP_SIZE-1]].  So the obligation is that every
    nonzero-frequency symbol is SOMEWHERE in that window when [build_tree] is
    done.  Tracing the four functions that touch the heap:

      [bt_init]     appends each nonzero-frequency symbol at [heap[++heap_len]]
                    and touches nothing already there.  NO PERMUTATION.
      [bt_force2]   only appends, at [heap[++heap_len]].  NO PERMUTATION.
      [bt_heapify]  [pqdownheap] repeatedly — PERMUTES [1 .. heap_len].
      [bt_step]     [pqremove] (which permutes), then moves the two extracted
                    nodes DOWN to [heap[--heap_max]], then [pqdownheap] again.

    SO THE REAL SHAPE IS A DISJOINT-UNION INVARIANT.  At every point in
    [build_tree], every nonzero-frequency symbol is EITHER still in the live heap
    [1 .. heap_len] OR already parked in [heap_max .. HEAP_SIZE-1]:

        {s : freq s <> 0}  SUBSET-OF  heap[1 .. heap_len] UNION
                                      heap[heap_max .. HEAP_SIZE-1]

    and [bt_step] moves elements from the left set to the right one, two per trip.
    When the loop ends [heap_len = 1] and the final [heap[--heap_max] :=
    heap[SMALLEST]] moves the last one across, leaving the right set alone —
    which is [gb_pass1]'s walk plus the root, and the root is exactly the symbol
    [gen_bitlen] hands length 0 before the walk starts.

    THE PRICE IS NOT EVENLY SPLIT, and that is the finding:
      - the two APPEND-ONLY functions need no permutation reasoning at all, and
        [bt_init]'s half is PROVED HERE ([bt_init_covers]);
      - everything else reduces to ONE reusable sub-lemma, **[pqdownheap]
        permutes [1 .. heap_len]** — every remaining step is that fact plus
        bookkeeping.  It is not proved here.

    That is a much better-shaped residual than "a heap invariant over five
    functions": one sub-lemma about one function, with three consumers. Third time
    in this lane that reading the code turned a vague obligation into a named
    one — and note that I only got here by naming the vague version FIRST and
    then looking, rather than by trying to price it from the outside. *)

(** CORRECTION APPENDED 2026-08-18 (huffman-id), not an edit of the text above.

    THE HEADER SAYS the residual reduces to "[pqdownheap] permutes [1 .. heap_len]
    ... It is not proved here."  THAT RESIDUAL IS CLOSED, and by a different route
    than the one predicted: [PqDown.pqdownheap_preserves] (with
    [bt_heapify_preserves] and [bt_init_then_heapify_covers]) establishes
    PRESERVATION of heap membership rather than a permutation property, and
    [BtForce2.bt_force2_preserves] covers the append-only stage.  Membership
    preservation is what the three consumers actually needed; the permutation would
    have been a stronger statement than any of them uses.

    Worth keeping as a shape note: naming the vague obligation first and then
    looking is what produced the good residual, and the residual still came out
    stated in the wrong vocabulary.  A named residual is a hypothesis about the
    route, not a specification of it. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** "Symbol [n] sits somewhere in the heap window [lo .. hi]." *)
Definition InHeap (hp : zarr) (lo hi n : Z) : Prop :=
  exists j, lo <= j <= hi /\ hp j = n.

Lemma InHeap_widen : forall hp lo hi hi' n,
  hi <= hi' -> InHeap hp lo hi n -> InHeap hp lo hi' n.
Proof. intros hp lo hi hi' n Hle [j [Hj Heq]]. exists j. split; [lia | exact Heq]. Qed.

(** [t_setlen] writes [tr_dl]; [t_freq] reads [tr_fc].  So [bt_init]'s
    zero-frequency arm cannot change the very predicate the lemma quantifies
    over — which is why the induction below can carry [t_freq t] unchanged. *)
Lemma t_freq_setlen : forall t i v s, t_freq (t_setlen t i v) s = t_freq t s.
Proof. intros. reflexivity. Qed.

(** ** [bt_init] covers every nonzero-frequency symbol

    Three conjuncts, and the middle one is load-bearing: without "the existing
    prefix is untouched" the coverage of the symbol appended on THIS trip cannot
    be carried through the recursive call, because the witness index is only
    valid if nothing later overwrites it.  Stating coverage alone would give an
    unprovable lemma that looks complete — the same trap as the accumulators in
    [HuffAuditOp.gc_next_congr] and the coverage split before it.

    The [0 <= hlen] premise is load-bearing for the same reason and I omitted it
    on the first pass: the symbol appended on the current trip has witness index
    [hlen + 1], and that is only inside the window [1 .. hlen'] when [hlen] is
    nonnegative.  [lia] reported it as "Cannot find witness", which reads like an
    arithmetic gap and is actually a MISSING HYPOTHESIS — the same misleading
    surface as the [vm_compute] case in my notes. *)
Lemma bt_init_covers : forall fuel n elems t hp dep hlen maxc,
  elems - n <= Z.of_nat fuel ->
  0 <= hlen ->
  match bt_init fuel n elems t hp dep hlen maxc with
  | (t', hp', dep', hlen', maxc') =>
      (forall s, n <= s < elems -> t_freq t s <> 0 -> InHeap hp' 1 hlen' s)
      /\ (forall j, 1 <= j <= hlen -> hp' j = hp j)
      /\ hlen <= hlen'
  end.
Proof.
  induction fuel as [|f IH]; intros n elems t hp dep hlen maxc Hf Hh.
  - (* NOT [repeat split]: it closes the middle conjunct itself here, because
       [hp' = hp] makes the body a reflexivity and [constructor] intros first.
       An explicit split keeps the goal count equal to the conjunct count. *)
    cbn [bt_init]. split; [| split].
    + intros s Hs Hfr. cbn in Hf. lia.
    + intros j Hj. reflexivity.
    + lia.
  - cbn [bt_init].
    destruct (Z.leb elems n) eqn:Eend.
    + apply Z.leb_le in Eend. split; [| split].
      * intros s Hs Hfr. lia.
      * intros j Hj. reflexivity.
      * lia.
    + apply Z.leb_gt in Eend.
      destruct (Z.eqb (t_freq t n) 0) eqn:E0.
      * (* zero frequency: not heaped, and [n] itself cannot be a witness *)
        apply Z.eqb_eq in E0.
        assert (Hf' : elems - (n + 1) <= Z.of_nat f) by lia.
        specialize (IH (n + 1) elems (t_setlen t n 0) hp dep hlen maxc Hf' Hh).
        destruct (bt_init f (n + 1) elems (t_setlen t n 0) hp dep hlen maxc)
          as [[[[t' hp'] dep'] hlen'] maxc'] eqn:Erec.
        destruct IH as [Hcov [Hpre Hmono]].
        split; [| split]; [| exact Hpre | exact Hmono].
        intros s Hs Hfr. destruct (Z.eq_dec s n) as [->|Hne]; [lia|].
        apply Hcov; [lia|]. rewrite t_freq_setlen. exact Hfr.
      * (* nonzero frequency: appended at [hlen+1], and the prefix guarantee of
           the recursive call is what keeps that witness valid *)
        apply Z.eqb_neq in E0.
        assert (Hf' : elems - (n + 1) <= Z.of_nat f) by lia.
        assert (Hh' : 0 <= hlen + 1) by lia.
        specialize (IH (n + 1) elems t (zset hp (hlen + 1) n) (zset dep n 0)
                       (hlen + 1) n Hf' Hh').
        destruct (bt_init f (n + 1) elems t (zset hp (hlen + 1) n) (zset dep n 0)
                          (hlen + 1) n)
          as [[[[t' hp'] dep'] hlen'] maxc'] eqn:Erec.
        destruct IH as [Hcov [Hpre Hmono]].
        split; [| split].
        -- intros s Hs Hfr. destruct (Z.eq_dec s n) as [->|Hne].
           ++ (* the symbol appended on THIS trip.  [1 <= hlen + 1] is exactly
                 what the [0 <= hlen] premise is for — without it this witness
                 index is not in the window and the lemma is unprovable. *)
              exists (hlen + 1). split; [lia|].
              rewrite Hpre by lia. apply zset_same.
           ++ apply Hcov; [lia | exact Hfr].
        -- intros j Hj. rewrite Hpre by lia. apply zset_other. lia.
        -- lia.
Qed.

(** The form a consumer wants: after [bt_init] over [0 .. elems-1], every
    nonzero-frequency symbol is in the live heap. *)
Corollary bt_init_covers_all : forall elems t hp dep maxc,
  0 <= elems ->
  match bt_init (Z.to_nat elems) 0 elems t hp dep 0 maxc with
  | (_, hp', _, hlen', _) =>
      forall s, 0 <= s < elems -> t_freq t s <> 0 -> InHeap hp' 1 hlen' s
  end.
Proof.
  intros elems t hp dep maxc He.
  assert (Hf : elems - 0 <= Z.of_nat (Z.to_nat elems))
    by (rewrite Z2Nat.id by lia; lia).
  assert (Hh : 0 <= 0) by lia.
  pose proof (bt_init_covers (Z.to_nat elems) 0 elems t hp dep 0 maxc Hf Hh) as H.
  destruct (bt_init (Z.to_nat elems) 0 elems t hp dep 0 maxc)
    as [[[[t' hp'] dep'] hlen'] maxc'].
  destruct H as [Hcov _]. exact Hcov.
Qed.

(** ** What is left, stated so it can be handed off or costed

    [bt_force2] is the same append-only shape as [bt_init] and would go the same
    way.  The rest — [bt_heapify], [bt_step] — all reduce to ONE fact:

      **[pqdownheap t dep hp hlen k] is a PERMUTATION of [hp] on [1 .. hlen],
        and is the identity outside it.**

    With that, [bt_heapify] preserves the live-heap set by transitivity, and
    [bt_step] moves exactly [heap[SMALLEST]] and the post-[pqdownheap]
    [heap[SMALLEST]] into the parked window while permuting the rest.  Without
    it, none of the three steps can be stated, let alone proved.  I am recording
    it as the single named dependency rather than starting it, because it is a
    genuine data-structure proof and the honest estimate is that it is larger
    than everything in [GenBitlen.v] and this file combined. *)

Print Assumptions InHeap_widen.
Print Assumptions bt_init_covers.
Print Assumptions bt_init_covers_all.
