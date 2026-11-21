(** * BtForce2 — the third of (B-lower)'s four heap-touching functions.

    OWNER: huffman-id.  Continues BtCover.v and PqDown.v.

    [bt_force2] is [trees.c:653-659], the "force at least two codes of non-zero
    frequency" fixup.  It is APPEND-ONLY on the heap — [heap[++heap_len] = node] —
    so membership preservation is the [bt_init] argument again and costs nothing
    new.  With this file, three of the four functions are done and the ONLY
    remaining one is the combine loop.

    ONE HONEST WRINKLE, and I am stating it as a hypothesis rather than proving it
    here because it belongs to a different invariant.  [bt_force2] does not only
    touch the heap: it also does [tree[node].Freq = 1].  So "the nonzero-frequency
    symbols" is a predicate that MOVES under this function, and a coverage
    statement phrased against the incoming tree is only preserved for symbols
    OTHER than [node].  That is true of the real code — [node] is chosen precisely
    because its frequency is zero, so no already-counted symbol is disturbed — but
    proving THAT is a statement about [max_code]'s relationship to the heap, not
    about the heap itself.  I take [s <> node] as a hypothesis and name the
    obligation instead of quietly assuming the two never collide.  Naming it is
    the point: this is exactly the kind of side condition that disappears into a
    "clearly" and then turns out to be the whole difficulty. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import BtCover PqDown.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** Appending past the live window cannot lose anything already inside it. *)
Lemma InHeap_append : forall hp lo hi i v s,
  hi < i -> InHeap hp lo hi s -> InHeap (zset hp i v) lo (hi + 1) s.
Proof.
  intros hp lo hi i v s Hlt [j [Hj Heq]].
  exists j. split; [lia|]. rewrite zset_other by lia. exact Heq.
Qed.

(** ** [bt_force2] preserves membership

    Nothing about [stree], [opt_len] or [static_len] is used: those are the
    counters whose [ulg] wraparound the header of [Trees.v] warns about, and they
    are irrelevant to whether a symbol stays in the heap.  Stated so that the
    wraparound cannot be mistaken for a hazard to coverage. *)
Lemma bt_force2_preserves : forall fuel stree t hp dep hlen maxc ol sl s,
  0 <= hlen ->
  InHeap hp 1 hlen s ->
  match bt_force2 fuel stree t hp dep hlen maxc ol sl with
  | (_, hp', _, hlen', _, _, _) => InHeap hp' 1 hlen' s
  end.
Proof.
  induction fuel as [|f IH];
    intros stree t hp dep hlen maxc ol sl s Hh Hin.
  - cbn [bt_force2]. exact Hin.
  - cbn [bt_force2].
    destruct (Z.leb 2 hlen) eqn:E2; [exact Hin|].
    apply Z.leb_gt in E2.
    apply IH; [lia|].
    (* the append lands at [hlen + 1], strictly past the live window *)
    apply InHeap_append; [lia | exact Hin].
Qed.

(** ** The prefix of [build_tree] up to the combine loop

    [bt_init] covers ([BtCover]), [bt_force2] keeps it (here), [bt_heapify] keeps
    it ([PqDown]).  Composed, every nonzero-frequency symbol is in the live heap
    when the combine loop starts.  That is (B-lower) minus the combine loop. *)
Corollary build_tree_prefix_covers :
  forall elems t hp dep maxc stree ol sl f2 fh n,
  0 <= elems ->
  match bt_init (Z.to_nat elems) 0 elems t hp dep 0 maxc with
  | (t1, hp1, dep1, hlen1, maxc1) =>
      0 <= hlen1 ->
      match bt_force2 f2 stree t1 hp1 dep1 hlen1 maxc1 ol sl with
      | (_, hp2, dep2, hlen2, _, _, _) =>
          n <= hlen2 ->
          forall s, 0 <= s < elems -> t_freq t s <> 0 ->
            InHeap (bt_heapify fh t1 dep2 hp2 hlen2 n) 1 hlen2 s
      end
  end.
Proof.
  intros elems t hp dep maxc stree ol sl f2 fh n He.
  pose proof (bt_init_covers_all elems t hp dep maxc He) as Hcov.
  destruct (bt_init (Z.to_nat elems) 0 elems t hp dep 0 maxc)
    as [[[[t1 hp1] dep1] hlen1] maxc1].
  intros Hh1.
  pose proof (fun s Hs Hfr =>
    bt_force2_preserves f2 stree t1 hp1 dep1 hlen1 maxc1 ol sl s Hh1
      (Hcov s Hs Hfr)) as Hf2.
  destruct (bt_force2 f2 stree t1 hp1 dep1 hlen1 maxc1 ol sl)
    as [[[[[[t2 hp2] dep2] hlen2] maxc2] ol2] sl2].
  intros Hn s Hs Hfr.
  apply bt_heapify_preserves; [exact Hn|].
  apply Hf2; [exact Hs | exact Hfr].
Qed.

(** WHAT IS LEFT OF (B-lower), and it is now ONE loop.

    The combine loop ([bt_step] / [bt_iter], trees.c:671-693) needs the
    DISJOINT-UNION invariant from §HUFFID-BTLOWER-STATEMENT:

        {s : freq s <> 0} SUBSET heap[1 .. heap_len] UNION heap[heap_max .. HEAP_SIZE-1]

    Both [pqdownheap] calls inside [bt_step] are already discharged by
    [PqDown.pqdownheap_preserves].  What remains is bookkeeping for the two parked
    writes ([heap[--heap_max] = n], then [= m]) and the [heap_len]/[heap_max]
    motion, plus the [s <> node] side condition discussed in this file's header —
    the internal nodes the loop creates are NOT symbols, and separating the two
    populations is the last thing (B-lower) actually needs.

    No permutation argument is required anywhere, and no part of it needs the heap
    ORDER — which was the surprise in PqDown.v and is worth restating, because
    "prove the heap correct" was never the obligation. *)

Print Assumptions InHeap_append.
Print Assumptions bt_force2_preserves.
Print Assumptions build_tree_prefix_covers.
