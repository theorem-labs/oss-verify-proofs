(** * BtRoot — the last gap: the element left in the live heap is the tree ROOT,
      not a symbol.  With this, (B-lower)'s heap half is closed.

    OWNER: huffman-id.  Follows BtStep.v.

    WHY THIS WAS STILL NEEDED, and I only saw it by chasing the composition
    through to [gen_bitlen] rather than stopping at "nothing is lost".

    BtStep.v proves the combine loop loses nothing: every symbol in the heap at
    entry is, at exit, in [heap[1 .. heap_len]] UNION [heap[heap_max .. HEAP_SIZE-1]].
    But [gen_bitlen] does NOT walk the union.  It does
    ([Trees.v:557]) [tree[heap[heap_max]].Len = 0] and then walks
    [heap[heap_max+1 .. HEAP_SIZE-1]].  So the element the loop leaves behind in
    the live heap — which [build_tree]'s tail moves to [heap[--heap_max]] — is
    given LENGTH ZERO.

    **If that element were a symbol, (B-lower) would be FALSE**: a
    positive-frequency symbol would come out with length 0.  It is not false,
    because the leftover is the Huffman tree's ROOT, an internal node created by
    the loop, and the root legitimately has no code.  But that is a fact about
    WHICH population the leftover belongs to, and "nothing is lost" says nothing
    about it.  Two populations share one array and only one of them may end up at
    that index.

    This is the obligation I named at the end of BtForce2.v as "separating the two
    populations".  It turns out to be the difference between (B-lower) being true
    and being false, not a tidiness matter — which is a good argument for chasing
    a composition to its actual consumer instead of stopping when the lemma looks
    like the shape you wanted. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import BtCover PqDown BtForce2 BtStep.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** A one-element heap cannot sift: [2k > hlen] on the first test, so
    [pq_down] falls straight through to [heap[k] = v] with [v = heap[k]].

    STATED OVER SYMBOLIC FUEL ON PURPOSE.  [pqdownheap]'s fuel is the LITERAL 12,
    and [cbn [pq_down]] against a literal keeps unfolding: twelve levels, two
    branches each, and the term blows up (1.5 GB and climbing before I killed it).
    [destruct fuel] first makes the fuel [S f] with [f] a variable, so exactly one
    layer unfolds.  Reduce against a variable, never against a numeral. *)
Lemma pq_down_no_room : forall fuel t dep hp hlen v k,
  hlen < 2 * k -> pq_down fuel t dep hp hlen v k = zset hp k v.
Proof.
  destruct fuel as [|f]; intros t dep hp hlen v k Hk; cbn [pq_down].
  - reflexivity.
  - destruct (Z.leb (2 * k) hlen) eqn:E;
      [apply Z.leb_le in E; lia | reflexivity].
Qed.

Lemma pqdownheap_no_room : forall t dep hp hlen k,
  hlen < 2 * k -> pqdownheap t dep hp hlen k k = hp k.
Proof.
  intros t dep hp hlen k Hk. unfold pqdownheap.
  rewrite pq_down_no_room by lia. apply zset_same.
Qed.

(** ** The loop's exit state

    [bt_loop] can only return [Some] via [BtDone], and [BtDone] fires exactly when
    [heap_len - 1 < 2].  Since every trip is entered with [heap_len >= 2], the
    exit [heap_len] is exactly 1, and the single live slot holds the node this
    trip created. *)
Lemma bt_loop_root : forall fuel st elems,
  2 <= b_hlen st -> elems <= b_node st ->
  match bt_loop fuel st with
  | Some stf => b_hlen stf = 1 /\ elems <= b_heap stf 1
  | None => True
  end.
Proof.
  induction fuel as [|f IH]; intros st elems Hlen Hnode.
  - cbn [bt_loop]. exact I.
  - cbn [bt_loop].
    destruct (bt_step st) as [st'|st'] eqn:Est.
    + (* another trip: [heap_len] still >= 2, and [node] only increases *)
      apply IH.
      * unfold bt_step in Est. cbv zeta in Est.
        destruct (Z.leb 2 (b_hlen st - 1)) eqn:E2; [|discriminate].
        apply Z.leb_le in E2. inversion Est. subst. cbn [b_hlen]. lia.
      * unfold bt_step in Est. cbv zeta in Est.
        destruct (Z.leb 2 (b_hlen st - 1)); [|discriminate].
        inversion Est. subst. cbn [b_node]. lia.
    + (* the last trip *)
      unfold bt_step in Est. cbv zeta in Est.
      destruct (Z.leb 2 (b_hlen st - 1)) eqn:E2; [discriminate|].
      apply Z.leb_gt in E2.
      inversion Est. subst. cbn [b_hlen b_heap b_node].
      split; [lia|].
      (* the live window is a single slot, so the second sift cannot move
         anything: [pqdownheap] falls through and leaves [node] at index 1 *)
      rewrite pqdownheap_no_room by lia.
      rewrite zset_same. exact Hnode.
Qed.

(** ** (B-lower)'s heap half, closed

    A symbol is [< elems]; the loop's internal nodes are [>= elems] because
    [b_node] starts at [elems] ([Trees.v]'s [build_tree]) and only increments.  So
    the leftover cannot be a symbol, and BtStep's union collapses to the parked
    region — which is exactly what [gb_pass1] walks. *)
Theorem combine_loop_parks_every_symbol :
  forall fuel hlen hp dep t node s elems,
  2 <= hlen -> hlen <= L_CODES ->
  elems <= node -> 0 <= s < elems ->
  InHeap hp 1 hlen s ->
  match bt_loop fuel {| b_tree := t; b_heap := hp; b_dep := dep;
                        b_hlen := hlen; b_hmax := HEAP_SIZE;
                        b_node := node |} with
  | Some stf => InHeap (b_heap stf) (b_hmax stf) (HEAP_SIZE - 1) s
  | None => True
  end.
Proof.
  intros fuel hlen hp dep t node s elems H2 Hl Hn Hs Hin.
  pose proof (combine_loop_covers fuel hlen hp dep t node s H2 Hl
                (or_introl Hin)) as Hcov.
  pose proof (bt_loop_root fuel
                {| b_tree := t; b_heap := hp; b_dep := dep;
                   b_hlen := hlen; b_hmax := HEAP_SIZE; b_node := node |}
                elems) as Hroot.
  cbn [b_hlen b_node] in Hroot.
  specialize (Hroot H2 Hn).
  destruct (bt_loop fuel {| b_tree := t; b_heap := hp; b_dep := dep;
                            b_hlen := hlen; b_hmax := HEAP_SIZE;
                            b_node := node |}) as [stf|]; [|exact I].
  destruct Hroot as [Hlen1 Hge].
  unfold Covered in Hcov.
  destruct Hcov as [[j [Hj Heq]]|Hpark]; [|exact Hpark].
  (* the only live slot is index 1, and it holds a node, not a symbol *)
  assert (j = 1) by lia. subst j.
  exfalso. rewrite Heq in Hge. lia.
Qed.

(** WHAT REMAINS BETWEEN HERE AND (B-lower) IN FULL — one arithmetic step and one
    plumbing step, both outside the heap:

      (i)  [gb_pass1] gives every index it visits a length [>= 1]
           ([min(maxlen, dad_len + 1)] with [maxlen >= 1]).  This is the "free
           arithmetic" I identified in GenBitlen.v's header and never wrote down,
           because at the time the visiting was the open part.
      (ii) [build_tree]'s tail moves [heap[SMALLEST]] to [heap[--heap_max]] and
           hands [heap_max] to [gen_bitlen], so the parked window proved here
           lines up with [heap[heap_max+1 .. HEAP_SIZE-1]] shifted by exactly the
           root slot.  Index bookkeeping, no new invariant.

    Neither needs the heap, the heap order, or a permutation — which has been true
    of every step of (B-lower) and was not at all obvious when it was described as
    "a heap invariant over five functions". *)

Print Assumptions pq_down_no_room.
Print Assumptions pqdownheap_no_room.
Print Assumptions bt_loop_root.
Print Assumptions combine_loop_parks_every_symbol.
