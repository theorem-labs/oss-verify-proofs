(** * GenBitlen — (B)'s UPPER half: every length [gen_bitlen] writes is at most
      [max_length], so the code-length tree's widths fit in 7 bits.

    OWNER: huffman-id.  (B) is HuffCover.v's sole residual and TL's new
    assignment (§TL-ACK-SCAN).

    (B) IN FULL, as HuffCover states it: [build_bl_tree] gives every
    POSITIVE-FREQUENCY symbol a length in [1, 7].  Reading [gen_bitlen] against
    the code splits that cleanly, and the two halves have very different prices:

      (B-upper)  every length written is <= max_length.
                 TRACTABLE, and proved here.  Both passes CLAMP:
                 [gb_pass1] writes [if maxlen < dad+1 then maxlen else dad+1]
                 ([Trees.v:402], zlib's own overflow test), and [gb_pass2] writes
                 [bits] which starts at [maxlen] and only decreases.  So the
                 bound is structural, not a consequence of the heap being right.

      (B-lower)  positive frequency => length >= 1.
                 HARD, and NOT proved here.  [gb_pass1] does give every symbol it
                 visits [bits >= 1] (the dad's length is >= 0 and [maxlen >= 1]),
                 so the arithmetic is free.  What is NOT free is that every
                 positive-frequency symbol IS visited: [gb_pass1] walks only
                 [heap[heap_max+1 .. HEAP_SIZE-1]], so the obligation is
                 **"[bt_init] puts every nonzero-frequency symbol into the heap
                 and [bt_loop] leaves it in that range"** — a heap invariant over
                 [bt_init] / [bt_force2] / [bt_heapify] / [bt_loop] /
                 [pqdownheap].  That is the genuinely expensive part of
                 build_tree and it is a different kind of proof from anything in
                 L-B so far.

    NAMING THE SPLIT IS THE POINT, again: (B) as one statement looked like "prove
    build_tree correct".  Split, one half falls out of two clamps and the other is
    a single named heap invariant.  I am not going to claim the second by starting
    it badly.

    ONE MORE THING THE CLAMP BUYS, worth stating because it is not obvious: the
    upper bound holds WHETHER OR NOT the overflow adjustment runs.  zlib's
    [gb_adjust] exists to make the code KRAFT-VALID after clamping, not to make
    the lengths short — the clamp already did that.  So (B-upper) is independent
    of [gb_adjust]'s correctness, which is the hardest single function in the
    file. *)

(** CORRECTION APPENDED 2026-08-18 (huffman-id), not an edit of the text above,
    which is quoted in §HUFFID-SCANSEND and elsewhere.

    THE HEADER SAYS (B-lower) IS "HARD, and NOT proved here", and names the
    obligation as "[bt_init] puts every nonzero-frequency symbol into the heap and
    [bt_loop] leaves it in that range ... the genuinely expensive part of
    build_tree".  ALL OF THAT IS PROVED, and was proved before this correction was
    written:

      BtCover.bt_init_covers_all              the bt_init half
      PqDown.pqdownheap_preserves             + bt_heapify_preserves
      BtForce2.bt_force2_preserves            the append-only stage
      BtRoot.combine_loop_parks_every_symbol  bt_loop leaves it in range
      GbVisit.gen_bitlen_pos                  every parked symbol gets length >= 1

    and they are COMPOSED, not merely adjacent: [BuildChain.build_chain] concludes
    [1 <= t_len (ts_trees (gen_bitlen k s1) k) s0 <= sd_max_length k] from
    [t_freq (ts_trees s k) s0 <> 0].  That is (B) IN FULL, both halves, for any
    tree kind, and [BtTerm.build_tree_bl_final] is the heap-free instance of it.

    WHY THIS CORRECTION MATTERS MORE THAN THE USUAL STALE COMMENT: I CONSUMED
    [BtTerm.build_tree_bl_final] -- i.e. (B) in full -- in CoverChain.v on the same
    day, while this header was telling any reader that half of it was unproved and
    was the expensive part.  A lane staffed off this paragraph would have rebuilt
    finished work.  Found by sweeping my own headers for open-obligation language
    and checking each claim against the declarations, which is a check worth running
    on any file set whose headers were written before its later files. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** Every length in the tree is within [0, m]. *)
Definition LenBound (t : Tree) (m : Z) : Prop := forall i, 0 <= t_len t i <= m.

Lemma t_len_setlen_same' : forall t i v, t_len (t_setlen t i v) i = u16 v.
Proof. intros t i v. unfold t_len, t_setlen. cbn [tr_dl]. apply zset_same. Qed.

Lemma t_len_setlen_other' : forall t i v j,
  j <> i -> t_len (t_setlen t i v) j = t_len t j.
Proof.
  intros t i v j H. unfold t_len, t_setlen. cbn [tr_dl]. apply zset_other. exact H.
Qed.

(** Writing a value inside the bound keeps the bound.  The [u16] is the identity
    because [m <= 15] — zlib's lengths are [ush] fields and the bound is what makes
    the truncation invisible, the same shape as everywhere else in this lane. *)
Lemma LenBound_setlen : forall t m i v,
  LenBound t m -> 0 <= v <= m -> m <= 15 -> LenBound (t_setlen t i v) m.
Proof.
  intros t m i v Hb Hv Hm j.
  destruct (Z.eq_dec j i) as [->|Hne].
  - rewrite t_len_setlen_same'. unfold u16. rewrite Z.mod_small by lia. lia.
  - rewrite t_len_setlen_other' by lia. apply Hb.
Qed.

(** ** Pass 1 preserves the bound

    [Trees.v:402]: [bits := if maxlen < dad+1 then maxlen else dad+1], which is
    zlib's overflow test doubling as a clamp.  Whichever branch is taken the value
    is at most [maxlen]. *)
Definition gb1_tree (r : Tree * zarr * Z * Z * Z) : Tree :=
  match r with (t, _, _, _, _) => t end.

Lemma gb_pass1_bound : forall fuel k hp maxc maxlen base extra stree h t blc ol sl ov,
  1 <= maxlen <= 15 ->
  LenBound t maxlen ->
  LenBound (gb1_tree (gb_pass1 fuel k hp maxc maxlen base extra stree
                               h t blc ol sl ov)) maxlen.
Proof.
  induction fuel as [|f IH];
    intros k hp maxc maxlen base extra stree h t blc ol sl ov Hm Hb.
  - cbn [gb_pass1 gb1_tree]. exact Hb.
  - cbn [gb_pass1].
    destruct (Z.leb HEAP_SIZE h); [exact Hb|].
    (* the clamped value is in range whichever branch the test takes *)
    assert (Hv : 0 <= (if Z.ltb maxlen (t_len t (t_dad t (hp h)) + 1)
                       then maxlen else t_len t (t_dad t (hp h)) + 1) <= maxlen).
    { destruct (Z.ltb maxlen (t_len t (t_dad t (hp h)) + 1)) eqn:E.
      - lia.
      - apply Z.ltb_ge in E. pose proof (Hb (t_dad t (hp h))) as Hd. lia. }
    assert (Hb' : LenBound (t_setlen t (hp h)
                    (if Z.ltb maxlen (t_len t (t_dad t (hp h)) + 1)
                     then maxlen else t_len t (t_dad t (hp h)) + 1)) maxlen)
      by (apply LenBound_setlen; [exact Hb | exact Hv | lia]).
    destruct (Z.ltb maxc (hp h)); apply IH; assumption.
Qed.

(** ** Pass 2 preserves the bound

    [gb_pass2] writes [bits], which starts at [maxlen] and only ever decreases,
    so the invariant is [1 <= bits <= maxlen]. *)
Lemma gb_pass2_bound : forall fuel hp maxc t blc bits n h ol maxlen,
  1 <= maxlen <= 15 -> 1 <= bits <= maxlen ->
  LenBound t maxlen ->
  LenBound (fst (gb_pass2 fuel hp maxc t blc bits n h ol)) maxlen.
Proof.
  induction fuel as [|f IH];
    intros hp maxc t blc bits n h ol maxlen Hm Hbits Hb.
  - cbn [gb_pass2 fst]. exact Hb.
  - cbn [gb_pass2].
    destruct (Z.eqb n 0).
    + destruct (Z.leb bits 1) eqn:E1; [exact Hb|].
      apply Z.leb_gt in E1. apply IH; try assumption; lia.
    + destruct (Z.ltb maxc (hp (h - 1))); [apply IH; assumption|].
      destruct (Z.eqb (t_len t (hp (h - 1))) bits); [apply IH; assumption|].
      apply IH; try assumption.
      apply LenBound_setlen; [exact Hb | lia | lia].
Qed.

(** ** (B-upper), at [gen_bitlen]

    Both branches of the overflow test are covered, so the bound does NOT depend
    on [gb_adjust] being right — only on the two clamps. *)
Theorem gen_bitlen_len_bound : forall k s,
  1 <= sd_max_length k <= 15 ->
  LenBound (ts_trees s k) (sd_max_length k) ->
  LenBound (ts_trees (gen_bitlen k s) k) (sd_max_length k).
Proof.
  intros k s Hm Hb.
  unfold gen_bitlen.
  (* the initial [t_setlen ... 0] at Trees.v:557 *)
  assert (Hb1 : LenBound (t_setlen (ts_trees s k) (ts_heap s (ts_heapmax s)) 0)
                         (sd_max_length k))
    by (apply LenBound_setlen; [exact Hb | lia | lia]).
  destruct (gb_pass1 (Z.to_nat HEAP_SIZE + 1) k (ts_heap s) (ts_maxcode s k)
                     (sd_max_length k) (sd_extra_base k) (sd_extra k)
                     (sd_stree k) (ts_heapmax s + 1)
                     (t_setlen (ts_trees s k) (ts_heap s (ts_heapmax s)) 0)
                     (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s))
                     (ts_optlen s) (ts_statlen s) 0)
    as [[[[t2 blc1] ol1] sl1] ov] eqn:E1.
  assert (Ht2 : LenBound t2 (sd_max_length k)).
  { pose proof (gb_pass1_bound (Z.to_nat HEAP_SIZE + 1) k (ts_heap s)
                  (ts_maxcode s k) (sd_max_length k) (sd_extra_base k)
                  (sd_extra k) (sd_stree k) (ts_heapmax s + 1)
                  (t_setlen (ts_trees s k) (ts_heap s (ts_heapmax s)) 0)
                  (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s))
                  (ts_optlen s) (ts_statlen s) 0 Hm Hb1) as H.
    rewrite E1 in H. cbn [gb1_tree] in H. exact H. }
  destruct (Z.eqb ov 0).
  - (* no overflow: the tree is pass 1's *)
    assert (Hk : Z.eqb k k = true) by apply Z.eqb_refl.
    unfold set_statlen, set_optlen, set_blcount, set_tree, set_trees.
    cbn [ts_trees]. rewrite Hk. exact Ht2.
  - (* overflow: pass 2 runs, and it also only writes <= maxlen *)
    destruct (gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                       (ts_heap s) (ts_maxcode s k) t2
                       (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov)
                       (sd_max_length k)
                       (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov
                          (sd_max_length k))
                       HEAP_SIZE ol1) as [t3 ol2] eqn:E2.
    assert (Ht3 : LenBound t3 (sd_max_length k)).
    { pose proof (gb_pass2_bound (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                    (ts_heap s) (ts_maxcode s k) t2
                    (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov)
                    (sd_max_length k)
                    (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov
                       (sd_max_length k))
                    HEAP_SIZE ol1 (sd_max_length k) Hm) as H.
      rewrite E2 in H. cbn [fst] in H. apply H; [lia | exact Ht2]. }
    assert (Hk : Z.eqb k k = true) by apply Z.eqb_refl.
    unfold set_statlen, set_optlen, set_blcount, set_tree, set_trees.
    cbn [ts_trees]. rewrite Hk. exact Ht3.
Qed.

(** ** The instance HuffCover wants

    The code-length tree's bound is [MAX_BL_BITS = 7] ([Trees.v:85],
    [sd_max_length TK_BL]), which is exactly the [<= 7] in [CLCovers]. *)
Example bl_max_length_is_7 : sd_max_length TK_BL = 7.
Proof. reflexivity. Qed.

Corollary gen_bitlen_bl_le_7 : forall s,
  LenBound (ts_trees s TK_BL) 7 ->
  LenBound (ts_trees (gen_bitlen TK_BL s) TK_BL) 7.
Proof.
  intro s. rewrite <- bl_max_length_is_7.
  apply gen_bitlen_len_bound. rewrite bl_max_length_is_7. lia.
Qed.

(** And the other two trees, since the same clamp governs them at 15. *)
Example l_max_length_is_15 : sd_max_length TK_L = 15.
Proof. reflexivity. Qed.

Example d_max_length_is_15 : sd_max_length TK_D = 15.
Proof. reflexivity. Qed.

Print Assumptions gb_pass1_bound.
Print Assumptions gb_pass2_bound.
Print Assumptions gen_bitlen_len_bound.
Print Assumptions gen_bitlen_bl_le_7.
