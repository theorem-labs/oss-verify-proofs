(** * GbVisit — (B-lower)'s arithmetic half: [gen_bitlen] never writes a zero
      length, and it writes at EVERY index of the walked window.

    OWNER: huffman-id.  The two items left at the end of BtRoot.v.

    THE TWO CLAIMS ARE ONE INDUCTION, which I did not expect and which is why this
    file is short.  I planned them as separate lemmas — "never writes 0" and
    "visits every h" — and they collapse into a single statement carrying the
    now-familiar disjunction:

        forall h0 < HEAP_SIZE,  (h <= h0  \/  1 <= t_len t (hp h0))
                             -> 1 <= t_len (final tree) (hp h0)

    "either this index is still ahead of the walk (so it WILL be written), or it
    is already positive (so it was written, or never needed writing)".  The walk
    and the value are the same fact seen from two ends. Fourth time in this lane
    that the workable statement was "achieved OR preserved" rather than either
    alone — at this point I reach for that shape first rather than last.

    A TRAP THIS FILE HIT AGAIN, third time in one session and each time wearing a
    different hat: BARE [cbn] reduces more than you asked.  Here [cbn in Hf]
    unfolded [HEAP_SIZE] to [573] in that ONE hypothesis while the others kept the
    constant, so [lia] compared two atoms it could not relate and reported
    "Cannot find witness" — for the third distinct reason tonight.  Every [cbn]
    in this file now carries a delta list, and the one numeral reduction I need is
    a surgical [change].

    WHY NO DISTINCTNESS IS NEEDED, which removes the last thing I was worried
    about.  The parked window could in principle hold the same index twice, and I
    had expected to need "the parked slots are distinct" to stop a second write
    clobbering a good length.  It is unnecessary: EVERY write is [>= 1], so a
    second write at the same index is just as good as the first.  A property that
    is preserved by all writes needs no injectivity — worth remembering, because
    distinctness of an array's contents is usually expensive. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import GenBitlen.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Pass 1: every index in the walked window ends up with a positive length *)
Lemma gb_pass1_pos :
  forall fuel k hp maxc maxlen base extra stree h t blc ol sl ov,
  1 <= maxlen <= 15 ->
  (forall i, 0 <= t_len t i) ->
  HEAP_SIZE - h <= Z.of_nat fuel ->
  forall h0, h0 < HEAP_SIZE ->
    (h <= h0 \/ 1 <= t_len t (hp h0)) ->
    1 <= t_len (gb1_tree (gb_pass1 fuel k hp maxc maxlen base extra stree
                                   h t blc ol sl ov)) (hp h0).
Proof.
  induction fuel as [|f IH];
    intros k hp maxc maxlen base extra stree h t blc ol sl ov
           Hm Hnn Hf h0 Hh0 Hdisj.
  - cbn [gb_pass1 gb1_tree].
    (* [cbn in Hf] (no delta list) unfolds HEAP_SIZE to 573 in Hf ONLY, so [lia]
       then sees [573] in one hypothesis and the opaque constant [HEAP_SIZE] in
       the others and finds no contradiction.  Reduce the numeral surgically. *)
    change (Z.of_nat 0) with 0 in Hf.
    destruct Hdisj as [Hle|Hpos]; [lia | exact Hpos].
  - cbn [gb_pass1].
    destruct (Z.leb HEAP_SIZE h) eqn:Eend.
    + apply Z.leb_le in Eend. cbn [gb1_tree].
      destruct Hdisj as [Hle|Hpos]; [lia | exact Hpos].
    + apply Z.leb_gt in Eend.
      (* the written value is in [1, maxlen] whichever branch the clamp takes *)
      assert (Hv : 1 <= (if Z.ltb maxlen (t_len t (t_dad t (hp h)) + 1)
                         then maxlen else t_len t (t_dad t (hp h)) + 1) <= maxlen).
      { destruct (Z.ltb maxlen (t_len t (t_dad t (hp h)) + 1)) eqn:E.
        - lia.
        - apply Z.ltb_ge in E. pose proof (Hnn (t_dad t (hp h))) as Hd. lia. }
      set (bits := if Z.ltb maxlen (t_len t (t_dad t (hp h)) + 1)
                   then maxlen else t_len t (t_dad t (hp h)) + 1) in *.
      set (t1 := t_setlen t (hp h) bits) in *.
      (* [t1] is still everywhere-nonnegative *)
      assert (Hnn1 : forall i, 0 <= t_len t1 i).
      { intro i. unfold t1. destruct (Z.eq_dec i (hp h)) as [->|Hne].
        - rewrite t_len_setlen_same'. unfold u16.
          rewrite Z.mod_small by lia. lia.
        - rewrite t_len_setlen_other' by exact Hne. apply Hnn. }
      (* and the disjunction advances to [h + 1] *)
      assert (Hdisj1 : h + 1 <= h0 \/ 1 <= t_len t1 (hp h0)).
      { destruct (Z_le_gt_dec (h + 1) h0) as [Hle|Hgt]; [left; exact Hle|].
        right. unfold t1.
        destruct (Z.eq_dec (hp h0) (hp h)) as [Heq|Hne].
        - (* same slot: it was just written, and the write is >= 1 *)
          rewrite Heq. rewrite t_len_setlen_same'. unfold u16.
          rewrite Z.mod_small by lia. lia.
        - rewrite t_len_setlen_other' by exact Hne.
          (* [h0 < h + 1] and [h0 <> h] force the right disjunct *)
          destruct Hdisj as [Hle|Hpos]; [|exact Hpos].
          assert (h0 = h) by lia. subst h0. exfalso. apply Hne. reflexivity. }
      destruct (Z.ltb maxc (hp h)); apply IH; try assumption; lia.
Qed.

(** ** Pass 2 cannot destroy it

    [gb_pass2] writes [bits], and [bits] starts at [max_length] and stops at 1, so
    every write is [>= 1] too.  Stated as preservation for EVERY index, which is
    all the composition needs. *)
Lemma gb_pass2_pos : forall fuel hp maxc t blc bits n h ol i,
  1 <= bits <= 15 ->
  1 <= t_len t i ->
  1 <= t_len (fst (gb_pass2 fuel hp maxc t blc bits n h ol)) i.
Proof.
  induction fuel as [|f IH]; intros hp maxc t blc bits n h ol i Hb Hpos.
  - cbn [gb_pass2 fst]. exact Hpos.
  - cbn [gb_pass2].
    destruct (Z.eqb n 0).
    + destruct (Z.leb bits 1) eqn:E1; [exact Hpos|].
      apply Z.leb_gt in E1. apply IH; [lia | exact Hpos].
    + destruct (Z.ltb maxc (hp (h - 1))); [apply IH; assumption|].
      destruct (Z.eqb (t_len t (hp (h - 1))) bits); [apply IH; assumption|].
      apply IH; [exact Hb|].
      destruct (Z.eq_dec i (hp (h - 1))) as [->|Hne].
      * (* [bits <= 15], so the [ush] truncation is the identity.  I first tried
           to case-split on [bits <= 65536] instead of carrying the real bound;
           [Z.mod_small] wants a STRICT [<], and the off-by-one surfaced as
           another "Cannot find witness" from the [by lia]. Carry the bound. *)
        rewrite t_len_setlen_same'. unfold u16.
        rewrite Z.mod_small by lia. lia.
      * rewrite t_len_setlen_other' by exact Hne. exact Hpos.
Qed.

(** ** (B-lower)'s arithmetic half, at [gen_bitlen]

    Both overflow branches are covered, so — exactly as with the UPPER bound in
    GenBitlen.v — this does not depend on [gb_adjust] being right. *)
Theorem gen_bitlen_pos : forall k s h0,
  1 <= sd_max_length k <= 15 ->
  (forall i, 0 <= t_len (ts_trees s k) i) ->
  0 <= ts_heapmax s ->
  ts_heapmax s + 1 <= h0 < HEAP_SIZE ->
  1 <= t_len (ts_trees (gen_bitlen k s) k) (ts_heap s h0).
Proof.
  intros k s h0 Hm Hnn Hhm Hh0.
  unfold gen_bitlen.
  set (t0 := t_setlen (ts_trees s k) (ts_heap s (ts_heapmax s)) 0) in *.
  assert (Hnn0 : forall i, 0 <= t_len t0 i).
  { intro i. unfold t0. destruct (Z.eq_dec i (ts_heap s (ts_heapmax s))) as [->|Hne].
    - rewrite t_len_setlen_same'. unfold u16. reflexivity.
    - rewrite t_len_setlen_other' by exact Hne. apply Hnn. }
  destruct (gb_pass1 (Z.to_nat HEAP_SIZE + 1) k (ts_heap s) (ts_maxcode s k)
                     (sd_max_length k) (sd_extra_base k) (sd_extra k)
                     (sd_stree k) (ts_heapmax s + 1) t0
                     (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s))
                     (ts_optlen s) (ts_statlen s) 0)
    as [[[[t2 blc1] ol1] sl1] ov] eqn:E1.
  assert (Ht2 : 1 <= t_len t2 (ts_heap s h0)).
  { pose proof (gb_pass1_pos (Z.to_nat HEAP_SIZE + 1) k (ts_heap s)
                  (ts_maxcode s k) (sd_max_length k) (sd_extra_base k)
                  (sd_extra k) (sd_stree k) (ts_heapmax s + 1) t0
                  (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s))
                  (ts_optlen s) (ts_statlen s) 0 Hm Hnn0) as H.
    rewrite E1 in H. cbn [gb1_tree] in H.
    apply H.
    - (* the fuel bound.  [lia] cannot relate [Z.of_nat (Z.to_nat HEAP_SIZE + 1)]
         to [HEAP_SIZE] on its own — they are unrelated ATOMS to it — so the
         conversion has to be done by rewriting, not by hoping. *)
      rewrite Nat2Z.inj_add, Z2Nat.id by (unfold HEAP_SIZE; lia).
      change (Z.of_nat 1) with 1. lia.
    - lia.
    - left. lia. }
  destruct (Z.eqb ov 0).
  - assert (Hk : Z.eqb k k = true) by apply Z.eqb_refl.
    unfold set_statlen, set_optlen, set_blcount, set_tree, set_trees.
    cbn [ts_trees]. rewrite Hk. exact Ht2.
  - destruct (gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                       (ts_heap s) (ts_maxcode s k) t2
                       (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov)
                       (sd_max_length k)
                       (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov
                          (sd_max_length k))
                       HEAP_SIZE ol1) as [t3 ol2] eqn:E2.
    assert (Ht3 : 1 <= t_len t3 (ts_heap s h0)).
    { pose proof (gb_pass2_pos (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                    (ts_heap s) (ts_maxcode s k) t2
                    (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov)
                    (sd_max_length k)
                    (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov
                       (sd_max_length k))
                    HEAP_SIZE ol1 (ts_heap s h0)) as H.
      rewrite E2 in H. cbn [fst] in H. apply H; [lia | exact Ht2]. }
    assert (Hk : Z.eqb k k = true) by apply Z.eqb_refl.
    unfold set_statlen, set_optlen, set_blcount, set_tree, set_trees.
    cbn [ts_trees]. rewrite Hk. exact Ht3.
Qed.

(** ** (B) IN FULL, both ends, for every index of the walked window

    Combining with [GenBitlen.gen_bitlen_len_bound]: every index [gb_pass1] walks
    comes out with a length in [1, max_length] — which for the code-length tree is
    [1, 7], exactly [HuffCover.CLCovers]'s requirement. *)
Theorem gen_bitlen_in_range : forall k s h0,
  1 <= sd_max_length k <= 15 ->
  (forall i, 0 <= t_len (ts_trees s k) i) ->
  LenBound (ts_trees s k) (sd_max_length k) ->
  0 <= ts_heapmax s ->
  ts_heapmax s + 1 <= h0 < HEAP_SIZE ->
  1 <= t_len (ts_trees (gen_bitlen k s) k) (ts_heap s h0) <= sd_max_length k.
Proof.
  intros k s h0 Hm Hnn Hb Hhm Hh0. split.
  - apply gen_bitlen_pos; assumption.
  - apply gen_bitlen_len_bound; assumption.
Qed.

Corollary bl_tree_lengths_in_1_7 : forall s h0,
  (forall i, 0 <= t_len (ts_trees s TK_BL) i) ->
  LenBound (ts_trees s TK_BL) 7 ->
  0 <= ts_heapmax s ->
  ts_heapmax s + 1 <= h0 < HEAP_SIZE ->
  1 <= t_len (ts_trees (gen_bitlen TK_BL s) TK_BL) (ts_heap s h0) <= 7.
Proof.
  intros s h0 Hnn Hb Hhm Hh0.
  rewrite <- bl_max_length_is_7.
  apply gen_bitlen_in_range;
    [rewrite bl_max_length_is_7; lia | exact Hnn
     | rewrite bl_max_length_is_7; exact Hb | exact Hhm | exact Hh0].
Qed.

Print Assumptions gb_pass1_pos.
Print Assumptions gb_pass2_pos.
Print Assumptions gen_bitlen_pos.
Print Assumptions gen_bitlen_in_range.
Print Assumptions bl_tree_lengths_in_1_7.
