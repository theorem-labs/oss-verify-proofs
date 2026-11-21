(** * GbRange — the UPPER bound at the VISITED indices, which is the version
      [build_tree] can actually use.

    OWNER: huffman-id.  Found by writing the composition, not by reading.

    THE GAP, and it is a real one that four green files did not reveal.
    [GenBitlen.gen_bitlen_len_bound] proves the upper bound from a GLOBAL
    hypothesis, [LenBound (ts_trees s k) (sd_max_length k)] — every entry of the
    input tree's length array is already within bounds. Every theorem built on it
    is true as stated. But **that hypothesis is FALSE at the point [build_tree]
    calls [gen_bitlen]**, and it is false for a structural reason:

      [t_dad] and [t_len] are ALIASES for the same [tr_dl] slot (Trees.v:222-224,
      zlib's [union { ush dad; ush len; }]). The combine loop fills that array
      with DADS — [t_setdad (t_setdad t1 m node) n node], node ids running up to
      HEAP_SIZE — and [gen_bitlen] is what later overwrites them with lengths. So
      on entry the "length" array holds values far above [max_length], and
      [LenBound] does not hold.

    So [GenBitlen.gen_bitlen_in_range] and [GbVisit.bl_tree_lengths_in_1_7], both
    green, both true, DO NOT APPLY WHERE (B) NEEDS THEM. Nothing is wrong with
    them; the hypothesis is simply unavailable at the call site.

    THE FIX IS THE SHAPE ALREADY USED FOR THE LOWER BOUND: state the upper bound
    at the VISITED indices with the "achieved OR preserved" disjunction, so it
    depends on the clamp rather than on the input array. Mirrors
    [GbVisit.gb_pass1_pos] line for line.

    I want this recorded as a methodological point, because it cost nothing to
    find and would have cost a lot to miss: **a global hypothesis is the easiest
    kind to prove a theorem WITH and the easiest kind to be unable to DISCHARGE.**
    The lower bound forced me into the per-index form because there was no global
    version to reach for; the upper bound had one, I used it, and it was the wrong
    tool. Writing the composition is what surfaced it — the same activity that
    surfaced the leftover-is-the-root gap. Two real gaps found by composing, zero
    by re-reading. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import GenBitlen GbVisit.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** Every write into the [dl] array is a [u16], so nonnegativity is free — the
    only property of the input array the bounds below actually need. *)
Lemma dl_nn_setlen : forall t i v,
  (forall j, 0 <= t_len t j) -> forall j, 0 <= t_len (t_setlen t i v) j.
Proof.
  intros t i v H j. destruct (Z.eq_dec j i) as [->|Hne].
  - rewrite t_len_setlen_same'. unfold u16. apply Z.mod_pos_bound. lia.
  - rewrite t_len_setlen_other' by exact Hne. apply H.
Qed.

Lemma gb_pass1_nn :
  forall fuel k hp maxc maxlen base extra stree h t blc ol sl ov,
  (forall i, 0 <= t_len t i) ->
  forall i, 0 <= t_len (gb1_tree (gb_pass1 fuel k hp maxc maxlen base extra
                                           stree h t blc ol sl ov)) i.
Proof.
  induction fuel as [|f IH];
    intros k hp maxc maxlen base extra stree h t blc ol sl ov Hnn i.
  - cbn [gb_pass1 gb1_tree]. apply Hnn.
  - cbn [gb_pass1].
    destruct (Z.leb HEAP_SIZE h); [cbn [gb1_tree]; apply Hnn|].
    destruct (Z.ltb maxc (hp h)); apply IH; apply dl_nn_setlen; exact Hnn.
Qed.

(** ** Pass 1: every VISITED index ends up at most [maxlen]

    The clamp ([Trees.v:402]) does all the work; the input array is irrelevant. *)
Lemma gb_pass1_ub :
  forall fuel k hp maxc maxlen base extra stree h t blc ol sl ov,
  1 <= maxlen <= 15 ->
  (forall i, 0 <= t_len t i) ->
  HEAP_SIZE - h <= Z.of_nat fuel ->
  forall h0, h0 < HEAP_SIZE ->
    (h <= h0 \/ t_len t (hp h0) <= maxlen) ->
    t_len (gb1_tree (gb_pass1 fuel k hp maxc maxlen base extra stree
                              h t blc ol sl ov)) (hp h0) <= maxlen.
Proof.
  induction fuel as [|f IH];
    intros k hp maxc maxlen base extra stree h t blc ol sl ov
           Hm Hnn Hf h0 Hh0 Hdisj.
  - cbn [gb_pass1 gb1_tree].
    change (Z.of_nat 0) with 0 in Hf.
    destruct Hdisj as [Hle|Hub]; [lia | exact Hub].
  - cbn [gb_pass1].
    destruct (Z.leb HEAP_SIZE h) eqn:Eend.
    + apply Z.leb_le in Eend. cbn [gb1_tree].
      destruct Hdisj as [Hle|Hub]; [lia | exact Hub].
    + apply Z.leb_gt in Eend.
      assert (Hv : 1 <= (if Z.ltb maxlen (t_len t (t_dad t (hp h)) + 1)
                         then maxlen else t_len t (t_dad t (hp h)) + 1) <= maxlen).
      { destruct (Z.ltb maxlen (t_len t (t_dad t (hp h)) + 1)) eqn:E.
        - lia.
        - apply Z.ltb_ge in E. pose proof (Hnn (t_dad t (hp h))) as Hd. lia. }
      set (bits := if Z.ltb maxlen (t_len t (t_dad t (hp h)) + 1)
                   then maxlen else t_len t (t_dad t (hp h)) + 1) in *.
      set (t1 := t_setlen t (hp h) bits) in *.
      assert (Hnn1 : forall i, 0 <= t_len t1 i).
      { intro i. unfold t1. destruct (Z.eq_dec i (hp h)) as [->|Hne].
        - rewrite t_len_setlen_same'. unfold u16.
          rewrite Z.mod_small by lia. lia.
        - rewrite t_len_setlen_other' by exact Hne. apply Hnn. }
      assert (Hdisj1 : h + 1 <= h0 \/ t_len t1 (hp h0) <= maxlen).
      { destruct (Z_le_gt_dec (h + 1) h0) as [Hle|Hgt]; [left; exact Hle|].
        right. unfold t1.
        destruct (Z.eq_dec (hp h0) (hp h)) as [Heq|Hne].
        - rewrite Heq. rewrite t_len_setlen_same'. unfold u16.
          rewrite Z.mod_small by lia. lia.
        - rewrite t_len_setlen_other' by exact Hne.
          destruct Hdisj as [Hle|Hub]; [|exact Hub].
          assert (h0 = h) by lia. subst h0. exfalso. apply Hne. reflexivity. }
      destruct (Z.ltb maxc (hp h)); apply IH; try assumption; lia.
Qed.

(** ** Pass 2 keeps it: it writes [bits], and [bits <= maxlen] throughout *)
Lemma gb_pass2_ub : forall fuel hp maxc t blc bits n h ol i maxlen,
  1 <= bits <= maxlen -> maxlen <= 15 ->
  t_len t i <= maxlen ->
  t_len (fst (gb_pass2 fuel hp maxc t blc bits n h ol)) i <= maxlen.
Proof.
  induction fuel as [|f IH]; intros hp maxc t blc bits n h ol i maxlen Hb Hm Hub.
  - cbn [gb_pass2 fst]. exact Hub.
  - cbn [gb_pass2].
    destruct (Z.eqb n 0).
    + destruct (Z.leb bits 1) eqn:E1; [exact Hub|].
      apply Z.leb_gt in E1. apply IH with (maxlen := maxlen); [lia | lia | exact Hub].
    + destruct (Z.ltb maxc (hp (h - 1)));
        [apply IH with (maxlen := maxlen); assumption|].
      destruct (Z.eqb (t_len t (hp (h - 1))) bits);
        [apply IH with (maxlen := maxlen); assumption|].
      apply IH with (maxlen := maxlen); [exact Hb | exact Hm |].
      destruct (Z.eq_dec i (hp (h - 1))) as [->|Hne].
      * rewrite t_len_setlen_same'. unfold u16.
        rewrite Z.mod_small by lia. lia.
      * rewrite t_len_setlen_other' by exact Hne. exact Hub.
Qed.

(** ** The upper bound at [gen_bitlen], with NO global [LenBound]

    Compare [GenBitlen.gen_bitlen_len_bound]: same conclusion at the visited
    index, but the input array is unconstrained apart from nonnegativity. That is
    what makes it usable after the combine loop. *)
Theorem gen_bitlen_ub : forall k s h0,
  1 <= sd_max_length k <= 15 ->
  (forall i, 0 <= t_len (ts_trees s k) i) ->
  0 <= ts_heapmax s ->
  ts_heapmax s + 1 <= h0 < HEAP_SIZE ->
  t_len (ts_trees (gen_bitlen k s) k) (ts_heap s h0) <= sd_max_length k.
Proof.
  intros k s h0 Hm Hnn Hhm Hh0.
  unfold gen_bitlen.
  set (t0 := t_setlen (ts_trees s k) (ts_heap s (ts_heapmax s)) 0) in *.
  assert (Hnn0 : forall i, 0 <= t_len t0 i).
  { intro i. unfold t0.
    destruct (Z.eq_dec i (ts_heap s (ts_heapmax s))) as [->|Hne].
    - rewrite t_len_setlen_same'. unfold u16. reflexivity.
    - rewrite t_len_setlen_other' by exact Hne. apply Hnn. }
  destruct (gb_pass1 (Z.to_nat HEAP_SIZE + 1) k (ts_heap s) (ts_maxcode s k)
                     (sd_max_length k) (sd_extra_base k) (sd_extra k)
                     (sd_stree k) (ts_heapmax s + 1) t0
                     (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s))
                     (ts_optlen s) (ts_statlen s) 0)
    as [[[[t2 blc1] ol1] sl1] ov] eqn:E1.
  assert (Ht2 : t_len t2 (ts_heap s h0) <= sd_max_length k).
  { pose proof (gb_pass1_ub (Z.to_nat HEAP_SIZE + 1) k (ts_heap s)
                  (ts_maxcode s k) (sd_max_length k) (sd_extra_base k)
                  (sd_extra k) (sd_stree k) (ts_heapmax s + 1) t0
                  (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s))
                  (ts_optlen s) (ts_statlen s) 0 Hm Hnn0) as H.
    rewrite E1 in H. cbn [gb1_tree] in H.
    apply H.
    - rewrite Nat2Z.inj_add, Z2Nat.id by (unfold HEAP_SIZE; lia).
      change (Z.of_nat 1) with 1. lia.
    - lia.
    - left. lia. }
  (* nonnegativity also has to reach pass 2 *)
  assert (Hnn2 : forall i, 0 <= t_len t2 i).
  { pose proof (gb_pass1_nn (Z.to_nat HEAP_SIZE + 1) k (ts_heap s)
                  (ts_maxcode s k) (sd_max_length k) (sd_extra_base k)
                  (sd_extra k) (sd_stree k) (ts_heapmax s + 1) t0
                  (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s))
                  (ts_optlen s) (ts_statlen s) 0 Hnn0) as H.
    rewrite E1 in H. cbn [gb1_tree] in H. exact H. }
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
    assert (Ht3 : t_len t3 (ts_heap s h0) <= sd_max_length k).
    { pose proof (gb_pass2_ub (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                    (ts_heap s) (ts_maxcode s k) t2
                    (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov)
                    (sd_max_length k)
                    (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov
                       (sd_max_length k))
                    HEAP_SIZE ol1 (ts_heap s h0) (sd_max_length k)) as H.
      rewrite E2 in H. cbn [fst] in H. apply H; [lia | lia | exact Ht2]. }
    assert (Hk : Z.eqb k k = true) by apply Z.eqb_refl.
    unfold set_statlen, set_optlen, set_blcount, set_tree, set_trees.
    cbn [ts_trees]. rewrite Hk. exact Ht3.
Qed.

(** ** (B) at [gen_bitlen], in the form [build_tree] can consume

    Both ends, at the visited index, with the input array required only to be
    nonnegative — which the union's [u16] writes give for free. *)
Theorem gen_bitlen_range_at : forall k s h0,
  1 <= sd_max_length k <= 15 ->
  (forall i, 0 <= t_len (ts_trees s k) i) ->
  0 <= ts_heapmax s ->
  ts_heapmax s + 1 <= h0 < HEAP_SIZE ->
  1 <= t_len (ts_trees (gen_bitlen k s) k) (ts_heap s h0) <= sd_max_length k.
Proof.
  intros. split; [apply gen_bitlen_pos | apply gen_bitlen_ub]; assumption.
Qed.

Corollary bl_lengths_in_1_7_at : forall s h0,
  (forall i, 0 <= t_len (ts_trees s TK_BL) i) ->
  0 <= ts_heapmax s ->
  ts_heapmax s + 1 <= h0 < HEAP_SIZE ->
  1 <= t_len (ts_trees (gen_bitlen TK_BL s) TK_BL) (ts_heap s h0) <= 7.
Proof.
  intros s h0 Hnn Hhm Hh0.
  rewrite <- bl_max_length_is_7.
  apply gen_bitlen_range_at;
    [rewrite bl_max_length_is_7; lia | exact Hnn | exact Hhm | exact Hh0].
Qed.

Print Assumptions gb_pass1_nn.
Print Assumptions gb_pass1_ub.
Print Assumptions gb_pass2_ub.
Print Assumptions gen_bitlen_ub.
Print Assumptions gen_bitlen_range_at.
Print Assumptions bl_lengths_in_1_7_at.
