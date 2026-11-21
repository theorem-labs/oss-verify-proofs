(** * LdDynSeam — the DYNAMIC leg's seam bricks (item (v)), and a re-pricing.

    OWNER: ld-seams.  Consumes huffman-id's STAGED (not landed) send_tree
    round-trip.

    ** WHY THIS FILE EXISTS, AND THE REFUTATION IT CARRIES

    I priced item (v) in §LD-VSCOPE as "a field-for-field mirror plus one fuel
    hazard".  That price was WRONG, and wrong in the direction I had told the
    fleet my errors never went: an UNDER-estimate.  The mechanism is worth more
    than the number.  I priced [send_all_trees], which is seven flat [let]s, and
    never opened [send_go] forty lines above it — a seven-parameter stateful
    run-length encoder whose branch selection at trip [n] depends on the tree's
    length at [n+1] and whose [maxcnt]/[mincnt] are carried from the previous
    trip.  I had written the rule that forbids exactly this ("price from bodies,
    not signatures") after mis-pricing a bridge the same way.

    AND THE EXISTENCE CHECK MISSED THE ANSWER.  Item (v)'s hardest half was
    ALREADY PROVED — huffman-id's [send_tree_roundtrip], general, with a witness,
    kernel-checked — in their staging tree.  My lane-wide grep for it returned
    nothing because I piped it through [head -30], and another lane's MIRROR of
    the graded tree filled the window with guaranteed-irrelevant duplicates of
    the very definitions I was searching for.  A truncated existence check is
    not a weak check, it is a check that reports the opposite of the truth:
    "nobody has this" is what it printed.

    ** WHAT (v) ACTUALLY COSTS, now that the object has been read

      (v-1) header fields, [bw_send_bits] 5/5/4 vs [read_bits] 5/5/4    open, small
      (v-2) [sat_ranks] vs [read_cl_lengths]: the permutation (BELOW),
            plus [bbl_scan]'s zero tail beyond [blcodes]                open, medium
      (v-3) the RLE inverse, [send_go] vs [read_lengths]         DONE, huffman-id
      (v-4) the code-length tree's codes are Huff's canonical ones DONE, huffman-id
      (v-5) THE SEAM: (a) their capstone is stated at [bw_init] but
            [send_all_trees] calls [send_tree] mid-stream (BELOW, free —
            their [emit_items_bits] was already general in the writer);
            (b) ONE [read_lengths] call spans BOTH trees, so the decode
            side needs a residual-[need] split, and the RLE reads
            [last_len acc] ACROSS that boundary (BELOW)                 open, mine
      (v-6) their four hypotheses discharged at the [send_all_trees] call
            site — [build_bl_tree] territory, which they explicitly put
            outside their layer, including the one they flag as a genuine
            coverage obligation rather than a range fact                 open, unowned

    So (v) is a seam job plus a header job plus an undischarged-hypothesis job.
    My original conclusion ("tractable") happened to survive; the reasoning that
    produced it did not, which is the case that is invisible from the outcome.

    ** PIN.  huffman-id's stage is another lane's scratch, not the graded tree.
    Built against these artifacts (md5, 2026-08-18):
       SendTreeRT.vo
       SendGo.vo
       SendGoLens.vo
       SendGoWf.vo
       SendItems.vo
       ClStream.vo
       HuffGenCodes.vo
    Build with build-dyn.sh, which binds their stage root and refuses to run if
    the stage is absent or unbuilt.  Zero module names occur in both their stage
    and the live tree (checked with comm, not assumed), so binding two physical
    dirs to one logical root shadows nothing. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec BwStream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoLens SendGoWf SendTreeRT.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 0. Their capstone's assumptions, measured here rather than relayed

    huffman-id's own [.out] log records three "Closed under the global context"
    verdicts and a [coqchk] rc=0.  This is the same claim re-derived by a
    process that is not theirs, which is the only kind of confirmation worth
    anything when the artifact is the thing in question. *)

Print Assumptions send_tree_roundtrip.

(** ** 1. The permutation agreement (item (v-2)'s first half)

    The emitter sends [blcodes] three-bit lengths in [bl_order] order
    ([Trees.v:824]); the decoder reads them and scatters them back through
    [cl_order] ([DeflateSpec.v:646]).  The round trip needs the two
    permutations to be THE SAME, and they are the same nineteen entries in the
    same order — one written in [Z], one in [nat].  As a list equality this dies
    in milliseconds if either table is ever edited; as prose in a header it
    would not.  *)

Lemma bl_order_is_cl_order : map Z.of_nat cl_order = bl_order_l.
Proof. vm_compute. reflexivity. Qed.

Lemma bl_order_l_length : length bl_order_l = 19%nat.
Proof. reflexivity. Qed.

(** The form a proof consumes: unconditional, because [nth] and [Z.to_nat] are
    both total and agree on the out-of-range and negative cases. *)
Lemma bl_order_at : forall i,
  bl_order i = Z.of_nat (nth (Z.to_nat i) cl_order 0%nat).
Proof.
  intro i. unfold bl_order, zlist. rewrite <- bl_order_is_cl_order.
  exact (map_nth Z.of_nat cl_order 0%nat (Z.to_nat i)).
Qed.

(** ** 2. The accumulator crosses the tree boundary (item (v-5b))

    [send_all_trees] emits the literal/length tree and the distance tree with
    TWO [send_tree] calls, but [decode_dynamic_tables] reads them back with ONE
    [read_lengths] call for [nlit + ndist] lengths.  So the decoder's
    accumulator at the start of the distance tree is not [[]] — it holds all
    [nlit] literal lengths — and [CLWf]'s [CRep] clause reads [last_len acc].
    A repeat symbol at the head of the distance stream would therefore copy the
    LAST LITERAL LENGTH, across a boundary the encoder does not see.

    [CLWf] only ever inspects [acc] through [last_len], so it is congruent in
    that projection.  That is what lets huffman-id's [CLWf [] items] be reused
    at the second tree, and it is the fact that makes the cross-boundary read
    harmless — rather than an assumption that it is. *)

Lemma repeat_nonnil : forall (p k : nat), (1 <= k)%nat -> repeat p k <> [].
Proof.
  intros p k Hk. destruct k as [|k']; [lia|]. cbn [repeat]. intro C. discriminate C.
Qed.

Lemma last_len_app_nonnil : forall acc xs,
  xs <> [] -> last_len (acc ++ xs) = last_len xs.
Proof.
  intros acc xs Hxs. unfold last_len. rewrite rev_app_distr.
  destruct (rev xs) as [|y t] eqn:E.
  - exfalso. apply Hxs.
    apply (f_equal (@rev nat)) in E. rewrite rev_involutive in E.
    cbn [rev] in E. exact E.
  - reflexivity.
Qed.

Lemma CLWf_last_len_cong : forall items acc acc',
  last_len acc = last_len acc' -> CLWf acc items -> CLWf acc' items.
Proof.
  induction items as [|it tl IH]; intros acc acc' Hll H.
  - exact I.
  - destruct it as [l|p k|k|k]; cbn [CLWf] in H |- *.
    + destruct H as [Hl Htl]. split; [exact Hl|].
      apply (IH (acc ++ [l])); [|exact Htl].
      assert (Hne : [l] <> []) by (intro C; discriminate C).
      rewrite (last_len_app_nonnil acc [l] Hne),
              (last_len_app_nonnil acc' [l] Hne). reflexivity.
    + destruct H as [Hk [Hprev Htl]].
      split; [exact Hk|]. split; [rewrite <- Hll; exact Hprev|].
      apply (IH (acc ++ repeat p k)); [|exact Htl].
      assert (Hne : repeat p k <> []) by (apply repeat_nonnil; lia).
      rewrite (last_len_app_nonnil acc (repeat p k) Hne),
              (last_len_app_nonnil acc' (repeat p k) Hne). reflexivity.
    + destruct H as [Hk Htl]. split; [exact Hk|].
      apply (IH (acc ++ repeat 0%nat k)); [|exact Htl].
      assert (Hne : repeat 0%nat k <> []) by (apply repeat_nonnil; lia).
      rewrite (last_len_app_nonnil acc (repeat 0%nat k) Hne),
              (last_len_app_nonnil acc' (repeat 0%nat k) Hne). reflexivity.
    + destruct H as [Hk Htl]. split; [exact Hk|].
      apply (IH (acc ++ repeat 0%nat k)); [|exact Htl].
      assert (Hne : repeat 0%nat k <> []) by (apply repeat_nonnil; lia).
      rewrite (last_len_app_nonnil acc (repeat 0%nat k) Hne),
              (last_len_app_nonnil acc' (repeat 0%nat k) Hne). reflexivity.
Qed.

(** NEGATIVE CONTROL for the congruence: [CLWf] is NOT insensitive to [acc]
    outright — a [CRep] at the head reads [last_len acc] with no prior item to
    fix it, so the same item list is well formed under one accumulator and not
    under another.  Without this, the lemma above could be read as "the
    accumulator does not matter", which is exactly the reading that would make
    the cross-boundary case look free. *)
Example CLWf_does_depend_on_the_accumulator :
  CLWf [3%nat] [CRep 3%nat 4%nat] /\ ~ CLWf [5%nat] [CRep 3%nat 4%nat].
Proof.
  split.
  - cbn [CLWf]. split; [lia|]. split; [reflexivity|exact I].
  - intros [_ [Hprev _]]. cbn [last_len rev] in Hprev. discriminate Hprev.
Qed.

(** ** 3. Their capstone at an arbitrary writer (item (v-5a))

    [send_tree_roundtrip] is stated at [bw_init], because that is where a
    standalone round-trip belongs.  [send_all_trees] calls [send_tree] twice
    MID-STREAM, after the 5/5/4 header fields and [sat_ranks]'s three-bit
    values, so the writer is neither empty nor byte-aligned.

    This needed no new induction: their [emit_items_bits] was already stated at
    an arbitrary writer with the [bw_wf] preserved clause, and only the final
    corollary specialised it.  Sixth instance in this campaign of the same
    pattern — the blocker was an unpublished general form of an existing fact,
    not missing proving capacity. *)

Theorem send_tree_stream_at_any_writer :
  forall t maxc cl blt maxcbl blc bits b,
  0 <= maxc <= 285 ->
  (forall i, 0 <= t_len t i) ->
  t_len t (maxc + 1) = 65535 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  LensOf blt cl -> BlcOf blc cl -> ValidLengths cl 7%nat ->
  AbsentBeyond cl maxcbl -> -1 <= maxcbl <= 288 ->
  cl_bits cl (send_tree_items t maxc) = Some bits ->
  bw_wf b ->
  bw_stream (send_tree t maxc (gen_codes blt maxcbl blc) b)
    = bw_stream b ++ bits
  /\ bw_wf (send_tree t maxc (gen_codes blt maxcbl blc) b).
Proof.
  intros t maxc cl blt maxcbl blc bits b
         Hmc Hnn Hguard Hlen15 Hlens Hblc HV Hab Hmcbl Hcb Hbw.
  rewrite (send_tree_emit t maxc (gen_codes blt maxcbl blc) b Hnn).
  exact (emit_items_bits cl blt maxcbl blc (send_tree_items t maxc) [] bits b
           Hlens Hblc HV Hab Hmcbl
           (send_tree_items_wf t maxc Hmc Hguard Hlen15) Hcb Hbw).
Qed.

Print Assumptions bl_order_at.
Print Assumptions CLWf_last_len_cong.
Print Assumptions send_tree_stream_at_any_writer.
