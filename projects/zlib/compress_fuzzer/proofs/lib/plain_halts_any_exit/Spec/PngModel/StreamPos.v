(** * Spec.PngModel.StreamPos — bit-position exactness across the drain
      boundary (round-trip layer L1's last item).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends on
    [Spec.PngModel.{Base, Bits, ZBitsOut, Trees, Deflate, BwStream}].
    Adds no [Definition] any model function calls; edits nothing.

    WHY THIS EXISTS.  [BwStream.bw_stream] speaks about the writer's CURRENT
    queue, but the output is drained in chunks: [Deflate.flush_pending]
    ([Deflate.v:535], [deflate.c:904-933]) runs [_tr_flush_bits] and then
    MOVES [firstn len] bytes out of [bw_out] into [zs_out], keeping
    [bi_buf]/[bi_valid].  So after a pump trip [bw_stream] is no longer the
    whole emitted stream — it is the UN-DRAINED SUFFIX plus the pending bits,
    and every bit position established in the per-symbol and seam theorems is
    stated against a queue a drain has since shortened.

    So the exactness property is an invariant ACROSS THE SPLIT: what has been
    handed out, concatenated with what is still held, does not change.  Read
    plainly, [flush_pending_stream] says A PUMP TRIP MOVES BITS ACROSS THE
    BOUNDARY BETWEEN "OUTPUT" AND "HELD" WITHOUT SHIFTING, DUPLICATING OR
    LOSING ONE — which is what every downstream composition silently assumes.

    It is the writer's counterpart of [ZBitsBridge.br_stream_pullbyte] (the
    reader's "buffering is a no-op at spec level").

    SCOPE, so this is not read as more than it is: exactness across the DRAIN
    boundary only.  It says nothing about how many trips a pump takes — that is
    [CodecThy.v]'s fuel-sufficiency reduction, open there and not this file's. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits ZBitsOut Chunk Trees Deflate BwStream.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. The byte split IS the bit split

    This is the whole formal content of "no bit shifts at the boundary". *)

Lemma bytes_bits_firstn_skipn : forall n l,
  bytes_bits (firstn n l) ++ bytes_bits (skipn n l) = bytes_bits l.
Proof.
  intros n l. rewrite <- bytes_bits_app. now rewrite firstn_skipn.
Qed.

(** ** 2. The total emitted stream of a deflate state *)

Definition dst_stream (s : DSt) : list bool :=
  bytes_bits (zs_out (d_strm s)) ++ bw_stream (ts_bw (d_ts s)).

(** ** 3. A pump trip is exact

    Three cases, and the third is the one a statement written for "flush
    everything" would miss: [availout] can CAP the move, so a trip may drain
    FEWER bytes than are pending and the invariant has to hold for a PARTIAL
    drain. *)

Theorem flush_pending_stream : forall s,
  bw_wf (ts_bw (d_ts s)) ->
  dst_stream (flush_pending s) = dst_stream s
  /\ bw_wf (ts_bw (d_ts (flush_pending s))).
Proof.
  intros s Hwf.
  (* the opening [_tr_flush_bits] is a stream no-op, and that is why no padding
     term appears anywhere below -- unlike [bi_windup], which IS observable *)
  destruct (bw_flush_stream (ts_bw (d_ts s)) Hwf) as [Sf Wf].
  unfold flush_pending, dst_stream, tr_flush_bits, set_bw, setD_ts, setD_strm,
         setZ_out, setZ_availout, setZ_totalout;
    cbn [d_ts d_strm ts_bw zs_out].
  destruct (Z.eqb_spec
              (if Z.ltb (zs_availout (d_strm s)) (zlen (bw_out (bw_flush (ts_bw (d_ts s)))))
               then zs_availout (d_strm s)
               else zlen (bw_out (bw_flush (ts_bw (d_ts s)))))
              0) as [E0|Ene].
  - (* nothing to drain: only the flush happened *)
    cbn [d_ts d_strm ts_bw zs_out]. rewrite Sf. split; [reflexivity | exact Wf].
  - (* a partial or complete drain *)
    cbn [d_ts d_strm ts_bw zs_out].
    set (len := if Z.ltb (zs_availout (d_strm s))
                         (zlen (bw_out (bw_flush (ts_bw (d_ts s)))))
                then zs_availout (d_strm s)
                else zlen (bw_out (bw_flush (ts_bw (d_ts s))))) in *.
    set (bf := bw_flush (ts_bw (d_ts s))) in *.
    (* the moved prefix and the retained suffix recombine *)
    unfold bw_stream; cbn [bw_out bw_buf bw_valid].
    rewrite bytes_bits_app, <- !app_assoc.
    rewrite (app_assoc (bytes_bits (firstn (Z.to_nat len) (bw_out bf)))).
    rewrite bytes_bits_firstn_skipn.
    split.
    + unfold dst_stream, bw_stream in Sf. rewrite <- Sf. reflexivity.
    + exact Wf.
Qed.

(** ** 4. What it buys: a bit position survives an arbitrary drain schedule

    The corollary the compositions need.  If two states have the same total
    stream, they still do after a trip — so any statement about bit positions
    in the emitted stream is stable under whatever interleaving of emission and
    drainage the pump happens to choose. *)

Corollary flush_pending_stream_stable : forall s1 s2,
  bw_wf (ts_bw (d_ts s1)) -> bw_wf (ts_bw (d_ts s2)) ->
  dst_stream s1 = dst_stream s2 ->
  dst_stream (flush_pending s1) = dst_stream (flush_pending s2).
Proof.
  intros s1 s2 H1 H2 Heq.
  destruct (flush_pending_stream s1 H1) as [E1 _].
  destruct (flush_pending_stream s2 H2) as [E2 _].
  rewrite E1, E2. exact Heq.
Qed.

(** And the form a consumer holding a per-symbol fact wants: the bits the
    writer had appended are still there, as a suffix of the total, after a
    trip. *)
Corollary flush_pending_preserves_suffix : forall s pre bits,
  bw_wf (ts_bw (d_ts s)) ->
  dst_stream s = pre ++ bits ->
  dst_stream (flush_pending s) = pre ++ bits.
Proof.
  intros s pre bits Hwf Heq.
  destruct (flush_pending_stream s Hwf) as [E _]. rewrite E. exact Heq.
Qed.

(** ** 5. THE UNKILLABLE CLASS, DECLARED RATHER THAN RUN

    filter-id's §LE-DRAIN establishes the better instrument discipline here:
    when a mutation class CANNOT kill a theorem, say so up front with a proof
    instead of running the mutants and interpreting the silence.  Two classes
    are unkillable against [flush_pending_stream], and both for the same
    reason — THIS FILE IS ABOUT STREAM CONTENT, NOT ABOUT WHERE OR WHEN BITS
    SIT.

    (i) THE SPLIT POINT.  [bytes_bits_firstn_skipn] holds for EVERY [n], and
    that generality is not incidental: it is exactly what the
    [availout]-capped partial drain needs.  So perturbing where the drain cuts
    perturbs nothing.  One line from the lemma above; filter-id proved the
    same statement independently at §LE-DRAIN, and I state it here rather than
    importing across lanes for a one-line consequence of a lemma I already
    have. *)

Lemma drain_split_point_unobservable : forall n m l,
  bytes_bits (firstn n l) ++ bytes_bits (skipn n l)
  = bytes_bits (firstn m l) ++ bytes_bits (skipn m l).
Proof. intros n m l. now rewrite !bytes_bits_firstn_skipn. Qed.

(** (ii) THE OPENING [_tr_flush_bits].  Removing it cannot change
    [dst_stream], because [BwStream.bw_flush_stream] proves [bi_flush] is a
    stream no-op.  It DOES change how many bytes a given trip moves — [len]
    is computed from the post-flush queue — but the theorem fixes the TOTAL
    and is silent about the division, so both sides of that change satisfy it.
    RECLASSIFICATION, on the record: I first ran this as mutant W3, predicted
    a survivor, got a kill, and filed it INCONCLUSIVE-BY-TACTIC-DEPENDENCY
    because my proof names [tr_flush_bits] in four tactic steps the mutant
    deletes.  With filter-id's framing it is better than inconclusive — it is
    UNKILLABLE BY CONSTRUCTION, and the witness is a theorem already in
    BwStream.v rather than a mutant run.  The prediction was right and the
    instrument was the wrong one. *)

(** What DOES kill is the PAIRING class — [firstn n] and [skipn n] must use
    the same [n] and appear in that order — and my suite covers all three of
    its members: LOSS (a byte dropped at the boundary), DUPLICATION (the
    drained prefix output AND retained), REORDER (prefix and suffix swapped).
    All three kill inside [flush_pending_stream]'s assembly.
    filter-id's sharpest point, which is why REORDER is the expensive half:
    swapping PRESERVES THE BIT COUNT, so any length-based or bits-drained-
    per-trip check passes it.  Only comparing the sequence catches it — and
    this theorem compares sequences, which is what the REORDER kill
    demonstrates. *)
