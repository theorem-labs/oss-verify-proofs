(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* the zlib 1.4 twin of GtBodySelect, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from GtBodySelect), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * GtBodySelect — the GAP7 corollary HEAD (statement-only, per (viii)).

    OWNER: an earlier development run (post-B3 commission, GAP7-PLAN W-A recommission).
    FACTORING PICK: the census form — ONE generic body-SUCCESS lemma;
    q7's three thin wrappers compose it with q6's landed entry/tail
    trilogy + the L0E transfer per config.  Chairs pass before proving.

    WHAT THIS IS: the landed block walk (ZReproQ6W.zr_body_walk, now
    premise-free via GtHuffFixed.zr_huff_fixed_holds +
    Composite.zr_huff_dyn_leg_holds) concludes the DISJUNCTIVE
    [zr_body_exit]: success-mirror OR M_BAD OR ret-preserving
    leave/fuel.  The pump faces need the CONVERSE-DIRECTION selection:
    on a stream whose DECLARATIVE decode succeeds (the emitted-stream
    half, q5's D2 corollaries) and with ROOM, the first arm holds
    POSITIVELY.  BAD arms are refuted by the round's marker/hdecode-None
    corpus (machine BAD only where dec also fails); leave arms by
    accounting (full input present under [br_wf]; output room from the
    cap premise).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsIn Inflate DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro ZReproL0E ZReproQ6A ZReproQ6W W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtBodySelect.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** THE HEAD.  Premises = [zr_body_walk]'s own entry band + the
    declarative success equation + room; conclusion = [zr_body_exit]'s
    first arm VERBATIM with the walk's existential [out] pinned to the
    premise's [X] and the reader pinned to [rem].

    Two premise slots FLAGGED for the chairs' pass:
    [ROOM] is spelled [zlen X <= q_out q]: [dec_stream_from] accumulates
    onto the entry slice, so [X] contains the [o_put]-prefix and the
    fresh bytes must fit in [o_left]; with the entry band's
    [q_out = o_put + o_left] this is exactly [cap >= zlen x] at the
    wrapper (ZR_PumpSucceeds quantifies cap above zlen x).
    [STRICT re-freeze (the incomplete-header STOP, both chairs verified;
    (viii) round 2)]: the premise is the STRICT decoder — the lax text
    plus the four machine-accept guards (Gap7Strict.v; asymmetry table
    in its header).  ONE premise replacing the lax one per q7's
    consumer constraint; the weakening lemma keeps every lax consumer
    supplied; q5's landed gen_bitlen_out kraft equality supplies the
    guards on emitted streams.
    [INPUT] carries NO extra premise: the pump's single Z_FINISH call
    hands the machine the whole encoded stream, and [br_wf] ties
    [br_have] to the reader — the starvation-leave refutation is proof
    content, not statement content.  If the proof finds a genuine hole
    here the head gains an availability premise and the chairs see a
    REPLACE. *)
Definition ZrBodySelect14 : Prop :=
  forall c q X rem,
    zr_cflush_ok c ->
    zr_body_entry q ->
    h_mode (s_hdr (q_st q)) = M_TYPE ->
    dec_stream_from_strict (br_stream (q_br q))
      (ob_slice (q_ob q) 0 (o_put (q_ob q))) = Some (X, rem) ->
    zlen X <= q_out q ->
    exists k q',
      inf_iter14 k c q = Some q'
      /\ br_stream (q_br q') = rem
      /\ ob_slice (q_ob q') 0 (o_put (q_ob q')) = X
      /\ br_wf (q_br q')
      /\ 0 <= o_put (q_ob q')
      /\ 0 <= o_left (q_ob q')
      /\ o_put (q_ob q') + o_left (q_ob q')
         = o_put (q_ob q) + o_left (q_ob q)
      /\ h_mode (s_hdr (q_st q')) = M_TYPE
      /\ h_last (s_hdr (q_st q')) <> 0
      /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
      /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
      /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
      /\ w_wsize (s_win (q_st q')) = w_wsize (s_win (q_st q))
      /\ w_whave (s_win (q_st q')) = w_whave (s_win (q_st q))
      /\ t_sane (s_tab (q_st q')) = t_sane (s_tab (q_st q))
      /\ W2Stream.br_haligned (q_br q')
      /\ br_have (q_br q') + br_bits (q_br q') / 8 <= 4294967290
      (* re-freeze (q7 consumer-pass amendment, pre-proof): the zlib
         adler gate folds upd_check onto the ENTRY h_check over the
         exported slice, and gzip's crc+ISIZE gates read h_total —
         without these frames the M_TYPE head has no consumer.  Spelling
         verbatim ZrBodySelectC (q7's staged wrapper bed).  Head0 is
         deliberately WITHOUT them: the raw lane has no trailer gates. *)
      /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
      /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q)).

(** The raw lane's entry variant (wrap-0 M_HEAD, mirroring
    zr_body_walk_head0) — same conclusion, so the wrappers stay
    copy-shaped across the three configs. *)
