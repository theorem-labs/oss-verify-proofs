(** * Gap7LeaveKill — PROPOSED leave-kill / fuel-arm-kill statements for
    g1's per-block assembly (q7 pass fork, bodysel-pass bed, 2026-08-22;
    fixsel protocol: STATEMENTS ONLY, g1 ratifies shapes before any
    proof — the (viii) grain).

    COMMISSION CONTEXT (ladder (b), Gap7BodySel ): the per-block
    step consumes the landed leg selections (Gap7LegSel :
    ZrHuffFixedLegSel_STMT / ZrHuffDynLegSel_STMT, both _holds-proved)
    and must reach the fuel head's GOOD-ARM-ONLY conclusion.  The legs
    conclude [zr_huff_exit_sel]'s 3-way disjunction; BAD arms carry
    entry-rebased declarative failure (refutable from the block's strict
    equations).  The leave/fuel arm is
      exists n s, inf_loop n c q = Some s
        /\ match s with InfLeave q2 => q_ret q2 = q_ret q
                      | InfFuel => True | _ => False end.

    FINDING (the survey's load-bearing result): THIS ARM IS NOT
    REFUTABLE FROM THE BLOCK'S PREMISES, at any altitude below the
    wrapper.  Witness world: a zlib-config state whose body decodes
    clean (all block premises hold) but whose reader ends before the
    4-byte adler trailer — the run Cont-steps through the whole body,
    then starves at M_CHECK's NEEDBITS(32): a RET-PRESERVING InfLeave.
    [inf_loop] from the LEG entry sees exactly that event as its first
    non-Cont outcome, so the leave arm is TRUE there while every block
    premise holds — no kill lemma premised on availability-under-br_wf
    + threaded room can conclude False.  (The wrapper altitude never
    meets the problem: its heads are good-arm-only, and the fuel gap is
    crossed positively — GtInfTotal.inflate_model_total_reach +
    Q6AsmSupport.zr_loop_uniq + zr_leave_done_fin — at ReachSt entries
    from reach_entry_fresh.)

    CONSEQUENCE: the per-block "kill" cannot be a refutation of the
    landed legs' third arm; it must be the POSITIVE selection at the leg
    altitude — the good arm CONCLUDED under the block's own availability
    (declarative success on the entry stream, with br_wf tying the
    stream to the counters) and threaded room (the head's
    [zlen X <= q_out] through per-block slice growth).  The leave/fuel
    refutations then live INSIDE those proofs, at the individual
    NEEDBITS / room / inner-fuel sites, where they are decidable.
    K2/K3 below are exactly that reshape: [zr_huff_exit_sel]'s good arm
    verbatim with the existentials premise-pinned.  K1 is the starve
    atom every site bottoms out on (no starve-side needbits lemma exists
    in-tree — only the NBOk side, ZReproQ6A.inf_nb_ok).  K5 is the
    stored dispatch's bare-leave kill (zr_stored_sound_plus arm 1).
    K4 is the loop plumbing that transports any residual arm-3 witness
    past a known crossing (completes Q6AsmSupport's compose/uniq pair;
    lets the block step absorb — not refute — a disjunctive supply).

    FUEL-ARM NOTE: in the good-only reshape no fuel arm reaches the
    consumer.  The InfFuel obligations move into K2/K3's proofs at the
    inner-decode sites (Inflate.v :1034/:1092/:1259-:1283/:1340/:1550/
    :1575); if any site's bound is not dischargeable from the band's
    br_wf + budget, the statement gains a premise and g1 sees a REPLACE
    (same protocol as the head's INPUT note).

    PROVER: q7's fork proves K1-K5 on ratification; K2/K3 re-run the
    landed _holds walks with the starve/room/fuel branches killed at
    their sites (the walks already construct the good arm under exactly
    these conditions).

    PA-EXPORTS: none (statements only).
    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A ZReproL0E.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Q6HuffResidue.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** ** K1 — the needbits starve atom (PROPOSED).

    The NBLeave twin of ZReproQ6A.inf_nb_ok: a starved pull certifies
    the stream is SHORT (fewer than [n] bits), is a stream no-op, and
    leaves the byte counter empty.  Consumed contrapositively at every
    leave site: declarative success on the entry stream bounds the
    stream length from below, so the machine cannot starve before the
    decoder is done.  [n <= 32] as in inf_nb_ok (NEEDBITS's C ceiling). *)
Definition ZrNbStarveShort_STMT : Prop :=
  forall n b b',
    br_wf b -> 0 <= n <= 32 ->
    inf_nb n b = NBLeave b' ->
    (length (br_stream b) < Z.to_nat n)%nat
    /\ br_stream b' = br_stream b
    /\ br_have b' = 0.

(** ** K2 — fixed leg, GOOD-ONLY selection (PROPOSED).

    Band verbatim ZrHuffFixedLegSel_STMT (Gap7LegSel :102-120); the
    exit shape's good arm verbatim with [syms]/[r3]/[out] hoisted to
    premise-pinned universals: availability = the leg's own declarative
    success on the ENTRY stream; room = the head's threading spelled at
    the leg ([zlen out <= q_out q], out slice-accumulated).  This is
    the shape g1's per-block step consumes with NO disjunction left to
    case on. *)
Definition ZrHuffFixedLegSelGood_STMT : Prop :=
  forall c q syms r3 out,
    zr_cflush_ok c ->
    br_wf (q_br q) ->
    W2Stream.br_haligned (q_br q) ->
    br_have (q_br q) + br_bits (q_br q) / 8 <= 4294967290 ->
    0 <= o_put (q_ob q) ->
    0 <= o_left (q_ob q) ->
    q_out q = o_put (q_ob q) + o_left (q_ob q) ->
    q_out q <= 4294967295 ->
    w_whave (s_win (q_st q)) = 0 ->
    t_sane (s_tab (q_st q)) <> 0 ->
    h_mode (s_hdr (q_st q)) = M_LEN_ ->
    t_lencode (s_tab (q_st q)) = TRlenfix ->
    t_lenbits (s_tab (q_st q)) = 9 ->
    t_distcode (s_tab (q_st q)) = TRdistfix ->
    t_distbits (s_tab (q_st q)) = 5 ->
    decode_symbols fixed_lit_lengths fixed_dist_lengths
      (br_stream (q_br q)) = Some (syms, r3) ->
    resolve_lz syms (ob_slice (q_ob q) 0 (o_put (q_ob q))) = Some out ->
    zlen out <= q_out q ->
    exists k q',
      inf_iter k c q = Some q'
      /\ br_stream (q_br q') = r3
      /\ br_wf (q_br q')
      /\ ob_slice (q_ob q') 0 (o_put (q_ob q')) = out
      /\ o_put (q_ob q') + o_left (q_ob q')
         = o_put (q_ob q) + o_left (q_ob q)
      /\ 0 <= o_put (q_ob q')
      /\ 0 <= o_left (q_ob q')
      /\ h_mode (s_hdr (q_st q')) = M_TYPE
      /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
      /\ zr_blk_frame q q'
      /\ W2Stream.br_haligned (q_br q')
      /\ br_have (q_br q') + br_bits (q_br q') / 8 <= 4294967290.

(** ** K3 — dyn leg, GOOD-ONLY selection (PROPOSED).

    Band verbatim ZrHuffDynLegSel_STMT (Gap7LegSel :125-142, incl. the
    STRICT header success and the code_for-256 carrier — the block-sel
    consumer derives the latter free from its own decode_symbols
    success via code_for_256_lens, per the head's note); availability/
    room premises as K2, on the POST-HEADER stream [r3]. *)
Definition ZrHuffDynLegSelGood_STMT : Prop :=
  forall c q (lit dst : list nat) (r3 : list bool) syms r4 out,
    zr_cflush_ok c ->
    br_wf (q_br q) ->
    W2Stream.br_haligned (q_br q) ->
    br_have (q_br q) + br_bits (q_br q) / 8 <= 4294967290 ->
    0 <= o_put (q_ob q) ->
    0 <= o_left (q_ob q) ->
    q_out q = o_put (q_ob q) + o_left (q_ob q) ->
    q_out q <= 4294967295 ->
    w_whave (s_win (q_st q)) = 0 ->
    t_sane (s_tab (q_st q)) <> 0 ->
    q_ret q = 0 ->
    h_mode (s_hdr (q_st q)) = M_TABLE ->
    decode_dynamic_tables_strict (br_stream (q_br q))
      = Some (lit, dst, r3) ->
    (exists cw, code_for lit 15%nat 256%nat = Some cw) ->
    decode_symbols lit dst r3 = Some (syms, r4) ->
    resolve_lz syms (ob_slice (q_ob q) 0 (o_put (q_ob q))) = Some out ->
    zlen out <= q_out q ->
    exists k q',
      inf_iter k c q = Some q'
      /\ br_stream (q_br q') = r4
      /\ br_wf (q_br q')
      /\ ob_slice (q_ob q') 0 (o_put (q_ob q')) = out
      /\ o_put (q_ob q') + o_left (q_ob q')
         = o_put (q_ob q) + o_left (q_ob q)
      /\ 0 <= o_put (q_ob q')
      /\ 0 <= o_left (q_ob q')
      /\ h_mode (s_hdr (q_st q')) = M_TYPE
      /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
      /\ zr_blk_frame q q'
      /\ W2Stream.br_haligned (q_br q')
      /\ br_have (q_br q') + br_bits (q_br q') / 8 <= 4294967290.

(** ** K4 — loop preemption (PROPOSED; completes the compose/uniq pair).

    An all-Cont crossing forces any inf_loop event PAST it and
    decomposes the event through it (converse direction of
    Q6AsmSupport.zr_iterloop_compose).  With this, a residual
    disjunctive supply's third arm is ABSORBED at the block step — its
    witness transports to the next block's entry, where the fuel
    induction's shorter stream takes over — rather than refuted (which
    the FINDING above shows impossible). *)
Definition ZrLoopPreempt_STMT : Prop :=
  forall k c q q',
    inf_iter k c q = Some q' ->
    (forall n, (n <= k)%nat -> inf_loop n c q = None)
    /\ (forall n s, inf_loop n c q = Some s ->
          (k < n)%nat /\ inf_loop (n - k) c q' = Some s).

(** ** K5 — stored dispatch leave-kill (REFUTED — LkStored.lk_k5_refuted, machine-checked; proven repair: LkStoredRoom.k5_stored_no_leave_room).

    Gap7Sib.zr_stored_sound_plus's first arm is a BARE starvation leave
    (no refutable content).  Under the block's own stored-header
    success it is dead: the aligned 32-bit read cannot starve (K1's
    contrapositive through br_bytebits), and no other inf_STORED arm
    leaves.  Spelled at the dispatch's single-step altitude so the
    block step consumes it right where the sound_plus disjunction
    lands. *)
Definition ZrStoredNoLeave_STMT : Prop :=
  forall c q,
    n_flush c <> Z_TREES ->
    br_wf (q_br q) ->
    decode_stored (br_stream (q_br q)) <> None ->
    forall q2, inf_STORED c q <> InfLeave q2.
