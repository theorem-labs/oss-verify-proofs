(* the zlib 1.4 twin of Q6HuffResidue, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from Q6HuffResidue), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * Q6HuffResidue — THE huffman-block residue: statement-only leaf.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20).
    PRODUCER: model-rt's stage-4 LEN-chain value walk.  CONSUMERS: both
    face assemblies (my raw walk, model-rt's zlib walk) cite these Props
    at their huffman-block trips — which is why this leaf holds
    STATEMENTS ONLY and lives inside neither assembly.

    Shape per model-rt's constraints (2026-08-20 msg): stated at the
    post-TYPEDO dispatch states (ZReproQ6C.zr_typedo_sound's ty=1 exit
    shape for the fixed leg, ty=2's M_TABLE for the dynamic leg);
    conclusion an absorbed-or-agreement disjunction in the leg style;
    premises the flush exclusion plus the dispatch-state shape only —
    reach-free, table-premise-free (keystone/transport/coverage
    consumption is internal to the stage-4 proof); no table-wide
    quantification anywhere.

    AMENDED at the producer's request (model-rt, TL
    cc'd; no proofs existed against the statements yet): (i) both legs
    take `0 <= o_left` and the agreement arm returns it — a stored trip
    after the block is unsound at negative o_left (inf_COPY's c2 clamp
    goes junk), and the generic reach-free per-step invariant is FALSE
    (the fast path rebuilds o_left from if_model, whose nonnegativity
    needs table facts) — so the fact can only travel inside the
    existential; (ii) zr_blk_frame carries h_wrap preservation (M_CHECK
    dispatches on wrap; the huffman trip is opaque behind this residue).

    AMENDED v3 (three-way: model-rt's MATCH-arm
    adversarial pass + an earlier development run's ret finding, both q6-fixedtbl-verified
    at the source): both legs gain FOUR premises the MATCH arm needs —
    the OUTPUT ANCHOR TIE `q_out q = o_put + o_left` (inf_MATCH picks the
    direct-copy source by `outd = u32 (q_out - o_left)` vs offset; a
    decoupled q_out admits reads at negative output indices), the cap
    `q_out q <= 2^32-1` (the u32 collapse), `w_whave = 0` (a window-read
    match copies bytes resolve_lz cannot see; the one-shot vacuity
    insight as an explicit premise), and `t_sane <> 0` (the far-match
    guard falls THROUGH into the window read at sane = 0 — Inflate.v's
    own dead-branch comment).  zr_blk_frame carries whave/sane
    preservation so the walk re-supplies them per trip (writer census:
    set_whave only in updatewindow/reset, set_sane only in
    inflateResetKeep — all outside the step loop).  ZrHuffDynLeg
    additionally gains `q_ret q = 0` (an earlier development run: the dynamic chain
    WRITES ret mid-chain — inf_LENLENS's qset_ret rc, inf_CODELENS's
    rl/rd, each 0 on surviving paths — so post-build starvation leaves
    carry the WRITTEN ret; the premise makes the EXIT arm's
    ret-preservation clause dischargeable; the fixed chain has no
    qset_ret and stays without it).

    AMENDED v4 (amendment #10, three-way frozen text:
    q6-fixedtbl INBOX-1159 + q7-decode fit-check CONFIRMED + model-rt
    GO): both legs gain TWO reader premises immediately after br_wf —
    `W2Stream.br_haligned (q_br q)` (the fast path (inflate_fast)
    re-reads whole bytes THROUGH the hold via the if_* view; without
    hold/input agreement at byte offsets the fast leg's if_model
    correspondence is unprovable — q7's countermodel: junk hold bits
    passing every carried clause) and the compositional input budget
    `br_have + br_bits/8 <= 4294967290` (the fast loop's avail_in u32
    arithmetic; the SUM is the form the walk can thread — it survives
    the R9 hold give-back, and it bridges to the fast leg's flat
    `br_have <= 4294967290` by one lia at the Q6S seam, which q7 owns).
    The agreement arm RETURNS both at q', appended LAST after
    zr_blk_frame (R28 destruct-arity: consumers extend patterns at the
    tail only).  BAD/EXIT arms unchanged — both are run-absorbed, no
    reader state escapes them.

    The three exit arms:
    - AGREEMENT: [k] continuing steps end the block at [M_TYPE], and the
      block's effect IS [dec_blk]'s huffman arm on the same stream — the
      symbol read ([decode_symbols] over the entry stream) and the
      output extension ([resolve_lz] over the entry slice) both equal
      the machine's exit state.
    - BAD: the iterate reaches [M_BAD] (invalid code/distance paths) —
      absorbed by the run-level success premise.
    - EXIT: the loop stops on a non-continue step.  Strengthened per
      model-rt's producibility check (2026-08-20): a leave carries
      ret-preservation (the leave-vacuity argument needs the terminal's
      verdict path; every mid-block starvation leave is [InfLeave
      (qset_br q b)], ret untouched, so the clause is reflexivity-cheap);
      [InfCont] is impossible in [inf_loop]'s [Some] by construction;
      [InfRet]'s only producer is [inf_DICT] (unreachable here); [InfDead]
      has no producer — the [False] arms hand the consumer dead cases
      outright.  [InfFuel] (model declined) is absorbed by the run
      returning [None]; [True] arm added because [InfStep] has five
      constructors and the match must be exhaustive.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A ZReproL0E.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Q6HuffResidue.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The bookkeeping a huffman block must not touch (the Q6B frame minus
    the output buffer, which the block legitimately extends). *)

(** The shared exit shape: from dispatch state [q], the block ends at
    [q'] agreeing with [decode_symbols ll dl] on stream [s0] (the
    dec-side entry stream for THIS leg) and [resolve_lz] on the entry
    output slice.  v4: the agreement arm returns the reader alignment
    and the compositional budget at [q'], appended last. *)
Definition zr_huff_exit14 (c : InfCtx) (q : InfSt)
           (ll dl : list nat) (s0 : list bool) : Prop :=
  (exists k q' syms r3,
      inf_iter14 k c q = Some q'
      /\ decode_symbols ll dl s0 = Some (syms, r3)
      /\ br_stream (q_br q') = r3
      /\ br_wf (q_br q')
      /\ resolve_lz syms (ob_slice (q_ob q) 0 (o_put (q_ob q)))
         = Some (ob_slice (q_ob q') 0 (o_put (q_ob q')))
      /\ o_put (q_ob q') + o_left (q_ob q')
         = o_put (q_ob q) + o_left (q_ob q)
      /\ 0 <= o_put (q_ob q')
      /\ 0 <= o_left (q_ob q')
      /\ h_mode (s_hdr (q_st q')) = M_TYPE
      /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
      /\ zr_blk_frame q q'
      /\ W2Stream.br_haligned (q_br q')
      /\ br_have (q_br q') + br_bits (q_br q') / 8 <= 4294967290)
  \/ (exists k q',
      inf_iter14 k c q = Some q'
      /\ h_mode (s_hdr (q_st q')) = M_BAD)
  \/ (exists n s,
      inf_loop14 n c q = Some s
      /\ match s with
         | InfLeave q2 => q_ret q2 = q_ret q
         | InfCont _ => False
         | InfRet _ _ => False
         | InfDead _ => False
         | InfFuel => True
         end).

(** THE fixed-block residue: from zr_typedo_sound's ty=1 exit shape, the
    block agrees with dec_blk's btype-1 arm ([decode_symbols] at the
    fixed lengths on the post-header stream). *)
Definition ZrHuffFixedLeg14 : Prop :=
  forall c q,
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
    zr_huff_exit14 c q fixed_lit_lengths fixed_dist_lengths
                 (br_stream (q_br q)).

(** THE dynamic-block residue: from ty=2's M_TABLE, the header build
    agrees with [decode_dynamic_tables] and the chain with
    [decode_symbols] at the decoded lengths — dec_blk's btype-2 arm. *)
Definition ZrHuffDynLeg14 : Prop :=
  forall c q,
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
    (exists lit dst r3,
        decode_dynamic_tables (br_stream (q_br q)) = Some (lit, dst, r3)
        /\ zr_huff_exit14 c q lit dst r3)
    \/ (exists k q',
        inf_iter14 k c q = Some q'
        /\ h_mode (s_hdr (q_st q')) = M_BAD)
    \/ (exists n s,
        inf_loop14 n c q = Some s
        /\ match s with
           | InfLeave q2 => q_ret q2 = q_ret q
           | InfCont _ => False
           | InfRet _ _ => False
           | InfDead _ => False
           | InfFuel => True
           end).
