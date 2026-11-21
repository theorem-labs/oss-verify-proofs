(** * Gap7BodySel — ladder (b): the block walk in selection form,
    STATEMENT ONLY (the (viii) pre-proof stage; q7 pass + division-of-
    labor ruling requested against this text).

    OWNER: an earlier development run.

    SHAPE: the FUELED form of the frozen ZrBodySelect head (GtBodySelect
    ) — same premise band, same GOOD-ARM-ONLY conclusion, plus
    the fuel bound that drives the per-block induction.  The head's own
    header declares the starvation-leave refutation PROOF CONTENT ("the
    pump's single Z_FINISH call hands the machine the whole encoded
    stream"), so the induction core must be good-only too: each block
    step refutes the leg exit shapes' BAD arms from the strict block
    equations (dec_blk_strict's per-arm successes) and their leave/fuel
    arms from the accounting corpus (input availability under br_wf;
    output room threaded from zlen X <= q_out through the per-block
    slice growth).

    CONSUMES at proof time (the per-block step): Gap7Sib's
    zr_typedo_sound_plus dispatch + zr_stored_sound_plus (stored arm),
    zr_huff_fixed_leg_sel_holds (Gap7FixAsm bed), and
    zr_huff_dyn_leg_sel_holds (DynLegSel bed; its code_for-256 premise
    from the block's own decode_symbols success via code_for_256_lens),
    plus q7's exit-path/accounting instruments for the leave arms —
    names and homes to be pinned by their pass.

    (c) then instantiates at fuel S (length stream): ZrBodySelect =
    this at n := S (length (br_stream (q_br q))), and Head0 rides the
    same core after the M_HEAD wrap-0 entry steps.

    PA-EXPORTS: none (statement only).
    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsIn Inflate DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro ZReproL0E ZReproQ6A ZReproQ6W W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Definition ZrBodySelectFuel_STMT : Prop :=
  forall n c q X rem,
    zr_cflush_ok c ->
    (length (br_stream (q_br q)) < n)%nat ->
    zr_body_entry q ->
    h_mode (s_hdr (q_st q)) = M_TYPE ->
    dec_stream_from_strict (br_stream (q_br q))
      (ob_slice (q_ob q) 0 (o_put (q_ob q))) = Some (X, rem) ->
    zlen X <= q_out q ->
    exists k q',
      inf_iter k c q = Some q'
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
      /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
      /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q)).
