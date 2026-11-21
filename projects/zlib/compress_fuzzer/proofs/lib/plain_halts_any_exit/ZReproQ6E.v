(** * ZReproQ6E — Q6 leg (e): the trailer tail (CHECK -> LENGTH -> DONE).

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-19).  After the
    final block, the declarative decoder has already RETURNED — the
    remainder ([pad ++ trailer]) is discarded by [dec_stream].  So the
    tail arms owe the walk exactly two facts: they never touch the output
    buffer (the answer is whatever the blocks accumulated), and the only
    non-absorbed exit is [InfLeave] with [q_ret = Z_STREAM_END] — which
    [ZReproL0E.zr_leave_shape] then turns into the call's return code.
    At a zlib stream ([wrap = 5], [flags = 0]) the whole chain
    CHECK-pass -> LENGTH-fallthrough -> DONE is one composite step.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma zr_check_tail : forall q,
  h_wrap (s_hdr (q_st q)) = 5 ->
  h_flags (s_hdr (q_st q)) = 0 ->
  (exists b, inf_CHECK q = InfLeave (qset_br q b))               (* starved *)
  \/ (exists q'', inf_CHECK q = InfCont q''
        /\ h_mode (s_hdr (q_st q'')) = M_BAD)             (* check mismatch *)
  \/ (exists q'', inf_CHECK q = InfLeave q''
        /\ q_ret q'' = Z_STREAM_END
        /\ o_buf (q_ob q'') = o_buf (q_ob q)
        /\ o_put (q_ob q'') = o_put (q_ob q)).
Proof.
  intros q Hw Hf.
  unfold inf_CHECK. cbv zeta.
  rewrite Hw.
  change (5 =? 0) with false. cbv beta iota.
  destruct (inf_nb 32 (q_br q)) as [b|b] eqn:EN;
    [| left; eexists; reflexivity].
  (* the adler-fold branch: both arms preserve hdr fields and the output
     buffer; destruct it so conversion can cross *)
  match goal with |- context [if ?t then qcheck _ _ else _] =>
    destruct t eqn:EFOLD end.
  all: match goal with |- context [if ?t then InfCont _ else _] =>
         destruct t eqn:EMISS end.
  all: try (right; left; eexists; split; reflexivity).
  (* the two pass branches: LENGTH falls through (flags = 0) into DONE *)
  all: right; right.
  all: unfold inf_LENGTH; cbv zeta.
  all: match goal with |- context [if negb (?w =? 0) && negb (?f =? 0)
                                   then _ else _] =>
         replace w with (h_wrap (s_hdr (q_st q))) by reflexivity;
         replace f with (h_flags (s_hdr (q_st q))) by reflexivity end.
  all: rewrite Hw, Hf.
  all: change (negb (5 =? 0) && negb (0 =? 0)) with false.
  all: cbv beta iota.
  all: unfold inf_DONE.
  all: eexists; split; [reflexivity|].
  all: split; [reflexivity|].
  all: split; reflexivity.
Qed.

Print Assumptions zr_check_tail.
