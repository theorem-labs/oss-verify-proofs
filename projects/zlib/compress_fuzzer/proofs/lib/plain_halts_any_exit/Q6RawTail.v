(** * Q6RawTail — the raw final-block tail: M_TYPE -> InfLeave STREAM_END.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20).  Consumes
    the body walk's final-block exit (an abstract state at [M_TYPE] with
    [h_last <> 0], the block byte-aligned) and runs the raw tail to the
    terminal leave.  BODY-WALK-INDEPENDENT: it takes only the mode/last/
    wrap facts, so it is stable whatever shape model-rt's stage-3 exit
    clauses settle to.

    Chain (all flush-agnostic at wrap 0): [inf_TYPE] -> (non-BLOCK/TREES)
    [inf_TYPEDO] at [h_last<>0] byte-aligns to [M_CHECK]
    ([Inflate.v:829-833]); [inf_CHECK] at wrap 0 falls to [inf_LENGTH]
    (zr_raw_check) whose wrap-0 guard falls to [inf_DONE] (zr_raw_length),
    which leaves with [Z_STREAM_END].  Two [inf_step]s; the output slice
    is untouched throughout (no arm writes [q_ob]).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproL0E Q6RawShims.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma zr_raw_tail : forall c q,
  zr_cflush_ok c ->
  h_wrap (s_hdr (q_st q)) = 0 ->
  h_mode (s_hdr (q_st q)) = M_TYPE ->
  h_last (s_hdr (q_st q)) <> 0 ->
  exists q',
    inf_loop 2 c q = Some (InfLeave q')
    /\ q_ret q' = Z_STREAM_END
    /\ ob_slice (q_ob q') 0 (o_put (q_ob q'))
       = ob_slice (q_ob q) 0 (o_put (q_ob q))
    /\ h_mode (s_hdr (q_st q')) = M_DONE
    /\ w_wsize (s_win (q_st q')) = w_wsize (s_win (q_st q)).
Proof.
  intros c q Hfl Hwrap Hmode Hlast.
  (* step 1: M_TYPE -> inf_TYPE -> inf_TYPEDO -> InfCont q1 at M_CHECK *)
  cbn [inf_loop].
  unfold inf_step, q_mode. rewrite Hmode.
  unfold inf_TYPE.
  rewrite (zr_eqb_nB c Hfl), (zr_eqb_nT c Hfl). cbn [orb].
  unfold inf_TYPEDO.
  rewrite (proj2 (Z.eqb_neq _ _) Hlast). cbn [negb].
  (* now inf_loop 1 over q1 *)
  cbn [inf_loop].
  set (q1 := qmode (qset_br q (br_bytebits (q_br q))) M_CHECK).
  assert (Hm1 : h_mode (s_hdr (q_st q1)) = M_CHECK) by reflexivity.
  assert (Hw1 : h_wrap (s_hdr (q_st q1)) = 0)
    by (unfold q1; cbn [q_st qmode qset_st qset_br set_mode s_hdr]; exact Hwrap).
  unfold inf_step, q_mode. rewrite Hm1.
  rewrite (zr_raw_check q1 Hw1).
  rewrite (zr_raw_length (qmode q1 M_LENGTH)
             ltac:(unfold qmode; cbn [q_st qset_st set_mode s_hdr]; exact Hw1)).
  unfold inf_DONE.
  eexists. split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; reflexivity.
Qed.

Print Assumptions zr_raw_tail.
