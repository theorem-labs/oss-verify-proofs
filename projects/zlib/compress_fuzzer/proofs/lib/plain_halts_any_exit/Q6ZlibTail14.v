(* the zlib 1.4 twin of Q6ZlibTail, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from Q6ZlibTail), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * Q6ZlibTail — the zlib trailer tail: M_TYPE -> InfLeave, all exits.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20; trilogy).
    The wrap-5/flags-0 sibling of Q6GzipTail (and of model-rt's arm-level
    ZReproQ6E.zr_check_tail, which lacks the M_DONE/wsize exports the
    FINISH-leave lemma consumes — hence this composed form in my file
    rather than an amendment to theirs).  At flags = 0 the LENGTH guard
    falls through, so the pass path is CHECK-read + adler compare ->
    DONE: ONE 32-bit read, one absorbed mismatch.  Value-free as always:
    dec_stream discarded the trailer before it.

    AMENDED v3 (q6-tailv3, 2026-08-20): both lemmas take [br_wf (q_br q)]
    (right after the flags premise) and the Z_STREAM_END arm exports
    [(32 <= length (br_stream (q_br q)))%nat] — the trailer-unconsumed
    WITNESS the assemblies' dec-split needs: [zr_dec_split] may discard
    the adler suffix only if the walk-exit stream still carries its 32
    bits, and the pass arm's successful [inf_nb 32] read is exactly the
    evidence (via [inf_nb_ok] + [br_stream_length], both wf-gated; the
    composed tail lifts the floor through BYTEBITS with
    [br_wf_dropbits], since [bits & 7] is in [0, bits]).  The [br_wf]
    premise is REQUIRED, not decorative: without it [br_pullbyte]
    succeeds on negative [br_have], so the pass path can fire from a
    zero-length stream and the length clause would be false.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproL0E ZReproQ6C.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Q6ZlibTail.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.


(** The composed tail from the body walk's exit. *)
Lemma zr_zl_tail14 : forall c q,
  zr_cflush_ok c ->
  h_wrap (s_hdr (q_st q)) = 5 ->
  h_flags (s_hdr (q_st q)) = 0 ->
  br_wf (q_br q) ->
  h_mode (s_hdr (q_st q)) = M_TYPE ->
  h_last (s_hdr (q_st q)) <> 0 ->
  (exists n q'', inf_loop14 n c q = Some (InfLeave q'')
     /\ q_ret q'' = q_ret q)
  \/ (exists n q'', inf_loop14 n c q = Some (InfLeave q'')
     /\ q_ret q'' = Z_DATA_ERROR)
  \/ (exists n q'', inf_loop14 n c q = Some (InfLeave q'')
     /\ q_ret q'' = Z_STREAM_END
     /\ ob_slice (q_ob q'') 0 (o_put (q_ob q''))
        = ob_slice (q_ob q) 0 (o_put (q_ob q))
     /\ h_mode (s_hdr (q_st q'')) = M_DONE
     /\ w_wsize (s_win (q_st q'')) = w_wsize (s_win (q_st q))
     /\ (32 <= length (br_stream (q_br q)))%nat).
Proof.
  intros c q Hfl Hw Hf Hwf Hmode Hlast.
  set (q1 := qmode (qset_br q (br_bytebits (q_br q))) M_CHECK).
  assert (S1 : inf_step14 c q = InfCont q1).
  { unfold inf_step14, q_mode. rewrite Hmode.
    unfold inf_TYPE.
    rewrite (zr_eqb_nB c Hfl), (zr_eqb_nT c Hfl). cbn [orb].
    unfold inf_TYPEDO. cbv zeta.
    rewrite (proj2 (Z.eqb_neq _ _) Hlast). reflexivity. }
  assert (Hw1 : h_wrap (s_hdr (q_st q1)) = 5) by exact Hw.
  assert (Hf1 : h_flags (s_hdr (q_st q1)) = 0) by exact Hf.
  assert (Hm1 : h_mode (s_hdr (q_st q1)) = M_CHECK) by reflexivity.
  (* v3: BYTEBITS drops [bits & 7] in-window bits, keeping wf *)
  assert (Hk : 0 <= Z.land (br_bits (q_br q)) 7 <= br_bits (q_br q)).
  { destruct Hwf as (Hb & _).
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia.
    change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (br_bits (q_br q)) 8 ltac:(lia)).
    pose proof (Z.mod_le (br_bits (q_br q)) 8 ltac:(lia) ltac:(lia)).
    lia. }
  assert (Hwf1 : br_wf (q_br q1)).
  { change (q_br q1) with (br_bytebits (q_br q)).
    unfold br_bytebits.
    apply br_wf_dropbits; [exact Hwf | exact Hk]. }
  destruct (zr_zl_check_tail q1 Hw1 Hf1 Hwf1)
    as [ (q2 & E2 & R2) | [ (q2 & E2 & M2) | (q2 & E2 & R2 & OB2 & H) ] ].
  - left. exists 2%nat, q2. split.
    + cbn [inf_loop14]. rewrite S1. cbv iota.
      unfold inf_step14, q_mode. rewrite Hm1.
      rewrite E2. reflexivity.
    + rewrite R2. reflexivity.
  - right; left. exists 3%nat, (qset_ret q2 Z_DATA_ERROR). split.
    + cbn [inf_loop14]. rewrite S1. cbv iota.
      unfold inf_step14, q_mode. rewrite Hm1.
      rewrite E2. cbv iota.
      rewrite M2.
      unfold inf_BAD. reflexivity.
    + reflexivity.
  - destruct H as (M2 & W2 & L2).
    right; right. exists 2%nat, q2. split.
    + cbn [inf_loop14]. rewrite S1. cbv iota.
      unfold inf_step14, q_mode. rewrite Hm1.
      rewrite E2. reflexivity.
    + split; [exact R2|].
      split; [rewrite OB2; reflexivity|].
      split; [exact M2|].
      split; [rewrite W2; reflexivity|].
      (* v3: the floor at q1 lifts to the entry through BYTEBITS *)
      pose proof (br_stream_length (q_br q) Hwf) as HL0.
      pose proof (br_stream_length (q_br q1) Hwf1) as HL1.
      assert (HB : br_bits (q_br q1)
                   = br_bits (q_br q) - Z.land (br_bits (q_br q)) 7)
        by reflexivity.
      assert (HH : br_have (q_br q1) = br_have (q_br q)) by reflexivity.
      lia.
Qed.

