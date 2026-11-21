(* the zlib 1.4 twin of Q6TailPos, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from Q6TailPos), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * Q6TailPos — the POSITIVE tails: STREAM_END-arm selections (GAP7 F5).

    OWNER: q6-fixedtbl (2026-08-21).  Proves the wrapper hypotheses
    Hzltail / Hgztail at the ratified spellings AS AMENDED by my
    o_put = 0 finding (to q7-decode): each tail
    takes ONE added premise — the running check is a fixed point of the
    empty update — because inf_CHECK skips the update at wrote = 0 and
    compares the RAW h_check, while the check premise pins its
    nil-image.  The two nil-fixed-point DISCHARGE lemmas are exported
    here (adler under AdVal; crc under the word range) so the pump
    consumes them by name.

    The discriminating structure: the stream pinned to padding ++
    trailer, the value equations in the machine's spelling, and THE TIE
    (q_out = o_put + o_left) — which pins the machine's M_CHECK update
    span to the WHOLE output slice, making the value equations
    state-general (do not simplify it away).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn ZBitsBridge Checksum ChecksumThy
  InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro ZReproQ6A ZReproL0C ZReproL0E ZReproQ6C GtAdlerChunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Q6TailPos.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   0.  Byte ranges.
   ========================================================================== *)



(* ==========================================================================
   1.  The aligned pull: a byte-aligned reader holding at least 32 bits
       of stream reaches bits = 32 exactly, preserving stream and wf.
       (Alignment is FREE at both call sites: availability 32 or 64
       forces bits = 8k.)
   ========================================================================== *)



(* ==========================================================================
   2.  Stream algebra: four bytes as one 32-bit write; the pinned hold.
   ========================================================================== *)




(** The wrapper's [br_stream] (ZReproQ6A) and the bridge's are the same
    function by delta; the bridge's [skipn] lemmas transport across. *)

(** A reader parked at bits = 32 whose stream opens with a pinned
    32-bit write holds exactly that value. *)

(** LE recomposition: [zr_le32]'s bytes reassemble to the value. *)

(* ==========================================================================
   3.  The nil-fixed-point discharge lemmas (the amendment's premises).
   ========================================================================== *)

(** A canonical adler value is a fixed point of the empty update. *)

(** A word-ranged crc value is a fixed point of the empty update. *)

(* ==========================================================================
   4.  initbits: wf and stream shape.
   ========================================================================== *)



(* ==========================================================================
   5.  The positive zlib CHECK arm.
   ========================================================================== *)


(* ==========================================================================
   6.  The composed zlib positive tail — Hzltail's ratified spelling,
       AMENDED (the one added fixed-point premise, last).
   ========================================================================== *)

Lemma zr_zl_tail_pos14 : forall q remb AD,
  h_wrap (s_hdr (q_st q)) = 5 ->
  h_flags (s_hdr (q_st q)) = 0 ->
  h_mode (s_hdr (q_st q)) = M_TYPE ->
  h_last (s_hdr (q_st q)) <> 0 ->
  br_wf (q_br q) ->
  W2Stream.br_haligned (q_br q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  br_stream (q_br q) = remb ++ bytes_bits (be32 AD) ->
  (length remb < 8)%nat ->
  0 <= AD < 4294967296 ->
  upd_check (h_flags (s_hdr (q_st q))) (h_check (s_hdr (q_st q)))
            (ob_slice (q_ob q) 0 (o_put (q_ob q))) = AD ->
  upd_check (h_flags (s_hdr (q_st q))) (h_check (s_hdr (q_st q))) []
    = h_check (s_hdr (q_st q)) ->
  exists n q'',
    inf_loop14 n zr_ic q = Some (InfLeave q'')
    /\ q_ret q'' = Z_STREAM_END
    /\ h_mode (s_hdr (q_st q'')) = M_DONE
    /\ w_wsize (s_win (q_st q'')) = w_wsize (s_win (q_st q)).
Proof.
  intros q remb AD Hw Hf Hmode Hlast Hwf Hal Htie Hpin Hremb HAD Hval Hfix.
  assert (Hfl : zr_cflush_ok zr_ic).
  { unfold zr_cflush_ok, zr_ic. cbn [n_flush].
    unfold Z_FINISH, Z_BLOCK, Z_TREES. split; lia. }
  set (q1 := qmode (qset_br q (br_bytebits (q_br q))) M_CHECK).
  assert (S1 : inf_step14 zr_ic q = InfCont q1).
  { unfold inf_step14, q_mode. rewrite Hmode.
    unfold inf_TYPE.
    rewrite (zr_eqb_nB zr_ic Hfl), (zr_eqb_nT zr_ic Hfl). cbn [orb].
    unfold inf_TYPEDO. cbv zeta.
    rewrite (proj2 (Z.eqb_neq _ _) Hlast). reflexivity. }
  assert (Hm1 : h_mode (s_hdr (q_st q1)) = M_CHECK) by reflexivity.
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
  (* transport: the drop is exactly the padding *)
  pose proof (br_stream_length (q_br q) Hwf) as HL0.
  assert (HLtr : length (bytes_bits (be32 AD)) = 32%nat).
  { unfold be32. rewrite bytes4_write32 by apply u8_range.
    apply write_bits_length. }
  assert (HLr : Z.of_nat (length remb) = Z.land (br_bits (q_br q)) 7).
  { rewrite Hpin, length_app, HLtr, Nat2Z.inj_add in HL0.
    change (Z.of_nat 32%nat) with 32 in HL0.
    replace (Z.land (br_bits (q_br q)) 7) with (br_bits (q_br q) mod 8)
      by (replace 7 with (Z.ones 3) by reflexivity;
          rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z_div_mod_eq_full (br_bits (q_br q)) 8).
    pose proof (Z.mod_pos_bound (br_bits (q_br q)) 8 ltac:(lia)).
    lia. }
  assert (Hpin1 : br_stream (q_br q1) = bytes_bits (be32 AD)).
  { change (q_br q1) with (br_bytebits (q_br q)).
    rewrite br_stream_agree, (br_stream_bytebits _ Hwf),
            <- br_stream_agree, Hpin.
    replace (Z.to_nat (Z.land (br_bits (q_br q)) 7)) with (length remb)
      by (rewrite <- HLr, Nat2Z.id; reflexivity).
    rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (Hav1 : br_bits (q_br q1) + 8 * br_have (q_br q1) = 32).
  { pose proof (br_stream_length (q_br q1) Hwf1) as HL1.
    rewrite Hpin1, HLtr in HL1.
    change (Z.of_nat 32%nat) with 32 in HL1. lia. }
  destruct (zr_zl_check_pos q1 AD Hw Hf Hwf1 Hav1 Hpin1 HAD Htie Hval Hfix)
    as (q2 & E2 & R2 & M2 & W2).
  exists 2%nat, q2. split.
  - cbn [inf_loop14]. rewrite S1. cbv iota.
    unfold inf_step14, q_mode. rewrite Hm1.
    rewrite E2. reflexivity.
  - split; [exact R2|].
    split; [exact M2|].
    rewrite W2. reflexivity.
Qed.

(* ==========================================================================
   7.  The positive gzip CHECK arm (flags = 8: raw-hold crc compare,
       then the ACTIVE LENGTH arm reads ISIZE from the drained bytes).
   ========================================================================== *)


(* ==========================================================================
   8.  The composed gzip positive tail — Hgztail's ratified spelling,
       AMENDED (the one added fixed-point premise, after the crc one).
   ========================================================================== *)


