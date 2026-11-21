(** * G3Stored — the STORED arm of one emitted block, at ANY bit position.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G3.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    [StoredRt.tr_stored_block_stream] pins the emitter's delta (3 header
    bits, the windup pad, LEN/NLEN, the raw bytes) and
    [StoredRt.decode_stored_tail] inverts the tail; this file closes the
    loop through [dec_blk]'s BTYPE-0 arm, generalising ZReproL0D's
    level-0 version to an arbitrary starting pad (mid-stream stored
    blocks start wherever the previous block left the bit cursor).

    The two byte-parity facts a consumer chains on:
      * the suffix must be byte-parity 0 (the decoder computes the
        alignment pad from the REMAINING length, which agrees with the
        emitter's absolute pad exactly when the total is whole bytes);
      * after this block the writer IS byte-aligned (valid = 0), so the
        next block's suffix parity obligation discharges. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
(* GAP7 strict twin (freeze r3): [dec_blk_strict]'s stored arm is the lax
   text verbatim, so the same computation proves both. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream DeflateSpec Trees StoredRt.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Gap7Strict.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** [map u8] is the identity on a byte list. *)
Lemma map_u8_id : forall dat,
  Forall (fun b => 0 <= b < 256) dat -> map u8 dat = dat.
Proof.
  intros dat H. induction H as [|x l Hx Hl IH]; [reflexivity|].
  cbn [map]. rewrite u8_id by exact Hx. now rewrite IH.
Qed.

Theorem tr_stored_block_dec_blk : forall dat stored_len last s,
  bw_wf (ts_bw s) ->
  last = 0 \/ last = 1 ->
  stored_len = zlen dat ->
  0 <= stored_len < 65536 ->
  Forall (fun b => 0 <= b < 256) dat ->
  exists delta,
    bw_stream (ts_bw (tr_stored_block dat stored_len last s))
      = bw_stream (ts_bw s) ++ delta
    /\ bw_wf (ts_bw (tr_stored_block dat stored_len last s))
    /\ bw_valid (ts_bw (tr_stored_block dat stored_len last s)) = 0
    /\ (length (bw_stream (ts_bw (tr_stored_block dat stored_len last s)))
        mod 8 = 0)%nat
    /\ (forall tail acc, (length tail mod 8 = 0)%nat ->
         dec_blk (delta ++ tail) acc
         = Some (Z.eqb last 1, acc ++ dat, tail))
    /\ (forall tail acc, (length tail mod 8 = 0)%nat ->
         Gap7Strict.dec_blk_strict (delta ++ tail) acc
         = Some (Z.eqb last 1, acc ++ dat, tail)).
Proof.
  intros dat stored_len last s Hwf Hl Hlen Hr Hb.
  destruct (tr_stored_block_stream dat stored_len last s Hwf
              ltac:(lia) Hr) as (pad & Hpad & Hs).
  exists (zwrite 3 (Z.shiftl STORED_BLOCK 1 + last)
          ++ stored_tail dat stored_len pad).
  split; [exact Hs|].
  (* the post-block writer: register empty, queue whole bytes *)
  assert (Hval : bw_valid (ts_bw (tr_stored_block dat stored_len last s)) = 0
                 /\ bw_buf (ts_bw (tr_stored_block dat stored_len last s)) = 0).
  { unfold tr_stored_block, set_bw. cbv zeta. cbn [ts_bw].
    destruct (bw_windup_empty
                (bw_send_bits (Z.shiftl STORED_BLOCK 1 + last) 3 (ts_bw s)))
      as [Hbuf1 Hval1].
    unfold bw_put_short, bw_put_byte.
    cbn [bw_valid bw_buf].
    split; assumption. }
  destruct Hval as [Hval Hbuf].
  split.
  { unfold bw_wf. rewrite Hval, Hbuf.
    split; [unfold Buf_size; lia | cbn; lia]. }
  split; [exact Hval|].
  split.
  { unfold bw_stream. rewrite Hval, zwrite_0, app_nil_r.
    rewrite bytes_bits_length, Nat.mul_comm.
    apply Nat.Div0.mod_mul. }
  split.
  {   intros tail acc Ht.
    assert (Hlen' : stored_len = Z.of_nat (length dat))
      by (rewrite Hlen; reflexivity).
    pose proof (decode_stored_tail dat stored_len pad tail Hlen' Hr Hpad Ht)
      as DS.
    rewrite <- app_assoc.
    assert (R1 : forall b (rest : list bool),
      read_bits 1%nat ([b; false; false] ++ rest)
      = Some (if b then 1 else 0, [false; false] ++ rest))
      by (intros [|] rest; reflexivity).
    assert (R2 : forall rest : list bool,
      read_bits 2%nat ([false; false] ++ rest) = Some (0, rest))
      by reflexivity.
    destruct Hl; subst last; unfold dec_blk.
    - change (zwrite 3 (Z.shiftl STORED_BLOCK 1 + 0))
        with [false; false; false].
      rewrite (R1 false). cbv beta iota zeta.
      rewrite R2. cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite DS. cbv beta iota.
      now rewrite (map_u8_id dat Hb).
    - change (zwrite 3 (Z.shiftl STORED_BLOCK 1 + 1))
        with [true; false; false].
      rewrite (R1 true). cbv beta iota zeta.
      rewrite R2. cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite DS. cbv beta iota.
      now rewrite (map_u8_id dat Hb). }
  {   intros tail acc Ht.
    assert (Hlen' : stored_len = Z.of_nat (length dat))
      by (rewrite Hlen; reflexivity).
    pose proof (decode_stored_tail dat stored_len pad tail Hlen' Hr Hpad Ht)
      as DS.
    rewrite <- app_assoc.
    assert (R1 : forall b (rest : list bool),
      read_bits 1%nat ([b; false; false] ++ rest)
      = Some (if b then 1 else 0, [false; false] ++ rest))
      by (intros [|] rest; reflexivity).
    assert (R2 : forall rest : list bool,
      read_bits 2%nat ([false; false] ++ rest) = Some (0, rest))
      by reflexivity.
    destruct Hl; subst last; unfold Gap7Strict.dec_blk_strict.
    - change (zwrite 3 (Z.shiftl STORED_BLOCK 1 + 0))
        with [false; false; false].
      rewrite (R1 false). cbv beta iota zeta.
      rewrite R2. cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite DS. cbv beta iota.
      now rewrite (map_u8_id dat Hb).
    - change (zwrite 3 (Z.shiftl STORED_BLOCK 1 + 1))
        with [true; false; false].
      rewrite (R1 true). cbv beta iota zeta.
      rewrite R2. cbv beta iota zeta.
      cbn [Z.eqb].
      rewrite DS. cbv beta iota.
      now rewrite (map_u8_id dat Hb). }
Qed.

Print Assumptions tr_stored_block_dec_blk.
