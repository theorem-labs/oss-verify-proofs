(** * ZReproG6B — G6 bound-fit, part B: the stored arm fits.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-19).

    [tr_stored_block]'s exact bit cost, and the amortized corollary the
    per-event step consumes: in [ceil8] potential, one stored block costs
    at most [8*stored_len + 40] bits — 3-bit header (+ pad to the byte
    ceiling, absorbed as at most one extra byte over the potential),
    LEN/NLEN (32 bits), and the bytes themselves.  The emitted stream is
    byte-ALIGNED afterwards, so the potential is exact there — which is
    why consecutive stored blocks pay 40, not 42.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 ZReproG6A.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The exact cost equation.  No value premises (see ZReproG6A's header);
    the [map u8 dat] append is counted through its length only. *)
Theorem tr_stored_block_len : forall dat stored_len last s,
  bwv (ts_bw s) ->
  zbits (ts_bw (tr_stored_block dat stored_len last s))
    = ceil8 (zbits (ts_bw s) + 3) + 32 + 8 * zlen dat
  /\ bw_valid (ts_bw (tr_stored_block dat stored_len last s)) = 0
  /\ bwv (ts_bw (tr_stored_block dat stored_len last s)).
Proof.
  intros dat stored_len last s Hb.
  unfold tr_stored_block. cbv zeta.
  rewrite ts_bw_set_bw.
  set (b0 := bw_send_bits (Z.shiftl STORED_BLOCK 1 + last) 3 (ts_bw s)).
  destruct (zbits_send_bits (Z.shiftl STORED_BLOCK 1 + last) 3 (ts_bw s)
              Hb ltac:(unfold Buf_size; lia)) as [Z0 V0].
  fold b0 in Z0, V0.
  destruct (zbits_windup b0 V0) as (Z1 & E1 & V1 & _).
  set (b1 := bw_windup b0) in *.
  destruct (zbits_put_short stored_len b1 ltac:(lia)) as [Z2 E2].
  set (b2 := bw_put_short stored_len b1) in *.
  destruct (zbits_put_short (u16 (- stored_len - 1)) b2 ltac:(lia)) as [Z3 E3].
  set (b3 := bw_put_short (u16 (- stored_len - 1)) b2) in *.
  assert (V3 : 0 <= bw_valid b3) by lia.
  assert (Z4 : zbits {| bw_out := bw_out b3 ++ map u8 dat;
                        bw_buf := bw_buf b3; bw_valid := bw_valid b3 |}
               = zbits b3 + 8 * zlen dat).
  { rewrite zbits_eqn by (cbn [bw_valid]; lia).
    rewrite (zbits_eqn b3 V3).
    cbn [bw_out bw_valid].
    unfold zlen. rewrite length_app, length_map. lia. }
  assert (E4 : bw_valid {| bw_out := bw_out b3 ++ map u8 dat;
                           bw_buf := bw_buf b3; bw_valid := bw_valid b3 |}
               = bw_valid b3) by reflexivity.
  split; [|split].
  - rewrite Z4, Z3, Z2, Z1, Z0. ring.
  - rewrite E4, E3, E2, E1. reflexivity.
  - unfold bwv. rewrite E4, E3, E2, E1.
    unfold Buf_size. lia.
Qed.

(** The fits corollary, in potential form: [ceil8 (zbits after)] is the
    value itself (aligned), and it sits within [8*stored_len + 40] of the
    pre-block potential. *)
Corollary tr_stored_block_fits : forall dat stored_len last s,
  bwv (ts_bw s) ->
  stored_len = zlen dat ->
  ceil8 (zbits (ts_bw (tr_stored_block dat stored_len last s)))
    = zbits (ts_bw (tr_stored_block dat stored_len last s))
  /\ zbits (ts_bw (tr_stored_block dat stored_len last s))
     <= ceil8 (zbits (ts_bw s)) + 8 * stored_len + 40
  /\ zbits (ts_bw s) <= zbits (ts_bw (tr_stored_block dat stored_len last s)).
Proof.
  intros dat stored_len last s Hb Hlen.
  destruct (tr_stored_block_len dat stored_len last s Hb) as (HZ & HV & HW).
  pose proof (zbits_nonneg (ts_bw s)) as Hnn.
  pose proof (zlen_nonneg dat) as Hdn.
  assert (Hc3 : ceil8 (zbits (ts_bw s) + 3)
                <= ceil8 (zbits (ts_bw s)) + 8).
  { pose proof (ceil8_add_le (zbits (ts_bw s)) 3 ltac:(lia)) as H.
    replace (ceil8 3) with 8 in H by reflexivity. exact H. }
  pose proof (ceil8_ge (zbits (ts_bw s))) as Hge.
  split; [|split].
  - apply ceil8_aligned.
    rewrite HZ.
    pose proof (ceil8_mod (zbits (ts_bw s) + 3)) as Hm.
    replace (ceil8 (zbits (ts_bw s) + 3) + 32 + 8 * zlen dat)
      with (ceil8 (zbits (ts_bw s) + 3) + 8 * (4 + zlen dat)) by ring.
    rewrite Z.add_mod, Z.mul_comm, Z_mod_mult, Hm by lia.
    reflexivity.
  - rewrite HZ, Hlen. lia.
  - rewrite HZ.
    pose proof (ceil8_ge (zbits (ts_bw s) + 3)). lia.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions tr_stored_block_len.
Print Assumptions tr_stored_block_fits.
