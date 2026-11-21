(** * ZReproG6A — G6 bound-fit, part A: the bit ledger.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-19).  Queue item G6
    (Q5 plan P7): the deflateBound-fit face at the level>=1 configs.

    This file is the CURRENCY layer:
      * [zbits]    — bit length of the writer's abstract stream;
      * [ceil8]    — the byte-ceiling potential.  The amortized per-block
                     bound ("one flush adds at most [8*span + 40] bits of
                     potential") is stated in [ceil8] because the stored
                     arm byte-aligns before its LEN/NLEN words and the
                     final windup pads to a byte: the ceiling absorbs
                     both pads without per-position case analysis;
      * [tot_bits] — drained output bytes + writer bits: the quantity
                     [flush_pending] conserves EXACTLY (a truncated drain
                     just redistributes bits between the two summands);
      * the per-primitive length equations.

    WHY THERE ARE NO VALUE PREMISES: both branches of [bw_send_bits]
    extend the stream by exactly [length] bits whatever the value sent,
    and the register width stays inside [0, Buf_size] whenever the sent
    width is.  The length layer therefore threads only [bwv] (the width
    window — [bw_wf] minus its value clause), so the accounting walks in
    ZReproG6B/C never owe a code-range or Kraft fact.  The decode side
    (the G3 files) carries [bw_wf]; [bwv_of_wf] is the bridge.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  zlen glue (list-level; tiny, local to keep the import cone lean).
   ========================================================================== *)

Lemma g6_zlen_app : forall (l1 l2 : list Z),
  zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros l1 l2. unfold zlen. rewrite length_app. lia. Qed.

Lemma g6_zlen_firstn : forall n (l : list Z),
  0 <= n <= zlen l -> zlen (firstn (Z.to_nat n) l) = n.
Proof.
  intros n l Hn. unfold zlen in *. rewrite length_firstn. lia.
Qed.

Lemma g6_zlen_skipn : forall n (l : list Z),
  0 <= n <= zlen l -> zlen (skipn (Z.to_nat n) l) = zlen l - n.
Proof.
  intros n l Hn. unfold zlen in *. rewrite length_skipn. lia.
Qed.

Lemma g6_zlen1 : forall a : Z, zlen [a] = 1.
Proof. reflexivity. Qed.

Lemma g6_zlen2 : forall a b : Z, zlen [a; b] = 2.
Proof. reflexivity. Qed.

(* ==========================================================================
   2.  ceil8 — the byte-ceiling potential.
   ========================================================================== *)

Definition ceil8 (n : Z) : Z := 8 * ((n + 7) / 8).

Lemma ceil8_ge : forall n, n <= ceil8 n.
Proof.
  intro n. unfold ceil8.
  pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as Hm.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as He. lia.
Qed.

Lemma ceil8_lt : forall n, ceil8 n < n + 8.
Proof.
  intro n. unfold ceil8.
  pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as Hm.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as He. lia.
Qed.

Lemma ceil8_mono : forall a b, a <= b -> ceil8 a <= ceil8 b.
Proof.
  intros a b Hab. unfold ceil8.
  apply Z.mul_le_mono_nonneg_l; [lia|].
  apply Z.div_le_mono; lia.
Qed.

Lemma ceil8_add_mul : forall n k, ceil8 (n + 8 * k) = ceil8 n + 8 * k.
Proof.
  intros n k. unfold ceil8.
  replace (n + 8 * k + 7) with (n + 7 + k * 8) by ring.
  rewrite Z.div_add by lia. ring.
Qed.

Lemma ceil8_aligned : forall n, n mod 8 = 0 -> ceil8 n = n.
Proof.
  intros n H. unfold ceil8.
  rewrite (Z.div_mod n 8) at 2 by lia. rewrite H.
  replace (n + 7) with (8 * (n / 8) + (n mod 8 + 7)) by lia.
  rewrite H.
  replace (8 * (n / 8) + (0 + 7)) with (n / 8 * 8 + 7) by ring.
  rewrite Z.div_add_l by lia.
  replace (7 / 8) with 0 by reflexivity. ring.
Qed.

Lemma ceil8_mod : forall n, (ceil8 n) mod 8 = 0.
Proof.
  intro n. unfold ceil8. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma ceil8_nonneg : forall n, 0 <= n -> 0 <= ceil8 n.
Proof. intros n Hn. pose proof (ceil8_ge n). lia. Qed.

(** The huffman-arm step: adding [k] bits moves the ceiling by at most
    [ceil8 k]. *)
Lemma ceil8_add_le : forall n k, 0 <= k -> ceil8 (n + k) <= ceil8 n + ceil8 k.
Proof.
  intros n k Hk. unfold ceil8.
  rewrite <- Z.mul_add_distr_l.
  apply Z.mul_le_mono_nonneg_l; [lia|].
  pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (k + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (k + 7) 8 ltac:(lia)).
  assert (Hlt : (n + k + 7) / 8 < (n + 7) / 8 + (k + 7) / 8 + 1).
  { apply Z.div_lt_upper_bound; lia. }
  lia.
Qed.

(* ==========================================================================
   3.  zbits — the stream length — and the width window.
   ========================================================================== *)

Definition zbits (b : BW) : Z := Z.of_nat (length (bw_stream b)).

(** [bw_wf] minus its value clause: all the length layer ever needs. *)
Definition bwv (b : BW) : Prop := 0 <= bw_valid b <= Buf_size.

Lemma bwv_of_wf : forall b, bw_wf b -> bwv b.
Proof. intros b [Hw _]. exact Hw. Qed.

Lemma zbits_eqn : forall b, 0 <= bw_valid b ->
  zbits b = 8 * zlen (bw_out b) + bw_valid b.
Proof.
  intros b Hv. unfold zbits, bw_stream, zlen.
  rewrite length_app, bytes_bits_length.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
  change (Z.of_nat 8) with 8.
  pose proof (zwrite_length (bw_valid b) (bw_buf b) Hv) as Hz.
  lia.
Qed.

Lemma zbits_nonneg : forall b, 0 <= zbits b.
Proof. intro b. unfold zbits. lia. Qed.

(* ==========================================================================
   4.  Per-primitive length equations.
   ========================================================================== *)

Lemma zbits_put_byte : forall v b, 0 <= bw_valid b ->
  zbits (bw_put_byte v b) = zbits b + 8 /\ bw_valid (bw_put_byte v b) = bw_valid b.
Proof.
  intros v b Hv.
  split; [|reflexivity].
  rewrite (zbits_eqn (bw_put_byte v b)) by exact Hv.
  rewrite (zbits_eqn b) by exact Hv.
  cbn [bw_put_byte bw_out bw_valid].
  rewrite g6_zlen_app, g6_zlen1. lia.
Qed.

Lemma zbits_put_short : forall w b, 0 <= bw_valid b ->
  zbits (bw_put_short w b) = zbits b + 16
  /\ bw_valid (bw_put_short w b) = bw_valid b.
Proof.
  intros w b Hv. unfold bw_put_short.
  destruct (zbits_put_byte w b Hv) as [H1 V1].
  destruct (zbits_put_byte (Z.shiftr (u16 w) 8) (bw_put_byte w b)
              ltac:(rewrite V1; exact Hv)) as [H2 V2].
  rewrite H2, H1, V2, V1. split; [lia | reflexivity].
Qed.

(** THE key primitive fact: both branches add exactly [n] bits, no value
    premise; and the width window is self-preserving. *)
Lemma zbits_send_bits : forall v n b,
  bwv b -> 0 <= n <= Buf_size ->
  zbits (bw_send_bits v n b) = zbits b + n /\ bwv (bw_send_bits v n b).
Proof.
  intros v n b [Hv0 Hv16] [Hn0 Hn16].
  assert (HB : Buf_size = 16) by reflexivity.
  unfold bw_send_bits. cbv zeta.
  destruct (Z.ltb_spec (Buf_size - n) (bw_valid b)) as [Hg|Hg].
  - (* spill: the merged short goes out, the register keeps the excess *)
    destruct (zbits_put_short
                (u16 (Z.lor (bw_buf b) (Z.shiftl (u16 v) (bw_valid b)))) b
                Hv0) as [Hs _].
    split.
    + rewrite zbits_eqn by (cbn [bw_valid]; lia).
      rewrite (zbits_eqn b Hv0).
      cbn [bw_out bw_valid].
      rewrite bw_put_short_out, g6_zlen_app, g6_zlen2. lia.
    + unfold bwv. cbn [bw_valid]. lia.
  - split.
    + rewrite zbits_eqn by (cbn [bw_valid]; lia).
      rewrite (zbits_eqn b Hv0).
      cbn [bw_out bw_valid]. lia.
    + unfold bwv. cbn [bw_valid]. lia.
Qed.

Lemma zbits_send_code : forall c t b,
  bwv b -> 0 <= t_len t c <= Buf_size ->
  zbits (send_code c t b) = zbits b + t_len t c /\ bwv (send_code c t b).
Proof.
  intros c t b Hb Hl. unfold send_code.
  apply zbits_send_bits; assumption.
Qed.

(** [bi_flush]: length-preserving, register drops below a byte. *)
Lemma zbits_flush : forall b, bwv b ->
  zbits (bw_flush b) = zbits b
  /\ bwv (bw_flush b)
  /\ 0 <= bw_valid (bw_flush b) < 8.
Proof.
  intros b [Hv0 Hv16].
  assert (HB : Buf_size = 16) by reflexivity.
  unfold bw_flush.
  destruct (Z.eqb_spec (bw_valid b) 16) as [E16|E16].
  - destruct (zbits_put_short (bw_buf b) b Hv0) as [_ _].
    repeat split; try (unfold bwv; cbn [bw_valid]; lia).
    rewrite zbits_eqn by (cbn [bw_valid]; lia).
    rewrite (zbits_eqn b Hv0).
    cbn [bw_out bw_valid].
    rewrite bw_put_short_out, g6_zlen_app, g6_zlen2. lia.
  - destruct (Z.leb_spec 8 (bw_valid b)) as [E8|E8].
    + repeat split; try (unfold bwv; cbn [bw_valid]; lia).
      rewrite zbits_eqn by (cbn [bw_valid]; lia).
      rewrite (zbits_eqn b Hv0).
      cbn [bw_out bw_valid].
      rewrite bw_put_byte_out, g6_zlen_app, g6_zlen1. lia.
    + repeat split; lia.
Qed.

(** [bi_windup]: pads to the ceiling, empties the register. *)
Lemma zbits_windup : forall b, bwv b ->
  zbits (bw_windup b) = ceil8 (zbits b)
  /\ bw_valid (bw_windup b) = 0
  /\ bwv (bw_windup b)
  /\ 8 * zlen (bw_out (bw_windup b)) = ceil8 (zbits b).
Proof.
  intros b [Hv0 Hv16].
  assert (HB : Buf_size = 16) by reflexivity.
  assert (Hz : zbits b = 8 * zlen (bw_out b) + bw_valid b)
    by (apply zbits_eqn; exact Hv0).
  assert (Hwind : zbits (bw_windup b)
                  = 8 * zlen (bw_out (bw_windup b))
                  /\ bw_valid (bw_windup b) = 0).
  { unfold bw_windup. cbv zeta.
    split; [|reflexivity].
    rewrite zbits_eqn by (cbn [bw_valid]; lia).
    cbn [bw_out bw_valid]. lia. }
  destruct Hwind as [Hw0 Hval0].
  assert (Hout : zbits (bw_windup b)
                 = 8 * zlen (bw_out b)
                   + (if Z.ltb 8 (bw_valid b) then 16
                      else if Z.ltb 0 (bw_valid b) then 8 else 0)).
  { unfold bw_windup. cbv zeta.
    rewrite zbits_eqn by (cbn [bw_valid]; lia).
    cbn [bw_out bw_valid].
    destruct (Z.ltb_spec 8 (bw_valid b)) as [E8|E8].
    - rewrite bw_put_short_out, g6_zlen_app, g6_zlen2. lia.
    - destruct (Z.ltb_spec 0 (bw_valid b)) as [E0|E0].
      + rewrite bw_put_byte_out, g6_zlen_app, g6_zlen1. lia.
      + lia. }
  assert (Hceil : ceil8 (zbits b)
                  = 8 * zlen (bw_out b)
                    + (if Z.ltb 8 (bw_valid b) then 16
                       else if Z.ltb 0 (bw_valid b) then 8 else 0)).
  { rewrite Hz.
    replace (8 * zlen (bw_out b) + bw_valid b)
      with (bw_valid b + 8 * zlen (bw_out b)) by ring.
    rewrite ceil8_add_mul.
    destruct (Z.ltb_spec 8 (bw_valid b)) as [E8|E8];
      [|destruct (Z.ltb_spec 0 (bw_valid b)) as [E0|E0]].
    - assert (Hd1 : 2 <= (bw_valid b + 7) / 8)
        by (apply Z.div_le_lower_bound; lia).
      assert (Hd2 : (bw_valid b + 7) / 8 < 3)
        by (apply Z.div_lt_upper_bound; lia).
      unfold ceil8. lia.
    - assert (Hd1 : 1 <= (bw_valid b + 7) / 8)
        by (apply Z.div_le_lower_bound; lia).
      assert (Hd2 : (bw_valid b + 7) / 8 < 2)
        by (apply Z.div_lt_upper_bound; lia).
      unfold ceil8. lia.
    - unfold ceil8.
      replace (bw_valid b) with 0 by lia.
      replace ((0 + 7) / 8) with 0 by reflexivity. ring. }
  refine (conj _ (conj Hval0 (conj _ _))).
  - rewrite Hout, <- Hceil. reflexivity.
  - unfold bwv. rewrite Hval0, HB. lia.
  - rewrite <- Hw0, Hout, <- Hceil. reflexivity.
Qed.

(** TSt-level wrappers. *)
Lemma zbits_tr_flush_bits : forall ts, bwv (ts_bw ts) ->
  zbits (ts_bw (tr_flush_bits ts)) = zbits (ts_bw ts)
  /\ bwv (ts_bw (tr_flush_bits ts))
  /\ 0 <= bw_valid (ts_bw (tr_flush_bits ts)) < 8.
Proof.
  intros ts Hb. unfold tr_flush_bits. rewrite ts_bw_set_bw.
  exact (zbits_flush (ts_bw ts) Hb).
Qed.

(* ==========================================================================
   5.  tot_bits — what flush_pending conserves.
   ========================================================================== *)

Definition zbw (s : DSt) : BW := ts_bw (d_ts s).

Definition tot_bits (s : DSt) : Z :=
  8 * zlen (zs_out (d_strm s)) + zbits (zbw s).

Theorem flush_pending_acct : forall s,
  bwv (zbw s) ->
  0 <= zs_availout (d_strm s) ->
  tot_bits (flush_pending s) = tot_bits s
  /\ bwv (zbw (flush_pending s))
  /\ zs_availout (d_strm (flush_pending s))
     = zs_availout (d_strm s)
       - (zlen (zs_out (d_strm (flush_pending s)))
          - zlen (zs_out (d_strm s)))
  /\ zlen (zs_out (d_strm s)) <= zlen (zs_out (d_strm (flush_pending s)))
  /\ 0 <= zs_availout (d_strm (flush_pending s))
  /\ (zlen (bw_out (bw_flush (zbw s))) <= zs_availout (d_strm s) ->
      bw_out (zbw (flush_pending s)) = []
      /\ bw_valid (zbw (flush_pending s)) = bw_valid (bw_flush (zbw s)))
  /\ zs_in (d_strm (flush_pending s)) = zs_in (d_strm s)
  /\ zs_done (d_strm (flush_pending s)) = zs_done (d_strm s)
  /\ d_ls (flush_pending s) = d_ls s
  /\ d_cfg (flush_pending s) = d_cfg s
  /\ d_wrap (flush_pending s) = d_wrap s.
Proof.
  intros s Hb Havo.
  unfold tot_bits, zbw in *.
  unfold flush_pending. cbv zeta.
  assert (Hfb : ts_bw (tr_flush_bits (d_ts s)) = bw_flush (ts_bw (d_ts s)))
    by (unfold tr_flush_bits; rewrite ts_bw_set_bw; reflexivity).
  destruct (zbits_flush (ts_bw (d_ts s)) Hb) as (Hfz & Hfv & Hfv8).
  pose proof (zlen_nonneg (bw_out (ts_bw (tr_flush_bits (d_ts s))))) as Hpd0.
  set (pd := bw_out (ts_bw (tr_flush_bits (d_ts s)))) in *.
  set (len0 := zlen pd) in *.
  set (len := if Z.ltb (zs_availout (d_strm s)) len0
              then zs_availout (d_strm s) else len0) in *.
  assert (Hlen : 0 <= len <= len0).
  { unfold len. destruct (Z.ltb_spec (zs_availout (d_strm s)) len0); lia. }
  assert (Hzfb : zbits (ts_bw (tr_flush_bits (d_ts s))) = zbits (ts_bw (d_ts s)))
    by (rewrite Hfb; exact Hfz).
  assert (Hvfb : 0 <= bw_valid (ts_bw (tr_flush_bits (d_ts s))) <= Buf_size)
    by (rewrite Hfb; exact Hfv).
  assert (Hpd_flush : len0 = zlen (bw_out (bw_flush (ts_bw (d_ts s)))))
    by (unfold len0, pd; rewrite Hfb; reflexivity).
  assert (Hcase2 : len0 <= zs_availout (d_strm s) -> len = len0).
  { intro H. unfold len.
    destruct (Z.ltb_spec (zs_availout (d_strm s)) len0) as [Hc|Hc];
      [lia|reflexivity]. }
  destruct (Z.eqb_spec len 0) as [E0|E0].
  - (* nothing moves *)
    cbn [setD_ts d_ts d_strm d_ls d_cfg d_wrap].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
              (conj _ (conj _ (conj _ (conj _ _)))))))))).
    + rewrite Hzfb. reflexivity.
    + exact Hvfb.
    + lia.
    + lia.
    + exact Havo.
    + (* drain clause: len = 0 with pd <= avail forces pd = [] *)
      intro Hle. rewrite <- Hpd_flush in Hle.
      split; [|rewrite Hfb; reflexivity].
      assert (E : len0 = 0) by (pose proof (Hcase2 Hle); lia).
      apply zlen_nil. unfold len0 in E. exact E.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - (* len bytes move out *)
    cbn [setD_strm setD_ts d_ts d_strm d_ls d_cfg d_wrap
         setZ_out setZ_availout setZ_totalout
         zs_out zs_availout zs_in zs_done].
    rewrite ts_bw_set_bw.
    cbn [bw_out bw_valid].
    assert (Hmoved : zlen (firstn (Z.to_nat len) pd) = len)
      by (apply g6_zlen_firstn; exact Hlen).
    assert (Hrest : zlen (skipn (Z.to_nat len) pd) = len0 - len)
      by (apply g6_zlen_skipn; exact Hlen).
    assert (Hz2 : zbits (ts_bw (tr_flush_bits (d_ts s)))
                  = 8 * len0 + bw_valid (ts_bw (tr_flush_bits (d_ts s))))
      by (apply zbits_eqn; lia).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
              (conj _ (conj _ (conj _ (conj _ _)))))))))).
    + (* conservation *)
      rewrite zbits_eqn by (cbn [bw_valid]; lia).
      cbn [bw_out bw_valid].
      rewrite g6_zlen_app, Hmoved, Hrest. lia.
    + (* width window *)
      unfold bwv. cbn [bw_valid]. exact Hvfb.
    + (* availout relation *)
      rewrite g6_zlen_app, Hmoved. lia.
    + rewrite g6_zlen_app, Hmoved. lia.
    + (* availout stays nonnegative *)
      unfold len. destruct (Z.ltb_spec (zs_availout (d_strm s)) len0); lia.
    + (* full drain *)
      intro Hle. rewrite <- Hpd_flush in Hle.
      pose proof (Hcase2 Hle) as Elen.
      split.
      * rewrite Elen.
        replace (skipn (Z.to_nat len0) pd) with (@nil Z); [reflexivity|].
        symmetry. apply zlen_nil.
        rewrite g6_zlen_skipn; unfold len0; lia.
      * cbn [bw_valid]. rewrite Hfb. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions flush_pending_acct.
Print Assumptions zbits_windup.
Print Assumptions zbits_send_bits.
Print Assumptions ceil8_add_le.
