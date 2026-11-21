(** * Bridge.DEmit.DZTrailLive — the zlib trailer pair with live symbols.

    [DZHeader.pair_deflate_trailer] (a worker) asks for an empty symbol
    buffer.  At levels 1-9 the trailer runs after [deflate_fast] /
    [deflate_slow] return [finish_done], whose pairs (group M) give only
    [em_inv] ([sym_next = 3 * nsym]).  This is the same pair for any
    [sym_next]: the four trailer bytes and [bi_flush]'s at most two land
    below [lit_bufsize], so the symbol area is untouched ([BrZKit]'s
    [dst_putShortMSB] and [dst_flush_pending']).  The zlib wrapper only
    ([wrap = 1]); that is all compress_fuzzer's [deflateInit] produces.

    Requested by a worker for [BrCompressCall] (claims board).
    Ownership: group D (a worker). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz Deflate DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs BrDFlush BrStored BrFbKit BrZKit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DZHeader.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module DZ := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Deflate.
Module DSf := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.

Lemma rt_psm_wrap32 : forall y ts, RD.putShortMSB (wrap32 y) ts = RD.putShortMSB y ts.
Proof.
  intros y ts. unfold RD.putShortMSB.
  rewrite (DZHeader.bw_put_byte_u8 (Z.shiftr (wrap32 y) 8) (Z.shiftr y 8)) by apply DZHeader.u8_shiftr8_wrap32.
  rewrite (DZHeader.bw_put_byte_u8 (Z.land (wrap32 y) 255) (Z.land y 255)) by apply DZHeader.u8_land_wrap32.
  reflexivity.
Qed.

Lemma setD_ts_twice : forall x y t, RD.setD_ts x (RD.setD_ts y t) = RD.setD_ts x t.
Proof. reflexivity. Qed.

Lemma psm_frame : forall s b,
  arr_len (DS.ds_pending_buf (DL.putShortMSB s b)) = arr_len (DS.ds_pending_buf s)
  /\ DS.ds_bi_valid (DL.putShortMSB s b) = DS.ds_bi_valid s
  /\ DS.ds_strm (DL.putShortMSB s b) = DS.ds_strm s
  /\ DS.ds_lit_bufsize (DL.putShortMSB s b) = DS.ds_lit_bufsize s.
Proof.
  intros s b. unfold DL.putShortMSB. cbv zeta. rewrite !pblen_put_byte, !strm_put_byte.
  split; [reflexivity|]. split; [unfold DS.put_byte; cbv zeta; autorewrite with s5f_pending s5f_pending_buf; reflexivity|].
  split; [reflexivity|]. exact (proj1 (gl_fields' _ _ (eq_trans (gl_put_byte _ _) (gl_put_byte s _)))).
Qed.

Theorem pair_deflate_trailer_live : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> room s 10 -> fp_ok s ->
  DS.ds_wrap s = 1 -> 0 <= DS.ds_bi_valid s <= 16 -> DS.ds_pending s + 10 <= DS.ds_lit_bufsize s ->
  exists t', RD.deflate_trailer t = RD.DfRet (snd (DZ.deflate_trailer s)) t'
             /\ dst_rel (fst (DZ.deflate_trailer s)) t' pre_out pre_in.
Proof.
  intros s t pre_out pre_in Hrel [Hpo Hroom] Hok Hw Hbv Hlbs.
  pose proof Hrel as (Hg & _ & _ & _ & _ & Hm).
  assert (Gw : DS.ds_wrap s = RD.d_wrap t)
    by (destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gw & _); exact Gw).
  assert (Sad : RD.zs_adler (RD.d_strm t) = DS.cs_adler (DS.ds_strm s))
    by (destruct Hm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Sad & _); exact Sad).
  pose proof Hok as (Hav & Hlen32 & Htot0 & Htot64).
  rewrite DSf.deflate_trailer_eq. unfold RD.deflate_trailer. unfold DSf.trailer_st. cbv zeta.
  rewrite <- Gw, Hw, Sad. cbn [Z.eqb Pos.eqb].
  set (a := DS.cs_adler (DS.ds_strm s)).
  (* the two halves of the adler *)
  destruct (dst_putShortMSB s t pre_out pre_in (wrap32 (Z.shiftr a 16)) Hrel ltac:(split; lia) ltac:(intros; lia))
    as (R1 & P1 & O1).
  destruct (psm_frame s (wrap32 (Z.shiftr a 16))) as (L1 & V1 & S1 & B1).
  rewrite rt_psm_wrap32 in R1.
  set (s1 := DL.putShortMSB s (wrap32 (Z.shiftr a 16))) in *.
  destruct (dst_putShortMSB s1 _ pre_out pre_in (Z.land a 65535) R1
              ltac:(split; [exact O1 | rewrite P1, L1; lia]) ltac:(intros; rewrite P1, B1; lia))
    as (R2 & P2 & O2).
  destruct (psm_frame s1 (Z.land a 65535)) as (L2 & V2 & S2 & B2).
  rewrite d_ts_setD_ts', setD_ts_twice in R2.
  set (s2 := DL.putShortMSB s1 (Z.land a 65535)) in *.
  (* the flush *)
  assert (Hbv2 : 0 <= DS.ds_bi_valid s2 <= 16) by (rewrite V2, V1; exact Hbv).
  assert (Hp2 : DS.ds_pending s2 + 2 < 2 ^ 32) by (rewrite P2, P1; lia).
  assert (Hsy2 : 0 < DS.ds_sym_next s2 -> DS.ds_pending s2 + 2 <= DS.ds_lit_bufsize s2)
    by (intros _; rewrite P2, P1, B2, B1; lia).
  assert (Hfr2 : flush_room s2) by (right; split; [exact O2 | rewrite P2, P1, L2, L1; lia]).
  assert (Hok2 : fp_ok s2) by (unfold fp_ok; rewrite S2, S1, L2, L1; exact Hok).
  pose proof (dst_flush_pending' s2 _ pre_out pre_in R2 O2 Hbv2 Hp2 Hsy2 Hfr2 Hok2) as H2.
  clearbody s1 s2.
  revert H2.
  generalize (DL.flush_pending s2) as x2.
  generalize (RD.flush_pending (RD.setD_ts (RD.putShortMSB (Z.land a 65535) (RD.putShortMSB (Z.shiftr a 16) (RD.d_ts t))) t))
    as t2.
  intros t2 x2 H2.
  assert (Ew : DS.ds_wrap x2 = RD.d_wrap t2)
    by (destruct H2 as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gw2 & _) & _);
        exact Gw2).
  rewrite <- Ew.
  destruct (0 <? DS.ds_wrap x2); cbn [fst snd].
  - exists (RD.setD_wrap (- DS.ds_wrap x2) t2).
    pose proof (DZHeader.dst_rel_wrap _ _ _ _ (- DS.ds_wrap x2) H2) as H3.
    split; [|exact H3].
    rewrite (DZHeader.pend_zlen _ _ _ _ H3).
    destruct (negb (DS.ds_pending (DS.set_wrap x2 (- DS.ds_wrap x2)) =? 0)); reflexivity.
  - exists t2. split; [|exact H2].
    rewrite (DZHeader.pend_zlen _ _ _ _ H2). destruct (negb (DS.ds_pending x2 =? 0)); reflexivity.
Qed.

Print Assumptions pair_deflate_trailer_live.
