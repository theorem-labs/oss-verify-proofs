(** * Bridge.DEmit.BrBlocks — pair D8 of PAIRS.md: the block driver at [Z_FINISH], S5 vs RT.

    S5's [deflate_blocks s 4] followed by the tail of [deflate_core] (return an early code, else
    the end-of-stream code or the trailer: [s5_tail]) against RT's [deflate_run 4], which has the
    same tail inside.  Both test the same condition, which holds ([status <> FINISH_STATE]), and
    run the same block function ([BrDispatch.br_dispatch]).  Then, by block state:

    - [need_more] / [finish_started]: both return [Z_OK], setting [last_flush] to -1 when the
      output is full;
    - [block_done]: not taken at [Z_FINISH] (S5's own block-function contract
      [RefDeflSafeI4.BFPOST]);
    - [finish_done]: both return [Z_STREAM_END] when [wrap <= 0], else both write the zlib
      trailer: a worker's [DZHeader.pair_deflate_trailer] at level 0 (D13 leaves no symbols),
      a worker's [DZTrailLive.pair_deflate_trailer_live] at levels 1-9 (live symbols; its
      [wrap = 1] from group M's [mt_inv]).

    S5's side conditions come from S5's own safety proof: the state is [RefDeflSafeI4.ST] (the
    call invariant [DC] with fixed sizes), whose [BFPOST] excludes [block_done] and empties the
    queue at [finish_done]; the trailer's [room], [fp_ok] and bit-buffer premises then follow
    from [DC] ([BrTopDefs.dc_room], [fp_ok_of_DC], [dc_bits]).  After the trailer only the
    stream relation is kept:
    the output and the return code are all the deflate entry (D7) reads. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Deflate
  RefDeflateRel RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeI6
  RefDeflSafeL0 RefDeflSafeL2 RefDeflSafeL3 RefDeflSafeL4 RefDeflSafeL5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface BrDispatch BrTopDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DZHeader DZTrailLive.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SI2 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI2.
Module SI3 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI3.
Module SI4 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI4.
Module SI6 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.
Module SL0 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL0.
Module SL2 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL2.
Module SL3 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL3.
Module SL4 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL4.
Module SL5 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL5.

(** The tail of S5's [deflate_core] after the header states, verbatim. *)
Definition s5_tail (s : DS.deflate_state) (flush : Z) : DS.deflate_state * Z :=
  let '(s, r) := SDfl.deflate_blocks s flush in
  match r with Some rc => (s, rc) | None =>
  if negb (Z.eqb flush Z_FINISH) then (s, Z_OK)
  else if Z.leb (DS.ds_wrap s) 0 then (s, Z_STREAM_END)
  else SDfl.deflate_trailer s
  end.

(** S5's block-function contract, as S5's own top-level proof instantiates it
    ([DeflateTaintTop.deflate_m_facts]). *)
Lemma s5_bfpost : forall c0 s0 s flush,
  SI2.C0OK' c0 -> SI4.ST c0 s0 s ->
  DS.ds_pending s = 0 -> DS.ds_status s <> DS.FINISH_STATE -> 0 <= flush <= 5 ->
  SI4.BFPOST c0 s flush (SDfl.run_compress_func s flush).
Proof.
  intros c0 s0 s flush HC0 HS Hp Hst Hfl.
  exact (proj2 (SI4.bf_call _ _ _ _ SL0.stored_bf_spec (SL3.huff_bf_spec SI6.FB_CALL_ok)
                  (SL4.rle_bf_spec SI6.FB_CALL_ok) (SL2.fast_bf_spec SI6.FB_CALL_ok)
                  (SL5.slow_bf_spec SI6.FB_CALL_ok) c0 s0 HC0 s flush HS Hp Hst Hfl)).
Qed.

Theorem br_blocks_finish : forall c0 s0 s t pre_out pre_in,
  SI2.C0OK' c0 -> SI4.ST c0 s0 s -> DS.cs_total_out c0 + DS.cs_avail_out c0 + 2 ^ 17 < 2 ^ 64 ->
  DS.ds_pending s = 0 -> DS.ds_status s <> DS.FINISH_STATE ->
  dst_rel s t pre_out pre_in -> mt_inv t -> blk_pre (RC.dg_level (RD.d_cfg t)) s ->
  exists code t', RD.deflate_run 4 t = RD.DfRet code t'
    /\ snd (s5_tail s 4) = code /\ strm_rel (fst (s5_tail s 4)) t' pre_out pre_in.
Proof.
  intros c0 s0 s t pre_out pre_in HC0 HS Hroom0 Hp Hst Hrel Hmt Hblk.
  destruct (dst_rel_geom _ _ _ _ Hrel) as (_ & Hstat & _ & _).
  pose proof (s5_bfpost c0 s0 s 4 HC0 HS Hp Hst ltac:(lia)) as HPOST.
  pose proof (br_dispatch s t pre_out pre_in Hrel Hmt Hblk) as Hd.
  unfold s5_tail, SDfl.deflate_blocks, RD.deflate_run.
  (* the driver's condition holds on both sides *)
  replace (negb (DS.cs_avail_in (DS.ds_strm s) =? 0) || negb (DS.ds_lookahead s =? 0)
           || negb (4 =? Z_NO_FLUSH) && negb (DS.ds_status s =? DS.FINISH_STATE)) with true
    by (symmetry; apply orb_true_iff; right; apply andb_true_iff; split; [reflexivity|];
        apply negb_true_iff, Z.eqb_neq; exact Hst).
  replace (negb (Chunk.zlen (RD.zs_in (RD.d_strm t)) =? 0) || negb (RD.ls_lookahead (RD.d_ls t) =? 0)
           || negb (4 =? Base.Z_NO_FLUSH) && negb (RD.d_status t =? RD.FINISH_STATE)) with true
    by (symmetry; apply orb_true_iff; right; apply andb_true_iff; split; [reflexivity|];
        apply negb_true_iff, Z.eqb_neq; rewrite <- Hstat; exact Hst).
  cbv beta iota.
  destruct (SDfl.run_compress_func s 4) as [s1 bst] eqn:Er.
  destruct (RD.dispatch 4 t) as [bs sa] eqn:Ed.
  rewrite ?Er in Hd, HPOST. rewrite ?Ed in Hd.
  cbn [fst snd] in Hd. destruct Hd as (Hbs & Hrel1 & Hpost).
  unfold SI4.BFPOST in HPOST. cbv zeta in HPOST. cbn [fst snd] in HPOST.
  destruct HPOST as (HDC1 & _ & _ & Hbd & Hfin & Hfd).
  destruct (dst_rel_avail _ _ _ _ Hrel1) as [Ha _].
  destruct bst; cbn [bs_of] in Hbs; subst bs; cbn [DL.block_state_eqb orb andb negb].
  - (* need_more *)
    rewrite Ha. eexists _, _. split; [reflexivity|]. cbn [fst snd]. split; [reflexivity|].
    destruct (DS.cs_avail_out (DS.ds_strm s1) =? 0);
      apply (strm_rel_congr s1 _ sa _ pre_out pre_in); first [reflexivity | exact (dst_rel_strm _ _ _ _ Hrel1)].
  - (* block_done: not at Z_FINISH *)
    exfalso. destruct (Hbd eq_refl) as (_ & Hnf & _). apply Hnf. reflexivity.
  - (* finish_started *)
    assert (Ea : RD.zs_availout (RD.d_strm (RD.setD_status RD.FINISH_STATE sa))
                 = DS.cs_avail_out (DS.ds_strm (DS.set_status s1 DS.FINISH_STATE))) by exact Ha.
    rewrite Ea. eexists _, _. split; [reflexivity|]. cbn [fst snd]. split; [reflexivity|].
    destruct (DS.cs_avail_out (DS.ds_strm (DS.set_status s1 DS.FINISH_STATE)) =? 0);
      apply (strm_rel_congr s1 _ sa _ pre_out pre_in); first [reflexivity | exact (dst_rel_strm _ _ _ _ Hrel1)].
  - (* finish_done: the end of the stream, or the trailer *)
    try change (Z.eqb 4 Z_FINISH) with true. try change (Z.eqb 4 Base.Z_FINISH) with true. cbn [negb].
    pose proof (dst_rel_set_status s1 sa pre_out pre_in DS.FINISH_STATE RD.FINISH_STATE eq_refl Hrel1) as Hrel2.
    destruct (dst_rel_geom _ _ _ _ Hrel2) as (_ & _ & Hw2 & _).
    rewrite <- Hw2.
    destruct (DS.ds_wrap (DS.set_status s1 DS.FINISH_STATE) <=? 0).
    + eexists _, _. split; [reflexivity|]. cbn [fst snd].
      split; [reflexivity | exact (dst_rel_strm _ _ _ _ Hrel2)].
    + assert (HDC2 : SI1.DC c0 (DS.set_status s1 DS.FINISH_STATE)).
      { refine (proj1 (SI3.DC_set_status c0 s1 DS.FINISH_STATE HDC1 _ _ _)).
        - right; right; right; reflexivity.
        - intros _; reflexivity.
        - intros _; exact (Hfin (or_intror eq_refl)). }
      pose proof (dc_room c0 _ 10 HDC2 (Hfd eq_refl) ltac:(lia)) as Hroom2.
      pose proof (fp_ok_of_DC c0 _ (SI2.c0'_ok _ HC0) HDC2 Hroom0) as Hok2.
      assert (Htr : exists t', RD.deflate_trailer (RD.setD_status RD.FINISH_STATE sa)
                               = RD.DfRet (snd (SDfl.deflate_trailer (DS.set_status s1 DS.FINISH_STATE))) t'
                    /\ dst_rel (fst (SDfl.deflate_trailer (DS.set_status s1 DS.FINISH_STATE))) t' pre_out pre_in).
      { unfold blk_post in Hpost. revert Hpost. destruct (Z.eqb (RC.dg_level (RD.d_cfg t)) 0); intros Hpost.
        - (* level 0: no symbols (D13), a worker's trailer *)
          destruct (DZHeader.pair_deflate_trailer _ _ _ _ Hrel2 Hpost Hroom2 Hok2) as (t' & E & H & _).
          exists t'. split; [exact E | exact H].
        - (* levels 1-9: live symbols, a worker's trailer; wrap = 1 from mt_inv *)
          destruct (dc_bits c0 _ HDC2 (Hfd eq_refl)) as [Hbv Hlbs].
          exact (DZTrailLive.pair_deflate_trailer_live _ _ _ _ Hrel2 Hroom2 Hok2
                   ltac:(rewrite Hw2; exact (mt_wrap _ Hpost)) Hbv Hlbs). }
      destruct Htr as (t' & Et' & Hs').
      exists (snd (SDfl.deflate_trailer (DS.set_status s1 DS.FINISH_STATE))), t'.
      split; [exact Et'|]. split; [reflexivity | exact (dst_rel_strm _ _ _ _ Hs')].
Qed.

Print Assumptions br_blocks_finish.
