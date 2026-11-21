(** * Bridge.DEmit.BrDeflate — pair D7 of PAIRS.md: one [deflate(Z_FINISH)] call from the
    fresh state, S5 vs RT.

    S5's [deflate_core s 4] against RT's [deflate 4 t] when the stream has not started
    ([INIT_STATE], empty queue and bit buffer, no symbols, empty window, room in the output, the
    zlib wrapper): compress_fuzzer's one call.  Both pass the same checks, set [last_flush],
    write the zlib header (a worker's pair D9, [DZHeader.pair_zlib_header]) and either return
    [Z_OK] at once (the header bytes did not fit) or run the block driver (pair D8,
    [BrBlocks.br_blocks_finish]).

    The two unfoldings of the call ([s5_core_init], [rt_deflate_init]) are stated over abstract
    states and used by [rewrite], so no conversion ever evaluates a model on a concrete state.
    The pairs' S5 side conditions come from S5's own safety proof: [DC] at the entry, and
    [RefDeflSafeI4.hdr_zlib] after the header (the post-header state is [ST]), through
    [BrTopDefs]' [dc_room], [fp_ok_of_DC], [st_inv_of_DC] (level 0) and [em_inv_of_DC]
    (levels 1-9). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Deflate DeflateSafe
  RefDeflateRel RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface BrDispatch BrTopDefs BrBlocks BrDFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DZHeader.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module DSf := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.

(* ------------------------------------------------------------------------- *)
(* 1.  The two calls, unfolded once over abstract states                     *)
(* ------------------------------------------------------------------------- *)

Lemma s5_core_init : forall s,
  SDfl.deflateStateCheck s = false -> DS.cs_avail_out (DS.ds_strm s) <> 0 ->
  DS.ds_status s = DS.INIT_STATE -> DS.ds_pending s = 0 -> DS.ds_wrap s = 1 ->
  SDfl.deflate_core s 4
  = (let '(s2, r) := SDfl.deflate_zlib_header (DS.set_last_flush s 4) in
     match r with Some rc => (s2, rc) | None =>
     let '(s3, r3) := if Z.eqb (DS.ds_status s2) DS.GZIP_STATE then SDfl.deflate_gzip_header s2 else (s2, None) in
     match r3 with Some rc => (s3, rc) | None => s5_tail s3 4 end end).
Proof.
  intros s Hc Ha Hst Hp Hw.
  assert (E1 : (DS.cs_avail_out (DS.ds_strm s) =? 0) = false) by (apply Z.eqb_neq; exact Ha).
  unfold SDfl.deflate_core.
  rewrite Hc, E1.
  change (Z.ltb Z_BLOCK 4) with false. change (Z.ltb 4 0) with false. change (Z.eqb 4 Z_FINISH) with true.
  repeat progress (cbn [orb andb negb]; autorewrite with s5f_last_flush;
                   rewrite ?Hp, ?Hst, ?Hw, ?Z.eqb_refl, ?andb_false_r;
                   try change (Z.eqb 0 0) with true;
                   try change (Z.eqb DS.INIT_STATE DS.FINISH_STATE) with false;
                   try change (Z.eqb 1 0) with false).
  reflexivity.
Qed.

Lemma rt_deflate_init : forall t,
  RD.zs_availout (RD.d_strm t) <> 0 -> RD.d_status t = RD.INIT_STATE ->
  ZBitsOut.bw_out (RT.ts_bw (RD.d_ts t)) = [] -> RD.d_wrap t = 1 ->
  RD.deflate 4 t
  = (let t2 := RD.flush_pending (RD.zlib_header (RD.setD_lastflush 4 t)) in
     if negb (Chunk.zlen (ZBitsOut.bw_out (RT.ts_bw (RD.d_ts t2))) =? 0)
     then RD.DfRet Base.Z_OK (RD.setD_lastflush (-1) t2)
     else RD.deflate_run 4 t2).
Proof.
  intros t Ha Hst Hbw Hw.
  assert (E1 : (RD.zs_availout (RD.d_strm t) =? 0) = false) by (apply Z.eqb_neq; exact Ha).
  unfold RD.deflate, RD.deflate_body.
  rewrite E1.
  change (Z.ltb Base.Z_BLOCK 4) with false. change (Z.ltb 4 0) with false. change (Z.eqb 4 Base.Z_FINISH) with true.
  repeat progress (cbn [orb andb negb RD.setD_lastflush RD.setD_status RD.d_status RD.d_wrap RD.d_ts RD.d_strm];
                   rewrite ?Hst, ?Hw, ?Hbw, ?Z.eqb_refl, ?andb_false_r;
                   try change (Chunk.zlen []) with 0;
                   try change (Z.eqb 0 0) with true;
                   try change (Z.eqb RD.INIT_STATE RD.FINISH_STATE) with false;
                   try change (Z.eqb 1 0) with false).
  reflexivity.
Qed.

(** RT's header and flush leave what [mt_inv] reads, and the symbol count, alone. *)
Lemma rt_hdr_frame : forall t,
  let t2 := RD.flush_pending (RD.zlib_header t) in
  RD.d_cfg t2 = RD.d_cfg t /\ RD.d_wrap t2 = RD.d_wrap t /\ RD.d_ls t2 = RD.d_ls t
  /\ RD.zs_in (RD.d_strm t2) = RD.zs_in (RD.d_strm t) /\ RD.zs_done (RD.d_strm t2) = RD.zs_done (RD.d_strm t)
  /\ RD.zs_totalin (RD.d_strm t2) = RD.zs_totalin (RD.d_strm t)
  /\ RT.ts_symnext (RD.d_ts t2) = RT.ts_symnext (RD.d_ts t).
Proof.
  intros t. cbv zeta.
  destruct (rt_flush_pending_frame (RD.zlib_header t))
    as (F1 & _ & _ & F4 & F5 & F6 & F7 & F8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F19 & _).
  rewrite F1, F4, F5, F6, F7, F8, F19.
  unfold RD.zlib_header. cbv zeta.
  destruct (negb (RD.ls_strstart (RD.d_ls t) =? 0)); repeat split; reflexivity.
Qed.

(** An empty bit buffer stays empty through the header (whole bytes) and its flush. *)
Lemma bw_flush_valid0 : forall b, ZBitsOut.bw_valid b = 0 -> ZBitsOut.bw_flush b = b.
Proof. intros b H. unfold ZBitsOut.bw_flush. rewrite H. reflexivity. Qed.

Lemma rt_hdr_valid : forall t, ZBitsOut.bw_valid (RT.ts_bw (RD.d_ts t)) = 0 ->
  ZBitsOut.bw_valid (RT.ts_bw (RD.d_ts (RD.flush_pending (RD.zlib_header t)))) = 0.
Proof.
  intros t H.
  assert (H1 : ZBitsOut.bw_valid (RT.ts_bw (RD.d_ts (RD.zlib_header t))) = 0).
  { unfold RD.zlib_header. cbv zeta. destruct (negb (RD.ls_strstart (RD.d_ls t) =? 0)); exact H. }
  unfold RD.flush_pending, RT.tr_flush_bits. cbv zeta.
  rewrite (bw_flush_valid0 _ H1).
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; exact H1.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The pair                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem br_deflate_entry : forall c0 s t pre_out pre_in,
  SI2.C0OK' c0 -> DS.ds_strm s = c0 -> SI1.DC c0 s ->
  DS.cs_total_out c0 + DS.cs_avail_out c0 + 2 ^ 17 < 2 ^ 64 -> 0 < DS.cs_avail_out c0 ->
  DS.ds_status s = DS.INIT_STATE -> DS.ds_pending s = 0 -> DS.ds_sym_next s = 0 ->
  DS.ds_lookahead s = 0 -> DS.ds_bi_valid s = 0 -> DS.ds_strstart s = 0 -> DS.ds_block_start s = 0 ->
  dst_rel s t pre_out pre_in -> mt_inv t ->
  exists code t', RD.deflate 4 t = RD.DfRet code t'
    /\ snd (SDfl.deflate_core s 4) = code /\ strm_rel (fst (SDfl.deflate_core s 4)) t' pre_out pre_in.
Proof.
  intros c0 s t pre_out pre_in HC0 Hs0 HDC Hroom Hao Hinit Hp Hsn Hla Hbv Hss Hbs Hrel Hmt.
  pose proof HDC as [[D0 _] _].
  assert (HS : SI4.ST c0 s s) by (split; [exact HDC | reflexivity]).
  destruct (dst_rel_geom _ _ _ _ Hrel) as (_ & Hstat & Hwrap & _).
  destruct (dst_rel_avail _ _ _ _ Hrel) as [Ha _].
  pose proof (mt_wrap _ Hmt) as Hw1.
  assert (Hw0 : DS.ds_wrap s = 1) by (rewrite Hwrap; exact Hw1).
  assert (Ha0 : DS.cs_avail_out (DS.ds_strm s) <> 0) by (rewrite Hs0; lia).
  rewrite (s5_core_init s (RefDeflateRel.df_status _ D0) Ha0 Hinit Hp Hw0).
  rewrite (rt_deflate_init t ltac:(rewrite Ha; exact Ha0) ltac:(rewrite <- Hstat; exact Hinit)
             (dst_rel_pending0 _ _ _ _ Hrel Hp) Hw1).
  set (s1 := DS.set_last_flush s 4).
  set (t1 := RD.setD_lastflush 4 t).
  cbv zeta.
  assert (Hrel1 : dst_rel s1 t1 pre_out pre_in)
    by exact (dst_rel_set_last_flush s t pre_out pre_in 4 4 eq_refl Hrel).
  assert (HS1 : SI4.ST c0 s s1) by exact (SI4.ST_set_last_flush c0 s s 4 HS ltac:(lia)).
  assert (HDC1 : SI1.DC c0 s1) by exact (SI1.DC_set_last_flush c0 s 4 ltac:(lia) HDC).
  (* pair D9, the header *)
  pose proof (DZHeader.pair_zlib_header s1 t1 pre_out pre_in Hrel1 Hsn (dc_room c0 s1 8 HDC1 Hp ltac:(lia))
                (fp_ok_of_DC c0 s1 (SI2.c0'_ok _ HC0) HDC1 Hroom)) as Hh.
  cbv zeta in Hh. destruct Hh as (Hrel2 & Hsnd & Hsn2).
  revert Hrel2 Hsnd Hsn2.
  destruct (negb (Chunk.zlen (ZBitsOut.bw_out (RT.ts_bw (RD.d_ts (RD.flush_pending (RD.zlib_header t1))))) =? 0))
    eqn:Enz; intros Hrel2 Hsnd Hsn2; cbv beta iota;
    destruct (SDfl.deflate_zlib_header s1) as [s2 r] eqn:Eh; rewrite ?Eh in Hsnd, Hrel2, Hsn2;
    cbn [fst snd] in Hsnd, Hrel2, Hsn2; subst r; cbv beta iota.
  - (* the header bytes did not all fit: Z_OK at once *)
    eexists _, _. split; [reflexivity|]. cbn [fst snd]. split; [reflexivity | exact (dst_rel_strm _ _ _ _ Hrel2)].
  - (* the header is out: the block driver *)
    destruct (SI4.hdr_zlib c0 s HC0 Hs0 D0 s1 HS1 Hp Hinit) as (_ & HS2 & Hbusy & _ & _ & Hla2 & _).
    rewrite DSf.deflate_zlib_header_eq in Eh. cbv zeta in Eh. revert Eh.
    destruct (negb (DS.ds_pending (DL.flush_pending (DSf.zhdr_st s1)) =? 0)) eqn:Ep; intros Eh; [discriminate Eh|].
    injection Eh as Es2. subst s2.
    apply negb_false_iff, Z.eqb_eq in Ep.
    rewrite Hbusy. change (Z.eqb DS.BUSY_STATE DS.GZIP_STATE) with false. cbv beta iota.
    set (s2 := DL.flush_pending (DSf.zhdr_st s1)) in *.
    set (t2 := RD.flush_pending (RD.zlib_header t1)) in *.
    destruct (rt_hdr_frame t1) as (F1 & F2 & F3 & F4 & F5 & F6 & _).
    assert (Hmt2 : mt_inv t2) by exact (mt_inv_frame t1 t2 F1 F2 F3 F4 F5 F6 (mt_inv_set_lastflush t 4 Hmt)).
    assert (Hbv2 : DS.ds_bi_valid s2 = 0).
    { rewrite (dst_rel_bivalid _ _ _ _ Hrel2).
      refine (rt_hdr_valid t1 _). change (RD.d_ts t1) with (RD.d_ts t).
      rewrite <- (dst_rel_bivalid _ _ _ _ Hrel). exact Hbv. }
    destruct (dst_rel_geom _ _ _ _ Hrel2) as (Hlev2 & _ & _ & _).
    pose proof (mt_level _ Hmt2) as HL2.
    (* the header leaves the window alone: [strstart], [block_start] read through both relations *)
    assert (Hss2 : DS.ds_strstart s2 = 0 /\ DS.ds_block_start s2 = 0).
    { pose proof Hrel as (_ & Hz1 & _). pose proof Hrel2 as (_ & Hz2 & _).
      unfold lz_rel in Hz1, Hz2. cbv zeta in Hz1, Hz2.
      assert (Els : RD.d_ls t2 = RD.d_ls t) by exact F3. rewrite Els in Hz2.
      destruct Hz1 as (_ & _ & _ & _ & _ & _ & _ & _ & B1 & _ & _ & _ & S1 & _).
      destruct Hz2 as (_ & _ & _ & _ & _ & _ & _ & _ & B2 & _ & _ & _ & S2 & _).
      split; [rewrite S2, <- S1; exact Hss | rewrite B2, <- B1; exact Hbs]. }
    assert (Hblk : blk_pre (RC.dg_level (RD.d_cfg t2)) s2).
    { unfold blk_pre. destruct (Z.eqb_spec (RC.dg_level (RD.d_cfg t2)) 0) as [E0|E0].
      - split; [exact (st_inv_of_DC c0 s2 (SI2.c0'_ok _ HC0) (proj1 HS2) Ep Hbv2 Hroom)|].
        split; [rewrite Hla2; exact Hla|]. split; [exact Hsn2 | exact Hss2].
      - exact (em_inv_of_DC c0 s2 (SI2.c0'_ok _ HC0) (proj1 HS2) Ep Hsn2 ltac:(lia) Hroom). }
    assert (Hst2 : DS.ds_status s2 <> DS.FINISH_STATE) by (rewrite Hbusy; unfold DS.BUSY_STATE, DS.FINISH_STATE; lia).
    exact (br_blocks_finish c0 s s2 t2 pre_out pre_in HC0 HS2 Hroom Ep Hst2 Hrel2 Hmt2 Hblk).
Qed.

Print Assumptions br_deflate_entry.
