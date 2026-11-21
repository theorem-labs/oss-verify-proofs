(** * G5Chain — the one-call [deflate(Z_FINISH)] plumbing, stage by stage.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G5, part 3.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    Four shape lemmas, one per band of [deflate]'s control flow, each
    stated with exactly the premises that band reads — so the per-face
    assemblies (zlib/raw/gzip) share them:

      A1  [deflate] -> [deflate_body]      (the entry checks)
      A2  [deflate_body] -> [deflate_run]  (the zlib header, drained)
      A3  [deflate_run] at BUSY -> the dispatch match over [deflate_slow]
      A4  [deflate_trailer] at wrap 1      (adler bytes, drained)      *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees CresChain
  CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac dsimp :=
  cbn [d_cfg d_status d_lastflush d_wrap d_ts d_ls d_strm
       setD_cfg setD_status setD_lastflush setD_wrap setD_ts setD_ls
       setD_strm
       zs_in zs_done zs_out zs_availout zs_totalin zs_totalout zs_adler
       zs_datatype
       setZ_in setZ_done setZ_out setZ_availout setZ_totalin setZ_totalout
       setZ_adler setZ_datatype
       fst snd].

(** ** A1: the entry checks pass and [deflate_body] runs *)

Lemma deflate_entry : forall s,
  d_status s <> FINISH_STATE ->
  zs_availout (d_strm s) <> 0 ->
  bw_out (ts_bw (d_ts s)) = [] ->
  deflate Z_FINISH s = deflate_body Z_FINISH (setD_lastflush Z_FINISH s).
Proof.
  intros s Hst Havo Hbw.
  unfold deflate.
  change (Z.ltb Z_BLOCK Z_FINISH) with false.
  change (Z.ltb Z_FINISH 0) with false.
  cbn [orb].
  rewrite (proj2 (Z.eqb_neq (d_status s) FINISH_STATE) Hst).
  cbn [andb].
  rewrite (proj2 (Z.eqb_neq (zs_availout (d_strm s)) 0) Havo).
  cbv iota.
  assert (Ebw : zlen (bw_out (ts_bw (d_ts (setD_lastflush Z_FINISH s)))) = 0)
    by (dsimp; rewrite Hbw; reflexivity).
  rewrite Ebw.
  change (Z.eqb 0 0) with true. cbn [negb]. cbv iota.
  change (negb (Z.eqb Z_FINISH Z_FINISH)) with false.
  rewrite !andb_false_r.
  cbv iota. reflexivity.
Qed.

(** ** A2: the zlib header (INIT state, wrap 1) is written and drained *)

Lemma deflate_body_header : forall s,
  d_status s = INIT_STATE ->
  d_wrap s = 1 ->
  bw_out (ts_bw (d_ts s)) = [] ->
  bw_valid (ts_bw (d_ts s)) = 0 ->
  ls_strstart (d_ls s) = 0 ->
  2 <= zs_availout (d_strm s) ->
  deflate_body Z_FINISH s
  = deflate_run Z_FINISH (flush_pending (zlib_header s)).
Proof.
  intros s Hst Hwrap Hbw Hbv Hss Havo.
  unfold deflate_body. cbv zeta.
  rewrite Hst, Hwrap.
  change (Z.eqb INIT_STATE FINISH_STATE) with false.
  change (Z.eqb 1 0) with false.
  cbn [andb]. rewrite ?andb_false_r. cbv iota.
  rewrite ?Hst.
  change (Z.eqb INIT_STATE INIT_STATE) with true. cbv iota.
  (* the header leaves exactly two pending bytes, and the drain takes
     both because avail_out has room *)
  assert (Hpend : exists b0 b1,
            bw_out (ts_bw (d_ts (zlib_header s))) = [b0; b1]).
  { unfold zlib_header. cbv zeta.
    rewrite Hss.
    change (negb (Z.eqb 0 0)) with false. cbv iota.
    dsimp.
    unfold putShortMSB, put_byte, bw_put_byte, set_bw.
    cbn [ts_bw bw_out].
    rewrite Hbw. cbn [app].
    eexists. eexists. reflexivity. }
  destruct Hpend as (b0 & b1 & Hpend).
  assert (Havo' : zs_availout (d_strm (zlib_header s))
                  = zs_availout (d_strm s)).
  { unfold zlib_header. cbv zeta. dsimp. reflexivity. }
  assert (Hdrained : zlen (bw_out (ts_bw (d_ts (flush_pending
                        (zlib_header s))))) = 0).
  { unfold flush_pending. cbv zeta.
    (* tr_flush_bits on an empty register is the identity on the queue *)
    assert (Hfb : bw_out (ts_bw (tr_flush_bits (d_ts (zlib_header s))))
                  = [b0; b1]).
    { unfold tr_flush_bits, bw_flush.
      assert (Hbv' : bw_valid (ts_bw (d_ts (zlib_header s)))
                     = bw_valid (ts_bw (d_ts s))).
      { unfold zlib_header. cbv zeta. rewrite Hss.
        change (negb (Z.eqb 0 0)) with false. cbv iota. dsimp.
        unfold putShortMSB, put_byte, bw_put_byte, set_bw.
        cbn [ts_bw bw_valid]. reflexivity. }
      rewrite Hbv', Hbv.
      change (Z.ltb 0 0) with false. cbv iota.
      cbn [set_bw ts_bw bw_out].
      exact Hpend. }
    rewrite Hfb.
    change (zlen [b0; b1]) with 2.
    rewrite Havo'.
    destruct (Z.ltb_spec (zs_availout (d_strm s)) 2) as [H|H]; [lia|].
    destruct (Z.eqb_spec 2 0) as [E|E]; [lia|].
    dsimp.
    cbn [set_bw ts_bw bw_out].
    change (Z.to_nat 2) with 2%nat.
    cbn [skipn]. reflexivity. }
  rewrite Hdrained.
  change (Z.eqb 0 0) with true. cbn [negb]. cbv iota.
  reflexivity.
Qed.


(** ** A3: the BUSY run dispatches to [deflate_slow] and plumbs its result *)

Lemma dispatch_slow : forall s,
  4 <= dg_level (d_cfg s) ->
  dg_level (d_cfg s) <> 0 ->
  dg_strategy (d_cfg s) = 0 ->
  dispatch Z_FINISH s = deflate_slow Z_FINISH s.
Proof.
  intros s Hl4 Hl0 Hstrat.
  unfold dispatch. cbv zeta.
  rewrite (proj2 (Z.eqb_neq (dg_level (d_cfg s)) 0) Hl0).
  rewrite Hstrat.
  change (Z.eqb 0 Z_HUFFMAN_ONLY) with false.
  change (Z.eqb 0 Z_RLE) with false.
  cbv iota.
  unfold cfg_func.
  rewrite (proj2 (Z.eqb_neq (dg_level (d_cfg s)) 0) Hl0).
  rewrite (proj2 (Z.leb_gt (dg_level (d_cfg s)) 3) ltac:(lia)).
  cbv iota. reflexivity.
Qed.

(** The [deflate_run] arms at BUSY, one lemma per [BlockState] the slow
    path can return at [Z_FINISH]. *)

Lemma deflate_run_arm : forall s bs sa,
  d_status s = BUSY_STATE ->
  dispatch Z_FINISH s = (bs, sa) ->
  deflate_run Z_FINISH s
  = match bs with
    | NeedMore =>
        DfRet Z_OK (if Z.eqb (zs_availout (d_strm sa)) 0
                    then setD_lastflush (-1) sa else sa)
    | FinishStarted =>
        DfRet Z_OK
          (if Z.eqb (zs_availout (d_strm (setD_status FINISH_STATE sa))) 0
           then setD_lastflush (-1) (setD_status FINISH_STATE sa)
           else setD_status FINISH_STATE sa)
    | FinishDone =>
        if Z.leb (d_wrap (setD_status FINISH_STATE sa)) 0
        then DfRet Z_STREAM_END (setD_status FINISH_STATE sa)
        else deflate_trailer (setD_status FINISH_STATE sa)
    | BlockDone =>
        let sc := setD_ts (tr_stored_block [] 0 0 (d_ts sa)) sa in
        let se := flush_pending sc in
        if Z.eqb (zs_availout (d_strm se)) 0
        then DfRet Z_OK (setD_lastflush (-1) se)
        else if Z.leb (d_wrap se) 0 then DfRet Z_STREAM_END se
             else deflate_trailer se
    end.
Proof.
  intros s bs sa Hst Edisp.
  unfold deflate_run.
  rewrite Hst.
  change (Z.eqb BUSY_STATE FINISH_STATE) with false.
  cbn [andb]. cbv iota.
  change (Z.eqb BUSY_STATE INIT_STATE) with false.
  cbn [andb]. cbv iota.
  rewrite ?Hst.
  change (Z.eqb BUSY_STATE INIT_STATE) with false. cbv iota.
  change (Z.eqb BUSY_STATE GZIP_STATE) with false. cbv iota.
  change (negb (Z.eqb Z_FINISH Z_NO_FLUSH)) with true.
  change (Z.eqb BUSY_STATE FINISH_STATE) with false.
  cbn [negb andb].
  rewrite !orb_true_r.
  cbv iota.
  rewrite Edisp.
  cbv beta iota zeta.
  destruct bs.
  - reflexivity.
  - (* BlockDone: reduce the flush-selector at Z_FINISH *)
    change (Z.eqb Z_FINISH Z_PARTIAL_FLUSH) with false.
    change (negb (Z.eqb Z_FINISH Z_BLOCK)) with true.
    change (Z.eqb Z_FINISH Z_FULL_FLUSH) with false.
    cbv iota.
    change (negb (Z.eqb Z_FINISH Z_FINISH)) with false.
    cbv iota. reflexivity.
  - change (negb (Z.eqb Z_FINISH Z_FINISH)) with false. cbv iota.
    reflexivity.
  - reflexivity.
Qed.


(** ** A4: the zlib trailer — four adler bytes, drained, [Z_STREAM_END] *)

Lemma deflate_trailer_zlib : forall s,
  d_wrap s = 1 ->
  bw_out (ts_bw (d_ts s)) = [] ->
  bw_valid (ts_bw (d_ts s)) = 0 ->
  4 <= zs_availout (d_strm s) ->
  let ad := zs_adler (d_strm s) in
  let tb := [u8 (Z.shiftr (Z.shiftr ad 16) 8);
             u8 (Z.land (Z.shiftr ad 16) 255);
             u8 (Z.shiftr (Z.land ad 65535) 8);
             u8 (Z.land (Z.land ad 65535) 255)] in
  let s' := setD_wrap (-1)
              (flush_pending
                 (setD_ts (putShortMSB (Z.land ad 65535)
                             (putShortMSB (Z.shiftr ad 16) (d_ts s))) s)) in
  deflate_trailer s = DfRet Z_STREAM_END s'
  /\ zs_out (d_strm s') = zs_out (d_strm s) ++ tb
  /\ d_wrap s' = -1
  /\ zs_in (d_strm s') = zs_in (d_strm s)
  /\ zs_done (d_strm s') = zs_done (d_strm s)
  /\ zs_adler (d_strm s') = zs_adler (d_strm s)
  /\ zs_totalin (d_strm s') = zs_totalin (d_strm s).
Proof.
  intros s Hwrap Hbw Hbv Havo.
  cbv zeta.
  set (ad := zs_adler (d_strm s)) in *.
  set (tst := putShortMSB (Z.land ad 65535)
                (putShortMSB (Z.shiftr ad 16) (d_ts s))) in *.
  set (sc := setD_ts tst s) in *.
  assert (Hpend : bw_out (ts_bw tst)
                  = [u8 (Z.shiftr (Z.shiftr ad 16) 8);
                     u8 (Z.land (Z.shiftr ad 16) 255);
                     u8 (Z.shiftr (Z.land ad 65535) 8);
                     u8 (Z.land (Z.land ad 65535) 255)]).
  { unfold tst, putShortMSB, set_bw, bw_put_byte.
    cbn [ts_bw bw_out].
    rewrite Hbw. reflexivity. }
  assert (Hval : bw_valid (ts_bw tst) = 0).
  { unfold tst, putShortMSB, set_bw, bw_put_byte.
    cbn [ts_bw bw_valid]. exact Hbv. }
  assert (Ects : d_ts sc = tst) by reflexivity.
  assert (Ecstrm : d_strm sc = d_strm s) by reflexivity.
  (* the flushed queue and moved bytes *)
  assert (Hfb : bw_out (ts_bw (tr_flush_bits (d_ts sc)))
                = bw_out (ts_bw tst)).
  { unfold tr_flush_bits, bw_flush.
    rewrite Ects, Hval.
    change (Z.ltb 0 0) with false. cbv iota.
    cbn [set_bw ts_bw bw_out]. reflexivity. }
  destruct (flush_pending_frame sc)
    as (Fls & Fcfg & Fwrap & Fstat & Fin & Fdone & Fad & Fti & Fdt
        & Fsb & Fsn & Ftr & Favo).
  (* the drained shape of [flush_pending sc] *)
  assert (Hflush :
      zs_out (d_strm (flush_pending sc)) = zs_out (d_strm s)
        ++ [u8 (Z.shiftr (Z.shiftr ad 16) 8);
            u8 (Z.land (Z.shiftr ad 16) 255);
            u8 (Z.shiftr (Z.land ad 65535) 8);
            u8 (Z.land (Z.land ad 65535) 255)]
      /\ bw_out (ts_bw (d_ts (flush_pending sc))) = []).
  { unfold flush_pending. cbv zeta.
    rewrite Hfb, Hpend.
    match goal with
    | |- context [zlen ?L] => change (zlen L) with 4
    end.
    rewrite Ecstrm.
    destruct (Z.ltb_spec (zs_availout (d_strm s)) 4) as [H|H]; [lia|].
    change (Z.eqb 4 0) with false. cbv iota.
    dsimp.
    cbn [set_bw ts_bw bw_out].
    change (Z.to_nat 4) with 4%nat.
    cbn [skipn firstn].
    split; reflexivity. }
  destruct Hflush as (Hout & Hempty).
  repeat apply conj.
  - (* the equation *)
    unfold deflate_trailer. cbv zeta.
    rewrite Hwrap.
    change (Z.eqb 1 2) with false. cbv iota.
    fold ad. fold tst. fold sc.
    assert (Ewsc : d_wrap sc = 1) by (unfold sc; dsimp; exact Hwrap).
    rewrite Fwrap, Ewsc.
    change (Z.ltb 0 1) with true. cbv iota.
    dsimp.
    rewrite Hempty.
    change (zlen (@nil Z)) with 0.
    change (Z.eqb 0 0) with true. cbn [negb]. cbv iota.
    reflexivity.
  - dsimp. exact Hout.
  - dsimp. reflexivity.
  - dsimp. rewrite Fin, Ecstrm. reflexivity.
  - dsimp. rewrite Fdone, Ecstrm. reflexivity.
  - dsimp. rewrite Fad, Ecstrm. reflexivity.
  - dsimp. rewrite Fti, Ecstrm. reflexivity.
Qed.

Print Assumptions deflate_entry.
Print Assumptions deflate_body_header.
Print Assumptions dispatch_slow.
Print Assumptions deflate_run_arm.
Print Assumptions deflate_trailer_zlib.
