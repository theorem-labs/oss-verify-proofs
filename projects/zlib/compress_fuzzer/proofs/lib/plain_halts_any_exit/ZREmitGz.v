(** * ZREmitGz — the gzip-side plumbing for the level-9 emitter face.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    The walk/body core is already wrap-generic; what gzip adds is the
    10-byte header ([deflate_body]'s GZIP arm) and the 8-byte
    little-endian CRC32+ISIZE trailer ([deflate_trailer]'s wrap-2 arm) —
    the mirrors of G5Chain's A2/A4.  Includes the general
    [flush_pending_all] drain (any queue that fits [avail_out]). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees
  CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwDrain ZREmitShell.
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

Local Ltac tsimp :=
  cbn [ts_bw ts_symbuf ts_symnext ts_trees ts_maxcode set_bw
       bw_out bw_buf bw_valid].

(* ==========================================================================
   1.  The general drain: an aligned queue that fits avail_out empties.
   ========================================================================== *)

Lemma flush_pending_all : forall s,
  bw_valid (ts_bw (d_ts s)) = 0 ->
  zlen (bw_out (ts_bw (d_ts s))) <= zs_availout (d_strm s) ->
  zs_out (d_strm (flush_pending s))
    = zs_out (d_strm s) ++ bw_out (ts_bw (d_ts s))
  /\ zs_availout (d_strm (flush_pending s))
     = zs_availout (d_strm s) - zlen (bw_out (ts_bw (d_ts s)))
  /\ bw_out (ts_bw (d_ts (flush_pending s))) = []
  /\ bw_valid (ts_bw (d_ts (flush_pending s))) = 0
  /\ d_status (flush_pending s) = d_status s
  /\ d_wrap (flush_pending s) = d_wrap s
  /\ d_cfg (flush_pending s) = d_cfg s
  /\ d_ls (flush_pending s) = d_ls s
  /\ zs_in (d_strm (flush_pending s)) = zs_in (d_strm s)
  /\ zs_done (d_strm (flush_pending s)) = zs_done (d_strm s)
  /\ zs_totalin (d_strm (flush_pending s)) = zs_totalin (d_strm s)
  /\ zs_adler (d_strm (flush_pending s)) = zs_adler (d_strm s)
  /\ ts_symbuf (d_ts (flush_pending s)) = ts_symbuf (d_ts s)
  /\ ts_symnext (d_ts (flush_pending s)) = ts_symnext (d_ts s)
  /\ ts_trees (d_ts (flush_pending s)) TK_L = ts_trees (d_ts s) TK_L
  /\ ts_trees (d_ts (flush_pending s)) TK_D = ts_trees (d_ts s) TK_D.
Proof.
  intros s Hbv Hfit.
  assert (Hfbw : ts_bw (tr_flush_bits (d_ts s)) = ts_bw (d_ts s))
    by (unfold tr_flush_bits; tsimp; apply bw_flush_valid0; exact Hbv).
  unfold flush_pending. cbv zeta.
  rewrite Hfbw.
  rewrite (proj2 (Z.ltb_ge (zs_availout (d_strm s))
                           (zlen (bw_out (ts_bw (d_ts s))))) Hfit).
  destruct (Z.eqb (zlen (bw_out (ts_bw (d_ts s)))) 0) eqn:E0.
  - apply Z.eqb_eq in E0.
    apply zlen_nil in E0.
    dsimp.
    rewrite ?E0, ?Hfbw.
    repeat split;
      first [ reflexivity
            | rewrite app_nil_r; reflexivity
            | change (zlen (@nil Z)) with 0; lia
            | exact Hbv
            | rewrite E0; reflexivity
            | (unfold tr_flush_bits; tsimp; rewrite ?E0; reflexivity) ].
  - assert (Efull : firstn (Z.to_nat (zlen (bw_out (ts_bw (d_ts s)))))
                      (bw_out (ts_bw (d_ts s)))
                    = bw_out (ts_bw (d_ts s))).
    { unfold zlen. rewrite Nat2Z.id. apply firstn_all. }
    assert (Eskip : skipn (Z.to_nat (zlen (bw_out (ts_bw (d_ts s)))))
                      (bw_out (ts_bw (d_ts s))) = []).
    { unfold zlen. rewrite Nat2Z.id. apply skipn_all. }
    dsimp. tsimp.
    rewrite ?Efull, ?Eskip, ?Hfbw.
    repeat split;
      first [ reflexivity
            | lia
            | exact Hbv
            | (unfold tr_flush_bits; tsimp; reflexivity) ].
Qed.

(* ==========================================================================
   2.  The ten header bytes, pinned at level 9 / strategy 0.
   ========================================================================== *)

Lemma gzip_header_pinned : forall s,
  dg_level (d_cfg s) = 9 ->
  gzip_header s
  = setD_status BUSY_STATE
      (setD_ts
         (put_byte OS_CODE (put_byte 2 (put_byte 0 (put_byte 0
            (put_byte 0 (put_byte 0 (put_byte 0 (put_byte 8
              (put_byte 139 (put_byte 31
                (d_ts (setD_strm (setZ_adler (crc32_z 0 true 0 [])
                                    (d_strm s)) s))))))))))))
         (setD_strm (setZ_adler (crc32_z 0 true 0 []) (d_strm s)) s)).
Proof.
  intros s Hlvl.
  unfold gzip_header. cbv zeta.
  rewrite Hlvl.
  reflexivity.
Qed.

(** GZIP-state entry: the ten bytes are written and drained. *)
Lemma deflate_body_gzheader : forall s,
  d_status s = GZIP_STATE ->
  bw_out (ts_bw (d_ts s)) = [] ->
  bw_valid (ts_bw (d_ts s)) = 0 ->
  10 <= zs_availout (d_strm s) ->
  deflate_body Z_FINISH s
  = deflate_run Z_FINISH (flush_pending (gzip_header s)).
Proof.
  intros s Hst Hbw Hbv Havo.
  unfold deflate_body. cbv zeta.
  rewrite Hst.
  change (Z.eqb GZIP_STATE FINISH_STATE) with false.
  cbn [andb]. cbv iota.
  change (Z.eqb GZIP_STATE INIT_STATE) with false.
  cbn [andb]. rewrite ?andb_false_l. cbv iota.
  rewrite ?Hst.
  change (Z.eqb GZIP_STATE INIT_STATE) with false. cbv iota.
  change (Z.eqb GZIP_STATE GZIP_STATE) with true. cbv iota.
  assert (Hpend : bw_out (ts_bw (d_ts (gzip_header s)))
                  = [31; 139; 8; 0; 0; 0; 0; 0;
                     u8 (if Z.eqb (dg_level (d_cfg s)) 9 then 2
                         else if (Z.leb Z_HUFFMAN_ONLY (dg_strategy (d_cfg s)))
                                 || (Z.ltb (dg_level (d_cfg s)) 2)
                              then 4 else 0);
                     OS_CODE]).
  { unfold gzip_header. cbv zeta. dsimp.
    unfold put_byte, bw_put_byte. tsimp.
    rewrite Hbw. reflexivity. }
  assert (Hval : bw_valid (ts_bw (d_ts (gzip_header s))) = 0).
  { unfold gzip_header. cbv zeta. dsimp.
    unfold put_byte, bw_put_byte. tsimp. exact Hbv. }
  assert (Havoh : zs_availout (d_strm (gzip_header s))
                  = zs_availout (d_strm s))
    by (unfold gzip_header; cbv zeta; dsimp; reflexivity).
  destruct (flush_pending_all (gzip_header s) Hval
              ltac:(rewrite Hpend, Havoh; unfold zlen; cbn [length];
                    change (Z.of_nat 10) with 10; lia))
    as (_ & _ & Hdr & _).
  rewrite Hdr.
  change (zlen (@nil Z)) with 0.
  change (negb (Z.eqb 0 0)) with false. cbv iota.
  reflexivity.
Qed.

(* ==========================================================================
   3.  The gzip trailer: CRC32 then ISIZE, both little-endian, drained.
   ========================================================================== *)

Lemma deflate_trailer_gzip : forall s,
  d_wrap s = 2 ->
  bw_out (ts_bw (d_ts s)) = [] ->
  bw_valid (ts_bw (d_ts s)) = 0 ->
  8 <= zs_availout (d_strm s) ->
  let ad := zs_adler (d_strm s) in
  let ti := zs_totalin (d_strm s) in
  let tb := [u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
             u8 (Z.shiftr ad 24);
             u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
             u8 (Z.shiftr ti 24)] in
  let s' := setD_wrap (-2)
              (flush_pending
                 (setD_ts
                    (put_byte (Z.shiftr ti 24) (put_byte (Z.shiftr ti 16)
                      (put_byte (Z.shiftr ti 8) (put_byte ti
                        (put_byte (Z.shiftr ad 24) (put_byte (Z.shiftr ad 16)
                          (put_byte (Z.shiftr ad 8) (put_byte ad
                            (d_ts s)))))))))
                    s)) in
  deflate_trailer s = DfRet Z_STREAM_END s'
  /\ zs_out (d_strm s') = zs_out (d_strm s) ++ tb
  /\ d_wrap s' = -2
  /\ zs_in (d_strm s') = zs_in (d_strm s)
  /\ zs_done (d_strm s') = zs_done (d_strm s)
  /\ zs_adler (d_strm s') = zs_adler (d_strm s)
  /\ zs_totalin (d_strm s') = zs_totalin (d_strm s).
Proof.
  intros s Hwrap Hbw Hbv Havo.
  cbv zeta.
  set (ad := zs_adler (d_strm s)) in *.
  set (ti := zs_totalin (d_strm s)) in *.
  set (tst := put_byte (Z.shiftr ti 24) (put_byte (Z.shiftr ti 16)
                (put_byte (Z.shiftr ti 8) (put_byte ti
                  (put_byte (Z.shiftr ad 24) (put_byte (Z.shiftr ad 16)
                    (put_byte (Z.shiftr ad 8) (put_byte ad
                      (d_ts s))))))))) in *.
  set (sc := setD_ts tst s) in *.
  assert (Hpend : bw_out (ts_bw tst)
                  = [u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
                     u8 (Z.shiftr ad 24);
                     u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
                     u8 (Z.shiftr ti 24)]).
  { unfold tst, put_byte, bw_put_byte. tsimp.
    rewrite Hbw. reflexivity. }
  assert (HvalC : bw_valid (ts_bw (d_ts sc)) = 0).
  { unfold sc. dsimp.
    unfold tst, put_byte, bw_put_byte. tsimp. exact Hbv. }
  assert (HbwC : bw_out (ts_bw (d_ts sc))
                 = [u8 ad; u8 (Z.shiftr ad 8); u8 (Z.shiftr ad 16);
                    u8 (Z.shiftr ad 24);
                    u8 ti; u8 (Z.shiftr ti 8); u8 (Z.shiftr ti 16);
                    u8 (Z.shiftr ti 24)])
    by (unfold sc; dsimp; exact Hpend).
  destruct (flush_pending_all sc HvalC
              ltac:(rewrite HbwC; unfold sc; dsimp;
                    unfold zlen; cbn [length];
                    change (Z.of_nat 8) with 8; lia))
    as (Fout & Favo & Fbw & Fbv & Fstat & Fwrap & Fcfg & Fls & Fin & Fdn
        & Fti & Fad & Fsb & Fsn & FtL & FtD).
  unfold deflate_trailer. cbv zeta.
  rewrite Hwrap.
  change (Z.eqb 2 2) with true. cbv iota.
  fold ad. fold ti. fold tst. fold sc.
  assert (Ewfp : d_wrap (flush_pending sc) = 2).
  { rewrite Fwrap. unfold sc. dsimp. exact Hwrap. }
  rewrite Ewfp.
  change (Z.ltb 0 2) with true. cbv iota.
  change (- 2) with (-2).
  dsimp.
  rewrite Fbw.
  change (zlen (@nil Z)) with 0.
  change (negb (Z.eqb 0 0)) with false. cbv iota.
  split; [reflexivity|].
  split.
  { dsimp. rewrite Fout, HbwC.
    unfold sc. dsimp. reflexivity. }
  split; [dsimp; reflexivity|].
  split; [dsimp; rewrite Fin; unfold sc; dsimp; reflexivity|].
  split; [dsimp; rewrite Fdn; unfold sc; dsimp; reflexivity|].
  split; [dsimp; rewrite Fad; unfold sc; dsimp; reflexivity|].
  dsimp; rewrite Fti; unfold sc; dsimp; reflexivity.
Qed.

Print Assumptions deflate_body_gzheader.
Print Assumptions deflate_trailer_gzip.
