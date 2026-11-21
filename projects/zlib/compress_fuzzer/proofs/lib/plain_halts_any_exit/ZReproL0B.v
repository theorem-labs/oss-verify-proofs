(** * ZReproL0B — config (0, 15) emitter, part B: deflate_stored, the
    trailer, room arithmetic, and the byte-exact shape theorem
    [zr_deflate_l0_shape].  Continues [ZReproL0] (part A: the dst_loop
    characterisation).

    Rests on the 2026-08-19 factoring of [deflate_stored] into
    [dst_win_update]/[dst_highwater]/[dst_tail] (Deflate.v): the original
    monolithic let-tower was kernel-intractable (conversion zeta-expands
    let-towers eagerly; cbv zeta alone OOMs 50 GB), and with the pieces
    FOLDED the tower's zeta stays linear and every projection fact below
    is a small destruct + conversion. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  GtAdlerChunk GtAdlerLoop ZRepro ZReproL0.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   5.  deflate_stored at the level-0 geometry.
   ========================================================================== *)

Definition zr_g0 : DeflGeom := defl_geom_wrap 1 0 15 8 0.

Lemma zr_fuel_ok : forall len aout,
  0 <= len -> len <= aout ->
  (S (Z.to_nat (len / 65535)) <= Z.to_nat (aout / 5) + 3)%nat.
Proof.
  intros len aout Hl Ha.
  assert (Hd : len / 65535 <= aout / 5).
  { transitivity (len / 5).
    - apply Z.div_le_compat_l; lia.
    - apply Z.div_le_mono; lia. }
  assert (H0 : 0 <= len / 65535) by (apply Z.div_pos; lia).
  lia.
Qed.

(** Projection facts for the factored pieces — the only way this file
    looks inside them.  Each is a guard-destruct plus conversion. *)
Lemma d_strm_win_update : forall g used s, d_strm (dst_win_update g used s) = d_strm s.
Proof.
  intros g used s. unfold dst_win_update. destruct (Z.eqb used 0); reflexivity.
Qed.

Lemma d_cfg_win_update : forall g used s, d_cfg (dst_win_update g used s) = d_cfg s.
Proof.
  intros g used s. unfold dst_win_update. destruct (Z.eqb used 0); reflexivity.
Qed.

Lemma d_status_win_update : forall g used s,
  d_status (dst_win_update g used s) = d_status s.
Proof.
  intros g used s. unfold dst_win_update. destruct (Z.eqb used 0); reflexivity.
Qed.

Lemma d_lastflush_win_update : forall g used s,
  d_lastflush (dst_win_update g used s) = d_lastflush s.
Proof.
  intros g used s. unfold dst_win_update. destruct (Z.eqb used 0); reflexivity.
Qed.

Lemma d_wrap_win_update : forall g used s, d_wrap (dst_win_update g used s) = d_wrap s.
Proof.
  intros g used s. unfold dst_win_update. destruct (Z.eqb used 0); reflexivity.
Qed.

Lemma ts_bw_win_update : forall g used s,
  ts_bw (d_ts (dst_win_update g used s)) = ts_bw (d_ts s).
Proof.
  intros g used s. unfold dst_win_update.
  destruct (Z.eqb used 0); [reflexivity|].
  destruct (Z.leb (dg_w_size g) used); [reflexivity|].
  destruct ((Z.leb (ls_windowsize (d_ls s) - ls_strstart (d_ls s)) used)
              && (Z.ltb (ts_matches (d_ts s)) 2)); reflexivity.
Qed.

Lemma d_strm_highwater : forall s, d_strm (dst_highwater s) = d_strm s.
Proof.
  intros s. unfold dst_highwater.
  destruct (Z.ltb (ls_highwater (d_ls s)) (ls_strstart (d_ls s))); reflexivity.
Qed.

Lemma d_cfg_highwater : forall s, d_cfg (dst_highwater s) = d_cfg s.
Proof.
  intros s. unfold dst_highwater.
  destruct (Z.ltb (ls_highwater (d_ls s)) (ls_strstart (d_ls s))); reflexivity.
Qed.

Lemma d_status_highwater : forall s, d_status (dst_highwater s) = d_status s.
Proof.
  intros s. unfold dst_highwater.
  destruct (Z.ltb (ls_highwater (d_ls s)) (ls_strstart (d_ls s))); reflexivity.
Qed.

Lemma d_lastflush_highwater : forall s, d_lastflush (dst_highwater s) = d_lastflush s.
Proof.
  intros s. unfold dst_highwater.
  destruct (Z.ltb (ls_highwater (d_ls s)) (ls_strstart (d_ls s))); reflexivity.
Qed.

Lemma d_wrap_highwater : forall s, d_wrap (dst_highwater s) = d_wrap s.
Proof.
  intros s. unfold dst_highwater.
  destruct (Z.ltb (ls_highwater (d_ls s)) (ls_strstart (d_ls s))); reflexivity.
Qed.

Lemma d_ts_highwater : forall s, d_ts (dst_highwater s) = d_ts s.
Proof.
  intros s. unfold dst_highwater.
  destruct (Z.ltb (ls_highwater (d_ls s)) (ls_strstart (d_ls s))); reflexivity.
Qed.

Lemma DSt_eta : forall s,
  s = mkDSt (d_cfg s) (d_status s) (d_lastflush s) (d_wrap s) (d_ts s)
            (d_ls s) (d_strm s).
Proof. intro s. destruct s. reflexivity. Qed.

Lemma deflate_stored_l0 :
  forall status lastf ts ls xin xdone xout aout tin tout ad dt,
  ts_bw ts = bw_init ->
  ls_strstart ls = ls_blockstart ls ->
  zlen xin + 5 * zr_nblocks xin <= aout ->
  exists ts3 ls3 st',
    deflate_stored Z_FINISH
      (mkDSt zr_g0 status lastf 1 ts ls
         (mkZStrm xin xdone xout aout tin tout ad dt))
    = (FinishDone, mkDSt zr_g0 status lastf 1 ts3 ls3 st')
    /\ ts_bw ts3 = bw_init
    /\ zs_in st' = []
    /\ zs_done st' = xdone ++ map u8 xin
    /\ zs_out st' = xout ++ zr_stored_body (zr_body_fuel xin) xin
    /\ zs_availout st' = aout - (5 * zr_nblocks xin + zlen xin)
    /\ zs_datatype st' = dt
    /\ (forall A, AdWf A ->
          AdlerTracksDone A (mkZStrm xin xdone xout aout tin tout ad dt) ->
          AdlerTracksDone A st').
Proof.
  intros status lastf ts ls xin xdone xout aout tin tout ad dt Hbw Hss Ha.
  pose proof (zlen_nonneg xin) as Hxn.
  pose proof (nblocks_pos xin) as Hnbp.
  unfold deflate_stored. cbv zeta.
  cbn [d_cfg d_strm zs_in zs_availout].
  replace (zmin (dg_pending_buf_size zr_g0 - 5) (dg_w_size zr_g0)) with 32768
    by reflexivity.
  destruct (dst_loop_l0 (Z.to_nat (aout / 5) + 3) xin zr_g0 status lastf ts ls
              xdone xout aout tin tout ad dt Hbw Hss Ha
              ltac:(apply zr_fuel_ok; lia))
    as [st' [Heq [Hin [Hdn [Hout [Hav [Hdt Htr]]]]]]].
  rewrite Heq.
  cbn [fst snd d_strm].
  replace (1 =? 0) with false by reflexivity.
  cbn [negb].
  set (S1 := mkDSt zr_g0 status lastf 1 (set_bw bw_init ts) ls st').
  set (USED := zlen xin - zlen (zs_in st')).
  exists (d_ts (dst_highwater (dst_win_update zr_g0 USED S1))).
  exists (d_ls (dst_highwater (dst_win_update zr_g0 USED S1))).
  exists st'.
  split.
  { f_equal.
    rewrite (DSt_eta (dst_highwater (dst_win_update zr_g0 USED S1))) at 1.
    rewrite d_cfg_highwater, d_cfg_win_update.
    rewrite d_status_highwater, d_status_win_update.
    rewrite d_lastflush_highwater, d_lastflush_win_update.
    rewrite d_wrap_highwater, d_wrap_win_update.
    rewrite d_strm_highwater, d_strm_win_update.
    reflexivity. }
  split.
  { rewrite d_ts_highwater, ts_bw_win_update. subst S1. cbn [d_ts].
    exact (ts_bw_set_bw _ _). }
  split; [exact Hin|].
  split; [exact Hdn|].
  split; [exact Hout|].
  split; [exact Hav|].
  split; [exact Hdt|].
  exact Htr.
Qed.

(* ==========================================================================
   6.  The trailer: 4 adler bytes MSB-first through [putShortMSB], then
       the big-endian bridge to [Chunk.be32].
   ========================================================================== *)

(** The bytes exactly as [deflate_trailer]'s two [putShortMSB]s emit them. *)
Definition zr_put4 (ad : Z) : list Z :=
  [u8 (Z.shiftr (Z.shiftr ad 16) 8); u8 (Z.land (Z.shiftr ad 16) 255);
   u8 (Z.shiftr (Z.land ad 65535) 8); u8 (Z.land (Z.land ad 65535) 255)].

(** [flush_pending] for the four-byte trailer queue. *)
Lemma flush_pending_bw4 :
  forall c1 c2 c3 c4 ts0 cfg status lastf wrap ls st,
  4 <= zs_availout st ->
  flush_pending
    (mkDSt cfg status lastf wrap
       (set_bw {| bw_out := [c1;c2;c3;c4]; bw_buf := 0; bw_valid := 0 |} ts0)
       ls st)
  = mkDSt cfg status lastf wrap (set_bw bw_init ts0) ls
      (setZ_out (zs_out st ++ [c1;c2;c3;c4])
        (setZ_availout (zs_availout st - 4)
          (setZ_totalout (zs_totalout st + 4) st))).
Proof.
  intros c1 c2 c3 c4 ts0 cfg status lastf wrap ls st Hav.
  unfold flush_pending. cbv zeta.
  unfold tr_flush_bits.
  cbn [d_ts d_strm].
  replace (zlen (bw_out (ts_bw (set_bw
             (bw_flush (ts_bw (set_bw {| bw_out := [c1;c2;c3;c4];
                                         bw_buf := 0; bw_valid := 0 |} ts0)))
             (set_bw {| bw_out := [c1;c2;c3;c4];
                        bw_buf := 0; bw_valid := 0 |} ts0)))))
    with 4 by reflexivity.
  destruct (zs_availout st <? 4) eqn:E1; [apply Z.ltb_lt in E1; lia|].
  reflexivity.
Qed.

Lemma deflate_trailer_l0 :
  forall status lastf ts3 ls3 xi xd xo av ti to ad dt,
  ts_bw ts3 = bw_init ->
  4 <= av ->
  deflate_trailer
    (mkDSt zr_g0 status lastf 1 ts3 ls3 (mkZStrm xi xd xo av ti to ad dt))
  = DfRet Z_STREAM_END
      (mkDSt zr_g0 status lastf (-1) (set_bw bw_init ts3) ls3
         (mkZStrm xi xd (xo ++ zr_put4 ad) (av - 4) ti (to + 4) ad dt)).
Proof.
  intros status lastf ts3 ls3 xi xd xo av ti to ad dt Hbw Hav.
  unfold deflate_trailer. cbv zeta.
  cbn [d_wrap d_ts d_strm d_cfg d_status d_lastflush d_ls
       zs_adler zs_availout zs_out zs_totalout].
  replace (1 =? 2) with false by reflexivity.
  unfold putShortMSB.
  rewrite Hbw.
  rewrite !ts_bw_set_bw.
  unfold bw_put_byte, bw_init.
  cbn [bw_out bw_buf bw_valid app].
  unfold setD_ts. zcbn.
  rewrite flush_pending_bw4 by (zcbn; lia).
  zcbn.
  replace (0 <? 1) with true by reflexivity.
  unfold setD_wrap. zcbn.
  replace (zlen (@nil Z)) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  zcbn.
  unfold zr_put4.
  reflexivity.
Qed.

(** The slice arithmetic behind the big-endian bridge. *)
Lemma zr_slice_16_8 : forall a, 0 <= a -> (a mod 65536) / 256 = (a / 256) mod 256.
Proof.
  intros a Ha.
  rewrite (Z.div_mod a 65536) at 2 by lia.
  set (q := a / 65536). set (r := a mod 65536).
  assert (Hr : 0 <= r < 65536) by (apply Z.mod_pos_bound; lia).
  replace (65536 * q + r) with (q * 256 * 256 + r) by ring.
  rewrite Z.div_add_l by lia.
  replace (q * 256 + r / 256) with (r / 256 + q * 256) by ring.
  rewrite Z_mod_plus_full.
  rewrite Z.mod_small; [reflexivity|].
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.

Lemma zr_mod_16_8 : forall a, (a mod 65536) mod 256 = a mod 256.
Proof.
  intros a.
  rewrite (Z.div_mod a 65536) at 2 by lia.
  replace (65536 * (a / 65536) + a mod 65536)
    with (a mod 65536 + (a / 65536 * 256) * 256) by ring.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma zr_be32_bridge : forall ad, 0 <= ad -> zr_put4 ad = be32 ad.
Proof.
  intros ad Ha. unfold zr_put4, be32, u8.
  replace 255 with (Z.ones 8) by reflexivity.
  replace 65535 with (Z.ones 16) by reflexivity.
  rewrite !Z.land_ones by lia.
  rewrite Z.shiftr_shiftr by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  replace (2 ^ 24) with 16777216 by reflexivity.
  replace (2 ^ 16) with 65536 by reflexivity.
  replace (2 ^ 8) with 256 by reflexivity.
  rewrite zr_slice_16_8 by lia.
  rewrite zr_mod_16_8.
  rewrite !Z.mod_mod by lia.
  reflexivity.
Qed.

(* ==========================================================================
   7.  Room: the deflateBound margin covers header + blocks + trailer.
   ========================================================================== *)

Lemma zr_l0_room : forall (x : list Z),
  zlen x + 5 * zr_nblocks x + 6 <= zr_deflate_bound 15 (zlen x) - 2.
Proof.
  intro x.
  pose proof (zlen_nonneg x) as Hxn.
  set (len := zlen x) in *.
  unfold zr_deflate_bound, zr_wraplen.
  replace (15 <? 0) with false by reflexivity.
  replace (15 <? 15) with false by reflexivity.
  rewrite !Z.shiftr_div_pow2 by lia.
  replace (2 ^ 12) with 4096 by reflexivity.
  replace (2 ^ 14) with 16384 by reflexivity.
  replace (2 ^ 25) with 33554432 by reflexivity.
  assert (H14 : 0 <= len / 16384) by (apply Z.div_pos; lia).
  assert (H25 : 0 <= len / 33554432) by (apply Z.div_pos; lia).
  assert (Hq : 5 * (len / 65535) <= len / 4096).
  { pose proof (Z.mul_div_le len 65535 ltac:(lia)) as Hm.
    assert (Hqp : 0 <= len / 65535) by (apply Z.div_pos; lia).
    apply Z.div_le_lower_bound; [lia|]. lia. }
  unfold zr_nblocks.
  destruct (zlen x =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. subst len. rewrite E0.
    replace (0 / 4096) with 0 by reflexivity. lia.
  - apply Z.eqb_neq in E0.
    assert (Hmono : (len - 1) / 65535 <= len / 65535)
      by (apply Z.div_le_mono; lia).
    lia.
Qed.

(* ==========================================================================
   8.  The whole call: init -> header -> stored -> trailer -> the stream.
   ========================================================================== *)

(** [flush_pending] for the two-byte zlib header queue. *)
Lemma flush_pending_bw2 :
  forall c1 c2 ts0 cfg status lastf wrap ls st,
  2 <= zs_availout st ->
  flush_pending
    (mkDSt cfg status lastf wrap
       (set_bw {| bw_out := [c1;c2]; bw_buf := 0; bw_valid := 0 |} ts0)
       ls st)
  = mkDSt cfg status lastf wrap (set_bw bw_init ts0) ls
      (setZ_out (zs_out st ++ [c1;c2])
        (setZ_availout (zs_availout st - 2)
          (setZ_totalout (zs_totalout st + 2) st))).
Proof.
  intros c1 c2 ts0 cfg status lastf wrap ls st Hav.
  unfold flush_pending. cbv zeta.
  unfold tr_flush_bits.
  cbn [d_ts d_strm].
  replace (zlen (bw_out (ts_bw (set_bw
             (bw_flush (ts_bw (set_bw {| bw_out := [c1;c2];
                                         bw_buf := 0; bw_valid := 0 |} ts0)))
             (set_bw {| bw_out := [c1;c2];
                        bw_buf := 0; bw_valid := 0 |} ts0)))))
    with 2 by reflexivity.
  destruct (zs_availout st <? 2) eqn:E1; [apply Z.ltb_lt in E1; lia|].
  reflexivity.
Qed.

(** The two-byte zlib header at the level-0 geometry: CMF 0x78, FLG 0x01
    (CINFO 7, level bits 0, FCHECK), and the adler reset. *)
Lemma zlib_header_l0 : forall lastf ls xin xd xo av ti to ad dt,
  ls_strstart ls = 0 ->
  zlib_header (mkDSt zr_g0 INIT_STATE lastf 1 (tr_init ts_new) ls
                 (mkZStrm xin xd xo av ti to ad dt))
  = mkDSt zr_g0 BUSY_STATE lastf 1
      (set_bw {| bw_out := [120; 1]; bw_buf := 0; bw_valid := 0 |}
              (tr_init ts_new)) ls
      (mkZStrm xin xd xo av ti to (adler32_z 0 true []) dt).
Proof.
  intros lastf ls xin xd xo av ti to ad dt Hss0.
  unfold zlib_header. cbv zeta.
  zcbn.
  rewrite Hss0.
  replace (0 =? 0) with true by reflexivity.
  zcbn.
  unfold putShortMSB, bw_put_byte.
  replace (ts_bw (tr_init ts_new)) with bw_init by reflexivity.
  unfold bw_init.
  cbn [bw_out bw_buf bw_valid app ts_bw set_bw].
  unfold setD_status, setD_strm, setD_ts, setZ_adler. zcbn.
  reflexivity.
Qed.

(** The stream, as one function of the input. *)
Definition zr_l0_stream (x : list Z) : list Z :=
  [120; 1] ++ zr_stored_body (zr_body_fuel x) x
           ++ be32 (adler32_z (adler32_z 0 true []) false (map u8 x)).

Theorem zr_deflate_l0_shape : forall x,
  zr_deflate 0 15 x = Some (zr_l0_stream x).
Proof.
  intro x.
  pose proof (zlen_nonneg x) as Hxn.
  pose proof (zr_l0_room x) as Hroom.
  pose proof (nblocks_pos x) as Hnbp.
  assert (HB : 13 <= zr_deflate_bound 15 (zlen x)).
  { unfold zr_deflate_bound, zr_wraplen.
    replace (15 <? 0) with false by reflexivity.
    replace (15 <? 15) with false by reflexivity.
    rewrite !Z.shiftr_div_pow2 by lia.
    assert (0 <= zlen x / 2 ^ 12) by (apply Z.div_pos; lia).
    assert (0 <= zlen x / 2 ^ 14) by (apply Z.div_pos; lia).
    assert (0 <= zlen x / 2 ^ 25) by (apply Z.div_pos; lia). lia. }
  unfold zr_deflate.
  replace (defl_new 0 8 15 8 ZR_STRATEGY)
    with (Some (deflate_reset zr_g0 1)) by (vm_compute; reflexivity).
  cbv beta iota zeta.
  replace (setD_strm
             (setZ_availout (zr_deflate_bound 15 (zlen x))
                (setZ_in x (d_strm (deflate_reset zr_g0 1))))
             (deflate_reset zr_g0 1))
    with (mkDSt zr_g0 INIT_STATE (-2) 1 (tr_init ts_new)
            (d_ls (deflate_reset zr_g0 1))
            (mkZStrm x [] [] (zr_deflate_bound 15 (zlen x)) 0 0
                     (adler32_z 0 true []) Z_UNKNOWN))
    by reflexivity.
  set (B := zr_deflate_bound 15 (zlen x)) in *.
  set (LS0 := d_ls (deflate_reset zr_g0 1)) in *.
  unfold deflate. cbv zeta.
  zcbn.
  replace ((Z_BLOCK <? Z_FINISH) || (Z_FINISH <? 0)) with false by reflexivity.
  replace (Z_FINISH =? Z_FINISH) with true by reflexivity.
  replace ((INIT_STATE =? FINISH_STATE) && negb true) with false by reflexivity.
  replace (B =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  zcbn.
  replace (zlen (bw_out (ts_bw (tr_init ts_new)))) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  zcbn.
  replace (RANK Z_FINISH <=? RANK (-2)) with false by reflexivity.
  rewrite ?andb_false_r.
  unfold setD_lastflush. zcbn.
  replace (zlen (bw_out (ts_bw (tr_init ts_new)))) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  zcbn.
  unfold deflate_body. cbv zeta.
  zcbn.
  replace (INIT_STATE =? FINISH_STATE) with false by reflexivity.
  replace (1 =? 0) with false by reflexivity.
  replace (INIT_STATE =? INIT_STATE) with true by reflexivity.
  zcbn.
  rewrite zlib_header_l0 by reflexivity.
  rewrite flush_pending_bw2 by (zcbn; lia).
  zcbn.
  rewrite ts_bw_set_bw.
  replace (zlen (bw_out bw_init)) with 0 by reflexivity.
  replace (0 =? 0) with true by reflexivity.
  zcbn.
  unfold deflate_run. cbv zeta.
  zcbn.
  replace (negb (Z_FINISH =? Z_NO_FLUSH) && negb (BUSY_STATE =? FINISH_STATE))
    with true by reflexivity.
  rewrite !orb_true_r.
  zcbn.
  unfold dispatch. zcbn.
  replace (dg_level zr_g0 =? 0) with true by reflexivity.
  zcbn.
  replace (INIT_STATE =? INIT_STATE) with true by reflexivity.
  unfold setZ_out, setZ_availout, setZ_totalout. zcbn.
  cbn [app].
  destruct (deflate_stored_l0 BUSY_STATE Z_FINISH
              (set_bw bw_init (tr_init ts_new))
              LS0
              x [] [120; 1] (B - 2) 0 (0 + 2) (adler32_z 0 true []) Z_UNKNOWN
              (ts_bw_set_bw _ _) ltac:(reflexivity) ltac:(subst B; lia))
    as [ts3 [ls3 [st' [Heq [Hbw3 [Hin [Hdn [Hout [Hav [Hdt Htr]]]]]]]]]].
  rewrite Heq.
  zcbn.
  replace (Z_FINISH =? Z_FINISH) with true by reflexivity.
  unfold setD_status. zcbn.
  replace (1 <=? 0) with false by reflexivity.
  destruct st' as [sin sdn sout sav sti sto sad sdt].
  cbn [zs_in zs_done zs_out zs_availout zs_datatype zs_adler] in
    Hin, Hdn, Hout, Hav, Hdt.
  subst sin sdn sout sav sdt.
  rewrite deflate_trailer_l0 by (assumption || (subst B; lia)).
  replace (Z_STREAM_END =? Z_STREAM_END) with true by reflexivity.
  zcbn.
  (* the adler value from the tracking thread *)
  assert (Ht0 : AdlerTracksDone (adler32_z 0 true [])
                  (mkZStrm x [] [120; 1] (B - 2) 0 (0 + 2)
                           (adler32_z 0 true []) Z_UNKNOWN))
    by (apply adler_tracks_done_at_reset; reflexivity).
  specialize (Htr _ adwf_init Ht0).
  destruct Htr as [HadV [Hadwf Heqad]].
  cbn [zs_adler zs_done] in HadV, Hadwf, Heqad.
  cbn [app] in Heqad.
  rewrite Heqad.
  unfold zr_l0_stream.
  rewrite <- zr_be32_bridge
    by (destruct HadV as [_ HadB]; rewrite Heqad in HadB; lia).
  rewrite <- !app_assoc.
  reflexivity.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Locate zr_deflate_l0_shape.
Print Assumptions zr_deflate_l0_shape.
Locate deflate_stored_l0.
Print Assumptions deflate_stored_l0.
