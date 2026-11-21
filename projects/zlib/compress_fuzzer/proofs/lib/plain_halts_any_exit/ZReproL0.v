(** * ZReproL0 — config (0, 15): the stored-path emitter, computed exactly.

    model-rt lane (z-repro campaign), 2026-08-19.  Q2a of the (0,15)
    end-to-end closure: [zr_deflate 0 15 x] is characterised byte-exactly
    ([zr_deflate_l0_shape]), which is the compute half of
    [ZRepro.ZRepro_Emitter_l0_zlib] and the input to the inflate walk.

    SHAPE OF THE ARGUMENT.  At level 0 the dispatch is [deflate_stored],
    and with the harness's one-call-at-deflateBound shape its inner
    [dst_loop] runs with [left0 = strstart - block_start = 0] on every
    trip: the window bookkeeping happens only AFTER the loop (and touches
    only [d_ls]/[ts_matches], never the byte stream).  So each trip is
    exactly: 5-byte stored header through the bit writer
    ([tr_stored_block [] 0 last] + [patch_len4] + [flush_pending]), then
    the payload chunk direct-copied by [read_buf] — and the whole loop is
    an induction over 65535-byte chunks with the bit writer returning to
    empty at every boundary.  The adler thread is NOT re-proved here: the
    loop carries [GtAdlerLoop.AdlerTracksDone] and the trailer equation
    falls out of [adler_field_is_the_trailer]. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtAdlerChunk GtAdlerLoop.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The emitted bytes, as functions of the input.
   ========================================================================== *)

(** One stored-block header: BFINAL byte (BTYPE=00 gives the whole first
    byte after [bi_windup]'s pad), LEN little-endian, NLEN = ~LEN
    little-endian ([deflate.c:1674-1677] via [patch_len4]). *)
Definition zr_stored_hdr (last len : Z) : list Z :=
  [last; u8 len; u8 (Z.shiftr len 8);
   u8 (Z.lnot len); u8 (Z.shiftr (u32 (Z.lnot len)) 8)].

(** The stored-block serialization of the whole input: full 65535-byte
    blocks, then a final block carrying the remainder (possibly empty —
    the [x = []] stream is one empty final block). *)
Fixpoint zr_stored_body (fuel : nat) (x : list Z) : list Z :=
  match fuel with
  | O => []
  | S f =>
      if Z.leb (zlen x) 65535
      then zr_stored_hdr 1 (zlen x) ++ map u8 x
      else zr_stored_hdr 0 65535 ++ map u8 (firstn (Z.to_nat 65535) x)
           ++ zr_stored_body f (skipn (Z.to_nat 65535) x)
  end.

Definition zr_body_fuel (x : list Z) : nat := S (Z.to_nat (zlen x / 65535)).

Definition zr_nblocks (x : list Z) : Z :=
  if Z.eqb (zlen x) 0 then 1 else (zlen x - 1) / 65535 + 1.

(* ==========================================================================
   2.  zlen plumbing.
   ========================================================================== *)

Lemma zlen_nonneg : forall (x : list Z), 0 <= zlen x.
Proof. intro x. unfold zlen. lia. Qed.

Lemma zlen_skipn_65535 : forall (x : list Z),
  65535 < zlen x -> zlen (skipn (Z.to_nat 65535) x) = zlen x - 65535.
Proof.
  intros x H. unfold zlen in *. rewrite length_skipn. lia.
Qed.

Lemma body_fuel_step : forall (x : list Z),
  65535 < zlen x -> zr_body_fuel x = S (zr_body_fuel (skipn (Z.to_nat 65535) x)).
Proof.
  intros x H. unfold zr_body_fuel.
  rewrite zlen_skipn_65535 by exact H.
  f_equal.
  replace (zlen x / 65535) with ((zlen x - 65535) / 65535 + 1); [lia|].
  replace (zlen x) with ((zlen x - 65535) + 1 * 65535) at 2 by lia.
  rewrite Z.div_add by lia. reflexivity.
Qed.

Lemma nblocks_step : forall (x : list Z),
  65535 < zlen x -> zr_nblocks x = zr_nblocks (skipn (Z.to_nat 65535) x) + 1.
Proof.
  intros x H. unfold zr_nblocks.
  rewrite zlen_skipn_65535 by exact H.
  replace (Z.eqb (zlen x) 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (Z.eqb (zlen x - 65535) 0) eqn:E0.
  - apply Z.eqb_eq in E0. lia.
  - apply Z.eqb_neq in E0.
    replace (zlen x - 1) with ((zlen x - 65535 - 1) + 1 * 65535) by lia.
    rewrite Z.div_add by lia. lia.
Qed.

Lemma nblocks_pos : forall (x : list Z), 1 <= zr_nblocks x.
Proof.
  intro x. unfold zr_nblocks.
  destruct (Z.eqb (zlen x) 0) eqn:E; [lia|].
  apply Z.eqb_neq in E. pose proof (zlen_nonneg x).
  assert (0 <= (zlen x - 1) / 65535) by (apply Z.div_pos; lia). lia.
Qed.

Lemma nblocks_one : forall (x : list Z),
  zlen x <= 65535 -> zr_nblocks x = 1.
Proof.
  intros x H. unfold zr_nblocks. pose proof (zlen_nonneg x).
  destruct (Z.eqb (zlen x) 0) eqn:E; [reflexivity|].
  apply Z.eqb_neq in E.
  rewrite Z.div_small by lia. reflexivity.
Qed.





(** ** The machinery pieces, one lemma per unit.

    DISCIPLINE NOTE (this file's hard lesson, 2026-08-19): [vm_compute] /
    [cbv] on the whole goal DIVERGE here — full normalization of the
    walled emitter machinery applied to OPEN arguments duplicates
    continuations under every stuck guard.  The working pattern is the
    tree's own: one equation lemma per machinery unit (closed pipeline
    parts computed by CONVERSION, never by a normalization tactic), guard
    atoms destructed as-spelled with dead branches killed by [lia], and
    the final record equality closed by [reflexivity]'s lazy
    conversion. *)

Lemma zlen_nil : forall (l : list Z), zlen l = 0 -> l = [].
Proof.
  intros l H. destruct l; [reflexivity|].
  unfold zlen in H. cbn [length] in H. lia.
Qed.

(** [tr_stored_block [] 0 last] on an empty bit buffer: the five header
    bytes before patching, at each of the two BFINAL values. *)
Lemma tr_stored_bw_1 : forall ts, ts_bw ts = bw_init ->
  ts_bw (tr_stored_block [] 0 1 ts)
  = {| bw_out := [1; 0; 0; 255; 255]; bw_buf := 0; bw_valid := 0 |}.
Proof. intros ts H. unfold tr_stored_block. rewrite H. reflexivity. Qed.

Lemma tr_stored_bw_0 : forall ts, ts_bw ts = bw_init ->
  ts_bw (tr_stored_block [] 0 0 ts)
  = {| bw_out := [0; 0; 0; 255; 255]; bw_buf := 0; bw_valid := 0 |}.
Proof. intros ts H. unfold tr_stored_block. rewrite H. reflexivity. Qed.

(** [patch_len4] on a five-byte queue keeps the first byte and rewrites
    the LEN/NLEN four. *)
Lemma patch_len4_5 : forall len c1 c2 c3 c4 c5,
  patch_len4 len [c1; c2; c3; c4; c5]
  = [c1; u8 len; u8 (Z.shiftr len 8);
     u8 (Z.lnot len); u8 (Z.shiftr (u32 (Z.lnot len)) 8)].
Proof. reflexivity. Qed.

(** [flush_pending] when the pending queue holds exactly five bytes and
    the bit buffer is drained: move all five.  The queue bytes sit in the
    LHS pattern so [rewrite] can infer them. *)
Lemma flush_pending_bw5 :
  forall c1 c2 c3 c4 c5 ts0 cfg status lastf wrap ls st,
  5 <= zs_availout st ->
  flush_pending
    (mkDSt cfg status lastf wrap
       (set_bw {| bw_out := [c1;c2;c3;c4;c5]; bw_buf := 0; bw_valid := 0 |}
               ts0) ls st)
  = mkDSt cfg status lastf wrap (set_bw bw_init ts0) ls
      (setZ_out (zs_out st ++ [c1;c2;c3;c4;c5])
        (setZ_availout (zs_availout st - 5)
          (setZ_totalout (zs_totalout st + 5) st))).
Proof.
  intros c1 c2 c3 c4 c5 ts0 cfg status lastf wrap ls st Hav.
  unfold flush_pending. cbv zeta.
  unfold tr_flush_bits.
  cbn [d_ts d_strm].
  replace (zlen (bw_out (ts_bw (set_bw
             (bw_flush (ts_bw (set_bw {| bw_out := [c1;c2;c3;c4;c5];
                                         bw_buf := 0; bw_valid := 0 |} ts0)))
             (set_bw {| bw_out := [c1;c2;c3;c4;c5];
                        bw_buf := 0; bw_valid := 0 |} ts0)))))
    with 5 by reflexivity.
  destruct (zs_availout st <? 5) eqn:E1; [apply Z.ltb_lt in E1; lia|].
  reflexivity.
Qed.

(** [read_buf] consuming the whole input (wrap 1, the zlib wrapper). *)
Lemma read_buf_all : forall xin xd xo av ti to ad dt,
  xin <> [] ->
  read_buf 1 (zlen xin) (mkZStrm xin xd xo av ti to ad dt)
  = (map u8 xin,
     mkZStrm [] (xd ++ map u8 xin) xo av (ti + zlen xin) to
             (adler32_z ad false (map u8 xin)) dt).
Proof.
  intros xin xd xo av ti to ad dt Hne.
  unfold read_buf. cbv zeta.
  cbn [zs_in zs_adler zs_done zs_totalin].
  destruct (zlen xin <? zlen xin) eqn:E1; [apply Z.ltb_lt in E1; lia|].
  destruct (zlen xin =? 0) eqn:E0.
  { apply Z.eqb_eq in E0. apply zlen_nil in E0. congruence. }
  replace (Z.to_nat (zlen xin)) with (length xin)
    by (unfold zlen; symmetry; apply Nat2Z.id).
  rewrite firstn_all, skipn_all.
  reflexivity.
Qed.

(** [read_buf] consuming one full 65535-byte chunk. *)
Lemma read_buf_part : forall xin xd xo av ti to ad dt,
  65535 < zlen xin ->
  read_buf 1 65535 (mkZStrm xin xd xo av ti to ad dt)
  = (map u8 (firstn (Z.to_nat 65535) xin),
     mkZStrm (skipn (Z.to_nat 65535) xin)
             (xd ++ map u8 (firstn (Z.to_nat 65535) xin)) xo av
             (ti + 65535) to
             (adler32_z ad false (map u8 (firstn (Z.to_nat 65535) xin))) dt).
Proof.
  intros xin xd xo av ti to ad dt Hlt.
  unfold read_buf. cbv zeta.
  cbn [zs_in zs_adler zs_done zs_totalin].
  destruct (65535 <? zlen xin) eqn:E1; [|apply Z.ltb_ge in E1; lia].
  reflexivity.
Qed.


(** The one reduction used inside the trip proofs: beta/iota plus record
    projections and plain booleans.  Comparisons are deliberately NOT
    unfolded — [cbn] partially evaluates a one-sided [Z.eqb] into a stuck
    [match], destroying the spelling every subsequent [replace] needs; all
    comparison atoms are handled by [replace]/[destruct] at their stable
    spellings instead. *)
Ltac zcbn :=
  cbn [andb orb negb fst snd
       bw_out bw_buf bw_valid
       d_cfg d_status d_lastflush d_wrap d_ts d_ls d_strm
       zs_in zs_done zs_out zs_availout zs_totalin zs_totalout zs_adler
       zs_datatype ls_strstart ls_blockstart].

(* ==========================================================================
   3.  One dst_step trip, three cases, each state exact.
   ========================================================================== *)

(** Case FINAL-EMPTY. *)
Lemma dst_step_l0_empty :
  forall cfg status lastf ts ls xdone xout aout tin tout ad dt,
  ts_bw ts = bw_init ->
  ls_strstart ls = ls_blockstart ls ->
  5 <= aout ->
  dst_step Z_FINISH 32768
    (mkDSt cfg status lastf 1 ts ls
       (mkZStrm [] xdone xout aout tin tout ad dt))
  = (false, 1,
     mkDSt cfg status lastf 1 (set_bw bw_init ts) ls
       (mkZStrm [] xdone (xout ++ zr_stored_hdr 1 0) (aout - 5)
                tin (tout + 5) ad dt)).
Proof.
  intros cfg status lastf ts ls xdone xout aout tin tout ad dt Hbw Hss Ha.
  unfold dst_step. cbv zeta.
  zcbn.
  rewrite Hbw, Hss.
  cbn [bw_valid bw_init].
  replace (Z.shiftr (0 + 42) 3) with 5 by reflexivity.
  replace (Z_FINISH =? Z_FINISH) with true by reflexivity.
  replace (Z_FINISH =? Z_NO_FLUSH) with false by reflexivity.
  destruct (aout <? 5) eqn:A1; [apply Z.ltb_lt in A1; lia|].
  replace (ls_blockstart ls - ls_blockstart ls) with 0 by lia.
  replace (zlen (@nil Z)) with 0 by reflexivity.
  replace (0 + 0) with 0 by reflexivity.
  unfold zmin, MAX_STORED.
  destruct (aout - 5 <? 0) eqn:A2; [apply Z.ltb_lt in A2; lia|].
  zcbn.
  replace (0 <? 65535) with true by reflexivity.
  zcbn.
  replace (0 =? 0) with true by reflexivity.
  replace (0 <? 32768) with true by reflexivity.
  zcbn.
  rewrite (tr_stored_bw_1 ts Hbw).
  zcbn.
  rewrite patch_len4_5.
  unfold setD_ts. zcbn.
  rewrite flush_pending_bw5 by (zcbn; lia).
  zcbn.
  unfold zr_stored_hdr.
  reflexivity.
Qed.

(** Case FINAL, nonempty. *)
Lemma dst_step_l0_final :
  forall cfg status lastf ts ls xin xdone xout aout tin tout ad dt,
  ts_bw ts = bw_init ->
  ls_strstart ls = ls_blockstart ls ->
  0 < zlen xin <= 65535 ->
  zlen xin + 5 <= aout ->
  dst_step Z_FINISH 32768
    (mkDSt cfg status lastf 1 ts ls
       (mkZStrm xin xdone xout aout tin tout ad dt))
  = (false, 1,
     mkDSt cfg status lastf 1 (set_bw bw_init ts) ls
       (mkZStrm [] (xdone ++ map u8 xin)
                ((xout ++ zr_stored_hdr 1 (zlen xin)) ++ map u8 xin)
                (aout - 5 - zlen xin) (tin + zlen xin) (tout + 5 + zlen xin)
                (adler32_z ad false (map u8 xin)) dt)).
Proof.
  intros cfg status lastf ts ls xin xdone xout aout tin tout ad dt
         Hbw Hss Hlen Ha.
  assert (Hne : xin <> []).
  { intro E. subst xin. revert Hlen.
    replace (zlen (@nil Z)) with 0 by reflexivity. lia. }
  unfold dst_step. cbv zeta.
  zcbn.
  rewrite Hbw, Hss.
  cbn [bw_valid bw_init].
  replace (Z.shiftr (0 + 42) 3) with 5 by reflexivity.
  replace (Z_FINISH =? Z_FINISH) with true by reflexivity.
  replace (Z_FINISH =? Z_NO_FLUSH) with false by reflexivity.
  destruct (aout <? 5) eqn:A1; [apply Z.ltb_lt in A1; lia|].
  replace (ls_blockstart ls - ls_blockstart ls) with 0 by lia.
  replace (0 + zlen xin) with (zlen xin) by lia.
  unfold zmin, MAX_STORED.
  destruct (aout - 5 <? zlen xin) eqn:A2; [apply Z.ltb_lt in A2; lia|].
  destruct (zlen xin <? 65535) eqn:A3.
  - (* strictly below one block *)
    zcbn.
    replace (zlen xin =? zlen xin) with true by (symmetry; apply Z.eqb_refl).
    replace (zlen xin =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    zcbn.
    rewrite andb_false_r.
    zcbn.
    rewrite (tr_stored_bw_1 ts Hbw).
    zcbn.
    rewrite patch_len4_5.
    unfold setD_ts. zcbn.
    rewrite flush_pending_bw5 by (zcbn; lia).
    zcbn.
    replace (0 =? 0) with true by reflexivity.
    replace (zlen xin =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    zcbn.
    unfold setZ_out, setZ_availout, setZ_totalout. zcbn.
    rewrite read_buf_all by exact Hne.
    zcbn.
    unfold zr_stored_hdr.
    reflexivity.
  - (* exactly one full block *)
    assert (EA : zlen xin = 65535).
    { pose proof A3 as A3'. apply Z.ltb_ge in A3'. lia. }
    zcbn.
    replace (65535 =? zlen xin) with true
      by (symmetry; apply Z.eqb_eq; lia).
    replace (zlen xin =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (65535 <? 32768) with false by reflexivity.
    zcbn.
    rewrite (tr_stored_bw_1 ts Hbw).
    zcbn.
    rewrite patch_len4_5.
    unfold setD_ts. zcbn.
    rewrite flush_pending_bw5 by (zcbn; lia).
    zcbn.
    replace (0 =? 0) with true by reflexivity.
    replace (zlen xin =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    zcbn.
    replace (65535 =? 0) with false by reflexivity.
    zcbn.
    unfold setZ_out, setZ_availout, setZ_totalout. zcbn.
    rewrite <- EA.
    rewrite read_buf_all by exact Hne.
    zcbn.
    unfold zr_stored_hdr.
    reflexivity.
Qed.

(** Case CONTINUE. *)
Lemma dst_step_l0_cont :
  forall cfg status lastf ts ls xin xdone xout aout tin tout ad dt,
  ts_bw ts = bw_init ->
  ls_strstart ls = ls_blockstart ls ->
  65535 < zlen xin ->
  zlen xin + 5 <= aout ->
  dst_step Z_FINISH 32768
    (mkDSt cfg status lastf 1 ts ls
       (mkZStrm xin xdone xout aout tin tout ad dt))
  = (false, 0,
     mkDSt cfg status lastf 1 (set_bw bw_init ts) ls
       (mkZStrm (skipn (Z.to_nat 65535) xin)
                (xdone ++ map u8 (firstn (Z.to_nat 65535) xin))
                ((xout ++ zr_stored_hdr 0 65535)
                   ++ map u8 (firstn (Z.to_nat 65535) xin))
                (aout - 5 - 65535) (tin + 65535) (tout + 5 + 65535)
                (adler32_z ad false (map u8 (firstn (Z.to_nat 65535) xin)))
                dt)).
Proof.
  intros cfg status lastf ts ls xin xdone xout aout tin tout ad dt
         Hbw Hss Hlen Ha.
  unfold dst_step. cbv zeta.
  zcbn.
  rewrite Hbw, Hss.
  cbn [bw_valid bw_init].
  replace (Z.shiftr (0 + 42) 3) with 5 by reflexivity.
  replace (Z_FINISH =? Z_FINISH) with true by reflexivity.
  replace (Z_FINISH =? Z_NO_FLUSH) with false by reflexivity.
  destruct (aout <? 5) eqn:A1; [apply Z.ltb_lt in A1; lia|].
  replace (ls_blockstart ls - ls_blockstart ls) with 0 by lia.
  replace (0 + zlen xin) with (zlen xin) by lia.
  unfold zmin, MAX_STORED.
  destruct (aout - 5 <? zlen xin) eqn:A2; [apply Z.ltb_lt in A2; lia|].
  destruct (zlen xin <? 65535) eqn:A3; [apply Z.ltb_lt in A3; lia|].
  zcbn.
  replace (65535 =? zlen xin) with false
    by (symmetry; apply Z.eqb_neq; lia).
  replace (65535 =? 0) with false by reflexivity.
  replace (65535 <? 32768) with false by reflexivity.
  zcbn.
  rewrite (tr_stored_bw_0 ts Hbw).
  zcbn.
  rewrite patch_len4_5.
  unfold setD_ts. zcbn.
  rewrite flush_pending_bw5 by (zcbn; lia).
  zcbn.
  replace (0 =? 0) with true by reflexivity.
  zcbn.
  unfold setZ_out, setZ_availout, setZ_totalout. zcbn.
  rewrite read_buf_part by exact Hlen.
  zcbn.
  unfold zr_stored_hdr.
  reflexivity.
Qed.

(* ==========================================================================
   4.  The loop: every trip returns the bit writer to empty, never moves
       [strstart]/[blockstart], and appends one block; induction over
       65535-byte chunks.
   ========================================================================== *)

Lemma set_bw_collapse : forall a b ts, set_bw a (set_bw b ts) = set_bw a ts.
Proof. reflexivity. Qed.

Lemma ts_bw_set_bw : forall b ts, ts_bw (set_bw b ts) = b.
Proof. reflexivity. Qed.

Lemma ad_wf_map_u8 : forall c, ad_wf false (map u8 c).
Proof.
  intro c. split; [|discriminate].
  intros b Hb. apply in_map_iff in Hb. destruct Hb as [v [<- _]].
  unfold u8. apply Z.mod_pos_bound. lia.
Qed.

(** One direct-copy chunk, in [GtAdlerLoop]'s invariant: the adler field
    and the consumed-bytes record advance together. *)
Lemma track_chunk : forall A (c : list Z) st st',
  AdWf A ->
  zs_adler st' = adler32_z (zs_adler st) false (map u8 c) ->
  zs_done st' = zs_done st ++ map u8 c ->
  AdlerTracksDone A st -> AdlerTracksDone A st'.
Proof.
  intros A c st st' HA Had Hdn [Hav [Hwf Heq]].
  split; [|split].
  - rewrite Had. apply adval_step; [exact Hav|apply ad_wf_map_u8].
  - rewrite Hdn. apply ad_wf_app; [exact Hwf|apply ad_wf_map_u8].
  - rewrite Had, Hdn, Heq.
    apply adler32_z_chunk; [exact HA|exact Hwf|apply ad_wf_map_u8].
Qed.

Lemma dst_loop_l0 :
  forall fuel (xin : list Z) cfg status lastf ts ls xdone xout aout tin tout ad dt,
  ts_bw ts = bw_init ->
  ls_strstart ls = ls_blockstart ls ->
  zlen xin + 5 * zr_nblocks xin <= aout ->
  (zr_body_fuel xin <= fuel)%nat ->
  exists st',
    dst_loop fuel Z_FINISH 32768
      (mkDSt cfg status lastf 1 ts ls
         (mkZStrm xin xdone xout aout tin tout ad dt))
    = (1, mkDSt cfg status lastf 1 (set_bw bw_init ts) ls st')
    /\ zs_in st' = []
    /\ zs_done st' = xdone ++ map u8 xin
    /\ zs_out st' = xout ++ zr_stored_body (zr_body_fuel xin) xin
    /\ zs_availout st' = aout - (5 * zr_nblocks xin + zlen xin)
    /\ zs_datatype st' = dt
    /\ (forall A, AdWf A ->
          AdlerTracksDone A (mkZStrm xin xdone xout aout tin tout ad dt) ->
          AdlerTracksDone A st').
Proof.
  induction fuel as [|fuel IH];
    intros xin cfg status lastf ts ls xdone xout aout tin tout ad dt
           Hbw Hss Ha Hf.
  - unfold zr_body_fuel in Hf. lia.
  - pose proof (zlen_nonneg xin) as Hxn.
    destruct (Z.leb (zlen xin) 65535) eqn:E65b.
    + apply Z.leb_le in E65b as E65.
      pose proof (nblocks_one xin E65) as Hnb.
      destruct (Z.eqb (zlen xin) 0) eqn:E0b.
      * (* the empty final block *)
        apply Z.eqb_eq in E0b.
        assert (Exin : xin = [])
          by (destruct xin; [reflexivity|unfold zlen in E0b; cbn in E0b; lia]).
        subst xin.
        assert (Ha5 : 5 <= aout).
        { replace (zlen (@nil Z)) with 0 in Ha by reflexivity.
          replace (zr_nblocks (@nil Z)) with 1 in Ha by reflexivity. lia. }
        cbn [dst_loop].
        rewrite (dst_step_l0_empty cfg status lastf ts ls xdone xout aout
                   tin tout ad dt Hbw Hss Ha5).
        cbn [Z.eqb].
        eexists. split; [reflexivity|].
        cbn [zs_in zs_done zs_out zs_availout zs_datatype].
        split; [reflexivity|].
        split; [now rewrite app_nil_r|].
        split.
        { replace (zr_stored_body (zr_body_fuel []) [])
            with (zr_stored_hdr 1 0) by (vm_compute; reflexivity).
          reflexivity. }
        split.
        { replace (5 * zr_nblocks [] + zlen []) with 5
            by (vm_compute; reflexivity). reflexivity. }
        split; [reflexivity|].
        intros A HA Ht. exact Ht.
      * (* the nonempty final block *)
        apply Z.eqb_neq in E0b.
        assert (Hfin : 0 < zlen xin <= 65535) by lia.
        assert (Ha5 : zlen xin + 5 <= aout) by lia.
        cbn [dst_loop].
        rewrite (dst_step_l0_final cfg status lastf ts ls xin xdone xout aout
                   tin tout ad dt Hbw Hss Hfin Ha5).
        cbn [Z.eqb].
        eexists. split; [reflexivity|].
        cbn [zs_in zs_done zs_out zs_availout zs_datatype].
        split; [reflexivity|].
        split; [reflexivity|].
        split.
        { unfold zr_body_fuel. cbn [zr_stored_body].
          rewrite E65b. rewrite <- app_assoc. reflexivity. }
        split; [lia|].
        split; [reflexivity|].
        intros A HA Ht.
        eapply (track_chunk A xin); [exact HA| | |exact Ht]; reflexivity.
    + (* a full non-final block, then the tail by induction *)
      apply Z.leb_gt in E65b as E65.
      pose proof (nblocks_pos (skipn (Z.to_nat 65535) xin)) as Hnbp.
      pose proof (nblocks_step xin E65) as Hnbs.
      pose proof (zlen_skipn_65535 xin E65) as Hzs.
      pose proof (body_fuel_step xin E65) as Hbfs.
      assert (Ha5 : zlen xin + 5 <= aout)
        by (pose proof (nblocks_pos xin); lia).
      cbn [dst_loop].
      rewrite (dst_step_l0_cont cfg status lastf ts ls xin xdone xout aout
                 tin tout ad dt Hbw Hss E65 Ha5).
      cbn [Z.eqb].
      destruct (IH (skipn (Z.to_nat 65535) xin) cfg status lastf
                  (set_bw bw_init ts) ls
                  (xdone ++ map u8 (firstn (Z.to_nat 65535) xin))
                  ((xout ++ zr_stored_hdr 0 65535)
                     ++ map u8 (firstn (Z.to_nat 65535) xin))
                  (aout - 5 - 65535) (tin + 65535) (tout + 5 + 65535)
                  (adler32_z ad false (map u8 (firstn (Z.to_nat 65535) xin)))
                  dt (ts_bw_set_bw _ _) Hss ltac:(lia) ltac:(lia))
        as [st' [Heq [Hin [Hdn [Hout [Hav [Hdt Htr]]]]]]].
      rewrite set_bw_collapse in Heq.
      exists st'. split; [exact Heq|].
      split; [exact Hin|].
      split.
      { rewrite Hdn. rewrite <- app_assoc, <- map_app, firstn_skipn.
        reflexivity. }
      split.
      { rewrite Hout. rewrite Hbfs. cbn [zr_stored_body]. rewrite E65b.
        rewrite <- !app_assoc. reflexivity. }
      split; [lia|].
      split; [exact Hdt|].
      intros A HA Ht.
      apply Htr; [exact HA|].
      eapply (track_chunk A (firstn (Z.to_nat 65535) xin));
        [exact HA| | |exact Ht]; reflexivity.
Qed.

