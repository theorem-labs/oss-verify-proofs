(** * Bridge.DEmit.DZHeader — pair D9 of PAIRS.md: the zlib header and trailer, S5 vs RT.

    S5 ([Z/Deflate.v:248], [:289]) writes the header (or trailer) bytes, then
    flushes and decides its return inside the same function; RT
    ([Deflate.v:1149], [:1190]) writes the bytes in [zlib_header] and leaves
    the flush to [deflate_body], while [deflate_trailer] flushes itself.  S5's
    own [DeflateSafe] already splits both functions at the flush
    ([zhdr_st], [trailer_st] and their [_eq] lemmas); the pairs follow that
    split.

    Delivered:
    - [pair_zlib_header]: S5's [deflate_zlib_header] against RT's
      [zlib_header] followed by [deflate_body]'s flush and pending test: the
      states keep [dst_rel] (with [last_flush = -1] when bytes stay pending)
      and S5's early return is [Some Z_OK] exactly when RT's queue is non-empty;
    - [pair_deflate_trailer]: S5's [deflate_trailer] against RT's: the same
      return code, and the states keep [dst_rel];
    - the byte kit: [wrap32] does not change the bytes [putShortMSB] takes
      ([u8_shiftr8_wrap32], [u8_land_wrap32]), and [hrel], the simulation of a
      run of [put_byte]s on both sides.

    Side conditions: no symbol pending ([sym_next = 0]), [room s 8] for the
    header and [room s 10] for the trailer (the bytes plus [bi_flush]'s two),
    and [fp_ok] (BrFlush's integer premises for the flush).

    Ownership: a worker (group D).  Reviewer: a worker. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz Deflate DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import BrDFlush DTrStored.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module DZ := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Deflate.
Module DSf := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.

(* ------------------------------------------------------------------------- *)
(* 1.  Bytes                                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma mod32_mod8 : forall y, (y mod 4294967296) mod 256 = y mod 256.
Proof.
  intros y. pose proof (Z.div_mod y 4294967296 ltac:(lia)) as D.
  replace (y mod 256) with ((y mod 4294967296 + (y / 4294967296 * 16777216) * 256) mod 256) by (f_equal; lia).
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma shiftr8_mod32 : forall y, (y mod 4294967296 / 256) mod 256 = (y / 256) mod 256.
Proof.
  intros y. pose proof (Z.div_mod y 4294967296 ltac:(lia)) as D.
  assert (E : y / 256 = (y mod 4294967296 + (y / 4294967296 * 65536 * 256) * 256) / 256) by (f_equal; lia).
  rewrite Z.div_add in E by lia. rewrite E. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma u8_wrap32 : forall y, Base.u8 (wrap32 y) = Base.u8 y.
Proof.
  intros y. unfold Base.u8, wrap32. change 4294967295 with (Z.ones 32).
  rewrite Z.land_ones by lia. change (2 ^ 32) with 4294967296. apply mod32_mod8.
Qed.

(** S5 hands [putShortMSB] [wrap32 (adler >> 16)], RT [adler >> 16]: the two
    bytes agree. *)
Lemma u8_shiftr8_wrap32 : forall y, Base.u8 (Z.shiftr (wrap32 y) 8) = Base.u8 (Z.shiftr y 8).
Proof.
  intros y. unfold Base.u8, wrap32. change 4294967295 with (Z.ones 32).
  rewrite Z.land_ones by lia. rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 32) with 4294967296. change (2 ^ 8) with 256. apply shiftr8_mod32.
Qed.

Lemma u8_land_wrap32 : forall y, Base.u8 (Z.land (wrap32 y) 255) = Base.u8 (Z.land y 255).
Proof. intros y. rewrite !u8_land255. apply u8_wrap32. Qed.

Lemma bw_put_byte_u8 : forall c c' b, Base.u8 c = Base.u8 c' ->
  ZBitsOut.bw_put_byte c b = ZBitsOut.bw_put_byte c' b.
Proof. intros c c' b E. unfold ZBitsOut.bw_put_byte. rewrite E. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  A run of byte writes on both sides                                    *)
(* ------------------------------------------------------------------------- *)

(** RT's frame: only the bit writer of the [TSt] changed. *)
Definition tbw (ts ts' : RT.TSt) : Prop := ts' = RT.set_bw (RT.ts_bw ts') ts.

Lemma tbw_refl : forall ts, tbw ts ts.
Proof. intros ts. unfold tbw. destruct ts; reflexivity. Qed.

Lemma tbw_trans : forall a b c, tbw a b -> tbw b c -> tbw a c.
Proof. unfold tbw. intros a b c E1 E2. rewrite E2 at 1. rewrite E1 at 1. destruct a; reflexivity. Qed.

Lemma tbw_put_byte : forall ts c, tbw ts (RD.put_byte c ts).
Proof. intros ts c. reflexivity. Qed.

Lemma s5_putShortMSB_eq : forall s b,
  DL.putShortMSB s b = DS.put_byte (DS.put_byte s (Z.shiftr b 8)) (Z.land b 255).
Proof. intros s b. reflexivity. Qed.

Lemma rt_putShortMSB_eq : forall ts b,
  RD.putShortMSB b ts = RD.put_byte (Z.land b 255) (RD.put_byte (Z.shiftr b 8) ts).
Proof. intros ts b. destruct ts. reflexivity. Qed.

(** From [s0]/[ts0], S5 reached [s] and RT reached [ts] by byte writes only,
    the queues agree, and [k] more bytes fit. *)
Definition hrel (s0 : DS.deflate_state) (ts0 : RT.TSt) (s : DS.deflate_state) (ts : RT.TSt) (k : Z) : Prop :=
  bw4 s0 s /\ tbw ts0 ts /\ bw_rel s (RT.ts_bw ts) /\ room s k.

Lemma hrel_start : forall s ts k, bw_rel s (RT.ts_bw ts) -> room s k -> hrel s ts s ts k.
Proof. intros s ts k Hb Hr. split; [apply bw4_refl|]. split; [apply tbw_refl|]. split; assumption. Qed.

Lemma room_put_byte : forall s c k, room s (k + 1) -> room (DS.put_byte s c) k.
Proof.
  intros s c k (Hpo & Hr). unfold room, DS.put_byte. cbv zeta. s5bw. rewrite arr_len_set.
  split; [exact Hpo | lia].
Qed.

Lemma hrel_put_byte : forall s0 ts0 s ts k c c', 0 <= k ->
  hrel s0 ts0 s ts (k + 1) -> Base.u8 c = Base.u8 c' ->
  hrel s0 ts0 (DS.put_byte s c) (RD.put_byte c' ts) k.
Proof.
  intros s0 ts0 s ts k c c' Hk (F & T & B & R) E.
  split; [eapply bw4_trans; [exact F | apply bw4_put_byte]|].
  split; [eapply tbw_trans; [exact T | apply tbw_put_byte]|].
  split; [|apply room_put_byte; exact R].
  unfold RD.put_byte. cbn [RT.ts_bw RT.set_bw]. rewrite <- (bw_put_byte_u8 _ _ (RT.ts_bw ts) E).
  apply br_put_byte; [exact B|]. destruct R as (Hpo & Hr). split; [exact Hpo | lia].
Qed.

Lemma hrel_putShortMSB : forall s0 ts0 s ts k b b', 0 <= k ->
  hrel s0 ts0 s ts (k + 2) ->
  Base.u8 (Z.shiftr b 8) = Base.u8 (Z.shiftr b' 8) -> Base.u8 (Z.land b 255) = Base.u8 (Z.land b' 255) ->
  hrel s0 ts0 (DL.putShortMSB s b) (RD.putShortMSB b' ts) k.
Proof.
  intros s0 ts0 s ts k b b' Hk H E1 E2.
  rewrite s5_putShortMSB_eq, rt_putShortMSB_eq.
  apply hrel_put_byte; [exact Hk| |exact E2].
  apply hrel_put_byte; [lia| |exact E1].
  replace (k + 1 + 1) with (k + 2) by lia. exact H.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  Frames of [dst_rel]                                                   *)
(* ------------------------------------------------------------------------- *)

Ltac and_hyps := repeat match goal with H : _ /\ _ |- _ => destruct H end.
Ltac and_goal := repeat match goal with |- _ /\ _ => split end.
Ltac rel_unfold :=
  unfold dst_rel, geom_rel, lz_rel, bw_rel, pend_rel, sym_rel, tree_rel, strm_rel,
         DS.sym_buf_get, DS.cs_output in *;
  cbv zeta in *.
Ltac rt_proj :=
  cbn [RD.d_cfg RD.d_status RD.d_wrap RD.d_lastflush RD.d_ts RD.d_ls RD.d_strm
       RD.setD_status RD.setD_strm RD.setD_ts RD.setD_wrap RD.setD_lastflush RD.setZ_adler
       RD.zs_in RD.zs_done RD.zs_out RD.zs_availout RD.zs_totalin RD.zs_totalout
       RD.zs_adler RD.zs_datatype] in *.

(** A bit-writer step on S5 against a [set_bw] on RT, no symbol pending. *)
Lemma dst_rel_bw4 : forall s s' t ts' pre_out pre_in,
  dst_rel s t pre_out pre_in -> DS.ds_sym_next s = 0 -> bw4 s s' -> tbw (RD.d_ts t) ts' ->
  bw_rel s' (RT.ts_bw ts') ->
  dst_rel s' (RD.setD_ts ts' t) pre_out pre_in.
Proof.
  intros s s' t ts' pre_out pre_in (Hg & Hlz & Hbw & Hsym & Htr & Hst) Hsn F T Hb.
  pose proof (bw4_proj _ _ F) as (Epo & Est & Ew & Esn).
  destruct F as (E & Lpb & _ & _).
  unfold tbw in T. rewrite T.
  revert Hb. generalize (RT.ts_bw ts'). intros b Hb.
  unfold dst_rel. cbn [RD.d_ts RD.d_cfg RD.d_ls RD.d_strm RD.d_status RD.d_wrap RD.d_lastflush RD.setD_ts].
  split; [|split; [|split; [cbn [RT.ts_bw RT.set_bw]; exact Hb|split; [|split]]]].
  - revert Hg. unfold geom_rel. cbn [RD.d_cfg RD.d_status RD.d_wrap RD.d_lastflush RD.setD_ts].
    rewrite E. unfold set4. s5bw. rewrite Lpb. exact (fun H => H).
  - revert Hlz. unfold lz_rel. cbn [RD.d_ls RD.setD_ts]. rewrite E. unfold set4. s5bw. exact (fun H => H).
  - revert Hsym. unfold sym_rel. cbn [RD.d_ts RD.setD_ts RT.ts_symnext RT.ts_symbuf RT.set_bw].
    rewrite E. unfold set4. s5bw. rewrite Lpb, Hsn.
    intros (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [intros i Hi; lia|].
    split; [exact H4 | intros Hc; lia].
  - revert Htr. unfold tree_rel.
    cbn [RD.d_ts RD.setD_ts RT.ts_trees RT.ts_blcount RT.ts_heap RT.ts_depth RT.ts_maxcode RT.ts_heaplen
         RT.ts_heapmax RT.ts_optlen RT.ts_statlen RT.ts_matches RT.set_bw].
    rewrite E. unfold set4. s5bw. exact (fun H => H).
  - revert Hst. unfold strm_rel. cbn [RD.d_strm RD.setD_ts]. rewrite Est. exact (fun H => H).
Qed.

(** The header's last two writes: [adler] reset, [status := BUSY_STATE]. *)
Lemma dst_rel_hdr_finish : forall s t ts pre_out pre_in a st,
  dst_rel s (RD.setD_ts ts t) pre_out pre_in ->
  dst_rel (DS.set_status (DS.set_strm s (DS.cset_adler (DS.ds_strm s) a)) st)
          (RD.setD_status st (RD.setD_strm (RD.setZ_adler a (RD.d_strm t)) (RD.setD_ts ts t))) pre_out pre_in.
Proof.
  intros s t ts pre_out pre_in a st H. rel_unfold. rt_proj.
  autorewrite with s5f_status s5f_strm s5c_adler.
  and_hyps. and_goal; first [assumption | reflexivity].
Qed.

Lemma dst_rel_last_flush : forall s t pre_out pre_in v, dst_rel s t pre_out pre_in ->
  dst_rel (DS.set_last_flush s v) (RD.setD_lastflush v t) pre_out pre_in.
Proof.
  intros s t pre_out pre_in v H. rel_unfold. rt_proj. autorewrite with s5f_last_flush.
  and_hyps. and_goal; first [assumption | reflexivity].
Qed.

Lemma dst_rel_wrap : forall s t pre_out pre_in v, dst_rel s t pre_out pre_in ->
  dst_rel (DS.set_wrap s v) (RD.setD_wrap v t) pre_out pre_in.
Proof.
  intros s t pre_out pre_in v H. rel_unfold. rt_proj. autorewrite with s5f_wrap.
  and_hyps. and_goal; first [assumption | reflexivity].
Qed.

Lemma pend_zlen : forall s t pre_out pre_in, dst_rel s t pre_out pre_in ->
  RC.zlen (ZBitsOut.bw_out (RT.ts_bw (RD.d_ts t))) = DS.ds_pending s.
Proof.
  intros s t pre_out pre_in H. destruct (dst_rel_bw _ _ _ _ H) as ((_ & Hp & _ & Hsl) & _).
  rewrite <- Hsl. change RC.zlen with (@zlength Z). rewrite arr_slice_length. lia.
Qed.

Lemma flush_sym_next : forall x, DS.ds_sym_next (DL.flush_pending x) = DS.ds_sym_next x.
Proof. intros x. rewrite flush_pending_shape. bw6_fields. reflexivity. Qed.

Lemma fp_ok_bw4 : forall s s', bw4 s s' -> fp_ok s -> fp_ok s'.
Proof.
  intros s s' F Hok. destruct (bw4_proj _ _ F) as (_ & Est & _ & _). destruct F as (_ & L & _ & _).
  unfold fp_ok in *. rewrite Est, L. exact Hok.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  The header                                                            *)
(* ------------------------------------------------------------------------- *)

Lemma putShortMSB_strstart_strm : forall s b,
  DS.ds_strstart (DL.putShortMSB s b) = DS.ds_strstart s /\ DS.ds_strm (DL.putShortMSB s b) = DS.ds_strm s.
Proof. intros s b. rewrite s5_putShortMSB_eq. unfold DS.put_byte. cbv zeta. s5bw. split; reflexivity. Qed.

Lemma hdr_finish : forall s t pre_out pre_in X TS,
  dst_rel s t pre_out pre_in -> DS.ds_sym_next s = 0 -> fp_ok s -> hrel s (RD.d_ts t) X TS 2 ->
  dst_rel (DS.set_status (DS.set_strm X (DS.cset_adler (DS.ds_strm X) DL.adler32_init)) DS.BUSY_STATE)
          (RD.setD_status DS.BUSY_STATE
             (RD.setD_strm (RD.setZ_adler DL.adler32_init (RD.d_strm t)) (RD.setD_ts TS t))) pre_out pre_in
  /\ DS.ds_sym_next (DS.set_status (DS.set_strm X (DS.cset_adler (DS.ds_strm X) DL.adler32_init)) DS.BUSY_STATE) = 0
  /\ room (DS.set_status (DS.set_strm X (DS.cset_adler (DS.ds_strm X) DL.adler32_init)) DS.BUSY_STATE) 2
  /\ fp_ok (DS.set_status (DS.set_strm X (DS.cset_adler (DS.ds_strm X) DL.adler32_init)) DS.BUSY_STATE).
Proof.
  intros s t pre_out pre_in X TS Hrel Hsn Hok (F & T & B & R).
  pose proof (dst_rel_bw4 _ _ _ _ _ _ Hrel Hsn F T B) as H1.
  pose proof (fp_ok_bw4 _ _ F Hok) as Hok1.
  destruct (bw4_proj _ _ F) as (_ & _ & _ & Esn).
  split; [apply dst_rel_hdr_finish; exact H1|].
  unfold room, fp_ok in *. autorewrite with s5f_status s5f_strm s5c_adler.
  split; [rewrite Esn; exact Hsn|]. split; [exact R | exact Hok1].
Qed.

(** The header bytes, before the flush.  S5 computes the header word from its
    own fields, RT from [d_cfg] and [ls_strstart]; [dst_rel] makes them equal,
    and [h + (31 - h mod 31)] is RT's [h + 31 - h mod 31]. *)
Lemma pair_zhdr_st : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> DS.ds_sym_next s = 0 -> room s 8 -> fp_ok s ->
  dst_rel (DSf.zhdr_st s) (RD.zlib_header t) pre_out pre_in
  /\ DS.ds_sym_next (DSf.zhdr_st s) = 0 /\ room (DSf.zhdr_st s) 2 /\ fp_ok (DSf.zhdr_st s).
Proof.
  intros s t pre_out pre_in Hrel Hsn Hroom Hok.
  pose proof Hrel as (Hg & Hlz & Hbw & _ & _ & Hst).
  destruct Hg as (Glv & Gst & Gwb & _).
  destruct Hlz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lss & _).
  destruct Hst as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Sad & _).
  destruct Hroom as (Hpo & Hr).
  unfold DSf.zhdr_st, RD.zlib_header. cbv zeta.
  rewrite <- Glv, <- Gst, <- Gwb, <- Lss, Sad.
  match goal with |- context [DL.putShortMSB s ?h] =>
    match goal with |- context [RD.putShortMSB ?h' (RD.d_ts t)] =>
      assert (Eh : h' = h) by (rewrite <- Z.add_sub_assoc; reflexivity); rewrite Eh; clear Eh end end.
  match goal with |- context [DL.putShortMSB s ?h] => set (h5 := h) end.
  clearbody h5.
  destruct (putShortMSB_strstart_strm s h5) as (Ess & Est). rewrite Ess, Est.
  match goal with |- context [RD.setD_status ?x _] => change x with DS.BUSY_STATE end.
  match goal with |- context [RD.setZ_adler ?a _] => change a with DL.adler32_init end.
  destruct (negb (DS.ds_strstart s =? 0)); cbv beta iota;
    (eapply hdr_finish; [exact Hrel | exact Hsn | exact Hok |]).
  - apply hrel_putShortMSB; [lia| |reflexivity|reflexivity].
    apply hrel_putShortMSB; [lia| |apply u8_shiftr8_wrap32|apply u8_land_wrap32].
    apply hrel_putShortMSB; [lia| |reflexivity|reflexivity].
    apply hrel_start; [exact Hbw|]. split; [exact Hpo | lia].
  - apply hrel_putShortMSB; [lia| |reflexivity|reflexivity].
    apply hrel_start; [exact Hbw|]. split; [exact Hpo | lia].
Qed.

(** The pair: S5's [deflate_zlib_header] against RT's [zlib_header], the
    flush and the pending test [deflate_body] runs after it. *)
Theorem pair_zlib_header : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> DS.ds_sym_next s = 0 -> room s 8 -> fp_ok s ->
  let t2 := RD.flush_pending (RD.zlib_header t) in
  let nz := negb (RC.zlen (ZBitsOut.bw_out (RT.ts_bw (RD.d_ts t2))) =? 0) in
  dst_rel (fst (DZ.deflate_zlib_header s)) (if nz then RD.setD_lastflush (-1) t2 else t2) pre_out pre_in
  /\ snd (DZ.deflate_zlib_header s) = (if nz then Some Z_OK else None)
  /\ DS.ds_sym_next (fst (DZ.deflate_zlib_header s)) = 0.
Proof.
  intros s t pre_out pre_in Hrel Hsn Hroom Hok. cbv zeta.
  destruct (pair_zhdr_st s t pre_out pre_in Hrel Hsn Hroom Hok) as (H1 & Hsn1 & Hr1 & Hok1).
  pose proof (dst_flush_pending _ _ _ _ H1 Hsn1 (or_intror Hr1) Hok1) as H2.
  pose proof (flush_sym_next (DSf.zhdr_st s)) as Hsn2. rewrite Hsn1 in Hsn2.
  rewrite DSf.deflate_zlib_header_eq. cbv zeta.
  revert H2 Hsn2.
  generalize (DL.flush_pending (DSf.zhdr_st s)) as s2.
  generalize (RD.flush_pending (RD.zlib_header t)) as t2.
  intros t2 s2 H2 Hsn2.
  rewrite (pend_zlen _ _ _ _ H2).
  destruct (negb (DS.ds_pending s2 =? 0)); cbn [fst snd].
  - split; [apply dst_rel_last_flush; exact H2|]. split; [reflexivity|].
    autorewrite with s5f_last_flush. exact Hsn2.
  - split; [exact H2|]. split; [reflexivity | exact Hsn2].
Qed.

(* ------------------------------------------------------------------------- *)
(* 5.  The trailer                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem pair_deflate_trailer : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> DS.ds_sym_next s = 0 -> room s 10 -> fp_ok s ->
  exists t', RD.deflate_trailer t = RD.DfRet (snd (DZ.deflate_trailer s)) t'
    /\ dst_rel (fst (DZ.deflate_trailer s)) t' pre_out pre_in
    /\ DS.ds_sym_next (fst (DZ.deflate_trailer s)) = 0.
Proof.
  intros s t pre_out pre_in Hrel Hsn Hroom Hok.
  rewrite DSf.deflate_trailer_eq. unfold RD.deflate_trailer. cbv zeta.
  match goal with |- context [RD.flush_pending (RD.setD_ts ?X t)] =>
    assert (HR : hrel s (RD.d_ts t) (DSf.trailer_st s) X 2);
    [| revert HR; generalize X as TS; intros TS HR] end.
  { pose proof Hrel as (Hg & _ & Hbw & _ & _ & Hst).
    destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gwr & _).
    destruct Hst as (_ & _ & _ & _ & _ & _ & _ & _ & Sti & _ & Sad & _).
    destruct Hroom as (Hpo & Hr).
    unfold DSf.trailer_st. cbv zeta. rewrite <- Gwr, Sad, Sti.
    destruct (DS.ds_wrap s =? 2); cbv beta iota.
    - do 8 (apply hrel_put_byte; [lia| |apply u8_land255]).
      apply hrel_start; [exact Hbw|]. split; [exact Hpo | lia].
    - apply hrel_putShortMSB; [lia| |reflexivity|reflexivity].
      apply hrel_putShortMSB; [lia| |apply u8_shiftr8_wrap32|apply u8_land_wrap32].
      apply hrel_start; [exact Hbw|]. split; [exact Hpo | lia]. }
  destruct HR as (F & T & B & R).
  pose proof (dst_rel_bw4 _ _ _ _ _ _ Hrel Hsn F T B) as H1.
  destruct (bw4_proj _ _ F) as (_ & _ & _ & Esn1).
  pose proof (fp_ok_bw4 _ _ F Hok) as Hok1.
  assert (Hsn1 : DS.ds_sym_next (DSf.trailer_st s) = 0) by (rewrite Esn1; exact Hsn).
  pose proof (dst_flush_pending _ _ _ _ H1 Hsn1 (or_intror R) Hok1) as H2.
  pose proof (flush_sym_next (DSf.trailer_st s)) as Hsn2. rewrite Hsn1 in Hsn2.
  revert H2 Hsn2.
  generalize (DL.flush_pending (DSf.trailer_st s)) as s2.
  generalize (RD.flush_pending (RD.setD_ts TS t)) as t2.
  intros t2 s2 H2 Hsn2.
  assert (Ew : DS.ds_wrap s2 = RD.d_wrap t2)
    by (destruct H2 as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gw & _) & _);
        exact Gw).
  rewrite <- Ew.
  destruct (0 <? DS.ds_wrap s2); cbn [fst snd].
  - exists (RD.setD_wrap (- DS.ds_wrap s2) t2).
    pose proof (dst_rel_wrap _ _ _ _ (- DS.ds_wrap s2) H2) as H3.
    split; [|split; [exact H3 | autorewrite with s5f_wrap; exact Hsn2]].
    rewrite (pend_zlen _ _ _ _ H3).
    destruct (negb (DS.ds_pending (DS.set_wrap s2 (- DS.ds_wrap s2)) =? 0)); reflexivity.
  - exists t2. split; [|split; [exact H2 | exact Hsn2]].
    rewrite (pend_zlen _ _ _ _ H2). destruct (negb (DS.ds_pending s2 =? 0)); reflexivity.
Qed.

Print Assumptions pair_zlib_header.
Print Assumptions pair_deflate_trailer.
