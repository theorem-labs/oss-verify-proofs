(** * Bridge.DEmit.DStKit — pair D13 ([deflate_stored]), part 1: the invariant and the kit.

    [sti s t]: what holds at the top of every trip of the two stored loops,
    and after them: the deflate relation, S5's queue empty and starting at 0
    with no bits pending and no symbol, the output counters in range, and on
    RT's side compress_fuzzer's geometry ([cfg_facts]), the [read_buf]
    premises ([rb_ok]), the window and its positions.

    The kit, each piece stated once for the trip and the tail files:
    - [dst_rel_frame4]: a write to S5's queue fields against a [set_bw] on
      RT, no symbol pending (the four-byte patch rewrites bytes below
      [pending], which [bw4] does not allow);
    - the dummy stored block's header on an empty queue is five bytes and
      leaves no bit pending ([tsb_hdr]);
    - the patch of its four length bytes ([dst_patch], S5's [sb_patch]
      against RT's [patch_len4]);
    - [flush_pending] on a queue the output can take whole ([s5_flush_all]);
    - the output counters ([dst_counters]) and the direct copy from the
      window ([dst_lcopy], S5's [st_lcopy]).

    Ownership: a worker (group D).  Reviewer: a worker. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz DeflateBlk
  RefDeflStored2 RefDeflStored4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import BrDFlush DTrStored DZHeader.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MLz.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module B2 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored2.
Module B4 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored4.

(* ------------------------------------------------------------------------- *)
(* 1.  The invariant                                                         *)
(* ------------------------------------------------------------------------- *)

Record sti (s : DS.deflate_state) (t : RD.DSt) (pre_out pre_in : list Z) : Prop := mkSti {
  si_rel : dst_rel s t pre_out pre_in;
  si_pend : DS.ds_pending s = 0;
  si_pout : DS.ds_pending_out s = 0;
  si_biv : DS.ds_bi_valid s = 0;
  si_sym : DS.ds_sym_next s = 0;
  si_aout : 0 <= DS.cs_avail_out (DS.ds_strm s) < 2 ^ 32;
  si_tout : 0 <= DS.cs_total_out (DS.ds_strm s);
  si_room : DS.cs_total_out (DS.ds_strm s) + DS.cs_avail_out (DS.ds_strm s)
            + arr_len (DS.ds_pending_buf s) < 2 ^ 64;
  si_cfg : cfg_facts (RD.d_cfg t);
  si_rb : rb_ok t;
  si_wsz : RD.ls_windowsize (RD.d_ls t) = 65536;
  si_bs : 0 <= RD.ls_blockstart (RD.d_ls t) <= RD.ls_strstart (RD.d_ls t);
  si_ss : RD.ls_strstart (RD.d_ls t) <= 65536;
  si_done : RD.ls_strstart (RD.d_ls t) <= RC.zlen (RD.zs_done (RD.d_strm t));
  si_inlen : RC.zlen (RD.zs_done (RD.d_strm t)) + RC.zlen (RD.zs_in (RD.d_strm t)) < 2 ^ 32;
  si_win : forall i, 0 <= i < 65536 -> 0 <= RD.ls_window (RD.d_ls t) i < 256;
  si_ins : 0 <= RD.ls_insert (RD.d_ls t) <= 32768
}.

(** The S5 fields the stored code reads, through [dst_rel] and [cfg_facts]. *)
Lemma rel_view : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> cfg_facts (RD.d_cfg t) ->
  DS.ds_w_size s = 32768 /\ DS.ds_pending_buf_size s = 65536 /\ arr_len (DS.ds_pending_buf s) = 65536
  /\ DS.ds_window_size s = RD.ls_windowsize (RD.d_ls t) /\ arr_len (DS.ds_window s) = RD.ls_windowsize (RD.d_ls t)
  /\ DS.ds_strstart s = RD.ls_strstart (RD.d_ls t) /\ DS.ds_block_start s = RD.ls_blockstart (RD.d_ls t)
  /\ DS.ds_wrap s = RD.d_wrap t
  /\ DS.cs_avail_in (DS.ds_strm s) = RC.zlen (RD.zs_in (RD.d_strm t))
  /\ DS.cs_avail_out (DS.ds_strm s) = RD.zs_availout (RD.d_strm t)
  /\ DS.cs_total_out (DS.ds_strm s) = RD.zs_totalout (RD.d_strm t)
  /\ DS.ds_insert s = RD.ls_insert (RD.d_ls t) /\ DS.ds_high_water s = RD.ls_highwater (RD.d_ls t)
  /\ DS.ds_matches s = RT.ts_matches (RD.d_ts t)
  /\ DS.ds_bi_valid s = ZBitsOut.bw_valid (RT.ts_bw (RD.d_ts t)).
Proof.
  intros s t pre_out pre_in (Hg & Hlz & Hbw & _ & Htr & Hst) Hc.
  destruct Hg as (_ & _ & _ & Gws & _ & _ & _ & _ & _ & _ & Gpbs & _ & _ & _ & _ & _ & _ & Gwr & _ & Gpbl).
  destruct Hlz as (Lwl & _ & _ & _ & _ & _ & Lwsz & _ & Lbs & _ & _ & _ & Lss & _ & _ & _ & Lins & Lhw).
  destruct Hst as (Hni & Hai & Hfit & _ & Hin & _ & _ & Hao & _ & Hto & _).
  destruct Htr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Tm).
  destruct Hbw as (_ & _ & Bv).
  destruct Hc.
  assert (Hzl : RC.zlen (RD.zs_in (RD.d_strm t)) = DS.cs_avail_in (DS.ds_strm s)).
  { rewrite <- Hin. change RC.zlen with (@zlength Z). rewrite arr_slice_length. lia. }
  and_goal; congruence.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  A write to S5's queue fields against [set_bw]                         *)
(* ------------------------------------------------------------------------- *)

Lemma rt_setD_ts_ts : forall a b t, RD.setD_ts a (RD.setD_ts b t) = RD.setD_ts a t.
Proof. intros a b t. destruct t. reflexivity. Qed.

Lemma tbw_set_bw : forall ts x, tbw ts (RT.set_bw x ts).
Proof. intros ts x. reflexivity. Qed.

Lemma dst_rel_frame4 : forall s s' t ts' pre_out pre_in,
  dst_rel s t pre_out pre_in -> DS.ds_sym_next s = 0 ->
  s' = set4 s (DS.ds_pending_buf s') (DS.ds_pending s') (DS.ds_bi_buf s') (DS.ds_bi_valid s') ->
  arr_len (DS.ds_pending_buf s') = arr_len (DS.ds_pending_buf s) ->
  tbw (RD.d_ts t) ts' -> bw_rel s' (RT.ts_bw ts') ->
  dst_rel s' (RD.setD_ts ts' t) pre_out pre_in.
Proof.
  intros s s' t ts' pre_out pre_in (Hg & Hlz & Hbw & Hsym & Htr & Hst) Hsn E Lpb T Hb.
  assert (Est : DS.ds_strm s' = DS.ds_strm s) by (rewrite E; unfold set4; s5bw; reflexivity).
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

(* ------------------------------------------------------------------------- *)
(* 3.  The dummy stored block on an empty queue                              *)
(* ------------------------------------------------------------------------- *)

Lemma send_bits3_0 : forall s v, DS.ds_bi_valid s = 0 ->
  DS.ds_pending (DT.send_bits s v 3) = DS.ds_pending s /\ DS.ds_bi_valid (DT.send_bits s v 3) = 3.
Proof.
  intros s v H. unfold DT.send_bits. cbv zeta. rewrite H.
  replace (DS.Buf_size - 3 <? 0) with false by reflexivity. cbv beta iota.
  s5bw. rewrite H. split; reflexivity.
Qed.

Lemma bi_windup3 : forall s, DS.ds_bi_valid s = 3 ->
  DS.ds_pending (DT.bi_windup s) = DS.ds_pending s + 1 /\ DS.ds_bi_valid (DT.bi_windup s) = 0.
Proof.
  intros s H. unfold DT.bi_windup. cbv zeta. rewrite H.
  replace (8 <? 3) with false by reflexivity. replace (0 <? 3) with true by reflexivity. cbv beta iota.
  unfold DS.put_byte. cbv zeta. s5bw. split; reflexivity.
Qed.

Lemma biv_put_short : forall s w, DS.ds_bi_valid (DT.put_short s w) = DS.ds_bi_valid s.
Proof. intros s w. unfold DT.put_short, DS.put_byte. cbv zeta. s5bw. reflexivity. Qed.

Lemma tsb_hdr : forall s last, DS.ds_bi_valid s = 0 -> DS.ds_pending s = 0 ->
  DS.ds_pending (DT.tr_stored_block s None 0 last) = 5
  /\ DS.ds_bi_valid (DT.tr_stored_block s None 0 last) = 0.
Proof.
  intros s last Hbv Hp.
  destruct (send_bits3_0 s (Z.shiftl DS.STORED_BLOCK 1 + last) Hbv) as (P1 & V1).
  destruct (bi_windup3 _ V1) as (P2 & V2).
  split; [rewrite tsb_pending; lia|].
  rewrite tsb_unfold. cbv zeta. unfold tsb_copy. cbn [negb Z.eqb]. s5bw.
  rewrite !biv_put_short. exact V2.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  The four length bytes                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma slice_patch4 : forall (a : arr) p v0 v1 v2 v3, 4 <= p <= arr_len a ->
  arr_slice (arr_set (arr_set (arr_set (arr_set a (p - 4) v0) (p - 3) v1) (p - 2) v2) (p - 1) v3) 0 p
  = firstn (Z.to_nat (p - 4)) (arr_slice a 0 p) ++ [v0; v1; v2; v3].
Proof.
  intros a p v0 v1 v2 v3 Hp.
  set (b := arr_set (arr_set (arr_set (arr_set a (p - 4) v0) (p - 3) v1) (p - 2) v2) (p - 1) v3).
  assert (Lb : arr_len b = arr_len a) by (unfold b; rewrite !arr_len_set; reflexivity).
  assert (E0 : arr_get b (p - 4) = v0).
  { unfold b. rewrite !arr_get_set_other by lia. apply arr_get_set_same. lia. }
  assert (E1 : arr_get b (p - 3) = v1).
  { unfold b. rewrite !arr_get_set_other by lia. apply arr_get_set_same. rewrite arr_len_set. lia. }
  assert (E2 : arr_get b (p - 2) = v2).
  { unfold b. rewrite !arr_get_set_other by lia. apply arr_get_set_same. rewrite !arr_len_set. lia. }
  assert (E3 : arr_get b (p - 1) = v3).
  { unfold b. apply arr_get_set_same. rewrite !arr_len_set. lia. }
  assert (Pre : forall k, (k < Z.to_nat (p - 4))%nat -> arr_get b (0 + Z.of_nat k) = arr_get a (0 + Z.of_nat k)).
  { intros k Hk. unfold b. rewrite !arr_get_set_other by lia. reflexivity. }
  clearbody b.
  unfold arr_slice. replace (Z.to_nat p) with (Z.to_nat (p - 4) + 4)%nat by lia.
  rewrite !slice_nat_app.
  rewrite firstn_app, arr_slice_nat_length, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite arr_slice_nat_length; lia).
  f_equal.
  - apply slice_nat_ext. exact Pre.
  - cbn [arr_slice_nat]. rewrite Z2Nat.id by lia.
    replace (0 + (p - 4)) with (p - 4) by lia. replace (p - 4 + 1) with (p - 3) by lia.
    replace (p - 3 + 1) with (p - 2) by lia. replace (p - 2 + 1) with (p - 1) by lia.
    rewrite E0, E1, E2, E3. reflexivity.
Qed.

Lemma br_patch : forall x b len, bw_rel x b -> DS.ds_pending_out x = 0 -> 4 <= DS.ds_pending x ->
  bw_rel (B2.sb_patch x len)
    {| ZBitsOut.bw_out := RD.patch_len4 len (ZBitsOut.bw_out b); ZBitsOut.bw_buf := ZBitsOut.bw_buf b;
       ZBitsOut.bw_valid := ZBitsOut.bw_valid b |}.
Proof.
  intros x b len ((Hpo & Hp & Hin & Hsl) & Hbb & Hbv) Hpo0 H4.
  rewrite Hpo0 in Hsl, Hin.
  unfold B2.sb_patch. cbv zeta. unfold bw_rel, pend_rel.
  cbn [ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid].
  autorewrite with s5f_pending_buf. rewrite !arr_len_set. rewrite Hpo0.
  split; [split; [lia|split; [lia|split; [lia|]]]|split; assumption].
  rewrite slice_patch4 by lia. rewrite Hsl. unfold RD.patch_len4. cbv zeta.
  replace (length (ZBitsOut.bw_out b)) with (Z.to_nat (DS.ds_pending x))
    by (rewrite <- Hsl; unfold arr_slice; symmetry; apply arr_slice_nat_length).
  replace (Z.to_nat (DS.ds_pending x) - 4)%nat with (Z.to_nat (DS.ds_pending x - 4)) by lia.
  f_equal. rewrite !wrap8_u8. rewrite wrap32_mod. reflexivity.
Qed.

Lemma dst_patch : forall x t ts1 len pre_out pre_in,
  dst_rel x (RD.setD_ts ts1 t) pre_out pre_in -> DS.ds_sym_next x = 0 -> DS.ds_pending_out x = 0 ->
  4 <= DS.ds_pending x ->
  dst_rel (B2.sb_patch x len)
    (RD.setD_ts (RT.set_bw {| ZBitsOut.bw_out := RD.patch_len4 len (ZBitsOut.bw_out (RT.ts_bw ts1));
                              ZBitsOut.bw_buf := ZBitsOut.bw_buf (RT.ts_bw ts1);
                              ZBitsOut.bw_valid := ZBitsOut.bw_valid (RT.ts_bw ts1) |} ts1) t)
    pre_out pre_in.
Proof.
  intros x t ts1 len pre_out pre_in H Hsn Hpo H4.
  rewrite <- (rt_setD_ts_ts _ ts1 t).
  apply (dst_rel_frame4 x).
  - exact H.
  - exact Hsn.
  - unfold B2.sb_patch, set4. cbv zeta. s5bw. destruct x; reflexivity.
  - unfold B2.sb_patch. cbv zeta. s5bw. rewrite !arr_len_set. reflexivity.
  - cbn [RD.d_ts RD.setD_ts]. apply tbw_set_bw.
  - cbn [RT.ts_bw RT.set_bw]. apply br_patch; [|exact Hpo|exact H4].
    apply dst_rel_bw in H. cbn [RD.d_ts RD.setD_ts] in H. exact H.
Qed.

Lemma patch_frame : forall x len,
  DS.ds_pending (B2.sb_patch x len) = DS.ds_pending x
  /\ DS.ds_pending_out (B2.sb_patch x len) = DS.ds_pending_out x
  /\ DS.ds_bi_valid (B2.sb_patch x len) = DS.ds_bi_valid x
  /\ DS.ds_sym_next (B2.sb_patch x len) = DS.ds_sym_next x
  /\ DS.ds_strm (B2.sb_patch x len) = DS.ds_strm x
  /\ arr_len (DS.ds_pending_buf (B2.sb_patch x len)) = arr_len (DS.ds_pending_buf x).
Proof.
  intros x len. unfold B2.sb_patch. cbv zeta. s5bw. rewrite !arr_len_set.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 5.  [flush_pending] when the output takes the whole queue                 *)
(* ------------------------------------------------------------------------- *)

Lemma s5_flush_all : forall s, 0 <= DS.ds_bi_valid s < 8 -> DS.ds_pending_out s = 0 ->
  0 < DS.ds_pending s < 2 ^ 32 -> DS.ds_pending s <= DS.cs_avail_out (DS.ds_strm s) ->
  let s' := DL.flush_pending s in
  DS.ds_pending s' = 0 /\ DS.ds_pending_out s' = 0 /\ DS.ds_bi_valid s' = DS.ds_bi_valid s
  /\ DS.ds_sym_next s' = DS.ds_sym_next s
  /\ DS.cs_avail_out (DS.ds_strm s') = DS.cs_avail_out (DS.ds_strm s) - DS.ds_pending s
  /\ DS.cs_total_out (DS.ds_strm s') = wrap64 (DS.cs_total_out (DS.ds_strm s) + DS.ds_pending s)
  /\ arr_len (DS.ds_pending_buf s') = arr_len (DS.ds_pending_buf s).
Proof.
  intros s Hbv Hpo Hp Ha. cbv zeta.
  unfold DL.flush_pending, DT.tr_flush_bits, DT.bi_flush. cbv zeta.
  replace (DS.ds_bi_valid s =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (8 <=? DS.ds_bi_valid s) with false by (symmetry; apply Z.leb_gt; lia).
  cbv beta iota.
  rewrite (wrap32_id (DS.ds_pending s)) by lia.
  replace (DS.cs_avail_out (DS.ds_strm s) <? DS.ds_pending s) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (DS.ds_pending s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv beta iota.
  autorewrite with s5f_pending s5f_strm s5f_pending_out.
  rewrite Z.sub_diag. cbn [Z.eqb].
  autorewrite with s5f_pending s5f_strm s5f_pending_out s5f_bi_valid s5f_sym_next s5f_pending_buf
    s5c_avail_out s5c_total_out s5c_emit.
  repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 6.  Output counters and the direct copy                                   *)
(* ------------------------------------------------------------------------- *)

Lemma dst_counters : forall s t pre_out pre_in k, dst_rel s t pre_out pre_in ->
  0 <= DS.cs_total_out (DS.ds_strm s) + k < 2 ^ 64 ->
  dst_rel (DS.set_strm s (DS.cset_total_out (DS.cset_avail_out (DS.ds_strm s) (DS.cs_avail_out (DS.ds_strm s) - k))
                                            (wrap64 (DS.cs_total_out (DS.ds_strm s) + k))))
          (RD.setD_strm (RD.setZ_availout (RD.zs_availout (RD.d_strm t) - k)
                           (RD.setZ_totalout (RD.zs_totalout (RD.d_strm t) + k) (RD.d_strm t))) t) pre_out pre_in.
Proof.
  intros s t pre_out pre_in k H Hk. rewrite wrap64_id by exact Hk.
  rel_unfold. rt_proj. cbn [RD.setZ_availout RD.setZ_totalout RD.zs_in RD.zs_done RD.zs_out RD.zs_availout
                            RD.zs_totalin RD.zs_totalout RD.zs_adler RD.zs_datatype].
  autorewrite with s5f_strm s5c_total_out s5c_avail_out.
  and_hyps. and_goal; first [assumption | congruence].
Qed.

Lemma dst_lcopy : forall s t pre_out pre_in k, dst_rel s t pre_out pre_in ->
  0 <= k -> 0 <= RD.ls_blockstart (RD.d_ls t) -> RD.ls_blockstart (RD.d_ls t) + k <= RD.ls_windowsize (RD.d_ls t) ->
  0 <= DS.cs_total_out (DS.ds_strm s) + k < 2 ^ 64 ->
  dst_rel (B4.st_lcopy s k)
    (RD.setD_ls (RD.setL_blockstart (RD.ls_blockstart (RD.d_ls t) + k) (RD.d_ls t))
       (RD.setD_strm (RD.setZ_out (RD.zs_out (RD.d_strm t)
                                   ++ RD.win_take (RD.ls_window (RD.d_ls t)) (RD.ls_blockstart (RD.d_ls t)) k)
                        (RD.setZ_availout (RD.zs_availout (RD.d_strm t) - k)
                           (RD.setZ_totalout (RD.zs_totalout (RD.d_strm t) + k) (RD.d_strm t)))) t))
    pre_out pre_in.
Proof.
  intros s t pre_out pre_in k H Hk Hb0 Hbk Htk.
  assert (Hsl : arr_slice (DS.ds_window s) (DS.ds_block_start s) k
                = RD.win_take (RD.ls_window (RD.d_ls t)) (RD.ls_blockstart (RD.d_ls t)) k).
  { pose proof H as (_ & Hlz & _). pose proof (lzr_win _ _ Hlz) as Rw. rewrite (lzr_bs _ _ Hlz).
    rewrite (arr_rel_slice _ _ _ _ _ k Rw) by lia. reflexivity. }
  unfold B4.st_lcopy. rewrite wrap64_id by exact Htk. revert Hsl.
  rel_unfold. intros Hsl. rt_proj.
  cbn [RD.d_cfg RD.d_status RD.d_wrap RD.d_lastflush RD.d_ts RD.d_ls RD.setD_ls RD.d_strm RD.setD_strm
       RD.setZ_out RD.setZ_availout RD.setZ_totalout RD.zs_in RD.zs_done RD.zs_out RD.zs_availout
       RD.zs_totalin RD.zs_totalout RD.zs_adler RD.zs_datatype RD.setL_blockstart RD.ls_window RD.ls_prev
       RD.ls_head RD.ls_insh RD.ls_blockstart RD.ls_matchlen RD.ls_prevmatch RD.ls_matchavail
       RD.ls_strstart RD.ls_matchstart RD.ls_lookahead RD.ls_prevlen RD.ls_insert RD.ls_highwater
       RD.ls_windowsize].
  autorewrite with s5f_block_start s5f_strm s5c_total_out s5c_avail_out.
  unfold DS.cs_emit. autorewrite with s5c_out_rev.
  and_hyps. and_goal; try first [assumption | congruence].
  match goal with H : RD.zs_out (RD.d_strm t) = _ |- _ => rewrite H end.
  rewrite <- Hsl. rewrite !rev_append_rev, !app_nil_r, rev_app_distr, rev_involutive.
  rewrite <- app_assoc. reflexivity.
Qed.
