(** * Bridge.DEmit.BrFlushBlock — pair D23 of PAIRS.md: [FLUSH_BLOCK_ONLY] / [FLUSH_BLOCK], S5 vs RT.

    Both macros are [_tr_flush_block] (pair D22, [BrTrFlush]), then
    [block_start := strstart], then [flush_pending] ([BrDFlush]).  S5's
    flush-entry record comes from [BrFbKit.fb_entry_of], so S5's closed
    [FB_CALL] applies; its [fb_post] supplies every S5 fact about the
    block's result that the rest of the proof uses (empty symbol buffer,
    reset frequencies, queue bounds, byte ranges).  What this file adds:

    - [dst_block_start]: the [block_start] store on both sides;
    - [em_after_flush]: when the flush leaves output room, [em_inv] holds
      again (the queue has drained and the next block starts empty). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz DeflateBlk DeflateOverlay TreeModel
  RefDeflSafeFB RefDeflSafeE5 OverlayCoreL RefDeflSafeFBT RefDeflSafeZ.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs BrDFlush BrTrFlush BrFbKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module FB := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeFB.
Module FBT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeFBT.

Ltac em_names H :=
  destruct H as [Elev Estr Edt Elbs Elbs2 Epbl Esymend Epend Epout Ebiv Ebib Epbb Etout Eaout Eroom
                 Esn Ensym Esyms Ehist Eopt Estat Etl Efc Edl Edep Eblc].

(* ------------------------------------------------------------------------- *)
(* 1.  [block_start := strstart] on both sides                               *)
(* ------------------------------------------------------------------------- *)

Lemma dst_block_start : forall s t pre_out pre_in v,
  dst_rel s t pre_out pre_in ->
  dst_rel (DS.set_block_start s v) (RD.setD_ls (RD.setL_blockstart v (RD.d_ls t)) t) pre_out pre_in.
Proof.
  intros s t pre_out pre_in v (Hg & Hl & Hb & Hs & Ht & Hm).
  unfold dst_rel. split; [exact Hg|]. split; [|split; [exact Hb|split; [exact Hs|split; [exact Ht | exact Hm]]]].
  unfold lz_rel in *. cbv zeta in *.
  destruct Hl as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & L18).
  repeat split; assumption.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The macros as compositions                                            *)
(* ------------------------------------------------------------------------- *)

Lemma s5_fbo_eq : forall s last,
  DL.flush_block_only s last
  = DL.flush_pending (DS.set_block_start (DT.tr_flush_block s (DO.fb_buf s) (DO.fb_len s) last)
                                         (DS.ds_strstart (DT.tr_flush_block s (DO.fb_buf s) (DO.fb_len s) last))).
Proof. reflexivity. Qed.

Lemma rt_fbo_eq : forall t last,
  RD.flush_block_only last t
  = RD.flush_pending (RD.setD_ls (RD.setL_blockstart (RD.ls_strstart (RD.d_ls t)) (RD.d_ls t)) (rt_fb_state t last)).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The invariant after a flush that leaves output room                   *)
(* ------------------------------------------------------------------------- *)

Lemma bi_flush_bib : forall s, 0 <= DS.ds_bi_buf s < 2 ^ 16 -> 0 <= DS.ds_bi_buf (DT.bi_flush s) < 2 ^ 16.
Proof.
  intros s H. unfold DT.bi_flush, DT.put_short, DS.put_byte. cbv zeta.
  split_ifs; bw6_fields; try lia.
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma flush_pending_bib : forall s, 0 <= DS.ds_bi_buf s < 2 ^ 16 ->
  0 <= DS.ds_bi_buf (DL.flush_pending s) < 2 ^ 16.
Proof.
  intros s H. pose proof (bi_flush_bib s H) as Q.
  unfold DL.flush_pending, DT.tr_flush_bits. cbv zeta.
  revert Q. generalize (DT.bi_flush s) as s1. intros s1 Q.
  split_ifs; autorewrite with s5f_pending s5f_strm s5f_pending_out; exact Q.
Qed.

(** The fields [em_core] reads that a [block_start] store and a
    [flush_pending] leave alone. *)
Lemma fp_bs_frame : forall x v,
  let y := DL.flush_pending (DS.set_block_start x v) in
  DS.ds_level y = DS.ds_level x /\ DS.ds_strategy y = DS.ds_strategy x
  /\ DS.ds_lit_bufsize y = DS.ds_lit_bufsize x /\ DS.ds_sym_end y = DS.ds_sym_end x
  /\ DS.ds_sym_next y = DS.ds_sym_next x /\ DS.ds_opt_len y = DS.ds_opt_len x
  /\ DS.ds_static_len y = DS.ds_static_len x
  /\ DS.ds_dyn_ltree_fc y = DS.ds_dyn_ltree_fc x /\ DS.ds_dyn_ltree_dl y = DS.ds_dyn_ltree_dl x
  /\ DS.ds_dyn_dtree_fc y = DS.ds_dyn_dtree_fc x /\ DS.ds_dyn_dtree_dl y = DS.ds_dyn_dtree_dl x
  /\ DS.ds_bl_tree_fc y = DS.ds_bl_tree_fc x /\ DS.ds_bl_tree_dl y = DS.ds_bl_tree_dl x
  /\ DS.ds_bl_count y = DS.ds_bl_count x /\ DS.ds_heap y = DS.ds_heap x /\ DS.ds_depth y = DS.ds_depth x.
Proof.
  intros x v. cbv zeta. rewrite flush_pending_shape. bw6_fields. autorewrite with s5f_block_start.
  repeat split; reflexivity.
Qed.

Lemma em_after_flush : forall s s8 t9 v,
  em_core s ->
  FB.fb_post s 0 s8 \/ FB.fb_post s 1 s8 ->
  DS.ds_level s8 = DS.ds_level s -> DS.ds_strategy s8 = DS.ds_strategy s ->
  DS.ds_lit_bufsize s8 = DS.ds_lit_bufsize s -> DS.ds_sym_end s8 = DS.ds_sym_end s ->
  (* the stream's output fields, through RT *)
  DS.cs_avail_out (DS.ds_strm (DL.flush_pending (DS.set_block_start s8 v))) = RD.zs_availout (RD.d_strm (RD.flush_pending t9)) ->
  DS.cs_total_out (DS.ds_strm (DL.flush_pending (DS.set_block_start s8 v))) = RD.zs_totalout (RD.d_strm (RD.flush_pending t9)) ->
  RD.zs_availout (RD.d_strm t9) = DS.cs_avail_out (DS.ds_strm s) ->
  RD.zs_totalout (RD.d_strm t9) = DS.cs_total_out (DS.ds_strm s) ->
  DS.cs_avail_out (DS.ds_strm (DL.flush_pending (DS.set_block_start s8 v))) <> 0 ->
  em_inv (DL.flush_pending (DS.set_block_start s8 v)).
Proof.
  intros s s8 t9 v H FP E1 E2 E3 E4 HA HT RA RT0 Hav.
  assert (FP' : exists last, FB.fb_post s last s8) by (destruct FP as [FP|FP]; eexists; exact FP).
  destruct FP' as [last FP0].
  destruct FP0 as [_ _ Fstrm Fsn _ Fopt Fstat Flt Fdt Fbt Ftl Ffc Fdl Fdep Fblc Fpend Fpout Fbiv _ Fbib Fpbl Fpbb].
  em_names H.
  set (x := DS.set_block_start s8 v) in *.
  set (y := DL.flush_pending x) in *.
  destruct (fp_bs_frame s8 v) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  fold x y in G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16.
  destruct Fstrm as (dt & Hst & Hdt).
  assert (Hx_strm : DS.ds_strm x = DS.cset_data_type (DS.ds_strm s) dt) by (subst x; autorewrite with s5f_block_start; exact Hst).
  assert (Hx_pb : arr_len (DS.ds_pending_buf x) = DS.ds_lit_bufsize s * 4) by (subst x; autorewrite with s5f_block_start; exact Fpbl).
  destruct (flush_pending_drained x) as (D1 & D2 & D3).
  { subst x; autorewrite with s5f_block_start. exact Fpout. }
  { subst x; autorewrite with s5f_block_start. lia. }
  { subst x; autorewrite with s5f_block_start. lia. }
  { subst x; autorewrite with s5f_block_start. exact Fbiv. }
  { exact Hav. }
  fold y in D1, D2, D3.
  destruct (rt_flush_pending_out t9) as (O1 & O2 & O3); [lia|].
  assert (Hy_dt : DS.cs_data_type (DS.ds_strm y) = dt).
  { subst y. destruct (flush_pending_strm_in x) as (_ & _ & _ & _ & _ & S6). rewrite S6, Hx_strm. reflexivity. }
  assert (Hy_pb : arr_len (DS.ds_pending_buf y) = DS.ds_lit_bufsize s * 4) by (subst y; rewrite flush_pending_pb_len; exact Hx_pb).
  destruct (FBT.BQ_fresh y) as ((BQ1 & BQ2 & BQ3 & BQ4) & BN).
  { rewrite G5. exact Fsn. }
  { intros c Hc. rewrite G8. exact (Flt c Hc). }
  { intros d Hd. rewrite G10. exact (Fdt d Hd). }
  { intros b Hb. rewrite G12. exact (Fbt b Hb). }
  split; [|rewrite BN, G3, E3; lia].
  constructor.
  - rewrite G1, E1. exact Elev.
  - rewrite G2, E2. exact Estr.
  - rewrite Hy_dt. exact Hdt.
  - rewrite G3, E3. exact Elbs.
  - rewrite G3, E3. exact Elbs2.
  - rewrite Hy_pb, G3, E3. reflexivity.
  - rewrite G4, G3, E4, E3. exact Esymend.
  - exact D1.
  - exact D2.
  - exact D3.
  - subst y. apply flush_pending_bib. subst x. autorewrite with s5f_block_start. exact Fbib.
  - subst y. apply flush_pending_pbb. subst x. autorewrite with s5f_block_start. exact Fpbb.
  - rewrite HT. lia.
  - rewrite HA. lia.
  - rewrite HA, HT, Hy_pb. lia.
  - exact BQ1.
  - rewrite G3, E3. lia.
  - exact BQ3.
  - exact BQ4.
  - rewrite G6. exact Fopt.
  - rewrite G7. exact Fstat.
  - unfold TM.tree_lens in *. rewrite G8, G9, G10, G11, G12, G13, G14, G15, G16. exact Ftl.
  - intros [| |] i; cbn [DS.tree_fc]; [rewrite G8 | rewrite G10 | rewrite G12]; [apply (Ffc DS.TL) | apply (Ffc DS.TD) | apply (Ffc DS.TB)].
  - intros [| |] i; cbn [DS.tree_dl]; [rewrite G9 | rewrite G11 | rewrite G13]; [apply (Fdl DS.TL) | apply (Fdl DS.TD) | apply (Fdl DS.TB)].
  - rewrite G16. exact Fdep.
  - rewrite G14. exact Fblc.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  The two pairs                                                         *)
(* ------------------------------------------------------------------------- *)

Theorem br_flush_block_only : forall s t pre_out pre_in last,
  dst_rel s t pre_out pre_in -> em_core s -> fb_lz t -> 0 <= last <= 1 ->
  dst_rel (DL.flush_block_only s last) (RD.flush_block_only last t) pre_out pre_in
  /\ (DS.cs_avail_out (DS.ds_strm (DL.flush_block_only s last)) <> 0 -> em_inv (DL.flush_block_only s last)).
Proof.
  intros s t pre_out pre_in last Hrel Hem Hlz Hlast.
  pose proof (fb_entry_of s t pre_out pre_in last Hrel Hem Hlz Hlast) as FE.
  destruct (RefDeflSafeE5.FB_CALL_intro OverlayCoreL.overlay_core_proof s last FE) as [_ FP].
  pose proof (br_tr_flush_block s t pre_out pre_in last Hrel Hem Hlz Hlast) as R8.
  rewrite s5_fbo_eq, rt_fbo_eq.
  set (s8 := DT.tr_flush_block s (DO.fb_buf s) (DO.fb_len s) last) in *.
  set (t8 := rt_fb_state t last) in *.
  assert (Hss : DS.ds_strstart s8 = RD.ls_strstart (RD.d_ls t)).
  { destruct R8 as (_ & L8 & _). unfold lz_rel in L8. cbv zeta in L8.
    destruct L8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lss & _). exact Lss. }
  rewrite Hss.
  pose proof (dst_block_start s8 t8 pre_out pre_in (RD.ls_strstart (RD.d_ls t)) R8) as R9.
  change (RD.d_ls t8) with (RD.d_ls t) in R9.
  set (t9 := RD.setD_ls (RD.setL_blockstart (RD.ls_strstart (RD.d_ls t)) (RD.d_ls t)) t8) in *.
  set (s9 := DS.set_block_start s8 (RD.ls_strstart (RD.d_ls t))) in *.
  pose proof FP as FP'.
  destruct FP' as [_ _ Fstrm Fsn _ _ _ _ _ _ _ _ _ _ _ Fpend Fpout Fbiv _ _ Fpbl _].
  destruct Fstrm as (dt & Hst & _).
  pose proof Hem as Hem'. em_names Hem'.
  assert (Hsn9 : DS.ds_sym_next s9 = 0) by (subst s9; autorewrite with s5f_block_start; exact Fsn).
  assert (Hfr9 : flush_room s9).
  { right. subst s9. unfold room. autorewrite with s5f_block_start. split; [exact Fpout|]. lia. }
  assert (Hok9 : fp_ok s9).
  { unfold fp_ok. subst s9. autorewrite with s5f_block_start. rewrite Hst, Fpbl. cbn [DS.cs_avail_out DS.cs_total_out DS.cset_data_type].
    lia. }
  pose proof (dst_flush_pending s9 t9 pre_out pre_in R9 Hsn9 Hfr9 Hok9) as R10.
  split; [exact R10|].
  intros Hav.
  pose proof Hrel as (Hg & _ & _ & _ & _ & Hm).
  pose proof R8 as (Hg8 & _).
  unfold geom_rel in Hg, Hg8. cbv zeta in Hg, Hg8.
  destruct Hg as (Glev & Gstr & _ & _ & _ & _ & _ & _ & _ & Glbs & _ & Gse & _).
  destruct Hg8 as (Glev8 & Gstr8 & _ & _ & _ & _ & _ & _ & _ & Glbs8 & _ & Gse8 & _).
  unfold strm_rel in Hm. cbv zeta in Hm. destruct Hm as (_ & _ & _ & _ & _ & _ & _ & Mav & _ & Mtot & _).
  pose proof R10 as (_ & _ & _ & _ & _ & M10). unfold strm_rel in M10. cbv zeta in M10.
  destruct M10 as (_ & _ & _ & _ & _ & _ & _ & Mav10 & _ & Mtot10 & _).
  apply (em_after_flush s s8 t9 (RD.ls_strstart (RD.d_ls t)) Hem).
  - destruct (Z.eq_dec last 0) as [->|N]; [left; exact FP | right; replace last with 1 in FP by lia; exact FP].
  - change (RC.dg_level (RD.d_cfg t8)) with (RC.dg_level (RD.d_cfg t)) in Glev8. congruence.
  - change (RC.dg_strategy (RD.d_cfg t8)) with (RC.dg_strategy (RD.d_cfg t)) in Gstr8. congruence.
  - change (RC.dg_lit_bufsize (RD.d_cfg t8)) with (RC.dg_lit_bufsize (RD.d_cfg t)) in Glbs8. congruence.
  - change (RC.dg_sym_end (RD.d_cfg t8)) with (RC.dg_sym_end (RD.d_cfg t)) in Gse8. congruence.
  - symmetry. exact Mav10.
  - symmetry. exact Mtot10.
  - exact Mav.
  - exact Mtot.
  - exact Hav.
Qed.

Theorem br_flush_block : forall s t pre_out pre_in last,
  dst_rel s t pre_out pre_in -> em_core s -> fb_lz t -> 0 <= last <= 1 ->
  dst_rel (fst (DB.flush_block s last)) (snd (RD.flush_block last t)) pre_out pre_in
  /\ option_map bs_of (snd (DB.flush_block s last)) = fst (RD.flush_block last t)
  /\ (DS.cs_avail_out (DS.ds_strm (fst (DB.flush_block s last))) <> 0 -> em_inv (fst (DB.flush_block s last))).
Proof.
  intros s t pre_out pre_in last Hrel Hem Hlz Hlast.
  destruct (br_flush_block_only s t pre_out pre_in last Hrel Hem Hlz Hlast) as [R E].
  unfold DB.flush_block, RD.flush_block. cbv zeta.
  pose proof R as (_ & _ & _ & _ & _ & M). unfold strm_rel in M. cbv zeta in M.
  destruct M as (_ & _ & _ & _ & _ & _ & _ & Mav & _).
  rewrite Mav.
  destruct (Z.eqb_spec (DS.cs_avail_out (DS.ds_strm (DL.flush_block_only s last))) 0) as [Z0|Z0];
    cbn [fst snd option_map].
  - split; [exact R|]. split; [|intros H; exfalso; exact (H Z0)].
    destruct (Z.eqb_spec last 0) as [->|N]; cbn [negb Z.eqb]; [reflexivity|].
    replace (last =? 0) with false by (symmetry; apply Z.eqb_neq; exact N). reflexivity.
  - split; [exact R|]. split; [reflexivity | exact E].
Qed.

Print Assumptions br_flush_block_only.
Print Assumptions br_flush_block.
