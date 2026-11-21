(** * Bridge.DEmit.BrFbFin — pair D22 assembled: [_tr_flush_block], S5 vs RT.

    S5's flush is [tfb_fin last (tfb_emit d X6 mb buf len last)]
    ([FlushBlockModel.tr_flush_block_eq], [RefDeflSafeE5.tfb_pre_ov]); RT's
    is [rt_fin last (set_bw (rt_emit_bw d ...) s2)] ([BrFbKit.rt_fb_split]).
    The branch [d] is the same on both sides ([branch_agree]), the trees at
    the branch point are related ([BrFbPre]), and so are the block's bits
    ([BrFbEmit]).  [fin_rel] then closes the relation over the final
    [init_block] / [bi_windup] with the emitted state abstract; the frames
    for the clusters D22 does not write come from S5's [fb_post]
    ([fp_keep], [fp_pbl]) and [tr_flush_block_strm]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel SendModel FlushBlockModel DeflateOverlay
  RefDeflSafeFB RefDeflSafeE1 RefDeflSafeE3 RefDeflSafeE5 RefFlushBlk13 RefDeflFast6 OverlayCoreL.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrSendAll BrStored
  BrFbKit BrFbPre BrFbEmit BrTrFlushDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DTreeIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module E3 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeE3.
Module FB13 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.

Lemma rt_fb_split' : forall buf sl last level strategy dtype ts, 0 < level ->
  RT.tr_flush_block buf sl last level strategy dtype ts =
  (if Z.eqb dtype RT.Z_UNKNOWN then RT.detect_data_type (RT.ts_trees ts RT.TK_L) else dtype,
   rt_fin last (RT.set_bw (rt_emit_bw (rt_branch buf sl strategy (snd (rt_tp ts))) buf sl last
                             (fst (rt_tp ts)) (snd (rt_tp ts)))
                          (snd (rt_tp ts)))).
Proof. intros. rewrite rt_fb_split by assumption. reflexivity. Qed.

Lemma trel_set_bw : forall s ts b, trel s ts -> trel s (RT.set_bw b ts).
Proof. intros s ts b H. exact H. Qed.

Lemma d_ts_setD_ts : forall x t, RD.d_ts (RD.setD_ts x t) = x.
Proof. reflexivity. Qed.
Lemma ts_bw_set_bw : forall b ts, RT.ts_bw (RT.set_bw b ts) = b.
Proof. reflexivity. Qed.
Lemma ts_symnext_set_bw : forall b ts, RT.ts_symnext (RT.set_bw b ts) = RT.ts_symnext ts.
Proof. reflexivity. Qed.

Lemma gl_fields : forall a b, gl_view a = gl_view b ->
  DS.ds_lit_bufsize a = DS.ds_lit_bufsize b /\ DS.ds_sym_end a = DS.ds_sym_end b.
Proof. intros a b E. unfold gl_view in E. injection E. intros. split; assumption. Qed.

(** The final [init_block] (and, for the last block, [bi_windup]) with the
    emitted state [P] and RT's emitted bit writer [B] abstract. *)
Lemma fin_rel : forall s t pre_out pre_in last (P : DS.deflate_state) (B : ZBitsOut.BW) (s2 : RT.TSt) dt,
  dst_rel s t pre_out pre_in -> 0 <= last <= 1 ->
  bw_rel P B -> DS.ds_pending_out P = 0 -> trel P s2 -> TM.tree_lens P ->
  (last <> 0 -> DS.ds_pending (DT.bi_windup (DT.init_block P)) <= arr_len (DS.ds_pending_buf P)) ->
  gl_view (FBM.tfb_fin last P) = gl_view s ->
  arr_len (DS.ds_pending_buf (FBM.tfb_fin last P)) = arr_len (DS.ds_pending_buf s) ->
  DS.ds_strm (FBM.tfb_fin last P) = DS.cset_data_type (DS.ds_strm s) dt ->
  dst_rel (FBM.tfb_fin last P)
    (RD.setD_ts (rt_fin last (RT.set_bw B s2)) (RD.setD_strm (RD.setZ_datatype dt (RD.d_strm t)) t)) pre_out pre_in.
Proof.
  intros s t pre_out pre_in last P B s2 dt Hrel Hlast HB HPO HT HL HW GL PL ST.
  pose proof Hrel as (Hg & Hl & _ & Hs & _ & Hm).
  destruct (DTreeIface.br_init_block P (RT.set_bw B s2) (trel_set_bw _ _ _ HT) HL) as (TI & _ & SNI & _ & BWI).
  destruct (bw_rel_init_block P B HB) as (BI & POI & LI & _).
  pose proof (E5.ib_sn _ _ (E5.init_block_facts P)) as SNP.
  pose proof Hs as (_ & (Hse0 & Hse1) & _ & Hroom & _).
  unfold strm_rel in Hm. cbv zeta in Hm.
  destruct Hm as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & _).
  unfold FBM.tfb_fin, rt_fin in *. cbv zeta in *.
  assert (HL01 : last = 0 \/ last = 1) by lia.
  destruct HL01 as [ -> | -> ]; cbn [negb Z.eqb Pos.eqb] in GL, PL, ST |- *.
  - (* not the last block: [init_block] *)
    destruct (gl_rel s (DT.init_block P) t
                (RD.setD_ts (RT.init_block (RT.set_bw B s2)) (RD.setD_strm (RD.setZ_datatype dt (RD.d_strm t)) t))
                GL PL eq_refl eq_refl eq_refl eq_refl eq_refl Hg Hl) as [G' L'].
    destruct (gl_fields _ _ GL) as [GLb GLe].
    unfold dst_rel. refine (conj G' (conj L' (conj _ (conj _ (conj _ _))))).
    + rewrite d_ts_setD_ts, BWI, ts_bw_set_bw. exact BI.
    + unfold sym_rel. cbv zeta. rewrite d_ts_setD_ts, SNP, SNI, GLb, GLe, PL.
      refine (conj eq_refl (conj _ (conj _ (conj _ _)))).
      * lia.
      * intros i Hi. lia.
      * exact Hroom.
      * intros Hi. lia.
    + apply tree_rel_trel. rewrite d_ts_setD_ts. exact TI.
    + unfold strm_rel. cbv zeta. rewrite ST.
      cbn [RD.d_strm RD.setD_ts RD.setD_strm RD.setZ_datatype RD.zs_in RD.zs_done RD.zs_out RD.zs_availout
           RD.zs_totalin RD.zs_totalout RD.zs_adler RD.zs_datatype].
      autorewrite with s5c_data_type.
      repeat (split; [assumption|]). reflexivity.
  - (* the last block: [init_block], then [bi_windup] *)
    destruct (gl_rel s (DT.bi_windup (DT.init_block P)) t
                (RD.setD_ts (RT.set_bw (ZBitsOut.bw_windup (RT.ts_bw (RT.init_block (RT.set_bw B s2))))
                                       (RT.init_block (RT.set_bw B s2)))
                            (RD.setD_strm (RD.setZ_datatype dt (RD.d_strm t)) t))
                GL PL eq_refl eq_refl eq_refl eq_refl eq_refl Hg Hl) as [G' L'].
    destruct (gl_fields _ _ GL) as [GLb GLe].
    unfold dst_rel. refine (conj G' (conj L' (conj _ (conj _ (conj _ _))))).
    + rewrite d_ts_setD_ts, ts_bw_set_bw, BWI, ts_bw_set_bw.
      apply br_bi_windup_fin; [exact BI | rewrite POI; exact HPO | rewrite LI; apply HW; lia].
    + unfold sym_rel. cbv zeta. rewrite d_ts_setD_ts, ts_symnext_set_bw.
      rewrite (FBM.k_bi_windup _ _ _ FBM.keeps_sym_next eq_refl), SNP, SNI, GLb, GLe, PL.
      refine (conj eq_refl (conj _ (conj _ (conj _ _)))).
      * lia.
      * intros i Hi. lia.
      * exact Hroom.
      * intros Hi. lia.
    + apply tree_rel_trel. rewrite d_ts_setD_ts. apply trel_set_bw.
      apply (trel_nbw (DT.init_block P)); [exact (proj2 (proj2 (bi_windup_frame _))) | exact TI].
    + unfold strm_rel. cbv zeta. rewrite ST.
      cbn [RD.d_strm RD.setD_ts RD.setD_strm RD.setZ_datatype RD.zs_in RD.zs_done RD.zs_out RD.zs_availout
           RD.zs_totalin RD.zs_totalout RD.zs_adler RD.zs_datatype].
      autorewrite with s5c_data_type.
      repeat (split; [assumption|]). reflexivity.
Qed.

Theorem br_tr_flush_block' : forall s t pre_out pre_in last,
  dst_rel s t pre_out pre_in -> em_core s -> fb_lz t -> 0 <= last <= 1 ->
  dst_rel (DT.tr_flush_block s (DO.fb_buf s) (DO.fb_len s) last) (rt_fb_state t last) pre_out pre_in.
Proof.
  intros s t pre_out pre_in last Hrel Hem Hlz Hlast.
  pose proof (fb_entry_of s t pre_out pre_in last Hrel Hem Hlz Hlast) as FE.
  destruct (E5.FB_CALL_intro OverlayCoreL.overlay_core_proof s last FE) as [FO FP].
  pose proof (E3.tree_phase s (E5.OP s last FE)) as TP.
  destruct (br_fb_trees s t pre_out pre_in last Hrel Hem Hlz Hlast) as (T6 & Emb & L6 & _ & _ & _).
  pose proof (E5.emit_facts s last FE OverlayCoreL.overlay_core_proof) as EF. cbv zeta in EF.
  destruct EF as [EM _].
  pose proof (E5.em_pbl _ _ EM) as PLpre.
  pose proof (FBM.tr_flush_block_strm s (DO.fb_buf s) (DO.fb_len s) last) as Estrm.
  pose proof (ec_level _ Hem) as Hlev.
  pose proof Hrel as (Hg & Hl & _ & _ & Ht & Hm).
  unfold geom_rel in Hg. cbv zeta in Hg. destruct Hg as (Glev & Gstr & _).
  unfold lz_rel in Hl. cbv zeta in Hl.
  destruct Hl as (_ & _ & _ & _ & _ & _ & _ & _ & Lbs & _ & _ & _ & Lss & _).
  pose proof Hlz as (_ & _ & _ & _ & W5 & _ & _).
  pose proof (E5.X6n s last FE) as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _).
  (* S5's room for the last [bi_windup], from [flush_ok] *)
  assert (POK : last <> 0 ->
    DS.ds_pending (DT.bi_windup (DT.init_block (FBM.tfb_pre s (DO.fb_buf s) (DO.fb_len s) last)))
    <= arr_len (DS.ds_pending_buf s)).
  { unfold RefDeflFast6.flush_ok in FO. cbv zeta in FO. destruct FO as [SAFE _].
    unfold FB13.fb_safe in SAFE. cbv zeta in SAFE. destruct SAFE as (_ & _ & _ & _ & (_ & PO) & _). exact PO. }
  (* S5's flush as [tfb_fin] of the branch's bits *)
  rewrite FBM.tr_flush_block_eq in FP, Estrm |- *.
  rewrite (E5.tfb_pre_ov s (DO.fb_buf s) (DO.fb_len s) last ltac:(lia)) in FP, Estrm, POK |- *.
  pose proof (RefDeflSafeFB.fp_keep _ _ _ FP _ gl_view keeps_gl) as GL. rewrite gl_X0 in GL.
  pose proof (RefDeflSafeFB.fp_pbl _ _ _ FP) as PL. rewrite <- (ec_pbl _ Hem) in PL.
  (* the length and the branch *)
  assert (Elen : DO.fb_len s = RD.ls_strstart (RD.d_ls t) - RD.ls_blockstart (RD.d_ls t)).
  { unfold DO.fb_len. rewrite Lss, Lbs. apply wrap64_id. lia. }
  assert (EB : FBM.tfb_branch (DO.ov_X6 s) (DO.fb_buf s) (DO.fb_len s)
               = rt_branch (if Z.leb 0 (RD.ls_blockstart (RD.d_ls t))
                            then Some (RD.win_take (RD.ls_window (RD.d_ls t)) (RD.ls_blockstart (RD.d_ls t))
                                         (RD.ls_strstart (RD.d_ls t) - RD.ls_blockstart (RD.d_ls t)))
                            else None)
                   (RD.ls_strstart (RD.d_ls t) - RD.ls_blockstart (RD.d_ls t))
                   (RC.dg_strategy (RD.d_cfg t)) (snd (rt_tp (RD.d_ts t)))).
  { rewrite <- Gstr, <- P9, <- Elen.
    apply branch_agree; [exact T6 | exact (E3.tp_opt _ TP) | exact (E3.tp_stat_range _ TP) | rewrite Elen; lia |].
    unfold DO.fb_buf. rewrite Lbs. destruct (0 <=? RD.ls_blockstart (RD.d_ls t)); reflexivity. }
  (* the block's bits *)
  assert (EMR :
    bw_rel (FBM.tfb_emit (FBM.tfb_branch (DO.ov_X6 s) (DO.fb_buf s) (DO.fb_len s)) (DO.ov_X6 s) (DO.ov_mb s)
              (DO.fb_buf s) (DO.fb_len s) last)
           (rt_emit_bw (FBM.tfb_branch (DO.ov_X6 s) (DO.fb_buf s) (DO.fb_len s))
              (if Z.leb 0 (RD.ls_blockstart (RD.d_ls t))
               then Some (RD.win_take (RD.ls_window (RD.d_ls t)) (RD.ls_blockstart (RD.d_ls t))
                            (RD.ls_strstart (RD.d_ls t) - RD.ls_blockstart (RD.d_ls t)))
               else None)
              (RD.ls_strstart (RD.d_ls t) - RD.ls_blockstart (RD.d_ls t)) last
              (fst (rt_tp (RD.d_ts t))) (snd (rt_tp (RD.d_ts t))))
    /\ DS.ds_pending_out (FBM.tfb_emit (FBM.tfb_branch (DO.ov_X6 s) (DO.fb_buf s) (DO.fb_len s)) (DO.ov_X6 s)
                            (DO.ov_mb s) (DO.fb_buf s) (DO.fb_len s) last) = 0
    /\ nbw (FBM.tfb_emit (FBM.tfb_branch (DO.ov_X6 s) (DO.fb_buf s) (DO.fb_len s)) (DO.ov_X6 s) (DO.ov_mb s)
              (DO.fb_buf s) (DO.fb_len s) last) = nbw (DO.ov_X6 s)).
  { destruct (E5.branch_cases (DO.ov_X6 s) (DO.fb_buf s) (DO.fb_len s)) as [Hd|[Hd|Hd]]; rewrite Hd.
    - exact (br_emit_stat s t pre_out pre_in last Hrel Hem Hlz Hlast _ _ _ Hd).
    - rewrite <- Emb. exact (br_emit_dyn s t pre_out pre_in last Hrel Hem Hlz Hlast _ _ Hd).
    - exact (br_emit_sto s t pre_out pre_in last Hrel Hem Hlz Hlast _ Hd). }
  destruct EMR as (EB1 & EB2 & EB3).
  (* the data type *)
  assert (ST : DS.ds_strm (FBM.tfb_fin last (FBM.tfb_emit (FBM.tfb_branch (DO.ov_X6 s) (DO.fb_buf s) (DO.fb_len s))
                 (DO.ov_X6 s) (DO.ov_mb s) (DO.fb_buf s) (DO.fb_len s) last))
               = DS.cset_data_type (DS.ds_strm s)
                   (if RD.zs_datatype (RD.d_strm t) =? RT.Z_UNKNOWN
                    then RT.detect_data_type (RT.ts_trees (RD.d_ts t) RT.TK_L) else RD.zs_datatype (RD.d_strm t))).
  { rewrite Estrm. replace (0 <? DS.ds_level s) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    unfold strm_rel in Hm. cbv zeta in Hm. destruct Hm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Mdt).
    rewrite Mdt, <- (DTreeIface.br_detect_data_type s (RD.d_ts t) Ht).
    assert (EU : RT.Z_UNKNOWN = Z_UNKNOWN) by reflexivity. rewrite EU.
    destruct (DS.cs_data_type (DS.ds_strm s) =? Z_UNKNOWN); [reflexivity | destruct (DS.ds_strm s); reflexivity]. }
  (* RT's flush, split the same way *)
  unfold rt_fb_state, rt_fb. cbv zeta.
  rewrite rt_fb_split' by (rewrite <- Glev; lia).
  rewrite <- EB, snd_pair', fst_pair'.
  apply (fin_rel s).
  - exact Hrel.
  - exact Hlast.
  - exact EB1.
  - exact EB2.
  - apply (trel_nbw (DO.ov_X6 s)); [exact EB3 | exact T6].
  - apply (tree_lens_nbw (DO.ov_X6 s)); [exact EB3 | exact L6].
  - intros HL0. rewrite PLpre, <- (ec_pbl _ Hem). exact (POK HL0).
  - exact GL.
  - exact PL.
  - exact ST.
Qed.

Print Assumptions br_tr_flush_block'.
