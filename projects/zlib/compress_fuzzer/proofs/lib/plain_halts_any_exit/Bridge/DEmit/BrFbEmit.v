(** * Bridge.DEmit.BrFbEmit — pair D22, the block's bits: S5's [tfb_emit] against
    RT's [rt_emit_bw], one lemma per branch.

    - static: [OvKit.ov_emit_stat] turns S5's [compress_block] (reading its
      symbols from the overlaid [pending_buf]) into [sbs_run] over the
      pristine calls, and [BrCompress.br_cb_body] relates those to RT's
      [compress_block];
    - dynamic: the same with [OvKit.ov_emit_dyn], after the tree header,
      which is [send_all_trees] ([BrFbKit.hX13_sat], [BrSendAll]);
    - stored: [BrStored.br_tr_stored_block].
    Every room condition is S5's own, from [RefDeflSafeE5.emit_facts]: the
    block's final bit position ([EMIT]'s [em_W]), [dyn_ok], [sto_ok]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel SendModel FlushBlockModel DeflateOverlay
  RefDeflSafeFB RefDeflSafeE1 RefDeflSafeE3 RefDeflSafeE5 RefFlushBlk12 RefFlushBlk13 RefSendTree4 OverlayCoreL
  TreesTab.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require OvKit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrSbs BrSendAll BrStored
  BrCompress BrFbKit BrFbPre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module E3 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeE3.
Module FB13 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.

Section Emit.
Variables (s : DS.deflate_state) (t : RD.DSt) (pre_out pre_in : list Z) (last : Z).
Hypothesis Hrel : dst_rel s t pre_out pre_in.
Hypothesis Hem : em_core s.
Hypothesis Hlz : fb_lz t.
Hypothesis Hlast : 0 <= last <= 1.

Local Notation X6 := (DO.ov_X6 s).
Local Notation mb := (DO.ov_mb s).
Local Notation s2 := (snd (rt_tp (RD.d_ts t))).
Local Notation N := (DO.nsym s).

Lemma fe_sec : FB.fb_entry s last.
Proof. exact (fb_entry_of s t pre_out pre_in last Hrel Hem Hlz Hlast). Qed.

(** Facts the three branches share. *)
Lemma em_facts :
  trel X6 s2 /\ TM.tree_lens X6 /\ bw_rel X6 (RT.ts_bw s2)
  /\ (forall i, 0 <= i < 3 * N -> DS.sym_buf_get s i = RT.ts_symbuf s2 i)
  /\ RT.ts_symnext s2 = 3 * N
  /\ DS.ds_pending_out X6 = 0 /\ DS.ds_pending X6 = 0
  /\ arr_len (DS.ds_pending_buf X6) = DS.ds_lit_bufsize s * 4
  /\ 0 <= DS.ds_bi_valid X6 <= 7.
Proof.
  destruct (br_fb_trees s t pre_out pre_in last Hrel Hem Hlz Hlast) as (T6 & _ & L6 & B6 & SB & SN).
  pose proof (E5.X6n s last fe_sec) as (P1 & P2 & P3 & P4 & _ & _ & P7 & _).
  pose proof Hrel as (_ & _ & _ & (Y1 & _ & Y3 & _) & _ & _).
  split; [exact T6|]. split; [exact L6|]. split; [exact B6|].
  split; [intros i Hi; rewrite SB; apply Y3; rewrite (ec_sn _ Hem); exact Hi|].
  split; [rewrite SN, <- Y1; exact (ec_sn _ Hem)|].
  split; [exact P7|]. split; [exact P2|]. split; [rewrite P1; exact (ec_pbl _ Hem)|].
  rewrite P4. exact (ec_biv _ Hem).
Qed.

(* ------------------------------------------------------------------------- *)
(* 1.  Static trees                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma br_emit_stat : forall rbuf sl mbi,
  FBM.tfb_branch X6 (DO.fb_buf s) (DO.fb_len s) = 0 ->
  bw_rel (FBM.tfb_emit 0 X6 mb (DO.fb_buf s) (DO.fb_len s) last) (rt_emit_bw 0 rbuf sl last mbi s2)
  /\ DS.ds_pending_out (FBM.tfb_emit 0 X6 mb (DO.fb_buf s) (DO.fb_len s) last) = 0
  /\ nbw (FBM.tfb_emit 0 X6 mb (DO.fb_buf s) (DO.fb_len s) last) = nbw X6.
Proof.
  intros rbuf sl mbi Hd.
  pose proof fe_sec as FE.
  destruct em_facts as (T6 & L6 & B6 & HS & SN & O6 & P6 & PL6 & V6).
  pose proof (E5.emit_facts s last FE OverlayCoreL.overlay_core_proof) as EF. cbv zeta in EF.
  rewrite Hd in EF. destruct EF as [EM _].
  pose proof (E5.em_W _ _ EM) as HW.
  pose proof (OvKit.ov_emit_stat s last FE) as OV. cbv zeta in OV.
  rewrite tfb_emit_0 in HW |- *. rewrite OV in HW |- *.
  rewrite rt_emit_bw_0, SN.
  pose proof (ec_lbs _ Hem) as Hlbs. pose proof (ec_nsym _ Hem) as RN.
  assert (BY : bw_rel (DT.send_bits X6 (Z.shiftl DS.STATIC_TREES 1 + last) 3)
                      (ZBitsOut.bw_send_bits (Z.shiftl DS.STATIC_TREES 1 + last) 3 (RT.ts_bw s2))).
  { apply br_send_bits; [exact B6 | split; [exact O6 | rewrite P6, PL6; lia]]. }
  assert (OY : DS.ds_pending_out (DT.send_bits X6 (Z.shiftl DS.STATIC_TREES 1 + last) 3) = 0)
    by (rewrite (FBM.k_send_bits _ _ _ keeps_po eq_refl); exact O6).
  assert (VY : 0 <= DS.ds_bi_valid (DT.send_bits X6 (Z.shiftl DS.STATIC_TREES 1 + last) 3) <= 16)
    by (apply E1.send_bits_biv; lia).
  assert (LY : arr_len (DS.ds_pending_buf (DT.send_bits X6 (Z.shiftl DS.STATIC_TREES 1 + last) 3))
               = DS.ds_lit_bufsize s * 4) by (rewrite SM.sb_pbl; exact PL6).
  assert (OK : SM.sbs_ok (arr_len (DS.ds_pending_buf (DT.send_bits X6 (Z.shiftl DS.STATIC_TREES 1 + last) 3)))
                 (DT.send_bits X6 (Z.shiftl DS.STATIC_TREES 1 + last) 3)
                 (OvKit.cb_all s DS.static_ltree_fc DS.static_ltree_dl DS.static_dtree_fc DS.static_dtree_dl N)).
  { apply cb_all_ok; [lia | exact VY | | | |].
    - intros j _. pose proof (TreesTab.static_ltree_dl_bound (DO.sym_lcode s j)). lia.
    - intros j _ _. pose proof (TreesTab.static_dtree_dl_bound (DO.sym_dcode s j)). lia.
    - pose proof (TreesTab.static_ltree_dl_bound DS.END_BLOCK). lia.
    - rewrite LY. lia. }
  destruct (br_cb_body _ _ s _ _ _ _ RT.static_ltree RT.static_dtree (RT.ts_symbuf s2) N BY OY ltac:(lia) HS
              (ec_syms _ Hem) (proj1 static_ltree_rel) (proj2 static_ltree_rel)
              (proj1 static_dtree_rel) (proj2 static_dtree_rel) OK) as (R1 & R2 & _).
  split; [exact R1|]. split; [exact R2|].
  rewrite nbw_sbs. apply nbw_send_bits.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  Dynamic trees                                                         *)
(* ------------------------------------------------------------------------- *)

Lemma br_emit_dyn : forall rbuf sl,
  FBM.tfb_branch X6 (DO.fb_buf s) (DO.fb_len s) = 1 ->
  bw_rel (FBM.tfb_emit 1 X6 mb (DO.fb_buf s) (DO.fb_len s) last) (rt_emit_bw 1 rbuf sl last mb s2)
  /\ DS.ds_pending_out (FBM.tfb_emit 1 X6 mb (DO.fb_buf s) (DO.fb_len s) last) = 0
  /\ nbw (FBM.tfb_emit 1 X6 mb (DO.fb_buf s) (DO.fb_len s) last) = nbw X6.
Proof.
  intros rbuf sl Hd.
  pose proof fe_sec as FE.
  pose proof (E3.tree_phase s (E5.OP s last FE)) as TP.
  destruct em_facts as (T6 & L6 & B6 & HS & SN & O6 & P6 & PL6 & V6).
  pose proof (E3.tp_mb _ TP) as Hmb. pose proof (E3.tp_lmax _ TP) as Hlm. pose proof (E3.tp_dmax _ TP) as Hdm.
  pose proof (E3.tp_LD _ TP) as HLD. pose proof (E3.tp_DD _ TP) as HDD. pose proof (E3.tp_BD _ TP) as HBD.
  unfold DS.L_CODES in Hlm. unfold DS.D_CODES in Hdm.
  pose proof (ec_lbs _ Hem) as Hlbs. pose proof (ec_nsym _ Hem) as RN.
  pose proof (E5.emit_facts s last FE OverlayCoreL.overlay_core_proof) as EF. cbv zeta in EF.
  rewrite Hd in EF. destruct EF as [EM DK].
  pose proof (E5.em_W _ _ EM) as HW.
  unfold FB12.dyn_ok in DK. cbv zeta in DK.
  destruct DK as (_ & HD & _ & _ & _ & _ & _ & _ & _ & _ & ST1 & ST2 & _).
  rewrite hd_sat in HD, ST1, ST2. rewrite sbs_run_cons in ST1, ST2. apply sbs_ok_cons_inv in HD.
  (* S5's block: the header state hX13, then the pristine body *)
  rewrite (E5.emit1_eq X6 last mb ltac:(lia)) in HW |- *.
  assert (NB13 : nbw (E5.hX13 X6 last mb) = nbw X6).
  { unfold E5.hX13, E5.hX12, E5.hX11. rewrite !nbw_send_tree, nbw_sbs. reflexivity. }
  destruct (nbw_dyn _ _ NB13) as (D1 & D2 & D3 & D4 & _ & _).
  rewrite D1, D2, D3, D4 in HW |- *.
  pose proof (OvKit.ov_emit_dyn s last FE Hd) as OV. cbv zeta in OV.
  rewrite OV in HW |- *.
  (* RT's block *)
  pose proof T6 as (A1 & A2 & A3 & A4 & _ & _ & _ & _ & _ & EL & ED & _).
  rewrite rt_emit_bw_1, SN, <- EL, <- ED.
  (* the header *)
  assert (Hsl : scan_ok X6 DS.TL (DS.ds_l_max_code X6 + 1 - 1)).
  { replace (DS.ds_l_max_code X6 + 1 - 1) with (DS.ds_l_max_code X6) by lia.
    split; [discriminate|]. cbn [TM.tsize]. split; [lia|]. split; [lia|]. exact HLD. }
  assert (Hsd : scan_ok X6 DS.TD (DS.ds_d_max_code X6 + 1 - 1)).
  { replace (DS.ds_d_max_code X6 + 1 - 1) with (DS.ds_d_max_code X6) by lia.
    split; [discriminate|]. cbn [TM.tsize]. split; [lia|]. split; [lia|]. exact HDD. }
  assert (Hbl : bl_lens_ok X6) by (intros i Hi; pose proof (HBD i Hi); lia).
  assert (B13 : bw_rel (E5.hX13 X6 last mb)
                  (RT.send_all_trees (DS.ds_l_max_code X6 + 1) (DS.ds_d_max_code X6 + 1) (mb + 1)
                     (RT.set_bw (ZBitsOut.bw_send_bits (4 + last) 3 (RT.ts_bw s2)) s2))
               /\ DS.ds_pending_out (E5.hX13 X6 last mb) = 0).
  { rewrite (hX13_sat X6 last mb) by lia.
    assert (BY : bw_rel (DT.send_bits X6 (4 + last) 3) (ZBitsOut.bw_send_bits (4 + last) 3 (RT.ts_bw s2)))
      by (apply br_send_bits; [exact B6 | split; [exact O6 | rewrite P6, PL6; lia]]).
    assert (NY : nbw (DT.send_bits X6 (4 + last) 3) = nbw X6) by apply nbw_send_bits.
    destruct (nbw_dyn _ _ NY) as (_ & _ & _ & _ & YL & YD).
    assert (LY : arr_len (DS.ds_pending_buf (DT.send_bits X6 (4 + last) 3)) = DS.ds_lit_bufsize s * 4)
      by (rewrite SM.sb_pbl; exact PL6).
    assert (OY : DS.ds_pending_out (DT.send_bits X6 (4 + last) 3) = 0)
      by (rewrite (FBM.k_send_bits _ _ _ keeps_po eq_refl); exact O6).
    assert (S1 : RefSendTree4.send_tree_safe (arr_len (DS.ds_pending_buf (DT.send_bits X6 (4 + last) 3)))
                   (SM.sbs_run (DT.send_bits X6 (4 + last) 3)
                      (FBM.sat_calls (DT.send_bits X6 (4 + last) 3) (DS.ds_l_max_code X6 + 1)
                         (DS.ds_d_max_code X6 + 1) (mb + 1))) DS.TL (DS.ds_l_max_code X6 + 1 - 1)).
    { rewrite LY. replace (DS.ds_l_max_code X6 + 1 - 1) with (DS.ds_l_max_code X6) by lia. exact ST1. }
    assert (S2 : RefSendTree4.send_tree_safe (arr_len (DS.ds_pending_buf (DT.send_bits X6 (4 + last) 3)))
                   (DT.send_tree (SM.sbs_run (DT.send_bits X6 (4 + last) 3)
                      (FBM.sat_calls (DT.send_bits X6 (4 + last) 3) (DS.ds_l_max_code X6 + 1)
                         (DS.ds_d_max_code X6 + 1) (mb + 1))) DS.TL (DS.ds_l_max_code X6 + 1 - 1))
                   DS.TD (DS.ds_d_max_code X6 + 1 - 1)).
    { rewrite LY. replace (DS.ds_l_max_code X6 + 1 - 1) with (DS.ds_l_max_code X6) by lia.
      replace (DS.ds_d_max_code X6 + 1 - 1) with (DS.ds_d_max_code X6) by lia. exact ST2. }
    assert (S0 : SM.sbs_ok (arr_len (DS.ds_pending_buf (DT.send_bits X6 (4 + last) 3)))
                   (DT.send_bits X6 (4 + last) 3)
                   (FBM.sat_calls (DT.send_bits X6 (4 + last) 3) (DS.ds_l_max_code X6 + 1)
                      (DS.ds_d_max_code X6 + 1) (mb + 1))) by (rewrite LY; exact HD).
    destruct (br_send_all_trees' (DT.send_bits X6 (4 + last) 3) _ s2
                (DS.ds_l_max_code X6 + 1) (DS.ds_d_max_code X6 + 1) (mb + 1)
                BY (trel_nbw _ _ NY _ T6) (tree_lens_nbw _ _ NY L6) OY
                ltac:(rewrite YL; reflexivity) ltac:(rewrite YD; reflexivity) ltac:(lia) ltac:(unfold DS.L_CODES; lia)
                (scan_ok_nbw _ _ NY _ _ Hsl) (scan_ok_nbw _ _ NY _ _ Hsd) (bl_lens_ok_nbw _ _ NY Hbl)
                S0 S1 S2) as (R1 & R2 & _).
    split; [exact R1 | exact R2]. }
  destruct B13 as (R13 & O13).
  (* the body *)
  destruct (E5.HDRs s last FE) as [[_ _ BV13 _ PL13 _ _ _] _].
  assert (OK : SM.sbs_ok (arr_len (DS.ds_pending_buf (E5.hX13 X6 last mb))) (E5.hX13 X6 last mb)
                 (OvKit.cb_all s (DS.ds_dyn_ltree_fc X6) (DS.ds_dyn_ltree_dl X6)
                    (DS.ds_dyn_dtree_fc X6) (DS.ds_dyn_dtree_dl X6) N)).
  { apply cb_all_ok; [lia | exact BV13 | | | |].
    - intros j Hj. pose proof (E5.used_L s last FE j Hj) as X. rewrite E3.Len_eq, E3.tree_dl_TL in X. lia.
    - intros j Hj Hd'. pose proof (E5.used_D s last FE j Hj Hd') as X. rewrite E3.Len_eq, E3.tree_dl_TD in X. lia.
    - pose proof (E5.used_E s last FE) as X. rewrite E3.Len_eq, E3.tree_dl_TL in X. lia.
    - rewrite PL13. lia. }
  destruct (br_cb_body _ _ s _ _ _ _ (RT.ts_trees s2 RT.TK_L) (RT.ts_trees s2 RT.TK_D) (RT.ts_symbuf s2) N
              R13 O13 ltac:(lia) HS (ec_syms _ Hem)
              (arr_rel_narrow _ _ 0 DS.HEAP_SIZE 0 286 ltac:(lia) ltac:(unfold DS.HEAP_SIZE; lia) A1)
              (arr_rel_narrow _ _ 0 DS.HEAP_SIZE 0 286 ltac:(lia) ltac:(unfold DS.HEAP_SIZE; lia) A2)
              (arr_rel_narrow _ _ 0 (2 * DS.D_CODES + 1) 0 30 ltac:(lia) ltac:(unfold DS.D_CODES; lia) A3)
              (arr_rel_narrow _ _ 0 (2 * DS.D_CODES + 1) 0 30 ltac:(lia) ltac:(unfold DS.D_CODES; lia) A4)
              OK) as (R1 & R2 & _).
  split; [exact R1|]. split; [exact R2|].
  rewrite nbw_sbs. exact NB13.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  Stored                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma br_emit_sto : forall mbi,
  FBM.tfb_branch X6 (DO.fb_buf s) (DO.fb_len s) = 2 ->
  bw_rel (FBM.tfb_emit 2 X6 mb (DO.fb_buf s) (DO.fb_len s) last)
    (rt_emit_bw 2 (if Z.leb 0 (RD.ls_blockstart (RD.d_ls t))
                   then Some (RD.win_take (RD.ls_window (RD.d_ls t)) (RD.ls_blockstart (RD.d_ls t))
                                (RD.ls_strstart (RD.d_ls t) - RD.ls_blockstart (RD.d_ls t)))
                   else None)
       (RD.ls_strstart (RD.d_ls t) - RD.ls_blockstart (RD.d_ls t)) last mbi s2)
  /\ DS.ds_pending_out (FBM.tfb_emit 2 X6 mb (DO.fb_buf s) (DO.fb_len s) last) = 0
  /\ nbw (FBM.tfb_emit 2 X6 mb (DO.fb_buf s) (DO.fb_len s) last) = nbw X6.
Proof.
  intros mbi Hd.
  pose proof fe_sec as FE.
  pose proof (E3.tree_phase s (E5.OP s last FE)) as TP.
  destruct em_facts as (T6 & L6 & B6 & HS & SN & O6 & P6 & PL6 & V6).
  pose proof (E5.emit_facts s last FE OverlayCoreL.overlay_core_proof) as EF. cbv zeta in EF.
  rewrite Hd in EF. destruct EF as [_ SO].
  pose proof Hrel as (_ & Hl & _).
  unfold lz_rel in Hl. cbv zeta in Hl.
  destruct Hl as (Lw & _ & _ & Rw & _ & _ & _ & _ & Lbs & _ & _ & _ & Lss & _).
  pose proof Hlz as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  pose proof (E5.X6n s last FE) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pw & _).
  assert (Elen : DO.fb_len s = RD.ls_strstart (RD.d_ls t) - RD.ls_blockstart (RD.d_ls t)).
  { unfold DO.fb_len. rewrite Lss, Lbs. apply wrap64_id. lia. }
  pose proof (E5.branch2_le X6 (DO.fb_buf s) (DO.fb_len s) (E3.tp_opt _ TP) (E3.tp_stat_range _ TP)
                ltac:(rewrite Elen; lia) Hd) as [_ NB].
  assert (Hbs : 0 <= RD.ls_blockstart (RD.d_ls t)).
  { unfold DO.fb_buf in NB. rewrite Lbs in NB.
    destruct (Z.leb_spec 0 (RD.ls_blockstart (RD.d_ls t))); [lia | exfalso; apply NB; reflexivity]. }
  assert (Ebuf : DO.fb_buf s = Some (RD.ls_blockstart (RD.d_ls t))).
  { unfold DO.fb_buf. rewrite Lbs. replace (0 <=? RD.ls_blockstart (RD.d_ls t)) with true by (symmetry; apply Z.leb_le; lia).
    rewrite wrap32_id by lia. reflexivity. }
  rewrite (rt_emit_bw_2 (0 <=? RD.ls_blockstart (RD.d_ls t))) by (apply Z.leb_le; lia).
  rewrite Ebuf, Elen in SO |- *.
  destruct SO as [SO _].
  rewrite tfb_emit_2.
  destruct (br_tr_stored_block X6 s2 (RD.ls_window (RD.d_ls t)) (RD.ls_blockstart (RD.d_ls t))
              (RD.ls_strstart (RD.d_ls t) - RD.ls_blockstart (RD.d_ls t)) last
              B6 O6 Hbs ltac:(lia)
              ltac:(intros i Hi; rewrite Pw; split; [apply Rw | apply W7]; lia)
              ltac:(rewrite PL6; exact SO)) as (R1 & R2 & _ & R4).
  split; [exact R1 | split; [exact R2 | exact R4]].
Qed.

End Emit.

Print Assumptions br_emit_stat.
Print Assumptions br_emit_dyn.
Print Assumptions br_emit_sto.
