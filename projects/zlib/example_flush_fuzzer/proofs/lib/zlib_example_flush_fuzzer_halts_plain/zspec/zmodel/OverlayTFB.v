(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import RefSendTree3 RefSendTree4 RefFlushBlk9 RefFlushBlk11.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import FillWinModel TreeModel BuildTreeModel ScanModel SendModel CompressModel GenBitlenModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees HuffBuild HuffBuild2 HuffSpec HuffFlush HuffSend DeflRoom DeflateInvKeep OverlayFBS OverlayRace OverlayCmp OverlayHdr OverlayFlush OverlayDyn OverlayStat OverlayBT OverlayNeed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma sat_ok_of_sbs : forall P f X b r,
  sbs_ok P X (sat_calls X b r) -> (Z.to_nat (b - r) <= f)%nat -> RefFlushBlk9.sat_ok P f X b r.
Proof.
  intros P f. induction f as [|f IH]; intros X b r OK Hf; [exact I|].
  rewrite RefFlushBlk9.sat_ok_step. destruct (Z.ltb_spec r b); [|exact I].
  unfold sat_calls in OK. replace (Z.to_nat (b - r)) with (S (Z.to_nat (b - (r + 1)))) in OK by lia.
  rewrite ziota_split1 in OK. cbn [map sbs_ok] in OK. destruct OK as (_ & R & OK).
  split; [exact R|]. apply IH; [|lia].
  unfold sat_calls. erewrite (map_ext _ _); [exact OK|].
  intros a. cbn beta. unfold Len. rewrite sb_tree_dl. reflexivity.
Qed.

Lemma strm_init_block : forall X, ds_strm (init_block X) = ds_strm X.
Proof. intros X. destruct X; reflexivity. Qed.

Lemma dt_set_strm : forall X st, cs_data_type (ds_strm (set_strm X st)) = cs_data_type st.
Proof. intros X st. destruct X; reflexivity. Qed.

Lemma set_strm_arrays : forall X st,
  ds_dyn_ltree_dl (set_strm X st) = ds_dyn_ltree_dl X /\ ds_dyn_dtree_dl (set_strm X st) = ds_dyn_dtree_dl X
  /\ ds_bl_tree_fc (set_strm X st) = ds_bl_tree_fc X /\ ds_bl_tree_dl (set_strm X st) = ds_bl_tree_dl X
  /\ ds_dyn_ltree_fc (set_strm X st) = ds_dyn_ltree_fc X /\ ds_dyn_dtree_fc (set_strm X st) = ds_dyn_dtree_fc X.
Proof. intros X st. destruct X; repeat split; reflexivity. Qed.

Lemma static_len_set_opt_len : forall X v, ds_static_len (set_opt_len X v) = ds_static_len X.
Proof. intros X v. destruct X; reflexivity. Qed.

Lemma tfb_strm : forall s buf len last, 0 < ds_level s ->
  ds_strm (tr_flush_block s buf len last) = ds_strm (fs0 s).
Proof.
  intros s buf len last Hl. unfold tr_flush_block. fold (fs0 s). set (s1 := fs0 s).
  assert (TAIL : forall a, ds_strm (if negb (last =? 0) then bi_windup (init_block a) else init_block a) = ds_strm a).
  { intros a. destruct (negb (last =? 0)); [rewrite (kp_strm _ _ (kp_bi_windup _))|]; apply strm_init_block. }
  replace (0 <? ds_level s) with true by (symmetry; apply Z.ltb_lt; exact Hl).
  destruct (build_bl_tree (build_tree (build_tree s1 TL) TD)) as [s4 mb] eqn:E4.
  pose proof (kp_build_bl_tree (build_tree (build_tree s1 TL) TD)) as K4. rewrite E4 in K4. cbn [fst] in K4. rewrite !kp_build_tree in K4.
  cbv beta iota zeta. rewrite TAIL. apply kp_strm.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    rewrite ?kp_tr_stored_block, ?kp_compress_block, ?kp_send_all_trees, ?kp_send_bits; exact K4.
Qed.


Ltac name_let x E rhs := intro x; generalize (@eq_refl _ x : x = rhs); clearbody x; revert x; intros x E.

Section TFB.
  Variable syms : list (Z * Z).
  Variables (s : deflate_state) (buf : option Z) (len last : Z).
  Hypothesis FB : FBS syms s buf len last.
  Hypothesis NEED : dyn_need syms s last.

  Theorem tfb_safe_need : fb_safe s buf len last.
  Proof.
    pose proof (fbs_level _ _ _ _ _ FB) as LV. pose proof (fbs_data_type _ _ _ _ _ FB) as DT.
    pose proof (L_range syms s buf len last FB) as [LR NR]. pose proof (PBL4 syms s buf len last FB) as P4.
    pose proof (fbs_cty _ _ _ _ _ FB) as CT. pose proof (fbs_lens _ _ _ _ _ FB) as TLS.
    pose proof (fbs_strategy _ _ _ _ _ FB) as STR. pose proof (fbs_len _ _ _ _ _ FB) as LEN0.
    pose proof (fbs_bi_valid _ _ _ _ _ FB) as BV0.
    cbv beta delta [fb_safe]. name_let PBLv EP (PBL s). subst PBLv.
    split; [lia|]. split; [exact DT|]. split; [rewrite P4; lia|].
    split.
    { rewrite (tfb_strm s buf len last ltac:(lia)). replace (0 <? ds_level s) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
      unfold fs0. destruct (cs_data_type (ds_strm s) =? Z_UNKNOWN); [apply dt_set_strm| reflexivity]. }
    replace (0 <? ds_level s) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
    split. { intros _ k Hk. apply (ct_lfc _ CT). unfold fbs_tree_lens in TLS. lia. }
    name_let s0 Es0 (fs0 s). subst s0.
    name_let X1 E1 (build_tree (fs0 s) TL).
    name_let X2 E2 (build_tree X1 TD).
    name_let mcl Emcl (ds_l_max_code X2). subst mcl.
    name_let X3 E3 (scan_tree X2 TL (ds_l_max_code X2)).
    name_let mcd Emcd (ds_d_max_code X3). subst mcd.
    name_let X4 E4 (scan_tree X3 TD (ds_d_max_code X3)).
    name_let X5 E5 (build_tree X4 TB).
    name_let mb Emb (fmb X5). subst mb.
    name_let X6 E6 (set_opt_len X5 (wrap64 (ds_opt_len X5 + 3 * (fmb X5 + 1) + 5 + 5 + 4))).
    name_let opt_lenb Eol (Z.shiftr (wrap64 (ds_opt_len X6 + 3 + 7)) 3).
    name_let static_lenb Esl (Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3).
    name_let opt_lenb0 Eol0 (if (static_lenb <=? opt_lenb) || (ds_strategy X6 =? Z_FIXED) then static_lenb else opt_lenb).
    name_let sto Esto ((wrap64 (len + 4) <=? opt_lenb0) && match buf with Some _ => true | None => false end).
    name_let sta Esta (static_lenb =? opt_lenb0).
    name_let X7 E7 (if sto then tr_stored_block X6 buf len last
                    else if sta then (let s1 := send_bits X6 (Z.shiftl STATIC_TREES 1 + last) 3 in
                                      compress_block s1 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl)
                    else (let s1 := send_bits X6 (Z.shiftl DYN_TREES 1 + last) 3 in
                          let s2 := send_all_trees s1 (ds_l_max_code s1 + 1) (ds_d_max_code s1 + 1) (fmb X5 + 1) in
                          compress_block s2 (ds_dyn_ltree_fc s2) (ds_dyn_ltree_dl s2) (ds_dyn_dtree_fc s2) (ds_dyn_dtree_dl s2))).
    destruct (flush_facts syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6) as (LL & LzL & LD & LzD & LB & LzB & b4 &
      [B1 B2 FC1D B5 FC4B Lb4 NN4 BS316 LENS ZL GL LEND ZD GD LENB ZB MCL MCD RL RD SU S256 EY3 EY4 LQ2 LQ3 BL2 BL4 B0 TL2 TL3 TL5
       SLv TBnn OLlo OLhi K6 PB6 PD6 BV6 BB6 DL6L DL6D DL6B FC6L FC6D TL4 P1 P2 P5 MCL2 MCD3]).
    assert (CT0 : cty (fs0 s)).
    { unfold fs0. destruct (cs_data_type (ds_strm s) =? Z_UNKNOWN); [apply cty_set_strm_dt; exact CT| exact CT]. }
    assert (CT1 : cty X1) by (rewrite E1; apply cty_build_tree; exact CT0).
    assert (CT2 : cty X2) by (rewrite E2; apply cty_build_tree; exact CT1).
    assert (CT3 : cty X3) by (rewrite E3; apply cty_scan_tree; exact CT2).
    assert (CT4 : cty X4) by (rewrite E4; apply cty_scan_tree; exact CT3).
    assert (CT5 : cty X5) by (rewrite E5; apply cty_build_tree; exact CT4).
    assert (CT6 : cty X6) by (rewrite E6; apply cty_set_opt_len; exact CT5).
    pose proof TL2 as TL2'. unfold tree_lens in TL2'. pose proof TL3 as TL3'. unfold tree_lens in TL3'. pose proof TL5 as TL5'. unfold tree_lens in TL5'.
    assert (L2v : forall i, 0 <= i <= bt_mc s TL -> Len X2 TL i = Len X5 TL i).
    { intros i Hi. rewrite (LQ2 i) by lia. rewrite Len_set_Len by (rewrite (tree_lens_dl X2 TL TL2); cbn [tsize]; lia).
      destruct (Z.eqb_spec (bt_mc s TL + 1) i); [lia| reflexivity]. }
    assert (L3v : forall i, 0 <= i <= bt_mc s TD -> Len X3 TD i = Len X5 TD i).
    { intros i Hi. rewrite (LQ3 i) by lia. rewrite Len_set_Len by (rewrite (tree_lens_dl X3 TD TL3); cbn [tsize]; lia).
      destruct (Z.eqb_spec (bt_mc s TD + 1) i); [lia| reflexivity]. }
    assert (L5L : forall i, 0 <= i <= bt_mc s TL -> 0 <= Len X5 TL i <= 15).
    { intros i Hi. destruct (in_dec Z.eq_dec i (bt_U s TL)) as [IN|NIN]; [pose proof (LENS i IN); lia| rewrite ZL by assumption; lia]. }
    assert (L5D : forall i, 0 <= i <= bt_mc s TD -> 0 <= Len X5 TD i <= 15).
    { intros i Hi. destruct (in_dec Z.eq_dec i (bt_U s TD)) as [IN|NIN]; [pose proof (LEND i IN); lia| rewrite ZD by assumption; lia]. }
    rewrite !MCL2, !MCD3.
    split; [exact (bt_safe_intro (fs0 s) TL P1 CT0)|].
    split; [exact (bt_safe_intro X1 TD P2 CT1)|].
    split; [lia|].
    split; [intros i Hi; rewrite L2v by exact Hi; apply L5L; exact Hi|].
    split; [intros i Hi; apply (cty_tree_dl X2 TL CT2); rewrite (tree_lens_dl X2 TL TL2); exact Hi|].
    split; [intros i Hi; apply (ct_bfc X2 CT2); lia|].
    split; [lia|].
    split; [intros i Hi; rewrite L3v by exact Hi; apply L5D; exact Hi|].
    split; [intros i Hi; apply (cty_tree_dl X3 TD CT3); rewrite (tree_lens_dl X3 TD TL3); exact Hi|].
    split; [intros i Hi; apply (ct_bfc X3 CT3); lia|].
    split; [exact (bt_safe_intro X4 TB P5 CT4)|].
    split; [intros i Hi; apply (cty_tree_dl X5 TB CT5); rewrite (tree_lens_dl X5 TB TL5); exact Hi|].
    pose proof (Sstat_bound syms s buf len last FB) as SB.
    assert (SL5 : ds_static_len X5 = Sstat syms) by (rewrite <- SLv, E6, static_len_set_opt_len; reflexivity).
    assert (OL5r : 0 <= ds_opt_len X5 < 2 ^ 64).
    { destruct B5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OL & _). rewrite OL. apply wrap64_range. }
    split; [exact OL5r|]. split; [rewrite SL5; lia|].
    assert (K5 : kproj X5 = kproj (fs0 s)) by (rewrite <- K6, E6, kp_set_opt_len; reflexivity).
    pose proof (fs0_fields syms s buf len last FB) as (Fpb & Fpd & Fbv & Fbb & Flb & Fsn & Fbc & Fhp & Fdp & Fol & Fsl & Flv & Fst & Fwi & Fbl & Fse).
    split; [rewrite (kp_strategy _ _ K5), Fst; exact STR|].
    assert (SLB : static_lenb = (Sstat syms + 10) / 8).
    { rewrite Esl, SLv. rewrite Z.shiftr_div_pow2 by lia. rewrite wrap64_id by lia. change (2 ^ 3) with 8. f_equal. lia. }
    destruct (dyn_cost_sum syms s buf len last FB LzL LzD ltac:(intros j Hj; apply (proj2 (LENS j Hj))) ltac:(intros j Hj; apply (proj2 (LEND j Hj)))) as (_ & DCS2 & L256).
    pose proof (fmb_range X5) as MBR.
    assert (OLB : opt_lenb = (ds_opt_len X6 + 10) / 8).
    { rewrite Eol. rewrite Z.shiftr_div_pow2 by lia. rewrite wrap64_id by lia. change (2 ^ 3) with 8. f_equal. lia. }
    assert (OLB0 : opt_lenb0 <= static_lenb /\ (opt_lenb0 = static_lenb \/ (opt_lenb0 = opt_lenb /\ ds_opt_len X6 < ds_static_len X6))).
    { rewrite Eol0. destruct (Z.leb_spec static_lenb opt_lenb); cbn [orb]; [lia|].
      destruct (ds_strategy X6 =? Z_FIXED); [lia|]. split; [lia|]. right. split; [reflexivity|].
      rewrite SLv. rewrite OLB, SLB in *.
      pose proof (Z.div_le_mono (Sstat syms + 10) (ds_opt_len X6 + 10) 8 ltac:(lia)). lia. }
    rewrite wrap64_id in Esto by lia.
    destruct sto.
    {
      assert (STO : len + 4 <= Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3).
      { rewrite <- Esl. symmetry in Esto. apply andb_prop in Esto. destruct Esto as [E _]. apply Z.leb_le in E. lia. }
      pose proof (sto_branch syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6 STO) as SBr. cbv zeta in SBr.
      destruct SBr as (BINV6 & WIN6 & BX & BVX & PX & ALX & CX).
      split. { split; [exact BINV6|]. split; [unfold BINV in BX; lia| exact WIN6]. }
      pose proof (tail_bits s last (tr_stored_block X6 buf len last) BX ltac:(unfold vsize; rewrite BVX; lia) ALX CX) as TB0.
      cbv zeta in TB0. destruct TB0 as (T1 & T2 & T3 & _).
      rewrite E7. split; [exact T1| intros _; exact T3]. }
    destruct sta.
    {
      pose proof (stat_branch syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6 _ _ eq_refl eq_refl) as SBr.
      destruct SBr as (BINV6 & R6 & CBOK & SN7 & LB7 & BE & VE & CE & ALE).
      split. { split; [exact BINV6|]. split; [exact R6|]. cbv zeta. split; [exact CBOK|]. rewrite SN7, LB7. unfold OverlayFlush.nS, OverlayFlush.LS in *. lia. }
      pose proof (tail_bits s last _ BE ltac:(rewrite VE; unfold OverlayFlush.nS in *; lia) ALE CE) as TB0.
      cbv zeta in TB0. destruct TB0 as (T1 & T2 & T3 & _).
      rewrite E7. split; [exact T1| intros _; exact T3]. }
    assert (DYN : ds_opt_len X6 < ds_static_len X6).
    { destruct OLB0 as [_ [E|[_ D]]]; [exfalso; rewrite E, Z.eqb_refl in Esta; discriminate| exact D]. }
    pose proof (NEED X1 X2 X3 X4 X5 X6 _ _ E1 E2 E3 E4 E5 E6 eq_refl eq_refl DYN) as RACE.
    pose proof (dyn_branch syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6 _ _ _ eq_refl eq_refl eq_refl ltac:(lia) RACE) as DB.
    pose proof (fY6_frames syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6 _ eq_refl) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (sbs_tabs syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6 _ eq_refl nil) as S7. cbn [sbs_run] in S7.
    destruct S7 as (XL7 & XC7 & DL7 & FCL7 & FCD7 & LB7 & SN7 & PBL7 & MCL7 & MCD7).
    assert (Elmc : ds_l_max_code X6 = bt_mc s TL) by (rewrite <- F4; exact MCL7).
    assert (Edmc : ds_d_max_code X6 = bt_mc s TD) by (rewrite <- F5; exact MCD7).
    cbv delta [fX10 fX11 fX12 HDR3] in DB. cbn [sbs_run] in DB.    destruct DB as (BINV6 & R6 & R7 & R8 & R9 & E10 & SOK & L11 & B11 & ST11 & L12 & B12 & ST12 & E13 & C11 & C12 & Ch & CBOK & SNh & LBh & BE & VE & CE & ALE & VO).
    assert (KL : forall X, cty X -> kproj X = kproj (fs0 s) ->
              (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X TL) i < 65536)
              /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X TD) i < 65536)
              /\ (forall c, 0 <= c < 39 -> 0 <= arr_get (ds_bl_tree_fc X) c < 65536)
              /\ (forall k, 0 <= k < 39 -> 0 <= arr_get (ds_bl_tree_dl X) k < 65536)
              /\ (forall i, 0 <= i < 286 -> 0 <= arr_get (ds_dyn_ltree_fc X) i < 65536)
              /\ (forall i, 0 <= i < 30 -> 0 <= arr_get (ds_dyn_dtree_fc X) i < 65536)).
    { intros X CX KX. unfold fbs_tree_lens in TLS.
      pose proof (kp_len_dyn_ltree_dl _ _ KX) as A1. pose proof (kp_len_dyn_dtree_dl _ _ KX) as A2.
      pose proof (kp_len_bl_tree_fc _ _ KX) as A3. pose proof (kp_len_bl_tree_dl _ _ KX) as A4.
      pose proof (kp_len_dyn_ltree_fc _ _ KX) as A5. pose proof (kp_len_dyn_dtree_fc _ _ KX) as A6.
      assert (FS : arr_len (ds_dyn_ltree_dl (fs0 s)) = 573 /\ arr_len (ds_dyn_dtree_dl (fs0 s)) = 61 /\ arr_len (ds_bl_tree_fc (fs0 s)) = 39
                   /\ arr_len (ds_bl_tree_dl (fs0 s)) = 39 /\ arr_len (ds_dyn_ltree_fc (fs0 s)) = 573 /\ arr_len (ds_dyn_dtree_fc (fs0 s)) = 61).
      { rewrite (fs0_eq syms s buf len last FB). destruct (set_strm_arrays s (ds_strm (fs0 s))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
        rewrite Q1, Q2, Q3, Q4, Q5, Q6. lia. }
      destruct FS as (F1' & F2' & F3' & F4' & F5' & F6').
      split; [intros i Hi; apply (ct_ldl _ CX); lia|]. split; [intros i Hi; apply (ct_ddl _ CX); lia|].
      split; [intros i Hi; apply (ct_bfc _ CX); lia|]. split; [intros i Hi; apply (ct_bdl _ CX); lia|].
      split; [intros i Hi; apply (ct_lfc _ CX); lia| intros i Hi; apply (ct_dfc _ CX); lia]. }
    assert (LenTB : forall X c, Len X TB c = arr_get (ds_bl_tree_dl X) c) by reflexivity.
    split.
    { cbv beta delta [RefFlushBlk9.dyn_ok]. cbv zeta. rewrite !Elmc, !Edmc. rewrite !E13.      match type of C11 with cty ?a => destruct (KL a C11 ltac:(autorewrite with kp; exact K6)) as (DL11' & _ & BFC11 & BDL11 & _) end.
      match type of C12 with cty ?a => destruct (KL a C12 ltac:(autorewrite with kp; exact K6)) as (_ & DL12' & BFC12 & BDL12 & _) end.
      match type of Ch with cty ?a => destruct (KL a Ch ltac:(autorewrite with kp; exact K6)) as (_ & _ & _ & _ & LFCh & DFCh) end.
      destruct (KL X6 CT6 K6) as (_ & _ & _ & BDL6 & _).
      split. { split; [exact BINV6|]. split; [exact R6|]. split; [exact R7|]. split; [exact R8|]. split; [exact R9|].
               apply sat_ok_of_sbs; [exact SOK| pose proof (fmb_range X5); lia]. }
      split; [lia|]. split; [lia|]. split; [exact BDL6|].
      split. { split; [exact L11|]. split; [exact DL11'|]. split; [exact BFC11|].
               split; [intros c Hc; pose proof (B11 c Hc) as Bc; rewrite LenTB in Bc; lia|].
               exact ST11. }
      split. { split; [exact L12|]. split; [exact DL12'|]. split; [exact BFC12|].
               split; [intros c Hc; pose proof (B12 c Hc) as Bc; rewrite LenTB in Bc; lia|].
               exact ST12. }
      split; [exact CBOK|]. split; [exact LFCh|]. split; [exact DFCh|]. rewrite SNh, LBh. unfold OverlayFlush.nS, OverlayFlush.LS in *. lia. }
    pose proof (tail_bits s last _ BE ltac:(rewrite SLv in VE; unfold OverlayFlush.nS in *; lia) ALE CE) as TB0.
    cbv zeta in TB0. destruct TB0 as (T1 & T2 & T3 & _).
    rewrite E7. split; [exact T1| intros _; exact T3].
  Qed.

  Theorem tfb_room_need :
    let s' := tr_flush_block s buf len last in
    vsize s' + 80 <= 8 * arr_len (ds_pending_buf s) /\ 0 <= ds_bi_valid s' <= 16 /\ 0 <= ds_bi_buf s' < 2 ^ 16 /\ 0 <= ds_pending s'.
  Proof.
    pose proof (fbs_level _ _ _ _ _ FB) as LV.
    pose proof (L_range syms s buf len last FB) as [LR NR]. pose proof (PBL4 syms s buf len last FB) as P4.
    pose proof (fbs_cty _ _ _ _ _ FB) as CT. pose proof (fbs_lens _ _ _ _ _ FB) as TLS.
    pose proof (fbs_strategy _ _ _ _ _ FB) as STR. pose proof (fbs_len _ _ _ _ _ FB) as LEN0.
    pose proof (fbs_bi_valid _ _ _ _ _ FB) as BV0.
    cbv zeta. rewrite (tfb_eq_raw s buf len last ltac:(lia)). change (arr_len (ds_pending_buf s)) with (PBL s).
    enough (H :
      let s1 := if cs_data_type (ds_strm s) =? Z_UNKNOWN then set_strm s (cset_data_type (ds_strm s) (detect_data_type s)) else s in
      let X1 := build_tree s1 TL in
      let X2 := build_tree X1 TD in
      let X3 := scan_tree X2 TL (ds_l_max_code X2) in
      let X4 := scan_tree X3 TD (ds_d_max_code X3) in
      let X5 := build_tree X4 TB in
      let mb := build_bl_tree_loop 17 X5 (BL_CODES - 1) in
      let X6 := set_opt_len X5 (wrap64 (ds_opt_len X5 + 3 * (mb + 1) + 5 + 5 + 4)) in
      let opt_lenb := Z.shiftr (wrap64 (ds_opt_len X6 + 3 + 7)) 3 in
      let static_lenb := Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3 in
      let opt_lenb0 := if (static_lenb <=? opt_lenb) || (ds_strategy X6 =? Z_FIXED) then static_lenb else opt_lenb in
      let X7 := if (wrap64 (len + 4) <=? opt_lenb0) && match buf with Some _ => true | None => false end
                then tr_stored_block X6 buf len last
                else if static_lenb =? opt_lenb0
                then (let s0 := send_bits X6 (Z.shiftl STATIC_TREES 1 + last) 3 in
                      compress_block s0 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl)
                else (let s0 := send_bits X6 (Z.shiftl DYN_TREES 1 + last) 3 in
                      let s1 := send_all_trees s0 (ds_l_max_code s0 + 1) (ds_d_max_code s0 + 1) (mb + 1) in
                      compress_block s1 (ds_dyn_ltree_fc s1) (ds_dyn_ltree_dl s1) (ds_dyn_dtree_fc s1) (ds_dyn_dtree_dl s1)) in
      let X8 := init_block X7 in
      let X9 := if negb (last =? 0) then bi_windup X8 else X8 in
      vsize X9 + 80 <= 8 * PBL s /\ 0 <= ds_bi_valid X9 <= 16 /\ 0 <= ds_bi_buf X9 < 2 ^ 16 /\ 0 <= ds_pending X9) by exact H.
    name_let s0 Es0 (fs0 s). subst s0.
    name_let X1 E1 (build_tree (fs0 s) TL).
    name_let X2 E2 (build_tree X1 TD).
    name_let X3 E3 (scan_tree X2 TL (ds_l_max_code X2)).
    name_let X4 E4 (scan_tree X3 TD (ds_d_max_code X3)).
    name_let X5 E5 (build_tree X4 TB).
    name_let mb Emb (fmb X5). subst mb.
    name_let X6 E6 (set_opt_len X5 (wrap64 (ds_opt_len X5 + 3 * (fmb X5 + 1) + 5 + 5 + 4))).
    name_let opt_lenb Eol (Z.shiftr (wrap64 (ds_opt_len X6 + 3 + 7)) 3).
    name_let static_lenb Esl (Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3).
    name_let opt_lenb0 Eol0 (if (static_lenb <=? opt_lenb) || (ds_strategy X6 =? Z_FIXED) then static_lenb else opt_lenb).
    name_let X7 E7 (if (wrap64 (len + 4) <=? opt_lenb0) && match buf with Some _ => true | None => false end then tr_stored_block X6 buf len last
                    else if static_lenb =? opt_lenb0 then (let s1 := send_bits X6 (Z.shiftl STATIC_TREES 1 + last) 3 in
                                      compress_block s1 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl)
                    else (let s1 := send_bits X6 (Z.shiftl DYN_TREES 1 + last) 3 in
                          let s2 := send_all_trees s1 (ds_l_max_code s1 + 1) (ds_d_max_code s1 + 1) (fmb X5 + 1) in
                          compress_block s2 (ds_dyn_ltree_fc s2) (ds_dyn_ltree_dl s2) (ds_dyn_dtree_fc s2) (ds_dyn_dtree_dl s2))).
    cbv zeta.
    destruct (flush_facts syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6) as (LL & LzL & LD & LzD & LB & LzB & b4 &
      [B1 B2 FC1D B5 FC4B Lb4 NN4 BS316 LENS ZL GL LEND ZD GD LENB ZB MCL MCD RL RD SU S256 EY3 EY4 LQ2 LQ3 BL2 BL4 B0 TL2 TL3 TL5
       SLv TBnn OLlo OLhi K6 PB6 PD6 BV6 BB6 DL6L DL6D DL6B FC6L FC6D TL4 P1 P2 P5 MCL2 MCD3]).
    pose proof (Sstat_bound syms s buf len last FB) as SB.
    destruct (dyn_cost_sum syms s buf len last FB LzL LzD ltac:(intros j Hj; apply (proj2 (LENS j Hj))) ltac:(intros j Hj; apply (proj2 (LEND j Hj)))) as (_ & DCS2 & L256).
    pose proof (fmb_range X5) as MBR.
    assert (SLB : static_lenb = (Sstat syms + 10) / 8).
    { rewrite Esl, SLv. rewrite Z.shiftr_div_pow2 by lia. rewrite wrap64_id by lia. change (2 ^ 3) with 8. f_equal. lia. }
    assert (OLB : opt_lenb = (ds_opt_len X6 + 10) / 8).
    { rewrite Eol. rewrite Z.shiftr_div_pow2 by lia. rewrite wrap64_id by lia. change (2 ^ 3) with 8. f_equal. lia. }
    assert (OLB0 : opt_lenb0 <= static_lenb /\ (opt_lenb0 = static_lenb \/ (opt_lenb0 = opt_lenb /\ ds_opt_len X6 < ds_static_len X6))).
    { rewrite Eol0. destruct (Z.leb_spec static_lenb opt_lenb); cbn [orb]; [lia|].
      destruct (ds_strategy X6 =? Z_FIXED); [lia|]. split; [lia|]. right. split; [reflexivity|].
      rewrite SLv. rewrite OLB, SLB in *.
      pose proof (Z.div_le_mono (Sstat syms + 10) (ds_opt_len X6 + 10) 8 ltac:(lia)). lia. }
    rewrite wrap64_id in E7 by lia.
    assert (GOAL : forall X, BINV (PBL s) X -> vsize X + 87 <= 8 * PBL s -> arr_len (ds_pending_buf X) = PBL s -> cty X -> X7 = X ->
              vsize (if negb (last =? 0) then bi_windup (init_block X7) else init_block X7) + 80 <= 8 * PBL s
              /\ 0 <= ds_bi_valid (if negb (last =? 0) then bi_windup (init_block X7) else init_block X7) <= 16
              /\ 0 <= ds_bi_buf (if negb (last =? 0) then bi_windup (init_block X7) else init_block X7) < 2 ^ 16
              /\ 0 <= ds_pending (if negb (last =? 0) then bi_windup (init_block X7) else init_block X7)).
    { intros X BX VX AX CX ->. pose proof (tail_bits s last X BX VX AX CX) as TB0. cbv zeta in TB0.
      destruct TB0 as (_ & _ & _ & T4 & T5 & T6 & T7 & _). auto. }
    destruct ((len + 4 <=? opt_lenb0) && match buf with Some _ => true | None => false end) eqn:Esto.
    {
      assert (STO : len + 4 <= Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3).
      { rewrite <- Esl. apply andb_prop in Esto. destruct Esto as [E _]. apply Z.leb_le in E. lia. }
      pose proof (sto_branch syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6 STO) as SBr. cbv zeta in SBr.
      destruct SBr as (BINV6 & WIN6 & BX & BVX & PX & ALX & CX).
      exact (GOAL _ BX ltac:(unfold vsize; rewrite BVX; lia) ALX CX E7). }
    destruct (static_lenb =? opt_lenb0) eqn:Esta.
    {
      pose proof (stat_branch syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6 _ _ eq_refl eq_refl) as SBr.
      destruct SBr as (BINV6 & R6 & CBOK & SN7 & LB7 & BE & VE & CE & ALE).
      exact (GOAL _ BE ltac:(rewrite VE; unfold OverlayFlush.nS in *; lia) ALE CE E7). }
    assert (DYN : ds_opt_len X6 < ds_static_len X6).
    { destruct OLB0 as [_ [E|[_ D]]]; [exfalso; rewrite E, Z.eqb_refl in Esta; discriminate| exact D]. }
    pose proof (NEED X1 X2 X3 X4 X5 X6 _ _ E1 E2 E3 E4 E5 E6 eq_refl eq_refl DYN) as RACE.
    pose proof (dyn_branch syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6 _ _ _ eq_refl eq_refl eq_refl ltac:(lia) RACE) as DB.
    destruct DB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BE & VE & CE & ALE & VO).
    exact (GOAL _ BE ltac:(rewrite SLv in VE; unfold OverlayFlush.nS in *; lia) ALE CE E7).
  Qed.
End TFB.


Theorem tfb_safe_of_need :
  (forall syms s buf len last, FBS syms s buf len last -> dyn_need syms s last) ->
  forall syms s buf len last, FBS syms s buf len last -> 0 <= cs_data_type (ds_strm s) <= 2 -> fb_safe s buf len last.
Proof. intros ND syms s buf len last FB _. exact (tfb_safe_need syms s buf len last FB (ND _ _ _ _ _ FB)). Qed.

Theorem tfb_room_of_need :
  (forall syms s buf len last, FBS syms s buf len last -> dyn_need syms s last) ->
  forall syms s buf len last, FBS syms s buf len last -> 0 <= cs_data_type (ds_strm s) <= 2 ->
    let s' := tr_flush_block s buf len last in
    vsize s' + 80 <= 8 * arr_len (ds_pending_buf s) /\ 0 <= ds_bi_valid s' <= 16 /\ 0 <= ds_bi_buf s' < 2 ^ 16 /\ 0 <= ds_pending s'.
Proof. intros ND syms s buf len last FB _. exact (tfb_room_need syms s buf len last FB (ND _ _ _ _ _ FB)). Qed.
