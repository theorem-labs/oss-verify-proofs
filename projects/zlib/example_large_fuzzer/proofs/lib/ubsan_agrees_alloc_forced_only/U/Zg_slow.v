(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_frame Z_slow_kit Z_ukit
  Z_slow_fbC Z_adler32 Zg_adler32_iface Zg_readbuf Zg_defl_iface Zg_slow_frame Zg_slow_fill Zgs_fbA Zgs_fbB Zgs_hash Zgs_dist2 Zgs_dist Zgs_lit Zgs_litT Zgs_misc Zg_slow_fbD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow5 RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Lemma st_bflush_true : forall s,
  st_bflush s true = (flush_block_only s 0, if cs_avail_out (ds_strm (flush_block_only s 0)) =? 0 then LRet need_more else LCont).
Proof. intros s. unfold st_bflush, flush_block. cbv zeta. destruct (_ =? 0); reflexivity. Qed.

Lemma st_bflush_false : forall s, st_bflush s false = (s, LCont).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fst_pr : forall {A B} (a : A) (b : B), fst (a, b) = a. Proof. reflexivity. Qed.
Lemma snd_pr : forall {A B} (a : A) (b : B), snd (a, b) = b. Proof. reflexivity. Qed.

Lemma deflate_tail_finish_eq : forall t,
  deflate_tail t Z_FINISH = (flush_block_only t 1, if cs_avail_out (ds_strm (flush_block_only t 1)) =? 0 then finish_started else finish_done).
Proof. intros t. unfold deflate_tail, flush_block. change (Z_FINISH =? Z_FINISH) with true. cbv iota zeta. destruct (_ =? 0); reflexivity. Qed.

Section SLOWG.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFW : fill_window_stmtg.
Hypothesis HTFBLK : tr_flush_block_stmtE.   (* [comment removed for export] *)
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : 0 <= flush <= 5.

Local Notation SKq := (SK L flush rest0 lo r fj F fc me).
Local Notation SKr := (SKret L flush rest0 lo r fj F fc me).
Local Notation ROOM s := (Box (OUT s <= length rest0)%nat).

(* [comment removed for export] *)
Lemma room_OUTg : forall s, ROOM s -> (length (cs_out_rev (ds_strm s)) <= length rest0)%nat.
Proof. intros s [H]. exact H. Qed.

(* [comment removed for export] *)
Lemma slow_decg : forall (Q : machine_state -> Prop) (X4 : deflate_state),
  SCFGg inp X4 -> sdec_ok 32768 X4 -> sdec_fe X4 -> ROOM (fst (st_decide X4)) ->
  (snd (st_decide X4) = LCont -> SKq Q Z_SLOW_HEAD (fst (st_decide X4))) ->
  (forall bs, snd (st_decide X4) = LRet bs -> SKr Q (bs_code bs) (fst (st_decide X4))) ->
  KD L flush rest0 lo r fj F fc me Q X4.
Proof.
  intros Q X4 C (SV & RLA & D) [FED FEL] RM KC KR.
  pose proof SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  pose proof C as [Cws Chs Clbs Cwrap Cwrap0 Cwrng Cain Caout Ctie].
  apply (slow_decide L flush rest0 lo r fj F fc me HFL); [exact Rpl| exact Rml| exact Rma| | |].
  - (* [comment removed for export] *)
    intros DC. rewrite DC in D. pose proof D as (PLLA & SL3 & DD & RLA' & FOK).
    pose proof (SCFGg_SF _ _ _ (SF_st_sdist' X4) C) as C'.
    assert (ED : st_decide X4 = st_bflush (fst (st_sdist X4)) (snd (st_sdist X4))) by (unfold st_decide; rewrite DC; reflexivity).
    rewrite ED in RM, KC, KR. clear ED.
    intros until m'. intros SI.
    eapply (slow_dist L flush inp rest0 lo r fj F fc me CTX HFL Q X4); [exact SI| exact SV| exact DC| exact D| lia| exact Cws| exact Chs| exact Clbs| |].
    + intros B. rewrite B in KC. rewrite st_bflush_false in KC. rewrite fst_pr, snd_pr in KC. exact (KC eq_refl).
    + intros B. specialize (FOK B). pose proof (FED DC B) as FE. rewrite B in RM, KC, KR. rewrite st_bflush_true in RM, KC, KR. rewrite ?fst_pr, ?snd_pr in RM, KC, KR.
      pose proof (SCFGg_fbo _ _ _ C' FOK) as CF.
      unfold KA. intros until m'0. intros SI'.
      eapply (slow_fbA L flush inp rest0 lo r fj F fc me CTX HTFBLK HTFB Q); [exact SI'| exact FOK| exact FE| exact (g_lbs _ _ C')| exact (g_ws _ _ C')| exact (g_aout _ _ C')| exact (room_OUTg _ RM)|].
      apply (slow_aexit L flush inp rest0 lo r fj F fc me CTX); [exact (g_aout _ _ CF)| |].
      * intros A0. rewrite A0 in KR. exact (KR need_more eq_refl).
      * intros A0. replace (cs_avail_out (ds_strm (flush_block_only (fst (st_sdist X4)) 0)) =? 0) with false in KC by (symmetry; apply Z.eqb_neq; exact A0).
        exact (KC eq_refl).
  - (* [comment removed for export] *)
    intros DC MA. rewrite DC in D. replace (negb (ds_match_available X4 =? 0)) with true in D by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact MA).
    destruct D as (SS1 & FOK & S2).
    unfold st_decide in RM, KC, KR. rewrite DC in RM, KC, KR.
    replace (negb (ds_match_available X4 =? 0)) with true in RM, KC, KR by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact MA).
    rewrite st_slit_eq in RM, KC, KR. cbv zeta in RM, KC, KR, S2. cbn [fst snd] in RM, KC, KR.
    pose proof (SCFGg_SF _ _ _ (SF_slit1 X4) C) as C1.
    (* [comment removed for export] *)
    assert (LT : forall Y, SCFGg inp Y -> 0 <= ds_strstart Y -> 1 <= ds_lookahead Y -> ds_strstart Y + ds_lookahead Y <= 2 * 32768 ->
              ROOM (ltail_st Y) ->
              ((if cs_avail_out (ds_strm (ltail_st Y)) =? 0 then LRet need_more else LCont) = LCont -> SKq Q Z_SLOW_HEAD (ltail_st Y)) ->
              (forall bs, (if cs_avail_out (ds_strm (ltail_st Y)) =? 0 then LRet need_more else LCont) = LRet bs -> SKr Q (bs_code bs) (ltail_st Y)) ->
              SKq Q Z_SLOW_LTAIL Y).
    { intros Y CY Y1 Y2 Y3 RY KCY KRY. apply (slow_ltail L flush inp rest0 lo r fj F fc me CTX Q Y); [lia| lia| exact (g_aout _ _ CY)| |].
      - intros A0. replace (cs_avail_out (ds_strm (ltail_st Y))) with (cs_avail_out (ds_strm Y)) in KRY by reflexivity.
        rewrite A0 in KRY. exact (KRY need_more eq_refl).
      - intros A0. replace (cs_avail_out (ds_strm (ltail_st Y))) with (cs_avail_out (ds_strm Y)) in KCY by reflexivity.
        replace (cs_avail_out (ds_strm Y) =? 0) with false in KCY by (symmetry; apply Z.eqb_neq; exact A0). exact (KCY eq_refl). }
    intros until m'. intros SI.
    eapply (slow_tlit L flush inp rest0 lo r fj F fc me CTX Q X4); [exact SI| exact SV| exact SS1| lia| exact Cws| exact Clbs| |].
    + intros B. apply Z.eqb_neq in B. rewrite B in RM, KC, KR, S2. destruct S2 as (Y1 & Y2 & Y3).
      apply LT; [exact C1| exact Y1| exact Y2| exact Y3| exact RM| exact KC| exact KR].
    + intros B. apply Z.eqb_eq in B. pose proof (FEL DC MA B) as FE. rewrite B in RM, KC, KR, S2. destruct S2 as (Y1 & Y2 & Y3). specialize (FOK B).
      pose proof (SCFGg_fbo _ _ _ C1 FOK) as CF.
      intros until m'0. intros SI'.
      eapply (slow_fbB L flush inp rest0 lo r fj F fc me CTX HTFBLK HTFB Q); [exact SI'| exact FOK| exact FE| exact (g_lbs _ _ C1)| exact (g_ws _ _ C1)| exact (g_aout _ _ C1)| |].
      * apply room_OUTg. destruct RM as [RM]. constructor. rewrite (OUT_SF _ _ (SF_ltail_st _)) in RM. exact RM.
      * apply LT; [exact CF| exact Y1| exact Y2| exact Y3| exact RM| exact KC| exact KR].
  - (* [comment removed for export] *)
    intros DC MA. unfold st_decide in RM, KC, KR. rewrite DC in RM, KC, KR.
    replace (negb (ds_match_available X4 =? 0)) with false in RM, KC, KR by (symmetry; apply negb_false_iff; apply Z.eqb_eq; exact MA).
    rewrite st_avail_eq in RM, KC, KR. cbn [fst snd] in RM, KC, KR.
    apply (slow_avail L flush inp rest0 lo r fj F fc me CTX Q X4); [lia| lia| exact (KC eq_refl)].
Qed.

(* [comment removed for export] *)
Lemma slow_tripg : forall (Q : machine_state -> Prop) (X : deflate_state),
  SCFGg inp X -> strip_ok 32768 32768 X flush -> - 2 ^ 62 <= ds_block_start X < 2 ^ 62 -> strip_fe X flush -> ROOM (fst (st_sbody X flush)) ->
  (snd (st_sbody X flush) = LCont -> SKq Q Z_SLOW_HEAD (fst (st_sbody X flush))) ->
  (snd (st_sbody X flush) = LBreak -> SKq Q Z_SLOW_TAIL (fst (st_sbody X flush))) ->
  (forall bs, snd (st_sbody X flush) = LRet bs -> SKr Q (bs_code bs) (fst (st_sbody X flush))) ->
  SKq Q Z_SLOW_HEAD X.
Proof.
  intros Q X C TOK RBS SFE RM KC KB KR. pose proof TOK as (_ & FW & _ & HOK). unfold strip_fe in SFE.
  destruct (fill_frameg inp X flush C FW) as [CF1 _].
  pose proof C as [Cws Chs Clbs Cwrap Cwrap0 Cwrng Cain Caout Ctie].
  unfold SK. intros until m'. intros SI.
  eapply (slow_fillg L flush inp rest0 lo r fj F fc me CTX HFW Q X); [exact SI| exact TOK| exact HFL| exact Cwrap| exact Cain| exact Ctie| exact RBS| | | |].
  - (* [comment removed for export] *)
    intros X1 EF.
    assert (ES : st_sbody X flush = (X1, LRet need_more)) by (unfold st_sbody; rewrite EF; reflexivity).
    rewrite ES in KR. rewrite fst_pr, snd_pr in KR. exact (KR need_more eq_refl).
  - (* [comment removed for export] *)
    intros X1 EF.
    assert (ES : st_sbody X flush = (X1, LBreak)) by (unfold st_sbody; rewrite EF; reflexivity).
    rewrite ES in KB. rewrite fst_pr, snd_pr in KB. exact (KB eq_refl).
  - (* [comment removed for export] *)
    intros X1 EF LA3.
    assert (ES : st_sbody X flush = st_srest X1) by (unfold st_sbody; rewrite EF; reflexivity).
    rewrite (st_srest_hi X1 LA3) in ES. rewrite ES in RM, KC, KR. clear ES KB.
    rewrite EF in HOK, CF1, SFE. rewrite fst_pr in CF1. rewrite fst_pr, snd_pr in HOK, SFE.
    destruct (shash_ok_hi _ _ (HOK eq_refl) LA3) as (SV1 & RLA1 & LMOK & DOK). pose proof (shash_fe_hi _ (SFE eq_refl) LA3) as DFE.
    pose proof SV1 as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
    pose proof (SCFGg_SF _ _ _ (SF_hash_st X1) CF1) as CH.
    assert (E4 : SF (st_lm (hash_st X1) (hash_hh X1)) = SF X1) by (rewrite SF_st_lm; apply SF_hash_st).
    apply (slow_hash L flush inp rest0 lo r fj F fc me CTX Q X1 SV1 LA3 (g_ws _ _ CF1) (g_hs _ _ CF1)).
    apply (slow_lm L flush inp rest0 lo r fj F fc me CTX Q (hash_st X1) (hash_hh X1)).
    + exact Rml.
    + exact Rlazy.
    + exact (g_ws _ _ CH).
    + rewrite (g_ws _ _ CF1) in Rsl. unfold hash_st, RefDeflSlow2.ins_str. dsred. lia.
    + reflexivity.
    + unfold hash_hh. rewrite (g_hs _ _ CF1) in Rhb, Rhm.
      pose proof (update_hash_range X1 (ds_ins_h X1) (arr_get (ds_window X1) (ds_strstart X1 + 2)) ltac:(lia)) as RH.
      pose proof (Rhb (update_hash X1 (ds_ins_h X1) (arr_get (ds_window X1) (ds_strstart X1 + 2))) ltac:(lia)) as RHH. lia.
    + exact Rstrat.
    + exact LMOK.
    + exact (proj1 DOK).
    + apply slow_decg; [exact (SCFGg_SF _ _ _ E4 CF1)| exact DOK| exact DFE| exact RM| exact KC| exact KR].
  - (* [comment removed for export] *)
    intros X1 EF LA3.
    assert (ES : st_sbody X flush = st_srest X1) by (unfold st_sbody; rewrite EF; reflexivity).
    rewrite (st_srest_lo X1 LA3) in ES. rewrite (st_lm_false _ 0 (sl_lm_cond_0 _)) in ES. rewrite ES in RM, KC, KR. clear ES KB.
    rewrite EF in HOK, CF1, SFE. rewrite fst_pr in CF1. rewrite fst_pr, snd_pr in HOK, SFE.
    destruct (shash_ok_lo _ _ (HOK eq_refl) LA3) as (_ & _ & _ & DOK). rewrite (st_lm_false _ 0 (sl_lm_cond_0 _)) in DOK.
    pose proof (shash_fe_lo _ (SFE eq_refl) LA3) as DFE. rewrite (st_lm_false _ 0 (sl_lm_cond_0 _)) in DFE.
    apply slow_decg; [exact (SCFGg_SF _ _ _ (SF_prev_st X1) CF1)| exact DOK| exact DFE| exact RM| exact KC| exact KR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma slow_tail2g : forall (Q : machine_state -> Prop) (Y : deflate_state),
  0 <= ds_strstart Y <= 65536 ->
  (flush = Z_FINISH -> forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
     SINV L flush rest0 lo r fj me (tail_st Y) m' ->
     evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart (tail_st Y))) y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a858) fc None m' (seg_rom usegs))) ->
  (flush <> Z_FINISH -> forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
     SINV L flush rest0 lo r fj me (tail_st Y) m' ->
     evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart (tail_st Y))) y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a898) fc None m' (seg_rom usegs))) ->
  SKq Q 0x1a838 Y.
Proof.
  intros Q Y Rss HK HKD. unfold SK. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU. unfold Z_FINISH in HK, HKD.
  name_mem mA.
  pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. zstep. zstep. zstep.
  eapply (evt_cut usegs (fun ms' => ms' = MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart Y)) (wz (if ds_strstart Y <? 2 then ds_strstart Y else 2)) (wz 2)
                                                  y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a84c) fc None mA (seg_rom usegs))).
  { if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    - apply evt_done. unfold slowR. replace (ds_strstart Y <? 2) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - zstep. apply evt_done. unfold slowR. replace (ds_strstart Y <? 2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  intros ms' ->. unfold slowR.
  assert (Rins : 0 <= (if ds_strstart Y <? 2 then ds_strstart Y else 2) <= 2) by (destruct (Z.ltb_spec (ds_strstart Y) 2); lia).
  zstep. zs. name_mem mB. zstep.
  assert (SI : SINV L flush rest0 lo r fj me (tail_st Y) mB).
  { tr_groups MUf WMf.
    split; [split|].
    - exact ZS.
    - unfold tail_st. change (MIN_MATCH - 1) with 2. constructor; [do 5 eexists; exact GA | exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  replace (wz (ds_strstart Y)) with (wz (ds_strstart (tail_st Y))) by reflexivity.
  if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia.
  - eapply (HKD ltac:(lia)). exact SI.
  - eapply (HK ltac:(lia)). exact SI.
Qed.

(* [comment removed for export] *)
Lemma slow_symD : forall (Q : machine_state -> Prop) (Z1 : deflate_state),
  0 <= ds_sym_next Z1 < 2^31 ->
  (ds_sym_next Z1 = 0 -> SKr Q 1 Z1) ->
  (ds_sym_next Z1 <> 0 -> forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
     SINV L flush rest0 lo r fj me Z1 m' ->
     evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart Z1)) y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a8a0) fc None m' (seg_rom usegs))) ->
  forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me Z1 m' ->
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart Z1)) y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a898) fc None m' (seg_rom usegs)).
Proof.
  intros Q Z1 Rsn K0 KD. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [_ ST]. destruct ST as [GA _ _ GD _ _ _ _ _ _ _ _ _ _ _ LAY1]. open_D GD. unfold slowR.
  zs. zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia.
  - (* [comment removed for export] *)
    zstep. unfold SKret, Z_SLOW_EPI in K0. eapply (K0 ltac:(lia)). exact SI.
  - eapply (KD ltac:(lia)). exact SI.
Qed.

(* [comment removed for export] *)
Lemma slow_finD : forall (Q : machine_state -> Prop) (Z0 : deflate_state),
  0 <= cs_avail_out (ds_strm Z0) < 2^31 ->
  SKr Q (if cs_avail_out (ds_strm Z0) =? 0 then 0 else 1) Z0 ->
  SKq Q 0x1a978 Z0.
Proof.
  intros Q Z0 Rao KR. unfold SK. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1].
  pose proof (sc_lay _ _ _ _ _ _ CTX) as LAY. lay_open LAY. pose proof (lo_S _ LAY) as BKS.
  open_zs ZS. open_A GA. unfold slowR. unfold SKret, Z_SLOW_EPI in KR.
  zs. gF. zstep. al8 (dl_S L). gF.
  zs. zstep. if_cases KAO; zify_cond KAO; rewrite ?unsigned_lit in KAO by lia.
  - replace (wz (cs_avail_out (ds_strm Z0))) with (wz (if cs_avail_out (ds_strm Z0) =? 0 then 0 else 1)) by (replace (cs_avail_out (ds_strm Z0) =? 0) with true by (symmetry; apply Z.eqb_eq; lia); f_equal; lia).
    eapply KR. exact SI.
  - zstep. replace (wz 1) with (wz (if cs_avail_out (ds_strm Z0) =? 0 then 0 else 1)) by (replace (cs_avail_out (ds_strm Z0) =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply KR. exact SI.
Qed.

(* [comment removed for export] *)
Lemma slow_tail1 : forall (Q : machine_state -> Prop) (X1 : deflate_state),
  0 <= ds_match_available X1 <= 1 ->
  (ds_match_available X1 = 0 -> SKq Q 0x1a838 X1) ->
  (ds_match_available X1 <> 0 -> SKq Q 0x1a758 X1) ->
  SKq Q Z_SLOW_TAIL X1.
Proof.
  intros Q X1 Rma K0 K1. unfold SK. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA. unfold slowR, Z_SLOW_TAIL. unfold SK, slowR in K0, K1.
  zs. zstep. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
  - eapply (K0 KM). exact SI.
  - eapply (K1 KM). exact SI.
Qed.

(* [comment removed for export] *)
Lemma slow_tailallg : forall (Q : machine_state -> Prop) (X1 : deflate_state),
  SCFGg inp X1 -> stail_ok 32768 X1 flush -> stail_fe X1 -> flush <> Z_NO_FLUSH -> ROOM (fst (slow_tailres X1 flush)) ->
  SKr Q (bs_code (snd (slow_tailres X1 flush))) (fst (slow_tailres X1 flush)) ->
  SKq Q Z_SLOW_TAIL X1.
Proof.
  intros Q X1 C (SV & RSS & MA1 & S2) TFE HNF RM KR.
  pose proof SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  pose proof C as [Cws Chs Clbs Cwrap Cwrap0 Cwrng Cain Caout Ctie].
  assert (ETL : slow_tailres X1 flush = deflate_tail (tail_st (if negb (ds_match_available X1 =? 0) then break1_st X1 else X1)) flush) by reflexivity.
  rewrite ETL in RM, KR. clear ETL. cbv zeta in S2.
  (* [comment removed for export] *)
  assert (T2 : forall s2, s2 = (if negb (ds_match_available X1 =? 0) then break1_st X1 else X1) -> SCFGg inp s2 -> SKq Q 0x1a838 s2).
  { intros s2 E2 C2. unfold stail_fe in TFE. rewrite <- E2 in RM, KR, S2, TFE. clear E2. destruct S2 as (RS2 & RSN & FOK & FOKD).
    assert (CT : ds_lit_bufsize (tail_st s2) = 16384 /\ ds_w_size (tail_st s2) = 32768 /\ 0 <= cs_avail_out (ds_strm (tail_st s2)) < 2^31)
      by (split; [exact (g_lbs _ _ C2)| split; [exact (g_ws _ _ C2)| exact (g_aout _ _ C2)]]).
    destruct CT as (CT1 & CT2 & CT3).
    apply (slow_tail2g Q s2); [lia| |].
    - (* [comment removed for export] *)
      intros HF. specialize (FOK HF). pose proof (TFE 1 ltac:(lia)) as FE.
      replace (deflate_tail (tail_st s2) flush) with (deflate_tail (tail_st s2) Z_FINISH) in RM, KR by (rewrite HF; reflexivity).
      rewrite deflate_tail_finish_eq in RM, KR. rewrite fst_pr in RM, KR. rewrite snd_pr in KR.
      intros until m'. intros SI.
      eapply (slow_fbC L flush inp rest0 lo r fj F fc me CTX HTFBLK HTFB Q); [exact SI| exact FOK| exact FE| exact CT1| exact CT2| exact CT3| exact (room_OUTg _ RM)|].
      assert (WF : ds_wrap (flush_block_only (tail_st s2) 1) = ds_wrap s2) by (rewrite fbo_wrap; reflexivity).
      apply (slow_fin L flush inp rest0 lo r fj F fc me CTX); [| rewrite WF; exact (g_nraw _ _ C2)| rewrite WF; pose proof (g_wrng _ _ C2); lia|].
      2:{ destruct (cs_avail_out (ds_strm (flush_block_only (tail_st s2) 1)) =? 0); exact KR. }
      pose proof (fbo_avail_out (tail_st s2) 1 FOK CT1 CT3). lia.
    - (* [comment removed for export] *)
      intros NF. specialize (FOKD NF). rewrite (deflate_tail_nf_eq (tail_st s2) flush NF) in RM, KR.
      apply slow_symD; [cbn [ds_sym_next tail_st set_insert]; clear - RSN; lia| |].
      + intros S0. replace (ds_sym_next (tail_st s2) =? 0) with true in KR by (symmetry; apply Z.eqb_eq; exact S0). cbn [negb] in KR.
        rewrite fst_pr, snd_pr in KR. exact KR.
      + intros S1. specialize (FOKD S1). pose proof (TFE 0 ltac:(lia)) as FE.
        replace (ds_sym_next (tail_st s2) =? 0) with false in RM, KR by (symmetry; apply Z.eqb_neq; exact S1). cbn [negb] in RM, KR.
        rewrite fst_pr in RM, KR. rewrite snd_pr in KR.
        intros until m'. intros SI.
        eapply (slow_fbD L flush inp rest0 lo r fj F fc me CTX HTFBLK HTFB Q); [exact SI| exact FOKD| exact FE| exact CT1| exact CT2| exact CT3| exact (room_OUTg _ RM)|].
        apply slow_finD; [|].
        2:{ destruct (cs_avail_out (ds_strm (flush_block_only (tail_st s2) 0)) =? 0); exact KR. }
        pose proof (fbo_avail_out (tail_st s2) 0 FOKD CT1 CT3). lia. }
  apply slow_tail1; [exact Rma| |].
  - intros M0. apply T2; [|exact C]. replace (ds_match_available X1 =? 0) with true by (symmetry; apply Z.eqb_eq; exact M0). reflexivity.
  - intros M1. specialize (MA1 M1). rewrite Cws in Rsl.
    intros until m'. intros SI.
    eapply (slow_tlitT L flush inp rest0 lo r fj F fc me CTX Q X1); [exact SI| exact SV| exact MA1| lia| exact Cws| exact Clbs|].
    apply T2; [|exact (SCFGg_SF _ _ _ (SF_break1_st X1) C)].
    replace (ds_match_available X1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact M1). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma slow_loopg : forall (f : nat) (X : deflate_state),
  SCFGg inp X -> sloop_ok 32768 32768 f X flush -> tail_safe flush f X -> ROOM (fst (slow_res flush f X)) -> sbs_ok f X flush ->
  sloop_fe f X flush -> tail_fe flush f X ->
  SKq (slow_post_gen r F fc L (fst (slow_res flush f X)) (bs_code (snd (slow_res flush f X))) inp rest0 lo me) Z_SLOW_HEAD X.
Proof.
  induction f as [|f IH]; intros X C LOK TS RM SBS LFE TFE; [destruct LOK|].
  rewrite sloop_ok_S in LOK. destruct LOK as [TOK LOK]. rewrite tail_safe_S in TS. rewrite sbs_ok_S in SBS. destruct SBS as [RBS SBS].
  rewrite sloop_fe_S in LFE. destruct LFE as [SFE LFE]. rewrite tail_fe_S in TFE.
  destruct (sbody_frameg inp X flush C TOK) as [C' O'].
  rewrite slow_res_S in RM |- *.
  remember (snd (st_sbody X flush)) as o eqn:ES. symmetry in ES. destruct o as [| |bs].
  - (* [comment removed for export] *)
    apply slow_tripg; [exact C| exact TOK| exact RBS| exact SFE| | | |].
    + destruct RM as [RM]. constructor. eapply Nat.le_trans; [apply (OUT_resg inp flush f _ C' LOK)| exact RM].
    + intros _. apply IH; assumption.
    + intros E'. rewrite ES in E'. discriminate.
    + intros bs E'. rewrite ES in E'. discriminate.
  - (* [comment removed for export] *)
    pose proof (sbody_break_flush X flush ES) as HNF.
    apply slow_tripg; [exact C| exact TOK| exact RBS| exact SFE| | | |].
    + destruct RM as [RM]. constructor. eapply Nat.le_trans; [apply OUT_tailres| exact RM].
    + intros E'. rewrite ES in E'. discriminate.
    + intros _. apply slow_tailallg; [exact C'| exact TS| exact TFE| exact HNF| exact RM|]. apply (slow_epi L flush inp rest0 lo r fj F fc me CTX).
    + intros bs E'. rewrite ES in E'. discriminate.
  - (* [comment removed for export] *)
    rewrite fst_pr, snd_pr. rewrite fst_pr in RM.
    apply slow_tripg; [exact C| exact TOK| exact RBS| exact SFE| exact RM| | |].
    + intros E'. rewrite ES in E'. discriminate.
    + intros E'. rewrite ES in E'. discriminate.
    + intros bs' E'. rewrite ES in E'. injection E' as <-. apply (slow_epi L flush inp rest0 lo r fj F fc me CTX).
Qed.
End SLOWG.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem deflate_slow_specg : fill_window_stmtg -> tr_flush_block_stmtE -> tr_flush_bits_stmt -> deflate_slow_stmtg.
Proof.
  intros HFW HTFBLK HTFB. unfold deflate_slow_stmtg.
  intros until m. intros DR DIN TIE DOUT MI RELRO STK LO SP16 BEL IO SAFE HFL WS HS LBS WRAP WRAP0 WRNG AIN RAO ROOM SBS [LFE TFE] -> ->.
  unfold Z_DEFLATE_SLOW.
  set (r := mkSR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  pose proof (st_lay _ _ _ _ (proj2 DR)) as LAY.
  assert (CTX : slow_ctx L inp rest0 lo r m) by (constructor; assumption).
  destruct SAFE as (DW & LOK & TSAFE). rewrite WS, HS in LOK. rewrite WS in TSAFE.
  assert (C : SCFGg inp d) by (constructor; assumption).
  rewrite deflate_slow_res in ROOM.
  (* [comment removed for export] *)
  lay_open LAY. pose proof BEL as BEL0. below_open BEL0. pose proof IO as I0. io_open I0. unfold Z_SLOW_STACK in LO.
  pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof HFL as HFL'. unfold Z_NO_FLUSH, Z_FINISH in HFL'.
  pose proof (munch_refl (slow_W L rest0 lo r) m) as MU. unfold slow_W in MU. cbn [r_sp r] in MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  carve_frame 128%nat STK.
  do 14 zs.
  gF. zs. zstep. al8 (dl_As L). gF. zs.
  do 19 zs.
  rewrite ?(zb_lxor_ones (dl_As L + 212)) by lia. rewrite ?(zb_lxor_ones (dl_As L + 2047 + 457)) by lia. rewrite ?(zb_lxor_ones (dl_As L + 2504)) by lia.
  name_mem mP.
  replace (wz (-1)) with (wz 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
  replace (wz (dl_As L + 2047 + 457)) with (wz (dl_As L + 2504)) by (f_equal; lia).
  replace (wz (18446744073709551615 - (dl_As L + 2047 + 457))) with (wz (18446744073709551615 - (dl_As L + 2504))) by (f_equal; lia).
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?x :: _) => set (fj := x) in FR end.
  assert (RM0 : Box (OUT (fst (slow_res flush (lz_fuel d) d)) <= length rest0)%nat) by (constructor; exact ROOM).
  assert (RMd : Box (length (cs_out_rev (ds_strm d)) <= length rest0)%nat).
  { constructor. eapply Nat.le_trans; [apply (OUT_resg inp flush (lz_fuel d) d C LOK)| exact ROOM]. }
  assert (SI : SINV L flush rest0 lo r fj m d mP).
  { split.
    { apply (DREP_agree m mP L d DR).
      - eapply ag_blocks_munch; [exact LAY| exact MUf| exact WMf| | | | |]; cbn [disjoint_from]; slia.
      - apply (agree_on_of_munch [(lo, bv_unsigned sp)]); [exact MUf| exact WMf| lia| lia| cbn [disjoint_from]; slia]. }
    split; [apply (dout_munch _ m mP L rest0 _ DOUT RMd MUf WMf); cbn [disjoint_from]; slia|].
    split; [exact RMd|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  eapply evt_mono.
  { eapply (slow_loopg L flush inp rest0 lo r fj F fc m CTX HFW HTFBLK HTFB HFL (lz_fuel d) d C LOK TSAFE RM0 SBS LFE TFE). exact SI. }
  intros ms' P. unfold deflate_slow_post. rewrite deflate_slow_res. exact P.
Qed.
