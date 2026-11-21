(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_adler32 Zg_adler32_iface Zg_defl_iface Zg_sto_model Zg_sto_ole Zg_sto_kit Zg_sto_loop Zg_sto_used Zg_sto_fill Zg_sto_read2 Zg_sto_fin.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 RefDeflStored9 RefDeflSafeS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation OL s := (length (cs_out_rev (ds_strm s))).

Definition sto_s2 (ai0 : Z) (sL : deflate_state) : deflate_state :=
  hw_st (st_wupd sL (ai0 - cs_avail_in (ds_strm sL))).

Definition sto_cond (flush : Z) (s2 : deflate_state) : bool :=
  negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (cs_avail_in (ds_strm s2) =? 0) && (ds_strstart s2 =? ds_block_start s2).

Definition sto_s4 (s2 : deflate_state) : deflate_state :=
  hw_st (st_fillw (fst (st_slide3 s2 (ds_window_size s2 - ds_strstart s2)))
                  (fmin (snd (st_slide3 s2 (ds_window_size s2 - ds_strstart s2)))
                        (cs_avail_in (ds_strm (fst (st_slide3 s2 (ds_window_size s2 - ds_strstart s2))))))).

Definition sto_tail (flush ai0 : Z) (sL : deflate_state) (last : Z) : deflate_state * block_state :=
  if negb (last =? 0) then (sto_s2 ai0 sL, finish_done)
  else if sto_cond flush (sto_s2 ai0 sL) then (sto_s2 ai0 sL, block_done)
  else st_final (sto_s4 (sto_s2 ai0 sL)) flush.

Lemma tail_fd : forall flush ai0 sL last, last = 1 -> sto_tail flush ai0 sL last = (sto_s2 ai0 sL, finish_done).
Proof. intros flush ai0 sL last ->. reflexivity. Qed.

Lemma tail_bd : forall flush ai0 sL last s2, s2 = sto_s2 ai0 sL -> last = 0 ->
  flush <> Z_NO_FLUSH -> flush <> Z_FINISH -> cs_avail_in (ds_strm s2) = 0 -> ds_strstart s2 = ds_block_start s2 ->
  sto_tail flush ai0 sL last = (s2, block_done).
Proof.
  intros flush ai0 sL last s2 E2 -> NF1 NF2 HAI HSB. unfold sto_tail. change (negb (0 =? 0)) with false. cbv iota.
  rewrite <- E2. unfold sto_cond. rewrite HAI, HSB, Z.eqb_refl, Z.eqb_refl.
  replace (flush =? Z_NO_FLUSH) with false by (symmetry; apply Z.eqb_neq; exact NF1).
  replace (flush =? Z_FINISH) with false by (symmetry; apply Z.eqb_neq; exact NF2).
  reflexivity.
Qed.

Lemma tail_fill : forall flush ai0 sL last s2, s2 = sto_s2 ai0 sL -> last = 0 -> sto_cond flush s2 = false ->
  sto_tail flush ai0 sL last = st_final (sto_s4 s2) flush.
Proof.
  intros flush ai0 sL last s2 E2 -> HC. unfold sto_tail. change (negb (0 =? 0)) with false. cbv iota.
  rewrite <- E2, HC. reflexivity.
Qed.

Lemma wrap_st_wupd : forall s u, ds_wrap (st_wupd s u) = ds_wrap s.
Proof.
  intros s u. unfold st_wupd.
  destruct (negb (u =? 0)); [| reflexivity].
  destruct (ds_w_size s <=? u); [dsred; reflexivity|].
  destruct (ds_window_size s - ds_strstart s <=? u); cbv zeta; dsred; [| reflexivity].
  destruct (ds_matches _ <? 2); dsred; destruct (_ <? ds_insert _); dsred; reflexivity.
Qed.

Lemma wrap_hw_st : forall s, ds_wrap (hw_st s) = ds_wrap s.
Proof. intros s. unfold hw_st. destruct (_ <? _); dsred; reflexivity. Qed.

Lemma wrap_st_slide3 : forall s h, ds_wrap (fst (st_slide3 s h)) = ds_wrap s.
Proof.
  intros s h. unfold st_slide3.
  destruct ((h <? cs_avail_in (ds_strm s)) && (ds_w_size s <=? ds_block_start s)); [| rewrite fst_pr; reflexivity].
  cbv zeta. rewrite fst_pr.
  destruct (ds_matches _ <? 2); dsred; destruct (_ <? ds_insert _); dsred; reflexivity.
Qed.

Lemma ai_hw_fillw : forall s n, 0 <= n <= cs_avail_in (ds_strm s) ->
  cs_avail_in (ds_strm (hw_st (st_fillw s n))) <= cs_avail_in (ds_strm s).
Proof.
  intros s n Hn. destruct (hw_st_facts (st_fillw s n)) as (_ & _ & E & _). rewrite E.
  destruct (Z.eq_dec n 0) as [-> |Hnz]; [rewrite st_fillw_0; lia|].
  rewrite (st_fillw_eq s s n eq_refl ltac:(lia)). unfold st_rbw, rbw_mid. cbv zeta.
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; dsred; lia.
Qed.

Lemma ole_tail : forall flush ai0 sL last, (OL sL <= OL (fst (sto_tail flush ai0 sL last)))%nat.
Proof.
  intros flush ai0 sL last. unfold sto_tail.
  destruct (negb (last =? 0)); [rewrite fst_pr; unfold sto_s2; rewrite ole_hw, ole_wupd; lia|].
  destruct (sto_cond flush (sto_s2 ai0 sL)); [rewrite fst_pr; unfold sto_s2; rewrite ole_hw, ole_wupd; lia|].
  eapply Nat.le_trans; [| apply ole_final]. unfold sto_s4, sto_s2. rewrite ole_hw, ole_fillw, ole_slide3, ole_hw, ole_wupd. lia.
Qed.

Lemma deflate_stored_tail : forall X flush, st_entry X -> ds_w_size X = 32768 -> ds_pending_buf_size X = 65536 ->
  deflate_stored X flush
  = sto_tail flush (cs_avail_in (ds_strm X))
      (fst (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768))
      (snd (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768)).
Proof.
  intros X flush SE WS PBS. pose proof SE as [HV Hp Hpo Hbb Hpbs Hao]. pose proof (vi_ai _ HV) as Vai. pose proof (vi_ni _ HV) as Vni.
  rewrite deflate_stored_eq. cbv zeta.
  replace (wrap32 (MIN (ds_pending_buf_size X - 5) (ds_w_size X))) with 32768 by (rewrite PBS, WS; reflexivity).
  destruct (loop_TI (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768 SE ltac:(rewrite WS; lia) ltac:(lia)) as [_ R]. cbv zeta in R.
  revert R.
  generalize (snd (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768)) as last.
  generalize (fst (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768)) as sL.
  intros sL last (HTL & SL & BSL & INL & ANL & AIL & AOL & OLL & Hlast & BVL).
  pose proof HTL as [HVL HpL HpoL HbbL HpbsL HaoL]. pose proof SL as (W1 & W2 & W3 & W4 & _). dsred in W4.
  replace (wrap32 (cs_avail_in (ds_strm X) - cs_avail_in (ds_strm sL))) with (cs_avail_in (ds_strm X) - cs_avail_in (ds_strm sL))
    by (rewrite wrap32_mod; symmetry; apply Z.mod_small; lia).
  unfold sto_tail, sto_s2, sto_cond, sto_s4.
  destruct (wupd_so_inv sL (cs_avail_in (ds_strm X) - cs_avail_in (ds_strm sL)) HVL ltac:(rewrite W4; lia) ltac:(lia)) as (HV1 & B1 & ST1 & WS1).
  destruct (hw_st_so_inv (st_wupd sL (cs_avail_in (ds_strm X) - cs_avail_in (ds_strm sL))) HV1 ltac:(rewrite WS1, W4; lia))
    as (HV2 & B2 & ST2 & STR2 & BS2 & WSZ2 & WS2).
  revert HV2 WS2. generalize (hw_st (st_wupd sL (cs_avail_in (ds_strm X) - cs_avail_in (ds_strm sL)))). intros s2 HV2 WS2.
  pose proof (vi_str _ HV2) as Vstr2. pose proof (vi_bs _ HV2) as Vbs2. pose proof (vi_wsz _ HV2) as Vwsz2.
  replace (wrap32 (ds_window_size s2 - ds_strstart s2)) with (ds_window_size s2 - ds_strstart s2)
    by (rewrite wrap32_mod; symmetry; apply Z.mod_small; rewrite Vwsz2; rewrite WS2, WS1, W4, WS in *; lia).
  reflexivity.
Qed.

Section BODY.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.
Hypothesis HTSB : tr_stored_block_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HADL : adler32_stmt.
Lemma sto_body : forall (X : deflate_state),
  st_entry X -> ds_w_size X = 32768 -> ds_lit_bufsize X = 16384 -> ds_pending_buf_size X = 65536 -> ds_wrap X <> 2 ->
  din_tie inp X -> cs_avail_in (ds_strm X) < 2^31 -> cs_avail_out (ds_strm X) < 2^31 -> ai0 = cs_avail_in (ds_strm X) ->
  Box (length (cs_out_rev (ds_strm (fst (deflate_stored X flush)))) <= length rest0)%nat ->
  TK L flush ai0 1 rest0 lo r F fc me
     (slow_post_gen r F fc L (fst (deflate_stored X flush)) (bs_code (snd (deflate_stored X flush))) inp rest0 lo me) Z_STO_HEAD X.
Proof.
  intros X SE WS LBS PBS WRAP [INP TIEB] AI AO Eai RM.
  rewrite (deflate_stored_tail X flush SE WS PBS) in RM |- *. rewrite <- Eai in RM |- *.
  pose proof SE as [HV Hp Hpo Hbb Hpbs Hao]. pose proof (vi_ai _ HV) as Vai. pose proof (vi_ni _ HV) as Vni.
  assert (TSX : TS inp X) by (constructor; [exact SE| exact WS| exact LBS| exact WRAP| exact INP| exact AI| exact AO]).
  destruct (loop_TI (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768 SE ltac:(rewrite WS; lia) ltac:(lia)) as [_ R]. cbv zeta in R.
  (* 1.4: the loop breaks at 0x18348 or at 0x1836c; both continue as sto_used / sto_used2 into one LASTT fact (KT) *)
  assert (KBOTH : forall pc0, pc0 = Z_STO_BREAK \/ pc0 = Z_STO_BREAK2 ->
    TK10 L flush ai0 (1 - snd (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768)) rest0 lo r F fc me
      (slow_post_gen r F fc L
         (fst (sto_tail flush ai0 (fst (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768))
                                  (snd (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768))))
         (bs_code (snd (sto_tail flush ai0 (fst (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768))
                                           (snd (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768)))))
         inp rest0 lo me)
      pc0 (dl_S L) (fst (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768))).
  2:{ refine (sto_loop L flush ai0 inp rest0 lo r F fc me CTX HFL HTSB HTFB HADL TIEB (Z.to_nat (cs_avail_out (ds_strm X) + 1)) _ X TSX ltac:(lia) _
                (KBOTH _ (or_introl eq_refl)) (KBOTH _ (or_intror eq_refl))).
      constructor. eapply Nat.le_trans; [apply ole_tail| exact (unbox _ RM)]. }
  intros pc0 HPC.
  revert R RM.
  generalize (snd (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768)) as last.
  generalize (fst (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm X) + 1)) X flush 32768)) as sL.
  intros sL last (HTL & SL & BSL & INL & ANL & AIL & AOL & OLL & Hlast & BVL) RM.
  pose proof HTL as [HVL HpL HpoL HbbL HpbsL HaoL].
  pose proof SL as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12). dsred in W2. dsred in W3. dsred in W4. dsred in W11.
  pose proof (vi_ai _ HVL) as VaiL.
  assert (WSL : ds_w_size sL = 32768) by (rewrite W4; exact WS).
  assert (INPL : cs_input (ds_strm sL) = arr_of_list inp) by (rewrite INL; exact INP).
  assert (RAI0 : 0 <= ai0 < 2^31) by (rewrite Eai; clear - Vai AI; lia).
  assert (RAIL : 0 <= cs_avail_in (ds_strm sL) <= ai0) by (rewrite Eai; exact AIL).
  assert (RUNI : ai0 - cs_avail_in (ds_strm sL) <= cs_next_in (ds_strm sL)) by (rewrite Eai; clear - ANL Vni; lia).
  match goal with |- TK10 _ _ _ _ _ _ _ _ _ _ ?QQ _ _ _ =>
    assert (KT : TK11 L flush ai0 (1 - last) rest0 lo r F fc me QQ Z_STO_LASTT (hw_st (st_wupd sL (ai0 - cs_avail_in (ds_strm sL))))) end.
  2:{ destruct HPC as [-> | ->].
      - exact (sto_used L flush ai0 inp rest0 lo r F fc me CTX _ (1 - last) sL HVL WSL INPL RAI0 RAIL RUNI KT).
      - exact (sto_used2 L flush ai0 inp rest0 lo r F fc me CTX _ (1 - last) sL HVL WSL INPL RAI0 RAIL RUNI KT). }

  destruct (wupd_so_inv sL (ai0 - cs_avail_in (ds_strm sL)) HVL ltac:(rewrite WSL; lia) ltac:(clear - RAIL RUNI; lia)) as (HV1 & B1 & ST1 & WS1).
  pose proof (wrap_st_wupd sL (ai0 - cs_avail_in (ds_strm sL))) as WR1.
  destruct (hw_st_so_inv (st_wupd sL (ai0 - cs_avail_in (ds_strm sL))) HV1 ltac:(rewrite WS1, WSL; lia)) as (HV2 & B2 & ST2 & STR2 & BS2 & WSZ2 & WS2).
  pose proof (wrap_hw_st (st_wupd sL (ai0 - cs_avail_in (ds_strm sL)))) as WR2.
  assert (HX2 : exists s2, s2 = sto_s2 ai0 sL) by (eexists; reflexivity). destruct HX2 as [s2 E2]. unfold sto_s2 in E2.
  rewrite <- E2 in HV2, B2, ST2, STR2, BS2, WSZ2, WS2, WR2 |- *.
  pose proof (vi_str _ HV2) as Vstr2. pose proof (vi_bs _ HV2) as Vbs2. pose proof (vi_wsz _ HV2) as Vwsz2. pose proof (vi_ai _ HV2) as Vai2.
  assert (WS2' : ds_w_size s2 = 32768) by (rewrite WS2, WS1; exact WSL).
  assert (ST2' : ds_strm s2 = ds_strm sL) by (rewrite ST2; exact ST1).
  assert (RAI2 : 0 <= cs_avail_in (ds_strm s2) < 2^31) by (rewrite ST2'; clear - RAIL RAI0; lia).
  refine (sto_lastt L flush ai0 inp rest0 lo r F fc me CTX HFL _ (1 - last) last s2 eq_refl Hlast
            ltac:(clear - Vstr2 Vbs2 WS2'; lia) RAI2 ltac:(clear - Vstr2 Vbs2 WS2'; lia) _ _ _).
  -
    intros Hl1. rewrite (tail_fd flush ai0 sL last Hl1). rewrite fst_pr, snd_pr. unfold sto_s2. rewrite <- E2.
    change (bs_code finish_done) with 3. exact (sto_epi_bu L flush ai0 inp rest0 lo r F fc me CTX (1 - last) s2 3).
  -
    intros Hl0 NF1 NF2 HAI HSB. rewrite (tail_bd flush ai0 sL last s2 E2 Hl0 NF1 NF2 HAI HSB). rewrite fst_pr, snd_pr.
    change (bs_code block_done) with 1. exact (sto_epi L flush ai0 inp rest0 lo r F fc me CTX (1 - last) s2 1).
  -
    intros Hl0 HC. change ((negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (cs_avail_in (ds_strm s2) =? 0) && (ds_strstart s2 =? ds_block_start s2)) = false)
      with (sto_cond flush s2 = false) in HC.
    rewrite (tail_fill flush ai0 sL last s2 E2 Hl0 HC) in RM |- *.
    refine (sto_slide2 L flush ai0 inp rest0 lo r F fc me CTX _ s2 HV2 WS2' RAI2 _).

    destruct (slide3_so_inv s2 (ds_window_size s2 - ds_strstart s2) HV2 ltac:(rewrite WS2'; lia) ltac:(rewrite Vwsz2; reflexivity)) as (HV3 & B3 & ST3 & WS3 & Eh3 & Hh3).
    pose proof (wrap_st_slide3 s2 (ds_window_size s2 - ds_strstart s2)) as WR3.
    assert (HX3 : exists s3, s3 = fst (st_slide3 s2 (ds_window_size s2 - ds_strstart s2))) by (eexists; reflexivity). destruct HX3 as [s3 E3].
    assert (HXh : exists hv, hv = snd (st_slide3 s2 (ds_window_size s2 - ds_strstart s2))) by (eexists; reflexivity). destruct HXh as [hv Eh].
    unfold sto_s4 in RM |- *.
    rewrite <- E3 in HV3, B3, ST3, WS3, Eh3, WR3, RM |- *. rewrite <- Eh in Eh3, Hh3, RM |- *.
    pose proof (vi_ai _ HV3) as Vai3.
    assert (WS3' : ds_w_size s3 = 32768) by (rewrite WS3; exact WS2').
    assert (TIE3 : din_tie inp s3) by (split; [rewrite ST3, ST2'; exact INPL| exact TIEB]).
    assert (WRAP3 : ds_wrap s3 <> 2) by (rewrite WR3, WR2, WR1, W11; exact WRAP).
    assert (RAI3 : cs_avail_in (ds_strm s3) < 2^31) by (rewrite ST3; clear - RAI2; lia).
    assert (RHV3 : 0 <= hv /\ ds_strstart s3 + hv <= 65536) by (clear - Eh3 Hh3 WS3'; lia).
    refine (sto_read2 L flush ai0 inp rest0 lo r F fc me CTX HADL _ s3 hv HV3 TIE3 WS3' WRAP3 RAI3 RHV3 _).

    assert (Hfm : 0 <= fmin hv (cs_avail_in (ds_strm s3)) <= hv /\ fmin hv (cs_avail_in (ds_strm s3)) <= cs_avail_in (ds_strm s3)).
    { unfold fmin. destruct (Z.ltb_spec (cs_avail_in (ds_strm s3)) hv); clear - Hh3 Vai3 H; lia. }
    destruct (fillw_so_inv s3 (fmin hv (cs_avail_in (ds_strm s3))) HV3 ltac:(rewrite WS3'; lia) ltac:(clear - Hfm; lia) ltac:(clear - Hfm Eh3 WS3; lia)) as (HV4 & B4 & WS4).
    destruct (hw_st_so_inv (st_fillw s3 (fmin hv (cs_avail_in (ds_strm s3)))) HV4 ltac:(rewrite WS4, WS3'; lia)) as (HV5 & B5 & ST5 & _).
    assert (HX5 : exists s5, s5 = hw_st (st_fillw s3 (fmin hv (cs_avail_in (ds_strm s3))))) by (eexists; reflexivity). destruct HX5 as [s5 E5].
    rewrite <- E5 in HV5, B5, ST5, RM |- *.
    destruct B1 as (P1 & PO1 & BV1 & BB1 & LB1 & PBS1 & _ & AO1 & _).
    destruct B2 as (P2 & PO2 & BV2 & BB2 & LB2 & PBS2 & _ & AO2 & _).
    destruct B3 as (P3 & PO3 & BV3 & BB3 & LB3 & PBS3 & _ & AO3 & _).
    destruct B4 as (P4 & PO4 & BV4 & BB4 & LB4 & PBS4 & _ & AO4 & _).
    destruct B5 as (P5 & PO5 & BV5 & BB5 & LB5 & PB5 & WZ5 & AO5 & _).
    assert (LBS5 : ds_lit_bufsize s5 = 16384) by (rewrite LB5, LB4, LB3, LB2, LB1, W2; exact LBS).
    assert (PBS5 : ds_pending_buf_size s5 = 65536) by (rewrite PB5, PBS4, PBS3, PBS2, PBS1, W3; exact PBS).
    assert (WS5 : ds_w_size s5 = 32768) by (rewrite WZ5, WS4; exact WS3').
    assert (AO5' : cs_avail_out (ds_strm s5) = cs_avail_out (ds_strm sL)) by (rewrite AO5, AO4, AO3, AO2, AO1; reflexivity).
    assert (RAO5 : 0 <= cs_avail_out (ds_strm s5) < 2^31) by (rewrite AO5'; clear - AOL AO HaoL; lia).
    assert (RAI5 : cs_avail_in (ds_strm s5) < 2^31) by (rewrite E5; pose proof (ai_hw_fillw s3 (fmin hv (cs_avail_in (ds_strm s3))) ltac:(clear - Hfm; lia)); clear - RAI3 H; lia).
    assert (FOK5 : so_final_ok s5 flush).
    { apply final_ok_intro; [exact HV5| rewrite LBS5; lia| | | | |].
      - rewrite P5, P4, P3, P2, P1. exact HpL.
      - rewrite PO5, PO4, PO3, PO2, PO1. exact HpoL.
      - rewrite BB5, BB4, BB3, BB2, BB1. exact HbbL.
      - rewrite PBS5, LBS5. reflexivity.
      - clear - RAO5; lia. }
    exact (sto_final L flush ai0 inp rest0 lo r F fc me CTX HFL HTSB HTFB s5 HV5 WS5 PBS5 LBS5 RAI5 RAO5 FOK5 RM).
Qed.
End BODY.

Theorem deflate_stored_spec : tr_stored_block_stmt -> tr_flush_bits_stmt -> adler32_stmt -> deflate_stored_stmt.
Proof.
  intros HTSB HTFB HADL. unfold deflate_stored_stmt.
  intros until m. intros DR DIN TIE DOUT MI STK LO SP16 BEL IO SE HFL WS LBS PBS WRAP AIN RAO ROOM -> ->.
  unfold Z_DEFLATE_STORED.
  set (r := mkSR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  pose proof (st_lay _ _ _ _ (proj2 DR)) as LAY.
  assert (CTX : sto_ctx L inp rest0 lo r m) by (constructor; assumption).
  pose proof SE as [HV Hp Hpo Hbb Hpbs Hao]. pose proof (vi_ai _ HV) as Vai.

  assert (RMd : Box (length (cs_out_rev (ds_strm d)) <= length rest0)%nat).
  { constructor. pose proof ROOM as R0. rewrite (deflate_stored_tail d flush SE WS PBS) in R0.
    eapply Nat.le_trans; [| exact R0]. eapply Nat.le_trans. 2: apply ole_tail. apply ole_loop. }

  lay_open LAY. pose proof BEL as BEL0. below_open BEL0. pose proof IO as I0. io_open I0. unfold Z_STORED_STACK in LO.
  pose proof (munch_refl (sto_W L rest0 lo r) m) as MU. unfold sto_W, slow_W in MU. cbn [r_sp r] in MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof DR as [ZS ST]. open_DST ST. open_A GA. open_zs ZS.
  carve_frame 160%nat STK.
  (* 1.4: 13 saves; have = min(pending_buf_size - 5, w_size) in s10 (the bltu is not taken: 65531 >= 32768);
     then the frame flags (sp+8 avail_in, +16 1, +24 flush, +32 flush != 0, +40 have, +48 flush == 4; sp+0 unwritten),
     s7 = s10 = As + 5928, s8 = 0xffff, s9 = 0xfffe; j to the loop head *)
  do 14 zs. do 6 zs. zstep. br_false. do 19 zs. zstep. name_mem mP.
  (* 1.4: snez leaves flush != 0 as Z.b2z (0 <? flush), with no mod *)
  replace (Z.b2z (0 <? flush)) with (if flush =? 0 then 0 else 1) in FR
    by (destruct (Z.eqb_spec flush 0) as [E0|E0]; [subst flush; reflexivity| destruct (Z.ltb_spec 0 flush); [reflexivity| lia]]).
  rewrite (sto_c48 flush HFL), ?WS in FR.
  assert (SI : STOINV L flush (cs_avail_in (ds_strm d)) 1 rest0 lo r m d mP).
  { split.
    { apply (DREP_agree m mP L d DR).
      - eapply ag_blocks_munch; [exact LAY| exact MUf| exact WMf| | | | |]; cbn [disjoint_from]; slia.
      - apply (agree_on_of_munch [(lo, bv_unsigned sp)]); [exact MUf| exact WMf| lia| lia| cbn [disjoint_from]; slia]. }
    split; [apply (dout_munch _ m mP L rest0 _ DOUT RMd MUf WMf); cbn [disjoint_from]; slia|].
    split; [exact RMd|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  pose proof (sto_body L flush (cs_avail_in (ds_strm d)) inp rest0 lo r F fc m CTX HFL HTSB HTFB HADL d SE WS LBS PBS WRAP TIE AIN (proj2 RAO) eq_refl
                ltac:(constructor; exact ROOM)) as BODY.
  unfold TK in BODY.
  eapply evt_mono; [eapply BODY; exact SI|].
  intros ms' P. exact P.
Qed.
