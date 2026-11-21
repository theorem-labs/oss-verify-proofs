(** * CodesBuildRows -- res-t2 (TL fork, T2 program under the 09-15; q7 R2083 section 2 / R2085): the four model
    facts of an ACCEPTED 19/7 CODES build ([it_model CT_CODES lens 19 7 t0 = Some o], [o_ret o = 0], lens <= 7) that the ReachMode fields
    [rm_tblCL0 .. rm_tblCL3] need at every producer of a CODELENS state: [1 <= o_bits o] (CfgBitsTblLeaf.it_model_bits_pos),
    [2 ^ o_bits o <= o_used o] (GtUsedBits.used_ge_root_block) and the op range [0 <= c_op (o_tbl o i) < 256] below [2 ^ o_bits o]
    (TieBStageCModel.cbr_codes_tbl_entries :529). The op range's home sits ABOVE StepPres and TieBPayLG (TieBStageCModel -> TieBBridgeL ->
    TieBPayLG), so its chain is COPIED here VERBATIM from the tree of record (4140): the range walk cbr_tr_here / cbr_tr_fill / cbr_tr_step / cbr_tr_loop /
    cbr_tr_model (TieBStageCModel :428-:527; every write of inflate_table is a mkCodeT, GtTblRange.mkCodeT_in_range) and the seed genericity
    cbr_br_covinv_side / cbr_it_model_tnone_generic / cbr_br_tnone_bits0 / cbr_it_model_seed_generic (TieBBridgeL :375-:470, over ItGTblT0 / GtItTotal /
    ItGTblCover); cbr_codes_tbl_entries is copied minus one unused line (its DynTblOkHolds.it_model_bits_range pose). [codes_build_rows] is the
    bundle in codes_build_root7's premise shape (StepReach :3224) so a producer passes the same four arguments it already passes there.
    Zero admits; this file is a leaf of the model lane (Spec/PngModel), importable by StepPres and by the tie ladder alike. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require ItGTblCover ItGTblSortWin GtTblWidth GtTblRange GtUsedBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ItGTblT0 GtItTotal CfgBitsTblLeaf.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ---- copied VERBATIM from TieBStageCModel.v :428-:434 (cbr_tr_here) ---- *)
Lemma cbr_tr_here : forall c st, GtTblRange.TblRangeE (it_here c st).
Proof.
  intros c st. unfold it_here. cbv zeta.
  destruct (Z.ltb (x_work c (s_sym st) + 1) (x_match c));
    [apply GtTblRange.mkCodeT_in_range|].
  destruct (Z.leb (x_match c) (x_work c (s_sym st))); apply GtTblRange.mkCodeT_in_range.
Qed.

(* ---- copied VERBATIM from TieBStageCModel.v :436-:443 (cbr_tr_fill) ---- *)
Lemma cbr_tr_fill : forall n t bi incr h,
  GtTblRange.TblRangeT t -> GtTblRange.TblRangeE h ->
  GtTblRange.TblRangeT (it_fill n t bi incr h).
Proof.
  induction n as [|k IH]; intros t bi incr h Ht Hh; cbn [it_fill]; [exact Ht|].
  apply IH; [|exact Hh].
  apply GtTblRange.tblrange_tset; [exact Ht | exact Hh].
Qed.

(* ---- copied VERBATIM from TieBStageCModel.v :445-:481 (cbr_tr_step) ---- *)
Lemma cbr_tr_step : forall c st,
  GtTblRange.TblRangeT (s_tbl st) ->
  match it_step c st with
  | ItCont st' => GtTblRange.TblRangeT (s_tbl st')
  | ItBreak st' => GtTblRange.TblRangeT (s_tbl st')
  | ItOverflow t => GtTblRange.TblRangeT t
  end.
Proof.
  intros c st Ht.
  assert (Hfill : GtTblRange.TblRangeT
            (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                                / Z.shiftl 1 (s_len st - s_drop st)))
               (s_tbl st)
               (s_next st + Z.shiftr (s_huff st) (s_drop st))
               (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)))
    by (apply cbr_tr_fill; [exact Ht | apply cbr_tr_here]).
  unfold it_step. cbv zeta.
  destruct (Z.eqb _ 0); cbn [andb].
  - destruct (Z.eqb (s_len st) (x_max c)); cbv beta match iota.
    + cbn [s_tbl]. exact Hfill.
    + destruct (Z.ltb (x_root c) _); cbn [andb]; cbv beta match iota.
      * destruct (Z.eqb _ (s_low st)); cbn [andb negb]; cbv beta match iota.
        -- cbn [s_tbl]. exact Hfill.
        -- destruct (it_enough _ _); cbv beta match iota.
           ++ exact Hfill.
           ++ cbn [s_tbl]. apply GtTblRange.tblrange_tset;
                [exact Hfill | apply GtTblRange.mkCodeT_in_range].
      * cbn [s_tbl]. exact Hfill.
  - destruct (Z.ltb (x_root c) _); cbn [andb]; cbv beta match iota.
    + destruct (Z.eqb _ (s_low st)); cbn [andb negb]; cbv beta match iota.
      * cbn [s_tbl]. exact Hfill.
      * destruct (it_enough _ _); cbv beta match iota.
        -- exact Hfill.
        -- cbn [s_tbl]. apply GtTblRange.tblrange_tset;
             [exact Hfill | apply GtTblRange.mkCodeT_in_range].
    + cbn [s_tbl]. exact Hfill.
Qed.

(* ---- copied VERBATIM from TieBStageCModel.v :483-:501 (cbr_tr_loop) ---- *)
Lemma cbr_tr_loop : forall n c st r,
  GtTblRange.TblRangeT (s_tbl st) ->
  it_loop n c st = Some r ->
  match r with
  | ItBreak st1 => GtTblRange.TblRangeT (it_finish st1)
  | ItOverflow t => GtTblRange.TblRangeT t
  | ItCont _ => True
  end.
Proof.
  induction n as [|k IH]; intros c st r Ht Hl; cbn [it_loop] in Hl;
    [discriminate Hl|].
  destruct (it_step c st) as [st'|st'|t'] eqn:Hs;
    pose proof (cbr_tr_step c st Ht) as HR; rewrite Hs in HR.
  - exact (IH c st' r HR Hl).
  - injection Hl as <-. unfold it_finish.
    destruct (Z.eqb (s_huff st') 0); [exact HR|].
    apply GtTblRange.tblrange_tset; [exact HR | apply GtTblRange.mkCodeT_in_range].
  - injection Hl as <-. exact HR.
Qed.

(* ---- copied VERBATIM from TieBStageCModel.v :504-:527 (cbr_tr_model) ---- *)
Lemma cbr_tr_model : forall ty lens codes root0 t0 out,
  GtTblRange.TblRangeT t0 ->
  it_model ty lens codes root0 t0 = Some out ->
  GtTblRange.TblRangeT (o_tbl out).
Proof.
  intros ty lens codes root0 t0 out Ht0 Hm.
  unfold it_model in Hm.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - injection Hm as <-. exact Ht0.
  - rewrite (ItGTblCover.it_pre_empty_shape _ _ _ _ _ _ Hpre) in Hm.
    injection Hm as <-. cbn [o_tbl].
    apply GtTblRange.tblrange_tset;
      [apply GtTblRange.tblrange_tset; [exact Ht0|]|]; apply GtTblRange.mkCodeT_in_range.
  - injection Hm as <-. exact Ht0.
  - assert (Hst : GtTblRange.TblRangeT (s_tbl st))
      by (rewrite (GtTblWidth.pre_tbl_go _ _ _ _ _ _ _ Hpre); exact Ht0).
    destruct (it_loop (S (Z.to_nat codes)) c st) as [r|] eqn:Hl;
      [|discriminate Hm].
    pose proof (cbr_tr_loop _ _ _ _ Hst Hl) as HR.
    destruct r as [st'|st'|tt].
    + discriminate Hm.
    + injection Hm as <-. exact HR.
    + injection Hm as <-. exact HR.
Qed.

(* ---- copied VERBATIM from TieBBridgeL.v :375-:383 (cbr_br_covinv_side) ---- *)
Lemma cbr_br_covinv_side : forall c cnt0 u,
  OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblCover.CovCtxOk c cnt0 ->
  OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblCover.CovInv c cnt0 u ->
  0 <= s_len u - s_drop u.
Proof.
  intros c cnt0 u Hctx Hinv.
  destruct Hctx as (Hroot & _).
  destruct Hinv as (Hl15 & _ & _ & _ & _ & _ & _ & [ (Hdrop & _) | (Hdrop & Hlen & _) ]); lia.
Qed.

(* ---- copied VERBATIM from TieBBridgeL.v :388-:433 (cbr_it_model_tnone_generic) ---- *)
Lemma cbr_it_model_tnone_generic : forall ty lens codes root0 t0 o o',
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  it_model ty lens codes root0 t0 = Some o ->
  it_model ty lens codes root0 tnone = Some o' ->
  o_ret o = o_ret o' /\ o_bits o = o_bits o' /\ o_used o = o_used o'
  /\ ItGTblT0.AgreeOrInit t0 (o_tbl o) (o_tbl o').
Proof.
  intros ty lens codes root0 t0 o o' Hc Hl Hr H1 H2.
  pose proof (ItGTblT0.it_pre_t0_generic ty lens codes root0 t0) as HPre.
  unfold it_model in H1, H2.
  destruct (it_pre ty lens codes root0 t0) as [ | a | | c st ] eqn:E1;
    destruct (it_pre ty lens codes root0 tnone) as [ | b | | c' st' ] eqn:E2;
    cbn in HPre; try contradiction.
  - injection H1 as <-. injection H2 as <-. cbn.
    repeat split; try reflexivity. exact (ItGTblT0.agreeorinit_refl_init t0).
  - injection H1 as <-. injection H2 as <-. cbn.
    repeat split; try reflexivity. exact HPre.
  - injection H1 as <-. injection H2 as <-. cbn.
    repeat split; try reflexivity. exact (ItGTblT0.agreeorinit_refl_init t0).
  - destruct HPre as (Ec & HS & HT). subst c'.
    destruct (OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblCover.cov_pre
                ty lens codes root0 t0 c st Hc Hl Hr E1) as [Hctx Hinv].
    destruct (it_loop (S (Z.to_nat codes)) c st) as [r|] eqn:L1; [|discriminate].
    destruct (it_loop (S (Z.to_nat codes)) c st') as [r'|] eqn:L2; [|discriminate].
    pose proof (ItGTblT0.it_loop_t0_generic
                  (OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblCover.CovInv c
                     (OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblSortWin.sw_cnt lens codes))
                  (S (Z.to_nat codes)) c t0 st st' r r'
                  (fun u Hu => cbr_br_covinv_side c _ u Hctx Hu)
                  (fun u u' Hu Hs =>
                     OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblCover.cov_step_cont
                       c _ u u' Hctx Hu Hs)
                  Hinv HS HT L1 L2) as HL.
    destruct r as [u|u|t]; destruct r' as [u'|u'|t'];
      cbn in HL, H1, H2; try contradiction; try discriminate.
    + destruct HL as [HS1 HT1].
      injection H1 as <-. injection H2 as <-. cbn.
      assert (Hused : s_used u = s_used u')
        by (destruct HS1 as (_ & _ & _ & _ & _ & _ & _ & H & _); exact H).
      repeat split; try reflexivity; try exact Hused;
        try exact (ItGTblT0.it_finish_t0_generic t0 u u' HS1 HT1).
    + injection H1 as <-. injection H2 as <-. cbn.
      repeat split; try reflexivity. exact HL.
Qed.

(* ---- copied VERBATIM from TieBBridgeL.v :435-:436 (cbr_br_tnone_bits0) ---- *)
Lemma cbr_br_tnone_bits0 : forall i, c_bits (tnone i) = 0.
Proof. intro i. reflexivity. Qed.

(* ---- copied VERBATIM from TieBBridgeL.v :440-:470 (cbr_it_model_seed_generic) ---- *)
Lemma cbr_it_model_seed_generic : forall ty lens codes root0 t0 t0' o,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  it_model ty lens codes root0 t0 = Some o ->
  exists o', it_model ty lens codes root0 t0' = Some o'
    /\ o_ret o' = o_ret o /\ o_bits o' = o_bits o /\ o_used o' = o_used o
    /\ (o_ret o = 0 -> forall i, 0 <= i < 2 ^ o_bits o -> o_tbl o' i = o_tbl o i).
Proof.
  intros ty lens codes root0 t0 t0' o Hc Hl Hr H.
  assert (HLB : GtItTotal.LensBounded lens codes) by exact Hl.
  destruct (it_model ty lens codes root0 tnone) as [o''|] eqn:H'';
    [| exfalso; exact (GtItTotal.it_model_total ty lens codes root0 tnone Hc HLB H'')].
  destruct (it_model ty lens codes root0 t0') as [o'|] eqn:H';
    [| exfalso; exact (GtItTotal.it_model_total ty lens codes root0 t0' Hc HLB H')].
  destruct (cbr_it_model_tnone_generic ty lens codes root0 t0 o o'' Hc Hl Hr H H'')
    as (R1 & B1 & U1 & A1).
  destruct (cbr_it_model_tnone_generic ty lens codes root0 t0' o' o'' Hc Hl Hr H' H'')
    as (R2 & B2 & U2 & A2).
  exists o'. split; [reflexivity|].
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros Hret i Hi.
  assert (Hret'' : o_ret o'' = 0) by congruence.
  assert (Hi'' : 0 <= i < 2 ^ o_bits o'') by (rewrite <- B1; exact Hi).
  pose proof (OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblCover.it_covers_root_pos
                ty lens codes root0 tnone o'' Hc Hl Hr H'' Hret'' i Hi'') as Hbits.
  destruct (A1 i) as [E1 | (_ & E1)]; destruct (A2 i) as [E2 | (_ & E2)];
    try (rewrite E1 in Hbits; rewrite cbr_br_tnone_bits0 in Hbits; lia);
    try (rewrite E2 in Hbits; rewrite cbr_br_tnone_bits0 in Hbits; lia).
  congruence.
Qed.

(* ---- copied VERBATIM from TieBStageCModel.v :529-:556 (cbr_codes_tbl_entries) ---- *)
Lemma cbr_codes_tbl_entries : forall lens t0 o,
  it_model CT_CODES lens 19 7 t0 = Some o ->
  o_ret o = 0 ->
  (forall i, 0 <= i < 19 -> 0 <= lens i <= 7) ->
  forall i, 0 <= i < 2 ^ o_bits o ->
    (0 <= c_op (o_tbl o i) < 256
     /\ 0 <= c_bits (o_tbl o i) < 256
     /\ 0 <= c_val (o_tbl o i) < 2 ^ 16)
    /\ 1 <= c_bits (o_tbl o i) <= o_bits o.
Proof.
  intros lens t0 o Hm Hret Hl i Hi.
  assert (Hl15 : forall j, 0 <= j < 19 -> 0 <= lens j <= 15)
    by (intros j Hj; specialize (Hl j Hj); lia).
  assert (Hc : 0 <= 19) by lia.
  assert (Hr : 1 <= 7 <= 15) by lia.
  pose proof (ItGTblCover.it_covers_root_pos CT_CODES lens 19 7 t0 o Hc Hl15 Hr Hm Hret i Hi)
    as Hb.
  destruct (cbr_it_model_seed_generic CT_CODES lens 19 7 t0 tnone o Hc Hl15 Hr Hm)
    as (o' & Hm' & _ & _ & _ & Heq).
  pose proof (Heq Hret i Hi) as Ei.
  pose proof (cbr_tr_model CT_CODES lens 19 7 tnone o' GtTblRange.tblrange_tnone Hm' i) as HR.
  rewrite Ei in HR.
  destruct HR as (Hop & Hcb & Hcv).
  split; [| exact Hb].
  split; [exact Hop|]. split; [exact Hcb|]. change (2 ^ 16) with 65536. exact Hcv.
Qed.


(** ---- THE BUNDLE: codes_build_root7's premise shape (StepReach :3224), so every producer passes what it already passes there ---- *)
Theorem codes_build_rows : forall lens t0 o,
  it_wf CT_CODES lens 19 7 -> (forall i, 0 <= i < 19 -> lens i <= 7) ->
  it_model CT_CODES lens 19 7 t0 = Some o -> o_ret o = 0 ->
  1 <= o_bits o
  /\ 2 ^ o_bits o <= o_used o
  /\ (forall i, 0 <= i < 2 ^ o_bits o -> 0 <= c_op (o_tbl o i) < 256).
Proof.
  intros lens t0 o Hwf Hl7 Hm Hret.
  assert (Hl07 : forall i, 0 <= i < 19 -> 0 <= lens i <= 7).
  { intros i Hi. destruct Hwf as (_ & Hl15 & _). specialize (Hl15 i Hi). specialize (Hl7 i Hi). lia. }
  split; [exact (CfgBitsTblLeaf.it_model_bits_pos CT_CODES lens 19 7 t0 o ltac:(lia) Hm Hret) |].
  split; [exact (GtUsedBits.used_ge_root_block CT_CODES lens 19 7 t0 o Hm Hret) |].
  intros i Hi. exact (proj1 (proj1 (cbr_codes_tbl_entries lens t0 o Hm Hret Hl07 i Hi))).
Qed.

Set Printing Width 2000.
About codes_build_rows.
Print Assumptions codes_build_rows.
Print Assumptions cbr_codes_tbl_entries.
Print Assumptions cbr_tr_model.
