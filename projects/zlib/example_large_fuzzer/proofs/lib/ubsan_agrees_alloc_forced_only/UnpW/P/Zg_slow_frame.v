(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_slow_model Z_slow_frame.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk DeflateOverlay FlushBlockModel FillWinModel SendModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefFlushBlk13 RefDeflFast1. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow5 RefDeflSlow6. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeW RefDeflSafeLW. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeLF RefDeflSafeI2. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflateDictM BoundFw. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import BoundSlow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record SCFGg (inp : list Z) (s : deflate_state) : Prop := mkSCFGg {
  g_ws : ds_w_size s = 32768;
  g_hs : ds_hash_size s = 32768;
  g_lbs : ds_lit_bufsize s = 16384;
  g_wrap : ds_wrap s <> 2;
  g_nraw : ds_wrap s <> 0;
  g_wrng : - 2 <= ds_wrap s <= 2;  (* 1.4 (zl14-cmp): FLUSH_BLOCK's finish test reads wrap; compress2 runs with wrap 1 *)
  g_ai : cs_avail_in (ds_strm s) < 2^31;
  g_aout : 0 <= cs_avail_out (ds_strm s) < 2^31;
  g_tie : din_tieP inp s }.

Lemma SCFGg_SF : forall inp s s', SF s' = SF s -> SCFGg inp s -> SCFGg inp s'.
Proof.
  intros inp s s' E [H1 H2 H3 H5 H4 H9 H6 H7 H8]. unfold SF in E.
  assert (E1 : ds_w_size s' = ds_w_size s) by congruence. assert (E2 : ds_hash_size s' = ds_hash_size s) by congruence.
  assert (E3 : ds_lit_bufsize s' = ds_lit_bufsize s) by congruence.
  assert (E5 : ds_wrap s' = ds_wrap s) by congruence. assert (E6 : ds_strm s' = ds_strm s) by congruence.
  constructor; unfold din_tieP in *; [rewrite E1| rewrite E2| rewrite E3| rewrite E5| rewrite E5| rewrite E5| rewrite E6| rewrite E6| rewrite E6]; assumption.
Qed.

Lemma SCFGg_fill : forall inp s, SCFGg inp s -> 0 <= cs_avail_in (ds_strm s) -> SCFGg inp (fill_window s) /\ OUT (fill_window s) = OUT s.
Proof.
  intros inp s [H1 H2 H3 H5 H4 H9 H6 H7 H8] H0.
  pose proof (fw_rest_fill_window s) as R. unfold fw_rest in R.
  pose proof (fwG_fill_window s) as G. unfold fwG in G.
  pose proof (fill_window_keep s) as K. unfold fw_keep in K.
  destruct (fill_window_LA s ltac:(unfold AI; lia)) as [_ A]. unfold AI in A.
  assert (E1 : ds_w_size (fill_window s) = ds_w_size s) by congruence.
  assert (E2 : ds_hash_size (fill_window s) = ds_hash_size s) by congruence.
  assert (E3 : ds_lit_bufsize (fill_window s) = ds_lit_bufsize s) by (decompose [and] K; assumption).
  assert (E5 : ds_wrap (fill_window s) = ds_wrap s) by congruence.
  assert (E6 : cs_input (ds_strm (fill_window s)) = cs_input (ds_strm s)) by congruence.
  assert (E7 : cs_avail_out (ds_strm (fill_window s)) = cs_avail_out (ds_strm s)) by (decompose [and] K; assumption).
  assert (E8 : cs_out_rev (ds_strm (fill_window s)) = cs_out_rev (ds_strm s)) by (decompose [and] K; assumption).
  split; [|unfold OUT; rewrite E8; reflexivity].
  constructor; unfold din_tieP in *; rewrite ?E1, ?E2, ?E3, ?E5, ?E6, ?E7; try assumption; try lia.
Qed.

Lemma SCFGg_fbo : forall inp X last, SCFGg inp X -> flush_ok X last -> SCFGg inp (flush_block_only X last).
Proof.
  intros inp X last [H1 H2 H3 H5 H4 H9 H6 H7 H8] F.
  pose proof (PF_fields _ _ (PF_fbo X last)) as ((_ & _ & _ & _ & _ & _) & (_ & Ei & _ & _ & _ & _ & _ & Ew) & (_ & Elb & _ & _ & Ehs & _) & (_ & _ & _ & _ & _ & _ & _ & _ & EK)).
  destruct (KV_fields _ _ EK) as (Ews & _).
  destruct (fbo_strm_keep X last) as [Ein Eain].
  pose proof (fbo_avail_out X last F H3 H7) as RA.
  constructor; unfold din_tieP in *; rewrite ?Ews, ?Ehs, ?Elb, ?Ei, ?Ew, ?Ein, ?Eain; try assumption; lia.
Qed.

Lemma decide_frameg : forall inp X4, SCFGg inp X4 -> sdec_ok 32768 X4 ->
  SCFGg inp (fst (st_decide X4)) /\ (OUT X4 <= OUT (fst (st_decide X4)))%nat.
Proof.
  intros inp X4 C (SV & RLA & D). unfold st_decide. destruct (dist_cond X4) eqn:DC.
  - destruct D as (_ & _ & _ & _ & FOK). rewrite st_bflush_fst.
    pose proof (SF_st_sdist' X4) as E. pose proof (SCFGg_SF _ _ _ E C) as C'. pose proof (OUT_SF _ _ E) as O'.
    destruct (snd (st_sdist X4)).
    + split; [apply SCFGg_fbo; [exact C'| exact (FOK eq_refl)]|]. rewrite <- O'. apply fbo_out_mono.
    + split; [exact C'| rewrite O'; apply le_n].
  - destruct (negb (ds_match_available X4 =? 0)).
    + rewrite st_slit_eq. cbv zeta. cbn [fst]. destruct D as (_ & FOK & _).
      pose proof (SCFGg_SF _ _ _ (SF_slit1 X4) C) as C1. pose proof (OUT_SF _ _ (SF_slit1 X4)) as O1.
      destruct (ds_sym_next X4 + 3 =? ds_sym_end X4).
      * split; [apply (SCFGg_SF _ _ _ (SF_ltail_st _)); apply SCFGg_fbo; [exact C1| exact (FOK eq_refl)]|].
        rewrite (OUT_SF _ _ (SF_ltail_st _)), <- O1. apply fbo_out_mono.
      * split; [apply (SCFGg_SF _ _ _ (SF_ltail_st _)); exact C1|]. rewrite (OUT_SF _ _ (SF_ltail_st _)), O1. apply le_n.
    + rewrite st_avail_eq. cbn [fst]. split; [apply (SCFGg_SF _ _ _ (SF_avail0_st _)); exact C|]. rewrite (OUT_SF _ _ (SF_avail0_st _)). apply le_n.
Qed.

Lemma fill_frameg : forall inp X flush, SCFGg inp X -> (ds_lookahead X < MIN_LOOKAHEAD -> fw_wf 32768 32768 X) ->
  SCFGg inp (fst (st_fill X flush)) /\ OUT (fst (st_fill X flush)) = OUT X.
Proof.
  intros inp X flush C FW. unfold st_fill. destruct (Z.ltb_spec (ds_lookahead X) MIN_LOOKAHEAD) as [LT|GE]; [|split; [exact C| reflexivity]].
  destruct (SCFGg_fill inp X C (proj1 (wf_ai _ _ _ (FW LT)))) as [C' O']. cbv zeta.
  destruct (_ && _); [split; assumption|]. destruct (_ =? 0); split; assumption.
Qed.

Lemma sbody_frameg : forall inp X flush, SCFGg inp X -> strip_ok 32768 32768 X flush ->
  SCFGg inp (fst (st_sbody X flush)) /\ (OUT X <= OUT (fst (st_sbody X flush)))%nat.
Proof.
  intros inp X flush C (_ & FW & _ & HOK). destruct (fill_frameg inp X flush C FW) as [C1 O1]. unfold st_sbody.
  destruct (snd (st_fill X flush)) as [o|] eqn:EO; cbn [fst]; [split; [exact C1| rewrite O1; apply le_n]|].
  specialize (HOK eq_refl). rewrite <- O1. set (X1 := fst (st_fill X flush)) in *. clearbody X1.
  destruct (Z_lt_le_dec (ds_lookahead X1) 3) as [LO|HI].
  - rewrite (st_srest_lo X1 LO). destruct (shash_ok_lo _ _ HOK LO) as (_ & _ & _ & DOK).
    assert (E : SF (st_lm (prev_st X1) 0) = SF X1) by (rewrite SF_st_lm; apply SF_prev_st).
    destruct (decide_frameg inp _ (SCFGg_SF _ _ _ E C1) DOK) as [C4 O4]. split; [exact C4|]. rewrite <- (OUT_SF _ _ E). exact O4.
  - rewrite (st_srest_hi X1 HI). destruct (shash_ok_hi _ _ HOK HI) as (_ & _ & _ & DOK).
    assert (E : SF (st_lm (hash_st X1) (hash_hh X1)) = SF X1) by (rewrite SF_st_lm; apply SF_hash_st).
    destruct (decide_frameg inp _ (SCFGg_SF _ _ _ E C1) DOK) as [C4 O4]. split; [exact C4|]. rewrite <- (OUT_SF _ _ E). exact O4.
Qed.

Lemma OUT_resg : forall inp flush f X, SCFGg inp X -> sloop_ok 32768 32768 f X flush ->
  (OUT X <= OUT (fst (slow_res flush f X)))%nat.
Proof.
  intros inp flush. induction f as [|f IH]; intros X C LOK; [destruct LOK|].
  rewrite sloop_ok_S in LOK. destruct LOK as [TOK LOK]. rewrite slow_res_S.
  destruct (sbody_frameg inp X flush C TOK) as [C' O'].
  destruct (snd (st_sbody X flush)) as [| |bs].
  - eapply Nat.le_trans; [exact O'| apply IH; assumption].
  - eapply Nat.le_trans; [exact O'| apply OUT_tailres].
  - exact O'.
Qed.

Lemma deflate_tail_nf_eq : forall t flush, flush <> Z_FINISH ->
  deflate_tail t flush = (if negb (ds_sym_next t =? 0)
                          then (flush_block_only t 0, if cs_avail_out (ds_strm (flush_block_only t 0)) =? 0 then need_more else block_done)
                          else (t, block_done)).
Proof.
  intros t flush NF. unfold deflate_tail. replace (flush =? Z_FINISH) with false by (symmetry; apply Z.eqb_neq; exact NF).
  destruct (negb (ds_sym_next t =? 0)); [| reflexivity].
  unfold flush_block. destruct (cs_avail_out (ds_strm (flush_block_only t 0)) =? 0); reflexivity.
Qed.
