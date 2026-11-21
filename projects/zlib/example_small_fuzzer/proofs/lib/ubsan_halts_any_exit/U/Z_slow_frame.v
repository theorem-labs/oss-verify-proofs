(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_slow_model.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk DeflateOverlay FlushBlockModel FillWinModel SendModel RefFlushBlk13 RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeLW RefDeflSafeLF RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require BoundSlow.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require BoundSlow.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateOverlay OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FlushBlockModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM.RefDeflSafeW OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLW OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeI2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe.RefDeflateDictM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BoundSlow.BoundFw OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BoundSlow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition din_tieP (inp : list Z) (d : deflate_state) : Prop :=
  cs_input (ds_strm d) = arr_of_list inp /\ Forall (fun b => 0 <= b < 256) inp.

Record SCFG (inp : list Z) (s : deflate_state) : Prop := mkSCFG {
  c_ws : ds_w_size s = 32768;
  c_hs : ds_hash_size s = 32768;
  c_lbs : ds_lit_bufsize s = 16384;
  c_ins : ds_insert s = 0;
  c_wrap : ds_wrap s <> 2;
  c_nraw : ds_wrap s <> 0;
  c_wrng : - 2 <= ds_wrap s <= 2;  (* FLUSH_BLOCK's finish test reads wrap *)
  c_ain : cs_avail_in (ds_strm s) <= 1;
  c_aout : 0 <= cs_avail_out (ds_strm s) < 2^31;
  c_tie : din_tieP inp s }.

Definition SF (s : deflate_state) := (ds_w_size s, ds_hash_size s, ds_lit_bufsize s, ds_insert s, ds_wrap s, ds_strm s).

Lemma SCFG_SF : forall inp s s', SF s' = SF s -> SCFG inp s -> SCFG inp s'.
Proof.
  intros inp s s' E [H1 H2 H3 H4 H5 H5a H5b H6 H7 H8]. unfold SF in E.
  assert (E1 : ds_w_size s' = ds_w_size s) by congruence. assert (E2 : ds_hash_size s' = ds_hash_size s) by congruence.
  assert (E3 : ds_lit_bufsize s' = ds_lit_bufsize s) by congruence. assert (E4 : ds_insert s' = ds_insert s) by congruence.
  assert (E5 : ds_wrap s' = ds_wrap s) by congruence. assert (E6 : ds_strm s' = ds_strm s) by congruence.
  constructor; unfold din_tieP in *; [rewrite E1| rewrite E2| rewrite E3| rewrite E4| rewrite E5| rewrite E5| rewrite E5| rewrite E6| rewrite E6| rewrite E6]; assumption.
Qed.

Definition OUT (s : deflate_state) : nat := length (cs_out_rev (ds_strm s)).
Lemma OUT_SF : forall s s', SF s' = SF s -> OUT s' = OUT s.
Proof. intros s s' E. unfold OUT. assert (E6 : ds_strm s' = ds_strm s) by (unfold SF in E; congruence). rewrite E6. reflexivity. Qed.


Lemma SF_prev_st : forall s, SF (prev_st s) = SF s. Proof. reflexivity. Qed.
Lemma SF_hash_st : forall s, SF (hash_st s) = SF s. Proof. reflexivity. Qed.
Lemma SF_sdist1 : forall s, SF (sdist1 s) = SF s. Proof. reflexivity. Qed.
Lemma SF_sdist2 : forall s dc, SF (sdist2 s dc) = SF s. Proof. reflexivity. Qed.
Lemma SF_dist2_st : forall s, SF (dist2_st s) = SF s. Proof. reflexivity. Qed.
Lemma SF_exit_st : forall s, SF (exit_st s) = SF s. Proof. reflexivity. Qed.
Lemma SF_slit1 : forall s, SF (slit1 s) = SF s. Proof. reflexivity. Qed.
Lemma SF_ltail_st : forall s, SF (ltail_st s) = SF s. Proof. reflexivity. Qed.
Lemma SF_avail0_st : forall s, SF (avail0_st s) = SF s. Proof. reflexivity. Qed.
Lemma SF_break1_st : forall s, SF (break1_st s) = SF s. Proof. reflexivity. Qed.

Lemma SF_insl_st : forall s mi, SF (insl_st s mi) = SF s.
Proof. intros s mi. unfold insl_st. destruct (_ <=? mi); reflexivity. Qed.

Lemma SF_slow_insert : forall n s mi, SF (deflate_slow_insert n s mi) = SF s.
Proof.
  induction n as [|n IH]; intros s mi; [reflexivity|].
  rewrite deflate_slow_insert_step. cbv zeta. destruct (negb _); [rewrite IH|]; apply SF_insl_st.
Qed.

Lemma SF_st_lm : forall s hh, SF (st_lm s hh) = SF s.
Proof.
  intros s hh. unfold st_lm. destruct (sl_lm_cond s hh); [|reflexivity].
  destruct (longest_match_ms s hh) as (ms & E). cbv zeta. rewrite E. destruct (sl_filter _); reflexivity.
Qed.

Lemma SF_st_sdist : forall s, 3 <= ds_prev_length s -> ds_prev_length s - 1 <= ds_lookahead s -> ds_lookahead s < 2 ^ 31 ->
  3 <= ds_strstart s + ds_lookahead s -> ds_strstart s + ds_lookahead s < 2 ^ 32 -> SF (fst (st_sdist s)) = SF s.
Proof.
  intros s H1 H2 H3 H4 H5. rewrite (proj1 (sdist_eq s H1 H2 H3 H4 H5)).
  rewrite SF_exit_st, SF_slow_insert, SF_dist2_st, SF_sdist2, SF_sdist1. reflexivity.
Qed.


Lemma SCFG_fill : forall inp s, SCFG inp s -> 0 <= cs_avail_in (ds_strm s) -> SCFG inp (fill_window s) /\ OUT (fill_window s) = OUT s.
Proof.
  intros inp s [H1 H2 H3 H4 H5 H5a H5b H6 H7 H8] H0.
  pose proof (fw_rest_fill_window s) as R. unfold fw_rest in R.
  pose proof (fwG_fill_window s) as G. unfold fwG in G.
  pose proof (fill_window_keep s) as K. unfold fw_keep in K.
  destruct (GZINS_fill_window s) as [_ I]. unfold INS in I.
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
  apply I; [exact H4| rewrite H1; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; lia].
Qed.


Lemma fbo_strm_keep : forall X last,
  cs_input (ds_strm (flush_block_only X last)) = cs_input (ds_strm X)
  /\ cs_avail_in (ds_strm (flush_block_only X last)) = cs_avail_in (ds_strm X).
Proof.
  intros X last. rewrite fbo_eq.
  assert (E1 : cs_input (ds_strm (fbo3 X last)) = cs_input (ds_strm X) /\ cs_avail_in (ds_strm (fbo3 X last)) = cs_avail_in (ds_strm X)).
  { rewrite fbo3_strm. unfold fbo1. rewrite tr_flush_block_strm. destruct (_ && _); [destruct (ds_strm X)|]; split; reflexivity. }
  destruct (fp_len (fbo3 X last) =? 0); [exact E1|].
  set (Y := fbo3 X last) in *. clearbody Y.
  destruct E1 as [Ea Eb]. rewrite <- Ea, <- Eb. unfold fp_tail.
  destruct Y; cbn -[Z.sub Z.add Z.eqb wrap64 wrap32 arr_slice cs_emit Z.ltb fp_len].
  destruct ds_strm; cbn -[Z.sub Z.add Z.eqb wrap64 wrap32 arr_slice Z.ltb fp_len rev_append].
  destruct (_ - _ =? 0); split; reflexivity.
Qed.

Lemma fbo_avail_out : forall X last, flush_ok X last -> ds_lit_bufsize X = 16384 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  0 <= cs_avail_out (ds_strm (flush_block_only X last)) <= cs_avail_out (ds_strm X).
Proof.
  intros X last F LB RA. destruct (flush_ok_fbo X last F LB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RP & _).
  destruct (tfb_keep X last) as (_ & _ & _ & EAO). pose proof (fbo3_strm X last) as ES.
  rewrite fbo_eq.
  assert (EL : fp_len (fbo3 X last) = if cs_avail_out (ds_strm X) <? ds_pending (fbo3 X last) then cs_avail_out (ds_strm X) else ds_pending (fbo3 X last)).
  { unfold fp_len. rewrite ES, EAO, wrap32_id by lia. reflexivity. }
  destruct (fp_len (fbo3 X last) =? 0) eqn:E0; [rewrite ES, EAO; lia|].
  unfold fp_tail. cbv zeta.
  assert (EA : forall c l v w, cs_avail_out (cset_total_out (cset_avail_out (cs_emit c l) v) w) = v) by (intros [] l v w; reflexivity).
  destruct (_ - _ =? 0); dsred; rewrite ?EA, ?ES, ?EAO, ?EL; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending (fbo3 X last))); lia.
Qed.

Lemma PF_fbo : forall X last, PF (flush_block_only X last) = PF X.
Proof. intros X last. unfold flush_block_only. cbv zeta. rewrite PF_flush_pending, PF_set_block_start, PF_tfb. reflexivity. Qed.

Lemma SCFG_fbo : forall inp X last, SCFG inp X -> flush_ok X last -> SCFG inp (flush_block_only X last).
Proof.
  intros inp X last [H1 H2 H3 H4 H5 H5a H5b H6 H7 H8] F.
  pose proof (PF_fields _ _ (PF_fbo X last)) as ((_ & _ & _ & _ & _ & _) & (_ & Ei & _ & _ & _ & _ & _ & Ew) & (_ & Elb & _ & _ & Ehs & _) & (_ & _ & _ & _ & _ & _ & _ & _ & EK)).
  destruct (KV_fields _ _ EK) as (Ews & _).
  destruct (fbo_strm_keep X last) as [Ein Eain].
  pose proof (fbo_avail_out X last F H3 H7) as RA.
  constructor; unfold din_tieP in *; rewrite ?Ews, ?Ehs, ?Elb, ?Ei, ?Ew, ?Ein, ?Eain; try assumption; lia.
Qed.

(* slow_fin reads wrap after FLUSH_BLOCK(s, 1); flush_block_only keeps it. *)
Lemma fbo_wrap : forall X last, ds_wrap (flush_block_only X last) = ds_wrap X.
Proof.
  intros X last.
  pose proof (PF_fields _ _ (PF_fbo X last)) as ((_ & _ & _ & _ & _ & _) & (_ & _ & _ & _ & _ & _ & _ & Ew) & _).
  exact Ew.
Qed.


Lemma SF_tally_dist : forall s d l, SF (fst (tr_tally_dist s d l)) = SF s.
Proof. reflexivity. Qed.

Lemma SF_st_sdist' : forall s, SF (fst (st_sdist s)) = SF s.
Proof.
  intros s. unfold st_sdist.
  pose proof (SF_tally_dist s (wrap32 (ds_strstart s - 1 - ds_prev_match s)) (ds_prev_length s - 3)) as ET.
  destruct (tr_tally_dist s _ _) as [s1 b]. cbn [fst] in ET. rewrite <- ET. clear ET. cbv zeta. cbn [fst].
  match goal with |- SF (set_strstart (set_match_length (set_match_available ?U 0) 2) _) = _ => transitivity (SF U); [generalize U; intros U0; reflexivity|] end.
  rewrite SF_slow_insert. reflexivity.
Qed.

Lemma flush_block_fst' : forall s last, fst (flush_block s last) = flush_block_only s last.
Proof. intros s last. unfold flush_block. destruct (_ =? 0); reflexivity. Qed.

Lemma st_bflush_fst : forall s b, fst (st_bflush s b) = if b then flush_block_only s 0 else s.
Proof.
  intros s b. unfold st_bflush. destruct b; [|reflexivity].
  rewrite <- flush_block_fst'. destruct (flush_block s 0) as [s' [bs|]]; reflexivity.
Qed.

Lemma decide_frame : forall inp X4, SCFG inp X4 -> sdec_ok 32768 X4 ->
  SCFG inp (fst (st_decide X4)) /\ (OUT X4 <= OUT (fst (st_decide X4)))%nat.
Proof.
  intros inp X4 C (SV & RLA & D). unfold st_decide. destruct (dist_cond X4) eqn:DC.
  - destruct D as (_ & _ & _ & _ & FOK). rewrite st_bflush_fst.
    pose proof (SF_st_sdist' X4) as E. pose proof (SCFG_SF _ _ _ E C) as C'. pose proof (OUT_SF _ _ E) as O'.
    destruct (snd (st_sdist X4)).
    + split; [apply SCFG_fbo; [exact C'| exact (FOK eq_refl)]|]. rewrite <- O'. apply fbo_out_mono.
    + split; [exact C'| rewrite O'; apply le_n].
  - destruct (negb (ds_match_available X4 =? 0)).
    + rewrite st_slit_eq. cbv zeta. cbn [fst]. destruct D as (_ & FOK & _).
      pose proof (SCFG_SF _ _ _ (SF_slit1 X4) C) as C1. pose proof (OUT_SF _ _ (SF_slit1 X4)) as O1.
      destruct (ds_sym_next X4 + 3 =? ds_sym_end X4).
      * split; [apply (SCFG_SF _ _ _ (SF_ltail_st _)); apply SCFG_fbo; [exact C1| exact (FOK eq_refl)]|].
        rewrite (OUT_SF _ _ (SF_ltail_st _)), <- O1. apply fbo_out_mono.
      * split; [apply (SCFG_SF _ _ _ (SF_ltail_st _)); exact C1|]. rewrite (OUT_SF _ _ (SF_ltail_st _)), O1. apply le_n.
    + rewrite st_avail_eq. cbn [fst]. split; [apply (SCFG_SF _ _ _ (SF_avail0_st _)); exact C|]. rewrite (OUT_SF _ _ (SF_avail0_st _)). apply le_n.
Qed.

Lemma fill_frame : forall inp X flush, SCFG inp X -> (ds_lookahead X < MIN_LOOKAHEAD -> fw_wf 32768 32768 X) ->
  SCFG inp (fst (st_fill X flush)) /\ OUT (fst (st_fill X flush)) = OUT X.
Proof.
  intros inp X flush C FW. unfold st_fill. destruct (Z.ltb_spec (ds_lookahead X) MIN_LOOKAHEAD) as [LT|GE]; [|split; [exact C| reflexivity]].
  destruct (SCFG_fill inp X C (proj1 (wf_ai _ _ _ (FW LT)))) as [C' O']. cbv zeta.
  destruct (_ && _); [split; assumption|]. destruct (_ =? 0); split; assumption.
Qed.

Lemma sbody_frame : forall inp X flush, SCFG inp X -> strip_ok 32768 32768 X flush ->
  SCFG inp (fst (st_sbody X flush)) /\ (OUT X <= OUT (fst (st_sbody X flush)))%nat.
Proof.
  intros inp X flush C (_ & FW & _ & HOK). destruct (fill_frame inp X flush C FW) as [C1 O1]. unfold st_sbody.
  destruct (snd (st_fill X flush)) as [o|] eqn:EO; cbn [fst]; [split; [exact C1| rewrite O1; apply le_n]|].
  specialize (HOK eq_refl). rewrite <- O1. set (X1 := fst (st_fill X flush)) in *. clearbody X1.
  destruct (Z_lt_le_dec (ds_lookahead X1) 3) as [LO|HI].
  - rewrite (st_srest_lo X1 LO). destruct (shash_ok_lo _ _ HOK LO) as (_ & _ & _ & DOK).
    assert (E : SF (st_lm (prev_st X1) 0) = SF X1) by (rewrite SF_st_lm; apply SF_prev_st).
    destruct (decide_frame inp _ (SCFG_SF _ _ _ E C1) DOK) as [C4 O4]. split; [exact C4|]. rewrite <- (OUT_SF _ _ E). exact O4.
  - rewrite (st_srest_hi X1 HI). destruct (shash_ok_hi _ _ HOK HI) as (_ & _ & _ & DOK).
    assert (E : SF (st_lm (hash_st X1) (hash_hh X1)) = SF X1) by (rewrite SF_st_lm; apply SF_hash_st).
    destruct (decide_frame inp _ (SCFG_SF _ _ _ E C1) DOK) as [C4 O4]. split; [exact C4|]. rewrite <- (OUT_SF _ _ E). exact O4.
Qed.


Definition slow_tailres (s1 : deflate_state) (flush : Z) : deflate_state * block_state :=
  deflate_tail (tail_st (if negb (ds_match_available s1 =? 0) then break1_st s1 else s1)) flush.

Definition slow_res (flush : Z) (f : nat) (X : deflate_state) : deflate_state * block_state :=
  match snd (deflate_slow_loop f X flush) with
  | Some bs => (fst (deflate_slow_loop f X flush), bs)
  | None => slow_tailres (fst (deflate_slow_loop f X flush)) flush
  end.

Lemma deflate_slow_res : forall s flush, deflate_slow s flush = slow_res flush (lz_fuel s) s.
Proof. intros s flush. rewrite deflate_slow_eq. unfold slow_res, slow_tailres. destruct (snd _); reflexivity. Qed.

Lemma slow_res_S : forall flush f X,
  slow_res flush (S f) X = match snd (st_sbody X flush) with
                           | LCont => slow_res flush f (fst (st_sbody X flush))
                           | LBreak => slow_tailres (fst (st_sbody X flush)) flush
                           | LRet bs => (fst (st_sbody X flush), bs)
                           end.
Proof. intros flush f X. unfold slow_res. rewrite sloop_step'. destruct (snd (st_sbody X flush)); reflexivity. Qed.

Definition tail_safe (flush : Z) (f : nat) (X : deflate_state) : Prop :=
  match snd (deflate_slow_loop f X flush) with Some _ => True | None => stail_ok 32768 (fst (deflate_slow_loop f X flush)) flush end.

Lemma tail_safe_S : forall flush f X,
  tail_safe flush (S f) X = match snd (st_sbody X flush) with
                            | LCont => tail_safe flush f (fst (st_sbody X flush))
                            | LBreak => stail_ok 32768 (fst (st_sbody X flush)) flush
                            | LRet bs => True
                            end.
Proof. intros flush f X. unfold tail_safe. rewrite sloop_step'. destruct (snd (st_sbody X flush)); reflexivity. Qed.

Lemma OUT_tailres : forall s1 flush, (OUT s1 <= OUT (fst (slow_tailres s1 flush)))%nat.
Proof.
  intros s1 flush. unfold slow_tailres.
  set (s2 := if negb (ds_match_available s1 =? 0) then break1_st s1 else s1).
  assert (E2 : OUT (tail_st s2) = OUT s1) by (unfold s2; destruct (negb _); reflexivity).
  rewrite <- E2. generalize (tail_st s2). intros t. unfold deflate_tail.
  destruct (flush =? Z_FINISH).
  - pose proof (fbo_out_mono t 1) as M. rewrite <- flush_block_fst' in M. destruct (flush_block t 1) as [s' [bs|]]; exact M.
  - destruct (negb (ds_sym_next t =? 0)); [|apply le_n].
    pose proof (fbo_out_mono t 0) as M. rewrite <- flush_block_fst' in M. destruct (flush_block t 0) as [s' [bs|]]; exact M.
Qed.

Lemma OUT_res : forall inp flush f X, SCFG inp X -> sloop_ok 32768 32768 f X flush ->
  (OUT X <= OUT (fst (slow_res flush f X)))%nat.
Proof.
  intros inp flush. induction f as [|f IH]; intros X C LOK; [destruct LOK|].
  rewrite sloop_ok_S in LOK. destruct LOK as [TOK LOK]. rewrite slow_res_S.
  destruct (sbody_frame inp X flush C TOK) as [C' O'].
  destruct (snd (st_sbody X flush)) as [| |bs].
  - eapply Nat.le_trans; [exact O'| apply IH; assumption].
  - eapply Nat.le_trans; [exact O'| apply OUT_tailres].
  - exact O'.
Qed.

Lemma sbody_break_flush : forall X flush, snd (st_sbody X flush) = LBreak -> flush <> Z_NO_FLUSH.
Proof. intros X flush H E. exact (BoundSlow.sbody_nobreak flush X E H). Qed.
