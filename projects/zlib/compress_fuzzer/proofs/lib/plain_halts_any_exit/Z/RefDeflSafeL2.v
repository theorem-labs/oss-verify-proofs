(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeW.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeF.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLM.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLW.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma fw_rest_fields : forall s s', fw_rest s' = fw_rest s ->
  (ds_status s' = ds_status s /\ ds_pending_buf s' = ds_pending_buf s /\ ds_pending_buf_size s' = ds_pending_buf_size s
   /\ ds_pending_out s' = ds_pending_out s /\ ds_pending s' = ds_pending s /\ ds_wrap s' = ds_wrap s /\ ds_gzhead s' = ds_gzhead s
   /\ ds_gzindex s' = ds_gzindex s /\ ds_method s' = ds_method s /\ ds_last_flush s' = ds_last_flush s /\ ds_w_size s' = ds_w_size s
   /\ ds_w_bits s' = ds_w_bits s /\ ds_w_mask s' = ds_w_mask s /\ ds_window_size s' = ds_window_size s /\ ds_hash_size s' = ds_hash_size s
   /\ ds_hash_bits s' = ds_hash_bits s /\ ds_hash_mask s' = ds_hash_mask s /\ ds_hash_shift s' = ds_hash_shift s
   /\ ds_match_length s' = ds_match_length s /\ ds_prev_match s' = ds_prev_match s /\ ds_match_available s' = ds_match_available s
   /\ ds_prev_length s' = ds_prev_length s)
  /\ (ds_max_chain_length s' = ds_max_chain_length s /\ ds_max_lazy_match s' = ds_max_lazy_match s /\ ds_level s' = ds_level s
      /\ ds_strategy s' = ds_strategy s /\ ds_good_match s' = ds_good_match s /\ ds_nice_match s' = ds_nice_match s
      /\ ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s /\ ds_dyn_ltree_dl s' = ds_dyn_ltree_dl s /\ ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s
      /\ ds_dyn_dtree_dl s' = ds_dyn_dtree_dl s /\ ds_bl_tree_fc s' = ds_bl_tree_fc s /\ ds_bl_tree_dl s' = ds_bl_tree_dl s
      /\ ds_l_max_code s' = ds_l_max_code s /\ ds_d_max_code s' = ds_d_max_code s /\ ds_bl_max_code s' = ds_bl_max_code s
      /\ ds_bl_count s' = ds_bl_count s /\ ds_heap s' = ds_heap s /\ ds_heap_len s' = ds_heap_len s /\ ds_heap_max s' = ds_heap_max s
      /\ ds_depth s' = ds_depth s /\ ds_lit_bufsize s' = ds_lit_bufsize s /\ ds_sym_next s' = ds_sym_next s /\ ds_sym_end s' = ds_sym_end s
      /\ ds_opt_len s' = ds_opt_len s /\ ds_static_len s' = ds_static_len s /\ ds_matches s' = ds_matches s
      /\ ds_bi_buf s' = ds_bi_buf s /\ ds_bi_valid s' = ds_bi_valid s)
  /\ (cs_input (ds_strm s') = cs_input (ds_strm s) /\ cs_out_rev (ds_strm s') = cs_out_rev (ds_strm s)
      /\ cs_avail_out (ds_strm s') = cs_avail_out (ds_strm s) /\ cs_total_out (ds_strm s') = cs_total_out (ds_strm s)
      /\ cs_msg (ds_strm s') = cs_msg (ds_strm s) /\ cs_data_type (ds_strm s') = cs_data_type (ds_strm s)).
Proof.
  intros s s' E. unfold fw_rest in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

Lemma dwf_wk : forall s, dwf s -> 0 <= ds_w_bits s /\ ds_w_size s = 2 ^ ds_w_bits s.
Proof. intros s D. pose proof (df_wbits _ D). split; [lia | exact (df_wsize _ D)]. Qed.

Definition adler_ok (s : deflate_state) : Prop := 0 <= cs_adler (ds_strm s) < 2 ^ 64.

Lemma DX_FWX : forall s, dwf s -> DX s -> adler_ok s -> dmode s <> 0 -> FWX s.
Proof.
  intros s D X Ha Hm. constructor.
  - exact (dx_chain _ X Hm).
  - exact (dx_insh _ X).
  - exact (dx_ins _ X).
  - exact (dx_hw _ X).
  - exact Ha.
Qed.

Lemma DC_fill_window : forall c0 s, C0OK c0 -> DC c0 s -> dmode s <> 0 -> ds_status s <> FINISH_STATE ->
  ds_lookahead s < MIN_LOOKAHEAD ->
  let s' := fill_window s in
  DC c0 s' /\ KV s' = KV s /\ OUTLE s s' /\ fw_rest s' = fw_rest s
  /\ ds_strstart s' - ds_block_start s' = ds_strstart s - ds_block_start s
  /\ ds_lookahead s <= ds_lookahead s' <= 2 * ds_w_size s
  /\ (ds_lookahead s' < MIN_LOOKAHEAD -> cs_avail_in (ds_strm s') = 0 /\ ds_strstart s' + ds_lookahead s' <= 2 * ds_w_size s - 2)
  /\ fw_wf (ds_w_size s) (ds_hash_size s) s'
  /\ ds_strstart s' <= 2 * ds_w_size s - MIN_LOOKAHEAD - 1
  /\ (1 <= ds_strstart s -> 1 <= ds_strstart s')
  /\ wrap32 (ds_strstart s' - ds_match_start s') = wrap32 (ds_strstart s - ds_match_start s).
Proof.
  intros c0 s HC0 HDC Hm Hst Hlook s'. subst s'. pose proof HDC as [[D X] V].
  pose proof (dwf_sizes s D) as (Sw & Sh & Sl & Spbs & Ssh).
  assert (Hwr : 0 <= ds_wrap s) by (pose proof (dx_wrapneg _ X); pose proof (df_wrap _ D); destruct (Z_lt_le_dec (ds_wrap s) 0); [exfalso; apply Hst; auto | lia]).
  pose proof (dwf_fw_wf s D Hwr (sv_nin _ _ V) (sv_ain _ _ V) ltac:(rewrite (sv_input _ _ V); pose proof (sv_inlen _ _ V); lia)
                (sv_tin _ _ V) (sv_adler _ _ V) (sv_ib _ _ V)) as HW.
  pose proof (fill_window_facts (ds_w_size s) (ds_hash_size s) s HW Hlook) as (HW' & HC' & HK' & HL' & HA' & HX').
  pose proof (fill_window_FWX (ds_w_size s) (ds_hash_size s) (ds_w_bits s) (dwf_wk s D) s HW (DX_FWX s D X (sv_adler _ _ V) Hm) Hlook) as (FX' & G' & SL' & SS' & S1' & LL').
  pose proof (fw_rest_fill_window s) as R'.
  set (s' := fill_window s) in *.
  pose proof (fw_rest_fields s s' R') as (R1 & R2 & R3).
  destruct R1 as (Est & Epb & Epbs & Epo & Epd & Ewr & Egz & Egi & Eme & Elf & Ews & Ewb & Ewm & Ewsz & Ehs & Ehb & Ehm & Ehsh & Eml & Epm & Ema & Epl).
  destruct R2 as (Emc & Elz & Elv & Esy & Egm & Enm & Elfc & Eldl & Edfc & Eddl & Ebfc & Ebdl & Elmc & Edmc & Ebmc & Eblc & Ehp & Ehpl & Ehpm & Edep & Elbs & Esn & Ese & Eol & Esl & Emt & Ebb & Ebv).
  destruct R3 as (Ein & Eout & Eao & Eto & Emsg & Edt).
  pose proof (fwG_fields s s' G') as (EKV & Eext & Enin & _ & Ewms).
  pose proof HW' as W. destruct W.
  apply pair_equal_spec in EKV. destruct EKV as [EKV3 EB].
  assert (Eb1 : ds_window_blk s' = ds_window_blk s) by congruence.
  assert (Eb2 : ds_prev_blk s' = ds_prev_blk s) by congruence.
  assert (Eb3 : ds_head_blk s' = ds_head_blk s) by congruence.
  assert (Eb4 : ds_pending_buf_blk s' = ds_pending_buf_blk s) by congruence.
  assert (D' : dwf s').
  { destruct D; constructor; rewrite ?Est, ?Epb, ?Epbs, ?Epo, ?Epd, ?Ewr, ?Egz, ?Eme, ?Elf, ?Ews, ?Ewb, ?Ewm, ?Ewsz, ?Ehs, ?Ehb, ?Ehm, ?Ehsh,
      ?Elv, ?Esy, ?Elbs, ?Ese, ?Ebb, ?Ebv, ?Eb1, ?Eb2, ?Eb3, ?Eb4; try assumption.
    - unfold deflateStateCheck in *. rewrite Est. assumption.
    - unfold tree_lens in *. rewrite Elfc, Eldl, Edfc, Eddl, Ebfc, Ebdl, Eblc, Ehp, Edep. assumption.
    - clear - wf_ins wf_sl wf_look Sw. lia. }
  assert (X' : DX s').
  { pose proof (dx_syms _ X) as Xsyms. pose proof (dx_hist _ X) as Xhist. pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl.
    pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc.
    assert (Em' : dmode s' = dmode s) by (unfold dmode; rewrite Elv, Esy; reflexivity).
    assert (En' : nsym s' = nsym s) by (unfold nsym; rewrite Esn; reflexivity).
    destruct X; constructor; rewrite ?Em', ?En', ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Eml, ?Epl, ?Ema, ?Epm, ?Emt, ?Ewr, ?Est, ?Esn, ?Elbs, ?Eol, ?Esl, ?Epd, ?Epo, ?Ebv;
      try assumption.
    - exact (fx_insh _ FX').
    - exact (fx_ins _ FX').
    - exact (fx_hw _ FX').
    - intros Hm4. destruct (dx_slow Hm4) as (A1 & A2 & A3). split; [exact A1|]. split; [intros Hma; exact (S1' (A2 Hma))|].
      intros H3. destruct (A3 H3) as (A4 & A6 & A5). rewrite Ewms, Ews. split; [clear - A4 HL'; lia | split; [exact (S1' A6) | exact A5]].
    - intros Hm0. exfalso. exact (Hm Hm0).
    - intros Hf. exfalso. exact (Hst Hf).
    - intros j Hj. apply (sym_okb_same s s' j Epb Elbs). exact (Xsyms j Hj).
    - apply (freq_hist_same s s' Epb Elbs Esn Elfc Edfc Ebfc). exact Xhist.
    - rewrite Eext. assumption.
    - intros t i. destruct t; cbn [tree_fc]; rewrite ?Elfc, ?Edfc, ?Ebfc; [apply (Xtfc TL i) | apply (Xtfc TD i) | apply (Xtfc TB i)].
    - intros t i. destruct t; cbn [tree_dl]; rewrite ?Eldl, ?Eddl, ?Ebdl; [apply (Xtdl TL i) | apply (Xtdl TD i) | apply (Xtdl TB i)].
    - intros i. rewrite Edep. apply Xdepth.
    - intros i Hi. rewrite Eblc. apply Xblc. exact Hi.
    - intros _. exact (fx_chain _ FX'). }
  assert (V' : SV c0 s').
  { destruct HK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kout & Kao & Kto & Ksum).
    constructor; rewrite ?Ein, ?Eout, ?Eao, ?Eto, ?Edt.
    - exact (sv_input _ _ V).
    - assumption.
    - rewrite Enin. exact (sv_inlen _ _ V).
    - assumption.
    - exact (sv_out _ _ V).
    - exact (sv_aout _ _ V).
    - exact (sv_grow _ _ V).
    - exact (sv_outb _ _ V).
    - assumption.
    - exact (sv_tout _ _ V).
    - exact (fx_ad _ FX').
    - exact (sv_dt _ _ V).
    - rewrite <- Ein. assumption. }
  split; [exact (conj (conj D' X') V')|].
  split; [unfold KV; rewrite EB, Ews, Ehs, Elbs; reflexivity|].
  split; [apply OUTLE_out; exact Eout|].
  split; [exact R'|]. split; [exact Eext|]. split; [exact HL'|]. split; [| split; [exact HW' | split; [exact SS' | split; [exact S1' | exact Ewms]]]].
  intros Hl'. split; [exact (HX' Hl') | exact (SL' Hl')].
Qed.

Section Fast.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hfl : 0 <= flush <= 5.
  Hypothesis HFB : FB_CALL.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Definition FTI (s : deflate_state) : Prop :=
    DC c0 s /\ KV s = KV s0 /\ ds_pending s = 0 /\ dmode s = 3 /\ ds_status s <> FINISH_STATE /\ OUTLE s0 s.

  Lemma FTI_facts : forall s, FTI s ->
    dwf s /\ DX s /\ SV c0 s
    /\ 512 <= ds_w_size s <= 32768 /\ 256 <= ds_hash_size s <= 65536 /\ 2048 <= ds_lit_bufsize s <= 32768
    /\ ds_prev_length s = 2 /\ ds_match_length s < MIN_MATCH /\ ds_match_available s = 0
    /\ 0 <= nsym s <= ds_lit_bufsize s - 2 /\ ds_sym_next s = 3 * nsym s /\ ds_sym_end s = (ds_lit_bufsize s - 1) * 3
    /\ 0 <= ds_strstart s /\ 0 <= ds_lookahead s /\ ds_strstart s + ds_lookahead s <= 2 * ds_w_size s
    /\ 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s.
  Proof.
    intros s (HDC & HK & Hp & Hm & Hst & Ho). pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
    pose proof (dx_fast _ X Hm) as [Hpl Hml]. pose proof (dx_notslow _ X ltac:(rewrite Hm; lia)) as Hma.
    pose proof (dx_nsym _ X). pose proof (dx_sn _ X). pose proof (df_symend _ D). pose proof (df_strstart _ D). pose proof (df_look _ D). pose proof (df_sl _ D).
    pose proof (dx_ext _ X ltac:(rewrite Hm; lia)) as He. rewrite Hma in He.
    repeat (split; [assumption|]). lia.
  Qed.

  Lemma fill_stage : forall s, FTI s ->
    let r := st_fill s flush in
    FTI (fst r) /\ lz_meas (fst r) = lz_meas s
    /\ 0 <= ds_lookahead s <= 2 * ds_w_size s
    /\ (ds_lookahead s < MIN_LOOKAHEAD -> fw_wf (ds_w_size s) (ds_hash_size s) s)
    /\ 0 <= ds_lookahead (fst r) <= 2 * ds_w_size s
    /\ ds_w_size (fst r) = ds_w_size s
    /\ (snd r = None -> 1 <= ds_lookahead (fst r)
                       /\ (ds_lookahead (fst r) < MIN_LOOKAHEAD -> ds_strstart (fst r) + ds_lookahead (fst r) <= 2 * ds_w_size s - 2))
    /\ (snd r = Some LBreak -> ds_lookahead (fst r) = 0)
    /\ (forall bs, snd r = Some (LRet bs) -> bs = need_more)
    /\ ds_strstart (fst r) + MIN_LOOKAHEAD <= 2 * ds_w_size s
    /\ snd r <> Some LCont.
  Proof.
    intros s HF r. subst r. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (FTI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    assert (Hwr : 0 <= ds_wrap s) by (pose proof (dx_wrapneg _ X); pose proof (df_wrap _ D); destruct (Z_lt_le_dec (ds_wrap s) 0); [exfalso; apply Hst; auto | lia]).
    assert (HW : fw_wf (ds_w_size s) (ds_hash_size s) s).
    { apply (dwf_fw_wf s D Hwr (sv_nin _ _ V) (sv_ain _ _ V) ltac:(rewrite (sv_input _ _ V); pose proof (sv_inlen _ _ V); lia)
             (sv_tin _ _ V) (sv_adler _ _ V) (sv_ib _ _ V)). }
    unfold st_fill.
    destruct (Z.ltb_spec (ds_lookahead s) MIN_LOOKAHEAD) as [Hlt|Hge].
    - destruct (DC_fill_window c0 s HC0w HDC ltac:(rewrite Hm; lia) Hst Hlt) as (HDC' & HK' & Ho' & R' & Eext & HL' & HX' & HW' & SS' & _).
      pose proof (fw_rest_fields _ _ R') as ((Est & _ & _ & _ & Epd & _) & (_ & _ & Elv & Esy & _) & _).
      pose proof (fill_window_keep s) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ksum).
      assert (HF' : FTI (fill_window s)).
      { split; [exact HDC'|]. split; [rewrite HK'; exact HK|]. split; [rewrite Epd; exact Hp|].
        split; [unfold dmode; rewrite Elv, Esy; exact Hm|]. split; [rewrite Est; exact Hst | exact (OUTLE_trans _ _ _ Ho Ho')]. }
      pose proof (wf_ws _ _ _ HW') as Ews'.
      destruct ((ds_lookahead (fill_window s) <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)) eqn:E1.
      + cbn [fst snd]. split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [lia|]. split; [intros _; exact HW|].
        split; [lia|]. split; [exact Ews'|]. split; [intros HH; discriminate HH|]. split; [intros HH; discriminate HH|].
        split; [intros bs Hbs; injection Hbs as <-; reflexivity|]. split; [clear - SS'; lia | intros HH; discriminate HH].
      + destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [E0|E0]; cbn [fst snd].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [lia|]. split; [intros _; exact HW|].
          split; [lia|]. split; [exact Ews'|]. split; [intros HH; discriminate HH|]. split; [intros _; exact E0|].
          split; [intros bs Hbs; discriminate Hbs|]. split; [clear - SS'; lia | intros HH; discriminate HH].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [lia|]. split; [intros _; exact HW|].
          split; [lia|]. split; [exact Ews'|]. split; [intros _; split; [lia | intros Hl; exact (proj2 (HX' Hl))]|].
          split; [intros HH; discriminate HH|]. split; [intros bs Hbs; discriminate Hbs|]. split; [clear - SS'; lia | intros HH; discriminate HH].
    - cbn [fst snd]. split; [exact HF|]. split; [reflexivity|]. split; [lia|]. split; [intros; lia|].
      split; [lia|]. split; [reflexivity|].
      split; [intros _; split; [unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hge; lia | intros; lia]|].
      split; [intros HH; discriminate HH|]. split; [intros bs Hbs; discriminate Hbs|]. split; [clear - Hge Hsl; lia | intros HH; discriminate HH].
  Qed.

  Definition TF (s : deflate_state) :=
    ((ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s, ds_level s, ds_strategy s),
     (ds_insert s, ds_w_size s, ds_prev_length s, ds_match_available s, ds_prev_match s, ds_matches s, ds_high_water s, ds_window_size s),
     (ds_block_start s, ds_wrap s, ds_status s, ds_lit_bufsize s, ds_bl_tree_fc s, ds_dyn_ltree_dl s, ds_dyn_dtree_dl s, ds_bl_tree_dl s),
     (ds_depth s, ds_bl_count s, ds_opt_len s, ds_static_len s, ds_hash_size s, ds_w_mask s, ds_hash_mask s, ds_hash_shift s),
     (ds_strm s, ds_pending s, ds_pending_out s, ds_bi_valid s, ds_bi_buf s, ds_last_flush s, ds_window s, KV s, ds_sym_end s),
     (ds_w_bits s, ds_hash_bits s, ds_pending_buf_size s, ds_gzhead s, ds_method s, ds_heap s)).

  Lemma TF_fields : forall a b, TF b = TF a ->
    (ds_good_match b = ds_good_match a /\ ds_max_lazy_match b = ds_max_lazy_match a /\ ds_nice_match b = ds_nice_match a
     /\ ds_max_chain_length b = ds_max_chain_length a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a)
    /\ (ds_insert b = ds_insert a /\ ds_w_size b = ds_w_size a /\ ds_prev_length b = ds_prev_length a /\ ds_match_available b = ds_match_available a
        /\ ds_prev_match b = ds_prev_match a /\ ds_matches b = ds_matches a /\ ds_high_water b = ds_high_water a /\ ds_window_size b = ds_window_size a)
    /\ (ds_block_start b = ds_block_start a /\ ds_wrap b = ds_wrap a /\ ds_status b = ds_status a /\ ds_lit_bufsize b = ds_lit_bufsize a
        /\ ds_bl_tree_fc b = ds_bl_tree_fc a /\ ds_dyn_ltree_dl b = ds_dyn_ltree_dl a /\ ds_dyn_dtree_dl b = ds_dyn_dtree_dl a /\ ds_bl_tree_dl b = ds_bl_tree_dl a)
    /\ (ds_depth b = ds_depth a /\ ds_bl_count b = ds_bl_count a /\ ds_opt_len b = ds_opt_len a /\ ds_static_len b = ds_static_len a
        /\ ds_hash_size b = ds_hash_size a /\ ds_w_mask b = ds_w_mask a /\ ds_hash_mask b = ds_hash_mask a /\ ds_hash_shift b = ds_hash_shift a)
    /\ (ds_strm b = ds_strm a /\ ds_pending b = ds_pending a /\ ds_pending_out b = ds_pending_out a /\ ds_bi_valid b = ds_bi_valid a
        /\ ds_bi_buf b = ds_bi_buf a /\ ds_last_flush b = ds_last_flush a /\ ds_window b = ds_window a /\ KV b = KV a /\ ds_sym_end b = ds_sym_end a)
    /\ (ds_w_bits b = ds_w_bits a /\ ds_hash_bits b = ds_hash_bits a /\ ds_pending_buf_size b = ds_pending_buf_size a /\ ds_gzhead b = ds_gzhead a
        /\ ds_method b = ds_method a /\ ds_heap b = ds_heap a).
  Proof.
    intros a b E. unfold TF in E.
    repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
    repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
    repeat split; assumption.
  Qed.

  Definition HREL (s1 s2 : deflate_state) : Prop :=
    TF s2 = TF s1 /\ ds_strstart s2 = ds_strstart s1 /\ ds_match_length s2 = ds_match_length s1 /\ ds_lookahead s2 = ds_lookahead s1
    /\ ds_sym_next s2 = ds_sym_next s1 /\ ds_match_start s2 = ds_match_start s1 /\ ds_pending_buf s2 = ds_pending_buf s1
    /\ ds_dyn_ltree_fc s2 = ds_dyn_ltree_fc s1 /\ ds_dyn_dtree_fc s2 = ds_dyn_dtree_fc s1
    /\ arr_len (ds_head s2) = arr_len (ds_head s1) /\ arr_len (ds_prev s2) = arr_len (ds_prev s1)
    /\ (forall i, 0 <= i < ds_hash_size s1 -> 0 <= arr_get (ds_head s2) i < 65536)
    /\ (forall i, 0 <= i < ds_w_size s1 -> 0 <= arr_get (ds_prev s2) i < 65536)
    /\ 0 <= ds_ins_h s2 < 65536
    /\ CHAIN s2 (ds_strstart s1) (ds_strstart s1).

  Lemma hash_stage : forall s1, FTI s1 -> 1 <= ds_lookahead s1 ->
    let r := st_hash s1 in
    HREL s1 (fst r)
    /\ (lm_cond (fst r) (snd r) = true ->
          Forall (fun c => 0 <= c < ds_strstart s1) (lm_visited (fst r) (snd r))
          /\ 1 <= snd r <= ds_strstart s1 - 1 /\ ds_strstart s1 - snd r <= ds_w_size s1 - MIN_LOOKAHEAD /\ MIN_MATCH <= ds_lookahead s1).
  Proof.
    intros s1 HF Hl1 r. subst r. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof (dx_chain _ X ltac:(rewrite Hm; lia)) as HC. pose proof (dx_insh _ X) as Hih.
    unfold st_hash.
    destruct (Z.leb_spec MIN_MATCH (ds_lookahead s1)) as [Big|Small].
    - pose proof (insert_string_facts s1 (ds_strstart s1)) as IF. cbv zeta in IF.
      destruct IF as (Ehh & Eih & Ehd & Epv & Estrm & Ewin & Elook & Estr & Ebs & Eml & Esn & Elfc & Edfc & Epd & Epb & Ebv & Ebb & Eins & Epl & Ems & Hh).
      specialize (Hh ltac:(rewrite (df_hmask _ D); lia)). rewrite (df_hmask _ D) in Hh.
      destruct (CHAIN_insert_string s1 (ds_strstart s1) (ds_strstart s1 - 1) (ds_strstart s1 - 1) (ds_w_bits s1) HC
                  (df_wsize _ D) ltac:(pose proof (df_wbits _ D); lia) (df_wmask _ D) (df_pl _ D) (df_hl _ D)
                  ltac:(rewrite (df_hmask _ D); lia) (df_hmask _ D) ltac:(lia)) as [HC2 Hhh].
      replace (Z.max (ds_strstart s1 - 1) (ds_strstart s1)) with (ds_strstart s1) in HC2 by lia.
      replace (Z.max (ds_strstart s1 - 1) (ds_strstart s1 - 1)) with (ds_strstart s1 - 1) in HC2 by lia.
      set (s2 := fst (insert_string s1 (ds_strstart s1))) in *. set (hh := snd (insert_string s1 (ds_strstart s1))) in *.
      split.
      + unfold HREL. rewrite Ehd, Epv, !arr_len_set.
        split; [subst s2; rewrite insert_string_fst; reflexivity|].
        split; [exact Estr|]. split; [exact Eml|]. split; [exact Elook|]. split; [exact Esn|]. split; [exact Ems|]. split; [exact Epb|].
        split; [exact Elfc|]. split; [exact Edfc|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros i Hi; rewrite arr_get_set; destruct (_ && _); [apply wrap16_range | apply (df_hb _ D); exact Hi]|].
        split; [intros i Hi; rewrite arr_get_set; destruct (_ && _); [apply (df_hb _ D); lia | apply (df_pb _ D); exact Hi]|].
        split; [rewrite Eih; lia|].
        eapply CHAIN_mono; [| | exact HC2]; lia.
      + intros Hlm. unfold lm_cond in Hlm. apply andb_prop in Hlm as [Hnz Hdist].
        assert (Hhh0 : hh <> 0) by (intros E0; rewrite E0 in Hnz; discriminate Hnz).
        assert (Hhh1 : 1 <= hh <= ds_strstart s1 - 1) by (destruct Hhh as [Z0|B]; [exfalso; exact (Hhh0 Z0) | exact B]).
        rewrite Estr in Hdist. apply Z.leb_le in Hdist. rewrite wrap32_id in Hdist by lia.
        split; [| split; [lia | split; [change (ds_w_size s2) with (ds_w_size s1) in Hdist; lia | exact Big]]].
        pose proof (lm_visited_bound s1 (ds_strstart s1) (ds_w_bits s1) HC (df_wsize _ D) ltac:(pose proof (df_wbits _ D); lia) (df_wmask _ D) (df_pl _ D) (df_hl _ D)
                      ltac:(rewrite (df_hmask _ D); lia) (df_hmask _ D) ltac:(lia) ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; lia)) as LV.
        cbv zeta in LV. fold s2 hh in LV. specialize (LV Hhh0 Estr). rewrite Estr in LV. exact LV.
    - cbn [fst snd]. split.
      + unfold HREL. repeat (split; [reflexivity|]).
        split; [intros i Hi; apply (df_hb _ D); exact Hi|].
        split; [intros i Hi; apply (df_pb _ D); exact Hi|].
        split; [exact Hih|]. eapply CHAIN_mono; [| | exact HC]; lia.
      + intros Hlm. exfalso. unfold lm_cond in Hlm. cbn in Hlm. discriminate Hlm.
  Qed.

  Lemma lm_curs_limit : forall f s cur ch bl nice limit se1 se,
    Forall (fun c => c = cur \/ limit < c) (lm_curs f s cur ch bl nice limit se1 se).
  Proof.
    induction f as [|f IH]; intros s cur ch bl nice limit se1 se; cbn [lm_curs].
    - constructor; [left; reflexivity | constructor].
    - constructor; [left; reflexivity|].
      destruct (longest_match_body s cur ch bl nice limit se1 se) as [[[[[[s' b'] se1'] se'] cur'] ch'] cont] eqn:E.
      destruct cont; [|constructor].
      destruct (lmb_cont _ _ _ _ _ _ _ _ _ _ _ _ _ _ E) as (_ & Hlt & _).
      eapply Forall_impl; [| apply IH]. intros c [-> | H]; right; [exact Hlt | exact H].
  Qed.

  Definition MREL (s1 s2 s3 : deflate_state) : Prop :=
    TF s3 = TF s2 /\ ds_strstart s3 = ds_strstart s2 /\ ds_lookahead s3 = ds_lookahead s2
    /\ ds_sym_next s3 = ds_sym_next s2 /\ ds_pending_buf s3 = ds_pending_buf s2
    /\ ds_dyn_ltree_fc s3 = ds_dyn_ltree_fc s2 /\ ds_dyn_dtree_fc s3 = ds_dyn_dtree_fc s2
    /\ ds_head s3 = ds_head s2 /\ ds_prev s3 = ds_prev s2 /\ ds_ins_h s3 = ds_ins_h s2
    /\ 0 <= ds_match_length s3 <= MAX_MATCH /\ 0 <= ds_match_start s3 < 2 ^ 32
    /\ (MIN_MATCH <= ds_match_length s3 ->
          ds_match_length s3 <= ds_lookahead s1 /\ 1 <= ds_strstart s1 - ds_match_start s3 <= ds_w_size s1 - MIN_LOOKAHEAD).

  Lemma match_stage : forall s1 s2 hh, FTI s1 -> 1 <= ds_lookahead s1 -> HREL s1 s2 ->
    (lm_cond s2 hh = true ->
       Forall (fun c => 0 <= c < ds_strstart s1) (lm_visited s2 hh)
       /\ 1 <= hh <= ds_strstart s1 - 1 /\ ds_strstart s1 - hh <= ds_w_size s1 - MIN_LOOKAHEAD /\ MIN_MATCH <= ds_lookahead s1) ->
    MREL s1 s2 (st_match s2 hh).
  Proof.
    intros s1 s2 hh HF Hl1 HR Hlm.
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    destruct HR as (T2 & Estr & Eml & Elook & Esn & Ems & Epb & Elfc & Edfc & Lh & Lp & Bh & Bp & Bih & HC2).
    pose proof (TF_fields _ _ T2) as ((_ & _ & _ & _ & _ & _) & (_ & Ews & Epl & _) & _).
    unfold st_match. destruct (lm_cond s2 hh) eqn:Elm.
    - destruct (Hlm eq_refl) as (LV & Hh1 & Hhd & Big).
      destruct (longest_match_facts s2 hh ltac:(rewrite Estr; lia) ltac:(rewrite Epl, Hpl; unfold MAX_MATCH; lia) ltac:(rewrite Elook; lia))
        as (ms & Efst & Hml3 & Hle & Hup & Hms).
      destruct (longest_match s2 hh) as [s3' ml]. cbn [fst snd] in *. subst s3'.
      assert (Hm : forall m, In m (lm_visited s2 hh) -> 1 <= ds_strstart s1 - m <= ds_w_size s1 - MIN_LOOKAHEAD).
      { intros m Hin. rewrite Forall_forall in LV. pose proof (LV m Hin) as Bm.
        unfold lm_visited in Hin. cbv zeta in Hin.
        match type of Hin with In m (lm_curs ?f ?s ?cur ?ch ?bl ?nice ?limit ?se1 ?se) =>
          pose proof (lm_curs_limit f s cur ch bl nice limit se1 se) as LL end.
        rewrite Forall_forall in LL. specialize (LL m Hin). cbv beta in LL.
        rewrite Estr, Ews in LL. unfold NIL in LL.
        destruct LL as [-> | LL]; [lia|].
        destruct (Z.ltb_spec (ds_w_size s1 - MIN_LOOKAHEAD) (ds_strstart s1)); unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia. }
      unfold MREL. destruct ms as [m|]; cbv beta iota; dsred.
      + repeat (split; [reflexivity|]).
        split; [exact Hml3|].
        split. { destruct Hms as [HH | (m' & Em & Hin)]; [discriminate HH|]. injection Em as ->. rewrite Forall_forall in LV. pose proof (LV m' Hin). lia. }
        intros H3. unfold MIN_MATCH in H3. split; [rewrite Elook in Hle; exact Hle|].
        destruct (Hup ltac:(rewrite Epl, Hpl; lia)) as (m' & Em & Hin). injection Em as ->. exact (Hm m' Hin).
      + repeat (split; [reflexivity|]).
        split; [exact Hml3|].
        split; [rewrite Ems; exact (df_ms _ D)|].
        intros H3. unfold MIN_MATCH in H3. exfalso. destruct (Hup ltac:(rewrite Epl, Hpl; lia)) as (m' & Em & _). discriminate Em.
    - unfold MREL. repeat (split; [reflexivity|]).
      split; [rewrite Eml; pose proof (dx_ml _ X); lia|].
      split; [rewrite Ems; exact (df_ms _ D)|].
      intros H3. exfalso. rewrite Eml in H3. unfold MIN_MATCH in *. lia.
  Qed.

  Definition IREL (s s' : deflate_state) : Prop :=
    TF s' = TF s /\ ds_strstart s' = ds_strstart s + ds_match_length s /\ ds_match_length s' = 0 /\ ds_lookahead s' = ds_lookahead s
    /\ ds_sym_next s' = ds_sym_next s /\ ds_match_start s' = ds_match_start s /\ ds_pending_buf s' = ds_pending_buf s
    /\ ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s /\ ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s
    /\ arr_len (ds_head s') = arr_len (ds_head s) /\ arr_len (ds_prev s') = arr_len (ds_prev s)
    /\ (forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head s') i < 65536)
    /\ (forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev s') i < 65536)
    /\ 0 <= ds_ins_h s' < 65536
    /\ CHAIN s' (ds_strstart s + ds_match_length s) (ds_strstart s + ds_match_length s).

  Lemma fast_insert_facts : forall n s k,
    ds_w_size s = 2 ^ k -> 0 <= k -> ds_w_mask s = ds_w_size s - 1 -> arr_len (ds_prev s) = ds_w_size s ->
    arr_len (ds_head s) = ds_hash_size s -> 0 <= ds_hash_mask s -> ds_hash_mask s = ds_hash_size s - 1 -> ds_hash_size s <= 65536 ->
    (forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head s) i < 65536) ->
    (forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev s) i < 65536) ->
    0 <= ds_ins_h s < 65536 ->
    1 <= ds_match_length s <= Z.of_nat n -> 0 <= ds_strstart s -> ds_strstart s + ds_match_length s < 2 ^ 16 ->
    CHAIN s (ds_strstart s) (ds_strstart s) ->
    IREL s (deflate_fast_insert n s).
  Proof.
    induction n as [|n IH]; intros s k Ews Hk Ewm Lp Lh Hm0 Ehm Hhs Bh Bp Bih Hml Hstr Hbnd HC; [lia|].
    rewrite deflate_fast_insert_step. cbv zeta. rewrite insl_eq.
    set (t := set_strstart s (ds_strstart s + 1)).
    pose proof (insert_string_facts t (ds_strstart s + 1)) as IF. cbv zeta in IF.
    destruct IF as (Ehh & Eih & Ehd & Epv & Estrm & Ewin & Elook & Estr & Ebs & Eml & Esn & Elfc & Edfc & Epd & Epb & Ebv & Ebb & Eins & Epl & Ems & Hh).
    specialize (Hh ltac:(subst t; dsred; lia)).
    assert (Hh2 : 0 <= update_hash t (ds_ins_h t) (arr_get (ds_window t) (ds_strstart s + 1 + (MIN_MATCH - 1))) <= ds_hash_size s - 1)
      by (revert Hh; subst t; dsred; rewrite Ehm; intros Hh; exact Hh).
    destruct (CHAIN_insert_string t (ds_strstart s + 1) (ds_strstart s) (ds_strstart s) k
                ltac:(apply (CHAIN_same s); subst t; dsred; try reflexivity; exact HC)
                ltac:(subst t; dsred; exact Ews) Hk ltac:(subst t; dsred; exact Ewm) ltac:(subst t; dsred; exact Lp) ltac:(subst t; dsred; exact Lh)
                ltac:(subst t; dsred; exact Hm0) ltac:(subst t; dsred; exact Ehm) ltac:(lia)) as [HC1 _].
    replace (Z.max (ds_strstart s) (ds_strstart s + 1)) with (ds_strstart s + 1) in HC1 by lia.
    replace (Z.max (ds_strstart s) (ds_strstart s)) with (ds_strstart s) in HC1 by lia.
    set (t1 := fst (insert_string t (ds_strstart s + 1))) in *.
    assert (Hh' : 0 <= ds_ins_h t1 < 65536) by (rewrite Eih; lia).
    assert (Bh1 : forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head t1) i < 65536).
    { intros i Hi. rewrite Ehd. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | subst t; dsred; apply Bh; exact Hi]. }
    assert (Bp1 : forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev t1) i < 65536).
    { intros i Hi. rewrite Epv. rewrite arr_get_set. destruct (_ && _); [revert Hh2; subst t; dsred; unfold update_hash; dsred; intros Hh2; apply Bh; lia | subst t; dsred; apply Bp; exact Hi]. }
    assert (Lh1 : arr_len (ds_head t1) = ds_hash_size s) by (rewrite Ehd, arr_len_set; subst t; dsred; exact Lh).
    assert (Lp1 : arr_len (ds_prev t1) = ds_w_size s) by (rewrite Epv, arr_len_set; subst t; dsred; exact Lp).
    assert (Tt1 : TF t1 = TF s /\ ds_strstart t1 = ds_strstart s + 1 /\ ds_match_length t1 = ds_match_length s /\ ds_lookahead t1 = ds_lookahead s
                  /\ ds_sym_next t1 = ds_sym_next s /\ ds_match_start t1 = ds_match_start s /\ ds_pending_buf t1 = ds_pending_buf s
                  /\ ds_dyn_ltree_fc t1 = ds_dyn_ltree_fc s /\ ds_dyn_dtree_fc t1 = ds_dyn_dtree_fc s
                  /\ ds_w_size t1 = ds_w_size s /\ ds_hash_size t1 = ds_hash_size s /\ ds_w_mask t1 = ds_w_mask s /\ ds_hash_mask t1 = ds_hash_mask s).
    { subst t1 t. rewrite insert_string_fst. dsred. repeat split; reflexivity. }
    destruct Tt1 as (Tt1 & St1 & Mt1 & Lt1 & Nt1 & MSt1 & Pt1 & LFt1 & DFt1 & Wt1 & Ht1 & WMt1 & HMt1).
    cbv zeta. dsred.
    destruct (Z.eqb_spec (ds_match_length s - 1) 0) as [Z0|Z0]; cbn [negb].
    -
      assert (Hml1 : ds_match_length s = 1) by lia.
      unfold IREL. dsred. rewrite Hml1.
      split; [exact Tt1|]. split; [exact St1|]. split; [lia|]. split; [exact Lt1|]. split; [exact Nt1|]. split; [exact MSt1|]. split; [exact Pt1|].
      split; [exact LFt1|]. split; [exact DFt1|].
      split; [rewrite Lh1; symmetry; exact Lh|]. split; [rewrite Lp1; symmetry; exact Lp|].
      split; [exact Bh1|]. split; [exact Bp1|]. split; [exact Hh'|].
      apply (CHAIN_same t1); dsred; try reflexivity. eapply CHAIN_mono; [| | exact HC1]; lia.
    - pose proof (IH (set_match_length t1 (ds_match_length s - 1)) k) as IH'. revert IH'. dsred. rewrite Wt1, WMt1, Ht1, HMt1, St1, Lh1, Lp1. intros IH'.
      specialize (IH' Ews Hk Ewm ltac:(reflexivity) ltac:(reflexivity) Hm0 Ehm Hhs Bh1 Bp1 Hh' ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(apply (CHAIN_same t1); dsred; try reflexivity; eapply CHAIN_mono; [| | exact HC1]; lia)).
      revert IH'. unfold IREL. dsred. rewrite Lh1, Lp1, Wt1, Ht1, St1, Lt1, Nt1, MSt1, Pt1, LFt1, DFt1.
      replace (ds_strstart s + 1 + (ds_match_length s - 1)) with (ds_strstart s + ds_match_length s) by lia.
      intros (T' & R'). split; [rewrite T'; revert Tt1; unfold TF; dsred; intros Tt1; exact Tt1|].
      rewrite Lh, Lp. exact R'.
  Qed.

  Definition TALLYF (s3 s4 : deflate_state) : Prop :=
    TF s4 = TF s3 /\ ds_strstart s4 = ds_strstart s3 /\ ds_lookahead s4 = ds_lookahead s3 /\ ds_match_length s4 = ds_match_length s3
    /\ ds_match_start s4 = ds_match_start s3 /\ ds_head s4 = ds_head s3 /\ ds_prev s4 = ds_prev s3 /\ ds_ins_h s4 = ds_ins_h s3
    /\ arr_len (ds_pending_buf s4) = arr_len (ds_pending_buf s3)
    /\ (forall i, 0 <= i < ds_lit_bufsize s3 * 4 -> 0 <= arr_get (ds_pending_buf s4) i < 256)
    /\ arr_len (ds_dyn_ltree_fc s4) = arr_len (ds_dyn_ltree_fc s3) /\ arr_len (ds_dyn_dtree_fc s4) = arr_len (ds_dyn_dtree_fc s3)
    /\ (forall i, 0 <= arr_get (ds_dyn_ltree_fc s4) i < 65536) /\ (forall i, 0 <= arr_get (ds_dyn_dtree_fc s4) i < 65536)
    /\ BQ s4 /\ nsym s4 = nsym s3 + 1 /\ ds_sym_next s4 = ds_sym_next s3 + 3.

  Lemma tally_common : forall s3 r,
    (forall j, 0 <= j < ds_lit_bufsize s3 * 4 -> 0 <= arr_get (ds_pending_buf s3) j < 256) ->
    (forall i, 0 <= arr_get (ds_dyn_ltree_fc s3) i < 65536) -> (forall i, 0 <= arr_get (ds_dyn_dtree_fc s3) i < 65536) ->
    tally_keep s3 r -> ds_sym_next r = ds_sym_next s3 + 3 ->
    (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf s3) j < 256) -> forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf r) j < 256) ->
    (exists k v, ds_dyn_ltree_fc r = arr_set (ds_dyn_ltree_fc s3) k (wrap16 v)) ->
    (ds_dyn_dtree_fc r = ds_dyn_dtree_fc s3 \/ exists k v, ds_dyn_dtree_fc r = arr_set (ds_dyn_dtree_fc s3) k (wrap16 v)) ->
    ds_bl_tree_fc r = ds_bl_tree_fc s3 -> ds_dyn_ltree_dl r = ds_dyn_ltree_dl s3 -> ds_dyn_dtree_dl r = ds_dyn_dtree_dl s3 -> ds_bl_tree_dl r = ds_bl_tree_dl s3 ->
    ds_depth r = ds_depth s3 -> ds_bl_count r = ds_bl_count s3 -> ds_opt_len r = ds_opt_len s3 -> ds_static_len r = ds_static_len s3 ->
    ds_hash_mask r = ds_hash_mask s3 -> ds_last_flush r = ds_last_flush s3 -> KV r = KV s3 ->
    (ds_w_bits r, ds_hash_bits r, ds_gzhead r, ds_method r, ds_heap r) = (ds_w_bits s3, ds_hash_bits s3, ds_gzhead s3, ds_method s3, ds_heap s3) ->
    BQ r -> nsym r = nsym s3 + 1 ->
    TALLYF s3 r.
  Proof.
    intros s3 r Bpb Bl Bd TK Esn Hpb (k1 & v1 & EL) ED Ebl Eldl Eddl Ebdl Edep Eblc Eol Esl Ehm Elf EKV Emisc HBQ EN.
    injection Emisc as Ewb Ehb Egz Eme Ehp.
    destruct TK as (Estrm & Ewin & Eprev & Ehead & Elook & Estr & Ebs & Eml & Ems & Epl & Epm & Ema & Epd & Epo & Ebv & Ebb & Elbs & Epbs & Ese
                    & Ews & Ehs & Ewm & Ehmk & Ehsh & Eih & Eins & Ewsz & Elv & Esy & Elz & Egm & Enm & Emc & Est & Ewr & Ehw & Emt & Lpb).
    unfold TALLYF. split.
    { unfold TF. rewrite Egm, Elz, Enm, Emc, Elv, Esy, Eins, Ews, Epl, Ema, Epm, Emt, Ehw, Ewsz, Ebs, Ewr, Est, Elbs, Ebl, Eldl, Eddl, Ebdl,
        Edep, Eblc, Eol, Esl, Ehs, Ewm, Ehm, Ehsh, Estrm, Epd, Epo, Ebv, Ebb, Elf, Ewin, EKV, Ese, Ewb, Ehb, Epbs, Egz, Eme, Ehp. reflexivity. }
    split; [exact Estr|]. split; [exact Elook|]. split; [exact Eml|]. split; [exact Ems|]. split; [exact Ehead|]. split; [exact Eprev|]. split; [exact Eih|].
    split; [exact Lpb|].
    split; [apply Hpb; exact Bpb|].
    split; [rewrite EL, arr_len_set; reflexivity|].
    split; [destruct ED as [-> | (k2 & v2 & ->)]; [| rewrite arr_len_set]; reflexivity|].
    split; [intros i; rewrite EL, arr_get_set; destruct (_ && _); [apply wrap16_range | apply Bl]|].
    split; [intros i; destruct ED as [-> | (k2 & v2 & ->)]; [apply Bd | rewrite arr_get_set; destruct (_ && _); [apply wrap16_range | apply Bd]]|].
    split; [exact HBQ|]. split; [exact EN | exact Esn].
  Qed.

  Lemma DX_BQ : forall s, DX s -> BQ s.
  Proof. intros s X. split; [exact (dx_sn _ X)|]. split; [pose proof (dx_nsym _ X); lia|]. split; [exact (dx_syms _ X) | exact (dx_hist _ X)]. Qed.

  Lemma tally_lit_stage : forall s1 s2 s3, FTI s1 -> HREL s1 s2 -> MREL s1 s2 s3 ->
    let r := tr_tally_lit s3 (arr_get (ds_window s3) (ds_strstart s3)) in
    TALLYF s3 (fst r) /\ snd r = (ds_sym_next s3 + 3 =? ds_sym_end s3).
  Proof.
    intros s1 s2 s3 HF HR MR r. subst r.
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    destruct HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    destruct MR as (T3 & Estr3 & Elook3 & Esn3 & Epb3 & Elfc3 & Edfc3 & Ehd3 & Epv3 & Eih3 & Hml3 & Hms3 & Hdist3).
    pose proof (TF_fields _ _ T2) as ((_ & _ & _ & _ & Elv2 & Esy2) & (_ & Ews2 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs2 & Ebl2 & _) & _ & (Estrm2 & Epd2 & Epo2 & Ebv2 & _ & _ & _ & EKV2 & Ese2) & _).
    pose proof (TF_fields _ _ T3) as ((_ & _ & _ & _ & Elv3 & Esy3) & (_ & Ews3 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs3 & Ebl3 & _) & _ & (Estrm3 & Epd3 & Epo3 & Ebv3 & _ & _ & _ & EKV3 & Ese3) & _).
    pose proof (tally_lit_facts s3 (arr_get (ds_window s3) (ds_strstart s3))) as (TK & Esn & Ebf & Edt & Ebt & Elt & Rl & Rp). cbv zeta in *.
    assert (BQ3 : BQ s3).
    { apply (BQ_same s1); [rewrite Epb3, Epb2 | rewrite Elbs3, Elbs2 | rewrite Esn3, Esn2 | rewrite Elfc3, Elfc2 | rewrite Edfc3, Edfc2 | rewrite Ebl3, Ebl2 |]; try reflexivity.
      exact (DX_BQ s1 X). }
    assert (N3 : nsym s3 = nsym s1) by (unfold nsym; rewrite Esn3, Esn2; reflexivity).
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL.
    destruct (BQ_tally_lit s3 BQ3 ltac:(rewrite Elbs3, Elbs2, Esn3, Esn2, Epb3, Epb2, (df_bl _ D); lia) ltac:(rewrite Elbs3, Elbs2; lia)
                ltac:(rewrite N3; lia) ltac:(rewrite Elfc3, Elfc2; unfold L_CODES; lia) (arr_get (ds_window s3) (ds_strstart s3))) as (BQ4 & N4 & _).
    cbv zeta in BQ4, N4.
    split; [| exact Ebf].
    destruct TK as (Estrm & Ewin & Eprev & Ehead & Elook & Estr & Ebs & Eml & Ems & Epl & Epm & Ema & Epd & Epo & Ebv & Ebb & Elbs & Epbs & Ese
                    & Ews & Ehs & Ewm & Ehmk & Ehsh & Eih & Eins & Ewsz & Elv & Esy & Elz & Egm & Enm & Emc & Est & Ewr & Ehw & Emt & Lpb).
    eapply tally_common.
    - rewrite Elbs3, Elbs2, Epb3, Epb2. exact (df_bb _ D).
    - rewrite Elfc3, Elfc2. exact (dx_tfc _ X DeflateState.TL).
    - rewrite Edfc3, Edfc2. exact (dx_tfc _ X DeflateState.TD).
    - exact (proj1 (tally_lit_facts s3 (arr_get (ds_window s3) (ds_strstart s3)))).
    - exact Esn.
    - exact Rp.
    - eexists. eexists. exact Elt.
    - left. exact Edt.
    - exact Ebt.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact Ehmk.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact BQ4.
    - exact N4.
  Qed.

  Lemma tally_dist_stage : forall s1 s2 s3, FTI s1 -> HREL s1 s2 -> MREL s1 s2 s3 -> MIN_MATCH <= ds_match_length s3 ->
    let r := tr_tally_dist s3 (wrap32 (ds_strstart s3 - ds_match_start s3)) (ds_match_length s3 - MIN_MATCH) in
    TALLYF s3 (fst r) /\ snd r = (ds_sym_next s3 + 3 =? ds_sym_end s3).
  Proof.
    intros s1 s2 s3 HF HR MR H3 r. subst r.
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    destruct HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    destruct MR as (T3 & Estr3 & Elook3 & Esn3 & Epb3 & Elfc3 & Edfc3 & Ehd3 & Epv3 & Eih3 & Hml3 & Hms3 & Hdist3).
    pose proof (TF_fields _ _ T2) as ((_ & _ & _ & _ & Elv2 & Esy2) & (_ & Ews2 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs2 & Ebl2 & _) & _ & (Estrm2 & Epd2 & Epo2 & Ebv2 & _ & _ & _ & EKV2 & Ese2) & _).
    pose proof (TF_fields _ _ T3) as ((_ & _ & _ & _ & Elv3 & Esy3) & (_ & Ews3 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs3 & Ebl3 & _) & _ & (Estrm3 & Epd3 & Epo3 & Ebv3 & _ & _ & _ & EKV3 & Ese3) & _).
    destruct (Hdist3 H3) as [Hmll Hd]. rewrite Estr3, Estr2.
    rewrite wrap32_id by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hd; lia).
    set (dist := ds_strstart s1 - ds_match_start s3). set (len := ds_match_length s3 - MIN_MATCH).
    pose proof (tally_dist_facts s3 dist len) as (TK & Esn & Ebf & Ebt & Rl & Rd & Rp). cbv zeta in *.
    assert (BQ3 : BQ s3).
    { apply (BQ_same s1); [rewrite Epb3, Epb2 | rewrite Elbs3, Elbs2 | rewrite Esn3, Esn2 | rewrite Elfc3, Elfc2 | rewrite Edfc3, Edfc2 | rewrite Ebl3, Ebl2 |]; try reflexivity.
      exact (DX_BQ s1 X). }
    assert (N3 : nsym s3 = nsym s1) by (unfold nsym; rewrite Esn3, Esn2; reflexivity).
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL.
    destruct (BQ_tally_dist s3 BQ3 ltac:(rewrite Elbs3, Elbs2, Esn3, Esn2, Epb3, Epb2, (df_bl _ D); lia) ltac:(rewrite Elbs3, Elbs2; lia)
                ltac:(rewrite N3; lia) ltac:(rewrite Elfc3, Elfc2; unfold L_CODES; lia) ltac:(rewrite Edfc3, Edfc2; unfold D_CODES; lia)
                dist len ltac:(subst dist; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hd; lia)) as (BQ4 & N4 & _).
    cbv zeta in BQ4, N4.
    pose proof (tally_dist_fields s3 dist len) as (_ & _ & _ & Elt & Edt & _). cbv zeta in Elt, Edt.
    split; [| exact Ebf].
    destruct TK as (Estrm & Ewin & Eprev & Ehead & Elook & Estr & Ebs & Eml & Ems & Epl & Epm & Ema & Epd & Epo & Ebv & Ebb & Elbs & Epbs & Ese
                    & Ews & Ehs & Ewm & Ehmk & Ehsh & Eih & Eins & Ewsz & Elv & Esy & Elz & Egm & Enm & Emc & Est & Ewr & Ehw & Emt & Lpb).
    eapply tally_common.
    - rewrite Elbs3, Elbs2, Epb3, Epb2. exact (df_bb _ D).
    - rewrite Elfc3, Elfc2. exact (dx_tfc _ X DeflateState.TL).
    - rewrite Edfc3, Edfc2. exact (dx_tfc _ X DeflateState.TD).
    - exact (proj1 (tally_dist_facts s3 dist len)).
    - exact Esn.
    - exact Rp.
    - eexists. eexists. exact Elt.
    - right. eexists. eexists. exact Edt.
    - exact Ebt.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact Ehmk.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact BQ4.
    - exact N4.
  Qed.

  Definition TREL (s3 s7 : deflate_state) (adv : Z) : Prop :=
    TF s7 = TF s3 /\ ds_strstart s7 = ds_strstart s3 + adv /\ ds_lookahead s7 = ds_lookahead s3 - adv
    /\ 0 <= ds_match_length s7 < MIN_MATCH /\ 0 <= ds_match_start s7 < 2 ^ 32
    /\ arr_len (ds_pending_buf s7) = arr_len (ds_pending_buf s3)
    /\ (forall i, 0 <= i < ds_lit_bufsize s3 * 4 -> 0 <= arr_get (ds_pending_buf s7) i < 256)
    /\ arr_len (ds_dyn_ltree_fc s7) = arr_len (ds_dyn_ltree_fc s3) /\ arr_len (ds_dyn_dtree_fc s7) = arr_len (ds_dyn_dtree_fc s3)
    /\ (forall i, 0 <= arr_get (ds_dyn_ltree_fc s7) i < 65536) /\ (forall i, 0 <= arr_get (ds_dyn_dtree_fc s7) i < 65536)
    /\ BQ s7 /\ nsym s7 = nsym s3 + 1 /\ ds_sym_next s7 = ds_sym_next s3 + 3
    /\ arr_len (ds_head s7) = arr_len (ds_head s3) /\ arr_len (ds_prev s7) = arr_len (ds_prev s3)
    /\ (forall i, 0 <= i < ds_hash_size s3 -> 0 <= arr_get (ds_head s7) i < 65536)
    /\ (forall i, 0 <= i < ds_w_size s3 -> 0 <= arr_get (ds_prev s7) i < 65536)
    /\ 0 <= ds_ins_h s7 < 65536
    /\ CHAIN s7 (ds_strstart s7 - 1) (ds_strstart s7 - 1).

  Lemma tally_stage : forall s1 s2 s3, FTI s1 -> 1 <= ds_lookahead s1 -> HREL s1 s2 -> MREL s1 s2 s3 ->
    let r := st_tally s3 in
    (exists adv, TREL s3 (fst r) adv /\ 1 <= adv /\ adv <= ds_lookahead s1 /\ adv <= 258
                 /\ (adv = 1 \/ adv = ds_match_length s3 /\ MIN_MATCH <= adv))
    /\ snd r = (ds_sym_next s3 + 3 =? ds_sym_end s3).
  Proof.
    intros s1 s2 s3 HF Hl1 HR MR r. subst r.
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    pose proof MR as (T3 & Estr3 & Elook3 & Esn3 & Epb3 & Elfc3 & Edfc3 & Ehd3 & Epv3 & Eih3 & Hml3 & Hms3 & Hdist3).
    pose proof (TF_fields _ _ T2) as ((_ & _ & _ & _ & Elv2 & Esy2) & (_ & Ews2 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs2 & Ebl2 & _) & (_ & _ & _ & _ & Ehs2 & Ewm2 & Ehm2 & _) & (Estrm2 & Epd2 & Epo2 & Ebv2 & _ & _ & _ & EKV2 & Ese2) & _).
    pose proof (TF_fields _ _ T3) as ((_ & _ & _ & _ & Elv3 & Esy3) & (_ & Ews3 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs3 & Ebl3 & _) & (_ & _ & _ & _ & Ehs3 & Ewm3 & Ehm3 & _) & (Estrm3 & Epd3 & Epo3 & Ebv3 & _ & _ & _ & EKV3 & Ese3) & _).
    unfold st_tally.
    destruct (Z.leb_spec MIN_MATCH (ds_match_length s3)) as [H3|H3].
    -
      destruct (tally_dist_stage s1 s2 s3 HF HR MR H3) as [TY Ebf]. cbv zeta in TY, Ebf.
      unfold st_dist. destruct (tr_tally_dist s3 _ _) as [s4 bf]. cbn [fst snd] in TY, Ebf |- *.
      split; [| exact Ebf].
      destruct TY as (T4 & Estr4 & Elook4 & Eml4 & Ems4 & Ehd4 & Epv4 & Eih4 & Lpb4 & Bpb4 & Llt4 & Ldt4 & Blt4 & Bdt4 & BQ4 & N4 & Esn4).
      pose proof (TF_fields _ _ T4) as (_ & (_ & Ews4 & _) & (_ & _ & _ & Elbs4 & _) & (_ & _ & _ & _ & Ehs4 & Ewm4 & Ehm4 & _) & _).
      destruct (Hdist3 H3) as [Hmll Hd].
      set (s5 := set_lookahead s4 (ds_lookahead s4 - ds_match_length s4)).
      exists (ds_match_length s3).
      split; [| unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia].
      assert (HC5 : CHAIN s5 (ds_strstart s1) (ds_strstart s1)).
      { apply (CHAIN_same s2); subst s5; dsred; rewrite ?Ehd4, ?Epv4, ?Ehd3, ?Epv3, ?Ehs4, ?Ehs3, ?Ews4, ?Ews3, ?Ewm4, ?Ewm3; try reflexivity. exact HC2. }
      destruct (ins_cond s5) eqn:Eic.
      +
        unfold st_ins.
        set (t := set_match_length s5 (ds_match_length s5 - 1)).
        assert (Hmlt : ds_match_length t = ds_match_length s3 - 1) by (subst t s5; dsred; rewrite Eml4; reflexivity).
        pose proof (fast_insert_facts (Z.to_nat (ds_match_length t)) t (ds_w_bits s1)) as IF.
        assert (Ewst : ds_w_size t = ds_w_size s1) by (subst t s5; dsred; rewrite Ews4, Ews3, Ews2; reflexivity).
        assert (Ehst : ds_hash_size t = ds_hash_size s1) by (subst t s5; dsred; rewrite Ehs4, Ehs3, Ehs2; reflexivity).
        specialize (IF ltac:(rewrite Ewst; exact (df_wsize _ D)) ltac:(pose proof (df_wbits _ D); lia)
                       ltac:(subst t s5; dsred; rewrite Ewm4, Ewm3, Ewm2, Ews4, Ews3, Ews2; exact (df_wmask _ D))
                       ltac:(subst t s5; dsred; rewrite Epv4, Epv3, Ews4, Ews3, Ews2, Lp2; exact (df_pl _ D))
                       ltac:(subst t s5; dsred; rewrite Ehd4, Ehd3, Ehs4, Ehs3, Ehs2, Lh2; exact (df_hl _ D))
                       ltac:(subst t s5; dsred; rewrite Ehm4, Ehm3, Ehm2, (df_hmask _ D); lia)
                       ltac:(subst t s5; dsred; rewrite Ehm4, Ehm3, Ehm2, Ehs4, Ehs3, Ehs2; exact (df_hmask _ D))
                       ltac:(rewrite Ehst; lia)
                       ltac:(rewrite Ehst; subst t s5; dsred; rewrite Ehd4, Ehd3; exact Bh2)
                       ltac:(rewrite Ewst; subst t s5; dsred; rewrite Epv4, Epv3; exact Bp2)
                       ltac:(subst t s5; dsred; rewrite Eih4, Eih3; exact Bih2)
                       ltac:(rewrite Hmlt, Z2Nat.id by (unfold MIN_MATCH in H3; lia); unfold MIN_MATCH in H3; lia)
                       ltac:(subst t s5; dsred; rewrite Estr4, Estr3, Estr2; lia)
                       ltac:(subst t s5; dsred; rewrite Estr4, Estr3, Estr2, Eml4; unfold MIN_MATCH in H3; lia)
                       ltac:(apply (CHAIN_same s5); subst t s5; dsred; try reflexivity; rewrite Estr4, Estr3, Estr2; exact HC5)).
        set (u := deflate_fast_insert (Z.to_nat (ds_match_length t)) t) in *.
        destruct IF as (Tu & Estru & Emlu & Elooku & Esnu & Emsu & Epbu & Elfcu & Edfcu & Lhu & Lpu & Bhu & Bpu & Bihu & HCu).
        assert (Et : TF t = TF s3 /\ ds_strstart t = ds_strstart s3 /\ ds_lookahead t = ds_lookahead s3 - ds_match_length s3
                     /\ ds_match_start t = ds_match_start s3 /\ ds_pending_buf t = ds_pending_buf s4
                     /\ ds_dyn_ltree_fc t = ds_dyn_ltree_fc s4 /\ ds_dyn_dtree_fc t = ds_dyn_dtree_fc s4
                     /\ ds_head t = ds_head s3 /\ ds_prev t = ds_prev s3 /\ ds_sym_next t = ds_sym_next s4 /\ ds_lit_bufsize t = ds_lit_bufsize s4
                     /\ ds_bl_tree_fc t = ds_bl_tree_fc s4).
        { subst t s5. dsred. rewrite Estr4, Elook4, Eml4, Ems4, Ehd4, Epv4. repeat split; try reflexivity. rewrite <- T4. reflexivity. }
        destruct Et as (Tt & Estrt & Elookt & Emst & Epbt & Elfct & Edfct & Ehdt & Epvt & Esnt & Elbst & Eblt).
        unfold TREL. dsred.
        split; [rewrite <- Tt, <- Tu; reflexivity|].
        split; [rewrite Estru, Estrt, Hmlt; lia|].
        split; [rewrite Elooku, Elookt; reflexivity|].
        split; [unfold MIN_MATCH; lia|].
        split; [rewrite Emsu, Emst; exact Hms3|].
        split; [rewrite Epbu, Epbt; exact Lpb4|].
        split; [rewrite Epbu, Epbt; exact Bpb4|].
        split; [rewrite Elfcu, Elfct; exact Llt4|]. split; [rewrite Edfcu, Edfct; exact Ldt4|].
        split; [rewrite Elfcu, Elfct; exact Blt4|]. split; [rewrite Edfcu, Edfct; exact Bdt4|].
        split; [apply (BQ_same u); dsred; try reflexivity; apply (BQ_same s4); rewrite ?Epbu, ?Epbt, ?Esnu, ?Esnt, ?Elfcu, ?Elfct, ?Edfcu, ?Edfct; try reflexivity;
                [pose proof (TF_fields _ _ Tu) as (_ & _ & (_ & _ & _ & L1 & _) & _); rewrite L1, Elbst; reflexivity
                | pose proof (TF_fields _ _ Tu) as (_ & _ & (_ & _ & _ & _ & B1 & _) & _); rewrite B1, Eblt; reflexivity
                | exact BQ4]|].
        split; [unfold nsym; dsred; rewrite Esnu, Esnt; unfold nsym in N4; exact N4|].
        split; [rewrite Esnu, Esnt; exact Esn4|].
        split; [rewrite Lhu, Ehdt; reflexivity|]. split; [rewrite Lpu, Epvt; reflexivity|].
        split; [rewrite Ehs3, Ehs2, <- Ehst; exact Bhu|]. split; [rewrite Ews3, Ews2, <- Ewst; exact Bpu|].
        split; [exact Bihu|].
        apply (CHAIN_same u); dsred; try reflexivity.
        replace (ds_strstart u + 1 - 1) with (ds_strstart t + ds_match_length t) by lia. exact HCu.
      +
        unfold st_noins, TREL. subst s5. dsred.
        rewrite Estr4, Eml4, Elook4, Ems4, Ehd4, Epv4.
        split; [rewrite <- T4; reflexivity|].
        split; [reflexivity|]. split; [lia|]. split; [unfold MIN_MATCH; lia|]. split; [exact Hms3|].
        split; [exact Lpb4|]. split; [exact Bpb4|]. split; [exact Llt4|]. split; [exact Ldt4|]. split; [exact Blt4|]. split; [exact Bdt4|].
        split; [apply (BQ_same s4); dsred; try reflexivity; exact BQ4|].
        split; [unfold nsym in *; dsred; exact N4|]. split; [exact Esn4|].
        split; [rewrite Ehd3; reflexivity|]. split; [rewrite Epv3; reflexivity|].
        split; [rewrite Ehd3, Ehs3, Ehs2; exact Bh2|]. split; [rewrite Epv3, Ews3, Ews2; exact Bp2|].
        split.
        { match goal with |- 0 <= update_hash ?st ?h ?c < 65536 =>
            pose proof (update_hash_range st h c ltac:(dsred; rewrite Ehm4, Ehm3, Ehm2, (df_hmask _ D); lia)) as R end.
          revert R. dsred. rewrite Ehm4, Ehm3, Ehm2, (df_hmask _ D). intros R. lia. }
        apply (CHAIN_same s2); dsred; rewrite ?Ehd4, ?Ehd3, ?Epv4, ?Epv3, ?Ehs4, ?Ehs3, ?Ews4, ?Ews3, ?Ewm4, ?Ewm3; try reflexivity.
        eapply CHAIN_mono; [| | exact HC2]; rewrite Estr3, Estr2; unfold MIN_MATCH in H3; lia.
    -
      destruct (tally_lit_stage s1 s2 s3 HF HR MR) as [TY Ebf]. cbv zeta in TY, Ebf.
      unfold st_lit. destruct (tr_tally_lit s3 _) as [s4 bf]. cbn [fst snd] in TY, Ebf |- *.
      split; [| exact Ebf].
      destruct TY as (T4 & Estr4 & Elook4 & Eml4 & Ems4 & Ehd4 & Epv4 & Eih4 & Lpb4 & Bpb4 & Llt4 & Ldt4 & Blt4 & Bdt4 & BQ4 & N4 & Esn4).
      exists 1. split; [| lia].
      unfold TREL. dsred. rewrite Estr4, Elook4, Eml4, Ems4, Ehd4, Epv4, Eih4.
      split; [rewrite <- T4; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact Hms3|].
      split; [exact Lpb4|]. split; [exact Bpb4|]. split; [exact Llt4|]. split; [exact Ldt4|]. split; [exact Blt4|]. split; [exact Bdt4|].
      split; [apply (BQ_same s4); dsred; try reflexivity; exact BQ4|].
      split; [unfold nsym in *; dsred; exact N4|]. split; [exact Esn4|].
      split; [rewrite Ehd3; reflexivity|]. split; [rewrite Epv3; reflexivity|].
      split; [rewrite Ehd3, Ehs3, Ehs2; exact Bh2|]. split; [rewrite Epv3, Ews3, Ews2; exact Bp2|].
      split; [rewrite Eih3; exact Bih2|].
      pose proof (TF_fields _ _ T4) as (_ & (_ & Ews4 & _) & _ & (_ & _ & _ & _ & Ehs4 & Ewm4 & _) & _).
      apply (CHAIN_same s2); dsred; rewrite ?Ehd4, ?Ehd3, ?Epv4, ?Epv3, ?Ehs4, ?Ehs3, ?Ews4, ?Ews3, ?Ewm4, ?Ewm3; try reflexivity.
      replace (ds_strstart s3 + 1 - 1) with (ds_strstart s1) by lia. exact HC2.
  Qed.

  Lemma trip_end : forall s1 s2 s3 s7 adv,
    FTI s1 -> 1 <= ds_lookahead s1 ->
    (ds_lookahead s1 < MIN_LOOKAHEAD -> ds_strstart s1 + ds_lookahead s1 <= 2 * ds_w_size s1 - 2) ->
    HREL s1 s2 -> MREL s1 s2 s3 -> TREL s3 s7 adv -> 1 <= adv <= ds_lookahead s1 -> adv <= 258 ->
    dwf s7 /\ SV c0 s7 /\ KV s7 = KV s0 /\ ds_pending s7 = 0 /\ dmode s7 = 3 /\ ds_status s7 <> FINISH_STATE /\ OUTLE s0 s7
    /\ ds_strm s7 = ds_strm s1 /\ lz_meas s7 < lz_meas s1 /\ 0 <= ds_lookahead s7 <= 2 * ds_w_size s1
    /\ nsym s7 = nsym s1 + 1 /\ ds_sym_next s7 = ds_sym_next s1 + 3 /\ ds_sym_end s7 = ds_sym_end s1 /\ ds_lit_bufsize s7 = ds_lit_bufsize s1
    /\ (nsym s7 <= ds_lit_bufsize s7 - 2 -> DX s7)
    /\ fb_entry s7 0
    /\ DXX s7 /\ TF s7 = TF s1
    /\ CHAIN s7 (ds_strstart s7 - 1) (ds_strstart s7 - 1) /\ 0 <= ds_ins_h s7 < 65536 /\ ds_match_length s7 < MIN_MATCH.
  Proof.
    intros s1 s2 s3 s7 adv HF Hl1 Hslack HR MR TR Hadv Hadv2.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    pose proof MR as (T3 & Estr3 & Elook3 & Esn3 & Epb3 & Elfc3 & Edfc3 & Ehd3 & Epv3 & Eih3 & Hml3 & Hms3 & Hdist3).
    destruct TR as (T7 & Estr7 & Elook7 & Hml7 & Hms7 & Lpb7 & Bpb7 & Llt7 & Ldt7 & Blt7 & Bdt7 & BQ7 & N7 & Esn7 & Lh7 & Lp7 & Bh7 & Bp7 & Bih7 & HC7).
    pose proof (TF_fields _ _ T2) as (_ & (_ & Ews2 & _) & (_ & _ & _ & Elbs2 & _) & (_ & _ & _ & _ & Ehs2 & _) & _).
    pose proof (TF_fields _ _ T3) as (_ & (_ & Ews3 & _) & (_ & _ & _ & Elbs3 & _) & (_ & _ & _ & _ & Ehs3 & _) & _).
    assert (T71 : TF s7 = TF s1) by (rewrite T7, T3, T2; reflexivity).
    pose proof (TF_fields _ _ T71) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Epl & Ema & Epm & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                        & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
    rewrite Estr3, Estr2 in Estr7. rewrite Elook3, Elook2 in Elook7.
    assert (N71 : nsym s7 = nsym s1 + 1) by (rewrite N7; unfold nsym; rewrite Esn3, Esn2; reflexivity).
    assert (Esn71 : ds_sym_next s7 = ds_sym_next s1 + 3) by (rewrite Esn7, Esn3, Esn2; reflexivity).
    assert (Em7 : dmode s7 = 3) by (unfold dmode; rewrite Elv, Esy; exact Hm).
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL. destruct TL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    assert (D7 : dwf s7).
    { destruct D; constructor; rewrite ?Est, ?Ewr, ?Elbs, ?Ebl, ?Eldl, ?Eddl, ?Ebdl, ?Edep, ?Eblc, ?Ehs, ?Ewm, ?Ehm, ?Ehsh, ?Epd, ?Epo, ?Ebv, ?Ebb, ?Elf, ?Ewin,
        ?Ese, ?Ewb, ?Ehb, ?Epbs, ?Egz, ?Eme, ?Elv, ?Esy, ?Ews, ?Eins, ?Ewsz, ?Ehw, ?Estr7, ?Elook7; try assumption.
      all: try (pose proof (KV_fields _ _ EKV) as (_ & _ & _ & KB); congruence).
      - unfold deflateStateCheck in *. rewrite Est. assumption.
      - unfold tree_lens. rewrite Llt7, Ldt7, Elfc3, Edfc3, Elfc2, Edfc2, Ebl, Eldl, Eddl, Ebdl, Eblc, Ehp, Edep. repeat split; assumption.
      - clear - Hstr Hadv Hsl Sw Hlook. lia.
      - clear - Hadv df_ins. lia.
      - clear - Hadv. lia.
      - clear - Hsl. lia.
      - clear - Bih7. lia.
      - rewrite Ews3, Ews2 in Bp7. exact Bp7.
      - rewrite Ehs3, Ehs2 in Bh7. exact Bh7.
      - rewrite Elbs3, Elbs2 in Bpb7. exact Bpb7. }
    assert (V7 : SV c0 s7) by (apply (SV_strm c0 s1); [exact Estrm | exact V]).
    pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl. pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc.
    destruct BQ7 as (Q1 & Q2 & Q3 & Q4).
    assert (Htfc7 : forall t i, 0 <= arr_get (tree_fc s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_fc]; [apply Blt7 | apply Bdt7 | rewrite Ebl; apply (Xtfc DeflateState.TB i)]. }
    assert (Htdl7 : forall t i, 0 <= arr_get (tree_dl s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_dl]; rewrite ?Eldl, ?Eddl, ?Ebdl; [apply (Xtdl DeflateState.TL i) | apply (Xtdl DeflateState.TD i) | apply (Xtdl DeflateState.TB i)]. }
    assert (X7 : nsym s7 <= ds_lit_bufsize s7 - 2 -> DX s7).
    { intros Hn7. pose proof X as X'. destruct X'; constructor; rewrite ?Em7, ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Esy, ?Eins, ?Ews, ?Epl, ?Ema, ?Epm, ?Emt, ?Ehw, ?Ewsz, ?Ebs, ?Ewr, ?Est,
        ?Elbs, ?Eol, ?Esl, ?Epd, ?Epo, ?Ebv, ?Estr7, ?Elook7, ?N71; try assumption.
      - clear - Hml7. unfold MIN_MATCH, MAX_MATCH in *. lia.
      - pose proof (RefDeflSafeI1.dx_matches _ X) as HM. clear - HM. lia.
      - intros _. split; [exact Hpl | exact (proj2 Hml7)].
      - intros _. exact Hma.
      - intros HH. discriminate HH.
      - intros HH. discriminate HH.
      - intros HH. exfalso. exact (Hst HH).
      - rewrite Q1, N71. reflexivity.
      - revert Hn7. rewrite N71, ?Elbs. clear - Hn. intros Hn7. lia.
      - rewrite <- N71. exact Q3.
      - intros _. rewrite Hma. clear - Hext Hadv Hadv2 Hn. lia.
      - rewrite Edep. exact Xdepth.
      - intros i Hi. rewrite Eblc. apply Xblc. exact Hi.
      - intros _. rewrite <- Estr7. exact HC7. }
    assert (FE7 : fb_entry s7 0).
    { pose proof (df_pend _ D) as Pd. pose proof (df_bi _ D) as Bi. pose proof (dx_biv _ X) as Bv. pose proof (dx_pout0 _ X Hp) as Po.
      pose proof (sv_dt _ _ V) as Dt. pose proof (sv_tout _ _ V) as To. pose proof (sv_aout _ _ V) as Ao. pose proof (sv_out _ _ V) as Ou.
      pose proof (c0_out _ HC0w) as O0. pose proof (c0_aout _ HC0w) as A0. rewrite O0 in Ou. unfold zlen in Ou. cbn [length Z.of_nat] in Ou.
      pose proof (zlen_nonneg (cs_out_rev (ds_strm s1))) as Zl. unfold zlen in Zl.
      pose proof (df_level _ D) as Lv. pose proof (df_strategy _ D) as Sy. unfold Z_FIXED in Sy.
      assert (Bpb7' : forall i, 0 <= i < ds_lit_bufsize s1 * 4 -> 0 <= arr_get (ds_pending_buf s7) i < 256) by (rewrite <- Elbs2, <- Elbs3; exact Bpb7).
      constructor; rewrite ?Estrm, ?Elv, ?Esy, ?Ews, ?Ebs, ?Elbs, ?Eol, ?Esl, ?Epd, ?Epo, ?Ebv, ?Ebb, ?Ewin, ?Ese, ?Estr7, ?Elook7, ?N71, ?Lpb7, ?Epb3, ?Epb2, ?(df_bl _ D).
      all: try assumption.
      - lia.
      - clear - Hext Hadv Hadv2 Hn Sl. lia.
      - pose proof (df_strstart _ D). clear - Hext H Hn Sl. lia.
      - clear - Hstr Hadv Hsl Hlook. lia.
      - clear - Hadv Hlook Hsl Hstr. lia.
      - clear - Sw. lia.
      - exact (df_wl _ D).
      - exact (df_wb _ D).
      - unfold dmode in Hm. destruct (Z.eqb_spec (ds_level s1) 0); [discriminate Hm | clear - Lv n; lia].
      - reflexivity.
      - clear - Bv Bi. lia.
      - clear - Bi. lia.
      - rewrite To. apply wrap64_range'.
      - clear - Ao Ou A0 Zl. lia.
      - rewrite Q1, N71. reflexivity.
      - clear - Hn. lia.
      - rewrite <- N71. exact Q3.
      - exact (dx_opt _ X).
      - exact (dx_stat _ X).
      - exact (df_tl _ D7).
      - rewrite Edep. exact Xdepth.
      - intros i Hi. rewrite Eblc. apply Xblc. exact Hi.
      - eexists; first [exact (df_lbs _ D7) | exact (df_lbs _ D)]. }
    split; [exact D7|]. split; [exact V7|]. split; [rewrite EKV; exact HK|]. split; [rewrite Epd; exact Hp|]. split; [exact Em7|].
    split; [rewrite Est; exact Hst|]. split; [apply (OUTLE_trans _ s1); [exact Ho | apply OUTLE_strm; exact Estrm]|].
    split; [exact Estrm|]. split; [unfold lz_meas; rewrite Estrm, Elook7; clear - Hadv; lia|]. split; [rewrite Elook7; clear - Hadv Hlook Hsl Hstr; lia|].
    split; [exact N71|]. split; [exact Esn71|]. split; [exact Ese|]. split; [exact Elbs|]. split; [exact X7|]. split; [exact FE7|].
    split.
    { pose proof X as X'. destruct X'; constructor; rewrite ?Em7, ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Esy, ?Eins, ?Ews, ?Epl, ?Ema, ?Epm, ?Emt, ?Ehw, ?Ewsz, ?Ebs, ?Ewr, ?Est,
        ?Elbs, ?Eol, ?Esl, ?Epd, ?Epo, ?Ebv, ?Estr7, ?Elook7, ?N71; try assumption.
      - clear - Hml7. unfold MIN_MATCH, MAX_MATCH in *. lia.
      - intros _. split; [exact Hpl | exact (proj2 Hml7)].
      - intros _. exact Hma.
      - intros HH. discriminate HH.
      - intros HH. discriminate HH.
      - intros HH. exfalso. exact (Hst HH).
      - rewrite Edep. exact Xdepth.
      - intros i Hi. rewrite Eblc. apply Xblc. exact Hi.
      - intros _. rewrite <- Estr7. eapply CHAIN_mono; [| | exact HC7]; clear; lia. }
    split; [exact T71|]. split; [exact HC7|]. split; [exact Bih7 | exact (proj2 Hml7)].
  Qed.

  Lemma cfg_ranges : forall s, dwf s -> DX s -> dmode s <> 0 ->
    1 <= ds_level s <= 9
    /\ 4 <= ds_good_match s <= 32 /\ 4 <= ds_max_lazy_match s <= 258 /\ 8 <= ds_nice_match s <= 258 /\ 4 <= ds_max_chain_length s <= 4096.
  Proof.
    intros s D X Hm. pose proof (df_level _ D) as Lv. pose proof (dx_cfg _ X) as C.
    assert (Hl : ds_level s <> 0) by (intros E0; apply Hm; unfold dmode; rewrite E0; reflexivity).
    assert (Hc : ds_level s = 1 \/ ds_level s = 2 \/ ds_level s = 3 \/ ds_level s = 4 \/ ds_level s = 5 \/ ds_level s = 6 \/ ds_level s = 7 \/ ds_level s = 8 \/ ds_level s = 9) by lia.
    destruct Hc as [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]; rewrite E in C |- *; cbn in C; injection C as -> -> -> ->; lia.
  Qed.

  Lemma trip_inv_intro : forall s, dwf s ->
    0 <= ds_ins_h s < 65536 -> 0 <= ds_match_length s <= 258 -> 0 <= ds_max_lazy_match s < 2 ^ 31 ->
    0 <= ds_sym_next s -> ds_sym_next s + 3 <= 3 * ds_lit_bufsize s ->
    (forall i, 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) -> (forall i, 0 <= arr_get (ds_dyn_dtree_fc s) i < 65536) ->
    trip_inv s.
  Proof.
    intros s D Hih Hml Hlz Hsn1 Hsn2 Hl Hd. pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
    pose proof (df_hbits _ D) as Hb. pose proof (df_hshift _ D) as Hsh.
    constructor.
    - exact (proj1 (df_strstart _ D)).
    - exact (df_sl _ D).
    - exact (df_look _ D).
    - clear - Hih. lia.
    - exact (df_hmask _ D).
    - exact (df_wmask _ D).
    - rewrite Hsh. unfold MIN_MATCH. clear - Hb. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
    - exact Hml.
    - exact (df_ms _ D).
    - exact Hlz.
    - clear - Hsn1 Hsn2. lia.
    - rewrite (df_symend _ D). clear - Sl. lia.
    - exact (df_wb _ D).
    - exact (df_hb _ D).
    - exact (df_pb _ D).
    - intros i _. apply Hl.
    - intros i _. apply Hd.
  Qed.

  Lemma trip_inv_transfer : forall a b, trip_inv a -> TF b = TF a ->
    ds_strstart b = ds_strstart a -> ds_lookahead b = ds_lookahead a -> ds_sym_next b = ds_sym_next a ->
    0 <= ds_ins_h b < 65536 -> 0 <= ds_match_length b <= 258 -> 0 <= ds_match_start b < 2 ^ 32 ->
    (forall i, 0 <= i < ds_hash_size a -> 0 <= arr_get (ds_head b) i < 65536) ->
    (forall i, 0 <= i < ds_w_size a -> 0 <= arr_get (ds_prev b) i < 65536) ->
    ds_dyn_ltree_fc b = ds_dyn_ltree_fc a -> ds_dyn_dtree_fc b = ds_dyn_dtree_fc a ->
    trip_inv b.
  Proof.
    intros a b T E Estr Elook Esn Hih Hml Hms Hh Hp El Ed.
    pose proof (TF_fields _ _ E) as ((_ & Elz & _) & (_ & Ews & _) & (_ & _ & _ & Elbs & _) & (_ & _ & _ & _ & Ehs & Ewm & Ehm & Ehsh) & (_ & _ & _ & _ & _ & _ & Ewin & _ & Ese) & _).
    destruct T; constructor; rewrite ?Estr, ?Elook, ?Esn, ?Elz, ?Ews, ?Elbs, ?Ehs, ?Ewm, ?Ehm, ?Ehsh, ?Ewin, ?Ese, ?El, ?Ed; try assumption.
    clear - Hih. lia.
  Qed.

  Lemma lm_stage_ok : forall s1 s2 hh, FTI s1 -> 1 <= ds_lookahead s1 -> ds_strstart s1 + MIN_LOOKAHEAD <= 2 * ds_w_size s1 ->
    HREL s1 s2 ->
    (lm_cond s2 hh = true ->
       Forall (fun c => 0 <= c < ds_strstart s1) (lm_visited s2 hh)
       /\ 1 <= hh <= ds_strstart s1 - 1 /\ ds_strstart s1 - hh <= ds_w_size s1 - MIN_LOOKAHEAD /\ MIN_MATCH <= ds_lookahead s1) ->
    lm_cond s2 hh = true -> lm_ok s2 hh.
  Proof.
    intros s1 s2 hh HF Hl1 Hss HR Hlm Hc. destruct (Hlm Hc) as (LV & Hh1 & Hhd & Big). clear Hlm.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    pose proof (TF_fields _ _ T2) as ((Egm & _ & Enm & Emc & _) & (_ & Ews & Epl & _) & _ & (_ & _ & _ & _ & _ & Ewm & _) & (_ & _ & _ & _ & _ & _ & Ewin & _) & _).
    pose proof (cfg_ranges s1 D X ltac:(rewrite Hm; lia)) as (_ & Gg & _ & Gn & Gc).
    pose proof (df_strstart _ D) as Rstr.
    destruct (longest_match_facts s2 hh ltac:(rewrite Estr2; lia) ltac:(rewrite Epl, Hpl; unfold MAX_MATCH; lia) ltac:(rewrite Elook2; lia)) as (ms & _ & Rml & _).
    unfold lm_ok. rewrite Ews, Estr2, Ewm, Epl, Hpl, Enm, Elook2, Egm, Emc, Ewin.
    split; [exact (df_wb _ D)|]. split; [exact Bp2|]. split; [lia|].
    split; [unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hss; lia|]. split; [exact (df_wmask _ D)|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [destruct (_ <=? 2); [rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_lower_bound; lia | lia]|].
    split; [lia|]. split; [exact LV|]. unfold MAX_MATCH in Rml. exact Rml.
  Qed.

  Definition RET (s' : deflate_state) (bs : block_state) : Prop :=
    DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ bs = need_more.

  Lemma fast_step : forall s, FTI s ->
    trip_ok (ds_w_size s0) (ds_hash_size s0) s flush
    /\ match snd (st_body s flush) with
       | LCont => FTI (fst (st_body s flush)) /\ lz_meas (fst (st_body s flush)) < lz_meas s
       | LBreak => FTI (fst (st_body s flush)) /\ ds_lookahead (fst (st_body s flush)) = 0
       | LRet bs => RET (fst (st_body s flush)) bs
       end.
  Proof.
    intros s HF. rewrite st_body_eq2.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (KV_fields _ _ HK) as (Ews0 & Ehs0 & Elbs0 & _).
    pose proof (fill_stage s HF) as FS. cbv zeta in FS.
    destruct FS as (HF1 & Emeas & Hl0 & Hfw & Hl1r & Ews1 & Hnone & Hbrk & Hret & Hss1 & Hnc).
    set (s1 := fst (st_fill s flush)) in *.
    pose proof HF1 as (HDC1 & HK1 & Hp1 & Hm1 & Hst1 & Ho1).
    pose proof (FTI_facts s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hpl1 & Hml1 & Hma1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & Hext1).
    rewrite <- Ews0, <- Ehs0.
    destruct (snd (st_fill s flush)) as [o|] eqn:Eo.
    -
      split.
      { split; [exact Hl0|]. split; [exact Hfw|]. split; [exact Hl1r|]. intros HH; rewrite Eo in HH; discriminate HH. }
      cbn [fst snd]. destruct o as [| |bs].
      + exfalso. exact (Hnc eq_refl).
      + split; [exact HF1 | exact (Hbrk eq_refl)].
      + rewrite (Hret bs eq_refl). split; [exact HDC1|]. split; [exact HK1|]. split; [exact Ho1 | reflexivity].
    - destruct (Hnone eq_refl) as [Hl1 Hslack].
      pose proof (hash_stage s1 HF1 Hl1) as HS. cbv zeta in HS. destruct HS as [HR Hlm].
      set (s2 := fst (st_hash s1)) in *. set (hh := snd (st_hash s1)) in *.
      pose proof (match_stage s1 s2 hh HF1 Hl1 HR Hlm) as MR.
      set (s3 := st_match s2 hh) in *.
      pose proof (tally_stage s1 s2 s3 HF1 Hl1 HR MR) as TS. cbv zeta in TS. destruct TS as [(adv & TR & Hadv1 & Hadv2 & Hadv3 & Hadv4) Ebf].
      set (s7 := fst (st_tally s3)) in *. set (bf := snd (st_tally s3)) in *.
      rewrite <- Ews1 in Hslack.
      pose proof (trip_end s1 s2 s3 s7 adv HF1 Hl1 Hslack HR MR TR (conj Hadv1 Hadv2) Hadv3) as TE.
      destruct TE as (D7 & V7 & HK7 & Hp7 & Hm7 & Hst7 & Ho7 & Estrm7 & Hmeas7 & Hl7 & N7 & Esn7 & Ese7 & Elbs7 & X7 & FE7 & XX7 & T71 & HC7 & Hih7 & Hml7).
      pose proof HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
      pose proof MR as (T3 & Estr3 & Elook3 & Esn3 & Epb3 & Elfc3 & Edfc3 & Ehd3 & Epv3 & Eih3 & Hml3 & Hms3 & Hdist3).
      assert (T31 : TF s3 = TF s1) by (rewrite T3; exact T2).
      pose proof (TF_fields _ _ T31) as ((_ & Elz3 & _) & (_ & Ews3 & _) & _).
      pose proof (cfg_ranges s1 D1 X1 ltac:(rewrite Hm1; lia)) as (_ & _ & Glz & _).
      pose proof (dx_tfc _ X1) as Xtfc1.
      assert (TI1 : trip_inv s1).
      { apply (trip_inv_intro s1 D1 (dx_insh _ X1) ltac:(pose proof (dx_ml _ X1) as R; unfold MAX_MATCH in R; exact R) ltac:(clear - Glz; lia)
                 ltac:(clear - Hsn1 Hn1; lia) ltac:(clear - Hsn1 Hn1; lia)); intros i; [apply (Xtfc1 TL i) | apply (Xtfc1 TD i)]. }
      assert (TI3 : trip_inv s3).
      { apply (trip_inv_transfer s1 s3 TI1 T31); rewrite ?Estr3, ?Estr2, ?Elook3, ?Elook2, ?Esn3, ?Esn2, ?Eih3, ?Ehd3, ?Epv3, ?Elfc3, ?Elfc2, ?Edfc3, ?Edfc2; try reflexivity.
        - exact Bih2.
        - unfold MAX_MATCH in Hml3. exact Hml3.
        - exact Hms3.
        - exact Bh2.
        - exact Bp2. }
      assert (FOK : bf = true -> flush_ok s7 0).
      { intros _. exact (proj1 (flush_block_only_facts c0 s7 0 HFB HC0w D7 V7 XX7 FE7 Hst7 ltac:(rewrite Hm7; lia) (conj (fun _ => HC7) (SLOW3_mode s7 ltac:(rewrite Hm7; lia))))). }
      split.
      { split; [exact Hl0|]. split; [exact Hfw|]. split; [exact Hl1r|]. intros _.
        change (trip_inv s1 /\ 1 <= ds_lookahead s1 <= 2 * ds_w_size s /\ (lm_cond s2 hh = true -> lm_ok s2 hh)
                /\ (trip_inv s3 /\ 1 <= ds_lookahead s3 <= 2 * ds_w_size s /\ (MIN_MATCH <= ds_match_length s3 -> dist_ok s3)
                    /\ 0 <= ds_lookahead s7 <= 2 * ds_w_size s /\ (bf = true -> flush_ok s7 0))).
        split; [exact TI1|]. split; [split; [exact Hl1 | exact (proj2 Hl1r)]|].
        split; [exact (lm_stage_ok s1 s2 hh HF1 Hl1 ltac:(rewrite <- Ews1 in Hss1; exact Hss1) HR Hlm)|].
        split; [exact TI3|]. split; [rewrite Elook3, Elook2; split; [exact Hl1 | exact (proj2 Hl1r)]|].
        split.
        { intros H3. destruct (Hdist3 H3) as [Hmll Hd]. unfold dist_ok, RefDeflFast3.tdist_D. rewrite Elook3, Elook2, Estr3, Estr2, Ews3.
          split; [exact Hmll|]. split; [| clear - Hss1 Hml3 Ews1; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia].
          rewrite Z.mod_small; clear - Hd Sw1; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia. }
        split; [rewrite <- Ews1; exact Hl7 | exact FOK]. }
      unfold st_rest. fold s2 hh s3. fold s7 bf.
      unfold st_bflush. destruct bf.
      +
        rewrite flush_block_eq'.
        pose proof (flush_block_only_facts c0 s7 0 HFB HC0w D7 V7 XX7 FE7 Hst7 ltac:(rewrite Hm7; lia) (conj (fun _ => HC7) (SLOW3_mode s7 ltac:(rewrite Hm7; lia)))) as FB. cbv zeta in FB.
        destruct FB as (_ & DC' & HK' & Ho' & EPF & Estr' & Elook' & Ebs' & Eml' & Ewin' & Esn' & Hpa & Eain & Enin).
        set (s' := flush_block_only s7 0) in *. clearbody s'.
        destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [Z.eqb negb fst snd].
        * split; [exact DC'|]. split; [rewrite HK'; exact HK7|]. split; [exact (OUTLE_trans _ _ _ Ho7 Ho')|]. reflexivity.
        * pose proof (PF_fields _ _ EPF) as (_ & _ & (Est' & _) & _).
          split.
          -- split; [exact DC'|]. split; [rewrite HK'; exact HK7|]. split; [destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)]|].
             split; [rewrite (dmode_PF _ _ EPF); exact Hm7|]. split; [rewrite Est'; exact Hst7|]. exact (OUTLE_trans _ _ _ Ho7 Ho').
          -- unfold lz_meas. rewrite Elook', Eain. unfold lz_meas in Hmeas7, Emeas. rewrite <- Emeas. exact Hmeas7.
      +
        cbn [fst snd].
        assert (Hn7 : nsym s7 <= ds_lit_bufsize s7 - 2).
        { symmetry in Ebf. apply Z.eqb_neq in Ebf. rewrite Esn3, Esn2 in Ebf.
          pose proof (TF_fields _ _ T31) as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & Ese3) & _). rewrite Ese3, (df_symend _ D1) in Ebf.
          rewrite Elbs7, N7. clear - Ebf Hsn1 Hn1. lia. }
        split.
        -- split; [split; [split; [exact D7 | exact (X7 Hn7)] | exact V7]|]. split; [exact HK7|]. split; [exact Hp7|].
           split; [exact Hm7|]. split; [exact Hst7|]. exact Ho7.
        -- rewrite <- Emeas. exact Hmeas7.
  Qed.

  Lemma fast_loop : forall fuel s, FTI s -> lz_meas s < Z.of_nat fuel ->
    loop_ok (ds_w_size s0) (ds_hash_size s0) fuel s flush
    /\ match snd (deflate_fast_loop fuel s flush) with
       | None => FTI (fst (deflate_fast_loop fuel s flush)) /\ ds_lookahead (fst (deflate_fast_loop fuel s flush)) = 0
       | Some bs => RET (fst (deflate_fast_loop fuel s flush)) bs
       end.
  Proof.
    induction fuel as [|f IH]; intros s HI Hmz.
    { exfalso. pose proof (FTI_facts s HI) as (D & _ & V & _). pose proof (sv_ain _ _ V). pose proof (df_look _ D). unfold lz_meas in Hmz. cbn [Z.of_nat] in Hmz. lia. }
    rewrite loop_ok_S, loop_step. destruct (fast_step s HI) as [HT HC].
    destruct (snd (st_body s flush)) eqn:E.
    - destruct HC as [HI' Hm'].
      destruct (IH (fst (st_body s flush)) HI' ltac:(lia)) as [HL HF].
      split; [exact (conj HT HL) | exact HF].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
  Qed.

  Lemma DD_set_insert : forall s v, dwf s -> DX s -> 0 <= v <= ds_strstart s -> v <= ds_w_size s ->
    dwf (set_insert s v) /\ DX (set_insert s v).
  Proof.
    intros s v D X Hv1 Hv2. split.
    - destruct D; constructor; try (dsred; assumption).
    - pose proof (dx_syms _ X) as Xsyms. pose proof (dx_hist _ X) as Xhist. pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl.
      pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc. pose proof (dx_chain _ X) as Xchain.
      assert (En : nsym (set_insert s v) = nsym s) by reflexivity.
      assert (Em : dmode (set_insert s v) = dmode s) by reflexivity.
      destruct X; constructor; rewrite ?En, ?Em; try (dsred; assumption).
  Qed.

  Lemma fast_tail : forall s, FTI s -> ds_lookahead s = 0 ->
    tail_ok (ds_w_size s0) s flush
    /\ BFPOST c0 s0 flush (deflate_tail (tail_st s) flush).
  Proof.
    intros s HF Hl0.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (FTI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof (KV_fields _ _ HK) as (Ews0 & _).
    set (st := tail_st s).
    assert (Efs : forall A (g : deflate_state -> A), (forall x v, g (set_insert x v) = g x) -> g st = g s) by (intros A g Hg; subst st; unfold tail_st; apply Hg).
    assert (Eins : 0 <= ds_insert st <= ds_strstart s /\ ds_insert st <= MIN_MATCH - 1).
    { subst st. unfold tail_st. dsred. destruct (Z.ltb_spec (ds_strstart s) (MIN_MATCH - 1)); unfold MIN_MATCH in *; lia. }
    destruct (DD_set_insert s (ds_insert st) D X ltac:(clear - Eins; lia) ltac:(clear - Eins Sw; unfold MIN_MATCH in Eins; lia)) as [Dst Xst].
    assert (Est : set_insert s (ds_insert st) = st) by (subst st; unfold tail_st; destruct s; reflexivity).
    rewrite Est in Dst, Xst.
    assert (Estrm : ds_strm st = ds_strm s) by (apply Efs; reflexivity).
    assert (Vst : SV c0 st) by (apply (SV_strm c0 s st Estrm V)).
    assert (DCst : DC c0 st) by (exact (conj (conj Dst Xst) Vst)).
    assert (Hpst : ds_pending st = 0) by (rewrite (Efs _ ds_pending) by reflexivity; exact Hp).
    assert (Hmst : dmode st = 3) by (rewrite (Efs _ dmode) by reflexivity; exact Hm).
    assert (Hstst : ds_status st <> FINISH_STATE) by (rewrite (Efs _ ds_status) by reflexivity; exact Hst).
    assert (HKst : KV st = KV s0) by (rewrite (Efs _ KV) by reflexivity; exact HK).
    assert (Hlst : ds_lookahead st = 0) by (rewrite (Efs _ ds_lookahead) by reflexivity; exact Hl0).
    assert (Esn : ds_sym_next st = ds_sym_next s) by (apply Efs; reflexivity).
    assert (Host : OUTLE s0 st) by (apply (OUTLE_trans _ s); [exact Ho | apply OUTLE_strm; exact Estrm]).
    assert (Hmast : ds_match_available st = 0) by (rewrite (Efs _ ds_match_available) by reflexivity; exact Hma).
    assert (FB : forall last, 0 <= last <= 1 ->
      let s' := flush_block_only st last in
      flush_ok st last /\ DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ ds_lookahead s' = 0 /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
      /\ ds_match_available s' = 0).
    { intros last Hlast.
      pose proof (flush_block_only_facts c0 st last HFB HC0w Dst Vst (DX_DXX _ Xst) (DC_fb_entry c0 st last HC0w DCst Hpst ltac:(rewrite Hmst; lia) Hlast)
                    Hstst ltac:(rewrite Hmst; lia) (DX_BND st Xst)) as FB. cbv zeta in FB.
      destruct FB as (FO & DC' & HK' & Ho' & EPF & _ & Elook' & _ & _ & _ & _ & Hpa & _).
      pose proof (PF_fields _ _ EPF) as (_ & (_ & _ & _ & Ema' & _) & _).
      cbv zeta. split; [exact FO|]. split; [exact DC'|]. split; [rewrite HK'; exact HKst|]. split; [exact (OUTLE_trans _ _ _ Host Ho')|].
      split; [rewrite Elook'; exact Hlst|]. split; [exact Hpa | rewrite Ema'; exact Hmast]. }
    split.
    -
      split; [clear - Hstr Hlook Hsl Ews0; lia|]. split; [clear - Hsn Hn Sl; lia|].
      split; [intros _; exact (proj1 (FB 1 ltac:(lia))) | intros _ _; exact (proj1 (FB 0 ltac:(lia)))].
    -
      unfold deflate_tail. destruct (Z.eqb_spec flush Z_FINISH) as [F4|F4].
      + rewrite flush_block_eq'. destruct (FB 1 ltac:(lia)) as (_ & DC' & HK' & Ho' & Hl' & Hpa & Hma').
        set (s' := flush_block_only st 1) in *. clearbody s'.
        destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [negb Z.eqb]; unfold BFPOST; cbn [fst snd].
        * split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
          split; [intros _; exact Hl'|]. intros HH; discriminate HH.
        * split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
          split; [intros _; exact Hl'|]. intros _. destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)].
      + destruct (Z.eqb_spec (ds_sym_next st) 0) as [N0|N0]; cbn [negb].
        * unfold BFPOST; cbn [fst snd].
          split; [exact DCst|]. split; [exact HKst|]. split; [exact Host|]. split; [intros _; split; [exact Hpst | split; [exact F4 | exact Hmast]]|].
          split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
        * rewrite flush_block_eq'. destruct (FB 0 ltac:(lia)) as (_ & DC' & HK' & Ho' & Hl' & Hpa & Hma').
          set (s' := flush_block_only st 0) in *. clearbody s'.
          destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [negb Z.eqb]; unfold BFPOST; cbn [fst snd].
          -- split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
             split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
          -- split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|].
             split; [intros _; split; [destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)] | split; [exact F4 | exact Hma']]|].
             split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
  Qed.

End Fast.

Theorem fast_bf_spec : FB_CALL -> BF_SPEC 3 fast_safe deflate_fast.
Proof.
  intros HFB c0 s flush (HC0 & HDC & Hp & Hst & Hfl) Hm.
  assert (HF : FTI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact Hm|]. split; [exact Hst | apply OUTLE_refl]. }
  pose proof HDC as [[D X] V].
  assert (Hmz : 0 <= lz_meas s) by (unfold lz_meas; pose proof (df_look _ D); pose proof (sv_ain _ _ V); lia).
  destruct (fast_loop c0 s flush HC0 HFB (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as [HL HR].
  assert (Hao : 0 <= cs_avail_out (ds_strm s) < 2 ^ 32).
  { pose proof (sv_out _ _ V) as Ou. pose proof (sv_aout _ _ V) as Ao. pose proof (c0_out _ (c0'_ok _ HC0)) as O0. pose proof (c0_aout _ (c0'_ok _ HC0)) as A0.
    rewrite O0 in Ou. unfold zlen in Ou. cbn [length Z.of_nat] in Ou. pose proof (zlen_nonneg (cs_out_rev (ds_strm s))) as Zl. unfold zlen in Zl. lia. }
  split.
  - unfold fast_safe. split; [exact (dwf_DWF s D Hao)|]. split; [exact HL|].
    destruct (snd (deflate_fast_loop (lz_fuel s) s flush)); [exact I|].
    destruct HR as [HF' Hl']. exact (proj1 (fast_tail c0 s flush HC0 HFB _ HF' Hl')).
  - unfold deflate_fast.
    destruct (deflate_fast_loop (lz_fuel s) s flush) as [s' r] eqn:E. cbn [fst snd] in HR.
    destruct r as [bs|].
    + destruct HR as (DC' & HK' & Ho' & ->). unfold BFPOST; cbn [fst snd].
      split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
      split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
    + destruct HR as [HF' Hl']. exact (proj2 (fast_tail c0 s flush HC0 HFB _ HF' Hl')).
Qed.
