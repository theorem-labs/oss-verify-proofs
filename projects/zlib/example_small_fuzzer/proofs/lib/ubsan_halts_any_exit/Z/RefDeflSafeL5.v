(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflFastM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM.RefDeflSafeW.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeL2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeL2.RefDeflSafeLM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeLW.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeL2.

Module RefDeflSafeL3.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflFastM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM.RefDeflSafeW.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeL2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeL2.RefDeflSafeLM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeLW.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeL2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Lemma fblk_ok_intro : forall s last,
  flush_ok s last -> 0 <= cs_avail_out (ds_strm (flush_block_only s last)) < 2 ^ 32 -> lz_keeps s (flush_block_only s last) ->
  fblk_ok fb_safe s last.
Proof.
  intros s last FO Hao HK. unfold flush_ok in FO. unfold fblk_ok. cbv zeta in FO |- *.
  destruct FO as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & H1 & H2 & H3 & H4).
  repeat (split; [assumption|]). exact HK.
Qed.

Lemma SV_aout : forall c0 s, C0OK c0 -> SV c0 s -> 0 <= cs_avail_out (ds_strm s) < 2 ^ 32.
Proof.
  intros c0 s HC0 V.
  pose proof (sv_out _ _ V) as Ou. pose proof (sv_aout _ _ V) as Ao. pose proof (c0_out _ HC0) as O0. pose proof (c0_aout _ HC0) as A0.
  rewrite O0 in Ou. unfold zlen in Ou. cbn [length Z.of_nat] in Ou. pose proof (zlen_nonneg (cs_out_rev (ds_strm s))) as Zl. unfold zlen in Zl. lia.
Qed.


Lemma dwf_TF_transfer : forall a b, dwf a -> TF b = TF a ->
  0 <= ds_strstart b -> 0 <= ds_lookahead b -> ds_strstart b + ds_lookahead b <= 2 * ds_w_size a -> ds_insert a <= ds_strstart b ->
  0 <= ds_match_start b < 2 ^ 32 -> 0 <= ds_ins_h b < 2 ^ 32 ->
  arr_len (ds_head b) = arr_len (ds_head a) -> arr_len (ds_prev b) = arr_len (ds_prev a) ->
  (forall i, 0 <= i < ds_hash_size a -> 0 <= arr_get (ds_head b) i < 65536) ->
  (forall i, 0 <= i < ds_w_size a -> 0 <= arr_get (ds_prev b) i < 65536) ->
  arr_len (ds_pending_buf b) = arr_len (ds_pending_buf a) ->
  (forall i, 0 <= i < ds_lit_bufsize a * 4 -> 0 <= arr_get (ds_pending_buf b) i < 256) ->
  arr_len (ds_dyn_ltree_fc b) = arr_len (ds_dyn_ltree_fc a) -> arr_len (ds_dyn_dtree_fc b) = arr_len (ds_dyn_dtree_fc a) ->
  dwf b.
Proof.
  intros a b D E Hstr Hlook Hsl Hins Hms Hih Lh Lp Bh Bp Lpb Bpb Llt Ldt.
  pose proof (dwf_sizes a D) as (Sw & _).
  pose proof (TF_fields _ _ E) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Epl & Ema & Epm & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                    & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
  pose proof (KV_fields _ _ EKV) as (_ & _ & _ & KB).
  pose proof (df_tl _ D) as TL.
  destruct D; constructor; rewrite ?Est, ?Ewr, ?Elbs, ?Ebl, ?Eldl, ?Eddl, ?Ebdl, ?Edep, ?Eblc, ?Ehs, ?Ewm, ?Ehm, ?Ehsh, ?Epd, ?Epo, ?Ebv, ?Ebb, ?Elf, ?Ewin,
      ?Ese, ?Ewb, ?Ehb, ?Epbs, ?Egz, ?Eme, ?Elv, ?Esy, ?Ews, ?Eins, ?Ewsz, ?Ehw, ?Lh, ?Lp, ?Lpb; try assumption.
  - unfold deflateStateCheck in *. rewrite Est. assumption.
  - congruence.
  - congruence.
  - congruence.
  - congruence.
  - unfold tree_lens in *. rewrite Llt, Ldt, Ebl, Eldl, Eddl, Ebdl, Eblc, Ehp, Edep. assumption.
  - clear - Hstr Hlook Hsl Sw. lia.
  - clear - Hins df_ins. lia.
Qed.

Lemma DXX_TF_transfer : forall a b, DX a -> TF b = TF a ->
  0 <= ds_ins_h b < 65536 -> 0 <= ds_match_length b <= MAX_MATCH ->
  (dmode a = 3 -> ds_match_length b < MIN_MATCH) ->
  (dmode a = 4 -> 2 <= ds_match_length b /\ (ds_match_available b = 1 -> 1 <= ds_strstart b)) ->
  dmode a <> 0 -> ds_status a <> FINISH_STATE ->
  (forall t i, 0 <= arr_get (tree_dl b t) i < 65536) ->
  CHAIN b (ds_strstart b - 1) (ds_strstart b - 1) ->
  DXX b.
Proof.
  intros a b X E Hih Hml H3 H4 Hm Hst Htdl HC.
  pose proof (TF_fields _ _ E) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Epl & Ema & Epm & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                    & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
  assert (Em : dmode b = dmode a) by (unfold dmode; rewrite Elv, Esy; reflexivity).
  pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc. pose proof (dx_fast _ X) as Xf.
  destruct X; constructor; rewrite ?Em, ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Esy, ?Eins, ?Ews, ?Epl, ?Ema, ?Epm, ?Emt, ?Ehw, ?Ewsz, ?Ebs, ?Ewr, ?Est, ?Edep, ?Eblc; try assumption.
  - intros Hm3. split; [exact (proj1 (Xf Hm3)) | exact (H3 Hm3)].
  - rewrite <- Ema. exact H4.
  - intros Hm0. exfalso. exact (Hm Hm0).
  - intros Hf. exfalso. exact (Hst Hf).
  - intros _. eapply CHAIN_mono; [| | exact HC]; clear; lia.
Qed.


Section Huff.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis HFB : FB_CALL.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Definition HTI (s : deflate_state) : Prop :=
    DC c0 s /\ KV s = KV s0 /\ ds_pending s = 0 /\ dmode s = 1 /\ ds_status s <> FINISH_STATE /\ OUTLE s0 s.

  Lemma HTI_facts : forall s, HTI s ->
    dwf s /\ DX s /\ SV c0 s
    /\ 512 <= ds_w_size s <= 32768 /\ 256 <= ds_hash_size s <= 65536 /\ 2048 <= ds_lit_bufsize s <= 32768
    /\ ds_match_available s = 0
    /\ 0 <= nsym s <= ds_lit_bufsize s - 2 /\ ds_sym_next s = 3 * nsym s /\ ds_sym_end s = (ds_lit_bufsize s - 1) * 3
    /\ 0 <= ds_strstart s /\ 0 <= ds_lookahead s /\ ds_strstart s + ds_lookahead s <= 2 * ds_w_size s
    /\ 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s.
  Proof.
    intros s (HDC & HK & Hp & Hm & Hst & Ho). pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
    pose proof (dx_notslow _ X ltac:(rewrite Hm; lia)) as Hma.
    pose proof (dx_nsym _ X). pose proof (dx_sn _ X). pose proof (df_symend _ D). pose proof (df_strstart _ D). pose proof (df_look _ D). pose proof (df_sl _ D).
    pose proof (dx_ext _ X ltac:(rewrite Hm; lia)) as He. rewrite Hma in He.
    repeat (split; [assumption|]). lia.
  Qed.

  Lemma hfill_stage : forall s, HTI s ->
    let r := hf_fill s flush in
    HTI (fst r) /\ lz_meas (fst r) = lz_meas s
    /\ (ds_lookahead s = 0 -> fw_wf (ds_w_size s) (ds_hash_size s) s /\ DOK (fill_window s) /\ lz_keeps s (fill_window s))
    /\ ds_w_size (fst r) = ds_w_size s
    /\ (snd r = None -> 1 <= ds_lookahead (fst r))
    /\ (snd r = Some LBreak -> ds_lookahead (fst r) = 0)
    /\ (forall bs, snd r = Some (LRet bs) -> bs = need_more)
    /\ snd r <> Some LCont.
  Proof.
    intros s HF r. subst r. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (HTI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    assert (Hwr : 0 <= ds_wrap s) by (pose proof (dx_wrapneg _ X); pose proof (df_wrap _ D); destruct (Z_lt_le_dec (ds_wrap s) 0); [exfalso; apply Hst; auto | lia]).
    assert (HW : fw_wf (ds_w_size s) (ds_hash_size s) s).
    { apply (dwf_fw_wf s D Hwr (sv_nin _ _ V) (sv_ain _ _ V) ltac:(rewrite (sv_input _ _ V); pose proof (sv_inlen _ _ V); lia)
             (sv_tin _ _ V) (sv_adler _ _ V) (sv_ib _ _ V)). }
    unfold hf_fill.
    destruct (Z.eqb_spec (ds_lookahead s) 0) as [Hl0|Hl0].
    - destruct (DC_fill_window c0 s HC0w HDC ltac:(rewrite Hm; lia) Hst ltac:(rewrite Hl0; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; lia))
        as (HDC' & HK' & Ho' & R' & Eext & HL' & HX' & HW' & SS').
      pose proof (fw_rest_fields _ _ R') as ((Est & _ & _ & _ & Epd & _) & (_ & _ & Elv & Esy & _) & _).
      pose proof (fill_window_keep s) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ksum).
      assert (HF' : HTI (fill_window s)).
      { split; [exact HDC'|]. split; [rewrite HK'; exact HK|]. split; [rewrite Epd; exact Hp|].
        split; [unfold dmode; rewrite Elv, Esy; exact Hm|]. split; [rewrite Est; exact Hst | exact (OUTLE_trans _ _ _ Ho Ho')]. }
      pose proof (wf_ws _ _ _ HW') as Ews'.
      assert (HFW : ds_lookahead s = 0 -> fw_wf (ds_w_size s) (ds_hash_size s) s /\ DOK (fill_window s) /\ lz_keeps s (fill_window s)).
      { intros _. split; [exact HW|]. split; [exact (DC_DOK c0 _ HC0w HDC')|].
        pose proof HDC as [[_ _] V0]. pose proof HDC' as [[D' _] V'].
        exact (lz_keeps_intro c0 s (fill_window s) D D' V0 V' HK' Ho'). }
      destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [E0|E0].
      + destruct (Z.eqb_spec flush Z_NO_FLUSH) as [F0|F0]; cbn [fst snd].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [exact HFW|]. split; [exact Ews'|].
          split; [intros HH; discriminate HH|]. split; [intros HH; discriminate HH|].
          split; [intros bs Hbs; injection Hbs as <-; reflexivity | intros HH; discriminate HH].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [exact HFW|]. split; [exact Ews'|].
          split; [intros HH; discriminate HH|]. split; [intros _; exact E0|].
          split; [intros bs Hbs; discriminate Hbs | intros HH; discriminate HH].
      + cbn [fst snd]. split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [exact HFW|]. split; [exact Ews'|].
        split; [intros _; lia|]. split; [intros HH; discriminate HH|].
        split; [intros bs Hbs; discriminate Hbs | intros HH; discriminate HH].
    - cbn [fst snd]. split; [exact HF|]. split; [reflexivity|]. split; [intros HH; exfalso; exact (Hl0 HH)|]. split; [reflexivity|].
      split; [intros _; lia|]. split; [intros HH; discriminate HH|].
      split; [intros bs Hbs; discriminate Hbs | intros HH; discriminate HH].
  Qed.

  Definition HTREL (s1 s7 : deflate_state) : Prop :=
    TF s7 = TF s1 /\ ds_strstart s7 = ds_strstart s1 + 1 /\ ds_lookahead s7 = ds_lookahead s1 - 1
    /\ ds_match_length s7 = 0 /\ ds_match_start s7 = ds_match_start s1
    /\ ds_head s7 = ds_head s1 /\ ds_prev s7 = ds_prev s1 /\ ds_ins_h s7 = ds_ins_h s1
    /\ arr_len (ds_pending_buf s7) = arr_len (ds_pending_buf s1)
    /\ (forall i, 0 <= i < ds_lit_bufsize s1 * 4 -> 0 <= arr_get (ds_pending_buf s7) i < 256)
    /\ arr_len (ds_dyn_ltree_fc s7) = arr_len (ds_dyn_ltree_fc s1) /\ arr_len (ds_dyn_dtree_fc s7) = arr_len (ds_dyn_dtree_fc s1)
    /\ (forall i, 0 <= arr_get (ds_dyn_ltree_fc s7) i < 65536) /\ (forall i, 0 <= arr_get (ds_dyn_dtree_fc s7) i < 65536)
    /\ BQ s7 /\ nsym s7 = nsym s1 + 1 /\ ds_sym_next s7 = ds_sym_next s1 + 3.

  Lemma htally_lit : forall s1, HTI s1 ->
    let s3 := set_match_length s1 0 in
    let r := tr_tally_lit s3 (arr_get (ds_window s3) (ds_strstart s3)) in
    TALLYF s3 (fst r) /\ snd r = (ds_sym_next s1 + 3 =? ds_sym_end s1).
  Proof.
    intros s1 HF s3 r. subst r.
    pose proof (HTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof (tally_lit_facts s3 (arr_get (ds_window s3) (ds_strstart s3))) as (TK & Esn & Ebf & Edt & Ebt & Elt & Rl & Rp). cbv zeta in *.
    assert (BQ3 : BQ s3) by (apply (BQ_same s1); try reflexivity; exact (DX_BQ s1 X)).
    assert (N3 : nsym s3 = nsym s1) by reflexivity.
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL. destruct TL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    destruct (BQ_tally_lit s3 BQ3 ltac:(change (ds_lit_bufsize s1 + ds_sym_next s1 + 3 <= arr_len (ds_pending_buf s1)); rewrite (df_bl _ D); lia)
                ltac:(change (0 <= ds_lit_bufsize s1); lia) ltac:(rewrite N3; lia) ltac:(change (L_CODES <= arr_len (ds_dyn_ltree_fc s1)); rewrite L1; unfold L_CODES; lia)
                (arr_get (ds_window s3) (ds_strstart s3))) as (BQ4 & N4 & _).
    cbv zeta in BQ4, N4.
    split; [| rewrite Ebf; reflexivity].
    eapply tally_common.
    - change (forall j, 0 <= j < ds_lit_bufsize s1 * 4 -> 0 <= arr_get (ds_pending_buf s1) j < 256). exact (df_bb _ D).
    - change (forall i, 0 <= arr_get (ds_dyn_ltree_fc s1) i < 65536). exact (dx_tfc _ X DeflateState.TL).
    - change (forall i, 0 <= arr_get (ds_dyn_dtree_fc s1) i < 65536). exact (dx_tfc _ X DeflateState.TD).
    - exact TK.
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
    - destruct TK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehmk & _). exact Ehmk.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact BQ4.
    - exact N4.
  Qed.

  Lemma htally_stage : forall s1, HTI s1 -> 1 <= ds_lookahead s1 ->
    let r := hf_tally s1 in
    HTREL s1 (fst r) /\ snd r = (ds_sym_next s1 + 3 =? ds_sym_end s1).
  Proof.
    intros s1 HF Hl1 r. subst r.
    pose proof (HTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof (htally_lit s1 HF) as [TY Ebf]. cbv zeta in TY, Ebf.
    unfold hf_tally. cbv zeta. destruct (tr_tally_lit (set_match_length s1 0) _) as [s4 bf]. cbn [fst snd] in TY, Ebf |- *.
    split; [| exact Ebf].
    destruct TY as (T4 & Estr4 & Elook4 & Eml4 & Ems4 & Ehd4 & Epv4 & Eih4 & Lpb4 & Bpb4 & Llt4 & Ldt4 & Blt4 & Bdt4 & BQ4 & N4 & Esn4).
    unfold HTREL. dsred. rewrite Estr4, Elook4, Eml4, Ems4, Ehd4, Epv4, Eih4. dsred.
    split; [etransitivity; [| exact T4]; reflexivity|].
    repeat (split; [reflexivity|]).
    split; [exact Lpb4|]. split; [exact Bpb4|]. split; [exact Llt4|]. split; [exact Ldt4|]. split; [exact Blt4|]. split; [exact Bdt4|].
    split; [apply (BQ_same s4); dsred; try reflexivity; exact BQ4|].
    split; [unfold nsym in *; dsred; exact N4 | exact Esn4].
  Qed.

  Lemma htrip_end : forall s1 s7, HTI s1 -> 1 <= ds_lookahead s1 -> HTREL s1 s7 ->
    dwf s7 /\ SV c0 s7 /\ KV s7 = KV s0 /\ ds_pending s7 = 0 /\ dmode s7 = 1 /\ ds_status s7 <> FINISH_STATE /\ OUTLE s0 s7
    /\ ds_strm s7 = ds_strm s1 /\ lz_meas s7 < lz_meas s1 /\ 0 <= ds_lookahead s7 <= 2 * ds_w_size s1
    /\ nsym s7 = nsym s1 + 1 /\ ds_sym_next s7 = ds_sym_next s1 + 3 /\ ds_sym_end s7 = ds_sym_end s1 /\ ds_lit_bufsize s7 = ds_lit_bufsize s1
    /\ (nsym s7 <= ds_lit_bufsize s7 - 2 -> DX s7)
    /\ fb_entry s7 0
    /\ DXX s7 /\ BND s7.
  Proof.
    intros s1 s7 HF Hl1 TR.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (HTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    destruct TR as (T7 & Estr7 & Elook7 & Hml7 & Ems7 & Ehd7 & Epv7 & Eih7 & Lpb7 & Bpb7 & Llt7 & Ldt7 & Blt7 & Bdt7 & BQ7 & N7 & Esn7).
    pose proof (TF_fields _ _ T7) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Epl & Ema & Epm & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                        & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
    assert (Em7 : dmode s7 = 1) by (unfold dmode; rewrite Elv, Esy; exact Hm).
    pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl. pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc.
    assert (Htfc7 : forall t i, 0 <= arr_get (tree_fc s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_fc]; [apply Blt7 | apply Bdt7 | rewrite Ebl; apply (Xtfc DeflateState.TB i)]. }
    assert (Htdl7 : forall t i, 0 <= arr_get (tree_dl s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_dl]; rewrite ?Eldl, ?Eddl, ?Ebdl; [apply (Xtdl DeflateState.TL i) | apply (Xtdl DeflateState.TD i) | apply (Xtdl DeflateState.TB i)]. }
    assert (HC7 : CHAIN s7 (ds_strstart s7 - 1) (ds_strstart s7 - 1)).
    { apply (CHAIN_same s1); [exact Ehd7 | exact Epv7 | exact Ehs | exact Ews | exact Ewm |].
      rewrite Estr7. replace (ds_strstart s1 + 1 - 1) with (ds_strstart s1) by lia.
      eapply CHAIN_mono; [| | exact (dx_chain _ X ltac:(rewrite Hm; lia))]; lia. }
    assert (D7 : dwf s7).
    { apply (dwf_TF_transfer s1 s7 D T7); rewrite ?Estr7, ?Elook7, ?Ems7, ?Eih7, ?Ehd7, ?Epv7; try reflexivity; try assumption.
      - clear - Hstr. lia.
      - clear - Hl1. lia.
      - clear - Hsl. lia.
      - pose proof (df_ins _ D). clear - H. lia.
      - exact (df_ms _ D).
      - pose proof (dx_insh _ X). clear - H. lia.
      - exact (df_hb _ D).
      - exact (df_pb _ D). }
    assert (XX7 : DXX s7).
    { apply (DXX_TF_transfer s1 s7 X T7); rewrite ?Eih7, ?Hml7, ?Hm; try assumption.
      - exact (dx_insh _ X).
      - unfold MAX_MATCH. clear. lia.
      - intros HH. discriminate HH.
      - intros HH. discriminate HH.
      - clear. lia. }
    assert (V7 : SV c0 s7) by (apply (SV_strm c0 s1); [exact Estrm | exact V]).
    assert (Hl7 : ds_level s7 <> 0) by (intros E0; unfold dmode in Em7; rewrite E0 in Em7; discriminate Em7).
    assert (X7 : nsym s7 <= ds_lit_bufsize s7 - 2 -> DX s7).
    { intros Hn7. destruct BQ7 as (Q1 & Q2 & Q3 & Q4).
      apply (DXX_DX s7 XX7 (SLOW3_mode s7 ltac:(rewrite Em7; lia))); rewrite ?Em7, ?Emt, ?N7, ?Eol, ?Esl, ?Epd, ?Epo, ?Ebv, ?Ebs, ?Ema; try assumption.
      - pose proof (RefDeflSafeI1.dx_matches _ X) as HM. clear - HM. lia.
      - rewrite <- N7. exact Q1.
      - revert Hn7. rewrite N7, Elbs. clear - Hn. intros Hn7. lia.
      - rewrite <- N7. exact Q3.
      - exact (dx_opt _ X).
      - exact (dx_stat _ X).
      - intros _. rewrite Estr7, Hma. clear - Hext Hn. lia.
      - intros _. exact (dx_pout0 _ X Hp).
      - exact (dx_biv _ X).
      - intros _. exact HC7. }
    assert (FE7 : fb_entry s7 0).
    { apply (fb_entry_intro c0 s7 0 HC0w D7 V7); rewrite ?Epd, ?Epo, ?Ebv, ?Eol, ?Esl, ?Edep, ?Eblc, ?Elv, ?Estr7, ?Ebs, ?N7, ?Elbs; try assumption.
      - exact (dx_pout0 _ X Hp).
      - exact (dx_biv _ X).
      - clear - Hn. lia.
      - exact (dx_opt _ X).
      - exact (dx_stat _ X).
      - intros E0. apply Hl7. rewrite Elv. exact E0.
      - clear - Hext Hn. lia.
      - clear. lia. }
    split; [exact D7|]. split; [exact V7|]. split; [rewrite EKV; exact HK|]. split; [rewrite Epd; exact Hp|]. split; [exact Em7|].
    split; [rewrite Est; exact Hst|]. split; [apply (OUTLE_trans _ s1); [exact Ho | apply OUTLE_strm; exact Estrm]|].
    split; [exact Estrm|]. split; [unfold lz_meas; rewrite Estrm, Elook7; clear; lia|]. split; [rewrite Elook7; clear - Hl1 Hlook Hsl Hstr; lia|].
    split; [exact N7|]. split; [exact Esn7|]. split; [exact Ese|]. split; [exact Elbs|]. split; [exact X7|]. split; [exact FE7|].
    split; [exact XX7 | exact (conj (fun _ => HC7) (SLOW3_mode s7 ltac:(rewrite Em7; lia)))].
  Qed.

  Definition HRET (s' : deflate_state) (bs : block_state) : Prop :=
    DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ bs = need_more.

  Lemma hflush : forall s last, dwf s -> SV c0 s -> DXX s -> fb_entry s last -> ds_status s <> FINISH_STATE -> dmode s = 1 -> BND s ->
    KV s = KV s0 -> OUTLE s0 s ->
    let s' := flush_block_only s last in
    fblk_ok fb_safe s last
    /\ DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ dmode s' = 1 /\ ds_status s' <> FINISH_STATE
    /\ ds_lookahead s' = ds_lookahead s /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
    /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s) /\ ds_match_available s' = ds_match_available s.
  Proof.
    intros s last D V XX FE Hst Hm B HK Ho s'.
    pose proof (flush_block_only_facts c0 s last HFB HC0w D V XX FE Hst ltac:(rewrite Hm; lia) B) as FB. cbv zeta in FB.
    destruct FB as (FO & DC' & HK' & Ho' & EPF & Estr' & Elook' & Ebs' & Eml' & Ewin' & Esn' & Hpa & Eain & Enin).
    subst s'. pose proof DC' as [[D' X'] V'].
    pose proof (PF_fields _ _ EPF) as (_ & (_ & _ & _ & Ema' & _) & (Est' & _) & _).
    split; [apply (fblk_ok_intro s last FO (SV_aout c0 _ HC0w V') (lz_keeps_intro c0 _ _ D D' V V' HK' Ho'))|].
    split; [exact DC'|]. split; [rewrite HK'; exact HK|]. split; [exact (OUTLE_trans _ _ _ Ho Ho')|].
    split; [rewrite (dmode_PF _ _ EPF); exact Hm|]. split; [rewrite Est'; exact Hst|].
    split; [exact Elook'|]. split; [exact Hpa|]. split; [exact Eain | exact Ema'].
  Qed.

  Lemma huff_outcome : forall s s1 s7 (bf : bool),
    HTI s1 -> lz_meas s1 = lz_meas s -> 1 <= ds_lookahead s1 -> HTREL s1 s7 -> bf = (ds_sym_next s1 + 3 =? ds_sym_end s1) ->
    (bf = true -> fblk_ok fb_safe s7 0)
    /\ match snd (st_bflush0 s7 bf) with
       | LCont => HTI (fst (st_bflush0 s7 bf)) /\ lz_meas (fst (st_bflush0 s7 bf)) < lz_meas s
       | LBreak => HTI (fst (st_bflush0 s7 bf)) /\ ds_lookahead (fst (st_bflush0 s7 bf)) = 0
       | LRet bs => HRET (fst (st_bflush0 s7 bf)) bs
       end.
  Proof.
    intros s s1 s7 bf HF1 Emeas Hl1 TR Ebf.
    pose proof (HTI_facts s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hma1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & Hext1).
    pose proof (htrip_end s1 s7 HF1 Hl1 TR) as TE.
    destruct TE as (D7 & V7 & HK7 & Hp7 & Hm7 & Hst7 & Ho7 & Estrm7 & Hmeas7 & Hl7 & N7 & Esn7 & Ese7 & Elbs7 & X7 & FE7 & XX7 & B7).
    split; [intros _; exact (proj1 (hflush s7 0 D7 V7 XX7 FE7 Hst7 Hm7 B7 HK7 Ho7))|].
    unfold st_bflush0. destruct bf.
    - rewrite flush_block_eq'.
      pose proof (hflush s7 0 D7 V7 XX7 FE7 Hst7 Hm7 B7 HK7 Ho7) as FB. cbv zeta in FB.
      destruct FB as (_ & DC' & HK' & Ho' & Hm' & Hst' & Elook' & Hpa & Eain & _).
      set (s' := flush_block_only s7 0) in *. clearbody s'.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [Z.eqb negb fst snd].
      + split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. reflexivity.
      + split.
        * split; [exact DC'|]. split; [exact HK'|]. split; [destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)]|].
          split; [exact Hm'|]. split; [exact Hst'|]. exact Ho'.
        * unfold lz_meas. rewrite Elook', Eain. unfold lz_meas in Hmeas7, Emeas. rewrite <- Emeas. exact Hmeas7.
    - cbn [fst snd].
      assert (Hn7 : nsym s7 <= ds_lit_bufsize s7 - 2).
      { symmetry in Ebf. apply Z.eqb_neq in Ebf. rewrite (df_symend _ D1) in Ebf. rewrite Elbs7, N7. clear - Ebf Hsn1 Hn1. lia. }
      split.
      + split; [split; [split; [exact D7 | exact (X7 Hn7)] | exact V7]|]. split; [exact HK7|]. split; [exact Hp7|].
        split; [exact Hm7|]. split; [exact Hst7|]. exact Ho7.
      + rewrite <- Emeas. exact Hmeas7.
  Qed.

  Lemma hf_body_eq2 : forall s,
    hf_body s flush = match snd (hf_fill s flush) with
                      | Some o => (fst (hf_fill s flush), o)
                      | None => st_bflush0 (fst (hf_tally (fst (hf_fill s flush)))) (snd (hf_tally (fst (hf_fill s flush))))
                      end.
  Proof.
    intros s. unfold hf_body. destruct (hf_fill s flush) as [s1 e]. cbn [fst snd]. destruct e; [reflexivity|]. destruct (hf_tally s1); reflexivity.
  Qed.

  Lemma huff_step : forall s, HTI s ->
    hf_trip_ok fb_safe s flush
    /\ match snd (hf_body s flush) with
       | LCont => HTI (fst (hf_body s flush)) /\ lz_meas (fst (hf_body s flush)) < lz_meas s
       | LBreak => HTI (fst (hf_body s flush)) /\ ds_lookahead (fst (hf_body s flush)) = 0
       | LRet bs => HRET (fst (hf_body s flush)) bs
       end.
  Proof.
    intros s HF.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (hfill_stage s HF) as FS. cbv zeta in FS.
    destruct FS as (HF1 & Emeas & Hfw & Ews1 & Hnone & Hbrk & Hret & Hnc).
    rewrite hf_body_eq2.
    set (s1 := fst (hf_fill s flush)) in *.
    pose proof HF1 as (HDC1 & HK1 & Hp1 & Hm1 & Hst1 & Ho1).
    pose proof (HTI_facts s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hma1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & Hext1).
    destruct (snd (hf_fill s flush)) as [o|] eqn:Eo.
    - split.
      { split; [exact (DC_DOK c0 s HC0w HDC)|]. split; [exact Hfw|]. intros HH; rewrite Eo in HH; discriminate HH. }
      cbn [fst snd]. destruct o as [| |bs].
      + exfalso. exact (Hnc eq_refl).
      + split; [exact HF1 | exact (Hbrk eq_refl)].
      + rewrite (Hret bs eq_refl). split; [exact HDC1|]. split; [exact HK1|]. split; [exact Ho1 | reflexivity].
    - pose proof (Hnone eq_refl) as Hl1.
      pose proof (htally_stage s1 HF1 Hl1) as TS. cbv zeta in TS. destruct TS as [TR Ebf].
      pose proof (huff_outcome s s1 (fst (hf_tally s1)) (snd (hf_tally s1)) HF1 Emeas Hl1 TR Ebf) as [FOK OUT].
      split; [| exact OUT].
      split; [exact (DC_DOK c0 s HC0w HDC)|]. split; [exact Hfw|]. intros _.
      change (DOK s1 /\ 1 <= ds_lookahead s1 /\ ds_strstart s1 + ds_lookahead s1 <= 2 * ds_w_size s1
              /\ 0 <= ds_sym_next s1 /\ ds_sym_next s1 + 3 <= 3 * ds_lit_bufsize s1 /\ 0 <= ds_sym_end s1 < 2 ^ 32
              /\ (forall j, 0 <= j < 2 * ds_w_size s1 -> 0 <= arr_get (ds_window s1) j < 256)
              /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s1) i < 65536)
              /\ (snd (hf_tally s1) = true -> fblk_ok fb_safe (fst (hf_tally s1)) 0)).
      split; [exact (DC_DOK c0 s1 HC0w HDC1)|]. split; [exact Hl1|]. split; [exact Hsl1|].
      split; [clear - Hsn1 Hn1; lia|]. split; [clear - Hsn1 Hn1; lia|]. split; [rewrite Hse1; clear - Sl1; lia|].
      split; [exact (df_wb _ D1)|]. split; [intros i _; exact (dx_tfc _ X1 DeflateState.TL i) | exact FOK].
  Qed.

  Lemma huff_loop : forall fuel s, HTI s -> lz_meas s < Z.of_nat fuel ->
    hf_loop_ok fb_safe fuel s flush
    /\ match snd (deflate_huff_loop fuel s flush) with
       | None => HTI (fst (deflate_huff_loop fuel s flush)) /\ ds_lookahead (fst (deflate_huff_loop fuel s flush)) = 0
       | Some bs => HRET (fst (deflate_huff_loop fuel s flush)) bs
       end.
  Proof.
    induction fuel as [|f IH]; intros s HI Hmz.
    { exfalso. pose proof (HTI_facts s HI) as (D & _ & V & _). pose proof (sv_ain _ _ V). pose proof (df_look _ D). unfold lz_meas in Hmz. cbn [Z.of_nat] in Hmz. lia. }
    rewrite hf_loop_ok_S, hloop_step. destruct (huff_step s HI) as [HT HC].
    destruct (snd (hf_body s flush)) eqn:E.
    - destruct HC as [HI' Hm'].
      destruct (IH (fst (hf_body s flush)) HI' ltac:(lia)) as [HL HF].
      split; [exact (conj HT HL) | exact HF].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
  Qed.

  Lemma huff_tail : forall s, HTI s -> ds_lookahead s = 0 ->
    tail0_ok fb_safe s flush
    /\ BFPOST c0 s0 flush (tail0 s flush).
  Proof.
    intros s HF Hl0.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (HTI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    set (st := set_insert s 0).
    destruct (DD_set_insert s 0 D X ltac:(clear - Hstr; lia) ltac:(clear - Sw; lia)) as [Dst Xst]. fold st in Dst, Xst.
    assert (Vst : SV c0 st) by (apply (SV_strm c0 s st eq_refl V)).
    assert (DCst : DC c0 st) by (exact (conj (conj Dst Xst) Vst)).
    assert (Hpst : ds_pending st = 0) by (exact Hp).
    assert (Hmst : dmode st = 1) by (exact Hm).
    assert (Hstst : ds_status st <> FINISH_STATE) by (exact Hst).
    assert (HKst : KV st = KV s0) by (exact HK).
    assert (Hlst : ds_lookahead st = 0) by (exact Hl0).
    assert (Host : OUTLE s0 st) by (exact Ho).
    assert (Hmast : ds_match_available st = 0) by (exact Hma).
    assert (FB : forall last, 0 <= last <= 1 ->
      let s' := flush_block_only st last in
      fblk_ok fb_safe st last /\ DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ ds_lookahead s' = 0 /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
      /\ ds_match_available s' = 0).
    { intros last Hlast.
      pose proof (hflush st last Dst Vst (DX_DXX _ Xst) (DC_fb_entry c0 st last HC0w DCst Hpst ltac:(rewrite Hmst; lia) Hlast) Hstst Hmst (DX_BND st Xst) HKst Host) as FB. cbv zeta in FB.
      destruct FB as (FO & DC' & HK' & Ho' & _ & _ & Elook' & Hpa & _ & Ema').
      cbv zeta. split; [exact FO|]. split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|].
      split; [rewrite Elook'; exact Hlst|]. split; [exact Hpa | rewrite Ema'; exact Hmast]. }
    split.
    -
      unfold tail0_ok. cbv zeta. fold st.
      split; [exact (DC_DOK c0 st HC0w DCst)|].
      split; [intros _; exact (proj1 (FB 1 ltac:(lia))) | intros _ _; exact (proj1 (FB 0 ltac:(lia)))].
    -
      unfold tail0. fold st. unfold deflate_tail. destruct (Z.eqb_spec flush Z_FINISH) as [F4|F4].
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

End Huff.


Theorem huff_bf_spec : FB_CALL -> BF_SPEC 1 (huff_ok fb_safe) deflate_huff.
Proof.
  intros HFB c0 s flush (HC0 & HDC & Hp & Hst & Hfl) Hm.
  assert (HF : HTI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact Hm|]. split; [exact Hst | apply OUTLE_refl]. }
  pose proof HDC as [[D X] V].
  assert (Hmz : 0 <= lz_meas s) by (unfold lz_meas; pose proof (df_look _ D); pose proof (sv_ain _ _ V); lia).
  destruct (huff_loop c0 s flush HC0 HFB (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as [HL HR].
  assert (POST : BFPOST c0 s flush (deflate_huff s flush)).
  { unfold deflate_huff.
    destruct (deflate_huff_loop (lz_fuel s) s flush) as [s' r] eqn:E. cbn [fst snd] in HR.
    destruct r as [bs|].
    + destruct HR as (DC' & HK' & Ho' & ->). unfold BFPOST; cbn [fst snd].
      split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
      split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
    + destruct HR as [HF' Hl']. exact (proj2 (huff_tail c0 s flush HC0 HFB _ HF' Hl')). }
  split; [| exact POST].
  unfold huff_ok. split; [exact HL|]. split.
  - destruct (snd (deflate_huff_loop (lz_fuel s) s flush)); [exact I|].
    destruct HR as [HF' Hl']. exact (proj1 (huff_tail c0 s flush HC0 HFB _ HF' Hl')).
  - destruct POST as (DC' & HK' & Ho' & _). pose proof DC' as [[D' X'] V'].
    split; [exact (lz_keeps_intro c0 _ _ D D' V V' HK' Ho') | exact (DC_DOK c0 _ (c0'_ok _ HC0) DC')].
Qed.
End RefDeflSafeL3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeL5.RefDeflSafeL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Definition TS (s : deflate_state) :=
  ((ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s, ds_level s, ds_strategy s),
   (ds_insert s, ds_w_size s, ds_matches s, ds_high_water s, ds_window_size s),
   (ds_block_start s, ds_wrap s, ds_status s, ds_lit_bufsize s, ds_bl_tree_fc s, ds_dyn_ltree_dl s, ds_dyn_dtree_dl s, ds_bl_tree_dl s),
   (ds_depth s, ds_bl_count s, ds_opt_len s, ds_static_len s, ds_hash_size s, ds_w_mask s, ds_hash_mask s, ds_hash_shift s),
   (ds_strm s, ds_pending s, ds_pending_out s, ds_bi_valid s, ds_bi_buf s, ds_last_flush s, ds_window s, KV s, ds_sym_end s),
   (ds_w_bits s, ds_hash_bits s, ds_pending_buf_size s, ds_gzhead s, ds_method s, ds_heap s)).

Lemma TS_fields : forall a b, TS b = TS a ->
  (ds_good_match b = ds_good_match a /\ ds_max_lazy_match b = ds_max_lazy_match a /\ ds_nice_match b = ds_nice_match a
   /\ ds_max_chain_length b = ds_max_chain_length a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a)
  /\ (ds_insert b = ds_insert a /\ ds_w_size b = ds_w_size a /\ ds_matches b = ds_matches a /\ ds_high_water b = ds_high_water a /\ ds_window_size b = ds_window_size a)
  /\ (ds_block_start b = ds_block_start a /\ ds_wrap b = ds_wrap a /\ ds_status b = ds_status a /\ ds_lit_bufsize b = ds_lit_bufsize a
      /\ ds_bl_tree_fc b = ds_bl_tree_fc a /\ ds_dyn_ltree_dl b = ds_dyn_ltree_dl a /\ ds_dyn_dtree_dl b = ds_dyn_dtree_dl a /\ ds_bl_tree_dl b = ds_bl_tree_dl a)
  /\ (ds_depth b = ds_depth a /\ ds_bl_count b = ds_bl_count a /\ ds_opt_len b = ds_opt_len a /\ ds_static_len b = ds_static_len a
      /\ ds_hash_size b = ds_hash_size a /\ ds_w_mask b = ds_w_mask a /\ ds_hash_mask b = ds_hash_mask a /\ ds_hash_shift b = ds_hash_shift a)
  /\ (ds_strm b = ds_strm a /\ ds_pending b = ds_pending a /\ ds_pending_out b = ds_pending_out a /\ ds_bi_valid b = ds_bi_valid a
      /\ ds_bi_buf b = ds_bi_buf a /\ ds_last_flush b = ds_last_flush a /\ ds_window b = ds_window a /\ KV b = KV a /\ ds_sym_end b = ds_sym_end a)
  /\ (ds_w_bits b = ds_w_bits a /\ ds_hash_bits b = ds_hash_bits a /\ ds_pending_buf_size b = ds_pending_buf_size a /\ ds_gzhead b = ds_gzhead a
      /\ ds_method b = ds_method a /\ ds_heap b = ds_heap a).
Proof.
  intros a b E. unfold TS in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

Lemma TF_TS : forall a b, TF b = TF a -> TS b = TS a.
Proof.
  intros a b E.
  pose proof (TF_fields _ _ E) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Epl & Ema & Epm & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                    & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
  unfold TS. rewrite Egm, Elz, Enm, Emc, Elv, Esy, Eins, Ews, Emt, Ehw, Ewsz, Ebs, Ewr, Est, Elbs, Ebl, Eldl, Eddl, Ebdl,
    Edep, Eblc, Eol, Esl, Ehs, Ewm, Ehm, Ehsh, Estrm, Epd, Epo, Ebv, Ebb, Elf, Ewin, EKV, Ese, Ewb, Ehb, Epbs, Egz, Eme, Ehp. reflexivity.
Qed.

Lemma dwf_TS_transfer : forall a b, dwf a -> TS b = TS a ->
  0 <= ds_strstart b -> 0 <= ds_lookahead b -> ds_strstart b + ds_lookahead b <= 2 * ds_w_size a -> ds_insert a <= ds_strstart b ->
  0 <= ds_match_start b < 2 ^ 32 -> 0 <= ds_ins_h b < 2 ^ 32 ->
  arr_len (ds_head b) = arr_len (ds_head a) -> arr_len (ds_prev b) = arr_len (ds_prev a) ->
  (forall i, 0 <= i < ds_hash_size a -> 0 <= arr_get (ds_head b) i < 65536) ->
  (forall i, 0 <= i < ds_w_size a -> 0 <= arr_get (ds_prev b) i < 65536) ->
  arr_len (ds_pending_buf b) = arr_len (ds_pending_buf a) ->
  (forall i, 0 <= i < ds_lit_bufsize a * 4 -> 0 <= arr_get (ds_pending_buf b) i < 256) ->
  arr_len (ds_dyn_ltree_fc b) = arr_len (ds_dyn_ltree_fc a) -> arr_len (ds_dyn_dtree_fc b) = arr_len (ds_dyn_dtree_fc a) ->
  dwf b.
Proof.
  intros a b D E Hstr Hlook Hsl Hins Hms Hih Lh Lp Bh Bp Lpb Bpb Llt Ldt.
  pose proof (dwf_sizes a D) as (Sw & _).
  pose proof (TS_fields _ _ E) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                    & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
  pose proof (KV_fields _ _ EKV) as (_ & _ & _ & KB).
  pose proof (df_tl _ D) as TL.
  destruct D; constructor; rewrite ?Est, ?Ewr, ?Elbs, ?Ebl, ?Eldl, ?Eddl, ?Ebdl, ?Edep, ?Eblc, ?Ehs, ?Ewm, ?Ehm, ?Ehsh, ?Epd, ?Epo, ?Ebv, ?Ebb, ?Elf, ?Ewin,
      ?Ese, ?Ewb, ?Ehb, ?Epbs, ?Egz, ?Eme, ?Elv, ?Esy, ?Ews, ?Eins, ?Ewsz, ?Ehw, ?Lh, ?Lp, ?Lpb; try assumption.
  - unfold deflateStateCheck in *. rewrite Est. assumption.
  - congruence.
  - congruence.
  - congruence.
  - congruence.
  - unfold tree_lens in *. rewrite Llt, Ldt, Ebl, Eldl, Eddl, Ebdl, Eblc, Ehp, Edep. assumption.
  - clear - Hstr Hlook Hsl Sw. lia.
  - clear - Hins df_ins. lia.
Qed.

Lemma DXX_TS_transfer : forall a b, DX a -> TS b = TS a -> dmode a = 4 ->
  0 <= ds_ins_h b < 65536 -> 2 <= ds_match_length b <= MAX_MATCH -> 0 <= ds_prev_length b <= MAX_MATCH ->
  (ds_match_available b = 0 \/ ds_match_available b = 1) -> 0 <= ds_prev_match b < 2 ^ 32 ->
  (ds_match_available b = 1 -> 1 <= ds_strstart b) ->
  ds_status a <> FINISH_STATE ->
  (forall t i, 0 <= arr_get (tree_dl b t) i < 65536) ->
  CHAIN b (ds_strstart b) (ds_strstart b) ->
  DXX b.
Proof.
  intros a b X E Hm Hih Hml Hpl Hma Hpm Hma1 Hst Htdl HC.
  pose proof (TS_fields _ _ E) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                    & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
  assert (Em : dmode b = dmode a) by (unfold dmode; rewrite Elv, Esy; reflexivity).
  pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc.
  destruct X; constructor; rewrite ?Em, ?Hm, ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Esy, ?Eins, ?Ews, ?Emt, ?Ehw, ?Ewsz, ?Ebs, ?Ewr, ?Est, ?Edep, ?Eblc; try assumption.
  - clear - Hml. unfold MAX_MATCH in *. lia.
  - intros HH. discriminate HH.
  - intros HH. exfalso. apply HH. reflexivity.
  - intros _. split; [clear - Hml; lia | exact Hma1].
  - intros HH. discriminate HH.
  - intros Hf. exfalso. exact (Hst Hf).
  - intros _. exact HC.
Qed.

Lemma wrap32_pred : forall x, 1 <= wrap32 x -> wrap32 (x - 1) = wrap32 x - 1.
Proof.
  intros x H. rewrite !wrap32_mod in *. Z.to_euclidean_division_equations; lia.
Qed.
Lemma wrap32_succ : forall x, wrap32 x < 2 ^ 32 - 1 -> wrap32 (x + 1) = wrap32 x + 1.
Proof.
  intros x H. rewrite !wrap32_mod in *. Z.to_euclidean_division_equations; lia.
Qed.

Ltac dsred_all :=
  cbv beta iota delta [set_status set_pending_buf set_pending_buf_size set_pending_out set_pending set_wrap set_gzhead
       set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size
       set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start
       set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead
       set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match
       set_nice_match set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc
       set_bl_tree_dl set_l_max_code set_d_max_code set_bl_max_code set_bl_count set_heap set_heap_len
       set_heap_max set_depth set_lit_bufsize set_sym_next set_sym_end set_opt_len set_static_len
       set_matches set_insert set_bi_buf set_bi_valid set_high_water set_self_blk set_window_blk
       set_prev_blk set_head_blk set_pending_buf_blk set_strm
       ds_status ds_pending_buf ds_pending_buf_size ds_pending_out ds_pending ds_wrap ds_gzhead
       ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size
       ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start
       ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead
       ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match
       ds_nice_match ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc
       ds_bl_tree_dl ds_l_max_code ds_d_max_code ds_bl_max_code ds_bl_count ds_heap ds_heap_len
       ds_heap_max ds_depth ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len
       ds_matches ds_insert ds_bi_buf ds_bi_valid ds_high_water ds_self_blk ds_window_blk
       ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm
       dmode nsym sym_okb sym_lc sym_dist sym_d0 sym_d1 sym_buf_get freq_hist sym_lcode sym_isdist sym_dcode tree_fc tree_dl tree_lens] in *.

Lemma set_ml_set_ml : forall X a b, set_match_length (set_match_length X a) b = set_match_length X b.
Proof. intros X a b. destruct X; reflexivity. Qed.

Lemma longest_match_min : forall s cur,
  0 <= ds_strstart s -> 0 <= ds_prev_length s <= MAX_MATCH -> 0 <= ds_lookahead s ->
  Z.min (ds_prev_length s) (ds_lookahead s) <= snd (longest_match s cur).
Proof.
  intros s cur Hstr Hpl Hlook. unfold longest_match. cbv zeta.
  match goal with |- context [longest_match_loop ?f s cur ?ch ?bl ?nice ?limit ?se1 ?se] =>
    destruct (lm_loop_facts f s cur ch bl nice limit se1 se Hstr Hpl) as (ms & b & Er & Hb & Hup & Hms);
    rewrite Er end.
  assert (El : ds_lookahead (match ms with Some m => set_match_start s m | None => s end) = ds_lookahead s) by (destruct ms; reflexivity).
  rewrite El. destruct (Z.leb_spec b (ds_lookahead s)); cbn [fst snd]; lia.
Qed.


Lemma lm_curs_visited_gen : forall s1 str k,
  CHAIN s1 (str - 1) (str - 1) ->
  ds_w_size s1 = 2 ^ k -> 0 <= k -> ds_w_mask s1 = ds_w_size s1 - 1 -> arr_len (ds_prev s1) = ds_w_size s1 ->
  arr_len (ds_head s1) = ds_hash_size s1 -> 0 <= ds_hash_mask s1 -> ds_hash_mask s1 = ds_hash_size s1 - 1 ->
  0 <= str < 2 ^ 16 ->
  let s2 := fst (insert_string s1 str) in
  let cur := snd (insert_string s1 str) in
  cur <> 0 ->
  forall s' f ch bl nice limit se1 se,
    ds_prev s' = ds_prev s2 -> ds_w_mask s' = ds_w_mask s2 -> ds_w_size s' = ds_w_size s2 -> 0 <= limit ->
    Forall (fun c => 1 <= c <= str - 1) (lm_curs f s' cur ch bl nice limit se1 se).
Proof.
  intros s1 str k HC Ews Hk Ewm Lp Lh Hm0 Ehm Hstr s2 cur Hnz s' f ch bl nice limit se1 se Ep' Em' Ew' Hlim.
  destruct (CHAIN_insert_string s1 str (str - 1) (str - 1) k HC Ews Hk Ewm Lp Lh Hm0 Ehm Hstr) as [(WS & H1 & H2) Hcur].
  fold s2 in H1, H2. fold cur in Hcur.
  destruct Hcur as [Z0|B]; [exfalso; exact (Hnz Z0)|].
  assert (Hcw : WS (Z.land cur (ds_w_mask s2))).
  { assert (Hslot : WS (Z.land str (ds_w_mask s1))).
    { subst s2 cur. rewrite insert_string_eq in H1. cbv zeta in H1. cbn [fst snd] in H1.
      set (h := update_hash s1 (ds_ins_h s1) (arr_get (ds_window s1) (str + (MIN_MATCH - 1)))) in *.
      pose proof (update_hash_range s1 (ds_ins_h s1) (arr_get (ds_window s1) (str + (MIN_MATCH - 1))) Hm0) as Hh. fold h in Hh. rewrite Ehm in Hh.
      specialize (H1 h).
      change (ds_hash_size (set_head ?x ?a)) with (ds_hash_size s1) in H1.
      change (ds_head (set_head ?x ?a)) with a in H1.
      change (ds_w_mask (set_head ?x ?a)) with (ds_w_mask s1) in H1.
      specialize (H1 ltac:(lia)). rewrite arr_get_set_same in H1 by (rewrite Lh; lia).
      assert (Ew16 : wrap16 str = str) by (rewrite wrap16_mod; apply Z.mod_small; lia). rewrite Ew16 in H1.
      destruct H1 as [S0|[_ W]]; [|exact W].
      exfalso. lia. }
    pose proof (H2 _ Hslot) as [_ P].
    subst s2 cur. rewrite insert_string_eq in P |- *. cbv zeta in P. cbn [fst snd] in P |- *.
    change (ds_prev (set_head (set_prev ?x ?b) ?a)) with b in P.
    change (ds_w_mask (set_head (set_prev (set_ins_h s1 ?hh) ?b) ?a)) with (ds_w_mask s1) in P |- *.
    rewrite arr_get_set_same in P by (rewrite Lp; pose proof (land_wmask_range k str Hk); rewrite <- Ews, <- Ewm in *; lia).
    destruct P as [Z0|[_ W]]; [exfalso; rewrite insert_string_eq in B; cbv zeta in B; cbn [snd] in B; lia | exact W]. }
  pose proof (lm_curs_bound f s' cur ch bl nice limit se1 se (Z.max (str - 1) (str - 1)) WS) as HB.
  rewrite Ep', Em', Ew' in HB.
  eapply Forall_impl; [| apply HB; [exact H2 | exact Hlim | lia | exact Hcw]].
  intros c Hc. cbv beta in Hc. lia.
Qed.

Lemma mod16_of_wrap32 : forall x c, wrap32 x = c -> 2 <= c < 2 ^ 16 + 2 -> (x + -2) mod 2 ^ 16 = c - 2.
Proof. intros x c H R. rewrite wrap32_mod in H. Z.to_euclidean_division_equations. nia. Qed.


Section Slow.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis HFB : FB_CALL.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Definition STI (s : deflate_state) : Prop :=
    DC c0 s /\ KV s = KV s0 /\ ds_pending s = 0 /\ dmode s = 4 /\ ds_status s <> FINISH_STATE /\ OUTLE s0 s.

  Lemma STI_facts : forall s, STI s ->
    dwf s /\ DX s /\ SV c0 s
    /\ 512 <= ds_w_size s <= 32768 /\ 256 <= ds_hash_size s <= 65536 /\ 2048 <= ds_lit_bufsize s <= 32768
    /\ (ds_match_available s = 0 \/ ds_match_available s = 1) /\ 2 <= ds_match_length s <= 258 /\ 0 <= ds_prev_length s <= 258
    /\ 0 <= nsym s <= ds_lit_bufsize s - 2 /\ ds_sym_next s = 3 * nsym s /\ ds_sym_end s = (ds_lit_bufsize s - 1) * 3
    /\ 0 <= ds_strstart s /\ 0 <= ds_lookahead s /\ ds_strstart s + ds_lookahead s <= 2 * ds_w_size s
    /\ 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s + ds_match_available s
    /\ (ds_match_available s = 1 -> 1 <= ds_strstart s)
    /\ (MIN_MATCH <= ds_match_length s -> ds_match_length s <= ds_lookahead s + 1 /\ 1 <= ds_strstart s
                                          /\ 2 <= wrap32 (ds_strstart s - ds_match_start s) <= ds_w_size s - MIN_LOOKAHEAD + 1).
  Proof.
    intros s (HDC & HK & Hp & Hm & Hst & Ho). pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
    destruct (dx_slow _ X Hm) as (Hml2 & Hma1 & H3). pose proof (dx_ml _ X) as Hml. pose proof (dx_pl _ X) as Hpl. unfold MAX_MATCH in Hml, Hpl.
    pose proof (dx_ma _ X) as Hma.
    pose proof (dx_nsym _ X). pose proof (dx_sn _ X). pose proof (df_symend _ D). pose proof (df_strstart _ D). pose proof (df_look _ D). pose proof (df_sl _ D).
    pose proof (dx_ext _ X ltac:(rewrite Hm; lia)) as He.
    split; [exact D|]. split; [exact X|]. split; [exact V|]. split; [exact Sw|]. split; [exact Sh|]. split; [exact Sl|].
    split; [exact Hma|]. split; [lia|]. split; [lia|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [lia|]. split; [assumption|]. split; [assumption|]. split; [exact He|]. split; [exact Hma1 | exact H3].
  Qed.

  Lemma sfill_stage : forall s, STI s ->
    let r := st_fill s flush in
    STI (fst r) /\ lz_meas (fst r) = lz_meas s
    /\ 0 <= ds_lookahead s <= 2 * ds_w_size s
    /\ (ds_lookahead s < MIN_LOOKAHEAD -> fw_wf (ds_w_size s) (ds_hash_size s) s)
    /\ 0 <= ds_lookahead (fst r) <= 2 * ds_w_size s
    /\ ds_w_size (fst r) = ds_w_size s
    /\ (snd r = None -> 1 <= ds_lookahead (fst r))
    /\ (snd r = Some LBreak -> ds_lookahead (fst r) = 0)
    /\ (forall bs, snd r = Some (LRet bs) -> bs = need_more)
    /\ ds_strstart (fst r) + MIN_LOOKAHEAD <= 2 * ds_w_size s
    /\ snd r <> Some LCont
    /\ ds_lookahead s <= ds_lookahead (fst r)
    /\ ds_match_length (fst r) = ds_match_length s /\ ds_match_available (fst r) = ds_match_available s.
  Proof.
    intros s HF r. subst r. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (STI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & _).
    assert (Hwr : 0 <= ds_wrap s) by (pose proof (dx_wrapneg _ X); pose proof (df_wrap _ D); destruct (Z_lt_le_dec (ds_wrap s) 0); [exfalso; apply Hst; auto | lia]).
    assert (HW : fw_wf (ds_w_size s) (ds_hash_size s) s).
    { apply (dwf_fw_wf s D Hwr (sv_nin _ _ V) (sv_ain _ _ V) ltac:(rewrite (sv_input _ _ V); pose proof (sv_inlen _ _ V); lia)
             (sv_tin _ _ V) (sv_adler _ _ V) (sv_ib _ _ V)). }
    unfold st_fill.
    destruct (Z.ltb_spec (ds_lookahead s) MIN_LOOKAHEAD) as [Hlt|Hge].
    - destruct (DC_fill_window c0 s HC0w HDC ltac:(rewrite Hm; lia) Hst Hlt) as (HDC' & HK' & Ho' & R' & Eext & HL' & HX' & HW' & SS' & _).
      pose proof (fw_rest_fields _ _ R') as ((Est & _ & _ & _ & Epd & _) & (_ & _ & Elv & Esy & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _) & _).
      pose proof (fw_rest_fields _ _ R') as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eml & Epm & Ema & Epl') & _).
      pose proof (fill_window_keep s) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ksum).
      assert (HF' : STI (fill_window s)).
      { split; [exact HDC'|]. split; [rewrite HK'; exact HK|]. split; [rewrite Epd; exact Hp|].
        split; [unfold dmode; rewrite Elv, Esy; exact Hm|]. split; [rewrite Est; exact Hst | exact (OUTLE_trans _ _ _ Ho Ho')]. }
      pose proof (wf_ws _ _ _ HW') as Ews'.
      destruct ((ds_lookahead (fill_window s) <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)) eqn:E1.
      + cbn [fst snd]. split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [lia|]. split; [intros _; exact HW|].
        split; [lia|]. split; [exact Ews'|]. split; [intros HH; discriminate HH|]. split; [intros HH; discriminate HH|].
        split; [intros bs Hbs; injection Hbs as <-; reflexivity|]. split; [clear - SS'; lia|]. split; [intros HH; discriminate HH|].
        split; [lia|]. split; [exact Eml | exact Ema].
      + destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [E0|E0]; cbn [fst snd].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [lia|]. split; [intros _; exact HW|].
          split; [lia|]. split; [exact Ews'|]. split; [intros HH; discriminate HH|]. split; [intros _; exact E0|].
          split; [intros bs Hbs; discriminate Hbs|]. split; [clear - SS'; lia|]. split; [intros HH; discriminate HH|].
          split; [lia|]. split; [exact Eml | exact Ema].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [lia|]. split; [intros _; exact HW|].
          split; [lia|]. split; [exact Ews'|]. split; [intros _; lia|].
          split; [intros HH; discriminate HH|]. split; [intros bs Hbs; discriminate Hbs|]. split; [clear - SS'; lia|]. split; [intros HH; discriminate HH|].
          split; [lia|]. split; [exact Eml | exact Ema].
    - cbn [fst snd]. split; [exact HF|]. split; [reflexivity|]. split; [lia|]. split; [intros; lia|].
      split; [lia|]. split; [reflexivity|]. split; [intros _; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hge; lia|].
      split; [intros HH; discriminate HH|]. split; [intros bs Hbs; discriminate Hbs|]. split; [clear - Hge Hsl; lia|]. split; [intros HH; discriminate HH|].
      split; [lia|]. split; reflexivity.
  Qed.

  Definition SHREL (s1 s2 : deflate_state) : Prop :=
    TS s2 = TS s1 /\ ds_strstart s2 = ds_strstart s1 /\ ds_match_length s2 = ds_match_length s1 /\ ds_lookahead s2 = ds_lookahead s1
    /\ ds_sym_next s2 = ds_sym_next s1 /\ ds_match_start s2 = ds_match_start s1 /\ ds_pending_buf s2 = ds_pending_buf s1
    /\ ds_dyn_ltree_fc s2 = ds_dyn_ltree_fc s1 /\ ds_dyn_dtree_fc s2 = ds_dyn_dtree_fc s1
    /\ ds_prev_length s2 = ds_prev_length s1 /\ ds_prev_match s2 = ds_prev_match s1 /\ ds_match_available s2 = ds_match_available s1
    /\ arr_len (ds_head s2) = arr_len (ds_head s1) /\ arr_len (ds_prev s2) = arr_len (ds_prev s1)
    /\ (forall i, 0 <= i < ds_hash_size s1 -> 0 <= arr_get (ds_head s2) i < 65536)
    /\ (forall i, 0 <= i < ds_w_size s1 -> 0 <= arr_get (ds_prev s2) i < 65536)
    /\ 0 <= ds_ins_h s2 < 65536
    /\ CHAIN s2 (ds_strstart s1) (ds_strstart s1).

  Lemma shash_stage : forall s1, STI s1 -> 1 <= ds_lookahead s1 ->
    let r := st_hash s1 in
    SHREL s1 (fst r)
    /\ (snd r <> 0 -> wrap32 (ds_strstart s1 - snd r) <= ds_w_size s1 - MIN_LOOKAHEAD ->
          (forall s' f ch bl nice limit se1 se,
             ds_prev s' = ds_prev (fst r) -> ds_w_mask s' = ds_w_mask (fst r) -> ds_w_size s' = ds_w_size (fst r) -> 0 <= limit ->
             Forall (fun c => 1 <= c <= ds_strstart s1 - 1) (lm_curs f s' (snd r) ch bl nice limit se1 se))
          /\ 1 <= snd r <= ds_strstart s1 - 1 /\ ds_strstart s1 - snd r <= ds_w_size s1 - MIN_LOOKAHEAD /\ MIN_MATCH <= ds_lookahead s1).
  Proof.
    intros s1 HF Hl1 r. subst r. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (STI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & _).
    pose proof (dx_chain _ X ltac:(rewrite Hm; lia)) as HC. pose proof (dx_insh _ X) as Hih.
    unfold st_hash.
    destruct (Z.leb_spec MIN_MATCH (ds_lookahead s1)) as [Big|Small].
    - pose proof (insert_string_facts s1 (ds_strstart s1)) as IF. cbv zeta in IF.
      destruct IF as (Ehh & Eih & Ehd & Epv & Estrm & Ewin & Elook & Estr & Ebs & Eml & Esn & Elfc & Edfc & Epd & Epb & Ebv & Ebb & Eins & Epl & Ems & Hh).
      specialize (Hh ltac:(rewrite (df_hmask _ D); lia)). rewrite (df_hmask _ D) in Hh.
      destruct (CHAIN_insert_string s1 (ds_strstart s1) (ds_strstart s1 - 1) (ds_strstart s1 - 1) (ds_w_bits s1) HC
                  (df_wsize _ D) ltac:(pose proof (df_wbits _ D); lia) (df_wmask _ D) (df_pl _ D) (df_hl _ D)
                  ltac:(rewrite (df_hmask _ D); lia) (df_hmask _ D) ltac:(unfold MIN_MATCH in Big; lia)) as [HC2 Hhh].
      replace (Z.max (ds_strstart s1 - 1) (ds_strstart s1)) with (ds_strstart s1) in HC2 by lia.
      replace (Z.max (ds_strstart s1 - 1) (ds_strstart s1 - 1)) with (ds_strstart s1 - 1) in HC2 by lia.
      set (s2 := fst (insert_string s1 (ds_strstart s1))) in *. set (hh := snd (insert_string s1 (ds_strstart s1))) in *.
      split.
      + unfold SHREL. rewrite Ehd, Epv, !arr_len_set.
        split; [subst s2; rewrite insert_string_fst; reflexivity|].
        split; [exact Estr|]. split; [exact Eml|]. split; [exact Elook|]. split; [exact Esn|]. split; [exact Ems|]. split; [exact Epb|].
        split; [exact Elfc|]. split; [exact Edfc|]. split; [exact Epl|].
        split; [subst s2; rewrite insert_string_fst; reflexivity|]. split; [subst s2; rewrite insert_string_fst; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [intros i Hi; rewrite arr_get_set; destruct (_ && _); [apply wrap16_range | apply (df_hb _ D); exact Hi]|].
        split; [intros i Hi; rewrite arr_get_set; destruct (_ && _); [apply (df_hb _ D); lia | apply (df_pb _ D); exact Hi]|].
        split; [rewrite Eih; lia|].
        eapply CHAIN_mono; [| | exact HC2]; lia.
      + intros Hnz Hdist.
        assert (Hhh1 : 1 <= hh <= ds_strstart s1 - 1) by (destruct Hhh as [Z0|B]; [exfalso; exact (Hnz Z0) | exact B]).
        rewrite wrap32_id in Hdist by lia.
        split; [| split; [exact Hhh1 | split; [exact Hdist | exact Big]]].
        intros s' f ch bl nice limit se1 se Ep' Em' Ew' Hlim.
        exact (lm_curs_visited_gen s1 (ds_strstart s1) (ds_w_bits s1) HC (df_wsize _ D) ltac:(pose proof (df_wbits _ D); lia) (df_wmask _ D) (df_pl _ D) (df_hl _ D)
                 ltac:(rewrite (df_hmask _ D); lia) (df_hmask _ D) ltac:(unfold MIN_MATCH in Big; lia) Hnz s' f ch bl nice limit se1 se Ep' Em' Ew' Hlim).
    - cbn [fst snd]. split.
      + unfold SHREL. repeat (split; [reflexivity|]).
        split; [intros i Hi; apply (df_hb _ D); exact Hi|].
        split; [intros i Hi; apply (df_pb _ D); exact Hi|].
        split; [exact Hih|]. eapply CHAIN_mono; [| | exact HC]; lia.
      + intros Hnz. exfalso. apply Hnz. reflexivity.
  Qed.

  Definition SMREL (s1 s2 s4 : deflate_state) : Prop :=
    TS s4 = TS s1 /\ ds_strstart s4 = ds_strstart s1 /\ ds_lookahead s4 = ds_lookahead s1
    /\ ds_sym_next s4 = ds_sym_next s1 /\ ds_pending_buf s4 = ds_pending_buf s1
    /\ ds_dyn_ltree_fc s4 = ds_dyn_ltree_fc s1 /\ ds_dyn_dtree_fc s4 = ds_dyn_dtree_fc s1
    /\ ds_head s4 = ds_head s2 /\ ds_prev s4 = ds_prev s2 /\ ds_ins_h s4 = ds_ins_h s2
    /\ ds_prev_length s4 = ds_match_length s1 /\ ds_prev_match s4 = ds_match_start s1 /\ ds_match_available s4 = ds_match_available s1
    /\ 2 <= ds_match_length s4 <= MAX_MATCH /\ 0 <= ds_match_start s4 < 2 ^ 32
    /\ (MIN_MATCH <= ds_match_length s4 ->
          ds_match_length s4 <= ds_lookahead s1
          /\ (ds_prev_length s4 < ds_match_length s4 -> 1 <= ds_strstart s1 - ds_match_start s4 <= ds_w_size s1 - MIN_LOOKAHEAD)).

  Lemma slm_stage : forall s1 s2 hh, STI s1 -> 1 <= ds_lookahead s1 -> ds_strstart s1 + MIN_LOOKAHEAD <= 2 * ds_w_size s1 -> SHREL s1 s2 ->
    (hh <> 0 -> wrap32 (ds_strstart s1 - hh) <= ds_w_size s1 - MIN_LOOKAHEAD ->
       (forall s' f ch bl nice limit se1 se,
          ds_prev s' = ds_prev s2 -> ds_w_mask s' = ds_w_mask s2 -> ds_w_size s' = ds_w_size s2 -> 0 <= limit ->
          Forall (fun c => 1 <= c <= ds_strstart s1 - 1) (lm_curs f s' hh ch bl nice limit se1 se))
       /\ 1 <= hh <= ds_strstart s1 - 1 /\ ds_strstart s1 - hh <= ds_w_size s1 - MIN_LOOKAHEAD /\ MIN_MATCH <= ds_lookahead s1) ->
    let s3 := prev_st s2 in
    SMREL s1 s2 (st_lm s3 hh)
    /\ (sl_lm_cond s3 hh = true -> lm_ok s3 hh).
  Proof.
    intros s1 s2 hh HF Hl1 Hss HR Hlm s3.
    pose proof (STI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & _).
    destruct HR as (T2 & Estr & Eml & Elook & Esn & Ems & Epb & Elfc & Edfc & Epl & Epm & Ema & Lh & Lp & Bh & Bp & Bih & HC2).
    pose proof (TS_fields _ _ T2) as ((Egm & _ & Enm & Emc & _ & _) & (_ & Ews & _) & _ & (_ & _ & _ & _ & _ & Ewm & _) & (_ & _ & _ & _ & _ & _ & Ewin & _) & _).
    pose proof (cfg_ranges s1 D X ltac:(pose proof HF as (_ & _ & _ & Hm & _); rewrite Hm; lia)) as (_ & Gg & Glz & Gn & Gc).
    assert (T3 : TS s3 = TS s1) by (subst s3; unfold prev_st; etransitivity; [| exact T2]; reflexivity).
    assert (E3 : ds_strstart s3 = ds_strstart s1 /\ ds_lookahead s3 = ds_lookahead s1 /\ ds_prev_length s3 = ds_match_length s1
                 /\ ds_prev s3 = ds_prev s2 /\ ds_w_mask s3 = ds_w_mask s2 /\ ds_w_size s3 = ds_w_size s2 /\ ds_window s3 = ds_window s1
                 /\ ds_good_match s3 = ds_good_match s1 /\ ds_nice_match s3 = ds_nice_match s1 /\ ds_max_chain_length s3 = ds_max_chain_length s1).
    { subst s3; unfold prev_st; dsred. rewrite Estr, Elook, Eml, Ewin, Egm, Enm, Emc. repeat split; reflexivity. }
    destruct E3 as (Estr3 & Elook3 & Epl3 & Epv3 & Ewm3 & Ews3 & Ewin3 & Egm3 & Enm3 & Emc3).
    assert (LMF : sl_lm_cond s3 hh = true ->
      lm_ok s3 hh
      /\ exists ms, fst (longest_match s3 hh) = match ms with Some m => set_match_start s3 m | None => s3 end
           /\ 2 <= snd (longest_match s3 hh) <= MAX_MATCH /\ snd (longest_match s3 hh) <= ds_lookahead s1
           /\ (ds_prev_length s3 < snd (longest_match s3 hh) -> exists m, ms = Some m /\ 1 <= m /\ 1 <= ds_strstart s1 - m <= ds_w_size s1 - MIN_LOOKAHEAD)
           /\ (ms = None \/ exists m, ms = Some m /\ 1 <= m /\ 1 <= ds_strstart s1 - m <= ds_w_size s1 - MIN_LOOKAHEAD)).
    { intros Hc. unfold sl_lm_cond in Hc. apply andb_prop in Hc as [Hc Hdist]. apply andb_prop in Hc as [Hnz _].
      assert (Hnz' : hh <> 0) by (intros E0; rewrite E0 in Hnz; discriminate Hnz).
      apply Z.leb_le in Hdist. rewrite Estr3, Ews3, Ews in Hdist.
      destruct (Hlm Hnz' ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; exact Hdist)) as (LV & Hh1 & Hhd & Big).
      assert (LVs : Forall (fun c => 1 <= c <= ds_strstart s1 - 1) (lm_visited s3 hh)).
      { unfold lm_visited. cbv zeta. apply LV; [exact Epv3 | exact Ewm3 | exact Ews3 |].
        rewrite Estr3, Ews3, Ews. unfold NIL. destruct (Z.ltb_spec (ds_w_size s1 - MIN_LOOKAHEAD) (ds_strstart s1)); lia. }
      destruct (longest_match_facts s3 hh ltac:(rewrite Estr3; lia) ltac:(rewrite Epl3; unfold MAX_MATCH; lia) ltac:(rewrite Elook3; lia))
        as (ms & Efst & Hml3 & Hle & Hup & Hms).
      pose proof (longest_match_min s3 hh ltac:(rewrite Estr3; lia) ltac:(rewrite Epl3; unfold MAX_MATCH; lia) ltac:(rewrite Elook3; lia)) as Hmin.
      rewrite Epl3, Elook3 in Hmin.
      assert (Hm : forall m, In m (lm_visited s3 hh) -> 1 <= m /\ 1 <= ds_strstart s1 - m <= ds_w_size s1 - MIN_LOOKAHEAD).
      { intros m Hin. rewrite Forall_forall in LVs. pose proof (LVs m Hin) as Bm.
        unfold lm_visited in Hin. cbv zeta in Hin.
        match type of Hin with In m (lm_curs ?f ?s ?cur ?ch ?bl ?nice ?limit ?se1 ?se) =>
          pose proof (lm_curs_limit f s cur ch bl nice limit se1 se) as LL end.
        rewrite Forall_forall in LL. specialize (LL m Hin). cbv beta in LL.
        rewrite Estr3, Ews3, Ews in LL. unfold NIL in LL.
        destruct LL as [-> | LL]; [lia|].
        destruct (Z.ltb_spec (ds_w_size s1 - MIN_LOOKAHEAD) (ds_strstart s1)); unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia. }
      split.
      - unfold lm_ok. rewrite Ews3, Ews, Estr3, Ewm3, Ewm, Epl3, Enm3, Elook3, Egm3, Emc3, Ewin3.
        split; [exact (df_wb _ D)|]. split; [rewrite Epv3; exact Bp|]. split; [lia|].
        split; [unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hss; lia|]. split; [exact (df_wmask _ D)|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [destruct (_ <=? _); [rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_lower_bound; lia | lia]|].
        split; [lia|]. split; [eapply Forall_impl; [| exact LVs]; intros c Hc; cbv beta in Hc; lia|].
        unfold MAX_MATCH in Hml3. exact Hml3.
      - exists ms. split; [exact Efst|]. split; [unfold MIN_MATCH in Big; clear - Hml3 Hmin Big Hml; lia|]. split; [rewrite <- Elook3; exact Hle|].
        split.
        + intros Hlt. destruct (Hup Hlt) as (m & Em & Hin). exists m. split; [exact Em | exact (Hm m Hin)].
        + destruct Hms as [Hn0 | (m & Em & Hin)]; [left; exact Hn0 | right; exists m; split; [exact Em | exact (Hm m Hin)]]. }
    split; [| intros Hc; exact (proj1 (LMF Hc))].
    unfold st_lm. destruct (sl_lm_cond s3 hh) eqn:Elm.
    - destruct (LMF eq_refl) as (_ & ms & Efst & Rml & Hle & Hup & Hms).
      set (res := snd (longest_match s3 hh)) in *. rewrite Efst.
      set (s4a := set_match_length (match ms with Some m => set_match_start s3 m | None => s3 end) res).
      assert (E4 : forall v, let s4 := set_match_length s4a v in
        TS s4 = TS s1 /\ ds_strstart s4 = ds_strstart s1 /\ ds_lookahead s4 = ds_lookahead s1
        /\ ds_sym_next s4 = ds_sym_next s1 /\ ds_pending_buf s4 = ds_pending_buf s1
        /\ ds_dyn_ltree_fc s4 = ds_dyn_ltree_fc s1 /\ ds_dyn_dtree_fc s4 = ds_dyn_dtree_fc s1
        /\ ds_head s4 = ds_head s2 /\ ds_prev s4 = ds_prev s2 /\ ds_ins_h s4 = ds_ins_h s2
        /\ ds_prev_length s4 = ds_match_length s1 /\ ds_prev_match s4 = ds_match_start s1 /\ ds_match_available s4 = ds_match_available s1
        /\ ds_match_length s4 = v
        /\ ds_match_start s4 = match ms with Some m => m | None => ds_match_start s1 end).
      { intros v. subst s4a s3. unfold prev_st. destruct ms as [m|]; dsred; rewrite ?Estr, ?Elook, ?Esn, ?Epb, ?Elfc, ?Edfc, ?Eml, ?Ems, ?Ema;
          (split; [etransitivity; [| exact T2]; reflexivity | repeat split; reflexivity]). }
      assert (SM : forall v, (v = 2 \/ v = res) -> SMREL s1 s2 (set_match_length s4a v)).
      { intros v Hv. destruct (E4 v) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15).
        unfold SMREL. rewrite A14, A15, A11.
        split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
        split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [reflexivity|]. split; [exact A12|]. split; [exact A13|].
        split; [unfold MAX_MATCH in *; clear - Hv Rml; lia|].
        split; [destruct Hms as [-> | (m & -> & Hm1 & Hmm)]; [exact (df_ms _ D) | clear - Hm1 Hmm Hstr Hsl Hlook Sw; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia]|].
        intros H3. destruct Hv as [-> | ->]; [exfalso; unfold MIN_MATCH in H3; clear - H3; lia|].
        split; [exact Hle|]. intros Hlt. rewrite Epl3 in Hup. destruct (Hup Hlt) as (m & -> & _ & Hmm). exact Hmm. }
      assert (Ea : set_match_length s4a res = s4a) by (subst s4a; apply set_ml_set_ml).
      destruct (sl_filter s4a).
      + apply SM. left; reflexivity.
      + rewrite <- Ea. apply SM. right; reflexivity.
    - unfold SMREL. subst s3. unfold prev_st. dsred. rewrite Estr, Elook, Esn, Epb, Elfc, Edfc, Eml, Ems, Ema.
      split; [etransitivity; [| exact T2]; reflexivity|]. repeat (split; [reflexivity|]).
      split; [unfold MAX_MATCH; lia|]. split; [exact (df_ms _ D)|].
      intros H3. exfalso. unfold MIN_MATCH in H3. clear - H3. lia.
  Qed.

  Definition ISREL (s s' : deflate_state) : Prop :=
    TS s' = TS s /\ ds_strstart s' = ds_strstart s + ds_prev_length s /\ ds_prev_length s' = 0 /\ ds_lookahead s' = ds_lookahead s
    /\ ds_sym_next s' = ds_sym_next s /\ ds_match_start s' = ds_match_start s /\ ds_pending_buf s' = ds_pending_buf s
    /\ ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s /\ ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s
    /\ ds_match_length s' = ds_match_length s /\ ds_match_available s' = ds_match_available s /\ ds_prev_match s' = ds_prev_match s
    /\ arr_len (ds_head s') = arr_len (ds_head s) /\ arr_len (ds_prev s') = arr_len (ds_prev s)
    /\ (forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head s') i < 65536)
    /\ (forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev s') i < 65536)
    /\ 0 <= ds_ins_h s' < 65536
    /\ CHAIN s' (ds_strstart s + ds_prev_length s) (ds_strstart s + ds_prev_length s).

  Lemma slow_insert_step : forall n s mi,
    deflate_slow_insert (S n) s mi
    = (let t := set_strstart s (ds_strstart s + 1) in
       let t1 := if ds_strstart t <=? mi then fst (insert_string t (ds_strstart t)) else t in
       let t2 := set_prev_length t1 (ds_prev_length t1 - 1) in
       if negb (ds_prev_length t2 =? 0) then deflate_slow_insert n t2 mi else t2).
  Proof. reflexivity. Qed.

  Lemma slow_insert_facts : forall n s mi k,
    ds_w_size s = 2 ^ k -> 0 <= k -> ds_w_mask s = ds_w_size s - 1 -> arr_len (ds_prev s) = ds_w_size s ->
    arr_len (ds_head s) = ds_hash_size s -> 0 <= ds_hash_mask s -> ds_hash_mask s = ds_hash_size s - 1 -> ds_hash_size s <= 65536 ->
    (forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head s) i < 65536) ->
    (forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev s) i < 65536) ->
    0 <= ds_ins_h s < 65536 ->
    1 <= ds_prev_length s <= Z.of_nat n -> 0 <= ds_strstart s -> ds_strstart s + ds_prev_length s < 2 ^ 16 ->
    CHAIN s (ds_strstart s) (ds_strstart s) ->
    ISREL s (deflate_slow_insert n s mi).
  Proof.
    induction n as [|n IH]; intros s mi k Ews Hk Ewm Lp Lh Hm0 Ehm Hhs Bh Bp Bih Hpl Hstr Hbnd HC; [lia|].
    rewrite slow_insert_step. cbv zeta.
    set (t := set_strstart s (ds_strstart s + 1)).
    change (ds_strstart t) with (ds_strstart s + 1).
    set (t1 := if ds_strstart s + 1 <=? mi then fst (insert_string t (ds_strstart s + 1)) else t).
    assert (Tt1 : TS t1 = TS s /\ ds_strstart t1 = ds_strstart s + 1 /\ ds_prev_length t1 = ds_prev_length s /\ ds_lookahead t1 = ds_lookahead s
                  /\ ds_sym_next t1 = ds_sym_next s /\ ds_match_start t1 = ds_match_start s /\ ds_pending_buf t1 = ds_pending_buf s
                  /\ ds_dyn_ltree_fc t1 = ds_dyn_ltree_fc s /\ ds_dyn_dtree_fc t1 = ds_dyn_dtree_fc s
                  /\ ds_match_length t1 = ds_match_length s /\ ds_match_available t1 = ds_match_available s /\ ds_prev_match t1 = ds_prev_match s
                  /\ ds_w_size t1 = ds_w_size s /\ ds_hash_size t1 = ds_hash_size s /\ ds_w_mask t1 = ds_w_mask s /\ ds_hash_mask t1 = ds_hash_mask s
                  /\ arr_len (ds_head t1) = ds_hash_size s /\ arr_len (ds_prev t1) = ds_w_size s
                  /\ (forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head t1) i < 65536)
                  /\ (forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev t1) i < 65536)
                  /\ 0 <= ds_ins_h t1 < 65536
                  /\ CHAIN t1 (ds_strstart s + 1) (ds_strstart s + 1)).
    { subst t1. destruct (ds_strstart s + 1 <=? mi).
      - pose proof (insert_string_facts t (ds_strstart s + 1)) as IF. cbv zeta in IF.
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
        split; [subst t1 t; rewrite insert_string_fst; reflexivity|].
        rewrite Estr, Epl, Elook, Esn, Ems, Epb, Elfc, Edfc, Eml, Eih, Ehd, Epv, !arr_len_set.
        subst t; dsred. repeat (split; [reflexivity|]).
        split; [exact Lh|]. split; [exact Lp|].
        split; [intros i Hi; rewrite arr_get_set; destruct (_ && _); [apply wrap16_range | apply Bh; exact Hi]|].
        split; [intros i Hi; rewrite arr_get_set; destruct (_ && _); [revert Hh2; dsred; unfold update_hash; dsred; intros Hh2; apply Bh; lia | apply Bp; exact Hi]|].
        split; [revert Hh2; dsred; intros Hh2; lia|].
        eapply CHAIN_mono; [| | exact HC1]; lia.
      - subst t. dsred. repeat (split; [reflexivity|]). split; [exact Lh|]. split; [exact Lp|]. split; [exact Bh|]. split; [exact Bp|]. split; [exact Bih|].
        apply (CHAIN_same s); dsred; try reflexivity. eapply CHAIN_mono; [| | exact HC]; lia. }
    clearbody t1. clear t.
    destruct Tt1 as (T1 & St1 & Pt1 & Lt1 & Nt1 & MSt1 & Pb1 & LFt1 & DFt1 & Mt1 & MAt1 & PMt1 & Wt1 & Ht1 & WMt1 & HMt1 & Lh1 & Lp1 & Bh1 & Bp1 & Hh1 & HC1).
    dsred. rewrite Pt1.
    destruct (Z.eqb_spec (ds_prev_length s - 1) 0) as [Z0|Z0]; cbn [negb].
    - assert (Hpl1 : ds_prev_length s = 1) by lia.
      unfold ISREL. dsred. rewrite Hpl1.
      split; [etransitivity; [| exact T1]; reflexivity|]. split; [exact St1|]. split; [lia|]. split; [exact Lt1|]. split; [exact Nt1|]. split; [exact MSt1|]. split; [exact Pb1|].
      split; [exact LFt1|]. split; [exact DFt1|]. split; [exact Mt1|]. split; [exact MAt1|]. split; [exact PMt1|].
      split; [rewrite Lh1; symmetry; exact Lh|]. split; [rewrite Lp1; symmetry; exact Lp|].
      split; [exact Bh1|]. split; [exact Bp1|]. split; [exact Hh1|].
      apply (CHAIN_same t1); dsred; try reflexivity. exact HC1.
    - pose proof (IH (set_prev_length t1 (ds_prev_length s - 1)) mi k) as IH'. revert IH'. dsred. rewrite Wt1, WMt1, Ht1, HMt1, St1, Lh1, Lp1. intros IH'.
      specialize (IH' Ews Hk Ewm ltac:(reflexivity) ltac:(reflexivity) Hm0 Ehm Hhs Bh1 Bp1 Hh1 ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(apply (CHAIN_same t1); dsred; try reflexivity; exact HC1)).
      revert IH'. unfold ISREL. dsred. rewrite Lh1, Lp1, Wt1, Ht1, St1, Lt1, Nt1, MSt1, Pb1, LFt1, DFt1, Mt1, MAt1, PMt1.
      replace (ds_strstart s + 1 + (ds_prev_length s - 1)) with (ds_strstart s + ds_prev_length s) by lia.
      intros (T' & R'). split; [rewrite T'; revert T1; unfold TS; dsred; intros T1; exact T1|].
      rewrite Lh, Lp. exact R'.
  Qed.

  Definition SDREL (s1 s7 : deflate_state) (adv : Z) : Prop :=
    TS s7 = TS s1 /\ ds_strstart s7 = ds_strstart s1 + adv /\ ds_lookahead s7 = ds_lookahead s1 - adv
    /\ ds_match_length s7 = 2 /\ ds_match_available s7 = 0 /\ ds_prev_length s7 = 0
    /\ 0 <= ds_match_start s7 < 2 ^ 32 /\ 0 <= ds_prev_match s7 < 2 ^ 32
    /\ arr_len (ds_head s7) = arr_len (ds_head s1) /\ arr_len (ds_prev s7) = arr_len (ds_prev s1)
    /\ (forall i, 0 <= i < ds_hash_size s1 -> 0 <= arr_get (ds_head s7) i < 65536)
    /\ (forall i, 0 <= i < ds_w_size s1 -> 0 <= arr_get (ds_prev s7) i < 65536)
    /\ 0 <= ds_ins_h s7 < 65536
    /\ arr_len (ds_pending_buf s7) = arr_len (ds_pending_buf s1)
    /\ (forall i, 0 <= i < ds_lit_bufsize s1 * 4 -> 0 <= arr_get (ds_pending_buf s7) i < 256)
    /\ arr_len (ds_dyn_ltree_fc s7) = arr_len (ds_dyn_ltree_fc s1) /\ arr_len (ds_dyn_dtree_fc s7) = arr_len (ds_dyn_dtree_fc s1)
    /\ (forall i, 0 <= arr_get (ds_dyn_ltree_fc s7) i < 65536) /\ (forall i, 0 <= arr_get (ds_dyn_dtree_fc s7) i < 65536)
    /\ BQ s7 /\ nsym s7 = nsym s1 + 1 /\ ds_sym_next s7 = ds_sym_next s1 + 3
    /\ CHAIN s7 (ds_strstart s7 - 1) (ds_strstart s7 - 1).

  Lemma sdist_tally : forall s1 s2 s4 d, STI s1 -> SHREL s1 s2 -> SMREL s1 s2 s4 -> 1 <= d <= 32768 ->
    let r := tr_tally_dist s4 d (ds_prev_length s4 - MIN_MATCH) in
    TALLYF s4 (fst r) /\ snd r = (ds_sym_next s1 + 3 =? ds_sym_end s1).
  Proof.
    intros s1 s2 s4 d HF HR MR Hd r. subst r.
    pose proof (STI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & _).
    destruct MR as (T4 & Estr4 & Elook4 & Esn4 & Epb4 & Elfc4 & Edfc4 & Ehd4 & Epv4 & Eih4 & Epl4 & Epm4 & Ema4 & Hml4 & Hms4 & Hlz4).
    pose proof (TS_fields _ _ T4) as ((_ & _ & _ & _ & Elv4 & Esy4) & (_ & Ews4 & _) & (_ & _ & _ & Elbs4 & Ebl4 & _) & _ & (Estrm4 & Epd4 & Epo4 & Ebv4 & _ & _ & _ & EKV4 & Ese4) & _).
    set (len := ds_prev_length s4 - MIN_MATCH).
    pose proof (tally_dist_facts s4 d len) as (TK & Esn & Ebf & Ebt & Rl & Rd & Rp). cbv zeta in *.
    assert (BQ4 : BQ s4).
    { apply (BQ_same s1); [rewrite Epb4 | rewrite Elbs4 | rewrite Esn4 | rewrite Elfc4 | rewrite Edfc4 | rewrite Ebl4 |]; try reflexivity. exact (DX_BQ s1 X). }
    assert (N4 : nsym s4 = nsym s1) by (unfold nsym; rewrite Esn4; reflexivity).
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL.
    destruct (BQ_tally_dist s4 BQ4 ltac:(rewrite Elbs4, Esn4, Epb4, (df_bl _ D); lia) ltac:(rewrite Elbs4; lia)
                ltac:(rewrite N4; lia) ltac:(rewrite Elfc4; unfold L_CODES; lia) ltac:(rewrite Edfc4; unfold D_CODES; lia)
                d len Hd) as (BQ5 & N5 & _).
    cbv zeta in BQ5, N5.
    pose proof (tally_dist_fields s4 d len) as (_ & _ & _ & Elt & Edt & _). cbv zeta in Elt, Edt.
    split; [| rewrite Ebf, Esn4, Ese4; reflexivity].
    eapply tally_common.
    - rewrite Elbs4, Epb4. exact (df_bb _ D).
    - rewrite Elfc4. exact (dx_tfc _ X DeflateState.TL).
    - rewrite Edfc4. exact (dx_tfc _ X DeflateState.TD).
    - exact TK.
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
    - destruct TK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehmk & _). exact Ehmk.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact BQ5.
    - exact N5.
  Qed.

  Lemma sdist_stage : forall s1 s2 s4, STI s1 -> 1 <= ds_lookahead s1 -> SHREL s1 s2 -> SMREL s1 s2 s4 -> dist_cond s4 = true ->
    let r := st_sdist s4 in
    SDREL s1 (fst r) (ds_match_length s1 - 1) /\ snd r = (ds_sym_next s1 + 3 =? ds_sym_end s1)
    /\ 3 <= ds_match_length s1 /\ ds_match_length s1 - 1 <= ds_lookahead s1 /\ 1 <= ds_strstart s1
    /\ sdist_D s4 < 32768.
  Proof.
    intros s1 s2 s4 HF Hl1 HR MR Hdc r. subst r.
    pose proof (STI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & Hma1 & H3).
    pose proof HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Epl2 & Epm2 & Ema2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    pose proof MR as (T4 & Estr4 & Elook4 & Esn4 & Epb4 & Elfc4 & Edfc4 & Ehd4 & Epv4 & Eih4 & Epl4 & Epm4 & Ema4 & Hml4 & Hms4 & Hlz4).
    pose proof (TS_fields _ _ T4) as ((_ & _ & _ & _ & Elv4 & Esy4) & (_ & Ews4 & _) & (_ & _ & _ & Elbs4 & Ebl4 & _) & (_ & _ & _ & _ & Ehs4 & Ewm4 & Ehm4 & _) & (Estrm4 & Epd4 & Epo4 & Ebv4 & _ & _ & _ & EKV4 & Ese4) & _).
    unfold dist_cond in Hdc. apply andb_prop in Hdc as [Hpl3 Hmlpl]. apply Z.leb_le in Hpl3. apply Z.leb_le in Hmlpl. rewrite Epl4 in Hpl3, Hmlpl.
    destruct (H3 ltac:(unfold MIN_MATCH; lia)) as (Hmll & Hstr1 & HW).
    set (W := wrap32 (ds_strstart s1 - ds_match_start s1)) in *.
    assert (Ed : wrap32 (ds_strstart s4 - 1 - ds_prev_match s4) = W - 1).
    { rewrite Estr4, Epm4. replace (ds_strstart s1 - 1 - ds_match_start s1) with (ds_strstart s1 - ds_match_start s1 - 1) by lia.
      subst W. apply wrap32_pred. lia. }
    assert (HsD : sdist_D s4 < 32768).
    { unfold sdist_D. rewrite Estr4, Epm4. rewrite (mod16_of_wrap32 _ W eq_refl ltac:(clear - HW Sw; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in HW; lia)).
      clear - HW Sw. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in HW. lia. }
    unfold st_sdist. cbv zeta. rewrite Ed.
    destruct (sdist_tally s1 s2 s4 (W - 1) HF HR MR ltac:(clear - HW Sw; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in HW; lia)) as [TY Ebf]. cbv zeta in TY, Ebf.
    change (ds_prev_length s4 - 3) with (ds_prev_length s4 - MIN_MATCH).
    destruct (tr_tally_dist s4 (W - 1) (ds_prev_length s4 - MIN_MATCH)) as [s5 bf]. cbn [fst snd] in TY, Ebf |- *.
    destruct TY as (T5 & Estr5 & Elook5 & Eml5 & Ems5 & Ehd5 & Epv5 & Eih5 & Lpb5 & Bpb5 & Llt5 & Ldt5 & Blt5 & Bdt5 & BQ5 & N5 & Esn5).
    pose proof (TF_fields _ _ T5) as ((_ & _ & _ & _ & _ & _) & (_ & Ews5 & Epl5 & Ema5 & Epm5 & _) & (_ & _ & _ & Elbs5 & Ebl5 & _) & (_ & _ & _ & _ & Ehs5 & Ewm5 & Ehm5 & _) & _).
    pose proof (TF_TS _ _ T5) as T5'.
    set (S6 := set_lookahead s5 (wrap32 (ds_lookahead s5 - (ds_prev_length s5 - 1)))).
    change (ds_prev_length S6) with (ds_prev_length s5).
    set (S7 := set_prev_length S6 (ds_prev_length s5 - 2)).
    change (ds_prev_length S7) with (ds_prev_length s5 - 2).
    set (mi := wrap32 (ds_strstart s4 + ds_lookahead s4 - 3)).
    assert (E7 : TS S7 = TS s1 /\ ds_strstart S7 = ds_strstart s1 /\ ds_prev_length S7 = ds_match_length s1 - 2 /\ ds_lookahead S7 = ds_lookahead s1 - (ds_match_length s1 - 1)
                 /\ ds_head S7 = ds_head s2 /\ ds_prev S7 = ds_prev s2 /\ ds_ins_h S7 = ds_ins_h s2 /\ ds_w_size S7 = ds_w_size s1 /\ ds_hash_size S7 = ds_hash_size s1
                 /\ ds_w_mask S7 = ds_w_mask s1 /\ ds_hash_mask S7 = ds_hash_mask s1
                 /\ ds_sym_next S7 = ds_sym_next s5 /\ ds_match_start S7 = ds_match_start s5 /\ ds_pending_buf S7 = ds_pending_buf s5
                 /\ ds_dyn_ltree_fc S7 = ds_dyn_ltree_fc s5 /\ ds_dyn_dtree_fc S7 = ds_dyn_dtree_fc s5
                 /\ ds_match_length S7 = ds_match_length s5 /\ ds_match_available S7 = ds_match_available s5 /\ ds_prev_match S7 = ds_prev_match s5).
    { subst S7 S6. dsred. rewrite Elook5, Epl5, Elook4, Epl4, Estr5, Estr4, Ehd5, Ehd4, Epv5, Epv4, Eih5, Eih4, Ews5, Ews4, Ehs5, Ehs4, Ewm5, Ewm4, Ehm5, Ehm4.
      rewrite (wrap32_id (ds_lookahead s1 - (ds_match_length s1 - 1))) by (clear - Hmll Hsl Hstr Sw Hpl3; lia).
      split; [etransitivity; [| exact T4]; etransitivity; [| exact T5']; reflexivity|]. repeat split; reflexivity. }
    destruct E7 as (T7 & Estr7 & Epl7 & Elook7 & Ehd7 & Epv7 & Eih7 & Ews7 & Ehsz7 & Ewm7 & Ehm7 & Esn7 & Ems7 & Epb7 & Elfc7 & Edfc7 & Eml7 & Ema7 & Epm7).
    pose proof (TS_fields _ _ T2) as (_ & (_ & Ews2 & _) & _ & (_ & _ & _ & _ & Ehs2 & Ewm2 & _) & _).
    pose proof (slow_insert_facts (Z.to_nat (ds_prev_length s5 - 2)) S7 mi (ds_w_bits s1)) as IS.
    rewrite Ews7, Ewm7, Epv7, Ehd7, Ehsz7, Ehm7, Eih7, Epl7, Estr7, Lp2, Lh2 in IS.
    rewrite Epl5, Epl4 in IS.
    specialize (IS (df_wsize _ D) ltac:(pose proof (df_wbits _ D); lia) (df_wmask _ D) (df_pl _ D) (df_hl _ D)
                   ltac:(rewrite (df_hmask _ D); lia) (df_hmask _ D) ltac:(lia) Bh2 Bp2 Bih2
                   ltac:(rewrite Z2Nat.id by lia; lia) Hstr ltac:(clear - Hmll Hsl Sw; lia)
                   ltac:(apply (CHAIN_same s2); [exact Ehd7 | exact Epv7 | rewrite Ehsz7; symmetry; exact Ehs2 | rewrite Ews7; symmetry; exact Ews2 | rewrite Ewm7; symmetry; exact Ewm2 | exact HC2])).
    revert IS. rewrite Epl5, Epl4. intros IS.
    set (S8 := deflate_slow_insert (Z.to_nat (ds_match_length s1 - 2)) S7 mi) in *. clearbody S8. clearbody S7. clear S6.
    destruct IS as (T8 & Estr8 & Epl8 & Elook8 & Esn8 & Ems8 & Epb8 & Elfc8 & Edfc8 & Eml8 & Ema8 & Epm8 & Lh8 & Lp8 & Bh8 & Bp8 & Bih8 & HC8).
    rewrite Estr7, Epl7 in Estr8, HC8. rewrite Elook7 in Elook8. rewrite Esn7 in Esn8. rewrite Ems7 in Ems8. rewrite Epb7 in Epb8.
    rewrite Elfc7 in Elfc8. rewrite Edfc7 in Edfc8. rewrite Epm7, Epm5, Epm4 in Epm8. rewrite Ehd7 in Lh8. rewrite Epv7 in Lp8.
    rewrite Ehsz7 in Bh8. rewrite Ews7 in Bp8.
    split; [| split; [exact Ebf | split; [unfold MIN_MATCH in Hpl3; exact Hpl3 | split; [clear - Hmll; lia | split; [exact Hstr1 | exact HsD]]]]].
    unfold SDREL. dsred. rewrite Estr8, Elook8, Esn8, Ems8, Epb8, Elfc8, Edfc8, Epm8, Epl8, Lh8, Lp8, Lh2, Lp2.
    split; [etransitivity; [| exact T7]; etransitivity; [| exact T8]; reflexivity|].
    split; [clear; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite Ems5; exact Hms4|]. split; [exact (df_ms _ D)|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Bh8|]. split; [exact Bp8|]. split; [exact Bih8|].
    split; [rewrite <- Epb4; exact Lpb5|]. split; [rewrite <- Elbs4; exact Bpb5|]. split; [rewrite <- Elfc4; exact Llt5|]. split; [rewrite <- Edfc4; exact Ldt5|]. split; [exact Blt5|]. split; [exact Bdt5|].
    pose proof (TS_fields _ _ T8) as (_ & _ & (_ & _ & _ & Elbs8 & Ebl8 & _) & _). pose proof (TS_fields _ _ T7) as (_ & _ & (_ & _ & _ & Elbs7 & Ebl7 & _) & _).
    split; [apply (BQ_same s5); dsred; [exact Epb8 | rewrite Elbs8, Elbs7, <- Elbs4; symmetry; exact Elbs5 | exact Esn8 | exact Elfc8 | exact Edfc8 | rewrite Ebl8, Ebl7, <- Ebl4; symmetry; exact Ebl5 | exact BQ5]|].
    split; [unfold nsym; dsred; rewrite Esn8; unfold nsym in N5; rewrite N5; unfold nsym; rewrite Esn4; reflexivity|].
    split; [rewrite Esn4 in Esn5; exact Esn5|].
    apply (CHAIN_same S8); dsred; try reflexivity. replace (ds_strstart s1 + (ds_match_length s1 - 2) + 1 - 1) with (ds_strstart s1 + (ds_match_length s1 - 2)) by lia. exact HC8.
  Qed.

  Lemma tally_lit_gen : forall t c,
    arr_len (ds_pending_buf t) = ds_lit_bufsize t * 4 -> tree_lens t -> BQ t -> 0 <= nsym t <= ds_lit_bufsize t - 2 -> 0 <= ds_lit_bufsize t <= 32768 ->
    (forall j, 0 <= j < ds_lit_bufsize t * 4 -> 0 <= arr_get (ds_pending_buf t) j < 256) ->
    (forall i, 0 <= arr_get (ds_dyn_ltree_fc t) i < 65536) -> (forall i, 0 <= arr_get (ds_dyn_dtree_fc t) i < 65536) ->
    let r := tr_tally_lit t c in
    TALLYF t (fst r) /\ snd r = (ds_sym_next t + 3 =? ds_sym_end t).
  Proof.
    intros t c Hbl TL HBQ Hn Hlbs Bpb Bl Bd r. subst r.
    pose proof (tally_lit_facts t c) as (TK & Esn & Ebf & Edt & Ebt & Elt & Rl & Rp). cbv zeta in *.
    pose proof TL as TL'. unfold tree_lens in TL'. destruct TL' as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    pose proof HBQ as (Q1 & _).
    destruct (BQ_tally_lit t HBQ ltac:(rewrite Hbl, Q1; lia) ltac:(lia) ltac:(lia) ltac:(rewrite L1; unfold L_CODES; lia) c) as (BQ4 & N4 & _).
    cbv zeta in BQ4, N4.
    split; [| exact Ebf].
    eapply tally_common.
    - exact Bpb.
    - exact Bl.
    - exact Bd.
    - exact TK.
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
    - destruct TK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehmk & _). exact Ehmk.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact BQ4.
    - exact N4.
  Qed.

  Definition SEND (s1 s7 : deflate_state) (adv dn : Z) : Prop :=
    TS s7 = TS s1 /\ ds_strstart s7 = ds_strstart s1 + adv /\ ds_lookahead s7 = ds_lookahead s1 - adv /\ 1 <= adv <= ds_lookahead s1 /\ adv <= 258
    /\ 2 <= ds_match_length s7 <= 258 /\ 0 <= ds_prev_length s7 <= 258 /\ (ds_match_available s7 = 0 \/ ds_match_available s7 = 1)
    /\ 0 <= ds_match_start s7 < 2 ^ 32 /\ 0 <= ds_prev_match s7 < 2 ^ 32
    /\ (MIN_MATCH <= ds_match_length s7 -> ds_match_length s7 <= ds_lookahead s7 + 1 /\ 2 <= wrap32 (ds_strstart s7 - ds_match_start s7) <= ds_w_size s1 - MIN_LOOKAHEAD + 1)
    /\ arr_len (ds_head s7) = arr_len (ds_head s1) /\ arr_len (ds_prev s7) = arr_len (ds_prev s1)
    /\ (forall i, 0 <= i < ds_hash_size s1 -> 0 <= arr_get (ds_head s7) i < 65536)
    /\ (forall i, 0 <= i < ds_w_size s1 -> 0 <= arr_get (ds_prev s7) i < 65536)
    /\ 0 <= ds_ins_h s7 < 65536
    /\ arr_len (ds_pending_buf s7) = arr_len (ds_pending_buf s1)
    /\ (forall i, 0 <= i < ds_lit_bufsize s1 * 4 -> 0 <= arr_get (ds_pending_buf s7) i < 256)
    /\ arr_len (ds_dyn_ltree_fc s7) = arr_len (ds_dyn_ltree_fc s1) /\ arr_len (ds_dyn_dtree_fc s7) = arr_len (ds_dyn_dtree_fc s1)
    /\ (forall i, 0 <= arr_get (ds_dyn_ltree_fc s7) i < 65536) /\ (forall i, 0 <= arr_get (ds_dyn_dtree_fc s7) i < 65536)
    /\ BQ s7 /\ nsym s7 = nsym s1 + dn /\ (dn = 0 \/ dn = 1) /\ ds_sym_next s7 = ds_sym_next s1 + 3 * dn
    /\ CHAIN s7 (ds_strstart s7 - 1) (ds_strstart s7 - 1)
    /\ ds_strstart s1 + adv - ds_block_start s1 <= 258 * (nsym s1 + dn) + ds_match_available s7.

  Lemma send_facts : forall s1 s7 adv dn, STI s1 -> SEND s1 s7 adv dn ->
    dwf s7 /\ SV c0 s7 /\ KV s7 = KV s0 /\ ds_pending s7 = 0 /\ dmode s7 = 4 /\ ds_status s7 <> FINISH_STATE /\ OUTLE s0 s7
    /\ ds_strm s7 = ds_strm s1 /\ lz_meas s7 = lz_meas s1 - adv /\ 0 <= ds_lookahead s7 <= 2 * ds_w_size s1
    /\ nsym s7 = nsym s1 + dn /\ ds_sym_end s7 = ds_sym_end s1 /\ ds_lit_bufsize s7 = ds_lit_bufsize s1
    /\ (nsym s7 <= ds_lit_bufsize s7 - 2 -> DX s7)
    /\ fb_entry s7 0
    /\ DXX s7 /\ BND s7.
  Proof.
    intros s1 s7 adv dn HF R.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (STI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & Hma1 & H3).
    destruct R as (T7 & Estr7 & Elook7 & Hadv & Hadv2 & Hml7 & Hpl7 & Hma7 & Hms7 & Hpm7 & H37 & Lh7 & Lp7 & Bh7 & Bp7 & Bih7 & Lpb7 & Bpb7 & Llt7 & Ldt7 & Blt7 & Bdt7 & BQ7 & N7 & Hdn & Esn7 & HC7 & Hext7).
    pose proof (TS_fields _ _ T7) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                        & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
    assert (Em7 : dmode s7 = 4) by (unfold dmode; rewrite Elv, Esy; exact Hm).
    pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl. pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc.
    assert (Htfc7 : forall t i, 0 <= arr_get (tree_fc s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_fc]; [apply Blt7 | apply Bdt7 | rewrite Ebl; apply (Xtfc DeflateState.TB i)]. }
    assert (Htdl7 : forall t i, 0 <= arr_get (tree_dl s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_dl]; rewrite ?Eldl, ?Eddl, ?Ebdl; [apply (Xtdl DeflateState.TL i) | apply (Xtdl DeflateState.TD i) | apply (Xtdl DeflateState.TB i)]. }
    assert (D7 : dwf s7).
    { apply (dwf_TS_transfer s1 s7 D T7); rewrite ?Estr7, ?Elook7, ?Lh7, ?Lp7, ?Lpb7, ?Llt7, ?Ldt7; try reflexivity; try assumption.
      - clear - Hstr Hadv. lia.
      - clear - Hadv. lia.
      - clear - Hsl. lia.
      - pose proof (df_ins _ D). clear - H Hadv. lia.
      - clear - Bih7. lia. }
    assert (SL7 : SLOW3 s7).
    { intros _ Hml3. destruct (H37 Hml3) as [A B]. split; [exact A|]. split; [rewrite Estr7; clear - Hstr Hadv; lia|]. rewrite Ews. exact B. }
    assert (XX7 : DXX s7).
    { apply (DXX_TS_transfer s1 s7 X T7 Hm); try assumption.
      all: first [unfold MAX_MATCH; assumption | intros _; rewrite Estr7; clear - Hstr Hadv; lia | eapply CHAIN_mono; [| | exact HC7]; clear; lia]. }
    assert (V7 : SV c0 s7) by (apply (SV_strm c0 s1); [exact Estrm | exact V]).
    assert (Hl7 : ds_level s7 <> 0) by (intros E0; unfold dmode in Em7; rewrite E0 in Em7; discriminate Em7).
    assert (X7 : nsym s7 <= ds_lit_bufsize s7 - 2 -> DX s7).
    { intros Hn7. destruct BQ7 as (Q1 & Q2 & Q3 & Q4).
      apply (DXX_DX s7 XX7 SL7); rewrite ?Em7, ?Emt, ?N7, ?Eol, ?Esl, ?Epd, ?Epo, ?Ebv, ?Ebs; try assumption.
      - pose proof (RefDeflSafeI1.dx_matches _ X) as HM. clear - HM Hdn. lia.
      - rewrite <- N7. exact Q1.
      - revert Hn7. rewrite N7, Elbs. clear - Hn Hdn. intros Hn7. lia.
      - rewrite <- N7. exact Q3.
      - exact (dx_opt _ X).
      - exact (dx_stat _ X).
      - intros _. rewrite Estr7. clear - Hext Hext7 Hn Hdn Hadv Hma. lia.
      - intros _. exact (dx_pout0 _ X Hp).
      - exact (dx_biv _ X).
      - intros _. exact HC7. }
    assert (FE7 : fb_entry s7 0).
    { apply (fb_entry_intro c0 s7 0 HC0w D7 V7); rewrite ?Epd, ?Epo, ?Ebv, ?Eol, ?Esl, ?Edep, ?Eblc, ?Elv, ?Estr7, ?Ebs, ?N7, ?Elbs; try assumption.
      - exact (dx_pout0 _ X Hp).
      - exact (dx_biv _ X).
      - clear - Hn Hdn. lia.
      - exact (dx_opt _ X).
      - exact (dx_stat _ X).
      - intros E0. apply Hl7. rewrite Elv. exact E0.
      - clear - Hext Hext7 Hn Hdn Hadv Hma Hma7. lia.
      - clear. lia. }
    split; [exact D7|]. split; [exact V7|]. split; [rewrite EKV; exact HK|]. split; [rewrite Epd; exact Hp|]. split; [exact Em7|].
    split; [rewrite Est; exact Hst|]. split; [apply (OUTLE_trans _ s1); [exact Ho | apply OUTLE_strm; exact Estrm]|].
    split; [exact Estrm|]. split; [unfold lz_meas; rewrite Estrm, Elook7; clear; lia|]. split; [rewrite Elook7; clear - Hadv Hlook Hsl Hstr; lia|].
    split; [exact N7|]. split; [exact Ese|]. split; [exact Elbs|]. split; [exact X7|]. split; [exact FE7|]. split; [exact XX7 | exact (conj (fun _ => HC7) SL7)].
  Qed.

  Lemma savail_send : forall s1 s2 s4, STI s1 -> 1 <= ds_lookahead s1 -> SHREL s1 s2 -> SMREL s1 s2 s4 ->
    dist_cond s4 = false -> ds_match_available s4 = 0 ->
    SEND s1 (fst (st_avail s4)) 1 0.
  Proof.
    intros s1 s2 s4 HF Hl1 HR MR Hdc Hma0.
    pose proof (STI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & Hma1 & H3).
    pose proof HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Epl2 & Epm2 & Ema2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    pose proof MR as (T4 & Estr4 & Elook4 & Esn4 & Epb4 & Elfc4 & Edfc4 & Ehd4 & Epv4 & Eih4 & Epl4 & Epm4 & Ema4 & Hml4 & Hms4 & Hlz4).
    pose proof (TS_fields _ _ T4) as ((_ & _ & _ & _ & _ & _) & (_ & Ews4 & _) & (_ & _ & _ & Elbs4 & Ebl4 & _) & (_ & _ & _ & _ & Ehs4 & Ewm4 & Ehm4 & _) & _).
    pose proof (TS_fields _ _ T2) as (_ & (_ & Ews2 & _) & _ & (_ & _ & _ & _ & Ehs2 & Ewm2 & _) & _).
    unfold dist_cond in Hdc. rewrite Epl4 in Hdc.
    assert (Hnd : MIN_MATCH <= ds_match_length s4 -> ds_prev_length s4 < ds_match_length s4).
    { intros Hm3. rewrite Epl4. apply andb_false_iff in Hdc. destruct Hdc as [Hdc|Hdc]; [apply Z.leb_gt in Hdc | apply Z.leb_gt in Hdc]; unfold MIN_MATCH in Hm3; lia. }
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL. destruct TL as (L1 & L2 & L3 & _).
    unfold st_avail. cbn [fst]. unfold SEND. dsred.
    rewrite Estr4, Elook4, Ehd4, Epv4, Eih4, Epb4, Elfc4, Edfc4, Esn4, Epl4, Epm4, Lh2, Lp2.
    split; [etransitivity; [| exact T4]; reflexivity|].
    split; [reflexivity|]. split; [clear; lia|]. split; [clear - Hl1; lia|]. split; [clear; lia|].
    split; [unfold MAX_MATCH in Hml4; exact Hml4|]. split; [clear - Hml; lia|]. split; [right; reflexivity|]. split; [exact Hms4|]. split; [exact (df_ms _ D)|].
    split.
    { intros Hm3. destruct (Hlz4 Hm3) as [Hle Hd]. specialize (Hd (Hnd Hm3)). split; [clear - Hle; lia|].
      rewrite wrap32_id by (clear - Hd Hstr Hsl Hlook Sw; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia).
      clear - Hd. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Bh2|]. split; [exact Bp2|]. split; [exact Bih2|].
    split; [reflexivity|]. split; [exact (df_bb _ D)|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (dx_tfc _ X DeflateState.TL)|]. split; [exact (dx_tfc _ X DeflateState.TD)|].
    split; [apply (BQ_same s1); dsred; rewrite ?Epb4, ?Esn4, ?Elfc4, ?Edfc4, ?Elbs4, ?Ebl4; try reflexivity; exact (DX_BQ s1 X)|].
    split; [unfold nsym; dsred; rewrite Esn4; lia|]. split; [left; reflexivity|]. split; [clear; lia|].
    split.
    { apply (CHAIN_same s2); dsred; [exact Ehd4 | exact Epv4 | rewrite Ehs4, Ehs2; reflexivity | rewrite Ews4, Ews2; reflexivity | rewrite Ewm4, Ewm2; reflexivity |].
      replace (ds_strstart s1 + 1 - 1) with (ds_strstart s1) by lia. exact HC2. }
    rewrite Ema4 in Hma0. rewrite Hma0 in Hext. clear - Hext. lia.
  Qed.

  Lemma smid_facts : forall s1 s2 s4, STI s1 -> 1 <= ds_lookahead s1 -> SHREL s1 s2 -> SMREL s1 s2 s4 ->
    dist_cond s4 = false -> ds_match_available s4 = 1 ->
    let r := tr_tally_lit s4 (arr_get (ds_window s4) (ds_strstart s4 - 1)) in
    let s5 := fst r in
    snd r = (ds_sym_next s1 + 3 =? ds_sym_end s1)
    /\ dwf s5 /\ SV c0 s5 /\ DXX s5 /\ fb_entry s5 0 /\ KV s5 = KV s0 /\ OUTLE s0 s5 /\ ds_status s5 <> FINISH_STATE /\ dmode s5 = 4
    /\ ds_strm s5 = ds_strm s1 /\ ds_strstart s5 = ds_strstart s1 /\ ds_lookahead s5 = ds_lookahead s1 /\ 1 <= ds_strstart s1
    /\ SEND s1 (set_lookahead (set_strstart s5 (ds_strstart s5 + 1)) (ds_lookahead s5 - 1)) 1 1
    /\ ds_match_available s5 = 1 /\ 2 <= ds_match_length s5 <= 258
    /\ (MIN_MATCH <= ds_match_length s5 -> ds_match_length s5 <= ds_lookahead s5 /\ 2 <= wrap32 (ds_strstart s5 + 1 - ds_match_start s5) <= ds_w_size s5 - MIN_LOOKAHEAD + 1)
    /\ ds_strstart s5 + 1 - ds_block_start s5 <= 258 * nsym s5 + 1
    /\ nsym s5 = nsym s1 + 1 /\ ds_lit_bufsize s5 = ds_lit_bufsize s1.
  Proof.
    intros s1 s2 s4 HF Hl1 HR MR Hdc Hma4 r s5. subst r s5.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (STI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & Hma1 & H3).
    pose proof HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Epl2 & Epm2 & Ema2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    pose proof MR as (T4 & Estr4 & Elook4 & Esn4 & Epb4 & Elfc4 & Edfc4 & Ehd4 & Epv4 & Eih4 & Epl4 & Epm4 & Ema4 & Hml4 & Hms4 & Hlz4).
    pose proof (TS_fields _ _ T4) as ((Egm4 & Elz4 & Enm4 & Emc4 & Elv4 & Esy4) & (Eins4 & Ews4 & Emt4 & Ehw4 & Ewsz4) & (Ebs4 & Ewr4 & Est4 & Elbs4 & Ebl4 & Eldl4 & Eddl4 & Ebdl4)
                                        & (Edep4 & Eblc4 & Eol4 & Esl4 & Ehs4 & Ewm4 & Ehm4 & Ehsh4) & (Estrm4 & Epd4 & Epo4 & Ebv4 & Ebb4 & Elf4 & Ewin4 & EKV4 & Ese4) & (Ewb4 & Ehb4 & Epbs4 & Egz4 & Eme4 & Ehp4)).
    pose proof (TS_fields _ _ T2) as (_ & (_ & Ews2 & _) & _ & (_ & _ & _ & _ & Ehs2 & Ewm2 & _) & _).
    rewrite Ema4 in Hma4.
    unfold dist_cond in Hdc. rewrite Epl4 in Hdc.
    assert (Hnd : MIN_MATCH <= ds_match_length s4 -> ds_prev_length s4 < ds_match_length s4).
    { intros Hm3. rewrite Epl4. apply andb_false_iff in Hdc. destruct Hdc as [Hdc|Hdc]; [apply Z.leb_gt in Hdc | apply Z.leb_gt in Hdc]; unfold MIN_MATCH in Hm3; lia. }
    pose proof (df_tl _ D) as TL.
    assert (TL4 : tree_lens s4) by (unfold tree_lens in *; rewrite Elfc4, Edfc4, Ebl4, Eldl4, Eddl4, Ebdl4, Eblc4, Ehp4, Edep4; exact TL).
    assert (BQ4 : BQ s4) by (apply (BQ_same s1); [exact Epb4 | exact Elbs4 | exact Esn4 | exact Elfc4 | exact Edfc4 | exact Ebl4 | exact (DX_BQ s1 X)]).
    assert (N4 : nsym s4 = nsym s1) by (unfold nsym; rewrite Esn4; reflexivity).
    destruct (tally_lit_gen s4 (arr_get (ds_window s4) (ds_strstart s4 - 1)) ltac:(rewrite Epb4, Elbs4; exact (df_bl _ D)) TL4 BQ4
                ltac:(rewrite N4, Elbs4; exact Hn) ltac:(rewrite Elbs4; clear - Sl; lia) ltac:(rewrite Elbs4, Epb4; exact (df_bb _ D))
                ltac:(rewrite Elfc4; exact (dx_tfc _ X DeflateState.TL)) ltac:(rewrite Edfc4; exact (dx_tfc _ X DeflateState.TD))) as [TY Ebf].
    cbv zeta in TY, Ebf.
    destruct (tr_tally_lit s4 (arr_get (ds_window s4) (ds_strstart s4 - 1))) as [s5 bf]. cbn [fst snd] in TY, Ebf |- *.
    destruct TY as (T5 & Estr5 & Elook5 & Eml5 & Ems5 & Ehd5 & Epv5 & Eih5 & Lpb5 & Bpb5 & Llt5 & Ldt5 & Blt5 & Bdt5 & BQ5 & N5 & Esn5).
    pose proof (TF_fields _ _ T5) as ((_ & _ & _ & _ & _ & _) & (_ & Ews5 & Epl5 & Ema5 & Epm5 & _) & (_ & _ & _ & Elbs5 & Ebl5 & _) & (_ & _ & _ & _ & Ehs5 & Ewm5 & Ehm5 & _) & _).
    pose proof (TF_TS _ _ T5) as T5'.
    assert (T51 : TS s5 = TS s1) by (rewrite T5'; exact T4).
    rewrite Estr4 in Estr5. rewrite Elook4 in Elook5. rewrite Epl4 in Epl5. rewrite Ema4 in Ema5. rewrite Epm4 in Epm5. rewrite N4 in N5. rewrite Esn4 in Esn5.
    rewrite Ehd4 in Ehd5. rewrite Epv4 in Epv5. rewrite Eih4 in Eih5. rewrite Epb4 in Lpb5. rewrite Elbs4 in Bpb5. rewrite Elfc4 in Llt5. rewrite Edfc4 in Ldt5.
    assert (SE : SEND s1 (set_lookahead (set_strstart s5 (ds_strstart s5 + 1)) (ds_lookahead s5 - 1)) 1 1).
    { unfold SEND. dsred. rewrite Estr5, Elook5, Eml5, Epl5, Ema5, Ems5, Epm5, Ehd5, Epv5, Eih5, Lpb5, Llt5, Ldt5, Lh2, Lp2.
      split; [etransitivity; [| exact T51]; reflexivity|].
      split; [reflexivity|]. split; [clear; lia|]. split; [clear - Hl1; lia|]. split; [clear; lia|].
      split; [unfold MAX_MATCH in Hml4; exact Hml4|]. split; [clear - Hml; lia|]. split; [right; exact Hma4|]. split; [exact Hms4|]. split; [exact (df_ms _ D)|].
      split.
      { intros Hm3. destruct (Hlz4 Hm3) as [Hle Hd]. specialize (Hd (Hnd Hm3)). split; [clear - Hle; lia|].
        rewrite wrap32_id by (clear - Hd Hstr Hsl Hlook Sw; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia).
        clear - Hd. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. lia. }
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Bh2|]. split; [exact Bp2|]. split; [exact Bih2|].
      split; [reflexivity|]. split; [exact Bpb5|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Blt5|]. split; [exact Bdt5|].
      split; [apply (BQ_same s5); dsred; try reflexivity; exact BQ5|].
      split; [unfold nsym; dsred; exact N5|]. split; [right; reflexivity|]. split; [exact Esn5|].
      split.
      { apply (CHAIN_same s2); dsred; [exact Ehd5 | exact Epv5 | rewrite Ehs5, Ehs4, Ehs2; reflexivity | rewrite Ews5, Ews4, Ews2; reflexivity | rewrite Ewm5, Ewm4, Ewm2; reflexivity |].
        replace (ds_strstart s1 + 1 - 1) with (ds_strstart s1) by lia. exact HC2. }
      rewrite Hma4 in Hext |- *. clear - Hext. lia. }
    pose proof (send_facts s1 _ 1 1 HF SE) as SF. cbv zeta in SF.
    destruct SF as (D7 & V7 & HK7 & Hp7 & Hm7 & Hst7 & Ho7 & Estrm7 & _).
    assert (D5 : dwf s5).
    { apply (dwf_TS_transfer s1 s5 D T51); rewrite ?Estr5, ?Elook5, ?Ems5, ?Eih5, ?Ehd5, ?Epv5, ?Lh2, ?Lp2, ?Lpb5, ?Llt5, ?Ldt5; try reflexivity; try assumption.
      all: first [exact (proj2 (df_ins _ D)) | exact Hms4 | clear - Bih2; lia | clear - Hstr; lia]. }
    assert (XX5 : DXX s5).
    { apply (DXX_TS_transfer s1 s5 X T51 Hm); rewrite ?Eih5, ?Eml5, ?Epl5, ?Ema5, ?Epm5, ?Estr5; try assumption.
      all: try (unfold MAX_MATCH in *; clear - Hml4 Hml; lia).
      all: try (right; exact Hma4). all: try exact (df_ms _ D). all: try (intros _; exact (Hma1 Hma4)).
      - pose proof (dx_tdl _ X) as Xtdl. pose proof (TS_fields _ _ T51) as (_ & _ & (_ & _ & _ & _ & _ & Eldl & Eddl & Ebdl) & _).
        intros t i. destruct t; cbn [tree_dl]; rewrite ?Eldl, ?Eddl, ?Ebdl; [apply (Xtdl DeflateState.TL i) | apply (Xtdl DeflateState.TD i) | apply (Xtdl DeflateState.TB i)].
      - apply (CHAIN_same s2); [exact Ehd5 | exact Epv5 | rewrite Ehs5, Ehs4, Ehs2; reflexivity | rewrite Ews5, Ews4, Ews2; reflexivity | rewrite Ewm5, Ewm4, Ewm2; reflexivity |].
        exact HC2. }
    assert (Estrm5 : ds_strm s5 = ds_strm s1) by (pose proof (TS_fields _ _ T51) as (_ & _ & _ & _ & (E & _) & _); exact E).
    assert (V5 : SV c0 s5) by (apply (SV_strm c0 s1); [exact Estrm5 | exact V]).
    pose proof (TS_fields _ _ T51) as ((_ & _ & _ & _ & Elv5 & Esy5) & _ & (Ebs5 & _ & Est5 & _) & (Edep5 & Eblc5 & Eol5 & Esl5 & _) & (_ & Epd5 & Epo5 & Ebv5 & _ & _ & _ & EKV5 & _) & _).
    assert (Em5 : dmode s5 = 4) by (unfold dmode; rewrite Elv5, Esy5; exact Hm).
    assert (FE5 : fb_entry s5 0).
    { pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl.
      apply (fb_entry_intro c0 s5 0 HC0w D5 V5); rewrite ?Epd5, ?Epo5, ?Ebv5, ?Eol5, ?Esl5, ?Edep5, ?Eblc5, ?Elv5, ?Estr5, ?Ebs5, ?N5, ?Elbs5, ?Elbs4; try assumption.
      - exact (dx_pout0 _ X Hp).
      - exact (dx_biv _ X).
      - clear - Hn. lia.
      - exact (dx_opt _ X).
      - exact (dx_stat _ X).
      - intros t i. destruct t; cbn [tree_fc]; [apply Blt5 | apply Bdt5 | rewrite Ebl5, Ebl4; apply (Xtfc DeflateState.TB i)].
      - exact (xx_tdl _ XX5).
      - exact (dx_depth _ X).
      - exact (dx_blc _ X).
      - intros E0. unfold dmode in Hm. rewrite E0 in Hm. discriminate Hm.
      - rewrite Hma4 in Hext. clear - Hext. lia.
      - clear. lia. }
    pose proof (TS_fields _ _ T4) as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & Ese4') & _).
    split; [rewrite Ebf, Esn4, Ese4'; reflexivity|]. split; [exact D5|]. split; [exact V5|]. split; [exact XX5|]. split; [exact FE5|]. split; [rewrite EKV5; exact HK|].
    split; [apply (OUTLE_trans _ s1); [exact Ho | apply OUTLE_strm; exact Estrm5]|]. split; [rewrite Est5; exact Hst|]. split; [exact Em5|].
    split; [exact Estrm5|]. split; [exact Estr5|]. split; [exact Elook5|]. split; [exact (Hma1 Hma4)|]. split; [exact SE|].
    split; [rewrite Ema5; exact Hma4|]. split; [rewrite Eml5; unfold MAX_MATCH in Hml4; exact Hml4|].
    split.
    { rewrite Eml5, Elook5, Estr5, Ems5, Ews5, Ews4. intros Hm3. destruct (Hlz4 Hm3) as [Hle Hd]. specialize (Hd (Hnd Hm3)). split; [exact Hle|].
      rewrite wrap32_id by (clear - Hd Hstr Hsl Hlook Sw; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia).
      clear - Hd. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. lia. }
    split; [rewrite Estr5, Ebs5, N5; rewrite Hma4 in Hext; clear - Hext; lia|].
    split; [exact N5 | rewrite Elbs5; exact Elbs4].
  Qed.

  Lemma DCW_advance1 : forall s, DCW c0 s -> ds_status s <> FINISH_STATE -> dmode s = 4 -> 1 <= ds_lookahead s ->
    ds_match_available s = 1 -> 2 <= ds_match_length s <= 258 ->
    (MIN_MATCH <= ds_match_length s -> ds_match_length s <= ds_lookahead s /\ 2 <= wrap32 (ds_strstart s + 1 - ds_match_start s) <= ds_w_size s - MIN_LOOKAHEAD + 1) ->
    ds_strstart s + 1 - ds_block_start s <= 258 * nsym s + 1 ->
    DC c0 (set_lookahead (set_strstart s (ds_strstart s + 1)) (ds_lookahead s - 1)).
  Proof.
    intros s [[D [XX XR]] V] Hst Hm Hl Hma Hml H3 Hext.
    pose proof (dwf_sizes s D) as (Sw & _). pose proof (df_strstart _ D) as Hstr. pose proof (df_sl _ D) as Hsl. pose proof (df_ins _ D) as Hins.
    split; [split|].
    - destruct s; destruct D; constructor; dsred_all; try assumption; try (clear - Hstr Hsl Hl Sw Hins; lia).
    - assert (HC7 : CHAIN (set_lookahead (set_strstart s (ds_strstart s + 1)) (ds_lookahead s - 1)) (ds_strstart s + 1) (ds_strstart s + 1)).
      { apply (CHAIN_same s); try reflexivity. eapply CHAIN_mono; [| | exact (xx_chain _ XX ltac:(rewrite Hm; lia))]; clear; lia. }
      apply DX_join.
      + pose proof (xx_slow _ XX Hm) as [_ XS1].
        destruct s; destruct XX; constructor; dsred_all; try assumption.
        * intros Hm4. split; [clear - Hml; lia | intros _; clear - Hstr; lia].
        * intros HH. exfalso. rewrite Hm in HH. discriminate HH.
        * intros Hf. exfalso. exact (Hst Hf).
        * intros _. exact HC7.
      + pose proof (xr_ext _ XR) as XE. pose proof (xr_syms _ XR) as XS. pose proof (xr_hist _ XR) as XH. pose proof (xr_tfc _ XR) as XT.
        destruct s; destruct XR; constructor; dsred_all; try assumption.
        intros Hm0. specialize (XE Hm0). clear - XE Hext Hma. lia.
      + split.
        * intros _. dsred. replace (ds_strstart s + 1 - 1) with (ds_strstart s) by lia.
          apply (CHAIN_same s); try reflexivity. apply (xx_chain _ XX). rewrite Hm. clear; lia.
        * intros _ Hm3. dsred. destruct (H3 Hm3) as [A B]. split; [clear - A; lia|]. split; [clear - Hstr; lia | exact B].
    - apply (SV_strm c0 s); [reflexivity | exact V].
  Qed.

  Definition SRET (s' : deflate_state) (bs : block_state) : Prop :=
    DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ bs = need_more.

  Lemma adv_fields : forall x a b,
    ds_strm (set_lookahead (set_strstart x a) b) = ds_strm x /\ ds_lookahead (set_lookahead (set_strstart x a) b) = b
    /\ ds_strstart (set_lookahead (set_strstart x a) b) = a /\ ds_pending (set_lookahead (set_strstart x a) b) = ds_pending x
    /\ KV (set_lookahead (set_strstart x a) b) = KV x /\ ds_match_available (set_lookahead (set_strstart x a) b) = ds_match_available x
    /\ dmode (set_lookahead (set_strstart x a) b) = dmode x /\ ds_status (set_lookahead (set_strstart x a) b) = ds_status x.
  Proof. intros x a b. repeat split; reflexivity. Qed.

  Lemma strstart_set_ma : forall x v, ds_strstart (set_match_available x v) = ds_strstart x.
  Proof. intros x v. reflexivity. Qed.

  Lemma sdist_send : forall s1 s7, STI s1 -> SDREL s1 s7 (ds_match_length s1 - 1) ->
    3 <= ds_match_length s1 -> ds_match_length s1 - 1 <= ds_lookahead s1 ->
    SEND s1 s7 (ds_match_length s1 - 1) 1.
  Proof.
    intros s1 s7 HF R Hml3 Hmll.
    pose proof (STI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & Hma1 & H3).
    destruct R as (T7 & Estr7 & Elook7 & Eml7 & Ema7 & Epl7 & Hms7 & Hpm7 & Lh7 & Lp7 & Bh7 & Bp7 & Bih7 & Lpb7 & Bpb7 & Llt7 & Ldt7 & Blt7 & Bdt7 & BQ7 & N7 & Esn7 & HC7).
    unfold SEND. rewrite Eml7, Ema7, Epl7, Esn7.
    split; [exact T7|]. split; [exact Estr7|]. split; [exact Elook7|]. split; [clear - Hml3 Hmll; lia|]. split; [clear - Hml; lia|].
    split; [clear; lia|]. split; [clear; lia|]. split; [left; reflexivity|]. split; [exact Hms7|]. split; [exact Hpm7|].
    split; [intros HH; exfalso; unfold MIN_MATCH in HH; clear - HH; lia|].
    split; [exact Lh7|]. split; [exact Lp7|]. split; [exact Bh7|]. split; [exact Bp7|]. split; [exact Bih7|].
    split; [exact Lpb7|]. split; [exact Bpb7|]. split; [exact Llt7|]. split; [exact Ldt7|]. split; [exact Blt7|]. split; [exact Bdt7|].
    split; [exact BQ7|]. split; [exact N7|]. split; [right; reflexivity|]. split; [clear; lia|]. split; [exact HC7|].
    clear - Hext Hml Hma. lia.
  Qed.

  Lemma sdist_outcome : forall s s1 s7 (bf : bool) adv,
    STI s1 -> lz_meas s1 = lz_meas s -> SEND s1 s7 adv 1 -> bf = (ds_sym_next s1 + 3 =? ds_sym_end s1) ->
    (bf = true -> flush_ok s7 0) /\ 0 <= ds_lookahead s7 <= 2 * ds_w_size s0
    /\ match snd (st_bflush s7 bf) with
       | LCont => STI (fst (st_bflush s7 bf)) /\ lz_meas (fst (st_bflush s7 bf)) < lz_meas s
       | LBreak => STI (fst (st_bflush s7 bf)) /\ ds_lookahead (fst (st_bflush s7 bf)) = 0
       | LRet bs => SRET (fst (st_bflush s7 bf)) bs
       end.
  Proof.
    intros s s1 s7 bf adv HF1 Emeas SE Ebf.
    pose proof HF1 as (_ & HK1 & _). pose proof (KV_fields _ _ HK1) as (Ews1 & _).
    pose proof (STI_facts s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hma1 & Hml1 & Hpl1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & _).
    pose proof SE as (_ & _ & _ & Hadv & _).
    pose proof (send_facts s1 s7 adv 1 HF1 SE) as SF. cbv zeta in SF.
    destruct SF as (D7 & V7 & HK7 & Hp7 & Hm7 & Hst7 & Ho7 & Estrm7 & Hmeas7 & Hl7 & N7 & Ese7 & Elbs7 & X7 & FE7 & XX7 & B7).
    split; [intros _; exact (proj1 (flush_block_only_facts c0 s7 0 HFB HC0w D7 V7 XX7 FE7 Hst7 ltac:(rewrite Hm7; lia) B7))|].
    split; [rewrite <- Ews1; exact Hl7|].
    unfold st_bflush. destruct bf.
    - rewrite flush_block_eq'.
      pose proof (flush_block_only_facts c0 s7 0 HFB HC0w D7 V7 XX7 FE7 Hst7 ltac:(rewrite Hm7; lia) B7) as FB. cbv zeta in FB.
      destruct FB as (_ & DC' & HK' & Ho' & EPF & _ & Elook' & _ & _ & _ & _ & Hpa & Eain & _).
      pose proof (PF_fields _ _ EPF) as (_ & _ & (Est' & _) & _).
      set (s' := flush_block_only s7 0) in *. clearbody s'.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [Z.eqb negb fst snd].
      + split; [exact DC'|]. split; [rewrite HK'; exact HK7|]. split; [exact (OUTLE_trans _ _ _ Ho7 Ho')|]. reflexivity.
      + split.
        * split; [exact DC'|]. split; [rewrite HK'; exact HK7|]. split; [destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)]|].
          split; [rewrite (dmode_PF _ _ EPF); exact Hm7|]. split; [rewrite Est'; exact Hst7|]. exact (OUTLE_trans _ _ _ Ho7 Ho').
        * unfold lz_meas. rewrite Elook', Eain. unfold lz_meas in Hmeas7, Emeas. rewrite <- Emeas. clear - Hmeas7 Hadv. lia.
    - cbn [fst snd].
      assert (Hn7 : nsym s7 <= ds_lit_bufsize s7 - 2).
      { symmetry in Ebf. apply Z.eqb_neq in Ebf. rewrite (df_symend _ D1) in Ebf. rewrite Elbs7, N7. clear - Ebf Hsn1 Hn1. lia. }
      split.
      + split; [split; [split; [exact D7 | exact (X7 Hn7)] | exact V7]|]. split; [exact HK7|]. split; [exact Hp7|].
        split; [exact Hm7|]. split; [exact Hst7|]. exact Ho7.
      + rewrite <- Emeas. clear - Hmeas7 Hadv. lia.
  Qed.

  Lemma slit_outcome : forall s s1 s5 (b : bool),
    STI s1 -> lz_meas s1 = lz_meas s -> 1 <= ds_lookahead s1 ->
    dwf s5 -> SV c0 s5 -> DXX s5 -> fb_entry s5 0 -> KV s5 = KV s0 -> OUTLE s0 s5 -> ds_status s5 <> FINISH_STATE -> dmode s5 = 4 ->
    ds_strm s5 = ds_strm s1 -> ds_strstart s5 = ds_strstart s1 -> ds_lookahead s5 = ds_lookahead s1 ->
    SEND s1 (set_lookahead (set_strstart s5 (ds_strstart s5 + 1)) (ds_lookahead s5 - 1)) 1 1 ->
    ds_match_available s5 = 1 -> 2 <= ds_match_length s5 <= 258 ->
    (MIN_MATCH <= ds_match_length s5 -> ds_match_length s5 <= ds_lookahead s5 /\ 2 <= wrap32 (ds_strstart s5 + 1 - ds_match_start s5) <= ds_w_size s5 - MIN_LOOKAHEAD + 1) ->
    ds_strstart s5 + 1 - ds_block_start s5 <= 258 * nsym s5 + 1 ->
    nsym s5 = nsym s1 + 1 -> ds_lit_bufsize s5 = ds_lit_bufsize s1 ->
    b = (ds_sym_next s1 + 3 =? ds_sym_end s1) ->
    let s6 := if b then flush_block_only s5 0 else s5 in
    let s7 := set_lookahead (set_strstart s6 (ds_strstart s6 + 1)) (ds_lookahead s6 - 1) in
    (b = true -> flush_ok s5 0)
    /\ (0 <= ds_strstart s6 /\ 1 <= ds_lookahead s6 /\ ds_strstart s6 + ds_lookahead s6 <= 2 * ds_w_size s0)
    /\ match (if cs_avail_out (ds_strm s7) =? 0 then LRet need_more else LCont) with
       | LCont => STI s7 /\ lz_meas s7 < lz_meas s
       | LBreak => STI s7 /\ ds_lookahead s7 = 0
       | LRet bs => SRET s7 bs
       end.
  Proof.
    intros s s1 s5 b HF1 Emeas Hl1 D5 V5 XX5 FE5 HK5 Ho5 Hst5 Hm5 Estrm5 Estr5 Elook5 SE Hma5 Hml5 H35 Hext5 N5 Elbs5 Eb s6 s7.
    pose proof HF1 as (_ & HK1 & _). pose proof (KV_fields _ _ HK1) as (Ews1 & _). pose proof (KV_fields _ _ HK5) as (Ews5 & _).
    pose proof (STI_facts s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hma1 & Hml1 & Hpl1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & _).
    subst s7 s6. destruct b.
    -
      pose proof (flush_block_only_factsW c0 s5 0 HFB HC0w D5 V5 XX5 FE5 Hst5 ltac:(rewrite Hm5; lia)) as FB. cbv zeta in FB.
      destruct FB as (FO & DCW6 & HK6 & Ho6 & EPF6 & Estr6 & Elook6 & Ebs6 & Eml6 & _ & Esn6 & Hpa6 & Eain6 & _).
      pose proof (PF_fields _ _ EPF6) as (_ & (_ & _ & _ & Ema6 & _) & (Est6 & _) & (_ & _ & _ & _ & _ & _ & _ & Ems6 & EKV6)).
      pose proof (KV_fields _ _ EKV6) as (Ews6 & _).
      set (s6 := flush_block_only s5 0) in *. clearbody s6.
      pose proof (adv_fields s6 (ds_strstart s6 + 1) (ds_lookahead s6 - 1)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      split; [intros _; exact FO|].
      split; [rewrite Estr6, Elook6, Estr5, Elook5, <- Ews1; clear - Hstr1 Hl1 Hsl1; lia|].
      assert (DC7 : DC c0 (set_lookahead (set_strstart s6 (ds_strstart s6 + 1)) (ds_lookahead s6 - 1))).
      { apply (DCW_advance1 s6 DCW6); rewrite ?Est6, ?(dmode_PF _ _ EPF6), ?Elook6, ?Ema6, ?Eml6, ?Estr6, ?Ems6, ?Ews6, ?Ebs6; try assumption.
        - rewrite Elook5. exact Hl1.
        - unfold nsym. rewrite Esn6. cbn. clear. lia. }
      rewrite A1. destruct (Z.eqb_spec (cs_avail_out (ds_strm s6)) 0) as [Ea|Ea].
      + split; [exact DC7|]. split; [rewrite A5, HK6; exact HK5|]. split; [apply (OUTLE_trans _ s6); [exact (OUTLE_trans _ _ _ Ho5 Ho6) | apply OUTLE_strm; exact A1]|]. reflexivity.
      + split.
        * split; [exact DC7|]. split; [rewrite A5, HK6; exact HK5|]. split; [rewrite A4; destruct Hpa6 as [P0|A00]; [exact P0 | exfalso; exact (Ea A00)]|].
          split; [rewrite A7, (dmode_PF _ _ EPF6); exact Hm5|].
          split; [rewrite A8, Est6; exact Hst5|].
          apply (OUTLE_trans _ s6); [exact (OUTLE_trans _ _ _ Ho5 Ho6) | apply OUTLE_strm; exact A1].
        * unfold lz_meas. rewrite A2, A1, Eain6, Elook6, Estrm5, Elook5. unfold lz_meas in Emeas. rewrite <- Emeas. clear; lia.
    -
      pose proof (send_facts s1 _ 1 1 HF1 SE) as SF. cbv zeta in SF.
      destruct SF as (D7 & V7 & HK7 & Hp7 & Hm7 & Hst7 & Ho7 & Estrm7 & Hmeas7 & Hl7 & N7 & Ese7 & Elbs7 & X7 & FE7 & XX7 & B7).
      split; [intros HH; discriminate HH|].
      split; [rewrite Estr5, Elook5, <- Ews1; clear - Hstr1 Hl1 Hsl1; lia|].
      assert (Hn7 : nsym (set_lookahead (set_strstart s5 (ds_strstart s5 + 1)) (ds_lookahead s5 - 1)) <= ds_lit_bufsize s5 - 2).
      { symmetry in Eb. apply Z.eqb_neq in Eb. rewrite (df_symend _ D1) in Eb. change (nsym s5 <= ds_lit_bufsize s5 - 2). rewrite N5, Elbs5. clear - Eb Hsn1 Hn1. lia. }
      pose proof (adv_fields s5 (ds_strstart s5 + 1) (ds_lookahead s5 - 1)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      rewrite A1. destruct (Z.eqb_spec (cs_avail_out (ds_strm s5)) 0) as [Ea|Ea].
      + split; [split; [split; [exact D7 | apply X7; rewrite Elbs7, <- Elbs5; exact Hn7] | exact V7]|]. split; [exact HK7|]. split; [exact Ho7|]. reflexivity.
      + split.
        * split; [split; [split; [exact D7 | apply X7; rewrite Elbs7, <- Elbs5; exact Hn7] | exact V7]|]. split; [exact HK7|]. split; [exact Hp7|].
          split; [exact Hm7|]. split; [exact Hst7|]. exact Ho7.
        * rewrite <- Emeas. clear - Hmeas7. lia.
  Qed.

  Lemma strip_inv_STI : forall s, STI s -> strip_inv s.
  Proof.
    intros s HF. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (STI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & _).
    pose proof (cfg_ranges s D X ltac:(rewrite Hm; lia)) as (_ & _ & Glz & _).
    pose proof (df_hbits _ D) as Hb. pose proof (df_hshift _ D) as Hsh. pose proof (dx_insh _ X) as Hih. pose proof (dx_tfc _ X) as Xtfc.
    constructor; try assumption.
    - clear - Hih. lia.
    - exact (df_hmask _ D).
    - exact (df_wmask _ D).
    - rewrite Hsh. unfold MIN_MATCH. clear - Hb. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
    - clear - Hml. lia.
    - exact (df_ms _ D).
    - exact (dx_pm _ X).
    - clear - Hma. lia.
    - pose proof (df_strategy _ D) as Sy. unfold Z_FIXED in Sy. exact Sy.
    - clear - Glz. lia.
    - clear - Hsn Hn. lia.
    - rewrite Hse. clear - Sl. lia.
    - exact (df_wb _ D).
    - exact (df_hb _ D).
    - exact (df_pb _ D).
    - intros i _. apply (Xtfc DeflateState.TL i).
    - intros i _. apply (Xtfc DeflateState.TD i).
  Qed.

  Lemma strip_inv_lm : forall s1 s2 s4, STI s1 -> SHREL s1 s2 -> SMREL s1 s2 s4 -> strip_inv s4.
  Proof.
    intros s1 s2 s4 HF HR MR. pose proof (strip_inv_STI s1 HF) as TI.
    pose proof (STI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & _).
    destruct HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Epl2 & Epm2 & Ema2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    destruct MR as (T4 & Estr4 & Elook4 & Esn4 & Epb4 & Elfc4 & Edfc4 & Ehd4 & Epv4 & Eih4 & Epl4 & Epm4 & Ema4 & Hml4 & Hms4 & Hlz4).
    pose proof (TS_fields _ _ T4) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                        & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
    destruct TI; constructor; rewrite ?Estr4, ?Elook4, ?Esn4, ?Elz, ?Esy, ?Ews, ?Elbs, ?Ehs, ?Ewm, ?Ehm, ?Ehsh, ?Ewin, ?Ese, ?Elfc4, ?Edfc4, ?Ehd4, ?Epv4, ?Eih4, ?Epl4, ?Epm4, ?Ema4; try assumption.
    all: first [clear - Bih2; lia | unfold MAX_MATCH in Hml4; clear - Hml4; lia | exact Hms4 | clear - Hml; lia | exact (df_ms _ D) | clear - Hma; lia].
  Qed.

  Lemma soutcome : forall s s1 s2 s4,
    STI s1 -> lz_meas s1 = lz_meas s -> 1 <= ds_lookahead s1 -> ds_strstart s1 + MIN_LOOKAHEAD <= 2 * ds_w_size s1 ->
    SHREL s1 s2 -> SMREL s1 s2 s4 ->
    (strip_inv s4 /\ 1 <= ds_lookahead s4 <= 2 * ds_w_size s0
     /\ if dist_cond s4 then sdist_ok (ds_w_size s0) s4
        else if negb (ds_match_available s4 =? 0) then slit_ok (ds_w_size s0) s4 else True)
    /\ match snd (st_decide s4) with
       | LCont => STI (fst (st_decide s4)) /\ lz_meas (fst (st_decide s4)) < lz_meas s
       | LBreak => STI (fst (st_decide s4)) /\ ds_lookahead (fst (st_decide s4)) = 0
       | LRet bs => SRET (fst (st_decide s4)) bs
       end.
  Proof.
    intros s s1 s2 s4 HF1 Emeas Hl1 Hss HR MR.
    pose proof HF1 as (HDC1 & HK1 & Hp1 & Hm1 & Hst1 & Ho1). pose proof (KV_fields _ _ HK1) as (Ews1 & _).
    pose proof (STI_facts s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hma1 & Hml1 & Hpl1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & Hext1 & Hma11 & H31).
    pose proof MR as (T4 & Estr4 & Elook4 & Esn4 & Epb4 & Elfc4 & Edfc4 & Ehd4 & Epv4 & Eih4 & Epl4 & Epm4 & Ema4 & Hml4 & Hms4 & Hlz4).
    pose proof (TS_fields _ _ T4) as (_ & (_ & Ews4 & _) & (_ & _ & _ & Elbs4 & _) & _ & (_ & _ & _ & _ & _ & _ & Ewin4 & _ & Ese4) & _).
    pose proof (strip_inv_lm s1 s2 s4 HF1 HR MR) as TI4.
    unfold st_decide.
    destruct (dist_cond s4) eqn:Hdc.
    -
      pose proof (sdist_stage s1 s2 s4 HF1 Hl1 HR MR Hdc) as SD. cbv zeta in SD. destruct SD as (R & Ebf & Hml3 & Hmll & Hstr3 & HsD).
      pose proof (sdist_send s1 _ HF1 R Hml3 Hmll) as SE.
      pose proof (sdist_outcome s s1 (fst (st_sdist s4)) (snd (st_sdist s4)) _ HF1 Emeas SE Ebf) as (FOK & Hl7 & OUT).
      split; [| exact OUT].
      split; [exact TI4|]. split; [rewrite Elook4, <- Ews1; clear - Hl1 Hsl1 Hstr1; lia|].
      unfold sdist_ok. rewrite Epl4, Elook4, Estr4.
      split; [exact Hmll|]. split; [clear - Hstr3 Hmll Hml3; lia|]. split; [exact HsD|]. split; [exact Hl7 | exact FOK].
    - destruct (Z.eqb_spec (ds_match_available s4) 0) as [Hma0|Hma0]; cbn [negb].
      +
        pose proof (savail_send s1 s2 s4 HF1 Hl1 HR MR Hdc Hma0) as SE.
        pose proof (send_facts s1 _ 1 0 HF1 SE) as SF. cbv zeta in SF.
        destruct SF as (D7 & V7 & HK7 & Hp7 & Hm7 & Hst7 & Ho7 & Estrm7 & Hmeas7 & Hl7 & N7 & Ese7 & Elbs7 & X7 & FE7 & XX7 & B7).
        split; [split; [exact TI4 | split; [rewrite Elook4, <- Ews1; clear - Hl1 Hsl1 Hstr1; lia | exact I]]|].
        unfold st_avail in *. cbn [fst snd] in *.
        split.
        * split; [split; [split; [exact D7 | apply X7; rewrite Elbs7, N7; clear - Hn1; lia] | exact V7]|]. split; [exact HK7|]. split; [exact Hp7|].
          split; [exact Hm7|]. split; [exact Hst7|]. exact Ho7.
        * rewrite <- Emeas. clear - Hmeas7. lia.
      +
        assert (Hma4 : ds_match_available s4 = 1) by (rewrite Ema4 in Hma0 |- *; clear - Hma1 Hma0; lia).
        pose proof (smid_facts s1 s2 s4 HF1 Hl1 HR MR Hdc Hma4) as SM. cbv zeta in SM.
        pose proof (slit_tally_eq s4) as [Es5 Eb5].
        unfold st_slit.
        destruct (tr_tally_lit s4 (arr_get (ds_window s4) (ds_strstart s4 - 1))) as [s5 b]. cbn [fst snd] in SM, Es5, Eb5 |- *.
        destruct SM as (Ebf & D5 & V5 & XX5 & FE5 & HK5 & Ho5 & Hst5 & Hm5 & Estrm5 & Estr5 & Elook5 & Hstr11 & SE & Hma5 & Hml5 & H35 & Hext5 & N5 & Elbs5).
        pose proof (slit_outcome s s1 s5 b HF1 Emeas Hl1 D5 V5 XX5 FE5 HK5 Ho5 Hst5 Hm5 Estrm5 Estr5 Elook5 SE Hma5 Hml5 H35 Hext5 N5 Elbs5 Ebf) as SO.
        cbv zeta in SO. destruct SO as (FOK & Hs6 & OUT).
        split; [| exact OUT].
        split; [exact TI4|]. split; [rewrite Elook4, <- Ews1; clear - Hl1 Hsl1 Hstr1; lia|].
        unfold slit_ok. rewrite <- Es5, <- Eb5, Estr4.
        split; [exact Hstr11|]. split; [exact FOK | exact Hs6].
  Qed.

  Lemma sstep : forall s, STI s ->
    strip_ok (ds_w_size s0) (ds_hash_size s0) s flush
    /\ match snd (st_sbody s flush) with
       | LCont => STI (fst (st_sbody s flush)) /\ lz_meas (fst (st_sbody s flush)) < lz_meas s
       | LBreak => STI (fst (st_sbody s flush)) /\ ds_lookahead (fst (st_sbody s flush)) = 0
       | LRet bs => SRET (fst (st_sbody s flush)) bs
       end.
  Proof.
    intros s HF. unfold st_sbody.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (KV_fields _ _ HK) as (Ews0 & Ehs0 & Elbs0 & _).
    pose proof (sfill_stage s HF) as FS. cbv zeta in FS.
    destruct FS as (HF1 & Emeas & Hl0 & Hfw & Hl1r & Ews1 & Hnone & Hbrk & Hret & Hss1 & Hnc & _).
    set (s1 := fst (st_fill s flush)) in *.
    pose proof HF1 as (HDC1 & HK1 & Hp1 & Hm1 & Hst1 & Ho1).
    rewrite <- Ews0, <- Ehs0.
    destruct (snd (st_fill s flush)) as [o|] eqn:Eo.
    - split.
      { split; [exact Hl0|]. split; [exact Hfw|]. split; [exact Hl1r|]. intros HH; rewrite Eo in HH; discriminate HH. }
      cbn [fst snd]. destruct o as [| |bs].
      + exfalso. exact (Hnc eq_refl).
      + split; [exact HF1 | exact (Hbrk eq_refl)].
      + rewrite (Hret bs eq_refl). split; [exact HDC1|]. split; [exact HK1|]. split; [exact Ho1 | reflexivity].
    - pose proof (Hnone eq_refl) as Hl1.
      pose proof (shash_stage s1 HF1 Hl1) as HS. cbv zeta in HS. destruct HS as [HR Hlm].
      rewrite <- Ews1 in Hss1.
      pose proof (slm_stage s1 (fst (st_hash s1)) (snd (st_hash s1)) HF1 Hl1 Hss1 HR Hlm) as LM. cbv zeta in LM. destruct LM as [MR LMOK].
      pose proof (soutcome s s1 (fst (st_hash s1)) (st_lm (prev_st (fst (st_hash s1))) (snd (st_hash s1))) HF1 Emeas Hl1 Hss1 HR MR) as [DEC OUT].
      split; [| unfold st_srest; exact OUT].
      split; [exact Hl0|]. split; [exact Hfw|]. split; [exact Hl1r|]. intros _.
      change (strip_inv s1 /\ 1 <= ds_lookahead s1 <= 2 * ds_w_size s
              /\ (sl_lm_cond (prev_st (fst (st_hash s1))) (snd (st_hash s1)) = true -> lm_ok (prev_st (fst (st_hash s1))) (snd (st_hash s1)))
              /\ sdec_ok (ds_w_size s) (st_lm (prev_st (fst (st_hash s1))) (snd (st_hash s1)))).
      split; [exact (strip_inv_STI s1 HF1)|]. split; [split; [exact Hl1 | exact (proj2 Hl1r)]|].
      split; [exact LMOK|]. unfold sdec_ok. rewrite Ews0. exact DEC.
  Qed.

  Lemma sloop : forall fuel s, STI s -> lz_meas s < Z.of_nat fuel ->
    sloop_ok (ds_w_size s0) (ds_hash_size s0) fuel s flush
    /\ match snd (deflate_slow_loop fuel s flush) with
       | None => STI (fst (deflate_slow_loop fuel s flush)) /\ ds_lookahead (fst (deflate_slow_loop fuel s flush)) = 0
       | Some bs => SRET (fst (deflate_slow_loop fuel s flush)) bs
       end.
  Proof.
    induction fuel as [|f IH]; intros s HI Hmz.
    { exfalso. pose proof (STI_facts s HI) as (D & _ & V & _). pose proof (sv_ain _ _ V). pose proof (df_look _ D). unfold lz_meas in Hmz. cbn [Z.of_nat] in Hmz. lia. }
    rewrite sloop_ok_S, sloop_step'. destruct (sstep s HI) as [HT HC].
    destruct (snd (st_sbody s flush)) eqn:E.
    - destruct HC as [HI' Hm'].
      destruct (IH (fst (st_sbody s flush)) HI' ltac:(lia)) as [HL HF].
      split; [exact (conj HT HL) | exact HF].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
  Qed.

  Definition TAILOK (u : deflate_state) : Prop :=
    dwf u /\ SV c0 u /\ DXX u /\ BND u /\ KV u = KV s0 /\ OUTLE s0 u /\ ds_status u <> FINISH_STATE /\ dmode u = 4
    /\ ds_pending u = 0 /\ ds_lookahead u = 0 /\ ds_match_available u = 0 /\ 0 <= ds_sym_next u < 2 ^ 18 /\ 0 <= ds_strstart u
    /\ (forall last, 0 <= last <= 1 -> fb_entry u last)
    /\ (ds_sym_next u = 0 -> DX u)
    /\ strip_inv u.

  Lemma TAILOK_STI : forall u, STI u -> ds_lookahead u = 0 -> ds_match_available u = 0 -> TAILOK u.
  Proof.
    intros u HF Hl0 Hma0. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho). pose proof HDC as [[D X] V].
    pose proof (STI_facts u HF) as (_ & _ & _ & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & _).
    split; [exact D|]. split; [exact V|]. split; [exact (DX_DXX u X)|]. split; [exact (DX_BND u X)|]. split; [exact HK|]. split; [exact Ho|].
    split; [exact Hst|]. split; [exact Hm|]. split; [exact Hp|]. split; [exact Hl0|]. split; [exact Hma0|]. split; [clear - Hsn Hn Sl; lia|]. split; [exact Hstr|].
    split; [intros last Hlast; exact (DC_fb_entry c0 u last HC0w HDC Hp ltac:(rewrite Hm; lia) Hlast)|].
    split; [intros _; exact X | exact (strip_inv_STI u HF)].
  Qed.

  Lemma TAILOK_lit : forall u, STI u -> ds_lookahead u = 0 -> ds_match_available u = 1 ->
    TAILOK (set_match_available (fst (tr_tally_lit u (arr_get (ds_window u) (ds_strstart u - 1)))) 0).
  Proof.
    intros u HF Hl0 Hma1'. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho). pose proof HDC as [[D X] V].
    pose proof (STI_facts u HF) as (_ & _ & _ & Sw & Sh & Sl & Hma & Hml & Hpl & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext & Hma1 & H3).
    pose proof (TAILOK_STI u HF Hl0) as _.
    destruct (tally_lit_gen u (arr_get (ds_window u) (ds_strstart u - 1)) (df_bl _ D) (df_tl _ D) (DX_BQ u X) Hn ltac:(clear - Sl; lia) (df_bb _ D)
                (dx_tfc _ X DeflateState.TL) (dx_tfc _ X DeflateState.TD)) as [TY _]. cbv zeta in TY.
    destruct (tr_tally_lit u (arr_get (ds_window u) (ds_strstart u - 1))) as [s5 b]. cbn [fst snd] in TY |- *.
    destruct TY as (T5 & Estr5 & Elook5 & Eml5 & Ems5 & Ehd5 & Epv5 & Eih5 & Lpb5 & Bpb5 & Llt5 & Ldt5 & Blt5 & Bdt5 & BQ5 & N5 & Esn5).
    pose proof (TF_fields _ _ T5) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Epl & Ema & Epm & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                        & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
    set (t := set_match_available s5 0).
    assert (T : TS t = TS u) by (subst t; etransitivity; [| exact (TF_TS _ _ T5)]; reflexivity).
    assert (Et : ds_strstart t = ds_strstart u /\ ds_lookahead t = 0 /\ ds_match_length t = ds_match_length u /\ ds_match_start t = ds_match_start u
                 /\ ds_head t = ds_head u /\ ds_prev t = ds_prev u /\ ds_ins_h t = ds_ins_h u /\ ds_match_available t = 0 /\ ds_prev_length t = ds_prev_length u
                 /\ ds_prev_match t = ds_prev_match u /\ ds_sym_next t = ds_sym_next u + 3 /\ ds_pending_buf t = ds_pending_buf s5
                 /\ ds_dyn_ltree_fc t = ds_dyn_ltree_fc s5 /\ ds_dyn_dtree_fc t = ds_dyn_dtree_fc s5).
    { subst t. dsred. rewrite Estr5, Elook5, Eml5, Ems5, Ehd5, Epv5, Eih5, Epl, Epm, Esn5, Hl0. repeat split; reflexivity. }
    clearbody t. destruct Et as (Estr & Elook & Eml & Ems & Ehd & Epv & Eih & Emat & Eplt & Epmt & Esn & Epb & Elfc & Edfc).
    pose proof (TS_fields _ _ T) as ((_ & Elzt & _ & _ & Elvt & Esyt) & (Einst & Ewst & Emtt & _) & (Ebst & _ & Estt & Elbst & Eblt & Eldlt & Eddlt & Ebdlt)
                                       & (Edept & Eblct & Eolt & Eslt & Ehst & Ewmt & Ehmt & Ehsht) & (Estrmt & Epdt & Epot & Ebvt & _ & _ & Ewint & EKVt & Eset) & _).
    assert (Emt' : dmode t = 4) by (unfold dmode; rewrite Elvt, Esyt; exact Hm).
    assert (Dt : dwf t).
    { apply (dwf_TS_transfer u t D T); rewrite ?Estr, ?Elook, ?Ems, ?Eih, ?Ehd, ?Epv, ?Epb, ?Elfc, ?Edfc; try reflexivity; try assumption.
      all: first [clear; lia | exact (proj2 (df_ins _ D)) | exact (df_ms _ D) | pose proof (dx_insh _ X); lia | exact (df_hb _ D) | exact (df_pb _ D) | clear - Hstr Hlook Hsl; lia]. }
    assert (HCt : CHAIN t (ds_strstart u - 1) (ds_strstart u - 1)).
    { apply (CHAIN_same u); [exact Ehd | exact Epv | exact Ehst | exact Ewst | exact Ewmt |]. exact (dx_chain _ X ltac:(rewrite Hm; lia)). }
    assert (XXt : DXX t).
    { apply (DXX_TS_transfer u t X T Hm); rewrite ?Eih, ?Eml, ?Eplt, ?Emat, ?Epmt, ?Estr; try assumption.
      all: first [exact (dx_insh _ X) | unfold MAX_MATCH; clear - Hml; lia | unfold MAX_MATCH; clear - Hpl; lia | left; reflexivity | exact (dx_pm _ X)
                 | intros HH; discriminate HH | idtac].
      - pose proof (dx_tdl _ X) as Xtdl. intros tt i. destruct tt; cbn [tree_dl]; rewrite ?Eldlt, ?Eddlt, ?Ebdlt; [apply (Xtdl DeflateState.TL i) | apply (Xtdl DeflateState.TD i) | apply (Xtdl DeflateState.TB i)].
      - eapply CHAIN_mono; [| | exact HCt]; clear; lia. }
    assert (Vt : SV c0 t) by (apply (SV_strm c0 u); [exact Estrmt | exact V]).
    assert (Bt : BND t).
    { split; [intros _; rewrite Estr; exact HCt|]. intros _ Hm3. exfalso. rewrite Eml in Hm3. destruct (H3 Hm3) as (A & _). clear - A Hl0 Hm3. unfold MIN_MATCH in Hm3. lia. }
    pose proof (dx_tfc _ X) as Xtfc.
    assert (FEt : forall last, 0 <= last <= 1 -> fb_entry t last).
    { intros last Hlast. apply (fb_entry_intro c0 t last HC0w Dt Vt); rewrite ?Epdt, ?Epot, ?Ebvt, ?Eolt, ?Eslt, ?Edept, ?Eblct, ?Elvt, ?Estr, ?Ebst, ?Elbst; try assumption.
      - exact (dx_pout0 _ X Hp).
      - exact (dx_biv _ X).
      - apply (BQ_same s5); [exact Epb | rewrite Elbst, Elbs; reflexivity | rewrite Esn, Esn5; reflexivity | exact Elfc | exact Edfc | rewrite Eblt, Ebl; reflexivity | exact BQ5].
      - unfold nsym in *. rewrite Esn. rewrite Hsn. replace ((3 * (ds_sym_next u / 3) + 3) / 3) with (ds_sym_next u / 3 + 1) by (clear; Z.to_euclidean_division_equations; lia). clear - Hn Hsn. lia.
      - exact (dx_opt _ X).
      - exact (dx_stat _ X).
      - intros tt i. destruct tt; cbn [tree_fc]; rewrite ?Elfc, ?Edfc, ?Eblt; [apply Blt5 | apply Bdt5 | apply (Xtfc DeflateState.TB i)].
      - exact (xx_tdl _ XXt).
      - exact (dx_depth _ X).
      - exact (dx_blc _ X).
      - intros E0. unfold dmode in Hm. rewrite E0 in Hm. discriminate Hm.
      - unfold nsym in *. rewrite Esn, Hsn. replace ((3 * (ds_sym_next u / 3) + 3) / 3) with (ds_sym_next u / 3 + 1) by (clear; Z.to_euclidean_division_equations; lia).
        rewrite Hma1' in Hext. clear - Hext Hn. lia. }
    split; [exact Dt|]. split; [exact Vt|]. split; [exact XXt|]. split; [exact Bt|]. split; [rewrite EKVt; exact HK|].
    split; [apply (OUTLE_trans _ u); [exact Ho | apply OUTLE_strm; exact Estrmt]|]. split; [rewrite Estt; exact Hst|]. split; [exact Emt'|].
    split; [rewrite Epdt; exact Hp|]. split; [exact Elook|]. split; [exact Emat|]. split; [rewrite Esn; clear - Hsn Hn Sl; lia|]. split; [rewrite Estr; exact Hstr|].
    split; [exact FEt|]. split; [intros E0; exfalso; rewrite Esn in E0; clear - E0 Hsn Hn; lia|].
    pose proof (strip_inv_STI u HF) as TI.
    destruct TI; constructor; rewrite ?Estr, ?Elook, ?Eih, ?Ehmt, ?Ehsht, ?Ewmt, ?Eml, ?Ems, ?Eplt, ?Epmt, ?Emat, ?Esyt, ?Elzt, ?Esn, ?Elbst, ?Ehd, ?Epv, ?Ewst, ?Ehst, ?Elfc, ?Edfc, ?Ewint, ?Eset; try assumption.
    all: first [clear - Hsl Hl0; lia | clear; lia | clear - Hsn Hn Sl; lia | intros i _; apply Blt5 | intros i _; apply Bdt5].
  Qed.

  Lemma tail_insert_facts : forall t v, 0 <= v <= ds_strstart t -> v <= ds_w_size t ->
    dwf t -> DXX t -> BND t -> (forall last, 0 <= last <= 1 -> fb_entry t last) -> (ds_sym_next t = 0 -> DX t) ->
    let st := set_insert t v in
    dwf st /\ DXX st /\ BND st /\ (forall last, 0 <= last <= 1 -> fb_entry st last) /\ (ds_sym_next st = 0 -> DX st).
  Proof.
    intros t v Hv1 Hv2 D XX B FE XD st. subst st.
    split; [destruct D; constructor; try (dsred; assumption)|].
    split.
    { pose proof (xx_chain _ XX) as XC. assert (En : nsym (set_insert t v) = nsym t) by reflexivity. assert (Em : dmode (set_insert t v) = dmode t) by reflexivity.
      destruct XX; constructor; rewrite ?En, ?Em; try (dsred; assumption).
      all: intros Hm; dsred; apply (CHAIN_same t); try reflexivity; exact (XC Hm). }
    split.
    { destruct B as [BC BS]. split.
      - intros Hm. dsred. apply (CHAIN_same t); try reflexivity. exact (BC Hm).
      - unfold SLOW3 in *. exact BS. }
    split.
    { intros last Hlast. pose proof (FE last Hlast) as F.
      assert (En : nsym (set_insert t v) = nsym t) by reflexivity.
      destruct F; constructor; rewrite ?En; try (dsred; assumption). }
    intros Hsn. destruct (DD_set_insert t v D (XD Hsn) Hv1 Hv2) as [_ X']. exact X'.
  Qed.

  Lemma stail : forall u, TAILOK u ->
    let u2 := tail_st u in
    0 <= ds_strstart u <= 2 * ds_w_size s0 /\ 0 <= ds_sym_next u < 2 ^ 18
    /\ (flush = Z_FINISH -> flush_ok u2 1)
    /\ (flush <> Z_FINISH -> ds_sym_next u <> 0 -> flush_ok u2 0)
    /\ BFPOST c0 s0 flush (deflate_tail u2 flush).
  Proof.
    intros u (D & V & XX & B & HK & Ho & Hst & Hm & Hp & Hl0 & Hma0 & Hsn & Hstr & FE & XD & TI) u2.
    pose proof (KV_fields _ _ HK) as (Ews & _). pose proof (dwf_sizes u D) as (Sw & _). pose proof (df_sl _ D) as Hsl.
    assert (Hv : 0 <= (if ds_strstart u <? MIN_MATCH - 1 then ds_strstart u else MIN_MATCH - 1) <= ds_strstart u
                 /\ (if ds_strstart u <? MIN_MATCH - 1 then ds_strstart u else MIN_MATCH - 1) <= ds_w_size u).
    { destruct (Z.ltb_spec (ds_strstart u) (MIN_MATCH - 1)); unfold MIN_MATCH in *; lia. }
    destruct (tail_insert_facts u _ (proj1 Hv) (proj2 Hv) D XX B FE XD) as (Dst & XXst & Bst & FEst & XDst).
    change (set_insert u (if ds_strstart u <? MIN_MATCH - 1 then ds_strstart u else MIN_MATCH - 1)) with (tail_st u) in Dst, XXst, Bst, FEst, XDst.
    fold u2 in Dst, XXst, Bst, FEst, XDst.
    assert (Efs : forall A (g : deflate_state -> A), (forall x v, g (set_insert x v) = g x) -> g u2 = g u) by (intros A g Hg; subst u2; unfold tail_st; apply Hg).
    assert (Estrm : ds_strm u2 = ds_strm u) by (apply Efs; reflexivity).
    assert (Vst : SV c0 u2) by (apply (SV_strm c0 u u2 Estrm V)).
    assert (Hpst : ds_pending u2 = 0) by (rewrite (Efs _ ds_pending) by reflexivity; exact Hp).
    assert (Hmst : dmode u2 = 4) by (rewrite (Efs _ dmode) by reflexivity; exact Hm).
    assert (Hstst : ds_status u2 <> FINISH_STATE) by (rewrite (Efs _ ds_status) by reflexivity; exact Hst).
    assert (HKst : KV u2 = KV s0) by (rewrite (Efs _ KV) by reflexivity; exact HK).
    assert (Hlst : ds_lookahead u2 = 0) by (rewrite (Efs _ ds_lookahead) by reflexivity; exact Hl0).
    assert (Hmast : ds_match_available u2 = 0) by (rewrite (Efs _ ds_match_available) by reflexivity; exact Hma0).
    assert (Esn : ds_sym_next u2 = ds_sym_next u) by (apply Efs; reflexivity).
    assert (Host : OUTLE s0 u2) by (apply (OUTLE_trans _ u); [exact Ho | apply OUTLE_strm; exact Estrm]).
    assert (FB : forall last, 0 <= last <= 1 ->
      let s' := flush_block_only u2 last in
      flush_ok u2 last /\ DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ ds_lookahead s' = 0 /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
      /\ ds_match_available s' = 0).
    { intros last Hlast.
      pose proof (flush_block_only_facts c0 u2 last HFB HC0w Dst Vst XXst (FEst last Hlast) Hstst ltac:(rewrite Hmst; lia) Bst) as FB. cbv zeta in FB.
      destruct FB as (FO & DC' & HK' & Ho' & EPF & _ & Elook' & _ & _ & _ & _ & Hpa & _).
      pose proof (PF_fields _ _ EPF) as (_ & (_ & _ & _ & Ema' & _) & _).
      cbv zeta. split; [exact FO|]. split; [exact DC'|]. split; [rewrite HK'; exact HKst|]. split; [exact (OUTLE_trans _ _ _ Host Ho')|].
      split; [rewrite Elook'; exact Hlst|]. split; [exact Hpa | rewrite Ema'; exact Hmast]. }
    split; [rewrite <- Ews; clear - Hstr Hsl Hl0; lia|]. split; [exact Hsn|].
    split; [intros _; exact (proj1 (FB 1 ltac:(lia)))|]. split; [intros _ _; exact (proj1 (FB 0 ltac:(lia)))|].
    unfold deflate_tail. destruct (Z.eqb_spec flush Z_FINISH) as [F4|F4].
    - rewrite flush_block_eq'. destruct (FB 1 ltac:(lia)) as (_ & DC' & HK' & Ho' & Hl' & Hpa & Hma').
      set (s' := flush_block_only u2 1) in *. clearbody s'.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [negb Z.eqb]; unfold BFPOST; cbn [fst snd].
      + split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
        split; [intros _; exact Hl'|]. intros HH; discriminate HH.
      + split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
        split; [intros _; exact Hl'|]. intros _. destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)].
    - destruct (Z.eqb_spec (ds_sym_next u2) 0) as [N0|N0]; cbn [negb].
      + unfold BFPOST; cbn [fst snd].
        assert (DCst : DC c0 u2) by (exact (conj (conj Dst (XDst N0)) Vst)).
        split; [exact DCst|]. split; [exact HKst|]. split; [exact Host|]. split; [intros _; split; [exact Hpst | split; [exact F4 | exact Hmast]]|].
        split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
      + rewrite flush_block_eq'. destruct (FB 0 ltac:(lia)) as (_ & DC' & HK' & Ho' & Hl' & Hpa & Hma').
        set (s' := flush_block_only u2 0) in *. clearbody s'.
        destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [negb Z.eqb]; unfold BFPOST; cbn [fst snd].
        * split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
          split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
        * split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|].
          split; [intros _; split; [destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)] | split; [exact F4 | exact Hma']]|].
          split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
  Qed.

End Slow.


Theorem slow_bf_spec : FB_CALL -> BF_SPEC 4 slow_safe deflate_slow.
Proof.
  intros HFB c0 s flush (HC0 & HDC & Hp & Hst & Hfl) Hm.
  assert (HF : STI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact Hm|]. split; [exact Hst | apply OUTLE_refl]. }
  pose proof HDC as [[D X] V].
  assert (Hmz : 0 <= lz_meas s) by (unfold lz_meas; pose proof (df_look _ D); pose proof (sv_ain _ _ V); lia).
  destruct (sloop c0 s flush HC0 HFB (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as [HL HR].
  assert (Hao : 0 <= cs_avail_out (ds_strm s) < 2 ^ 32) by (exact (SV_aout c0 s (c0'_ok _ HC0) V)).
  assert (TL : snd (deflate_slow_loop (lz_fuel s) s flush) = None ->
    let s1 := fst (deflate_slow_loop (lz_fuel s) s flush) in
    let u := if negb (ds_match_available s1 =? 0) then break1_st s1 else s1 in
    stail_ok (ds_w_size s) s1 flush /\ BFPOST c0 s flush (deflate_tail (tail_st u) flush)).
  { intros Hnone s1 u. rewrite Hnone in HR. fold s1 in HR. destruct HR as [HF1 Hl1].
    pose proof (STI_facts c0 s s1 HF1) as (D1 & X1 & V1 & _ & _ & _ & Hma1 & _ & _ & _ & _ & _ & Hstr1 & _ & _ & _ & Hma11 & _).
    pose proof HF1 as (_ & HK1 & _). pose proof (KV_fields _ _ HK1) as (Ews1 & _).
    assert (TU : TAILOK c0 s u).
    { subst u. destruct (Z.eqb_spec (ds_match_available s1) 0) as [M0|M0]; cbn [negb].
      - exact (TAILOK_STI c0 s HC0 s1 HF1 Hl1 M0).
      - unfold break1_st. destruct (slit_tally_eq s1) as [E1 _]. rewrite <- E1.
        apply (TAILOK_lit c0 s HC0 s1 HF1 Hl1). clear - Hma1 M0. lia. }
    pose proof (stail c0 s flush HC0 HFB u TU) as ST. cbv zeta in ST. destruct ST as (R1 & R2 & F1 & F0 & POST).
    split; [| exact POST].
    unfold stail_ok. fold u.
    split; [exact (strip_inv_STI c0 s s1 HF1)|].
    split; [rewrite <- Ews1; pose proof (df_sl _ D1); clear - Hstr1 Hl1 H; lia|].
    split; [intros Hma; apply Hma11; clear - Hma Hma1; lia|].
    assert (Estru : ds_strstart u = ds_strstart s1).
    { subst u. destruct (negb (ds_match_available s1 =? 0)); [| reflexivity]. unfold break1_st. destruct (slit_tally_eq s1) as [E1 _]. rewrite <- E1.
      pose proof (tally_lit_facts s1 (arr_get (ds_window s1) (ds_strstart s1 - 1))) as (TK & _). destruct TK as (_ & _ & _ & _ & _ & Es & _). rewrite strstart_set_ma. exact Es. }
    split; [rewrite Estru, <- Ews1; pose proof (df_sl _ D1); clear - Hstr1 Hl1 H; lia|].
    split; [exact R2|]. split; [exact F1 | exact F0]. }
  split.
  - unfold slow_safe. split; [exact (dwf_DWF s D Hao)|]. split; [exact HL|].
    destruct (snd (deflate_slow_loop (lz_fuel s) s flush)); [exact I|]. exact (proj1 (TL eq_refl)).
  - rewrite deflate_slow_eq.
    destruct (snd (deflate_slow_loop (lz_fuel s) s flush)) as [bs|] eqn:E.
    + destruct HR as (DC' & HK' & Ho' & ->). unfold BFPOST; cbn [fst snd].
      split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
      split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
    + exact (proj2 (TL eq_refl)).
Qed.
