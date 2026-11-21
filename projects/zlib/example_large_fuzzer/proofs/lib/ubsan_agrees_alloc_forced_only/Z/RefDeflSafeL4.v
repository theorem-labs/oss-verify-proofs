(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeW.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeLM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeLW.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rle_cmpk_range : forall k w prev scan,
  let r := rle_cmpk k w prev scan in
  scan <= fst r <= scan + Z.of_nat k /\ (snd r = true -> fst r = scan + Z.of_nat k).
Proof.
  induction k as [|k IH]; intros w prev scan r; subst r.
  - cbn [rle_cmpk fst snd]. lia.
  - cbn [rle_cmpk]. destruct (prev =? arr_get w (scan + 1)).
    + specialize (IH w prev (scan + 1)). cbv zeta in IH. destruct (rle_cmpk k w prev (scan + 1)) as [sc ok]. cbn [fst snd] in *.
      rewrite Nat2Z.inj_succ. split; [lia|]. intros Hok. rewrite (proj2 IH Hok). lia.
    + cbn [fst snd]. rewrite Nat2Z.inj_succ. split; [lia|]. intros HH; discriminate HH.
Qed.

Lemma rle_cmp_loop_range : forall f w prev scan strend,
  scan < strend -> (exists q, strend - scan = 8 * q) ->
  scan <= rle_cmp_loop f w prev scan strend <= strend.
Proof.
  induction f as [|f IH]; intros w prev scan strend Hlt [q Hq].
  - cbn [rle_cmp_loop]. lia.
  - cbn [rle_cmp_loop]. pose proof (rle_cmpk_range 8 w prev scan) as R. cbv zeta in R.
    destruct (rle_cmpk 8 w prev scan) as [sc ok]. cbn [fst snd] in R. destruct R as [R1 R2]. change (Z.of_nat 8) with 8 in R1, R2.
    destruct ok; cbn [andb].
    + specialize (R2 eq_refl). destruct (Z.ltb_spec sc strend) as [L|L].
      * pose proof (IH w prev sc strend L ltac:(exists (q - 1); lia)). lia.
      * lia.
    + lia.
Qed.

(* [comment removed for export] *)
Lemma rl_run_facts : forall s, 0 <= ds_lookahead s ->
  exists v, rl_run s = set_match_length s v /\ 0 <= v <= ds_lookahead s /\ v <= MAX_MATCH.
Proof.
  intros s Hl. unfold rl_run.
  change (ds_lookahead (set_match_length s 0)) with (ds_lookahead s).
  change (ds_strstart (set_match_length s 0)) with (ds_strstart s).
  change (ds_window (set_match_length s 0)) with (ds_window s).
  destruct ((MIN_MATCH <=? ds_lookahead s) && (0 <? ds_strstart s)) eqn:C.
  - pose proof (rle_cmpk_range 3 (ds_window s) (arr_get (ds_window s) (ds_strstart s - 1)) (ds_strstart s - 1)) as R. cbv zeta in R.
    destruct (rle_cmpk 3 _ _ _) as [sc ok]. cbn [fst snd] in R. destruct R as [R1 R2]. change (Z.of_nat 3) with 3 in R1, R2.
    destruct ok.
    + specialize (R2 eq_refl).
      pose proof (rle_cmp_loop_range 33 (ds_window s) (arr_get (ds_window s) (ds_strstart s - 1)) sc (ds_strstart s + MAX_MATCH)
                    ltac:(unfold MAX_MATCH; lia) ltac:(exists 32; unfold MAX_MATCH; lia)) as L.
      set (sc' := rle_cmp_loop 33 _ _ _ _) in *. clearbody sc'.
      cbv zeta. change (ds_lookahead (set_match_length (set_match_length s 0) ?v)) with (ds_lookahead s).
      change (ds_match_length (set_match_length (set_match_length s 0) ?v)) with v.
      destruct (Z.ltb_spec (ds_lookahead s) (MAX_MATCH - (ds_strstart s + MAX_MATCH - sc'))).
      * exists (ds_lookahead s). split; [destruct s; reflexivity|]. unfold MAX_MATCH in *. lia.
      * exists (MAX_MATCH - (ds_strstart s + MAX_MATCH - sc')). split; [destruct s; reflexivity|]. unfold MAX_MATCH in *. lia.
    + exists 0. split; [reflexivity|]. unfold MAX_MATCH. lia.
  - exists 0. split; [reflexivity|]. unfold MAX_MATCH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Rle.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis HFB : FB_CALL.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Definition RTI (s : deflate_state) : Prop :=
    DC c0 s /\ KV s = KV s0 /\ ds_pending s = 0 /\ dmode s = 2 /\ ds_status s <> FINISH_STATE /\ OUTLE s0 s.

  Lemma RTI_facts : forall s, RTI s ->
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

  (* [comment removed for export] *)
  Lemma rfill_stage : forall s, RTI s ->
    let r := rl_fill s flush in
    RTI (fst r) /\ lz_meas (fst r) = lz_meas s
    /\ (ds_lookahead s <= MAX_MATCH -> fw_wf (ds_w_size s) (ds_hash_size s) s /\ DOK (fill_window s) /\ lz_keeps s (fill_window s))
    /\ ds_w_size (fst r) = ds_w_size s
    /\ (snd r = None -> 1 <= ds_lookahead (fst r))
    /\ (snd r = Some LBreak -> ds_lookahead (fst r) = 0)
    /\ (forall bs, snd r = Some (LRet bs) -> bs = need_more)
    /\ snd r <> Some LCont
    /\ ds_strstart (fst r) + MAX_MATCH < 2 * ds_w_size s.
  Proof.
    intros s HF r. subst r. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (RTI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    assert (Hwr : 0 <= ds_wrap s) by (pose proof (dx_wrapneg _ X); pose proof (df_wrap _ D); destruct (Z_lt_le_dec (ds_wrap s) 0); [exfalso; apply Hst; auto | lia]).
    assert (HW : fw_wf (ds_w_size s) (ds_hash_size s) s).
    { apply (dwf_fw_wf s D Hwr (sv_nin _ _ V) (sv_ain _ _ V) ltac:(rewrite (sv_input _ _ V); pose proof (sv_inlen _ _ V); lia)
             (sv_tin _ _ V) (sv_adler _ _ V) (sv_ib _ _ V)). }
    unfold rl_fill.
    destruct (Z.leb_spec (ds_lookahead s) MAX_MATCH) as [Hl0|Hl0].
    - destruct (DC_fill_window c0 s HC0w HDC ltac:(rewrite Hm; lia) Hst ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia))
        as (HDC' & HK' & Ho' & R' & Eext & HL' & HX' & HW' & SS').
      pose proof (fw_rest_fields _ _ R') as ((Est & _ & _ & _ & Epd & _) & (_ & _ & Elv & Esy & _) & _).
      pose proof (fill_window_keep s) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ksum).
      assert (HF' : RTI (fill_window s)).
      { split; [exact HDC'|]. split; [rewrite HK'; exact HK|]. split; [rewrite Epd; exact Hp|].
        split; [unfold dmode; rewrite Elv, Esy; exact Hm|]. split; [rewrite Est; exact Hst | exact (OUTLE_trans _ _ _ Ho Ho')]. }
      pose proof (wf_ws _ _ _ HW') as Ews'.
      assert (HFW : ds_lookahead s <= MAX_MATCH -> fw_wf (ds_w_size s) (ds_hash_size s) s /\ DOK (fill_window s) /\ lz_keeps s (fill_window s)).
      { intros _. split; [exact HW|]. split; [exact (DC_DOK c0 _ HC0w HDC')|].
        pose proof HDC as [[_ _] V0]. pose proof HDC' as [[D' _] V'].
        exact (lz_keeps_intro c0 s (fill_window s) D D' V0 V' HK' Ho'). }
      assert (SS : ds_strstart (fill_window s) + MAX_MATCH < 2 * ds_w_size s) by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; clear - SS'; lia).
      destruct ((ds_lookahead (fill_window s) <=? MAX_MATCH) && (flush =? Z_NO_FLUSH)) eqn:E1.
      + cbn [fst snd]. split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [exact HFW|]. split; [exact Ews'|].
        split; [intros HH; discriminate HH|]. split; [intros HH; discriminate HH|].
        split; [intros bs Hbs; injection Hbs as <-; reflexivity|]. split; [intros HH; discriminate HH | exact SS].
      + destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [E0|E0]; cbn [fst snd].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [exact HFW|]. split; [exact Ews'|].
          split; [intros HH; discriminate HH|]. split; [intros _; exact E0|].
          split; [intros bs Hbs; discriminate Hbs|]. split; [intros HH; discriminate HH | exact SS].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [exact HFW|]. split; [exact Ews'|].
          split; [intros _; lia|]. split; [intros HH; discriminate HH|].
          split; [intros bs Hbs; discriminate Hbs|]. split; [intros HH; discriminate HH | exact SS].
    - cbn [fst snd]. split; [exact HF|]. split; [reflexivity|]. split; [intros HH; exfalso; lia|]. split; [reflexivity|].
      split; [intros _; unfold MAX_MATCH in Hl0; lia|]. split; [intros HH; discriminate HH|].
      split; [intros bs Hbs; discriminate Hbs|]. split; [intros HH; discriminate HH | clear - Hl0 Hsl; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rtally_lit : forall s1 v, RTI s1 ->
    let s3 := set_match_length s1 v in
    let r := tr_tally_lit s3 (arr_get (ds_window s3) (ds_strstart s3)) in
    TALLYF s3 (fst r) /\ snd r = (ds_sym_next s1 + 3 =? ds_sym_end s1).
  Proof.
    intros s1 v HF s3 r. subst r.
    pose proof (RTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
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

  Lemma rtally_dist : forall s1 v, RTI s1 ->
    let s3 := set_match_length s1 v in
    let r := tr_tally_dist s3 1 (v - MIN_MATCH) in
    TALLYF s3 (fst r) /\ snd r = (ds_sym_next s1 + 3 =? ds_sym_end s1).
  Proof.
    intros s1 v HF s3 r. subst r.
    pose proof (RTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    set (len := v - MIN_MATCH).
    pose proof (tally_dist_facts s3 1 len) as (TK & Esn & Ebf & Ebt & Rl & Rd & Rp). cbv zeta in *.
    assert (BQ3 : BQ s3) by (apply (BQ_same s1); try reflexivity; exact (DX_BQ s1 X)).
    assert (N3 : nsym s3 = nsym s1) by reflexivity.
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL. destruct TL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    destruct (BQ_tally_dist s3 BQ3 ltac:(change (ds_lit_bufsize s1 + ds_sym_next s1 + 3 <= arr_len (ds_pending_buf s1)); rewrite (df_bl _ D); lia)
                ltac:(change (0 <= ds_lit_bufsize s1); lia) ltac:(rewrite N3; lia) ltac:(change (L_CODES <= arr_len (ds_dyn_ltree_fc s1)); rewrite L1; unfold L_CODES; lia)
                ltac:(change (D_CODES <= arr_len (ds_dyn_dtree_fc s1)); rewrite L3; unfold D_CODES; lia)
                1 len ltac:(lia)) as (BQ4 & N4 & _).
    cbv zeta in BQ4, N4.
    pose proof (tally_dist_fields s3 1 len) as (_ & _ & _ & Elt & Edt & _). cbv zeta in Elt, Edt.
    split; [| rewrite Ebf; reflexivity].
    eapply tally_common.
    - change (forall j, 0 <= j < ds_lit_bufsize s1 * 4 -> 0 <= arr_get (ds_pending_buf s1) j < 256). exact (df_bb _ D).
    - change (forall i, 0 <= arr_get (ds_dyn_ltree_fc s1) i < 65536). exact (dx_tfc _ X DeflateState.TL).
    - change (forall i, 0 <= arr_get (ds_dyn_dtree_fc s1) i < 65536). exact (dx_tfc _ X DeflateState.TD).
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
    - exact BQ4.
    - exact N4.
  Qed.

  (* [comment removed for export] *)
  Definition RTREL (s1 s7 : deflate_state) (adv : Z) : Prop :=
    TF s7 = TF s1 /\ ds_strstart s7 = ds_strstart s1 + adv /\ ds_lookahead s7 = ds_lookahead s1 - adv
    /\ 0 <= ds_match_length s7 < MIN_MATCH /\ ds_match_start s7 = ds_match_start s1
    /\ ds_head s7 = ds_head s1 /\ ds_prev s7 = ds_prev s1 /\ ds_ins_h s7 = ds_ins_h s1
    /\ arr_len (ds_pending_buf s7) = arr_len (ds_pending_buf s1)
    /\ (forall i, 0 <= i < ds_lit_bufsize s1 * 4 -> 0 <= arr_get (ds_pending_buf s7) i < 256)
    /\ arr_len (ds_dyn_ltree_fc s7) = arr_len (ds_dyn_ltree_fc s1) /\ arr_len (ds_dyn_dtree_fc s7) = arr_len (ds_dyn_dtree_fc s1)
    /\ (forall i, 0 <= arr_get (ds_dyn_ltree_fc s7) i < 65536) /\ (forall i, 0 <= arr_get (ds_dyn_dtree_fc s7) i < 65536)
    /\ BQ s7 /\ nsym s7 = nsym s1 + 1 /\ ds_sym_next s7 = ds_sym_next s1 + 3.

  Lemma rtally_stage : forall s1, RTI s1 -> 1 <= ds_lookahead s1 ->
    let r := rl_tally (rl_run s1) in
    (exists adv, RTREL s1 (fst r) adv /\ 1 <= adv <= ds_lookahead s1 /\ adv <= 258)
    /\ snd r = (ds_sym_next s1 + 3 =? ds_sym_end s1)
    /\ 0 <= ds_match_length (rl_run s1) <= ds_lookahead s1 /\ ds_match_length (rl_run s1) <= MAX_MATCH
    /\ (exists v, rl_run s1 = set_match_length s1 v).
  Proof.
    intros s1 HF Hl1 r. subst r.
    pose proof (RTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    destruct (rl_run_facts s1 ltac:(lia)) as (v & Erun & Hv & Hv2). rewrite Erun.
    split; [| split; [| split; [dsred; exact Hv | split; [dsred; exact Hv2 | exists v; reflexivity]]]].
    all: unfold rl_tally; change (ds_match_length (set_match_length s1 v)) with v.
    all: destruct (Z.leb_spec MIN_MATCH v) as [H3|H3].
    - (* [comment removed for export] *)
      destruct (rtally_dist s1 v HF) as [TY Ebf]. cbv zeta in TY, Ebf.
      destruct (tr_tally_dist (set_match_length s1 v) 1 (v - MIN_MATCH)) as [s4 bf]. cbn [fst snd] in TY, Ebf |- *.
      destruct TY as (T4 & Estr4 & Elook4 & Eml4 & Ems4 & Ehd4 & Epv4 & Eih4 & Lpb4 & Bpb4 & Llt4 & Ldt4 & Blt4 & Bdt4 & BQ4 & N4 & Esn4).
      change (ds_match_length (set_match_length s1 v)) with v in Eml4.
      exists v. split; [| unfold MAX_MATCH, MIN_MATCH in Hv2, H3; lia].
      unfold RTREL. dsred. rewrite Estr4, Elook4, Eml4, Ems4, Ehd4, Epv4, Eih4. dsred.
      split; [etransitivity; [| exact T4]; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [unfold MIN_MATCH; lia|]. repeat (split; [reflexivity|]).
      split; [exact Lpb4|]. split; [exact Bpb4|]. split; [exact Llt4|]. split; [exact Ldt4|]. split; [exact Blt4|]. split; [exact Bdt4|].
      split; [apply (BQ_same s4); dsred; try reflexivity; exact BQ4|].
      split; [unfold nsym in *; dsred; exact N4 | exact Esn4].
    - (* [comment removed for export] *)
      destruct (rtally_lit s1 v HF) as [TY Ebf]. cbv zeta in TY, Ebf.
      destruct (tr_tally_lit (set_match_length s1 v) _) as [s4 bf]. cbn [fst snd] in TY, Ebf |- *.
      destruct TY as (T4 & Estr4 & Elook4 & Eml4 & Ems4 & Ehd4 & Epv4 & Eih4 & Lpb4 & Bpb4 & Llt4 & Ldt4 & Blt4 & Bdt4 & BQ4 & N4 & Esn4).
      change (ds_match_length (set_match_length s1 v)) with v in Eml4.
      exists 1. split; [| lia].
      unfold RTREL. dsred. rewrite Estr4, Elook4, Eml4, Ems4, Ehd4, Epv4, Eih4. dsred.
      split; [etransitivity; [| exact T4]; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. repeat (split; [reflexivity|]).
      split; [exact Lpb4|]. split; [exact Bpb4|]. split; [exact Llt4|]. split; [exact Ldt4|]. split; [exact Blt4|]. split; [exact Bdt4|].
      split; [apply (BQ_same s4); dsred; try reflexivity; exact BQ4|].
      split; [unfold nsym in *; dsred; exact N4 | exact Esn4].
    - destruct (rtally_dist s1 v HF) as [_ Ebf]. cbv zeta in Ebf.
      destruct (tr_tally_dist (set_match_length s1 v) 1 (v - MIN_MATCH)) as [s4 bf]. cbn [fst snd] in Ebf |- *. exact Ebf.
    - destruct (rtally_lit s1 v HF) as [_ Ebf]. cbv zeta in Ebf.
      destruct (tr_tally_lit (set_match_length s1 v) _) as [s4 bf]. cbn [fst snd] in Ebf |- *. exact Ebf.
  Qed.

  (* [comment removed for export] *)
  Lemma rtrip_end : forall s1 s7 adv, RTI s1 -> 1 <= ds_lookahead s1 -> RTREL s1 s7 adv -> 1 <= adv <= ds_lookahead s1 -> adv <= 258 ->
    dwf s7 /\ SV c0 s7 /\ KV s7 = KV s0 /\ ds_pending s7 = 0 /\ dmode s7 = 2 /\ ds_status s7 <> FINISH_STATE /\ OUTLE s0 s7
    /\ ds_strm s7 = ds_strm s1 /\ lz_meas s7 < lz_meas s1 /\ 0 <= ds_lookahead s7 <= 2 * ds_w_size s1
    /\ nsym s7 = nsym s1 + 1 /\ ds_sym_next s7 = ds_sym_next s1 + 3 /\ ds_sym_end s7 = ds_sym_end s1 /\ ds_lit_bufsize s7 = ds_lit_bufsize s1
    /\ (nsym s7 <= ds_lit_bufsize s7 - 2 -> DX s7)
    /\ fb_entry s7 0
    /\ DXX s7 /\ BND s7.
  Proof.
    intros s1 s7 adv HF Hl1 TR Hadv Hadv2.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (RTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    destruct TR as (T7 & Estr7 & Elook7 & Hml7 & Ems7 & Ehd7 & Epv7 & Eih7 & Lpb7 & Bpb7 & Llt7 & Ldt7 & Blt7 & Bdt7 & BQ7 & N7 & Esn7).
    pose proof (TF_fields _ _ T7) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Epl & Ema & Epm & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                        & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
    assert (Em7 : dmode s7 = 2) by (unfold dmode; rewrite Elv, Esy; exact Hm).
    pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl. pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc.
    assert (Htfc7 : forall t i, 0 <= arr_get (tree_fc s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_fc]; [apply Blt7 | apply Bdt7 | rewrite Ebl; apply (Xtfc DeflateState.TB i)]. }
    assert (Htdl7 : forall t i, 0 <= arr_get (tree_dl s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_dl]; rewrite ?Eldl, ?Eddl, ?Ebdl; [apply (Xtdl DeflateState.TL i) | apply (Xtdl DeflateState.TD i) | apply (Xtdl DeflateState.TB i)]. }
    assert (HC7 : CHAIN s7 (ds_strstart s7 - 1) (ds_strstart s7 - 1)).
    { apply (CHAIN_same s1); [exact Ehd7 | exact Epv7 | exact Ehs | exact Ews | exact Ewm |].
      rewrite Estr7. eapply CHAIN_mono; [| | exact (dx_chain _ X ltac:(rewrite Hm; lia))]; clear - Hadv; lia. }
    assert (D7 : dwf s7).
    { apply (dwf_TF_transfer s1 s7 D T7); rewrite ?Estr7, ?Elook7, ?Ems7, ?Eih7, ?Ehd7, ?Epv7; try reflexivity; try assumption.
      - clear - Hstr Hadv. lia.
      - clear - Hadv. lia.
      - clear - Hsl. lia.
      - pose proof (df_ins _ D). clear - H Hadv. lia.
      - exact (df_ms _ D).
      - pose proof (dx_insh _ X). clear - H. lia.
      - exact (df_hb _ D).
      - exact (df_pb _ D). }
    assert (XX7 : DXX s7).
    { apply (DXX_TF_transfer s1 s7 X T7); rewrite ?Eih7, ?Hm; try assumption.
      - exact (dx_insh _ X).
      - unfold MAX_MATCH, MIN_MATCH in *. clear - Hml7. lia.
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
      - intros _. rewrite Estr7, Hma. clear - Hext Hn Hadv Hadv2. lia.
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
      - clear - Hext Hn Hadv Hadv2. lia.
      - clear. lia. }
    split; [exact D7|]. split; [exact V7|]. split; [rewrite EKV; exact HK|]. split; [rewrite Epd; exact Hp|]. split; [exact Em7|].
    split; [rewrite Est; exact Hst|]. split; [apply (OUTLE_trans _ s1); [exact Ho | apply OUTLE_strm; exact Estrm]|].
    split; [exact Estrm|]. split; [unfold lz_meas; rewrite Estrm, Elook7; clear - Hadv; lia|]. split; [rewrite Elook7; clear - Hadv Hlook Hsl Hstr; lia|].
    split; [exact N7|]. split; [exact Esn7|]. split; [exact Ese|]. split; [exact Elbs|]. split; [exact X7|]. split; [exact FE7|].
    split; [exact XX7 | exact (conj (fun _ => HC7) (SLOW3_mode s7 ltac:(rewrite Em7; lia)))].
  Qed.

  (* [comment removed for export] *)
  Definition RRET (s' : deflate_state) (bs : block_state) : Prop :=
    DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ bs = need_more.

  (* [comment removed for export] *)
  Lemma rflush : forall s last, dwf s -> SV c0 s -> DXX s -> fb_entry s last -> ds_status s <> FINISH_STATE -> dmode s = 2 -> BND s ->
    KV s = KV s0 -> OUTLE s0 s ->
    let s' := flush_block_only s last in
    fblk_ok fb_safe s last
    /\ DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ dmode s' = 2 /\ ds_status s' <> FINISH_STATE
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

  Lemma rle_outcome : forall s s1 s7 adv (bf : bool),
    RTI s1 -> lz_meas s1 = lz_meas s -> 1 <= ds_lookahead s1 -> RTREL s1 s7 adv -> 1 <= adv <= ds_lookahead s1 -> adv <= 258 ->
    bf = (ds_sym_next s1 + 3 =? ds_sym_end s1) ->
    (bf = true -> fblk_ok fb_safe s7 0)
    /\ match snd (st_bflush0 s7 bf) with
       | LCont => RTI (fst (st_bflush0 s7 bf)) /\ lz_meas (fst (st_bflush0 s7 bf)) < lz_meas s
       | LBreak => RTI (fst (st_bflush0 s7 bf)) /\ ds_lookahead (fst (st_bflush0 s7 bf)) = 0
       | LRet bs => RRET (fst (st_bflush0 s7 bf)) bs
       end.
  Proof.
    intros s s1 s7 adv bf HF1 Emeas Hl1 TR Hadv Hadv2 Ebf.
    pose proof (RTI_facts s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hma1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & Hext1).
    pose proof (rtrip_end s1 s7 adv HF1 Hl1 TR Hadv Hadv2) as TE.
    destruct TE as (D7 & V7 & HK7 & Hp7 & Hm7 & Hst7 & Ho7 & Estrm7 & Hmeas7 & Hl7 & N7 & Esn7 & Ese7 & Elbs7 & X7 & FE7 & XX7 & B7).
    split; [intros _; exact (proj1 (rflush s7 0 D7 V7 XX7 FE7 Hst7 Hm7 B7 HK7 Ho7))|].
    unfold st_bflush0. destruct bf.
    - rewrite flush_block_eq'.
      pose proof (rflush s7 0 D7 V7 XX7 FE7 Hst7 Hm7 B7 HK7 Ho7) as FB. cbv zeta in FB.
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

  Lemma rl_body_eq2 : forall s,
    rl_body s flush = match snd (rl_fill s flush) with
                      | Some o => (fst (rl_fill s flush), o)
                      | None => st_bflush0 (fst (rl_tally (rl_run (fst (rl_fill s flush))))) (snd (rl_tally (rl_run (fst (rl_fill s flush)))))
                      end.
  Proof.
    intros s. unfold rl_body. destruct (rl_fill s flush) as [s1 e]. cbn [fst snd]. destruct e; [reflexivity|]. destruct (rl_tally (rl_run s1)); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rle_step : forall s, RTI s ->
    rl_trip_ok fb_safe s flush
    /\ match snd (rl_body s flush) with
       | LCont => RTI (fst (rl_body s flush)) /\ lz_meas (fst (rl_body s flush)) < lz_meas s
       | LBreak => RTI (fst (rl_body s flush)) /\ ds_lookahead (fst (rl_body s flush)) = 0
       | LRet bs => RRET (fst (rl_body s flush)) bs
       end.
  Proof.
    intros s HF.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (rfill_stage s HF) as FS. cbv zeta in FS.
    destruct FS as (HF1 & Emeas & Hfw & Ews1 & Hnone & Hbrk & Hret & Hnc & Hss1).
    rewrite rl_body_eq2.
    set (s1 := fst (rl_fill s flush)) in *.
    pose proof HF1 as (HDC1 & HK1 & Hp1 & Hm1 & Hst1 & Ho1).
    pose proof (RTI_facts s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hma1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & Hext1).
    destruct (snd (rl_fill s flush)) as [o|] eqn:Eo.
    - split.
      { split; [exact (DC_DOK c0 s HC0w HDC)|]. split; [exact Hfw|]. intros HH; rewrite Eo in HH; discriminate HH. }
      cbn [fst snd]. destruct o as [| |bs].
      + exfalso. exact (Hnc eq_refl).
      + split; [exact HF1 | exact (Hbrk eq_refl)].
      + rewrite (Hret bs eq_refl). split; [exact HDC1|]. split; [exact HK1|]. split; [exact Ho1 | reflexivity].
    - pose proof (Hnone eq_refl) as Hl1.
      pose proof (rtally_stage s1 HF1 Hl1) as TS. cbv zeta in TS. destruct TS as ((adv & TR & Hadv & Hadv2) & Ebf & Hml2 & Hml2' & (v & Erun)).
      pose proof (rle_outcome s s1 (fst (rl_tally (rl_run s1))) adv (snd (rl_tally (rl_run s1))) HF1 Emeas Hl1 TR Hadv Hadv2 Ebf) as [FOK OUT].
      split; [| exact OUT].
      split; [exact (DC_DOK c0 s HC0w HDC)|]. split; [exact Hfw|]. intros _.
      change ((DOK s1 /\ 1 <= ds_lookahead s1 /\ ds_strstart s1 + ds_lookahead s1 <= 2 * ds_w_size s1
               /\ (MIN_MATCH <= ds_lookahead s1 -> 0 < ds_strstart s1 -> ds_strstart s1 + MAX_MATCH < 2 * ds_w_size s1)
               /\ (forall j, 0 <= j < 2 * ds_w_size s1 -> 0 <= arr_get (ds_window s1) j < 256))
              /\ (DOK (rl_run s1) /\ 1 <= ds_lookahead (rl_run s1) /\ ds_strstart (rl_run s1) + ds_lookahead (rl_run s1) <= 2 * ds_w_size (rl_run s1)
                  /\ 0 <= ds_match_length (rl_run s1) <= ds_lookahead (rl_run s1) /\ ds_match_length (rl_run s1) <= MAX_MATCH
                  /\ 0 <= ds_sym_next (rl_run s1) /\ ds_sym_next (rl_run s1) + 3 <= 3 * ds_lit_bufsize (rl_run s1) /\ 0 <= ds_sym_end (rl_run s1) < 2 ^ 32
                  /\ (forall j, 0 <= j < 2 * ds_w_size (rl_run s1) -> 0 <= arr_get (ds_window (rl_run s1)) j < 256)
                  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc (rl_run s1)) i < 65536)
                  /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc (rl_run s1)) i < 65536)
                  /\ (snd (rl_tally (rl_run s1)) = true -> fblk_ok fb_safe (fst (rl_tally (rl_run s1))) 0))).
      split.
      + split; [exact (DC_DOK c0 s1 HC0w HDC1)|]. split; [exact Hl1|]. split; [exact Hsl1|].
        split; [intros _ _; rewrite Ews1; exact Hss1|]. exact (df_wb _ D1).
      + rewrite Erun in Hml2, Hml2' |- *. revert Hml2 Hml2' FOK. rewrite Erun. dsred. intros Hml2 Hml2' FOK.
        destruct (DD_set_insert s1 (ds_insert s1) D1 X1 (df_ins _ D1) (dx_ins _ X1)) as [_ _].
        split.
        { pose proof (DC_DOK c0 s1 HC0w HDC1) as OK1. destruct OK1; constructor; dsred; assumption. }
        split; [exact Hl1|]. split; [exact Hsl1|]. split; [exact Hml2|]. split; [exact Hml2'|].
        split; [clear - Hsn1 Hn1; lia|]. split; [clear - Hsn1 Hn1; lia|]. split; [rewrite Hse1; clear - Sl1; lia|].
        split; [exact (df_wb _ D1)|]. split; [intros i _; exact (dx_tfc _ X1 DeflateState.TL i)|].
        split; [intros i _; exact (dx_tfc _ X1 DeflateState.TD i) | exact FOK].
  Qed.

  (* [comment removed for export] *)
  Lemma rle_loop : forall fuel s, RTI s -> lz_meas s < Z.of_nat fuel ->
    rl_loop_ok fb_safe fuel s flush
    /\ match snd (deflate_rle_loop fuel s flush) with
       | None => RTI (fst (deflate_rle_loop fuel s flush)) /\ ds_lookahead (fst (deflate_rle_loop fuel s flush)) = 0
       | Some bs => RRET (fst (deflate_rle_loop fuel s flush)) bs
       end.
  Proof.
    induction fuel as [|f IH]; intros s HI Hmz.
    { exfalso. pose proof (RTI_facts s HI) as (D & _ & V & _). pose proof (sv_ain _ _ V). pose proof (df_look _ D). unfold lz_meas in Hmz. cbn [Z.of_nat] in Hmz. lia. }
    rewrite rl_loop_ok_S, rloop_step. destruct (rle_step s HI) as [HT HC].
    destruct (snd (rl_body s flush)) eqn:E.
    - destruct HC as [HI' Hm'].
      destruct (IH (fst (rl_body s flush)) HI' ltac:(lia)) as [HL HF].
      split; [exact (conj HT HL) | exact HF].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
  Qed.

  (* [comment removed for export] *)
  Lemma rle_tail : forall s, RTI s -> ds_lookahead s = 0 ->
    tail0_ok fb_safe s flush
    /\ BFPOST c0 s0 flush (tail0 s flush).
  Proof.
    intros s HF Hl0.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (RTI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    set (st := set_insert s 0).
    destruct (DD_set_insert s 0 D X ltac:(clear - Hstr; lia) ltac:(clear - Sw; lia)) as [Dst Xst]. fold st in Dst, Xst.
    assert (Vst : SV c0 st) by (apply (SV_strm c0 s st eq_refl V)).
    assert (DCst : DC c0 st) by (exact (conj (conj Dst Xst) Vst)).
    assert (Hpst : ds_pending st = 0) by (exact Hp).
    assert (Hmst : dmode st = 2) by (exact Hm).
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
      pose proof (rflush st last Dst Vst (DX_DXX _ Xst) (DC_fb_entry c0 st last HC0w DCst Hpst ltac:(rewrite Hmst; lia) Hlast) Hstst Hmst (DX_BND st Xst) HKst Host) as FB. cbv zeta in FB.
      destruct FB as (FO & DC' & HK' & Ho' & _ & _ & Elook' & Hpa & _ & Ema').
      cbv zeta. split; [exact FO|]. split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|].
      split; [rewrite Elook'; exact Hlst|]. split; [exact Hpa | rewrite Ema'; exact Hmast]. }
    split.
    - unfold tail0_ok. cbv zeta. fold st.
      split; [exact (DC_DOK c0 st HC0w DCst)|].
      split; [intros _; exact (proj1 (FB 1 ltac:(lia))) | intros _ _; exact (proj1 (FB 0 ltac:(lia)))].
    - unfold tail0. fold st. unfold deflate_tail. destruct (Z.eqb_spec flush Z_FINISH) as [F4|F4].
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

End Rle.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rle_bf_spec : FB_CALL -> BF_SPEC 2 (rle_ok fb_safe) deflate_rle.
Proof.
  intros HFB c0 s flush (HC0 & HDC & Hp & Hst & Hfl) Hm.
  assert (HF : RTI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact Hm|]. split; [exact Hst | apply OUTLE_refl]. }
  pose proof HDC as [[D X] V].
  assert (Hmz : 0 <= lz_meas s) by (unfold lz_meas; pose proof (df_look _ D); pose proof (sv_ain _ _ V); lia).
  destruct (rle_loop c0 s flush HC0 HFB (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as [HL HR].
  assert (POST : BFPOST c0 s flush (deflate_rle s flush)).
  { unfold deflate_rle.
    destruct (deflate_rle_loop (lz_fuel s) s flush) as [s' r] eqn:E. cbn [fst snd] in HR.
    destruct r as [bs|].
    + destruct HR as (DC' & HK' & Ho' & ->). unfold BFPOST; cbn [fst snd].
      split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
      split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
    + destruct HR as [HF' Hl']. exact (proj2 (rle_tail c0 s flush HC0 HFB _ HF' Hl')). }
  split; [| exact POST].
  unfold rle_ok. split; [exact HL|]. split.
  - destruct (snd (deflate_rle_loop (lz_fuel s) s flush)); [exact I|].
    destruct HR as [HF' Hl']. exact (proj1 (rle_tail c0 s flush HC0 HFB _ HF' Hl')).
  - destruct POST as (DC' & HK' & Ho' & _). pose proof DC' as [[D' X'] V'].
    split; [exact (lz_keeps_intro c0 _ _ D D' V V' HK' Ho') | exact (DC_DOK c0 _ (c0'_ok _ HC0) DC')].
Qed.
