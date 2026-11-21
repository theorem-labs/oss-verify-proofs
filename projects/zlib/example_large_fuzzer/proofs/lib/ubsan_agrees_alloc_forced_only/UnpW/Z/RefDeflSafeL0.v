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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored7.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeW.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeLF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Ltac bytes_tac Hbb :=
  intros i Hi; rewrite !arr_get_set;
  repeat (match goal with |- 0 <= (if ?c then _ else _) < 256 => destruct c end; [apply wrap8_range|]); apply Hbb; exact Hi.

Lemma SV_aout0 : forall c0 s, C0OK c0 -> SV c0 s -> 0 <= cs_avail_out (ds_strm s) < 2 ^ 32.
Proof.
  intros c0 s HC0 V.
  pose proof (sv_out _ _ V) as Ou. pose proof (sv_aout _ _ V) as Ao. pose proof (c0_out _ HC0) as O0. pose proof (c0_aout _ HC0) as A0.
  rewrite O0 in Ou. unfold zlen in Ou. cbn [length Z.of_nat] in Ou. pose proof (zlen_nonneg (cs_out_rev (ds_strm s))) as Zl. unfold zlen in Zl. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SF (s : deflate_state) :=
  ((ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s, ds_level s, ds_strategy s),
   (ds_ins_h s, ds_match_length s, ds_prev_length s, ds_match_available s, ds_prev_match s, ds_match_start s, ds_lookahead s, ds_sym_next s),
   (ds_wrap s, ds_status s, ds_lit_bufsize s, ds_bl_tree_fc s, ds_dyn_ltree_dl s, ds_dyn_dtree_dl s, ds_bl_tree_dl s, ds_dyn_ltree_fc s, ds_dyn_dtree_fc s),
   (ds_depth s, ds_bl_count s, ds_opt_len s, ds_static_len s, ds_hash_size s, ds_w_mask s, ds_hash_mask s, ds_hash_shift s),
   (ds_head s, ds_prev s, ds_last_flush s, KV s, ds_sym_end s, ds_window_size s, ds_w_size s),
   (ds_w_bits s, ds_hash_bits s, ds_pending_buf_size s, ds_gzhead s, ds_method s, ds_heap s)).

Lemma SF_fields : forall a b, SF b = SF a ->
  (ds_good_match b = ds_good_match a /\ ds_max_lazy_match b = ds_max_lazy_match a /\ ds_nice_match b = ds_nice_match a
   /\ ds_max_chain_length b = ds_max_chain_length a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a)
  /\ (ds_ins_h b = ds_ins_h a /\ ds_match_length b = ds_match_length a /\ ds_prev_length b = ds_prev_length a /\ ds_match_available b = ds_match_available a
      /\ ds_prev_match b = ds_prev_match a /\ ds_match_start b = ds_match_start a /\ ds_lookahead b = ds_lookahead a /\ ds_sym_next b = ds_sym_next a)
  /\ (ds_wrap b = ds_wrap a /\ ds_status b = ds_status a /\ ds_lit_bufsize b = ds_lit_bufsize a
      /\ ds_bl_tree_fc b = ds_bl_tree_fc a /\ ds_dyn_ltree_dl b = ds_dyn_ltree_dl a /\ ds_dyn_dtree_dl b = ds_dyn_dtree_dl a /\ ds_bl_tree_dl b = ds_bl_tree_dl a
      /\ ds_dyn_ltree_fc b = ds_dyn_ltree_fc a /\ ds_dyn_dtree_fc b = ds_dyn_dtree_fc a)
  /\ (ds_depth b = ds_depth a /\ ds_bl_count b = ds_bl_count a /\ ds_opt_len b = ds_opt_len a /\ ds_static_len b = ds_static_len a
      /\ ds_hash_size b = ds_hash_size a /\ ds_w_mask b = ds_w_mask a /\ ds_hash_mask b = ds_hash_mask a /\ ds_hash_shift b = ds_hash_shift a)
  /\ (ds_head b = ds_head a /\ ds_prev b = ds_prev a /\ ds_last_flush b = ds_last_flush a /\ KV b = KV a /\ ds_sym_end b = ds_sym_end a
      /\ ds_window_size b = ds_window_size a /\ ds_w_size b = ds_w_size a)
  /\ (ds_w_bits b = ds_w_bits a /\ ds_hash_bits b = ds_hash_bits a /\ ds_pending_buf_size b = ds_pending_buf_size a /\ ds_gzhead b = ds_gzhead a
      /\ ds_method b = ds_method a /\ ds_heap b = ds_heap a).
Proof.
  intros a b E. unfold SF in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma DC_SF_transfer : forall c0 a b, DC c0 a -> dmode a = 0 -> SF b = SF a ->
  arr_len (ds_window b) = 2 * ds_w_size a -> (forall i, 0 <= i < 2 * ds_w_size a -> 0 <= arr_get (ds_window b) i < 256) ->
  0 <= ds_block_start b <= ds_strstart b -> ds_strstart b <= 2 * ds_w_size a ->
  0 <= ds_insert b <= ds_strstart b -> ds_insert b <= ds_w_size a ->
  0 <= ds_matches b <= 2 -> 0 <= ds_high_water b < 2 ^ 64 -> ds_high_water b <= ds_window_size a ->
  arr_len (ds_pending_buf b) = ds_lit_bufsize a * 4 -> (forall i, 0 <= i < ds_lit_bufsize a * 4 -> 0 <= arr_get (ds_pending_buf b) i < 256) ->
  0 <= ds_pending_out b -> 0 <= ds_pending b -> ds_pending_out b + ds_pending b <= ds_lit_bufsize a * 4 ->
  (ds_pending b = 0 -> ds_pending_out b = 0) ->
  0 <= ds_bi_valid b <= 7 -> 0 <= ds_bi_buf b < 2 ^ 16 ->
  SV c0 b ->
  DC c0 b.
Proof.
  intros c0 a b [[D X] V] Hm E Hwl Hwb Hbs Hstr Hins Hinsw Hmat Hhw Hhww Hpbl Hpbb Hpo Hpd Hpp Hpo0 Hbv Hbb Vb.
  pose proof (dwf_sizes a D) as (Sw & Sh & Sl & _).
  pose proof (SF_fields a b E) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eih & Eml & Epl & Ema & Epm & Ems & Elook & Esn) & (Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl & Elfc & Edfc)
                                   & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Ehd & Epv & Elf & EKV & Ese & Ewsz & Ews) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
  pose proof (KV_fields _ _ EKV) as (_ & _ & _ & KB).
  assert (Em : dmode b = 0) by (unfold dmode; rewrite Elv, Esy; exact Hm).
  destruct (dx_st0 _ X Hm) as (Hl0 & Hbs0 & Hsn0 & Hmt0).
  split; [split|]; [| | exact Vb].
  - pose proof (df_tl _ D) as TL.
    destruct D; constructor; rewrite ?Est, ?Ewr, ?Elbs, ?Ebl, ?Eldl, ?Eddl, ?Ebdl, ?Elfc, ?Edfc, ?Edep, ?Eblc, ?Ehs, ?Ewm, ?Ehm, ?Ehsh, ?Elf, ?Ese, ?Ewb, ?Ehb, ?Epbs,
        ?Egz, ?Eme, ?Elv, ?Esy, ?Ews, ?Ewsz, ?Ehd, ?Epv, ?Eih, ?Ems, ?Elook, ?Hwl, ?Hpbl; try assumption.
    + unfold deflateStateCheck in *. rewrite Est. assumption.
    + congruence.
    + congruence.
    + congruence.
    + congruence.
    + reflexivity.
    + reflexivity.
    + unfold tree_lens in *. rewrite Elfc, Edfc, Ebl, Eldl, Eddl, Ebdl, Eblc, Ehp, Edep. assumption.
    + clear - Hbs Hstr Sw. lia.
    + clear - Hbs Hstr Hl0. lia.
    + clear - Hpo Hpd Hpp. lia.
    + clear - Hbv Hbb. lia.
  - apply DX_join.
    + pose proof (dx_tdl _ X) as Xtdl. pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc. pose proof (DX_DXX a X) as XX.
      destruct XX; constructor; rewrite ?Em, ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Esy, ?Eih, ?Eml, ?Epl, ?Ema, ?Epm, ?Ems, ?Elook, ?Esn, ?Ewr, ?Est, ?Elbs, ?Ews, ?Ewsz, ?Edep, ?Eblc;
        try assumption.
      * intros HH. discriminate HH.
      * intros _. apply xx_notslow. rewrite Hm. clear; lia.
      * intros HH. discriminate HH.
      * intros _. rewrite Hl0. split; [reflexivity|]. split; [exact Hbs|]. split; [exact Hsn0 | clear - Hmat; lia].
      * intros t i. destruct t; cbn [tree_dl]; rewrite ?Eldl, ?Eddl, ?Ebdl; [apply (Xtdl TL i) | apply (Xtdl TD i) | apply (Xtdl TB i)].
      * intros Hm'. exfalso. exact (Hm' eq_refl).
    + pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_hist _ X) as XH.
      assert (En : nsym b = 0) by (unfold nsym; rewrite Esn, Hsn0; reflexivity).
      assert (Ena : nsym a = 0) by (unfold nsym; rewrite Hsn0; reflexivity).
      constructor; rewrite ?En, ?Em, ?Esn, ?Elbs, ?Eol, ?Esl; try assumption.
      * clear - Sl. lia.
      * intros j Hj. exfalso. clear - Hj. lia.
      * unfold freq_hist in *. rewrite En. rewrite Ena in XH. rewrite Elfc, Edfc, Ebl. exact XH.
      * exact (dx_opt _ X).
      * exact (dx_stat _ X).
      * intros Hm'. exfalso. exact (Hm' eq_refl).
      * intros t i. destruct t; cbn [tree_fc]; rewrite ?Elfc, ?Edfc, ?Ebl; [apply (Xtfc TL i) | apply (Xtfc TD i) | apply (Xtfc TB i)].
      * clear - Hbv. lia.
    + split; [intros Hm'; exfalso; exact (Hm' Em) | apply SLOW3_mode; rewrite Em; clear; lia].
Qed.

Section Stored.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Definition SI (s : deflate_state) : Prop :=
    DC c0 s /\ KV s = KV s0 /\ dmode s = 0 /\ ds_status s <> FINISH_STATE /\ OUTLE s0 s /\ ds_pending s = 0.

  Lemma SI_facts : forall s, SI s ->
    dwf s /\ DX s /\ SV c0 s
    /\ 512 <= ds_w_size s <= 32768 /\ 2048 <= ds_lit_bufsize s <= 32768 /\ ds_pending_buf_size s = ds_lit_bufsize s * 4
    /\ ds_lookahead s = 0 /\ 0 <= ds_block_start s <= ds_strstart s /\ ds_sym_next s = 0 /\ 0 <= ds_matches s <= 2
    /\ ds_strstart s <= 2 * ds_w_size s /\ ds_window_size s = 2 * ds_w_size s /\ 0 <= ds_wrap s <= 2
    /\ ds_pending_out s = 0 /\ 0 <= ds_bi_valid s <= 7 /\ 0 <= ds_bi_buf s < 2 ^ 16
    /\ 0 <= cs_avail_out (ds_strm s) < 2 ^ 32 /\ 0 <= cs_avail_in (ds_strm s) < 2 ^ 32
    /\ 0 <= ds_insert s <= ds_strstart s /\ ds_insert s <= ds_w_size s /\ 0 <= ds_high_water s < 2 ^ 64.
  Proof.
    intros s (HDC & HK & Hm & Hst & Ho & Hp). pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (Sw & Sh & Sl & Spbs & _).
    destruct (dx_st0 _ X Hm) as (Hl0 & Hbs & Hsn & Hmt). pose proof (RefDeflSafeI1.dx_matches _ X) as Hmt'.
    pose proof (df_sl _ D) as Hsl. pose proof (df_wrap _ D) as Hwr. pose proof (dx_wrapneg _ X) as Hwn.
    pose proof (df_bi _ D) as [Hbv Hbb]. pose proof (dx_biv _ X) as Hbv7.
    split; [exact D|]. split; [exact X|]. split; [exact V|]. split; [exact Sw|]. split; [exact Sl|]. split; [exact (df_pbs _ D)|].
    split; [exact Hl0|]. split; [exact Hbs|]. split; [exact Hsn|]. split; [clear - Hmt Hmt'; lia|].
    split; [clear - Hsl Hl0; lia|]. split; [exact (df_wsz _ D)|].
    split; [destruct (Z_lt_le_dec (ds_wrap s) 0); [exfalso; exact (Hst (Hwn l)) | clear - Hwr l; lia]|].
    split; [exact (dx_pout0 _ X Hp)|]. split; [clear - Hbv Hbv7; lia|]. split; [exact Hbb|].
    split; [exact (SV_aout0 c0 s HC0w V)|]. split; [exact (sv_ain _ _ V)|].
    split; [exact (df_ins _ D)|]. split; [exact (dx_ins _ X) | exact (df_hw _ D)].
  Qed.

  (* [comment removed for export] *)
  Lemma SI_st_entry : forall s, SI s -> st_entry s.
  Proof.
    intros s HS. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts s HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    constructor; [| exact Hp | exact Hpo | exact Hbb | exact Epbs | exact Hao].
    constructor; try assumption.
    - pose proof (df_bi _ D). lia.
    - exact (sv_nin _ _ V).
    - rewrite (sv_inlen _ _ V), (sv_input _ _ V). lia.
    - exact (sv_ib _ _ V).
    - exact (sv_tin _ _ V).
    - rewrite (sv_tout _ _ V). apply wrap64_range'.
    - intros _. exact (sv_adler _ _ V).
    - clear - Hins Hinsw. lia.
    - clear - Hmt. lia.
    - rewrite Epbs. clear - Sl. lia.
    - exact (df_wb _ D).
  Qed.

  (* [comment removed for export] *)
  Definition LZS (s : deflate_state) := (ds_window s, ds_strstart s, ds_insert s, ds_matches s, ds_high_water s).

  Lemma SF_upd4 : forall s a p b v, SF (upd4 s a p b v) = SF s. Proof. reflexivity. Qed.
  Lemma SF_fp_tail : forall s len, SF (fp_tail s len) = SF s.
  Proof. intros s len. unfold fp_tail. destruct (_ =? 0); reflexivity. Qed.
  Lemma LZS_upd4 : forall s a p b v, LZS (upd4 s a p b v) = LZS s. Proof. reflexivity. Qed.
  Lemma LZS_fp_tail : forall s len, LZS (fp_tail s len) = LZS s.
  Proof. intros s len. unfold fp_tail. destruct (_ =? 0); reflexivity. Qed.
  Lemma LZS_fields : forall a b, LZS b = LZS a ->
    ds_window b = ds_window a /\ ds_strstart b = ds_strstart a /\ ds_insert b = ds_insert a /\ ds_matches b = ds_matches a /\ ds_high_water b = ds_high_water a.
  Proof.
    intros a b E. unfold LZS in E.
    repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma emit_stage : forall t, SI t -> sb_hdr t <= cs_avail_out (ds_strm t) ->
    let t' := st_emit1 t flush in
    SI t' /\ SF t' = SF t /\ LZS t' = LZS t /\ ds_block_start t' = ds_block_start t
    /\ cs_avail_out (ds_strm t') = cs_avail_out (ds_strm t) - sb_hdr t
    /\ cs_avail_in (ds_strm t') = cs_avail_in (ds_strm t) /\ cs_next_in (ds_strm t') = cs_next_in (ds_strm t) /\ cs_input (ds_strm t') = cs_input (ds_strm t).
  Proof.
    intros t HS Hroom t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    pose proof (df_bb _ D) as Hbytes. pose proof (df_bl _ D) as Hbl.
    pose proof (sb_hdr_eq' t ltac:(clear - Hbv; lia)) as EP. rewrite Hp in EP.
    pose proof (sb_hdr_eq t ltac:(clear - Hbv; lia)) as [_ Hhdr7]. pose proof (proj1 (sb_hdr_eq t ltac:(clear - Hbv; lia))) as Ehdr. rewrite <- Ehdr in Hhdr7.
    pose proof (tsb_hP_range t) as HP. rewrite Hp in HP.
    unfold st_emit1. rewrite (tr_stored_block_eq t None 0 (sb_lastv t flush) ltac:(clear - Hbv; lia) Hbb). unfold tsb_tail. cbn [negb Z.eqb].
    set (A := tsb_lenA (tsb_hA t (sb_lastv t flush)) (tsb_hP t) 0).
    set (P := tsb_hP t + 1 + 1 + 1 + 1 + 0).
    set (len := sb_len t).
    set (A' := arr_set (arr_set (arr_set (arr_set A (P - 4) (wrap8 len)) (P - 3) (wrap8 (Z.shiftr len 8))) (P - 2) (wrap8 (Z.lnot len))) (P - 1) (wrap8 (Z.shiftr (wrap32 (Z.lnot len)) 8))).
    assert (E1 : sb_patch (upd4 t A P 0 0) len = upd4 t A' P 0 0) by reflexivity.
    rewrite E1.
    assert (HA : forall i, 3 <= i -> arr_get (tsb_hA t (sb_lastv t flush)) i = arr_get (ds_pending_buf t) i).
    { intros i Hi. unfold tsb_hA. rewrite Hp. destruct (_ <=? 5); [| destruct (_ <=? 13)]; rewrite !arr_get_set_other' by lia; reflexivity. }
    assert (HAb : forall i, 0 <= i < ds_lit_bufsize t * 4 -> 0 <= arr_get (tsb_hA t (sb_lastv t flush)) i < 256).
    { unfold tsb_hA. destruct (_ <=? 5); [| destruct (_ <=? 13)]; bytes_tac Hbytes. }
    assert (HA'b : forall i, 0 <= i < ds_lit_bufsize t * 4 -> 0 <= arr_get A' i < 256).
    { subst A' A. unfold tsb_lenA. bytes_tac HAb. }
    assert (HA'hi : forall i, ds_lit_bufsize t <= i -> arr_get A' i = arr_get (ds_pending_buf t) i).
    { intros i Hi. subst A' A P. unfold tsb_lenA. rewrite !arr_get_set_other' by lia. apply HA. lia. }
    assert (HA'len : arr_len A' = arr_len (ds_pending_buf t)) by (subst A' A; unfold tsb_lenA; rewrite !arr_len_set; apply tsb_hA_len).
    destruct (DC_upd4 c0 t A' P 0 0 HDC Hpo HA'len HA'b HA'hi ltac:(subst P; clear - HP Sl; lia) ltac:(clear; lia) ltac:(clear; lia)) as (DC1 & KV1 & Estrm1).
    set (X1 := upd4 t A' P 0 0) in *.
    assert (EP' : P = sb_hdr t) by (subst P; clear - EP; lia).
    assert (Efp : flush_pending X1 = fp_tail X1 P).
    { rewrite flush_pending_eq. cbv zeta. rewrite (tr_flush_bits_0 X1) by reflexivity.
      rewrite (fp_len_all X1) by (change (ds_pending X1) with P; change (ds_strm X1) with (ds_strm t); clear - HP Hroom EP' Sl; lia).
      change (ds_pending X1) with P. replace (P =? 0) with false by (symmetry; apply Z.eqb_neq; clear - HP; lia). reflexivity. }
    pose proof (DC_flush_pending c0 X1 HC0w DC1) as FPF. cbv zeta in FPF. rewrite Efp in FPF.
    destruct FPF as (DC2 & KV2 & Ho2 & _).
    pose proof (fp_tail_facts X1 P eq_refl) as TF. cbv zeta in TF.
    destruct TF as (Tpd & Tpo & _ & _ & Tao & Tai & Tni & Tin & _).
    change (ds_strm X1) with (ds_strm t) in Tao, Tai, Tni, Tin.
    assert (ESF : SF (fp_tail X1 P) = SF t) by (rewrite SF_fp_tail; subst X1; apply SF_upd4).
    pose proof (SF_fields _ _ ESF) as ((_ & _ & _ & _ & Elv & Esy) & _ & (_ & Est & _) & _).
    rewrite Efp. split.
    { split; [exact DC2|]. split; [rewrite KV2, KV1; exact HK|]. split; [unfold dmode; rewrite Elv, Esy; exact Hm|].
      split; [rewrite Est; exact Hst|]. split; [apply (OUTLE_trans _ t); [exact Ho | apply (OUTLE_trans _ X1); [apply OUTLE_strm; exact Estrm1 | exact Ho2]]|]. exact Tpd. }
    split; [exact ESF|]. split; [rewrite LZS_fp_tail; subst X1; apply LZS_upd4|].
    split; [etransitivity; [apply (f_equal ds_block_start (eq_refl _)) |]; unfold fp_tail; destruct (_ =? 0); reflexivity|].
    split; [rewrite Tao, EP'; reflexivity|]. split; [exact Tai|]. split; [exact Tni | exact Tin].
  Qed.

  Lemma dmode_SF : forall a b, SF b = SF a -> dmode b = dmode a.
  Proof. intros a b E. pose proof (SF_fields _ _ E) as ((_ & _ & _ & _ & Elv & Esy) & _). unfold dmode. rewrite Elv, Esy. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma SV_emit : forall t l (src : arr) ofs,
    SV c0 t -> 0 <= l <= cs_avail_out (ds_strm t) -> (forall i, ofs <= i < ofs + l -> 0 <= arr_get src i < 256) ->
    forall st, cs_input st = cs_input (ds_strm t) -> cs_next_in st = cs_next_in (ds_strm t) -> cs_avail_in st = cs_avail_in (ds_strm t) ->
    cs_out_rev st = rev_append (arr_slice src ofs l) (cs_out_rev (ds_strm t)) -> cs_avail_out st = cs_avail_out (ds_strm t) - l ->
    cs_total_in st = cs_total_in (ds_strm t) -> cs_total_out st = wrap64 (cs_total_out (ds_strm t) + l) ->
    cs_adler st = cs_adler (ds_strm t) -> cs_data_type st = cs_data_type (ds_strm t) ->
    forall t', ds_strm t' = st -> SV c0 t' /\ OUTLE t t'.
  Proof.
    intros t l src ofs V Hl Hsrc st Ein Eni Eai Eout Eao Eti Eto Ead Edt t' Est.
    assert (Hlen : Z.of_nat (length (cs_out_rev st)) = Z.of_nat (length (cs_out_rev (ds_strm t))) + l).
    { rewrite Eout, rev_append_rev, length_app, length_rev. unfold arr_slice. rewrite arr_slice_nat_length. lia. }
    split.
    - constructor; rewrite ?Est, ?Ein, ?Eni, ?Eai, ?Eao, ?Eti, ?Eto, ?Ead, ?Edt.
      + exact (sv_input _ _ V).
      + exact (sv_nin _ _ V).
      + exact (sv_inlen _ _ V).
      + exact (sv_ain _ _ V).
      + unfold zlen in *. rewrite Hlen. pose proof (sv_out _ _ V) as Ou. unfold zlen in Ou. lia.
      + lia.
      + pose proof (sv_grow _ _ V). rewrite Eout, rev_append_rev, length_app. lia.
      + rewrite Eout. apply Forall_rev_append; [| exact (sv_outb _ _ V)]. apply Forall_arr_slice. exact Hsrc.
      + exact (sv_tin _ _ V).
      + rewrite (sv_tout _ _ V), wrap64_add_l. f_equal. unfold zlen in *. rewrite Hlen. lia.
      + exact (sv_adler _ _ V).
      + exact (sv_dt _ _ V).
      + intros i Hi. apply (sv_ib _ _ V). exact Hi.
    - apply (OUTLE_emit _ _ (arr_slice src ofs l)). rewrite Est. exact Eout.
  Qed.

  (* [comment removed for export] *)
  Lemma lcopy_stage : forall t l, SI t -> 0 <= l -> ds_block_start t + l <= ds_strstart t -> l <= cs_avail_out (ds_strm t) ->
    let t' := st_lcopy t l in
    SI t' /\ SF t' = SF t /\ LZS t' = LZS t /\ ds_block_start t' = ds_block_start t + l
    /\ cs_avail_out (ds_strm t') = cs_avail_out (ds_strm t) - l
    /\ cs_avail_in (ds_strm t') = cs_avail_in (ds_strm t) /\ cs_next_in (ds_strm t') = cs_next_in (ds_strm t) /\ cs_input (ds_strm t') = cs_input (ds_strm t).
  Proof.
    intros t l HS Hl Hbl Hla t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    unfold st_lcopy.
    match goal with |- context [set_strm t ?st] => set (ST := st) end.
    destruct (SV_emit t l (ds_window t) (ds_block_start t) V ltac:(clear - Hl Hla; lia) ltac:(intros i Hi; apply (df_wb _ D); clear - Hi Hbs Hbl Hstr; lia)
                ST eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (set_block_start (set_strm t ST) (ds_block_start t + l)) eq_refl) as [V' Ho'].
    split.
    { split.
      { apply (DC_SF_transfer c0 t _ HDC Hm); dsred; try reflexivity; try assumption.
        all: first [exact (df_wl _ D) | exact (df_wb _ D) | exact (dx_hw _ X) | exact (df_bl _ D) | exact (df_bb _ D)
                   | clear - Hbs Hl Hbl; lia | clear - Hp Hpo Sl; lia | intros _; exact Hpo]. }
      split; [exact HK|]. split; [exact Hm|]. split; [exact Hst|]. split; [exact (OUTLE_trans _ _ _ Ho Ho') | exact Hp]. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. dsred. cbn. repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma input_slice_bytes : forall t ofs n, SV c0 t -> 0 <= ofs -> ofs + n <= arr_len (cs_input (ds_strm t)) ->
    forall b, In b (arr_slice (cs_input (ds_strm t)) ofs n) -> 0 <= b < 256.
  Proof. intros t ofs n V Ho Hn b Hb. eapply arr_slice_In; [| exact Hb]. intros i Hi. apply (sv_ib _ _ V). lia. Qed.

  (* [comment removed for export] *)
  Lemma rdo_stage : forall t n, SI t -> 0 < n <= cs_avail_in (ds_strm t) -> n <= cs_avail_out (ds_strm t) ->
    let t' := st_rdo t n in
    SI t' /\ SF t' = SF t /\ LZS t' = LZS t /\ ds_block_start t' = ds_block_start t
    /\ cs_avail_out (ds_strm t') = cs_avail_out (ds_strm t) - n
    /\ cs_avail_in (ds_strm t') = cs_avail_in (ds_strm t) - n /\ cs_next_in (ds_strm t') = cs_next_in (ds_strm t) + n /\ cs_input (ds_strm t') = cs_input (ds_strm t).
  Proof.
    intros t n HS Hn Hna t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    pose proof (sv_nin _ _ V) as Hni. pose proof (sv_inlen _ _ V) as Hil. rewrite <- (sv_input _ _ V) in Hil.
    assert (Hb : forall b, In b (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t)) n) -> 0 <= b < 256)
      by (apply input_slice_bytes; [exact V | exact Hni | clear - Hil Hn; lia]).
    set (bytes := arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t)) n) in *.
    set (ad := if ds_wrap t =? 1 then adler32_upd (cs_adler (ds_strm t)) bytes else if ds_wrap t =? 2 then crc32_upd (cs_adler (ds_strm t)) bytes else cs_adler (ds_strm t)).
    assert (Had : 0 <= ad < 2 ^ 64).
    { subst ad. destruct (ds_wrap t =? 1); [apply adler32_upd_range; exact Hb|]. destruct (ds_wrap t =? 2); [pose proof (crc32_upd_range (cs_adler (ds_strm t)) _ Hb); lia|]. exact (sv_adler _ _ V). }
    set (ST := mkCS (cs_input (ds_strm t)) (cs_next_in (ds_strm t) + n) (cs_avail_in (ds_strm t) - n) (rev_append bytes (cs_out_rev (ds_strm t)))
                    (cs_avail_out (ds_strm t) - n) (wrap64 (cs_total_in (ds_strm t) + n)) (wrap64 (cs_total_out (ds_strm t) + n)) (cs_msg (ds_strm t)) (cs_data_type (ds_strm t)) ad).
    assert (Erdo : st_rdo t n = set_strm t ST).
    { unfold st_rdo, read_buf. replace (negb (n =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      cbv zeta. rewrite (rb_len_eq n (cs_avail_in (ds_strm t)) Hn). replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota beta.
      subst ST ad bytes. unfold cs_emit. destruct (ds_wrap t =? 1); [| destruct (ds_wrap t =? 2)]; destruct t; cbn; destruct ds_strm; cbn; reflexivity. }
    rewrite Erdo.
    assert (Hlen : Z.of_nat (length (rev_append bytes (cs_out_rev (ds_strm t)))) = Z.of_nat (length (cs_out_rev (ds_strm t))) + n).
    { rewrite rev_append_rev, length_app, length_rev. subst bytes. unfold arr_slice. rewrite arr_slice_nat_length. lia. }
    assert (V' : SV c0 (set_strm t ST)).
    { constructor; cbn.
      - exact (sv_input _ _ V).
      - clear - Hni Hn. lia.
      - rewrite (sv_input _ _ V) in Hil. clear - Hil. lia.
      - clear - Hai Hn. lia.
      - unfold zlen in *. rewrite Hlen. pose proof (sv_out _ _ V) as Ou. unfold zlen in Ou. lia.
      - clear - Hna Hn Hao. lia.
      - pose proof (sv_grow _ _ V). rewrite rev_append_rev, length_app. lia.
      - apply Forall_rev_append; [| exact (sv_outb _ _ V)]. apply Forall_forall. exact Hb.
      - apply wrap64_range'.
      - rewrite (sv_tout _ _ V), wrap64_add_l. f_equal. unfold zlen in *. rewrite Hlen. lia.
      - exact Had.
      - exact (sv_dt _ _ V).
      - intros i Hi. apply (sv_ib _ _ V). exact Hi. }
    split.
    { split.
      { apply (DC_SF_transfer c0 t _ HDC Hm); dsred; try reflexivity; try assumption.
        all: first [exact (df_wl _ D) | exact (df_wb _ D) | exact (dx_hw _ X) | exact (df_bl _ D) | exact (df_bb _ D)
                   | clear - Hp Hpo Sl; lia | intros _; exact Hpo]. }
      split; [exact HK|]. split; [exact Hm|]. split; [exact Hst|]. split; [| exact Hp].
      apply (OUTLE_trans _ t); [exact Ho|]. eapply OUTLE_emit. cbn. reflexivity. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. cbn. repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma window_upd_bytes : forall t ofs l, dwf t -> (forall b, In b l -> 0 <= b < 256) ->
    arr_len (arr_upd (ds_window t) ofs l) = 2 * ds_w_size t /\ (forall j, 0 <= j < 2 * ds_w_size t -> 0 <= arr_get (arr_upd (ds_window t) ofs l) j < 256).
  Proof.
    intros t ofs l D Hl. split; [rewrite arr_len_upd; exact (df_wl _ D)|]. apply arr_upd_bytes; [exact (df_wb _ D) | exact Hl].
  Qed.
  Lemma window_blit_bytes : forall t dofs sofs n, dwf t ->
    arr_len (arr_blit (ds_window t) dofs (ds_window t) sofs n) = 2 * ds_w_size t
    /\ ((forall j, dofs <= j < dofs + n -> 0 <= sofs + (j - dofs) < 2 * ds_w_size t) ->
        forall j, 0 <= j < 2 * ds_w_size t -> 0 <= arr_get (arr_blit (ds_window t) dofs (ds_window t) sofs n) j < 256).
  Proof.
    intros t dofs sofs n D. split; [rewrite arr_len_blit; exact (df_wl _ D)|].
    intros Hs j Hj. rewrite arr_get_blit. destruct (_ && _) eqn:E; [| apply (df_wb _ D); exact Hj].
    apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    apply (df_wb _ D). apply Hs. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wupd_stage : forall t used, SI t -> 0 <= used <= cs_next_in (ds_strm t) ->
    let t' := st_wupd t used in
    SI t' /\ ds_strm t' = ds_strm t /\ (used <> 0 -> ds_block_start t' = ds_strstart t').
  Proof.
    intros t used HS Hu t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    pose proof (sv_nin _ _ V) as Hni. pose proof (sv_inlen _ _ V) as Hil. rewrite <- (sv_input _ _ V) in Hil.
    assert (GEN : forall w str ins mat,
      arr_len w = 2 * ds_w_size t -> (forall j, 0 <= j < 2 * ds_w_size t -> 0 <= arr_get w j < 256) ->
      0 <= str <= 2 * ds_w_size t -> 0 <= ins <= str -> ins <= ds_w_size t -> 0 <= mat <= 2 ->
      SI (set_block_start (set_insert (set_strstart (set_matches (set_window t w) mat) str) ins) str)).
    { intros w str ins mat Hwl Hwb Hs Hi Hiw Hmat'. split; [| split; [exact HK | split; [exact Hm | split; [exact Hst | split; [exact Ho | exact Hp]]]]].
      apply (DC_SF_transfer c0 t _ HDC Hm); dsred; try reflexivity; try assumption.
      all: first [clear - Hs; lia | exact (dx_hw _ X) | exact (df_bl _ D) | exact (df_bb _ D) | clear - Hpo; lia | clear - Hp; lia | clear - Hp Hpo Sl; lia | intros _; exact Hpo
                 | apply (SV_strm c0 t); [reflexivity | exact V]]. }
    unfold st_wupd.
    destruct (Z.eqb_spec used 0) as [U0|U0]; cbn [negb].
    { split; [exact HS|]. split; [reflexivity|]. intros HH; exfalso; exact (HH U0). }
    destruct (Z.leb_spec (ds_w_size t) used) as [C1|C1].
    - (* [comment removed for export] *)
      dsred.
      destruct (window_upd_bytes t 0 (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t) - ds_w_size t) (ds_w_size t)) D
                  ltac:(apply input_slice_bytes; [exact V | clear - Hu C1; lia | clear - Hu Hil Hai; lia])) as [Wl Wb].
      split; [| split; reflexivity].
      match goal with |- SI ?x => change x with (set_block_start (set_insert (set_strstart (set_matches (set_window t
        (arr_upd (ds_window t) 0 (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t) - ds_w_size t) (ds_w_size t)))) 2) (ds_w_size t)) (ds_w_size t)) (ds_w_size t)) end.
      apply GEN; try assumption; clear - Sw; lia.
    - assert (INS : forall ins, 0 <= ins <= ds_w_size t ->
        ins <= ins + MIN used (wrap32 (ds_w_size t - ins)) <= ds_w_size t /\ ins + MIN used (wrap32 (ds_w_size t - ins)) <= ins + used).
      { intros ins Hi. pose proof (ins_add_eq ins used (ds_w_size t) Hi ltac:(clear - Sw; lia) ltac:(clear - Hu; lia)) as [E R]. unfold ins_add in E, R.
        rewrite E in R |- *. destruct (Z.ltb_spec used (ds_w_size t - ins)) as [l|l]; clear - Hi R Hu l; lia. }
      destruct (Z.leb_spec (ds_window_size t - ds_strstart t) used) as [C2|C2].
      + (* [comment removed for export] *)
        rewrite Ewsz in C2.
        pose proof (window_blit_bytes t 0 (ds_w_size t) (ds_strstart t - ds_w_size t) D) as [Bl Bb].
        specialize (Bb ltac:(intros j Hj; clear - Hj C1 C2 Hstr Sw; lia)).
        assert (Hsl : forall b, In b (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t) - used) used) -> 0 <= b < 256)
          by (apply input_slice_bytes; [exact V | clear - Hu; lia | clear - Hu Hil Hai; lia]).
        dsred. destruct (Z.ltb_spec (ds_matches t) 2) as [C3|C3]; dsred; destruct (Z.ltb_spec (ds_strstart t - ds_w_size t) (ds_insert t)) as [C4|C4]; dsred;
          (split; [split; [match goal with |- DC _ ?x => apply (DC_SF_transfer c0 t x HDC Hm) end; dsred; try reflexivity; try assumption
                         | split; [exact HK | split; [exact Hm | split; [exact Hst | split; [exact Ho | exact Hp]]]]]
                 | split; [reflexivity | intros _; reflexivity]]);
          try (rewrite arr_len_upd; exact Bl); try (apply arr_upd_bytes; [exact Bb | exact Hsl]).
        all: try exact (dx_hw _ X). all: try exact (df_bl _ D). all: try exact (df_bb _ D). all: try (intros _; exact Hpo). all: try (apply (SV_strm c0 t); [reflexivity | exact V]).
        all: try (clear - C1 C2 C3 C4 Hstr Sw Hu Hmt Hp Hpo Sl; lia).
        all: first [pose proof (INS (ds_strstart t - ds_w_size t) ltac:(clear - C1 C2 Hstr Sw; lia)); clear - H C1 C2 Hstr Sw Hu; lia
                   | pose proof (INS (ds_insert t) ltac:(clear - Hins Hinsw; lia)); clear - H C1 C2 C4 Hstr Sw Hu Hins; lia
                   | match goal with |- ?g => idtac "GOAL" g end].
      + (* [comment removed for export] *)
        rewrite Ewsz in C2.
        assert (Hsl : forall b, In b (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t) - used) used) -> 0 <= b < 256)
          by (apply input_slice_bytes; [exact V | clear - Hu; lia | clear - Hu Hil Hai; lia]).
        destruct (window_upd_bytes t (ds_strstart t) (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t) - used) used) D Hsl) as [Wl Wb].
        dsred. split; [split; [match goal with |- DC _ ?x => apply (DC_SF_transfer c0 t x HDC Hm) end; dsred; try reflexivity; try assumption
                              | split; [exact HK | split; [exact Hm | split; [exact Hst | split; [exact Ho | exact Hp]]]]]
                      | split; [reflexivity | intros _; reflexivity]]; try exact Wl; try exact Wb.
        all: try exact (dx_hw _ X). all: try exact (df_bl _ D). all: try exact (df_bb _ D). all: try (intros _; exact Hpo). all: try (apply (SV_strm c0 t); [reflexivity | exact V]).
        all: try (clear - C2 Hbs Hu Hmt Hp Hpo Sl; lia).
        all: first [pose proof (INS (ds_insert t) ltac:(clear - Hins Hinsw; lia)); clear - H Hins Hu; lia
                   | match goal with |- ?g => idtac "GOAL" g end].
  Qed.

  Local Ltac si_rest HK Hm Hst Ho Hp := split; [exact HK | split; [exact Hm | split; [exact Hst | split; [exact Ho | exact Hp]]]].

  (* [comment removed for export] *)
  Lemma hw_stage : forall t, SI t -> SI (hw_st t) /\ ds_strm (hw_st t) = ds_strm t /\ ds_strstart (hw_st t) = ds_strstart t
    /\ ds_block_start (hw_st t) = ds_block_start t /\ ds_window_size (hw_st t) = ds_window_size t /\ ds_w_size (hw_st t) = ds_w_size t /\ ds_insert (hw_st t) = ds_insert t.
  Proof.
    intros t HS. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    unfold hw_st. destruct (Z.ltb_spec (ds_high_water t) (ds_strstart t)) as [C|C]; [| split; [exact HS | repeat split; reflexivity]].
    dsred. split; [| repeat split; reflexivity].
    split; [| si_rest HK Hm Hst Ho Hp].
    match goal with |- DC _ ?x => apply (DC_SF_transfer c0 t x HDC Hm) end; dsred; try reflexivity; try assumption.
    all: first [exact (df_wl _ D) | exact (df_wb _ D) | exact (df_bl _ D) | exact (df_bb _ D) | clear - Hbs Hstr Sw; lia | rewrite Ewsz; clear - Hstr; lia
               | clear - Hp Hpo Sl; lia | intros _; exact Hpo | apply (SV_strm c0 t); [reflexivity | exact V]].
  Qed.

  (* [comment removed for export] *)
  Lemma slide3_stage : forall t have, SI t -> have = 2 * ds_w_size t - ds_strstart t ->
    let r := st_slide3 t have in
    SI (fst r) /\ ds_strm (fst r) = ds_strm t /\ snd r = 2 * ds_w_size t - ds_strstart (fst r) /\ ds_w_size (fst r) = ds_w_size t.
  Proof.
    intros t have HS Hhave r. subst r. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    unfold st_slide3.
    destruct (Z.ltb_spec have (cs_avail_in (ds_strm t))) as [C1|C1]; [| cbn [andb fst snd]; split; [exact HS | repeat split; try reflexivity; exact Hhave]].
    destruct (Z.leb_spec (ds_w_size t) (ds_block_start t)) as [C2|C2]; cbn [andb fst snd]; [| split; [exact HS | repeat split; try reflexivity; exact Hhave]].
    pose proof (window_blit_bytes t 0 (ds_w_size t) (ds_strstart t - ds_w_size t) D) as [Bl Bb].
    specialize (Bb ltac:(intros j Hj; clear - Hj C2 Hbs Hstr Sw; lia)).
    dsred. destruct (Z.ltb_spec (ds_matches t) 2) as [C3|C3]; dsred; destruct (Z.ltb_spec (ds_strstart t - ds_w_size t) (ds_insert t)) as [C4|C4]; dsred;
      (split; [split; [match goal with |- DC _ ?x => apply (DC_SF_transfer c0 t x HDC Hm) end; dsred; try reflexivity; try assumption | si_rest HK Hm Hst Ho Hp]
             | split; [reflexivity | split; [rewrite wrap32_id by (clear - Hhave Hstr Hbs C2 Sw; lia); clear - Hhave; lia | reflexivity]]]).
    all: try exact Bl. all: try exact Bb. all: try exact (dx_hw _ X). all: try exact (df_bl _ D). all: try exact (df_bb _ D). all: try (intros _; exact Hpo).
    all: try (apply (SV_strm c0 t); [reflexivity | exact V]).
    all: clear - C1 C2 C3 C4 Hstr Hbs Sw Hmt Hp Hpo Sl Hins Hinsw; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fillw_stage : forall t n, SI t -> 0 <= n <= cs_avail_in (ds_strm t) -> n <= 2 * ds_w_size t - ds_strstart t ->
    let t' := st_fillw t n in
    SI t' /\ ds_strstart t' = ds_strstart t + n /\ ds_block_start t' = ds_block_start t /\ ds_w_size t' = ds_w_size t
    /\ cs_avail_in (ds_strm t') = cs_avail_in (ds_strm t) - n /\ cs_avail_out (ds_strm t') = cs_avail_out (ds_strm t)
    /\ ds_bi_valid t' = ds_bi_valid t /\ ds_pending_buf_size t' = ds_pending_buf_size t.
  Proof.
    intros t n HS Hn Hroom t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    pose proof (sv_nin _ _ V) as Hni. pose proof (sv_inlen _ _ V) as Hil. rewrite <- (sv_input _ _ V) in Hil.
    unfold st_fillw.
    destruct (Z.eqb_spec n 0) as [N0|N0]; cbn [negb].
    { split; [exact HS|]. rewrite N0, Z.add_0_r, Z.sub_0_r. repeat split; reflexivity. }
    unfold read_buf. cbv zeta. rewrite (rb_len_eq n (cs_avail_in (ds_strm t))) by (clear - Hn N0; lia).
    replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact N0). cbv iota beta.
    set (bytes := arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t)) n).
    assert (Hb : forall b, In b bytes -> 0 <= b < 256) by (subst bytes; apply input_slice_bytes; [exact V | exact Hni | clear - Hil Hn; lia]).
    set (ad := if ds_wrap t =? 1 then adler32_upd (cs_adler (ds_strm t)) bytes else if ds_wrap t =? 2 then crc32_upd (cs_adler (ds_strm t)) bytes else cs_adler (ds_strm t)).
    assert (Had : 0 <= ad < 2 ^ 64).
    { subst ad. destruct (ds_wrap t =? 1); [apply adler32_upd_range; exact Hb|]. destruct (ds_wrap t =? 2); [pose proof (crc32_upd_range (cs_adler (ds_strm t)) _ Hb); lia|]. exact (sv_adler _ _ V). }
    set (ST := mkCS (cs_input (ds_strm t)) (cs_next_in (ds_strm t) + n) (cs_avail_in (ds_strm t) - n) (cs_out_rev (ds_strm t))
                    (cs_avail_out (ds_strm t)) (wrap64 (cs_total_in (ds_strm t) + n)) (cs_total_out (ds_strm t)) (cs_msg (ds_strm t)) (cs_data_type (ds_strm t)) ad).
    set (w := arr_upd (ds_window t) (ds_strstart t) bytes).
    match goal with |- SI ?x /\ _ => assert (Ex : x = set_insert (set_strstart (set_strm (set_window t w) ST) (ds_strstart t + n)) (ins_add (ds_insert t) n (ds_w_size t)));
      [subst ST ad w; unfold ins_add; dsred; destruct (ds_wrap t =? 1); [| destruct (ds_wrap t =? 2)]; destruct t; cbn; destruct ds_strm; reflexivity | rewrite Ex] end.
    destruct (window_upd_bytes t (ds_strstart t) bytes D Hb) as [Wl Wb]. fold w in Wl, Wb.
    pose proof (ins_add_eq (ds_insert t) n (ds_w_size t) ltac:(clear - Hins Hinsw; lia) ltac:(clear - Sw; lia) ltac:(clear - Hn; lia)) as [Ei Ri].
    assert (Ri2 : ins_add (ds_insert t) n (ds_w_size t) <= ds_insert t + n) by (rewrite Ei; destruct (Z.ltb_spec n (ds_w_size t - ds_insert t)) as [l|l]; clear - Hins l Hn; lia).
    assert (V' : SV c0 (set_insert (set_strstart (set_strm (set_window t w) ST) (ds_strstart t + n)) (ins_add (ds_insert t) n (ds_w_size t)))).
    { constructor; cbn.
      - exact (sv_input _ _ V).
      - clear - Hni Hn. lia.
      - rewrite (sv_input _ _ V) in Hil. clear - Hil. lia.
      - clear - Hai Hn. lia.
      - exact (sv_out _ _ V).
      - exact (sv_aout _ _ V).
      - exact (sv_grow _ _ V).
      - exact (sv_outb _ _ V).
      - apply wrap64_range'.
      - exact (sv_tout _ _ V).
      - exact Had.
      - exact (sv_dt _ _ V).
      - intros i Hi. apply (sv_ib _ _ V). exact Hi. }
    dsred. split; [| cbn; repeat split; reflexivity].
    assert (Ho' : OUTLE s0 (set_insert (set_strstart (set_strm (set_window t w) ST) (ds_strstart t + n)) (ins_add (ds_insert t) n (ds_w_size t)))) by (apply (OUTLE_trans _ t); [exact Ho | apply OUTLE_out; cbn; reflexivity]).
    split; [| si_rest HK Hm Hst Ho' Hp].
    match goal with |- DC _ ?x => apply (DC_SF_transfer c0 t x HDC Hm) end; dsred; try reflexivity; try assumption.
    all: first [clear - Hbs Hn; lia | clear - Hroom Hn Hstr; lia | clear - Ri Ri2 Hins Hn; lia | clear - Ri; lia | exact (dx_hw _ X)
               | exact (df_bl _ D) | exact (df_bb _ D) | clear - Hp Hpo Sl; lia | intros _; exact Hpo].
  Qed.

  (* [comment removed for export] *)
  Lemma DC_upd4_st0 : forall a A P, SI a ->
    arr_len A = arr_len (ds_pending_buf a) -> (forall i, 0 <= i < ds_lit_bufsize a * 4 -> 0 <= arr_get A i < 256) -> 0 <= P <= ds_lit_bufsize a * 4 ->
    DC c0 (upd4 a A P 0 0) /\ SF (upd4 a A P 0 0) = SF a /\ ds_strm (upd4 a A P 0 0) = ds_strm a.
  Proof.
    intros a A P HS HlenA HbA HP. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts a HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    split; [| split; reflexivity].
    apply (DC_SF_transfer c0 a (upd4 a A P 0 0) HDC Hm); unfold upd4; dsred; try reflexivity; try assumption.
    all: first [exact (df_wl _ D) | exact (df_wb _ D) | exact (dx_hw _ X) | rewrite HlenA; exact (df_bl _ D) | clear - Hpo; lia | clear - HP; lia
               | clear - HP Hpo; lia | intros _; exact Hpo | clear; lia | apply (SV_strm c0 a); [reflexivity | exact V]].
  Qed.

  (* [comment removed for export] *)
  Lemma DC_set_block_start : forall a v, DC c0 a -> dmode a = 0 -> 0 <= v <= ds_strstart a -> DC c0 (set_block_start a v).
  Proof.
    intros a v HDC Hm Hv. pose proof HDC as [[D X] V]. pose proof (dwf_sizes a D) as (Sw & Sh & Sl & _).
    destruct (dx_st0 _ X Hm) as (Hl0 & Hbs & Hsn & Hmt). pose proof (df_sl _ D) as Hsl. pose proof (df_pend _ D) as Hpd. pose proof (df_bi _ D) as Hbi.
    pose proof (RefDeflSafeI1.dx_matches _ X) as M. unfold nsym in M. rewrite Hsn in M. change (0 / 3 + 2) with 2 in M.
    pose proof (dx_biv _ X) as B7.
    apply (DC_SF_transfer c0 a (set_block_start a v) HDC Hm); dsred; try reflexivity; try assumption.
    all: first [exact (df_wl _ D) | exact (df_wb _ D) | exact (df_ins _ D) | exact (dx_ins _ X) | exact (df_hw _ D) | exact (dx_hw _ X) | exact (df_bl _ D) | exact (df_bb _ D)
               | exact (dx_pout0 _ X) | apply (SV_strm c0 a); [reflexivity | exact V] | clear - Hsl Hl0 Hpd Hbi B7; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma final_stage : forall t, SI t ->
    let r := st_final t flush in
    DC c0 (fst r) /\ KV (fst r) = KV s0 /\ OUTLE s0 (fst r) /\ ds_lookahead (fst r) = 0
    /\ (snd r = finish_started \/ snd r = need_more).
  Proof.
    intros t HS r. subst r. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    pose proof (df_bb _ D) as Hbytes. pose proof (df_bl _ D) as Hbl.
    unfold st_final. cbv zeta.
    match goal with |- context [if ?c then _ else (t, need_more)] => destruct c eqn:Hcond end.
    2:{ cbn [fst snd]. split; [exact HDC|]. split; [exact HK|]. split; [exact Ho|]. split; [exact Hl0 | right; reflexivity]. }
    pose proof (t_have_eq t ltac:(clear - Hbv; lia) ltac:(rewrite Epbs; clear - Sl; lia)) as (Eh & Rh & Rhdr).
    assert (Hleft : wrap32 (ds_strstart t - ds_block_start t) = ds_strstart t - ds_block_start t) by (apply wrap32_id; clear - Hbs Hstr Sw; lia).
    rewrite Hleft.
    assert (Hhv : t_have t <= ds_pending_buf_size t - (ds_bi_valid t + 42) / 2 ^ 3).
    { rewrite Eh. destruct (Z.ltb_spec (ds_pending_buf_size t - (ds_bi_valid t + 42) / 2 ^ 3) 65536) as [l|l]; clear - l Rhdr Epbs Sl; lia. }
    set (len := MIN (ds_strstart t - ds_block_start t) (t_have t)).
    assert (Hlen : 0 <= len <= t_have t /\ len <= ds_strstart t - ds_block_start t).
    { subst len. unfold MIN. destruct (Z.ltb_spec (t_have t) (ds_strstart t - ds_block_start t)) as [l|l]; clear - l Rh Hbs; lia. }
    set (last := if (flush =? Z_FINISH) && (cs_avail_in (ds_strm t) =? 0) && (len =? ds_strstart t - ds_block_start t) then 1 else 0). clearbody last.
    pose proof (tsb_hP_range t) as HP. rewrite Hp in HP.
    pose proof (sb_hdr_eq' t ltac:(clear - Hbv; lia)) as EP. rewrite Hp in EP. pose proof (proj1 (sb_hdr_eq t ltac:(clear - Hbv; lia))) as Ehdr.
    rewrite (tr_stored_block_eq t (Some (ds_block_start t)) len last ltac:(clear - Hbv; lia) Hbb). unfold tsb_tail. cbv zeta.
    set (A2 := tsb_lenA (tsb_hA t last) (tsb_hP t) len).
    set (A3 := if negb (len =? 0) then arr_blit A2 (tsb_hP t + 1 + 1 + 1 + 1) (ds_window t) (ds_block_start t) len else A2).
    set (P := tsb_hP t + 1 + 1 + 1 + 1 + len).
    assert (HAb : forall i, 0 <= i < ds_lit_bufsize t * 4 -> 0 <= arr_get (tsb_hA t last) i < 256).
    { unfold tsb_hA. destruct (_ <=? 5); [| destruct (_ <=? 13)]; bytes_tac Hbytes. }
    assert (HA2b : forall i, 0 <= i < ds_lit_bufsize t * 4 -> 0 <= arr_get A2 i < 256) by (subst A2; unfold tsb_lenA; bytes_tac HAb).
    assert (HA3b : forall i, 0 <= i < ds_lit_bufsize t * 4 -> 0 <= arr_get A3 i < 256).
    { subst A3. destruct (negb (len =? 0)); [| exact HA2b]. intros i Hi. rewrite arr_get_blit.
      match goal with |- 0 <= (if ?c then _ else _) < 256 => destruct c eqn:E end; [| apply HA2b; exact Hi].
      apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      apply (df_wb _ D). clear - E1 E2 Hlen Hbs Hstr. lia. }
    assert (HA3len : arr_len A3 = arr_len (ds_pending_buf t)).
    { subst A3 A2. destruct (negb (len =? 0)); rewrite ?arr_len_blit; unfold tsb_lenA; rewrite !arr_len_set; apply tsb_hA_len. }
    destruct (DC_upd4_st0 t A3 P HS HA3len HA3b ltac:(subst P; clear - HP Hlen Hhv Epbs EP Ehdr; rewrite Ehdr in EP; lia)) as (DC1 & ESF1 & Estrm1).
    set (X1 := upd4 t A3 P 0 0) in *.
    assert (DC2 : DC c0 (set_block_start X1 (ds_block_start X1 + len))).
    { apply (DC_set_block_start X1 _ DC1 ltac:(rewrite (dmode_SF _ _ ESF1); exact Hm)). subst X1; unfold upd4; dsred. clear - Hbs Hlen. lia. }
    set (X2 := set_block_start X1 (ds_block_start X1 + len)) in *.
    pose proof (DC_flush_pending c0 X2 HC0w DC2) as FPF. cbv zeta in FPF.
    destruct FPF as (DC3 & KV3 & Ho3 & Ecore & _).
    pose proof (dx_core2_fields _ _ Ecore) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Elook3 & _).
    cbn [fst snd]. split; [exact DC3|].
    split; [rewrite KV3; subst X2 X1; unfold upd4; dsred; exact HK|].
    split; [apply (OUTLE_trans _ X2); [apply (OUTLE_trans _ t); [exact Ho | apply OUTLE_strm; subst X2 X1; reflexivity] | exact Ho3]|].
    split; [rewrite Elook3; subst X2 X1; unfold upd4; dsred; exact Hl0|].
    destruct (negb (last =? 0)); [left | right]; reflexivity.
  Qed.
  Lemma rdo_stage0 : forall t n, SI t -> 0 <= n <= cs_avail_in (ds_strm t) -> n <= cs_avail_out (ds_strm t) ->
    SI (st_rdo t n) /\ cs_avail_in (ds_strm (st_rdo t n)) = cs_avail_in (ds_strm t) - n.
  Proof.
    intros t n HS Hn Hna. destruct (Z.eq_dec n 0) as [N0|N0].
    - subst n. unfold st_rdo. cbn [negb Z.eqb]. split; [exact HS | lia].
    - pose proof (rdo_stage t n HS ltac:(lia) Hna) as R. cbv zeta in R. destruct R as (R1 & _ & _ & _ & _ & R6 & _). exact (conj R1 R6).
  Qed.

  (* [comment removed for export] *)
  Lemma trip_stage : forall t mb, SI t -> sb_broke t flush mb = false ->
    let t' := st_trip t flush in SI t' /\ cs_avail_in (ds_strm t') <= cs_avail_in (ds_strm t).
  Proof.
    intros t mb HS Hb t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    unfold sb_broke in Hb. apply Bool.orb_false_iff in Hb. destruct Hb as [Hb _]. apply Z.ltb_ge in Hb.
    pose proof (sb_len_range t ltac:(clear - Hai; lia) Hb) as (Rl1 & Rl2 & Rl3).
    pose proof (sb_len1_eq t ltac:(clear - Hai; lia)) as (_ & _ & Rl4).
    assert (Eleft : sb_left t = ds_strstart t - ds_block_start t) by (unfold sb_left; apply wrap32_id; clear - Hbs Hstr Sw; lia).
    unfold st_trip.
    pose proof (emit_stage t HS Hb) as E. cbv zeta in E. destruct E as (HS3 & ESF3 & ELZ3 & Ebs3 & Eao3 & Eai3 & Eni3 & Ein3).
    pose proof (LZS_fields _ _ ELZ3) as (Ew3 & Estr3 & _).
    set (t3 := st_emit1 t flush) in *. clearbody t3.
    unfold st_copy. rewrite Eleft in Rl4 |- *.
    destruct (Z.eqb_spec (ds_strstart t - ds_block_start t) 0) as [L0|L0]; cbn [negb fst snd].
    - destruct (rdo_stage0 t3 (sb_len t) HS3 ltac:(rewrite Eai3; clear - Rl1 Rl3 Rl4 L0; lia) ltac:(rewrite Eao3; exact Rl2)) as [HS5 Eai5].
      split; [exact HS5|]. rewrite Eai5, Eai3. clear - Rl1. lia.
    - set (l := lc_len (ds_strstart t - ds_block_start t) (sb_len t)).
      assert (Hl : 0 <= l <= sb_len t /\ l <= ds_strstart t - ds_block_start t /\ sb_len t - l <= cs_avail_in (ds_strm t)).
      { subst l. unfold lc_len. destruct (Z.ltb_spec (sb_len t) (ds_strstart t - ds_block_start t)) as [l0|l0]; clear - l0 Rl1 Rl3 Rl4 Hbs Hai; lia. }
      pose proof (lcopy_stage t3 l HS3 ltac:(clear - Hl; lia) ltac:(rewrite Ebs3, Estr3; clear - Hl; lia) ltac:(rewrite Eao3; clear - Hl Rl2; lia)) as C. cbv zeta in C.
      destruct C as (HS4 & _ & _ & _ & Eao4 & Eai4 & _).
      set (t4 := st_lcopy t3 l) in *. clearbody t4.
      destruct (rdo_stage0 t4 (sb_len t - l) HS4 ltac:(rewrite Eai4, Eai3; clear - Hl; lia) ltac:(rewrite Eao4, Eao3; clear - Hl Rl2; lia)) as [HS5 Eai5].
      split; [exact HS5|]. rewrite Eai5, Eai4, Eai3. clear - Hl. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_stage : forall fuel t mb, SI t ->
    SI (fst (deflate_stored_loop fuel t flush mb)) /\ cs_avail_in (ds_strm (fst (deflate_stored_loop fuel t flush mb))) <= cs_avail_in (ds_strm t).
  Proof.
    induction fuel as [|f IH]; intros t mb HS.
    - cbn [deflate_stored_loop fst]. split; [exact HS | lia].
    - rewrite sloop_S'. destruct (sb_broke t flush mb) eqn:Hb; [cbn [fst]; split; [exact HS | lia]|].
      pose proof (trip_stage t mb HS Hb) as T. cbv zeta in T. destruct T as [HS1 Hai1].
      destruct (sb_lastv t flush =? 0).
      + destruct (IH (st_trip t flush) mb HS1) as [HS2 Hai2]. split; [exact HS2 | lia].
      + cbn [fst]. split; [exact HS1 | exact Hai1].
  Qed.

End Stored.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem stored_bf_spec : BF_SPEC 0 stored_safe deflate_stored.
Proof.
  intros c0 s flush (HC0 & HDC & Hp & Hst & Hfl) Hm. pose proof (c0'_ok _ HC0) as HC0w.
  assert (HS : SI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hm|]. split; [exact Hst|]. split; [apply OUTLE_refl | exact Hp]. }
  pose proof HDC as [[D X] V].
  pose proof (SI_facts c0 s HC0 s HS) as (_ & _ & _ & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & _).
  split; [exact (stored_safe_intro s flush (SI_st_entry c0 s HC0 s HS) (dwf_DWF s D Hao))|].
  rewrite deflate_stored_eq. cbv zeta.
  set (mb := wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s))). clearbody mb.
  set (fuel := Z.to_nat (cs_avail_out (ds_strm s) + 1)). clearbody fuel.
  destruct (loop_stage c0 s flush HC0 fuel s mb HS) as [HSL HaiL].
  set (sL := fst (deflate_stored_loop fuel s flush mb)) in *. clearbody sL.
  set (last := snd (deflate_stored_loop fuel s flush mb)). clearbody last.
  pose proof (SI_facts c0 s HC0 sL HSL) as (DL & XL & VL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HaiL2 & _).
  assert (Eused : wrap32 (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL)) = cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL))
    by (apply wrap32_id; clear - HaiL Hai HaiL2; lia).
  rewrite Eused.
  pose proof (sv_inlen _ _ V) as Il. pose proof (sv_inlen _ _ VL) as IlL. pose proof (sv_nin _ _ V) as Ni.
  pose proof (wupd_stage c0 s HC0 sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL)) HSL ltac:(clear - HaiL Il IlL Ni; lia)) as W. cbv zeta in W.
  destruct W as (HSW & EstrmW & HbsW).
  set (sW := st_wupd sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL))) in *. clearbody sW.
  pose proof (hw_stage c0 s HC0 sW HSW) as (HS2 & Estrm2 & Estr2 & Ebs2 & Ewsz2 & Ews2 & _).
  set (s2 := hw_st sW) in *. clearbody s2.
  pose proof HS2 as (HDC2 & HK2 & Hm2 & Hst2 & Ho2 & Hp2).
  pose proof (SI_facts c0 s HC0 s2 HS2) as (D2 & X2 & V2 & Sw2 & _ & _ & Hl02 & Hbs2 & _ & _ & Hstr2 & Ewsz2' & _ & _ & _ & _ & _ & Hai2 & _).
  destruct (negb (last =? 0)).
  { unfold BFPOST; cbn [fst snd]. split; [exact HDC2|]. split; [exact HK2|]. split; [exact Ho2|].
    split; [intros HH; discriminate HH|]. split; [intros _; exact Hl02|]. intros _. exact Hp2. }
  match goal with |- context [if ?c then (s2, block_done) else _] => destruct c eqn:Hcond end.
  { unfold BFPOST; cbn [fst snd]. split; [exact HDC2|]. split; [exact HK2|]. split; [exact Ho2|].
    split.
    - intros _. split; [exact Hp2|]. split; [| exact (dx_notslow _ X2 ltac:(rewrite Hm2; lia))].
      apply andb_prop in Hcond as [Hcond _]. apply andb_prop in Hcond as [Hcond _]. apply andb_prop in Hcond as [_ Hcond].
      intros F4. rewrite F4 in Hcond. cbn in Hcond. discriminate Hcond.
    - split; [intros [HH|HH]; discriminate HH | intros HH; discriminate HH]. }
  assert (Ehave : wrap32 (ds_window_size s2 - ds_strstart s2) = 2 * ds_w_size s2 - ds_strstart s2) by (rewrite Ewsz2'; apply wrap32_id; clear - Hstr2 Hbs2 Sw2; lia).
  rewrite Ehave.
  pose proof (slide3_stage c0 s HC0 s2 _ HS2 eq_refl) as SL3. cbv zeta in SL3. destruct SL3 as (HS3 & Estrm3 & Ehave3 & Ews3).
  destruct (st_slide3 s2 (2 * ds_w_size s2 - ds_strstart s2)) as [s3 have]. cbn [fst snd] in *.
  pose proof (SI_facts c0 s HC0 s3 HS3) as (_ & _ & _ & _ & _ & _ & _ & Hbs3 & _ & _ & Hstr3 & _ & _ & _ & _ & _ & _ & Hai3 & _).
  assert (Hfm : 0 <= fmin have (cs_avail_in (ds_strm s3)) <= cs_avail_in (ds_strm s3) /\ fmin have (cs_avail_in (ds_strm s3)) <= 2 * ds_w_size s3 - ds_strstart s3).
  { unfold fmin. rewrite Ehave3, Ews3. destruct (Z.ltb_spec (cs_avail_in (ds_strm s3)) (2 * ds_w_size s2 - ds_strstart s3)) as [l|l]; clear - l Hai3 Hstr3 Hbs3 Ews3; lia. }
  pose proof (fillw_stage c0 s HC0 s3 (fmin have (cs_avail_in (ds_strm s3))) HS3 (proj1 Hfm) (proj2 Hfm)) as FW. cbv zeta in FW. destruct FW as (HS4 & _).
  set (s4 := st_fillw s3 (fmin have (cs_avail_in (ds_strm s3)))) in *. clearbody s4.
  pose proof (hw_stage c0 s HC0 s4 HS4) as (HS5 & _).
  set (s5 := hw_st s4) in *. clearbody s5.
  pose proof (final_stage c0 s flush HC0 s5 HS5) as FN. cbv zeta in FN. destruct FN as (DCf & KVf & Hof & Hlf & Hbsf).
  destruct (st_final s5 flush) as [sf bs]. cbn [fst snd] in *.
  unfold BFPOST; cbn [fst snd]. split; [exact DCf|]. split; [exact KVf|]. split; [exact Hof|].
  split; [intros ->; destruct Hbsf as [HH|HH]; discriminate HH|].
  split; [intros _; exact Hlf|]. intros ->. destruct Hbsf as [HH|HH]; discriminate HH.
Qed.
