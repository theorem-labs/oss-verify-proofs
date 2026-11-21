(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateParams.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel RefDeflateRel RefDeflateInitLib RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI4 RefDeflSafeI5b BoundFw.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateParamsDD DeflateParamsZ1 ZApiOkL ZTaintL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_defl_path Zg_defl_path Zg_defl_pathi Zl_defl_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma set_level_fields : forall s level strategy, dwf s ->
  let s' := set_strategy (if negb (ds_level s =? level) then dparams_set_level s level else s) strategy in
  ds_strm s' = ds_strm s /\ ds_level s' = level /\ ds_strategy s' = strategy /\ ds_wrap s' = ds_wrap s /\ ds_status s' = ds_status s
  /\ ds_w_size s' = ds_w_size s /\ ds_hash_size s' = ds_hash_size s /\ ds_lit_bufsize s' = ds_lit_bufsize s.
Proof.
  intros s level strategy D. cbv zeta.
  destruct (Z.eqb_spec (ds_level s) level) as [EL|NL]; cbn [negb].
  - repeat split; try (destruct s; reflexivity). destruct s; cbn. exact EL.
  - rewrite dparams_set_level_eq. destruct (configuration_table level) as [[[good lazy] nice] chain]. cbv zeta.
    destruct (pre_st_shape s D) as (hd & pv & E & _). rewrite E.
    destruct (_ && _); repeat split; destruct s; reflexivity.
Qed.

Lemma SV_same_strm : forall c0 a b, ds_strm b = ds_strm a -> SV c0 a -> SV c0 b.
Proof. intros c0 a b E V. destruct V. constructor; rewrite ?E; assumption. Qed.

(* [comment removed for export] *)
Lemma dparams_lv_ok : forall level strategy X, dwf X -> DX X -> ds_w_size X = 32768 -> ds_hash_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  dparams_lv level strategy (set_strategy (if negb (ds_level X =? level) then dparams_set_level X level else X) strategy, Z_OK) X.
Proof.
  intros level strategy X D XX WS HS LBS. unfold dparams_lv.
  pose proof (df_level _ D) as RL. pose proof (dx_matches _ XX) as RM. pose proof (dx_nsym _ XX) as RN. rewrite LBS in RN.
  split; [exact RL|]. split; [lia|].
  split.
  - intros EL. rewrite EL, Z.eqb_refl. reflexivity.
  - intros NL. replace (ds_level X =? level) with false by (symmetry; apply Z.eqb_neq; exact NL). cbn [negb].
    split; [| reflexivity]. intros _ _. split; [exact WS|]. split; [exact HS|].
    split; intros i Hi; [apply (df_hb _ D); rewrite HS | apply (df_pb _ D); rewrite WS]; exact Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Api.
  Variables (ds : deflate_state) (zc : ZCall) (level strategy : Z).
  Hypothesis HDD : DD ds.
  Hypothesis Hzc : dcall_wf zc.
  Hypothesis P : PATG ds.
  Hypothesis HWS : ds_w_size ds = 32768.
  Hypothesis HHS : ds_hash_size ds = 32768.
  Hypothesis HLBS : ds_lit_bufsize ds = 16384.
  Hypothesis HL : 0 <= level <= 9.
  Hypothesis HCL : cfunc_id level = 0 \/ cfunc_id level = 2.
  Hypothesis HST : strategy = 0 \/ strategy = 1.
  Hypothesis HIL : zlength (zc_input zc) < 2^31.
  Hypothesis HAO : zc_avail_out zc < 2^31.

  Let c0 := cstrm_of_call zc.
  Let d0 := set_strm ds c0.
  Let HB5 : Z_BLOCK = Z_NO_FLUSH \/ Z_BLOCK = Z_FINISH \/ Z_BLOCK = Z_BLOCK := or_intror (or_intror eq_refl).

  Lemma dp_D0 : dwf d0. Proof. exact (proj1 (DD_set_strm ds c0 HDD)). Qed.
  Lemma dp_X0 : DX d0. Proof. exact (proj2 (DD_set_strm ds c0 HDD)). Qed.
  Lemma dp_V0 : SV c0 d0. Proof. subst d0 c0. apply SV_entry. exact Hzc. Qed.

  (* [comment removed for export] *)
  Let X1 := fst (deflate_core d0 Z_BLOCK).

  Lemma X1_facts : PATG X1 /\ dwf X1 /\ DX X1 /\ SV c0 X1 /\ ds_w_size X1 = 32768 /\ ds_hash_size X1 = 32768 /\ ds_lit_bufsize X1 = 16384
    /\ 0 <= cs_avail_in (ds_strm X1) < 2^31 /\ 0 <= ds_strstart X1 < 2^32 /\ 0 <= ds_lookahead X1 < 2^32 /\ - 2^62 <= ds_block_start X1 < 2^62.
  Proof.
    destruct (deflate_core_P2g ds zc Z_BLOCK HDD Hzc P HWS HHS HLBS HB5 HIL HAO) as [PX [[[D X] V] K]]. fold c0 d0 X1 in PX, D, X, V, K.
    pose proof (KV_fields _ _ K) as (Kw & Kh & Kl & _).
    change (ds_w_size d0) with (ds_w_size ds) in Kw. change (ds_hash_size d0) with (ds_hash_size ds) in Kh. change (ds_lit_bufsize d0) with (ds_lit_bufsize ds) in Kl.
    rewrite HWS in Kw. rewrite HHS in Kh. rewrite HLBS in Kl.
    pose proof (sv_inlen _ _ V) as A2. pose proof (sv_nin _ _ V) as A3. pose proof (sv_ain _ _ V) as A1.
    assert (IL : arr_len (cs_input c0) = zlength (zc_input zc)) by (subst c0; cbn [cstrm_of_call cs_input]; apply arr_len_of_list). rewrite IL in A2.
    pose proof (df_strstart _ D) as RSS. pose proof (df_look _ D) as RLA. pose proof (df_sl _ D) as RSL. rewrite Kw in RSL.
    pose proof (dx_nsym _ X) as RN. rewrite Kl in RN. pose proof (dx_ma _ X) as RMA.
    assert (RBS : - 2^62 <= ds_block_start X1 < 2^62).
    { destruct (Z.eq_dec (dmode X1) 0) as [M|M].
      - pose proof (dx_st0 _ X M) as (_ & B & _). lia.
      - pose proof (dx_ext _ X M) as B. lia. }
    split; [exact PX|]. split; [exact D|]. split; [exact X|]. split; [exact V|]. split; [exact Kw|]. split; [exact Kh|]. split; [exact Kl|].
    split; [lia|]. split; [exact RSS|]. split; [lia|]. exact RBS.
  Qed.

  Theorem dparams_path_intro : dparams_path (zc_input zc) level strategy (deflateParams_core d0 level strategy) d0.
  Proof.
    pose proof dp_D0 as D0. pose proof dp_X0 as X0. pose proof (PATG_set_strm ds c0 P) as P0. fold d0 in P0.
    assert (HS4 : 0 <= strategy <= Z_FIXED) by (unfold Z_FIXED; destruct HST as [-> | ->]; lia).
    unfold dparams_path.
    split; [exact (pg_st _ P0)|]. split; [exact (df_level _ D0)|]. split; [pose proof (PATG_strategy _ P0); lia|]. split; [exact (df_lf _ D0)|].
    split; [exact HL|]. split; [destruct HST as [-> | ->]; lia|].
    rewrite (deflateParams_core_eq d0 level strategy (df_status _ D0) HL HS4). cbv zeta.
    split.
    - intros Efl. rewrite Efl.
      destruct X1_facts as (PX & D1 & XX1 & V1 & Kw & Kh & Kl & RAI & RSS & RLA & RBS).
      pose proof (defl_pathg_intro ds zc Z_BLOCK HDD Hzc P HWS HHS HLBS HB5 HIL HAO) as PATH. fold c0 d0 in PATH.
      pose proof (deflate_core_rc d0 Z_BLOCK) as RC.
      change 5 with Z_BLOCK.
      revert PX D1 XX1 V1 Kw Kh Kl RAI RSS RLA RBS PATH RC. subst X1. generalize (deflate_core d0 Z_BLOCK). intros [s1 err]. cbn [fst snd].
      intros PX D1 XX1 V1 Kw Kh Kl RAI RSS RLA RBS PATH RC.
      split; [exact PATH|]. split; [exact RAI|]. split; [exact RSS|]. split; [exact RLA|]. split; [exact RBS|].
      split.
      { destruct (err =? Z_STREAM_ERROR); [cbn [fst]; apply Nat.le_refl|].
        destruct (_ || _); cbn [fst]; [apply Nat.le_refl|].
        rewrite (proj1 (set_level_fields s1 level strategy D1)). apply Nat.le_refl. }
      split; [destruct RC as [E|[E|[E|E]]]; rewrite E; unfold Z_OK, Z_STREAM_END, Z_STREAM_ERROR, Z_BUF_ERROR; lia|].
      split; [intros E; rewrite E; reflexivity|].
      split.
      { intros NE HOR. replace (err =? Z_STREAM_ERROR) with false by (symmetry; apply Z.eqb_neq; exact NE).
        destruct HOR as [A|A].
        - replace (cs_avail_in (ds_strm s1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact A). reflexivity.
        - replace (ds_strstart s1 - ds_block_start s1 + ds_lookahead s1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact A).
          rewrite orb_true_r. reflexivity. }
      intros NE A0 S0. replace (err =? Z_STREAM_ERROR) with false by (symmetry; apply Z.eqb_neq; exact NE).
      rewrite A0, S0. cbn [Z.eqb negb orb].
      exact (dparams_lv_ok level strategy s1 D1 XX1 Kw Kh Kl).
    - intros Efl. rewrite Efl.
      apply (dparams_lv_ok level strategy d0 D0 X0); [exact HWS| exact HHS| exact HLBS].
  Qed.

  (* [comment removed for export] *)
  Theorem dparams_core_facts :
    let R := deflateParams_core d0 level strategy in
    PATG (fst R) /\ SV c0 (fst R) /\ fwT (fst R) = fwT d0
    /\ ds_w_size (fst R) = 32768 /\ ds_hash_size (fst R) = 32768 /\ ds_lit_bufsize (fst R) = 16384.
  Proof.
    pose proof dp_D0 as D0. pose proof dp_X0 as X0. pose proof dp_V0 as V0. pose proof (PATG_set_strm ds c0 P) as P0. fold d0 in P0.
    assert (HS4 : 0 <= strategy <= Z_FIXED) by (unfold Z_FIXED; destruct HST as [-> | ->]; lia).
    pose proof (zl_level_cases level HL HCL) as HLV.
    assert (SW : forall X, PATG X -> dwf X -> ds_w_size X = 32768 -> ds_hash_size X = 32768 -> ds_lit_bufsize X = 16384 ->
              let s' := set_strategy (if negb (ds_level X =? level) then dparams_set_level X level else X) strategy in
              PATG s' /\ ds_strm s' = ds_strm X /\ ds_w_size s' = 32768 /\ ds_hash_size s' = 32768 /\ ds_lit_bufsize s' = 16384).
    { intros X PX DX_ WS HS LBS. cbv zeta.
      destruct (set_level_fields X level strategy DX_) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
      revert E1 E2 E3 E4 E5 E6 E7 E8. generalize (set_strategy (if negb (ds_level X =? level) then dparams_set_level X level else X) strategy).
      intros s' E1 E2 E3 E4 E5 E6 E7 E8.
      split; [| rewrite E6, E7, E8; repeat split; assumption].
      destruct PX as [Q1 Q2 Q3 Q4]. constructor.
      - rewrite (dmode_zl s' ltac:(rewrite E3; exact HST)), E2.
        destruct HLV as [-> | R4]; [left; reflexivity| right].
        replace (level =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (level <=? 3) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      - rewrite E3. exact HST.
      - rewrite E4, E5. exact Q3.
      - rewrite E5. exact Q4. }
    cbv zeta. rewrite (deflateParams_core_eq d0 level strategy (df_status _ D0) HL HS4). cbv zeta.
    destruct (dparams_flushes d0 level strategy).
    - destruct X1_facts as (PX & D1 & XX1 & V1 & Kw & Kh & Kl & _).
      pose proof (defl_pathg_intro ds zc Z_BLOCK HDD Hzc P HWS HHS HLBS HB5 HIL HAO) as PATH. fold c0 d0 in PATH.
      destruct PATH as [[_ FT] _]. fold X1 in FT.
      revert PX D1 XX1 V1 Kw Kh Kl FT. subst X1. generalize (deflate_core d0 Z_BLOCK). intros [s1 err]. cbn [fst snd].
      intros PX D1 XX1 V1 Kw Kh Kl FT.
      assert (G1 : PATG s1 /\ SV c0 s1 /\ fwT s1 = fwT d0 /\ ds_w_size s1 = 32768 /\ ds_hash_size s1 = 32768 /\ ds_lit_bufsize s1 = 16384)
        by (split; [exact PX|]; split; [exact V1|]; split; [exact FT|]; split; [exact Kw|]; split; [exact Kh| exact Kl]).
      destruct (err =? Z_STREAM_ERROR); [cbn [fst]; exact G1|].
      destruct (_ || _); cbn [fst]; [exact G1|].
      destruct (SW s1 PX D1 Kw Kh Kl) as (P' & ES & W' & H' & L').
      split; [exact P'|]. split; [exact (SV_same_strm c0 s1 _ ES V1)|]. split; [unfold fwT; rewrite ES; exact FT|].
      split; [exact W'|]. split; [exact H'| exact L'].
    - cbn [fst]. destruct (SW d0 P0 D0 HWS HHS HLBS) as (P' & ES & W' & H' & L').
      split; [exact P'|]. split; [exact (SV_same_strm c0 d0 _ ES V0)|]. split; [unfold fwT; rewrite ES; reflexivity|].
      split; [exact W'|]. split; [exact H'| exact L'].
  Qed.
End Api.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac proj_cbn :=
  cbn [ds_status ds_pending_buf ds_pending_buf_size ds_pending_out ds_pending ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush
       ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift
       ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length
       ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_dyn_ltree_fc ds_dyn_ltree_dl
       ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_l_max_code ds_d_max_code ds_bl_max_code ds_bl_count ds_heap
       ds_heap_len ds_heap_max ds_depth ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len ds_matches ds_insert ds_bi_buf
       ds_bi_valid ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm].

Theorem PATG_init9 : forall g, PATG (dinit9_of g).
Proof.
  intros g. constructor; unfold dmode, dinit9_of, dFg; proj_cbn.
  - right. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
Qed.

