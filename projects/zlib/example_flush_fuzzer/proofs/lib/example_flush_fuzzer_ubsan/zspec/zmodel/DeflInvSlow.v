(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvHash DeflateInvKeep OverlayFBS DeflRoom.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel SendModel DeflFastModel DeflSlowModel TreesTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflSlowOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw DeflInvFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac dsr := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd].
Tactic Notation "dsr" "in" hyp(H) := cbn [ds_status ds_pending_buf_size ds_pending_out ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_lit_bufsize ds_sym_next ds_sym_end ds_matches ds_insert ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm ds_pending ds_l_max_code ds_d_max_code ds_bl_max_code ds_heap_len ds_heap_max ds_opt_len ds_static_len ds_bi_buf ds_bi_valid ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_status set_pending_buf_size set_pending_out set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_lit_bufsize set_sym_next set_sym_end set_matches set_insert set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm set_pending set_l_max_code set_d_max_code set_bl_max_code set_heap_len set_heap_max set_opt_len set_static_len set_bi_buf set_bi_valid set_pending_buf set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_bl_count set_heap set_depth cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler fst snd] in H.

Ltac drop_impl := repeat match goal with H : _ -> _ |- _ => clear H end.


Lemma dist1_mod16 : forall a, 1 <= wrap32 a <= 32768 -> (a - 1) mod 65536 = wrap32 a - 1.
Proof.
  intros a H. rewrite wrap32_mod in *.
  pose proof (Z_div_mod_eq_full a (2 ^ 32)) as E.
  set (q := a / 2 ^ 32) in *. set (r := a mod 2 ^ 32) in *.
  replace (a - 1) with ((r - 1) + (q * 65536) * 65536) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma siloop_ok_S : forall k s mi, siloop_ok (S k) s mi = (lzw s /\ siloop_ok k (sistep s mi) mi).
Proof. reflexivity. Qed.

Lemma set_ma_str_comm : forall s a v, set_strstart (set_match_available s a) v = set_match_available (set_strstart s v) a.
Proof. intros s a v. destruct s; reflexivity. Qed.

Section SLOW.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.

  Let DRUN rm hb fz := drunR rm hb fz ws hs PBL ILEN OCAP tot0.
  Let DPOST := dpost ws hs PBL ILEN OCAP tot0.
  Local Notation LZPOST := (LZPOST ws hs PBL ILEN OCAP tot0).
  Local Notation BPOST := (BPOST ws hs PBL ILEN OCAP tot0).

  Let KML : MIN_LOOKAHEAD = 262 := eq_refl.
  Let KMM : MIN_MATCH = 3 := eq_refl.
  Let KXM : MAX_MATCH = 258 := eq_refl.


  Lemma snone_run : forall hb s, 0 <= hb <= 1 -> DRUN 3 hb false s -> 1 <= ds_lookahead s -> ds_match_available s = 0 ->
    4 <= ds_level s -> lz_strat s ->
    (MIN_MATCH <= ds_match_length s -> 1 <= ds_strstart s - ds_match_start s <= ds_w_size s - MIN_LOOKAHEAD /\ ds_match_length s <= ds_lookahead s) ->
    snone_ok s
    /\ let s' := set_lookahead (set_strstart (set_match_available s 1) (ds_strstart s + 1)) (ds_lookahead s - 1) in
       DRUN 3 0 true s' /\ ds_lookahead s' = ds_lookahead s - 1 /\ ds_strstart s' = ds_strstart s + 1
       /\ ds_strm s' = ds_strm s /\ ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s.
  Proof.
    intros hb s Hhb D Hlook Hma Hlv Hst SF. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    split; [split; [exact (dinv_lzw 3 hb false s ltac:(lia) C I) | exact Hlook]|].
    cbv zeta. rewrite set_ma_str_comm.
    pose proof (di_syms _ _ _ _ I) as (syms & DS & COV). specialize (COV Slz). rewrite Hma in COV.
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_ml _ _ _ _ I) as Iml.
    assert (I2 : dinvR 3 0 true (set_lookahead (set_match_available (set_strstart s (ds_strstart s + 1)) 1) (ds_lookahead s - 1))).
    { pose proof I as [T Istr' Ilook Isl' Iins Ibs Ibs0 Ihw Iih Ims Ipm Iml' Ipl Ima Ima1 Imt Ifast Ifastpl Islow Islow1 Ihash Isyms Iroom Ibv Ibb Ipend Ipout Ipop Ipo0 Ipobv Ilf Ilive Iinit Igz Ineg Ilk0 Isn0 Iinw Ifl Imas Ips].
      constructor; unfold lz_strat in *; dsr; try assumption; try (solve [auto with cty]).
      all: try (intros L; destruct (Ihash L) as [Ins HC]; exists Ins; dsr; apply (hc_inv_str_le _ _ _ _ _ _ _ HC); clear -Hhb; lia).
      all: try (exists syms; split; [eapply dsyms_keep; [exact DS | dsr; reflexivity ..] | intros _; clear -COV; lia]).
      all: try (intros _ _ _ M; destruct (SF M) as [X Y]; rewrite Z.add_simpl_r, wrap32_id by (clear -X Sw KML; lia); clear -X Y Istr KML; lia).
      all: intros; drop_impl; unfold BUSY_STATE, FINISH_STATE, INIT_STATE in *.
      all: try (split; [clear -Hlv; lia | exact Hst]).
      all: clear T Isyms DS D C CL; lia. }
    assert (C2 : dcfg (set_lookahead (set_match_available (set_strstart s (ds_strstart s + 1)) 1) (ds_lookahead s - 1))).
    { apply dcfg_set_lookahead, dcfg_set_match_available, dcfg_set_strstart. exact C. }
    split; [| dsr; repeat split; reflexivity].
    eapply drun_relift; [exact D | exact I2 | exact C2 | dsr; reflexivity ..].
  Qed.


  Record sif (s s' : deflate_state) : Prop := MkSIF {
    if_lzf : lzf s s';
    if_look : ds_lookahead s' = ds_lookahead s;
    if_ml : ds_match_length s' = ds_match_length s;
    if_ms : ds_match_start s' = ds_match_start s;
    if_pm : ds_prev_match s' = ds_prev_match s;
    if_sn : ds_sym_next s' = ds_sym_next s;
    if_se : ds_sym_end s' = ds_sym_end s }.
  Lemma sif_trans : forall a b c, sif a b -> sif b c -> sif a c.
  Proof. intros a b c [A1 A2 A3 A4 A5 A6 A7] [B1 B2 B3 B4 B5 B6 B7]; constructor; [exact (lzf_trans _ _ _ A1 B1) | congruence ..]. Qed.

  Lemma sins_run : forall rm hb s syms mi, 0 <= rm -> 0 <= hb <= 1 -> DRUN rm hb false s ->
    1 <= ds_prev_length s -> mi + MIN_MATCH <= 2 * ds_w_size s ->
    ds_strstart s + 1 + ds_lookahead s <= 2 * ds_w_size s ->
    4 <= ds_level s ->
    dsyms syms s -> ds_strstart s + 1 - ds_block_start s <= zcov syms + ds_match_available s ->
    lzw s
    /\ let s' := sistep s mi in
       DRUN rm 1 false s' /\ sif s s' /\ dsyms syms s'
       /\ ds_strstart s' = ds_strstart s + 1 /\ ds_prev_length s' = ds_prev_length s - 1.
  Proof.
    intros rm hb s syms mi Hrm Hhb D Hpl Hmi Hsl Hlv DS COV. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    split; [exact (dinv_lzw _ _ _ _ Hrm C I)|].
    unfold sistep. cbv zeta.
    set (s1 := set_strstart s (ds_strstart s + 1)).
    assert (I1 : dinvR rm 0 false s1).
    { subst s1. apply (dinv_set_strstart rm hb false 0 s); try exact I; try lia.
      all: try (intros X; discriminate X). intros _. exists syms. split; [exact DS | lia]. }
    assert (C1 : dcfg s1) by (subst s1; apply dcfg_set_strstart; exact C).
    replace (ds_strstart s1) with (ds_strstart s + 1) by (subst s1; dsr; reflexivity).
    destruct (Z.leb_spec (ds_strstart s + 1) mi) as [LE|GT].
    -
      pose proof (dinv_insert_string_gen rm false s1 C1 I1 ltac:(subst s1; dsr; lia)) as INS.
      pose proof (dcfg_insert_string s1 (ds_strstart s1) C1) as C2.
      pose proof (insert_string_fields s1 (ds_strstart s1)) as IF.
      replace (ds_strstart s1) with (ds_strstart s + 1) in INS, C2, IF by (subst s1; dsr; reflexivity).
      destruct (insert_string s1 (ds_strstart s + 1)) as [s2 hh]. cbn [fst snd] in *.
      destruct INS as (I2 & _ & K2 & Q1 & Q2 & Q3 & _). destruct IF as (_ & _ & _ & _ & _ & _ & _ & _ & Eol & Esl & Epb & Elt & Edt & Ebt).
      assert (F : forall (f : deflate_state -> Z), (forall b a, kproj a = kproj b -> f a = f b) ->
                 (forall x a, f (set_head x a) = f x) -> (forall x a, f (set_prev x a) = f x) -> (forall x a, f (set_ins_h x a) = f x) -> f s2 = f s1).
      { intros f E1 E2 E3 E4. rewrite <- (E1 _ _ K2), E2, E3, E4. reflexivity. }
      pose proof (F ds_strstart kp_strstart strstart_set_head strstart_set_prev strstart_set_ins_h) as Fstr.
      pose proof (F ds_lookahead kp_lookahead lookahead_set_head lookahead_set_prev lookahead_set_ins_h) as Flook.
      pose proof (F ds_match_length kp_match_length match_length_set_head match_length_set_prev match_length_set_ins_h) as Fml.
      pose proof (F ds_match_start kp_match_start match_start_set_head match_start_set_prev match_start_set_ins_h) as Fms.
      pose proof (F ds_prev_match kp_prev_match prev_match_set_head prev_match_set_prev prev_match_set_ins_h) as Fpm.
      pose proof (F ds_prev_length kp_prev_length prev_length_set_head prev_length_set_prev prev_length_set_ins_h) as Fpl.
      pose proof (F ds_w_size kp_w_size w_size_set_head w_size_set_prev w_size_set_ins_h) as Fws.
      pose proof (F ds_hash_size kp_hash_size hash_size_set_head hash_size_set_prev hash_size_set_ins_h) as Fhs.
      pose proof (F ds_lit_bufsize kp_lit_bufsize lit_bufsize_set_head lit_bufsize_set_prev lit_bufsize_set_ins_h) as Flb.
      pose proof (F ds_status kp_status status_set_head status_set_prev status_set_ins_h) as Fst.
      pose proof (F ds_wrap kp_wrap wrap_set_head wrap_set_prev wrap_set_ins_h) as Fwr.
      pose proof (F ds_level kp_level level_set_head level_set_prev level_set_ins_h) as Flv.
      pose proof (F ds_strategy kp_strategy strategy_set_head strategy_set_prev strategy_set_ins_h) as Fsg.
      pose proof (F ds_pending_out kp_pending_out pending_out_set_head pending_out_set_prev pending_out_set_ins_h) as Fpo.
      pose proof (F ds_max_lazy_match kp_max_lazy_match max_lazy_match_set_head max_lazy_match_set_prev max_lazy_match_set_ins_h) as Flz.
      pose proof (F ds_block_start kp_block_start block_start_set_head block_start_set_prev block_start_set_ins_h) as Fbs.
      pose proof (F ds_sym_next kp_sym_next sym_next_set_head sym_next_set_prev sym_next_set_ins_h) as Fsn.
      pose proof (F ds_sym_end kp_sym_end sym_end_set_head sym_end_set_prev sym_end_set_ins_h) as Fse.
      pose proof (F ds_match_available kp_match_available match_available_set_head match_available_set_prev match_available_set_ins_h) as Fma.
      assert (Fsm : ds_strm s2 = ds_strm s1).
      { pose proof (kp_strm _ _ K2) as X. rewrite strm_set_head, strm_set_prev, strm_set_ins_h in X. exact X. }
      assert (I3 : dinvR rm 1 false (set_prev_length s2 (ds_prev_length s2 - 1))).
      { apply dinv_set_prev_length; [exact I2 | rewrite Fpl; subst s1; dsr; pose proof (di_pl _ _ _ _ I); lia | rewrite Flv; subst s1; dsr; intros A; lia]. }
      remember (set_prev_length s2 (ds_prev_length s2 - 1)) as s3 eqn:Es3.
      assert (SF : sif s s3).
      { subst s3. constructor; [constructor|..]; dsr; rewrite ?Fsm, ?Fws, ?Fhs, ?Flb, ?Fst, ?Fwr, ?Flv, ?Fsg, ?Fpo, ?Flz, ?Fbs, ?Fma, ?Q2, ?Q3, ?Flook, ?Fml, ?Fms, ?Fpm, ?Fsn, ?Fse, ?Q1; subst s1; dsr; reflexivity. }
      assert (C3 : dcfg s3) by (subst s3; apply dcfg_set_prev_length; exact C2).
      split; [exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I3 C3 (if_lzf _ _ SF))|].
      split; [exact SF|].
      split; [subst s3; eapply dsyms_keep; [exact DS | dsr ..]; rewrite ?Fsn, ?Epb, ?Flb, ?Fws, ?Elt, ?Edt, ?Ebt, ?Eol, ?Esl; subst s1; dsr; reflexivity|].
      subst s3. dsr. rewrite Fstr, Fpl. subst s1. dsr. split; reflexivity.
    -
      assert (I3 : dinvR rm 1 false (set_prev_length s1 (ds_prev_length s1 - 1))).
      { apply dinv_set_prev_length; [apply dinv_hb01; exact I1 | subst s1; dsr; pose proof (di_pl _ _ _ _ I); lia | subst s1; dsr; intros A; lia]. }
      assert (C3 : dcfg (set_prev_length s1 (ds_prev_length s1 - 1))) by (apply dcfg_set_prev_length; exact C1).
      assert (SF : sif s (set_prev_length s1 (ds_prev_length s1 - 1))).
      { subst s1. constructor; [constructor|..]; dsr; reflexivity. }
      split; [exact (drun_lzf _ _ _ _ _ _ _ _ _ _ _ _ _ _ D I3 C3 (if_lzf _ _ SF))|].
      split; [exact SF|].
      split; [subst s1; eapply dsyms_keep; [exact DS | dsr; reflexivity ..]|].
      subst s1. dsr. split; reflexivity.
  Qed.

  Lemma slow_insert_run : forall n rm hb s syms mi, 0 <= rm -> 0 <= hb <= 1 -> DRUN rm hb false s ->
    Z.of_nat n = ds_prev_length s -> 1 <= ds_prev_length s -> mi + MIN_MATCH <= 2 * ds_w_size s ->
    ds_strstart s + ds_prev_length s + ds_lookahead s <= 2 * ds_w_size s ->
    4 <= ds_level s ->
    dsyms syms s -> ds_strstart s + ds_prev_length s - ds_block_start s <= zcov syms + ds_match_available s ->
    siloop_ok n s mi
    /\ let s' := deflate_slow_insert n s mi in
       DRUN rm 1 false s' /\ sif s s' /\ dsyms syms s'
       /\ ds_strstart s' = ds_strstart s + ds_prev_length s /\ ds_prev_length s' = 0.
  Proof.
    induction n as [|n IH]; intros rm hb s syms mi Hrm Hhb D Hn Hpl Hmi Hsl Hlv DS COV.
    { exfalso. cbn in Hn. lia. }
    destruct (sins_run rm hb s syms mi Hrm Hhb D Hpl Hmi ltac:(lia) Hlv DS ltac:(lia)) as (LZ & D1 & SF1 & DS1 & S1 & P1).
    rewrite deflate_slow_insert_step, siloop_ok_S. cbv zeta.
    remember (sistep s mi) as s1 eqn:Es1.
    destruct (Z.eqb_spec (ds_prev_length s1) 0) as [Z0|Z0]; cbn [negb].
    - split; [split; [exact LZ | destruct n; [exact Logic.I | rewrite Nat2Z.inj_succ in Hn; exfalso; lia]]|].
      split; [exact D1|]. split; [exact SF1|]. split; [exact DS1|]. rewrite S1. split; [lia | exact Z0].
    - pose proof SF1 as [[F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15] G2 G3 G4 G5 G6 G7].
      destruct (IH rm 1 s1 syms mi Hrm ltac:(lia) D1 ltac:(rewrite Nat2Z.inj_succ in Hn; lia) ltac:(lia) ltac:(rewrite F4; lia) ltac:(rewrite S1, P1, G2, F4; lia)
                  ltac:(rewrite F9; exact Hlv) DS1 ltac:(rewrite S1, P1, F14, F15; lia)) as (IL & D2 & SF2 & DS2 & S2 & P2).
      split; [split; [exact LZ | exact IL]|].
      split; [exact D2|]. split; [exact (sif_trans _ _ _ SF1 SF2)|]. split; [exact DS2|]. rewrite S2, S1, P1. split; [lia | exact P2].
  Qed.

End SLOW.
