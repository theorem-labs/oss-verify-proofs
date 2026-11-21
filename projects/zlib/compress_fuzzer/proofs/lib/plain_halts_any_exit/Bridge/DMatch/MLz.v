(** * Bridge.DMatch.MLz — group M: the window kit and pairs D18 ([insert_string],
    [update_hash]) and D19 ([clear_hash], [slide_hash]).

    - [m_cfg_facts] / [m_s5_geom]: compress_fuzzer's geometry constants on
      both sides, from [mt_inv] and [geom_rel].
    - [nl_rel] / [nonlz_view]: the five clusters of [dst_rel] that the
      matching code never touches, and the S5 fields they read.  A step that
      changes only LZ fields on both sides keeps [nl_rel] by [m_nl_frame]
      (one [destruct] of the two records, no setter unfolded in a goal).
    - [m_insert_string], [m_slide_hash], [m_clear_hash]: the pairs, stated on
      [lz_rel].

    S5's [insert_string] keeps a [wrap32] in the hash ([MBasic.m_update_hash])
    and writes [wrap16 str] where RT writes [u16 str] (the same function). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.

(* ------------------------------------------------------------------------- *)
(* 1.  Geometry constants                                                    *)
(* ------------------------------------------------------------------------- *)

Record cfg_facts (g : RC.DeflGeom) : Prop := mkCfgFacts {
  cf_w_size : RC.dg_w_size g = 32768;
  cf_w_mask : RC.dg_w_mask g = 32767;
  cf_hash_size : RC.dg_hash_size g = 32768;
  cf_hash_mask : RC.dg_hash_mask g = 32767;
  cf_hash_shift : RC.dg_hash_shift g = 5;
  cf_max_dist : RC.dg_max_dist g = 32506;
  cf_lit_bufsize : RC.dg_lit_bufsize g = 16384;
  cf_sym_end : RC.dg_sym_end g = 49149;
  cf_pbs : RC.dg_pending_buf_size g = 65536;
  cf_strategy : RC.dg_strategy g = 0;
  cf_wrap : RC.dg_wrap g = 1;
  cf_good : RC.dg_good_match g = RC.cfg_good_length (RC.dg_level g);
  cf_lazy : RC.dg_max_lazy_match g = RC.cfg_max_lazy (RC.dg_level g);
  cf_nice : RC.dg_nice_match g = RC.cfg_nice_length (RC.dg_level g);
  cf_chain : RC.dg_max_chain_length g = RC.cfg_max_chain (RC.dg_level g)
}.

Lemma m_cfg_geom : forall level, 0 <= level -> cfg_facts (cf_geom level).
Proof.
  intros level Hl.
  assert (Hz : RC.zdefl_level level = level)
    by (unfold RC.zdefl_level; destruct (Z.eqb_spec level (-1)); lia).
  unfold cf_geom, RC.defl_geom_wrap. constructor; cbn [RC.dg_level RC.dg_good_match RC.dg_max_lazy_match
    RC.dg_nice_match RC.dg_max_chain_length]; try reflexivity.
Qed.

Lemma m_cfg_facts : forall t, mt_inv t -> cfg_facts (RD.d_cfg t).
Proof.
  intros t H. rewrite (mt_cfg t H). apply m_cfg_geom. pose proof (mt_level t H). lia.
Qed.

(** The S5 side of the same constants, through [geom_rel]. *)
Record s5_geom (s : DS.deflate_state) : Prop := mkS5Geom {
  sg_w_size : DS.ds_w_size s = 32768;
  sg_w_mask : DS.ds_w_mask s = 32767;
  sg_hash_size : DS.ds_hash_size s = 32768;
  sg_hash_mask : DS.ds_hash_mask s = 32767;
  sg_hash_shift : DS.ds_hash_shift s = 5;
  sg_lit_bufsize : DS.ds_lit_bufsize s = 16384;
  sg_strategy : DS.ds_strategy s = 0
}.

Lemma m_s5_geom : forall s t, geom_rel s t -> mt_inv t -> s5_geom s.
Proof.
  intros s t Hg Hi. pose proof (m_cfg_facts t Hi) as Hc.
  unfold geom_rel in Hg. cbv zeta in Hg.
  destruct Hg as (_ & Hst & _ & Hws & Hwm & _ & Hhs & Hhm & Hsh & Hlb & _).
  destruct Hc. constructor; congruence.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The clusters the matching code never touches                          *)
(* ------------------------------------------------------------------------- *)

Definition nl_rel (s : DS.deflate_state) (t : RD.DSt) (pre_out pre_in : list Z) : Prop :=
  geom_rel s t /\ bw_rel s (RT.ts_bw (RD.d_ts t)) /\ sym_rel s t /\ tree_rel s t
  /\ strm_rel s t pre_out pre_in.

Lemma m_dst_split : forall s t po pi,
  dst_rel s t po pi <-> lz_rel s t /\ nl_rel s t po pi.
Proof.
  intros s t po pi. unfold dst_rel, nl_rel. split.
  - intros (Hg & Hl & Hb & Hs & Ht & Hm). tauto.
  - intros (Hl & Hg & Hb & Hs & Ht & Hm). tauto.
Qed.

(** Every S5 field [nl_rel] reads. *)
Definition nonlz_view (s : DS.deflate_state) :=
  (DS.ds_status s, DS.ds_pending_buf s, DS.ds_pending_buf_size s, DS.ds_pending_out s,
   DS.ds_pending s, DS.ds_wrap s, DS.ds_last_flush s, DS.ds_w_size s, DS.ds_w_bits s,
   DS.ds_w_mask s, DS.ds_hash_size s, DS.ds_hash_bits s, DS.ds_hash_mask s,
   DS.ds_hash_shift s, DS.ds_max_chain_length s, DS.ds_max_lazy_match s, DS.ds_level s,
   DS.ds_strategy s, DS.ds_good_match s, DS.ds_nice_match s,
   (DS.ds_dyn_ltree_fc s, DS.ds_dyn_ltree_dl s, DS.ds_dyn_dtree_fc s, DS.ds_dyn_dtree_dl s,
    DS.ds_bl_tree_fc s, DS.ds_bl_tree_dl s, DS.ds_l_max_code s, DS.ds_d_max_code s,
    DS.ds_bl_max_code s, DS.ds_bl_count s, DS.ds_heap s, DS.ds_heap_len s, DS.ds_heap_max s,
    DS.ds_depth s),
   DS.ds_lit_bufsize s, DS.ds_sym_next s, DS.ds_sym_end s, DS.ds_opt_len s,
   DS.ds_static_len s, DS.ds_matches s, DS.ds_bi_buf s, DS.ds_bi_valid s, DS.ds_strm s).

Lemma m_nl_frame : forall s s' t l po pi,
  nonlz_view s' = nonlz_view s -> nl_rel s t po pi -> nl_rel s' (RD.setD_ls l t) po pi.
Proof.
  intros s s' t l po pi Hv H.
  destruct s, s'. unfold nonlz_view in Hv. cbn in Hv.
  injection Hv; intros; subst. exact H.
Qed.

(** RT's side of a pure LZ step: [d_ls] replaced, everything else kept. *)
Lemma m_lz_step : forall s s' t l po pi,
  dst_rel s t po pi -> nonlz_view s' = nonlz_view s -> lz_rel s' (RD.setD_ls l t) ->
  dst_rel s' (RD.setD_ls l t) po pi.
Proof.
  intros s s' t l po pi H Hv Hl. apply m_dst_split. split; [exact Hl|].
  apply m_dst_split in H as [_ Hn]. eapply m_nl_frame; eassumption.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  D18: insert_string                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma m_land_wmask : forall x, 0 <= Z.land x 32767 < 32768.
Proof.
  intros x. change 32767 with (Z.ones 15). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

(** The LZ half of [insert_string] at position [str]: the hash, the head
    read, and the two writes agree. *)
Theorem m_insert_string : forall s t str,
  lz_rel s t -> s5_geom s -> cfg_facts (RD.d_cfg t) -> RD.ls_windowsize (RD.d_ls t) = 65536 ->
  0 <= str -> str + 2 < 65536 ->
  snd (SLz.insert_string s str) = fst (RD.insert_string (RD.d_cfg t) str (RD.d_ls t))
  /\ lz_rel (fst (SLz.insert_string s str))
            (RD.setD_ls (snd (RD.insert_string (RD.d_cfg t) str (RD.d_ls t))) t)
  /\ nonlz_view (fst (SLz.insert_string s str)) = nonlz_view s.
Proof.
  intros s t str Hl Hg Hc Hws Hs0 Hs1.
  destruct Hg, Hc.
  unfold lz_rel in Hl. cbv zeta in Hl.
  destruct Hl as (Hlw & Hlp & Hlh & Hrw & Hrp & Hrh & Hwsz & Hih & Hbs & Hml & Hpm & Hma & Hss & Hms
                  & Hla & Hpl & Hin & Hhw).
  rewrite Hws in *.
  unfold SLz.insert_string, RD.insert_string. cbv zeta.
  (* the hash *)
  replace (str + (DS.MIN_MATCH - 1)) with (str + RC.MIN_MATCH - 1)
    by (unfold DS.MIN_MATCH, RC.MIN_MATCH; lia).
  rewrite <- (Hrw (str + RC.MIN_MATCH - 1)) by (unfold RC.MIN_MATCH; lia).
  rewrite (m_update_hash s (RD.d_cfg t)) by congruence. rewrite <- Hih.
  set (h := RD.update_hash (RD.d_cfg t) (DS.ds_ins_h s) (arr_get (DS.ds_window s) (str + RC.MIN_MATCH - 1))).
  assert (Hh : 0 <= h < 32768) by (apply m_update_hash_range; exact cf_hash_mask0).
  rewrite ds_head__set_ins_h.
  assert (Hmh : arr_get (DS.ds_head s) h = RD.ls_head (RD.d_ls t) h) by (apply Hrh; lia).
  cbn [fst snd]. split; [exact Hmh|].
  split.
  - unfold lz_rel. cbv zeta.
    autorewrite with s5f_head s5f_prev s5f_ins_h.
    cbn [RD.d_ls RD.setD_ls RD.setL_head RD.setL_prev RD.setL_insh RD.ls_window RD.ls_prev RD.ls_head RD.ls_insh
         RD.ls_blockstart RD.ls_matchlen RD.ls_prevmatch RD.ls_matchavail RD.ls_strstart RD.ls_matchstart
         RD.ls_lookahead RD.ls_prevlen RD.ls_insert RD.ls_highwater RD.ls_windowsize].
    rewrite Hws.
    rewrite sg_w_mask0, cf_w_mask0, sg_hash_size0 in *.
    pose proof (m_land_wmask str) as Hpi.
    split; [exact Hlw|]. split; [rewrite arr_len_set; exact Hlp|]. split; [rewrite arr_len_set; exact Hlh|].
    split; [exact Hrw|].
    split.
    { rewrite sg_w_size0 in *. rewrite Hmh. apply arr_rel_set; [exact Hrp|]. intros _. rewrite Hlp. exact Hpi. }
    split.
    { rewrite m_wrap16_u16. apply arr_rel_set; [exact Hrh|]. intros _. rewrite Hlh. exact Hh. }
    split; [exact Hwsz|]. split; [reflexivity|].
    split; [exact Hbs|]. split; [exact Hml|]. split; [exact Hpm|]. split; [exact Hma|]. split; [exact Hss|].
    split; [exact Hms|]. split; [exact Hla|]. split; [exact Hpl|]. split; [exact Hin|exact Hhw].
  - reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  D19: slide_hash and clear_hash                                        *)
(* ------------------------------------------------------------------------- *)

(** S5's write loop over [[0, n)], top down, is RT's pointwise update. *)
Lemma m_slide_loop : forall f a n w,
  1 <= n <= Z.of_nat f -> n <= arr_len a ->
  arr_len (SLz.slide_hash_loop f a n w) = arr_len a
  /\ forall i, arr_get (SLz.slide_hash_loop f a n w) i =
       if (0 <=? i) && (i <? n)
       then wrap16 (if w <=? arr_get a i then arr_get a i - w else DS.NIL) else arr_get a i.
Proof.
  induction f as [|f IH]; intros a n w Hn Hlen; [lia|].
  cbn [SLz.slide_hash_loop]. cbv zeta.
  set (v := wrap16 (if w <=? arr_get a (n - 1) then arr_get a (n - 1) - w else DS.NIL)).
  assert (Hp : 0 <= n - 1 < arr_len a) by lia.
  destruct (Z.eqb_spec (n - 1) 0) as [E|E]; cbn [negb].
  - split; [apply arr_len_set|]. intros i.
    rewrite arr_get_set. unfold arr_inb.
    destruct (Z.eqb_spec (n - 1) i); destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i n);
      destruct (Z.ltb_spec (n - 1) (arr_len a)); destruct (Z.leb_spec 0 (n - 1)); cbn [andb]; try lia;
      try reflexivity; subst i; reflexivity.
  - destruct (IH (arr_set a (n - 1) v) (n - 1) w ltac:(lia) ltac:(rewrite arr_len_set; lia)) as [IHl IHg].
    split; [rewrite IHl; apply arr_len_set|]. intros i. rewrite IHg.
    rewrite !arr_get_set. unfold arr_inb.
    destruct (Z.eqb_spec (n - 1) i); destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (n - 1));
      destruct (Z.ltb_spec i n); destruct (Z.ltb_spec (n - 1) (arr_len a)); destruct (Z.leb_spec 0 (n - 1));
      cbn [andb]; try lia; try reflexivity; subst i; reflexivity.
Qed.

Lemma m_slide_rel : forall f a z n w,
  arr_rel a z 0 n -> 1 <= n <= Z.of_nat f -> n <= arr_len a ->
  arr_rel (SLz.slide_hash_loop f a n w) (RD.slide_range n w z) 0 n
  /\ arr_len (SLz.slide_hash_loop f a n w) = arr_len a.
Proof.
  intros f a z n w Hr Hn Hl. destruct (m_slide_loop f a n w Hn Hl) as [HL HG].
  split; [|exact HL]. intros i Hi. rewrite HG. unfold RD.slide_range, RD.slide_one.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i n); cbn [andb]; try lia.
  rewrite (Hr i Hi), m_wrap16_u16. reflexivity.
Qed.

(** [slide_hash], LZ half. *)
Theorem m_slide_hash : forall s t,
  lz_rel s t -> s5_geom s -> cfg_facts (RD.d_cfg t) ->
  lz_rel (SLz.slide_hash s) (RD.setD_ls (RD.slide_hash (RD.d_cfg t) (RD.d_ls t)) t)
  /\ nonlz_view (SLz.slide_hash s) = nonlz_view s.
Proof.
  intros s t Hl Hg Hc. destruct Hg, Hc.
  unfold lz_rel in Hl. cbv zeta in Hl.
  destruct Hl as (Hlw & Hlp & Hlh & Hrw & Hrp & Hrh & Hrest).
  unfold SLz.slide_hash, RD.slide_hash. cbv zeta.
  split; [|reflexivity].
  unfold lz_rel. cbv zeta.
  autorewrite with s5f_prev s5f_head.
  cbn [RD.d_ls RD.setD_ls RD.setL_head RD.setL_prev RD.ls_window RD.ls_prev RD.ls_head RD.ls_insh
       RD.ls_blockstart RD.ls_matchlen RD.ls_prevmatch RD.ls_matchavail RD.ls_strstart RD.ls_matchstart
       RD.ls_lookahead RD.ls_prevlen RD.ls_insert RD.ls_highwater RD.ls_windowsize].
  rewrite sg_w_size0, sg_hash_size0 in *. rewrite cf_w_size0, cf_hash_size0.
  destruct (m_slide_rel (Z.to_nat 32768) (DS.ds_head s) (RD.ls_head (RD.d_ls t)) 32768 32768 Hrh
              ltac:(lia) ltac:(lia)) as [Hh1 Hh2].
  destruct (m_slide_rel (Z.to_nat 32768) (DS.ds_prev s) (RD.ls_prev (RD.d_ls t)) 32768 32768 Hrp
              ltac:(lia) ltac:(lia)) as [Hp1 Hp2].
  split; [exact Hlw|]. split; [rewrite Hp2; exact Hlp|]. split; [rewrite Hh2; exact Hlh|].
  split; [exact Hrw|]. split; [exact Hp1|]. split; [exact Hh1|]. exact Hrest.
Qed.

(** [clear_hash] (CLEAR_HASH), LZ half. *)
Theorem m_clear_hash : forall s t,
  lz_rel s t -> s5_geom s -> cfg_facts (RD.d_cfg t) ->
  lz_rel (SLz.clear_hash s) (RD.setD_ls (RD.clear_hash (RD.d_cfg t) (RD.d_ls t)) t)
  /\ nonlz_view (SLz.clear_hash s) = nonlz_view s.
Proof.
  intros s t Hl Hg Hc. destruct Hg, Hc.
  unfold lz_rel in Hl. cbv zeta in Hl.
  destruct Hl as (Hlw & Hlp & Hlh & Hrw & Hrp & Hrh & Hrest).
  unfold SLz.clear_hash, RD.clear_hash.
  split; [|reflexivity].
  unfold lz_rel. cbv zeta.
  autorewrite with s5f_head.
  cbn [RD.d_ls RD.setD_ls RD.setL_head RD.ls_window RD.ls_prev RD.ls_head RD.ls_insh
       RD.ls_blockstart RD.ls_matchlen RD.ls_prevmatch RD.ls_matchavail RD.ls_strstart RD.ls_matchstart
       RD.ls_lookahead RD.ls_prevlen RD.ls_insert RD.ls_highwater RD.ls_windowsize].
  rewrite sg_hash_size0 in *. rewrite cf_hash_size0.
  split; [exact Hlw|]. split; [exact Hlp|].
  split; [rewrite arr_len_fill, arr_len_set; exact Hlh|].
  split; [exact Hrw|]. split; [exact Hrp|].
  split; [|exact Hrest].
  intros i Hi. rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_set, Hlh.
  rewrite arr_get_set. unfold arr_inb. rewrite Hlh.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (0 + Z.max 0 (32768 - 1)));
    destruct (Z.ltb_spec i 32768); destruct (Z.eqb_spec (32768 - 1) i); cbn [andb]; try lia;
    unfold RD.NIL, DS.NIL; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 5.  What group D's flush needs of the window                              *)
(* ------------------------------------------------------------------------- *)

Theorem m_fb_lz : forall t, mt_inv t -> DEmitDefs.fb_lz t.
Proof.
  intros t H. pose proof (m_cfg_facts t H) as Hc.
  destruct H as [Hlev Hcfg Hwr Hrb Hms Hfa Hsl Hwin Hma Hml Hbs Hhw Hslid Hinl].
  destruct Hms as [Hch Hws Hmd Hwz Hstr Hlk Hrm Hins].
  destruct Hslid as (slid & Hs0 & Hdone & Hbs0 & _).
  assert (0 <= Chunk.zlen (RD.zs_in (RD.d_strm t))) by (unfold Chunk.zlen; lia).
  unfold DEmitDefs.fb_lz. rewrite (cf_w_size _ Hc) in *. rewrite Hwz.
  split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
  split; [mpow; lia|]. split; [mpow; lia|].
  intros i Hi. apply Hwin. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 6.  Projections of lz_rel                                                 *)
(* ------------------------------------------------------------------------- *)

Section LzProj.
  Variables (s : DS.deflate_state) (t : RD.DSt).
  Hypothesis H : lz_rel s t.
  Let l := RD.d_ls t.
  Lemma lzr_wlen : arr_len (DS.ds_window s) = RD.ls_windowsize l.
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_win : arr_rel (DS.ds_window s) (RD.ls_window l) 0 (RD.ls_windowsize l).
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_wsz : DS.ds_window_size s = RD.ls_windowsize l.
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_ih : DS.ds_ins_h s = RD.ls_insh l.
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_bs : DS.ds_block_start s = RD.ls_blockstart l.
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_ml : DS.ds_match_length s = RD.ls_matchlen l.
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_pm : DS.ds_prev_match s = wrap32 (RD.ls_prevmatch l).
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_ma : DS.ds_match_available s = RD.ls_matchavail l.
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_ss : DS.ds_strstart s = RD.ls_strstart l.
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_ms : DS.ds_match_start s = wrap32 (RD.ls_matchstart l).
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_la : DS.ds_lookahead s = RD.ls_lookahead l.
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_pl : DS.ds_prev_length s = RD.ls_prevlen l.
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_ins : DS.ds_insert s = RD.ls_insert l.
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_hw : DS.ds_high_water s = RD.ls_highwater l.
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_prev : arr_rel (DS.ds_prev s) (RD.ls_prev l) 0 (DS.ds_w_size s).
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
  Lemma lzr_head : arr_rel (DS.ds_head s) (RD.ls_head l) 0 (DS.ds_hash_size s).
  Proof. unfold lz_rel in H. cbv zeta in H. tauto. Qed.
End LzProj.

(* ------------------------------------------------------------------------- *)
(* 7.  One setter at a time                                                  *)
(* ------------------------------------------------------------------------- *)

(** Every LZ step is a chain of single-field updates on both sides.  These
    lemmas carry [lz_rel] across one update each, with one setter database
    per goal (rewriting a whole chain at once with all its databases took
    32 s on a four-setter slide).  RT states are written [setD_ls l t] for a
    fixed frame [t]: [lz_rel] reads only [d_ls]. *)

Lemma rt_setD_ls_ls : forall a b t, RD.setD_ls a (RD.setD_ls b t) = RD.setD_ls a t.
Proof. intros a b t. destruct t. reflexivity. Qed.

Lemma rt_setD_ls_eta : forall t, RD.setD_ls (RD.d_ls t) t = t.
Proof. intros t. destruct t. reflexivity. Qed.

Ltac lz_one db :=
  match goal with H : lz_rel _ _ |- _ =>
    unfold lz_rel in H |- *; cbv zeta in H |- *;
    autorewrite with db;
    cbn [RD.d_ls RD.setD_ls RD.setL_window RD.setL_prev RD.setL_head RD.setL_insh
         RD.setL_blockstart RD.setL_matchlen RD.setL_prevmatch RD.setL_matchavail RD.setL_strstart
         RD.setL_matchstart RD.setL_lookahead RD.setL_prevlen RD.setL_insert RD.setL_highwater
         RD.ls_window RD.ls_prev RD.ls_head RD.ls_insh RD.ls_blockstart RD.ls_matchlen RD.ls_prevmatch
         RD.ls_matchavail RD.ls_strstart RD.ls_matchstart RD.ls_lookahead RD.ls_prevlen RD.ls_insert
         RD.ls_highwater RD.ls_windowsize] in H |- *;
    destruct H as (Hlw & Hlp & Hlh & Hrw & Hrp & Hrh & Hwsz & Hih & Hbs & Hml & Hpm & Hma & Hss & Hms
                   & Hla & Hpl & Hin & Hhw)
  end.

Lemma lz_set_window : forall s t l w z,
  lz_rel s (RD.setD_ls l t) -> arr_len w = arr_len (DS.ds_window s) ->
  arr_rel w z 0 (RD.ls_windowsize l) ->
  lz_rel (DS.set_window s w) (RD.setD_ls (RD.setL_window z l) t).
Proof. intros s t l w z H Hw Hr. lz_one s5f_window. rewrite Hw. repeat split; assumption. Qed.

Lemma lz_set_prev : forall s t l w z,
  lz_rel s (RD.setD_ls l t) -> arr_len w = arr_len (DS.ds_prev s) -> arr_rel w z 0 (DS.ds_w_size s) ->
  lz_rel (DS.set_prev s w) (RD.setD_ls (RD.setL_prev z l) t).
Proof. intros s t l w z H Hw Hr. lz_one s5f_prev. rewrite Hw. repeat split; assumption. Qed.

Lemma lz_set_head : forall s t l w z,
  lz_rel s (RD.setD_ls l t) -> arr_len w = arr_len (DS.ds_head s) -> arr_rel w z 0 (DS.ds_hash_size s) ->
  lz_rel (DS.set_head s w) (RD.setD_ls (RD.setL_head z l) t).
Proof. intros s t l w z H Hw Hr. lz_one s5f_head. rewrite Hw. repeat split; assumption. Qed.

Lemma lz_set_ins_h : forall s t l v5 v,
  lz_rel s (RD.setD_ls l t) -> v5 = v -> lz_rel (DS.set_ins_h s v5) (RD.setD_ls (RD.setL_insh v l) t).
Proof. intros. lz_one s5f_ins_h. repeat split; assumption. Qed.

Lemma lz_set_block_start : forall s t l v5 v,
  lz_rel s (RD.setD_ls l t) -> v5 = v -> lz_rel (DS.set_block_start s v5) (RD.setD_ls (RD.setL_blockstart v l) t).
Proof. intros. lz_one s5f_block_start. repeat split; assumption. Qed.

Lemma lz_set_match_length : forall s t l v5 v,
  lz_rel s (RD.setD_ls l t) -> v5 = v -> lz_rel (DS.set_match_length s v5) (RD.setD_ls (RD.setL_matchlen v l) t).
Proof. intros. lz_one s5f_match_length. repeat split; assumption. Qed.

Lemma lz_set_prev_match : forall s t l v5 v,
  lz_rel s (RD.setD_ls l t) -> v5 = wrap32 v ->
  lz_rel (DS.set_prev_match s v5) (RD.setD_ls (RD.setL_prevmatch v l) t).
Proof. intros. lz_one s5f_prev_match. repeat split; assumption. Qed.

Lemma lz_set_match_available : forall s t l v5 v,
  lz_rel s (RD.setD_ls l t) -> v5 = v ->
  lz_rel (DS.set_match_available s v5) (RD.setD_ls (RD.setL_matchavail v l) t).
Proof. intros. lz_one s5f_match_available. repeat split; assumption. Qed.

Lemma lz_set_strstart : forall s t l v5 v,
  lz_rel s (RD.setD_ls l t) -> v5 = v -> lz_rel (DS.set_strstart s v5) (RD.setD_ls (RD.setL_strstart v l) t).
Proof. intros. lz_one s5f_strstart. repeat split; assumption. Qed.

Lemma lz_set_match_start : forall s t l v5 v,
  lz_rel s (RD.setD_ls l t) -> v5 = wrap32 v ->
  lz_rel (DS.set_match_start s v5) (RD.setD_ls (RD.setL_matchstart v l) t).
Proof. intros. lz_one s5f_match_start. repeat split; assumption. Qed.

Lemma lz_set_lookahead : forall s t l v5 v,
  lz_rel s (RD.setD_ls l t) -> v5 = v -> lz_rel (DS.set_lookahead s v5) (RD.setD_ls (RD.setL_lookahead v l) t).
Proof. intros. lz_one s5f_lookahead. repeat split; assumption. Qed.

Lemma lz_set_prev_length : forall s t l v5 v,
  lz_rel s (RD.setD_ls l t) -> v5 = v -> lz_rel (DS.set_prev_length s v5) (RD.setD_ls (RD.setL_prevlen v l) t).
Proof. intros. lz_one s5f_prev_length. repeat split; assumption. Qed.

Lemma lz_set_insert : forall s t l v5 v,
  lz_rel s (RD.setD_ls l t) -> v5 = v -> lz_rel (DS.set_insert s v5) (RD.setD_ls (RD.setL_insert v l) t).
Proof. intros. lz_one s5f_insert. repeat split; assumption. Qed.

Lemma lz_set_high_water : forall s t l v5 v,
  lz_rel s (RD.setD_ls l t) -> v5 = v -> lz_rel (DS.set_high_water s v5) (RD.setD_ls (RD.setL_highwater v l) t).
Proof. intros. lz_one s5f_high_water. repeat split; assumption. Qed.
