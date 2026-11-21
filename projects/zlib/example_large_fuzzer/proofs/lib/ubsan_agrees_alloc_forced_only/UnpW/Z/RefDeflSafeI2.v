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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KV (s : deflate_state) :=
  (ds_w_size s, ds_hash_size s, ds_lit_bufsize s,
   (ds_self_blk s, ds_window_blk s, ds_prev_blk s, ds_head_blk s, ds_pending_buf_blk s)).

Lemma KV_fields : forall s s', KV s' = KV s ->
  ds_w_size s' = ds_w_size s /\ ds_hash_size s' = ds_hash_size s /\ ds_lit_bufsize s' = ds_lit_bufsize s
  /\ (ds_self_blk s', ds_window_blk s', ds_prev_blk s', ds_head_blk s', ds_pending_buf_blk s')
     = (ds_self_blk s, ds_window_blk s, ds_prev_blk s, ds_head_blk s, ds_pending_buf_blk s).
Proof.
  intros s s' E. unfold KV in E.
  apply pair_equal_spec in E; destruct E as [E E4]. apply pair_equal_spec in E; destruct E as [E E3].
  apply pair_equal_spec in E; destruct E as [E1 E2]. repeat split; assumption.
Qed.

Lemma KV_set_last_flush : forall s v, KV (set_last_flush s v) = KV s. Proof. reflexivity. Qed.

Lemma KV_err_return : forall s e, KV (fst (err_return s e)) = KV s. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OUTLE (a b : deflate_state) : Prop := exists l, cs_out_rev (ds_strm b) = l ++ cs_out_rev (ds_strm a).
Lemma OUTLE_refl : forall a, OUTLE a a. Proof. intros a. exists nil. reflexivity. Qed.
Lemma OUTLE_trans : forall a b c, OUTLE a b -> OUTLE b c -> OUTLE a c.
Proof. intros a b c [l1 H1] [l2 H2]. exists (l2 ++ l1). rewrite H2, H1, app_assoc. reflexivity. Qed.
Lemma OUTLE_strm : forall a b, ds_strm b = ds_strm a -> OUTLE a b.
Proof. intros a b E. exists nil. rewrite E. reflexivity. Qed.
Lemma OUTLE_out : forall a b, cs_out_rev (ds_strm b) = cs_out_rev (ds_strm a) -> OUTLE a b.
Proof. intros a b E. exists nil. rewrite E. reflexivity. Qed.
Lemma OUTLE_emit : forall a b l, cs_out_rev (ds_strm b) = rev_append l (cs_out_rev (ds_strm a)) -> OUTLE a b.
Proof. intros a b l E. exists (rev l). rewrite E, rev_append_rev. reflexivity. Qed.
Lemma OUTLE_len : forall a b, OUTLE a b -> (length (cs_out_rev (ds_strm a)) <= length (cs_out_rev (ds_strm b)))%nat.
Proof. intros a b [l E]. rewrite E, length_app. apply Nat.le_add_l. Qed.

(* [comment removed for export] *)
Lemma lz_keeps_intro : forall c0 a b, dwf a -> dwf b -> SV c0 a -> SV c0 b -> KV b = KV a -> OUTLE a b -> lz_keeps a b.
Proof.
  intros c0 a b Da Db Va Vb E Ho. destruct (KV_fields a b E) as (E1 & E2 & E3 & _).
  unfold lz_keeps. rewrite E1, E2, E3.
  split; [reflexivity|].
  split; [rewrite (df_wl _ Db), (df_wl _ Da), E1; reflexivity|].
  split; [rewrite (df_pl _ Db), (df_pl _ Da), E1; reflexivity|].
  split; [rewrite (df_hl _ Db), (df_hl _ Da), E2; reflexivity|].
  split; [rewrite (df_bl _ Db), (df_bl _ Da), E3; reflexivity|].
  split; [rewrite (sv_input _ _ Vb), (sv_input _ _ Va); reflexivity|].
  split; [pose proof (sv_out _ _ Va) as A; pose proof (sv_out _ _ Vb) as B; unfold zlen in A, B; lia|].
  split; [exact (sv_aout _ _ Vb) | exact (OUTLE_len _ _ Ho)].
Qed.

(* [comment removed for export] *)
Record C0OK' (c0 : cstrm) : Prop := {
  c0'_ok : C0OK c0;
  c0'_nin : cs_next_in c0 = 0;
  c0'_ain : cs_avail_in c0 = arr_len (cs_input c0);
  c0'_tin : 0 <= cs_total_in c0 < 2 ^ 64;
  c0'_adler : 0 <= cs_adler c0 < 2 ^ 64;
  c0'_dt : - 2 ^ 31 <= cs_data_type c0 < 2 ^ 31;
  c0'_ib : forall i, 0 <= i < arr_len (cs_input c0) -> 0 <= arr_get (cs_input c0) i < 256 }.

Lemma C0OK'_of_call : forall zc, dcall_wf zc -> C0OK' (cstrm_of_call zc).
Proof.
  intros zc Hwf. pose proof Hwf as (Hz & Hao & Hlen & Hb). destruct Hz as (Ht1 & Ht2 & Had & Hdt).
  constructor; cbn [cstrm_of_call cs_next_in cs_avail_in cs_input cs_total_in cs_adler cs_data_type].
  - apply C0OK_of_call. exact Hwf.
  - reflexivity.
  - rewrite arr_len_of_list. reflexivity.
  - exact Ht1.
  - exact Had.
  - exact Hdt.
  - intros i Hi. rewrite arr_len_of_list in Hi. apply bytes_okP_get; [exact Hb | exact Hi].
Qed.

Lemma DC_dpost : forall c0 s0 s rc,
  C0OK' c0 -> ds_strm s0 = c0 -> dwf s0 -> DC c0 s -> KV s = KV s0 -> - 2 ^ 31 <= rc < 2 ^ 31 -> dpost_ok dwf s0 s rc.
Proof.
  intros c0 s0 s rc HC0' E0 D0 HDC E Hrc. pose proof (c0'_ok _ HC0') as HC0. pose proof HDC as [[D X] V].
  pose proof (c0_out _ HC0) as O0.
  unfold dpost_ok. cbv zeta. rewrite E0.
  split; [exact D|]. split; [exact (DC_DOK c0 s HC0 HDC)|].
  split.
  { destruct (KV_fields s0 s E) as (E1 & E2 & E3 & E4).
    split; [exact E4|]. unfold lz_keeps. rewrite E1, E2, E3, E0.
    split; [reflexivity|].
    split; [rewrite (df_wl _ D), (df_wl _ D0), E1; reflexivity|].
    split; [rewrite (df_pl _ D), (df_pl _ D0), E1; reflexivity|].
    split; [rewrite (df_hl _ D), (df_hl _ D0), E2; reflexivity|].
    split; [rewrite (df_bl _ D), (df_bl _ D0), E3; reflexivity|].
    split; [exact (sv_input _ _ V)|].
    split; [pose proof (sv_out _ _ V) as A; unfold zlen in A; lia|].
    split; [exact (sv_aout _ _ V)|]. rewrite O0. cbn [length]. lia. }
  split; [pose proof (sv_nin _ _ V); pose proof (sv_inlen _ _ V); pose proof (sv_ain _ _ V); lia|].
  split; [exact (sv_inlen _ _ V)|].
  split; [pose proof (sv_out _ _ V) as A; unfold zlen in A; lia|].
  split; [exact (sv_aout _ _ V)|].
  split; [unfold cs_output; rewrite rev_append_rev, app_nil_r; apply Forall_rev; exact (sv_outb _ _ V)|].
  split; [exact Hrc|].
  left. rewrite (sv_tout _ _ V), O0. unfold zlen. cbn [length Z.of_nat]. f_equal; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sym_buf_get_put_byte : forall s b i, 0 <= i -> ds_pending s < ds_lit_bufsize s ->
  sym_buf_get (put_byte s b) i = sym_buf_get s i.
Proof.
  intros s b i Hi Hp. unfold sym_buf_get, put_byte. dsred. rewrite arr_get_set.
  destruct (Z.eqb_spec (ds_pending s) (ds_lit_bufsize s + i)); [lia|]. cbn [andb]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition dx_core2 (s : deflate_state) :=
  (ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s, ds_level s, ds_strategy s,
   ds_ins_h s, ds_insert s, ds_w_size s, ds_match_length s, ds_prev_length s, ds_match_available s, ds_prev_match s,
   ds_matches s, ds_high_water s, ds_window_size s, ds_lookahead s, ds_block_start s, ds_strstart s,
   (ds_sym_next s, ds_wrap s, ds_status s, ds_lit_bufsize s, ds_dyn_ltree_fc s, ds_dyn_dtree_fc s, ds_bl_tree_fc s,
    ds_dyn_ltree_dl s, ds_dyn_dtree_dl s, ds_bl_tree_dl s, ds_depth s, ds_bl_count s, ds_opt_len s, ds_static_len s,
    ds_head s, ds_prev s, ds_hash_size s, ds_w_mask s, ds_match_start s)).

Lemma sym_readers_same : forall s s', (forall i, 0 <= i -> sym_buf_get s' i = sym_buf_get s i) ->
  (forall j, 0 <= j -> sym_lc s' (3 * j) = sym_lc s (3 * j)) /\ (forall j, 0 <= j -> sym_dist s' (3 * j) = sym_dist s (3 * j)).
Proof.
  intros s s' H. unfold sym_lc, sym_dist, sym_d0, sym_d1. split; intros j Hj; rewrite !H by lia; reflexivity.
Qed.

Lemma freq_hist_same2 : forall s s',
  (forall i, 0 <= i -> sym_buf_get s' i = sym_buf_get s i) -> ds_sym_next s' = ds_sym_next s ->
  ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s -> ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s -> ds_bl_tree_fc s' = ds_bl_tree_fc s ->
  0 <= nsym s -> freq_hist s -> freq_hist s'.
Proof.
  intros s s' Hs E3 E4 E5 E6 Hn (H1 & H2 & H3). destruct (sym_readers_same s s' Hs) as [La Lb].
  unfold freq_hist. rewrite (nsym_same s s' E3), E4, E5, E6.
  split; [|split; [|exact H3]].
  - intros c Hc. rewrite (H1 c Hc). f_equal. apply zsum_ext. intros j Hj. unfold sym_lcode. rewrite La, Lb by lia. reflexivity.
  - intros d Hd. rewrite (H2 d Hd). apply zsum_ext. intros j Hj. unfold sym_isdist, sym_dcode. rewrite Lb by lia. reflexivity.
Qed.

Lemma dx_core2_fields : forall s s', dx_core2 s' = dx_core2 s ->
  ds_good_match s' = ds_good_match s /\ ds_max_lazy_match s' = ds_max_lazy_match s /\ ds_nice_match s' = ds_nice_match s
  /\ ds_max_chain_length s' = ds_max_chain_length s /\ ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s
  /\ ds_ins_h s' = ds_ins_h s /\ ds_insert s' = ds_insert s /\ ds_w_size s' = ds_w_size s /\ ds_match_length s' = ds_match_length s
  /\ ds_prev_length s' = ds_prev_length s /\ ds_match_available s' = ds_match_available s /\ ds_prev_match s' = ds_prev_match s
  /\ ds_matches s' = ds_matches s /\ ds_high_water s' = ds_high_water s /\ ds_window_size s' = ds_window_size s
  /\ ds_lookahead s' = ds_lookahead s /\ ds_block_start s' = ds_block_start s /\ ds_strstart s' = ds_strstart s
  /\ ds_sym_next s' = ds_sym_next s /\ ds_wrap s' = ds_wrap s /\ ds_status s' = ds_status s /\ ds_lit_bufsize s' = ds_lit_bufsize s
  /\ ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s /\ ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s
  /\ ds_bl_tree_fc s' = ds_bl_tree_fc s /\ ds_dyn_ltree_dl s' = ds_dyn_ltree_dl s /\ ds_dyn_dtree_dl s' = ds_dyn_dtree_dl s
  /\ ds_bl_tree_dl s' = ds_bl_tree_dl s /\ ds_depth s' = ds_depth s /\ ds_bl_count s' = ds_bl_count s
  /\ ds_opt_len s' = ds_opt_len s /\ ds_static_len s' = ds_static_len s /\ ds_head s' = ds_head s /\ ds_prev s' = ds_prev s
  /\ ds_hash_size s' = ds_hash_size s /\ ds_w_mask s' = ds_w_mask s /\ ds_match_start s' = ds_match_start s.
Proof.
  intros s s' E. unfold dx_core2 in E.
  repeat match type of E with
  | (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?]
  end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

Lemma DX_core2_same : forall s s', dx_core2 s' = dx_core2 s ->
  (forall i, 0 <= i -> sym_buf_get s' i = sym_buf_get s i) ->
  (ds_pending s' = 0 -> ds_pending_out s' = 0) -> ds_bi_valid s' <= 7 ->
  DX s -> DX s'.
Proof.
  intros s s' E Hsym Hp Hbv X. pose proof (dx_core2_fields s s' E) as F.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20
               & F21 & F22 & F23 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & F32 & F33 & F34 & F35 & F36 & F37 & F38 & F39).
  assert (Em : dmode s' = dmode s) by (unfold dmode; rewrite F5, F6; reflexivity).
  assert (En : nsym s' = nsym s) by (apply nsym_same; exact F20).
  destruct (sym_readers_same s s' Hsym) as [La Lb].
  pose proof (dx_nsym _ X) as Hn.
  pose proof (dx_syms _ X) as Xsyms. pose proof (dx_hist _ X) as Xhist. pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl.
  pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc. pose proof (dx_chain _ X) as Xchain.
  destruct X; constructor; rewrite ?Em, ?En, ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11, ?F12, ?F13, ?F14, ?F15, ?F16,
    ?F17, ?F18, ?F19, ?F20, ?F21, ?F22, ?F23, ?F33, ?F34, ?F39; try assumption.
  - intros j Hj. unfold sym_okb. rewrite La, Lb by lia. apply Xsyms. exact Hj.
  - eapply freq_hist_same2; [exact Hsym | exact F20 | exact F25 | exact F26 | exact F27 | lia | exact Xhist].
  - intros t i. destruct t; cbn [tree_fc]; rewrite ?F25, ?F26, ?F27; [apply (Xtfc TL i) | apply (Xtfc TD i) | apply (Xtfc TB i)].
  - intros t i. destruct t; cbn [tree_dl]; rewrite ?F28, ?F29, ?F30; [apply (Xtdl TL i) | apply (Xtdl TD i) | apply (Xtdl TB i)].
  - intros i. rewrite F31. apply Xdepth.
  - intros i Hi. rewrite F32. apply Xblc. exact Hi.
  - intros Hm. apply (CHAIN_same s s'); [exact F35 | exact F36 | exact F37 | exact F9 | exact F38 |]. apply Xchain. exact Hm.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dwf_put_byte : forall s b, dwf s -> ds_pending_out s + ds_pending s + 1 <= ds_lit_bufsize s * 4 -> dwf (put_byte s b).
Proof.
  intros s b D Hroom. pose proof (df_pend _ D) as P.
  destruct D; constructor; unfold put_byte; dsred; try assumption.
  - rewrite arr_len_set. assumption.
  - intros i Hi. rewrite arr_get_set. destruct (_ && _); [pose proof (wrap8_range b); lia | auto].
  - lia.
Qed.

Lemma DX_put_byte : forall s b, DX s -> 0 <= ds_pending s < ds_lit_bufsize s -> DX (put_byte s b).
Proof.
  intros s b X Hp. apply (DX_core2_same s); [reflexivity | | | | exact X].
  - intros i Hi. apply sym_buf_get_put_byte; lia.
  - unfold put_byte; dsred. lia.
  - unfold put_byte; dsred. exact (dx_biv _ X).
Qed.

Lemma SV_put_byte : forall c0 s b, SV c0 s -> SV c0 (put_byte s b).
Proof. intros c0 s b V. apply (SV_strm c0 s); [reflexivity | exact V]. Qed.

Lemma DC_put_byte : forall c0 s b, DC c0 s -> 0 <= ds_pending s -> ds_pending_out s + ds_pending s + 1 <= ds_lit_bufsize s ->
  DC c0 (put_byte s b) /\ ds_pending (put_byte s b) = ds_pending s + 1 /\ ds_pending_out (put_byte s b) = ds_pending_out s
  /\ KV (put_byte s b) = KV s /\ ds_strm (put_byte s b) = ds_strm s /\ ds_lit_bufsize (put_byte s b) = ds_lit_bufsize s.
Proof.
  intros c0 s b [[D X] V] Hp Hroom. pose proof (dwf_sizes s D) as (_ & _ & Sl & _). pose proof (df_pend _ D).
  split; [| unfold put_byte; dsred; repeat split; reflexivity].
  split; [split|].
  - apply dwf_put_byte; [exact D | lia].
  - apply DX_put_byte; [exact X | lia].
  - apply SV_put_byte. exact V.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tr_flush_bits_id7 : forall s, ds_bi_valid s <= 7 -> tr_flush_bits s = s.
Proof.
  intros s H. unfold tr_flush_bits, bi_flush.
  destruct (Z.eqb_spec (ds_bi_valid s) 16); [lia|]. destruct (Z.leb_spec 8 (ds_bi_valid s)); [lia|]. reflexivity.
Qed.

Lemma fp_len_range : forall s, 0 <= cs_avail_out (ds_strm s) -> 0 <= ds_pending s < 2 ^ 32 ->
  0 <= fp_len s <= ds_pending s /\ fp_len s <= cs_avail_out (ds_strm s)
  /\ (fp_len s = ds_pending s \/ fp_len s = cs_avail_out (ds_strm s)).
Proof.
  intros s Ha Hp. unfold fp_len. rewrite wrap32_mod, Z.mod_small by lia.
  destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (ds_pending s)); lia.
Qed.

(* [comment removed for export] *)
Lemma fp_tail_facts' : forall s len, 0 <= len <= ds_pending s ->
  let s1 := fp_tail s len in
  ds_pending s1 = ds_pending s - len
  /\ (ds_pending s1 = 0 -> ds_pending_out s1 = 0)
  /\ (ds_pending s1 <> 0 -> ds_pending_out s1 = ds_pending_out s + len)
  /\ ds_bi_valid s1 = ds_bi_valid s /\ ds_bi_buf s1 = ds_bi_buf s /\ ds_pending_buf s1 = ds_pending_buf s
  /\ cs_avail_out (ds_strm s1) = cs_avail_out (ds_strm s) - len
  /\ cs_avail_in (ds_strm s1) = cs_avail_in (ds_strm s) /\ cs_next_in (ds_strm s1) = cs_next_in (ds_strm s)
  /\ cs_input (ds_strm s1) = cs_input (ds_strm s) /\ cs_total_in (ds_strm s1) = cs_total_in (ds_strm s)
  /\ cs_total_out (ds_strm s1) = wrap64 (cs_total_out (ds_strm s) + len) /\ cs_adler (ds_strm s1) = cs_adler (ds_strm s)
  /\ cs_data_type (ds_strm s1) = cs_data_type (ds_strm s)
  /\ cs_out_rev (ds_strm s1) = rev_append (arr_slice (ds_pending_buf s) (ds_pending_out s) len) (cs_out_rev (ds_strm s))
  /\ KV s1 = KV s /\ dx_core2 s1 = dx_core2 s.
Proof.
  intros s len Hl s1. subst s1. unfold fp_tail, cs_emit.
  destruct (Z.eqb_spec (ds_pending s - len) 0); dsred; repeat split; try reflexivity; try lia.
Qed.

Lemma Forall_rev_append : forall (P : Z -> Prop) l acc, Forall P l -> Forall P acc -> Forall P (rev_append l acc).
Proof.
  intros P l. induction l as [|x l IH]; intros acc Hl Hacc; cbn [rev_append]; [exact Hacc|].
  inversion Hl; subst. apply IH; [assumption | constructor; assumption].
Qed.

Lemma Forall_arr_slice_nat : forall (P : Z -> Prop) a k ofs,
  (forall i, ofs <= i < ofs + Z.of_nat k -> P (arr_get a i)) -> Forall P (arr_slice_nat a ofs k).
Proof.
  intros P a k. induction k as [|k IH]; intros ofs H; cbn [arr_slice_nat]; constructor.
  - apply H. lia.
  - apply IH. intros i Hi. apply H. lia.
Qed.

Lemma Forall_arr_slice : forall (P : Z -> Prop) a ofs n,
  (forall i, ofs <= i < ofs + n -> P (arr_get a i)) -> Forall P (arr_slice a ofs n).
Proof.
  intros P a ofs n H. unfold arr_slice. apply Forall_arr_slice_nat. intros i Hi. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma DC_flush_pending : forall c0 s, C0OK c0 -> DC c0 s ->
  let s' := flush_pending s in
  DC c0 s' /\ KV s' = KV s /\ OUTLE s s' /\ dx_core2 s' = dx_core2 s
  /\ fp_ok s
  /\ 0 <= ds_pending s' <= ds_pending s
  /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
  /\ (ds_pending s = 0 -> s' = s)
  /\ ds_bi_valid s' = ds_bi_valid s /\ ds_pending_buf s' = ds_pending_buf s
  /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s) /\ cs_next_in (ds_strm s') = cs_next_in (ds_strm s).
Proof.
  intros c0 s HC0 HDC s'. pose proof HDC as [[D X] V]. subst s'.
  pose proof (dwf_sizes s D) as (Sw & Sh & Sl & Spbs & Ssh). pose proof (df_pend _ D) as (P1 & P2 & P3). pose proof (df_bi _ D) as (B1 & B2).
  pose proof (dx_biv _ X) as B7.
  pose proof (sv_aout _ _ V) as A0. pose proof (sv_out _ _ V) as Ao. pose proof (c0_out _ HC0) as O0. pose proof (c0_aout _ HC0) as Aa.
  rewrite O0 in Ao. unfold zlen in Ao. cbn [length Z.of_nat] in Ao.
  assert (Hfp : fp_ok s).
  { unfold fp_ok. cbv zeta. rewrite (tr_flush_bits_id7 s B7).
    pose proof (fp_len_range s A0 ltac:(lia)) as (R1 & R2 & R3).
    split; [unfold BINV; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    rewrite (sv_tout _ _ V). apply wrap64_range'. }
  rewrite flush_pending_eq. cbv zeta. rewrite (tr_flush_bits_id7 s B7).
  pose proof (fp_len_range s A0 ltac:(lia)) as (R1 & R2 & R3).
  destruct (Z.eqb_spec (fp_len s) 0) as [E0|E0].
  { split; [exact HDC|]. split; [reflexivity|]. split; [apply OUTLE_refl|]. split; [reflexivity|]. split; [exact Hfp|].
    split; [lia|]. split; [lia|]. split; [reflexivity|]. repeat split; reflexivity. }
  pose proof (fp_tail_facts' s (fp_len s) ltac:(lia)) as
    (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17).
  set (s1 := fp_tail s (fp_len s)) in *.
  assert (D1 : dwf s1).
  { destruct D; constructor; subst s1; unfold fp_tail, cs_emit; destruct (_ =? 0); dsred; try assumption; lia. }
  assert (X1 : DX s1).
  { apply (DX_core2_same s s1 F17); [| exact F2 | rewrite F4; exact B7 | exact X].
    intros i Hi. unfold sym_buf_get. rewrite F6. destruct (KV_fields s s1 F16) as (_ & _ & E3 & _). rewrite E3. reflexivity. }
  assert (V1 : SV c0 s1).
  { constructor; rewrite ?F7, ?F8, ?F9, ?F10, ?F11, ?F12, ?F13, ?F14, ?F15.
    - exact (sv_input _ _ V).
    - exact (sv_nin _ _ V).
    - exact (sv_inlen _ _ V).
    - exact (sv_ain _ _ V).
    - unfold zlen. rewrite rev_append_rev, length_app, length_rev. unfold arr_slice. rewrite arr_slice_nat_length.
      rewrite O0. cbn [length]. unfold zlen in Ao. lia.
    - lia.
    - rewrite O0. apply le_0_n.
    - apply Forall_rev_append; [| exact (sv_outb _ _ V)]. apply Forall_arr_slice. intros i Hi.
      apply (df_bb _ D). lia.
    - exact (sv_tin _ _ V).
    - rewrite (sv_tout _ _ V), O0. unfold zlen. rewrite rev_append_rev, length_app, length_rev. unfold arr_slice. rewrite arr_slice_nat_length.
      cbn [length Z.of_nat]. rewrite Z.sub_0_r, Z.sub_0_r. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
      rewrite wrap64_add_l. f_equal. lia.
    - exact (sv_adler _ _ V).
    - exact (sv_dt _ _ V).
    - intros i Hi. apply (sv_ib _ _ V). exact Hi. }
  split; [exact (conj (conj D1 X1) V1)|]. split; [exact F16|].
  split; [apply (OUTLE_emit _ _ (arr_slice (ds_pending_buf s) (ds_pending_out s) (fp_len s))); exact F15|].
  split; [exact F17|]. split; [exact Hfp|]. split; [lia|]. split; [lia|].
  split; [intros Hp0; exfalso; lia|]. repeat split; assumption.
Qed.
