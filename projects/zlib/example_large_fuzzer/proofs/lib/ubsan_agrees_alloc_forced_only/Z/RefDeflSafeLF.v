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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeW.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record DXX (s : deflate_state) : Prop := {
  xx_cfg : (ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s) = configuration_table (ds_level s);
  xx_insh : 0 <= ds_ins_h s < 65536;
  xx_ins : ds_insert s <= ds_w_size s;
  xx_ml : 0 <= ds_match_length s <= MAX_MATCH;
  xx_pl : 0 <= ds_prev_length s <= MAX_MATCH;
  xx_ma : ds_match_available s = 0 \/ ds_match_available s = 1;
  xx_pm : 0 <= ds_prev_match s < 2 ^ 32;
  xx_hw : ds_high_water s <= ds_window_size s;
  xx_fast : dmode s = 3 -> ds_prev_length s = 2 /\ ds_match_length s < MIN_MATCH;
  xx_notslow : dmode s <> 4 -> ds_match_available s = 0;
  xx_slow : dmode s = 4 -> 2 <= ds_match_length s /\ (ds_match_available s = 1 -> 1 <= ds_strstart s);
  xx_st0 : dmode s = 0 -> ds_lookahead s = 0 /\ 0 <= ds_block_start s <= ds_strstart s /\ ds_sym_next s = 0 /\ ds_matches s <= 2;
  xx_wrapneg : ds_wrap s < 0 -> ds_status s = FINISH_STATE;
  xx_fin : ds_status s = FINISH_STATE -> ds_lookahead s = 0;
  xx_tdl : forall t i, 0 <= arr_get (tree_dl s t) i < 65536;
  xx_depth : forall i, 0 <= arr_get (ds_depth s) i < 256;
  xx_blc : forall i, 0 <= i < 16 -> 0 <= arr_get (ds_bl_count s) i < 65536;
  xx_chain : dmode s <> 0 -> CHAIN s (ds_strstart s) (ds_strstart s) }.

(* [comment removed for export] *)
Record DXR (s : deflate_state) : Prop := {
  xr_matches : 0 <= ds_matches s <= nsym s + 2;
  xr_sn : ds_sym_next s = 3 * nsym s;
  xr_nsym : 0 <= nsym s <= ds_lit_bufsize s - 2;
  xr_syms : forall j, 0 <= j < nsym s -> sym_okb s j;
  xr_hist : freq_hist s;
  xr_opt : ds_opt_len s = 0;
  xr_stat : ds_static_len s = 0;
  xr_ext : dmode s <> 0 -> 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s + ds_match_available s;
  xr_tfc : forall t i, 0 <= arr_get (tree_fc s t) i < 65536;
  xr_pout0 : ds_pending s = 0 -> ds_pending_out s = 0;
  xr_biv : ds_bi_valid s <= 7 }.

(* [comment removed for export] *)
Definition SLOW3 (s : deflate_state) : Prop :=
  dmode s = 4 -> MIN_MATCH <= ds_match_length s ->
  ds_match_length s <= ds_lookahead s + 1 /\ 1 <= ds_strstart s
  /\ 2 <= wrap32 (ds_strstart s - ds_match_start s) <= ds_w_size s - MIN_LOOKAHEAD + 1.
Definition BND (s : deflate_state) : Prop :=
  (dmode s <> 0 -> CHAIN s (ds_strstart s - 1) (ds_strstart s - 1)) /\ SLOW3 s.

Lemma SLOW3_mode : forall s, dmode s <> 4 -> SLOW3 s.
Proof. intros s Hm H4. exfalso. exact (Hm H4). Qed.

Lemma DX_DXX : forall s, DX s -> DXX s.
Proof.
  intros s X. destruct X; constructor; try assumption.
  - intros Hm. destruct (dx_slow Hm) as (A & B & _). exact (conj A B).
  - intros Hm. eapply CHAIN_mono; [| | exact (dx_chain Hm)]; lia.
Qed.

Lemma DX_BND : forall s, DX s -> BND s.
Proof. intros s X. split; [exact (dx_chain _ X)|]. intros Hm H3. destruct (dx_slow _ X Hm) as (_ & _ & C). exact (C H3). Qed.

Lemma DX_join : forall s, DXX s -> DXR s -> BND s -> DX s.
Proof.
  intros s XX XR [BC BS]. destruct XX, XR; constructor; try assumption.
  intros Hm. match goal with Hx : dmode s = 4 -> 2 <= ds_match_length s /\ _ |- _ => destruct (Hx Hm) as [A B] end.
  split; [exact A|]. split; [exact B|]. exact (BS Hm).
Qed.

(* [comment removed for export] *)
Lemma DXX_DX : forall s, DXX s -> SLOW3 s ->
  0 <= ds_matches s <= nsym s + 2 -> ds_sym_next s = 3 * nsym s -> 0 <= nsym s <= ds_lit_bufsize s - 2 ->
  (forall j, 0 <= j < nsym s -> sym_okb s j) -> freq_hist s -> ds_opt_len s = 0 -> ds_static_len s = 0 ->
  (dmode s <> 0 -> 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s + ds_match_available s) ->
  (forall t i, 0 <= arr_get (tree_fc s t) i < 65536) ->
  (ds_pending s = 0 -> ds_pending_out s = 0) -> ds_bi_valid s <= 7 ->
  (dmode s <> 0 -> CHAIN s (ds_strstart s - 1) (ds_strstart s - 1)) -> DX s.
Proof. intros s XX SL; intros. apply (DX_join s XX); [constructor; assumption | split; assumption]. Qed.

(* [comment removed for export] *)
Definition DCW (c0 : cstrm) (s : deflate_state) : Prop := (dwf s /\ (DXX s /\ DXR s)) /\ SV c0 s.

Lemma DCW_DC : forall c0 s, DCW c0 s -> BND s -> DC c0 s.
Proof. intros c0 s [[D [XX XR]] V] B. exact (conj (conj D (DX_join s XX XR B)) V). Qed.

(* [comment removed for export] *)
Lemma DXX_core2_same : forall s s', dx_core2 s' = dx_core2 s -> DXX s -> DXX s'.
Proof.
  intros s s' E X. pose proof (dx_core2_fields s s' E) as F.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20
               & F21 & F22 & F23 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & F32 & F33 & F34 & F35 & F36 & F37 & F38 & F39).
  assert (Em : dmode s' = dmode s) by (unfold dmode; rewrite F5, F6; reflexivity).
  pose proof (xx_tdl _ X) as Xtdl. pose proof (xx_depth _ X) as Xdepth. pose proof (xx_blc _ X) as Xblc. pose proof (xx_chain _ X) as Xchain.
  destruct X; constructor; rewrite ?Em, ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11, ?F12, ?F13, ?F14, ?F15, ?F16,
    ?F17, ?F18, ?F19, ?F20, ?F21, ?F22, ?F23, ?F33, ?F34, ?F39; try assumption.
  - intros t i. destruct t; cbn [tree_dl]; rewrite ?F28, ?F29, ?F30; [apply (Xtdl TL i) | apply (Xtdl TD i) | apply (Xtdl TB i)].
  - intros i. rewrite F31. apply Xdepth.
  - intros i Hi. rewrite F32. apply Xblc. exact Hi.
  - intros Hm. apply (CHAIN_same s s'); [exact F35 | exact F36 | exact F37 | exact F9 | exact F38 |]. apply Xchain. exact Hm.
Qed.

Lemma DXR_core2_same : forall s s', dx_core2 s' = dx_core2 s ->
  (forall i, 0 <= i -> sym_buf_get s' i = sym_buf_get s i) ->
  (ds_pending s' = 0 -> ds_pending_out s' = 0) -> ds_bi_valid s' <= 7 ->
  DXR s -> DXR s'.
Proof.
  intros s s' E Hsym Hp Hbv X. pose proof (dx_core2_fields s s' E) as F.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20
               & F21 & F22 & F23 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & F32 & F33 & F34 & F35 & F36 & F37 & F38 & F39).
  assert (Em : dmode s' = dmode s) by (unfold dmode; rewrite F5, F6; reflexivity).
  assert (En : nsym s' = nsym s) by (apply nsym_same; exact F20).
  destruct (sym_readers_same s s' Hsym) as [La Lb].
  pose proof (xr_syms _ X) as Xsyms. pose proof (xr_hist _ X) as Xhist. pose proof (xr_tfc _ X) as Xtfc.
  destruct X; constructor; rewrite ?Em, ?En, ?F12, ?F14, ?F18, ?F19, ?F20, ?F23, ?F33, ?F34; try assumption.
  - intros j Hj. unfold sym_okb. rewrite La, Lb by lia. apply Xsyms. exact Hj.
  - eapply freq_hist_same2; [exact Hsym | exact F20 | exact F25 | exact F26 | exact F27 | lia | exact Xhist].
  - intros t i. destruct t; cbn [tree_fc]; rewrite ?F25, ?F26, ?F27; [apply (Xtfc TL i) | apply (Xtfc TD i) | apply (Xtfc TB i)].
Qed.

(* [comment removed for export] *)
Lemma DCW_flush_pending : forall c0 s, C0OK c0 -> DCW c0 s ->
  let s' := flush_pending s in
  DCW c0 s' /\ KV s' = KV s /\ OUTLE s s' /\ dx_core2 s' = dx_core2 s
  /\ fp_ok s
  /\ 0 <= ds_pending s' <= ds_pending s
  /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
  /\ (ds_pending s = 0 -> s' = s)
  /\ ds_bi_valid s' = ds_bi_valid s /\ ds_pending_buf s' = ds_pending_buf s
  /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s) /\ cs_next_in (ds_strm s') = cs_next_in (ds_strm s).
Proof.
  intros c0 s HC0 HDC s'. pose proof HDC as [[D [XX XR]] V]. subst s'.
  pose proof (dwf_sizes s D) as (Sw & Sh & Sl & Spbs & Ssh). pose proof (df_pend _ D) as (P1 & P2 & P3). pose proof (df_bi _ D) as (B1 & B2).
  pose proof (xr_biv _ XR) as B7.
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
  assert (Hsb : forall i, 0 <= i -> sym_buf_get s1 i = sym_buf_get s i).
  { intros i Hi. unfold sym_buf_get. rewrite F6. destruct (KV_fields s s1 F16) as (_ & _ & E3 & _). rewrite E3. reflexivity. }
  assert (XX1 : DXX s1) by (exact (DXX_core2_same s s1 F17 XX)).
  assert (XR1 : DXR s1) by (apply (DXR_core2_same s s1 F17 Hsb F2); [rewrite F4; exact B7 | exact XR]).
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
  split; [exact (conj (conj D1 (conj XX1 XR1)) V1)|]. split; [exact F16|].
  split; [apply (OUTLE_emit _ _ (arr_slice (ds_pending_buf s) (ds_pending_out s) (fp_len s))); exact F15|].
  split; [exact F17|]. split; [exact Hfp|]. split; [lia|]. split; [lia|].
  split; [intros Hp0; exfalso; lia|]. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma BND_same : forall a b, BND a -> dmode b = dmode a ->
  ds_head b = ds_head a -> ds_prev b = ds_prev a -> ds_hash_size b = ds_hash_size a -> ds_w_size b = ds_w_size a -> ds_w_mask b = ds_w_mask a ->
  ds_strstart b = ds_strstart a -> ds_match_length b = ds_match_length a -> ds_lookahead b = ds_lookahead a -> ds_match_start b = ds_match_start a ->
  BND b.
Proof.
  intros a b [BC BS] Em Ehd Epv Ehs Ews Ewm Estr Eml Elook Ems. split.
  - intros Hm. rewrite Estr. apply (CHAIN_same a b _ _ Ehd Epv Ehs Ews Ewm). apply BC. rewrite <- Em. exact Hm.
  - unfold SLOW3 in *. rewrite Em, Eml, Elook, Estr, Ems, Ews. exact BS.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PF (s : deflate_state) :=
  ((ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s, ds_level s, ds_strategy s),
   (ds_ins_h s, ds_insert s, ds_prev_length s, ds_match_available s, ds_prev_match s, ds_high_water s, ds_window_size s, ds_wrap s),
   (ds_status s, ds_lit_bufsize s, ds_head s, ds_prev s, ds_hash_size s, ds_w_mask s, ds_hash_mask s, ds_hash_shift s),
   (ds_w_bits s, ds_hash_bits s, ds_pending_buf_size s, ds_gzhead s, ds_method s, ds_last_flush s, ds_sym_end s, ds_match_start s, KV s)).

Lemma keeps_PF : keeps PF true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Lemma PF_fields : forall a b, PF b = PF a ->
  (ds_good_match b = ds_good_match a /\ ds_max_lazy_match b = ds_max_lazy_match a /\ ds_nice_match b = ds_nice_match a
   /\ ds_max_chain_length b = ds_max_chain_length a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a)
  /\ (ds_ins_h b = ds_ins_h a /\ ds_insert b = ds_insert a /\ ds_prev_length b = ds_prev_length a /\ ds_match_available b = ds_match_available a
      /\ ds_prev_match b = ds_prev_match a /\ ds_high_water b = ds_high_water a /\ ds_window_size b = ds_window_size a /\ ds_wrap b = ds_wrap a)
  /\ (ds_status b = ds_status a /\ ds_lit_bufsize b = ds_lit_bufsize a /\ ds_head b = ds_head a /\ ds_prev b = ds_prev a
      /\ ds_hash_size b = ds_hash_size a /\ ds_w_mask b = ds_w_mask a /\ ds_hash_mask b = ds_hash_mask a /\ ds_hash_shift b = ds_hash_shift a)
  /\ (ds_w_bits b = ds_w_bits a /\ ds_hash_bits b = ds_hash_bits a /\ ds_pending_buf_size b = ds_pending_buf_size a /\ ds_gzhead b = ds_gzhead a
      /\ ds_method b = ds_method a /\ ds_last_flush b = ds_last_flush a /\ ds_sym_end b = ds_sym_end a /\ ds_match_start b = ds_match_start a /\ KV b = KV a).
Proof.
  intros a b E. unfold PF in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

Lemma tr_flush_bits_shape : forall s, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2 ^ 16 ->
  exists A P B V, tr_flush_bits s = upd4 s A P B V
    /\ ds_pending s <= P <= ds_pending s + 2 /\ 0 <= V <= 7 /\ 0 <= B < 2 ^ 16 /\ arr_len A = arr_len (ds_pending_buf s)
    /\ (forall n, (forall i, 0 <= i < n -> 0 <= arr_get (ds_pending_buf s) i < 256) -> forall i, 0 <= i < n -> 0 <= arr_get A i < 256).
Proof.
  intros s Hbv Hbb.
  destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E.
  - exists (ds_pending_buf s), (ds_pending s), (ds_bi_buf s), (ds_bi_valid s).
    split; [destruct s; reflexivity|]. 
    assert (ds_bi_valid s <= 7).
    { unfold tr_flush_bits, bi_flush in E. destruct (Z.eqb_spec (ds_bi_valid s) 16); [exfalso|].
      - (* [comment removed for export] *) 
        apply (f_equal ds_pending) in E. unfold put_short, put_byte in E. revert E. dsred. lia.
      - destruct (Z.leb_spec 8 (ds_bi_valid s)); [exfalso | lia].
        apply (f_equal ds_pending) in E. unfold put_byte in E. revert E. dsred. lia. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. intros nn Hn ii Hi. apply Hn. exact Hi.
  - exists (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (ds_bi_buf s))), (ds_pending s + 1), (Z.shiftr (ds_bi_buf s) 8), (ds_bi_valid s - 8).
    assert (8 <= ds_bi_valid s < 16).
    { unfold tr_flush_bits, bi_flush in E. destruct (Z.eqb_spec (ds_bi_valid s) 16).
      - exfalso. apply (f_equal ds_pending) in E. unfold put_short, put_byte in E. revert E. dsred. lia.
      - destruct (Z.leb_spec 8 (ds_bi_valid s)); [lia|]. exfalso. apply (f_equal ds_pending) in E. unfold put_byte in E. revert E. dsred. lia. }
    split; [unfold upd4, put_byte; dsred; reflexivity|].
    split; [lia|]. split; [lia|].
    split; [rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]|].
    split; [rewrite arr_len_set; reflexivity|].
    intros nn Hn ii Hi. rewrite arr_get_set. destruct (_ && _); [apply wrap8_range | apply Hn; exact Hi].
  - exists (arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255))) (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 (ds_bi_buf s)) 8))),
           (ds_pending s + 1 + 1), 0, 0.
    split; [unfold upd4, put_byte; dsred; reflexivity|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite !arr_len_set; reflexivity|].
    intros nn Hn ii Hi. rewrite !arr_get_set. repeat (destruct (_ && _); [apply wrap8_range|]). apply Hn. exact Hi.
Qed.

Lemma flush_pending_bits : forall s, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2 ^ 16 -> flush_pending (tr_flush_bits s) = flush_pending s.
Proof.
  intros s Hbv Hbb. rewrite (flush_pending_eq (tr_flush_bits s)), (flush_pending_eq s). cbv zeta.
  destruct (tr_flush_bits_shape s Hbv Hbb) as (A & P & B & V & E & _ & HV & _).
  rewrite (tr_flush_bits_id7 (tr_flush_bits s)) by (rewrite E; unfold upd4; dsred; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TRS (s : deflate_state) :=
  ((ds_dyn_ltree_fc s, ds_dyn_dtree_fc s, ds_bl_tree_fc s, ds_dyn_ltree_dl s, ds_dyn_dtree_dl s, ds_bl_tree_dl s),
   (ds_depth s, ds_bl_count s, ds_heap s, ds_opt_len s, ds_static_len s, ds_matches s, ds_sym_next s)).

Lemma TRS_fields : forall a b, TRS b = TRS a ->
  (ds_dyn_ltree_fc b = ds_dyn_ltree_fc a /\ ds_dyn_dtree_fc b = ds_dyn_dtree_fc a /\ ds_bl_tree_fc b = ds_bl_tree_fc a
   /\ ds_dyn_ltree_dl b = ds_dyn_ltree_dl a /\ ds_dyn_dtree_dl b = ds_dyn_dtree_dl a /\ ds_bl_tree_dl b = ds_bl_tree_dl a)
  /\ (ds_depth b = ds_depth a /\ ds_bl_count b = ds_bl_count a /\ ds_heap b = ds_heap a /\ ds_opt_len b = ds_opt_len a
      /\ ds_static_len b = ds_static_len a /\ ds_matches b = ds_matches a /\ ds_sym_next b = ds_sym_next a).
Proof.
  intros a b E. unfold TRS in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

Lemma tree_fc_TRS : forall a b t, TRS b = TRS a -> tree_fc b t = tree_fc a t.
Proof. intros a b t E. pose proof (TRS_fields a b E) as ((E1 & E2 & E3 & _) & _). destruct t; cbn [tree_fc]; congruence. Qed.
Lemma tree_dl_TRS : forall a b t, TRS b = TRS a -> tree_dl b t = tree_dl a t.
Proof. intros a b t E. pose proof (TRS_fields a b E) as ((_ & _ & _ & E1 & E2 & E3) & _). destruct t; cbn [tree_dl]; congruence. Qed.
Lemma tree_lens_TRS : forall a b, TRS b = TRS a -> tree_lens a -> tree_lens b.
Proof.
  intros a b E T. pose proof (TRS_fields a b E) as ((E1 & E2 & E3 & E4 & E5 & E6) & (E7 & E8 & E9 & _)).
  unfold tree_lens in *. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9. exact T.
Qed.

(* [comment removed for export] *)
Lemma PF_tfb : forall s buf len last, PF (tr_flush_block s buf len last) = PF s.
Proof. intros. rewrite (k_tr_flush_block PF keeps_PF). unfold tfb_X0. destruct (_ && _); [destruct s|]; reflexivity. Qed.
Lemma PF_set_block_start : forall s v, PF (set_block_start s v) = PF s. Proof. reflexivity. Qed.
Lemma PF_upd4 : forall s a p b v, PF (upd4 s a p b v) = PF s. Proof. reflexivity. Qed.
Lemma PF_tr_flush_bits : forall s, PF (tr_flush_bits s) = PF s.
Proof. intros s. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; reflexivity. Qed.
Lemma PF_fp_tail : forall s len, PF (fp_tail s len) = PF s.
Proof. intros s len. unfold fp_tail. destruct (_ =? 0); reflexivity. Qed.
Lemma PF_flush_pending : forall s, PF (flush_pending s) = PF s.
Proof. intros s. rewrite flush_pending_eq. cbv zeta. destruct (_ =? 0); rewrite ?PF_fp_tail; apply PF_tr_flush_bits. Qed.

Lemma TRS_upd4 : forall s a p b v, TRS (upd4 s a p b v) = TRS s. Proof. reflexivity. Qed.

Lemma window_tr_flush_bits : forall s, ds_window (tr_flush_bits s) = ds_window s.
Proof. intros s. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; reflexivity. Qed.
Lemma window_fp_tail : forall s len, ds_window (fp_tail s len) = ds_window s.
Proof. intros s len. unfold fp_tail. destruct (_ =? 0); reflexivity. Qed.
Lemma window_flush_pending : forall s, ds_window (flush_pending s) = ds_window s.
Proof. intros s. rewrite flush_pending_eq. cbv zeta. destruct (_ =? 0); rewrite ?window_fp_tail; apply window_tr_flush_bits. Qed.
Lemma ml_flush_pending : forall s, ds_match_length (flush_pending s) = ds_match_length s.
Proof.
  intros s. rewrite flush_pending_eq. cbv zeta.
  assert (E1 : forall len, ds_match_length (fp_tail (tr_flush_bits s) len) = ds_match_length (tr_flush_bits s)) by (intros len; unfold fp_tail; destruct (_ =? 0); reflexivity).
  assert (E2 : ds_match_length (tr_flush_bits s) = ds_match_length s) by (destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; reflexivity).
  destruct (_ =? 0); rewrite ?E1; exact E2.
Qed.

Lemma lz_set_block_start : forall s v,
  (ds_strstart (set_block_start s v), ds_lookahead (set_block_start s v), ds_block_start (set_block_start s v),
   ds_match_length (set_block_start s v), ds_window (set_block_start s v), ds_strm (set_block_start s v), ds_pending_out (set_block_start s v))
  = (ds_strstart s, ds_lookahead s, v, ds_match_length s, ds_window s, ds_strm s, ds_pending_out s).
Proof. reflexivity. Qed.
Lemma lz_upd4 : forall s a p b v,
  (ds_strstart (upd4 s a p b v), ds_lookahead (upd4 s a p b v), ds_block_start (upd4 s a p b v),
   ds_match_length (upd4 s a p b v), ds_window (upd4 s a p b v), ds_strm (upd4 s a p b v), ds_pending_out (upd4 s a p b v))
  = (ds_strstart s, ds_lookahead s, ds_block_start s, ds_match_length s, ds_window s, ds_strm s, ds_pending_out s).
Proof. reflexivity. Qed.
Lemma bits_upd4 : forall s a p b v,
  (ds_pending_buf (upd4 s a p b v), ds_pending (upd4 s a p b v), ds_bi_buf (upd4 s a p b v), ds_bi_valid (upd4 s a p b v)) = (a, p, b, v).
Proof. reflexivity. Qed.

Lemma lz_view_fields : forall a b, lz_view b = lz_view a ->
  ds_strstart b = ds_strstart a /\ ds_lookahead b = ds_lookahead a /\ ds_block_start b = ds_block_start a
  /\ ds_match_length b = ds_match_length a /\ ds_window b = ds_window a /\ ds_w_size b = ds_w_size a.
Proof.
  intros a b E. unfold lz_view in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma SV_cset_data_type : forall c0 s s' dt, SV c0 s -> ds_strm s' = cset_data_type (ds_strm s) dt -> - 2 ^ 31 <= dt < 2 ^ 31 -> SV c0 s'.
Proof.
  intros c0 s s' dt V E Hdt. destruct V; constructor; rewrite E; unfold cset_data_type; cbn; assumption.
Qed.

Lemma dmode_PF : forall a b, PF b = PF a -> dmode b = dmode a.
Proof. intros a b E. pose proof (PF_fields a b E) as ((_ & _ & _ & _ & El & Es) & _). unfold dmode. rewrite El, Es. reflexivity. Qed.

(* [comment removed for export] *)
Lemma DXX_transfer : forall a b, DXX a -> PF b = PF a ->
  ds_strstart b = ds_strstart a -> ds_lookahead b = ds_lookahead a -> ds_match_length b = ds_match_length a -> dmode a <> 0 ->
  (forall t i, 0 <= arr_get (tree_dl b t) i < 65536) -> (forall i, 0 <= arr_get (ds_depth b) i < 256) ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get (ds_bl_count b) i < 65536) -> DXX b.
Proof.
  intros a b X E Estr Elook Eml Hm Htdl Hdep Hblc.
  pose proof (PF_fields a b E) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eih & Eins & Epl & Ema & Epm & Ehw & Ewsz & Ewr) & (Est & Elbs & Ehd & Epv & Ehs & Ewm & Ehm & Ehsh) & (Ewb & Ehb & Epbs & Egz & Eme & Elf & Ese & Ems & EKV)).
  pose proof (KV_fields _ _ EKV) as (Ews & Ehsz & _ & _).
  assert (Em : dmode b = dmode a) by (unfold dmode; rewrite Elv, Esy; reflexivity).
  pose proof (xx_chain _ X) as XC.
  destruct X; constructor; rewrite ?Em, ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Esy, ?Eih, ?Eins, ?Epl, ?Ema, ?Epm, ?Ehw, ?Ewsz, ?Ewr, ?Est, ?Ews, ?Estr, ?Elook, ?Eml, ?Ems; try assumption.
  - intros H0. exfalso. exact (Hm H0).
  - intros Hm'. apply (CHAIN_same a b); [exact Ehd | exact Epv | exact Ehs | exact Ews | exact Ewm |]. exact (XC Hm').
Qed.

Lemma PF_tfb_X0 : forall s, PF (tfb_X0 s) = PF s.
Proof. intros s. unfold tfb_X0. destruct (_ && _); [destruct s|]; reflexivity. Qed.

Lemma flush_block_only_eq' : forall s last,
  flush_block_only s last
  = flush_pending (set_block_start (tr_flush_block s (fb_buf s) (fb_len s) last) (ds_strstart (tr_flush_block s (fb_buf s) (fb_len s) last))).
Proof. reflexivity. Qed.

Lemma flush_block_eq' : forall s last,
  flush_block s last
  = (flush_block_only s last,
     if cs_avail_out (ds_strm (flush_block_only s last)) =? 0 then Some (if negb (last =? 0) then finish_started else need_more) else None).
Proof. intros s last. unfold flush_block. destruct (_ =? 0); reflexivity. Qed.

(* [comment removed for export] *)
Lemma flush_post10 : forall c0 s last s8,
  C0OK c0 -> dwf s -> SV c0 s -> DXX s -> fb_entry s last -> ds_status s <> FINISH_STATE -> dmode s <> 0 ->
  fb_post s last s8 ->
  let s9 := set_block_start s8 (ds_strstart s8) in
  let s10 := tr_flush_bits s9 in
  DCW c0 s10 /\ PF s10 = PF s /\ TRS s10 = TRS s8
  /\ ds_strstart s10 = ds_strstart s /\ ds_lookahead s10 = ds_lookahead s /\ ds_block_start s10 = ds_strstart s
  /\ ds_match_length s10 = ds_match_length s /\ ds_window s10 = ds_window s
  /\ (exists dt, ds_strm s10 = cset_data_type (ds_strm s) dt)
  /\ ds_sym_next s10 = 0 /\ ds_pending_out s10 = 0
  /\ flush_pending s9 = flush_pending s10.
Proof.
  intros c0 s last s8 HC0 D V XX FE Hst Hm FP s9 s10.
  pose proof (fp_keep _ _ _ FP _ PF keeps_PF) as EPF8. rewrite PF_tfb_X0 in EPF8.
  pose proof (lz_view_fields _ _ (fp_lz _ _ _ FP)) as (Estr8 & Elook8 & Ebs8 & Eml8 & Ewin8 & Ews8).
  destruct (fp_strm _ _ _ FP) as (dt & Estrm8 & Hdt).
  pose proof (fp_biv _ _ _ FP) as Bv8. pose proof (fp_bib _ _ _ FP) as Bb8. pose proof (fp_pending _ _ _ FP) as Pd8.
  pose proof (fp_pout _ _ _ FP) as Po8. pose proof (fp_pbl _ _ _ FP) as Pbl8. pose proof (fp_pbb _ _ _ FP) as Pbb8.
  destruct (tr_flush_bits_shape s9 ltac:(exact Bv8) ltac:(exact Bb8)) as (A & P & B & Bv & E10 & HP & HBv & HB & HA & HAb).
  change (ds_pending s9) with (ds_pending s8) in HP. change (ds_pending_buf s9) with (ds_pending_buf s8) in HA, HAb.
  assert (E10' : s10 = upd4 s9 A P B Bv) by exact E10.
  assert (EPF : PF s10 = PF s) by (rewrite E10', PF_upd4; exact EPF8).
  assert (ETRS : TRS s10 = TRS s8) by (rewrite E10', TRS_upd4; reflexivity).
  pose proof (f_equal (fun s => (ds_strstart s, ds_lookahead s, ds_block_start s, ds_match_length s, ds_window s, ds_strm s, ds_pending_out s)) E10') as EL.
  cbv beta in EL. rewrite lz_upd4 in EL. unfold s9 in EL. rewrite lz_set_block_start in EL.
  apply pair_equal_spec in EL; destruct EL as [EL Epo10]. apply pair_equal_spec in EL; destruct EL as [EL Estrm10].
  apply pair_equal_spec in EL; destruct EL as [EL Ewin10]. apply pair_equal_spec in EL; destruct EL as [EL Eml10].
  apply pair_equal_spec in EL; destruct EL as [EL Ebs10]. apply pair_equal_spec in EL; destruct EL as [Estr10 Elook10].
  pose proof (f_equal (fun s => (ds_pending_buf s, ds_pending s, ds_bi_buf s, ds_bi_valid s)) E10') as EB.
  cbv beta in EB. rewrite bits_upd4 in EB.
  apply pair_equal_spec in EB; destruct EB as [EB Ebv10]. apply pair_equal_spec in EB; destruct EB as [EB Ebb10].
  apply pair_equal_spec in EB; destruct EB as [Epb10 Epd10].
  rewrite Estr8 in Estr10, Ebs10. rewrite Elook8 in Elook10. rewrite Eml8 in Eml10. rewrite Ewin8 in Ewin10. rewrite Estrm8 in Estrm10. rewrite Po8 in Epo10.
  pose proof (PF_fields _ _ EPF) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eih & Eins & Epl & Ema & Epm & Ehw & Ewsz & Ewr) & (Est & Elbs & Ehd & Epv & Ehs & Ewm & Ehm & Ehsh) & (Ewb & Ehb & Epbs & Egz & Eme & Elf & Ese & Ems & EKV)).
  pose proof (KV_fields _ _ EKV) as (Ews & Ehsz & _ & KB).
  pose proof (TRS_fields _ _ ETRS) as ((Eltf & Edtf & Ebtf & Eltd & Edtd & Ebtd) & (Edep & Eblc & Ehp & Eol & Esl & Emt & Esn)).
  rewrite (fp_sn _ _ _ FP) in Esn. rewrite (fp_matches _ _ _ FP) in Emt. rewrite (fp_optlen _ _ _ FP) in Eol. rewrite (fp_statlen _ _ _ FP) in Esl.
  pose proof (PF_fields _ _ EPF8) as (_ & _ & (_ & Elbs8 & _) & _).
  assert (HAb' : forall i, 0 <= i < ds_lit_bufsize s * 4 -> 0 <= arr_get A i < 256).
  { apply HAb. intros i Hi. apply Pbb8. rewrite Pbl8. exact Hi. }
  assert (D10 : dwf s10).
  { pose proof (df_tl _ D) as TL.
    destruct D; constructor; rewrite ?Est, ?Ewb, ?Ews, ?Ewm, ?Ewsz, ?Ehb, ?Ehsz, ?Ehm, ?Ehsh, ?Elbs, ?Epbs, ?Ese, ?Ewin10, ?Epv, ?Ehd, ?Epb10, ?Egz, ?Eme, ?Elv, ?Esy, ?Ewr, ?Estr10, ?Eins, ?Elook10, ?Ems, ?Eih, ?Ehw, ?Elf, ?Epo10, ?Epd10, ?Ebb10, ?Ebv10; try assumption.
    - unfold deflateStateCheck in *. rewrite Est. assumption.
    - congruence.
    - congruence.
    - congruence.
    - congruence.
    - rewrite HA, Pbl8. reflexivity.
    - apply (tree_lens_TRS s8 s10 ETRS). exact (fp_tl _ _ _ FP).
    - clear - HP Pd8. lia.
    - clear - HBv HB. lia. }
  assert (XX10 : DXX s10).
  { apply (DXX_transfer s s10 XX EPF Estr10 Elook10 Eml10 Hm).
    - intros t i. rewrite (tree_dl_TRS s8 s10 t ETRS). apply (fp_dl _ _ _ FP).
    - intros i. rewrite Edep. apply (fp_depth _ _ _ FP).
    - intros i Hi. rewrite Eblc. apply (fp_blc _ _ _ FP). exact Hi. }
  assert (N10 : nsym s10 = 0) by (unfold nsym; rewrite Esn; reflexivity).
  assert (XR10 : DXR s10).
  { constructor; rewrite ?N10, ?Esn, ?Emt, ?Eol, ?Esl, ?Elbs, ?Epd10, ?Epo10, ?Ebv10, ?Estr10, ?Ebs10, ?Ema.
    - clear. lia.
    - reflexivity.
    - pose proof (fe_lbs _ _ FE). clear - H. lia.
    - intros j Hj. exfalso. clear - Hj. lia.
    - unfold freq_hist. rewrite N10, Eltf, Edtf, Ebtf. cbv beta iota delta [Z.to_nat zsum].
      split; [| split]; [intros c Hc; rewrite (fp_ltree _ _ _ FP c Hc); lia | intros d Hd; exact (fp_dtree _ _ _ FP d Hd) | intros b Hb; exact (fp_bltree _ _ _ FP b Hb)].
    - reflexivity.
    - reflexivity.
    - intros _. pose proof (xx_ma _ XX). clear - H. lia.
    - intros t i. rewrite (tree_fc_TRS s8 s10 t ETRS). apply (fp_fc _ _ _ FP).
    - intros _. reflexivity.
    - clear - HBv. lia. }
  assert (V10 : SV c0 s10) by (apply (SV_cset_data_type c0 s s10 dt V Estrm10 Hdt)).
  split; [exact (conj (conj D10 (conj XX10 XR10)) V10)|]. split; [exact EPF|]. split; [exact ETRS|].
  split; [exact Estr10|]. split; [exact Elook10|]. split; [exact Ebs10|]. split; [exact Eml10|]. split; [exact Ewin10|].
  split; [exists dt; exact Estrm10|]. split; [exact Esn|]. split; [exact Epo10|].
  symmetry. apply flush_pending_bits; [exact Bv8 | exact Bb8].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem flush_block_only_factsW : forall c0 s last,
  FB_CALL -> C0OK c0 -> dwf s -> SV c0 s -> DXX s -> fb_entry s last -> ds_status s <> FINISH_STATE -> dmode s <> 0 ->
  let s' := flush_block_only s last in
  flush_ok s last
  /\ DCW c0 s' /\ KV s' = KV s /\ OUTLE s s' /\ PF s' = PF s
  /\ ds_strstart s' = ds_strstart s /\ ds_lookahead s' = ds_lookahead s /\ ds_block_start s' = ds_strstart s
  /\ ds_match_length s' = ds_match_length s /\ ds_window s' = ds_window s
  /\ ds_sym_next s' = 0
  /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
  /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s) /\ cs_next_in (ds_strm s') = cs_next_in (ds_strm s).
Proof.
  intros c0 s last HFB HC0 D V XX FE Hst Hm s'.
  destruct (HFB s last FE) as [FO FP].
  subst s'. rewrite flush_block_only_eq'.
  set (s8 := tr_flush_block s (fb_buf s) (fb_len s) last) in *. clearbody s8.
  pose proof (flush_post10 c0 s last s8 HC0 D V XX FE Hst Hm FP) as H10. cbv zeta in H10.
  destruct H10 as (DC10 & EPF & ETRS & Estr10 & Elook10 & Ebs10 & Eml10 & Ewin10 & (dt & Estrm10) & Esn10 & Epo10 & Efp).
  rewrite Efp.
  set (s10 := tr_flush_bits (set_block_start s8 (ds_strstart s8))) in *. clearbody s10.
  pose proof (DCW_flush_pending c0 s10 HC0 DC10) as HF. cbv zeta in HF.
  pose proof (ml_flush_pending s10) as Eml'. pose proof (PF_flush_pending s10) as EPF'. pose proof (window_flush_pending s10) as Ewin'.
  set (s' := flush_pending s10) in *. clearbody s'.
  destruct HF as (DC' & EKV' & Ho' & Ecore & _ & _ & Hpa & _ & _ & _ & Eain & Enin).
  pose proof (dx_core2_fields _ _ Ecore) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Elook' & Ebs' & Estr' & Esn' & _).
  pose proof (PF_fields _ _ EPF) as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & EKV)).
  split; [exact FO|]. split; [exact DC'|]. split; [rewrite EKV'; exact EKV|].
  split; [apply (OUTLE_trans _ s10); [apply OUTLE_out; rewrite Estrm10; reflexivity | exact Ho']|].
  split; [rewrite EPF'; exact EPF|].
  split; [rewrite Estr'; exact Estr10|]. split; [rewrite Elook'; exact Elook10|]. split; [rewrite Ebs'; exact Ebs10|].
  split; [rewrite Eml'; exact Eml10|]. split; [rewrite Ewin'; exact Ewin10|].
  split; [rewrite Esn'; exact Esn10|]. split; [exact Hpa|].
  rewrite Eain, Enin, Estrm10. unfold cset_data_type; cbn. split; reflexivity.
Qed.

(* [comment removed for export] *)
Theorem flush_block_only_facts : forall c0 s last,
  FB_CALL -> C0OK c0 -> dwf s -> SV c0 s -> DXX s -> fb_entry s last -> ds_status s <> FINISH_STATE -> dmode s <> 0 -> BND s ->
  let s' := flush_block_only s last in
  flush_ok s last
  /\ DC c0 s' /\ KV s' = KV s /\ OUTLE s s' /\ PF s' = PF s
  /\ ds_strstart s' = ds_strstart s /\ ds_lookahead s' = ds_lookahead s /\ ds_block_start s' = ds_strstart s
  /\ ds_match_length s' = ds_match_length s /\ ds_window s' = ds_window s
  /\ ds_sym_next s' = 0
  /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
  /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s) /\ cs_next_in (ds_strm s') = cs_next_in (ds_strm s).
Proof.
  intros c0 s last HFB HC0 D V XX FE Hst Hm B s'.
  pose proof (flush_block_only_factsW c0 s last HFB HC0 D V XX FE Hst Hm) as H. cbv zeta in H. subst s'.
  destruct H as (FO & DC' & HK' & Ho' & EPF & Estr' & Elook' & Ebs' & Eml' & Ewin' & Esn' & Hpa & Eain & Enin).
  split; [exact FO|]. split; [| exact (conj HK' (conj Ho' (conj EPF (conj Estr' (conj Elook' (conj Ebs' (conj Eml' (conj Ewin' (conj Esn' (conj Hpa (conj Eain Enin)))))))))))].
  pose proof (PF_fields _ _ EPF) as (_ & (_ & _ & _ & Ema & _) & (_ & _ & Ehd & Epv & Ehs & Ewm & _) & (_ & _ & _ & _ & _ & _ & _ & Ems & EKV)).
  pose proof (KV_fields _ _ EKV) as (Ews & _).
  apply (DCW_DC c0 _ DC'). apply (BND_same s); try assumption. exact (dmode_PF _ _ EPF).
Qed.

(* [comment removed for export] *)
Lemma DC_fb_entry : forall c0 s last, C0OK c0 -> DC c0 s -> ds_pending s = 0 -> dmode s <> 0 -> 0 <= last <= 1 ->
  fb_entry s last.
Proof.
  intros c0 s last HC0 [[D X] V] Hp Hm Hlast.
  pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
  pose proof (df_pend _ D) as Pd. pose proof (df_bi _ D) as Bi. pose proof (dx_biv _ X) as Bv. pose proof (dx_pout0 _ X Hp) as Po.
  pose proof (sv_dt _ _ V) as Dt. pose proof (sv_tout _ _ V) as To. pose proof (sv_aout _ _ V) as Ao. pose proof (sv_out _ _ V) as Ou.
  pose proof (c0_out _ HC0) as O0. pose proof (c0_aout _ HC0) as A0. rewrite O0 in Ou. unfold zlen in Ou. cbn [length Z.of_nat] in Ou.
  pose proof (zlen_nonneg (cs_out_rev (ds_strm s))) as Zl. unfold zlen in Zl.
  pose proof (df_level _ D) as Lv. pose proof (df_strategy _ D) as Sy. unfold Z_FIXED in Sy.
  pose proof (dx_ext _ X Hm) as He. pose proof (dx_nsym _ X) as Hn. pose proof (dx_ma _ X) as Hma.
  pose proof (df_strstart _ D) as Hstr. pose proof (df_look _ D) as Hlook. pose proof (df_sl _ D) as Hsl.
  assert (Hl : ds_level s <> 0) by (intros E0; apply Hm; unfold dmode; rewrite E0; reflexivity).
  constructor.
  - exact Hlast.
  - clear - He Hn Hma Sl. lia.
  - clear - He Hn Hma Sl Hstr. lia.
  - clear - Hstr Hlook Hsl. lia.
  - clear - Hstr Hlook Hsl. lia.
  - clear - Sw. lia.
  - exact (df_wl _ D).
  - exact (df_wb _ D).
  - clear - Lv Hl. lia.
  - exact Sy.
  - exact Dt.
  - exact Sl.
  - exact (df_bl _ D).
  - exact (df_symend _ D).
  - exact Hp.
  - exact Po.
  - clear - Bv Bi. lia.
  - clear - Bi. lia.
  - rewrite (df_bl _ D). exact (df_bb _ D).
  - rewrite To. apply wrap64_range'.
  - clear - Ao Ou A0 Zl. lia.
  - exact (dx_sn _ X).
  - clear - Hn. lia.
  - exact (dx_syms _ X).
  - exact (dx_hist _ X).
  - exact (dx_opt _ X).
  - exact (dx_stat _ X).
  - exact (df_tl _ D).
  - exact (dx_tfc _ X).
  - exact (dx_tdl _ X).
  - exact (dx_depth _ X).
  - exact (dx_blc _ X).
  - exists (ds_hash_bits s - 1). exact (df_lbs _ D).
Qed.

(* [comment removed for export] *)
Lemma fb_entry_intro : forall c0 s last, C0OK c0 -> dwf s -> SV c0 s ->
  ds_pending s = 0 -> ds_pending_out s = 0 -> ds_bi_valid s <= 7 ->
  BQ s -> nsym s <= ds_lit_bufsize s - 1 -> ds_opt_len s = 0 -> ds_static_len s = 0 ->
  (forall t i, 0 <= arr_get (tree_fc s t) i < 65536) -> (forall t i, 0 <= arr_get (tree_dl s t) i < 65536) ->
  (forall i, 0 <= arr_get (ds_depth s) i < 256) -> (forall i, 0 <= i < 16 -> 0 <= arr_get (ds_bl_count s) i < 65536) ->
  ds_level s <> 0 -> 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s + 1 -> 0 <= last <= 1 ->
  fb_entry s last.
Proof.
  intros c0 s last HC0 D V Hp Po Bv (Q1 & Q2 & Q3 & Q4) Hn Hol Hsl Htfc Htdl Hdep Hblc Hl He Hlast.
  pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
  pose proof (df_bi _ D) as Bi.
  pose proof (sv_dt _ _ V) as Dt. pose proof (sv_tout _ _ V) as To. pose proof (sv_aout _ _ V) as Ao. pose proof (sv_out _ _ V) as Ou.
  pose proof (c0_out _ HC0) as O0. pose proof (c0_aout _ HC0) as A0. rewrite O0 in Ou. unfold zlen in Ou. cbn [length Z.of_nat] in Ou.
  pose proof (zlen_nonneg (cs_out_rev (ds_strm s))) as Zl. unfold zlen in Zl.
  pose proof (df_level _ D) as Lv. pose proof (df_strategy _ D) as Sy. unfold Z_FIXED in Sy.
  pose proof (df_strstart _ D) as Hstr. pose proof (df_look _ D) as Hlook. pose proof (df_sl _ D) as Hsl'.
  constructor.
  - exact Hlast.
  - clear - He Hn Q2 Sl. lia.
  - clear - He Hn Q2 Sl Hstr. lia.
  - clear - Hstr Hlook Hsl'. lia.
  - clear - Hstr Hlook Hsl'. lia.
  - clear - Sw. lia.
  - exact (df_wl _ D).
  - exact (df_wb _ D).
  - clear - Lv Hl. lia.
  - exact Sy.
  - exact Dt.
  - exact Sl.
  - exact (df_bl _ D).
  - exact (df_symend _ D).
  - exact Hp.
  - exact Po.
  - clear - Bv Bi. lia.
  - clear - Bi. lia.
  - rewrite (df_bl _ D). exact (df_bb _ D).
  - rewrite To. apply wrap64_range'.
  - clear - Ao Ou A0 Zl. lia.
  - exact Q1.
  - clear - Hn Q2. lia.
  - exact Q3.
  - exact Q4.
  - exact Hol.
  - exact Hsl.
  - exact (df_tl _ D).
  - exact Htfc.
  - exact Htdl.
  - exact Hdep.
  - exact Hblc.
  - exists (ds_hash_bits s - 1). exact (df_lbs _ D).
Qed.
