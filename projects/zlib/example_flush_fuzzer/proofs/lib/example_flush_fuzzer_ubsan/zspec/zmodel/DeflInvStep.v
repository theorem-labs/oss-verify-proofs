(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz Deflate DeflateInvHash DeflateInvKeep OverlayFBS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflInvTally DeflInvLm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac dtac I := destruct I; constructor; unfold lz_strat in *; dsr; try assumption;
  try (solve [auto with cty]);
  try (lazymatch goal with Hs : (exists syms, dsyms syms _ /\ _) |- ex _ =>
         destruct Hs as (sy_ & D_ & C_); exists sy_; split; [eapply dsyms_keep; [exact D_ | dsr; reflexivity ..] | dsr; exact C_] end).


Lemma dinv_set_lookahead : forall rm hb fz s v, dinvR rm hb fz s ->
  0 <= v -> ds_strstart s + v <= 2 * ds_w_size s ->
  (fz = true -> 4 <= ds_level s -> lz_strat s -> MIN_MATCH <= ds_match_length s -> ds_match_length s <= v + 1) ->
  (ds_wrap s < 0 -> v = 0) -> (ds_level s = 0 -> v = 0) -> v <= ds_lookahead s ->
  dinvR rm hb fz (set_lookahead s v).
Proof.
  intros rm hb fz s v I H1 H2 H3 H4 H5 H6. dtac I.
  - intros Fz A B C. destruct (di_slow Fz A B C) as (X & Y & _). split; [exact X|]. split; [exact Y|]. exact (H3 Fz A B C).
  - intros W. split; [exact (proj1 (di_negwrap W)) | exact (H4 W)].
  - intros F. pose proof (di_finlook F) as X. clear -X H1 H6. lia.
Qed.

Lemma dinv_set_ins_h : forall rm hb fz s v, dinvR rm hb fz s -> 0 <= v < 2 ^ 16 -> dinvR rm hb fz (set_ins_h s v).
Proof. intros rm hb fz s v I H. dtac I. Qed.

Lemma dinv_set_insert : forall rm hb fz s v, dinvR rm hb fz s -> 0 <= v <= ds_strstart s -> dinvR rm hb fz (set_insert s v).
Proof. intros rm hb fz s v I H. dtac I. Qed.

Lemma dinv_set_prev_match : forall rm hb fz s v, dinvR rm hb fz s -> 0 <= v < 2 ^ 32 -> dinvR rm hb fz (set_prev_match s v).
Proof. intros rm hb fz s v I H. dtac I. Qed.

Lemma dinv_set_prev_length : forall rm hb fz s v, dinvR rm hb fz s -> 0 <= v <= MAX_MATCH ->
  (1 <= ds_level s <= 3 -> lz_strat s -> v = MIN_MATCH - 1) -> dinvR rm hb fz (set_prev_length s v).
Proof. intros rm hb fz s v I H1 H2. dtac I. Qed.

Lemma dinv_set_match_start : forall rm hb fz s v, dinvR rm hb fz s -> 0 <= v < 2 ^ 32 ->
  (fz = true -> 4 <= ds_level s -> lz_strat s -> MIN_MATCH <= ds_match_length s -> 1 <= wrap32 (ds_strstart s - 1 - v) <= ds_w_size s - MIN_LOOKAHEAD) ->
  dinvR rm hb fz (set_match_start s v).
Proof.
  intros rm hb fz s v I H1 H2. dtac I.
  intros Fz A B C. destruct (di_slow Fz A B C) as (X & _ & Y). split; [exact X|]. split; [exact (H2 Fz A B C) | exact Y].
Qed.

Lemma dinv_set_match_length : forall rm hb fz fz' s v, dinvR rm hb fz s -> 0 <= v <= MAX_MATCH ->
  (fz' = true -> 1 <= ds_level s <= 3 -> lz_strat s -> v < MIN_MATCH) ->
  (fz' = true -> 4 <= ds_level s -> lz_strat s -> MIN_MATCH <= v ->
     1 <= ds_strstart s /\ 1 <= wrap32 (ds_strstart s - 1 - ds_match_start s) <= ds_w_size s - MIN_LOOKAHEAD /\ v <= ds_lookahead s + 1) ->
  (4 <= ds_level s -> lz_strat s -> 1 <= v) ->
  dinvR rm hb fz' (set_match_length s v).
Proof. intros rm hb fz fz' s v I H1 H2 H3 H4. dtac I. Qed.

Lemma dinv_set_strm : forall rm hb fz s st, dinvR rm hb fz s -> u8a (cs_input st) -> dinvR rm hb fz (set_strm s st).
Proof. intros rm hb fz s st I H. dtac I. destruct di_cty; constructor; dsr; assumption. Qed.

Lemma dinv_zin : forall rm hb fz s, dinvR rm hb fz s -> dinvR rm hb fz (zin s).
Proof. intros rm hb fz s I. unfold zin. apply dinv_set_strm; [exact I | exact u8a_arr0]. Qed.

Lemma DI_of : forall s, dcfg s -> dinv s -> DI s.
Proof. intros s C I. split; [exact C | exact (dinv_zin _ _ _ s I)]. Qed.


Lemma dinv_set_match_available : forall rm hb fz s v, dinvR rm hb fz s -> (v = 0 \/ v = 1) -> (v = 1 -> 1 <= ds_strstart s) ->
  (ds_level s <> 0 -> exists syms, dsyms syms s /\ ds_strstart s - ds_block_start s <= zcov syms + v) ->
  (v <> 0 -> 4 <= ds_level s /\ lz_strat s) ->
  dinvR rm hb fz (set_match_available s v).
Proof.
  intros rm hb fz s v I H1 H2 H3 H4. pose proof (di_syms _ _ _ _ I) as (syms0 & D0 & _). unfold lz_strat in H4. dtac I.
  destruct (Z.eq_dec (ds_level s) 0) as [Z0|Z0].
  - exists syms0. split; [eapply dsyms_keep; [exact D0 | reflexivity ..]|]. intros X. exfalso. exact (X Z0).
  - destruct (H3 Z0) as (syms & D & C). exists syms. split; [eapply dsyms_keep; [exact D | reflexivity ..] | intros _; exact C].
Qed.

Lemma dinv_set_strstart : forall rm hb fz hb' s v, dinvR rm hb fz s ->
  ds_strstart s <= v -> v + ds_lookahead s <= 2 * ds_w_size s -> ds_strstart s + hb <= v + hb' ->
  (ds_level s <> 0 -> exists syms, dsyms syms s /\ v - ds_block_start s <= zcov syms + ds_match_available s) ->
  (fz = true -> 4 <= ds_level s -> lz_strat s -> MIN_MATCH <= ds_match_length s -> 1 <= wrap32 (v - 1 - ds_match_start s) <= ds_w_size s - MIN_LOOKAHEAD) ->
  dinvR rm hb' fz (set_strstart s v).
Proof.
  intros rm hb fz hb' s v I H1 H2 H3 H4 H5. pose proof (di_syms _ _ _ _ I) as (syms0 & D0 & _).
  pose proof (di_str _ _ _ _ I) as Pstr. pose proof (di_ins _ _ _ _ I) as Pins. pose proof (di_bs _ _ _ _ I) as Pbs.
  dtac I.
  - clear -H1 Pstr. lia.
  - clear -H1 Pins. lia.
  - clear -H1 Pbs. lia.
  - intros M L. pose proof (di_ma1 M L) as X. clear -H1 X. lia.
  - intros Fz A B C. destruct (di_slow Fz A B C) as (X & _ & Y). split; [clear -X H1; lia|]. split; [exact (H5 Fz A B C) | exact Y].
  - intros L. destruct (di_hash L) as [Ins HC]. exists Ins. dsr. apply (hc_inv_str_le _ _ _ _ _ _ _ HC). clear -H3. lia.
  - destruct (Z.eq_dec (ds_level s) 0) as [Z0|Z0].
    + exists syms0. split; [eapply dsyms_keep; [exact D0 | reflexivity ..]|]. intros X. exfalso. exact (X Z0).
    + destruct (H4 Z0) as (syms & D & C). exists syms. split; [eapply dsyms_keep; [exact D | reflexivity ..] | intros _; exact C].
Qed.


Lemma tally_lit_T : forall s c, let s' := fst (tr_tally_lit s c) in
  ds_pending s' = ds_pending s /\ ds_bi_valid s' = ds_bi_valid s /\ ds_bi_buf s' = ds_bi_buf s /\ kproj s' = kproj (set_sym_next s (ds_sym_next s + 3)).
Proof. intros s c. cbv zeta. split; [| split; [| split; [| apply kp_tr_tally_lit]]]; destruct s; reflexivity. Qed.
Lemma tally_dist_T : forall s d l, let s' := fst (tr_tally_dist s d l) in
  ds_pending s' = ds_pending s /\ ds_bi_valid s' = ds_bi_valid s /\ ds_bi_buf s' = ds_bi_buf s /\ kproj s' = kproj (set_sym_next s (ds_sym_next s + 3)).
Proof. intros s d l. cbv zeta. split; [| split; [| split; [| apply kp_tr_tally_dist]]]; destruct s; reflexivity. Qed.

Local Ltac kpf K lem Xset := let E := fresh in pose proof (lem _ _ K) as E; rewrite ?Xset in E; exact E.

Section TallyInv.
  Variables (rm hb : Z) (fz : bool) (s : deflate_state).
  Hypothesis C : dcfg s.
  Hypothesis I : dinvR 3 hb fz s.
  Hypothesis Lz : ds_level s <> 0.
  Hypothesis P0 : ds_pending s = 0.
  Hypothesis SB : ds_status s = BUSY_STATE.

  Let SZ := dcfg_sizes s C.

  Lemma dinv_tally_lit : forall c, 0 <= c < 256 ->
    let '(s', bflush) := tr_tally_lit s c in
    dinvR (if bflush then 0 else 3) hb fz s'
    /\ (exists syms, dsyms syms s /\ dsyms (syms ++ [(0, c)]) s')
    /\ bflush = (ds_sym_next s' =? ds_sym_end s')
    /\ ds_pending s' = ds_pending s /\ ds_bi_valid s' = ds_bi_valid s /\ ds_bi_buf s' = ds_bi_buf s
    /\ kproj s' = kproj (set_sym_next s (ds_sym_next s + 3)).
  Proof.
    intros c Hc. pose proof SZ as (Sw & Sh & Sl & Shl).
    destruct (di_syms _ _ _ _ I) as (syms & D & COV).
    pose proof (cf_tl _ C) as TL9. pose proof TL9 as (L1 & _ & L3 & _).
    destruct (dsyms_tally_lit syms s D ltac:(rewrite (cf_bl _ C); lia) ltac:(rewrite (cf_symend _ C); lia) ltac:(lia) (di_room _ _ _ _ I) L1
                ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; lia) c Hc) as [D' Hb].
    destruct (tally_lit_T s c) as (P1 & P2 & P3 & K).
    pose proof (cty_tr_tally_lit s c (di_cty _ _ _ _ I)) as T'.
    destruct (tr_tally_lit s c) as [s' bflush]. cbn [fst snd] in *.
    pose proof (sy_next _ _ D') as SN'. rewrite length_app1 in SN'. pose proof (sy_next _ _ D) as SN.
    assert (SE : ds_sym_end s' = ds_sym_end s) by kpf K kp_sym_end sym_end_set_sym_next.
    split; [| split; [exists syms; split; assumption | split; [rewrite Hb, SN', SE; reflexivity | split; [exact P1 | split; [exact P2 | split; [exact P3 | exact K]]]]]].
    pose proof I as [_ Istr Ilook Isl Iins Ibs Ibs0 Ihw Iih Ims Ipm Iml Ipl Ima Ima1 Imt Ifast Ifastpl Islow Islow1 Ihash Isyms Iroom Ibv Ibb Ipend Ipout Ipop Ipo0 Ipobv Ilf Ilive Iinit Igz Ineg Ilk0 Isn0 Iinw Ifl Imas Ips].
    constructor; unfold lz_strat, dhashb in *;
      try (kpf K kp_strstart strstart_set_sym_next || idtac);
      rewrite ?(kp_strstart _ _ K), ?(kp_lookahead _ _ K), ?(kp_w_size _ _ K), ?(kp_insert _ _ K), ?(kp_block_start _ _ K), ?(kp_level _ _ K),
              ?(kp_high_water _ _ K), ?(kp_ins_h _ _ K), ?(kp_match_start _ _ K), ?(kp_prev_match _ _ K), ?(kp_match_length _ _ K),
              ?(kp_prev_length _ _ K), ?(kp_match_available _ _ K), ?(kp_matches _ _ K), ?(kp_strategy _ _ K), ?(kp_head _ _ K),
              ?(kp_prev _ _ K), ?(kp_hash_size _ _ K), ?(kp_lit_bufsize _ _ K), ?(kp_pending_out _ _ K), ?(kp_last_flush _ _ K),
              ?(kp_status _ _ K), ?(kp_wrap _ _ K), ?SE, ?SN', ?P1, ?P2, ?P3; dsf; try assumption.
    - exists (syms ++ [(0, c)]). split; [exact D'|]. intros L. rewrite zcov_app1, (Z.eqb_refl 0). specialize (COV L). clear -COV. lia.
    - pose proof (cf_symend _ C) as SE0. symmetry in Hb. destruct bflush.
      + apply Z.eqb_eq in Hb. clear -Hb. lia.
      + apply Z.eqb_neq in Hb. rewrite SE0 in Hb. rewrite SE0, SN in Iroom. rewrite SE0. clear -Hb Iroom. lia.
    - first [ intros X; exfalso; rewrite SB in X; first [ destruct X as [X|X]; discriminate X | discriminate X ]
            | intros L0; exfalso; exact (Lz L0)
            | rewrite P0; intros X; exfalso; exact (X eq_refl) ].
    - first [ intros X; exfalso; rewrite SB in X; first [ destruct X as [X|X]; discriminate X | discriminate X ]
            | intros L0; exfalso; exact (Lz L0)
            | rewrite P0; intros X; exfalso; exact (X eq_refl) ].
    - first [ intros X; exfalso; rewrite SB in X; first [ destruct X as [X|X]; discriminate X | discriminate X ]
            | intros L0; exfalso; exact (Lz L0)
            | rewrite P0; intros X; exfalso; exact (X eq_refl) ].
    - first [ intros X; exfalso; rewrite SB in X; first [ destruct X as [X|X]; discriminate X | discriminate X ]
            | intros L0; exfalso; exact (Lz L0)
            | rewrite P0; intros X; exfalso; exact (X eq_refl) ].
  Qed.
  Lemma dinv_tally_dist : forall d lc, 1 <= d <= ds_w_size s - MIN_LOOKAHEAD -> 0 <= lc <= 255 ->
    let '(s', bflush) := tr_tally_dist s d lc in
    dinvR (if bflush then 0 else 3) hb fz s'
    /\ (exists syms, dsyms syms s /\ dsyms (syms ++ [(d, lc)]) s')
    /\ bflush = (ds_sym_next s' =? ds_sym_end s')
    /\ ds_pending s' = ds_pending s /\ ds_bi_valid s' = ds_bi_valid s /\ ds_bi_buf s' = ds_bi_buf s
    /\ kproj s' = kproj (set_sym_next s (ds_sym_next s + 3)).
  Proof.
    intros d lc Hd Hlc. pose proof SZ as (Sw & Sh & Sl & Shl).
    destruct (di_syms _ _ _ _ I) as (syms & D & COV).
    pose proof (cf_tl _ C) as TL9. pose proof TL9 as (L1 & _ & L3 & _).
    destruct (dsyms_tally_dist syms s D ltac:(rewrite (cf_bl _ C); lia) ltac:(rewrite (cf_symend _ C); lia) ltac:(lia) (di_room _ _ _ _ I) L1 L3
                ltac:(lia) d lc Hd Hlc) as [D' Hb].
    destruct (tally_dist_T s d lc) as (P1 & P2 & P3 & K).
    pose proof (cty_tr_tally_dist s d lc (di_cty _ _ _ _ I)) as T'.
    destruct (tr_tally_dist s d lc) as [s' bflush]. cbn [fst snd] in *.
    pose proof (sy_next _ _ D') as SN'. rewrite length_app1 in SN'. pose proof (sy_next _ _ D) as SN.
    assert (SE : ds_sym_end s' = ds_sym_end s) by kpf K kp_sym_end sym_end_set_sym_next.
    split; [| split; [exists syms; split; assumption | split; [rewrite Hb, SN', SE; reflexivity | split; [exact P1 | split; [exact P2 | split; [exact P3 | exact K]]]]]].
    pose proof I as [_ Istr Ilook Isl Iins Ibs Ibs0 Ihw Iih Ims Ipm Iml Ipl Ima Ima1 Imt Ifast Ifastpl Islow Islow1 Ihash Isyms Iroom Ibv Ibb Ipend Ipout Ipop Ipo0 Ipobv Ilf Ilive Iinit Igz Ineg Ilk0 Isn0 Iinw Ifl Imas Ips].
    constructor; unfold lz_strat, dhashb in *;
      try (kpf K kp_strstart strstart_set_sym_next || idtac);
      rewrite ?(kp_strstart _ _ K), ?(kp_lookahead _ _ K), ?(kp_w_size _ _ K), ?(kp_insert _ _ K), ?(kp_block_start _ _ K), ?(kp_level _ _ K),
              ?(kp_high_water _ _ K), ?(kp_ins_h _ _ K), ?(kp_match_start _ _ K), ?(kp_prev_match _ _ K), ?(kp_match_length _ _ K),
              ?(kp_prev_length _ _ K), ?(kp_match_available _ _ K), ?(kp_matches _ _ K), ?(kp_strategy _ _ K), ?(kp_head _ _ K),
              ?(kp_prev _ _ K), ?(kp_hash_size _ _ K), ?(kp_lit_bufsize _ _ K), ?(kp_pending_out _ _ K), ?(kp_last_flush _ _ K),
              ?(kp_status _ _ K), ?(kp_wrap _ _ K), ?SE, ?SN', ?P1, ?P2, ?P3; dsf; try assumption.
    - exists (syms ++ [(d, lc)]). split; [exact D'|]. intros L. rewrite zcov_app1. replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; lia). specialize (COV L). unfold MIN_MATCH. clear -COV Hlc. lia.
    - pose proof (cf_symend _ C) as SE0. symmetry in Hb. destruct bflush.
      + apply Z.eqb_eq in Hb. clear -Hb. lia.
      + apply Z.eqb_neq in Hb. rewrite SE0 in Hb. rewrite SE0, SN in Iroom. rewrite SE0. clear -Hb Iroom. lia.
    - first [ intros X; exfalso; rewrite SB in X; first [ destruct X as [X|X]; discriminate X | discriminate X ]
            | intros L0; exfalso; exact (Lz L0)
            | rewrite P0; intros X; exfalso; exact (X eq_refl) ].
    - first [ intros X; exfalso; rewrite SB in X; first [ destruct X as [X|X]; discriminate X | discriminate X ]
            | intros L0; exfalso; exact (Lz L0)
            | rewrite P0; intros X; exfalso; exact (X eq_refl) ].
    - first [ intros X; exfalso; rewrite SB in X; first [ destruct X as [X|X]; discriminate X | discriminate X ]
            | intros L0; exfalso; exact (Lz L0)
            | rewrite P0; intros X; exfalso; exact (X eq_refl) ].
    - first [ intros X; exfalso; rewrite SB in X; first [ destruct X as [X|X]; discriminate X | discriminate X ]
            | intros L0; exfalso; exact (Lz L0)
            | rewrite P0; intros X; exfalso; exact (X eq_refl) ].
  Qed.
End TallyInv.

Record snf (b a : deflate_state) : Prop := MkSNF {
  sn_status : ds_status a = ds_status b;
  sn_pending_buf_size : ds_pending_buf_size a = ds_pending_buf_size b;
  sn_pending_out : ds_pending_out a = ds_pending_out b;
  sn_wrap : ds_wrap a = ds_wrap b;
  sn_gzhead : ds_gzhead a = ds_gzhead b;
  sn_gzindex : ds_gzindex a = ds_gzindex b;
  sn_method : ds_method a = ds_method b;
  sn_last_flush : ds_last_flush a = ds_last_flush b;
  sn_w_size : ds_w_size a = ds_w_size b;
  sn_w_bits : ds_w_bits a = ds_w_bits b;
  sn_w_mask : ds_w_mask a = ds_w_mask b;
  sn_window : ds_window a = ds_window b;
  sn_window_size : ds_window_size a = ds_window_size b;
  sn_prev : ds_prev a = ds_prev b;
  sn_head : ds_head a = ds_head b;
  sn_ins_h : ds_ins_h a = ds_ins_h b;
  sn_hash_size : ds_hash_size a = ds_hash_size b;
  sn_hash_bits : ds_hash_bits a = ds_hash_bits b;
  sn_hash_mask : ds_hash_mask a = ds_hash_mask b;
  sn_hash_shift : ds_hash_shift a = ds_hash_shift b;
  sn_block_start : ds_block_start a = ds_block_start b;
  sn_match_length : ds_match_length a = ds_match_length b;
  sn_prev_match : ds_prev_match a = ds_prev_match b;
  sn_match_available : ds_match_available a = ds_match_available b;
  sn_strstart : ds_strstart a = ds_strstart b;
  sn_match_start : ds_match_start a = ds_match_start b;
  sn_lookahead : ds_lookahead a = ds_lookahead b;
  sn_prev_length : ds_prev_length a = ds_prev_length b;
  sn_max_chain_length : ds_max_chain_length a = ds_max_chain_length b;
  sn_max_lazy_match : ds_max_lazy_match a = ds_max_lazy_match b;
  sn_level : ds_level a = ds_level b;
  sn_strategy : ds_strategy a = ds_strategy b;
  sn_good_match : ds_good_match a = ds_good_match b;
  sn_nice_match : ds_nice_match a = ds_nice_match b;
  sn_lit_bufsize : ds_lit_bufsize a = ds_lit_bufsize b;
  sn_sym_end : ds_sym_end a = ds_sym_end b;
  sn_matches : ds_matches a = ds_matches b;
  sn_insert : ds_insert a = ds_insert b;
  sn_high_water : ds_high_water a = ds_high_water b;
  sn_self_blk : ds_self_blk a = ds_self_blk b;
  sn_window_blk : ds_window_blk a = ds_window_blk b;
  sn_prev_blk : ds_prev_blk a = ds_prev_blk b;
  sn_head_blk : ds_head_blk a = ds_head_blk b;
  sn_pending_buf_blk : ds_pending_buf_blk a = ds_pending_buf_blk b;
  sn_strm : ds_strm a = ds_strm b;
  sn_len : arr_len (ds_pending_buf a) = arr_len (ds_pending_buf b) }.
Lemma kp_sn_fields : forall a b v, kproj a = kproj (set_sym_next b v) -> snf b a.
Proof.
  intros a b v K. constructor.
  - pose proof (kp_status _ _ K) as E. rewrite status_set_sym_next in E. exact E.
  - pose proof (kp_pending_buf_size _ _ K) as E. rewrite pending_buf_size_set_sym_next in E. exact E.
  - pose proof (kp_pending_out _ _ K) as E. rewrite pending_out_set_sym_next in E. exact E.
  - pose proof (kp_wrap _ _ K) as E. rewrite wrap_set_sym_next in E. exact E.
  - pose proof (kp_gzhead _ _ K) as E. rewrite gzhead_set_sym_next in E. exact E.
  - pose proof (kp_gzindex _ _ K) as E. rewrite gzindex_set_sym_next in E. exact E.
  - pose proof (kp_method _ _ K) as E. rewrite method_set_sym_next in E. exact E.
  - pose proof (kp_last_flush _ _ K) as E. rewrite last_flush_set_sym_next in E. exact E.
  - pose proof (kp_w_size _ _ K) as E. rewrite w_size_set_sym_next in E. exact E.
  - pose proof (kp_w_bits _ _ K) as E. rewrite w_bits_set_sym_next in E. exact E.
  - pose proof (kp_w_mask _ _ K) as E. rewrite w_mask_set_sym_next in E. exact E.
  - pose proof (kp_window _ _ K) as E. rewrite window_set_sym_next in E. exact E.
  - pose proof (kp_window_size _ _ K) as E. rewrite window_size_set_sym_next in E. exact E.
  - pose proof (kp_prev _ _ K) as E. rewrite prev_set_sym_next in E. exact E.
  - pose proof (kp_head _ _ K) as E. rewrite head_set_sym_next in E. exact E.
  - pose proof (kp_ins_h _ _ K) as E. rewrite ins_h_set_sym_next in E. exact E.
  - pose proof (kp_hash_size _ _ K) as E. rewrite hash_size_set_sym_next in E. exact E.
  - pose proof (kp_hash_bits _ _ K) as E. rewrite hash_bits_set_sym_next in E. exact E.
  - pose proof (kp_hash_mask _ _ K) as E. rewrite hash_mask_set_sym_next in E. exact E.
  - pose proof (kp_hash_shift _ _ K) as E. rewrite hash_shift_set_sym_next in E. exact E.
  - pose proof (kp_block_start _ _ K) as E. rewrite block_start_set_sym_next in E. exact E.
  - pose proof (kp_match_length _ _ K) as E. rewrite match_length_set_sym_next in E. exact E.
  - pose proof (kp_prev_match _ _ K) as E. rewrite prev_match_set_sym_next in E. exact E.
  - pose proof (kp_match_available _ _ K) as E. rewrite match_available_set_sym_next in E. exact E.
  - pose proof (kp_strstart _ _ K) as E. rewrite strstart_set_sym_next in E. exact E.
  - pose proof (kp_match_start _ _ K) as E. rewrite match_start_set_sym_next in E. exact E.
  - pose proof (kp_lookahead _ _ K) as E. rewrite lookahead_set_sym_next in E. exact E.
  - pose proof (kp_prev_length _ _ K) as E. rewrite prev_length_set_sym_next in E. exact E.
  - pose proof (kp_max_chain_length _ _ K) as E. rewrite max_chain_length_set_sym_next in E. exact E.
  - pose proof (kp_max_lazy_match _ _ K) as E. rewrite max_lazy_match_set_sym_next in E. exact E.
  - pose proof (kp_level _ _ K) as E. rewrite level_set_sym_next in E. exact E.
  - pose proof (kp_strategy _ _ K) as E. rewrite strategy_set_sym_next in E. exact E.
  - pose proof (kp_good_match _ _ K) as E. rewrite good_match_set_sym_next in E. exact E.
  - pose proof (kp_nice_match _ _ K) as E. rewrite nice_match_set_sym_next in E. exact E.
  - pose proof (kp_lit_bufsize _ _ K) as E. rewrite lit_bufsize_set_sym_next in E. exact E.
  - pose proof (kp_sym_end _ _ K) as E. rewrite sym_end_set_sym_next in E. exact E.
  - pose proof (kp_matches _ _ K) as E. rewrite matches_set_sym_next in E. exact E.
  - pose proof (kp_insert _ _ K) as E. rewrite insert_set_sym_next in E. exact E.
  - pose proof (kp_high_water _ _ K) as E. rewrite high_water_set_sym_next in E. exact E.
  - pose proof (kp_self_blk _ _ K) as E. rewrite self_blk_set_sym_next in E. exact E.
  - pose proof (kp_window_blk _ _ K) as E. rewrite window_blk_set_sym_next in E. exact E.
  - pose proof (kp_prev_blk _ _ K) as E. rewrite prev_blk_set_sym_next in E. exact E.
  - pose proof (kp_head_blk _ _ K) as E. rewrite head_blk_set_sym_next in E. exact E.
  - pose proof (kp_pending_buf_blk _ _ K) as E. rewrite pending_buf_blk_set_sym_next in E. exact E.
  - pose proof (kp_strm _ _ K) as E. rewrite strm_set_sym_next in E. exact E.
  - pose proof (kp_len_pending_buf _ _ K) as E. rewrite pending_buf_set_sym_next in E. exact E.
Qed.


Lemma insert_string_fields : forall s str,
  let '(s', hh) := insert_string s str in
  let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) in
  hh = arr_get (ds_head s) h
  /\ ds_ins_h s' = h
  /\ ds_prev s' = arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) h)
  /\ ds_head s' = arr_set (ds_head s) h (wrap16 str)
  /\ kproj (set_head (set_prev (set_ins_h s' (ds_ins_h s)) (ds_prev s)) (ds_head s)) = kproj s
  /\ ds_pending s' = ds_pending s /\ ds_bi_valid s' = ds_bi_valid s /\ ds_bi_buf s' = ds_bi_buf s
  /\ ds_opt_len s' = ds_opt_len s /\ ds_static_len s' = ds_static_len s /\ ds_pending_buf s' = ds_pending_buf s
  /\ ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s /\ ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s /\ ds_bl_tree_fc s' = ds_bl_tree_fc s.
Proof. intros s str. unfold insert_string. destruct s; repeat split; reflexivity. Qed.

Section InsertInv.
  Variables (rm : Z) (fz : bool) (s : deflate_state).
  Hypothesis C : dcfg s.
  Hypothesis I : dinvR rm 0 fz s.
  Hypothesis HL : ds_strstart s + MIN_MATCH <= 2 * ds_w_size s.

  Lemma dinv_insert_string_gen :
    let '(s', hh) := insert_string s (ds_strstart s) in
    dinvR rm 1 fz s'
    /\ 0 <= hh < 65536
    /\ kproj (set_head (set_prev (set_ins_h s' (ds_ins_h s)) (ds_prev s)) (ds_head s)) = kproj s
    /\ ds_pending s' = ds_pending s /\ ds_bi_valid s' = ds_bi_valid s /\ ds_bi_buf s' = ds_bi_buf s
    /\ (ds_level s <> 0 -> exists Ins, (hh <> 0 -> Ins hh) /\ chain_inv Ins (ds_strstart s) (ds_w_size s) (ds_prev s')).
  Proof.
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof (insert_string_fields s (ds_strstart s)) as IF.
    pose proof (cty_insert_string s (ds_strstart s) (di_cty _ _ _ _ I) ltac:(rewrite (cf_hmask _ C), (cf_hl _ C); lia)) as T'.
    destruct (insert_string s (ds_strstart s)) as [s' hh]. cbn [fst snd] in *.
    destruct IF as (Ehh & Eih & Epv & Ehd & K & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    set (h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (ds_strstart s + (MIN_MATCH - 1)))) in *.
    assert (Hh : 0 <= h < ds_hash_size s).
    { subst h. pose proof (update_hash_lt s (ds_ins_h s) (arr_get (ds_window s) (ds_strstart s + (MIN_MATCH - 1))) ltac:(rewrite (cf_hmask _ C), (cf_hl _ C); lia)) as X.
      rewrite (cf_hl _ C) in X. exact X. }
    assert (Hhh : 0 <= hh < 65536).
    { rewrite Ehh. apply (ct_head _ (di_cty _ _ _ _ I)). rewrite (cf_hl _ C). exact Hh. }
    assert (POW : Z.land (ds_strstart s) (ds_w_mask s) = ds_strstart s mod ds_w_size s).
    { rewrite (cf_wmask _ C), (cf_wsize _ C). pose proof (cf_wbits _ C).
      replace (2 ^ ds_w_bits s - 1) with (Z.ones (ds_w_bits s)) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia). apply Z.land_ones. lia. }
    rewrite POW in Epv.
    assert (KF : forall (f : deflate_state -> Z), (forall x a, f (set_head x a) = f x) -> (forall x a, f (set_prev x a) = f x) -> (forall x a, f (set_ins_h x a) = f x) ->
                 (forall b a, kproj a = kproj b -> f a = f b) -> f s' = f s).
    { intros f E1 E2 E3 E4. rewrite <- (E4 _ _ K), E1, E2, E3. reflexivity. }
    pose proof (KF ds_strstart strstart_set_head strstart_set_prev strstart_set_ins_h kp_strstart) as Fstr.
    pose proof (KF ds_lookahead lookahead_set_head lookahead_set_prev lookahead_set_ins_h kp_lookahead) as Flook.
    pose proof (KF ds_w_size w_size_set_head w_size_set_prev w_size_set_ins_h kp_w_size) as Fws.
    pose proof (KF ds_insert insert_set_head insert_set_prev insert_set_ins_h kp_insert) as Fins.
    pose proof (KF ds_block_start block_start_set_head block_start_set_prev block_start_set_ins_h kp_block_start) as Fbs.
    pose proof (KF ds_level level_set_head level_set_prev level_set_ins_h kp_level) as Flv.
    pose proof (KF ds_high_water high_water_set_head high_water_set_prev high_water_set_ins_h kp_high_water) as Fhw.
    pose proof (KF ds_match_start match_start_set_head match_start_set_prev match_start_set_ins_h kp_match_start) as Fms.
    pose proof (KF ds_prev_match prev_match_set_head prev_match_set_prev prev_match_set_ins_h kp_prev_match) as Fpm.
    pose proof (KF ds_match_length match_length_set_head match_length_set_prev match_length_set_ins_h kp_match_length) as Fml.
    pose proof (KF ds_prev_length prev_length_set_head prev_length_set_prev prev_length_set_ins_h kp_prev_length) as Fpl.
    pose proof (KF ds_match_available match_available_set_head match_available_set_prev match_available_set_ins_h kp_match_available) as Fma.
    pose proof (KF ds_matches matches_set_head matches_set_prev matches_set_ins_h kp_matches) as Fmt.
    pose proof (KF ds_strategy strategy_set_head strategy_set_prev strategy_set_ins_h kp_strategy) as Fsg.
    pose proof (KF ds_hash_size hash_size_set_head hash_size_set_prev hash_size_set_ins_h kp_hash_size) as Fhs.
    pose proof (KF ds_sym_next sym_next_set_head sym_next_set_prev sym_next_set_ins_h kp_sym_next) as Fsn.
    pose proof (KF ds_sym_end sym_end_set_head sym_end_set_prev sym_end_set_ins_h kp_sym_end) as Fse.
    pose proof (KF ds_lit_bufsize lit_bufsize_set_head lit_bufsize_set_prev lit_bufsize_set_ins_h kp_lit_bufsize) as Flb.
    pose proof (KF ds_pending_out pending_out_set_head pending_out_set_prev pending_out_set_ins_h kp_pending_out) as Fpo.
    pose proof (KF ds_last_flush last_flush_set_head last_flush_set_prev last_flush_set_ins_h kp_last_flush) as Flf.
    pose proof (KF ds_status status_set_head status_set_prev status_set_ins_h kp_status) as Fst.
    pose proof (KF ds_wrap wrap_set_head wrap_set_prev wrap_set_ins_h kp_wrap) as Fwr.
    assert (HASH : ds_level s <> 0 ->
              (exists Ins, (hh <> 0 -> Ins hh) /\ chain_inv Ins (ds_strstart s) (ds_w_size s) (ds_prev s'))
              /\ dhashb 1 s').
    { intros L. destruct (di_hash _ _ _ _ I L) as [Ins HC]. rewrite Z.add_0_r in HC. split.
      - exists Ins. split.
        + intros Hz. rewrite Ehh in Hz |- *. destruct (proj1 (proj2 HC) h Hh) as [E0 | In]; [exfalso; exact (Hz E0) | exact In].
        + rewrite Epv. apply chain_set_slot; [lia|]. exact (hc_chain _ _ _ _ _ _ HC).
      - exists (fun q => Ins q \/ q = ds_strstart s). rewrite Fstr, Fws, Fhs, Ehd, Epv.
        pose proof (di_str _ _ _ _ I). pose proof (di_sl _ _ _ _ I). pose proof (di_look _ _ _ _ I).
        unfold MIN_MATCH in HL.
        apply hc_inv_insert_str; try assumption; rewrite ?(cf_pl _ C), ?(cf_hl _ C); try lia.
        rewrite wrap16_id by lia. reflexivity. }
    split; [| split; [exact Hhh | split; [exact K | split; [exact P1 | split; [exact P2 | split; [exact P3 | intros L; exact (proj1 (HASH L))]]]]]].
    pose proof I as [_ Istr Ilook Isl Iins Ibs Ibs0 Ihw Iih Ims Ipm Iml Ipl Ima Ima1 Imt Ifast Ifastpl Islow Islow1 Ihash Isyms Iroom Ibv Ibb Ipend Ipout Ipop Ipo0 Ipobv Ilf Ilive Iinit Igz Ineg Ilk0 Isn0 Iinw Ifl Imas Ips].
    constructor; unfold lz_strat in *; rewrite ?Fstr, ?Flook, ?Fws, ?Fins, ?Fbs, ?Flv, ?Fhw, ?Fms, ?Fpm, ?Fml, ?Fpl, ?Fma, ?Fmt, ?Fsg, ?Fhs, ?Fsn, ?Fse, ?Flb, ?Fpo, ?Flf, ?Fst, ?Fwr, ?Eih, ?P1, ?P2, ?P3; try assumption.
    - clear -Hh Sh. lia.
    - intros L. exact (proj2 (HASH L)).
    - destruct Isyms as (syms & D & COV). exists syms. split; [| exact COV]. eapply dsyms_keep; [exact D | ..]; assumption.
  Qed.
End InsertInv.

Lemma dinv_insert_string : forall (rm : Z) (fz : bool) (s : deflate_state),
  dcfg s -> dinvR rm 0 fz s -> MIN_MATCH <= ds_lookahead s ->
    let '(s', hh) := insert_string s (ds_strstart s) in
    dinvR rm 1 fz s'
    /\ 0 <= hh < 65536
    /\ kproj (set_head (set_prev (set_ins_h s' (ds_ins_h s)) (ds_prev s)) (ds_head s)) = kproj s
    /\ ds_pending s' = ds_pending s /\ ds_bi_valid s' = ds_bi_valid s /\ ds_bi_buf s' = ds_bi_buf s
    /\ (ds_level s <> 0 -> exists Ins, (hh <> 0 -> Ins hh) /\ chain_inv Ins (ds_strstart s) (ds_w_size s) (ds_prev s')).
Proof. intros rm fz s C I HL. apply dinv_insert_string_gen; [exact C | exact I | pose proof (di_sl _ _ _ _ I); lia]. Qed.


Lemma dcfg_kproj : forall a b, kproj a = kproj b -> dcfg b -> dcfg a.
Proof.
  intros a b K C.
  pose proof (kp_status _ _ K) as E1. pose proof (kp_window_blk _ _ K) as E2. pose proof (kp_prev_blk _ _ K) as E3.
  pose proof (kp_head_blk _ _ K) as E4. pose proof (kp_pending_buf_blk _ _ K) as E5. pose proof (kp_w_bits _ _ K) as E6.
  pose proof (kp_w_size _ _ K) as E7. pose proof (kp_w_mask _ _ K) as E8. pose proof (kp_window_size _ _ K) as E9.
  pose proof (kp_hash_bits _ _ K) as E10. pose proof (kp_hash_size _ _ K) as E11. pose proof (kp_hash_mask _ _ K) as E12.
  pose proof (kp_hash_shift _ _ K) as E13. pose proof (kp_lit_bufsize _ _ K) as E14. pose proof (kp_pending_buf_size _ _ K) as E15.
  pose proof (kp_sym_end _ _ K) as E16. pose proof (kp_window _ _ K) as E17. pose proof (kp_prev _ _ K) as E18.
  pose proof (kp_head _ _ K) as E19. pose proof (kp_len_pending_buf _ _ K) as E20. pose proof (kp_gzhead _ _ K) as E21.
  pose proof (kp_method _ _ K) as E22. pose proof (kp_level _ _ K) as E23. pose proof (kp_strategy _ _ K) as E24.
  pose proof (kp_wrap _ _ K) as E25. pose proof (kp_good_match _ _ K) as E26. pose proof (kp_max_lazy_match _ _ K) as E27.
  pose proof (kp_nice_match _ _ K) as E28. pose proof (kp_max_chain_length _ _ K) as E29.
  pose proof (kp_len_dyn_ltree_fc _ _ K) as L1. pose proof (kp_len_dyn_ltree_dl _ _ K) as L2. pose proof (kp_len_dyn_dtree_fc _ _ K) as L3.
  pose proof (kp_len_dyn_dtree_dl _ _ K) as L4. pose proof (kp_len_bl_tree_fc _ _ K) as L5. pose proof (kp_len_bl_tree_dl _ _ K) as L6.
  pose proof (kp_len_bl_count _ _ K) as L7. pose proof (kp_len_heap _ _ K) as L8. pose proof (kp_len_depth _ _ K) as L9.
  destruct C; constructor; unfold deflateStateCheck, fbs_tree_lens in *;
    rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E10, ?E11, ?E12, ?E13, ?E14, ?E15, ?E16, ?E17, ?E18, ?E19, ?E20,
            ?E21, ?E22, ?E23, ?E24, ?E25, ?E26, ?E27, ?E28, ?E29, ?L1, ?L2, ?L3, ?L4, ?L5, ?L6, ?L7, ?L8, ?L9; assumption.
Qed.

Lemma dcfg_set_pending_out : forall s v, dcfg s -> dcfg (set_pending_out s v).
Proof. intros s v C. destruct C; constructor; dsr; assumption. Qed.
Lemma dcfg_set_block_start : forall s v, dcfg s -> dcfg (set_block_start s v).
Proof. intros s v C. destruct C; constructor; dsr; assumption. Qed.
Lemma dcfg_set_sym_next : forall s v, dcfg s -> dcfg (set_sym_next s v).
Proof. intros s v C. destruct C; constructor; dsr; assumption. Qed.
Lemma dcfg_set_matches : forall s v, dcfg s -> dcfg (set_matches s v).
Proof. intros s v C. destruct C; constructor; dsr; assumption. Qed.
Lemma dcfg_set_strm : forall s v, dcfg s -> dcfg (set_strm s v).
Proof. intros s v C. destruct C; constructor; dsr; assumption. Qed.



Local Ltac ctac C := destruct C; constructor; dsr; try assumption.
Lemma dcfg_set_lookahead : forall s v, dcfg s -> dcfg (set_lookahead s v). Proof. intros s v C. ctac C. Qed.
Lemma dcfg_set_strstart : forall s v, dcfg s -> dcfg (set_strstart s v). Proof. intros s v C. ctac C. Qed.
Lemma dcfg_set_match_length : forall s v, dcfg s -> dcfg (set_match_length s v). Proof. intros s v C. ctac C. Qed.
Lemma dcfg_set_ins_h : forall s v, dcfg s -> dcfg (set_ins_h s v). Proof. intros s v C. ctac C. Qed.
Lemma dcfg_set_insert : forall s v, dcfg s -> dcfg (set_insert s v). Proof. intros s v C. ctac C. Qed.
Lemma dcfg_set_match_start : forall s v, dcfg s -> dcfg (set_match_start s v). Proof. intros s v C. ctac C. Qed.
Lemma dcfg_set_prev_length : forall s v, dcfg s -> dcfg (set_prev_length s v). Proof. intros s v C. ctac C. Qed.
Lemma dcfg_set_prev_match : forall s v, dcfg s -> dcfg (set_prev_match s v). Proof. intros s v C. ctac C. Qed.
Lemma dcfg_set_match_available : forall s v, dcfg s -> dcfg (set_match_available s v). Proof. intros s v C. ctac C. Qed.
Lemma dcfg_set_high_water : forall s v, dcfg s -> dcfg (set_high_water s v). Proof. intros s v C. ctac C. Qed.
Lemma dcfg_set_head : forall s a, dcfg s -> arr_len a = arr_len (ds_head s) -> dcfg (set_head s a).
Proof. intros s a C L. destruct C; constructor; dsr; try assumption. rewrite L. assumption. Qed.
Lemma dcfg_set_prev : forall s a, dcfg s -> arr_len a = arr_len (ds_prev s) -> dcfg (set_prev s a).
Proof. intros s a C L. destruct C; constructor; dsr; try assumption. rewrite L. assumption. Qed.
Lemma dcfg_set_window : forall s a, dcfg s -> arr_len a = arr_len (ds_window s) -> dcfg (set_window s a).
Proof. intros s a C L. destruct C; constructor; dsr; try assumption. rewrite L. assumption. Qed.

Lemma dcfg_insert_string : forall s str, dcfg s -> dcfg (fst (insert_string s str)).
Proof.
  intros s str C. unfold insert_string. cbn [fst].
  apply dcfg_set_head; [apply dcfg_set_prev; [apply dcfg_set_ins_h; exact C|]|]; dsr; apply arr_len_set.
Qed.
Lemma dcfg_tally_lit : forall s c, dcfg s -> dcfg (fst (tr_tally_lit s c)).
Proof. intros s c C. apply (dcfg_kproj _ _ (kp_tr_tally_lit s c)). apply dcfg_set_sym_next. exact C. Qed.
Lemma dcfg_tally_dist : forall s d l, dcfg s -> dcfg (fst (tr_tally_dist s d l)).
Proof. intros s d l C. apply (dcfg_kproj _ _ (kp_tr_tally_dist s d l)). apply dcfg_set_sym_next. exact C. Qed.
