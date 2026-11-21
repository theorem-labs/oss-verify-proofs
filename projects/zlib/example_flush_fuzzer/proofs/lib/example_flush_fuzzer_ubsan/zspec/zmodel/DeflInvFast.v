(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateInvHash DeflateInvKeep OverlayFBS DeflRoom.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel SendModel DeflFastModel TreesTab.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import RefFlushBlk11 RefFlushPend1 RefDeflFastOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma dinv_lzw : forall rm hb fz s, 0 <= rm -> dcfg s -> dinvR rm hb fz s -> lzw s.
Proof.
  intros rm hb fz s Hrm C I.
  pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
  pose proof (cf_table _ C) as TB.
  assert (LZ : 0 <= ds_max_lazy_match s <= 258).
  { pose proof (cf_level _ C). assert (E : ds_max_lazy_match s = snd (fst (fst (configuration_table (ds_level s))))) by (rewrite <- TB; reflexivity).
    rewrite E. unfold configuration_table.
    destruct (ds_level s) as [|p|p]; try lia; cbn; try lia. do 4 (destruct p; cbn; try lia). }
  constructor.
  - symmetry. exact (cf_bl _ C).
  - exact (cf_symend _ C).
  - pose proof (di_room _ _ _ _ I). destruct (di_syms _ _ _ _ I) as (syms & D & _). pose proof (sy_next _ _ D). lia.
  - exact (cf_wmask _ C).
  - exact (cf_hmask _ C).
  - rewrite (cf_hshift _ C). pose proof (cf_hbits _ C). unfold MIN_MATCH. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  - exact (di_ih _ _ _ _ I).
  - exact (di_str _ _ _ _ I).
  - exact (di_look _ _ _ _ I).
  - rewrite (cf_wl _ C). exact (di_sl _ _ _ _ I).
  - pose proof (di_ml _ _ _ _ I). unfold MAX_MATCH in *. lia.
  - exact (di_ms _ _ _ _ I).
  - lia.
  - intros i Hi. exact (ct_win _ (di_cty _ _ _ _ I) i Hi).
  - intros i Hi. exact (ct_head _ (di_cty _ _ _ _ I) i Hi).
  - intros i Hi. exact (ct_prev _ (di_cty _ _ _ _ I) i Hi).
Qed.

Lemma dcfg_params : forall s, dcfg s -> ds_level s <> 0 ->
  4 <= ds_max_chain_length s <= 4096 /\ 0 <= ds_max_lazy_match s <= 258 /\ 0 <= ds_good_match s <= 32 /\ 0 <= ds_nice_match s <= 258.
Proof.
  intros s C Lz. pose proof (cf_table _ C) as TB. pose proof (cf_level _ C) as LV.
  assert (E1 : ds_good_match s = fst (fst (fst (configuration_table (ds_level s))))) by (rewrite <- TB; reflexivity).
  assert (E2 : ds_max_lazy_match s = snd (fst (fst (configuration_table (ds_level s))))) by (rewrite <- TB; reflexivity).
  assert (E3 : ds_nice_match s = snd (fst (configuration_table (ds_level s)))) by (rewrite <- TB; reflexivity).
  assert (E4 : ds_max_chain_length s = snd (configuration_table (ds_level s))) by (rewrite <- TB; reflexivity).
  rewrite E1, E2, E3, E4. unfold configuration_table.
  destruct (ds_level s) as [|p|p]; try lia; cbn. do 4 (destruct p; cbn; try lia).
Qed.


Lemma lm_run : forall rm hb fz s hh Ins,
  dcfg s -> dinvR rm hb fz s -> ds_level s <> 0 ->
  Ins hh -> hh <> 0 -> chain_inv Ins (ds_strstart s) (ds_w_size s) (ds_prev s) ->
  ds_strstart s - hh <= ds_w_size s - MIN_LOOKAHEAD -> 0 <= hh < 65536 ->
  ds_strstart s + MIN_LOOKAHEAD <= 2 * ds_w_size s -> 1 <= ds_prev_length s ->
  lm_pre s hh
  /\ let '(s', ml) := longest_match s hh in
     exists v, s' = set_match_start s v /\ 0 <= v < 2 ^ 32
       /\ ml <= ds_lookahead s /\ ml <= Z.max (ds_prev_length s) MAX_MATCH /\ Z.min (ds_prev_length s) (ds_lookahead s) <= ml
       /\ ((v = ds_match_start s /\ ml <= ds_prev_length s)
           \/ (0 <= v < ds_strstart s /\ ds_strstart s - (ds_w_size s - MIN_LOOKAHEAD) <= v)).
Proof.
  intros rm hb fz s hh Ins C I Lz Ihh Hnz HC Hdist Hhh Hstr Hpl1.
  pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl). pose proof (dcfg_params s C Lz) as (P1 & P2 & P3 & P4).
  assert (CTX : lm_ctx Ins s hh).
  { constructor; try assumption.
    - exact (cf_wmask _ C).
    - exists (ds_w_bits s). pose proof (cf_wbits _ C). split; [lia | exact (cf_wsize _ C)].
    - unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH. lia. }
  split.
  - apply (lm_pre_intro Ins s hh CTX); try lia.
    + exact (di_str _ _ _ _ I).
    + rewrite (cf_wl _ C). unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hstr. lia.
    + rewrite (cf_wl _ C). lia.
    + rewrite (cf_wmask _ C), (cf_pl _ C). lia.
    + rewrite (cf_pl _ C). lia.
    + pose proof (di_pl _ _ _ _ I). unfold MAX_MATCH in *. lia.
    + pose proof (di_look _ _ _ _ I). pose proof (di_sl _ _ _ _ I). pose proof (di_str _ _ _ _ I). lia.
  - pose proof (longest_match_post Ins s hh CTX) as LP.
    destruct (longest_match s hh) as [s' ml]. destruct LP as (v & Es & M1 & M2 & M3 & Alt).
    exists v. split; [exact Es|]. split.
    { pose proof (di_sl _ _ _ _ I). pose proof (di_look _ _ _ _ I). destruct Alt as [[-> _] | (A & B)]; [exact (di_ms _ _ _ _ I) | lia]. }
    split; [exact M1|]. split; [exact M3|]. split; [| exact Alt]. apply M2. exact (di_look _ _ _ _ I).
Qed.


Definition fast_disp (s : deflate_state) : deflate_state * bool :=
  if Z.leb MIN_MATCH (ds_match_length s) then
    let '(s, bflush) := tr_tally_dist s (wrap32 (ds_strstart s - ds_match_start s)) (ds_match_length s - MIN_MATCH) in
    let s := set_lookahead s (ds_lookahead s - ds_match_length s) in
    let s :=
      if Z.leb (ds_match_length s) (ds_max_lazy_match s) && Z.leb MIN_MATCH (ds_lookahead s)
      then
        let s := set_match_length s (ds_match_length s - 1) in
        let s := deflate_fast_insert (Z.to_nat (ds_match_length s)) s in
        set_strstart s (ds_strstart s + 1)
      else
        let s := set_strstart s (ds_strstart s + ds_match_length s) in
        let s := set_match_length s 0 in
        let s := set_ins_h s (arr_get (ds_window s) (ds_strstart s)) in
        set_ins_h s (update_hash s (ds_ins_h s) (arr_get (ds_window s) (ds_strstart s + 1)))
    in (s, bflush)
  else
    let '(s, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s)) in
    let s := set_lookahead s (ds_lookahead s - 1) in
    let s := set_strstart s (ds_strstart s + 1) in
    (s, bflush).

Lemma dispatch_spec_eq' : forall s, dispatch_spec s = (let '(s', b) := fast_disp s in after_tally s' b).
Proof. intros s. reflexivity. Qed.

Section FAST.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.

  Let DRUN rm hb fz := drunR rm hb fz ws hs PBL ILEN OCAP tot0.
  Let DPOST := dpost ws hs PBL ILEN OCAP tot0.

  Lemma drun_relift : forall rm hb fz rm' hb' fz' s s',
    DRUN rm hb fz s -> dinvR rm' hb' fz' s' -> dcfg s' ->
    ds_strm s' = ds_strm s -> ds_pending s' = ds_pending s -> ds_pending_out s' = ds_pending_out s ->
    ds_w_size s' = ds_w_size s -> ds_hash_size s' = ds_hash_size s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
    ds_status s' = ds_status s -> ds_wrap s' = ds_wrap s -> ds_level s' = ds_level s ->
    DRUN rm' hb' fz' s'.
  Proof.
    intros rm hb fz rm' hb' fz' s s' [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0] I' C' E1 E2 E3 E4 E5 E6 E7 E8 E9.
    split; [| rewrite E2; exact P0 | rewrite E3; exact PO0].
    constructor; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9; try assumption.
    destruct CL; constructor; rewrite ?E1, ?E8; assumption.
  Qed.

  Record lzf (s s' : deflate_state) : Prop := MkLZF {
    zf_strm : ds_strm s' = ds_strm s; zf_pending : ds_pending s' = ds_pending s; zf_pout : ds_pending_out s' = ds_pending_out s;
    zf_ws : ds_w_size s' = ds_w_size s; zf_hs : ds_hash_size s' = ds_hash_size s; zf_lbs : ds_lit_bufsize s' = ds_lit_bufsize s;
    zf_status : ds_status s' = ds_status s; zf_wrap : ds_wrap s' = ds_wrap s; zf_level : ds_level s' = ds_level s;
    zf_strategy : ds_strategy s' = ds_strategy s; zf_bi_valid : ds_bi_valid s' = ds_bi_valid s; zf_bi_buf : ds_bi_buf s' = ds_bi_buf s;
    zf_lazy : ds_max_lazy_match s' = ds_max_lazy_match s; zf_bs : ds_block_start s' = ds_block_start s;
    zf_ma : ds_match_available s' = ds_match_available s }.
  Lemma lzf_refl : forall s, lzf s s. Proof. intros s; constructor; reflexivity. Qed.
  Lemma lzf_trans : forall a b c, lzf a b -> lzf b c -> lzf a c.
  Proof. intros a b c [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15]; constructor; congruence. Qed.
  Lemma drun_lzf : forall rm hb fz rm' hb' fz' s s', DRUN rm hb fz s -> dinvR rm' hb' fz' s' -> dcfg s' -> lzf s s' -> DRUN rm' hb' fz' s'.
  Proof. intros rm hb fz rm' hb' fz' s s' D I C [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15]. exact (drun_relift _ _ _ _ _ _ _ _ D I C F1 F2 F3 F4 F5 F6 F7 F8 F9). Qed.

  Lemma lit_run : forall hb fz s, 0 <= hb <= 1 -> DRUN 3 hb fz s -> 1 <= ds_lookahead s ->
    (lz_strat s -> 1 <= ds_level s <= 3 /\ ds_match_length s < MIN_MATCH) ->
    lit_ok ws PBL OCAP s
    /\ let '(s', bflush) := lit_core s in
       DRUN (if bflush then 0 else 3) 0 true s' /\ lzf s s'
       /\ ds_lookahead s' = ds_lookahead s - 1 /\ ds_strstart s' = ds_strstart s + 1
       /\ bflush = (ds_sym_next s' =? ds_sym_end s').
  Proof.
    intros hb fz s Hhb D Hlook Hfast. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl.
    assert (Hc : 0 <= arr_get (ds_window s) (ds_strstart s) < 256).
    { apply (ct_win _ (di_cty _ _ _ _ I)). rewrite (cf_wl _ C). lia. }
    pose proof (dinv_tally_lit _ _ s C I Slz P0 Sst (arr_get (ds_window s) (ds_strstart s)) Hc) as TL.
    pose proof (dcfg_tally_lit s (arr_get (ds_window s) (ds_strstart s)) C) as C1.
    unfold lit_ok, lit_core. cbv zeta.
    destruct (tr_tally_lit s (arr_get (ds_window s) (ds_strstart s))) as [s1 bflush]. cbn [fst snd] in *.
    destruct TL as (I1 & (syms & D0 & D1) & Hb & P1 & P2 & P3 & K1).
    assert (F : forall (f : deflate_state -> Z) kpf, (forall a b, kproj a = kproj b -> f a = f b) -> (forall x v, f (set_sym_next x v) = f x) -> kpf = f -> f s1 = f s).
    { intros f kpf E1 E2 _. rewrite (E1 _ _ K1), E2. reflexivity. }
    pose proof (F ds_strstart ds_strstart (fun a b H => kp_strstart b a H) strstart_set_sym_next eq_refl) as Fstr.
    pose proof (F ds_lookahead ds_lookahead (fun a b H => kp_lookahead b a H) lookahead_set_sym_next eq_refl) as Flook.
    pose proof (F ds_w_size ds_w_size (fun a b H => kp_w_size b a H) w_size_set_sym_next eq_refl) as Fws.
    pose proof (F ds_block_start ds_block_start (fun a b H => kp_block_start b a H) block_start_set_sym_next eq_refl) as Fbs.
    pose proof (F ds_level ds_level (fun a b H => kp_level b a H) level_set_sym_next eq_refl) as Flv.
    pose proof (F ds_match_length ds_match_length (fun a b H => kp_match_length b a H) match_length_set_sym_next eq_refl) as Fml.
    pose proof (F ds_match_start ds_match_start (fun a b H => kp_match_start b a H) match_start_set_sym_next eq_refl) as Fms.
    pose proof (F ds_match_available ds_match_available (fun a b H => kp_match_available b a H) match_available_set_sym_next eq_refl) as Fma.
    pose proof (F ds_strategy ds_strategy (fun a b H => kp_strategy b a H) strategy_set_sym_next eq_refl) as Fsg.
    pose proof (F ds_wrap ds_wrap (fun a b H => kp_wrap b a H) wrap_set_sym_next eq_refl) as Fwr.
    pose proof (F ds_hash_size ds_hash_size (fun a b H => kp_hash_size b a H) hash_size_set_sym_next eq_refl) as Fhs.
    pose proof (F ds_lit_bufsize ds_lit_bufsize (fun a b H => kp_lit_bufsize b a H) lit_bufsize_set_sym_next eq_refl) as Flb.
    pose proof (F ds_status ds_status (fun a b H => kp_status b a H) status_set_sym_next eq_refl) as Fst.
    pose proof (F ds_pending_out ds_pending_out (fun a b H => kp_pending_out b a H) pending_out_set_sym_next eq_refl) as Fpo.
    pose proof (F ds_max_lazy_match ds_max_lazy_match (fun a b H => kp_max_lazy_match b a H) max_lazy_match_set_sym_next eq_refl) as Flz.
    assert (Fsm : ds_strm s1 = ds_strm s) by (rewrite <- (kp_strm s1 (set_sym_next s (ds_sym_next s + 3)) (eq_sym K1)); dsr; reflexivity).
    assert (I2 : dinvR (if bflush then 0 else 3) hb true (set_lookahead s1 (ds_lookahead s1 - 1))).
    { apply dinv_set_lookahead.
      - destruct I1; constructor; try assumption.
        + intros _. rewrite Flv, Fml. unfold lz_strat. rewrite Fsg. intros A B. exact (proj2 (Hfast B)).
        + intros _. rewrite Flv. unfold lz_strat. rewrite Fsg. intros A B. pose proof (proj1 (Hfast B)) as X. clear -A X. lia.
      - rewrite Flook. clear -Hlook. lia.
      - rewrite Fstr, Flook, Fws. clear -Isl Hlook. lia.
      - rewrite Flv. unfold lz_strat. rewrite Fsg. intros _ A B. pose proof (proj1 (Hfast B)) as X. clear -A X. lia.
      - rewrite Fwr. intros W. destruct (di_negwrap _ _ _ _ I W) as [_ L0]. clear -L0 Hlook. lia.
      - rewrite Flv. intros L0. exfalso. exact (Slz L0).
      - clear. lia. }
    set (s2 := set_lookahead s1 (ds_lookahead s1 - 1)) in *.
    assert (I3 : dinvR (if bflush then 0 else 3) 0 true (set_strstart s2 (ds_strstart s2 + 1))).
    { apply (dinv_set_strstart _ hb); try exact I2; subst s2; dsr; rewrite ?Fstr, ?Flook, ?Fws, ?Flv, ?Fbs, ?Fma, ?Fms, ?Fsg; try lia.
      - intros L. exists (syms ++ [(0, arr_get (ds_window s) (ds_strstart s))]). split.
        + eapply dsyms_keep; [exact D1 | dsr; reflexivity ..].
        + rewrite zcov_app1, (Z.eqb_refl 0). destruct (di_syms _ _ _ _ I) as (sy0 & Dy0 & COV0).
          rewrite (dsyms_unique _ _ _ Dy0 D0) in COV0. specialize (COV0 L). clear -COV0. lia.
      - unfold lz_strat. dsr. rewrite Fsg. intros _ A B. pose proof (proj1 (Hfast B)). lia. }
    remember (set_strstart s2 (ds_strstart s2 + 1)) as s3 eqn:Es3.
    replace (set_strstart s2 (ds_strstart s1 + 1)) with s3 by (subst s3 s2; dsr; reflexivity).
    assert (LF : lzf s s3).
    { subst s3 s2. constructor; dsr; try assumption. }
    assert (C3 : dcfg s3) by (subst s3 s2; apply dcfg_set_strstart, dcfg_set_lookahead; exact C1).
    assert (D3 : DRUN (if bflush then 0 else 3) 0 true s3) by exact (drun_lzf _ _ _ _ _ _ _ _ D I3 C3 LF).
    assert (E3a : ds_lookahead s3 = ds_lookahead s - 1) by (subst s3 s2; dsr; rewrite Flook; reflexivity).
    assert (E3b : ds_strstart s3 = ds_strstart s + 1) by (subst s3 s2; dsr; rewrite Fstr; reflexivity).
    assert (E3c : bflush = (ds_sym_next s3 =? ds_sym_end s3)) by (subst s3 s2; dsr; exact Hb).
    split.
    - split; [exact (dinv_lzw 3 hb fz s ltac:(lia) C I)|]. split; [exact (di_room _ _ _ _ I)|]. split; [exact Hlook|].
      split; [destruct bflush; [exact (dinv_lzw 0 0 true s3 ltac:(lia) C3 I3) | exact (dinv_lzw 3 0 true s3 ltac:(lia) C3 I3)]|].
      intros Hbf. rewrite Hbf in D3. exact (proj1 (fbo_run ws hs PBL ILEN OCAP tot0 TS TR HPBL 0 0 true s3 0 ltac:(lia) D3 ltac:(left; reflexivity))).
    - split; [exact D3|]. split; [exact LF|]. split; [exact E3a|]. split; [exact E3b|]. exact E3c.
  Qed.

  Lemma dinv_fz_true : forall rm hb fz s, dinvR rm hb fz s -> (1 <= ds_level s <= 3 -> lz_strat s -> ds_match_length s < MIN_MATCH) ->
    (4 <= ds_level s -> lz_strat s -> MIN_MATCH <= ds_match_length s ->
       1 <= ds_strstart s /\ 1 <= wrap32 (ds_strstart s - 1 - ds_match_start s) <= ds_w_size s - MIN_LOOKAHEAD /\ ds_match_length s <= ds_lookahead s + 1) ->
    dinvR rm hb true s.
  Proof. intros rm hb fz s I H H'. destruct I; constructor; try assumption; intros _; [exact H | exact H']. Qed.

  Lemma istep_run : forall rm s syms, 0 <= rm -> DRUN rm 1 false s -> 1 <= ds_match_length s -> MIN_MATCH <= ds_lookahead s ->
    ds_strstart s + 1 + ds_lookahead s <= 2 * ds_w_size s -> 1 <= ds_level s <= 3 -> lz_strat s ->
    dsyms syms s -> ds_strstart s + ds_match_length s - ds_block_start s <= zcov syms + ds_match_available s ->
    lzw s
    /\ let s' := istep s in
       DRUN rm 1 false s' /\ lzf s s' /\ dsyms syms s'
       /\ ds_strstart s' = ds_strstart s + 1 /\ ds_match_length s' = ds_match_length s - 1 /\ ds_lookahead s' = ds_lookahead s.
  Proof.
    intros rm s syms Hrm D Hml Hlook Hsl Hlv Hst DS COV. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    split; [exact (dinv_lzw _ _ _ _ Hrm C I)|].
    unfold istep. cbv zeta.
    set (s1 := set_strstart s (ds_strstart s + 1)).
    assert (I1 : dinvR rm 0 false s1).
    { subst s1. apply (dinv_set_strstart rm 1 false 0 s); try exact I; try lia.
      intros _. exists syms. split; [exact DS | lia]. }
    assert (C1 : dcfg s1) by (subst s1; apply dcfg_set_strstart; exact C).
    pose proof (dinv_insert_string rm false s1 C1 I1 ltac:(subst s1; dsr; exact Hlook)) as INS.
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
    pose proof (F ds_match_available kp_match_available match_available_set_head match_available_set_prev match_available_set_ins_h) as Fma.
    assert (Fsm : ds_strm s2 = ds_strm s1).
    { pose proof (kp_strm _ _ K2) as X. rewrite strm_set_head, strm_set_prev, strm_set_ins_h in X. exact X. }
    assert (I3 : dinvR rm 1 false (set_match_length s2 (ds_match_length s - 1))).
    { apply (dinv_set_match_length rm 1 false false s2); try exact I2.
      - pose proof (di_ml _ _ _ _ I). lia.
      - intros X. discriminate X.
      - intros X. discriminate X.
      - rewrite Flv. subst s1. dsr. intros A. lia. }
    remember (set_match_length s2 (ds_match_length s - 1)) as s3 eqn:Es3.
    assert (LF : lzf s s3).
    { subst s3. constructor; dsr; rewrite ?Fsm, ?Fws, ?Fhs, ?Flb, ?Fst, ?Fwr, ?Flv, ?Fsg, ?Fpo, ?Flz, ?Fbs, ?Fma, ?Q1, ?Q2, ?Q3; subst s1; dsr; reflexivity. }
    assert (C3 : dcfg s3) by (subst s3; apply dcfg_set_match_length; exact C2).
    split; [exact (drun_lzf _ _ _ _ _ _ _ _ D I3 C3 LF)|].
    split; [exact LF|].
    split; [subst s3; eapply dsyms_keep; [exact DS | dsr ..]; rewrite ?Fsn, ?Epb, ?Flb, ?Fws, ?Elt, ?Edt, ?Ebt, ?Eol, ?Esl; subst s1; dsr; reflexivity|].
    subst s3. dsr. rewrite Fstr, Flook. subst s1. dsr. repeat split; reflexivity.
  Qed.

  Lemma fast_insert_run : forall n rm s syms, 0 <= rm -> DRUN rm 1 false s -> Z.of_nat n = ds_match_length s -> 1 <= ds_match_length s ->
    MIN_MATCH <= ds_lookahead s -> ds_strstart s + ds_match_length s + ds_lookahead s <= 2 * ds_w_size s ->
    1 <= ds_level s <= 3 -> lz_strat s ->
    dsyms syms s -> ds_strstart s + ds_match_length s - ds_block_start s <= zcov syms + ds_match_available s ->
    iloop_ok n s
    /\ let s' := deflate_fast_insert n s in
       DRUN rm 1 false s' /\ lzf s s' /\ dsyms syms s'
       /\ ds_strstart s' = ds_strstart s + ds_match_length s /\ ds_match_length s' = 0 /\ ds_lookahead s' = ds_lookahead s.
  Proof.
    induction n as [|n IH]; intros rm s syms Hrm D Hn Hml Hlook Hsl Hlv Hst DS COV.
    { exfalso. cbn in Hn. lia. }
    destruct (istep_run rm s syms Hrm D Hml Hlook ltac:(lia) Hlv Hst DS ltac:(lia)) as (LZ & D1 & LF1 & DS1 & S1 & M1 & L1).
    rewrite deflate_fast_insert_step. cbn [iloop_ok]. cbv zeta.
    remember (istep s) as s1 eqn:Es1.
    destruct (Z.eqb_spec (ds_match_length s1) 0) as [Z0|Z0]; cbn [negb].
    - split; [split; [exact LZ | destruct n; [exact Logic.I | rewrite Nat2Z.inj_succ in Hn; exfalso; lia]]|].
      split; [exact D1|]. split; [exact LF1|]. split; [exact DS1|]. rewrite S1, L1. split; [lia|]. split; [exact Z0 | reflexivity].
    - pose proof LF1 as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15].
      destruct (IH rm s1 syms Hrm D1 ltac:(rewrite Nat2Z.inj_succ in Hn; lia) ltac:(lia) ltac:(lia) ltac:(rewrite S1, M1, L1, F4; lia)
                  ltac:(rewrite F9; exact Hlv) ltac:(unfold lz_strat; rewrite F10; exact Hst) DS1 ltac:(rewrite S1, M1, F14, F15; lia)) as (IL & D2 & LF2 & DS2 & S2 & M2 & L2).
      split; [split; [exact LZ | exact IL]|].
      split; [exact D2|]. split; [exact (lzf_trans _ _ _ LF1 LF2)|]. split; [exact DS2|]. rewrite S2, M2, L2, S1, M1, L1. split; [lia|]. split; reflexivity.
  Qed.

  Lemma match_run : forall s, DRUN 3 1 false s -> MIN_MATCH <= ds_match_length s ->
    1 <= ds_strstart s - ds_match_start s <= ds_w_size s - MIN_LOOKAHEAD -> ds_match_length s <= ds_lookahead s ->
    (MIN_LOOKAHEAD <= ds_lookahead s \/ ds_strstart s + ds_lookahead s <= 2 * ds_w_size s - 2) ->
    1 <= ds_level s <= 3 -> lz_strat s ->
    match_ok ws PBL OCAP s
    /\ let '(s', bflush) := fast_disp s in
       DRUN (if bflush then 0 else 3) 0 true s' /\ lzf s s'
       /\ ds_lookahead s' = ds_lookahead s - ds_match_length s /\ ds_strstart s' = ds_strstart s + ds_match_length s
       /\ bflush = (ds_sym_next s' =? ds_sym_end s').
  Proof.
    intros s D Hml Hdist Hmll G Hlv Hst. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    pose proof (di_str _ _ _ _ I) as Istr. pose proof (di_sl _ _ _ _ I) as Isl. pose proof (di_ml _ _ _ _ I) as Iml. pose proof (di_look _ _ _ _ I) as Ilook.
    assert (KML : MIN_LOOKAHEAD = 262) by reflexivity. assert (KMM : MIN_MATCH = 3) by reflexivity. assert (KXM : MAX_MATCH = 258) by reflexivity.
    unfold match_ok, fast_disp. rewrite (proj2 (Z.leb_le _ _) Hml). cbv zeta.
    rewrite (wrap32_id (ds_strstart s - ds_match_start s)) by lia.
    pose proof (dinv_tally_dist 1 false s C I Slz P0 Sst (ds_strstart s - ds_match_start s) (ds_match_length s - MIN_MATCH) Hdist
                  ltac:(lia)) as TD.
    pose proof (dcfg_tally_dist s (ds_strstart s - ds_match_start s) (ds_match_length s - MIN_MATCH) C) as C5.
    destruct (tr_tally_dist s (ds_strstart s - ds_match_start s) (ds_match_length s - MIN_MATCH)) as [s5 bflush]. cbn [fst snd] in *.
    destruct TD as (I5 & (syms & D0 & D5) & Hb & P1 & P2 & P3 & K5).
    pose proof (kp_sn_fields _ _ _ K5) as SF. destruct SF.
    assert (Fsm : ds_strm s5 = ds_strm s) by exact sn_strm.
    assert (I6 : dinvR (if bflush then 0 else 3) 1 false (set_lookahead s5 (ds_lookahead s5 - ds_match_length s5))).
    { apply dinv_set_lookahead; try exact I5; rewrite ?sn_lookahead, ?sn_match_length, ?sn_strstart, ?sn_w_size, ?sn_level, ?sn_wrap; try lia. all: intros L0; exfalso; exact (Slz L0). }
    set (s6 := set_lookahead s5 (ds_lookahead s5 - ds_match_length s5)) in *.
    assert (C6 : dcfg s6) by (subst s6; apply dcfg_set_lookahead; exact C5).
    pose proof (di_syms _ _ _ _ I) as (sy0 & Dy0 & COV0). rewrite (dsyms_unique _ _ _ Dy0 D0) in COV0. specialize (COV0 Slz).
    assert (DS6 : dsyms (syms ++ [(ds_strstart s - ds_match_start s, ds_match_length s - MIN_MATCH)]) s6) by (subst s6; eapply dsyms_keep; [exact D5 | dsr; reflexivity ..]).
    assert (ZC : zcov (syms ++ [(ds_strstart s - ds_match_start s, ds_match_length s - MIN_MATCH)]) = zcov syms + ds_match_length s).
    { rewrite zcov_app1. replace (ds_strstart s - ds_match_start s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
    assert (LZ0 : lzw s) by exact (dinv_lzw 3 1 false s ltac:(lia) C I).
    assert (LZ5 : lzw s5) by (destruct bflush; [exact (dinv_lzw 0 1 false s5 ltac:(lia) C5 I5) | exact (dinv_lzw 3 1 false s5 ltac:(lia) C5 I5)]).
    assert (LZ6 : lzw s6) by (destruct bflush; [exact (dinv_lzw 0 1 false s6 ltac:(lia) C6 I6) | exact (dinv_lzw 3 1 false s6 ltac:(lia) C6 I6)]).
    assert (Hrm : 0 <= (if bflush then 0 else 3)) by (destruct bflush; lia).
    assert (E6str : ds_strstart s6 = ds_strstart s) by (subst s6; dsr; exact sn_strstart).
    assert (E6ml : ds_match_length s6 = ds_match_length s) by (subst s6; dsr; exact sn_match_length).
    assert (E6look : ds_lookahead s6 = ds_lookahead s - ds_match_length s) by (subst s6; dsr; rewrite sn_lookahead, sn_match_length; reflexivity).
    assert (E6ws : ds_w_size s6 = ds_w_size s) by (subst s6; dsr; exact sn_w_size).
    assert (E6bs : ds_block_start s6 = ds_block_start s) by (subst s6; dsr; exact sn_block_start).
    assert (E6ma : ds_match_available s6 = ds_match_available s) by (subst s6; dsr; exact sn_match_available).
    assert (E6lv : ds_level s6 = ds_level s) by (subst s6; dsr; exact sn_level).
    assert (E6sg : ds_strategy s6 = ds_strategy s) by (subst s6; dsr; exact sn_strategy).
    assert (E6win : ds_window s6 = ds_window s) by (subst s6; dsr; exact sn_window).
    assert (LF6 : lzf s s6).
    { subst s6. constructor; dsr; try assumption. }
    assert (D6 : DRUN (if bflush then 0 else 3) 1 false s6) by exact (drun_lzf _ _ _ _ _ _ _ _ D I6 C6 LF6).
    clearbody s6.
    destruct (Z.leb (ds_match_length s6) (ds_max_lazy_match s6) && Z.leb MIN_MATCH (ds_lookahead s6)) eqn:EB.
    +
      apply Bool.andb_true_iff in EB as [_ EB]. apply Z.leb_le in EB.
      assert (I7 : dinvR (if bflush then 0 else 3) 1 false (set_match_length s6 (ds_match_length s6 - 1))).
      { apply (dinv_set_match_length _ 1 false false s6 _ I6); rewrite ?E6ml, ?E6lv; [lia | intros X; discriminate X | intros X; discriminate X | intros A; lia]. }
      set (s7 := set_match_length s6 (ds_match_length s6 - 1)) in *.
      assert (C7 : dcfg s7) by (subst s7; apply dcfg_set_match_length; exact C6).
      assert (LF7 : lzf s s7) by (eapply lzf_trans; [exact LF6 | subst s7; constructor; dsr; reflexivity]).
      assert (D7 : DRUN (if bflush then 0 else 3) 1 false s7) by exact (drun_lzf _ _ _ _ _ _ _ _ D I7 C7 LF7).
      assert (DS7 : dsyms (syms ++ [(ds_strstart s - ds_match_start s, ds_match_length s - MIN_MATCH)]) s7) by (subst s7; eapply dsyms_keep; [exact DS6 | dsr; reflexivity ..]).
      assert (X1 : Z.of_nat (Z.to_nat (ds_match_length s7)) = ds_match_length s7) by (subst s7; dsr; rewrite E6ml; lia).
      assert (X2 : 1 <= ds_match_length s7) by (subst s7; dsr; rewrite E6ml; lia).
      assert (X3 : MIN_MATCH <= ds_lookahead s7) by (subst s7; dsr; lia).
      assert (X4 : ds_strstart s7 + ds_match_length s7 + ds_lookahead s7 <= 2 * ds_w_size s7) by (subst s7; dsr; rewrite E6str, E6ml, E6look, E6ws; lia).
      assert (X5 : 1 <= ds_level s7 <= 3) by (subst s7; dsr; rewrite E6lv; exact Hlv).
      assert (X6 : lz_strat s7) by (subst s7; unfold lz_strat; dsr; rewrite E6sg; exact Hst).
      assert (X7 : ds_strstart s7 + ds_match_length s7 - ds_block_start s7 <= zcov (syms ++ [(ds_strstart s - ds_match_start s, ds_match_length s - MIN_MATCH)]) + ds_match_available s7).
      { subst s7; dsr. rewrite E6str, E6ml, E6bs, E6ma, ZC. lia. }
      destruct (fast_insert_run (Z.to_nat (ds_match_length s7)) _ s7 _ Hrm D7 X1 X2 X3 X4 X5 X6 DS7 X7) as (IL & D8 & LF8 & DS8 & S8 & M8 & L8).
      remember (deflate_fast_insert (Z.to_nat (ds_match_length s7)) s7) as s8 eqn:Es8.
      pose proof LF8 as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15].
      pose proof (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D8)) as I8. pose proof (dp_cfg _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D8)) as C8.
      assert (E7str : ds_strstart s7 = ds_strstart s) by (subst s7; dsr; exact E6str).
      assert (E7ml : ds_match_length s7 = ds_match_length s - 1) by (subst s7; dsr; rewrite E6ml; reflexivity).
      assert (E7look : ds_lookahead s7 = ds_lookahead s - ds_match_length s) by (subst s7; dsr; exact E6look).
      assert (E7ws : ds_w_size s7 = ds_w_size s) by (subst s7; dsr; exact E6ws).
      assert (E7bs : ds_block_start s7 = ds_block_start s) by (subst s7; dsr; exact E6bs).
      assert (E7ma : ds_match_available s7 = ds_match_available s) by (subst s7; dsr; exact E6ma).
      assert (E7lv : ds_level s7 = ds_level s) by (subst s7; dsr; exact E6lv).
      assert (I9 : dinvR (if bflush then 0 else 3) 0 true (set_strstart s8 (ds_strstart s8 + 1))).
      { apply (dinv_fz_true _ _ false).
        - apply (dinv_set_strstart _ 1 false 0 s8 _ I8); rewrite ?S8, ?M8, ?L8, ?G4, ?G9, ?G14, ?G15, ?E7str, ?E7ml, ?E7look, ?E7ws, ?E7bs, ?E7ma, ?E7lv; try lia.
          intros _. eexists. split; [exact DS8|]. rewrite ZC. lia.
        - dsr. rewrite M8. intros _ _. lia.
        - dsr. rewrite G9, E7lv. intros A. lia. }
      remember (set_strstart s8 (ds_strstart s8 + 1)) as s9 eqn:Es9.
      assert (C9 : dcfg s9) by (subst s9; apply dcfg_set_strstart; exact C8).
      assert (LF9 : lzf s s9) by (eapply lzf_trans; [exact LF7|]; eapply lzf_trans; [exact LF8|]; subst s9; constructor; dsr; reflexivity).
      assert (D9 : DRUN (if bflush then 0 else 3) 0 true s9) by exact (drun_lzf _ _ _ _ _ _ _ _ D I9 C9 LF9).
      assert (LZ8 : lzw s8) by exact (dinv_lzw _ _ _ _ Hrm C8 I8).
      assert (LZ9 : lzw s9) by exact (dinv_lzw _ _ _ _ Hrm C9 I9).
      split.
      * split; [exact LZ0|]. split; [exact (di_room _ _ _ _ I)|]. split; [rewrite Z.mod_small by lia; lia|]. split; [exact Hmll|].
        split; [exact LZ5|]. split; [exact LZ6|]. rewrite E6str, E6ml. split; [rewrite <- Ews; lia|]. split; [lia|].
        split; [exact IL|]. split; [exact LZ8|]. split; [exact LZ9|].
        intros Hbf. rewrite Hbf in D9. exact (proj1 (fbo_run ws hs PBL ILEN OCAP tot0 TS TR HPBL 0 0 true s9 0 ltac:(lia) D9 ltac:(left; reflexivity))).
      * split; [exact D9|]. split; [exact LF9|]. subst s9. dsr. rewrite S8, L8, E7str, E7ml, E7look. split; [reflexivity|]. split; [lia|].
        rewrite Hb, (sy_next _ _ DS8), (sy_next _ _ D5), (cf_symend _ C8), (cf_symend _ C5), G6. subst s7. dsr. rewrite (zf_lbs _ _ LF6), <- sn_lit_bufsize. reflexivity.
    +
      assert (GEO : ds_strstart s + ds_match_length s + 2 <= 2 * ds_w_size s).
      { destruct G as [G|G]; [| lia]. lia. }
      assert (I7 : dinvR (if bflush then 0 else 3) 0 false (set_strstart s6 (ds_strstart s6 + ds_match_length s6))).
      { apply (dinv_set_strstart _ 1 false 0 s6 _ I6); rewrite ?E6str, ?E6ml, ?E6look, ?E6ws, ?E6lv, ?E6bs, ?E6ma; try lia.
        intros _. eexists. split; [exact DS6|]. rewrite ZC. lia. }
      set (s7 := set_strstart s6 (ds_strstart s6 + ds_match_length s6)) in *.
      assert (I8 : dinvR (if bflush then 0 else 3) 0 true (set_match_length s7 0)).
      { apply (dinv_set_match_length _ 0 false true s7 _ I7); [lia | intros _ _ _; lia | subst s7; dsr; rewrite E6lv; intros _ A; lia | subst s7; dsr; rewrite E6lv; intros A; lia]. }
      set (s8 := set_match_length s7 0) in *.
      assert (W8 : ds_window s8 = ds_window s) by (subst s8 s7; dsr; exact E6win).
      assert (S8 : ds_strstart s8 = ds_strstart s + ds_match_length s) by (subst s8 s7; dsr; rewrite E6str, E6ml; reflexivity).
      assert (B0 : 0 <= arr_get (ds_window s8) (ds_strstart s8) < 256).
      { rewrite W8, S8. apply (ct_win _ (di_cty _ _ _ _ I)). rewrite (cf_wl _ C). lia. }
      assert (I9 : dinvR (if bflush then 0 else 3) 0 true (set_ins_h s8 (arr_get (ds_window s8) (ds_strstart s8)))).
      { apply dinv_set_ins_h; [exact I8 | lia]. }
      set (s9 := set_ins_h s8 (arr_get (ds_window s8) (ds_strstart s8))) in *.
      assert (HM9 : 0 <= ds_hash_mask s9 < 2 ^ 16).
      { subst s9 s8 s7. dsr. rewrite (zf_hs _ _ LF6) || idtac. pose proof (cf_hmask _ C6) as HM. dsr in HM.
        assert (HS6 : ds_hash_size s6 = ds_hash_size s) by exact (zf_hs _ _ LF6).
        replace (ds_hash_mask s6) with (ds_hash_size s6 - 1) by (symmetry; exact HM). rewrite HS6. lia. }
      assert (I10 : dinvR (if bflush then 0 else 3) 0 true (set_ins_h s9 (update_hash s9 (ds_ins_h s9) (arr_get (ds_window s9) (ds_strstart s9 + 1))))).
      { apply dinv_set_ins_h; [exact I9|]. apply update_hash_range16. exact HM9. }
      remember (set_ins_h s9 (update_hash s9 (ds_ins_h s9) (arr_get (ds_window s9) (ds_strstart s9 + 1)))) as s10 eqn:Es10.
      assert (C10 : dcfg s10) by (subst s10 s9 s8 s7; apply dcfg_set_ins_h, dcfg_set_ins_h, dcfg_set_match_length, dcfg_set_strstart; exact C6).
      assert (LF10 : lzf s s10) by (eapply lzf_trans; [exact LF6|]; subst s10 s9 s8 s7; constructor; dsr; reflexivity).
      assert (D10 : DRUN (if bflush then 0 else 3) 0 true s10) by exact (drun_lzf _ _ _ _ _ _ _ _ D I10 C10 LF10).
      split.
      * split; [exact LZ0|]. split; [exact (di_room _ _ _ _ I)|]. split; [rewrite Z.mod_small by lia; lia|]. split; [exact Hmll|].
        split; [exact LZ5|]. split; [exact LZ6|]. rewrite E6str, E6ml. split; [rewrite <- Ews; lia|].
        split; [exact (dinv_lzw _ _ _ _ Hrm C10 I10)|].
        intros Hbf. rewrite Hbf in D10. exact (proj1 (fbo_run ws hs PBL ILEN OCAP tot0 TS TR HPBL 0 0 true s10 0 ltac:(lia) D10 ltac:(left; reflexivity))).
      * split; [exact D10|]. split; [exact LF10|]. subst s10 s9 s8 s7. dsr. rewrite E6str, E6ml, E6look. split; [reflexivity|]. split; [reflexivity|].
        rewrite Hb, (cf_symend _ C6), (cf_symend _ C5), (zf_lbs _ _ LF6), <- sn_lit_bufsize.
        rewrite (sy_next _ _ DS6), (sy_next _ _ D5). reflexivity.
  Qed.

  Lemma dinv_fz_weaken : forall rm hb s, dinvR rm hb true s -> dinvR rm hb false s.
  Proof. intros rm hb s I. destruct I; constructor; try assumption; intros X; discriminate X. Qed.
  Lemma dinv_hb01 : forall rm fz s, dinvR rm 0 fz s -> dinvR rm 1 fz s.
  Proof.
    intros rm fz s I. destruct I; constructor; try assumption.
    intros L. destruct (di_hash L) as [Ins HC]. exists Ins. apply (hc_inv_str_le _ _ _ _ _ _ _ HC). lia.
  Qed.

  Definition lzm (s : deflate_state) : Z := ds_lookahead s + cs_avail_in (ds_strm s).

  Variable flush : Z.
  Hypothesis Hflush : 0 <= flush <= 5.

  Definition NMPROG (s' : deflate_state) : Prop :=
    cs_avail_out (ds_strm s') = 0 \/ (cs_avail_in (ds_strm s') = 0 /\ flush = Z_NO_FLUSH).

  Definition LZPOST (M0 : Z) (s0 : deflate_state) (r : deflate_state * loop_out) : Prop :=
    let '(s', o) := r in
    (ds_level s' = ds_level s0 /\ ds_strategy s' = ds_strategy s0)
    /\ match o with
       | LCont => DRUN 3 0 true s' /\ 0 <= lzm s' < M0
       | LBreak => DRUN 3 0 true s' /\ ds_lookahead s' = 0 /\ flush <> Z_NO_FLUSH
       | LRet bs => bs = need_more /\ DPOST s' /\ NMPROG s'
       end.

  Lemma drun_dpost : forall s, DRUN 3 0 true s -> DPOST s.
  Proof. intros s [P _ _]. exact P. Qed.

  Lemma after_tally_run : forall M0 s0 s (b : bool),
    DRUN (if b then 0 else 3) 0 true s -> 0 <= lzm s < M0 -> ds_level s = ds_level s0 -> ds_strategy s = ds_strategy s0 ->
    (b = true -> fbo_ok ws PBL OCAP s 0) /\ LZPOST M0 s0 (after_tally s b).
  Proof.
    intros M0 s0 s b D HM EL ES. unfold after_tally, flush_block. destruct b.
    - destruct (fbo_run ws hs PBL ILEN OCAP tot0 TS TR HPBL 0 0 true s 0 ltac:(lia) D ltac:(left; reflexivity)) as (OK & P & SN & BS & FR).
      cbv zeta in P. cbv zeta in FR.
      split; [intros _; exact OK|].
      remember (flush_block_only s 0) as s1 eqn:Es1.
      assert (LS : ds_level s1 = ds_level s0 /\ ds_strategy s1 = ds_strategy s0) by (rewrite (ff_level _ _ FR), (ff_strategy _ _ FR); split; assumption).
      destruct (Z.eqb_spec (cs_avail_out (ds_strm s1)) 0) as [A|A]; cbn.
      + split; [exact LS|]. split; [reflexivity|]. split; [exact P | left; exact A].
      + split; [exact LS|]. split.
        * split; [exact P | ..]; apply (dp_flush _ _ _ _ _ _ _ _ _ _ P); exact A.
        * unfold lzm in *. rewrite (ff_lookahead _ _ FR), (ff_avail_in _ _ FR). exact HM.
    - split; [intros X; discriminate X|]. cbn. split; [split; assumption|]. split; [exact D | exact HM].
  Qed.

  Lemma dispatch_run : forall M0 s, DRUN 3 1 false s -> 1 <= ds_lookahead s ->
    (MIN_MATCH <= ds_match_length s -> 1 <= ds_strstart s - ds_match_start s <= ds_w_size s - MIN_LOOKAHEAD /\ ds_match_length s <= ds_lookahead s) ->
    (MIN_LOOKAHEAD <= ds_lookahead s \/ ds_strstart s + ds_lookahead s <= 2 * ds_w_size s - 2) ->
    1 <= ds_level s <= 3 -> lz_strat s -> lzm s <= M0 ->
    dispatch_ok ws PBL OCAP s /\ LZPOST M0 s (dispatch_spec s).
  Proof.
    intros M0 s D Hlook Hvalid G Hlv Hst HM. unfold dispatch_ok. rewrite dispatch_spec_eq'.
    pose proof (di_look _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))) as L0.
    pose proof (di_ml _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))) as ML0.
    destruct (Z.leb_spec MIN_MATCH (ds_match_length s)) as [Hm|Hm].
    - destruct (Hvalid Hm) as [V1 V2].
      destruct (match_run s D Hm V1 V2 G Hlv Hst) as [OK POST].
      unfold fast_disp in POST. rewrite (proj2 (Z.leb_le _ _) Hm) in POST.
      unfold fast_disp. rewrite (proj2 (Z.leb_le _ _) Hm).
      match goal with |- _ /\ LZPOST M0 s (let '(s', b) := ?X in after_tally s' b) => destruct X as [s' b] end.
      destruct POST as (D' & LF & L' & S' & Hb).
      destruct (after_tally_run M0 s s' b D' ltac:(unfold lzm in *; rewrite L', (zf_strm _ _ LF); pose proof (dc_ai _ _ _ _ (dp_call _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))); unfold MIN_MATCH in Hm; lia) (zf_level _ _ LF) (zf_strategy _ _ LF)) as [_ PQ].
      split; [exact OK | exact PQ].
    - destruct (lit_run 1 false s ltac:(lia) D Hlook ltac:(intros _; split; [exact Hlv | lia])) as [OK POST].
      unfold fast_disp. rewrite (proj2 (Z.leb_gt _ _) Hm). unfold lit_core in POST.
      match goal with |- _ /\ LZPOST M0 s (let '(s', b) := ?X in after_tally s' b) => replace X with (lit_core s) by reflexivity end.
      unfold lit_core. destruct (tr_tally_lit s (arr_get (ds_window s) (ds_strstart s))) as [s1 b]. cbn [fst snd] in POST.
      destruct POST as (D' & LF & L' & S' & Hb).
      destruct (after_tally_run M0 s _ b D' ltac:(unfold lzm in *; rewrite L', (zf_strm _ _ LF); pose proof (dc_ai _ _ _ _ (dp_call _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))); lia) (zf_level _ _ LF) (zf_strategy _ _ LF)) as [_ PQ].
      split; [exact OK | exact PQ].
  Qed.

  Lemma p1_run : forall M0 s, DRUN 3 0 true s -> 1 <= ds_lookahead s ->
    ds_strstart s + MIN_LOOKAHEAD <= 2 * ds_w_size s ->
    (MIN_LOOKAHEAD <= ds_lookahead s \/ ds_strstart s + ds_lookahead s <= 2 * ds_w_size s - 2) ->
    1 <= ds_level s <= 3 -> lz_strat s -> lzm s <= M0 ->
    p1_ok ws PBL OCAP s /\ LZPOST M0 s (p1_spec s).
  Proof.
    intros M0 s D Hlook Hstr G Hlv Hst HM. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    pose proof (dcfg_sizes s C) as (Sw & Sh & Sl & Shl).
    assert (KML : MIN_LOOKAHEAD = 262) by reflexivity. assert (KMM : MIN_MATCH = 3) by reflexivity.
    unfold p1_ok, p1_spec.
    pose proof (dinv_lzw 3 0 true s ltac:(lia) C I) as LZ0.
    destruct (Z.leb_spec MIN_MATCH (ds_lookahead s)) as [L3|L3].
    -
      pose proof (dinv_insert_string 3 true s C I L3) as INS. pose proof (dcfg_insert_string s (ds_strstart s) C) as C2.
      destruct (insert_string s (ds_strstart s)) as [s2 hh]. cbn [fst snd] in *.
      destruct INS as (I2 & Hhh & K2 & Q1 & Q2 & Q3 & HASH).
      assert (F : forall (f : deflate_state -> Z), (forall b a, kproj a = kproj b -> f a = f b) ->
                 (forall x a, f (set_head x a) = f x) -> (forall x a, f (set_prev x a) = f x) -> (forall x a, f (set_ins_h x a) = f x) -> f s2 = f s).
      { intros f E1 E2 E3 E4. rewrite <- (E1 _ _ K2), E2, E3, E4. reflexivity. }
      pose proof (F ds_strstart kp_strstart strstart_set_head strstart_set_prev strstart_set_ins_h) as Fstr.
      pose proof (F ds_lookahead kp_lookahead lookahead_set_head lookahead_set_prev lookahead_set_ins_h) as Flook.
      pose proof (F ds_match_length kp_match_length match_length_set_head match_length_set_prev match_length_set_ins_h) as Fml.
      pose proof (F ds_match_start kp_match_start match_start_set_head match_start_set_prev match_start_set_ins_h) as Fms.
      pose proof (F ds_w_size kp_w_size w_size_set_head w_size_set_prev w_size_set_ins_h) as Fws.
      pose proof (F ds_level kp_level level_set_head level_set_prev level_set_ins_h) as Flv.
      pose proof (F ds_strategy kp_strategy strategy_set_head strategy_set_prev strategy_set_ins_h) as Fsg.
      pose proof (F ds_prev_length kp_prev_length prev_length_set_head prev_length_set_prev prev_length_set_ins_h) as Fpl.
      assert (Fsm : ds_strm s2 = ds_strm s) by (pose proof (kp_strm _ _ K2) as X; rewrite strm_set_head, strm_set_prev, strm_set_ins_h in X; exact X).
      assert (LF2 : lzf s s2).
      { constructor; try assumption; try (apply F; [intros b a Hk | intros; reflexivity ..]);
          first [exact (kp_pending_out _ _ Hk) | exact (kp_w_size _ _ Hk) | exact (kp_hash_size _ _ Hk) | exact (kp_lit_bufsize _ _ Hk)
                | exact (kp_status _ _ Hk) | exact (kp_wrap _ _ Hk) | exact (kp_level _ _ Hk) | exact (kp_strategy _ _ Hk)
                | exact (kp_max_lazy_match _ _ Hk) | exact (kp_block_start _ _ Hk) | exact (kp_match_available _ _ Hk) ]. }
      assert (D2 : DRUN 3 1 true s2) by exact (drun_lzf _ _ _ _ _ _ _ _ D I2 C2 LF2).
      assert (LZ2 : lzw s2) by exact (dinv_lzw 3 1 true s2 ltac:(lia) C2 I2).
      assert (PL2 : ds_prev_length s2 = 2) by (rewrite Fpl; exact (di_fastpl _ _ _ _ I Hlv Hst)).
      assert (ML2 : ds_match_length s2 < 3) by (rewrite Fml; exact (di_fast _ _ _ _ I eq_refl Hlv Hst)).
      pose proof (dc_ai _ _ _ _ CL) as AI0.
      destruct (negb (hh =? NIL) && (wrap32 (ds_strstart s2 - hh) <=? ds_w_size s2 - MIN_LOOKAHEAD)) eqn:EC.
      + apply Bool.andb_true_iff in EC as [EC1 EC2]. apply Bool.negb_true_iff in EC1. apply Z.eqb_neq in EC1. apply Z.leb_le in EC2. unfold NIL in EC1.
        destruct (HASH Slz) as (Ins & Ihh & CH). specialize (Ihh EC1).
        pose proof (proj1 CH hh Ihh) as Rhh.
        rewrite Fstr, Fws in EC2. rewrite wrap32_id in EC2 by lia.
        destruct (lm_run 3 1 true s2 hh Ins C2 I2 ltac:(rewrite Flv; exact Slz) Ihh EC1 ltac:(rewrite Fstr, Fws; exact CH) ltac:(rewrite Fstr, Fws; exact EC2) Hhh
                    ltac:(rewrite Fstr, Fws; exact Hstr) ltac:(rewrite PL2; lia)) as [PRE POST].
        destruct (longest_match s2 hh) as [s3 ml]. destruct POST as (v & Es3 & Hv & M1 & M2 & M3 & Alt).
        rewrite PL2 in M2, M3, Alt. rewrite Flook in M1, M3.
        assert (I3 : dinvR 3 1 true s3).
        { rewrite Es3. apply dinv_set_match_start; [exact I2 | exact Hv | rewrite Flv; intros _ A; lia]. }
        assert (C3 : dcfg s3) by (rewrite Es3; apply dcfg_set_match_start; exact C2).
        assert (I4 : dinvR 3 1 false (set_match_length s3 ml)).
        { apply (dinv_set_match_length 3 1 true false s3 _ I3).
          - unfold MAX_MATCH in *. lia.
          - intros X; discriminate X.
          - intros X; discriminate X.
          - rewrite Es3. dsr. rewrite Flv. intros A. lia. }
        assert (C4 : dcfg (set_match_length s3 ml)) by (apply dcfg_set_match_length; exact C3).
        assert (LF4 : lzf s (set_match_length s3 ml)) by (eapply lzf_trans; [exact LF2 | rewrite Es3; constructor; dsr; reflexivity]).
        assert (D4 : DRUN 3 1 false (set_match_length s3 ml)) by exact (drun_lzf _ _ _ _ _ _ _ _ D I4 C4 LF4).
        remember (set_match_length s3 ml) as s4 eqn:Es4.
        assert (Y1 : 1 <= ds_lookahead s4) by (subst s4 s3; dsr; rewrite Flook; exact Hlook).
        assert (Y2 : MIN_MATCH <= ds_match_length s4 -> 1 <= ds_strstart s4 - ds_match_start s4 <= ds_w_size s4 - MIN_LOOKAHEAD /\ ds_match_length s4 <= ds_lookahead s4).
        { subst s4 s3. dsr. rewrite Fstr, Fws, Flook. intros Hm. destruct Alt as [[_ Bad] | [A B]]; [lia|]. lia. }
        assert (Y3 : MIN_LOOKAHEAD <= ds_lookahead s4 \/ ds_strstart s4 + ds_lookahead s4 <= 2 * ds_w_size s4 - 2) by (subst s4 s3; dsr; rewrite Flook, Fstr, Fws; exact G).
        assert (Y4 : 1 <= ds_level s4 <= 3) by (subst s4 s3; dsr; rewrite Flv; exact Hlv).
        assert (Y5 : lz_strat s4) by (subst s4 s3; unfold lz_strat; dsr; rewrite Fsg; exact Hst).
        assert (Y6 : lzm s4 <= M0) by (subst s4 s3; unfold lzm in *; dsr; rewrite Flook, Fsm; exact HM).
        destruct (dispatch_run M0 s4 D4 Y1 Y2 Y3 Y4 Y5 Y6) as [DOK DQ].
        assert (LS4 : ds_level s4 = ds_level s /\ ds_strategy s4 = ds_strategy s) by (split; [exact (zf_level _ _ LF4) | exact (zf_strategy _ _ LF4)]).
        split; [| revert DQ; unfold LZPOST; destruct (dispatch_spec s4) as [sx ox]; rewrite (proj1 LS4), (proj2 LS4); intros X; exact X].
        split; [exact LZ0|]. split; [exact Hlook|]. split; [exact LZ2|]. split; [exact PRE|].
        split; [exact (dinv_lzw 3 1 true _ ltac:(lia) C3 I3)|].
        split; [pose proof (di_sl _ _ _ _ I); lia|]. exact DOK.
      + assert (D2' : DRUN 3 1 false s2) by exact (drun_lzf _ _ _ _ _ _ _ _ D (dinv_fz_weaken _ _ _ I2) C2 LF2).
        destruct (dispatch_run M0 s2 D2') as [DOK DQ]; rewrite ?Flook, ?Fstr, ?Fws, ?Flv, ?Fml; try lia; try exact Hlv; try exact G.
        { unfold lz_strat. rewrite Fsg. exact Hst. }
        { unfold lzm in *. rewrite Flook, Fsm. exact HM. }
        split; [| revert DQ; unfold LZPOST; destruct (dispatch_spec s2) as [sx ox]; rewrite Flv, Fsg; intros X; exact X].
        split; [exact LZ0|]. split; [exact Hlook|]. split; [exact LZ2|]. exact DOK.
    -
      cbn [fst snd]. replace (negb (NIL =? NIL) && (wrap32 (ds_strstart s - NIL) <=? ds_w_size s - MIN_LOOKAHEAD)) with false by reflexivity.
      assert (D' : DRUN 3 1 false s) by exact (drun_lzf _ _ _ _ _ _ _ _ D (dinv_fz_weaken _ _ _ (dinv_hb01 _ _ _ I)) C (lzf_refl s)).
      pose proof (di_fast _ _ _ _ I eq_refl Hlv Hst) as ML.
      destruct (dispatch_run M0 s D' Hlook ltac:(intros Hm; lia) G Hlv Hst HM) as [DOK DQ].
      split; [| exact DQ].
      split; [exact LZ0|]. split; [exact Hlook|]. split; [exact LZ0|]. exact DOK.
  Qed.



  Lemma drun_dwin : forall rm fz s, DRUN rm 0 fz s -> dwin rm fz ws hs ILEN s.
  Proof.
    intros rm fz s [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0]. destruct CL. constructor; try assumption.
  Qed.
  Lemma dwin_drun : forall rm fz s s', DRUN rm 0 fz s -> dwin rm fz ws hs ILEN s' -> fwzap s' = fwzap s -> DRUN rm 0 fz s'.
  Proof.
    intros rm fz s s' [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0] W Z.
    destruct W as [C' I' Ews' Ehs' Wr' Lz' Il' Il32' Ni' Ai' In' Ti' Ad' Ad1'].
    pose proof (fw_pending _ _ Z) as E1. pose proof (fw_pending_out _ _ Z) as E2. pose proof (fw_status _ _ Z) as E3.
    pose proof (fw_lit_bufsize _ _ Z) as E4. pose proof (fw_level _ _ Z) as E5.
    pose proof (fw_cs_out_rev _ _ Z) as S1. pose proof (fw_cs_avail_out _ _ Z) as S2. pose proof (fw_cs_total_out _ _ Z) as S3.
    pose proof (fw_cs_data_type _ _ Z) as S4.
    split; [| rewrite E1; exact P0 | rewrite E2; exact PO0].
    constructor; try assumption; rewrite ?E3, ?E4, ?S2, ?E1, ?E2; try assumption.
    destruct CL; constructor; rewrite ?S1, ?S2, ?S3, ?S4; try assumption.
  Qed.

  Lemma trip_run : forall s, DRUN 3 0 true s -> 1 <= ds_level s <= 3 -> lz_strat s ->
    fast_trip_ok ws hs PBL OCAP s flush /\ LZPOST (lzm s) s (deflate_fast_body s flush).
  Proof.
    intros s D Hlv Hst. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    assert (KML : MIN_LOOKAHEAD = 262) by reflexivity.
    pose proof (dinv_lzw 3 0 true s ltac:(lia) C I) as LZ0.
    pose proof (di_look _ _ _ _ I) as L0. pose proof (di_sl _ _ _ _ I) as SL0. pose proof (dcfg_sizes s C) as (Sw & _).
    unfold fast_trip_ok. rewrite deflate_fast_body_eq.
    destruct (Z.ltb_spec (ds_lookahead s) MIN_LOOKAHEAD) as [Hl|Hl].
    - pose proof (drun_dwin _ _ _ D) as W.
      pose proof (dwin_fw_wf _ _ _ _ _ _ W) as WF.
      destruct (fw_run _ _ _ _ _ _ W Hl) as (W1 & Z1 & L1 & CONS & EX & ST1 & BS1 & MS1 & NI1 & NB1).
      remember (fill_window s) as s1 eqn:Es1.
      pose proof (dwin_drun _ _ _ _ D W1 Z1) as D1. pose proof D1 as [[C1 I1 _ _ _ _ _ _ _ _] _ _].
      pose proof (dinv_lzw 3 0 true s1 ltac:(lia) C1 I1) as LZ1.
      pose proof (dw_ws _ _ _ _ _ _ W1) as Ews1. pose proof (di_look _ _ _ _ I1) as L1'.
      assert (P1 : ds_lookahead s1 <> 0 -> p1_ok ws PBL OCAP s1 /\ LZPOST (lzm s) s1 (p1_spec s1)).
      { intros E0. apply (p1_run (lzm s) s1 D1); try lia.
        - rewrite (fw_level _ _ Z1). exact Hlv.
        - unfold lz_strat. rewrite (fw_strategy _ _ Z1). exact Hst.
        - unfold lzm in *. lia. }
      split.
      + split; [exact LZ0|]. split; [exact WF|]. split; [exact LZ1|].
        destruct ((ds_lookahead s1 <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)); [exact Logic.I|].
        destruct (Z.eqb_spec (ds_lookahead s1) 0) as [E0|E0]; [exact Logic.I|]. exact (proj1 (P1 E0)).
      + assert (LS1 : ds_level s1 = ds_level s /\ ds_strategy s1 = ds_strategy s) by (split; [exact (fw_level _ _ Z1) | exact (fw_strategy _ _ Z1)]).
        cbv zeta. destruct (Z.ltb_spec (ds_lookahead s1) MIN_LOOKAHEAD) as [Hl1|Hl1]; destruct (Z.eqb_spec flush Z_NO_FLUSH) as [F0|F0]; cbn [andb].
        1: { unfold LZPOST; cbv beta iota. split; [exact LS1|]. split; [reflexivity|]. split; [exact (drun_dpost _ D1)|].
             right; split; [destruct EX as [X|X]; [exact X | exfalso; clear -X Hl1 KML; lia] | exact F0]. }
        all: destruct (Z.eqb_spec (ds_lookahead s1) 0) as [E0|E0]; [unfold LZPOST; cbv beta iota; split; [exact LS1|]; split; [exact D1|]; split; [exact E0 | first [exact F0 | exfalso; clear -E0 Hl1 KML; lia]]|].
        all: pose proof (proj2 (P1 E0)) as X; revert X; unfold LZPOST; destruct (p1_spec s1) as [sx ox]; rewrite (proj1 LS1), (proj2 LS1); intros X; exact X.
    - destruct (p1_run (lzm s) s D ltac:(lia) ltac:(lia) ltac:(left; lia) Hlv Hst ltac:(lia)) as [OK PQ].
      split; [| exact PQ]. split; [exact LZ0 | exact OK].
  Qed.

  Definition BPOST (s0 s' : deflate_state) (bs : block_state) : Prop :=
    DPOST s' /\ ds_level s' = ds_level s0 /\ ds_strategy s' = ds_strategy s0
    /\ match bs with
       | need_more => NMPROG s'
       | block_done => DRUN 3 0 true s' /\ ds_sym_next s' = 0 /\ ds_lookahead s' = 0 /\ flush <> Z_FINISH /\ ds_match_available s' = 0 /\ flush <> Z_NO_FLUSH
       | finish_started => ds_lookahead s' = 0 /\ flush = Z_FINISH /\ ds_sym_next s' = 0 /\ cs_avail_out (ds_strm s') = 0
       | finish_done => DRUN 3 0 true s' /\ ds_sym_next s' = 0 /\ ds_lookahead s' = 0 /\ flush = Z_FINISH /\ ds_match_available s' = 0
       end.

  Lemma loop_run : forall n s, DRUN 3 0 true s -> 1 <= ds_level s <= 3 -> lz_strat s -> lzm s < Z.of_nat n ->
    fast_loop_ok ws hs PBL OCAP n s flush
    /\ let '(s', r) := deflate_fast_loop n s flush in
       ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s
       /\ match r with None => DRUN 3 0 true s' /\ ds_lookahead s' = 0 /\ flush <> Z_NO_FLUSH | Some bs => bs = need_more /\ DPOST s' /\ NMPROG s' end.
  Proof.
    induction n as [|n IH]; intros s D Hlv Hst HM.
    { exfalso. unfold lzm in HM. pose proof (di_look _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))).
      pose proof (dc_ai _ _ _ _ (dp_call _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))). cbn in HM. lia. }
    cbn [fast_loop_ok]. rewrite deflate_fast_loop_step.
    destruct (trip_run s D Hlv Hst) as [TOK TP].
    destruct (deflate_fast_body s flush) as [s1 o]. destruct TP as [[EL ES] TP].
    destruct o as [| |bs].
    - destruct TP as [D1 M1].
      destruct (IH s1 D1 ltac:(rewrite EL; exact Hlv) ltac:(unfold lz_strat; rewrite ES; exact Hst) ltac:(rewrite Nat2Z.inj_succ in HM; lia)) as [LOK LP].
      split; [split; [exact TOK | exact LOK]|].
      destruct (deflate_fast_loop n s1 flush) as [s' r]. destruct LP as (EL' & ES' & LP). split; [congruence|]. split; [congruence|]. exact LP.
    - split; [split; [exact TOK | exact Logic.I]|]. split; [exact EL|]. split; [exact ES|]. exact TP.
    - split; [split; [exact TOK | exact Logic.I]|]. split; [exact EL|]. split; [exact ES|]. exact TP.
  Qed.

  Lemma drun_room : forall rm rm' hb fz s, DRUN rm hb fz s -> ds_sym_next s + rm' <= ds_sym_end s -> DRUN rm' hb fz s.
  Proof.
    intros rm rm' hb fz s [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0] R.
    split; [| exact P0 | exact PO0]. constructor; try assumption. destruct I; constructor; try assumption.
  Qed.

  Lemma tailv_run : forall rm s v, 0 <= rm -> DRUN rm 0 true s -> ds_lookahead s = 0 -> 0 <= v <= ds_strstart s ->
    ds_match_available s = 0 -> flush <> Z_NO_FLUSH ->
    (lzw s
     /\ let s1 := set_insert s v in
        - 2 ^ 63 <= ds_block_start s1 < 2 ^ 63
        /\ if Z.eqb flush Z_FINISH then fbo_ok ws PBL OCAP s1 1 else (ds_sym_next s1 <> 0 -> fbo_ok ws PBL OCAP s1 0))
    /\ let '(s', bs) := (let s1 := set_insert s v in deflate_tail s1 flush) in
       BPOST s s' bs.
  Proof.
    intros rm s v Hrm D Hlook Hv Hma HNF. pose proof D as [[C I CL Ews Ehs Epbl Sst Swr Slz Sfl] P0 PO0].
    unfold deflate_tail. cbv zeta.
    assert (I1 : dinvR rm 0 true (set_insert s v)) by (apply dinv_set_insert; [exact I | exact Hv]).
    assert (C1 : dcfg (set_insert s v)) by (apply dcfg_set_insert; exact C).
    assert (D1 : DRUN rm 0 true (set_insert s v)).
    { eapply drun_lzf; [exact D | exact I1 | exact C1 | constructor; dsr; reflexivity]. }
    remember (set_insert s v) as s1 eqn:Es1.
    assert (LZ1 : lzw s1) by exact (dinv_lzw rm 0 true s1 Hrm C1 I1). assert (LZ0 : lzw s) by exact (dinv_lzw rm 0 true s Hrm C I).
    assert (L1 : ds_lookahead s1 = 0) by (subst s1; dsr; exact Hlook).
    assert (MA1 : ds_match_available s1 = 0) by (subst s1; dsr; exact Hma).
    assert (LV1 : ds_level s1 = ds_level s /\ ds_strategy s1 = ds_strategy s) by (subst s1; dsr; split; reflexivity). pose proof LV1 as [LVa LVb].
    assert (BS1 : - 2 ^ 63 <= ds_block_start s1 < 2 ^ 63).
    { pose proof (drun_span rm 0 true _ _ _ _ _ _ s1 Hrm (dr_post _ _ _ _ _ _ _ _ _ _ D1)) as (R & RS & _). lia. }
    unfold flush_block.
    destruct (Z.eqb_spec flush Z_FINISH) as [HF|HF].
    - destruct (fbo_run ws hs PBL ILEN OCAP tot0 TS TR HPBL rm 0 true s1 1 Hrm D1 ltac:(right; reflexivity)) as (OK & P & SN & BS & FR). cbv zeta in P. cbv zeta in FR.
      split; [split; [exact LZ0|]; split; [exact BS1 | exact OK]|].
      remember (flush_block_only s1 1) as s2 eqn:Es2.
      pose proof (ff_lookahead _ _ FR) as L2. pose proof (ff_level _ _ FR) as EL2. pose proof (ff_strategy _ _ FR) as ES2.
      pose proof (ff_match_available _ _ FR) as MA2.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm s2)) 0) as [A|A]; cbn -[DPOST DRUN Z_FINISH].
      + split; [exact P|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [exact HF|]. split; [exact SN | exact A].
      + split; [exact P|]. split; [congruence|]. split; [congruence|].
        split; [split; [exact P | ..]; apply (dp_flush _ _ _ _ _ _ _ _ _ _ P); exact A|]. split; [exact SN|]. split; [congruence|]. split; [exact HF | congruence].
    - destruct (Z.eqb_spec (ds_sym_next s1) 0) as [Z0|Z0]; cbn -[DPOST DRUN Z_FINISH].
      + split; [split; [exact LZ0|]; split; [exact BS1 | intros X; exfalso; exact (X Z0)]|].
        assert (D1' : DRUN 3 0 true s1) by (apply (drun_room rm 3 0 true s1 D1); rewrite Z0, (cf_symend _ C1); pose proof (dcfg_sizes s1 C1); lia).
        split; [exact (drun_dpost _ D1')|]. split; [exact (proj1 LV1)|]. split; [exact (proj2 LV1)|].
        split; [exact D1'|]. split; [exact Z0|]. split; [exact L1|]. split; [exact HF|]. split; [exact MA1 | exact HNF].
      + destruct (fbo_run ws hs PBL ILEN OCAP tot0 TS TR HPBL rm 0 true s1 0 Hrm D1 ltac:(left; reflexivity)) as (OK & P & SN & BS & FR). cbv zeta in P. cbv zeta in FR.
        split; [split; [exact LZ0|]; split; [exact BS1 | intros _; exact OK]|].
        remember (flush_block_only s1 0) as s2 eqn:Es2.
        pose proof (ff_lookahead _ _ FR) as L2. pose proof (ff_level _ _ FR) as EL2. pose proof (ff_strategy _ _ FR) as ES2.
        pose proof (ff_match_available _ _ FR) as MA2.
        destruct (Z.eqb_spec (cs_avail_out (ds_strm s2)) 0) as [A|A]; cbn -[DPOST DRUN Z_FINISH].
        * split; [exact P|]. split; [congruence|]. split; [congruence | left; exact A].
        * split; [exact P|]. split; [congruence|]. split; [congruence|].
          split; [split; [exact P | ..]; apply (dp_flush _ _ _ _ _ _ _ _ _ _ P); exact A|]. split; [exact SN|]. split; [congruence|]. split; [exact HF|]. split; [congruence | exact HNF].
  Qed.

  Lemma tail_run : forall rm s, 0 <= rm -> DRUN rm 0 true s -> ds_lookahead s = 0 -> ds_match_available s = 0 -> flush <> Z_NO_FLUSH ->
    tail_ok ws PBL OCAP s flush
    /\ let '(s', bs) := (let s1 := set_insert s (if ds_strstart s <? MIN_MATCH - 1 then ds_strstart s else MIN_MATCH - 1) in deflate_tail s1 flush) in
       BPOST s s' bs.
  Proof.
    intros rm s Hrm D Hlook Hma HNF. unfold tail_ok. apply (tailv_run rm s _ Hrm D Hlook); [| exact Hma | exact HNF].
    pose proof (di_str _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D))).
    unfold MIN_MATCH. destruct (Z.ltb_spec (ds_strstart s) (3 - 1)); lia.
  Qed.

  Theorem fast_run : forall s, DRUN 3 0 true s -> 1 <= ds_level s <= 3 -> lz_strat s ->
    fast_ok ws hs PBL OCAP s flush
    /\ let '(s', bs) := deflate_fast s flush in BPOST s s' bs.
  Proof.
    intros s D Hlv Hst. unfold fast_ok, deflate_fast.
    pose proof D as [[C I CL _ _ _ _ _ _ _] _ _].
    destruct (loop_run (lz_fuel s) s D Hlv Hst) as [LOK LP].
    { unfold lz_fuel, lzm. pose proof (di_look _ _ _ _ I). pose proof (dc_ai _ _ _ _ CL). rewrite Z2Nat.id by lia. lia. }
    assert (MA : forall s1, DRUN 3 0 true s1 -> ds_level s1 = ds_level s -> ds_match_available s1 = 0).
    { intros s1 D1 EL. pose proof (di_maslow _ _ _ _ (dp_inv _ _ _ _ _ _ _ _ _ _ (dr_post _ _ _ _ _ _ _ _ _ _ D1))) as X.
      destruct (Z.eq_dec (ds_match_available s1) 0) as [E|E]; [exact E | exfalso; pose proof (X E) as [Y _]; rewrite EL in Y; lia]. }
    split; [split; [exact LOK|]|]; destruct (deflate_fast_loop (lz_fuel s) s flush) as [s1 r]; destruct LP as (EL & ES & LP).
    - destruct r as [bs|]; [exact Logic.I|]. destruct LP as (D1 & L1 & NF). exact (proj1 (tail_run 3 s1 ltac:(lia) D1 L1 (MA s1 D1 EL) NF)).
    - destruct r as [bs|].
      + destruct LP as (-> & P & NM). split; [exact P|]. split; [exact EL|]. split; [exact ES | exact NM].
      + destruct LP as (D1 & L1 & NF). pose proof (proj2 (tail_run 3 s1 ltac:(lia) D1 L1 (MA s1 D1 EL) NF)) as TP. cbv zeta in TP.
        match goal with |- let '(s', bs) := ?X in _ => destruct X as [s' bs] end.
        destruct TP as (P & EL' & ES' & R). split; [exact P|]. split; [congruence|]. split; [congruence | exact R].
  Qed.
End FAST.
