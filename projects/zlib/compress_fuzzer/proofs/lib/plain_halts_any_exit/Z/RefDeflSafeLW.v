(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition fwG (s : deflate_state) :=
  ((ds_w_size s, ds_hash_size s, ds_lit_bufsize s,
    (ds_self_blk s, ds_window_blk s, ds_prev_blk s, ds_head_blk s, ds_pending_buf_blk s)),
   ds_strstart s - ds_block_start s,
   cs_next_in (ds_strm s) + cs_avail_in (ds_strm s),
   cs_input (ds_strm s),
   wrap32 (ds_strstart s - ds_match_start s)).

Lemma fwG_read_buf : forall s off n, fwG (fst (read_buf s (RB_window off) n)) = fwG s.
Proof.
  intros s off n. unfold read_buf. cbv beta iota zeta. dsred.
  destruct ((if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) =? 0); [reflexivity|].
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; unfold fwG; dsred; cbn [cs_next_in cs_avail_in cs_input];
    (apply (f_equal2 pair); [apply (f_equal2 pair); [apply (f_equal2 pair); [apply (f_equal2 pair); [reflexivity | try reflexivity; lia] | lia] | reflexivity] | reflexivity]).
Qed.

Lemma fwG_insert : forall n s str, fwG (fill_window_insert n s str) = fwG s.
Proof.
  induction n as [|n IH]; intros s str; [reflexivity|].
  cbn -[fwG update_hash Z.ltb Z.eqb Z.add Z.sub Z.land arr_get arr_set wrap16 negb].
  destruct (negb (ds_insert s =? 0)); [|reflexivity].
  destruct (_ <? _); [unfold fwG; dsred; reflexivity|].
  rewrite IH. unfold fwG; dsred; reflexivity.
Qed.

Lemma wrap32_sub_wrap32 : forall a b, wrap32 (a - wrap32 b) = wrap32 (a - b).
Proof. intros a b. rewrite !wrap32_mod. apply Zminus_mod_idemp_r. Qed.

Lemma fwG_slide : forall s ws more, fwG (fw_slide s ws more) = fwG s.
Proof.
  intros s ws more. unfold fw_slide, slide_hash. destruct (_ <? _); unfold fwG; dsred;
    (apply (f_equal2 pair); [apply (f_equal2 pair); [apply (f_equal2 pair); [apply (f_equal2 pair); [reflexivity | lia] | reflexivity] | reflexivity] | rewrite wrap32_sub_wrap32; f_equal; lia]).
Qed.

Lemma fwG_body : forall s ws, fwG (fst (fill_window_body s ws)) = fwG s.
Proof.
  intros s ws. rewrite fill_window_body_eq.
  set (s1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then fw_slide s ws (fw_more s) else s).
  set (m1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then wrap32 (fw_more s + ws) else fw_more s).
  assert (E1 : fwG s1 = fwG s) by (subst s1; destruct (_ <=? _); [apply fwG_slide | reflexivity]).
  replace (if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then (fw_slide s ws (fw_more s), wrap32 (fw_more s + ws)) else (s, fw_more s))
    with (s1, m1) by (subst s1 m1; destruct (_ <=? _); reflexivity).
  cbv beta iota zeta.
  destruct (cs_avail_in (ds_strm s1) =? 0); [exact E1|].
  destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) m1) as [s2 n] eqn:E2.
  pose proof (fwG_read_buf s1 (ds_strstart s1 + ds_lookahead s1) m1) as E2'. rewrite E2 in E2'. cbn [fst] in E2'.
  cbn [fst]. unfold fw_insert. dsred. destruct (MIN_MATCH <=? _).
  - rewrite fwG_insert. rewrite <- E1, <- E2'. unfold fwG; dsred; reflexivity.
  - rewrite <- E1, <- E2'. unfold fwG; dsred; reflexivity.
Qed.

Lemma fwG_loop : forall n s ws, fwG (fill_window_loop n s ws) = fwG s.
Proof.
  induction n as [|n IH]; intros s ws; [reflexivity|].
  rewrite fill_window_loop_step. destruct (fill_window_body s ws) as [s1 b] eqn:E.
  pose proof (fwG_body s ws) as E'. rewrite E in E'. cbn [fst] in E'.
  destruct b; [exact E'|]. destruct (_ && _); [rewrite IH; exact E' | exact E'].
Qed.

Lemma fwG_high : forall s, fwG (fill_window_high s) = fwG s.
Proof.
  intros s. unfold fill_window_high.
  destruct (_ <? _); [|reflexivity]. destruct (_ <? _); [unfold fwG; dsred; reflexivity|].
  destruct (_ <? _); [unfold fwG; dsred; reflexivity | reflexivity].
Qed.

Lemma fwG_fill_window : forall s, fwG (fill_window s) = fwG s.
Proof. intros s. unfold fill_window. rewrite fwG_high, fwG_loop. reflexivity. Qed.

Lemma fwG_fields : forall s s', fwG s' = fwG s ->
  (ds_w_size s', ds_hash_size s', ds_lit_bufsize s', (ds_self_blk s', ds_window_blk s', ds_prev_blk s', ds_head_blk s', ds_pending_buf_blk s'))
  = (ds_w_size s, ds_hash_size s, ds_lit_bufsize s, (ds_self_blk s, ds_window_blk s, ds_prev_blk s, ds_head_blk s, ds_pending_buf_blk s))
  /\ ds_strstart s' - ds_block_start s' = ds_strstart s - ds_block_start s
  /\ cs_next_in (ds_strm s') + cs_avail_in (ds_strm s') = cs_next_in (ds_strm s) + cs_avail_in (ds_strm s)
  /\ cs_input (ds_strm s') = cs_input (ds_strm s)
  /\ wrap32 (ds_strstart s' - ds_match_start s') = wrap32 (ds_strstart s - ds_match_start s).
Proof.
  intros s s' E. unfold fwG in E.
  apply pair_equal_spec in E; destruct E as [E E5].
  apply pair_equal_spec in E; destruct E as [E E4]. apply pair_equal_spec in E; destruct E as [E E3].
  apply pair_equal_spec in E; destruct E as [E1 E2]. repeat split; assumption.
Qed.

Record FWX (s : deflate_state) : Prop := {
  fx_chain : CHAIN s (ds_strstart s - 1) (ds_strstart s - 1);
  fx_insh : 0 <= ds_ins_h s < 65536;
  fx_ins : ds_insert s <= ds_w_size s;
  fx_hw : ds_high_water s <= ds_window_size s;
  fx_ad : 0 <= cs_adler (ds_strm s) < 2 ^ 64 }.

Section WF.
  Variables ws hs : Z.

  Variable wk : Z.
  Hypothesis Hwk : 0 <= wk /\ ws = 2 ^ wk.

  Lemma FWX_same : forall s s', FWX s ->
    ds_head s' = ds_head s -> ds_prev s' = ds_prev s -> ds_hash_size s' = ds_hash_size s -> ds_w_size s' = ds_w_size s ->
    ds_w_mask s' = ds_w_mask s -> ds_strstart s' = ds_strstart s -> ds_ins_h s' = ds_ins_h s -> ds_insert s' <= ds_insert s ->
    ds_high_water s' = ds_high_water s -> ds_window_size s' = ds_window_size s -> ds_strm s' = ds_strm s -> FWX s'.
  Proof.
    intros s s' X E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11. destruct X. constructor.
    - rewrite E6. apply (CHAIN_same s s'); assumption.
    - rewrite E7. assumption.
    - rewrite E4. lia.
    - rewrite E9, E10. assumption.
    - rewrite E11. assumption.
  Qed.

  Lemma FWX_same' : forall s s', FWX s ->
    ds_head s' = ds_head s -> ds_prev s' = ds_prev s -> ds_hash_size s' = ds_hash_size s -> ds_w_size s' = ds_w_size s ->
    ds_w_mask s' = ds_w_mask s -> ds_strstart s' = ds_strstart s -> 0 <= ds_ins_h s' < 65536 -> ds_insert s' <= ds_insert s ->
    ds_high_water s' = ds_high_water s -> ds_window_size s' = ds_window_size s -> ds_strm s' = ds_strm s -> FWX s'.
  Proof.
    intros s s' X E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11. destruct X. constructor.
    - rewrite E6. apply (CHAIN_same s s'); assumption.
    - exact E7.
    - rewrite E4. lia.
    - rewrite E9, E10. assumption.
    - rewrite E11. assumption.
  Qed.

  Lemma FWX_slide : forall s more, fw_wf ws hs s -> FWX s -> ws + (ws - 262) <= ds_strstart s -> FWX (fw_slide s ws more).
  Proof.
    intros s more HW X Hsl. pose proof HW as HW'. destruct HW. destruct X as [Xc Xi Xn Xh Xa].
    set (s0 := set_block_start (set_strstart (set_match_start (set_window s
                   (arr_blit (ds_window s) 0 (ds_window s) ws (wrap32 (ws - more)))) (wrap32 (ds_match_start s - ws))) (ds_strstart s - ws)) (ds_block_start s - ws)).
    pose proof (CHAIN_slide_hash s0 (ds_strstart s - 1) (ds_strstart s - 1) wk) as HC.
    subst s0. revert HC. dsred. intros HC.
    specialize (HC ltac:(apply (CHAIN_same s); dsred; try reflexivity; exact Xc) ltac:(rewrite wf_ws; lia) ltac:(lia)
                   ltac:(rewrite wf_wmask, wf_ws; reflexivity) ltac:(rewrite wf_pl, wf_ws; reflexivity) ltac:(rewrite wf_hl, wf_hs; reflexivity)
                   ltac:(rewrite wf_hs; lia) ltac:(rewrite wf_hs; intros i Hi; apply wf_hb; exact Hi) ltac:(rewrite wf_ws; intros i Hi; apply wf_pb; exact Hi)).
    rewrite wf_ws in HC.
    unfold fw_slide. cbv zeta. unfold slide_hash in *. dsred. destruct (Z.ltb_spec (ds_strstart s - ws) (ds_insert s)) as [C|C].
    - constructor; dsred; try assumption; try lia.
      replace (ds_strstart s - ws - 1) with (ds_strstart s - 1 - ws) by lia.
      revert HC. unfold CHAIN, CHAINW. dsred. intros HC. exact HC.
    - constructor; dsred; try assumption; try lia.
      replace (ds_strstart s - ws - 1) with (ds_strstart s - 1 - ws) by lia.
      revert HC. unfold CHAIN, CHAINW. dsred. intros HC. exact HC.
  Qed.

  Lemma FWX_read_buf : forall s off n, fw_wf ws hs s -> FWX s -> 0 <= n -> FWX (fst (read_buf s (RB_window off) n)).
  Proof.
    intros s off n HW X Hn0. pose proof (wf_ib _ _ _ HW) as Hib. pose proof (wf_ai _ _ _ HW) as Hai. pose proof (wf_ni _ _ _ HW) as Hni.
    pose proof (wf_inlen _ _ _ HW) as Hil.
    unfold read_buf. cbv beta iota zeta. dsred.
    set (len := if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)).
    destruct (Z.eqb_spec len 0) as [L0|L0]; [exact X|].
    assert (Hlen : 0 <= len <= cs_avail_in (ds_strm s)) by (subst len; destruct (Z.ltb_spec n (cs_avail_in (ds_strm s))); lia).
    assert (Hbytes : forall b, In b (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) len) -> 0 <= b < 256).
    { intros b Hb. eapply arr_slice_In; [|exact Hb]. intros i Hi. apply Hib. lia. }
    destruct X as [Xc Xi Xn Xh Xa].
    destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; constructor; dsred; cbn [cs_adler]; try assumption.
    all: try (revert Xc; unfold CHAIN, CHAINW; dsred; intros Xc; exact Xc).
    - apply adler32_upd_range. exact Hbytes.
    - pose proof (crc32_upd_range (cs_adler (ds_strm s)) _ Hbytes). lia.
  Qed.

  Lemma insert_string_fst : forall s str,
    fst (insert_string s str) =
    (let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) in
     set_head (set_prev (set_ins_h s h) (arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) h)))
              (arr_set (ds_head s) h (wrap16 str))).
  Proof. intros s str. reflexivity. Qed.

  Lemma FWX_insert : forall n s str,
    ds_insert s = Z.of_nat n -> fw_wf ws hs s -> FWX s -> 0 <= str -> ds_insert s = ds_strstart s - str ->
    FWX (fill_window_insert (Z.to_nat (ds_insert s)) s str).
  Proof.
    induction n as [|n IH]; intros s str Hn HW X Hstr Hins.
    - rewrite Hn. change (Z.to_nat (Z.of_nat 0)) with 0%nat. cbn [fill_window_insert]. exact X.
    - rewrite (fill_window_insert_step (ds_insert s) s str) by lia.
      replace (ds_insert s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv zeta.
      pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_hsr _ _ _ HW) as Lhs. pose proof (wf_sl _ _ _ HW) as Vsl.
      pose proof (wf_hmask _ _ _ HW) as Vhm. pose proof (wf_ws _ _ _ HW) as Vws. pose proof (wf_wmask _ _ _ HW) as Vwm.
      pose proof (wf_pl _ _ _ HW) as Vpl. pose proof (wf_hl _ _ _ HW) as Vhl. pose proof (wf_hs _ _ _ HW) as Vhs.
      pose proof (wf_look _ _ _ HW) as Vlook.

      set (s3 := set_head (set_prev (set_ins_h s _) _) _).
      assert (E3 : s3 = fst (insert_string s str)) by (subst s3; rewrite insert_string_fst; reflexivity).
      assert (HC3 : CHAIN s3 (ds_strstart s - 1) (ds_strstart s - 1)).
      { rewrite E3.
        destruct (CHAIN_insert_string s str (ds_strstart s - 1) (ds_strstart s - 1) wk (fx_chain _ X)
                    ltac:(rewrite Vws; lia) ltac:(lia) ltac:(rewrite Vwm, Vws; reflexivity) ltac:(rewrite Vpl, Vws; reflexivity)
                    ltac:(rewrite Vhl, Vhs; reflexivity) ltac:(rewrite Vhm; lia) ltac:(rewrite Vhm, Vhs; reflexivity) ltac:(lia)) as [HC _].
        replace (Z.max (ds_strstart s - 1) str) with (ds_strstart s - 1) in HC by lia.
        replace (Z.max (ds_strstart s - 1) (ds_strstart s - 1)) with (ds_strstart s - 1) in HC by lia. exact HC. }
      assert (Hh : 0 <= update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) <= ds_hash_mask s).
      { apply update_hash_range. rewrite Vhm. lia. }
      set (s4 := set_insert s3 (ds_insert s3 - 1)).
      assert (X4 : FWX s4).
      { subst s4 s3. constructor; dsred.
        - revert HC3. unfold CHAIN, CHAINW. dsred. intros HC. exact HC.
        - rewrite Vhm in Hh. lia.
        - pose proof (fx_ins _ X). lia.
        - exact (fx_hw _ X).
        - exact (fx_ad _ X). }
      assert (HW4 : fw_wf ws hs s4).
      { subst s4 s3. destruct HW; constructor; dsred; try assumption; try lia.
        - rewrite arr_len_set. assumption.
        - rewrite arr_len_set. assumption.
        - intros i Hi. rewrite arr_get_set. destruct (_ && _); [apply wf_hb; rewrite Vhm in Hh; lia | apply wf_pb; exact Hi].
        - intros i Hi. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply wf_hb; exact Hi]. }
      destruct (Z.ltb_spec (ds_lookahead s4 + ds_insert s4) MIN_MATCH) as [Sm|Bg]; [exact X4|].
      replace (Z.to_nat (ds_insert s - 1)) with (Z.to_nat (ds_insert s4)) by (subst s4 s3; dsred; reflexivity).
      apply (IH s4 (str + 1)); subst s4 s3; dsred; try assumption; lia.
  Qed.

  Lemma FWX_fw_insert : forall s, fw_wf ws hs s -> FWX s -> FWX (fw_insert s).
  Proof.
    intros s HW X. unfold fw_insert.
    destruct (Z.leb_spec MIN_MATCH (ds_lookahead s + ds_insert s)) as [Big|Small]; [| exact X]. cbv zeta.
    pose proof (wf_ins _ _ _ HW) as Vins. pose proof (wf_hmask _ _ _ HW) as Vhm. pose proof (wf_hsr _ _ _ HW) as Lhs.
    set (s2 := set_ins_h (set_ins_h s _) _).
    assert (Hh : 0 <= ds_ins_h s2 < 65536).
    { subst s2. dsred.
      match goal with |- 0 <= update_hash ?t ?a ?b < 65536 =>
        pose proof (update_hash_range t a b ltac:(dsred; rewrite Vhm; lia)) as R end.
      revert R. dsred. rewrite Vhm. intros R. lia. }
    assert (X2 : FWX s2) by (apply (FWX_same' s); [exact X | ..]; subst s2; dsred; try reflexivity; try lia; exact Hh).
    assert (HW2 : fw_wf ws hs s2) by (revert Hh; subst s2; dsred; intros Hh; destruct HW; constructor; dsred; try assumption; lia).
    replace (Z.to_nat (ds_insert s)) with (Z.to_nat (ds_insert s2)) by (subst s2; reflexivity).
    remember (Z.to_nat (ds_insert s2)) as n eqn:Hn.
    rewrite Hn. apply (FWX_insert n s2 (ds_strstart s - ds_insert s)); subst s2; dsred; try assumption; try lia.
    revert Hn. dsred. intros Hn. rewrite Hn, Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma FWX_high : forall s, fw_wf ws hs s -> FWX s -> FWX (fill_window_high s).
  Proof.
    intros s HW X. pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vlook. pose proof (wf_wsz _ _ _ HW) as Vwsz.
    pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_ins _ _ _ HW) as Vins.
    unfold fill_window_high, WIN_INIT, MAX_MATCH.
    destruct (Z.ltb_spec (ds_high_water s) (ds_window_size s)) as [C1|C1]; [| exact X]. cbv zeta.
    destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s)) as [C2|C2];
      [| destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s + 258)) as [C3|C3]; [| exact X]];
      destruct X; constructor; dsred; try assumption.
    - destruct (Z.ltb_spec 258 (ds_window_size s - (ds_strstart s + ds_lookahead s))); lia.
    - destruct (Z.ltb_spec (ds_window_size s - ds_high_water s) (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)); lia.
  Qed.

  Lemma FWX_body : forall s, fw_wf ws hs s -> FWX s -> ds_lookahead s < MIN_LOOKAHEAD ->
    let '(s', brk) := fill_window_body s ws in
    FWX s' /\ (ds_lookahead s' < MIN_LOOKAHEAD -> ds_strstart s' + ds_lookahead s' <= 2 * ws - 2) /\ ds_strstart s' <= 2 * ws - MIN_LOOKAHEAD - 1
    /\ (1 <= ds_strstart s -> 1 <= ds_strstart s') /\ ds_lookahead s <= ds_lookahead s'.
  Proof.
    intros s HW X Hlook. rewrite fill_window_body_eq.
    pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vlook.
    pose proof (wf_ws _ _ _ HW) as Vws. pose proof (wf_wsz _ _ _ HW) as Vwsz. pose proof (wf_ins _ _ _ HW) as Vins.
    unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
    assert (Hmore : fw_more s = 2 * ws - ds_lookahead s - ds_strstart s).
    { unfold fw_more. rewrite Vwsz. rewrite wrap32_id by lia. lia. }
    destruct (Z.leb_spec (ws + (ds_w_size s - (258 + 3 + 1))) (ds_strstart s)) as [Sl|Ns].
    - destruct (fw_slide_wf ws hs s (fw_more s) HW ltac:(lia) Hmore) as (HW1 & HC1 & HL1 & HS1).
      pose proof (FWX_slide s (fw_more s) HW X ltac:(lia)) as X1.
      set (s1 := fw_slide s ws (fw_more s)) in *.
      assert (Hm1 : wrap32 (fw_more s + ws) = 3 * ws - ds_lookahead s - ds_strstart s) by (rewrite Hmore; rewrite wrap32_id by lia; lia).
      rewrite Hm1.
      destruct (Z.eqb_spec (cs_avail_in (ds_strm s1)) 0) as [A0|A0].
      + split; [exact X1|]. rewrite HS1, HL1. split; [intros _; lia | lia].
      + destruct (read_buf_wf ws hs s1 (ds_strstart s1 + ds_lookahead s1) (3 * ws - ds_lookahead s - ds_strstart s) HW1 eq_refl
                    ltac:(lia) ltac:(lia)) as (HW2 & HC2 & HL2 & HS2 & _ & _ & _ & _ & _ & Hn & Hpos & _).
        pose proof (FWX_read_buf s1 (ds_strstart s1 + ds_lookahead s1) (3 * ws - ds_lookahead s - ds_strstart s) HW1 X1 ltac:(lia)) as X2.
        destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) (3 * ws - ds_lookahead s - ds_strstart s)) as [s2 n].
        cbn [fst snd] in *.
        assert (HW3 : fw_wf ws hs (set_lookahead s2 (ds_lookahead s2 + n))) by (destruct HW2; constructor; dsred; try assumption; lia).
        assert (X3 : FWX (set_lookahead s2 (ds_lookahead s2 + n))) by (apply (FWX_same s2); [exact X2 | ..]; dsred; try reflexivity; lia).
        destruct (fw_insert_wf ws hs _ HW3) as (HW4 & HC4 & HL4 & HS4 & _).
        split; [exact (FWX_fw_insert _ HW3 X3)|].
        rewrite HS4, HL4. dsred. rewrite HS2, HL2, HS1, HL1. split; [intros Hl4; lia | lia].
    - destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [A0|A0].
      + split; [exact X|]. split; [intros _; lia | lia].
      + destruct (read_buf_wf ws hs s (ds_strstart s + ds_lookahead s) (fw_more s) HW eq_refl ltac:(lia) ltac:(lia))
          as (HW2 & HC2 & HL2 & HS2 & _ & _ & _ & _ & _ & Hn & Hpos & _).
        pose proof (FWX_read_buf s (ds_strstart s + ds_lookahead s) (fw_more s) HW X ltac:(lia)) as X2.
        destruct (read_buf s (RB_window (ds_strstart s + ds_lookahead s)) (fw_more s)) as [s2 n].
        cbn [fst snd] in *.
        assert (HW3 : fw_wf ws hs (set_lookahead s2 (ds_lookahead s2 + n))) by (destruct HW2; constructor; dsred; try assumption; lia).
        assert (X3 : FWX (set_lookahead s2 (ds_lookahead s2 + n))) by (apply (FWX_same s2); [exact X2 | ..]; dsred; try reflexivity; lia).
        destruct (fw_insert_wf ws hs _ HW3) as (HW4 & HC4 & HL4 & HS4 & _).
        split; [exact (FWX_fw_insert _ HW3 X3)|].
        rewrite HS4, HL4. dsred. rewrite HS2, HL2. split; [intros Hl4; lia | lia].
  Qed.

  Lemma FWX_loop : forall n s, fw_wf ws hs s -> FWX s -> ds_lookahead s < MIN_LOOKAHEAD ->
    let s' := fill_window_loop (S n) s ws in
    FWX s' /\ (ds_lookahead s' < MIN_LOOKAHEAD -> ds_strstart s' + ds_lookahead s' <= 2 * ws - 2) /\ ds_strstart s' <= 2 * ws - MIN_LOOKAHEAD - 1
    /\ (1 <= ds_strstart s -> 1 <= ds_strstart s') /\ ds_lookahead s <= ds_lookahead s'.
  Proof.
    induction n as [|n IH]; intros s HW X Hl s'; subst s'.
    - rewrite fill_window_loop_step. pose proof (FWX_body s HW X Hl) as B.
      destruct (fill_window_body s ws) as [s1 brk]. destruct brk; [exact B|].
      destruct (_ && _); cbn [fill_window_loop]; exact B.
    - rewrite fill_window_loop_step. pose proof (FWX_body s HW X Hl) as B. pose proof (fill_window_body_wf ws hs s HW Hl) as C.
      destruct (fill_window_body s ws) as [s1 brk]. destruct B as [X1 SL1]. destruct C as (HW1 & _ & _).
      destruct brk; [exact (conj X1 SL1)|].
      destruct (Z.ltb_spec (ds_lookahead s1) MIN_LOOKAHEAD) as [Lo|Hi]; cbn [andb].
      + destruct (negb (cs_avail_in (ds_strm s1) =? 0)); [| exact (conj X1 SL1)].
        pose proof (IH s1 HW1 X1 Lo) as R. cbv zeta in R. destruct R as (R1 & R2 & R3 & R4 & R5). destruct SL1 as (_ & _ & S4 & S5).
        split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [intros H1; exact (R4 (S4 H1)) | lia].
      + exact (conj X1 SL1).
  Qed.

  Lemma fill_window_FWX : forall s, fw_wf ws hs s -> FWX s -> ds_lookahead s < MIN_LOOKAHEAD ->
    let s' := fill_window s in
    FWX s' /\ fwG s' = fwG s
    /\ (ds_lookahead s' < MIN_LOOKAHEAD -> ds_strstart s' + ds_lookahead s' <= 2 * ws - 2) /\ ds_strstart s' <= 2 * ws - MIN_LOOKAHEAD - 1
    /\ (1 <= ds_strstart s -> 1 <= ds_strstart s') /\ ds_lookahead s <= ds_lookahead s'.
  Proof.
    intros s HW X Hl s'. subst s'. pose proof (wf_ws _ _ _ HW) as Vws.
    unfold fill_window. rewrite Vws.
    destruct (FWX_loop 262 s HW X Hl) as [X1 SL1].
    destruct (fill_window_loop_wf ws hs 263 s HW Hl) as (HW1 & _ & _).
    change (fill_window_loop 263 s ws) with (fill_window_loop (S 262) s ws) in HW1 |- *.
    pose proof (fill_window_high_keep (fill_window_loop (S 262) s ws)) as (_ & L2 & S2 & _).
    split; [exact (FWX_high _ HW1 X1)|].
    split; [rewrite fwG_high, <- Vws; change (fill_window_loop (S 262) s (ds_w_size s)) with (fill_window_loop 263 s (ds_w_size s)); apply fwG_loop|].
    rewrite L2, S2. exact SL1.
  Qed.
End WF.
