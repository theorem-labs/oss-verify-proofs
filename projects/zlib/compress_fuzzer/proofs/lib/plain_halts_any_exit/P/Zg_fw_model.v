(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_fw_model Z_fw_slide.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ins_clamp (s : deflate_state) : Z :=
  if ds_strstart s - 32768 <? ds_insert s then ds_strstart s - 32768 else ds_insert s.

Lemma fw_slide_eqg : forall s more, 32768 <= ds_strstart s -> ds_w_size s = 32768 -> ds_hash_size s = 32768 ->
  0 <= more <= 32768 ->
  fw_slide s 32768 more
  = set_prev (set_head (set_insert (fw_slide4 s more) (ins_clamp s)) (slide_hash_loop (Z.to_nat 32768) (ds_head s) 32768 32768))
             (slide_hash_loop (Z.to_nat 32768) (ds_prev s) 32768 32768).
Proof.
  intros s more SS WS HS HM. unfold fw_slide, fw_slide4, ins_clamp. cbv zeta. dsred.
  destruct (ds_strstart s - 32768 <? ds_insert s); unfold slide_hash; dsred; rewrite WS, HS, (wrap32_id (32768 - more)) by lia; [reflexivity|].
  destruct s; reflexivity.
Qed.

Section ONE.
  Variable d : deflate_state.
  Hypothesis FW : fw_wf 32768 32768 d.

  Lemma fw_more_eqg : fw_more d = fw_more0 d /\ 0 <= fw_more0 d <= 65536.
  Proof.
    pose proof (wf_wsz _ _ _ FW) as W2. pose proof (wf_sl _ _ _ FW) as SL. pose proof (wf_look _ _ _ FW) as LK. pose proof (wf_ins _ _ _ FW) as IN.
    unfold fw_more, fw_more0. rewrite W2 in *. split; [apply wrap32_id; lia| lia].
  Qed.

  Lemma fwA_factsg : fw_wf 32768 32768 (fwA d) /\ ds_wrap (fwA d) = ds_wrap d /\ ds_strm (fwA d) = ds_strm d
    /\ ds_high_water (fwA d) = ds_high_water d
    /\ moreA d = ds_window_size (fwA d) - ds_lookahead (fwA d) - ds_strstart (fwA d) /\ 0 <= moreA d < 2 ^ 32
    /\ (moreA d = 0 -> 262 < ds_lookahead (fwA d))
    /\ (cs_avail_in (ds_strm (fwA d)) <> 0 -> 262 <= ds_lookahead (fwA d) + moreA d).
  Proof.
    destruct fw_more_eqg as [EM RM].
    pose proof (wf_wsz _ _ _ FW) as W2. pose proof (wf_sl _ _ _ FW) as SL. pose proof (wf_look _ _ _ FW) as LK. pose proof (wf_ins _ _ _ FW) as IN.
    unfold fwA, moreA, slide_cond. destruct (Z.leb_spec 65274 (ds_strstart d)) as [C|C].
    - destruct (fw_slide_wf 32768 32768 d (fw_more d) FW ltac:(lia) ltac:(rewrite EM; unfold fw_more0; lia)) as (W' & (C1 & C2 & C3 & C4) & EL & ES).
      pose proof (wf_wsz _ _ _ W') as W2'.
      assert (EZ : ds_strm (fw_slide d 32768 (fw_more d)) = ds_strm d /\ ds_high_water (fw_slide d 32768 (fw_more d)) = ds_high_water d).
      { unfold fw_slide. cbv zeta. unfold slide_hash. destruct (_ <? _); dsred; split; reflexivity. }
      destruct EZ as [EZ EH].
      split; [exact W'|]. split; [exact C2|]. split; [exact EZ|]. split; [exact EH|].
      rewrite W2', EL, ES. unfold fw_more0 in *. rewrite W2 in *. split; [lia|]. split; [lia|]. split; intros; lia.
    - split; [exact FW|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      unfold fw_more0 in *. rewrite W2 in *. split; [lia|]. split; [lia|]. split; intros; lia.
  Qed.

  Theorem fill_window_eqg : fill_window d = fill_window_high (fwB (fwA d) (moreA d)).
  Proof.
    destruct fw_more_eqg as [EM RM]. destruct fwA_factsg as (W' & _ & EZ & _ & EMA & RMA & ZLA & FULL).
    pose proof (wf_ws _ _ _ FW) as W1. pose proof (wf_ai _ _ _ W') as RA. pose proof (wf_sl _ _ _ W') as SL'. pose proof (wf_wsz _ _ _ W') as W2'.
    unfold fill_window. rewrite W1. change 263%nat with (S 262). rewrite fill_window_loop_step, fill_window_body_eq.
    rewrite W1. change (32768 + (32768 - MIN_LOOKAHEAD)) with 65274.
    assert (E1 : (if 65274 <=? ds_strstart d then (fw_slide d 32768 (fw_more d), wrap32 (fw_more d + 32768)) else (d, fw_more d)) = (fwA d, moreA d)).
    { unfold fwA, moreA, slide_cond. destruct (65274 <=? ds_strstart d); rewrite EM; [| reflexivity].
      f_equal. apply wrap32_id. pose proof (wf_sl _ _ _ FW). pose proof (wf_wsz _ _ _ FW). unfold fw_more0 in *. lia. }
    rewrite E1. unfold fwB. f_equal.
    destruct (Z.eqb_spec (cs_avail_in (ds_strm (fwA d))) 0) as [A0|A1]; [reflexivity|].
    pose proof (proj1 (read_buf_wf 32768 32768 (fwA d) (ds_strstart (fwA d) + ds_lookahead (fwA d)) (moreA d) W' eq_refl ltac:(lia) ltac:(lia))) as W2.
    cbv zeta in W2.
    destruct (read_buf_small (fwA d) (ds_strstart (fwA d) + ds_lookahead (fwA d)) (moreA d)) as (R1 & R2 & R3 & R4 & R5 & _).
    revert W2 R1 R2 R3 R4 R5.
    generalize (read_buf (fwA d) (RB_window (ds_strstart (fwA d) + ds_lookahead (fwA d))) (moreA d)). intros [s2 n]. cbn [fst snd]. intros.
    destruct (fw_insert_wf 32768 32768 (set_lookahead s2 (ds_lookahead s2 + n)) ltac:(unfold rb_len in R1; destruct W2; constructor; dsred; try assumption; destruct (Z.ltb_spec (moreA d) (cs_avail_in (ds_strm (fwA d)))); lia)) as (_ & _ & EL3 & _ & EA3).
    rewrite EL3, EA3. dsred. rewrite R3, R2.
    destruct (Z.eq_dec (cs_avail_in (ds_strm (fwA d)) - rb_len (fwA d) (moreA d)) 0) as [Z0|Z1].
    - rewrite Z0. cbn [Z.eqb negb]. rewrite andb_false_r. reflexivity.
    -
      assert (En : n = moreA d) by (unfold rb_len in R1, Z1; destruct (Z.ltb_spec (moreA d) (cs_avail_in (ds_strm (fwA d)))); lia).
      specialize (FULL A1).
      replace (ds_lookahead (fwA d) + n <? MIN_LOOKAHEAD) with false by (symmetry; apply Z.ltb_ge; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; lia).
      reflexivity.
  Qed.
End ONE.

Definition rbn_strm (s : deflate_state) (l : list Z) (n : Z) : cstrm :=
  let st := ds_strm s in
  let st1 := cset_avail_in st (cs_avail_in st - n) in
  let st2 := if ds_wrap s =? 1 then cset_adler st1 (adler32_upd (cs_adler st) l) else st1 in
  cset_total_in (cset_next_in st2 (cs_next_in st + n)) (wrap64 (cs_total_in st + n)).

Lemma read_buf_eqn : forall s off more n, n = rb_len s more -> 0 < n -> ds_wrap s <> 2 ->
  read_buf s (RB_window off) more
  = (set_strm (set_window s (arr_upd (ds_window s) off (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n)))
              (rbn_strm s (arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n) n), n).
Proof.
  intros s off more n En Pn W2. unfold read_buf, rbn_strm. unfold rb_len in En. cbv zeta. rewrite <- En.
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  dsred. destruct (Z.eqb_spec (ds_wrap s) 1) as [E1|E1]; [reflexivity|].
  replace (ds_wrap s =? 2) with false by (symmetry; apply Z.eqb_neq; exact W2). reflexivity.
Qed.

Lemma rb_len_range : forall s more, 0 <= cs_avail_in (ds_strm s) -> 0 <= more ->
  0 <= rb_len s more <= more /\ rb_len s more <= cs_avail_in (ds_strm s) /\ (rb_len s more = 0 <-> (more = 0 \/ cs_avail_in (ds_strm s) = 0)).
Proof. intros s more Ha Hm. unfold rb_len. destruct (Z.ltb_spec more (cs_avail_in (ds_strm s))); lia. Qed.

Lemma fwB_pos : forall s1 more, cs_avail_in (ds_strm s1) <> 0 ->
  fwB s1 more = fw_insert (set_lookahead (fst (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more))
                                        (ds_lookahead (fst (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more))
                                         + snd (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more))).
Proof. intros s1 more A. unfold fwB. replace (cs_avail_in (ds_strm s1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact A). reflexivity. Qed.

Lemma fwB_g0 : forall s1 more, cs_avail_in (ds_strm s1) <> 0 -> rb_len s1 more = 0 ->
  fwB s1 more = fw_insert (set_lookahead s1 (ds_lookahead s1 + 0)).
Proof.
  intros s1 more A Z0. rewrite (fwB_pos s1 more A). unfold read_buf. cbv zeta. unfold rb_len in Z0. rewrite Z0. cbn [Z.eqb fst snd]. reflexivity.
Qed.

Lemma fwB_gn : forall s1 more n, cs_avail_in (ds_strm s1) <> 0 -> n = rb_len s1 more -> 0 < n -> ds_wrap s1 <> 2 ->
  fwB s1 more
  = fw_insert (set_lookahead
      (set_strm (set_window s1 (arr_upd (ds_window s1) (ds_strstart s1 + ds_lookahead s1) (arr_slice (cs_input (ds_strm s1)) (cs_next_in (ds_strm s1)) n)))
                (rbn_strm s1 (arr_slice (cs_input (ds_strm s1)) (cs_next_in (ds_strm s1)) n) n))
      (ds_lookahead s1 + n)).
Proof.
  intros s1 more n A En Pn W2. rewrite (fwB_pos s1 more A). rewrite (read_buf_eqn s1 _ more n En Pn W2). cbn [fst snd]. dsred. reflexivity.
Qed.

Definition rbn_adler (s : deflate_state) (l : list Z) : Z :=
  if ds_wrap s =? 1 then adler32_upd (cs_adler (ds_strm s)) l else cs_adler (ds_strm s).

Lemma rbn_cells : forall L s l n p1 p2 p3 resv,
  zs_call_cells L (rbn_strm s l n) p1 p2 p3 resv =
  [C8 (Z_to_bv 64 (dl_NI L + (cs_next_in (ds_strm s) + n))); C4 (Z_to_bv 64 (cs_avail_in (ds_strm s) - n)); CB 4 p1;
   C8 (Z_to_bv 64 (wrap64 (cs_total_in (ds_strm s) + n)));
   C8 (Z_to_bv 64 (dl_NO L + Z.of_nat (length (cs_out_rev (ds_strm s))))); C4 (Z_to_bv 64 (cs_avail_out (ds_strm s))); CB 4 p2;
   C8 (Z_to_bv 64 (cs_total_out (ds_strm s)));
   C8 (Z_to_bv 64 (msg_ptr (cs_msg (ds_strm s)))); C8 (Z_to_bv 64 (dl_As L)); C8 (Z_to_bv 64 Z_ZCALLOC); C8 (Z_to_bv 64 Z_ZCFREE); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 (cs_data_type (ds_strm s))); CB 4 p3; C8 (Z_to_bv 64 (rbn_adler s l)); C8 resv].
Proof.
  intros. unfold zs_call_cells, zs_priv_cells, rbn_strm, rbn_adler. destruct (ds_wrap s =? 1); reflexivity.
Qed.

Lemma rbn_avail_in : forall s l n, cs_avail_in (rbn_strm s l n) = cs_avail_in (ds_strm s) - n.
Proof. intros. unfold rbn_strm. destruct (ds_wrap s =? 1); reflexivity. Qed.

