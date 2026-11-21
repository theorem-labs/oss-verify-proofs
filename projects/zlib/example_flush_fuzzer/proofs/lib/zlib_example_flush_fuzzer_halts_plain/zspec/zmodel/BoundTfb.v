(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import RefSendTree3 RefSendTree4 RefFlushBlk9 RefFlushBlk11.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import FillWinModel TreeModel BuildTreeModel ScanModel SendModel CompressModel GenBitlenModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees HuffBuild HuffBuild2 HuffSpec HuffFlush HuffSend
  DeflRoom DeflateInvKeep OverlayFBS OverlayRace OverlayCmp OverlayHdr OverlayFlush OverlayDyn OverlayStat OverlayBT OverlayNeed OverlayTFB
  BoundArith.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma put_byte_acct : forall s b, ds_pending (put_byte s b) = ds_pending s + 1 /\ ds_bi_valid (put_byte s b) = ds_bi_valid s
  /\ ds_bi_buf (put_byte s b) = ds_bi_buf s.
Proof. intros s b. unfold put_byte. dsred. repeat split; reflexivity. Qed.

Lemma put_short_acct : forall s w, ds_pending (put_short s w) = ds_pending s + 2 /\ ds_bi_valid (put_short s w) = ds_bi_valid s
  /\ ds_bi_buf (put_short s w) = ds_bi_buf s.
Proof.
  intros s w. unfold put_short.
  destruct (put_byte_acct s (Z.land w 255)) as (A & B & C).
  destruct (put_byte_acct (put_byte s (Z.land w 255)) (Z.shiftr (wrap16 w) 8)) as (A' & B' & C').
  rewrite A', B', C', A, B, C. repeat split; lia.
Qed.

Lemma send_bits_acct : forall s v l, 0 <= l <= 16 -> 0 <= ds_bi_valid s <= 16 ->
  8 * ds_pending (send_bits s v l) + ds_bi_valid (send_bits s v l) = 8 * ds_pending s + ds_bi_valid s + l
  /\ 0 <= ds_bi_valid (send_bits s v l) <= 16.
Proof.
  intros s v l Hl Hb. pose proof (send_bits_size s v l) as SZ. unfold vsize in SZ. split; [lia|].
  unfold send_bits, Buf_size. destruct (Z.ltb_spec (16 - l) (ds_bi_valid s)); dsred; [|lia].
  match goal with |- context [ds_bi_valid (put_short ?x ?w)] => destruct (put_short_acct x w) as (_ & -> & _) end. dsred. lia.
Qed.

Lemma bi_windup_acct : forall s, 0 <= ds_bi_valid s <= 16 ->
  ds_pending (bi_windup s) = ds_pending s + cdiv8 (ds_bi_valid s) /\ ds_bi_valid (bi_windup s) = 0.
Proof.
  intros s Hb. unfold bi_windup.
  destruct (Z.ltb_spec 8 (ds_bi_valid s)).
  - destruct (put_short_acct s (ds_bi_buf s)) as (A & B & C). dsred. rewrite A.
    split; [|reflexivity]. unfold cdiv8.
    assert (E2 : (ds_bi_valid s + 7) / 8 = 2) by (symmetry; apply Z.div_unique with (r := ds_bi_valid s + 7 - 16); lia). lia.
  - destruct (Z.ltb_spec 0 (ds_bi_valid s)).
    + destruct (put_byte_acct s (ds_bi_buf s)) as (A & B & C). dsred. rewrite A.
      split; [|reflexivity]. unfold cdiv8.
      assert (E1 : (ds_bi_valid s + 7) / 8 = 1) by (symmetry; apply Z.div_unique with (r := ds_bi_valid s + 7 - 8); lia). lia.
    + dsred. split; [|reflexivity]. unfold cdiv8. replace (ds_bi_valid s) with 0 by lia. change ((0 + 7) / 8) with 0. lia.
Qed.

Lemma bi_windup_cdiv8 : forall s, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_pending s ->
  cdiv8 (vsize (bi_windup s)) = cdiv8 (vsize s).
Proof.
  intros s Hb Hp. destruct (bi_windup_acct s Hb) as [A B]. unfold vsize. rewrite A, B, Z.add_0_r.
  rewrite cdiv8_mul. replace (8 * (ds_pending s + cdiv8 (ds_bi_valid s))) with (8 * (ds_pending s + cdiv8 (ds_bi_valid s)) + 0) by lia.
  rewrite cdiv8_mul, cdiv8_0. lia.
Qed.

Lemma tr_stored_block_acct : forall s buf len last, 0 <= ds_bi_valid s <= 16 -> (last = 0 \/ last = 1) ->
  ds_pending (tr_stored_block s buf len last) = ds_pending s + cdiv8 (ds_bi_valid s + 3) + 4 + len
  /\ ds_bi_valid (tr_stored_block s buf len last) = 0.
Proof.
  intros s buf len last Hb Hl. unfold tr_stored_block.
  set (s1 := send_bits s (Z.shiftl STORED_BLOCK 1 + last) 3).
  destruct (send_bits_acct s (Z.shiftl STORED_BLOCK 1 + last) 3 ltac:(lia) Hb) as [S1 S1b]. fold s1 in S1, S1b.
  destruct (bi_windup_acct s1 S1b) as [W1 W2]. set (s2 := bi_windup s1) in *.
  destruct (put_short_acct s2 (wrap16 len)) as (P1 & P1b & _). set (s3 := put_short s2 (wrap16 len)) in *.
  destruct (put_short_acct s3 (wrap16 (Z.lnot len))) as (P2 & P2b & _). set (s4 := put_short s3 (wrap16 (Z.lnot len))) in *.
  assert (K : forall x a, ds_pending (set_pending x a) = a /\ ds_bi_valid (set_pending x a) = ds_bi_valid x) by (intros; dsred; split; reflexivity).
  assert (KB : forall x a, ds_pending (set_pending_buf x a) = ds_pending x /\ ds_bi_valid (set_pending_buf x a) = ds_bi_valid x) by (intros; dsred; split; reflexivity).
  assert (MID : forall x, ds_pending x = ds_pending s4 -> ds_bi_valid x = ds_bi_valid s4 ->
            ds_pending (set_pending x (ds_pending x + len)) = ds_pending s + cdiv8 (ds_bi_valid s + 3) + 4 + len
            /\ ds_bi_valid (set_pending x (ds_pending x + len)) = 0).
  { intros x Ex Ebx. destruct (K x (ds_pending x + len)) as [K1 K2]. rewrite K1, K2, Ex, Ebx, P2, P2b, P1, P1b, W2, W1.
    split; [|reflexivity].
    enough (E : ds_pending s1 + cdiv8 (ds_bi_valid s1) = ds_pending s + cdiv8 (ds_bi_valid s + 3)) by lia.
    replace (ds_bi_valid s + 3) with (8 * (ds_pending s1 - ds_pending s) + ds_bi_valid s1) by lia.
    rewrite cdiv8_mul. lia. }
  destruct (negb (len =? 0)); [destruct buf as [off|]|]; [destruct (KB s4 (arr_blit (ds_pending_buf s4) (ds_pending s4) (ds_window s4) off len)) as [B1 B2]; apply MID; assumption | apply MID; reflexivity | apply MID; reflexivity].
Qed.


Ltac name_let x E rhs := intro x; generalize (@eq_refl _ x : x = rhs); clearbody x; revert x; intros x E.

Section TFB.
  Variable syms : list (Z * Z).
  Variables (s : deflate_state) (buf : option Z) (len last : Z).
  Hypothesis FB : FBS syms s buf len last.
  Hypothesis HL : 512 <= ds_lit_bufsize s.
  Hypothesis COMPRESSIBLE : buf = None -> Sstat syms <= 8 * len + 7.

  Theorem tfb_cb :
    cdiv8 (vsize (tr_flush_block s buf len last)) <= cdiv8 (ds_bi_valid s) + len + 5.
  Proof.
    pose proof (dyn_need_ge512 syms s buf len last FB ltac:(unfold LS; exact HL)) as NEED.
    pose proof (fbs_level _ _ _ _ _ FB) as LV.
    pose proof (L_range syms s buf len last FB) as [LR NR]. pose proof (PBL4 syms s buf len last FB) as P4.
    pose proof (fbs_cty _ _ _ _ _ FB) as CT. pose proof (fbs_lens _ _ _ _ _ FB) as TLS.
    pose proof (fbs_strategy _ _ _ _ _ FB) as STR. pose proof (fbs_len _ _ _ _ _ FB) as LEN0.
    pose proof (fbs_bi_valid _ _ _ _ _ FB) as BV0. pose proof (fbs_last _ _ _ _ _ FB) as LAST.
    rewrite (tfb_eq_raw s buf len last ltac:(lia)).
    enough (H :
      let s1 := if cs_data_type (ds_strm s) =? Z_UNKNOWN then set_strm s (cset_data_type (ds_strm s) (detect_data_type s)) else s in
      let X1 := build_tree s1 TL in
      let X2 := build_tree X1 TD in
      let X3 := scan_tree X2 TL (ds_l_max_code X2) in
      let X4 := scan_tree X3 TD (ds_d_max_code X3) in
      let X5 := build_tree X4 TB in
      let mb := build_bl_tree_loop 17 X5 (BL_CODES - 1) in
      let X6 := set_opt_len X5 (wrap64 (ds_opt_len X5 + 3 * (mb + 1) + 5 + 5 + 4)) in
      let opt_lenb := Z.shiftr (wrap64 (ds_opt_len X6 + 3 + 7)) 3 in
      let static_lenb := Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3 in
      let opt_lenb0 := if (static_lenb <=? opt_lenb) || (ds_strategy X6 =? Z_FIXED) then static_lenb else opt_lenb in
      let X7 := if (wrap64 (len + 4) <=? opt_lenb0) && match buf with Some _ => true | None => false end
                then tr_stored_block X6 buf len last
                else if static_lenb =? opt_lenb0
                then (let s0 := send_bits X6 (Z.shiftl STATIC_TREES 1 + last) 3 in
                      compress_block s0 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl)
                else (let s0 := send_bits X6 (Z.shiftl DYN_TREES 1 + last) 3 in
                      let s1 := send_all_trees s0 (ds_l_max_code s0 + 1) (ds_d_max_code s0 + 1) (mb + 1) in
                      compress_block s1 (ds_dyn_ltree_fc s1) (ds_dyn_ltree_dl s1) (ds_dyn_dtree_fc s1) (ds_dyn_dtree_dl s1)) in
      let X8 := init_block X7 in
      let X9 := if negb (last =? 0) then bi_windup X8 else X8 in
      cdiv8 (vsize X9) <= cdiv8 (ds_bi_valid s) + len + 5) by exact H.
    name_let s0 Es0 (fs0 s). subst s0.
    name_let X1 E1 (build_tree (fs0 s) TL).
    name_let X2 E2 (build_tree X1 TD).
    name_let X3 E3 (scan_tree X2 TL (ds_l_max_code X2)).
    name_let X4 E4 (scan_tree X3 TD (ds_d_max_code X3)).
    name_let X5 E5 (build_tree X4 TB).
    name_let mb Emb (fmb X5). subst mb.
    name_let X6 E6 (set_opt_len X5 (wrap64 (ds_opt_len X5 + 3 * (fmb X5 + 1) + 5 + 5 + 4))).
    name_let opt_lenb Eol (Z.shiftr (wrap64 (ds_opt_len X6 + 3 + 7)) 3).
    name_let static_lenb Esl (Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3).
    name_let opt_lenb0 Eol0 (if (static_lenb <=? opt_lenb) || (ds_strategy X6 =? Z_FIXED) then static_lenb else opt_lenb).
    name_let X7 E7 (if (wrap64 (len + 4) <=? opt_lenb0) && match buf with Some _ => true | None => false end then tr_stored_block X6 buf len last
                    else if static_lenb =? opt_lenb0 then (let s1 := send_bits X6 (Z.shiftl STATIC_TREES 1 + last) 3 in
                                      compress_block s1 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl)
                    else (let s1 := send_bits X6 (Z.shiftl DYN_TREES 1 + last) 3 in
                          let s2 := send_all_trees s1 (ds_l_max_code s1 + 1) (ds_d_max_code s1 + 1) (fmb X5 + 1) in
                          compress_block s2 (ds_dyn_ltree_fc s2) (ds_dyn_ltree_dl s2) (ds_dyn_dtree_fc s2) (ds_dyn_dtree_dl s2))).
    cbv zeta.
    destruct (flush_facts syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6) as (LL & LzL & LD & LzD & LB & LzB & b4 &
      [B1 B2 FC1D B5 FC4B Lb4 NN4 BS316 LENS ZL GL LEND ZD GD LENB ZB MCL MCD RL RD SU S256 EY3 EY4 LQ2 LQ3 BL2 BL4 B0 TL2 TL3 TL5
       SLv TBnn OLlo OLhi K6 PB6 PD6 BV6 BB6 DL6L DL6D DL6B FC6L FC6D TL4 P1 P2 P5 MCL2 MCD3]).
    pose proof (Sstat_bound syms s buf len last FB) as SB.
    destruct (dyn_cost_sum syms s buf len last FB LzL LzD ltac:(intros j Hj; apply (proj2 (LENS j Hj))) ltac:(intros j Hj; apply (proj2 (LEND j Hj)))) as (_ & DCS2 & L256).
    pose proof (fmb_range X5) as MBR.
    assert (SLB : static_lenb = cdiv8 (Sstat syms + 3)).
    { rewrite Esl, SLv. rewrite wrap64_id by lia. apply lenb_cdiv8. lia. }
    assert (OLB : opt_lenb = cdiv8 (ds_opt_len X6 + 3)).
    { rewrite Eol. rewrite wrap64_id by lia. apply lenb_cdiv8. lia. }
    assert (OLB0 : opt_lenb0 <= static_lenb /\ (opt_lenb0 = static_lenb \/ (opt_lenb0 = opt_lenb /\ ds_opt_len X6 < ds_static_len X6))).
    { rewrite Eol0. destruct (Z.leb_spec static_lenb opt_lenb); cbn [orb]; [lia|].
      destruct (ds_strategy X6 =? Z_FIXED); [lia|]. split; [lia|]. right. split; [reflexivity|].
      rewrite SLv. rewrite OLB, SLB in *. pose proof (cdiv8_mono (Sstat syms + 3) (ds_opt_len X6 + 3)). lia. }
    rewrite wrap64_id in E7 by lia.
    assert (TAIL : forall X, 0 <= ds_bi_valid X <= 16 -> 0 <= ds_pending X ->
              cdiv8 (vsize (if negb (last =? 0) then bi_windup (init_block X) else init_block X)) = cdiv8 (vsize X)).
    { intros X BX PX. destruct (init_block_bits X) as (I1 & I2 & _).
      assert (V8 : vsize (init_block X) = vsize X) by (unfold vsize; rewrite I1, I2; reflexivity).
      destruct (negb (last =? 0)); [| rewrite V8; reflexivity ].
      rewrite bi_windup_cdiv8 by (rewrite ?I1, ?I2; lia). rewrite V8; reflexivity. }
    assert (V6 : vsize X6 = ds_bi_valid s) by (unfold vsize; rewrite PD6, BV6; lia).
    assert (FIN : forall X, X7 = X -> 0 <= ds_bi_valid X <= 16 -> 0 <= ds_pending X ->
              cdiv8 (vsize X) <= cdiv8 (ds_bi_valid s) + len + 5 ->
              cdiv8 (vsize (if negb (last =? 0) then bi_windup (init_block X7) else init_block X7)) <= cdiv8 (ds_bi_valid s) + len + 5).
    { intros X -> BX PX GX. rewrite (TAIL X BX PX). exact GX. }
    destruct ((len + 4 <=? opt_lenb0) && match buf with Some _ => true | None => false end) eqn:Esto.
    {
      destruct (tr_stored_block_acct X6 buf len last ltac:(rewrite BV6; lia) LAST) as [SP SB0].
      pose proof (cdiv8_le (ds_bi_valid s + 3) ltac:(lia)) as C3. pose proof (cdiv8_3 (ds_bi_valid s) ltac:(lia)) as C3'.
      apply (FIN _ E7); [rewrite SB0; lia | rewrite SP, PD6, BV6; lia |].
      unfold vsize. rewrite SP, SB0, PD6, BV6, Z.add_0_r.
      replace (8 * (0 + cdiv8 (ds_bi_valid s + 3) + 4 + len)) with (8 * (cdiv8 (ds_bi_valid s + 3) + 4 + len) + 0) by lia.
      rewrite cdiv8_mul, cdiv8_0. lia. }
    assert (OL4 : opt_lenb0 <= len + 4).
    { apply Bool.andb_false_iff in Esto. destruct Esto as [Ele | Ebuf].
      - apply Z.leb_gt in Ele. lia.
      - destruct buf as [off|]; [discriminate Ebuf|]. specialize (COMPRESSIBLE eq_refl).
        rewrite SLB in OLB0. pose proof (cdiv8_mono (Sstat syms + 3) (8 * (len + 1) + 2) ltac:(lia)) as M1.
        rewrite cdiv8_mul in M1. change (cdiv8 2) with 1 in M1. lia. }
    destruct (static_lenb =? opt_lenb0) eqn:Esta.
    {
      pose proof (stat_branch syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6 _ _ eq_refl eq_refl) as SBr.
      destruct SBr as (BINV6 & R6 & CBOK & SN7 & LB7 & BE & VE & CE & ALE).
      apply Z.eqb_eq in Esta. unfold BINV in BE.
      apply (FIN _ E7); cbv zeta; [lia | lia |]. rewrite VE.
      replace (ds_bi_valid s + 3 + Sstat syms) with (ds_bi_valid s + (Sstat syms + 3)) by lia.
      pose proof (cdiv8_add_le (ds_bi_valid s) (Sstat syms + 3) ltac:(lia)). rewrite <- SLB in *. lia. }
    assert (DYN : ds_opt_len X6 < ds_static_len X6).
    { destruct OLB0 as [_ [E|[_ D]]]; [exfalso; rewrite E, Z.eqb_refl in Esta; discriminate| exact D]. }
    pose proof (NEED X1 X2 X3 X4 X5 X6 _ _ E1 E2 E3 E4 E5 E6 eq_refl eq_refl DYN) as RACE.
    pose proof (dyn_branch syms s buf len last FB X1 X2 X3 X4 X5 X6 E1 E2 E3 E4 E5 E6 _ _ _ eq_refl eq_refl eq_refl ltac:(lia) RACE) as DB.
    destruct DB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BE & VE & CE & ALE & VO).
    unfold BINV in BE.
    assert (OD : opt_lenb0 = opt_lenb) by (destruct OLB0 as [_ [E|[E _]]]; [exfalso; rewrite E, Z.eqb_refl in Esta; discriminate| exact E]).
    apply (FIN _ E7); cbv zeta; [lia | lia |].
    pose proof (cdiv8_mono _ _ VO) as M1.
    replace (ds_bi_valid s + 3 + ds_opt_len X6) with (ds_bi_valid s + (ds_opt_len X6 + 3)) in M1 by lia.
    pose proof (cdiv8_add_le (ds_bi_valid s) (ds_opt_len X6 + 3) ltac:(lia)). rewrite <- OLB in *. lia.
  Qed.
End TFB.
