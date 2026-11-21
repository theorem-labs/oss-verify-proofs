(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffBuild HuffBuild2 HuffFib HuffSpec HuffFlush HuffSend DeflRoom OverlayFBS OverlayRace OverlayCmp OverlayHdr OverlayFlush OverlayDyn DeflateInvKeep.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import FillWinModel TreeModel BuildTreeModel ScanModel SendModel CompressModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma cost_of_static : forall x, sym_valid x ->
  cost_of static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl x = scost x
  /\ lens_ok (calls_of static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl x)
  /\ (fst x = 0 -> 0 <= arr_get static_ltree_dl (snd x) <= 15)
  /\ (fst x <> 0 -> 0 <= arr_get static_ltree_dl (arr_get length_code_a (snd x) + LITERALS + 1) <= 15
                   /\ 0 <= arr_get static_dtree_dl (d_code (fst x - 1)) <= 15).
Proof.
  intros [d lc] V. pose proof V as V0. unfold sym_valid in V. cbn [fst snd].
  destruct (Z.eqb_spec d 0) as [->|Hd].
  - rewrite cost_of_lit. unfold calls_of, scost. rewrite Z.eqb_refl.
    pose proof (static_ltree_len lc ltac:(lia)) as SL.
    assert (R : 8 <= arr_get static_ltree_dl lc <= 9) by (rewrite SL; destruct (lc <? 144); [lia|]; destruct (Z.ltb_spec lc 256); lia).
    split; [reflexivity|]. split; [constructor; [cbn [snd]; lia| constructor]|]. split; [intros _; lia| intros X; exfalso; apply X; reflexivity].
  - rewrite cost_of_match by exact Hd. unfold calls_of, scost. replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hd). cbv zeta.
    pose proof (length_code_range lc ltac:(lia)) as CR.
    pose proof (extra_lbits_range _ CR) as XL.
    pose proof (d_code_range (d - 1) ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in V; lia)) as DR.
    pose proof (extra_dbits_range _ DR) as XD.
    pose proof (static_ltree_len (arr_get length_code_a lc + LITERALS + 1) ltac:(unfold LITERALS; lia)) as SL.
    assert (R : 7 <= arr_get static_ltree_dl (arr_get length_code_a lc + LITERALS + 1) <= 8).
    { rewrite SL. unfold LITERALS. destruct (Z.ltb_spec (arr_get length_code_a lc + 256 + 1) 144); [lia|].
      destruct (Z.ltb_spec (arr_get length_code_a lc + 256 + 1) 256); [lia|]. destruct (_ <? 280); lia. }
    rewrite (static_dtree_len (d_code (d - 1))) by lia.
    split; [lia|].
    split.
    + apply lens_ok_app; [constructor; [cbn [snd]; lia| constructor]|].
      apply lens_ok_app; [destruct (negb (arr_get extra_lbits_a (arr_get length_code_a lc) =? 0)); [constructor; [cbn [snd]; lia| constructor]| constructor]|].
      apply lens_ok_app; [constructor; [cbn [snd]; lia| constructor]|].
      destruct (negb (arr_get extra_dbits_a (d_code (d - 1)) =? 0)); [constructor; [cbn [snd]; lia| constructor]| constructor].
    + split; [intros X; exfalso; exact (Hd X)|]. intros _. lia.
Qed.

Lemma static_ltree_256 : arr_get static_ltree_dl END_BLOCK = 7.
Proof. vm_compute. reflexivity. Qed.

Lemma excess_scost : forall l, Forall sym_valid l -> excess scost l <= 7 * Z.of_nat (length l) /\ 0 <= csum scost l <= 31 * Z.of_nat (length l).
Proof.
  induction l as [|x l IH]; intros V; [cbn; lia|].
  inversion V; subst. specialize (IH ltac:(assumption)). pose proof (scost_bound x ltac:(assumption)).
  unfold excess in *. cbn [csum length]. rewrite Nat2Z.inj_succ. lia.
Qed.


Section FB3.
  Local Set Warnings "-notation-for-abbreviation".
  Variable syms : list (Z * Z).
  Variable s : deflate_state.
  Variable buf : option Z.
  Variables len last : Z.
  Hypothesis FB : FBS syms s buf len last.

  Local Notation nS := (nS syms).
  Local Notation LS := (LS s).
  Local Notation fs0 := (fs0 s).
  Local Notation PBL := (PBL s).
  Variables fY1 fY2 fY3 fY4 fY5 fY6 : deflate_state.
  Local Notation fmb := (fmb fY5).
  Hypothesis EfY1 : fY1 = build_tree fs0 TL.
  Hypothesis EfY2 : fY2 = build_tree fY1 TD.
  Hypothesis EfY3 : fY3 = scan_tree fY2 TL (ds_l_max_code fY2).
  Hypothesis EfY4 : fY4 = scan_tree fY3 TD (ds_d_max_code fY3).
  Hypothesis EfY5 : fY5 = build_tree fY4 TB.
  Hypothesis EfY6 : fY6 = set_opt_len fY5 (wrap64 (ds_opt_len fY5 + 3 * (fmb + 1) + 5 + 5 + 4)).

  Variables fS7 fSe : deflate_state.
  Hypothesis EfS7 : fS7 = send_bits fY6 (Z.shiftl STATIC_TREES 1 + last) 3.
  Hypothesis EfSe : fSe = compress_block fS7 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl.

  Local Ltac get_ff :=
    destruct (flush_facts syms s buf len last FB fY1 fY2 fY3 fY4 fY5 fY6 EfY1 EfY2 EfY3 EfY4 EfY5 EfY6) as (LL & LzL & LD & LzD & LB & LzB & b4 &
      [B1 B2 FC1D B5 FC4B Lb4 NN4 BS316 LENS ZL GL LEND ZD GD LENB ZB MCL MCD RL RD SU S256 EY3 EY4 LQ2 LQ3 BL2 BL4 B0 TL2 TL3 TL5
       SLv TBnn OLlo OLhi K6 PB6 PD6 BV6 BB6 DL6L DL6D DL6B FC6L FC6D TL4' P1' P2' P5' MCL2' MCD3']).

  Theorem stat_branch :
       BINV PBL fY6 /\ sb_room PBL fY6 3
    /\ compress_block_ok PBL fS7 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
    /\ ds_sym_next fS7 = 3 * nS /\ ds_lit_bufsize fS7 = LS
    /\ BINV PBL fSe /\ vsize fSe = ds_bi_valid s + 3 + Sstat syms /\ cty fSe
    /\ arr_len (ds_pending_buf fSe) = PBL.
  Proof.
    get_ff. pose proof (fY6_frames syms s buf len last FB fY1 fY2 fY3 fY4 fY5 fY6 EfY1 EfY2 EfY3 EfY4 EfY5 EfY6 _ eq_refl) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (L_range syms s buf len last FB) as [LR NR]. pose proof (PBL4 syms s buf len last FB) as P4.
    pose proof (fbs_cty _ _ _ _ _ FB) as CT.
    pose proof (fbs_bi_valid _ _ _ _ _ FB) as BV0.
    assert (V6 : vsize fY6 = ds_bi_valid s) by (unfold vsize; rewrite PD6, BV6; lia).
    assert (V7 : vsize fS7 = ds_bi_valid s + 3) by (rewrite EfS7; rewrite send_bits_size, V6; reflexivity).
    assert (BINV6 : BINV PBL fY6) by (unfold BINV; rewrite PD6; lia).
    assert (R6 : sb_room PBL fY6 3) by (unfold sb_room; rewrite PD6; lia).
    assert (BINV7 : BINV PBL fS7) by (rewrite EfS7; apply send_bits_BINV; [exact BINV6| lia| exact R6]).
    assert (CT0 : cty fs0).
    { unfold OverlayFlush.fs0. destruct (cs_data_type (ds_strm s) =? Z_UNKNOWN); [apply cty_set_strm_dt; exact CT| exact CT]. }
    assert (CT6 : cty fY6).
    { rewrite EfY6. apply cty_set_opt_len. rewrite EfY5. apply cty_build_tree. rewrite EfY4. apply cty_scan_tree.
      rewrite EfY3. apply cty_scan_tree. rewrite EfY2. apply cty_build_tree. rewrite EfY1. apply cty_build_tree. exact CT0. }
    assert (CT7 : cty fS7) by (rewrite EfS7; apply cty_send_bits; exact CT6).
    pose proof (send_bits_fp fY6 (Z.shiftl STATIC_TREES 1 + last) 3) as FP7. cbv zeta in FP7.
    destruct FP7 as (PD7 & AL7 & PR7 & LB7 & SN7).
    rewrite <- EfS7 in PD7, AL7, PR7, LB7, SN7.
    rewrite F1 in LB7. rewrite F2 in SN7. rewrite F3 in AL7. rewrite PD6 in PD7, PR7.
    pose proof (fbs_syms_valid _ _ _ _ _ FB) as VAL.
    assert (DR : Forall (fun dl : Z * Z => 0 <= fst dl < 65536) syms).
    { apply Forall_forall. intros [d lc] Hx. pose proof (proj1 (Forall_forall _ _) VAL _ Hx) as V. unfold sym_valid, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in V. cbn [fst]. lia. }
    assert (DM : Forall (fun dl : Z * Z => fst dl <= 32768) syms).
    { apply Forall_forall. intros [d lc] Hx. pose proof (proj1 (Forall_forall _ _) VAL _ Hx) as V. unfold sym_valid, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in V. cbn [fst]. lia. }
    set (CC := cost_of static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl).
    assert (CE : forall l, Forall sym_valid l -> csum CC l = csum scost l).
    { induction l as [|x l IH]; intros V; cbn [csum]; [reflexivity|]. inversion V; subst.
      unfold CC at 1. rewrite (proj1 (cost_of_static x ltac:(assumption))). rewrite IH by assumption. reflexivity. }
    pose proof (excess_scost syms VAL) as [EXS CSB].
    assert (EXE : excess CC syms = excess scost syms).
    { unfold excess. clear - VAL. induction syms as [|x l IH]; cbn [csum]; [reflexivity|]. inversion VAL; subst.
      unfold CC at 1. rewrite (proj1 (cost_of_static x ltac:(assumption))). rewrite IH by assumption. reflexivity. }
    assert (RACE : vsize fS7 + excess CC syms <= 8 * LS + 7).
    { rewrite EXE, V7. unfold OverlayFlush.nS in NR. lia. }
    assert (LENSX : forall dl, In dl syms -> lens_ok (calls_of static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl dl)).
    { intros dl Hdl. apply (proj1 (proj2 (cost_of_static dl (proj1 (Forall_forall _ _) VAL _ Hdl)))). }
    assert (RACEk : forall k, (k < length syms)%nat -> vsize fS7 + csum CC (firstn k syms) <= 8 * (ds_lit_bufsize fS7 + 3 * Z.of_nat k) + 7).
    { intros k Hk. rewrite LB7. apply (cb_race_suff (vsize fS7) LS CC syms RACE k Hk). }
    assert (BYTES : forall i d lc, nth_error syms i = Some (d, lc) -> sym_at fS7 (3 * Z.of_nat i) d lc).
    { intros i d lc Hi. pose proof (fbs_sym_bytes _ _ _ _ _ FB i d lc Hi) as (Y1 & Y2 & Y3). unfold fbs_L in Y1, Y2, Y3.
      assert (Hlen : (i < length syms)%nat) by (apply (proj1 (nth_error_Some syms i)); rewrite Hi; discriminate).
      unfold sym_at. rewrite LB7. unfold OverlayFlush.LS in *. rewrite !PR7 by lia. rewrite PB6.
      split; [exact Y1|]. split; [exact Y2| exact Y3]. }
    assert (ROOM : vsize fS7 + csum CC syms + arr_get static_ltree_dl END_BLOCK <= 8 * PBL).
    { rewrite static_ltree_256, V7, P4, (CE syms VAL). unfold OverlayFlush.nS in NR. lia. }
    assert (ROOM' : vsize fS7 + csum CC syms <= 8 * PBL) by (pose proof static_ltree_256; lia).
    assert (TABS : Forall (tabs_ok static_ltree_dl static_dtree_dl) syms).
    { apply Forall_forall. intros dl Hdl. destruct (cost_of_static dl (proj1 (Forall_forall _ _) VAL _ Hdl)) as (_ & _ & T1 & T2).
      split; [exact T1| exact T2]. }
    assert (SYMN : ds_sym_next fS7 = 3 * Z.of_nat (length syms)) by (rewrite SN7; reflexivity).
    assert (SYMROOM : ds_lit_bufsize fS7 + 3 * Z.of_nat (length syms) <= PBL) by (rewrite LB7, P4; unfold OverlayFlush.nS in NR; lia).
    destruct (cb_race_ok fS7 static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl syms
                SYMN BYTES DR ltac:(unfold BINV in BINV7; lia) LENSX RACEk PBL AL7 ROOM' SYMROOM BINV7 DM TABS (ct_pb _ CT7)
                ltac:(rewrite static_ltree_256; lia) ROOM)
      as (CBOK & CBE & CBV & CBB & CBP & CBPR & CBL).
    split; [exact BINV6|]. split; [exact R6|]. split; [exact CBOK|]. split; [exact SN7|]. split; [exact LB7|].
    pose proof (CE syms VAL) as CES. subst CC.
    rewrite EfSe. split; [exact CBB|]. split; [rewrite CBV, V7, static_ltree_256, CES; unfold Sstat; lia|].
    split; [apply cty_compress_block; exact CT7| exact CBL].
  Qed.

  Lemma put_byte_bits : forall X c, ds_pending (put_byte X c) = ds_pending X + 1 /\ ds_bi_valid (put_byte X c) = ds_bi_valid X
    /\ ds_bi_buf (put_byte X c) = ds_bi_buf X /\ arr_len (ds_pending_buf (put_byte X c)) = arr_len (ds_pending_buf X)
    /\ ds_window (put_byte X c) = ds_window X.
  Proof. intros X c. unfold put_byte. dsred. rewrite arr_len_set. repeat split; reflexivity. Qed.

  Lemma put_short_bits : forall X w, ds_pending (put_short X w) = ds_pending X + 2 /\ ds_bi_valid (put_short X w) = ds_bi_valid X
    /\ ds_bi_buf (put_short X w) = ds_bi_buf X /\ arr_len (ds_pending_buf (put_short X w)) = arr_len (ds_pending_buf X)
    /\ ds_window (put_short X w) = ds_window X.
  Proof.
    intros X w. unfold put_short.
    destruct (put_byte_bits (put_byte X (Z.land w 255)) (Z.shiftr (wrap16 w) 8)) as (A1 & A2 & A3 & A4 & A5).
    destruct (put_byte_bits X (Z.land w 255)) as (C1 & C2 & C3 & C4 & C5).
    rewrite A1, A2, A3, A4, A5, C1, C2, C3, C4, C5. repeat split; reflexivity || lia.
  Qed.

  Lemma bi_windup_bits' : forall X, 0 <= ds_bi_valid X <= 16 ->
    ds_bi_valid (bi_windup X) = 0 /\ ds_bi_buf (bi_windup X) = 0
    /\ ds_pending X <= ds_pending (bi_windup X) /\ 8 * ds_pending (bi_windup X) <= vsize X + 7
    /\ arr_len (ds_pending_buf (bi_windup X)) = arr_len (ds_pending_buf X) /\ ds_window (bi_windup X) = ds_window X
    /\ ds_strm (bi_windup X) = ds_strm X /\ ds_lit_bufsize (bi_windup X) = ds_lit_bufsize X.
  Proof.
    intros X BV. unfold bi_windup, put_short, put_byte, vsize.
    destruct (Z.ltb_spec 8 (ds_bi_valid X)); [|destruct (Z.ltb_spec 0 (ds_bi_valid X))]; dsred; rewrite ?arr_len_set; repeat split; try reflexivity; lia.
  Qed.

  Theorem sto_branch :
    len + 4 <= Z.shiftr (wrap64 (ds_static_len fY6 + 3 + 7)) 3 ->
    let X := tr_stored_block fY6 buf len last in
       BINV PBL fY6 /\ ds_window fY6 = ds_window s
    /\ BINV PBL X /\ ds_bi_valid X = 0 /\ 8 * ds_pending X + 96 <= 8 * PBL
    /\ arr_len (ds_pending_buf X) = PBL /\ cty X.
  Proof.
    intros STO. cbv zeta. get_ff.
    pose proof (L_range syms s buf len last FB) as [LR NR]. pose proof (PBL4 syms s buf len last FB) as P4.
    pose proof (fbs_cty _ _ _ _ _ FB) as CT. pose proof (fbs_bi_valid _ _ _ _ _ FB) as BV0. pose proof (fbs_bi_buf _ _ _ _ _ FB) as BB0.
    pose proof (fbs_len _ _ _ _ _ FB) as LEN0.
    pose proof (Sstat_bound syms s buf len last FB) as SB. rewrite <- SLv in SB.
    assert (SLB : Z.shiftr (wrap64 (ds_static_len fY6 + 3 + 7)) 3 = (ds_static_len fY6 + 10) / 8).
    { rewrite Z.shiftr_div_pow2 by lia. rewrite wrap64_id by lia. change (2 ^ 3) with 8. f_equal. lia. }
    rewrite SLB in STO.
    assert (LEN8 : 8 * len + 46 <= 31 * LS).
    { pose proof (Z.mul_div_le (ds_static_len fY6 + 10) 8 ltac:(lia)). unfold OverlayFlush.nS in *. lia. }
    assert (BINV6 : BINV PBL fY6) by (unfold BINV; rewrite PD6, BV6, BB6; lia).
    assert (WIN6 : ds_window fY6 = ds_window s).
    { pose proof (fs0_fields syms s buf len last FB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fwi & _). rewrite <- Fwi. apply (kp_window _ _ K6). }
    split; [exact BINV6|]. split; [exact WIN6|].
    assert (GEN : forall Y, BINV PBL Y -> ds_pending Y = 0 -> arr_len (ds_pending_buf Y) = PBL -> cty Y -> ds_window Y = ds_window s ->
              let X := tr_stored_block Y buf len last in
              BINV PBL X /\ ds_bi_valid X = 0 /\ 8 * ds_pending X + 96 <= 8 * PBL /\ arr_len (ds_pending_buf X) = PBL /\ cty X).
    { intros Y BY PY AY CY WY. cbv zeta.
      assert (CTX : cty (tr_stored_block Y buf len last)).
      { apply cty_tr_stored_block; [exact CY|]. intros off Ho Hl. rewrite WY. pose proof (fbs_buf _ _ _ _ _ FB off Ho) as (O1 & O2 & _). lia. }
      enough (G : let X := tr_stored_block Y buf len last in BINV PBL X /\ ds_bi_valid X = 0 /\ 8 * ds_pending X + 96 <= 8 * PBL /\ arr_len (ds_pending_buf X) = PBL) by (cbv zeta in G; tauto).
      unfold tr_stored_block.
      set (Y1 := send_bits Y (Z.shiftl STORED_BLOCK 1 + last) 3).
      pose proof (send_bits_fp Y (Z.shiftl STORED_BLOCK 1 + last) 3) as FP. cbv zeta in FP. fold Y1 in FP.
      destruct FP as (PD1 & AL1 & _ & LB1 & _).
      assert (BY1 : BINV PBL Y1) by (subst Y1; apply send_bits_BINV; [exact BY| lia| unfold sb_room; rewrite PY; pose proof (L_range syms s buf len last FB); lia]).
      assert (BV1 : 0 <= ds_bi_valid Y1 <= 16) by (unfold BINV in BY1; lia).
      assert (VS1 : vsize Y1 = vsize Y + 3) by (subst Y1; apply send_bits_size).
      assert (V1 : vsize Y1 <= 19) by (rewrite VS1; unfold vsize; unfold BINV in BY; lia).
      destruct (bi_windup_bits' Y1 BV1) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
      set (Y2 := bi_windup Y1) in *.
      destruct (put_short_bits Y2 (wrap16 len)) as (S1 & S2 & S3 & S4 & S5).
      set (Y3 := put_short Y2 (wrap16 len)) in *.
      destruct (put_short_bits Y3 (wrap16 (Z.lnot len))) as (T1 & T2 & T3 & T4 & T5).
      set (Y4 := put_short Y3 (wrap16 (Z.lnot len))) in *.
      assert (P4' : ds_pending Y4 <= 7) by lia.
      assert (GEN2 : forall Z4, ds_pending Z4 = ds_pending Y4 -> ds_bi_valid Z4 = 0 -> ds_bi_buf Z4 = 0 -> arr_len (ds_pending_buf Z4) = PBL ->
                 let X := set_pending Z4 (ds_pending Z4 + len) in
                 BINV PBL X /\ ds_bi_valid X = 0 /\ 8 * ds_pending X + 96 <= 8 * PBL /\ arr_len (ds_pending_buf X) = PBL).
      { intros Z4 ZP ZV ZBB ZA. cbv zeta. dsred. unfold BINV. dsred. rewrite ZV, ZBB, ZA, ZP. lia. }
      assert (A4 : arr_len (ds_pending_buf Y4) = PBL) by (rewrite T4, S4, W5, AL1; exact AY).
      assert (KB : forall x a, ds_pending (set_pending_buf x a) = ds_pending x /\ ds_bi_valid (set_pending_buf x a) = ds_bi_valid x
                               /\ ds_bi_buf (set_pending_buf x a) = ds_bi_buf x /\ ds_pending_buf (set_pending_buf x a) = a)
        by (clear; intros; dsred; repeat split; reflexivity).
      destruct (negb (len =? 0)); [destruct buf as [off|]|].
      - destruct (KB Y4 (arr_blit (ds_pending_buf Y4) (ds_pending Y4) (ds_window Y4) off len)) as (K1 & K2 & K3 & K4).
        apply (GEN2 (set_pending_buf Y4 (arr_blit (ds_pending_buf Y4) (ds_pending Y4) (ds_window Y4) off len))
                   K1 ltac:(rewrite K2; lia) ltac:(rewrite K3; lia) ltac:(rewrite K4, arr_len_blit; exact A4)).
      - exact (GEN2 Y4 eq_refl ltac:(lia) ltac:(lia) A4).
      - exact (GEN2 Y4 eq_refl ltac:(lia) ltac:(lia) A4). }
    assert (CT0 : cty fs0).
    { unfold OverlayFlush.fs0. destruct (cs_data_type (ds_strm s) =? Z_UNKNOWN); [apply cty_set_strm_dt; exact CT| exact CT]. }
    assert (CT6 : cty fY6).
    { rewrite EfY6. apply cty_set_opt_len. rewrite EfY5. apply cty_build_tree. rewrite EfY4. apply cty_scan_tree.
      rewrite EfY3. apply cty_scan_tree. rewrite EfY2. apply cty_build_tree. rewrite EfY1. apply cty_build_tree. exact CT0. }
    apply (GEN fY6 BINV6 PD6 ltac:(rewrite PB6; reflexivity) CT6 WIN6).
  Qed.

  Theorem tail_bits : forall X, BINV PBL X -> vsize X + 87 <= 8 * PBL -> arr_len (ds_pending_buf X) = PBL -> cty X ->
    let X8 := init_block X in
    let X9 := if negb (last =? 0) then bi_windup X8 else X8 in
       BINV PBL X8 /\ ds_pending X8 + 2 <= PBL /\ ds_pending (bi_windup X8) <= PBL
    /\ vsize X9 + 80 <= 8 * PBL /\ 0 <= ds_bi_valid X9 <= 16 /\ 0 <= ds_bi_buf X9 < 2 ^ 16 /\ 0 <= ds_pending X9
    /\ cty X9 /\ ds_strm X9 = ds_strm X.
  Proof.
    intros X BX VX AX CX. cbv zeta.
    destruct (init_block_bits X) as (I1 & I2 & I3 & I4 & I5).
    assert (B8 : BINV PBL (init_block X)) by (unfold BINV in *; rewrite I1, I2, I3; exact BX).
    assert (V8 : vsize (init_block X) = vsize X) by (unfold vsize; rewrite I1, I2; reflexivity).
    assert (P8 : ds_pending (init_block X) + 2 <= PBL).
    { pose proof (pending_le_vsize (init_block X) ltac:(unfold BINV in B8; lia)). lia. }
    destruct (bi_windup_bits PBL (init_block X) B8 P8) as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
    assert (C8 : cty (init_block X)) by (apply cty_init_block; exact CX).
    split; [exact B8|]. split; [exact P8|]. split; [lia|].
    destruct (negb (last =? 0)).
    - split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold BINV in W1; lia|]. split; [apply cty_bi_windup; exact C8| rewrite W7; exact I5].
    - split; [lia|]. unfold BINV in B8. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact C8| exact I5].
  Qed.
End FB3.
