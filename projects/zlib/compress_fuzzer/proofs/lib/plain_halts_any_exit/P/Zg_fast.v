(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_frame Z_slow_kit
  Z_lmatch Z_tr_rod Zg_defl_iface Zg_defl_iface2 Zg_slow_frame Zg_fast_model Zg_fast_kit Zg_fast_fill Zg_fast_hash Zg_fast_dist Zg_fast_lit
  Zg_fast_fbA Zg_fast_fbB Zg_fast_fbC Zg_fast_tail.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast2 RefDeflFast3 RefDeflFast6 LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma st_bflush_true' : forall s,
  st_bflush s true = (flush_block_only s 0, if cs_avail_out (ds_strm (flush_block_only s 0)) =? 0 then LRet need_more else LCont).
Proof. intros s. unfold st_bflush, flush_block. cbv zeta. destruct (_ =? 0); reflexivity. Qed.

Lemma deflate_tail_finish_eq' : forall t,
  deflate_tail t Z_FINISH = (flush_block_only t 1, if cs_avail_out (ds_strm (flush_block_only t 1)) =? 0 then finish_started else finish_done).
Proof. intros t. unfold deflate_tail, flush_block. change (Z_FINISH =? Z_FINISH) with true. cbv iota zeta. destruct (_ =? 0); reflexivity. Qed.

Lemma st_tally_hi : forall s, 3 <= ds_match_length s -> st_tally s = st_dist s.
Proof. intros s H. unfold st_tally, MIN_MATCH. destruct (Z.leb_spec 3 (ds_match_length s)); [reflexivity| lia]. Qed.

Lemma st_tally_lo : forall s, ds_match_length s < 3 -> st_tally s = st_lit s.
Proof. intros s H. unfold st_tally, MIN_MATCH. destruct (Z.leb_spec 3 (ds_match_length s)); [lia| reflexivity]. Qed.

Section FASTG.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFW : fill_window_stmtg.
Hypothesis HTFBLK : tr_flush_block_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : 0 <= flush <= 5.

Local Notation FKq := (FK L flush rest0 lo r F fc me).
Local Notation FKr := (FKret L flush rest0 lo r F fc me).
Local Notation ROOM s := (Box (OUT s <= length rest0)%nat).

Lemma room_OUTf : forall s, ROOM s -> (length (cs_out_rev (ds_strm s)) <= length rest0)%nat.
Proof. intros s [H]. exact H. Qed.

Lemma fast_siteA : forall (Q : machine_state -> Prop) (X7 : deflate_state),
  SCFGg inp X7 -> flush_ok X7 0 -> ROOM (flush_block_only X7 0) ->
  (cs_avail_out (ds_strm (flush_block_only X7 0)) = 0 -> FKr Q 0 (flush_block_only X7 0)) ->
  (cs_avail_out (ds_strm (flush_block_only X7 0)) <> 0 -> FKq Q Z_FAST_HEAD (flush_block_only X7 0)) ->
  FKA L flush rest0 lo r F fc me Q X7.
Proof.
  intros Q X7 C FOK RM K0 K1. pose proof (SCFGg_fbo _ _ _ C FOK) as CF.
  unfold FKA. intros until m'. intros SI.
  eapply (fast_fbA L flush inp rest0 lo r F fc me CTX HTFBLK HTFB Q X7); [exact SI| exact FOK| exact (g_lbs _ _ C)| exact (g_ws _ _ C)| exact (g_aout _ _ C)| exact (room_OUTf _ RM)|].
  apply fast_aexit; [exact (g_aout _ _ CF)| exact K0| exact K1].
Qed.

Lemma fast_tallyg : forall (Q : machine_state -> Prop) (s3 : deflate_state),
  SCFGg inp s3 -> tally_ok 32768 s3 -> ROOM (fst (st_bflush (fst (st_tally s3)) (snd (st_tally s3)))) ->
  (snd (st_bflush (fst (st_tally s3)) (snd (st_tally s3))) = LCont -> FKq Q Z_FAST_HEAD (fst (st_bflush (fst (st_tally s3)) (snd (st_tally s3))))) ->
  (forall bs, snd (st_bflush (fst (st_tally s3)) (snd (st_tally s3))) = LRet bs -> FKr Q (bs_code bs) (fst (st_bflush (fst (st_tally s3)) (snd (st_tally s3))))) ->
  (3 <= ds_match_length s3 -> FKD L flush rest0 lo r F fc me Q s3) /\ (ds_match_length s3 < 3 -> FKq Q Z_FAST_LIT s3).
Proof.
  intros Q s3 C (SV & RLA & DOK & RLA7 & FOK) RM KC KR.
  pose proof C as [Cws Chs Clbs Cwrap Cwrap0 Cwrng Cain Caout Ctie].

  assert (BF : forall X7, fst (st_tally s3) = X7 -> SCFGg inp X7 ->
    (snd (st_tally s3) = false -> FKq Q Z_FAST_HEAD X7) /\ (snd (st_tally s3) = true -> FKA L flush rest0 lo r F fc me Q X7)).
  { intros X7 E7 C7. rewrite E7 in RM, KC, KR, FOK. split.
    - intros B. rewrite B, st_bflush_false, fst_prf, snd_prf in KC. exact (KC eq_refl).
    - intros B. specialize (FOK B). rewrite B, st_bflush_true' in RM, KC, KR. rewrite fst_prf in RM, KC, KR. rewrite snd_prf in KC, KR.
      apply fast_siteA; [exact C7| exact FOK| exact RM| |].
      + intros A0. rewrite A0 in KR. exact (KR need_more eq_refl).
      + intros A0. replace (cs_avail_out (ds_strm (flush_block_only X7 0)) =? 0) with false in KC by (symmetry; apply Z.eqb_neq; exact A0).
        exact (KC eq_refl). }
  split.
  -
    intros ML3. rewrite (st_tally_hi s3 ML3) in BF.
    destruct (BF (fst (st_dist s3)) eq_refl (SCFGg_SF _ _ _ (SF_st_dist s3) C)) as [B0 B1].
    apply (fast_dist L flush inp rest0 lo r F fc me CTX Q s3 SV ML3 (DOK ltac:(unfold MIN_MATCH; lia)) RLA Cws Chs Clbs B0 B1).
  -
    intros ML2. rewrite (st_tally_lo s3 ML2), tally_lit_eq in BF.
    destruct (BF (tlit1 s3) eq_refl (SCFGg_SF _ _ _ (SF_tlit1 s3) C)) as [B0 B1]. rewrite snd_prf in B0, B1.
    unfold FK. intros until m'. intros SI.
    eapply (fast_lit L flush inp rest0 lo r F fc me CTX Q s3); [exact SI| exact SV| lia| exact Cws| exact Clbs| |].
    + intros NE. apply B0. apply Z.eqb_neq. exact NE.
    + intros EQ. apply B1. apply Z.eqb_eq. exact EQ.
Qed.

Lemma fast_tripg : forall (Q : machine_state -> Prop) (X : deflate_state),
  SCFGg inp X -> trip_ok 32768 32768 X flush -> ROOM (fst (st_body X flush)) ->
  (snd (st_body X flush) = LCont -> FKq Q Z_FAST_HEAD (fst (st_body X flush))) ->
  (snd (st_body X flush) = LBreak -> FKq Q Z_FAST_TAIL (fst (st_body X flush))) ->
  (forall bs, snd (st_body X flush) = LRet bs -> FKr Q (bs_code bs) (fst (st_body X flush))) ->
  FKq Q Z_FAST_HEAD X.
Proof.
  intros Q X C TOK RM KC KB KR. pose proof TOK as (_ & FW & _ & HOK).
  destruct (fill_frameg inp X flush C FW) as [CF1 _].
  pose proof C as [Cws Chs Clbs Cwrap Cwrap0 Cwrng Cain Caout Ctie].
  apply (fast_fill L flush inp rest0 lo r F fc me CTX HFW Q X TOK HFL Cwrap Cain Ctie).
  -
    intros X1 EF.
    assert (ES : st_body X flush = (X1, LRet need_more)) by (rewrite st_body_eq2, EF; reflexivity).
    rewrite ES in KR. rewrite fst_prf, snd_prf in KR. exact (KR need_more eq_refl).
  -
    intros X1 EF.
    assert (ES : st_body X flush = (X1, LBreak)) by (rewrite st_body_eq2, EF; reflexivity).
    rewrite ES in KB. rewrite fst_prf, snd_prf in KB. exact (KB eq_refl).
  -
    intros X1 EF LA3.
    assert (ES : st_body X flush = st_rest X1) by (rewrite st_body_eq2, EF; reflexivity).
    rewrite (st_rest_hi X1 LA3) in ES. rewrite ES in RM, KC, KR. clear ES KB.
    rewrite EF in HOK, CF1. rewrite fst_prf in CF1. rewrite fst_prf, snd_prf in HOK.
    destruct (hash_ok_hi _ _ (HOK eq_refl) LA3) as (SV1 & RLA1 & LMOK & TOK7).
    pose proof (SCFGg_SF _ _ _ (SF_ins_str X1 (ds_strstart X1)) CF1) as C2.
    apply (fast_hash L flush inp rest0 lo r F fc me CTX Q X1 SV1 LA3 (g_ws _ _ CF1) (g_hs _ _ CF1)).
    +
      intros LMF. rewrite (st_match_false _ _ LMF) in RM, KC, KR, TOK7.
      destruct (fast_tallyg Q _ C2 TOK7 RM KC KR) as [KD KL].
      apply fast_mtest; [| exact KD| exact KL].
      destruct TOK7 as (SV2 & _). exact (ti_ml _ SV2).
    +
      intros LMT. rewrite (st_match_true _ _ LMT) in RM, KC, KR, TOK7.
      assert (C3 : SCFGg inp (set_match_length (fst (longest_match (ins_str X1 (ds_strstart X1)) (hash_hh X1))) (snd (longest_match (ins_str X1 (ds_strstart X1)) (hash_hh X1))))).
      { destruct (longest_match_ms (ins_str X1 (ds_strstart X1)) (hash_hh X1)) as (ms & E). rewrite E. refine (SCFGg_SF _ _ _ _ C2). reflexivity. }
      destruct (fast_tallyg Q _ C3 TOK7 RM KC KR) as [KD KL].
      apply (fast_lm L flush inp rest0 lo r F fc me CTX Q _ _ (g_ws _ _ C2) (LMOK LMT)).
      * intros ML3. apply KD. exact ML3.
      * intros ML2. apply KL. exact ML2.
  -
    intros X1 EF LA3.
    assert (ES : st_body X flush = st_rest X1) by (rewrite st_body_eq2, EF; reflexivity).
    rewrite (st_rest_lo X1 LA3) in ES. rewrite ES in RM, KC, KR. clear ES KB.
    rewrite EF in HOK, CF1. rewrite fst_prf in CF1. rewrite fst_prf, snd_prf in HOK.
    destruct (hash_ok_lo _ _ (HOK eq_refl) LA3) as (SV1 & RLA1 & TOK7).
    destruct (fast_tallyg Q _ CF1 TOK7 RM KC KR) as [KD KL].
    apply fast_mtest; [exact (ti_ml _ SV1)| exact KD| exact KL].
Qed.

Lemma fast_tailallg : forall (Q : machine_state -> Prop) (X1 : deflate_state),
  SCFGg inp X1 -> tail_ok 32768 X1 flush -> ROOM (fst (fast_tailres X1 flush)) ->
  FKr Q (bs_code (snd (fast_tailres X1 flush))) (fst (fast_tailres X1 flush)) ->
  FKq Q Z_FAST_TAIL X1.
Proof.
  intros Q X1 C (RSS & RSN & FOK & FOKD) RM KR.
  pose proof (SCFGg_tail_st inp X1 C) as CT.
  assert (CT3 : ds_lit_bufsize (tail_st X1) = 16384 /\ ds_w_size (tail_st X1) = 32768 /\ 0 <= cs_avail_out (ds_strm (tail_st X1)) < 2^31)
    by (split; [exact (g_lbs _ _ CT)| split; [exact (g_ws _ _ CT)| exact (g_aout _ _ CT)]]).
  destruct CT3 as (CT1 & CT2 & CT3).
  unfold fast_tailres in RM, KR.
  apply (fast_tail1 L flush inp rest0 lo r F fc me CTX Q X1); [lia| exact HFL| |].
  -
    intros HF. specialize (FOK HF).
    replace (deflate_tail (tail_st X1) flush) with (deflate_tail (tail_st X1) Z_FINISH) in RM, KR by (rewrite HF; reflexivity).
    rewrite deflate_tail_finish_eq' in RM, KR. rewrite fst_prf in RM, KR. rewrite snd_prf in KR.
    intros until m'. intros SI.
    eapply (fast_fbB L flush inp rest0 lo r F fc me CTX HTFBLK HTFB Q); [exact SI| exact FOK| exact CT1| exact CT2| exact CT3| exact (room_OUTf _ RM)|].
    pose proof (SCFGg_fbo _ _ _ CT FOK) as CF.
    apply fast_finB; [| exact (g_nraw _ _ CF)| pose proof (g_wrng _ _ CF); lia|].
    2:{ destruct (cs_avail_out (ds_strm (flush_block_only (tail_st X1) 1)) =? 0); exact KR. }
    pose proof (fbo_avail_out (tail_st X1) 1 FOK CT1 CT3). lia.
  -
    intros NF. rewrite (deflate_tail_nf_eq (tail_st X1) flush NF) in RM, KR.
    apply fast_symC; [cbn [ds_sym_next tail_st set_insert]; clear - RSN; lia| |].
    + intros S0. replace (ds_sym_next (tail_st X1) =? 0) with true in KR by (symmetry; apply Z.eqb_eq; exact S0). cbn [negb] in KR.
      rewrite fst_prf, snd_prf in KR. exact KR.
    + intros S1. specialize (FOKD NF S1). replace (ds_sym_next (tail_st X1) =? 0) with false in RM, KR by (symmetry; apply Z.eqb_neq; exact S1). cbn [negb] in RM, KR.
      rewrite fst_prf in RM, KR. rewrite snd_prf in KR.
      intros until m'. intros SI.
      eapply (fast_fbC L flush inp rest0 lo r F fc me CTX HTFBLK HTFB Q); [exact SI| exact FOKD| exact CT1| exact CT2| exact CT3| exact (room_OUTf _ RM)|].
      apply fast_finC; [|].
      2:{ destruct (cs_avail_out (ds_strm (flush_block_only (tail_st X1) 0)) =? 0); exact KR. }
      pose proof (fbo_avail_out (tail_st X1) 0 FOKD CT1 CT3). lia.
Qed.

Lemma fast_loopg : forall (f : nat) (X : deflate_state),
  SCFGg inp X -> loop_ok 32768 32768 f X flush -> ftail_safe flush f X -> ROOM (fst (fast_res flush f X)) ->
  FKq (slow_post_gen r F fc L (fst (fast_res flush f X)) (bs_code (snd (fast_res flush f X))) inp rest0 lo me) Z_FAST_HEAD X.
Proof.
  induction f as [|f IH]; intros X C LOK TS RM; [destruct LOK|].
  rewrite loop_ok_S in LOK. destruct LOK as [TOK LOK]. rewrite ftail_safe_S in TS.
  destruct (fbody_frameg inp X flush C TOK) as [C' O'].
  rewrite fast_res_S in RM |- *.
  remember (snd (st_body X flush)) as o eqn:ES. symmetry in ES. destruct o as [| |bs].
  -
    apply fast_tripg; [exact C| exact TOK| | | |].
    + destruct RM as [RM]. constructor. eapply Nat.le_trans; [apply (OUT_fres inp flush f _ C' LOK)| exact RM].
    + intros _. apply IH; assumption.
    + intros E'. rewrite ES in E'. discriminate.
    + intros bs E'. rewrite ES in E'. discriminate.
  -
    apply fast_tripg; [exact C| exact TOK| | | |].
    + destruct RM as [RM]. constructor. eapply Nat.le_trans; [apply OUT_ftailres| exact RM].
    + intros E'. rewrite ES in E'. discriminate.
    + intros _. apply fast_tailallg; [exact C'| exact TS| exact RM|]. apply (fast_epi L flush inp rest0 lo r F fc me CTX).
    + intros bs E'. rewrite ES in E'. discriminate.
  -
    rewrite fst_prf, snd_prf. rewrite fst_prf in RM.
    apply fast_tripg; [exact C| exact TOK| exact RM| | |].
    + intros E'. rewrite ES in E'. discriminate.
    + intros E'. rewrite ES in E'. discriminate.
    + intros bs' E'. rewrite ES in E'. injection E' as <-. apply (fast_epi L flush inp rest0 lo r F fc me CTX).
Qed.
End FASTG.

Theorem deflate_fast_specg : fill_window_stmtg -> tr_flush_block_stmt -> tr_flush_bits_stmt -> deflate_fast_stmtg.
Proof.
  intros HFW HTFBLK HTFB. unfold deflate_fast_stmtg.
  intros until m. intros DR DIN TIE DOUT MI RELRO STK LO SP16 BEL IO SAFE HFL WS HS LBS WRAP WRAP0 WRNG AIN RAO ROOM -> ->.
  unfold Z_DEFLATE_FAST.
  set (r := mkSR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  pose proof (st_lay _ _ _ _ (proj2 DR)) as LAY.
  assert (CTX : slow_ctx L inp rest0 lo r m) by (constructor; assumption).
  destruct (fast_safe_open d flush SAFE WS HS) as (DW & LOK & TSAFE).
  assert (C : SCFGg inp d) by (constructor; assumption).
  rewrite deflate_fast_res in ROOM.

  lay_open LAY. pose proof BEL as BEL0. below_open BEL0. pose proof IO as I0. io_open I0. unfold Z_FAST_STACK in LO.
  pose proof (munch_refl (slow_W L rest0 lo r) m) as MU. unfold slow_W in MU. cbn [r_sp r] in MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf. pose proof (wmono_refl psegs m) as WMf.
  carve_frame 128%nat STK.
  (* 1.4: 34 prologue instructions; the last store is sd a4,8(sp) (28th); sp+0 is never written *)
  do 28 zs. name_mem mP.

  (* 1.4: _length_code / _dist_code are file-static, addressed pc-relative: no GOT reads *)
  do 6 zs.
  change (wz 0x11cf0) with (wz Z_LENGTH_CODE). change (wz 0x11af0) with (wz Z_DIST_CODE).
  assert (RM0 : Box (OUT (fst (fast_res flush (lz_fuel d) d)) <= length rest0)%nat) by (constructor; exact ROOM).
  assert (RMd : Box (length (cs_out_rev (ds_strm d)) <= length rest0)%nat).
  { constructor. eapply Nat.le_trans; [apply (OUT_fres inp flush (lz_fuel d) d C LOK)| exact ROOM]. }
  assert (SI : FINV L flush rest0 lo r m d mP).
  { split.
    { apply (DREP_agree m mP L d DR).
      - eapply ag_blocks_munch; [exact LAY| exact MUf| exact WMf| | | | |]; cbn [disjoint_from]; slia.
      - apply (agree_on_of_munch [(lo, bv_unsigned sp)]); [exact MUf| exact WMf| lia| lia| cbn [disjoint_from]; slia]. }
    split; [apply (dout_munch _ m mP L rest0 _ DOUT RMd MUf WMf); cbn [disjoint_from]; slia|].
    split; [exact RMd|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  eapply evt_mono.
  { eapply (fast_loopg L flush inp rest0 lo r F fc m CTX HFW HTFBLK HTFB HFL (lz_fuel d) d C LOK TSAFE RM0). exact SI. }
  intros ms' P. unfold deflate_fast_post. rewrite deflate_fast_res. exact P.
Qed.
