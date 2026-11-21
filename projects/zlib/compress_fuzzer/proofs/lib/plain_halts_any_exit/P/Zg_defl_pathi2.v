(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay RefDeflSlow6 RefDeflSafeS.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel RefDeflSafeG RefDeflSafeT RefDeflSafeFB RefDeflSafeLF RefDeflSafeF RefDeflSafeL0 RefDeflSafeL2 RefDeflSafeL5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeI6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel FlushBlockModel RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM RefDeflFast1 RefDeflFast2 RefDeflFast3 RefDeflFast6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BoundFw BoundSlow BoundPat.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Export DeflPat2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_defl_model Z_defl_path Zg_defl_path Zg_defl_path2 Zg_defl_pathi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma CF_ins_str : forall X str, CF (ins_str X str) = CF X.
Proof. intros X str. reflexivity. Qed.

Lemma CF_fst_hash : forall s, CF (fst (st_hash s)) = CF s.
Proof. intros s. unfold st_hash. destruct (MIN_MATCH <=? ds_lookahead s); [| reflexivity]. rewrite ins_str_eq. cbn [fst]. apply CF_ins_str. Qed.

Lemma CF_st_match : forall s hh, CF (st_match s hh) = CF s.
Proof.
  intros s hh. unfold st_match. destruct (lm_cond s hh); [| reflexivity].
  destruct (longest_match_ms s hh) as [ms E]. destruct (longest_match s hh) as [s' ml]. cbn [fst] in E. subst s'. reflexivity.
Qed.

Lemma CF_insl : forall X, CF (insl_st X) = CF X.
Proof. intros X. rewrite insl_eq, ins_str_eq. cbn [fst]. reflexivity. Qed.

Lemma CF_fast_insert : forall n s, CF (deflate_fast_insert n s) = CF s.
Proof.
  induction n as [|n IH]; intros s; [reflexivity|].
  rewrite deflate_fast_insert_step. cbv zeta. destruct (negb _); [rewrite IH|]; apply CF_insl.
Qed.

Lemma CF_st_noins : forall s, CF (st_noins s) = CF s.
Proof. intros s. reflexivity. Qed.

Lemma CF_st_ins : forall s, CF (st_ins s) = CF s.
Proof. intros s. unfold st_ins. cbv zeta. rewrite CF_set_strstart, CF_fast_insert. reflexivity. Qed.

Lemma CF_st_lit : forall s, CF (fst (st_lit s)) = CF s.
Proof.
  intros s. unfold st_lit.
  pose proof (tally_lit_facts s (arr_get (ds_window s) (ds_strstart s))) as (TK & _). cbv zeta in TK.
  pose proof (CF_tally_keep _ _ TK) as E.
  destruct (tr_tally_lit s _) as [t b]. cbv zeta. cbn [fst] in E |- *. rewrite <- E. reflexivity.
Qed.

Lemma CF_st_dist : forall s, CF (fst (st_dist s)) = CF s.
Proof.
  intros s. unfold st_dist.
  pose proof (tally_dist_facts s (wrap32 (ds_strstart s - ds_match_start s)) (ds_match_length s - MIN_MATCH)) as (TK & _). cbv zeta in TK.
  pose proof (CF_tally_keep _ _ TK) as E.
  destruct (tr_tally_dist s _ _) as [t b]. cbv zeta. cbn [fst] in E |- *. rewrite <- E.
  destruct (ins_cond _); [rewrite CF_st_ins | rewrite CF_st_noins]; reflexivity.
Qed.

Lemma CF_st_tally : forall s, CF (fst (st_tally s)) = CF s.
Proof. intros s. unfold st_tally. destruct (MIN_MATCH <=? _); [apply CF_st_dist | apply CF_st_lit]. Qed.

Lemma CF_flush_block : forall s last, CF (fst (flush_block s last)) = CF s.
Proof. intros s last. unfold flush_block. cbv zeta. destruct (_ =? 0); cbn [fst]; apply CF_flush_block_only. Qed.

Lemma flush_block_bs : forall s last bs, snd (flush_block s last) = Some bs -> bs = (if negb (last =? 0) then finish_started else need_more).
Proof.
  intros s last bs. unfold flush_block. cbv zeta. destruct (_ =? 0); cbn [snd]; intros E; [| discriminate E].
  injection E as E. symmetry. exact E.
Qed.

Lemma CF_st_bflush : forall s b, CF (fst (st_bflush s b)) = CF s.
Proof.
  intros s b. unfold st_bflush. destruct b; [| reflexivity].
  pose proof (CF_flush_block s 0) as E. destruct (flush_block s 0) as [s' [bs|]]; cbn [fst] in E |- *; exact E.
Qed.

Lemma st_bflush_ret : forall s b bs, snd (st_bflush s b) = LRet bs -> bs = need_more.
Proof.
  intros s b bs. unfold st_bflush. destruct b; [| cbn [snd]; intros E; discriminate E].
  pose proof (flush_block_bs s 0) as R. destruct (flush_block s 0) as [s' [bs'|]]; cbn [snd] in R |- *; intros E; [| discriminate E].
  injection E as E. subst bs'. exact (R bs eq_refl).
Qed.

Lemma st_bflush_nobreak : forall s b, snd (st_bflush s b) <> LBreak.
Proof.
  intros s b. unfold st_bflush. destruct b; [| cbn [snd]; intros E; discriminate E].
  destruct (flush_block s 0) as [s' [bs'|]]; cbn [snd]; intros E; discriminate E.
Qed.

Lemma CF_st_fill : forall s flush, CF (fst (RefDeflFast6.st_fill s flush)) = CF s.
Proof.
  intros s flush. unfold RefDeflFast6.st_fill. destruct (_ <? _); [| reflexivity].
  destruct (_ && _); [cbn [fst]; apply CF_fill_window|]. destruct (_ =? 0); cbn [fst]; apply CF_fill_window.
Qed.

Lemma st_fill_ret : forall s flush bs, snd (RefDeflFast6.st_fill s flush) = Some (LRet bs) -> bs = need_more.
Proof.
  intros s flush bs. unfold RefDeflFast6.st_fill. destruct (_ <? _); [| cbn [snd]; intros E; discriminate E].
  destruct (_ && _); [cbn [snd]; intros E; injection E as E; symmetry; exact E|].
  destruct (_ =? 0); cbn [snd]; intros E; discriminate E.
Qed.

Lemma st_fill_nobreak0 : forall s, snd (RefDeflFast6.st_fill s Z_NO_FLUSH) <> Some LBreak.
Proof.
  intros s. unfold RefDeflFast6.st_fill. destruct (_ <? _); [| cbn [snd]; intros E; discriminate E].
  change (Z_NO_FLUSH =? Z_NO_FLUSH) with true. rewrite andb_true_r.
  destruct (Z.ltb_spec (ds_lookahead (fill_window s)) MIN_LOOKAHEAD) as [L|L]; cbn [snd]; [intros E; discriminate E|].
  destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [E0|E0]; cbn [snd]; [| intros E; discriminate E].
  exfalso. rewrite E0 in L. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in L. lia.
Qed.

Lemma CF_st_body : forall s flush, CF (fst (st_body s flush)) = CF s.
Proof.
  intros s flush. rewrite st_body_eq2. pose proof (CF_st_fill s flush) as E1.
  destruct (snd (RefDeflFast6.st_fill s flush)) as [o|]; [cbn [fst]; exact E1|].
  unfold st_rest. rewrite CF_st_bflush, CF_st_tally, CF_st_match, CF_fst_hash. exact E1.
Qed.

Lemma st_body_ret : forall s flush bs, snd (st_body s flush) = LRet bs -> bs = need_more.
Proof.
  intros s flush bs. rewrite st_body_eq2. pose proof (st_fill_ret s flush) as R.
  destruct (snd (RefDeflFast6.st_fill s flush)) as [o|]; [cbn [snd]; intros E; subst o; exact (R bs eq_refl)|].
  unfold st_rest. apply st_bflush_ret.
Qed.

Lemma st_body_nobreak0 : forall s, snd (st_body s Z_NO_FLUSH) <> LBreak.
Proof.
  intros s. rewrite st_body_eq2. pose proof (st_fill_nobreak0 s) as NB.
  destruct (snd (RefDeflFast6.st_fill s Z_NO_FLUSH)) as [o|]; [cbn [snd]; intros E; subst o; exact (NB eq_refl)|].
  unfold st_rest. apply st_bflush_nobreak.
Qed.

Lemma CF_floop : forall fuel s flush, CF (fst (deflate_fast_loop fuel s flush)) = CF s.
Proof.
  induction fuel as [|f IH]; intros s flush; [reflexivity|]. rewrite loop_step.
  pose proof (CF_st_body s flush) as E.
  destruct (snd (st_body s flush)); cbn [fst]; [rewrite IH; exact E | exact E | exact E].
Qed.

Lemma floop_ret : forall fuel s flush bs, snd (deflate_fast_loop fuel s flush) = Some bs -> bs = need_more.
Proof.
  induction fuel as [|f IH]; intros s flush bs; [cbn; intros E; discriminate E|]. rewrite loop_step.
  pose proof (st_body_ret s flush) as R.
  destruct (snd (st_body s flush)) as [| |bs']; cbn [snd]; [apply IH | intros E; discriminate E |].
  intros E. injection E as E. subst bs'. exact (R bs eq_refl).
Qed.

Lemma floop_noflush : forall fuel s ws hs, loop_ok ws hs fuel s Z_NO_FLUSH -> snd (deflate_fast_loop fuel s Z_NO_FLUSH) <> None.
Proof.
  induction fuel as [|f IH]; intros s ws hs HL; [exact (False_ind _ HL)|].
  rewrite loop_ok_S in HL. destruct HL as [_ HL]. rewrite loop_step.
  pose proof (st_body_nobreak0 s) as NB.
  destruct (snd (st_body s Z_NO_FLUSH)); [exact (IH _ _ _ HL) | exfalso; exact (NB eq_refl) | cbn [snd]; intros HH; discriminate HH].
Qed.

Lemma CF_deflate_tail : forall s flush, CF (fst (deflate_tail s flush)) = CF s.
Proof.
  intros s flush. unfold deflate_tail. destruct (flush =? Z_FINISH).
  - pose proof (CF_flush_block s 1) as E. destruct (flush_block s 1) as [s' [bs|]]; cbn [fst] in E |- *; exact E.
  - destruct (negb (ds_sym_next s =? 0)); [| reflexivity].
    pose proof (CF_flush_block s 0) as E. destruct (flush_block s 0) as [s' [bs|]]; cbn [fst] in E |- *; exact E.
Qed.

Lemma deflate_tail_bstate : forall s flush, snd (deflate_tail s flush) = block_done -> flush <> Z_FINISH.
Proof.
  intros s flush. unfold deflate_tail. destruct (Z.eqb_spec flush Z_FINISH) as [F|F]; [| intros _; exact F].
  pose proof (flush_block_bs s 1) as R. destruct (flush_block s 1) as [s' [bs|]]; cbn [snd] in R |- *; intros E; [| discriminate E].
  exfalso. rewrite (R bs eq_refl) in E. discriminate E.
Qed.

Theorem CF_fast : forall s flush, CF (fst (deflate_fast s flush)) = CF s.
Proof.
  intros s flush. unfold deflate_fast. pose proof (CF_floop (lz_fuel s) s flush) as EL.
  destruct (deflate_fast_loop (lz_fuel s) s flush) as [s1 [bs|]]; cbn [fst] in EL |- *; [exact EL|].
  cbv zeta. rewrite CF_deflate_tail, CF_set_insert. exact EL.
Qed.

Theorem fast_bstate : forall s flush, fast_safe s flush -> snd (deflate_fast s flush) = block_done -> flush <> Z_NO_FLUSH /\ flush <> Z_FINISH.
Proof.
  intros s flush (_ & HL & _). unfold deflate_fast.
  pose proof (floop_ret (lz_fuel s) s flush) as R.
  assert (NB : flush = Z_NO_FLUSH -> snd (deflate_fast_loop (lz_fuel s) s flush) <> None)
    by (intros F; rewrite F in HL |- *; exact (floop_noflush _ _ _ _ HL)).
  destruct (deflate_fast_loop (lz_fuel s) s flush) as [s1 [bs|]]; cbn [fst snd] in R, NB |- *.
  - intros E. exfalso. rewrite (R bs eq_refl) in E. discriminate E.
  - cbv zeta. intros E. split; [intros F; exact (NB F eq_refl) | exact (deflate_tail_bstate _ _ E)].
Qed.

Section PathProofG2.
  Variables (inp : list Z) (flush : Z).
  Variable c0 : cstrm.
  Variable s0 : deflate_state.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hs0 : ds_strm s0 = c0.
  Hypothesis D0 : dwf s0.
  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK.
  Hypothesis HAO : cs_avail_out c0 < 2^31.
  Hypothesis HIN : cs_input c0 = arr_of_list inp.
  Hypothesis HIL : zlength inp < 2^31.
  Hypothesis HIB : Forall (fun b => 0 <= b < 256) inp.
  Hypothesis HWS : ds_w_size s0 = 32768.
  Hypothesis HHS : ds_hash_size s0 = 32768.
  Hypothesis HLBS : ds_lit_bufsize s0 = 16384.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.
  Local Abbreviation ST := (RefDeflSafeI4.ST c0 s0).

  Definition P2g2 (s : deflate_state) : Prop := ST s /\ PATG2 s.

  Lemma Hfl5b : 0 <= flush <= 5.
  Proof. destruct HFL as [-> | [-> | ->]]; unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK; lia. Qed.

  Lemma P2g2_slf : forall s v, P2g2 s -> - 2 <= v <= 5 -> P2g2 (set_last_flush s v).
  Proof. intros s v [H P] Hv. split; [exact (ST_set_last_flush c0 s0 s v H Hv) | exact (PATG2_slf s v P)]. Qed.
  Lemma P2g2_err : forall s e, P2g2 s -> P2g2 (fst (err_return s e)).
  Proof. intros s e [H P]. split; [exact (ST_err_return c0 s0 s e H) | exact (PATG2_err s e P)]. Qed.
  Lemma P2g2_fp : forall s, P2g2 s -> P2g2 (flush_pending s) /\ (ds_pending (flush_pending s) = 0 \/ cs_avail_out (ds_strm (flush_pending s)) = 0).
  Proof.
    intros s [H P]. destruct (ST_flush_pending c0 s0 HC0 s H) as (H' & _ & Hor & _).
    split; [split; [exact H' | exact (PATG2_CF _ _ (CF_flush_pending s) P)] | exact Hor].
  Qed.

  Lemma P2g2_facts : forall X, P2g2 X ->
    0 <= cs_avail_in (ds_strm X) < 2^31 /\ 0 <= cs_avail_out (ds_strm X) < 2^31 /\ din_tieg inp X
    /\ ds_hash_size X = 32768 /\ ds_w_bits X = 15 /\ 0 <= ds_lookahead X < 2^31 /\ 0 <= ds_strstart X < 2^31
    /\ ds_w_size X = 32768 /\ ds_lit_bufsize X = 16384.
  Proof.
    intros X [[[[D XX] V] K] P].
    pose proof (sv_ain _ _ V) as A1. pose proof (sv_inlen _ _ V) as A2. pose proof (sv_nin _ _ V) as A3.
    rewrite HIN, arr_len_of_list in A2. unfold zlength in HIL, A2.
    pose proof (sv_out _ _ V) as O1. pose proof (sv_aout _ _ V) as O2. rewrite (c0_out _ HC0w) in O1. unfold zlen in O1. cbn [length Z.of_nat] in O1.
    pose proof (KV_fields _ _ K) as (Kw & Kh & Kl & _). rewrite HWS in Kw. rewrite HHS in Kh. rewrite HLBS in Kl.
    pose proof (df_wsize _ D) as E1. pose proof (df_wbits _ D) as Rw. rewrite Kw in E1.
    assert (WB : ds_w_bits X = 15) by (symmetry; apply pow2_inj_small; [lia | lia | exact E1]).
    pose proof (df_look _ D) as L1. pose proof (df_sl _ D) as L2. pose proof (df_strstart _ D) as L3. rewrite Kw in L2.
    split; [lia|]. split; [lia|]. split; [split; [rewrite (sv_input _ _ V); exact HIN| exact HIB]|].
    split; [exact Kh|]. split; [exact WB|]. split; [lia|]. split; [lia|]. split; [exact Kw| exact Kl].
  Qed.

  Lemma fin_pathg2_ok : forall X, P2g2 X -> ds_pending X = 0 -> (flush = Z_FINISH -> ds_status X = FINISH_STATE) ->
    fin_path flush (dc_fin X flush) X.
  Proof.
    intros X PP Hp Hfin. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    pose proof (df_wrap _ D) as RW.
    pose proof (PATG2_wrap2 X P) as W2.
    destruct (P2g2_facts X PP) as (_ & RAO & _ & _ & _ & _ & _ & _ & LBS).
    destruct (trailer_facts c0 X H Hp) as ((H1 & Po1 & P1) & K1 & O1 & St1 & Wr1 & Lk1).
    assert (HS1 : ST (trailer_st X)) by (split; [exact H1| rewrite K1; exact K]).
    destruct (ST_flush_pending c0 s0 HC0 (trailer_st X) HS1) as (HS2 & Hfp & Hor & Hp2 & St2 & Wr2 & Lk2 & Ai2).
    destruct (DC_flush_pending c0 (trailer_st X) HC0w H1) as (_ & _ & O2 & _).
    pose proof HS2 as [[[D2 _] _] _]. pose proof (df_pend _ D2) as Pd2. pose proof (dwf_sizes _ D2) as (_ & _ & Sl2 & _).
    pose proof (sv_adler _ _ V) as RAD.
    rewrite (trailer_st_put_adler X W2) in *.
    unfold fin_path, dc_fin.
    destruct (Z.eq_dec flush Z_FINISH) as [F4|NF4].
    2:{ replace (negb (flush =? Z_FINISH)) with true by (symmetry; destruct (Z.eqb_spec flush Z_FINISH); [contradiction| reflexivity]). cbv iota.
        split; [apply ole_strm; reflexivity|]. split; [exact RW|]. split; [exact W2|].
        split; [intros _; reflexivity|]. split; [intros F4; contradiction|]. intros F4; contradiction. }
    rewrite F4. change (negb (Z_FINISH =? Z_FINISH)) with false. cbv iota.
    split.
    {
      destruct (ds_wrap X <=? 0); [apply ole_strm; reflexivity|].
      rewrite deflate_trailer_eq, (trailer_st_put_adler X W2). cbv zeta.
      apply (ole_step _ X (flush_pending (put_adler X))); [exact (OUTLE_trans _ _ _ O1 O2)| rewrite fwT_flush_pending; apply fwT_put_adler|].
      generalize (flush_pending (put_adler X)). intros s2. apply ole_strm. cbn [fst]. destruct (0 <? ds_wrap s2); [apply strm_set_wrap| reflexivity]. }
    split; [exact RW|]. split; [exact W2|].
    split; [intros C; contradiction|].
    split.
    { intros _ WN. replace (ds_wrap X <=? 0) with true by (symmetry; apply Z.leb_le; exact WN). reflexivity. }
    intros _ WP. cbv zeta.
    split; [lia|]. split; [lia|]. split; [exact RAD|]. split; [exact LBS|]. split; [exact RAO|]. split; [exact Hfp|].
    split; [rewrite Wr2; exact Wr1|]. split; [lia|].
    replace (ds_wrap X <=? 0) with false by (symmetry; apply Z.leb_gt; exact WP).
    rewrite deflate_trailer_eq, (trailer_st_put_adler X W2). cbv zeta.
    assert (W2' : 0 < ds_wrap (flush_pending (put_adler X))) by (rewrite Wr2, Wr1; exact WP).
    revert W2'. generalize (flush_pending (put_adler X)). intros s2 W2'.
    replace (0 <? ds_wrap s2) with true by (symmetry; apply Z.ltb_lt; exact W2').
    rewrite pending_set_wrap.
    split; [apply ole_strm; apply strm_set_wrap|]. split.
    - intros E. rewrite E. reflexivity.
    - intros E. replace (ds_pending s2 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E). reflexivity.
  Qed.

  Lemma bf_g2 : forall X, P2g2 X -> ds_pending X = 0 -> ds_status X <> FINISH_STATE ->
    let r := dblk2 X flush in
    run_compress_func X flush = r
    /\ BFPOST c0 X flush r /\ CF (fst r) = CF X /\ (snd r = block_done -> flush = Z_BLOCK)
    /\ (ds_level X = 0 -> st_entry X /\ ds_pending_buf_size X = 65536)
    /\ (1 <= ds_level X <= 3 -> fast_safe X flush)
    /\ (4 <= ds_level X -> slow_safe X flush).
  Proof.
    intros X PP Hp Hst0. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    destruct (P2g2_facts X PP) as (_ & _ & _ & _ & _ & _ & _ & WS & LBS).
    assert (PRE : BFPRE c0 X flush) by (split; [exact HC0|]; split; [exact H|]; split; [exact Hp|]; split; [exact Hst0 | exact Hfl5b]).
    cbv zeta. rewrite run_compress_func_dmode.
    destruct (PATG2_cases X D P) as [[M L]|[[M L]|[M L]]]; rewrite M.
    -
      rewrite (dblk2_stored X flush L).
      destruct (stored_bf_spec c0 X flush PRE M) as [_ POST].
      split; [reflexivity|]. split; [exact POST|]. split; [apply CF_stored|].
      split.
      { intros BD. destruct (sto_bstate X flush BD) as [N0 N4]. destruct HFL as [F|[F|F]]; [contradiction| contradiction| exact F]. }
      split.
      { intros _. split.
        + apply (SI_st_entry c0 X HC0 X). split; [exact H|]. split; [reflexivity|]. split; [exact M|]. split; [exact Hst0|]. split; [apply OUTLE_refl| exact Hp].
        + rewrite (df_pbs _ D), LBS. reflexivity. }
      split; [intros C; exfalso; lia| intros C; exfalso; lia].
    -
      rewrite (dblk2_fast X flush L).
      destruct (fast_bf_spec FB_CALL_ok c0 X flush PRE M) as [SAFE POST].
      split; [reflexivity|]. split; [exact POST|]. split; [apply CF_fast|].
      split.
      { intros BD. destruct (fast_bstate X flush SAFE BD) as [N0 N4]. destruct HFL as [F|[F|F]]; [contradiction| contradiction| exact F]. }
      split; [intros C; exfalso; lia|]. split; [intros _; exact SAFE| intros C; exfalso; lia].
    -
      rewrite (dblk2_slow X flush ltac:(lia)).
      destruct (slow_bf_spec FB_CALL_ok c0 X flush PRE M) as [SAFE POST].
      pose proof (slow_frames5 c0 X flush FB_CALL_ok PRE M WS HFL) as [ECF BD].
      split; [reflexivity|]. split; [exact POST|]. split; [exact ECF|]. split; [exact BD|].
      split; [intros C; exfalso; lia|]. split; [intros C; exfalso; lia| intros _; exact SAFE].
  Qed.

  Lemma deflate_blocks_unfold2 : forall X,
    deflate_blocks X flush =
      if blk_cond X flush then
        (let '(s, bstate) := run_compress_func X flush in
         let s := if block_state_eqb bstate finish_started || block_state_eqb bstate finish_done then set_status s FINISH_STATE else s in
         if block_state_eqb bstate need_more || block_state_eqb bstate finish_started then
           (if Z.eqb (cs_avail_out (ds_strm s)) 0 then set_last_flush s (-1) else s, Some Z_OK)
         else if block_state_eqb bstate block_done then
           (let s' := if Z.eqb flush Z_PARTIAL_FLUSH then tr_align s
                      else if negb (Z.eqb flush Z_BLOCK) then
                        let s := tr_stored_block s None 0 0 in
                        if Z.eqb flush Z_FULL_FLUSH then
                          let s := clear_hash s in
                          if Z.eqb (ds_lookahead s) 0 then set_insert (set_block_start (set_strstart s 0) 0) 0 else s
                        else s
                      else s in
            let s' := flush_pending s' in
            if Z.eqb (cs_avail_out (ds_strm s')) 0 then (set_last_flush s' (-1), Some Z_OK) else (s', None))
         else (s, None))
      else (X, None).
  Proof. intros X. reflexivity. Qed.

  Lemma P2g2_blocks : forall X, P2g2 X -> ds_pending X = 0 ->
    (ds_status X = FINISH_STATE -> cs_avail_in (ds_strm X) = 0) ->
    let r := deflate_blocks X flush in
    P2g2 (fst r) /\ (snd r = None -> ds_pending (fst r) = 0 /\ (flush = Z_FINISH -> ds_status (fst r) = FINISH_STATE)).
  Proof.
    intros X PP Hp Hfin. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    rewrite deflate_blocks_unfold2.
    destruct (blk_cond X flush) eqn:Hcond.
    2:{ cbn [fst snd]. split; [exact PP|]. intros _. split; [exact Hp|]. intros Hf.
        unfold blk_cond in Hcond. apply orb_false_iff in Hcond as [Hcond C3]. apply andb_false_iff in C3. destruct C3 as [C3|C3].
        - exfalso. rewrite Hf in C3. cbn in C3. discriminate C3.
        - destruct (Z.eqb_spec (ds_status X) FINISH_STATE); [assumption | discriminate C3]. }
    assert (Hst0 : ds_status X <> FINISH_STATE).
    { intros Ef. unfold blk_cond in Hcond. rewrite (Hfin Ef), (dx_fin _ XX Ef), Ef in Hcond. cbn in Hcond. rewrite andb_false_r in Hcond. discriminate Hcond. }
    clear Hcond.
    destruct (bf_g2 X PP Hp Hst0) as (ER & POST & ECF & BD & _). rewrite ER.
    revert POST ECF BD. generalize (dblk2 X flush). intros [s1 bst] POST ECF BD. cbn [fst snd] in POST, ECF, BD. cbv beta iota zeta.
    unfold BFPOST in POST. cbn [fst snd] in POST. destruct POST as (H1 & K1 & O1 & Pbd & Pfin & Pfd).
    assert (HS1 : ST s1) by (split; [exact H1 | rewrite K1; exact K]).
    pose proof (PATG2_CF _ _ ECF P) as P1.
    assert (Est1 : ds_status s1 = ds_status X) by exact (proj1 (proj2 (proj2 (proj2 (CF_fields _ _ ECF))))).
    assert (P1f : PATG2 (set_status s1 FINISH_STATE)) by (apply PATG2_finish; [exact P1| rewrite Est1; exact Hst0]).
    destruct bst; cbn [block_state_eqb orb]; cbv iota.
    -
      destruct (cs_avail_out (ds_strm s1) =? 0); cbn [fst snd].
      + split; [apply P2g2_slf; [exact (conj HS1 P1) | lia] | intros E; discriminate E].
      + split; [exact (conj HS1 P1) | intros E; discriminate E].
    -
      pose proof (BD eq_refl) as F5. rewrite F5. change (Z_BLOCK =? Z_PARTIAL_FLUSH) with false. change (negb (Z_BLOCK =? Z_BLOCK)) with false. cbv iota.
      destruct (P2g2_fp s1 (conj HS1 P1)) as [PPf Hor].
      destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending s1))) 0) as [Ea|Ea]; cbn [fst snd].
      + split; [apply P2g2_slf; [exact PPf | lia] | intros E; discriminate E].
      + split; [exact PPf|]. intros _. split; [destruct Hor as [X0|X0]; [exact X0 | contradiction]|].
        intros F4. exfalso. unfold Z_FINISH, Z_BLOCK in F4. discriminate F4.
    -
      destruct (DC_set_status c0 s1 FINISH_STATE H1 ltac:(unfold FINISH_STATE; lia) ltac:(intros; reflexivity)
                  ltac:(intros _; exact (Pfin (or_introl eq_refl)))) as (H2 & K2 & S2).
      assert (HS2 : ST (set_status s1 FINISH_STATE)) by (split; [exact H2 | rewrite K2, K1; exact K]).
      revert HS2 P1f. generalize (set_status s1 FINISH_STATE). intros s2 HS2 PP2.
      destruct (cs_avail_out (ds_strm s2) =? 0); cbn [fst snd].
      + split; [apply P2g2_slf; [exact (conj HS2 PP2) | lia] | intros E; discriminate E].
      + split; [exact (conj HS2 PP2) | intros E; discriminate E].
    -
      destruct (DC_set_status c0 s1 FINISH_STATE H1 ltac:(unfold FINISH_STATE; lia) ltac:(intros; reflexivity)
                  ltac:(intros _; exact (Pfin (or_intror eq_refl)))) as (H2 & K2 & S2).
      assert (HS2 : ST (set_status s1 FINISH_STATE)) by (split; [exact H2 | rewrite K2, K1; exact K]).
      assert (Pd2 : ds_pending (set_status s1 FINISH_STATE) = ds_pending s1) by reflexivity.
      assert (St2 : ds_status (set_status s1 FINISH_STATE) = FINISH_STATE) by reflexivity.
      revert HS2 P1f Pd2 St2. generalize (set_status s1 FINISH_STATE). intros s2 HS2 PP2 Pd2 St2.
      cbn [fst snd]. split; [exact (conj HS2 PP2)|]. intros _. split; [rewrite Pd2; exact (Pfd eq_refl) | intros _; exact St2].
  Qed.

  Lemma blocks_pathg2_ok : forall X, P2g2 X -> ds_pending X = 0 -> (ds_status X = FINISH_STATE -> cs_avail_in (ds_strm X) = 0) ->
    blocks_pathg2 inp flush (dc_blocks X flush) X.
  Proof.
    intros X PP Hp Hfin. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    destruct (P2g2_facts X PP) as (RAI & RAO & TIE & HSZ & WB & RLA & RSS & WS & LBS).
    assert (RST : 0 <= ds_status X < 1000) by (destruct (pg2_st _ P) as [E|[E|E]]; rewrite E; unfold INIT_STATE, BUSY_STATE, FINISH_STATE; lia).
    pose proof (P2g2_blocks X PP Hp Hfin) as PB. cbv zeta in PB.
    unfold blocks_pathg2, dc_blocks.
    rewrite deflate_blocks_unfold2 in PB |- *.
    destruct (blk_cond X flush) eqn:Hcond.
    2:{
        cbn [fst snd] in PB. destruct PB as [_ PB2]. destruct (PB2 eq_refl) as [_ Hf].
        pose proof (fin_pathg2_ok X PP Hp Hf) as FP.
        split; [exact (proj1 FP)|]. split; [exact RAI|]. split; [exact RLA|]. split; [exact RST|].
        split; [intros HH; discriminate HH| intros _; exact FP]. }
    assert (Hst0 : ds_status X <> FINISH_STATE).
    { intros Ef. unfold blk_cond in Hcond. rewrite (Hfin Ef), (dx_fin _ XX Ef), Ef in Hcond. cbn in Hcond. rewrite andb_false_r in Hcond. discriminate Hcond. }
    destruct (bf_g2 X PP Hp Hst0) as (ER & POST & ECF & BD & SAFE0 & SAFEF & SAFE4). rewrite ER in PB |- *.
    pose proof (PATG2_level X D P) as LV. pose proof (PATG2_strategy X P) as SG. pose proof (PATG2_wrap2 X P) as W2.
    revert POST ECF BD PB. generalize (dblk2 X flush). intros [s1 bst] POST ECF BD PB.
    cbn [fst snd] in POST, ECF, BD, PB |- *. cbv beta iota zeta in PB |- *.
    unfold BFPOST in POST. cbn [fst snd] in POST. destruct POST as (H1 & K1 & O1 & Pbd & Pfin & Pfd).
    assert (HS1 : ST s1) by (split; [exact H1 | rewrite K1; exact K]).
    pose proof (PATG2_CF _ _ ECF P) as P1. pose proof (fwT_of_CF _ _ ECF) as FT1.
    destruct (P2g2_facts s1 (conj HS1 P1)) as (_ & RAO1 & _ & _ & _ & _ & _ & _ & LBS1).
    split.
    {   apply (ole_step _ X s1 O1 FT1).
      destruct bst; cbn [block_state_eqb orb] in PB |- *; cbv iota in PB |- *.
      - apply ole_strm. destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity.
      - rewrite (BD eq_refl). change (Z_BLOCK =? Z_PARTIAL_FLUSH) with false. change (negb (Z_BLOCK =? Z_BLOCK)) with false. cbv iota.
        destruct (DC_flush_pending c0 s1 HC0w H1) as (_ & _ & O2 & _).
        apply (ole_step _ s1 (flush_pending s1) O2 (fwT_flush_pending s1)).
        apply ole_strm. destruct (cs_avail_out (ds_strm (flush_pending s1)) =? 0); cbn [fst]; [apply strm_set_last_flush|].
        unfold dc_fin. change (negb (Z_BLOCK =? Z_FINISH)) with true. reflexivity.
      - apply ole_strm. rewrite strm_set_status. destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity.
      - cbn [fst snd] in PB. destruct PB as [PP2 PB2]. destruct (PB2 eq_refl) as [Hp2 Hf2].
        exact (ole_step _ s1 (set_status s1 FINISH_STATE) (OUTLE_strm _ _ eq_refl) eq_refl (proj1 (fin_pathg2_ok _ PP2 Hp2 Hf2))). }
    split; [exact RAI|]. split; [exact RLA|]. split; [exact RST|].
    split; [|intros HH; discriminate HH]. intros _.
    split; [exact LV|]. split; [exact SG|]. split; [exact TIE|].
    split; [exact WS|]. split; [exact HSZ|]. split; [exact LBS|].
    split; [destruct (pg2_wrap _ P) as [W|[_ Fw]]; [exact W| contradiction (Hst0 Fw)]|]. split; [exact RAO|].
    split; [exact SAFE0|]. split; [exact SAFEF|]. split; [exact SAFE4|].
    destruct bst; cbn [block_state_eqb orb] in PB |- *; cbv iota in PB |- *.
    -
      split; [apply ole_strm; destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity|].
      split; [exact RAO1|].
      split; [intros _ E; rewrite E; reflexivity|].
      split; [intros _ E; replace (cs_avail_out (ds_strm s1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact E); reflexivity|].
      split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. intros E; discriminate E.
    -
      pose proof (BD eq_refl) as F5. rewrite F5. change (Z_BLOCK =? Z_PARTIAL_FLUSH) with false. change (negb (Z_BLOCK =? Z_BLOCK)) with false. cbv iota.
      unfold dc_fin. change (negb (Z_BLOCK =? Z_FINISH)) with true. cbv iota.
      destruct (DC_flush_pending c0 s1 HC0w H1) as (_ & _ & O2 & _).
      destruct (ST_flush_pending c0 s0 HC0 s1 HS1) as (HSf & FPOK & _).
      pose proof (PATG2_CF _ _ (CF_flush_pending s1) P1) as Pf.
      destruct (P2g2_facts (flush_pending s1) (conj HSf Pf)) as (_ & RAOf & _).
      pose proof (df_wrap _ (proj1 (proj1 (proj1 HSf)))) as RWf. pose proof (PATG2_wrap2 _ Pf) as W2f.
      split.
      { apply (ole_step _ s1 (flush_pending s1) O2 (fwT_flush_pending s1)). apply ole_strm.
        destruct (cs_avail_out (ds_strm (flush_pending s1)) =? 0); cbn [fst]; [apply strm_set_last_flush| reflexivity]. }
      split; [exact RAO1|].
      split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. split; [intros E; discriminate E|].
      split; [intros E; discriminate E|].
      intros _. split; [reflexivity|]. split; [exact FPOK|]. split; [exact LBS1|].
      revert RAOf RWf W2f. generalize (flush_pending s1). intros s2 RAOf RWf W2f.
      split; [apply ole_strm; destruct (cs_avail_out (ds_strm s2) =? 0); cbn [fst]; [apply strm_set_last_flush| reflexivity]|].
      split; [exact RAOf|].
      split; [intros E; rewrite E; reflexivity|].
      intros E. replace (cs_avail_out (ds_strm s2) =? 0) with false by (symmetry; apply Z.eqb_neq; exact E). cbn [fst].
      unfold fin_path. split; [apply ole_strm; reflexivity|]. split; [exact RWf|]. split; [exact W2f|].
      split; [intros _; reflexivity|]. split; [intros F4; discriminate F4|]. intros F4; discriminate F4.
    -
      rewrite ?strm_set_status. split; [apply ole_strm; destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity|].
      split; [exact RAO1|].
      split; [intros E; discriminate E|]. split; [intros E; discriminate E|].
      split; [intros _ E; rewrite E; reflexivity|].
      split; [intros _ E; replace (cs_avail_out (ds_strm s1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact E); reflexivity|].
      split; [intros E; discriminate E|]. intros E; discriminate E.
    -
      cbn [fst snd] in PB. destruct PB as [PP2 PB2]. destruct (PB2 eq_refl) as [Hp2 Hf2].
      pose proof (fin_pathg2_ok _ PP2 Hp2 Hf2) as FP.
      rewrite ?strm_set_status. split; [exact (ole_step _ s1 (set_status s1 FINISH_STATE) (OUTLE_strm _ _ eq_refl) eq_refl (proj1 FP))|].
      split; [exact RAO1|].
      split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. split; [intros E; discriminate E|].
      split; [intros _; exact FP|]. intros E; discriminate E.
  Qed.

  Lemma dc_hdr_skip2 : forall X, ds_status X <> INIT_STATE -> ds_status X <> GZIP_STATE -> dc_hdr X flush = dc_blocks X flush.
  Proof.
    intros X E1 E2. unfold dc_hdr, dc_gz.
    replace (ds_status X =? INIT_STATE) with false by (symmetry; apply Z.eqb_neq; exact E1).
    replace (ds_status X =? GZIP_STATE) with false by (symmetry; apply Z.eqb_neq; exact E2). reflexivity.
  Qed.

  Lemma body_pathg2_ok : forall X, P2g2 X -> ds_pending X = 0 -> body_pathg2 inp flush (dc_body X flush) X.
  Proof.
    intros X PP Hp. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    destruct (P2g2_facts X PP) as (RAI & RAO & TIE & HSZ & WB & RLA & RSS & WS & LBS).
    assert (HST : ds_status X = 42 \/ ds_status X = 113 \/ ds_status X = 666) by exact (pg2_st _ P).
    assert (E4 : ((ds_status X =? INIT_STATE) && (ds_wrap X =? 0)) = false).
    { destruct (Z.eqb_spec (ds_status X) INIT_STATE) as [E|E]; [| reflexivity].
      destruct (pg2_wrap _ P) as [W|[_ F]]; [rewrite W; reflexivity | rewrite E in F; discriminate F]. }
    unfold body_pathg2, dc_body. rewrite E4.
    destruct (Z.eq_dec (ds_status X) 666) as [E6|N6].
    -
      destruct (Z.eq_dec (cs_avail_in (ds_strm X)) 0) as [A0|AN].
      + replace ((ds_status X =? FINISH_STATE) && negb (cs_avail_in (ds_strm X) =? 0)) with false
          by (rewrite A0; cbn; rewrite andb_false_r; reflexivity).
        rewrite (dc_hdr_skip2 X ltac:(rewrite E6; discriminate) ltac:(rewrite E6; discriminate)).
        pose proof (blocks_pathg2_ok X PP Hp (fun _ => A0)) as BP.
        split; [exact (proj1 BP)|]. split; [exact HST|]. split; [exact RAI|].
        split; [intros _ C; contradiction|]. split; [intros _ _; exact BP|].
        split; [intros C; rewrite E6 in C; discriminate C|]. intros C; rewrite E6 in C; discriminate C.
      + replace ((ds_status X =? FINISH_STATE) && negb (cs_avail_in (ds_strm X) =? 0)) with true
          by (rewrite E6; replace (cs_avail_in (ds_strm X) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AN); reflexivity).
        split; [apply (ole_err X Z_BUF_ERROR Z_BUF_ERROR)|]. split; [exact HST|]. split; [exact RAI|].
        split; [intros _ _; reflexivity|]. split; [intros _ C; contradiction|].
        split; [intros C; rewrite E6 in C; discriminate C|]. intros C; rewrite E6 in C; discriminate C.
    - replace ((ds_status X =? FINISH_STATE) && negb (cs_avail_in (ds_strm X) =? 0)) with false
        by (replace (ds_status X =? FINISH_STATE) with false by (symmetry; apply Z.eqb_neq; exact N6); reflexivity).
      destruct (Z.eq_dec (ds_status X) 113) as [E1|N1].
      + rewrite (dc_hdr_skip2 X ltac:(rewrite E1; discriminate) ltac:(rewrite E1; discriminate)).
        pose proof (blocks_pathg2_ok X PP Hp (fun C => False_ind _ (N6 C))) as BP.
        split; [exact (proj1 BP)|]. split; [exact HST|]. split; [exact RAI|].
        split; [intros C; contradiction|]. split; [intros C; contradiction|].
        split; [intros _; exact BP|]. intros C; rewrite E1 in C; discriminate C.
      +
        assert (E : ds_status X = INIT_STATE) by (unfold INIT_STATE; lia).
        destruct (hdr_zlib c0 s0 HC0 Hs0 D0 X HS Hp E) as (HOK & HSz & Stz & Horz & Aiz & Lkz & Wrz).
        destruct (zhdr_facts c0 X H Hp E) as ((H1 & _ & _) & K1 & O1 & _).
        destruct (DC_flush_pending c0 (zhdr_st X) HC0w H1) as (_ & _ & O2 & _).
        assert (Pz : PATG2 (flush_pending (zhdr_st X))).
        { apply (PATG2_CF _ _ (CF_flush_pending (zhdr_st X))). destruct (PF_zhdr_pre X) as (t & Et & Pt). rewrite Et.
          apply PATG2_busy; [exact (PATG2_PF _ _ Pt P)|].
          pose proof (PF_fields _ _ Pt) as (_ & _ & (Est & _) & _). rewrite Est. exact E. }
        destruct HOK as (_ & _ & _ & FPOK & HOK2). cbv zeta in HOK2. destruct HOK2 as (_ & RP5 & _).
        assert (W1 : ds_wrap X = 1) by (destruct (pg2_wrap _ P) as [W|[_ F]]; [exact W| rewrite E in F; discriminate F]).
        pose proof (sv_adler _ _ V) as RAD. pose proof (df_level _ D) as RLV. pose proof (PATG2_strategy X P) as RSG.
        unfold dc_hdr. replace (ds_status X =? INIT_STATE) with true by (symmetry; apply Z.eqb_eq; exact E).
        rewrite deflate_zlib_header_eq. cbv zeta.
        assert (BPK : ds_pending (flush_pending (zhdr_st X)) = 0 -> blocks_pathg2 inp flush (dc_blocks (flush_pending (zhdr_st X)) flush) (flush_pending (zhdr_st X))).
        { intros P0. apply (blocks_pathg2_ok _ (conj HSz Pz) P0). intros C. rewrite Stz in C. discriminate C. }
        assert (EGZ : dc_gz (flush_pending (zhdr_st X)) flush = dc_blocks (flush_pending (zhdr_st X)) flush).
        { unfold dc_gz. rewrite Stz. reflexivity. }
        assert (FW5 : fwT (flush_pending (zhdr_st X)) = fwT X) by (rewrite fwT_flush_pending; apply fwT_zhdr_g).
        revert O2 Stz RP5 BPK EGZ FPOK FW5. generalize (flush_pending (zhdr_st X)). intros X5 O2 Stz RP5 BPK EGZ FPOK FW5.
        assert (OL5 : ole (if negb (ds_pending X5 =? 0) then (set_last_flush X5 (-1), Z_OK) else dc_blocks X5 flush) X5).
        { destruct (Z.eqb_spec (ds_pending X5) 0) as [P0|PN]; cbn [negb].
          - exact (proj1 (BPK P0)).
          - apply ole_strm. reflexivity. }
        assert (ER : (let '(s, r) := if negb (ds_pending X5 =? 0) then (set_last_flush X5 (-1), Some Z_OK) else (X5, None) in
                      match r with Some rc => (s, rc) | None => dc_gz s flush end)
                     = (if negb (ds_pending X5 =? 0) then (set_last_flush X5 (-1), Z_OK) else dc_blocks X5 flush)).
        { destruct (negb (ds_pending X5 =? 0)); [reflexivity| exact EGZ]. }
        rewrite ER.
        split; [exact (ole_step _ X X5 (OUTLE_trans _ _ _ O1 O2) FW5 OL5)|].
        split; [exact HST|]. split; [exact RAI|].
        split; [intros C; contradiction|]. split; [intros C; contradiction|]. split; [intros C; contradiction|].
        intros _.
        split; [exact W1|]. split; [exact WB|]. split; [exact RLV|]. split; [exact RSG|]. split; [exact RSS|].
        split; [lia|]. split; [lia|]. split; [exact LBS|]. split; [exact RAD|]. split; [exact RAO|]. split; [exact FPOK|].
        split; [exact Stz|]. split; [exact RP5|]. split; [exact OL5|].
        split.
        * intros PN. replace (ds_pending X5 =? 0) with false by (symmetry; apply Z.eqb_neq; exact PN). reflexivity.
        * intros P0. rewrite P0. cbn [negb Z.eqb]. exact (BPK P0).
  Qed.

  Theorem defl_pathg2_ok : P2g2 s0 -> defl_pathg2 inp flush (deflate_core s0 flush) s0.
  Proof.
    intros PP. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    destruct (P2g2_facts s0 PP) as (RAI & RAO & TIE & HSZ & WB & RLA & RSS & WS & LBS).
    pose proof Hfl5b as Hfl.
    pose proof (sv_nin _ _ V) as N1. pose proof (sv_inlen _ _ V) as N2. rewrite HIN, arr_len_of_list in N2. unfold zlength in N2.
    pose proof (df_lf _ D) as RLF. pose proof (df_pend _ D) as (Pd1 & Pd2 & Pd3). rewrite LBS in Pd3.
    unfold defl_pathg2. cbv zeta. rewrite deflate_core_eq.
    replace (deflateStateCheck s0 || (Z_BLOCK <? flush) || (flush <? 0)) with false
      by (rewrite (df_status _ D); destruct HFL as [-> | [-> | ->]]; reflexivity).
    match goal with |- _ /\ ?T => assert (REST : T) end.
    2:{ split; [|exact REST]. destruct REST as (_ & _ & _ & PERR & POK).
        destruct (Z.eq_dec (ds_status s0) 666) as [E6|N6]; [destruct (Z.eq_dec flush 4) as [F4|F4]|].
        2:{ rewrite (PERR (conj E6 F4)). apply ole_err. }
        all: (assert (NE : ~ (ds_status s0 = 666 /\ flush <> 4)) by (intros [C1 C2]; first [exact (C2 F4)| exact (N6 C1)]));
             destruct (POK NE) as (_ & _ & _ & _ & EBUF & PGO);
             (destruct (Z.eq_dec (cs_avail_out (ds_strm s0)) 0) as [A0|AN]; [rewrite (EBUF A0); apply ole_err|]);
             destruct (PGO AN) as [PG1 PG2];
             (destruct (Z.eq_dec (ds_pending s0) 0) as [P0|PN];
              [ destruct (PG2 P0) as [RK1 RK2];
                destruct ((cs_avail_in (ds_strm s0) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)) eqn:ERK;
                [ assert (RK : rank_err s0 flush)
                    by (apply andb_true_iff in ERK as [ERK E3]; apply andb_true_iff in ERK as [E1 E2];
                        split; [apply Z.eqb_eq; exact E1|]; split; [apply Z.leb_le; exact E2|]; intros F; rewrite F in E3; discriminate E3);
                  rewrite (RK1 RK); exact (ole_step _ s0 (set_last_flush s0 flush) (OUTLE_strm _ _ eq_refl) eq_refl (ole_err _ _ _))
                | assert (NRK : ~ rank_err s0 flush)
                    by (intros (R1 & R2 & R3); apply andb_false_iff in ERK; destruct ERK as [ERK|E3];
                        [ apply andb_false_iff in ERK; destruct ERK as [E1|E2]; [apply Z.eqb_neq in E1; contradiction| apply Z.leb_gt in E2; lia]
                        | destruct (Z.eqb_spec flush Z_FINISH) as [F|F]; [contradiction| discriminate E3] ]);
                  exact (ole_step _ s0 (set_last_flush s0 flush) (OUTLE_strm _ _ eq_refl) eq_refl (proj1 (RK2 NRK))) ]
              | pose proof (PG1 PN) as PG; cbv zeta in PG; destruct PG as (_ & _ & OL2 & _);
                destruct (DC_flush_pending c0 (set_last_flush s0 flush) HC0w (proj1 (proj1 (P2g2_slf s0 flush PP ltac:(lia))))) as (_ & _ & O2 & _);
                exact (ole_step _ s0 (flush_pending (set_last_flush s0 flush)) (OUTLE_trans _ _ _ (OUTLE_strm _ _ eq_refl) O2)
                         (eq_trans (fwT_flush_pending _) eq_refl) OL2) ]). }
    split; [exact (pg2_st _ P)|]. split; [exact RAI|]. split; [lia|].
    split.
    { intros [E6 F4]. replace ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)) with true; [reflexivity|].
      rewrite E6. destruct (Z.eqb_spec flush Z_FINISH) as [F|F]; [exfalso; exact (F4 F)| reflexivity]. }
    intros NE.
    replace ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)) with false.
    2:{ symmetry. apply andb_false_iff. destruct (Z.eqb_spec (ds_status s0) FINISH_STATE) as [E|E]; [right|left; reflexivity].
        destruct (Z.eqb_spec flush Z_FINISH) as [F|F]; [reflexivity|]. exfalso. apply NE. split; [exact E| exact F]. }
    split; [exact RAO|]. split; [exact RLF|]. split; [lia|]. split; [exact LBS|].
    split.
    { intros A0. rewrite A0. reflexivity. }
    intros AN. replace (cs_avail_out (ds_strm s0) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AN).
    pose proof (P2g2_slf s0 flush PP ltac:(lia)) as PP1.
    unfold dc_pend. cbv zeta.
    change (ds_pending (set_last_flush s0 flush)) with (ds_pending s0).
    change (cs_avail_in (ds_strm (set_last_flush s0 flush))) with (cs_avail_in (ds_strm s0)).
    split.
    -
      intros PN. replace (ds_pending s0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact PN). cbn [negb].
      destruct (P2g2_fp _ PP1) as [PPf Hor].
      destruct (ST_flush_pending c0 s0 HC0 _ (proj1 PP1)) as (_ & FPOK & _).
      assert (RST2 : 0 <= ds_status (flush_pending (set_last_flush s0 flush)) < 1000)
        by (destruct (pg2_st _ (proj2 PPf)) as [E|[E|E]]; rewrite E; unfold INIT_STATE, BUSY_STATE, FINISH_STATE; lia).
      assert (BPK : cs_avail_out (ds_strm (flush_pending (set_last_flush s0 flush))) <> 0 ->
                    body_pathg2 inp flush (dc_body (flush_pending (set_last_flush s0 flush)) flush) (flush_pending (set_last_flush s0 flush))).
      { intros A2. apply (body_pathg2_ok _ PPf). destruct Hor as [X0|X0]; [exact X0| contradiction]. }
      revert RST2 BPK. generalize (flush_pending (set_last_flush s0 flush)). intros s2 RST2 BPK.
      split; [exact FPOK|]. split; [exact RST2|].
      destruct (Z.eqb_spec (cs_avail_out (ds_strm s2)) 0) as [A2|A2].
      + split; [apply ole_strm; reflexivity|].
        split; [intros _; reflexivity| intros C; contradiction].
      + split; [exact (proj1 (BPK A2))|]. split; [intros C; contradiction| intros _; exact (BPK A2)].
    -
      intros P0. rewrite P0. cbn [Z.eqb negb].
      destruct ((cs_avail_in (ds_strm s0) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)) eqn:ERK.
      + split; [intros _; reflexivity|]. intros NR. exfalso. apply NR.
        apply andb_true_iff in ERK as [ERK E3]. apply andb_true_iff in ERK as [E1 E2].
        split; [apply Z.eqb_eq; exact E1|]. split; [apply Z.leb_le; exact E2|].
        intros F. rewrite F in E3. discriminate E3.
      + split.
        * intros (R1 & R2 & R3). exfalso.
          apply andb_false_iff in ERK. destruct ERK as [ERK|E3].
          -- apply andb_false_iff in ERK. destruct ERK as [E1|E2]; [apply Z.eqb_neq in E1; contradiction| apply Z.leb_gt in E2; lia].
          -- destruct (Z.eqb_spec flush Z_FINISH) as [F|F]; [contradiction| discriminate E3].
        * intros _. apply (body_pathg2_ok _ PP1). exact P0.
  Qed.

  Theorem patg2_core : P2g2 s0 -> P2g2 (fst (deflate_core s0 flush)).
  Proof.
    intros PP0. pose proof PP0 as [HS0 P0]. pose proof Hfl5b as Hfl.
    unfold deflate_core.
    destruct (deflateStateCheck s0 || (Z_BLOCK <? flush) || (flush <? 0)); [cbn [fst]; exact PP0|].
    destruct ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)); [apply P2g2_err; exact PP0|].
    destruct (cs_avail_out (ds_strm s0) =? 0); [apply P2g2_err; exact PP0|].
    cbv zeta.
    pose proof (P2g2_slf s0 flush PP0 ltac:(lia)) as PP1.
    assert (Pd1 : ds_pending (set_last_flush s0 flush) = ds_pending s0) by reflexivity.
    revert PP1 Pd1. generalize (set_last_flush s0 flush). intros s1 PP1 Pd1.
    match goal with |- P2g2 (fst (let '(s, r) := ?head in _)) => destruct head as [s2 r2] eqn:Ehead end.
    assert (H2 : P2g2 s2 /\ (r2 = None -> ds_pending s2 = 0)).
    { destruct (negb (ds_pending s1 =? 0)) eqn:Ep.
      - destruct (P2g2_fp s1 PP1) as [PPf Hor].
        destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending s1))) 0) as [Ea|Ea]; inversion Ehead; subst s2 r2.
        + split; [apply P2g2_slf; [exact PPf | lia] | intros HH; discriminate HH].
        + split; [exact PPf | intros _; destruct Hor as [X0|X0]; [exact X0 | contradiction]].
      - destruct ((cs_avail_in (ds_strm s1) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)).
        + unfold err_return in Ehead. inversion Ehead; subst s2 r2. split; [exact (P2g2_err s1 Z_BUF_ERROR PP1) | intros HH; discriminate HH].
        + inversion Ehead; subst s2 r2. split; [exact PP1|]. intros _. destruct (Z.eqb_spec (ds_pending s1) 0); [assumption | discriminate Ep]. }
    clear Ehead. destruct H2 as [PP2 Hp2].
    destruct r2 as [rc|]; [cbn [fst]; exact PP2|]. specialize (Hp2 eq_refl).
    destruct ((ds_status s2 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s2) =? 0)) eqn:Efa; [apply P2g2_err; exact PP2|].
    pose proof PP2 as [HS2 P2'].
    assert (E4 : ((ds_status s2 =? INIT_STATE) && (ds_wrap s2 =? 0)) = false).
    { destruct (Z.eqb_spec (ds_status s2) INIT_STATE) as [E|E]; [| reflexivity].
      destruct (pg2_wrap _ P2') as [W|[_ F]]; [rewrite W; reflexivity | rewrite E in F; discriminate F]. }
    rewrite E4.
    rewrite deflate_zlib_header_eq.
    match goal with |- P2g2 (fst (let '(s, r) := ?head in _)) => destruct head as [s5 r5] eqn:Ehead end.
    assert (H5 : P2g2 s5 /\ (r5 = None -> ds_pending s5 = 0 /\ cs_avail_in (ds_strm s5) = cs_avail_in (ds_strm s2)
                                        /\ (ds_status s5 = FINISH_STATE -> ds_status s2 = FINISH_STATE))).
    { destruct (Z.eqb_spec (ds_status s2) INIT_STATE) as [E|E].
      - destruct (hdr_zlib c0 s0 HC0 Hs0 D0 s2 HS2 Hp2 E) as (_ & HSz & Stz & Horz & Aiz & _).
        assert (Pz : PATG2 (flush_pending (zhdr_st s2))).
        { apply (PATG2_CF _ _ (CF_flush_pending (zhdr_st s2))). destruct (PF_zhdr_pre s2) as (t & Et & Pt). rewrite Et.
          apply PATG2_busy; [exact (PATG2_PF _ _ Pt P2')|].
          pose proof (PF_fields _ _ Pt) as (_ & _ & (Est & _) & _). rewrite Est. exact E. }
        cbv zeta in Ehead. destruct (negb (ds_pending (flush_pending (zhdr_st s2)) =? 0)) eqn:Ep; inversion Ehead; subst s5 r5.
        + split; [apply P2g2_slf; [exact (conj HSz Pz) | lia] | intros HH; discriminate HH].
        + split; [exact (conj HSz Pz)|]. intros _. rewrite Aiz, Stz.
          split; [destruct (Z.eqb_spec (ds_pending (flush_pending (zhdr_st s2))) 0); [assumption | discriminate Ep]|].
          split; [reflexivity | unfold BUSY_STATE, FINISH_STATE; intros; lia].
      - inversion Ehead; subst s5 r5. split; [exact PP2|]. intros _. split; [exact Hp2|]. split; [reflexivity | intros X; exact X]. }
    clear Ehead. destruct H5 as [PP5 Hr5].
    destruct r5 as [rc|]; [cbn [fst]; exact PP5|]. destruct (Hr5 eq_refl) as (Hp5 & Ai5 & Fin5).
    assert (E6 : (ds_status s5 =? GZIP_STATE) = false).
    { destruct (pg2_st _ (proj2 PP5)) as [E|[E|E]]; rewrite E; reflexivity. }
    rewrite E6.
    assert (Hfin5 : ds_status s5 = FINISH_STATE -> cs_avail_in (ds_strm s5) = 0).
    { intros E. rewrite Ai5. pose proof (Fin5 E) as E2. rewrite E2 in Efa. cbn in Efa.
      destruct (Z.eqb_spec (cs_avail_in (ds_strm s2)) 0); [assumption | discriminate Efa]. }
    destruct (P2g2_blocks s5 PP5 Hp5 Hfin5) as [PP7 Hr7]. cbv zeta in PP7, Hr7.
    destruct (deflate_blocks s5 flush) as [s7 r7]. cbn [fst snd] in PP7, Hr7.
    destruct r7 as [rc|]; [cbn [fst]; exact PP7|]. destruct (Hr7 eq_refl) as [Hp7 Hfin7].
    destruct (negb (flush =? Z_FINISH)) eqn:Ef; [cbn [fst]; exact PP7|].
    assert (Hf : flush = Z_FINISH) by (destruct (Z.eqb_spec flush Z_FINISH); [assumption | discriminate Ef]).
    destruct (Z.leb_spec (ds_wrap s7) 0) as [Hw|Hw]; [cbn [fst]; exact PP7|].

    destruct PP7 as [HS7 P7].
    pose proof (proj2 (finish_stage c0 s0 HC0 Hs0 D0 s7 flush HS7 Hp7 Hfl Hfin7) Hf Hw) as HT.
    revert HT. rewrite deflate_trailer_eq. cbv zeta.
    assert (Pt : PATG2 (flush_pending (trailer_st s7))) by (apply (PATG2_CF _ _ (CF_flush_pending (trailer_st s7))); exact (PATG2_PF _ _ (PF_trailer s7) P7)).
    assert (St : ds_status (flush_pending (trailer_st s7)) = FINISH_STATE).
    { pose proof (PF_fields _ _ (PF_flush_pending (trailer_st s7))) as (_ & _ & (E1 & _) & _).
      pose proof (PF_fields _ _ (PF_trailer s7)) as (_ & _ & (E2 & _) & _). rewrite E1, E2. exact (Hfin7 Hf). }
    assert (Wt : ds_wrap (flush_pending (trailer_st s7)) = 1).
    { destruct (pg2_wrap _ Pt) as [W|[W _]]; [exact W|].
      pose proof (PF_fields _ _ (PF_flush_pending (trailer_st s7))) as (_ & (_ & _ & _ & _ & _ & _ & _ & E1) & _).
      pose proof (PF_fields _ _ (PF_trailer s7)) as (_ & (_ & _ & _ & _ & _ & _ & _ & E2) & _). rewrite E1, E2 in W. lia. }
    revert Pt St Wt. generalize (flush_pending (trailer_st s7)). intros s8 Pt St Wt.
    rewrite Wt. change (0 <? 1) with true. cbv iota. change (Z.opp 1) with (-1). cbn [fst]. intros HT.
    split; [exact HT | exact (PATG2_wrapneg s8 Pt St)].
  Qed.
End PathProofG2.

Section Api2.
  Variables (ds : deflate_state) (zc : ZCall) (flush : Z).
  Hypothesis HDD : DD ds.
  Hypothesis Hzc : dcall_wf zc.
  Hypothesis P : PATG2 ds.
  Hypothesis HWS : ds_w_size ds = 32768.
  Hypothesis HHS : ds_hash_size ds = 32768.
  Hypothesis HLBS : ds_lit_bufsize ds = 16384.
  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK.
  Hypothesis HIL : zlength (zc_input zc) < 2^31.
  Hypothesis HAO : zc_avail_out zc < 2^31.

  Let c0 := cstrm_of_call zc.
  Let d0 := set_strm ds c0.

  Lemma api2_HC0 : C0OK' c0. Proof. exact (C0OK'_of_call zc Hzc). Qed.
  Lemma api2_DC0 : DC c0 d0. Proof. split; [apply DD_set_strm; exact HDD | subst d0 c0; apply SV_entry; exact Hzc]. Qed.
  Lemma api2_P2g : P2g2 c0 d0 d0. Proof. split; [split; [exact api2_DC0| reflexivity]| exact (PATG2_set_strm ds c0 P)]. Qed.

  Theorem defl_pathg2_intro : defl_pathg2 (zc_input zc) flush (deflate_core d0 flush) d0.
  Proof.
    destruct Hzc as (_ & _ & _ & HB).
    apply (defl_pathg2_ok (zc_input zc) flush c0 d0 api2_HC0 eq_refl (proj1 (proj1 api2_DC0)) HFL).
    - exact HAO. - reflexivity. - exact HIL. - exact HB. - exact HWS. - exact HHS. - exact HLBS. - exact api2_P2g.
  Qed.

  Theorem deflate_core_P2g2 : PATG2 (fst (deflate_core d0 flush)) /\ RefDeflSafeI4.ST c0 d0 (fst (deflate_core d0 flush)).
  Proof.
    destruct Hzc as (_ & _ & _ & HB).
    destruct (patg2_core (zc_input zc) flush c0 d0 api2_HC0 eq_refl (proj1 (proj1 api2_DC0)) HFL HAO eq_refl HIL HB HWS HHS HLBS api2_P2g) as [A B].
    split; [exact B| exact A].
  Qed.
End Api2.

