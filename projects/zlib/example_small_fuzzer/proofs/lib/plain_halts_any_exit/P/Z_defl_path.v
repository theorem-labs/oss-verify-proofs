(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateOverlay OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel RefDeflSafeG RefDeflSafeFB RefDeflSafeLF RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeI1 RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeI6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require BoundSlow.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require BoundSlow BoundCore BoundPat.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundSlow.BoundFw OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundSlow OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundCore OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.BoundPat.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_defl_iface Z_defl_model.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition dc_fin (s : deflate_state) (flush : Z) : deflate_state * Z :=
  if negb (Z.eqb flush Z_FINISH) then (s, Z_OK)
  else if Z.leb (ds_wrap s) 0 then (s, Z_STREAM_END)
  else deflate_trailer s.

Definition dc_blocks (s : deflate_state) (flush : Z) : deflate_state * Z :=
  let '(s, r) := deflate_blocks s flush in
  match r with Some rc => (s, rc) | None => dc_fin s flush end.

Definition dc_gz (s : deflate_state) (flush : Z) : deflate_state * Z :=
  let '(s, r) := if Z.eqb (ds_status s) GZIP_STATE then deflate_gzip_header s else (s, None) in
  match r with Some rc => (s, rc) | None => dc_blocks s flush end.

Definition dc_hdr (s : deflate_state) (flush : Z) : deflate_state * Z :=
  let '(s, r) := if Z.eqb (ds_status s) INIT_STATE then deflate_zlib_header s else (s, None) in
  match r with Some rc => (s, rc) | None => dc_gz s flush end.

Definition dc_body (s : deflate_state) (flush : Z) : deflate_state * Z :=
  if Z.eqb (ds_status s) FINISH_STATE && negb (Z.eqb (cs_avail_in (ds_strm s)) 0) then err_return s Z_BUF_ERROR
  else dc_hdr (if Z.eqb (ds_status s) INIT_STATE && Z.eqb (ds_wrap s) 0 then set_status s BUSY_STATE else s) flush.

Definition dc_pend (s : deflate_state) (flush : Z) : deflate_state * option Z :=
  let s1 := set_last_flush s flush in
  if negb (Z.eqb (ds_pending s1) 0) then
    let s2 := flush_pending s1 in
    if Z.eqb (cs_avail_out (ds_strm s2)) 0 then (set_last_flush s2 (-1), Some Z_OK) else (s2, None)
  else if Z.eqb (cs_avail_in (ds_strm s1)) 0 && Z.leb (RANK flush) (RANK (ds_last_flush s)) && negb (Z.eqb flush Z_FINISH)
  then let '(s, rc) := err_return s1 Z_BUF_ERROR in (s, Some rc)
  else (s1, None).

Lemma deflate_core_eq : forall s flush,
  deflate_core s flush =
  if deflateStateCheck s || Z.ltb Z_BLOCK flush || Z.ltb flush 0 then (s, Z_STREAM_ERROR)
  else if Z.eqb (ds_status s) FINISH_STATE && negb (Z.eqb flush Z_FINISH) then err_return s Z_STREAM_ERROR
  else if Z.eqb (cs_avail_out (ds_strm s)) 0 then err_return s Z_BUF_ERROR
  else let '(s2, r) := dc_pend s flush in
       match r with Some rc => (s2, rc) | None => dc_body s2 flush end.
Proof. intros s flush. reflexivity. Qed.


Definition blk_cond (X : deflate_state) (flush : Z) : bool :=
  negb (Z.eqb (cs_avail_in (ds_strm X)) 0) || negb (Z.eqb (ds_lookahead X) 0)
  || (negb (Z.eqb flush Z_NO_FLUSH) && negb (Z.eqb (ds_status X) FINISH_STATE)).

Section PathDefs.
  Variables (inp : list Z) (flush : Z) (R : deflate_state * Z).

  Definition ole (X : deflate_state) : Prop :=
    (length (cs_out_rev (ds_strm X)) <= length (cs_out_rev (ds_strm (fst R))))%nat /\ fwT (fst R) = fwT X.

  Definition fin_path (X : deflate_state) : Prop :=
    ole X /\ - 2 <= ds_wrap X <= 2 /\ ds_wrap X <> 2
    /\ (flush <> 4 -> R = (X, 0))
    /\ (flush = 4 -> ds_wrap X <= 0 -> R = (X, 1))
    /\ (flush = 4 -> 0 < ds_wrap X ->
        let s2 := flush_pending (put_adler X) in
        0 <= ds_pending X /\ ds_pending X + 4 <= 65536 /\ 0 <= cs_adler (ds_strm X) < 2^64 /\ ds_lit_bufsize X = 16384
        /\ 0 <= cs_avail_out (ds_strm X) < 2^31 /\ fp_ok (put_adler X)
        /\ ds_wrap s2 = ds_wrap X /\ 0 <= ds_pending s2 < 2^64 /\ ole s2
        /\ (ds_pending s2 = 0 -> R = (set_wrap s2 (- ds_wrap s2), 1))
        /\ (ds_pending s2 <> 0 -> R = (set_wrap s2 (- ds_wrap s2), 0))).

  Definition blocks_path (X : deflate_state) : Prop :=
    ole X /\ 0 <= cs_avail_in (ds_strm X) <= 1 /\ 0 <= ds_lookahead X < 2^31 /\ 0 <= ds_status X < 1000
    /\ (blk_cond X flush = true ->
        ds_level X = 6 /\ ds_strategy X = 0 /\ din_tie inp X /\ slow_safe X flush
        /\ ds_w_size X = 32768 /\ ds_hash_size X = 32768 /\ ds_lit_bufsize X = 16384 /\ ds_insert X = 0 /\ ds_wrap X = 1  (* was <> 2; the blocks need wrap <> 0 and a range *)
        /\ 0 <= cs_avail_out (ds_strm X) < 2^31
        /\ snd (deflate_slow X flush) <> block_done /\ 0 <= cs_avail_out (ds_strm (blk_s2 X flush)) < 2^31
        /\ ole (fst (deflate_slow X flush))
        /\ (snd (deflate_slow X flush) = need_more \/ snd (deflate_slow X flush) = finish_started ->
            cs_avail_out (ds_strm (blk_s2 X flush)) = 0 -> R = (set_last_flush (blk_s2 X flush) (-1), 0))
        /\ (snd (deflate_slow X flush) = need_more \/ snd (deflate_slow X flush) = finish_started ->
            cs_avail_out (ds_strm (blk_s2 X flush)) <> 0 -> R = (blk_s2 X flush, 0))
        /\ (snd (deflate_slow X flush) = finish_done -> fin_path (blk_s2 X flush)))
    /\ (blk_cond X flush = false -> fin_path X).

  Definition body_path (X : deflate_state) : Prop :=
    ole X /\ (ds_status X = 42 \/ ds_status X = 113 \/ ds_status X = 666) /\ 0 <= cs_avail_in (ds_strm X) <= 1
    /\ (ds_status X = 666 -> cs_avail_in (ds_strm X) <> 0 -> R = (fst (err_return X Z_BUF_ERROR), -5))
    /\ (ds_status X = 666 -> cs_avail_in (ds_strm X) = 0 -> blocks_path X)
    /\ (ds_status X = 113 -> blocks_path X)
    /\ (ds_status X = 42 ->
        let X5 := flush_pending (zhdr_st X) in
        ds_wrap X = 1 /\ ds_w_bits X = 15 /\ ds_level X = 6 /\ ds_strategy X = 0 /\ 0 <= ds_strstart X < 2^31
        /\ 0 <= ds_pending X /\ ds_pending X + 6 <= 65536 /\ ds_lit_bufsize X = 16384 /\ 0 <= cs_adler (ds_strm X) < 2^64
        /\ 0 <= cs_avail_out (ds_strm X) < 2^31 /\ fp_ok (zhdr_st X) /\ ds_status X5 = 113 /\ 0 <= ds_pending X5 < 2^64 /\ ole X5
        /\ (ds_pending X5 <> 0 -> R = (set_last_flush X5 (-1), 0))
        /\ (ds_pending X5 = 0 -> blocks_path X5)).

  Definition defl_path (d : deflate_state) : Prop :=
    let s1 := set_last_flush d flush in
    ole d /\ (ds_status d = 42 \/ ds_status d = 113 \/ ds_status d = 666) /\ 0 <= cs_avail_in (ds_strm d) <= 1
    /\ 0 <= cs_next_in (ds_strm d) <= Z.of_nat (length inp)
    /\ (ds_status d = 666 /\ flush <> 4 -> R = (fst (err_return d Z_STREAM_ERROR), -2))
    /\ (~ (ds_status d = 666 /\ flush <> 4) ->
        0 <= cs_avail_out (ds_strm d) < 2^31 /\ - 2 <= ds_last_flush d <= 5 /\ 0 <= ds_pending d <= 65536 /\ ds_lit_bufsize d = 16384
        /\ (cs_avail_out (ds_strm d) = 0 -> R = (fst (err_return d Z_BUF_ERROR), -5))
        /\ (cs_avail_out (ds_strm d) <> 0 ->
            (ds_pending d <> 0 ->
             let s2 := flush_pending s1 in
             fp_ok s1 /\ 0 <= ds_status s2 < 1000 /\ ole s2
             /\ (cs_avail_out (ds_strm s2) = 0 -> R = (set_last_flush s2 (-1), 0))
             /\ (cs_avail_out (ds_strm s2) <> 0 -> body_path s2))
            /\ (ds_pending d = 0 ->
                (rank_err d flush -> R = (fst (err_return s1 Z_BUF_ERROR), -5))
                /\ (~ rank_err d flush -> body_path s1)))).
End PathDefs.


Lemma ole_strm : forall (R : deflate_state * Z) X, ds_strm (fst R) = ds_strm X -> ole R X.
Proof. intros R X E. unfold ole, fwT. rewrite E. split; [lia| reflexivity]. Qed.

Lemma ole_step : forall (R : deflate_state * Z) X Y, OUTLE X Y -> fwT Y = fwT X -> ole R Y -> ole R X.
Proof. intros R X Y O E [H1 H2]. pose proof (OUTLE_len _ _ O). split; [lia| rewrite H2; exact E]. Qed.

Lemma fwT_flush_pending : forall s, fwT (flush_pending s) = fwT s.
Proof. intros s. exact (proj2 (proj2 (proj2 (proj2 (CF_fields _ _ (CF_flush_pending s)))))). Qed.
Lemma fwT_put_adler : forall s, fwT (put_adler s) = fwT s. Proof. reflexivity. Qed.
Lemma fwT_zhdr : forall s, ds_w_bits s = 15 -> ds_level s = 6 -> ds_strategy s = 0 -> fwT (zhdr_st s) = fwT s.
Proof. intros s WB LV SG. rewrite (zhdr_eq s WB LV SG). cbv zeta. destruct (ds_strstart s =? 0); reflexivity. Qed.
Lemma ole_err : forall s e rc, ole (fst (err_return s e), rc) s.
Proof. intros s e rc. unfold ole, fwT, err_return. cbn [fst]. split; [apply Nat.le_refl| reflexivity]. Qed.

Lemma strm_set_wrap : forall s v, ds_strm (set_wrap s v) = ds_strm s. Proof. reflexivity. Qed.
Lemma pending_set_wrap : forall s v, ds_pending (set_wrap s v) = ds_pending s. Proof. reflexivity. Qed.
Lemma strm_set_last_flush : forall s v, ds_strm (set_last_flush s v) = ds_strm s. Proof. reflexivity. Qed.
Lemma strm_set_status : forall s v, ds_strm (set_status s v) = ds_strm s. Proof. reflexivity. Qed.

Lemma trailer_st_put_adler : forall X, ds_wrap X <> 2 -> trailer_st X = put_adler X.
Proof. intros X W. unfold trailer_st. replace (ds_wrap X =? 2) with false by (symmetry; apply Z.eqb_neq; exact W). reflexivity. Qed.

Section PathProof.
  Variables (inp : list Z) (flush : Z).
  Variable c0 : cstrm.
  Variable s0 : deflate_state.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hs0 : ds_strm s0 = c0.
  Hypothesis D0 : dwf s0.
  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.
  Hypothesis HAO : cs_avail_out c0 <= 1.
  Hypothesis HIN : cs_input c0 = arr_of_list inp.
  Hypothesis HIL : zlength inp <= 1.
  Hypothesis HIB : Forall (fun b => 0 <= b < 256) inp.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.
  Local Notation P2 := (BoundPat.P2 c0 s0).

  Lemma P2_facts : forall X, P2 X ->
    0 <= cs_avail_in (ds_strm X) <= 1 /\ 0 <= cs_avail_out (ds_strm X) < 2^31 /\ din_tie inp X
    /\ ds_hash_size X = 32768 /\ ds_w_bits X = 15 /\ 0 <= ds_lookahead X < 2^31 /\ 0 <= ds_strstart X < 2^31.
  Proof.
    intros X [[[[D XX] V] K] P].
    pose proof (sv_ain _ _ V) as A1. pose proof (sv_inlen _ _ V) as A2. pose proof (sv_nin _ _ V) as A3.
    rewrite HIN, arr_len_of_list in A2.
    pose proof (sv_out _ _ V) as O1. pose proof (sv_aout _ _ V) as O2. rewrite (c0_out _ HC0w) in O1. unfold zlen in O1. cbn [length Z.of_nat] in O1.
    destruct (PAT_bits X D P) as [WB HB].
    pose proof (df_hsize _ D) as HS. rewrite HB in HS.
    pose proof (df_look _ D) as L1. pose proof (df_sl _ D) as L2. pose proof (df_strstart _ D) as L3. rewrite (pt_ws _ P) in L2.
    split; [lia|]. split; [lia|]. split; [split; [rewrite (sv_input _ _ V); exact HIN| exact HIB]|].
    split; [exact HS|]. split; [exact WB|]. split; lia.
  Qed.

  Lemma fin_path_ok : forall X, P2 X -> ds_pending X = 0 -> (flush = Z_FINISH -> ds_status X = FINISH_STATE) ->
    fin_path flush (dc_fin X flush) X.
  Proof.
    intros X PP Hp Hfin. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    pose proof (df_wrap _ D) as RW.
    assert (W2 : ds_wrap X <> 2) by (destruct (pt_wrap _ P) as [W|[W _]]; lia).
    destruct (P2_facts X PP) as (_ & RAO & _).
    destruct (trailer_facts c0 X H Hp) as ((H1 & Po1 & P1) & K1 & O1 & St1 & Wr1 & Lk1).
    assert (HS1 : OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4.ST c0 s0 (trailer_st X)) by (split; [exact H1| rewrite K1; exact K]).
    destruct (ST_flush_pending c0 s0 HC0 (trailer_st X) HS1) as (HS2 & Hfp & Hor & Hp2 & St2 & Wr2 & Lk2 & Ai2).
    destruct (DC_flush_pending c0 (trailer_st X) HC0w H1) as (_ & _ & O2 & _).
    pose proof HS2 as [[[D2 _] _] _]. pose proof (df_pend _ D2) as Pd2. pose proof (dwf_sizes _ D2) as (_ & _ & Sl2 & _).
    pose proof (sv_adler _ _ V) as RAD.
    rewrite (trailer_st_put_adler X W2) in *.
    unfold fin_path, dc_fin.
    split.
    {
      destruct HFL as [F|F]; rewrite F; [change (negb (Z_NO_FLUSH =? Z_FINISH)) with true; cbv iota; apply ole_strm; reflexivity|].
      change (negb (Z_FINISH =? Z_FINISH)) with false. cbv iota.
      destruct (ds_wrap X <=? 0); [apply ole_strm; reflexivity|].
      rewrite deflate_trailer_eq, (trailer_st_put_adler X W2). cbv zeta.
      apply (ole_step _ X (flush_pending (put_adler X))); [exact (OUTLE_trans _ _ _ O1 O2)| rewrite fwT_flush_pending; apply fwT_put_adler|].
      generalize (flush_pending (put_adler X)). intros s2. apply ole_strm. cbn [fst]. destruct (0 <? ds_wrap s2); [apply strm_set_wrap| reflexivity]. }
    split; [exact RW|]. split; [exact W2|].
    split.
    { intros F4. destruct HFL as [F|F]; [|unfold Z_FINISH in F; lia]. rewrite F. reflexivity. }
    split.
    { intros F4 WN. rewrite F4. change (negb (4 =? Z_FINISH)) with false. cbv iota.
      replace (ds_wrap X <=? 0) with true by (symmetry; apply Z.leb_le; exact WN). reflexivity. }
    intros F4 WP. cbv zeta.
    split; [lia|]. split; [lia|]. split; [exact RAD|]. split; [exact (pt_lbs _ P)|]. split; [exact RAO|]. split; [exact Hfp|].
    split; [rewrite Wr2; exact Wr1|]. split; [lia|].
    rewrite F4. change (negb (4 =? Z_FINISH)) with false. cbv iota.
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

  Lemma blocks_path_ok : forall X, P2 X -> ds_pending X = 0 -> (ds_status X = FINISH_STATE -> cs_avail_in (ds_strm X) = 0) ->
    blocks_path inp flush (dc_blocks X flush) X.
  Proof.
    intros X PP Hp Hfin. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    destruct (P2_facts X PP) as (RAI & RAO & TIE & HSZ & WB & RLA & RSS).
    assert (Hfl : 0 <= flush <= 5) by (destruct HFL as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia).
    assert (RST : 0 <= ds_status X < 1000) by (destruct (pt_status _ P) as [E|[E|E]]; rewrite E; unfold INIT_STATE, BUSY_STATE, FINISH_STATE; lia).
    pose proof (P2_blocks c0 s0 HC0 X flush PP Hp HFL Hfin) as PB. cbv zeta in PB.
    unfold blocks_path, dc_blocks.
    assert (EDB : deflate_blocks X flush =
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
                  else (X, None)) by reflexivity.
    destruct (blk_cond X flush) eqn:Hcond.
    2:{
        rewrite EDB in PB |- *. cbn [fst snd] in PB. destruct PB as [_ PB2]. destruct (PB2 eq_refl) as [_ Hf].
        pose proof (fin_path_ok X PP Hp Hf) as FP.
        split; [exact (proj1 FP)|]. split; [exact RAI|]. split; [exact RLA|]. split; [exact RST|].
        split; [intros HH; discriminate HH| intros _; exact FP]. }
    assert (Hst0 : ds_status X <> FINISH_STATE).
    { intros Ef. unfold blk_cond in Hcond. rewrite (Hfin Ef), (dx_fin _ XX Ef), Ef in Hcond. cbn in Hcond. rewrite andb_false_r in Hcond. discriminate Hcond. }
    pose proof (PAT_dmode X P) as Em.
    assert (PRE : BFPRE c0 X flush) by (split; [exact HC0|]; split; [exact H|]; split; [exact Hp|]; split; [exact Hst0 | exact Hfl]).
    destruct (slow_bf_spec FB_CALL_ok c0 X flush PRE Em) as [SAFE POST].
    pose proof (bslow_frames c0 X flush FB_CALL_ok PRE Em (pt_ws _ P) HFL) as BS. cbv zeta in BS.
    rewrite EDB in PB |- *. rewrite run_compress_func_dmode, Em in PB |- *. cbv iota in PB |- *.
    unfold BFPOST in POST. unfold blk_s2.
    destruct (deflate_slow X flush) as [s1 bst]. cbn [fst snd] in POST, BS, PB |- *. cbv beta iota zeta in PB |- *.
    destruct POST as (H1 & K1 & O1 & Pbd & Pfin & Pfd). destruct BS as (B3 & B4 & B5 & B6).
    pose proof H1 as [_ V1]. pose proof (sv_out _ _ V1) as O1a. pose proof (sv_aout _ _ V1) as O1b. rewrite (c0_out _ HC0w) in O1a. unfold zlen in O1a. cbn [length Z.of_nat] in O1a.
    assert (NBD : bst <> block_done) by (intros E; destruct (B6 ltac:(rewrite E; discriminate)) as (_ & [E2|E2]); rewrite E in E2; discriminate E2).
    assert (INS0 : ds_insert X = 0) by (destruct (pt_ins _ P) as [I|F]; [exact I| contradiction]).
    assert (W2 : ds_wrap X = 1) by (destruct (pt_wrap _ P) as [W|[_ Fw]]; [exact W| contradiction (Hst0 Fw)]).
    split.
    { apply (ole_step _ X s1 O1 (proj2 (proj2 (proj2 (proj2 (CF_fields _ _ B3)))))).
      destruct bst; cbn [block_state_eqb orb] in PB |- *; cbv iota in PB |- *.
      - apply ole_strm. destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity.
      - exfalso; apply NBD; reflexivity.
      - apply ole_strm. rewrite strm_set_status. destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity.
      - cbn [fst snd] in PB. destruct PB as [PP2 PB2]. destruct (PB2 eq_refl) as [Hp2 Hf2].
        exact (ole_step _ s1 (set_status s1 FINISH_STATE) (OUTLE_strm _ _ eq_refl) eq_refl (proj1 (fin_path_ok _ PP2 Hp2 Hf2))). }
    split; [exact RAI|]. split; [exact RLA|]. split; [exact RST|].
    split; [|intros HH; discriminate HH]. intros _.
    split; [exact (pt_level _ P)|]. split; [exact (pt_strategy _ P)|]. split; [exact TIE|]. split; [exact SAFE|].
    split; [exact (pt_ws _ P)|]. split; [exact HSZ|]. split; [exact (pt_lbs _ P)|]. split; [exact INS0|]. split; [exact W2|]. split; [exact RAO|].
    split; [exact NBD|].
    destruct bst; cbn [block_state_eqb orb] in PB |- *; cbv iota in PB |- *; try (exfalso; apply NBD; reflexivity).
    -
      split; [lia|]. split.
      { apply ole_strm. destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity. }
      split; [intros _ E; rewrite E; reflexivity|].
      split; [intros _ E; replace (cs_avail_out (ds_strm s1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact E); reflexivity|].
      intros E; discriminate E.
    -
      rewrite !strm_set_status. split; [lia|]. split.
      { apply ole_strm. destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity. }
      split; [intros _ E; rewrite E; reflexivity|].
      split; [intros _ E; replace (cs_avail_out (ds_strm s1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact E); reflexivity|].
      intros E; discriminate E.
    -
      cbn [fst snd] in PB. destruct PB as [PP2 PB2]. destruct (PB2 eq_refl) as [Hp2 Hf2].
      pose proof (fin_path_ok _ PP2 Hp2 Hf2) as FP.
      rewrite !strm_set_status. split; [lia|]. split.
      { exact (ole_step _ s1 (set_status s1 FINISH_STATE) (OUTLE_strm _ _ eq_refl) eq_refl (proj1 FP)). }
      split; [intros [E|E]; discriminate E|]. split; [intros [E|E]; discriminate E|].
      intros _. exact FP.
  Qed.

  Lemma dc_hdr_skip : forall X, ds_status X <> INIT_STATE -> ds_status X <> GZIP_STATE -> dc_hdr X flush = dc_blocks X flush.
  Proof.
    intros X E1 E2. unfold dc_hdr, dc_gz.
    replace (ds_status X =? INIT_STATE) with false by (symmetry; apply Z.eqb_neq; exact E1).
    replace (ds_status X =? GZIP_STATE) with false by (symmetry; apply Z.eqb_neq; exact E2). reflexivity.
  Qed.

  Lemma body_path_ok : forall X, P2 X -> ds_pending X = 0 -> body_path inp flush (dc_body X flush) X.
  Proof.
    intros X PP Hp. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    destruct (P2_facts X PP) as (RAI & RAO & TIE & HSZ & WB & RLA & RSS).
    assert (HST : ds_status X = 42 \/ ds_status X = 113 \/ ds_status X = 666) by exact (pt_status _ P).
    assert (E4 : ((ds_status X =? INIT_STATE) && (ds_wrap X =? 0)) = false).
    { destruct (Z.eqb_spec (ds_status X) INIT_STATE) as [E|E]; [| reflexivity].
      destruct (pt_wrap _ P) as [W|[_ F]]; [rewrite W; reflexivity | rewrite E in F; discriminate F]. }
    unfold body_path, dc_body. rewrite E4.
    destruct (Z.eq_dec (ds_status X) 666) as [E6|N6].
    -
      destruct (Z.eq_dec (cs_avail_in (ds_strm X)) 0) as [A0|AN].
      + replace ((ds_status X =? FINISH_STATE) && negb (cs_avail_in (ds_strm X) =? 0)) with false
          by (rewrite A0; cbn; rewrite andb_false_r; reflexivity).
        rewrite (dc_hdr_skip X ltac:(rewrite E6; discriminate) ltac:(rewrite E6; discriminate)).
        pose proof (blocks_path_ok X PP Hp (fun _ => A0)) as BP.
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
      + rewrite (dc_hdr_skip X ltac:(rewrite E1; discriminate) ltac:(rewrite E1; discriminate)).
        pose proof (blocks_path_ok X PP Hp (fun C => False_ind _ (N6 C))) as BP.
        split; [exact (proj1 BP)|]. split; [exact HST|]. split; [exact RAI|].
        split; [intros C; contradiction|]. split; [intros C; contradiction|].
        split; [intros _; exact BP|]. intros C; rewrite E1 in C; discriminate C.
      +
        assert (E : ds_status X = INIT_STATE) by (unfold INIT_STATE; lia).
        destruct (hdr_zlib c0 s0 HC0 Hs0 D0 X HS Hp E) as (HOK & HSz & Stz & Horz & Aiz & Lkz & Wrz).
        destruct (zhdr_facts c0 X H Hp E) as ((H1 & _ & _) & K1 & O1 & _).
        destruct (DC_flush_pending c0 (zhdr_st X) HC0w H1) as (_ & _ & O2 & _).
        assert (Pz : PAT (flush_pending (zhdr_st X))).
        { apply (PAT_PF _ _ (PF_flush_pending (zhdr_st X))). destruct (PF_zhdr_pre X) as (t & Et & Pt). rewrite Et.
          apply PAT_busy; [exact (PAT_PF _ _ Pt P)|].
          pose proof (PF_fields _ _ Pt) as (_ & _ & (Est & _) & _). rewrite Est. exact E. }
        destruct HOK as (_ & _ & _ & FPOK & HOK2). cbv zeta in HOK2. destruct HOK2 as (_ & RP5 & _).
        assert (W1 : ds_wrap X = 1) by (destruct (pt_wrap _ P) as [W|[_ F]]; [exact W| rewrite E in F; discriminate F]).
        pose proof (sv_adler _ _ V) as RAD.
        unfold dc_hdr. replace (ds_status X =? INIT_STATE) with true by (symmetry; apply Z.eqb_eq; exact E).
        rewrite deflate_zlib_header_eq. cbv zeta.
        assert (BPK : ds_pending (flush_pending (zhdr_st X)) = 0 -> blocks_path inp flush (dc_blocks (flush_pending (zhdr_st X)) flush) (flush_pending (zhdr_st X))).
        { intros P0. apply (blocks_path_ok _ (conj HSz Pz) P0). intros C. rewrite Stz in C. discriminate C. }
        assert (EGZ : dc_gz (flush_pending (zhdr_st X)) flush = dc_blocks (flush_pending (zhdr_st X)) flush).
        { unfold dc_gz. rewrite Stz. reflexivity. }
        assert (FW5 : fwT (flush_pending (zhdr_st X)) = fwT X) by (rewrite fwT_flush_pending; exact (fwT_zhdr X WB (pt_level _ P) (pt_strategy _ P))).
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
        split; [exact W1|]. split; [exact WB|]. split; [exact (pt_level _ P)|]. split; [exact (pt_strategy _ P)|]. split; [exact RSS|].
        split; [lia|]. split; [lia|]. split; [exact (pt_lbs _ P)|]. split; [exact RAD|]. split; [exact RAO|]. split; [exact FPOK|].
        split; [exact Stz|]. split; [exact RP5|]. split; [exact OL5|].
        split.
        * intros PN. replace (ds_pending X5 =? 0) with false by (symmetry; apply Z.eqb_neq; exact PN). reflexivity.
        * intros P0. rewrite P0. cbn [negb Z.eqb]. exact (BPK P0).
  Qed.

  Theorem defl_path_ok : P2 s0 -> defl_path inp flush (deflate_core s0 flush) s0.
  Proof.
    intros PP. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    destruct (P2_facts s0 PP) as (RAI & RAO & TIE & HSZ & WB & RLA & RSS).
    assert (Hfl : 0 <= flush <= 5) by (destruct HFL as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia).
    pose proof (sv_nin _ _ V) as N1. pose proof (sv_inlen _ _ V) as N2. rewrite HIN, arr_len_of_list in N2. unfold zlength in N2.
    pose proof (df_lf _ D) as RLF. pose proof (df_pend _ D) as (Pd1 & Pd2 & Pd3). rewrite (pt_lbs _ P) in Pd3.
    unfold defl_path. cbv zeta. rewrite deflate_core_eq.
    replace (deflateStateCheck s0 || (Z_BLOCK <? flush) || (flush <? 0)) with false
      by (rewrite (df_status _ D); destruct HFL as [-> | ->]; reflexivity).
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
                destruct (DC_flush_pending c0 (set_last_flush s0 flush) HC0w (proj1 (proj1 (P2_slf c0 s0 s0 flush PP ltac:(lia))))) as (_ & _ & O2 & _);
                exact (ole_step _ s0 (flush_pending (set_last_flush s0 flush)) (OUTLE_trans _ _ _ (OUTLE_strm _ _ eq_refl) O2)
                         (eq_trans (fwT_flush_pending _) eq_refl) OL2) ]). }
    split; [exact (pt_status _ P)|]. split; [exact RAI|]. split; [lia|].
    split.
    { intros [E6 F4]. replace ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)) with true; [reflexivity|].
      rewrite E6. destruct HFL as [-> | F]; [reflexivity| unfold Z_FINISH in F; lia]. }
    intros NE.
    replace ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)) with false.
    2:{ symmetry. apply andb_false_iff. destruct (Z.eqb_spec (ds_status s0) FINISH_STATE) as [E|E]; [right|left; reflexivity].
        destruct (Z.eqb_spec flush Z_FINISH) as [F|F]; [reflexivity|]. exfalso. apply NE. split; [exact E| exact F]. }
    split; [exact RAO|]. split; [exact RLF|]. split; [lia|]. split; [exact (pt_lbs _ P)|].
    split.
    { intros A0. rewrite A0. reflexivity. }
    intros AN. replace (cs_avail_out (ds_strm s0) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AN).
    pose proof (P2_slf c0 s0 s0 flush PP ltac:(lia)) as PP1.
    unfold dc_pend. cbv zeta.
    change (ds_pending (set_last_flush s0 flush)) with (ds_pending s0).
    change (cs_avail_in (ds_strm (set_last_flush s0 flush))) with (cs_avail_in (ds_strm s0)).
    split.
    -
      intros PN. replace (ds_pending s0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact PN). cbn [negb].
      destruct (P2_fp c0 s0 HC0 _ PP1) as [PPf Hor].
      destruct (ST_flush_pending c0 s0 HC0 _ (proj1 PP1)) as (_ & FPOK & _).
      assert (RST2 : 0 <= ds_status (flush_pending (set_last_flush s0 flush)) < 1000)
        by (destruct (pt_status _ (proj2 PPf)) as [E|[E|E]]; rewrite E; unfold INIT_STATE, BUSY_STATE, FINISH_STATE; lia).
      assert (BPK : cs_avail_out (ds_strm (flush_pending (set_last_flush s0 flush))) <> 0 ->
                    body_path inp flush (dc_body (flush_pending (set_last_flush s0 flush)) flush) (flush_pending (set_last_flush s0 flush))).
      { intros A2. apply (body_path_ok _ PPf). destruct Hor as [X0|X0]; [exact X0| contradiction]. }
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
        * intros _. apply (body_path_ok _ PP1). exact P0.
  Qed.
End PathProof.

Theorem defl_path_intro : forall ds zc flush,
  DD ds -> dcall_wf zc -> PAT ds -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
  zlength (zc_input zc) <= 1 -> zc_avail_out zc <= 1 ->
  defl_path (zc_input zc) flush (deflate_core (set_strm ds (cstrm_of_call zc)) flush) (set_strm ds (cstrm_of_call zc)).
Proof.
  intros ds zc flush HDD Hzc P HFL HIL HAO.
  set (c0 := cstrm_of_call zc).
  pose proof (C0OK'_of_call zc Hzc) as HC0. fold c0 in HC0.
  assert (H0 : DC c0 (set_strm ds c0)) by (split; [apply DD_set_strm; exact HDD | subst c0; apply SV_entry; exact Hzc]).
  assert (E0 : ds_strm (set_strm ds c0) = c0) by reflexivity.
  pose proof (PAT_set_strm ds c0 P) as P0.
  destruct Hzc as (_ & _ & _ & HB).
  apply (defl_path_ok (zc_input zc) flush c0 (set_strm ds c0) HC0 E0 (proj1 (proj1 H0)) HFL).
  - exact HAO.
  - reflexivity.
  - exact HIL.
  - exact HB.
  - exact (conj (conj H0 eq_refl) P0).
Qed.
