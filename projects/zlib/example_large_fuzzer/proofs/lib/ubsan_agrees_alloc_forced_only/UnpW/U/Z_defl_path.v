From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSlow2 RefDeflSlow3 RefDeflSlow6 RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateRel RefDeflSafeG RefDeflSafeFB RefDeflSafeF RefDeflSafeLF RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BoundFw. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import BoundSlow BoundCore BoundPat.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_defl_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_defl_iface.
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
        ds_level X = 6 /\ ds_strategy X = 0 /\ din_tie inp X /\ slow_safe X flush /\ Z_defl_iface.sbs_ok (lz_fuel X) X flush /\ slow_fe X flush
        /\ ds_w_size X = 32768 /\ ds_hash_size X = 32768 /\ ds_lit_bufsize X = 16384 /\ ds_insert X = 0 /\ ds_wrap X = 1
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
Lemma ole_err : forall s e rc, ole (fst (err_return s e), rc) s.
Proof. intros s e rc. unfold ole, fwT, err_return. cbn [fst]. split; [apply Nat.le_refl| reflexivity]. Qed.
Lemma strm_set_wrap : forall s v, ds_strm (set_wrap s v) = ds_strm s. Proof. reflexivity. Qed.
Lemma pending_set_wrap : forall s v, ds_pending (set_wrap s v) = ds_pending s. Proof. reflexivity. Qed.
Lemma strm_set_last_flush : forall s v, ds_strm (set_last_flush s v) = ds_strm s. Proof. reflexivity. Qed.
Lemma strm_set_status : forall s v, ds_strm (set_status s v) = ds_strm s. Proof. reflexivity. Qed.
Lemma trailer_st_put_adler : forall X, ds_wrap X <> 2 -> trailer_st X = put_adler X.
Proof. intros X W. unfold trailer_st. replace (ds_wrap X =? 2) with false by (symmetry; apply Z.eqb_neq; exact W). reflexivity. Qed.
Lemma sbs_of_STI : forall c0 s0 flush, C0OK' c0 -> forall fuel s, RefDeflSafeL5.STI c0 s0 s -> Z_defl_iface.sbs_ok fuel s flush.
Proof.
  intros c0 s0 flush HC0. induction fuel as [|f IH]; intros s HS; [exact I|].
  rewrite sbs_ok_S. split.
  - pose proof (RefDeflSafeL5.STI_facts c0 s0 s HS) as (_ & _ & _ & W & _ & LB & MA & _ & _ & NS & _ & _ & S0 & L0 & SL & BS & _). lia.
  - destruct (RefDeflSafeL5.sstep c0 s0 flush HC0 FB_CALL_ok s HS) as [_ HC].
    destruct (snd (st_sbody s flush)); [apply IH; exact (proj1 HC)| exact I| exact I].
Qed.
Section FE.
  Variable c0 : cstrm.
  Variable s0 : deflate_state.
  Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Let HFB : FB_CALL := FB_CALL_ok.
  Local Notation STI := (RefDeflSafeL5.STI c0 s0).
  Lemma strip_fe_of_STI : forall s, STI s -> strip_fe s flush.
  Proof.
    intros s HF. unfold strip_fe, shash_fe. intros Hnone.
    pose proof (RefDeflSafeL5.sfill_stage c0 s0 flush HC0 s HF) as FS. cbv zeta in FS.
    destruct FS as (HF1 & Emeas & Hl0 & Hfw & Hl1r & Ews1 & Hnone' & Hbrk & Hret & Hss1 & Hnc & _).
    set (s1 := fst (st_fill s flush)) in *.
    pose proof (Hnone' Hnone) as Hl1.
    pose proof (RefDeflSafeL5.shash_stage c0 s0 s1 HF1 Hl1) as HS. cbv zeta in HS. destruct HS as [HR Hlm].
    rewrite <- Ews1 in Hss1.
    pose proof (RefDeflSafeL5.slm_stage c0 s0 s1 (fst (st_hash s1)) (snd (st_hash s1)) HF1 Hl1 Hss1 HR Hlm) as LM. cbv zeta in LM. destruct LM as [MR _].
    set (s2 := fst (st_hash s1)) in *. set (s4 := st_lm (prev_st s2) (snd (st_hash s1))) in *.
    split.
    -
      intros Hdc Hbf.
      pose proof (RefDeflSafeL5.sdist_stage c0 s0 s1 s2 s4 HF1 Hl1 HR MR Hdc) as SD. cbv zeta in SD. destruct SD as (R & Ebf & Hml3 & Hmll & _).
      pose proof (RefDeflSafeL5.sdist_send c0 s0 s1 _ HF1 R Hml3 Hmll) as SE.
      pose proof (RefDeflSafeL5.send_facts c0 s0 HC0 s1 _ _ _ HF1 SE) as SF. cbv zeta in SF.
      destruct SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FE7 & _). exact FE7.
    -
      intros Hdc Hma0 Hb.
      pose proof (RefDeflSafeL5.STI_facts c0 s0 s1 HF1) as (_ & _ & _ & _ & _ & _ & Hma1 & _).
      pose proof MR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ema4 & _).
      assert (Hma4 : ds_match_available s4 = 1) by (rewrite Ema4 in Hma0 |- *; clear - Hma1 Hma0; lia).
      pose proof (RefDeflSafeL5.smid_facts c0 s0 HC0 s1 s2 s4 HF1 Hl1 HR MR Hdc Hma4) as SM. cbv zeta in SM.
      destruct SM as (_ & _ & _ & _ & FE5 & _).
      destruct (slit_tally_eq s4) as [Es5 _]. rewrite <- Es5. exact FE5.
  Qed.
  Lemma sloop_fe_of_STI : forall fuel s, STI s -> sloop_fe fuel s flush.
  Proof.
    induction fuel as [|f IH]; intros s HF; [exact I|].
    rewrite sloop_fe_S. split; [exact (strip_fe_of_STI s HF)|].
    destruct (RefDeflSafeL5.sstep c0 s0 flush HC0 HFB s HF) as [_ HC].
    destruct (snd (st_sbody s flush)); [apply IH; exact (proj1 HC)| exact I| exact I].
  Qed.
  Lemma stail_fe_of_STI : forall u, STI u -> ds_lookahead u = 0 -> stail_fe u.
  Proof.
    intros s1 HF1 Hl1. unfold stail_fe.
    pose proof (RefDeflSafeL5.STI_facts c0 s0 s1 HF1) as (D1 & X1 & V1 & _ & _ & _ & Hma1 & _ & _ & _ & _ & _ & Hstr1 & _ & _ & _ & Hma11 & _).
    set (u := if negb (ds_match_available s1 =? 0) then break1_st s1 else s1).
    assert (TU : RefDeflSafeL5.TAILOK c0 s0 u).
    { subst u. destruct (Z.eqb_spec (ds_match_available s1) 0) as [M0|M0]; cbn [negb].
      - exact (RefDeflSafeL5.TAILOK_STI c0 s0 HC0 s1 HF1 Hl1 M0).
      - unfold break1_st. destruct (slit_tally_eq s1) as [E1 _]. rewrite <- E1.
        apply (RefDeflSafeL5.TAILOK_lit c0 s0 HC0 s1 HF1 Hl1). clear - Hma1 M0. lia. }
    destruct TU as (D & V & XX & B & HK & Ho & Hst & Hm & Hp & Hl0 & Hma0 & Hsn & Hstr & FE & XD & TI).
    pose proof (dwf_sizes u D) as (Sw & _). pose proof (df_sl _ D) as Hsl.
    assert (Hv : 0 <= (if ds_strstart u <? MIN_MATCH - 1 then ds_strstart u else MIN_MATCH - 1) <= ds_strstart u
                 /\ (if ds_strstart u <? MIN_MATCH - 1 then ds_strstart u else MIN_MATCH - 1) <= ds_w_size u).
    { destruct (Z.ltb_spec (ds_strstart u) (MIN_MATCH - 1)); unfold MIN_MATCH in *; lia. }
    destruct (RefDeflSafeL5.tail_insert_facts u _ (proj1 Hv) (proj2 Hv) D XX B FE XD) as (_ & _ & _ & FEst & _).
    exact FEst.
  Qed.
  Lemma tail_fe_of_STI : forall fuel s, STI s -> lz_meas s < Z.of_nat fuel -> tail_fe flush fuel s.
  Proof.
    intros fuel s HF Hmz. unfold tail_fe.
    destruct (RefDeflSafeL5.sloop c0 s0 flush HC0 HFB fuel s HF Hmz) as [_ HR].
    destruct (snd (deflate_slow_loop fuel s flush)); [exact I|]. destruct HR as [HF1 Hl1]. exact (stail_fe_of_STI _ HF1 Hl1).
  Qed.
  Lemma slow_fe_of_STI : forall s, STI s -> slow_fe s flush.
  Proof.
    intros s HF. split; [exact (sloop_fe_of_STI _ s HF)|].
    apply (tail_fe_of_STI (lz_fuel s) s HF). apply lz_fuel_meas.
    pose proof (RefDeflSafeL5.STI_facts c0 s0 s HF) as (D & _ & V & _). unfold lz_meas. pose proof (df_look _ D). pose proof (sv_ain _ _ V). lia.
  Qed.
End FE.
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
  Lemma dc_hdr_skip : forall X, ds_status X <> INIT_STATE -> ds_status X <> GZIP_STATE -> dc_hdr X flush = dc_blocks X flush.
  Proof.
    intros X E1 E2. unfold dc_hdr, dc_gz.
    replace (ds_status X =? INIT_STATE) with false by (symmetry; apply Z.eqb_neq; exact E1).
    replace (ds_status X =? GZIP_STATE) with false by (symmetry; apply Z.eqb_neq; exact E2). reflexivity.
  Qed.
End PathProof.
