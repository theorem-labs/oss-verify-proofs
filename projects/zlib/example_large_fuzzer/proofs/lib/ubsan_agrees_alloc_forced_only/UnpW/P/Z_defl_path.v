(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateRel RefDeflSafeG RefDeflSafeFB RefDeflSafeLF RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BoundFw. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import BoundSlow BoundCore BoundPat.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_defl_iface. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_defl_model.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)

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
        /\ ds_w_size X = 32768 /\ ds_hash_size X = 32768 /\ ds_lit_bufsize X = 16384 /\ ds_insert X = 0 /\ ds_wrap X <> 2
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

(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)

