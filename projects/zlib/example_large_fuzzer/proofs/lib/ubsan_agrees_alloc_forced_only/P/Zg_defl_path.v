(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay RefDeflSlow6 RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_defl_model Z_defl_path.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition din_tieg (inp : list Z) (d : deflate_state) : Prop :=
  cs_input (ds_strm d) = arr_of_list inp /\ Forall (fun b => 0 <= b < 256) inp.

(* [comment removed for export] *)
Definition dblk (X : deflate_state) (flush : Z) : deflate_state * block_state :=
  if ds_level X =? 0 then deflate_stored X flush else deflate_slow X flush.

Section PathDefs.
  Variables (inp : list Z) (flush : Z) (R : deflate_state * Z).

  Definition blocks_pathg (X : deflate_state) : Prop :=
    ole R X /\ 0 <= cs_avail_in (ds_strm X) < 2^31 /\ 0 <= ds_lookahead X < 2^31 /\ 0 <= ds_status X < 1000
    /\ (blk_cond X flush = true ->
        let X1 := fst (dblk X flush) in
        (ds_level X = 0 \/ 4 <= ds_level X <= 9) /\ 0 <= ds_strategy X <= 1 /\ din_tieg inp X
        /\ ds_w_size X = 32768 /\ ds_hash_size X = 32768 /\ ds_lit_bufsize X = 16384 /\ ds_wrap X <> 2 /\ ds_wrap X <> 0 /\ - 2 <= ds_wrap X <= 2
        /\ 0 <= cs_avail_out (ds_strm X) < 2^31
        /\ (ds_level X = 0 -> st_entry X /\ ds_pending_buf_size X = 65536) /\ (ds_level X <> 0 -> slow_safe X flush)
        /\ ole R X1 /\ 0 <= cs_avail_out (ds_strm X1) < 2^31
        /\ (snd (dblk X flush) = need_more -> cs_avail_out (ds_strm X1) = 0 -> R = (set_last_flush X1 (-1), 0))
        /\ (snd (dblk X flush) = need_more -> cs_avail_out (ds_strm X1) <> 0 -> R = (X1, 0))
        /\ (snd (dblk X flush) = finish_started -> cs_avail_out (ds_strm X1) = 0 -> R = (set_last_flush (set_status X1 FINISH_STATE) (-1), 0))
        /\ (snd (dblk X flush) = finish_started -> cs_avail_out (ds_strm X1) <> 0 -> R = (set_status X1 FINISH_STATE, 0))
        /\ (snd (dblk X flush) = finish_done -> fin_path flush R (set_status X1 FINISH_STATE))
        /\ (snd (dblk X flush) = block_done ->
            flush = 5 /\ fp_ok X1 /\ ds_lit_bufsize X1 = 16384 /\ ole R (flush_pending X1)
            /\ 0 <= cs_avail_out (ds_strm (flush_pending X1)) < 2^31
            /\ (cs_avail_out (ds_strm (flush_pending X1)) = 0 -> R = (set_last_flush (flush_pending X1) (-1), 0))
            /\ (cs_avail_out (ds_strm (flush_pending X1)) <> 0 -> fin_path flush R (flush_pending X1))))
    /\ (blk_cond X flush = false -> fin_path flush R X).

  Definition body_pathg (X : deflate_state) : Prop :=
    ole R X /\ (ds_status X = 42 \/ ds_status X = 113 \/ ds_status X = 666) /\ 0 <= cs_avail_in (ds_strm X) < 2^31
    /\ (ds_status X = 666 -> cs_avail_in (ds_strm X) <> 0 -> R = (fst (err_return X Z_BUF_ERROR), -5))
    /\ (ds_status X = 666 -> cs_avail_in (ds_strm X) = 0 -> blocks_pathg X)
    /\ (ds_status X = 113 -> blocks_pathg X)
    /\ (ds_status X = 42 ->
        let X5 := flush_pending (zhdr_st X) in
        ds_wrap X = 1 /\ ds_w_bits X = 15 /\ 0 <= ds_level X <= 9 /\ 0 <= ds_strategy X <= 1 /\ 0 <= ds_strstart X < 2^31
        /\ 0 <= ds_pending X /\ ds_pending X + 6 <= 65536 /\ ds_lit_bufsize X = 16384 /\ 0 <= cs_adler (ds_strm X) < 2^64
        /\ 0 <= cs_avail_out (ds_strm X) < 2^31 /\ fp_ok (zhdr_st X) /\ ds_status X5 = 113 /\ 0 <= ds_pending X5 < 2^64 /\ ole R X5
        /\ (ds_pending X5 <> 0 -> R = (set_last_flush X5 (-1), 0))
        /\ (ds_pending X5 = 0 -> blocks_pathg X5)).

  Definition defl_pathg (d : deflate_state) : Prop :=
    let s1 := set_last_flush d flush in
    ole R d /\ (ds_status d = 42 \/ ds_status d = 113 \/ ds_status d = 666) /\ 0 <= cs_avail_in (ds_strm d) < 2^31
    /\ 0 <= cs_next_in (ds_strm d) <= Z.of_nat (length inp)
    /\ (ds_status d = 666 /\ flush <> 4 -> R = (fst (err_return d Z_STREAM_ERROR), -2))
    /\ (~ (ds_status d = 666 /\ flush <> 4) ->
        0 <= cs_avail_out (ds_strm d) < 2^31 /\ - 2 <= ds_last_flush d <= 5 /\ 0 <= ds_pending d <= 65536 /\ ds_lit_bufsize d = 16384
        /\ (cs_avail_out (ds_strm d) = 0 -> R = (fst (err_return d Z_BUF_ERROR), -5))
        /\ (cs_avail_out (ds_strm d) <> 0 ->
            (ds_pending d <> 0 ->
             let s2 := flush_pending s1 in
             fp_ok s1 /\ 0 <= ds_status s2 < 1000 /\ ole R s2
             /\ (cs_avail_out (ds_strm s2) = 0 -> R = (set_last_flush s2 (-1), 0))
             /\ (cs_avail_out (ds_strm s2) <> 0 -> body_pathg s2))
            /\ (ds_pending d = 0 ->
                (rank_err d flush -> R = (fst (err_return s1 Z_BUF_ERROR), -5))
                /\ (~ rank_err d flush -> body_pathg s1)))).
End PathDefs.
