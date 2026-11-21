(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sb_lastv (s : deflate_state) (flush : Z) : Z :=
  if (flush =? Z_FINISH) && (sb_len s =? wrap32 (sb_left s + cs_avail_in (ds_strm s))) then 1 else 0.

(* [comment removed for export] *)
Definition st_emit1 (s : deflate_state) (flush : Z) : deflate_state :=
  flush_pending (sb_patch (tr_stored_block s None 0 (sb_lastv s flush)) (sb_len s)).

(* [comment removed for export] *)
Definition st_copy (s3 : deflate_state) (left len : Z) : deflate_state * Z :=
  if negb (left =? 0) then (st_lcopy s3 (lc_len left len), len - lc_len left len) else (s3, len).

(* [comment removed for export] *)
Definition st_rdo (s4 : deflate_state) (n : Z) : deflate_state :=
  if negb (n =? 0) then
    let '(s, _) := read_buf s4 RB_next_out n in
    let st := ds_strm s in
    let st := cset_avail_out st (cs_avail_out st - n) in
    let st := cset_total_out st (wrap64 (cs_total_out st + n)) in
    set_strm s st
  else s4.

(* [comment removed for export] *)
Ltac synrefl := lazymatch goal with |- ?a = ?b => first [constr_eq a b; exact (@eq_refl _ a) | fail "synrefl: sides differ"] end.

Lemma deflate_stored_body_eq : forall s flush mb,
  deflate_stored_body s flush mb
  = (if cs_avail_out (ds_strm s) <? sb_hdr s then (s, 0, true)
     else if sb_brk s flush mb then (s, 0, true)
     else let s3 := st_emit1 s flush in
          let '(s4, len') := st_copy s3 (sb_left s) (sb_len s) in
          (st_rdo s4 len', sb_lastv s flush, false)).
Proof.
  intros s flush mb.
  unfold deflate_stored_body, sb_brk, st_emit1, st_copy, st_rdo, sb_lastv, sb_len, sb_len1, sb_left, sb_hdr, sb_patch, st_lcopy, lc_len, MAX_STORED.
  cbv zeta.
  destruct (cs_avail_out (ds_strm s) <? Z.shiftr (ds_bi_valid s + 42) 3); [reflexivity|].
  match goal with |- (if ?c then _ else _) = (if ?c' then _ else _) => change c' with c; destruct c; [reflexivity|] end.
  set (len := if cs_avail_out (ds_strm s) - Z.shiftr (ds_bi_valid s + 42) 3 <? _ then _ else _). clearbody len.
  set (last := if (flush =? Z_FINISH) && _ then 1 else 0). clearbody last.
  set (s3 := flush_pending _). clearbody s3.
  set (left0 := wrap32 (ds_strstart s - ds_block_start s)). clearbody left0.
  destruct (negb (left0 =? 0)).
  - set (left := if len <? left0 then len else left0). clearbody left. unfold cs_emit.
    destruct s3; dsred. synrefl.
  - cbn [negb]. dsred. synrefl.
Qed.

Lemma sloop_S : forall f s flush mb,
  deflate_stored_loop (S f) s flush mb
  = (let '(s1, last, broke) := deflate_stored_body s flush mb in
     if broke then (s1, last) else if last =? 0 then deflate_stored_loop f s1 flush mb else (s1, last)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac krefl := lazymatch goal with |- ?a = _ => exact_no_check (@eq_refl _ a) end.

(* [comment removed for export] *)
Definition st_wupd (s : deflate_state) (used : Z) : deflate_state :=
  if negb (Z.eqb used 0) then
    let s :=
      if Z.leb (ds_w_size s) used then
        let s := set_matches s 2 in
        let st := ds_strm s in
        let s := set_window s (arr_upd (ds_window s) 0
                   (arr_slice (cs_input st) (cs_next_in st - ds_w_size s) (ds_w_size s))) in
        let s := set_strstart s (ds_w_size s) in
        set_insert s (ds_strstart s)
      else
        let s :=
          if Z.leb (ds_window_size s - ds_strstart s) used then
            let s := set_strstart s (ds_strstart s - ds_w_size s) in
            let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s)) in
            let s := if Z.ltb (ds_matches s) 2 then set_matches s (ds_matches s + 1) else s in
            if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s
          else s in
        let st := ds_strm s in
        let s := set_window s (arr_upd (ds_window s) (ds_strstart s)
                   (arr_slice (cs_input st) (cs_next_in st - used) used)) in
        let s := set_strstart s (ds_strstart s + used) in
        set_insert s (ds_insert s + MIN used (wrap32 (ds_w_size s - ds_insert s))) in
    set_block_start s (ds_strstart s)
  else s.

(* [comment removed for export] *)
Definition st_slide3 (s : deflate_state) (have : Z) : deflate_state * Z :=
  if Z.ltb have (cs_avail_in (ds_strm s)) && Z.leb (ds_w_size s) (ds_block_start s) then
    let s := set_block_start s (ds_block_start s - ds_w_size s) in
    let s := set_strstart s (ds_strstart s - ds_w_size s) in
    let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s)) in
    let s := if Z.ltb (ds_matches s) 2 then set_matches s (ds_matches s + 1) else s in
    let have := wrap32 (have + ds_w_size s) in
    let s := if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s in
    (s, have)
  else (s, have).

(* [comment removed for export] *)
Definition st_fillw (s : deflate_state) (have : Z) : deflate_state :=
  if negb (Z.eqb have 0) then
    let '(s, _) := read_buf s (RB_window (ds_strstart s)) have in
    let s := set_strstart s (ds_strstart s + have) in
    set_insert s (ds_insert s + MIN have (wrap32 (ds_w_size s - ds_insert s)))
  else s.

(* [comment removed for export] *)
Definition st_final (s : deflate_state) (flush : Z) : deflate_state * block_state :=
  let have := t_have s in
  let min_block := t_mb s in
  let left := wrap32 (ds_strstart s - ds_block_start s) in
  if Z.leb min_block left
     || ((negb (Z.eqb left 0) || Z.eqb flush Z_FINISH) && negb (Z.eqb flush Z_NO_FLUSH)
         && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.leb left have)
  then
    let len := MIN left have in
    let last := if Z.eqb flush Z_FINISH && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.eqb len left
                then 1 else 0 in
    let s := tr_stored_block s (Some (ds_block_start s)) len last in
    let s := set_block_start s (ds_block_start s + len) in
    let s := flush_pending s in
    (s, if negb (Z.eqb last 0) then finish_started else need_more)
  else (s, need_more).

(* [comment removed for export] *)
Definition post_slide (s : deflate_state) (have flush : Z) : deflate_state * block_state :=
    let have := if Z.ltb (cs_avail_in (ds_strm s)) have then cs_avail_in (ds_strm s) else have in
    let s :=
      if negb (Z.eqb have 0) then
        let '(s, _) := read_buf s (RB_window (ds_strstart s)) have in
        let s := set_strstart s (ds_strstart s + have) in
        set_insert s (ds_insert s + MIN have (wrap32 (ds_w_size s - ds_insert s)))
      else s in
    let s := if Z.ltb (ds_high_water s) (ds_strstart s) then set_high_water s (ds_strstart s) else s in
    (* [comment removed for export] *)
    let have := Z.shiftr (ds_bi_valid s + 42) 3 in
    let have := MIN (ds_pending_buf_size s - have) MAX_STORED in
    let min_block := MIN have (ds_w_size s) in
    let left := wrap32 (ds_strstart s - ds_block_start s) in
    if Z.leb min_block left
       || ((negb (Z.eqb left 0) || Z.eqb flush Z_FINISH) && negb (Z.eqb flush Z_NO_FLUSH)
           && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.leb left have)
    then
      let len := MIN left have in
      let last := if Z.eqb flush Z_FINISH && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.eqb len left
                  then 1 else 0 in
      let s := tr_stored_block s (Some (ds_block_start s)) len last in
      let s := set_block_start s (ds_block_start s + len) in
      let s := flush_pending s in
      (s, if negb (Z.eqb last 0) then finish_started else need_more)
    else (s, need_more).

(* [comment removed for export] *)
Definition post_hw (s : deflate_state) (last flush : Z) : deflate_state * block_state :=
  if negb (Z.eqb last 0) then (s, finish_done)
  else if negb (Z.eqb flush Z_NO_FLUSH) && negb (Z.eqb flush Z_FINISH)
          && Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.eqb (ds_strstart s) (ds_block_start s)
  then (s, block_done)
  else
    (* [comment removed for export] *)
    let have := wrap32 (ds_window_size s - ds_strstart s) in
    let '(s, have) :=
      if Z.ltb have (cs_avail_in (ds_strm s)) && Z.leb (ds_w_size s) (ds_block_start s) then
        let s := set_block_start s (ds_block_start s - ds_w_size s) in
        let s := set_strstart s (ds_strstart s - ds_w_size s) in
        let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s)) in
        let s := if Z.ltb (ds_matches s) 2 then set_matches s (ds_matches s + 1) else s in
        let have := wrap32 (have + ds_w_size s) in
        let s := if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s in
        (s, have)
      else (s, have) in
    post_slide s have flush.

(* [comment removed for export] *)
Definition post_loop (s0 : deflate_state) (flush : Z) (p : deflate_state * Z) : deflate_state * block_state :=
  let used := cs_avail_in (ds_strm s0) in
  let '(s, last) := p in
  (* [comment removed for export] *)
  let used := wrap32 (used - cs_avail_in (ds_strm s)) in
  let s :=
    if negb (Z.eqb used 0) then
      let s :=
        if Z.leb (ds_w_size s) used then
          let s := set_matches s 2 in
          (* [comment removed for export] *)
          let st := ds_strm s in
          let s := set_window s (arr_upd (ds_window s) 0
                     (arr_slice (cs_input st) (cs_next_in st - ds_w_size s) (ds_w_size s))) in
          let s := set_strstart s (ds_w_size s) in
          set_insert s (ds_strstart s)
        else
          let s :=
            if Z.leb (ds_window_size s - ds_strstart s) used then
              let s := set_strstart s (ds_strstart s - ds_w_size s) in
              let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) (ds_w_size s) (ds_strstart s)) in
              let s := if Z.ltb (ds_matches s) 2 then set_matches s (ds_matches s + 1) else s in
              if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s
            else s in
          (* [comment removed for export] *)
          let st := ds_strm s in
          let s := set_window s (arr_upd (ds_window s) (ds_strstart s)
                     (arr_slice (cs_input st) (cs_next_in st - used) used)) in
          let s := set_strstart s (ds_strstart s + used) in
          set_insert s (ds_insert s + MIN used (wrap32 (ds_w_size s - ds_insert s))) in
      set_block_start s (ds_strstart s)
    else s in
  let s := if Z.ltb (ds_high_water s) (ds_strstart s) then set_high_water s (ds_strstart s) else s in
  post_hw s last flush.

Lemma deflate_stored_eq1 : forall s flush,
  deflate_stored s flush
  = post_loop s flush (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm s) + 1)) s flush
                         (wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s)))).
Proof. intros. krefl. Qed.

(* [comment removed for export] *)
Local Strategy 1000 [post_hw].

Lemma post_loop_eq : forall s0 flush s1 last,
  post_loop s0 flush (s1, last)
  = post_hw (hw_st (st_wupd s1 (wrap32 (cs_avail_in (ds_strm s0) - cs_avail_in (ds_strm s1))))) last flush.
Proof. intros. krefl. Qed.

Local Strategy transparent [post_hw].

Lemma post_hw_eq : forall s last flush,
  post_hw s last flush
  = (if negb (last =? 0) then (s, finish_done)
     else if negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH)
             && (cs_avail_in (ds_strm s) =? 0) && (ds_strstart s =? ds_block_start s) then (s, block_done)
     else let '(s4, have) := st_slide3 s (wrap32 (ds_window_size s - ds_strstart s)) in post_slide s4 have flush).
Proof. intros. krefl. Qed.

Lemma post_slide_eq : forall s4 have flush,
  post_slide s4 have flush = st_final (hw_st (st_fillw s4 (fmin have (cs_avail_in (ds_strm s4))))) flush.
Proof. intros. krefl. Qed.
