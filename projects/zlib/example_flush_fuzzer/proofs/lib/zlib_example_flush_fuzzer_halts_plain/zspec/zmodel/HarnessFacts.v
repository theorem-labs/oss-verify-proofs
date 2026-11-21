(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface DeflateState Trees DeflateLz Deflate
  TreeModel FillWinModel DeflInitLib InflateState Inftrees InflateFast InflateArms Inflate HarnessKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.


Definition hgrant (o : horacle) (k : Z) : option Z := if ho_fail o k then None else Some k.







Definition dend_events (s : deflate_state) : list hevent :=
  let f (ob : option blk) := match ob with Some b => [HEfree (Z.of_N b)] | None => [] end in
  [HEfree (Z.of_N (ds_self_blk s))] ++ f (ds_window_blk s) ++ f (ds_prev_blk s) ++ f (ds_head_blk s) ++ f (ds_pending_buf_blk s).




Section Init.
  Variables (o : horacle) (n : Z) (log : list hevent) (bad : bool).
  Variables (zc : ZCall) (level method wb memLevel strategy : Z).
  Hypothesis Hn : 0 <= n.
  Hypothesis Hok : di_bad level method wb memLevel strategy = false.

  Let cs := cs_init zc.
  Let WS := Z.shiftl 1 (di_wb9 wb).
  Let HS := Z.shiftl 1 (memLevel + 7).
  Let LBS := Z.shiftl 1 (memLevel + 6).

  Definition dinit_events (r0 rw rp rh rb : option Z) : list hevent :=
    [HEmalloc (mul32 LBS LIT_BUFS) rb; HEmalloc (mul32 HS 2) rh; HEmalloc (mul32 WS 2) rp;
     HEmalloc (mul32 WS 2) rw; HEmalloc (mul32 1 SIZEOF_deflate_state) r0].

  Definition init_state : deflate_state :=
    sLM (ho_garb o n) (ho_garb o (n + 1)) (ho_garb o (n + 2)) (ho_garb o (n + 3)) (ho_garb o (n + 4))
        (Z.to_N n) (Z.to_N (n + 1)) (Z.to_N (n + 2)) (Z.to_N (n + 3)) (Z.to_N (n + 4))
        cs (di_wrap wb) (di_wb9 wb) memLevel (di_level level) strategy method.

  Let gr (r : option Z) : option (blk * (Z -> Z)) :=
    match r with Some k => Some (Z.to_N k, ho_garb o k) | None => None end.

  Let s1 := s_setup (ho_garb o n) (Z.to_N n) cs (di_wrap wb) (di_wb9 wb) memLevel.
  Let s5 := s_pb (s_lbs (s_hd (s_prv (s_win s1 (gr (hgrant o (n + 1)))) (gr (hgrant o (n + 2)))) (gr (hgrant o (n + 3)))) memLevel)
                 (gr (hgrant o (n + 4))).






End Init.


Definition uw_core (s : inflate_state) (src : arr) (end_ copy : Z) : inflate_state :=
  let s := if is_wsize s =? 0
           then iset_whave (iset_wnext (iset_wsize s (shl32 1 (is_wbits s))) 0) 0
           else s in
  if is_wsize s <=? copy then
    let s := iset_window s (arr_blit (is_window s) 0 src (end_ - is_wsize s) (is_wsize s)) in
    iset_whave (iset_wnext s 0) (is_wsize s)
  else
    let dist := wrap32 (is_wsize s - is_wnext s) in
    let dist := if copy <? dist then copy else dist in
    let s := iset_window s (arr_blit (is_window s) (is_wnext s) src (end_ - copy) dist) in
    let copy := wrap32 (copy - dist) in
    if negb (copy =? 0) then
      let s := iset_window s (arr_blit (is_window s) 0 src (end_ - copy) copy) in
      iset_whave (iset_wnext s copy) (is_wsize s)
    else
      let s := iset_wnext s (wrap32 (is_wnext s + dist)) in
      let s := if is_wnext s =? is_wsize s then iset_wnext s 0 else s in
      let s := if is_whave s <? is_wsize s then iset_whave s (wrap32 (is_whave s + dist)) else s in
      s.

Definition uw_fresh (s : inflate_state) (b : blk) (g : Z -> Z) : inflate_state :=
  iset_window (iset_window_blk s (Some b)) (iarr_u8_of g 0 (shl32 1 (is_wbits s))).



Definition leave_tail (flush : Z) (s : inflate_state) (c : icall) (r : iregs) : inflate_state * ZRet :=
  let in_ := wrap32 (ir_in r - ic_avail_in c) in
  let out := wrap32 (ir_out r - ic_avail_out c) in
  let c := icset_total_in c (wrap64 (ic_total_in c + in_)) in
  let c := icset_total_out c (wrap64 (ic_total_out c + out)) in
  let s := iset_total s (wrap64 (is_total s + out)) in
  let '(s, c) :=
    if negb (Z.land (is_wrap s) 4 =? 0) && negb (out =? 0) then
      let v := UPDATE_CHECK_bytes s (is_check s)
                 (arr_slice (ic_outbuf c) (ic_next_out c - out) out) in
      (iset_check s v, icset_adler c v)
    else (s, c) in
  let c := icset_data_type c
             (is_bits s + (if negb (is_last s =? 0) then 64 else 0) +
              (if is_mode s =? TYPE then 128 else 0) +
              (if (is_mode s =? LEN_) || (is_mode s =? COPY_) then 256 else 0)) in
  let ret := if (((in_ =? 0) && (out =? 0)) || (flush =? Z_FINISH)) && (ir_ret r =? Z_OK)
             then Z_BUF_ERROR else ir_ret r in
  (s, zret_of_icall c ret).

Definition leave_need (flush : Z) (s : inflate_state) (c : icall) (r : iregs) : bool :=
  negb (is_wsize s =? 0) ||
  (negb (ir_out r =? ic_avail_out c) && (is_mode s <? BAD) && ((is_mode s <? CHECK) || negb (flush =? Z_FINISH))).

Section InflP.
  Variable iv : ivariant.

  Definition inf_leave_p (ans : option (blk * (Z -> Z))) (flush : Z) (w : iw) : (inflate_state * ZRet) * option Z :=
    let w := RESTORE w in
    let s := w_s w in let c := w_c w in let r := w_r w in
    let '(so, asked) :=
      if leave_need flush s c r then
        match is_window_blk s with
        | Some _ => (Some (uw_core s (ic_outbuf c) (ic_next_out c) (wrap32 (ir_out r - ic_avail_out c))), None)
        | None => (match ans with
                   | Some (b, g) => Some (uw_core (uw_fresh s b g) (ic_outbuf c) (ic_next_out c) (wrap32 (ir_out r - ic_avail_out c)))
                   | None => None
                   end, Some (mul32 (shl32 1 (is_wbits s)) 1))
        end
      else (Some s, None) in
    (match so with
     | None => (iset_mode s MEM, zret_of_icall c Z_MEM_ERROR)
     | Some s' => leave_tail flush s' c r
     end, asked).

  Definition inflate_p (ans : option (blk * (Z -> Z))) (s : inflate_state) (zc : ZCall) (flush : Z)
    : (inflate_state * ZRet) * option Z :=
    let c := icall_of_zcall zc in
    if inflateStateCheck s then ((s, zret_of_icall c Z_STREAM_ERROR), None)
    else
      let s := if is_mode s =? TYPE then iset_mode s TYPEDO else s in
      let w := mkW s c (mkIR 0 0 0 0 0 0 0 0 Z_OK) in
      let w := LOAD w in
      let w := wset_r w (irset_ret (irset_out (irset_in (w_r w) (ir_have (w_r w))) (ir_left (w_r w))) Z_OK) in
      let '(stop, w) := inf_loop iv flush w in
      match stop with
      | SRet rc => ((w_s w, zret_of_icall (w_c w) rc), None)
      | SLeave => inf_leave_p ans flush w
      end.

  Definition hans (o : horacle) (n : Z) : option (blk * (Z -> Z)) :=
    match hgrant o n with Some k => Some (Z.to_N k, ho_garb o k) | None => None end.

  Definition hstep (o : horacle) (n : Z) (log : list hevent) (bad : bool) (asked : option Z) : hst :=
    match asked with
    | Some size => mkHS o (n + 1) (HEmalloc size (hgrant o n) :: log) bad
    | None => mkHS o n log bad
    end.


End InflP.


Section IInit.
  Variable iv : ivariant.

  Definition iinit_pre (g : Z -> Z) (b : blk) : inflate_state :=
    iset_mode (iset_window (iset_window_blk (is_of_oracle (iv_lay iv) g b) None) (arr_make 0 0)) HEAD.

  Definition iinit_state (g : Z -> Z) (b : blk) (z : zstrm) : inflate_state * zstrm :=
    fst (inflateReset iv (iset_wbits (iset_wrap (iinit_pre g b) 5) 15) z).



End IInit.
