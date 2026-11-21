(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflate1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflate2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefAdler_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateInit_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateUpdw_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zlength_slice : forall (a : arr) n, 0 <= n -> zlength (arr_slice a 0 n) = n.
Proof. intros a n Hn. rewrite arr_slice_length. lia. Qed.

Definition s_entry (st : inflate_state) : inflate_state :=
  if is_mode st =? TYPE then iset_mode st TYPEDO else st.
Definition W0 (st : inflate_state) (zc : ZCall) : iw :=
  mkW (s_entry st) (icall_of_zcall zc)
      (mkIR 0 (zlength (zc_input zc)) 0 (zc_avail_out zc) (is_hold st) (is_bits st)
            (zlength (zc_input zc)) (zc_avail_out zc) Z_OK).

Lemma s_entry_facts : forall st,
  is_hold (s_entry st) = is_hold st /\ is_bits (s_entry st) = is_bits st /\ is_wsize (s_entry st) = is_wsize st
  /\ is_window (s_entry st) = is_window st /\ is_window_blk (s_entry st) = is_window_blk st
  /\ is_wbits (s_entry st) = is_wbits st /\ is_self_blk (s_entry st) = is_self_blk st
  /\ is_lens (s_entry st) = is_lens st /\ is_work (s_entry st) = is_work st /\ is_codes (s_entry st) = is_codes st
  /\ is_mode (s_entry st) = (if is_mode st =? TYPE then TYPEDO else is_mode st)
  /\ (iwf st -> iwf (s_entry st)).
Proof.
  intros st. unfold s_entry. destruct (Z.eqb_spec (is_mode st) TYPE) as [E|E].
  - repeat (split; [reflexivity|]). apply iwf_set_mode. unfold TYPEDO, HEAD, SYNC; lia.
  - repeat (split; [reflexivity|]). intros H; exact H.
Qed.

Section Model.

  Context {St : Type} (hooks : zhooks St).
  Lemma inflate_m_W0 : forall st zc flush,
    inflateStateCheck st = false ->
    inflate_m ivar_ref hooks st zc flush
    = (let '(stop, w) := inf_loop ivar_ref flush (W0 st zc) in
       match stop with
       | SRet rc => sret (w_s w, zret_of_icall (w_c w) rc)
       | SLeave => inf_leave hooks flush w
       end).
  Proof.
    intros st zc flush Hc. unfold inflate_m. rewrite Hc. unfold W0, s_entry.
    destruct (is_mode st =? TYPE); reflexivity.
  Qed.
End Model.

Section ZS2.
Variable strm : Z.
Variable S : Z.
Variable fa : Z.
Variable ff : Z.
Hypothesis Hstrm : 0 <= strm /\ strm + 112 <= 2 ^ 63.
End ZS2.

Definition boxP (P : Prop) : Prop := P.

Ltac inl_tac := cbn; repeat (first [ left; reflexivity | right ]).

Section Proofs.
  Variable arm_ok : Z -> iw -> bool.

  Definition WNof (st : inflate_state) : Z := match is_window_blk st with Some _ => 2 ^ is_wbits st | None => 0 end.

  Hypothesis HSAFE : forall st zc flush,
    iwf st -> zstrm_ok (zc_strm zc) -> 0 <= zc_avail_out zc < 2 ^ 32 -> zlength (zc_input zc) < 2 ^ 32 ->
    bytes_ok (zc_input zc) -> 0 <= flush < 16 ->
    loop_ok arm_ok flush (W0 st zc) = true.

  Local Ltac dcs15 tac :=
    let r := fresh "rg" in let Hr := fresh "Hrg" in
    intros r Hr; cbn in Hr;
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]; tac.

  Definition dt_model (s : inflate_state) : Z :=
    is_bits s + (if negb (is_last s =? 0) then 64 else 0) + (if is_mode s =? TYPE then 128 else 0)
    + (if (is_mode s =? LEN_) || (is_mode s =? COPY_) then 256 else 0).

  Definition ret_model (flush in_ out : Z) (r : iregs) : Z :=
    if (((in_ =? 0) && (out =? 0)) || (flush =? Z_FINISH)) && (ir_ret r =? Z_OK) then Z_BUF_ERROR else ir_ret r.

  Definition lv_fin (flush : Z) (s : inflate_state) (c : icall) (r : iregs) : inflate_state * ZRet :=
    let in_ := wrap32 (ir_in r - ic_avail_in c) in
    let out := wrap32 (ir_out r - ic_avail_out c) in
    let c := icset_total_in c (wrap64 (ic_total_in c + in_)) in
    let c := icset_total_out c (wrap64 (ic_total_out c + out)) in
    let s := iset_total s (wrap64 (is_total s + out)) in
    let '(s, c) :=
      if negb (Z.land (is_wrap s) 4 =? 0) && negb (out =? 0) then
        let v := UPDATE_CHECK_bytes s (is_check s) (arr_slice (ic_outbuf c) (ic_next_out c - out) out) in
        (iset_check s v, icset_adler c v)
      else (s, c) in
    (s, zret_of_icall (icset_data_type c (dt_model s)) (ret_model flush in_ out r)).
  Definition s_rest (s : inflate_state) (r : iregs) : inflate_state := iset_bits (iset_hold s (ir_hold r)) (ir_bits r).
  Definition c_rest (c : icall) (r : iregs) : icall :=
    icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r).

  Definition lv_cond (flush : Z) (s : inflate_state) (c : icall) (r : iregs) : bool :=
    negb (is_wsize s =? 0) || (negb (wrap32 (ir_out r - ic_avail_out c) =? 0) && (is_mode s <? BAD) && ((is_mode s <? CHECK) || negb (flush =? Z_FINISH))).

  Definition lv_pre (s : inflate_state) (c : icall) (r : iregs) : inflate_state * icall :=
    let in_ := wrap32 (ir_in r - ic_avail_in c) in
    let out := wrap32 (ir_out r - ic_avail_out c) in
    let c := icset_total_in c (wrap64 (ic_total_in c + in_)) in
    let c := icset_total_out c (wrap64 (ic_total_out c + out)) in
    let s := iset_total s (wrap64 (is_total s + out)) in
    let '(s, c) :=
      if negb (Z.land (is_wrap s) 4 =? 0) && negb (out =? 0) then
        let v := UPDATE_CHECK_bytes s (is_check s) (arr_slice (ic_outbuf c) (ic_next_out c - out) out) in
        (iset_check s v, icset_adler c v)
      else (s, c) in
    (s, icset_data_type c (dt_model s)).

  Definition lv_mem (s : inflate_state) (c : icall) (r : iregs) : inflate_state * ZRet :=
    (iset_mode (fst (lv_pre s c r)) MEM, zret_of_icall (snd (lv_pre s c r)) Z_MEM_ERROR).

  Lemma lv_fin_pre : forall flush s c r,
    lv_fin flush s c r
    = (fst (lv_pre s c r), zret_of_icall (snd (lv_pre s c r)) (ret_model flush (wrap32 (ir_in r - ic_avail_in c)) (wrap32 (ir_out r - ic_avail_out c)) r)).
  Proof.
    intros. unfold lv_fin, lv_pre. cbv zeta.
    lazymatch goal with |- (let '(a, b) := (if ?cnd then _ else _) in _) = _ => destruct cnd; reflexivity end.
  Qed.

  Lemma lv_pre_fields : forall s c r,
    is_wsize (fst (lv_pre s c r)) = is_wsize s /\ is_mode (fst (lv_pre s c r)) = is_mode s
    /\ is_window_blk (fst (lv_pre s c r)) = is_window_blk s /\ is_wbits (fst (lv_pre s c r)) = is_wbits s
    /\ ic_outbuf (snd (lv_pre s c r)) = ic_outbuf c /\ ic_next_out (snd (lv_pre s c r)) = ic_next_out c.
  Proof.
    intros. unfold lv_pre. cbv zeta.
    lazymatch goal with |- context [if ?cnd then _ else _] => destruct cnd end; cbn [fst snd]; repeat split; reflexivity.
  Qed.

  Local Ltac saccA :=
    cbn [is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize
         is_whave is_wnext is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode
         is_distcode is_lenbits is_distbits is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes
         is_sane is_back is_was is_self_blk is_reqwrap is_reqbits
         iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits
         iset_wsize iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset
         iset_extra iset_lencode iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have
         iset_next iset_lens iset_work iset_codes iset_sane iset_back iset_was iset_self_blk iset_reqwrap iset_reqbits
         ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler
         ic_data_type ic_msg
         icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out
         icset_adler icset_data_type icset_msg fst snd].

  Lemma updw_core_comm : forall (f : inflate_state -> inflate_state),
    (forall x, is_wsize (f x) = is_wsize x) -> (forall x, is_wnext (f x) = is_wnext x) -> (forall x, is_whave (f x) = is_whave x) ->
    (forall x, is_window (f x) = is_window x) -> (forall x, is_wbits (f x) = is_wbits x) ->
    (forall x v, f (iset_wsize x v) = iset_wsize (f x) v) -> (forall x v, f (iset_wnext x v) = iset_wnext (f x) v) ->
    (forall x v, f (iset_whave x v) = iset_whave (f x) v) -> (forall x v, f (iset_window x v) = iset_window (f x) v) ->
    forall s src e copy, f (updw_core s src e copy) = updw_core (f s) src e copy.
  Proof.
    intros f R1 R2 R3 R4 R5 C1 C2 C3 C4 s src e copy. unfold updw_core.
    assert (EA : RefUpdWin1.sA (f s) = f (RefUpdWin1.sA s)).
    { unfold RefUpdWin1.sA. rewrite R1, R5. destruct (is_wsize s =? 0); [rewrite C3, C2, C1|]; reflexivity. }
    rewrite EA. set (x := RefUpdWin1.sA s). clearbody x. cbv zeta.
    Local Ltac norm_f R1 R2 R3 R4 C2 C3 C4 := saccA; rewrite ?R1, ?R2, ?R3, ?R4; rewrite ?C3, ?C2, ?C4; saccA; rewrite ?R1, ?R2, ?R3, ?R4.
    norm_f R1 R2 R3 R4 C2 C3 C4.
    destruct (is_wsize x <=? copy); [norm_f R1 R2 R3 R4 C2 C3 C4; reflexivity|].
    norm_f R1 R2 R3 R4 C2 C3 C4.
    repeat (match goal with |- context [if ?cnd then _ else _] =>
              lazymatch cnd with context [if _ then _ else _] => fail | _ => destruct cnd end end; norm_f R1 R2 R3 R4 C2 C3 C4); reflexivity.
  Qed.

  Lemma bk_updw : forall (b : bool) t v s src e copy,
    (if b then iset_check (iset_total (updw_core s src e copy) t) v else iset_total (updw_core s src e copy) t)
    = updw_core (if b then iset_check (iset_total s t) v else iset_total s t) src e copy.
  Proof.
    intros b t v s src e copy. destruct b.
    - apply (updw_core_comm (fun x => iset_check (iset_total x t) v)); intros; destruct x; reflexivity.
    - apply (updw_core_comm (fun x => iset_total x t)); intros; destruct x; reflexivity.
  Qed.
  Lemma bk_fresh : forall (b : bool) t v s wb w,
    (if b then iset_check (iset_total (iset_window (iset_window_blk s wb) w) t) v else iset_total (iset_window (iset_window_blk s wb) w) t)
    = iset_window (iset_window_blk (if b then iset_check (iset_total s t) v else iset_total s t) wb) w.
  Proof. intros b t v s wb w. destruct b; destruct s; reflexivity. Qed.

  Lemma lv_pre_shape : forall s c r,
    lv_pre s c r
    = (let out := wrap32 (ir_out r - ic_avail_out c) in
       let b := negb (Z.land (is_wrap s) 4 =? 0) && negb (out =? 0) in
       let t := wrap64 (is_total s + out) in
       let c2 := icset_total_out (icset_total_in c (wrap64 (ic_total_in c + wrap32 (ir_in r - ic_avail_in c)))) (wrap64 (ic_total_out c + out)) in
       let v := UPDATE_CHECK_bytes s (is_check s) (arr_slice (ic_outbuf c) (ic_next_out c - out) out) in
       ((if b then iset_check (iset_total s t) v else iset_total s t),
        icset_data_type (if b then icset_adler c2 v else c2) (dt_model s))).
  Proof.
    intros. unfold lv_pre. cbv zeta. saccA.
    destruct (negb (Z.land (is_wrap s) 4 =? 0) && negb (wrap32 (ir_out r - ic_avail_out c) =? 0)); cbn [fst snd]; reflexivity.
  Qed.

  Lemma lv_pre_updw : forall s c r src e copy,
    lv_pre (updw_core s src e copy) c r = (updw_core (fst (lv_pre s c r)) src e copy, snd (lv_pre s c r)).
  Proof.
    intros. rewrite !lv_pre_shape. cbv zeta. cbn [fst snd].
    assert (F : is_wrap (updw_core s src e copy) = is_wrap s /\ is_check (updw_core s src e copy) = is_check s
                /\ is_flags (updw_core s src e copy) = is_flags s /\ is_total (updw_core s src e copy) = is_total s
                /\ is_bits (updw_core s src e copy) = is_bits s /\ is_last (updw_core s src e copy) = is_last s
                /\ is_mode (updw_core s src e copy) = is_mode s).
    { unfold updw_core, RefUpdWin1.sA. saccA.
      repeat lazymatch goal with |- context [if ?cnd then _ else _] => destruct cnd end; saccA; repeat split; reflexivity. }
    destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    unfold UPDATE_CHECK_bytes, dt_model. rewrite F1, F2, F3, F4, F5, F6, F7. rewrite bk_updw. reflexivity.
  Qed.

  Lemma lv_pre_fresh : forall s c r wb w,
    lv_pre (iset_window (iset_window_blk s wb) w) c r
    = (iset_window (iset_window_blk (fst (lv_pre s c r)) wb) w, snd (lv_pre s c r)).
  Proof.
    intros. rewrite !lv_pre_shape. cbv zeta. cbn [fst snd]. unfold UPDATE_CHECK_bytes, dt_model. saccA. rewrite bk_fresh. reflexivity.
  Qed.

  Lemma inf_leave_eq0 : forall {St'} (hooks : zhooks St') flush s c r (g : St'),
    inf_leave hooks flush (mkW s c r) g
    = sbind (if lv_cond flush (s_rest s r) (c_rest c r) r
             then updatewindow hooks (fst (lv_pre (s_rest s r) (c_rest c r) r)) (ic_outbuf (c_rest c r)) (ic_next_out (c_rest c r))
                               (wrap32 (ir_out r - ic_avail_out (c_rest c r)))
             else sret (Some (fst (lv_pre (s_rest s r) (c_rest c r) r))))
            (fun so => match so with
                       | None => sret (lv_mem (s_rest s r) (c_rest c r) r)
                       | Some s' => sret (s', zret_of_icall (snd (lv_pre (s_rest s r) (c_rest c r) r))
                                                (ret_model flush (wrap32 (ir_in r - ic_avail_in (c_rest c r))) (wrap32 (ir_out r - ic_avail_out (c_rest c r))) r))
                       end) g.
  Proof.
    intros. unfold inf_leave, lv_mem, lv_pre, lv_cond, ret_model, dt_model. cbn [w_s w_c w_r RESTORE].
    change (iset_bits (iset_hold s (ir_hold r)) (ir_bits r)) with (s_rest s r).
    change (icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)) with (c_rest c r).
    cbv zeta.
    lazymatch goal with |- context [if negb (Z.land ?w 4 =? 0) && ?o then _ else _] => destruct (negb (Z.land w 4 =? 0) && o) end; reflexivity.
  Qed.

  Lemma inf_leave_eq : forall {St'} (hooks : zhooks St') flush s c r (g : St'),
    inf_leave hooks flush (mkW s c r) g
    = sbind (if lv_cond flush (s_rest s r) (c_rest c r) r
             then updatewindow hooks (s_rest s r) (ic_outbuf (c_rest c r)) (ic_next_out (c_rest c r)) (wrap32 (ir_out r - ic_avail_out (c_rest c r)))
             else sret (Some (s_rest s r)))
            (fun so => match so with
                       | None => sret (lv_mem (s_rest s r) (c_rest c r) r)
                       | Some s' => sret (lv_fin flush s' (c_rest c r) r)
                       end) g.
  Proof.
    intros. rewrite inf_leave_eq0.
    set (S0 := s_rest s r). set (C0 := c_rest c r).
    destruct (lv_pre_fields S0 C0 r) as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct (lv_cond flush S0 C0 r).
    2:{ unfold sbind, sret. cbn [mbind fst snd]. rewrite lv_fin_pre. reflexivity. }
    destruct (is_window_blk S0) as [b|] eqn:EB.
    - rewrite (updatewindow_some hooks (fst (lv_pre S0 C0 r)) _ _ _ b) by exact F3.
      rewrite (updatewindow_some hooks S0 _ _ _ b EB).
      unfold sbind, sret. cbn [mbind fst snd]. rewrite lv_fin_pre, lv_pre_updw. reflexivity.
    - rewrite !updatewindow_unfold. rewrite F3, EB, F4.
      rewrite !sbind_assoc.
      assert (SE : forall {A B} (m : SM St' A) (f f' : A -> SM St' B) g0, (forall a g1, f a g1 = f' a g1) -> sbind m f g0 = sbind m f' g0).
      { intros A B m f f' g0 H. unfold sbind. f_equal. extensionality p. destruct p. apply H. }
      apply SE. intros a g1. destruct a as [[b g']|].
      + rewrite !sbind_ret_l. rewrite !updw_body_eq. rewrite !sbind_ret_l.
        rewrite lv_fin_pre, lv_pre_updw, lv_pre_fresh. cbn [fst snd]. reflexivity.
      + rewrite !sbind_ret_l. reflexivity.
  Qed.

  Definition lv_s2 (s : inflate_state) (out : Z) : inflate_state := iset_total s (wrap64 (is_total s + out)).
  Definition lv_c2 (c : icall) (in_ out : Z) : icall :=
    icset_total_out (icset_total_in c (wrap64 (ic_total_in c + in_))) (wrap64 (ic_total_out c + out)).

End Proofs.
