(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateUpdw_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateUpdw_run.RefInflateInit_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.

Module RefInflate_runA.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateRel.RefInflateInit1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCtx.RefInflate1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateCtx.RefInflate2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefAdler_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateUpdw_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateUpdw_run.RefInflateInit_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateUpdw_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zlength_slice : forall (a : arr) n, 0 <= n -> zlength (arr_slice a 0 n) = n.
Proof. intros a n Hn. rewrite arr_slice_length. lia. Qed.

Lemma bytes_ok_slice : forall (a : arr) n,
  (forall i, 0 <= i < n -> 0 <= arr_get a i < 256) -> bytes_ok (arr_slice a 0 n).
Proof.
  intros a n Hb. unfold bytes_ok. rewrite Forall_forall. intros x Hin.
  apply In_nth with (d := 0) in Hin. destruct Hin as (k & Hk & <-).
  pose proof (arr_slice_length a 0 n) as HL. unfold zlength in HL.
  pose proof (arr_slice_nth a 0 n (Z.of_nat k) 0 ltac:(lia)) as E. unfold ZIface.znth in E.
  rewrite (proj2 (Z.ltb_ge (Z.of_nat k) 0)) in E by lia. rewrite Nat2Z.id in E. rewrite E. apply Hb. lia.
Qed.

Lemma arr_get_of_list : forall l i, 0 <= i < zlength l -> arr_get (arr_of_list l) i = ZIface.znth 0 l i.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb, arr_make. rewrite arr_len_init.
  replace ((0 <=? i) && (i <? 0 + zlength l) && ((0 <=? i) && (i <? zlength l))) with true
    by (symmetry; rewrite !andb_true_iff; rewrite !Z.leb_le, !Z.ltb_lt; lia).
  unfold ZIface.znth. rewrite (proj2 (Z.ltb_ge i 0)) by lia. rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma iwf_set_holdbits : forall st h b, 0 <= b < 64 -> 0 <= h < 2 ^ b -> iwf st -> iwf (iset_bits (iset_hold st h) b).
Proof.
  intros st h b Hb Hh H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.
Lemma iwf_set_total : forall st v, 0 <= v < 2 ^ 64 -> iwf st -> iwf (iset_total st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.
Lemma iwf_set_check : forall st v, 0 <= v < 2 ^ 64 -> iwf st -> iwf (iset_check st v).
Proof.
  intros st v Hv H. unfold iwf, iwfx in *. destruct st; cbn -[Z.pow Z.le Z.lt Z.add Z.sub Z.mul Z.opp arr_get arr_len HEAD SYNC] in *.
  decompose [and] H. repeat apply conj; first [assumption | lia].
Qed.

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
  (* inflate.c inf_leave: a failed window update returns Z_MEM_ERROR before total_in / total_out / total / check /
     data_type are written *)
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

  (* zl14infl-r2 drops inf_leave_eq0 (1.4's inf_leave runs updatewindow before the totals; see inf_leave_eq) *)
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

  Lemma c_rest_facts : forall c r,
    ic_next_in (c_rest c r) = ir_next r /\ ic_avail_in (c_rest c r) = ir_have r /\ ic_next_out (c_rest c r) = ir_put r
    /\ ic_avail_out (c_rest c r) = ir_left r /\ ic_outbuf (c_rest c r) = ic_outbuf c /\ ic_input (c_rest c r) = ic_input c
    /\ ic_total_in (c_rest c r) = ic_total_in c /\ ic_total_out (c_rest c r) = ic_total_out c /\ ic_adler (c_rest c r) = ic_adler c
    /\ ic_data_type (c_rest c r) = ic_data_type c /\ ic_msg (c_rest c r) = ic_msg c.
  Proof. intros. repeat split; reflexivity. Qed.
  Lemma s_rest_facts : forall s r,
    is_bits (s_rest s r) = ir_bits r /\ is_hold (s_rest s r) = ir_hold r /\ is_mode (s_rest s r) = is_mode s /\ is_wsize (s_rest s r) = is_wsize s
    /\ is_wrap (s_rest s r) = is_wrap s /\ is_flags (s_rest s r) = is_flags s /\ is_check (s_rest s r) = is_check s
    /\ is_window_blk (s_rest s r) = is_window_blk s /\ is_wbits (s_rest s r) = is_wbits s /\ is_self_blk (s_rest s r) = is_self_blk s
    /\ is_window (s_rest s r) = is_window s /\ is_lens (s_rest s r) = is_lens s /\ is_work (s_rest s r) = is_work s /\ is_codes (s_rest s r) = is_codes s
    /\ is_total (s_rest s r) = is_total s /\ is_last (s_rest s r) = is_last s.
  Proof. intros. repeat split; reflexivity. Qed.

  Definition lv_s2 (s : inflate_state) (out : Z) : inflate_state := iset_total s (wrap64 (is_total s + out)).
  Definition lv_c2 (c : icall) (in_ out : Z) : icall :=
    icset_total_out (icset_total_in c (wrap64 (ic_total_in c + in_))) (wrap64 (ic_total_out c + out)).

  Lemma lv_fin_nocheck : forall flush s c r in_ out,
    in_ = wrap32 (ir_in r - ic_avail_in c) -> out = wrap32 (ir_out r - ic_avail_out c) ->
    (Z.land (is_wrap s) 4 = 0 \/ out = 0) ->
    lv_fin flush s c r = (lv_s2 s out, zret_of_icall (icset_data_type (lv_c2 c in_ out) (dt_model (lv_s2 s out))) (ret_model flush in_ out r)).
  Proof.
    intros flush s c r in_ out -> -> Hc. unfold lv_fin, lv_s2, lv_c2.
    replace (is_wrap (iset_total s (wrap64 (is_total s + wrap32 (ir_out r - ic_avail_out c))))) with (is_wrap s) by (destruct s; reflexivity).
    destruct Hc as [Hc|Hc]; rewrite Hc, ?Z.eqb_refl; cbn [negb andb]; [| rewrite Bool.andb_false_r]; reflexivity.
  Qed.
  Lemma lv_fin_check : forall flush s c r in_ out,
    in_ = wrap32 (ir_in r - ic_avail_in c) -> out = wrap32 (ir_out r - ic_avail_out c) ->
    Z.land (is_wrap s) 4 <> 0 -> out <> 0 ->
    let v := UPDATE_CHECK_bytes s (is_check s) (arr_slice (ic_outbuf c) (ic_next_out c - out) out) in
    lv_fin flush s c r = (iset_check (lv_s2 s out) v,
                          zret_of_icall (icset_data_type (icset_adler (lv_c2 c in_ out) v) (dt_model (iset_check (lv_s2 s out) v))) (ret_model flush in_ out r)).
  Proof.
    intros flush s c r in_ out -> -> Hw Ho. unfold lv_fin, lv_s2, lv_c2. cbv zeta.
    replace (is_wrap (iset_total s (wrap64 (is_total s + wrap32 (ir_out r - ic_avail_out c))))) with (is_wrap s) by (destruct s; reflexivity).
    replace (is_check (iset_total s (wrap64 (is_total s + wrap32 (ir_out r - ic_avail_out c))))) with (is_check s) by (destruct s; reflexivity).
    replace (ic_outbuf (icset_total_out (icset_total_in c (wrap64 (ic_total_in c + wrap32 (ir_in r - ic_avail_in c)))) (wrap64 (ic_total_out c + wrap32 (ir_out r - ic_avail_out c)))))
      with (ic_outbuf c) by (destruct c; reflexivity).
    replace (ic_next_out (icset_total_out (icset_total_in c (wrap64 (ic_total_in c + wrap32 (ir_in r - ic_avail_in c)))) (wrap64 (ic_total_out c + wrap32 (ir_out r - ic_avail_out c)))))
      with (ic_next_out c) by (destruct c; reflexivity).
    rewrite (proj2 (Z.eqb_neq _ _) Hw), (proj2 (Z.eqb_neq _ _) Ho). cbn [negb andb].
    unfold UPDATE_CHECK_bytes.
    replace (is_flags (iset_total s (wrap64 (is_total s + wrap32 (ir_out r - ic_avail_out c))))) with (is_flags s) by (destruct s; reflexivity).
    reflexivity.
  Qed.


  Lemma iset_hold_bits_comm : forall s h b, iset_hold (iset_bits s b) h = iset_bits (iset_hold s h) b.
  Proof. intros s h b. destruct s. reflexivity. Qed.
  Lemma iset_mode_facts : forall s v,
    is_window_blk (iset_mode s v) = is_window_blk s /\ is_window (iset_mode s v) = is_window s
    /\ is_self_blk (iset_mode s v) = is_self_blk s /\ iblocks (iset_mode s v) = iblocks s
    /\ is_lens (iset_mode s v) = is_lens s /\ is_work (iset_mode s v) = is_work s /\ is_codes (iset_mode s v) = is_codes s
    /\ is_wbits (iset_mode s v) = is_wbits s.
  Proof. intros s v. destruct s. repeat split; reflexivity. Qed.

End Proofs.
End RefInflate_runA.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.

Module RefInflateSafeA2.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section StoredArms.
  Variable iv : ivariant.
Variable flush : Z.

  Lemma arm_COPY_safe : arm_safe COPY arm_COPY.
  Proof.
    intros w0 s c r HW E HP. unfold arm_COPY. arun gs_eq. cbv zeta.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8]. pose proof (CORE_length s HC) as HL0.
    acase Clen.
    - arun gr_eq. cbv zeta.
      match goal with |- POST _ ((if ?x =? 0 then _ else _) _) => set (cp := x) in * end.
      assert (Hcp : 0 <= cp /\ cp <= ir_have r /\ cp <= ir_left r /\ cp <= is_length s).
      { subst cp. destruct (Z.ltb_spec (ir_have r) (is_length s));
          [destruct (Z.ltb_spec (ir_left r) (ir_have r)) | destruct (Z.ltb_spec (ir_left r) (is_length s))]; lia. }
      acase Ccp.
      + aleave. exact HW0.
      + apply Z.eqb_neq in Ccp.
        aflat. arun uc_eq. aflat. arun ur_eq. rewrite us_eq. apply POST_ARun.
        * winv_split.
          -- core_keep HC. apply wrap32_range.
          -- apply REGS_copy; [exact HR | apply arr_len_blit | lia | lia | lia].
          -- rewrite E. mred. split; [common_keep HCm | exact Hb8].
          -- rewrite E. mred. rewrite arr_len_blit. exact HWF.
          -- intros W. exfalso. exact (proj1 HCm W).
        * phi_norm E HP. rewrite !wrap32_id by lia. lia.
    - rewrite set_mode_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * exact HR.
        * split; [common_keep HCm | exact Hb8].
        * exact HWF.
        * exact HWB.
      + phi_norm E HP. lia.
  Qed.

  Lemma arm_COPY__safe : arm_safe COPY_ arm_COPY_.
  Proof.
    intros w0 s c r HW E HP. unfold arm_COPY_. arun set_mode_eq.
    winv_open2 HW E HC HR. destruct HMF as [HCm Hb8].
    apply (POST_arm COPY arm_COPY _ _ _ _ arm_COPY_safe).
    - winv_split.
      + core_keep HC. apply CORE_length; exact HC.
      + exact HR.
      + split; [common_keep HCm | exact Hb8].
      + exact HWF.
      + exact HWB.
    - reflexivity.
    - phi_norm E HP. lia.
  Qed.

  Lemma arm_STORED_safe : arm_safe STORED (arm_STORED iv flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_STORED.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    arun BYTEBITS_eq.
    pose proof (land7_mod (ir_bits r) ltac:(lia)) as L7.
    assert (Hm8 : 0 <= ir_bits r mod 8 <= ir_bits r) by (split; [apply Z.mod_pos_bound; lia|apply Z.mod_le; lia]).
    set (rb := irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7))).
    assert (HRb : REGS c rb) by (subst rb; apply REGS_drop; [exact HR|lia]).
    assert (Ebb : ir_bits rb = ir_bits r - ir_bits r mod 8) by (subst rb; sacc; rewrite L7; apply wrap32_id; lia).
    assert (Eob : ir_out rb = ir_out r /\ ir_put rb = ir_put r /\ ir_left rb = ir_left r /\ ir_have rb = ir_have r) by (subst rb; sacc; repeat split; reflexivity).
    destruct Eob as (Eob & Epb & Elb & Ehb).
    destruct (NEEDBITS_spec c 32 s rb HRb ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta.
      pose proof (pulled_out rb r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi rb r1 HP1) as PH1.
      rewrite Eob in Eo1. rewrite Epb in Ep1. rewrite Elb in El1. rewrite Elb, Ehb, Ebb in PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      arun HOLD_eq. acase Cbad.
      + arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
        * winv_split.
          -- core_keep HC. apply CORE_length; exact HC.
          -- eapply REGS_cview; [exact HR1 | reflexivity | reflexivity].
          -- exact (proj2 HMF).
          -- exact I.
          -- rewrite Ep1. exact HWB.
        * phi_norm E HP. lia.
      + aflat. arun us_eq. aflat. arun INITBITS_eq. aflat. arun set_mode_eq.
        match goal with |- POST _ (_ ?w) => assert (HW2 : WINV w) end.
        { winv_split.
          - core_keep HC. pose proof (land_65535 (wrap32 (ir_hold r1))). lia.
          - apply REGS_init. exact HR1.
          - split; [common_keep HMF|]. lia.
          - rewrite Eo1. exact HWF.
          - rewrite Ep1. exact HWB. }
        acase Cz.
        * aleave. exact HW2.
        * match goal with |- POST _ (_ (mkW ?s2 ?c2 ?r2)) => apply (POST_arm COPY_ arm_COPY_ w0 s2 c2 r2 arm_COPY__safe HW2) end.
          -- reflexivity.
          -- phi_norm E HP. lia.
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out rb r1 HP1) as (Eo1 & Ep1 & _). rewrite Eob in Eo1. rewrite Epb in Ep1.
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  Qed.
End StoredArms.


Section DictArms.
  Variable iv : ivariant.
Variable flush : Z.

  Lemma arm_DICT_safe : arm_safe DICT (arm_DICT iv flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_DICT. arun gs_eq.
    winv_open2 HW E HC HR. destruct HMF as [HWb Hb8].
    acase Chd.
    - (* zlib 1.4: total_in += in - avail_in after RESTORE, before Z_NEED_DICT *)
      arun amodify_eq. arun gr_eq. arun uc_eq. aleave. unfold RESTORE. cbn [w_s w_c w_r]. split.
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * eapply REGS_cview; [exact HR | reflexivity | reflexivity].
        * rewrite E. mred. split; [exact HWb | exact Hb8].
        * rewrite E. mred. exact HWF.
        * exact HWB.
      + unfold INV. sacc. rewrite E. mred. split; [core_keep HC; apply CORE_length; exact HC|].
        split; [|split; [exact HWb | exact Hb8]]. destruct HR as (_ & _ & _ & _ & _ & _ & HBr & _). exact HBr.
    - aflat. arun set_adler_check_eq. arun set_mode_eq.
      apply (POST_arm TYPE (arm_TYPE iv flush) _ _ _ _ (arm_TYPE_safe iv flush)).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * eapply REGS_cview; [exact HR | reflexivity | reflexivity].
        * split; [|exact Hb8]. split; [exact HWb|]. intros _. exact adler_canon_1.
        * exact HWF.
        * exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
  Qed.

  Lemma arm_DICTID_safe : arm_safe DICTID (arm_DICTID iv flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_DICTID.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      arun HOLD_eq. aflat. arun set_adler_check_eq. aflat. arun INITBITS_eq. aflat. arun set_mode_eq.
      apply (POST_arm DICT (arm_DICT iv flush) _ _ _ _ arm_DICT_safe).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * eapply REGS_cview; [apply REGS_init; exact HR1 | reflexivity | reflexivity].
        * split; [exact (proj1 HMF) | lia].
        * rewrite Eo1. exact HWF.
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  Qed.
End DictArms.
End RefInflateSafeA2.

Module RefInflateSafeA4.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition canon_b (a : Z) : bool := (0 <=? a) && (a <? 2 ^ 32) && (lo16 a <? ABASE) && (hi16 a <? ABASE).
Lemma canon_b_ok : forall a, canon_b a = true -> adler_canon a.
Proof.
  intros a H. unfold canon_b in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. unfold adler_canon. lia.
Qed.
Lemma adler_canon_0 : adler_canon 0.
Proof. apply canon_b_ok. vm_compute. reflexivity. Qed.

Lemma gz_magic_crc_canon : adler_canon (icrc32_upd icrc32_init [31; 139]).
Proof. apply canon_b_ok. vm_compute. reflexivity. Qed.

Lemma hcrc_on_flags : forall s, hcrc_on s = true -> is_flags s <> 0.
Proof.
  intros s H F. unfold hcrc_on in H. rewrite F in H. cbn in H. discriminate H.
Qed.

Lemma common_hcrc : forall s s1 s', common s -> hcrc_on s1 = true -> is_flags s1 = is_flags s ->
  is_wbits s' = is_wbits s -> is_flags s' = is_flags s -> common s'.
Proof.
  intros s s1 s' [W F] Hh E1 E2 E3. unfold common. rewrite E2, E3. split; [exact W|].
  intros F0. exfalso. apply (hcrc_on_flags s1 Hh). rewrite E1. exact F0.
Qed.

Lemma land_flag_nz : forall f m, Z.land f m <> 0 -> f <> 0.
Proof. intros f m H F. apply H. rewrite F. apply Z.land_0_l. Qed.

Lemma CORE_wbits : forall s v, CORE s -> is_wbits s = 0 -> v <> 0 -> CORE (iset_wbits s v).
Proof.
  intros s v HC W Hv. pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
  destruct (C9 W) as [N Wr]. pose proof (C1 N) as Z0.
  unfold CORE. sacc. rewrite N, Z0. repeat (split; [first [assumption | congruence | lia] |]). lia.
Qed.

Lemma scan_zero_spec : forall input next have, 0 < have < 2 ^ 32 ->
  let '(copy, _) := scan_zero input next have in 1 <= copy <= have.
Proof.
  intros input next have Hh.
  assert (GEN : forall m k l, 0 <= k < have -> have - k <= Z.of_nat m ->
    let '(copy, _) := loopZ (Z.of_nat m)
        (fun cl : Z * Z => let '(copy, _) := cl in
           let len := arr_get input (next + copy) in
           let copy := wrap32 (copy + 1) in
           (negb (len =? 0) && (copy <? have), (copy, len))) (k, l) in k + 1 <= copy <= have).
  { induction m as [|m IH]; intros k l Hk Hm; [cbn in Hm; lia|].
    rewrite loopZ_step by lia. cbv beta iota zeta.
    rewrite (wrap32_id (k + 1)) by lia.
    destruct (negb (arr_get input (next + k) =? 0) && (k + 1 <? have)) eqn:C.
    - apply andb_prop in C as [_ C]. apply Z.ltb_lt in C.
      replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
      specialize (IH (k + 1) (arr_get input (next + k)) ltac:(lia) ltac:(lia)).
      destruct (loopZ _ _ _) as [cp ln]. lia.
    - lia. }
  unfold scan_zero. specialize (GEN (Z.to_nat have) 0 0 ltac:(lia) ltac:(lia)).
  rewrite Z2Nat.id in GEN by lia. cbv zeta in GEN. exact GEN.
Qed.

Section HeaderArms.
  Variable iv : ivariant.
Variable flush : Z.


  Lemma arm_HCRC_safe : arm_safe HCRC arm_HCRC.
  Proof.
    intros w0 s c r HW E HP. unfold arm_HCRC. arun gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    pose proof (CORE_length s HC) as HL0.
    acase Cf.
    - aflat.
      destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply POST_bind_run; [exact EQ|]. cbv beta iota.
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
        aflat. arun HOLD_eq. aflat. arun gs_eq. acase Cbad.
        * aflat. arun go_bad_eq. arun aret_eq. rewrite aret_eq. apply POST_ARun.
          -- winv_split.
             ++ core_keep HC. exact HL0.
             ++ eapply REGS_cview; [exact HR1 | reflexivity | reflexivity].
             ++ exact (proj2 HCm).
             ++ exact I.
             ++ rewrite Ep1. exact HWB.
          -- phi_norm E HP. lia.
        * aflat. arun INITBITS_eq. arun aret_eq. aflat. arun set_adler_check_eq. rewrite set_mode_eq. apply POST_ARun.
          -- winv_split.
             ++ core_keep HC. exact HL0.
             ++ eapply REGS_cview; [apply REGS_init; exact HR1 | reflexivity | reflexivity].
             ++ split; [|cbn; lia]. split; [exact (proj1 HCm)|]. intros _. exact adler_canon_0.
             ++ rewrite Eo1. exact HWF.
             ++ rewrite Ep1. exact HWB.
          -- phi_norm E HP. lia.
      + eapply POST_bind_leave; [exact EQ|].
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
        apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. split; [exact HCm|].
        intros F0. rewrite F0 in Cf. discriminate Cf.
    - arun aret_eq. aflat. arun set_adler_check_eq. rewrite set_mode_eq.
      assert (F0 : Z.land (is_flags s) 512 = 0) by (destruct (Z.eqb_spec (Z.land (is_flags s) 512) 0); [assumption|discriminate Cf]).
      apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * eapply REGS_cview; [exact HR | reflexivity | reflexivity].
        * split; [|exact (Hb8 F0)]. split; [exact (proj1 HCm)|]. intros _. exact adler_canon_0.
        * exact HWF.
        * exact HWB.
      + phi_norm E HP. lia.
  Qed.


  Lemma POST_name_like : forall w0 flag s c r M (K : bool -> AM unit),
    WINV (mkW s c r) -> is_mode s = M -> (M = NAME \/ M = COMMENT) ->
    (forall w', WINV w' -> POST w0 (K false w')) ->
    (forall s' r', CORE s' -> REGS c r' -> common s' -> is_mode s' = M -> is_wbits s' = is_wbits s ->
                   is_length s' = is_length s ->
                   ir_bits r' = ir_bits r -> ir_hold r' = ir_hold r -> ir_out r' = ir_out r -> ir_put r' = ir_put r ->
                   ir_left r' = ir_left r -> 0 <= ir_have r' <= ir_have r ->
                   POST w0 (K true (mkW s' c r'))) ->
    POST w0 (abind (name_like flag) K (mkW s c r)).
  Proof.
    intros w0 flag s c r M K HW E HM KF KT.
    assert (HW' : CORE s /\ REGS c r /\ (common s /\ ir_bits r < 8) /\ ir_out r = arr_len (ic_outbuf c) /\ (is_wbits s = 0 -> ir_put r = 0)).
    { pose proof HW as HW1. destruct HM as [-> | ->]; [winv_open2 HW1 E HC HR | winv_open2 HW1 E HC HR]; repeat (split; [assumption|]); assumption. }
    destruct HW' as (HC & HR & [HCm Hb8] & HWF & HWB). regs_open HR.
    unfold name_like. aflat. arun gs_eq. acase Cf.
    - aflat. arun gr_eq. acase Ch0.
      + arun aret_eq. apply KF. exact HW.
      + apply Z.eqb_neq in Ch0. aflat. arun aget_eq. cbn [w_s w_c w_r].
        pose proof (scan_zero_spec (ic_input c) (ir_next r) (ir_have r) ltac:(lia)) as SZ.
        destruct (scan_zero (ic_input c) (ir_next r) (ir_have r)) as [copy len]. ired.
        assert (STEP : exists ck, (if hcrc_on s then crc_input copy else aret tt) (mkW s c r) = ARun tt (mkW (iset_check s ck) c r)
                       /\ (hcrc_on s = false -> ck = is_check s)).
        { destruct (hcrc_on s).
          - eexists. split; [reflexivity|]. intros X; discriminate X.
          - exists (is_check s). split; [|reflexivity]. unfold aret. f_equal. destruct s; reflexivity. }
        destruct STEP as (ck & STEP & Hck).
        aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun ur_eq.
        assert (HCm' : common (iset_check s ck)).
        { destruct (hcrc_on s) eqn:Hh.
          - eapply (common_hcrc s s); [exact HCm | exact Hh | reflexivity | reflexivity | reflexivity].
          - rewrite (Hck eq_refl). common_keep HCm. }
        rewrite (wrap32_id (ir_have r - copy)) by lia.
        acase Clen.
        * arun aret_eq. apply KF.
          unfold WINV. cbn [w_s w_c w_r]. sacc. rewrite E. split; [core_keep HC; apply CORE_length; exact HC|].
          split; [regs_solve RIN|].
          split; [destruct HM as [-> | ->]; mred; (split; [exact HCm'|exact Hb8])|].
          split; [destruct HM as [-> | ->]; mred; exact HWF|]. exact HWB.
        * arun aret_eq. apply KT; try reflexivity.
          -- core_keep HC. apply CORE_length; exact HC.
          -- regs_solve RIN.
          -- exact HCm'.
          -- sacc. exact E.
          -- sacc. lia.
    - arun aret_eq. apply KT; try reflexivity; try assumption. lia.
  Qed.

  Lemma arm_COMMENT_safe : arm_safe COMMENT arm_COMMENT.
  Proof.
    intros w0 s c r HW E HP. unfold arm_COMMENT.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    apply (POST_name_like w0 4096 s c r COMMENT _ HW0 E (or_intror eq_refl)).
    - intros w' HW'. cbv beta. aleave. exact HW'.
    - intros s' r' HC' HR' HCm' E' Ewb EL Eb Eh Eo Ep El Hh. cbv beta iota. arun set_mode_eq.
      apply (POST_arm HCRC arm_HCRC _ _ _ _ arm_HCRC_safe).
      + winv_split.
        * core_keep HC'. apply CORE_length; exact HC'.
        * exact HR'.
        * split; [common_keep HCm'|]. intros _. rewrite Eb. exact Hb8.
        * rewrite Eo. exact HWF.
        * rewrite Ep, Ewb. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
  Qed.

  Lemma arm_NAME_safe : arm_safe NAME arm_NAME.
  Proof.
    intros w0 s c r HW E HP. unfold arm_NAME.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    apply (POST_name_like w0 2048 s c r NAME _ HW0 E (or_introl eq_refl)).
    - intros w' HW'. cbv beta. aleave. exact HW'.
    - intros s' r' HC' HR' HCm' E' Ewb EL Eb Eh Eo Ep El Hh. cbv beta iota. aflat. arun us_eq. arun set_mode_eq.
      apply (POST_arm COMMENT arm_COMMENT _ _ _ _ arm_COMMENT_safe).
      + winv_split.
        * core_keep HC'. lia.
        * exact HR'.
        * split; [common_keep HCm'|]. rewrite Eb. exact Hb8.
        * rewrite Eo. exact HWF.
        * rewrite Ep, Ewb. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
  Qed.


  Lemma arm_EXTRA_safe : arm_safe EXTRA arm_EXTRA.
  Proof.
    intros w0 s c r HW E HP. unfold arm_EXTRA. arun gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    pose proof (CORE_length s HC) as HL0.
    assert (TAIL : forall s' r', CORE s' -> REGS c r' -> common s' -> is_wbits s' = is_wbits s ->
              ir_bits r' = ir_bits r -> ir_out r' = ir_out r -> ir_put r' = ir_put r -> ir_left r' = ir_left r -> 0 <= ir_have r' <= ir_have r ->
              POST w0 ((us (fun s0 => iset_length s0 0) ;; set_mode NAME ;; arm_NAME)%am (mkW s' c r'))).
    { intros s' r' HC' HR' HCm' Ewb Eb Eo Ep El Hh. aflat. arun us_eq. arun set_mode_eq.
      apply (POST_arm NAME arm_NAME _ _ _ _ arm_NAME_safe).
      - winv_split.
        + core_keep HC'. lia.
        + exact HR'.
        + split; [common_keep HCm'|]. rewrite Eb. exact Hb8.
        + rewrite Eo. exact HWF.
        + rewrite Ep, Ewb. exact HWB.
      - reflexivity.
      - phi_norm E HP. lia. }
    acase Cf.
    - aflat. arun gr_eq. cbv zeta.
      set (cp := if ir_have r <? is_length s then ir_have r else is_length s).
      assert (Hcp : 0 <= cp <= ir_have r /\ cp <= is_length s) by (subst cp; destruct (Z.ltb_spec (ir_have r) (is_length s)); lia).
      match goal with |- POST _ (abind (abind ?m _) _ ?w) =>
        assert (STEP : exists ck, m w = ARun tt (mkW (iset_length (iset_check s ck) (is_length s - cp)) c
                                                  (irset_next (irset_have r (ir_have r - cp)) (ir_next r + cp)))
                       /\ common (iset_check s ck))
      end.
      { destruct (negb (cp =? 0)) eqn:Ccp.
        - assert (CRC : exists ck, (if hcrc_on s then crc_input cp else aret tt) (mkW s c r) = ARun tt (mkW (iset_check s ck) c r)
                         /\ common (iset_check s ck)).
          { destruct (hcrc_on s) eqn:Hh.
            - eexists. split; [reflexivity|]. eapply (common_hcrc s s); [exact HCm | exact Hh | reflexivity | reflexivity | reflexivity].
            - exists (is_check s). split; [unfold aret; f_equal; destruct s; reflexivity|]. common_keep HCm. }
          destruct CRC as (ck & CRC & HCk). exists ck. split; [|exact HCk].
          unfold abind. rewrite CRC. rewrite ur_eq. cbn [w_s w_c w_r]. unfold us. cbn [w_s w_c w_r wset_s]. sacc.
          rewrite !wrap32_id by lia. destruct s; reflexivity.
        - exists (is_check s). destruct (Z.eqb_spec cp 0) as [C0|C0]; [|discriminate Ccp]. rewrite C0, !Z.sub_0_r, !Z.add_0_r.
          split; [|common_keep HCm]. unfold aret. f_equal. destruct s, r; reflexivity. }
      destruct STEP as (ck & STEP & HCk).
      aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun gs_eq. acase Clen.
      + arun aret_eq. aleave.
        unfold WINV. cbn [w_s w_c w_r]. sacc. rewrite E. mred.
        split; [core_keep HC; lia|]. split; [regs_solve RIN|]. split; [split; [common_keep HCk|exact Hb8]|]. split; [exact HWF|exact HWB].
      + arun aret_eq. apply TAIL; first [ core_keep HC; lia | regs_solve RIN | common_keep HCk | sacc; first [reflexivity | lia] ].
    - arun aret_eq. apply TAIL; first [assumption | reflexivity | lia].
  Qed.


  Lemma hcrc_step : forall s (m : AM unit) c r,
    common s -> (exists ck, m (mkW s c r) = ARun tt (mkW (iset_check s ck) c r)) ->
    exists ck, (if hcrc_on s then m else aret tt) (mkW s c r) = ARun tt (mkW (iset_check s ck) c r) /\ common (iset_check s ck).
  Proof.
    intros s m c r HCm [ck0 Hm]. destruct (hcrc_on s) eqn:Hh.
    - exists ck0. split; [exact Hm|]. eapply (common_hcrc s s); [exact HCm | exact Hh | reflexivity | reflexivity | reflexivity].
    - exists (is_check s). split; [unfold aret; f_equal; destruct s; reflexivity|]. common_keep HCm.
  Qed.

  Lemma arm_EXLEN_safe : arm_safe EXLEN arm_EXLEN.
  Proof.
    intros w0 s c r HW E HP. unfold arm_EXLEN. arun gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb8].
    pose proof (CORE_length s HC) as HL0.
    assert (TAIL : forall s' r', CORE s' -> REGS c r' -> common s' -> is_wbits s' = is_wbits s ->
              ir_bits r' < 8 -> ir_out r' = ir_out r -> ir_put r' = ir_put r -> ir_left r' = ir_left r ->
              64 * ir_have r' + 8 * ir_bits r' <= 64 * ir_have r + 8 * ir_bits r ->
              POST w0 ((set_mode EXTRA ;; arm_EXTRA)%am (mkW s' c r'))).
    { intros s' r' HC' HR' HCm' Ewb Hb Eo Ep El Hm. arun set_mode_eq.
      apply (POST_arm EXTRA arm_EXTRA _ _ _ _ arm_EXTRA_safe).
      - winv_split.
        + core_keep HC'. apply CORE_length; exact HC'.
        + exact HR'.
        + split; [common_keep HCm'|exact Hb].
        + rewrite Eo. exact HWF.
        + rewrite Ep, Ewb. exact HWB.
      - reflexivity.
      - phi_norm E HP. lia. }
    acase Cf.
    - aflat.
      destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply POST_bind_run; [exact EQ|]. cbv beta iota.
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
        aflat. arun HOLD_eq. aflat. arun us_eq.
        destruct (hcrc_step (iset_length s (wrap32 (ir_hold r1))) (CRC2 (ir_hold r1)) c r1 ltac:(common_keep HCm) ltac:(eexists; reflexivity))
          as (ck & STEP & HCk).
        aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun INITBITS_eq.
        apply TAIL; first [ core_keep HC; apply wrap32_range | apply REGS_init; exact HR1 | exact HCk | sacc; first [reflexivity | lia] ].
      + eapply POST_bind_leave; [exact EQ|].
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
        apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. split; [exact HCm|].
        intros F0. rewrite F0 in Cf. discriminate Cf.
    - arun aret_eq.
      assert (F0 : Z.land (is_flags s) 1024 = 0) by (destruct (Z.eqb_spec (Z.land (is_flags s) 1024) 0); [assumption|discriminate Cf]).
      apply TAIL; first [assumption | reflexivity | exact (Hb8 F0) | lia].
  Qed.

  Lemma arm_OS_safe : arm_safe OS arm_OS.
  Proof.
    intros w0 s c r HW E HP. unfold arm_OS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      aflat. arun HOLD_eq. aflat. arun gs_eq.
      destruct (hcrc_step s (CRC2 (ir_hold r1)) c r1 HMF ltac:(eexists; reflexivity)) as (ck & STEP & HCk).
      aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun INITBITS_eq. arun set_mode_eq.
      apply (POST_arm EXLEN arm_EXLEN _ _ _ _ arm_EXLEN_safe).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * apply REGS_init. exact HR1.
        * split; [common_keep HCk|]. intros _. cbn. lia.
        * rewrite Eo1. exact HWF.
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  Qed.

  Lemma arm_TIME_safe : arm_safe TIME arm_TIME.
  Proof.
    intros w0 s c r HW E HP. unfold arm_TIME.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct (NEEDBITS_spec c 32 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      aflat. arun HOLD_eq. aflat. arun gs_eq.
      destruct (hcrc_step s (CRC4 (ir_hold r1)) c r1 HMF ltac:(eexists; reflexivity)) as (ck & STEP & HCk).
      aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun INITBITS_eq. arun set_mode_eq.
      apply (POST_arm OS arm_OS _ _ _ _ arm_OS_safe).
      + winv_split.
        * core_keep HC. apply CORE_length; exact HC.
        * apply REGS_init. exact HR1.
        * common_keep HCk.
        * rewrite Eo1. exact HWF.
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  Qed.

  Lemma arm_FLAGS_safe : arm_safe FLAGS arm_FLAGS.
  Proof.
    intros w0 s c r HW E HP. unfold arm_FLAGS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HWb HCk0].
    pose proof (CORE_length s HC) as HL0.
    destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    - eapply POST_bind_run; [exact EQ|]. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      aflat. arun HOLD_eq. aflat. arun us_eq. aflat. arun gs_eq.
      assert (BADc : forall msg, POST w0 (go_bad msg (mkW (iset_flags s (swrap32 (ir_hold r1))) c r1))).
      { intros msg. unfold go_bad. arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
        - winv_split.
          + core_keep HC. exact HL0.
          + eapply REGS_cview; [exact HR1|reflexivity|reflexivity].
          + intros _. exact HCk0.
          + exact I.
          + rewrite Ep1. exact HWB.
        - phi_norm E HP. lia. }
      acase C1; [apply BADc|]. acase C2; [apply BADc|].
      assert (HCm1 : common (iset_flags s (swrap32 (ir_hold r1)))).
      { split; [exact HWb|]. intros _. exact HCk0. }
      destruct (hcrc_step (iset_flags s (swrap32 (ir_hold r1))) (CRC2 (ir_hold r1)) c r1 HCm1 ltac:(eexists; reflexivity)) as (ck & STEP & HCk).
      aflat. eapply POST_bind_run; [exact STEP|]. cbv beta iota. aflat. arun INITBITS_eq. arun set_mode_eq.
      apply (POST_arm TIME arm_TIME _ _ _ _ arm_TIME_safe).
      + winv_split.
        * core_keep HC. exact HL0.
        * apply REGS_init. exact HR1.
        * common_keep HCk.
        * rewrite Eo1. exact (proj1 HWF).
        * rewrite Ep1. exact HWB.
      + reflexivity.
      + phi_norm E HP. lia.
    - eapply POST_bind_leave; [exact EQ|].
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
      apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. intros X; exact X.
  Qed.


  Lemma aux_ref' : forall f s c r, aux ivar_ref f (mkW s c r) = ARun tt (mkW (f s) c r).
  Proof. reflexivity. Qed.

  Lemma wbits_step : forall s c r v, CORE s -> v <> 0 ->
    exists s1, (if is_wbits s =? 0 then us (fun s0 => iset_wbits s0 v) else aret tt) (mkW s c r) = ARun tt (mkW s1 c r)
      /\ CORE s1 /\ is_wbits s1 <> 0 /\ is_flags s1 = is_flags s /\ is_check s1 = is_check s.
  Proof.
    intros s c r v HC Hv. destruct (Z.eqb_spec (is_wbits s) 0) as [W|W].
    - exists (iset_wbits s v). split; [reflexivity|]. split; [apply CORE_wbits; assumption|]. sacc. repeat split; try reflexivity. exact Hv.
    - exists s. split; [reflexivity|]. split; [exact HC|]. split; [exact W|]. split; reflexivity.
  Qed.

  Lemma arm_HEAD_safe : arm_safe HEAD (arm_HEAD ivar_ref).
  Proof.
    intros w0 s c r HW E HP. unfold arm_HEAD. arun gs_eq.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [Hwb8 HCk0].
    pose proof (CORE_length s HC) as HL0.
    pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & C9 & _).
    acase Cw0.
    -
      apply Z.eqb_eq in Cw0.
      assert (HWb : is_wbits s <> 0) by (intros W; exact (proj2 (C9 W) Cw0)).
      rewrite set_mode_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * exact HR.
        * split; [split; [exact HWb | exact HCk0] | exact (Hwb8 Cw0)].
        * exact (proj1 HWF).
        * exact HWB.
      + phi_norm E HP. lia.
    - aflat.
      destruct (NEEDBITS_spec c 16 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      + eapply POST_bind_run; [exact EQ|]. cbv beta iota.
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
        pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
        aflat. arun HOLD_eq. acase Cgz.
        *
          apply andb_prop in Cgz as [_ Cgz]. apply Z.eqb_eq in Cgz.
          aflat. destruct (wbits_step s c r1 15 HC ltac:(lia)) as (s1 & STEP & HC1 & HWb1 & EF1 & ECk1).
          eapply POST_bind_run; [exact STEP|]. cbv beta iota.
          aflat. arun us_eq. unfold CRC2. aflat. arun us_eq. aflat. arun INITBITS_eq. rewrite set_mode_eq.
          apply POST_ARun.
          -- winv_split.
             ++ core_keep HC1. apply CORE_length; exact HC1.
             ++ apply REGS_init. exact HR1.
             ++ split; [exact HWb1|]. rewrite Cgz.
                change (adler_canon (icrc32_upd icrc32_init [31; 139])). exact gz_magic_crc_canon.
             ++ split; [rewrite Eo1; exact (proj1 HWF) | rewrite Ep1; exact (proj2 HWF)].
             ++ intros W. exfalso. exact (HWb1 W).
          -- phi_norm E HP. lia.
        *
          aflat. arun BITS_eq.
          assert (BADc : forall msg s1 r', CORE s1 -> REGS c r' -> is_flags s1 = is_flags s -> is_check s1 = is_check s ->
                    ir_put r' = ir_put r -> (is_wbits s1 = 0 -> is_wbits s = 0) ->
                    64 * ir_have r' + 8 * ir_bits r' + 8 * ir_left r' <= 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r ->
                    POST w0 (go_bad msg (mkW s1 c r'))).
          { intros msg s1 r' HC1 HR' EF ECk Ep Ewb Hm. unfold go_bad. arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
            - winv_split.
              + core_keep HC1. apply CORE_length; exact HC1.
              + eapply REGS_cview; [exact HR'|reflexivity|reflexivity].
              + rewrite EF, ECk. exact HCk0.
              + exact I.
              + intros W. rewrite Ep. exact (HWB (Ewb W)).
            - phi_norm E HP. lia. }
          acase Chk; [apply BADc; [exact HC | exact HR1 | reflexivity | reflexivity | exact Ep1 | intros W; exact W | lia]|].
          aflat. arun BITS_eq.
          acase Ccm; [apply BADc; [exact HC | exact HR1 | reflexivity | reflexivity | exact Ep1 | intros W; exact W | lia]|].
          aflat. arun DROPBITS_eq. aflat. arun BITS_eq. cbv zeta. sacc.
          rewrite (wrap32_id (ir_bits r1 - 4)) by lia.
          set (r2 := irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 4)) (ir_bits r1 - 4)).
          assert (HR2 : REGS c r2).
          { subst r2. rewrite <- (wrap32_id (ir_bits r1 - 4)) by lia. apply REGS_drop; [exact HR1 | lia]. }
          set (len := BITSv (Z.shiftr (ir_hold r1) 4) 4 + 8).
          assert (Hlen : 8 <= len).
          { subst len. rewrite BITSv_mod; [|apply Z.shiftr_nonneg; lia|lia]. pose proof (mod_pow2_range (Z.shiftr (ir_hold r1) 4) 4 ltac:(lia)). lia. }
          aflat. arun gs_eq.
          acase Cws; [apply BADc; [exact HC | exact HR2 | reflexivity | reflexivity | subst r2; sacc; exact Ep1 | intros W; exact W | subst r2; sacc; lia]|].
          aflat. destruct (wbits_step s c r2 len HC ltac:(lia)) as (s1 & STEP & HC1 & HWb1 & EF1 & ECk1).
          eapply POST_bind_run; [exact STEP|]. cbv beta iota.
          aflat. arun aux_ref'. aflat. arun us_eq. aflat. arun set_adler_check_eq. aflat. arun HOLD_eq. aflat. arun set_mode_eq.
          rewrite INITBITS_eq.
          apply POST_ARun.
          -- destruct (negb (Z.land (ir_hold r2) 512 =? 0)).
             ++ winv_split.
                ** core_keep HC1. apply CORE_length; exact HC1.
                ** eapply REGS_cview; [apply REGS_holdbits; [exact HR2 | exact HB_0] | reflexivity | reflexivity].
                ** split; [exact HWb1|]. intros _. exact adler_canon_1.
                ** subst r2. sacc. rewrite Eo1. exact (proj1 HWF).
                ** intros W. exfalso. exact (HWb1 W).
             ++ winv_split.
                ** core_keep HC1. apply CORE_length; exact HC1.
                ** eapply REGS_cview; [apply REGS_holdbits; [exact HR2 | exact HB_0] | reflexivity | reflexivity].
                ** split; [|cbn; lia]. split; [exact HWb1|]. intros _. exact adler_canon_1.
                ** subst r2. sacc. rewrite Eo1. exact (proj1 HWF).
                ** intros W. exfalso. exact (HWb1 W).
          -- lazymatch goal with |- _ < PHI ?w => set (PW0 := PHI w) in *; clearbody PW0 end.
             pose proof (rank_le3 (if negb (Z.land (ir_hold r2) 512 =? 0) then DICTID else TYPE)) as R3.
             unfold PHI. cbn [w_s w_c w_r]. subst r2. sacc. revert R3. sacc. intros R3.
             unfold PHI in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. mred_in HP. lia.
      + eapply POST_bind_leave; [exact EQ|].
        pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
        apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. split; [|exact HCk0].
        intros W. rewrite W in Cw0. discriminate Cw0.
  Qed.
End HeaderArms.
End RefInflateSafeA4.

Module RefInflateSafeA5.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma decoded_entry_stable : forall ty get root used h1 b1 h' here,
  TBLg ty get root used -> here = get (h1 mod 2 ^ root) -> code_bits here <= b1 -> 0 <= b1 ->
  0 <= h1 < 2 ^ b1 -> h' mod 2 ^ b1 = h1 -> get (h' mod 2 ^ root) = here.
Proof.
  intros ty get root used h1 b1 h' here HT Eh Hcb Hb1 Hh1 Hm.
  pose proof (T_root _ _ _ _ HT) as HR.
  assert (Hm' : h' mod 2 ^ b1 = h1 mod 2 ^ b1) by (rewrite Hm; symmetry; apply Z.mod_small; lia).
  destruct (Z.lt_ge_cases b1 root) as [LT|GE].
  - rewrite Eh. symmetry. symmetry. rewrite <- (rep_root_apply ty get root used HT h' h1 b1 ltac:(lia) ltac:(symmetry; exact Hm') ltac:(rewrite <- Eh; exact Hcb)). reflexivity.
  - rewrite (same_root_idx ty get root used HT h1 h' b1 GE Hm'). symmetry. exact Eh.
Qed.

Lemma codes_cell : forall e,
  ((exists sy, 0 <= sy < nsyms CODES /\ code_op e = fst (sym_entry CODES sy) /\ code_val e = snd (sym_entry CODES sy)) \/ code_op e = 64) ->
  0 <= code_val e < 19 \/ code_op e = 64.
Proof.
  intros e [[sy (Hsy & Hop & Hv)]|Hop]; [left|right; exact Hop].
  cbn [nsyms sym_entry fst snd] in Hsy, Hv. lia.
Qed.

Lemma cl_ext_lt16 : forall v, v < 16 -> cl_ext v = 0.
Proof. intros v H. unfold cl_ext. replace (v <? 16) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity. Qed.
Lemma cl_ext_16 : cl_ext 16 = 2. Proof. reflexivity. Qed.
Lemma cl_ext_17 : cl_ext 17 = 3. Proof. reflexivity. Qed.
Lemma cl_ext_ge18 : forall v, 18 <= v -> cl_ext v = 7.
Proof.
  intros v H. unfold cl_ext. replace (v <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (v =? 16) with false by (symmetry; apply Z.eqb_neq; lia). replace (v =? 17) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma TBLg_ext : forall ty get get' root used,
  (forall x, 0 <= x < used -> get' x = get x) -> TBLg ty get root used -> TBLg ty get' root used.
Proof.
  intros ty get get' root used E HT. pose proof HT as (R1 & R2 & SH & RRt & RSb).
  pose proof (pow2_pos root ltac:(lia)) as PR.
  split; [exact R1|]. split; [exact R2|]. split; [|split].
  - intros x Hx. rewrite E by exact Hx. exact (SH x Hx).
  - intros x x' Hx Hx' Hb Hm. rewrite !E in * by lia. exact (RRt x x' Hx Hx' Hb Hm).
  - intros x Hx Hop y y' Hy Hy' Hb Hm. rewrite (E x) in * by lia.
    destruct (root_cell ty get root used HT x Hx) as (_ & RL & _).
    destruct (RL ltac:(apply is_linkb_true; exact Hop)) as (_ & _ & Hv1 & Hv2).
    pose proof (pow2_pos (code_op (get x)) ltac:(lia)).
    rewrite !E in * by lia. exact (RSb x Hx Hop y y' Hy Hy' Hb Hm).
Qed.

Lemma lens_repeat_loop : forall m lens have len,
  0 <= have -> have + Z.of_nat m < 2 ^ 32 ->
  let '(lens', have', copy') :=
    loopZ (Z.of_nat m)
      (fun st : arr * Z * Z => let '(lens0, have0, copy0) := st in
         if negb (copy0 =? 0) then (true, (arr_set lens0 have0 (wrap16 len), wrap32 (have0 + 1), wrap32 (copy0 - 1)))
         else (false, (lens0, have0, copy0))) (lens, have, Z.of_nat m) in
  have' = have + Z.of_nat m /\ arr_len lens' = arr_len lens
  /\ (forall i, arr_get lens' i = if (have <=? i) && (i <? have + Z.of_nat m) && (i <? arr_len lens) then wrap16 len else arr_get lens i).
Proof.
  induction m as [|m IH]; intros lens have len Hh Hm.
  - change (Z.of_nat 0) with 0. rewrite loopZ_le0 by lia. split; [lia|]. split; [reflexivity|].
    intros i. destruct (Z.leb_spec have i), (Z.ltb_spec i (have + 0)), (Z.ltb_spec i (arr_len lens)); cbn [andb]; try reflexivity. all: exfalso; lia.
  - rewrite loopZ_step by lia. cbv beta iota zeta.
    replace (negb (Z.of_nat (S m) =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). cbv iota.
    rewrite (wrap32_id (have + 1)) by lia. replace (wrap32 (Z.of_nat (S m) - 1)) with (Z.of_nat m) by (rewrite wrap32_id by lia; lia).
    replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
    specialize (IH (arr_set lens have (wrap16 len)) (have + 1) len ltac:(lia) ltac:(lia)).
    destruct (loopZ (Z.of_nat m) _ _) as [[lens' have'] copy']. destruct IH as (A & B & C).
    split; [lia|]. split; [rewrite B; apply arr_len_set|].
    intros i. rewrite C. rewrite arr_len_set. rewrite arr_get_set. unfold arr_inb.
    destruct (Z.leb_spec (have + 1) i), (Z.ltb_spec i (have + 1 + Z.of_nat m)), (Z.leb_spec have i), (Z.ltb_spec i (have + Z.of_nat (S m))),
      (Z.eqb_spec have i), (Z.leb_spec 0 have), (Z.ltb_spec have (arr_len lens)), (Z.ltb_spec i (arr_len lens)); cbn [andb]; try reflexivity; try (exfalso; lia); subst; try reflexivity; try lia.
Qed.

Lemma lens_repeat_eq : forall copy len s c r, 0 <= copy -> 0 <= is_have s -> is_have s + copy < 2 ^ 32 ->
  exists lens', lens_repeat copy len (mkW s c r) = ARun tt (mkW (iset_have (iset_lens s lens') (is_have s + copy)) c r)
    /\ arr_len lens' = arr_len (is_lens s)
    /\ (forall i, arr_get lens' i = if (is_have s <=? i) && (i <? is_have s + copy) && (i <? arr_len (is_lens s)) then wrap16 len else arr_get (is_lens s) i).
Proof.
  intros copy len s c r Hc Hh Hm. unfold lens_repeat, us. cbn [w_s wset_s].
  pose proof (lens_repeat_loop (Z.to_nat copy) (is_lens s) (is_have s) len Hh ltac:(lia)) as L.
  rewrite Z2Nat.id in L by lia.
  destruct (loopZ copy _ _) as [[lens' have'] copy']. destruct L as (A & B & C).
  exists lens'. rewrite A. split; [reflexivity|]. split; [exact B|exact C].
Qed.


Definition CL (s : inflate_state) (c : icall) (r : iregs) : Prop :=
  CORE s /\ REGS c r /\ is_mode s = CODELENS /\ common s
  /\ (ir_bits r < 8 \/ ir_bits r < cneed s (ir_hold r))
  /\ 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 0 <= is_have s <= is_nlen s + is_ndist s
  /\ (forall i, 0 <= i < is_have s -> 0 <= arr_get (is_lens s) i <= 15)
  /\ cpok CODES (is_codes s) (is_lencode s) (is_lenbits s)
  /\ ir_out r = arr_len (ic_outbuf c) /\ (is_wbits s = 0 -> ir_put r = 0).

Lemma CL_WINV : forall s c r, CL s c r -> is_have s < is_nlen s + is_ndist s -> WINV (mkW s c r).
Proof.
  intros s c r (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB) Hlt.
  unfold WINV. cbn [w_s w_c w_r]. rewrite E. mred.
  split; [exact HC|]. split; [exact HR|]. split; [|split; [exact HWF|exact HWB]].
  repeat (split; [first [assumption | lia]|]). exact HT.
Qed.

Definition PHIr (r : iregs) : Z := 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r.

Ltac mrun lem := rewrite ?abind_assoc; unfold abind at 1; rewrite lem; cbv beta iota.

Section Codelens.
  Variable c : icall.

  Lemma codelens_body_spec : forall s r,
    CL s c r -> is_have s < is_nlen s + is_ndist s ->
    match codelens_body (mkW s c r) with
    | ARun true (mkW s' c' r') => c' = c /\ CL s' c' r' /\ is_have s < is_have s' /\ ir_bits r' < 8
        /\ is_nlen s' = is_nlen s /\ is_ndist s' = is_ndist s /\ PHIr r' + 8 <= PHIr r /\ ir_put r' = ir_put r
    | ARun false (mkW s' c' r') => is_mode s' = BAD /\ WINV (mkW s' c' r') /\ PHIr r' + 8 <= PHIr r /\ ir_put r' = ir_put r
        /\ ic_input c' = ic_input c /\ ic_outbuf c' = ic_outbuf c
    | ALeave w' => WINV w' /\ ir_put (w_r w') = ir_put r
    | ARet _ _ => False
    end.
  Proof.
    intros s r HCL Hlt. pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
    regs_open HR. pose proof (CORE_length s HC) as HL0. pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
    destruct (cpok_TBLg CODES s (is_lencode s) (is_lenbits s) HT) as (used & HTg & _).
    pose proof (T_root _ _ _ _ HTg) as HR15.
    unfold codelens_body. unfold abind at 1. rewrite gs_eq. cbn [w_s].
    destruct (DECODE1_spec c s (is_lencode s) CODES (is_lenbits s) used HTg r HR)
      as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
    2:{ unfold abind at 1. rewrite EQ. split.
        - pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
          apply (WINV_regs s c r r1 (CL_WINV s c r HCL Hlt) HR1 Eo1 Ep1). rewrite E. mred.
          intros _. split; [exact HCm|]. split; [|repeat (split; [first [assumption | lia]|]); exact HT].
          right. rewrite cneed_cneedg. pose proof (cneedg_range CODES _ _ used HTg (ir_hold r1)) as [_ CR]. lia.
        - cbn [w_r]. destruct (pulled_out r r1 HP1) as (_ & Ep1 & _). exact Ep1. }
    unfold abind at 1. rewrite EQ.
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
    pose proof HR1 as (RN1 & RH1 & RNH1 & RP1 & RL1 & RPL1 & [RB1 RHO1] & _).
    destruct (root_cell CODES _ _ used HTg (ir_hold r1 mod 2 ^ is_lenbits s) (ridx_range _ _ _ _ HTg _)) as (Hbits & RLk & RNk).
    rewrite <- Eh in Hbits, RLk, RNk.
    assert (SAME : ir_bits r1 = ir_bits r -> ir_hold r1 = ir_hold r).
    { intros Eb. destruct HP1 as (k & _ & _ & _ & _ & Bk & Mk & Hk & _). rewrite <- Mk. symmetry. apply Z.mod_small. rewrite <- Eb. exact Hk. }
    assert (DISC : ir_bits r1 = ir_bits r -> ir_bits r < 8 \/ ir_bits r < code_bits here + cl_ext (code_val here)).
    { intros Eb. destruct Hbx as [Hbx|Hbx]; [left; exact Hbx|right].
      rewrite cneed_cneedg in Hbx. unfold cneedg in Hbx. rewrite <- (SAME Eb), <- Eh in Hbx. exact Hbx. }
    cbv beta. destruct (Z.ltb_spec (code_val here) 16) as [V16|V16].
    -
      rewrite (cl_ext_lt16 _ V16) in DISC.
      unfold abind. rewrite DROPBITS_eq. rewrite gs_eq. cbn [w_s]. unfold set_lens. rewrite us_eq. rewrite us_eq. unfold aret. sacc.
      rewrite (wrap32_id (ir_bits r1 - code_bits here)) by lia. rewrite (wrap32_id (is_have s + 1)) by lia.
      rewrite (wrap16_id (code_val here)) by (pose proof (code_val_nonneg here); lia).
      pose proof (code_val_nonneg here) as V0.
      split; [reflexivity|]. split; [|split; [sacc; lia|split; [sacc|split; [reflexivity|split; [reflexivity|split; [unfold PHIr; sacc; lia|sacc; exact Ep1]]]]]].
      2:{ destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct (DISC Hb1); lia. }
      unfold CL. sacc. split; [core_keep HC; exact HL0|].
      split; [apply REGS_holdbits; [exact HR1|]; apply HB_drop; [split; [exact RB1|exact RHO1]|lia]|].
      split; [exact E|]. split; [common_keep HCm|].
      split; [left; destruct Hb1 as [Hb1|Hb1]; [destruct (DISC Hb1); lia|lia]|].
      split; [exact Hnl|]. split; [exact Hnd|]. split; [lia|].
      split.
      { intros i Hi. rewrite arr_get_set. unfold arr_inb. rewrite CA1.
        destruct (Z.eqb_spec (is_have s) i); cbn [andb].
        - replace ((0 <=? is_have s) && (is_have s <? 320)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia). lia.
        - apply HLs. lia. }
      split; [exact HT|]. split; [rewrite Eo1; exact HWF|rewrite Ep1; exact HWB].
    -
      assert (GEN : forall e base (lenf : inflate_state -> Z) (chk : bool),
        cl_ext (code_val here) = e -> 1 <= e <= 7 -> 3 <= base -> base + 2 ^ e <= 139 ->
        (forall s0, is_have s0 = is_have s -> is_lens s0 = is_lens s -> (chk = true -> 1 <= is_have s) -> 0 <= lenf s0 <= 15) ->
        match (abind (NEEDBITS (code_bits here + e) ;; DROPBITS (code_bits here) ;;
                      do s0 <- gs (fun s0 => s0) ;
                      if chk && (is_have s0 =? 0) then go_bad MSG_invalid_bit_length_repeat ;; aret None
                      else do b <- BITS e ; DROPBITS e ;; aret (Some (lenf s0, base + b)))
                     (fun lc => match lc with
                                | None => aret false
                                | Some (len, copy) =>
                                    do s0 <- gs (fun s0 => s0) ;
                                    if is_nlen s0 + is_ndist s0 <? is_have s0 + copy
                                    then go_bad MSG_invalid_bit_length_repeat ;; aret false
                                    else lens_repeat copy len ;; aret true
                                end) (mkW s c r1))%am
        with
        | ARun true (mkW s' c' r') => c' = c /\ CL s' c' r' /\ is_have s < is_have s' /\ ir_bits r' < 8
            /\ is_nlen s' = is_nlen s /\ is_ndist s' = is_ndist s /\ PHIr r' + 8 <= PHIr r /\ ir_put r' = ir_put r
        | ARun false (mkW s' c' r') => is_mode s' = BAD /\ WINV (mkW s' c' r') /\ PHIr r' + 8 <= PHIr r /\ ir_put r' = ir_put r
            /\ ic_input c' = ic_input c /\ ic_outbuf c' = ic_outbuf c
        | ALeave w' => WINV w' /\ ir_put (w_r w') = ir_put r
        | ARet _ _ => False
        end).
      { intros e base lenf chk He HeR Hbase Hcap Hlenf.
        pose proof (pow2_pos e ltac:(lia)) as PE.
        rewrite abind_assoc. unfold abind at 1.
        destruct (NEEDBITS_spec c (code_bits here + e) s r1 HR1 ltac:(lia)) as [(r2 & EQ2 & HR2 & HP2 & Hn2 & Hb2)|(r2 & EQ2 & HR2 & HP2 & Hb2 & Hh2)].
        2:{ rewrite EQ2. pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & _). split; [|cbn [w_r]; rewrite Ep2; exact Ep1].
            apply (WINV_regs s c r r2 (CL_WINV s c r HCL Hlt) HR2 ltac:(rewrite Eo2; exact Eo1) ltac:(rewrite Ep2; exact Ep1)).
            rewrite E. mred. intros _. split; [exact HCm|]. split; [|repeat (split; [first [assumption | lia]|]); exact HT].
            right. rewrite cneed_cneedg. unfold cneedg.
            destruct HP2 as (k & _ & _ & _ & _ & _ & Mk & _).
            rewrite (decoded_entry_stable CODES _ _ used (ir_hold r1) (ir_bits r1) (ir_hold r2) here HTg Eh Hle ltac:(lia) RHO1 Mk).
            rewrite He. exact Hb2. }
        rewrite EQ2. pose proof (pulled_out r1 r2 HP2) as (Eo2 & Ep2 & El2 & _). pose proof (pulled_phi r1 r2 HP2) as PH2.
        pose proof HR2 as (RN2 & RH2 & RNH2 & RP2 & RL2 & RPL2 & [RB2 RHO2] & _).
        assert (B8 : ir_bits r2 - code_bits here - e < 8).
        { destruct Hb2 as [Hb2|Hb2]; [|lia]. destruct Hb1 as [Hb1|Hb1]; [|lia]. destruct (DISC Hb1); lia. }
        mrun DROPBITS_eq. mrun gs_eq. cbn [w_s].
        rewrite (wrap32_id (ir_bits r2 - code_bits here)) by lia.
        set (r3 := irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) (code_bits here))) (ir_bits r2 - code_bits here)).
        assert (HR3 : REGS c r3) by (subst r3; apply REGS_holdbits; [exact HR2|]; apply HB_drop; [split; [exact RB2|exact RHO2]|lia]).
        destruct (chk && (is_have s =? 0)) eqn:Cchk.
        {
          mrun go_bad_eq. unfold aret.
          split; [reflexivity|]. split; [|split; [unfold PHIr; subst r3; sacc; lia|split; [subst r3; sacc; rewrite Ep2; exact Ep1|split; reflexivity]]].
          unfold WINV. cbn [w_s w_c w_r]. sacc. mred.
          split; [core_keep HC; exact HL0|]. split; [eapply REGS_cview; [exact HR3|reflexivity|reflexivity]|].
          split; [exact (proj2 HCm)|]. split; [exact I|]. subst r3. sacc. rewrite Ep2, Ep1. exact HWB. }
        mrun BITS_eq. mrun DROPBITS_eq. mrun aret_eq.
        subst r3. sacc. rewrite (BITSv_mod _ e) by (try apply Z.shiftr_nonneg; lia).
        pose proof (mod_pow2_range (Z.shiftr (ir_hold r2) (code_bits here)) e ltac:(lia)) as MV.
        set (v := Z.shiftr (ir_hold r2) (code_bits here) mod 2 ^ e) in *.
        rewrite (wrap32_id (ir_bits r2 - code_bits here - e)) by lia.
        set (r4 := irset_bits (irset_hold (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) (code_bits here))) (ir_bits r2 - code_bits here))
                     (Z.shiftr (Z.shiftr (ir_hold r2) (code_bits here)) e)) (ir_bits r2 - code_bits here - e)).
        assert (HR4 : REGS c r4).
        { subst r4. apply (REGS_holdbits c (irset_bits (irset_hold r2 (Z.shiftr (ir_hold r2) (code_bits here))) (ir_bits r2 - code_bits here))); [exact HR3|].
          apply (HB_drop _ (ir_bits r2 - code_bits here)); [|lia]. apply HB_drop; [split; [exact RB2|exact RHO2]|lia]. }
        assert (E4 : ir_bits r4 = ir_bits r2 - code_bits here - e /\ ir_have r4 = ir_have r2 /\ ir_left r4 = ir_left r2 /\ ir_put r4 = ir_put r2 /\ ir_out r4 = ir_out r2)
          by (subst r4; sacc; repeat split; reflexivity).
        destruct E4 as (E4b & E4h & E4l & E4p & E4o).
        mrun gs_eq. cbn [w_s].
        destruct (Z.ltb_spec (is_nlen s + is_ndist s) (is_have s + (base + v))) as [OV|OV].
        { mrun go_bad_eq. unfold aret.
          split; [reflexivity|]. split; [|split; [unfold PHIr; rewrite E4b, E4h, E4l; lia|split; [rewrite E4p, Ep2; exact Ep1|split; reflexivity]]].
          unfold WINV. cbn [w_s w_c w_r]. sacc. mred.
          split; [core_keep HC; exact HL0|]. split; [eapply REGS_cview; [exact HR4|reflexivity|reflexivity]|].
          split; [exact (proj2 HCm)|]. split; [exact I|]. rewrite E4p, Ep2, Ep1. exact HWB. }
        destruct (lens_repeat_eq (base + v) (lenf s) s c r4 ltac:(lia) ltac:(lia) ltac:(lia)) as (lens' & EQR & HL' & HG').
        mrun EQR. unfold aret.
        assert (HLF : 0 <= lenf s <= 15).
        { apply (Hlenf s eq_refl eq_refl). intros Hc. rewrite Hc in Cchk. cbn [andb] in Cchk. apply Z.eqb_neq in Cchk. lia. }
        split; [reflexivity|]. split; [|split; [sacc; lia|split; [lia|split; [reflexivity|split; [reflexivity|split; [unfold PHIr; rewrite E4b, E4h, E4l; lia|rewrite E4p, Ep2; exact Ep1]]]]]].
        unfold CL. sacc. split; [core_keep HC; [rewrite HL'; reflexivity|exact HL0]|].
        split; [exact HR4|]. split; [exact E|]. split; [common_keep HCm|]. split; [left; lia|].
        split; [exact Hnl|]. split; [exact Hnd|]. split; [lia|].
        split.
        { intros i Hi. rewrite HG'. rewrite CA1.
          destruct (Z.ltb_spec i (is_have s)) as [LT|GE].
          - replace (is_have s <=? i) with false by (symmetry; apply Z.leb_gt; exact LT). cbn [andb]. apply HLs. lia.
          - replace ((is_have s <=? i) && (i <? is_have s + (base + v)) && (i <? 320)) with true
              by (symmetry; rewrite !Bool.andb_true_iff, Z.leb_le, !Z.ltb_lt; lia).
            rewrite wrap16_id by lia. exact HLF. }
        split; [exact HT|]. rewrite E4o, E4p, Eo2, Ep2. split; [rewrite Eo1; exact HWF|rewrite Ep1; exact HWB]. }
      pose proof (code_val_nonneg here) as V0.
      destruct (Z.eqb_spec (code_val here) 16) as [E16|E16].
      + exact (GEN 2 3 (fun s0 => arr_get (is_lens s0) (is_have s0 - 1)) true ltac:(rewrite E16; reflexivity) ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                 ltac:(intros s0 Eh0 El0 H1; cbv beta; rewrite Eh0, El0; apply HLs; lia)).
      + destruct (Z.eqb_spec (code_val here) 17) as [E17|E17].
        * exact (GEN 3 3 (fun _ => 0) false ltac:(rewrite E17; reflexivity) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(intros; lia)).
        * exact (GEN 7 11 (fun _ => 0) false ltac:(apply cl_ext_ge18; lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(intros; lia)).
  Qed.

  Lemma codelens_while_S : forall k w,
    codelens_while (S k) w = (do s0 <- gs (fun s0 => s0) ;
                              if is_have s0 <? is_nlen s0 + is_ndist s0 then
                                do c0 <- codelens_body ; if c0 then codelens_while k else aret tt
                              else aret tt)%am w.
  Proof. reflexivity. Qed.

  Lemma codelens_while_spec : forall k s r,
    CL s c r -> is_nlen s + is_ndist s - is_have s < Z.of_nat k ->
    match codelens_while k (mkW s c r) with
    | ARun _ (mkW s' c' r') =>
        (c' = c /\ CL s' c' r' /\ is_have s' = is_nlen s' + is_ndist s' /\ is_nlen s' = is_nlen s /\ is_ndist s' = is_ndist s
         /\ PHIr r' <= PHIr r /\ ir_put r' = ir_put r /\ (is_have s < is_nlen s + is_ndist s -> PHIr r' + 8 <= PHIr r /\ ir_bits r' < 8)
         /\ (is_nlen s + is_ndist s <= is_have s -> s' = s /\ r' = r))
        \/ (is_mode s' = BAD /\ WINV (mkW s' c' r') /\ PHIr r' + 8 <= PHIr r /\ ir_put r' = ir_put r
            /\ ic_input c' = ic_input c /\ ic_outbuf c' = ic_outbuf c)
    | ALeave w' => WINV w' /\ ir_put (w_r w') = ir_put r
    | ARet _ _ => False
    end.
  Proof.
    induction k as [|k IH]; intros s r HCL Hk.
    { exfalso. pose proof HCL as (_ & _ & _ & _ & _ & _ & _ & Hh & _). cbn in Hk. lia. }
    rewrite codelens_while_S. mrun gs_eq. cbn [w_s].
    destruct (Z.ltb_spec (is_have s) (is_nlen s + is_ndist s)) as [LT|GE].
    - unfold abind at 1. pose proof (codelens_body_spec s r HCL LT) as B.
      destruct (codelens_body (mkW s c r)) as [[|] [s1 c1 r1] | w1 | rc w1].
      + cbv beta iota. destruct B as (-> & HCL1 & Hh1 & Hb1 & En1 & Ed1 & P1 & Ep1).
        specialize (IH s1 r1 HCL1 ltac:(lia)).
        destruct (codelens_while k (mkW s1 c r1)) as [u [s' c' r'] | w' | rc w']; [|rewrite <- Ep1; exact IH|exact IH].
        destruct IH as [(-> & HCL' & Hh' & En' & Ed' & P' & Ep' & Q' & Z')|(Hm & HW' & P' & Ep' & Ei' & Eo')].
        * left. rewrite En', Ed', En1, Ed1 in *. rewrite Ep1 in Ep'.
          split; [reflexivity|]. split; [exact HCL'|]. split; [exact Hh'|]. split; [reflexivity|]. split; [reflexivity|].
          split; [lia|]. split; [exact Ep'|]. split.
          -- intros _. split; [lia|]. destruct (Z.lt_ge_cases (is_have s1) (is_nlen s + is_ndist s)) as [X|X]; [apply Q'; exact X|].
             destruct (Z' X) as [_ ->]. exact Hb1.
          -- intros X. exfalso. lia.
        * right. rewrite Ep1 in Ep'. repeat (split; [first [assumption | lia]|]). exact Eo'.
      + cbv beta iota. unfold aret. right. destruct B as (Hm & HW1 & P1 & Ep1 & Ei1 & Eo1). repeat (split; [first [assumption | lia]|]). exact Eo1.
      + exact B.
      + exact B.
    - unfold aret. left. pose proof HCL as (_ & _ & _ & _ & _ & _ & _ & Hh & _).
      split; [reflexivity|]. split; [exact HCL|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [lia|]. split; [reflexivity|]. split; [intros X; exfalso; lia|]. intros _; split; reflexivity.
  Qed.
End Codelens.
End RefInflateSafeA5.

Module ItRep.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSort.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItCover.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItShape.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Rep.
  Variable wl : list Z.
Variable ll : list Z.
Variable root : Z.
Variable ty : codetype.
Variable table : Z.
  Hypothesis HW : forall l, 0 <= W wl l.
  Hypothesis HL : length wl = 16%nat.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  Hypothesis HK : TM wl (MAXL wl) <= 2 ^ MAXL wl.
  #[local] Set Default Proof Using "HW HL Hroot HM1 HK".

  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation TM := (TM wl).
  Local Notation len_at := (len_at wl).
  Local Notation Apos := (Apos wl).
  Local Notation Anext := (Anext wl).
  Local Notation code := (code wl).
  Local Notation hf := (hf wl).
  Local Notation GR := (GR wl root).
  Local Notation Pfx := (Pfx wl root).
  Local Notation islong := (islong wl root).
  Local Notation newtable := (newtable wl root).
  Local Notation noff := (noff wl root).
  Local Notation curr := (curr wl root).
  Local Notation used := (used wl root).
  Local Notation drop := (drop wl root).
  Local Notation lay := (lay wl root).
  Local Notation fill_writes := (fill_writes wl ll root ty table).
  Local Notation link_writes := (link_writes wl root ty table).
  Local Notation trip_writes := (trip_writes wl ll root ty table).
  Local Notation trips_writes := (trips_writes wl ll root ty table).
  Local Notation here := (here wl ll root ty).

  Let RR := root_range wl HW HL root Hroot HM1.
  Let GP := GR_pos wl HW HL root Hroot HM1.
  Let NP := NZ_pos wl HW HL HM1.


  Lemma fill_short_pos : forall k i v, 0 <= k < NZ -> islong k = false -> In (i, v) (fill_writes k) ->
    let x := i - table in
    0 <= x < 2 ^ root /\ v = here k /\ x mod 2 ^ len_at k = hf k /\ 0 <= hf k < 2 ^ len_at k /\ 1 <= len_at k <= root
    /\ Apos k <= rev root x * GR < Anext k.
  Proof.
    intros k i v Hk HS Hin.
    pose proof (lay_inv wl HW HL root Hroot HM1 k Hk) as [LI _]. destruct (LI HS) as (En & Ec & Eu).
    pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as (C1 & C2 & C3).
    assert (Ed : drop k = 0) by (unfold ItDefs.drop; rewrite HS; reflexivity).
    apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k i v ltac:(lia)) in Hin as [-> [j [Hj Ei]]].
    rewrite Ed, En, Ec in *. rewrite Z.sub_0_r in *. change (2 ^ 0) with 1 in *. rewrite Z.div_1_r in *.
    pose proof HS as HS'. unfold ItDefs.islong in HS'. apply Z.ltb_ge in HS'.
    pose proof (len_at_spec wl HW HL k Hk) as [L _].
    pose proof (hf_spec wl HW HL HK k Hk) as Ehf.
    pose proof (code_nonneg wl HW HL k Hk) as CN. pose proof (code_bound wl HW HL HK k Hk) as CB.
    assert (Hh : 0 <= hf k < 2 ^ len_at k) by (rewrite Ehf; apply rev_bound; lia).
    cbv zeta. set (x := i - table). assert (Ex : x = hf k + j * 2 ^ len_at k) by lia.
    pose proof (pow2_pos (len_at k) ltac:(lia)) as PL. pose proof (pow2_pos (root - len_at k) ltac:(lia)) as PRL.
    assert (Hx : 0 <= x < 2 ^ root).
    { rewrite Ex. split; [nia|]. replace root with (len_at k + (root - len_at k)) by lia. rewrite Z.pow_add_r by lia. nia. }
    assert (Hm : x mod 2 ^ len_at k = hf k).
    { rewrite Ex. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    split; [exact Hx|]. split; [reflexivity|]. split; [exact Hm|]. split; [exact Hh|]. split; [lia|].
    pose proof (proj1 (fillset root (len_at k) x (code k) ltac:(lia) Hx ltac:(lia)) ltac:(rewrite Hm, Ehf; reflexivity)) as Hq.
    pose proof (rev_bound root x ltac:(lia)) as RB.
    pose proof (Z.div_mod (rev root x) (2 ^ (root - len_at k)) ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (rev root x) (2 ^ (root - len_at k)) ltac:(lia)) as MB.
    rewrite Hq in DM.
    pose proof (code_mul wl HW HL k Hk) as CM. unfold Anext.
    assert (E2 : 2 ^ (MAXL - len_at k) = 2 ^ (root - len_at k) * GR).
    { unfold ItDefs.GR. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    rewrite E2 in CM |- *. nia.
  Qed.

  Lemma long_group : forall k, 0 <= k < NZ -> islong k = true ->
    exists g, 0 <= g <= k /\ newtable g = true /\ Pfx g = Pfx k /\ lay k = lay g /\ islong g = true.
  Proof.
    intros k Hk HLg. destruct (group_of wl HW HL root Hroot HM1 k Hk HLg) as [g (Hg & N & P & G4)].
    destruct (G4 k ltac:(lia)) as (E1 & E2 & E3). exists g. repeat split; try assumption; try lia.
    apply (newtable_long wl HW HL root Hroot HM1). exact N.
  Qed.

  Lemma noff_new : forall g, 1 <= g < NZ -> newtable g = true -> noff g = used (g - 1).
  Proof.
    intros g Hg N. pose proof (lay_S_new wl HW HL root Hroot HM1 (g - 1) ltac:(lia)) as LS.
    replace (g - 1 + 1) with g in LS by lia. destruct (LS N) as (E1 & _ & _).
    rewrite E1. symmetry. apply (used_eq wl HW HL root Hroot HM1). lia.
  Qed.

  Lemma group_unique_by_cell : forall g g' x, 0 <= g < NZ -> 0 <= g' < NZ ->
    newtable g = true -> newtable g' = true ->
    noff g <= x < noff g + 2 ^ curr g -> noff g' <= x < noff g' + 2 ^ curr g' -> g = g'.
  Proof.
    intros g g' x Hg Hg' N N' R R'.
    assert (GEN : forall a b, 0 <= a < b -> b < NZ -> newtable a = true -> newtable b = true ->
                  noff a + 2 ^ curr a <= noff b).
    { intros a b Hab Hb Na Nb.
      assert (Hb1 : 1 <= b).
      { destruct (Z.eq_dec b 0) as [->|]; [|lia]. lia. }
      rewrite (noff_new b ltac:(lia) Nb).
      rewrite <- (used_eq wl HW HL root Hroot HM1 a ltac:(lia)).
      apply (used_mono wl HW HL root Hroot HM1); lia. }
    destruct (Z.lt_trichotomy g g') as [LT|[EQ|GT]]; [|exact EQ|].
    - pose proof (GEN g g' ltac:(lia) ltac:(lia) N N'). lia.
    - pose proof (GEN g' g ltac:(lia) ltac:(lia) N' N). lia.
  Qed.

  Lemma fill_long_pos : forall k i v, 0 <= k < NZ -> islong k = true -> In (i, v) (fill_writes k) ->
    let x := i - table in let l := len_at k - root in let y := x - noff k in
    2 ^ root <= noff k /\ noff k <= x < noff k + 2 ^ curr k /\ v = here k
    /\ 1 <= l <= curr k /\ root + curr k <= MAXL
    /\ y mod 2 ^ l = hf k / 2 ^ root /\ 0 <= hf k / 2 ^ root < 2 ^ l
    /\ Apos k <= Pfx k * GR + rev (curr k) y * 2 ^ (MAXL - root - curr k) < Anext k.
  Proof.
    intros k i v Hk HLg Hin.
    pose proof (lay_inv wl HW HL root Hroot HM1 k Hk) as [_ LI]. destruct (LI HLg) as (J1 & J2 & J3 & J4 & J5).
    assert (Ed : drop k = root) by (unfold ItDefs.drop; rewrite HLg; reflexivity).
    pose proof (fill_writes_range wl ll root ty table HW HL Hroot HM1 HK k i v Hk Hin) as FR.
    apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k i v ltac:(rewrite Ed; lia)) in Hin as [-> [j [Hj Ei]]].
    rewrite Ed in *.
    pose proof HLg as HL'. unfold ItDefs.islong in HL'. apply Z.ltb_lt in HL'.
    pose proof (len_at_spec wl HW HL k Hk) as [L _]. pose proof (len_at_range wl HW HL k Hk) as LR.
    pose proof (hf_spec wl HW HL HK k Hk) as Ehf.
    pose proof (code_nonneg wl HW HL k Hk) as CN. pose proof (code_bound wl HW HL HK k Hk) as CB.
    cbv zeta. set (x := i - table). set (l := len_at k - root) in *. set (y := x - noff k).
    pose proof (pow2_pos l ltac:(lia)) as PL. pose proof (pow2_pos (curr k - l) ltac:(lia)) as PCL.
    set (sfx := code k mod 2 ^ l).
    assert (Hsfx : 0 <= sfx < 2 ^ l) by (subst sfx; apply Z.mod_pos_bound; lia).
    assert (Ehd : hf k / 2 ^ root = rev l sfx).
    { rewrite Ehf. subst l sfx. rewrite rev_div by lia. reflexivity. }
    assert (Hhd : 0 <= hf k / 2 ^ root < 2 ^ l) by (rewrite Ehd; apply rev_bound; lia).
    assert (Ey : y = hf k / 2 ^ root + j * 2 ^ l) by (subst y x; lia).
    assert (Hy : 0 <= y < 2 ^ curr k).
    { rewrite Ey. split; [nia|]. replace (curr k) with (l + (curr k - l)) by lia. rewrite Z.pow_add_r by lia. nia. }
    assert (Hm : y mod 2 ^ l = hf k / 2 ^ root).
    { rewrite Ey. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    split; [exact J1|]. split; [subst y; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [exact Hm|]. split; [exact Hhd|].
    pose proof (proj1 (fillset (curr k) l y sfx ltac:(lia) Hy Hsfx) ltac:(rewrite Hm, Ehd; reflexivity)) as Hq.
    pose proof (rev_bound (curr k) y ltac:(lia)) as RB.
    pose proof (Z.div_mod (rev (curr k) y) (2 ^ (curr k - l)) ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (rev (curr k) y) (2 ^ (curr k - l)) ltac:(lia)) as MB.
    rewrite Hq in DM.
    pose proof (Apos_decomp wl HW HL root Hroot HM1 k Hk HLg) as (D1 & D2 & D3). fold l sfx in D1, D2, D3.
    unfold Anext.
    pose proof (pow2_pos (MAXL - root - curr k) ltac:(lia)) as PQ.
    assert (E3 : 2 ^ (MAXL - len_at k) = 2 ^ (curr k - l) * 2 ^ (MAXL - root - curr k)).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    rewrite E3 in D1 |- *. nia.
  Qed.

  Lemma link_pos : forall k i v, 0 <= k < NZ -> In (i, v) (link_writes k) ->
    let g := k + 1 in let x := i - table in
    g < NZ /\ newtable g = true /\ islong g = true /\ x = rev root (Pfx g) /\ 0 <= Pfx g < 2 ^ root /\ 0 <= x < 2 ^ root
    /\ v = code_pack (curr g) root (noff g) /\ rev root x * GR = Apos g.
  Proof.
    intros k i v Hk Hin. cbv zeta.
    apply (In_link_writes wl root ty table HW HL Hroot HM1 HK k i v) in Hin as (Hk1 & N & _ & Ei & ->).
    pose proof (newtable_long wl HW HL root Hroot HM1 (k + 1) N) as Lg.
    pose proof (Pfx_nonneg wl HW HL root Hroot HM1 (k + 1) ltac:(lia)) as P0.
    pose proof (Pfx_bound wl HW HL root Hroot HM1 HK (k + 1) ltac:(lia)) as P1.
    assert (Ex : i - table = rev root (Pfx (k + 1))) by lia.
    rewrite Ex. rewrite rev_rev by lia.
    repeat (split; [first [assumption | reflexivity | lia | apply rev_bound; lia] |]).
    symmetry. apply (group_start wl HW HL root Hroot HM1); [lia | exact N].
  Qed.


  Lemma short_before_long : forall k g, 0 <= k < NZ -> 0 <= g < NZ -> islong k = false -> islong g = true -> k < g.
  Proof.
    intros k g Hk Hg HS HLg. destruct (Z.lt_ge_cases k g) as [X|X]; [exact X|]. exfalso.
    rewrite (islong_mono wl HW HL root Hroot HM1 g k ltac:(lia) ltac:(lia) HLg) in HS. discriminate HS.
  Qed.

  Lemma interval_unique : forall k k' t, 0 <= k < NZ -> 0 <= k' < NZ ->
    Apos k <= t < Anext k -> Apos k' <= t < Anext k' -> k = k'.
  Proof.
    intros k k' t Hk Hk' A B.
    destruct (Z.lt_trichotomy k k') as [LT|[EQ|GT]]; [|exact EQ|]; exfalso.
    - pose proof (Apos_lt wl HW HL k k' ltac:(lia) ltac:(lia)). lia.
    - pose proof (Apos_lt wl HW HL k' k ltac:(lia) ltac:(lia)). lia.
  Qed.

  Lemma fill_fill_unique : forall k k' i v v', 0 <= k < NZ -> 0 <= k' < NZ ->
    In (i, v) (fill_writes k) -> In (i, v') (fill_writes k') -> k = k'.
  Proof.
    intros k k' i v v' Hk Hk' Hin Hin'.
    destruct (islong k) eqn:E; destruct (islong k') eqn:E'.
    -
      pose proof (fill_long_pos k i v Hk E Hin) as A. pose proof (fill_long_pos k' i v' Hk' E' Hin') as B.
      cbv zeta in A, B. destruct A as (A1 & A2 & _ & A4 & A5 & _ & _ & A8). destruct B as (B1 & B2 & _ & B4 & B5 & _ & _ & B8).
      destruct (long_group k Hk E) as (g & Hg & N & P & Lk & Lg).
      destruct (long_group k' Hk' E') as (g' & Hg' & N' & P' & Lk' & Lg').
      assert (En : noff k = noff g /\ curr k = curr g) by (unfold ItDefs.noff, ItDefs.curr; rewrite Lk; split; reflexivity).
      assert (En' : noff k' = noff g' /\ curr k' = curr g') by (unfold ItDefs.noff, ItDefs.curr; rewrite Lk'; split; reflexivity).
      destruct En as [En Ec]. destruct En' as [En' Ec'].
      pose proof (group_unique_by_cell g g' (i - table) ltac:(lia) ltac:(lia) N N' ltac:(rewrite <- En, <- Ec; exact A2) ltac:(rewrite <- En', <- Ec'; exact B2)) as <-.
      rewrite <- P', P in B8. rewrite En', <- En in B8. rewrite Ec', <- Ec in B8.
      exact (interval_unique k k' _ Hk Hk' A8 B8).
    - exfalso. pose proof (fill_long_pos k i v Hk E Hin) as A. pose proof (fill_short_pos k' i v' Hk' E' Hin') as B.
      cbv zeta in A, B. destruct A as (A1 & A2 & _). destruct B as (B1 & _). lia.
    - exfalso. pose proof (fill_short_pos k i v Hk E Hin) as A. pose proof (fill_long_pos k' i v' Hk' E' Hin') as B.
      cbv zeta in A, B. destruct A as (A1 & _). destruct B as (B1 & B2 & _). lia.
    - pose proof (fill_short_pos k i v Hk E Hin) as A. pose proof (fill_short_pos k' i v' Hk' E' Hin') as B.
      cbv zeta in A, B. destruct A as (_ & _ & _ & _ & _ & A6). destruct B as (_ & _ & _ & _ & _ & B6).
      exact (interval_unique k k' _ Hk Hk' A6 B6).
  Qed.

  Lemma fill_link_disjoint : forall k k' i v v', 0 <= k < NZ -> 0 <= k' < NZ ->
    In (i, v) (fill_writes k) -> In (i, v') (link_writes k') -> False.
  Proof.
    intros k k' i v v' Hk Hk' Hin Hin'.
    pose proof (link_pos k' i v' Hk' Hin') as B. cbv zeta in B. destruct B as (G1 & N & Lg & Ex & HP & Hx & _ & Et).
    destruct (islong k) eqn:E.
    - pose proof (fill_long_pos k i v Hk E Hin) as A. cbv zeta in A. destruct A as (A1 & A2 & _). lia.
    - pose proof (fill_short_pos k i v Hk E Hin) as A. cbv zeta in A. destruct A as (_ & _ & _ & _ & _ & A6).
      rewrite Et in A6.
      pose proof (short_before_long k (k' + 1) Hk ltac:(lia) E Lg) as LT.
      pose proof (Apos_lt wl HW HL k (k' + 1) ltac:(lia) ltac:(lia)). lia.
  Qed.

  Lemma link_link_unique : forall k k' i v v', 0 <= k < NZ -> 0 <= k' < NZ ->
    In (i, v) (link_writes k) -> In (i, v') (link_writes k') -> k = k'.
  Proof.
    intros k k' i v v' Hk Hk' Hin Hin'.
    pose proof (link_pos k i v Hk Hin) as A. pose proof (link_pos k' i v' Hk' Hin') as B. cbv zeta in A, B.
    destruct A as (G1 & N & _ & Ex & HP & _). destruct B as (G1' & N' & _ & Ex' & HP' & _).
    assert (EP : Pfx (k + 1) = Pfx (k' + 1)).
    { apply (rev_inj root); lia. }
    pose proof (newtable_unique wl root HW HL Hroot HM1 HK (k + 1) (k' + 1) ltac:(lia) ltac:(lia) N N' EP). lia.
  Qed.

  Theorem writes_unique : forall n i v v', 0 <= n <= NZ ->
    In (i, v) (trips_writes n) -> In (i, v') (trips_writes n) -> v = v'.
  Proof.
    intros n i v v' Hn Hin Hin'.
    apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK n (i, v) ltac:(lia)) in Hin as [k [Hk Hin]].
    apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK n (i, v') ltac:(lia)) in Hin' as [k' [Hk' Hin']].
    apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK) in Hin. apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK) in Hin'.
    destruct Hin as [Hin|Hin]; destruct Hin' as [Hin'|Hin'].
    - pose proof (fill_fill_unique k k' i v v' ltac:(lia) ltac:(lia) Hin Hin') as <-.
      pose proof (curr_range wl HW HL root Hroot HM1 k ltac:(lia)) as (_ & C2 & _).
      apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k i v ltac:(lia)) in Hin as [-> _].
      apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k i v' ltac:(lia)) in Hin' as [-> _]. reflexivity.
    - exfalso. exact (fill_link_disjoint k k' i v v' ltac:(lia) ltac:(lia) Hin Hin').
    - exfalso. exact (fill_link_disjoint k' k i v' v ltac:(lia) ltac:(lia) Hin' Hin).
    - pose proof (link_link_unique k k' i v v' ltac:(lia) ltac:(lia) Hin Hin') as <-.
      apply (In_link_writes wl root ty table HW HL Hroot HM1 HK k i v) in Hin as (_ & _ & _ & _ & ->).
      apply (In_link_writes wl root ty table HW HL Hroot HM1 HK k i v') in Hin' as (_ & _ & _ & _ & ->). reflexivity.
  Qed.

  Lemma In_fill_trips : forall k p, 0 <= k < NZ -> In p (fill_writes k) -> In p (trips_writes NZ).
  Proof.
    intros k p Hk Hin. apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK NZ p ltac:(lia)).
    exists k. split; [exact Hk|]. apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK). left. exact Hin.
  Qed.
  Lemma In_link_trips : forall k p, 0 <= k < NZ -> In p (link_writes k) -> In p (trips_writes NZ).
  Proof.
    intros k p Hk Hin. apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK NZ p ltac:(lia)).
    exists k. split; [exact Hk|]. apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK). right. exact Hin.
  Qed.
  Lemma In_trips_cases : forall p, In p (trips_writes NZ) ->
    exists k, 0 <= k < NZ /\ (In p (fill_writes k) \/ In p (link_writes k)).
  Proof.
    intros p Hin. apply (In_trips_writes wl ll root ty table HW HL Hroot HM1 HK NZ p ltac:(lia)) in Hin as [k [Hk Hin]].
    exists k. split; [exact Hk|]. apply (In_trip_writes wl ll root ty table HW HL Hroot HM1 HK). exact Hin.
  Qed.

  Lemma here_bits : forall k, 0 <= k < NZ -> code_bits (here k) = len_at k - drop k.
  Proof.
    intros k Hk. pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as (C1 & C2 & C3).
    unfold ItDefs.here. destruct (entry ty (wsym wl ll k)) as [op val]. rewrite code_bits_pack. apply wrap8_small. lia.
  Qed.


  Theorem rep_root_w : forall x x' v,
    In (table + x, v) (trips_writes NZ) -> 0 <= x < 2 ^ root -> 0 <= x' < 2 ^ root ->
    x' mod 2 ^ code_bits v = x mod 2 ^ code_bits v ->
    In (table + x', v) (trips_writes NZ).
  Proof.
    intros x x' v Hin Hx Hx' Hm.
    destruct (In_trips_cases _ Hin) as (k & Hk & [HinF|HinL]).
    - destruct (islong k) eqn:E.
      { pose proof (fill_long_pos k _ _ Hk E HinF) as A. cbv zeta in A. destruct A as (A1 & A2 & _). exfalso. lia. }
      pose proof (fill_short_pos k _ _ Hk E HinF) as A. cbv zeta in A.
      replace (table + x - table) with x in A by lia. destruct A as (_ & Ev & Hmx & Hh & Hl & _).
      assert (Eb : code_bits v = len_at k).
      { rewrite Ev, (here_bits k Hk). unfold ItDefs.drop. rewrite E. lia. }
      rewrite Eb in Hm. rewrite Hmx in Hm.
      destruct (in_progression (hf k) (len_at k) (root - len_at k) x' ltac:(lia) ltac:(lia) Hh ltac:(replace (len_at k + (root - len_at k)) with root by lia; exact Hx') Hm)
        as [j [Hj Ej]].
      apply (In_fill_trips k); [exact Hk|].
      pose proof (lay_inv wl HW HL root Hroot HM1 k Hk) as [LI _]. destruct (LI E) as (En & Ec & Eu).
      apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k); [unfold ItDefs.drop; rewrite E, Ec; lia|].
      split; [exact Ev|]. exists j. unfold ItDefs.drop. rewrite E, En, Ec. rewrite Z.sub_0_r. change (2 ^ 0) with 1. rewrite Z.div_1_r.
      split; [exact Hj|lia].
    - pose proof (link_pos k _ _ Hk HinL) as A. cbv zeta in A. replace (table + x - table) with x in A by lia.
      destruct A as (G1 & N & Lg & Ex & HP & _ & Ev & _).
      assert (Eb : code_bits v = root) by (rewrite Ev, code_bits_pack; apply wrap8_small; lia).
      rewrite Eb in Hm. rewrite !Z.mod_small in Hm by lia. subst x'. apply (In_link_trips k); [exact Hk|exact HinL].
  Qed.


  Hypothesis HU : used (NZ - 1) < 65536.

  Theorem rep_sub_w : forall k x L y y' v,
    0 <= k < NZ -> In (table + x, L) (link_writes k) ->
    0 <= y < 2 ^ code_op L -> 0 <= y' < 2 ^ code_op L ->
    In (table + code_val L + y, v) (trips_writes NZ) ->
    y' mod 2 ^ code_bits v = y mod 2 ^ code_bits v ->
    In (table + code_val L + y', v) (trips_writes NZ).
  Proof using HW HL Hroot HM1 HK HU.
    intros k x L y y' v Hk HinL Hy Hy' Hin Hm.
    pose proof (link_pos k _ _ Hk HinL) as A. cbv zeta in A. destruct A as (G1 & N & Lg & _ & _ & _ & Ev & _).
    set (g := k + 1) in *.
    pose proof (lay_inv wl HW HL root Hroot HM1 g ltac:(lia)) as [_ LI]. destruct (LI Lg) as (N1 & N2 & N3 & N4 & N5).
    pose proof (used_mono wl HW HL root Hroot HM1 g (NZ - 1) ltac:(lia) ltac:(lia)) as UM.
    pose proof (MAXL_spec wl HW HL) as [MM _].
    assert (Eop : code_op L = curr g) by (rewrite Ev, code_op_pack; apply wrap8_small; lia).
    assert (Eval : code_val L = noff g) by (rewrite Ev, code_val_pack; apply wrap16_small; pose proof (Z.pow_nonneg 2 (curr g)); lia).
    rewrite Eop in Hy, Hy'. rewrite Eval in Hin |- *.
    destruct (In_trips_cases _ Hin) as (k' & Hk' & [HinF|HinL']).
    2:{ exfalso. pose proof (link_pos k' _ _ Hk' HinL') as B. cbv zeta in B. destruct B as (_ & _ & _ & _ & _ & Bx & _). lia. }
    destruct (islong k') eqn:E'.
    2:{ exfalso. pose proof (fill_short_pos k' _ _ Hk' E' HinF) as B. cbv zeta in B. destruct B as (Bx & _). lia. }
    pose proof (fill_long_pos k' _ _ Hk' E' HinF) as B. cbv zeta in B.
    replace (table + noff g + y - table) with (noff g + y) in B by lia.
    destruct B as (B1 & B2 & Ev' & Bl & Bm & Bmod & Bh & _).
    destruct (long_group k' Hk' E') as (g' & Hg' & N' & P' & Lk' & Lg').
    assert (En' : noff k' = noff g' /\ curr k' = curr g') by (unfold ItDefs.noff, ItDefs.curr; rewrite Lk'; split; reflexivity).
    destruct En' as [En' Ec'].
    pose proof (group_unique_by_cell g' g (noff g + y) ltac:(lia) ltac:(lia) N' N ltac:(rewrite <- En', <- Ec'; exact B2) ltac:(lia)) as Egg.
    subst g'. rewrite En' in *. rewrite Ec' in *.
    replace (noff g + y - noff g) with y in Bmod by lia.
    set (l := len_at k' - root) in *.
    assert (Eb : code_bits v = l) by (rewrite Ev', (here_bits k' Hk'); unfold ItDefs.drop; rewrite E'; reflexivity).
    rewrite Eb in Hm. rewrite Bmod in Hm.
    destruct (in_progression (hf k' / 2 ^ root) l (curr g - l) y' ltac:(lia) ltac:(lia) Bh ltac:(replace (l + (curr g - l)) with (curr g) by lia; exact Hy') Hm)
      as [j [Hj Ej]].
    apply (In_fill_trips k'); [exact Hk'|].
    apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k'); [unfold ItDefs.drop; rewrite E', Ec'; lia|].
    split; [exact Ev'|]. exists j. unfold ItDefs.drop. rewrite E', En', Ec'. fold l. split; [exact Hj|lia].
  Qed.
End Rep.


Lemma land240_small' : forall op, 0 <= op <= 15 -> Z.land op 240 = 0.
Proof.
  intros op H. destruct op as [|p|p]; [reflexivity| |lia].
  do 4 (destruct p as [p|p|]; [| |reflexivity]); cbn in H; lia.
Qed.

Section Rep2.
  Variable wl : list Z.
Variable ll : list Z.
Variable root : Z.
Variable ty : codetype.
Variable table : Z.
  Hypothesis Hll : Forall (fun l => 0 <= l <= 15) ll.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  Hypothesis HK : TM wl (MAXL wl) <= 2 ^ MAXL wl.
  Hypothesis Hns : NC ll <= nsyms ty.
  Hypothesis HU : used wl root (NZ wl - 1) < 65536.
  Let HW := HW' wl ll root ty Hll Ewl Hroot HM1 HK Hns HU.
  Let HL := HL' wl ll root ty Hll Ewl Hroot HM1 HK Hns HU.

  Lemma here_op_notlink : forall k, 0 <= k < NZ wl -> ~ (1 <= code_op (here wl ll root ty k) <= 15).
  Proof.
    intros k Hk H. pose proof (wsym_ok wl ll root ty Hll Ewl Hroot HM1 HK Hns HU k Hk) as [SR _].
    unfold ItDefs.here in H. destruct (entry ty (wsym wl ll k)) as [op val] eqn:E.
    rewrite code_op_pack in H.
    pose proof (entry_sym_entry ty (wsym wl ll k) ltac:(lia)) as [E1 _]. rewrite E in E1. cbn [fst] in E1. rewrite E1 in H.
    destruct (sym_entry_nolink ty (wsym wl ll k) SR) as [X|X]; [lia|].
    unfold may_link_op in X. rewrite (land240_small' (fst (sym_entry ty (wsym wl ll k))) ltac:(lia)) in X. cbn in X. discriminate X.
  Qed.

  Lemma root_link_write : forall x v,
    In (table + x, v) (trips_writes wl ll root ty table (NZ wl)) -> 0 <= x < 2 ^ root -> 1 <= code_op v <= 15 ->
    exists k, 0 <= k < NZ wl /\ In (table + x, v) (link_writes wl root ty table k).
  Proof.
    intros x v Hin Hx Hop.
    destruct (In_trips_cases wl ll root ty table HW HL Hroot HM1 HK _ Hin) as (k & Hk & [HinF|HinL]).
    - exfalso. pose proof (curr_range wl HW HL root Hroot HM1 k Hk) as (_ & C2 & _).
      apply (In_fill_writes wl ll root ty table HW HL Hroot HM1 HK k) in HinF as [-> _]; [|lia].
      exact (here_op_notlink k Hk Hop).
    - exists k. split; [exact Hk|exact HinL].
  Qed.
End Rep2.


Section AbsRep.
  Variable wl : list Z.
Variable ll : list Z.
Variable table : Z.
Variable bits : Z.
  Hypothesis Hll : Forall (fun l => 0 <= l <= 15) ll.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hbits : 1 <= bits <= 15.
  #[local] Set Default Proof Using "Hll Ewl Hbits".

  Let HW := OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.HWa wl ll bits Hll Ewl Hbits.
  Let HL := OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.HLa wl ll bits Hll Ewl Hbits.

  Definition REPW (ws : list (Z * Z)) (root toff : Z) : Prop :=
    (forall i v v', In (i, v) ws -> In (i, v') ws -> v = v')
    /\ (forall x x' v, In (table + x, v) ws -> 0 <= x < 2 ^ root -> 0 <= x' < 2 ^ root ->
          x' mod 2 ^ code_bits v = x mod 2 ^ code_bits v -> In (table + x', v) ws)
    /\ (forall x L y y' v, In (table + x, L) ws -> 0 <= x < 2 ^ root -> 1 <= code_op L <= 15 ->
          0 <= y < 2 ^ code_op L -> 0 <= y' < 2 ^ code_op L ->
          table + 2 ^ root <= table + code_val L + y < toff
          /\ (In (table + code_val L + y, v) ws -> y' mod 2 ^ code_bits v = y mod 2 ^ code_bits v ->
              In (table + code_val L + y', v) ws)).

  Theorem it_abs_rep : forall ty, ty_ok ty ll bits ->
    let '(ret, ws, toff, bits', ww) := it_abs wl ll ty table bits in
    ret = 0 -> REPW ws bits' toff.
  Proof.
    intros ty Hty. pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]]. pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.nsyms_ok wl ll bits Hll Ewl Hbits ty Hty) as NS.
    assert (HR : 2 <= it_room ty) by (destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia).
    unfold it_abs.
    destruct (Z.eqb_spec (MAXL wl) 0) as [HM0|HM0].
    {
      intros _. change (2 ^ 1) with 2. split; [|split].
      - intros i v v' A B. destruct A as [A|[A|[]]]; destruct B as [B|[B|[]]]; congruence.
      - intros x x' v A Hx Hx' _. assert (v = code_pack 64 1 0) as -> by (destruct A as [A|[A|[]]]; congruence).
        assert (x' = 0 \/ x' = 1) as [->| ->] by lia; [left; f_equal; lia|right; left; reflexivity].
      - intros x L y y' v A Hx HL0. exfalso.
        assert (L = code_pack 64 1 0) as -> by (destruct A as [A|[A|[]]]; congruence).
        rewrite code_op_pack, wrap8_small in HL0 by lia. lia. }
    assert (HM1 : 1 <= MAXL wl) by lia.
    pose proof (MINL_spec wl HW HL HM1) as [MA [MB MC]].
    destruct (Z.ltb_spec (LEFT wl) 0) as [HL0|HL0]; [intros X; discriminate X|].
    pose proof (LEFT_sign wl HW HL) as [LS1 [LS2 LS3]].
    assert (HK : TM wl (MAXL wl) <= 2 ^ MAXL wl) by lia.
    destruct ((0 <? LEFT wl) && (codetype_eqb ty CODES || negb (MAXL wl =? 1))) eqn:Hinc; [intros X; discriminate X|].
    set (root := ROOT wl bits).
    assert (RRg : MINL wl <= root <= MAXL wl) by (subst root; unfold ROOT; lia).
    pose proof (root_range wl HW HL root RRg HM1) as RR2.
    destruct (it_not_enough ty (2 ^ root)) eqn:NE0; [intros X; discriminate X|].
    unfold loop_abs.
    destruct (Z.ltb_spec (first_fail wl root ty) (NZ wl - 1)) as [FF|FF]; [intros X; discriminate X|].
    intros _.
    pose proof (NZ_pos wl HW HL HM1) as NP.
    assert (Hnf : forall k, 0 <= k < NZ wl - 1 -> fails_at wl root ty k = false).
    { intros k Hk. rewrite (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.first_fail_eq wl ll bits Hll Ewl Hbits) in FF. apply (zsearch_before (fails_at wl root ty) 0 (Z.to_nat (NZ wl - 1))). lia. }
    pose proof (used_lower wl HW HL root RRg HM1 (NZ wl - 1) ltac:(lia)) as UL.
    pose proof (used_enough wl root ty HW HL RRg HM1 HK NE0 Hnf (NZ wl - 1) ltac:(lia)) as UE.
    assert (HU : 2 ^ root <= used wl root (NZ wl - 1) <= it_room ty).
    { split; [exact UL|]. destruct (codetype_eqb ty CODES) eqn:TC.
      - assert (ty = CODES) as -> by (destruct ty; cbn in TC; congruence).
        destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.codes_short wl ll bits Hll Ewl Hbits Hty HM1) as [E7 M7]. fold root in E7.
        pose proof (lay_inv wl HW HL root RRg HM1 (NZ wl - 1) ltac:(lia)) as [LI _].
        assert (HS : islong wl root (NZ wl - 1) = false).
        { unfold islong. apply Z.ltb_ge. rewrite (len_at_last wl HW HL HM1). lia. }
        destruct (LI HS) as [_ [_ ->]]. cbn [it_room]. rewrite E7.
        change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
      - apply (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.room_enough wl ll bits Hll Ewl Hbits); [exact UE|]. destruct ty; cbn in TC; congruence. }
    assert (HU2 : used wl root (NZ wl - 1) < 65536).
    { assert (it_room ty <= 852) by (destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia). lia. }
    destruct (Z.eq_dec (LEFT wl) 0) as [HC0|HC0].
    -
      assert (HC : TM wl (MAXL wl) = 2 ^ MAXL wl) by (apply (proj1 LS2); exact HC0).
      unfold final_writes. rewrite (hf_NZ_complete wl root ty HW HL RRg HM1 HK HC Hnf NE0). cbn [Z.eqb]. rewrite app_nil_r.
      split; [|split].
      + intros i v v' A B. exact (writes_unique wl ll root ty table HW HL RRg HM1 HK (NZ wl) i v v' ltac:(lia) A B).
      + intros x x' v A Hx Hx' Hm. exact (rep_root_w wl ll root ty table HW HL RRg HM1 HK x x' v A Hx Hx' Hm).
      + intros x L y y' v A Hx HLo Hy Hy'.
        destruct (root_link_write wl ll root ty table Hll Ewl RRg HM1 HK NS HU2 x L A Hx HLo) as (k & Hk & HinL).
        pose proof (link_pos wl root ty table HW HL RRg HM1 HK k _ _ Hk HinL) as B. cbv zeta in B.
        destruct B as (G1 & N & Lg & _ & _ & _ & Ev & _).
        pose proof (lay_inv wl HW HL root RRg HM1 (k + 1) ltac:(lia)) as [_ LI]. destruct (LI Lg) as (N1 & N2 & N3 & N4 & N5).
        pose proof (used_mono wl HW HL root RRg HM1 (k + 1) (NZ wl - 1) ltac:(lia) ltac:(lia)) as UM.
        assert (Eop : code_op L = curr wl root (k + 1)) by (rewrite Ev, code_op_pack; apply wrap8_small; lia).
        assert (Eval : code_val L = noff wl root (k + 1)) by (rewrite Ev, code_val_pack; apply wrap16_small; pose proof (Z.pow_nonneg 2 (curr wl root (k + 1))); lia).
        split; [rewrite Eval; rewrite Eop in Hy; lia|].
        intros B Hm. exact (rep_sub_w wl ll root ty table HW HL RRg HM1 HK HU2 k x L y y' v Hk HinL Hy Hy' B Hm).
    -
      assert (HLp : 0 < LEFT wl) by lia.
      destruct (Z.ltb_spec 0 (LEFT wl)); [|lia]. cbn [andb] in Hinc. apply Bool.orb_false_iff in Hinc as [TC HMx].
      apply Bool.negb_false_iff in HMx. apply Z.eqb_eq in HMx.
      destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.incomplete_facts wl ll bits Hll Ewl Hbits HLp HMx) as (Emin & W1 & NZ1 & R1 & _). fold root in R1.
      unfold final_writes. rewrite NZ1 in *. change (1 - 1) with 0 in *.
      pose proof (lay_0 wl HW HL root RRg HM1) as L0.
      assert (E0 : noff wl root 0 = 0 /\ curr wl root 0 = root /\ used wl root 0 = 2 ^ root).
      { unfold noff, curr, used. rewrite L0. repeat split; reflexivity. }
      destruct E0 as (En & Ec & Eu).
      pose proof (len_at_0 wl HW HL HM1) as EL. rewrite Emin in EL.
      assert (Ed : drop wl root 0 = 0) by (unfold drop, islong; rewrite EL, R1; reflexivity).
      assert (Ehf0 : hf wl 0 = 0) by reflexivity.
      assert (Ehf1 : hf wl 1 = 1).
      { unfold ItDefs.hf. cbn [Z.eqb]. change (1 - 1) with 0. rewrite (code_0 wl HW HL HM1), EL. reflexivity. }
      rewrite Ehf1. cbn [Z.eqb]. assert (P2 : 2 ^ root = 2) by (rewrite R1; reflexivity).
      rewrite ?Eu, ?En, ?EL, ?Ed, ?P2 in *.
      assert (ET : trips_writes wl ll root ty table 1 = fill_writes wl ll root ty table 0).
      { unfold trips_writes. change (Z.to_nat 1) with 1%nat. cbn [seq flat_map]. rewrite app_nil_r.
        change (Z.of_nat 0) with 0. unfold trip_writes, link_writes. rewrite NZ1. cbn [Z.add Z.ltb andb]. apply app_nil_r. }
      rewrite ET.
      assert (HF : forall i v, In (i, v) (fill_writes wl ll root ty table 0) <-> i = table /\ v = here wl ll root ty 0).
      { intros i v. rewrite (In_fill_writes wl ll root ty table HW HL RRg HM1 HK 0 i v) by (rewrite EL, Ed, Ec, R1; lia).
        rewrite EL, Ed, Ec, En, Ehf0, R1. change (2 ^ (1 - (1 - 0))) with 1. change (2 ^ 0) with 1. change (0 / 1) with 0.
        split.
        - intros [-> [j [Hj ->]]]. split; [lia|reflexivity].
        - intros [-> ->]. split; [reflexivity|]. exists 0. lia. }
      assert (Hb0 : code_bits (here wl ll root ty 0) = 1).
      { rewrite (here_bits wl ll root ty HW HL RRg HM1 HK 0 ltac:(lia)). rewrite EL, Ed. reflexivity. }
      assert (Hop0 : ~ (1 <= code_op (here wl ll root ty 0) <= 15)).
      { apply (here_op_notlink wl ll root ty Hll Ewl RRg HM1 HK NS); [rewrite NZ1; change (1 - 1) with 0; rewrite Eu; lia | rewrite NZ1; lia]. }
      assert (CASES : forall i v, In (i, v) (fill_writes wl ll root ty table 0 ++ [(table + 0 + 1, code_pack 64 (1 - 0) 0)]) ->
                      (i = table /\ v = here wl ll root ty 0) \/ (i = table + 0 + 1 /\ v = code_pack 64 1 0)).
      { intros i v Hin. apply in_app_iff in Hin as [Hin|[Hin|[]]]; [left; apply HF; exact Hin | right]. injection Hin; intros E1 E2. rewrite <- E1, <- E2. split; reflexivity. }
      split; [|split].
      + intros i v v' A B. destruct (CASES _ _ A) as [[-> ->]|[-> ->]]; destruct (CASES _ _ B) as [[X ->]|[X ->]]; try reflexivity; lia.
      + intros x x' v A Hx Hx' Hm. rewrite R1 in Hx, Hx'. change (2 ^ 1) with 2 in Hx, Hx'.
        destruct (CASES _ _ A) as [[X ->]|[X ->]].
        * rewrite Hb0 in Hm. change (2 ^ 1) with 2 in Hm. rewrite !Z.mod_small in Hm by lia.
          apply in_app_iff. left. apply HF. split; [lia|reflexivity].
        * rewrite code_bits_pack in Hm. change (2 ^ wrap8 1) with 2 in Hm. rewrite !Z.mod_small in Hm by lia.
          apply in_app_iff. right. left. f_equal. lia.
      + intros x L y y' v A Hx HLo. exfalso. destruct (CASES _ _ A) as [[X ->]|[X ->]].
        * exact (Hop0 HLo).
        * rewrite code_op_pack, wrap8_small in HLo by lia. lia.
  Qed.
End AbsRep.
End ItRep.

Module RefInflateSafeR.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItMath.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSort.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSimPre.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSim2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItCover.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItShape.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.ItRep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma applyw_unique : forall ws a i v,
  (forall j w w', In (j, w) ws -> In (j, w') ws -> w = w') ->
  In (i, v) ws -> 0 <= i < arr_len a -> arr_get (applyw ws a) i = v.
Proof.
  intros ws a i v U Hin Hr.
  destruct (applyw_in ws a i (in_map_fst ws i v Hin) Hr) as [v' [Hin' E]]. rewrite E. exact (U i v' v Hin' Hin).
Qed.

Theorem inflate_table_TBLg : forall ty lens lens_ofs codes tbl table bits work,
  0 <= codes <= 288 -> codes <= arr_len work ->
  (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15) ->
  ty_ok ty (lens_list lens lens_ofs codes) bits ->
  1 <= bits <= 15 -> 0 <= table -> table + it_room ty <= arr_len tbl ->
  let '(ret, tbl', toff, bits', work') := inflate_table ty lens lens_ofs codes tbl table bits work in
  (arr_len tbl' = arr_len tbl /\ arr_len work' = arr_len work) /\
  (ret = 0 ->
   1 <= bits' <= 15 /\ table + 2 ^ bits' <= toff <= table + it_room ty
   /\ TBLg ty (fun x => arr_get tbl' (table + x)) bits' (toff - table)
   /\ (forall i, ~ (table <= i < toff) -> arr_get tbl' i = arr_get tbl i)).
Proof.
  intros ty lens lens_ofs codes tbl table bits work Hcodes Hwork Hlens Hty Hbits Htable Hroom.
  set (ll := lens_list lens lens_ofs codes) in *. set (wl := wl_of ll).
  assert (Hty' : ty = CODES -> codes <= 19).
  { intros ->. cbn [ty_ok] in Hty. destruct Hty as [H _]. subst ll. unfold NC, lens_list in H. unfold zlength in H. rewrite length_map, length_seq in H. lia. }
  rewrite (inflate_table_abs ty lens lens_ofs codes ll wl table bits Hcodes Hlens eq_refl eq_refl Hty' Hbits tbl work Hwork).
  pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItSimPre.Hll lens lens_ofs codes ll wl Hcodes Hlens eq_refl eq_refl) as Hll.
  pose proof (it_abs_props wl ll table bits Hll eq_refl Hbits ty Hty) as P.
  pose proof (it_abs_rep wl ll table bits Hll eq_refl Hbits ty Hty) as R.
  destruct (it_abs wl ll ty table bits) as [[[[ret ws] toff] bits'] ww].
  split; [split; apply arr_len_applyw|].
  intros Hret. specialize (P Hret). specialize (R Hret).
  destruct P as (P1 & P2 & P3 & P4 & P5). destruct R as (U & RR & RS).
  pose proof (Z.pow_pos_nonneg 2 bits' ltac:(lia) ltac:(lia)) as PB.
  assert (GETW : forall x v, In (table + x, v) ws -> arr_get (applyw ws tbl) (table + x) = v).
  { intros x v Hin. apply (applyw_unique ws tbl _ v U Hin). pose proof (P3 _ _ Hin). lia. }
  assert (COV : forall x, 0 <= x < toff - table -> exists v, In (table + x, v) ws /\ arr_get (applyw ws tbl) (table + x) = v).
  { intros x Hx. apply applyw_in; [apply P4; lia | lia]. }
  split; [exact P1|]. split; [exact P2|]. split.
  - split; [exact P1|]. split; [lia|]. split; [|split].
    + intros x Hx. destruct (COV x Hx) as [v [Hin ->]]. left.
      replace x with (table + x - table) at 1 by lia. apply P5. exact Hin.
    + intros x x' Hx Hx' Hb Hm. destruct (COV x ltac:(lia)) as [v [Hin E]]. rewrite E in *.
      apply GETW. apply (RR x x' v Hin Hx Hx' Hm).
    + intros x Hx Hop y y' Hy Hy' Hb Hm. destruct (COV x ltac:(lia)) as [L [HinL EL]]. rewrite EL in *.
      destruct (RS x L y y' 0 HinL Hx Hop Hy Hy') as [Hrange _].
      destruct (COV (code_val L + y) ltac:(lia)) as [v [Hin Ev]]. rewrite Ev in *.
      rewrite Z.add_assoc in Hin.
      destruct (RS x L y y' v HinL Hx Hop Hy Hy') as [_ Hrep].
      apply GETW. rewrite Z.add_assoc. apply Hrep; [exact Hin | exact Hm].
  - intros i Hi. apply applyw_other. intros v Hin. pose proof (P3 _ _ Hin). lia.
Qed.
End RefInflateSafeR.

Module RefInflateSafeA6.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItTable.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeR.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeF3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma NC_lens_list : forall lens ofs n, 0 <= n -> NC (lens_list lens ofs n) = n.
Proof.
  intros lens ofs n Hn. unfold NC, lens_list, zlength. rewrite length_map, length_seq. lia.
Qed.

Lemma lens_list_forall : forall (P : Z -> Prop) lens ofs n,
  (forall i, ofs <= i < ofs + n -> P (arr_get lens i)) -> Forall P (lens_list lens ofs n).
Proof.
  intros P lens ofs n H. unfold lens_list. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx as [k [<- Hk]]. apply in_seq in Hk. apply H. lia.
Qed.


Section TableArms.
  Variable iv : ivariant.
Variable flush : Z.

  Lemma arm_CODELENS_safe : arm_safe CODELENS (arm_CODELENS ivar_ref flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_CODELENS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct HMF as (HCm & Hbx & Hnl & Hnd & Hh & HLs & HT).
    pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & CA2 & CA3 & CS & CL0).
    assert (HP0 : PHIr r <= PHI w0).
    { unfold PHI at 1 in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. change (rank CODELENS) with 0 in HP. unfold PHIr. lia. }
    assert (HCL : CL s c r).
    { unfold CL. repeat (split; [first [assumption | lia]|]). exact HWB. }
    apply POST_bind.
    pose proof (codelens_while_spec c 321 s r HCL ltac:(cbn; lia)) as W.
    destruct (codelens_while 321 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|exact (proj1 W)|destruct W].
    destruct W as [(-> & HCL1 & Hh1 & En1 & Ed1 & P1 & Ep1 & Q1 & _)|(Hm1 & HW1 & P1 & Ep1 & Ei1 & Eo1)].
    2:{
        arun gs_eq. rewrite Hm1. change (BAD =? BAD) with true. cbv iota. rewrite aret_eq. apply POST_ARun; [exact HW1|].
        lazymatch goal with |- _ < PHI ?w => set (PW0 := PHI w) in *; clearbody PW0 end.
        unfold PHI. cbn [w_s w_c w_r]. rewrite Hm1. change (rank BAD) with 0. unfold PHIr in *. lia. }
    destruct (Q1 (proj2 Hh)) as [P1' Hb1]. clear Q1 P1.
    pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & _ & Hnl1 & Hnd1 & Hh1' & HLs1 & HT1 & HWF1 & HWB1).
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    arun gs_eq. rewrite E1. change (CODELENS =? BAD) with false. cbv iota.
    acase C256.
    { arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1. apply CORE_length; exact HC1.
        + eapply REGS_cview; [exact HR1|reflexivity|reflexivity].
        + exact (proj2 HCm1).
        + exact I.
        + exact HWB1.
      - phi_goal. unfold PHIr in *. lia. }
    pose proof (inflate_table_TBLg LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite CB3; lia)) as TL.
    match goal with |- context [inflate_table LENS ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] => destruct (inflate_table LENS a1 a2 a3 a4 a5 a6 a7) as [[[[retL tblL] nextL] lenbitsL] workL] end.
    destruct TL as [[TL5 TL6] TL].
    cbv beta iota. aflat. arun us_eq. aflat. arun ur_eq.
    acase CrL.
    { arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1; [rewrite TL6; reflexivity | rewrite TL5; reflexivity | apply CORE_length; exact HC1].
        + eapply REGS_cview; [apply REGS_ret; exact HR1|reflexivity|reflexivity].
        + exact (proj2 HCm1).
        + exact I.
        + exact HWB1.
      - phi_goal. unfold PHIr in *. lia. }
    assert (RL0 : retL = 0) by (destruct (Z.eqb_spec retL 0); [assumption|discriminate CrL]).
    specialize (TL RL0). destruct TL as (TL1 & TL2 & TL3 & TL4). cbn [it_room] in TL2. unfold ENOUGH_LENS in TL2.
    arun gs_eq. sacc.
    pose proof (inflate_table_TBLg DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL
                  ltac:(lia) ltac:(rewrite TL6, CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite TL5, CB3; lia)) as TD.
    match goal with |- context [inflate_table DISTS ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] => destruct (inflate_table DISTS a1 a2 a3 a4 a5 a6 a7) as [[[[retD tblD] nextD] distbitsD] workD] end.
    destruct TD as [[TD5 TD6] TD].
    cbv beta iota. aflat. arun us_eq. aflat. arun ur_eq.
    acase CrD.
    { arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1; [rewrite TD6, TL6; reflexivity | rewrite TD5, TL5; reflexivity | apply CORE_length; exact HC1].
        + eapply REGS_cview; [apply REGS_ret; apply REGS_ret; exact HR1|reflexivity|reflexivity].
        + exact (proj2 HCm1).
        + exact I.
        + exact HWB1.
      - phi_goal. unfold PHIr in *. lia. }
    assert (RD0 : retD = 0) by (destruct (Z.eqb_spec retD 0); [assumption|discriminate CrD]).
    specialize (TD RD0). destruct TD as (TD1 & TD2 & TD3 & TD4). cbn [it_room] in TD2. unfold ENOUGH_DISTS in TD2.
    aflat. arun set_mode_eq.
    match goal with |- POST _ (_ ?w) => assert (HW3 : WINV w) end.
    { winv_split.
      - core_keep HC1; [rewrite TD6, TL6; reflexivity | rewrite TD5, TL5; reflexivity | apply CORE_length; exact HC1].
      - eapply REGS_cview; [apply REGS_ret; apply REGS_ret; exact HR1|reflexivity|reflexivity].
      - split; [common_keep HCm1|]. split; [exact Hb1|]. unfold tables. sacc. split.
        + cbn [cpok]. split; [lia|]. exists (nextL - 0). split; [lia|].
          apply (TBLg_ext LENS (fun x => arr_get tblL (0 + x))); [|exact TL3]. intros x Hx. apply TD4. lia.
        + cbn [cpok]. split; [lia|]. exists (nextD - nextL). split; [lia|]. exact TD3.
      - exact HWF1.
      - exact HWB1. }
    acase Cz.
    - aleave. exact HW3.
    - match goal with |- POST _ (_ (mkW ?s3 ?c3 ?r3)) => apply (POST_arm LEN_ (arm_LEN_ ivar_ref) w0 s3 c3 r3 arm_LEN__safe HW3) end.
      + reflexivity.
      + phi_goal. unfold PHIr in *. lia.
  Qed.


  Definition LL (s : inflate_state) (c : icall) (r : iregs) : Prop :=
    CORE s /\ REGS c r /\ is_mode s = LENLENS /\ common s /\ ir_bits r < 8
    /\ 4 <= is_ncode s <= 19 /\ 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 0 <= is_have s <= is_ncode s
    /\ (forall k, 0 <= k < is_have s -> 0 <= arr_get (is_lens s) (arr_get order_a k) <= 7)
    /\ ir_out r = arr_len (ic_outbuf c) /\ (is_wbits s = 0 -> ir_put r = 0).

  Lemma lenlens_while1_S : forall k w,
    lenlens_while1 (S k) w = (do s0 <- gs (fun s0 => s0) ;
                              if is_have s0 <? is_ncode s0 then
                                NEEDBITS 3 ;;
                                do b <- BITS 3 ;
                                do s1 <- gs (fun s1 => s1) ;
                                set_lens (arr_get order_a (is_have s1)) b ;;
                                us (fun s1 => iset_have s1 (wrap32 (is_have s1 + 1))) ;;
                                DROPBITS 3 ;;
                                lenlens_while1 k
                              else aret tt)%am w.
  Proof. reflexivity. Qed.

  Lemma lenlens_while1_spec : forall c k s r,
    LL s c r -> is_ncode s - is_have s <= Z.of_nat k ->
    match lenlens_while1 k (mkW s c r) with
    | ARun _ (mkW s' c' r') => c' = c /\ LL s' c' r' /\ is_have s' = is_ncode s' /\ is_ncode s' = is_ncode s
        /\ is_nlen s' = is_nlen s /\ is_ndist s' = is_ndist s /\ PHIr r' <= PHIr r /\ ir_put r' = ir_put r
        /\ (is_have s < is_ncode s -> PHIr r' + 8 <= PHIr r)
        /\ is_codes s' = is_codes s /\ is_work s' = is_work s
    | ALeave w' => WINV w'
    | ARet _ _ => False
    end.
  Proof.
    intros c k. induction k as [|k IH]; intros s r HLL Hk.
    - cbn [lenlens_while1]. unfold aret. pose proof HLL as (_ & _ & _ & _ & _ & _ & _ & _ & Hh & _).
      cbn in Hk. repeat (split; [first [reflexivity | assumption | lia]|]); first [reflexivity | assumption | lia].
    - pose proof HLL as (HC & HR & E & HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs & HWF & HWB). regs_open HR.
      pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
      rewrite lenlens_while1_S. mrun gs_eq. cbn [w_s].
      destruct (Z.ltb_spec (is_have s) (is_ncode s)) as [LT|GE].
      2:{ unfold aret. repeat (split; [first [reflexivity | assumption | lia]|]); first [reflexivity | assumption | lia]. }
      rewrite ?abind_assoc. unfold abind at 1.
      destruct (NEEDBITS_spec c 3 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      2:{ rewrite EQ. pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
          unfold WINV. cbn [w_s w_c w_r]. rewrite E. mred. split; [exact HC|]. split; [exact HR1|].
          split; [|split; [rewrite Eo1; exact HWF|rewrite Ep1; exact HWB]]. repeat (split; [first [assumption | lia]|]). exact HLs. }
      rewrite EQ. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      mrun BITS_eq. mrun gs_eq. cbn [w_s]. unfold set_lens. mrun us_eq. mrun us_eq. mrun DROPBITS_eq. sacc.
      rewrite (BITSv_mod (ir_hold r1) 3) by lia. pose proof (mod_pow2_range (ir_hold r1) 3 ltac:(lia)) as MV.
      rewrite wrap16_id by lia. rewrite !wrap32_id by lia.
      pose proof (order_a_range (is_have s) ltac:(lia)) as OR.
      match goal with |- context [lenlens_while1 k (mkW ?s1 ?c1 ?r1')] =>
        specialize (IH s1 r1'); assert (HLL1 : LL s1 c r1') end.
      { unfold LL. sacc. split; [core_keep HC; apply CORE_length; exact HC|].
        split; [apply REGS_holdbits; [exact HR1|]; apply HB_drop; [split; [exact RB1|exact RHO1]|lia]|].
        split; [exact E|]. split; [common_keep HCm|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split.
        - intros j Hj. rewrite arr_get_set. unfold arr_inb. rewrite CA1.
          replace ((0 <=? arr_get order_a (is_have s)) && (arr_get order_a (is_have s) <? 320)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
          destruct (Z.eqb_spec (arr_get order_a (is_have s)) (arr_get order_a j)) as [Ej|Ej]; cbn [andb]; [lia|].
          apply HLs. destruct (Z.eq_dec j (is_have s)) as [->|]; [congruence|lia].
        - split; [rewrite Eo1; exact HWF|rewrite Ep1; exact HWB]. }
      specialize (IH HLL1 ltac:(sacc; lia)).
      destruct (lenlens_while1 k _) as [u [s' c' r'] | w' | rc w']; [|exact IH|exact IH].
      revert IH. sacc. intros (-> & HLL' & Hh' & Enc & Enl & End & P' & Ep' & _ & Ecd & Ewk).
      unfold PHIr in *. revert P'. sacc. intros P'.
      repeat (split; [first [reflexivity | assumption | lia]|]). exact Ewk.
  Qed.

  Lemma lenlens_while2_S : forall k w,
    lenlens_while2 (S k) w = (do s0 <- gs (fun s0 => s0) ;
                              if is_have s0 <? 19 then
                                set_lens (arr_get order_a (is_have s0)) 0 ;;
                                us (fun s1 => iset_have s1 (wrap32 (is_have s1 + 1))) ;;
                                lenlens_while2 k
                              else aret tt)%am w.
  Proof. reflexivity. Qed.

  Lemma lenlens_while2_spec : forall c k s r,
    CORE s -> 0 <= is_have s <= 19 -> 19 - is_have s <= Z.of_nat k ->
    (forall j, 0 <= j < is_have s -> 0 <= arr_get (is_lens s) (arr_get order_a j) <= 7) ->
    exists lens', lenlens_while2 k (mkW s c r) = ARun tt (mkW (iset_have (iset_lens s lens') 19) c r)
      /\ arr_len lens' = 320 /\ (forall j, 0 <= j < 19 -> 0 <= arr_get lens' (arr_get order_a j) <= 7).
  Proof.
    intros c k. induction k as [|k IH]; intros s r HC Hh Hk HLs.
    - exists (is_lens s). cbn in Hk. assert (E19 : is_have s = 19) by lia.
      pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
      split; [cbn [lenlens_while2]; unfold aret; f_equal; rewrite <- E19; destruct s; reflexivity|].
      split; [exact CA1|]. intros j Hj. apply HLs. lia.
    - pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
      rewrite lenlens_while2_S. unfold abind at 1. rewrite gs_eq. cbn [w_s].
      destruct (Z.ltb_spec (is_have s) 19) as [LT|GE].
      + unfold set_lens. rewrite ?abind_assoc. unfold abind at 1. rewrite us_eq. unfold abind at 1. rewrite us_eq. sacc.
        change (wrap16 0) with 0. rewrite wrap32_id by lia.
        pose proof (order_a_range (is_have s) ltac:(lia)) as OR.
        match goal with |- context [lenlens_while2 k (mkW ?s1 _ _)] =>
          destruct (IH s1 r) as (lens' & EQ & HL' & HLs') end.
        * core_keep HC. apply CORE_length; exact HC.
        * sacc. lia.
        * sacc. lia.
        * sacc. intros j Hj. rewrite arr_get_set. unfold arr_inb. rewrite CA1.
          replace ((0 <=? arr_get order_a (is_have s)) && (arr_get order_a (is_have s) <? 320)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
          destruct (Z.eqb_spec (arr_get order_a (is_have s)) (arr_get order_a j)) as [Ej|Ej]; cbn [andb]; [lia|].
          apply HLs. destruct (Z.eq_dec j (is_have s)) as [->|]; [congruence|lia].
        * exists lens'. rewrite EQ. revert HL' HLs'. sacc. intros HL' HLs'. split; [destruct s; reflexivity|]. split; [exact HL'|exact HLs'].
      + exists (is_lens s). assert (E19 : is_have s = 19) by lia.
        split; [unfold aret; f_equal; rewrite <- E19; destruct s; reflexivity|].
        split; [exact CA1|]. intros j Hj. apply HLs. lia.
  Qed.

  Lemma arm_LENLENS_safe : arm_safe LENLENS (arm_LENLENS ivar_ref flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_LENLENS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct HMF as (HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs).
    assert (HP0 : PHIr r <= PHI w0).
    { unfold PHI at 1 in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. change (rank LENLENS) with 0 in HP. unfold PHIr. lia. }
    assert (HLL : LL s c r) by (unfold LL; repeat (split; [first [assumption | lia]|]); exact HWB).
    apply POST_bind.
    pose proof (lenlens_while1_spec c 19 s r HLL ltac:(cbn; lia)) as W1.
    destruct (lenlens_while1 19 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|exact W1|destruct W1].
    destruct W1 as (-> & HLL1 & Hh1 & Enc & Enl & End & P1 & Ep1 & Q1 & Ecd & Ewk). specialize (Q1 (proj2 Hh)).
    pose proof HLL1 as (HC1 & HR1 & E1 & HCm1 & Hb1 & Hnc1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HWF1 & HWB1).
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    apply POST_bind.
    destruct (lenlens_while2_spec c 19 s1 r1 HC1 ltac:(lia) ltac:(cbn; lia) HLs1) as (lens19 & EQ2 & HL19 & HLs19).
    rewrite EQ2.
    assert (HLs' : forall i, 0 <= i < 0 + 19 -> 0 <= arr_get lens19 i <= 7).
    { intros i Hi. destruct (order_a_onto i ltac:(lia)) as [j [Hj <-]]. apply HLs19. exact Hj. }
    arun gs_eq. sacc.
    pose proof (inflate_table_TBLg CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; pose proof (HLs' i Hi); lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; split; [lia|]; split; [lia|]; apply lens_list_forall; intros i Hi; pose proof (HLs' i Hi); lia)
                  ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; rewrite CB3; lia)) as TC.
    match goal with |- context [inflate_table CODES ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] => destruct (inflate_table CODES a1 a2 a3 a4 a5 a6 a7) as [[[[retC tblC] nextC] lenbitsC] workC] end.
    destruct TC as [[TC5 TC6] TC].
    cbv beta iota. aflat. arun us_eq. aflat. arun ur_eq.
    acase CrC.
    { arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1; [rewrite HL19, CB1; reflexivity | rewrite TC6; reflexivity | rewrite TC5; reflexivity | apply CORE_length; exact HC1].
        + eapply REGS_cview; [apply REGS_ret; exact HR1|reflexivity|reflexivity].
        + exact (proj2 HCm1).
        + exact I.
        + exact HWB1.
      - phi_goal. unfold PHIr in *. lia. }
    assert (RC0 : retC = 0) by (destruct (Z.eqb_spec retC 0); [assumption|discriminate CrC]).
    specialize (TC RC0). destruct TC as (TC1 & TC2 & TC3 & TC4). cbn [it_room] in TC2.
    aflat. arun us_eq. arun set_mode_eq.
    apply (POST_arm CODELENS (arm_CODELENS ivar_ref flush) _ _ _ _ arm_CODELENS_safe).
    - winv_split.
      + core_keep HC1; [rewrite HL19, CB1; reflexivity | rewrite TC6; reflexivity | rewrite TC5; reflexivity | apply CORE_length; exact HC1].
      + eapply REGS_cview; [apply REGS_ret; exact HR1|reflexivity|reflexivity].
      + split; [common_keep HCm1|]. split; [left; exact Hb1|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [intros i Hi; exfalso; lia|].
        cbn [cpok]. split; [lia|]. exists (nextC - 0). split; [lia|]. exact TC3.
      + exact HWF1.
      + exact HWB1.
    - reflexivity.
    - phi_norm E HP. unfold PHIr in *. lia.
  Qed.


  Lemma arm_TABLE_safe : arm_safe TABLE (arm_TABLE ivar_ref flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_TABLE.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb14].
    pose proof (CORE_length s HC) as HL0.
    destruct (NEEDBITS_spec c 14 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    2:{ eapply POST_bind_leave; [exact EQ|]. pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
        apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. split; [exact HCm|lia]. }
    eapply POST_bind_run; [exact EQ|]. cbv beta iota.
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    aflat. arun BITS_eq. aflat. arun us_eq. aflat. arun DROPBITS_eq.
    aflat. arun BITS_eq. aflat. arun us_eq. aflat. arun DROPBITS_eq.
    aflat. arun BITS_eq. aflat. arun us_eq. aflat. arun DROPBITS_eq.
    aflat. arun gs_eq. sacc.
    rewrite (wrap32_id (ir_bits r1 - 5)) by lia. rewrite (wrap32_id (ir_bits r1 - 5 - 5)) by lia. rewrite (wrap32_id (ir_bits r1 - 5 - 5 - 4)) by lia.
    rewrite !BITSv_mod by (repeat (try apply Z.shiftr_nonneg); lia).
    pose proof (mod_pow2_range (ir_hold r1) 5 ltac:(lia)) as M1.
    pose proof (mod_pow2_range (Z.shiftr (ir_hold r1) 5) 5 ltac:(lia)) as M2.
    pose proof (mod_pow2_range (Z.shiftr (Z.shiftr (ir_hold r1) 5) 5) 4 ltac:(lia)) as M3.
    match goal with |- POST _ (_ (mkW _ _ ?r4)) => set (r' := r4) in *; assert (HR' : REGS c r') end.
    { subst r'. apply REGS_holdbits; [apply REGS_holdbits; [apply REGS_holdbits; [exact HR1|]|]|].
      all: repeat (apply HB_drop); try (split; [exact RB1|exact RHO1]); lia. }
    acase Cbad.
    - arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * eapply REGS_cview; [exact HR'|reflexivity|reflexivity].
        * exact (proj2 HCm).
        * exact I.
        * subst r'. sacc. rewrite Ep1. exact HWB.
      + phi_norm E HP. subst r'. sacc. lia.
    - apply Bool.orb_false_iff in Cbad as [C1 C2]. apply Z.ltb_ge in C1. apply Z.ltb_ge in C2.
      aflat. arun us_eq. arun set_mode_eq.
      apply (POST_arm LENLENS (arm_LENLENS ivar_ref flush) _ _ _ _ arm_LENLENS_safe).
      + winv_split.
        * core_keep HC. exact HL0.
        * exact HR'.
        * split; [common_keep HCm|]. subst r'. sacc. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          intros k Hk. exfalso. lia.
        * subst r'. sacc. rewrite Eo1. exact HWF.
        * subst r'. sacc. rewrite Ep1. exact HWB.
      + reflexivity.
      + phi_norm E HP. subst r'. sacc. lia.
  Qed.
End TableArms.
End RefInflateSafeA6.

Module RefInflateSafeS1.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section Dispatch.
  Variable flush : Z.

  Theorem dispatch_safe : forall w0 s c r,
    WINV (mkW s c r) -> PHI (mkW s c r) <= PHI w0 -> POST w0 (dispatch ivar_ref flush (mkW s c r)).
  Proof.
    intros w0 s c r HW HP. unfold dispatch. arun gs_eq. cbv zeta.
    Ltac try_arm lem := lazymatch goal with |- POST ?w0 ((if is_mode ?s =? ?M then _ else _) (mkW _ ?c ?r)) =>
      destruct (Z.eqb_spec (is_mode s) M) as [E|?NE]; [exact (lem w0 s c r ltac:(assumption) E ltac:(assumption))|] end.
    try_arm (arm_HEAD_safe). try_arm (arm_FLAGS_safe). try_arm (arm_TIME_safe). try_arm (arm_OS_safe).
    try_arm (arm_EXLEN_safe). try_arm (arm_EXTRA_safe). try_arm (arm_NAME_safe). try_arm (arm_COMMENT_safe).
    try_arm (arm_HCRC_safe). try_arm (arm_DICTID_safe ivar_ref flush). try_arm (arm_DICT_safe ivar_ref flush).
    try_arm (arm_TYPE_safe ivar_ref flush). try_arm (arm_TYPEDO_safe ivar_ref flush). try_arm (arm_STORED_safe ivar_ref flush).
    try_arm (arm_COPY__safe). try_arm (arm_COPY_safe). try_arm (arm_TABLE_safe flush). try_arm (arm_LENLENS_safe flush).
    try_arm (arm_CODELENS_safe flush). try_arm (arm_LEN__safe). try_arm (arm_LEN_safe). try_arm (arm_LENEXT_safe).
    try_arm (arm_DIST_safe). try_arm (arm_DISTEXT_safe). try_arm (arm_MATCH_safe ivar_ref). try_arm (arm_LIT_safe).
    try_arm (arm_CHECK_safe). try_arm (arm_LENGTH_safe). try_arm (arm_DONE_safe). try_arm (arm_BAD_safe). try_arm (arm_MEM_safe).
    exfalso. unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (_ & _ & HMF & _). unfold MF in HMF.
    repeat match goal with N : is_mode s <> ?K |- _ => rewrite (proj2 (Z.eqb_neq _ _) N) in HMF; clear N end.
    cbn [orb] in HMF. exact HMF.
  Qed.
End Dispatch.


Lemma PHI_nonneg : forall w, WINV w -> 0 <= PHI w.
Proof.
  intros [s c r] HW. unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (_ & (RN & RH & _ & RP & RL & _ & [RB _] & _) & _).
  unfold PHI. cbn [w_s w_c w_r]. pose proof (rank_range (is_mode s)). lia.
Qed.


Section Loops.
  Variable flush : Z.

  Definition lstep (w : iw) : iw + (istop * iw) :=
    match dispatch ivar_ref flush w with
    | ARun _ w' => inl w'
    | ALeave w' => inr (SLeave, w')
    | ARet rc w' => inr (SRet rc, w')
    end.

  Lemma inf_loop_nat : forall m w, WINV w -> PHI w < Z.of_nat m ->
    let '(stop, w') := iterZ (Z.of_nat m) lstep (fun w0 => (SLeave, w0)) w in
    WINV w' /\
    match stop with
    | SLeave => exists w1, WINV w1 /\ dispatch ivar_ref flush w1 = ALeave w'
    | SRet rc => INV (w_s w')
    end.
  Proof.
    induction m as [|m IH]; intros w HW HP.
    { exfalso. pose proof (PHI_nonneg w HW). cbn in HP. lia. }
    rewrite iterZ_step by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
    unfold lstep at 1. destruct w as [s c r].
    pose proof (dispatch_safe flush (mkW s c r) s c r HW ltac:(lia)) as D.
    destruct (dispatch ivar_ref flush (mkW s c r)) as [u w'|w'|rc w'] eqn:ED.
    - destruct D as [HW' HP']. apply IH; [exact HW'|lia].
    - split; [exact D|]. exists (mkW s c r). split; [exact HW|exact ED].
    - exact D.
  Qed.

  Theorem inf_loop_post : forall w, WINV w ->
    PHI w < 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64) ->
    let '(stop, w') := inf_loop ivar_ref flush w in
    WINV w' /\
    match stop with
    | SLeave => exists w1, WINV w1 /\ dispatch ivar_ref flush w1 = ALeave w'
    | SRet rc => INV (w_s w')
    end.
  Proof.
    intros w HW HP. unfold inf_loop. change (fun w0 : iw => _) with lstep at 1.
    pose proof (PHI_nonneg w HW).
    rewrite <- (Z2Nat.id (64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64))) by lia.
    apply inf_loop_nat; [exact HW|]. rewrite Z2Nat.id by lia. exact HP.
  Qed.


  Section Checker.
    Variable arm_ok : Z -> iw -> bool.
    Hypothesis OK : forall w, WINV w -> arm_ok flush w = true.

    Definition okstep' (w : iw) : iw + bool :=
      if arm_ok flush w then
        match dispatch ivar_ref flush w with
        | ARun _ w' => inl w'
        | ALeave _ => inr true
        | ARet _ _ => inr true
        end
      else inr false.

    Lemma iter_ok_nat : forall m w, WINV w -> PHI w < Z.of_nat m ->
      iterZ (Z.of_nat m) okstep' (fun _ => false) w = true.
    Proof.
      induction m as [|m IH]; intros w HW HP.
      { exfalso. pose proof (PHI_nonneg w HW). cbn in HP. lia. }
      rewrite iterZ_step by lia. replace (Z.of_nat (S m) - 1) with (Z.of_nat m) by lia.
      unfold okstep' at 1. rewrite (OK w HW). destruct w as [s c r].
      pose proof (dispatch_safe flush (mkW s c r) s c r HW ltac:(lia)) as D.
      destruct (dispatch ivar_ref flush (mkW s c r)) as [u w'|w'|rc w'].
      - destruct D as [HW' HP']. apply IH; [exact HW'|lia].
      - reflexivity.
      - reflexivity.
    Qed.

    Theorem iter_ok : forall n w, WINV w -> PHI w < n -> iterZ n okstep' (fun _ => false) w = true.
    Proof.
      intros n w HW HP. pose proof (PHI_nonneg w HW).
      rewrite <- (Z2Nat.id n) by lia. apply iter_ok_nat; [exact HW|]. rewrite Z2Nat.id by lia. exact HP.
    Qed.
  End Checker.
End Loops.
End RefInflateSafeS1.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS1.

Module RefInflateSafeS2.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Inflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Inflate.InflateArms.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeD.InftreesCoverage.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.ItProof.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflate_runA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeH.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeH.RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeF3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeF3.RefInflateSafeA1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma MF_ext : forall m s s' h b,
  is_wrap s' = is_wrap s -> is_flags s' = is_flags s -> is_check s' = is_check s -> is_wbits s' = is_wbits s ->
  is_length s' = is_length s -> is_offset s' = is_offset s -> is_extra s' = is_extra s ->
  is_lencode s' = is_lencode s -> is_distcode s' = is_distcode s -> is_lenbits s' = is_lenbits s -> is_distbits s' = is_distbits s ->
  is_ncode s' = is_ncode s -> is_nlen s' = is_nlen s -> is_ndist s' = is_ndist s -> is_have s' = is_have s ->
  is_lens s' = is_lens s -> is_codes s' = is_codes s ->
  is_hold s' = h -> is_bits s' = b ->
  MF m s h b -> MF m s' h b.
Proof.
  intros m s s' h b E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 Eh Eb H.
  unfold MF, common, tables, lneed, cneed, code_at in *.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17.
  destruct (m =? MEM) eqn:EM.
  -
    revert H. repeat match goal with |- (if ?c then _ else _) -> _ => lazymatch c with MEM =? MEM => fail | _ => destruct c; [intros X; exact X|] end end.
    intros _. exact (conj Eh Eb).
  - revert H. repeat match goal with |- (if ?c then _ else _) -> (if ?c then _ else _) => destruct c; [intros X; exact X|] end.
    intros X; exact X.
Qed.

Ltac csplit := lazymatch goal with |- _ /\ _ => split; csplit | _ => idtac end.

Lemma MF_set_check : forall m s ck h b,
  (is_flags s = 0 -> adler_canon ck) -> (m = FLAGS -> adler_canon ck) -> MF m s h b -> MF m (iset_check s ck) h b.
Proof.
  intros m s ck h b Hc Hf. unfold MF, common, tables, lneed, cneed, code_at. sacc.
  destruct (Z.eqb_spec m FLAGS) as [->|NE].
  { cbn. intros [A B]. split; [exact A|exact (Hf eq_refl)]. }
  repeat match goal with |- (if ?c then _ else _) -> (if ?c then _ else _) => destruct c end;
    first [ intros X; exact X
          | intros X; decompose [and] X; csplit; first [assumption | exact Hc] ].
Qed.


Lemma CORE_updw : forall s src end_ copy, CORE s ->
  is_window_blk s <> None -> 0 <= copy ->
  CORE (updw_core s src end_ copy).
Proof.
  intros s src end_ copy HC Hb Hcopy.
  pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
  destruct (C2 Hb) as [WL WB].
  unfold updw_core, sA.
  pose proof (wrap32_range (Z.shiftl 1 (is_wbits s))) as VR. unfold shl32 in *.
  set (V := wrap32 (Z.shiftl 1 (is_wbits s))) in *.
  set (s1 := if is_wsize s =? 0 then iset_whave (iset_wnext (iset_wsize s V) 0) 0 else s).
  assert (H1 : is_wsize s1 = V /\ 0 <= is_whave s1 <= V /\ 0 <= is_wnext s1 /\ (V <> 0 -> is_wnext s1 < V) /\ (is_whave s1 < V -> is_wnext s1 = is_whave s1)
               /\ is_window_blk s1 = is_window_blk s /\ arr_len (is_window s1) = V /\ is_wbits s1 = is_wbits s /\ is_wrap s1 = is_wrap s
               /\ arr_len (is_lens s1) = 320 /\ arr_len (is_work s1) = 288 /\ arr_len (is_codes s1) = 1444 /\ is_sane s1 = 1 /\ 0 <= is_length s1 < 2 ^ 32).
  { subst s1. destruct (Z.eqb_spec (is_wsize s) 0) as [Z0|Z0]; sacc.
    - repeat split; try assumption; try lia.
    - pose proof (C3 Z0). pose proof (C7 Z0). pose proof (C8 Z0). repeat split; try assumption; try lia. }
  clearbody s1. destruct H1 as (W1 & W2 & W3 & W4 & W5 & B1 & L1 & WB1 & WR1 & A1 & A2 & A3 & S1 & LL1).
  Ltac norm1 W1 B1 L1 WB1 WR1 A1 A2 A3 S1 V := unfold shl32; rewrite ?arr_len_blit, ?W1, ?B1, ?L1, ?WB1, ?WR1, ?A1, ?A2, ?A3, ?S1; fold V.
  destruct (Z.leb_spec (is_wsize s1) copy) as [LE|GT]; unfold CORE; sacc; norm1 W1 B1 L1 WB1 WR1 A1 A2 A3 S1 V.
  - repeat split; first [ lia | reflexivity | (intros X; exfalso; exact (Hb X)) | (intros X; exfalso; exact (WB X))
            | (intros _; split; [first [lia | assumption | reflexivity] | exact WB]) | (intros; lia) | (pose proof W5; intros; lia) ].
  - rewrite (wrap32_id (V - is_wnext s1)) by lia.
    set (dist := if copy <? V - is_wnext s1 then copy else V - is_wnext s1).
    assert (Hd : 0 <= dist <= copy /\ dist <= V - is_wnext s1) by (subst dist; destruct (Z.ltb_spec copy (V - is_wnext s1)); lia).
    rewrite (wrap32_id (copy - dist)) by lia.
    destruct (Z.eqb_spec (copy - dist) 0) as [CD|CD]; cbn [negb]; sacc; norm1 W1 B1 L1 WB1 WR1 A1 A2 A3 S1 V.
    + rewrite (wrap32_id (is_wnext s1 + dist)) by lia.
      destruct (Z.eqb_spec (is_wnext s1 + dist) V) as [EV|EV]; sacc; norm1 W1 B1 L1 WB1 WR1 A1 A2 A3 S1 V;
        (destruct (Z.ltb_spec (is_whave s1) V) as [WH|WH]; sacc; norm1 W1 B1 L1 WB1 WR1 A1 A2 A3 S1 V);
        rewrite ?(wrap32_id (is_whave s1 + dist)) by lia; repeat split; first [ lia | reflexivity | (intros X; exfalso; exact (Hb X)) | (intros X; exfalso; exact (WB X))
            | (intros _; split; [first [lia | assumption | reflexivity] | exact WB]) | (intros; lia) | (pose proof W5; intros; lia) ].
    + repeat split; first [ lia | reflexivity | (intros X; exfalso; exact (Hb X)) | (intros X; exfalso; exact (WB X))
            | (intros _; split; [first [lia | assumption | reflexivity] | exact WB]) | (intros; lia) | (pose proof W5; intros; lia) ].
Qed.

Lemma updw_core_fields : forall s src end_ copy,
  let s' := updw_core s src end_ copy in
  is_mode s' = is_mode s /\ is_wrap s' = is_wrap s /\ is_flags s' = is_flags s /\ is_check s' = is_check s /\ is_wbits s' = is_wbits s
  /\ is_length s' = is_length s /\ is_offset s' = is_offset s /\ is_extra s' = is_extra s
  /\ is_lencode s' = is_lencode s /\ is_distcode s' = is_distcode s /\ is_lenbits s' = is_lenbits s /\ is_distbits s' = is_distbits s
  /\ is_ncode s' = is_ncode s /\ is_nlen s' = is_nlen s /\ is_ndist s' = is_ndist s /\ is_have s' = is_have s
  /\ is_lens s' = is_lens s /\ is_codes s' = is_codes s /\ is_hold s' = is_hold s /\ is_bits s' = is_bits s /\ is_total s' = is_total s
  /\ is_window_blk s' = is_window_blk s /\ is_last s' = is_last s.
Proof.
  intros s src end_ copy. cbv zeta. unfold updw_core, sA.
  destruct (is_wsize s =? 0); sacc;
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity);
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity);
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity);
  match goal with |- context [if ?c then _ else _] => destruct c end; sacc; try (csplit; reflexivity).
Qed.


Lemma arr_get_of_list_byte : forall l i, bytes_ok l -> 0 <= arr_get (arr_of_list l) i < 256.
Proof.
  intros l i Hb. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  destruct ((0 <=? i) && (i <? 0 + zlength l) && arr_inb (arr_make (zlength l) 0) i) eqn:C.
  - unfold bytes_ok in Hb. rewrite Forall_forall in Hb.
    apply andb_prop in C as [C _]. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
    apply Hb. apply nth_In. unfold zlength in C2. lia.
  - unfold arr_make. rewrite arr_get_init. lia.
Qed.

Ltac munf := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY,
  TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.
Ltac mode_lit E := first [ apply Z.eqb_eq in E | apply Bool.orb_true_iff in E; destruct E as [E|E]; mode_lit E ].

Lemma MF_mode_range : forall m s h b, MF m s h b -> HEAD <= m <= MEM.
Proof.
  intros m s h b HM. unfold MF in HM. revert HM.
  repeat match goal with |- (if ?c then _ else _) -> _ =>
    let E := fresh "E" in destruct c eqn:E;
    [ mode_lit E; revert E; clear; intros; munf; lia |] end.
  intros X. destruct X.
Qed.

Lemma INV_check : forall st, INV st -> inflateStateCheck st = false.
Proof.
  intros st (_ & _ & HM). apply MF_mode_range in HM. unfold inflateStateCheck.
  destruct (Z.ltb_spec (is_mode st) HEAD) as [L|L]; [munf; lia|].
  destruct (Z.ltb_spec SYNC (is_mode st)) as [G|G]; [munf; lia|reflexivity].
Qed.

Lemma WINV_entry : forall st zc,
  INV st -> zcall_wf zc ->
  WINV (W0 st zc) /\ PHI (W0 st zc) < 64 * (ic_avail_in (w_c (W0 st zc)) + ic_avail_out (w_c (W0 st zc)) + 64).
Proof.
  intros st zc (HC & HBs & HM) (Hz & Hao & Hlen & Hby).
  pose proof (zlength_nonneg (zc_input zc)) as LN. destruct HBs as [B1 B2].
  assert (HR : REGS (icall_of_zcall zc) (mkIR 0 (zlength (zc_input zc)) 0 (zc_avail_out zc) (is_hold st) (is_bits st) (zlength (zc_input zc)) (zc_avail_out zc) Z_OK)).
  { unfold REGS, HB, icall_of_zcall. cbn [ic_input ic_outbuf ir_next ir_have ir_put ir_left ir_hold ir_bits].
    rewrite arr_len_of_list. unfold arr_make. rewrite arr_len_init.
    repeat (split; [first [lia | intros i; apply arr_get_of_list_byte; exact Hby] |]). lia. }
  unfold W0, s_entry. destruct (Z.eqb_spec (is_mode st) TYPE) as [ET|ET].
  - split.
    + unfold WINV. cbn [w_s w_c w_r]. sacc. split; [core_keep HC; apply CORE_length; exact HC|]. split; [exact HR|].
      rewrite ET in HM. split; [revert HM; mred; intros HM; split; [common_keep (proj1 HM) | exact (proj2 HM)]|].
      split; [mred; unfold icall_of_zcall; cbn [ic_outbuf]; unfold arr_make; rewrite arr_len_init; reflexivity|].
      intros _; reflexivity.
    + unfold PHI. cbn [w_s w_c w_r]. sacc. unfold icall_of_zcall. cbn [ic_avail_in ic_avail_out]. mred. lia.
  - split.
    + unfold WINV. cbn [w_s w_c w_r]. cbn [ir_hold ir_bits ir_out ir_put]. split; [exact HC|]. split; [exact HR|]. split; [exact HM|].
      split; [|intros _; reflexivity].
      unfold WF. destruct ((is_mode st =? LENGTH) || (is_mode st =? DONE) || (is_mode st =? BAD)); [exact I|].
      unfold icall_of_zcall. cbn [ic_outbuf]. unfold arr_make. rewrite arr_len_init.
      destruct ((is_mode st =? HEAD) || (is_mode st =? FLAGS)); [split|]; reflexivity.
    + unfold PHI. cbn [w_s w_c w_r]. cbn [ir_have ir_bits ir_left]. unfold icall_of_zcall. cbn [ic_avail_in ic_avail_out].
      pose proof (rank_range (is_mode st)). lia.
Qed.


Lemma lv_fin_INV : forall flush m s2 c2 r,
  CORE s2 -> HB (ir_hold r) (ir_bits r) -> is_hold s2 = ir_hold r -> is_bits s2 = ir_bits r -> is_mode s2 = m ->
  MF m s2 (ir_hold r) (ir_bits r) ->
  (m = FLAGS -> wrap32 (ir_out r - ic_avail_out c2) = 0) ->
  INV (fst (lv_fin flush s2 c2 r)).
Proof.
  intros flush m s2 c2 r HC HBr Eh Eb Em HM Hfl.
  unfold lv_fin. cbv zeta.
  set (out := wrap32 (ir_out r - ic_avail_out c2)) in *.
  match goal with |- INV (fst (let '(a, b) := (if ?cnd then _ else _) in _)) => destruct cnd eqn:C end; cbn [fst].
  - unfold INV. sacc. rewrite Em, Eh, Eb. split; [core_keep HC; apply CORE_length; exact HC|]. split; [exact HBr|].
    apply MF_set_check.
    + sacc. intros F0. unfold UPDATE_CHECK_bytes. sacc. rewrite F0. cbn [Z.eqb negb]. unfold iadler32_upd. apply adler32_model_canon.
    + intros EM. exfalso. rewrite (Hfl EM) in C. rewrite Z.eqb_refl, Bool.andb_false_r in C. discriminate C.
    + apply (MF_ext _ s2); first [sacc; reflexivity | sacc; assumption | exact HM].
  - unfold INV. sacc. rewrite Em, Eh, Eb. split; [core_keep HC; apply CORE_length; exact HC|]. split; [exact HBr|].
    apply (MF_ext _ s2); first [sacc; reflexivity | sacc; assumption | exact HM].
Qed.

Lemma CORE_fresh_window : forall s b g,
  CORE s -> is_window_blk s = None -> is_wbits s <> 0 ->
  CORE (iset_window (iset_window_blk s (Some b)) (iarr_u8_of g 0 (shl32 1 (is_wbits s)))).
Proof.
  intros s b g HC EB WB.
  pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
  pose proof (C1 EB) as Z0.
  unfold CORE. sacc. unfold iarr_u8_of. rewrite arr_len_init. rewrite Z0.
  split; [intros X; discriminate X|]. split; [intros _; split; [reflexivity|exact WB]|].
  split; [intros X; exfalso; exact (X eq_refl)|]. split; [exact C4|]. split; [exact C5|].
  split; [intros _; exact (C6 Z0)|]. split; [intros X; exfalso; exact (X eq_refl)|]. split; [intros X; exfalso; exact (X eq_refl)|].
  split; [intros X; exfalso; exact (WB X)|]. exact (conj C10 (conj C11 (conj C12 (conj C13 C14)))).
Qed.

Lemma inf_leave_INV : forall flush s c r ch s' zr ch',
  WINV (mkW s c r) -> inf_leave hooks_pure flush (mkW s c r) ch = MRet ((s', zr), ch') -> INV s'.
Proof.
  intros flush s c r ch s' zr ch' HW.
  unfold WINV in HW. cbn [w_s w_c w_r] in HW. destruct HW as (HC & HR & HMF & HWF & HWB).
  pose proof HR as (RN & RH & RNH & RP & RL & RPL & HBr & RIN & RNI & RNO).
  pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & _).
  rewrite (inf_leave_eq hooks_pure). unfold sbind.
  assert (HCR : CORE (s_rest s r)) by (unfold s_rest; core_keep HC; apply CORE_length; exact HC).
  assert (HMR : MF (is_mode s) (s_rest s r) (ir_hold r) (ir_bits r)).
  { apply (MF_ext _ s); unfold s_rest; first [sacc; reflexivity | exact HMF]. }
  assert (HFL : is_mode s = FLAGS -> wrap32 (ir_out r - ic_avail_out (c_rest c r)) = 0).
  { intros EM. unfold c_rest. sacc. rewrite EM in HWF. revert HWF. mred. intros [E1 E2]. rewrite E1, <- RPL, E2. replace (0 + ir_left r - ir_left r) with 0 by lia. reflexivity. }
  assert (TAIL : forall s2 g, CORE s2 -> is_hold s2 = ir_hold r -> is_bits s2 = ir_bits r -> is_mode s2 = is_mode s ->
            MF (is_mode s) s2 (ir_hold r) (ir_bits r) ->
            sret (lv_fin flush s2 (c_rest c r) r) g = MRet ((s', zr), ch') -> INV s').
  { intros s2 g HC2 Eh Eb Em HM2 E. unfold sret in E.
    apply (f_equal (fun mm => match mm with MRet p => fst (fst p) | _ => s' end)) in E. cbn [fst] in E.
    rewrite <- E. exact (lv_fin_INV flush (is_mode s) s2 (c_rest c r) r HC2 HBr Eh Eb Em HM2 HFL). }
  destruct (lv_cond flush (s_rest s r) (c_rest c r) r) eqn:LC.
  -
    assert (WB : is_wbits s <> 0).
    { intros W. destruct (C9 W) as [N _]. pose proof (C1 N) as Z0. pose proof (HWB W) as P0.
      assert (NLD : is_mode s <> LENGTH /\ is_mode s <> DONE).
      { split; intros E; rewrite E in HMF; revert HMF; mred; intros [X _]; exact (X W). }
      unfold WF in HWF.
      revert LC. unfold lv_cond, s_rest, c_rest. sacc. rewrite Z0, Z.eqb_refl. change (negb true) with false. rewrite Bool.orb_false_l.
      destruct (Z.eqb_spec (is_mode s) BAD) as [EB'|NB].
      - rewrite EB' in *. replace (BAD <? BAD) with false by reflexivity. rewrite Bool.andb_false_r. cbn [andb]. intros X; discriminate X.
      - assert (EO : ir_out r = ir_left r).
        { destruct NLD as [N1 N2]. rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2) in HWF. cbn [orb] in HWF.
          destruct ((is_mode s =? HEAD) || (is_mode s =? FLAGS)); [destruct HWF as [E1 _]|rename HWF into E1]; rewrite E1, <- RPL, P0; lia. }
        rewrite EO. replace (ir_left r - ir_left r) with 0 by lia. change (wrap32 0 =? 0) with true. cbn [negb andb]. intros X; discriminate X. }
    rewrite updatewindow_pure. cbn [mbind fst snd].
    unfold uw_pure. replace (is_window_blk (s_rest s r)) with (is_window_blk s) by reflexivity.
    pose proof (wrap32_range (ir_out r - ic_avail_out (c_rest c r))) as CP.
    destruct (is_window_blk s) as [b|] eqn:EB.
    + apply TAIL.
      * apply CORE_updw; [exact HCR | unfold s_rest; sacc; rewrite EB; intros X; discriminate X | lia].
      * rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (updw_core_fields _ _ _ _)))))))))))))))))))). reflexivity.
      * rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (updw_core_fields _ _ _ _))))))))))))))))))))). reflexivity.
      * rewrite (proj1 (updw_core_fields _ _ _ _)). reflexivity.
      * pose proof (updw_core_fields (s_rest s r) (ic_outbuf (c_rest c r)) (ic_next_out (c_rest c r)) (wrap32 (ir_out r - ic_avail_out (c_rest c r)))) as F.
        cbv zeta in F. decompose [and] F.
        apply (MF_ext _ (s_rest s r)); first [assumption | exact HMR | idtac].
        all: match goal with H : ?f (updw_core ?ba _ _ _) = ?f ?ba |- ?f _ = _ => rewrite H; reflexivity end.
    + destruct ch as [[b g]|].
      * set (s1 := iset_window (iset_window_blk (s_rest s r) (Some b)) (iarr_u8_of g 0 (shl32 1 (is_wbits (s_rest s r))))).
        assert (HC1 : CORE s1) by (subst s1; apply CORE_fresh_window; [exact HCR | exact EB | exact WB]).
        assert (HM1 : MF (is_mode s) s1 (ir_hold r) (ir_bits r)).
        { apply (MF_ext _ s); subst s1; unfold s_rest; first [sacc; reflexivity | exact HMF]. }
        apply TAIL.
        -- apply CORE_updw; [exact HC1 | subst s1; sacc; intros X; discriminate X | lia].
        -- rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (updw_core_fields _ _ _ _)))))))))))))))))))). reflexivity.
        -- rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (updw_core_fields _ _ _ _))))))))))))))))))))). reflexivity.
        -- rewrite (proj1 (updw_core_fields _ _ _ _)). reflexivity.
        -- pose proof (updw_core_fields s1 (ic_outbuf (c_rest c r)) (ic_next_out (c_rest c r)) (wrap32 (ir_out r - ic_avail_out (c_rest c r)))) as F.
           cbv zeta in F. decompose [and] F.
           apply (MF_ext _ s1); first [assumption | exact HM1 | idtac].
           all: first [ match goal with H : ?f (updw_core ?ba _ _ _) = ?f ?ba |- ?f _ = _ => rewrite H; reflexivity end | subst s1; sacc; reflexivity ].
      *
        unfold sret. intros E.
        apply (f_equal (fun mm => match mm with MRet p => fst (fst p) | _ => s' end)) in E. cbn [fst] in E.
        rewrite <- E. unfold lv_mem. cbn [fst]. rewrite lv_pre_shape. cbv zeta. cbn [fst].
        match goal with |- context [if ?bb then _ else _] => destruct bb end;
          (unfold INV, s_rest; sacc; split; [core_keep HC; apply CORE_length; exact HC|]; split; [exact HBr|]; mred; split; reflexivity).
  -
    cbn [sret mbind fst snd]. intros E. apply (TAIL (s_rest s r) ch); first [exact HCR | reflexivity | exact HMR | exact E].
Qed.
End RefInflateSafeS2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefInflateSafeS3.RefInflateSafeS2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac csplit := lazymatch goal with |- _ /\ _ => split; csplit | _ => idtac end.


Theorem inflate_INV : forall s zc flush ch s' zr,
  INV s -> zcall_wf zc -> ipure (inflate_m ivar_ref hooks_pure s zc flush) ch = Some (s', zr) -> INV s'.
Proof.
  intros s zc flush ch s' zr HI Hz E.
  unfold ipure in E. rewrite (inflate_m_W0 hooks_pure) in E by (apply INV_check; exact HI).
  destruct (WINV_entry s zc HI Hz) as [HW HP].
  pose proof (inf_loop_post flush (W0 s zc) HW HP) as L.
  destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop w'].
  destruct stop as [|rc].
  - destruct L as [HW' _]. destruct w' as [s1 c1 r1].
    destruct (inf_leave hooks_pure flush (mkW s1 c1 r1) ch) as [p| | |] eqn:EL; try discriminate E.
    destruct p as [[s2 zr2] ch']. cbn [fst] in E.
    assert (E2 : s2 = s') by (injection E; intros _ X; exact X). subst s2.
    exact (inf_leave_INV flush s1 c1 r1 ch s' zr2 ch' HW' EL).
  - destruct L as [_ HI']. unfold sret in E. cbn [fst] in E.
    assert (E2 : w_s w' = s') by (injection E; intros _ X; exact X). rewrite <- E2. exact HI'.
Qed.


Lemma init_u16_range : forall g base i, 0 <= init_u16 g base i < 65536.
Proof.
  intros g base i. unfold init_u16.
  pose proof (wrap8_range (g (base + 2 * i))). pose proof (wrap8_range (g (base + 2 * i + 1))). lia.
Qed.
Lemma init_u32_range : forall g base i, 0 <= init_u32 g base i < 2 ^ 32.
Proof.
  intros g base i. unfold init_u32.
  pose proof (init_u16_range g base (2 * i)). pose proof (init_u16_range g base (2 * i + 1)). lia.
Qed.

Lemma INV_fresh : forall init b wb, ir2_bad wb = false -> INV (ireset_s (s_pre init b wb)).
Proof.
  intros init b wb Hbad.
  pose proof (ir2_ranges wb Hbad) as (Rw & Rb & Rwb).
  assert (WZ : ir2_wb wb = 0 -> ir2_wrap wb <> 0).
  { unfold ir2_wb, ir2_wrap. destruct (Z.ltb_spec wb 0); [lia|]. intros _. rewrite Z.shiftr_div_pow2 by lia.
    assert (0 <= wb / 2 ^ 4) by (apply Z.div_pos; lia). lia. }
  unfold INV. unfold ireset_s, s_pre, is_of_oracle. sacc.
  split; [|split; [exact HB_0 | mred; sacc; split; [intros _; lia | intros X; exfalso; lia]]].
  unfold CORE. sacc. unfold iarr_u16_of, iarr_u32_of. rewrite ?arr_len_init.
  pose proof (init_u32_range (fun _ => 0) (lay_length lay_ref) 0) as LR.
  repeat match goal with |- _ /\ _ => split end;
    first [ reflexivity | lia | exact LR
          | intros X; exfalso; first [exact (X eq_refl) | lia]
          | intros X0; split; [reflexivity | apply WZ; exact X0]
          | intros; lia ].
Qed.

Theorem init_INV : forall zc wb ch s zr,
  ipure (inflateInit2_m ivar_ref hooks_pure zc wb) ch = Some (Some s, zr) -> INV s.
Proof.
  intros zc wb ch s zr E. unfold ipure in E. rewrite (inflateInit2_m_eq hooks_pure) in E.
  unfold sbind in E. cbn [zalloc hooks_pure mbind fst snd] in E.
  destruct ch as [[b init]|].
  - destruct (ir2_bad wb) eqn:Hbad.
    + unfold sbind in E. cbn [zfree hooks_pure mbind fst snd sret] in E. discriminate E.
    + unfold sret in E. cbn [fst] in E.
      assert (E2 : ireset_s (s_pre init b wb) = s) by (injection E; intros _ X; exact X).
      rewrite <- E2. apply INV_fresh. exact Hbad.
  - unfold sret in E. cbn [fst] in E. discriminate E.
Qed.


Theorem setdict_INV : forall s zc dict ch s' zr,
  INV s -> ipure (inflateSetDictionary_m hooks_pure s zc dict) ch = Some (s', zr) -> INV s'.
Proof.
  intros s zc dict ch s' zr HI E. pose proof HI as (HC & HBs & HM).
  pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & _).
  unfold ipure, inflateSetDictionary_m in E. rewrite (INV_check s HI) in E.
  destruct (negb (is_wrap s =? 0) && negb (is_mode s =? DICT)) eqn:G1.
  { unfold sret in E. cbn [fst] in E. assert (E2 : s = s') by (injection E; intros _ X; exact X). subst s'. exact HI. }
  match type of E with context [if ?c then sret (s, zret0 _ Z_DATA_ERROR) else _] => destruct c eqn:G2 end.
  { unfold sret in E. cbn [fst] in E. assert (E2 : s = s') by (injection E; intros _ X; exact X). subst s'. exact HI. }
  assert (WB : is_wbits s <> 0).
  { intros W. destruct (C9 W) as [_ WR]. rewrite (proj2 (Z.eqb_neq _ _) WR) in G1. cbn [negb andb] in G1.
    apply Bool.negb_false_iff in G1. apply Z.eqb_eq in G1. rewrite G1 in HM. revert HM. mred. intros [X _]. exact (X W). }
  unfold sbind in E. rewrite updatewindow_pure in E. cbn [mbind fst snd] in E. unfold uw_pure in E.
  pose proof (zlength_nonneg dict) as LD.
  assert (TAIL : forall base, CORE base -> is_window_blk base <> None ->
            MF (is_mode s) base (is_hold s) (is_bits s) -> is_hold base = is_hold s -> is_bits base = is_bits s -> is_mode base = is_mode s ->
            INV (iset_havedict (updw_core base (arr_of_list dict) (zlength dict) (zlength dict)) 1)).
  { intros base HCb HBb HMb Eh Eb Em.
    pose proof (updw_core_fields base (arr_of_list dict) (zlength dict) (zlength dict)) as F. cbv zeta in F. decompose [and] F.
    unfold INV. sacc.
    repeat match goal with H : ?f (updw_core ?ba ?x ?y ?y) = ?f ?ba |- context [?f (updw_core ?ba ?x ?y ?y)] => rewrite H end.
    rewrite Em, Eh, Eb.
    split; [|split; [exact HBs|]].
    - pose proof (CORE_updw base (arr_of_list dict) (zlength dict) (zlength dict) HCb HBb LD) as HC2.
      core_keep HC2. apply CORE_length. exact HC2.
    - apply (MF_ext _ base); first [ sacc; assumption | sacc; congruence | exact HMb ]. }
  Ltac getE E s' := apply (f_equal (fun o => match o with Some p => fst p | None => s' end)) in E; cbn [fst] in E; rewrite <- E.
  destruct (is_window_blk s) as [b|] eqn:EB.
  - cbn [sret fst] in E. getE E s'.
    apply TAIL; [exact HC | rewrite EB; intros X; discriminate X | exact HM | reflexivity | reflexivity | reflexivity].
  - destruct ch as [[b g]|].
    + cbn [sret fst] in E. getE E s'.
      apply (TAIL (iset_window (iset_window_blk s (Some b)) (iarr_u8_of g 0 (shl32 1 (is_wbits s))))).
      * apply CORE_fresh_window; [exact HC | exact EB | exact WB].
      * sacc. intros X; discriminate X.
      * apply (MF_ext _ s); first [sacc; reflexivity | exact HM].
      * reflexivity. * reflexivity. * reflexivity.
    + cbn [sret fst] in E. getE E s'.
      unfold INV. sacc. split; [core_keep HC; apply CORE_length; exact HC|]. split; [exact HBs|]. mred. split; reflexivity.
Qed.


Theorem ireach_INV : forall st, ireach st -> INV st.
Proof.
  intros st H. induction H.
  - eapply init_INV. eassumption.
  - eapply inflate_INV; eassumption.
  - eapply setdict_INV; eassumption.
Qed.

Theorem ireach_WINV : forall st zc, ireach st -> zcall_wf zc ->
  WINV (W0 st zc) /\ PHI (W0 st zc) < 64 * (ic_avail_in (w_c (W0 st zc)) + ic_avail_out (w_c (W0 st zc)) + 64).
Proof. intros st zc HR Hz. exact (WINV_entry st zc (ireach_INV st HR) Hz). Qed.

Theorem inflate_safe_gen : forall (arm_ok : Z -> iw -> bool) flush,
  (forall w, WINV w -> arm_ok flush w = true) ->
  forall st zc, ireach st -> zcall_wf zc -> loop_ok arm_ok flush (W0 st zc) = true.
Proof.
  intros arm_ok flush OK st zc HR Hz.
  destruct (ireach_WINV st zc HR Hz) as [HW HP].
  unfold loop_ok. change (okstep arm_ok flush) with (okstep' flush arm_ok).
  exact (iter_ok flush arm_ok OK _ _ HW HP).
Qed.
