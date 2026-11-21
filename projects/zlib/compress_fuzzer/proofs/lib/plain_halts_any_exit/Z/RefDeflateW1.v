(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateG.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflate1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflate2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflate3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflate4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflate5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflate6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflate7.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma pending_set_wrap : forall s v, ds_pending (set_wrap s v) = ds_pending s.
Proof. intros; reflexivity. Qed.

Lemma strm_set_last_flush : forall s v, ds_strm (set_last_flush s v) = ds_strm s.
Proof. intros; reflexivity. Qed.
Lemma strm_set_status : forall s v, ds_strm (set_status s v) = ds_strm s.
Proof. intros; reflexivity. Qed.

Definition RES_fin (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if negb (flush =? Z_FINISH) then (X, Z_OK)
  else if ds_wrap X <=? 0 then (X, Z_STREAM_END)
  else deflate_trailer X.

Definition RES_bde (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if cs_avail_out (ds_strm X) =? 0 then (set_last_flush X (-1), Z_OK) else RES_fin flush X.

Definition oka_st (X : deflate_state) : deflate_state :=
  if cs_avail_out (ds_strm X) =? 0 then set_last_flush X (-1) else X.

Definition bs_st2 (X1 : deflate_state) (b : block_state) : deflate_state :=
  if block_state_eqb b finish_started || block_state_eqb b finish_done then set_status X1 FINISH_STATE else X1.

Definition RES_bs (flush : Z) (X2 : deflate_state) (b : block_state) : deflate_state * Z :=
  match b with
  | need_more | finish_started => (oka_st X2, Z_OK)
  | block_done => RES_bde flush (flush_pending (bdone_st X2 flush))
  | finish_done => RES_fin flush X2
  end.

Definition RES_bks (flush : Z) (X : deflate_state) : deflate_state * Z :=
  match deflate_blocks X flush with
  | (s, Some rc) => (s, rc)
  | (s, None) => RES_fin flush s
  end.

Definition RES_gzh (flush : Z) (X : deflate_state) : deflate_state * Z :=
  let s2 := flush_pending (gz_st X) in
  if negb (ds_pending s2 =? 0) then (set_last_flush s2 (-1), Z_OK) else RES_bks flush s2.
Definition RES_dsp (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if ds_status X =? GZIP_STATE then RES_gzh flush X else RES_bks flush X.
Definition RES_zh (flush : Z) (X : deflate_state) : deflate_state * Z :=
  let s2 := flush_pending (zhdr_st X) in
  if negb (ds_pending s2 =? 0) then (set_last_flush s2 (-1), Z_OK) else RES_dsp flush s2.
Definition RES_42 (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if ds_status X =? INIT_STATE then (if ds_wrap X =? 0 then RES_bks flush (set_status X BUSY_STATE) else RES_zh flush X)
  else RES_dsp flush X.

Definition RES_996 (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if (ds_status X =? FINISH_STATE) && negb (cs_avail_in (ds_strm X) =? 0) then err_return X Z_BUF_ERROR else RES_42 flush X.
Definition RES_974 (flush : Z) (X : deflate_state) : deflate_state * Z :=
  let old := ds_last_flush X in
  let s1 := set_last_flush X flush in
  if negb (ds_pending s1 =? 0) then
    (let s2 := flush_pending s1 in
     if cs_avail_out (ds_strm s2) =? 0 then (set_last_flush s2 (-1), Z_OK) else RES_996 flush s2)
  else if (cs_avail_in (ds_strm s1) =? 0) && (RANK flush <=? RANK old) && negb (flush =? Z_FINISH)
       then err_return s1 Z_BUF_ERROR
       else RES_996 flush s1.
Definition RES_entry (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if Z_BLOCK <? flush then (X, Z_STREAM_ERROR)
  else if (ds_status X =? FINISH_STATE) && negb (flush =? Z_FINISH) then err_return X Z_STREAM_ERROR
  else if cs_avail_out (ds_strm X) =? 0 then err_return X Z_BUF_ERROR
  else RES_974 flush X.

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation SP := (sp - 96).
Local Notation FPOK := (RefDeflate3.FPOK ds).

Variable SAFEs : deflate_state -> Z -> Prop.
Variable SAFEf : deflate_state -> Z -> Prop.
Variable SAFEw : deflate_state -> Z -> Prop.
Variable FB : deflate_state -> option Z -> Z -> Z -> Prop.
Variable WF : deflate_state -> Prop.
Variable s0 : deflate_state.

Definition RES_abw (X : deflate_state) : deflate_state * Z :=
  if ds_wrap X <=? 0 then (X, Z_STREAM_END) else deflate_trailer X.

Definition BS_OK (X2 : deflate_state) (b : block_state) : Prop :=
  DOK X2
  /\ (b = block_done -> bdone_ok X2 flush
        /\ (cs_avail_out (ds_strm (flush_pending (bdone_st X2 flush))) <> 0 -> finish_ok WF s0 (flush_pending (bdone_st X2 flush)) flush))
  /\ (b = finish_done -> finish_ok WF s0 X2 flush).

Definition GZ_OK (s5 : deflate_state) : Prop :=
  (ds_status s5 = GZIP_STATE -> hdr_ok WF s0 s5 (gzhdr_st s5) 10)
  /\ let s6 := if Z.eqb (ds_status s5) GZIP_STATE then flush_pending (gzhdr_st s5) else s5 in
     ((ds_status s5 = GZIP_STATE -> ds_pending s6 = 0) ->
      blocks_ok SAFEs SAFEf SAFEw FB WF s0 s6 flush
      /\ (snd (deflate_blocks s6 flush) = None -> finish_ok WF s0 (fst (deflate_blocks s6 flush)) flush)).

Definition ZH_OK (s4 : deflate_state) : Prop :=
  DOK s4
  /\ (ds_status s4 = INIT_STATE -> hdr_ok WF s0 s4 (zhdr_st s4) 6)
  /\ let s5 := if Z.eqb (ds_status s4) INIT_STATE then flush_pending (zhdr_st s4) else s4 in
     ((ds_status s4 = INIT_STATE -> ds_pending s5 = 0) -> GZ_OK s5).

Definition PEND_OK (X : deflate_state) : Prop :=
  let s1 := set_last_flush X flush in
  DOK s1
  /\ (ds_pending s1 <> 0 ->
      fp_ok s1
      /\ let s2 := flush_pending s1 in
         DOK s2
         /\ (cs_avail_out (ds_strm s2) = 0 -> dpost_ok WF s0 (set_last_flush s2 (-1)) Z_OK)
         /\ (cs_avail_out (ds_strm s2) <> 0 -> body_ok SAFEs SAFEf SAFEw FB WF s0 s2 flush))
  /\ (ds_pending s1 = 0 ->
      (rank_err s0 flush -> dpost_ok WF s0 (fst (err_return s1 Z_BUF_ERROR)) Z_BUF_ERROR)
      /\ (~ rank_err s0 flush -> body_ok SAFEs SAFEf SAFEw FB WF s0 s1 flush)).

End Walk.

