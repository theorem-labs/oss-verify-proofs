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
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefAdler_run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFillWin1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFillWin2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable S : Z.
Variable sp : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.

Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation CSTL := (RefFillWin1.CSTL ds).
Local Notation LF := (RefFillWin1.LF S sp p ds).
Local Notation moreof := (RefFillWin1.moreof ds).
Local Notation CSTL_match_start := (RefFillWin1.CSTL_match_start ds).
Local Notation CSTL_strstart := (RefFillWin1.CSTL_strstart ds).
Local Notation CSTL_lookahead := (RefFillWin1.CSTL_lookahead ds).
Local Notation CSTL_block_start := (RefFillWin1.CSTL_block_start ds).
Local Notation CSTL_ins_h := (RefFillWin1.CSTL_ins_h ds).
Local Notation CSTL_insert := (RefFillWin1.CSTL_insert ds).
Local Notation CSTL_high_water := (RefFillWin1.CSTL_high_water ds).
Local Notation CSTL_set_window := (RefFillWin1.CSTL_set_window ds).
Local Notation CSTL_set_head := (RefFillWin1.CSTL_set_head ds).
Local Notation CSTL_set_prev := (RefFillWin1.CSTL_set_prev ds).
Local Ltac open_lregs H :=
  let H' := fresh "HL'" in pose proof H as H';
  destruct H' as (P20 & P2 & P8 & P9 & P18 & P19 & P21 & P22).
Local Ltac open_cstl HK :=
  pose proof HK as (Kwl & Kpl & Khl & Kin & Kwr & Kws & Khs);
  pose proof (f_equal (@arr_len Z) Kin) as KIL; cbn beta in KIL.
Local Ltac in_LF := unfold RefFillWin1.LF; repeat first [ apply sub_franges_here; cbn; lia | apply sub_franges_later ].

Definition ILINV (s : deflate_state) (str : Z) : Prop :=
  0 <= ds_hash_shift s < 32 /\ ds_hash_mask s = hs - 1 /\ ds_w_mask s = ws - 1
  /\ 0 <= str /\ ds_insert s = ds_strstart s - str /\ 0 <= ds_insert s
  /\ 0 <= ds_ins_h s < 2 ^ 32 /\ 0 <= ds_lookahead s
  /\ ds_strstart s + ds_lookahead s <= 2 * ws
  /\ (forall i, 0 <= i < 2 * ws -> 0 <= arr_get (ds_window s) i < 256)
  /\ (forall i, 0 <= i < ws -> 0 <= arr_get (ds_prev s) i < 65536)
  /\ (forall i, 0 <= i < hs -> 0 <= arr_get (ds_head s) i < 65536).

Definition il_next (s : deflate_state) (str : Z) : deflate_state :=
  let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + 2)) in
  let s1 := set_ins_h s h in
  let s2 := set_prev s1 (arr_set (ds_prev s1) (Z.land str (ds_w_mask s1)) (arr_get (ds_head s1) h)) in
  let s3 := set_head s2 (arr_set (ds_head s2) h (wrap16 str)) in
  set_insert s3 (ds_insert s3 - 1).

End Walk.
