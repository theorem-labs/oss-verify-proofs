(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefAdler_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateInitLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateEnd1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateDict1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateDict2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateDictM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateDict3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SD.
  Variable ds : deflate_state.
Variable zc : ZCall.
Variable aout : Z.
Variable dict : list Z.
  Definition sd_cs : cstrm := cstrm_of_call (zc_ao zc aout).
  Definition sd_s0 : deflate_state := set_strm ds sd_cs.
  Definition sd_s3 : deflate_state := fst (sd_split (ds_wrap ds) (sd_s2 sd_s0 dict) dict).
  Definition sd_dict : list Z := snd (sd_split (ds_wrap ds) (sd_s2 sd_s0 dict) dict).
  Definition sd_clr : bool := (ds_w_size ds <=? zlength dict) && (ds_wrap ds =? 0).
  Definition sd_cs3 : cstrm := if ds_wrap ds =? 1 then cset_adler sd_cs (adler32_upd (cs_adler sd_cs) dict) else sd_cs.

End SD.

Section Proofs.

  Section Call.
  Variable sp : Z.
Variable ZP : Z.
Variable nin : Z.
Variable ain : Z.
Variable nout : Z.
Variable aout : Z.
Variable S : Z.
Variable ds : deflate_state.
Variable zc : ZCall.
Variable pd : Z.
Variable dict : list Z.
Variable ra : Z.
  Hypothesis Hzok : zstrm_ok (zc_strm zc).
  Hypothesis Hdok : bytes_ok dict.
  Hypothesis Hdl : 0 < zlength dict < 2 ^ 32.
  Hypothesis HAP : ZP + ZS_SIZE <= pd \/ pd + zlength dict <= ZP.
  Local Notation ws := (ds_w_size ds).
  Local Notation hs := (ds_hash_size ds).
  Local Notation dl := (zlength dict).

  Local Notation SL := 192320. Local Notation SD' := 192352. Local Notation SB := 192384.

  Ltac rcs_via Hfr Hprev :=
    let r := fresh "r" in let Hr := fresh "Hr" in
    intros r Hr; rewrite <- (Hprev r Hr); apply Hfr; revert Hr; clear; intros Hr; cbn in Hr;
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; reflexivity.
  End Call.
End Proofs.

Section Api.
End Api.
