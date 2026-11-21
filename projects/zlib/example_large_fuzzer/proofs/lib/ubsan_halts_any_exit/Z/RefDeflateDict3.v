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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFillWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFillWin4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateDict2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateDictM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Loop.
Variable S : Z.
Variable sp : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ws : Z.
Variable hs : Z.
Variable INP : arr.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation strm := (p_strm p).
Local Notation DIN := (zp_in zp).
Local Notation n := (arr_len INP).
Hypothesis Lsp : 176 <= sp /\ sp + 80 <= 2 ^ 63.
Hypothesis LS : 0 < S /\ S + 5952 <= 2 ^ 63.
Hypothesis LW : 0 < W /\ W + 2 * ws <= 2 ^ 63.
Hypothesis LPV : 0 < PV /\ PV + 2 * ws <= 2 ^ 63.
Hypothesis LHD : 0 < HD /\ HD + 2 * hs <= 2 ^ 63.
Hypothesis Lstrm : 0 < strm /\ strm + 112 <= 2 ^ 63.
Hypothesis LIN : 0 < DIN /\ DIN + n < 2 ^ 63.
Hypothesis Lws : 256 <= ws <= 32768.
Hypothesis Lhs : 256 <= hs <= 65536.
Hypothesis Ln : 0 <= n <= ws.
Hypothesis AP : apart_all [(sp - 176, 176); (S, 5952); (W, 2 * ws); (PV, 2 * ws); (HD, 2 * hs); (strm, 112); (DIN, n)].

Definition FP : franges :=
  [(sp - 176, 176); (S, 212); (S + 5888, 64); (W, 2 * ws); (PV, 2 * ws); (HD, 2 * hs); (strm, 24); (strm + 96, 8)].

Hypothesis FP_rod : forall x, in_franges FP x -> ~ (0x2f550 <= x < 0x2f9d0 + 4096).

Definition KC (t : deflate_state) : Prop :=
  ds_w_size t = ws /\ ds_hash_size t = hs /\ cs_input (ds_strm t) = INP /\ ds_wrap t = 0.

Local Ltac apart i j :=
  let H := fresh "AP" in
  pose proof (apart_get _ i j (0, 0) AP ltac:(lia) ltac:(cbn; lia)) as H;
  cbn [nth] in H; unfold apart in H; cbn [fst snd] in H.

Definition il_h (t : deflate_state) (str : Z) : Z :=
  update_hash t (ds_ins_h t) (arr_get (ds_window t) (str + (MIN_MATCH - 1))).
Definition il_s1 (t : deflate_state) (str : Z) : deflate_state := set_ins_h t (il_h t str).
Definition il_s2 (t : deflate_state) (str : Z) : deflate_state :=
  set_prev (il_s1 t str) (arr_set (ds_prev (il_s1 t str)) (Z.land str (ds_w_mask (il_s1 t str))) (arr_get (ds_head (il_s1 t str)) (il_h t str))).
Definition il_s3 (t : deflate_state) (str : Z) : deflate_state :=
  set_head (il_s2 t str) (arr_set (ds_head (il_s2 t str)) (il_h t str) (wrap16 str)).

Definition fuel_ok (f : nat) (t : deflate_state) : Prop :=
  AI t + 1 + (if MIN_MATCH <=? ds_lookahead t then 1 else 0) <= Z.of_nat f.

Definition sd_fin7 (t : deflate_state) (wrap : Z) : deflate_state :=
  set_wrap (set_match_available (set_match_length (set_prev_length (set_lookahead (set_insert (set_block_start
    (set_strstart t (ds_strstart t + ds_lookahead t)) (ds_strstart t + ds_lookahead t)) (ds_lookahead t)) 0)
    (MIN_MATCH - 1)) (MIN_MATCH - 1)) 0) wrap.
End Loop.
