(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.

Module RefInffast2.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma byte_shl_lt64 : forall v k, 0 <= v < 256 -> 0 <= k <= 55 -> v * 2 ^ k < 2 ^ 64.
Proof.
  intros v k Hv Hk. pose proof (Z.pow_le_mono_r 2 k 55 ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). change (2 ^ 64) with (256 * 2 ^ 56). change (2 ^ 56) with (2 * 2 ^ 55). nia.
Qed.

Section Walk.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.



Definition refill2 (inp : arr) (fin hold bits : Z) : Z * Z * Z :=
  if bits <? 15 then (fin + 2, hold + (arr_get inp (fin + 1) * 2 ^ (bits + 8) + arr_get inp fin * 2 ^ bits), bits + 16)
  else (fin, hold, bits).

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.

Module RefInffast15.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma eqm32_szwrap_add : forall x k, (szwrap 32 x + k) mod 2 ^ 32 = (x + k) mod 2 ^ 32.
Proof. intros x k. rewrite <- Zplus_mod_idemp_l, szwrap_eqm, Zplus_mod_idemp_l by lia. reflexivity. Qed.

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast15.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast15.

Module RefInffast3.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition xslot_ok (o : Z) : Prop := o = 8 \/ o = 16 \/ o = 64 \/ o = 72.

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.


Definition len_step (inp : arr) (fin hold bits val e : Z) : Z * Z * Z * Z :=
  if e =? 0 then (fin, hold, bits, val)
  else if bits <? e then (fin + 1, (hold + arr_get inp fin * 2 ^ bits) / 2 ^ e, bits + 8 - e, (hold + arr_get inp fin * 2 ^ bits) mod 2 ^ e + val)
  else (fin, hold / 2 ^ e, bits - e, hold mod 2 ^ e + val).

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast3.

Module RefInffast4.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.


Definition dpull (inp : arr) (fin hold bits e : Z) : Z * Z * Z :=
  if bits <? e then
    if bits + 8 <? e then (fin + 2, hold + arr_get inp fin * 2 ^ bits + arr_get inp (fin + 1) * 2 ^ (bits + 8), bits + 16)
    else (fin + 1, hold + arr_get inp fin * 2 ^ bits, bits + 8)
  else (fin, hold, bits).

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast4.

Module RefInffast5.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition srcn_ok (WN fout : Z) (fr : fromptr) (n : Z) : Prop :=
  match fr with FWin i => 0 <= i /\ i + n <= WN | FOut i => 0 <= i < fout end.

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.

Local Notation XSOK xs := (forall e, In e xs -> let '(o, w, _) := e in RefInffast3.xslot_ok o /\ w = 8%nat).

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast5.

Module RefInffast6.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.

Local Notation XSOK xs := (forall e, In e xs -> let '(o, w, _) := e in RefInffast3.xslot_ok o /\ w = 8%nat).

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast6.

Module RefInffast7.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma land_m8 : forall x, Z.land x (-8) = x - x mod 8.
Proof.
  intros x. change (-8) with (Z.lnot 7). rewrite <- Z.ldiff_land.
  assert (D : Z.land (Z.ldiff x 7) (Z.land x 7) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit x i), (Z.testbit 7 i); reflexivity. }
  pose proof (Z.lor_ldiff_and x 7) as H. rewrite <- Z.lxor_lor in H by exact D. rewrite <- Z.add_nocarry_lxor in H by exact D.
  assert (M : Z.land x 7 = x mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  lia.
Qed.

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.

Local Notation XSOK xs := (forall e, In e xs -> let '(o, w, _) := e in RefInffast3.xslot_ok o /\ w = 8%nat).

Definition vec8 (P0 WB fout widx opw : Z) : bool :=
  (7 <? opw - 1) && negb ((P0 + fout - (WB + widx) + -1) mod 2 ^ 64 <? 7) && (Z.lor (P0 + fout) (WB + widx) mod 2 ^ 3 =? 0).

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast7.

Module RefInffast8.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.
Local Notation XSOK xs := (forall e, In e xs -> let '(o, w, _) := e in RefInffast3.xslot_ok o /\ w = 8%nat).


Lemma Z_to_nat_split8 : forall opw, 0 <= opw -> Z.to_nat opw = (8 * Z.to_nat (opw / 8) + Z.to_nat (opw mod 8))%nat.
Proof. intros opw H. pose proof (Z.div_mod opw 8 ltac:(lia)). pose proof (Z.mod_pos_bound opw 8 ltac:(lia)). pose proof (Z.div_pos opw 8 H ltac:(lia)). lia. Qed.

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast8.

Module RefInffast9.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.

Local Notation XSOK xs := (forall e, In e xs -> let '(o, w, _) := e in RefInffast3.xslot_ok o /\ w = 8%nat).

Local Notation vec8 := RefInffast7.vec8.

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast9.

Module RefInffast10.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast8.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.
Local Notation XSOK xs := (forall e, In e xs -> let '(o, w, _) := e in RefInffast3.xslot_ok o /\ w = 8%nat).

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast10.

Module RefInffast11.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.
Local Notation XSOK xs := (forall e, In e xs -> let '(o, w, _) := e in RefInffast3.xslot_ok o /\ w = 8%nat).
Local Notation vec8 := RefInffast7.vec8.

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast11.

Module RefInffast12.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast8.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast11.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.
Local Notation XSOK xs := (forall e, In e xs -> let '(o, w, _) := e in RefInffast3.xslot_ok o /\ w = 8%nat).

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast12.

Module RefInffast13.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.
Local Notation XSOK xs := (forall e, In e xs -> let '(o, w, _) := e in RefInffast3.xslot_ok o /\ w = 8%nat).

Definition w2vec (P0 WB fo opp wnext : Z) : bool :=
  (7 <? wnext - 1) && negb ((opp + (P0 + (fo - opp)) - WB + -1) mod 2 ^ 64 <? 7) && (Z.lor WB (opp + (P0 + (fo - opp))) mod 2 ^ 3 =? 0).

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast13.

Module RefInffast14.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast8.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.
Local Notation XSOK xs := (forall e, In e xs -> let '(o, w, _) := e in RefInffast3.xslot_ok o /\ w = 8%nat).

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast14.

Module RefInffast16.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.

Lemma XSOK72 : forall v : Z, forall e : Z * nat * Z, In e [(72, 8%nat, v)] -> let '(o, w, _) := e in RefInffast3.xslot_ok o /\ w = 8%nat.
Proof. intros v e [<-|[]]. split; [unfold RefInffast3.xslot_ok; lia | reflexivity]. Qed.

Lemma cpn_in : forall x n f, f_in (cpn x n f) = f_in f. Proof. intros. apply cpn_keep. Qed.
Lemma cpn_hold : forall x n f, f_hold (cpn x n f) = f_hold f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_bits : forall x n f, f_bits (cpn x n f) = f_bits f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_len : forall x n f, f_len (cpn x n f) = f_len f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_dist : forall x n f, f_dist (cpn x n f) = f_dist f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_op : forall x n f, f_op (cpn x n f) = f_op f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_ob : forall x n f, f_ob (cpn x n f) = cblit (x_window x) (f_from f) (f_ob f) (f_out f) n. Proof. intros. apply cpn_cblit. Qed.
Lemma cpn_from : forall x n f, f_from (cpn x n f) = fr_add (f_from f) n. Proof. intros. apply (cpn_cblit x n f). Qed.
Lemma fset_len_id : forall f, fset_len f (f_len f) = f. Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9]; reflexivity. Qed.

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast16.

Module RefInffast17.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast8.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast10.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast12.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast14.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast16.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma land_wrap32_zmask : forall h e, 0 <= h -> 0 <= e < 32 -> Z.land (wrap32 h) (zmask e) = h mod 2 ^ e.
Proof.
  intros h e Hh He. rewrite zmask_pow2, land_ones_mod, wrap32_mod by lia.
  apply Z.mod_mod_divide. exists (2 ^ (32 - e)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma land_zmask : forall h e, 0 <= e < 32 -> Z.land h (zmask e) = h mod 2 ^ e.
Proof. intros h e He. rewrite zmask_pow2, land_ones_mod by lia. reflexivity. Qed.

Lemma pull1_if_eq : forall x f e,
  0 <= f_hold f < 2 ^ f_bits f -> 0 <= f_bits f -> 0 <= e < 16 ->
  (f_bits f < e -> 0 <= arr_get (x_input x) (f_in f) < 256) ->
  (if f_bits f <? e then fpull x f else f)
  = (let '(i, h, b) := (if f_bits f <? e then (f_in f + 1, f_hold f + arr_get (x_input x) (f_in f) * 2 ^ f_bits f, f_bits f + 8)
                       else (f_in f, f_hold f, f_bits f)) in
    mkF i (f_out f) h b (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f))
  /\ (let '(i, h, b) := (if f_bits f <? e then (f_in f + 1, f_hold f + arr_get (x_input x) (f_in f) * 2 ^ f_bits f, f_bits f + 8)
                         else (f_in f, f_hold f, f_bits f)) in 0 <= h < 2 ^ b).
Proof.
  intros x f e Hh Hb He Hv. destruct (Z.ltb_spec (f_bits f) e) as [Hl|Hl].
  - destruct (fpull_eq x f ltac:(lia) ltac:(lia) ltac:(lia) (Hv Hl)) as [E B]. rewrite E. split; [reflexivity|].
    pose proof (Z.pow_pos_nonneg 2 (f_bits f) ltac:(lia) ltac:(lia)). specialize (Hv Hl). split; [nia | exact B].
  - split; [destruct f; reflexivity | exact Hh].
Qed.

Lemma dpull_eq : forall x f e,
  0 <= f_hold f < 2 ^ f_bits f -> 0 <= f_bits f -> 0 <= e < 16 ->
  (f_bits f < e -> 0 <= arr_get (x_input x) (f_in f) < 256) ->
  (f_bits f + 8 < e -> 0 <= arr_get (x_input x) (f_in f + 1) < 256) ->
  (if f_bits f <? e then if f_bits (fpull x f) <? e then fpull x (fpull x f) else fpull x f else f)
  = (let '(i, h, b) := RefInffast4.dpull (x_input x) (f_in f) (f_hold f) (f_bits f) e in
    mkF i (f_out f) h b (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f))
  /\ (let '(i, h, b) := RefInffast4.dpull (x_input x) (f_in f) (f_hold f) (f_bits f) e in 0 <= h < 2 ^ b).
Proof.
  intros x f e Hh Hb He Hv0 Hv1. unfold RefInffast4.dpull.
  destruct (Z.ltb_spec (f_bits f) e) as [Hl|Hl].
  - destruct (fpull_eq x f ltac:(lia) ltac:(lia) ltac:(lia) (Hv0 Hl)) as [E B]. rewrite E. cbn [f_bits f_in f_hold f_out f_len f_dist f_op f_from f_ob].
    pose proof (Z.pow_pos_nonneg 2 (f_bits f) ltac:(lia) ltac:(lia)) as Hp. pose proof (Hv0 Hl) as Hb0.
    destruct (Z.ltb_spec (f_bits f + 8) e) as [Hl2|Hl2].
    + set (f1 := mkF _ _ _ _ _ _ _ _ _).
      destruct (fpull_eq x f1 ltac:(subst f1; cbn; nia) ltac:(subst f1; cbn; lia) ltac:(subst f1; cbn; exact B) ltac:(subst f1; cbn; apply Hv1; lia)) as [E1 B1].
      rewrite E1. subst f1. cbn. cbn in B1. split; [f_equal; lia|]. replace (f_bits f + 16) with (f_bits f + 8 + 8) by lia. split; [nia | exact B1].
    + split; [reflexivity|]. split; [nia | exact B].
  - split; [destruct f; reflexivity | exact Hh].
Qed.

Lemma fpull2_if_eq : forall x f,
  0 <= f_hold f < 2 ^ f_bits f -> 0 <= f_bits f ->
  (f_bits f < 15 -> 0 <= arr_get (x_input x) (f_in f) < 256 /\ 0 <= arr_get (x_input x) (f_in f + 1) < 256) ->
  fpull2_if x f
  = (let '(i, h, b) := RefInffast2.refill2 (x_input x) (f_in f) (f_hold f) (f_bits f) in
    mkF i (f_out f) h b (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f))
  /\ (let '(i, h, b) := RefInffast2.refill2 (x_input x) (f_in f) (f_hold f) (f_bits f) in 0 <= h < 2 ^ b /\ b < f_bits f + 17).
Proof.
  intros x f Hh Hb Hv. unfold fpull2_if, RefInffast2.refill2.
  destruct (Z.ltb_spec (f_bits f) 15) as [Hl|Hl].
  - destruct (Hv Hl) as [Hb0 Hb1].
    destruct (fpull_eq x f ltac:(lia) ltac:(lia) ltac:(lia) Hb0) as [E B]. rewrite E.
    pose proof (Z.pow_pos_nonneg 2 (f_bits f) ltac:(lia) ltac:(lia)) as Hp.
    set (f1 := mkF _ _ _ _ _ _ _ _ _).
    destruct (fpull_eq x f1 ltac:(subst f1; cbn; nia) ltac:(subst f1; cbn; lia) ltac:(subst f1; cbn; exact B) ltac:(subst f1; cbn; exact Hb1)) as [E1 B1].
    rewrite E1. subst f1. cbn. cbn in B1. split; [f_equal; lia|]. split; [|lia].
    replace (f_hold f + (arr_get (x_input x) (f_in f + 1) * 2 ^ (f_bits f + 8) + arr_get (x_input x) (f_in f) * 2 ^ f_bits f))
      with (f_hold f + arr_get (x_input x) (f_in f) * 2 ^ f_bits f + arr_get (x_input x) (f_in f + 1) * 2 ^ (f_bits f + 8)) by lia.
    replace (f_bits f + 16) with (f_bits f + 8 + 8) by lia. split; [nia | exact B1].
  - split; [destruct f; reflexivity | lia].
Qed.

Definition ffmsg_addr (a : Z) : Z :=
  if a =? MSG_invalid_literal_length_code then 0x2dc30
  else if a =? MSG_invalid_distance_code then 0x2dc50 else 0x2dc68.

Lemma fdrop_eq : forall f op, fdrop f op = mkF (f_in f) (f_out f) (Z.shiftr (f_hold f) op) (wrap32 (f_bits f - op)) (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f).
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9] op; reflexivity. Qed.

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.

Local Ltac nf :=
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob x_window x_input x_wsize x_wnext x_whave ffx_of];
  rewrite ?cpn_in, ?cpn_out, ?cpn_hold, ?cpn_bits, ?cpn_len, ?cpn_dist, ?cpn_ob, ?cpn_from, ?fr_add_win, ?fr_add_out;
  cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob fset_in fset_out fset_hold fset_bits fset_len fset_dist fset_op fset_from fset_ob x_window x_input x_wsize x_wnext x_whave ffx_of].

Lemma dpull_cases : forall inp fin hold bits e fin' hold' bits',
  RefInffast4.dpull inp fin hold bits e = (fin', hold', bits') ->
  (e <= bits /\ bits' = bits /\ fin' = fin /\ hold' = hold)
  \/ (bits < e <= bits + 8 /\ bits' = bits + 8 /\ fin' = fin + 1)
  \/ (bits + 8 < e /\ bits' = bits + 16 /\ fin' = fin + 2).
Proof.
  intros inp fin hold bits e fin' hold' bits' H. unfold RefInffast4.dpull in H.
  destruct (Z.ltb_spec bits e); [destruct (Z.ltb_spec (bits + 8) e)|]; injection H as <- <- <-; lia.
Qed.

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast17.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast17.

Module RefInffast18.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastMem.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastMem.ItableMem2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require InffastCtx.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInffast1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast17.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Lemma len_if_eq : forall x f e,
  0 <= f_hold f < 2 ^ f_bits f -> 0 <= f_bits f < 64 -> 0 <= e < 16 -> 0 <= f_len f < 65536 ->
  (e <> 0 -> f_bits f < e -> 0 <= arr_get (x_input x) (f_in f) < 256 /\ e <= f_bits f + 8) ->
  (if negb (e =? 0) then
     fdrop (fset_len (if f_bits f <? e then fpull x f else f)
              (wrap32 (f_len (if f_bits f <? e then fpull x f else f)
                       + Z.land (wrap32 (f_hold (if f_bits f <? e then fpull x f else f))) (zmask e)))) e
   else f)
  = (let '(i, h, b, l) := RefInffast3.len_step (x_input x) (f_in f) (f_hold f) (f_bits f) (f_len f) e in
     mkF i (f_out f) h b l (f_dist f) (f_op f) (f_from f) (f_ob f)).
Proof.
  intros x f e Hh Hb He Hl Hv. unfold RefInffast3.len_step.
  pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) ltac:(lia)) as Hpe0.
  pose proof (Z.pow_le_mono_r 2 e 15 ltac:(lia) ltac:(lia)) as Hpe. change (2 ^ 15) with 32768 in Hpe.
  destruct (Z.eqb_spec e 0) as [He0|He0]; cbn [negb]; [destruct f; reflexivity|].
  destruct (Z.ltb_spec (f_bits f) e) as [Hlt|Hge].
  - destruct (Hv He0 Hlt) as [Hin Hle].
    destruct (fpull_eq x f ltac:(lia) ltac:(lia) ltac:(lia) Hin) as [E B]. rewrite E.
    cbn [f_len f_hold f_in f_out f_bits f_dist f_op f_from f_ob fset_len]. rewrite fdrop_eq.
    cbn [f_len f_hold f_in f_out f_bits f_dist f_op f_from f_ob fset_len].
    pose proof (Z.pow_pos_nonneg 2 (f_bits f) ltac:(lia) ltac:(lia)) as Hp.
    assert (H0 : 0 <= f_hold f + arr_get (x_input x) (f_in f) * 2 ^ f_bits f) by nia.
    pose proof (Z.mod_pos_bound (f_hold f + arr_get (x_input x) (f_in f) * 2 ^ f_bits f) (2 ^ e) Hpe0) as Hm.
    rewrite land_wrap32_zmask by lia. rewrite (wrap32_id (f_len f + _)) by lia.
    rewrite Z.shiftr_div_pow2 by lia. rewrite (wrap32_id (f_bits f + 8 - e)) by lia.
    f_equal; lia.
  - rewrite fdrop_eq. cbn [f_len f_hold f_in f_out f_bits f_dist f_op f_from f_ob fset_len].
    pose proof (Z.mod_pos_bound (f_hold f) (2 ^ e) Hpe0) as Hm.
    rewrite land_wrap32_zmask by lia. rewrite (wrap32_id (f_len f + _)) by lia.
    rewrite Z.shiftr_div_pow2 by lia. rewrite (wrap32_id (f_bits f - e)) by lia.
    f_equal; lia.
Qed.

Lemma dodist_ok_bits : forall x st IN ON WN k h f, dodist_ok x st IN ON WN k h f = true -> code_bits h <= f_bits f.
Proof.
  intros x st IN ON WN [|k] h f H; cbn [dodist_ok] in H; [discriminate H|].
  apply andb_prop in H as [H _]. apply Z.leb_le in H. exact H.
Qed.

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefInffast18.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInffast_run.RefInffast18.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).




Definition ff_loop (s : inflate_state) (c : icall) (r : iregs) : ffs * option (Z * option Z) :=
  iterZ (8 * ic_avail_in c + ic_avail_out c + 80)
    (fun f => match fast_trip (ffx_of s c r) s f with
              | FCont f' => if (f_in f' <? x_last (ffx_of s c r)) && (f_out f' <? x_end (ffx_of s c r)) then inl f'
                            else inr (f', None)
              | FBreak f' mode msg => inr (f', Some (mode, msg))
              end)
    (fun f => (f, None)) (ff0_of s c).

Definition ff_fin (f : ffs) : ffs :=
  let len := Z.shiftr (f_bits f) 3 in
  let f := fset_in f (f_in f - len) in
  let f := fset_bits f (wrap32 (f_bits f - Z.shiftl len 3)) in
  fset_hold f (Z.land (f_hold f) (zmask (f_bits f))).

Definition ff_post (s : inflate_state) (c : icall) (r : iregs) (x : ffx) (f : ffs) (mm : option (Z * option Z)) : iw :=
  let c := icset_outbuf c (f_ob f) in
  let c := icset_next_in c (f_in f) in
  let c := icset_next_out c (f_out f) in
  let c := icset_avail_in c (wrap32 (if f_in f <? x_last x then 5 + (x_last x - f_in f) else 5 - (f_in f - x_last x))) in
  let c := icset_avail_out c (wrap32 (if f_out f <? x_end x then 257 + (x_end x - f_out f) else 257 - (f_out f - x_end x))) in
  let s := iset_hold s (f_hold f) in
  let s := iset_bits s (f_bits f) in
  let '(s, c) := match mm with
                 | Some (mode, Some msg) => (iset_mode s mode, icset_msg c msg)
                 | Some (mode, None) => (iset_mode s mode, c)
                 | None => (s, c)
                 end in
  mkW s c r.

Lemma inflate_fast_eq : forall s c r,
  inflate_fast (mkW s c r) = let '(f, mm) := ff_loop s c r in ff_post s c r (ffx_of s c r) (ff_fin f) mm.
Proof. intros. reflexivity. Qed.

Lemma ff_fin_eq : forall f, 0 <= f_bits f < 64 ->
  ff_fin f = mkF (f_in f - f_bits f / 8) (f_out f) (f_hold f mod 2 ^ (f_bits f mod 8)) (f_bits f mod 8)
                 (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f).
Proof.
  intros f Hb. unfold ff_fin. cbn [f_in f_bits f_hold f_out f_len f_dist f_op f_from f_ob fset_in fset_bits fset_hold].
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod (f_bits f) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (f_bits f) 8 ltac:(lia)).
  rewrite (wrap32_id (f_bits f - f_bits f / 8 * 8)) by lia.
  replace (f_bits f - f_bits f / 8 * 8) with (f_bits f mod 8) by lia.
  rewrite land_zmask by lia. destruct f; reflexivity.
Qed.

Section Walk.

Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?mod64_id by lia; rewrite ?mod32_id by lia; lia.

Local Ltac mlia := Z.to_euclidean_division_equations; lia.
Local Ltac sfr := first [ apply sub_franges_here; cbn; lia | apply sub_franges_later; sfr ].

End Walk.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
