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
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateEnd1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateBound1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateDict1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition sd_pc2 (wrap st look : Z) : Z :=
  if wrap =? 2 then 0x153d8
  else if wrap =? 1 then (if (st =? 42) && (look =? 0) then 0x1540c else 0x153d8)
  else 0x152a4.

Section W2.
End W2.

Section Adl.
End Adl.

Definition sd_n (ws dl : Z) : Z := if dl <? ws then dl else ws.
Definition sd_pd (ws dl pd : Z) : Z := if dl <? ws then pd else pd + (dl - ws).

Section PostAdl.
End PostAdl.

Definition sd_pc3 (ws dl wrap : Z) : Z :=
  if dl <? ws then 0x152cc else if wrap =? 0 then 0x15448 else 0x152cc.

Section B152ac.
End B152ac.

Section Clear1.
End Clear1.

Section Clear2.
End Clear2.

Section Call1.
End Call1.

Section Head.

Definition sd_head_pc (second : bool) : Z := if second then 0x15388 else 0x152f0.
End Head.

Section Body.
End Body.

Section Call2.
End Call2.

Section Final.
End Final.
