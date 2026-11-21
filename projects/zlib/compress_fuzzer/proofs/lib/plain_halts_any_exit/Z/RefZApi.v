(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import String.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

Definition pc_deflateInit2 : Z := 0x17e04.
Definition pc_deflateInit : Z := 0x181b0.
Definition pc_deflateSetDictionary : Z := 0x151ac.
Definition pc_deflateBound : Z := 0x15c8c.
Definition pc_deflate : Z := 0x15e54.
Definition pc_deflateEnd : Z := 0x17ca8.
Definition pc_inflateInit2 : Z := 0x18c14.
Definition pc_inflateInit : Z := 0x18dcc.
Definition pc_inflate : Z := 0x18fe4.
Definition pc_inflateEnd : Z := 0x1b74c.
Definition pc_inflateSetDictionary : Z := 0x1b9c8.
Definition pc_compress2 : Z := 0x1f8bc.
Definition pc_compressBound : Z := 0x1fa00.
Definition pc_uncompress : Z := 0x1fbec.
Definition pc_zalloc : Z := 0x10b28.
Definition pc_zfree : Z := 0x10cd0.
Definition pc_zcalloc : Z := 0x1f8a4.
Definition pc_zcfree : Z := 0x1f8b4.
Definition a_zlib_version : Z := 0x2d0a0.
Definition ZS_SIZE : Z := 112.
Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.

Definition zstrm_ok (z : zstrm) : Prop :=
  0 <= zs_total_in z < 2 ^ 64 /\ 0 <= zs_total_out z < 2 ^ 64 /\ 0 <= zs_adler z < 2 ^ 64
  /\ - 2 ^ 31 <= zs_data_type z < 2 ^ 31.

Definition zs_delta (zc : ZCall) (r : ZRet) : Prop :=
  zs_total_out (zr_strm r) = wrap64 (zs_total_out (zc_strm zc) + zlength (zr_output r))
  \/ (zr_rc r = Z_MEM_ERROR /\ zs_total_out (zr_strm r) = zs_total_out (zc_strm zc)).

Definition CH : Type := option (blk * (Z -> Z)).
Definition hooks_pure : zhooks CH :=
  mkHooks (fun _ _ => fun ch : CH => MRet (ch, ch)) (fun _ => fun ch : CH => MRet (tt, ch)).
Definition ipure {A} (m : SM CH A) (ch : CH) : option A :=
  match m ch with MRet p => Some (fst p) | _ => None end.

Section ZApi.

  Variable DS : Type.
Variable IS : Type.
Variable D : deflate_api DS.
Variable I : inflate_api IS.
  Variable garb : blk -> Z -> Z.
  Variable dblocks : DS -> list (blk * Z).
  Variable iblocks : IS -> list (blk * Z).
  Definition HOOK_DEPTH : Z := 65536.

  Definition Wstrm (strm : Z) : Z -> Prop := fun z => strm <= z < strm + ZS_SIZE.

  Definition Wstrm_out (strm pout n : Z) : Z -> Prop :=
    fun z => (strm <= z < strm + ZS_SIZE) \/ (pout <= z < pout + n).

  Definition Wc2 (pdl dest n : Z) : Z -> Prop :=
    fun z => (pdl <= z < pdl + 8) \/ (dest <= z < dest + n).
  Variable draw : DS -> list blk.
  Variable iraw : IS -> list blk.
  Variable DEQ : DS -> DS -> Prop.
  Variable IEQ : IS -> IS -> Prop.

  Definition deflate_deq_stmt : Prop :=
    forall ds1 ds2 zc f, DEQ ds1 ds2 ->
      snd (da_deflate D ds1 zc f) = snd (da_deflate D ds2 zc f)
      /\ DEQ (fst (da_deflate D ds1 zc f)) (fst (da_deflate D ds2 zc f)).

End ZApi.
