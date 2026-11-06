(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxMem HxStep HxHook.
From OSSVerify.Proofs.openssl.bignum.lib.HXS Require Import HxsHook.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope uint63_scope.

Definition NQ : int := 8.
Definition ASZI : int := 64.
Definition RSZI : int := 128.
Definition ASHI : int := 8.
Definition RSHI : int := 16.
Definition CSQI : int := 288.

Definition ALQ : int := 3.
Definition TQ_GOT : int := 1.
Definition TQ_A : int := 2.
Definition TQ_R : int := 6.
Definition TQ_STK : int := 8.
Definition TQ_SHB : int := 9.
Definition TQ_RA : int := 10.
Definition TQ_GP : int := 11.
Definition TQ_TP : int := 12.
Definition TQ_S0 : int := 13.
Definition TQ_LA : int := 40.
Definition NEXTQ : int := 48.

Definition SHBW : w64 := W false 2147450880.
Definition GOT_SHB_CELL : int := 5917624.
Definition SHB_CELL : int := 6738232.

Definition limb_cellsq (t0 : int) : itrie cell :=
  fold_left (fun tr k => iset 3%nat tr k (CP (t0 + k) (W false 0))) [0; 1; 2; 3; 4; 5; 6; 7] IEmpty.

Definition cq_got : region := RG (Some GOT_SHB_CELL) 8 3 false DUnk 0%nat (iset 0%nat IEmpty 0 (CW (W false SHB_CELL) 255)).
Definition cq_shb : region := RG (Some SHB_CELL) 8 3 false DUnk 0%nat (iset 0%nat IEmpty 0 (CW SHBW 255)).
Definition cq_a : region := RG None ASZI ALQ false DUnk 3%nat (limb_cellsq TQ_LA).
Definition cq_ash : region := shadow_region ASHI false DZero.
Definition cq_r : region := RG None RSZI ALQ true DUnk (depth_for 60 RSZI 0) IEmpty.
Definition cq_rsh : region := shadow_region RSHI false DZero.
Definition cq_stk : region := RG None CSQI 0 true DUnk (depth_for 60 CSQI 0) IEmpty.

Definition MQ_got : mem := mset IEmpty TQ_GOT cq_got.
Definition MQ_shb : mem := mset MQ_got TQ_SHB cq_shb.
Definition MQ_a : mem := mset MQ_shb TQ_A cq_a.
Definition MQ_ash : mem := mset MQ_a 3 cq_ash.
Definition MQ_rsh : mem := mset MQ_ash 7 cq_rsh.
Definition MQ_r : mem := mset MQ_rsh TQ_R cq_r.
Definition MQ : mem := mset MQ_r TQ_STK cq_stk.

Definition absQ : abstab := [(5917624, 5917632, 1); (6738232, 6738240, 9)].

Definition regsq : regfile hval :=
  RF (VP 10 (W false 0)) (VP 8 (W false CSQI)) (VP 11 (W false 0)) (VP 12 (W false 0)) VU VU VU (VP 13 (W false 0)) (VP 14 (W false 0))
     (VP 6 (W false 0)) (VP 2 (W false 0)) VU VU VU VU VU VU
     (VP 15 (W false 0)) (VP 16 (W false 0)) (VP 17 (W false 0)) (VP 18 (W false 0)) (VP 19 (W false 0)) (VP 20 (W false 0))
     (VP 21 (W false 0)) (VP 22 (W false 0)) (VP 23 (W false 0)) (VP 24 (W false 0)) VU VU VU VU.

Definition PC_CQ : w64 := W false 0x22e558.
Definition PC_CQ_RET : w64 := W false 0x22f9c0.

Definition SQ : sstate := SS PC_CQ regsq RNone MQ absQ NEXTQ.
