(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxMem HxStep HxHook.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope uint63_scope.

Definition NQ : int := 4.
Definition ASZI : int := 32.
Definition RSZI : int := 64.
Definition CSQI : int := 96.

Definition ALQ : int := 3.
Definition TQ_A : int := 2.
Definition TQ_R : int := 3.
Definition TQ_RA : int := 4.
Definition TQ_GP : int := 5.
Definition TQ_TP : int := 6.
Definition TQ_S0 : int := 7.
Definition TQ_LA : int := 19.
Definition NEXTQ : int := 23.

Definition limb_cellsq (t0 : int) : itrie cell :=
  fold_left (fun tr k => iset 3%nat tr k (CP (t0 + k) (W false 0))) [0; 1; 2; 3] IEmpty.

Definition cq_1 : region := RG None CSQI 0 true DUnk 6%nat IEmpty.
Definition cq_2 : region := RG None ASZI ALQ false DUnk 3%nat (limb_cellsq TQ_LA).
Definition cq_3 : region := RG None RSZI ALQ true DUnk 4%nat IEmpty.

Definition MQ_2 : mem := mset IEmpty 2 cq_2.
Definition MQ_3 : mem := mset MQ_2 3 cq_3.
Definition MQ : mem := mset MQ_3 1 cq_1.

Definition regsq : regfile hval :=
  RF (VP 4 (W false 0)) (VP 1 (W false CSQI)) (VP 5 (W false 0)) (VP 6 (W false 0)) VU VU VU (VP 7 (W false 0)) (VP 8 (W false 0))
     (VP 3 (W false 0)) (VP 2 (W false 0)) VU VU VU VU VU VU
     (VP 9 (W false 0)) (VP 10 (W false 0)) (VP 11 (W false 0)) (VP 12 (W false 0)) (VP 13 (W false 0)) (VP 14 (W false 0))
     (VP 15 (W false 0)) (VP 16 (W false 0)) (VP 17 (W false 0)) (VP 18 (W false 0)) VU VU VU VU.

Definition PC_CQ : w64 := W false 0x106eac.
Definition PC_CQ_RET : w64 := W false 0x10736c.

Definition SQ : sstate := SS PC_CQ regsq RNone MQ [] NEXTQ.
