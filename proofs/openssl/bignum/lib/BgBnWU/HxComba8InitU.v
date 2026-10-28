(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxMem HxStep HxHook.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope uint63_scope.

Definition CS8I : int := 368.
(* [comment removed for export] *)
Definition AL8 : int := 3.
Definition T8_A : int := 2.
Definition T8_B : int := 3.
Definition T8_R : int := 4.
Definition T8_RA : int := 5.
Definition T8_GP : int := 6.
Definition T8_TP : int := 7.
Definition T8_S0 : int := 8.
Definition T8_LA : int := 20.     (* [comment removed for export] *)
Definition T8_LB : int := 28.     (* [comment removed for export] *)
Definition NEXT8 : int := 36.

Definition limb_cells (t0 : int) : itrie cell :=
  fold_left (fun tr k => iset 3%nat tr k (CP (t0 + k) (W false 0))) [0; 1; 2; 3; 4; 5; 6; 7] IEmpty.

Definition c8_1 : region := RG None CS8I 0 true DUnk 6%nat IEmpty.
Definition c8_2 : region := RG None 64 AL8 false DUnk 3%nat (limb_cells T8_LA).
Definition c8_3 : region := RG None 64 AL8 false DUnk 3%nat (limb_cells T8_LB).
Definition c8_4 : region := RG None 128 AL8 true DUnk 4%nat IEmpty.

Definition M8_2 : mem := mset IEmpty 2 c8_2.
Definition M8_3 : mem := mset M8_2 3 c8_3.
Definition M8_4 : mem := mset M8_3 4 c8_4.
Definition M8 : mem := mset M8_4 1 c8_1.

Definition regs8 : regfile hval :=
  RF (VP 5 (W false 0)) (VP 1 (W false CS8I)) (VP 6 (W false 0)) (VP 7 (W false 0)) VU VU VU (VP 8 (W false 0)) (VP 9 (W false 0))
     (VP 4 (W false 0)) (VP 2 (W false 0)) (VP 3 (W false 0)) VU VU VU VU VU
     (VP 10 (W false 0)) (VP 11 (W false 0)) (VP 12 (W false 0)) (VP 13 (W false 0)) (VP 14 (W false 0)) (VP 15 (W false 0))
     (VP 16 (W false 0)) (VP 17 (W false 0)) (VP 18 (W false 0)) (VP 19 (W false 0)) VU VU VU VU.

Definition PC_C8 : w64 := W false 0x1038ec.
Definition PC_C8_RET : w64 := W false 0x105aec.

Definition S8 : sstate := SS PC_C8 regs8 RNone M8 [] NEXT8.
