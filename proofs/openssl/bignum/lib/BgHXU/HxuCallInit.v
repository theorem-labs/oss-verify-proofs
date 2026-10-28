(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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

Definition CSTK : int := 16384.

Definition T_GOTFREE : int := 2.
Definition T_FREEIMPL : int := 3.
Definition T_MASTER : int := 4.
Definition T_STOPPED : int := 5.
Definition T_BASEONCE : int := 6.
Definition T_OPTSDONE : int := 7.
Definition T_TCBTSD : int := 8.
Definition T_TSD2 : int := 9.
Definition T_MK : int := 10.
Definition T_SA : int := 11.
Definition T_ND : int := 12.
Definition T_ES : int := 13.
Definition TC_RA : int := 14.
Definition TC_GP : int := 15.
Definition TC_S0 : int := 16.
Definition NEXTC : int := 28.

Definition w_allones : w64 := W true 9223372036854775807.

Definition cell0 (c : cell) : itrie cell := iset 0%nat IEmpty 0 c.

Definition cg_1 : region := RG None CSTK 4 true DUnk 11%nat IEmpty.
Definition cg_2 : region := RG (Some 0x31c6b8) 8 3 false DUnk 0%nat (cell0 (CW (W false 0xe94dc) 255)).
Definition cg_3 : region := RG (Some 0x31db20) 8 3 false DUnk 0%nat (cell0 (CW (W false 0xe94dc) 255)).
Definition cg_4 : region := RG (Some 0x32e4d4) 8 2 false DUnk 0%nat (cell0 (CW (W false 8589934594) 255)).
Definition cg_5 : region := RG (Some 0x32e458) 1 0 false DUnk 0%nat (cell0 (CW (W false 0) 1)).
Definition cg_6 : region := RG (Some 0x32e470) 8 3 false DUnk 0%nat (cell0 (CW (W false 4294967298) 255)).
Definition cg_7 : region := RG (Some 0x32e4b0) 8 3 false DUnk 0%nat (cell0 (CW (W false 2) 255)).
Definition cg_8 : region := RG (Some 0x330f40) 8 3 false DUnk 0%nat (cell0 (CW (W false 0x352300) 255)).
Definition cg_9 : region := RG (Some 0x352310) 8 3 false DUnk 0%nat (cell0 (CP T_MK (W false 0))).
Definition cg_10 : region := RG None 72 4 false DUnk 4%nat (iset 4%nat IEmpty 3 (CP T_SA (W false 0))).
Definition cg_11 : region := RG None 32 4 false DUnk 2%nat
  (iset 2%nat (iset 2%nat (iset 2%nat (iset 2%nat IEmpty 0 (CW (W false 1) 15)) 1 (CW (W false 0) 255)) 2 (CW (W false 1) 255)) 3 (CP T_ND (W false 0))).
Definition cg_12 : region := RG None 128 4 false DUnk 4%nat (iset 4%nat IEmpty 0 (CP T_ES (W false 0))).
Definition cg_13 : region := RG None 904 4 true DZero 7%nat
  (fold_left (fun tr k => iset 7%nat tr k (CW w_allones 255)) [88; 89; 90; 91; 92; 93; 94; 95] IEmpty).

Definition MC_2 : mem := mset IEmpty 2 cg_2.
Definition MC_3 : mem := mset MC_2 3 cg_3.
Definition MC_4 : mem := mset MC_3 4 cg_4.
Definition MC_5 : mem := mset MC_4 5 cg_5.
Definition MC_6 : mem := mset MC_5 6 cg_6.
Definition MC_7 : mem := mset MC_6 7 cg_7.
Definition MC_8 : mem := mset MC_7 8 cg_8.
Definition MC_9 : mem := mset MC_8 9 cg_9.
Definition MC_10 : mem := mset MC_9 10 cg_10.
Definition MC_11 : mem := mset MC_10 11 cg_11.
Definition MC_12 : mem := mset MC_11 12 cg_12.
Definition MC_13 : mem := mset MC_12 13 cg_13.
Definition MC : mem := mset MC_13 1 cg_1.

Definition absC : abstab :=
  [(0x31c6b8, 0x31c6c0, 2); (0x31db20, 0x31db28, 3); (0x32e4d4, 0x32e4dc, 4); (0x32e458, 0x32e459, 5); (0x32e470, 0x32e478, 6);
   (0x32e4b0, 0x32e4b8, 7); (0x330f40, 0x330f48, 8); (0x352310, 0x352318, 9)].

Definition TPVC : w64 := W false 3346328.

Definition regsC : regfile hval :=
  RF (VP 14 (W false 0)) (VP 1 (W false CSTK)) (VP 15 (W false 0)) (VC TPVC) VU VU VU (VP 16 (W false 0)) (VP 17 (W false 0))
     VU VU VU VU VU VU VU VU
     (VP 18 (W false 0)) (VP 19 (W false 0)) (VP 20 (W false 0)) (VP 21 (W false 0)) (VP 22 (W false 0)) (VP 23 (W false 0))
     (VP 24 (W false 0)) (VP 25 (W false 0)) (VP 26 (W false 0)) (VP 27 (W false 0)) VU VU VU VU.

Definition PC_ECE : w64 := W false 0xe80ac.
Definition PC_ECE_RET : w64 := W false 0xe811c.

Definition S0C : sstate := SS PC_ECE regsC RNone MC absC NEXTC.
