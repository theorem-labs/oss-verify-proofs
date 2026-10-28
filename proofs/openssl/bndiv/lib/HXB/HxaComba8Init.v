(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxMem HxStep HxHook.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXS Require Import HxsHook.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope uint63_scope.

Definition CS8AI : int := 592.
(* [comment removed for export] *)
Definition AL8A : int := 3.
Definition T8_GOT : int := 1.
Definition T8_A : int := 2.
Definition T8_B : int := 4.
Definition T8_R : int := 6.
Definition T8_STK : int := 8.
Definition T8_SHB : int := 9.
Definition T8_RA : int := 10.
Definition T8_GP : int := 11.
Definition T8_TP : int := 12.
Definition T8_S0 : int := 13.
Definition T8_LA : int := 40.     (* [comment removed for export] *)
Definition T8_LB : int := 48.     (* [comment removed for export] *)
Definition NEXT8A : int := 56.

(* [comment removed for export] *)
Definition SHBW : w64 := W false 2147450880.
Definition GOT_SHB_CELL : int := 6163672.       (* [comment removed for export] *)
Definition SHB_CELL : int := 6961656.           (* [comment removed for export] *)

Definition limb_cells (t0 : int) : itrie cell :=
  fold_left (fun tr k => iset 3%nat tr k (CP (t0 + k) (W false 0))) [0; 1; 2; 3; 4; 5; 6; 7] IEmpty.

Definition c8_got : region := RG (Some GOT_SHB_CELL) 8 3 false DUnk 0%nat (iset 0%nat IEmpty 0 (CW (W false SHB_CELL) 255)).
Definition c8_shb : region := RG (Some SHB_CELL) 8 3 false DUnk 0%nat (iset 0%nat IEmpty 0 (CW SHBW 255)).
Definition c8_a : region := RG None 64 AL8A false DUnk 3%nat (limb_cells T8_LA).
Definition c8_ash : region := shadow_region 8 false DZero.
Definition c8_b : region := RG None 64 AL8A false DUnk 3%nat (limb_cells T8_LB).
Definition c8_bsh : region := shadow_region 8 false DZero.
Definition c8_r : region := RG None 128 AL8A true DUnk (depth_for 60 128 0) IEmpty.
Definition c8_rsh : region := shadow_region 16 false DZero.
Definition c8_stk : region := RG None CS8AI 0 true DUnk (depth_for 60 CS8AI 0) IEmpty.

Definition M8_got : mem := mset IEmpty T8_GOT c8_got.
Definition M8_shb : mem := mset M8_got T8_SHB c8_shb.
Definition M8_a : mem := mset M8_shb T8_A c8_a.
Definition M8_ash : mem := mset M8_a 3 c8_ash.
Definition M8_b : mem := mset M8_ash T8_B c8_b.
Definition M8_bsh : mem := mset M8_b 5 c8_bsh.
Definition M8_rsh : mem := mset M8_bsh 7 c8_rsh.
Definition M8_r : mem := mset M8_rsh T8_R c8_r.
Definition M8A : mem := mset M8_r T8_STK c8_stk.

Definition abs8A : abstab := [(6163672, 6163680, 1); (6961656, 6961664, 9)].

Definition regs8A : regfile hval :=
  RF (VP 10 (W false 0)) (VP 8 (W false CS8AI)) (VP 11 (W false 0)) (VP 12 (W false 0)) VU VU VU (VP 13 (W false 0)) (VP 14 (W false 0))
     (VP 6 (W false 0)) (VP 2 (W false 0)) (VP 4 (W false 0)) VU VU VU VU VU
     (VP 15 (W false 0)) (VP 16 (W false 0)) (VP 17 (W false 0)) (VP 18 (W false 0)) (VP 19 (W false 0)) (VP 20 (W false 0))
     (VP 21 (W false 0)) (VP 22 (W false 0)) (VP 23 (W false 0)) (VP 24 (W false 0)) VU VU VU VU.

Definition PC_C8A : w64 := W false 2255440.        (* [comment removed for export] *)
Definition PC_C8A_RET : w64 := W false 2267412.    (* [comment removed for export] *)

Definition S8A : sstate := SS PC_C8A regs8A RNone M8A abs8A NEXT8A.
