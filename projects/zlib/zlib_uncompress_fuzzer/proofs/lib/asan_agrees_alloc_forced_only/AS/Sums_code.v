(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6fcac : bv 32 := 0x02060063.
Lemma D_6fcac : decode_any W_6fcac = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fcb0 : bv 32 := 0x00c50633.
Lemma D_6fcb0 : decode_any W_6fcb0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fcb4 : bv 32 := 0x00050693.
Lemma D_6fcb4 : decode_any W_6fcb4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fcb8 : bv 32 := 0x0005c703.
Lemma D_6fcb8 : decode_any W_6fcb8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fcbc : bv 32 := 0x00e68023.
Lemma D_6fcbc : decode_any W_6fcbc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fcc0 : bv 32 := 0x00168693.
Lemma D_6fcc0 : decode_any W_6fcc0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fcc4 : bv 32 := 0x00158593.
Lemma D_6fcc4 : decode_any W_6fcc4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fcc8 : bv 32 := 0xfec698e3.
Lemma D_6fcc8 : decode_any W_6fcc8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fccc : bv 32 := 0x00008067.
Lemma D_6fccc : decode_any W_6fccc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd28 : bv 32 := 0x00a666b3.
Lemma D_6fd28 : decode_any W_6fd28 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd2c : bv 32 := 0x00f6f693.
Lemma D_6fd2c : decode_any W_6fd2c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd30 : bv 32 := 0x02068063.
Lemma D_6fd30 : decode_any W_6fd30 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd34 : bv 32 := 0x04060863.
Lemma D_6fd34 : decode_any W_6fd34 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd38 : bv 32 := 0x00c50633.
Lemma D_6fd38 : decode_any W_6fd38 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd3c : bv 32 := 0x00050693.
Lemma D_6fd3c : decode_any W_6fd3c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd40 : bv 32 := 0x00b68023.
Lemma D_6fd40 : decode_any W_6fd40 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd44 : bv 32 := 0x00168693.
Lemma D_6fd44 : decode_any W_6fd44 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd48 : bv 32 := 0xfec69ce3.
Lemma D_6fd48 : decode_any W_6fd48 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd4c : bv 32 := 0x0380006f.
Lemma D_6fd4c : decode_any W_6fd4c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd50 : bv 32 := 0x02060a63.
Lemma D_6fd50 : decode_any W_6fd50 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd54 : bv 32 := 0x00c50633.
Lemma D_6fd54 : decode_any W_6fd54 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd58 : bv 32 := 0x00859693.
Lemma D_6fd58 : decode_any W_6fd58 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd5c : bv 32 := 0x00b6e5b3.
Lemma D_6fd5c : decode_any W_6fd5c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd60 : bv 32 := 0x01059693.
Lemma D_6fd60 : decode_any W_6fd60 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd64 : bv 32 := 0x00b6e5b3.
Lemma D_6fd64 : decode_any W_6fd64 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd68 : bv 32 := 0x02059693.
Lemma D_6fd68 : decode_any W_6fd68 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd6c : bv 32 := 0x00b6e5b3.
Lemma D_6fd6c : decode_any W_6fd6c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd70 : bv 32 := 0x00050693.
Lemma D_6fd70 : decode_any W_6fd70 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd74 : bv 32 := 0x00b6b023.
Lemma D_6fd74 : decode_any W_6fd74 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd78 : bv 32 := 0x00b6b423.
Lemma D_6fd78 : decode_any W_6fd78 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd7c : bv 32 := 0x01068693.
Lemma D_6fd7c : decode_any W_6fd7c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd80 : bv 32 := 0xfec6eae3.
Lemma D_6fd80 : decode_any W_6fd80 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd84 : bv 32 := 0x00008067.
Lemma D_6fd84 : decode_any W_6fd84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70258 : bv 32 := 0xff010113.
Lemma D_70258 : decode_any W_70258 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_7025c : bv 32 := 0x00113423.
Lemma D_7025c : decode_any W_7025c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70260 : bv 32 := 0x00058693.
Lemma D_70260 : decode_any W_70260 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70264 : bv 32 := 0x00100713.
Lemma D_70264 : decode_any W_70264 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70268 : bv 32 := 0x02871713.
Lemma D_70268 : decode_any W_70268 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7026c : bv 32 := 0x00170593.
Lemma D_7026c : decode_any W_7026c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70270 : bv 32 := 0x08b6f263.
Lemma D_70270 : decode_any W_70270 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_70274 : bv 32 := 0x00000593.
Lemma D_70274 : decode_any W_70274 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70278 : bv 32 := 0x00d50733.
Lemma D_70278 : decode_any W_70278 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7027c : bv 32 := 0x00750793.
Lemma D_7027c : decode_any W_7027c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_70280 : bv 32 := 0xff87f793.
Lemma D_70280 : decode_any W_70280 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_70284 : bv 32 := 0xff877613.
Lemma D_70284 : decode_any W_70284 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_70288 : bv 32 := 0x02f57463.
Lemma D_70288 : decode_any W_70288 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7028c : bv 32 := 0x02068263.
Lemma D_7028c : decode_any W_7028c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_70290 : bv 32 := 0x00000593.
Lemma D_70290 : decode_any W_70290 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70294 : bv 32 := 0x00150693.
Lemma D_70294 : decode_any W_70294 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70298 : bv 32 := 0x00068813.
Lemma D_70298 : decode_any W_70298 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7029c : bv 32 := 0xfff6c683.
Lemma D_7029c : decode_any W_7029c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_702a0 : bv 32 := 0x00d5e5b3.
Lemma D_702a0 : decode_any W_702a0 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_702a4 : bv 32 := 0x00f87663.
Lemma D_702a4 : decode_any W_702a4 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_702a8 : bv 32 := 0x00180693.
Lemma D_702a8 : decode_any W_702a8 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_702ac : bv 32 := 0xfee866e3.
Lemma D_702ac : decode_any W_702ac = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_702b0 : bv 32 := 0x00c7fa63.
Lemma D_702b0 : decode_any W_702b0 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_702b4 : bv 32 := 0x0007b683.
Lemma D_702b4 : decode_any W_702b4 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_702b8 : bv 32 := 0x00878793.
Lemma D_702b8 : decode_any W_702b8 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_702bc : bv 32 := 0x00b6e5b3.
Lemma D_702bc : decode_any W_702bc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_702c0 : bv 32 := 0xfec7eae3.
Lemma D_702c0 : decode_any W_702c0 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_702c4 : bv 32 := 0x02a66063.
Lemma D_702c4 : decode_any W_702c4 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_702c8 : bv 32 := 0x00e67e63.
Lemma D_702c8 : decode_any W_702c8 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_702cc : bv 32 := 0x40c70733.
Lemma D_702cc : decode_any W_702cc = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_702d0 : bv 32 := 0x00064503.
Lemma D_702d0 : decode_any W_702d0 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_702d4 : bv 32 := 0xfff70713.
Lemma D_702d4 : decode_any W_702d4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_702d8 : bv 32 := 0x00a5e5b3.
Lemma D_702d8 : decode_any W_702d8 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_702dc : bv 32 := 0x00160613.
Lemma D_702dc : decode_any W_702dc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_702e0 : bv 32 := 0xfe0718e3.
Lemma D_702e0 : decode_any W_702e0 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_702e4 : bv 32 := 0x0015b513.
Lemma D_702e4 : decode_any W_702e4 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_702e8 : bv 32 := 0x00813083.
Lemma D_702e8 : decode_any W_702e8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_702ec : bv 32 := 0x01010113.
Lemma D_702ec : decode_any W_702ec = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_702f0 : bv 32 := 0x00008067.
Lemma D_702f0 : decode_any W_702f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
