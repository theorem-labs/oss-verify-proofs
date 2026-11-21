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

Definition W_6ff48 : bv 32 := 0x02060063.
Lemma D_6ff48 : decode_any W_6ff48 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff4c : bv 32 := 0x00c50633.
Lemma D_6ff4c : decode_any W_6ff4c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff50 : bv 32 := 0x00050693.
Lemma D_6ff50 : decode_any W_6ff50 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff54 : bv 32 := 0x0005c703.
Lemma D_6ff54 : decode_any W_6ff54 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff58 : bv 32 := 0x00e68023.
Lemma D_6ff58 : decode_any W_6ff58 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff5c : bv 32 := 0x00168693.
Lemma D_6ff5c : decode_any W_6ff5c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff60 : bv 32 := 0x00158593.
Lemma D_6ff60 : decode_any W_6ff60 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff64 : bv 32 := 0xfec698e3.
Lemma D_6ff64 : decode_any W_6ff64 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff68 : bv 32 := 0x00008067.
Lemma D_6ff68 : decode_any W_6ff68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffc4 : bv 32 := 0x00a666b3.
Lemma D_6ffc4 : decode_any W_6ffc4 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffc8 : bv 32 := 0x00f6f693.
Lemma D_6ffc8 : decode_any W_6ffc8 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffcc : bv 32 := 0x02068063.
Lemma D_6ffcc : decode_any W_6ffcc = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffd0 : bv 32 := 0x04060863.
Lemma D_6ffd0 : decode_any W_6ffd0 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffd4 : bv 32 := 0x00c50633.
Lemma D_6ffd4 : decode_any W_6ffd4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffd8 : bv 32 := 0x00050693.
Lemma D_6ffd8 : decode_any W_6ffd8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffdc : bv 32 := 0x00b68023.
Lemma D_6ffdc : decode_any W_6ffdc = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffe0 : bv 32 := 0x00168693.
Lemma D_6ffe0 : decode_any W_6ffe0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffe4 : bv 32 := 0xfec69ce3.
Lemma D_6ffe4 : decode_any W_6ffe4 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffe8 : bv 32 := 0x0380006f.
Lemma D_6ffe8 : decode_any W_6ffe8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffec : bv 32 := 0x02060a63.
Lemma D_6ffec : decode_any W_6ffec = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fff0 : bv 32 := 0x00c50633.
Lemma D_6fff0 : decode_any W_6fff0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fff4 : bv 32 := 0x00859693.
Lemma D_6fff4 : decode_any W_6fff4 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fff8 : bv 32 := 0x00b6e5b3.
Lemma D_6fff8 : decode_any W_6fff8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fffc : bv 32 := 0x01059693.
Lemma D_6fffc : decode_any W_6fffc = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_70000 : bv 32 := 0x00b6e5b3.
Lemma D_70000 : decode_any W_70000 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70004 : bv 32 := 0x02059693.
Lemma D_70004 : decode_any W_70004 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_70008 : bv 32 := 0x00b6e5b3.
Lemma D_70008 : decode_any W_70008 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7000c : bv 32 := 0x00050693.
Lemma D_7000c : decode_any W_7000c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70010 : bv 32 := 0x00b6b023.
Lemma D_70010 : decode_any W_70010 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70014 : bv 32 := 0x00b6b423.
Lemma D_70014 : decode_any W_70014 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70018 : bv 32 := 0x01068693.
Lemma D_70018 : decode_any W_70018 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7001c : bv 32 := 0xfec6eae3.
Lemma D_7001c : decode_any W_7001c = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_70020 : bv 32 := 0x00008067.
Lemma D_70020 : decode_any W_70020 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_704f4 : bv 32 := 0xff010113.
Lemma D_704f4 : decode_any W_704f4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_704f8 : bv 32 := 0x00113423.
Lemma D_704f8 : decode_any W_704f8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_704fc : bv 32 := 0x00058693.
Lemma D_704fc : decode_any W_704fc = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70500 : bv 32 := 0x00100713.
Lemma D_70500 : decode_any W_70500 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70504 : bv 32 := 0x02871713.
Lemma D_70504 : decode_any W_70504 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_70508 : bv 32 := 0x00170593.
Lemma D_70508 : decode_any W_70508 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7050c : bv 32 := 0x08b6f263.
Lemma D_7050c : decode_any W_7050c = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_70510 : bv 32 := 0x00000593.
Lemma D_70510 : decode_any W_70510 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70514 : bv 32 := 0x00d50733.
Lemma D_70514 : decode_any W_70514 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70518 : bv 32 := 0x00750793.
Lemma D_70518 : decode_any W_70518 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7051c : bv 32 := 0xff87f793.
Lemma D_7051c : decode_any W_7051c = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_70520 : bv 32 := 0xff877613.
Lemma D_70520 : decode_any W_70520 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_70524 : bv 32 := 0x02f57463.
Lemma D_70524 : decode_any W_70524 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_70528 : bv 32 := 0x02068263.
Lemma D_70528 : decode_any W_70528 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_7052c : bv 32 := 0x00000593.
Lemma D_7052c : decode_any W_7052c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70530 : bv 32 := 0x00150693.
Lemma D_70530 : decode_any W_70530 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70534 : bv 32 := 0x00068813.
Lemma D_70534 : decode_any W_70534 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70538 : bv 32 := 0xfff6c683.
Lemma D_70538 : decode_any W_70538 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7053c : bv 32 := 0x00d5e5b3.
Lemma D_7053c : decode_any W_7053c = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70540 : bv 32 := 0x00f87663.
Lemma D_70540 : decode_any W_70540 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70544 : bv 32 := 0x00180693.
Lemma D_70544 : decode_any W_70544 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70548 : bv 32 := 0xfee866e3.
Lemma D_70548 : decode_any W_70548 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_7054c : bv 32 := 0x00c7fa63.
Lemma D_7054c : decode_any W_7054c = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_70550 : bv 32 := 0x0007b683.
Lemma D_70550 : decode_any W_70550 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70554 : bv 32 := 0x00878793.
Lemma D_70554 : decode_any W_70554 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70558 : bv 32 := 0x00b6e5b3.
Lemma D_70558 : decode_any W_70558 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7055c : bv 32 := 0xfec7eae3.
Lemma D_7055c : decode_any W_7055c = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_70560 : bv 32 := 0x02a66063.
Lemma D_70560 : decode_any W_70560 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_70564 : bv 32 := 0x00e67e63.
Lemma D_70564 : decode_any W_70564 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70568 : bv 32 := 0x40c70733.
Lemma D_70568 : decode_any W_70568 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7056c : bv 32 := 0x00064503.
Lemma D_7056c : decode_any W_7056c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70570 : bv 32 := 0xfff70713.
Lemma D_70570 : decode_any W_70570 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_70574 : bv 32 := 0x00a5e5b3.
Lemma D_70574 : decode_any W_70574 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_70578 : bv 32 := 0x00160613.
Lemma D_70578 : decode_any W_70578 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7057c : bv 32 := 0xfe0718e3.
Lemma D_7057c : decode_any W_7057c = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_70580 : bv 32 := 0x0015b513.
Lemma D_70580 : decode_any W_70580 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70584 : bv 32 := 0x00813083.
Lemma D_70584 : decode_any W_70584 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70588 : bv 32 := 0x01010113.
Lemma D_70588 : decode_any W_70588 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7058c : bv 32 := 0x00008067.
Lemma D_7058c : decode_any W_7058c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
