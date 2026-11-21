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

Definition W_6feb8 : bv 32 := 0x02060063.
Lemma D_6feb8 : decode_any W_6feb8 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6febc : bv 32 := 0x00c50633.
Lemma D_6febc : decode_any W_6febc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fec0 : bv 32 := 0x00050693.
Lemma D_6fec0 : decode_any W_6fec0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fec4 : bv 32 := 0x0005c703.
Lemma D_6fec4 : decode_any W_6fec4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fec8 : bv 32 := 0x00e68023.
Lemma D_6fec8 : decode_any W_6fec8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fecc : bv 32 := 0x00168693.
Lemma D_6fecc : decode_any W_6fecc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fed0 : bv 32 := 0x00158593.
Lemma D_6fed0 : decode_any W_6fed0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fed4 : bv 32 := 0xfec698e3.
Lemma D_6fed4 : decode_any W_6fed4 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fed8 : bv 32 := 0x00008067.
Lemma D_6fed8 : decode_any W_6fed8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff34 : bv 32 := 0x00a666b3.
Lemma D_6ff34 : decode_any W_6ff34 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff38 : bv 32 := 0x00f6f693.
Lemma D_6ff38 : decode_any W_6ff38 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff3c : bv 32 := 0x02068063.
Lemma D_6ff3c : decode_any W_6ff3c = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff40 : bv 32 := 0x04060863.
Lemma D_6ff40 : decode_any W_6ff40 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff44 : bv 32 := 0x00c50633.
Lemma D_6ff44 : decode_any W_6ff44 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff48 : bv 32 := 0x00050693.
Lemma D_6ff48 : decode_any W_6ff48 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff4c : bv 32 := 0x00b68023.
Lemma D_6ff4c : decode_any W_6ff4c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff50 : bv 32 := 0x00168693.
Lemma D_6ff50 : decode_any W_6ff50 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff54 : bv 32 := 0xfec69ce3.
Lemma D_6ff54 : decode_any W_6ff54 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff58 : bv 32 := 0x0380006f.
Lemma D_6ff58 : decode_any W_6ff58 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff5c : bv 32 := 0x02060a63.
Lemma D_6ff5c : decode_any W_6ff5c = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff60 : bv 32 := 0x00c50633.
Lemma D_6ff60 : decode_any W_6ff60 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff64 : bv 32 := 0x00859693.
Lemma D_6ff64 : decode_any W_6ff64 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff68 : bv 32 := 0x00b6e5b3.
Lemma D_6ff68 : decode_any W_6ff68 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff6c : bv 32 := 0x01059693.
Lemma D_6ff6c : decode_any W_6ff6c = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff70 : bv 32 := 0x00b6e5b3.
Lemma D_6ff70 : decode_any W_6ff70 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff74 : bv 32 := 0x02059693.
Lemma D_6ff74 : decode_any W_6ff74 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff78 : bv 32 := 0x00b6e5b3.
Lemma D_6ff78 : decode_any W_6ff78 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff7c : bv 32 := 0x00050693.
Lemma D_6ff7c : decode_any W_6ff7c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff80 : bv 32 := 0x00b6b023.
Lemma D_6ff80 : decode_any W_6ff80 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff84 : bv 32 := 0x00b6b423.
Lemma D_6ff84 : decode_any W_6ff84 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff88 : bv 32 := 0x01068693.
Lemma D_6ff88 : decode_any W_6ff88 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff8c : bv 32 := 0xfec6eae3.
Lemma D_6ff8c : decode_any W_6ff8c = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ff90 : bv 32 := 0x00008067.
Lemma D_6ff90 : decode_any W_6ff90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70464 : bv 32 := 0xff010113.
Lemma D_70464 : decode_any W_70464 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_70468 : bv 32 := 0x00113423.
Lemma D_70468 : decode_any W_70468 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7046c : bv 32 := 0x00058693.
Lemma D_7046c : decode_any W_7046c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70470 : bv 32 := 0x00100713.
Lemma D_70470 : decode_any W_70470 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70474 : bv 32 := 0x02871713.
Lemma D_70474 : decode_any W_70474 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_70478 : bv 32 := 0x00170593.
Lemma D_70478 : decode_any W_70478 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7047c : bv 32 := 0x08b6f263.
Lemma D_7047c : decode_any W_7047c = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_70480 : bv 32 := 0x00000593.
Lemma D_70480 : decode_any W_70480 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70484 : bv 32 := 0x00d50733.
Lemma D_70484 : decode_any W_70484 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70488 : bv 32 := 0x00750793.
Lemma D_70488 : decode_any W_70488 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7048c : bv 32 := 0xff87f793.
Lemma D_7048c : decode_any W_7048c = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_70490 : bv 32 := 0xff877613.
Lemma D_70490 : decode_any W_70490 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_70494 : bv 32 := 0x02f57463.
Lemma D_70494 : decode_any W_70494 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_70498 : bv 32 := 0x02068263.
Lemma D_70498 : decode_any W_70498 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_7049c : bv 32 := 0x00000593.
Lemma D_7049c : decode_any W_7049c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_704a0 : bv 32 := 0x00150693.
Lemma D_704a0 : decode_any W_704a0 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_704a4 : bv 32 := 0x00068813.
Lemma D_704a4 : decode_any W_704a4 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_704a8 : bv 32 := 0xfff6c683.
Lemma D_704a8 : decode_any W_704a8 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_704ac : bv 32 := 0x00d5e5b3.
Lemma D_704ac : decode_any W_704ac = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_704b0 : bv 32 := 0x00f87663.
Lemma D_704b0 : decode_any W_704b0 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_704b4 : bv 32 := 0x00180693.
Lemma D_704b4 : decode_any W_704b4 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_704b8 : bv 32 := 0xfee866e3.
Lemma D_704b8 : decode_any W_704b8 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_704bc : bv 32 := 0x00c7fa63.
Lemma D_704bc : decode_any W_704bc = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_704c0 : bv 32 := 0x0007b683.
Lemma D_704c0 : decode_any W_704c0 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_704c4 : bv 32 := 0x00878793.
Lemma D_704c4 : decode_any W_704c4 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_704c8 : bv 32 := 0x00b6e5b3.
Lemma D_704c8 : decode_any W_704c8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_704cc : bv 32 := 0xfec7eae3.
Lemma D_704cc : decode_any W_704cc = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_704d0 : bv 32 := 0x02a66063.
Lemma D_704d0 : decode_any W_704d0 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_704d4 : bv 32 := 0x00e67e63.
Lemma D_704d4 : decode_any W_704d4 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_704d8 : bv 32 := 0x40c70733.
Lemma D_704d8 : decode_any W_704d8 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_704dc : bv 32 := 0x00064503.
Lemma D_704dc : decode_any W_704dc = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_704e0 : bv 32 := 0xfff70713.
Lemma D_704e0 : decode_any W_704e0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_704e4 : bv 32 := 0x00a5e5b3.
Lemma D_704e4 : decode_any W_704e4 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_704e8 : bv 32 := 0x00160613.
Lemma D_704e8 : decode_any W_704e8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_704ec : bv 32 := 0xfe0718e3.
Lemma D_704ec : decode_any W_704ec = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_704f0 : bv 32 := 0x0015b513.
Lemma D_704f0 : decode_any W_704f0 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_704f4 : bv 32 := 0x00813083.
Lemma D_704f4 : decode_any W_704f4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_704f8 : bv 32 := 0x01010113.
Lemma D_704f8 : decode_any W_704f8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_704fc : bv 32 := 0x00008067.
Lemma D_704fc : decode_any W_704fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
