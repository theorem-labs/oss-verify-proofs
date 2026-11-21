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

Definition W_6fd34 : bv 32 := 0x02060063.
Lemma D_6fd34 : decode_any W_6fd34 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd38 : bv 32 := 0x00c50633.
Lemma D_6fd38 : decode_any W_6fd38 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd3c : bv 32 := 0x00050693.
Lemma D_6fd3c : decode_any W_6fd3c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd40 : bv 32 := 0x0005c703.
Lemma D_6fd40 : decode_any W_6fd40 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd44 : bv 32 := 0x00e68023.
Lemma D_6fd44 : decode_any W_6fd44 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd48 : bv 32 := 0x00168693.
Lemma D_6fd48 : decode_any W_6fd48 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd4c : bv 32 := 0x00158593.
Lemma D_6fd4c : decode_any W_6fd4c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd50 : bv 32 := 0xfec698e3.
Lemma D_6fd50 : decode_any W_6fd50 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fd54 : bv 32 := 0x00008067.
Lemma D_6fd54 : decode_any W_6fd54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdb0 : bv 32 := 0x00a666b3.
Lemma D_6fdb0 : decode_any W_6fdb0 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdb4 : bv 32 := 0x00f6f693.
Lemma D_6fdb4 : decode_any W_6fdb4 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdb8 : bv 32 := 0x02068063.
Lemma D_6fdb8 : decode_any W_6fdb8 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdbc : bv 32 := 0x04060863.
Lemma D_6fdbc : decode_any W_6fdbc = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdc0 : bv 32 := 0x00c50633.
Lemma D_6fdc0 : decode_any W_6fdc0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdc4 : bv 32 := 0x00050693.
Lemma D_6fdc4 : decode_any W_6fdc4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdc8 : bv 32 := 0x00b68023.
Lemma D_6fdc8 : decode_any W_6fdc8 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdcc : bv 32 := 0x00168693.
Lemma D_6fdcc : decode_any W_6fdcc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdd0 : bv 32 := 0xfec69ce3.
Lemma D_6fdd0 : decode_any W_6fdd0 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdd4 : bv 32 := 0x0380006f.
Lemma D_6fdd4 : decode_any W_6fdd4 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdd8 : bv 32 := 0x02060a63.
Lemma D_6fdd8 : decode_any W_6fdd8 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fddc : bv 32 := 0x00c50633.
Lemma D_6fddc : decode_any W_6fddc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fde0 : bv 32 := 0x00859693.
Lemma D_6fde0 : decode_any W_6fde0 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fde4 : bv 32 := 0x00b6e5b3.
Lemma D_6fde4 : decode_any W_6fde4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fde8 : bv 32 := 0x01059693.
Lemma D_6fde8 : decode_any W_6fde8 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdec : bv 32 := 0x00b6e5b3.
Lemma D_6fdec : decode_any W_6fdec = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdf0 : bv 32 := 0x02059693.
Lemma D_6fdf0 : decode_any W_6fdf0 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdf4 : bv 32 := 0x00b6e5b3.
Lemma D_6fdf4 : decode_any W_6fdf4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdf8 : bv 32 := 0x00050693.
Lemma D_6fdf8 : decode_any W_6fdf8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fdfc : bv 32 := 0x00b6b023.
Lemma D_6fdfc : decode_any W_6fdfc = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fe00 : bv 32 := 0x00b6b423.
Lemma D_6fe00 : decode_any W_6fe00 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fe04 : bv 32 := 0x01068693.
Lemma D_6fe04 : decode_any W_6fe04 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fe08 : bv 32 := 0xfec6eae3.
Lemma D_6fe08 : decode_any W_6fe08 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6fe0c : bv 32 := 0x00008067.
Lemma D_6fe0c : decode_any W_6fe0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_702e0 : bv 32 := 0xff010113.
Lemma D_702e0 : decode_any W_702e0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_702e4 : bv 32 := 0x00113423.
Lemma D_702e4 : decode_any W_702e4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_702e8 : bv 32 := 0x00058693.
Lemma D_702e8 : decode_any W_702e8 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_702ec : bv 32 := 0x00100713.
Lemma D_702ec : decode_any W_702ec = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_702f0 : bv 32 := 0x02871713.
Lemma D_702f0 : decode_any W_702f0 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_702f4 : bv 32 := 0x00170593.
Lemma D_702f4 : decode_any W_702f4 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_702f8 : bv 32 := 0x08b6f263.
Lemma D_702f8 : decode_any W_702f8 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_702fc : bv 32 := 0x00000593.
Lemma D_702fc : decode_any W_702fc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70300 : bv 32 := 0x00d50733.
Lemma D_70300 : decode_any W_70300 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70304 : bv 32 := 0x00750793.
Lemma D_70304 : decode_any W_70304 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_70308 : bv 32 := 0xff87f793.
Lemma D_70308 : decode_any W_70308 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7030c : bv 32 := 0xff877613.
Lemma D_7030c : decode_any W_7030c = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_70310 : bv 32 := 0x02f57463.
Lemma D_70310 : decode_any W_70310 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_70314 : bv 32 := 0x02068263.
Lemma D_70314 : decode_any W_70314 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_70318 : bv 32 := 0x00000593.
Lemma D_70318 : decode_any W_70318 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7031c : bv 32 := 0x00150693.
Lemma D_7031c : decode_any W_7031c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70320 : bv 32 := 0x00068813.
Lemma D_70320 : decode_any W_70320 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70324 : bv 32 := 0xfff6c683.
Lemma D_70324 : decode_any W_70324 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_70328 : bv 32 := 0x00d5e5b3.
Lemma D_70328 : decode_any W_70328 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7032c : bv 32 := 0x00f87663.
Lemma D_7032c : decode_any W_7032c = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70330 : bv 32 := 0x00180693.
Lemma D_70330 : decode_any W_70330 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70334 : bv 32 := 0xfee866e3.
Lemma D_70334 : decode_any W_70334 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_70338 : bv 32 := 0x00c7fa63.
Lemma D_70338 : decode_any W_70338 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7033c : bv 32 := 0x0007b683.
Lemma D_7033c : decode_any W_7033c = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70340 : bv 32 := 0x00878793.
Lemma D_70340 : decode_any W_70340 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70344 : bv 32 := 0x00b6e5b3.
Lemma D_70344 : decode_any W_70344 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70348 : bv 32 := 0xfec7eae3.
Lemma D_70348 : decode_any W_70348 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7034c : bv 32 := 0x02a66063.
Lemma D_7034c : decode_any W_7034c = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_70350 : bv 32 := 0x00e67e63.
Lemma D_70350 : decode_any W_70350 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70354 : bv 32 := 0x40c70733.
Lemma D_70354 : decode_any W_70354 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70358 : bv 32 := 0x00064503.
Lemma D_70358 : decode_any W_70358 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7035c : bv 32 := 0xfff70713.
Lemma D_7035c : decode_any W_7035c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_70360 : bv 32 := 0x00a5e5b3.
Lemma D_70360 : decode_any W_70360 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_70364 : bv 32 := 0x00160613.
Lemma D_70364 : decode_any W_70364 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70368 : bv 32 := 0xfe0718e3.
Lemma D_70368 : decode_any W_70368 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7036c : bv 32 := 0x0015b513.
Lemma D_7036c : decode_any W_7036c = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70370 : bv 32 := 0x00813083.
Lemma D_70370 : decode_any W_70370 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70374 : bv 32 := 0x01010113.
Lemma D_70374 : decode_any W_70374 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_70378 : bv 32 := 0x00008067.
Lemma D_70378 : decode_any W_70378 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
