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

Definition W_70360 : bv 32 := 0x06060663.
Lemma D_70360 : decode_any W_70360 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_70364 : bv 32 := 0x00000693.
Lemma D_70364 : decode_any W_70364 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70368 : bv 32 := 0x00d58733.
Lemma D_70368 : decode_any W_70368 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7036c : bv 32 := 0x00074703.
Lemma D_7036c : decode_any W_7036c = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70370 : bv 32 := 0x00070c63.
Lemma D_70370 : decode_any W_70370 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_70374 : bv 32 := 0x00d507b3.
Lemma D_70374 : decode_any W_70374 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70378 : bv 32 := 0x00168693.
Lemma D_70378 : decode_any W_70378 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7037c : bv 32 := 0x00e78023.
Lemma D_7037c : decode_any W_7037c = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70380 : bv 32 := 0xfed614e3.
Lemma D_70380 : decode_any W_70380 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_70384 : bv 32 := 0x00060693.
Lemma D_70384 : decode_any W_70384 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70388 : bv 32 := 0x00d505b3.
Lemma D_70388 : decode_any W_70388 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7038c : bv 32 := 0x40d6073b.
Lemma D_7038c : decode_any W_7038c = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70390 : bv 32 := 0x00b76733.
Lemma D_70390 : decode_any W_70390 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70394 : bv 32 := 0x00f77713.
Lemma D_70394 : decode_any W_70394 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_70398 : bv 32 := 0x00070e63.
Lemma D_70398 : decode_any W_70398 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7039c : bv 32 := 0x02d60863.
Lemma D_7039c : decode_any W_7039c = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_703a0 : bv 32 := 0x00c50633.
Lemma D_703a0 : decode_any W_703a0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_703a4 : bv 32 := 0x00058023.
Lemma D_703a4 : decode_any W_703a4 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_703a8 : bv 32 := 0x00158593.
Lemma D_703a8 : decode_any W_703a8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_703ac : bv 32 := 0xfec59ce3.
Lemma D_703ac : decode_any W_703ac = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_703b0 : bv 32 := 0x01c0006f.
Lemma D_703b0 : decode_any W_703b0 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_703b4 : bv 32 := 0x00d60c63.
Lemma D_703b4 : decode_any W_703b4 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_703b8 : bv 32 := 0x00c50633.
Lemma D_703b8 : decode_any W_703b8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_703bc : bv 32 := 0x0005b023.
Lemma D_703bc : decode_any W_703bc = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_703c0 : bv 32 := 0x0005b423.
Lemma D_703c0 : decode_any W_703c0 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_703c4 : bv 32 := 0x01058593.
Lemma D_703c4 : decode_any W_703c4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_703c8 : bv 32 := 0xfec5eae3.
Lemma D_703c8 : decode_any W_703c8 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_703cc : bv 32 := 0x00008067.
Lemma D_703cc : decode_any W_703cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



Definition W_5ceb0 : bv 32 := 0x00200613.
Lemma D_5ceb0 : decode_any W_5ceb0 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ceb4 : bv 32 := 0x14c5ea63.
Lemma D_5ceb4 : decode_any W_5ceb4 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ceb8 : bv 32 := 0x00100613.
Lemma D_5ceb8 : decode_any W_5ceb8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cebc : bv 32 := 0x00100693.
Lemma D_5cebc : decode_any W_5cebc = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cec0 : bv 32 := 0x00c0006f.
Lemma D_5cec0 : decode_any W_5cec0 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cec4 : bv 32 := 0x00160613.
Lemma D_5cec4 : decode_any W_5cec4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cec8 : bv 32 := 0x12b60c63.
Lemma D_5cec8 : decode_any W_5cec8 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cecc : bv 32 := 0x00461713.
Lemma D_5cecc : decode_any W_5cecc = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ced0 : bv 32 := 0x00e50733.
Lemma D_5ced0 : decode_any W_5ced0 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ced4 : bv 32 := 0x00072703.
Lemma D_5ced4 : decode_any W_5ced4 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ced8 : bv 32 := 0x00060893.
Lemma D_5ced8 : decode_any W_5ced8 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cedc : bv 32 := 0xfff88793.
Lemma D_5cedc : decode_any W_5cedc = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cee0 : bv 32 := 0x0017d813.
Lemma D_5cee0 : decode_any W_5cee0 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cee4 : bv 32 := 0x00481293.
Lemma D_5cee4 : decode_any W_5cee4 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cee8 : bv 32 := 0x005502b3.
Lemma D_5cee8 : decode_any W_5cee8 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ceec : bv 32 := 0x0002a303.
Lemma D_5ceec : decode_any W_5ceec = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cef0 : bv 32 := 0xfce37ae3.
Lemma D_5cef0 : decode_any W_5cef0 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cef4 : bv 32 := 0x0002b303.
Lemma D_5cef4 : decode_any W_5cef4 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cef8 : bv 32 := 0x00489893.
Lemma D_5cef8 : decode_any W_5cef8 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cefc : bv 32 := 0x011508b3.
Lemma D_5cefc : decode_any W_5cefc = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf00 : bv 32 := 0x0048a383.
Lemma D_5cf00 : decode_any W_5cf00 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf04 : bv 32 := 0x0068b023.
Lemma D_5cf04 : decode_any W_5cf04 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf08 : bv 32 := 0x0082b303.
Lemma D_5cf08 : decode_any W_5cf08 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf0c : bv 32 := 0x0088be03.
Lemma D_5cf0c : decode_any W_5cf0c = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf10 : bv 32 := 0x0068b423.
Lemma D_5cf10 : decode_any W_5cf10 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf14 : bv 32 := 0x00e2a023.
Lemma D_5cf14 : decode_any W_5cf14 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf18 : bv 32 := 0x0072a223.
Lemma D_5cf18 : decode_any W_5cf18 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf1c : bv 32 := 0x01c2b423.
Lemma D_5cf1c : decode_any W_5cf1c = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf20 : bv 32 := 0x00080893.
Lemma D_5cf20 : decode_any W_5cf20 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf24 : bv 32 := 0xfaf6ece3.
Lemma D_5cf24 : decode_any W_5cf24 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf28 : bv 32 := 0xf9dff06f.
Lemma D_5cf28 : decode_any W_5cf28 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf2c : bv 32 := 0x00000613.
Lemma D_5cf2c : decode_any W_5cf2c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf30 : bv 32 := 0x00459693.
Lemma D_5cf30 : decode_any W_5cf30 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf34 : bv 32 := 0x00d506b3.
Lemma D_5cf34 : decode_any W_5cf34 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf38 : bv 32 := 0x0006b703.
Lemma D_5cf38 : decode_any W_5cf38 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf3c : bv 32 := 0x0086b783.
Lemma D_5cf3c : decode_any W_5cf3c = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf40 : bv 32 := 0x00053803.
Lemma D_5cf40 : decode_any W_5cf40 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf44 : bv 32 := 0x00853883.
Lemma D_5cf44 : decode_any W_5cf44 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf48 : bv 32 := 0x00e53023.
Lemma D_5cf48 : decode_any W_5cf48 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf4c : bv 32 := 0x00f53423.
Lemma D_5cf4c : decode_any W_5cf4c = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf50 : bv 32 := 0x0106b023.
Lemma D_5cf50 : decode_any W_5cf50 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf54 : bv 32 := 0x0116b423.
Lemma D_5cf54 : decode_any W_5cf54 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf58 : bv 32 := 0x00000693.
Lemma D_5cf58 : decode_any W_5cf58 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf5c : bv 32 := 0x00161793.
Lemma D_5cf5c : decode_any W_5cf5c = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf60 : bv 32 := 0x00178813.
Lemma D_5cf60 : decode_any W_5cf60 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf64 : bv 32 := 0x00461713.
Lemma D_5cf64 : decode_any W_5cf64 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf68 : bv 32 := 0x00b86a63.
Lemma D_5cf68 : decode_any W_5cf68 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf6c : bv 32 := 0x00278793.
Lemma D_5cf6c : decode_any W_5cf6c = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf70 : bv 32 := 0x02b7ea63.
Lemma D_5cf70 : decode_any W_5cf70 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf74 : bv 32 := 0x04c69c63.
Lemma D_5cf74 : decode_any W_5cf74 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf78 : bv 32 := 0x0880006f.
Lemma D_5cf78 : decode_any W_5cf78 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf7c : bv 32 := 0x00e506b3.
Lemma D_5cf7c : decode_any W_5cf7c = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf80 : bv 32 := 0x00481893.
Lemma D_5cf80 : decode_any W_5cf80 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf84 : bv 32 := 0x011508b3.
Lemma D_5cf84 : decode_any W_5cf84 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf88 : bv 32 := 0x0006a683.
Lemma D_5cf88 : decode_any W_5cf88 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf8c : bv 32 := 0x0008a883.
Lemma D_5cf8c : decode_any W_5cf8c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf90 : bv 32 := 0x0116e463.
Lemma D_5cf90 : decode_any W_5cf90 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf94 : bv 32 := 0x00060813.
Lemma D_5cf94 : decode_any W_5cf94 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf98 : bv 32 := 0x00080693.
Lemma D_5cf98 : decode_any W_5cf98 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cf9c : bv 32 := 0x00278793.
Lemma D_5cf9c : decode_any W_5cf9c = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfa0 : bv 32 := 0xfcb7fae3.
Lemma D_5cfa0 : decode_any W_5cfa0 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfa4 : bv 32 := 0x00469813.
Lemma D_5cfa4 : decode_any W_5cfa4 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfa8 : bv 32 := 0x00479893.
Lemma D_5cfa8 : decode_any W_5cfa8 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfac : bv 32 := 0x01050833.
Lemma D_5cfac : decode_any W_5cfac = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfb0 : bv 32 := 0x011508b3.
Lemma D_5cfb0 : decode_any W_5cfb0 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfb4 : bv 32 := 0x00082803.
Lemma D_5cfb4 : decode_any W_5cfb4 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfb8 : bv 32 := 0x0008a883.
Lemma D_5cfb8 : decode_any W_5cfb8 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfbc : bv 32 := 0x01186463.
Lemma D_5cfbc : decode_any W_5cfbc = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfc0 : bv 32 := 0x00068793.
Lemma D_5cfc0 : decode_any W_5cfc0 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfc4 : bv 32 := 0x00078693.
Lemma D_5cfc4 : decode_any W_5cfc4 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfc8 : bv 32 := 0x02c78c63.
Lemma D_5cfc8 : decode_any W_5cfc8 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfcc : bv 32 := 0x00469613.
Lemma D_5cfcc : decode_any W_5cfcc = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfd0 : bv 32 := 0x00c50633.
Lemma D_5cfd0 : decode_any W_5cfd0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfd4 : bv 32 := 0x00063783.
Lemma D_5cfd4 : decode_any W_5cfd4 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfd8 : bv 32 := 0x00e50733.
Lemma D_5cfd8 : decode_any W_5cfd8 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfdc : bv 32 := 0x00073803.
Lemma D_5cfdc : decode_any W_5cfdc = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfe0 : bv 32 := 0x00873883.
Lemma D_5cfe0 : decode_any W_5cfe0 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfe4 : bv 32 := 0x00f73023.
Lemma D_5cfe4 : decode_any W_5cfe4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfe8 : bv 32 := 0x00863783.
Lemma D_5cfe8 : decode_any W_5cfe8 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cfec : bv 32 := 0x00f73423.
Lemma D_5cfec : decode_any W_5cfec = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cff0 : bv 32 := 0x01063023.
Lemma D_5cff0 : decode_any W_5cff0 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cff4 : bv 32 := 0x01163423.
Lemma D_5cff4 : decode_any W_5cff4 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cff8 : bv 32 := 0x00068613.
Lemma D_5cff8 : decode_any W_5cff8 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cffc : bv 32 := 0xf6b6e0e3.
Lemma D_5cffc : decode_any W_5cffc = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d000 : bv 32 := 0xfff58593.
Lemma D_5d000 : decode_any W_5d000 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d004 : bv 32 := 0xf20594e3.
Lemma D_5d004 : decode_any W_5d004 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d008 : bv 32 := 0x00008067.
Lemma D_5d008 : decode_any W_5d008 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
