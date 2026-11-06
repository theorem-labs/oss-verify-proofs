(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6ffb4 : bv 32 := 0x02060063.
Lemma D_6ffb4 : decode_any W_6ffb4 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffb8 : bv 32 := 0x00c50633.
Lemma D_6ffb8 : decode_any W_6ffb8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffbc : bv 32 := 0x00050693.
Lemma D_6ffbc : decode_any W_6ffbc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffc0 : bv 32 := 0x0005c703.
Lemma D_6ffc0 : decode_any W_6ffc0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffc4 : bv 32 := 0x00e68023.
Lemma D_6ffc4 : decode_any W_6ffc4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffc8 : bv 32 := 0x00168693.
Lemma D_6ffc8 : decode_any W_6ffc8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffcc : bv 32 := 0x00158593.
Lemma D_6ffcc : decode_any W_6ffcc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffd0 : bv 32 := 0xfec698e3.
Lemma D_6ffd0 : decode_any W_6ffd0 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ffd4 : bv 32 := 0x00008067.
Lemma D_6ffd4 : decode_any W_6ffd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70030 : bv 32 := 0x00a666b3.
Lemma D_70030 : decode_any W_70030 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_70034 : bv 32 := 0x00f6f693.
Lemma D_70034 : decode_any W_70034 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_70038 : bv 32 := 0x02068063.
Lemma D_70038 : decode_any W_70038 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7003c : bv 32 := 0x04060863.
Lemma D_7003c : decode_any W_7003c = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_70040 : bv 32 := 0x00c50633.
Lemma D_70040 : decode_any W_70040 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70044 : bv 32 := 0x00050693.
Lemma D_70044 : decode_any W_70044 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70048 : bv 32 := 0x00b68023.
Lemma D_70048 : decode_any W_70048 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7004c : bv 32 := 0x00168693.
Lemma D_7004c : decode_any W_7004c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70050 : bv 32 := 0xfec69ce3.
Lemma D_70050 : decode_any W_70050 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_70054 : bv 32 := 0x0380006f.
Lemma D_70054 : decode_any W_70054 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_70058 : bv 32 := 0x02060a63.
Lemma D_70058 : decode_any W_70058 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7005c : bv 32 := 0x00c50633.
Lemma D_7005c : decode_any W_7005c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70060 : bv 32 := 0x00859693.
Lemma D_70060 : decode_any W_70060 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70064 : bv 32 := 0x00b6e5b3.
Lemma D_70064 : decode_any W_70064 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70068 : bv 32 := 0x01059693.
Lemma D_70068 : decode_any W_70068 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7006c : bv 32 := 0x00b6e5b3.
Lemma D_7006c : decode_any W_7006c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70070 : bv 32 := 0x02059693.
Lemma D_70070 : decode_any W_70070 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_70074 : bv 32 := 0x00b6e5b3.
Lemma D_70074 : decode_any W_70074 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70078 : bv 32 := 0x00050693.
Lemma D_70078 : decode_any W_70078 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7007c : bv 32 := 0x00b6b023.
Lemma D_7007c : decode_any W_7007c = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70080 : bv 32 := 0x00b6b423.
Lemma D_70080 : decode_any W_70080 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70084 : bv 32 := 0x01068693.
Lemma D_70084 : decode_any W_70084 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_70088 : bv 32 := 0xfec6eae3.
Lemma D_70088 : decode_any W_70088 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7008c : bv 32 := 0x00008067.
Lemma D_7008c : decode_any W_7008c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70560 : bv 32 := 0xff010113.
Lemma D_70560 : decode_any W_70560 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_70564 : bv 32 := 0x00113423.
Lemma D_70564 : decode_any W_70564 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70568 : bv 32 := 0x00058693.
Lemma D_70568 : decode_any W_70568 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7056c : bv 32 := 0x00100713.
Lemma D_7056c : decode_any W_7056c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70570 : bv 32 := 0x02871713.
Lemma D_70570 : decode_any W_70570 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_70574 : bv 32 := 0x00170593.
Lemma D_70574 : decode_any W_70574 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70578 : bv 32 := 0x08b6f263.
Lemma D_70578 : decode_any W_70578 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_7057c : bv 32 := 0x00000593.
Lemma D_7057c : decode_any W_7057c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70580 : bv 32 := 0x00d50733.
Lemma D_70580 : decode_any W_70580 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70584 : bv 32 := 0x00750793.
Lemma D_70584 : decode_any W_70584 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_70588 : bv 32 := 0xff87f793.
Lemma D_70588 : decode_any W_70588 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7058c : bv 32 := 0xff877613.
Lemma D_7058c : decode_any W_7058c = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_70590 : bv 32 := 0x02f57463.
Lemma D_70590 : decode_any W_70590 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_70594 : bv 32 := 0x02068263.
Lemma D_70594 : decode_any W_70594 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_70598 : bv 32 := 0x00000593.
Lemma D_70598 : decode_any W_70598 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7059c : bv 32 := 0x00150693.
Lemma D_7059c : decode_any W_7059c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_705a0 : bv 32 := 0x00068813.
Lemma D_705a0 : decode_any W_705a0 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_705a4 : bv 32 := 0xfff6c683.
Lemma D_705a4 : decode_any W_705a4 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_705a8 : bv 32 := 0x00d5e5b3.
Lemma D_705a8 : decode_any W_705a8 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_705ac : bv 32 := 0x00f87663.
Lemma D_705ac : decode_any W_705ac = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_705b0 : bv 32 := 0x00180693.
Lemma D_705b0 : decode_any W_705b0 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_705b4 : bv 32 := 0xfee866e3.
Lemma D_705b4 : decode_any W_705b4 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_705b8 : bv 32 := 0x00c7fa63.
Lemma D_705b8 : decode_any W_705b8 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_705bc : bv 32 := 0x0007b683.
Lemma D_705bc : decode_any W_705bc = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_705c0 : bv 32 := 0x00878793.
Lemma D_705c0 : decode_any W_705c0 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_705c4 : bv 32 := 0x00b6e5b3.
Lemma D_705c4 : decode_any W_705c4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_705c8 : bv 32 := 0xfec7eae3.
Lemma D_705c8 : decode_any W_705c8 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_705cc : bv 32 := 0x02a66063.
Lemma D_705cc : decode_any W_705cc = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_705d0 : bv 32 := 0x00e67e63.
Lemma D_705d0 : decode_any W_705d0 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_705d4 : bv 32 := 0x40c70733.
Lemma D_705d4 : decode_any W_705d4 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_705d8 : bv 32 := 0x00064503.
Lemma D_705d8 : decode_any W_705d8 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_705dc : bv 32 := 0xfff70713.
Lemma D_705dc : decode_any W_705dc = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_705e0 : bv 32 := 0x00a5e5b3.
Lemma D_705e0 : decode_any W_705e0 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_705e4 : bv 32 := 0x00160613.
Lemma D_705e4 : decode_any W_705e4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_705e8 : bv 32 := 0xfe0718e3.
Lemma D_705e8 : decode_any W_705e8 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_705ec : bv 32 := 0x0015b513.
Lemma D_705ec : decode_any W_705ec = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_705f0 : bv 32 := 0x00813083.
Lemma D_705f0 : decode_any W_705f0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_705f4 : bv 32 := 0x01010113.
Lemma D_705f4 : decode_any W_705f4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_705f8 : bv 32 := 0x00008067.
Lemma D_705f8 : decode_any W_705f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
