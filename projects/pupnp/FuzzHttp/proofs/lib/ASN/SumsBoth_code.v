(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_69828 : bv 32 := 0x02060063.
Lemma D_69828 : decode_any W_69828 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6982c : bv 32 := 0x00c50633.
Lemma D_6982c : decode_any W_6982c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69830 : bv 32 := 0x00050693.
Lemma D_69830 : decode_any W_69830 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69834 : bv 32 := 0x0005c703.
Lemma D_69834 : decode_any W_69834 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69838 : bv 32 := 0x00e68023.
Lemma D_69838 : decode_any W_69838 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6983c : bv 32 := 0x00168693.
Lemma D_6983c : decode_any W_6983c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69840 : bv 32 := 0x00158593.
Lemma D_69840 : decode_any W_69840 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69844 : bv 32 := 0xfec698e3.
Lemma D_69844 : decode_any W_69844 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_69848 : bv 32 := 0x00008067.
Lemma D_69848 : decode_any W_69848 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_698a4 : bv 32 := 0x00a666b3.
Lemma D_698a4 : decode_any W_698a4 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_698a8 : bv 32 := 0x00f6f693.
Lemma D_698a8 : decode_any W_698a8 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_698ac : bv 32 := 0x02068063.
Lemma D_698ac : decode_any W_698ac = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_698b0 : bv 32 := 0x04060863.
Lemma D_698b0 : decode_any W_698b0 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_698b4 : bv 32 := 0x00c50633.
Lemma D_698b4 : decode_any W_698b4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_698b8 : bv 32 := 0x00050693.
Lemma D_698b8 : decode_any W_698b8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_698bc : bv 32 := 0x00b68023.
Lemma D_698bc : decode_any W_698bc = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_698c0 : bv 32 := 0x00168693.
Lemma D_698c0 : decode_any W_698c0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_698c4 : bv 32 := 0xfec69ce3.
Lemma D_698c4 : decode_any W_698c4 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_698c8 : bv 32 := 0x0380006f.
Lemma D_698c8 : decode_any W_698c8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_698cc : bv 32 := 0x02060a63.
Lemma D_698cc : decode_any W_698cc = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_698d0 : bv 32 := 0x00c50633.
Lemma D_698d0 : decode_any W_698d0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_698d4 : bv 32 := 0x00859693.
Lemma D_698d4 : decode_any W_698d4 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_698d8 : bv 32 := 0x00b6e5b3.
Lemma D_698d8 : decode_any W_698d8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_698dc : bv 32 := 0x01059693.
Lemma D_698dc : decode_any W_698dc = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_698e0 : bv 32 := 0x00b6e5b3.
Lemma D_698e0 : decode_any W_698e0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_698e4 : bv 32 := 0x02059693.
Lemma D_698e4 : decode_any W_698e4 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_698e8 : bv 32 := 0x00b6e5b3.
Lemma D_698e8 : decode_any W_698e8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_698ec : bv 32 := 0x00050693.
Lemma D_698ec : decode_any W_698ec = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_698f0 : bv 32 := 0x00b6b023.
Lemma D_698f0 : decode_any W_698f0 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_698f4 : bv 32 := 0x00b6b423.
Lemma D_698f4 : decode_any W_698f4 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_698f8 : bv 32 := 0x01068693.
Lemma D_698f8 : decode_any W_698f8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_698fc : bv 32 := 0xfec6eae3.
Lemma D_698fc : decode_any W_698fc = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_69900 : bv 32 := 0x00008067.
Lemma D_69900 : decode_any W_69900 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69df0 : bv 32 := 0xff010113.
Lemma D_69df0 : decode_any W_69df0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_69df4 : bv 32 := 0x00113423.
Lemma D_69df4 : decode_any W_69df4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69df8 : bv 32 := 0x00058693.
Lemma D_69df8 : decode_any W_69df8 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69dfc : bv 32 := 0x00100713.
Lemma D_69dfc : decode_any W_69dfc = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e00 : bv 32 := 0x02871713.
Lemma D_69e00 : decode_any W_69e00 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e04 : bv 32 := 0x00170593.
Lemma D_69e04 : decode_any W_69e04 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e08 : bv 32 := 0x08b6f263.
Lemma D_69e08 : decode_any W_69e08 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e0c : bv 32 := 0x00000593.
Lemma D_69e0c : decode_any W_69e0c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e10 : bv 32 := 0x00d50733.
Lemma D_69e10 : decode_any W_69e10 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e14 : bv 32 := 0x00750793.
Lemma D_69e14 : decode_any W_69e14 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e18 : bv 32 := 0xff87f793.
Lemma D_69e18 : decode_any W_69e18 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e1c : bv 32 := 0xff877613.
Lemma D_69e1c : decode_any W_69e1c = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e20 : bv 32 := 0x02f57463.
Lemma D_69e20 : decode_any W_69e20 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e24 : bv 32 := 0x02068263.
Lemma D_69e24 : decode_any W_69e24 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e28 : bv 32 := 0x00000593.
Lemma D_69e28 : decode_any W_69e28 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e2c : bv 32 := 0x00150693.
Lemma D_69e2c : decode_any W_69e2c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e30 : bv 32 := 0x00068813.
Lemma D_69e30 : decode_any W_69e30 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e34 : bv 32 := 0xfff6c683.
Lemma D_69e34 : decode_any W_69e34 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e38 : bv 32 := 0x00d5e5b3.
Lemma D_69e38 : decode_any W_69e38 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e3c : bv 32 := 0x00f87663.
Lemma D_69e3c : decode_any W_69e3c = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e40 : bv 32 := 0x00180693.
Lemma D_69e40 : decode_any W_69e40 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e44 : bv 32 := 0xfee866e3.
Lemma D_69e44 : decode_any W_69e44 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e48 : bv 32 := 0x00c7fa63.
Lemma D_69e48 : decode_any W_69e48 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e4c : bv 32 := 0x0007b683.
Lemma D_69e4c : decode_any W_69e4c = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e50 : bv 32 := 0x00878793.
Lemma D_69e50 : decode_any W_69e50 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e54 : bv 32 := 0x00b6e5b3.
Lemma D_69e54 : decode_any W_69e54 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e58 : bv 32 := 0xfec7eae3.
Lemma D_69e58 : decode_any W_69e58 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e5c : bv 32 := 0x02a66063.
Lemma D_69e5c : decode_any W_69e5c = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e60 : bv 32 := 0x00e67e63.
Lemma D_69e60 : decode_any W_69e60 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e64 : bv 32 := 0x40c70733.
Lemma D_69e64 : decode_any W_69e64 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e68 : bv 32 := 0x00064503.
Lemma D_69e68 : decode_any W_69e68 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e6c : bv 32 := 0xfff70713.
Lemma D_69e6c : decode_any W_69e6c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e70 : bv 32 := 0x00a5e5b3.
Lemma D_69e70 : decode_any W_69e70 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e74 : bv 32 := 0x00160613.
Lemma D_69e74 : decode_any W_69e74 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e78 : bv 32 := 0xfe0718e3.
Lemma D_69e78 : decode_any W_69e78 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e7c : bv 32 := 0x0015b513.
Lemma D_69e7c : decode_any W_69e7c = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e80 : bv 32 := 0x00813083.
Lemma D_69e80 : decode_any W_69e80 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e84 : bv 32 := 0x01010113.
Lemma D_69e84 : decode_any W_69e84 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69e88 : bv 32 := 0x00008067.
Lemma D_69e88 : decode_any W_69e88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
