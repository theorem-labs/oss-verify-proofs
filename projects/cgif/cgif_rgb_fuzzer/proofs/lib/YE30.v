(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_e2430 : bv 32 := 0x02060063.
Lemma D_e2430 : decode_any W_e2430 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2434 : bv 32 := 0x00c50633.
Lemma D_e2434 : decode_any W_e2434 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2438 : bv 32 := 0x00050693.
Lemma D_e2438 : decode_any W_e2438 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e243c : bv 32 := 0x0005c703.
Lemma D_e243c : decode_any W_e243c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2440 : bv 32 := 0x00e68023.
Lemma D_e2440 : decode_any W_e2440 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2444 : bv 32 := 0x00168693.
Lemma D_e2444 : decode_any W_e2444 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2448 : bv 32 := 0x00158593.
Lemma D_e2448 : decode_any W_e2448 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_e244c : bv 32 := 0xfec698e3.
Lemma D_e244c : decode_any W_e244c = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2450 : bv 32 := 0x00008067.
Lemma D_e2450 : decode_any W_e2450 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24ac : bv 32 := 0x00a666b3.
Lemma D_e24ac : decode_any W_e24ac = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24b0 : bv 32 := 0x00f6f693.
Lemma D_e24b0 : decode_any W_e24b0 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24b4 : bv 32 := 0x02068063.
Lemma D_e24b4 : decode_any W_e24b4 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24b8 : bv 32 := 0x04060863.
Lemma D_e24b8 : decode_any W_e24b8 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24bc : bv 32 := 0x00c50633.
Lemma D_e24bc : decode_any W_e24bc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24c0 : bv 32 := 0x00050693.
Lemma D_e24c0 : decode_any W_e24c0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24c4 : bv 32 := 0x00b68023.
Lemma D_e24c4 : decode_any W_e24c4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24c8 : bv 32 := 0x00168693.
Lemma D_e24c8 : decode_any W_e24c8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24cc : bv 32 := 0xfec69ce3.
Lemma D_e24cc : decode_any W_e24cc = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24d0 : bv 32 := 0x0380006f.
Lemma D_e24d0 : decode_any W_e24d0 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24d4 : bv 32 := 0x02060a63.
Lemma D_e24d4 : decode_any W_e24d4 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24d8 : bv 32 := 0x00c50633.
Lemma D_e24d8 : decode_any W_e24d8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24dc : bv 32 := 0x00859693.
Lemma D_e24dc : decode_any W_e24dc = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24e0 : bv 32 := 0x00b6e5b3.
Lemma D_e24e0 : decode_any W_e24e0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24e4 : bv 32 := 0x01059693.
Lemma D_e24e4 : decode_any W_e24e4 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24e8 : bv 32 := 0x00b6e5b3.
Lemma D_e24e8 : decode_any W_e24e8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24ec : bv 32 := 0x02059693.
Lemma D_e24ec : decode_any W_e24ec = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24f0 : bv 32 := 0x00b6e5b3.
Lemma D_e24f0 : decode_any W_e24f0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24f4 : bv 32 := 0x00050693.
Lemma D_e24f4 : decode_any W_e24f4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24f8 : bv 32 := 0x00b6b023.
Lemma D_e24f8 : decode_any W_e24f8 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e24fc : bv 32 := 0x00b6b423.
Lemma D_e24fc : decode_any W_e24fc = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2500 : bv 32 := 0x01068693.
Lemma D_e2500 : decode_any W_e2500 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2504 : bv 32 := 0xfec6eae3.
Lemma D_e2504 : decode_any W_e2504 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2508 : bv 32 := 0x00008067.
Lemma D_e2508 : decode_any W_e2508 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b10 : bv 32 := 0xff010113.
Lemma D_e2b10 : decode_any W_e2b10 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b14 : bv 32 := 0x00113423.
Lemma D_e2b14 : decode_any W_e2b14 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b18 : bv 32 := 0x00058693.
Lemma D_e2b18 : decode_any W_e2b18 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b1c : bv 32 := 0x00100713.
Lemma D_e2b1c : decode_any W_e2b1c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b20 : bv 32 := 0x02871713.
Lemma D_e2b20 : decode_any W_e2b20 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b24 : bv 32 := 0x00170593.
Lemma D_e2b24 : decode_any W_e2b24 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b28 : bv 32 := 0x08b6f263.
Lemma D_e2b28 : decode_any W_e2b28 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b2c : bv 32 := 0x00000593.
Lemma D_e2b2c : decode_any W_e2b2c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b30 : bv 32 := 0x00d50733.
Lemma D_e2b30 : decode_any W_e2b30 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b34 : bv 32 := 0x00750793.
Lemma D_e2b34 : decode_any W_e2b34 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b38 : bv 32 := 0xff87f793.
Lemma D_e2b38 : decode_any W_e2b38 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b3c : bv 32 := 0xff877613.
Lemma D_e2b3c : decode_any W_e2b3c = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b40 : bv 32 := 0x02f57463.
Lemma D_e2b40 : decode_any W_e2b40 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b44 : bv 32 := 0x02068263.
Lemma D_e2b44 : decode_any W_e2b44 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b48 : bv 32 := 0x00000593.
Lemma D_e2b48 : decode_any W_e2b48 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b4c : bv 32 := 0x00150693.
Lemma D_e2b4c : decode_any W_e2b4c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b50 : bv 32 := 0x00068813.
Lemma D_e2b50 : decode_any W_e2b50 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b54 : bv 32 := 0xfff6c683.
Lemma D_e2b54 : decode_any W_e2b54 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b58 : bv 32 := 0x00d5e5b3.
Lemma D_e2b58 : decode_any W_e2b58 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b5c : bv 32 := 0x00f87663.
Lemma D_e2b5c : decode_any W_e2b5c = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b60 : bv 32 := 0x00180693.
Lemma D_e2b60 : decode_any W_e2b60 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b64 : bv 32 := 0xfee866e3.
Lemma D_e2b64 : decode_any W_e2b64 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b68 : bv 32 := 0x00c7fa63.
Lemma D_e2b68 : decode_any W_e2b68 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b6c : bv 32 := 0x0007b683.
Lemma D_e2b6c : decode_any W_e2b6c = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b70 : bv 32 := 0x00878793.
Lemma D_e2b70 : decode_any W_e2b70 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b74 : bv 32 := 0x00b6e5b3.
Lemma D_e2b74 : decode_any W_e2b74 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b78 : bv 32 := 0xfec7eae3.
Lemma D_e2b78 : decode_any W_e2b78 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b7c : bv 32 := 0x02a66063.
Lemma D_e2b7c : decode_any W_e2b7c = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b80 : bv 32 := 0x00e67e63.
Lemma D_e2b80 : decode_any W_e2b80 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b84 : bv 32 := 0x40c70733.
Lemma D_e2b84 : decode_any W_e2b84 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b88 : bv 32 := 0x00064503.
Lemma D_e2b88 : decode_any W_e2b88 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b8c : bv 32 := 0xfff70713.
Lemma D_e2b8c : decode_any W_e2b8c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b90 : bv 32 := 0x00a5e5b3.
Lemma D_e2b90 : decode_any W_e2b90 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b94 : bv 32 := 0x00160613.
Lemma D_e2b94 : decode_any W_e2b94 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b98 : bv 32 := 0xfe0718e3.
Lemma D_e2b98 : decode_any W_e2b98 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2b9c : bv 32 := 0x0015b513.
Lemma D_e2b9c : decode_any W_e2b9c = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2ba0 : bv 32 := 0x00813083.
Lemma D_e2ba0 : decode_any W_e2ba0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2ba4 : bv 32 := 0x01010113.
Lemma D_e2ba4 : decode_any W_e2ba4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2ba8 : bv 32 := 0x00008067.
Lemma D_e2ba8 : decode_any W_e2ba8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
