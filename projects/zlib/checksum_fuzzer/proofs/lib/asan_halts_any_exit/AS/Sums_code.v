(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_63918 : bv 32 := 0x02060063.
Lemma D_63918 : decode_any W_63918 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6391c : bv 32 := 0x00c50633.
Lemma D_6391c : decode_any W_6391c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_63920 : bv 32 := 0x00050693.
Lemma D_63920 : decode_any W_63920 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63924 : bv 32 := 0x0005c703.
Lemma D_63924 : decode_any W_63924 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63928 : bv 32 := 0x00e68023.
Lemma D_63928 : decode_any W_63928 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6392c : bv 32 := 0x00168693.
Lemma D_6392c : decode_any W_6392c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63930 : bv 32 := 0x00158593.
Lemma D_63930 : decode_any W_63930 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63934 : bv 32 := 0xfec698e3.
Lemma D_63934 : decode_any W_63934 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_63938 : bv 32 := 0x00008067.
Lemma D_63938 : decode_any W_63938 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63994 : bv 32 := 0x00a666b3.
Lemma D_63994 : decode_any W_63994 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_63998 : bv 32 := 0x00f6f693.
Lemma D_63998 : decode_any W_63998 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6399c : bv 32 := 0x02068063.
Lemma D_6399c : decode_any W_6399c = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_639a0 : bv 32 := 0x04060863.
Lemma D_639a0 : decode_any W_639a0 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_639a4 : bv 32 := 0x00c50633.
Lemma D_639a4 : decode_any W_639a4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_639a8 : bv 32 := 0x00050693.
Lemma D_639a8 : decode_any W_639a8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_639ac : bv 32 := 0x00b68023.
Lemma D_639ac : decode_any W_639ac = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_639b0 : bv 32 := 0x00168693.
Lemma D_639b0 : decode_any W_639b0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_639b4 : bv 32 := 0xfec69ce3.
Lemma D_639b4 : decode_any W_639b4 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_639b8 : bv 32 := 0x0380006f.
Lemma D_639b8 : decode_any W_639b8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_639bc : bv 32 := 0x02060a63.
Lemma D_639bc : decode_any W_639bc = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_639c0 : bv 32 := 0x00c50633.
Lemma D_639c0 : decode_any W_639c0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_639c4 : bv 32 := 0x00859693.
Lemma D_639c4 : decode_any W_639c4 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_639c8 : bv 32 := 0x00b6e5b3.
Lemma D_639c8 : decode_any W_639c8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_639cc : bv 32 := 0x01059693.
Lemma D_639cc : decode_any W_639cc = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_639d0 : bv 32 := 0x00b6e5b3.
Lemma D_639d0 : decode_any W_639d0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_639d4 : bv 32 := 0x02059693.
Lemma D_639d4 : decode_any W_639d4 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_639d8 : bv 32 := 0x00b6e5b3.
Lemma D_639d8 : decode_any W_639d8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_639dc : bv 32 := 0x00050693.
Lemma D_639dc : decode_any W_639dc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_639e0 : bv 32 := 0x00b6b023.
Lemma D_639e0 : decode_any W_639e0 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_639e4 : bv 32 := 0x00b6b423.
Lemma D_639e4 : decode_any W_639e4 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_639e8 : bv 32 := 0x01068693.
Lemma D_639e8 : decode_any W_639e8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_639ec : bv 32 := 0xfec6eae3.
Lemma D_639ec : decode_any W_639ec = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_639f0 : bv 32 := 0x00008067.
Lemma D_639f0 : decode_any W_639f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ec4 : bv 32 := 0xff010113.
Lemma D_63ec4 : decode_any W_63ec4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ec8 : bv 32 := 0x00113423.
Lemma D_63ec8 : decode_any W_63ec8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ecc : bv 32 := 0x00058693.
Lemma D_63ecc : decode_any W_63ecc = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ed0 : bv 32 := 0x00100713.
Lemma D_63ed0 : decode_any W_63ed0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ed4 : bv 32 := 0x02871713.
Lemma D_63ed4 : decode_any W_63ed4 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ed8 : bv 32 := 0x00170593.
Lemma D_63ed8 : decode_any W_63ed8 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63edc : bv 32 := 0x08b6f263.
Lemma D_63edc : decode_any W_63edc = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ee0 : bv 32 := 0x00000593.
Lemma D_63ee0 : decode_any W_63ee0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ee4 : bv 32 := 0x00d50733.
Lemma D_63ee4 : decode_any W_63ee4 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ee8 : bv 32 := 0x00750793.
Lemma D_63ee8 : decode_any W_63ee8 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_63eec : bv 32 := 0xff87f793.
Lemma D_63eec : decode_any W_63eec = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ef0 : bv 32 := 0xff877613.
Lemma D_63ef0 : decode_any W_63ef0 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ef4 : bv 32 := 0x02f57463.
Lemma D_63ef4 : decode_any W_63ef4 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ef8 : bv 32 := 0x02068263.
Lemma D_63ef8 : decode_any W_63ef8 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_63efc : bv 32 := 0x00000593.
Lemma D_63efc : decode_any W_63efc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f00 : bv 32 := 0x00150693.
Lemma D_63f00 : decode_any W_63f00 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f04 : bv 32 := 0x00068813.
Lemma D_63f04 : decode_any W_63f04 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f08 : bv 32 := 0xfff6c683.
Lemma D_63f08 : decode_any W_63f08 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f0c : bv 32 := 0x00d5e5b3.
Lemma D_63f0c : decode_any W_63f0c = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f10 : bv 32 := 0x00f87663.
Lemma D_63f10 : decode_any W_63f10 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f14 : bv 32 := 0x00180693.
Lemma D_63f14 : decode_any W_63f14 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f18 : bv 32 := 0xfee866e3.
Lemma D_63f18 : decode_any W_63f18 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f1c : bv 32 := 0x00c7fa63.
Lemma D_63f1c : decode_any W_63f1c = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f20 : bv 32 := 0x0007b683.
Lemma D_63f20 : decode_any W_63f20 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f24 : bv 32 := 0x00878793.
Lemma D_63f24 : decode_any W_63f24 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f28 : bv 32 := 0x00b6e5b3.
Lemma D_63f28 : decode_any W_63f28 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f2c : bv 32 := 0xfec7eae3.
Lemma D_63f2c : decode_any W_63f2c = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f30 : bv 32 := 0x02a66063.
Lemma D_63f30 : decode_any W_63f30 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f34 : bv 32 := 0x00e67e63.
Lemma D_63f34 : decode_any W_63f34 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f38 : bv 32 := 0x40c70733.
Lemma D_63f38 : decode_any W_63f38 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f3c : bv 32 := 0x00064503.
Lemma D_63f3c : decode_any W_63f3c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f40 : bv 32 := 0xfff70713.
Lemma D_63f40 : decode_any W_63f40 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f44 : bv 32 := 0x00a5e5b3.
Lemma D_63f44 : decode_any W_63f44 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f48 : bv 32 := 0x00160613.
Lemma D_63f48 : decode_any W_63f48 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f4c : bv 32 := 0xfe0718e3.
Lemma D_63f4c : decode_any W_63f4c = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f50 : bv 32 := 0x0015b513.
Lemma D_63f50 : decode_any W_63f50 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f54 : bv 32 := 0x00813083.
Lemma D_63f54 : decode_any W_63f54 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f58 : bv 32 := 0x01010113.
Lemma D_63f58 : decode_any W_63f58 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f5c : bv 32 := 0x00008067.
Lemma D_63f5c : decode_any W_63f5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
