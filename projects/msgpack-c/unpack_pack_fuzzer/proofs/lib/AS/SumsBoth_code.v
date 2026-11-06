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

Definition W_7096c : bv 32 := 0x02060063.
Lemma D_7096c : decode_any W_7096c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_70970 : bv 32 := 0x00c50633.
Lemma D_70970 : decode_any W_70970 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70974 : bv 32 := 0x00050693.
Lemma D_70974 : decode_any W_70974 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70978 : bv 32 := 0x0005c703.
Lemma D_70978 : decode_any W_70978 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7097c : bv 32 := 0x00e68023.
Lemma D_7097c : decode_any W_7097c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70980 : bv 32 := 0x00168693.
Lemma D_70980 : decode_any W_70980 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70984 : bv 32 := 0x00158593.
Lemma D_70984 : decode_any W_70984 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70988 : bv 32 := 0xfec698e3.
Lemma D_70988 : decode_any W_70988 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7098c : bv 32 := 0x00008067.
Lemma D_7098c : decode_any W_7098c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_709e8 : bv 32 := 0x00a666b3.
Lemma D_709e8 : decode_any W_709e8 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_709ec : bv 32 := 0x00f6f693.
Lemma D_709ec : decode_any W_709ec = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_709f0 : bv 32 := 0x02068063.
Lemma D_709f0 : decode_any W_709f0 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_709f4 : bv 32 := 0x04060863.
Lemma D_709f4 : decode_any W_709f4 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_709f8 : bv 32 := 0x00c50633.
Lemma D_709f8 : decode_any W_709f8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_709fc : bv 32 := 0x00050693.
Lemma D_709fc : decode_any W_709fc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a00 : bv 32 := 0x00b68023.
Lemma D_70a00 : decode_any W_70a00 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a04 : bv 32 := 0x00168693.
Lemma D_70a04 : decode_any W_70a04 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a08 : bv 32 := 0xfec69ce3.
Lemma D_70a08 : decode_any W_70a08 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a0c : bv 32 := 0x0380006f.
Lemma D_70a0c : decode_any W_70a0c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a10 : bv 32 := 0x02060a63.
Lemma D_70a10 : decode_any W_70a10 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a14 : bv 32 := 0x00c50633.
Lemma D_70a14 : decode_any W_70a14 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a18 : bv 32 := 0x00859693.
Lemma D_70a18 : decode_any W_70a18 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a1c : bv 32 := 0x00b6e5b3.
Lemma D_70a1c : decode_any W_70a1c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a20 : bv 32 := 0x01059693.
Lemma D_70a20 : decode_any W_70a20 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a24 : bv 32 := 0x00b6e5b3.
Lemma D_70a24 : decode_any W_70a24 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a28 : bv 32 := 0x02059693.
Lemma D_70a28 : decode_any W_70a28 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a2c : bv 32 := 0x00b6e5b3.
Lemma D_70a2c : decode_any W_70a2c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a30 : bv 32 := 0x00050693.
Lemma D_70a30 : decode_any W_70a30 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a34 : bv 32 := 0x00b6b023.
Lemma D_70a34 : decode_any W_70a34 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a38 : bv 32 := 0x00b6b423.
Lemma D_70a38 : decode_any W_70a38 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a3c : bv 32 := 0x01068693.
Lemma D_70a3c : decode_any W_70a3c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a40 : bv 32 := 0xfec6eae3.
Lemma D_70a40 : decode_any W_70a40 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_70a44 : bv 32 := 0x00008067.
Lemma D_70a44 : decode_any W_70a44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f18 : bv 32 := 0xff010113.
Lemma D_70f18 : decode_any W_70f18 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f1c : bv 32 := 0x00113423.
Lemma D_70f1c : decode_any W_70f1c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f20 : bv 32 := 0x00058693.
Lemma D_70f20 : decode_any W_70f20 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f24 : bv 32 := 0x00100713.
Lemma D_70f24 : decode_any W_70f24 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f28 : bv 32 := 0x02871713.
Lemma D_70f28 : decode_any W_70f28 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f2c : bv 32 := 0x00170593.
Lemma D_70f2c : decode_any W_70f2c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f30 : bv 32 := 0x08b6f263.
Lemma D_70f30 : decode_any W_70f30 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f34 : bv 32 := 0x00000593.
Lemma D_70f34 : decode_any W_70f34 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f38 : bv 32 := 0x00d50733.
Lemma D_70f38 : decode_any W_70f38 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f3c : bv 32 := 0x00750793.
Lemma D_70f3c : decode_any W_70f3c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f40 : bv 32 := 0xff87f793.
Lemma D_70f40 : decode_any W_70f40 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f44 : bv 32 := 0xff877613.
Lemma D_70f44 : decode_any W_70f44 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f48 : bv 32 := 0x02f57463.
Lemma D_70f48 : decode_any W_70f48 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f4c : bv 32 := 0x02068263.
Lemma D_70f4c : decode_any W_70f4c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f50 : bv 32 := 0x00000593.
Lemma D_70f50 : decode_any W_70f50 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f54 : bv 32 := 0x00150693.
Lemma D_70f54 : decode_any W_70f54 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f58 : bv 32 := 0x00068813.
Lemma D_70f58 : decode_any W_70f58 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f5c : bv 32 := 0xfff6c683.
Lemma D_70f5c : decode_any W_70f5c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f60 : bv 32 := 0x00d5e5b3.
Lemma D_70f60 : decode_any W_70f60 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f64 : bv 32 := 0x00f87663.
Lemma D_70f64 : decode_any W_70f64 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f68 : bv 32 := 0x00180693.
Lemma D_70f68 : decode_any W_70f68 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f6c : bv 32 := 0xfee866e3.
Lemma D_70f6c : decode_any W_70f6c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f70 : bv 32 := 0x00c7fa63.
Lemma D_70f70 : decode_any W_70f70 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f74 : bv 32 := 0x0007b683.
Lemma D_70f74 : decode_any W_70f74 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f78 : bv 32 := 0x00878793.
Lemma D_70f78 : decode_any W_70f78 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f7c : bv 32 := 0x00b6e5b3.
Lemma D_70f7c : decode_any W_70f7c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f80 : bv 32 := 0xfec7eae3.
Lemma D_70f80 : decode_any W_70f80 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f84 : bv 32 := 0x02a66063.
Lemma D_70f84 : decode_any W_70f84 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f88 : bv 32 := 0x00e67e63.
Lemma D_70f88 : decode_any W_70f88 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f8c : bv 32 := 0x40c70733.
Lemma D_70f8c : decode_any W_70f8c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f90 : bv 32 := 0x00064503.
Lemma D_70f90 : decode_any W_70f90 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f94 : bv 32 := 0xfff70713.
Lemma D_70f94 : decode_any W_70f94 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f98 : bv 32 := 0x00a5e5b3.
Lemma D_70f98 : decode_any W_70f98 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_70f9c : bv 32 := 0x00160613.
Lemma D_70f9c : decode_any W_70f9c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fa0 : bv 32 := 0xfe0718e3.
Lemma D_70fa0 : decode_any W_70fa0 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fa4 : bv 32 := 0x0015b513.
Lemma D_70fa4 : decode_any W_70fa4 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fa8 : bv 32 := 0x00813083.
Lemma D_70fa8 : decode_any W_70fa8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fac : bv 32 := 0x01010113.
Lemma D_70fac : decode_any W_70fac = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_70fb0 : bv 32 := 0x00008067.
Lemma D_70fb0 : decode_any W_70fb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
