(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6497c : bv 32 := 0x02060063.
Lemma D_6497c : decode_any W_6497c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64980 : bv 32 := 0x00c50633.
Lemma D_64980 : decode_any W_64980 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64984 : bv 32 := 0x00050693.
Lemma D_64984 : decode_any W_64984 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64988 : bv 32 := 0x0005c703.
Lemma D_64988 : decode_any W_64988 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6498c : bv 32 := 0x00e68023.
Lemma D_6498c : decode_any W_6498c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64990 : bv 32 := 0x00168693.
Lemma D_64990 : decode_any W_64990 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64994 : bv 32 := 0x00158593.
Lemma D_64994 : decode_any W_64994 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64998 : bv 32 := 0xfec698e3.
Lemma D_64998 : decode_any W_64998 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6499c : bv 32 := 0x00008067.
Lemma D_6499c : decode_any W_6499c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_649f8 : bv 32 := 0x00a666b3.
Lemma D_649f8 : decode_any W_649f8 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_649fc : bv 32 := 0x00f6f693.
Lemma D_649fc : decode_any W_649fc = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a00 : bv 32 := 0x02068063.
Lemma D_64a00 : decode_any W_64a00 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a04 : bv 32 := 0x04060863.
Lemma D_64a04 : decode_any W_64a04 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a08 : bv 32 := 0x00c50633.
Lemma D_64a08 : decode_any W_64a08 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a0c : bv 32 := 0x00050693.
Lemma D_64a0c : decode_any W_64a0c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a10 : bv 32 := 0x00b68023.
Lemma D_64a10 : decode_any W_64a10 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a14 : bv 32 := 0x00168693.
Lemma D_64a14 : decode_any W_64a14 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a18 : bv 32 := 0xfec69ce3.
Lemma D_64a18 : decode_any W_64a18 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a1c : bv 32 := 0x0380006f.
Lemma D_64a1c : decode_any W_64a1c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a20 : bv 32 := 0x02060a63.
Lemma D_64a20 : decode_any W_64a20 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a24 : bv 32 := 0x00c50633.
Lemma D_64a24 : decode_any W_64a24 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a28 : bv 32 := 0x00859693.
Lemma D_64a28 : decode_any W_64a28 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a2c : bv 32 := 0x00b6e5b3.
Lemma D_64a2c : decode_any W_64a2c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a30 : bv 32 := 0x01059693.
Lemma D_64a30 : decode_any W_64a30 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a34 : bv 32 := 0x00b6e5b3.
Lemma D_64a34 : decode_any W_64a34 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a38 : bv 32 := 0x02059693.
Lemma D_64a38 : decode_any W_64a38 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a3c : bv 32 := 0x00b6e5b3.
Lemma D_64a3c : decode_any W_64a3c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a40 : bv 32 := 0x00050693.
Lemma D_64a40 : decode_any W_64a40 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a44 : bv 32 := 0x00b6b023.
Lemma D_64a44 : decode_any W_64a44 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a48 : bv 32 := 0x00b6b423.
Lemma D_64a48 : decode_any W_64a48 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a4c : bv 32 := 0x01068693.
Lemma D_64a4c : decode_any W_64a4c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a50 : bv 32 := 0xfec6eae3.
Lemma D_64a50 : decode_any W_64a50 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a54 : bv 32 := 0x00008067.
Lemma D_64a54 : decode_any W_64a54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f28 : bv 32 := 0xff010113.
Lemma D_64f28 : decode_any W_64f28 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f2c : bv 32 := 0x00113423.
Lemma D_64f2c : decode_any W_64f2c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f30 : bv 32 := 0x00058693.
Lemma D_64f30 : decode_any W_64f30 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f34 : bv 32 := 0x00100713.
Lemma D_64f34 : decode_any W_64f34 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f38 : bv 32 := 0x02871713.
Lemma D_64f38 : decode_any W_64f38 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f3c : bv 32 := 0x00170593.
Lemma D_64f3c : decode_any W_64f3c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f40 : bv 32 := 0x08b6f263.
Lemma D_64f40 : decode_any W_64f40 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f44 : bv 32 := 0x00000593.
Lemma D_64f44 : decode_any W_64f44 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f48 : bv 32 := 0x00d50733.
Lemma D_64f48 : decode_any W_64f48 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f4c : bv 32 := 0x00750793.
Lemma D_64f4c : decode_any W_64f4c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f50 : bv 32 := 0xff87f793.
Lemma D_64f50 : decode_any W_64f50 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f54 : bv 32 := 0xff877613.
Lemma D_64f54 : decode_any W_64f54 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f58 : bv 32 := 0x02f57463.
Lemma D_64f58 : decode_any W_64f58 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f5c : bv 32 := 0x02068263.
Lemma D_64f5c : decode_any W_64f5c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f60 : bv 32 := 0x00000593.
Lemma D_64f60 : decode_any W_64f60 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f64 : bv 32 := 0x00150693.
Lemma D_64f64 : decode_any W_64f64 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f68 : bv 32 := 0x00068813.
Lemma D_64f68 : decode_any W_64f68 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f6c : bv 32 := 0xfff6c683.
Lemma D_64f6c : decode_any W_64f6c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f70 : bv 32 := 0x00d5e5b3.
Lemma D_64f70 : decode_any W_64f70 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f74 : bv 32 := 0x00f87663.
Lemma D_64f74 : decode_any W_64f74 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f78 : bv 32 := 0x00180693.
Lemma D_64f78 : decode_any W_64f78 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f7c : bv 32 := 0xfee866e3.
Lemma D_64f7c : decode_any W_64f7c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f80 : bv 32 := 0x00c7fa63.
Lemma D_64f80 : decode_any W_64f80 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f84 : bv 32 := 0x0007b683.
Lemma D_64f84 : decode_any W_64f84 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f88 : bv 32 := 0x00878793.
Lemma D_64f88 : decode_any W_64f88 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f8c : bv 32 := 0x00b6e5b3.
Lemma D_64f8c : decode_any W_64f8c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f90 : bv 32 := 0xfec7eae3.
Lemma D_64f90 : decode_any W_64f90 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f94 : bv 32 := 0x02a66063.
Lemma D_64f94 : decode_any W_64f94 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f98 : bv 32 := 0x00e67e63.
Lemma D_64f98 : decode_any W_64f98 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f9c : bv 32 := 0x40c70733.
Lemma D_64f9c : decode_any W_64f9c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fa0 : bv 32 := 0x00064503.
Lemma D_64fa0 : decode_any W_64fa0 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fa4 : bv 32 := 0xfff70713.
Lemma D_64fa4 : decode_any W_64fa4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fa8 : bv 32 := 0x00a5e5b3.
Lemma D_64fa8 : decode_any W_64fa8 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fac : bv 32 := 0x00160613.
Lemma D_64fac : decode_any W_64fac = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fb0 : bv 32 := 0xfe0718e3.
Lemma D_64fb0 : decode_any W_64fb0 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fb4 : bv 32 := 0x0015b513.
Lemma D_64fb4 : decode_any W_64fb4 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fb8 : bv 32 := 0x00813083.
Lemma D_64fb8 : decode_any W_64fb8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fbc : bv 32 := 0x01010113.
Lemma D_64fbc : decode_any W_64fbc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fc0 : bv 32 := 0x00008067.
Lemma D_64fc0 : decode_any W_64fc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
