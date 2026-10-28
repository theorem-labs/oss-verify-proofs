(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_cc07c : bv 32 := 0x02060063.
Lemma D_cc07c : decode_any W_cc07c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc080 : bv 32 := 0x00c50633.
Lemma D_cc080 : decode_any W_cc080 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc084 : bv 32 := 0x00050693.
Lemma D_cc084 : decode_any W_cc084 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc088 : bv 32 := 0x0005c703.
Lemma D_cc088 : decode_any W_cc088 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc08c : bv 32 := 0x00e68023.
Lemma D_cc08c : decode_any W_cc08c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc090 : bv 32 := 0x00168693.
Lemma D_cc090 : decode_any W_cc090 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc094 : bv 32 := 0x00158593.
Lemma D_cc094 : decode_any W_cc094 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc098 : bv 32 := 0xfec698e3.
Lemma D_cc098 : decode_any W_cc098 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc09c : bv 32 := 0x00008067.
Lemma D_cc09c : decode_any W_cc09c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc0f8 : bv 32 := 0x00a666b3.
Lemma D_cc0f8 : decode_any W_cc0f8 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc0fc : bv 32 := 0x00f6f693.
Lemma D_cc0fc : decode_any W_cc0fc = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc100 : bv 32 := 0x02068063.
Lemma D_cc100 : decode_any W_cc100 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc104 : bv 32 := 0x04060863.
Lemma D_cc104 : decode_any W_cc104 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc108 : bv 32 := 0x00c50633.
Lemma D_cc108 : decode_any W_cc108 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc10c : bv 32 := 0x00050693.
Lemma D_cc10c : decode_any W_cc10c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc110 : bv 32 := 0x00b68023.
Lemma D_cc110 : decode_any W_cc110 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc114 : bv 32 := 0x00168693.
Lemma D_cc114 : decode_any W_cc114 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc118 : bv 32 := 0xfec69ce3.
Lemma D_cc118 : decode_any W_cc118 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc11c : bv 32 := 0x0380006f.
Lemma D_cc11c : decode_any W_cc11c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc120 : bv 32 := 0x02060a63.
Lemma D_cc120 : decode_any W_cc120 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc124 : bv 32 := 0x00c50633.
Lemma D_cc124 : decode_any W_cc124 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc128 : bv 32 := 0x00859693.
Lemma D_cc128 : decode_any W_cc128 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc12c : bv 32 := 0x00b6e5b3.
Lemma D_cc12c : decode_any W_cc12c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc130 : bv 32 := 0x01059693.
Lemma D_cc130 : decode_any W_cc130 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc134 : bv 32 := 0x00b6e5b3.
Lemma D_cc134 : decode_any W_cc134 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc138 : bv 32 := 0x02059693.
Lemma D_cc138 : decode_any W_cc138 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc13c : bv 32 := 0x00b6e5b3.
Lemma D_cc13c : decode_any W_cc13c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc140 : bv 32 := 0x00050693.
Lemma D_cc140 : decode_any W_cc140 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc144 : bv 32 := 0x00b6b023.
Lemma D_cc144 : decode_any W_cc144 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc148 : bv 32 := 0x00b6b423.
Lemma D_cc148 : decode_any W_cc148 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc14c : bv 32 := 0x01068693.
Lemma D_cc14c : decode_any W_cc14c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc150 : bv 32 := 0xfec6eae3.
Lemma D_cc150 : decode_any W_cc150 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc154 : bv 32 := 0x00008067.
Lemma D_cc154 : decode_any W_cc154 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc644 : bv 32 := 0xff010113.
Lemma D_cc644 : decode_any W_cc644 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc648 : bv 32 := 0x00113423.
Lemma D_cc648 : decode_any W_cc648 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc64c : bv 32 := 0x00058693.
Lemma D_cc64c : decode_any W_cc64c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc650 : bv 32 := 0x00100713.
Lemma D_cc650 : decode_any W_cc650 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc654 : bv 32 := 0x02871713.
Lemma D_cc654 : decode_any W_cc654 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc658 : bv 32 := 0x00170593.
Lemma D_cc658 : decode_any W_cc658 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc65c : bv 32 := 0x08b6f263.
Lemma D_cc65c : decode_any W_cc65c = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc660 : bv 32 := 0x00000593.
Lemma D_cc660 : decode_any W_cc660 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc664 : bv 32 := 0x00d50733.
Lemma D_cc664 : decode_any W_cc664 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc668 : bv 32 := 0x00750793.
Lemma D_cc668 : decode_any W_cc668 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc66c : bv 32 := 0xff87f793.
Lemma D_cc66c : decode_any W_cc66c = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc670 : bv 32 := 0xff877613.
Lemma D_cc670 : decode_any W_cc670 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc674 : bv 32 := 0x02f57463.
Lemma D_cc674 : decode_any W_cc674 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc678 : bv 32 := 0x02068263.
Lemma D_cc678 : decode_any W_cc678 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc67c : bv 32 := 0x00000593.
Lemma D_cc67c : decode_any W_cc67c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc680 : bv 32 := 0x00150693.
Lemma D_cc680 : decode_any W_cc680 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc684 : bv 32 := 0x00068813.
Lemma D_cc684 : decode_any W_cc684 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc688 : bv 32 := 0xfff6c683.
Lemma D_cc688 : decode_any W_cc688 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc68c : bv 32 := 0x00d5e5b3.
Lemma D_cc68c : decode_any W_cc68c = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc690 : bv 32 := 0x00f87663.
Lemma D_cc690 : decode_any W_cc690 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc694 : bv 32 := 0x00180693.
Lemma D_cc694 : decode_any W_cc694 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc698 : bv 32 := 0xfee866e3.
Lemma D_cc698 : decode_any W_cc698 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc69c : bv 32 := 0x00c7fa63.
Lemma D_cc69c : decode_any W_cc69c = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6a0 : bv 32 := 0x0007b683.
Lemma D_cc6a0 : decode_any W_cc6a0 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6a4 : bv 32 := 0x00878793.
Lemma D_cc6a4 : decode_any W_cc6a4 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6a8 : bv 32 := 0x00b6e5b3.
Lemma D_cc6a8 : decode_any W_cc6a8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6ac : bv 32 := 0xfec7eae3.
Lemma D_cc6ac : decode_any W_cc6ac = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6b0 : bv 32 := 0x02a66063.
Lemma D_cc6b0 : decode_any W_cc6b0 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6b4 : bv 32 := 0x00e67e63.
Lemma D_cc6b4 : decode_any W_cc6b4 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6b8 : bv 32 := 0x40c70733.
Lemma D_cc6b8 : decode_any W_cc6b8 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6bc : bv 32 := 0x00064503.
Lemma D_cc6bc : decode_any W_cc6bc = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6c0 : bv 32 := 0xfff70713.
Lemma D_cc6c0 : decode_any W_cc6c0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6c4 : bv 32 := 0x00a5e5b3.
Lemma D_cc6c4 : decode_any W_cc6c4 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6c8 : bv 32 := 0x00160613.
Lemma D_cc6c8 : decode_any W_cc6c8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6cc : bv 32 := 0xfe0718e3.
Lemma D_cc6cc : decode_any W_cc6cc = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6d0 : bv 32 := 0x0015b513.
Lemma D_cc6d0 : decode_any W_cc6d0 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6d4 : bv 32 := 0x00813083.
Lemma D_cc6d4 : decode_any W_cc6d4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6d8 : bv 32 := 0x01010113.
Lemma D_cc6d8 : decode_any W_cc6d8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc6dc : bv 32 := 0x00008067.
Lemma D_cc6dc : decode_any W_cc6dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
