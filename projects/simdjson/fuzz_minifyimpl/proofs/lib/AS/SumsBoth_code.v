(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition W_945a0 : bv 32 := 0x02060063.
Lemma D_945a0 : decode_any W_945a0 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_945a4 : bv 32 := 0x00c50633.
Lemma D_945a4 : decode_any W_945a4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_945a8 : bv 32 := 0x00050693.
Lemma D_945a8 : decode_any W_945a8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_945ac : bv 32 := 0x0005c703.
Lemma D_945ac : decode_any W_945ac = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_945b0 : bv 32 := 0x00e68023.
Lemma D_945b0 : decode_any W_945b0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_945b4 : bv 32 := 0x00168693.
Lemma D_945b4 : decode_any W_945b4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_945b8 : bv 32 := 0x00158593.
Lemma D_945b8 : decode_any W_945b8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_945bc : bv 32 := 0xfec698e3.
Lemma D_945bc : decode_any W_945bc = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_945c0 : bv 32 := 0x00008067.
Lemma D_945c0 : decode_any W_945c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9461c : bv 32 := 0x00a666b3.
Lemma D_9461c : decode_any W_9461c = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94620 : bv 32 := 0x00f6f693.
Lemma D_94620 : decode_any W_94620 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94624 : bv 32 := 0x02068063.
Lemma D_94624 : decode_any W_94624 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94628 : bv 32 := 0x04060863.
Lemma D_94628 : decode_any W_94628 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9462c : bv 32 := 0x00c50633.
Lemma D_9462c : decode_any W_9462c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94630 : bv 32 := 0x00050693.
Lemma D_94630 : decode_any W_94630 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94634 : bv 32 := 0x00b68023.
Lemma D_94634 : decode_any W_94634 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94638 : bv 32 := 0x00168693.
Lemma D_94638 : decode_any W_94638 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9463c : bv 32 := 0xfec69ce3.
Lemma D_9463c : decode_any W_9463c = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94640 : bv 32 := 0x0380006f.
Lemma D_94640 : decode_any W_94640 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94644 : bv 32 := 0x02060a63.
Lemma D_94644 : decode_any W_94644 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94648 : bv 32 := 0x00c50633.
Lemma D_94648 : decode_any W_94648 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9464c : bv 32 := 0x00859693.
Lemma D_9464c : decode_any W_9464c = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94650 : bv 32 := 0x00b6e5b3.
Lemma D_94650 : decode_any W_94650 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94654 : bv 32 := 0x01059693.
Lemma D_94654 : decode_any W_94654 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94658 : bv 32 := 0x00b6e5b3.
Lemma D_94658 : decode_any W_94658 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9465c : bv 32 := 0x02059693.
Lemma D_9465c : decode_any W_9465c = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94660 : bv 32 := 0x00b6e5b3.
Lemma D_94660 : decode_any W_94660 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94664 : bv 32 := 0x00050693.
Lemma D_94664 : decode_any W_94664 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94668 : bv 32 := 0x00b6b023.
Lemma D_94668 : decode_any W_94668 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9466c : bv 32 := 0x00b6b423.
Lemma D_9466c : decode_any W_9466c = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94670 : bv 32 := 0x01068693.
Lemma D_94670 : decode_any W_94670 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94674 : bv 32 := 0xfec6eae3.
Lemma D_94674 : decode_any W_94674 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94678 : bv 32 := 0x00008067.
Lemma D_94678 : decode_any W_94678 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b68 : bv 32 := 0xff010113.
Lemma D_94b68 : decode_any W_94b68 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b6c : bv 32 := 0x00113423.
Lemma D_94b6c : decode_any W_94b6c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b70 : bv 32 := 0x00058693.
Lemma D_94b70 : decode_any W_94b70 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b74 : bv 32 := 0x00100713.
Lemma D_94b74 : decode_any W_94b74 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b78 : bv 32 := 0x02871713.
Lemma D_94b78 : decode_any W_94b78 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b7c : bv 32 := 0x00170593.
Lemma D_94b7c : decode_any W_94b7c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b80 : bv 32 := 0x08b6f263.
Lemma D_94b80 : decode_any W_94b80 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b84 : bv 32 := 0x00000593.
Lemma D_94b84 : decode_any W_94b84 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b88 : bv 32 := 0x00d50733.
Lemma D_94b88 : decode_any W_94b88 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b8c : bv 32 := 0x00750793.
Lemma D_94b8c : decode_any W_94b8c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b90 : bv 32 := 0xff87f793.
Lemma D_94b90 : decode_any W_94b90 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b94 : bv 32 := 0xff877613.
Lemma D_94b94 : decode_any W_94b94 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b98 : bv 32 := 0x02f57463.
Lemma D_94b98 : decode_any W_94b98 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b9c : bv 32 := 0x02068263.
Lemma D_94b9c : decode_any W_94b9c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ba0 : bv 32 := 0x00000593.
Lemma D_94ba0 : decode_any W_94ba0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ba4 : bv 32 := 0x00150693.
Lemma D_94ba4 : decode_any W_94ba4 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ba8 : bv 32 := 0x00068813.
Lemma D_94ba8 : decode_any W_94ba8 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bac : bv 32 := 0xfff6c683.
Lemma D_94bac : decode_any W_94bac = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bb0 : bv 32 := 0x00d5e5b3.
Lemma D_94bb0 : decode_any W_94bb0 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bb4 : bv 32 := 0x00f87663.
Lemma D_94bb4 : decode_any W_94bb4 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bb8 : bv 32 := 0x00180693.
Lemma D_94bb8 : decode_any W_94bb8 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bbc : bv 32 := 0xfee866e3.
Lemma D_94bbc : decode_any W_94bbc = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bc0 : bv 32 := 0x00c7fa63.
Lemma D_94bc0 : decode_any W_94bc0 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bc4 : bv 32 := 0x0007b683.
Lemma D_94bc4 : decode_any W_94bc4 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bc8 : bv 32 := 0x00878793.
Lemma D_94bc8 : decode_any W_94bc8 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bcc : bv 32 := 0x00b6e5b3.
Lemma D_94bcc : decode_any W_94bcc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bd0 : bv 32 := 0xfec7eae3.
Lemma D_94bd0 : decode_any W_94bd0 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bd4 : bv 32 := 0x02a66063.
Lemma D_94bd4 : decode_any W_94bd4 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bd8 : bv 32 := 0x00e67e63.
Lemma D_94bd8 : decode_any W_94bd8 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bdc : bv 32 := 0x40c70733.
Lemma D_94bdc : decode_any W_94bdc = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94be0 : bv 32 := 0x00064503.
Lemma D_94be0 : decode_any W_94be0 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94be4 : bv 32 := 0xfff70713.
Lemma D_94be4 : decode_any W_94be4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94be8 : bv 32 := 0x00a5e5b3.
Lemma D_94be8 : decode_any W_94be8 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bec : bv 32 := 0x00160613.
Lemma D_94bec : decode_any W_94bec = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bf0 : bv 32 := 0xfe0718e3.
Lemma D_94bf0 : decode_any W_94bf0 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bf4 : bv 32 := 0x0015b513.
Lemma D_94bf4 : decode_any W_94bf4 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bf8 : bv 32 := 0x00813083.
Lemma D_94bf8 : decode_any W_94bf8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94bfc : bv 32 := 0x01010113.
Lemma D_94bfc : decode_any W_94bfc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94c00 : bv 32 := 0x00008067.
Lemma D_94c00 : decode_any W_94c00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
