(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
Definition W_735c0 : bv 32 := 0x02060063.
Lemma D_735c0 : decode_any W_735c0 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_735c4 : bv 32 := 0x00c50633.
Lemma D_735c4 : decode_any W_735c4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_735c8 : bv 32 := 0x00050693.
Lemma D_735c8 : decode_any W_735c8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_735cc : bv 32 := 0x0005c703.
Lemma D_735cc : decode_any W_735cc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_735d0 : bv 32 := 0x00e68023.
Lemma D_735d0 : decode_any W_735d0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_735d4 : bv 32 := 0x00168693.
Lemma D_735d4 : decode_any W_735d4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_735d8 : bv 32 := 0x00158593.
Lemma D_735d8 : decode_any W_735d8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_735dc : bv 32 := 0xfec698e3.
Lemma D_735dc : decode_any W_735dc = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_735e0 : bv 32 := 0x00008067.
Lemma D_735e0 : decode_any W_735e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7363c : bv 32 := 0x00a666b3.
Lemma D_7363c : decode_any W_7363c = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73640 : bv 32 := 0x00f6f693.
Lemma D_73640 : decode_any W_73640 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73644 : bv 32 := 0x02068063.
Lemma D_73644 : decode_any W_73644 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73648 : bv 32 := 0x04060863.
Lemma D_73648 : decode_any W_73648 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7364c : bv 32 := 0x00c50633.
Lemma D_7364c : decode_any W_7364c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73650 : bv 32 := 0x00050693.
Lemma D_73650 : decode_any W_73650 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73654 : bv 32 := 0x00b68023.
Lemma D_73654 : decode_any W_73654 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73658 : bv 32 := 0x00168693.
Lemma D_73658 : decode_any W_73658 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7365c : bv 32 := 0xfec69ce3.
Lemma D_7365c : decode_any W_7365c = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73660 : bv 32 := 0x0380006f.
Lemma D_73660 : decode_any W_73660 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73664 : bv 32 := 0x02060a63.
Lemma D_73664 : decode_any W_73664 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73668 : bv 32 := 0x00c50633.
Lemma D_73668 : decode_any W_73668 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7366c : bv 32 := 0x00859693.
Lemma D_7366c : decode_any W_7366c = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73670 : bv 32 := 0x00b6e5b3.
Lemma D_73670 : decode_any W_73670 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73674 : bv 32 := 0x01059693.
Lemma D_73674 : decode_any W_73674 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73678 : bv 32 := 0x00b6e5b3.
Lemma D_73678 : decode_any W_73678 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7367c : bv 32 := 0x02059693.
Lemma D_7367c : decode_any W_7367c = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73680 : bv 32 := 0x00b6e5b3.
Lemma D_73680 : decode_any W_73680 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73684 : bv 32 := 0x00050693.
Lemma D_73684 : decode_any W_73684 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73688 : bv 32 := 0x00b6b023.
Lemma D_73688 : decode_any W_73688 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7368c : bv 32 := 0x00b6b423.
Lemma D_7368c : decode_any W_7368c = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73690 : bv 32 := 0x01068693.
Lemma D_73690 : decode_any W_73690 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73694 : bv 32 := 0xfec6eae3.
Lemma D_73694 : decode_any W_73694 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73698 : bv 32 := 0x00008067.
Lemma D_73698 : decode_any W_73698 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b6c : bv 32 := 0xff010113.
Lemma D_73b6c : decode_any W_73b6c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b70 : bv 32 := 0x00113423.
Lemma D_73b70 : decode_any W_73b70 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b74 : bv 32 := 0x00058693.
Lemma D_73b74 : decode_any W_73b74 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b78 : bv 32 := 0x00100713.
Lemma D_73b78 : decode_any W_73b78 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b7c : bv 32 := 0x02871713.
Lemma D_73b7c : decode_any W_73b7c = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b80 : bv 32 := 0x00170593.
Lemma D_73b80 : decode_any W_73b80 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b84 : bv 32 := 0x08b6f263.
Lemma D_73b84 : decode_any W_73b84 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b88 : bv 32 := 0x00000593.
Lemma D_73b88 : decode_any W_73b88 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b8c : bv 32 := 0x00d50733.
Lemma D_73b8c : decode_any W_73b8c = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b90 : bv 32 := 0x00750793.
Lemma D_73b90 : decode_any W_73b90 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b94 : bv 32 := 0xff87f793.
Lemma D_73b94 : decode_any W_73b94 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b98 : bv 32 := 0xff877613.
Lemma D_73b98 : decode_any W_73b98 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73b9c : bv 32 := 0x02f57463.
Lemma D_73b9c : decode_any W_73b9c = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ba0 : bv 32 := 0x02068263.
Lemma D_73ba0 : decode_any W_73ba0 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ba4 : bv 32 := 0x00000593.
Lemma D_73ba4 : decode_any W_73ba4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ba8 : bv 32 := 0x00150693.
Lemma D_73ba8 : decode_any W_73ba8 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bac : bv 32 := 0x00068813.
Lemma D_73bac : decode_any W_73bac = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bb0 : bv 32 := 0xfff6c683.
Lemma D_73bb0 : decode_any W_73bb0 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bb4 : bv 32 := 0x00d5e5b3.
Lemma D_73bb4 : decode_any W_73bb4 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bb8 : bv 32 := 0x00f87663.
Lemma D_73bb8 : decode_any W_73bb8 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bbc : bv 32 := 0x00180693.
Lemma D_73bbc : decode_any W_73bbc = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bc0 : bv 32 := 0xfee866e3.
Lemma D_73bc0 : decode_any W_73bc0 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bc4 : bv 32 := 0x00c7fa63.
Lemma D_73bc4 : decode_any W_73bc4 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bc8 : bv 32 := 0x0007b683.
Lemma D_73bc8 : decode_any W_73bc8 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bcc : bv 32 := 0x00878793.
Lemma D_73bcc : decode_any W_73bcc = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bd0 : bv 32 := 0x00b6e5b3.
Lemma D_73bd0 : decode_any W_73bd0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bd4 : bv 32 := 0xfec7eae3.
Lemma D_73bd4 : decode_any W_73bd4 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bd8 : bv 32 := 0x02a66063.
Lemma D_73bd8 : decode_any W_73bd8 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bdc : bv 32 := 0x00e67e63.
Lemma D_73bdc : decode_any W_73bdc = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73be0 : bv 32 := 0x40c70733.
Lemma D_73be0 : decode_any W_73be0 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73be4 : bv 32 := 0x00064503.
Lemma D_73be4 : decode_any W_73be4 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73be8 : bv 32 := 0xfff70713.
Lemma D_73be8 : decode_any W_73be8 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bec : bv 32 := 0x00a5e5b3.
Lemma D_73bec : decode_any W_73bec = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bf0 : bv 32 := 0x00160613.
Lemma D_73bf0 : decode_any W_73bf0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bf4 : bv 32 := 0xfe0718e3.
Lemma D_73bf4 : decode_any W_73bf4 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bf8 : bv 32 := 0x0015b513.
Lemma D_73bf8 : decode_any W_73bf8 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73bfc : bv 32 := 0x00813083.
Lemma D_73bfc : decode_any W_73bfc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c00 : bv 32 := 0x01010113.
Lemma D_73c00 : decode_any W_73c00 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c04 : bv 32 := 0x00008067.
Lemma D_73c04 : decode_any W_73c04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
