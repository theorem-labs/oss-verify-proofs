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
Definition W_646b0 : bv 32 := 0x02060063.
Lemma D_646b0 : decode_any W_646b0 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646b4 : bv 32 := 0x00c50633.
Lemma D_646b4 : decode_any W_646b4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646b8 : bv 32 := 0x00050693.
Lemma D_646b8 : decode_any W_646b8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646bc : bv 32 := 0x0005c703.
Lemma D_646bc : decode_any W_646bc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646c0 : bv 32 := 0x00e68023.
Lemma D_646c0 : decode_any W_646c0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646c4 : bv 32 := 0x00168693.
Lemma D_646c4 : decode_any W_646c4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646c8 : bv 32 := 0x00158593.
Lemma D_646c8 : decode_any W_646c8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646cc : bv 32 := 0xfec698e3.
Lemma D_646cc : decode_any W_646cc = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_646d0 : bv 32 := 0x00008067.
Lemma D_646d0 : decode_any W_646d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6472c : bv 32 := 0x00a666b3.
Lemma D_6472c : decode_any W_6472c = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64730 : bv 32 := 0x00f6f693.
Lemma D_64730 : decode_any W_64730 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64734 : bv 32 := 0x02068063.
Lemma D_64734 : decode_any W_64734 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64738 : bv 32 := 0x04060863.
Lemma D_64738 : decode_any W_64738 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6473c : bv 32 := 0x00c50633.
Lemma D_6473c : decode_any W_6473c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64740 : bv 32 := 0x00050693.
Lemma D_64740 : decode_any W_64740 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64744 : bv 32 := 0x00b68023.
Lemma D_64744 : decode_any W_64744 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64748 : bv 32 := 0x00168693.
Lemma D_64748 : decode_any W_64748 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6474c : bv 32 := 0xfec69ce3.
Lemma D_6474c : decode_any W_6474c = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64750 : bv 32 := 0x0380006f.
Lemma D_64750 : decode_any W_64750 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64754 : bv 32 := 0x02060a63.
Lemma D_64754 : decode_any W_64754 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64758 : bv 32 := 0x00c50633.
Lemma D_64758 : decode_any W_64758 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6475c : bv 32 := 0x00859693.
Lemma D_6475c : decode_any W_6475c = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64760 : bv 32 := 0x00b6e5b3.
Lemma D_64760 : decode_any W_64760 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64764 : bv 32 := 0x01059693.
Lemma D_64764 : decode_any W_64764 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64768 : bv 32 := 0x00b6e5b3.
Lemma D_64768 : decode_any W_64768 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6476c : bv 32 := 0x02059693.
Lemma D_6476c : decode_any W_6476c = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64770 : bv 32 := 0x00b6e5b3.
Lemma D_64770 : decode_any W_64770 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64774 : bv 32 := 0x00050693.
Lemma D_64774 : decode_any W_64774 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64778 : bv 32 := 0x00b6b023.
Lemma D_64778 : decode_any W_64778 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6477c : bv 32 := 0x00b6b423.
Lemma D_6477c : decode_any W_6477c = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64780 : bv 32 := 0x01068693.
Lemma D_64780 : decode_any W_64780 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64784 : bv 32 := 0xfec6eae3.
Lemma D_64784 : decode_any W_64784 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64788 : bv 32 := 0x00008067.
Lemma D_64788 : decode_any W_64788 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c5c : bv 32 := 0xff010113.
Lemma D_64c5c : decode_any W_64c5c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c60 : bv 32 := 0x00113423.
Lemma D_64c60 : decode_any W_64c60 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c64 : bv 32 := 0x00058693.
Lemma D_64c64 : decode_any W_64c64 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c68 : bv 32 := 0x00100713.
Lemma D_64c68 : decode_any W_64c68 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c6c : bv 32 := 0x02871713.
Lemma D_64c6c : decode_any W_64c6c = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c70 : bv 32 := 0x00170593.
Lemma D_64c70 : decode_any W_64c70 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c74 : bv 32 := 0x08b6f263.
Lemma D_64c74 : decode_any W_64c74 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c78 : bv 32 := 0x00000593.
Lemma D_64c78 : decode_any W_64c78 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c7c : bv 32 := 0x00d50733.
Lemma D_64c7c : decode_any W_64c7c = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c80 : bv 32 := 0x00750793.
Lemma D_64c80 : decode_any W_64c80 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c84 : bv 32 := 0xff87f793.
Lemma D_64c84 : decode_any W_64c84 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c88 : bv 32 := 0xff877613.
Lemma D_64c88 : decode_any W_64c88 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c8c : bv 32 := 0x02f57463.
Lemma D_64c8c : decode_any W_64c8c = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c90 : bv 32 := 0x02068263.
Lemma D_64c90 : decode_any W_64c90 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c94 : bv 32 := 0x00000593.
Lemma D_64c94 : decode_any W_64c94 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c98 : bv 32 := 0x00150693.
Lemma D_64c98 : decode_any W_64c98 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c9c : bv 32 := 0x00068813.
Lemma D_64c9c : decode_any W_64c9c = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ca0 : bv 32 := 0xfff6c683.
Lemma D_64ca0 : decode_any W_64ca0 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ca4 : bv 32 := 0x00d5e5b3.
Lemma D_64ca4 : decode_any W_64ca4 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ca8 : bv 32 := 0x00f87663.
Lemma D_64ca8 : decode_any W_64ca8 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cac : bv 32 := 0x00180693.
Lemma D_64cac : decode_any W_64cac = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cb0 : bv 32 := 0xfee866e3.
Lemma D_64cb0 : decode_any W_64cb0 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cb4 : bv 32 := 0x00c7fa63.
Lemma D_64cb4 : decode_any W_64cb4 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cb8 : bv 32 := 0x0007b683.
Lemma D_64cb8 : decode_any W_64cb8 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cbc : bv 32 := 0x00878793.
Lemma D_64cbc : decode_any W_64cbc = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cc0 : bv 32 := 0x00b6e5b3.
Lemma D_64cc0 : decode_any W_64cc0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cc4 : bv 32 := 0xfec7eae3.
Lemma D_64cc4 : decode_any W_64cc4 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cc8 : bv 32 := 0x02a66063.
Lemma D_64cc8 : decode_any W_64cc8 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ccc : bv 32 := 0x00e67e63.
Lemma D_64ccc : decode_any W_64ccc = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cd0 : bv 32 := 0x40c70733.
Lemma D_64cd0 : decode_any W_64cd0 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cd4 : bv 32 := 0x00064503.
Lemma D_64cd4 : decode_any W_64cd4 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cd8 : bv 32 := 0xfff70713.
Lemma D_64cd8 : decode_any W_64cd8 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cdc : bv 32 := 0x00a5e5b3.
Lemma D_64cdc : decode_any W_64cdc = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ce0 : bv 32 := 0x00160613.
Lemma D_64ce0 : decode_any W_64ce0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ce4 : bv 32 := 0xfe0718e3.
Lemma D_64ce4 : decode_any W_64ce4 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ce8 : bv 32 := 0x0015b513.
Lemma D_64ce8 : decode_any W_64ce8 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cec : bv 32 := 0x00813083.
Lemma D_64cec : decode_any W_64cec = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cf0 : bv 32 := 0x01010113.
Lemma D_64cf0 : decode_any W_64cf0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cf4 : bv 32 := 0x00008067.
Lemma D_64cf4 : decode_any W_64cf4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
