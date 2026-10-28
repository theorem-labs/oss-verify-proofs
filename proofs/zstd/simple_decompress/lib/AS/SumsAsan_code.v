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
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_66118 : bv 32 := 0x02060063.
Lemma D_66118 : decode_any W_66118 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6611c : bv 32 := 0x00c50633.
Lemma D_6611c : decode_any W_6611c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66120 : bv 32 := 0x00050693.
Lemma D_66120 : decode_any W_66120 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66124 : bv 32 := 0x0005c703.
Lemma D_66124 : decode_any W_66124 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66128 : bv 32 := 0x00e68023.
Lemma D_66128 : decode_any W_66128 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6612c : bv 32 := 0x00168693.
Lemma D_6612c : decode_any W_6612c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66130 : bv 32 := 0x00158593.
Lemma D_66130 : decode_any W_66130 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66134 : bv 32 := 0xfec698e3.
Lemma D_66134 : decode_any W_66134 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66138 : bv 32 := 0x00008067.
Lemma D_66138 : decode_any W_66138 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66194 : bv 32 := 0x00a666b3.
Lemma D_66194 : decode_any W_66194 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66198 : bv 32 := 0x00f6f693.
Lemma D_66198 : decode_any W_66198 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6619c : bv 32 := 0x02068063.
Lemma D_6619c : decode_any W_6619c = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661a0 : bv 32 := 0x04060863.
Lemma D_661a0 : decode_any W_661a0 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661a4 : bv 32 := 0x00c50633.
Lemma D_661a4 : decode_any W_661a4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661a8 : bv 32 := 0x00050693.
Lemma D_661a8 : decode_any W_661a8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661ac : bv 32 := 0x00b68023.
Lemma D_661ac : decode_any W_661ac = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661b0 : bv 32 := 0x00168693.
Lemma D_661b0 : decode_any W_661b0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661b4 : bv 32 := 0xfec69ce3.
Lemma D_661b4 : decode_any W_661b4 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661b8 : bv 32 := 0x0380006f.
Lemma D_661b8 : decode_any W_661b8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661bc : bv 32 := 0x02060a63.
Lemma D_661bc : decode_any W_661bc = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661c0 : bv 32 := 0x00c50633.
Lemma D_661c0 : decode_any W_661c0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661c4 : bv 32 := 0x00859693.
Lemma D_661c4 : decode_any W_661c4 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661c8 : bv 32 := 0x00b6e5b3.
Lemma D_661c8 : decode_any W_661c8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661cc : bv 32 := 0x01059693.
Lemma D_661cc : decode_any W_661cc = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661d0 : bv 32 := 0x00b6e5b3.
Lemma D_661d0 : decode_any W_661d0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661d4 : bv 32 := 0x02059693.
Lemma D_661d4 : decode_any W_661d4 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661d8 : bv 32 := 0x00b6e5b3.
Lemma D_661d8 : decode_any W_661d8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661dc : bv 32 := 0x00050693.
Lemma D_661dc : decode_any W_661dc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661e0 : bv 32 := 0x00b6b023.
Lemma D_661e0 : decode_any W_661e0 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661e4 : bv 32 := 0x00b6b423.
Lemma D_661e4 : decode_any W_661e4 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661e8 : bv 32 := 0x01068693.
Lemma D_661e8 : decode_any W_661e8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661ec : bv 32 := 0xfec6eae3.
Lemma D_661ec : decode_any W_661ec = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661f0 : bv 32 := 0x00008067.
Lemma D_661f0 : decode_any W_661f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666c4 : bv 32 := 0xff010113.
Lemma D_666c4 : decode_any W_666c4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666c8 : bv 32 := 0x00113423.
Lemma D_666c8 : decode_any W_666c8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666cc : bv 32 := 0x00058693.
Lemma D_666cc : decode_any W_666cc = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666d0 : bv 32 := 0x00100713.
Lemma D_666d0 : decode_any W_666d0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666d4 : bv 32 := 0x02871713.
Lemma D_666d4 : decode_any W_666d4 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666d8 : bv 32 := 0x00170593.
Lemma D_666d8 : decode_any W_666d8 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666dc : bv 32 := 0x08b6f263.
Lemma D_666dc : decode_any W_666dc = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666e0 : bv 32 := 0x00000593.
Lemma D_666e0 : decode_any W_666e0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666e4 : bv 32 := 0x00d50733.
Lemma D_666e4 : decode_any W_666e4 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666e8 : bv 32 := 0x00750793.
Lemma D_666e8 : decode_any W_666e8 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666ec : bv 32 := 0xff87f793.
Lemma D_666ec : decode_any W_666ec = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666f0 : bv 32 := 0xff877613.
Lemma D_666f0 : decode_any W_666f0 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666f4 : bv 32 := 0x02f57463.
Lemma D_666f4 : decode_any W_666f4 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666f8 : bv 32 := 0x02068263.
Lemma D_666f8 : decode_any W_666f8 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666fc : bv 32 := 0x00000593.
Lemma D_666fc : decode_any W_666fc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66700 : bv 32 := 0x00150693.
Lemma D_66700 : decode_any W_66700 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66704 : bv 32 := 0x00068813.
Lemma D_66704 : decode_any W_66704 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66708 : bv 32 := 0xfff6c683.
Lemma D_66708 : decode_any W_66708 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6670c : bv 32 := 0x00d5e5b3.
Lemma D_6670c : decode_any W_6670c = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66710 : bv 32 := 0x00f87663.
Lemma D_66710 : decode_any W_66710 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66714 : bv 32 := 0x00180693.
Lemma D_66714 : decode_any W_66714 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66718 : bv 32 := 0xfee866e3.
Lemma D_66718 : decode_any W_66718 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6671c : bv 32 := 0x00c7fa63.
Lemma D_6671c : decode_any W_6671c = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66720 : bv 32 := 0x0007b683.
Lemma D_66720 : decode_any W_66720 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66724 : bv 32 := 0x00878793.
Lemma D_66724 : decode_any W_66724 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66728 : bv 32 := 0x00b6e5b3.
Lemma D_66728 : decode_any W_66728 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6672c : bv 32 := 0xfec7eae3.
Lemma D_6672c : decode_any W_6672c = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66730 : bv 32 := 0x02a66063.
Lemma D_66730 : decode_any W_66730 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66734 : bv 32 := 0x00e67e63.
Lemma D_66734 : decode_any W_66734 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66738 : bv 32 := 0x40c70733.
Lemma D_66738 : decode_any W_66738 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6673c : bv 32 := 0x00064503.
Lemma D_6673c : decode_any W_6673c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66740 : bv 32 := 0xfff70713.
Lemma D_66740 : decode_any W_66740 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66744 : bv 32 := 0x00a5e5b3.
Lemma D_66744 : decode_any W_66744 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66748 : bv 32 := 0x00160613.
Lemma D_66748 : decode_any W_66748 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6674c : bv 32 := 0xfe0718e3.
Lemma D_6674c : decode_any W_6674c = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66750 : bv 32 := 0x0015b513.
Lemma D_66750 : decode_any W_66750 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66754 : bv 32 := 0x00813083.
Lemma D_66754 : decode_any W_66754 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66758 : bv 32 := 0x01010113.
Lemma D_66758 : decode_any W_66758 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6675c : bv 32 := 0x00008067.
Lemma D_6675c : decode_any W_6675c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
