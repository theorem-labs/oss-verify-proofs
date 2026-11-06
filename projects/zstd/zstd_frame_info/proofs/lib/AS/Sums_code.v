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
Definition W_6303c : bv 32 := 0x02060063.
Lemma D_6303c : decode_any W_6303c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63040 : bv 32 := 0x00c50633.
Lemma D_63040 : decode_any W_63040 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63044 : bv 32 := 0x00050693.
Lemma D_63044 : decode_any W_63044 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63048 : bv 32 := 0x0005c703.
Lemma D_63048 : decode_any W_63048 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6304c : bv 32 := 0x00e68023.
Lemma D_6304c : decode_any W_6304c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63050 : bv 32 := 0x00168693.
Lemma D_63050 : decode_any W_63050 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63054 : bv 32 := 0x00158593.
Lemma D_63054 : decode_any W_63054 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63058 : bv 32 := 0xfec698e3.
Lemma D_63058 : decode_any W_63058 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6305c : bv 32 := 0x00008067.
Lemma D_6305c : decode_any W_6305c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630b8 : bv 32 := 0x00a666b3.
Lemma D_630b8 : decode_any W_630b8 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630bc : bv 32 := 0x00f6f693.
Lemma D_630bc : decode_any W_630bc = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630c0 : bv 32 := 0x02068063.
Lemma D_630c0 : decode_any W_630c0 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630c4 : bv 32 := 0x04060863.
Lemma D_630c4 : decode_any W_630c4 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630c8 : bv 32 := 0x00c50633.
Lemma D_630c8 : decode_any W_630c8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630cc : bv 32 := 0x00050693.
Lemma D_630cc : decode_any W_630cc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630d0 : bv 32 := 0x00b68023.
Lemma D_630d0 : decode_any W_630d0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630d4 : bv 32 := 0x00168693.
Lemma D_630d4 : decode_any W_630d4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630d8 : bv 32 := 0xfec69ce3.
Lemma D_630d8 : decode_any W_630d8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630dc : bv 32 := 0x0380006f.
Lemma D_630dc : decode_any W_630dc = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630e0 : bv 32 := 0x02060a63.
Lemma D_630e0 : decode_any W_630e0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630e4 : bv 32 := 0x00c50633.
Lemma D_630e4 : decode_any W_630e4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630e8 : bv 32 := 0x00859693.
Lemma D_630e8 : decode_any W_630e8 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630ec : bv 32 := 0x00b6e5b3.
Lemma D_630ec : decode_any W_630ec = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630f0 : bv 32 := 0x01059693.
Lemma D_630f0 : decode_any W_630f0 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630f4 : bv 32 := 0x00b6e5b3.
Lemma D_630f4 : decode_any W_630f4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630f8 : bv 32 := 0x02059693.
Lemma D_630f8 : decode_any W_630f8 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_630fc : bv 32 := 0x00b6e5b3.
Lemma D_630fc : decode_any W_630fc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63100 : bv 32 := 0x00050693.
Lemma D_63100 : decode_any W_63100 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63104 : bv 32 := 0x00b6b023.
Lemma D_63104 : decode_any W_63104 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63108 : bv 32 := 0x00b6b423.
Lemma D_63108 : decode_any W_63108 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6310c : bv 32 := 0x01068693.
Lemma D_6310c : decode_any W_6310c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63110 : bv 32 := 0xfec6eae3.
Lemma D_63110 : decode_any W_63110 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63114 : bv 32 := 0x00008067.
Lemma D_63114 : decode_any W_63114 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635e8 : bv 32 := 0xff010113.
Lemma D_635e8 : decode_any W_635e8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635ec : bv 32 := 0x00113423.
Lemma D_635ec : decode_any W_635ec = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635f0 : bv 32 := 0x00058693.
Lemma D_635f0 : decode_any W_635f0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635f4 : bv 32 := 0x00100713.
Lemma D_635f4 : decode_any W_635f4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635f8 : bv 32 := 0x02871713.
Lemma D_635f8 : decode_any W_635f8 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_635fc : bv 32 := 0x00170593.
Lemma D_635fc : decode_any W_635fc = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63600 : bv 32 := 0x08b6f263.
Lemma D_63600 : decode_any W_63600 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63604 : bv 32 := 0x00000593.
Lemma D_63604 : decode_any W_63604 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63608 : bv 32 := 0x00d50733.
Lemma D_63608 : decode_any W_63608 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6360c : bv 32 := 0x00750793.
Lemma D_6360c : decode_any W_6360c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63610 : bv 32 := 0xff87f793.
Lemma D_63610 : decode_any W_63610 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63614 : bv 32 := 0xff877613.
Lemma D_63614 : decode_any W_63614 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63618 : bv 32 := 0x02f57463.
Lemma D_63618 : decode_any W_63618 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6361c : bv 32 := 0x02068263.
Lemma D_6361c : decode_any W_6361c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63620 : bv 32 := 0x00000593.
Lemma D_63620 : decode_any W_63620 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63624 : bv 32 := 0x00150693.
Lemma D_63624 : decode_any W_63624 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63628 : bv 32 := 0x00068813.
Lemma D_63628 : decode_any W_63628 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6362c : bv 32 := 0xfff6c683.
Lemma D_6362c : decode_any W_6362c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63630 : bv 32 := 0x00d5e5b3.
Lemma D_63630 : decode_any W_63630 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63634 : bv 32 := 0x00f87663.
Lemma D_63634 : decode_any W_63634 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63638 : bv 32 := 0x00180693.
Lemma D_63638 : decode_any W_63638 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6363c : bv 32 := 0xfee866e3.
Lemma D_6363c : decode_any W_6363c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63640 : bv 32 := 0x00c7fa63.
Lemma D_63640 : decode_any W_63640 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63644 : bv 32 := 0x0007b683.
Lemma D_63644 : decode_any W_63644 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63648 : bv 32 := 0x00878793.
Lemma D_63648 : decode_any W_63648 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6364c : bv 32 := 0x00b6e5b3.
Lemma D_6364c : decode_any W_6364c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63650 : bv 32 := 0xfec7eae3.
Lemma D_63650 : decode_any W_63650 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63654 : bv 32 := 0x02a66063.
Lemma D_63654 : decode_any W_63654 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63658 : bv 32 := 0x00e67e63.
Lemma D_63658 : decode_any W_63658 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6365c : bv 32 := 0x40c70733.
Lemma D_6365c : decode_any W_6365c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63660 : bv 32 := 0x00064503.
Lemma D_63660 : decode_any W_63660 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63664 : bv 32 := 0xfff70713.
Lemma D_63664 : decode_any W_63664 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63668 : bv 32 := 0x00a5e5b3.
Lemma D_63668 : decode_any W_63668 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6366c : bv 32 := 0x00160613.
Lemma D_6366c : decode_any W_6366c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63670 : bv 32 := 0xfe0718e3.
Lemma D_63670 : decode_any W_63670 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63674 : bv 32 := 0x0015b513.
Lemma D_63674 : decode_any W_63674 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63678 : bv 32 := 0x00813083.
Lemma D_63678 : decode_any W_63678 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6367c : bv 32 := 0x01010113.
Lemma D_6367c : decode_any W_6367c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63680 : bv 32 := 0x00008067.
Lemma D_63680 : decode_any W_63680 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
