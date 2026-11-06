(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_85028 : bv 32 := 0x02060063.
Lemma D_85028 : decode_any W_85028 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8502c : bv 32 := 0x00c50633.
Lemma D_8502c : decode_any W_8502c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85030 : bv 32 := 0x00050693.
Lemma D_85030 : decode_any W_85030 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85034 : bv 32 := 0x0005c703.
Lemma D_85034 : decode_any W_85034 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85038 : bv 32 := 0x00e68023.
Lemma D_85038 : decode_any W_85038 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8503c : bv 32 := 0x00168693.
Lemma D_8503c : decode_any W_8503c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85040 : bv 32 := 0x00158593.
Lemma D_85040 : decode_any W_85040 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85044 : bv 32 := 0xfec698e3.
Lemma D_85044 : decode_any W_85044 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85048 : bv 32 := 0x00008067.
Lemma D_85048 : decode_any W_85048 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850a4 : bv 32 := 0x00a666b3.
Lemma D_850a4 : decode_any W_850a4 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850a8 : bv 32 := 0x00f6f693.
Lemma D_850a8 : decode_any W_850a8 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850ac : bv 32 := 0x02068063.
Lemma D_850ac : decode_any W_850ac = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850b0 : bv 32 := 0x04060863.
Lemma D_850b0 : decode_any W_850b0 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850b4 : bv 32 := 0x00c50633.
Lemma D_850b4 : decode_any W_850b4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850b8 : bv 32 := 0x00050693.
Lemma D_850b8 : decode_any W_850b8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850bc : bv 32 := 0x00b68023.
Lemma D_850bc : decode_any W_850bc = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850c0 : bv 32 := 0x00168693.
Lemma D_850c0 : decode_any W_850c0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850c4 : bv 32 := 0xfec69ce3.
Lemma D_850c4 : decode_any W_850c4 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850c8 : bv 32 := 0x0380006f.
Lemma D_850c8 : decode_any W_850c8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850cc : bv 32 := 0x02060a63.
Lemma D_850cc : decode_any W_850cc = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850d0 : bv 32 := 0x00c50633.
Lemma D_850d0 : decode_any W_850d0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850d4 : bv 32 := 0x00859693.
Lemma D_850d4 : decode_any W_850d4 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850d8 : bv 32 := 0x00b6e5b3.
Lemma D_850d8 : decode_any W_850d8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850dc : bv 32 := 0x01059693.
Lemma D_850dc : decode_any W_850dc = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850e0 : bv 32 := 0x00b6e5b3.
Lemma D_850e0 : decode_any W_850e0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850e4 : bv 32 := 0x02059693.
Lemma D_850e4 : decode_any W_850e4 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850e8 : bv 32 := 0x00b6e5b3.
Lemma D_850e8 : decode_any W_850e8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850ec : bv 32 := 0x00050693.
Lemma D_850ec : decode_any W_850ec = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850f0 : bv 32 := 0x00b6b023.
Lemma D_850f0 : decode_any W_850f0 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850f4 : bv 32 := 0x00b6b423.
Lemma D_850f4 : decode_any W_850f4 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850f8 : bv 32 := 0x01068693.
Lemma D_850f8 : decode_any W_850f8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_850fc : bv 32 := 0xfec6eae3.
Lemma D_850fc : decode_any W_850fc = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85100 : bv 32 := 0x00008067.
Lemma D_85100 : decode_any W_85100 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855d4 : bv 32 := 0xff010113.
Lemma D_855d4 : decode_any W_855d4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855d8 : bv 32 := 0x00113423.
Lemma D_855d8 : decode_any W_855d8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855dc : bv 32 := 0x00058693.
Lemma D_855dc : decode_any W_855dc = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855e0 : bv 32 := 0x00100713.
Lemma D_855e0 : decode_any W_855e0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855e4 : bv 32 := 0x02871713.
Lemma D_855e4 : decode_any W_855e4 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855e8 : bv 32 := 0x00170593.
Lemma D_855e8 : decode_any W_855e8 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855ec : bv 32 := 0x08b6f263.
Lemma D_855ec : decode_any W_855ec = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855f0 : bv 32 := 0x00000593.
Lemma D_855f0 : decode_any W_855f0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855f4 : bv 32 := 0x00d50733.
Lemma D_855f4 : decode_any W_855f4 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855f8 : bv 32 := 0x00750793.
Lemma D_855f8 : decode_any W_855f8 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_855fc : bv 32 := 0xff87f793.
Lemma D_855fc : decode_any W_855fc = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85600 : bv 32 := 0xff877613.
Lemma D_85600 : decode_any W_85600 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85604 : bv 32 := 0x02f57463.
Lemma D_85604 : decode_any W_85604 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85608 : bv 32 := 0x02068263.
Lemma D_85608 : decode_any W_85608 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8560c : bv 32 := 0x00000593.
Lemma D_8560c : decode_any W_8560c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85610 : bv 32 := 0x00150693.
Lemma D_85610 : decode_any W_85610 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85614 : bv 32 := 0x00068813.
Lemma D_85614 : decode_any W_85614 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85618 : bv 32 := 0xfff6c683.
Lemma D_85618 : decode_any W_85618 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8561c : bv 32 := 0x00d5e5b3.
Lemma D_8561c : decode_any W_8561c = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85620 : bv 32 := 0x00f87663.
Lemma D_85620 : decode_any W_85620 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85624 : bv 32 := 0x00180693.
Lemma D_85624 : decode_any W_85624 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85628 : bv 32 := 0xfee866e3.
Lemma D_85628 : decode_any W_85628 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8562c : bv 32 := 0x00c7fa63.
Lemma D_8562c : decode_any W_8562c = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85630 : bv 32 := 0x0007b683.
Lemma D_85630 : decode_any W_85630 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85634 : bv 32 := 0x00878793.
Lemma D_85634 : decode_any W_85634 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85638 : bv 32 := 0x00b6e5b3.
Lemma D_85638 : decode_any W_85638 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8563c : bv 32 := 0xfec7eae3.
Lemma D_8563c : decode_any W_8563c = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85640 : bv 32 := 0x02a66063.
Lemma D_85640 : decode_any W_85640 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85644 : bv 32 := 0x00e67e63.
Lemma D_85644 : decode_any W_85644 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85648 : bv 32 := 0x40c70733.
Lemma D_85648 : decode_any W_85648 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8564c : bv 32 := 0x00064503.
Lemma D_8564c : decode_any W_8564c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85650 : bv 32 := 0xfff70713.
Lemma D_85650 : decode_any W_85650 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85654 : bv 32 := 0x00a5e5b3.
Lemma D_85654 : decode_any W_85654 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85658 : bv 32 := 0x00160613.
Lemma D_85658 : decode_any W_85658 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8565c : bv 32 := 0xfe0718e3.
Lemma D_8565c : decode_any W_8565c = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85660 : bv 32 := 0x0015b513.
Lemma D_85660 : decode_any W_85660 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85664 : bv 32 := 0x00813083.
Lemma D_85664 : decode_any W_85664 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_85668 : bv 32 := 0x01010113.
Lemma D_85668 : decode_any W_85668 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8566c : bv 32 := 0x00008067.
Lemma D_8566c : decode_any W_8566c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
