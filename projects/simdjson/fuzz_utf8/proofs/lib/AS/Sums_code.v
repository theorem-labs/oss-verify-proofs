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
Definition W_93160 : bv 32 := 0x02060063.
Lemma D_93160 : decode_any W_93160 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93164 : bv 32 := 0x00c50633.
Lemma D_93164 : decode_any W_93164 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93168 : bv 32 := 0x00050693.
Lemma D_93168 : decode_any W_93168 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9316c : bv 32 := 0x0005c703.
Lemma D_9316c : decode_any W_9316c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93170 : bv 32 := 0x00e68023.
Lemma D_93170 : decode_any W_93170 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93174 : bv 32 := 0x00168693.
Lemma D_93174 : decode_any W_93174 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93178 : bv 32 := 0x00158593.
Lemma D_93178 : decode_any W_93178 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9317c : bv 32 := 0xfec698e3.
Lemma D_9317c : decode_any W_9317c = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93180 : bv 32 := 0x00008067.
Lemma D_93180 : decode_any W_93180 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_931dc : bv 32 := 0x00a666b3.
Lemma D_931dc : decode_any W_931dc = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_931e0 : bv 32 := 0x00f6f693.
Lemma D_931e0 : decode_any W_931e0 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_931e4 : bv 32 := 0x02068063.
Lemma D_931e4 : decode_any W_931e4 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_931e8 : bv 32 := 0x04060863.
Lemma D_931e8 : decode_any W_931e8 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_931ec : bv 32 := 0x00c50633.
Lemma D_931ec : decode_any W_931ec = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_931f0 : bv 32 := 0x00050693.
Lemma D_931f0 : decode_any W_931f0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_931f4 : bv 32 := 0x00b68023.
Lemma D_931f4 : decode_any W_931f4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_931f8 : bv 32 := 0x00168693.
Lemma D_931f8 : decode_any W_931f8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_931fc : bv 32 := 0xfec69ce3.
Lemma D_931fc : decode_any W_931fc = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93200 : bv 32 := 0x0380006f.
Lemma D_93200 : decode_any W_93200 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93204 : bv 32 := 0x02060a63.
Lemma D_93204 : decode_any W_93204 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93208 : bv 32 := 0x00c50633.
Lemma D_93208 : decode_any W_93208 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9320c : bv 32 := 0x00859693.
Lemma D_9320c : decode_any W_9320c = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93210 : bv 32 := 0x00b6e5b3.
Lemma D_93210 : decode_any W_93210 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93214 : bv 32 := 0x01059693.
Lemma D_93214 : decode_any W_93214 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93218 : bv 32 := 0x00b6e5b3.
Lemma D_93218 : decode_any W_93218 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9321c : bv 32 := 0x02059693.
Lemma D_9321c : decode_any W_9321c = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93220 : bv 32 := 0x00b6e5b3.
Lemma D_93220 : decode_any W_93220 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93224 : bv 32 := 0x00050693.
Lemma D_93224 : decode_any W_93224 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93228 : bv 32 := 0x00b6b023.
Lemma D_93228 : decode_any W_93228 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9322c : bv 32 := 0x00b6b423.
Lemma D_9322c : decode_any W_9322c = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93230 : bv 32 := 0x01068693.
Lemma D_93230 : decode_any W_93230 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93234 : bv 32 := 0xfec6eae3.
Lemma D_93234 : decode_any W_93234 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93238 : bv 32 := 0x00008067.
Lemma D_93238 : decode_any W_93238 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93728 : bv 32 := 0xff010113.
Lemma D_93728 : decode_any W_93728 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9372c : bv 32 := 0x00113423.
Lemma D_9372c : decode_any W_9372c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93730 : bv 32 := 0x00058693.
Lemma D_93730 : decode_any W_93730 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93734 : bv 32 := 0x00100713.
Lemma D_93734 : decode_any W_93734 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93738 : bv 32 := 0x02871713.
Lemma D_93738 : decode_any W_93738 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9373c : bv 32 := 0x00170593.
Lemma D_9373c : decode_any W_9373c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93740 : bv 32 := 0x08b6f263.
Lemma D_93740 : decode_any W_93740 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93744 : bv 32 := 0x00000593.
Lemma D_93744 : decode_any W_93744 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93748 : bv 32 := 0x00d50733.
Lemma D_93748 : decode_any W_93748 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9374c : bv 32 := 0x00750793.
Lemma D_9374c : decode_any W_9374c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93750 : bv 32 := 0xff87f793.
Lemma D_93750 : decode_any W_93750 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93754 : bv 32 := 0xff877613.
Lemma D_93754 : decode_any W_93754 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93758 : bv 32 := 0x02f57463.
Lemma D_93758 : decode_any W_93758 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9375c : bv 32 := 0x02068263.
Lemma D_9375c : decode_any W_9375c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93760 : bv 32 := 0x00000593.
Lemma D_93760 : decode_any W_93760 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93764 : bv 32 := 0x00150693.
Lemma D_93764 : decode_any W_93764 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93768 : bv 32 := 0x00068813.
Lemma D_93768 : decode_any W_93768 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9376c : bv 32 := 0xfff6c683.
Lemma D_9376c : decode_any W_9376c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93770 : bv 32 := 0x00d5e5b3.
Lemma D_93770 : decode_any W_93770 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93774 : bv 32 := 0x00f87663.
Lemma D_93774 : decode_any W_93774 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93778 : bv 32 := 0x00180693.
Lemma D_93778 : decode_any W_93778 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9377c : bv 32 := 0xfee866e3.
Lemma D_9377c : decode_any W_9377c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93780 : bv 32 := 0x00c7fa63.
Lemma D_93780 : decode_any W_93780 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93784 : bv 32 := 0x0007b683.
Lemma D_93784 : decode_any W_93784 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93788 : bv 32 := 0x00878793.
Lemma D_93788 : decode_any W_93788 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9378c : bv 32 := 0x00b6e5b3.
Lemma D_9378c : decode_any W_9378c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93790 : bv 32 := 0xfec7eae3.
Lemma D_93790 : decode_any W_93790 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93794 : bv 32 := 0x02a66063.
Lemma D_93794 : decode_any W_93794 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93798 : bv 32 := 0x00e67e63.
Lemma D_93798 : decode_any W_93798 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9379c : bv 32 := 0x40c70733.
Lemma D_9379c : decode_any W_9379c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_937a0 : bv 32 := 0x00064503.
Lemma D_937a0 : decode_any W_937a0 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_937a4 : bv 32 := 0xfff70713.
Lemma D_937a4 : decode_any W_937a4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_937a8 : bv 32 := 0x00a5e5b3.
Lemma D_937a8 : decode_any W_937a8 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_937ac : bv 32 := 0x00160613.
Lemma D_937ac : decode_any W_937ac = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_937b0 : bv 32 := 0xfe0718e3.
Lemma D_937b0 : decode_any W_937b0 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_937b4 : bv 32 := 0x0015b513.
Lemma D_937b4 : decode_any W_937b4 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_937b8 : bv 32 := 0x00813083.
Lemma D_937b8 : decode_any W_937b8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_937bc : bv 32 := 0x01010113.
Lemma D_937bc : decode_any W_937bc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_937c0 : bv 32 := 0x00008067.
Lemma D_937c0 : decode_any W_937c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
