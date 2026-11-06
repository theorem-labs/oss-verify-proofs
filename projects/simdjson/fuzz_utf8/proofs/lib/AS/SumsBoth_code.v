(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
Definition W_92fac : bv 32 := 0x02060063.
Lemma D_92fac : decode_any W_92fac = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92fb0 : bv 32 := 0x00c50633.
Lemma D_92fb0 : decode_any W_92fb0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92fb4 : bv 32 := 0x00050693.
Lemma D_92fb4 : decode_any W_92fb4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92fb8 : bv 32 := 0x0005c703.
Lemma D_92fb8 : decode_any W_92fb8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92fbc : bv 32 := 0x00e68023.
Lemma D_92fbc : decode_any W_92fbc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92fc0 : bv 32 := 0x00168693.
Lemma D_92fc0 : decode_any W_92fc0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92fc4 : bv 32 := 0x00158593.
Lemma D_92fc4 : decode_any W_92fc4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92fc8 : bv 32 := 0xfec698e3.
Lemma D_92fc8 : decode_any W_92fc8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92fcc : bv 32 := 0x00008067.
Lemma D_92fcc : decode_any W_92fcc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93028 : bv 32 := 0x00a666b3.
Lemma D_93028 : decode_any W_93028 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9302c : bv 32 := 0x00f6f693.
Lemma D_9302c : decode_any W_9302c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93030 : bv 32 := 0x02068063.
Lemma D_93030 : decode_any W_93030 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93034 : bv 32 := 0x04060863.
Lemma D_93034 : decode_any W_93034 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93038 : bv 32 := 0x00c50633.
Lemma D_93038 : decode_any W_93038 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9303c : bv 32 := 0x00050693.
Lemma D_9303c : decode_any W_9303c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93040 : bv 32 := 0x00b68023.
Lemma D_93040 : decode_any W_93040 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93044 : bv 32 := 0x00168693.
Lemma D_93044 : decode_any W_93044 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93048 : bv 32 := 0xfec69ce3.
Lemma D_93048 : decode_any W_93048 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9304c : bv 32 := 0x0380006f.
Lemma D_9304c : decode_any W_9304c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93050 : bv 32 := 0x02060a63.
Lemma D_93050 : decode_any W_93050 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93054 : bv 32 := 0x00c50633.
Lemma D_93054 : decode_any W_93054 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93058 : bv 32 := 0x00859693.
Lemma D_93058 : decode_any W_93058 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9305c : bv 32 := 0x00b6e5b3.
Lemma D_9305c : decode_any W_9305c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93060 : bv 32 := 0x01059693.
Lemma D_93060 : decode_any W_93060 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93064 : bv 32 := 0x00b6e5b3.
Lemma D_93064 : decode_any W_93064 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93068 : bv 32 := 0x02059693.
Lemma D_93068 : decode_any W_93068 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9306c : bv 32 := 0x00b6e5b3.
Lemma D_9306c : decode_any W_9306c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93070 : bv 32 := 0x00050693.
Lemma D_93070 : decode_any W_93070 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93074 : bv 32 := 0x00b6b023.
Lemma D_93074 : decode_any W_93074 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93078 : bv 32 := 0x00b6b423.
Lemma D_93078 : decode_any W_93078 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9307c : bv 32 := 0x01068693.
Lemma D_9307c : decode_any W_9307c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93080 : bv 32 := 0xfec6eae3.
Lemma D_93080 : decode_any W_93080 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93084 : bv 32 := 0x00008067.
Lemma D_93084 : decode_any W_93084 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93574 : bv 32 := 0xff010113.
Lemma D_93574 : decode_any W_93574 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93578 : bv 32 := 0x00113423.
Lemma D_93578 : decode_any W_93578 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9357c : bv 32 := 0x00058693.
Lemma D_9357c : decode_any W_9357c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93580 : bv 32 := 0x00100713.
Lemma D_93580 : decode_any W_93580 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93584 : bv 32 := 0x02871713.
Lemma D_93584 : decode_any W_93584 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93588 : bv 32 := 0x00170593.
Lemma D_93588 : decode_any W_93588 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9358c : bv 32 := 0x08b6f263.
Lemma D_9358c : decode_any W_9358c = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93590 : bv 32 := 0x00000593.
Lemma D_93590 : decode_any W_93590 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93594 : bv 32 := 0x00d50733.
Lemma D_93594 : decode_any W_93594 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93598 : bv 32 := 0x00750793.
Lemma D_93598 : decode_any W_93598 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9359c : bv 32 := 0xff87f793.
Lemma D_9359c : decode_any W_9359c = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935a0 : bv 32 := 0xff877613.
Lemma D_935a0 : decode_any W_935a0 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935a4 : bv 32 := 0x02f57463.
Lemma D_935a4 : decode_any W_935a4 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935a8 : bv 32 := 0x02068263.
Lemma D_935a8 : decode_any W_935a8 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935ac : bv 32 := 0x00000593.
Lemma D_935ac : decode_any W_935ac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935b0 : bv 32 := 0x00150693.
Lemma D_935b0 : decode_any W_935b0 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935b4 : bv 32 := 0x00068813.
Lemma D_935b4 : decode_any W_935b4 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935b8 : bv 32 := 0xfff6c683.
Lemma D_935b8 : decode_any W_935b8 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935bc : bv 32 := 0x00d5e5b3.
Lemma D_935bc : decode_any W_935bc = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935c0 : bv 32 := 0x00f87663.
Lemma D_935c0 : decode_any W_935c0 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935c4 : bv 32 := 0x00180693.
Lemma D_935c4 : decode_any W_935c4 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935c8 : bv 32 := 0xfee866e3.
Lemma D_935c8 : decode_any W_935c8 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935cc : bv 32 := 0x00c7fa63.
Lemma D_935cc : decode_any W_935cc = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935d0 : bv 32 := 0x0007b683.
Lemma D_935d0 : decode_any W_935d0 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935d4 : bv 32 := 0x00878793.
Lemma D_935d4 : decode_any W_935d4 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935d8 : bv 32 := 0x00b6e5b3.
Lemma D_935d8 : decode_any W_935d8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935dc : bv 32 := 0xfec7eae3.
Lemma D_935dc : decode_any W_935dc = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935e0 : bv 32 := 0x02a66063.
Lemma D_935e0 : decode_any W_935e0 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935e4 : bv 32 := 0x00e67e63.
Lemma D_935e4 : decode_any W_935e4 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935e8 : bv 32 := 0x40c70733.
Lemma D_935e8 : decode_any W_935e8 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935ec : bv 32 := 0x00064503.
Lemma D_935ec : decode_any W_935ec = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935f0 : bv 32 := 0xfff70713.
Lemma D_935f0 : decode_any W_935f0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935f4 : bv 32 := 0x00a5e5b3.
Lemma D_935f4 : decode_any W_935f4 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935f8 : bv 32 := 0x00160613.
Lemma D_935f8 : decode_any W_935f8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_935fc : bv 32 := 0xfe0718e3.
Lemma D_935fc : decode_any W_935fc = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93600 : bv 32 := 0x0015b513.
Lemma D_93600 : decode_any W_93600 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93604 : bv 32 := 0x00813083.
Lemma D_93604 : decode_any W_93604 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93608 : bv 32 := 0x01010113.
Lemma D_93608 : decode_any W_93608 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9360c : bv 32 := 0x00008067.
Lemma D_9360c : decode_any W_9360c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
