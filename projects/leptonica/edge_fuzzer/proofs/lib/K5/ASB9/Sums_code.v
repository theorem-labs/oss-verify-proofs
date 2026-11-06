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
Definition W_ca488 : bv 32 := 0x02060063.
Lemma D_ca488 : decode_any W_ca488 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca48c : bv 32 := 0x00c50633.
Lemma D_ca48c : decode_any W_ca48c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca490 : bv 32 := 0x00050693.
Lemma D_ca490 : decode_any W_ca490 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca494 : bv 32 := 0x0005c703.
Lemma D_ca494 : decode_any W_ca494 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca498 : bv 32 := 0x00e68023.
Lemma D_ca498 : decode_any W_ca498 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca49c : bv 32 := 0x00168693.
Lemma D_ca49c : decode_any W_ca49c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca4a0 : bv 32 := 0x00158593.
Lemma D_ca4a0 : decode_any W_ca4a0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca4a4 : bv 32 := 0xfec698e3.
Lemma D_ca4a4 : decode_any W_ca4a4 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca4a8 : bv 32 := 0x00008067.
Lemma D_ca4a8 : decode_any W_ca4a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca504 : bv 32 := 0x00a666b3.
Lemma D_ca504 : decode_any W_ca504 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca508 : bv 32 := 0x00f6f693.
Lemma D_ca508 : decode_any W_ca508 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca50c : bv 32 := 0x02068063.
Lemma D_ca50c : decode_any W_ca50c = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca510 : bv 32 := 0x04060863.
Lemma D_ca510 : decode_any W_ca510 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca514 : bv 32 := 0x00c50633.
Lemma D_ca514 : decode_any W_ca514 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca518 : bv 32 := 0x00050693.
Lemma D_ca518 : decode_any W_ca518 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca51c : bv 32 := 0x00b68023.
Lemma D_ca51c : decode_any W_ca51c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca520 : bv 32 := 0x00168693.
Lemma D_ca520 : decode_any W_ca520 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca524 : bv 32 := 0xfec69ce3.
Lemma D_ca524 : decode_any W_ca524 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca528 : bv 32 := 0x0380006f.
Lemma D_ca528 : decode_any W_ca528 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca52c : bv 32 := 0x02060a63.
Lemma D_ca52c : decode_any W_ca52c = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca530 : bv 32 := 0x00c50633.
Lemma D_ca530 : decode_any W_ca530 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca534 : bv 32 := 0x00859693.
Lemma D_ca534 : decode_any W_ca534 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca538 : bv 32 := 0x00b6e5b3.
Lemma D_ca538 : decode_any W_ca538 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca53c : bv 32 := 0x01059693.
Lemma D_ca53c : decode_any W_ca53c = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca540 : bv 32 := 0x00b6e5b3.
Lemma D_ca540 : decode_any W_ca540 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca544 : bv 32 := 0x02059693.
Lemma D_ca544 : decode_any W_ca544 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca548 : bv 32 := 0x00b6e5b3.
Lemma D_ca548 : decode_any W_ca548 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca54c : bv 32 := 0x00050693.
Lemma D_ca54c : decode_any W_ca54c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca550 : bv 32 := 0x00b6b023.
Lemma D_ca550 : decode_any W_ca550 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca554 : bv 32 := 0x00b6b423.
Lemma D_ca554 : decode_any W_ca554 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca558 : bv 32 := 0x01068693.
Lemma D_ca558 : decode_any W_ca558 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca55c : bv 32 := 0xfec6eae3.
Lemma D_ca55c : decode_any W_ca55c = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca560 : bv 32 := 0x00008067.
Lemma D_ca560 : decode_any W_ca560 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa34 : bv 32 := 0xff010113.
Lemma D_caa34 : decode_any W_caa34 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa38 : bv 32 := 0x00113423.
Lemma D_caa38 : decode_any W_caa38 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa3c : bv 32 := 0x00058693.
Lemma D_caa3c : decode_any W_caa3c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa40 : bv 32 := 0x00100713.
Lemma D_caa40 : decode_any W_caa40 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa44 : bv 32 := 0x02871713.
Lemma D_caa44 : decode_any W_caa44 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa48 : bv 32 := 0x00170593.
Lemma D_caa48 : decode_any W_caa48 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa4c : bv 32 := 0x08b6f263.
Lemma D_caa4c : decode_any W_caa4c = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa50 : bv 32 := 0x00000593.
Lemma D_caa50 : decode_any W_caa50 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa54 : bv 32 := 0x00d50733.
Lemma D_caa54 : decode_any W_caa54 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa58 : bv 32 := 0x00750793.
Lemma D_caa58 : decode_any W_caa58 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa5c : bv 32 := 0xff87f793.
Lemma D_caa5c : decode_any W_caa5c = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa60 : bv 32 := 0xff877613.
Lemma D_caa60 : decode_any W_caa60 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa64 : bv 32 := 0x02f57463.
Lemma D_caa64 : decode_any W_caa64 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa68 : bv 32 := 0x02068263.
Lemma D_caa68 : decode_any W_caa68 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa6c : bv 32 := 0x00000593.
Lemma D_caa6c : decode_any W_caa6c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa70 : bv 32 := 0x00150693.
Lemma D_caa70 : decode_any W_caa70 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa74 : bv 32 := 0x00068813.
Lemma D_caa74 : decode_any W_caa74 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa78 : bv 32 := 0xfff6c683.
Lemma D_caa78 : decode_any W_caa78 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa7c : bv 32 := 0x00d5e5b3.
Lemma D_caa7c : decode_any W_caa7c = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa80 : bv 32 := 0x00f87663.
Lemma D_caa80 : decode_any W_caa80 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa84 : bv 32 := 0x00180693.
Lemma D_caa84 : decode_any W_caa84 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa88 : bv 32 := 0xfee866e3.
Lemma D_caa88 : decode_any W_caa88 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa8c : bv 32 := 0x00c7fa63.
Lemma D_caa8c : decode_any W_caa8c = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa90 : bv 32 := 0x0007b683.
Lemma D_caa90 : decode_any W_caa90 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa94 : bv 32 := 0x00878793.
Lemma D_caa94 : decode_any W_caa94 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa98 : bv 32 := 0x00b6e5b3.
Lemma D_caa98 : decode_any W_caa98 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caa9c : bv 32 := 0xfec7eae3.
Lemma D_caa9c : decode_any W_caa9c = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caaa0 : bv 32 := 0x02a66063.
Lemma D_caaa0 : decode_any W_caaa0 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caaa4 : bv 32 := 0x00e67e63.
Lemma D_caaa4 : decode_any W_caaa4 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caaa8 : bv 32 := 0x40c70733.
Lemma D_caaa8 : decode_any W_caaa8 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caaac : bv 32 := 0x00064503.
Lemma D_caaac : decode_any W_caaac = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caab0 : bv 32 := 0xfff70713.
Lemma D_caab0 : decode_any W_caab0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caab4 : bv 32 := 0x00a5e5b3.
Lemma D_caab4 : decode_any W_caab4 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caab8 : bv 32 := 0x00160613.
Lemma D_caab8 : decode_any W_caab8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caabc : bv 32 := 0xfe0718e3.
Lemma D_caabc : decode_any W_caabc = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caac0 : bv 32 := 0x0015b513.
Lemma D_caac0 : decode_any W_caac0 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caac4 : bv 32 := 0x00813083.
Lemma D_caac4 : decode_any W_caac4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caac8 : bv 32 := 0x01010113.
Lemma D_caac8 : decode_any W_caac8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_caacc : bv 32 := 0x00008067.
Lemma D_caacc : decode_any W_caacc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
