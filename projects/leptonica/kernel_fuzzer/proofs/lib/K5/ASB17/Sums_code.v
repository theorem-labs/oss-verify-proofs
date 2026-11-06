(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
Definition W_6f60c : bv 32 := 0x02060063.
Lemma D_6f60c : decode_any W_6f60c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f610 : bv 32 := 0x00c50633.
Lemma D_6f610 : decode_any W_6f610 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f614 : bv 32 := 0x00050693.
Lemma D_6f614 : decode_any W_6f614 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f618 : bv 32 := 0x0005c703.
Lemma D_6f618 : decode_any W_6f618 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f61c : bv 32 := 0x00e68023.
Lemma D_6f61c : decode_any W_6f61c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f620 : bv 32 := 0x00168693.
Lemma D_6f620 : decode_any W_6f620 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f624 : bv 32 := 0x00158593.
Lemma D_6f624 : decode_any W_6f624 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f628 : bv 32 := 0xfec698e3.
Lemma D_6f628 : decode_any W_6f628 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f62c : bv 32 := 0x00008067.
Lemma D_6f62c : decode_any W_6f62c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f688 : bv 32 := 0x00a666b3.
Lemma D_6f688 : decode_any W_6f688 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f68c : bv 32 := 0x00f6f693.
Lemma D_6f68c : decode_any W_6f68c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f690 : bv 32 := 0x02068063.
Lemma D_6f690 : decode_any W_6f690 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f694 : bv 32 := 0x04060863.
Lemma D_6f694 : decode_any W_6f694 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f698 : bv 32 := 0x00c50633.
Lemma D_6f698 : decode_any W_6f698 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f69c : bv 32 := 0x00050693.
Lemma D_6f69c : decode_any W_6f69c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6a0 : bv 32 := 0x00b68023.
Lemma D_6f6a0 : decode_any W_6f6a0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6a4 : bv 32 := 0x00168693.
Lemma D_6f6a4 : decode_any W_6f6a4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6a8 : bv 32 := 0xfec69ce3.
Lemma D_6f6a8 : decode_any W_6f6a8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6ac : bv 32 := 0x0380006f.
Lemma D_6f6ac : decode_any W_6f6ac = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6b0 : bv 32 := 0x02060a63.
Lemma D_6f6b0 : decode_any W_6f6b0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6b4 : bv 32 := 0x00c50633.
Lemma D_6f6b4 : decode_any W_6f6b4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6b8 : bv 32 := 0x00859693.
Lemma D_6f6b8 : decode_any W_6f6b8 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6bc : bv 32 := 0x00b6e5b3.
Lemma D_6f6bc : decode_any W_6f6bc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6c0 : bv 32 := 0x01059693.
Lemma D_6f6c0 : decode_any W_6f6c0 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6c4 : bv 32 := 0x00b6e5b3.
Lemma D_6f6c4 : decode_any W_6f6c4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6c8 : bv 32 := 0x02059693.
Lemma D_6f6c8 : decode_any W_6f6c8 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6cc : bv 32 := 0x00b6e5b3.
Lemma D_6f6cc : decode_any W_6f6cc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6d0 : bv 32 := 0x00050693.
Lemma D_6f6d0 : decode_any W_6f6d0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6d4 : bv 32 := 0x00b6b023.
Lemma D_6f6d4 : decode_any W_6f6d4 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6d8 : bv 32 := 0x00b6b423.
Lemma D_6f6d8 : decode_any W_6f6d8 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6dc : bv 32 := 0x01068693.
Lemma D_6f6dc : decode_any W_6f6dc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6e0 : bv 32 := 0xfec6eae3.
Lemma D_6f6e0 : decode_any W_6f6e0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f6e4 : bv 32 := 0x00008067.
Lemma D_6f6e4 : decode_any W_6f6e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbb8 : bv 32 := 0xff010113.
Lemma D_6fbb8 : decode_any W_6fbb8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbbc : bv 32 := 0x00113423.
Lemma D_6fbbc : decode_any W_6fbbc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbc0 : bv 32 := 0x00058693.
Lemma D_6fbc0 : decode_any W_6fbc0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbc4 : bv 32 := 0x00100713.
Lemma D_6fbc4 : decode_any W_6fbc4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbc8 : bv 32 := 0x02871713.
Lemma D_6fbc8 : decode_any W_6fbc8 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbcc : bv 32 := 0x00170593.
Lemma D_6fbcc : decode_any W_6fbcc = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbd0 : bv 32 := 0x08b6f263.
Lemma D_6fbd0 : decode_any W_6fbd0 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbd4 : bv 32 := 0x00000593.
Lemma D_6fbd4 : decode_any W_6fbd4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbd8 : bv 32 := 0x00d50733.
Lemma D_6fbd8 : decode_any W_6fbd8 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbdc : bv 32 := 0x00750793.
Lemma D_6fbdc : decode_any W_6fbdc = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbe0 : bv 32 := 0xff87f793.
Lemma D_6fbe0 : decode_any W_6fbe0 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbe4 : bv 32 := 0xff877613.
Lemma D_6fbe4 : decode_any W_6fbe4 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbe8 : bv 32 := 0x02f57463.
Lemma D_6fbe8 : decode_any W_6fbe8 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbec : bv 32 := 0x02068263.
Lemma D_6fbec : decode_any W_6fbec = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbf0 : bv 32 := 0x00000593.
Lemma D_6fbf0 : decode_any W_6fbf0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbf4 : bv 32 := 0x00150693.
Lemma D_6fbf4 : decode_any W_6fbf4 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbf8 : bv 32 := 0x00068813.
Lemma D_6fbf8 : decode_any W_6fbf8 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fbfc : bv 32 := 0xfff6c683.
Lemma D_6fbfc : decode_any W_6fbfc = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc00 : bv 32 := 0x00d5e5b3.
Lemma D_6fc00 : decode_any W_6fc00 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc04 : bv 32 := 0x00f87663.
Lemma D_6fc04 : decode_any W_6fc04 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc08 : bv 32 := 0x00180693.
Lemma D_6fc08 : decode_any W_6fc08 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc0c : bv 32 := 0xfee866e3.
Lemma D_6fc0c : decode_any W_6fc0c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc10 : bv 32 := 0x00c7fa63.
Lemma D_6fc10 : decode_any W_6fc10 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc14 : bv 32 := 0x0007b683.
Lemma D_6fc14 : decode_any W_6fc14 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc18 : bv 32 := 0x00878793.
Lemma D_6fc18 : decode_any W_6fc18 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc1c : bv 32 := 0x00b6e5b3.
Lemma D_6fc1c : decode_any W_6fc1c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc20 : bv 32 := 0xfec7eae3.
Lemma D_6fc20 : decode_any W_6fc20 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc24 : bv 32 := 0x02a66063.
Lemma D_6fc24 : decode_any W_6fc24 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc28 : bv 32 := 0x00e67e63.
Lemma D_6fc28 : decode_any W_6fc28 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc2c : bv 32 := 0x40c70733.
Lemma D_6fc2c : decode_any W_6fc2c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc30 : bv 32 := 0x00064503.
Lemma D_6fc30 : decode_any W_6fc30 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc34 : bv 32 := 0xfff70713.
Lemma D_6fc34 : decode_any W_6fc34 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc38 : bv 32 := 0x00a5e5b3.
Lemma D_6fc38 : decode_any W_6fc38 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc3c : bv 32 := 0x00160613.
Lemma D_6fc3c : decode_any W_6fc3c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc40 : bv 32 := 0xfe0718e3.
Lemma D_6fc40 : decode_any W_6fc40 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc44 : bv 32 := 0x0015b513.
Lemma D_6fc44 : decode_any W_6fc44 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc48 : bv 32 := 0x00813083.
Lemma D_6fc48 : decode_any W_6fc48 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc4c : bv 32 := 0x01010113.
Lemma D_6fc4c : decode_any W_6fc4c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fc50 : bv 32 := 0x00008067.
Lemma D_6fc50 : decode_any W_6fc50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
