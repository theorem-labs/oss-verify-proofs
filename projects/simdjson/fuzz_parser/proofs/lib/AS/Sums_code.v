(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
Definition W_78b78 : bv 32 := 0x02060063.
Lemma D_78b78 : decode_any W_78b78 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b7c : bv 32 := 0x00c50633.
Lemma D_78b7c : decode_any W_78b7c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b80 : bv 32 := 0x00050693.
Lemma D_78b80 : decode_any W_78b80 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b84 : bv 32 := 0x0005c703.
Lemma D_78b84 : decode_any W_78b84 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b88 : bv 32 := 0x00e68023.
Lemma D_78b88 : decode_any W_78b88 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b8c : bv 32 := 0x00168693.
Lemma D_78b8c : decode_any W_78b8c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b90 : bv 32 := 0x00158593.
Lemma D_78b90 : decode_any W_78b90 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b94 : bv 32 := 0xfec698e3.
Lemma D_78b94 : decode_any W_78b94 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78b98 : bv 32 := 0x00008067.
Lemma D_78b98 : decode_any W_78b98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78bf4 : bv 32 := 0x00a666b3.
Lemma D_78bf4 : decode_any W_78bf4 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78bf8 : bv 32 := 0x00f6f693.
Lemma D_78bf8 : decode_any W_78bf8 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78bfc : bv 32 := 0x02068063.
Lemma D_78bfc : decode_any W_78bfc = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c00 : bv 32 := 0x04060863.
Lemma D_78c00 : decode_any W_78c00 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c04 : bv 32 := 0x00c50633.
Lemma D_78c04 : decode_any W_78c04 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c08 : bv 32 := 0x00050693.
Lemma D_78c08 : decode_any W_78c08 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c0c : bv 32 := 0x00b68023.
Lemma D_78c0c : decode_any W_78c0c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c10 : bv 32 := 0x00168693.
Lemma D_78c10 : decode_any W_78c10 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c14 : bv 32 := 0xfec69ce3.
Lemma D_78c14 : decode_any W_78c14 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c18 : bv 32 := 0x0380006f.
Lemma D_78c18 : decode_any W_78c18 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c1c : bv 32 := 0x02060a63.
Lemma D_78c1c : decode_any W_78c1c = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c20 : bv 32 := 0x00c50633.
Lemma D_78c20 : decode_any W_78c20 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c24 : bv 32 := 0x00859693.
Lemma D_78c24 : decode_any W_78c24 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c28 : bv 32 := 0x00b6e5b3.
Lemma D_78c28 : decode_any W_78c28 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c2c : bv 32 := 0x01059693.
Lemma D_78c2c : decode_any W_78c2c = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c30 : bv 32 := 0x00b6e5b3.
Lemma D_78c30 : decode_any W_78c30 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c34 : bv 32 := 0x02059693.
Lemma D_78c34 : decode_any W_78c34 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c38 : bv 32 := 0x00b6e5b3.
Lemma D_78c38 : decode_any W_78c38 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c3c : bv 32 := 0x00050693.
Lemma D_78c3c : decode_any W_78c3c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c40 : bv 32 := 0x00b6b023.
Lemma D_78c40 : decode_any W_78c40 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c44 : bv 32 := 0x00b6b423.
Lemma D_78c44 : decode_any W_78c44 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c48 : bv 32 := 0x01068693.
Lemma D_78c48 : decode_any W_78c48 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c4c : bv 32 := 0xfec6eae3.
Lemma D_78c4c : decode_any W_78c4c = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78c50 : bv 32 := 0x00008067.
Lemma D_78c50 : decode_any W_78c50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79124 : bv 32 := 0xff010113.
Lemma D_79124 : decode_any W_79124 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79128 : bv 32 := 0x00113423.
Lemma D_79128 : decode_any W_79128 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7912c : bv 32 := 0x00058693.
Lemma D_7912c : decode_any W_7912c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79130 : bv 32 := 0x00100713.
Lemma D_79130 : decode_any W_79130 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79134 : bv 32 := 0x02871713.
Lemma D_79134 : decode_any W_79134 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79138 : bv 32 := 0x00170593.
Lemma D_79138 : decode_any W_79138 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7913c : bv 32 := 0x08b6f263.
Lemma D_7913c : decode_any W_7913c = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79140 : bv 32 := 0x00000593.
Lemma D_79140 : decode_any W_79140 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79144 : bv 32 := 0x00d50733.
Lemma D_79144 : decode_any W_79144 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79148 : bv 32 := 0x00750793.
Lemma D_79148 : decode_any W_79148 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7914c : bv 32 := 0xff87f793.
Lemma D_7914c : decode_any W_7914c = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79150 : bv 32 := 0xff877613.
Lemma D_79150 : decode_any W_79150 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79154 : bv 32 := 0x02f57463.
Lemma D_79154 : decode_any W_79154 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79158 : bv 32 := 0x02068263.
Lemma D_79158 : decode_any W_79158 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7915c : bv 32 := 0x00000593.
Lemma D_7915c : decode_any W_7915c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79160 : bv 32 := 0x00150693.
Lemma D_79160 : decode_any W_79160 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79164 : bv 32 := 0x00068813.
Lemma D_79164 : decode_any W_79164 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79168 : bv 32 := 0xfff6c683.
Lemma D_79168 : decode_any W_79168 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7916c : bv 32 := 0x00d5e5b3.
Lemma D_7916c : decode_any W_7916c = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79170 : bv 32 := 0x00f87663.
Lemma D_79170 : decode_any W_79170 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79174 : bv 32 := 0x00180693.
Lemma D_79174 : decode_any W_79174 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79178 : bv 32 := 0xfee866e3.
Lemma D_79178 : decode_any W_79178 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7917c : bv 32 := 0x00c7fa63.
Lemma D_7917c : decode_any W_7917c = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79180 : bv 32 := 0x0007b683.
Lemma D_79180 : decode_any W_79180 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79184 : bv 32 := 0x00878793.
Lemma D_79184 : decode_any W_79184 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79188 : bv 32 := 0x00b6e5b3.
Lemma D_79188 : decode_any W_79188 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7918c : bv 32 := 0xfec7eae3.
Lemma D_7918c : decode_any W_7918c = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79190 : bv 32 := 0x02a66063.
Lemma D_79190 : decode_any W_79190 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79194 : bv 32 := 0x00e67e63.
Lemma D_79194 : decode_any W_79194 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79198 : bv 32 := 0x40c70733.
Lemma D_79198 : decode_any W_79198 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7919c : bv 32 := 0x00064503.
Lemma D_7919c : decode_any W_7919c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791a0 : bv 32 := 0xfff70713.
Lemma D_791a0 : decode_any W_791a0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791a4 : bv 32 := 0x00a5e5b3.
Lemma D_791a4 : decode_any W_791a4 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791a8 : bv 32 := 0x00160613.
Lemma D_791a8 : decode_any W_791a8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791ac : bv 32 := 0xfe0718e3.
Lemma D_791ac : decode_any W_791ac = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791b0 : bv 32 := 0x0015b513.
Lemma D_791b0 : decode_any W_791b0 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791b4 : bv 32 := 0x00813083.
Lemma D_791b4 : decode_any W_791b4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791b8 : bv 32 := 0x01010113.
Lemma D_791b8 : decode_any W_791b8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_791bc : bv 32 := 0x00008067.
Lemma D_791bc : decode_any W_791bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
