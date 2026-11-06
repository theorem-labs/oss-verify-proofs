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
Definition W_73c9c : bv 32 := 0x02060063.
Lemma D_73c9c : decode_any W_73c9c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ca0 : bv 32 := 0x00c50633.
Lemma D_73ca0 : decode_any W_73ca0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ca4 : bv 32 := 0x00050693.
Lemma D_73ca4 : decode_any W_73ca4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ca8 : bv 32 := 0x0005c703.
Lemma D_73ca8 : decode_any W_73ca8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cac : bv 32 := 0x00e68023.
Lemma D_73cac : decode_any W_73cac = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cb0 : bv 32 := 0x00168693.
Lemma D_73cb0 : decode_any W_73cb0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cb4 : bv 32 := 0x00158593.
Lemma D_73cb4 : decode_any W_73cb4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cb8 : bv 32 := 0xfec698e3.
Lemma D_73cb8 : decode_any W_73cb8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cbc : bv 32 := 0x00008067.
Lemma D_73cbc : decode_any W_73cbc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d18 : bv 32 := 0x00a666b3.
Lemma D_73d18 : decode_any W_73d18 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d1c : bv 32 := 0x00f6f693.
Lemma D_73d1c : decode_any W_73d1c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d20 : bv 32 := 0x02068063.
Lemma D_73d20 : decode_any W_73d20 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d24 : bv 32 := 0x04060863.
Lemma D_73d24 : decode_any W_73d24 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d28 : bv 32 := 0x00c50633.
Lemma D_73d28 : decode_any W_73d28 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d2c : bv 32 := 0x00050693.
Lemma D_73d2c : decode_any W_73d2c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d30 : bv 32 := 0x00b68023.
Lemma D_73d30 : decode_any W_73d30 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d34 : bv 32 := 0x00168693.
Lemma D_73d34 : decode_any W_73d34 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d38 : bv 32 := 0xfec69ce3.
Lemma D_73d38 : decode_any W_73d38 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d3c : bv 32 := 0x0380006f.
Lemma D_73d3c : decode_any W_73d3c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d40 : bv 32 := 0x02060a63.
Lemma D_73d40 : decode_any W_73d40 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d44 : bv 32 := 0x00c50633.
Lemma D_73d44 : decode_any W_73d44 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d48 : bv 32 := 0x00859693.
Lemma D_73d48 : decode_any W_73d48 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d4c : bv 32 := 0x00b6e5b3.
Lemma D_73d4c : decode_any W_73d4c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d50 : bv 32 := 0x01059693.
Lemma D_73d50 : decode_any W_73d50 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d54 : bv 32 := 0x00b6e5b3.
Lemma D_73d54 : decode_any W_73d54 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d58 : bv 32 := 0x02059693.
Lemma D_73d58 : decode_any W_73d58 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d5c : bv 32 := 0x00b6e5b3.
Lemma D_73d5c : decode_any W_73d5c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d60 : bv 32 := 0x00050693.
Lemma D_73d60 : decode_any W_73d60 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d64 : bv 32 := 0x00b6b023.
Lemma D_73d64 : decode_any W_73d64 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d68 : bv 32 := 0x00b6b423.
Lemma D_73d68 : decode_any W_73d68 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d6c : bv 32 := 0x01068693.
Lemma D_73d6c : decode_any W_73d6c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d70 : bv 32 := 0xfec6eae3.
Lemma D_73d70 : decode_any W_73d70 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d74 : bv 32 := 0x00008067.
Lemma D_73d74 : decode_any W_73d74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74248 : bv 32 := 0xff010113.
Lemma D_74248 : decode_any W_74248 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7424c : bv 32 := 0x00113423.
Lemma D_7424c : decode_any W_7424c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74250 : bv 32 := 0x00058693.
Lemma D_74250 : decode_any W_74250 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74254 : bv 32 := 0x00100713.
Lemma D_74254 : decode_any W_74254 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74258 : bv 32 := 0x02871713.
Lemma D_74258 : decode_any W_74258 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7425c : bv 32 := 0x00170593.
Lemma D_7425c : decode_any W_7425c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74260 : bv 32 := 0x08b6f263.
Lemma D_74260 : decode_any W_74260 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74264 : bv 32 := 0x00000593.
Lemma D_74264 : decode_any W_74264 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74268 : bv 32 := 0x00d50733.
Lemma D_74268 : decode_any W_74268 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7426c : bv 32 := 0x00750793.
Lemma D_7426c : decode_any W_7426c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74270 : bv 32 := 0xff87f793.
Lemma D_74270 : decode_any W_74270 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74274 : bv 32 := 0xff877613.
Lemma D_74274 : decode_any W_74274 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74278 : bv 32 := 0x02f57463.
Lemma D_74278 : decode_any W_74278 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7427c : bv 32 := 0x02068263.
Lemma D_7427c : decode_any W_7427c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74280 : bv 32 := 0x00000593.
Lemma D_74280 : decode_any W_74280 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74284 : bv 32 := 0x00150693.
Lemma D_74284 : decode_any W_74284 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74288 : bv 32 := 0x00068813.
Lemma D_74288 : decode_any W_74288 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7428c : bv 32 := 0xfff6c683.
Lemma D_7428c : decode_any W_7428c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74290 : bv 32 := 0x00d5e5b3.
Lemma D_74290 : decode_any W_74290 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74294 : bv 32 := 0x00f87663.
Lemma D_74294 : decode_any W_74294 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74298 : bv 32 := 0x00180693.
Lemma D_74298 : decode_any W_74298 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7429c : bv 32 := 0xfee866e3.
Lemma D_7429c : decode_any W_7429c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742a0 : bv 32 := 0x00c7fa63.
Lemma D_742a0 : decode_any W_742a0 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742a4 : bv 32 := 0x0007b683.
Lemma D_742a4 : decode_any W_742a4 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742a8 : bv 32 := 0x00878793.
Lemma D_742a8 : decode_any W_742a8 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742ac : bv 32 := 0x00b6e5b3.
Lemma D_742ac : decode_any W_742ac = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742b0 : bv 32 := 0xfec7eae3.
Lemma D_742b0 : decode_any W_742b0 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742b4 : bv 32 := 0x02a66063.
Lemma D_742b4 : decode_any W_742b4 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742b8 : bv 32 := 0x00e67e63.
Lemma D_742b8 : decode_any W_742b8 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742bc : bv 32 := 0x40c70733.
Lemma D_742bc : decode_any W_742bc = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742c0 : bv 32 := 0x00064503.
Lemma D_742c0 : decode_any W_742c0 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742c4 : bv 32 := 0xfff70713.
Lemma D_742c4 : decode_any W_742c4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742c8 : bv 32 := 0x00a5e5b3.
Lemma D_742c8 : decode_any W_742c8 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742cc : bv 32 := 0x00160613.
Lemma D_742cc : decode_any W_742cc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742d0 : bv 32 := 0xfe0718e3.
Lemma D_742d0 : decode_any W_742d0 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742d4 : bv 32 := 0x0015b513.
Lemma D_742d4 : decode_any W_742d4 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742d8 : bv 32 := 0x00813083.
Lemma D_742d8 : decode_any W_742d8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742dc : bv 32 := 0x01010113.
Lemma D_742dc : decode_any W_742dc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_742e0 : bv 32 := 0x00008067.
Lemma D_742e0 : decode_any W_742e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
