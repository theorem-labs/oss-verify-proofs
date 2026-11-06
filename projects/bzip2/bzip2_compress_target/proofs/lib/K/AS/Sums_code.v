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
Definition W_64c0c : bv 32 := 0x02060063.
Lemma D_64c0c : decode_any W_64c0c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c10 : bv 32 := 0x00c50633.
Lemma D_64c10 : decode_any W_64c10 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c14 : bv 32 := 0x00050693.
Lemma D_64c14 : decode_any W_64c14 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c18 : bv 32 := 0x0005c703.
Lemma D_64c18 : decode_any W_64c18 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c1c : bv 32 := 0x00e68023.
Lemma D_64c1c : decode_any W_64c1c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c20 : bv 32 := 0x00168693.
Lemma D_64c20 : decode_any W_64c20 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c24 : bv 32 := 0x00158593.
Lemma D_64c24 : decode_any W_64c24 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c28 : bv 32 := 0xfec698e3.
Lemma D_64c28 : decode_any W_64c28 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c2c : bv 32 := 0x00008067.
Lemma D_64c2c : decode_any W_64c2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c88 : bv 32 := 0x00a666b3.
Lemma D_64c88 : decode_any W_64c88 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c8c : bv 32 := 0x00f6f693.
Lemma D_64c8c : decode_any W_64c8c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c90 : bv 32 := 0x02068063.
Lemma D_64c90 : decode_any W_64c90 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c94 : bv 32 := 0x04060863.
Lemma D_64c94 : decode_any W_64c94 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c98 : bv 32 := 0x00c50633.
Lemma D_64c98 : decode_any W_64c98 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64c9c : bv 32 := 0x00050693.
Lemma D_64c9c : decode_any W_64c9c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ca0 : bv 32 := 0x00b68023.
Lemma D_64ca0 : decode_any W_64ca0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ca4 : bv 32 := 0x00168693.
Lemma D_64ca4 : decode_any W_64ca4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ca8 : bv 32 := 0xfec69ce3.
Lemma D_64ca8 : decode_any W_64ca8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cac : bv 32 := 0x0380006f.
Lemma D_64cac : decode_any W_64cac = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cb0 : bv 32 := 0x02060a63.
Lemma D_64cb0 : decode_any W_64cb0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cb4 : bv 32 := 0x00c50633.
Lemma D_64cb4 : decode_any W_64cb4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cb8 : bv 32 := 0x00859693.
Lemma D_64cb8 : decode_any W_64cb8 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cbc : bv 32 := 0x00b6e5b3.
Lemma D_64cbc : decode_any W_64cbc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cc0 : bv 32 := 0x01059693.
Lemma D_64cc0 : decode_any W_64cc0 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cc4 : bv 32 := 0x00b6e5b3.
Lemma D_64cc4 : decode_any W_64cc4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cc8 : bv 32 := 0x02059693.
Lemma D_64cc8 : decode_any W_64cc8 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ccc : bv 32 := 0x00b6e5b3.
Lemma D_64ccc : decode_any W_64ccc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cd0 : bv 32 := 0x00050693.
Lemma D_64cd0 : decode_any W_64cd0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cd4 : bv 32 := 0x00b6b023.
Lemma D_64cd4 : decode_any W_64cd4 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cd8 : bv 32 := 0x00b6b423.
Lemma D_64cd8 : decode_any W_64cd8 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64cdc : bv 32 := 0x01068693.
Lemma D_64cdc : decode_any W_64cdc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ce0 : bv 32 := 0xfec6eae3.
Lemma D_64ce0 : decode_any W_64ce0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_64ce4 : bv 32 := 0x00008067.
Lemma D_64ce4 : decode_any W_64ce4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651b8 : bv 32 := 0xff010113.
Lemma D_651b8 : decode_any W_651b8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651bc : bv 32 := 0x00113423.
Lemma D_651bc : decode_any W_651bc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651c0 : bv 32 := 0x00058693.
Lemma D_651c0 : decode_any W_651c0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651c4 : bv 32 := 0x00100713.
Lemma D_651c4 : decode_any W_651c4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651c8 : bv 32 := 0x02871713.
Lemma D_651c8 : decode_any W_651c8 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651cc : bv 32 := 0x00170593.
Lemma D_651cc : decode_any W_651cc = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651d0 : bv 32 := 0x08b6f263.
Lemma D_651d0 : decode_any W_651d0 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651d4 : bv 32 := 0x00000593.
Lemma D_651d4 : decode_any W_651d4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651d8 : bv 32 := 0x00d50733.
Lemma D_651d8 : decode_any W_651d8 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651dc : bv 32 := 0x00750793.
Lemma D_651dc : decode_any W_651dc = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651e0 : bv 32 := 0xff87f793.
Lemma D_651e0 : decode_any W_651e0 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651e4 : bv 32 := 0xff877613.
Lemma D_651e4 : decode_any W_651e4 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651e8 : bv 32 := 0x02f57463.
Lemma D_651e8 : decode_any W_651e8 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651ec : bv 32 := 0x02068263.
Lemma D_651ec : decode_any W_651ec = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651f0 : bv 32 := 0x00000593.
Lemma D_651f0 : decode_any W_651f0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651f4 : bv 32 := 0x00150693.
Lemma D_651f4 : decode_any W_651f4 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651f8 : bv 32 := 0x00068813.
Lemma D_651f8 : decode_any W_651f8 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651fc : bv 32 := 0xfff6c683.
Lemma D_651fc : decode_any W_651fc = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65200 : bv 32 := 0x00d5e5b3.
Lemma D_65200 : decode_any W_65200 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65204 : bv 32 := 0x00f87663.
Lemma D_65204 : decode_any W_65204 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65208 : bv 32 := 0x00180693.
Lemma D_65208 : decode_any W_65208 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6520c : bv 32 := 0xfee866e3.
Lemma D_6520c : decode_any W_6520c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65210 : bv 32 := 0x00c7fa63.
Lemma D_65210 : decode_any W_65210 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65214 : bv 32 := 0x0007b683.
Lemma D_65214 : decode_any W_65214 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65218 : bv 32 := 0x00878793.
Lemma D_65218 : decode_any W_65218 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6521c : bv 32 := 0x00b6e5b3.
Lemma D_6521c : decode_any W_6521c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65220 : bv 32 := 0xfec7eae3.
Lemma D_65220 : decode_any W_65220 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65224 : bv 32 := 0x02a66063.
Lemma D_65224 : decode_any W_65224 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65228 : bv 32 := 0x00e67e63.
Lemma D_65228 : decode_any W_65228 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6522c : bv 32 := 0x40c70733.
Lemma D_6522c : decode_any W_6522c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65230 : bv 32 := 0x00064503.
Lemma D_65230 : decode_any W_65230 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65234 : bv 32 := 0xfff70713.
Lemma D_65234 : decode_any W_65234 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65238 : bv 32 := 0x00a5e5b3.
Lemma D_65238 : decode_any W_65238 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6523c : bv 32 := 0x00160613.
Lemma D_6523c : decode_any W_6523c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65240 : bv 32 := 0xfe0718e3.
Lemma D_65240 : decode_any W_65240 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65244 : bv 32 := 0x0015b513.
Lemma D_65244 : decode_any W_65244 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65248 : bv 32 := 0x00813083.
Lemma D_65248 : decode_any W_65248 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6524c : bv 32 := 0x01010113.
Lemma D_6524c : decode_any W_6524c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65250 : bv 32 := 0x00008067.
Lemma D_65250 : decode_any W_65250 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
