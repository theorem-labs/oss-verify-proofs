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
Definition W_73c0c : bv 32 := 0x02060063.
Lemma D_73c0c : decode_any W_73c0c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c10 : bv 32 := 0x00c50633.
Lemma D_73c10 : decode_any W_73c10 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c14 : bv 32 := 0x00050693.
Lemma D_73c14 : decode_any W_73c14 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c18 : bv 32 := 0x0005c703.
Lemma D_73c18 : decode_any W_73c18 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c1c : bv 32 := 0x00e68023.
Lemma D_73c1c : decode_any W_73c1c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c20 : bv 32 := 0x00168693.
Lemma D_73c20 : decode_any W_73c20 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c24 : bv 32 := 0x00158593.
Lemma D_73c24 : decode_any W_73c24 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c28 : bv 32 := 0xfec698e3.
Lemma D_73c28 : decode_any W_73c28 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c2c : bv 32 := 0x00008067.
Lemma D_73c2c : decode_any W_73c2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c88 : bv 32 := 0x00a666b3.
Lemma D_73c88 : decode_any W_73c88 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c8c : bv 32 := 0x00f6f693.
Lemma D_73c8c : decode_any W_73c8c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c90 : bv 32 := 0x02068063.
Lemma D_73c90 : decode_any W_73c90 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c94 : bv 32 := 0x04060863.
Lemma D_73c94 : decode_any W_73c94 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c98 : bv 32 := 0x00c50633.
Lemma D_73c98 : decode_any W_73c98 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c9c : bv 32 := 0x00050693.
Lemma D_73c9c : decode_any W_73c9c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ca0 : bv 32 := 0x00b68023.
Lemma D_73ca0 : decode_any W_73ca0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ca4 : bv 32 := 0x00168693.
Lemma D_73ca4 : decode_any W_73ca4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ca8 : bv 32 := 0xfec69ce3.
Lemma D_73ca8 : decode_any W_73ca8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cac : bv 32 := 0x0380006f.
Lemma D_73cac : decode_any W_73cac = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cb0 : bv 32 := 0x02060a63.
Lemma D_73cb0 : decode_any W_73cb0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cb4 : bv 32 := 0x00c50633.
Lemma D_73cb4 : decode_any W_73cb4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cb8 : bv 32 := 0x00859693.
Lemma D_73cb8 : decode_any W_73cb8 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cbc : bv 32 := 0x00b6e5b3.
Lemma D_73cbc : decode_any W_73cbc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cc0 : bv 32 := 0x01059693.
Lemma D_73cc0 : decode_any W_73cc0 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cc4 : bv 32 := 0x00b6e5b3.
Lemma D_73cc4 : decode_any W_73cc4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cc8 : bv 32 := 0x02059693.
Lemma D_73cc8 : decode_any W_73cc8 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ccc : bv 32 := 0x00b6e5b3.
Lemma D_73ccc : decode_any W_73ccc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cd0 : bv 32 := 0x00050693.
Lemma D_73cd0 : decode_any W_73cd0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cd4 : bv 32 := 0x00b6b023.
Lemma D_73cd4 : decode_any W_73cd4 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cd8 : bv 32 := 0x00b6b423.
Lemma D_73cd8 : decode_any W_73cd8 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cdc : bv 32 := 0x01068693.
Lemma D_73cdc : decode_any W_73cdc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ce0 : bv 32 := 0xfec6eae3.
Lemma D_73ce0 : decode_any W_73ce0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ce4 : bv 32 := 0x00008067.
Lemma D_73ce4 : decode_any W_73ce4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741b8 : bv 32 := 0xff010113.
Lemma D_741b8 : decode_any W_741b8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741bc : bv 32 := 0x00113423.
Lemma D_741bc : decode_any W_741bc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741c0 : bv 32 := 0x00058693.
Lemma D_741c0 : decode_any W_741c0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741c4 : bv 32 := 0x00100713.
Lemma D_741c4 : decode_any W_741c4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741c8 : bv 32 := 0x02871713.
Lemma D_741c8 : decode_any W_741c8 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741cc : bv 32 := 0x00170593.
Lemma D_741cc : decode_any W_741cc = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741d0 : bv 32 := 0x08b6f263.
Lemma D_741d0 : decode_any W_741d0 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741d4 : bv 32 := 0x00000593.
Lemma D_741d4 : decode_any W_741d4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741d8 : bv 32 := 0x00d50733.
Lemma D_741d8 : decode_any W_741d8 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741dc : bv 32 := 0x00750793.
Lemma D_741dc : decode_any W_741dc = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741e0 : bv 32 := 0xff87f793.
Lemma D_741e0 : decode_any W_741e0 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741e4 : bv 32 := 0xff877613.
Lemma D_741e4 : decode_any W_741e4 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741e8 : bv 32 := 0x02f57463.
Lemma D_741e8 : decode_any W_741e8 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741ec : bv 32 := 0x02068263.
Lemma D_741ec : decode_any W_741ec = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741f0 : bv 32 := 0x00000593.
Lemma D_741f0 : decode_any W_741f0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741f4 : bv 32 := 0x00150693.
Lemma D_741f4 : decode_any W_741f4 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741f8 : bv 32 := 0x00068813.
Lemma D_741f8 : decode_any W_741f8 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741fc : bv 32 := 0xfff6c683.
Lemma D_741fc : decode_any W_741fc = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74200 : bv 32 := 0x00d5e5b3.
Lemma D_74200 : decode_any W_74200 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74204 : bv 32 := 0x00f87663.
Lemma D_74204 : decode_any W_74204 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74208 : bv 32 := 0x00180693.
Lemma D_74208 : decode_any W_74208 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7420c : bv 32 := 0xfee866e3.
Lemma D_7420c : decode_any W_7420c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74210 : bv 32 := 0x00c7fa63.
Lemma D_74210 : decode_any W_74210 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74214 : bv 32 := 0x0007b683.
Lemma D_74214 : decode_any W_74214 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74218 : bv 32 := 0x00878793.
Lemma D_74218 : decode_any W_74218 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7421c : bv 32 := 0x00b6e5b3.
Lemma D_7421c : decode_any W_7421c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74220 : bv 32 := 0xfec7eae3.
Lemma D_74220 : decode_any W_74220 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74224 : bv 32 := 0x02a66063.
Lemma D_74224 : decode_any W_74224 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74228 : bv 32 := 0x00e67e63.
Lemma D_74228 : decode_any W_74228 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7422c : bv 32 := 0x40c70733.
Lemma D_7422c : decode_any W_7422c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74230 : bv 32 := 0x00064503.
Lemma D_74230 : decode_any W_74230 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74234 : bv 32 := 0xfff70713.
Lemma D_74234 : decode_any W_74234 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74238 : bv 32 := 0x00a5e5b3.
Lemma D_74238 : decode_any W_74238 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7423c : bv 32 := 0x00160613.
Lemma D_7423c : decode_any W_7423c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74240 : bv 32 := 0xfe0718e3.
Lemma D_74240 : decode_any W_74240 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74244 : bv 32 := 0x0015b513.
Lemma D_74244 : decode_any W_74244 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74248 : bv 32 := 0x00813083.
Lemma D_74248 : decode_any W_74248 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7424c : bv 32 := 0x01010113.
Lemma D_7424c : decode_any W_7424c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74250 : bv 32 := 0x00008067.
Lemma D_74250 : decode_any W_74250 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
