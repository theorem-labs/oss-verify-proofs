(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
Definition W_7891c : bv 32 := 0x02060063.
Lemma D_7891c : decode_any W_7891c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78920 : bv 32 := 0x00c50633.
Lemma D_78920 : decode_any W_78920 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78924 : bv 32 := 0x00050693.
Lemma D_78924 : decode_any W_78924 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78928 : bv 32 := 0x0005c703.
Lemma D_78928 : decode_any W_78928 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7892c : bv 32 := 0x00e68023.
Lemma D_7892c : decode_any W_7892c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78930 : bv 32 := 0x00168693.
Lemma D_78930 : decode_any W_78930 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78934 : bv 32 := 0x00158593.
Lemma D_78934 : decode_any W_78934 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78938 : bv 32 := 0xfec698e3.
Lemma D_78938 : decode_any W_78938 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7893c : bv 32 := 0x00008067.
Lemma D_7893c : decode_any W_7893c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78998 : bv 32 := 0x00a666b3.
Lemma D_78998 : decode_any W_78998 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7899c : bv 32 := 0x00f6f693.
Lemma D_7899c : decode_any W_7899c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789a0 : bv 32 := 0x02068063.
Lemma D_789a0 : decode_any W_789a0 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789a4 : bv 32 := 0x04060863.
Lemma D_789a4 : decode_any W_789a4 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789a8 : bv 32 := 0x00c50633.
Lemma D_789a8 : decode_any W_789a8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789ac : bv 32 := 0x00050693.
Lemma D_789ac : decode_any W_789ac = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789b0 : bv 32 := 0x00b68023.
Lemma D_789b0 : decode_any W_789b0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789b4 : bv 32 := 0x00168693.
Lemma D_789b4 : decode_any W_789b4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789b8 : bv 32 := 0xfec69ce3.
Lemma D_789b8 : decode_any W_789b8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789bc : bv 32 := 0x0380006f.
Lemma D_789bc : decode_any W_789bc = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789c0 : bv 32 := 0x02060a63.
Lemma D_789c0 : decode_any W_789c0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789c4 : bv 32 := 0x00c50633.
Lemma D_789c4 : decode_any W_789c4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789c8 : bv 32 := 0x00859693.
Lemma D_789c8 : decode_any W_789c8 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789cc : bv 32 := 0x00b6e5b3.
Lemma D_789cc : decode_any W_789cc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789d0 : bv 32 := 0x01059693.
Lemma D_789d0 : decode_any W_789d0 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789d4 : bv 32 := 0x00b6e5b3.
Lemma D_789d4 : decode_any W_789d4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789d8 : bv 32 := 0x02059693.
Lemma D_789d8 : decode_any W_789d8 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789dc : bv 32 := 0x00b6e5b3.
Lemma D_789dc : decode_any W_789dc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789e0 : bv 32 := 0x00050693.
Lemma D_789e0 : decode_any W_789e0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789e4 : bv 32 := 0x00b6b023.
Lemma D_789e4 : decode_any W_789e4 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789e8 : bv 32 := 0x00b6b423.
Lemma D_789e8 : decode_any W_789e8 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789ec : bv 32 := 0x01068693.
Lemma D_789ec : decode_any W_789ec = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789f0 : bv 32 := 0xfec6eae3.
Lemma D_789f0 : decode_any W_789f0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789f4 : bv 32 := 0x00008067.
Lemma D_789f4 : decode_any W_789f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ec8 : bv 32 := 0xff010113.
Lemma D_78ec8 : decode_any W_78ec8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ecc : bv 32 := 0x00113423.
Lemma D_78ecc : decode_any W_78ecc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ed0 : bv 32 := 0x00058693.
Lemma D_78ed0 : decode_any W_78ed0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ed4 : bv 32 := 0x00100713.
Lemma D_78ed4 : decode_any W_78ed4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ed8 : bv 32 := 0x02871713.
Lemma D_78ed8 : decode_any W_78ed8 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78edc : bv 32 := 0x00170593.
Lemma D_78edc : decode_any W_78edc = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ee0 : bv 32 := 0x08b6f263.
Lemma D_78ee0 : decode_any W_78ee0 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ee4 : bv 32 := 0x00000593.
Lemma D_78ee4 : decode_any W_78ee4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ee8 : bv 32 := 0x00d50733.
Lemma D_78ee8 : decode_any W_78ee8 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78eec : bv 32 := 0x00750793.
Lemma D_78eec : decode_any W_78eec = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ef0 : bv 32 := 0xff87f793.
Lemma D_78ef0 : decode_any W_78ef0 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ef4 : bv 32 := 0xff877613.
Lemma D_78ef4 : decode_any W_78ef4 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ef8 : bv 32 := 0x02f57463.
Lemma D_78ef8 : decode_any W_78ef8 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78efc : bv 32 := 0x02068263.
Lemma D_78efc : decode_any W_78efc = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f00 : bv 32 := 0x00000593.
Lemma D_78f00 : decode_any W_78f00 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f04 : bv 32 := 0x00150693.
Lemma D_78f04 : decode_any W_78f04 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f08 : bv 32 := 0x00068813.
Lemma D_78f08 : decode_any W_78f08 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f0c : bv 32 := 0xfff6c683.
Lemma D_78f0c : decode_any W_78f0c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f10 : bv 32 := 0x00d5e5b3.
Lemma D_78f10 : decode_any W_78f10 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f14 : bv 32 := 0x00f87663.
Lemma D_78f14 : decode_any W_78f14 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f18 : bv 32 := 0x00180693.
Lemma D_78f18 : decode_any W_78f18 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f1c : bv 32 := 0xfee866e3.
Lemma D_78f1c : decode_any W_78f1c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f20 : bv 32 := 0x00c7fa63.
Lemma D_78f20 : decode_any W_78f20 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f24 : bv 32 := 0x0007b683.
Lemma D_78f24 : decode_any W_78f24 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f28 : bv 32 := 0x00878793.
Lemma D_78f28 : decode_any W_78f28 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f2c : bv 32 := 0x00b6e5b3.
Lemma D_78f2c : decode_any W_78f2c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f30 : bv 32 := 0xfec7eae3.
Lemma D_78f30 : decode_any W_78f30 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f34 : bv 32 := 0x02a66063.
Lemma D_78f34 : decode_any W_78f34 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f38 : bv 32 := 0x00e67e63.
Lemma D_78f38 : decode_any W_78f38 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f3c : bv 32 := 0x40c70733.
Lemma D_78f3c : decode_any W_78f3c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f40 : bv 32 := 0x00064503.
Lemma D_78f40 : decode_any W_78f40 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f44 : bv 32 := 0xfff70713.
Lemma D_78f44 : decode_any W_78f44 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f48 : bv 32 := 0x00a5e5b3.
Lemma D_78f48 : decode_any W_78f48 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f4c : bv 32 := 0x00160613.
Lemma D_78f4c : decode_any W_78f4c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f50 : bv 32 := 0xfe0718e3.
Lemma D_78f50 : decode_any W_78f50 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f54 : bv 32 := 0x0015b513.
Lemma D_78f54 : decode_any W_78f54 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f58 : bv 32 := 0x00813083.
Lemma D_78f58 : decode_any W_78f58 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f5c : bv 32 := 0x01010113.
Lemma D_78f5c : decode_any W_78f5c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78f60 : bv 32 := 0x00008067.
Lemma D_78f60 : decode_any W_78f60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
