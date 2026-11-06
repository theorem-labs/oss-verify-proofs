(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_642ec : bv 32 := 0x02060063.
Lemma D_642ec : decode_any W_642ec = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_642f0 : bv 32 := 0x00c50633.
Lemma D_642f0 : decode_any W_642f0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_642f4 : bv 32 := 0x00050693.
Lemma D_642f4 : decode_any W_642f4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_642f8 : bv 32 := 0x0005c703.
Lemma D_642f8 : decode_any W_642f8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_642fc : bv 32 := 0x00e68023.
Lemma D_642fc : decode_any W_642fc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_64300 : bv 32 := 0x00168693.
Lemma D_64300 : decode_any W_64300 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_64304 : bv 32 := 0x00158593.
Lemma D_64304 : decode_any W_64304 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_64308 : bv 32 := 0xfec698e3.
Lemma D_64308 : decode_any W_64308 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.
Definition W_6430c : bv 32 := 0x00008067.
Lemma D_6430c : decode_any W_6430c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_64368 : bv 32 := 0x00a666b3.
Lemma D_64368 : decode_any W_64368 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_6436c : bv 32 := 0x00f6f693.
Lemma D_6436c : decode_any W_6436c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_64370 : bv 32 := 0x02068063.
Lemma D_64370 : decode_any W_64370 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_64374 : bv 32 := 0x04060863.
Lemma D_64374 : decode_any W_64374 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.
Definition W_64378 : bv 32 := 0x00c50633.
Lemma D_64378 : decode_any W_64378 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_6437c : bv 32 := 0x00050693.
Lemma D_6437c : decode_any W_6437c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_64380 : bv 32 := 0x00b68023.
Lemma D_64380 : decode_any W_64380 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_64384 : bv 32 := 0x00168693.
Lemma D_64384 : decode_any W_64384 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_64388 : bv 32 := 0xfec69ce3.
Lemma D_64388 : decode_any W_64388 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.
Definition W_6438c : bv 32 := 0x0380006f.
Lemma D_6438c : decode_any W_6438c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.
Definition W_64390 : bv 32 := 0x02060a63.
Lemma D_64390 : decode_any W_64390 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.
Definition W_64394 : bv 32 := 0x00c50633.
Lemma D_64394 : decode_any W_64394 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_64398 : bv 32 := 0x00859693.
Lemma D_64398 : decode_any W_64398 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_6439c : bv 32 := 0x00b6e5b3.
Lemma D_6439c : decode_any W_6439c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_643a0 : bv 32 := 0x01059693.
Lemma D_643a0 : decode_any W_643a0 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_643a4 : bv 32 := 0x00b6e5b3.
Lemma D_643a4 : decode_any W_643a4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_643a8 : bv 32 := 0x02059693.
Lemma D_643a8 : decode_any W_643a8 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_643ac : bv 32 := 0x00b6e5b3.
Lemma D_643ac : decode_any W_643ac = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_643b0 : bv 32 := 0x00050693.
Lemma D_643b0 : decode_any W_643b0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_643b4 : bv 32 := 0x00b6b023.
Lemma D_643b4 : decode_any W_643b4 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_643b8 : bv 32 := 0x00b6b423.
Lemma D_643b8 : decode_any W_643b8 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_643bc : bv 32 := 0x01068693.
Lemma D_643bc : decode_any W_643bc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_643c0 : bv 32 := 0xfec6eae3.
Lemma D_643c0 : decode_any W_643c0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.
Definition W_643c4 : bv 32 := 0x00008067.
Lemma D_643c4 : decode_any W_643c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_64898 : bv 32 := 0xff010113.
Lemma D_64898 : decode_any W_64898 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_6489c : bv 32 := 0x00113423.
Lemma D_6489c : decode_any W_6489c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_648a0 : bv 32 := 0x00058693.
Lemma D_648a0 : decode_any W_648a0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_648a4 : bv 32 := 0x00100713.
Lemma D_648a4 : decode_any W_648a4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_648a8 : bv 32 := 0x02871713.
Lemma D_648a8 : decode_any W_648a8 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.
Definition W_648ac : bv 32 := 0x00170593.
Lemma D_648ac : decode_any W_648ac = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_648b0 : bv 32 := 0x08b6f263.
Lemma D_648b0 : decode_any W_648b0 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.
Definition W_648b4 : bv 32 := 0x00000593.
Lemma D_648b4 : decode_any W_648b4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_648b8 : bv 32 := 0x00d50733.
Lemma D_648b8 : decode_any W_648b8 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_648bc : bv 32 := 0x00750793.
Lemma D_648bc : decode_any W_648bc = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_648c0 : bv 32 := 0xff87f793.
Lemma D_648c0 : decode_any W_648c0 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_648c4 : bv 32 := 0xff877613.
Lemma D_648c4 : decode_any W_648c4 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_648c8 : bv 32 := 0x02f57463.
Lemma D_648c8 : decode_any W_648c8 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.
Definition W_648cc : bv 32 := 0x02068263.
Lemma D_648cc : decode_any W_648cc = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.
Definition W_648d0 : bv 32 := 0x00000593.
Lemma D_648d0 : decode_any W_648d0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_648d4 : bv 32 := 0x00150693.
Lemma D_648d4 : decode_any W_648d4 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_648d8 : bv 32 := 0x00068813.
Lemma D_648d8 : decode_any W_648d8 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_648dc : bv 32 := 0xfff6c683.
Lemma D_648dc : decode_any W_648dc = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_648e0 : bv 32 := 0x00d5e5b3.
Lemma D_648e0 : decode_any W_648e0 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_648e4 : bv 32 := 0x00f87663.
Lemma D_648e4 : decode_any W_648e4 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_648e8 : bv 32 := 0x00180693.
Lemma D_648e8 : decode_any W_648e8 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_648ec : bv 32 := 0xfee866e3.
Lemma D_648ec : decode_any W_648ec = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.
Definition W_648f0 : bv 32 := 0x00c7fa63.
Lemma D_648f0 : decode_any W_648f0 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.
Definition W_648f4 : bv 32 := 0x0007b683.
Lemma D_648f4 : decode_any W_648f4 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_648f8 : bv 32 := 0x00878793.
Lemma D_648f8 : decode_any W_648f8 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_648fc : bv 32 := 0x00b6e5b3.
Lemma D_648fc : decode_any W_648fc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_64900 : bv 32 := 0xfec7eae3.
Lemma D_64900 : decode_any W_64900 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.
Definition W_64904 : bv 32 := 0x02a66063.
Lemma D_64904 : decode_any W_64904 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_64908 : bv 32 := 0x00e67e63.
Lemma D_64908 : decode_any W_64908 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.
Definition W_6490c : bv 32 := 0x40c70733.
Lemma D_6490c : decode_any W_6490c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_64910 : bv 32 := 0x00064503.
Lemma D_64910 : decode_any W_64910 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_64914 : bv 32 := 0xfff70713.
Lemma D_64914 : decode_any W_64914 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_64918 : bv 32 := 0x00a5e5b3.
Lemma D_64918 : decode_any W_64918 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_6491c : bv 32 := 0x00160613.
Lemma D_6491c : decode_any W_6491c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_64920 : bv 32 := 0xfe0718e3.
Lemma D_64920 : decode_any W_64920 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.
Definition W_64924 : bv 32 := 0x0015b513.
Lemma D_64924 : decode_any W_64924 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_64928 : bv 32 := 0x00813083.
Lemma D_64928 : decode_any W_64928 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_6492c : bv 32 := 0x01010113.
Lemma D_6492c : decode_any W_6492c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_64930 : bv 32 := 0x00008067.
Lemma D_64930 : decode_any W_64930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
