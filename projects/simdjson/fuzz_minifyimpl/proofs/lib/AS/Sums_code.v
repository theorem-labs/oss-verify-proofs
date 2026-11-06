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
Definition W_94288 : bv 32 := 0x02060063.
Lemma D_94288 : decode_any W_94288 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9428c : bv 32 := 0x00c50633.
Lemma D_9428c : decode_any W_9428c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94290 : bv 32 := 0x00050693.
Lemma D_94290 : decode_any W_94290 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94294 : bv 32 := 0x0005c703.
Lemma D_94294 : decode_any W_94294 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94298 : bv 32 := 0x00e68023.
Lemma D_94298 : decode_any W_94298 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9429c : bv 32 := 0x00168693.
Lemma D_9429c : decode_any W_9429c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942a0 : bv 32 := 0x00158593.
Lemma D_942a0 : decode_any W_942a0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942a4 : bv 32 := 0xfec698e3.
Lemma D_942a4 : decode_any W_942a4 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942a8 : bv 32 := 0x00008067.
Lemma D_942a8 : decode_any W_942a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94304 : bv 32 := 0x00a666b3.
Lemma D_94304 : decode_any W_94304 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94308 : bv 32 := 0x00f6f693.
Lemma D_94308 : decode_any W_94308 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9430c : bv 32 := 0x02068063.
Lemma D_9430c : decode_any W_9430c = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94310 : bv 32 := 0x04060863.
Lemma D_94310 : decode_any W_94310 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94314 : bv 32 := 0x00c50633.
Lemma D_94314 : decode_any W_94314 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94318 : bv 32 := 0x00050693.
Lemma D_94318 : decode_any W_94318 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9431c : bv 32 := 0x00b68023.
Lemma D_9431c : decode_any W_9431c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94320 : bv 32 := 0x00168693.
Lemma D_94320 : decode_any W_94320 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94324 : bv 32 := 0xfec69ce3.
Lemma D_94324 : decode_any W_94324 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94328 : bv 32 := 0x0380006f.
Lemma D_94328 : decode_any W_94328 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9432c : bv 32 := 0x02060a63.
Lemma D_9432c : decode_any W_9432c = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94330 : bv 32 := 0x00c50633.
Lemma D_94330 : decode_any W_94330 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94334 : bv 32 := 0x00859693.
Lemma D_94334 : decode_any W_94334 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94338 : bv 32 := 0x00b6e5b3.
Lemma D_94338 : decode_any W_94338 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9433c : bv 32 := 0x01059693.
Lemma D_9433c : decode_any W_9433c = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94340 : bv 32 := 0x00b6e5b3.
Lemma D_94340 : decode_any W_94340 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94344 : bv 32 := 0x02059693.
Lemma D_94344 : decode_any W_94344 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94348 : bv 32 := 0x00b6e5b3.
Lemma D_94348 : decode_any W_94348 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9434c : bv 32 := 0x00050693.
Lemma D_9434c : decode_any W_9434c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94350 : bv 32 := 0x00b6b023.
Lemma D_94350 : decode_any W_94350 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94354 : bv 32 := 0x00b6b423.
Lemma D_94354 : decode_any W_94354 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94358 : bv 32 := 0x01068693.
Lemma D_94358 : decode_any W_94358 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9435c : bv 32 := 0xfec6eae3.
Lemma D_9435c : decode_any W_9435c = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94360 : bv 32 := 0x00008067.
Lemma D_94360 : decode_any W_94360 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94850 : bv 32 := 0xff010113.
Lemma D_94850 : decode_any W_94850 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94854 : bv 32 := 0x00113423.
Lemma D_94854 : decode_any W_94854 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94858 : bv 32 := 0x00058693.
Lemma D_94858 : decode_any W_94858 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9485c : bv 32 := 0x00100713.
Lemma D_9485c : decode_any W_9485c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94860 : bv 32 := 0x02871713.
Lemma D_94860 : decode_any W_94860 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94864 : bv 32 := 0x00170593.
Lemma D_94864 : decode_any W_94864 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94868 : bv 32 := 0x08b6f263.
Lemma D_94868 : decode_any W_94868 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9486c : bv 32 := 0x00000593.
Lemma D_9486c : decode_any W_9486c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94870 : bv 32 := 0x00d50733.
Lemma D_94870 : decode_any W_94870 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94874 : bv 32 := 0x00750793.
Lemma D_94874 : decode_any W_94874 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94878 : bv 32 := 0xff87f793.
Lemma D_94878 : decode_any W_94878 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9487c : bv 32 := 0xff877613.
Lemma D_9487c : decode_any W_9487c = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94880 : bv 32 := 0x02f57463.
Lemma D_94880 : decode_any W_94880 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94884 : bv 32 := 0x02068263.
Lemma D_94884 : decode_any W_94884 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94888 : bv 32 := 0x00000593.
Lemma D_94888 : decode_any W_94888 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9488c : bv 32 := 0x00150693.
Lemma D_9488c : decode_any W_9488c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94890 : bv 32 := 0x00068813.
Lemma D_94890 : decode_any W_94890 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94894 : bv 32 := 0xfff6c683.
Lemma D_94894 : decode_any W_94894 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94898 : bv 32 := 0x00d5e5b3.
Lemma D_94898 : decode_any W_94898 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9489c : bv 32 := 0x00f87663.
Lemma D_9489c : decode_any W_9489c = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948a0 : bv 32 := 0x00180693.
Lemma D_948a0 : decode_any W_948a0 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948a4 : bv 32 := 0xfee866e3.
Lemma D_948a4 : decode_any W_948a4 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948a8 : bv 32 := 0x00c7fa63.
Lemma D_948a8 : decode_any W_948a8 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948ac : bv 32 := 0x0007b683.
Lemma D_948ac : decode_any W_948ac = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948b0 : bv 32 := 0x00878793.
Lemma D_948b0 : decode_any W_948b0 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948b4 : bv 32 := 0x00b6e5b3.
Lemma D_948b4 : decode_any W_948b4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948b8 : bv 32 := 0xfec7eae3.
Lemma D_948b8 : decode_any W_948b8 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948bc : bv 32 := 0x02a66063.
Lemma D_948bc : decode_any W_948bc = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948c0 : bv 32 := 0x00e67e63.
Lemma D_948c0 : decode_any W_948c0 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948c4 : bv 32 := 0x40c70733.
Lemma D_948c4 : decode_any W_948c4 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948c8 : bv 32 := 0x00064503.
Lemma D_948c8 : decode_any W_948c8 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948cc : bv 32 := 0xfff70713.
Lemma D_948cc : decode_any W_948cc = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948d0 : bv 32 := 0x00a5e5b3.
Lemma D_948d0 : decode_any W_948d0 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948d4 : bv 32 := 0x00160613.
Lemma D_948d4 : decode_any W_948d4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948d8 : bv 32 := 0xfe0718e3.
Lemma D_948d8 : decode_any W_948d8 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948dc : bv 32 := 0x0015b513.
Lemma D_948dc : decode_any W_948dc = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948e0 : bv 32 := 0x00813083.
Lemma D_948e0 : decode_any W_948e0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948e4 : bv 32 := 0x01010113.
Lemma D_948e4 : decode_any W_948e4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_948e8 : bv 32 := 0x00008067.
Lemma D_948e8 : decode_any W_948e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
