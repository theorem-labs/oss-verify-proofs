(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_638a4 : bv 32 := 0x02060063.
Lemma D_638a4 : decode_any W_638a4 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_638a8 : bv 32 := 0x00c50633.
Lemma D_638a8 : decode_any W_638a8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_638ac : bv 32 := 0x00050693.
Lemma D_638ac : decode_any W_638ac = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_638b0 : bv 32 := 0x0005c703.
Lemma D_638b0 : decode_any W_638b0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_638b4 : bv 32 := 0x00e68023.
Lemma D_638b4 : decode_any W_638b4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_638b8 : bv 32 := 0x00168693.
Lemma D_638b8 : decode_any W_638b8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_638bc : bv 32 := 0x00158593.
Lemma D_638bc : decode_any W_638bc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_638c0 : bv 32 := 0xfec698e3.
Lemma D_638c0 : decode_any W_638c0 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_638c4 : bv 32 := 0x00008067.
Lemma D_638c4 : decode_any W_638c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63920 : bv 32 := 0x00a666b3.
Lemma D_63920 : decode_any W_63920 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_63924 : bv 32 := 0x00f6f693.
Lemma D_63924 : decode_any W_63924 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_63928 : bv 32 := 0x02068063.
Lemma D_63928 : decode_any W_63928 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6392c : bv 32 := 0x04060863.
Lemma D_6392c : decode_any W_6392c = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_63930 : bv 32 := 0x00c50633.
Lemma D_63930 : decode_any W_63930 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_63934 : bv 32 := 0x00050693.
Lemma D_63934 : decode_any W_63934 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63938 : bv 32 := 0x00b68023.
Lemma D_63938 : decode_any W_63938 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6393c : bv 32 := 0x00168693.
Lemma D_6393c : decode_any W_6393c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63940 : bv 32 := 0xfec69ce3.
Lemma D_63940 : decode_any W_63940 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_63944 : bv 32 := 0x0380006f.
Lemma D_63944 : decode_any W_63944 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_63948 : bv 32 := 0x02060a63.
Lemma D_63948 : decode_any W_63948 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_6394c : bv 32 := 0x00c50633.
Lemma D_6394c : decode_any W_6394c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_63950 : bv 32 := 0x00859693.
Lemma D_63950 : decode_any W_63950 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63954 : bv 32 := 0x00b6e5b3.
Lemma D_63954 : decode_any W_63954 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_63958 : bv 32 := 0x01059693.
Lemma D_63958 : decode_any W_63958 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6395c : bv 32 := 0x00b6e5b3.
Lemma D_6395c : decode_any W_6395c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_63960 : bv 32 := 0x02059693.
Lemma D_63960 : decode_any W_63960 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_63964 : bv 32 := 0x00b6e5b3.
Lemma D_63964 : decode_any W_63964 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_63968 : bv 32 := 0x00050693.
Lemma D_63968 : decode_any W_63968 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6396c : bv 32 := 0x00b6b023.
Lemma D_6396c : decode_any W_6396c = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63970 : bv 32 := 0x00b6b423.
Lemma D_63970 : decode_any W_63970 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63974 : bv 32 := 0x01068693.
Lemma D_63974 : decode_any W_63974 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_63978 : bv 32 := 0xfec6eae3.
Lemma D_63978 : decode_any W_63978 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6397c : bv 32 := 0x00008067.
Lemma D_6397c : decode_any W_6397c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e50 : bv 32 := 0xff010113.
Lemma D_63e50 : decode_any W_63e50 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e54 : bv 32 := 0x00113423.
Lemma D_63e54 : decode_any W_63e54 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e58 : bv 32 := 0x00058693.
Lemma D_63e58 : decode_any W_63e58 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e5c : bv 32 := 0x00100713.
Lemma D_63e5c : decode_any W_63e5c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e60 : bv 32 := 0x02871713.
Lemma D_63e60 : decode_any W_63e60 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e64 : bv 32 := 0x00170593.
Lemma D_63e64 : decode_any W_63e64 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e68 : bv 32 := 0x08b6f263.
Lemma D_63e68 : decode_any W_63e68 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e6c : bv 32 := 0x00000593.
Lemma D_63e6c : decode_any W_63e6c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e70 : bv 32 := 0x00d50733.
Lemma D_63e70 : decode_any W_63e70 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e74 : bv 32 := 0x00750793.
Lemma D_63e74 : decode_any W_63e74 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e78 : bv 32 := 0xff87f793.
Lemma D_63e78 : decode_any W_63e78 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e7c : bv 32 := 0xff877613.
Lemma D_63e7c : decode_any W_63e7c = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e80 : bv 32 := 0x02f57463.
Lemma D_63e80 : decode_any W_63e80 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e84 : bv 32 := 0x02068263.
Lemma D_63e84 : decode_any W_63e84 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e88 : bv 32 := 0x00000593.
Lemma D_63e88 : decode_any W_63e88 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e8c : bv 32 := 0x00150693.
Lemma D_63e8c : decode_any W_63e8c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e90 : bv 32 := 0x00068813.
Lemma D_63e90 : decode_any W_63e90 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e94 : bv 32 := 0xfff6c683.
Lemma D_63e94 : decode_any W_63e94 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e98 : bv 32 := 0x00d5e5b3.
Lemma D_63e98 : decode_any W_63e98 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e9c : bv 32 := 0x00f87663.
Lemma D_63e9c : decode_any W_63e9c = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ea0 : bv 32 := 0x00180693.
Lemma D_63ea0 : decode_any W_63ea0 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ea4 : bv 32 := 0xfee866e3.
Lemma D_63ea4 : decode_any W_63ea4 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ea8 : bv 32 := 0x00c7fa63.
Lemma D_63ea8 : decode_any W_63ea8 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_63eac : bv 32 := 0x0007b683.
Lemma D_63eac : decode_any W_63eac = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63eb0 : bv 32 := 0x00878793.
Lemma D_63eb0 : decode_any W_63eb0 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63eb4 : bv 32 := 0x00b6e5b3.
Lemma D_63eb4 : decode_any W_63eb4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_63eb8 : bv 32 := 0xfec7eae3.
Lemma D_63eb8 : decode_any W_63eb8 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ebc : bv 32 := 0x02a66063.
Lemma D_63ebc : decode_any W_63ebc = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ec0 : bv 32 := 0x00e67e63.
Lemma D_63ec0 : decode_any W_63ec0 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ec4 : bv 32 := 0x40c70733.
Lemma D_63ec4 : decode_any W_63ec4 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ec8 : bv 32 := 0x00064503.
Lemma D_63ec8 : decode_any W_63ec8 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ecc : bv 32 := 0xfff70713.
Lemma D_63ecc : decode_any W_63ecc = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ed0 : bv 32 := 0x00a5e5b3.
Lemma D_63ed0 : decode_any W_63ed0 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ed4 : bv 32 := 0x00160613.
Lemma D_63ed4 : decode_any W_63ed4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ed8 : bv 32 := 0xfe0718e3.
Lemma D_63ed8 : decode_any W_63ed8 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_63edc : bv 32 := 0x0015b513.
Lemma D_63edc : decode_any W_63edc = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ee0 : bv 32 := 0x00813083.
Lemma D_63ee0 : decode_any W_63ee0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ee4 : bv 32 := 0x01010113.
Lemma D_63ee4 : decode_any W_63ee4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ee8 : bv 32 := 0x00008067.
Lemma D_63ee8 : decode_any W_63ee8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
