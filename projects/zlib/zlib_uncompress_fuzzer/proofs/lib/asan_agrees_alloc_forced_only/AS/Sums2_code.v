(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_70154 : bv 32 := 0x06060663.
Lemma D_70154 : decode_any W_70154 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_70158 : bv 32 := 0x00000693.
Lemma D_70158 : decode_any W_70158 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7015c : bv 32 := 0x00d58733.
Lemma D_7015c : decode_any W_7015c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70160 : bv 32 := 0x00074703.
Lemma D_70160 : decode_any W_70160 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70164 : bv 32 := 0x00070c63.
Lemma D_70164 : decode_any W_70164 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_70168 : bv 32 := 0x00d507b3.
Lemma D_70168 : decode_any W_70168 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7016c : bv 32 := 0x00168693.
Lemma D_7016c : decode_any W_7016c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70170 : bv 32 := 0x00e78023.
Lemma D_70170 : decode_any W_70170 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70174 : bv 32 := 0xfed614e3.
Lemma D_70174 : decode_any W_70174 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_70178 : bv 32 := 0x00060693.
Lemma D_70178 : decode_any W_70178 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7017c : bv 32 := 0x00d505b3.
Lemma D_7017c : decode_any W_7017c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70180 : bv 32 := 0x40d6073b.
Lemma D_70180 : decode_any W_70180 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70184 : bv 32 := 0x00b76733.
Lemma D_70184 : decode_any W_70184 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70188 : bv 32 := 0x00f77713.
Lemma D_70188 : decode_any W_70188 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7018c : bv 32 := 0x00070e63.
Lemma D_7018c : decode_any W_7018c = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70190 : bv 32 := 0x02d60863.
Lemma D_70190 : decode_any W_70190 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_70194 : bv 32 := 0x00c50633.
Lemma D_70194 : decode_any W_70194 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70198 : bv 32 := 0x00058023.
Lemma D_70198 : decode_any W_70198 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7019c : bv 32 := 0x00158593.
Lemma D_7019c : decode_any W_7019c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_701a0 : bv 32 := 0xfec59ce3.
Lemma D_701a0 : decode_any W_701a0 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_701a4 : bv 32 := 0x01c0006f.
Lemma D_701a4 : decode_any W_701a4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_701a8 : bv 32 := 0x00d60c63.
Lemma D_701a8 : decode_any W_701a8 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_701ac : bv 32 := 0x00c50633.
Lemma D_701ac : decode_any W_701ac = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_701b0 : bv 32 := 0x0005b023.
Lemma D_701b0 : decode_any W_701b0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_701b4 : bv 32 := 0x0005b423.
Lemma D_701b4 : decode_any W_701b4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_701b8 : bv 32 := 0x01058593.
Lemma D_701b8 : decode_any W_701b8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_701bc : bv 32 := 0xfec5eae3.
Lemma D_701bc : decode_any W_701bc = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_701c0 : bv 32 := 0x00008067.
Lemma D_701c0 : decode_any W_701c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



Definition W_5cca4 : bv 32 := 0x00200613.
Lemma D_5cca4 : decode_any W_5cca4 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cca8 : bv 32 := 0x14c5ea63.
Lemma D_5cca8 : decode_any W_5cca8 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccac : bv 32 := 0x00100613.
Lemma D_5ccac : decode_any W_5ccac = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccb0 : bv 32 := 0x00100693.
Lemma D_5ccb0 : decode_any W_5ccb0 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccb4 : bv 32 := 0x00c0006f.
Lemma D_5ccb4 : decode_any W_5ccb4 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccb8 : bv 32 := 0x00160613.
Lemma D_5ccb8 : decode_any W_5ccb8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccbc : bv 32 := 0x12b60c63.
Lemma D_5ccbc : decode_any W_5ccbc = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccc0 : bv 32 := 0x00461713.
Lemma D_5ccc0 : decode_any W_5ccc0 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccc4 : bv 32 := 0x00e50733.
Lemma D_5ccc4 : decode_any W_5ccc4 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccc8 : bv 32 := 0x00072703.
Lemma D_5ccc8 : decode_any W_5ccc8 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cccc : bv 32 := 0x00060893.
Lemma D_5cccc : decode_any W_5cccc = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccd0 : bv 32 := 0xfff88793.
Lemma D_5ccd0 : decode_any W_5ccd0 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccd4 : bv 32 := 0x0017d813.
Lemma D_5ccd4 : decode_any W_5ccd4 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccd8 : bv 32 := 0x00481293.
Lemma D_5ccd8 : decode_any W_5ccd8 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccdc : bv 32 := 0x005502b3.
Lemma D_5ccdc : decode_any W_5ccdc = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cce0 : bv 32 := 0x0002a303.
Lemma D_5cce0 : decode_any W_5cce0 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cce4 : bv 32 := 0xfce37ae3.
Lemma D_5cce4 : decode_any W_5cce4 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cce8 : bv 32 := 0x0002b303.
Lemma D_5cce8 : decode_any W_5cce8 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccec : bv 32 := 0x00489893.
Lemma D_5ccec : decode_any W_5ccec = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccf0 : bv 32 := 0x011508b3.
Lemma D_5ccf0 : decode_any W_5ccf0 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccf4 : bv 32 := 0x0048a383.
Lemma D_5ccf4 : decode_any W_5ccf4 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccf8 : bv 32 := 0x0068b023.
Lemma D_5ccf8 : decode_any W_5ccf8 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ccfc : bv 32 := 0x0082b303.
Lemma D_5ccfc : decode_any W_5ccfc = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd00 : bv 32 := 0x0088be03.
Lemma D_5cd00 : decode_any W_5cd00 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd04 : bv 32 := 0x0068b423.
Lemma D_5cd04 : decode_any W_5cd04 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd08 : bv 32 := 0x00e2a023.
Lemma D_5cd08 : decode_any W_5cd08 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd0c : bv 32 := 0x0072a223.
Lemma D_5cd0c : decode_any W_5cd0c = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd10 : bv 32 := 0x01c2b423.
Lemma D_5cd10 : decode_any W_5cd10 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd14 : bv 32 := 0x00080893.
Lemma D_5cd14 : decode_any W_5cd14 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd18 : bv 32 := 0xfaf6ece3.
Lemma D_5cd18 : decode_any W_5cd18 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd1c : bv 32 := 0xf9dff06f.
Lemma D_5cd1c : decode_any W_5cd1c = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd20 : bv 32 := 0x00000613.
Lemma D_5cd20 : decode_any W_5cd20 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd24 : bv 32 := 0x00459693.
Lemma D_5cd24 : decode_any W_5cd24 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd28 : bv 32 := 0x00d506b3.
Lemma D_5cd28 : decode_any W_5cd28 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd2c : bv 32 := 0x0006b703.
Lemma D_5cd2c : decode_any W_5cd2c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd30 : bv 32 := 0x0086b783.
Lemma D_5cd30 : decode_any W_5cd30 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd34 : bv 32 := 0x00053803.
Lemma D_5cd34 : decode_any W_5cd34 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd38 : bv 32 := 0x00853883.
Lemma D_5cd38 : decode_any W_5cd38 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd3c : bv 32 := 0x00e53023.
Lemma D_5cd3c : decode_any W_5cd3c = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd40 : bv 32 := 0x00f53423.
Lemma D_5cd40 : decode_any W_5cd40 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd44 : bv 32 := 0x0106b023.
Lemma D_5cd44 : decode_any W_5cd44 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd48 : bv 32 := 0x0116b423.
Lemma D_5cd48 : decode_any W_5cd48 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd4c : bv 32 := 0x00000693.
Lemma D_5cd4c : decode_any W_5cd4c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd50 : bv 32 := 0x00161793.
Lemma D_5cd50 : decode_any W_5cd50 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd54 : bv 32 := 0x00178813.
Lemma D_5cd54 : decode_any W_5cd54 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd58 : bv 32 := 0x00461713.
Lemma D_5cd58 : decode_any W_5cd58 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd5c : bv 32 := 0x00b86a63.
Lemma D_5cd5c : decode_any W_5cd5c = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd60 : bv 32 := 0x00278793.
Lemma D_5cd60 : decode_any W_5cd60 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd64 : bv 32 := 0x02b7ea63.
Lemma D_5cd64 : decode_any W_5cd64 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd68 : bv 32 := 0x04c69c63.
Lemma D_5cd68 : decode_any W_5cd68 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd6c : bv 32 := 0x0880006f.
Lemma D_5cd6c : decode_any W_5cd6c = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd70 : bv 32 := 0x00e506b3.
Lemma D_5cd70 : decode_any W_5cd70 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd74 : bv 32 := 0x00481893.
Lemma D_5cd74 : decode_any W_5cd74 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd78 : bv 32 := 0x011508b3.
Lemma D_5cd78 : decode_any W_5cd78 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd7c : bv 32 := 0x0006a683.
Lemma D_5cd7c : decode_any W_5cd7c = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd80 : bv 32 := 0x0008a883.
Lemma D_5cd80 : decode_any W_5cd80 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd84 : bv 32 := 0x0116e463.
Lemma D_5cd84 : decode_any W_5cd84 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd88 : bv 32 := 0x00060813.
Lemma D_5cd88 : decode_any W_5cd88 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd8c : bv 32 := 0x00080693.
Lemma D_5cd8c : decode_any W_5cd8c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd90 : bv 32 := 0x00278793.
Lemma D_5cd90 : decode_any W_5cd90 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd94 : bv 32 := 0xfcb7fae3.
Lemma D_5cd94 : decode_any W_5cd94 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd98 : bv 32 := 0x00469813.
Lemma D_5cd98 : decode_any W_5cd98 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd9c : bv 32 := 0x00479893.
Lemma D_5cd9c : decode_any W_5cd9c = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cda0 : bv 32 := 0x01050833.
Lemma D_5cda0 : decode_any W_5cda0 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cda4 : bv 32 := 0x011508b3.
Lemma D_5cda4 : decode_any W_5cda4 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cda8 : bv 32 := 0x00082803.
Lemma D_5cda8 : decode_any W_5cda8 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdac : bv 32 := 0x0008a883.
Lemma D_5cdac : decode_any W_5cdac = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdb0 : bv 32 := 0x01186463.
Lemma D_5cdb0 : decode_any W_5cdb0 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdb4 : bv 32 := 0x00068793.
Lemma D_5cdb4 : decode_any W_5cdb4 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdb8 : bv 32 := 0x00078693.
Lemma D_5cdb8 : decode_any W_5cdb8 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdbc : bv 32 := 0x02c78c63.
Lemma D_5cdbc : decode_any W_5cdbc = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdc0 : bv 32 := 0x00469613.
Lemma D_5cdc0 : decode_any W_5cdc0 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdc4 : bv 32 := 0x00c50633.
Lemma D_5cdc4 : decode_any W_5cdc4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdc8 : bv 32 := 0x00063783.
Lemma D_5cdc8 : decode_any W_5cdc8 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdcc : bv 32 := 0x00e50733.
Lemma D_5cdcc : decode_any W_5cdcc = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdd0 : bv 32 := 0x00073803.
Lemma D_5cdd0 : decode_any W_5cdd0 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdd4 : bv 32 := 0x00873883.
Lemma D_5cdd4 : decode_any W_5cdd4 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdd8 : bv 32 := 0x00f73023.
Lemma D_5cdd8 : decode_any W_5cdd8 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cddc : bv 32 := 0x00863783.
Lemma D_5cddc : decode_any W_5cddc = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cde0 : bv 32 := 0x00f73423.
Lemma D_5cde0 : decode_any W_5cde0 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cde4 : bv 32 := 0x01063023.
Lemma D_5cde4 : decode_any W_5cde4 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cde8 : bv 32 := 0x01163423.
Lemma D_5cde8 : decode_any W_5cde8 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdec : bv 32 := 0x00068613.
Lemma D_5cdec : decode_any W_5cdec = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdf0 : bv 32 := 0xf6b6e0e3.
Lemma D_5cdf0 : decode_any W_5cdf0 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdf4 : bv 32 := 0xfff58593.
Lemma D_5cdf4 : decode_any W_5cdf4 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdf8 : bv 32 := 0xf20594e3.
Lemma D_5cdf8 : decode_any W_5cdf8 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdfc : bv 32 := 0x00008067.
Lemma D_5cdfc : decode_any W_5cdfc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
