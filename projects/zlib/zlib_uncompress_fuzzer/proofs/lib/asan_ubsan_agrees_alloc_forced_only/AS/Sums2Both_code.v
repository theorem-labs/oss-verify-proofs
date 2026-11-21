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

Definition W_701dc : bv 32 := 0x06060663.
Lemma D_701dc : decode_any W_701dc = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_701e0 : bv 32 := 0x00000693.
Lemma D_701e0 : decode_any W_701e0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_701e4 : bv 32 := 0x00d58733.
Lemma D_701e4 : decode_any W_701e4 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_701e8 : bv 32 := 0x00074703.
Lemma D_701e8 : decode_any W_701e8 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_701ec : bv 32 := 0x00070c63.
Lemma D_701ec : decode_any W_701ec = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_701f0 : bv 32 := 0x00d507b3.
Lemma D_701f0 : decode_any W_701f0 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_701f4 : bv 32 := 0x00168693.
Lemma D_701f4 : decode_any W_701f4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_701f8 : bv 32 := 0x00e78023.
Lemma D_701f8 : decode_any W_701f8 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_701fc : bv 32 := 0xfed614e3.
Lemma D_701fc : decode_any W_701fc = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_70200 : bv 32 := 0x00060693.
Lemma D_70200 : decode_any W_70200 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70204 : bv 32 := 0x00d505b3.
Lemma D_70204 : decode_any W_70204 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70208 : bv 32 := 0x40d6073b.
Lemma D_70208 : decode_any W_70208 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7020c : bv 32 := 0x00b76733.
Lemma D_7020c : decode_any W_7020c = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70210 : bv 32 := 0x00f77713.
Lemma D_70210 : decode_any W_70210 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_70214 : bv 32 := 0x00070e63.
Lemma D_70214 : decode_any W_70214 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70218 : bv 32 := 0x02d60863.
Lemma D_70218 : decode_any W_70218 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7021c : bv 32 := 0x00c50633.
Lemma D_7021c : decode_any W_7021c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70220 : bv 32 := 0x00058023.
Lemma D_70220 : decode_any W_70220 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70224 : bv 32 := 0x00158593.
Lemma D_70224 : decode_any W_70224 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70228 : bv 32 := 0xfec59ce3.
Lemma D_70228 : decode_any W_70228 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_7022c : bv 32 := 0x01c0006f.
Lemma D_7022c : decode_any W_7022c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70230 : bv 32 := 0x00d60c63.
Lemma D_70230 : decode_any W_70230 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_70234 : bv 32 := 0x00c50633.
Lemma D_70234 : decode_any W_70234 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70238 : bv 32 := 0x0005b023.
Lemma D_70238 : decode_any W_70238 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7023c : bv 32 := 0x0005b423.
Lemma D_7023c : decode_any W_7023c = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70240 : bv 32 := 0x01058593.
Lemma D_70240 : decode_any W_70240 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_70244 : bv 32 := 0xfec5eae3.
Lemma D_70244 : decode_any W_70244 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_70248 : bv 32 := 0x00008067.
Lemma D_70248 : decode_any W_70248 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



Definition W_5cd2c : bv 32 := 0x00200613.
Lemma D_5cd2c : decode_any W_5cd2c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd30 : bv 32 := 0x14c5ea63.
Lemma D_5cd30 : decode_any W_5cd30 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd34 : bv 32 := 0x00100613.
Lemma D_5cd34 : decode_any W_5cd34 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd38 : bv 32 := 0x00100693.
Lemma D_5cd38 : decode_any W_5cd38 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd3c : bv 32 := 0x00c0006f.
Lemma D_5cd3c : decode_any W_5cd3c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd40 : bv 32 := 0x00160613.
Lemma D_5cd40 : decode_any W_5cd40 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd44 : bv 32 := 0x12b60c63.
Lemma D_5cd44 : decode_any W_5cd44 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd48 : bv 32 := 0x00461713.
Lemma D_5cd48 : decode_any W_5cd48 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd4c : bv 32 := 0x00e50733.
Lemma D_5cd4c : decode_any W_5cd4c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd50 : bv 32 := 0x00072703.
Lemma D_5cd50 : decode_any W_5cd50 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd54 : bv 32 := 0x00060893.
Lemma D_5cd54 : decode_any W_5cd54 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd58 : bv 32 := 0xfff88793.
Lemma D_5cd58 : decode_any W_5cd58 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd5c : bv 32 := 0x0017d813.
Lemma D_5cd5c : decode_any W_5cd5c = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd60 : bv 32 := 0x00481293.
Lemma D_5cd60 : decode_any W_5cd60 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd64 : bv 32 := 0x005502b3.
Lemma D_5cd64 : decode_any W_5cd64 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd68 : bv 32 := 0x0002a303.
Lemma D_5cd68 : decode_any W_5cd68 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd6c : bv 32 := 0xfce37ae3.
Lemma D_5cd6c : decode_any W_5cd6c = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd70 : bv 32 := 0x0002b303.
Lemma D_5cd70 : decode_any W_5cd70 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd74 : bv 32 := 0x00489893.
Lemma D_5cd74 : decode_any W_5cd74 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd78 : bv 32 := 0x011508b3.
Lemma D_5cd78 : decode_any W_5cd78 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd7c : bv 32 := 0x0048a383.
Lemma D_5cd7c : decode_any W_5cd7c = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd80 : bv 32 := 0x0068b023.
Lemma D_5cd80 : decode_any W_5cd80 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd84 : bv 32 := 0x0082b303.
Lemma D_5cd84 : decode_any W_5cd84 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd88 : bv 32 := 0x0088be03.
Lemma D_5cd88 : decode_any W_5cd88 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd8c : bv 32 := 0x0068b423.
Lemma D_5cd8c : decode_any W_5cd8c = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd90 : bv 32 := 0x00e2a023.
Lemma D_5cd90 : decode_any W_5cd90 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd94 : bv 32 := 0x0072a223.
Lemma D_5cd94 : decode_any W_5cd94 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd98 : bv 32 := 0x01c2b423.
Lemma D_5cd98 : decode_any W_5cd98 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cd9c : bv 32 := 0x00080893.
Lemma D_5cd9c : decode_any W_5cd9c = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cda0 : bv 32 := 0xfaf6ece3.
Lemma D_5cda0 : decode_any W_5cda0 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cda4 : bv 32 := 0xf9dff06f.
Lemma D_5cda4 : decode_any W_5cda4 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cda8 : bv 32 := 0x00000613.
Lemma D_5cda8 : decode_any W_5cda8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdac : bv 32 := 0x00459693.
Lemma D_5cdac : decode_any W_5cdac = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdb0 : bv 32 := 0x00d506b3.
Lemma D_5cdb0 : decode_any W_5cdb0 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdb4 : bv 32 := 0x0006b703.
Lemma D_5cdb4 : decode_any W_5cdb4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdb8 : bv 32 := 0x0086b783.
Lemma D_5cdb8 : decode_any W_5cdb8 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdbc : bv 32 := 0x00053803.
Lemma D_5cdbc : decode_any W_5cdbc = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdc0 : bv 32 := 0x00853883.
Lemma D_5cdc0 : decode_any W_5cdc0 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdc4 : bv 32 := 0x00e53023.
Lemma D_5cdc4 : decode_any W_5cdc4 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdc8 : bv 32 := 0x00f53423.
Lemma D_5cdc8 : decode_any W_5cdc8 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdcc : bv 32 := 0x0106b023.
Lemma D_5cdcc : decode_any W_5cdcc = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdd0 : bv 32 := 0x0116b423.
Lemma D_5cdd0 : decode_any W_5cdd0 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdd4 : bv 32 := 0x00000693.
Lemma D_5cdd4 : decode_any W_5cdd4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdd8 : bv 32 := 0x00161793.
Lemma D_5cdd8 : decode_any W_5cdd8 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cddc : bv 32 := 0x00178813.
Lemma D_5cddc : decode_any W_5cddc = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cde0 : bv 32 := 0x00461713.
Lemma D_5cde0 : decode_any W_5cde0 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cde4 : bv 32 := 0x00b86a63.
Lemma D_5cde4 : decode_any W_5cde4 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cde8 : bv 32 := 0x00278793.
Lemma D_5cde8 : decode_any W_5cde8 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdec : bv 32 := 0x02b7ea63.
Lemma D_5cdec : decode_any W_5cdec = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdf0 : bv 32 := 0x04c69c63.
Lemma D_5cdf0 : decode_any W_5cdf0 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdf4 : bv 32 := 0x0880006f.
Lemma D_5cdf4 : decode_any W_5cdf4 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdf8 : bv 32 := 0x00e506b3.
Lemma D_5cdf8 : decode_any W_5cdf8 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5cdfc : bv 32 := 0x00481893.
Lemma D_5cdfc : decode_any W_5cdfc = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce00 : bv 32 := 0x011508b3.
Lemma D_5ce00 : decode_any W_5ce00 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce04 : bv 32 := 0x0006a683.
Lemma D_5ce04 : decode_any W_5ce04 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce08 : bv 32 := 0x0008a883.
Lemma D_5ce08 : decode_any W_5ce08 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce0c : bv 32 := 0x0116e463.
Lemma D_5ce0c : decode_any W_5ce0c = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce10 : bv 32 := 0x00060813.
Lemma D_5ce10 : decode_any W_5ce10 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce14 : bv 32 := 0x00080693.
Lemma D_5ce14 : decode_any W_5ce14 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce18 : bv 32 := 0x00278793.
Lemma D_5ce18 : decode_any W_5ce18 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce1c : bv 32 := 0xfcb7fae3.
Lemma D_5ce1c : decode_any W_5ce1c = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce20 : bv 32 := 0x00469813.
Lemma D_5ce20 : decode_any W_5ce20 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce24 : bv 32 := 0x00479893.
Lemma D_5ce24 : decode_any W_5ce24 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce28 : bv 32 := 0x01050833.
Lemma D_5ce28 : decode_any W_5ce28 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce2c : bv 32 := 0x011508b3.
Lemma D_5ce2c : decode_any W_5ce2c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce30 : bv 32 := 0x00082803.
Lemma D_5ce30 : decode_any W_5ce30 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce34 : bv 32 := 0x0008a883.
Lemma D_5ce34 : decode_any W_5ce34 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce38 : bv 32 := 0x01186463.
Lemma D_5ce38 : decode_any W_5ce38 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce3c : bv 32 := 0x00068793.
Lemma D_5ce3c : decode_any W_5ce3c = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce40 : bv 32 := 0x00078693.
Lemma D_5ce40 : decode_any W_5ce40 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce44 : bv 32 := 0x02c78c63.
Lemma D_5ce44 : decode_any W_5ce44 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce48 : bv 32 := 0x00469613.
Lemma D_5ce48 : decode_any W_5ce48 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce4c : bv 32 := 0x00c50633.
Lemma D_5ce4c : decode_any W_5ce4c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce50 : bv 32 := 0x00063783.
Lemma D_5ce50 : decode_any W_5ce50 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce54 : bv 32 := 0x00e50733.
Lemma D_5ce54 : decode_any W_5ce54 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce58 : bv 32 := 0x00073803.
Lemma D_5ce58 : decode_any W_5ce58 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce5c : bv 32 := 0x00873883.
Lemma D_5ce5c : decode_any W_5ce5c = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce60 : bv 32 := 0x00f73023.
Lemma D_5ce60 : decode_any W_5ce60 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce64 : bv 32 := 0x00863783.
Lemma D_5ce64 : decode_any W_5ce64 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce68 : bv 32 := 0x00f73423.
Lemma D_5ce68 : decode_any W_5ce68 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce6c : bv 32 := 0x01063023.
Lemma D_5ce6c : decode_any W_5ce6c = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce70 : bv 32 := 0x01163423.
Lemma D_5ce70 : decode_any W_5ce70 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce74 : bv 32 := 0x00068613.
Lemma D_5ce74 : decode_any W_5ce74 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce78 : bv 32 := 0xf6b6e0e3.
Lemma D_5ce78 : decode_any W_5ce78 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce7c : bv 32 := 0xfff58593.
Lemma D_5ce7c : decode_any W_5ce7c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce80 : bv 32 := 0xf20594e3.
Lemma D_5ce80 : decode_any W_5ce80 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ce84 : bv 32 := 0x00008067.
Lemma D_5ce84 : decode_any W_5ce84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
