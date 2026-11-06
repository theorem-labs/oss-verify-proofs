(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_64e24 : bv 32 := 0x06060663.
Lemma D_64e24 : decode_any W_64e24 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e28 : bv 32 := 0x00000693.
Lemma D_64e28 : decode_any W_64e28 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e2c : bv 32 := 0x00d58733.
Lemma D_64e2c : decode_any W_64e2c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e30 : bv 32 := 0x00074703.
Lemma D_64e30 : decode_any W_64e30 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e34 : bv 32 := 0x00070c63.
Lemma D_64e34 : decode_any W_64e34 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e38 : bv 32 := 0x00d507b3.
Lemma D_64e38 : decode_any W_64e38 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e3c : bv 32 := 0x00168693.
Lemma D_64e3c : decode_any W_64e3c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e40 : bv 32 := 0x00e78023.
Lemma D_64e40 : decode_any W_64e40 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e44 : bv 32 := 0xfed614e3.
Lemma D_64e44 : decode_any W_64e44 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e48 : bv 32 := 0x00060693.
Lemma D_64e48 : decode_any W_64e48 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e4c : bv 32 := 0x00d505b3.
Lemma D_64e4c : decode_any W_64e4c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e50 : bv 32 := 0x40d6073b.
Lemma D_64e50 : decode_any W_64e50 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e54 : bv 32 := 0x00b76733.
Lemma D_64e54 : decode_any W_64e54 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e58 : bv 32 := 0x00f77713.
Lemma D_64e58 : decode_any W_64e58 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e5c : bv 32 := 0x00070e63.
Lemma D_64e5c : decode_any W_64e5c = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e60 : bv 32 := 0x02d60863.
Lemma D_64e60 : decode_any W_64e60 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e64 : bv 32 := 0x00c50633.
Lemma D_64e64 : decode_any W_64e64 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e68 : bv 32 := 0x00058023.
Lemma D_64e68 : decode_any W_64e68 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e6c : bv 32 := 0x00158593.
Lemma D_64e6c : decode_any W_64e6c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e70 : bv 32 := 0xfec59ce3.
Lemma D_64e70 : decode_any W_64e70 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e74 : bv 32 := 0x01c0006f.
Lemma D_64e74 : decode_any W_64e74 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e78 : bv 32 := 0x00d60c63.
Lemma D_64e78 : decode_any W_64e78 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e7c : bv 32 := 0x00c50633.
Lemma D_64e7c : decode_any W_64e7c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e80 : bv 32 := 0x0005b023.
Lemma D_64e80 : decode_any W_64e80 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e84 : bv 32 := 0x0005b423.
Lemma D_64e84 : decode_any W_64e84 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e88 : bv 32 := 0x01058593.
Lemma D_64e88 : decode_any W_64e88 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e8c : bv 32 := 0xfec5eae3.
Lemma D_64e8c : decode_any W_64e8c = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e90 : bv 32 := 0x00008067.
Lemma D_64e90 : decode_any W_64e90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52508 : bv 32 := 0x00200613.
Lemma D_52508 : decode_any W_52508 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5250c : bv 32 := 0x14c5ea63.
Lemma D_5250c : decode_any W_5250c = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_52510 : bv 32 := 0x00100613.
Lemma D_52510 : decode_any W_52510 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52514 : bv 32 := 0x00100693.
Lemma D_52514 : decode_any W_52514 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52518 : bv 32 := 0x00c0006f.
Lemma D_52518 : decode_any W_52518 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5251c : bv 32 := 0x00160613.
Lemma D_5251c : decode_any W_5251c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_52520 : bv 32 := 0x12b60c63.
Lemma D_52520 : decode_any W_52520 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_52524 : bv 32 := 0x00461713.
Lemma D_52524 : decode_any W_52524 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_52528 : bv 32 := 0x00e50733.
Lemma D_52528 : decode_any W_52528 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5252c : bv 32 := 0x00072703.
Lemma D_5252c : decode_any W_5252c = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52530 : bv 32 := 0x00060893.
Lemma D_52530 : decode_any W_52530 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52534 : bv 32 := 0xfff88793.
Lemma D_52534 : decode_any W_52534 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_52538 : bv 32 := 0x0017d813.
Lemma D_52538 : decode_any W_52538 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5253c : bv 32 := 0x00481293.
Lemma D_5253c : decode_any W_5253c = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_52540 : bv 32 := 0x005502b3.
Lemma D_52540 : decode_any W_52540 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_52544 : bv 32 := 0x0002a303.
Lemma D_52544 : decode_any W_52544 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52548 : bv 32 := 0xfce37ae3.
Lemma D_52548 : decode_any W_52548 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5254c : bv 32 := 0x0002b303.
Lemma D_5254c : decode_any W_5254c = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52550 : bv 32 := 0x00489893.
Lemma D_52550 : decode_any W_52550 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_52554 : bv 32 := 0x011508b3.
Lemma D_52554 : decode_any W_52554 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_52558 : bv 32 := 0x0048a383.
Lemma D_52558 : decode_any W_52558 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5255c : bv 32 := 0x0068b023.
Lemma D_5255c : decode_any W_5255c = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52560 : bv 32 := 0x0082b303.
Lemma D_52560 : decode_any W_52560 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52564 : bv 32 := 0x0088be03.
Lemma D_52564 : decode_any W_52564 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52568 : bv 32 := 0x0068b423.
Lemma D_52568 : decode_any W_52568 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5256c : bv 32 := 0x00e2a023.
Lemma D_5256c : decode_any W_5256c = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52570 : bv 32 := 0x0072a223.
Lemma D_52570 : decode_any W_52570 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_52574 : bv 32 := 0x01c2b423.
Lemma D_52574 : decode_any W_52574 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52578 : bv 32 := 0x00080893.
Lemma D_52578 : decode_any W_52578 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5257c : bv 32 := 0xfaf6ece3.
Lemma D_5257c : decode_any W_5257c = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_52580 : bv 32 := 0xf9dff06f.
Lemma D_52580 : decode_any W_52580 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

Definition W_52584 : bv 32 := 0x00000613.
Lemma D_52584 : decode_any W_52584 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52588 : bv 32 := 0x00459693.
Lemma D_52588 : decode_any W_52588 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5258c : bv 32 := 0x00d506b3.
Lemma D_5258c : decode_any W_5258c = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_52590 : bv 32 := 0x0006b703.
Lemma D_52590 : decode_any W_52590 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52594 : bv 32 := 0x0086b783.
Lemma D_52594 : decode_any W_52594 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52598 : bv 32 := 0x00053803.
Lemma D_52598 : decode_any W_52598 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5259c : bv 32 := 0x00853883.
Lemma D_5259c : decode_any W_5259c = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_525a0 : bv 32 := 0x00e53023.
Lemma D_525a0 : decode_any W_525a0 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_525a4 : bv 32 := 0x00f53423.
Lemma D_525a4 : decode_any W_525a4 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_525a8 : bv 32 := 0x0106b023.
Lemma D_525a8 : decode_any W_525a8 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_525ac : bv 32 := 0x0116b423.
Lemma D_525ac : decode_any W_525ac = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_525b0 : bv 32 := 0x00000693.
Lemma D_525b0 : decode_any W_525b0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_525b4 : bv 32 := 0x00161793.
Lemma D_525b4 : decode_any W_525b4 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_525b8 : bv 32 := 0x00178813.
Lemma D_525b8 : decode_any W_525b8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_525bc : bv 32 := 0x00461713.
Lemma D_525bc : decode_any W_525bc = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_525c0 : bv 32 := 0x00b86a63.
Lemma D_525c0 : decode_any W_525c0 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_525c4 : bv 32 := 0x00278793.
Lemma D_525c4 : decode_any W_525c4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_525c8 : bv 32 := 0x02b7ea63.
Lemma D_525c8 : decode_any W_525c8 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_525cc : bv 32 := 0x04c69c63.
Lemma D_525cc : decode_any W_525cc = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_525d0 : bv 32 := 0x0880006f.
Lemma D_525d0 : decode_any W_525d0 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_525d4 : bv 32 := 0x00e506b3.
Lemma D_525d4 : decode_any W_525d4 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_525d8 : bv 32 := 0x00481893.
Lemma D_525d8 : decode_any W_525d8 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_525dc : bv 32 := 0x011508b3.
Lemma D_525dc : decode_any W_525dc = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_525e0 : bv 32 := 0x0006a683.
Lemma D_525e0 : decode_any W_525e0 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_525e4 : bv 32 := 0x0008a883.
Lemma D_525e4 : decode_any W_525e4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_525e8 : bv 32 := 0x0116e463.
Lemma D_525e8 : decode_any W_525e8 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_525ec : bv 32 := 0x00060813.
Lemma D_525ec : decode_any W_525ec = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_525f0 : bv 32 := 0x00080693.
Lemma D_525f0 : decode_any W_525f0 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_525f4 : bv 32 := 0x00278793.
Lemma D_525f4 : decode_any W_525f4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_525f8 : bv 32 := 0xfcb7fae3.
Lemma D_525f8 : decode_any W_525f8 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_525fc : bv 32 := 0x00469813.
Lemma D_525fc : decode_any W_525fc = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_52600 : bv 32 := 0x00479893.
Lemma D_52600 : decode_any W_52600 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_52604 : bv 32 := 0x01050833.
Lemma D_52604 : decode_any W_52604 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52608 : bv 32 := 0x011508b3.
Lemma D_52608 : decode_any W_52608 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5260c : bv 32 := 0x00082803.
Lemma D_5260c : decode_any W_5260c = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52610 : bv 32 := 0x0008a883.
Lemma D_52610 : decode_any W_52610 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52614 : bv 32 := 0x01186463.
Lemma D_52614 : decode_any W_52614 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52618 : bv 32 := 0x00068793.
Lemma D_52618 : decode_any W_52618 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5261c : bv 32 := 0x00078693.
Lemma D_5261c : decode_any W_5261c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52620 : bv 32 := 0x02c78c63.
Lemma D_52620 : decode_any W_52620 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_52624 : bv 32 := 0x00469613.
Lemma D_52624 : decode_any W_52624 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_52628 : bv 32 := 0x00c50633.
Lemma D_52628 : decode_any W_52628 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5262c : bv 32 := 0x00063783.
Lemma D_5262c : decode_any W_5262c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52630 : bv 32 := 0x00e50733.
Lemma D_52630 : decode_any W_52630 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_52634 : bv 32 := 0x00073803.
Lemma D_52634 : decode_any W_52634 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52638 : bv 32 := 0x00873883.
Lemma D_52638 : decode_any W_52638 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5263c : bv 32 := 0x00f73023.
Lemma D_5263c : decode_any W_5263c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52640 : bv 32 := 0x00863783.
Lemma D_52640 : decode_any W_52640 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52644 : bv 32 := 0x00f73423.
Lemma D_52644 : decode_any W_52644 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52648 : bv 32 := 0x01063023.
Lemma D_52648 : decode_any W_52648 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5264c : bv 32 := 0x01163423.
Lemma D_5264c : decode_any W_5264c = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52650 : bv 32 := 0x00068613.
Lemma D_52650 : decode_any W_52650 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52654 : bv 32 := 0xf6b6e0e3.
Lemma D_52654 : decode_any W_52654 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_52658 : bv 32 := 0xfff58593.
Lemma D_52658 : decode_any W_52658 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5265c : bv 32 := 0xf20594e3.
Lemma D_5265c : decode_any W_5265c = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

Definition W_52660 : bv 32 := 0x00008067.
Lemma D_52660 : decode_any W_52660 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
