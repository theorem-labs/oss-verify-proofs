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

Definition W_70e14 : bv 32 := 0x06060663.
Lemma D_70e14 : decode_any W_70e14 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e18 : bv 32 := 0x00000693.
Lemma D_70e18 : decode_any W_70e18 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e1c : bv 32 := 0x00d58733.
Lemma D_70e1c : decode_any W_70e1c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e20 : bv 32 := 0x00074703.
Lemma D_70e20 : decode_any W_70e20 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e24 : bv 32 := 0x00070c63.
Lemma D_70e24 : decode_any W_70e24 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e28 : bv 32 := 0x00d507b3.
Lemma D_70e28 : decode_any W_70e28 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e2c : bv 32 := 0x00168693.
Lemma D_70e2c : decode_any W_70e2c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e30 : bv 32 := 0x00e78023.
Lemma D_70e30 : decode_any W_70e30 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e34 : bv 32 := 0xfed614e3.
Lemma D_70e34 : decode_any W_70e34 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e38 : bv 32 := 0x00060693.
Lemma D_70e38 : decode_any W_70e38 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e3c : bv 32 := 0x00d505b3.
Lemma D_70e3c : decode_any W_70e3c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e40 : bv 32 := 0x40d6073b.
Lemma D_70e40 : decode_any W_70e40 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e44 : bv 32 := 0x00b76733.
Lemma D_70e44 : decode_any W_70e44 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e48 : bv 32 := 0x00f77713.
Lemma D_70e48 : decode_any W_70e48 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e4c : bv 32 := 0x00070e63.
Lemma D_70e4c : decode_any W_70e4c = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e50 : bv 32 := 0x02d60863.
Lemma D_70e50 : decode_any W_70e50 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e54 : bv 32 := 0x00c50633.
Lemma D_70e54 : decode_any W_70e54 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e58 : bv 32 := 0x00058023.
Lemma D_70e58 : decode_any W_70e58 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e5c : bv 32 := 0x00158593.
Lemma D_70e5c : decode_any W_70e5c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e60 : bv 32 := 0xfec59ce3.
Lemma D_70e60 : decode_any W_70e60 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e64 : bv 32 := 0x01c0006f.
Lemma D_70e64 : decode_any W_70e64 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e68 : bv 32 := 0x00d60c63.
Lemma D_70e68 : decode_any W_70e68 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e6c : bv 32 := 0x00c50633.
Lemma D_70e6c : decode_any W_70e6c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e70 : bv 32 := 0x0005b023.
Lemma D_70e70 : decode_any W_70e70 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e74 : bv 32 := 0x0005b423.
Lemma D_70e74 : decode_any W_70e74 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e78 : bv 32 := 0x01058593.
Lemma D_70e78 : decode_any W_70e78 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e7c : bv 32 := 0xfec5eae3.
Lemma D_70e7c : decode_any W_70e7c = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_70e80 : bv 32 := 0x00008067.
Lemma D_70e80 : decode_any W_70e80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d424 : bv 32 := 0x00200613.
Lemma D_5d424 : decode_any W_5d424 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d428 : bv 32 := 0x14c5ea63.
Lemma D_5d428 : decode_any W_5d428 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d42c : bv 32 := 0x00100613.
Lemma D_5d42c : decode_any W_5d42c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d430 : bv 32 := 0x00100693.
Lemma D_5d430 : decode_any W_5d430 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d434 : bv 32 := 0x00c0006f.
Lemma D_5d434 : decode_any W_5d434 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d438 : bv 32 := 0x00160613.
Lemma D_5d438 : decode_any W_5d438 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d43c : bv 32 := 0x12b60c63.
Lemma D_5d43c : decode_any W_5d43c = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d440 : bv 32 := 0x00461713.
Lemma D_5d440 : decode_any W_5d440 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d444 : bv 32 := 0x00e50733.
Lemma D_5d444 : decode_any W_5d444 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d448 : bv 32 := 0x00072703.
Lemma D_5d448 : decode_any W_5d448 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d44c : bv 32 := 0x00060893.
Lemma D_5d44c : decode_any W_5d44c = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d450 : bv 32 := 0xfff88793.
Lemma D_5d450 : decode_any W_5d450 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d454 : bv 32 := 0x0017d813.
Lemma D_5d454 : decode_any W_5d454 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d458 : bv 32 := 0x00481293.
Lemma D_5d458 : decode_any W_5d458 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d45c : bv 32 := 0x005502b3.
Lemma D_5d45c : decode_any W_5d45c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d460 : bv 32 := 0x0002a303.
Lemma D_5d460 : decode_any W_5d460 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d464 : bv 32 := 0xfce37ae3.
Lemma D_5d464 : decode_any W_5d464 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d468 : bv 32 := 0x0002b303.
Lemma D_5d468 : decode_any W_5d468 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d46c : bv 32 := 0x00489893.
Lemma D_5d46c : decode_any W_5d46c = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d470 : bv 32 := 0x011508b3.
Lemma D_5d470 : decode_any W_5d470 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d474 : bv 32 := 0x0048a383.
Lemma D_5d474 : decode_any W_5d474 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d478 : bv 32 := 0x0068b023.
Lemma D_5d478 : decode_any W_5d478 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d47c : bv 32 := 0x0082b303.
Lemma D_5d47c : decode_any W_5d47c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d480 : bv 32 := 0x0088be03.
Lemma D_5d480 : decode_any W_5d480 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d484 : bv 32 := 0x0068b423.
Lemma D_5d484 : decode_any W_5d484 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d488 : bv 32 := 0x00e2a023.
Lemma D_5d488 : decode_any W_5d488 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d48c : bv 32 := 0x0072a223.
Lemma D_5d48c : decode_any W_5d48c = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d490 : bv 32 := 0x01c2b423.
Lemma D_5d490 : decode_any W_5d490 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d494 : bv 32 := 0x00080893.
Lemma D_5d494 : decode_any W_5d494 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d498 : bv 32 := 0xfaf6ece3.
Lemma D_5d498 : decode_any W_5d498 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d49c : bv 32 := 0xf9dff06f.
Lemma D_5d49c : decode_any W_5d49c = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4a0 : bv 32 := 0x00000613.
Lemma D_5d4a0 : decode_any W_5d4a0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4a4 : bv 32 := 0x00459693.
Lemma D_5d4a4 : decode_any W_5d4a4 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4a8 : bv 32 := 0x00d506b3.
Lemma D_5d4a8 : decode_any W_5d4a8 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4ac : bv 32 := 0x0006b703.
Lemma D_5d4ac : decode_any W_5d4ac = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4b0 : bv 32 := 0x0086b783.
Lemma D_5d4b0 : decode_any W_5d4b0 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4b4 : bv 32 := 0x00053803.
Lemma D_5d4b4 : decode_any W_5d4b4 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4b8 : bv 32 := 0x00853883.
Lemma D_5d4b8 : decode_any W_5d4b8 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4bc : bv 32 := 0x00e53023.
Lemma D_5d4bc : decode_any W_5d4bc = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4c0 : bv 32 := 0x00f53423.
Lemma D_5d4c0 : decode_any W_5d4c0 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4c4 : bv 32 := 0x0106b023.
Lemma D_5d4c4 : decode_any W_5d4c4 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4c8 : bv 32 := 0x0116b423.
Lemma D_5d4c8 : decode_any W_5d4c8 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4cc : bv 32 := 0x00000693.
Lemma D_5d4cc : decode_any W_5d4cc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4d0 : bv 32 := 0x00161793.
Lemma D_5d4d0 : decode_any W_5d4d0 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4d4 : bv 32 := 0x00178813.
Lemma D_5d4d4 : decode_any W_5d4d4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4d8 : bv 32 := 0x00461713.
Lemma D_5d4d8 : decode_any W_5d4d8 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4dc : bv 32 := 0x00b86a63.
Lemma D_5d4dc : decode_any W_5d4dc = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4e0 : bv 32 := 0x00278793.
Lemma D_5d4e0 : decode_any W_5d4e0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4e4 : bv 32 := 0x02b7ea63.
Lemma D_5d4e4 : decode_any W_5d4e4 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4e8 : bv 32 := 0x04c69c63.
Lemma D_5d4e8 : decode_any W_5d4e8 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4ec : bv 32 := 0x0880006f.
Lemma D_5d4ec : decode_any W_5d4ec = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4f0 : bv 32 := 0x00e506b3.
Lemma D_5d4f0 : decode_any W_5d4f0 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4f4 : bv 32 := 0x00481893.
Lemma D_5d4f4 : decode_any W_5d4f4 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4f8 : bv 32 := 0x011508b3.
Lemma D_5d4f8 : decode_any W_5d4f8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d4fc : bv 32 := 0x0006a683.
Lemma D_5d4fc : decode_any W_5d4fc = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d500 : bv 32 := 0x0008a883.
Lemma D_5d500 : decode_any W_5d500 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d504 : bv 32 := 0x0116e463.
Lemma D_5d504 : decode_any W_5d504 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d508 : bv 32 := 0x00060813.
Lemma D_5d508 : decode_any W_5d508 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d50c : bv 32 := 0x00080693.
Lemma D_5d50c : decode_any W_5d50c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d510 : bv 32 := 0x00278793.
Lemma D_5d510 : decode_any W_5d510 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d514 : bv 32 := 0xfcb7fae3.
Lemma D_5d514 : decode_any W_5d514 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d518 : bv 32 := 0x00469813.
Lemma D_5d518 : decode_any W_5d518 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d51c : bv 32 := 0x00479893.
Lemma D_5d51c : decode_any W_5d51c = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d520 : bv 32 := 0x01050833.
Lemma D_5d520 : decode_any W_5d520 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d524 : bv 32 := 0x011508b3.
Lemma D_5d524 : decode_any W_5d524 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d528 : bv 32 := 0x00082803.
Lemma D_5d528 : decode_any W_5d528 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d52c : bv 32 := 0x0008a883.
Lemma D_5d52c : decode_any W_5d52c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d530 : bv 32 := 0x01186463.
Lemma D_5d530 : decode_any W_5d530 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d534 : bv 32 := 0x00068793.
Lemma D_5d534 : decode_any W_5d534 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d538 : bv 32 := 0x00078693.
Lemma D_5d538 : decode_any W_5d538 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d53c : bv 32 := 0x02c78c63.
Lemma D_5d53c : decode_any W_5d53c = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d540 : bv 32 := 0x00469613.
Lemma D_5d540 : decode_any W_5d540 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d544 : bv 32 := 0x00c50633.
Lemma D_5d544 : decode_any W_5d544 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d548 : bv 32 := 0x00063783.
Lemma D_5d548 : decode_any W_5d548 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d54c : bv 32 := 0x00e50733.
Lemma D_5d54c : decode_any W_5d54c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d550 : bv 32 := 0x00073803.
Lemma D_5d550 : decode_any W_5d550 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d554 : bv 32 := 0x00873883.
Lemma D_5d554 : decode_any W_5d554 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d558 : bv 32 := 0x00f73023.
Lemma D_5d558 : decode_any W_5d558 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d55c : bv 32 := 0x00863783.
Lemma D_5d55c : decode_any W_5d55c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d560 : bv 32 := 0x00f73423.
Lemma D_5d560 : decode_any W_5d560 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d564 : bv 32 := 0x01063023.
Lemma D_5d564 : decode_any W_5d564 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d568 : bv 32 := 0x01163423.
Lemma D_5d568 : decode_any W_5d568 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d56c : bv 32 := 0x00068613.
Lemma D_5d56c : decode_any W_5d56c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d570 : bv 32 := 0xf6b6e0e3.
Lemma D_5d570 : decode_any W_5d570 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d574 : bv 32 := 0xfff58593.
Lemma D_5d574 : decode_any W_5d574 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d578 : bv 32 := 0xf20594e3.
Lemma D_5d578 : decode_any W_5d578 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d57c : bv 32 := 0x00008067.
Lemma D_5d57c : decode_any W_5d57c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
