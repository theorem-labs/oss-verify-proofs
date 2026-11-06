(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_634f0 : bv 32 := 0x06060663.
Lemma D_634f0 : decode_any W_634f0 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_634f4 : bv 32 := 0x00000693.
Lemma D_634f4 : decode_any W_634f4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_634f8 : bv 32 := 0x00d58733.
Lemma D_634f8 : decode_any W_634f8 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_634fc : bv 32 := 0x00074703.
Lemma D_634fc : decode_any W_634fc = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63500 : bv 32 := 0x00070c63.
Lemma D_63500 : decode_any W_63500 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63504 : bv 32 := 0x00d507b3.
Lemma D_63504 : decode_any W_63504 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63508 : bv 32 := 0x00168693.
Lemma D_63508 : decode_any W_63508 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6350c : bv 32 := 0x00e78023.
Lemma D_6350c : decode_any W_6350c = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63510 : bv 32 := 0xfed614e3.
Lemma D_63510 : decode_any W_63510 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63514 : bv 32 := 0x00060693.
Lemma D_63514 : decode_any W_63514 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63518 : bv 32 := 0x00d505b3.
Lemma D_63518 : decode_any W_63518 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6351c : bv 32 := 0x40d6073b.
Lemma D_6351c : decode_any W_6351c = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63520 : bv 32 := 0x00b76733.
Lemma D_63520 : decode_any W_63520 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63524 : bv 32 := 0x00f77713.
Lemma D_63524 : decode_any W_63524 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63528 : bv 32 := 0x00070e63.
Lemma D_63528 : decode_any W_63528 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6352c : bv 32 := 0x02d60863.
Lemma D_6352c : decode_any W_6352c = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63530 : bv 32 := 0x00c50633.
Lemma D_63530 : decode_any W_63530 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63534 : bv 32 := 0x00058023.
Lemma D_63534 : decode_any W_63534 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63538 : bv 32 := 0x00158593.
Lemma D_63538 : decode_any W_63538 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6353c : bv 32 := 0xfec59ce3.
Lemma D_6353c : decode_any W_6353c = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63540 : bv 32 := 0x01c0006f.
Lemma D_63540 : decode_any W_63540 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63544 : bv 32 := 0x00d60c63.
Lemma D_63544 : decode_any W_63544 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63548 : bv 32 := 0x00c50633.
Lemma D_63548 : decode_any W_63548 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6354c : bv 32 := 0x0005b023.
Lemma D_6354c : decode_any W_6354c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63550 : bv 32 := 0x0005b423.
Lemma D_63550 : decode_any W_63550 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63554 : bv 32 := 0x01058593.
Lemma D_63554 : decode_any W_63554 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63558 : bv 32 := 0xfec5eae3.
Lemma D_63558 : decode_any W_63558 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6355c : bv 32 := 0x00008067.
Lemma D_6355c : decode_any W_6355c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_50bd4 : bv 32 := 0x00200613.
Lemma D_50bd4 : decode_any W_50bd4 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bd8 : bv 32 := 0x14c5ea63.
Lemma D_50bd8 : decode_any W_50bd8 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bdc : bv 32 := 0x00100613.
Lemma D_50bdc : decode_any W_50bdc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50be0 : bv 32 := 0x00100693.
Lemma D_50be0 : decode_any W_50be0 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50be4 : bv 32 := 0x00c0006f.
Lemma D_50be4 : decode_any W_50be4 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50be8 : bv 32 := 0x00160613.
Lemma D_50be8 : decode_any W_50be8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bec : bv 32 := 0x12b60c63.
Lemma D_50bec : decode_any W_50bec = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bf0 : bv 32 := 0x00461713.
Lemma D_50bf0 : decode_any W_50bf0 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bf4 : bv 32 := 0x00e50733.
Lemma D_50bf4 : decode_any W_50bf4 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bf8 : bv 32 := 0x00072703.
Lemma D_50bf8 : decode_any W_50bf8 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bfc : bv 32 := 0x00060893.
Lemma D_50bfc : decode_any W_50bfc = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c00 : bv 32 := 0xfff88793.
Lemma D_50c00 : decode_any W_50c00 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c04 : bv 32 := 0x0017d813.
Lemma D_50c04 : decode_any W_50c04 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c08 : bv 32 := 0x00481293.
Lemma D_50c08 : decode_any W_50c08 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c0c : bv 32 := 0x005502b3.
Lemma D_50c0c : decode_any W_50c0c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c10 : bv 32 := 0x0002a303.
Lemma D_50c10 : decode_any W_50c10 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c14 : bv 32 := 0xfce37ae3.
Lemma D_50c14 : decode_any W_50c14 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c18 : bv 32 := 0x0002b303.
Lemma D_50c18 : decode_any W_50c18 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c1c : bv 32 := 0x00489893.
Lemma D_50c1c : decode_any W_50c1c = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c20 : bv 32 := 0x011508b3.
Lemma D_50c20 : decode_any W_50c20 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c24 : bv 32 := 0x0048a383.
Lemma D_50c24 : decode_any W_50c24 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c28 : bv 32 := 0x0068b023.
Lemma D_50c28 : decode_any W_50c28 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c2c : bv 32 := 0x0082b303.
Lemma D_50c2c : decode_any W_50c2c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c30 : bv 32 := 0x0088be03.
Lemma D_50c30 : decode_any W_50c30 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c34 : bv 32 := 0x0068b423.
Lemma D_50c34 : decode_any W_50c34 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c38 : bv 32 := 0x00e2a023.
Lemma D_50c38 : decode_any W_50c38 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c3c : bv 32 := 0x0072a223.
Lemma D_50c3c : decode_any W_50c3c = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c40 : bv 32 := 0x01c2b423.
Lemma D_50c40 : decode_any W_50c40 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c44 : bv 32 := 0x00080893.
Lemma D_50c44 : decode_any W_50c44 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c48 : bv 32 := 0xfaf6ece3.
Lemma D_50c48 : decode_any W_50c48 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c4c : bv 32 := 0xf9dff06f.
Lemma D_50c4c : decode_any W_50c4c = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c50 : bv 32 := 0x00000613.
Lemma D_50c50 : decode_any W_50c50 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c54 : bv 32 := 0x00459693.
Lemma D_50c54 : decode_any W_50c54 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c58 : bv 32 := 0x00d506b3.
Lemma D_50c58 : decode_any W_50c58 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c5c : bv 32 := 0x0006b703.
Lemma D_50c5c : decode_any W_50c5c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c60 : bv 32 := 0x0086b783.
Lemma D_50c60 : decode_any W_50c60 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c64 : bv 32 := 0x00053803.
Lemma D_50c64 : decode_any W_50c64 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c68 : bv 32 := 0x00853883.
Lemma D_50c68 : decode_any W_50c68 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c6c : bv 32 := 0x00e53023.
Lemma D_50c6c : decode_any W_50c6c = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c70 : bv 32 := 0x00f53423.
Lemma D_50c70 : decode_any W_50c70 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c74 : bv 32 := 0x0106b023.
Lemma D_50c74 : decode_any W_50c74 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c78 : bv 32 := 0x0116b423.
Lemma D_50c78 : decode_any W_50c78 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c7c : bv 32 := 0x00000693.
Lemma D_50c7c : decode_any W_50c7c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c80 : bv 32 := 0x00161793.
Lemma D_50c80 : decode_any W_50c80 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c84 : bv 32 := 0x00178813.
Lemma D_50c84 : decode_any W_50c84 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c88 : bv 32 := 0x00461713.
Lemma D_50c88 : decode_any W_50c88 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c8c : bv 32 := 0x00b86a63.
Lemma D_50c8c : decode_any W_50c8c = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c90 : bv 32 := 0x00278793.
Lemma D_50c90 : decode_any W_50c90 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c94 : bv 32 := 0x02b7ea63.
Lemma D_50c94 : decode_any W_50c94 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c98 : bv 32 := 0x04c69c63.
Lemma D_50c98 : decode_any W_50c98 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c9c : bv 32 := 0x0880006f.
Lemma D_50c9c : decode_any W_50c9c = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ca0 : bv 32 := 0x00e506b3.
Lemma D_50ca0 : decode_any W_50ca0 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ca4 : bv 32 := 0x00481893.
Lemma D_50ca4 : decode_any W_50ca4 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ca8 : bv 32 := 0x011508b3.
Lemma D_50ca8 : decode_any W_50ca8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cac : bv 32 := 0x0006a683.
Lemma D_50cac : decode_any W_50cac = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cb0 : bv 32 := 0x0008a883.
Lemma D_50cb0 : decode_any W_50cb0 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cb4 : bv 32 := 0x0116e463.
Lemma D_50cb4 : decode_any W_50cb4 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cb8 : bv 32 := 0x00060813.
Lemma D_50cb8 : decode_any W_50cb8 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cbc : bv 32 := 0x00080693.
Lemma D_50cbc : decode_any W_50cbc = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cc0 : bv 32 := 0x00278793.
Lemma D_50cc0 : decode_any W_50cc0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cc4 : bv 32 := 0xfcb7fae3.
Lemma D_50cc4 : decode_any W_50cc4 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cc8 : bv 32 := 0x00469813.
Lemma D_50cc8 : decode_any W_50cc8 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ccc : bv 32 := 0x00479893.
Lemma D_50ccc : decode_any W_50ccc = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cd0 : bv 32 := 0x01050833.
Lemma D_50cd0 : decode_any W_50cd0 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cd4 : bv 32 := 0x011508b3.
Lemma D_50cd4 : decode_any W_50cd4 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cd8 : bv 32 := 0x00082803.
Lemma D_50cd8 : decode_any W_50cd8 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cdc : bv 32 := 0x0008a883.
Lemma D_50cdc : decode_any W_50cdc = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ce0 : bv 32 := 0x01186463.
Lemma D_50ce0 : decode_any W_50ce0 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ce4 : bv 32 := 0x00068793.
Lemma D_50ce4 : decode_any W_50ce4 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ce8 : bv 32 := 0x00078693.
Lemma D_50ce8 : decode_any W_50ce8 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cec : bv 32 := 0x02c78c63.
Lemma D_50cec : decode_any W_50cec = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cf0 : bv 32 := 0x00469613.
Lemma D_50cf0 : decode_any W_50cf0 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cf4 : bv 32 := 0x00c50633.
Lemma D_50cf4 : decode_any W_50cf4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cf8 : bv 32 := 0x00063783.
Lemma D_50cf8 : decode_any W_50cf8 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cfc : bv 32 := 0x00e50733.
Lemma D_50cfc : decode_any W_50cfc = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d00 : bv 32 := 0x00073803.
Lemma D_50d00 : decode_any W_50d00 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d04 : bv 32 := 0x00873883.
Lemma D_50d04 : decode_any W_50d04 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d08 : bv 32 := 0x00f73023.
Lemma D_50d08 : decode_any W_50d08 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d0c : bv 32 := 0x00863783.
Lemma D_50d0c : decode_any W_50d0c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d10 : bv 32 := 0x00f73423.
Lemma D_50d10 : decode_any W_50d10 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d14 : bv 32 := 0x01063023.
Lemma D_50d14 : decode_any W_50d14 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d18 : bv 32 := 0x01163423.
Lemma D_50d18 : decode_any W_50d18 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d1c : bv 32 := 0x00068613.
Lemma D_50d1c : decode_any W_50d1c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d20 : bv 32 := 0xf6b6e0e3.
Lemma D_50d20 : decode_any W_50d20 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d24 : bv 32 := 0xfff58593.
Lemma D_50d24 : decode_any W_50d24 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d28 : bv 32 := 0xf20594e3.
Lemma D_50d28 : decode_any W_50d28 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d2c : bv 32 := 0x00008067.
Lemma D_50d2c : decode_any W_50d2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
