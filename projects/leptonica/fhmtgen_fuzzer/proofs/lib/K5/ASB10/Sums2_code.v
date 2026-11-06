(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_74674 : bv 32 := 0x06060663.
Lemma D_74674 : decode_any W_74674 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74678 : bv 32 := 0x00000693.
Lemma D_74678 : decode_any W_74678 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7467c : bv 32 := 0x00d58733.
Lemma D_7467c : decode_any W_7467c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74680 : bv 32 := 0x00074703.
Lemma D_74680 : decode_any W_74680 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74684 : bv 32 := 0x00070c63.
Lemma D_74684 : decode_any W_74684 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74688 : bv 32 := 0x00d507b3.
Lemma D_74688 : decode_any W_74688 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7468c : bv 32 := 0x00168693.
Lemma D_7468c : decode_any W_7468c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74690 : bv 32 := 0x00e78023.
Lemma D_74690 : decode_any W_74690 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74694 : bv 32 := 0xfed614e3.
Lemma D_74694 : decode_any W_74694 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74698 : bv 32 := 0x00060693.
Lemma D_74698 : decode_any W_74698 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7469c : bv 32 := 0x00d505b3.
Lemma D_7469c : decode_any W_7469c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746a0 : bv 32 := 0x40d6073b.
Lemma D_746a0 : decode_any W_746a0 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746a4 : bv 32 := 0x00b76733.
Lemma D_746a4 : decode_any W_746a4 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746a8 : bv 32 := 0x00f77713.
Lemma D_746a8 : decode_any W_746a8 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746ac : bv 32 := 0x00070e63.
Lemma D_746ac : decode_any W_746ac = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746b0 : bv 32 := 0x02d60863.
Lemma D_746b0 : decode_any W_746b0 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746b4 : bv 32 := 0x00c50633.
Lemma D_746b4 : decode_any W_746b4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746b8 : bv 32 := 0x00058023.
Lemma D_746b8 : decode_any W_746b8 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746bc : bv 32 := 0x00158593.
Lemma D_746bc : decode_any W_746bc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746c0 : bv 32 := 0xfec59ce3.
Lemma D_746c0 : decode_any W_746c0 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746c4 : bv 32 := 0x01c0006f.
Lemma D_746c4 : decode_any W_746c4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746c8 : bv 32 := 0x00d60c63.
Lemma D_746c8 : decode_any W_746c8 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746cc : bv 32 := 0x00c50633.
Lemma D_746cc : decode_any W_746cc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746d0 : bv 32 := 0x0005b023.
Lemma D_746d0 : decode_any W_746d0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746d4 : bv 32 := 0x0005b423.
Lemma D_746d4 : decode_any W_746d4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746d8 : bv 32 := 0x01058593.
Lemma D_746d8 : decode_any W_746d8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746dc : bv 32 := 0xfec5eae3.
Lemma D_746dc : decode_any W_746dc = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_746e0 : bv 32 := 0x00008067.
Lemma D_746e0 : decode_any W_746e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_60c24 : bv 32 := 0x00200613.
Lemma D_60c24 : decode_any W_60c24 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c28 : bv 32 := 0x14c5ea63.
Lemma D_60c28 : decode_any W_60c28 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c2c : bv 32 := 0x00100613.
Lemma D_60c2c : decode_any W_60c2c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c30 : bv 32 := 0x00100693.
Lemma D_60c30 : decode_any W_60c30 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c34 : bv 32 := 0x00c0006f.
Lemma D_60c34 : decode_any W_60c34 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c38 : bv 32 := 0x00160613.
Lemma D_60c38 : decode_any W_60c38 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c3c : bv 32 := 0x12b60c63.
Lemma D_60c3c : decode_any W_60c3c = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c40 : bv 32 := 0x00461713.
Lemma D_60c40 : decode_any W_60c40 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c44 : bv 32 := 0x00e50733.
Lemma D_60c44 : decode_any W_60c44 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c48 : bv 32 := 0x00072703.
Lemma D_60c48 : decode_any W_60c48 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c4c : bv 32 := 0x00060893.
Lemma D_60c4c : decode_any W_60c4c = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c50 : bv 32 := 0xfff88793.
Lemma D_60c50 : decode_any W_60c50 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c54 : bv 32 := 0x0017d813.
Lemma D_60c54 : decode_any W_60c54 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c58 : bv 32 := 0x00481293.
Lemma D_60c58 : decode_any W_60c58 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c5c : bv 32 := 0x005502b3.
Lemma D_60c5c : decode_any W_60c5c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c60 : bv 32 := 0x0002a303.
Lemma D_60c60 : decode_any W_60c60 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c64 : bv 32 := 0xfce37ae3.
Lemma D_60c64 : decode_any W_60c64 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c68 : bv 32 := 0x0002b303.
Lemma D_60c68 : decode_any W_60c68 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c6c : bv 32 := 0x00489893.
Lemma D_60c6c : decode_any W_60c6c = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c70 : bv 32 := 0x011508b3.
Lemma D_60c70 : decode_any W_60c70 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c74 : bv 32 := 0x0048a383.
Lemma D_60c74 : decode_any W_60c74 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c78 : bv 32 := 0x0068b023.
Lemma D_60c78 : decode_any W_60c78 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c7c : bv 32 := 0x0082b303.
Lemma D_60c7c : decode_any W_60c7c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c80 : bv 32 := 0x0088be03.
Lemma D_60c80 : decode_any W_60c80 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c84 : bv 32 := 0x0068b423.
Lemma D_60c84 : decode_any W_60c84 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c88 : bv 32 := 0x00e2a023.
Lemma D_60c88 : decode_any W_60c88 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c8c : bv 32 := 0x0072a223.
Lemma D_60c8c : decode_any W_60c8c = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c90 : bv 32 := 0x01c2b423.
Lemma D_60c90 : decode_any W_60c90 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c94 : bv 32 := 0x00080893.
Lemma D_60c94 : decode_any W_60c94 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c98 : bv 32 := 0xfaf6ece3.
Lemma D_60c98 : decode_any W_60c98 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c9c : bv 32 := 0xf9dff06f.
Lemma D_60c9c : decode_any W_60c9c = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ca0 : bv 32 := 0x00000613.
Lemma D_60ca0 : decode_any W_60ca0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ca4 : bv 32 := 0x00459693.
Lemma D_60ca4 : decode_any W_60ca4 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ca8 : bv 32 := 0x00d506b3.
Lemma D_60ca8 : decode_any W_60ca8 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cac : bv 32 := 0x0006b703.
Lemma D_60cac : decode_any W_60cac = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cb0 : bv 32 := 0x0086b783.
Lemma D_60cb0 : decode_any W_60cb0 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cb4 : bv 32 := 0x00053803.
Lemma D_60cb4 : decode_any W_60cb4 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cb8 : bv 32 := 0x00853883.
Lemma D_60cb8 : decode_any W_60cb8 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cbc : bv 32 := 0x00e53023.
Lemma D_60cbc : decode_any W_60cbc = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cc0 : bv 32 := 0x00f53423.
Lemma D_60cc0 : decode_any W_60cc0 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cc4 : bv 32 := 0x0106b023.
Lemma D_60cc4 : decode_any W_60cc4 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cc8 : bv 32 := 0x0116b423.
Lemma D_60cc8 : decode_any W_60cc8 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ccc : bv 32 := 0x00000693.
Lemma D_60ccc : decode_any W_60ccc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cd0 : bv 32 := 0x00161793.
Lemma D_60cd0 : decode_any W_60cd0 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cd4 : bv 32 := 0x00178813.
Lemma D_60cd4 : decode_any W_60cd4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cd8 : bv 32 := 0x00461713.
Lemma D_60cd8 : decode_any W_60cd8 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cdc : bv 32 := 0x00b86a63.
Lemma D_60cdc : decode_any W_60cdc = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ce0 : bv 32 := 0x00278793.
Lemma D_60ce0 : decode_any W_60ce0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ce4 : bv 32 := 0x02b7ea63.
Lemma D_60ce4 : decode_any W_60ce4 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ce8 : bv 32 := 0x04c69c63.
Lemma D_60ce8 : decode_any W_60ce8 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cec : bv 32 := 0x0880006f.
Lemma D_60cec : decode_any W_60cec = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cf0 : bv 32 := 0x00e506b3.
Lemma D_60cf0 : decode_any W_60cf0 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cf4 : bv 32 := 0x00481893.
Lemma D_60cf4 : decode_any W_60cf4 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cf8 : bv 32 := 0x011508b3.
Lemma D_60cf8 : decode_any W_60cf8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60cfc : bv 32 := 0x0006a683.
Lemma D_60cfc : decode_any W_60cfc = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d00 : bv 32 := 0x0008a883.
Lemma D_60d00 : decode_any W_60d00 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d04 : bv 32 := 0x0116e463.
Lemma D_60d04 : decode_any W_60d04 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d08 : bv 32 := 0x00060813.
Lemma D_60d08 : decode_any W_60d08 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d0c : bv 32 := 0x00080693.
Lemma D_60d0c : decode_any W_60d0c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d10 : bv 32 := 0x00278793.
Lemma D_60d10 : decode_any W_60d10 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d14 : bv 32 := 0xfcb7fae3.
Lemma D_60d14 : decode_any W_60d14 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d18 : bv 32 := 0x00469813.
Lemma D_60d18 : decode_any W_60d18 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d1c : bv 32 := 0x00479893.
Lemma D_60d1c : decode_any W_60d1c = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d20 : bv 32 := 0x01050833.
Lemma D_60d20 : decode_any W_60d20 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d24 : bv 32 := 0x011508b3.
Lemma D_60d24 : decode_any W_60d24 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d28 : bv 32 := 0x00082803.
Lemma D_60d28 : decode_any W_60d28 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d2c : bv 32 := 0x0008a883.
Lemma D_60d2c : decode_any W_60d2c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d30 : bv 32 := 0x01186463.
Lemma D_60d30 : decode_any W_60d30 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d34 : bv 32 := 0x00068793.
Lemma D_60d34 : decode_any W_60d34 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d38 : bv 32 := 0x00078693.
Lemma D_60d38 : decode_any W_60d38 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d3c : bv 32 := 0x02c78c63.
Lemma D_60d3c : decode_any W_60d3c = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d40 : bv 32 := 0x00469613.
Lemma D_60d40 : decode_any W_60d40 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d44 : bv 32 := 0x00c50633.
Lemma D_60d44 : decode_any W_60d44 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d48 : bv 32 := 0x00063783.
Lemma D_60d48 : decode_any W_60d48 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d4c : bv 32 := 0x00e50733.
Lemma D_60d4c : decode_any W_60d4c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d50 : bv 32 := 0x00073803.
Lemma D_60d50 : decode_any W_60d50 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d54 : bv 32 := 0x00873883.
Lemma D_60d54 : decode_any W_60d54 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d58 : bv 32 := 0x00f73023.
Lemma D_60d58 : decode_any W_60d58 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d5c : bv 32 := 0x00863783.
Lemma D_60d5c : decode_any W_60d5c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d60 : bv 32 := 0x00f73423.
Lemma D_60d60 : decode_any W_60d60 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d64 : bv 32 := 0x01063023.
Lemma D_60d64 : decode_any W_60d64 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d68 : bv 32 := 0x01163423.
Lemma D_60d68 : decode_any W_60d68 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d6c : bv 32 := 0x00068613.
Lemma D_60d6c : decode_any W_60d6c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d70 : bv 32 := 0xf6b6e0e3.
Lemma D_60d70 : decode_any W_60d70 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d74 : bv 32 := 0xfff58593.
Lemma D_60d74 : decode_any W_60d74 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d78 : bv 32 := 0xf20594e3.
Lemma D_60d78 : decode_any W_60d78 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d7c : bv 32 := 0x00008067.
Lemma D_60d7c : decode_any W_60d7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
