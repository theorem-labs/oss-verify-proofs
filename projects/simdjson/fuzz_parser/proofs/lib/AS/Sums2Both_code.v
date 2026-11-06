(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_78dc4 : bv 32 := 0x06060663.
Lemma D_78dc4 : decode_any W_78dc4 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dc8 : bv 32 := 0x00000693.
Lemma D_78dc8 : decode_any W_78dc8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dcc : bv 32 := 0x00d58733.
Lemma D_78dcc : decode_any W_78dcc = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dd0 : bv 32 := 0x00074703.
Lemma D_78dd0 : decode_any W_78dd0 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dd4 : bv 32 := 0x00070c63.
Lemma D_78dd4 : decode_any W_78dd4 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dd8 : bv 32 := 0x00d507b3.
Lemma D_78dd8 : decode_any W_78dd8 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78ddc : bv 32 := 0x00168693.
Lemma D_78ddc : decode_any W_78ddc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78de0 : bv 32 := 0x00e78023.
Lemma D_78de0 : decode_any W_78de0 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78de4 : bv 32 := 0xfed614e3.
Lemma D_78de4 : decode_any W_78de4 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78de8 : bv 32 := 0x00060693.
Lemma D_78de8 : decode_any W_78de8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dec : bv 32 := 0x00d505b3.
Lemma D_78dec : decode_any W_78dec = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78df0 : bv 32 := 0x40d6073b.
Lemma D_78df0 : decode_any W_78df0 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78df4 : bv 32 := 0x00b76733.
Lemma D_78df4 : decode_any W_78df4 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78df8 : bv 32 := 0x00f77713.
Lemma D_78df8 : decode_any W_78df8 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78dfc : bv 32 := 0x00070e63.
Lemma D_78dfc : decode_any W_78dfc = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e00 : bv 32 := 0x02d60863.
Lemma D_78e00 : decode_any W_78e00 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e04 : bv 32 := 0x00c50633.
Lemma D_78e04 : decode_any W_78e04 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e08 : bv 32 := 0x00058023.
Lemma D_78e08 : decode_any W_78e08 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e0c : bv 32 := 0x00158593.
Lemma D_78e0c : decode_any W_78e0c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e10 : bv 32 := 0xfec59ce3.
Lemma D_78e10 : decode_any W_78e10 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e14 : bv 32 := 0x01c0006f.
Lemma D_78e14 : decode_any W_78e14 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e18 : bv 32 := 0x00d60c63.
Lemma D_78e18 : decode_any W_78e18 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e1c : bv 32 := 0x00c50633.
Lemma D_78e1c : decode_any W_78e1c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e20 : bv 32 := 0x0005b023.
Lemma D_78e20 : decode_any W_78e20 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e24 : bv 32 := 0x0005b423.
Lemma D_78e24 : decode_any W_78e24 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e28 : bv 32 := 0x01058593.
Lemma D_78e28 : decode_any W_78e28 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e2c : bv 32 := 0xfec5eae3.
Lemma D_78e2c : decode_any W_78e2c = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78e30 : bv 32 := 0x00008067.
Lemma D_78e30 : decode_any W_78e30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_650e4 : bv 32 := 0x00200613.
Lemma D_650e4 : decode_any W_650e4 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_650e8 : bv 32 := 0x14c5ea63.
Lemma D_650e8 : decode_any W_650e8 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_650ec : bv 32 := 0x00100613.
Lemma D_650ec : decode_any W_650ec = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_650f0 : bv 32 := 0x00100693.
Lemma D_650f0 : decode_any W_650f0 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_650f4 : bv 32 := 0x00c0006f.
Lemma D_650f4 : decode_any W_650f4 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_650f8 : bv 32 := 0x00160613.
Lemma D_650f8 : decode_any W_650f8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_650fc : bv 32 := 0x12b60c63.
Lemma D_650fc : decode_any W_650fc = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65100 : bv 32 := 0x00461713.
Lemma D_65100 : decode_any W_65100 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65104 : bv 32 := 0x00e50733.
Lemma D_65104 : decode_any W_65104 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65108 : bv 32 := 0x00072703.
Lemma D_65108 : decode_any W_65108 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6510c : bv 32 := 0x00060893.
Lemma D_6510c : decode_any W_6510c = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65110 : bv 32 := 0xfff88793.
Lemma D_65110 : decode_any W_65110 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65114 : bv 32 := 0x0017d813.
Lemma D_65114 : decode_any W_65114 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65118 : bv 32 := 0x00481293.
Lemma D_65118 : decode_any W_65118 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6511c : bv 32 := 0x005502b3.
Lemma D_6511c : decode_any W_6511c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65120 : bv 32 := 0x0002a303.
Lemma D_65120 : decode_any W_65120 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65124 : bv 32 := 0xfce37ae3.
Lemma D_65124 : decode_any W_65124 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65128 : bv 32 := 0x0002b303.
Lemma D_65128 : decode_any W_65128 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6512c : bv 32 := 0x00489893.
Lemma D_6512c : decode_any W_6512c = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65130 : bv 32 := 0x011508b3.
Lemma D_65130 : decode_any W_65130 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65134 : bv 32 := 0x0048a383.
Lemma D_65134 : decode_any W_65134 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65138 : bv 32 := 0x0068b023.
Lemma D_65138 : decode_any W_65138 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6513c : bv 32 := 0x0082b303.
Lemma D_6513c : decode_any W_6513c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65140 : bv 32 := 0x0088be03.
Lemma D_65140 : decode_any W_65140 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65144 : bv 32 := 0x0068b423.
Lemma D_65144 : decode_any W_65144 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65148 : bv 32 := 0x00e2a023.
Lemma D_65148 : decode_any W_65148 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6514c : bv 32 := 0x0072a223.
Lemma D_6514c : decode_any W_6514c = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65150 : bv 32 := 0x01c2b423.
Lemma D_65150 : decode_any W_65150 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65154 : bv 32 := 0x00080893.
Lemma D_65154 : decode_any W_65154 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65158 : bv 32 := 0xfaf6ece3.
Lemma D_65158 : decode_any W_65158 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6515c : bv 32 := 0xf9dff06f.
Lemma D_6515c : decode_any W_6515c = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65160 : bv 32 := 0x00000613.
Lemma D_65160 : decode_any W_65160 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65164 : bv 32 := 0x00459693.
Lemma D_65164 : decode_any W_65164 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65168 : bv 32 := 0x00d506b3.
Lemma D_65168 : decode_any W_65168 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6516c : bv 32 := 0x0006b703.
Lemma D_6516c : decode_any W_6516c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65170 : bv 32 := 0x0086b783.
Lemma D_65170 : decode_any W_65170 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65174 : bv 32 := 0x00053803.
Lemma D_65174 : decode_any W_65174 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65178 : bv 32 := 0x00853883.
Lemma D_65178 : decode_any W_65178 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6517c : bv 32 := 0x00e53023.
Lemma D_6517c : decode_any W_6517c = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65180 : bv 32 := 0x00f53423.
Lemma D_65180 : decode_any W_65180 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65184 : bv 32 := 0x0106b023.
Lemma D_65184 : decode_any W_65184 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65188 : bv 32 := 0x0116b423.
Lemma D_65188 : decode_any W_65188 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6518c : bv 32 := 0x00000693.
Lemma D_6518c : decode_any W_6518c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65190 : bv 32 := 0x00161793.
Lemma D_65190 : decode_any W_65190 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65194 : bv 32 := 0x00178813.
Lemma D_65194 : decode_any W_65194 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65198 : bv 32 := 0x00461713.
Lemma D_65198 : decode_any W_65198 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6519c : bv 32 := 0x00b86a63.
Lemma D_6519c : decode_any W_6519c = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651a0 : bv 32 := 0x00278793.
Lemma D_651a0 : decode_any W_651a0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651a4 : bv 32 := 0x02b7ea63.
Lemma D_651a4 : decode_any W_651a4 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651a8 : bv 32 := 0x04c69c63.
Lemma D_651a8 : decode_any W_651a8 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651ac : bv 32 := 0x0880006f.
Lemma D_651ac : decode_any W_651ac = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651b0 : bv 32 := 0x00e506b3.
Lemma D_651b0 : decode_any W_651b0 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651b4 : bv 32 := 0x00481893.
Lemma D_651b4 : decode_any W_651b4 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651b8 : bv 32 := 0x011508b3.
Lemma D_651b8 : decode_any W_651b8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651bc : bv 32 := 0x0006a683.
Lemma D_651bc : decode_any W_651bc = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651c0 : bv 32 := 0x0008a883.
Lemma D_651c0 : decode_any W_651c0 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651c4 : bv 32 := 0x0116e463.
Lemma D_651c4 : decode_any W_651c4 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651c8 : bv 32 := 0x00060813.
Lemma D_651c8 : decode_any W_651c8 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651cc : bv 32 := 0x00080693.
Lemma D_651cc : decode_any W_651cc = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651d0 : bv 32 := 0x00278793.
Lemma D_651d0 : decode_any W_651d0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651d4 : bv 32 := 0xfcb7fae3.
Lemma D_651d4 : decode_any W_651d4 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651d8 : bv 32 := 0x00469813.
Lemma D_651d8 : decode_any W_651d8 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651dc : bv 32 := 0x00479893.
Lemma D_651dc : decode_any W_651dc = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651e0 : bv 32 := 0x01050833.
Lemma D_651e0 : decode_any W_651e0 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651e4 : bv 32 := 0x011508b3.
Lemma D_651e4 : decode_any W_651e4 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651e8 : bv 32 := 0x00082803.
Lemma D_651e8 : decode_any W_651e8 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651ec : bv 32 := 0x0008a883.
Lemma D_651ec : decode_any W_651ec = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651f0 : bv 32 := 0x01186463.
Lemma D_651f0 : decode_any W_651f0 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651f4 : bv 32 := 0x00068793.
Lemma D_651f4 : decode_any W_651f4 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651f8 : bv 32 := 0x00078693.
Lemma D_651f8 : decode_any W_651f8 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_651fc : bv 32 := 0x02c78c63.
Lemma D_651fc : decode_any W_651fc = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65200 : bv 32 := 0x00469613.
Lemma D_65200 : decode_any W_65200 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65204 : bv 32 := 0x00c50633.
Lemma D_65204 : decode_any W_65204 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65208 : bv 32 := 0x00063783.
Lemma D_65208 : decode_any W_65208 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6520c : bv 32 := 0x00e50733.
Lemma D_6520c : decode_any W_6520c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65210 : bv 32 := 0x00073803.
Lemma D_65210 : decode_any W_65210 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65214 : bv 32 := 0x00873883.
Lemma D_65214 : decode_any W_65214 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65218 : bv 32 := 0x00f73023.
Lemma D_65218 : decode_any W_65218 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6521c : bv 32 := 0x00863783.
Lemma D_6521c : decode_any W_6521c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65220 : bv 32 := 0x00f73423.
Lemma D_65220 : decode_any W_65220 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65224 : bv 32 := 0x01063023.
Lemma D_65224 : decode_any W_65224 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65228 : bv 32 := 0x01163423.
Lemma D_65228 : decode_any W_65228 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6522c : bv 32 := 0x00068613.
Lemma D_6522c : decode_any W_6522c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65230 : bv 32 := 0xf6b6e0e3.
Lemma D_65230 : decode_any W_65230 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65234 : bv 32 := 0xfff58593.
Lemma D_65234 : decode_any W_65234 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65238 : bv 32 := 0xf20594e3.
Lemma D_65238 : decode_any W_65238 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6523c : bv 32 := 0x00008067.
Lemma D_6523c : decode_any W_6523c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
