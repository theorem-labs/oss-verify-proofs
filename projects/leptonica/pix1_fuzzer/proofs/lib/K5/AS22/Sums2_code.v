(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
Definition W_6fab4 : bv 32 := 0x06060663.
Lemma D_6fab4 : decode_any W_6fab4 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fab8 : bv 32 := 0x00000693.
Lemma D_6fab8 : decode_any W_6fab8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fabc : bv 32 := 0x00d58733.
Lemma D_6fabc : decode_any W_6fabc = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fac0 : bv 32 := 0x00074703.
Lemma D_6fac0 : decode_any W_6fac0 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fac4 : bv 32 := 0x00070c63.
Lemma D_6fac4 : decode_any W_6fac4 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fac8 : bv 32 := 0x00d507b3.
Lemma D_6fac8 : decode_any W_6fac8 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6facc : bv 32 := 0x00168693.
Lemma D_6facc : decode_any W_6facc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fad0 : bv 32 := 0x00e78023.
Lemma D_6fad0 : decode_any W_6fad0 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fad4 : bv 32 := 0xfed614e3.
Lemma D_6fad4 : decode_any W_6fad4 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fad8 : bv 32 := 0x00060693.
Lemma D_6fad8 : decode_any W_6fad8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fadc : bv 32 := 0x00d505b3.
Lemma D_6fadc : decode_any W_6fadc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fae0 : bv 32 := 0x40d6073b.
Lemma D_6fae0 : decode_any W_6fae0 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fae4 : bv 32 := 0x00b76733.
Lemma D_6fae4 : decode_any W_6fae4 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fae8 : bv 32 := 0x00f77713.
Lemma D_6fae8 : decode_any W_6fae8 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6faec : bv 32 := 0x00070e63.
Lemma D_6faec : decode_any W_6faec = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6faf0 : bv 32 := 0x02d60863.
Lemma D_6faf0 : decode_any W_6faf0 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6faf4 : bv 32 := 0x00c50633.
Lemma D_6faf4 : decode_any W_6faf4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6faf8 : bv 32 := 0x00058023.
Lemma D_6faf8 : decode_any W_6faf8 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fafc : bv 32 := 0x00158593.
Lemma D_6fafc : decode_any W_6fafc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fb00 : bv 32 := 0xfec59ce3.
Lemma D_6fb00 : decode_any W_6fb00 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fb04 : bv 32 := 0x01c0006f.
Lemma D_6fb04 : decode_any W_6fb04 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fb08 : bv 32 := 0x00d60c63.
Lemma D_6fb08 : decode_any W_6fb08 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fb0c : bv 32 := 0x00c50633.
Lemma D_6fb0c : decode_any W_6fb0c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fb10 : bv 32 := 0x0005b023.
Lemma D_6fb10 : decode_any W_6fb10 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fb14 : bv 32 := 0x0005b423.
Lemma D_6fb14 : decode_any W_6fb14 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fb18 : bv 32 := 0x01058593.
Lemma D_6fb18 : decode_any W_6fb18 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fb1c : bv 32 := 0xfec5eae3.
Lemma D_6fb1c : decode_any W_6fb1c = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6fb20 : bv 32 := 0x00008067.
Lemma D_6fb20 : decode_any W_6fb20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_5c064 : bv 32 := 0x00200613.
Lemma D_5c064 : decode_any W_5c064 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c068 : bv 32 := 0x14c5ea63.
Lemma D_5c068 : decode_any W_5c068 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c06c : bv 32 := 0x00100613.
Lemma D_5c06c : decode_any W_5c06c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c070 : bv 32 := 0x00100693.
Lemma D_5c070 : decode_any W_5c070 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c074 : bv 32 := 0x00c0006f.
Lemma D_5c074 : decode_any W_5c074 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c078 : bv 32 := 0x00160613.
Lemma D_5c078 : decode_any W_5c078 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c07c : bv 32 := 0x12b60c63.
Lemma D_5c07c : decode_any W_5c07c = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c080 : bv 32 := 0x00461713.
Lemma D_5c080 : decode_any W_5c080 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c084 : bv 32 := 0x00e50733.
Lemma D_5c084 : decode_any W_5c084 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c088 : bv 32 := 0x00072703.
Lemma D_5c088 : decode_any W_5c088 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c08c : bv 32 := 0x00060893.
Lemma D_5c08c : decode_any W_5c08c = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c090 : bv 32 := 0xfff88793.
Lemma D_5c090 : decode_any W_5c090 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c094 : bv 32 := 0x0017d813.
Lemma D_5c094 : decode_any W_5c094 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c098 : bv 32 := 0x00481293.
Lemma D_5c098 : decode_any W_5c098 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c09c : bv 32 := 0x005502b3.
Lemma D_5c09c : decode_any W_5c09c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0a0 : bv 32 := 0x0002a303.
Lemma D_5c0a0 : decode_any W_5c0a0 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0a4 : bv 32 := 0xfce37ae3.
Lemma D_5c0a4 : decode_any W_5c0a4 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0a8 : bv 32 := 0x0002b303.
Lemma D_5c0a8 : decode_any W_5c0a8 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0ac : bv 32 := 0x00489893.
Lemma D_5c0ac : decode_any W_5c0ac = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0b0 : bv 32 := 0x011508b3.
Lemma D_5c0b0 : decode_any W_5c0b0 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0b4 : bv 32 := 0x0048a383.
Lemma D_5c0b4 : decode_any W_5c0b4 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0b8 : bv 32 := 0x0068b023.
Lemma D_5c0b8 : decode_any W_5c0b8 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0bc : bv 32 := 0x0082b303.
Lemma D_5c0bc : decode_any W_5c0bc = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0c0 : bv 32 := 0x0088be03.
Lemma D_5c0c0 : decode_any W_5c0c0 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0c4 : bv 32 := 0x0068b423.
Lemma D_5c0c4 : decode_any W_5c0c4 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0c8 : bv 32 := 0x00e2a023.
Lemma D_5c0c8 : decode_any W_5c0c8 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0cc : bv 32 := 0x0072a223.
Lemma D_5c0cc : decode_any W_5c0cc = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0d0 : bv 32 := 0x01c2b423.
Lemma D_5c0d0 : decode_any W_5c0d0 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0d4 : bv 32 := 0x00080893.
Lemma D_5c0d4 : decode_any W_5c0d4 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0d8 : bv 32 := 0xfaf6ece3.
Lemma D_5c0d8 : decode_any W_5c0d8 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0dc : bv 32 := 0xf9dff06f.
Lemma D_5c0dc : decode_any W_5c0dc = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0e0 : bv 32 := 0x00000613.
Lemma D_5c0e0 : decode_any W_5c0e0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0e4 : bv 32 := 0x00459693.
Lemma D_5c0e4 : decode_any W_5c0e4 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0e8 : bv 32 := 0x00d506b3.
Lemma D_5c0e8 : decode_any W_5c0e8 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0ec : bv 32 := 0x0006b703.
Lemma D_5c0ec : decode_any W_5c0ec = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0f0 : bv 32 := 0x0086b783.
Lemma D_5c0f0 : decode_any W_5c0f0 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0f4 : bv 32 := 0x00053803.
Lemma D_5c0f4 : decode_any W_5c0f4 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0f8 : bv 32 := 0x00853883.
Lemma D_5c0f8 : decode_any W_5c0f8 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c0fc : bv 32 := 0x00e53023.
Lemma D_5c0fc : decode_any W_5c0fc = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c100 : bv 32 := 0x00f53423.
Lemma D_5c100 : decode_any W_5c100 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c104 : bv 32 := 0x0106b023.
Lemma D_5c104 : decode_any W_5c104 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c108 : bv 32 := 0x0116b423.
Lemma D_5c108 : decode_any W_5c108 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c10c : bv 32 := 0x00000693.
Lemma D_5c10c : decode_any W_5c10c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c110 : bv 32 := 0x00161793.
Lemma D_5c110 : decode_any W_5c110 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c114 : bv 32 := 0x00178813.
Lemma D_5c114 : decode_any W_5c114 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c118 : bv 32 := 0x00461713.
Lemma D_5c118 : decode_any W_5c118 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c11c : bv 32 := 0x00b86a63.
Lemma D_5c11c : decode_any W_5c11c = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c120 : bv 32 := 0x00278793.
Lemma D_5c120 : decode_any W_5c120 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c124 : bv 32 := 0x02b7ea63.
Lemma D_5c124 : decode_any W_5c124 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c128 : bv 32 := 0x04c69c63.
Lemma D_5c128 : decode_any W_5c128 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c12c : bv 32 := 0x0880006f.
Lemma D_5c12c : decode_any W_5c12c = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c130 : bv 32 := 0x00e506b3.
Lemma D_5c130 : decode_any W_5c130 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c134 : bv 32 := 0x00481893.
Lemma D_5c134 : decode_any W_5c134 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c138 : bv 32 := 0x011508b3.
Lemma D_5c138 : decode_any W_5c138 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c13c : bv 32 := 0x0006a683.
Lemma D_5c13c : decode_any W_5c13c = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c140 : bv 32 := 0x0008a883.
Lemma D_5c140 : decode_any W_5c140 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c144 : bv 32 := 0x0116e463.
Lemma D_5c144 : decode_any W_5c144 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c148 : bv 32 := 0x00060813.
Lemma D_5c148 : decode_any W_5c148 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c14c : bv 32 := 0x00080693.
Lemma D_5c14c : decode_any W_5c14c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c150 : bv 32 := 0x00278793.
Lemma D_5c150 : decode_any W_5c150 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c154 : bv 32 := 0xfcb7fae3.
Lemma D_5c154 : decode_any W_5c154 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c158 : bv 32 := 0x00469813.
Lemma D_5c158 : decode_any W_5c158 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c15c : bv 32 := 0x00479893.
Lemma D_5c15c : decode_any W_5c15c = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c160 : bv 32 := 0x01050833.
Lemma D_5c160 : decode_any W_5c160 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c164 : bv 32 := 0x011508b3.
Lemma D_5c164 : decode_any W_5c164 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c168 : bv 32 := 0x00082803.
Lemma D_5c168 : decode_any W_5c168 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c16c : bv 32 := 0x0008a883.
Lemma D_5c16c : decode_any W_5c16c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c170 : bv 32 := 0x01186463.
Lemma D_5c170 : decode_any W_5c170 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c174 : bv 32 := 0x00068793.
Lemma D_5c174 : decode_any W_5c174 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c178 : bv 32 := 0x00078693.
Lemma D_5c178 : decode_any W_5c178 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c17c : bv 32 := 0x02c78c63.
Lemma D_5c17c : decode_any W_5c17c = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c180 : bv 32 := 0x00469613.
Lemma D_5c180 : decode_any W_5c180 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c184 : bv 32 := 0x00c50633.
Lemma D_5c184 : decode_any W_5c184 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c188 : bv 32 := 0x00063783.
Lemma D_5c188 : decode_any W_5c188 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c18c : bv 32 := 0x00e50733.
Lemma D_5c18c : decode_any W_5c18c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c190 : bv 32 := 0x00073803.
Lemma D_5c190 : decode_any W_5c190 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c194 : bv 32 := 0x00873883.
Lemma D_5c194 : decode_any W_5c194 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c198 : bv 32 := 0x00f73023.
Lemma D_5c198 : decode_any W_5c198 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c19c : bv 32 := 0x00863783.
Lemma D_5c19c : decode_any W_5c19c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c1a0 : bv 32 := 0x00f73423.
Lemma D_5c1a0 : decode_any W_5c1a0 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c1a4 : bv 32 := 0x01063023.
Lemma D_5c1a4 : decode_any W_5c1a4 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c1a8 : bv 32 := 0x01163423.
Lemma D_5c1a8 : decode_any W_5c1a8 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c1ac : bv 32 := 0x00068613.
Lemma D_5c1ac : decode_any W_5c1ac = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c1b0 : bv 32 := 0xf6b6e0e3.
Lemma D_5c1b0 : decode_any W_5c1b0 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c1b4 : bv 32 := 0xfff58593.
Lemma D_5c1b4 : decode_any W_5c1b4 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c1b8 : bv 32 := 0xf20594e3.
Lemma D_5c1b8 : decode_any W_5c1b8 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c1bc : bv 32 := 0x00008067.
Lemma D_5c1bc : decode_any W_5c1bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
