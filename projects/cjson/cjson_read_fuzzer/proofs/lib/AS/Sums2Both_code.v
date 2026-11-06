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
Definition W_65c6c : bv 32 := 0x06060663.
Lemma D_65c6c : decode_any W_65c6c = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c70 : bv 32 := 0x00000693.
Lemma D_65c70 : decode_any W_65c70 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c74 : bv 32 := 0x00d58733.
Lemma D_65c74 : decode_any W_65c74 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c78 : bv 32 := 0x00074703.
Lemma D_65c78 : decode_any W_65c78 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c7c : bv 32 := 0x00070c63.
Lemma D_65c7c : decode_any W_65c7c = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c80 : bv 32 := 0x00d507b3.
Lemma D_65c80 : decode_any W_65c80 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c84 : bv 32 := 0x00168693.
Lemma D_65c84 : decode_any W_65c84 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c88 : bv 32 := 0x00e78023.
Lemma D_65c88 : decode_any W_65c88 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c8c : bv 32 := 0xfed614e3.
Lemma D_65c8c : decode_any W_65c8c = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c90 : bv 32 := 0x00060693.
Lemma D_65c90 : decode_any W_65c90 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c94 : bv 32 := 0x00d505b3.
Lemma D_65c94 : decode_any W_65c94 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c98 : bv 32 := 0x40d6073b.
Lemma D_65c98 : decode_any W_65c98 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65c9c : bv 32 := 0x00b76733.
Lemma D_65c9c : decode_any W_65c9c = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ca0 : bv 32 := 0x00f77713.
Lemma D_65ca0 : decode_any W_65ca0 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ca4 : bv 32 := 0x00070e63.
Lemma D_65ca4 : decode_any W_65ca4 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ca8 : bv 32 := 0x02d60863.
Lemma D_65ca8 : decode_any W_65ca8 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cac : bv 32 := 0x00c50633.
Lemma D_65cac : decode_any W_65cac = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cb0 : bv 32 := 0x00058023.
Lemma D_65cb0 : decode_any W_65cb0 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cb4 : bv 32 := 0x00158593.
Lemma D_65cb4 : decode_any W_65cb4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cb8 : bv 32 := 0xfec59ce3.
Lemma D_65cb8 : decode_any W_65cb8 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cbc : bv 32 := 0x01c0006f.
Lemma D_65cbc : decode_any W_65cbc = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cc0 : bv 32 := 0x00d60c63.
Lemma D_65cc0 : decode_any W_65cc0 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cc4 : bv 32 := 0x00c50633.
Lemma D_65cc4 : decode_any W_65cc4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cc8 : bv 32 := 0x0005b023.
Lemma D_65cc8 : decode_any W_65cc8 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ccc : bv 32 := 0x0005b423.
Lemma D_65ccc : decode_any W_65ccc = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cd0 : bv 32 := 0x01058593.
Lemma D_65cd0 : decode_any W_65cd0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cd4 : bv 32 := 0xfec5eae3.
Lemma D_65cd4 : decode_any W_65cd4 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65cd8 : bv 32 := 0x00008067.
Lemma D_65cd8 : decode_any W_65cd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_53008 : bv 32 := 0x00200613.
Lemma D_53008 : decode_any W_53008 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5300c : bv 32 := 0x14c5ea63.
Lemma D_5300c : decode_any W_5300c = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53010 : bv 32 := 0x00100613.
Lemma D_53010 : decode_any W_53010 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53014 : bv 32 := 0x00100693.
Lemma D_53014 : decode_any W_53014 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53018 : bv 32 := 0x00c0006f.
Lemma D_53018 : decode_any W_53018 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5301c : bv 32 := 0x00160613.
Lemma D_5301c : decode_any W_5301c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53020 : bv 32 := 0x12b60c63.
Lemma D_53020 : decode_any W_53020 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53024 : bv 32 := 0x00461713.
Lemma D_53024 : decode_any W_53024 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53028 : bv 32 := 0x00e50733.
Lemma D_53028 : decode_any W_53028 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5302c : bv 32 := 0x00072703.
Lemma D_5302c : decode_any W_5302c = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53030 : bv 32 := 0x00060893.
Lemma D_53030 : decode_any W_53030 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53034 : bv 32 := 0xfff88793.
Lemma D_53034 : decode_any W_53034 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53038 : bv 32 := 0x0017d813.
Lemma D_53038 : decode_any W_53038 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5303c : bv 32 := 0x00481293.
Lemma D_5303c : decode_any W_5303c = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53040 : bv 32 := 0x005502b3.
Lemma D_53040 : decode_any W_53040 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53044 : bv 32 := 0x0002a303.
Lemma D_53044 : decode_any W_53044 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53048 : bv 32 := 0xfce37ae3.
Lemma D_53048 : decode_any W_53048 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5304c : bv 32 := 0x0002b303.
Lemma D_5304c : decode_any W_5304c = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53050 : bv 32 := 0x00489893.
Lemma D_53050 : decode_any W_53050 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53054 : bv 32 := 0x011508b3.
Lemma D_53054 : decode_any W_53054 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53058 : bv 32 := 0x0048a383.
Lemma D_53058 : decode_any W_53058 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5305c : bv 32 := 0x0068b023.
Lemma D_5305c : decode_any W_5305c = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53060 : bv 32 := 0x0082b303.
Lemma D_53060 : decode_any W_53060 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53064 : bv 32 := 0x0088be03.
Lemma D_53064 : decode_any W_53064 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53068 : bv 32 := 0x0068b423.
Lemma D_53068 : decode_any W_53068 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5306c : bv 32 := 0x00e2a023.
Lemma D_5306c : decode_any W_5306c = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53070 : bv 32 := 0x0072a223.
Lemma D_53070 : decode_any W_53070 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53074 : bv 32 := 0x01c2b423.
Lemma D_53074 : decode_any W_53074 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53078 : bv 32 := 0x00080893.
Lemma D_53078 : decode_any W_53078 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5307c : bv 32 := 0xfaf6ece3.
Lemma D_5307c : decode_any W_5307c = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53080 : bv 32 := 0xf9dff06f.
Lemma D_53080 : decode_any W_53080 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53084 : bv 32 := 0x00000613.
Lemma D_53084 : decode_any W_53084 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53088 : bv 32 := 0x00459693.
Lemma D_53088 : decode_any W_53088 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5308c : bv 32 := 0x00d506b3.
Lemma D_5308c : decode_any W_5308c = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53090 : bv 32 := 0x0006b703.
Lemma D_53090 : decode_any W_53090 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53094 : bv 32 := 0x0086b783.
Lemma D_53094 : decode_any W_53094 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53098 : bv 32 := 0x00053803.
Lemma D_53098 : decode_any W_53098 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5309c : bv 32 := 0x00853883.
Lemma D_5309c : decode_any W_5309c = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530a0 : bv 32 := 0x00e53023.
Lemma D_530a0 : decode_any W_530a0 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530a4 : bv 32 := 0x00f53423.
Lemma D_530a4 : decode_any W_530a4 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530a8 : bv 32 := 0x0106b023.
Lemma D_530a8 : decode_any W_530a8 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530ac : bv 32 := 0x0116b423.
Lemma D_530ac : decode_any W_530ac = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530b0 : bv 32 := 0x00000693.
Lemma D_530b0 : decode_any W_530b0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530b4 : bv 32 := 0x00161793.
Lemma D_530b4 : decode_any W_530b4 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530b8 : bv 32 := 0x00178813.
Lemma D_530b8 : decode_any W_530b8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530bc : bv 32 := 0x00461713.
Lemma D_530bc : decode_any W_530bc = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530c0 : bv 32 := 0x00b86a63.
Lemma D_530c0 : decode_any W_530c0 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530c4 : bv 32 := 0x00278793.
Lemma D_530c4 : decode_any W_530c4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530c8 : bv 32 := 0x02b7ea63.
Lemma D_530c8 : decode_any W_530c8 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530cc : bv 32 := 0x04c69c63.
Lemma D_530cc : decode_any W_530cc = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530d0 : bv 32 := 0x0880006f.
Lemma D_530d0 : decode_any W_530d0 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530d4 : bv 32 := 0x00e506b3.
Lemma D_530d4 : decode_any W_530d4 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530d8 : bv 32 := 0x00481893.
Lemma D_530d8 : decode_any W_530d8 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530dc : bv 32 := 0x011508b3.
Lemma D_530dc : decode_any W_530dc = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530e0 : bv 32 := 0x0006a683.
Lemma D_530e0 : decode_any W_530e0 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530e4 : bv 32 := 0x0008a883.
Lemma D_530e4 : decode_any W_530e4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530e8 : bv 32 := 0x0116e463.
Lemma D_530e8 : decode_any W_530e8 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530ec : bv 32 := 0x00060813.
Lemma D_530ec : decode_any W_530ec = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530f0 : bv 32 := 0x00080693.
Lemma D_530f0 : decode_any W_530f0 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530f4 : bv 32 := 0x00278793.
Lemma D_530f4 : decode_any W_530f4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530f8 : bv 32 := 0xfcb7fae3.
Lemma D_530f8 : decode_any W_530f8 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_530fc : bv 32 := 0x00469813.
Lemma D_530fc : decode_any W_530fc = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53100 : bv 32 := 0x00479893.
Lemma D_53100 : decode_any W_53100 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53104 : bv 32 := 0x01050833.
Lemma D_53104 : decode_any W_53104 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53108 : bv 32 := 0x011508b3.
Lemma D_53108 : decode_any W_53108 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5310c : bv 32 := 0x00082803.
Lemma D_5310c : decode_any W_5310c = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53110 : bv 32 := 0x0008a883.
Lemma D_53110 : decode_any W_53110 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53114 : bv 32 := 0x01186463.
Lemma D_53114 : decode_any W_53114 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53118 : bv 32 := 0x00068793.
Lemma D_53118 : decode_any W_53118 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5311c : bv 32 := 0x00078693.
Lemma D_5311c : decode_any W_5311c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53120 : bv 32 := 0x02c78c63.
Lemma D_53120 : decode_any W_53120 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53124 : bv 32 := 0x00469613.
Lemma D_53124 : decode_any W_53124 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53128 : bv 32 := 0x00c50633.
Lemma D_53128 : decode_any W_53128 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5312c : bv 32 := 0x00063783.
Lemma D_5312c : decode_any W_5312c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53130 : bv 32 := 0x00e50733.
Lemma D_53130 : decode_any W_53130 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53134 : bv 32 := 0x00073803.
Lemma D_53134 : decode_any W_53134 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53138 : bv 32 := 0x00873883.
Lemma D_53138 : decode_any W_53138 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5313c : bv 32 := 0x00f73023.
Lemma D_5313c : decode_any W_5313c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53140 : bv 32 := 0x00863783.
Lemma D_53140 : decode_any W_53140 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53144 : bv 32 := 0x00f73423.
Lemma D_53144 : decode_any W_53144 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53148 : bv 32 := 0x01063023.
Lemma D_53148 : decode_any W_53148 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5314c : bv 32 := 0x01163423.
Lemma D_5314c : decode_any W_5314c = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53150 : bv 32 := 0x00068613.
Lemma D_53150 : decode_any W_53150 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53154 : bv 32 := 0xf6b6e0e3.
Lemma D_53154 : decode_any W_53154 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53158 : bv 32 := 0xfff58593.
Lemma D_53158 : decode_any W_53158 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5315c : bv 32 := 0xf20594e3.
Lemma D_5315c : decode_any W_5315c = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53160 : bv 32 := 0x00008067.
Lemma D_53160 : decode_any W_53160 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
