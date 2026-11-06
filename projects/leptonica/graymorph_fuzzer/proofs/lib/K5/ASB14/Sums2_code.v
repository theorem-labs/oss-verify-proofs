(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
Definition W_73a68 : bv 32 := 0x06060663.
Lemma D_73a68 : decode_any W_73a68 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a6c : bv 32 := 0x00000693.
Lemma D_73a6c : decode_any W_73a6c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a70 : bv 32 := 0x00d58733.
Lemma D_73a70 : decode_any W_73a70 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a74 : bv 32 := 0x00074703.
Lemma D_73a74 : decode_any W_73a74 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a78 : bv 32 := 0x00070c63.
Lemma D_73a78 : decode_any W_73a78 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a7c : bv 32 := 0x00d507b3.
Lemma D_73a7c : decode_any W_73a7c = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a80 : bv 32 := 0x00168693.
Lemma D_73a80 : decode_any W_73a80 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a84 : bv 32 := 0x00e78023.
Lemma D_73a84 : decode_any W_73a84 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a88 : bv 32 := 0xfed614e3.
Lemma D_73a88 : decode_any W_73a88 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a8c : bv 32 := 0x00060693.
Lemma D_73a8c : decode_any W_73a8c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a90 : bv 32 := 0x00d505b3.
Lemma D_73a90 : decode_any W_73a90 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a94 : bv 32 := 0x40d6073b.
Lemma D_73a94 : decode_any W_73a94 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a98 : bv 32 := 0x00b76733.
Lemma D_73a98 : decode_any W_73a98 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73a9c : bv 32 := 0x00f77713.
Lemma D_73a9c : decode_any W_73a9c = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73aa0 : bv 32 := 0x00070e63.
Lemma D_73aa0 : decode_any W_73aa0 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73aa4 : bv 32 := 0x02d60863.
Lemma D_73aa4 : decode_any W_73aa4 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73aa8 : bv 32 := 0x00c50633.
Lemma D_73aa8 : decode_any W_73aa8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73aac : bv 32 := 0x00058023.
Lemma D_73aac : decode_any W_73aac = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ab0 : bv 32 := 0x00158593.
Lemma D_73ab0 : decode_any W_73ab0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ab4 : bv 32 := 0xfec59ce3.
Lemma D_73ab4 : decode_any W_73ab4 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ab8 : bv 32 := 0x01c0006f.
Lemma D_73ab8 : decode_any W_73ab8 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73abc : bv 32 := 0x00d60c63.
Lemma D_73abc : decode_any W_73abc = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ac0 : bv 32 := 0x00c50633.
Lemma D_73ac0 : decode_any W_73ac0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ac4 : bv 32 := 0x0005b023.
Lemma D_73ac4 : decode_any W_73ac4 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ac8 : bv 32 := 0x0005b423.
Lemma D_73ac8 : decode_any W_73ac8 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73acc : bv 32 := 0x01058593.
Lemma D_73acc : decode_any W_73acc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ad0 : bv 32 := 0xfec5eae3.
Lemma D_73ad0 : decode_any W_73ad0 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ad4 : bv 32 := 0x00008067.
Lemma D_73ad4 : decode_any W_73ad4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_60018 : bv 32 := 0x00200613.
Lemma D_60018 : decode_any W_60018 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6001c : bv 32 := 0x14c5ea63.
Lemma D_6001c : decode_any W_6001c = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60020 : bv 32 := 0x00100613.
Lemma D_60020 : decode_any W_60020 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60024 : bv 32 := 0x00100693.
Lemma D_60024 : decode_any W_60024 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60028 : bv 32 := 0x00c0006f.
Lemma D_60028 : decode_any W_60028 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6002c : bv 32 := 0x00160613.
Lemma D_6002c : decode_any W_6002c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60030 : bv 32 := 0x12b60c63.
Lemma D_60030 : decode_any W_60030 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60034 : bv 32 := 0x00461713.
Lemma D_60034 : decode_any W_60034 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60038 : bv 32 := 0x00e50733.
Lemma D_60038 : decode_any W_60038 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6003c : bv 32 := 0x00072703.
Lemma D_6003c : decode_any W_6003c = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60040 : bv 32 := 0x00060893.
Lemma D_60040 : decode_any W_60040 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60044 : bv 32 := 0xfff88793.
Lemma D_60044 : decode_any W_60044 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60048 : bv 32 := 0x0017d813.
Lemma D_60048 : decode_any W_60048 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6004c : bv 32 := 0x00481293.
Lemma D_6004c : decode_any W_6004c = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60050 : bv 32 := 0x005502b3.
Lemma D_60050 : decode_any W_60050 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60054 : bv 32 := 0x0002a303.
Lemma D_60054 : decode_any W_60054 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60058 : bv 32 := 0xfce37ae3.
Lemma D_60058 : decode_any W_60058 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6005c : bv 32 := 0x0002b303.
Lemma D_6005c : decode_any W_6005c = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60060 : bv 32 := 0x00489893.
Lemma D_60060 : decode_any W_60060 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60064 : bv 32 := 0x011508b3.
Lemma D_60064 : decode_any W_60064 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60068 : bv 32 := 0x0048a383.
Lemma D_60068 : decode_any W_60068 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6006c : bv 32 := 0x0068b023.
Lemma D_6006c : decode_any W_6006c = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60070 : bv 32 := 0x0082b303.
Lemma D_60070 : decode_any W_60070 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60074 : bv 32 := 0x0088be03.
Lemma D_60074 : decode_any W_60074 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60078 : bv 32 := 0x0068b423.
Lemma D_60078 : decode_any W_60078 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6007c : bv 32 := 0x00e2a023.
Lemma D_6007c : decode_any W_6007c = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60080 : bv 32 := 0x0072a223.
Lemma D_60080 : decode_any W_60080 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60084 : bv 32 := 0x01c2b423.
Lemma D_60084 : decode_any W_60084 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60088 : bv 32 := 0x00080893.
Lemma D_60088 : decode_any W_60088 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6008c : bv 32 := 0xfaf6ece3.
Lemma D_6008c : decode_any W_6008c = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60090 : bv 32 := 0xf9dff06f.
Lemma D_60090 : decode_any W_60090 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60094 : bv 32 := 0x00000613.
Lemma D_60094 : decode_any W_60094 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60098 : bv 32 := 0x00459693.
Lemma D_60098 : decode_any W_60098 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6009c : bv 32 := 0x00d506b3.
Lemma D_6009c : decode_any W_6009c = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600a0 : bv 32 := 0x0006b703.
Lemma D_600a0 : decode_any W_600a0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600a4 : bv 32 := 0x0086b783.
Lemma D_600a4 : decode_any W_600a4 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600a8 : bv 32 := 0x00053803.
Lemma D_600a8 : decode_any W_600a8 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600ac : bv 32 := 0x00853883.
Lemma D_600ac : decode_any W_600ac = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600b0 : bv 32 := 0x00e53023.
Lemma D_600b0 : decode_any W_600b0 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600b4 : bv 32 := 0x00f53423.
Lemma D_600b4 : decode_any W_600b4 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600b8 : bv 32 := 0x0106b023.
Lemma D_600b8 : decode_any W_600b8 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600bc : bv 32 := 0x0116b423.
Lemma D_600bc : decode_any W_600bc = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600c0 : bv 32 := 0x00000693.
Lemma D_600c0 : decode_any W_600c0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600c4 : bv 32 := 0x00161793.
Lemma D_600c4 : decode_any W_600c4 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600c8 : bv 32 := 0x00178813.
Lemma D_600c8 : decode_any W_600c8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600cc : bv 32 := 0x00461713.
Lemma D_600cc : decode_any W_600cc = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600d0 : bv 32 := 0x00b86a63.
Lemma D_600d0 : decode_any W_600d0 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600d4 : bv 32 := 0x00278793.
Lemma D_600d4 : decode_any W_600d4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600d8 : bv 32 := 0x02b7ea63.
Lemma D_600d8 : decode_any W_600d8 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600dc : bv 32 := 0x04c69c63.
Lemma D_600dc : decode_any W_600dc = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600e0 : bv 32 := 0x0880006f.
Lemma D_600e0 : decode_any W_600e0 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600e4 : bv 32 := 0x00e506b3.
Lemma D_600e4 : decode_any W_600e4 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600e8 : bv 32 := 0x00481893.
Lemma D_600e8 : decode_any W_600e8 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600ec : bv 32 := 0x011508b3.
Lemma D_600ec : decode_any W_600ec = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600f0 : bv 32 := 0x0006a683.
Lemma D_600f0 : decode_any W_600f0 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600f4 : bv 32 := 0x0008a883.
Lemma D_600f4 : decode_any W_600f4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600f8 : bv 32 := 0x0116e463.
Lemma D_600f8 : decode_any W_600f8 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_600fc : bv 32 := 0x00060813.
Lemma D_600fc : decode_any W_600fc = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60100 : bv 32 := 0x00080693.
Lemma D_60100 : decode_any W_60100 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60104 : bv 32 := 0x00278793.
Lemma D_60104 : decode_any W_60104 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60108 : bv 32 := 0xfcb7fae3.
Lemma D_60108 : decode_any W_60108 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6010c : bv 32 := 0x00469813.
Lemma D_6010c : decode_any W_6010c = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60110 : bv 32 := 0x00479893.
Lemma D_60110 : decode_any W_60110 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60114 : bv 32 := 0x01050833.
Lemma D_60114 : decode_any W_60114 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60118 : bv 32 := 0x011508b3.
Lemma D_60118 : decode_any W_60118 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6011c : bv 32 := 0x00082803.
Lemma D_6011c : decode_any W_6011c = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60120 : bv 32 := 0x0008a883.
Lemma D_60120 : decode_any W_60120 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60124 : bv 32 := 0x01186463.
Lemma D_60124 : decode_any W_60124 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60128 : bv 32 := 0x00068793.
Lemma D_60128 : decode_any W_60128 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6012c : bv 32 := 0x00078693.
Lemma D_6012c : decode_any W_6012c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60130 : bv 32 := 0x02c78c63.
Lemma D_60130 : decode_any W_60130 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60134 : bv 32 := 0x00469613.
Lemma D_60134 : decode_any W_60134 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60138 : bv 32 := 0x00c50633.
Lemma D_60138 : decode_any W_60138 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6013c : bv 32 := 0x00063783.
Lemma D_6013c : decode_any W_6013c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60140 : bv 32 := 0x00e50733.
Lemma D_60140 : decode_any W_60140 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60144 : bv 32 := 0x00073803.
Lemma D_60144 : decode_any W_60144 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60148 : bv 32 := 0x00873883.
Lemma D_60148 : decode_any W_60148 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6014c : bv 32 := 0x00f73023.
Lemma D_6014c : decode_any W_6014c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60150 : bv 32 := 0x00863783.
Lemma D_60150 : decode_any W_60150 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60154 : bv 32 := 0x00f73423.
Lemma D_60154 : decode_any W_60154 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60158 : bv 32 := 0x01063023.
Lemma D_60158 : decode_any W_60158 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6015c : bv 32 := 0x01163423.
Lemma D_6015c : decode_any W_6015c = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60160 : bv 32 := 0x00068613.
Lemma D_60160 : decode_any W_60160 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60164 : bv 32 := 0xf6b6e0e3.
Lemma D_60164 : decode_any W_60164 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60168 : bv 32 := 0xfff58593.
Lemma D_60168 : decode_any W_60168 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6016c : bv 32 := 0xf20594e3.
Lemma D_6016c : decode_any W_6016c = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60170 : bv 32 := 0x00008067.
Lemma D_60170 : decode_any W_60170 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
