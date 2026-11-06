(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
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
Definition W_79020 : bv 32 := 0x06060663.
Lemma D_79020 : decode_any W_79020 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79024 : bv 32 := 0x00000693.
Lemma D_79024 : decode_any W_79024 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79028 : bv 32 := 0x00d58733.
Lemma D_79028 : decode_any W_79028 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7902c : bv 32 := 0x00074703.
Lemma D_7902c : decode_any W_7902c = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79030 : bv 32 := 0x00070c63.
Lemma D_79030 : decode_any W_79030 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79034 : bv 32 := 0x00d507b3.
Lemma D_79034 : decode_any W_79034 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79038 : bv 32 := 0x00168693.
Lemma D_79038 : decode_any W_79038 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7903c : bv 32 := 0x00e78023.
Lemma D_7903c : decode_any W_7903c = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79040 : bv 32 := 0xfed614e3.
Lemma D_79040 : decode_any W_79040 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79044 : bv 32 := 0x00060693.
Lemma D_79044 : decode_any W_79044 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79048 : bv 32 := 0x00d505b3.
Lemma D_79048 : decode_any W_79048 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7904c : bv 32 := 0x40d6073b.
Lemma D_7904c : decode_any W_7904c = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79050 : bv 32 := 0x00b76733.
Lemma D_79050 : decode_any W_79050 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79054 : bv 32 := 0x00f77713.
Lemma D_79054 : decode_any W_79054 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79058 : bv 32 := 0x00070e63.
Lemma D_79058 : decode_any W_79058 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7905c : bv 32 := 0x02d60863.
Lemma D_7905c : decode_any W_7905c = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79060 : bv 32 := 0x00c50633.
Lemma D_79060 : decode_any W_79060 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79064 : bv 32 := 0x00058023.
Lemma D_79064 : decode_any W_79064 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79068 : bv 32 := 0x00158593.
Lemma D_79068 : decode_any W_79068 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7906c : bv 32 := 0xfec59ce3.
Lemma D_7906c : decode_any W_7906c = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79070 : bv 32 := 0x01c0006f.
Lemma D_79070 : decode_any W_79070 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79074 : bv 32 := 0x00d60c63.
Lemma D_79074 : decode_any W_79074 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79078 : bv 32 := 0x00c50633.
Lemma D_79078 : decode_any W_79078 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7907c : bv 32 := 0x0005b023.
Lemma D_7907c : decode_any W_7907c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79080 : bv 32 := 0x0005b423.
Lemma D_79080 : decode_any W_79080 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79084 : bv 32 := 0x01058593.
Lemma D_79084 : decode_any W_79084 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79088 : bv 32 := 0xfec5eae3.
Lemma D_79088 : decode_any W_79088 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7908c : bv 32 := 0x00008067.
Lemma D_7908c : decode_any W_7908c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_65340 : bv 32 := 0x00200613.
Lemma D_65340 : decode_any W_65340 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65344 : bv 32 := 0x14c5ea63.
Lemma D_65344 : decode_any W_65344 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65348 : bv 32 := 0x00100613.
Lemma D_65348 : decode_any W_65348 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6534c : bv 32 := 0x00100693.
Lemma D_6534c : decode_any W_6534c = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65350 : bv 32 := 0x00c0006f.
Lemma D_65350 : decode_any W_65350 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65354 : bv 32 := 0x00160613.
Lemma D_65354 : decode_any W_65354 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65358 : bv 32 := 0x12b60c63.
Lemma D_65358 : decode_any W_65358 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6535c : bv 32 := 0x00461713.
Lemma D_6535c : decode_any W_6535c = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65360 : bv 32 := 0x00e50733.
Lemma D_65360 : decode_any W_65360 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65364 : bv 32 := 0x00072703.
Lemma D_65364 : decode_any W_65364 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65368 : bv 32 := 0x00060893.
Lemma D_65368 : decode_any W_65368 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6536c : bv 32 := 0xfff88793.
Lemma D_6536c : decode_any W_6536c = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65370 : bv 32 := 0x0017d813.
Lemma D_65370 : decode_any W_65370 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65374 : bv 32 := 0x00481293.
Lemma D_65374 : decode_any W_65374 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65378 : bv 32 := 0x005502b3.
Lemma D_65378 : decode_any W_65378 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6537c : bv 32 := 0x0002a303.
Lemma D_6537c : decode_any W_6537c = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65380 : bv 32 := 0xfce37ae3.
Lemma D_65380 : decode_any W_65380 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65384 : bv 32 := 0x0002b303.
Lemma D_65384 : decode_any W_65384 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65388 : bv 32 := 0x00489893.
Lemma D_65388 : decode_any W_65388 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6538c : bv 32 := 0x011508b3.
Lemma D_6538c : decode_any W_6538c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65390 : bv 32 := 0x0048a383.
Lemma D_65390 : decode_any W_65390 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65394 : bv 32 := 0x0068b023.
Lemma D_65394 : decode_any W_65394 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65398 : bv 32 := 0x0082b303.
Lemma D_65398 : decode_any W_65398 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6539c : bv 32 := 0x0088be03.
Lemma D_6539c : decode_any W_6539c = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653a0 : bv 32 := 0x0068b423.
Lemma D_653a0 : decode_any W_653a0 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653a4 : bv 32 := 0x00e2a023.
Lemma D_653a4 : decode_any W_653a4 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653a8 : bv 32 := 0x0072a223.
Lemma D_653a8 : decode_any W_653a8 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653ac : bv 32 := 0x01c2b423.
Lemma D_653ac : decode_any W_653ac = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653b0 : bv 32 := 0x00080893.
Lemma D_653b0 : decode_any W_653b0 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653b4 : bv 32 := 0xfaf6ece3.
Lemma D_653b4 : decode_any W_653b4 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653b8 : bv 32 := 0xf9dff06f.
Lemma D_653b8 : decode_any W_653b8 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653bc : bv 32 := 0x00000613.
Lemma D_653bc : decode_any W_653bc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653c0 : bv 32 := 0x00459693.
Lemma D_653c0 : decode_any W_653c0 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653c4 : bv 32 := 0x00d506b3.
Lemma D_653c4 : decode_any W_653c4 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653c8 : bv 32 := 0x0006b703.
Lemma D_653c8 : decode_any W_653c8 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653cc : bv 32 := 0x0086b783.
Lemma D_653cc : decode_any W_653cc = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653d0 : bv 32 := 0x00053803.
Lemma D_653d0 : decode_any W_653d0 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653d4 : bv 32 := 0x00853883.
Lemma D_653d4 : decode_any W_653d4 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653d8 : bv 32 := 0x00e53023.
Lemma D_653d8 : decode_any W_653d8 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653dc : bv 32 := 0x00f53423.
Lemma D_653dc : decode_any W_653dc = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653e0 : bv 32 := 0x0106b023.
Lemma D_653e0 : decode_any W_653e0 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653e4 : bv 32 := 0x0116b423.
Lemma D_653e4 : decode_any W_653e4 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653e8 : bv 32 := 0x00000693.
Lemma D_653e8 : decode_any W_653e8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653ec : bv 32 := 0x00161793.
Lemma D_653ec : decode_any W_653ec = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653f0 : bv 32 := 0x00178813.
Lemma D_653f0 : decode_any W_653f0 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653f4 : bv 32 := 0x00461713.
Lemma D_653f4 : decode_any W_653f4 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653f8 : bv 32 := 0x00b86a63.
Lemma D_653f8 : decode_any W_653f8 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653fc : bv 32 := 0x00278793.
Lemma D_653fc : decode_any W_653fc = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65400 : bv 32 := 0x02b7ea63.
Lemma D_65400 : decode_any W_65400 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65404 : bv 32 := 0x04c69c63.
Lemma D_65404 : decode_any W_65404 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65408 : bv 32 := 0x0880006f.
Lemma D_65408 : decode_any W_65408 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6540c : bv 32 := 0x00e506b3.
Lemma D_6540c : decode_any W_6540c = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65410 : bv 32 := 0x00481893.
Lemma D_65410 : decode_any W_65410 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65414 : bv 32 := 0x011508b3.
Lemma D_65414 : decode_any W_65414 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65418 : bv 32 := 0x0006a683.
Lemma D_65418 : decode_any W_65418 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6541c : bv 32 := 0x0008a883.
Lemma D_6541c : decode_any W_6541c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65420 : bv 32 := 0x0116e463.
Lemma D_65420 : decode_any W_65420 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65424 : bv 32 := 0x00060813.
Lemma D_65424 : decode_any W_65424 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65428 : bv 32 := 0x00080693.
Lemma D_65428 : decode_any W_65428 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6542c : bv 32 := 0x00278793.
Lemma D_6542c : decode_any W_6542c = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65430 : bv 32 := 0xfcb7fae3.
Lemma D_65430 : decode_any W_65430 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65434 : bv 32 := 0x00469813.
Lemma D_65434 : decode_any W_65434 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65438 : bv 32 := 0x00479893.
Lemma D_65438 : decode_any W_65438 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6543c : bv 32 := 0x01050833.
Lemma D_6543c : decode_any W_6543c = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65440 : bv 32 := 0x011508b3.
Lemma D_65440 : decode_any W_65440 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65444 : bv 32 := 0x00082803.
Lemma D_65444 : decode_any W_65444 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65448 : bv 32 := 0x0008a883.
Lemma D_65448 : decode_any W_65448 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6544c : bv 32 := 0x01186463.
Lemma D_6544c : decode_any W_6544c = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65450 : bv 32 := 0x00068793.
Lemma D_65450 : decode_any W_65450 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65454 : bv 32 := 0x00078693.
Lemma D_65454 : decode_any W_65454 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65458 : bv 32 := 0x02c78c63.
Lemma D_65458 : decode_any W_65458 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6545c : bv 32 := 0x00469613.
Lemma D_6545c : decode_any W_6545c = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65460 : bv 32 := 0x00c50633.
Lemma D_65460 : decode_any W_65460 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65464 : bv 32 := 0x00063783.
Lemma D_65464 : decode_any W_65464 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65468 : bv 32 := 0x00e50733.
Lemma D_65468 : decode_any W_65468 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6546c : bv 32 := 0x00073803.
Lemma D_6546c : decode_any W_6546c = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65470 : bv 32 := 0x00873883.
Lemma D_65470 : decode_any W_65470 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65474 : bv 32 := 0x00f73023.
Lemma D_65474 : decode_any W_65474 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65478 : bv 32 := 0x00863783.
Lemma D_65478 : decode_any W_65478 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6547c : bv 32 := 0x00f73423.
Lemma D_6547c : decode_any W_6547c = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65480 : bv 32 := 0x01063023.
Lemma D_65480 : decode_any W_65480 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65484 : bv 32 := 0x01163423.
Lemma D_65484 : decode_any W_65484 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65488 : bv 32 := 0x00068613.
Lemma D_65488 : decode_any W_65488 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6548c : bv 32 := 0xf6b6e0e3.
Lemma D_6548c : decode_any W_6548c = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65490 : bv 32 := 0xfff58593.
Lemma D_65490 : decode_any W_65490 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65494 : bv 32 := 0xf20594e3.
Lemma D_65494 : decode_any W_65494 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65498 : bv 32 := 0x00008067.
Lemma D_65498 : decode_any W_65498 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
