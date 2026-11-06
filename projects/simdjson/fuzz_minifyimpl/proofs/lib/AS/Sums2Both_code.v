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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_94a48 : bv 32 := 0x06060663.
Lemma D_94a48 : decode_any W_94a48 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a4c : bv 32 := 0x00000693.
Lemma D_94a4c : decode_any W_94a4c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a50 : bv 32 := 0x00d58733.
Lemma D_94a50 : decode_any W_94a50 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a54 : bv 32 := 0x00074703.
Lemma D_94a54 : decode_any W_94a54 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a58 : bv 32 := 0x00070c63.
Lemma D_94a58 : decode_any W_94a58 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a5c : bv 32 := 0x00d507b3.
Lemma D_94a5c : decode_any W_94a5c = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a60 : bv 32 := 0x00168693.
Lemma D_94a60 : decode_any W_94a60 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a64 : bv 32 := 0x00e78023.
Lemma D_94a64 : decode_any W_94a64 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a68 : bv 32 := 0xfed614e3.
Lemma D_94a68 : decode_any W_94a68 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a6c : bv 32 := 0x00060693.
Lemma D_94a6c : decode_any W_94a6c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a70 : bv 32 := 0x00d505b3.
Lemma D_94a70 : decode_any W_94a70 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a74 : bv 32 := 0x40d6073b.
Lemma D_94a74 : decode_any W_94a74 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a78 : bv 32 := 0x00b76733.
Lemma D_94a78 : decode_any W_94a78 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a7c : bv 32 := 0x00f77713.
Lemma D_94a7c : decode_any W_94a7c = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a80 : bv 32 := 0x00070e63.
Lemma D_94a80 : decode_any W_94a80 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a84 : bv 32 := 0x02d60863.
Lemma D_94a84 : decode_any W_94a84 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a88 : bv 32 := 0x00c50633.
Lemma D_94a88 : decode_any W_94a88 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a8c : bv 32 := 0x00058023.
Lemma D_94a8c : decode_any W_94a8c = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a90 : bv 32 := 0x00158593.
Lemma D_94a90 : decode_any W_94a90 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a94 : bv 32 := 0xfec59ce3.
Lemma D_94a94 : decode_any W_94a94 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a98 : bv 32 := 0x01c0006f.
Lemma D_94a98 : decode_any W_94a98 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a9c : bv 32 := 0x00d60c63.
Lemma D_94a9c : decode_any W_94a9c = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94aa0 : bv 32 := 0x00c50633.
Lemma D_94aa0 : decode_any W_94aa0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94aa4 : bv 32 := 0x0005b023.
Lemma D_94aa4 : decode_any W_94aa4 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94aa8 : bv 32 := 0x0005b423.
Lemma D_94aa8 : decode_any W_94aa8 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94aac : bv 32 := 0x01058593.
Lemma D_94aac : decode_any W_94aac = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ab0 : bv 32 := 0xfec5eae3.
Lemma D_94ab0 : decode_any W_94ab0 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ab4 : bv 32 := 0x00008067.
Lemma D_94ab4 : decode_any W_94ab4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_80828 : bv 32 := 0x00200613.
Lemma D_80828 : decode_any W_80828 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8082c : bv 32 := 0x14c5ea63.
Lemma D_8082c : decode_any W_8082c = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80830 : bv 32 := 0x00100613.
Lemma D_80830 : decode_any W_80830 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80834 : bv 32 := 0x00100693.
Lemma D_80834 : decode_any W_80834 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80838 : bv 32 := 0x00c0006f.
Lemma D_80838 : decode_any W_80838 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8083c : bv 32 := 0x00160613.
Lemma D_8083c : decode_any W_8083c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80840 : bv 32 := 0x12b60c63.
Lemma D_80840 : decode_any W_80840 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80844 : bv 32 := 0x00461713.
Lemma D_80844 : decode_any W_80844 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80848 : bv 32 := 0x00e50733.
Lemma D_80848 : decode_any W_80848 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8084c : bv 32 := 0x00072703.
Lemma D_8084c : decode_any W_8084c = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80850 : bv 32 := 0x00060893.
Lemma D_80850 : decode_any W_80850 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80854 : bv 32 := 0xfff88793.
Lemma D_80854 : decode_any W_80854 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80858 : bv 32 := 0x0017d813.
Lemma D_80858 : decode_any W_80858 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8085c : bv 32 := 0x00481293.
Lemma D_8085c : decode_any W_8085c = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80860 : bv 32 := 0x005502b3.
Lemma D_80860 : decode_any W_80860 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80864 : bv 32 := 0x0002a303.
Lemma D_80864 : decode_any W_80864 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80868 : bv 32 := 0xfce37ae3.
Lemma D_80868 : decode_any W_80868 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8086c : bv 32 := 0x0002b303.
Lemma D_8086c : decode_any W_8086c = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80870 : bv 32 := 0x00489893.
Lemma D_80870 : decode_any W_80870 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80874 : bv 32 := 0x011508b3.
Lemma D_80874 : decode_any W_80874 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80878 : bv 32 := 0x0048a383.
Lemma D_80878 : decode_any W_80878 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8087c : bv 32 := 0x0068b023.
Lemma D_8087c : decode_any W_8087c = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80880 : bv 32 := 0x0082b303.
Lemma D_80880 : decode_any W_80880 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80884 : bv 32 := 0x0088be03.
Lemma D_80884 : decode_any W_80884 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80888 : bv 32 := 0x0068b423.
Lemma D_80888 : decode_any W_80888 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8088c : bv 32 := 0x00e2a023.
Lemma D_8088c : decode_any W_8088c = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80890 : bv 32 := 0x0072a223.
Lemma D_80890 : decode_any W_80890 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80894 : bv 32 := 0x01c2b423.
Lemma D_80894 : decode_any W_80894 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80898 : bv 32 := 0x00080893.
Lemma D_80898 : decode_any W_80898 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8089c : bv 32 := 0xfaf6ece3.
Lemma D_8089c : decode_any W_8089c = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808a0 : bv 32 := 0xf9dff06f.
Lemma D_808a0 : decode_any W_808a0 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808a4 : bv 32 := 0x00000613.
Lemma D_808a4 : decode_any W_808a4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808a8 : bv 32 := 0x00459693.
Lemma D_808a8 : decode_any W_808a8 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808ac : bv 32 := 0x00d506b3.
Lemma D_808ac : decode_any W_808ac = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808b0 : bv 32 := 0x0006b703.
Lemma D_808b0 : decode_any W_808b0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808b4 : bv 32 := 0x0086b783.
Lemma D_808b4 : decode_any W_808b4 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808b8 : bv 32 := 0x00053803.
Lemma D_808b8 : decode_any W_808b8 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808bc : bv 32 := 0x00853883.
Lemma D_808bc : decode_any W_808bc = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808c0 : bv 32 := 0x00e53023.
Lemma D_808c0 : decode_any W_808c0 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808c4 : bv 32 := 0x00f53423.
Lemma D_808c4 : decode_any W_808c4 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808c8 : bv 32 := 0x0106b023.
Lemma D_808c8 : decode_any W_808c8 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808cc : bv 32 := 0x0116b423.
Lemma D_808cc : decode_any W_808cc = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808d0 : bv 32 := 0x00000693.
Lemma D_808d0 : decode_any W_808d0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808d4 : bv 32 := 0x00161793.
Lemma D_808d4 : decode_any W_808d4 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808d8 : bv 32 := 0x00178813.
Lemma D_808d8 : decode_any W_808d8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808dc : bv 32 := 0x00461713.
Lemma D_808dc : decode_any W_808dc = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808e0 : bv 32 := 0x00b86a63.
Lemma D_808e0 : decode_any W_808e0 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808e4 : bv 32 := 0x00278793.
Lemma D_808e4 : decode_any W_808e4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808e8 : bv 32 := 0x02b7ea63.
Lemma D_808e8 : decode_any W_808e8 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808ec : bv 32 := 0x04c69c63.
Lemma D_808ec : decode_any W_808ec = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808f0 : bv 32 := 0x0880006f.
Lemma D_808f0 : decode_any W_808f0 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808f4 : bv 32 := 0x00e506b3.
Lemma D_808f4 : decode_any W_808f4 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808f8 : bv 32 := 0x00481893.
Lemma D_808f8 : decode_any W_808f8 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_808fc : bv 32 := 0x011508b3.
Lemma D_808fc : decode_any W_808fc = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80900 : bv 32 := 0x0006a683.
Lemma D_80900 : decode_any W_80900 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80904 : bv 32 := 0x0008a883.
Lemma D_80904 : decode_any W_80904 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80908 : bv 32 := 0x0116e463.
Lemma D_80908 : decode_any W_80908 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8090c : bv 32 := 0x00060813.
Lemma D_8090c : decode_any W_8090c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80910 : bv 32 := 0x00080693.
Lemma D_80910 : decode_any W_80910 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80914 : bv 32 := 0x00278793.
Lemma D_80914 : decode_any W_80914 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80918 : bv 32 := 0xfcb7fae3.
Lemma D_80918 : decode_any W_80918 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8091c : bv 32 := 0x00469813.
Lemma D_8091c : decode_any W_8091c = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80920 : bv 32 := 0x00479893.
Lemma D_80920 : decode_any W_80920 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80924 : bv 32 := 0x01050833.
Lemma D_80924 : decode_any W_80924 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80928 : bv 32 := 0x011508b3.
Lemma D_80928 : decode_any W_80928 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8092c : bv 32 := 0x00082803.
Lemma D_8092c : decode_any W_8092c = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80930 : bv 32 := 0x0008a883.
Lemma D_80930 : decode_any W_80930 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80934 : bv 32 := 0x01186463.
Lemma D_80934 : decode_any W_80934 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80938 : bv 32 := 0x00068793.
Lemma D_80938 : decode_any W_80938 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8093c : bv 32 := 0x00078693.
Lemma D_8093c : decode_any W_8093c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80940 : bv 32 := 0x02c78c63.
Lemma D_80940 : decode_any W_80940 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80944 : bv 32 := 0x00469613.
Lemma D_80944 : decode_any W_80944 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80948 : bv 32 := 0x00c50633.
Lemma D_80948 : decode_any W_80948 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8094c : bv 32 := 0x00063783.
Lemma D_8094c : decode_any W_8094c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80950 : bv 32 := 0x00e50733.
Lemma D_80950 : decode_any W_80950 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80954 : bv 32 := 0x00073803.
Lemma D_80954 : decode_any W_80954 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80958 : bv 32 := 0x00873883.
Lemma D_80958 : decode_any W_80958 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8095c : bv 32 := 0x00f73023.
Lemma D_8095c : decode_any W_8095c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80960 : bv 32 := 0x00863783.
Lemma D_80960 : decode_any W_80960 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80964 : bv 32 := 0x00f73423.
Lemma D_80964 : decode_any W_80964 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80968 : bv 32 := 0x01063023.
Lemma D_80968 : decode_any W_80968 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8096c : bv 32 := 0x01163423.
Lemma D_8096c : decode_any W_8096c = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80970 : bv 32 := 0x00068613.
Lemma D_80970 : decode_any W_80970 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80974 : bv 32 := 0xf6b6e0e3.
Lemma D_80974 : decode_any W_80974 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80978 : bv 32 := 0xfff58593.
Lemma D_80978 : decode_any W_80978 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8097c : bv 32 := 0xf20594e3.
Lemma D_8097c : decode_any W_8097c = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80980 : bv 32 := 0x00008067.
Lemma D_80980 : decode_any W_80980 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
