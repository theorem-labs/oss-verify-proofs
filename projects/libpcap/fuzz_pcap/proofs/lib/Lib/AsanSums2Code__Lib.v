(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AsanSums2Code.
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
Definition W_e4b9c : bv 32 := 0x06060663.
Lemma D_e4b9c : decode_any W_e4b9c = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4ba0 : bv 32 := 0x00000693.
Lemma D_e4ba0 : decode_any W_e4ba0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4ba4 : bv 32 := 0x00d58733.
Lemma D_e4ba4 : decode_any W_e4ba4 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4ba8 : bv 32 := 0x00074703.
Lemma D_e4ba8 : decode_any W_e4ba8 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bac : bv 32 := 0x00070c63.
Lemma D_e4bac : decode_any W_e4bac = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bb0 : bv 32 := 0x00d507b3.
Lemma D_e4bb0 : decode_any W_e4bb0 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bb4 : bv 32 := 0x00168693.
Lemma D_e4bb4 : decode_any W_e4bb4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bb8 : bv 32 := 0x00e78023.
Lemma D_e4bb8 : decode_any W_e4bb8 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bbc : bv 32 := 0xfed614e3.
Lemma D_e4bbc : decode_any W_e4bbc = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bc0 : bv 32 := 0x00060693.
Lemma D_e4bc0 : decode_any W_e4bc0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bc4 : bv 32 := 0x00d505b3.
Lemma D_e4bc4 : decode_any W_e4bc4 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bc8 : bv 32 := 0x40d6073b.
Lemma D_e4bc8 : decode_any W_e4bc8 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bcc : bv 32 := 0x00b76733.
Lemma D_e4bcc : decode_any W_e4bcc = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bd0 : bv 32 := 0x00f77713.
Lemma D_e4bd0 : decode_any W_e4bd0 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bd4 : bv 32 := 0x00070e63.
Lemma D_e4bd4 : decode_any W_e4bd4 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bd8 : bv 32 := 0x02d60863.
Lemma D_e4bd8 : decode_any W_e4bd8 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bdc : bv 32 := 0x00c50633.
Lemma D_e4bdc : decode_any W_e4bdc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4be0 : bv 32 := 0x00058023.
Lemma D_e4be0 : decode_any W_e4be0 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4be4 : bv 32 := 0x00158593.
Lemma D_e4be4 : decode_any W_e4be4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4be8 : bv 32 := 0xfec59ce3.
Lemma D_e4be8 : decode_any W_e4be8 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bec : bv 32 := 0x01c0006f.
Lemma D_e4bec : decode_any W_e4bec = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bf0 : bv 32 := 0x00d60c63.
Lemma D_e4bf0 : decode_any W_e4bf0 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bf4 : bv 32 := 0x00c50633.
Lemma D_e4bf4 : decode_any W_e4bf4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bf8 : bv 32 := 0x0005b023.
Lemma D_e4bf8 : decode_any W_e4bf8 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4bfc : bv 32 := 0x0005b423.
Lemma D_e4bfc : decode_any W_e4bfc = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4c00 : bv 32 := 0x01058593.
Lemma D_e4c00 : decode_any W_e4c00 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4c04 : bv 32 := 0xfec5eae3.
Lemma D_e4c04 : decode_any W_e4c04 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4c08 : bv 32 := 0x00008067.
Lemma D_e4c08 : decode_any W_e4c08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_cb8c8 : bv 32 := 0x00200613.
Lemma D_cb8c8 : decode_any W_cb8c8 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8cc : bv 32 := 0x14c5ea63.
Lemma D_cb8cc : decode_any W_cb8cc = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8d0 : bv 32 := 0x00100613.
Lemma D_cb8d0 : decode_any W_cb8d0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8d4 : bv 32 := 0x00100693.
Lemma D_cb8d4 : decode_any W_cb8d4 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8d8 : bv 32 := 0x00c0006f.
Lemma D_cb8d8 : decode_any W_cb8d8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8dc : bv 32 := 0x00160613.
Lemma D_cb8dc : decode_any W_cb8dc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8e0 : bv 32 := 0x12b60c63.
Lemma D_cb8e0 : decode_any W_cb8e0 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8e4 : bv 32 := 0x00461713.
Lemma D_cb8e4 : decode_any W_cb8e4 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8e8 : bv 32 := 0x00e50733.
Lemma D_cb8e8 : decode_any W_cb8e8 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8ec : bv 32 := 0x00072703.
Lemma D_cb8ec : decode_any W_cb8ec = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8f0 : bv 32 := 0x00060893.
Lemma D_cb8f0 : decode_any W_cb8f0 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8f4 : bv 32 := 0xfff88793.
Lemma D_cb8f4 : decode_any W_cb8f4 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8f8 : bv 32 := 0x0017d813.
Lemma D_cb8f8 : decode_any W_cb8f8 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8fc : bv 32 := 0x00481293.
Lemma D_cb8fc : decode_any W_cb8fc = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb900 : bv 32 := 0x005502b3.
Lemma D_cb900 : decode_any W_cb900 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb904 : bv 32 := 0x0002a303.
Lemma D_cb904 : decode_any W_cb904 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb908 : bv 32 := 0xfce37ae3.
Lemma D_cb908 : decode_any W_cb908 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb90c : bv 32 := 0x0002b303.
Lemma D_cb90c : decode_any W_cb90c = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb910 : bv 32 := 0x00489893.
Lemma D_cb910 : decode_any W_cb910 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb914 : bv 32 := 0x011508b3.
Lemma D_cb914 : decode_any W_cb914 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb918 : bv 32 := 0x0048a383.
Lemma D_cb918 : decode_any W_cb918 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb91c : bv 32 := 0x0068b023.
Lemma D_cb91c : decode_any W_cb91c = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb920 : bv 32 := 0x0082b303.
Lemma D_cb920 : decode_any W_cb920 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb924 : bv 32 := 0x0088be03.
Lemma D_cb924 : decode_any W_cb924 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb928 : bv 32 := 0x0068b423.
Lemma D_cb928 : decode_any W_cb928 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb92c : bv 32 := 0x00e2a023.
Lemma D_cb92c : decode_any W_cb92c = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb930 : bv 32 := 0x0072a223.
Lemma D_cb930 : decode_any W_cb930 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb934 : bv 32 := 0x01c2b423.
Lemma D_cb934 : decode_any W_cb934 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb938 : bv 32 := 0x00080893.
Lemma D_cb938 : decode_any W_cb938 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb93c : bv 32 := 0xfaf6ece3.
Lemma D_cb93c : decode_any W_cb93c = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb940 : bv 32 := 0xf9dff06f.
Lemma D_cb940 : decode_any W_cb940 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb944 : bv 32 := 0x00000613.
Lemma D_cb944 : decode_any W_cb944 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb948 : bv 32 := 0x00459693.
Lemma D_cb948 : decode_any W_cb948 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb94c : bv 32 := 0x00d506b3.
Lemma D_cb94c : decode_any W_cb94c = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb950 : bv 32 := 0x0006b703.
Lemma D_cb950 : decode_any W_cb950 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb954 : bv 32 := 0x0086b783.
Lemma D_cb954 : decode_any W_cb954 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb958 : bv 32 := 0x00053803.
Lemma D_cb958 : decode_any W_cb958 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb95c : bv 32 := 0x00853883.
Lemma D_cb95c : decode_any W_cb95c = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb960 : bv 32 := 0x00e53023.
Lemma D_cb960 : decode_any W_cb960 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb964 : bv 32 := 0x00f53423.
Lemma D_cb964 : decode_any W_cb964 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb968 : bv 32 := 0x0106b023.
Lemma D_cb968 : decode_any W_cb968 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb96c : bv 32 := 0x0116b423.
Lemma D_cb96c : decode_any W_cb96c = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb970 : bv 32 := 0x00000693.
Lemma D_cb970 : decode_any W_cb970 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb974 : bv 32 := 0x00161793.
Lemma D_cb974 : decode_any W_cb974 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb978 : bv 32 := 0x00178813.
Lemma D_cb978 : decode_any W_cb978 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb97c : bv 32 := 0x00461713.
Lemma D_cb97c : decode_any W_cb97c = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb980 : bv 32 := 0x00b86a63.
Lemma D_cb980 : decode_any W_cb980 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb984 : bv 32 := 0x00278793.
Lemma D_cb984 : decode_any W_cb984 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb988 : bv 32 := 0x02b7ea63.
Lemma D_cb988 : decode_any W_cb988 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb98c : bv 32 := 0x04c69c63.
Lemma D_cb98c : decode_any W_cb98c = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb990 : bv 32 := 0x0880006f.
Lemma D_cb990 : decode_any W_cb990 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb994 : bv 32 := 0x00e506b3.
Lemma D_cb994 : decode_any W_cb994 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb998 : bv 32 := 0x00481893.
Lemma D_cb998 : decode_any W_cb998 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb99c : bv 32 := 0x011508b3.
Lemma D_cb99c : decode_any W_cb99c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9a0 : bv 32 := 0x0006a683.
Lemma D_cb9a0 : decode_any W_cb9a0 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9a4 : bv 32 := 0x0008a883.
Lemma D_cb9a4 : decode_any W_cb9a4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9a8 : bv 32 := 0x0116e463.
Lemma D_cb9a8 : decode_any W_cb9a8 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9ac : bv 32 := 0x00060813.
Lemma D_cb9ac : decode_any W_cb9ac = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9b0 : bv 32 := 0x00080693.
Lemma D_cb9b0 : decode_any W_cb9b0 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9b4 : bv 32 := 0x00278793.
Lemma D_cb9b4 : decode_any W_cb9b4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9b8 : bv 32 := 0xfcb7fae3.
Lemma D_cb9b8 : decode_any W_cb9b8 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9bc : bv 32 := 0x00469813.
Lemma D_cb9bc : decode_any W_cb9bc = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9c0 : bv 32 := 0x00479893.
Lemma D_cb9c0 : decode_any W_cb9c0 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9c4 : bv 32 := 0x01050833.
Lemma D_cb9c4 : decode_any W_cb9c4 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9c8 : bv 32 := 0x011508b3.
Lemma D_cb9c8 : decode_any W_cb9c8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9cc : bv 32 := 0x00082803.
Lemma D_cb9cc : decode_any W_cb9cc = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9d0 : bv 32 := 0x0008a883.
Lemma D_cb9d0 : decode_any W_cb9d0 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9d4 : bv 32 := 0x01186463.
Lemma D_cb9d4 : decode_any W_cb9d4 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9d8 : bv 32 := 0x00068793.
Lemma D_cb9d8 : decode_any W_cb9d8 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9dc : bv 32 := 0x00078693.
Lemma D_cb9dc : decode_any W_cb9dc = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9e0 : bv 32 := 0x02c78c63.
Lemma D_cb9e0 : decode_any W_cb9e0 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9e4 : bv 32 := 0x00469613.
Lemma D_cb9e4 : decode_any W_cb9e4 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9e8 : bv 32 := 0x00c50633.
Lemma D_cb9e8 : decode_any W_cb9e8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9ec : bv 32 := 0x00063783.
Lemma D_cb9ec : decode_any W_cb9ec = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9f0 : bv 32 := 0x00e50733.
Lemma D_cb9f0 : decode_any W_cb9f0 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9f4 : bv 32 := 0x00073803.
Lemma D_cb9f4 : decode_any W_cb9f4 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9f8 : bv 32 := 0x00873883.
Lemma D_cb9f8 : decode_any W_cb9f8 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9fc : bv 32 := 0x00f73023.
Lemma D_cb9fc : decode_any W_cb9fc = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba00 : bv 32 := 0x00863783.
Lemma D_cba00 : decode_any W_cba00 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba04 : bv 32 := 0x00f73423.
Lemma D_cba04 : decode_any W_cba04 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba08 : bv 32 := 0x01063023.
Lemma D_cba08 : decode_any W_cba08 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba0c : bv 32 := 0x01163423.
Lemma D_cba0c : decode_any W_cba0c = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba10 : bv 32 := 0x00068613.
Lemma D_cba10 : decode_any W_cba10 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba14 : bv 32 := 0xf6b6e0e3.
Lemma D_cba14 : decode_any W_cba14 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba18 : bv 32 := 0xfff58593.
Lemma D_cba18 : decode_any W_cba18 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba1c : bv 32 := 0xf20594e3.
Lemma D_cba1c : decode_any W_cba1c = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba20 : bv 32 := 0x00008067.
Lemma D_cba20 : decode_any W_cba20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End AsanSums2Code.

(* [comment removed for export] *)
Module AsanSumsCode.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_e460c : bv 32 := 0x02060063.
Lemma D_e460c : decode_any W_e460c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4610 : bv 32 := 0x00c50633.
Lemma D_e4610 : decode_any W_e4610 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4614 : bv 32 := 0x00050693.
Lemma D_e4614 : decode_any W_e4614 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4618 : bv 32 := 0x0005c703.
Lemma D_e4618 : decode_any W_e4618 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e461c : bv 32 := 0x00e68023.
Lemma D_e461c : decode_any W_e461c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4620 : bv 32 := 0x00168693.
Lemma D_e4620 : decode_any W_e4620 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4624 : bv 32 := 0x00158593.
Lemma D_e4624 : decode_any W_e4624 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4628 : bv 32 := 0xfec698e3.
Lemma D_e4628 : decode_any W_e4628 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e462c : bv 32 := 0x00008067.
Lemma D_e462c : decode_any W_e462c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4688 : bv 32 := 0x00a666b3.
Lemma D_e4688 : decode_any W_e4688 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e468c : bv 32 := 0x00f6f693.
Lemma D_e468c : decode_any W_e468c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4690 : bv 32 := 0x02068063.
Lemma D_e4690 : decode_any W_e4690 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4694 : bv 32 := 0x04060863.
Lemma D_e4694 : decode_any W_e4694 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4698 : bv 32 := 0x00c50633.
Lemma D_e4698 : decode_any W_e4698 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e469c : bv 32 := 0x00050693.
Lemma D_e469c : decode_any W_e469c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46a0 : bv 32 := 0x00b68023.
Lemma D_e46a0 : decode_any W_e46a0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46a4 : bv 32 := 0x00168693.
Lemma D_e46a4 : decode_any W_e46a4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46a8 : bv 32 := 0xfec69ce3.
Lemma D_e46a8 : decode_any W_e46a8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46ac : bv 32 := 0x0380006f.
Lemma D_e46ac : decode_any W_e46ac = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46b0 : bv 32 := 0x02060a63.
Lemma D_e46b0 : decode_any W_e46b0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46b4 : bv 32 := 0x00c50633.
Lemma D_e46b4 : decode_any W_e46b4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46b8 : bv 32 := 0x00859693.
Lemma D_e46b8 : decode_any W_e46b8 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46bc : bv 32 := 0x00b6e5b3.
Lemma D_e46bc : decode_any W_e46bc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46c0 : bv 32 := 0x01059693.
Lemma D_e46c0 : decode_any W_e46c0 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46c4 : bv 32 := 0x00b6e5b3.
Lemma D_e46c4 : decode_any W_e46c4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46c8 : bv 32 := 0x02059693.
Lemma D_e46c8 : decode_any W_e46c8 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46cc : bv 32 := 0x00b6e5b3.
Lemma D_e46cc : decode_any W_e46cc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46d0 : bv 32 := 0x00050693.
Lemma D_e46d0 : decode_any W_e46d0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46d4 : bv 32 := 0x00b6b023.
Lemma D_e46d4 : decode_any W_e46d4 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46d8 : bv 32 := 0x00b6b423.
Lemma D_e46d8 : decode_any W_e46d8 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46dc : bv 32 := 0x01068693.
Lemma D_e46dc : decode_any W_e46dc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46e0 : bv 32 := 0xfec6eae3.
Lemma D_e46e0 : decode_any W_e46e0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e46e4 : bv 32 := 0x00008067.
Lemma D_e46e4 : decode_any W_e46e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4cec : bv 32 := 0xff010113.
Lemma D_e4cec : decode_any W_e4cec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4cf0 : bv 32 := 0x00113423.
Lemma D_e4cf0 : decode_any W_e4cf0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4cf4 : bv 32 := 0x00058693.
Lemma D_e4cf4 : decode_any W_e4cf4 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4cf8 : bv 32 := 0x00100713.
Lemma D_e4cf8 : decode_any W_e4cf8 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4cfc : bv 32 := 0x02871713.
Lemma D_e4cfc : decode_any W_e4cfc = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d00 : bv 32 := 0x00170593.
Lemma D_e4d00 : decode_any W_e4d00 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d04 : bv 32 := 0x08b6f263.
Lemma D_e4d04 : decode_any W_e4d04 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d08 : bv 32 := 0x00000593.
Lemma D_e4d08 : decode_any W_e4d08 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d0c : bv 32 := 0x00d50733.
Lemma D_e4d0c : decode_any W_e4d0c = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d10 : bv 32 := 0x00750793.
Lemma D_e4d10 : decode_any W_e4d10 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d14 : bv 32 := 0xff87f793.
Lemma D_e4d14 : decode_any W_e4d14 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d18 : bv 32 := 0xff877613.
Lemma D_e4d18 : decode_any W_e4d18 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d1c : bv 32 := 0x02f57463.
Lemma D_e4d1c : decode_any W_e4d1c = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d20 : bv 32 := 0x02068263.
Lemma D_e4d20 : decode_any W_e4d20 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d24 : bv 32 := 0x00000593.
Lemma D_e4d24 : decode_any W_e4d24 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d28 : bv 32 := 0x00150693.
Lemma D_e4d28 : decode_any W_e4d28 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d2c : bv 32 := 0x00068813.
Lemma D_e4d2c : decode_any W_e4d2c = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d30 : bv 32 := 0xfff6c683.
Lemma D_e4d30 : decode_any W_e4d30 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d34 : bv 32 := 0x00d5e5b3.
Lemma D_e4d34 : decode_any W_e4d34 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d38 : bv 32 := 0x00f87663.
Lemma D_e4d38 : decode_any W_e4d38 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d3c : bv 32 := 0x00180693.
Lemma D_e4d3c : decode_any W_e4d3c = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d40 : bv 32 := 0xfee866e3.
Lemma D_e4d40 : decode_any W_e4d40 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d44 : bv 32 := 0x00c7fa63.
Lemma D_e4d44 : decode_any W_e4d44 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d48 : bv 32 := 0x0007b683.
Lemma D_e4d48 : decode_any W_e4d48 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d4c : bv 32 := 0x00878793.
Lemma D_e4d4c : decode_any W_e4d4c = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d50 : bv 32 := 0x00b6e5b3.
Lemma D_e4d50 : decode_any W_e4d50 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d54 : bv 32 := 0xfec7eae3.
Lemma D_e4d54 : decode_any W_e4d54 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d58 : bv 32 := 0x02a66063.
Lemma D_e4d58 : decode_any W_e4d58 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d5c : bv 32 := 0x00e67e63.
Lemma D_e4d5c : decode_any W_e4d5c = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d60 : bv 32 := 0x40c70733.
Lemma D_e4d60 : decode_any W_e4d60 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d64 : bv 32 := 0x00064503.
Lemma D_e4d64 : decode_any W_e4d64 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d68 : bv 32 := 0xfff70713.
Lemma D_e4d68 : decode_any W_e4d68 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d6c : bv 32 := 0x00a5e5b3.
Lemma D_e4d6c : decode_any W_e4d6c = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d70 : bv 32 := 0x00160613.
Lemma D_e4d70 : decode_any W_e4d70 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d74 : bv 32 := 0xfe0718e3.
Lemma D_e4d74 : decode_any W_e4d74 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d78 : bv 32 := 0x0015b513.
Lemma D_e4d78 : decode_any W_e4d78 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d7c : bv 32 := 0x00813083.
Lemma D_e4d7c : decode_any W_e4d7c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d80 : bv 32 := 0x01010113.
Lemma D_e4d80 : decode_any W_e4d80 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e4d84 : bv 32 := 0x00008067.
Lemma D_e4d84 : decode_any W_e4d84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End AsanSumsCode.
