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
Definition W_ca930 : bv 32 := 0x06060663.
Lemma D_ca930 : decode_any W_ca930 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca934 : bv 32 := 0x00000693.
Lemma D_ca934 : decode_any W_ca934 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca938 : bv 32 := 0x00d58733.
Lemma D_ca938 : decode_any W_ca938 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca93c : bv 32 := 0x00074703.
Lemma D_ca93c : decode_any W_ca93c = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca940 : bv 32 := 0x00070c63.
Lemma D_ca940 : decode_any W_ca940 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca944 : bv 32 := 0x00d507b3.
Lemma D_ca944 : decode_any W_ca944 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca948 : bv 32 := 0x00168693.
Lemma D_ca948 : decode_any W_ca948 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca94c : bv 32 := 0x00e78023.
Lemma D_ca94c : decode_any W_ca94c = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca950 : bv 32 := 0xfed614e3.
Lemma D_ca950 : decode_any W_ca950 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca954 : bv 32 := 0x00060693.
Lemma D_ca954 : decode_any W_ca954 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca958 : bv 32 := 0x00d505b3.
Lemma D_ca958 : decode_any W_ca958 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca95c : bv 32 := 0x40d6073b.
Lemma D_ca95c : decode_any W_ca95c = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca960 : bv 32 := 0x00b76733.
Lemma D_ca960 : decode_any W_ca960 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca964 : bv 32 := 0x00f77713.
Lemma D_ca964 : decode_any W_ca964 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca968 : bv 32 := 0x00070e63.
Lemma D_ca968 : decode_any W_ca968 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca96c : bv 32 := 0x02d60863.
Lemma D_ca96c : decode_any W_ca96c = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca970 : bv 32 := 0x00c50633.
Lemma D_ca970 : decode_any W_ca970 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca974 : bv 32 := 0x00058023.
Lemma D_ca974 : decode_any W_ca974 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca978 : bv 32 := 0x00158593.
Lemma D_ca978 : decode_any W_ca978 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca97c : bv 32 := 0xfec59ce3.
Lemma D_ca97c : decode_any W_ca97c = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca980 : bv 32 := 0x01c0006f.
Lemma D_ca980 : decode_any W_ca980 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca984 : bv 32 := 0x00d60c63.
Lemma D_ca984 : decode_any W_ca984 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca988 : bv 32 := 0x00c50633.
Lemma D_ca988 : decode_any W_ca988 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca98c : bv 32 := 0x0005b023.
Lemma D_ca98c : decode_any W_ca98c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca990 : bv 32 := 0x0005b423.
Lemma D_ca990 : decode_any W_ca990 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca994 : bv 32 := 0x01058593.
Lemma D_ca994 : decode_any W_ca994 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca998 : bv 32 := 0xfec5eae3.
Lemma D_ca998 : decode_any W_ca998 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca99c : bv 32 := 0x00008067.
Lemma D_ca99c : decode_any W_ca99c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_b6b5c : bv 32 := 0x00200613.
Lemma D_b6b5c : decode_any W_b6b5c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b60 : bv 32 := 0x14c5ea63.
Lemma D_b6b60 : decode_any W_b6b60 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b64 : bv 32 := 0x00100613.
Lemma D_b6b64 : decode_any W_b6b64 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b68 : bv 32 := 0x00100693.
Lemma D_b6b68 : decode_any W_b6b68 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b6c : bv 32 := 0x00c0006f.
Lemma D_b6b6c : decode_any W_b6b6c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b70 : bv 32 := 0x00160613.
Lemma D_b6b70 : decode_any W_b6b70 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b74 : bv 32 := 0x12b60c63.
Lemma D_b6b74 : decode_any W_b6b74 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b78 : bv 32 := 0x00461713.
Lemma D_b6b78 : decode_any W_b6b78 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b7c : bv 32 := 0x00e50733.
Lemma D_b6b7c : decode_any W_b6b7c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b80 : bv 32 := 0x00072703.
Lemma D_b6b80 : decode_any W_b6b80 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b84 : bv 32 := 0x00060893.
Lemma D_b6b84 : decode_any W_b6b84 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b88 : bv 32 := 0xfff88793.
Lemma D_b6b88 : decode_any W_b6b88 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b8c : bv 32 := 0x0017d813.
Lemma D_b6b8c : decode_any W_b6b8c = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b90 : bv 32 := 0x00481293.
Lemma D_b6b90 : decode_any W_b6b90 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b94 : bv 32 := 0x005502b3.
Lemma D_b6b94 : decode_any W_b6b94 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b98 : bv 32 := 0x0002a303.
Lemma D_b6b98 : decode_any W_b6b98 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b9c : bv 32 := 0xfce37ae3.
Lemma D_b6b9c : decode_any W_b6b9c = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ba0 : bv 32 := 0x0002b303.
Lemma D_b6ba0 : decode_any W_b6ba0 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ba4 : bv 32 := 0x00489893.
Lemma D_b6ba4 : decode_any W_b6ba4 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ba8 : bv 32 := 0x011508b3.
Lemma D_b6ba8 : decode_any W_b6ba8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bac : bv 32 := 0x0048a383.
Lemma D_b6bac : decode_any W_b6bac = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bb0 : bv 32 := 0x0068b023.
Lemma D_b6bb0 : decode_any W_b6bb0 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bb4 : bv 32 := 0x0082b303.
Lemma D_b6bb4 : decode_any W_b6bb4 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bb8 : bv 32 := 0x0088be03.
Lemma D_b6bb8 : decode_any W_b6bb8 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bbc : bv 32 := 0x0068b423.
Lemma D_b6bbc : decode_any W_b6bbc = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bc0 : bv 32 := 0x00e2a023.
Lemma D_b6bc0 : decode_any W_b6bc0 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bc4 : bv 32 := 0x0072a223.
Lemma D_b6bc4 : decode_any W_b6bc4 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bc8 : bv 32 := 0x01c2b423.
Lemma D_b6bc8 : decode_any W_b6bc8 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bcc : bv 32 := 0x00080893.
Lemma D_b6bcc : decode_any W_b6bcc = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bd0 : bv 32 := 0xfaf6ece3.
Lemma D_b6bd0 : decode_any W_b6bd0 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bd4 : bv 32 := 0xf9dff06f.
Lemma D_b6bd4 : decode_any W_b6bd4 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bd8 : bv 32 := 0x00000613.
Lemma D_b6bd8 : decode_any W_b6bd8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bdc : bv 32 := 0x00459693.
Lemma D_b6bdc : decode_any W_b6bdc = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6be0 : bv 32 := 0x00d506b3.
Lemma D_b6be0 : decode_any W_b6be0 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6be4 : bv 32 := 0x0006b703.
Lemma D_b6be4 : decode_any W_b6be4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6be8 : bv 32 := 0x0086b783.
Lemma D_b6be8 : decode_any W_b6be8 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bec : bv 32 := 0x00053803.
Lemma D_b6bec : decode_any W_b6bec = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bf0 : bv 32 := 0x00853883.
Lemma D_b6bf0 : decode_any W_b6bf0 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bf4 : bv 32 := 0x00e53023.
Lemma D_b6bf4 : decode_any W_b6bf4 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bf8 : bv 32 := 0x00f53423.
Lemma D_b6bf8 : decode_any W_b6bf8 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bfc : bv 32 := 0x0106b023.
Lemma D_b6bfc : decode_any W_b6bfc = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c00 : bv 32 := 0x0116b423.
Lemma D_b6c00 : decode_any W_b6c00 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c04 : bv 32 := 0x00000693.
Lemma D_b6c04 : decode_any W_b6c04 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c08 : bv 32 := 0x00161793.
Lemma D_b6c08 : decode_any W_b6c08 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c0c : bv 32 := 0x00178813.
Lemma D_b6c0c : decode_any W_b6c0c = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c10 : bv 32 := 0x00461713.
Lemma D_b6c10 : decode_any W_b6c10 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c14 : bv 32 := 0x00b86a63.
Lemma D_b6c14 : decode_any W_b6c14 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c18 : bv 32 := 0x00278793.
Lemma D_b6c18 : decode_any W_b6c18 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c1c : bv 32 := 0x02b7ea63.
Lemma D_b6c1c : decode_any W_b6c1c = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c20 : bv 32 := 0x04c69c63.
Lemma D_b6c20 : decode_any W_b6c20 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c24 : bv 32 := 0x0880006f.
Lemma D_b6c24 : decode_any W_b6c24 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c28 : bv 32 := 0x00e506b3.
Lemma D_b6c28 : decode_any W_b6c28 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c2c : bv 32 := 0x00481893.
Lemma D_b6c2c : decode_any W_b6c2c = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c30 : bv 32 := 0x011508b3.
Lemma D_b6c30 : decode_any W_b6c30 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c34 : bv 32 := 0x0006a683.
Lemma D_b6c34 : decode_any W_b6c34 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c38 : bv 32 := 0x0008a883.
Lemma D_b6c38 : decode_any W_b6c38 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c3c : bv 32 := 0x0116e463.
Lemma D_b6c3c : decode_any W_b6c3c = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c40 : bv 32 := 0x00060813.
Lemma D_b6c40 : decode_any W_b6c40 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c44 : bv 32 := 0x00080693.
Lemma D_b6c44 : decode_any W_b6c44 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c48 : bv 32 := 0x00278793.
Lemma D_b6c48 : decode_any W_b6c48 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c4c : bv 32 := 0xfcb7fae3.
Lemma D_b6c4c : decode_any W_b6c4c = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c50 : bv 32 := 0x00469813.
Lemma D_b6c50 : decode_any W_b6c50 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c54 : bv 32 := 0x00479893.
Lemma D_b6c54 : decode_any W_b6c54 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c58 : bv 32 := 0x01050833.
Lemma D_b6c58 : decode_any W_b6c58 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c5c : bv 32 := 0x011508b3.
Lemma D_b6c5c : decode_any W_b6c5c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c60 : bv 32 := 0x00082803.
Lemma D_b6c60 : decode_any W_b6c60 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c64 : bv 32 := 0x0008a883.
Lemma D_b6c64 : decode_any W_b6c64 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c68 : bv 32 := 0x01186463.
Lemma D_b6c68 : decode_any W_b6c68 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c6c : bv 32 := 0x00068793.
Lemma D_b6c6c : decode_any W_b6c6c = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c70 : bv 32 := 0x00078693.
Lemma D_b6c70 : decode_any W_b6c70 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c74 : bv 32 := 0x02c78c63.
Lemma D_b6c74 : decode_any W_b6c74 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c78 : bv 32 := 0x00469613.
Lemma D_b6c78 : decode_any W_b6c78 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c7c : bv 32 := 0x00c50633.
Lemma D_b6c7c : decode_any W_b6c7c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c80 : bv 32 := 0x00063783.
Lemma D_b6c80 : decode_any W_b6c80 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c84 : bv 32 := 0x00e50733.
Lemma D_b6c84 : decode_any W_b6c84 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c88 : bv 32 := 0x00073803.
Lemma D_b6c88 : decode_any W_b6c88 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c8c : bv 32 := 0x00873883.
Lemma D_b6c8c : decode_any W_b6c8c = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c90 : bv 32 := 0x00f73023.
Lemma D_b6c90 : decode_any W_b6c90 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c94 : bv 32 := 0x00863783.
Lemma D_b6c94 : decode_any W_b6c94 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c98 : bv 32 := 0x00f73423.
Lemma D_b6c98 : decode_any W_b6c98 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6c9c : bv 32 := 0x01063023.
Lemma D_b6c9c : decode_any W_b6c9c = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ca0 : bv 32 := 0x01163423.
Lemma D_b6ca0 : decode_any W_b6ca0 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ca4 : bv 32 := 0x00068613.
Lemma D_b6ca4 : decode_any W_b6ca4 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ca8 : bv 32 := 0xf6b6e0e3.
Lemma D_b6ca8 : decode_any W_b6ca8 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6cac : bv 32 := 0xfff58593.
Lemma D_b6cac : decode_any W_b6cac = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6cb0 : bv 32 := 0xf20594e3.
Lemma D_b6cb0 : decode_any W_b6cb0 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6cb4 : bv 32 := 0x00008067.
Lemma D_b6cb4 : decode_any W_b6cb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
