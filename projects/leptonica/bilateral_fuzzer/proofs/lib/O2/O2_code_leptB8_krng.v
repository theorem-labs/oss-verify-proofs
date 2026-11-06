(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2ca64 : bv 32 := 0x06050863.
Lemma F_2ca64 : fetch_word Plain.M.loaded_segments (0x2cabc : word) = Some W_2ca64.
Proof. vm_refl. Qed.
Lemma D_2ca64 : decode_any W_2ca64 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca68 : bv 32 := 0x0405c063.
Lemma F_2ca68 : fetch_word Plain.M.loaded_segments (0x2cac0 : word) = Some W_2ca68.
Proof. vm_refl. Qed.
Lemma D_2ca68 : decode_any W_2ca68 = Some (Branch BC_LT 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca6c : bv 32 := 0x00052683.
Lemma F_2ca6c : fetch_word Plain.M.loaded_segments (0x2cac4 : word) = Some W_2ca6c.
Proof. vm_refl. Qed.
Lemma D_2ca6c : decode_any W_2ca6c = Some (Load SZ4 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca70 : bv 32 := 0x02d5dc63.
Lemma F_2ca70 : fetch_word Plain.M.loaded_segments (0x2cac8 : word) = Some W_2ca70.
Proof. vm_refl. Qed.
Lemma D_2ca70 : decode_any W_2ca70 = Some (Branch BC_GE 11 13 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca74 : bv 32 := 0x08064663.
Lemma F_2ca74 : fetch_word Plain.M.loaded_segments (0x2cacc : word) = Some W_2ca74.
Proof. vm_refl. Qed.
Lemma D_2ca74 : decode_any W_2ca74 = Some (Branch BC_LT 12 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca78 : bv 32 := 0x00452683.
Lemma F_2ca78 : fetch_word Plain.M.loaded_segments (0x2cad0 : word) = Some W_2ca78.
Proof. vm_refl. Qed.
Lemma D_2ca78 : decode_any W_2ca78 = Some (Load SZ4 true 13 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca7c : bv 32 := 0x08d65263.
Lemma F_2ca7c : fetch_word Plain.M.loaded_segments (0x2cad4 : word) = Some W_2ca7c.
Proof. vm_refl. Qed.
Lemma D_2ca7c : decode_any W_2ca7c = Some (Branch BC_GE 12 13 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca80 : bv 32 := 0x00050693.
Lemma F_2ca80 : fetch_word Plain.M.loaded_segments (0x2cad8 : word) = Some W_2ca80.
Proof. vm_refl. Qed.
Lemma D_2ca80 : decode_any W_2ca80 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca84 : bv 32 := 0x00000513.
Lemma F_2ca84 : fetch_word Plain.M.loaded_segments (0x2cadc : word) = Some W_2ca84.
Proof. vm_refl. Qed.
Lemma D_2ca84 : decode_any W_2ca84 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca88 : bv 32 := 0x0106b683.
Lemma F_2ca88 : fetch_word Plain.M.loaded_segments (0x2cae0 : word) = Some W_2ca88.
Proof. vm_refl. Qed.
Lemma D_2ca88 : decode_any W_2ca88 = Some (Load SZ8 true 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca8c : bv 32 := 0x00359593.
Lemma F_2ca8c : fetch_word Plain.M.loaded_segments (0x2cae4 : word) = Some W_2ca8c.
Proof. vm_refl. Qed.
Lemma D_2ca8c : decode_any W_2ca8c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca90 : bv 32 := 0x00b685b3.
Lemma F_2ca90 : fetch_word Plain.M.loaded_segments (0x2cae8 : word) = Some W_2ca90.
Proof. vm_refl. Qed.
Lemma D_2ca90 : decode_any W_2ca90 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca94 : bv 32 := 0x0005b583.
Lemma F_2ca94 : fetch_word Plain.M.loaded_segments (0x2caec : word) = Some W_2ca94.
Proof. vm_refl. Qed.
Lemma D_2ca94 : decode_any W_2ca94 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca98 : bv 32 := 0x00261613.
Lemma F_2ca98 : fetch_word Plain.M.loaded_segments (0x2caf0 : word) = Some W_2ca98.
Proof. vm_refl. Qed.
Lemma D_2ca98 : decode_any W_2ca98 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ca9c : bv 32 := 0x00c585b3.
Lemma F_2ca9c : fetch_word Plain.M.loaded_segments (0x2caf4 : word) = Some W_2ca9c.
Proof. vm_refl. Qed.
Lemma D_2ca9c : decode_any W_2ca9c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2caa0 : bv 32 := 0x00a5a027.
Lemma F_2caa0 : fetch_word Plain.M.loaded_segments (0x2caf8 : word) = Some W_2caa0.
Proof. vm_refl. Qed.
Lemma D_2caa0 : decode_any W_2caa0 = Some (FStore FMT_S 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2caa4 : bv 32 := 0x00008067.
Lemma F_2caa4 : fetch_word Plain.M.loaded_segments (0x2cafc : word) = Some W_2caa4.
Proof. vm_refl. Qed.
Lemma D_2caa4 : decode_any W_2caa4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb48 : bv 32 := 0xfd010113.
Lemma F_2eb48 : fetch_word Plain.M.loaded_segments (0x2eba0 : word) = Some W_2eb48.
Proof. vm_refl. Qed.
Lemma D_2eb48 : decode_any W_2eb48 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb4c : bv 32 := 0x02113423.
Lemma F_2eb4c : fetch_word Plain.M.loaded_segments (0x2eba4 : word) = Some W_2eb4c.
Proof. vm_refl. Qed.
Lemma D_2eb4c : decode_any W_2eb4c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb50 : bv 32 := 0x02813023.
Lemma F_2eb50 : fetch_word Plain.M.loaded_segments (0x2eba8 : word) = Some W_2eb50.
Proof. vm_refl. Qed.
Lemma D_2eb50 : decode_any W_2eb50 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb54 : bv 32 := 0x00913c23.
Lemma F_2eb54 : fetch_word Plain.M.loaded_segments (0x2ebac : word) = Some W_2eb54.
Proof. vm_refl. Qed.
Lemma D_2eb54 : decode_any W_2eb54 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb58 : bv 32 := 0x01213823.
Lemma F_2eb58 : fetch_word Plain.M.loaded_segments (0x2ebb0 : word) = Some W_2eb58.
Proof. vm_refl. Qed.
Lemma D_2eb58 : decode_any W_2eb58 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb5c : bv 32 := 0x00813427.
Lemma F_2eb5c : fetch_word Plain.M.loaded_segments (0x2ebb4 : word) = Some W_2eb5c.
Proof. vm_refl. Qed.
Lemma D_2eb5c : decode_any W_2eb5c = Some (FStore FMT_D 2 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb60 : bv 32 := 0xf00007d3.
Lemma F_2eb60 : fetch_word Plain.M.loaded_segments (0x2ebb8 : word) = Some W_2eb60.
Proof. vm_refl. Qed.
Lemma D_2eb60 : decode_any W_2eb60 = Some (Fmv FMV_F_X FMT_S 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb64 : bv 32 := 0xa0f50553.
Lemma F_2eb64 : fetch_word Plain.M.loaded_segments (0x2ebbc : word) = Some W_2eb64.
Proof. vm_refl. Qed.
Lemma D_2eb64 : decode_any W_2eb64 = Some (Fcmp F_LE FMT_S 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb68 : bv 32 := 0x06051863.
Lemma F_2eb68 : fetch_word Plain.M.loaded_segments (0x2ebc0 : word) = Some W_2eb68.
Proof. vm_refl. Qed.
Lemma D_2eb68 : decode_any W_2eb68 = Some (Branch BC_NE 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb6c : bv 32 := 0x20a50453.
Lemma F_2eb6c : fetch_word Plain.M.loaded_segments (0x2ebc4 : word) = Some W_2eb6c.
Proof. vm_refl. Qed.
Lemma D_2eb6c : decode_any W_2eb6c = Some (Fsgnj F_SGNJ FMT_S 8 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb70 : bv 32 := 0x00100513.
Lemma F_2eb70 : fetch_word Plain.M.loaded_segments (0x2ebc8 : word) = Some W_2eb70.
Proof. vm_refl. Qed.
Lemma D_2eb70 : decode_any W_2eb70 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb74 : bv 32 := 0x10000593.
Lemma F_2eb74 : fetch_word Plain.M.loaded_segments (0x2ebcc : word) = Some W_2eb74.
Proof. vm_refl. Qed.
Lemma D_2eb74 : decode_any W_2eb74 = Some (OpImm ALU_ADD 11 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb78 : bv 32 := 0x10000913.
Lemma F_2eb78 : fetch_word Plain.M.loaded_segments (0x2ebd0 : word) = Some W_2eb78.
Proof. vm_refl. Qed.
Lemma D_2eb78 : decode_any W_2eb78 = Some (OpImm ALU_ADD 18 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb7c : bv 32 := 0xa29fd0ef.
Lemma F_2eb7c : fetch_word Plain.M.loaded_segments (0x2ebd4 : word) = Some W_2eb7c.
Proof. vm_refl. Qed.
Lemma D_2eb7c : decode_any W_2eb7c = Some (Jal 1 2087464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb80 : bv 32 := 0x06050c63.
Lemma F_2eb80 : fetch_word Plain.M.loaded_segments (0x2ebd8 : word) = Some W_2eb80.
Proof. vm_refl. Qed.
Lemma D_2eb80 : decode_any W_2eb80 = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb84 : bv 32 := 0x00050413.
Lemma F_2eb84 : fetch_word Plain.M.loaded_segments (0x2ebdc : word) = Some W_2eb84.
Proof. vm_refl. Qed.
Lemma D_2eb84 : decode_any W_2eb84 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb88 : bv 32 := 0x420407d3.
Lemma F_2eb88 : fetch_word Plain.M.loaded_segments (0x2ebe0 : word) = Some W_2eb88.
Proof. vm_refl. Qed.
Lemma D_2eb88 : decode_any W_2eb88 = Some (Fcvt FC_D FC_S 15 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb8c : bv 32 := 0x02f7f753.
Lemma F_2eb8c : fetch_word Plain.M.loaded_segments (0x2ebe4 : word) = Some W_2eb8c.
Proof. vm_refl. Qed.
Lemma D_2eb8c : decode_any W_2eb8c = Some (Fari F_ADD FMT_D 14 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb90 : bv 32 := 0x12f777d3.
Lemma F_2eb90 : fetch_word Plain.M.loaded_segments (0x2ebe8 : word) = Some W_2eb90.
Proof. vm_refl. Qed.
Lemma D_2eb90 : decode_any W_2eb90 = Some (Fari F_MUL FMT_D 15 14 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb94 : bv 32 := 0x4017f453.
Lemma F_2eb94 : fetch_word Plain.M.loaded_segments (0x2ebec : word) = Some W_2eb94.
Proof. vm_refl. Qed.
Lemma D_2eb94 : decode_any W_2eb94 = Some (Fcvt FC_S FC_D 8 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb98 : bv 32 := 0x00000593.
Lemma F_2eb98 : fetch_word Plain.M.loaded_segments (0x2ebf0 : word) = Some W_2eb98.
Proof. vm_refl. Qed.
Lemma D_2eb98 : decode_any W_2eb98 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb9c : bv 32 := 0x00000613.
Lemma F_2eb9c : fetch_word Plain.M.loaded_segments (0x2ebf4 : word) = Some W_2eb9c.
Proof. vm_refl. Qed.
Lemma D_2eb9c : decode_any W_2eb9c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eba0 : bv 32 := 0xf95fd0ef.
Lemma F_2eba0 : fetch_word Plain.M.loaded_segments (0x2ebf8 : word) = Some W_2eba0.
Proof. vm_refl. Qed.
Lemma D_2eba0 : decode_any W_2eba0 = Some (Jal 1 2088852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eba4 : bv 32 := 0x00000493.
Lemma F_2eba4 : fetch_word Plain.M.loaded_segments (0x2ebfc : word) = Some W_2eba4.
Proof. vm_refl. Qed.
Lemma D_2eba4 : decode_any W_2eba4 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eba8 : bv 32 := 0x02948533.
Lemma F_2eba8 : fetch_word Plain.M.loaded_segments (0x2ec00 : word) = Some W_2eba8.
Proof. vm_refl. Qed.
Lemma D_2eba8 : decode_any W_2eba8 = Some (Mul M_MUL 10 9 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ebac : bv 32 := 0xd01577d3.
Lemma F_2ebac : fetch_word Plain.M.loaded_segments (0x2ec04 : word) = Some W_2ebac.
Proof. vm_refl. Qed.
Lemma D_2ebac : decode_any W_2ebac = Some (Fcvt FC_S FC_WU 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ebb0 : bv 32 := 0x20f797d3.
Lemma F_2ebb0 : fetch_word Plain.M.loaded_segments (0x2ec08 : word) = Some W_2ebb0.
Proof. vm_refl. Qed.
Lemma D_2ebb0 : decode_any W_2ebb0 = Some (Fsgnj F_SGNJN FMT_S 15 15 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ebb4 : bv 32 := 0x1887f553.
Lemma F_2ebb4 : fetch_word Plain.M.loaded_segments (0x2ec0c : word) = Some W_2ebb4.
Proof. vm_refl. Qed.
Lemma D_2ebb4 : decode_any W_2ebb4 = Some (Fari F_DIV FMT_S 10 15 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ebb8 : bv 32 := 0x5a8020ef.
Lemma F_2ebb8 : fetch_word Plain.M.loaded_segments (0x2ec10 : word) = Some W_2ebb8.
Proof. vm_refl. Qed.
Lemma D_2ebb8 : decode_any W_2ebb8 = Some (Jal 1 9640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ebbc : bv 32 := 0x00040513.
Lemma F_2ebbc : fetch_word Plain.M.loaded_segments (0x2ec14 : word) = Some W_2ebbc.
Proof. vm_refl. Qed.
Lemma D_2ebbc : decode_any W_2ebbc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ebc0 : bv 32 := 0x00000593.
Lemma F_2ebc0 : fetch_word Plain.M.loaded_segments (0x2ec18 : word) = Some W_2ebc0.
Proof. vm_refl. Qed.
Lemma D_2ebc0 : decode_any W_2ebc0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ebc4 : bv 32 := 0x00048613.
Lemma F_2ebc4 : fetch_word Plain.M.loaded_segments (0x2ec1c : word) = Some W_2ebc4.
Proof. vm_refl. Qed.
Lemma D_2ebc4 : decode_any W_2ebc4 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ebc8 : bv 32 := 0xe9dfd0ef.
Lemma F_2ebc8 : fetch_word Plain.M.loaded_segments (0x2ec20 : word) = Some W_2ebc8.
Proof. vm_refl. Qed.
Lemma D_2ebc8 : decode_any W_2ebc8 = Some (Jal 1 2088604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ebcc : bv 32 := 0x0014849b.
Lemma F_2ebcc : fetch_word Plain.M.loaded_segments (0x2ec24 : word) = Some W_2ebcc.
Proof. vm_refl. Qed.
Lemma D_2ebcc : decode_any W_2ebcc = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ebd0 : bv 32 := 0xfd249ce3.
Lemma F_2ebd0 : fetch_word Plain.M.loaded_segments (0x2ec28 : word) = Some W_2ebd0.
Proof. vm_refl. Qed.
Lemma D_2ebd0 : decode_any W_2ebd0 = Some (Branch BC_NE 9 18 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ebd4 : bv 32 := 0x06c0006f.
Lemma F_2ebd4 : fetch_word Plain.M.loaded_segments (0x2ec2c : word) = Some W_2ebd4.
Proof. vm_refl. Qed.
Lemma D_2ebd4 : decode_any W_2ebd4 = Some (Jal 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ec40 : bv 32 := 0x00040513.
Lemma F_2ec40 : fetch_word Plain.M.loaded_segments (0x2ec98 : word) = Some W_2ec40.
Proof. vm_refl. Qed.
Lemma D_2ec40 : decode_any W_2ec40 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ec44 : bv 32 := 0x02813083.
Lemma F_2ec44 : fetch_word Plain.M.loaded_segments (0x2ec9c : word) = Some W_2ec44.
Proof. vm_refl. Qed.
Lemma D_2ec44 : decode_any W_2ec44 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ec48 : bv 32 := 0x02013403.
Lemma F_2ec48 : fetch_word Plain.M.loaded_segments (0x2eca0 : word) = Some W_2ec48.
Proof. vm_refl. Qed.
Lemma D_2ec48 : decode_any W_2ec48 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ec4c : bv 32 := 0x01813483.
Lemma F_2ec4c : fetch_word Plain.M.loaded_segments (0x2eca4 : word) = Some W_2ec4c.
Proof. vm_refl. Qed.
Lemma D_2ec4c : decode_any W_2ec4c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ec50 : bv 32 := 0x01013903.
Lemma F_2ec50 : fetch_word Plain.M.loaded_segments (0x2eca8 : word) = Some W_2ec50.
Proof. vm_refl. Qed.
Lemma D_2ec50 : decode_any W_2ec50 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ec54 : bv 32 := 0x00813407.
Lemma F_2ec54 : fetch_word Plain.M.loaded_segments (0x2ecac : word) = Some W_2ec54.
Proof. vm_refl. Qed.
Lemma D_2ec54 : decode_any W_2ec54 = Some (FLoad FMT_D 8 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ec58 : bv 32 := 0x03010113.
Lemma F_2ec58 : fetch_word Plain.M.loaded_segments (0x2ecb0 : word) = Some W_2ec58.
Proof. vm_refl. Qed.
Lemma D_2ec58 : decode_any W_2ec58 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ec5c : bv 32 := 0x00008067.
Lemma F_2ec5c : fetch_word Plain.M.loaded_segments (0x2ecb4 : word) = Some W_2ec5c.
Proof. vm_refl. Qed.
Lemma D_2ec5c : decode_any W_2ec5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
