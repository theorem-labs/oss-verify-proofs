(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
Module Na0_code_rb4330_b4334.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c6f3c : bv 32 := 0x00008067.
Lemma F_c6f3c : fetch_word Asan.M.loaded_segments (0xc6f8c : word) = Some W_c6f3c.
Proof. vm_refl. Qed.
Lemma D_c6f3c : decode_any W_c6f3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb4330_b4334.
Module Na0_code_rbe250_be258.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_be10c : bv 32 := 0x0184b787.
Lemma F_be10c : fetch_word Asan.M.loaded_segments (0xbe15c : word) = Some W_be10c.
Proof. vm_refl. Qed.
Lemma D_be10c : decode_any W_be10c = Some (FLoad FMT_D 15 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_be110 : bv 32 := 0xa287a553.
Lemma F_be110 : fetch_word Asan.M.loaded_segments (0xbe160 : word) = Some W_be110.
Proof. vm_refl. Qed.
Lemma D_be110 : decode_any W_be110 = Some (Fcmp F_EQ FMT_D 10 15 8, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbe250_be258.
Module Na0_code_rbda04_bda08.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bd8c0 : bv 32 := 0x00a9b027.
Lemma F_bd8c0 : fetch_word Asan.M.loaded_segments (0xbd910 : word) = Some W_bd8c0.
Proof. vm_refl. Qed.
Lemma D_bd8c0 : decode_any W_bd8c0 = Some (FStore FMT_D 19 10 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbda04_bda08.
Module Na0_code_rbda18_bda20.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bd8d4 : bv 32 := 0x0009b787.
Lemma F_bd8d4 : fetch_word Asan.M.loaded_segments (0xbd924 : word) = Some W_bd8d4.
Proof. vm_refl. Qed.
Lemma D_bd8d4 : decode_any W_bd8d4 = Some (FLoad FMT_D 15 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd8d8 : bv 32 := 0xe2079553.
Lemma F_bd8d8 : fetch_word Asan.M.loaded_segments (0xbd928 : word) = Some W_bd8d8.
Proof. vm_refl. Qed.
Lemma D_bd8d8 : decode_any W_bd8d8 = Some (Fclass FMT_D 10 15, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbda18_bda20.
Module Na0_code_rbdb1c_bdb20.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bd9d8 : bv 32 := 0x00008067.
Lemma F_bd9d8 : fetch_word Asan.M.loaded_segments (0xbda28 : word) = Some W_bd9d8.
Proof. vm_refl. Qed.
Lemma D_bd9d8 : decode_any W_bd9d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbdb1c_bdb20.
Module Na0_code_rbde68_bde6c.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_bdd24 : bv 32 := 0x0204a603.
Lemma F_bdd24 : fetch_word Asan.M.loaded_segments (0xbdd74 : word) = Some W_bdd24.
Proof. vm_refl. Qed.
Lemma D_bdd24 : decode_any W_bdd24 = Some (Load SZ4 true 12 9 32, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbde68_bde6c.
Module Na0_code_rb99dc_b99e0.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b9898 : bv 32 := 0x00008067.
Lemma F_b9898 : fetch_word Asan.M.loaded_segments (0xb98e8 : word) = Some W_b9898.
Proof. vm_refl. Qed.
Lemma D_b9898 : decode_any W_b9898 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb99dc_b99e0.
Module Na0_code_rba0a8_ba0ac.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b9f64 : bv 32 := 0x00008067.
Lemma F_b9f64 : fetch_word Asan.M.loaded_segments (0xb9fb4 : word) = Some W_b9f64.
Proof. vm_refl. Qed.
Lemma D_b9f64 : decode_any W_b9f64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rba0a8_ba0ac.
Module Na0_code_rba0f4_ba0f8.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b9fb0 : bv 32 := 0x00008067.
Lemma F_b9fb0 : fetch_word Asan.M.loaded_segments (0xba000 : word) = Some W_b9fb0.
Proof. vm_refl. Qed.
Lemma D_b9fb0 : decode_any W_b9fb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rba0f4_ba0f8.
Module Na0_code_rbe71c_be720.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_be5d8 : bv 32 := 0x00008067.
Lemma F_be5d8 : fetch_word Asan.M.loaded_segments (0xbe628 : word) = Some W_be5d8.
Proof. vm_refl. Qed.
Lemma D_be5d8 : decode_any W_be5d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbe71c_be720.
Module Na0_code_rb44b8_b44bc.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b4374 : bv 32 := 0x00008067.
Lemma F_b4374 : fetch_word Asan.M.loaded_segments (0xb43c4 : word) = Some W_b4374.
Proof. vm_refl. Qed.
Lemma D_b4374 : decode_any W_b4374 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb44b8_b44bc.
Module Na0_code_rb9d70_b9d74.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b9c2c : bv 32 := 0x00008067.
Lemma F_b9c2c : fetch_word Asan.M.loaded_segments (0xb9c7c : word) = Some W_b9c2c.
Proof. vm_refl. Qed.
Lemma D_b9c2c : decode_any W_b9c2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb9d70_b9d74.
Module Na0_code_rc1014_c1018.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c0ed0 : bv 32 := 0x00008067.
Lemma F_c0ed0 : fetch_word Asan.M.loaded_segments (0xc0f20 : word) = Some W_c0ed0.
Proof. vm_refl. Qed.
Lemma D_c0ed0 : decode_any W_c0ed0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc1014_c1018.
Module Na0_code_rb8880_b8884.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b873c : bv 32 := 0x00008067.
Lemma F_b873c : fetch_word Asan.M.loaded_segments (0xb878c : word) = Some W_b873c.
Proof. vm_refl. Qed.
Lemma D_b873c : decode_any W_b873c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb8880_b8884.
Module Na0_code_rb83d0_b83d8.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b828c : bv 32 := 0x4035d593.
Lemma F_b828c : fetch_word Asan.M.loaded_segments (0xb82dc : word) = Some W_b828c.
Proof. vm_refl. Qed.
Lemma D_b828c : decode_any W_b828c = Some (ShiftImm ALU_SRA 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b8290 : bv 32 := 0x02d585b3.
Lemma F_b8290 : fetch_word Asan.M.loaded_segments (0xb82e0 : word) = Some W_b8290.
Proof. vm_refl. Qed.
Lemma D_b8290 : decode_any W_b8290 = Some (Mul M_MUL 11 11 13, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb83d0_b83d8.
Module Na0_code_rcd618_cd61c.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_cc058 : bv 32 := 0x00008067.
Lemma F_cc058 : fetch_word Asan.M.loaded_segments (0xcc0a8 : word) = Some W_cc058.
Proof. vm_refl. Qed.
Lemma D_cc058 : decode_any W_cc058 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rcd618_cd61c.
Module Na0_code_rcac00_cac04.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_cbaa8 : bv 32 := 0x00008067.
Lemma F_cbaa8 : fetch_word Asan.M.loaded_segments (0xcbaf8 : word) = Some W_cbaa8.
Proof. vm_refl. Qed.
Lemma D_cbaa8 : decode_any W_cbaa8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rcac00_cac04.
Module Na0_code_r5fac4_60344.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_806ec : bv 32 := 0x0100006f.
Lemma F_806ec : fetch_word Asan.M.loaded_segments (0x8073c : word) = Some W_806ec.
Proof. vm_refl. Qed.
Lemma D_806ec : decode_any W_806ec = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_806f0 : bv 32 := 0x1dc0006f.
Lemma F_806f0 : fetch_word Asan.M.loaded_segments (0x80740 : word) = Some W_806f0.
Proof. vm_refl. Qed.
Lemma D_806f0 : decode_any W_806f0 = Some (Jal 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_806f8 : bv 32 := 0x7400006f.
Lemma F_806f8 : fetch_word Asan.M.loaded_segments (0x80748 : word) = Some W_806f8.
Proof. vm_refl. Qed.
Lemma D_806f8 : decode_any W_806f8 = Some (Jal 0 1856, 4%Z).
Proof. vm_refl. Qed.

Definition W_806fc : bv 32 := 0x81010113.
Lemma F_806fc : fetch_word Asan.M.loaded_segments (0x8074c : word) = Some W_806fc.
Proof. vm_refl. Qed.
Lemma D_806fc : decode_any W_806fc = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_80700 : bv 32 := 0x7e113423.
Lemma F_80700 : fetch_word Asan.M.loaded_segments (0x80750 : word) = Some W_80700.
Proof. vm_refl. Qed.
Lemma D_80700 : decode_any W_80700 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80704 : bv 32 := 0x7e813023.
Lemma F_80704 : fetch_word Asan.M.loaded_segments (0x80754 : word) = Some W_80704.
Proof. vm_refl. Qed.
Lemma D_80704 : decode_any W_80704 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80708 : bv 32 := 0x7c913c23.
Lemma F_80708 : fetch_word Asan.M.loaded_segments (0x80758 : word) = Some W_80708.
Proof. vm_refl. Qed.
Lemma D_80708 : decode_any W_80708 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_8070c : bv 32 := 0x7d213823.
Lemma F_8070c : fetch_word Asan.M.loaded_segments (0x8075c : word) = Some W_8070c.
Proof. vm_refl. Qed.
Lemma D_8070c : decode_any W_8070c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80710 : bv 32 := 0x7d313423.
Lemma F_80710 : fetch_word Asan.M.loaded_segments (0x80760 : word) = Some W_80710.
Proof. vm_refl. Qed.
Lemma D_80710 : decode_any W_80710 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80714 : bv 32 := 0x7d413023.
Lemma F_80714 : fetch_word Asan.M.loaded_segments (0x80764 : word) = Some W_80714.
Proof. vm_refl. Qed.
Lemma D_80714 : decode_any W_80714 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80718 : bv 32 := 0x7b513c23.
Lemma F_80718 : fetch_word Asan.M.loaded_segments (0x80768 : word) = Some W_80718.
Proof. vm_refl. Qed.
Lemma D_80718 : decode_any W_80718 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_8071c : bv 32 := 0x7f010413.
Lemma F_8071c : fetch_word Asan.M.loaded_segments (0x8076c : word) = Some W_8071c.
Proof. vm_refl. Qed.
Lemma D_8071c : decode_any W_8071c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80720 : bv 32 := 0xfa010113.
Lemma F_80720 : fetch_word Asan.M.loaded_segments (0x80770 : word) = Some W_80720.
Proof. vm_refl. Qed.
Lemma D_80720 : decode_any W_80720 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80724 : bv 32 := 0x00008913.
Lemma F_80724 : fetch_word Asan.M.loaded_segments (0x80774 : word) = Some W_80724.
Proof. vm_refl. Qed.
Lemma D_80724 : decode_any W_80724 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80728 : bv 32 := 0x00050493.
Lemma F_80728 : fetch_word Asan.M.loaded_segments (0x80778 : word) = Some W_80728.
Proof. vm_refl. Qed.
Lemma D_80728 : decode_any W_80728 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8072c : bv 32 := 0x10c0c0ef.
Lemma F_8072c : fetch_word Asan.M.loaded_segments (0x8077c : word) = Some W_8072c.
Proof. vm_refl. Qed.
Lemma D_8072c : decode_any W_8072c = Some (Jal 1 49420, 4%Z).
Proof. vm_refl. Qed.

Definition W_80730 : bv 32 := 0x02f4d593.
Lemma F_80730 : fetch_word Asan.M.loaded_segments (0x80780 : word) = Some W_80730.
Proof. vm_refl. Qed.
Lemma D_80730 : decode_any W_80730 = Some (ShiftImm ALU_SRL 11 9 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_80734 : bv 32 := 0x0a059063.
Lemma F_80734 : fetch_word Asan.M.loaded_segments (0x80784 : word) = Some W_80734.
Proof. vm_refl. Qed.
Lemma D_80734 : decode_any W_80734 = Some (Branch BC_NE 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_80738 : bv 32 := 0x0204d593.
Lemma F_80738 : fetch_word Asan.M.loaded_segments (0x80788 : word) = Some W_80738.
Proof. vm_refl. Qed.
Lemma D_80738 : decode_any W_80738 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8073c : bv 32 := 0x00359613.
Lemma F_8073c : fetch_word Asan.M.loaded_segments (0x8078c : word) = Some W_8073c.
Proof. vm_refl. Qed.
Lemma D_8073c : decode_any W_8073c = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80740 : bv 32 := 0x00c50633.
Lemma F_80740 : fetch_word Asan.M.loaded_segments (0x80790 : word) = Some W_80740.
Proof. vm_refl. Qed.
Lemma D_80740 : decode_any W_80740 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80744 : bv 32 := 0x00863683.
Lemma F_80744 : fetch_word Asan.M.loaded_segments (0x80794 : word) = Some W_80744.
Proof. vm_refl. Qed.
Lemma D_80744 : decode_any W_80744 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80748 : bv 32 := 0x0230000f.
Lemma F_80748 : fetch_word Asan.M.loaded_segments (0x80798 : word) = Some W_80748.
Proof. vm_refl. Qed.
Lemma D_80748 : decode_any W_80748 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8074c : bv 32 := 0x08068463.
Lemma F_8074c : fetch_word Asan.M.loaded_segments (0x8079c : word) = Some W_8074c.
Proof. vm_refl. Qed.
Lemma D_8074c : decode_any W_8074c = Some (Branch BC_EQ 13 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_807d4 : bv 32 := 0x80040a13.
Lemma F_807d4 : fetch_word Asan.M.loaded_segments (0x80824 : word) = Some W_807d4.
Proof. vm_refl. Qed.
Lemma D_807d4 : decode_any W_807d4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_807d8 : bv 32 := 0xfb0a0a13.
Lemma F_807d8 : fetch_word Asan.M.loaded_segments (0x80828 : word) = Some W_807d8.
Proof. vm_refl. Qed.
Lemma D_807d8 : decode_any W_807d8 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_807dc : bv 32 := 0x80040513.
Lemma F_807dc : fetch_word Asan.M.loaded_segments (0x8082c : word) = Some W_807dc.
Proof. vm_refl. Qed.
Lemma D_807dc : decode_any W_807dc = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_807e0 : bv 32 := 0xfc050513.
Lemma F_807e0 : fetch_word Asan.M.loaded_segments (0x80830 : word) = Some W_807e0.
Proof. vm_refl. Qed.
Lemma D_807e0 : decode_any W_807e0 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_807e4 : bv 32 := 0x7ffa0a93.
Lemma F_807e4 : fetch_word Asan.M.loaded_segments (0x80834 : word) = Some W_807e4.
Proof. vm_refl. Qed.
Lemma D_807e4 : decode_any W_807e4 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_807e8 : bv 32 := 0x000ab4a3.
Lemma F_807e8 : fetch_word Asan.M.loaded_segments (0x80838 : word) = Some W_807e8.
Proof. vm_refl. Qed.
Lemma D_807e8 : decode_any W_807e8 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_807ec : bv 32 := 0x00aa3023.
Lemma F_807ec : fetch_word Asan.M.loaded_segments (0x8083c : word) = Some W_807ec.
Proof. vm_refl. Qed.
Lemma D_807ec : decode_any W_807ec = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_807f0 : bv 32 := 0x000a3423.
Lemma F_807f0 : fetch_word Asan.M.loaded_segments (0x80840 : word) = Some W_807f0.
Proof. vm_refl. Qed.
Lemma D_807f0 : decode_any W_807f0 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_807f4 : bv 32 := 0x550080ef.
Lemma F_807f4 : fetch_word Asan.M.loaded_segments (0x80844 : word) = Some W_807f4.
Proof. vm_refl. Qed.
Lemma D_807f4 : decode_any W_807f4 = Some (Jal 1 34128, 4%Z).
Proof. vm_refl. Qed.

Definition W_807f8 : bv 32 := 0x00200593.
Lemma F_807f8 : fetch_word Asan.M.loaded_segments (0x80848 : word) = Some W_807f8.
Proof. vm_refl. Qed.
Lemma D_807f8 : decode_any W_807f8 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_807fc : bv 32 := 0x02a5ea63.
Lemma F_807fc : fetch_word Asan.M.loaded_segments (0x8084c : word) = Some W_807fc.
Proof. vm_refl. Qed.
Lemma D_807fc : decode_any W_807fc = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_80830 : bv 32 := 0x7f1200ef.
Lemma F_80830 : fetch_word Asan.M.loaded_segments (0x80880 : word) = Some W_80830.
Proof. vm_refl. Qed.
Lemma D_80830 : decode_any W_80830 = Some (Jal 1 135152, 4%Z).
Proof. vm_refl. Qed.

Definition W_80834 : bv 32 := 0x000d6597.
Lemma F_80834 : fetch_word Asan.M.loaded_segments (0x80884 : word) = Some W_80834.
Proof. vm_refl. Qed.
Lemma D_80834 : decode_any W_80834 = Some (Auipc 11 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_80838 : bv 32 := 0x5045b583.
Lemma F_80838 : fetch_word Asan.M.loaded_segments (0x80888 : word) = Some W_80838.
Proof. vm_refl. Qed.
Lemma D_80838 : decode_any W_80838 = Some (Load SZ8 true 11 11 1284, 4%Z).
Proof. vm_refl. Qed.

Definition W_8083c : bv 32 := 0x0225c983.
Lemma F_8083c : fetch_word Asan.M.loaded_segments (0x8088c : word) = Some W_8083c.
Proof. vm_refl. Qed.
Lemma D_8083c : decode_any W_8083c = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_80840 : bv 32 := 0x00050913.
Lemma F_80840 : fetch_word Asan.M.loaded_segments (0x80890 : word) = Some W_80840.
Proof. vm_refl. Qed.
Lemma D_80840 : decode_any W_80840 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80844 : bv 32 := 0x500080ef.
Lemma F_80844 : fetch_word Asan.M.loaded_segments (0x80894 : word) = Some W_80844.
Proof. vm_refl. Qed.
Lemma D_80844 : decode_any W_80844 = Some (Jal 1 34048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80848 : bv 32 := 0x00050793.
Lemma F_80848 : fetch_word Asan.M.loaded_segments (0x80898 : word) = Some W_80848.
Proof. vm_refl. Qed.
Lemma D_80848 : decode_any W_80848 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8084c : bv 32 := 0x00153513.
Lemma F_8084c : fetch_word Asan.M.loaded_segments (0x8089c : word) = Some W_8084c.
Proof. vm_refl. Qed.
Lemma D_8084c : decode_any W_8084c = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80850 : bv 32 := 0xfff50513.
Lemma F_80850 : fetch_word Asan.M.loaded_segments (0x808a0 : word) = Some W_80850.
Proof. vm_refl. Qed.
Lemma D_80850 : decode_any W_80850 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80854 : bv 32 := 0x008575b3.
Lemma F_80854 : fetch_word Asan.M.loaded_segments (0x808a4 : word) = Some W_80854.
Proof. vm_refl. Qed.
Lemma D_80854 : decode_any W_80854 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80858 : bv 32 := 0x00100513.
Lemma F_80858 : fetch_word Asan.M.loaded_segments (0x808a8 : word) = Some W_80858.
Proof. vm_refl. Qed.
Lemma D_80858 : decode_any W_80858 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8085c : bv 32 := 0x00bab4a3.
Lemma F_8085c : fetch_word Asan.M.loaded_segments (0x808ac : word) = Some W_8085c.
Proof. vm_refl. Qed.
Lemma D_8085c : decode_any W_8085c = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80860 : bv 32 := 0x00f56a63.
Lemma F_80860 : fetch_word Asan.M.loaded_segments (0x808b0 : word) = Some W_80860.
Proof. vm_refl. Qed.
Lemma D_80860 : decode_any W_80860 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80874 : bv 32 := 0x80040513.
Lemma F_80874 : fetch_word Asan.M.loaded_segments (0x808c4 : word) = Some W_80874.
Proof. vm_refl. Qed.
Lemma D_80874 : decode_any W_80874 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80878 : bv 32 := 0xfb050513.
Lemma F_80878 : fetch_word Asan.M.loaded_segments (0x808c8 : word) = Some W_80878.
Proof. vm_refl. Qed.
Lemma D_80878 : decode_any W_80878 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_8087c : bv 32 := 0x00090593.
Lemma F_8087c : fetch_word Asan.M.loaded_segments (0x808cc : word) = Some W_8087c.
Proof. vm_refl. Qed.
Lemma D_8087c : decode_any W_8087c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80880 : bv 32 := 0x00040613.
Lemma F_80880 : fetch_word Asan.M.loaded_segments (0x808d0 : word) = Some W_80880.
Proof. vm_refl. Qed.
Lemma D_80880 : decode_any W_80880 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80884 : bv 32 := 0x00000693.
Lemma F_80884 : fetch_word Asan.M.loaded_segments (0x808d4 : word) = Some W_80884.
Proof. vm_refl. Qed.
Lemma D_80884 : decode_any W_80884 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80888 : bv 32 := 0x00098713.
Lemma F_80888 : fetch_word Asan.M.loaded_segments (0x808d8 : word) = Some W_80888.
Proof. vm_refl. Qed.
Lemma D_80888 : decode_any W_80888 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8088c : bv 32 := 0x4c8080ef.
Lemma F_8088c : fetch_word Asan.M.loaded_segments (0x808dc : word) = Some W_8088c.
Proof. vm_refl. Qed.
Lemma D_8088c : decode_any W_8088c = Some (Jal 1 33992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80890 : bv 32 := 0x80040593.
Lemma F_80890 : fetch_word Asan.M.loaded_segments (0x808e0 : word) = Some W_80890.
Proof. vm_refl. Qed.
Lemma D_80890 : decode_any W_80890 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80894 : bv 32 := 0xfb058593.
Lemma F_80894 : fetch_word Asan.M.loaded_segments (0x808e4 : word) = Some W_80894.
Proof. vm_refl. Qed.
Lemma D_80894 : decode_any W_80894 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80898 : bv 32 := 0x00100613.
Lemma F_80898 : fetch_word Asan.M.loaded_segments (0x808e8 : word) = Some W_80898.
Proof. vm_refl. Qed.
Lemma D_80898 : decode_any W_80898 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8089c : bv 32 := 0x00048513.
Lemma F_8089c : fetch_word Asan.M.loaded_segments (0x808ec : word) = Some W_8089c.
Proof. vm_refl. Qed.
Lemma D_8089c : decode_any W_8089c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a0 : bv 32 := 0xd78d80ef.
Lemma F_808a0 : fetch_word Asan.M.loaded_segments (0x808f0 : word) = Some W_808a0.
Proof. vm_refl. Qed.
Lemma D_808a0 : decode_any W_808a0 = Some (Jal 1 1934712, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a4 : bv 32 := 0x06010113.
Lemma F_808a4 : fetch_word Asan.M.loaded_segments (0x808f4 : word) = Some W_808a4.
Proof. vm_refl. Qed.
Lemma D_808a4 : decode_any W_808a4 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a8 : bv 32 := 0x7e813083.
Lemma F_808a8 : fetch_word Asan.M.loaded_segments (0x808f8 : word) = Some W_808a8.
Proof. vm_refl. Qed.
Lemma D_808a8 : decode_any W_808a8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_808ac : bv 32 := 0x7e013403.
Lemma F_808ac : fetch_word Asan.M.loaded_segments (0x808fc : word) = Some W_808ac.
Proof. vm_refl. Qed.
Lemma D_808ac : decode_any W_808ac = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b0 : bv 32 := 0x7d813483.
Lemma F_808b0 : fetch_word Asan.M.loaded_segments (0x80900 : word) = Some W_808b0.
Proof. vm_refl. Qed.
Lemma D_808b0 : decode_any W_808b0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b4 : bv 32 := 0x7d013903.
Lemma F_808b4 : fetch_word Asan.M.loaded_segments (0x80904 : word) = Some W_808b4.
Proof. vm_refl. Qed.
Lemma D_808b4 : decode_any W_808b4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b8 : bv 32 := 0x7c813983.
Lemma F_808b8 : fetch_word Asan.M.loaded_segments (0x80908 : word) = Some W_808b8.
Proof. vm_refl. Qed.
Lemma D_808b8 : decode_any W_808b8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_808bc : bv 32 := 0x7c013a03.
Lemma F_808bc : fetch_word Asan.M.loaded_segments (0x8090c : word) = Some W_808bc.
Proof. vm_refl. Qed.
Lemma D_808bc : decode_any W_808bc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c0 : bv 32 := 0x7b813a83.
Lemma F_808c0 : fetch_word Asan.M.loaded_segments (0x80910 : word) = Some W_808c0.
Proof. vm_refl. Qed.
Lemma D_808c0 : decode_any W_808c0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c4 : bv 32 := 0x7f010113.
Lemma F_808c4 : fetch_word Asan.M.loaded_segments (0x80914 : word) = Some W_808c4.
Proof. vm_refl. Qed.
Lemma D_808c4 : decode_any W_808c4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c8 : bv 32 := 0x00008067.
Lemma F_808c8 : fetch_word Asan.M.loaded_segments (0x80918 : word) = Some W_808c8.
Proof. vm_refl. Qed.
Lemma D_808c8 : decode_any W_808c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808cc : bv 32 := 0x81010113.
Lemma F_808cc : fetch_word Asan.M.loaded_segments (0x8091c : word) = Some W_808cc.
Proof. vm_refl. Qed.
Lemma D_808cc : decode_any W_808cc = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d0 : bv 32 := 0x7e113423.
Lemma F_808d0 : fetch_word Asan.M.loaded_segments (0x80920 : word) = Some W_808d0.
Proof. vm_refl. Qed.
Lemma D_808d0 : decode_any W_808d0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d4 : bv 32 := 0x7e813023.
Lemma F_808d4 : fetch_word Asan.M.loaded_segments (0x80924 : word) = Some W_808d4.
Proof. vm_refl. Qed.
Lemma D_808d4 : decode_any W_808d4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d8 : bv 32 := 0x7c913c23.
Lemma F_808d8 : fetch_word Asan.M.loaded_segments (0x80928 : word) = Some W_808d8.
Proof. vm_refl. Qed.
Lemma D_808d8 : decode_any W_808d8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_808dc : bv 32 := 0x7d213823.
Lemma F_808dc : fetch_word Asan.M.loaded_segments (0x8092c : word) = Some W_808dc.
Proof. vm_refl. Qed.
Lemma D_808dc : decode_any W_808dc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e0 : bv 32 := 0x7d313423.
Lemma F_808e0 : fetch_word Asan.M.loaded_segments (0x80930 : word) = Some W_808e0.
Proof. vm_refl. Qed.
Lemma D_808e0 : decode_any W_808e0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e4 : bv 32 := 0x7d413023.
Lemma F_808e4 : fetch_word Asan.M.loaded_segments (0x80934 : word) = Some W_808e4.
Proof. vm_refl. Qed.
Lemma D_808e4 : decode_any W_808e4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e8 : bv 32 := 0x7b513c23.
Lemma F_808e8 : fetch_word Asan.M.loaded_segments (0x80938 : word) = Some W_808e8.
Proof. vm_refl. Qed.
Lemma D_808e8 : decode_any W_808e8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_808ec : bv 32 := 0x7f010413.
Lemma F_808ec : fetch_word Asan.M.loaded_segments (0x8093c : word) = Some W_808ec.
Proof. vm_refl. Qed.
Lemma D_808ec : decode_any W_808ec = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f0 : bv 32 := 0xfa010113.
Lemma F_808f0 : fetch_word Asan.M.loaded_segments (0x80940 : word) = Some W_808f0.
Proof. vm_refl. Qed.
Lemma D_808f0 : decode_any W_808f0 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f4 : bv 32 := 0x00008913.
Lemma F_808f4 : fetch_word Asan.M.loaded_segments (0x80944 : word) = Some W_808f4.
Proof. vm_refl. Qed.
Lemma D_808f4 : decode_any W_808f4 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f8 : bv 32 := 0x00050493.
Lemma F_808f8 : fetch_word Asan.M.loaded_segments (0x80948 : word) = Some W_808f8.
Proof. vm_refl. Qed.
Lemma D_808f8 : decode_any W_808f8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808fc : bv 32 := 0x6c0070ef.
Lemma F_808fc : fetch_word Asan.M.loaded_segments (0x8094c : word) = Some W_808fc.
Proof. vm_refl. Qed.
Lemma D_808fc : decode_any W_808fc = Some (Jal 1 30400, 4%Z).
Proof. vm_refl. Qed.

Definition W_80900 : bv 32 := 0x06050063.
Lemma F_80900 : fetch_word Asan.M.loaded_segments (0x80950 : word) = Some W_80900.
Proof. vm_refl. Qed.
Lemma D_80900 : decode_any W_80900 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80904 : bv 32 := 0x80040a13.
Lemma F_80904 : fetch_word Asan.M.loaded_segments (0x80954 : word) = Some W_80904.
Proof. vm_refl. Qed.
Lemma D_80904 : decode_any W_80904 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80908 : bv 32 := 0xfb0a0a13.
Lemma F_80908 : fetch_word Asan.M.loaded_segments (0x80958 : word) = Some W_80908.
Proof. vm_refl. Qed.
Lemma D_80908 : decode_any W_80908 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_8090c : bv 32 := 0x80040513.
Lemma F_8090c : fetch_word Asan.M.loaded_segments (0x8095c : word) = Some W_8090c.
Proof. vm_refl. Qed.
Lemma D_8090c : decode_any W_8090c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80910 : bv 32 := 0xfc050513.
Lemma F_80910 : fetch_word Asan.M.loaded_segments (0x80960 : word) = Some W_80910.
Proof. vm_refl. Qed.
Lemma D_80910 : decode_any W_80910 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80914 : bv 32 := 0x7ffa0a93.
Lemma F_80914 : fetch_word Asan.M.loaded_segments (0x80964 : word) = Some W_80914.
Proof. vm_refl. Qed.
Lemma D_80914 : decode_any W_80914 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_80918 : bv 32 := 0x000ab4a3.
Lemma F_80918 : fetch_word Asan.M.loaded_segments (0x80968 : word) = Some W_80918.
Proof. vm_refl. Qed.
Lemma D_80918 : decode_any W_80918 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_8091c : bv 32 := 0x00aa3023.
Lemma F_8091c : fetch_word Asan.M.loaded_segments (0x8096c : word) = Some W_8091c.
Proof. vm_refl. Qed.
Lemma D_8091c : decode_any W_8091c = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80920 : bv 32 := 0x000a3423.
Lemma F_80920 : fetch_word Asan.M.loaded_segments (0x80970 : word) = Some W_80920.
Proof. vm_refl. Qed.
Lemma D_80920 : decode_any W_80920 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80924 : bv 32 := 0x420080ef.
Lemma F_80924 : fetch_word Asan.M.loaded_segments (0x80974 : word) = Some W_80924.
Proof. vm_refl. Qed.
Lemma D_80924 : decode_any W_80924 = Some (Jal 1 33824, 4%Z).
Proof. vm_refl. Qed.

Definition W_80928 : bv 32 := 0x00200593.
Lemma F_80928 : fetch_word Asan.M.loaded_segments (0x80978 : word) = Some W_80928.
Proof. vm_refl. Qed.
Lemma D_80928 : decode_any W_80928 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8092c : bv 32 := 0x06a5e263.
Lemma F_8092c : fetch_word Asan.M.loaded_segments (0x8097c : word) = Some W_8092c.
Proof. vm_refl. Qed.
Lemma D_8092c : decode_any W_8092c = Some (Branch BC_LTU 11 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_80990 : bv 32 := 0x691200ef.
Lemma F_80990 : fetch_word Asan.M.loaded_segments (0x809e0 : word) = Some W_80990.
Proof. vm_refl. Qed.
Lemma D_80990 : decode_any W_80990 = Some (Jal 1 134800, 4%Z).
Proof. vm_refl. Qed.

Definition W_80994 : bv 32 := 0x000d6597.
Lemma F_80994 : fetch_word Asan.M.loaded_segments (0x809e4 : word) = Some W_80994.
Proof. vm_refl. Qed.
Lemma D_80994 : decode_any W_80994 = Some (Auipc 11 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_80998 : bv 32 := 0x3a45b583.
Lemma F_80998 : fetch_word Asan.M.loaded_segments (0x809e8 : word) = Some W_80998.
Proof. vm_refl. Qed.
Lemma D_80998 : decode_any W_80998 = Some (Load SZ8 true 11 11 932, 4%Z).
Proof. vm_refl. Qed.

Definition W_8099c : bv 32 := 0x0225c983.
Lemma F_8099c : fetch_word Asan.M.loaded_segments (0x809ec : word) = Some W_8099c.
Proof. vm_refl. Qed.
Lemma D_8099c : decode_any W_8099c = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_809a0 : bv 32 := 0x00050913.
Lemma F_809a0 : fetch_word Asan.M.loaded_segments (0x809f0 : word) = Some W_809a0.
Proof. vm_refl. Qed.
Lemma D_809a0 : decode_any W_809a0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809a4 : bv 32 := 0x3a0080ef.
Lemma F_809a4 : fetch_word Asan.M.loaded_segments (0x809f4 : word) = Some W_809a4.
Proof. vm_refl. Qed.
Lemma D_809a4 : decode_any W_809a4 = Some (Jal 1 33696, 4%Z).
Proof. vm_refl. Qed.

Definition W_809a8 : bv 32 := 0x00050793.
Lemma F_809a8 : fetch_word Asan.M.loaded_segments (0x809f8 : word) = Some W_809a8.
Proof. vm_refl. Qed.
Lemma D_809a8 : decode_any W_809a8 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809ac : bv 32 := 0x00153513.
Lemma F_809ac : fetch_word Asan.M.loaded_segments (0x809fc : word) = Some W_809ac.
Proof. vm_refl. Qed.
Lemma D_809ac : decode_any W_809ac = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_809b0 : bv 32 := 0xfff50513.
Lemma F_809b0 : fetch_word Asan.M.loaded_segments (0x80a00 : word) = Some W_809b0.
Proof. vm_refl. Qed.
Lemma D_809b0 : decode_any W_809b0 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_809b4 : bv 32 := 0x008575b3.
Lemma F_809b4 : fetch_word Asan.M.loaded_segments (0x80a04 : word) = Some W_809b4.
Proof. vm_refl. Qed.
Lemma D_809b4 : decode_any W_809b4 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_809b8 : bv 32 := 0x00100513.
Lemma F_809b8 : fetch_word Asan.M.loaded_segments (0x80a08 : word) = Some W_809b8.
Proof. vm_refl. Qed.
Lemma D_809b8 : decode_any W_809b8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_809bc : bv 32 := 0x00bab4a3.
Lemma F_809bc : fetch_word Asan.M.loaded_segments (0x80a0c : word) = Some W_809bc.
Proof. vm_refl. Qed.
Lemma D_809bc : decode_any W_809bc = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_809c0 : bv 32 := 0x00f56a63.
Lemma F_809c0 : fetch_word Asan.M.loaded_segments (0x80a10 : word) = Some W_809c0.
Proof. vm_refl. Qed.
Lemma D_809c0 : decode_any W_809c0 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_809d4 : bv 32 := 0x80040513.
Lemma F_809d4 : fetch_word Asan.M.loaded_segments (0x80a24 : word) = Some W_809d4.
Proof. vm_refl. Qed.
Lemma D_809d4 : decode_any W_809d4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_809d8 : bv 32 := 0xfb050513.
Lemma F_809d8 : fetch_word Asan.M.loaded_segments (0x80a28 : word) = Some W_809d8.
Proof. vm_refl. Qed.
Lemma D_809d8 : decode_any W_809d8 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_809dc : bv 32 := 0x00090593.
Lemma F_809dc : fetch_word Asan.M.loaded_segments (0x80a2c : word) = Some W_809dc.
Proof. vm_refl. Qed.
Lemma D_809dc : decode_any W_809dc = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809e0 : bv 32 := 0x00040613.
Lemma F_809e0 : fetch_word Asan.M.loaded_segments (0x80a30 : word) = Some W_809e0.
Proof. vm_refl. Qed.
Lemma D_809e0 : decode_any W_809e0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809e4 : bv 32 := 0x00000693.
Lemma F_809e4 : fetch_word Asan.M.loaded_segments (0x80a34 : word) = Some W_809e4.
Proof. vm_refl. Qed.
Lemma D_809e4 : decode_any W_809e4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809e8 : bv 32 := 0x00098713.
Lemma F_809e8 : fetch_word Asan.M.loaded_segments (0x80a38 : word) = Some W_809e8.
Proof. vm_refl. Qed.
Lemma D_809e8 : decode_any W_809e8 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809ec : bv 32 := 0x368080ef.
Lemma F_809ec : fetch_word Asan.M.loaded_segments (0x80a3c : word) = Some W_809ec.
Proof. vm_refl. Qed.
Lemma D_809ec : decode_any W_809ec = Some (Jal 1 33640, 4%Z).
Proof. vm_refl. Qed.

Definition W_809f0 : bv 32 := 0x80040593.
Lemma F_809f0 : fetch_word Asan.M.loaded_segments (0x80a40 : word) = Some W_809f0.
Proof. vm_refl. Qed.
Lemma D_809f0 : decode_any W_809f0 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_809f4 : bv 32 := 0xfb058593.
Lemma F_809f4 : fetch_word Asan.M.loaded_segments (0x80a44 : word) = Some W_809f4.
Proof. vm_refl. Qed.
Lemma D_809f4 : decode_any W_809f4 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_809f8 : bv 32 := 0x00048513.
Lemma F_809f8 : fetch_word Asan.M.loaded_segments (0x80a48 : word) = Some W_809f8.
Proof. vm_refl. Qed.
Lemma D_809f8 : decode_any W_809f8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809fc : bv 32 := 0xefcd80ef.
Lemma F_809fc : fetch_word Asan.M.loaded_segments (0x80a4c : word) = Some W_809fc.
Proof. vm_refl. Qed.
Lemma D_809fc : decode_any W_809fc = Some (Jal 1 1935100, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a00 : bv 32 := 0x06010113.
Lemma F_80a00 : fetch_word Asan.M.loaded_segments (0x80a50 : word) = Some W_80a00.
Proof. vm_refl. Qed.
Lemma D_80a00 : decode_any W_80a00 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a04 : bv 32 := 0x7e813083.
Lemma F_80a04 : fetch_word Asan.M.loaded_segments (0x80a54 : word) = Some W_80a04.
Proof. vm_refl. Qed.
Lemma D_80a04 : decode_any W_80a04 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a08 : bv 32 := 0x7e013403.
Lemma F_80a08 : fetch_word Asan.M.loaded_segments (0x80a58 : word) = Some W_80a08.
Proof. vm_refl. Qed.
Lemma D_80a08 : decode_any W_80a08 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a0c : bv 32 := 0x7d813483.
Lemma F_80a0c : fetch_word Asan.M.loaded_segments (0x80a5c : word) = Some W_80a0c.
Proof. vm_refl. Qed.
Lemma D_80a0c : decode_any W_80a0c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a10 : bv 32 := 0x7d013903.
Lemma F_80a10 : fetch_word Asan.M.loaded_segments (0x80a60 : word) = Some W_80a10.
Proof. vm_refl. Qed.
Lemma D_80a10 : decode_any W_80a10 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a14 : bv 32 := 0x7c813983.
Lemma F_80a14 : fetch_word Asan.M.loaded_segments (0x80a64 : word) = Some W_80a14.
Proof. vm_refl. Qed.
Lemma D_80a14 : decode_any W_80a14 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a18 : bv 32 := 0x7c013a03.
Lemma F_80a18 : fetch_word Asan.M.loaded_segments (0x80a68 : word) = Some W_80a18.
Proof. vm_refl. Qed.
Lemma D_80a18 : decode_any W_80a18 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a1c : bv 32 := 0x7b813a83.
Lemma F_80a1c : fetch_word Asan.M.loaded_segments (0x80a6c : word) = Some W_80a1c.
Proof. vm_refl. Qed.
Lemma D_80a1c : decode_any W_80a1c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a20 : bv 32 := 0x7f010113.
Lemma F_80a20 : fetch_word Asan.M.loaded_segments (0x80a70 : word) = Some W_80a20.
Proof. vm_refl. Qed.
Lemma D_80a20 : decode_any W_80a20 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a24 : bv 32 := 0x00008067.
Lemma F_80a24 : fetch_word Asan.M.loaded_segments (0x80a74 : word) = Some W_80a24.
Proof. vm_refl. Qed.
Lemma D_80a24 : decode_any W_80a24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e38 : bv 32 := 0x81010113.
Lemma F_80e38 : fetch_word Asan.M.loaded_segments (0x80e88 : word) = Some W_80e38.
Proof. vm_refl. Qed.
Lemma D_80e38 : decode_any W_80e38 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e3c : bv 32 := 0x7e113423.
Lemma F_80e3c : fetch_word Asan.M.loaded_segments (0x80e8c : word) = Some W_80e3c.
Proof. vm_refl. Qed.
Lemma D_80e3c : decode_any W_80e3c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e40 : bv 32 := 0x7e813023.
Lemma F_80e40 : fetch_word Asan.M.loaded_segments (0x80e90 : word) = Some W_80e40.
Proof. vm_refl. Qed.
Lemma D_80e40 : decode_any W_80e40 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e44 : bv 32 := 0x7c913c23.
Lemma F_80e44 : fetch_word Asan.M.loaded_segments (0x80e94 : word) = Some W_80e44.
Proof. vm_refl. Qed.
Lemma D_80e44 : decode_any W_80e44 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e48 : bv 32 := 0x7d213823.
Lemma F_80e48 : fetch_word Asan.M.loaded_segments (0x80e98 : word) = Some W_80e48.
Proof. vm_refl. Qed.
Lemma D_80e48 : decode_any W_80e48 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e4c : bv 32 := 0x7d313423.
Lemma F_80e4c : fetch_word Asan.M.loaded_segments (0x80e9c : word) = Some W_80e4c.
Proof. vm_refl. Qed.
Lemma D_80e4c : decode_any W_80e4c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e50 : bv 32 := 0x7d413023.
Lemma F_80e50 : fetch_word Asan.M.loaded_segments (0x80ea0 : word) = Some W_80e50.
Proof. vm_refl. Qed.
Lemma D_80e50 : decode_any W_80e50 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e54 : bv 32 := 0x7b513c23.
Lemma F_80e54 : fetch_word Asan.M.loaded_segments (0x80ea4 : word) = Some W_80e54.
Proof. vm_refl. Qed.
Lemma D_80e54 : decode_any W_80e54 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e58 : bv 32 := 0x7b613823.
Lemma F_80e58 : fetch_word Asan.M.loaded_segments (0x80ea8 : word) = Some W_80e58.
Proof. vm_refl. Qed.
Lemma D_80e58 : decode_any W_80e58 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e5c : bv 32 := 0x7f010413.
Lemma F_80e5c : fetch_word Asan.M.loaded_segments (0x80eac : word) = Some W_80e5c.
Proof. vm_refl. Qed.
Lemma D_80e5c : decode_any W_80e5c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e60 : bv 32 := 0xf9010113.
Lemma F_80e60 : fetch_word Asan.M.loaded_segments (0x80eb0 : word) = Some W_80e60.
Proof. vm_refl. Qed.
Lemma D_80e60 : decode_any W_80e60 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e64 : bv 32 := 0x00008993.
Lemma F_80e64 : fetch_word Asan.M.loaded_segments (0x80eb4 : word) = Some W_80e64.
Proof. vm_refl. Qed.
Lemma D_80e64 : decode_any W_80e64 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e68 : bv 32 := 0x00058493.
Lemma F_80e68 : fetch_word Asan.M.loaded_segments (0x80eb8 : word) = Some W_80e68.
Proof. vm_refl. Qed.
Lemma D_80e68 : decode_any W_80e68 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e6c : bv 32 := 0x00050913.
Lemma F_80e6c : fetch_word Asan.M.loaded_segments (0x80ebc : word) = Some W_80e6c.
Proof. vm_refl. Qed.
Lemma D_80e6c : decode_any W_80e6c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e70 : bv 32 := 0x80040a93.
Lemma F_80e70 : fetch_word Asan.M.loaded_segments (0x80ec0 : word) = Some W_80e70.
Proof. vm_refl. Qed.
Lemma D_80e70 : decode_any W_80e70 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e74 : bv 32 := 0xfa8a8a93.
Lemma F_80e74 : fetch_word Asan.M.loaded_segments (0x80ec4 : word) = Some W_80e74.
Proof. vm_refl. Qed.
Lemma D_80e74 : decode_any W_80e74 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e78 : bv 32 := 0x80040513.
Lemma F_80e78 : fetch_word Asan.M.loaded_segments (0x80ec8 : word) = Some W_80e78.
Proof. vm_refl. Qed.
Lemma D_80e78 : decode_any W_80e78 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e7c : bv 32 := 0xfb850513.
Lemma F_80e7c : fetch_word Asan.M.loaded_segments (0x80ecc : word) = Some W_80e7c.
Proof. vm_refl. Qed.
Lemma D_80e7c : decode_any W_80e7c = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e80 : bv 32 := 0x7ffa8b13.
Lemma F_80e80 : fetch_word Asan.M.loaded_segments (0x80ed0 : word) = Some W_80e80.
Proof. vm_refl. Qed.
Lemma D_80e80 : decode_any W_80e80 = Some (OpImm ALU_ADD 22 21 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e84 : bv 32 := 0x000b34a3.
Lemma F_80e84 : fetch_word Asan.M.loaded_segments (0x80ed4 : word) = Some W_80e84.
Proof. vm_refl. Qed.
Lemma D_80e84 : decode_any W_80e84 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e88 : bv 32 := 0x00aab023.
Lemma F_80e88 : fetch_word Asan.M.loaded_segments (0x80ed8 : word) = Some W_80e88.
Proof. vm_refl. Qed.
Lemma D_80e88 : decode_any W_80e88 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e8c : bv 32 := 0x000ab423.
Lemma F_80e8c : fetch_word Asan.M.loaded_segments (0x80edc : word) = Some W_80e8c.
Proof. vm_refl. Qed.
Lemma D_80e8c : decode_any W_80e8c = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e90 : bv 32 := 0x6b5070ef.
Lemma F_80e90 : fetch_word Asan.M.loaded_segments (0x80ee0 : word) = Some W_80e90.
Proof. vm_refl. Qed.
Lemma D_80e90 : decode_any W_80e90 = Some (Jal 1 32436, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e94 : bv 32 := 0x00200593.
Lemma F_80e94 : fetch_word Asan.M.loaded_segments (0x80ee4 : word) = Some W_80e94.
Proof. vm_refl. Qed.
Lemma D_80e94 : decode_any W_80e94 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e98 : bv 32 := 0x02a5ea63.
Lemma F_80e98 : fetch_word Asan.M.loaded_segments (0x80ee8 : word) = Some W_80e98.
Proof. vm_refl. Qed.
Lemma D_80e98 : decode_any W_80e98 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ecc : bv 32 := 0x155200ef.
Lemma F_80ecc : fetch_word Asan.M.loaded_segments (0x80f1c : word) = Some W_80ecc.
Proof. vm_refl. Qed.
Lemma D_80ecc : decode_any W_80ecc = Some (Jal 1 133460, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed0 : bv 32 := 0x000d6597.
Lemma F_80ed0 : fetch_word Asan.M.loaded_segments (0x80f20 : word) = Some W_80ed0.
Proof. vm_refl. Qed.
Lemma D_80ed0 : decode_any W_80ed0 = Some (Auipc 11 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed4 : bv 32 := 0xe685b583.
Lemma F_80ed4 : fetch_word Asan.M.loaded_segments (0x80f24 : word) = Some W_80ed4.
Proof. vm_refl. Qed.
Lemma D_80ed4 : decode_any W_80ed4 = Some (Load SZ8 true 11 11 3688, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed8 : bv 32 := 0x0225ca03.
Lemma F_80ed8 : fetch_word Asan.M.loaded_segments (0x80f28 : word) = Some W_80ed8.
Proof. vm_refl. Qed.
Lemma D_80ed8 : decode_any W_80ed8 = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_80edc : bv 32 := 0x00050993.
Lemma F_80edc : fetch_word Asan.M.loaded_segments (0x80f2c : word) = Some W_80edc.
Proof. vm_refl. Qed.
Lemma D_80edc : decode_any W_80edc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ee0 : bv 32 := 0x665070ef.
Lemma F_80ee0 : fetch_word Asan.M.loaded_segments (0x80f30 : word) = Some W_80ee0.
Proof. vm_refl. Qed.
Lemma D_80ee0 : decode_any W_80ee0 = Some (Jal 1 32356, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ee4 : bv 32 := 0x00050793.
Lemma F_80ee4 : fetch_word Asan.M.loaded_segments (0x80f34 : word) = Some W_80ee4.
Proof. vm_refl. Qed.
Lemma D_80ee4 : decode_any W_80ee4 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ee8 : bv 32 := 0x00153513.
Lemma F_80ee8 : fetch_word Asan.M.loaded_segments (0x80f38 : word) = Some W_80ee8.
Proof. vm_refl. Qed.
Lemma D_80ee8 : decode_any W_80ee8 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eec : bv 32 := 0xfff50513.
Lemma F_80eec : fetch_word Asan.M.loaded_segments (0x80f3c : word) = Some W_80eec.
Proof. vm_refl. Qed.
Lemma D_80eec : decode_any W_80eec = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ef0 : bv 32 := 0x008575b3.
Lemma F_80ef0 : fetch_word Asan.M.loaded_segments (0x80f40 : word) = Some W_80ef0.
Proof. vm_refl. Qed.
Lemma D_80ef0 : decode_any W_80ef0 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ef4 : bv 32 := 0x00100513.
Lemma F_80ef4 : fetch_word Asan.M.loaded_segments (0x80f44 : word) = Some W_80ef4.
Proof. vm_refl. Qed.
Lemma D_80ef4 : decode_any W_80ef4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ef8 : bv 32 := 0x00bb34a3.
Lemma F_80ef8 : fetch_word Asan.M.loaded_segments (0x80f48 : word) = Some W_80ef8.
Proof. vm_refl. Qed.
Lemma D_80ef8 : decode_any W_80ef8 = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80efc : bv 32 := 0x00f56a63.
Lemma F_80efc : fetch_word Asan.M.loaded_segments (0x80f4c : word) = Some W_80efc.
Proof. vm_refl. Qed.
Lemma D_80efc : decode_any W_80efc = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f10 : bv 32 := 0x80040513.
Lemma F_80f10 : fetch_word Asan.M.loaded_segments (0x80f60 : word) = Some W_80f10.
Proof. vm_refl. Qed.
Lemma D_80f10 : decode_any W_80f10 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f14 : bv 32 := 0xfa850513.
Lemma F_80f14 : fetch_word Asan.M.loaded_segments (0x80f64 : word) = Some W_80f14.
Proof. vm_refl. Qed.
Lemma D_80f14 : decode_any W_80f14 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f18 : bv 32 := 0x00098593.
Lemma F_80f18 : fetch_word Asan.M.loaded_segments (0x80f68 : word) = Some W_80f18.
Proof. vm_refl. Qed.
Lemma D_80f18 : decode_any W_80f18 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f1c : bv 32 := 0x00040613.
Lemma F_80f1c : fetch_word Asan.M.loaded_segments (0x80f6c : word) = Some W_80f1c.
Proof. vm_refl. Qed.
Lemma D_80f1c : decode_any W_80f1c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f20 : bv 32 := 0x00000693.
Lemma F_80f20 : fetch_word Asan.M.loaded_segments (0x80f70 : word) = Some W_80f20.
Proof. vm_refl. Qed.
Lemma D_80f20 : decode_any W_80f20 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f24 : bv 32 := 0x000a0713.
Lemma F_80f24 : fetch_word Asan.M.loaded_segments (0x80f74 : word) = Some W_80f24.
Proof. vm_refl. Qed.
Lemma D_80f24 : decode_any W_80f24 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f28 : bv 32 := 0x62d070ef.
Lemma F_80f28 : fetch_word Asan.M.loaded_segments (0x80f78 : word) = Some W_80f28.
Proof. vm_refl. Qed.
Lemma D_80f28 : decode_any W_80f28 = Some (Jal 1 32300, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f2c : bv 32 := 0x80040613.
Lemma F_80f2c : fetch_word Asan.M.loaded_segments (0x80f7c : word) = Some W_80f2c.
Proof. vm_refl. Qed.
Lemma D_80f2c : decode_any W_80f2c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f30 : bv 32 := 0xfa860613.
Lemma F_80f30 : fetch_word Asan.M.loaded_segments (0x80f80 : word) = Some W_80f30.
Proof. vm_refl. Qed.
Lemma D_80f30 : decode_any W_80f30 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f34 : bv 32 := 0x00090513.
Lemma F_80f34 : fetch_word Asan.M.loaded_segments (0x80f84 : word) = Some W_80f34.
Proof. vm_refl. Qed.
Lemma D_80f34 : decode_any W_80f34 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f38 : bv 32 := 0x00048593.
Lemma F_80f38 : fetch_word Asan.M.loaded_segments (0x80f88 : word) = Some W_80f38.
Proof. vm_refl. Qed.
Lemma D_80f38 : decode_any W_80f38 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f3c : bv 32 := 0xdadd80ef.
Lemma F_80f3c : fetch_word Asan.M.loaded_segments (0x80f8c : word) = Some W_80f3c.
Proof. vm_refl. Qed.
Lemma D_80f3c : decode_any W_80f3c = Some (Jal 1 1936812, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f40 : bv 32 := 0x07010113.
Lemma F_80f40 : fetch_word Asan.M.loaded_segments (0x80f90 : word) = Some W_80f40.
Proof. vm_refl. Qed.
Lemma D_80f40 : decode_any W_80f40 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f44 : bv 32 := 0x7e813083.
Lemma F_80f44 : fetch_word Asan.M.loaded_segments (0x80f94 : word) = Some W_80f44.
Proof. vm_refl. Qed.
Lemma D_80f44 : decode_any W_80f44 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f48 : bv 32 := 0x7e013403.
Lemma F_80f48 : fetch_word Asan.M.loaded_segments (0x80f98 : word) = Some W_80f48.
Proof. vm_refl. Qed.
Lemma D_80f48 : decode_any W_80f48 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f4c : bv 32 := 0x7d813483.
Lemma F_80f4c : fetch_word Asan.M.loaded_segments (0x80f9c : word) = Some W_80f4c.
Proof. vm_refl. Qed.
Lemma D_80f4c : decode_any W_80f4c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f50 : bv 32 := 0x7d013903.
Lemma F_80f50 : fetch_word Asan.M.loaded_segments (0x80fa0 : word) = Some W_80f50.
Proof. vm_refl. Qed.
Lemma D_80f50 : decode_any W_80f50 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f54 : bv 32 := 0x7c813983.
Lemma F_80f54 : fetch_word Asan.M.loaded_segments (0x80fa4 : word) = Some W_80f54.
Proof. vm_refl. Qed.
Lemma D_80f54 : decode_any W_80f54 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f58 : bv 32 := 0x7c013a03.
Lemma F_80f58 : fetch_word Asan.M.loaded_segments (0x80fa8 : word) = Some W_80f58.
Proof. vm_refl. Qed.
Lemma D_80f58 : decode_any W_80f58 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f5c : bv 32 := 0x7b813a83.
Lemma F_80f5c : fetch_word Asan.M.loaded_segments (0x80fac : word) = Some W_80f5c.
Proof. vm_refl. Qed.
Lemma D_80f5c : decode_any W_80f5c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f60 : bv 32 := 0x7b013b03.
Lemma F_80f60 : fetch_word Asan.M.loaded_segments (0x80fb0 : word) = Some W_80f60.
Proof. vm_refl. Qed.
Lemma D_80f60 : decode_any W_80f60 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f64 : bv 32 := 0x7f010113.
Lemma F_80f64 : fetch_word Asan.M.loaded_segments (0x80fb4 : word) = Some W_80f64.
Proof. vm_refl. Qed.
Lemma D_80f64 : decode_any W_80f64 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f68 : bv 32 := 0x00008067.
Lemma F_80f68 : fetch_word Asan.M.loaded_segments (0x80fb8 : word) = Some W_80f68.
Proof. vm_refl. Qed.
Lemma D_80f68 : decode_any W_80f68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r5fac4_60344.
