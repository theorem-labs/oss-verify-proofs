(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
Module Na0_code_rb3dd8_b3ddc.
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

Definition W_d531c : bv 32 := 0x00008067.
Lemma F_d531c : fetch_word Asan.M.loaded_segments (0xd536c : word) = Some W_d531c.
Proof. vm_refl. Qed.
Lemma D_d531c : decode_any W_d531c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb3dd8_b3ddc.
Module Na0_code_rb3ec4_b3ec8.
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

Definition W_d5408 : bv 32 := 0x00008067.
Lemma F_d5408 : fetch_word Asan.M.loaded_segments (0xd5458 : word) = Some W_d5408.
Proof. vm_refl. Qed.
Lemma D_d5408 : decode_any W_d5408 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb3ec4_b3ec8.
Module Na0_code_rb313c_b3140.
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

Definition W_b2ff8 : bv 32 := 0x00008067.
Lemma F_b2ff8 : fetch_word Asan.M.loaded_segments (0xb3048 : word) = Some W_b2ff8.
Proof. vm_refl. Qed.
Lemma D_b2ff8 : decode_any W_b2ff8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb313c_b3140.
Module Na0_code_rb6494_b6498.
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

Definition W_b6350 : bv 32 := 0x00008067.
Lemma F_b6350 : fetch_word Asan.M.loaded_segments (0xb63a0 : word) = Some W_b6350.
Proof. vm_refl. Qed.
Lemma D_b6350 : decode_any W_b6350 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb6494_b6498.
Module Na0_code_rb5b6c_b5b70.
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

Definition W_b5a28 : bv 32 := 0x00008067.
Lemma F_b5a28 : fetch_word Asan.M.loaded_segments (0xb5a78 : word) = Some W_b5a28.
Proof. vm_refl. Qed.
Lemma D_b5a28 : decode_any W_b5a28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb5b6c_b5b70.
Module Na0_code_rba46c_ba480.
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

Definition W_ba328 : bv 32 := 0x02a797b3.
Lemma F_ba328 : fetch_word Asan.M.loaded_segments (0xba378 : word) = Some W_ba328.
Proof. vm_refl. Qed.
Lemma D_ba328 : decode_any W_ba328 = Some (Mul M_MULH 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ba32c : bv 32 := 0x001a8a93.
Lemma F_ba32c : fetch_word Asan.M.loaded_segments (0xba37c : word) = Some W_ba32c.
Proof. vm_refl. Qed.
Lemma D_ba32c : decode_any W_ba32c = Some (OpImm ALU_ADD 21 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ba330 : bv 32 := 0x03f7d293.
Lemma F_ba330 : fetch_word Asan.M.loaded_segments (0xba380 : word) = Some W_ba330.
Proof. vm_refl. Qed.
Lemma D_ba330 : decode_any W_ba330 = Some (ShiftImm ALU_SRL 5 15 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_ba334 : bv 32 := 0x4027d793.
Lemma F_ba334 : fetch_word Asan.M.loaded_segments (0xba384 : word) = Some W_ba334.
Proof. vm_refl. Qed.
Lemma D_ba334 : decode_any W_ba334 = Some (ShiftImm ALU_SRA 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ba338 : bv 32 := 0x005787b3.
Lemma F_ba338 : fetch_word Asan.M.loaded_segments (0xba388 : word) = Some W_ba338.
Proof. vm_refl. Qed.
Lemma D_ba338 : decode_any W_ba338 = Some (Op ALU_ADD 15 15 5, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rba46c_ba480.
Module Na0_code_rba6c0_ba6c4.
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

Definition W_ba57c : bv 32 := 0x00008067.
Lemma F_ba57c : fetch_word Asan.M.loaded_segments (0xba5cc : word) = Some W_ba57c.
Proof. vm_refl. Qed.
Lemma D_ba57c : decode_any W_ba57c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rba6c0_ba6c4.
Module Na0_code_rb94bc_b94c0.
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

Definition W_b9378 : bv 32 := 0x00008067.
Lemma F_b9378 : fetch_word Asan.M.loaded_segments (0xb93c8 : word) = Some W_b9378.
Proof. vm_refl. Qed.
Lemma D_b9378 : decode_any W_b9378 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb94bc_b94c0.
Module Na0_code_rb22d0_b22d4.
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

Definition W_b218c : bv 32 := 0x00008067.
Lemma F_b218c : fetch_word Asan.M.loaded_segments (0xb21dc : word) = Some W_b218c.
Proof. vm_refl. Qed.
Lemma D_b218c : decode_any W_b218c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb22d0_b22d4.
Module Na0_code_rb1aac_b1ab0.
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

Definition W_b1968 : bv 32 := 0x00008067.
Lemma F_b1968 : fetch_word Asan.M.loaded_segments (0xb19b8 : word) = Some W_b1968.
Proof. vm_refl. Qed.
Lemma D_b1968 : decode_any W_b1968 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb1aac_b1ab0.
Module Na0_code_rb52d0_b52d4.
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

Definition W_b518c : bv 32 := 0x00008067.
Lemma F_b518c : fetch_word Asan.M.loaded_segments (0xb51dc : word) = Some W_b518c.
Proof. vm_refl. Qed.
Lemma D_b518c : decode_any W_b518c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb52d0_b52d4.
Module Na0_code_rc6188_c618c.
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

Definition W_d3068 : bv 32 := 0x00008067.
Lemma F_d3068 : fetch_word Asan.M.loaded_segments (0xd30b8 : word) = Some W_d3068.
Proof. vm_refl. Qed.
Lemma D_d3068 : decode_any W_d3068 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc6188_c618c.
Module Na0_code_rb5cac_b5cb0.
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

Definition W_d36ac : bv 32 := 0x0005cc83.
Lemma F_d36ac : fetch_word Asan.M.loaded_segments (0xd36fc : word) = Some W_d36ac.
Proof. vm_refl. Qed.
Lemma D_d36ac : decode_any W_d36ac = Some (Load SZ1 false 25 11 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb5cac_b5cb0.
Module Na0_code_rb5e74_b5e78.
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

Definition W_d3874 : bv 32 := 0x00008067.
Lemma F_d3874 : fetch_word Asan.M.loaded_segments (0xd38c4 : word) = Some W_d3874.
Proof. vm_refl. Qed.
Lemma D_d3874 : decode_any W_d3874 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb5e74_b5e78.
Module Na0_code_rc6d9c_c6da0.
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

Definition W_d3c7c : bv 32 := 0x00008067.
Lemma F_d3c7c : fetch_word Asan.M.loaded_segments (0xd3ccc : word) = Some W_d3c7c.
Proof. vm_refl. Qed.
Lemma D_d3c7c : decode_any W_d3c7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc6d9c_c6da0.
Module Na0_code_rc5b30_c5b34.
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

Definition W_c5f14 : bv 32 := 0x00008067.
Lemma F_c5f14 : fetch_word Asan.M.loaded_segments (0xc5f64 : word) = Some W_c5f14.
Proof. vm_refl. Qed.
Lemma D_c5f14 : decode_any W_c5f14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc5b30_c5b34.
Module Na0_code_rc3a10_c3a14.
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

Definition W_d09cc : bv 32 := 0x00008067.
Lemma F_d09cc : fetch_word Asan.M.loaded_segments (0xd0a1c : word) = Some W_d09cc.
Proof. vm_refl. Qed.
Lemma D_d09cc : decode_any W_d09cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc3a10_c3a14.
Module Na0_code_rc6fc4_c6fc8.
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

Definition W_ccfa0 : bv 32 := 0x00008067.
Lemma F_ccfa0 : fetch_word Asan.M.loaded_segments (0xccff0 : word) = Some W_ccfa0.
Proof. vm_refl. Qed.
Lemma D_ccfa0 : decode_any W_ccfa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc6fc4_c6fc8.
Module Na0_code_r80560_806c8.
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

Definition W_a1820 : bv 32 := 0x00008513.
Lemma F_a1820 : fetch_word Asan.M.loaded_segments (0xa1870 : word) = Some W_a1820.
Proof. vm_refl. Qed.
Lemma D_a1820 : decode_any W_a1820 = Some (OpImm ALU_ADD 10 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1824 : bv 32 := 0x00008067.
Lemma F_a1824 : fetch_word Asan.M.loaded_segments (0xa1874 : word) = Some W_a1824.
Proof. vm_refl. Qed.
Lemma D_a1824 : decode_any W_a1824 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1828 : bv 32 := 0xfc010113.
Lemma F_a1828 : fetch_word Asan.M.loaded_segments (0xa1878 : word) = Some W_a1828.
Proof. vm_refl. Qed.
Lemma D_a1828 : decode_any W_a1828 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_a182c : bv 32 := 0x02113c23.
Lemma F_a182c : fetch_word Asan.M.loaded_segments (0xa187c : word) = Some W_a182c.
Proof. vm_refl. Qed.
Lemma D_a182c : decode_any W_a182c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1830 : bv 32 := 0x02813823.
Lemma F_a1830 : fetch_word Asan.M.loaded_segments (0xa1880 : word) = Some W_a1830.
Proof. vm_refl. Qed.
Lemma D_a1830 : decode_any W_a1830 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1834 : bv 32 := 0x02913423.
Lemma F_a1834 : fetch_word Asan.M.loaded_segments (0xa1884 : word) = Some W_a1834.
Proof. vm_refl. Qed.
Lemma D_a1834 : decode_any W_a1834 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1838 : bv 32 := 0x03213023.
Lemma F_a1838 : fetch_word Asan.M.loaded_segments (0xa1888 : word) = Some W_a1838.
Proof. vm_refl. Qed.
Lemma D_a1838 : decode_any W_a1838 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a183c : bv 32 := 0x01313c23.
Lemma F_a183c : fetch_word Asan.M.loaded_segments (0xa188c : word) = Some W_a183c.
Proof. vm_refl. Qed.
Lemma D_a183c : decode_any W_a183c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1840 : bv 32 := 0x01413823.
Lemma F_a1840 : fetch_word Asan.M.loaded_segments (0xa1890 : word) = Some W_a1840.
Proof. vm_refl. Qed.
Lemma D_a1840 : decode_any W_a1840 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1844 : bv 32 := 0x01513423.
Lemma F_a1844 : fetch_word Asan.M.loaded_segments (0xa1894 : word) = Some W_a1844.
Proof. vm_refl. Qed.
Lemma D_a1844 : decode_any W_a1844 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1848 : bv 32 := 0x01613023.
Lemma F_a1848 : fetch_word Asan.M.loaded_segments (0xa1898 : word) = Some W_a1848.
Proof. vm_refl. Qed.
Lemma D_a1848 : decode_any W_a1848 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a184c : bv 32 := 0x00068493.
Lemma F_a184c : fetch_word Asan.M.loaded_segments (0xa189c : word) = Some W_a184c.
Proof. vm_refl. Qed.
Lemma D_a184c : decode_any W_a184c = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1850 : bv 32 := 0x02079413.
Lemma F_a1850 : fetch_word Asan.M.loaded_segments (0xa18a0 : word) = Some W_a1850.
Proof. vm_refl. Qed.
Lemma D_a1850 : decode_any W_a1850 = Some (ShiftImm ALU_SLL 8 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1854 : bv 32 := 0x00100693.
Lemma F_a1854 : fetch_word Asan.M.loaded_segments (0xa18a4 : word) = Some W_a1854.
Proof. vm_refl. Qed.
Lemma D_a1854 : decode_any W_a1854 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1858 : bv 32 := 0x02045413.
Lemma F_a1858 : fetch_word Asan.M.loaded_segments (0xa18a8 : word) = Some W_a1858.
Proof. vm_refl. Qed.
Lemma D_a1858 : decode_any W_a1858 = Some (ShiftImm ALU_SRL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a185c : bv 32 := 0x0ef6f863.
Lemma F_a185c : fetch_word Asan.M.loaded_segments (0xa18ac : word) = Some W_a185c.
Proof. vm_refl. Qed.
Lemma D_a185c : decode_any W_a185c = Some (Branch BC_GEU 13 15 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1860 : bv 32 := 0x000b5697.
Lemma F_a1860 : fetch_word Asan.M.loaded_segments (0xa18b0 : word) = Some W_a1860.
Proof. vm_refl. Qed.
Lemma D_a1860 : decode_any W_a1860 = Some (Auipc 13 181, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1864 : bv 32 := 0x4c86b903.
Lemma F_a1864 : fetch_word Asan.M.loaded_segments (0xa18b4 : word) = Some W_a1864.
Proof. vm_refl. Qed.
Lemma D_a1864 : decode_any W_a1864 = Some (Load SZ8 true 18 13 1224, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1868 : bv 32 := 0x00093683.
Lemma F_a1868 : fetch_word Asan.M.loaded_segments (0xa18b8 : word) = Some W_a1868.
Proof. vm_refl. Qed.
Lemma D_a1868 : decode_any W_a1868 = Some (Load SZ8 true 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a186c : bv 32 := 0x00068e63.
Lemma F_a186c : fetch_word Asan.M.loaded_segments (0xa18bc : word) = Some W_a186c.
Proof. vm_refl. Qed.
Lemma D_a186c : decode_any W_a186c = Some (Branch BC_EQ 13 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1870 : bv 32 := 0x00100793.
Lemma F_a1870 : fetch_word Asan.M.loaded_segments (0xa18c0 : word) = Some W_a1870.
Proof. vm_refl. Qed.
Lemma D_a1870 : decode_any W_a1870 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1874 : bv 32 := 0x00c4d813.
Lemma F_a1874 : fetch_word Asan.M.loaded_segments (0xa18c4 : word) = Some W_a1874.
Proof. vm_refl. Qed.
Lemma D_a1874 : decode_any W_a1874 = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1878 : bv 32 := 0x00f52423.
Lemma F_a1878 : fetch_word Asan.M.loaded_segments (0xa18c8 : word) = Some W_a1878.
Proof. vm_refl. Qed.
Lemma D_a1878 : decode_any W_a1878 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a187c : bv 32 := 0x00b53823.
Lemma F_a187c : fetch_word Asan.M.loaded_segments (0xa18cc : word) = Some W_a187c.
Proof. vm_refl. Qed.
Lemma D_a187c : decode_any W_a187c = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1880 : bv 32 := 0x04081463.
Lemma F_a1880 : fetch_word Asan.M.loaded_segments (0xa18d0 : word) = Some W_a1880.
Proof. vm_refl. Qed.
Lemma D_a1880 : decode_any W_a1880 = Some (Branch BC_NE 16 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18c8 : bv 32 := 0x0a977263.
Lemma F_a18c8 : fetch_word Asan.M.loaded_segments (0xa1918 : word) = Some W_a18c8.
Proof. vm_refl. Qed.
Lemma D_a18c8 : decode_any W_a18c8 = Some (Branch BC_GEU 14 9 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18cc : bv 32 := 0x04c77c63.
Lemma F_a18cc : fetch_word Asan.M.loaded_segments (0xa191c : word) = Some W_a18cc.
Proof. vm_refl. Qed.
Lemma D_a18cc : decode_any W_a18cc = Some (Branch BC_GEU 14 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18d0 : bv 32 := 0xff048493.
Lemma F_a18d0 : fetch_word Asan.M.loaded_segments (0xa1920 : word) = Some W_a18d0.
Proof. vm_refl. Qed.
Lemma D_a18d0 : decode_any W_a18d0 = Some (OpImm ALU_ADD 9 9 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18d4 : bv 32 := 0x04967863.
Lemma F_a18d4 : fetch_word Asan.M.loaded_segments (0xa1924 : word) = Some W_a18d4.
Proof. vm_refl. Qed.
Lemma D_a18d4 : decode_any W_a18d4 = Some (Branch BC_GEU 12 9 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18d8 : bv 32 := 0x00767713.
Lemma F_a18d8 : fetch_word Asan.M.loaded_segments (0xa1928 : word) = Some W_a18d8.
Proof. vm_refl. Qed.
Lemma D_a18d8 : decode_any W_a18d8 = Some (OpImm ALU_AND 14 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18dc : bv 32 := 0x04071463.
Lemma F_a18dc : fetch_word Asan.M.loaded_segments (0xa192c : word) = Some W_a18dc.
Proof. vm_refl. Qed.
Lemma D_a18dc : decode_any W_a18dc = Some (Branch BC_NE 14 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18e0 : bv 32 := 0x01050713.
Lemma F_a18e0 : fetch_word Asan.M.loaded_segments (0xa1930 : word) = Some W_a18e0.
Proof. vm_refl. Qed.
Lemma D_a18e0 : decode_any W_a18e0 = Some (OpImm ALU_ADD 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18e4 : bv 32 := 0x00100793.
Lemma F_a18e4 : fetch_word Asan.M.loaded_segments (0xa1934 : word) = Some W_a18e4.
Proof. vm_refl. Qed.
Lemma D_a18e4 : decode_any W_a18e4 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18e8 : bv 32 := 0x0287fe63.
Lemma F_a18e8 : fetch_word Asan.M.loaded_segments (0xa1938 : word) = Some W_a18e8.
Proof. vm_refl. Qed.
Lemma D_a18e8 : decode_any W_a18e8 = Some (Branch BC_GEU 15 8 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18ec : bv 32 := 0xff863803.
Lemma F_a18ec : fetch_word Asan.M.loaded_segments (0xa193c : word) = Some W_a18ec.
Proof. vm_refl. Qed.
Lemma D_a18ec : decode_any W_a18ec = Some (Load SZ8 true 16 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18f0 : bv 32 := 0x02d86a63.
Lemma F_a18f0 : fetch_word Asan.M.loaded_segments (0xa1940 : word) = Some W_a18f0.
Proof. vm_refl. Qed.
Lemma D_a18f0 : decode_any W_a18f0 = Some (Branch BC_LTU 16 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18f4 : bv 32 := 0x00b80c63.
Lemma F_a18f4 : fetch_word Asan.M.loaded_segments (0xa1944 : word) = Some W_a18f4.
Proof. vm_refl. Qed.
Lemma D_a18f4 : decode_any W_a18f4 = Some (Branch BC_EQ 16 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18f8 : bv 32 := 0x00379893.
Lemma F_a18f8 : fetch_word Asan.M.loaded_segments (0xa1948 : word) = Some W_a18f8.
Proof. vm_refl. Qed.
Lemma D_a18f8 : decode_any W_a18f8 = Some (ShiftImm ALU_SLL 17 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18fc : bv 32 := 0x00178793.
Lemma F_a18fc : fetch_word Asan.M.loaded_segments (0xa194c : word) = Some W_a18fc.
Proof. vm_refl. Qed.
Lemma D_a18fc : decode_any W_a18fc = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1900 : bv 32 := 0x011708b3.
Lemma F_a1900 : fetch_word Asan.M.loaded_segments (0xa1950 : word) = Some W_a1900.
Proof. vm_refl. Qed.
Lemma D_a1900 : decode_any W_a1900 = Some (Op ALU_ADD 17 14 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1904 : bv 32 := 0x00f52423.
Lemma F_a1904 : fetch_word Asan.M.loaded_segments (0xa1954 : word) = Some W_a1904.
Proof. vm_refl. Qed.
Lemma D_a1904 : decode_any W_a1904 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1908 : bv 32 := 0x0108b023.
Lemma F_a1908 : fetch_word Asan.M.loaded_segments (0xa1958 : word) = Some W_a1908.
Proof. vm_refl. Qed.
Lemma D_a1908 : decode_any W_a1908 = Some (Store SZ8 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a190c : bv 32 := 0xff063803.
Lemma F_a190c : fetch_word Asan.M.loaded_segments (0xa195c : word) = Some W_a190c.
Proof. vm_refl. Qed.
Lemma D_a190c : decode_any W_a190c = Some (Load SZ8 true 16 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1910 : bv 32 := 0x01067a63.
Lemma F_a1910 : fetch_word Asan.M.loaded_segments (0xa1960 : word) = Some W_a1910.
Proof. vm_refl. Qed.
Lemma D_a1910 : decode_any W_a1910 = Some (Branch BC_GEU 12 16 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1914 : bv 32 := 0x00987863.
Lemma F_a1914 : fetch_word Asan.M.loaded_segments (0xa1964 : word) = Some W_a1914.
Proof. vm_refl. Qed.
Lemma D_a1914 : decode_any W_a1914 = Some (Branch BC_GEU 16 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1918 : bv 32 := 0x00787893.
Lemma F_a1918 : fetch_word Asan.M.loaded_segments (0xa1968 : word) = Some W_a1918.
Proof. vm_refl. Qed.
Lemma D_a1918 : decode_any W_a1918 = Some (OpImm ALU_AND 17 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a191c : bv 32 := 0x00080613.
Lemma F_a191c : fetch_word Asan.M.loaded_segments (0xa196c : word) = Some W_a191c.
Proof. vm_refl. Qed.
Lemma D_a191c : decode_any W_a191c = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1920 : bv 32 := 0xfc0884e3.
Lemma F_a1920 : fetch_word Asan.M.loaded_segments (0xa1970 : word) = Some W_a1920.
Proof. vm_refl. Qed.
Lemma D_a1920 : decode_any W_a1920 = Some (Branch BC_EQ 17 0 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1924 : bv 32 := 0x03813083.
Lemma F_a1924 : fetch_word Asan.M.loaded_segments (0xa1974 : word) = Some W_a1924.
Proof. vm_refl. Qed.
Lemma D_a1924 : decode_any W_a1924 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1928 : bv 32 := 0x03013403.
Lemma F_a1928 : fetch_word Asan.M.loaded_segments (0xa1978 : word) = Some W_a1928.
Proof. vm_refl. Qed.
Lemma D_a1928 : decode_any W_a1928 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a192c : bv 32 := 0x02813483.
Lemma F_a192c : fetch_word Asan.M.loaded_segments (0xa197c : word) = Some W_a192c.
Proof. vm_refl. Qed.
Lemma D_a192c : decode_any W_a192c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1930 : bv 32 := 0x02013903.
Lemma F_a1930 : fetch_word Asan.M.loaded_segments (0xa1980 : word) = Some W_a1930.
Proof. vm_refl. Qed.
Lemma D_a1930 : decode_any W_a1930 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1934 : bv 32 := 0x01813983.
Lemma F_a1934 : fetch_word Asan.M.loaded_segments (0xa1984 : word) = Some W_a1934.
Proof. vm_refl. Qed.
Lemma D_a1934 : decode_any W_a1934 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1938 : bv 32 := 0x01013a03.
Lemma F_a1938 : fetch_word Asan.M.loaded_segments (0xa1988 : word) = Some W_a1938.
Proof. vm_refl. Qed.
Lemma D_a1938 : decode_any W_a1938 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a193c : bv 32 := 0x00813a83.
Lemma F_a193c : fetch_word Asan.M.loaded_segments (0xa198c : word) = Some W_a193c.
Proof. vm_refl. Qed.
Lemma D_a193c : decode_any W_a193c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1940 : bv 32 := 0x00013b03.
Lemma F_a1940 : fetch_word Asan.M.loaded_segments (0xa1990 : word) = Some W_a1940.
Proof. vm_refl. Qed.
Lemma D_a1940 : decode_any W_a1940 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1944 : bv 32 := 0x04010113.
Lemma F_a1944 : fetch_word Asan.M.loaded_segments (0xa1994 : word) = Some W_a1944.
Proof. vm_refl. Qed.
Lemma D_a1944 : decode_any W_a1944 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1948 : bv 32 := 0x00008067.
Lemma F_a1948 : fetch_word Asan.M.loaded_segments (0xa1998 : word) = Some W_a1948.
Proof. vm_refl. Qed.
Lemma D_a1948 : decode_any W_a1948 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r80560_806c8.
Module Na0_code_r8d0d0_8d0e8.
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

Definition W_ae39c : bv 32 := 0x000a9517.
Lemma F_ae39c : fetch_word Asan.M.loaded_segments (0xae3ec : word) = Some W_ae39c.
Proof. vm_refl. Qed.
Lemma D_ae39c : decode_any W_ae39c = Some (Auipc 10 169, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3a0 : bv 32 := 0x60c53503.
Lemma F_ae3a0 : fetch_word Asan.M.loaded_segments (0xae3f0 : word) = Some W_ae3a0.
Proof. vm_refl. Qed.
Lemma D_ae3a0 : decode_any W_ae3a0 = Some (Load SZ8 true 10 10 1548, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3a4 : bv 32 := 0x00450533.
Lemma F_ae3a4 : fetch_word Asan.M.loaded_segments (0xae3f4 : word) = Some W_ae3a4.
Proof. vm_refl. Qed.
Lemma D_ae3a4 : decode_any W_ae3a4 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3a8 : bv 32 := 0x00052503.
Lemma F_ae3a8 : fetch_word Asan.M.loaded_segments (0xae3f8 : word) = Some W_ae3a8.
Proof. vm_refl. Qed.
Lemma D_ae3a8 : decode_any W_ae3a8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3ac : bv 32 := 0x00a02533.
Lemma F_ae3ac : fetch_word Asan.M.loaded_segments (0xae3fc : word) = Some W_ae3ac.
Proof. vm_refl. Qed.
Lemma D_ae3ac : decode_any W_ae3ac = Some (Op ALU_SLT 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae3b0 : bv 32 := 0x00008067.
Lemma F_ae3b0 : fetch_word Asan.M.loaded_segments (0xae400 : word) = Some W_ae3b0.
Proof. vm_refl. Qed.
Lemma D_ae3b0 : decode_any W_ae3b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r8d0d0_8d0e8.
Module Na0_code_r80bc4_80cdc.
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

Definition W_a1e84 : bv 32 := 0xfc010113.
Lemma F_a1e84 : fetch_word Asan.M.loaded_segments (0xa1ed4 : word) = Some W_a1e84.
Proof. vm_refl. Qed.
Lemma D_a1e84 : decode_any W_a1e84 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1e88 : bv 32 := 0x02113c23.
Lemma F_a1e88 : fetch_word Asan.M.loaded_segments (0xa1ed8 : word) = Some W_a1e88.
Proof. vm_refl. Qed.
Lemma D_a1e88 : decode_any W_a1e88 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1e8c : bv 32 := 0x02813823.
Lemma F_a1e8c : fetch_word Asan.M.loaded_segments (0xa1edc : word) = Some W_a1e8c.
Proof. vm_refl. Qed.
Lemma D_a1e8c : decode_any W_a1e8c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1e90 : bv 32 := 0x02913423.
Lemma F_a1e90 : fetch_word Asan.M.loaded_segments (0xa1ee0 : word) = Some W_a1e90.
Proof. vm_refl. Qed.
Lemma D_a1e90 : decode_any W_a1e90 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1e94 : bv 32 := 0x03213023.
Lemma F_a1e94 : fetch_word Asan.M.loaded_segments (0xa1ee4 : word) = Some W_a1e94.
Proof. vm_refl. Qed.
Lemma D_a1e94 : decode_any W_a1e94 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1e98 : bv 32 := 0x01313c23.
Lemma F_a1e98 : fetch_word Asan.M.loaded_segments (0xa1ee8 : word) = Some W_a1e98.
Proof. vm_refl. Qed.
Lemma D_a1e98 : decode_any W_a1e98 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1e9c : bv 32 := 0x01413823.
Lemma F_a1e9c : fetch_word Asan.M.loaded_segments (0xa1eec : word) = Some W_a1e9c.
Proof. vm_refl. Qed.
Lemma D_a1e9c : decode_any W_a1e9c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ea0 : bv 32 := 0x01513423.
Lemma F_a1ea0 : fetch_word Asan.M.loaded_segments (0xa1ef0 : word) = Some W_a1ea0.
Proof. vm_refl. Qed.
Lemma D_a1ea0 : decode_any W_a1ea0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ea4 : bv 32 := 0x00058413.
Lemma F_a1ea4 : fetch_word Asan.M.loaded_segments (0xa1ef4 : word) = Some W_a1ea4.
Proof. vm_refl. Qed.
Lemma D_a1ea4 : decode_any W_a1ea4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ea8 : bv 32 := 0x0015b593.
Lemma F_a1ea8 : fetch_word Asan.M.loaded_segments (0xa1ef8 : word) = Some W_a1ea8.
Proof. vm_refl. Qed.
Lemma D_a1ea8 : decode_any W_a1ea8 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1eac : bv 32 := 0x7ff50293.
Lemma F_a1eac : fetch_word Asan.M.loaded_segments (0xa1efc : word) = Some W_a1eac.
Proof. vm_refl. Qed.
Lemma D_a1eac : decode_any W_a1eac = Some (OpImm ALU_ADD 5 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1eb0 : bv 32 := 0xfff58593.
Lemma F_a1eb0 : fetch_word Asan.M.loaded_segments (0xa1f00 : word) = Some W_a1eb0.
Proof. vm_refl. Qed.
Lemma D_a1eb0 : decode_any W_a1eb0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1eb4 : bv 32 := 0x00d5f333.
Lemma F_a1eb4 : fetch_word Asan.M.loaded_segments (0xa1f04 : word) = Some W_a1eb4.
Proof. vm_refl. Qed.
Lemma D_a1eb4 : decode_any W_a1eb4 = Some (Op ALU_AND 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1eb8 : bv 32 := 0x00100593.
Lemma F_a1eb8 : fetch_word Asan.M.loaded_segments (0xa1f08 : word) = Some W_a1eb8.
Proof. vm_refl. Qed.
Lemma D_a1eb8 : decode_any W_a1eb8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ebc : bv 32 := 0x0062b4a3.
Lemma F_a1ebc : fetch_word Asan.M.loaded_segments (0xa1f0c : word) = Some W_a1ebc.
Proof. vm_refl. Qed.
Lemma D_a1ebc : decode_any W_a1ebc = Some (Store SZ8 5 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ec0 : bv 32 := 0x00b40863.
Lemma F_a1ec0 : fetch_word Asan.M.loaded_segments (0xa1f10 : word) = Some W_a1ec0.
Proof. vm_refl. Qed.
Lemma D_a1ec0 : decode_any W_a1ec0 = Some (Branch BC_EQ 8 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ec4 : bv 32 := 0x02041c63.
Lemma F_a1ec4 : fetch_word Asan.M.loaded_segments (0xa1f14 : word) = Some W_a1ec4.
Proof. vm_refl. Qed.
Lemma D_a1ec4 : decode_any W_a1ec4 = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1efc : bv 32 := 0x06089463.
Lemma F_a1efc : fetch_word Asan.M.loaded_segments (0xa1f4c : word) = Some W_a1efc.
Proof. vm_refl. Qed.
Lemma D_a1efc : decode_any W_a1efc = Some (Branch BC_NE 17 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f64 : bv 32 := 0x00060593.
Lemma F_a1f64 : fetch_word Asan.M.loaded_segments (0xa1fb4 : word) = Some W_a1f64.
Proof. vm_refl. Qed.
Lemma D_a1f64 : decode_any W_a1f64 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f68 : bv 32 := 0x00068613.
Lemma F_a1f68 : fetch_word Asan.M.loaded_segments (0xa1fb8 : word) = Some W_a1f68.
Proof. vm_refl. Qed.
Lemma D_a1f68 : decode_any W_a1f68 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f6c : bv 32 := 0x00078693.
Lemma F_a1f6c : fetch_word Asan.M.loaded_segments (0xa1fbc : word) = Some W_a1f6c.
Proof. vm_refl. Qed.
Lemma D_a1f6c : decode_any W_a1f6c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f70 : bv 32 := 0x00080713.
Lemma F_a1f70 : fetch_word Asan.M.loaded_segments (0xa1fc0 : word) = Some W_a1f70.
Proof. vm_refl. Qed.
Lemma D_a1f70 : decode_any W_a1f70 = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f74 : bv 32 := 0x00040793.
Lemma F_a1f74 : fetch_word Asan.M.loaded_segments (0xa1fc4 : word) = Some W_a1f74.
Proof. vm_refl. Qed.
Lemma D_a1f74 : decode_any W_a1f74 = Some (OpImm ALU_ADD 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f78 : bv 32 := 0x03813083.
Lemma F_a1f78 : fetch_word Asan.M.loaded_segments (0xa1fc8 : word) = Some W_a1f78.
Proof. vm_refl. Qed.
Lemma D_a1f78 : decode_any W_a1f78 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f7c : bv 32 := 0x03013403.
Lemma F_a1f7c : fetch_word Asan.M.loaded_segments (0xa1fcc : word) = Some W_a1f7c.
Proof. vm_refl. Qed.
Lemma D_a1f7c : decode_any W_a1f7c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f80 : bv 32 := 0x02813483.
Lemma F_a1f80 : fetch_word Asan.M.loaded_segments (0xa1fd0 : word) = Some W_a1f80.
Proof. vm_refl. Qed.
Lemma D_a1f80 : decode_any W_a1f80 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f84 : bv 32 := 0x02013903.
Lemma F_a1f84 : fetch_word Asan.M.loaded_segments (0xa1fd4 : word) = Some W_a1f84.
Proof. vm_refl. Qed.
Lemma D_a1f84 : decode_any W_a1f84 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f88 : bv 32 := 0x01813983.
Lemma F_a1f88 : fetch_word Asan.M.loaded_segments (0xa1fd8 : word) = Some W_a1f88.
Proof. vm_refl. Qed.
Lemma D_a1f88 : decode_any W_a1f88 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f8c : bv 32 := 0x01013a03.
Lemma F_a1f8c : fetch_word Asan.M.loaded_segments (0xa1fdc : word) = Some W_a1f8c.
Proof. vm_refl. Qed.
Lemma D_a1f8c : decode_any W_a1f8c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f90 : bv 32 := 0x00813a83.
Lemma F_a1f90 : fetch_word Asan.M.loaded_segments (0xa1fe0 : word) = Some W_a1f90.
Proof. vm_refl. Qed.
Lemma D_a1f90 : decode_any W_a1f90 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f94 : bv 32 := 0x04010113.
Lemma F_a1f94 : fetch_word Asan.M.loaded_segments (0xa1fe4 : word) = Some W_a1f94.
Proof. vm_refl. Qed.
Lemma D_a1f94 : decode_any W_a1f94 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f98 : bv 32 := 0x891ff06f.
Lemma F_a1f98 : fetch_word Asan.M.loaded_segments (0xa1fe8 : word) = Some W_a1f98.
Proof. vm_refl. Qed.
Lemma D_a1f98 : decode_any W_a1f98 = Some (Jal 0 2095248, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r80bc4_80cdc.
