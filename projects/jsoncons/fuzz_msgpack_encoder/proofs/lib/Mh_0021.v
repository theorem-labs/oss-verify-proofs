(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain.
Module Ns0_code_ra93ac_a9404.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b9d40 : bv 32 := 0x08b50663.
Lemma F_b9d40 : fetch_word Plain.M.loaded_segments (0xb9d7c : word) = Some W_b9d40.
Proof. vm_refl. Qed.
Lemma D_b9d40 : decode_any W_b9d40 = Some (Branch BC_EQ 10 11 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d44 : bv 32 := 0x00a606b3.
Lemma F_b9d44 : fetch_word Plain.M.loaded_segments (0xb9d80 : word) = Some W_b9d44.
Proof. vm_refl. Qed.
Lemma D_b9d44 : decode_any W_b9d44 = Some (Op ALU_ADD 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d48 : bv 32 := 0x00161713.
Lemma F_b9d48 : fetch_word Plain.M.loaded_segments (0xb9d84 : word) = Some W_b9d48.
Proof. vm_refl. Qed.
Lemma D_b9d48 : decode_any W_b9d48 = Some (ShiftImm ALU_SLL 14 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d4c : bv 32 := 0x40d586b3.
Lemma F_b9d4c : fetch_word Plain.M.loaded_segments (0xb9d88 : word) = Some W_b9d4c.
Proof. vm_refl. Qed.
Lemma D_b9d4c : decode_any W_b9d4c = Some (Op ALU_SUB 13 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d50 : bv 32 := 0x40e00733.
Lemma F_b9d50 : fetch_word Plain.M.loaded_segments (0xb9d8c : word) = Some W_b9d50.
Proof. vm_refl. Qed.
Lemma D_b9d50 : decode_any W_b9d50 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d54 : bv 32 := 0x04d77063.
Lemma F_b9d54 : fetch_word Plain.M.loaded_segments (0xb9d90 : word) = Some W_b9d54.
Proof. vm_refl. Qed.
Lemma D_b9d54 : decode_any W_b9d54 = Some (Branch BC_GEU 14 13 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d58 : bv 32 := 0x00a5c6b3.
Lemma F_b9d58 : fetch_word Plain.M.loaded_segments (0xb9d94 : word) = Some W_b9d58.
Proof. vm_refl. Qed.
Lemma D_b9d58 : decode_any W_b9d58 = Some (Op ALU_XOR 13 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d5c : bv 32 := 0x0076f693.
Lemma F_b9d5c : fetch_word Plain.M.loaded_segments (0xb9d98 : word) = Some W_b9d5c.
Proof. vm_refl. Qed.
Lemma D_b9d5c : decode_any W_b9d5c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d60 : bv 32 := 0x02b57c63.
Lemma F_b9d60 : fetch_word Plain.M.loaded_segments (0xb9d9c : word) = Some W_b9d60.
Proof. vm_refl. Qed.
Lemma D_b9d60 : decode_any W_b9d60 = Some (Branch BC_GEU 10 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d64 : bv 32 := 0x06068663.
Lemma F_b9d64 : fetch_word Plain.M.loaded_segments (0xb9da0 : word) = Some W_b9d64.
Proof. vm_refl. Qed.
Lemma D_b9d64 : decode_any W_b9d64 = Some (Branch BC_EQ 13 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d68 : bv 32 := 0x00050693.
Lemma F_b9d68 : fetch_word Plain.M.loaded_segments (0xb9da4 : word) = Some W_b9d68.
Proof. vm_refl. Qed.
Lemma D_b9d68 : decode_any W_b9d68 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d6c : bv 32 := 0x00058713.
Lemma F_b9d6c : fetch_word Plain.M.loaded_segments (0xb9da8 : word) = Some W_b9d6c.
Proof. vm_refl. Qed.
Lemma D_b9d6c : decode_any W_b9d6c = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d70 : bv 32 := 0x04060e63.
Lemma F_b9d70 : fetch_word Plain.M.loaded_segments (0xb9dac : word) = Some W_b9d70.
Proof. vm_refl. Qed.
Lemma D_b9d70 : decode_any W_b9d70 = Some (Branch BC_EQ 12 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d74 : bv 32 := 0x00c68633.
Lemma F_b9d74 : fetch_word Plain.M.loaded_segments (0xb9db0 : word) = Some W_b9d74.
Proof. vm_refl. Qed.
Lemma D_b9d74 : decode_any W_b9d74 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d78 : bv 32 := 0x00074583.
Lemma F_b9d78 : fetch_word Plain.M.loaded_segments (0xb9db4 : word) = Some W_b9d78.
Proof. vm_refl. Qed.
Lemma D_b9d78 : decode_any W_b9d78 = Some (Load SZ1 false 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d7c : bv 32 := 0x00170713.
Lemma F_b9d7c : fetch_word Plain.M.loaded_segments (0xb9db8 : word) = Some W_b9d7c.
Proof. vm_refl. Qed.
Lemma D_b9d7c : decode_any W_b9d7c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d80 : bv 32 := 0x00168793.
Lemma F_b9d80 : fetch_word Plain.M.loaded_segments (0xb9dbc : word) = Some W_b9d80.
Proof. vm_refl. Qed.
Lemma D_b9d80 : decode_any W_b9d80 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d84 : bv 32 := 0x00b68023.
Lemma F_b9d84 : fetch_word Plain.M.loaded_segments (0xb9dc0 : word) = Some W_b9d84.
Proof. vm_refl. Qed.
Lemma D_b9d84 : decode_any W_b9d84 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d88 : bv 32 := 0x00078693.
Lemma F_b9d88 : fetch_word Plain.M.loaded_segments (0xb9dc4 : word) = Some W_b9d88.
Proof. vm_refl. Qed.
Lemma D_b9d88 : decode_any W_b9d88 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d8c : bv 32 := 0xfec796e3.
Lemma F_b9d8c : fetch_word Plain.M.loaded_segments (0xb9dc8 : word) = Some W_b9d8c.
Proof. vm_refl. Qed.
Lemma D_b9d8c : decode_any W_b9d8c = Some (Branch BC_NE 15 12 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d90 : bv 32 := 0x03c0006f.
Lemma F_b9d90 : fetch_word Plain.M.loaded_segments (0xb9dcc : word) = Some W_b9d90.
Proof. vm_refl. Qed.
Lemma D_b9d90 : decode_any W_b9d90 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_b9d94 : bv 32 := 0xba9ff06f.
Lemma F_b9d94 : fetch_word Plain.M.loaded_segments (0xb9dd0 : word) = Some W_b9d94.
Proof. vm_refl. Qed.
Lemma D_b9d94 : decode_any W_b9d94 = Some (Jal 0 2096040, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_ra93ac_a9404.
Module Ns0_code_r3c73c_3c740.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_3cdb8 : bv 32 := 0x00008067.
Lemma F_3cdb8 : fetch_word Plain.M.loaded_segments (0x3ce00 : word) = Some W_3cdb8.
Proof. vm_refl. Qed.
Lemma D_3cdb8 : decode_any W_3cdb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3c73c_3c740.
Module Ns0_code_r3c898_3c89c.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_3cf14 : bv 32 := 0x00008067.
Lemma F_3cf14 : fetch_word Plain.M.loaded_segments (0x3cf5c : word) = Some W_3cf14.
Proof. vm_refl. Qed.
Lemma D_3cf14 : decode_any W_3cf14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3c898_3c89c.
Module Ns0_code_r62758_6275c.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_663f4 : bv 32 := 0x00008067.
Lemma F_663f4 : fetch_word Plain.M.loaded_segments (0x6643c : word) = Some W_663f4.
Proof. vm_refl. Qed.
Lemma D_663f4 : decode_any W_663f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r62758_6275c.
Module Ns0_code_r3e358_3e35c.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_3e9d4 : bv 32 := 0x00008067.
Lemma F_3e9d4 : fetch_word Plain.M.loaded_segments (0x3ea1c : word) = Some W_3e9d4.
Proof. vm_refl. Qed.
Lemma D_3e9d4 : decode_any W_3e9d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3e358_3e35c.
Module Ns0_code_r3e4b4_3e4b8.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_3eb30 : bv 32 := 0x00008067.
Lemma F_3eb30 : fetch_word Plain.M.loaded_segments (0x3eb78 : word) = Some W_3eb30.
Proof. vm_refl. Qed.
Lemma D_3eb30 : decode_any W_3eb30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3e4b4_3e4b8.
Module Ns0_code_r62890_62894.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6652c : bv 32 := 0x00008067.
Lemma F_6652c : fetch_word Plain.M.loaded_segments (0x66574 : word) = Some W_6652c.
Proof. vm_refl. Qed.
Lemma D_6652c : decode_any W_6652c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r62890_62894.
