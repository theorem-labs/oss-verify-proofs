(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain.
Module Ns0_code_r59000_59c90.
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

Definition W_ba8e8 : bv 32 := 0x00008067.
Lemma F_ba8e8 : fetch_word Plain.M.loaded_segments (0xba924 : word) = Some W_ba8e8.
Proof. vm_refl. Qed.
Lemma D_ba8e8 : decode_any W_ba8e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ba8ec : bv 32 := 0xfddff06f.
Lemma F_ba8ec : fetch_word Plain.M.loaded_segments (0xba928 : word) = Some W_ba8ec.
Proof. vm_refl. Qed.
Lemma D_ba8ec : decode_any W_ba8ec = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition W_bbffc : bv 32 := 0x00050213.
Lemma F_bbffc : fetch_word Plain.M.loaded_segments (0xbc038 : word) = Some W_bbffc.
Proof. vm_refl. Qed.
Lemma D_bbffc : decode_any W_bbffc = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bc000 : bv 32 := 0x00000513.
Lemma F_bc000 : fetch_word Plain.M.loaded_segments (0xbc03c : word) = Some W_bc000.
Proof. vm_refl. Qed.
Lemma D_bc000 : decode_any W_bc000 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bc004 : bv 32 := 0x00008067.
Lemma F_bc004 : fetch_word Plain.M.loaded_segments (0xbc040 : word) = Some W_bc004.
Proof. vm_refl. Qed.
Lemma D_bc004 : decode_any W_bc004 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be7e0 : bv 32 := 0xff010113.
Lemma F_be7e0 : fetch_word Plain.M.loaded_segments (0xbe81c : word) = Some W_be7e0.
Proof. vm_refl. Qed.
Lemma D_be7e0 : decode_any W_be7e0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_be7e4 : bv 32 := 0x00113423.
Lemma F_be7e4 : fetch_word Plain.M.loaded_segments (0xbe820 : word) = Some W_be7e4.
Proof. vm_refl. Qed.
Lemma D_be7e4 : decode_any W_be7e4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_be7e8 : bv 32 := 0xe49ef0ef.
Lemma F_be7e8 : fetch_word Plain.M.loaded_segments (0xbe824 : word) = Some W_be7e8.
Proof. vm_refl. Qed.
Lemma D_be7e8 : decode_any W_be7e8 = Some (Jal 1 2031176, 4%Z).
Proof. vm_refl. Qed.

Definition W_be7ec : bv 32 := 0x00050593.
Lemma F_be7ec : fetch_word Plain.M.loaded_segments (0xbe828 : word) = Some W_be7ec.
Proof. vm_refl. Qed.
Lemma D_be7ec : decode_any W_be7ec = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be7f0 : bv 32 := 0x03900513.
Lemma F_be7f0 : fetch_word Plain.M.loaded_segments (0xbe82c : word) = Some W_be7f0.
Proof. vm_refl. Qed.
Lemma D_be7f0 : decode_any W_be7f0 = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_be7f4 : bv 32 := 0x00000613.
Lemma F_be7f4 : fetch_word Plain.M.loaded_segments (0xbe830 : word) = Some W_be7f4.
Proof. vm_refl. Qed.
Lemma D_be7f4 : decode_any W_be7f4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be7f8 : bv 32 := 0x00000693.
Lemma F_be7f8 : fetch_word Plain.M.loaded_segments (0xbe834 : word) = Some W_be7f8.
Proof. vm_refl. Qed.
Lemma D_be7f8 : decode_any W_be7f8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be7fc : bv 32 := 0x00000713.
Lemma F_be7fc : fetch_word Plain.M.loaded_segments (0xbe838 : word) = Some W_be7fc.
Proof. vm_refl. Qed.
Lemma D_be7fc : decode_any W_be7fc = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be800 : bv 32 := 0x00000793.
Lemma F_be800 : fetch_word Plain.M.loaded_segments (0xbe83c : word) = Some W_be800.
Proof. vm_refl. Qed.
Lemma D_be800 : decode_any W_be800 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be804 : bv 32 := 0x00000813.
Lemma F_be804 : fetch_word Plain.M.loaded_segments (0xbe840 : word) = Some W_be804.
Proof. vm_refl. Qed.
Lemma D_be804 : decode_any W_be804 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be808 : bv 32 := 0x8e4fc0ef.
Lemma F_be808 : fetch_word Plain.M.loaded_segments (0xbe844 : word) = Some W_be808.
Proof. vm_refl. Qed.
Lemma D_be808 : decode_any W_be808 = Some (Jal 1 2080996, 4%Z).
Proof. vm_refl. Qed.

Definition W_be80c : bv 32 := 0x0005051b.
Lemma F_be80c : fetch_word Plain.M.loaded_segments (0xbe848 : word) = Some W_be80c.
Proof. vm_refl. Qed.
Lemma D_be80c : decode_any W_be80c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be810 : bv 32 := 0x00450593.
Lemma F_be810 : fetch_word Plain.M.loaded_segments (0xbe84c : word) = Some W_be810.
Proof. vm_refl. Qed.
Lemma D_be810 : decode_any W_be810 = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_be814 : bv 32 := 0x0015b593.
Lemma F_be814 : fetch_word Plain.M.loaded_segments (0xbe850 : word) = Some W_be814.
Proof. vm_refl. Qed.
Lemma D_be814 : decode_any W_be814 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_be818 : bv 32 := 0xfff58593.
Lemma F_be818 : fetch_word Plain.M.loaded_segments (0xbe854 : word) = Some W_be818.
Proof. vm_refl. Qed.
Lemma D_be818 : decode_any W_be818 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_be81c : bv 32 := 0x00a5f533.
Lemma F_be81c : fetch_word Plain.M.loaded_segments (0xbe858 : word) = Some W_be81c.
Proof. vm_refl. Qed.
Lemma D_be81c : decode_any W_be81c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_be820 : bv 32 := 0xc35ea0ef.
Lemma F_be820 : fetch_word Plain.M.loaded_segments (0xbe85c : word) = Some W_be820.
Proof. vm_refl. Qed.
Lemma D_be820 : decode_any W_be820 = Some (Jal 1 2010164, 4%Z).
Proof. vm_refl. Qed.

Definition W_be824 : bv 32 := 0x0005051b.
Lemma F_be824 : fetch_word Plain.M.loaded_segments (0xbe860 : word) = Some W_be824.
Proof. vm_refl. Qed.
Lemma D_be824 : decode_any W_be824 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be828 : bv 32 := 0x00813083.
Lemma F_be828 : fetch_word Plain.M.loaded_segments (0xbe864 : word) = Some W_be828.
Proof. vm_refl. Qed.
Lemma D_be828 : decode_any W_be828 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_be82c : bv 32 := 0x01010113.
Lemma F_be82c : fetch_word Plain.M.loaded_segments (0xbe868 : word) = Some W_be82c.
Proof. vm_refl. Qed.
Lemma D_be82c : decode_any W_be82c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_be830 : bv 32 := 0x00008067.
Lemma F_be830 : fetch_word Plain.M.loaded_segments (0xbe86c : word) = Some W_be830.
Proof. vm_refl. Qed.
Lemma D_be830 : decode_any W_be830 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be840 : bv 32 := 0xff010113.
Lemma F_be840 : fetch_word Plain.M.loaded_segments (0xbe87c : word) = Some W_be840.
Proof. vm_refl. Qed.
Lemma D_be840 : decode_any W_be840 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_be844 : bv 32 := 0x00113423.
Lemma F_be844 : fetch_word Plain.M.loaded_segments (0xbe880 : word) = Some W_be844.
Proof. vm_refl. Qed.
Lemma D_be844 : decode_any W_be844 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_be848 : bv 32 := 0x00060693.
Lemma F_be848 : fetch_word Plain.M.loaded_segments (0xbe884 : word) = Some W_be848.
Proof. vm_refl. Qed.
Lemma D_be848 : decode_any W_be848 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be84c : bv 32 := 0x00058613.
Lemma F_be84c : fetch_word Plain.M.loaded_segments (0xbe888 : word) = Some W_be84c.
Proof. vm_refl. Qed.
Lemma D_be84c : decode_any W_be84c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be850 : bv 32 := 0x00050593.
Lemma F_be850 : fetch_word Plain.M.loaded_segments (0xbe88c : word) = Some W_be850.
Proof. vm_refl. Qed.
Lemma D_be850 : decode_any W_be850 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be854 : bv 32 := 0x03f00513.
Lemma F_be854 : fetch_word Plain.M.loaded_segments (0xbe890 : word) = Some W_be854.
Proof. vm_refl. Qed.
Lemma D_be854 : decode_any W_be854 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_be858 : bv 32 := 0x00000713.
Lemma F_be858 : fetch_word Plain.M.loaded_segments (0xbe894 : word) = Some W_be858.
Proof. vm_refl. Qed.
Lemma D_be858 : decode_any W_be858 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be85c : bv 32 := 0x00000793.
Lemma F_be85c : fetch_word Plain.M.loaded_segments (0xbe898 : word) = Some W_be85c.
Proof. vm_refl. Qed.
Lemma D_be85c : decode_any W_be85c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be860 : bv 32 := 0x00000813.
Lemma F_be860 : fetch_word Plain.M.loaded_segments (0xbe89c : word) = Some W_be860.
Proof. vm_refl. Qed.
Lemma D_be860 : decode_any W_be860 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_be864 : bv 32 := 0x888fc0ef.
Lemma F_be864 : fetch_word Plain.M.loaded_segments (0xbe8a0 : word) = Some W_be864.
Proof. vm_refl. Qed.
Lemma D_be864 : decode_any W_be864 = Some (Jal 1 2080904, 4%Z).
Proof. vm_refl. Qed.

Definition W_be868 : bv 32 := 0x00813083.
Lemma F_be868 : fetch_word Plain.M.loaded_segments (0xbe8a4 : word) = Some W_be868.
Proof. vm_refl. Qed.
Lemma D_be868 : decode_any W_be868 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_be86c : bv 32 := 0x01010113.
Lemma F_be86c : fetch_word Plain.M.loaded_segments (0xbe8a8 : word) = Some W_be86c.
Proof. vm_refl. Qed.
Lemma D_be86c : decode_any W_be86c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_be870 : bv 32 := 0xbe5ea06f.
Lemma F_be870 : fetch_word Plain.M.loaded_segments (0xbe8ac : word) = Some W_be870.
Proof. vm_refl. Qed.
Lemma D_be870 : decode_any W_be870 = Some (Jal 0 2010084, 4%Z).
Proof. vm_refl. Qed.

Definition W_be8b8 : bv 32 := 0x00008067.
Lemma F_be8b8 : fetch_word Plain.M.loaded_segments (0xbe8f4 : word) = Some W_be8b8.
Proof. vm_refl. Qed.
Lemma D_be8b8 : decode_any W_be8b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r59000_59c90.
Module Ns0_code_r368b0_368b4.
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

Definition W_463d0 : bv 32 := 0x00008067.
Lemma F_463d0 : fetch_word Plain.M.loaded_segments (0x46418 : word) = Some W_463d0.
Proof. vm_refl. Qed.
Lemma D_463d0 : decode_any W_463d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r368b0_368b4.
Module Ns0_code_r395b0_395b4.
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

Definition W_39c2c : bv 32 := 0x00008067.
Lemma F_39c2c : fetch_word Plain.M.loaded_segments (0x39c74 : word) = Some W_39c2c.
Proof. vm_refl. Qed.
Lemma D_39c2c : decode_any W_39c2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r395b0_395b4.
Module Ns0_code_r3c390_3c394.
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

Definition W_3ca0c : bv 32 := 0x00008067.
Lemma F_3ca0c : fetch_word Plain.M.loaded_segments (0x3ca54 : word) = Some W_3ca0c.
Proof. vm_refl. Qed.
Lemma D_3ca0c : decode_any W_3ca0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3c390_3c394.
Module Ns0_code_r3b26c_3b270.
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

Definition W_3b8e8 : bv 32 := 0x00008067.
Lemma F_3b8e8 : fetch_word Plain.M.loaded_segments (0x3b930 : word) = Some W_3b8e8.
Proof. vm_refl. Qed.
Lemma D_3b8e8 : decode_any W_3b8e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3b26c_3b270.
Module Ns0_code_r3c564_3c568.
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

Definition W_3cbe0 : bv 32 := 0xfce7eae3.
Lemma F_3cbe0 : fetch_word Plain.M.loaded_segments (0x3cc28 : word) = Some W_3cbe0.
Proof. vm_refl. Qed.
Lemma D_3cbe0 : decode_any W_3cbe0 = Some (Branch BC_LTU 15 14 8148, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3c564_3c568.
Module Ns0_code_r3c5ac_3c5b0.
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

Definition W_3cc28 : bv 32 := 0x00008067.
Lemma F_3cc28 : fetch_word Plain.M.loaded_segments (0x3cc70 : word) = Some W_3cc28.
Proof. vm_refl. Qed.
Lemma D_3cc28 : decode_any W_3cc28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3c5ac_3c5b0.
Module Ns0_code_r3a6d8_3a6dc.
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

Definition W_3ad54 : bv 32 := 0x00008067.
Lemma F_3ad54 : fetch_word Plain.M.loaded_segments (0x3ad9c : word) = Some W_3ad54.
Proof. vm_refl. Qed.
Lemma D_3ad54 : decode_any W_3ad54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3a6d8_3a6dc.
Module Ns0_code_r3e6a8_3e6ac.
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

Definition W_3ed24 : bv 32 := 0x00054583.
Lemma F_3ed24 : fetch_word Plain.M.loaded_segments (0x3ed6c : word) = Some W_3ed24.
Proof. vm_refl. Qed.
Lemma D_3ed24 : decode_any W_3ed24 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3e6a8_3e6ac.
Module Ns0_code_r3e74c_3e750.
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

Definition W_3edc8 : bv 32 := 0x00054583.
Lemma F_3edc8 : fetch_word Plain.M.loaded_segments (0x3ee10 : word) = Some W_3edc8.
Proof. vm_refl. Qed.
Lemma D_3edc8 : decode_any W_3edc8 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3e74c_3e750.
Module Ns0_code_r3e7c4_3e7c8.
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

Definition W_3ee40 : bv 32 := 0x00008067.
Lemma F_3ee40 : fetch_word Plain.M.loaded_segments (0x3ee88 : word) = Some W_3ee40.
Proof. vm_refl. Qed.
Lemma D_3ee40 : decode_any W_3ee40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3e7c4_3e7c8.
Module Ns0_code_r39d14_39d18.
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

Definition W_3a390 : bv 32 := 0x02813027.
Lemma F_3a390 : fetch_word Plain.M.loaded_segments (0x3a3d8 : word) = Some W_3a390.
Proof. vm_refl. Qed.
Lemma D_3a390 : decode_any W_3a390 = Some (FStore FMT_D 2 8 32, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r39d14_39d18.
Module Ns0_code_r39d30_39d34.
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

Definition W_3a3ac : bv 32 := 0x22a50453.
Lemma F_3a3ac : fetch_word Plain.M.loaded_segments (0x3a3f4 : word) = Some W_3a3ac.
Proof. vm_refl. Qed.
Lemma D_3a3ac : decode_any W_3a3ac = Some (Fsgnj F_SGNJ FMT_D 8 10 10, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r39d30_39d34.
Module Ns0_code_r39d9c_39da0.
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

Definition W_3a418 : bv 32 := 0x22840553.
Lemma F_3a418 : fetch_word Plain.M.loaded_segments (0x3a460 : word) = Some W_3a418.
Proof. vm_refl. Qed.
Lemma D_3a418 : decode_any W_3a418 = Some (Fsgnj F_SGNJ FMT_D 10 8 8, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r39d9c_39da0.
Module Ns0_code_r39e08_39e0c.
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

Definition W_3a484 : bv 32 := 0x22840553.
Lemma F_3a484 : fetch_word Plain.M.loaded_segments (0x3a4cc : word) = Some W_3a484.
Proof. vm_refl. Qed.
Lemma D_3a484 : decode_any W_3a484 = Some (Fsgnj F_SGNJ FMT_D 10 8 8, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r39e08_39e0c.
Module Ns0_code_r39f88_39f8c.
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

Definition W_3a604 : bv 32 := 0x02013407.
Lemma F_3a604 : fetch_word Plain.M.loaded_segments (0x3a64c : word) = Some W_3a604.
Proof. vm_refl. Qed.
Lemma D_3a604 : decode_any W_3a604 = Some (FLoad FMT_D 8 2 32, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r39f88_39f8c.
Module Ns0_code_r39f90_39f94.
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

Definition W_3a60c : bv 32 := 0x00008067.
Lemma F_3a60c : fetch_word Plain.M.loaded_segments (0x3a654 : word) = Some W_3a60c.
Proof. vm_refl. Qed.
Lemma D_3a60c : decode_any W_3a60c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r39f90_39f94.
Module Ns0_code_r39610_3961c.
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

Definition W_39c8c : bv 32 := 0x40b505b3.
Lemma F_39c8c : fetch_word Plain.M.loaded_segments (0x39cd4 : word) = Some W_39c8c.
Proof. vm_refl. Qed.
Lemma D_39c8c : decode_any W_39c8c = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_39c90 : bv 32 := 0x4035d593.
Lemma F_39c90 : fetch_word Plain.M.loaded_segments (0x39cd8 : word) = Some W_39c90.
Proof. vm_refl. Qed.
Lemma D_39c90 : decode_any W_39c90 = Some (ShiftImm ALU_SRA 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_39c94 : bv 32 := 0x02c585b3.
Lemma F_39c94 : fetch_word Plain.M.loaded_segments (0x39cdc : word) = Some W_39c94.
Proof. vm_refl. Qed.
Lemma D_39c94 : decode_any W_39c94 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r39610_3961c.
Module Ns0_code_r39654_39660.
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

Definition W_39cd0 : bv 32 := 0x40b505b3.
Lemma F_39cd0 : fetch_word Plain.M.loaded_segments (0x39d18 : word) = Some W_39cd0.
Proof. vm_refl. Qed.
Lemma D_39cd0 : decode_any W_39cd0 = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_39cd4 : bv 32 := 0x4035d593.
Lemma F_39cd4 : fetch_word Plain.M.loaded_segments (0x39d1c : word) = Some W_39cd4.
Proof. vm_refl. Qed.
Lemma D_39cd4 : decode_any W_39cd4 = Some (ShiftImm ALU_SRA 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_39cd8 : bv 32 := 0x02c585b3.
Lemma F_39cd8 : fetch_word Plain.M.loaded_segments (0x39d20 : word) = Some W_39cd8.
Proof. vm_refl. Qed.
Lemma D_39cd8 : decode_any W_39cd8 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r39654_39660.
Module Ns0_code_r3976c_39770.
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

Definition W_39de8 : bv 32 := 0x00008067.
Lemma F_39de8 : fetch_word Plain.M.loaded_segments (0x39e30 : word) = Some W_39de8.
Proof. vm_refl. Qed.
Lemma D_39de8 : decode_any W_39de8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3976c_39770.
Module Ns0_code_r3a738_3a744.
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

Definition W_3adb4 : bv 32 := 0x40b505b3.
Lemma F_3adb4 : fetch_word Plain.M.loaded_segments (0x3adfc : word) = Some W_3adb4.
Proof. vm_refl. Qed.
Lemma D_3adb4 : decode_any W_3adb4 = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adb8 : bv 32 := 0x4035d593.
Lemma F_3adb8 : fetch_word Plain.M.loaded_segments (0x3ae00 : word) = Some W_3adb8.
Proof. vm_refl. Qed.
Lemma D_3adb8 : decode_any W_3adb8 = Some (ShiftImm ALU_SRA 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adbc : bv 32 := 0x02c585b3.
Lemma F_3adbc : fetch_word Plain.M.loaded_segments (0x3ae04 : word) = Some W_3adbc.
Proof. vm_refl. Qed.
Lemma D_3adbc : decode_any W_3adbc = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3a738_3a744.
Module Ns0_code_r3a77c_3a788.
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

Definition W_3adf8 : bv 32 := 0x40b505b3.
Lemma F_3adf8 : fetch_word Plain.M.loaded_segments (0x3ae40 : word) = Some W_3adf8.
Proof. vm_refl. Qed.
Lemma D_3adf8 : decode_any W_3adf8 = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3adfc : bv 32 := 0x4035d593.
Lemma F_3adfc : fetch_word Plain.M.loaded_segments (0x3ae44 : word) = Some W_3adfc.
Proof. vm_refl. Qed.
Lemma D_3adfc : decode_any W_3adfc = Some (ShiftImm ALU_SRA 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ae00 : bv 32 := 0x02c585b3.
Lemma F_3ae00 : fetch_word Plain.M.loaded_segments (0x3ae48 : word) = Some W_3ae00.
Proof. vm_refl. Qed.
Lemma D_3ae00 : decode_any W_3ae00 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3a77c_3a788.
Module Ns0_code_r3a894_3a898.
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

Definition W_3af10 : bv 32 := 0x00008067.
Lemma F_3af10 : fetch_word Plain.M.loaded_segments (0x3af58 : word) = Some W_3af10.
Proof. vm_refl. Qed.
Lemma D_3af10 : decode_any W_3af10 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3a894_3a898.
Module Ns0_code_r39cf8_39cfc.
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

Definition W_3a374 : bv 32 := 0x00008067.
Lemma F_3a374 : fetch_word Plain.M.loaded_segments (0x3a3bc : word) = Some W_3a374.
Proof. vm_refl. Qed.
Lemma D_3a374 : decode_any W_3a374 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r39cf8_39cfc.
Module Ns0_code_r3cacc_3cad0.
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

Definition W_3d148 : bv 32 := 0xfce86ae3.
Lemma F_3d148 : fetch_word Plain.M.loaded_segments (0x3d190 : word) = Some W_3d148.
Proof. vm_refl. Qed.
Lemma D_3d148 : decode_any W_3d148 = Some (Branch BC_LTU 16 14 8148, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3cacc_3cad0.
Module Ns0_code_r3cafc_3cb10.
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

Definition W_3d178 : bv 32 := 0x02c898b3.
Lemma F_3d178 : fetch_word Plain.M.loaded_segments (0x3d1c0 : word) = Some W_3d178.
Proof. vm_refl. Qed.
Lemma D_3d178 : decode_any W_3d178 = Some (Mul M_MULH 17 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d17c : bv 32 := 0x00148493.
Lemma F_3d17c : fetch_word Plain.M.loaded_segments (0x3d1c4 : word) = Some W_3d17c.
Proof. vm_refl. Qed.
Lemma D_3d17c : decode_any W_3d17c = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d180 : bv 32 := 0x03f8d393.
Lemma F_3d180 : fetch_word Plain.M.loaded_segments (0x3d1c8 : word) = Some W_3d180.
Proof. vm_refl. Qed.
Lemma D_3d180 : decode_any W_3d180 = Some (ShiftImm ALU_SRL 7 17 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d184 : bv 32 := 0x4028d893.
Lemma F_3d184 : fetch_word Plain.M.loaded_segments (0x3d1cc : word) = Some W_3d184.
Proof. vm_refl. Qed.
Lemma D_3d184 : decode_any W_3d184 = Some (ShiftImm ALU_SRA 17 17 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d188 : bv 32 := 0x007888b3.
Lemma F_3d188 : fetch_word Plain.M.loaded_segments (0x3d1d0 : word) = Some W_3d188.
Proof. vm_refl. Qed.
Lemma D_3d188 : decode_any W_3d188 = Some (Op ALU_ADD 17 17 7, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3cafc_3cb10.
Module Ns0_code_r3cb8c_3cb90.
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

Definition W_3d208 : bv 32 := 0x00008067.
Lemma F_3d208 : fetch_word Plain.M.loaded_segments (0x3d250 : word) = Some W_3d208.
Proof. vm_refl. Qed.
Lemma D_3d208 : decode_any W_3d208 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3cb8c_3cb90.
Module Ns0_code_r3afcc_3afd0.
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

Definition W_3b648 : bv 32 := 0x00008067.
Lemma F_3b648 : fetch_word Plain.M.loaded_segments (0x3b690 : word) = Some W_3b648.
Proof. vm_refl. Qed.
Lemma D_3b648 : decode_any W_3b648 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3afcc_3afd0.
Module Ns0_code_r39a94_39a98.
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

Definition W_3a110 : bv 32 := 0x00008067.
Lemma F_3a110 : fetch_word Plain.M.loaded_segments (0x3a158 : word) = Some W_3a110.
Proof. vm_refl. Qed.
Lemma D_3a110 : decode_any W_3a110 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r39a94_39a98.
Module Ns0_code_r3b418_3b41c.
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

Definition W_3ba94 : bv 32 := 0x00008067.
Lemma F_3ba94 : fetch_word Plain.M.loaded_segments (0x3badc : word) = Some W_3ba94.
Proof. vm_refl. Qed.
Lemma D_3ba94 : decode_any W_3ba94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3b418_3b41c.
Module Ns0_code_r3d0dc_3d0e0.
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

Definition W_3d758 : bv 32 := 0x00008067.
Lemma F_3d758 : fetch_word Plain.M.loaded_segments (0x3d7a0 : word) = Some W_3d758.
Proof. vm_refl. Qed.
Lemma D_3d758 : decode_any W_3d758 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3d0dc_3d0e0.
Module Ns0_code_r3df64_3dfa8.
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

Definition W_3e5e0 : bv 32 := 0x01813903.
Lemma F_3e5e0 : fetch_word Plain.M.loaded_segments (0x3e628 : word) = Some W_3e5e0.
Proof. vm_refl. Qed.
Lemma D_3e5e0 : decode_any W_3e5e0 = Some (Load SZ8 true 18 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e5e4 : bv 32 := 0x00a43027.
Lemma F_3e5e4 : fetch_word Plain.M.loaded_segments (0x3e62c : word) = Some W_3e5e4.
Proof. vm_refl. Qed.
Lemma D_3e5e4 : decode_any W_3e5e4 = Some (FStore FMT_D 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e5e8 : bv 32 := 0x03496e63.
Lemma F_3e5e8 : fetch_word Plain.M.loaded_segments (0x3e630 : word) = Some W_3e5e8.
Proof. vm_refl. Qed.
Lemma D_3e5e8 : decode_any W_3e5e8 = Some (Branch BC_LTU 18 20 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e5ec : bv 32 := 0xe2051553.
Lemma F_3e5ec : fetch_word Plain.M.loaded_segments (0x3e634 : word) = Some W_3e5ec.
Proof. vm_refl. Qed.
Lemma D_3e5ec : decode_any W_3e5ec = Some (Fclass FMT_D 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e5f0 : bv 32 := 0x08157513.
Lemma F_3e5f0 : fetch_word Plain.M.loaded_segments (0x3e638 : word) = Some W_3e5f0.
Proof. vm_refl. Qed.
Lemma D_3e5f0 : decode_any W_3e5f0 = Some (OpImm ALU_AND 10 10 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e5f4 : bv 32 := 0x00153513.
Lemma F_3e5f4 : fetch_word Plain.M.loaded_segments (0x3e63c : word) = Some W_3e5f4.
Proof. vm_refl. Qed.
Lemma D_3e5f4 : decode_any W_3e5f4 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e5f8 : bv 32 := 0xfff50513.
Lemma F_3e5f8 : fetch_word Plain.M.loaded_segments (0x3e640 : word) = Some W_3e5f8.
Proof. vm_refl. Qed.
Lemma D_3e5f8 : decode_any W_3e5f8 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e5fc : bv 32 := 0x02257593.
Lemma F_3e5fc : fetch_word Plain.M.loaded_segments (0x3e644 : word) = Some W_3e5fc.
Proof. vm_refl. Qed.
Lemma D_3e5fc : decode_any W_3e5fc = Some (OpImm ALU_AND 11 10 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e600 : bv 32 := 0x00090513.
Lemma F_3e600 : fetch_word Plain.M.loaded_segments (0x3e648 : word) = Some W_3e600.
Proof. vm_refl. Qed.
Lemma D_3e600 : decode_any W_3e600 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e604 : bv 32 := 0x04813083.
Lemma F_3e604 : fetch_word Plain.M.loaded_segments (0x3e64c : word) = Some W_3e604.
Proof. vm_refl. Qed.
Lemma D_3e604 : decode_any W_3e604 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e608 : bv 32 := 0x04013403.
Lemma F_3e608 : fetch_word Plain.M.loaded_segments (0x3e650 : word) = Some W_3e608.
Proof. vm_refl. Qed.
Lemma D_3e608 : decode_any W_3e608 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e60c : bv 32 := 0x03813483.
Lemma F_3e60c : fetch_word Plain.M.loaded_segments (0x3e654 : word) = Some W_3e60c.
Proof. vm_refl. Qed.
Lemma D_3e60c : decode_any W_3e60c = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e610 : bv 32 := 0x03013903.
Lemma F_3e610 : fetch_word Plain.M.loaded_segments (0x3e658 : word) = Some W_3e610.
Proof. vm_refl. Qed.
Lemma D_3e610 : decode_any W_3e610 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e614 : bv 32 := 0x02813983.
Lemma F_3e614 : fetch_word Plain.M.loaded_segments (0x3e65c : word) = Some W_3e614.
Proof. vm_refl. Qed.
Lemma D_3e614 : decode_any W_3e614 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e618 : bv 32 := 0x02013a03.
Lemma F_3e618 : fetch_word Plain.M.loaded_segments (0x3e660 : word) = Some W_3e618.
Proof. vm_refl. Qed.
Lemma D_3e618 : decode_any W_3e618 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e61c : bv 32 := 0x05010113.
Lemma F_3e61c : fetch_word Plain.M.loaded_segments (0x3e664 : word) = Some W_3e61c.
Proof. vm_refl. Qed.
Lemma D_3e61c : decode_any W_3e61c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e620 : bv 32 := 0x00008067.
Lemma F_3e620 : fetch_word Plain.M.loaded_segments (0x3e668 : word) = Some W_3e620.
Proof. vm_refl. Qed.
Lemma D_3e620 : decode_any W_3e620 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3df64_3dfa8.
Module Ns0_code_r3d788_3d78c.
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

Definition W_3de04 : bv 32 := 0x00008067.
Lemma F_3de04 : fetch_word Plain.M.loaded_segments (0x3de4c : word) = Some W_3de04.
Proof. vm_refl. Qed.
Lemma D_3de04 : decode_any W_3de04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3d788_3d78c.
Module Ns0_code_r394a8_394ac.
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

Definition W_46990 : bv 32 := 0x0005cc03.
Lemma F_46990 : fetch_word Plain.M.loaded_segments (0x469d8 : word) = Some W_46990.
Proof. vm_refl. Qed.
Lemma D_46990 : decode_any W_46990 = Some (Load SZ1 false 24 11 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r394a8_394ac.
Module Ns0_code_r395a4_395a8.
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

Definition W_46a8c : bv 32 := 0x00008067.
Lemma F_46a8c : fetch_word Plain.M.loaded_segments (0x46ad4 : word) = Some W_46a8c.
Proof. vm_refl. Qed.
Lemma D_46a8c : decode_any W_46a8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r395a4_395a8.
Module Ns0_code_r363e8_363ec.
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

Definition W_41a60 : bv 32 := 0x00008067.
Lemma F_41a60 : fetch_word Plain.M.loaded_segments (0x41aa8 : word) = Some W_41a60.
Proof. vm_refl. Qed.
Lemma D_41a60 : decode_any W_41a60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r363e8_363ec.
Module Ns0_code_r342cc_342d0.
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

Definition W_3943c : bv 32 := 0x00008067.
Lemma F_3943c : fetch_word Plain.M.loaded_segments (0x39484 : word) = Some W_3943c.
Proof. vm_refl. Qed.
Lemma D_3943c : decode_any W_3943c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r342cc_342d0.
Module Ns0_code_r7f81c_7f820.
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

Definition W_900d0 : bv 32 := 0x00008067.
Lemma F_900d0 : fetch_word Plain.M.loaded_segments (0x90118 : word) = Some W_900d0.
Proof. vm_refl. Qed.
Lemma D_900d0 : decode_any W_900d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r7f81c_7f820.
Module Ns0_code_r7f8b8_7f8bc.
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

Definition W_9016c : bv 32 := 0x00008067.
Lemma F_9016c : fetch_word Plain.M.loaded_segments (0x901b4 : word) = Some W_9016c.
Proof. vm_refl. Qed.
Lemma D_9016c : decode_any W_9016c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r7f8b8_7f8bc.
Module Ns0_code_r3f884_3f888.
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

Definition W_450ec : bv 32 := 0x00008067.
Lemma F_450ec : fetch_word Plain.M.loaded_segments (0x45134 : word) = Some W_450ec.
Proof. vm_refl. Qed.
Lemma D_450ec : decode_any W_450ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3f884_3f888.
Module Ns0_code_r3f734_3f738.
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

Definition W_44f9c : bv 32 := 0x00008067.
Lemma F_44f9c : fetch_word Plain.M.loaded_segments (0x44fe4 : word) = Some W_44f9c.
Proof. vm_refl. Qed.
Lemma D_44f9c : decode_any W_44f9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3f734_3f738.
Module Ns0_code_r38420_38424.
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

Definition W_394c8 : bv 32 := 0x00008067.
Lemma F_394c8 : fetch_word Plain.M.loaded_segments (0x39510 : word) = Some W_394c8.
Proof. vm_refl. Qed.
Lemma D_394c8 : decode_any W_394c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r38420_38424.
Module Ns0_code_r42d88_42d8c.
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

Definition W_429d0 : bv 32 := 0x00008067.
Lemma F_429d0 : fetch_word Plain.M.loaded_segments (0x42a18 : word) = Some W_429d0.
Proof. vm_refl. Qed.
Lemma D_429d0 : decode_any W_429d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r42d88_42d8c.
Module Ns0_code_r5b260_5b264.
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

Definition W_6bb14 : bv 32 := 0x00008067.
Lemma F_6bb14 : fetch_word Plain.M.loaded_segments (0x6bb5c : word) = Some W_6bb14.
Proof. vm_refl. Qed.
Lemma D_6bb14 : decode_any W_6bb14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r5b260_5b264.
Module Ns0_code_r59e7c_59e80.
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

Definition W_6a704 : bv 32 := 0x00008067.
Lemma F_6a704 : fetch_word Plain.M.loaded_segments (0x6a74c : word) = Some W_6a704.
Proof. vm_refl. Qed.
Lemma D_6a704 : decode_any W_6a704 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r59e7c_59e80.
Module Ns0_code_r414d4_414d8.
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

Definition W_44544 : bv 32 := 0x00008067.
Lemma F_44544 : fetch_word Plain.M.loaded_segments (0x4458c : word) = Some W_44544.
Proof. vm_refl. Qed.
Lemma D_44544 : decode_any W_44544 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r414d4_414d8.
Module Ns0_code_r41608_4160c.
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

Definition W_432f0 : bv 32 := 0x00008067.
Lemma F_432f0 : fetch_word Plain.M.loaded_segments (0x43338 : word) = Some W_432f0.
Proof. vm_refl. Qed.
Lemma D_432f0 : decode_any W_432f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r41608_4160c.
Module Ns0_code_r41bc0_41bc4.
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

Definition W_43a64 : bv 32 := 0x00008067.
Lemma F_43a64 : fetch_word Plain.M.loaded_segments (0x43aac : word) = Some W_43a64.
Proof. vm_refl. Qed.
Lemma D_43a64 : decode_any W_43a64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r41bc0_41bc4.
Module Ns0_code_r41da0_41da4.
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

Definition W_47074 : bv 32 := 0x00008067.
Lemma F_47074 : fetch_word Plain.M.loaded_segments (0x470bc : word) = Some W_47074.
Proof. vm_refl. Qed.
Lemma D_47074 : decode_any W_47074 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r41da0_41da4.
Module Ns0_code_r418a8_418ac.
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

Definition W_46e40 : bv 32 := 0x00008067.
Lemma F_46e40 : fetch_word Plain.M.loaded_segments (0x46e88 : word) = Some W_46e40.
Proof. vm_refl. Qed.
Lemma D_46e40 : decode_any W_46e40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r418a8_418ac.
Module Ns0_code_r42200_42204.
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

Definition W_47454 : bv 32 := 0x00008067.
Lemma F_47454 : fetch_word Plain.M.loaded_segments (0x4749c : word) = Some W_47454.
Proof. vm_refl. Qed.
Lemma D_47454 : decode_any W_47454 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r42200_42204.
Module Ns0_code_r420c0_420c4.
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

Definition W_47314 : bv 32 := 0x00008067.
Lemma F_47314 : fetch_word Plain.M.loaded_segments (0x4735c : word) = Some W_47314.
Proof. vm_refl. Qed.
Lemma D_47314 : decode_any W_47314 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r420c0_420c4.
Module Ns0_code_r41030_41034.
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

Definition W_46874 : bv 32 := 0x00008067.
Lemma F_46874 : fetch_word Plain.M.loaded_segments (0x468bc : word) = Some W_46874.
Proof. vm_refl. Qed.
Lemma D_46874 : decode_any W_46874 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r41030_41034.
Module Ns0_code_r42098_4209c.
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

Definition W_472ec : bv 32 := 0x00008067.
Lemma F_472ec : fetch_word Plain.M.loaded_segments (0x47334 : word) = Some W_472ec.
Proof. vm_refl. Qed.
Lemma D_472ec : decode_any W_472ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r42098_4209c.
Module Ns0_code_r36afc_36b00.
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

Definition W_46990 : bv 32 := 0x0005cc03.
Lemma F_46990 : fetch_word Plain.M.loaded_segments (0x469d8 : word) = Some W_46990.
Proof. vm_refl. Qed.
Lemma D_46990 : decode_any W_46990 = Some (Load SZ1 false 24 11 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r36afc_36b00.
Module Ns0_code_r36bf8_36bfc.
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

Definition W_46a8c : bv 32 := 0x00008067.
Lemma F_46a8c : fetch_word Plain.M.loaded_segments (0x46ad4 : word) = Some W_46a8c.
Proof. vm_refl. Qed.
Lemma D_46a8c : decode_any W_46a8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r36bf8_36bfc.
Module Ns0_code_r1ff24_20000.
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

Definition W_38a98 : bv 32 := 0xfffd8197.
Lemma F_38a98 : fetch_word Plain.M.loaded_segments (0x38ae0 : word) = Some W_38a98.
Proof. vm_refl. Qed.
Lemma D_38a98 : decode_any W_38a98 = Some (Auipc 3 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a9c : bv 32 := 0xd2018193.
Lemma F_38a9c : fetch_word Plain.M.loaded_segments (0x38ae4 : word) = Some W_38a9c.
Proof. vm_refl. Qed.
Lemma D_38a9c : decode_any W_38a9c = Some (OpImm ALU_ADD 3 3 3360, 4%Z).
Proof. vm_refl. Qed.

Definition W_38aa0 : bv 32 := 0x00010513.
Lemma F_38aa0 : fetch_word Plain.M.loaded_segments (0x38ae8 : word) = Some W_38aa0.
Proof. vm_refl. Qed.
Lemma D_38aa0 : decode_any W_38aa0 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38aa4 : bv 32 := 0xfffc7597.
Lemma F_38aa4 : fetch_word Plain.M.loaded_segments (0x38aec : word) = Some W_38aa4.
Proof. vm_refl. Qed.
Lemma D_38aa4 : decode_any W_38aa4 = Some (Auipc 11 1048519, 4%Z).
Proof. vm_refl. Qed.

Definition W_38aa8 : bv 32 := 0x51458593.
Lemma F_38aa8 : fetch_word Plain.M.loaded_segments (0x38af0 : word) = Some W_38aa8.
Proof. vm_refl. Qed.
Lemma D_38aa8 : decode_any W_38aa8 = Some (OpImm ALU_ADD 11 11 1300, 4%Z).
Proof. vm_refl. Qed.

Definition W_38aac : bv 32 := 0xff017113.
Lemma F_38aac : fetch_word Plain.M.loaded_segments (0x38af4 : word) = Some W_38aac.
Proof. vm_refl. Qed.
Lemma D_38aac : decode_any W_38aac = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ab0 : bv 32 := 0x0040006f.
Lemma F_38ab0 : fetch_word Plain.M.loaded_segments (0x38af8 : word) = Some W_38ab0.
Proof. vm_refl. Qed.
Lemma D_38ab0 : decode_any W_38ab0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ab4 : bv 32 := 0x00052583.
Lemma F_38ab4 : fetch_word Plain.M.loaded_segments (0x38afc : word) = Some W_38ab4.
Proof. vm_refl. Qed.
Lemma D_38ab4 : decode_any W_38ab4 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ab8 : bv 32 := 0x0008d617.
Lemma F_38ab8 : fetch_word Plain.M.loaded_segments (0x38b00 : word) = Some W_38ab8.
Proof. vm_refl. Qed.
Lemma D_38ab8 : decode_any W_38ab8 = Some (Auipc 12 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_38abc : bv 32 := 0x0008d697.
Lemma F_38abc : fetch_word Plain.M.loaded_segments (0x38b04 : word) = Some W_38abc.
Proof. vm_refl. Qed.
Lemma D_38abc : decode_any W_38abc = Some (Auipc 13 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ac0 : bv 32 := 0x0008d717.
Lemma F_38ac0 : fetch_word Plain.M.loaded_segments (0x38b08 : word) = Some W_38ac0.
Proof. vm_refl. Qed.
Lemma D_38ac0 : decode_any W_38ac0 = Some (Auipc 14 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ac4 : bv 32 := 0xe3063783.
Lemma F_38ac4 : fetch_word Plain.M.loaded_segments (0x38b0c : word) = Some W_38ac4.
Proof. vm_refl. Qed.
Lemma D_38ac4 : decode_any W_38ac4 = Some (Load SZ8 true 15 12 3632, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ac8 : bv 32 := 0xe346b683.
Lemma F_38ac8 : fetch_word Plain.M.loaded_segments (0x38b10 : word) = Some W_38ac8.
Proof. vm_refl. Qed.
Lemma D_38ac8 : decode_any W_38ac8 = Some (Load SZ8 true 13 13 3636, 4%Z).
Proof. vm_refl. Qed.

Definition W_38acc : bv 32 := 0xe3873703.
Lemma F_38acc : fetch_word Plain.M.loaded_segments (0x38b14 : word) = Some W_38acc.
Proof. vm_refl. Qed.
Lemma D_38acc : decode_any W_38acc = Some (Load SZ8 true 14 14 3640, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ad0 : bv 32 := 0x00850613.
Lemma F_38ad0 : fetch_word Plain.M.loaded_segments (0x38b18 : word) = Some W_38ad0.
Proof. vm_refl. Qed.
Lemma D_38ad0 : decode_any W_38ad0 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ad4 : bv 32 := 0x00078513.
Lemma F_38ad4 : fetch_word Plain.M.loaded_segments (0x38b1c : word) = Some W_38ad4.
Proof. vm_refl. Qed.
Lemma D_38ad4 : decode_any W_38ad4 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ad8 : bv 32 := 0x00000793.
Lemma F_38ad8 : fetch_word Plain.M.loaded_segments (0x38b20 : word) = Some W_38ad8.
Proof. vm_refl. Qed.
Lemma D_38ad8 : decode_any W_38ad8 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38adc : bv 32 := 0x0bc7006f.
Lemma F_38adc : fetch_word Plain.M.loaded_segments (0x38b24 : word) = Some W_38adc.
Proof. vm_refl. Qed.
Lemma D_38adc : decode_any W_38adc = Some (Jal 0 458940, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ae0 : bv 32 := 0xff010113.
Lemma F_38ae0 : fetch_word Plain.M.loaded_segments (0x38b28 : word) = Some W_38ae0.
Proof. vm_refl. Qed.
Lemma D_38ae0 : decode_any W_38ae0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ae4 : bv 32 := 0x00113423.
Lemma F_38ae4 : fetch_word Plain.M.loaded_segments (0x38b2c : word) = Some W_38ae4.
Proof. vm_refl. Qed.
Lemma D_38ae4 : decode_any W_38ae4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ae8 : bv 32 := 0x00813023.
Lemma F_38ae8 : fetch_word Plain.M.loaded_segments (0x38b30 : word) = Some W_38ae8.
Proof. vm_refl. Qed.
Lemma D_38ae8 : decode_any W_38ae8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38aec : bv 32 := 0x01010413.
Lemma F_38aec : fetch_word Plain.M.loaded_segments (0x38b34 : word) = Some W_38aec.
Proof. vm_refl. Qed.
Lemma D_38aec : decode_any W_38aec = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38af0 : bv 32 := 0x0008e517.
Lemma F_38af0 : fetch_word Plain.M.loaded_segments (0x38b38 : word) = Some W_38af0.
Proof. vm_refl. Qed.
Lemma D_38af0 : decode_any W_38af0 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_38af4 : bv 32 := 0x29850513.
Lemma F_38af4 : fetch_word Plain.M.loaded_segments (0x38b3c : word) = Some W_38af4.
Proof. vm_refl. Qed.
Lemma D_38af4 : decode_any W_38af4 = Some (OpImm ALU_ADD 10 10 664, 4%Z).
Proof. vm_refl. Qed.

Definition W_38af8 : bv 32 := 0x00054503.
Lemma F_38af8 : fetch_word Plain.M.loaded_segments (0x38b40 : word) = Some W_38af8.
Proof. vm_refl. Qed.
Lemma D_38af8 : decode_any W_38af8 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38afc : bv 32 := 0x00157513.
Lemma F_38afc : fetch_word Plain.M.loaded_segments (0x38b44 : word) = Some W_38afc.
Proof. vm_refl. Qed.
Lemma D_38afc : decode_any W_38afc = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b00 : bv 32 := 0x00050663.
Lemma F_38b00 : fetch_word Plain.M.loaded_segments (0x38b48 : word) = Some W_38b00.
Proof. vm_refl. Qed.
Lemma D_38b00 : decode_any W_38b00 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b0c : bv 32 := 0x0008e517.
Lemma F_38b0c : fetch_word Plain.M.loaded_segments (0x38b54 : word) = Some W_38b0c.
Proof. vm_refl. Qed.
Lemma D_38b0c : decode_any W_38b0c = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b10 : bv 32 := 0x27c50593.
Lemma F_38b10 : fetch_word Plain.M.loaded_segments (0x38b58 : word) = Some W_38b10.
Proof. vm_refl. Qed.
Lemma D_38b10 : decode_any W_38b10 = Some (OpImm ALU_ADD 11 10 636, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b14 : bv 32 := 0x00100513.
Lemma F_38b14 : fetch_word Plain.M.loaded_segments (0x38b5c : word) = Some W_38b14.
Proof. vm_refl. Qed.
Lemma D_38b14 : decode_any W_38b14 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b18 : bv 32 := 0x00a58023.
Lemma F_38b18 : fetch_word Plain.M.loaded_segments (0x38b60 : word) = Some W_38b18.
Proof. vm_refl. Qed.
Lemma D_38b18 : decode_any W_38b18 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b1c : bv 32 := 0x0008d517.
Lemma F_38b1c : fetch_word Plain.M.loaded_segments (0x38b64 : word) = Some W_38b1c.
Proof. vm_refl. Qed.
Lemma D_38b1c : decode_any W_38b1c = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b20 : bv 32 := 0xde453503.
Lemma F_38b20 : fetch_word Plain.M.loaded_segments (0x38b68 : word) = Some W_38b20.
Proof. vm_refl. Qed.
Lemma D_38b20 : decode_any W_38b20 = Some (Load SZ8 true 10 10 3556, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b24 : bv 32 := 0x02050063.
Lemma F_38b24 : fetch_word Plain.M.loaded_segments (0x38b6c : word) = Some W_38b24.
Proof. vm_refl. Qed.
Lemma D_38b24 : decode_any W_38b24 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b44 : bv 32 := 0x00813083.
Lemma F_38b44 : fetch_word Plain.M.loaded_segments (0x38b8c : word) = Some W_38b44.
Proof. vm_refl. Qed.
Lemma D_38b44 : decode_any W_38b44 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b48 : bv 32 := 0x00013403.
Lemma F_38b48 : fetch_word Plain.M.loaded_segments (0x38b90 : word) = Some W_38b48.
Proof. vm_refl. Qed.
Lemma D_38b48 : decode_any W_38b48 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b4c : bv 32 := 0x01010113.
Lemma F_38b4c : fetch_word Plain.M.loaded_segments (0x38b94 : word) = Some W_38b4c.
Proof. vm_refl. Qed.
Lemma D_38b4c : decode_any W_38b4c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b50 : bv 32 := 0x00008067.
Lemma F_38b50 : fetch_word Plain.M.loaded_segments (0x38b98 : word) = Some W_38b50.
Proof. vm_refl. Qed.
Lemma D_38b50 : decode_any W_38b50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b54 : bv 32 := 0xff010113.
Lemma F_38b54 : fetch_word Plain.M.loaded_segments (0x38b9c : word) = Some W_38b54.
Proof. vm_refl. Qed.
Lemma D_38b54 : decode_any W_38b54 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b58 : bv 32 := 0x00113423.
Lemma F_38b58 : fetch_word Plain.M.loaded_segments (0x38ba0 : word) = Some W_38b58.
Proof. vm_refl. Qed.
Lemma D_38b58 : decode_any W_38b58 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b5c : bv 32 := 0x00813023.
Lemma F_38b5c : fetch_word Plain.M.loaded_segments (0x38ba4 : word) = Some W_38b5c.
Proof. vm_refl. Qed.
Lemma D_38b5c : decode_any W_38b5c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b60 : bv 32 := 0x01010413.
Lemma F_38b60 : fetch_word Plain.M.loaded_segments (0x38ba8 : word) = Some W_38b60.
Proof. vm_refl. Qed.
Lemma D_38b60 : decode_any W_38b60 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b64 : bv 32 := 0x0008e517.
Lemma F_38b64 : fetch_word Plain.M.loaded_segments (0x38bac : word) = Some W_38b64.
Proof. vm_refl. Qed.
Lemma D_38b64 : decode_any W_38b64 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b68 : bv 32 := 0x26c50513.
Lemma F_38b68 : fetch_word Plain.M.loaded_segments (0x38bb0 : word) = Some W_38b68.
Proof. vm_refl. Qed.
Lemma D_38b68 : decode_any W_38b68 = Some (OpImm ALU_ADD 10 10 620, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b6c : bv 32 := 0x00054503.
Lemma F_38b6c : fetch_word Plain.M.loaded_segments (0x38bb4 : word) = Some W_38b6c.
Proof. vm_refl. Qed.
Lemma D_38b6c : decode_any W_38b6c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b70 : bv 32 := 0x00157513.
Lemma F_38b70 : fetch_word Plain.M.loaded_segments (0x38bb8 : word) = Some W_38b70.
Proof. vm_refl. Qed.
Lemma D_38b70 : decode_any W_38b70 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r1ff24_20000.
Module Ns0_code_r20000_21000.
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

Definition W_38b74 : bv 32 := 0x00050663.
Lemma F_38b74 : fetch_word Plain.M.loaded_segments (0x38bbc : word) = Some W_38b74.
Proof. vm_refl. Qed.
Lemma D_38b74 : decode_any W_38b74 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b80 : bv 32 := 0x0008e517.
Lemma F_38b80 : fetch_word Plain.M.loaded_segments (0x38bc8 : word) = Some W_38b80.
Proof. vm_refl. Qed.
Lemma D_38b80 : decode_any W_38b80 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b84 : bv 32 := 0x25050593.
Lemma F_38b84 : fetch_word Plain.M.loaded_segments (0x38bcc : word) = Some W_38b84.
Proof. vm_refl. Qed.
Lemma D_38b84 : decode_any W_38b84 = Some (OpImm ALU_ADD 11 10 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b88 : bv 32 := 0x00100513.
Lemma F_38b88 : fetch_word Plain.M.loaded_segments (0x38bd0 : word) = Some W_38b88.
Proof. vm_refl. Qed.
Lemma D_38b88 : decode_any W_38b88 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b8c : bv 32 := 0x00a58023.
Lemma F_38b8c : fetch_word Plain.M.loaded_segments (0x38bd4 : word) = Some W_38b8c.
Proof. vm_refl. Qed.
Lemma D_38b8c : decode_any W_38b8c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b90 : bv 32 := 0x0008d517.
Lemma F_38b90 : fetch_word Plain.M.loaded_segments (0x38bd8 : word) = Some W_38b90.
Proof. vm_refl. Qed.
Lemma D_38b90 : decode_any W_38b90 = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b94 : bv 32 := 0xd7853503.
Lemma F_38b94 : fetch_word Plain.M.loaded_segments (0x38bdc : word) = Some W_38b94.
Proof. vm_refl. Qed.
Lemma D_38b94 : decode_any W_38b94 = Some (Load SZ8 true 10 10 3448, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b98 : bv 32 := 0x00050e63.
Lemma F_38b98 : fetch_word Plain.M.loaded_segments (0x38be0 : word) = Some W_38b98.
Proof. vm_refl. Qed.
Lemma D_38b98 : decode_any W_38b98 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bb4 : bv 32 := 0x0008d517.
Lemma F_38bb4 : fetch_word Plain.M.loaded_segments (0x38bfc : word) = Some W_38bb4.
Proof. vm_refl. Qed.
Lemma D_38bb4 : decode_any W_38bb4 = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bb8 : bv 32 := 0xd5c53503.
Lemma F_38bb8 : fetch_word Plain.M.loaded_segments (0x38c00 : word) = Some W_38bb8.
Proof. vm_refl. Qed.
Lemma D_38bb8 : decode_any W_38bb8 = Some (Load SZ8 true 10 10 3420, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bbc : bv 32 := 0x00050c63.
Lemma F_38bbc : fetch_word Plain.M.loaded_segments (0x38c04 : word) = Some W_38bbc.
Proof. vm_refl. Qed.
Lemma D_38bbc : decode_any W_38bbc = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bd4 : bv 32 := 0x00813083.
Lemma F_38bd4 : fetch_word Plain.M.loaded_segments (0x38c1c : word) = Some W_38bd4.
Proof. vm_refl. Qed.
Lemma D_38bd4 : decode_any W_38bd4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bd8 : bv 32 := 0x00013403.
Lemma F_38bd8 : fetch_word Plain.M.loaded_segments (0x38c20 : word) = Some W_38bd8.
Proof. vm_refl. Qed.
Lemma D_38bd8 : decode_any W_38bd8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bdc : bv 32 := 0x01010113.
Lemma F_38bdc : fetch_word Plain.M.loaded_segments (0x38c24 : word) = Some W_38bdc.
Proof. vm_refl. Qed.
Lemma D_38bdc : decode_any W_38bdc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38be0 : bv 32 := 0x00008067.
Lemma F_38be0 : fetch_word Plain.M.loaded_segments (0x38c28 : word) = Some W_38be0.
Proof. vm_refl. Qed.
Lemma D_38be0 : decode_any W_38be0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38c38 : bv 32 := 0x24050a63.
Lemma F_38c38 : fetch_word Plain.M.loaded_segments (0x38c80 : word) = Some W_38c38.
Proof. vm_refl. Qed.
Lemma D_38c38 : decode_any W_38c38 = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_38c78 : bv 32 := 0x01a9d513.
Lemma F_38c78 : fetch_word Plain.M.loaded_segments (0x38cc0 : word) = Some W_38c78.
Proof. vm_refl. Qed.
Lemma D_38c78 : decode_any W_38c78 = Some (ShiftImm ALU_SRL 10 19 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_38c7c : bv 32 := 0x1a051863.
Lemma F_38c7c : fetch_word Plain.M.loaded_segments (0x38cc4 : word) = Some W_38c7c.
Proof. vm_refl. Qed.
Lemma D_38c7c : decode_any W_38c7c = Some (Branch BC_NE 10 0 432, 4%Z).
Proof. vm_refl. Qed.

Definition W_38c80 : bv 32 := 0x00199a93.
Lemma F_38c80 : fetch_word Plain.M.loaded_segments (0x38cc8 : word) = Some W_38c80.
Proof. vm_refl. Qed.
Lemma D_38c80 : decode_any W_38c80 = Some (ShiftImm ALU_SLL 21 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38c84 : bv 32 := 0x000a8513.
Lemma F_38c84 : fetch_word Plain.M.loaded_segments (0x38ccc : word) = Some W_38c84.
Proof. vm_refl. Qed.
Lemma D_38c84 : decode_any W_38c84 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38c88 : bv 32 := 0x5e4720ef.
Lemma F_38c88 : fetch_word Plain.M.loaded_segments (0x38cd0 : word) = Some W_38c88.
Proof. vm_refl. Qed.
Lemma D_38c88 : decode_any W_38c88 = Some (Jal 1 468452, 4%Z).
Proof. vm_refl. Qed.

Definition W_38c8c : bv 32 := 0x1c050063.
Lemma F_38c8c : fetch_word Plain.M.loaded_segments (0x38cd4 : word) = Some W_38c8c.
Proof. vm_refl. Qed.
Lemma D_38c8c : decode_any W_38c8c = Some (Branch BC_EQ 10 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_38c90 : bv 32 := 0x00050493.
Lemma F_38c90 : fetch_word Plain.M.loaded_segments (0x38cd8 : word) = Some W_38c90.
Proof. vm_refl. Qed.
Lemma D_38c90 : decode_any W_38c90 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38c94 : bv 32 := 0x00098a63.
Lemma F_38c94 : fetch_word Plain.M.loaded_segments (0x38cdc : word) = Some W_38c94.
Proof. vm_refl. Qed.
Lemma D_38c94 : decode_any W_38c94 = Some (Branch BC_EQ 19 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_38c98 : bv 32 := 0x00048513.
Lemma F_38c98 : fetch_word Plain.M.loaded_segments (0x38ce0 : word) = Some W_38c98.
Proof. vm_refl. Qed.
Lemma D_38c98 : decode_any W_38c98 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38c9c : bv 32 := 0x000b8593.
Lemma F_38c9c : fetch_word Plain.M.loaded_segments (0x38ce4 : word) = Some W_38c9c.
Proof. vm_refl. Qed.
Lemma D_38c9c : decode_any W_38c9c = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ca0 : bv 32 := 0x00098613.
Lemma F_38ca0 : fetch_word Plain.M.loaded_segments (0x38ce8 : word) = Some W_38ca0.
Proof. vm_refl. Qed.
Lemma D_38ca0 : decode_any W_38ca0 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ca4 : bv 32 := 0x48d800ef.
Lemma F_38ca4 : fetch_word Plain.M.loaded_segments (0x38cec : word) = Some W_38ca4.
Proof. vm_refl. Qed.
Lemma D_38ca4 : decode_any W_38ca4 = Some (Jal 1 527500, 4%Z).
Proof. vm_refl. Qed.

Definition W_38cd8 : bv 32 := 0x000a0513.
Lemma F_38cd8 : fetch_word Plain.M.loaded_segments (0x38d20 : word) = Some W_38cd8.
Proof. vm_refl. Qed.
Lemma D_38cd8 : decode_any W_38cd8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38cdc : bv 32 := 0x2f9850ef.
Lemma F_38cdc : fetch_word Plain.M.loaded_segments (0x38d24 : word) = Some W_38cdc.
Proof. vm_refl. Qed.
Lemma D_38cdc : decode_any W_38cdc = Some (Jal 1 547576, 4%Z).
Proof. vm_refl. Qed.

Definition W_38d58 : bv 32 := 0x000ac663.
Lemma F_38d58 : fetch_word Plain.M.loaded_segments (0x38da0 : word) = Some W_38d58.
Proof. vm_refl. Qed.
Lemma D_38d58 : decode_any W_38d58 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38d5c : bv 32 := 0x00050413.
Lemma F_38d5c : fetch_word Plain.M.loaded_segments (0x38da4 : word) = Some W_38d5c.
Proof. vm_refl. Qed.
Lemma D_38d5c : decode_any W_38d5c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38d60 : bv 32 := 0x0780006f.
Lemma F_38d60 : fetch_word Plain.M.loaded_segments (0x38da8 : word) = Some W_38d60.
Proof. vm_refl. Qed.
Lemma D_38d60 : decode_any W_38d60 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_38d64 : bv 32 := 0x148000ef.
Lemma F_38d64 : fetch_word Plain.M.loaded_segments (0x38dac : word) = Some W_38d64.
Proof. vm_refl. Qed.
Lemma D_38d64 : decode_any W_38d64 = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_38d68 : bv 32 := 0x0fb00593.
Lemma F_38d68 : fetch_word Plain.M.loaded_segments (0x38db0 : word) = Some W_38d68.
Proof. vm_refl. Qed.
Lemma D_38d68 : decode_any W_38d68 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_38d6c : bv 32 := 0x00050413.
Lemma F_38d6c : fetch_word Plain.M.loaded_segments (0x38db4 : word) = Some W_38d6c.
Proof. vm_refl. Qed.
Lemma D_38d6c : decode_any W_38d6c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38d70 : bv 32 := 0x06b56463.
Lemma F_38d70 : fetch_word Plain.M.loaded_segments (0x38db8 : word) = Some W_38d70.
Proof. vm_refl. Qed.
Lemma D_38d70 : decode_any W_38d70 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_38eac : bv 32 := 0x00000513.
Lemma F_38eac : fetch_word Plain.M.loaded_segments (0x38ef4 : word) = Some W_38eac.
Proof. vm_refl. Qed.
Lemma D_38eac : decode_any W_38eac = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38eb0 : bv 32 := 0x00008067.
Lemma F_38eb0 : fetch_word Plain.M.loaded_segments (0x38ef8 : word) = Some W_38eb0.
Proof. vm_refl. Qed.
Lemma D_38eb0 : decode_any W_38eb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r20000_21000.
Module Ns0_code_r33a9c_33b2c.
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

Definition W_38b54 : bv 32 := 0xff010113.
Lemma F_38b54 : fetch_word Plain.M.loaded_segments (0x38b9c : word) = Some W_38b54.
Proof. vm_refl. Qed.
Lemma D_38b54 : decode_any W_38b54 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b58 : bv 32 := 0x00113423.
Lemma F_38b58 : fetch_word Plain.M.loaded_segments (0x38ba0 : word) = Some W_38b58.
Proof. vm_refl. Qed.
Lemma D_38b58 : decode_any W_38b58 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b5c : bv 32 := 0x00813023.
Lemma F_38b5c : fetch_word Plain.M.loaded_segments (0x38ba4 : word) = Some W_38b5c.
Proof. vm_refl. Qed.
Lemma D_38b5c : decode_any W_38b5c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b60 : bv 32 := 0x01010413.
Lemma F_38b60 : fetch_word Plain.M.loaded_segments (0x38ba8 : word) = Some W_38b60.
Proof. vm_refl. Qed.
Lemma D_38b60 : decode_any W_38b60 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b64 : bv 32 := 0x0008e517.
Lemma F_38b64 : fetch_word Plain.M.loaded_segments (0x38bac : word) = Some W_38b64.
Proof. vm_refl. Qed.
Lemma D_38b64 : decode_any W_38b64 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b68 : bv 32 := 0x26c50513.
Lemma F_38b68 : fetch_word Plain.M.loaded_segments (0x38bb0 : word) = Some W_38b68.
Proof. vm_refl. Qed.
Lemma D_38b68 : decode_any W_38b68 = Some (OpImm ALU_ADD 10 10 620, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b6c : bv 32 := 0x00054503.
Lemma F_38b6c : fetch_word Plain.M.loaded_segments (0x38bb4 : word) = Some W_38b6c.
Proof. vm_refl. Qed.
Lemma D_38b6c : decode_any W_38b6c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b70 : bv 32 := 0x00157513.
Lemma F_38b70 : fetch_word Plain.M.loaded_segments (0x38bb8 : word) = Some W_38b70.
Proof. vm_refl. Qed.
Lemma D_38b70 : decode_any W_38b70 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b74 : bv 32 := 0x00050663.
Lemma F_38b74 : fetch_word Plain.M.loaded_segments (0x38bbc : word) = Some W_38b74.
Proof. vm_refl. Qed.
Lemma D_38b74 : decode_any W_38b74 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b78 : bv 32 := 0x0040006f.
Lemma F_38b78 : fetch_word Plain.M.loaded_segments (0x38bc0 : word) = Some W_38b78.
Proof. vm_refl. Qed.
Lemma D_38b78 : decode_any W_38b78 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b7c : bv 32 := 0x0580006f.
Lemma F_38b7c : fetch_word Plain.M.loaded_segments (0x38bc4 : word) = Some W_38b7c.
Proof. vm_refl. Qed.
Lemma D_38b7c : decode_any W_38b7c = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b80 : bv 32 := 0x0008e517.
Lemma F_38b80 : fetch_word Plain.M.loaded_segments (0x38bc8 : word) = Some W_38b80.
Proof. vm_refl. Qed.
Lemma D_38b80 : decode_any W_38b80 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b84 : bv 32 := 0x25050593.
Lemma F_38b84 : fetch_word Plain.M.loaded_segments (0x38bcc : word) = Some W_38b84.
Proof. vm_refl. Qed.
Lemma D_38b84 : decode_any W_38b84 = Some (OpImm ALU_ADD 11 10 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b88 : bv 32 := 0x00100513.
Lemma F_38b88 : fetch_word Plain.M.loaded_segments (0x38bd0 : word) = Some W_38b88.
Proof. vm_refl. Qed.
Lemma D_38b88 : decode_any W_38b88 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b8c : bv 32 := 0x00a58023.
Lemma F_38b8c : fetch_word Plain.M.loaded_segments (0x38bd4 : word) = Some W_38b8c.
Proof. vm_refl. Qed.
Lemma D_38b8c : decode_any W_38b8c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b90 : bv 32 := 0x0008d517.
Lemma F_38b90 : fetch_word Plain.M.loaded_segments (0x38bd8 : word) = Some W_38b90.
Proof. vm_refl. Qed.
Lemma D_38b90 : decode_any W_38b90 = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b94 : bv 32 := 0xd7853503.
Lemma F_38b94 : fetch_word Plain.M.loaded_segments (0x38bdc : word) = Some W_38b94.
Proof. vm_refl. Qed.
Lemma D_38b94 : decode_any W_38b94 = Some (Load SZ8 true 10 10 3448, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b98 : bv 32 := 0x00050e63.
Lemma F_38b98 : fetch_word Plain.M.loaded_segments (0x38be0 : word) = Some W_38b98.
Proof. vm_refl. Qed.
Lemma D_38b98 : decode_any W_38b98 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_38b9c : bv 32 := 0x0040006f.
Lemma F_38b9c : fetch_word Plain.M.loaded_segments (0x38be4 : word) = Some W_38b9c.
Proof. vm_refl. Qed.
Lemma D_38b9c : decode_any W_38b9c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ba0 : bv 32 := 0x0008e517.
Lemma F_38ba0 : fetch_word Plain.M.loaded_segments (0x38be8 : word) = Some W_38ba0.
Proof. vm_refl. Qed.
Lemma D_38ba0 : decode_any W_38ba0 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ba4 : bv 32 := 0xf0050513.
Lemma F_38ba4 : fetch_word Plain.M.loaded_segments (0x38bec : word) = Some W_38ba4.
Proof. vm_refl. Qed.
Lemma D_38ba4 : decode_any W_38ba4 = Some (OpImm ALU_ADD 10 10 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ba8 : bv 32 := 0x00053503.
Lemma F_38ba8 : fetch_word Plain.M.loaded_segments (0x38bf0 : word) = Some W_38ba8.
Proof. vm_refl. Qed.
Lemma D_38ba8 : decode_any W_38ba8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bac : bv 32 := 0x4f8700ef.
Lemma F_38bac : fetch_word Plain.M.loaded_segments (0x38bf4 : word) = Some W_38bac.
Proof. vm_refl. Qed.
Lemma D_38bac : decode_any W_38bac = Some (Jal 1 460024, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bb0 : bv 32 := 0x0040006f.
Lemma F_38bb0 : fetch_word Plain.M.loaded_segments (0x38bf8 : word) = Some W_38bb0.
Proof. vm_refl. Qed.
Lemma D_38bb0 : decode_any W_38bb0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bb4 : bv 32 := 0x0008d517.
Lemma F_38bb4 : fetch_word Plain.M.loaded_segments (0x38bfc : word) = Some W_38bb4.
Proof. vm_refl. Qed.
Lemma D_38bb4 : decode_any W_38bb4 = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bb8 : bv 32 := 0xd5c53503.
Lemma F_38bb8 : fetch_word Plain.M.loaded_segments (0x38c00 : word) = Some W_38bb8.
Proof. vm_refl. Qed.
Lemma D_38bb8 : decode_any W_38bb8 = Some (Load SZ8 true 10 10 3420, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bbc : bv 32 := 0x00050c63.
Lemma F_38bbc : fetch_word Plain.M.loaded_segments (0x38c04 : word) = Some W_38bbc.
Proof. vm_refl. Qed.
Lemma D_38bbc : decode_any W_38bbc = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bc0 : bv 32 := 0x0040006f.
Lemma F_38bc0 : fetch_word Plain.M.loaded_segments (0x38c08 : word) = Some W_38bc0.
Proof. vm_refl. Qed.
Lemma D_38bc0 : decode_any W_38bc0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bc4 : bv 32 := 0xffff0517.
Lemma F_38bc4 : fetch_word Plain.M.loaded_segments (0x38c0c : word) = Some W_38bc4.
Proof. vm_refl. Qed.
Lemma D_38bc4 : decode_any W_38bc4 = Some (Auipc 10 1048560, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bc8 : bv 32 := 0xdcc50513.
Lemma F_38bc8 : fetch_word Plain.M.loaded_segments (0x38c10 : word) = Some W_38bc8.
Proof. vm_refl. Qed.
Lemma D_38bc8 : decode_any W_38bc8 = Some (OpImm ALU_ADD 10 10 3532, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bcc : bv 32 := 0x000000ef.
Lemma F_38bcc : fetch_word Plain.M.loaded_segments (0x38c14 : word) = Some W_38bcc.
Proof. vm_refl. Qed.
Lemma D_38bcc : decode_any W_38bcc = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bd0 : bv 32 := 0x0040006f.
Lemma F_38bd0 : fetch_word Plain.M.loaded_segments (0x38c18 : word) = Some W_38bd0.
Proof. vm_refl. Qed.
Lemma D_38bd0 : decode_any W_38bd0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bd4 : bv 32 := 0x00813083.
Lemma F_38bd4 : fetch_word Plain.M.loaded_segments (0x38c1c : word) = Some W_38bd4.
Proof. vm_refl. Qed.
Lemma D_38bd4 : decode_any W_38bd4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bd8 : bv 32 := 0x00013403.
Lemma F_38bd8 : fetch_word Plain.M.loaded_segments (0x38c20 : word) = Some W_38bd8.
Proof. vm_refl. Qed.
Lemma D_38bd8 : decode_any W_38bd8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38bdc : bv 32 := 0x01010113.
Lemma F_38bdc : fetch_word Plain.M.loaded_segments (0x38c24 : word) = Some W_38bdc.
Proof. vm_refl. Qed.
Lemma D_38bdc : decode_any W_38bdc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38be0 : bv 32 := 0x00008067.
Lemma F_38be0 : fetch_word Plain.M.loaded_segments (0x38c28 : word) = Some W_38be0.
Proof. vm_refl. Qed.
Lemma D_38be0 : decode_any W_38be0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r33a9c_33b2c.
Module Ns0_code_r34324_34354.
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

Definition W_3900c : bv 32 := 0x0009e517.
Lemma F_3900c : fetch_word Plain.M.loaded_segments (0x39054 : word) = Some W_3900c.
Proof. vm_refl. Qed.
Lemma D_3900c : decode_any W_3900c = Some (Auipc 10 158, 4%Z).
Proof. vm_refl. Qed.

Definition W_39010 : bv 32 := 0xdd054503.
Lemma F_39010 : fetch_word Plain.M.loaded_segments (0x39058 : word) = Some W_39010.
Proof. vm_refl. Qed.
Lemma D_39010 : decode_any W_39010 = Some (Load SZ1 false 10 10 3536, 4%Z).
Proof. vm_refl. Qed.

Definition W_39014 : bv 32 := 0x00051463.
Lemma F_39014 : fetch_word Plain.M.loaded_segments (0x3905c : word) = Some W_39014.
Proof. vm_refl. Qed.
Lemma D_39014 : decode_any W_39014 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_39018 : bv 32 := 0x00008067.
Lemma F_39018 : fetch_word Plain.M.loaded_segments (0x39060 : word) = Some W_39018.
Proof. vm_refl. Qed.
Lemma D_39018 : decode_any W_39018 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3901c : bv 32 := 0xff010113.
Lemma F_3901c : fetch_word Plain.M.loaded_segments (0x39064 : word) = Some W_3901c.
Proof. vm_refl. Qed.
Lemma D_3901c : decode_any W_3901c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_39020 : bv 32 := 0x00113423.
Lemma F_39020 : fetch_word Plain.M.loaded_segments (0x39068 : word) = Some W_39020.
Proof. vm_refl. Qed.
Lemma D_39020 : decode_any W_39020 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_39024 : bv 32 := 0x0008d517.
Lemma F_39024 : fetch_word Plain.M.loaded_segments (0x3906c : word) = Some W_39024.
Proof. vm_refl. Qed.
Lemma D_39024 : decode_any W_39024 = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_39028 : bv 32 := 0x90c53503.
Lemma F_39028 : fetch_word Plain.M.loaded_segments (0x39070 : word) = Some W_39028.
Proof. vm_refl. Qed.
Lemma D_39028 : decode_any W_39028 = Some (Load SZ8 true 10 10 2316, 4%Z).
Proof. vm_refl. Qed.

Definition W_3902c : bv 32 := 0x00053503.
Lemma F_3902c : fetch_word Plain.M.loaded_segments (0x39074 : word) = Some W_3902c.
Proof. vm_refl. Qed.
Lemma D_3902c : decode_any W_3902c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39030 : bv 32 := 0x190750ef.
Lemma F_39030 : fetch_word Plain.M.loaded_segments (0x39078 : word) = Some W_39030.
Proof. vm_refl. Qed.
Lemma D_39030 : decode_any W_39030 = Some (Jal 1 479632, 4%Z).
Proof. vm_refl. Qed.

Definition W_39034 : bv 32 := 0x04d00513.
Lemma F_39034 : fetch_word Plain.M.loaded_segments (0x3907c : word) = Some W_39034.
Proof. vm_refl. Qed.
Lemma D_39034 : decode_any W_39034 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_39038 : bv 32 := 0x790850ef.
Lemma F_39038 : fetch_word Plain.M.loaded_segments (0x39080 : word) = Some W_39038.
Proof. vm_refl. Qed.
Lemma D_39038 : decode_any W_39038 = Some (Jal 1 546704, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r34324_34354.
Module Ns0_code_r4b000_4c000.
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

Definition W_a8f9c : bv 32 := 0x00050593.
Lemma F_a8f9c : fetch_word Plain.M.loaded_segments (0xa8fd8 : word) = Some W_a8f9c.
Proof. vm_refl. Qed.
Lemma D_a8f9c : decode_any W_a8f9c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8fa0 : bv 32 := 0x05e00893.
Lemma F_a8fa0 : fetch_word Plain.M.loaded_segments (0xa8fdc : word) = Some W_a8fa0.
Proof. vm_refl. Qed.
Lemma D_a8fa0 : decode_any W_a8fa0 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8fa4 : bv 32 := 0x00000073.
Lemma F_a8fa4 : fetch_word Plain.M.loaded_segments (0xa8fe0 : word) = Some W_a8fa4.
Proof. vm_refl. Qed.
Lemma D_a8fa4 : decode_any W_a8fa4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a8fa4 : is_ecall W_a8fa4 = true.
Proof. reflexivity. Qed.

Definition W_a9248 : bv 32 := 0xfe010113.
Lemma F_a9248 : fetch_word Plain.M.loaded_segments (0xa9284 : word) = Some W_a9248.
Proof. vm_refl. Qed.
Lemma D_a9248 : decode_any W_a9248 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_a924c : bv 32 := 0x00113c23.
Lemma F_a924c : fetch_word Plain.M.loaded_segments (0xa9288 : word) = Some W_a924c.
Proof. vm_refl. Qed.
Lemma D_a924c : decode_any W_a924c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9250 : bv 32 := 0x00813823.
Lemma F_a9250 : fetch_word Plain.M.loaded_segments (0xa928c : word) = Some W_a9250.
Proof. vm_refl. Qed.
Lemma D_a9250 : decode_any W_a9250 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9254 : bv 32 := 0x00913423.
Lemma F_a9254 : fetch_word Plain.M.loaded_segments (0xa9290 : word) = Some W_a9254.
Proof. vm_refl. Qed.
Lemma D_a9254 : decode_any W_a9254 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9258 : bv 32 := 0x0001d517.
Lemma F_a9258 : fetch_word Plain.M.loaded_segments (0xa9294 : word) = Some W_a9258.
Proof. vm_refl. Qed.
Lemma D_a9258 : decode_any W_a9258 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a925c : bv 32 := 0x0001d597.
Lemma F_a925c : fetch_word Plain.M.loaded_segments (0xa9298 : word) = Some W_a925c.
Proof. vm_refl. Qed.
Lemma D_a925c : decode_any W_a925c = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9260 : bv 32 := 0x82c53503.
Lemma F_a9260 : fetch_word Plain.M.loaded_segments (0xa929c : word) = Some W_a9260.
Proof. vm_refl. Qed.
Lemma D_a9260 : decode_any W_a9260 = Some (Load SZ8 true 10 10 2092, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9264 : bv 32 := 0x8305b403.
Lemma F_a9264 : fetch_word Plain.M.loaded_segments (0xa92a0 : word) = Some W_a9264.
Proof. vm_refl. Qed.
Lemma D_a9264 : decode_any W_a9264 = Some (Load SZ8 true 8 11 2096, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9268 : bv 32 := 0x00a47c63.
Lemma F_a9268 : fetch_word Plain.M.loaded_segments (0xa92a4 : word) = Some W_a9268.
Proof. vm_refl. Qed.
Lemma D_a9268 : decode_any W_a9268 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a926c : bv 32 := 0xff853583.
Lemma F_a926c : fetch_word Plain.M.loaded_segments (0xa92a8 : word) = Some W_a926c.
Proof. vm_refl. Qed.
Lemma D_a926c : decode_any W_a926c = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9270 : bv 32 := 0xff850493.
Lemma F_a9270 : fetch_word Plain.M.loaded_segments (0xa92ac : word) = Some W_a9270.
Proof. vm_refl. Qed.
Lemma D_a9270 : decode_any W_a9270 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9274 : bv 32 := 0x000580e7.
Lemma F_a9274 : fetch_word Plain.M.loaded_segments (0xa92b0 : word) = Some W_a9274.
Proof. vm_refl. Qed.
Lemma D_a9274 : decode_any W_a9274 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9278 : bv 32 := 0x00048513.
Lemma F_a9278 : fetch_word Plain.M.loaded_segments (0xa92b4 : word) = Some W_a9278.
Proof. vm_refl. Qed.
Lemma D_a9278 : decode_any W_a9278 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a927c : bv 32 := 0xfe9468e3.
Lemma F_a927c : fetch_word Plain.M.loaded_segments (0xa92b8 : word) = Some W_a927c.
Proof. vm_refl. Qed.
Lemma D_a927c : decode_any W_a927c = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9280 : bv 32 := 0x01813083.
Lemma F_a9280 : fetch_word Plain.M.loaded_segments (0xa92bc : word) = Some W_a9280.
Proof. vm_refl. Qed.
Lemma D_a9280 : decode_any W_a9280 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9284 : bv 32 := 0x01013403.
Lemma F_a9284 : fetch_word Plain.M.loaded_segments (0xa92c0 : word) = Some W_a9284.
Proof. vm_refl. Qed.
Lemma D_a9284 : decode_any W_a9284 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9288 : bv 32 := 0x00813483.
Lemma F_a9288 : fetch_word Plain.M.loaded_segments (0xa92c4 : word) = Some W_a9288.
Proof. vm_refl. Qed.
Lemma D_a9288 : decode_any W_a9288 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a928c : bv 32 := 0x02010113.
Lemma F_a928c : fetch_word Plain.M.loaded_segments (0xa92c8 : word) = Some W_a928c.
Proof. vm_refl. Qed.
Lemma D_a928c : decode_any W_a928c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9290 : bv 32 := 0xfb5ff06f.
Lemma F_a9290 : fetch_word Plain.M.loaded_segments (0xa92cc : word) = Some W_a9290.
Proof. vm_refl. Qed.
Lemma D_a9290 : decode_any W_a9290 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9294 : bv 32 := 0xff010113.
Lemma F_a9294 : fetch_word Plain.M.loaded_segments (0xa92d0 : word) = Some W_a9294.
Proof. vm_refl. Qed.
Lemma D_a9294 : decode_any W_a9294 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9298 : bv 32 := 0x00113423.
Lemma F_a9298 : fetch_word Plain.M.loaded_segments (0xa92d4 : word) = Some W_a9298.
Proof. vm_refl. Qed.
Lemma D_a9298 : decode_any W_a9298 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a929c : bv 32 := 0x00813023.
Lemma F_a929c : fetch_word Plain.M.loaded_segments (0xa92d8 : word) = Some W_a929c.
Proof. vm_refl. Qed.
Lemma D_a929c : decode_any W_a929c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92a0 : bv 32 := 0x00000593.
Lemma F_a92a0 : fetch_word Plain.M.loaded_segments (0xa92dc : word) = Some W_a92a0.
Proof. vm_refl. Qed.
Lemma D_a92a0 : decode_any W_a92a0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92a4 : bv 32 := 0x00020613.
Lemma F_a92a4 : fetch_word Plain.M.loaded_segments (0xa92e0 : word) = Some W_a92a4.
Proof. vm_refl. Qed.
Lemma D_a92a4 : decode_any W_a92a4 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92a8 : bv 32 := 0xf5862603.
Lemma F_a92a8 : fetch_word Plain.M.loaded_segments (0xa92e4 : word) = Some W_a92a8.
Proof. vm_refl. Qed.
Lemma D_a92a8 : decode_any W_a92a8 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92ac : bv 32 := 0x0004f697.
Lemma F_a92ac : fetch_word Plain.M.loaded_segments (0xa92e8 : word) = Some W_a92ac.
Proof. vm_refl. Qed.
Lemma D_a92ac : decode_any W_a92ac = Some (Auipc 13 79, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92b0 : bv 32 := 0x7d068693.
Lemma F_a92b0 : fetch_word Plain.M.loaded_segments (0xa92ec : word) = Some W_a92b0.
Proof. vm_refl. Qed.
Lemma D_a92b0 : decode_any W_a92b0 = Some (OpImm ALU_ADD 13 13 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92b4 : bv 32 := 0x1606a72f.
Lemma F_a92b4 : fetch_word Plain.M.loaded_segments (0xa92f0 : word) = Some W_a92b4.
Proof. vm_refl. Qed.
Lemma D_a92b4 : decode_any W_a92b4 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92b8 : bv 32 := 0x00b71663.
Lemma F_a92b8 : fetch_word Plain.M.loaded_segments (0xa92f4 : word) = Some W_a92b8.
Proof. vm_refl. Qed.
Lemma D_a92b8 : decode_any W_a92b8 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92bc : bv 32 := 0x1ec6a7af.
Lemma F_a92bc : fetch_word Plain.M.loaded_segments (0xa92f8 : word) = Some W_a92bc.
Proof. vm_refl. Qed.
Lemma D_a92bc : decode_any W_a92bc = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92c0 : bv 32 := 0xfe079ae3.
Lemma F_a92c0 : fetch_word Plain.M.loaded_segments (0xa92fc : word) = Some W_a92c0.
Proof. vm_refl. Qed.
Lemma D_a92c0 : decode_any W_a92c0 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92c4 : bv 32 := 0x0007059b.
Lemma F_a92c4 : fetch_word Plain.M.loaded_segments (0xa9300 : word) = Some W_a92c4.
Proof. vm_refl. Qed.
Lemma D_a92c4 : decode_any W_a92c4 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92c8 : bv 32 := 0x02c58263.
Lemma F_a92c8 : fetch_word Plain.M.loaded_segments (0xa9304 : word) = Some W_a92c8.
Proof. vm_refl. Qed.
Lemma D_a92c8 : decode_any W_a92c8 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92cc : bv 32 := 0x02058263.
Lemma F_a92cc : fetch_word Plain.M.loaded_segments (0xa9308 : word) = Some W_a92cc.
Proof. vm_refl. Qed.
Lemma D_a92cc : decode_any W_a92cc = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92f0 : bv 32 := 0x00050413.
Lemma F_a92f0 : fetch_word Plain.M.loaded_segments (0xa932c : word) = Some W_a92f0.
Proof. vm_refl. Qed.
Lemma D_a92f0 : decode_any W_a92f0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92f4 : bv 32 := 0xcf5ff0ef.
Lemma F_a92f4 : fetch_word Plain.M.loaded_segments (0xa9330 : word) = Some W_a92f4.
Proof. vm_refl. Qed.
Lemma D_a92f4 : decode_any W_a92f4 = Some (Jal 1 2096372, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92f8 : bv 32 := 0xf51ff0ef.
Lemma F_a92f8 : fetch_word Plain.M.loaded_segments (0xa9334 : word) = Some W_a92f8.
Proof. vm_refl. Qed.
Lemma D_a92f8 : decode_any W_a92f8 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_a92fc : bv 32 := 0x63c050ef.
Lemma F_a92fc : fetch_word Plain.M.loaded_segments (0xa9338 : word) = Some W_a92fc.
Proof. vm_refl. Qed.
Lemma D_a92fc : decode_any W_a92fc = Some (Jal 1 22076, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9300 : bv 32 := 0x00040513.
Lemma F_a9300 : fetch_word Plain.M.loaded_segments (0xa933c : word) = Some W_a9300.
Proof. vm_refl. Qed.
Lemma D_a9300 : decode_any W_a9300 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9304 : bv 32 := 0xc99ff0ef.
Lemma F_a9304 : fetch_word Plain.M.loaded_segments (0xa9340 : word) = Some W_a9304.
Proof. vm_refl. Qed.
Lemma D_a9304 : decode_any W_a9304 = Some (Jal 1 2096280, 4%Z).
Proof. vm_refl. Qed.

Definition W_a93ec : bv 32 := 0xff010113.
Lemma F_a93ec : fetch_word Plain.M.loaded_segments (0xa9428 : word) = Some W_a93ec.
Proof. vm_refl. Qed.
Lemma D_a93ec : decode_any W_a93ec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a93f0 : bv 32 := 0x00113423.
Lemma F_a93f0 : fetch_word Plain.M.loaded_segments (0xa942c : word) = Some W_a93f0.
Proof. vm_refl. Qed.
Lemma D_a93f0 : decode_any W_a93f0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a93f4 : bv 32 := 0x00050e63.
Lemma F_a93f4 : fetch_word Plain.M.loaded_segments (0xa9430 : word) = Some W_a93f4.
Proof. vm_refl. Qed.
Lemma D_a93f4 : decode_any W_a93f4 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a93f8 : bv 32 := 0x00050593.
Lemma F_a93f8 : fetch_word Plain.M.loaded_segments (0xa9434 : word) = Some W_a93f8.
Proof. vm_refl. Qed.
Lemma D_a93f8 : decode_any W_a93f8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a93fc : bv 32 := 0x0001c517.
Lemma F_a93fc : fetch_word Plain.M.loaded_segments (0xa9438 : word) = Some W_a93fc.
Proof. vm_refl. Qed.
Lemma D_a93fc : decode_any W_a93fc = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9400 : bv 32 := 0x68053503.
Lemma F_a9400 : fetch_word Plain.M.loaded_segments (0xa943c : word) = Some W_a9400.
Proof. vm_refl. Qed.
Lemma D_a9400 : decode_any W_a9400 = Some (Load SZ8 true 10 10 1664, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9404 : bv 32 := 0x00800613.
Lemma F_a9404 : fetch_word Plain.M.loaded_segments (0xa9440 : word) = Some W_a9404.
Proof. vm_refl. Qed.
Lemma D_a9404 : decode_any W_a9404 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9408 : bv 32 := 0x534100ef.
Lemma F_a9408 : fetch_word Plain.M.loaded_segments (0xa9444 : word) = Some W_a9408.
Proof. vm_refl. Qed.
Lemma D_a9408 : decode_any W_a9408 = Some (Jal 1 66868, 4%Z).
Proof. vm_refl. Qed.

Definition W_a940c : bv 32 := 0x01c0006f.
Lemma F_a940c : fetch_word Plain.M.loaded_segments (0xa9448 : word) = Some W_a940c.
Proof. vm_refl. Qed.
Lemma D_a940c : decode_any W_a940c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9428 : bv 32 := 0x0001c517.
Lemma F_a9428 : fetch_word Plain.M.loaded_segments (0xa9464 : word) = Some W_a9428.
Proof. vm_refl. Qed.
Lemma D_a9428 : decode_any W_a9428 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a942c : bv 32 := 0x65453503.
Lemma F_a942c : fetch_word Plain.M.loaded_segments (0xa9468 : word) = Some W_a942c.
Proof. vm_refl. Qed.
Lemma D_a942c : decode_any W_a942c = Some (Load SZ8 true 10 10 1620, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9430 : bv 32 := 0x000500a3.
Lemma F_a9430 : fetch_word Plain.M.loaded_segments (0xa946c : word) = Some W_a9430.
Proof. vm_refl. Qed.
Lemma D_a9430 : decode_any W_a9430 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9434 : bv 32 := 0x00053503.
Lemma F_a9434 : fetch_word Plain.M.loaded_segments (0xa9470 : word) = Some W_a9434.
Proof. vm_refl. Qed.
Lemma D_a9434 : decode_any W_a9434 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9438 : bv 32 := 0x00020593.
Lemma F_a9438 : fetch_word Plain.M.loaded_segments (0xa9474 : word) = Some W_a9438.
Proof. vm_refl. Qed.
Lemma D_a9438 : decode_any W_a9438 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a943c : bv 32 := 0xfea5b823.
Lemma F_a943c : fetch_word Plain.M.loaded_segments (0xa9478 : word) = Some W_a943c.
Proof. vm_refl. Qed.
Lemma D_a943c : decode_any W_a943c = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9440 : bv 32 := 0x00813083.
Lemma F_a9440 : fetch_word Plain.M.loaded_segments (0xa947c : word) = Some W_a9440.
Proof. vm_refl. Qed.
Lemma D_a9440 : decode_any W_a9440 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9444 : bv 32 := 0x01010113.
Lemma F_a9444 : fetch_word Plain.M.loaded_segments (0xa9480 : word) = Some W_a9444.
Proof. vm_refl. Qed.
Lemma D_a9444 : decode_any W_a9444 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9448 : bv 32 := 0x00008067.
Lemma F_a9448 : fetch_word Plain.M.loaded_segments (0xa9484 : word) = Some W_a9448.
Proof. vm_refl. Qed.
Lemma D_a9448 : decode_any W_a9448 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9454 : bv 32 := 0xfffff5b7.
Lemma F_a9454 : fetch_word Plain.M.loaded_segments (0xa9490 : word) = Some W_a9454.
Proof. vm_refl. Qed.
Lemma D_a9454 : decode_any W_a9454 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9458 : bv 32 := 0x0015859b.
Lemma F_a9458 : fetch_word Plain.M.loaded_segments (0xa9494 : word) = Some W_a9458.
Proof. vm_refl. Qed.
Lemma D_a9458 : decode_any W_a9458 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a945c : bv 32 := 0x02b56663.
Lemma F_a945c : fetch_word Plain.M.loaded_segments (0xa9498 : word) = Some W_a945c.
Proof. vm_refl. Qed.
Lemma D_a945c : decode_any W_a945c = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9488 : bv 32 := 0x00008067.
Lemma F_a9488 : fetch_word Plain.M.loaded_segments (0xa94c4 : word) = Some W_a9488.
Proof. vm_refl. Qed.
Lemma D_a9488 : decode_any W_a9488 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r4b000_4c000.
Module Ns0_code_r4d000_4e000.
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

Definition W_ae6e0 : bv 32 := 0x02d61863.
Lemma F_ae6e0 : fetch_word Plain.M.loaded_segments (0xae71c : word) = Some W_ae6e0.
Proof. vm_refl. Qed.
Lemma D_ae6e0 : decode_any W_ae6e0 = Some (Branch BC_NE 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae700 : bv 32 := 0x02e5b423.
Lemma F_ae700 : fetch_word Plain.M.loaded_segments (0xae73c : word) = Some W_ae700.
Proof. vm_refl. Qed.
Lemma D_ae700 : decode_any W_ae700 = Some (Store SZ8 11 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae710 : bv 32 := 0x0100006f.
Lemma F_ae710 : fetch_word Plain.M.loaded_segments (0xae74c : word) = Some W_ae710.
Proof. vm_refl. Qed.
Lemma D_ae710 : decode_any W_ae710 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae714 : bv 32 := 0x00058513.
Lemma F_ae714 : fetch_word Plain.M.loaded_segments (0xae750 : word) = Some W_ae714.
Proof. vm_refl. Qed.
Lemma D_ae714 : decode_any W_ae714 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae73c : bv 32 := 0x08c48413.
Lemma F_ae73c : fetch_word Plain.M.loaded_segments (0xae778 : word) = Some W_ae73c.
Proof. vm_refl. Qed.
Lemma D_ae73c : decode_any W_ae73c = Some (OpImm ALU_ADD 8 9 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae778 : bv 32 := 0x0204b583.
Lemma F_ae778 : fetch_word Plain.M.loaded_segments (0xae7b4 : word) = Some W_ae778.
Proof. vm_refl. Qed.
Lemma D_ae778 : decode_any W_ae778 = Some (Load SZ8 true 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae784 : bv 32 := 0x00150593.
Lemma F_ae784 : fetch_word Plain.M.loaded_segments (0xae7c0 : word) = Some W_ae784.
Proof. vm_refl. Qed.
Lemma D_ae784 : decode_any W_ae784 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae788 : bv 32 := 0x02b4b423.
Lemma F_ae788 : fetch_word Plain.M.loaded_segments (0xae7c4 : word) = Some W_ae788.
Proof. vm_refl. Qed.
Lemma D_ae788 : decode_any W_ae788 = Some (Store SZ8 9 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae78c : bv 32 := 0x01250023.
Lemma F_ae78c : fetch_word Plain.M.loaded_segments (0xae7c8 : word) = Some W_ae78c.
Proof. vm_refl. Qed.
Lemma D_ae78c : decode_any W_ae78c = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae790 : bv 32 := 0x0140006f.
Lemma F_ae790 : fetch_word Plain.M.loaded_segments (0xae7cc : word) = Some W_ae790.
Proof. vm_refl. Qed.
Lemma D_ae790 : decode_any W_ae790 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae794 : bv 32 := 0x00048513.
Lemma F_ae794 : fetch_word Plain.M.loaded_segments (0xae7d0 : word) = Some W_ae794.
Proof. vm_refl. Qed.
Lemma D_ae794 : decode_any W_ae794 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae798 : bv 32 := 0x00068593.
Lemma F_ae798 : fetch_word Plain.M.loaded_segments (0xae7d4 : word) = Some W_ae798.
Proof. vm_refl. Qed.
Lemma D_ae798 : decode_any W_ae798 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae79c : bv 32 := 0x07c000ef.
Lemma F_ae79c : fetch_word Plain.M.loaded_segments (0xae7d8 : word) = Some W_ae79c.
Proof. vm_refl. Qed.
Lemma D_ae79c : decode_any W_ae79c = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7a0 : bv 32 := 0x00050693.
Lemma F_ae7a0 : fetch_word Plain.M.loaded_segments (0xae7dc : word) = Some W_ae7a0.
Proof. vm_refl. Qed.
Lemma D_ae7a0 : decode_any W_ae7a0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7a4 : bv 32 := 0x00000513.
Lemma F_ae7a4 : fetch_word Plain.M.loaded_segments (0xae7e0 : word) = Some W_ae7a4.
Proof. vm_refl. Qed.
Lemma D_ae7a4 : decode_any W_ae7a4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7a8 : bv 32 := 0x00042583.
Lemma F_ae7a8 : fetch_word Plain.M.loaded_segments (0xae7e4 : word) = Some W_ae7a8.
Proof. vm_refl. Qed.
Lemma D_ae7a8 : decode_any W_ae7a8 = Some (Load SZ4 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7ac : bv 32 := 0x1604262f.
Lemma F_ae7ac : fetch_word Plain.M.loaded_segments (0xae7e8 : word) = Some W_ae7ac.
Proof. vm_refl. Qed.
Lemma D_ae7ac : decode_any W_ae7ac = Some (Lr AW true true 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7b0 : bv 32 := 0x00b61663.
Lemma F_ae7b0 : fetch_word Plain.M.loaded_segments (0xae7ec : word) = Some W_ae7b0.
Proof. vm_refl. Qed.
Lemma D_ae7b0 : decode_any W_ae7b0 = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7b4 : bv 32 := 0x1ea4272f.
Lemma F_ae7b4 : fetch_word Plain.M.loaded_segments (0xae7f0 : word) = Some W_ae7b4.
Proof. vm_refl. Qed.
Lemma D_ae7b4 : decode_any W_ae7b4 = Some (Sc AW true true 14 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7b8 : bv 32 := 0xfe071ae3.
Lemma F_ae7b8 : fetch_word Plain.M.loaded_segments (0xae7f4 : word) = Some W_ae7b8.
Proof. vm_refl. Qed.
Lemma D_ae7b8 : decode_any W_ae7b8 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7bc : bv 32 := 0x0006061b.
Lemma F_ae7bc : fetch_word Plain.M.loaded_segments (0xae7f8 : word) = Some W_ae7bc.
Proof. vm_refl. Qed.
Lemma D_ae7bc : decode_any W_ae7bc = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7c0 : bv 32 := 0xfeb614e3.
Lemma F_ae7c0 : fetch_word Plain.M.loaded_segments (0xae7fc : word) = Some W_ae7c0.
Proof. vm_refl. Qed.
Lemma D_ae7c0 : decode_any W_ae7c0 = Some (Branch BC_NE 12 11 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7c4 : bv 32 := 0x02159593.
Lemma F_ae7c4 : fetch_word Plain.M.loaded_segments (0xae800 : word) = Some W_ae7c4.
Proof. vm_refl. Qed.
Lemma D_ae7c4 : decode_any W_ae7c4 = Some (ShiftImm ALU_SLL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7c8 : bv 32 := 0x0205da63.
Lemma F_ae7c8 : fetch_word Plain.M.loaded_segments (0xae804 : word) = Some W_ae7c8.
Proof. vm_refl. Qed.
Lemma D_ae7c8 : decode_any W_ae7c8 = Some (Branch BC_GE 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7cc : bv 32 := 0x06200893.
Lemma F_ae7cc : fetch_word Plain.M.loaded_segments (0xae808 : word) = Some W_ae7cc.
Proof. vm_refl. Qed.
Lemma D_ae7cc : decode_any W_ae7cc = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7d0 : bv 32 := 0x08100593.
Lemma F_ae7d0 : fetch_word Plain.M.loaded_segments (0xae80c : word) = Some W_ae7d0.
Proof. vm_refl. Qed.
Lemma D_ae7d0 : decode_any W_ae7d0 = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7d4 : bv 32 := 0x00100613.
Lemma F_ae7d4 : fetch_word Plain.M.loaded_segments (0xae810 : word) = Some W_ae7d4.
Proof. vm_refl. Qed.
Lemma D_ae7d4 : decode_any W_ae7d4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7d8 : bv 32 := 0xfda00713.
Lemma F_ae7d8 : fetch_word Plain.M.loaded_segments (0xae814 : word) = Some W_ae7d8.
Proof. vm_refl. Qed.
Lemma D_ae7d8 : decode_any W_ae7d8 = Some (OpImm ALU_ADD 14 0 4058, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7dc : bv 32 := 0x00040513.
Lemma F_ae7dc : fetch_word Plain.M.loaded_segments (0xae818 : word) = Some W_ae7dc.
Proof. vm_refl. Qed.
Lemma D_ae7dc : decode_any W_ae7dc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7e0 : bv 32 := 0x00000073.
Lemma F_ae7e0 : fetch_word Plain.M.loaded_segments (0xae81c : word) = Some W_ae7e0.
Proof. vm_refl. Qed.
Lemma D_ae7e0 : decode_any W_ae7e0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ae7e0 : is_ecall W_ae7e0 = true.
Proof. reflexivity. Qed.

Definition W_ae7e4 : bv 32 := 0x00e51c63.
Lemma F_ae7e4 : fetch_word Plain.M.loaded_segments (0xae820 : word) = Some W_ae7e4.
Proof. vm_refl. Qed.
Lemma D_ae7e4 : decode_any W_ae7e4 = Some (Branch BC_NE 10 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7e8 : bv 32 := 0x06200893.
Lemma F_ae7e8 : fetch_word Plain.M.loaded_segments (0xae824 : word) = Some W_ae7e8.
Proof. vm_refl. Qed.
Lemma D_ae7e8 : decode_any W_ae7e8 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7ec : bv 32 := 0x00100593.
Lemma F_ae7ec : fetch_word Plain.M.loaded_segments (0xae828 : word) = Some W_ae7ec.
Proof. vm_refl. Qed.
Lemma D_ae7ec : decode_any W_ae7ec = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7f0 : bv 32 := 0x00100613.
Lemma F_ae7f0 : fetch_word Plain.M.loaded_segments (0xae82c : word) = Some W_ae7f0.
Proof. vm_refl. Qed.
Lemma D_ae7f0 : decode_any W_ae7f0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7f4 : bv 32 := 0x00040513.
Lemma F_ae7f4 : fetch_word Plain.M.loaded_segments (0xae830 : word) = Some W_ae7f4.
Proof. vm_refl. Qed.
Lemma D_ae7f4 : decode_any W_ae7f4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae7f8 : bv 32 := 0x00000073.
Lemma F_ae7f8 : fetch_word Plain.M.loaded_segments (0xae834 : word) = Some W_ae7f8.
Proof. vm_refl. Qed.
Lemma D_ae7f8 : decode_any W_ae7f8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ae7f8 : is_ecall W_ae7f8 = true.
Proof. reflexivity. Qed.

Definition W_ae7fc : bv 32 := 0x00068513.
Lemma F_ae7fc : fetch_word Plain.M.loaded_segments (0xae838 : word) = Some W_ae7fc.
Proof. vm_refl. Qed.
Lemma D_ae7fc : decode_any W_ae7fc = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae800 : bv 32 := 0x01813083.
Lemma F_ae800 : fetch_word Plain.M.loaded_segments (0xae83c : word) = Some W_ae800.
Proof. vm_refl. Qed.
Lemma D_ae800 : decode_any W_ae800 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae804 : bv 32 := 0x01013403.
Lemma F_ae804 : fetch_word Plain.M.loaded_segments (0xae840 : word) = Some W_ae804.
Proof. vm_refl. Qed.
Lemma D_ae804 : decode_any W_ae804 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae808 : bv 32 := 0x00813483.
Lemma F_ae808 : fetch_word Plain.M.loaded_segments (0xae844 : word) = Some W_ae808.
Proof. vm_refl. Qed.
Lemma D_ae808 : decode_any W_ae808 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae80c : bv 32 := 0x00013903.
Lemma F_ae80c : fetch_word Plain.M.loaded_segments (0xae848 : word) = Some W_ae80c.
Proof. vm_refl. Qed.
Lemma D_ae80c : decode_any W_ae80c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae810 : bv 32 := 0x02010113.
Lemma F_ae810 : fetch_word Plain.M.loaded_segments (0xae84c : word) = Some W_ae810.
Proof. vm_refl. Qed.
Lemma D_ae810 : decode_any W_ae810 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae814 : bv 32 := 0x00008067.
Lemma F_ae814 : fetch_word Plain.M.loaded_segments (0xae850 : word) = Some W_ae814.
Proof. vm_refl. Qed.
Lemma D_ae814 : decode_any W_ae814 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae818 : bv 32 := 0xfd010113.
Lemma F_ae818 : fetch_word Plain.M.loaded_segments (0xae854 : word) = Some W_ae818.
Proof. vm_refl. Qed.
Lemma D_ae818 : decode_any W_ae818 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae81c : bv 32 := 0x02113423.
Lemma F_ae81c : fetch_word Plain.M.loaded_segments (0xae858 : word) = Some W_ae81c.
Proof. vm_refl. Qed.
Lemma D_ae81c : decode_any W_ae81c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae820 : bv 32 := 0x02813023.
Lemma F_ae820 : fetch_word Plain.M.loaded_segments (0xae85c : word) = Some W_ae820.
Proof. vm_refl. Qed.
Lemma D_ae820 : decode_any W_ae820 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae824 : bv 32 := 0x00913c23.
Lemma F_ae824 : fetch_word Plain.M.loaded_segments (0xae860 : word) = Some W_ae824.
Proof. vm_refl. Qed.
Lemma D_ae824 : decode_any W_ae824 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae828 : bv 32 := 0x01213823.
Lemma F_ae828 : fetch_word Plain.M.loaded_segments (0xae864 : word) = Some W_ae828.
Proof. vm_refl. Qed.
Lemma D_ae828 : decode_any W_ae828 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae82c : bv 32 := 0x00017617.
Lemma F_ae82c : fetch_word Plain.M.loaded_segments (0xae868 : word) = Some W_ae82c.
Proof. vm_refl. Qed.
Lemma D_ae82c : decode_any W_ae82c = Some (Auipc 12 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae830 : bv 32 := 0x25063403.
Lemma F_ae830 : fetch_word Plain.M.loaded_segments (0xae86c : word) = Some W_ae830.
Proof. vm_refl. Qed.
Lemma D_ae830 : decode_any W_ae830 = Some (Load SZ8 true 8 12 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae834 : bv 32 := 0x00043603.
Lemma F_ae834 : fetch_word Plain.M.loaded_segments (0xae870 : word) = Some W_ae834.
Proof. vm_refl. Qed.
Lemma D_ae834 : decode_any W_ae834 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae838 : bv 32 := 0x00c13423.
Lemma F_ae838 : fetch_word Plain.M.loaded_segments (0xae874 : word) = Some W_ae838.
Proof. vm_refl. Qed.
Lemma D_ae838 : decode_any W_ae838 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae83c : bv 32 := 0x02053683.
Lemma F_ae83c : fetch_word Plain.M.loaded_segments (0xae878 : word) = Some W_ae83c.
Proof. vm_refl. Qed.
Lemma D_ae83c : decode_any W_ae83c = Some (Load SZ8 true 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae840 : bv 32 := 0x00b103a3.
Lemma F_ae840 : fetch_word Plain.M.loaded_segments (0xae87c : word) = Some W_ae840.
Proof. vm_refl. Qed.
Lemma D_ae840 : decode_any W_ae840 = Some (Store SZ1 2 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae844 : bv 32 := 0x02068c63.
Lemma F_ae844 : fetch_word Plain.M.loaded_segments (0xae880 : word) = Some W_ae844.
Proof. vm_refl. Qed.
Lemma D_ae844 : decode_any W_ae844 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae848 : bv 32 := 0x02853603.
Lemma F_ae848 : fetch_word Plain.M.loaded_segments (0xae884 : word) = Some W_ae848.
Proof. vm_refl. Qed.
Lemma D_ae848 : decode_any W_ae848 = Some (Load SZ8 true 12 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae84c : bv 32 := 0x00d60863.
Lemma F_ae84c : fetch_word Plain.M.loaded_segments (0xae888 : word) = Some W_ae84c.
Proof. vm_refl. Qed.
Lemma D_ae84c : decode_any W_ae84c = Some (Branch BC_EQ 12 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae850 : bv 32 := 0x09052703.
Lemma F_ae850 : fetch_word Plain.M.loaded_segments (0xae88c : word) = Some W_ae850.
Proof. vm_refl. Qed.
Lemma D_ae850 : decode_any W_ae850 = Some (Load SZ4 true 14 10 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae854 : bv 32 := 0x0ff5f793.
Lemma F_ae854 : fetch_word Plain.M.loaded_segments (0xae890 : word) = Some W_ae854.
Proof. vm_refl. Qed.
Lemma D_ae854 : decode_any W_ae854 = Some (OpImm ALU_AND 15 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae858 : bv 32 := 0x02f71e63.
Lemma F_ae858 : fetch_word Plain.M.loaded_segments (0xae894 : word) = Some W_ae858.
Proof. vm_refl. Qed.
Lemma D_ae858 : decode_any W_ae858 = Some (Branch BC_NE 14 15 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae85c : bv 32 := 0x04853683.
Lemma F_ae85c : fetch_word Plain.M.loaded_segments (0xae898 : word) = Some W_ae85c.
Proof. vm_refl. Qed.
Lemma D_ae85c : decode_any W_ae85c = Some (Load SZ8 true 13 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae860 : bv 32 := 0x00710593.
Lemma F_ae860 : fetch_word Plain.M.loaded_segments (0xae89c : word) = Some W_ae860.
Proof. vm_refl. Qed.
Lemma D_ae860 : decode_any W_ae860 = Some (OpImm ALU_ADD 11 2 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae864 : bv 32 := 0x00100613.
Lemma F_ae864 : fetch_word Plain.M.loaded_segments (0xae8a0 : word) = Some W_ae864.
Proof. vm_refl. Qed.
Lemma D_ae864 : decode_any W_ae864 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae904 : bv 32 := 0x06053683.
Lemma F_ae904 : fetch_word Plain.M.loaded_segments (0xae940 : word) = Some W_ae904.
Proof. vm_refl. Qed.
Lemma D_ae904 : decode_any W_ae904 = Some (Load SZ8 true 13 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae908 : bv 32 := 0x02c53c23.
Lemma F_ae908 : fetch_word Plain.M.loaded_segments (0xae944 : word) = Some W_ae908.
Proof. vm_refl. Qed.
Lemma D_ae908 : decode_any W_ae908 = Some (Store SZ8 10 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae914 : bv 32 := 0x00053823.
Lemma F_ae914 : fetch_word Plain.M.loaded_segments (0xae950 : word) = Some W_ae914.
Proof. vm_refl. Qed.
Lemma D_ae914 : decode_any W_ae914 = Some (Store SZ8 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae918 : bv 32 := 0x02d53023.
Lemma F_ae918 : fetch_word Plain.M.loaded_segments (0xae954 : word) = Some W_ae918.
Proof. vm_refl. Qed.
Lemma D_ae918 : decode_any W_ae918 = Some (Store SZ8 10 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae91c : bv 32 := 0x02c53423.
Lemma F_ae91c : fetch_word Plain.M.loaded_segments (0xae958 : word) = Some W_ae91c.
Proof. vm_refl. Qed.
Lemma D_ae91c : decode_any W_ae91c = Some (Store SZ8 10 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae920 : bv 32 := 0x00000513.
Lemma F_ae920 : fetch_word Plain.M.loaded_segments (0xae95c : word) = Some W_ae920.
Proof. vm_refl. Qed.
Lemma D_ae920 : decode_any W_ae920 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae924 : bv 32 := 0x00008067.
Lemma F_ae924 : fetch_word Plain.M.loaded_segments (0xae960 : word) = Some W_ae924.
Proof. vm_refl. Qed.
Lemma D_ae924 : decode_any W_ae924 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae928 : bv 32 := 0x0205e593.
Lemma F_ae928 : fetch_word Plain.M.loaded_segments (0xae964 : word) = Some W_ae928.
Proof. vm_refl. Qed.
Lemma D_ae928 : decode_any W_ae928 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae92c : bv 32 := 0x00b52023.
Lemma F_ae92c : fetch_word Plain.M.loaded_segments (0xae968 : word) = Some W_ae92c.
Proof. vm_refl. Qed.
Lemma D_ae92c : decode_any W_ae92c = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae930 : bv 32 := 0xfff00513.
Lemma F_ae930 : fetch_word Plain.M.loaded_segments (0xae96c : word) = Some W_ae930.
Proof. vm_refl. Qed.
Lemma D_ae930 : decode_any W_ae930 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae934 : bv 32 := 0x00008067.
Lemma F_ae934 : fetch_word Plain.M.loaded_segments (0xae970 : word) = Some W_ae934.
Proof. vm_refl. Qed.
Lemma D_ae934 : decode_any W_ae934 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae938 : bv 32 := 0xff010113.
Lemma F_ae938 : fetch_word Plain.M.loaded_segments (0xae974 : word) = Some W_ae938.
Proof. vm_refl. Qed.
Lemma D_ae938 : decode_any W_ae938 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae93c : bv 32 := 0x00113423.
Lemma F_ae93c : fetch_word Plain.M.loaded_segments (0xae978 : word) = Some W_ae93c.
Proof. vm_refl. Qed.
Lemma D_ae93c : decode_any W_ae93c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae940 : bv 32 := 0x00813023.
Lemma F_ae940 : fetch_word Plain.M.loaded_segments (0xae97c : word) = Some W_ae940.
Proof. vm_refl. Qed.
Lemma D_ae940 : decode_any W_ae940 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae944 : bv 32 := 0x41c000ef.
Lemma F_ae944 : fetch_word Plain.M.loaded_segments (0xae980 : word) = Some W_ae944.
Proof. vm_refl. Qed.
Lemma D_ae944 : decode_any W_ae944 = Some (Jal 1 1052, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae948 : bv 32 := 0x00053403.
Lemma F_ae948 : fetch_word Plain.M.loaded_segments (0xae984 : word) = Some W_ae948.
Proof. vm_refl. Qed.
Lemma D_ae948 : decode_any W_ae948 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae94c : bv 32 := 0x12041663.
Lemma F_ae94c : fetch_word Plain.M.loaded_segments (0xae988 : word) = Some W_ae94c.
Proof. vm_refl. Qed.
Lemma D_ae94c : decode_any W_ae94c = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae950 : bv 32 := 0x0004a517.
Lemma F_ae950 : fetch_word Plain.M.loaded_segments (0xae98c : word) = Some W_ae950.
Proof. vm_refl. Qed.
Lemma D_ae950 : decode_any W_ae950 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae954 : bv 32 := 0x68c53403.
Lemma F_ae954 : fetch_word Plain.M.loaded_segments (0xae990 : word) = Some W_ae954.
Proof. vm_refl. Qed.
Lemma D_ae954 : decode_any W_ae954 = Some (Load SZ8 true 8 10 1676, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae958 : bv 32 := 0x04040a63.
Lemma F_ae958 : fetch_word Plain.M.loaded_segments (0xae994 : word) = Some W_ae958.
Proof. vm_refl. Qed.
Lemma D_ae958 : decode_any W_ae958 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9ac : bv 32 := 0x00018517.
Lemma F_ae9ac : fetch_word Plain.M.loaded_segments (0xae9e8 : word) = Some W_ae9ac.
Proof. vm_refl. Qed.
Lemma D_ae9ac : decode_any W_ae9ac = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9b0 : bv 32 := 0x3c053403.
Lemma F_ae9b0 : fetch_word Plain.M.loaded_segments (0xae9ec : word) = Some W_ae9b0.
Proof. vm_refl. Qed.
Lemma D_ae9b0 : decode_any W_ae9b0 = Some (Load SZ8 true 8 10 960, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9b4 : bv 32 := 0x04040a63.
Lemma F_ae9b4 : fetch_word Plain.M.loaded_segments (0xae9f0 : word) = Some W_ae9b4.
Proof. vm_refl. Qed.
Lemma D_ae9b4 : decode_any W_ae9b4 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9b8 : bv 32 := 0x08c42503.
Lemma F_ae9b8 : fetch_word Plain.M.loaded_segments (0xae9f4 : word) = Some W_ae9b8.
Proof. vm_refl. Qed.
Lemma D_ae9b8 : decode_any W_ae9b8 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9bc : bv 32 := 0x00054663.
Lemma F_ae9bc : fetch_word Plain.M.loaded_segments (0xae9f8 : word) = Some W_ae9bc.
Proof. vm_refl. Qed.
Lemma D_ae9bc : decode_any W_ae9bc = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9c8 : bv 32 := 0x02843503.
Lemma F_ae9c8 : fetch_word Plain.M.loaded_segments (0xaea04 : word) = Some W_ae9c8.
Proof. vm_refl. Qed.
Lemma D_ae9c8 : decode_any W_ae9c8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9cc : bv 32 := 0x03843583.
Lemma F_ae9cc : fetch_word Plain.M.loaded_segments (0xaea08 : word) = Some W_ae9cc.
Proof. vm_refl. Qed.
Lemma D_ae9cc : decode_any W_ae9cc = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9d0 : bv 32 := 0x00b50c63.
Lemma F_ae9d0 : fetch_word Plain.M.loaded_segments (0xaea0c : word) = Some W_ae9d0.
Proof. vm_refl. Qed.
Lemma D_ae9d0 : decode_any W_ae9d0 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9d4 : bv 32 := 0x04843683.
Lemma F_ae9d4 : fetch_word Plain.M.loaded_segments (0xaea10 : word) = Some W_ae9d4.
Proof. vm_refl. Qed.
Lemma D_ae9d4 : decode_any W_ae9d4 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9d8 : bv 32 := 0x00040513.
Lemma F_ae9d8 : fetch_word Plain.M.loaded_segments (0xaea14 : word) = Some W_ae9d8.
Proof. vm_refl. Qed.
Lemma D_ae9d8 : decode_any W_ae9d8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9dc : bv 32 := 0x00000593.
Lemma F_ae9dc : fetch_word Plain.M.loaded_segments (0xaea18 : word) = Some W_ae9dc.
Proof. vm_refl. Qed.
Lemma D_ae9dc : decode_any W_ae9dc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9e0 : bv 32 := 0x00000613.
Lemma F_ae9e0 : fetch_word Plain.M.loaded_segments (0xaea1c : word) = Some W_ae9e0.
Proof. vm_refl. Qed.
Lemma D_ae9e0 : decode_any W_ae9e0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9e4 : bv 32 := 0x000680e7.
Lemma F_ae9e4 : fetch_word Plain.M.loaded_segments (0xaea20 : word) = Some W_ae9e4.
Proof. vm_refl. Qed.
Lemma D_ae9e4 : decode_any W_ae9e4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9e8 : bv 32 := 0x00843503.
Lemma F_ae9e8 : fetch_word Plain.M.loaded_segments (0xaea24 : word) = Some W_ae9e8.
Proof. vm_refl. Qed.
Lemma D_ae9e8 : decode_any W_ae9e8 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9ec : bv 32 := 0x01043583.
Lemma F_ae9ec : fetch_word Plain.M.loaded_segments (0xaea28 : word) = Some W_ae9ec.
Proof. vm_refl. Qed.
Lemma D_ae9ec : decode_any W_ae9ec = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae9f0 : bv 32 := 0x00b50c63.
Lemma F_ae9f0 : fetch_word Plain.M.loaded_segments (0xaea2c : word) = Some W_ae9f0.
Proof. vm_refl. Qed.
Lemma D_ae9f0 : decode_any W_ae9f0 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea08 : bv 32 := 0x00018517.
Lemma F_aea08 : fetch_word Plain.M.loaded_segments (0xaea44 : word) = Some W_aea08.
Proof. vm_refl. Qed.
Lemma D_aea08 : decode_any W_aea08 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea0c : bv 32 := 0x27453403.
Lemma F_aea0c : fetch_word Plain.M.loaded_segments (0xaea48 : word) = Some W_aea0c.
Proof. vm_refl. Qed.
Lemma D_aea0c : decode_any W_aea0c = Some (Load SZ8 true 8 10 628, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea10 : bv 32 := 0x0a040e63.
Lemma F_aea10 : fetch_word Plain.M.loaded_segments (0xaea4c : word) = Some W_aea10.
Proof. vm_refl. Qed.
Lemma D_aea10 : decode_any W_aea10 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea14 : bv 32 := 0x08c42503.
Lemma F_aea14 : fetch_word Plain.M.loaded_segments (0xaea50 : word) = Some W_aea14.
Proof. vm_refl. Qed.
Lemma D_aea14 : decode_any W_aea14 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea18 : bv 32 := 0x00054663.
Lemma F_aea18 : fetch_word Plain.M.loaded_segments (0xaea54 : word) = Some W_aea18.
Proof. vm_refl. Qed.
Lemma D_aea18 : decode_any W_aea18 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea24 : bv 32 := 0x02843503.
Lemma F_aea24 : fetch_word Plain.M.loaded_segments (0xaea60 : word) = Some W_aea24.
Proof. vm_refl. Qed.
Lemma D_aea24 : decode_any W_aea24 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea28 : bv 32 := 0x03843583.
Lemma F_aea28 : fetch_word Plain.M.loaded_segments (0xaea64 : word) = Some W_aea28.
Proof. vm_refl. Qed.
Lemma D_aea28 : decode_any W_aea28 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea2c : bv 32 := 0x00b50c63.
Lemma F_aea2c : fetch_word Plain.M.loaded_segments (0xaea68 : word) = Some W_aea2c.
Proof. vm_refl. Qed.
Lemma D_aea2c : decode_any W_aea2c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea44 : bv 32 := 0x00843503.
Lemma F_aea44 : fetch_word Plain.M.loaded_segments (0xaea80 : word) = Some W_aea44.
Proof. vm_refl. Qed.
Lemma D_aea44 : decode_any W_aea44 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea48 : bv 32 := 0x01043583.
Lemma F_aea48 : fetch_word Plain.M.loaded_segments (0xaea84 : word) = Some W_aea48.
Proof. vm_refl. Qed.
Lemma D_aea48 : decode_any W_aea48 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_aea4c : bv 32 := 0x08b50063.
Lemma F_aea4c : fetch_word Plain.M.loaded_segments (0xaea88 : word) = Some W_aea4c.
Proof. vm_refl. Qed.
Lemma D_aea4c : decode_any W_aea4c = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_aeacc : bv 32 := 0x00813083.
Lemma F_aeacc : fetch_word Plain.M.loaded_segments (0xaeb08 : word) = Some W_aeacc.
Proof. vm_refl. Qed.
Lemma D_aeacc : decode_any W_aeacc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aead0 : bv 32 := 0x00013403.
Lemma F_aead0 : fetch_word Plain.M.loaded_segments (0xaeb0c : word) = Some W_aead0.
Proof. vm_refl. Qed.
Lemma D_aead0 : decode_any W_aead0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aead4 : bv 32 := 0x01010113.
Lemma F_aead4 : fetch_word Plain.M.loaded_segments (0xaeb10 : word) = Some W_aead4.
Proof. vm_refl. Qed.
Lemma D_aead4 : decode_any W_aead4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_aead8 : bv 32 := 0x00008067.
Lemma F_aead8 : fetch_word Plain.M.loaded_segments (0xaeb14 : word) = Some W_aead8.
Proof. vm_refl. Qed.
Lemma D_aead8 : decode_any W_aead8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r4d000_4e000.
Module Ns0_code_r55a7c_55a80.
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

Definition W_654f4 : bv 32 := 0x00008067.
Lemma F_654f4 : fetch_word Plain.M.loaded_segments (0x6553c : word) = Some W_654f4.
Proof. vm_refl. Qed.
Lemma D_654f4 : decode_any W_654f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r55a7c_55a80.
Module Ns0_code_r56d4c_56d5c.
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

Definition W_65a8c : bv 32 := 0x00054583.
Lemma F_65a8c : fetch_word Plain.M.loaded_segments (0x65ad4 : word) = Some W_65a8c.
Proof. vm_refl. Qed.
Lemma D_65a8c : decode_any W_65a8c = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a90 : bv 32 := 0x0015f593.
Lemma F_65a90 : fetch_word Plain.M.loaded_segments (0x65ad8 : word) = Some W_65a90.
Proof. vm_refl. Qed.
Lemma D_65a90 : decode_any W_65a90 = Some (OpImm ALU_AND 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a94 : bv 32 := 0x00059463.
Lemma F_65a94 : fetch_word Plain.M.loaded_segments (0x65adc : word) = Some W_65a94.
Proof. vm_refl. Qed.
Lemma D_65a94 : decode_any W_65a94 = Some (Branch BC_NE 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a98 : bv 32 := 0x00008067.
Lemma F_65a98 : fetch_word Plain.M.loaded_segments (0x65ae0 : word) = Some W_65a98.
Proof. vm_refl. Qed.
Lemma D_65a98 : decode_any W_65a98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r56d4c_56d5c.
Module Ns0_code_r98734_98800.
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

Definition W_a8fe8 : bv 32 := 0xfd010113.
Lemma F_a8fe8 : fetch_word Plain.M.loaded_segments (0xa9024 : word) = Some W_a8fe8.
Proof. vm_refl. Qed.
Lemma D_a8fe8 : decode_any W_a8fe8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8fec : bv 32 := 0x02113423.
Lemma F_a8fec : fetch_word Plain.M.loaded_segments (0xa9028 : word) = Some W_a8fec.
Proof. vm_refl. Qed.
Lemma D_a8fec : decode_any W_a8fec = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ff0 : bv 32 := 0x02813023.
Lemma F_a8ff0 : fetch_word Plain.M.loaded_segments (0xa902c : word) = Some W_a8ff0.
Proof. vm_refl. Qed.
Lemma D_a8ff0 : decode_any W_a8ff0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ff4 : bv 32 := 0x00913c23.
Lemma F_a8ff4 : fetch_word Plain.M.loaded_segments (0xa9030 : word) = Some W_a8ff4.
Proof. vm_refl. Qed.
Lemma D_a8ff4 : decode_any W_a8ff4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ff8 : bv 32 := 0x01213823.
Lemma F_a8ff8 : fetch_word Plain.M.loaded_segments (0xa9034 : word) = Some W_a8ff8.
Proof. vm_refl. Qed.
Lemma D_a8ff8 : decode_any W_a8ff8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ffc : bv 32 := 0x01313423.
Lemma F_a8ffc : fetch_word Plain.M.loaded_segments (0xa9038 : word) = Some W_a8ffc.
Proof. vm_refl. Qed.
Lemma D_a8ffc : decode_any W_a8ffc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9000 : bv 32 := 0x00050517.
Lemma F_a9000 : fetch_word Plain.M.loaded_segments (0xa903c : word) = Some W_a9000.
Proof. vm_refl. Qed.
Lemma D_a9000 : decode_any W_a9000 = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9004 : bv 32 := 0x85c50913.
Lemma F_a9004 : fetch_word Plain.M.loaded_segments (0xa9040 : word) = Some W_a9004.
Proof. vm_refl. Qed.
Lemma D_a9004 : decode_any W_a9004 = Some (OpImm ALU_ADD 18 10 2140, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9008 : bv 32 := 0x00490413.
Lemma F_a9008 : fetch_word Plain.M.loaded_segments (0xa9044 : word) = Some W_a9008.
Proof. vm_refl. Qed.
Lemma D_a9008 : decode_any W_a9008 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a900c : bv 32 := 0x00040513.
Lemma F_a900c : fetch_word Plain.M.loaded_segments (0xa9048 : word) = Some W_a900c.
Proof. vm_refl. Qed.
Lemma D_a900c : decode_any W_a900c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9010 : bv 32 := 0x5bc110ef.
Lemma F_a9010 : fetch_word Plain.M.loaded_segments (0xa904c : word) = Some W_a9010.
Proof. vm_refl. Qed.
Lemma D_a9010 : decode_any W_a9010 = Some (Jal 1 71100, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9014 : bv 32 := 0x01093503.
Lemma F_a9014 : fetch_word Plain.M.loaded_segments (0xa9050 : word) = Some W_a9014.
Proof. vm_refl. Qed.
Lemma D_a9014 : decode_any W_a9014 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9018 : bv 32 := 0x06050863.
Lemma F_a9018 : fetch_word Plain.M.loaded_segments (0xa9054 : word) = Some W_a9018.
Proof. vm_refl. Qed.
Lemma D_a9018 : decode_any W_a9018 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a901c : bv 32 := 0x00892583.
Lemma F_a901c : fetch_word Plain.M.loaded_segments (0xa9058 : word) = Some W_a901c.
Proof. vm_refl. Qed.
Lemma D_a901c : decode_any W_a901c = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9020 : bv 32 := 0x0180006f.
Lemma F_a9020 : fetch_word Plain.M.loaded_segments (0xa905c : word) = Some W_a9020.
Proof. vm_refl. Qed.
Lemma D_a9020 : decode_any W_a9020 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9024 : bv 32 := 0x00053503.
Lemma F_a9024 : fetch_word Plain.M.loaded_segments (0xa9060 : word) = Some W_a9024.
Proof. vm_refl. Qed.
Lemma D_a9024 : decode_any W_a9024 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9028 : bv 32 := 0x02000593.
Lemma F_a9028 : fetch_word Plain.M.loaded_segments (0xa9064 : word) = Some W_a9028.
Proof. vm_refl. Qed.
Lemma D_a9028 : decode_any W_a9028 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a902c : bv 32 := 0x00b92423.
Lemma F_a902c : fetch_word Plain.M.loaded_segments (0xa9068 : word) = Some W_a902c.
Proof. vm_refl. Qed.
Lemma D_a902c : decode_any W_a902c = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9030 : bv 32 := 0x00a93823.
Lemma F_a9030 : fetch_word Plain.M.loaded_segments (0xa906c : word) = Some W_a9030.
Proof. vm_refl. Qed.
Lemma D_a9030 : decode_any W_a9030 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9034 : bv 32 := 0x04050a63.
Lemma F_a9034 : fetch_word Plain.M.loaded_segments (0xa9070 : word) = Some W_a9034.
Proof. vm_refl. Qed.
Lemma D_a9034 : decode_any W_a9034 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9038 : bv 32 := 0xfff5861b.
Lemma F_a9038 : fetch_word Plain.M.loaded_segments (0xa9074 : word) = Some W_a9038.
Proof. vm_refl. Qed.
Lemma D_a9038 : decode_any W_a9038 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a903c : bv 32 := 0x00c92423.
Lemma F_a903c : fetch_word Plain.M.loaded_segments (0xa9078 : word) = Some W_a903c.
Proof. vm_refl. Qed.
Lemma D_a903c : decode_any W_a903c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9040 : bv 32 := 0xfeb052e3.
Lemma F_a9040 : fetch_word Plain.M.loaded_segments (0xa907c : word) = Some W_a9040.
Proof. vm_refl. Qed.
Lemma D_a9040 : decode_any W_a9040 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9044 : bv 32 := 0x01093503.
Lemma F_a9044 : fetch_word Plain.M.loaded_segments (0xa9080 : word) = Some W_a9044.
Proof. vm_refl. Qed.
Lemma D_a9044 : decode_any W_a9044 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9048 : bv 32 := 0x00361613.
Lemma F_a9048 : fetch_word Plain.M.loaded_segments (0xa9084 : word) = Some W_a9048.
Proof. vm_refl. Qed.
Lemma D_a9048 : decode_any W_a9048 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a904c : bv 32 := 0x00c50533.
Lemma F_a904c : fetch_word Plain.M.loaded_segments (0xa9088 : word) = Some W_a904c.
Proof. vm_refl. Qed.
Lemma D_a904c : decode_any W_a904c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9050 : bv 32 := 0x00853983.
Lemma F_a9050 : fetch_word Plain.M.loaded_segments (0xa908c : word) = Some W_a9050.
Proof. vm_refl. Qed.
Lemma D_a9050 : decode_any W_a9050 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9054 : bv 32 := 0x10853483.
Lemma F_a9054 : fetch_word Plain.M.loaded_segments (0xa9090 : word) = Some W_a9054.
Proof. vm_refl. Qed.
Lemma D_a9054 : decode_any W_a9054 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9058 : bv 32 := 0x00040513.
Lemma F_a9058 : fetch_word Plain.M.loaded_segments (0xa9094 : word) = Some W_a9058.
Proof. vm_refl. Qed.
Lemma D_a9058 : decode_any W_a9058 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a905c : bv 32 := 0x7f8110ef.
Lemma F_a905c : fetch_word Plain.M.loaded_segments (0xa9098 : word) = Some W_a905c.
Proof. vm_refl. Qed.
Lemma D_a905c : decode_any W_a905c = Some (Jal 1 71672, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9060 : bv 32 := 0x00048513.
Lemma F_a9060 : fetch_word Plain.M.loaded_segments (0xa909c : word) = Some W_a9060.
Proof. vm_refl. Qed.
Lemma D_a9060 : decode_any W_a9060 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9064 : bv 32 := 0x000980e7.
Lemma F_a9064 : fetch_word Plain.M.loaded_segments (0xa90a0 : word) = Some W_a9064.
Proof. vm_refl. Qed.
Lemma D_a9064 : decode_any W_a9064 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9068 : bv 32 := 0x00040513.
Lemma F_a9068 : fetch_word Plain.M.loaded_segments (0xa90a4 : word) = Some W_a9068.
Proof. vm_refl. Qed.
Lemma D_a9068 : decode_any W_a9068 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a906c : bv 32 := 0x560110ef.
Lemma F_a906c : fetch_word Plain.M.loaded_segments (0xa90a8 : word) = Some W_a906c.
Proof. vm_refl. Qed.
Lemma D_a906c : decode_any W_a906c = Some (Jal 1 71008, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9070 : bv 32 := 0x00892503.
Lemma F_a9070 : fetch_word Plain.M.loaded_segments (0xa90ac : word) = Some W_a9070.
Proof. vm_refl. Qed.
Lemma D_a9070 : decode_any W_a9070 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9074 : bv 32 := 0xfff5061b.
Lemma F_a9074 : fetch_word Plain.M.loaded_segments (0xa90b0 : word) = Some W_a9074.
Proof. vm_refl. Qed.
Lemma D_a9074 : decode_any W_a9074 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9078 : bv 32 := 0x00c92423.
Lemma F_a9078 : fetch_word Plain.M.loaded_segments (0xa90b4 : word) = Some W_a9078.
Proof. vm_refl. Qed.
Lemma D_a9078 : decode_any W_a9078 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a907c : bv 32 := 0xfca044e3.
Lemma F_a907c : fetch_word Plain.M.loaded_segments (0xa90b8 : word) = Some W_a907c.
Proof. vm_refl. Qed.
Lemma D_a907c : decode_any W_a907c = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9080 : bv 32 := 0x01093503.
Lemma F_a9080 : fetch_word Plain.M.loaded_segments (0xa90bc : word) = Some W_a9080.
Proof. vm_refl. Qed.
Lemma D_a9080 : decode_any W_a9080 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9084 : bv 32 := 0xfa1ff06f.
Lemma F_a9084 : fetch_word Plain.M.loaded_segments (0xa90c0 : word) = Some W_a9084.
Proof. vm_refl. Qed.
Lemma D_a9084 : decode_any W_a9084 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9088 : bv 32 := 0x00100513.
Lemma F_a9088 : fetch_word Plain.M.loaded_segments (0xa90c4 : word) = Some W_a9088.
Proof. vm_refl. Qed.
Lemma D_a9088 : decode_any W_a9088 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a908c : bv 32 := 0x00a90023.
Lemma F_a908c : fetch_word Plain.M.loaded_segments (0xa90c8 : word) = Some W_a908c.
Proof. vm_refl. Qed.
Lemma D_a908c : decode_any W_a908c = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9090 : bv 32 := 0x00040513.
Lemma F_a9090 : fetch_word Plain.M.loaded_segments (0xa90cc : word) = Some W_a9090.
Proof. vm_refl. Qed.
Lemma D_a9090 : decode_any W_a9090 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9094 : bv 32 := 0x02813083.
Lemma F_a9094 : fetch_word Plain.M.loaded_segments (0xa90d0 : word) = Some W_a9094.
Proof. vm_refl. Qed.
Lemma D_a9094 : decode_any W_a9094 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a9098 : bv 32 := 0x02013403.
Lemma F_a9098 : fetch_word Plain.M.loaded_segments (0xa90d4 : word) = Some W_a9098.
Proof. vm_refl. Qed.
Lemma D_a9098 : decode_any W_a9098 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a909c : bv 32 := 0x01813483.
Lemma F_a909c : fetch_word Plain.M.loaded_segments (0xa90d8 : word) = Some W_a909c.
Proof. vm_refl. Qed.
Lemma D_a909c : decode_any W_a909c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a90a0 : bv 32 := 0x01013903.
Lemma F_a90a0 : fetch_word Plain.M.loaded_segments (0xa90dc : word) = Some W_a90a0.
Proof. vm_refl. Qed.
Lemma D_a90a0 : decode_any W_a90a0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a90a4 : bv 32 := 0x00813983.
Lemma F_a90a4 : fetch_word Plain.M.loaded_segments (0xa90e0 : word) = Some W_a90a4.
Proof. vm_refl. Qed.
Lemma D_a90a4 : decode_any W_a90a4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a90a8 : bv 32 := 0x03010113.
Lemma F_a90a8 : fetch_word Plain.M.loaded_segments (0xa90e4 : word) = Some W_a90a8.
Proof. vm_refl. Qed.
Lemma D_a90a8 : decode_any W_a90a8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a90ac : bv 32 := 0x7a81106f.
Lemma F_a90ac : fetch_word Plain.M.loaded_segments (0xa90e8 : word) = Some W_a90ac.
Proof. vm_refl. Qed.
Lemma D_a90ac : decode_any W_a90ac = Some (Jal 0 71592, 4%Z).
Proof. vm_refl. Qed.

Definition W_a90b0 : bv 32 := 0x00008067.
Lemma F_a90b0 : fetch_word Plain.M.loaded_segments (0xa90ec : word) = Some W_a90b0.
Proof. vm_refl. Qed.
Lemma D_a90b0 : decode_any W_a90b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r98734_98800.
Module Ns0_code_r988c8_988cc.
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

Definition W_a9244 : bv 32 := 0x00008067.
Lemma F_a9244 : fetch_word Plain.M.loaded_segments (0xa9280 : word) = Some W_a9244.
Proof. vm_refl. Qed.
Lemma D_a9244 : decode_any W_a9244 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r988c8_988cc.
Module Ns0_code_r99768_9976c.
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

Definition W_a9240 : bv 32 := 0x00050067.
Lemma F_a9240 : fetch_word Plain.M.loaded_segments (0xa927c : word) = Some W_a9240.
Proof. vm_refl. Qed.
Lemma D_a9240 : decode_any W_a9240 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r99768_9976c.
Module Ns0_code_ra9ec0_a9ecc.
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

Definition W_ba854 : bv 32 := 0x00052583.
Lemma F_ba854 : fetch_word Plain.M.loaded_segments (0xba890 : word) = Some W_ba854.
Proof. vm_refl. Qed.
Lemma D_ba854 : decode_any W_ba854 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ba858 : bv 32 := 0x0005c463.
Lemma F_ba858 : fetch_word Plain.M.loaded_segments (0xba894 : word) = Some W_ba858.
Proof. vm_refl. Qed.
Lemma D_ba858 : decode_any W_ba858 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ba85c : bv 32 := 0x00008067.
Lemma F_ba85c : fetch_word Plain.M.loaded_segments (0xba898 : word) = Some W_ba85c.
Proof. vm_refl. Qed.
Lemma D_ba85c : decode_any W_ba85c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_ra9ec0_a9ecc.
Module Ns0_code_r4e000_4f000.
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

Definition W_ae498 : bv 32 := 0xf9010113.
Lemma F_ae498 : fetch_word Plain.M.loaded_segments (0xae4d4 : word) = Some W_ae498.
Proof. vm_refl. Qed.
Lemma D_ae498 : decode_any W_ae498 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae49c : bv 32 := 0x06113423.
Lemma F_ae49c : fetch_word Plain.M.loaded_segments (0xae4d8 : word) = Some W_ae49c.
Proof. vm_refl. Qed.
Lemma D_ae49c : decode_any W_ae49c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4a0 : bv 32 := 0x06813023.
Lemma F_ae4a0 : fetch_word Plain.M.loaded_segments (0xae4dc : word) = Some W_ae4a0.
Proof. vm_refl. Qed.
Lemma D_ae4a0 : decode_any W_ae4a0 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4a4 : bv 32 := 0x04913c23.
Lemma F_ae4a4 : fetch_word Plain.M.loaded_segments (0xae4e0 : word) = Some W_ae4a4.
Proof. vm_refl. Qed.
Lemma D_ae4a4 : decode_any W_ae4a4 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4a8 : bv 32 := 0x05213823.
Lemma F_ae4a8 : fetch_word Plain.M.loaded_segments (0xae4e4 : word) = Some W_ae4a8.
Proof. vm_refl. Qed.
Lemma D_ae4a8 : decode_any W_ae4a8 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4ac : bv 32 := 0x05313423.
Lemma F_ae4ac : fetch_word Plain.M.loaded_segments (0xae4e8 : word) = Some W_ae4ac.
Proof. vm_refl. Qed.
Lemma D_ae4ac : decode_any W_ae4ac = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4b0 : bv 32 := 0x05413023.
Lemma F_ae4b0 : fetch_word Plain.M.loaded_segments (0xae4ec : word) = Some W_ae4b0.
Proof. vm_refl. Qed.
Lemma D_ae4b0 : decode_any W_ae4b0 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4b4 : bv 32 := 0x03513c23.
Lemma F_ae4b4 : fetch_word Plain.M.loaded_segments (0xae4f0 : word) = Some W_ae4b4.
Proof. vm_refl. Qed.
Lemma D_ae4b4 : decode_any W_ae4b4 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4b8 : bv 32 := 0x03613823.
Lemma F_ae4b8 : fetch_word Plain.M.loaded_segments (0xae4f4 : word) = Some W_ae4b8.
Proof. vm_refl. Qed.
Lemma D_ae4b8 : decode_any W_ae4b8 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4bc : bv 32 := 0x00060413.
Lemma F_ae4bc : fetch_word Plain.M.loaded_segments (0xae4f8 : word) = Some W_ae4bc.
Proof. vm_refl. Qed.
Lemma D_ae4bc : decode_any W_ae4bc = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4c0 : bv 32 := 0x00050493.
Lemma F_ae4c0 : fetch_word Plain.M.loaded_segments (0xae4fc : word) = Some W_ae4c0.
Proof. vm_refl. Qed.
Lemma D_ae4c0 : decode_any W_ae4c0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4c4 : bv 32 := 0x00017517.
Lemma F_ae4c4 : fetch_word Plain.M.loaded_segments (0xae500 : word) = Some W_ae4c4.
Proof. vm_refl. Qed.
Lemma D_ae4c4 : decode_any W_ae4c4 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4c8 : bv 32 := 0x5b853a83.
Lemma F_ae4c8 : fetch_word Plain.M.loaded_segments (0xae504 : word) = Some W_ae4c8.
Proof. vm_refl. Qed.
Lemma D_ae4c8 : decode_any W_ae4c8 = Some (Load SZ8 true 21 10 1464, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4cc : bv 32 := 0x000ab503.
Lemma F_ae4cc : fetch_word Plain.M.loaded_segments (0xae508 : word) = Some W_ae4cc.
Proof. vm_refl. Qed.
Lemma D_ae4cc : decode_any W_ae4cc = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4d0 : bv 32 := 0x02a13423.
Lemma F_ae4d0 : fetch_word Plain.M.loaded_segments (0xae50c : word) = Some W_ae4d0.
Proof. vm_refl. Qed.
Lemma D_ae4d0 : decode_any W_ae4d0 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4d4 : bv 32 := 0x0284b503.
Lemma F_ae4d4 : fetch_word Plain.M.loaded_segments (0xae510 : word) = Some W_ae4d4.
Proof. vm_refl. Qed.
Lemma D_ae4d4 : decode_any W_ae4d4 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4d8 : bv 32 := 0x0384b603.
Lemma F_ae4d8 : fetch_word Plain.M.loaded_segments (0xae514 : word) = Some W_ae4d8.
Proof. vm_refl. Qed.
Lemma D_ae4d8 : decode_any W_ae4d8 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4dc : bv 32 := 0x40c50b33.
Lemma F_ae4dc : fetch_word Plain.M.loaded_segments (0xae518 : word) = Some W_ae4dc.
Proof. vm_refl. Qed.
Lemma D_ae4dc : decode_any W_ae4dc = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4e0 : bv 32 := 0x00c546b3.
Lemma F_ae4e0 : fetch_word Plain.M.loaded_segments (0xae51c : word) = Some W_ae4e0.
Proof. vm_refl. Qed.
Lemma D_ae4e0 : decode_any W_ae4e0 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4e4 : bv 32 := 0x00c13423.
Lemma F_ae4e4 : fetch_word Plain.M.loaded_segments (0xae520 : word) = Some W_ae4e4.
Proof. vm_refl. Qed.
Lemma D_ae4e4 : decode_any W_ae4e4 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4e8 : bv 32 := 0x01613823.
Lemma F_ae4e8 : fetch_word Plain.M.loaded_segments (0xae524 : word) = Some W_ae4e8.
Proof. vm_refl. Qed.
Lemma D_ae4e8 : decode_any W_ae4e8 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4ec : bv 32 := 0x00b13c23.
Lemma F_ae4ec : fetch_word Plain.M.loaded_segments (0xae528 : word) = Some W_ae4ec.
Proof. vm_refl. Qed.
Lemma D_ae4ec : decode_any W_ae4ec = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4f0 : bv 32 := 0x02813023.
Lemma F_ae4f0 : fetch_word Plain.M.loaded_segments (0xae52c : word) = Some W_ae4f0.
Proof. vm_refl. Qed.
Lemma D_ae4f0 : decode_any W_ae4f0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4f4 : bv 32 := 0x008b0b33.
Lemma F_ae4f4 : fetch_word Plain.M.loaded_segments (0xae530 : word) = Some W_ae4f4.
Proof. vm_refl. Qed.
Lemma D_ae4f4 : decode_any W_ae4f4 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4f8 : bv 32 := 0x00d03933.
Lemma F_ae4f8 : fetch_word Plain.M.loaded_segments (0xae534 : word) = Some W_ae4f8.
Proof. vm_refl. Qed.
Lemma D_ae4f8 : decode_any W_ae4f8 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae4fc : bv 32 := 0x00c50663.
Lemma F_ae4fc : fetch_word Plain.M.loaded_segments (0xae538 : word) = Some W_ae4fc.
Proof. vm_refl. Qed.
Lemma D_ae4fc : decode_any W_ae4fc = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae500 : bv 32 := 0x00810993.
Lemma F_ae500 : fetch_word Plain.M.loaded_segments (0xae53c : word) = Some W_ae500.
Proof. vm_refl. Qed.
Lemma D_ae500 : decode_any W_ae500 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae504 : bv 32 := 0x0080006f.
Lemma F_ae504 : fetch_word Plain.M.loaded_segments (0xae540 : word) = Some W_ae504.
Proof. vm_refl. Qed.
Lemma D_ae504 : decode_any W_ae504 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae508 : bv 32 := 0x01810993.
Lemma F_ae508 : fetch_word Plain.M.loaded_segments (0xae544 : word) = Some W_ae508.
Proof. vm_refl. Qed.
Lemma D_ae508 : decode_any W_ae508 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae50c : bv 32 := 0x0784a503.
Lemma F_ae50c : fetch_word Plain.M.loaded_segments (0xae548 : word) = Some W_ae50c.
Proof. vm_refl. Qed.
Lemma D_ae50c : decode_any W_ae50c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae510 : bv 32 := 0x00190913.
Lemma F_ae510 : fetch_word Plain.M.loaded_segments (0xae54c : word) = Some W_ae510.
Proof. vm_refl. Qed.
Lemma D_ae510 : decode_any W_ae510 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae514 : bv 32 := 0x04200893.
Lemma F_ae514 : fetch_word Plain.M.loaded_segments (0xae550 : word) = Some W_ae514.
Proof. vm_refl. Qed.
Lemma D_ae514 : decode_any W_ae514 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae518 : bv 32 := 0x00098593.
Lemma F_ae518 : fetch_word Plain.M.loaded_segments (0xae554 : word) = Some W_ae518.
Proof. vm_refl. Qed.
Lemma D_ae518 : decode_any W_ae518 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae51c : bv 32 := 0x00090613.
Lemma F_ae51c : fetch_word Plain.M.loaded_segments (0xae558 : word) = Some W_ae51c.
Proof. vm_refl. Qed.
Lemma D_ae51c : decode_any W_ae51c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae520 : bv 32 := 0x00000073.
Lemma F_ae520 : fetch_word Plain.M.loaded_segments (0xae55c : word) = Some W_ae520.
Proof. vm_refl. Qed.
Lemma D_ae520 : decode_any W_ae520 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ae520 : is_ecall W_ae520 = true.
Proof. reflexivity. Qed.

Definition W_ae524 : bv 32 := 0xf31fa0ef.
Lemma F_ae524 : fetch_word Plain.M.loaded_segments (0xae560 : word) = Some W_ae524.
Proof. vm_refl. Qed.
Lemma D_ae524 : decode_any W_ae524 = Some (Jal 1 2076464, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae528 : bv 32 := 0x09651863.
Lemma F_ae528 : fetch_word Plain.M.loaded_segments (0xae564 : word) = Some W_ae528.
Proof. vm_refl. Qed.
Lemma D_ae528 : decode_any W_ae528 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae52c : bv 32 := 0x0584b503.
Lemma F_ae52c : fetch_word Plain.M.loaded_segments (0xae568 : word) = Some W_ae52c.
Proof. vm_refl. Qed.
Lemma D_ae52c : decode_any W_ae52c = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae530 : bv 32 := 0x0604b583.
Lemma F_ae530 : fetch_word Plain.M.loaded_segments (0xae56c : word) = Some W_ae530.
Proof. vm_refl. Qed.
Lemma D_ae530 : decode_any W_ae530 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae534 : bv 32 := 0x00b505b3.
Lemma F_ae534 : fetch_word Plain.M.loaded_segments (0xae570 : word) = Some W_ae534.
Proof. vm_refl. Qed.
Lemma D_ae534 : decode_any W_ae534 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae538 : bv 32 := 0x02b4b023.
Lemma F_ae538 : fetch_word Plain.M.loaded_segments (0xae574 : word) = Some W_ae538.
Proof. vm_refl. Qed.
Lemma D_ae538 : decode_any W_ae538 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae53c : bv 32 := 0x02a4b423.
Lemma F_ae53c : fetch_word Plain.M.loaded_segments (0xae578 : word) = Some W_ae53c.
Proof. vm_refl. Qed.
Lemma D_ae53c : decode_any W_ae53c = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae540 : bv 32 := 0x02a4bc23.
Lemma F_ae540 : fetch_word Plain.M.loaded_segments (0xae57c : word) = Some W_ae540.
Proof. vm_refl. Qed.
Lemma D_ae540 : decode_any W_ae540 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae544 : bv 32 := 0x00040513.
Lemma F_ae544 : fetch_word Plain.M.loaded_segments (0xae580 : word) = Some W_ae544.
Proof. vm_refl. Qed.
Lemma D_ae544 : decode_any W_ae544 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae548 : bv 32 := 0x000ab583.
Lemma F_ae548 : fetch_word Plain.M.loaded_segments (0xae584 : word) = Some W_ae548.
Proof. vm_refl. Qed.
Lemma D_ae548 : decode_any W_ae548 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae54c : bv 32 := 0x02813603.
Lemma F_ae54c : fetch_word Plain.M.loaded_segments (0xae588 : word) = Some W_ae54c.
Proof. vm_refl. Qed.
Lemma D_ae54c : decode_any W_ae54c = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae550 : bv 32 := 0x0cc59a63.
Lemma F_ae550 : fetch_word Plain.M.loaded_segments (0xae58c : word) = Some W_ae550.
Proof. vm_refl. Qed.
Lemma D_ae550 : decode_any W_ae550 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae554 : bv 32 := 0x06813083.
Lemma F_ae554 : fetch_word Plain.M.loaded_segments (0xae590 : word) = Some W_ae554.
Proof. vm_refl. Qed.
Lemma D_ae554 : decode_any W_ae554 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae558 : bv 32 := 0x06013403.
Lemma F_ae558 : fetch_word Plain.M.loaded_segments (0xae594 : word) = Some W_ae558.
Proof. vm_refl. Qed.
Lemma D_ae558 : decode_any W_ae558 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae55c : bv 32 := 0x05813483.
Lemma F_ae55c : fetch_word Plain.M.loaded_segments (0xae598 : word) = Some W_ae55c.
Proof. vm_refl. Qed.
Lemma D_ae55c : decode_any W_ae55c = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae560 : bv 32 := 0x05013903.
Lemma F_ae560 : fetch_word Plain.M.loaded_segments (0xae59c : word) = Some W_ae560.
Proof. vm_refl. Qed.
Lemma D_ae560 : decode_any W_ae560 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae564 : bv 32 := 0x04813983.
Lemma F_ae564 : fetch_word Plain.M.loaded_segments (0xae5a0 : word) = Some W_ae564.
Proof. vm_refl. Qed.
Lemma D_ae564 : decode_any W_ae564 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae568 : bv 32 := 0x04013a03.
Lemma F_ae568 : fetch_word Plain.M.loaded_segments (0xae5a4 : word) = Some W_ae568.
Proof. vm_refl. Qed.
Lemma D_ae568 : decode_any W_ae568 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae56c : bv 32 := 0x03813a83.
Lemma F_ae56c : fetch_word Plain.M.loaded_segments (0xae5a8 : word) = Some W_ae56c.
Proof. vm_refl. Qed.
Lemma D_ae56c : decode_any W_ae56c = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae570 : bv 32 := 0x03013b03.
Lemma F_ae570 : fetch_word Plain.M.loaded_segments (0xae5ac : word) = Some W_ae570.
Proof. vm_refl. Qed.
Lemma D_ae570 : decode_any W_ae570 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae574 : bv 32 := 0x07010113.
Lemma F_ae574 : fetch_word Plain.M.loaded_segments (0xae5b0 : word) = Some W_ae574.
Proof. vm_refl. Qed.
Lemma D_ae574 : decode_any W_ae574 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae578 : bv 32 := 0x00008067.
Lemma F_ae578 : fetch_word Plain.M.loaded_segments (0xae5b4 : word) = Some W_ae578.
Proof. vm_refl. Qed.
Lemma D_ae578 : decode_any W_ae578 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae57c : bv 32 := 0x00800713.
Lemma F_ae57c : fetch_word Plain.M.loaded_segments (0xae5b8 : word) = Some W_ae57c.
Proof. vm_refl. Qed.
Lemma D_ae57c : decode_any W_ae57c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae580 : bv 32 := 0x000a0593.
Lemma F_ae580 : fetch_word Plain.M.loaded_segments (0xae5bc : word) = Some W_ae580.
Proof. vm_refl. Qed.
Lemma D_ae580 : decode_any W_ae580 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae584 : bv 32 := 0x00e98733.
Lemma F_ae584 : fetch_word Plain.M.loaded_segments (0xae5c0 : word) = Some W_ae584.
Proof. vm_refl. Qed.
Lemma D_ae584 : decode_any W_ae584 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae588 : bv 32 := 0x00073783.
Lemma F_ae588 : fetch_word Plain.M.loaded_segments (0xae5c4 : word) = Some W_ae588.
Proof. vm_refl. Qed.
Lemma D_ae588 : decode_any W_ae588 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae58c : bv 32 := 0x40ab0b33.
Lemma F_ae58c : fetch_word Plain.M.loaded_segments (0xae5c8 : word) = Some W_ae58c.
Proof. vm_refl. Qed.
Lemma D_ae58c : decode_any W_ae58c = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae590 : bv 32 := 0x0784a503.
Lemma F_ae590 : fetch_word Plain.M.loaded_segments (0xae5cc : word) = Some W_ae590.
Proof. vm_refl. Qed.
Lemma D_ae590 : decode_any W_ae590 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae594 : bv 32 := 0x40c9093b.
Lemma F_ae594 : fetch_word Plain.M.loaded_segments (0xae5d0 : word) = Some W_ae594.
Proof. vm_refl. Qed.
Lemma D_ae594 : decode_any W_ae594 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae598 : bv 32 := 0x40d787b3.
Lemma F_ae598 : fetch_word Plain.M.loaded_segments (0xae5d4 : word) = Some W_ae598.
Proof. vm_refl. Qed.
Lemma D_ae598 : decode_any W_ae598 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae59c : bv 32 := 0x00f73023.
Lemma F_ae59c : fetch_word Plain.M.loaded_segments (0xae5d8 : word) = Some W_ae59c.
Proof. vm_refl. Qed.
Lemma D_ae59c : decode_any W_ae59c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5a0 : bv 32 := 0x04200893.
Lemma F_ae5a0 : fetch_word Plain.M.loaded_segments (0xae5dc : word) = Some W_ae5a0.
Proof. vm_refl. Qed.
Lemma D_ae5a0 : decode_any W_ae5a0 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5a4 : bv 32 := 0x00090613.
Lemma F_ae5a4 : fetch_word Plain.M.loaded_segments (0xae5e0 : word) = Some W_ae5a4.
Proof. vm_refl. Qed.
Lemma D_ae5a4 : decode_any W_ae5a4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5a8 : bv 32 := 0x00000073.
Lemma F_ae5a8 : fetch_word Plain.M.loaded_segments (0xae5e4 : word) = Some W_ae5a8.
Proof. vm_refl. Qed.
Lemma D_ae5a8 : decode_any W_ae5a8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ae5a8 : is_ecall W_ae5a8 = true.
Proof. reflexivity. Qed.

Definition W_ae5ac : bv 32 := 0xea9fa0ef.
Lemma F_ae5ac : fetch_word Plain.M.loaded_segments (0xae5e8 : word) = Some W_ae5ac.
Proof. vm_refl. Qed.
Lemma D_ae5ac : decode_any W_ae5ac = Some (Jal 1 2076328, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5b0 : bv 32 := 0x000a0993.
Lemma F_ae5b0 : fetch_word Plain.M.loaded_segments (0xae5ec : word) = Some W_ae5b0.
Proof. vm_refl. Qed.
Lemma D_ae5b0 : decode_any W_ae5b0 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5b4 : bv 32 := 0xf7650ce3.
Lemma F_ae5b4 : fetch_word Plain.M.loaded_segments (0xae5f0 : word) = Some W_ae5b4.
Proof. vm_refl. Qed.
Lemma D_ae5b4 : decode_any W_ae5b4 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5b8 : bv 32 := 0x02054c63.
Lemma F_ae5b8 : fetch_word Plain.M.loaded_segments (0xae5f4 : word) = Some W_ae5b8.
Proof. vm_refl. Qed.
Lemma D_ae5b8 : decode_any W_ae5b8 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5bc : bv 32 := 0x0089b583.
Lemma F_ae5bc : fetch_word Plain.M.loaded_segments (0xae5f8 : word) = Some W_ae5bc.
Proof. vm_refl. Qed.
Lemma D_ae5bc : decode_any W_ae5bc = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5c0 : bv 32 := 0x00a5b633.
Lemma F_ae5c0 : fetch_word Plain.M.loaded_segments (0xae5fc : word) = Some W_ae5c0.
Proof. vm_refl. Qed.
Lemma D_ae5c0 : decode_any W_ae5c0 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5c4 : bv 32 := 0x00461a13.
Lemma F_ae5c4 : fetch_word Plain.M.loaded_segments (0xae600 : word) = Some W_ae5c4.
Proof. vm_refl. Qed.
Lemma D_ae5c4 : decode_any W_ae5c4 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5c8 : bv 32 := 0x01498a33.
Lemma F_ae5c8 : fetch_word Plain.M.loaded_segments (0xae604 : word) = Some W_ae5c8.
Proof. vm_refl. Qed.
Lemma D_ae5c8 : decode_any W_ae5c8 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5cc : bv 32 := 0x000a3703.
Lemma F_ae5cc : fetch_word Plain.M.loaded_segments (0xae608 : word) = Some W_ae5cc.
Proof. vm_refl. Qed.
Lemma D_ae5cc : decode_any W_ae5cc = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5d0 : bv 32 := 0x40c006b3.
Lemma F_ae5d0 : fetch_word Plain.M.loaded_segments (0xae60c : word) = Some W_ae5d0.
Proof. vm_refl. Qed.
Lemma D_ae5d0 : decode_any W_ae5d0 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5d4 : bv 32 := 0x00b6f6b3.
Lemma F_ae5d4 : fetch_word Plain.M.loaded_segments (0xae610 : word) = Some W_ae5d4.
Proof. vm_refl. Qed.
Lemma D_ae5d4 : decode_any W_ae5d4 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5d8 : bv 32 := 0x40d506b3.
Lemma F_ae5d8 : fetch_word Plain.M.loaded_segments (0xae614 : word) = Some W_ae5d8.
Proof. vm_refl. Qed.
Lemma D_ae5d8 : decode_any W_ae5d8 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5dc : bv 32 := 0x00d70733.
Lemma F_ae5dc : fetch_word Plain.M.loaded_segments (0xae618 : word) = Some W_ae5dc.
Proof. vm_refl. Qed.
Lemma D_ae5dc : decode_any W_ae5dc = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5e0 : bv 32 := 0x00ea3023.
Lemma F_ae5e0 : fetch_word Plain.M.loaded_segments (0xae61c : word) = Some W_ae5e0.
Proof. vm_refl. Qed.
Lemma D_ae5e0 : decode_any W_ae5e0 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5e4 : bv 32 := 0xf8a5fce3.
Lemma F_ae5e4 : fetch_word Plain.M.loaded_segments (0xae620 : word) = Some W_ae5e4.
Proof. vm_refl. Qed.
Lemma D_ae5e4 : decode_any W_ae5e4 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5e8 : bv 32 := 0x01800713.
Lemma F_ae5e8 : fetch_word Plain.M.loaded_segments (0xae624 : word) = Some W_ae5e8.
Proof. vm_refl. Qed.
Lemma D_ae5e8 : decode_any W_ae5e8 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae5ec : bv 32 := 0xf95ff06f.
Lemma F_ae5ec : fetch_word Plain.M.loaded_segments (0xae628 : word) = Some W_ae5ec.
Proof. vm_refl. Qed.
Lemma D_ae5ec : decode_any W_ae5ec = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

Definition W_ae630 : bv 32 := 0x00008067.
Lemma F_ae630 : fetch_word Plain.M.loaded_segments (0xae66c : word) = Some W_ae630.
Proof. vm_refl. Qed.
Lemma D_ae630 : decode_any W_ae630 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed60 : bv 32 := 0xff010113.
Lemma F_aed60 : fetch_word Plain.M.loaded_segments (0xaed9c : word) = Some W_aed60.
Proof. vm_refl. Qed.
Lemma D_aed60 : decode_any W_aed60 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed64 : bv 32 := 0x00113423.
Lemma F_aed64 : fetch_word Plain.M.loaded_segments (0xaeda0 : word) = Some W_aed64.
Proof. vm_refl. Qed.
Lemma D_aed64 : decode_any W_aed64 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed68 : bv 32 := 0x00813023.
Lemma F_aed68 : fetch_word Plain.M.loaded_segments (0xaeda4 : word) = Some W_aed68.
Proof. vm_refl. Qed.
Lemma D_aed68 : decode_any W_aed68 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed6c : bv 32 := 0x0004a517.
Lemma F_aed6c : fetch_word Plain.M.loaded_segments (0xaeda8 : word) = Some W_aed6c.
Proof. vm_refl. Qed.
Lemma D_aed6c : decode_any W_aed6c = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed70 : bv 32 := 0x27850413.
Lemma F_aed70 : fetch_word Plain.M.loaded_segments (0xaedac : word) = Some W_aed70.
Proof. vm_refl. Qed.
Lemma D_aed70 : decode_any W_aed70 = Some (OpImm ALU_ADD 8 10 632, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed74 : bv 32 := 0x00040513.
Lemma F_aed74 : fetch_word Plain.M.loaded_segments (0xaedb0 : word) = Some W_aed74.
Proof. vm_refl. Qed.
Lemma D_aed74 : decode_any W_aed74 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed78 : bv 32 := 0x0550b0ef.
Lemma F_aed78 : fetch_word Plain.M.loaded_segments (0xaedb4 : word) = Some W_aed78.
Proof. vm_refl. Qed.
Lemma D_aed78 : decode_any W_aed78 = Some (Jal 1 47188, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed7c : bv 32 := 0x00840513.
Lemma F_aed7c : fetch_word Plain.M.loaded_segments (0xaedb8 : word) = Some W_aed7c.
Proof. vm_refl. Qed.
Lemma D_aed7c : decode_any W_aed7c = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed80 : bv 32 := 0x00813083.
Lemma F_aed80 : fetch_word Plain.M.loaded_segments (0xaedbc : word) = Some W_aed80.
Proof. vm_refl. Qed.
Lemma D_aed80 : decode_any W_aed80 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed84 : bv 32 := 0x00013403.
Lemma F_aed84 : fetch_word Plain.M.loaded_segments (0xaedc0 : word) = Some W_aed84.
Proof. vm_refl. Qed.
Lemma D_aed84 : decode_any W_aed84 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed88 : bv 32 := 0x01010113.
Lemma F_aed88 : fetch_word Plain.M.loaded_segments (0xaedc4 : word) = Some W_aed88.
Proof. vm_refl. Qed.
Lemma D_aed88 : decode_any W_aed88 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_aed8c : bv 32 := 0x00008067.
Lemma F_aed8c : fetch_word Plain.M.loaded_segments (0xaedc8 : word) = Some W_aed8c.
Proof. vm_refl. Qed.
Lemma D_aed8c : decode_any W_aed8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r4e000_4f000.
Module Ns0_code_r4a000_4b000.
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

Definition W_a891c : bv 32 := 0x00008067.
Lemma F_a891c : fetch_word Plain.M.loaded_segments (0xa8964 : word) = Some W_a891c.
Proof. vm_refl. Qed.
Lemma D_a891c : decode_any W_a891c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8920 : bv 32 := 0xe8010113.
Lemma F_a8920 : fetch_word Plain.M.loaded_segments (0xa8968 : word) = Some W_a8920.
Proof. vm_refl. Qed.
Lemma D_a8920 : decode_any W_a8920 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8924 : bv 32 := 0x16113c23.
Lemma F_a8924 : fetch_word Plain.M.loaded_segments (0xa896c : word) = Some W_a8924.
Proof. vm_refl. Qed.
Lemma D_a8924 : decode_any W_a8924 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8928 : bv 32 := 0x16813823.
Lemma F_a8928 : fetch_word Plain.M.loaded_segments (0xa8970 : word) = Some W_a8928.
Proof. vm_refl. Qed.
Lemma D_a8928 : decode_any W_a8928 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_a892c : bv 32 := 0x16913423.
Lemma F_a892c : fetch_word Plain.M.loaded_segments (0xa8974 : word) = Some W_a892c.
Proof. vm_refl. Qed.
Lemma D_a892c : decode_any W_a892c = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8930 : bv 32 := 0x17213023.
Lemma F_a8930 : fetch_word Plain.M.loaded_segments (0xa8978 : word) = Some W_a8930.
Proof. vm_refl. Qed.
Lemma D_a8930 : decode_any W_a8930 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8934 : bv 32 := 0x00058413.
Lemma F_a8934 : fetch_word Plain.M.loaded_segments (0xa897c : word) = Some W_a8934.
Proof. vm_refl. Qed.
Lemma D_a8934 : decode_any W_a8934 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8938 : bv 32 := 0x00050493.
Lemma F_a8938 : fetch_word Plain.M.loaded_segments (0xa8980 : word) = Some W_a8938.
Proof. vm_refl. Qed.
Lemma D_a8938 : decode_any W_a8938 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a893c : bv 32 := 0x03010513.
Lemma F_a893c : fetch_word Plain.M.loaded_segments (0xa8984 : word) = Some W_a893c.
Proof. vm_refl. Qed.
Lemma D_a893c : decode_any W_a893c = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8940 : bv 32 := 0x13000613.
Lemma F_a8940 : fetch_word Plain.M.loaded_segments (0xa8988 : word) = Some W_a8940.
Proof. vm_refl. Qed.
Lemma D_a8940 : decode_any W_a8940 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8944 : bv 32 := 0x00000593.
Lemma F_a8944 : fetch_word Plain.M.loaded_segments (0xa898c : word) = Some W_a8944.
Proof. vm_refl. Qed.
Lemma D_a8944 : decode_any W_a8944 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8948 : bv 32 := 0x568110ef.
Lemma F_a8948 : fetch_word Plain.M.loaded_segments (0xa8990 : word) = Some W_a8948.
Proof. vm_refl. Qed.
Lemma D_a8948 : decode_any W_a8948 = Some (Jal 1 71016, 4%Z).
Proof. vm_refl. Qed.

Definition W_a894c : bv 32 := 0x0001d517.
Lemma F_a894c : fetch_word Plain.M.loaded_segments (0xa8994 : word) = Some W_a894c.
Proof. vm_refl. Qed.
Lemma D_a894c : decode_any W_a894c = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8950 : bv 32 := 0x0fc53503.
Lemma F_a8950 : fetch_word Plain.M.loaded_segments (0xa8998 : word) = Some W_a8950.
Proof. vm_refl. Qed.
Lemma D_a8950 : decode_any W_a8950 = Some (Load SZ8 true 10 10 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8954 : bv 32 := 0x00953023.
Lemma F_a8954 : fetch_word Plain.M.loaded_segments (0xa899c : word) = Some W_a8954.
Proof. vm_refl. Qed.
Lemma D_a8954 : decode_any W_a8954 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8958 : bv 32 := 0x0004b503.
Lemma F_a8958 : fetch_word Plain.M.loaded_segments (0xa89a0 : word) = Some W_a8958.
Proof. vm_refl. Qed.
Lemma D_a8958 : decode_any W_a8958 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a895c : bv 32 := 0x00848493.
Lemma F_a895c : fetch_word Plain.M.loaded_segments (0xa89a4 : word) = Some W_a895c.
Proof. vm_refl. Qed.
Lemma D_a895c : decode_any W_a895c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8960 : bv 32 := 0xfe051ce3.
Lemma F_a8960 : fetch_word Plain.M.loaded_segments (0xa89a8 : word) = Some W_a8960.
Proof. vm_refl. Qed.
Lemma D_a8960 : decode_any W_a8960 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8964 : bv 32 := 0x00050517.
Lemma F_a8964 : fetch_word Plain.M.loaded_segments (0xa89ac : word) = Some W_a8964.
Proof. vm_refl. Qed.
Lemma D_a8964 : decode_any W_a8964 = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8968 : bv 32 := 0x13450913.
Lemma F_a8968 : fetch_word Plain.M.loaded_segments (0xa89b0 : word) = Some W_a8968.
Proof. vm_refl. Qed.
Lemma D_a8968 : decode_any W_a8968 = Some (OpImm ALU_ADD 18 10 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_a896c : bv 32 := 0x00993423.
Lemma F_a896c : fetch_word Plain.M.loaded_segments (0xa89b4 : word) = Some W_a896c.
Proof. vm_refl. Qed.
Lemma D_a896c : decode_any W_a896c = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8970 : bv 32 := 0x0004b583.
Lemma F_a8970 : fetch_word Plain.M.loaded_segments (0xa89b8 : word) = Some W_a8970.
Proof. vm_refl. Qed.
Lemma D_a8970 : decode_any W_a8970 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8974 : bv 32 := 0x04058c63.
Lemma F_a8974 : fetch_word Plain.M.loaded_segments (0xa89bc : word) = Some W_a8974.
Proof. vm_refl. Qed.
Lemma D_a8974 : decode_any W_a8974 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8978 : bv 32 := 0x01048493.
Lemma F_a8978 : fetch_word Plain.M.loaded_segments (0xa89c0 : word) = Some W_a8978.
Proof. vm_refl. Qed.
Lemma D_a8978 : decode_any W_a8978 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a897c : bv 32 := 0x02500513.
Lemma F_a897c : fetch_word Plain.M.loaded_segments (0xa89c4 : word) = Some W_a897c.
Proof. vm_refl. Qed.
Lemma D_a897c : decode_any W_a897c = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8980 : bv 32 := 0x03010613.
Lemma F_a8980 : fetch_word Plain.M.loaded_segments (0xa89c8 : word) = Some W_a8980.
Proof. vm_refl. Qed.
Lemma D_a8980 : decode_any W_a8980 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8984 : bv 32 := 0x0100006f.
Lemma F_a8984 : fetch_word Plain.M.loaded_segments (0xa89cc : word) = Some W_a8984.
Proof. vm_refl. Qed.
Lemma D_a8984 : decode_any W_a8984 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8988 : bv 32 := 0x0004b583.
Lemma F_a8988 : fetch_word Plain.M.loaded_segments (0xa89d0 : word) = Some W_a8988.
Proof. vm_refl. Qed.
Lemma D_a8988 : decode_any W_a8988 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a898c : bv 32 := 0x01048493.
Lemma F_a898c : fetch_word Plain.M.loaded_segments (0xa89d4 : word) = Some W_a898c.
Proof. vm_refl. Qed.
Lemma D_a898c : decode_any W_a898c = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8990 : bv 32 := 0x00058e63.
Lemma F_a8990 : fetch_word Plain.M.loaded_segments (0xa89d8 : word) = Some W_a8990.
Proof. vm_refl. Qed.
Lemma D_a8990 : decode_any W_a8990 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8994 : bv 32 := 0xfeb56ae3.
Lemma F_a8994 : fetch_word Plain.M.loaded_segments (0xa89dc : word) = Some W_a8994.
Proof. vm_refl. Qed.
Lemma D_a8994 : decode_any W_a8994 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8998 : bv 32 := 0xff84b683.
Lemma F_a8998 : fetch_word Plain.M.loaded_segments (0xa89e0 : word) = Some W_a8998.
Proof. vm_refl. Qed.
Lemma D_a8998 : decode_any W_a8998 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a899c : bv 32 := 0x00359593.
Lemma F_a899c : fetch_word Plain.M.loaded_segments (0xa89e4 : word) = Some W_a899c.
Proof. vm_refl. Qed.
Lemma D_a899c : decode_any W_a899c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89a0 : bv 32 := 0x00b605b3.
Lemma F_a89a0 : fetch_word Plain.M.loaded_segments (0xa89e8 : word) = Some W_a89a0.
Proof. vm_refl. Qed.
Lemma D_a89a0 : decode_any W_a89a0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89a4 : bv 32 := 0x00d5b023.
Lemma F_a89a4 : fetch_word Plain.M.loaded_segments (0xa89ec : word) = Some W_a89a4.
Proof. vm_refl. Qed.
Lemma D_a89a4 : decode_any W_a89a4 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89a8 : bv 32 := 0xfe1ff06f.
Lemma F_a89a8 : fetch_word Plain.M.loaded_segments (0xa89f0 : word) = Some W_a89a8.
Proof. vm_refl. Qed.
Lemma D_a89a8 : decode_any W_a89a8 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89ac : bv 32 := 0x0b013583.
Lemma F_a89ac : fetch_word Plain.M.loaded_segments (0xa89f4 : word) = Some W_a89ac.
Proof. vm_refl. Qed.
Lemma D_a89ac : decode_any W_a89ac = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89b0 : bv 32 := 0x13013503.
Lemma F_a89b0 : fetch_word Plain.M.loaded_segments (0xa89f8 : word) = Some W_a89b0.
Proof. vm_refl. Qed.
Lemma D_a89b0 : decode_any W_a89b0 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89b4 : bv 32 := 0x00050617.
Lemma F_a89b4 : fetch_word Plain.M.loaded_segments (0xa89fc : word) = Some W_a89b4.
Proof. vm_refl. Qed.
Lemma D_a89b4 : decode_any W_a89b4 = Some (Auipc 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89b8 : bv 32 := 0x14b63623.
Lemma F_a89b8 : fetch_word Plain.M.loaded_segments (0xa8a00 : word) = Some W_a89b8.
Proof. vm_refl. Qed.
Lemma D_a89b8 : decode_any W_a89b8 = Some (Store SZ8 12 11 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89bc : bv 32 := 0x00050c63.
Lemma F_a89bc : fetch_word Plain.M.loaded_segments (0xa8a04 : word) = Some W_a89bc.
Proof. vm_refl. Qed.
Lemma D_a89bc : decode_any W_a89bc = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89d4 : bv 32 := 0x06013503.
Lemma F_a89d4 : fetch_word Plain.M.loaded_segments (0xa8a1c : word) = Some W_a89d4.
Proof. vm_refl. Qed.
Lemma D_a89d4 : decode_any W_a89d4 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89d8 : bv 32 := 0x02a93823.
Lemma F_a89d8 : fetch_word Plain.M.loaded_segments (0xa8a20 : word) = Some W_a89d8.
Proof. vm_refl. Qed.
Lemma D_a89d8 : decode_any W_a89d8 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89dc : bv 32 := 0x00041463.
Lemma F_a89dc : fetch_word Plain.M.loaded_segments (0xa8a24 : word) = Some W_a89dc.
Proof. vm_refl. Qed.
Lemma D_a89dc : decode_any W_a89dc = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89e4 : bv 32 := 0x00041663.
Lemma F_a89e4 : fetch_word Plain.M.loaded_segments (0xa8a2c : word) = Some W_a89e4.
Proof. vm_refl. Qed.
Lemma D_a89e4 : decode_any W_a89e4 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89f0 : bv 32 := 0x0001d517.
Lemma F_a89f0 : fetch_word Plain.M.loaded_segments (0xa8a38 : word) = Some W_a89f0.
Proof. vm_refl. Qed.
Lemma D_a89f0 : decode_any W_a89f0 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89f4 : bv 32 := 0x06053583.
Lemma F_a89f4 : fetch_word Plain.M.loaded_segments (0xa8a3c : word) = Some W_a89f4.
Proof. vm_refl. Qed.
Lemma D_a89f4 : decode_any W_a89f4 = Some (Load SZ8 true 11 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89f8 : bv 32 := 0x0001d517.
Lemma F_a89f8 : fetch_word Plain.M.loaded_segments (0xa8a40 : word) = Some W_a89f8.
Proof. vm_refl. Qed.
Lemma D_a89f8 : decode_any W_a89f8 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a89fc : bv 32 := 0x06053503.
Lemma F_a89fc : fetch_word Plain.M.loaded_segments (0xa8a44 : word) = Some W_a89fc.
Proof. vm_refl. Qed.
Lemma D_a89fc : decode_any W_a89fc = Some (Load SZ8 true 10 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a00 : bv 32 := 0x0085b023.
Lemma F_a8a00 : fetch_word Plain.M.loaded_segments (0xa8a48 : word) = Some W_a8a00.
Proof. vm_refl. Qed.
Lemma D_a8a00 : decode_any W_a8a00 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a04 : bv 32 := 0x00140593.
Lemma F_a8a04 : fetch_word Plain.M.loaded_segments (0xa8a4c : word) = Some W_a8a04.
Proof. vm_refl. Qed.
Lemma D_a8a04 : decode_any W_a8a04 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a08 : bv 32 := 0x00853023.
Lemma F_a8a08 : fetch_word Plain.M.loaded_segments (0xa8a50 : word) = Some W_a8a08.
Proof. vm_refl. Qed.
Lemma D_a8a08 : decode_any W_a8a08 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a0c : bv 32 := 0x02f00613.
Lemma F_a8a0c : fetch_word Plain.M.loaded_segments (0xa8a54 : word) = Some W_a8a0c.
Proof. vm_refl. Qed.
Lemma D_a8a0c : decode_any W_a8a0c = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a10 : bv 32 := 0x00c0006f.
Lemma F_a8a10 : fetch_word Plain.M.loaded_segments (0xa8a58 : word) = Some W_a8a10.
Proof. vm_refl. Qed.
Lemma D_a8a10 : decode_any W_a8a10 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a14 : bv 32 := 0x00b53023.
Lemma F_a8a14 : fetch_word Plain.M.loaded_segments (0xa8a5c : word) = Some W_a8a14.
Proof. vm_refl. Qed.
Lemma D_a8a14 : decode_any W_a8a14 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a18 : bv 32 := 0x00158593.
Lemma F_a8a18 : fetch_word Plain.M.loaded_segments (0xa8a60 : word) = Some W_a8a18.
Proof. vm_refl. Qed.
Lemma D_a8a18 : decode_any W_a8a18 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a1c : bv 32 := 0xfff5c683.
Lemma F_a8a1c : fetch_word Plain.M.loaded_segments (0xa8a64 : word) = Some W_a8a1c.
Proof. vm_refl. Qed.
Lemma D_a8a1c : decode_any W_a8a1c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a20 : bv 32 := 0xfec68ae3.
Lemma F_a8a20 : fetch_word Plain.M.loaded_segments (0xa8a68 : word) = Some W_a8a20.
Proof. vm_refl. Qed.
Lemma D_a8a20 : decode_any W_a8a20 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a24 : bv 32 := 0xfe069ae3.
Lemma F_a8a24 : fetch_word Plain.M.loaded_segments (0xa8a6c : word) = Some W_a8a24.
Proof. vm_refl. Qed.
Lemma D_a8a24 : decode_any W_a8a24 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a28 : bv 32 := 0x03010513.
Lemma F_a8a28 : fetch_word Plain.M.loaded_segments (0xa8a70 : word) = Some W_a8a28.
Proof. vm_refl. Qed.
Lemma D_a8a28 : decode_any W_a8a28 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a2c : bv 32 := 0x214000ef.
Lemma F_a8a2c : fetch_word Plain.M.loaded_segments (0xa8a74 : word) = Some W_a8a2c.
Proof. vm_refl. Qed.
Lemma D_a8a2c : decode_any W_a8a2c = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a30 : bv 32 := 0x0f813503.
Lemma F_a8a30 : fetch_word Plain.M.loaded_segments (0xa8a78 : word) = Some W_a8a30.
Proof. vm_refl. Qed.
Lemma D_a8a30 : decode_any W_a8a30 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a34 : bv 32 := 0x1ad000ef.
Lemma F_a8a34 : fetch_word Plain.M.loaded_segments (0xa8a7c : word) = Some W_a8a34.
Proof. vm_refl. Qed.
Lemma D_a8a34 : decode_any W_a8a34 = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a38 : bv 32 := 0x08813503.
Lemma F_a8a38 : fetch_word Plain.M.loaded_segments (0xa8a80 : word) = Some W_a8a38.
Proof. vm_refl. Qed.
Lemma D_a8a38 : decode_any W_a8a38 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a3c : bv 32 := 0x09013583.
Lemma F_a8a3c : fetch_word Plain.M.loaded_segments (0xa8a84 : word) = Some W_a8a3c.
Proof. vm_refl. Qed.
Lemma D_a8a3c : decode_any W_a8a3c = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a40 : bv 32 := 0x00b51c63.
Lemma F_a8a40 : fetch_word Plain.M.loaded_segments (0xa8a88 : word) = Some W_a8a40.
Proof. vm_refl. Qed.
Lemma D_a8a40 : decode_any W_a8a40 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a44 : bv 32 := 0x09813503.
Lemma F_a8a44 : fetch_word Plain.M.loaded_segments (0xa8a8c : word) = Some W_a8a44.
Proof. vm_refl. Qed.
Lemma D_a8a44 : decode_any W_a8a44 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a48 : bv 32 := 0x0a013583.
Lemma F_a8a48 : fetch_word Plain.M.loaded_segments (0xa8a90 : word) = Some W_a8a48.
Proof. vm_refl. Qed.
Lemma D_a8a48 : decode_any W_a8a48 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a4c : bv 32 := 0x00b51663.
Lemma F_a8a4c : fetch_word Plain.M.loaded_segments (0xa8a94 : word) = Some W_a8a4c.
Proof. vm_refl. Qed.
Lemma D_a8a4c : decode_any W_a8a4c = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a50 : bv 32 := 0x0e813503.
Lemma F_a8a50 : fetch_word Plain.M.loaded_segments (0xa8a98 : word) = Some W_a8a50.
Proof. vm_refl. Qed.
Lemma D_a8a50 : decode_any W_a8a50 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8a54 : bv 32 := 0x0e050063.
Lemma F_a8a54 : fetch_word Plain.M.loaded_segments (0xa8a9c : word) = Some W_a8a54.
Proof. vm_refl. Qed.
Lemma D_a8a54 : decode_any W_a8a54 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b34 : bv 32 := 0x17813083.
Lemma F_a8b34 : fetch_word Plain.M.loaded_segments (0xa8b7c : word) = Some W_a8b34.
Proof. vm_refl. Qed.
Lemma D_a8b34 : decode_any W_a8b34 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b38 : bv 32 := 0x17013403.
Lemma F_a8b38 : fetch_word Plain.M.loaded_segments (0xa8b80 : word) = Some W_a8b38.
Proof. vm_refl. Qed.
Lemma D_a8b38 : decode_any W_a8b38 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b3c : bv 32 := 0x16813483.
Lemma F_a8b3c : fetch_word Plain.M.loaded_segments (0xa8b84 : word) = Some W_a8b3c.
Proof. vm_refl. Qed.
Lemma D_a8b3c : decode_any W_a8b3c = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b40 : bv 32 := 0x16013903.
Lemma F_a8b40 : fetch_word Plain.M.loaded_segments (0xa8b88 : word) = Some W_a8b40.
Proof. vm_refl. Qed.
Lemma D_a8b40 : decode_any W_a8b40 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b44 : bv 32 := 0x18010113.
Lemma F_a8b44 : fetch_word Plain.M.loaded_segments (0xa8b8c : word) = Some W_a8b44.
Proof. vm_refl. Qed.
Lemma D_a8b44 : decode_any W_a8b44 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b48 : bv 32 := 0x00008067.
Lemma F_a8b48 : fetch_word Plain.M.loaded_segments (0xa8b90 : word) = Some W_a8b48.
Proof. vm_refl. Qed.
Lemma D_a8b48 : decode_any W_a8b48 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b4c : bv 32 := 0xfe010113.
Lemma F_a8b4c : fetch_word Plain.M.loaded_segments (0xa8b94 : word) = Some W_a8b4c.
Proof. vm_refl. Qed.
Lemma D_a8b4c : decode_any W_a8b4c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b50 : bv 32 := 0x00113c23.
Lemma F_a8b50 : fetch_word Plain.M.loaded_segments (0xa8b98 : word) = Some W_a8b50.
Proof. vm_refl. Qed.
Lemma D_a8b50 : decode_any W_a8b50 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b54 : bv 32 := 0x00813823.
Lemma F_a8b54 : fetch_word Plain.M.loaded_segments (0xa8b9c : word) = Some W_a8b54.
Proof. vm_refl. Qed.
Lemma D_a8b54 : decode_any W_a8b54 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b58 : bv 32 := 0x00913423.
Lemma F_a8b58 : fetch_word Plain.M.loaded_segments (0xa8ba0 : word) = Some W_a8b58.
Proof. vm_refl. Qed.
Lemma D_a8b58 : decode_any W_a8b58 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b5c : bv 32 := 0xdc1ff0ef.
Lemma F_a8b5c : fetch_word Plain.M.loaded_segments (0xa8ba4 : word) = Some W_a8b5c.
Proof. vm_refl. Qed.
Lemma D_a8b5c : decode_any W_a8b5c = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b60 : bv 32 := 0x0001d517.
Lemma F_a8b60 : fetch_word Plain.M.loaded_segments (0xa8ba8 : word) = Some W_a8b60.
Proof. vm_refl. Qed.
Lemma D_a8b60 : decode_any W_a8b60 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b64 : bv 32 := 0x0001d597.
Lemma F_a8b64 : fetch_word Plain.M.loaded_segments (0xa8bac : word) = Some W_a8b64.
Proof. vm_refl. Qed.
Lemma D_a8b64 : decode_any W_a8b64 = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b68 : bv 32 := 0xf0053403.
Lemma F_a8b68 : fetch_word Plain.M.loaded_segments (0xa8bb0 : word) = Some W_a8b68.
Proof. vm_refl. Qed.
Lemma D_a8b68 : decode_any W_a8b68 = Some (Load SZ8 true 8 10 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b6c : bv 32 := 0xf045b483.
Lemma F_a8b6c : fetch_word Plain.M.loaded_segments (0xa8bb4 : word) = Some W_a8b6c.
Proof. vm_refl. Qed.
Lemma D_a8b6c : decode_any W_a8b6c = Some (Load SZ8 true 9 11 3844, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b70 : bv 32 := 0x0084fa63.
Lemma F_a8b70 : fetch_word Plain.M.loaded_segments (0xa8bb8 : word) = Some W_a8b70.
Proof. vm_refl. Qed.
Lemma D_a8b70 : decode_any W_a8b70 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b74 : bv 32 := 0x0004b503.
Lemma F_a8b74 : fetch_word Plain.M.loaded_segments (0xa8bbc : word) = Some W_a8b74.
Proof. vm_refl. Qed.
Lemma D_a8b74 : decode_any W_a8b74 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b78 : bv 32 := 0x000500e7.
Lemma F_a8b78 : fetch_word Plain.M.loaded_segments (0xa8bc0 : word) = Some W_a8b78.
Proof. vm_refl. Qed.
Lemma D_a8b78 : decode_any W_a8b78 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b7c : bv 32 := 0x00848493.
Lemma F_a8b7c : fetch_word Plain.M.loaded_segments (0xa8bc4 : word) = Some W_a8b7c.
Proof. vm_refl. Qed.
Lemma D_a8b7c : decode_any W_a8b7c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b80 : bv 32 := 0xfe84eae3.
Lemma F_a8b80 : fetch_word Plain.M.loaded_segments (0xa8bc8 : word) = Some W_a8b80.
Proof. vm_refl. Qed.
Lemma D_a8b80 : decode_any W_a8b80 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b84 : bv 32 := 0x01813083.
Lemma F_a8b84 : fetch_word Plain.M.loaded_segments (0xa8bcc : word) = Some W_a8b84.
Proof. vm_refl. Qed.
Lemma D_a8b84 : decode_any W_a8b84 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b88 : bv 32 := 0x01013403.
Lemma F_a8b88 : fetch_word Plain.M.loaded_segments (0xa8bd0 : word) = Some W_a8b88.
Proof. vm_refl. Qed.
Lemma D_a8b88 : decode_any W_a8b88 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b8c : bv 32 := 0x00813483.
Lemma F_a8b8c : fetch_word Plain.M.loaded_segments (0xa8bd4 : word) = Some W_a8b8c.
Proof. vm_refl. Qed.
Lemma D_a8b8c : decode_any W_a8b8c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b90 : bv 32 := 0x02010113.
Lemma F_a8b90 : fetch_word Plain.M.loaded_segments (0xa8bd8 : word) = Some W_a8b90.
Proof. vm_refl. Qed.
Lemma D_a8b90 : decode_any W_a8b90 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b94 : bv 32 := 0x00008067.
Lemma F_a8b94 : fetch_word Plain.M.loaded_segments (0xa8bdc : word) = Some W_a8b94.
Proof. vm_refl. Qed.
Lemma D_a8b94 : decode_any W_a8b94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b98 : bv 32 := 0xfe010113.
Lemma F_a8b98 : fetch_word Plain.M.loaded_segments (0xa8be0 : word) = Some W_a8b98.
Proof. vm_refl. Qed.
Lemma D_a8b98 : decode_any W_a8b98 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8b9c : bv 32 := 0x00113c23.
Lemma F_a8b9c : fetch_word Plain.M.loaded_segments (0xa8be4 : word) = Some W_a8b9c.
Proof. vm_refl. Qed.
Lemma D_a8b9c : decode_any W_a8b9c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ba0 : bv 32 := 0x00813823.
Lemma F_a8ba0 : fetch_word Plain.M.loaded_segments (0xa8be8 : word) = Some W_a8ba0.
Proof. vm_refl. Qed.
Lemma D_a8ba0 : decode_any W_a8ba0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ba4 : bv 32 := 0x00913423.
Lemma F_a8ba4 : fetch_word Plain.M.loaded_segments (0xa8bec : word) = Some W_a8ba4.
Proof. vm_refl. Qed.
Lemma D_a8ba4 : decode_any W_a8ba4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8ba8 : bv 32 := 0x01213023.
Lemma F_a8ba8 : fetch_word Plain.M.loaded_segments (0xa8bf0 : word) = Some W_a8ba8.
Proof. vm_refl. Qed.
Lemma D_a8ba8 : decode_any W_a8ba8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bac : bv 32 := 0x00060413.
Lemma F_a8bac : fetch_word Plain.M.loaded_segments (0xa8bf4 : word) = Some W_a8bac.
Proof. vm_refl. Qed.
Lemma D_a8bac : decode_any W_a8bac = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bb0 : bv 32 := 0x00058493.
Lemma F_a8bb0 : fetch_word Plain.M.loaded_segments (0xa8bf8 : word) = Some W_a8bb0.
Proof. vm_refl. Qed.
Lemma D_a8bb0 : decode_any W_a8bb0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bb4 : bv 32 := 0x00050913.
Lemma F_a8bb4 : fetch_word Plain.M.loaded_segments (0xa8bfc : word) = Some W_a8bb4.
Proof. vm_refl. Qed.
Lemma D_a8bb4 : decode_any W_a8bb4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bb8 : bv 32 := 0x00063583.
Lemma F_a8bb8 : fetch_word Plain.M.loaded_segments (0xa8c00 : word) = Some W_a8bb8.
Proof. vm_refl. Qed.
Lemma D_a8bb8 : decode_any W_a8bb8 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bbc : bv 32 := 0x00349513.
Lemma F_a8bbc : fetch_word Plain.M.loaded_segments (0xa8c04 : word) = Some W_a8bbc.
Proof. vm_refl. Qed.
Lemma D_a8bbc : decode_any W_a8bbc = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bc0 : bv 32 := 0x00a60533.
Lemma F_a8bc0 : fetch_word Plain.M.loaded_segments (0xa8c08 : word) = Some W_a8bc0.
Proof. vm_refl. Qed.
Lemma D_a8bc0 : decode_any W_a8bc0 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bc4 : bv 32 := 0x00850513.
Lemma F_a8bc4 : fetch_word Plain.M.loaded_segments (0xa8c0c : word) = Some W_a8bc4.
Proof. vm_refl. Qed.
Lemma D_a8bc4 : decode_any W_a8bc4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bc8 : bv 32 := 0xd59ff0ef.
Lemma F_a8bc8 : fetch_word Plain.M.loaded_segments (0xa8c10 : word) = Some W_a8bc8.
Proof. vm_refl. Qed.
Lemma D_a8bc8 : decode_any W_a8bc8 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bcc : bv 32 := 0x00000517.
Lemma F_a8bcc : fetch_word Plain.M.loaded_segments (0xa8c14 : word) = Some W_a8bcc.
Proof. vm_refl. Qed.
Lemma D_a8bcc : decode_any W_a8bcc = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bd0 : bv 32 := 0x02c50313.
Lemma F_a8bd0 : fetch_word Plain.M.loaded_segments (0xa8c18 : word) = Some W_a8bd0.
Proof. vm_refl. Qed.
Lemma D_a8bd0 : decode_any W_a8bd0 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bd4 : bv 32 := 0x00090513.
Lemma F_a8bd4 : fetch_word Plain.M.loaded_segments (0xa8c1c : word) = Some W_a8bd4.
Proof. vm_refl. Qed.
Lemma D_a8bd4 : decode_any W_a8bd4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bd8 : bv 32 := 0x00048593.
Lemma F_a8bd8 : fetch_word Plain.M.loaded_segments (0xa8c20 : word) = Some W_a8bd8.
Proof. vm_refl. Qed.
Lemma D_a8bd8 : decode_any W_a8bd8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bdc : bv 32 := 0x00040613.
Lemma F_a8bdc : fetch_word Plain.M.loaded_segments (0xa8c24 : word) = Some W_a8bdc.
Proof. vm_refl. Qed.
Lemma D_a8bdc : decode_any W_a8bdc = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8be0 : bv 32 := 0x01813083.
Lemma F_a8be0 : fetch_word Plain.M.loaded_segments (0xa8c28 : word) = Some W_a8be0.
Proof. vm_refl. Qed.
Lemma D_a8be0 : decode_any W_a8be0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8be4 : bv 32 := 0x01013403.
Lemma F_a8be4 : fetch_word Plain.M.loaded_segments (0xa8c2c : word) = Some W_a8be4.
Proof. vm_refl. Qed.
Lemma D_a8be4 : decode_any W_a8be4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8be8 : bv 32 := 0x00813483.
Lemma F_a8be8 : fetch_word Plain.M.loaded_segments (0xa8c30 : word) = Some W_a8be8.
Proof. vm_refl. Qed.
Lemma D_a8be8 : decode_any W_a8be8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bec : bv 32 := 0x00013903.
Lemma F_a8bec : fetch_word Plain.M.loaded_segments (0xa8c34 : word) = Some W_a8bec.
Proof. vm_refl. Qed.
Lemma D_a8bec : decode_any W_a8bec = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bf0 : bv 32 := 0x02010113.
Lemma F_a8bf0 : fetch_word Plain.M.loaded_segments (0xa8c38 : word) = Some W_a8bf0.
Proof. vm_refl. Qed.
Lemma D_a8bf0 : decode_any W_a8bf0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bf4 : bv 32 := 0x00030067.
Lemma F_a8bf4 : fetch_word Plain.M.loaded_segments (0xa8c3c : word) = Some W_a8bf4.
Proof. vm_refl. Qed.
Lemma D_a8bf4 : decode_any W_a8bf4 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bf8 : bv 32 := 0xfd010113.
Lemma F_a8bf8 : fetch_word Plain.M.loaded_segments (0xa8c40 : word) = Some W_a8bf8.
Proof. vm_refl. Qed.
Lemma D_a8bf8 : decode_any W_a8bf8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8bfc : bv 32 := 0x02113423.
Lemma F_a8bfc : fetch_word Plain.M.loaded_segments (0xa8c44 : word) = Some W_a8bfc.
Proof. vm_refl. Qed.
Lemma D_a8bfc : decode_any W_a8bfc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c00 : bv 32 := 0x02813023.
Lemma F_a8c00 : fetch_word Plain.M.loaded_segments (0xa8c48 : word) = Some W_a8c00.
Proof. vm_refl. Qed.
Lemma D_a8c00 : decode_any W_a8c00 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c04 : bv 32 := 0x00913c23.
Lemma F_a8c04 : fetch_word Plain.M.loaded_segments (0xa8c4c : word) = Some W_a8c04.
Proof. vm_refl. Qed.
Lemma D_a8c04 : decode_any W_a8c04 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c08 : bv 32 := 0x01213823.
Lemma F_a8c08 : fetch_word Plain.M.loaded_segments (0xa8c50 : word) = Some W_a8c08.
Proof. vm_refl. Qed.
Lemma D_a8c08 : decode_any W_a8c08 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c0c : bv 32 := 0x01313423.
Lemma F_a8c0c : fetch_word Plain.M.loaded_segments (0xa8c54 : word) = Some W_a8c0c.
Proof. vm_refl. Qed.
Lemma D_a8c0c : decode_any W_a8c0c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c10 : bv 32 := 0x00060413.
Lemma F_a8c10 : fetch_word Plain.M.loaded_segments (0xa8c58 : word) = Some W_a8c10.
Proof. vm_refl. Qed.
Lemma D_a8c10 : decode_any W_a8c10 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c14 : bv 32 := 0x00058493.
Lemma F_a8c14 : fetch_word Plain.M.loaded_segments (0xa8c5c : word) = Some W_a8c14.
Proof. vm_refl. Qed.
Lemma D_a8c14 : decode_any W_a8c14 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c18 : bv 32 := 0x00050913.
Lemma F_a8c18 : fetch_word Plain.M.loaded_segments (0xa8c60 : word) = Some W_a8c18.
Proof. vm_refl. Qed.
Lemma D_a8c18 : decode_any W_a8c18 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c1c : bv 32 := 0x00359513.
Lemma F_a8c1c : fetch_word Plain.M.loaded_segments (0xa8c64 : word) = Some W_a8c1c.
Proof. vm_refl. Qed.
Lemma D_a8c1c : decode_any W_a8c1c = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c20 : bv 32 := 0x00a60533.
Lemma F_a8c20 : fetch_word Plain.M.loaded_segments (0xa8c68 : word) = Some W_a8c20.
Proof. vm_refl. Qed.
Lemma D_a8c20 : decode_any W_a8c20 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c24 : bv 32 := 0x00850993.
Lemma F_a8c24 : fetch_word Plain.M.loaded_segments (0xa8c6c : word) = Some W_a8c24.
Proof. vm_refl. Qed.
Lemma D_a8c24 : decode_any W_a8c24 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c28 : bv 32 := 0xf25ff0ef.
Lemma F_a8c28 : fetch_word Plain.M.loaded_segments (0xa8c70 : word) = Some W_a8c28.
Proof. vm_refl. Qed.
Lemma D_a8c28 : decode_any W_a8c28 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c2c : bv 32 := 0x00048513.
Lemma F_a8c2c : fetch_word Plain.M.loaded_segments (0xa8c74 : word) = Some W_a8c2c.
Proof. vm_refl. Qed.
Lemma D_a8c2c : decode_any W_a8c2c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c30 : bv 32 := 0x00040593.
Lemma F_a8c30 : fetch_word Plain.M.loaded_segments (0xa8c78 : word) = Some W_a8c30.
Proof. vm_refl. Qed.
Lemma D_a8c30 : decode_any W_a8c30 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c34 : bv 32 := 0x00098613.
Lemma F_a8c34 : fetch_word Plain.M.loaded_segments (0xa8c7c : word) = Some W_a8c34.
Proof. vm_refl. Qed.
Lemma D_a8c34 : decode_any W_a8c34 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8c38 : bv 32 := 0x000900e7.
Lemma F_a8c38 : fetch_word Plain.M.loaded_segments (0xa8c80 : word) = Some W_a8c38.
Proof. vm_refl. Qed.
Lemma D_a8c38 : decode_any W_a8c38 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r4a000_4b000.
