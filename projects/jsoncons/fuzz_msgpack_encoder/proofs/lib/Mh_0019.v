(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain.
Module Ns0_code_r369d8_369dc.
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

Definition W_47198 : bv 32 := 0x00008067.
Lemma F_47198 : fetch_word Plain.M.loaded_segments (0x471e0 : word) = Some W_47198.
Proof. vm_refl. Qed.
Lemma D_47198 : decode_any W_47198 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r369d8_369dc.
Module Ns0_code_r3b998_3b99c.
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

Definition W_3c014 : bv 32 := 0x00008067.
Lemma F_3c014 : fetch_word Plain.M.loaded_segments (0x3c05c : word) = Some W_3c014.
Proof. vm_refl. Qed.
Lemma D_3c014 : decode_any W_3c014 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3b998_3b99c.
Module Ns0_code_r3b6ec_3b6f0.
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

Definition W_3bd68 : bv 32 := 0x00008067.
Lemma F_3bd68 : fetch_word Plain.M.loaded_segments (0x3bdb0 : word) = Some W_3bd68.
Proof. vm_refl. Qed.
Lemma D_3bd68 : decode_any W_3bd68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3b6ec_3b6f0.
Module Ns0_code_r3cd54_3cd58.
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

Definition W_3d3d0 : bv 32 := 0x00008067.
Lemma F_3d3d0 : fetch_word Plain.M.loaded_segments (0x3d418 : word) = Some W_3d3d0.
Proof. vm_refl. Qed.
Lemma D_3d3d0 : decode_any W_3d3d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3cd54_3cd58.
Module Ns0_code_r3e130_3e244.
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

Definition W_3e7ac : bv 32 := 0xf6010113.
Lemma F_3e7ac : fetch_word Plain.M.loaded_segments (0x3e7f4 : word) = Some W_3e7ac.
Proof. vm_refl. Qed.
Lemma D_3e7ac : decode_any W_3e7ac = Some (OpImm ALU_ADD 2 2 3936, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7b0 : bv 32 := 0x08113c23.
Lemma F_3e7b0 : fetch_word Plain.M.loaded_segments (0x3e7f8 : word) = Some W_3e7b0.
Proof. vm_refl. Qed.
Lemma D_3e7b0 : decode_any W_3e7b0 = Some (Store SZ8 2 1 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7b4 : bv 32 := 0x08813823.
Lemma F_3e7b4 : fetch_word Plain.M.loaded_segments (0x3e7fc : word) = Some W_3e7b4.
Proof. vm_refl. Qed.
Lemma D_3e7b4 : decode_any W_3e7b4 = Some (Store SZ8 2 8 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7b8 : bv 32 := 0x08913423.
Lemma F_3e7b8 : fetch_word Plain.M.loaded_segments (0x3e800 : word) = Some W_3e7b8.
Proof. vm_refl. Qed.
Lemma D_3e7b8 : decode_any W_3e7b8 = Some (Store SZ8 2 9 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7bc : bv 32 := 0x09213023.
Lemma F_3e7bc : fetch_word Plain.M.loaded_segments (0x3e804 : word) = Some W_3e7bc.
Proof. vm_refl. Qed.
Lemma D_3e7bc : decode_any W_3e7bc = Some (Store SZ8 2 18 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7c0 : bv 32 := 0x07313c23.
Lemma F_3e7c0 : fetch_word Plain.M.loaded_segments (0x3e808 : word) = Some W_3e7c0.
Proof. vm_refl. Qed.
Lemma D_3e7c0 : decode_any W_3e7c0 = Some (Store SZ8 2 19 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7c4 : bv 32 := 0x06813827.
Lemma F_3e7c4 : fetch_word Plain.M.loaded_segments (0x3e80c : word) = Some W_3e7c4.
Proof. vm_refl. Qed.
Lemma D_3e7c4 : decode_any W_3e7c4 = Some (FStore FMT_D 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7c8 : bv 32 := 0x00058413.
Lemma F_3e7c8 : fetch_word Plain.M.loaded_segments (0x3e810 : word) = Some W_3e7c8.
Proof. vm_refl. Qed.
Lemma D_3e7c8 : decode_any W_3e7c8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7cc : bv 32 := 0xf20007d3.
Lemma F_3e7cc : fetch_word Plain.M.loaded_segments (0x3e814 : word) = Some W_3e7cc.
Proof. vm_refl. Qed.
Lemma D_3e7cc : decode_any W_3e7cc = Some (Fmv FMV_F_X FMT_D 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7d0 : bv 32 := 0xa2f525d3.
Lemma F_3e7d0 : fetch_word Plain.M.loaded_segments (0x3e818 : word) = Some W_3e7d0.
Proof. vm_refl. Qed.
Lemma D_3e7d0 : decode_any W_3e7d0 = Some (Fcmp F_EQ FMT_D 11 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7d4 : bv 32 := 0x02058863.
Lemma F_3e7d4 : fetch_word Plain.M.loaded_segments (0x3e81c : word) = Some W_3e7d4.
Proof. vm_refl. Qed.
Lemma D_3e7d4 : decode_any W_3e7d4 = Some (Branch BC_EQ 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7d8 : bv 32 := 0x00043503.
Lemma F_3e7d8 : fetch_word Plain.M.loaded_segments (0x3e820 : word) = Some W_3e7d8.
Proof. vm_refl. Qed.
Lemma D_3e7d8 : decode_any W_3e7d8 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7dc : bv 32 := 0x03000593.
Lemma F_3e7dc : fetch_word Plain.M.loaded_segments (0x3e824 : word) = Some W_3e7dc.
Proof. vm_refl. Qed.
Lemma D_3e7dc : decode_any W_3e7dc = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7e0 : bv 32 := 0x41d270ef.
Lemma F_3e7e0 : fetch_word Plain.M.loaded_segments (0x3e828 : word) = Some W_3e7e0.
Proof. vm_refl. Qed.
Lemma D_3e7e0 : decode_any W_3e7e0 = Some (Jal 1 162844, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7e4 : bv 32 := 0x00043503.
Lemma F_3e7e4 : fetch_word Plain.M.loaded_segments (0x3e82c : word) = Some W_3e7e4.
Proof. vm_refl. Qed.
Lemma D_3e7e4 : decode_any W_3e7e4 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7e8 : bv 32 := 0x02e00593.
Lemma F_3e7e8 : fetch_word Plain.M.loaded_segments (0x3e830 : word) = Some W_3e7e8.
Proof. vm_refl. Qed.
Lemma D_3e7e8 : decode_any W_3e7e8 = Some (OpImm ALU_ADD 11 0 46, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7ec : bv 32 := 0x411270ef.
Lemma F_3e7ec : fetch_word Plain.M.loaded_segments (0x3e834 : word) = Some W_3e7ec.
Proof. vm_refl. Qed.
Lemma D_3e7ec : decode_any W_3e7ec = Some (Jal 1 162832, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7f0 : bv 32 := 0x00043503.
Lemma F_3e7f0 : fetch_word Plain.M.loaded_segments (0x3e838 : word) = Some W_3e7f0.
Proof. vm_refl. Qed.
Lemma D_3e7f0 : decode_any W_3e7f0 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7f4 : bv 32 := 0x03000593.
Lemma F_3e7f4 : fetch_word Plain.M.loaded_segments (0x3e83c : word) = Some W_3e7f4.
Proof. vm_refl. Qed.
Lemma D_3e7f4 : decode_any W_3e7f4 = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7f8 : bv 32 := 0x405270ef.
Lemma F_3e7f8 : fetch_word Plain.M.loaded_segments (0x3e840 : word) = Some W_3e7f8.
Proof. vm_refl. Qed.
Lemma D_3e7f8 : decode_any W_3e7f8 = Some (Jal 1 162820, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7fc : bv 32 := 0x00100513.
Lemma F_3e7fc : fetch_word Plain.M.loaded_segments (0x3e844 : word) = Some W_3e7fc.
Proof. vm_refl. Qed.
Lemma D_3e7fc : decode_any W_3e7fc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e800 : bv 32 := 0x0580006f.
Lemma F_3e800 : fetch_word Plain.M.loaded_segments (0x3e848 : word) = Some W_3e800.
Proof. vm_refl. Qed.
Lemma D_3e800 : decode_any W_3e800 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e804 : bv 32 := 0x22a50453.
Lemma F_3e804 : fetch_word Plain.M.loaded_segments (0x3e84c : word) = Some W_3e804.
Proof. vm_refl. Qed.
Lemma D_3e804 : decode_any W_3e804 = Some (Fsgnj F_SGNJ FMT_D 8 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e808 : bv 32 := 0x00050493.
Lemma F_3e808 : fetch_word Plain.M.loaded_segments (0x3e850 : word) = Some W_3e808.
Proof. vm_refl. Qed.
Lemma D_3e808 : decode_any W_3e808 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e80c : bv 32 := 0xe2050953.
Lemma F_3e80c : fetch_word Plain.M.loaded_segments (0x3e854 : word) = Some W_3e80c.
Proof. vm_refl. Qed.
Lemma D_3e80c : decode_any W_3e80c = Some (Fmv FMV_X_F FMT_D 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e810 : bv 32 := 0xfffd4617.
Lemma F_3e810 : fetch_word Plain.M.loaded_segments (0x3e858 : word) = Some W_3e810.
Proof. vm_refl. Qed.
Lemma D_3e810 : decode_any W_3e810 = Some (Auipc 12 1048532, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e814 : bv 32 := 0x00c10513.
Lemma F_3e814 : fetch_word Plain.M.loaded_segments (0x3e85c : word) = Some W_3e814.
Proof. vm_refl. Qed.
Lemma D_3e814 : decode_any W_3e814 = Some (OpImm ALU_ADD 10 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e818 : bv 32 := 0x06400593.
Lemma F_3e818 : fetch_word Plain.M.loaded_segments (0x3e860 : word) = Some W_3e818.
Proof. vm_refl. Qed.
Lemma D_3e818 : decode_any W_3e818 = Some (OpImm ALU_ADD 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e81c : bv 32 := 0x3b360613.
Lemma F_3e81c : fetch_word Plain.M.loaded_segments (0x3e864 : word) = Some W_3e81c.
Proof. vm_refl. Qed.
Lemma D_3e81c : decode_any W_3e81c = Some (OpImm ALU_ADD 12 12 947, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e820 : bv 32 := 0x00f00693.
Lemma F_3e820 : fetch_word Plain.M.loaded_segments (0x3e868 : word) = Some W_3e820.
Proof. vm_refl. Qed.
Lemma D_3e820 : decode_any W_3e820 = Some (OpImm ALU_ADD 13 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e824 : bv 32 := 0x00090713.
Lemma F_3e824 : fetch_word Plain.M.loaded_segments (0x3e86c : word) = Some W_3e824.
Proof. vm_refl. Qed.
Lemma D_3e824 : decode_any W_3e824 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e828 : bv 32 := 0x568700ef.
Lemma F_3e828 : fetch_word Plain.M.loaded_segments (0x3e870 : word) = Some W_3e828.
Proof. vm_refl. Qed.
Lemma D_3e828 : decode_any W_3e828 = Some (Jal 1 460136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e82c : bv 32 := 0x02054463.
Lemma F_3e82c : fetch_word Plain.M.loaded_segments (0x3e874 : word) = Some W_3e82c.
Proof. vm_refl. Qed.
Lemma D_3e82c : decode_any W_3e82c = Some (Branch BC_LT 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e830 : bv 32 := 0x00050993.
Lemma F_3e830 : fetch_word Plain.M.loaded_segments (0x3e878 : word) = Some W_3e830.
Proof. vm_refl. Qed.
Lemma D_3e830 : decode_any W_3e830 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e834 : bv 32 := 0x00013023.
Lemma F_3e834 : fetch_word Plain.M.loaded_segments (0x3e87c : word) = Some W_3e834.
Proof. vm_refl. Qed.
Lemma D_3e834 : decode_any W_3e834 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e838 : bv 32 := 0x00c10513.
Lemma F_3e838 : fetch_word Plain.M.loaded_segments (0x3e880 : word) = Some W_3e838.
Proof. vm_refl. Qed.
Lemma D_3e838 : decode_any W_3e838 = Some (OpImm ALU_ADD 10 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e83c : bv 32 := 0x00010613.
Lemma F_3e83c : fetch_word Plain.M.loaded_segments (0x3e884 : word) = Some W_3e83c.
Proof. vm_refl. Qed.
Lemma D_3e83c : decode_any W_3e83c = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e840 : bv 32 := 0x00098593.
Lemma F_3e840 : fetch_word Plain.M.loaded_segments (0x3e888 : word) = Some W_3e840.
Proof. vm_refl. Qed.
Lemma D_3e840 : decode_any W_3e840 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e844 : bv 32 := 0xd65ff0ef.
Lemma F_3e844 : fetch_word Plain.M.loaded_segments (0x3e88c : word) = Some W_3e844.
Proof. vm_refl. Qed.
Lemma D_3e844 : decode_any W_3e844 = Some (Jal 1 2096484, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e848 : bv 32 := 0x0005859b.
Lemma F_3e848 : fetch_word Plain.M.loaded_segments (0x3e890 : word) = Some W_3e848.
Proof. vm_refl. Qed.
Lemma D_3e848 : decode_any W_3e848 = Some (OpImm32 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e84c : bv 32 := 0x01600513.
Lemma F_3e84c : fetch_word Plain.M.loaded_segments (0x3e894 : word) = Some W_3e84c.
Proof. vm_refl. Qed.
Lemma D_3e84c : decode_any W_3e84c = Some (OpImm ALU_ADD 10 0 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e850 : bv 32 := 0x02a59463.
Lemma F_3e850 : fetch_word Plain.M.loaded_segments (0x3e898 : word) = Some W_3e850.
Proof. vm_refl. Qed.
Lemma D_3e850 : decode_any W_3e850 = Some (Branch BC_NE 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e854 : bv 32 := 0x00000513.
Lemma F_3e854 : fetch_word Plain.M.loaded_segments (0x3e89c : word) = Some W_3e854.
Proof. vm_refl. Qed.
Lemma D_3e854 : decode_any W_3e854 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e858 : bv 32 := 0x09813083.
Lemma F_3e858 : fetch_word Plain.M.loaded_segments (0x3e8a0 : word) = Some W_3e858.
Proof. vm_refl. Qed.
Lemma D_3e858 : decode_any W_3e858 = Some (Load SZ8 true 1 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e85c : bv 32 := 0x09013403.
Lemma F_3e85c : fetch_word Plain.M.loaded_segments (0x3e8a4 : word) = Some W_3e85c.
Proof. vm_refl. Qed.
Lemma D_3e85c : decode_any W_3e85c = Some (Load SZ8 true 8 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e860 : bv 32 := 0x08813483.
Lemma F_3e860 : fetch_word Plain.M.loaded_segments (0x3e8a8 : word) = Some W_3e860.
Proof. vm_refl. Qed.
Lemma D_3e860 : decode_any W_3e860 = Some (Load SZ8 true 9 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e864 : bv 32 := 0x08013903.
Lemma F_3e864 : fetch_word Plain.M.loaded_segments (0x3e8ac : word) = Some W_3e864.
Proof. vm_refl. Qed.
Lemma D_3e864 : decode_any W_3e864 = Some (Load SZ8 true 18 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e868 : bv 32 := 0x07813983.
Lemma F_3e868 : fetch_word Plain.M.loaded_segments (0x3e8b0 : word) = Some W_3e868.
Proof. vm_refl. Qed.
Lemma D_3e868 : decode_any W_3e868 = Some (Load SZ8 true 19 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e86c : bv 32 := 0x07013407.
Lemma F_3e86c : fetch_word Plain.M.loaded_segments (0x3e8b4 : word) = Some W_3e86c.
Proof. vm_refl. Qed.
Lemma D_3e86c : decode_any W_3e86c = Some (FLoad FMT_D 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e870 : bv 32 := 0x0a010113.
Lemma F_3e870 : fetch_word Plain.M.loaded_segments (0x3e8b8 : word) = Some W_3e870.
Proof. vm_refl. Qed.
Lemma D_3e870 : decode_any W_3e870 = Some (OpImm ALU_ADD 2 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e874 : bv 32 := 0x00008067.
Lemma F_3e874 : fetch_word Plain.M.loaded_segments (0x3e8bc : word) = Some W_3e874.
Proof. vm_refl. Qed.
Lemma D_3e874 : decode_any W_3e874 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e878 : bv 32 := 0x00013787.
Lemma F_3e878 : fetch_word Plain.M.loaded_segments (0x3e8c0 : word) = Some W_3e878.
Proof. vm_refl. Qed.
Lemma D_3e878 : decode_any W_3e878 = Some (FLoad FMT_D 15 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e87c : bv 32 := 0xa287a553.
Lemma F_3e87c : fetch_word Plain.M.loaded_segments (0x3e8c4 : word) = Some W_3e87c.
Proof. vm_refl. Qed.
Lemma D_3e87c : decode_any W_3e87c = Some (Fcmp F_EQ FMT_D 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e880 : bv 32 := 0x02051463.
Lemma F_3e880 : fetch_word Plain.M.loaded_segments (0x3e8c8 : word) = Some W_3e880.
Proof. vm_refl. Qed.
Lemma D_3e880 : decode_any W_3e880 = Some (Branch BC_NE 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e884 : bv 32 := 0xfffd4617.
Lemma F_3e884 : fetch_word Plain.M.loaded_segments (0x3e8cc : word) = Some W_3e884.
Proof. vm_refl. Qed.
Lemma D_3e884 : decode_any W_3e884 = Some (Auipc 12 1048532, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e888 : bv 32 := 0x00c10513.
Lemma F_3e888 : fetch_word Plain.M.loaded_segments (0x3e8d0 : word) = Some W_3e888.
Proof. vm_refl. Qed.
Lemma D_3e888 : decode_any W_3e888 = Some (OpImm ALU_ADD 10 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e88c : bv 32 := 0x06400593.
Lemma F_3e88c : fetch_word Plain.M.loaded_segments (0x3e8d4 : word) = Some W_3e88c.
Proof. vm_refl. Qed.
Lemma D_3e88c : decode_any W_3e88c = Some (OpImm ALU_ADD 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e890 : bv 32 := 0x33f60613.
Lemma F_3e890 : fetch_word Plain.M.loaded_segments (0x3e8d8 : word) = Some W_3e890.
Proof. vm_refl. Qed.
Lemma D_3e890 : decode_any W_3e890 = Some (OpImm ALU_ADD 12 12 831, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e894 : bv 32 := 0x01100693.
Lemma F_3e894 : fetch_word Plain.M.loaded_segments (0x3e8dc : word) = Some W_3e894.
Proof. vm_refl. Qed.
Lemma D_3e894 : decode_any W_3e894 = Some (OpImm ALU_ADD 13 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e898 : bv 32 := 0x00090713.
Lemma F_3e898 : fetch_word Plain.M.loaded_segments (0x3e8e0 : word) = Some W_3e898.
Proof. vm_refl. Qed.
Lemma D_3e898 : decode_any W_3e898 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e89c : bv 32 := 0x4f4700ef.
Lemma F_3e89c : fetch_word Plain.M.loaded_segments (0x3e8e4 : word) = Some W_3e89c.
Proof. vm_refl. Qed.
Lemma D_3e89c : decode_any W_3e89c = Some (Jal 1 460020, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e8a0 : bv 32 := 0xfa054ae3.
Lemma F_3e8a0 : fetch_word Plain.M.loaded_segments (0x3e8e8 : word) = Some W_3e8a0.
Proof. vm_refl. Qed.
Lemma D_3e8a0 : decode_any W_3e8a0 = Some (Branch BC_LT 10 0 8116, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e8a4 : bv 32 := 0x00050993.
Lemma F_3e8a4 : fetch_word Plain.M.loaded_segments (0x3e8ec : word) = Some W_3e8a4.
Proof. vm_refl. Qed.
Lemma D_3e8a4 : decode_any W_3e8a4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e8a8 : bv 32 := 0x00c10513.
Lemma F_3e8a8 : fetch_word Plain.M.loaded_segments (0x3e8f0 : word) = Some W_3e8a8.
Proof. vm_refl. Qed.
Lemma D_3e8a8 : decode_any W_3e8a8 = Some (OpImm ALU_ADD 10 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e8ac : bv 32 := 0x00098593.
Lemma F_3e8ac : fetch_word Plain.M.loaded_segments (0x3e8f4 : word) = Some W_3e8ac.
Proof. vm_refl. Qed.
Lemma D_3e8ac : decode_any W_3e8ac = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e8b0 : bv 32 := 0x00048613.
Lemma F_3e8b0 : fetch_word Plain.M.loaded_segments (0x3e8f8 : word) = Some W_3e8b0.
Proof. vm_refl. Qed.
Lemma D_3e8b0 : decode_any W_3e8b0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e8b4 : bv 32 := 0x00040693.
Lemma F_3e8b4 : fetch_word Plain.M.loaded_segments (0x3e8fc : word) = Some W_3e8b4.
Proof. vm_refl. Qed.
Lemma D_3e8b4 : decode_any W_3e8b4 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e8b8 : bv 32 := 0xd61fe0ef.
Lemma F_3e8b8 : fetch_word Plain.M.loaded_segments (0x3e900 : word) = Some W_3e8b8.
Proof. vm_refl. Qed.
Lemma D_3e8b8 : decode_any W_3e8b8 = Some (Jal 1 2092384, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e8bc : bv 32 := 0xf41ff06f.
Lemma F_3e8bc : fetch_word Plain.M.loaded_segments (0x3e904 : word) = Some W_3e8bc.
Proof. vm_refl. Qed.
Lemma D_3e8bc : decode_any W_3e8bc = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3e130_3e244.
Module Ns0_code_r3e05c_3e130.
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

Definition W_3e6d8 : bv 32 := 0xf7010113.
Lemma F_3e6d8 : fetch_word Plain.M.loaded_segments (0x3e720 : word) = Some W_3e6d8.
Proof. vm_refl. Qed.
Lemma D_3e6d8 : decode_any W_3e6d8 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e6dc : bv 32 := 0x08113423.
Lemma F_3e6dc : fetch_word Plain.M.loaded_segments (0x3e724 : word) = Some W_3e6dc.
Proof. vm_refl. Qed.
Lemma D_3e6dc : decode_any W_3e6dc = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e6e0 : bv 32 := 0x08813023.
Lemma F_3e6e0 : fetch_word Plain.M.loaded_segments (0x3e728 : word) = Some W_3e6e0.
Proof. vm_refl. Qed.
Lemma D_3e6e0 : decode_any W_3e6e0 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e6e4 : bv 32 := 0x06913c23.
Lemma F_3e6e4 : fetch_word Plain.M.loaded_segments (0x3e72c : word) = Some W_3e6e4.
Proof. vm_refl. Qed.
Lemma D_3e6e4 : decode_any W_3e6e4 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e6e8 : bv 32 := 0x06813827.
Lemma F_3e6e8 : fetch_word Plain.M.loaded_segments (0x3e730 : word) = Some W_3e6e8.
Proof. vm_refl. Qed.
Lemma D_3e6e8 : decode_any W_3e6e8 = Some (FStore FMT_D 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e6ec : bv 32 := 0x00058413.
Lemma F_3e6ec : fetch_word Plain.M.loaded_segments (0x3e734 : word) = Some W_3e6ec.
Proof. vm_refl. Qed.
Lemma D_3e6ec : decode_any W_3e6ec = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e6f0 : bv 32 := 0xf20007d3.
Lemma F_3e6f0 : fetch_word Plain.M.loaded_segments (0x3e738 : word) = Some W_3e6f0.
Proof. vm_refl. Qed.
Lemma D_3e6f0 : decode_any W_3e6f0 = Some (Fmv FMV_F_X FMT_D 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e6f4 : bv 32 := 0xa2f525d3.
Lemma F_3e6f4 : fetch_word Plain.M.loaded_segments (0x3e73c : word) = Some W_3e6f4.
Proof. vm_refl. Qed.
Lemma D_3e6f4 : decode_any W_3e6f4 = Some (Fcmp F_EQ FMT_D 11 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e6f8 : bv 32 := 0x02058663.
Lemma F_3e6f8 : fetch_word Plain.M.loaded_segments (0x3e740 : word) = Some W_3e6f8.
Proof. vm_refl. Qed.
Lemma D_3e6f8 : decode_any W_3e6f8 = Some (Branch BC_EQ 11 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e6fc : bv 32 := 0x00043503.
Lemma F_3e6fc : fetch_word Plain.M.loaded_segments (0x3e744 : word) = Some W_3e6fc.
Proof. vm_refl. Qed.
Lemma D_3e6fc : decode_any W_3e6fc = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e700 : bv 32 := 0x03000593.
Lemma F_3e700 : fetch_word Plain.M.loaded_segments (0x3e748 : word) = Some W_3e700.
Proof. vm_refl. Qed.
Lemma D_3e700 : decode_any W_3e700 = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e704 : bv 32 := 0x4f9270ef.
Lemma F_3e704 : fetch_word Plain.M.loaded_segments (0x3e74c : word) = Some W_3e704.
Proof. vm_refl. Qed.
Lemma D_3e704 : decode_any W_3e704 = Some (Jal 1 163064, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e708 : bv 32 := 0x00043503.
Lemma F_3e708 : fetch_word Plain.M.loaded_segments (0x3e750 : word) = Some W_3e708.
Proof. vm_refl. Qed.
Lemma D_3e708 : decode_any W_3e708 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e70c : bv 32 := 0x02e00593.
Lemma F_3e70c : fetch_word Plain.M.loaded_segments (0x3e754 : word) = Some W_3e70c.
Proof. vm_refl. Qed.
Lemma D_3e70c : decode_any W_3e70c = Some (OpImm ALU_ADD 11 0 46, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e710 : bv 32 := 0x4ed270ef.
Lemma F_3e710 : fetch_word Plain.M.loaded_segments (0x3e758 : word) = Some W_3e710.
Proof. vm_refl. Qed.
Lemma D_3e710 : decode_any W_3e710 = Some (Jal 1 163052, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e714 : bv 32 := 0x00043503.
Lemma F_3e714 : fetch_word Plain.M.loaded_segments (0x3e75c : word) = Some W_3e714.
Proof. vm_refl. Qed.
Lemma D_3e714 : decode_any W_3e714 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e718 : bv 32 := 0x03000593.
Lemma F_3e718 : fetch_word Plain.M.loaded_segments (0x3e760 : word) = Some W_3e718.
Proof. vm_refl. Qed.
Lemma D_3e718 : decode_any W_3e718 = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e71c : bv 32 := 0x4e1270ef.
Lemma F_3e71c : fetch_word Plain.M.loaded_segments (0x3e764 : word) = Some W_3e71c.
Proof. vm_refl. Qed.
Lemma D_3e71c : decode_any W_3e71c = Some (Jal 1 163040, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e720 : bv 32 := 0x0580006f.
Lemma F_3e720 : fetch_word Plain.M.loaded_segments (0x3e768 : word) = Some W_3e720.
Proof. vm_refl. Qed.
Lemma D_3e720 : decode_any W_3e720 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e724 : bv 32 := 0x22a50453.
Lemma F_3e724 : fetch_word Plain.M.loaded_segments (0x3e76c : word) = Some W_3e724.
Proof. vm_refl. Qed.
Lemma D_3e724 : decode_any W_3e724 = Some (Fsgnj F_SGNJ FMT_D 8 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e728 : bv 32 := 0x00050493.
Lemma F_3e728 : fetch_word Plain.M.loaded_segments (0x3e770 : word) = Some W_3e728.
Proof. vm_refl. Qed.
Lemma D_3e728 : decode_any W_3e728 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e72c : bv 32 := 0x06012623.
Lemma F_3e72c : fetch_word Plain.M.loaded_segments (0x3e774 : word) = Some W_3e72c.
Proof. vm_refl. Qed.
Lemma D_3e72c : decode_any W_3e72c = Some (Store SZ4 2 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e730 : bv 32 := 0x22a52553.
Lemma F_3e730 : fetch_word Plain.M.loaded_segments (0x3e778 : word) = Some W_3e730.
Proof. vm_refl. Qed.
Lemma D_3e730 : decode_any W_3e730 = Some (Fsgnj F_SGNJX FMT_D 10 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e734 : bv 32 := 0x00410513.
Lemma F_3e734 : fetch_word Plain.M.loaded_segments (0x3e77c : word) = Some W_3e734.
Proof. vm_refl. Qed.
Lemma D_3e734 : decode_any W_3e734 = Some (OpImm ALU_ADD 10 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e738 : bv 32 := 0x06c10593.
Lemma F_3e738 : fetch_word Plain.M.loaded_segments (0x3e780 : word) = Some W_3e738.
Proof. vm_refl. Qed.
Lemma D_3e738 : decode_any W_3e738 = Some (OpImm ALU_ADD 11 2 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e73c : bv 32 := 0x06810613.
Lemma F_3e73c : fetch_word Plain.M.loaded_segments (0x3e784 : word) = Some W_3e73c.
Proof. vm_refl. Qed.
Lemma D_3e73c : decode_any W_3e73c = Some (OpImm ALU_ADD 12 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e740 : bv 32 := 0xa98ff0ef.
Lemma F_3e740 : fetch_word Plain.M.loaded_segments (0x3e788 : word) = Some W_3e740.
Proof. vm_refl. Qed.
Lemma D_3e740 : decode_any W_3e740 = Some (Jal 1 2093720, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e744 : bv 32 := 0x04050863.
Lemma F_3e744 : fetch_word Plain.M.loaded_segments (0x3e78c : word) = Some W_3e744.
Proof. vm_refl. Qed.
Lemma D_3e744 : decode_any W_3e744 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e748 : bv 32 := 0xe2040553.
Lemma F_3e748 : fetch_word Plain.M.loaded_segments (0x3e790 : word) = Some W_3e748.
Proof. vm_refl. Qed.
Lemma D_3e748 : decode_any W_3e748 = Some (Fmv FMV_X_F FMT_D 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e74c : bv 32 := 0x00055863.
Lemma F_3e74c : fetch_word Plain.M.loaded_segments (0x3e794 : word) = Some W_3e74c.
Proof. vm_refl. Qed.
Lemma D_3e74c : decode_any W_3e74c = Some (Branch BC_GE 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e750 : bv 32 := 0x00043503.
Lemma F_3e750 : fetch_word Plain.M.loaded_segments (0x3e798 : word) = Some W_3e750.
Proof. vm_refl. Qed.
Lemma D_3e750 : decode_any W_3e750 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e754 : bv 32 := 0x02d00593.
Lemma F_3e754 : fetch_word Plain.M.loaded_segments (0x3e79c : word) = Some W_3e754.
Proof. vm_refl. Qed.
Lemma D_3e754 : decode_any W_3e754 = Some (OpImm ALU_ADD 11 0 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e758 : bv 32 := 0x4a5270ef.
Lemma F_3e758 : fetch_word Plain.M.loaded_segments (0x3e7a0 : word) = Some W_3e758.
Proof. vm_refl. Qed.
Lemma D_3e758 : decode_any W_3e758 = Some (Jal 1 162980, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e75c : bv 32 := 0x06c12583.
Lemma F_3e75c : fetch_word Plain.M.loaded_segments (0x3e7a4 : word) = Some W_3e75c.
Proof. vm_refl. Qed.
Lemma D_3e75c : decode_any W_3e75c = Some (Load SZ4 true 11 2 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e760 : bv 32 := 0x06812603.
Lemma F_3e760 : fetch_word Plain.M.loaded_segments (0x3e7a8 : word) = Some W_3e760.
Proof. vm_refl. Qed.
Lemma D_3e760 : decode_any W_3e760 = Some (Load SZ4 true 12 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e764 : bv 32 := 0x00410513.
Lemma F_3e764 : fetch_word Plain.M.loaded_segments (0x3e7ac : word) = Some W_3e764.
Proof. vm_refl. Qed.
Lemma D_3e764 : decode_any W_3e764 = Some (OpImm ALU_ADD 10 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e768 : bv 32 := 0xffc00693.
Lemma F_3e768 : fetch_word Plain.M.loaded_segments (0x3e7b0 : word) = Some W_3e768.
Proof. vm_refl. Qed.
Lemma D_3e768 : decode_any W_3e768 = Some (OpImm ALU_ADD 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e76c : bv 32 := 0x01100713.
Lemma F_3e76c : fetch_word Plain.M.loaded_segments (0x3e7b4 : word) = Some W_3e76c.
Proof. vm_refl. Qed.
Lemma D_3e76c : decode_any W_3e76c = Some (OpImm ALU_ADD 14 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e770 : bv 32 := 0x00040793.
Lemma F_3e770 : fetch_word Plain.M.loaded_segments (0x3e7b8 : word) = Some W_3e770.
Proof. vm_refl. Qed.
Lemma D_3e770 : decode_any W_3e770 = Some (OpImm ALU_ADD 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e774 : bv 32 := 0xd10ff0ef.
Lemma F_3e774 : fetch_word Plain.M.loaded_segments (0x3e7bc : word) = Some W_3e774.
Proof. vm_refl. Qed.
Lemma D_3e774 : decode_any W_3e774 = Some (Jal 1 2094352, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e778 : bv 32 := 0x00100513.
Lemma F_3e778 : fetch_word Plain.M.loaded_segments (0x3e7c0 : word) = Some W_3e778.
Proof. vm_refl. Qed.
Lemma D_3e778 : decode_any W_3e778 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e77c : bv 32 := 0x08813083.
Lemma F_3e77c : fetch_word Plain.M.loaded_segments (0x3e7c4 : word) = Some W_3e77c.
Proof. vm_refl. Qed.
Lemma D_3e77c : decode_any W_3e77c = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e780 : bv 32 := 0x08013403.
Lemma F_3e780 : fetch_word Plain.M.loaded_segments (0x3e7c8 : word) = Some W_3e780.
Proof. vm_refl. Qed.
Lemma D_3e780 : decode_any W_3e780 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e784 : bv 32 := 0x07813483.
Lemma F_3e784 : fetch_word Plain.M.loaded_segments (0x3e7cc : word) = Some W_3e784.
Proof. vm_refl. Qed.
Lemma D_3e784 : decode_any W_3e784 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e788 : bv 32 := 0x07013407.
Lemma F_3e788 : fetch_word Plain.M.loaded_segments (0x3e7d0 : word) = Some W_3e788.
Proof. vm_refl. Qed.
Lemma D_3e788 : decode_any W_3e788 = Some (FLoad FMT_D 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e78c : bv 32 := 0x09010113.
Lemma F_3e78c : fetch_word Plain.M.loaded_segments (0x3e7d4 : word) = Some W_3e78c.
Proof. vm_refl. Qed.
Lemma D_3e78c : decode_any W_3e78c = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e790 : bv 32 := 0x00008067.
Lemma F_3e790 : fetch_word Plain.M.loaded_segments (0x3e7d8 : word) = Some W_3e790.
Proof. vm_refl. Qed.
Lemma D_3e790 : decode_any W_3e790 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e794 : bv 32 := 0x22840553.
Lemma F_3e794 : fetch_word Plain.M.loaded_segments (0x3e7dc : word) = Some W_3e794.
Proof. vm_refl. Qed.
Lemma D_3e794 : decode_any W_3e794 = Some (Fsgnj F_SGNJ FMT_D 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e798 : bv 32 := 0x00048513.
Lemma F_3e798 : fetch_word Plain.M.loaded_segments (0x3e7e0 : word) = Some W_3e798.
Proof. vm_refl. Qed.
Lemma D_3e798 : decode_any W_3e798 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e79c : bv 32 := 0x00040593.
Lemma F_3e79c : fetch_word Plain.M.loaded_segments (0x3e7e4 : word) = Some W_3e79c.
Proof. vm_refl. Qed.
Lemma D_3e79c : decode_any W_3e79c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7a0 : bv 32 := 0x00000613.
Lemma F_3e7a0 : fetch_word Plain.M.loaded_segments (0x3e7e8 : word) = Some W_3e7a0.
Proof. vm_refl. Qed.
Lemma D_3e7a0 : decode_any W_3e7a0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7a4 : bv 32 := 0x008000ef.
Lemma F_3e7a4 : fetch_word Plain.M.loaded_segments (0x3e7ec : word) = Some W_3e7a4.
Proof. vm_refl. Qed.
Lemma D_3e7a4 : decode_any W_3e7a4 = Some (Jal 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3e7a8 : bv 32 := 0xfd5ff06f.
Lemma F_3e7a8 : fetch_word Plain.M.loaded_segments (0x3e7f0 : word) = Some W_3e7a8.
Proof. vm_refl. Qed.
Lemma D_3e7a8 : decode_any W_3e7a8 = Some (Jal 0 2097108, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3e05c_3e130.
Module Ns0_code_447f0_447f4.
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

Definition W_447f0 : bv 32 := 0x0005cc03.
Lemma F_447f0 : fetch_word Plain.M.loaded_segments (0x44838 : word) = Some W_447f0.
Proof. vm_refl. Qed.
Lemma D_447f0 : decode_any W_447f0 = Some (Load SZ1 false 24 11 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_447f0_447f4.
Module Ns0_code_448ec_448f0.
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

Definition W_448ec : bv 32 := 0x00008067.
Lemma F_448ec : fetch_word Plain.M.loaded_segments (0x44934 : word) = Some W_448ec.
Proof. vm_refl. Qed.
Lemma D_448ec : decode_any W_448ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_448ec_448f0.
Module Ns0_code_r40db0_40f78.
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

Definition W_465f4 : bv 32 := 0xf9010113.
Lemma F_465f4 : fetch_word Plain.M.loaded_segments (0x4663c : word) = Some W_465f4.
Proof. vm_refl. Qed.
Lemma D_465f4 : decode_any W_465f4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_465f8 : bv 32 := 0x06113423.
Lemma F_465f8 : fetch_word Plain.M.loaded_segments (0x46640 : word) = Some W_465f8.
Proof. vm_refl. Qed.
Lemma D_465f8 : decode_any W_465f8 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_465fc : bv 32 := 0x06813023.
Lemma F_465fc : fetch_word Plain.M.loaded_segments (0x46644 : word) = Some W_465fc.
Proof. vm_refl. Qed.
Lemma D_465fc : decode_any W_465fc = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_46600 : bv 32 := 0x04913c23.
Lemma F_46600 : fetch_word Plain.M.loaded_segments (0x46648 : word) = Some W_46600.
Proof. vm_refl. Qed.
Lemma D_46600 : decode_any W_46600 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_46604 : bv 32 := 0x05213823.
Lemma F_46604 : fetch_word Plain.M.loaded_segments (0x4664c : word) = Some W_46604.
Proof. vm_refl. Qed.
Lemma D_46604 : decode_any W_46604 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_46608 : bv 32 := 0x05313423.
Lemma F_46608 : fetch_word Plain.M.loaded_segments (0x46650 : word) = Some W_46608.
Proof. vm_refl. Qed.
Lemma D_46608 : decode_any W_46608 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4660c : bv 32 := 0x05413023.
Lemma F_4660c : fetch_word Plain.M.loaded_segments (0x46654 : word) = Some W_4660c.
Proof. vm_refl. Qed.
Lemma D_4660c : decode_any W_4660c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_46610 : bv 32 := 0x03513c23.
Lemma F_46610 : fetch_word Plain.M.loaded_segments (0x46658 : word) = Some W_46610.
Proof. vm_refl. Qed.
Lemma D_46610 : decode_any W_46610 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_46614 : bv 32 := 0x03613823.
Lemma F_46614 : fetch_word Plain.M.loaded_segments (0x4665c : word) = Some W_46614.
Proof. vm_refl. Qed.
Lemma D_46614 : decode_any W_46614 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_46618 : bv 32 := 0x00068493.
Lemma F_46618 : fetch_word Plain.M.loaded_segments (0x46660 : word) = Some W_46618.
Proof. vm_refl. Qed.
Lemma D_46618 : decode_any W_46618 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4661c : bv 32 := 0x00058913.
Lemma F_4661c : fetch_word Plain.M.loaded_segments (0x46664 : word) = Some W_4661c.
Proof. vm_refl. Qed.
Lemma D_4661c : decode_any W_4661c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46620 : bv 32 := 0x00050413.
Lemma F_46620 : fetch_word Plain.M.loaded_segments (0x46668 : word) = Some W_46620.
Proof. vm_refl. Qed.
Lemma D_46620 : decode_any W_46620 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46624 : bv 32 := 0x00c52503.
Lemma F_46624 : fetch_word Plain.M.loaded_segments (0x4666c : word) = Some W_46624.
Proof. vm_refl. Qed.
Lemma D_46624 : decode_any W_46624 = Some (Load SZ4 true 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_46628 : bv 32 := 0x14042583.
Lemma F_46628 : fetch_word Plain.M.loaded_segments (0x46670 : word) = Some W_46628.
Proof. vm_refl. Qed.
Lemma D_46628 : decode_any W_46628 = Some (Load SZ4 true 11 8 320, 4%Z).
Proof. vm_refl. Qed.

Definition W_4662c : bv 32 := 0x00150693.
Lemma F_4662c : fetch_word Plain.M.loaded_segments (0x46674 : word) = Some W_4662c.
Proof. vm_refl. Qed.
Lemma D_4662c : decode_any W_4662c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_46630 : bv 32 := 0x00d42623.
Lemma F_46630 : fetch_word Plain.M.loaded_segments (0x46678 : word) = Some W_46630.
Proof. vm_refl. Qed.
Lemma D_46630 : decode_any W_46630 = Some (Store SZ4 8 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_46634 : bv 32 := 0x16b55863.
Lemma F_46634 : fetch_word Plain.M.loaded_segments (0x4667c : word) = Some W_46634.
Proof. vm_refl. Qed.
Lemma D_46634 : decode_any W_46634 = Some (Branch BC_GE 10 11 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_46638 : bv 32 := 0x00040513.
Lemma F_46638 : fetch_word Plain.M.loaded_segments (0x46680 : word) = Some W_46638.
Proof. vm_refl. Qed.
Lemma D_46638 : decode_any W_46638 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4663c : bv 32 := 0x00060593.
Lemma F_4663c : fetch_word Plain.M.loaded_segments (0x46684 : word) = Some W_4663c.
Proof. vm_refl. Qed.
Lemma D_4663c : decode_any W_4663c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46640 : bv 32 := 0x00048613.
Lemma F_46640 : fetch_word Plain.M.loaded_segments (0x46688 : word) = Some W_46640.
Proof. vm_refl. Qed.
Lemma D_46640 : decode_any W_46640 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46644 : bv 32 := 0x44c000ef.
Lemma F_46644 : fetch_word Plain.M.loaded_segments (0x4668c : word) = Some W_46644.
Proof. vm_refl. Qed.
Lemma D_46644 : decode_any W_46644 = Some (Jal 1 1100, 4%Z).
Proof. vm_refl. Qed.

Definition W_46648 : bv 32 := 0x00844583.
Lemma F_46648 : fetch_word Plain.M.loaded_segments (0x46690 : word) = Some W_46648.
Proof. vm_refl. Qed.
Lemma D_46648 : decode_any W_46648 = Some (Load SZ1 false 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4664c : bv 32 := 0x12058863.
Lemma F_4664c : fetch_word Plain.M.loaded_segments (0x46694 : word) = Some W_4664c.
Proof. vm_refl. Qed.
Lemma D_4664c : decode_any W_4664c = Some (Branch BC_EQ 11 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_46650 : bv 32 := 0x00050993.
Lemma F_46650 : fetch_word Plain.M.loaded_segments (0x46698 : word) = Some W_46650.
Proof. vm_refl. Qed.
Lemma D_46650 : decode_any W_46650 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46654 : bv 32 := 0x18043a83.
Lemma F_46654 : fetch_word Plain.M.loaded_segments (0x4669c : word) = Some W_46654.
Proof. vm_refl. Qed.
Lemma D_46654 : decode_any W_46654 = Some (Load SZ8 true 21 8 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_46658 : bv 32 := 0x18843583.
Lemma F_46658 : fetch_word Plain.M.loaded_segments (0x466a0 : word) = Some W_46658.
Proof. vm_refl. Qed.
Lemma D_46658 : decode_any W_46658 = Some (Load SZ8 true 11 8 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_4665c : bv 32 := 0x00bafe63.
Lemma F_4665c : fetch_word Plain.M.loaded_segments (0x466a4 : word) = Some W_4665c.
Proof. vm_refl. Qed.
Lemma D_4665c : decode_any W_4665c = Some (Branch BC_GEU 21 11 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_46660 : bv 32 := 0x00200513.
Lemma F_46660 : fetch_word Plain.M.loaded_segments (0x466a8 : word) = Some W_46660.
Proof. vm_refl. Qed.
Lemma D_46660 : decode_any W_46660 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_46664 : bv 32 := 0x00aaa023.
Lemma F_46664 : fetch_word Plain.M.loaded_segments (0x466ac : word) = Some W_46664.
Proof. vm_refl. Qed.
Lemma D_46664 : decode_any W_46664 = Some (Store SZ4 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46668 : bv 32 := 0x013ab423.
Lemma F_46668 : fetch_word Plain.M.loaded_segments (0x466b0 : word) = Some W_46668.
Proof. vm_refl. Qed.
Lemma D_46668 : decode_any W_46668 = Some (Store SZ8 21 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4666c : bv 32 := 0x000ab823.
Lemma F_4666c : fetch_word Plain.M.loaded_segments (0x466b4 : word) = Some W_4666c.
Proof. vm_refl. Qed.
Lemma D_4666c : decode_any W_4666c = Some (Store SZ8 21 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_46670 : bv 32 := 0x018a8a93.
Lemma F_46670 : fetch_word Plain.M.loaded_segments (0x466b8 : word) = Some W_46670.
Proof. vm_refl. Qed.
Lemma D_46670 : decode_any W_46670 = Some (OpImm ALU_ADD 21 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_46674 : bv 32 := 0x0d40006f.
Lemma F_46674 : fetch_word Plain.M.loaded_segments (0x466bc : word) = Some W_46674.
Proof. vm_refl. Qed.
Lemma D_46674 : decode_any W_46674 = Some (Jal 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_46678 : bv 32 := 0x17840513.
Lemma F_46678 : fetch_word Plain.M.loaded_segments (0x466c0 : word) = Some W_46678.
Proof. vm_refl. Qed.
Lemma D_46678 : decode_any W_46678 = Some (OpImm ALU_ADD 10 8 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_4667c : bv 32 := 0x00053603.
Lemma F_4667c : fetch_word Plain.M.loaded_segments (0x466c4 : word) = Some W_4667c.
Proof. vm_refl. Qed.
Lemma D_4667c : decode_any W_4667c = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46680 : bv 32 := 0xfffcd697.
Lemma F_46680 : fetch_word Plain.M.loaded_segments (0x466c8 : word) = Some W_46680.
Proof. vm_refl. Qed.
Lemma D_46680 : decode_any W_46680 = Some (Auipc 13 1048525, 4%Z).
Proof. vm_refl. Qed.

Definition W_46684 : bv 32 := 0xfffcd797.
Lemma F_46684 : fetch_word Plain.M.loaded_segments (0x466cc : word) = Some W_46684.
Proof. vm_refl. Qed.
Lemma D_46684 : decode_any W_46684 = Some (Auipc 15 1048525, 4%Z).
Proof. vm_refl. Qed.

Definition W_46688 : bv 32 := 0x1686b703.
Lemma F_46688 : fetch_word Plain.M.loaded_segments (0x466d0 : word) = Some W_46688.
Proof. vm_refl. Qed.
Lemma D_46688 : decode_any W_46688 = Some (Load SZ8 true 14 13 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_4668c : bv 32 := 0x40ca8a33.
Lemma F_4668c : fetch_word Plain.M.loaded_segments (0x466d4 : word) = Some W_4668c.
Proof. vm_refl. Qed.
Lemma D_4668c : decode_any W_4668c = Some (Op ALU_SUB 20 21 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_46690 : bv 32 := 0x16c7b783.
Lemma F_46690 : fetch_word Plain.M.loaded_segments (0x466d8 : word) = Some W_46690.
Proof. vm_refl. Qed.
Lemma D_46690 : decode_any W_46690 = Some (Load SZ8 true 15 15 364, 4%Z).
Proof. vm_refl. Qed.

Definition W_46694 : bv 32 := 0x403a5693.
Lemma F_46694 : fetch_word Plain.M.loaded_segments (0x466dc : word) = Some W_46694.
Proof. vm_refl. Qed.
Lemma D_46694 : decode_any W_46694 = Some (ShiftImm ALU_SRA 13 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_46698 : bv 32 := 0x02e686b3.
Lemma F_46698 : fetch_word Plain.M.loaded_segments (0x466e0 : word) = Some W_46698.
Proof. vm_refl. Qed.
Lemma D_46698 : decode_any W_46698 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4669c : bv 32 := 0x00168693.
Lemma F_4669c : fetch_word Plain.M.loaded_segments (0x466e4 : word) = Some W_4669c.
Proof. vm_refl. Qed.
Lemma D_4669c : decode_any W_4669c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_466a0 : bv 32 := 0x10f6fc63.
Lemma F_466a0 : fetch_word Plain.M.loaded_segments (0x466e8 : word) = Some W_466a0.
Proof. vm_refl. Qed.
Lemma D_466a0 : decode_any W_466a0 = Some (Branch BC_GEU 13 15 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_466a4 : bv 32 := 0x40c585b3.
Lemma F_466a4 : fetch_word Plain.M.loaded_segments (0x466ec : word) = Some W_466a4.
Proof. vm_refl. Qed.
Lemma D_466a4 : decode_any W_466a4 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_466a8 : bv 32 := 0x4035d593.
Lemma F_466a8 : fetch_word Plain.M.loaded_segments (0x466f0 : word) = Some W_466a8.
Proof. vm_refl. Qed.
Lemma D_466a8 : decode_any W_466a8 = Some (ShiftImm ALU_SRA 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_466ac : bv 32 := 0x02e58633.
Lemma F_466ac : fetch_word Plain.M.loaded_segments (0x466f4 : word) = Some W_466ac.
Proof. vm_refl. Qed.
Lemma D_466ac : decode_any W_466ac = Some (Mul M_MUL 12 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_466b0 : bv 32 := 0x00161593.
Lemma F_466b0 : fetch_word Plain.M.loaded_segments (0x466f8 : word) = Some W_466b0.
Proof. vm_refl. Qed.
Lemma D_466b0 : decode_any W_466b0 = Some (ShiftImm ALU_SLL 11 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_466b4 : bv 32 := 0x00b6e463.
Lemma F_466b4 : fetch_word Plain.M.loaded_segments (0x466fc : word) = Some W_466b4.
Proof. vm_refl. Qed.
Lemma D_466b4 : decode_any W_466b4 = Some (Branch BC_LTU 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_466b8 : bv 32 := 0x00068593.
Lemma F_466b8 : fetch_word Plain.M.loaded_segments (0x46700 : word) = Some W_466b8.
Proof. vm_refl. Qed.
Lemma D_466b8 : decode_any W_466b8 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_466bc : bv 32 := 0xfffcd697.
Lemma F_466bc : fetch_word Plain.M.loaded_segments (0x46704 : word) = Some W_466bc.
Proof. vm_refl. Qed.
Lemma D_466bc : decode_any W_466bc = Some (Auipc 13 1048525, 4%Z).
Proof. vm_refl. Qed.

Definition W_466c0 : bv 32 := 0x14c6b683.
Lemma F_466c0 : fetch_word Plain.M.loaded_segments (0x46708 : word) = Some W_466c0.
Proof. vm_refl. Qed.
Lemma D_466c0 : decode_any W_466c0 = Some (Load SZ8 true 13 13 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_466c4 : bv 32 := 0x00d66663.
Lemma F_466c4 : fetch_word Plain.M.loaded_segments (0x4670c : word) = Some W_466c4.
Proof. vm_refl. Qed.
Lemma D_466c4 : decode_any W_466c4 = Some (Branch BC_LTU 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_466c8 : bv 32 := 0xfffcd597.
Lemma F_466c8 : fetch_word Plain.M.loaded_segments (0x46710 : word) = Some W_466c8.
Proof. vm_refl. Qed.
Lemma D_466c8 : decode_any W_466c8 = Some (Auipc 11 1048525, 4%Z).
Proof. vm_refl. Qed.

Definition W_466cc : bv 32 := 0x1605b583.
Lemma F_466cc : fetch_word Plain.M.loaded_segments (0x46714 : word) = Some W_466cc.
Proof. vm_refl. Qed.
Lemma D_466cc : decode_any W_466cc = Some (Load SZ8 true 11 11 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_466d0 : bv 32 := 0x02a13423.
Lemma F_466d0 : fetch_word Plain.M.loaded_segments (0x46718 : word) = Some W_466d0.
Proof. vm_refl. Qed.
Lemma D_466d0 : decode_any W_466d0 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_466d4 : bv 32 := 0xc89fe0ef.
Lemma F_466d4 : fetch_word Plain.M.loaded_segments (0x4671c : word) = Some W_466d4.
Proof. vm_refl. Qed.
Lemma D_466d4 : decode_any W_466d4 = Some (Jal 1 2092168, 4%Z).
Proof. vm_refl. Qed.

Definition W_466d8 : bv 32 := 0x17843683.
Lemma F_466d8 : fetch_word Plain.M.loaded_segments (0x46720 : word) = Some W_466d8.
Proof. vm_refl. Qed.
Lemma D_466d8 : decode_any W_466d8 = Some (Load SZ8 true 13 8 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_466dc : bv 32 := 0x18043603.
Lemma F_466dc : fetch_word Plain.M.loaded_segments (0x46724 : word) = Some W_466dc.
Proof. vm_refl. Qed.
Lemma D_466dc : decode_any W_466dc = Some (Load SZ8 true 12 8 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_466e0 : bv 32 := 0x01450a33.
Lemma F_466e0 : fetch_word Plain.M.loaded_segments (0x46728 : word) = Some W_466e0.
Proof. vm_refl. Qed.
Lemma D_466e0 : decode_any W_466e0 = Some (Op ALU_ADD 20 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_466e4 : bv 32 := 0x00359713.
Lemma F_466e4 : fetch_word Plain.M.loaded_segments (0x4672c : word) = Some W_466e4.
Proof. vm_refl. Qed.
Lemma D_466e4 : decode_any W_466e4 = Some (ShiftImm ALU_SLL 14 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_466e8 : bv 32 := 0x00559593.
Lemma F_466e8 : fetch_word Plain.M.loaded_segments (0x46730 : word) = Some W_466e8.
Proof. vm_refl. Qed.
Lemma D_466e8 : decode_any W_466e8 = Some (ShiftImm ALU_SLL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_466ec : bv 32 := 0x40e585b3.
Lemma F_466ec : fetch_word Plain.M.loaded_segments (0x46734 : word) = Some W_466ec.
Proof. vm_refl. Qed.
Lemma D_466ec : decode_any W_466ec = Some (Op ALU_SUB 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_466f0 : bv 32 := 0x00200713.
Lemma F_466f0 : fetch_word Plain.M.loaded_segments (0x46738 : word) = Some W_466f0.
Proof. vm_refl. Qed.
Lemma D_466f0 : decode_any W_466f0 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_466f4 : bv 32 := 0x00ea2023.
Lemma F_466f4 : fetch_word Plain.M.loaded_segments (0x4673c : word) = Some W_466f4.
Proof. vm_refl. Qed.
Lemma D_466f4 : decode_any W_466f4 = Some (Store SZ4 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_466f8 : bv 32 := 0x013a3423.
Lemma F_466f8 : fetch_word Plain.M.loaded_segments (0x46740 : word) = Some W_466f8.
Proof. vm_refl. Qed.
Lemma D_466f8 : decode_any W_466f8 = Some (Store SZ8 20 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_466fc : bv 32 := 0x000a3823.
Lemma F_466fc : fetch_word Plain.M.loaded_segments (0x46744 : word) = Some W_466fc.
Proof. vm_refl. Qed.
Lemma D_466fc : decode_any W_466fc = Some (Store SZ8 20 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_46700 : bv 32 := 0x00b50b33.
Lemma F_46700 : fetch_word Plain.M.loaded_segments (0x46748 : word) = Some W_46700.
Proof. vm_refl. Qed.
Lemma D_46700 : decode_any W_46700 = Some (Op ALU_ADD 22 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_46704 : bv 32 := 0x40d60633.
Lemma F_46704 : fetch_word Plain.M.loaded_segments (0x4674c : word) = Some W_46704.
Proof. vm_refl. Qed.
Lemma D_46704 : decode_any W_46704 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_46708 : bv 32 := 0x018a0a93.
Lemma F_46708 : fetch_word Plain.M.loaded_segments (0x46750 : word) = Some W_46708.
Proof. vm_refl. Qed.
Lemma D_46708 : decode_any W_46708 = Some (OpImm ALU_ADD 21 20 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4670c : bv 32 := 0x40ca0a33.
Lemma F_4670c : fetch_word Plain.M.loaded_segments (0x46754 : word) = Some W_4670c.
Proof. vm_refl. Qed.
Lemma D_4670c : decode_any W_4670c = Some (Op ALU_SUB 20 20 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_46710 : bv 32 := 0x000a0513.
Lemma F_46710 : fetch_word Plain.M.loaded_segments (0x46758 : word) = Some W_46710.
Proof. vm_refl. Qed.
Lemma D_46710 : decode_any W_46710 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46714 : bv 32 := 0x00068593.
Lemma F_46714 : fetch_word Plain.M.loaded_segments (0x4675c : word) = Some W_46714.
Proof. vm_refl. Qed.
Lemma D_46714 : decode_any W_46714 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46718 : bv 32 := 0x218730ef.
Lemma F_46718 : fetch_word Plain.M.loaded_segments (0x46760 : word) = Some W_46718.
Proof. vm_refl. Qed.
Lemma D_46718 : decode_any W_46718 = Some (Jal 1 471576, 4%Z).
Proof. vm_refl. Qed.

Definition W_4671c : bv 32 := 0x17843503.
Lemma F_4671c : fetch_word Plain.M.loaded_segments (0x46764 : word) = Some W_4671c.
Proof. vm_refl. Qed.
Lemma D_4671c : decode_any W_4671c = Some (Load SZ8 true 10 8 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_46720 : bv 32 := 0x18843583.
Lemma F_46720 : fetch_word Plain.M.loaded_segments (0x46768 : word) = Some W_46720.
Proof. vm_refl. Qed.
Lemma D_46720 : decode_any W_46720 = Some (Load SZ8 true 11 8 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_46724 : bv 32 := 0x17443c23.
Lemma F_46724 : fetch_word Plain.M.loaded_segments (0x4676c : word) = Some W_46724.
Proof. vm_refl. Qed.
Lemma D_46724 : decode_any W_46724 = Some (Store SZ8 8 20 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_46728 : bv 32 := 0x19543023.
Lemma F_46728 : fetch_word Plain.M.loaded_segments (0x46770 : word) = Some W_46728.
Proof. vm_refl. Qed.
Lemma D_46728 : decode_any W_46728 = Some (Store SZ8 8 21 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_4672c : bv 32 := 0x19643423.
Lemma F_4672c : fetch_word Plain.M.loaded_segments (0x46774 : word) = Some W_4672c.
Proof. vm_refl. Qed.
Lemma D_4672c : decode_any W_4672c = Some (Store SZ8 8 22 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_46730 : bv 32 := 0x00a13423.
Lemma F_46730 : fetch_word Plain.M.loaded_segments (0x46778 : word) = Some W_46730.
Proof. vm_refl. Qed.
Lemma D_46730 : decode_any W_46730 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46734 : bv 32 := 0x00a13823.
Lemma F_46734 : fetch_word Plain.M.loaded_segments (0x4677c : word) = Some W_46734.
Proof. vm_refl. Qed.
Lemma D_46734 : decode_any W_46734 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_46738 : bv 32 := 0x00a13c23.
Lemma F_46738 : fetch_word Plain.M.loaded_segments (0x46780 : word) = Some W_46738.
Proof. vm_refl. Qed.
Lemma D_46738 : decode_any W_46738 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4673c : bv 32 := 0x02b13023.
Lemma F_4673c : fetch_word Plain.M.loaded_segments (0x46784 : word) = Some W_4673c.
Proof. vm_refl. Qed.
Lemma D_4673c : decode_any W_4673c = Some (Store SZ8 2 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_46740 : bv 32 := 0x00810513.
Lemma F_46740 : fetch_word Plain.M.loaded_segments (0x46788 : word) = Some W_46740.
Proof. vm_refl. Qed.
Lemma D_46740 : decode_any W_46740 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46744 : bv 32 := 0xbadfe0ef.
Lemma F_46744 : fetch_word Plain.M.loaded_segments (0x4678c : word) = Some W_46744.
Proof. vm_refl. Qed.
Lemma D_46744 : decode_any W_46744 = Some (Jal 1 2091948, 4%Z).
Proof. vm_refl. Qed.

Definition W_46748 : bv 32 := 0x00093503.
Lemma F_46748 : fetch_word Plain.M.loaded_segments (0x46790 : word) = Some W_46748.
Proof. vm_refl. Qed.
Lemma D_46748 : decode_any W_46748 = Some (Load SZ8 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4674c : bv 32 := 0x19543023.
Lemma F_4674c : fetch_word Plain.M.loaded_segments (0x46794 : word) = Some W_4674c.
Proof. vm_refl. Qed.
Lemma D_4674c : decode_any W_4674c = Some (Store SZ8 8 21 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_46750 : bv 32 := 0x01053783.
Lemma F_46750 : fetch_word Plain.M.loaded_segments (0x46798 : word) = Some W_46750.
Proof. vm_refl. Qed.
Lemma D_46750 : decode_any W_46750 = Some (Load SZ8 true 15 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_46754 : bv 32 := 0x00090513.
Lemma F_46754 : fetch_word Plain.M.loaded_segments (0x4679c : word) = Some W_46754.
Proof. vm_refl. Qed.
Lemma D_46754 : decode_any W_46754 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46758 : bv 32 := 0x00098593.
Lemma F_46758 : fetch_word Plain.M.loaded_segments (0x467a0 : word) = Some W_46758.
Proof. vm_refl. Qed.
Lemma D_46758 : decode_any W_46758 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4675c : bv 32 := 0x00000613.
Lemma F_4675c : fetch_word Plain.M.loaded_segments (0x467a4 : word) = Some W_4675c.
Proof. vm_refl. Qed.
Lemma D_4675c : decode_any W_4675c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46760 : bv 32 := 0x00040693.
Lemma F_46760 : fetch_word Plain.M.loaded_segments (0x467a8 : word) = Some W_46760.
Proof. vm_refl. Qed.
Lemma D_46760 : decode_any W_46760 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46764 : bv 32 := 0x00048713.
Lemma F_46764 : fetch_word Plain.M.loaded_segments (0x467ac : word) = Some W_46764.
Proof. vm_refl. Qed.
Lemma D_46764 : decode_any W_46764 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46768 : bv 32 := 0x000780e7.
Lemma F_46768 : fetch_word Plain.M.loaded_segments (0x467b0 : word) = Some W_46768.
Proof. vm_refl. Qed.
Lemma D_46768 : decode_any W_46768 = Some (Jalr 1 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4676c : bv 32 := 0x01044503.
Lemma F_4676c : fetch_word Plain.M.loaded_segments (0x467b4 : word) = Some W_4676c.
Proof. vm_refl. Qed.
Lemma D_4676c : decode_any W_4676c = Some (Load SZ1 false 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_46770 : bv 32 := 0xfff54513.
Lemma F_46770 : fetch_word Plain.M.loaded_segments (0x467b8 : word) = Some W_46770.
Proof. vm_refl. Qed.
Lemma D_46770 : decode_any W_46770 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_46774 : bv 32 := 0x00157513.
Lemma F_46774 : fetch_word Plain.M.loaded_segments (0x467bc : word) = Some W_46774.
Proof. vm_refl. Qed.
Lemma D_46774 : decode_any W_46774 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_46778 : bv 32 := 0x00a40423.
Lemma F_46778 : fetch_word Plain.M.loaded_segments (0x467c0 : word) = Some W_46778.
Proof. vm_refl. Qed.
Lemma D_46778 : decode_any W_46778 = Some (Store SZ1 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4677c : bv 32 := 0x06813083.
Lemma F_4677c : fetch_word Plain.M.loaded_segments (0x467c4 : word) = Some W_4677c.
Proof. vm_refl. Qed.
Lemma D_4677c : decode_any W_4677c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_46780 : bv 32 := 0x06013403.
Lemma F_46780 : fetch_word Plain.M.loaded_segments (0x467c8 : word) = Some W_46780.
Proof. vm_refl. Qed.
Lemma D_46780 : decode_any W_46780 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_46784 : bv 32 := 0x05813483.
Lemma F_46784 : fetch_word Plain.M.loaded_segments (0x467cc : word) = Some W_46784.
Proof. vm_refl. Qed.
Lemma D_46784 : decode_any W_46784 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_46788 : bv 32 := 0x05013903.
Lemma F_46788 : fetch_word Plain.M.loaded_segments (0x467d0 : word) = Some W_46788.
Proof. vm_refl. Qed.
Lemma D_46788 : decode_any W_46788 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_4678c : bv 32 := 0x04813983.
Lemma F_4678c : fetch_word Plain.M.loaded_segments (0x467d4 : word) = Some W_4678c.
Proof. vm_refl. Qed.
Lemma D_4678c : decode_any W_4678c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_46790 : bv 32 := 0x04013a03.
Lemma F_46790 : fetch_word Plain.M.loaded_segments (0x467d8 : word) = Some W_46790.
Proof. vm_refl. Qed.
Lemma D_46790 : decode_any W_46790 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_46794 : bv 32 := 0x03813a83.
Lemma F_46794 : fetch_word Plain.M.loaded_segments (0x467dc : word) = Some W_46794.
Proof. vm_refl. Qed.
Lemma D_46794 : decode_any W_46794 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_46798 : bv 32 := 0x03013b03.
Lemma F_46798 : fetch_word Plain.M.loaded_segments (0x467e0 : word) = Some W_46798.
Proof. vm_refl. Qed.
Lemma D_46798 : decode_any W_46798 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4679c : bv 32 := 0x07010113.
Lemma F_4679c : fetch_word Plain.M.loaded_segments (0x467e4 : word) = Some W_4679c.
Proof. vm_refl. Qed.
Lemma D_4679c : decode_any W_4679c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_467a0 : bv 32 := 0x00008067.
Lemma F_467a0 : fetch_word Plain.M.loaded_segments (0x467e8 : word) = Some W_467a0.
Proof. vm_refl. Qed.
Lemma D_467a0 : decode_any W_467a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_467a4 : bv 32 := 0x00800593.
Lemma F_467a4 : fetch_word Plain.M.loaded_segments (0x467ec : word) = Some W_467a4.
Proof. vm_refl. Qed.
Lemma D_467a4 : decode_any W_467a4 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_467a8 : bv 32 := 0x00048513.
Lemma F_467a8 : fetch_word Plain.M.loaded_segments (0x467f0 : word) = Some W_467a8.
Proof. vm_refl. Qed.
Lemma D_467a8 : decode_any W_467a8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_467ac : bv 32 := 0xa60fb0ef.
Lemma F_467ac : fetch_word Plain.M.loaded_segments (0x467f4 : word) = Some W_467ac.
Proof. vm_refl. Qed.
Lemma D_467ac : decode_any W_467ac = Some (Jal 1 2077280, 4%Z).
Proof. vm_refl. Qed.

Definition W_467b0 : bv 32 := 0x00000513.
Lemma F_467b0 : fetch_word Plain.M.loaded_segments (0x467f8 : word) = Some W_467b0.
Proof. vm_refl. Qed.
Lemma D_467b0 : decode_any W_467b0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_467b4 : bv 32 := 0xfc5ff06f.
Lemma F_467b4 : fetch_word Plain.M.loaded_segments (0x467fc : word) = Some W_467b4.
Proof. vm_refl. Qed.
Lemma D_467b4 : decode_any W_467b4 = Some (Jal 0 2097092, 4%Z).
Proof. vm_refl. Qed.

Definition W_467b8 : bv 32 := 0xb91fe0ef.
Lemma F_467b8 : fetch_word Plain.M.loaded_segments (0x46800 : word) = Some W_467b8.
Proof. vm_refl. Qed.
Lemma D_467b8 : decode_any W_467b8 = Some (Jal 1 2091920, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r40db0_40f78.
Module Ns0_code_r40be8_40db0.
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

Definition W_4642c : bv 32 := 0xf9010113.
Lemma F_4642c : fetch_word Plain.M.loaded_segments (0x46474 : word) = Some W_4642c.
Proof. vm_refl. Qed.
Lemma D_4642c : decode_any W_4642c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_46430 : bv 32 := 0x06113423.
Lemma F_46430 : fetch_word Plain.M.loaded_segments (0x46478 : word) = Some W_46430.
Proof. vm_refl. Qed.
Lemma D_46430 : decode_any W_46430 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_46434 : bv 32 := 0x06813023.
Lemma F_46434 : fetch_word Plain.M.loaded_segments (0x4647c : word) = Some W_46434.
Proof. vm_refl. Qed.
Lemma D_46434 : decode_any W_46434 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_46438 : bv 32 := 0x04913c23.
Lemma F_46438 : fetch_word Plain.M.loaded_segments (0x46480 : word) = Some W_46438.
Proof. vm_refl. Qed.
Lemma D_46438 : decode_any W_46438 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4643c : bv 32 := 0x05213823.
Lemma F_4643c : fetch_word Plain.M.loaded_segments (0x46484 : word) = Some W_4643c.
Proof. vm_refl. Qed.
Lemma D_4643c : decode_any W_4643c = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_46440 : bv 32 := 0x05313423.
Lemma F_46440 : fetch_word Plain.M.loaded_segments (0x46488 : word) = Some W_46440.
Proof. vm_refl. Qed.
Lemma D_46440 : decode_any W_46440 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_46444 : bv 32 := 0x05413023.
Lemma F_46444 : fetch_word Plain.M.loaded_segments (0x4648c : word) = Some W_46444.
Proof. vm_refl. Qed.
Lemma D_46444 : decode_any W_46444 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_46448 : bv 32 := 0x03513c23.
Lemma F_46448 : fetch_word Plain.M.loaded_segments (0x46490 : word) = Some W_46448.
Proof. vm_refl. Qed.
Lemma D_46448 : decode_any W_46448 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4644c : bv 32 := 0x03613823.
Lemma F_4644c : fetch_word Plain.M.loaded_segments (0x46494 : word) = Some W_4644c.
Proof. vm_refl. Qed.
Lemma D_4644c : decode_any W_4644c = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_46450 : bv 32 := 0x00068493.
Lemma F_46450 : fetch_word Plain.M.loaded_segments (0x46498 : word) = Some W_46450.
Proof. vm_refl. Qed.
Lemma D_46450 : decode_any W_46450 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46454 : bv 32 := 0x00058913.
Lemma F_46454 : fetch_word Plain.M.loaded_segments (0x4649c : word) = Some W_46454.
Proof. vm_refl. Qed.
Lemma D_46454 : decode_any W_46454 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46458 : bv 32 := 0x00050413.
Lemma F_46458 : fetch_word Plain.M.loaded_segments (0x464a0 : word) = Some W_46458.
Proof. vm_refl. Qed.
Lemma D_46458 : decode_any W_46458 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4645c : bv 32 := 0x00c52503.
Lemma F_4645c : fetch_word Plain.M.loaded_segments (0x464a4 : word) = Some W_4645c.
Proof. vm_refl. Qed.
Lemma D_4645c : decode_any W_4645c = Some (Load SZ4 true 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_46460 : bv 32 := 0x14042583.
Lemma F_46460 : fetch_word Plain.M.loaded_segments (0x464a8 : word) = Some W_46460.
Proof. vm_refl. Qed.
Lemma D_46460 : decode_any W_46460 = Some (Load SZ4 true 11 8 320, 4%Z).
Proof. vm_refl. Qed.

Definition W_46464 : bv 32 := 0x00150693.
Lemma F_46464 : fetch_word Plain.M.loaded_segments (0x464ac : word) = Some W_46464.
Proof. vm_refl. Qed.
Lemma D_46464 : decode_any W_46464 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_46468 : bv 32 := 0x00d42623.
Lemma F_46468 : fetch_word Plain.M.loaded_segments (0x464b0 : word) = Some W_46468.
Proof. vm_refl. Qed.
Lemma D_46468 : decode_any W_46468 = Some (Store SZ4 8 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4646c : bv 32 := 0x16b55863.
Lemma F_4646c : fetch_word Plain.M.loaded_segments (0x464b4 : word) = Some W_4646c.
Proof. vm_refl. Qed.
Lemma D_4646c : decode_any W_4646c = Some (Branch BC_GE 10 11 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_46470 : bv 32 := 0x00040513.
Lemma F_46470 : fetch_word Plain.M.loaded_segments (0x464b8 : word) = Some W_46470.
Proof. vm_refl. Qed.
Lemma D_46470 : decode_any W_46470 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46474 : bv 32 := 0x00060593.
Lemma F_46474 : fetch_word Plain.M.loaded_segments (0x464bc : word) = Some W_46474.
Proof. vm_refl. Qed.
Lemma D_46474 : decode_any W_46474 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46478 : bv 32 := 0x00048613.
Lemma F_46478 : fetch_word Plain.M.loaded_segments (0x464c0 : word) = Some W_46478.
Proof. vm_refl. Qed.
Lemma D_46478 : decode_any W_46478 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4647c : bv 32 := 0x614000ef.
Lemma F_4647c : fetch_word Plain.M.loaded_segments (0x464c4 : word) = Some W_4647c.
Proof. vm_refl. Qed.
Lemma D_4647c : decode_any W_4647c = Some (Jal 1 1556, 4%Z).
Proof. vm_refl. Qed.

Definition W_46480 : bv 32 := 0x00844583.
Lemma F_46480 : fetch_word Plain.M.loaded_segments (0x464c8 : word) = Some W_46480.
Proof. vm_refl. Qed.
Lemma D_46480 : decode_any W_46480 = Some (Load SZ1 false 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46484 : bv 32 := 0x12058863.
Lemma F_46484 : fetch_word Plain.M.loaded_segments (0x464cc : word) = Some W_46484.
Proof. vm_refl. Qed.
Lemma D_46484 : decode_any W_46484 = Some (Branch BC_EQ 11 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_46488 : bv 32 := 0x00050993.
Lemma F_46488 : fetch_word Plain.M.loaded_segments (0x464d0 : word) = Some W_46488.
Proof. vm_refl. Qed.
Lemma D_46488 : decode_any W_46488 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4648c : bv 32 := 0x18043a83.
Lemma F_4648c : fetch_word Plain.M.loaded_segments (0x464d4 : word) = Some W_4648c.
Proof. vm_refl. Qed.
Lemma D_4648c : decode_any W_4648c = Some (Load SZ8 true 21 8 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_46490 : bv 32 := 0x18843583.
Lemma F_46490 : fetch_word Plain.M.loaded_segments (0x464d8 : word) = Some W_46490.
Proof. vm_refl. Qed.
Lemma D_46490 : decode_any W_46490 = Some (Load SZ8 true 11 8 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_46494 : bv 32 := 0x00bafe63.
Lemma F_46494 : fetch_word Plain.M.loaded_segments (0x464dc : word) = Some W_46494.
Proof. vm_refl. Qed.
Lemma D_46494 : decode_any W_46494 = Some (Branch BC_GEU 21 11 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_46498 : bv 32 := 0x00300513.
Lemma F_46498 : fetch_word Plain.M.loaded_segments (0x464e0 : word) = Some W_46498.
Proof. vm_refl. Qed.
Lemma D_46498 : decode_any W_46498 = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4649c : bv 32 := 0x00aaa023.
Lemma F_4649c : fetch_word Plain.M.loaded_segments (0x464e4 : word) = Some W_4649c.
Proof. vm_refl. Qed.
Lemma D_4649c : decode_any W_4649c = Some (Store SZ4 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_464a0 : bv 32 := 0x013ab423.
Lemma F_464a0 : fetch_word Plain.M.loaded_segments (0x464e8 : word) = Some W_464a0.
Proof. vm_refl. Qed.
Lemma D_464a0 : decode_any W_464a0 = Some (Store SZ8 21 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_464a4 : bv 32 := 0x000ab823.
Lemma F_464a4 : fetch_word Plain.M.loaded_segments (0x464ec : word) = Some W_464a4.
Proof. vm_refl. Qed.
Lemma D_464a4 : decode_any W_464a4 = Some (Store SZ8 21 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_464a8 : bv 32 := 0x018a8a93.
Lemma F_464a8 : fetch_word Plain.M.loaded_segments (0x464f0 : word) = Some W_464a8.
Proof. vm_refl. Qed.
Lemma D_464a8 : decode_any W_464a8 = Some (OpImm ALU_ADD 21 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_464ac : bv 32 := 0x0d40006f.
Lemma F_464ac : fetch_word Plain.M.loaded_segments (0x464f4 : word) = Some W_464ac.
Proof. vm_refl. Qed.
Lemma D_464ac : decode_any W_464ac = Some (Jal 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_464b0 : bv 32 := 0x17840513.
Lemma F_464b0 : fetch_word Plain.M.loaded_segments (0x464f8 : word) = Some W_464b0.
Proof. vm_refl. Qed.
Lemma D_464b0 : decode_any W_464b0 = Some (OpImm ALU_ADD 10 8 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_464b4 : bv 32 := 0x00053603.
Lemma F_464b4 : fetch_word Plain.M.loaded_segments (0x464fc : word) = Some W_464b4.
Proof. vm_refl. Qed.
Lemma D_464b4 : decode_any W_464b4 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_464b8 : bv 32 := 0xfffcd697.
Lemma F_464b8 : fetch_word Plain.M.loaded_segments (0x46500 : word) = Some W_464b8.
Proof. vm_refl. Qed.
Lemma D_464b8 : decode_any W_464b8 = Some (Auipc 13 1048525, 4%Z).
Proof. vm_refl. Qed.

Definition W_464bc : bv 32 := 0xfffcd797.
Lemma F_464bc : fetch_word Plain.M.loaded_segments (0x46504 : word) = Some W_464bc.
Proof. vm_refl. Qed.
Lemma D_464bc : decode_any W_464bc = Some (Auipc 15 1048525, 4%Z).
Proof. vm_refl. Qed.

Definition W_464c0 : bv 32 := 0x3306b703.
Lemma F_464c0 : fetch_word Plain.M.loaded_segments (0x46508 : word) = Some W_464c0.
Proof. vm_refl. Qed.
Lemma D_464c0 : decode_any W_464c0 = Some (Load SZ8 true 14 13 816, 4%Z).
Proof. vm_refl. Qed.

Definition W_464c4 : bv 32 := 0x40ca8a33.
Lemma F_464c4 : fetch_word Plain.M.loaded_segments (0x4650c : word) = Some W_464c4.
Proof. vm_refl. Qed.
Lemma D_464c4 : decode_any W_464c4 = Some (Op ALU_SUB 20 21 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_464c8 : bv 32 := 0x3347b783.
Lemma F_464c8 : fetch_word Plain.M.loaded_segments (0x46510 : word) = Some W_464c8.
Proof. vm_refl. Qed.
Lemma D_464c8 : decode_any W_464c8 = Some (Load SZ8 true 15 15 820, 4%Z).
Proof. vm_refl. Qed.

Definition W_464cc : bv 32 := 0x403a5693.
Lemma F_464cc : fetch_word Plain.M.loaded_segments (0x46514 : word) = Some W_464cc.
Proof. vm_refl. Qed.
Lemma D_464cc : decode_any W_464cc = Some (ShiftImm ALU_SRA 13 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_464d0 : bv 32 := 0x02e686b3.
Lemma F_464d0 : fetch_word Plain.M.loaded_segments (0x46518 : word) = Some W_464d0.
Proof. vm_refl. Qed.
Lemma D_464d0 : decode_any W_464d0 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_464d4 : bv 32 := 0x00168693.
Lemma F_464d4 : fetch_word Plain.M.loaded_segments (0x4651c : word) = Some W_464d4.
Proof. vm_refl. Qed.
Lemma D_464d4 : decode_any W_464d4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_464d8 : bv 32 := 0x10f6fc63.
Lemma F_464d8 : fetch_word Plain.M.loaded_segments (0x46520 : word) = Some W_464d8.
Proof. vm_refl. Qed.
Lemma D_464d8 : decode_any W_464d8 = Some (Branch BC_GEU 13 15 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_464dc : bv 32 := 0x40c585b3.
Lemma F_464dc : fetch_word Plain.M.loaded_segments (0x46524 : word) = Some W_464dc.
Proof. vm_refl. Qed.
Lemma D_464dc : decode_any W_464dc = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_464e0 : bv 32 := 0x4035d593.
Lemma F_464e0 : fetch_word Plain.M.loaded_segments (0x46528 : word) = Some W_464e0.
Proof. vm_refl. Qed.
Lemma D_464e0 : decode_any W_464e0 = Some (ShiftImm ALU_SRA 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_464e4 : bv 32 := 0x02e58633.
Lemma F_464e4 : fetch_word Plain.M.loaded_segments (0x4652c : word) = Some W_464e4.
Proof. vm_refl. Qed.
Lemma D_464e4 : decode_any W_464e4 = Some (Mul M_MUL 12 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_464e8 : bv 32 := 0x00161593.
Lemma F_464e8 : fetch_word Plain.M.loaded_segments (0x46530 : word) = Some W_464e8.
Proof. vm_refl. Qed.
Lemma D_464e8 : decode_any W_464e8 = Some (ShiftImm ALU_SLL 11 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_464ec : bv 32 := 0x00b6e463.
Lemma F_464ec : fetch_word Plain.M.loaded_segments (0x46534 : word) = Some W_464ec.
Proof. vm_refl. Qed.
Lemma D_464ec : decode_any W_464ec = Some (Branch BC_LTU 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_464f0 : bv 32 := 0x00068593.
Lemma F_464f0 : fetch_word Plain.M.loaded_segments (0x46538 : word) = Some W_464f0.
Proof. vm_refl. Qed.
Lemma D_464f0 : decode_any W_464f0 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_464f4 : bv 32 := 0xfffcd697.
Lemma F_464f4 : fetch_word Plain.M.loaded_segments (0x4653c : word) = Some W_464f4.
Proof. vm_refl. Qed.
Lemma D_464f4 : decode_any W_464f4 = Some (Auipc 13 1048525, 4%Z).
Proof. vm_refl. Qed.

Definition W_464f8 : bv 32 := 0x3146b683.
Lemma F_464f8 : fetch_word Plain.M.loaded_segments (0x46540 : word) = Some W_464f8.
Proof. vm_refl. Qed.
Lemma D_464f8 : decode_any W_464f8 = Some (Load SZ8 true 13 13 788, 4%Z).
Proof. vm_refl. Qed.

Definition W_464fc : bv 32 := 0x00d66663.
Lemma F_464fc : fetch_word Plain.M.loaded_segments (0x46544 : word) = Some W_464fc.
Proof. vm_refl. Qed.
Lemma D_464fc : decode_any W_464fc = Some (Branch BC_LTU 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_46500 : bv 32 := 0xfffcd597.
Lemma F_46500 : fetch_word Plain.M.loaded_segments (0x46548 : word) = Some W_46500.
Proof. vm_refl. Qed.
Lemma D_46500 : decode_any W_46500 = Some (Auipc 11 1048525, 4%Z).
Proof. vm_refl. Qed.

Definition W_46504 : bv 32 := 0x3285b583.
Lemma F_46504 : fetch_word Plain.M.loaded_segments (0x4654c : word) = Some W_46504.
Proof. vm_refl. Qed.
Lemma D_46504 : decode_any W_46504 = Some (Load SZ8 true 11 11 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_46508 : bv 32 := 0x02a13423.
Lemma F_46508 : fetch_word Plain.M.loaded_segments (0x46550 : word) = Some W_46508.
Proof. vm_refl. Qed.
Lemma D_46508 : decode_any W_46508 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4650c : bv 32 := 0xe51fe0ef.
Lemma F_4650c : fetch_word Plain.M.loaded_segments (0x46554 : word) = Some W_4650c.
Proof. vm_refl. Qed.
Lemma D_4650c : decode_any W_4650c = Some (Jal 1 2092624, 4%Z).
Proof. vm_refl. Qed.

Definition W_46510 : bv 32 := 0x17843683.
Lemma F_46510 : fetch_word Plain.M.loaded_segments (0x46558 : word) = Some W_46510.
Proof. vm_refl. Qed.
Lemma D_46510 : decode_any W_46510 = Some (Load SZ8 true 13 8 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_46514 : bv 32 := 0x18043603.
Lemma F_46514 : fetch_word Plain.M.loaded_segments (0x4655c : word) = Some W_46514.
Proof. vm_refl. Qed.
Lemma D_46514 : decode_any W_46514 = Some (Load SZ8 true 12 8 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_46518 : bv 32 := 0x01450a33.
Lemma F_46518 : fetch_word Plain.M.loaded_segments (0x46560 : word) = Some W_46518.
Proof. vm_refl. Qed.
Lemma D_46518 : decode_any W_46518 = Some (Op ALU_ADD 20 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4651c : bv 32 := 0x00359713.
Lemma F_4651c : fetch_word Plain.M.loaded_segments (0x46564 : word) = Some W_4651c.
Proof. vm_refl. Qed.
Lemma D_4651c : decode_any W_4651c = Some (ShiftImm ALU_SLL 14 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_46520 : bv 32 := 0x00559593.
Lemma F_46520 : fetch_word Plain.M.loaded_segments (0x46568 : word) = Some W_46520.
Proof. vm_refl. Qed.
Lemma D_46520 : decode_any W_46520 = Some (ShiftImm ALU_SLL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_46524 : bv 32 := 0x40e585b3.
Lemma F_46524 : fetch_word Plain.M.loaded_segments (0x4656c : word) = Some W_46524.
Proof. vm_refl. Qed.
Lemma D_46524 : decode_any W_46524 = Some (Op ALU_SUB 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_46528 : bv 32 := 0x00300713.
Lemma F_46528 : fetch_word Plain.M.loaded_segments (0x46570 : word) = Some W_46528.
Proof. vm_refl. Qed.
Lemma D_46528 : decode_any W_46528 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4652c : bv 32 := 0x00ea2023.
Lemma F_4652c : fetch_word Plain.M.loaded_segments (0x46574 : word) = Some W_4652c.
Proof. vm_refl. Qed.
Lemma D_4652c : decode_any W_4652c = Some (Store SZ4 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46530 : bv 32 := 0x013a3423.
Lemma F_46530 : fetch_word Plain.M.loaded_segments (0x46578 : word) = Some W_46530.
Proof. vm_refl. Qed.
Lemma D_46530 : decode_any W_46530 = Some (Store SZ8 20 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46534 : bv 32 := 0x000a3823.
Lemma F_46534 : fetch_word Plain.M.loaded_segments (0x4657c : word) = Some W_46534.
Proof. vm_refl. Qed.
Lemma D_46534 : decode_any W_46534 = Some (Store SZ8 20 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_46538 : bv 32 := 0x00b50b33.
Lemma F_46538 : fetch_word Plain.M.loaded_segments (0x46580 : word) = Some W_46538.
Proof. vm_refl. Qed.
Lemma D_46538 : decode_any W_46538 = Some (Op ALU_ADD 22 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4653c : bv 32 := 0x40d60633.
Lemma F_4653c : fetch_word Plain.M.loaded_segments (0x46584 : word) = Some W_4653c.
Proof. vm_refl. Qed.
Lemma D_4653c : decode_any W_4653c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_46540 : bv 32 := 0x018a0a93.
Lemma F_46540 : fetch_word Plain.M.loaded_segments (0x46588 : word) = Some W_46540.
Proof. vm_refl. Qed.
Lemma D_46540 : decode_any W_46540 = Some (OpImm ALU_ADD 21 20 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_46544 : bv 32 := 0x40ca0a33.
Lemma F_46544 : fetch_word Plain.M.loaded_segments (0x4658c : word) = Some W_46544.
Proof. vm_refl. Qed.
Lemma D_46544 : decode_any W_46544 = Some (Op ALU_SUB 20 20 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_46548 : bv 32 := 0x000a0513.
Lemma F_46548 : fetch_word Plain.M.loaded_segments (0x46590 : word) = Some W_46548.
Proof. vm_refl. Qed.
Lemma D_46548 : decode_any W_46548 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4654c : bv 32 := 0x00068593.
Lemma F_4654c : fetch_word Plain.M.loaded_segments (0x46594 : word) = Some W_4654c.
Proof. vm_refl. Qed.
Lemma D_4654c : decode_any W_4654c = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46550 : bv 32 := 0x3e0730ef.
Lemma F_46550 : fetch_word Plain.M.loaded_segments (0x46598 : word) = Some W_46550.
Proof. vm_refl. Qed.
Lemma D_46550 : decode_any W_46550 = Some (Jal 1 472032, 4%Z).
Proof. vm_refl. Qed.

Definition W_46554 : bv 32 := 0x17843503.
Lemma F_46554 : fetch_word Plain.M.loaded_segments (0x4659c : word) = Some W_46554.
Proof. vm_refl. Qed.
Lemma D_46554 : decode_any W_46554 = Some (Load SZ8 true 10 8 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_46558 : bv 32 := 0x18843583.
Lemma F_46558 : fetch_word Plain.M.loaded_segments (0x465a0 : word) = Some W_46558.
Proof. vm_refl. Qed.
Lemma D_46558 : decode_any W_46558 = Some (Load SZ8 true 11 8 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_4655c : bv 32 := 0x17443c23.
Lemma F_4655c : fetch_word Plain.M.loaded_segments (0x465a4 : word) = Some W_4655c.
Proof. vm_refl. Qed.
Lemma D_4655c : decode_any W_4655c = Some (Store SZ8 8 20 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_46560 : bv 32 := 0x19543023.
Lemma F_46560 : fetch_word Plain.M.loaded_segments (0x465a8 : word) = Some W_46560.
Proof. vm_refl. Qed.
Lemma D_46560 : decode_any W_46560 = Some (Store SZ8 8 21 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_46564 : bv 32 := 0x19643423.
Lemma F_46564 : fetch_word Plain.M.loaded_segments (0x465ac : word) = Some W_46564.
Proof. vm_refl. Qed.
Lemma D_46564 : decode_any W_46564 = Some (Store SZ8 8 22 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_46568 : bv 32 := 0x00a13423.
Lemma F_46568 : fetch_word Plain.M.loaded_segments (0x465b0 : word) = Some W_46568.
Proof. vm_refl. Qed.
Lemma D_46568 : decode_any W_46568 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4656c : bv 32 := 0x00a13823.
Lemma F_4656c : fetch_word Plain.M.loaded_segments (0x465b4 : word) = Some W_4656c.
Proof. vm_refl. Qed.
Lemma D_4656c : decode_any W_4656c = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_46570 : bv 32 := 0x00a13c23.
Lemma F_46570 : fetch_word Plain.M.loaded_segments (0x465b8 : word) = Some W_46570.
Proof. vm_refl. Qed.
Lemma D_46570 : decode_any W_46570 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_46574 : bv 32 := 0x02b13023.
Lemma F_46574 : fetch_word Plain.M.loaded_segments (0x465bc : word) = Some W_46574.
Proof. vm_refl. Qed.
Lemma D_46574 : decode_any W_46574 = Some (Store SZ8 2 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_46578 : bv 32 := 0x00810513.
Lemma F_46578 : fetch_word Plain.M.loaded_segments (0x465c0 : word) = Some W_46578.
Proof. vm_refl. Qed.
Lemma D_46578 : decode_any W_46578 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4657c : bv 32 := 0xd75fe0ef.
Lemma F_4657c : fetch_word Plain.M.loaded_segments (0x465c4 : word) = Some W_4657c.
Proof. vm_refl. Qed.
Lemma D_4657c : decode_any W_4657c = Some (Jal 1 2092404, 4%Z).
Proof. vm_refl. Qed.

Definition W_46580 : bv 32 := 0x00093503.
Lemma F_46580 : fetch_word Plain.M.loaded_segments (0x465c8 : word) = Some W_46580.
Proof. vm_refl. Qed.
Lemma D_46580 : decode_any W_46580 = Some (Load SZ8 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46584 : bv 32 := 0x19543023.
Lemma F_46584 : fetch_word Plain.M.loaded_segments (0x465cc : word) = Some W_46584.
Proof. vm_refl. Qed.
Lemma D_46584 : decode_any W_46584 = Some (Store SZ8 8 21 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_46588 : bv 32 := 0x04853783.
Lemma F_46588 : fetch_word Plain.M.loaded_segments (0x465d0 : word) = Some W_46588.
Proof. vm_refl. Qed.
Lemma D_46588 : decode_any W_46588 = Some (Load SZ8 true 15 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4658c : bv 32 := 0x00090513.
Lemma F_4658c : fetch_word Plain.M.loaded_segments (0x465d4 : word) = Some W_4658c.
Proof. vm_refl. Qed.
Lemma D_4658c : decode_any W_4658c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46590 : bv 32 := 0x00098593.
Lemma F_46590 : fetch_word Plain.M.loaded_segments (0x465d8 : word) = Some W_46590.
Proof. vm_refl. Qed.
Lemma D_46590 : decode_any W_46590 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46594 : bv 32 := 0x00000613.
Lemma F_46594 : fetch_word Plain.M.loaded_segments (0x465dc : word) = Some W_46594.
Proof. vm_refl. Qed.
Lemma D_46594 : decode_any W_46594 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46598 : bv 32 := 0x00040693.
Lemma F_46598 : fetch_word Plain.M.loaded_segments (0x465e0 : word) = Some W_46598.
Proof. vm_refl. Qed.
Lemma D_46598 : decode_any W_46598 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4659c : bv 32 := 0x00048713.
Lemma F_4659c : fetch_word Plain.M.loaded_segments (0x465e4 : word) = Some W_4659c.
Proof. vm_refl. Qed.
Lemma D_4659c : decode_any W_4659c = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_465a0 : bv 32 := 0x000780e7.
Lemma F_465a0 : fetch_word Plain.M.loaded_segments (0x465e8 : word) = Some W_465a0.
Proof. vm_refl. Qed.
Lemma D_465a0 : decode_any W_465a0 = Some (Jalr 1 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_465a4 : bv 32 := 0x01044503.
Lemma F_465a4 : fetch_word Plain.M.loaded_segments (0x465ec : word) = Some W_465a4.
Proof. vm_refl. Qed.
Lemma D_465a4 : decode_any W_465a4 = Some (Load SZ1 false 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_465a8 : bv 32 := 0xfff54513.
Lemma F_465a8 : fetch_word Plain.M.loaded_segments (0x465f0 : word) = Some W_465a8.
Proof. vm_refl. Qed.
Lemma D_465a8 : decode_any W_465a8 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_465ac : bv 32 := 0x00157513.
Lemma F_465ac : fetch_word Plain.M.loaded_segments (0x465f4 : word) = Some W_465ac.
Proof. vm_refl. Qed.
Lemma D_465ac : decode_any W_465ac = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_465b0 : bv 32 := 0x00a40423.
Lemma F_465b0 : fetch_word Plain.M.loaded_segments (0x465f8 : word) = Some W_465b0.
Proof. vm_refl. Qed.
Lemma D_465b0 : decode_any W_465b0 = Some (Store SZ1 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_465b4 : bv 32 := 0x06813083.
Lemma F_465b4 : fetch_word Plain.M.loaded_segments (0x465fc : word) = Some W_465b4.
Proof. vm_refl. Qed.
Lemma D_465b4 : decode_any W_465b4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_465b8 : bv 32 := 0x06013403.
Lemma F_465b8 : fetch_word Plain.M.loaded_segments (0x46600 : word) = Some W_465b8.
Proof. vm_refl. Qed.
Lemma D_465b8 : decode_any W_465b8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_465bc : bv 32 := 0x05813483.
Lemma F_465bc : fetch_word Plain.M.loaded_segments (0x46604 : word) = Some W_465bc.
Proof. vm_refl. Qed.
Lemma D_465bc : decode_any W_465bc = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_465c0 : bv 32 := 0x05013903.
Lemma F_465c0 : fetch_word Plain.M.loaded_segments (0x46608 : word) = Some W_465c0.
Proof. vm_refl. Qed.
Lemma D_465c0 : decode_any W_465c0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_465c4 : bv 32 := 0x04813983.
Lemma F_465c4 : fetch_word Plain.M.loaded_segments (0x4660c : word) = Some W_465c4.
Proof. vm_refl. Qed.
Lemma D_465c4 : decode_any W_465c4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_465c8 : bv 32 := 0x04013a03.
Lemma F_465c8 : fetch_word Plain.M.loaded_segments (0x46610 : word) = Some W_465c8.
Proof. vm_refl. Qed.
Lemma D_465c8 : decode_any W_465c8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_465cc : bv 32 := 0x03813a83.
Lemma F_465cc : fetch_word Plain.M.loaded_segments (0x46614 : word) = Some W_465cc.
Proof. vm_refl. Qed.
Lemma D_465cc : decode_any W_465cc = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_465d0 : bv 32 := 0x03013b03.
Lemma F_465d0 : fetch_word Plain.M.loaded_segments (0x46618 : word) = Some W_465d0.
Proof. vm_refl. Qed.
Lemma D_465d0 : decode_any W_465d0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_465d4 : bv 32 := 0x07010113.
Lemma F_465d4 : fetch_word Plain.M.loaded_segments (0x4661c : word) = Some W_465d4.
Proof. vm_refl. Qed.
Lemma D_465d4 : decode_any W_465d4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_465d8 : bv 32 := 0x00008067.
Lemma F_465d8 : fetch_word Plain.M.loaded_segments (0x46620 : word) = Some W_465d8.
Proof. vm_refl. Qed.
Lemma D_465d8 : decode_any W_465d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_465dc : bv 32 := 0x00800593.
Lemma F_465dc : fetch_word Plain.M.loaded_segments (0x46624 : word) = Some W_465dc.
Proof. vm_refl. Qed.
Lemma D_465dc : decode_any W_465dc = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_465e0 : bv 32 := 0x00048513.
Lemma F_465e0 : fetch_word Plain.M.loaded_segments (0x46628 : word) = Some W_465e0.
Proof. vm_refl. Qed.
Lemma D_465e0 : decode_any W_465e0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_465e4 : bv 32 := 0xc28fb0ef.
Lemma F_465e4 : fetch_word Plain.M.loaded_segments (0x4662c : word) = Some W_465e4.
Proof. vm_refl. Qed.
Lemma D_465e4 : decode_any W_465e4 = Some (Jal 1 2077736, 4%Z).
Proof. vm_refl. Qed.

Definition W_465e8 : bv 32 := 0x00000513.
Lemma F_465e8 : fetch_word Plain.M.loaded_segments (0x46630 : word) = Some W_465e8.
Proof. vm_refl. Qed.
Lemma D_465e8 : decode_any W_465e8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_465ec : bv 32 := 0xfc5ff06f.
Lemma F_465ec : fetch_word Plain.M.loaded_segments (0x46634 : word) = Some W_465ec.
Proof. vm_refl. Qed.
Lemma D_465ec : decode_any W_465ec = Some (Jal 0 2097092, 4%Z).
Proof. vm_refl. Qed.

Definition W_465f0 : bv 32 := 0xd59fe0ef.
Lemma F_465f0 : fetch_word Plain.M.loaded_segments (0x46638 : word) = Some W_465f0.
Proof. vm_refl. Qed.
Lemma D_465f0 : decode_any W_465f0 = Some (Jal 1 2092376, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r40be8_40db0.
Module Ns0_code_r4124c_413b4.
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

Definition W_46a90 : bv 32 := 0xfd010113.
Lemma F_46a90 : fetch_word Plain.M.loaded_segments (0x46ad8 : word) = Some W_46a90.
Proof. vm_refl. Qed.
Lemma D_46a90 : decode_any W_46a90 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_46a94 : bv 32 := 0x02113423.
Lemma F_46a94 : fetch_word Plain.M.loaded_segments (0x46adc : word) = Some W_46a94.
Proof. vm_refl. Qed.
Lemma D_46a94 : decode_any W_46a94 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_46a98 : bv 32 := 0x02813023.
Lemma F_46a98 : fetch_word Plain.M.loaded_segments (0x46ae0 : word) = Some W_46a98.
Proof. vm_refl. Qed.
Lemma D_46a98 : decode_any W_46a98 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_46a9c : bv 32 := 0x00913c23.
Lemma F_46a9c : fetch_word Plain.M.loaded_segments (0x46ae4 : word) = Some W_46a9c.
Proof. vm_refl. Qed.
Lemma D_46a9c : decode_any W_46a9c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_46aa0 : bv 32 := 0x01213823.
Lemma F_46aa0 : fetch_word Plain.M.loaded_segments (0x46ae8 : word) = Some W_46aa0.
Proof. vm_refl. Qed.
Lemma D_46aa0 : decode_any W_46aa0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_46aa4 : bv 32 := 0x00060493.
Lemma F_46aa4 : fetch_word Plain.M.loaded_segments (0x46aec : word) = Some W_46aa4.
Proof. vm_refl. Qed.
Lemma D_46aa4 : decode_any W_46aa4 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46aa8 : bv 32 := 0xf3c58613.
Lemma F_46aa8 : fetch_word Plain.M.loaded_segments (0x46af0 : word) = Some W_46aa8.
Proof. vm_refl. Qed.
Lemma D_46aa8 : decode_any W_46aa8 = Some (OpImm ALU_ADD 12 11 3900, 4%Z).
Proof. vm_refl. Qed.

Definition W_46aac : bv 32 := 0x01b00693.
Lemma F_46aac : fetch_word Plain.M.loaded_segments (0x46af4 : word) = Some W_46aac.
Proof. vm_refl. Qed.
Lemma D_46aac : decode_any W_46aac = Some (OpImm ALU_ADD 13 0 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ab0 : bv 32 := 0x00050413.
Lemma F_46ab0 : fetch_word Plain.M.loaded_segments (0x46af8 : word) = Some W_46ab0.
Proof. vm_refl. Qed.
Lemma D_46ab0 : decode_any W_46ab0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ab4 : bv 32 := 0x10c6e463.
Lemma F_46ab4 : fetch_word Plain.M.loaded_segments (0x46afc : word) = Some W_46ab4.
Proof. vm_refl. Qed.
Lemma D_46ab4 : decode_any W_46ab4 = Some (Branch BC_LTU 13 12 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ab8 : bv 32 := 0x00261613.
Lemma F_46ab8 : fetch_word Plain.M.loaded_segments (0x46b00 : word) = Some W_46ab8.
Proof. vm_refl. Qed.
Lemma D_46ab8 : decode_any W_46ab8 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_46abc : bv 32 := 0xfffcd517.
Lemma F_46abc : fetch_word Plain.M.loaded_segments (0x46b04 : word) = Some W_46abc.
Proof. vm_refl. Qed.
Lemma D_46abc : decode_any W_46abc = Some (Auipc 10 1048525, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ac0 : bv 32 := 0xed450513.
Lemma F_46ac0 : fetch_word Plain.M.loaded_segments (0x46b08 : word) = Some W_46ac0.
Proof. vm_refl. Qed.
Lemma D_46ac0 : decode_any W_46ac0 = Some (OpImm ALU_ADD 10 10 3796, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ac4 : bv 32 := 0x00a60633.
Lemma F_46ac4 : fetch_word Plain.M.loaded_segments (0x46b0c : word) = Some W_46ac4.
Proof. vm_refl. Qed.
Lemma D_46ac4 : decode_any W_46ac4 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ac8 : bv 32 := 0x00062603.
Lemma F_46ac8 : fetch_word Plain.M.loaded_segments (0x46b10 : word) = Some W_46ac8.
Proof. vm_refl. Qed.
Lemma D_46ac8 : decode_any W_46ac8 = Some (Load SZ4 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46acc : bv 32 := 0x00a60633.
Lemma F_46acc : fetch_word Plain.M.loaded_segments (0x46b14 : word) = Some W_46acc.
Proof. vm_refl. Qed.
Lemma D_46acc : decode_any W_46acc = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ad0 : bv 32 := 0x00100513.
Lemma F_46ad0 : fetch_word Plain.M.loaded_segments (0x46b18 : word) = Some W_46ad0.
Proof. vm_refl. Qed.
Lemma D_46ad0 : decode_any W_46ad0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ad4 : bv 32 := 0x00060067.
Lemma F_46ad4 : fetch_word Plain.M.loaded_segments (0x46b1c : word) = Some W_46ad4.
Proof. vm_refl. Qed.
Lemma D_46ad4 : decode_any W_46ad4 = Some (Jalr 0 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ad8 : bv 32 := 0x01840513.
Lemma F_46ad8 : fetch_word Plain.M.loaded_segments (0x46b20 : word) = Some W_46ad8.
Proof. vm_refl. Qed.
Lemma D_46ad8 : decode_any W_46ad8 = Some (OpImm ALU_ADD 10 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_46adc : bv 32 := 0x00c10593.
Lemma F_46adc : fetch_word Plain.M.loaded_segments (0x46b24 : word) = Some W_46adc.
Proof. vm_refl. Qed.
Lemma D_46adc : decode_any W_46adc = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ae0 : bv 32 := 0x00200613.
Lemma F_46ae0 : fetch_word Plain.M.loaded_segments (0x46b28 : word) = Some W_46ae0.
Proof. vm_refl. Qed.
Lemma D_46ae0 : decode_any W_46ae0 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ae4 : bv 32 := 0x00200913.
Lemma F_46ae4 : fetch_word Plain.M.loaded_segments (0x46b2c : word) = Some W_46ae4.
Proof. vm_refl. Qed.
Lemma D_46ae4 : decode_any W_46ae4 = Some (OpImm ALU_ADD 18 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ae8 : bv 32 := 0xf6cff0ef.
Lemma F_46ae8 : fetch_word Plain.M.loaded_segments (0x46b30 : word) = Some W_46ae8.
Proof. vm_refl. Qed.
Lemma D_46ae8 : decode_any W_46ae8 = Some (Jal 1 2094956, 4%Z).
Proof. vm_refl. Qed.

Definition W_46aec : bv 32 := 0x09251a63.
Lemma F_46aec : fetch_word Plain.M.loaded_segments (0x46b34 : word) = Some W_46aec.
Proof. vm_refl. Qed.
Lemma D_46aec : decode_any W_46aec = Some (Branch BC_NE 10 18 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_46af0 : bv 32 := 0x00c15503.
Lemma F_46af0 : fetch_word Plain.M.loaded_segments (0x46b38 : word) = Some W_46af0.
Proof. vm_refl. Qed.
Lemma D_46af0 : decode_any W_46af0 = Some (Load SZ2 false 10 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_46af4 : bv 32 := 0x00855593.
Lemma F_46af4 : fetch_word Plain.M.loaded_segments (0x46b3c : word) = Some W_46af4.
Proof. vm_refl. Qed.
Lemma D_46af4 : decode_any W_46af4 = Some (ShiftImm ALU_SRL 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46af8 : bv 32 := 0x00851513.
Lemma F_46af8 : fetch_word Plain.M.loaded_segments (0x46b40 : word) = Some W_46af8.
Proof. vm_refl. Qed.
Lemma D_46af8 : decode_any W_46af8 = Some (ShiftImm ALU_SLL 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46afc : bv 32 := 0x00b56533.
Lemma F_46afc : fetch_word Plain.M.loaded_segments (0x46b44 : word) = Some W_46afc.
Proof. vm_refl. Qed.
Lemma D_46afc : decode_any W_46afc = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b00 : bv 32 := 0x03051513.
Lemma F_46b00 : fetch_word Plain.M.loaded_segments (0x46b48 : word) = Some W_46b00.
Proof. vm_refl. Qed.
Lemma D_46b00 : decode_any W_46b00 = Some (ShiftImm ALU_SLL 10 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b04 : bv 32 := 0x03055513.
Lemma F_46b04 : fetch_word Plain.M.loaded_segments (0x46b4c : word) = Some W_46b04.
Proof. vm_refl. Qed.
Lemma D_46b04 : decode_any W_46b04 = Some (ShiftImm ALU_SRL 10 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b08 : bv 32 := 0x08c0006f.
Lemma F_46b08 : fetch_word Plain.M.loaded_segments (0x46b50 : word) = Some W_46b08.
Proof. vm_refl. Qed.
Lemma D_46b08 : decode_any W_46b08 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b0c : bv 32 := 0x01840513.
Lemma F_46b0c : fetch_word Plain.M.loaded_segments (0x46b54 : word) = Some W_46b0c.
Proof. vm_refl. Qed.
Lemma D_46b0c : decode_any W_46b0c = Some (OpImm ALU_ADD 10 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b10 : bv 32 := 0x00810593.
Lemma F_46b10 : fetch_word Plain.M.loaded_segments (0x46b58 : word) = Some W_46b10.
Proof. vm_refl. Qed.
Lemma D_46b10 : decode_any W_46b10 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b14 : bv 32 := 0x00400613.
Lemma F_46b14 : fetch_word Plain.M.loaded_segments (0x46b5c : word) = Some W_46b14.
Proof. vm_refl. Qed.
Lemma D_46b14 : decode_any W_46b14 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b18 : bv 32 := 0x00400913.
Lemma F_46b18 : fetch_word Plain.M.loaded_segments (0x46b60 : word) = Some W_46b18.
Proof. vm_refl. Qed.
Lemma D_46b18 : decode_any W_46b18 = Some (OpImm ALU_ADD 18 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b1c : bv 32 := 0xf38ff0ef.
Lemma F_46b1c : fetch_word Plain.M.loaded_segments (0x46b64 : word) = Some W_46b1c.
Proof. vm_refl. Qed.
Lemma D_46b1c : decode_any W_46b1c = Some (Jal 1 2094904, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b20 : bv 32 := 0x07251063.
Lemma F_46b20 : fetch_word Plain.M.loaded_segments (0x46b68 : word) = Some W_46b20.
Proof. vm_refl. Qed.
Lemma D_46b20 : decode_any W_46b20 = Some (Branch BC_NE 10 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b24 : bv 32 := 0x00812503.
Lemma F_46b24 : fetch_word Plain.M.loaded_segments (0x46b6c : word) = Some W_46b24.
Proof. vm_refl. Qed.
Lemma D_46b24 : decode_any W_46b24 = Some (Load SZ4 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b28 : bv 32 := 0x000105b7.
Lemma F_46b28 : fetch_word Plain.M.loaded_segments (0x46b70 : word) = Some W_46b28.
Proof. vm_refl. Qed.
Lemma D_46b28 : decode_any W_46b28 = Some (Lui 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b2c : bv 32 := 0xf0058593.
Lemma F_46b2c : fetch_word Plain.M.loaded_segments (0x46b74 : word) = Some W_46b2c.
Proof. vm_refl. Qed.
Lemma D_46b2c : decode_any W_46b2c = Some (OpImm ALU_ADD 11 11 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b30 : bv 32 := 0x00855613.
Lemma F_46b30 : fetch_word Plain.M.loaded_segments (0x46b78 : word) = Some W_46b30.
Proof. vm_refl. Qed.
Lemma D_46b30 : decode_any W_46b30 = Some (ShiftImm ALU_SRL 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b34 : bv 32 := 0x0185569b.
Lemma F_46b34 : fetch_word Plain.M.loaded_segments (0x46b7c : word) = Some W_46b34.
Proof. vm_refl. Qed.
Lemma D_46b34 : decode_any W_46b34 = Some (ShiftImm32 ALU_SRL 13 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b38 : bv 32 := 0x00b67633.
Lemma F_46b38 : fetch_word Plain.M.loaded_segments (0x46b80 : word) = Some W_46b38.
Proof. vm_refl. Qed.
Lemma D_46b38 : decode_any W_46b38 = Some (Op ALU_AND 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b3c : bv 32 := 0x00b575b3.
Lemma F_46b3c : fetch_word Plain.M.loaded_segments (0x46b84 : word) = Some W_46b3c.
Proof. vm_refl. Qed.
Lemma D_46b3c : decode_any W_46b3c = Some (Op ALU_AND 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b40 : bv 32 := 0x01851513.
Lemma F_46b40 : fetch_word Plain.M.loaded_segments (0x46b88 : word) = Some W_46b40.
Proof. vm_refl. Qed.
Lemma D_46b40 : decode_any W_46b40 = Some (ShiftImm ALU_SLL 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b44 : bv 32 := 0x00859593.
Lemma F_46b44 : fetch_word Plain.M.loaded_segments (0x46b8c : word) = Some W_46b44.
Proof. vm_refl. Qed.
Lemma D_46b44 : decode_any W_46b44 = Some (ShiftImm ALU_SLL 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b48 : bv 32 := 0x00d66633.
Lemma F_46b48 : fetch_word Plain.M.loaded_segments (0x46b90 : word) = Some W_46b48.
Proof. vm_refl. Qed.
Lemma D_46b48 : decode_any W_46b48 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b4c : bv 32 := 0x00b56533.
Lemma F_46b4c : fetch_word Plain.M.loaded_segments (0x46b94 : word) = Some W_46b4c.
Proof. vm_refl. Qed.
Lemma D_46b4c : decode_any W_46b4c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b50 : bv 32 := 0x00c56533.
Lemma F_46b50 : fetch_word Plain.M.loaded_segments (0x46b98 : word) = Some W_46b50.
Proof. vm_refl. Qed.
Lemma D_46b50 : decode_any W_46b50 = Some (Op ALU_OR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b54 : bv 32 := 0x02051513.
Lemma F_46b54 : fetch_word Plain.M.loaded_segments (0x46b9c : word) = Some W_46b54.
Proof. vm_refl. Qed.
Lemma D_46b54 : decode_any W_46b54 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b58 : bv 32 := 0x02055513.
Lemma F_46b58 : fetch_word Plain.M.loaded_segments (0x46ba0 : word) = Some W_46b58.
Proof. vm_refl. Qed.
Lemma D_46b58 : decode_any W_46b58 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b5c : bv 32 := 0x0380006f.
Lemma F_46b5c : fetch_word Plain.M.loaded_segments (0x46ba4 : word) = Some W_46b5c.
Proof. vm_refl. Qed.
Lemma D_46b5c : decode_any W_46b5c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b60 : bv 32 := 0x01840513.
Lemma F_46b60 : fetch_word Plain.M.loaded_segments (0x46ba8 : word) = Some W_46b60.
Proof. vm_refl. Qed.
Lemma D_46b60 : decode_any W_46b60 = Some (OpImm ALU_ADD 10 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b64 : bv 32 := 0x00f10593.
Lemma F_46b64 : fetch_word Plain.M.loaded_segments (0x46bac : word) = Some W_46b64.
Proof. vm_refl. Qed.
Lemma D_46b64 : decode_any W_46b64 = Some (OpImm ALU_ADD 11 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b68 : bv 32 := 0x00100613.
Lemma F_46b68 : fetch_word Plain.M.loaded_segments (0x46bb0 : word) = Some W_46b68.
Proof. vm_refl. Qed.
Lemma D_46b68 : decode_any W_46b68 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b6c : bv 32 := 0x00100913.
Lemma F_46b6c : fetch_word Plain.M.loaded_segments (0x46bb4 : word) = Some W_46b6c.
Proof. vm_refl. Qed.
Lemma D_46b6c : decode_any W_46b6c = Some (OpImm ALU_ADD 18 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b70 : bv 32 := 0xee4ff0ef.
Lemma F_46b70 : fetch_word Plain.M.loaded_segments (0x46bb8 : word) = Some W_46b70.
Proof. vm_refl. Qed.
Lemma D_46b70 : decode_any W_46b70 = Some (Jal 1 2094820, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b74 : bv 32 := 0x01251663.
Lemma F_46b74 : fetch_word Plain.M.loaded_segments (0x46bbc : word) = Some W_46b74.
Proof. vm_refl. Qed.
Lemma D_46b74 : decode_any W_46b74 = Some (Branch BC_NE 10 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b78 : bv 32 := 0x00f14503.
Lemma F_46b78 : fetch_word Plain.M.loaded_segments (0x46bc0 : word) = Some W_46b78.
Proof. vm_refl. Qed.
Lemma D_46b78 : decode_any W_46b78 = Some (Load SZ1 false 10 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b7c : bv 32 := 0x0180006f.
Lemma F_46b7c : fetch_word Plain.M.loaded_segments (0x46bc4 : word) = Some W_46b7c.
Proof. vm_refl. Qed.
Lemma D_46b7c : decode_any W_46b7c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b80 : bv 32 := 0x00100593.
Lemma F_46b80 : fetch_word Plain.M.loaded_segments (0x46bc8 : word) = Some W_46b80.
Proof. vm_refl. Qed.
Lemma D_46b80 : decode_any W_46b80 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b84 : bv 32 := 0x00048513.
Lemma F_46b84 : fetch_word Plain.M.loaded_segments (0x46bcc : word) = Some W_46b84.
Proof. vm_refl. Qed.
Lemma D_46b84 : decode_any W_46b84 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b88 : bv 32 := 0xe85fa0ef.
Lemma F_46b88 : fetch_word Plain.M.loaded_segments (0x46bd0 : word) = Some W_46b88.
Proof. vm_refl. Qed.
Lemma D_46b88 : decode_any W_46b88 = Some (Jal 1 2076292, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b8c : bv 32 := 0x00000513.
Lemma F_46b8c : fetch_word Plain.M.loaded_segments (0x46bd4 : word) = Some W_46b8c.
Proof. vm_refl. Qed.
Lemma D_46b8c : decode_any W_46b8c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b90 : bv 32 := 0x00040423.
Lemma F_46b90 : fetch_word Plain.M.loaded_segments (0x46bd8 : word) = Some W_46b90.
Proof. vm_refl. Qed.
Lemma D_46b90 : decode_any W_46b90 = Some (Store SZ1 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b94 : bv 32 := 0x02813083.
Lemma F_46b94 : fetch_word Plain.M.loaded_segments (0x46bdc : word) = Some W_46b94.
Proof. vm_refl. Qed.
Lemma D_46b94 : decode_any W_46b94 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b98 : bv 32 := 0x02013403.
Lemma F_46b98 : fetch_word Plain.M.loaded_segments (0x46be0 : word) = Some W_46b98.
Proof. vm_refl. Qed.
Lemma D_46b98 : decode_any W_46b98 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_46b9c : bv 32 := 0x01813483.
Lemma F_46b9c : fetch_word Plain.M.loaded_segments (0x46be4 : word) = Some W_46b9c.
Proof. vm_refl. Qed.
Lemma D_46b9c : decode_any W_46b9c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ba0 : bv 32 := 0x01013903.
Lemma F_46ba0 : fetch_word Plain.M.loaded_segments (0x46be8 : word) = Some W_46ba0.
Proof. vm_refl. Qed.
Lemma D_46ba0 : decode_any W_46ba0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ba4 : bv 32 := 0x03010113.
Lemma F_46ba4 : fetch_word Plain.M.loaded_segments (0x46bec : word) = Some W_46ba4.
Proof. vm_refl. Qed.
Lemma D_46ba4 : decode_any W_46ba4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_46ba8 : bv 32 := 0x00008067.
Lemma F_46ba8 : fetch_word Plain.M.loaded_segments (0x46bf0 : word) = Some W_46ba8.
Proof. vm_refl. Qed.
Lemma D_46ba8 : decode_any W_46ba8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bac : bv 32 := 0x00200513.
Lemma F_46bac : fetch_word Plain.M.loaded_segments (0x46bf4 : word) = Some W_46bac.
Proof. vm_refl. Qed.
Lemma D_46bac : decode_any W_46bac = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bb0 : bv 32 := 0xfe5ff06f.
Lemma F_46bb0 : fetch_word Plain.M.loaded_segments (0x46bf8 : word) = Some W_46bb0.
Proof. vm_refl. Qed.
Lemma D_46bb0 : decode_any W_46bb0 = Some (Jal 0 2097124, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bb4 : bv 32 := 0x00400513.
Lemma F_46bb4 : fetch_word Plain.M.loaded_segments (0x46bfc : word) = Some W_46bb4.
Proof. vm_refl. Qed.
Lemma D_46bb4 : decode_any W_46bb4 = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bb8 : bv 32 := 0xfddff06f.
Lemma F_46bb8 : fetch_word Plain.M.loaded_segments (0x46c00 : word) = Some W_46bb8.
Proof. vm_refl. Qed.
Lemma D_46bb8 : decode_any W_46bb8 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bbc : bv 32 := 0x03859513.
Lemma F_46bbc : fetch_word Plain.M.loaded_segments (0x46c04 : word) = Some W_46bbc.
Proof. vm_refl. Qed.
Lemma D_46bbc : decode_any W_46bbc = Some (ShiftImm ALU_SLL 10 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bc0 : bv 32 := 0x43855513.
Lemma F_46bc0 : fetch_word Plain.M.loaded_segments (0x46c08 : word) = Some W_46bc0.
Proof. vm_refl. Qed.
Lemma D_46bc0 : decode_any W_46bc0 = Some (ShiftImm ALU_SRA 10 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bc4 : bv 32 := 0xf9000613.
Lemma F_46bc4 : fetch_word Plain.M.loaded_segments (0x46c0c : word) = Some W_46bc4.
Proof. vm_refl. Qed.
Lemma D_46bc4 : decode_any W_46bc4 = Some (OpImm ALU_ADD 12 0 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bc8 : bv 32 := 0x02c54463.
Lemma F_46bc8 : fetch_word Plain.M.loaded_segments (0x46c10 : word) = Some W_46bc8.
Proof. vm_refl. Qed.
Lemma D_46bc8 : decode_any W_46bc8 = Some (Branch BC_LT 10 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bcc : bv 32 := 0x0f05f513.
Lemma F_46bcc : fetch_word Plain.M.loaded_segments (0x46c14 : word) = Some W_46bcc.
Proof. vm_refl. Qed.
Lemma D_46bcc : decode_any W_46bcc = Some (OpImm ALU_AND 10 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bd0 : bv 32 := 0x09000613.
Lemma F_46bd0 : fetch_word Plain.M.loaded_segments (0x46c18 : word) = Some W_46bd0.
Proof. vm_refl. Qed.
Lemma D_46bd0 : decode_any W_46bd0 = Some (OpImm ALU_ADD 12 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bd4 : bv 32 := 0x00c50e63.
Lemma F_46bd4 : fetch_word Plain.M.loaded_segments (0x46c1c : word) = Some W_46bd4.
Proof. vm_refl. Qed.
Lemma D_46bd4 : decode_any W_46bd4 = Some (Branch BC_EQ 10 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bd8 : bv 32 := 0x00b00593.
Lemma F_46bd8 : fetch_word Plain.M.loaded_segments (0x46c20 : word) = Some W_46bd8.
Proof. vm_refl. Qed.
Lemma D_46bd8 : decode_any W_46bd8 = Some (OpImm ALU_ADD 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bdc : bv 32 := 0xfa9ff06f.
Lemma F_46bdc : fetch_word Plain.M.loaded_segments (0x46c24 : word) = Some W_46bdc.
Proof. vm_refl. Qed.
Lemma D_46bdc : decode_any W_46bdc = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition W_46be0 : bv 32 := 0x01000513.
Lemma F_46be0 : fetch_word Plain.M.loaded_segments (0x46c28 : word) = Some W_46be0.
Proof. vm_refl. Qed.
Lemma D_46be0 : decode_any W_46be0 = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_46be4 : bv 32 := 0xfb1ff06f.
Lemma F_46be4 : fetch_word Plain.M.loaded_segments (0x46c2c : word) = Some W_46be4.
Proof. vm_refl. Qed.
Lemma D_46be4 : decode_any W_46be4 = Some (Jal 0 2097072, 4%Z).
Proof. vm_refl. Qed.

Definition W_46be8 : bv 32 := 0x00800513.
Lemma F_46be8 : fetch_word Plain.M.loaded_segments (0x46c30 : word) = Some W_46be8.
Proof. vm_refl. Qed.
Lemma D_46be8 : decode_any W_46be8 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bec : bv 32 := 0xfa9ff06f.
Lemma F_46bec : fetch_word Plain.M.loaded_segments (0x46c34 : word) = Some W_46bec.
Proof. vm_refl. Qed.
Lemma D_46bec : decode_any W_46bec = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bf0 : bv 32 := 0x00f5f513.
Lemma F_46bf0 : fetch_word Plain.M.loaded_segments (0x46c38 : word) = Some W_46bf0.
Proof. vm_refl. Qed.
Lemma D_46bf0 : decode_any W_46bf0 = Some (OpImm ALU_AND 10 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_46bf4 : bv 32 := 0xfa1ff06f.
Lemma F_46bf4 : fetch_word Plain.M.loaded_segments (0x46c3c : word) = Some W_46bf4.
Proof. vm_refl. Qed.
Lemma D_46bf4 : decode_any W_46bf4 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r4124c_413b4.
Module Ns0_code_r3fc7c_3fe84.
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

Definition W_45558 : bv 32 := 0xf9010113.
Lemma F_45558 : fetch_word Plain.M.loaded_segments (0x455a0 : word) = Some W_45558.
Proof. vm_refl. Qed.
Lemma D_45558 : decode_any W_45558 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4555c : bv 32 := 0x06113423.
Lemma F_4555c : fetch_word Plain.M.loaded_segments (0x455a4 : word) = Some W_4555c.
Proof. vm_refl. Qed.
Lemma D_4555c : decode_any W_4555c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_45560 : bv 32 := 0x06813023.
Lemma F_45560 : fetch_word Plain.M.loaded_segments (0x455a8 : word) = Some W_45560.
Proof. vm_refl. Qed.
Lemma D_45560 : decode_any W_45560 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_45564 : bv 32 := 0x04913c23.
Lemma F_45564 : fetch_word Plain.M.loaded_segments (0x455ac : word) = Some W_45564.
Proof. vm_refl. Qed.
Lemma D_45564 : decode_any W_45564 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_45568 : bv 32 := 0x05213823.
Lemma F_45568 : fetch_word Plain.M.loaded_segments (0x455b0 : word) = Some W_45568.
Proof. vm_refl. Qed.
Lemma D_45568 : decode_any W_45568 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_4556c : bv 32 := 0x05313423.
Lemma F_4556c : fetch_word Plain.M.loaded_segments (0x455b4 : word) = Some W_4556c.
Proof. vm_refl. Qed.
Lemma D_4556c : decode_any W_4556c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_45570 : bv 32 := 0x05413023.
Lemma F_45570 : fetch_word Plain.M.loaded_segments (0x455b8 : word) = Some W_45570.
Proof. vm_refl. Qed.
Lemma D_45570 : decode_any W_45570 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_45574 : bv 32 := 0x03513c23.
Lemma F_45574 : fetch_word Plain.M.loaded_segments (0x455bc : word) = Some W_45574.
Proof. vm_refl. Qed.
Lemma D_45574 : decode_any W_45574 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_45578 : bv 32 := 0x03613823.
Lemma F_45578 : fetch_word Plain.M.loaded_segments (0x455c0 : word) = Some W_45578.
Proof. vm_refl. Qed.
Lemma D_45578 : decode_any W_45578 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4557c : bv 32 := 0x03713423.
Lemma F_4557c : fetch_word Plain.M.loaded_segments (0x455c4 : word) = Some W_4557c.
Proof. vm_refl. Qed.
Lemma D_4557c : decode_any W_4557c = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_45580 : bv 32 := 0x03813023.
Lemma F_45580 : fetch_word Plain.M.loaded_segments (0x455c8 : word) = Some W_45580.
Proof. vm_refl. Qed.
Lemma D_45580 : decode_any W_45580 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_45584 : bv 32 := 0x00050493.
Lemma F_45584 : fetch_word Plain.M.loaded_segments (0x455cc : word) = Some W_45584.
Proof. vm_refl. Qed.
Lemma D_45584 : decode_any W_45584 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45588 : bv 32 := 0x00954503.
Lemma F_45588 : fetch_word Plain.M.loaded_segments (0x455d0 : word) = Some W_45588.
Proof. vm_refl. Qed.
Lemma D_45588 : decode_any W_45588 = Some (Load SZ1 false 10 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4558c : bv 32 := 0x12051663.
Lemma F_4558c : fetch_word Plain.M.loaded_segments (0x455d4 : word) = Some W_4558c.
Proof. vm_refl. Qed.
Lemma D_4558c : decode_any W_4558c = Some (Branch BC_NE 10 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_45590 : bv 32 := 0x00060413.
Lemma F_45590 : fetch_word Plain.M.loaded_segments (0x455d8 : word) = Some W_45590.
Proof. vm_refl. Qed.
Lemma D_45590 : decode_any W_45590 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45594 : bv 32 := 0x00058913.
Lemma F_45594 : fetch_word Plain.M.loaded_segments (0x455dc : word) = Some W_45594.
Proof. vm_refl. Qed.
Lemma D_45594 : decode_any W_45594 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45598 : bv 32 := 0x00400993.
Lemma F_45598 : fetch_word Plain.M.loaded_segments (0x455e0 : word) = Some W_45598.
Proof. vm_refl. Qed.
Lemma D_45598 : decode_any W_45598 = Some (OpImm ALU_ADD 19 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_4559c : bv 32 := 0xfffce517.
Lemma F_4559c : fetch_word Plain.M.loaded_segments (0x455e4 : word) = Some W_4559c.
Proof. vm_refl. Qed.
Lemma D_4559c : decode_any W_4559c = Some (Auipc 10 1048526, 4%Z).
Proof. vm_refl. Qed.

Definition W_455a0 : bv 32 := 0x00100a13.
Lemma F_455a0 : fetch_word Plain.M.loaded_segments (0x455e8 : word) = Some W_455a0.
Proof. vm_refl. Qed.
Lemma D_455a0 : decode_any W_455a0 = Some (OpImm ALU_ADD 20 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_455a4 : bv 32 := 0x01800a93.
Lemma F_455a4 : fetch_word Plain.M.loaded_segments (0x455ec : word) = Some W_455a4.
Proof. vm_refl. Qed.
Lemma D_455a4 : decode_any W_455a4 = Some (OpImm ALU_ADD 21 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_455a8 : bv 32 := 0x10000b13.
Lemma F_455a8 : fetch_word Plain.M.loaded_segments (0x455f0 : word) = Some W_455a8.
Proof. vm_refl. Qed.
Lemma D_455a8 : decode_any W_455a8 = Some (OpImm ALU_ADD 22 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_455ac : bv 32 := 0x36050b93.
Lemma F_455ac : fetch_word Plain.M.loaded_segments (0x455f4 : word) = Some W_455ac.
Proof. vm_refl. Qed.
Lemma D_455ac : decode_any W_455ac = Some (OpImm ALU_ADD 23 10 864, 4%Z).
Proof. vm_refl. Qed.

Definition W_455b0 : bv 32 := 0x00300c13.
Lemma F_455b0 : fetch_word Plain.M.loaded_segments (0x455f8 : word) = Some W_455b0.
Proof. vm_refl. Qed.
Lemma D_455b0 : decode_any W_455b0 = Some (OpImm ALU_ADD 24 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_455b4 : bv 32 := 0x0084c503.
Lemma F_455b4 : fetch_word Plain.M.loaded_segments (0x455fc : word) = Some W_455b4.
Proof. vm_refl. Qed.
Lemma D_455b4 : decode_any W_455b4 = Some (Load SZ1 false 10 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_455b8 : bv 32 := 0x10050063.
Lemma F_455b8 : fetch_word Plain.M.loaded_segments (0x45600 : word) = Some W_455b8.
Proof. vm_refl. Qed.
Lemma D_455b8 : decode_any W_455b8 = Some (Branch BC_EQ 10 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_455bc : bv 32 := 0x1804b503.
Lemma F_455bc : fetch_word Plain.M.loaded_segments (0x45604 : word) = Some W_455bc.
Proof. vm_refl. Qed.
Lemma D_455bc : decode_any W_455bc = Some (Load SZ8 true 10 9 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_455c0 : bv 32 := 0xfe852583.
Lemma F_455c0 : fetch_word Plain.M.loaded_segments (0x45608 : word) = Some W_455c0.
Proof. vm_refl. Qed.
Lemma D_455c0 : decode_any W_455c0 = Some (Load SZ4 true 11 10 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_455c4 : bv 32 := 0x0eb9e663.
Lemma F_455c4 : fetch_word Plain.M.loaded_segments (0x4560c : word) = Some W_455c4.
Proof. vm_refl. Qed.
Lemma D_455c4 : decode_any W_455c4 = Some (Branch BC_LTU 19 11 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_455c8 : bv 32 := 0x00259593.
Lemma F_455c8 : fetch_word Plain.M.loaded_segments (0x45610 : word) = Some W_455c8.
Proof. vm_refl. Qed.
Lemma D_455c8 : decode_any W_455c8 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_455cc : bv 32 := 0x017585b3.
Lemma F_455cc : fetch_word Plain.M.loaded_segments (0x45614 : word) = Some W_455cc.
Proof. vm_refl. Qed.
Lemma D_455cc : decode_any W_455cc = Some (Op ALU_ADD 11 11 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_455d0 : bv 32 := 0x0005a583.
Lemma F_455d0 : fetch_word Plain.M.loaded_segments (0x45618 : word) = Some W_455d0.
Proof. vm_refl. Qed.
Lemma D_455d0 : decode_any W_455d0 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_455d4 : bv 32 := 0x017585b3.
Lemma F_455d4 : fetch_word Plain.M.loaded_segments (0x4561c : word) = Some W_455d4.
Proof. vm_refl. Qed.
Lemma D_455d4 : decode_any W_455d4 = Some (Op ALU_ADD 11 11 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_455d8 : bv 32 := 0x00058067.
Lemma F_455d8 : fetch_word Plain.M.loaded_segments (0x45620 : word) = Some W_455d8.
Proof. vm_refl. Qed.
Lemma D_455d8 : decode_any W_455d8 = Some (Jalr 0 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_455dc : bv 32 := 0xff452423.
Lemma F_455dc : fetch_word Plain.M.loaded_segments (0x45624 : word) = Some W_455dc.
Proof. vm_refl. Qed.
Lemma D_455dc : decode_any W_455dc = Some (Store SZ4 10 20 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_455e0 : bv 32 := 0x0380006f.
Lemma F_455e0 : fetch_word Plain.M.loaded_segments (0x45628 : word) = Some W_455e0.
Proof. vm_refl. Qed.
Lemma D_455e0 : decode_any W_455e0 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_455e4 : bv 32 := 0xff852423.
Lemma F_455e4 : fetch_word Plain.M.loaded_segments (0x4562c : word) = Some W_455e4.
Proof. vm_refl. Qed.
Lemma D_455e4 : decode_any W_455e4 = Some (Store SZ4 10 24 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_455e8 : bv 32 := 0x0300006f.
Lemma F_455e8 : fetch_word Plain.M.loaded_segments (0x45630 : word) = Some W_455e8.
Proof. vm_refl. Qed.
Lemma D_455e8 : decode_any W_455e8 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_455ec : bv 32 := 0xff053603.
Lemma F_455ec : fetch_word Plain.M.loaded_segments (0x45634 : word) = Some W_455ec.
Proof. vm_refl. Qed.
Lemma D_455ec : decode_any W_455ec = Some (Load SZ8 true 12 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_455f0 : bv 32 := 0xff853583.
Lemma F_455f0 : fetch_word Plain.M.loaded_segments (0x45638 : word) = Some W_455f0.
Proof. vm_refl. Qed.
Lemma D_455f0 : decode_any W_455f0 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_455f4 : bv 32 := 0x06c5f463.
Lemma F_455f4 : fetch_word Plain.M.loaded_segments (0x4563c : word) = Some W_455f4.
Proof. vm_refl. Qed.
Lemma D_455f4 : decode_any W_455f4 = Some (Branch BC_GEU 11 12 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_455f8 : bv 32 := 0x00158593.
Lemma F_455f8 : fetch_word Plain.M.loaded_segments (0x45640 : word) = Some W_455f8.
Proof. vm_refl. Qed.
Lemma D_455f8 : decode_any W_455f8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_455fc : bv 32 := 0x0180006f.
Lemma F_455fc : fetch_word Plain.M.loaded_segments (0x45644 : word) = Some W_455fc.
Proof. vm_refl. Qed.
Lemma D_455fc : decode_any W_455fc = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_45600 : bv 32 := 0xff053603.
Lemma F_45600 : fetch_word Plain.M.loaded_segments (0x45648 : word) = Some W_45600.
Proof. vm_refl. Qed.
Lemma D_45600 : decode_any W_45600 = Some (Load SZ8 true 12 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_45604 : bv 32 := 0xff853583.
Lemma F_45604 : fetch_word Plain.M.loaded_segments (0x4564c : word) = Some W_45604.
Proof. vm_refl. Qed.
Lemma D_45604 : decode_any W_45604 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_45608 : bv 32 := 0x06c5f663.
Lemma F_45608 : fetch_word Plain.M.loaded_segments (0x45650 : word) = Some W_45608.
Proof. vm_refl. Qed.
Lemma D_45608 : decode_any W_45608 = Some (Branch BC_GEU 11 12 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_4560c : bv 32 := 0x00158593.
Lemma F_4560c : fetch_word Plain.M.loaded_segments (0x45654 : word) = Some W_4560c.
Proof. vm_refl. Qed.
Lemma D_4560c : decode_any W_4560c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_45610 : bv 32 := 0xff352423.
Lemma F_45610 : fetch_word Plain.M.loaded_segments (0x45658 : word) = Some W_45610.
Proof. vm_refl. Qed.
Lemma D_45610 : decode_any W_45610 = Some (Store SZ4 10 19 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_45614 : bv 32 := 0xfeb53c23.
Lemma F_45614 : fetch_word Plain.M.loaded_segments (0x4565c : word) = Some W_45614.
Proof. vm_refl. Qed.
Lemma D_45614 : decode_any W_45614 = Some (Store SZ8 10 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_45618 : bv 32 := 0x00048513.
Lemma F_45618 : fetch_word Plain.M.loaded_segments (0x45660 : word) = Some W_45618.
Proof. vm_refl. Qed.
Lemma D_45618 : decode_any W_45618 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4561c : bv 32 := 0x00090593.
Lemma F_4561c : fetch_word Plain.M.loaded_segments (0x45664 : word) = Some W_4561c.
Proof. vm_refl. Qed.
Lemma D_4561c : decode_any W_4561c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45620 : bv 32 := 0x00040613.
Lemma F_45620 : fetch_word Plain.M.loaded_segments (0x45668 : word) = Some W_45620.
Proof. vm_refl. Qed.
Lemma D_45620 : decode_any W_45620 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45624 : bv 32 := 0x13c000ef.
Lemma F_45624 : fetch_word Plain.M.loaded_segments (0x4566c : word) = Some W_45624.
Proof. vm_refl. Qed.
Lemma D_45624 : decode_any W_45624 = Some (Jal 1 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_45628 : bv 32 := 0x00042503.
Lemma F_45628 : fetch_word Plain.M.loaded_segments (0x45670 : word) = Some W_45628.
Proof. vm_refl. Qed.
Lemma D_45628 : decode_any W_45628 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4562c : bv 32 := 0x08051663.
Lemma F_4562c : fetch_word Plain.M.loaded_segments (0x45674 : word) = Some W_4562c.
Proof. vm_refl. Qed.
Lemma D_4562c : decode_any W_4562c = Some (Branch BC_NE 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_45630 : bv 32 := 0x0800006f.
Lemma F_45630 : fetch_word Plain.M.loaded_segments (0x45678 : word) = Some W_45630.
Proof. vm_refl. Qed.
Lemma D_45630 : decode_any W_45630 = Some (Jal 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_45634 : bv 32 := 0x1784b583.
Lemma F_45634 : fetch_word Plain.M.loaded_segments (0x4567c : word) = Some W_45634.
Proof. vm_refl. Qed.
Lemma D_45634 : decode_any W_45634 = Some (Load SZ8 true 11 9 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_45638 : bv 32 := 0x40b50533.
Lemma F_45638 : fetch_word Plain.M.loaded_segments (0x45680 : word) = Some W_45638.
Proof. vm_refl. Qed.
Lemma D_45638 : decode_any W_45638 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4563c : bv 32 := 0x0b551663.
Lemma F_4563c : fetch_word Plain.M.loaded_segments (0x45684 : word) = Some W_4563c.
Proof. vm_refl. Qed.
Lemma D_4563c : decode_any W_4563c = Some (Branch BC_NE 10 21 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_45640 : bv 32 := 0x01649423.
Lemma F_45640 : fetch_word Plain.M.loaded_segments (0x45688 : word) = Some W_45640.
Proof. vm_refl. Qed.
Lemma D_45640 : decode_any W_45640 = Some (Store SZ2 9 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_45644 : bv 32 := 0x00093503.
Lemma F_45644 : fetch_word Plain.M.loaded_segments (0x4568c : word) = Some W_45644.
Proof. vm_refl. Qed.
Lemma D_45644 : decode_any W_45644 = Some (Load SZ8 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45648 : bv 32 := 0x18b4b023.
Lemma F_45648 : fetch_word Plain.M.loaded_segments (0x45690 : word) = Some W_45648.
Proof. vm_refl. Qed.
Lemma D_45648 : decode_any W_45648 = Some (Store SZ8 9 11 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_4564c : bv 32 := 0x03853583.
Lemma F_4564c : fetch_word Plain.M.loaded_segments (0x45694 : word) = Some W_4564c.
Proof. vm_refl. Qed.
Lemma D_4564c : decode_any W_4564c = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_45650 : bv 32 := 0x00090513.
Lemma F_45650 : fetch_word Plain.M.loaded_segments (0x45698 : word) = Some W_45650.
Proof. vm_refl. Qed.
Lemma D_45650 : decode_any W_45650 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45654 : bv 32 := 0x000580e7.
Lemma F_45654 : fetch_word Plain.M.loaded_segments (0x4569c : word) = Some W_45654.
Proof. vm_refl. Qed.
Lemma D_45654 : decode_any W_45654 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45658 : bv 32 := 0x0580006f.
Lemma F_45658 : fetch_word Plain.M.loaded_segments (0x456a0 : word) = Some W_45658.
Proof. vm_refl. Qed.
Lemma D_45658 : decode_any W_45658 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4565c : bv 32 := 0x00c4a503.
Lemma F_4565c : fetch_word Plain.M.loaded_segments (0x456a4 : word) = Some W_4565c.
Proof. vm_refl. Qed.
Lemma D_4565c : decode_any W_4565c = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_45660 : bv 32 := 0x00093583.
Lemma F_45660 : fetch_word Plain.M.loaded_segments (0x456a8 : word) = Some W_45660.
Proof. vm_refl. Qed.
Lemma D_45660 : decode_any W_45660 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45664 : bv 32 := 0xfff50513.
Lemma F_45664 : fetch_word Plain.M.loaded_segments (0x456ac : word) = Some W_45664.
Proof. vm_refl. Qed.
Lemma D_45664 : decode_any W_45664 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_45668 : bv 32 := 0x00a4a623.
Lemma F_45668 : fetch_word Plain.M.loaded_segments (0x456b0 : word) = Some W_45668.
Proof. vm_refl. Qed.
Lemma D_45668 : decode_any W_45668 = Some (Store SZ4 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4566c : bv 32 := 0x0185b683.
Lemma F_4566c : fetch_word Plain.M.loaded_segments (0x456b4 : word) = Some W_4566c.
Proof. vm_refl. Qed.
Lemma D_4566c : decode_any W_4566c = Some (Load SZ8 true 13 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_45670 : bv 32 := 0x0180006f.
Lemma F_45670 : fetch_word Plain.M.loaded_segments (0x456b8 : word) = Some W_45670.
Proof. vm_refl. Qed.
Lemma D_45670 : decode_any W_45670 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_45674 : bv 32 := 0x00c4a503.
Lemma F_45674 : fetch_word Plain.M.loaded_segments (0x456bc : word) = Some W_45674.
Proof. vm_refl. Qed.
Lemma D_45674 : decode_any W_45674 = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_45678 : bv 32 := 0x00093583.
Lemma F_45678 : fetch_word Plain.M.loaded_segments (0x456c0 : word) = Some W_45678.
Proof. vm_refl. Qed.
Lemma D_45678 : decode_any W_45678 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4567c : bv 32 := 0xfff50513.
Lemma F_4567c : fetch_word Plain.M.loaded_segments (0x456c4 : word) = Some W_4567c.
Proof. vm_refl. Qed.
Lemma D_4567c : decode_any W_4567c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_45680 : bv 32 := 0x00a4a623.
Lemma F_45680 : fetch_word Plain.M.loaded_segments (0x456c8 : word) = Some W_45680.
Proof. vm_refl. Qed.
Lemma D_45680 : decode_any W_45680 = Some (Store SZ4 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_45684 : bv 32 := 0x0505b683.
Lemma F_45684 : fetch_word Plain.M.loaded_segments (0x456cc : word) = Some W_45684.
Proof. vm_refl. Qed.
Lemma D_45684 : decode_any W_45684 = Some (Load SZ8 true 13 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_45688 : bv 32 := 0x00090513.
Lemma F_45688 : fetch_word Plain.M.loaded_segments (0x456d0 : word) = Some W_45688.
Proof. vm_refl. Qed.
Lemma D_45688 : decode_any W_45688 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4568c : bv 32 := 0x00048593.
Lemma F_4568c : fetch_word Plain.M.loaded_segments (0x456d4 : word) = Some W_4568c.
Proof. vm_refl. Qed.
Lemma D_4568c : decode_any W_4568c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45690 : bv 32 := 0x00040613.
Lemma F_45690 : fetch_word Plain.M.loaded_segments (0x456d8 : word) = Some W_45690.
Proof. vm_refl. Qed.
Lemma D_45690 : decode_any W_45690 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45694 : bv 32 := 0x000680e7.
Lemma F_45694 : fetch_word Plain.M.loaded_segments (0x456dc : word) = Some W_45694.
Proof. vm_refl. Qed.
Lemma D_45694 : decode_any W_45694 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45698 : bv 32 := 0x0104c503.
Lemma F_45698 : fetch_word Plain.M.loaded_segments (0x456e0 : word) = Some W_45698.
Proof. vm_refl. Qed.
Lemma D_45698 : decode_any W_45698 = Some (Load SZ1 false 10 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4569c : bv 32 := 0x1804b583.
Lemma F_4569c : fetch_word Plain.M.loaded_segments (0x456e4 : word) = Some W_4569c.
Proof. vm_refl. Qed.
Lemma D_4569c : decode_any W_4569c = Some (Load SZ8 true 11 9 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_456a0 : bv 32 := 0x00154513.
Lemma F_456a0 : fetch_word Plain.M.loaded_segments (0x456e8 : word) = Some W_456a0.
Proof. vm_refl. Qed.
Lemma D_456a0 : decode_any W_456a0 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_456a4 : bv 32 := 0x00a48423.
Lemma F_456a4 : fetch_word Plain.M.loaded_segments (0x456ec : word) = Some W_456a4.
Proof. vm_refl. Qed.
Lemma D_456a4 : decode_any W_456a4 = Some (Store SZ1 9 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_456a8 : bv 32 := 0xfe858593.
Lemma F_456a8 : fetch_word Plain.M.loaded_segments (0x456f0 : word) = Some W_456a8.
Proof. vm_refl. Qed.
Lemma D_456a8 : decode_any W_456a8 = Some (OpImm ALU_ADD 11 11 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_456ac : bv 32 := 0x18b4b023.
Lemma F_456ac : fetch_word Plain.M.loaded_segments (0x456f4 : word) = Some W_456ac.
Proof. vm_refl. Qed.
Lemma D_456ac : decode_any W_456ac = Some (Store SZ8 9 11 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_456b0 : bv 32 := 0x0094c503.
Lemma F_456b0 : fetch_word Plain.M.loaded_segments (0x456f8 : word) = Some W_456b0.
Proof. vm_refl. Qed.
Lemma D_456b0 : decode_any W_456b0 = Some (Load SZ1 false 10 9 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_456b4 : bv 32 := 0xf00500e3.
Lemma F_456b4 : fetch_word Plain.M.loaded_segments (0x456fc : word) = Some W_456b4.
Proof. vm_refl. Qed.
Lemma D_456b4 : decode_any W_456b4 = Some (Branch BC_EQ 10 0 7936, 4%Z).
Proof. vm_refl. Qed.

Definition W_456b8 : bv 32 := 0x06813083.
Lemma F_456b8 : fetch_word Plain.M.loaded_segments (0x45700 : word) = Some W_456b8.
Proof. vm_refl. Qed.
Lemma D_456b8 : decode_any W_456b8 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_456bc : bv 32 := 0x06013403.
Lemma F_456bc : fetch_word Plain.M.loaded_segments (0x45704 : word) = Some W_456bc.
Proof. vm_refl. Qed.
Lemma D_456bc : decode_any W_456bc = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_456c0 : bv 32 := 0x05813483.
Lemma F_456c0 : fetch_word Plain.M.loaded_segments (0x45708 : word) = Some W_456c0.
Proof. vm_refl. Qed.
Lemma D_456c0 : decode_any W_456c0 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_456c4 : bv 32 := 0x05013903.
Lemma F_456c4 : fetch_word Plain.M.loaded_segments (0x4570c : word) = Some W_456c4.
Proof. vm_refl. Qed.
Lemma D_456c4 : decode_any W_456c4 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_456c8 : bv 32 := 0x04813983.
Lemma F_456c8 : fetch_word Plain.M.loaded_segments (0x45710 : word) = Some W_456c8.
Proof. vm_refl. Qed.
Lemma D_456c8 : decode_any W_456c8 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_456cc : bv 32 := 0x04013a03.
Lemma F_456cc : fetch_word Plain.M.loaded_segments (0x45714 : word) = Some W_456cc.
Proof. vm_refl. Qed.
Lemma D_456cc : decode_any W_456cc = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_456d0 : bv 32 := 0x03813a83.
Lemma F_456d0 : fetch_word Plain.M.loaded_segments (0x45718 : word) = Some W_456d0.
Proof. vm_refl. Qed.
Lemma D_456d0 : decode_any W_456d0 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_456d4 : bv 32 := 0x03013b03.
Lemma F_456d4 : fetch_word Plain.M.loaded_segments (0x4571c : word) = Some W_456d4.
Proof. vm_refl. Qed.
Lemma D_456d4 : decode_any W_456d4 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_456d8 : bv 32 := 0x02813b83.
Lemma F_456d8 : fetch_word Plain.M.loaded_segments (0x45720 : word) = Some W_456d8.
Proof. vm_refl. Qed.
Lemma D_456d8 : decode_any W_456d8 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_456dc : bv 32 := 0x02013c03.
Lemma F_456dc : fetch_word Plain.M.loaded_segments (0x45724 : word) = Some W_456dc.
Proof. vm_refl. Qed.
Lemma D_456dc : decode_any W_456dc = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_456e0 : bv 32 := 0x07010113.
Lemma F_456e0 : fetch_word Plain.M.loaded_segments (0x45728 : word) = Some W_456e0.
Proof. vm_refl. Qed.
Lemma D_456e0 : decode_any W_456e0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_456e4 : bv 32 := 0x00008067.
Lemma F_456e4 : fetch_word Plain.M.loaded_segments (0x4572c : word) = Some W_456e4.
Proof. vm_refl. Qed.
Lemma D_456e4 : decode_any W_456e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_456e8 : bv 32 := 0x01000513.
Lemma F_456e8 : fetch_word Plain.M.loaded_segments (0x45730 : word) = Some W_456e8.
Proof. vm_refl. Qed.
Lemma D_456e8 : decode_any W_456e8 = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_456ec : bv 32 := 0x7241e0ef.
Lemma F_456ec : fetch_word Plain.M.loaded_segments (0x45734 : word) = Some W_456ec.
Proof. vm_refl. Qed.
Lemma D_456ec : decode_any W_456ec = Some (Jal 1 124708, 4%Z).
Proof. vm_refl. Qed.

Definition W_456f0 : bv 32 := 0x00050413.
Lemma F_456f0 : fetch_word Plain.M.loaded_segments (0x45738 : word) = Some W_456f0.
Proof. vm_refl. Qed.
Lemma D_456f0 : decode_any W_456f0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_456f4 : bv 32 := 0xfffce517.
Lemma F_456f4 : fetch_word Plain.M.loaded_segments (0x4573c : word) = Some W_456f4.
Proof. vm_refl. Qed.
Lemma D_456f4 : decode_any W_456f4 = Some (Auipc 10 1048526, 4%Z).
Proof. vm_refl. Qed.

Definition W_456f8 : bv 32 := 0xa6250593.
Lemma F_456f8 : fetch_word Plain.M.loaded_segments (0x45740 : word) = Some W_456f8.
Proof. vm_refl. Qed.
Lemma D_456f8 : decode_any W_456f8 = Some (OpImm ALU_ADD 11 10 2658, 4%Z).
Proof. vm_refl. Qed.

Definition W_456fc : bv 32 := 0x00810513.
Lemma F_456fc : fetch_word Plain.M.loaded_segments (0x45744 : word) = Some W_456fc.
Proof. vm_refl. Qed.
Lemma D_456fc : decode_any W_456fc = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_45700 : bv 32 := 0xb48f70ef.
Lemma F_45700 : fetch_word Plain.M.loaded_segments (0x45748 : word) = Some W_45700.
Proof. vm_refl. Qed.
Lemma D_45700 : decode_any W_45700 = Some (Jal 1 2061128, 4%Z).
Proof. vm_refl. Qed.

Definition W_45704 : bv 32 := 0x00810593.
Lemma F_45704 : fetch_word Plain.M.loaded_segments (0x4574c : word) = Some W_45704.
Proof. vm_refl. Qed.
Lemma D_45704 : decode_any W_45704 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_45708 : bv 32 := 0x00040513.
Lemma F_45708 : fetch_word Plain.M.loaded_segments (0x45750 : word) = Some W_45708.
Proof. vm_refl. Qed.
Lemma D_45708 : decode_any W_45708 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4570c : bv 32 := 0xbfcf70ef.
Lemma F_4570c : fetch_word Plain.M.loaded_segments (0x45754 : word) = Some W_4570c.
Proof. vm_refl. Qed.
Lemma D_4570c : decode_any W_4570c = Some (Jal 1 2061308, 4%Z).
Proof. vm_refl. Qed.

Definition W_45710 : bv 32 := 0x00080517.
Lemma F_45710 : fetch_word Plain.M.loaded_segments (0x45758 : word) = Some W_45710.
Proof. vm_refl. Qed.
Lemma D_45710 : decode_any W_45710 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_45714 : bv 32 := 0x24853603.
Lemma F_45714 : fetch_word Plain.M.loaded_segments (0x4575c : word) = Some W_45714.
Proof. vm_refl. Qed.
Lemma D_45714 : decode_any W_45714 = Some (Load SZ8 true 12 10 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_45718 : bv 32 := 0x0007a517.
Lemma F_45718 : fetch_word Plain.M.loaded_segments (0x45760 : word) = Some W_45718.
Proof. vm_refl. Qed.
Lemma D_45718 : decode_any W_45718 = Some (Auipc 10 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_4571c : bv 32 := 0x46050593.
Lemma F_4571c : fetch_word Plain.M.loaded_segments (0x45764 : word) = Some W_4571c.
Proof. vm_refl. Qed.
Lemma D_4571c : decode_any W_4571c = Some (OpImm ALU_ADD 11 10 1120, 4%Z).
Proof. vm_refl. Qed.

Definition W_45720 : bv 32 := 0x00040513.
Lemma F_45720 : fetch_word Plain.M.loaded_segments (0x45768 : word) = Some W_45720.
Proof. vm_refl. Qed.
Lemma D_45720 : decode_any W_45720 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45724 : bv 32 := 0x0f11e0ef.
Lemma F_45724 : fetch_word Plain.M.loaded_segments (0x4576c : word) = Some W_45724.
Proof. vm_refl. Qed.
Lemma D_45724 : decode_any W_45724 = Some (Jal 1 125168, 4%Z).
Proof. vm_refl. Qed.

Definition W_45728 : bv 32 := 0x00814583.
Lemma F_45728 : fetch_word Plain.M.loaded_segments (0x45770 : word) = Some W_45728.
Proof. vm_refl. Qed.
Lemma D_45728 : decode_any W_45728 = Some (Load SZ1 false 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4572c : bv 32 := 0x0015f593.
Lemma F_4572c : fetch_word Plain.M.loaded_segments (0x45774 : word) = Some W_4572c.
Proof. vm_refl. Qed.
Lemma D_4572c : decode_any W_4572c = Some (OpImm ALU_AND 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_45730 : bv 32 := 0x00050493.
Lemma F_45730 : fetch_word Plain.M.loaded_segments (0x45778 : word) = Some W_45730.
Proof. vm_refl. Qed.
Lemma D_45730 : decode_any W_45730 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45734 : bv 32 := 0x02058263.
Lemma F_45734 : fetch_word Plain.M.loaded_segments (0x4577c : word) = Some W_45734.
Proof. vm_refl. Qed.
Lemma D_45734 : decode_any W_45734 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_45738 : bv 32 := 0x00813583.
Lemma F_45738 : fetch_word Plain.M.loaded_segments (0x45780 : word) = Some W_45738.
Proof. vm_refl. Qed.
Lemma D_45738 : decode_any W_45738 = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4573c : bv 32 := 0x01813503.
Lemma F_4573c : fetch_word Plain.M.loaded_segments (0x45784 : word) = Some W_4573c.
Proof. vm_refl. Qed.
Lemma D_4573c : decode_any W_4573c = Some (Load SZ8 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_45740 : bv 32 := 0xffe5f593.
Lemma F_45740 : fetch_word Plain.M.loaded_segments (0x45788 : word) = Some W_45740.
Proof. vm_refl. Qed.
Lemma D_45740 : decode_any W_45740 = Some (OpImm ALU_AND 11 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_45744 : bv 32 := 0x6381e0ef.
Lemma F_45744 : fetch_word Plain.M.loaded_segments (0x4578c : word) = Some W_45744.
Proof. vm_refl. Qed.
Lemma D_45744 : decode_any W_45744 = Some (Jal 1 124472, 4%Z).
Proof. vm_refl. Qed.

Definition W_45748 : bv 32 := 0x0100006f.
Lemma F_45748 : fetch_word Plain.M.loaded_segments (0x45790 : word) = Some W_45748.
Proof. vm_refl. Qed.
Lemma D_45748 : decode_any W_45748 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4574c : bv 32 := 0x00050493.
Lemma F_4574c : fetch_word Plain.M.loaded_segments (0x45794 : word) = Some W_4574c.
Proof. vm_refl. Qed.
Lemma D_4574c : decode_any W_4574c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45750 : bv 32 := 0x00040513.
Lemma F_45750 : fetch_word Plain.M.loaded_segments (0x45798 : word) = Some W_45750.
Proof. vm_refl. Qed.
Lemma D_45750 : decode_any W_45750 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45754 : bv 32 := 0x7c01e0ef.
Lemma F_45754 : fetch_word Plain.M.loaded_segments (0x4579c : word) = Some W_45754.
Proof. vm_refl. Qed.
Lemma D_45754 : decode_any W_45754 = Some (Jal 1 124864, 4%Z).
Proof. vm_refl. Qed.

Definition W_45758 : bv 32 := 0x00048513.
Lemma F_45758 : fetch_word Plain.M.loaded_segments (0x457a0 : word) = Some W_45758.
Proof. vm_refl. Qed.
Lemma D_45758 : decode_any W_45758 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4575c : bv 32 := 0x0b55c0ef.
Lemma F_4575c : fetch_word Plain.M.loaded_segments (0x457a4 : word) = Some W_4575c.
Proof. vm_refl. Qed.
Lemma D_4575c : decode_any W_4575c = Some (Jal 1 379060, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3fc7c_3fe84.
Module Ns0_code_r3fb3c_3fc7c.
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

Definition W_45418 : bv 32 := 0xfb010113.
Lemma F_45418 : fetch_word Plain.M.loaded_segments (0x45460 : word) = Some W_45418.
Proof. vm_refl. Qed.
Lemma D_45418 : decode_any W_45418 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4541c : bv 32 := 0x04113423.
Lemma F_4541c : fetch_word Plain.M.loaded_segments (0x45464 : word) = Some W_4541c.
Proof. vm_refl. Qed.
Lemma D_4541c : decode_any W_4541c = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_45420 : bv 32 := 0x04813023.
Lemma F_45420 : fetch_word Plain.M.loaded_segments (0x45468 : word) = Some W_45420.
Proof. vm_refl. Qed.
Lemma D_45420 : decode_any W_45420 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_45424 : bv 32 := 0x02913c23.
Lemma F_45424 : fetch_word Plain.M.loaded_segments (0x4546c : word) = Some W_45424.
Proof. vm_refl. Qed.
Lemma D_45424 : decode_any W_45424 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_45428 : bv 32 := 0x03213823.
Lemma F_45428 : fetch_word Plain.M.loaded_segments (0x45470 : word) = Some W_45428.
Proof. vm_refl. Qed.
Lemma D_45428 : decode_any W_45428 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4542c : bv 32 := 0x03313423.
Lemma F_4542c : fetch_word Plain.M.loaded_segments (0x45474 : word) = Some W_4542c.
Proof. vm_refl. Qed.
Lemma D_4542c : decode_any W_4542c = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_45430 : bv 32 := 0x00050413.
Lemma F_45430 : fetch_word Plain.M.loaded_segments (0x45478 : word) = Some W_45430.
Proof. vm_refl. Qed.
Lemma D_45430 : decode_any W_45430 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45434 : bv 32 := 0x14854503.
Lemma F_45434 : fetch_word Plain.M.loaded_segments (0x4547c : word) = Some W_45434.
Proof. vm_refl. Qed.
Lemma D_45434 : decode_any W_45434 = Some (Load SZ1 false 10 10 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_45438 : bv 32 := 0x00100593.
Lemma F_45438 : fetch_word Plain.M.loaded_segments (0x45480 : word) = Some W_45438.
Proof. vm_refl. Qed.
Lemma D_45438 : decode_any W_45438 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4543c : bv 32 := 0x00157513.
Lemma F_4543c : fetch_word Plain.M.loaded_segments (0x45484 : word) = Some W_4543c.
Proof. vm_refl. Qed.
Lemma D_4543c : decode_any W_4543c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_45440 : bv 32 := 0x00b41423.
Lemma F_45440 : fetch_word Plain.M.loaded_segments (0x45488 : word) = Some W_45440.
Proof. vm_refl. Qed.
Lemma D_45440 : decode_any W_45440 = Some (Store SZ2 8 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_45444 : bv 32 := 0x00051663.
Lemma F_45444 : fetch_word Plain.M.loaded_segments (0x4548c : word) = Some W_45444.
Proof. vm_refl. Qed.
Lemma D_45444 : decode_any W_45444 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_45448 : bv 32 := 0x14041423.
Lemma F_45448 : fetch_word Plain.M.loaded_segments (0x45490 : word) = Some W_45448.
Proof. vm_refl. Qed.
Lemma D_45448 : decode_any W_45448 = Some (Store SZ2 8 0 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_4544c : bv 32 := 0x0100006f.
Lemma F_4544c : fetch_word Plain.M.loaded_segments (0x45494 : word) = Some W_4544c.
Proof. vm_refl. Qed.
Lemma D_4544c : decode_any W_4544c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_45450 : bv 32 := 0x15843503.
Lemma F_45450 : fetch_word Plain.M.loaded_segments (0x45498 : word) = Some W_45450.
Proof. vm_refl. Qed.
Lemma D_45450 : decode_any W_45450 = Some (Load SZ8 true 10 8 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_45454 : bv 32 := 0x00050023.
Lemma F_45454 : fetch_word Plain.M.loaded_segments (0x4549c : word) = Some W_45454.
Proof. vm_refl. Qed.
Lemma D_45454 : decode_any W_45454 = Some (Store SZ1 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45458 : bv 32 := 0x14043823.
Lemma F_45458 : fetch_word Plain.M.loaded_segments (0x454a0 : word) = Some W_45458.
Proof. vm_refl. Qed.
Lemma D_45458 : decode_any W_45458 = Some (Store SZ8 8 0 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_4545c : bv 32 := 0x16043603.
Lemma F_4545c : fetch_word Plain.M.loaded_segments (0x454a4 : word) = Some W_4545c.
Proof. vm_refl. Qed.
Lemma D_4545c : decode_any W_4545c = Some (Load SZ8 true 12 8 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_45460 : bv 32 := 0x17843503.
Lemma F_45460 : fetch_word Plain.M.loaded_segments (0x454a8 : word) = Some W_45460.
Proof. vm_refl. Qed.
Lemma D_45460 : decode_any W_45460 = Some (Load SZ8 true 10 8 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_45464 : bv 32 := 0x18843583.
Lemma F_45464 : fetch_word Plain.M.loaded_segments (0x454ac : word) = Some W_45464.
Proof. vm_refl. Qed.
Lemma D_45464 : decode_any W_45464 = Some (Load SZ8 true 11 8 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_45468 : bv 32 := 0x16c43423.
Lemma F_45468 : fetch_word Plain.M.loaded_segments (0x454b0 : word) = Some W_45468.
Proof. vm_refl. Qed.
Lemma D_45468 : decode_any W_45468 = Some (Store SZ8 8 12 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_4546c : bv 32 := 0x18a43023.
Lemma F_4546c : fetch_word Plain.M.loaded_segments (0x454b4 : word) = Some W_4546c.
Proof. vm_refl. Qed.
Lemma D_4546c : decode_any W_4546c = Some (Store SZ8 8 10 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_45470 : bv 32 := 0x00b57c63.
Lemma F_45470 : fetch_word Plain.M.loaded_segments (0x454b8 : word) = Some W_45470.
Proof. vm_refl. Qed.
Lemma D_45470 : decode_any W_45470 = Some (Branch BC_GEU 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_45474 : bv 32 := 0x01850913.
Lemma F_45474 : fetch_word Plain.M.loaded_segments (0x454bc : word) = Some W_45474.
Proof. vm_refl. Qed.
Lemma D_45474 : decode_any W_45474 = Some (OpImm ALU_ADD 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_45478 : bv 32 := 0x00052023.
Lemma F_45478 : fetch_word Plain.M.loaded_segments (0x454c0 : word) = Some W_45478.
Proof. vm_refl. Qed.
Lemma D_45478 : decode_any W_45478 = Some (Store SZ4 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4547c : bv 32 := 0x00053423.
Lemma F_4547c : fetch_word Plain.M.loaded_segments (0x454c4 : word) = Some W_4547c.
Proof. vm_refl. Qed.
Lemma D_4547c : decode_any W_4547c = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_45480 : bv 32 := 0x00053823.
Lemma F_45480 : fetch_word Plain.M.loaded_segments (0x454c8 : word) = Some W_45480.
Proof. vm_refl. Qed.
Lemma D_45480 : decode_any W_45480 = Some (Store SZ8 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_45484 : bv 32 := 0x0b00006f.
Lemma F_45484 : fetch_word Plain.M.loaded_segments (0x454cc : word) = Some W_45484.
Proof. vm_refl. Qed.
Lemma D_45484 : decode_any W_45484 = Some (Jal 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_45488 : bv 32 := 0xfffce617.
Lemma F_45488 : fetch_word Plain.M.loaded_segments (0x454d0 : word) = Some W_45488.
Proof. vm_refl. Qed.
Lemma D_45488 : decode_any W_45488 = Some (Auipc 12 1048526, 4%Z).
Proof. vm_refl. Qed.

Definition W_4548c : bv 32 := 0x36063603.
Lemma F_4548c : fetch_word Plain.M.loaded_segments (0x454d4 : word) = Some W_4548c.
Proof. vm_refl. Qed.
Lemma D_4548c : decode_any W_4548c = Some (Load SZ8 true 12 12 864, 4%Z).
Proof. vm_refl. Qed.

Definition W_45490 : bv 32 := 0xfffce697.
Lemma F_45490 : fetch_word Plain.M.loaded_segments (0x454d8 : word) = Some W_45490.
Proof. vm_refl. Qed.
Lemma D_45490 : decode_any W_45490 = Some (Auipc 13 1048526, 4%Z).
Proof. vm_refl. Qed.

Definition W_45494 : bv 32 := 0x3786b683.
Lemma F_45494 : fetch_word Plain.M.loaded_segments (0x454dc : word) = Some W_45494.
Proof. vm_refl. Qed.
Lemma D_45494 : decode_any W_45494 = Some (Load SZ8 true 13 13 888, 4%Z).
Proof. vm_refl. Qed.

Definition W_45498 : bv 32 := 0x40a585b3.
Lemma F_45498 : fetch_word Plain.M.loaded_segments (0x454e0 : word) = Some W_45498.
Proof. vm_refl. Qed.
Lemma D_45498 : decode_any W_45498 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4549c : bv 32 := 0x4035d593.
Lemma F_4549c : fetch_word Plain.M.loaded_segments (0x454e4 : word) = Some W_4549c.
Proof. vm_refl. Qed.
Lemma D_4549c : decode_any W_4549c = Some (ShiftImm ALU_SRA 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_454a0 : bv 32 := 0x02c585b3.
Lemma F_454a0 : fetch_word Plain.M.loaded_segments (0x454e8 : word) = Some W_454a0.
Proof. vm_refl. Qed.
Lemma D_454a0 : decode_any W_454a0 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_454a4 : bv 32 := 0x17840513.
Lemma F_454a4 : fetch_word Plain.M.loaded_segments (0x454ec : word) = Some W_454a4.
Proof. vm_refl. Qed.
Lemma D_454a4 : decode_any W_454a4 = Some (OpImm ALU_ADD 10 8 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_454a8 : bv 32 := 0x00d5e863.
Lemma F_454a8 : fetch_word Plain.M.loaded_segments (0x454f0 : word) = Some W_454a8.
Proof. vm_refl. Qed.
Lemma D_454a8 : decode_any W_454a8 = Some (Branch BC_LTU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_454ac : bv 32 := 0xfffce597.
Lemma F_454ac : fetch_word Plain.M.loaded_segments (0x454f4 : word) = Some W_454ac.
Proof. vm_refl. Qed.
Lemma D_454ac : decode_any W_454ac = Some (Auipc 11 1048526, 4%Z).
Proof. vm_refl. Qed.

Definition W_454b0 : bv 32 := 0x37c5b583.
Lemma F_454b0 : fetch_word Plain.M.loaded_segments (0x454f8 : word) = Some W_454b0.
Proof. vm_refl. Qed.
Lemma D_454b0 : decode_any W_454b0 = Some (Load SZ8 true 11 11 892, 4%Z).
Proof. vm_refl. Qed.

Definition W_454b4 : bv 32 := 0x0100006f.
Lemma F_454b4 : fetch_word Plain.M.loaded_segments (0x454fc : word) = Some W_454b4.
Proof. vm_refl. Qed.
Lemma D_454b4 : decode_any W_454b4 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_454b8 : bv 32 := 0x00159593.
Lemma F_454b8 : fetch_word Plain.M.loaded_segments (0x45500 : word) = Some W_454b8.
Proof. vm_refl. Qed.
Lemma D_454b8 : decode_any W_454b8 = Some (ShiftImm ALU_SLL 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_454bc : bv 32 := 0x0015b613.
Lemma F_454bc : fetch_word Plain.M.loaded_segments (0x45504 : word) = Some W_454bc.
Proof. vm_refl. Qed.
Lemma D_454bc : decode_any W_454bc = Some (OpImm ALU_SLTU 12 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_454c0 : bv 32 := 0x00c5e5b3.
Lemma F_454c0 : fetch_word Plain.M.loaded_segments (0x45508 : word) = Some W_454c0.
Proof. vm_refl. Qed.
Lemma D_454c0 : decode_any W_454c0 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_454c4 : bv 32 := 0x02a13023.
Lemma F_454c4 : fetch_word Plain.M.loaded_segments (0x4550c : word) = Some W_454c4.
Proof. vm_refl. Qed.
Lemma D_454c4 : decode_any W_454c4 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_454c8 : bv 32 := 0xe95ff0ef.
Lemma F_454c8 : fetch_word Plain.M.loaded_segments (0x45510 : word) = Some W_454c8.
Proof. vm_refl. Qed.
Lemma D_454c8 : decode_any W_454c8 = Some (Jal 1 2096788, 4%Z).
Proof. vm_refl. Qed.

Definition W_454cc : bv 32 := 0x17843683.
Lemma F_454cc : fetch_word Plain.M.loaded_segments (0x45514 : word) = Some W_454cc.
Proof. vm_refl. Qed.
Lemma D_454cc : decode_any W_454cc = Some (Load SZ8 true 13 8 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_454d0 : bv 32 := 0x18043603.
Lemma F_454d0 : fetch_word Plain.M.loaded_segments (0x45518 : word) = Some W_454d0.
Proof. vm_refl. Qed.
Lemma D_454d0 : decode_any W_454d0 = Some (Load SZ8 true 12 8 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_454d4 : bv 32 := 0x00359713.
Lemma F_454d4 : fetch_word Plain.M.loaded_segments (0x4551c : word) = Some W_454d4.
Proof. vm_refl. Qed.
Lemma D_454d4 : decode_any W_454d4 = Some (ShiftImm ALU_SLL 14 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_454d8 : bv 32 := 0x00559593.
Lemma F_454d8 : fetch_word Plain.M.loaded_segments (0x45520 : word) = Some W_454d8.
Proof. vm_refl. Qed.
Lemma D_454d8 : decode_any W_454d8 = Some (ShiftImm ALU_SLL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_454dc : bv 32 := 0x01850913.
Lemma F_454dc : fetch_word Plain.M.loaded_segments (0x45524 : word) = Some W_454dc.
Proof. vm_refl. Qed.
Lemma D_454dc : decode_any W_454dc = Some (OpImm ALU_ADD 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_454e0 : bv 32 := 0x40e585b3.
Lemma F_454e0 : fetch_word Plain.M.loaded_segments (0x45528 : word) = Some W_454e0.
Proof. vm_refl. Qed.
Lemma D_454e0 : decode_any W_454e0 = Some (Op ALU_SUB 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_454e4 : bv 32 := 0x00b509b3.
Lemma F_454e4 : fetch_word Plain.M.loaded_segments (0x4552c : word) = Some W_454e4.
Proof. vm_refl. Qed.
Lemma D_454e4 : decode_any W_454e4 = Some (Op ALU_ADD 19 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_454e8 : bv 32 := 0x40d60633.
Lemma F_454e8 : fetch_word Plain.M.loaded_segments (0x45530 : word) = Some W_454e8.
Proof. vm_refl. Qed.
Lemma D_454e8 : decode_any W_454e8 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_454ec : bv 32 := 0x40c504b3.
Lemma F_454ec : fetch_word Plain.M.loaded_segments (0x45534 : word) = Some W_454ec.
Proof. vm_refl. Qed.
Lemma D_454ec : decode_any W_454ec = Some (Op ALU_SUB 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_454f0 : bv 32 := 0x00052023.
Lemma F_454f0 : fetch_word Plain.M.loaded_segments (0x45538 : word) = Some W_454f0.
Proof. vm_refl. Qed.
Lemma D_454f0 : decode_any W_454f0 = Some (Store SZ4 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_454f4 : bv 32 := 0x00053423.
Lemma F_454f4 : fetch_word Plain.M.loaded_segments (0x4553c : word) = Some W_454f4.
Proof. vm_refl. Qed.
Lemma D_454f4 : decode_any W_454f4 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_454f8 : bv 32 := 0x00053823.
Lemma F_454f8 : fetch_word Plain.M.loaded_segments (0x45540 : word) = Some W_454f8.
Proof. vm_refl. Qed.
Lemma D_454f8 : decode_any W_454f8 = Some (Store SZ8 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_454fc : bv 32 := 0x00048513.
Lemma F_454fc : fetch_word Plain.M.loaded_segments (0x45544 : word) = Some W_454fc.
Proof. vm_refl. Qed.
Lemma D_454fc : decode_any W_454fc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45500 : bv 32 := 0x00068593.
Lemma F_45500 : fetch_word Plain.M.loaded_segments (0x45548 : word) = Some W_45500.
Proof. vm_refl. Qed.
Lemma D_45500 : decode_any W_45500 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45504 : bv 32 := 0x42c740ef.
Lemma F_45504 : fetch_word Plain.M.loaded_segments (0x4554c : word) = Some W_45504.
Proof. vm_refl. Qed.
Lemma D_45504 : decode_any W_45504 = Some (Jal 1 476204, 4%Z).
Proof. vm_refl. Qed.

Definition W_45508 : bv 32 := 0x17843503.
Lemma F_45508 : fetch_word Plain.M.loaded_segments (0x45550 : word) = Some W_45508.
Proof. vm_refl. Qed.
Lemma D_45508 : decode_any W_45508 = Some (Load SZ8 true 10 8 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_4550c : bv 32 := 0x18843583.
Lemma F_4550c : fetch_word Plain.M.loaded_segments (0x45554 : word) = Some W_4550c.
Proof. vm_refl. Qed.
Lemma D_4550c : decode_any W_4550c = Some (Load SZ8 true 11 8 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_45510 : bv 32 := 0x16943c23.
Lemma F_45510 : fetch_word Plain.M.loaded_segments (0x45558 : word) = Some W_45510.
Proof. vm_refl. Qed.
Lemma D_45510 : decode_any W_45510 = Some (Store SZ8 8 9 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_45514 : bv 32 := 0x19243023.
Lemma F_45514 : fetch_word Plain.M.loaded_segments (0x4555c : word) = Some W_45514.
Proof. vm_refl. Qed.
Lemma D_45514 : decode_any W_45514 = Some (Store SZ8 8 18 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_45518 : bv 32 := 0x19343423.
Lemma F_45518 : fetch_word Plain.M.loaded_segments (0x45560 : word) = Some W_45518.
Proof. vm_refl. Qed.
Lemma D_45518 : decode_any W_45518 = Some (Store SZ8 8 19 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_4551c : bv 32 := 0x00a13023.
Lemma F_4551c : fetch_word Plain.M.loaded_segments (0x45564 : word) = Some W_4551c.
Proof. vm_refl. Qed.
Lemma D_4551c : decode_any W_4551c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45520 : bv 32 := 0x00a13423.
Lemma F_45520 : fetch_word Plain.M.loaded_segments (0x45568 : word) = Some W_45520.
Proof. vm_refl. Qed.
Lemma D_45520 : decode_any W_45520 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_45524 : bv 32 := 0x00a13823.
Lemma F_45524 : fetch_word Plain.M.loaded_segments (0x4556c : word) = Some W_45524.
Proof. vm_refl. Qed.
Lemma D_45524 : decode_any W_45524 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_45528 : bv 32 := 0x00b13c23.
Lemma F_45528 : fetch_word Plain.M.loaded_segments (0x45570 : word) = Some W_45528.
Proof. vm_refl. Qed.
Lemma D_45528 : decode_any W_45528 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4552c : bv 32 := 0x00010513.
Lemma F_4552c : fetch_word Plain.M.loaded_segments (0x45574 : word) = Some W_4552c.
Proof. vm_refl. Qed.
Lemma D_4552c : decode_any W_4552c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_45530 : bv 32 := 0xdc1ff0ef.
Lemma F_45530 : fetch_word Plain.M.loaded_segments (0x45578 : word) = Some W_45530.
Proof. vm_refl. Qed.
Lemma D_45530 : decode_any W_45530 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_45534 : bv 32 := 0x19243023.
Lemma F_45534 : fetch_word Plain.M.loaded_segments (0x4557c : word) = Some W_45534.
Proof. vm_refl. Qed.
Lemma D_45534 : decode_any W_45534 = Some (Store SZ8 8 18 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_45538 : bv 32 := 0x00042623.
Lemma F_45538 : fetch_word Plain.M.loaded_segments (0x45580 : word) = Some W_45538.
Proof. vm_refl. Qed.
Lemma D_45538 : decode_any W_45538 = Some (Store SZ4 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4553c : bv 32 := 0x04813083.
Lemma F_4553c : fetch_word Plain.M.loaded_segments (0x45584 : word) = Some W_4553c.
Proof. vm_refl. Qed.
Lemma D_4553c : decode_any W_4553c = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_45540 : bv 32 := 0x04013403.
Lemma F_45540 : fetch_word Plain.M.loaded_segments (0x45588 : word) = Some W_45540.
Proof. vm_refl. Qed.
Lemma D_45540 : decode_any W_45540 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_45544 : bv 32 := 0x03813483.
Lemma F_45544 : fetch_word Plain.M.loaded_segments (0x4558c : word) = Some W_45544.
Proof. vm_refl. Qed.
Lemma D_45544 : decode_any W_45544 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_45548 : bv 32 := 0x03013903.
Lemma F_45548 : fetch_word Plain.M.loaded_segments (0x45590 : word) = Some W_45548.
Proof. vm_refl. Qed.
Lemma D_45548 : decode_any W_45548 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4554c : bv 32 := 0x02813983.
Lemma F_4554c : fetch_word Plain.M.loaded_segments (0x45594 : word) = Some W_4554c.
Proof. vm_refl. Qed.
Lemma D_4554c : decode_any W_4554c = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_45550 : bv 32 := 0x05010113.
Lemma F_45550 : fetch_word Plain.M.loaded_segments (0x45598 : word) = Some W_45550.
Proof. vm_refl. Qed.
Lemma D_45550 : decode_any W_45550 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_45554 : bv 32 := 0x00008067.
Lemma F_45554 : fetch_word Plain.M.loaded_segments (0x4559c : word) = Some W_45554.
Proof. vm_refl. Qed.
Lemma D_45554 : decode_any W_45554 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r3fb3c_3fc7c.
Module Ns0_code_41aa4_42408.
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

Definition W_41aa4 : bv 32 := 0xfd010113.
Lemma F_41aa4 : fetch_word Plain.M.loaded_segments (0x41aec : word) = Some W_41aa4.
Proof. vm_refl. Qed.
Lemma D_41aa4 : decode_any W_41aa4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_41aa8 : bv 32 := 0x02113423.
Lemma F_41aa8 : fetch_word Plain.M.loaded_segments (0x41af0 : word) = Some W_41aa8.
Proof. vm_refl. Qed.
Lemma D_41aa8 : decode_any W_41aa8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41aac : bv 32 := 0x02813023.
Lemma F_41aac : fetch_word Plain.M.loaded_segments (0x41af4 : word) = Some W_41aac.
Proof. vm_refl. Qed.
Lemma D_41aac : decode_any W_41aac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ab0 : bv 32 := 0x00913c23.
Lemma F_41ab0 : fetch_word Plain.M.loaded_segments (0x41af8 : word) = Some W_41ab0.
Proof. vm_refl. Qed.
Lemma D_41ab0 : decode_any W_41ab0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ab4 : bv 32 := 0x01213823.
Lemma F_41ab4 : fetch_word Plain.M.loaded_segments (0x41afc : word) = Some W_41ab4.
Proof. vm_refl. Qed.
Lemma D_41ab4 : decode_any W_41ab4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ab8 : bv 32 := 0x00058413.
Lemma F_41ab8 : fetch_word Plain.M.loaded_segments (0x41b00 : word) = Some W_41ab8.
Proof. vm_refl. Qed.
Lemma D_41ab8 : decode_any W_41ab8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41abc : bv 32 := 0x00855593.
Lemma F_41abc : fetch_word Plain.M.loaded_segments (0x41b04 : word) = Some W_41abc.
Proof. vm_refl. Qed.
Lemma D_41abc : decode_any W_41abc = Some (ShiftImm ALU_SRL 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ac0 : bv 32 := 0x00851513.
Lemma F_41ac0 : fetch_word Plain.M.loaded_segments (0x41b08 : word) = Some W_41ac0.
Proof. vm_refl. Qed.
Lemma D_41ac0 : decode_any W_41ac0 = Some (ShiftImm ALU_SLL 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ac4 : bv 32 := 0x00b56533.
Lemma F_41ac4 : fetch_word Plain.M.loaded_segments (0x41b0c : word) = Some W_41ac4.
Proof. vm_refl. Qed.
Lemma D_41ac4 : decode_any W_41ac4 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ac8 : bv 32 := 0x00c10493.
Lemma F_41ac8 : fetch_word Plain.M.loaded_segments (0x41b10 : word) = Some W_41ac8.
Proof. vm_refl. Qed.
Lemma D_41ac8 : decode_any W_41ac8 = Some (OpImm ALU_ADD 9 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41acc : bv 32 := 0x00a11623.
Lemma F_41acc : fetch_word Plain.M.loaded_segments (0x41b14 : word) = Some W_41acc.
Proof. vm_refl. Qed.
Lemma D_41acc : decode_any W_41acc = Some (Store SZ2 2 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ad0 : bv 32 := 0x00e10913.
Lemma F_41ad0 : fetch_word Plain.M.loaded_segments (0x41b18 : word) = Some W_41ad0.
Proof. vm_refl. Qed.
Lemma D_41ad0 : decode_any W_41ad0 = Some (OpImm ALU_ADD 18 2 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ad4 : bv 32 := 0x0004c583.
Lemma F_41ad4 : fetch_word Plain.M.loaded_segments (0x41b1c : word) = Some W_41ad4.
Proof. vm_refl. Qed.
Lemma D_41ad4 : decode_any W_41ad4 = Some (Load SZ1 false 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ad8 : bv 32 := 0x00043503.
Lemma F_41ad8 : fetch_word Plain.M.loaded_segments (0x41b20 : word) = Some W_41ad8.
Proof. vm_refl. Qed.
Lemma D_41ad8 : decode_any W_41ad8 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41adc : bv 32 := 0x00b107a3.
Lemma F_41adc : fetch_word Plain.M.loaded_segments (0x41b24 : word) = Some W_41adc.
Proof. vm_refl. Qed.
Lemma D_41adc : decode_any W_41adc = Some (Store SZ1 2 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ae0 : bv 32 := 0x00f10593.
Lemma F_41ae0 : fetch_word Plain.M.loaded_segments (0x41b28 : word) = Some W_41ae0.
Proof. vm_refl. Qed.
Lemma D_41ae0 : decode_any W_41ae0 = Some (OpImm ALU_ADD 11 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ae4 : bv 32 := 0x1d8000ef.
Lemma F_41ae4 : fetch_word Plain.M.loaded_segments (0x41b2c : word) = Some W_41ae4.
Proof. vm_refl. Qed.
Lemma D_41ae4 : decode_any W_41ae4 = Some (Jal 1 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ae8 : bv 32 := 0x00148493.
Lemma F_41ae8 : fetch_word Plain.M.loaded_segments (0x41b30 : word) = Some W_41ae8.
Proof. vm_refl. Qed.
Lemma D_41ae8 : decode_any W_41ae8 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_41aec : bv 32 := 0xff2494e3.
Lemma F_41aec : fetch_word Plain.M.loaded_segments (0x41b34 : word) = Some W_41aec.
Proof. vm_refl. Qed.
Lemma D_41aec : decode_any W_41aec = Some (Branch BC_NE 9 18 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_41af0 : bv 32 := 0x02813083.
Lemma F_41af0 : fetch_word Plain.M.loaded_segments (0x41b38 : word) = Some W_41af0.
Proof. vm_refl. Qed.
Lemma D_41af0 : decode_any W_41af0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41af4 : bv 32 := 0x02013403.
Lemma F_41af4 : fetch_word Plain.M.loaded_segments (0x41b3c : word) = Some W_41af4.
Proof. vm_refl. Qed.
Lemma D_41af4 : decode_any W_41af4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41af8 : bv 32 := 0x01813483.
Lemma F_41af8 : fetch_word Plain.M.loaded_segments (0x41b40 : word) = Some W_41af8.
Proof. vm_refl. Qed.
Lemma D_41af8 : decode_any W_41af8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41afc : bv 32 := 0x01013903.
Lemma F_41afc : fetch_word Plain.M.loaded_segments (0x41b44 : word) = Some W_41afc.
Proof. vm_refl. Qed.
Lemma D_41afc : decode_any W_41afc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b00 : bv 32 := 0x03010113.
Lemma F_41b00 : fetch_word Plain.M.loaded_segments (0x41b48 : word) = Some W_41b00.
Proof. vm_refl. Qed.
Lemma D_41b00 : decode_any W_41b00 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b04 : bv 32 := 0x00008067.
Lemma F_41b04 : fetch_word Plain.M.loaded_segments (0x41b4c : word) = Some W_41b04.
Proof. vm_refl. Qed.
Lemma D_41b04 : decode_any W_41b04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b08 : bv 32 := 0xfd010113.
Lemma F_41b08 : fetch_word Plain.M.loaded_segments (0x41b50 : word) = Some W_41b08.
Proof. vm_refl. Qed.
Lemma D_41b08 : decode_any W_41b08 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b0c : bv 32 := 0x02113423.
Lemma F_41b0c : fetch_word Plain.M.loaded_segments (0x41b54 : word) = Some W_41b0c.
Proof. vm_refl. Qed.
Lemma D_41b0c : decode_any W_41b0c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b10 : bv 32 := 0x02813023.
Lemma F_41b10 : fetch_word Plain.M.loaded_segments (0x41b58 : word) = Some W_41b10.
Proof. vm_refl. Qed.
Lemma D_41b10 : decode_any W_41b10 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b14 : bv 32 := 0x00913c23.
Lemma F_41b14 : fetch_word Plain.M.loaded_segments (0x41b5c : word) = Some W_41b14.
Proof. vm_refl. Qed.
Lemma D_41b14 : decode_any W_41b14 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b18 : bv 32 := 0x01213823.
Lemma F_41b18 : fetch_word Plain.M.loaded_segments (0x41b60 : word) = Some W_41b18.
Proof. vm_refl. Qed.
Lemma D_41b18 : decode_any W_41b18 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b1c : bv 32 := 0x00058413.
Lemma F_41b1c : fetch_word Plain.M.loaded_segments (0x41b64 : word) = Some W_41b1c.
Proof. vm_refl. Qed.
Lemma D_41b1c : decode_any W_41b1c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b20 : bv 32 := 0x00855593.
Lemma F_41b20 : fetch_word Plain.M.loaded_segments (0x41b68 : word) = Some W_41b20.
Proof. vm_refl. Qed.
Lemma D_41b20 : decode_any W_41b20 = Some (ShiftImm ALU_SRL 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b24 : bv 32 := 0x00010637.
Lemma F_41b24 : fetch_word Plain.M.loaded_segments (0x41b6c : word) = Some W_41b24.
Proof. vm_refl. Qed.
Lemma D_41b24 : decode_any W_41b24 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b28 : bv 32 := 0x0185569b.
Lemma F_41b28 : fetch_word Plain.M.loaded_segments (0x41b70 : word) = Some W_41b28.
Proof. vm_refl. Qed.
Lemma D_41b28 : decode_any W_41b28 = Some (ShiftImm32 ALU_SRL 13 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b2c : bv 32 := 0xf0060613.
Lemma F_41b2c : fetch_word Plain.M.loaded_segments (0x41b74 : word) = Some W_41b2c.
Proof. vm_refl. Qed.
Lemma D_41b2c : decode_any W_41b2c = Some (OpImm ALU_ADD 12 12 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b30 : bv 32 := 0x00c5f5b3.
Lemma F_41b30 : fetch_word Plain.M.loaded_segments (0x41b78 : word) = Some W_41b30.
Proof. vm_refl. Qed.
Lemma D_41b30 : decode_any W_41b30 = Some (Op ALU_AND 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b34 : bv 32 := 0x00c57633.
Lemma F_41b34 : fetch_word Plain.M.loaded_segments (0x41b7c : word) = Some W_41b34.
Proof. vm_refl. Qed.
Lemma D_41b34 : decode_any W_41b34 = Some (Op ALU_AND 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b38 : bv 32 := 0x01851513.
Lemma F_41b38 : fetch_word Plain.M.loaded_segments (0x41b80 : word) = Some W_41b38.
Proof. vm_refl. Qed.
Lemma D_41b38 : decode_any W_41b38 = Some (ShiftImm ALU_SLL 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b3c : bv 32 := 0x00d5e5b3.
Lemma F_41b3c : fetch_word Plain.M.loaded_segments (0x41b84 : word) = Some W_41b3c.
Proof. vm_refl. Qed.
Lemma D_41b3c : decode_any W_41b3c = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b40 : bv 32 := 0x00810493.
Lemma F_41b40 : fetch_word Plain.M.loaded_segments (0x41b88 : word) = Some W_41b40.
Proof. vm_refl. Qed.
Lemma D_41b40 : decode_any W_41b40 = Some (OpImm ALU_ADD 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b44 : bv 32 := 0x00861613.
Lemma F_41b44 : fetch_word Plain.M.loaded_segments (0x41b8c : word) = Some W_41b44.
Proof. vm_refl. Qed.
Lemma D_41b44 : decode_any W_41b44 = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b48 : bv 32 := 0x00c56533.
Lemma F_41b48 : fetch_word Plain.M.loaded_segments (0x41b90 : word) = Some W_41b48.
Proof. vm_refl. Qed.
Lemma D_41b48 : decode_any W_41b48 = Some (Op ALU_OR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b4c : bv 32 := 0x00b56533.
Lemma F_41b4c : fetch_word Plain.M.loaded_segments (0x41b94 : word) = Some W_41b4c.
Proof. vm_refl. Qed.
Lemma D_41b4c : decode_any W_41b4c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b50 : bv 32 := 0x00a12423.
Lemma F_41b50 : fetch_word Plain.M.loaded_segments (0x41b98 : word) = Some W_41b50.
Proof. vm_refl. Qed.
Lemma D_41b50 : decode_any W_41b50 = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b54 : bv 32 := 0x00c10913.
Lemma F_41b54 : fetch_word Plain.M.loaded_segments (0x41b9c : word) = Some W_41b54.
Proof. vm_refl. Qed.
Lemma D_41b54 : decode_any W_41b54 = Some (OpImm ALU_ADD 18 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b58 : bv 32 := 0x0004c583.
Lemma F_41b58 : fetch_word Plain.M.loaded_segments (0x41ba0 : word) = Some W_41b58.
Proof. vm_refl. Qed.
Lemma D_41b58 : decode_any W_41b58 = Some (Load SZ1 false 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b5c : bv 32 := 0x00043503.
Lemma F_41b5c : fetch_word Plain.M.loaded_segments (0x41ba4 : word) = Some W_41b5c.
Proof. vm_refl. Qed.
Lemma D_41b5c : decode_any W_41b5c = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b60 : bv 32 := 0x00b107a3.
Lemma F_41b60 : fetch_word Plain.M.loaded_segments (0x41ba8 : word) = Some W_41b60.
Proof. vm_refl. Qed.
Lemma D_41b60 : decode_any W_41b60 = Some (Store SZ1 2 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b64 : bv 32 := 0x00f10593.
Lemma F_41b64 : fetch_word Plain.M.loaded_segments (0x41bac : word) = Some W_41b64.
Proof. vm_refl. Qed.
Lemma D_41b64 : decode_any W_41b64 = Some (OpImm ALU_ADD 11 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b68 : bv 32 := 0x154000ef.
Lemma F_41b68 : fetch_word Plain.M.loaded_segments (0x41bb0 : word) = Some W_41b68.
Proof. vm_refl. Qed.
Lemma D_41b68 : decode_any W_41b68 = Some (Jal 1 340, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b6c : bv 32 := 0x00148493.
Lemma F_41b6c : fetch_word Plain.M.loaded_segments (0x41bb4 : word) = Some W_41b6c.
Proof. vm_refl. Qed.
Lemma D_41b6c : decode_any W_41b6c = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b70 : bv 32 := 0xff2494e3.
Lemma F_41b70 : fetch_word Plain.M.loaded_segments (0x41bb8 : word) = Some W_41b70.
Proof. vm_refl. Qed.
Lemma D_41b70 : decode_any W_41b70 = Some (Branch BC_NE 9 18 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b74 : bv 32 := 0x02813083.
Lemma F_41b74 : fetch_word Plain.M.loaded_segments (0x41bbc : word) = Some W_41b74.
Proof. vm_refl. Qed.
Lemma D_41b74 : decode_any W_41b74 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b78 : bv 32 := 0x02013403.
Lemma F_41b78 : fetch_word Plain.M.loaded_segments (0x41bc0 : word) = Some W_41b78.
Proof. vm_refl. Qed.
Lemma D_41b78 : decode_any W_41b78 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b7c : bv 32 := 0x01813483.
Lemma F_41b7c : fetch_word Plain.M.loaded_segments (0x41bc4 : word) = Some W_41b7c.
Proof. vm_refl. Qed.
Lemma D_41b7c : decode_any W_41b7c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b80 : bv 32 := 0x01013903.
Lemma F_41b80 : fetch_word Plain.M.loaded_segments (0x41bc8 : word) = Some W_41b80.
Proof. vm_refl. Qed.
Lemma D_41b80 : decode_any W_41b80 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b84 : bv 32 := 0x03010113.
Lemma F_41b84 : fetch_word Plain.M.loaded_segments (0x41bcc : word) = Some W_41b84.
Proof. vm_refl. Qed.
Lemma D_41b84 : decode_any W_41b84 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b88 : bv 32 := 0x00008067.
Lemma F_41b88 : fetch_word Plain.M.loaded_segments (0x41bd0 : word) = Some W_41b88.
Proof. vm_refl. Qed.
Lemma D_41b88 : decode_any W_41b88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b8c : bv 32 := 0xff010113.
Lemma F_41b8c : fetch_word Plain.M.loaded_segments (0x41bd4 : word) = Some W_41b8c.
Proof. vm_refl. Qed.
Lemma D_41b8c : decode_any W_41b8c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b90 : bv 32 := 0x00113423.
Lemma F_41b90 : fetch_word Plain.M.loaded_segments (0x41bd8 : word) = Some W_41b90.
Proof. vm_refl. Qed.
Lemma D_41b90 : decode_any W_41b90 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b94 : bv 32 := 0x00813023.
Lemma F_41b94 : fetch_word Plain.M.loaded_segments (0x41bdc : word) = Some W_41b94.
Proof. vm_refl. Qed.
Lemma D_41b94 : decode_any W_41b94 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b98 : bv 32 := 0x00050413.
Lemma F_41b98 : fetch_word Plain.M.loaded_segments (0x41be0 : word) = Some W_41b98.
Proof. vm_refl. Qed.
Lemma D_41b98 : decode_any W_41b98 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41b9c : bv 32 := 0x159230ef.
Lemma F_41b9c : fetch_word Plain.M.loaded_segments (0x41be4 : word) = Some W_41b9c.
Proof. vm_refl. Qed.
Lemma D_41b9c : decode_any W_41b9c = Some (Jal 1 145752, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ba0 : bv 32 := 0x00800593.
Lemma F_41ba0 : fetch_word Plain.M.loaded_segments (0x41be8 : word) = Some W_41ba0.
Proof. vm_refl. Qed.
Lemma D_41ba0 : decode_any W_41ba0 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ba4 : bv 32 := 0x00040513.
Lemma F_41ba4 : fetch_word Plain.M.loaded_segments (0x41bec : word) = Some W_41ba4.
Proof. vm_refl. Qed.
Lemma D_41ba4 : decode_any W_41ba4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ba8 : bv 32 := 0x00813083.
Lemma F_41ba8 : fetch_word Plain.M.loaded_segments (0x41bf0 : word) = Some W_41ba8.
Proof. vm_refl. Qed.
Lemma D_41ba8 : decode_any W_41ba8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bac : bv 32 := 0x00013403.
Lemma F_41bac : fetch_word Plain.M.loaded_segments (0x41bf4 : word) = Some W_41bac.
Proof. vm_refl. Qed.
Lemma D_41bac : decode_any W_41bac = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bb0 : bv 32 := 0x01010113.
Lemma F_41bb0 : fetch_word Plain.M.loaded_segments (0x41bf8 : word) = Some W_41bb0.
Proof. vm_refl. Qed.
Lemma D_41bb0 : decode_any W_41bb0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bb4 : bv 32 := 0x1c82206f.
Lemma F_41bb4 : fetch_word Plain.M.loaded_segments (0x41bfc : word) = Some W_41bb4.
Proof. vm_refl. Qed.
Lemma D_41bb4 : decode_any W_41bb4 = Some (Jal 0 139720, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bb8 : bv 32 := 0xfffcf517.
Lemma F_41bb8 : fetch_word Plain.M.loaded_segments (0x41c00 : word) = Some W_41bb8.
Proof. vm_refl. Qed.
Lemma D_41bb8 : decode_any W_41bb8 = Some (Auipc 10 1048527, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bbc : bv 32 := 0xc4150513.
Lemma F_41bbc : fetch_word Plain.M.loaded_segments (0x41c04 : word) = Some W_41bbc.
Proof. vm_refl. Qed.
Lemma D_41bbc : decode_any W_41bbc = Some (OpImm ALU_ADD 10 10 3137, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bc0 : bv 32 := 0x00008067.
Lemma F_41bc0 : fetch_word Plain.M.loaded_segments (0x41c08 : word) = Some W_41bc0.
Proof. vm_refl. Qed.
Lemma D_41bc0 : decode_any W_41bc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bc4 : bv 32 := 0xfff6061b.
Lemma F_41bc4 : fetch_word Plain.M.loaded_segments (0x41c0c : word) = Some W_41bc4.
Proof. vm_refl. Qed.
Lemma D_41bc4 : decode_any W_41bc4 = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bc8 : bv 32 := 0x00a00593.
Lemma F_41bc8 : fetch_word Plain.M.loaded_segments (0x41c10 : word) = Some W_41bc8.
Proof. vm_refl. Qed.
Lemma D_41bc8 : decode_any W_41bc8 = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bcc : bv 32 := 0x02c5e063.
Lemma F_41bcc : fetch_word Plain.M.loaded_segments (0x41c14 : word) = Some W_41bcc.
Proof. vm_refl. Qed.
Lemma D_41bcc : decode_any W_41bcc = Some (Branch BC_LTU 11 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bd0 : bv 32 := 0x00261613.
Lemma F_41bd0 : fetch_word Plain.M.loaded_segments (0x41c18 : word) = Some W_41bd0.
Proof. vm_refl. Qed.
Lemma D_41bd0 : decode_any W_41bd0 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bd4 : bv 32 := 0xfffd4597.
Lemma F_41bd4 : fetch_word Plain.M.loaded_segments (0x41c1c : word) = Some W_41bd4.
Proof. vm_refl. Qed.
Lemma D_41bd4 : decode_any W_41bd4 = Some (Auipc 11 1048532, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bd8 : bv 32 := 0x31c58593.
Lemma F_41bd8 : fetch_word Plain.M.loaded_segments (0x41c20 : word) = Some W_41bd8.
Proof. vm_refl. Qed.
Lemma D_41bd8 : decode_any W_41bd8 = Some (OpImm ALU_ADD 11 11 796, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bdc : bv 32 := 0x00c58633.
Lemma F_41bdc : fetch_word Plain.M.loaded_segments (0x41c24 : word) = Some W_41bdc.
Proof. vm_refl. Qed.
Lemma D_41bdc : decode_any W_41bdc = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41be0 : bv 32 := 0x00062603.
Lemma F_41be0 : fetch_word Plain.M.loaded_segments (0x41c28 : word) = Some W_41be0.
Proof. vm_refl. Qed.
Lemma D_41be0 : decode_any W_41be0 = Some (Load SZ4 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41be4 : bv 32 := 0x00c585b3.
Lemma F_41be4 : fetch_word Plain.M.loaded_segments (0x41c2c : word) = Some W_41be4.
Proof. vm_refl. Qed.
Lemma D_41be4 : decode_any W_41be4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41be8 : bv 32 := 0x00c0006f.
Lemma F_41be8 : fetch_word Plain.M.loaded_segments (0x41c30 : word) = Some W_41be8.
Proof. vm_refl. Qed.
Lemma D_41be8 : decode_any W_41be8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bec : bv 32 := 0xfffcf597.
Lemma F_41bec : fetch_word Plain.M.loaded_segments (0x41c34 : word) = Some W_41bec.
Proof. vm_refl. Qed.
Lemma D_41bec : decode_any W_41bec = Some (Auipc 11 1048527, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bf0 : bv 32 := 0xc1e58593.
Lemma F_41bf0 : fetch_word Plain.M.loaded_segments (0x41c38 : word) = Some W_41bf0.
Proof. vm_refl. Qed.
Lemma D_41bf0 : decode_any W_41bf0 = Some (OpImm ALU_ADD 11 11 3102, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bf4 : bv 32 := 0xff010113.
Lemma F_41bf4 : fetch_word Plain.M.loaded_segments (0x41c3c : word) = Some W_41bf4.
Proof. vm_refl. Qed.
Lemma D_41bf4 : decode_any W_41bf4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bf8 : bv 32 := 0x00113423.
Lemma F_41bf8 : fetch_word Plain.M.loaded_segments (0x41c40 : word) = Some W_41bf8.
Proof. vm_refl. Qed.
Lemma D_41bf8 : decode_any W_41bf8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41bfc : bv 32 := 0xe4dfa0ef.
Lemma F_41bfc : fetch_word Plain.M.loaded_segments (0x41c44 : word) = Some W_41bfc.
Proof. vm_refl. Qed.
Lemma D_41bfc : decode_any W_41bfc = Some (Jal 1 2076236, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c00 : bv 32 := 0x00813083.
Lemma F_41c00 : fetch_word Plain.M.loaded_segments (0x41c48 : word) = Some W_41c00.
Proof. vm_refl. Qed.
Lemma D_41c00 : decode_any W_41c00 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c04 : bv 32 := 0x01010113.
Lemma F_41c04 : fetch_word Plain.M.loaded_segments (0x41c4c : word) = Some W_41c04.
Proof. vm_refl. Qed.
Lemma D_41c04 : decode_any W_41c04 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c08 : bv 32 := 0x00008067.
Lemma F_41c08 : fetch_word Plain.M.loaded_segments (0x41c50 : word) = Some W_41c08.
Proof. vm_refl. Qed.
Lemma D_41c08 : decode_any W_41c08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c0c : bv 32 := 0x00853603.
Lemma F_41c0c : fetch_word Plain.M.loaded_segments (0x41c54 : word) = Some W_41c0c.
Proof. vm_refl. Qed.
Lemma D_41c0c : decode_any W_41c0c = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c10 : bv 32 := 0x01053583.
Lemma F_41c10 : fetch_word Plain.M.loaded_segments (0x41c58 : word) = Some W_41c10.
Proof. vm_refl. Qed.
Lemma D_41c10 : decode_any W_41c10 = Some (Load SZ8 true 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c14 : bv 32 := 0x02b60a63.
Lemma F_41c14 : fetch_word Plain.M.loaded_segments (0x41c5c : word) = Some W_41c14.
Proof. vm_refl. Qed.
Lemma D_41c14 : decode_any W_41c14 = Some (Branch BC_EQ 12 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c18 : bv 32 := 0xfffd2697.
Lemma F_41c18 : fetch_word Plain.M.loaded_segments (0x41c60 : word) = Some W_41c18.
Proof. vm_refl. Qed.
Lemma D_41c18 : decode_any W_41c18 = Some (Auipc 13 1048530, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c1c : bv 32 := 0xbd06b683.
Lemma F_41c1c : fetch_word Plain.M.loaded_segments (0x41c64 : word) = Some W_41c1c.
Proof. vm_refl. Qed.
Lemma D_41c1c : decode_any W_41c1c = Some (Load SZ8 true 13 13 3024, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c20 : bv 32 := 0x40c58633.
Lemma F_41c20 : fetch_word Plain.M.loaded_segments (0x41c68 : word) = Some W_41c20.
Proof. vm_refl. Qed.
Lemma D_41c20 : decode_any W_41c20 = Some (Op ALU_SUB 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c24 : bv 32 := 0xfe860613.
Lemma F_41c24 : fetch_word Plain.M.loaded_segments (0x41c6c : word) = Some W_41c24.
Proof. vm_refl. Qed.
Lemma D_41c24 : decode_any W_41c24 = Some (OpImm ALU_ADD 12 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c28 : bv 32 := 0x02d63633.
Lemma F_41c28 : fetch_word Plain.M.loaded_segments (0x41c70 : word) = Some W_41c28.
Proof. vm_refl. Qed.
Lemma D_41c28 : decode_any W_41c28 = Some (Mul M_MULHU 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c2c : bv 32 := 0x00465613.
Lemma F_41c2c : fetch_word Plain.M.loaded_segments (0x41c74 : word) = Some W_41c2c.
Proof. vm_refl. Qed.
Lemma D_41c2c : decode_any W_41c2c = Some (ShiftImm ALU_SRL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c30 : bv 32 := 0x00561693.
Lemma F_41c30 : fetch_word Plain.M.loaded_segments (0x41c78 : word) = Some W_41c30.
Proof. vm_refl. Qed.
Lemma D_41c30 : decode_any W_41c30 = Some (ShiftImm ALU_SLL 13 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c34 : bv 32 := 0x00361613.
Lemma F_41c34 : fetch_word Plain.M.loaded_segments (0x41c7c : word) = Some W_41c34.
Proof. vm_refl. Qed.
Lemma D_41c34 : decode_any W_41c34 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c38 : bv 32 := 0x40d60633.
Lemma F_41c38 : fetch_word Plain.M.loaded_segments (0x41c80 : word) = Some W_41c38.
Proof. vm_refl. Qed.
Lemma D_41c38 : decode_any W_41c38 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c3c : bv 32 := 0x00c585b3.
Lemma F_41c3c : fetch_word Plain.M.loaded_segments (0x41c84 : word) = Some W_41c3c.
Proof. vm_refl. Qed.
Lemma D_41c3c : decode_any W_41c3c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c40 : bv 32 := 0xfe858593.
Lemma F_41c40 : fetch_word Plain.M.loaded_segments (0x41c88 : word) = Some W_41c40.
Proof. vm_refl. Qed.
Lemma D_41c40 : decode_any W_41c40 = Some (OpImm ALU_ADD 11 11 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c44 : bv 32 := 0x00b53823.
Lemma F_41c44 : fetch_word Plain.M.loaded_segments (0x41c8c : word) = Some W_41c44.
Proof. vm_refl. Qed.
Lemma D_41c44 : decode_any W_41c44 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c48 : bv 32 := 0x00053603.
Lemma F_41c48 : fetch_word Plain.M.loaded_segments (0x41c90 : word) = Some W_41c48.
Proof. vm_refl. Qed.
Lemma D_41c48 : decode_any W_41c48 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c4c : bv 32 := 0x00060a63.
Lemma F_41c4c : fetch_word Plain.M.loaded_segments (0x41c94 : word) = Some W_41c4c.
Proof. vm_refl. Qed.
Lemma D_41c4c : decode_any W_41c4c = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c50 : bv 32 := 0x01853583.
Lemma F_41c50 : fetch_word Plain.M.loaded_segments (0x41c98 : word) = Some W_41c50.
Proof. vm_refl. Qed.
Lemma D_41c50 : decode_any W_41c50 = Some (Load SZ8 true 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c54 : bv 32 := 0x40c585b3.
Lemma F_41c54 : fetch_word Plain.M.loaded_segments (0x41c9c : word) = Some W_41c54.
Proof. vm_refl. Qed.
Lemma D_41c54 : decode_any W_41c54 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c58 : bv 32 := 0x00060513.
Lemma F_41c58 : fetch_word Plain.M.loaded_segments (0x41ca0 : word) = Some W_41c58.
Proof. vm_refl. Qed.
Lemma D_41c58 : decode_any W_41c58 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c5c : bv 32 := 0x1202206f.
Lemma F_41c5c : fetch_word Plain.M.loaded_segments (0x41ca4 : word) = Some W_41c5c.
Proof. vm_refl. Qed.
Lemma D_41c5c : decode_any W_41c5c = Some (Jal 0 139552, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c60 : bv 32 := 0x00008067.
Lemma F_41c60 : fetch_word Plain.M.loaded_segments (0x41ca8 : word) = Some W_41c60.
Proof. vm_refl. Qed.
Lemma D_41c60 : decode_any W_41c60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c64 : bv 32 := 0xff010113.
Lemma F_41c64 : fetch_word Plain.M.loaded_segments (0x41cac : word) = Some W_41c64.
Proof. vm_refl. Qed.
Lemma D_41c64 : decode_any W_41c64 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c68 : bv 32 := 0x00113423.
Lemma F_41c68 : fetch_word Plain.M.loaded_segments (0x41cb0 : word) = Some W_41c68.
Proof. vm_refl. Qed.
Lemma D_41c68 : decode_any W_41c68 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c6c : bv 32 := 0xfffd1517.
Lemma F_41c6c : fetch_word Plain.M.loaded_segments (0x41cb4 : word) = Some W_41c6c.
Proof. vm_refl. Qed.
Lemma D_41c6c : decode_any W_41c6c = Some (Auipc 10 1048529, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c70 : bv 32 := 0xc2950513.
Lemma F_41c70 : fetch_word Plain.M.loaded_segments (0x41cb8 : word) = Some W_41c70.
Proof. vm_refl. Qed.
Lemma D_41c70 : decode_any W_41c70 = Some (OpImm ALU_ADD 10 10 3113, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c74 : bv 32 := 0xcd5fa0ef.
Lemma F_41c74 : fetch_word Plain.M.loaded_segments (0x41cbc : word) = Some W_41c74.
Proof. vm_refl. Qed.
Lemma D_41c74 : decode_any W_41c74 = Some (Jal 1 2075860, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c78 : bv 32 := 0xff010113.
Lemma F_41c78 : fetch_word Plain.M.loaded_segments (0x41cc0 : word) = Some W_41c78.
Proof. vm_refl. Qed.
Lemma D_41c78 : decode_any W_41c78 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c7c : bv 32 := 0x00113423.
Lemma F_41c7c : fetch_word Plain.M.loaded_segments (0x41cc4 : word) = Some W_41c7c.
Proof. vm_refl. Qed.
Lemma D_41c7c : decode_any W_41c7c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c80 : bv 32 := 0x00813023.
Lemma F_41c80 : fetch_word Plain.M.loaded_segments (0x41cc8 : word) = Some W_41c80.
Proof. vm_refl. Qed.
Lemma D_41c80 : decode_any W_41c80 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c84 : bv 32 := 0xfffd2517.
Lemma F_41c84 : fetch_word Plain.M.loaded_segments (0x41ccc : word) = Some W_41c84.
Proof. vm_refl. Qed.
Lemma D_41c84 : decode_any W_41c84 = Some (Auipc 10 1048530, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c88 : bv 32 := 0xb6c53503.
Lemma F_41c88 : fetch_word Plain.M.loaded_segments (0x41cd0 : word) = Some W_41c88.
Proof. vm_refl. Qed.
Lemma D_41c88 : decode_any W_41c88 = Some (Load SZ8 true 10 10 2924, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c8c : bv 32 := 0x02a5f663.
Lemma F_41c8c : fetch_word Plain.M.loaded_segments (0x41cd4 : word) = Some W_41c8c.
Proof. vm_refl. Qed.
Lemma D_41c8c : decode_any W_41c8c = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c90 : bv 32 := 0x00058413.
Lemma F_41c90 : fetch_word Plain.M.loaded_segments (0x41cd8 : word) = Some W_41c90.
Proof. vm_refl. Qed.
Lemma D_41c90 : decode_any W_41c90 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c94 : bv 32 := 0x00359513.
Lemma F_41c94 : fetch_word Plain.M.loaded_segments (0x41cdc : word) = Some W_41c94.
Proof. vm_refl. Qed.
Lemma D_41c94 : decode_any W_41c94 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c98 : bv 32 := 0x00559593.
Lemma F_41c98 : fetch_word Plain.M.loaded_segments (0x41ce0 : word) = Some W_41c98.
Proof. vm_refl. Qed.
Lemma D_41c98 : decode_any W_41c98 = Some (ShiftImm ALU_SLL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_41c9c : bv 32 := 0x40a58533.
Lemma F_41c9c : fetch_word Plain.M.loaded_segments (0x41ce4 : word) = Some W_41c9c.
Proof. vm_refl. Qed.
Lemma D_41c9c : decode_any W_41c9c = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ca0 : bv 32 := 0x3c97c0ef.
Lemma F_41ca0 : fetch_word Plain.M.loaded_segments (0x41ce8 : word) = Some W_41ca0.
Proof. vm_refl. Qed.
Lemma D_41ca0 : decode_any W_41ca0 = Some (Jal 1 510920, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ca4 : bv 32 := 0x00040593.
Lemma F_41ca4 : fetch_word Plain.M.loaded_segments (0x41cec : word) = Some W_41ca4.
Proof. vm_refl. Qed.
Lemma D_41ca4 : decode_any W_41ca4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ca8 : bv 32 := 0x00813083.
Lemma F_41ca8 : fetch_word Plain.M.loaded_segments (0x41cf0 : word) = Some W_41ca8.
Proof. vm_refl. Qed.
Lemma D_41ca8 : decode_any W_41ca8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cac : bv 32 := 0x00013403.
Lemma F_41cac : fetch_word Plain.M.loaded_segments (0x41cf4 : word) = Some W_41cac.
Proof. vm_refl. Qed.
Lemma D_41cac : decode_any W_41cac = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cb0 : bv 32 := 0x01010113.
Lemma F_41cb0 : fetch_word Plain.M.loaded_segments (0x41cf8 : word) = Some W_41cb0.
Proof. vm_refl. Qed.
Lemma D_41cb0 : decode_any W_41cb0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cb4 : bv 32 := 0x00008067.
Lemma F_41cb4 : fetch_word Plain.M.loaded_segments (0x41cfc : word) = Some W_41cb4.
Proof. vm_refl. Qed.
Lemma D_41cb4 : decode_any W_41cb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cb8 : bv 32 := 0xd5dfa0ef.
Lemma F_41cb8 : fetch_word Plain.M.loaded_segments (0x41d00 : word) = Some W_41cb8.
Proof. vm_refl. Qed.
Lemma D_41cb8 : decode_any W_41cb8 = Some (Jal 1 2075996, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cbc : bv 32 := 0xfc010113.
Lemma F_41cbc : fetch_word Plain.M.loaded_segments (0x41d04 : word) = Some W_41cbc.
Proof. vm_refl. Qed.
Lemma D_41cbc : decode_any W_41cbc = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cc0 : bv 32 := 0x02113c23.
Lemma F_41cc0 : fetch_word Plain.M.loaded_segments (0x41d08 : word) = Some W_41cc0.
Proof. vm_refl. Qed.
Lemma D_41cc0 : decode_any W_41cc0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cc4 : bv 32 := 0x02813823.
Lemma F_41cc4 : fetch_word Plain.M.loaded_segments (0x41d0c : word) = Some W_41cc4.
Proof. vm_refl. Qed.
Lemma D_41cc4 : decode_any W_41cc4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cc8 : bv 32 := 0x02913423.
Lemma F_41cc8 : fetch_word Plain.M.loaded_segments (0x41d10 : word) = Some W_41cc8.
Proof. vm_refl. Qed.
Lemma D_41cc8 : decode_any W_41cc8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ccc : bv 32 := 0x03213023.
Lemma F_41ccc : fetch_word Plain.M.loaded_segments (0x41d14 : word) = Some W_41ccc.
Proof. vm_refl. Qed.
Lemma D_41ccc : decode_any W_41ccc = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cd0 : bv 32 := 0x01313c23.
Lemma F_41cd0 : fetch_word Plain.M.loaded_segments (0x41d18 : word) = Some W_41cd0.
Proof. vm_refl. Qed.
Lemma D_41cd0 : decode_any W_41cd0 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cd4 : bv 32 := 0x01413823.
Lemma F_41cd4 : fetch_word Plain.M.loaded_segments (0x41d1c : word) = Some W_41cd4.
Proof. vm_refl. Qed.
Lemma D_41cd4 : decode_any W_41cd4 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cd8 : bv 32 := 0x01513423.
Lemma F_41cd8 : fetch_word Plain.M.loaded_segments (0x41d20 : word) = Some W_41cd8.
Proof. vm_refl. Qed.
Lemma D_41cd8 : decode_any W_41cd8 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cdc : bv 32 := 0x01613023.
Lemma F_41cdc : fetch_word Plain.M.loaded_segments (0x41d24 : word) = Some W_41cdc.
Proof. vm_refl. Qed.
Lemma D_41cdc : decode_any W_41cdc = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ce0 : bv 32 := 0x00050413.
Lemma F_41ce0 : fetch_word Plain.M.loaded_segments (0x41d28 : word) = Some W_41ce0.
Proof. vm_refl. Qed.
Lemma D_41ce0 : decode_any W_41ce0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ce4 : bv 32 := 0x00853603.
Lemma F_41ce4 : fetch_word Plain.M.loaded_segments (0x41d2c : word) = Some W_41ce4.
Proof. vm_refl. Qed.
Lemma D_41ce4 : decode_any W_41ce4 = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ce8 : bv 32 := 0x01053503.
Lemma F_41ce8 : fetch_word Plain.M.loaded_segments (0x41d30 : word) = Some W_41ce8.
Proof. vm_refl. Qed.
Lemma D_41ce8 : decode_any W_41ce8 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cec : bv 32 := 0x00058a13.
Lemma F_41cec : fetch_word Plain.M.loaded_segments (0x41d34 : word) = Some W_41cec.
Proof. vm_refl. Qed.
Lemma D_41cec : decode_any W_41cec = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cf0 : bv 32 := 0x00a67a63.
Lemma F_41cf0 : fetch_word Plain.M.loaded_segments (0x41d38 : word) = Some W_41cf0.
Proof. vm_refl. Qed.
Lemma D_41cf0 : decode_any W_41cf0 = Some (Branch BC_GEU 12 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cf4 : bv 32 := 0x000a4503.
Lemma F_41cf4 : fetch_word Plain.M.loaded_segments (0x41d3c : word) = Some W_41cf4.
Proof. vm_refl. Qed.
Lemma D_41cf4 : decode_any W_41cf4 = Some (Load SZ1 false 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cf8 : bv 32 := 0x00a60023.
Lemma F_41cf8 : fetch_word Plain.M.loaded_segments (0x41d40 : word) = Some W_41cf8.
Proof. vm_refl. Qed.
Lemma D_41cf8 : decode_any W_41cf8 = Some (Store SZ1 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41cfc : bv 32 := 0x00160a13.
Lemma F_41cfc : fetch_word Plain.M.loaded_segments (0x41d44 : word) = Some W_41cfc.
Proof. vm_refl. Qed.
Lemma D_41cfc : decode_any W_41cfc = Some (OpImm ALU_ADD 20 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d00 : bv 32 := 0x08c0006f.
Lemma F_41d00 : fetch_word Plain.M.loaded_segments (0x41d48 : word) = Some W_41d00.
Proof. vm_refl. Qed.
Lemma D_41d00 : decode_any W_41d00 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d04 : bv 32 := 0x00043483.
Lemma F_41d04 : fetch_word Plain.M.loaded_segments (0x41d4c : word) = Some W_41d04.
Proof. vm_refl. Qed.
Lemma D_41d04 : decode_any W_41d04 = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d08 : bv 32 := 0x409609b3.
Lemma F_41d08 : fetch_word Plain.M.loaded_segments (0x41d50 : word) = Some W_41d08.
Proof. vm_refl. Qed.
Lemma D_41d08 : decode_any W_41d08 = Some (Op ALU_SUB 19 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d0c : bv 32 := 0x00198593.
Lemma F_41d0c : fetch_word Plain.M.loaded_segments (0x41d54 : word) = Some W_41d0c.
Proof. vm_refl. Qed.
Lemma D_41d0c : decode_any W_41d0c = Some (OpImm ALU_ADD 11 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d10 : bv 32 := 0x0a05c463.
Lemma F_41d10 : fetch_word Plain.M.loaded_segments (0x41d58 : word) = Some W_41d10.
Proof. vm_refl. Qed.
Lemma D_41d10 : decode_any W_41d10 = Some (Branch BC_LT 11 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d14 : bv 32 := 0x40950933.
Lemma F_41d14 : fetch_word Plain.M.loaded_segments (0x41d5c : word) = Some W_41d14.
Proof. vm_refl. Qed.
Lemma D_41d14 : decode_any W_41d14 = Some (Op ALU_SUB 18 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d18 : bv 32 := 0x00191a93.
Lemma F_41d18 : fetch_word Plain.M.loaded_segments (0x41d60 : word) = Some W_41d18.
Proof. vm_refl. Qed.
Lemma D_41d18 : decode_any W_41d18 = Some (ShiftImm ALU_SLL 21 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d1c : bv 32 := 0x0155e463.
Lemma F_41d1c : fetch_word Plain.M.loaded_segments (0x41d64 : word) = Some W_41d1c.
Proof. vm_refl. Qed.
Lemma D_41d1c : decode_any W_41d1c = Some (Branch BC_LTU 11 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d20 : bv 32 := 0x00058a93.
Lemma F_41d20 : fetch_word Plain.M.loaded_segments (0x41d68 : word) = Some W_41d20.
Proof. vm_refl. Qed.
Lemma D_41d20 : decode_any W_41d20 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d24 : bv 32 := 0xfff00513.
Lemma F_41d24 : fetch_word Plain.M.loaded_segments (0x41d6c : word) = Some W_41d24.
Proof. vm_refl. Qed.
Lemma D_41d24 : decode_any W_41d24 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d28 : bv 32 := 0x00255593.
Lemma F_41d28 : fetch_word Plain.M.loaded_segments (0x41d70 : word) = Some W_41d28.
Proof. vm_refl. Qed.
Lemma D_41d28 : decode_any W_41d28 = Some (ShiftImm ALU_SRL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d2c : bv 32 := 0x00b96463.
Lemma F_41d2c : fetch_word Plain.M.loaded_segments (0x41d74 : word) = Some W_41d2c.
Proof. vm_refl. Qed.
Lemma D_41d2c : decode_any W_41d2c = Some (Branch BC_LTU 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d30 : bv 32 := 0x00155a93.
Lemma F_41d30 : fetch_word Plain.M.loaded_segments (0x41d78 : word) = Some W_41d30.
Proof. vm_refl. Qed.
Lemma D_41d30 : decode_any W_41d30 = Some (ShiftImm ALU_SRL 21 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d34 : bv 32 := 0x000a8a63.
Lemma F_41d34 : fetch_word Plain.M.loaded_segments (0x41d7c : word) = Some W_41d34.
Proof. vm_refl. Qed.
Lemma D_41d34 : decode_any W_41d34 = Some (Branch BC_EQ 21 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d38 : bv 32 := 0x000a8513.
Lemma F_41d38 : fetch_word Plain.M.loaded_segments (0x41d80 : word) = Some W_41d38.
Proof. vm_refl. Qed.
Lemma D_41d38 : decode_any W_41d38 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d3c : bv 32 := 0x32d7c0ef.
Lemma F_41d3c : fetch_word Plain.M.loaded_segments (0x41d84 : word) = Some W_41d3c.
Proof. vm_refl. Qed.
Lemma D_41d3c : decode_any W_41d3c = Some (Jal 1 510764, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d40 : bv 32 := 0x00050b13.
Lemma F_41d40 : fetch_word Plain.M.loaded_segments (0x41d88 : word) = Some W_41d40.
Proof. vm_refl. Qed.
Lemma D_41d40 : decode_any W_41d40 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d44 : bv 32 := 0x0080006f.
Lemma F_41d44 : fetch_word Plain.M.loaded_segments (0x41d8c : word) = Some W_41d44.
Proof. vm_refl. Qed.
Lemma D_41d44 : decode_any W_41d44 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d48 : bv 32 := 0x00000b13.
Lemma F_41d48 : fetch_word Plain.M.loaded_segments (0x41d90 : word) = Some W_41d48.
Proof. vm_refl. Qed.
Lemma D_41d48 : decode_any W_41d48 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d4c : bv 32 := 0x000a4503.
Lemma F_41d4c : fetch_word Plain.M.loaded_segments (0x41d94 : word) = Some W_41d4c.
Proof. vm_refl. Qed.
Lemma D_41d4c : decode_any W_41d4c = Some (Load SZ1 false 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d50 : bv 32 := 0x013b0a33.
Lemma F_41d50 : fetch_word Plain.M.loaded_segments (0x41d98 : word) = Some W_41d50.
Proof. vm_refl. Qed.
Lemma D_41d50 : decode_any W_41d50 = Some (Op ALU_ADD 20 22 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d54 : bv 32 := 0x015b0ab3.
Lemma F_41d54 : fetch_word Plain.M.loaded_segments (0x41d9c : word) = Some W_41d54.
Proof. vm_refl. Qed.
Lemma D_41d54 : decode_any W_41d54 = Some (Op ALU_ADD 21 22 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d58 : bv 32 := 0x00aa0023.
Lemma F_41d58 : fetch_word Plain.M.loaded_segments (0x41da0 : word) = Some W_41d58.
Proof. vm_refl. Qed.
Lemma D_41d58 : decode_any W_41d58 = Some (Store SZ1 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d5c : bv 32 := 0x001a0a13.
Lemma F_41d5c : fetch_word Plain.M.loaded_segments (0x41da4 : word) = Some W_41d5c.
Proof. vm_refl. Qed.
Lemma D_41d5c : decode_any W_41d5c = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d60 : bv 32 := 0x000b0513.
Lemma F_41d60 : fetch_word Plain.M.loaded_segments (0x41da8 : word) = Some W_41d60.
Proof. vm_refl. Qed.
Lemma D_41d60 : decode_any W_41d60 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d64 : bv 32 := 0x00048593.
Lemma F_41d64 : fetch_word Plain.M.loaded_segments (0x41dac : word) = Some W_41d64.
Proof. vm_refl. Qed.
Lemma D_41d64 : decode_any W_41d64 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d68 : bv 32 := 0x00098613.
Lemma F_41d68 : fetch_word Plain.M.loaded_segments (0x41db0 : word) = Some W_41d68.
Proof. vm_refl. Qed.
Lemma D_41d68 : decode_any W_41d68 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d6c : bv 32 := 0x3c5770ef.
Lemma F_41d6c : fetch_word Plain.M.loaded_segments (0x41db4 : word) = Some W_41d6c.
Proof. vm_refl. Qed.
Lemma D_41d6c : decode_any W_41d6c = Some (Jal 1 490436, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d70 : bv 32 := 0x01643023.
Lemma F_41d70 : fetch_word Plain.M.loaded_segments (0x41db8 : word) = Some W_41d70.
Proof. vm_refl. Qed.
Lemma D_41d70 : decode_any W_41d70 = Some (Store SZ8 8 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d74 : bv 32 := 0x01443423.
Lemma F_41d74 : fetch_word Plain.M.loaded_segments (0x41dbc : word) = Some W_41d74.
Proof. vm_refl. Qed.
Lemma D_41d74 : decode_any W_41d74 = Some (Store SZ8 8 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d78 : bv 32 := 0x01543823.
Lemma F_41d78 : fetch_word Plain.M.loaded_segments (0x41dc0 : word) = Some W_41d78.
Proof. vm_refl. Qed.
Lemma D_41d78 : decode_any W_41d78 = Some (Store SZ8 8 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d7c : bv 32 := 0x00048863.
Lemma F_41d7c : fetch_word Plain.M.loaded_segments (0x41dc4 : word) = Some W_41d7c.
Proof. vm_refl. Qed.
Lemma D_41d7c : decode_any W_41d7c = Some (Branch BC_EQ 9 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d80 : bv 32 := 0x00048513.
Lemma F_41d80 : fetch_word Plain.M.loaded_segments (0x41dc8 : word) = Some W_41d80.
Proof. vm_refl. Qed.
Lemma D_41d80 : decode_any W_41d80 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d84 : bv 32 := 0x00090593.
Lemma F_41d84 : fetch_word Plain.M.loaded_segments (0x41dcc : word) = Some W_41d84.
Proof. vm_refl. Qed.
Lemma D_41d84 : decode_any W_41d84 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d88 : bv 32 := 0x7f5210ef.
Lemma F_41d88 : fetch_word Plain.M.loaded_segments (0x41dd0 : word) = Some W_41d88.
Proof. vm_refl. Qed.
Lemma D_41d88 : decode_any W_41d88 = Some (Jal 1 139252, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d8c : bv 32 := 0x01443423.
Lemma F_41d8c : fetch_word Plain.M.loaded_segments (0x41dd4 : word) = Some W_41d8c.
Proof. vm_refl. Qed.
Lemma D_41d8c : decode_any W_41d8c = Some (Store SZ8 8 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d90 : bv 32 := 0x03813083.
Lemma F_41d90 : fetch_word Plain.M.loaded_segments (0x41dd8 : word) = Some W_41d90.
Proof. vm_refl. Qed.
Lemma D_41d90 : decode_any W_41d90 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d94 : bv 32 := 0x03013403.
Lemma F_41d94 : fetch_word Plain.M.loaded_segments (0x41ddc : word) = Some W_41d94.
Proof. vm_refl. Qed.
Lemma D_41d94 : decode_any W_41d94 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d98 : bv 32 := 0x02813483.
Lemma F_41d98 : fetch_word Plain.M.loaded_segments (0x41de0 : word) = Some W_41d98.
Proof. vm_refl. Qed.
Lemma D_41d98 : decode_any W_41d98 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41d9c : bv 32 := 0x02013903.
Lemma F_41d9c : fetch_word Plain.M.loaded_segments (0x41de4 : word) = Some W_41d9c.
Proof. vm_refl. Qed.
Lemma D_41d9c : decode_any W_41d9c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41da0 : bv 32 := 0x01813983.
Lemma F_41da0 : fetch_word Plain.M.loaded_segments (0x41de8 : word) = Some W_41da0.
Proof. vm_refl. Qed.
Lemma D_41da0 : decode_any W_41da0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41da4 : bv 32 := 0x01013a03.
Lemma F_41da4 : fetch_word Plain.M.loaded_segments (0x41dec : word) = Some W_41da4.
Proof. vm_refl. Qed.
Lemma D_41da4 : decode_any W_41da4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41da8 : bv 32 := 0x00813a83.
Lemma F_41da8 : fetch_word Plain.M.loaded_segments (0x41df0 : word) = Some W_41da8.
Proof. vm_refl. Qed.
Lemma D_41da8 : decode_any W_41da8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41dac : bv 32 := 0x00013b03.
Lemma F_41dac : fetch_word Plain.M.loaded_segments (0x41df4 : word) = Some W_41dac.
Proof. vm_refl. Qed.
Lemma D_41dac : decode_any W_41dac = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41db0 : bv 32 := 0x04010113.
Lemma F_41db0 : fetch_word Plain.M.loaded_segments (0x41df8 : word) = Some W_41db0.
Proof. vm_refl. Qed.
Lemma D_41db0 : decode_any W_41db0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_41db4 : bv 32 := 0x00008067.
Lemma F_41db4 : fetch_word Plain.M.loaded_segments (0x41dfc : word) = Some W_41db4.
Proof. vm_refl. Qed.
Lemma D_41db4 : decode_any W_41db4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41db8 : bv 32 := 0x004000ef.
Lemma F_41db8 : fetch_word Plain.M.loaded_segments (0x41e00 : word) = Some W_41db8.
Proof. vm_refl. Qed.
Lemma D_41db8 : decode_any W_41db8 = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_41dbc : bv 32 := 0xff010113.
Lemma F_41dbc : fetch_word Plain.M.loaded_segments (0x41e04 : word) = Some W_41dbc.
Proof. vm_refl. Qed.
Lemma D_41dbc : decode_any W_41dbc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_41dc0 : bv 32 := 0x00113423.
Lemma F_41dc0 : fetch_word Plain.M.loaded_segments (0x41e08 : word) = Some W_41dc0.
Proof. vm_refl. Qed.
Lemma D_41dc0 : decode_any W_41dc0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41dc4 : bv 32 := 0xfffd1517.
Lemma F_41dc4 : fetch_word Plain.M.loaded_segments (0x41e0c : word) = Some W_41dc4.
Proof. vm_refl. Qed.
Lemma D_41dc4 : decode_any W_41dc4 = Some (Auipc 10 1048529, 4%Z).
Proof. vm_refl. Qed.

Definition W_41dc8 : bv 32 := 0xad150513.
Lemma F_41dc8 : fetch_word Plain.M.loaded_segments (0x41e10 : word) = Some W_41dc8.
Proof. vm_refl. Qed.
Lemma D_41dc8 : decode_any W_41dc8 = Some (OpImm ALU_ADD 10 10 2769, 4%Z).
Proof. vm_refl. Qed.

Definition W_41dcc : bv 32 := 0xb7dfa0ef.
Lemma F_41dcc : fetch_word Plain.M.loaded_segments (0x41e14 : word) = Some W_41dcc.
Proof. vm_refl. Qed.
Lemma D_41dcc : decode_any W_41dcc = Some (Jal 1 2075516, 4%Z).
Proof. vm_refl. Qed.

Definition W_41dd0 : bv 32 := 0xfd010113.
Lemma F_41dd0 : fetch_word Plain.M.loaded_segments (0x41e18 : word) = Some W_41dd0.
Proof. vm_refl. Qed.
Lemma D_41dd0 : decode_any W_41dd0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_41dd4 : bv 32 := 0x02113423.
Lemma F_41dd4 : fetch_word Plain.M.loaded_segments (0x41e1c : word) = Some W_41dd4.
Proof. vm_refl. Qed.
Lemma D_41dd4 : decode_any W_41dd4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41dd8 : bv 32 := 0x02813023.
Lemma F_41dd8 : fetch_word Plain.M.loaded_segments (0x41e20 : word) = Some W_41dd8.
Proof. vm_refl. Qed.
Lemma D_41dd8 : decode_any W_41dd8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ddc : bv 32 := 0x00913c23.
Lemma F_41ddc : fetch_word Plain.M.loaded_segments (0x41e24 : word) = Some W_41ddc.
Proof. vm_refl. Qed.
Lemma D_41ddc : decode_any W_41ddc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41de0 : bv 32 := 0x01213823.
Lemma F_41de0 : fetch_word Plain.M.loaded_segments (0x41e28 : word) = Some W_41de0.
Proof. vm_refl. Qed.
Lemma D_41de0 : decode_any W_41de0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41de4 : bv 32 := 0x01313423.
Lemma F_41de4 : fetch_word Plain.M.loaded_segments (0x41e2c : word) = Some W_41de4.
Proof. vm_refl. Qed.
Lemma D_41de4 : decode_any W_41de4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41de8 : bv 32 := 0x00060493.
Lemma F_41de8 : fetch_word Plain.M.loaded_segments (0x41e30 : word) = Some W_41de8.
Proof. vm_refl. Qed.
Lemma D_41de8 : decode_any W_41de8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41dec : bv 32 := 0x00058413.
Lemma F_41dec : fetch_word Plain.M.loaded_segments (0x41e34 : word) = Some W_41dec.
Proof. vm_refl. Qed.
Lemma D_41dec : decode_any W_41dec = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41df0 : bv 32 := 0x0225d593.
Lemma F_41df0 : fetch_word Plain.M.loaded_segments (0x41e38 : word) = Some W_41df0.
Proof. vm_refl. Qed.
Lemma D_41df0 : decode_any W_41df0 = Some (ShiftImm ALU_SRL 11 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_41df4 : bv 32 := 0x00050913.
Lemma F_41df4 : fetch_word Plain.M.loaded_segments (0x41e3c : word) = Some W_41df4.
Proof. vm_refl. Qed.
Lemma D_41df4 : decode_any W_41df4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41df8 : bv 32 := 0x04059863.
Lemma F_41df8 : fetch_word Plain.M.loaded_segments (0x41e40 : word) = Some W_41df8.
Proof. vm_refl. Qed.
Lemma D_41df8 : decode_any W_41df8 = Some (Branch BC_NE 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_41dfc : bv 32 := 0x02249493.
Lemma F_41dfc : fetch_word Plain.M.loaded_segments (0x41e44 : word) = Some W_41dfc.
Proof. vm_refl. Qed.
Lemma D_41dfc : decode_any W_41dfc = Some (ShiftImm ALU_SLL 9 9 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e00 : bv 32 := 0x00893503.
Lemma F_41e00 : fetch_word Plain.M.loaded_segments (0x41e48 : word) = Some W_41e00.
Proof. vm_refl. Qed.
Lemma D_41e00 : decode_any W_41e00 = Some (Load SZ8 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e04 : bv 32 := 0x0084e9b3.
Lemma F_41e04 : fetch_word Plain.M.loaded_segments (0x41e4c : word) = Some W_41e04.
Proof. vm_refl. Qed.
Lemma D_41e04 : decode_any W_41e04 = Some (Op ALU_OR 19 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e08 : bv 32 := 0x0209d593.
Lemma F_41e08 : fetch_word Plain.M.loaded_segments (0x41e50 : word) = Some W_41e08.
Proof. vm_refl. Qed.
Lemma D_41e08 : decode_any W_41e08 = Some (ShiftImm ALU_SRL 11 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e0c : bv 32 := 0x00890493.
Lemma F_41e0c : fetch_word Plain.M.loaded_segments (0x41e54 : word) = Some W_41e0c.
Proof. vm_refl. Qed.
Lemma D_41e0c : decode_any W_41e0c = Some (OpImm ALU_ADD 9 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e10 : bv 32 := 0x08059863.
Lemma F_41e10 : fetch_word Plain.M.loaded_segments (0x41e58 : word) = Some W_41e10.
Proof. vm_refl. Qed.
Lemma D_41e10 : decode_any W_41e10 = Some (Branch BC_NE 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e14 : bv 32 := 0x0d600593.
Lemma F_41e14 : fetch_word Plain.M.loaded_segments (0x41e5c : word) = Some W_41e14.
Proof. vm_refl. Qed.
Lemma D_41e14 : decode_any W_41e14 = Some (OpImm ALU_ADD 11 0 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e18 : bv 32 := 0x00b100a3.
Lemma F_41e18 : fetch_word Plain.M.loaded_segments (0x41e60 : word) = Some W_41e18.
Proof. vm_refl. Qed.
Lemma D_41e18 : decode_any W_41e18 = Some (Store SZ1 2 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e1c : bv 32 := 0x00110593.
Lemma F_41e1c : fetch_word Plain.M.loaded_segments (0x41e64 : word) = Some W_41e1c.
Proof. vm_refl. Qed.
Lemma D_41e1c : decode_any W_41e1c = Some (OpImm ALU_ADD 11 2 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e20 : bv 32 := 0xe9dff0ef.
Lemma F_41e20 : fetch_word Plain.M.loaded_segments (0x41e68 : word) = Some W_41e20.
Proof. vm_refl. Qed.
Lemma D_41e20 : decode_any W_41e20 = Some (Jal 1 2096796, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e24 : bv 32 := 0x0004b503.
Lemma F_41e24 : fetch_word Plain.M.loaded_segments (0x41e6c : word) = Some W_41e24.
Proof. vm_refl. Qed.
Lemma D_41e24 : decode_any W_41e24 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e28 : bv 32 := 0xfff00593.
Lemma F_41e28 : fetch_word Plain.M.loaded_segments (0x41e70 : word) = Some W_41e28.
Proof. vm_refl. Qed.
Lemma D_41e28 : decode_any W_41e28 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e2c : bv 32 := 0x00b10123.
Lemma F_41e2c : fetch_word Plain.M.loaded_segments (0x41e74 : word) = Some W_41e2c.
Proof. vm_refl. Qed.
Lemma D_41e2c : decode_any W_41e2c = Some (Store SZ1 2 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e30 : bv 32 := 0x00210593.
Lemma F_41e30 : fetch_word Plain.M.loaded_segments (0x41e78 : word) = Some W_41e30.
Proof. vm_refl. Qed.
Lemma D_41e30 : decode_any W_41e30 = Some (OpImm ALU_ADD 11 2 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e34 : bv 32 := 0xe89ff0ef.
Lemma F_41e34 : fetch_word Plain.M.loaded_segments (0x41e7c : word) = Some W_41e34.
Proof. vm_refl. Qed.
Lemma D_41e34 : decode_any W_41e34 = Some (Jal 1 2096776, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e38 : bv 32 := 0x0004051b.
Lemma F_41e38 : fetch_word Plain.M.loaded_segments (0x41e80 : word) = Some W_41e38.
Proof. vm_refl. Qed.
Lemma D_41e38 : decode_any W_41e38 = Some (OpImm32 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e3c : bv 32 := 0x00048593.
Lemma F_41e3c : fetch_word Plain.M.loaded_segments (0x41e84 : word) = Some W_41e3c.
Proof. vm_refl. Qed.
Lemma D_41e3c : decode_any W_41e3c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e40 : bv 32 := 0xcc9ff0ef.
Lemma F_41e40 : fetch_word Plain.M.loaded_segments (0x41e88 : word) = Some W_41e40.
Proof. vm_refl. Qed.
Lemma D_41e40 : decode_any W_41e40 = Some (Jal 1 2096328, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e44 : bv 32 := 0x08c0006f.
Lemma F_41e44 : fetch_word Plain.M.loaded_segments (0x41e8c : word) = Some W_41e44.
Proof. vm_refl. Qed.
Lemma D_41e44 : decode_any W_41e44 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e48 : bv 32 := 0x00893503.
Lemma F_41e48 : fetch_word Plain.M.loaded_segments (0x41e90 : word) = Some W_41e48.
Proof. vm_refl. Qed.
Lemma D_41e48 : decode_any W_41e48 = Some (Load SZ8 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e4c : bv 32 := 0x00890993.
Lemma F_41e4c : fetch_word Plain.M.loaded_segments (0x41e94 : word) = Some W_41e4c.
Proof. vm_refl. Qed.
Lemma D_41e4c : decode_any W_41e4c = Some (OpImm ALU_ADD 19 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e50 : bv 32 := 0x0c700593.
Lemma F_41e50 : fetch_word Plain.M.loaded_segments (0x41e98 : word) = Some W_41e50.
Proof. vm_refl. Qed.
Lemma D_41e50 : decode_any W_41e50 = Some (OpImm ALU_ADD 11 0 199, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e54 : bv 32 := 0x00b102a3.
Lemma F_41e54 : fetch_word Plain.M.loaded_segments (0x41e9c : word) = Some W_41e54.
Proof. vm_refl. Qed.
Lemma D_41e54 : decode_any W_41e54 = Some (Store SZ1 2 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e58 : bv 32 := 0x00510593.
Lemma F_41e58 : fetch_word Plain.M.loaded_segments (0x41ea0 : word) = Some W_41e58.
Proof. vm_refl. Qed.
Lemma D_41e58 : decode_any W_41e58 = Some (OpImm ALU_ADD 11 2 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e5c : bv 32 := 0xe61ff0ef.
Lemma F_41e5c : fetch_word Plain.M.loaded_segments (0x41ea4 : word) = Some W_41e5c.
Proof. vm_refl. Qed.
Lemma D_41e5c : decode_any W_41e5c = Some (Jal 1 2096736, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e60 : bv 32 := 0x00893503.
Lemma F_41e60 : fetch_word Plain.M.loaded_segments (0x41ea8 : word) = Some W_41e60.
Proof. vm_refl. Qed.
Lemma D_41e60 : decode_any W_41e60 = Some (Load SZ8 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e64 : bv 32 := 0x00c00593.
Lemma F_41e64 : fetch_word Plain.M.loaded_segments (0x41eac : word) = Some W_41e64.
Proof. vm_refl. Qed.
Lemma D_41e64 : decode_any W_41e64 = Some (OpImm ALU_ADD 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e68 : bv 32 := 0x00b10323.
Lemma F_41e68 : fetch_word Plain.M.loaded_segments (0x41eb0 : word) = Some W_41e68.
Proof. vm_refl. Qed.
Lemma D_41e68 : decode_any W_41e68 = Some (Store SZ1 2 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e6c : bv 32 := 0x00610593.
Lemma F_41e6c : fetch_word Plain.M.loaded_segments (0x41eb4 : word) = Some W_41e6c.
Proof. vm_refl. Qed.
Lemma D_41e6c : decode_any W_41e6c = Some (OpImm ALU_ADD 11 2 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e70 : bv 32 := 0xe4dff0ef.
Lemma F_41e70 : fetch_word Plain.M.loaded_segments (0x41eb8 : word) = Some W_41e70.
Proof. vm_refl. Qed.
Lemma D_41e70 : decode_any W_41e70 = Some (Jal 1 2096716, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e74 : bv 32 := 0x00893503.
Lemma F_41e74 : fetch_word Plain.M.loaded_segments (0x41ebc : word) = Some W_41e74.
Proof. vm_refl. Qed.
Lemma D_41e74 : decode_any W_41e74 = Some (Load SZ8 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e78 : bv 32 := 0xfff00593.
Lemma F_41e78 : fetch_word Plain.M.loaded_segments (0x41ec0 : word) = Some W_41e78.
Proof. vm_refl. Qed.
Lemma D_41e78 : decode_any W_41e78 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e7c : bv 32 := 0x00b103a3.
Lemma F_41e7c : fetch_word Plain.M.loaded_segments (0x41ec4 : word) = Some W_41e7c.
Proof. vm_refl. Qed.
Lemma D_41e7c : decode_any W_41e7c = Some (Store SZ1 2 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e80 : bv 32 := 0x00710593.
Lemma F_41e80 : fetch_word Plain.M.loaded_segments (0x41ec8 : word) = Some W_41e80.
Proof. vm_refl. Qed.
Lemma D_41e80 : decode_any W_41e80 = Some (OpImm ALU_ADD 11 2 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e84 : bv 32 := 0xe39ff0ef.
Lemma F_41e84 : fetch_word Plain.M.loaded_segments (0x41ecc : word) = Some W_41e84.
Proof. vm_refl. Qed.
Lemma D_41e84 : decode_any W_41e84 = Some (Jal 1 2096696, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e88 : bv 32 := 0x0004851b.
Lemma F_41e88 : fetch_word Plain.M.loaded_segments (0x41ed0 : word) = Some W_41e88.
Proof. vm_refl. Qed.
Lemma D_41e88 : decode_any W_41e88 = Some (OpImm32 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e8c : bv 32 := 0x00098593.
Lemma F_41e8c : fetch_word Plain.M.loaded_segments (0x41ed4 : word) = Some W_41e8c.
Proof. vm_refl. Qed.
Lemma D_41e8c : decode_any W_41e8c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e90 : bv 32 := 0xc79ff0ef.
Lemma F_41e90 : fetch_word Plain.M.loaded_segments (0x41ed8 : word) = Some W_41e90.
Proof. vm_refl. Qed.
Lemma D_41e90 : decode_any W_41e90 = Some (Jal 1 2096248, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e94 : bv 32 := 0x00040513.
Lemma F_41e94 : fetch_word Plain.M.loaded_segments (0x41edc : word) = Some W_41e94.
Proof. vm_refl. Qed.
Lemma D_41e94 : decode_any W_41e94 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e98 : bv 32 := 0x00098593.
Lemma F_41e98 : fetch_word Plain.M.loaded_segments (0x41ee0 : word) = Some W_41e98.
Proof. vm_refl. Qed.
Lemma D_41e98 : decode_any W_41e98 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41e9c : bv 32 := 0x0300006f.
Lemma F_41e9c : fetch_word Plain.M.loaded_segments (0x41ee4 : word) = Some W_41e9c.
Proof. vm_refl. Qed.
Lemma D_41e9c : decode_any W_41e9c = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ea0 : bv 32 := 0x0d700593.
Lemma F_41ea0 : fetch_word Plain.M.loaded_segments (0x41ee8 : word) = Some W_41ea0.
Proof. vm_refl. Qed.
Lemma D_41ea0 : decode_any W_41ea0 = Some (OpImm ALU_ADD 11 0 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ea4 : bv 32 := 0x00b101a3.
Lemma F_41ea4 : fetch_word Plain.M.loaded_segments (0x41eec : word) = Some W_41ea4.
Proof. vm_refl. Qed.
Lemma D_41ea4 : decode_any W_41ea4 = Some (Store SZ1 2 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ea8 : bv 32 := 0x00310593.
Lemma F_41ea8 : fetch_word Plain.M.loaded_segments (0x41ef0 : word) = Some W_41ea8.
Proof. vm_refl. Qed.
Lemma D_41ea8 : decode_any W_41ea8 = Some (OpImm ALU_ADD 11 2 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_41eac : bv 32 := 0xe11ff0ef.
Lemma F_41eac : fetch_word Plain.M.loaded_segments (0x41ef4 : word) = Some W_41eac.
Proof. vm_refl. Qed.
Lemma D_41eac : decode_any W_41eac = Some (Jal 1 2096656, 4%Z).
Proof. vm_refl. Qed.

Definition W_41eb0 : bv 32 := 0x0004b503.
Lemma F_41eb0 : fetch_word Plain.M.loaded_segments (0x41ef8 : word) = Some W_41eb0.
Proof. vm_refl. Qed.
Lemma D_41eb0 : decode_any W_41eb0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41eb4 : bv 32 := 0xfff00593.
Lemma F_41eb4 : fetch_word Plain.M.loaded_segments (0x41efc : word) = Some W_41eb4.
Proof. vm_refl. Qed.
Lemma D_41eb4 : decode_any W_41eb4 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_41eb8 : bv 32 := 0x00b10223.
Lemma F_41eb8 : fetch_word Plain.M.loaded_segments (0x41f00 : word) = Some W_41eb8.
Proof. vm_refl. Qed.
Lemma D_41eb8 : decode_any W_41eb8 = Some (Store SZ1 2 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ebc : bv 32 := 0x00410593.
Lemma F_41ebc : fetch_word Plain.M.loaded_segments (0x41f04 : word) = Some W_41ebc.
Proof. vm_refl. Qed.
Lemma D_41ebc : decode_any W_41ebc = Some (OpImm ALU_ADD 11 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ec0 : bv 32 := 0xdfdff0ef.
Lemma F_41ec0 : fetch_word Plain.M.loaded_segments (0x41f08 : word) = Some W_41ec0.
Proof. vm_refl. Qed.
Lemma D_41ec0 : decode_any W_41ec0 = Some (Jal 1 2096636, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ec4 : bv 32 := 0x00098513.
Lemma F_41ec4 : fetch_word Plain.M.loaded_segments (0x41f0c : word) = Some W_41ec4.
Proof. vm_refl. Qed.
Lemma D_41ec4 : decode_any W_41ec4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ec8 : bv 32 := 0x00048593.
Lemma F_41ec8 : fetch_word Plain.M.loaded_segments (0x41f10 : word) = Some W_41ec8.
Proof. vm_refl. Qed.
Lemma D_41ec8 : decode_any W_41ec8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ecc : bv 32 := 0x020000ef.
Lemma F_41ecc : fetch_word Plain.M.loaded_segments (0x41f14 : word) = Some W_41ecc.
Proof. vm_refl. Qed.
Lemma D_41ecc : decode_any W_41ecc = Some (Jal 1 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ed0 : bv 32 := 0x02813083.
Lemma F_41ed0 : fetch_word Plain.M.loaded_segments (0x41f18 : word) = Some W_41ed0.
Proof. vm_refl. Qed.
Lemma D_41ed0 : decode_any W_41ed0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ed4 : bv 32 := 0x02013403.
Lemma F_41ed4 : fetch_word Plain.M.loaded_segments (0x41f1c : word) = Some W_41ed4.
Proof. vm_refl. Qed.
Lemma D_41ed4 : decode_any W_41ed4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ed8 : bv 32 := 0x01813483.
Lemma F_41ed8 : fetch_word Plain.M.loaded_segments (0x41f20 : word) = Some W_41ed8.
Proof. vm_refl. Qed.
Lemma D_41ed8 : decode_any W_41ed8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41edc : bv 32 := 0x01013903.
Lemma F_41edc : fetch_word Plain.M.loaded_segments (0x41f24 : word) = Some W_41edc.
Proof. vm_refl. Qed.
Lemma D_41edc : decode_any W_41edc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ee0 : bv 32 := 0x00813983.
Lemma F_41ee0 : fetch_word Plain.M.loaded_segments (0x41f28 : word) = Some W_41ee0.
Proof. vm_refl. Qed.
Lemma D_41ee0 : decode_any W_41ee0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ee4 : bv 32 := 0x03010113.
Lemma F_41ee4 : fetch_word Plain.M.loaded_segments (0x41f2c : word) = Some W_41ee4.
Proof. vm_refl. Qed.
Lemma D_41ee4 : decode_any W_41ee4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ee8 : bv 32 := 0x00008067.
Lemma F_41ee8 : fetch_word Plain.M.loaded_segments (0x41f30 : word) = Some W_41ee8.
Proof. vm_refl. Qed.
Lemma D_41ee8 : decode_any W_41ee8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41eec : bv 32 := 0xfd010113.
Lemma F_41eec : fetch_word Plain.M.loaded_segments (0x41f34 : word) = Some W_41eec.
Proof. vm_refl. Qed.
Lemma D_41eec : decode_any W_41eec = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ef0 : bv 32 := 0x02113423.
Lemma F_41ef0 : fetch_word Plain.M.loaded_segments (0x41f38 : word) = Some W_41ef0.
Proof. vm_refl. Qed.
Lemma D_41ef0 : decode_any W_41ef0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ef4 : bv 32 := 0x02813023.
Lemma F_41ef4 : fetch_word Plain.M.loaded_segments (0x41f3c : word) = Some W_41ef4.
Proof. vm_refl. Qed.
Lemma D_41ef4 : decode_any W_41ef4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ef8 : bv 32 := 0x00913c23.
Lemma F_41ef8 : fetch_word Plain.M.loaded_segments (0x41f40 : word) = Some W_41ef8.
Proof. vm_refl. Qed.
Lemma D_41ef8 : decode_any W_41ef8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41efc : bv 32 := 0x01213823.
Lemma F_41efc : fetch_word Plain.M.loaded_segments (0x41f44 : word) = Some W_41efc.
Proof. vm_refl. Qed.
Lemma D_41efc : decode_any W_41efc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f00 : bv 32 := 0x00058413.
Lemma F_41f00 : fetch_word Plain.M.loaded_segments (0x41f48 : word) = Some W_41f00.
Proof. vm_refl. Qed.
Lemma D_41f00 : decode_any W_41f00 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f04 : bv 32 := 0x02855593.
Lemma F_41f04 : fetch_word Plain.M.loaded_segments (0x41f4c : word) = Some W_41f04.
Proof. vm_refl. Qed.
Lemma D_41f04 : decode_any W_41f04 = Some (ShiftImm ALU_SRL 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f08 : bv 32 := 0x00010637.
Lemma F_41f08 : fetch_word Plain.M.loaded_segments (0x41f50 : word) = Some W_41f08.
Proof. vm_refl. Qed.
Lemma D_41f08 : decode_any W_41f08 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f0c : bv 32 := 0x03855693.
Lemma F_41f0c : fetch_word Plain.M.loaded_segments (0x41f54 : word) = Some W_41f0c.
Proof. vm_refl. Qed.
Lemma D_41f0c : decode_any W_41f0c = Some (ShiftImm ALU_SRL 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f10 : bv 32 := 0x01855713.
Lemma F_41f10 : fetch_word Plain.M.loaded_segments (0x41f58 : word) = Some W_41f10.
Proof. vm_refl. Qed.
Lemma D_41f10 : decode_any W_41f10 = Some (ShiftImm ALU_SRL 14 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f14 : bv 32 := 0x00ff07b7.
Lemma F_41f14 : fetch_word Plain.M.loaded_segments (0x41f5c : word) = Some W_41f14.
Proof. vm_refl. Qed.
Lemma D_41f14 : decode_any W_41f14 = Some (Lui 15 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f18 : bv 32 := 0xf006061b.
Lemma F_41f18 : fetch_word Plain.M.loaded_segments (0x41f60 : word) = Some W_41f18.
Proof. vm_refl. Qed.
Lemma D_41f18 : decode_any W_41f18 = Some (OpImm32 12 12 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f1c : bv 32 := 0x00c5f5b3.
Lemma F_41f1c : fetch_word Plain.M.loaded_segments (0x41f64 : word) = Some W_41f1c.
Proof. vm_refl. Qed.
Lemma D_41f1c : decode_any W_41f1c = Some (Op ALU_AND 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f20 : bv 32 := 0x00d5e5b3.
Lemma F_41f20 : fetch_word Plain.M.loaded_segments (0x41f68 : word) = Some W_41f20.
Proof. vm_refl. Qed.
Lemma D_41f20 : decode_any W_41f20 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f24 : bv 32 := 0x00855693.
Lemma F_41f24 : fetch_word Plain.M.loaded_segments (0x41f6c : word) = Some W_41f24.
Proof. vm_refl. Qed.
Lemma D_41f24 : decode_any W_41f24 = Some (ShiftImm ALU_SRL 13 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f28 : bv 32 := 0x00f77733.
Lemma F_41f28 : fetch_word Plain.M.loaded_segments (0x41f70 : word) = Some W_41f28.
Proof. vm_refl. Qed.
Lemma D_41f28 : decode_any W_41f28 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f2c : bv 32 := 0x0186d69b.
Lemma F_41f2c : fetch_word Plain.M.loaded_segments (0x41f74 : word) = Some W_41f2c.
Proof. vm_refl. Qed.
Lemma D_41f2c : decode_any W_41f2c = Some (ShiftImm32 ALU_SRL 13 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f30 : bv 32 := 0x01869693.
Lemma F_41f30 : fetch_word Plain.M.loaded_segments (0x41f78 : word) = Some W_41f30.
Proof. vm_refl. Qed.
Lemma D_41f30 : decode_any W_41f30 = Some (ShiftImm ALU_SLL 13 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f34 : bv 32 := 0x00e6e6b3.
Lemma F_41f34 : fetch_word Plain.M.loaded_segments (0x41f7c : word) = Some W_41f34.
Proof. vm_refl. Qed.
Lemma D_41f34 : decode_any W_41f34 = Some (Op ALU_OR 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f38 : bv 32 := 0x0185571b.
Lemma F_41f38 : fetch_word Plain.M.loaded_segments (0x41f80 : word) = Some W_41f38.
Proof. vm_refl. Qed.
Lemma D_41f38 : decode_any W_41f38 = Some (ShiftImm32 ALU_SRL 14 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f3c : bv 32 := 0x00f577b3.
Lemma F_41f3c : fetch_word Plain.M.loaded_segments (0x41f84 : word) = Some W_41f3c.
Proof. vm_refl. Qed.
Lemma D_41f3c : decode_any W_41f3c = Some (Op ALU_AND 15 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f40 : bv 32 := 0x00c57633.
Lemma F_41f40 : fetch_word Plain.M.loaded_segments (0x41f88 : word) = Some W_41f40.
Proof. vm_refl. Qed.
Lemma D_41f40 : decode_any W_41f40 = Some (Op ALU_AND 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f44 : bv 32 := 0x03851513.
Lemma F_41f44 : fetch_word Plain.M.loaded_segments (0x41f8c : word) = Some W_41f44.
Proof. vm_refl. Qed.
Lemma D_41f44 : decode_any W_41f44 = Some (ShiftImm ALU_SLL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f48 : bv 32 := 0x02071713.
Lemma F_41f48 : fetch_word Plain.M.loaded_segments (0x41f90 : word) = Some W_41f48.
Proof. vm_refl. Qed.
Lemma D_41f48 : decode_any W_41f48 = Some (ShiftImm ALU_SLL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f4c : bv 32 := 0x01879793.
Lemma F_41f4c : fetch_word Plain.M.loaded_segments (0x41f94 : word) = Some W_41f4c.
Proof. vm_refl. Qed.
Lemma D_41f4c : decode_any W_41f4c = Some (ShiftImm ALU_SLL 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f50 : bv 32 := 0x00e7e733.
Lemma F_41f50 : fetch_word Plain.M.loaded_segments (0x41f98 : word) = Some W_41f50.
Proof. vm_refl. Qed.
Lemma D_41f50 : decode_any W_41f50 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f54 : bv 32 := 0x00010493.
Lemma F_41f54 : fetch_word Plain.M.loaded_segments (0x41f9c : word) = Some W_41f54.
Proof. vm_refl. Qed.
Lemma D_41f54 : decode_any W_41f54 = Some (OpImm ALU_ADD 9 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f58 : bv 32 := 0x02861613.
Lemma F_41f58 : fetch_word Plain.M.loaded_segments (0x41fa0 : word) = Some W_41f58.
Proof. vm_refl. Qed.
Lemma D_41f58 : decode_any W_41f58 = Some (ShiftImm ALU_SLL 12 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f5c : bv 32 := 0x00b6e5b3.
Lemma F_41f5c : fetch_word Plain.M.loaded_segments (0x41fa4 : word) = Some W_41f5c.
Proof. vm_refl. Qed.
Lemma D_41f5c : decode_any W_41f5c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f60 : bv 32 := 0x00c56533.
Lemma F_41f60 : fetch_word Plain.M.loaded_segments (0x41fa8 : word) = Some W_41f60.
Proof. vm_refl. Qed.
Lemma D_41f60 : decode_any W_41f60 = Some (Op ALU_OR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f64 : bv 32 := 0x00e56533.
Lemma F_41f64 : fetch_word Plain.M.loaded_segments (0x41fac : word) = Some W_41f64.
Proof. vm_refl. Qed.
Lemma D_41f64 : decode_any W_41f64 = Some (Op ALU_OR 10 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f68 : bv 32 := 0x00b56533.
Lemma F_41f68 : fetch_word Plain.M.loaded_segments (0x41fb0 : word) = Some W_41f68.
Proof. vm_refl. Qed.
Lemma D_41f68 : decode_any W_41f68 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f6c : bv 32 := 0x00a13023.
Lemma F_41f6c : fetch_word Plain.M.loaded_segments (0x41fb4 : word) = Some W_41f6c.
Proof. vm_refl. Qed.
Lemma D_41f6c : decode_any W_41f6c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f70 : bv 32 := 0x00810913.
Lemma F_41f70 : fetch_word Plain.M.loaded_segments (0x41fb8 : word) = Some W_41f70.
Proof. vm_refl. Qed.
Lemma D_41f70 : decode_any W_41f70 = Some (OpImm ALU_ADD 18 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f74 : bv 32 := 0x0004c583.
Lemma F_41f74 : fetch_word Plain.M.loaded_segments (0x41fbc : word) = Some W_41f74.
Proof. vm_refl. Qed.
Lemma D_41f74 : decode_any W_41f74 = Some (Load SZ1 false 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f78 : bv 32 := 0x00043503.
Lemma F_41f78 : fetch_word Plain.M.loaded_segments (0x41fc0 : word) = Some W_41f78.
Proof. vm_refl. Qed.
Lemma D_41f78 : decode_any W_41f78 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f7c : bv 32 := 0x00b107a3.
Lemma F_41f7c : fetch_word Plain.M.loaded_segments (0x41fc4 : word) = Some W_41f7c.
Proof. vm_refl. Qed.
Lemma D_41f7c : decode_any W_41f7c = Some (Store SZ1 2 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f80 : bv 32 := 0x00f10593.
Lemma F_41f80 : fetch_word Plain.M.loaded_segments (0x41fc8 : word) = Some W_41f80.
Proof. vm_refl. Qed.
Lemma D_41f80 : decode_any W_41f80 = Some (OpImm ALU_ADD 11 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f84 : bv 32 := 0xd39ff0ef.
Lemma F_41f84 : fetch_word Plain.M.loaded_segments (0x41fcc : word) = Some W_41f84.
Proof. vm_refl. Qed.
Lemma D_41f84 : decode_any W_41f84 = Some (Jal 1 2096440, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f88 : bv 32 := 0x00148493.
Lemma F_41f88 : fetch_word Plain.M.loaded_segments (0x41fd0 : word) = Some W_41f88.
Proof. vm_refl. Qed.
Lemma D_41f88 : decode_any W_41f88 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f8c : bv 32 := 0xff2494e3.
Lemma F_41f8c : fetch_word Plain.M.loaded_segments (0x41fd4 : word) = Some W_41f8c.
Proof. vm_refl. Qed.
Lemma D_41f8c : decode_any W_41f8c = Some (Branch BC_NE 9 18 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f90 : bv 32 := 0x02813083.
Lemma F_41f90 : fetch_word Plain.M.loaded_segments (0x41fd8 : word) = Some W_41f90.
Proof. vm_refl. Qed.
Lemma D_41f90 : decode_any W_41f90 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f94 : bv 32 := 0x02013403.
Lemma F_41f94 : fetch_word Plain.M.loaded_segments (0x41fdc : word) = Some W_41f94.
Proof. vm_refl. Qed.
Lemma D_41f94 : decode_any W_41f94 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f98 : bv 32 := 0x01813483.
Lemma F_41f98 : fetch_word Plain.M.loaded_segments (0x41fe0 : word) = Some W_41f98.
Proof. vm_refl. Qed.
Lemma D_41f98 : decode_any W_41f98 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41f9c : bv 32 := 0x01013903.
Lemma F_41f9c : fetch_word Plain.M.loaded_segments (0x41fe4 : word) = Some W_41f9c.
Proof. vm_refl. Qed.
Lemma D_41f9c : decode_any W_41f9c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fa0 : bv 32 := 0x03010113.
Lemma F_41fa0 : fetch_word Plain.M.loaded_segments (0x41fe8 : word) = Some W_41fa0.
Proof. vm_refl. Qed.
Lemma D_41fa0 : decode_any W_41fa0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fa4 : bv 32 := 0x00008067.
Lemma F_41fa4 : fetch_word Plain.M.loaded_segments (0x41fec : word) = Some W_41fa4.
Proof. vm_refl. Qed.
Lemma D_41fa4 : decode_any W_41fa4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fa8 : bv 32 := 0xfd010113.
Lemma F_41fa8 : fetch_word Plain.M.loaded_segments (0x41ff0 : word) = Some W_41fa8.
Proof. vm_refl. Qed.
Lemma D_41fa8 : decode_any W_41fa8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fac : bv 32 := 0x02113423.
Lemma F_41fac : fetch_word Plain.M.loaded_segments (0x41ff4 : word) = Some W_41fac.
Proof. vm_refl. Qed.
Lemma D_41fac : decode_any W_41fac = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fb0 : bv 32 := 0x02813023.
Lemma F_41fb0 : fetch_word Plain.M.loaded_segments (0x41ff8 : word) = Some W_41fb0.
Proof. vm_refl. Qed.
Lemma D_41fb0 : decode_any W_41fb0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fb4 : bv 32 := 0x00913c23.
Lemma F_41fb4 : fetch_word Plain.M.loaded_segments (0x41ffc : word) = Some W_41fb4.
Proof. vm_refl. Qed.
Lemma D_41fb4 : decode_any W_41fb4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fb8 : bv 32 := 0x01213823.
Lemma F_41fb8 : fetch_word Plain.M.loaded_segments (0x42000 : word) = Some W_41fb8.
Proof. vm_refl. Qed.
Lemma D_41fb8 : decode_any W_41fb8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fbc : bv 32 := 0x00058413.
Lemma F_41fbc : fetch_word Plain.M.loaded_segments (0x42004 : word) = Some W_41fbc.
Proof. vm_refl. Qed.
Lemma D_41fbc : decode_any W_41fbc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fc0 : bv 32 := 0x00851593.
Lemma F_41fc0 : fetch_word Plain.M.loaded_segments (0x42008 : word) = Some W_41fc0.
Proof. vm_refl. Qed.
Lemma D_41fc0 : decode_any W_41fc0 = Some (ShiftImm ALU_SLL 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fc4 : bv 32 := 0x03051513.
Lemma F_41fc4 : fetch_word Plain.M.loaded_segments (0x4200c : word) = Some W_41fc4.
Proof. vm_refl. Qed.
Lemma D_41fc4 : decode_any W_41fc4 = Some (ShiftImm ALU_SLL 10 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fc8 : bv 32 := 0x03855513.
Lemma F_41fc8 : fetch_word Plain.M.loaded_segments (0x42010 : word) = Some W_41fc8.
Proof. vm_refl. Qed.
Lemma D_41fc8 : decode_any W_41fc8 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fcc : bv 32 := 0x00a5e533.
Lemma F_41fcc : fetch_word Plain.M.loaded_segments (0x42014 : word) = Some W_41fcc.
Proof. vm_refl. Qed.
Lemma D_41fcc : decode_any W_41fcc = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fd0 : bv 32 := 0x00c10493.
Lemma F_41fd0 : fetch_word Plain.M.loaded_segments (0x42018 : word) = Some W_41fd0.
Proof. vm_refl. Qed.
Lemma D_41fd0 : decode_any W_41fd0 = Some (OpImm ALU_ADD 9 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fd4 : bv 32 := 0x00a11623.
Lemma F_41fd4 : fetch_word Plain.M.loaded_segments (0x4201c : word) = Some W_41fd4.
Proof. vm_refl. Qed.
Lemma D_41fd4 : decode_any W_41fd4 = Some (Store SZ2 2 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fd8 : bv 32 := 0x00e10913.
Lemma F_41fd8 : fetch_word Plain.M.loaded_segments (0x42020 : word) = Some W_41fd8.
Proof. vm_refl. Qed.
Lemma D_41fd8 : decode_any W_41fd8 = Some (OpImm ALU_ADD 18 2 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fdc : bv 32 := 0x0004c583.
Lemma F_41fdc : fetch_word Plain.M.loaded_segments (0x42024 : word) = Some W_41fdc.
Proof. vm_refl. Qed.
Lemma D_41fdc : decode_any W_41fdc = Some (Load SZ1 false 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fe0 : bv 32 := 0x00043503.
Lemma F_41fe0 : fetch_word Plain.M.loaded_segments (0x42028 : word) = Some W_41fe0.
Proof. vm_refl. Qed.
Lemma D_41fe0 : decode_any W_41fe0 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fe4 : bv 32 := 0x00b107a3.
Lemma F_41fe4 : fetch_word Plain.M.loaded_segments (0x4202c : word) = Some W_41fe4.
Proof. vm_refl. Qed.
Lemma D_41fe4 : decode_any W_41fe4 = Some (Store SZ1 2 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fe8 : bv 32 := 0x00f10593.
Lemma F_41fe8 : fetch_word Plain.M.loaded_segments (0x42030 : word) = Some W_41fe8.
Proof. vm_refl. Qed.
Lemma D_41fe8 : decode_any W_41fe8 = Some (OpImm ALU_ADD 11 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_41fec : bv 32 := 0xcd1ff0ef.
Lemma F_41fec : fetch_word Plain.M.loaded_segments (0x42034 : word) = Some W_41fec.
Proof. vm_refl. Qed.
Lemma D_41fec : decode_any W_41fec = Some (Jal 1 2096336, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ff0 : bv 32 := 0x00148493.
Lemma F_41ff0 : fetch_word Plain.M.loaded_segments (0x42038 : word) = Some W_41ff0.
Proof. vm_refl. Qed.
Lemma D_41ff0 : decode_any W_41ff0 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ff4 : bv 32 := 0xff2494e3.
Lemma F_41ff4 : fetch_word Plain.M.loaded_segments (0x4203c : word) = Some W_41ff4.
Proof. vm_refl. Qed.
Lemma D_41ff4 : decode_any W_41ff4 = Some (Branch BC_NE 9 18 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ff8 : bv 32 := 0x02813083.
Lemma F_41ff8 : fetch_word Plain.M.loaded_segments (0x42040 : word) = Some W_41ff8.
Proof. vm_refl. Qed.
Lemma D_41ff8 : decode_any W_41ff8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_41ffc : bv 32 := 0x02013403.
Lemma F_41ffc : fetch_word Plain.M.loaded_segments (0x42044 : word) = Some W_41ffc.
Proof. vm_refl. Qed.
Lemma D_41ffc : decode_any W_41ffc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_42000 : bv 32 := 0x01813483.
Lemma F_42000 : fetch_word Plain.M.loaded_segments (0x42048 : word) = Some W_42000.
Proof. vm_refl. Qed.
Lemma D_42000 : decode_any W_42000 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42004 : bv 32 := 0x01013903.
Lemma F_42004 : fetch_word Plain.M.loaded_segments (0x4204c : word) = Some W_42004.
Proof. vm_refl. Qed.
Lemma D_42004 : decode_any W_42004 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42008 : bv 32 := 0x03010113.
Lemma F_42008 : fetch_word Plain.M.loaded_segments (0x42050 : word) = Some W_42008.
Proof. vm_refl. Qed.
Lemma D_42008 : decode_any W_42008 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4200c : bv 32 := 0x00008067.
Lemma F_4200c : fetch_word Plain.M.loaded_segments (0x42054 : word) = Some W_4200c.
Proof. vm_refl. Qed.
Lemma D_4200c : decode_any W_4200c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42010 : bv 32 := 0xfd010113.
Lemma F_42010 : fetch_word Plain.M.loaded_segments (0x42058 : word) = Some W_42010.
Proof. vm_refl. Qed.
Lemma D_42010 : decode_any W_42010 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_42014 : bv 32 := 0x02113423.
Lemma F_42014 : fetch_word Plain.M.loaded_segments (0x4205c : word) = Some W_42014.
Proof. vm_refl. Qed.
Lemma D_42014 : decode_any W_42014 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42018 : bv 32 := 0x02813023.
Lemma F_42018 : fetch_word Plain.M.loaded_segments (0x42060 : word) = Some W_42018.
Proof. vm_refl. Qed.
Lemma D_42018 : decode_any W_42018 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4201c : bv 32 := 0x00913c23.
Lemma F_4201c : fetch_word Plain.M.loaded_segments (0x42064 : word) = Some W_4201c.
Proof. vm_refl. Qed.
Lemma D_4201c : decode_any W_4201c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42020 : bv 32 := 0x01213823.
Lemma F_42020 : fetch_word Plain.M.loaded_segments (0x42068 : word) = Some W_42020.
Proof. vm_refl. Qed.
Lemma D_42020 : decode_any W_42020 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42024 : bv 32 := 0x00058413.
Lemma F_42024 : fetch_word Plain.M.loaded_segments (0x4206c : word) = Some W_42024.
Proof. vm_refl. Qed.
Lemma D_42024 : decode_any W_42024 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42028 : bv 32 := 0x00855593.
Lemma F_42028 : fetch_word Plain.M.loaded_segments (0x42070 : word) = Some W_42028.
Proof. vm_refl. Qed.
Lemma D_42028 : decode_any W_42028 = Some (ShiftImm ALU_SRL 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4202c : bv 32 := 0x00010637.
Lemma F_4202c : fetch_word Plain.M.loaded_segments (0x42074 : word) = Some W_4202c.
Proof. vm_refl. Qed.
Lemma D_4202c : decode_any W_4202c = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42030 : bv 32 := 0x0185569b.
Lemma F_42030 : fetch_word Plain.M.loaded_segments (0x42078 : word) = Some W_42030.
Proof. vm_refl. Qed.
Lemma D_42030 : decode_any W_42030 = Some (ShiftImm32 ALU_SRL 13 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42034 : bv 32 := 0xf0060613.
Lemma F_42034 : fetch_word Plain.M.loaded_segments (0x4207c : word) = Some W_42034.
Proof. vm_refl. Qed.
Lemma D_42034 : decode_any W_42034 = Some (OpImm ALU_ADD 12 12 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_42038 : bv 32 := 0x00c5f5b3.
Lemma F_42038 : fetch_word Plain.M.loaded_segments (0x42080 : word) = Some W_42038.
Proof. vm_refl. Qed.
Lemma D_42038 : decode_any W_42038 = Some (Op ALU_AND 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4203c : bv 32 := 0x00c57633.
Lemma F_4203c : fetch_word Plain.M.loaded_segments (0x42084 : word) = Some W_4203c.
Proof. vm_refl. Qed.
Lemma D_4203c : decode_any W_4203c = Some (Op ALU_AND 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_42040 : bv 32 := 0x01851513.
Lemma F_42040 : fetch_word Plain.M.loaded_segments (0x42088 : word) = Some W_42040.
Proof. vm_refl. Qed.
Lemma D_42040 : decode_any W_42040 = Some (ShiftImm ALU_SLL 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42044 : bv 32 := 0x00d5e5b3.
Lemma F_42044 : fetch_word Plain.M.loaded_segments (0x4208c : word) = Some W_42044.
Proof. vm_refl. Qed.
Lemma D_42044 : decode_any W_42044 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_42048 : bv 32 := 0x00810493.
Lemma F_42048 : fetch_word Plain.M.loaded_segments (0x42090 : word) = Some W_42048.
Proof. vm_refl. Qed.
Lemma D_42048 : decode_any W_42048 = Some (OpImm ALU_ADD 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4204c : bv 32 := 0x00861613.
Lemma F_4204c : fetch_word Plain.M.loaded_segments (0x42094 : word) = Some W_4204c.
Proof. vm_refl. Qed.
Lemma D_4204c : decode_any W_4204c = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42050 : bv 32 := 0x00c56533.
Lemma F_42050 : fetch_word Plain.M.loaded_segments (0x42098 : word) = Some W_42050.
Proof. vm_refl. Qed.
Lemma D_42050 : decode_any W_42050 = Some (Op ALU_OR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_42054 : bv 32 := 0x00b56533.
Lemma F_42054 : fetch_word Plain.M.loaded_segments (0x4209c : word) = Some W_42054.
Proof. vm_refl. Qed.
Lemma D_42054 : decode_any W_42054 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_42058 : bv 32 := 0x00a12423.
Lemma F_42058 : fetch_word Plain.M.loaded_segments (0x420a0 : word) = Some W_42058.
Proof. vm_refl. Qed.
Lemma D_42058 : decode_any W_42058 = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4205c : bv 32 := 0x00c10913.
Lemma F_4205c : fetch_word Plain.M.loaded_segments (0x420a4 : word) = Some W_4205c.
Proof. vm_refl. Qed.
Lemma D_4205c : decode_any W_4205c = Some (OpImm ALU_ADD 18 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_42060 : bv 32 := 0x0004c583.
Lemma F_42060 : fetch_word Plain.M.loaded_segments (0x420a8 : word) = Some W_42060.
Proof. vm_refl. Qed.
Lemma D_42060 : decode_any W_42060 = Some (Load SZ1 false 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42064 : bv 32 := 0x00043503.
Lemma F_42064 : fetch_word Plain.M.loaded_segments (0x420ac : word) = Some W_42064.
Proof. vm_refl. Qed.
Lemma D_42064 : decode_any W_42064 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42068 : bv 32 := 0x00b107a3.
Lemma F_42068 : fetch_word Plain.M.loaded_segments (0x420b0 : word) = Some W_42068.
Proof. vm_refl. Qed.
Lemma D_42068 : decode_any W_42068 = Some (Store SZ1 2 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_4206c : bv 32 := 0x00f10593.
Lemma F_4206c : fetch_word Plain.M.loaded_segments (0x420b4 : word) = Some W_4206c.
Proof. vm_refl. Qed.
Lemma D_4206c : decode_any W_4206c = Some (OpImm ALU_ADD 11 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_42070 : bv 32 := 0xc4dff0ef.
Lemma F_42070 : fetch_word Plain.M.loaded_segments (0x420b8 : word) = Some W_42070.
Proof. vm_refl. Qed.
Lemma D_42070 : decode_any W_42070 = Some (Jal 1 2096204, 4%Z).
Proof. vm_refl. Qed.

Definition W_42074 : bv 32 := 0x00148493.
Lemma F_42074 : fetch_word Plain.M.loaded_segments (0x420bc : word) = Some W_42074.
Proof. vm_refl. Qed.
Lemma D_42074 : decode_any W_42074 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_42078 : bv 32 := 0xff2494e3.
Lemma F_42078 : fetch_word Plain.M.loaded_segments (0x420c0 : word) = Some W_42078.
Proof. vm_refl. Qed.
Lemma D_42078 : decode_any W_42078 = Some (Branch BC_NE 9 18 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_4207c : bv 32 := 0x02813083.
Lemma F_4207c : fetch_word Plain.M.loaded_segments (0x420c4 : word) = Some W_4207c.
Proof. vm_refl. Qed.
Lemma D_4207c : decode_any W_4207c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42080 : bv 32 := 0x02013403.
Lemma F_42080 : fetch_word Plain.M.loaded_segments (0x420c8 : word) = Some W_42080.
Proof. vm_refl. Qed.
Lemma D_42080 : decode_any W_42080 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_42084 : bv 32 := 0x01813483.
Lemma F_42084 : fetch_word Plain.M.loaded_segments (0x420cc : word) = Some W_42084.
Proof. vm_refl. Qed.
Lemma D_42084 : decode_any W_42084 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42088 : bv 32 := 0x01013903.
Lemma F_42088 : fetch_word Plain.M.loaded_segments (0x420d0 : word) = Some W_42088.
Proof. vm_refl. Qed.
Lemma D_42088 : decode_any W_42088 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4208c : bv 32 := 0x03010113.
Lemma F_4208c : fetch_word Plain.M.loaded_segments (0x420d4 : word) = Some W_4208c.
Proof. vm_refl. Qed.
Lemma D_4208c : decode_any W_4208c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_42090 : bv 32 := 0x00008067.
Lemma F_42090 : fetch_word Plain.M.loaded_segments (0x420d8 : word) = Some W_42090.
Proof. vm_refl. Qed.
Lemma D_42090 : decode_any W_42090 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42094 : bv 32 := 0xfd010113.
Lemma F_42094 : fetch_word Plain.M.loaded_segments (0x420dc : word) = Some W_42094.
Proof. vm_refl. Qed.
Lemma D_42094 : decode_any W_42094 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_42098 : bv 32 := 0x02113423.
Lemma F_42098 : fetch_word Plain.M.loaded_segments (0x420e0 : word) = Some W_42098.
Proof. vm_refl. Qed.
Lemma D_42098 : decode_any W_42098 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4209c : bv 32 := 0x02813023.
Lemma F_4209c : fetch_word Plain.M.loaded_segments (0x420e4 : word) = Some W_4209c.
Proof. vm_refl. Qed.
Lemma D_4209c : decode_any W_4209c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_420a0 : bv 32 := 0x00913c23.
Lemma F_420a0 : fetch_word Plain.M.loaded_segments (0x420e8 : word) = Some W_420a0.
Proof. vm_refl. Qed.
Lemma D_420a0 : decode_any W_420a0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_420a4 : bv 32 := 0x01213823.
Lemma F_420a4 : fetch_word Plain.M.loaded_segments (0x420ec : word) = Some W_420a4.
Proof. vm_refl. Qed.
Lemma D_420a4 : decode_any W_420a4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_420a8 : bv 32 := 0x00058413.
Lemma F_420a8 : fetch_word Plain.M.loaded_segments (0x420f0 : word) = Some W_420a8.
Proof. vm_refl. Qed.
Lemma D_420a8 : decode_any W_420a8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_420ac : bv 32 := 0x02855593.
Lemma F_420ac : fetch_word Plain.M.loaded_segments (0x420f4 : word) = Some W_420ac.
Proof. vm_refl. Qed.
Lemma D_420ac : decode_any W_420ac = Some (ShiftImm ALU_SRL 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_420b0 : bv 32 := 0x00010637.
Lemma F_420b0 : fetch_word Plain.M.loaded_segments (0x420f8 : word) = Some W_420b0.
Proof. vm_refl. Qed.
Lemma D_420b0 : decode_any W_420b0 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_420b4 : bv 32 := 0x03855693.
Lemma F_420b4 : fetch_word Plain.M.loaded_segments (0x420fc : word) = Some W_420b4.
Proof. vm_refl. Qed.
Lemma D_420b4 : decode_any W_420b4 = Some (ShiftImm ALU_SRL 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_420b8 : bv 32 := 0x01855713.
Lemma F_420b8 : fetch_word Plain.M.loaded_segments (0x42100 : word) = Some W_420b8.
Proof. vm_refl. Qed.
Lemma D_420b8 : decode_any W_420b8 = Some (ShiftImm ALU_SRL 14 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_420bc : bv 32 := 0x00ff07b7.
Lemma F_420bc : fetch_word Plain.M.loaded_segments (0x42104 : word) = Some W_420bc.
Proof. vm_refl. Qed.
Lemma D_420bc : decode_any W_420bc = Some (Lui 15 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_420c0 : bv 32 := 0xf006061b.
Lemma F_420c0 : fetch_word Plain.M.loaded_segments (0x42108 : word) = Some W_420c0.
Proof. vm_refl. Qed.
Lemma D_420c0 : decode_any W_420c0 = Some (OpImm32 12 12 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_420c4 : bv 32 := 0x00c5f5b3.
Lemma F_420c4 : fetch_word Plain.M.loaded_segments (0x4210c : word) = Some W_420c4.
Proof. vm_refl. Qed.
Lemma D_420c4 : decode_any W_420c4 = Some (Op ALU_AND 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_420c8 : bv 32 := 0x00d5e5b3.
Lemma F_420c8 : fetch_word Plain.M.loaded_segments (0x42110 : word) = Some W_420c8.
Proof. vm_refl. Qed.
Lemma D_420c8 : decode_any W_420c8 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_420cc : bv 32 := 0x00855693.
Lemma F_420cc : fetch_word Plain.M.loaded_segments (0x42114 : word) = Some W_420cc.
Proof. vm_refl. Qed.
Lemma D_420cc : decode_any W_420cc = Some (ShiftImm ALU_SRL 13 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_420d0 : bv 32 := 0x00f77733.
Lemma F_420d0 : fetch_word Plain.M.loaded_segments (0x42118 : word) = Some W_420d0.
Proof. vm_refl. Qed.
Lemma D_420d0 : decode_any W_420d0 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_420d4 : bv 32 := 0x0186d69b.
Lemma F_420d4 : fetch_word Plain.M.loaded_segments (0x4211c : word) = Some W_420d4.
Proof. vm_refl. Qed.
Lemma D_420d4 : decode_any W_420d4 = Some (ShiftImm32 ALU_SRL 13 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_420d8 : bv 32 := 0x01869693.
Lemma F_420d8 : fetch_word Plain.M.loaded_segments (0x42120 : word) = Some W_420d8.
Proof. vm_refl. Qed.
Lemma D_420d8 : decode_any W_420d8 = Some (ShiftImm ALU_SLL 13 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_420dc : bv 32 := 0x00e6e6b3.
Lemma F_420dc : fetch_word Plain.M.loaded_segments (0x42124 : word) = Some W_420dc.
Proof. vm_refl. Qed.
Lemma D_420dc : decode_any W_420dc = Some (Op ALU_OR 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_420e0 : bv 32 := 0x0185571b.
Lemma F_420e0 : fetch_word Plain.M.loaded_segments (0x42128 : word) = Some W_420e0.
Proof. vm_refl. Qed.
Lemma D_420e0 : decode_any W_420e0 = Some (ShiftImm32 ALU_SRL 14 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_420e4 : bv 32 := 0x00f577b3.
Lemma F_420e4 : fetch_word Plain.M.loaded_segments (0x4212c : word) = Some W_420e4.
Proof. vm_refl. Qed.
Lemma D_420e4 : decode_any W_420e4 = Some (Op ALU_AND 15 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_420e8 : bv 32 := 0x00c57633.
Lemma F_420e8 : fetch_word Plain.M.loaded_segments (0x42130 : word) = Some W_420e8.
Proof. vm_refl. Qed.
Lemma D_420e8 : decode_any W_420e8 = Some (Op ALU_AND 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_420ec : bv 32 := 0x03851513.
Lemma F_420ec : fetch_word Plain.M.loaded_segments (0x42134 : word) = Some W_420ec.
Proof. vm_refl. Qed.
Lemma D_420ec : decode_any W_420ec = Some (ShiftImm ALU_SLL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_420f0 : bv 32 := 0x02071713.
Lemma F_420f0 : fetch_word Plain.M.loaded_segments (0x42138 : word) = Some W_420f0.
Proof. vm_refl. Qed.
Lemma D_420f0 : decode_any W_420f0 = Some (ShiftImm ALU_SLL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_420f4 : bv 32 := 0x01879793.
Lemma F_420f4 : fetch_word Plain.M.loaded_segments (0x4213c : word) = Some W_420f4.
Proof. vm_refl. Qed.
Lemma D_420f4 : decode_any W_420f4 = Some (ShiftImm ALU_SLL 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_420f8 : bv 32 := 0x00e7e733.
Lemma F_420f8 : fetch_word Plain.M.loaded_segments (0x42140 : word) = Some W_420f8.
Proof. vm_refl. Qed.
Lemma D_420f8 : decode_any W_420f8 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_420fc : bv 32 := 0x00010493.
Lemma F_420fc : fetch_word Plain.M.loaded_segments (0x42144 : word) = Some W_420fc.
Proof. vm_refl. Qed.
Lemma D_420fc : decode_any W_420fc = Some (OpImm ALU_ADD 9 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42100 : bv 32 := 0x02861613.
Lemma F_42100 : fetch_word Plain.M.loaded_segments (0x42148 : word) = Some W_42100.
Proof. vm_refl. Qed.
Lemma D_42100 : decode_any W_42100 = Some (ShiftImm ALU_SLL 12 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42104 : bv 32 := 0x00b6e5b3.
Lemma F_42104 : fetch_word Plain.M.loaded_segments (0x4214c : word) = Some W_42104.
Proof. vm_refl. Qed.
Lemma D_42104 : decode_any W_42104 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_42108 : bv 32 := 0x00c56533.
Lemma F_42108 : fetch_word Plain.M.loaded_segments (0x42150 : word) = Some W_42108.
Proof. vm_refl. Qed.
Lemma D_42108 : decode_any W_42108 = Some (Op ALU_OR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4210c : bv 32 := 0x00e56533.
Lemma F_4210c : fetch_word Plain.M.loaded_segments (0x42154 : word) = Some W_4210c.
Proof. vm_refl. Qed.
Lemma D_4210c : decode_any W_4210c = Some (Op ALU_OR 10 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_42110 : bv 32 := 0x00b56533.
Lemma F_42110 : fetch_word Plain.M.loaded_segments (0x42158 : word) = Some W_42110.
Proof. vm_refl. Qed.
Lemma D_42110 : decode_any W_42110 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_42114 : bv 32 := 0x00a13023.
Lemma F_42114 : fetch_word Plain.M.loaded_segments (0x4215c : word) = Some W_42114.
Proof. vm_refl. Qed.
Lemma D_42114 : decode_any W_42114 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42118 : bv 32 := 0x00810913.
Lemma F_42118 : fetch_word Plain.M.loaded_segments (0x42160 : word) = Some W_42118.
Proof. vm_refl. Qed.
Lemma D_42118 : decode_any W_42118 = Some (OpImm ALU_ADD 18 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4211c : bv 32 := 0x0004c583.
Lemma F_4211c : fetch_word Plain.M.loaded_segments (0x42164 : word) = Some W_4211c.
Proof. vm_refl. Qed.
Lemma D_4211c : decode_any W_4211c = Some (Load SZ1 false 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42120 : bv 32 := 0x00043503.
Lemma F_42120 : fetch_word Plain.M.loaded_segments (0x42168 : word) = Some W_42120.
Proof. vm_refl. Qed.
Lemma D_42120 : decode_any W_42120 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42124 : bv 32 := 0x00b107a3.
Lemma F_42124 : fetch_word Plain.M.loaded_segments (0x4216c : word) = Some W_42124.
Proof. vm_refl. Qed.
Lemma D_42124 : decode_any W_42124 = Some (Store SZ1 2 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_42128 : bv 32 := 0x00f10593.
Lemma F_42128 : fetch_word Plain.M.loaded_segments (0x42170 : word) = Some W_42128.
Proof. vm_refl. Qed.
Lemma D_42128 : decode_any W_42128 = Some (OpImm ALU_ADD 11 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_4212c : bv 32 := 0xb91ff0ef.
Lemma F_4212c : fetch_word Plain.M.loaded_segments (0x42174 : word) = Some W_4212c.
Proof. vm_refl. Qed.
Lemma D_4212c : decode_any W_4212c = Some (Jal 1 2096016, 4%Z).
Proof. vm_refl. Qed.

Definition W_42130 : bv 32 := 0x00148493.
Lemma F_42130 : fetch_word Plain.M.loaded_segments (0x42178 : word) = Some W_42130.
Proof. vm_refl. Qed.
Lemma D_42130 : decode_any W_42130 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_42134 : bv 32 := 0xff2494e3.
Lemma F_42134 : fetch_word Plain.M.loaded_segments (0x4217c : word) = Some W_42134.
Proof. vm_refl. Qed.
Lemma D_42134 : decode_any W_42134 = Some (Branch BC_NE 9 18 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_42138 : bv 32 := 0x02813083.
Lemma F_42138 : fetch_word Plain.M.loaded_segments (0x42180 : word) = Some W_42138.
Proof. vm_refl. Qed.
Lemma D_42138 : decode_any W_42138 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4213c : bv 32 := 0x02013403.
Lemma F_4213c : fetch_word Plain.M.loaded_segments (0x42184 : word) = Some W_4213c.
Proof. vm_refl. Qed.
Lemma D_4213c : decode_any W_4213c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_42140 : bv 32 := 0x01813483.
Lemma F_42140 : fetch_word Plain.M.loaded_segments (0x42188 : word) = Some W_42140.
Proof. vm_refl. Qed.
Lemma D_42140 : decode_any W_42140 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42144 : bv 32 := 0x01013903.
Lemma F_42144 : fetch_word Plain.M.loaded_segments (0x4218c : word) = Some W_42144.
Proof. vm_refl. Qed.
Lemma D_42144 : decode_any W_42144 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42148 : bv 32 := 0x03010113.
Lemma F_42148 : fetch_word Plain.M.loaded_segments (0x42190 : word) = Some W_42148.
Proof. vm_refl. Qed.
Lemma D_42148 : decode_any W_42148 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4214c : bv 32 := 0x00008067.
Lemma F_4214c : fetch_word Plain.M.loaded_segments (0x42194 : word) = Some W_4214c.
Proof. vm_refl. Qed.
Lemma D_4214c : decode_any W_4214c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42150 : bv 32 := 0xfd010113.
Lemma F_42150 : fetch_word Plain.M.loaded_segments (0x42198 : word) = Some W_42150.
Proof. vm_refl. Qed.
Lemma D_42150 : decode_any W_42150 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_42154 : bv 32 := 0x02113423.
Lemma F_42154 : fetch_word Plain.M.loaded_segments (0x4219c : word) = Some W_42154.
Proof. vm_refl. Qed.
Lemma D_42154 : decode_any W_42154 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42158 : bv 32 := 0x02813023.
Lemma F_42158 : fetch_word Plain.M.loaded_segments (0x421a0 : word) = Some W_42158.
Proof. vm_refl. Qed.
Lemma D_42158 : decode_any W_42158 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4215c : bv 32 := 0x00913c23.
Lemma F_4215c : fetch_word Plain.M.loaded_segments (0x421a4 : word) = Some W_4215c.
Proof. vm_refl. Qed.
Lemma D_4215c : decode_any W_4215c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42160 : bv 32 := 0x01213823.
Lemma F_42160 : fetch_word Plain.M.loaded_segments (0x421a8 : word) = Some W_42160.
Proof. vm_refl. Qed.
Lemma D_42160 : decode_any W_42160 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42164 : bv 32 := 0x00050413.
Lemma F_42164 : fetch_word Plain.M.loaded_segments (0x421ac : word) = Some W_42164.
Proof. vm_refl. Qed.
Lemma D_42164 : decode_any W_42164 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42168 : bv 32 := 0xe0050553.
Lemma F_42168 : fetch_word Plain.M.loaded_segments (0x421b0 : word) = Some W_42168.
Proof. vm_refl. Qed.
Lemma D_42168 : decode_any W_42168 = Some (Fmv FMV_X_F FMT_S 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4216c : bv 32 := 0x000105b7.
Lemma F_4216c : fetch_word Plain.M.loaded_segments (0x421b4 : word) = Some W_4216c.
Proof. vm_refl. Qed.
Lemma D_4216c : decode_any W_4216c = Some (Lui 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42170 : bv 32 := 0x00855613.
Lemma F_42170 : fetch_word Plain.M.loaded_segments (0x421b8 : word) = Some W_42170.
Proof. vm_refl. Qed.
Lemma D_42170 : decode_any W_42170 = Some (ShiftImm ALU_SRL 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42174 : bv 32 := 0xf0058593.
Lemma F_42174 : fetch_word Plain.M.loaded_segments (0x421bc : word) = Some W_42174.
Proof. vm_refl. Qed.
Lemma D_42174 : decode_any W_42174 = Some (OpImm ALU_ADD 11 11 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_42178 : bv 32 := 0x0185569b.
Lemma F_42178 : fetch_word Plain.M.loaded_segments (0x421c0 : word) = Some W_42178.
Proof. vm_refl. Qed.
Lemma D_42178 : decode_any W_42178 = Some (ShiftImm32 ALU_SRL 13 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4217c : bv 32 := 0x00b67633.
Lemma F_4217c : fetch_word Plain.M.loaded_segments (0x421c4 : word) = Some W_4217c.
Proof. vm_refl. Qed.
Lemma D_4217c : decode_any W_4217c = Some (Op ALU_AND 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_42180 : bv 32 := 0x00d66633.
Lemma F_42180 : fetch_word Plain.M.loaded_segments (0x421c8 : word) = Some W_42180.
Proof. vm_refl. Qed.
Lemma D_42180 : decode_any W_42180 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_42184 : bv 32 := 0x00810493.
Lemma F_42184 : fetch_word Plain.M.loaded_segments (0x421cc : word) = Some W_42184.
Proof. vm_refl. Qed.
Lemma D_42184 : decode_any W_42184 = Some (OpImm ALU_ADD 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42188 : bv 32 := 0x00b575b3.
Lemma F_42188 : fetch_word Plain.M.loaded_segments (0x421d0 : word) = Some W_42188.
Proof. vm_refl. Qed.
Lemma D_42188 : decode_any W_42188 = Some (Op ALU_AND 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4218c : bv 32 := 0x01851513.
Lemma F_4218c : fetch_word Plain.M.loaded_segments (0x421d4 : word) = Some W_4218c.
Proof. vm_refl. Qed.
Lemma D_4218c : decode_any W_4218c = Some (ShiftImm ALU_SLL 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42190 : bv 32 := 0x00859593.
Lemma F_42190 : fetch_word Plain.M.loaded_segments (0x421d8 : word) = Some W_42190.
Proof. vm_refl. Qed.
Lemma D_42190 : decode_any W_42190 = Some (ShiftImm ALU_SLL 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42194 : bv 32 := 0x00b56533.
Lemma F_42194 : fetch_word Plain.M.loaded_segments (0x421dc : word) = Some W_42194.
Proof. vm_refl. Qed.
Lemma D_42194 : decode_any W_42194 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_42198 : bv 32 := 0x00c56533.
Lemma F_42198 : fetch_word Plain.M.loaded_segments (0x421e0 : word) = Some W_42198.
Proof. vm_refl. Qed.
Lemma D_42198 : decode_any W_42198 = Some (Op ALU_OR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4219c : bv 32 := 0x00a12423.
Lemma F_4219c : fetch_word Plain.M.loaded_segments (0x421e4 : word) = Some W_4219c.
Proof. vm_refl. Qed.
Lemma D_4219c : decode_any W_4219c = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_421a0 : bv 32 := 0x00c10913.
Lemma F_421a0 : fetch_word Plain.M.loaded_segments (0x421e8 : word) = Some W_421a0.
Proof. vm_refl. Qed.
Lemma D_421a0 : decode_any W_421a0 = Some (OpImm ALU_ADD 18 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_421a4 : bv 32 := 0x0004c583.
Lemma F_421a4 : fetch_word Plain.M.loaded_segments (0x421ec : word) = Some W_421a4.
Proof. vm_refl. Qed.
Lemma D_421a4 : decode_any W_421a4 = Some (Load SZ1 false 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_421a8 : bv 32 := 0x00043503.
Lemma F_421a8 : fetch_word Plain.M.loaded_segments (0x421f0 : word) = Some W_421a8.
Proof. vm_refl. Qed.
Lemma D_421a8 : decode_any W_421a8 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_421ac : bv 32 := 0x00b107a3.
Lemma F_421ac : fetch_word Plain.M.loaded_segments (0x421f4 : word) = Some W_421ac.
Proof. vm_refl. Qed.
Lemma D_421ac : decode_any W_421ac = Some (Store SZ1 2 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_421b0 : bv 32 := 0x00f10593.
Lemma F_421b0 : fetch_word Plain.M.loaded_segments (0x421f8 : word) = Some W_421b0.
Proof. vm_refl. Qed.
Lemma D_421b0 : decode_any W_421b0 = Some (OpImm ALU_ADD 11 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_421b4 : bv 32 := 0xb09ff0ef.
Lemma F_421b4 : fetch_word Plain.M.loaded_segments (0x421fc : word) = Some W_421b4.
Proof. vm_refl. Qed.
Lemma D_421b4 : decode_any W_421b4 = Some (Jal 1 2095880, 4%Z).
Proof. vm_refl. Qed.

Definition W_421b8 : bv 32 := 0x00148493.
Lemma F_421b8 : fetch_word Plain.M.loaded_segments (0x42200 : word) = Some W_421b8.
Proof. vm_refl. Qed.
Lemma D_421b8 : decode_any W_421b8 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_421bc : bv 32 := 0xff2494e3.
Lemma F_421bc : fetch_word Plain.M.loaded_segments (0x42204 : word) = Some W_421bc.
Proof. vm_refl. Qed.
Lemma D_421bc : decode_any W_421bc = Some (Branch BC_NE 9 18 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_421c0 : bv 32 := 0x02813083.
Lemma F_421c0 : fetch_word Plain.M.loaded_segments (0x42208 : word) = Some W_421c0.
Proof. vm_refl. Qed.
Lemma D_421c0 : decode_any W_421c0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_421c4 : bv 32 := 0x02013403.
Lemma F_421c4 : fetch_word Plain.M.loaded_segments (0x4220c : word) = Some W_421c4.
Proof. vm_refl. Qed.
Lemma D_421c4 : decode_any W_421c4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_421c8 : bv 32 := 0x01813483.
Lemma F_421c8 : fetch_word Plain.M.loaded_segments (0x42210 : word) = Some W_421c8.
Proof. vm_refl. Qed.
Lemma D_421c8 : decode_any W_421c8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_421cc : bv 32 := 0x01013903.
Lemma F_421cc : fetch_word Plain.M.loaded_segments (0x42214 : word) = Some W_421cc.
Proof. vm_refl. Qed.
Lemma D_421cc : decode_any W_421cc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_421d0 : bv 32 := 0x03010113.
Lemma F_421d0 : fetch_word Plain.M.loaded_segments (0x42218 : word) = Some W_421d0.
Proof. vm_refl. Qed.
Lemma D_421d0 : decode_any W_421d0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_421d4 : bv 32 := 0x00008067.
Lemma F_421d4 : fetch_word Plain.M.loaded_segments (0x4221c : word) = Some W_421d4.
Proof. vm_refl. Qed.
Lemma D_421d4 : decode_any W_421d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_421d8 : bv 32 := 0xfd010113.
Lemma F_421d8 : fetch_word Plain.M.loaded_segments (0x42220 : word) = Some W_421d8.
Proof. vm_refl. Qed.
Lemma D_421d8 : decode_any W_421d8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_421dc : bv 32 := 0x02113423.
Lemma F_421dc : fetch_word Plain.M.loaded_segments (0x42224 : word) = Some W_421dc.
Proof. vm_refl. Qed.
Lemma D_421dc : decode_any W_421dc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_421e0 : bv 32 := 0x02813023.
Lemma F_421e0 : fetch_word Plain.M.loaded_segments (0x42228 : word) = Some W_421e0.
Proof. vm_refl. Qed.
Lemma D_421e0 : decode_any W_421e0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_421e4 : bv 32 := 0x00913c23.
Lemma F_421e4 : fetch_word Plain.M.loaded_segments (0x4222c : word) = Some W_421e4.
Proof. vm_refl. Qed.
Lemma D_421e4 : decode_any W_421e4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_421e8 : bv 32 := 0x01213823.
Lemma F_421e8 : fetch_word Plain.M.loaded_segments (0x42230 : word) = Some W_421e8.
Proof. vm_refl. Qed.
Lemma D_421e8 : decode_any W_421e8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_421ec : bv 32 := 0x00050413.
Lemma F_421ec : fetch_word Plain.M.loaded_segments (0x42234 : word) = Some W_421ec.
Proof. vm_refl. Qed.
Lemma D_421ec : decode_any W_421ec = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_421f0 : bv 32 := 0xe2050553.
Lemma F_421f0 : fetch_word Plain.M.loaded_segments (0x42238 : word) = Some W_421f0.
Proof. vm_refl. Qed.
Lemma D_421f0 : decode_any W_421f0 = Some (Fmv FMV_X_F FMT_D 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_421f4 : bv 32 := 0x00ff05b7.
Lemma F_421f4 : fetch_word Plain.M.loaded_segments (0x4223c : word) = Some W_421f4.
Proof. vm_refl. Qed.
Lemma D_421f4 : decode_any W_421f4 = Some (Lui 11 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_421f8 : bv 32 := 0x00010637.
Lemma F_421f8 : fetch_word Plain.M.loaded_segments (0x42240 : word) = Some W_421f8.
Proof. vm_refl. Qed.
Lemma D_421f8 : decode_any W_421f8 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_421fc : bv 32 := 0x00b576b3.
Lemma F_421fc : fetch_word Plain.M.loaded_segments (0x42244 : word) = Some W_421fc.
Proof. vm_refl. Qed.
Lemma D_421fc : decode_any W_421fc = Some (Op ALU_AND 13 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_42200 : bv 32 := 0x0185571b.
Lemma F_42200 : fetch_word Plain.M.loaded_segments (0x42248 : word) = Some W_42200.
Proof. vm_refl. Qed.
Lemma D_42200 : decode_any W_42200 = Some (ShiftImm32 ALU_SRL 14 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42204 : bv 32 := 0xf006061b.
Lemma F_42204 : fetch_word Plain.M.loaded_segments (0x4224c : word) = Some W_42204.
Proof. vm_refl. Qed.
Lemma D_42204 : decode_any W_42204 = Some (OpImm32 12 12 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_42208 : bv 32 := 0x01855793.
Lemma F_42208 : fetch_word Plain.M.loaded_segments (0x42250 : word) = Some W_42208.
Proof. vm_refl. Qed.
Lemma D_42208 : decode_any W_42208 = Some (ShiftImm ALU_SRL 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4220c : bv 32 := 0x00b7f5b3.
Lemma F_4220c : fetch_word Plain.M.loaded_segments (0x42254 : word) = Some W_4220c.
Proof. vm_refl. Qed.
Lemma D_4220c : decode_any W_4220c = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_42210 : bv 32 := 0x02855793.
Lemma F_42210 : fetch_word Plain.M.loaded_segments (0x42258 : word) = Some W_42210.
Proof. vm_refl. Qed.
Lemma D_42210 : decode_any W_42210 = Some (ShiftImm ALU_SRL 15 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42214 : bv 32 := 0x01869693.
Lemma F_42214 : fetch_word Plain.M.loaded_segments (0x4225c : word) = Some W_42214.
Proof. vm_refl. Qed.
Lemma D_42214 : decode_any W_42214 = Some (ShiftImm ALU_SLL 13 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42218 : bv 32 := 0x02071713.
Lemma F_42218 : fetch_word Plain.M.loaded_segments (0x42260 : word) = Some W_42218.
Proof. vm_refl. Qed.
Lemma D_42218 : decode_any W_42218 = Some (ShiftImm ALU_SLL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4221c : bv 32 := 0x00e6e6b3.
Lemma F_4221c : fetch_word Plain.M.loaded_segments (0x42264 : word) = Some W_4221c.
Proof. vm_refl. Qed.
Lemma D_4221c : decode_any W_4221c = Some (Op ALU_OR 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_42220 : bv 32 := 0x03855713.
Lemma F_42220 : fetch_word Plain.M.loaded_segments (0x42268 : word) = Some W_42220.
Proof. vm_refl. Qed.
Lemma D_42220 : decode_any W_42220 = Some (ShiftImm ALU_SRL 14 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_42224 : bv 32 := 0x00c7f7b3.
Lemma F_42224 : fetch_word Plain.M.loaded_segments (0x4226c : word) = Some W_42224.
Proof. vm_refl. Qed.
Lemma D_42224 : decode_any W_42224 = Some (Op ALU_AND 15 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_42228 : bv 32 := 0x00e7e733.
Lemma F_42228 : fetch_word Plain.M.loaded_segments (0x42270 : word) = Some W_42228.
Proof. vm_refl. Qed.
Lemma D_42228 : decode_any W_42228 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4222c : bv 32 := 0x03851793.
Lemma F_4222c : fetch_word Plain.M.loaded_segments (0x42274 : word) = Some W_4222c.
Proof. vm_refl. Qed.
Lemma D_4222c : decode_any W_4222c = Some (ShiftImm ALU_SLL 15 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_42230 : bv 32 := 0x00c57633.
Lemma F_42230 : fetch_word Plain.M.loaded_segments (0x42278 : word) = Some W_42230.
Proof. vm_refl. Qed.
Lemma D_42230 : decode_any W_42230 = Some (Op ALU_AND 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_42234 : bv 32 := 0x02861613.
Lemma F_42234 : fetch_word Plain.M.loaded_segments (0x4227c : word) = Some W_42234.
Proof. vm_refl. Qed.
Lemma D_42234 : decode_any W_42234 = Some (ShiftImm ALU_SLL 12 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42238 : bv 32 := 0x00c7e633.
Lemma F_42238 : fetch_word Plain.M.loaded_segments (0x42280 : word) = Some W_42238.
Proof. vm_refl. Qed.
Lemma D_42238 : decode_any W_42238 = Some (Op ALU_OR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4223c : bv 32 := 0x00010493.
Lemma F_4223c : fetch_word Plain.M.loaded_segments (0x42284 : word) = Some W_4223c.
Proof. vm_refl. Qed.
Lemma D_4223c : decode_any W_4223c = Some (OpImm ALU_ADD 9 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42240 : bv 32 := 0x00855513.
Lemma F_42240 : fetch_word Plain.M.loaded_segments (0x42288 : word) = Some W_42240.
Proof. vm_refl. Qed.
Lemma D_42240 : decode_any W_42240 = Some (ShiftImm ALU_SRL 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42244 : bv 32 := 0x0185551b.
Lemma F_42244 : fetch_word Plain.M.loaded_segments (0x4228c : word) = Some W_42244.
Proof. vm_refl. Qed.
Lemma D_42244 : decode_any W_42244 = Some (ShiftImm32 ALU_SRL 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42248 : bv 32 := 0x01851513.
Lemma F_42248 : fetch_word Plain.M.loaded_segments (0x42290 : word) = Some W_42248.
Proof. vm_refl. Qed.
Lemma D_42248 : decode_any W_42248 = Some (ShiftImm ALU_SLL 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4224c : bv 32 := 0x00b56533.
Lemma F_4224c : fetch_word Plain.M.loaded_segments (0x42294 : word) = Some W_4224c.
Proof. vm_refl. Qed.
Lemma D_4224c : decode_any W_4224c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_42250 : bv 32 := 0x00d66633.
Lemma F_42250 : fetch_word Plain.M.loaded_segments (0x42298 : word) = Some W_42250.
Proof. vm_refl. Qed.
Lemma D_42250 : decode_any W_42250 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_42254 : bv 32 := 0x00e56533.
Lemma F_42254 : fetch_word Plain.M.loaded_segments (0x4229c : word) = Some W_42254.
Proof. vm_refl. Qed.
Lemma D_42254 : decode_any W_42254 = Some (Op ALU_OR 10 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_42258 : bv 32 := 0x00a66533.
Lemma F_42258 : fetch_word Plain.M.loaded_segments (0x422a0 : word) = Some W_42258.
Proof. vm_refl. Qed.
Lemma D_42258 : decode_any W_42258 = Some (Op ALU_OR 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4225c : bv 32 := 0x00a13023.
Lemma F_4225c : fetch_word Plain.M.loaded_segments (0x422a4 : word) = Some W_4225c.
Proof. vm_refl. Qed.
Lemma D_4225c : decode_any W_4225c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42260 : bv 32 := 0x00810913.
Lemma F_42260 : fetch_word Plain.M.loaded_segments (0x422a8 : word) = Some W_42260.
Proof. vm_refl. Qed.
Lemma D_42260 : decode_any W_42260 = Some (OpImm ALU_ADD 18 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42264 : bv 32 := 0x0004c583.
Lemma F_42264 : fetch_word Plain.M.loaded_segments (0x422ac : word) = Some W_42264.
Proof. vm_refl. Qed.
Lemma D_42264 : decode_any W_42264 = Some (Load SZ1 false 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42268 : bv 32 := 0x00043503.
Lemma F_42268 : fetch_word Plain.M.loaded_segments (0x422b0 : word) = Some W_42268.
Proof. vm_refl. Qed.
Lemma D_42268 : decode_any W_42268 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4226c : bv 32 := 0x00b107a3.
Lemma F_4226c : fetch_word Plain.M.loaded_segments (0x422b4 : word) = Some W_4226c.
Proof. vm_refl. Qed.
Lemma D_4226c : decode_any W_4226c = Some (Store SZ1 2 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_42270 : bv 32 := 0x00f10593.
Lemma F_42270 : fetch_word Plain.M.loaded_segments (0x422b8 : word) = Some W_42270.
Proof. vm_refl. Qed.
Lemma D_42270 : decode_any W_42270 = Some (OpImm ALU_ADD 11 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_42274 : bv 32 := 0xa49ff0ef.
Lemma F_42274 : fetch_word Plain.M.loaded_segments (0x422bc : word) = Some W_42274.
Proof. vm_refl. Qed.
Lemma D_42274 : decode_any W_42274 = Some (Jal 1 2095688, 4%Z).
Proof. vm_refl. Qed.

Definition W_42278 : bv 32 := 0x00148493.
Lemma F_42278 : fetch_word Plain.M.loaded_segments (0x422c0 : word) = Some W_42278.
Proof. vm_refl. Qed.
Lemma D_42278 : decode_any W_42278 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4227c : bv 32 := 0xff2494e3.
Lemma F_4227c : fetch_word Plain.M.loaded_segments (0x422c4 : word) = Some W_4227c.
Proof. vm_refl. Qed.
Lemma D_4227c : decode_any W_4227c = Some (Branch BC_NE 9 18 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_42280 : bv 32 := 0x02813083.
Lemma F_42280 : fetch_word Plain.M.loaded_segments (0x422c8 : word) = Some W_42280.
Proof. vm_refl. Qed.
Lemma D_42280 : decode_any W_42280 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42284 : bv 32 := 0x02013403.
Lemma F_42284 : fetch_word Plain.M.loaded_segments (0x422cc : word) = Some W_42284.
Proof. vm_refl. Qed.
Lemma D_42284 : decode_any W_42284 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_42288 : bv 32 := 0x01813483.
Lemma F_42288 : fetch_word Plain.M.loaded_segments (0x422d0 : word) = Some W_42288.
Proof. vm_refl. Qed.
Lemma D_42288 : decode_any W_42288 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4228c : bv 32 := 0x01013903.
Lemma F_4228c : fetch_word Plain.M.loaded_segments (0x422d4 : word) = Some W_4228c.
Proof. vm_refl. Qed.
Lemma D_4228c : decode_any W_4228c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42290 : bv 32 := 0x03010113.
Lemma F_42290 : fetch_word Plain.M.loaded_segments (0x422d8 : word) = Some W_42290.
Proof. vm_refl. Qed.
Lemma D_42290 : decode_any W_42290 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_42294 : bv 32 := 0x00008067.
Lemma F_42294 : fetch_word Plain.M.loaded_segments (0x422dc : word) = Some W_42294.
Proof. vm_refl. Qed.
Lemma D_42294 : decode_any W_42294 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42298 : bv 32 := 0x00063023.
Lemma F_42298 : fetch_word Plain.M.loaded_segments (0x422e0 : word) = Some W_42298.
Proof. vm_refl. Qed.
Lemma D_42298 : decode_any W_42298 = Some (Store SZ8 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4229c : bv 32 := 0x06058463.
Lemma F_4229c : fetch_word Plain.M.loaded_segments (0x422e4 : word) = Some W_4229c.
Proof. vm_refl. Qed.
Lemma D_4229c : decode_any W_4229c = Some (Branch BC_EQ 11 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_422a0 : bv 32 := 0xfd010113.
Lemma F_422a0 : fetch_word Plain.M.loaded_segments (0x422e8 : word) = Some W_422a0.
Proof. vm_refl. Qed.
Lemma D_422a0 : decode_any W_422a0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_422a4 : bv 32 := 0x02113423.
Lemma F_422a4 : fetch_word Plain.M.loaded_segments (0x422ec : word) = Some W_422a4.
Proof. vm_refl. Qed.
Lemma D_422a4 : decode_any W_422a4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_422a8 : bv 32 := 0x02813023.
Lemma F_422a8 : fetch_word Plain.M.loaded_segments (0x422f0 : word) = Some W_422a8.
Proof. vm_refl. Qed.
Lemma D_422a8 : decode_any W_422a8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_422ac : bv 32 := 0x00913c23.
Lemma F_422ac : fetch_word Plain.M.loaded_segments (0x422f4 : word) = Some W_422ac.
Proof. vm_refl. Qed.
Lemma D_422ac : decode_any W_422ac = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_422b0 : bv 32 := 0x01213823.
Lemma F_422b0 : fetch_word Plain.M.loaded_segments (0x422f8 : word) = Some W_422b0.
Proof. vm_refl. Qed.
Lemma D_422b0 : decode_any W_422b0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_422b4 : bv 32 := 0x00060413.
Lemma F_422b4 : fetch_word Plain.M.loaded_segments (0x422fc : word) = Some W_422b4.
Proof. vm_refl. Qed.
Lemma D_422b4 : decode_any W_422b4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_422b8 : bv 32 := 0x00054903.
Lemma F_422b8 : fetch_word Plain.M.loaded_segments (0x42300 : word) = Some W_422b8.
Proof. vm_refl. Qed.
Lemma D_422b8 : decode_any W_422b8 = Some (Load SZ1 false 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_422bc : bv 32 := 0xfff00493.
Lemma F_422bc : fetch_word Plain.M.loaded_segments (0x42304 : word) = Some W_422bc.
Proof. vm_refl. Qed.
Lemma D_422bc : decode_any W_422bc = Some (OpImm ALU_ADD 9 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_422c0 : bv 32 := 0x0204d493.
Lemma F_422c0 : fetch_word Plain.M.loaded_segments (0x42308 : word) = Some W_422c0.
Proof. vm_refl. Qed.
Lemma D_422c0 : decode_any W_422c0 = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_422c4 : bv 32 := 0xfd390613.
Lemma F_422c4 : fetch_word Plain.M.loaded_segments (0x4230c : word) = Some W_422c4.
Proof. vm_refl. Qed.
Lemma D_422c4 : decode_any W_422c4 = Some (OpImm ALU_ADD 12 18 4051, 4%Z).
Proof. vm_refl. Qed.

Definition W_422c8 : bv 32 := 0x00163613.
Lemma F_422c8 : fetch_word Plain.M.loaded_segments (0x42310 : word) = Some W_422c8.
Proof. vm_refl. Qed.
Lemma D_422c8 : decode_any W_422c8 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_422cc : bv 32 := 0x40c585b3.
Lemma F_422cc : fetch_word Plain.M.loaded_segments (0x42314 : word) = Some W_422cc.
Proof. vm_refl. Qed.
Lemma D_422cc : decode_any W_422cc = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_422d0 : bv 32 := 0x00c50533.
Lemma F_422d0 : fetch_word Plain.M.loaded_segments (0x42318 : word) = Some W_422d0.
Proof. vm_refl. Qed.
Lemma D_422d0 : decode_any W_422d0 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_422d4 : bv 32 := 0x00810613.
Lemma F_422d4 : fetch_word Plain.M.loaded_segments (0x4231c : word) = Some W_422d4.
Proof. vm_refl. Qed.
Lemma D_422d4 : decode_any W_422d4 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_422d8 : bv 32 := 0x199000ef.
Lemma F_422d8 : fetch_word Plain.M.loaded_segments (0x42320 : word) = Some W_422d8.
Proof. vm_refl. Qed.
Lemma D_422d8 : decode_any W_422d8 = Some (Jal 1 2456, 4%Z).
Proof. vm_refl. Qed.

Definition W_422dc : bv 32 := 0x0005861b.
Lemma F_422dc : fetch_word Plain.M.loaded_segments (0x42324 : word) = Some W_422dc.
Proof. vm_refl. Qed.
Lemma D_422dc : decode_any W_422dc = Some (OpImm32 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_422e0 : bv 32 := 0x04061063.
Lemma F_422e0 : fetch_word Plain.M.loaded_segments (0x42328 : word) = Some W_422e0.
Proof. vm_refl. Qed.
Lemma D_422e0 : decode_any W_422e0 = Some (Branch BC_NE 12 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_422e4 : bv 32 := 0x00813603.
Lemma F_422e4 : fetch_word Plain.M.loaded_segments (0x4232c : word) = Some W_422e4.
Proof. vm_refl. Qed.
Lemma D_422e4 : decode_any W_422e4 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_422e8 : bv 32 := 0x02d00593.
Lemma F_422e8 : fetch_word Plain.M.loaded_segments (0x42330 : word) = Some W_422e8.
Proof. vm_refl. Qed.
Lemma D_422e8 : decode_any W_422e8 = Some (OpImm ALU_ADD 11 0 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_422ec : bv 32 := 0x02b91063.
Lemma F_422ec : fetch_word Plain.M.loaded_segments (0x42334 : word) = Some W_422ec.
Proof. vm_refl. Qed.
Lemma D_422ec : decode_any W_422ec = Some (Branch BC_NE 18 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_422f0 : bv 32 := 0xfff00593.
Lemma F_422f0 : fetch_word Plain.M.loaded_segments (0x42338 : word) = Some W_422f0.
Proof. vm_refl. Qed.
Lemma D_422f0 : decode_any W_422f0 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_422f4 : bv 32 := 0x03f59593.
Lemma F_422f4 : fetch_word Plain.M.loaded_segments (0x4233c : word) = Some W_422f4.
Proof. vm_refl. Qed.
Lemma D_422f4 : decode_any W_422f4 = Some (ShiftImm ALU_SLL 11 11 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_422f8 : bv 32 := 0x02c5e263.
Lemma F_422f8 : fetch_word Plain.M.loaded_segments (0x42340 : word) = Some W_422f8.
Proof. vm_refl. Qed.
Lemma D_422f8 : decode_any W_422f8 = Some (Branch BC_LTU 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_422fc : bv 32 := 0x40c00633.
Lemma F_422fc : fetch_word Plain.M.loaded_segments (0x42344 : word) = Some W_422fc.
Proof. vm_refl. Qed.
Lemma D_422fc : decode_any W_422fc = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_42300 : bv 32 := 0x0100006f.
Lemma F_42300 : fetch_word Plain.M.loaded_segments (0x42348 : word) = Some W_42300.
Proof. vm_refl. Qed.
Lemma D_42300 : decode_any W_42300 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42304 : bv 32 := 0x01600593.
Lemma F_42304 : fetch_word Plain.M.loaded_segments (0x4234c : word) = Some W_42304.
Proof. vm_refl. Qed.
Lemma D_42304 : decode_any W_42304 = Some (OpImm ALU_ADD 11 0 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_42308 : bv 32 := 0x00008067.
Lemma F_42308 : fetch_word Plain.M.loaded_segments (0x42350 : word) = Some W_42308.
Proof. vm_refl. Qed.
Lemma D_42308 : decode_any W_42308 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4230c : bv 32 := 0x00064863.
Lemma F_4230c : fetch_word Plain.M.loaded_segments (0x42354 : word) = Some W_4230c.
Proof. vm_refl. Qed.
Lemma D_4230c : decode_any W_4230c = Some (Branch BC_LT 12 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42310 : bv 32 := 0x00000593.
Lemma F_42310 : fetch_word Plain.M.loaded_segments (0x42358 : word) = Some W_42310.
Proof. vm_refl. Qed.
Lemma D_42310 : decode_any W_42310 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42314 : bv 32 := 0x00c43023.
Lemma F_42314 : fetch_word Plain.M.loaded_segments (0x4235c : word) = Some W_42314.
Proof. vm_refl. Qed.
Lemma D_42314 : decode_any W_42314 = Some (Store SZ8 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42318 : bv 32 := 0x0080006f.
Lemma F_42318 : fetch_word Plain.M.loaded_segments (0x42360 : word) = Some W_42318.
Proof. vm_refl. Qed.
Lemma D_42318 : decode_any W_42318 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4231c : bv 32 := 0x02200593.
Lemma F_4231c : fetch_word Plain.M.loaded_segments (0x42364 : word) = Some W_4231c.
Proof. vm_refl. Qed.
Lemma D_4231c : decode_any W_4231c = Some (OpImm ALU_ADD 11 0 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_42320 : bv 32 := 0x0095f5b3.
Lemma F_42320 : fetch_word Plain.M.loaded_segments (0x42368 : word) = Some W_42320.
Proof. vm_refl. Qed.
Lemma D_42320 : decode_any W_42320 = Some (Op ALU_AND 11 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_42324 : bv 32 := 0x02813083.
Lemma F_42324 : fetch_word Plain.M.loaded_segments (0x4236c : word) = Some W_42324.
Proof. vm_refl. Qed.
Lemma D_42324 : decode_any W_42324 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42328 : bv 32 := 0x02013403.
Lemma F_42328 : fetch_word Plain.M.loaded_segments (0x42370 : word) = Some W_42328.
Proof. vm_refl. Qed.
Lemma D_42328 : decode_any W_42328 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4232c : bv 32 := 0x01813483.
Lemma F_4232c : fetch_word Plain.M.loaded_segments (0x42374 : word) = Some W_4232c.
Proof. vm_refl. Qed.
Lemma D_4232c : decode_any W_4232c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42330 : bv 32 := 0x01013903.
Lemma F_42330 : fetch_word Plain.M.loaded_segments (0x42378 : word) = Some W_42330.
Proof. vm_refl. Qed.
Lemma D_42330 : decode_any W_42330 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42334 : bv 32 := 0x03010113.
Lemma F_42334 : fetch_word Plain.M.loaded_segments (0x4237c : word) = Some W_42334.
Proof. vm_refl. Qed.
Lemma D_42334 : decode_any W_42334 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_42338 : bv 32 := 0x00008067.
Lemma F_42338 : fetch_word Plain.M.loaded_segments (0x42380 : word) = Some W_42338.
Proof. vm_refl. Qed.
Lemma D_42338 : decode_any W_42338 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4233c : bv 32 := 0x04058863.
Lemma F_4233c : fetch_word Plain.M.loaded_segments (0x42384 : word) = Some W_4233c.
Proof. vm_refl. Qed.
Lemma D_4233c : decode_any W_4233c = Some (Branch BC_EQ 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_42340 : bv 32 := 0xff010113.
Lemma F_42340 : fetch_word Plain.M.loaded_segments (0x42388 : word) = Some W_42340.
Proof. vm_refl. Qed.
Lemma D_42340 : decode_any W_42340 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_42344 : bv 32 := 0x00113423.
Lemma F_42344 : fetch_word Plain.M.loaded_segments (0x4238c : word) = Some W_42344.
Proof. vm_refl. Qed.
Lemma D_42344 : decode_any W_42344 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42348 : bv 32 := 0x00060693.
Lemma F_42348 : fetch_word Plain.M.loaded_segments (0x42390 : word) = Some W_42348.
Proof. vm_refl. Qed.
Lemma D_42348 : decode_any W_42348 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4234c : bv 32 := 0x00054603.
Lemma F_4234c : fetch_word Plain.M.loaded_segments (0x42394 : word) = Some W_4234c.
Proof. vm_refl. Qed.
Lemma D_4234c : decode_any W_4234c = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42350 : bv 32 := 0x02d00713.
Lemma F_42350 : fetch_word Plain.M.loaded_segments (0x42398 : word) = Some W_42350.
Proof. vm_refl. Qed.
Lemma D_42350 : decode_any W_42350 = Some (OpImm ALU_ADD 14 0 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_42354 : bv 32 := 0x00e61c63.
Lemma F_42354 : fetch_word Plain.M.loaded_segments (0x4239c : word) = Some W_42354.
Proof. vm_refl. Qed.
Lemma D_42354 : decode_any W_42354 = Some (Branch BC_NE 12 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42358 : bv 32 := 0x00150513.
Lemma F_42358 : fetch_word Plain.M.loaded_segments (0x423a0 : word) = Some W_42358.
Proof. vm_refl. Qed.
Lemma D_42358 : decode_any W_42358 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4235c : bv 32 := 0xfff58593.
Lemma F_4235c : fetch_word Plain.M.loaded_segments (0x423a4 : word) = Some W_4235c.
Proof. vm_refl. Qed.
Lemma D_4235c : decode_any W_4235c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_42360 : bv 32 := 0x00100613.
Lemma F_42360 : fetch_word Plain.M.loaded_segments (0x423a8 : word) = Some W_42360.
Proof. vm_refl. Qed.
Lemma D_42360 : decode_any W_42360 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_42364 : bv 32 := 0x00710713.
Lemma F_42364 : fetch_word Plain.M.loaded_segments (0x423ac : word) = Some W_42364.
Proof. vm_refl. Qed.
Lemma D_42364 : decode_any W_42364 = Some (OpImm ALU_ADD 14 2 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_42368 : bv 32 := 0x00c0006f.
Lemma F_42368 : fetch_word Plain.M.loaded_segments (0x423b0 : word) = Some W_42368.
Proof. vm_refl. Qed.
Lemma D_42368 : decode_any W_42368 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4236c : bv 32 := 0x00610713.
Lemma F_4236c : fetch_word Plain.M.loaded_segments (0x423b4 : word) = Some W_4236c.
Proof. vm_refl. Qed.
Lemma D_4236c : decode_any W_4236c = Some (OpImm ALU_ADD 14 2 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_42370 : bv 32 := 0x00000613.
Lemma F_42370 : fetch_word Plain.M.loaded_segments (0x423b8 : word) = Some W_42370.
Proof. vm_refl. Qed.
Lemma D_42370 : decode_any W_42370 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42374 : bv 32 := 0x375000ef.
Lemma F_42374 : fetch_word Plain.M.loaded_segments (0x423bc : word) = Some W_42374.
Proof. vm_refl. Qed.
Lemma D_42374 : decode_any W_42374 = Some (Jal 1 2932, 4%Z).
Proof. vm_refl. Qed.

Definition W_42378 : bv 32 := 0x00813083.
Lemma F_42378 : fetch_word Plain.M.loaded_segments (0x423c0 : word) = Some W_42378.
Proof. vm_refl. Qed.
Lemma D_42378 : decode_any W_42378 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4237c : bv 32 := 0x01010113.
Lemma F_4237c : fetch_word Plain.M.loaded_segments (0x423c4 : word) = Some W_4237c.
Proof. vm_refl. Qed.
Lemma D_4237c : decode_any W_4237c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42380 : bv 32 := 0x02059593.
Lemma F_42380 : fetch_word Plain.M.loaded_segments (0x423c8 : word) = Some W_42380.
Proof. vm_refl. Qed.
Lemma D_42380 : decode_any W_42380 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_42384 : bv 32 := 0x0205d593.
Lemma F_42384 : fetch_word Plain.M.loaded_segments (0x423cc : word) = Some W_42384.
Proof. vm_refl. Qed.
Lemma D_42384 : decode_any W_42384 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_42388 : bv 32 := 0x00008067.
Lemma F_42388 : fetch_word Plain.M.loaded_segments (0x423d0 : word) = Some W_42388.
Proof. vm_refl. Qed.
Lemma D_42388 : decode_any W_42388 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4238c : bv 32 := 0x01600593.
Lemma F_4238c : fetch_word Plain.M.loaded_segments (0x423d4 : word) = Some W_4238c.
Proof. vm_refl. Qed.
Lemma D_4238c : decode_any W_4238c = Some (OpImm ALU_ADD 11 0 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_42390 : bv 32 := 0xff1ff06f.
Lemma F_42390 : fetch_word Plain.M.loaded_segments (0x423d8 : word) = Some W_42390.
Proof. vm_refl. Qed.
Lemma D_42390 : decode_any W_42390 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

Definition W_42394 : bv 32 := 0xfd010113.
Lemma F_42394 : fetch_word Plain.M.loaded_segments (0x423dc : word) = Some W_42394.
Proof. vm_refl. Qed.
Lemma D_42394 : decode_any W_42394 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_42398 : bv 32 := 0x02113423.
Lemma F_42398 : fetch_word Plain.M.loaded_segments (0x423e0 : word) = Some W_42398.
Proof. vm_refl. Qed.
Lemma D_42398 : decode_any W_42398 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4239c : bv 32 := 0x02813023.
Lemma F_4239c : fetch_word Plain.M.loaded_segments (0x423e4 : word) = Some W_4239c.
Proof. vm_refl. Qed.
Lemma D_4239c : decode_any W_4239c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_423a0 : bv 32 := 0x43f5d613.
Lemma F_423a0 : fetch_word Plain.M.loaded_segments (0x423e8 : word) = Some W_423a0.
Proof. vm_refl. Qed.
Lemma D_423a0 : decode_any W_423a0 = Some (ShiftImm ALU_SRA 12 11 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_423a4 : bv 32 := 0x00c5c6b3.
Lemma F_423a4 : fetch_word Plain.M.loaded_segments (0x423ec : word) = Some W_423a4.
Proof. vm_refl. Qed.
Lemma D_423a4 : decode_any W_423a4 = Some (Op ALU_XOR 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_423a8 : bv 32 := 0x40c686b3.
Lemma F_423a8 : fetch_word Plain.M.loaded_segments (0x423f0 : word) = Some W_423a8.
Proof. vm_refl. Qed.
Lemma D_423a8 : decode_any W_423a8 = Some (Op ALU_SUB 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_423ac : bv 32 := 0x01e5d613.
Lemma F_423ac : fetch_word Plain.M.loaded_segments (0x423f4 : word) = Some W_423ac.
Proof. vm_refl. Qed.
Lemma D_423ac : decode_any W_423ac = Some (ShiftImm ALU_SRL 12 11 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_423b0 : bv 32 := 0x00b035b3.
Lemma F_423b0 : fetch_word Plain.M.loaded_segments (0x423f8 : word) = Some W_423b0.
Proof. vm_refl. Qed.
Lemma D_423b0 : decode_any W_423b0 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_423b4 : bv 32 := 0x00267613.
Lemma F_423b4 : fetch_word Plain.M.loaded_segments (0x423fc : word) = Some W_423b4.
Proof. vm_refl. Qed.
Lemma D_423b4 : decode_any W_423b4 = Some (OpImm ALU_AND 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_423b8 : bv 32 := 0x00c10023.
Lemma F_423b8 : fetch_word Plain.M.loaded_segments (0x42400 : word) = Some W_423b8.
Proof. vm_refl. Qed.
Lemma D_423b8 : decode_any W_423b8 = Some (Store SZ1 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_423bc : bv 32 := 0x00b13423.
Lemma F_423bc : fetch_word Plain.M.loaded_segments (0x42404 : word) = Some W_423bc.
Proof. vm_refl. Qed.
Lemma D_423bc : decode_any W_423bc = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_423c0 : bv 32 := 0x00d13823.
Lemma F_423c0 : fetch_word Plain.M.loaded_segments (0x42408 : word) = Some W_423c0.
Proof. vm_refl. Qed.
Lemma D_423c0 : decode_any W_423c0 = Some (Store SZ8 2 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_423c4 : bv 32 := 0x00013c23.
Lemma F_423c4 : fetch_word Plain.M.loaded_segments (0x4240c : word) = Some W_423c4.
Proof. vm_refl. Qed.
Lemma D_423c4 : decode_any W_423c4 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_423c8 : bv 32 := 0x00010593.
Lemma F_423c8 : fetch_word Plain.M.loaded_segments (0x42410 : word) = Some W_423c8.
Proof. vm_refl. Qed.
Lemma D_423c8 : decode_any W_423c8 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_423cc : bv 32 := 0x21d010ef.
Lemma F_423cc : fetch_word Plain.M.loaded_segments (0x42414 : word) = Some W_423cc.
Proof. vm_refl. Qed.
Lemma D_423cc : decode_any W_423cc = Some (Jal 1 6684, 4%Z).
Proof. vm_refl. Qed.

Definition W_423d0 : bv 32 := 0x00014583.
Lemma F_423d0 : fetch_word Plain.M.loaded_segments (0x42418 : word) = Some W_423d0.
Proof. vm_refl. Qed.
Lemma D_423d0 : decode_any W_423d0 = Some (Load SZ1 false 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_423d4 : bv 32 := 0x0015f593.
Lemma F_423d4 : fetch_word Plain.M.loaded_segments (0x4241c : word) = Some W_423d4.
Proof. vm_refl. Qed.
Lemma D_423d4 : decode_any W_423d4 = Some (OpImm ALU_AND 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_423d8 : bv 32 := 0x00050413.
Lemma F_423d8 : fetch_word Plain.M.loaded_segments (0x42420 : word) = Some W_423d8.
Proof. vm_refl. Qed.
Lemma D_423d8 : decode_any W_423d8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_423dc : bv 32 := 0x00058c63.
Lemma F_423dc : fetch_word Plain.M.loaded_segments (0x42424 : word) = Some W_423dc.
Proof. vm_refl. Qed.
Lemma D_423dc : decode_any W_423dc = Some (Branch BC_EQ 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_423e0 : bv 32 := 0x01813503.
Lemma F_423e0 : fetch_word Plain.M.loaded_segments (0x42428 : word) = Some W_423e0.
Proof. vm_refl. Qed.
Lemma D_423e0 : decode_any W_423e0 = Some (Load SZ8 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_423e4 : bv 32 := 0x00050863.
Lemma F_423e4 : fetch_word Plain.M.loaded_segments (0x4242c : word) = Some W_423e4.
Proof. vm_refl. Qed.
Lemma D_423e4 : decode_any W_423e4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_423e8 : bv 32 := 0x01013583.
Lemma F_423e8 : fetch_word Plain.M.loaded_segments (0x42430 : word) = Some W_423e8.
Proof. vm_refl. Qed.
Lemma D_423e8 : decode_any W_423e8 = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_423ec : bv 32 := 0x00359593.
Lemma F_423ec : fetch_word Plain.M.loaded_segments (0x42434 : word) = Some W_423ec.
Proof. vm_refl. Qed.
Lemma D_423ec : decode_any W_423ec = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_423f0 : bv 32 := 0x18d210ef.
Lemma F_423f0 : fetch_word Plain.M.loaded_segments (0x42438 : word) = Some W_423f0.
Proof. vm_refl. Qed.
Lemma D_423f0 : decode_any W_423f0 = Some (Jal 1 137612, 4%Z).
Proof. vm_refl. Qed.

Definition W_423f4 : bv 32 := 0x00803533.
Lemma F_423f4 : fetch_word Plain.M.loaded_segments (0x4243c : word) = Some W_423f4.
Proof. vm_refl. Qed.
Lemma D_423f4 : decode_any W_423f4 = Some (Op ALU_SLTU 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_423f8 : bv 32 := 0x02813083.
Lemma F_423f8 : fetch_word Plain.M.loaded_segments (0x42440 : word) = Some W_423f8.
Proof. vm_refl. Qed.
Lemma D_423f8 : decode_any W_423f8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_423fc : bv 32 := 0x02013403.
Lemma F_423fc : fetch_word Plain.M.loaded_segments (0x42444 : word) = Some W_423fc.
Proof. vm_refl. Qed.
Lemma D_423fc : decode_any W_423fc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_42400 : bv 32 := 0x03010113.
Lemma F_42400 : fetch_word Plain.M.loaded_segments (0x42448 : word) = Some W_42400.
Proof. vm_refl. Qed.
Lemma D_42400 : decode_any W_42400 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_42404 : bv 32 := 0x00008067.
Lemma F_42404 : fetch_word Plain.M.loaded_segments (0x4244c : word) = Some W_42404.
Proof. vm_refl. Qed.
Lemma D_42404 : decode_any W_42404 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_41aa4_42408.
Module Ns0_code_42af4_42c70.
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

Definition W_42af4 : bv 32 := 0xfc010113.
Lemma F_42af4 : fetch_word Plain.M.loaded_segments (0x42b3c : word) = Some W_42af4.
Proof. vm_refl. Qed.
Lemma D_42af4 : decode_any W_42af4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_42af8 : bv 32 := 0x02113c23.
Lemma F_42af8 : fetch_word Plain.M.loaded_segments (0x42b40 : word) = Some W_42af8.
Proof. vm_refl. Qed.
Lemma D_42af8 : decode_any W_42af8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_42afc : bv 32 := 0x02813823.
Lemma F_42afc : fetch_word Plain.M.loaded_segments (0x42b44 : word) = Some W_42afc.
Proof. vm_refl. Qed.
Lemma D_42afc : decode_any W_42afc = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b00 : bv 32 := 0x02913423.
Lemma F_42b00 : fetch_word Plain.M.loaded_segments (0x42b48 : word) = Some W_42b00.
Proof. vm_refl. Qed.
Lemma D_42b00 : decode_any W_42b00 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b04 : bv 32 := 0x03213023.
Lemma F_42b04 : fetch_word Plain.M.loaded_segments (0x42b4c : word) = Some W_42b04.
Proof. vm_refl. Qed.
Lemma D_42b04 : decode_any W_42b04 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b08 : bv 32 := 0x01313c23.
Lemma F_42b08 : fetch_word Plain.M.loaded_segments (0x42b50 : word) = Some W_42b08.
Proof. vm_refl. Qed.
Lemma D_42b08 : decode_any W_42b08 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b0c : bv 32 := 0x00058493.
Lemma F_42b0c : fetch_word Plain.M.loaded_segments (0x42b54 : word) = Some W_42b0c.
Proof. vm_refl. Qed.
Lemma D_42b0c : decode_any W_42b0c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b10 : bv 32 := 0x0005b603.
Lemma F_42b10 : fetch_word Plain.M.loaded_segments (0x42b58 : word) = Some W_42b10.
Proof. vm_refl. Qed.
Lemma D_42b10 : decode_any W_42b10 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b14 : bv 32 := 0x0085b583.
Lemma F_42b14 : fetch_word Plain.M.loaded_segments (0x42b5c : word) = Some W_42b14.
Proof. vm_refl. Qed.
Lemma D_42b14 : decode_any W_42b14 = Some (Load SZ8 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b18 : bv 32 := 0x00050413.
Lemma F_42b18 : fetch_word Plain.M.loaded_segments (0x42b60 : word) = Some W_42b18.
Proof. vm_refl. Qed.
Lemma D_42b18 : decode_any W_42b18 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b1c : bv 32 := 0x00060513.
Lemma F_42b1c : fetch_word Plain.M.loaded_segments (0x42b64 : word) = Some W_42b1c.
Proof. vm_refl. Qed.
Lemma D_42b1c : decode_any W_42b1c = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b20 : bv 32 := 0x3c5010ef.
Lemma F_42b20 : fetch_word Plain.M.loaded_segments (0x42b68 : word) = Some W_42b20.
Proof. vm_refl. Qed.
Lemma D_42b20 : decode_any W_42b20 = Some (Jal 1 7108, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b24 : bv 32 := 0x0005859b.
Lemma F_42b24 : fetch_word Plain.M.loaded_segments (0x42b6c : word) = Some W_42b24.
Proof. vm_refl. Qed.
Lemma D_42b24 : decode_any W_42b24 = Some (OpImm32 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b28 : bv 32 := 0x0e059a63.
Lemma F_42b28 : fetch_word Plain.M.loaded_segments (0x42b70 : word) = Some W_42b28.
Proof. vm_refl. Qed.
Lemma D_42b28 : decode_any W_42b28 = Some (Branch BC_NE 11 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b2c : bv 32 := 0x0084b903.
Lemma F_42b2c : fetch_word Plain.M.loaded_segments (0x42b74 : word) = Some W_42b2c.
Proof. vm_refl. Qed.
Lemma D_42b2c : decode_any W_42b2c = Some (Load SZ8 true 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b30 : bv 32 := 0x01f00513.
Lemma F_42b30 : fetch_word Plain.M.loaded_segments (0x42b78 : word) = Some W_42b30.
Proof. vm_refl. Qed.
Lemma D_42b30 : decode_any W_42b30 = Some (OpImm ALU_ADD 10 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b34 : bv 32 := 0x01256a63.
Lemma F_42b34 : fetch_word Plain.M.loaded_segments (0x42b7c : word) = Some W_42b34.
Proof. vm_refl. Qed.
Lemma D_42b34 : decode_any W_42b34 = Some (Branch BC_LTU 10 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b38 : bv 32 := 0x00843503.
Lemma F_42b38 : fetch_word Plain.M.loaded_segments (0x42b80 : word) = Some W_42b38.
Proof. vm_refl. Qed.
Lemma D_42b38 : decode_any W_42b38 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b3c : bv 32 := 0x0a096593.
Lemma F_42b3c : fetch_word Plain.M.loaded_segments (0x42b84 : word) = Some W_42b3c.
Proof. vm_refl. Qed.
Lemma D_42b3c : decode_any W_42b3c = Some (OpImm ALU_OR 11 18 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b40 : bv 32 := 0x00b10ba3.
Lemma F_42b40 : fetch_word Plain.M.loaded_segments (0x42b88 : word) = Some W_42b40.
Proof. vm_refl. Qed.
Lemma D_42b40 : decode_any W_42b40 = Some (Store SZ1 2 11 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b44 : bv 32 := 0x0600006f.
Lemma F_42b44 : fetch_word Plain.M.loaded_segments (0x42b8c : word) = Some W_42b44.
Proof. vm_refl. Qed.
Lemma D_42b44 : decode_any W_42b44 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b48 : bv 32 := 0x0ff00513.
Lemma F_42b48 : fetch_word Plain.M.loaded_segments (0x42b90 : word) = Some W_42b48.
Proof. vm_refl. Qed.
Lemma D_42b48 : decode_any W_42b48 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b4c : bv 32 := 0x03257e63.
Lemma F_42b4c : fetch_word Plain.M.loaded_segments (0x42b94 : word) = Some W_42b4c.
Proof. vm_refl. Qed.
Lemma D_42b4c : decode_any W_42b4c = Some (Branch BC_GEU 10 18 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b50 : bv 32 := 0x01095513.
Lemma F_42b50 : fetch_word Plain.M.loaded_segments (0x42b98 : word) = Some W_42b50.
Proof. vm_refl. Qed.
Lemma D_42b50 : decode_any W_42b50 = Some (ShiftImm ALU_SRL 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b54 : bv 32 := 0x0a050063.
Lemma F_42b54 : fetch_word Plain.M.loaded_segments (0x42b9c : word) = Some W_42b54.
Proof. vm_refl. Qed.
Lemma D_42b54 : decode_any W_42b54 = Some (Branch BC_EQ 10 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b58 : bv 32 := 0x02095513.
Lemma F_42b58 : fetch_word Plain.M.loaded_segments (0x42ba0 : word) = Some W_42b58.
Proof. vm_refl. Qed.
Lemma D_42b58 : decode_any W_42b58 = Some (ShiftImm ALU_SRL 10 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b5c : bv 32 := 0x04051863.
Lemma F_42b5c : fetch_word Plain.M.loaded_segments (0x42ba4 : word) = Some W_42b5c.
Proof. vm_refl. Qed.
Lemma D_42b5c : decode_any W_42b5c = Some (Branch BC_NE 10 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b60 : bv 32 := 0x00843503.
Lemma F_42b60 : fetch_word Plain.M.loaded_segments (0x42ba8 : word) = Some W_42b60.
Proof. vm_refl. Qed.
Lemma D_42b60 : decode_any W_42b60 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b64 : bv 32 := 0x00840993.
Lemma F_42b64 : fetch_word Plain.M.loaded_segments (0x42bac : word) = Some W_42b64.
Proof. vm_refl. Qed.
Lemma D_42b64 : decode_any W_42b64 = Some (OpImm ALU_ADD 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b68 : bv 32 := 0x0db00593.
Lemma F_42b68 : fetch_word Plain.M.loaded_segments (0x42bb0 : word) = Some W_42b68.
Proof. vm_refl. Qed.
Lemma D_42b68 : decode_any W_42b68 = Some (OpImm ALU_ADD 11 0 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b6c : bv 32 := 0x00b10ba3.
Lemma F_42b6c : fetch_word Plain.M.loaded_segments (0x42bb4 : word) = Some W_42b6c.
Proof. vm_refl. Qed.
Lemma D_42b6c : decode_any W_42b6c = Some (Store SZ1 2 11 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b70 : bv 32 := 0x01710593.
Lemma F_42b70 : fetch_word Plain.M.loaded_segments (0x42bb8 : word) = Some W_42b70.
Proof. vm_refl. Qed.
Lemma D_42b70 : decode_any W_42b70 = Some (OpImm ALU_ADD 11 2 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b74 : bv 32 := 0x948ff0ef.
Lemma F_42b74 : fetch_word Plain.M.loaded_segments (0x42bbc : word) = Some W_42b74.
Proof. vm_refl. Qed.
Lemma D_42b74 : decode_any W_42b74 = Some (Jal 1 2093384, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b78 : bv 32 := 0x0009051b.
Lemma F_42b78 : fetch_word Plain.M.loaded_segments (0x42bc0 : word) = Some W_42b78.
Proof. vm_refl. Qed.
Lemma D_42b78 : decode_any W_42b78 = Some (OpImm32 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b7c : bv 32 := 0x00098593.
Lemma F_42b7c : fetch_word Plain.M.loaded_segments (0x42bc4 : word) = Some W_42b7c.
Proof. vm_refl. Qed.
Lemma D_42b7c : decode_any W_42b7c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b80 : bv 32 := 0xf89fe0ef.
Lemma F_42b80 : fetch_word Plain.M.loaded_segments (0x42bc8 : word) = Some W_42b80.
Proof. vm_refl. Qed.
Lemma D_42b80 : decode_any W_42b80 = Some (Jal 1 2092936, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b84 : bv 32 := 0x0280006f.
Lemma F_42b84 : fetch_word Plain.M.loaded_segments (0x42bcc : word) = Some W_42b84.
Proof. vm_refl. Qed.
Lemma D_42b84 : decode_any W_42b84 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b88 : bv 32 := 0x00843503.
Lemma F_42b88 : fetch_word Plain.M.loaded_segments (0x42bd0 : word) = Some W_42b88.
Proof. vm_refl. Qed.
Lemma D_42b88 : decode_any W_42b88 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b8c : bv 32 := 0x0d900593.
Lemma F_42b8c : fetch_word Plain.M.loaded_segments (0x42bd4 : word) = Some W_42b8c.
Proof. vm_refl. Qed.
Lemma D_42b8c : decode_any W_42b8c = Some (OpImm ALU_ADD 11 0 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b90 : bv 32 := 0x00b10ba3.
Lemma F_42b90 : fetch_word Plain.M.loaded_segments (0x42bd8 : word) = Some W_42b90.
Proof. vm_refl. Qed.
Lemma D_42b90 : decode_any W_42b90 = Some (Store SZ1 2 11 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b94 : bv 32 := 0x01710593.
Lemma F_42b94 : fetch_word Plain.M.loaded_segments (0x42bdc : word) = Some W_42b94.
Proof. vm_refl. Qed.
Lemma D_42b94 : decode_any W_42b94 = Some (OpImm ALU_ADD 11 2 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b98 : bv 32 := 0x924ff0ef.
Lemma F_42b98 : fetch_word Plain.M.loaded_segments (0x42be0 : word) = Some W_42b98.
Proof. vm_refl. Qed.
Lemma D_42b98 : decode_any W_42b98 = Some (Jal 1 2093348, 4%Z).
Proof. vm_refl. Qed.

Definition W_42b9c : bv 32 := 0x00843503.
Lemma F_42b9c : fetch_word Plain.M.loaded_segments (0x42be4 : word) = Some W_42b9c.
Proof. vm_refl. Qed.
Lemma D_42b9c : decode_any W_42b9c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42ba0 : bv 32 := 0x01210ba3.
Lemma F_42ba0 : fetch_word Plain.M.loaded_segments (0x42be8 : word) = Some W_42ba0.
Proof. vm_refl. Qed.
Lemma D_42ba0 : decode_any W_42ba0 = Some (Store SZ1 2 18 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_42ba4 : bv 32 := 0x01710593.
Lemma F_42ba4 : fetch_word Plain.M.loaded_segments (0x42bec : word) = Some W_42ba4.
Proof. vm_refl. Qed.
Lemma D_42ba4 : decode_any W_42ba4 = Some (OpImm ALU_ADD 11 2 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_42ba8 : bv 32 := 0x914ff0ef.
Lemma F_42ba8 : fetch_word Plain.M.loaded_segments (0x42bf0 : word) = Some W_42ba8.
Proof. vm_refl. Qed.
Lemma D_42ba8 : decode_any W_42ba8 = Some (Jal 1 2093332, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bac : bv 32 := 0x0084b903.
Lemma F_42bac : fetch_word Plain.M.loaded_segments (0x42bf4 : word) = Some W_42bac.
Proof. vm_refl. Qed.
Lemma D_42bac : decode_any W_42bac = Some (Load SZ8 true 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bb0 : bv 32 := 0x02090463.
Lemma F_42bb0 : fetch_word Plain.M.loaded_segments (0x42bf8 : word) = Some W_42bb0.
Proof. vm_refl. Qed.
Lemma D_42bb0 : decode_any W_42bb0 = Some (Branch BC_EQ 18 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bb4 : bv 32 := 0x0004b483.
Lemma F_42bb4 : fetch_word Plain.M.loaded_segments (0x42bfc : word) = Some W_42bb4.
Proof. vm_refl. Qed.
Lemma D_42bb4 : decode_any W_42bb4 = Some (Load SZ8 true 9 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bb8 : bv 32 := 0x0004c583.
Lemma F_42bb8 : fetch_word Plain.M.loaded_segments (0x42c00 : word) = Some W_42bb8.
Proof. vm_refl. Qed.
Lemma D_42bb8 : decode_any W_42bb8 = Some (Load SZ1 false 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bbc : bv 32 := 0x00843503.
Lemma F_42bbc : fetch_word Plain.M.loaded_segments (0x42c04 : word) = Some W_42bbc.
Proof. vm_refl. Qed.
Lemma D_42bbc : decode_any W_42bbc = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bc0 : bv 32 := 0x00b10ba3.
Lemma F_42bc0 : fetch_word Plain.M.loaded_segments (0x42c08 : word) = Some W_42bc0.
Proof. vm_refl. Qed.
Lemma D_42bc0 : decode_any W_42bc0 = Some (Store SZ1 2 11 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bc4 : bv 32 := 0x01710593.
Lemma F_42bc4 : fetch_word Plain.M.loaded_segments (0x42c0c : word) = Some W_42bc4.
Proof. vm_refl. Qed.
Lemma D_42bc4 : decode_any W_42bc4 = Some (OpImm ALU_ADD 11 2 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bc8 : bv 32 := 0x8f4ff0ef.
Lemma F_42bc8 : fetch_word Plain.M.loaded_segments (0x42c10 : word) = Some W_42bc8.
Proof. vm_refl. Qed.
Lemma D_42bc8 : decode_any W_42bc8 = Some (Jal 1 2093300, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bcc : bv 32 := 0xfff90913.
Lemma F_42bcc : fetch_word Plain.M.loaded_segments (0x42c14 : word) = Some W_42bcc.
Proof. vm_refl. Qed.
Lemma D_42bcc : decode_any W_42bcc = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bd0 : bv 32 := 0x00148493.
Lemma F_42bd0 : fetch_word Plain.M.loaded_segments (0x42c18 : word) = Some W_42bd0.
Proof. vm_refl. Qed.
Lemma D_42bd0 : decode_any W_42bd0 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bd4 : bv 32 := 0xfe0912e3.
Lemma F_42bd4 : fetch_word Plain.M.loaded_segments (0x42c1c : word) = Some W_42bd4.
Proof. vm_refl. Qed.
Lemma D_42bd4 : decode_any W_42bd4 = Some (Branch BC_NE 18 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bd8 : bv 32 := 0x03813083.
Lemma F_42bd8 : fetch_word Plain.M.loaded_segments (0x42c20 : word) = Some W_42bd8.
Proof. vm_refl. Qed.
Lemma D_42bd8 : decode_any W_42bd8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bdc : bv 32 := 0x03013403.
Lemma F_42bdc : fetch_word Plain.M.loaded_segments (0x42c24 : word) = Some W_42bdc.
Proof. vm_refl. Qed.
Lemma D_42bdc : decode_any W_42bdc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_42be0 : bv 32 := 0x02813483.
Lemma F_42be0 : fetch_word Plain.M.loaded_segments (0x42c28 : word) = Some W_42be0.
Proof. vm_refl. Qed.
Lemma D_42be0 : decode_any W_42be0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_42be4 : bv 32 := 0x02013903.
Lemma F_42be4 : fetch_word Plain.M.loaded_segments (0x42c2c : word) = Some W_42be4.
Proof. vm_refl. Qed.
Lemma D_42be4 : decode_any W_42be4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_42be8 : bv 32 := 0x01813983.
Lemma F_42be8 : fetch_word Plain.M.loaded_segments (0x42c30 : word) = Some W_42be8.
Proof. vm_refl. Qed.
Lemma D_42be8 : decode_any W_42be8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bec : bv 32 := 0x04010113.
Lemma F_42bec : fetch_word Plain.M.loaded_segments (0x42c34 : word) = Some W_42bec.
Proof. vm_refl. Qed.
Lemma D_42bec : decode_any W_42bec = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bf0 : bv 32 := 0x00008067.
Lemma F_42bf0 : fetch_word Plain.M.loaded_segments (0x42c38 : word) = Some W_42bf0.
Proof. vm_refl. Qed.
Lemma D_42bf0 : decode_any W_42bf0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bf4 : bv 32 := 0x00843503.
Lemma F_42bf4 : fetch_word Plain.M.loaded_segments (0x42c3c : word) = Some W_42bf4.
Proof. vm_refl. Qed.
Lemma D_42bf4 : decode_any W_42bf4 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bf8 : bv 32 := 0x00840993.
Lemma F_42bf8 : fetch_word Plain.M.loaded_segments (0x42c40 : word) = Some W_42bf8.
Proof. vm_refl. Qed.
Lemma D_42bf8 : decode_any W_42bf8 = Some (OpImm ALU_ADD 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42bfc : bv 32 := 0x0da00593.
Lemma F_42bfc : fetch_word Plain.M.loaded_segments (0x42c44 : word) = Some W_42bfc.
Proof. vm_refl. Qed.
Lemma D_42bfc : decode_any W_42bfc = Some (OpImm ALU_ADD 11 0 218, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c00 : bv 32 := 0x00b10ba3.
Lemma F_42c00 : fetch_word Plain.M.loaded_segments (0x42c48 : word) = Some W_42c00.
Proof. vm_refl. Qed.
Lemma D_42c00 : decode_any W_42c00 = Some (Store SZ1 2 11 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c04 : bv 32 := 0x01710593.
Lemma F_42c04 : fetch_word Plain.M.loaded_segments (0x42c4c : word) = Some W_42c04.
Proof. vm_refl. Qed.
Lemma D_42c04 : decode_any W_42c04 = Some (OpImm ALU_ADD 11 2 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c08 : bv 32 := 0x8b4ff0ef.
Lemma F_42c08 : fetch_word Plain.M.loaded_segments (0x42c50 : word) = Some W_42c08.
Proof. vm_refl. Qed.
Lemma D_42c08 : decode_any W_42c08 = Some (Jal 1 2093236, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c0c : bv 32 := 0x00090513.
Lemma F_42c0c : fetch_word Plain.M.loaded_segments (0x42c54 : word) = Some W_42c0c.
Proof. vm_refl. Qed.
Lemma D_42c0c : decode_any W_42c0c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c10 : bv 32 := 0x00098593.
Lemma F_42c10 : fetch_word Plain.M.loaded_segments (0x42c58 : word) = Some W_42c10.
Proof. vm_refl. Qed.
Lemma D_42c10 : decode_any W_42c10 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c14 : bv 32 := 0xe91fe0ef.
Lemma F_42c14 : fetch_word Plain.M.loaded_segments (0x42c5c : word) = Some W_42c14.
Proof. vm_refl. Qed.
Lemma D_42c14 : decode_any W_42c14 = Some (Jal 1 2092688, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c18 : bv 32 := 0xf95ff06f.
Lemma F_42c18 : fetch_word Plain.M.loaded_segments (0x42c60 : word) = Some W_42c18.
Proof. vm_refl. Qed.
Lemma D_42c18 : decode_any W_42c18 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c1c : bv 32 := 0x04800513.
Lemma F_42c1c : fetch_word Plain.M.loaded_segments (0x42c64 : word) = Some W_42c1c.
Proof. vm_refl. Qed.
Lemma D_42c1c : decode_any W_42c1c = Some (OpImm ALU_ADD 10 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c20 : bv 32 := 0x1f0210ef.
Lemma F_42c20 : fetch_word Plain.M.loaded_segments (0x42c68 : word) = Some W_42c20.
Proof. vm_refl. Qed.
Lemma D_42c20 : decode_any W_42c20 = Some (Jal 1 135664, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c24 : bv 32 := 0x00050413.
Lemma F_42c24 : fetch_word Plain.M.loaded_segments (0x42c6c : word) = Some W_42c24.
Proof. vm_refl. Qed.
Lemma D_42c24 : decode_any W_42c24 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c28 : bv 32 := 0x00010513.
Lemma F_42c28 : fetch_word Plain.M.loaded_segments (0x42c70 : word) = Some W_42c28.
Proof. vm_refl. Qed.
Lemma D_42c28 : decode_any W_42c28 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c2c : bv 32 := 0x00300593.
Lemma F_42c2c : fetch_word Plain.M.loaded_segments (0x42c74 : word) = Some W_42c2c.
Proof. vm_refl. Qed.
Lemma D_42c2c : decode_any W_42c2c = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c30 : bv 32 := 0x4c1010ef.
Lemma F_42c30 : fetch_word Plain.M.loaded_segments (0x42c78 : word) = Some W_42c30.
Proof. vm_refl. Qed.
Lemma D_42c30 : decode_any W_42c30 = Some (Jal 1 7360, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c34 : bv 32 := 0x00013583.
Lemma F_42c34 : fetch_word Plain.M.loaded_segments (0x42c7c : word) = Some W_42c34.
Proof. vm_refl. Qed.
Lemma D_42c34 : decode_any W_42c34 = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c38 : bv 32 := 0x00813603.
Lemma F_42c38 : fetch_word Plain.M.loaded_segments (0x42c80 : word) = Some W_42c38.
Proof. vm_refl. Qed.
Lemma D_42c38 : decode_any W_42c38 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c3c : bv 32 := 0x00040513.
Lemma F_42c3c : fetch_word Plain.M.loaded_segments (0x42c84 : word) = Some W_42c3c.
Proof. vm_refl. Qed.
Lemma D_42c3c : decode_any W_42c3c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c40 : bv 32 := 0x545010ef.
Lemma F_42c40 : fetch_word Plain.M.loaded_segments (0x42c88 : word) = Some W_42c40.
Proof. vm_refl. Qed.
Lemma D_42c40 : decode_any W_42c40 = Some (Jal 1 7492, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c44 : bv 32 := 0x0007d517.
Lemma F_42c44 : fetch_word Plain.M.loaded_segments (0x42c8c : word) = Some W_42c44.
Proof. vm_refl. Qed.
Lemma D_42c44 : decode_any W_42c44 = Some (Auipc 10 125, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c48 : bv 32 := 0x00002617.
Lemma F_42c48 : fetch_word Plain.M.loaded_segments (0x42c90 : word) = Some W_42c48.
Proof. vm_refl. Qed.
Lemma D_42c48 : decode_any W_42c48 = Some (Auipc 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c4c : bv 32 := 0x33450593.
Lemma F_42c4c : fetch_word Plain.M.loaded_segments (0x42c94 : word) = Some W_42c4c.
Proof. vm_refl. Qed.
Lemma D_42c4c : decode_any W_42c4c = Some (OpImm ALU_ADD 11 10 820, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c50 : bv 32 := 0xe1460613.
Lemma F_42c50 : fetch_word Plain.M.loaded_segments (0x42c98 : word) = Some W_42c50.
Proof. vm_refl. Qed.
Lemma D_42c50 : decode_any W_42c50 = Some (OpImm ALU_ADD 12 12 3604, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c54 : bv 32 := 0x00040513.
Lemma F_42c54 : fetch_word Plain.M.loaded_segments (0x42c9c : word) = Some W_42c54.
Proof. vm_refl. Qed.
Lemma D_42c54 : decode_any W_42c54 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c58 : bv 32 := 0x3bc210ef.
Lemma F_42c58 : fetch_word Plain.M.loaded_segments (0x42ca0 : word) = Some W_42c58.
Proof. vm_refl. Qed.
Lemma D_42c58 : decode_any W_42c58 = Some (Jal 1 136124, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c5c : bv 32 := 0x00050493.
Lemma F_42c5c : fetch_word Plain.M.loaded_segments (0x42ca4 : word) = Some W_42c5c.
Proof. vm_refl. Qed.
Lemma D_42c5c : decode_any W_42c5c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c60 : bv 32 := 0x00040513.
Lemma F_42c60 : fetch_word Plain.M.loaded_segments (0x42ca8 : word) = Some W_42c60.
Proof. vm_refl. Qed.
Lemma D_42c60 : decode_any W_42c60 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c64 : bv 32 := 0x2b0210ef.
Lemma F_42c64 : fetch_word Plain.M.loaded_segments (0x42cac : word) = Some W_42c64.
Proof. vm_refl. Qed.
Lemma D_42c64 : decode_any W_42c64 = Some (Jal 1 135856, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c68 : bv 32 := 0x00048513.
Lemma F_42c68 : fetch_word Plain.M.loaded_segments (0x42cb0 : word) = Some W_42c68.
Proof. vm_refl. Qed.
Lemma D_42c68 : decode_any W_42c68 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_42c6c : bv 32 := 0x3a45f0ef.
Lemma F_42c6c : fetch_word Plain.M.loaded_segments (0x42cb4 : word) = Some W_42c6c.
Proof. vm_refl. Qed.
Lemma D_42c6c : decode_any W_42c6c = Some (Jal 1 390052, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_42af4_42c70.
Module Ns0_code_39084_392a0.
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

Definition W_39084 : bv 32 := 0xc6010113.
Lemma F_39084 : fetch_word Plain.M.loaded_segments (0x390cc : word) = Some W_39084.
Proof. vm_refl. Qed.
Lemma D_39084 : decode_any W_39084 = Some (OpImm ALU_ADD 2 2 3168, 4%Z).
Proof. vm_refl. Qed.

Definition W_39088 : bv 32 := 0x38113c23.
Lemma F_39088 : fetch_word Plain.M.loaded_segments (0x390d0 : word) = Some W_39088.
Proof. vm_refl. Qed.
Lemma D_39088 : decode_any W_39088 = Some (Store SZ8 2 1 920, 4%Z).
Proof. vm_refl. Qed.

Definition W_3908c : bv 32 := 0x38813823.
Lemma F_3908c : fetch_word Plain.M.loaded_segments (0x390d4 : word) = Some W_3908c.
Proof. vm_refl. Qed.
Lemma D_3908c : decode_any W_3908c = Some (Store SZ8 2 8 912, 4%Z).
Proof. vm_refl. Qed.

Definition W_39090 : bv 32 := 0x00058613.
Lemma F_39090 : fetch_word Plain.M.loaded_segments (0x390d8 : word) = Some W_39090.
Proof. vm_refl. Qed.
Lemma D_39090 : decode_any W_39090 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39094 : bv 32 := 0x00050593.
Lemma F_39094 : fetch_word Plain.M.loaded_segments (0x390dc : word) = Some W_39094.
Proof. vm_refl. Qed.
Lemma D_39094 : decode_any W_39094 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39098 : bv 32 := 0x37810513.
Lemma F_39098 : fetch_word Plain.M.loaded_segments (0x390e0 : word) = Some W_39098.
Proof. vm_refl. Qed.
Lemma D_39098 : decode_any W_39098 = Some (OpImm ALU_ADD 10 2 888, 4%Z).
Proof. vm_refl. Qed.

Definition W_3909c : bv 32 := 0x204000ef.
Lemma F_3909c : fetch_word Plain.M.loaded_segments (0x390e4 : word) = Some W_3909c.
Proof. vm_refl. Qed.
Lemma D_3909c : decode_any W_3909c = Some (Jal 1 516, 4%Z).
Proof. vm_refl. Qed.

Definition W_390a0 : bv 32 := 0x26810513.
Lemma F_390a0 : fetch_word Plain.M.loaded_segments (0x390e8 : word) = Some W_390a0.
Proof. vm_refl. Qed.
Lemma D_390a0 : decode_any W_390a0 = Some (OpImm ALU_ADD 10 2 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_390a4 : bv 32 := 0x37810593.
Lemma F_390a4 : fetch_word Plain.M.loaded_segments (0x390ec : word) = Some W_390a4.
Proof. vm_refl. Qed.
Lemma D_390a4 : decode_any W_390a4 = Some (OpImm ALU_ADD 11 2 888, 4%Z).
Proof. vm_refl. Qed.

Definition W_390a8 : bv 32 := 0x00800613.
Lemma F_390a8 : fetch_word Plain.M.loaded_segments (0x390f0 : word) = Some W_390a8.
Proof. vm_refl. Qed.
Lemma D_390a8 : decode_any W_390a8 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_390ac : bv 32 := 0x2ac000ef.
Lemma F_390ac : fetch_word Plain.M.loaded_segments (0x390f4 : word) = Some W_390ac.
Proof. vm_refl. Qed.
Lemma D_390ac : decode_any W_390ac = Some (Jal 1 684, 4%Z).
Proof. vm_refl. Qed.

Definition W_390b0 : bv 32 := 0x24013823.
Lemma F_390b0 : fetch_word Plain.M.loaded_segments (0x390f8 : word) = Some W_390b0.
Proof. vm_refl. Qed.
Lemma D_390b0 : decode_any W_390b0 = Some (Store SZ8 2 0 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_390b4 : bv 32 := 0x24013c23.
Lemma F_390b4 : fetch_word Plain.M.loaded_segments (0x390fc : word) = Some W_390b4.
Proof. vm_refl. Qed.
Lemma D_390b4 : decode_any W_390b4 = Some (Store SZ8 2 0 600, 4%Z).
Proof. vm_refl. Qed.

Definition W_390b8 : bv 32 := 0x26013023.
Lemma F_390b8 : fetch_word Plain.M.loaded_segments (0x39100 : word) = Some W_390b8.
Proof. vm_refl. Qed.
Lemma D_390b8 : decode_any W_390b8 = Some (Store SZ8 2 0 608, 4%Z).
Proof. vm_refl. Qed.

Definition W_390bc : bv 32 := 0x00087517.
Lemma F_390bc : fetch_word Plain.M.loaded_segments (0x39104 : word) = Some W_390bc.
Proof. vm_refl. Qed.
Lemma D_390bc : decode_any W_390bc = Some (Auipc 10 135, 4%Z).
Proof. vm_refl. Qed.

Definition W_390c0 : bv 32 := 0x25010593.
Lemma F_390c0 : fetch_word Plain.M.loaded_segments (0x39108 : word) = Some W_390c0.
Proof. vm_refl. Qed.
Lemma D_390c0 : decode_any W_390c0 = Some (OpImm ALU_ADD 11 2 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_390c4 : bv 32 := 0x40000613.
Lemma F_390c4 : fetch_word Plain.M.loaded_segments (0x3910c : word) = Some W_390c4.
Proof. vm_refl. Qed.
Lemma D_390c4 : decode_any W_390c4 = Some (OpImm ALU_ADD 12 0 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_390c8 : bv 32 := 0x22013c23.
Lemma F_390c8 : fetch_word Plain.M.loaded_segments (0x39110 : word) = Some W_390c8.
Proof. vm_refl. Qed.
Lemma D_390c8 : decode_any W_390c8 = Some (Store SZ8 2 0 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_390cc : bv 32 := 0x24013023.
Lemma F_390cc : fetch_word Plain.M.loaded_segments (0x39114 : word) = Some W_390cc.
Proof. vm_refl. Qed.
Lemma D_390cc : decode_any W_390cc = Some (Store SZ8 2 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_390d0 : bv 32 := 0x24012423.
Lemma F_390d0 : fetch_word Plain.M.loaded_segments (0x39118 : word) = Some W_390d0.
Proof. vm_refl. Qed.
Lemma D_390d0 : decode_any W_390d0 = Some (Store SZ4 2 0 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_390d4 : bv 32 := 0x00087697.
Lemma F_390d4 : fetch_word Plain.M.loaded_segments (0x3911c : word) = Some W_390d4.
Proof. vm_refl. Qed.
Lemma D_390d4 : decode_any W_390d4 = Some (Auipc 13 135, 4%Z).
Proof. vm_refl. Qed.

Definition W_390d8 : bv 32 := 0xd2c50513.
Lemma F_390d8 : fetch_word Plain.M.loaded_segments (0x39120 : word) = Some W_390d8.
Proof. vm_refl. Qed.
Lemma D_390d8 : decode_any W_390d8 = Some (OpImm ALU_ADD 10 10 3372, 4%Z).
Proof. vm_refl. Qed.

Definition W_390dc : bv 32 := 0x8d468693.
Lemma F_390dc : fetch_word Plain.M.loaded_segments (0x39124 : word) = Some W_390dc.
Proof. vm_refl. Qed.
Lemma D_390dc : decode_any W_390dc = Some (OpImm ALU_ADD 13 13 2260, 4%Z).
Proof. vm_refl. Qed.

Definition W_390e0 : bv 32 := 0x20a13c23.
Lemma F_390e0 : fetch_word Plain.M.loaded_segments (0x39128 : word) = Some W_390e0.
Proof. vm_refl. Qed.
Lemma D_390e0 : decode_any W_390e0 = Some (Store SZ8 2 10 536, 4%Z).
Proof. vm_refl. Qed.

Definition W_390e4 : bv 32 := 0x22b13023.
Lemma F_390e4 : fetch_word Plain.M.loaded_segments (0x3912c : word) = Some W_390e4.
Proof. vm_refl. Qed.
Lemma D_390e4 : decode_any W_390e4 = Some (Store SZ8 2 11 544, 4%Z).
Proof. vm_refl. Qed.

Definition W_390e8 : bv 32 := 0x22c12423.
Lemma F_390e8 : fetch_word Plain.M.loaded_segments (0x39130 : word) = Some W_390e8.
Proof. vm_refl. Qed.
Lemma D_390e8 : decode_any W_390e8 = Some (Store SZ4 2 12 552, 4%Z).
Proof. vm_refl. Qed.

Definition W_390ec : bv 32 := 0x22013823.
Lemma F_390ec : fetch_word Plain.M.loaded_segments (0x39134 : word) = Some W_390ec.
Proof. vm_refl. Qed.
Lemma D_390ec : decode_any W_390ec = Some (Store SZ8 2 0 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_390f0 : bv 32 := 0x01868513.
Lemma F_390f0 : fetch_word Plain.M.loaded_segments (0x39138 : word) = Some W_390f0.
Proof. vm_refl. Qed.
Lemma D_390f0 : decode_any W_390f0 = Some (OpImm ALU_ADD 10 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_390f4 : bv 32 := 0x04068593.
Lemma F_390f4 : fetch_word Plain.M.loaded_segments (0x3913c : word) = Some W_390f4.
Proof. vm_refl. Qed.
Lemma D_390f4 : decode_any W_390f4 = Some (OpImm ALU_ADD 11 13 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_390f8 : bv 32 := 0x00a13423.
Lemma F_390f8 : fetch_word Plain.M.loaded_segments (0x39140 : word) = Some W_390f8.
Proof. vm_refl. Qed.
Lemma D_390f8 : decode_any W_390f8 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_390fc : bv 32 := 0x00b13823.
Lemma F_390fc : fetch_word Plain.M.loaded_segments (0x39144 : word) = Some W_390fc.
Proof. vm_refl. Qed.
Lemma D_390fc : decode_any W_390fc = Some (Store SZ8 2 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_39100 : bv 32 := 0x00013c23.
Lemma F_39100 : fetch_word Plain.M.loaded_segments (0x39148 : word) = Some W_39100.
Proof. vm_refl. Qed.
Lemma D_39100 : decode_any W_39100 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_39104 : bv 32 := 0x00c12c23.
Lemma F_39104 : fetch_word Plain.M.loaded_segments (0x3914c : word) = Some W_39104.
Proof. vm_refl. Qed.
Lemma D_39104 : decode_any W_39104 = Some (Store SZ4 2 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_39108 : bv 32 := 0x02010513.
Lemma F_39108 : fetch_word Plain.M.loaded_segments (0x39150 : word) = Some W_39108.
Proof. vm_refl. Qed.
Lemma D_39108 : decode_any W_39108 = Some (OpImm ALU_ADD 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3910c : bv 32 := 0x26810593.
Lemma F_3910c : fetch_word Plain.M.loaded_segments (0x39154 : word) = Some W_3910c.
Proof. vm_refl. Qed.
Lemma D_3910c : decode_any W_3910c = Some (OpImm ALU_ADD 11 2 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_39110 : bv 32 := 0x21810613.
Lemma F_39110 : fetch_word Plain.M.loaded_segments (0x39158 : word) = Some W_39110.
Proof. vm_refl. Qed.
Lemma D_39110 : decode_any W_39110 = Some (OpImm ALU_ADD 12 2 536, 4%Z).
Proof. vm_refl. Qed.

Definition W_39114 : bv 32 := 0x00810693.
Lemma F_39114 : fetch_word Plain.M.loaded_segments (0x3915c : word) = Some W_39114.
Proof. vm_refl. Qed.
Lemma D_39114 : decode_any W_39114 = Some (OpImm ALU_ADD 13 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_39118 : bv 32 := 0x00710713.
Lemma F_39118 : fetch_word Plain.M.loaded_segments (0x39160 : word) = Some W_39118.
Proof. vm_refl. Qed.
Lemma D_39118 : decode_any W_39118 = Some (OpImm ALU_ADD 14 2 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3911c : bv 32 := 0x34c000ef.
Lemma F_3911c : fetch_word Plain.M.loaded_segments (0x39164 : word) = Some W_3911c.
Proof. vm_refl. Qed.
Lemma D_3911c : decode_any W_3911c = Some (Jal 1 844, 4%Z).
Proof. vm_refl. Qed.

Definition W_39120 : bv 32 := 0x00012423.
Lemma F_39120 : fetch_word Plain.M.loaded_segments (0x39168 : word) = Some W_39120.
Proof. vm_refl. Qed.
Lemma D_39120 : decode_any W_39120 = Some (Store SZ4 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_39124 : bv 32 := 0x5c8310ef.
Lemma F_39124 : fetch_word Plain.M.loaded_segments (0x3916c : word) = Some W_39124.
Proof. vm_refl. Qed.
Lemma D_39124 : decode_any W_39124 = Some (Jal 1 202184, 4%Z).
Proof. vm_refl. Qed.

Definition W_39128 : bv 32 := 0x00a13823.
Lemma F_39128 : fetch_word Plain.M.loaded_segments (0x39170 : word) = Some W_39128.
Proof. vm_refl. Qed.
Lemma D_39128 : decode_any W_39128 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3912c : bv 32 := 0x02010513.
Lemma F_3912c : fetch_word Plain.M.loaded_segments (0x39174 : word) = Some W_3912c.
Proof. vm_refl. Qed.
Lemma D_3912c : decode_any W_3912c = Some (OpImm ALU_ADD 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_39130 : bv 32 := 0x2e80c0ef.
Lemma F_39130 : fetch_word Plain.M.loaded_segments (0x39178 : word) = Some W_39130.
Proof. vm_refl. Qed.
Lemma D_39130 : decode_any W_39130 = Some (Jal 1 49896, 4%Z).
Proof. vm_refl. Qed.

Definition W_39134 : bv 32 := 0x21013583.
Lemma F_39134 : fetch_word Plain.M.loaded_segments (0x3917c : word) = Some W_39134.
Proof. vm_refl. Qed.
Lemma D_39134 : decode_any W_39134 = Some (Load SZ8 true 11 2 528, 4%Z).
Proof. vm_refl. Qed.

Definition W_39138 : bv 32 := 0x02010513.
Lemma F_39138 : fetch_word Plain.M.loaded_segments (0x39180 : word) = Some W_39138.
Proof. vm_refl. Qed.
Lemma D_39138 : decode_any W_39138 = Some (OpImm ALU_ADD 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3913c : bv 32 := 0x00810613.
Lemma F_3913c : fetch_word Plain.M.loaded_segments (0x39184 : word) = Some W_3913c.
Proof. vm_refl. Qed.
Lemma D_3913c : decode_any W_3913c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_39140 : bv 32 := 0x4180c0ef.
Lemma F_39140 : fetch_word Plain.M.loaded_segments (0x39188 : word) = Some W_39140.
Proof. vm_refl. Qed.
Lemma D_39140 : decode_any W_39140 = Some (Jal 1 50200, 4%Z).
Proof. vm_refl. Qed.

Definition W_39144 : bv 32 := 0x02010513.
Lemma F_39144 : fetch_word Plain.M.loaded_segments (0x3918c : word) = Some W_39144.
Proof. vm_refl. Qed.
Lemma D_39144 : decode_any W_39144 = Some (OpImm ALU_ADD 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_39148 : bv 32 := 0x39c000ef.
Lemma F_39148 : fetch_word Plain.M.loaded_segments (0x39190 : word) = Some W_39148.
Proof. vm_refl. Qed.
Lemma D_39148 : decode_any W_39148 = Some (Jal 1 924, 4%Z).
Proof. vm_refl. Qed.

Definition W_3914c : bv 32 := 0x23013503.
Lemma F_3914c : fetch_word Plain.M.loaded_segments (0x39194 : word) = Some W_3914c.
Proof. vm_refl. Qed.
Lemma D_3914c : decode_any W_3914c = Some (Load SZ8 true 10 2 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_39150 : bv 32 := 0x00050a63.
Lemma F_39150 : fetch_word Plain.M.loaded_segments (0x39198 : word) = Some W_39150.
Proof. vm_refl. Qed.
Lemma D_39150 : decode_any W_39150 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_39154 : bv 32 := 0x24013583.
Lemma F_39154 : fetch_word Plain.M.loaded_segments (0x3919c : word) = Some W_39154.
Proof. vm_refl. Qed.
Lemma D_39154 : decode_any W_39154 = Some (Load SZ8 true 11 2 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_39158 : bv 32 := 0x22a13c23.
Lemma F_39158 : fetch_word Plain.M.loaded_segments (0x391a0 : word) = Some W_39158.
Proof. vm_refl. Qed.
Lemma D_39158 : decode_any W_39158 = Some (Store SZ8 2 10 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_3915c : bv 32 := 0x40a585b3.
Lemma F_3915c : fetch_word Plain.M.loaded_segments (0x391a4 : word) = Some W_3915c.
Proof. vm_refl. Qed.
Lemma D_3915c : decode_any W_3915c = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_39160 : bv 32 := 0x41d2a0ef.
Lemma F_39160 : fetch_word Plain.M.loaded_segments (0x391a8 : word) = Some W_39160.
Proof. vm_refl. Qed.
Lemma D_39160 : decode_any W_39160 = Some (Jal 1 175132, 4%Z).
Proof. vm_refl. Qed.

Definition W_39164 : bv 32 := 0x25013503.
Lemma F_39164 : fetch_word Plain.M.loaded_segments (0x391ac : word) = Some W_39164.
Proof. vm_refl. Qed.
Lemma D_39164 : decode_any W_39164 = Some (Load SZ8 true 10 2 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_39168 : bv 32 := 0x00050a63.
Lemma F_39168 : fetch_word Plain.M.loaded_segments (0x391b0 : word) = Some W_39168.
Proof. vm_refl. Qed.
Lemma D_39168 : decode_any W_39168 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3916c : bv 32 := 0x26013583.
Lemma F_3916c : fetch_word Plain.M.loaded_segments (0x391b4 : word) = Some W_3916c.
Proof. vm_refl. Qed.
Lemma D_3916c : decode_any W_3916c = Some (Load SZ8 true 11 2 608, 4%Z).
Proof. vm_refl. Qed.

Definition W_39170 : bv 32 := 0x24a13c23.
Lemma F_39170 : fetch_word Plain.M.loaded_segments (0x391b8 : word) = Some W_39170.
Proof. vm_refl. Qed.
Lemma D_39170 : decode_any W_39170 = Some (Store SZ8 2 10 600, 4%Z).
Proof. vm_refl. Qed.

Definition W_39174 : bv 32 := 0x40a585b3.
Lemma F_39174 : fetch_word Plain.M.loaded_segments (0x391bc : word) = Some W_39174.
Proof. vm_refl. Qed.
Lemma D_39174 : decode_any W_39174 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_39178 : bv 32 := 0x4052a0ef.
Lemma F_39178 : fetch_word Plain.M.loaded_segments (0x391c0 : word) = Some W_39178.
Proof. vm_refl. Qed.
Lemma D_39178 : decode_any W_39178 = Some (Jal 1 175108, 4%Z).
Proof. vm_refl. Qed.

Definition W_3917c : bv 32 := 0x0008c517.
Lemma F_3917c : fetch_word Plain.M.loaded_segments (0x391c4 : word) = Some W_3917c.
Proof. vm_refl. Qed.
Lemma D_3917c : decode_any W_3917c = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_39180 : bv 32 := 0x7bc53403.
Lemma F_39180 : fetch_word Plain.M.loaded_segments (0x391c8 : word) = Some W_39180.
Proof. vm_refl. Qed.
Lemma D_39180 : decode_any W_39180 = Some (Load SZ8 true 8 10 1980, 4%Z).
Proof. vm_refl. Qed.

Definition W_39184 : bv 32 := 0x00043503.
Lemma F_39184 : fetch_word Plain.M.loaded_segments (0x391cc : word) = Some W_39184.
Proof. vm_refl. Qed.
Lemma D_39184 : decode_any W_39184 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39188 : bv 32 := 0x01843583.
Lemma F_39188 : fetch_word Plain.M.loaded_segments (0x391d0 : word) = Some W_39188.
Proof. vm_refl. Qed.
Lemma D_39188 : decode_any W_39188 = Some (Load SZ8 true 11 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3918c : bv 32 := 0x26a13423.
Lemma F_3918c : fetch_word Plain.M.loaded_segments (0x391d4 : word) = Some W_3918c.
Proof. vm_refl. Qed.
Lemma D_3918c : decode_any W_3918c = Some (Store SZ8 2 10 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_39190 : bv 32 := 0xfe853503.
Lemma F_39190 : fetch_word Plain.M.loaded_segments (0x391d8 : word) = Some W_39190.
Proof. vm_refl. Qed.
Lemma D_39190 : decode_any W_39190 = Some (Load SZ8 true 10 10 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_39194 : bv 32 := 0x26810613.
Lemma F_39194 : fetch_word Plain.M.loaded_segments (0x391dc : word) = Some W_39194.
Proof. vm_refl. Qed.
Lemma D_39194 : decode_any W_39194 = Some (OpImm ALU_ADD 12 2 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_39198 : bv 32 := 0x00a60533.
Lemma F_39198 : fetch_word Plain.M.loaded_segments (0x391e0 : word) = Some W_39198.
Proof. vm_refl. Qed.
Lemma D_39198 : decode_any W_39198 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3919c : bv 32 := 0x0008c617.
Lemma F_3919c : fetch_word Plain.M.loaded_segments (0x391e4 : word) = Some W_3919c.
Proof. vm_refl. Qed.
Lemma D_3919c : decode_any W_3919c = Some (Auipc 12 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_391a0 : bv 32 := 0x00b53023.
Lemma F_391a0 : fetch_word Plain.M.loaded_segments (0x391e8 : word) = Some W_391a0.
Proof. vm_refl. Qed.
Lemma D_391a0 : decode_any W_391a0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_391a4 : bv 32 := 0x7a463503.
Lemma F_391a4 : fetch_word Plain.M.loaded_segments (0x391ec : word) = Some W_391a4.
Proof. vm_refl. Qed.
Lemma D_391a4 : decode_any W_391a4 = Some (Load SZ8 true 10 12 1956, 4%Z).
Proof. vm_refl. Qed.

Definition W_391a8 : bv 32 := 0x2b814583.
Lemma F_391a8 : fetch_word Plain.M.loaded_segments (0x391f0 : word) = Some W_391a8.
Proof. vm_refl. Qed.
Lemma D_391a8 : decode_any W_391a8 = Some (Load SZ1 false 11 2 696, 4%Z).
Proof. vm_refl. Qed.

Definition W_391ac : bv 32 := 0x01050513.
Lemma F_391ac : fetch_word Plain.M.loaded_segments (0x391f4 : word) = Some W_391ac.
Proof. vm_refl. Qed.
Lemma D_391ac : decode_any W_391ac = Some (OpImm ALU_ADD 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_391b0 : bv 32 := 0x0015f593.
Lemma F_391b0 : fetch_word Plain.M.loaded_segments (0x391f8 : word) = Some W_391b0.
Proof. vm_refl. Qed.
Lemma D_391b0 : decode_any W_391b0 = Some (OpImm ALU_AND 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_391b4 : bv 32 := 0x26a13c23.
Lemma F_391b4 : fetch_word Plain.M.loaded_segments (0x391fc : word) = Some W_391b4.
Proof. vm_refl. Qed.
Lemma D_391b4 : decode_any W_391b4 = Some (Store SZ8 2 10 632, 4%Z).
Proof. vm_refl. Qed.

Definition W_391b8 : bv 32 := 0x00058a63.
Lemma F_391b8 : fetch_word Plain.M.loaded_segments (0x39200 : word) = Some W_391b8.
Proof. vm_refl. Qed.
Lemma D_391b8 : decode_any W_391b8 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_391bc : bv 32 := 0x2b813583.
Lemma F_391bc : fetch_word Plain.M.loaded_segments (0x39204 : word) = Some W_391bc.
Proof. vm_refl. Qed.
Lemma D_391bc : decode_any W_391bc = Some (Load SZ8 true 11 2 696, 4%Z).
Proof. vm_refl. Qed.

Definition W_391c0 : bv 32 := 0x2c813503.
Lemma F_391c0 : fetch_word Plain.M.loaded_segments (0x39208 : word) = Some W_391c0.
Proof. vm_refl. Qed.
Lemma D_391c0 : decode_any W_391c0 = Some (Load SZ8 true 10 2 712, 4%Z).
Proof. vm_refl. Qed.

Definition W_391c4 : bv 32 := 0xffe5f593.
Lemma F_391c4 : fetch_word Plain.M.loaded_segments (0x3920c : word) = Some W_391c4.
Proof. vm_refl. Qed.
Lemma D_391c4 : decode_any W_391c4 = Some (OpImm ALU_AND 11 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_391c8 : bv 32 := 0x3b52a0ef.
Lemma F_391c8 : fetch_word Plain.M.loaded_segments (0x39210 : word) = Some W_391c8.
Proof. vm_refl. Qed.
Lemma D_391c8 : decode_any W_391c8 = Some (Jal 1 175028, 4%Z).
Proof. vm_refl. Qed.

Definition W_391cc : bv 32 := 0x0008c517.
Lemma F_391cc : fetch_word Plain.M.loaded_segments (0x39214 : word) = Some W_391cc.
Proof. vm_refl. Qed.
Lemma D_391cc : decode_any W_391cc = Some (Auipc 10 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_391d0 : bv 32 := 0x77c53503.
Lemma F_391d0 : fetch_word Plain.M.loaded_segments (0x39218 : word) = Some W_391d0.
Proof. vm_refl. Qed.
Lemma D_391d0 : decode_any W_391d0 = Some (Load SZ8 true 10 10 1916, 4%Z).
Proof. vm_refl. Qed.

Definition W_391d4 : bv 32 := 0x01050513.
Lemma F_391d4 : fetch_word Plain.M.loaded_segments (0x3921c : word) = Some W_391d4.
Proof. vm_refl. Qed.
Lemma D_391d4 : decode_any W_391d4 = Some (OpImm ALU_ADD 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_391d8 : bv 32 := 0x26a13c23.
Lemma F_391d8 : fetch_word Plain.M.loaded_segments (0x39220 : word) = Some W_391d8.
Proof. vm_refl. Qed.
Lemma D_391d8 : decode_any W_391d8 = Some (Store SZ8 2 10 632, 4%Z).
Proof. vm_refl. Qed.

Definition W_391dc : bv 32 := 0x28010513.
Lemma F_391dc : fetch_word Plain.M.loaded_segments (0x39224 : word) = Some W_391dc.
Proof. vm_refl. Qed.
Lemma D_391dc : decode_any W_391dc = Some (OpImm ALU_ADD 10 2 640, 4%Z).
Proof. vm_refl. Qed.

Definition W_391e0 : bv 32 := 0x76d560ef.
Lemma F_391e0 : fetch_word Plain.M.loaded_segments (0x39228 : word) = Some W_391e0.
Proof. vm_refl. Qed.
Lemma D_391e0 : decode_any W_391e0 = Some (Jal 1 356204, 4%Z).
Proof. vm_refl. Qed.

Definition W_391e4 : bv 32 := 0x00840593.
Lemma F_391e4 : fetch_word Plain.M.loaded_segments (0x3922c : word) = Some W_391e4.
Proof. vm_refl. Qed.
Lemma D_391e4 : decode_any W_391e4 = Some (OpImm ALU_ADD 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_391e8 : bv 32 := 0x26810513.
Lemma F_391e8 : fetch_word Plain.M.loaded_segments (0x39230 : word) = Some W_391e8.
Proof. vm_refl. Qed.
Lemma D_391e8 : decode_any W_391e8 = Some (OpImm ALU_ADD 10 2 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_391ec : bv 32 := 0x269320ef.
Lemma F_391ec : fetch_word Plain.M.loaded_segments (0x39234 : word) = Some W_391ec.
Proof. vm_refl. Qed.
Lemma D_391ec : decode_any W_391ec = Some (Jal 1 207464, 4%Z).
Proof. vm_refl. Qed.

Definition W_391f0 : bv 32 := 0x2e010513.
Lemma F_391f0 : fetch_word Plain.M.loaded_segments (0x39238 : word) = Some W_391f0.
Proof. vm_refl. Qed.
Lemma D_391f0 : decode_any W_391f0 = Some (OpImm ALU_ADD 10 2 736, 4%Z).
Proof. vm_refl. Qed.

Definition W_391f4 : bv 32 := 0x774320ef.
Lemma F_391f4 : fetch_word Plain.M.loaded_segments (0x3923c : word) = Some W_391f4.
Proof. vm_refl. Qed.
Lemma D_391f4 : decode_any W_391f4 = Some (Jal 1 206708, 4%Z).
Proof. vm_refl. Qed.

Definition W_391f8 : bv 32 := 0x37814503.
Lemma F_391f8 : fetch_word Plain.M.loaded_segments (0x39240 : word) = Some W_391f8.
Proof. vm_refl. Qed.
Lemma D_391f8 : decode_any W_391f8 = Some (Load SZ1 false 10 2 888, 4%Z).
Proof. vm_refl. Qed.

Definition W_391fc : bv 32 := 0x00157513.
Lemma F_391fc : fetch_word Plain.M.loaded_segments (0x39244 : word) = Some W_391fc.
Proof. vm_refl. Qed.
Lemma D_391fc : decode_any W_391fc = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_39200 : bv 32 := 0x00050a63.
Lemma F_39200 : fetch_word Plain.M.loaded_segments (0x39248 : word) = Some W_39200.
Proof. vm_refl. Qed.
Lemma D_39200 : decode_any W_39200 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_39204 : bv 32 := 0x37813583.
Lemma F_39204 : fetch_word Plain.M.loaded_segments (0x3924c : word) = Some W_39204.
Proof. vm_refl. Qed.
Lemma D_39204 : decode_any W_39204 = Some (Load SZ8 true 11 2 888, 4%Z).
Proof. vm_refl. Qed.

Definition W_39208 : bv 32 := 0x38813503.
Lemma F_39208 : fetch_word Plain.M.loaded_segments (0x39250 : word) = Some W_39208.
Proof. vm_refl. Qed.
Lemma D_39208 : decode_any W_39208 = Some (Load SZ8 true 10 2 904, 4%Z).
Proof. vm_refl. Qed.

Definition W_3920c : bv 32 := 0xffe5f593.
Lemma F_3920c : fetch_word Plain.M.loaded_segments (0x39254 : word) = Some W_3920c.
Proof. vm_refl. Qed.
Lemma D_3920c : decode_any W_3920c = Some (OpImm ALU_AND 11 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_39210 : bv 32 := 0x36d2a0ef.
Lemma F_39210 : fetch_word Plain.M.loaded_segments (0x39258 : word) = Some W_39210.
Proof. vm_refl. Qed.
Lemma D_39210 : decode_any W_39210 = Some (Jal 1 174956, 4%Z).
Proof. vm_refl. Qed.

Definition W_39214 : bv 32 := 0x00000513.
Lemma F_39214 : fetch_word Plain.M.loaded_segments (0x3925c : word) = Some W_39214.
Proof. vm_refl. Qed.
Lemma D_39214 : decode_any W_39214 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39218 : bv 32 := 0x39813083.
Lemma F_39218 : fetch_word Plain.M.loaded_segments (0x39260 : word) = Some W_39218.
Proof. vm_refl. Qed.
Lemma D_39218 : decode_any W_39218 = Some (Load SZ8 true 1 2 920, 4%Z).
Proof. vm_refl. Qed.

Definition W_3921c : bv 32 := 0x39013403.
Lemma F_3921c : fetch_word Plain.M.loaded_segments (0x39264 : word) = Some W_3921c.
Proof. vm_refl. Qed.
Lemma D_3921c : decode_any W_3921c = Some (Load SZ8 true 8 2 912, 4%Z).
Proof. vm_refl. Qed.

Definition W_39220 : bv 32 := 0x3a010113.
Lemma F_39220 : fetch_word Plain.M.loaded_segments (0x39268 : word) = Some W_39220.
Proof. vm_refl. Qed.
Lemma D_39220 : decode_any W_39220 = Some (OpImm ALU_ADD 2 2 928, 4%Z).
Proof. vm_refl. Qed.

Definition W_39224 : bv 32 := 0x00008067.
Lemma F_39224 : fetch_word Plain.M.loaded_segments (0x3926c : word) = Some W_39224.
Proof. vm_refl. Qed.
Lemma D_39224 : decode_any W_39224 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39228 : bv 32 := 0x00050413.
Lemma F_39228 : fetch_word Plain.M.loaded_segments (0x39270 : word) = Some W_39228.
Proof. vm_refl. Qed.
Lemma D_39228 : decode_any W_39228 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3922c : bv 32 := 0x0180006f.
Lemma F_3922c : fetch_word Plain.M.loaded_segments (0x39274 : word) = Some W_3922c.
Proof. vm_refl. Qed.
Lemma D_3922c : decode_any W_3922c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_39230 : bv 32 := 0x00050413.
Lemma F_39230 : fetch_word Plain.M.loaded_segments (0x39278 : word) = Some W_39230.
Proof. vm_refl. Qed.
Lemma D_39230 : decode_any W_39230 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39234 : bv 32 := 0x0480006f.
Lemma F_39234 : fetch_word Plain.M.loaded_segments (0x3927c : word) = Some W_39234.
Proof. vm_refl. Qed.
Lemma D_39234 : decode_any W_39234 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_39238 : bv 32 := 0x00050413.
Lemma F_39238 : fetch_word Plain.M.loaded_segments (0x39280 : word) = Some W_39238.
Proof. vm_refl. Qed.
Lemma D_39238 : decode_any W_39238 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3923c : bv 32 := 0x02010513.
Lemma F_3923c : fetch_word Plain.M.loaded_segments (0x39284 : word) = Some W_3923c.
Proof. vm_refl. Qed.
Lemma D_3923c : decode_any W_3923c = Some (OpImm ALU_ADD 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_39240 : bv 32 := 0x2a4000ef.
Lemma F_39240 : fetch_word Plain.M.loaded_segments (0x39288 : word) = Some W_39240.
Proof. vm_refl. Qed.
Lemma D_39240 : decode_any W_39240 = Some (Jal 1 676, 4%Z).
Proof. vm_refl. Qed.

Definition W_39244 : bv 32 := 0x23013503.
Lemma F_39244 : fetch_word Plain.M.loaded_segments (0x3928c : word) = Some W_39244.
Proof. vm_refl. Qed.
Lemma D_39244 : decode_any W_39244 = Some (Load SZ8 true 10 2 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_39248 : bv 32 := 0x00050a63.
Lemma F_39248 : fetch_word Plain.M.loaded_segments (0x39290 : word) = Some W_39248.
Proof. vm_refl. Qed.
Lemma D_39248 : decode_any W_39248 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3924c : bv 32 := 0x24013583.
Lemma F_3924c : fetch_word Plain.M.loaded_segments (0x39294 : word) = Some W_3924c.
Proof. vm_refl. Qed.
Lemma D_3924c : decode_any W_3924c = Some (Load SZ8 true 11 2 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_39250 : bv 32 := 0x22a13c23.
Lemma F_39250 : fetch_word Plain.M.loaded_segments (0x39298 : word) = Some W_39250.
Proof. vm_refl. Qed.
Lemma D_39250 : decode_any W_39250 = Some (Store SZ8 2 10 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_39254 : bv 32 := 0x40a585b3.
Lemma F_39254 : fetch_word Plain.M.loaded_segments (0x3929c : word) = Some W_39254.
Proof. vm_refl. Qed.
Lemma D_39254 : decode_any W_39254 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_39258 : bv 32 := 0x3252a0ef.
Lemma F_39258 : fetch_word Plain.M.loaded_segments (0x392a0 : word) = Some W_39258.
Proof. vm_refl. Qed.
Lemma D_39258 : decode_any W_39258 = Some (Jal 1 174884, 4%Z).
Proof. vm_refl. Qed.

Definition W_3925c : bv 32 := 0x25013503.
Lemma F_3925c : fetch_word Plain.M.loaded_segments (0x392a4 : word) = Some W_3925c.
Proof. vm_refl. Qed.
Lemma D_3925c : decode_any W_3925c = Some (Load SZ8 true 10 2 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_39260 : bv 32 := 0x00050a63.
Lemma F_39260 : fetch_word Plain.M.loaded_segments (0x392a8 : word) = Some W_39260.
Proof. vm_refl. Qed.
Lemma D_39260 : decode_any W_39260 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_39264 : bv 32 := 0x26013583.
Lemma F_39264 : fetch_word Plain.M.loaded_segments (0x392ac : word) = Some W_39264.
Proof. vm_refl. Qed.
Lemma D_39264 : decode_any W_39264 = Some (Load SZ8 true 11 2 608, 4%Z).
Proof. vm_refl. Qed.

Definition W_39268 : bv 32 := 0x24a13c23.
Lemma F_39268 : fetch_word Plain.M.loaded_segments (0x392b0 : word) = Some W_39268.
Proof. vm_refl. Qed.
Lemma D_39268 : decode_any W_39268 = Some (Store SZ8 2 10 600, 4%Z).
Proof. vm_refl. Qed.

Definition W_3926c : bv 32 := 0x40a585b3.
Lemma F_3926c : fetch_word Plain.M.loaded_segments (0x392b4 : word) = Some W_3926c.
Proof. vm_refl. Qed.
Lemma D_3926c : decode_any W_3926c = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_39270 : bv 32 := 0x30d2a0ef.
Lemma F_39270 : fetch_word Plain.M.loaded_segments (0x392b8 : word) = Some W_39270.
Proof. vm_refl. Qed.
Lemma D_39270 : decode_any W_39270 = Some (Jal 1 174860, 4%Z).
Proof. vm_refl. Qed.

Definition W_39274 : bv 32 := 0x26810513.
Lemma F_39274 : fetch_word Plain.M.loaded_segments (0x392bc : word) = Some W_39274.
Proof. vm_refl. Qed.
Lemma D_39274 : decode_any W_39274 = Some (OpImm ALU_ADD 10 2 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_39278 : bv 32 := 0x364000ef.
Lemma F_39278 : fetch_word Plain.M.loaded_segments (0x392c0 : word) = Some W_39278.
Proof. vm_refl. Qed.
Lemma D_39278 : decode_any W_39278 = Some (Jal 1 868, 4%Z).
Proof. vm_refl. Qed.

Definition W_3927c : bv 32 := 0x37814503.
Lemma F_3927c : fetch_word Plain.M.loaded_segments (0x392c4 : word) = Some W_3927c.
Proof. vm_refl. Qed.
Lemma D_3927c : decode_any W_3927c = Some (Load SZ1 false 10 2 888, 4%Z).
Proof. vm_refl. Qed.

Definition W_39280 : bv 32 := 0x00157513.
Lemma F_39280 : fetch_word Plain.M.loaded_segments (0x392c8 : word) = Some W_39280.
Proof. vm_refl. Qed.
Lemma D_39280 : decode_any W_39280 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_39284 : bv 32 := 0x00050a63.
Lemma F_39284 : fetch_word Plain.M.loaded_segments (0x392cc : word) = Some W_39284.
Proof. vm_refl. Qed.
Lemma D_39284 : decode_any W_39284 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_39288 : bv 32 := 0x37813583.
Lemma F_39288 : fetch_word Plain.M.loaded_segments (0x392d0 : word) = Some W_39288.
Proof. vm_refl. Qed.
Lemma D_39288 : decode_any W_39288 = Some (Load SZ8 true 11 2 888, 4%Z).
Proof. vm_refl. Qed.

Definition W_3928c : bv 32 := 0x38813503.
Lemma F_3928c : fetch_word Plain.M.loaded_segments (0x392d4 : word) = Some W_3928c.
Proof. vm_refl. Qed.
Lemma D_3928c : decode_any W_3928c = Some (Load SZ8 true 10 2 904, 4%Z).
Proof. vm_refl. Qed.

Definition W_39290 : bv 32 := 0xffe5f593.
Lemma F_39290 : fetch_word Plain.M.loaded_segments (0x392d8 : word) = Some W_39290.
Proof. vm_refl. Qed.
Lemma D_39290 : decode_any W_39290 = Some (OpImm ALU_AND 11 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_39294 : bv 32 := 0x2e92a0ef.
Lemma F_39294 : fetch_word Plain.M.loaded_segments (0x392dc : word) = Some W_39294.
Proof. vm_refl. Qed.
Lemma D_39294 : decode_any W_39294 = Some (Jal 1 174824, 4%Z).
Proof. vm_refl. Qed.

Definition W_39298 : bv 32 := 0x00040513.
Lemma F_39298 : fetch_word Plain.M.loaded_segments (0x392e0 : word) = Some W_39298.
Proof. vm_refl. Qed.
Lemma D_39298 : decode_any W_39298 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3929c : bv 32 := 0x575680ef.
Lemma F_3929c : fetch_word Plain.M.loaded_segments (0x392e4 : word) = Some W_3929c.
Proof. vm_refl. Qed.
Lemma D_3929c : decode_any W_3929c = Some (Jal 1 429428, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_39084_392a0.
Module Ns0_code_r341e0_341e4.
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

Definition W_39350 : bv 32 := 0x00008067.
Lemma F_39350 : fetch_word Plain.M.loaded_segments (0x39398 : word) = Some W_39350.
Proof. vm_refl. Qed.
Lemma D_39350 : decode_any W_39350 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Ns0_code_r341e0_341e4.
