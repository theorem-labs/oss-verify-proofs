(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
Module Na0_code_raf6e0_af6e4.
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

Definition W_d4d2c : bv 32 := 0x00008067.
Lemma F_d4d2c : fetch_word Asan.M.loaded_segments (0xd4d7c : word) = Some W_d4d2c.
Proof. vm_refl. Qed.
Lemma D_d4d2c : decode_any W_d4d2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_raf6e0_af6e4.
Module Na0_code_raf314_af318.
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

Definition W_d2d9c : bv 32 := 0x00008067.
Lemma F_d2d9c : fetch_word Asan.M.loaded_segments (0xd2dec : word) = Some W_d2d9c.
Proof. vm_refl. Qed.
Lemma D_d2d9c : decode_any W_d2d9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_raf314_af318.
Module Na0_code_rb265c_b2660.
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

Definition W_d3498 : bv 32 := 0x00008067.
Lemma F_d3498 : fetch_word Asan.M.loaded_segments (0xd34e8 : word) = Some W_d3498.
Proof. vm_refl. Qed.
Lemma D_d3498 : decode_any W_d3498 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb265c_b2660.
Module Na0_code_rb404c_b4050.
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

Definition W_d5590 : bv 32 := 0x00008067.
Lemma F_d5590 : fetch_word Asan.M.loaded_segments (0xd55e0 : word) = Some W_d5590.
Proof. vm_refl. Qed.
Lemma D_d5590 : decode_any W_d5590 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb404c_b4050.
Module Na0_code_rab014_ab018.
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

Definition W_c142c : bv 32 := 0x00008067.
Lemma F_c142c : fetch_word Asan.M.loaded_segments (0xc147c : word) = Some W_c142c.
Proof. vm_refl. Qed.
Lemma D_c142c : decode_any W_c142c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rab014_ab018.
Module Na0_code_rab0c0_ab0c4.
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

Definition W_c14d8 : bv 32 := 0x00008067.
Lemma F_c14d8 : fetch_word Asan.M.loaded_segments (0xc1528 : word) = Some W_c14d8.
Proof. vm_refl. Qed.
Lemma D_c14d8 : decode_any W_c14d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rab0c0_ab0c4.
Module Na0_code_rab164_ab168.
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

Definition W_c157c : bv 32 := 0x00008067.
Lemma F_c157c : fetch_word Asan.M.loaded_segments (0xc15cc : word) = Some W_c157c.
Proof. vm_refl. Qed.
Lemma D_c157c : decode_any W_c157c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rab164_ab168.
Module Na0_code_r71700_717b4.
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

Definition W_92884 : bv 32 := 0xff010113.
Lemma F_92884 : fetch_word Asan.M.loaded_segments (0x928d4 : word) = Some W_92884.
Proof. vm_refl. Qed.
Lemma D_92884 : decode_any W_92884 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_92888 : bv 32 := 0x00113423.
Lemma F_92888 : fetch_word Asan.M.loaded_segments (0x928d8 : word) = Some W_92888.
Proof. vm_refl. Qed.
Lemma D_92888 : decode_any W_92888 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9288c : bv 32 := 0x00058693.
Lemma F_9288c : fetch_word Asan.M.loaded_segments (0x928dc : word) = Some W_9288c.
Proof. vm_refl. Qed.
Lemma D_9288c : decode_any W_9288c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92890 : bv 32 := 0x00100713.
Lemma F_92890 : fetch_word Asan.M.loaded_segments (0x928e0 : word) = Some W_92890.
Proof. vm_refl. Qed.
Lemma D_92890 : decode_any W_92890 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92894 : bv 32 := 0x02871713.
Lemma F_92894 : fetch_word Asan.M.loaded_segments (0x928e4 : word) = Some W_92894.
Proof. vm_refl. Qed.
Lemma D_92894 : decode_any W_92894 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_92898 : bv 32 := 0x00170593.
Lemma F_92898 : fetch_word Asan.M.loaded_segments (0x928e8 : word) = Some W_92898.
Proof. vm_refl. Qed.
Lemma D_92898 : decode_any W_92898 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9289c : bv 32 := 0x08b6f263.
Lemma F_9289c : fetch_word Asan.M.loaded_segments (0x928ec : word) = Some W_9289c.
Proof. vm_refl. Qed.
Lemma D_9289c : decode_any W_9289c = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_928a0 : bv 32 := 0x00000593.
Lemma F_928a0 : fetch_word Asan.M.loaded_segments (0x928f0 : word) = Some W_928a0.
Proof. vm_refl. Qed.
Lemma D_928a0 : decode_any W_928a0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_928a4 : bv 32 := 0x00d50733.
Lemma F_928a4 : fetch_word Asan.M.loaded_segments (0x928f4 : word) = Some W_928a4.
Proof. vm_refl. Qed.
Lemma D_928a4 : decode_any W_928a4 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_928a8 : bv 32 := 0x00750793.
Lemma F_928a8 : fetch_word Asan.M.loaded_segments (0x928f8 : word) = Some W_928a8.
Proof. vm_refl. Qed.
Lemma D_928a8 : decode_any W_928a8 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_928ac : bv 32 := 0xff87f793.
Lemma F_928ac : fetch_word Asan.M.loaded_segments (0x928fc : word) = Some W_928ac.
Proof. vm_refl. Qed.
Lemma D_928ac : decode_any W_928ac = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_928b0 : bv 32 := 0xff877613.
Lemma F_928b0 : fetch_word Asan.M.loaded_segments (0x92900 : word) = Some W_928b0.
Proof. vm_refl. Qed.
Lemma D_928b0 : decode_any W_928b0 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_928b4 : bv 32 := 0x02f57463.
Lemma F_928b4 : fetch_word Asan.M.loaded_segments (0x92904 : word) = Some W_928b4.
Proof. vm_refl. Qed.
Lemma D_928b4 : decode_any W_928b4 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_928b8 : bv 32 := 0x02068263.
Lemma F_928b8 : fetch_word Asan.M.loaded_segments (0x92908 : word) = Some W_928b8.
Proof. vm_refl. Qed.
Lemma D_928b8 : decode_any W_928b8 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_928bc : bv 32 := 0x00000593.
Lemma F_928bc : fetch_word Asan.M.loaded_segments (0x9290c : word) = Some W_928bc.
Proof. vm_refl. Qed.
Lemma D_928bc : decode_any W_928bc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_928c0 : bv 32 := 0x00150693.
Lemma F_928c0 : fetch_word Asan.M.loaded_segments (0x92910 : word) = Some W_928c0.
Proof. vm_refl. Qed.
Lemma D_928c0 : decode_any W_928c0 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_928c4 : bv 32 := 0x00068813.
Lemma F_928c4 : fetch_word Asan.M.loaded_segments (0x92914 : word) = Some W_928c4.
Proof. vm_refl. Qed.
Lemma D_928c4 : decode_any W_928c4 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_928c8 : bv 32 := 0xfff6c683.
Lemma F_928c8 : fetch_word Asan.M.loaded_segments (0x92918 : word) = Some W_928c8.
Proof. vm_refl. Qed.
Lemma D_928c8 : decode_any W_928c8 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_928cc : bv 32 := 0x00d5e5b3.
Lemma F_928cc : fetch_word Asan.M.loaded_segments (0x9291c : word) = Some W_928cc.
Proof. vm_refl. Qed.
Lemma D_928cc : decode_any W_928cc = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_928d0 : bv 32 := 0x00f87663.
Lemma F_928d0 : fetch_word Asan.M.loaded_segments (0x92920 : word) = Some W_928d0.
Proof. vm_refl. Qed.
Lemma D_928d0 : decode_any W_928d0 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_928d4 : bv 32 := 0x00180693.
Lemma F_928d4 : fetch_word Asan.M.loaded_segments (0x92924 : word) = Some W_928d4.
Proof. vm_refl. Qed.
Lemma D_928d4 : decode_any W_928d4 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_928d8 : bv 32 := 0xfee866e3.
Lemma F_928d8 : fetch_word Asan.M.loaded_segments (0x92928 : word) = Some W_928d8.
Proof. vm_refl. Qed.
Lemma D_928d8 : decode_any W_928d8 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_928dc : bv 32 := 0x00c7fa63.
Lemma F_928dc : fetch_word Asan.M.loaded_segments (0x9292c : word) = Some W_928dc.
Proof. vm_refl. Qed.
Lemma D_928dc : decode_any W_928dc = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_928e0 : bv 32 := 0x0007b683.
Lemma F_928e0 : fetch_word Asan.M.loaded_segments (0x92930 : word) = Some W_928e0.
Proof. vm_refl. Qed.
Lemma D_928e0 : decode_any W_928e0 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_928e4 : bv 32 := 0x00878793.
Lemma F_928e4 : fetch_word Asan.M.loaded_segments (0x92934 : word) = Some W_928e4.
Proof. vm_refl. Qed.
Lemma D_928e4 : decode_any W_928e4 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_928e8 : bv 32 := 0x00b6e5b3.
Lemma F_928e8 : fetch_word Asan.M.loaded_segments (0x92938 : word) = Some W_928e8.
Proof. vm_refl. Qed.
Lemma D_928e8 : decode_any W_928e8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_928ec : bv 32 := 0xfec7eae3.
Lemma F_928ec : fetch_word Asan.M.loaded_segments (0x9293c : word) = Some W_928ec.
Proof. vm_refl. Qed.
Lemma D_928ec : decode_any W_928ec = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_928f0 : bv 32 := 0x02a66063.
Lemma F_928f0 : fetch_word Asan.M.loaded_segments (0x92940 : word) = Some W_928f0.
Proof. vm_refl. Qed.
Lemma D_928f0 : decode_any W_928f0 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_928f4 : bv 32 := 0x00e67e63.
Lemma F_928f4 : fetch_word Asan.M.loaded_segments (0x92944 : word) = Some W_928f4.
Proof. vm_refl. Qed.
Lemma D_928f4 : decode_any W_928f4 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_928f8 : bv 32 := 0x40c70733.
Lemma F_928f8 : fetch_word Asan.M.loaded_segments (0x92948 : word) = Some W_928f8.
Proof. vm_refl. Qed.
Lemma D_928f8 : decode_any W_928f8 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_928fc : bv 32 := 0x00064503.
Lemma F_928fc : fetch_word Asan.M.loaded_segments (0x9294c : word) = Some W_928fc.
Proof. vm_refl. Qed.
Lemma D_928fc : decode_any W_928fc = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92900 : bv 32 := 0xfff70713.
Lemma F_92900 : fetch_word Asan.M.loaded_segments (0x92950 : word) = Some W_92900.
Proof. vm_refl. Qed.
Lemma D_92900 : decode_any W_92900 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_92904 : bv 32 := 0x00a5e5b3.
Lemma F_92904 : fetch_word Asan.M.loaded_segments (0x92954 : word) = Some W_92904.
Proof. vm_refl. Qed.
Lemma D_92904 : decode_any W_92904 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_92908 : bv 32 := 0x00160613.
Lemma F_92908 : fetch_word Asan.M.loaded_segments (0x92958 : word) = Some W_92908.
Proof. vm_refl. Qed.
Lemma D_92908 : decode_any W_92908 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9290c : bv 32 := 0xfe0718e3.
Lemma F_9290c : fetch_word Asan.M.loaded_segments (0x9295c : word) = Some W_9290c.
Proof. vm_refl. Qed.
Lemma D_9290c : decode_any W_9290c = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_92910 : bv 32 := 0x0015b513.
Lemma F_92910 : fetch_word Asan.M.loaded_segments (0x92960 : word) = Some W_92910.
Proof. vm_refl. Qed.
Lemma D_92910 : decode_any W_92910 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92914 : bv 32 := 0x00813083.
Lemma F_92914 : fetch_word Asan.M.loaded_segments (0x92964 : word) = Some W_92914.
Proof. vm_refl. Qed.
Lemma D_92914 : decode_any W_92914 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92918 : bv 32 := 0x01010113.
Lemma F_92918 : fetch_word Asan.M.loaded_segments (0x92968 : word) = Some W_92918.
Proof. vm_refl. Qed.
Lemma D_92918 : decode_any W_92918 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9291c : bv 32 := 0x00008067.
Lemma F_9291c : fetch_word Asan.M.loaded_segments (0x9296c : word) = Some W_9291c.
Proof. vm_refl. Qed.
Lemma D_9291c : decode_any W_9291c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r71700_717b4.
Module Na0_code_r61770_61ab4.
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

Definition W_82398 : bv 32 := 0xfc010113.
Lemma F_82398 : fetch_word Asan.M.loaded_segments (0x823e8 : word) = Some W_82398.
Proof. vm_refl. Qed.
Lemma D_82398 : decode_any W_82398 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_8239c : bv 32 := 0x02113c23.
Lemma F_8239c : fetch_word Asan.M.loaded_segments (0x823ec : word) = Some W_8239c.
Proof. vm_refl. Qed.
Lemma D_8239c : decode_any W_8239c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_823a0 : bv 32 := 0x02813823.
Lemma F_823a0 : fetch_word Asan.M.loaded_segments (0x823f0 : word) = Some W_823a0.
Proof. vm_refl. Qed.
Lemma D_823a0 : decode_any W_823a0 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_823a4 : bv 32 := 0x02913423.
Lemma F_823a4 : fetch_word Asan.M.loaded_segments (0x823f4 : word) = Some W_823a4.
Proof. vm_refl. Qed.
Lemma D_823a4 : decode_any W_823a4 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_823a8 : bv 32 := 0x03213023.
Lemma F_823a8 : fetch_word Asan.M.loaded_segments (0x823f8 : word) = Some W_823a8.
Proof. vm_refl. Qed.
Lemma D_823a8 : decode_any W_823a8 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_823ac : bv 32 := 0x01313c23.
Lemma F_823ac : fetch_word Asan.M.loaded_segments (0x823fc : word) = Some W_823ac.
Proof. vm_refl. Qed.
Lemma D_823ac : decode_any W_823ac = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_823b0 : bv 32 := 0x01413823.
Lemma F_823b0 : fetch_word Asan.M.loaded_segments (0x82400 : word) = Some W_823b0.
Proof. vm_refl. Qed.
Lemma D_823b0 : decode_any W_823b0 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_823b4 : bv 32 := 0x01513423.
Lemma F_823b4 : fetch_word Asan.M.loaded_segments (0x82404 : word) = Some W_823b4.
Proof. vm_refl. Qed.
Lemma D_823b4 : decode_any W_823b4 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_823b8 : bv 32 := 0x14058c63.
Lemma F_823b8 : fetch_word Asan.M.loaded_segments (0x82408 : word) = Some W_823b8.
Proof. vm_refl. Qed.
Lemma D_823b8 : decode_any W_823b8 = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_823bc : bv 32 := 0x00058493.
Lemma F_823bc : fetch_word Asan.M.loaded_segments (0x8240c : word) = Some W_823bc.
Proof. vm_refl. Qed.
Lemma D_823bc : decode_any W_823bc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_823c0 : bv 32 := 0x00050413.
Lemma F_823c0 : fetch_word Asan.M.loaded_segments (0x82410 : word) = Some W_823c0.
Proof. vm_refl. Qed.
Lemma D_823c0 : decode_any W_823c0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_823c4 : bv 32 := 0x000d5517.
Lemma F_823c4 : fetch_word Asan.M.loaded_segments (0x82414 : word) = Some W_823c4.
Proof. vm_refl. Qed.
Lemma D_823c4 : decode_any W_823c4 = Some (Auipc 10 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_823c8 : bv 32 := 0x98453a83.
Lemma F_823c8 : fetch_word Asan.M.loaded_segments (0x82418 : word) = Some W_823c8.
Proof. vm_refl. Qed.
Lemma D_823c8 : decode_any W_823c8 = Some (Load SZ8 true 21 10 2436, 4%Z).
Proof. vm_refl. Qed.

Definition W_823cc : bv 32 := 0x000ab583.
Lemma F_823cc : fetch_word Asan.M.loaded_segments (0x8241c : word) = Some W_823cc.
Proof. vm_refl. Qed.
Lemma D_823cc : decode_any W_823cc = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_823d0 : bv 32 := 0xfff58513.
Lemma F_823d0 : fetch_word Asan.M.loaded_segments (0x82420 : word) = Some W_823d0.
Proof. vm_refl. Qed.
Lemma D_823d0 : decode_any W_823d0 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_823d4 : bv 32 := 0x00a5b633.
Lemma F_823d4 : fetch_word Asan.M.loaded_segments (0x82424 : word) = Some W_823d4.
Proof. vm_refl. Qed.
Lemma D_823d4 : decode_any W_823d4 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_823d8 : bv 32 := 0xfff60613.
Lemma F_823d8 : fetch_word Asan.M.loaded_segments (0x82428 : word) = Some W_823d8.
Proof. vm_refl. Qed.
Lemma D_823d8 : decode_any W_823d8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_823dc : bv 32 := 0x00a67633.
Lemma F_823dc : fetch_word Asan.M.loaded_segments (0x8242c : word) = Some W_823dc.
Proof. vm_refl. Qed.
Lemma D_823dc : decode_any W_823dc = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_823e0 : bv 32 := 0x04867263.
Lemma F_823e0 : fetch_word Asan.M.loaded_segments (0x82430 : word) = Some W_823e0.
Proof. vm_refl. Qed.
Lemma D_823e0 : decode_any W_823e0 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_823e4 : bv 32 := 0x000d5697.
Lemma F_823e4 : fetch_word Asan.M.loaded_segments (0x82434 : word) = Some W_823e4.
Proof. vm_refl. Qed.
Lemma D_823e4 : decode_any W_823e4 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_823e8 : bv 32 := 0x96c6b683.
Lemma F_823e8 : fetch_word Asan.M.loaded_segments (0x82438 : word) = Some W_823e8.
Proof. vm_refl. Qed.
Lemma D_823e8 : decode_any W_823e8 = Some (Load SZ8 true 13 13 2412, 4%Z).
Proof. vm_refl. Qed.

Definition W_823ec : bv 32 := 0x000d5717.
Lemma F_823ec : fetch_word Asan.M.loaded_segments (0x8243c : word) = Some W_823ec.
Proof. vm_refl. Qed.
Lemma D_823ec : decode_any W_823ec = Some (Auipc 14 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_823f0 : bv 32 := 0x96c73703.
Lemma F_823f0 : fetch_word Asan.M.loaded_segments (0x82440 : word) = Some W_823f0.
Proof. vm_refl. Qed.
Lemma D_823f0 : decode_any W_823f0 = Some (Load SZ8 true 14 14 2412, 4%Z).
Proof. vm_refl. Qed.

Definition W_823f4 : bv 32 := 0x0006b803.
Lemma F_823f4 : fetch_word Asan.M.loaded_segments (0x82444 : word) = Some W_823f4.
Proof. vm_refl. Qed.
Lemma D_823f4 : decode_any W_823f4 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_823f8 : bv 32 := 0x00073683.
Lemma F_823f8 : fetch_word Asan.M.loaded_segments (0x82448 : word) = Some W_823f8.
Proof. vm_refl. Qed.
Lemma D_823f8 : decode_any W_823f8 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_823fc : bv 32 := 0xfff80793.
Lemma F_823fc : fetch_word Asan.M.loaded_segments (0x8244c : word) = Some W_823fc.
Proof. vm_refl. Qed.
Lemma D_823fc : decode_any W_823fc = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82400 : bv 32 := 0x0087f463.
Lemma F_82400 : fetch_word Asan.M.loaded_segments (0x82450 : word) = Some W_82400.
Proof. vm_refl. Qed.
Lemma D_82400 : decode_any W_82400 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82408 : bv 32 := 0x000d5717.
Lemma F_82408 : fetch_word Asan.M.loaded_segments (0x82458 : word) = Some W_82408.
Proof. vm_refl. Qed.
Lemma D_82408 : decode_any W_82408 = Some (Auipc 14 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_8240c : bv 32 := 0x95873703.
Lemma F_8240c : fetch_word Asan.M.loaded_segments (0x8245c : word) = Some W_8240c.
Proof. vm_refl. Qed.
Lemma D_8240c : decode_any W_8240c = Some (Load SZ8 true 14 14 2392, 4%Z).
Proof. vm_refl. Qed.

Definition W_82410 : bv 32 := 0x00073283.
Lemma F_82410 : fetch_word Asan.M.loaded_segments (0x82460 : word) = Some W_82410.
Proof. vm_refl. Qed.
Lemma D_82410 : decode_any W_82410 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82414 : bv 32 := 0x0032d713.
Lemma F_82414 : fetch_word Asan.M.loaded_segments (0x82464 : word) = Some W_82414.
Proof. vm_refl. Qed.
Lemma D_82414 : decode_any W_82414 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82418 : bv 32 := 0x00b708b3.
Lemma F_82418 : fetch_word Asan.M.loaded_segments (0x82468 : word) = Some W_82418.
Proof. vm_refl. Qed.
Lemma D_82418 : decode_any W_82418 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8241c : bv 32 := 0x1282e063.
Lemma F_8241c : fetch_word Asan.M.loaded_segments (0x8246c : word) = Some W_8241c.
Proof. vm_refl. Qed.
Lemma D_8241c : decode_any W_8241c = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_82420 : bv 32 := 0x1088fe63.
Lemma F_82420 : fetch_word Asan.M.loaded_segments (0x82470 : word) = Some W_82420.
Proof. vm_refl. Qed.
Lemma D_82420 : decode_any W_82420 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_82424 : bv 32 := 0x00848933.
Lemma F_82424 : fetch_word Asan.M.loaded_segments (0x82474 : word) = Some W_82424.
Proof. vm_refl. Qed.
Lemma D_82424 : decode_any W_82424 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82428 : bv 32 := 0x05267263.
Lemma F_82428 : fetch_word Asan.M.loaded_segments (0x82478 : word) = Some W_82428.
Proof. vm_refl. Qed.
Lemma D_82428 : decode_any W_82428 = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_8242c : bv 32 := 0x000d5617.
Lemma F_8242c : fetch_word Asan.M.loaded_segments (0x8247c : word) = Some W_8242c.
Proof. vm_refl. Qed.
Lemma D_8242c : decode_any W_8242c = Some (Auipc 12 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_82430 : bv 32 := 0x92463603.
Lemma F_82430 : fetch_word Asan.M.loaded_segments (0x82480 : word) = Some W_82430.
Proof. vm_refl. Qed.
Lemma D_82430 : decode_any W_82430 = Some (Load SZ8 true 12 12 2340, 4%Z).
Proof. vm_refl. Qed.

Definition W_82434 : bv 32 := 0x000d5697.
Lemma F_82434 : fetch_word Asan.M.loaded_segments (0x82484 : word) = Some W_82434.
Proof. vm_refl. Qed.
Lemma D_82434 : decode_any W_82434 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_82438 : bv 32 := 0x9246b683.
Lemma F_82438 : fetch_word Asan.M.loaded_segments (0x82488 : word) = Some W_82438.
Proof. vm_refl. Qed.
Lemma D_82438 : decode_any W_82438 = Some (Load SZ8 true 13 13 2340, 4%Z).
Proof. vm_refl. Qed.

Definition W_8243c : bv 32 := 0x00063783.
Lemma F_8243c : fetch_word Asan.M.loaded_segments (0x8248c : word) = Some W_8243c.
Proof. vm_refl. Qed.
Lemma D_8243c : decode_any W_8243c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82440 : bv 32 := 0x0006b603.
Lemma F_82440 : fetch_word Asan.M.loaded_segments (0x82490 : word) = Some W_82440.
Proof. vm_refl. Qed.
Lemma D_82440 : decode_any W_82440 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82444 : bv 32 := 0xfff78713.
Lemma F_82444 : fetch_word Asan.M.loaded_segments (0x82494 : word) = Some W_82444.
Proof. vm_refl. Qed.
Lemma D_82444 : decode_any W_82444 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_82448 : bv 32 := 0x01277463.
Lemma F_82448 : fetch_word Asan.M.loaded_segments (0x82498 : word) = Some W_82448.
Proof. vm_refl. Qed.
Lemma D_82448 : decode_any W_82448 = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82450 : bv 32 := 0x000d5697.
Lemma F_82450 : fetch_word Asan.M.loaded_segments (0x824a0 : word) = Some W_82450.
Proof. vm_refl. Qed.
Lemma D_82450 : decode_any W_82450 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_82454 : bv 32 := 0x9106b683.
Lemma F_82454 : fetch_word Asan.M.loaded_segments (0x824a4 : word) = Some W_82454.
Proof. vm_refl. Qed.
Lemma D_82454 : decode_any W_82454 = Some (Load SZ8 true 13 13 2320, 4%Z).
Proof. vm_refl. Qed.

Definition W_82458 : bv 32 := 0x0006b883.
Lemma F_82458 : fetch_word Asan.M.loaded_segments (0x824a8 : word) = Some W_82458.
Proof. vm_refl. Qed.
Lemma D_82458 : decode_any W_82458 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8245c : bv 32 := 0x0038d693.
Lemma F_8245c : fetch_word Asan.M.loaded_segments (0x824ac : word) = Some W_8245c.
Proof. vm_refl. Qed.
Lemma D_8245c : decode_any W_8245c = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82460 : bv 32 := 0x00b68833.
Lemma F_82460 : fetch_word Asan.M.loaded_segments (0x824b0 : word) = Some W_82460.
Proof. vm_refl. Qed.
Lemma D_82460 : decode_any W_82460 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_82464 : bv 32 := 0x1328e463.
Lemma F_82464 : fetch_word Asan.M.loaded_segments (0x824b4 : word) = Some W_82464.
Proof. vm_refl. Qed.
Lemma D_82464 : decode_any W_82464 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_82468 : bv 32 := 0x13287263.
Lemma F_82468 : fetch_word Asan.M.loaded_segments (0x824b8 : word) = Some W_82468.
Proof. vm_refl. Qed.
Lemma D_82468 : decode_any W_82468 = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_8246c : bv 32 := 0x23247863.
Lemma F_8246c : fetch_word Asan.M.loaded_segments (0x824bc : word) = Some W_8246c.
Proof. vm_refl. Qed.
Lemma D_8246c : decode_any W_8246c = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_82470 : bv 32 := 0x00740513.
Lemma F_82470 : fetch_word Asan.M.loaded_segments (0x824c0 : word) = Some W_82470.
Proof. vm_refl. Qed.
Lemma D_82470 : decode_any W_82470 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82474 : bv 32 := 0xff857513.
Lemma F_82474 : fetch_word Asan.M.loaded_segments (0x824c4 : word) = Some W_82474.
Proof. vm_refl. Qed.
Lemma D_82474 : decode_any W_82474 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82478 : bv 32 := 0xff897a13.
Lemma F_82478 : fetch_word Asan.M.loaded_segments (0x824c8 : word) = Some W_82478.
Proof. vm_refl. Qed.
Lemma D_82478 : decode_any W_82478 = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_8247c : bv 32 := 0xa91ff0ef.
Lemma F_8247c : fetch_word Asan.M.loaded_segments (0x824cc : word) = Some W_8247c.
Proof. vm_refl. Qed.
Lemma D_8247c : decode_any W_8247c = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

Definition W_82480 : bv 32 := 0x00050993.
Lemma F_82480 : fetch_word Asan.M.loaded_segments (0x824d0 : word) = Some W_82480.
Proof. vm_refl. Qed.
Lemma D_82480 : decode_any W_82480 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82484 : bv 32 := 0x000a0513.
Lemma F_82484 : fetch_word Asan.M.loaded_segments (0x824d4 : word) = Some W_82484.
Proof. vm_refl. Qed.
Lemma D_82484 : decode_any W_82484 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82488 : bv 32 := 0xa85ff0ef.
Lemma F_82488 : fetch_word Asan.M.loaded_segments (0x824d8 : word) = Some W_82488.
Proof. vm_refl. Qed.
Lemma D_82488 : decode_any W_82488 = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

Definition W_8248c : bv 32 := 0x000ab583.
Lemma F_8248c : fetch_word Asan.M.loaded_segments (0x824dc : word) = Some W_8248c.
Proof. vm_refl. Qed.
Lemma D_8248c : decode_any W_8248c = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82490 : bv 32 := 0x00345613.
Lemma F_82490 : fetch_word Asan.M.loaded_segments (0x824e0 : word) = Some W_82490.
Proof. vm_refl. Qed.
Lemma D_82490 : decode_any W_82490 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82494 : bv 32 := 0x00c58633.
Lemma F_82494 : fetch_word Asan.M.loaded_segments (0x824e4 : word) = Some W_82494.
Proof. vm_refl. Qed.
Lemma D_82494 : decode_any W_82494 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82498 : bv 32 := 0x00060603.
Lemma F_82498 : fetch_word Asan.M.loaded_segments (0x824e8 : word) = Some W_82498.
Proof. vm_refl. Qed.
Lemma D_82498 : decode_any W_82498 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8249c : bv 32 := 0x00060663.
Lemma F_8249c : fetch_word Asan.M.loaded_segments (0x824ec : word) = Some W_8249c.
Proof. vm_refl. Qed.
Lemma D_8249c : decode_any W_8249c = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_824a0 : bv 32 := 0x00747693.
Lemma F_824a0 : fetch_word Asan.M.loaded_segments (0x824f0 : word) = Some W_824a0.
Proof. vm_refl. Qed.
Lemma D_824a0 : decode_any W_824a0 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_824a4 : bv 32 := 0x02c6d063.
Lemma F_824a4 : fetch_word Asan.M.loaded_segments (0x824f4 : word) = Some W_824a4.
Proof. vm_refl. Qed.
Lemma D_824a4 : decode_any W_824a4 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_824a8 : bv 32 := 0xfff90913.
Lemma F_824a8 : fetch_word Asan.M.loaded_segments (0x824f8 : word) = Some W_824a8.
Proof. vm_refl. Qed.
Lemma D_824a8 : decode_any W_824a8 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_824ac : bv 32 := 0x00395613.
Lemma F_824ac : fetch_word Asan.M.loaded_segments (0x824fc : word) = Some W_824ac.
Proof. vm_refl. Qed.
Lemma D_824ac : decode_any W_824ac = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_824b0 : bv 32 := 0x00c585b3.
Lemma F_824b0 : fetch_word Asan.M.loaded_segments (0x82500 : word) = Some W_824b0.
Proof. vm_refl. Qed.
Lemma D_824b0 : decode_any W_824b0 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_824b4 : bv 32 := 0x00058583.
Lemma F_824b4 : fetch_word Asan.M.loaded_segments (0x82504 : word) = Some W_824b4.
Proof. vm_refl. Qed.
Lemma D_824b4 : decode_any W_824b4 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_824b8 : bv 32 := 0x04058263.
Lemma F_824b8 : fetch_word Asan.M.loaded_segments (0x82508 : word) = Some W_824b8.
Proof. vm_refl. Qed.
Lemma D_824b8 : decode_any W_824b8 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_824bc : bv 32 := 0x00797613.
Lemma F_824bc : fetch_word Asan.M.loaded_segments (0x8250c : word) = Some W_824bc.
Proof. vm_refl. Qed.
Lemma D_824bc : decode_any W_824bc = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_824c0 : bv 32 := 0x02b64e63.
Lemma F_824c0 : fetch_word Asan.M.loaded_segments (0x82510 : word) = Some W_824c0.
Proof. vm_refl. Qed.
Lemma D_824c0 : decode_any W_824c0 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_824fc : bv 32 := 0x00a9fa63.
Lemma F_824fc : fetch_word Asan.M.loaded_segments (0x8254c : word) = Some W_824fc.
Proof. vm_refl. Qed.
Lemma D_824fc : decode_any W_824fc = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_82500 : bv 32 := 0x413505b3.
Lemma F_82500 : fetch_word Asan.M.loaded_segments (0x82550 : word) = Some W_82500.
Proof. vm_refl. Qed.
Lemma D_82500 : decode_any W_82500 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_82504 : bv 32 := 0x00098513.
Lemma F_82504 : fetch_word Asan.M.loaded_segments (0x82554 : word) = Some W_82504.
Proof. vm_refl. Qed.
Lemma D_82504 : decode_any W_82504 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82508 : bv 32 := 0x37c100ef.
Lemma F_82508 : fetch_word Asan.M.loaded_segments (0x82558 : word) = Some W_82508.
Proof. vm_refl. Qed.
Lemma D_82508 : decode_any W_82508 = Some (Jal 1 66428, 4%Z).
Proof. vm_refl. Qed.

Definition W_8250c : bv 32 := 0xfa050ce3.
Lemma F_8250c : fetch_word Asan.M.loaded_segments (0x8255c : word) = Some W_8250c.
Proof. vm_refl. Qed.
Lemma D_8250c : decode_any W_8250c = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

Definition W_82510 : bv 32 := 0x00000413.
Lemma F_82510 : fetch_word Asan.M.loaded_segments (0x82560 : word) = Some W_82510.
Proof. vm_refl. Qed.
Lemma D_82510 : decode_any W_82510 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82514 : bv 32 := 0x00040513.
Lemma F_82514 : fetch_word Asan.M.loaded_segments (0x82564 : word) = Some W_82514.
Proof. vm_refl. Qed.
Lemma D_82514 : decode_any W_82514 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82518 : bv 32 := 0x03813083.
Lemma F_82518 : fetch_word Asan.M.loaded_segments (0x82568 : word) = Some W_82518.
Proof. vm_refl. Qed.
Lemma D_82518 : decode_any W_82518 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8251c : bv 32 := 0x03013403.
Lemma F_8251c : fetch_word Asan.M.loaded_segments (0x8256c : word) = Some W_8251c.
Proof. vm_refl. Qed.
Lemma D_8251c : decode_any W_8251c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82520 : bv 32 := 0x02813483.
Lemma F_82520 : fetch_word Asan.M.loaded_segments (0x82570 : word) = Some W_82520.
Proof. vm_refl. Qed.
Lemma D_82520 : decode_any W_82520 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82524 : bv 32 := 0x02013903.
Lemma F_82524 : fetch_word Asan.M.loaded_segments (0x82574 : word) = Some W_82524.
Proof. vm_refl. Qed.
Lemma D_82524 : decode_any W_82524 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_82528 : bv 32 := 0x01813983.
Lemma F_82528 : fetch_word Asan.M.loaded_segments (0x82578 : word) = Some W_82528.
Proof. vm_refl. Qed.
Lemma D_82528 : decode_any W_82528 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8252c : bv 32 := 0x01013a03.
Lemma F_8252c : fetch_word Asan.M.loaded_segments (0x8257c : word) = Some W_8252c.
Proof. vm_refl. Qed.
Lemma D_8252c : decode_any W_8252c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_82530 : bv 32 := 0x00813a83.
Lemma F_82530 : fetch_word Asan.M.loaded_segments (0x82580 : word) = Some W_82530.
Proof. vm_refl. Qed.
Lemma D_82530 : decode_any W_82530 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82534 : bv 32 := 0x04010113.
Lemma F_82534 : fetch_word Asan.M.loaded_segments (0x82584 : word) = Some W_82534.
Proof. vm_refl. Qed.
Lemma D_82534 : decode_any W_82534 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_82538 : bv 32 := 0x00008067.
Lemma F_82538 : fetch_word Asan.M.loaded_segments (0x82588 : word) = Some W_82538.
Proof. vm_refl. Qed.
Lemma D_82538 : decode_any W_82538 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r61770_61ab4.
Module Na0_code_r4da8c_4da94.
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

Definition W_6a244 : bv 32 := 0x0e40006f.
Lemma F_6a244 : fetch_word Asan.M.loaded_segments (0x6a294 : word) = Some W_6a244.
Proof. vm_refl. Qed.
Lemma D_6a244 : decode_any W_6a244 = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r4da8c_4da94.
Module Na0_code_r4db30_4ddc4.
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

Definition W_6a328 : bv 32 := 0x81010113.
Lemma F_6a328 : fetch_word Asan.M.loaded_segments (0x6a378 : word) = Some W_6a328.
Proof. vm_refl. Qed.
Lemma D_6a328 : decode_any W_6a328 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a32c : bv 32 := 0x7e113423.
Lemma F_6a32c : fetch_word Asan.M.loaded_segments (0x6a37c : word) = Some W_6a32c.
Proof. vm_refl. Qed.
Lemma D_6a32c : decode_any W_6a32c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a330 : bv 32 := 0x7e813023.
Lemma F_6a330 : fetch_word Asan.M.loaded_segments (0x6a380 : word) = Some W_6a330.
Proof. vm_refl. Qed.
Lemma D_6a330 : decode_any W_6a330 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a334 : bv 32 := 0x7c913c23.
Lemma F_6a334 : fetch_word Asan.M.loaded_segments (0x6a384 : word) = Some W_6a334.
Proof. vm_refl. Qed.
Lemma D_6a334 : decode_any W_6a334 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a338 : bv 32 := 0x7d213823.
Lemma F_6a338 : fetch_word Asan.M.loaded_segments (0x6a388 : word) = Some W_6a338.
Proof. vm_refl. Qed.
Lemma D_6a338 : decode_any W_6a338 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a33c : bv 32 := 0x7d313423.
Lemma F_6a33c : fetch_word Asan.M.loaded_segments (0x6a38c : word) = Some W_6a33c.
Proof. vm_refl. Qed.
Lemma D_6a33c : decode_any W_6a33c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a340 : bv 32 := 0x7d413023.
Lemma F_6a340 : fetch_word Asan.M.loaded_segments (0x6a390 : word) = Some W_6a340.
Proof. vm_refl. Qed.
Lemma D_6a340 : decode_any W_6a340 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a344 : bv 32 := 0x7b513c23.
Lemma F_6a344 : fetch_word Asan.M.loaded_segments (0x6a394 : word) = Some W_6a344.
Proof. vm_refl. Qed.
Lemma D_6a344 : decode_any W_6a344 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a348 : bv 32 := 0x7b613823.
Lemma F_6a348 : fetch_word Asan.M.loaded_segments (0x6a398 : word) = Some W_6a348.
Proof. vm_refl. Qed.
Lemma D_6a348 : decode_any W_6a348 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a34c : bv 32 := 0x7f010413.
Lemma F_6a34c : fetch_word Asan.M.loaded_segments (0x6a39c : word) = Some W_6a34c.
Proof. vm_refl. Qed.
Lemma D_6a34c : decode_any W_6a34c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a350 : bv 32 := 0xf9010113.
Lemma F_6a350 : fetch_word Asan.M.loaded_segments (0x6a3a0 : word) = Some W_6a350.
Proof. vm_refl. Qed.
Lemma D_6a350 : decode_any W_6a350 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a354 : bv 32 := 0x00050913.
Lemma F_6a354 : fetch_word Asan.M.loaded_segments (0x6a3a4 : word) = Some W_6a354.
Proof. vm_refl. Qed.
Lemma D_6a354 : decode_any W_6a354 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a358 : bv 32 := 0x5551c0ef.
Lemma F_6a358 : fetch_word Asan.M.loaded_segments (0x6a3a8 : word) = Some W_6a358.
Proof. vm_refl. Qed.
Lemma D_6a358 : decode_any W_6a358 = Some (Jal 1 118100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a35c : bv 32 := 0x0a050863.
Lemma F_6a35c : fetch_word Asan.M.loaded_segments (0x6a3ac : word) = Some W_6a35c.
Proof. vm_refl. Qed.
Lemma D_6a35c : decode_any W_6a35c = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a360 : bv 32 := 0x45d1d0ef.
Lemma F_6a360 : fetch_word Asan.M.loaded_segments (0x6a3b0 : word) = Some W_6a360.
Proof. vm_refl. Qed.
Lemma D_6a360 : decode_any W_6a360 = Some (Jal 1 121948, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a364 : bv 32 := 0x000ee597.
Lemma F_6a364 : fetch_word Asan.M.loaded_segments (0x6a3b4 : word) = Some W_6a364.
Proof. vm_refl. Qed.
Lemma D_6a364 : decode_any W_6a364 = Some (Auipc 11 238, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a368 : bv 32 := 0x7fc5b583.
Lemma F_6a368 : fetch_word Asan.M.loaded_segments (0x6a3b8 : word) = Some W_6a368.
Proof. vm_refl. Qed.
Lemma D_6a368 : decode_any W_6a368 = Some (Load SZ8 true 11 11 2044, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a36c : bv 32 := 0x00050493.
Lemma F_6a36c : fetch_word Asan.M.loaded_segments (0x6a3bc : word) = Some W_6a36c.
Proof. vm_refl. Qed.
Lemma D_6a36c : decode_any W_6a36c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a370 : bv 32 := 0x00090513.
Lemma F_6a370 : fetch_word Asan.M.loaded_segments (0x6a3c0 : word) = Some W_6a370.
Proof. vm_refl. Qed.
Lemma D_6a370 : decode_any W_6a370 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a374 : bv 32 := 0x000580e7.
Lemma F_6a374 : fetch_word Asan.M.loaded_segments (0x6a3c4 : word) = Some W_6a374.
Proof. vm_refl. Qed.
Lemma D_6a374 : decode_any W_6a374 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a378 : bv 32 := 0x06048463.
Lemma F_6a378 : fetch_word Asan.M.loaded_segments (0x6a3c8 : word) = Some W_6a378.
Proof. vm_refl. Qed.
Lemma D_6a378 : decode_any W_6a378 = Some (Branch BC_EQ 9 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a37c : bv 32 := 0x000ed597.
Lemma F_6a37c : fetch_word Asan.M.loaded_segments (0x6a3cc : word) = Some W_6a37c.
Proof. vm_refl. Qed.
Lemma D_6a37c : decode_any W_6a37c = Some (Auipc 11 237, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a380 : bv 32 := 0x9bc5b983.
Lemma F_6a380 : fetch_word Asan.M.loaded_segments (0x6a3d0 : word) = Some W_6a380.
Proof. vm_refl. Qed.
Lemma D_6a380 : decode_any W_6a380 = Some (Load SZ8 true 19 11 2492, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a384 : bv 32 := 0x0fb9c583.
Lemma F_6a384 : fetch_word Asan.M.loaded_segments (0x6a3d4 : word) = Some W_6a384.
Proof. vm_refl. Qed.
Lemma D_6a384 : decode_any W_6a384 = Some (Load SZ1 false 11 19 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a388 : bv 32 := 0x04058c63.
Lemma F_6a388 : fetch_word Asan.M.loaded_segments (0x6a3d8 : word) = Some W_6a388.
Proof. vm_refl. Qed.
Lemma D_6a388 : decode_any W_6a388 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a38c : bv 32 := 0x00150493.
Lemma F_6a38c : fetch_word Asan.M.loaded_segments (0x6a3dc : word) = Some W_6a38c.
Proof. vm_refl. Qed.
Lemma D_6a38c : decode_any W_6a38c = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a390 : bv 32 := 0xfff94593.
Lemma F_6a390 : fetch_word Asan.M.loaded_segments (0x6a3e0 : word) = Some W_6a390.
Proof. vm_refl. Qed.
Lemma D_6a390 : decode_any W_6a390 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a394 : bv 32 := 0x80040a13.
Lemma F_6a394 : fetch_word Asan.M.loaded_segments (0x6a3e4 : word) = Some W_6a394.
Proof. vm_refl. Qed.
Lemma D_6a394 : decode_any W_6a394 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a398 : bv 32 := 0xfa8a0a13.
Lemma F_6a398 : fetch_word Asan.M.loaded_segments (0x6a3e8 : word) = Some W_6a398.
Proof. vm_refl. Qed.
Lemma D_6a398 : decode_any W_6a398 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a39c : bv 32 := 0x0a95e063.
Lemma F_6a39c : fetch_word Asan.M.loaded_segments (0x6a3ec : word) = Some W_6a39c.
Proof. vm_refl. Qed.
Lemma D_6a39c : decode_any W_6a39c = Some (Branch BC_LTU 11 9 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3a0 : bv 32 := 0x04000593.
Lemma F_6a3a0 : fetch_word Asan.M.loaded_segments (0x6a3f0 : word) = Some W_6a3a0.
Proof. vm_refl. Qed.
Lemma D_6a3a0 : decode_any W_6a3a0 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3a4 : bv 32 := 0x10b57263.
Lemma F_6a3a4 : fetch_word Asan.M.loaded_segments (0x6a3f4 : word) = Some W_6a3a4.
Proof. vm_refl. Qed.
Lemma D_6a3a4 : decode_any W_6a3a4 = Some (Branch BC_GEU 10 11 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3a8 : bv 32 := 0x000ed597.
Lemma F_6a3a8 : fetch_word Asan.M.loaded_segments (0x6a3f8 : word) = Some W_6a3a8.
Proof. vm_refl. Qed.
Lemma D_6a3a8 : decode_any W_6a3a8 = Some (Auipc 11 237, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3ac : bv 32 := 0x9a05b583.
Lemma F_6a3ac : fetch_word Asan.M.loaded_segments (0x6a3fc : word) = Some W_6a3ac.
Proof. vm_refl. Qed.
Lemma D_6a3ac : decode_any W_6a3ac = Some (Load SZ8 true 11 11 2464, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3b0 : bv 32 := 0x0005b603.
Lemma F_6a3b0 : fetch_word Asan.M.loaded_segments (0x6a400 : word) = Some W_6a3b0.
Proof. vm_refl. Qed.
Lemma D_6a3b0 : decode_any W_6a3b0 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3b4 : bv 32 := 0x012506b3.
Lemma F_6a3b4 : fetch_word Asan.M.loaded_segments (0x6a404 : word) = Some W_6a3b4.
Proof. vm_refl. Qed.
Lemma D_6a3b4 : decode_any W_6a3b4 = Some (Op ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3b8 : bv 32 := 0x00395593.
Lemma F_6a3b8 : fetch_word Asan.M.loaded_segments (0x6a408 : word) = Some W_6a3b8.
Proof. vm_refl. Qed.
Lemma D_6a3b8 : decode_any W_6a3b8 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3bc : bv 32 := 0x0036d713.
Lemma F_6a3bc : fetch_word Asan.M.loaded_segments (0x6a40c : word) = Some W_6a3bc.
Proof. vm_refl. Qed.
Lemma D_6a3bc : decode_any W_6a3bc = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3c0 : bv 32 := 0x00b605b3.
Lemma F_6a3c0 : fetch_word Asan.M.loaded_segments (0x6a410 : word) = Some W_6a3c0.
Proof. vm_refl. Qed.
Lemma D_6a3c0 : decode_any W_6a3c0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3c4 : bv 32 := 0x00e60633.
Lemma F_6a3c4 : fetch_word Asan.M.loaded_segments (0x6a414 : word) = Some W_6a3c4.
Proof. vm_refl. Qed.
Lemma D_6a3c4 : decode_any W_6a3c4 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3c8 : bv 32 := 0xff85f713.
Lemma F_6a3c8 : fetch_word Asan.M.loaded_segments (0x6a418 : word) = Some W_6a3c8.
Proof. vm_refl. Qed.
Lemma D_6a3c8 : decode_any W_6a3c8 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3cc : bv 32 := 0xff867793.
Lemma F_6a3cc : fetch_word Asan.M.loaded_segments (0x6a41c : word) = Some W_6a3cc.
Proof. vm_refl. Qed.
Lemma D_6a3cc : decode_any W_6a3cc = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3d0 : bv 32 := 0x00073703.
Lemma F_6a3d0 : fetch_word Asan.M.loaded_segments (0x6a420 : word) = Some W_6a3d0.
Proof. vm_refl. Qed.
Lemma D_6a3d0 : decode_any W_6a3d0 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3d4 : bv 32 := 0x0007b783.
Lemma F_6a3d4 : fetch_word Asan.M.loaded_segments (0x6a424 : word) = Some W_6a3d4.
Proof. vm_refl. Qed.
Lemma D_6a3d4 : decode_any W_6a3d4 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3d8 : bv 32 := 0x00e7e733.
Lemma F_6a3d8 : fetch_word Asan.M.loaded_segments (0x6a428 : word) = Some W_6a3d8.
Proof. vm_refl. Qed.
Lemma D_6a3d8 : decode_any W_6a3d8 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3dc : bv 32 := 0x0c071e63.
Lemma F_6a3dc : fetch_word Asan.M.loaded_segments (0x6a42c : word) = Some W_6a3dc.
Proof. vm_refl. Qed.
Lemma D_6a3dc : decode_any W_6a3dc = Some (Branch BC_NE 14 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3e0 : bv 32 := 0x07010113.
Lemma F_6a3e0 : fetch_word Asan.M.loaded_segments (0x6a430 : word) = Some W_6a3e0.
Proof. vm_refl. Qed.
Lemma D_6a3e0 : decode_any W_6a3e0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3e4 : bv 32 := 0x7e813083.
Lemma F_6a3e4 : fetch_word Asan.M.loaded_segments (0x6a434 : word) = Some W_6a3e4.
Proof. vm_refl. Qed.
Lemma D_6a3e4 : decode_any W_6a3e4 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3e8 : bv 32 := 0x7e013403.
Lemma F_6a3e8 : fetch_word Asan.M.loaded_segments (0x6a438 : word) = Some W_6a3e8.
Proof. vm_refl. Qed.
Lemma D_6a3e8 : decode_any W_6a3e8 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3ec : bv 32 := 0x7d813483.
Lemma F_6a3ec : fetch_word Asan.M.loaded_segments (0x6a43c : word) = Some W_6a3ec.
Proof. vm_refl. Qed.
Lemma D_6a3ec : decode_any W_6a3ec = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3f0 : bv 32 := 0x7d013903.
Lemma F_6a3f0 : fetch_word Asan.M.loaded_segments (0x6a440 : word) = Some W_6a3f0.
Proof. vm_refl. Qed.
Lemma D_6a3f0 : decode_any W_6a3f0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3f4 : bv 32 := 0x7c813983.
Lemma F_6a3f4 : fetch_word Asan.M.loaded_segments (0x6a444 : word) = Some W_6a3f4.
Proof. vm_refl. Qed.
Lemma D_6a3f4 : decode_any W_6a3f4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3f8 : bv 32 := 0x7c013a03.
Lemma F_6a3f8 : fetch_word Asan.M.loaded_segments (0x6a448 : word) = Some W_6a3f8.
Proof. vm_refl. Qed.
Lemma D_6a3f8 : decode_any W_6a3f8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a3fc : bv 32 := 0x7b813a83.
Lemma F_6a3fc : fetch_word Asan.M.loaded_segments (0x6a44c : word) = Some W_6a3fc.
Proof. vm_refl. Qed.
Lemma D_6a3fc : decode_any W_6a3fc = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a400 : bv 32 := 0x7b013b03.
Lemma F_6a400 : fetch_word Asan.M.loaded_segments (0x6a450 : word) = Some W_6a400.
Proof. vm_refl. Qed.
Lemma D_6a400 : decode_any W_6a400 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a404 : bv 32 := 0x7f010113.
Lemma F_6a404 : fetch_word Asan.M.loaded_segments (0x6a454 : word) = Some W_6a404.
Proof. vm_refl. Qed.
Lemma D_6a404 : decode_any W_6a404 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a408 : bv 32 := 0x00008067.
Lemma F_6a408 : fetch_word Asan.M.loaded_segments (0x6a458 : word) = Some W_6a408.
Proof. vm_refl. Qed.
Lemma D_6a408 : decode_any W_6a408 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4a8 : bv 32 := 0x00050a93.
Lemma F_6a4a8 : fetch_word Asan.M.loaded_segments (0x6a4f8 : word) = Some W_6a4a8.
Proof. vm_refl. Qed.
Lemma D_6a4a8 : decode_any W_6a4a8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4ac : bv 32 := 0x04049263.
Lemma F_6a4ac : fetch_word Asan.M.loaded_segments (0x6a4fc : word) = Some W_6a4ac.
Proof. vm_refl. Qed.
Lemma D_6a4ac : decode_any W_6a4ac = Some (Branch BC_NE 9 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4b8 : bv 32 := 0x00050a93.
Lemma F_6a4b8 : fetch_word Asan.M.loaded_segments (0x6a508 : word) = Some W_6a4b8.
Proof. vm_refl. Qed.
Lemma D_6a4b8 : decode_any W_6a4b8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4bc : bv 32 := 0x00060503.
Lemma F_6a4bc : fetch_word Asan.M.loaded_segments (0x6a50c : word) = Some W_6a4bc.
Proof. vm_refl. Qed.
Lemma D_6a4bc : decode_any W_6a4bc = Some (Load SZ1 true 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4c0 : bv 32 := 0x0076f693.
Lemma F_6a4c0 : fetch_word Asan.M.loaded_segments (0x6a510 : word) = Some W_6a4c0.
Proof. vm_refl. Qed.
Lemma D_6a4c0 : decode_any W_6a4c0 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4c4 : bv 32 := 0x00a03733.
Lemma F_6a4c4 : fetch_word Asan.M.loaded_segments (0x6a514 : word) = Some W_6a4c4.
Proof. vm_refl. Qed.
Lemma D_6a4c4 : decode_any W_6a4c4 = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4c8 : bv 32 := 0x00a6a533.
Lemma F_6a4c8 : fetch_word Asan.M.loaded_segments (0x6a518 : word) = Some W_6a4c8.
Proof. vm_refl. Qed.
Lemma D_6a4c8 : decode_any W_6a4c8 = Some (Op ALU_SLT 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4cc : bv 32 := 0x00154513.
Lemma F_6a4cc : fetch_word Asan.M.loaded_segments (0x6a51c : word) = Some W_6a4cc.
Proof. vm_refl. Qed.
Lemma D_6a4cc : decode_any W_6a4cc = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4d0 : bv 32 := 0x00a77533.
Lemma F_6a4d0 : fetch_word Asan.M.loaded_segments (0x6a520 : word) = Some W_6a4d0.
Proof. vm_refl. Qed.
Lemma D_6a4d0 : decode_any W_6a4d0 = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4d4 : bv 32 := 0x00c5fa63.
Lemma F_6a4d4 : fetch_word Asan.M.loaded_segments (0x6a524 : word) = Some W_6a4d4.
Proof. vm_refl. Qed.
Lemma D_6a4d4 : decode_any W_6a4d4 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4d8 : bv 32 := 0x0005c683.
Lemma F_6a4d8 : fetch_word Asan.M.loaded_segments (0x6a528 : word) = Some W_6a4d8.
Proof. vm_refl. Qed.
Lemma D_6a4d8 : decode_any W_6a4d8 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4dc : bv 32 := 0x00158593.
Lemma F_6a4dc : fetch_word Asan.M.loaded_segments (0x6a52c : word) = Some W_6a4dc.
Proof. vm_refl. Qed.
Lemma D_6a4dc : decode_any W_6a4dc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4e0 : bv 32 := 0x00a6e533.
Lemma F_6a4e0 : fetch_word Asan.M.loaded_segments (0x6a530 : word) = Some W_6a4e0.
Proof. vm_refl. Qed.
Lemma D_6a4e0 : decode_any W_6a4e0 = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4e4 : bv 32 := 0xfec59ae3.
Lemma F_6a4e4 : fetch_word Asan.M.loaded_segments (0x6a534 : word) = Some W_6a4e4.
Proof. vm_refl. Qed.
Lemma D_6a4e4 : decode_any W_6a4e4 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4e8 : bv 32 := 0x0ff57513.
Lemma F_6a4e8 : fetch_word Asan.M.loaded_segments (0x6a538 : word) = Some W_6a4e8.
Proof. vm_refl. Qed.
Lemma D_6a4e8 : decode_any W_6a4e8 = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4ec : bv 32 := 0x0c050463.
Lemma F_6a4ec : fetch_word Asan.M.loaded_segments (0x6a53c : word) = Some W_6a4ec.
Proof. vm_refl. Qed.
Lemma D_6a4ec : decode_any W_6a4ec = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4f0 : bv 32 := 0x00090513.
Lemma F_6a4f0 : fetch_word Asan.M.loaded_segments (0x6a540 : word) = Some W_6a4f0.
Proof. vm_refl. Qed.
Lemma D_6a4f0 : decode_any W_6a4f0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4f4 : bv 32 := 0x00048593.
Lemma F_6a4f4 : fetch_word Asan.M.loaded_segments (0x6a544 : word) = Some W_6a4f4.
Proof. vm_refl. Qed.
Lemma D_6a4f4 : decode_any W_6a4f4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4f8 : bv 32 := 0x6a1170ef.
Lemma F_6a4f8 : fetch_word Asan.M.loaded_segments (0x6a548 : word) = Some W_6a4f8.
Proof. vm_refl. Qed.
Lemma D_6a4f8 : decode_any W_6a4f8 = Some (Jal 1 97952, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a4fc : bv 32 := 0x0a050c63.
Lemma F_6a4fc : fetch_word Asan.M.loaded_segments (0x6a54c : word) = Some W_6a4fc.
Proof. vm_refl. Qed.
Lemma D_6a4fc : decode_any W_6a4fc = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5b4 : bv 32 := 0x000a8513.
Lemma F_6a5b4 : fetch_word Asan.M.loaded_segments (0x6a604 : word) = Some W_6a5b4.
Proof. vm_refl. Qed.
Lemma D_6a5b4 : decode_any W_6a5b4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5b8 : bv 32 := 0xe29ff06f.
Lemma F_6a5b8 : fetch_word Asan.M.loaded_segments (0x6a608 : word) = Some W_6a5b8.
Proof. vm_refl. Qed.
Lemma D_6a5b8 : decode_any W_6a5b8 = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r4db30_4ddc4.
Module Na0_code_r4dae8_4daec.
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

Definition W_6a2c8 : bv 32 := 0x4a50706f.
Lemma F_6a2c8 : fetch_word Asan.M.loaded_segments (0x6a318 : word) = Some W_6a2c8.
Proof. vm_refl. Qed.
Lemma D_6a2c8 : decode_any W_6a2c8 = Some (Jal 0 31908, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r4dae8_4daec.
Module Na0_code_r52640_526bc.
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

Definition W_71f6c : bv 32 := 0xfe010113.
Lemma F_71f6c : fetch_word Asan.M.loaded_segments (0x71fbc : word) = Some W_71f6c.
Proof. vm_refl. Qed.
Lemma D_71f6c : decode_any W_71f6c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f70 : bv 32 := 0x00113c23.
Lemma F_71f70 : fetch_word Asan.M.loaded_segments (0x71fc0 : word) = Some W_71f70.
Proof. vm_refl. Qed.
Lemma D_71f70 : decode_any W_71f70 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f74 : bv 32 := 0x00813823.
Lemma F_71f74 : fetch_word Asan.M.loaded_segments (0x71fc4 : word) = Some W_71f74.
Proof. vm_refl. Qed.
Lemma D_71f74 : decode_any W_71f74 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f78 : bv 32 := 0x00913423.
Lemma F_71f78 : fetch_word Asan.M.loaded_segments (0x71fc8 : word) = Some W_71f78.
Proof. vm_refl. Qed.
Lemma D_71f78 : decode_any W_71f78 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f7c : bv 32 := 0x01213023.
Lemma F_71f7c : fetch_word Asan.M.loaded_segments (0x71fcc : word) = Some W_71f7c.
Proof. vm_refl. Qed.
Lemma D_71f7c : decode_any W_71f7c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f80 : bv 32 := 0x00050413.
Lemma F_71f80 : fetch_word Asan.M.loaded_segments (0x71fd0 : word) = Some W_71f80.
Proof. vm_refl. Qed.
Lemma D_71f80 : decode_any W_71f80 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f84 : bv 32 := 0x038160ef.
Lemma F_71f84 : fetch_word Asan.M.loaded_segments (0x71fd4 : word) = Some W_71f84.
Proof. vm_refl. Qed.
Lemma D_71f84 : decode_any W_71f84 = Some (Jal 1 90168, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f88 : bv 32 := 0x000e7597.
Lemma F_71f88 : fetch_word Asan.M.loaded_segments (0x71fd8 : word) = Some W_71f88.
Proof. vm_refl. Qed.
Lemma D_71f88 : decode_any W_71f88 = Some (Auipc 11 231, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f8c : bv 32 := 0xcc05b583.
Lemma F_71f8c : fetch_word Asan.M.loaded_segments (0x71fdc : word) = Some W_71f8c.
Proof. vm_refl. Qed.
Lemma D_71f8c : decode_any W_71f8c = Some (Load SZ8 true 11 11 3264, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f90 : bv 32 := 0x00050913.
Lemma F_71f90 : fetch_word Asan.M.loaded_segments (0x71fe0 : word) = Some W_71f90.
Proof. vm_refl. Qed.
Lemma D_71f90 : decode_any W_71f90 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f94 : bv 32 := 0x00040513.
Lemma F_71f94 : fetch_word Asan.M.loaded_segments (0x71fe4 : word) = Some W_71f94.
Proof. vm_refl. Qed.
Lemma D_71f94 : decode_any W_71f94 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f98 : bv 32 := 0x000580e7.
Lemma F_71f98 : fetch_word Asan.M.loaded_segments (0x71fe8 : word) = Some W_71f98.
Proof. vm_refl. Qed.
Lemma D_71f98 : decode_any W_71f98 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71f9c : bv 32 := 0x00050493.
Lemma F_71f9c : fetch_word Asan.M.loaded_segments (0x71fec : word) = Some W_71f9c.
Proof. vm_refl. Qed.
Lemma D_71f9c : decode_any W_71f9c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fa0 : bv 32 := 0x02090663.
Lemma F_71fa0 : fetch_word Asan.M.loaded_segments (0x71ff0 : word) = Some W_71fa0.
Proof. vm_refl. Qed.
Lemma D_71fa0 : decode_any W_71fa0 = Some (Branch BC_EQ 18 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fa4 : bv 32 := 0x019180ef.
Lemma F_71fa4 : fetch_word Asan.M.loaded_segments (0x71ff4 : word) = Some W_71fa4.
Proof. vm_refl. Qed.
Lemma D_71fa4 : decode_any W_71fa4 = Some (Jal 1 100376, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fa8 : bv 32 := 0x00050863.
Lemma F_71fa8 : fetch_word Asan.M.loaded_segments (0x71ff8 : word) = Some W_71fa8.
Proof. vm_refl. Qed.
Lemma D_71fa8 : decode_any W_71fa8 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fac : bv 32 := 0x03053603.
Lemma F_71fac : fetch_word Asan.M.loaded_segments (0x71ffc : word) = Some W_71fac.
Proof. vm_refl. Qed.
Lemma D_71fac : decode_any W_71fac = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fb0 : bv 32 := 0x03853683.
Lemma F_71fb0 : fetch_word Asan.M.loaded_segments (0x72000 : word) = Some W_71fb0.
Proof. vm_refl. Qed.
Lemma D_71fb0 : decode_any W_71fb0 = Some (Load SZ8 true 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fb4 : bv 32 := 0x00c0006f.
Lemma F_71fb4 : fetch_word Asan.M.loaded_segments (0x72004 : word) = Some W_71fb4.
Proof. vm_refl. Qed.
Lemma D_71fb4 : decode_any W_71fb4 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fc0 : bv 32 := 0x00040513.
Lemma F_71fc0 : fetch_word Asan.M.loaded_segments (0x72010 : word) = Some W_71fc0.
Proof. vm_refl. Qed.
Lemma D_71fc0 : decode_any W_71fc0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fc4 : bv 32 := 0x00048593.
Lemma F_71fc4 : fetch_word Asan.M.loaded_segments (0x72014 : word) = Some W_71fc4.
Proof. vm_refl. Qed.
Lemma D_71fc4 : decode_any W_71fc4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fc8 : bv 32 := 0x725250ef.
Lemma F_71fc8 : fetch_word Asan.M.loaded_segments (0x72018 : word) = Some W_71fc8.
Proof. vm_refl. Qed.
Lemma D_71fc8 : decode_any W_71fc8 = Some (Jal 1 155428, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fcc : bv 32 := 0x00048513.
Lemma F_71fcc : fetch_word Asan.M.loaded_segments (0x7201c : word) = Some W_71fcc.
Proof. vm_refl. Qed.
Lemma D_71fcc : decode_any W_71fcc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fd0 : bv 32 := 0x01813083.
Lemma F_71fd0 : fetch_word Asan.M.loaded_segments (0x72020 : word) = Some W_71fd0.
Proof. vm_refl. Qed.
Lemma D_71fd0 : decode_any W_71fd0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fd4 : bv 32 := 0x01013403.
Lemma F_71fd4 : fetch_word Asan.M.loaded_segments (0x72024 : word) = Some W_71fd4.
Proof. vm_refl. Qed.
Lemma D_71fd4 : decode_any W_71fd4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fd8 : bv 32 := 0x00813483.
Lemma F_71fd8 : fetch_word Asan.M.loaded_segments (0x72028 : word) = Some W_71fd8.
Proof. vm_refl. Qed.
Lemma D_71fd8 : decode_any W_71fd8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fdc : bv 32 := 0x00013903.
Lemma F_71fdc : fetch_word Asan.M.loaded_segments (0x7202c : word) = Some W_71fdc.
Proof. vm_refl. Qed.
Lemma D_71fdc : decode_any W_71fdc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fe0 : bv 32 := 0x02010113.
Lemma F_71fe0 : fetch_word Asan.M.loaded_segments (0x72030 : word) = Some W_71fe0.
Proof. vm_refl. Qed.
Lemma D_71fe0 : decode_any W_71fe0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_71fe4 : bv 32 := 0x00008067.
Lemma F_71fe4 : fetch_word Asan.M.loaded_segments (0x72034 : word) = Some W_71fe4.
Proof. vm_refl. Qed.
Lemma D_71fe4 : decode_any W_71fe4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r52640_526bc.
Module Na0_code_r76d68_770b8.
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

Definition W_97eec : bv 32 := 0xf7010113.
Lemma F_97eec : fetch_word Asan.M.loaded_segments (0x97f3c : word) = Some W_97eec.
Proof. vm_refl. Qed.
Lemma D_97eec : decode_any W_97eec = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_97ef0 : bv 32 := 0x08113423.
Lemma F_97ef0 : fetch_word Asan.M.loaded_segments (0x97f40 : word) = Some W_97ef0.
Proof. vm_refl. Qed.
Lemma D_97ef0 : decode_any W_97ef0 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_97ef4 : bv 32 := 0x08813023.
Lemma F_97ef4 : fetch_word Asan.M.loaded_segments (0x97f44 : word) = Some W_97ef4.
Proof. vm_refl. Qed.
Lemma D_97ef4 : decode_any W_97ef4 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_97ef8 : bv 32 := 0x06913c23.
Lemma F_97ef8 : fetch_word Asan.M.loaded_segments (0x97f48 : word) = Some W_97ef8.
Proof. vm_refl. Qed.
Lemma D_97ef8 : decode_any W_97ef8 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_97efc : bv 32 := 0x07213823.
Lemma F_97efc : fetch_word Asan.M.loaded_segments (0x97f4c : word) = Some W_97efc.
Proof. vm_refl. Qed.
Lemma D_97efc : decode_any W_97efc = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f00 : bv 32 := 0x07313423.
Lemma F_97f00 : fetch_word Asan.M.loaded_segments (0x97f50 : word) = Some W_97f00.
Proof. vm_refl. Qed.
Lemma D_97f00 : decode_any W_97f00 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f04 : bv 32 := 0x07413023.
Lemma F_97f04 : fetch_word Asan.M.loaded_segments (0x97f54 : word) = Some W_97f04.
Proof. vm_refl. Qed.
Lemma D_97f04 : decode_any W_97f04 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f08 : bv 32 := 0x05513c23.
Lemma F_97f08 : fetch_word Asan.M.loaded_segments (0x97f58 : word) = Some W_97f08.
Proof. vm_refl. Qed.
Lemma D_97f08 : decode_any W_97f08 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f0c : bv 32 := 0x05613823.
Lemma F_97f0c : fetch_word Asan.M.loaded_segments (0x97f5c : word) = Some W_97f0c.
Proof. vm_refl. Qed.
Lemma D_97f0c : decode_any W_97f0c = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f10 : bv 32 := 0x05713423.
Lemma F_97f10 : fetch_word Asan.M.loaded_segments (0x97f60 : word) = Some W_97f10.
Proof. vm_refl. Qed.
Lemma D_97f10 : decode_any W_97f10 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f14 : bv 32 := 0x05813023.
Lemma F_97f14 : fetch_word Asan.M.loaded_segments (0x97f64 : word) = Some W_97f14.
Proof. vm_refl. Qed.
Lemma D_97f14 : decode_any W_97f14 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f18 : bv 32 := 0x03913c23.
Lemma F_97f18 : fetch_word Asan.M.loaded_segments (0x97f68 : word) = Some W_97f18.
Proof. vm_refl. Qed.
Lemma D_97f18 : decode_any W_97f18 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f1c : bv 32 := 0x03a13823.
Lemma F_97f1c : fetch_word Asan.M.loaded_segments (0x97f6c : word) = Some W_97f1c.
Proof. vm_refl. Qed.
Lemma D_97f1c : decode_any W_97f1c = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f20 : bv 32 := 0x03b13423.
Lemma F_97f20 : fetch_word Asan.M.loaded_segments (0x97f70 : word) = Some W_97f20.
Proof. vm_refl. Qed.
Lemma D_97f20 : decode_any W_97f20 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f24 : bv 32 := 0x00058913.
Lemma F_97f24 : fetch_word Asan.M.loaded_segments (0x97f74 : word) = Some W_97f24.
Proof. vm_refl. Qed.
Lemma D_97f24 : decode_any W_97f24 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f28 : bv 32 := 0x000bf597.
Lemma F_97f28 : fetch_word Asan.M.loaded_segments (0x97f78 : word) = Some W_97f28.
Proof. vm_refl. Qed.
Lemma D_97f28 : decode_any W_97f28 = Some (Auipc 11 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f2c : bv 32 := 0xe105b583.
Lemma F_97f2c : fetch_word Asan.M.loaded_segments (0x97f7c : word) = Some W_97f2c.
Proof. vm_refl. Qed.
Lemma D_97f2c : decode_any W_97f2c = Some (Load SZ8 true 11 11 3600, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f30 : bv 32 := 0x0895c583.
Lemma F_97f30 : fetch_word Asan.M.loaded_segments (0x97f80 : word) = Some W_97f30.
Proof. vm_refl. Qed.
Lemma D_97f30 : decode_any W_97f30 = Some (Load SZ1 false 11 11 137, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f34 : bv 32 := 0x18058a63.
Lemma F_97f34 : fetch_word Asan.M.loaded_segments (0x97f84 : word) = Some W_97f34.
Proof. vm_refl. Qed.
Lemma D_97f34 : decode_any W_97f34 = Some (Branch BC_EQ 11 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f38 : bv 32 := 0x00050993.
Lemma F_97f38 : fetch_word Asan.M.loaded_segments (0x97f88 : word) = Some W_97f38.
Proof. vm_refl. Qed.
Lemma D_97f38 : decode_any W_97f38 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f3c : bv 32 := 0x000bf517.
Lemma F_97f3c : fetch_word Asan.M.loaded_segments (0x97f8c : word) = Some W_97f3c.
Proof. vm_refl. Qed.
Lemma D_97f3c : decode_any W_97f3c = Some (Auipc 10 191, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f40 : bv 32 := 0xe5c53d03.
Lemma F_97f40 : fetch_word Asan.M.loaded_segments (0x97f90 : word) = Some W_97f40.
Proof. vm_refl. Qed.
Lemma D_97f40 : decode_any W_97f40 = Some (Load SZ8 true 26 10 3676, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f44 : bv 32 := 0x0009ba03.
Lemma F_97f44 : fetch_word Asan.M.loaded_segments (0x97f94 : word) = Some W_97f44.
Proof. vm_refl. Qed.
Lemma D_97f44 : decode_any W_97f44 = Some (Load SZ8 true 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f48 : bv 32 := 0x000c0517.
Lemma F_97f48 : fetch_word Asan.M.loaded_segments (0x97f98 : word) = Some W_97f48.
Proof. vm_refl. Qed.
Lemma D_97f48 : decode_any W_97f48 = Some (Auipc 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f4c : bv 32 := 0x000d2583.
Lemma F_97f4c : fetch_word Asan.M.loaded_segments (0x97f9c : word) = Some W_97f4c.
Proof. vm_refl. Qed.
Lemma D_97f4c : decode_any W_97f4c = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f50 : bv 32 := 0xc0853a83.
Lemma F_97f50 : fetch_word Asan.M.loaded_segments (0x97fa0 : word) = Some W_97f50.
Proof. vm_refl. Qed.
Lemma D_97f50 : decode_any W_97f50 = Some (Load SZ8 true 21 10 3080, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f54 : bv 32 := 0x00300513.
Lemma F_97f54 : fetch_word Asan.M.loaded_segments (0x97fa4 : word) = Some W_97f54.
Proof. vm_refl. Qed.
Lemma D_97f54 : decode_any W_97f54 = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f58 : bv 32 := 0x004a8ab3.
Lemma F_97f58 : fetch_word Asan.M.loaded_segments (0x97fa8 : word) = Some W_97f58.
Proof. vm_refl. Qed.
Lemma D_97f58 : decode_any W_97f58 = Some (Op ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f5c : bv 32 := 0x1ea5fa63.
Lemma F_97f5c : fetch_word Asan.M.loaded_segments (0x97fac : word) = Some W_97f5c.
Proof. vm_refl. Qed.
Lemma D_97f5c : decode_any W_97f5c = Some (Branch BC_GEU 11 10 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f60 : bv 32 := 0x000abb03.
Lemma F_97f60 : fetch_word Asan.M.loaded_segments (0x97fb0 : word) = Some W_97f60.
Proof. vm_refl. Qed.
Lemma D_97f60 : decode_any W_97f60 = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f64 : bv 32 := 0xfff00513.
Lemma F_97f64 : fetch_word Asan.M.loaded_segments (0x97fb4 : word) = Some W_97f64.
Proof. vm_refl. Qed.
Lemma D_97f64 : decode_any W_97f64 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f68 : bv 32 := 0x0230000f.
Lemma F_97f68 : fetch_word Asan.M.loaded_segments (0x97fb8 : word) = Some W_97f68.
Proof. vm_refl. Qed.
Lemma D_97f68 : decode_any W_97f68 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f6c : bv 32 := 0x14ab0e63.
Lemma F_97f6c : fetch_word Asan.M.loaded_segments (0x97fbc : word) = Some W_97f6c.
Proof. vm_refl. Qed.
Lemma D_97f6c : decode_any W_97f6c = Some (Branch BC_EQ 22 10 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_97f70 : bv 32 := 0x080b1263.
Lemma F_97f70 : fetch_word Asan.M.loaded_segments (0x97fc0 : word) = Some W_97f70.
Proof. vm_refl. Qed.
Lemma D_97f70 : decode_any W_97f70 = Some (Branch BC_NE 22 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_97ff4 : bv 32 := 0x0c0b0a63.
Lemma F_97ff4 : fetch_word Asan.M.loaded_segments (0x98044 : word) = Some W_97ff4.
Proof. vm_refl. Qed.
Lemma D_97ff4 : decode_any W_97ff4 = Some (Branch BC_EQ 22 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_97ff8 : bv 32 := 0x00c13823.
Lemma F_97ff8 : fetch_word Asan.M.loaded_segments (0x98048 : word) = Some W_97ff8.
Proof. vm_refl. Qed.
Lemma D_97ff8 : decode_any W_97ff8 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_97ffc : bv 32 := 0x00d13c23.
Lemma F_97ffc : fetch_word Asan.M.loaded_segments (0x9804c : word) = Some W_97ffc.
Proof. vm_refl. Qed.
Lemma D_97ffc : decode_any W_97ffc = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_98000 : bv 32 := 0x0ff00513.
Lemma F_98000 : fetch_word Asan.M.loaded_segments (0x98050 : word) = Some W_98000.
Proof. vm_refl. Qed.
Lemma D_98000 : decode_any W_98000 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_98004 : bv 32 := 0x0aaa6863.
Lemma F_98004 : fetch_word Asan.M.loaded_segments (0x98054 : word) = Some W_98004.
Proof. vm_refl. Qed.
Lemma D_98004 : decode_any W_98004 = Some (Branch BC_LTU 20 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_980b4 : bv 32 := 0x000b0513.
Lemma F_980b4 : fetch_word Asan.M.loaded_segments (0x98104 : word) = Some W_980b4.
Proof. vm_refl. Qed.
Lemma D_980b4 : decode_any W_980b4 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_980b8 : bv 32 := 0x004a1413.
Lemma F_980b8 : fetch_word Asan.M.loaded_segments (0x98108 : word) = Some W_980b8.
Proof. vm_refl. Qed.
Lemma D_980b8 : decode_any W_980b8 = Some (ShiftImm ALU_SLL 8 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_980bc : bv 32 := 0x00850433.
Lemma F_980bc : fetch_word Asan.M.loaded_segments (0x9810c : word) = Some W_980bc.
Proof. vm_refl. Qed.
Lemma D_980bc : decode_any W_980bc = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_980c0 : bv 32 := 0x00843503.
Lemma F_980c0 : fetch_word Asan.M.loaded_segments (0x98110 : word) = Some W_980c0.
Proof. vm_refl. Qed.
Lemma D_980c0 : decode_any W_980c0 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_980c4 : bv 32 := 0x04050263.
Lemma F_980c4 : fetch_word Asan.M.loaded_segments (0x98114 : word) = Some W_980c4.
Proof. vm_refl. Qed.
Lemma D_980c4 : decode_any W_980c4 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_980c8 : bv 32 := 0x00000513.
Lemma F_980c8 : fetch_word Asan.M.loaded_segments (0x98118 : word) = Some W_980c8.
Proof. vm_refl. Qed.
Lemma D_980c8 : decode_any W_980c8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_980cc : bv 32 := 0x08813083.
Lemma F_980cc : fetch_word Asan.M.loaded_segments (0x9811c : word) = Some W_980cc.
Proof. vm_refl. Qed.
Lemma D_980cc : decode_any W_980cc = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_980d0 : bv 32 := 0x08013403.
Lemma F_980d0 : fetch_word Asan.M.loaded_segments (0x98120 : word) = Some W_980d0.
Proof. vm_refl. Qed.
Lemma D_980d0 : decode_any W_980d0 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_980d4 : bv 32 := 0x07813483.
Lemma F_980d4 : fetch_word Asan.M.loaded_segments (0x98124 : word) = Some W_980d4.
Proof. vm_refl. Qed.
Lemma D_980d4 : decode_any W_980d4 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_980d8 : bv 32 := 0x07013903.
Lemma F_980d8 : fetch_word Asan.M.loaded_segments (0x98128 : word) = Some W_980d8.
Proof. vm_refl. Qed.
Lemma D_980d8 : decode_any W_980d8 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_980dc : bv 32 := 0x06813983.
Lemma F_980dc : fetch_word Asan.M.loaded_segments (0x9812c : word) = Some W_980dc.
Proof. vm_refl. Qed.
Lemma D_980dc : decode_any W_980dc = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_980e0 : bv 32 := 0x06013a03.
Lemma F_980e0 : fetch_word Asan.M.loaded_segments (0x98130 : word) = Some W_980e0.
Proof. vm_refl. Qed.
Lemma D_980e0 : decode_any W_980e0 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_980e4 : bv 32 := 0x05813a83.
Lemma F_980e4 : fetch_word Asan.M.loaded_segments (0x98134 : word) = Some W_980e4.
Proof. vm_refl. Qed.
Lemma D_980e4 : decode_any W_980e4 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_980e8 : bv 32 := 0x05013b03.
Lemma F_980e8 : fetch_word Asan.M.loaded_segments (0x98138 : word) = Some W_980e8.
Proof. vm_refl. Qed.
Lemma D_980e8 : decode_any W_980e8 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_980ec : bv 32 := 0x04813b83.
Lemma F_980ec : fetch_word Asan.M.loaded_segments (0x9813c : word) = Some W_980ec.
Proof. vm_refl. Qed.
Lemma D_980ec : decode_any W_980ec = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_980f0 : bv 32 := 0x04013c03.
Lemma F_980f0 : fetch_word Asan.M.loaded_segments (0x98140 : word) = Some W_980f0.
Proof. vm_refl. Qed.
Lemma D_980f0 : decode_any W_980f0 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_980f4 : bv 32 := 0x03813c83.
Lemma F_980f4 : fetch_word Asan.M.loaded_segments (0x98144 : word) = Some W_980f4.
Proof. vm_refl. Qed.
Lemma D_980f4 : decode_any W_980f4 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_980f8 : bv 32 := 0x03013d03.
Lemma F_980f8 : fetch_word Asan.M.loaded_segments (0x98148 : word) = Some W_980f8.
Proof. vm_refl. Qed.
Lemma D_980f8 : decode_any W_980f8 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_980fc : bv 32 := 0x02813d83.
Lemma F_980fc : fetch_word Asan.M.loaded_segments (0x9814c : word) = Some W_980fc.
Proof. vm_refl. Qed.
Lemma D_980fc : decode_any W_980fc = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_98100 : bv 32 := 0x09010113.
Lemma F_98100 : fetch_word Asan.M.loaded_segments (0x98150 : word) = Some W_98100.
Proof. vm_refl. Qed.
Lemma D_98100 : decode_any W_98100 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_98104 : bv 32 := 0x00008067.
Lemma F_98104 : fetch_word Asan.M.loaded_segments (0x98154 : word) = Some W_98104.
Proof. vm_refl. Qed.
Lemma D_98104 : decode_any W_98104 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r76d68_770b8.
Module Na0_code_rcc154_cc178.
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

Definition W_149d08 : bv 32 := 0x00020593.
Lemma F_149d08 : fetch_word Asan.M.loaded_segments (0x149d4c : word) = Some W_149d08.
Proof. vm_refl. Qed.
Lemma D_149d08 : decode_any W_149d08 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149d0c : bv 32 := 0x00053603.
Lemma F_149d0c : fetch_word Asan.M.loaded_segments (0x149d50 : word) = Some W_149d0c.
Proof. vm_refl. Qed.
Lemma D_149d0c : decode_any W_149d0c = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149d10 : bv 32 := 0xff85b583.
Lemma F_149d10 : fetch_word Asan.M.loaded_segments (0x149d54 : word) = Some W_149d10.
Proof. vm_refl. Qed.
Lemma D_149d10 : decode_any W_149d10 = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_149d14 : bv 32 := 0x00853503.
Lemma F_149d14 : fetch_word Asan.M.loaded_segments (0x149d58 : word) = Some W_149d14.
Proof. vm_refl. Qed.
Lemma D_149d14 : decode_any W_149d14 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_149d18 : bv 32 := 0x00361613.
Lemma F_149d18 : fetch_word Asan.M.loaded_segments (0x149d5c : word) = Some W_149d18.
Proof. vm_refl. Qed.
Lemma D_149d18 : decode_any W_149d18 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_149d1c : bv 32 := 0x00c585b3.
Lemma F_149d1c : fetch_word Asan.M.loaded_segments (0x149d60 : word) = Some W_149d1c.
Proof. vm_refl. Qed.
Lemma D_149d1c : decode_any W_149d1c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_149d20 : bv 32 := 0x0005b583.
Lemma F_149d20 : fetch_word Asan.M.loaded_segments (0x149d64 : word) = Some W_149d20.
Proof. vm_refl. Qed.
Lemma D_149d20 : decode_any W_149d20 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149d24 : bv 32 := 0x00b50533.
Lemma F_149d24 : fetch_word Asan.M.loaded_segments (0x149d68 : word) = Some W_149d24.
Proof. vm_refl. Qed.
Lemma D_149d24 : decode_any W_149d24 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_149d28 : bv 32 := 0x00008067.
Lemma F_149d28 : fetch_word Asan.M.loaded_segments (0x149d6c : word) = Some W_149d28.
Proof. vm_refl. Qed.
Lemma D_149d28 : decode_any W_149d28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rcc154_cc178.
Module Na0_code_rb428c_b4290.
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

Definition W_c6d2c : bv 32 := 0x00008067.
Lemma F_c6d2c : fetch_word Asan.M.loaded_segments (0xc6d7c : word) = Some W_c6d2c.
Proof. vm_refl. Qed.
Lemma D_c6d2c : decode_any W_c6d2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb428c_b4290.
Module Na0_code_rbf0e8_bf0ec.
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

Definition W_befa4 : bv 32 := 0x00008067.
Lemma F_befa4 : fetch_word Asan.M.loaded_segments (0xbeff4 : word) = Some W_befa4.
Proof. vm_refl. Qed.
Lemma D_befa4 : decode_any W_befa4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbf0e8_bf0ec.
Module Na0_code_rc1f64_c1f68.
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

Definition W_ceeac : bv 32 := 0x00008067.
Lemma F_ceeac : fetch_word Asan.M.loaded_segments (0xceefc : word) = Some W_ceeac.
Proof. vm_refl. Qed.
Lemma D_ceeac : decode_any W_ceeac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc1f64_c1f68.
Module Na0_code_r71324_71340.
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

Definition W_9248c : bv 32 := 0x00000593.
Lemma F_9248c : fetch_word Asan.M.loaded_segments (0x924dc : word) = Some W_9248c.
Proof. vm_refl. Qed.
Lemma D_9248c : decode_any W_9248c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92490 : bv 32 := 0x00b50633.
Lemma F_92490 : fetch_word Asan.M.loaded_segments (0x924e0 : word) = Some W_92490.
Proof. vm_refl. Qed.
Lemma D_92490 : decode_any W_92490 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_92494 : bv 32 := 0x00064603.
Lemma F_92494 : fetch_word Asan.M.loaded_segments (0x924e4 : word) = Some W_92494.
Proof. vm_refl. Qed.
Lemma D_92494 : decode_any W_92494 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92498 : bv 32 := 0x00158593.
Lemma F_92498 : fetch_word Asan.M.loaded_segments (0x924e8 : word) = Some W_92498.
Proof. vm_refl. Qed.
Lemma D_92498 : decode_any W_92498 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9249c : bv 32 := 0xfe061ae3.
Lemma F_9249c : fetch_word Asan.M.loaded_segments (0x924ec : word) = Some W_9249c.
Proof. vm_refl. Qed.
Lemma D_9249c : decode_any W_9249c = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_924a0 : bv 32 := 0xfff58513.
Lemma F_924a0 : fetch_word Asan.M.loaded_segments (0x924f0 : word) = Some W_924a0.
Proof. vm_refl. Qed.
Lemma D_924a0 : decode_any W_924a0 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_924a4 : bv 32 := 0x00008067.
Lemma F_924a4 : fetch_word Asan.M.loaded_segments (0x924f4 : word) = Some W_924a4.
Proof. vm_refl. Qed.
Lemma D_924a4 : decode_any W_924a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r71324_71340.
Module Na0_code_r4de14_4df90.
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

Definition W_6a60c : bv 32 := 0x06048a63.
Lemma F_6a60c : fetch_word Asan.M.loaded_segments (0x6a65c : word) = Some W_6a60c.
Proof. vm_refl. Qed.
Lemma D_6a60c : decode_any W_6a60c = Some (Branch BC_EQ 9 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a610 : bv 32 := 0x000ec597.
Lemma F_6a610 : fetch_word Asan.M.loaded_segments (0x6a660 : word) = Some W_6a610.
Proof. vm_refl. Qed.
Lemma D_6a610 : decode_any W_6a610 = Some (Auipc 11 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a614 : bv 32 := 0x7285ba83.
Lemma F_6a614 : fetch_word Asan.M.loaded_segments (0x6a664 : word) = Some W_6a614.
Proof. vm_refl. Qed.
Lemma D_6a614 : decode_any W_6a614 = Some (Load SZ8 true 21 11 1832, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a618 : bv 32 := 0x0fbac583.
Lemma F_6a618 : fetch_word Asan.M.loaded_segments (0x6a668 : word) = Some W_6a618.
Proof. vm_refl. Qed.
Lemma D_6a618 : decode_any W_6a618 = Some (Load SZ1 false 11 21 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a61c : bv 32 := 0x06058263.
Lemma F_6a61c : fetch_word Asan.M.loaded_segments (0x6a66c : word) = Some W_6a61c.
Proof. vm_refl. Qed.
Lemma D_6a61c : decode_any W_6a61c = Some (Branch BC_EQ 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a620 : bv 32 := 0x00150493.
Lemma F_6a620 : fetch_word Asan.M.loaded_segments (0x6a670 : word) = Some W_6a620.
Proof. vm_refl. Qed.
Lemma D_6a620 : decode_any W_6a620 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a624 : bv 32 := 0x0934f463.
Lemma F_6a624 : fetch_word Asan.M.loaded_segments (0x6a674 : word) = Some W_6a624.
Proof. vm_refl. Qed.
Lemma D_6a624 : decode_any W_6a624 = Some (Branch BC_GEU 9 19 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a628 : bv 32 := 0xfff94593.
Lemma F_6a628 : fetch_word Asan.M.loaded_segments (0x6a678 : word) = Some W_6a628.
Proof. vm_refl. Qed.
Lemma D_6a628 : decode_any W_6a628 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a62c : bv 32 := 0x80040a13.
Lemma F_6a62c : fetch_word Asan.M.loaded_segments (0x6a67c : word) = Some W_6a62c.
Proof. vm_refl. Qed.
Lemma D_6a62c : decode_any W_6a62c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a630 : bv 32 := 0xfa8a0a13.
Lemma F_6a630 : fetch_word Asan.M.loaded_segments (0x6a680 : word) = Some W_6a630.
Proof. vm_refl. Qed.
Lemma D_6a630 : decode_any W_6a630 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a634 : bv 32 := 0x0895e663.
Lemma F_6a634 : fetch_word Asan.M.loaded_segments (0x6a684 : word) = Some W_6a634.
Proof. vm_refl. Qed.
Lemma D_6a634 : decode_any W_6a634 = Some (Branch BC_LTU 11 9 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a638 : bv 32 := 0xfbf48593.
Lemma F_6a638 : fetch_word Asan.M.loaded_segments (0x6a688 : word) = Some W_6a638.
Proof. vm_refl. Qed.
Lemma D_6a638 : decode_any W_6a638 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a63c : bv 32 := 0xfbf00613.
Lemma F_6a63c : fetch_word Asan.M.loaded_segments (0x6a68c : word) = Some W_6a63c.
Proof. vm_refl. Qed.
Lemma D_6a63c : decode_any W_6a63c = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a640 : bv 32 := 0x0eb67863.
Lemma F_6a640 : fetch_word Asan.M.loaded_segments (0x6a690 : word) = Some W_6a640.
Proof. vm_refl. Qed.
Lemma D_6a640 : decode_any W_6a640 = Some (Branch BC_GEU 12 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a644 : bv 32 := 0x000ec597.
Lemma F_6a644 : fetch_word Asan.M.loaded_segments (0x6a694 : word) = Some W_6a644.
Proof. vm_refl. Qed.
Lemma D_6a644 : decode_any W_6a644 = Some (Auipc 11 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a648 : bv 32 := 0x7045b583.
Lemma F_6a648 : fetch_word Asan.M.loaded_segments (0x6a698 : word) = Some W_6a648.
Proof. vm_refl. Qed.
Lemma D_6a648 : decode_any W_6a648 = Some (Load SZ8 true 11 11 1796, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a64c : bv 32 := 0x009906b3.
Lemma F_6a64c : fetch_word Asan.M.loaded_segments (0x6a69c : word) = Some W_6a64c.
Proof. vm_refl. Qed.
Lemma D_6a64c : decode_any W_6a64c = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a650 : bv 32 := 0x0005b603.
Lemma F_6a650 : fetch_word Asan.M.loaded_segments (0x6a6a0 : word) = Some W_6a650.
Proof. vm_refl. Qed.
Lemma D_6a650 : decode_any W_6a650 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a654 : bv 32 := 0x00395593.
Lemma F_6a654 : fetch_word Asan.M.loaded_segments (0x6a6a4 : word) = Some W_6a654.
Proof. vm_refl. Qed.
Lemma D_6a654 : decode_any W_6a654 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a658 : bv 32 := 0xfff68693.
Lemma F_6a658 : fetch_word Asan.M.loaded_segments (0x6a6a8 : word) = Some W_6a658.
Proof. vm_refl. Qed.
Lemma D_6a658 : decode_any W_6a658 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a65c : bv 32 := 0x0036d713.
Lemma F_6a65c : fetch_word Asan.M.loaded_segments (0x6a6ac : word) = Some W_6a65c.
Proof. vm_refl. Qed.
Lemma D_6a65c : decode_any W_6a65c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a660 : bv 32 := 0x00b605b3.
Lemma F_6a660 : fetch_word Asan.M.loaded_segments (0x6a6b0 : word) = Some W_6a660.
Proof. vm_refl. Qed.
Lemma D_6a660 : decode_any W_6a660 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a664 : bv 32 := 0x00e60633.
Lemma F_6a664 : fetch_word Asan.M.loaded_segments (0x6a6b4 : word) = Some W_6a664.
Proof. vm_refl. Qed.
Lemma D_6a664 : decode_any W_6a664 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a668 : bv 32 := 0xff85f713.
Lemma F_6a668 : fetch_word Asan.M.loaded_segments (0x6a6b8 : word) = Some W_6a668.
Proof. vm_refl. Qed.
Lemma D_6a668 : decode_any W_6a668 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a66c : bv 32 := 0xff867793.
Lemma F_6a66c : fetch_word Asan.M.loaded_segments (0x6a6bc : word) = Some W_6a66c.
Proof. vm_refl. Qed.
Lemma D_6a66c : decode_any W_6a66c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a670 : bv 32 := 0x00073703.
Lemma F_6a670 : fetch_word Asan.M.loaded_segments (0x6a6c0 : word) = Some W_6a670.
Proof. vm_refl. Qed.
Lemma D_6a670 : decode_any W_6a670 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a674 : bv 32 := 0x0007b783.
Lemma F_6a674 : fetch_word Asan.M.loaded_segments (0x6a6c4 : word) = Some W_6a674.
Proof. vm_refl. Qed.
Lemma D_6a674 : decode_any W_6a674 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a678 : bv 32 := 0x00e7e733.
Lemma F_6a678 : fetch_word Asan.M.loaded_segments (0x6a6c8 : word) = Some W_6a678.
Proof. vm_refl. Qed.
Lemma D_6a678 : decode_any W_6a678 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a67c : bv 32 := 0x0a071e63.
Lemma F_6a67c : fetch_word Asan.M.loaded_segments (0x6a6cc : word) = Some W_6a67c.
Proof. vm_refl. Qed.
Lemma D_6a67c : decode_any W_6a67c = Some (Branch BC_NE 14 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a730 : bv 32 := 0x02049e63.
Lemma F_6a730 : fetch_word Asan.M.loaded_segments (0x6a780 : word) = Some W_6a730.
Proof. vm_refl. Qed.
Lemma D_6a730 : decode_any W_6a730 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a76c : bv 32 := 0x00050b13.
Lemma F_6a76c : fetch_word Asan.M.loaded_segments (0x6a7bc : word) = Some W_6a76c.
Proof. vm_refl. Qed.
Lemma D_6a76c : decode_any W_6a76c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a770 : bv 32 := 0x00090513.
Lemma F_6a770 : fetch_word Asan.M.loaded_segments (0x6a7c0 : word) = Some W_6a770.
Proof. vm_refl. Qed.
Lemma D_6a770 : decode_any W_6a770 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a774 : bv 32 := 0x00048593.
Lemma F_6a774 : fetch_word Asan.M.loaded_segments (0x6a7c4 : word) = Some W_6a774.
Proof. vm_refl. Qed.
Lemma D_6a774 : decode_any W_6a774 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a778 : bv 32 := 0x421170ef.
Lemma F_6a778 : fetch_word Asan.M.loaded_segments (0x6a7c8 : word) = Some W_6a778.
Proof. vm_refl. Qed.
Lemma D_6a778 : decode_any W_6a778 = Some (Jal 1 97312, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a77c : bv 32 := 0x00050913.
Lemma F_6a77c : fetch_word Asan.M.loaded_segments (0x6a7cc : word) = Some W_6a77c.
Proof. vm_refl. Qed.
Lemma D_6a77c : decode_any W_6a77c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a780 : bv 32 := 0x000b0513.
Lemma F_6a780 : fetch_word Asan.M.loaded_segments (0x6a7d0 : word) = Some W_6a780.
Proof. vm_refl. Qed.
Lemma D_6a780 : decode_any W_6a780 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a784 : bv 32 := 0xee090ee3.
Lemma F_6a784 : fetch_word Asan.M.loaded_segments (0x6a7d4 : word) = Some W_6a784.
Proof. vm_refl. Qed.
Lemma D_6a784 : decode_any W_6a784 = Some (Branch BC_EQ 18 0 7932, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r4de14_4df90.
Module Na0_code_r4f2d8_4f480.
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

Definition W_6bf58 : bv 32 := 0x060a0063.
Lemma F_6bf58 : fetch_word Asan.M.loaded_segments (0x6bfa8 : word) = Some W_6bf58.
Proof. vm_refl. Qed.
Lemma D_6bf58 : decode_any W_6bf58 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf5c : bv 32 := 0x0a051c63.
Lemma F_6bf5c : fetch_word Asan.M.loaded_segments (0x6bfac : word) = Some W_6bf5c.
Proof. vm_refl. Qed.
Lemma D_6bf5c : decode_any W_6bf5c = Some (Branch BC_NE 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf70 : bv 32 := 0xfbf48593.
Lemma F_6bf70 : fetch_word Asan.M.loaded_segments (0x6bfc0 : word) = Some W_6bf70.
Proof. vm_refl. Qed.
Lemma D_6bf70 : decode_any W_6bf70 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf74 : bv 32 := 0xfbf00613.
Lemma F_6bf74 : fetch_word Asan.M.loaded_segments (0x6bfc4 : word) = Some W_6bf74.
Proof. vm_refl. Qed.
Lemma D_6bf74 : decode_any W_6bf74 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf78 : bv 32 := 0x12b67663.
Lemma F_6bf78 : fetch_word Asan.M.loaded_segments (0x6bfc8 : word) = Some W_6bf78.
Proof. vm_refl. Qed.
Lemma D_6bf78 : decode_any W_6bf78 = Some (Branch BC_GEU 12 11 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf7c : bv 32 := 0x000eb597.
Lemma F_6bf7c : fetch_word Asan.M.loaded_segments (0x6bfcc : word) = Some W_6bf7c.
Proof. vm_refl. Qed.
Lemma D_6bf7c : decode_any W_6bf7c = Some (Auipc 11 235, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf80 : bv 32 := 0xdcc5b583.
Lemma F_6bf80 : fetch_word Asan.M.loaded_segments (0x6bfd0 : word) = Some W_6bf80.
Proof. vm_refl. Qed.
Lemma D_6bf80 : decode_any W_6bf80 = Some (Load SZ8 true 11 11 3532, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf84 : bv 32 := 0x009906b3.
Lemma F_6bf84 : fetch_word Asan.M.loaded_segments (0x6bfd4 : word) = Some W_6bf84.
Proof. vm_refl. Qed.
Lemma D_6bf84 : decode_any W_6bf84 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf88 : bv 32 := 0x0005b603.
Lemma F_6bf88 : fetch_word Asan.M.loaded_segments (0x6bfd8 : word) = Some W_6bf88.
Proof. vm_refl. Qed.
Lemma D_6bf88 : decode_any W_6bf88 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf8c : bv 32 := 0x00395593.
Lemma F_6bf8c : fetch_word Asan.M.loaded_segments (0x6bfdc : word) = Some W_6bf8c.
Proof. vm_refl. Qed.
Lemma D_6bf8c : decode_any W_6bf8c = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf90 : bv 32 := 0xfff68693.
Lemma F_6bf90 : fetch_word Asan.M.loaded_segments (0x6bfe0 : word) = Some W_6bf90.
Proof. vm_refl. Qed.
Lemma D_6bf90 : decode_any W_6bf90 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf94 : bv 32 := 0x0036d713.
Lemma F_6bf94 : fetch_word Asan.M.loaded_segments (0x6bfe4 : word) = Some W_6bf94.
Proof. vm_refl. Qed.
Lemma D_6bf94 : decode_any W_6bf94 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf98 : bv 32 := 0x00b605b3.
Lemma F_6bf98 : fetch_word Asan.M.loaded_segments (0x6bfe8 : word) = Some W_6bf98.
Proof. vm_refl. Qed.
Lemma D_6bf98 : decode_any W_6bf98 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bf9c : bv 32 := 0x00e60633.
Lemma F_6bf9c : fetch_word Asan.M.loaded_segments (0x6bfec : word) = Some W_6bf9c.
Proof. vm_refl. Qed.
Lemma D_6bf9c : decode_any W_6bf9c = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bfa0 : bv 32 := 0xff85f713.
Lemma F_6bfa0 : fetch_word Asan.M.loaded_segments (0x6bff0 : word) = Some W_6bfa0.
Proof. vm_refl. Qed.
Lemma D_6bfa0 : decode_any W_6bfa0 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bfa4 : bv 32 := 0xff867793.
Lemma F_6bfa4 : fetch_word Asan.M.loaded_segments (0x6bff4 : word) = Some W_6bfa4.
Proof. vm_refl. Qed.
Lemma D_6bfa4 : decode_any W_6bfa4 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bfa8 : bv 32 := 0x00073703.
Lemma F_6bfa8 : fetch_word Asan.M.loaded_segments (0x6bff8 : word) = Some W_6bfa8.
Proof. vm_refl. Qed.
Lemma D_6bfa8 : decode_any W_6bfa8 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bfac : bv 32 := 0x0007b783.
Lemma F_6bfac : fetch_word Asan.M.loaded_segments (0x6bffc : word) = Some W_6bfac.
Proof. vm_refl. Qed.
Lemma D_6bfac : decode_any W_6bfac = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bfb0 : bv 32 := 0x00e7e733.
Lemma F_6bfb0 : fetch_word Asan.M.loaded_segments (0x6c000 : word) = Some W_6bfb0.
Proof. vm_refl. Qed.
Lemma D_6bfb0 : decode_any W_6bfb0 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bfb4 : bv 32 := 0x0e071c63.
Lemma F_6bfb4 : fetch_word Asan.M.loaded_segments (0x6c004 : word) = Some W_6bfb4.
Proof. vm_refl. Qed.
Lemma D_6bfb4 : decode_any W_6bfb4 = Some (Branch BC_NE 14 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c014 : bv 32 := 0x412504b3.
Lemma F_6c014 : fetch_word Asan.M.loaded_segments (0x6c064 : word) = Some W_6c014.
Proof. vm_refl. Qed.
Lemma D_6c014 : decode_any W_6c014 = Some (Op ALU_SUB 9 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c018 : bv 32 := 0x00148493.
Lemma F_6c018 : fetch_word Asan.M.loaded_segments (0x6c068 : word) = Some W_6c018.
Proof. vm_refl. Qed.
Lemma D_6c018 : decode_any W_6c018 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c01c : bv 32 := 0xfff94593.
Lemma F_6c01c : fetch_word Asan.M.loaded_segments (0x6c06c : word) = Some W_6c01c.
Proof. vm_refl. Qed.
Lemma D_6c01c : decode_any W_6c01c = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c020 : bv 32 := 0x80040a13.
Lemma F_6c020 : fetch_word Asan.M.loaded_segments (0x6c070 : word) = Some W_6c020.
Proof. vm_refl. Qed.
Lemma D_6c020 : decode_any W_6c020 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c024 : bv 32 := 0xfb0a0a13.
Lemma F_6c024 : fetch_word Asan.M.loaded_segments (0x6c074 : word) = Some W_6c024.
Proof. vm_refl. Qed.
Lemma D_6c024 : decode_any W_6c024 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c028 : bv 32 := 0xf495f4e3.
Lemma F_6c028 : fetch_word Asan.M.loaded_segments (0x6c078 : word) = Some W_6c028.
Proof. vm_refl. Qed.
Lemma D_6c028 : decode_any W_6c028 = Some (Branch BC_GEU 11 9 8008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0a4 : bv 32 := 0x02049e63.
Lemma F_6c0a4 : fetch_word Asan.M.loaded_segments (0x6c0f4 : word) = Some W_6c0a4.
Proof. vm_refl. Qed.
Lemma D_6c0a4 : decode_any W_6c0a4 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0e0 : bv 32 := 0x00050a93.
Lemma F_6c0e0 : fetch_word Asan.M.loaded_segments (0x6c130 : word) = Some W_6c0e0.
Proof. vm_refl. Qed.
Lemma D_6c0e0 : decode_any W_6c0e0 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0e4 : bv 32 := 0x00090513.
Lemma F_6c0e4 : fetch_word Asan.M.loaded_segments (0x6c134 : word) = Some W_6c0e4.
Proof. vm_refl. Qed.
Lemma D_6c0e4 : decode_any W_6c0e4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0e8 : bv 32 := 0x00048593.
Lemma F_6c0e8 : fetch_word Asan.M.loaded_segments (0x6c138 : word) = Some W_6c0e8.
Proof. vm_refl. Qed.
Lemma D_6c0e8 : decode_any W_6c0e8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0ec : bv 32 := 0x2ac160ef.
Lemma F_6c0ec : fetch_word Asan.M.loaded_segments (0x6c13c : word) = Some W_6c0ec.
Proof. vm_refl. Qed.
Lemma D_6c0ec : decode_any W_6c0ec = Some (Jal 1 90796, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0f0 : bv 32 := 0x00050913.
Lemma F_6c0f0 : fetch_word Asan.M.loaded_segments (0x6c140 : word) = Some W_6c0f0.
Proof. vm_refl. Qed.
Lemma D_6c0f0 : decode_any W_6c0f0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0f4 : bv 32 := 0x000a8513.
Lemma F_6c0f4 : fetch_word Asan.M.loaded_segments (0x6c144 : word) = Some W_6c0f4.
Proof. vm_refl. Qed.
Lemma D_6c0f4 : decode_any W_6c0f4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0f8 : bv 32 := 0xec0900e3.
Lemma F_6c0f8 : fetch_word Asan.M.loaded_segments (0x6c148 : word) = Some W_6c0f8.
Proof. vm_refl. Qed.
Lemma D_6c0f8 : decode_any W_6c0f8 = Some (Branch BC_EQ 18 0 7872, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r4f2d8_4f480.
Module Na0_code_r50950_509ec.
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

Definition W_6e388 : bv 32 := 0x104240ef.
Lemma F_6e388 : fetch_word Asan.M.loaded_segments (0x6e3d8 : word) = Some W_6e388.
Proof. vm_refl. Qed.
Lemma D_6e388 : decode_any W_6e388 = Some (Jal 1 147716, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e38c : bv 32 := 0x00150b93.
Lemma F_6e38c : fetch_word Asan.M.loaded_segments (0x6e3dc : word) = Some W_6e38c.
Proof. vm_refl. Qed.
Lemma D_6e38c : decode_any W_6e38c = Some (OpImm ALU_ADD 23 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e390 : bv 32 := 0xfffb4513.
Lemma F_6e390 : fetch_word Asan.M.loaded_segments (0x6e3e0 : word) = Some W_6e390.
Proof. vm_refl. Qed.
Lemma D_6e390 : decode_any W_6e390 = Some (OpImm ALU_XOR 10 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e394 : bv 32 := 0x25756e63.
Lemma F_6e394 : fetch_word Asan.M.loaded_segments (0x6e3e4 : word) = Some W_6e394.
Proof. vm_refl. Qed.
Lemma D_6e394 : decode_any W_6e394 = Some (Branch BC_LTU 10 23 604, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e398 : bv 32 := 0xfbfb8513.
Lemma F_6e398 : fetch_word Asan.M.loaded_segments (0x6e3e8 : word) = Some W_6e398.
Proof. vm_refl. Qed.
Lemma D_6e398 : decode_any W_6e398 = Some (OpImm ALU_ADD 10 23 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e39c : bv 32 := 0xfbf00593.
Lemma F_6e39c : fetch_word Asan.M.loaded_segments (0x6e3ec : word) = Some W_6e39c.
Proof. vm_refl. Qed.
Lemma D_6e39c : decode_any W_6e39c = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3a0 : bv 32 := 0x2ca5f063.
Lemma F_6e3a0 : fetch_word Asan.M.loaded_segments (0x6e3f0 : word) = Some W_6e3a0.
Proof. vm_refl. Qed.
Lemma D_6e3a0 : decode_any W_6e3a0 = Some (Branch BC_GEU 11 10 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3a4 : bv 32 := 0x000e9517.
Lemma F_6e3a4 : fetch_word Asan.M.loaded_segments (0x6e3f4 : word) = Some W_6e3a4.
Proof. vm_refl. Qed.
Lemma D_6e3a4 : decode_any W_6e3a4 = Some (Auipc 10 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3a8 : bv 32 := 0x9a453503.
Lemma F_6e3a8 : fetch_word Asan.M.loaded_segments (0x6e3f8 : word) = Some W_6e3a8.
Proof. vm_refl. Qed.
Lemma D_6e3a8 : decode_any W_6e3a8 = Some (Load SZ8 true 10 10 2468, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3ac : bv 32 := 0x017b0633.
Lemma F_6e3ac : fetch_word Asan.M.loaded_segments (0x6e3fc : word) = Some W_6e3ac.
Proof. vm_refl. Qed.
Lemma D_6e3ac : decode_any W_6e3ac = Some (Op ALU_ADD 12 22 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3b0 : bv 32 := 0x00053583.
Lemma F_6e3b0 : fetch_word Asan.M.loaded_segments (0x6e400 : word) = Some W_6e3b0.
Proof. vm_refl. Qed.
Lemma D_6e3b0 : decode_any W_6e3b0 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3b4 : bv 32 := 0x003b5513.
Lemma F_6e3b4 : fetch_word Asan.M.loaded_segments (0x6e404 : word) = Some W_6e3b4.
Proof. vm_refl. Qed.
Lemma D_6e3b4 : decode_any W_6e3b4 = Some (ShiftImm ALU_SRL 10 22 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3b8 : bv 32 := 0xfff60613.
Lemma F_6e3b8 : fetch_word Asan.M.loaded_segments (0x6e408 : word) = Some W_6e3b8.
Proof. vm_refl. Qed.
Lemma D_6e3b8 : decode_any W_6e3b8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3bc : bv 32 := 0x00365693.
Lemma F_6e3bc : fetch_word Asan.M.loaded_segments (0x6e40c : word) = Some W_6e3bc.
Proof. vm_refl. Qed.
Lemma D_6e3bc : decode_any W_6e3bc = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3c0 : bv 32 := 0x00a58533.
Lemma F_6e3c0 : fetch_word Asan.M.loaded_segments (0x6e410 : word) = Some W_6e3c0.
Proof. vm_refl. Qed.
Lemma D_6e3c0 : decode_any W_6e3c0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3c4 : bv 32 := 0x00d585b3.
Lemma F_6e3c4 : fetch_word Asan.M.loaded_segments (0x6e414 : word) = Some W_6e3c4.
Proof. vm_refl. Qed.
Lemma D_6e3c4 : decode_any W_6e3c4 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3c8 : bv 32 := 0xff857693.
Lemma F_6e3c8 : fetch_word Asan.M.loaded_segments (0x6e418 : word) = Some W_6e3c8.
Proof. vm_refl. Qed.
Lemma D_6e3c8 : decode_any W_6e3c8 = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3cc : bv 32 := 0xff85f713.
Lemma F_6e3cc : fetch_word Asan.M.loaded_segments (0x6e41c : word) = Some W_6e3cc.
Proof. vm_refl. Qed.
Lemma D_6e3cc : decode_any W_6e3cc = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3d0 : bv 32 := 0x0006b683.
Lemma F_6e3d0 : fetch_word Asan.M.loaded_segments (0x6e420 : word) = Some W_6e3d0.
Proof. vm_refl. Qed.
Lemma D_6e3d0 : decode_any W_6e3d0 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3d4 : bv 32 := 0x00073703.
Lemma F_6e3d4 : fetch_word Asan.M.loaded_segments (0x6e424 : word) = Some W_6e3d4.
Proof. vm_refl. Qed.
Lemma D_6e3d4 : decode_any W_6e3d4 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3d8 : bv 32 := 0x00d766b3.
Lemma F_6e3d8 : fetch_word Asan.M.loaded_segments (0x6e428 : word) = Some W_6e3d8.
Proof. vm_refl. Qed.
Lemma D_6e3d8 : decode_any W_6e3d8 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e3dc : bv 32 := 0xf00688e3.
Lemma F_6e3dc : fetch_word Asan.M.loaded_segments (0x6e42c : word) = Some W_6e3dc.
Proof. vm_refl. Qed.
Lemma D_6e3dc : decode_any W_6e3dc = Some (Branch BC_EQ 13 0 7952, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e414 : bv 32 := 0x000b0513.
Lemma F_6e414 : fetch_word Asan.M.loaded_segments (0x6e464 : word) = Some W_6e414.
Proof. vm_refl. Qed.
Lemma D_6e414 : decode_any W_6e414 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e418 : bv 32 := 0x000b8593.
Lemma F_6e418 : fetch_word Asan.M.loaded_segments (0x6e468 : word) = Some W_6e418.
Proof. vm_refl. Qed.
Lemma D_6e418 : decode_any W_6e418 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e41c : bv 32 := 0x77d130ef.
Lemma F_6e41c : fetch_word Asan.M.loaded_segments (0x6e46c : word) = Some W_6e41c.
Proof. vm_refl. Qed.
Lemma D_6e41c : decode_any W_6e41c = Some (Jal 1 81788, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e420 : bv 32 := 0xec0506e3.
Lemma F_6e420 : fetch_word Asan.M.loaded_segments (0x6e470 : word) = Some W_6e420.
Proof. vm_refl. Qed.
Lemma D_6e420 : decode_any W_6e420 = Some (Branch BC_EQ 10 0 7884, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r50950_509ec.
Module Na0_code_r50c28_50c30.
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

Definition W_6e660 : bv 32 := 0xda0b9ae3.
Lemma F_6e660 : fetch_word Asan.M.loaded_segments (0x6e6b0 : word) = Some W_6e660.
Proof. vm_refl. Qed.
Lemma D_6e660 : decode_any W_6e660 = Some (Branch BC_NE 23 0 7604, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r50c28_50c30.
Module Na0_code_rb4d74_b4d78.
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

Definition W_b4c30 : bv 32 := 0x00008067.
Lemma F_b4c30 : fetch_word Asan.M.loaded_segments (0xb4c80 : word) = Some W_b4c30.
Proof. vm_refl. Qed.
Lemma D_b4c30 : decode_any W_b4c30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb4d74_b4d78.
Module Na0_code_rb2498_b249c.
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

Definition W_b2354 : bv 32 := 0x02813827.
Lemma F_b2354 : fetch_word Asan.M.loaded_segments (0xb23a4 : word) = Some W_b2354.
Proof. vm_refl. Qed.
Lemma D_b2354 : decode_any W_b2354 = Some (FStore FMT_D 2 8 48, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb2498_b249c.
Module Na0_code_rba91c_ba920.
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

Definition W_ba7d8 : bv 32 := 0x00813427.
Lemma F_ba7d8 : fetch_word Asan.M.loaded_segments (0xba828 : word) = Some W_ba7d8.
Proof. vm_refl. Qed.
Lemma D_ba7d8 : decode_any W_ba7d8 = Some (FStore FMT_D 2 8 8, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rba91c_ba920.
Module Na0_code_rba930_ba934.
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

Definition W_ba7ec : bv 32 := 0x22a50453.
Lemma F_ba7ec : fetch_word Asan.M.loaded_segments (0xba83c : word) = Some W_ba7ec.
Proof. vm_refl. Qed.
Lemma D_ba7ec : decode_any W_ba7ec = Some (Fsgnj F_SGNJ FMT_D 8 10 10, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rba930_ba934.
Module Na0_code_rbae00_bae0c.
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

Definition W_bacbc : bv 32 := 0x00813407.
Lemma F_bacbc : fetch_word Asan.M.loaded_segments (0xbad0c : word) = Some W_bacbc.
Proof. vm_refl. Qed.
Lemma D_bacbc : decode_any W_bacbc = Some (FLoad FMT_D 8 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_bacc0 : bv 32 := 0x06010113.
Lemma F_bacc0 : fetch_word Asan.M.loaded_segments (0xbad10 : word) = Some W_bacc0.
Proof. vm_refl. Qed.
Lemma D_bacc0 : decode_any W_bacc0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_bacc4 : bv 32 := 0x00008067.
Lemma F_bacc4 : fetch_word Asan.M.loaded_segments (0xbad14 : word) = Some W_bacc4.
Proof. vm_refl. Qed.
Lemma D_bacc4 : decode_any W_bacc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbae00_bae0c.
Module Na0_code_rbaea4_baea8.
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

Definition W_bad60 : bv 32 := 0x22840553.
Lemma F_bad60 : fetch_word Asan.M.loaded_segments (0xbadb0 : word) = Some W_bad60.
Proof. vm_refl. Qed.
Lemma D_bad60 : decode_any W_bad60 = Some (Fsgnj F_SGNJ FMT_D 10 8 8, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbaea4_baea8.
Module Na0_code_rbe060_be064.
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

Definition W_bdf1c : bv 32 := 0x02813027.
Lemma F_bdf1c : fetch_word Asan.M.loaded_segments (0xbdf6c : word) = Some W_bdf1c.
Proof. vm_refl. Qed.
Lemma D_bdf1c : decode_any W_bdf1c = Some (FStore FMT_D 2 8 32, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbe060_be064.
Module Na0_code_rbe090_be094.
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

Definition W_bdf4c : bv 32 := 0x22a50453.
Lemma F_bdf4c : fetch_word Asan.M.loaded_segments (0xbdf9c : word) = Some W_bdf4c.
Proof. vm_refl. Qed.
Lemma D_bdf4c : decode_any W_bdf4c = Some (Fsgnj F_SGNJ FMT_D 8 10 10, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbe090_be094.
Module Na0_code_rbe108_be10c.
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

Definition W_bdfc4 : bv 32 := 0xf20007d3.
Lemma F_bdfc4 : fetch_word Asan.M.loaded_segments (0xbe014 : word) = Some W_bdfc4.
Proof. vm_refl. Qed.
Lemma D_bdfc4 : decode_any W_bdfc4 = Some (Fmv FMV_F_X FMT_D 15 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbe108_be10c.
Module Na0_code_rbe120_be124.
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

Definition W_bdfdc : bv 32 := 0xa2f42653.
Lemma F_bdfdc : fetch_word Asan.M.loaded_segments (0xbe02c : word) = Some W_bdfdc.
Proof. vm_refl. Qed.
Lemma D_bdfdc : decode_any W_bdfdc = Some (Fcmp F_EQ FMT_D 12 8 15, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbe120_be124.
Module Na0_code_rbe200_be204.
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

Definition W_be0bc : bv 32 := 0xe2040b53.
Lemma F_be0bc : fetch_word Asan.M.loaded_segments (0xbe10c : word) = Some W_be0bc.
Proof. vm_refl. Qed.
Lemma D_be0bc : decode_any W_be0bc = Some (Fmv FMV_X_F FMT_D 22 8, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbe200_be204.
Module Na0_code_rbe400_be40c.
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

Definition W_be2bc : bv 32 := 0x02013407.
Lemma F_be2bc : fetch_word Asan.M.loaded_segments (0xbe30c : word) = Some W_be2bc.
Proof. vm_refl. Qed.
Lemma D_be2bc : decode_any W_be2bc = Some (FLoad FMT_D 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_be2c0 : bv 32 := 0x08010113.
Lemma F_be2c0 : fetch_word Asan.M.loaded_segments (0xbe310 : word) = Some W_be2c0.
Proof. vm_refl. Qed.
Lemma D_be2c0 : decode_any W_be2c0 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_be2c4 : bv 32 := 0x00008067.
Lemma F_be2c4 : fetch_word Asan.M.loaded_segments (0xbe314 : word) = Some W_be2c4.
Proof. vm_refl. Qed.
Lemma D_be2c4 : decode_any W_be2c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbe400_be40c.
Module Na0_code_rbb5d4_bb5d8.
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

Definition W_bb490 : bv 32 := 0x00008067.
Lemma F_bb490 : fetch_word Asan.M.loaded_segments (0xbb4e0 : word) = Some W_bb490.
Proof. vm_refl. Qed.
Lemma D_bb490 : decode_any W_bb490 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbb5d4_bb5d8.
Module Na0_code_rbdc84_bdc88.
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

Definition W_bdb40 : bv 32 := 0x02813427.
Lemma F_bdb40 : fetch_word Asan.M.loaded_segments (0xbdb90 : word) = Some W_bdb40.
Proof. vm_refl. Qed.
Lemma D_bdb40 : decode_any W_bdb40 = Some (FStore FMT_D 2 8 40, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbdc84_bdc88.
Module Na0_code_rbdcb4_bdcb8.
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

Definition W_bdb70 : bv 32 := 0x22a50453.
Lemma F_bdb70 : fetch_word Asan.M.loaded_segments (0xbdbc0 : word) = Some W_bdb70.
Proof. vm_refl. Qed.
Lemma D_bdb70 : decode_any W_bdb70 = Some (Fsgnj F_SGNJ FMT_D 8 10 10, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbdcb4_bdcb8.
Module Na0_code_rbdd2c_bdd30.
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

Definition W_bdbe8 : bv 32 := 0xf20007d3.
Lemma F_bdbe8 : fetch_word Asan.M.loaded_segments (0xbdc38 : word) = Some W_bdbe8.
Proof. vm_refl. Qed.
Lemma D_bdbe8 : decode_any W_bdbe8 = Some (Fmv FMV_F_X FMT_D 15 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbdd2c_bdd30.
Module Na0_code_rbdd44_bdd48.
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

Definition W_bdc00 : bv 32 := 0xa2f42653.
Lemma F_bdc00 : fetch_word Asan.M.loaded_segments (0xbdc50 : word) = Some W_bdc00.
Proof. vm_refl. Qed.
Lemma D_bdc00 : decode_any W_bdc00 = Some (Fcmp F_EQ FMT_D 12 8 15, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbdd44_bdd48.
Module Na0_code_rbde28_bde2c.
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

Definition W_bdce4 : bv 32 := 0x22842553.
Lemma F_bdce4 : fetch_word Asan.M.loaded_segments (0xbdd34 : word) = Some W_bdce4.
Proof. vm_refl. Qed.
Lemma D_bdce4 : decode_any W_bdce4 = Some (Fsgnj F_SGNJX FMT_D 10 8 8, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbde28_bde2c.
Module Na0_code_rbde40_bde44.
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

Definition W_bdcfc : bv 32 := 0xe2040553.
Lemma F_bdcfc : fetch_word Asan.M.loaded_segments (0xbdd4c : word) = Some W_bdcfc.
Proof. vm_refl. Qed.
Lemma D_bdcfc : decode_any W_bdcfc = Some (Fmv FMV_X_F FMT_D 10 8, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbde40_bde44.
Module Na0_code_rbde88_bde8c.
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

Definition W_bdd44 : bv 32 := 0x22840553.
Lemma F_bdd44 : fetch_word Asan.M.loaded_segments (0xbdd94 : word) = Some W_bdd44.
Proof. vm_refl. Qed.
Lemma D_bdd44 : decode_any W_bdd44 = Some (Fsgnj F_SGNJ FMT_D 10 8 8, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbde88_bde8c.
Module Na0_code_rbe000_be00c.
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

Definition W_bdebc : bv 32 := 0x02813407.
Lemma F_bdebc : fetch_word Asan.M.loaded_segments (0xbdf0c : word) = Some W_bdebc.
Proof. vm_refl. Qed.
Lemma D_bdebc : decode_any W_bdebc = Some (FLoad FMT_D 8 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_bdec0 : bv 32 := 0x08010113.
Lemma F_bdec0 : fetch_word Asan.M.loaded_segments (0xbdf10 : word) = Some W_bdec0.
Proof. vm_refl. Qed.
Lemma D_bdec0 : decode_any W_bdec0 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_bdec4 : bv 32 := 0x00008067.
Lemma F_bdec4 : fetch_word Asan.M.loaded_segments (0xbdf14 : word) = Some W_bdec4.
Proof. vm_refl. Qed.
Lemma D_bdec4 : decode_any W_bdec4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbe000_be00c.
Module Na0_code_rbc538_bc53c.
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

Definition W_bc3f4 : bv 32 := 0x00008067.
Lemma F_bc3f4 : fetch_word Asan.M.loaded_segments (0xbc444 : word) = Some W_bc3f4.
Proof. vm_refl. Qed.
Lemma D_bc3f4 : decode_any W_bc3f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbc538_bc53c.
Module Na0_code_rec64c_ec650.
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

Definition W_f45e8 : bv 32 := 0x00008067.
Lemma F_f45e8 : fetch_word Asan.M.loaded_segments (0xf4638 : word) = Some W_f45e8.
Proof. vm_refl. Qed.
Lemma D_f45e8 : decode_any W_f45e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rec64c_ec650.
Module Na0_code_rd36f8_d36fc.
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

Definition W_f4720 : bv 32 := 0x00008067.
Lemma F_f4720 : fetch_word Asan.M.loaded_segments (0xf4770 : word) = Some W_f4720.
Proof. vm_refl. Qed.
Lemma D_f4720 : decode_any W_f4720 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rd36f8_d36fc.
Module Na0_code_rbea10_bea14.
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

Definition W_be8cc : bv 32 := 0x00008067.
Lemma F_be8cc : fetch_word Asan.M.loaded_segments (0xbe91c : word) = Some W_be8cc.
Proof. vm_refl. Qed.
Lemma D_be8cc : decode_any W_be8cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rbea10_bea14.
Module Na0_code_rb8504_b8508.
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

Definition W_b83c0 : bv 32 := 0x00008067.
Lemma F_b83c0 : fetch_word Asan.M.loaded_segments (0xb8410 : word) = Some W_b83c0.
Proof. vm_refl. Qed.
Lemma D_b83c0 : decode_any W_b83c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb8504_b8508.
Module Na0_code_rb85b4_b85b8.
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

Definition W_b8470 : bv 32 := 0x00008067.
Lemma F_b8470 : fetch_word Asan.M.loaded_segments (0xb84c0 : word) = Some W_b8470.
Proof. vm_refl. Qed.
Lemma D_b8470 : decode_any W_b8470 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb85b4_b85b8.
Module Na0_code_rc2444_c2448.
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

Definition W_cf38c : bv 32 := 0x00008067.
Lemma F_cf38c : fetch_word Asan.M.loaded_segments (0xcf3dc : word) = Some W_cf38c.
Proof. vm_refl. Qed.
Lemma D_cf38c : decode_any W_cf38c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc2444_c2448.
Module Na0_code_rc9038_c903c.
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

Definition W_d4fdc : bv 32 := 0x00008067.
Lemma F_d4fdc : fetch_word Asan.M.loaded_segments (0xd502c : word) = Some W_d4fdc.
Proof. vm_refl. Qed.
Lemma D_d4fdc : decode_any W_d4fdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc9038_c903c.
Module Na0_code_rcba8c_cba90.
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

Definition W_c8634 : bv 32 := 0x00008067.
Lemma F_c8634 : fetch_word Asan.M.loaded_segments (0xc8684 : word) = Some W_c8634.
Proof. vm_refl. Qed.
Lemma D_c8634 : decode_any W_c8634 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rcba8c_cba90.
Module Na0_code_rcc9f0_cc9f4.
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

Definition W_c9f84 : bv 32 := 0x00008067.
Lemma F_c9f84 : fetch_word Asan.M.loaded_segments (0xc9fd4 : word) = Some W_c9f84.
Proof. vm_refl. Qed.
Lemma D_c9f84 : decode_any W_c9f84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rcc9f0_cc9f4.
Module Na0_code_rc9ee0_c9ee4.
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

Definition W_ca5c0 : bv 32 := 0x00008067.
Lemma F_ca5c0 : fetch_word Asan.M.loaded_segments (0xca610 : word) = Some W_ca5c0.
Proof. vm_refl. Qed.
Lemma D_ca5c0 : decode_any W_ca5c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc9ee0_c9ee4.
Module Na0_code_rc9b88_c9b8c.
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

Definition W_ca268 : bv 32 := 0x00008067.
Lemma F_ca268 : fetch_word Asan.M.loaded_segments (0xca2b8 : word) = Some W_ca268.
Proof. vm_refl. Qed.
Lemma D_ca268 : decode_any W_ca268 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc9b88_c9b8c.
Module Na0_code_rca8a8_ca8ac.
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

Definition W_cb750 : bv 32 := 0x00008067.
Lemma F_cb750 : fetch_word Asan.M.loaded_segments (0xcb7a0 : word) = Some W_cb750.
Proof. vm_refl. Qed.
Lemma D_cb750 : decode_any W_cb750 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rca8a8_ca8ac.
Module Na0_code_rcc6a0_cc6a4.
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

Definition W_cca88 : bv 32 := 0x00008067.
Lemma F_cca88 : fetch_word Asan.M.loaded_segments (0xccad8 : word) = Some W_cca88.
Proof. vm_refl. Qed.
Lemma D_cca88 : decode_any W_cca88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rcc6a0_cc6a4.
Module Na0_code_rca75c_ca760.
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

Definition W_cae3c : bv 32 := 0x00008067.
Lemma F_cae3c : fetch_word Asan.M.loaded_segments (0xcae8c : word) = Some W_cae3c.
Proof. vm_refl. Qed.
Lemma D_cae3c : decode_any W_cae3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rca75c_ca760.
Module Na0_code_rb00dc_b00e4.
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

Definition W_f1f6c : bv 32 := 0xf808e06f.
Lemma F_f1f6c : fetch_word Asan.M.loaded_segments (0xf1fbc : word) = Some W_f1f6c.
Proof. vm_refl. Qed.
Lemma D_f1f6c : decode_any W_f1f6c = Some (Jal 0 1632128, 4%Z).
Proof. vm_refl. Qed.

Definition W_f1f70 : bv 32 := 0xffdff06f.
Lemma F_f1f70 : fetch_word Asan.M.loaded_segments (0xf1fc0 : word) = Some W_f1f70.
Proof. vm_refl. Qed.
Lemma D_f1f70 : decode_any W_f1f70 = Some (Jal 0 2097148, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rb00dc_b00e4.
Module Na0_code_ra7e28_a7e2c.
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

Definition W_afb84 : bv 32 := 0x00008067.
Lemma F_afb84 : fetch_word Asan.M.loaded_segments (0xafbd4 : word) = Some W_afb84.
Proof. vm_refl. Qed.
Lemma D_afb84 : decode_any W_afb84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_ra7e28_a7e2c.
Module Na0_code_rf9c14_f9c18.
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

Definition W_11e2c4 : bv 32 := 0x00008067.
Lemma F_11e2c4 : fetch_word Asan.M.loaded_segments (0x11e314 : word) = Some W_11e2c4.
Proof. vm_refl. Qed.
Lemma D_11e2c4 : decode_any W_11e2c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rf9c14_f9c18.
Module Na0_code_rf9cb0_f9cb4.
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

Definition W_11e360 : bv 32 := 0x00008067.
Lemma F_11e360 : fetch_word Asan.M.loaded_segments (0x11e3b0 : word) = Some W_11e360.
Proof. vm_refl. Qed.
Lemma D_11e360 : decode_any W_11e360 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rf9cb0_f9cb4.
Module Na0_code_rc331c_c3320.
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

Definition W_d02d8 : bv 32 := 0x00008067.
Lemma F_d02d8 : fetch_word Asan.M.loaded_segments (0xd0328 : word) = Some W_d02d8.
Proof. vm_refl. Qed.
Lemma D_d02d8 : decode_any W_d02d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc331c_c3320.
Module Na0_code_rc10c4_c10c8.
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

Definition W_c0f80 : bv 32 := 0x00008067.
Lemma F_c0f80 : fetch_word Asan.M.loaded_segments (0xc0fd0 : word) = Some W_c0f80.
Proof. vm_refl. Qed.
Lemma D_c0f80 : decode_any W_c0f80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc10c4_c10c8.
Module Na0_code_rc1d78_c1d7c.
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

Definition W_cecc0 : bv 32 := 0x00008067.
Lemma F_cecc0 : fetch_word Asan.M.loaded_segments (0xced10 : word) = Some W_cecc0.
Proof. vm_refl. Qed.
Lemma D_cecc0 : decode_any W_cecc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc1d78_c1d7c.
Module Na0_code_rae51c_ae520.
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

Definition W_afee4 : bv 32 := 0x00008067.
Lemma F_afee4 : fetch_word Asan.M.loaded_segments (0xaff34 : word) = Some W_afee4.
Proof. vm_refl. Qed.
Lemma D_afee4 : decode_any W_afee4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rae51c_ae520.
Module Na0_code_rc2d28_c2d2c.
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

Definition W_cfce4 : bv 32 := 0x00008067.
Lemma F_cfce4 : fetch_word Asan.M.loaded_segments (0xcfd34 : word) = Some W_cfce4.
Proof. vm_refl. Qed.
Lemma D_cfce4 : decode_any W_cfce4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc2d28_c2d2c.
Module Na0_code_raf0a4_af0a8.
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

Definition W_c6a94 : bv 32 := 0x00008067.
Lemma F_c6a94 : fetch_word Asan.M.loaded_segments (0xc6ae4 : word) = Some W_c6a94.
Proof. vm_refl. Qed.
Lemma D_c6a94 : decode_any W_c6a94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_raf0a4_af0a8.
Module Na0_code_raf24c_af250.
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

Definition W_c6c3c : bv 32 := 0x00008067.
Lemma F_c6c3c : fetch_word Asan.M.loaded_segments (0xc6c8c : word) = Some W_c6c3c.
Proof. vm_refl. Qed.
Lemma D_c6c3c : decode_any W_c6c3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_raf24c_af250.
Module Na0_code_rd5658_d565c.
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

Definition W_f9d08 : bv 32 := 0x00008067.
Lemma F_f9d08 : fetch_word Asan.M.loaded_segments (0xf9d58 : word) = Some W_f9d08.
Proof. vm_refl. Qed.
Lemma D_f9d08 : decode_any W_f9d08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rd5658_d565c.
Module Na0_code_rc737c_c7380.
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

Definition W_c9d1c : bv 32 := 0x00008067.
Lemma F_c9d1c : fetch_word Asan.M.loaded_segments (0xc9d6c : word) = Some W_c9d1c.
Proof. vm_refl. Qed.
Lemma D_c9d1c : decode_any W_c9d1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc737c_c7380.
Module Na0_code_rca1dc_ca1e0.
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

Definition W_ca8bc : bv 32 := 0x00008067.
Lemma F_ca8bc : fetch_word Asan.M.loaded_segments (0xca90c : word) = Some W_ca8bc.
Proof. vm_refl. Qed.
Lemma D_ca8bc : decode_any W_ca8bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rca1dc_ca1e0.
Module Na0_code_rca528_ca52c.
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

Definition W_cac08 : bv 32 := 0x00008067.
Lemma F_cac08 : fetch_word Asan.M.loaded_segments (0xcac58 : word) = Some W_cac08.
Proof. vm_refl. Qed.
Lemma D_cac08 : decode_any W_cac08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rca528_ca52c.
Module Na0_code_rc8964_c8968.
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

Definition W_d49a8 : bv 32 := 0x00008067.
Lemma F_d49a8 : fetch_word Asan.M.loaded_segments (0xd49f8 : word) = Some W_d49a8.
Proof. vm_refl. Qed.
Lemma D_d49a8 : decode_any W_d49a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc8964_c8968.
Module Na0_code_rc83b4_c83b8.
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

Definition W_cb420 : bv 32 := 0x00008067.
Lemma F_cb420 : fetch_word Asan.M.loaded_segments (0xcb470 : word) = Some W_cb420.
Proof. vm_refl. Qed.
Lemma D_cb420 : decode_any W_cb420 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc83b4_c83b8.
Module Na0_code_rc7a14_c7a18.
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

Definition W_d4220 : bv 32 := 0x00008067.
Lemma F_d4220 : fetch_word Asan.M.loaded_segments (0xd4270 : word) = Some W_d4220.
Proof. vm_refl. Qed.
Lemma D_d4220 : decode_any W_d4220 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rc7a14_c7a18.
Module Na0_code_rec304_ec308.
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

Definition W_f41a4 : bv 32 := 0x00008067.
Lemma F_f41a4 : fetch_word Asan.M.loaded_segments (0xf41f4 : word) = Some W_f41a4.
Proof. vm_refl. Qed.
Lemma D_f41a4 : decode_any W_f41a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rec304_ec308.
Module Na0_code_rec4d4_ec4d8.
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

Definition W_f4374 : bv 32 := 0x00008067.
Lemma F_f4374 : fetch_word Asan.M.loaded_segments (0xf43c4 : word) = Some W_f4374.
Proof. vm_refl. Qed.
Lemma D_f4374 : decode_any W_f4374 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rec4d4_ec4d8.
Module Na0_code_rcc128_cc12c.
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

Definition W_cc510 : bv 32 := 0x00008067.
Lemma F_cc510 : fetch_word Asan.M.loaded_segments (0xcc560 : word) = Some W_cc510.
Proof. vm_refl. Qed.
Lemma D_cc510 : decode_any W_cc510 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rcc128_cc12c.
Module Na0_code_rccca8_cccac.
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

Definition W_ccd58 : bv 32 := 0x00008067.
Lemma F_ccd58 : fetch_word Asan.M.loaded_segments (0xccda8 : word) = Some W_ccd58.
Proof. vm_refl. Qed.
Lemma D_ccd58 : decode_any W_ccd58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rccca8_cccac.
Module Na0_code_rcc570_cc574.
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

Definition W_cc958 : bv 32 := 0x00008067.
Lemma F_cc958 : fetch_word Asan.M.loaded_segments (0xcc9a8 : word) = Some W_cc958.
Proof. vm_refl. Qed.
Lemma D_cc958 : decode_any W_cc958 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rcc570_cc574.
Module Na0_code_r6a9a4_6a9e0.
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

Definition W_6c21c : bv 32 := 0x000eb517.
Lemma F_6c21c : fetch_word Asan.M.loaded_segments (0x6c26c : word) = Some W_6c21c.
Proof. vm_refl. Qed.
Lemma D_6c21c : decode_any W_6c21c = Some (Auipc 10 235, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c220 : bv 32 := 0xb2c53503.
Lemma F_6c220 : fetch_word Asan.M.loaded_segments (0x6c270 : word) = Some W_6c220.
Proof. vm_refl. Qed.
Lemma D_6c220 : decode_any W_6c220 = Some (Load SZ8 true 10 10 2860, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c224 : bv 32 := 0x00053583.
Lemma F_6c224 : fetch_word Asan.M.loaded_segments (0x6c274 : word) = Some W_6c224.
Proof. vm_refl. Qed.
Lemma D_6c224 : decode_any W_6c224 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c228 : bv 32 := 0x00348613.
Lemma F_6c228 : fetch_word Asan.M.loaded_segments (0x6c278 : word) = Some W_6c228.
Proof. vm_refl. Qed.
Lemma D_6c228 : decode_any W_6c228 = Some (OpImm ALU_ADD 12 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c22c : bv 32 := 0x0034d513.
Lemma F_6c22c : fetch_word Asan.M.loaded_segments (0x6c27c : word) = Some W_6c22c.
Proof. vm_refl. Qed.
Lemma D_6c22c : decode_any W_6c22c = Some (ShiftImm ALU_SRL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c230 : bv 32 := 0x00365693.
Lemma F_6c230 : fetch_word Asan.M.loaded_segments (0x6c280 : word) = Some W_6c230.
Proof. vm_refl. Qed.
Lemma D_6c230 : decode_any W_6c230 = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c234 : bv 32 := 0x00a58533.
Lemma F_6c234 : fetch_word Asan.M.loaded_segments (0x6c284 : word) = Some W_6c234.
Proof. vm_refl. Qed.
Lemma D_6c234 : decode_any W_6c234 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c238 : bv 32 := 0x00d585b3.
Lemma F_6c238 : fetch_word Asan.M.loaded_segments (0x6c288 : word) = Some W_6c238.
Proof. vm_refl. Qed.
Lemma D_6c238 : decode_any W_6c238 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c23c : bv 32 := 0xff857693.
Lemma F_6c23c : fetch_word Asan.M.loaded_segments (0x6c28c : word) = Some W_6c23c.
Proof. vm_refl. Qed.
Lemma D_6c23c : decode_any W_6c23c = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c240 : bv 32 := 0xff85f713.
Lemma F_6c240 : fetch_word Asan.M.loaded_segments (0x6c290 : word) = Some W_6c240.
Proof. vm_refl. Qed.
Lemma D_6c240 : decode_any W_6c240 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c244 : bv 32 := 0x0006b683.
Lemma F_6c244 : fetch_word Asan.M.loaded_segments (0x6c294 : word) = Some W_6c244.
Proof. vm_refl. Qed.
Lemma D_6c244 : decode_any W_6c244 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c248 : bv 32 := 0x00073703.
Lemma F_6c248 : fetch_word Asan.M.loaded_segments (0x6c298 : word) = Some W_6c248.
Proof. vm_refl. Qed.
Lemma D_6c248 : decode_any W_6c248 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c24c : bv 32 := 0x00d766b3.
Lemma F_6c24c : fetch_word Asan.M.loaded_segments (0x6c29c : word) = Some W_6c24c.
Proof. vm_refl. Qed.
Lemma D_6c24c : decode_any W_6c24c = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c250 : bv 32 := 0x0e069863.
Lemma F_6c250 : fetch_word Asan.M.loaded_segments (0x6c2a0 : word) = Some W_6c250.
Proof. vm_refl. Qed.
Lemma D_6c250 : decode_any W_6c250 = Some (Branch BC_NE 13 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c254 : bv 32 := 0x000ed517.
Lemma F_6c254 : fetch_word Asan.M.loaded_segments (0x6c2a4 : word) = Some W_6c254.
Proof. vm_refl. Qed.
Lemma D_6c254 : decode_any W_6c254 = Some (Auipc 10 237, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r6a9a4_6a9e0.
Module Na0_code_r6cfa8_6cfac.
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

Definition W_74970 : bv 32 := 0x00008067.
Lemma F_74970 : fetch_word Asan.M.loaded_segments (0x749c0 : word) = Some W_74970.
Proof. vm_refl. Qed.
Lemma D_74970 : decode_any W_74970 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r6cfa8_6cfac.
Module Na0_code_r4daac_4dab0.
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

Definition W_6a268 : bv 32 := 0x1dc0206f.
Lemma F_6a268 : fetch_word Asan.M.loaded_segments (0x6a2b8 : word) = Some W_6a268.
Proof. vm_refl. Qed.
Lemma D_6a268 : decode_any W_6a268 = Some (Jal 0 8668, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r4daac_4dab0.
