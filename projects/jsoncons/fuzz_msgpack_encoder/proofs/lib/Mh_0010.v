(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
Module Na0_code_r7fbdc_7fe80.
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

Definition W_a0e9c : bv 32 := 0x00058613.
Lemma F_a0e9c : fetch_word Asan.M.loaded_segments (0xa0eec : word) = Some W_a0e9c.
Proof. vm_refl. Qed.
Lemma D_a0e9c : decode_any W_a0e9c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ea0 : bv 32 := 0x001a1597.
Lemma F_a0ea0 : fetch_word Asan.M.loaded_segments (0xa0ef0 : word) = Some W_a0ea0.
Proof. vm_refl. Qed.
Lemma D_a0ea0 : decode_any W_a0ea0 = Some (Auipc 11 417, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ea4 : bv 32 := 0xa6858593.
Lemma F_a0ea4 : fetch_word Asan.M.loaded_segments (0xa0ef4 : word) = Some W_a0ea4.
Proof. vm_refl. Qed.
Lemma D_a0ea4 : decode_any W_a0ea4 = Some (OpImm ALU_ADD 11 11 2664, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ea8 : bv 32 := 0x00050693.
Lemma F_a0ea8 : fetch_word Asan.M.loaded_segments (0xa0ef8 : word) = Some W_a0ea8.
Proof. vm_refl. Qed.
Lemma D_a0ea8 : decode_any W_a0ea8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0eac : bv 32 := 0x00058513.
Lemma F_a0eac : fetch_word Asan.M.loaded_segments (0xa0efc : word) = Some W_a0eac.
Proof. vm_refl. Qed.
Lemma D_a0eac : decode_any W_a0eac = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0eb0 : bv 32 := 0x00068593.
Lemma F_a0eb0 : fetch_word Asan.M.loaded_segments (0xa0f00 : word) = Some W_a0eb0.
Proof. vm_refl. Qed.
Lemma D_a0eb0 : decode_any W_a0eb0 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0eb4 : bv 32 := 0x00000693.
Lemma F_a0eb4 : fetch_word Asan.M.loaded_segments (0xa0f04 : word) = Some W_a0eb4.
Proof. vm_refl. Qed.
Lemma D_a0eb4 : decode_any W_a0eb4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0eb8 : bv 32 := 0x0040006f.
Lemma F_a0eb8 : fetch_word Asan.M.loaded_segments (0xa0f08 : word) = Some W_a0eb8.
Proof. vm_refl. Qed.
Lemma D_a0eb8 : decode_any W_a0eb8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ebc : bv 32 := 0xf9010113.
Lemma F_a0ebc : fetch_word Asan.M.loaded_segments (0xa0f0c : word) = Some W_a0ebc.
Proof. vm_refl. Qed.
Lemma D_a0ebc : decode_any W_a0ebc = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ec0 : bv 32 := 0x06113423.
Lemma F_a0ec0 : fetch_word Asan.M.loaded_segments (0xa0f10 : word) = Some W_a0ec0.
Proof. vm_refl. Qed.
Lemma D_a0ec0 : decode_any W_a0ec0 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ec4 : bv 32 := 0x06813023.
Lemma F_a0ec4 : fetch_word Asan.M.loaded_segments (0xa0f14 : word) = Some W_a0ec4.
Proof. vm_refl. Qed.
Lemma D_a0ec4 : decode_any W_a0ec4 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ec8 : bv 32 := 0x04913c23.
Lemma F_a0ec8 : fetch_word Asan.M.loaded_segments (0xa0f18 : word) = Some W_a0ec8.
Proof. vm_refl. Qed.
Lemma D_a0ec8 : decode_any W_a0ec8 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ecc : bv 32 := 0x05213823.
Lemma F_a0ecc : fetch_word Asan.M.loaded_segments (0xa0f1c : word) = Some W_a0ecc.
Proof. vm_refl. Qed.
Lemma D_a0ecc : decode_any W_a0ecc = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ed0 : bv 32 := 0x05313423.
Lemma F_a0ed0 : fetch_word Asan.M.loaded_segments (0xa0f20 : word) = Some W_a0ed0.
Proof. vm_refl. Qed.
Lemma D_a0ed0 : decode_any W_a0ed0 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ed4 : bv 32 := 0x05413023.
Lemma F_a0ed4 : fetch_word Asan.M.loaded_segments (0xa0f24 : word) = Some W_a0ed4.
Proof. vm_refl. Qed.
Lemma D_a0ed4 : decode_any W_a0ed4 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ed8 : bv 32 := 0x03513c23.
Lemma F_a0ed8 : fetch_word Asan.M.loaded_segments (0xa0f28 : word) = Some W_a0ed8.
Proof. vm_refl. Qed.
Lemma D_a0ed8 : decode_any W_a0ed8 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0edc : bv 32 := 0x03613823.
Lemma F_a0edc : fetch_word Asan.M.loaded_segments (0xa0f2c : word) = Some W_a0edc.
Proof. vm_refl. Qed.
Lemma D_a0edc : decode_any W_a0edc = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ee0 : bv 32 := 0x03713423.
Lemma F_a0ee0 : fetch_word Asan.M.loaded_segments (0xa0f30 : word) = Some W_a0ee0.
Proof. vm_refl. Qed.
Lemma D_a0ee0 : decode_any W_a0ee0 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ee4 : bv 32 := 0x03813023.
Lemma F_a0ee4 : fetch_word Asan.M.loaded_segments (0xa0f34 : word) = Some W_a0ee4.
Proof. vm_refl. Qed.
Lemma D_a0ee4 : decode_any W_a0ee4 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ee8 : bv 32 := 0x01913c23.
Lemma F_a0ee8 : fetch_word Asan.M.loaded_segments (0xa0f38 : word) = Some W_a0ee8.
Proof. vm_refl. Qed.
Lemma D_a0ee8 : decode_any W_a0ee8 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0eec : bv 32 := 0x00068413.
Lemma F_a0eec : fetch_word Asan.M.loaded_segments (0xa0f3c : word) = Some W_a0eec.
Proof. vm_refl. Qed.
Lemma D_a0eec : decode_any W_a0eec = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ef0 : bv 32 := 0x00050493.
Lemma F_a0ef0 : fetch_word Asan.M.loaded_segments (0xa0f40 : word) = Some W_a0ef0.
Proof. vm_refl. Qed.
Lemma D_a0ef0 : decode_any W_a0ef0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ef4 : bv 32 := 0x00b13423.
Lemma F_a0ef4 : fetch_word Asan.M.loaded_segments (0xa0f44 : word) = Some W_a0ef4.
Proof. vm_refl. Qed.
Lemma D_a0ef4 : decode_any W_a0ef4 = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ef8 : bv 32 := 0x00c13823.
Lemma F_a0ef8 : fetch_word Asan.M.loaded_segments (0xa0f48 : word) = Some W_a0ef8.
Proof. vm_refl. Qed.
Lemma D_a0ef8 : decode_any W_a0ef8 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0efc : bv 32 := 0x00068463.
Lemma F_a0efc : fetch_word Asan.M.loaded_segments (0xa0f4c : word) = Some W_a0efc.
Proof. vm_refl. Qed.
Lemma D_a0efc : decode_any W_a0efc = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f04 : bv 32 := 0x0006069b.
Lemma F_a0f04 : fetch_word Asan.M.loaded_segments (0xa0f54 : word) = Some W_a0f04.
Proof. vm_refl. Qed.
Lemma D_a0f04 : decode_any W_a0f04 = Some (OpImm32 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f08 : bv 32 := 0x00000513.
Lemma F_a0f08 : fetch_word Asan.M.loaded_segments (0xa0f58 : word) = Some W_a0f08.
Proof. vm_refl. Qed.
Lemma D_a0f08 : decode_any W_a0f08 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f0c : bv 32 := 0x1c068a63.
Lemma F_a0f0c : fetch_word Asan.M.loaded_segments (0xa0f5c : word) = Some W_a0f0c.
Proof. vm_refl. Qed.
Lemma D_a0f0c : decode_any W_a0f0c = Some (Branch BC_EQ 13 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f10 : bv 32 := 0x1c058863.
Lemma F_a0f10 : fetch_word Asan.M.loaded_segments (0xa0f60 : word) = Some W_a0f10.
Proof. vm_refl. Qed.
Lemma D_a0f10 : decode_any W_a0f10 = Some (Branch BC_EQ 11 0 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f14 : bv 32 := 0x02065693.
Lemma F_a0f14 : fetch_word Asan.M.loaded_segments (0xa0f64 : word) = Some W_a0f14.
Proof. vm_refl. Qed.
Lemma D_a0f14 : decode_any W_a0f14 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f18 : bv 32 := 0xfff00513.
Lemma F_a0f18 : fetch_word Asan.M.loaded_segments (0xa0f68 : word) = Some W_a0f18.
Proof. vm_refl. Qed.
Lemma D_a0f18 : decode_any W_a0f18 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f1c : bv 32 := 0xfff6f717.
Lemma F_a0f1c : fetch_word Asan.M.loaded_segments (0xa0f6c : word) = Some W_a0f1c.
Proof. vm_refl. Qed.
Lemma D_a0f1c : decode_any W_a0f1c = Some (Auipc 14 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f20 : bv 32 := 0xfff6f797.
Lemma F_a0f20 : fetch_word Asan.M.loaded_segments (0xa0f70 : word) = Some W_a0f20.
Proof. vm_refl. Qed.
Lemma D_a0f20 : decode_any W_a0f20 = Some (Auipc 15 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f24 : bv 32 := 0x02055513.
Lemma F_a0f24 : fetch_word Asan.M.loaded_segments (0xa0f74 : word) = Some W_a0f24.
Proof. vm_refl. Qed.
Lemma D_a0f24 : decode_any W_a0f24 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f28 : bv 32 := 0x3b87b783.
Lemma F_a0f28 : fetch_word Asan.M.loaded_segments (0xa0f78 : word) = Some W_a0f28.
Proof. vm_refl. Qed.
Lemma D_a0f28 : decode_any W_a0f28 = Some (Load SZ8 true 15 15 952, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f2c : bv 32 := 0x00a67633.
Lemma F_a0f2c : fetch_word Asan.M.loaded_segments (0xa0f7c : word) = Some W_a0f2c.
Proof. vm_refl. Qed.
Lemma D_a0f2c : decode_any W_a0f2c = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f30 : bv 32 := 0xfff6f517.
Lemma F_a0f30 : fetch_word Asan.M.loaded_segments (0xa0f80 : word) = Some W_a0f30.
Proof. vm_refl. Qed.
Lemma D_a0f30 : decode_any W_a0f30 = Some (Auipc 10 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f34 : bv 32 := 0x4c053803.
Lemma F_a0f34 : fetch_word Asan.M.loaded_segments (0xa0f84 : word) = Some W_a0f34.
Proof. vm_refl. Qed.
Lemma D_a0f34 : decode_any W_a0f34 = Some (Load SZ8 true 16 10 1216, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f38 : bv 32 := 0x37c73503.
Lemma F_a0f38 : fetch_word Asan.M.loaded_segments (0xa0f88 : word) = Some W_a0f38.
Proof. vm_refl. Qed.
Lemma D_a0f38 : decode_any W_a0f38 = Some (Load SZ8 true 10 14 892, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f3c : bv 32 := 0x02f60733.
Lemma F_a0f3c : fetch_word Asan.M.loaded_segments (0xa0f8c : word) = Some W_a0f3c.
Proof. vm_refl. Qed.
Lemma D_a0f3c : decode_any W_a0f3c = Some (Mul M_MUL 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f40 : bv 32 := 0x00361793.
Lemma F_a0f40 : fetch_word Asan.M.loaded_segments (0xa0f90 : word) = Some W_a0f40.
Proof. vm_refl. Qed.
Lemma D_a0f40 : decode_any W_a0f40 = Some (ShiftImm ALU_SLL 15 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f44 : bv 32 := 0x01074633.
Lemma F_a0f44 : fetch_word Asan.M.loaded_segments (0xa0f94 : word) = Some W_a0f44.
Proof. vm_refl. Qed.
Lemma D_a0f44 : decode_any W_a0f44 = Some (Op ALU_XOR 12 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f48 : bv 32 := 0x00f58733.
Lemma F_a0f48 : fetch_word Asan.M.loaded_segments (0xa0f98 : word) = Some W_a0f48.
Proof. vm_refl. Qed.
Lemma D_a0f48 : decode_any W_a0f48 = Some (Op ALU_ADD 14 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f4c : bv 32 := 0x0005b783.
Lemma F_a0f4c : fetch_word Asan.M.loaded_segments (0xa0f9c : word) = Some W_a0f4c.
Proof. vm_refl. Qed.
Lemma D_a0f4c : decode_any W_a0f4c = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f50 : bv 32 := 0x00858593.
Lemma F_a0f50 : fetch_word Asan.M.loaded_segments (0xa0fa0 : word) = Some W_a0f50.
Proof. vm_refl. Qed.
Lemma D_a0f50 : decode_any W_a0f50 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f54 : bv 32 := 0x02a787b3.
Lemma F_a0f54 : fetch_word Asan.M.loaded_segments (0xa0fa4 : word) = Some W_a0f54.
Proof. vm_refl. Qed.
Lemma D_a0f54 : decode_any W_a0f54 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f58 : bv 32 := 0x02f7d813.
Lemma F_a0f58 : fetch_word Asan.M.loaded_segments (0xa0fa8 : word) = Some W_a0f58.
Proof. vm_refl. Qed.
Lemma D_a0f58 : decode_any W_a0f58 = Some (ShiftImm ALU_SRL 16 15 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f5c : bv 32 := 0x00f847b3.
Lemma F_a0f5c : fetch_word Asan.M.loaded_segments (0xa0fac : word) = Some W_a0f5c.
Proof. vm_refl. Qed.
Lemma D_a0f5c : decode_any W_a0f5c = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f60 : bv 32 := 0x02a787b3.
Lemma F_a0f60 : fetch_word Asan.M.loaded_segments (0xa0fb0 : word) = Some W_a0f60.
Proof. vm_refl. Qed.
Lemma D_a0f60 : decode_any W_a0f60 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f64 : bv 32 := 0x00c7c633.
Lemma F_a0f64 : fetch_word Asan.M.loaded_segments (0xa0fb4 : word) = Some W_a0f64.
Proof. vm_refl. Qed.
Lemma D_a0f64 : decode_any W_a0f64 = Some (Op ALU_XOR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f68 : bv 32 := 0x02a60633.
Lemma F_a0f68 : fetch_word Asan.M.loaded_segments (0xa0fb8 : word) = Some W_a0f68.
Proof. vm_refl. Qed.
Lemma D_a0f68 : decode_any W_a0f68 = Some (Mul M_MUL 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f6c : bv 32 := 0xfee590e3.
Lemma F_a0f6c : fetch_word Asan.M.loaded_segments (0xa0fbc : word) = Some W_a0f6c.
Proof. vm_refl. Qed.
Lemma D_a0f6c : decode_any W_a0f6c = Some (Branch BC_NE 11 14 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f70 : bv 32 := 0x00010b37.
Lemma F_a0f70 : fetch_word Asan.M.loaded_segments (0xa0fc0 : word) = Some W_a0f70.
Proof. vm_refl. Qed.
Lemma D_a0f70 : decode_any W_a0f70 = Some (Lui 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f74 : bv 32 := 0x80000bb7.
Lemma F_a0f74 : fetch_word Asan.M.loaded_segments (0xa0fc4 : word) = Some W_a0f74.
Proof. vm_refl. Qed.
Lemma D_a0f74 : decode_any W_a0f74 = Some (Lui 23 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f78 : bv 32 := 0x02a685b3.
Lemma F_a0f78 : fetch_word Asan.M.loaded_segments (0xa0fc8 : word) = Some W_a0f78.
Proof. vm_refl. Qed.
Lemma D_a0f78 : decode_any W_a0f78 = Some (Mul M_MUL 11 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f7c : bv 32 := 0x004006b7.
Lemma F_a0f7c : fetch_word Asan.M.loaded_segments (0xa0fcc : word) = Some W_a0f7c.
Proof. vm_refl. Qed.
Lemma D_a0f7c : decode_any W_a0f7c = Some (Lui 13 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f80 : bv 32 := 0xfffb0b1b.
Lemma F_a0f80 : fetch_word Asan.M.loaded_segments (0xa0fd0 : word) = Some W_a0f80.
Proof. vm_refl. Qed.
Lemma D_a0f80 : decode_any W_a0f80 = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f84 : bv 32 := 0xfffb8b9b.
Lemma F_a0f84 : fetch_word Asan.M.loaded_segments (0xa0fd4 : word) = Some W_a0f84.
Proof. vm_refl. Qed.
Lemma D_a0f84 : decode_any W_a0f84 = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f88 : bv 32 := 0x02f5d713.
Lemma F_a0f88 : fetch_word Asan.M.loaded_segments (0xa0fd8 : word) = Some W_a0f88.
Proof. vm_refl. Qed.
Lemma D_a0f88 : decode_any W_a0f88 = Some (ShiftImm ALU_SRL 14 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f8c : bv 32 := 0x00b745b3.
Lemma F_a0f8c : fetch_word Asan.M.loaded_segments (0xa0fdc : word) = Some W_a0f8c.
Proof. vm_refl. Qed.
Lemma D_a0f8c : decode_any W_a0f8c = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f90 : bv 32 := 0x02a585b3.
Lemma F_a0f90 : fetch_word Asan.M.loaded_segments (0xa0fe0 : word) = Some W_a0f90.
Proof. vm_refl. Qed.
Lemma D_a0f90 : decode_any W_a0f90 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f94 : bv 32 := 0x00c5c5b3.
Lemma F_a0f94 : fetch_word Asan.M.loaded_segments (0xa0fe4 : word) = Some W_a0f94.
Proof. vm_refl. Qed.
Lemma D_a0f94 : decode_any W_a0f94 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f98 : bv 32 := 0x02a585b3.
Lemma F_a0f98 : fetch_word Asan.M.loaded_segments (0xa0fe8 : word) = Some W_a0f98.
Proof. vm_refl. Qed.
Lemma D_a0f98 : decode_any W_a0f98 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0f9c : bv 32 := 0x02f5d613.
Lemma F_a0f9c : fetch_word Asan.M.loaded_segments (0xa0fec : word) = Some W_a0f9c.
Proof. vm_refl. Qed.
Lemma D_a0f9c : decode_any W_a0f9c = Some (ShiftImm ALU_SRL 12 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fa0 : bv 32 := 0x00b645b3.
Lemma F_a0fa0 : fetch_word Asan.M.loaded_segments (0xa0ff0 : word) = Some W_a0fa0.
Proof. vm_refl. Qed.
Lemma D_a0fa0 : decode_any W_a0fa0 = Some (Op ALU_XOR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fa4 : bv 32 := 0x02a58533.
Lemma F_a0fa4 : fetch_word Asan.M.loaded_segments (0xa0ff4 : word) = Some W_a0fa4.
Proof. vm_refl. Qed.
Lemma D_a0fa4 : decode_any W_a0fa4 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fa8 : bv 32 := 0x02f55593.
Lemma F_a0fa8 : fetch_word Asan.M.loaded_segments (0xa0ff8 : word) = Some W_a0fa8.
Proof. vm_refl. Qed.
Lemma D_a0fa8 : decode_any W_a0fa8 = Some (ShiftImm ALU_SRL 11 10 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fac : bv 32 := 0x00a5c9b3.
Lemma F_a0fac : fetch_word Asan.M.loaded_segments (0xa0ffc : word) = Some W_a0fac.
Proof. vm_refl. Qed.
Lemma D_a0fac : decode_any W_a0fac = Some (Op ALU_XOR 19 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fb0 : bv 32 := 0x02c99513.
Lemma F_a0fb0 : fetch_word Asan.M.loaded_segments (0xa1000 : word) = Some W_a0fb0.
Proof. vm_refl. Qed.
Lemma D_a0fb0 : decode_any W_a0fb0 = Some (ShiftImm ALU_SLL 10 19 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fb4 : bv 32 := 0x02a55513.
Lemma F_a0fb4 : fetch_word Asan.M.loaded_segments (0xa1004 : word) = Some W_a0fb4.
Proof. vm_refl. Qed.
Lemma D_a0fb4 : decode_any W_a0fb4 = Some (ShiftImm ALU_SRL 10 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fb8 : bv 32 := 0x00a48933.
Lemma F_a0fb8 : fetch_word Asan.M.loaded_segments (0xa1008 : word) = Some W_a0fb8.
Proof. vm_refl. Qed.
Lemma D_a0fb8 : decode_any W_a0fb8 = Some (Op ALU_ADD 18 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fbc : bv 32 := 0x00092503.
Lemma F_a0fbc : fetch_word Asan.M.loaded_segments (0xa100c : word) = Some W_a0fbc.
Proof. vm_refl. Qed.
Lemma D_a0fbc : decode_any W_a0fbc = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fc0 : bv 32 := 0x01068c1b.
Lemma F_a0fc0 : fetch_word Asan.M.loaded_segments (0xa1010 : word) = Some W_a0fc0.
Proof. vm_refl. Qed.
Lemma D_a0fc0 : decode_any W_a0fc0 = Some (OpImm32 24 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fc4 : bv 32 := 0x01848c33.
Lemma F_a0fc4 : fetch_word Asan.M.loaded_segments (0xa1014 : word) = Some W_a0fc4.
Proof. vm_refl. Qed.
Lemma D_a0fc4 : decode_any W_a0fc4 = Some (Op ALU_ADD 24 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fc8 : bv 32 := 0x0230000f.
Lemma F_a0fc8 : fetch_word Asan.M.loaded_segments (0xa1018 : word) = Some W_a0fc8.
Proof. vm_refl. Qed.
Lemma D_a0fc8 : decode_any W_a0fc8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fcc : bv 32 := 0x01757cb3.
Lemma F_a0fcc : fetch_word Asan.M.loaded_segments (0xa101c : word) = Some W_a0fcc.
Proof. vm_refl. Qed.
Lemma D_a0fcc : decode_any W_a0fcc = Some (Op ALU_AND 25 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fd0 : bv 32 := 0x0086869b.
Lemma F_a0fd0 : fetch_word Asan.M.loaded_segments (0xa1020 : word) = Some W_a0fd0.
Proof. vm_refl. Qed.
Lemma D_a0fd0 : decode_any W_a0fd0 = Some (OpImm32 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fd4 : bv 32 := 0x00d48a33.
Lemma F_a0fd4 : fetch_word Asan.M.loaded_segments (0xa1024 : word) = Some W_a0fd4.
Proof. vm_refl. Qed.
Lemma D_a0fd4 : decode_any W_a0fd4 = Some (Op ALU_ADD 20 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fd8 : bv 32 := 0x000c8593.
Lemma F_a0fd8 : fetch_word Asan.M.loaded_segments (0xa1028 : word) = Some W_a0fd8.
Proof. vm_refl. Qed.
Lemma D_a0fd8 : decode_any W_a0fd8 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fdc : bv 32 := 0x04058c63.
Lemma F_a0fdc : fetch_word Asan.M.loaded_segments (0xa102c : word) = Some W_a0fdc.
Proof. vm_refl. Qed.
Lemma D_a0fdc : decode_any W_a0fdc = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fe0 : bv 32 := 0x00058513.
Lemma F_a0fe0 : fetch_word Asan.M.loaded_segments (0xa1030 : word) = Some W_a0fe0.
Proof. vm_refl. Qed.
Lemma D_a0fe0 : decode_any W_a0fe0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fe4 : bv 32 := 0x0105d59b.
Lemma F_a0fe4 : fetch_word Asan.M.loaded_segments (0xa1034 : word) = Some W_a0fe4.
Proof. vm_refl. Qed.
Lemma D_a0fe4 : decode_any W_a0fe4 = Some (ShiftImm32 ALU_SRL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fe8 : bv 32 := 0x00359613.
Lemma F_a0fe8 : fetch_word Asan.M.loaded_segments (0xa1038 : word) = Some W_a0fe8.
Proof. vm_refl. Qed.
Lemma D_a0fe8 : decode_any W_a0fe8 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fec : bv 32 := 0x00cc0633.
Lemma F_a0fec : fetch_word Asan.M.loaded_segments (0xa103c : word) = Some W_a0fec.
Proof. vm_refl. Qed.
Lemma D_a0fec : decode_any W_a0fec = Some (Op ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ff0 : bv 32 := 0x00063603.
Lemma F_a0ff0 : fetch_word Asan.M.loaded_segments (0xa1040 : word) = Some W_a0ff0.
Proof. vm_refl. Qed.
Lemma D_a0ff0 : decode_any W_a0ff0 = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ff4 : bv 32 := 0x02060463.
Lemma F_a0ff4 : fetch_word Asan.M.loaded_segments (0xa1044 : word) = Some W_a0ff4.
Proof. vm_refl. Qed.
Lemma D_a0ff4 : decode_any W_a0ff4 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ff8 : bv 32 := 0x02051593.
Lemma F_a0ff8 : fetch_word Asan.M.loaded_segments (0xa1048 : word) = Some W_a0ff8.
Proof. vm_refl. Qed.
Lemma D_a0ff8 : decode_any W_a0ff8 = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ffc : bv 32 := 0x0205d593.
Lemma F_a0ffc : fetch_word Asan.M.loaded_segments (0xa104c : word) = Some W_a0ffc.
Proof. vm_refl. Qed.
Lemma D_a0ffc : decode_any W_a0ffc = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1000 : bv 32 := 0x0165f5b3.
Lemma F_a1000 : fetch_word Asan.M.loaded_segments (0xa1050 : word) = Some W_a1000.
Proof. vm_refl. Qed.
Lemma D_a1000 : decode_any W_a1000 = Some (Op ALU_AND 11 11 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1004 : bv 32 := 0x00459593.
Lemma F_a1004 : fetch_word Asan.M.loaded_segments (0xa1054 : word) = Some W_a1004.
Proof. vm_refl. Qed.
Lemma D_a1004 : decode_any W_a1004 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1008 : bv 32 := 0x00b605b3.
Lemma F_a1008 : fetch_word Asan.M.loaded_segments (0xa1058 : word) = Some W_a1008.
Proof. vm_refl. Qed.
Lemma D_a1008 : decode_any W_a1008 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a100c : bv 32 := 0x0005b603.
Lemma F_a100c : fetch_word Asan.M.loaded_segments (0xa105c : word) = Some W_a100c.
Proof. vm_refl. Qed.
Lemma D_a100c : decode_any W_a100c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1010 : bv 32 := 0x0085a583.
Lemma F_a1010 : fetch_word Asan.M.loaded_segments (0xa1060 : word) = Some W_a1010.
Proof. vm_refl. Qed.
Lemma D_a1010 : decode_any W_a1010 = Some (Load SZ4 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1014 : bv 32 := 0xfcc994e3.
Lemma F_a1014 : fetch_word Asan.M.loaded_segments (0xa1064 : word) = Some W_a1014.
Proof. vm_refl. Qed.
Lemma D_a1014 : decode_any W_a1014 = Some (Branch BC_NE 19 12 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1018 : bv 32 := 0x0c80006f.
Lemma F_a1018 : fetch_word Asan.M.loaded_segments (0xa1068 : word) = Some W_a1018.
Proof. vm_refl. Qed.
Lemma D_a1018 : decode_any W_a1018 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1034 : bv 32 := 0x00090513.
Lemma F_a1034 : fetch_word Asan.M.loaded_segments (0xa1084 : word) = Some W_a1034.
Proof. vm_refl. Qed.
Lemma D_a1034 : decode_any W_a1034 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1038 : bv 32 := 0x5f8000ef.
Lemma F_a1038 : fetch_word Asan.M.loaded_segments (0xa1088 : word) = Some W_a1038.
Proof. vm_refl. Qed.
Lemma D_a1038 : decode_any W_a1038 = Some (Jal 1 1528, 4%Z).
Proof. vm_refl. Qed.

Definition W_a103c : bv 32 := 0x00050a93.
Lemma F_a103c : fetch_word Asan.M.loaded_segments (0xa108c : word) = Some W_a103c.
Proof. vm_refl. Qed.
Lemma D_a103c : decode_any W_a103c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1040 : bv 32 := 0x03950663.
Lemma F_a1040 : fetch_word Asan.M.loaded_segments (0xa1090 : word) = Some W_a1040.
Proof. vm_refl. Qed.
Lemma D_a1040 : decode_any W_a1040 = Some (Branch BC_EQ 10 25 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a106c : bv 32 := 0x00400537.
Lemma F_a106c : fetch_word Asan.M.loaded_segments (0xa10bc : word) = Some W_a106c.
Proof. vm_refl. Qed.
Lemma D_a106c : decode_any W_a106c = Some (Lui 10 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1070 : bv 32 := 0x00a48533.
Lemma F_a1070 : fetch_word Asan.M.loaded_segments (0xa10c0 : word) = Some W_a1070.
Proof. vm_refl. Qed.
Lemma D_a1070 : decode_any W_a1070 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1074 : bv 32 := 0x00100593.
Lemma F_a1074 : fetch_word Asan.M.loaded_segments (0xa10c4 : word) = Some W_a1074.
Proof. vm_refl. Qed.
Lemma D_a1074 : decode_any W_a1074 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1078 : bv 32 := 0x00b5252f.
Lemma F_a1078 : fetch_word Asan.M.loaded_segments (0xa10c8 : word) = Some W_a1078.
Proof. vm_refl. Qed.
Lemma D_a1078 : decode_any W_a1078 = Some (Amo AMO_ADD AW false false 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a107c : bv 32 := 0x0015051b.
Lemma F_a107c : fetch_word Asan.M.loaded_segments (0xa10cc : word) = Some W_a107c.
Proof. vm_refl. Qed.
Lemma D_a107c : decode_any W_a107c = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1080 : bv 32 := 0x02051493.
Lemma F_a1080 : fetch_word Asan.M.loaded_segments (0xa10d0 : word) = Some W_a1080.
Proof. vm_refl. Qed.
Lemma D_a1080 : decode_any W_a1080 = Some (ShiftImm ALU_SLL 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1084 : bv 32 := 0x0204d493.
Lemma F_a1084 : fetch_word Asan.M.loaded_segments (0xa10d4 : word) = Some W_a1084.
Proof. vm_refl. Qed.
Lemma D_a1084 : decode_any W_a1084 = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1088 : bv 32 := 0x08054663.
Lemma F_a1088 : fetch_word Asan.M.loaded_segments (0xa10d8 : word) = Some W_a1088.
Proof. vm_refl. Qed.
Lemma D_a1088 : decode_any W_a1088 = Some (Branch BC_LT 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_a108c : bv 32 := 0x00050b93.
Lemma F_a108c : fetch_word Asan.M.loaded_segments (0xa10dc : word) = Some W_a108c.
Proof. vm_refl. Qed.
Lemma D_a108c : decode_any W_a108c = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1090 : bv 32 := 0x0104d593.
Lemma F_a1090 : fetch_word Asan.M.loaded_segments (0xa10e0 : word) = Some W_a1090.
Proof. vm_refl. Qed.
Lemma D_a1090 : decode_any W_a1090 = Some (ShiftImm ALU_SRL 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1094 : bv 32 := 0x00359513.
Lemma F_a1094 : fetch_word Asan.M.loaded_segments (0xa10e4 : word) = Some W_a1094.
Proof. vm_refl. Qed.
Lemma D_a1094 : decode_any W_a1094 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1098 : bv 32 := 0x00ac0533.
Lemma F_a1098 : fetch_word Asan.M.loaded_segments (0xa10e8 : word) = Some W_a1098.
Proof. vm_refl. Qed.
Lemma D_a1098 : decode_any W_a1098 = Some (Op ALU_ADD 10 24 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a109c : bv 32 := 0x00053503.
Lemma F_a109c : fetch_word Asan.M.loaded_segments (0xa10ec : word) = Some W_a109c.
Proof. vm_refl. Qed.
Lemma D_a109c : decode_any W_a109c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10a0 : bv 32 := 0x08050a63.
Lemma F_a10a0 : fetch_word Asan.M.loaded_segments (0xa10f0 : word) = Some W_a10a0.
Proof. vm_refl. Qed.
Lemma D_a10a0 : decode_any W_a10a0 = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10a4 : bv 32 := 0x0164f5b3.
Lemma F_a10a4 : fetch_word Asan.M.loaded_segments (0xa10f4 : word) = Some W_a10a4.
Proof. vm_refl. Qed.
Lemma D_a10a4 : decode_any W_a10a4 = Some (Op ALU_AND 11 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10a8 : bv 32 := 0x00459593.
Lemma F_a10a8 : fetch_word Asan.M.loaded_segments (0xa10f8 : word) = Some W_a10a8.
Proof. vm_refl. Qed.
Lemma D_a10a8 : decode_any W_a10a8 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10ac : bv 32 := 0x00b504b3.
Lemma F_a10ac : fetch_word Asan.M.loaded_segments (0xa10fc : word) = Some W_a10ac.
Proof. vm_refl. Qed.
Lemma D_a10ac : decode_any W_a10ac = Some (Op ALU_ADD 9 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10b0 : bv 32 := 0x00810613.
Lemma F_a10b0 : fetch_word Asan.M.loaded_segments (0xa1100 : word) = Some W_a10b0.
Proof. vm_refl. Qed.
Lemma D_a10b0 : decode_any W_a10b0 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10b4 : bv 32 := 0x00048513.
Lemma F_a10b4 : fetch_word Asan.M.loaded_segments (0xa1104 : word) = Some W_a10b4.
Proof. vm_refl. Qed.
Lemma D_a10b4 : decode_any W_a10b4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10b8 : bv 32 := 0x00000593.
Lemma F_a10b8 : fetch_word Asan.M.loaded_segments (0xa1108 : word) = Some W_a10b8.
Proof. vm_refl. Qed.
Lemma D_a10b8 : decode_any W_a10b8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10bc : bv 32 := 0x00098693.
Lemma F_a10bc : fetch_word Asan.M.loaded_segments (0xa110c : word) = Some W_a10bc.
Proof. vm_refl. Qed.
Lemma D_a10bc : decode_any W_a10bc = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10c0 : bv 32 := 0xaf5ff0ef.
Lemma F_a10c0 : fetch_word Asan.M.loaded_segments (0xa1110 : word) = Some W_a10c0.
Proof. vm_refl. Qed.
Lemma D_a10c0 : decode_any W_a10c0 = Some (Jal 1 2095860, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10c4 : bv 32 := 0x0154a423.
Lemma F_a10c4 : fetch_word Asan.M.loaded_segments (0xa1114 : word) = Some W_a10c4.
Proof. vm_refl. Qed.
Lemma D_a10c4 : decode_any W_a10c4 = Some (Store SZ4 9 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10c8 : bv 32 := 0x0310000f.
Lemma F_a10c8 : fetch_word Asan.M.loaded_segments (0xa1118 : word) = Some W_a10c8.
Proof. vm_refl. Qed.
Lemma D_a10c8 : decode_any W_a10c8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10cc : bv 32 := 0x000b8513.
Lemma F_a10cc : fetch_word Asan.M.loaded_segments (0xa111c : word) = Some W_a10cc.
Proof. vm_refl. Qed.
Lemma D_a10cc : decode_any W_a10cc = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10d0 : bv 32 := 0x01792023.
Lemma F_a10d0 : fetch_word Asan.M.loaded_segments (0xa1120 : word) = Some W_a10d0.
Proof. vm_refl. Qed.
Lemma D_a10d0 : decode_any W_a10d0 = Some (Store SZ4 18 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10d4 : bv 32 := 0x00040663.
Lemma F_a10d4 : fetch_word Asan.M.loaded_segments (0xa1124 : word) = Some W_a10d4.
Proof. vm_refl. Qed.
Lemma D_a10d4 : decode_any W_a10d4 = Some (Branch BC_EQ 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10e0 : bv 32 := 0x06813083.
Lemma F_a10e0 : fetch_word Asan.M.loaded_segments (0xa1130 : word) = Some W_a10e0.
Proof. vm_refl. Qed.
Lemma D_a10e0 : decode_any W_a10e0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10e4 : bv 32 := 0x06013403.
Lemma F_a10e4 : fetch_word Asan.M.loaded_segments (0xa1134 : word) = Some W_a10e4.
Proof. vm_refl. Qed.
Lemma D_a10e4 : decode_any W_a10e4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10e8 : bv 32 := 0x05813483.
Lemma F_a10e8 : fetch_word Asan.M.loaded_segments (0xa1138 : word) = Some W_a10e8.
Proof. vm_refl. Qed.
Lemma D_a10e8 : decode_any W_a10e8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10ec : bv 32 := 0x05013903.
Lemma F_a10ec : fetch_word Asan.M.loaded_segments (0xa113c : word) = Some W_a10ec.
Proof. vm_refl. Qed.
Lemma D_a10ec : decode_any W_a10ec = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10f0 : bv 32 := 0x04813983.
Lemma F_a10f0 : fetch_word Asan.M.loaded_segments (0xa1140 : word) = Some W_a10f0.
Proof. vm_refl. Qed.
Lemma D_a10f0 : decode_any W_a10f0 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10f4 : bv 32 := 0x04013a03.
Lemma F_a10f4 : fetch_word Asan.M.loaded_segments (0xa1144 : word) = Some W_a10f4.
Proof. vm_refl. Qed.
Lemma D_a10f4 : decode_any W_a10f4 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10f8 : bv 32 := 0x03813a83.
Lemma F_a10f8 : fetch_word Asan.M.loaded_segments (0xa1148 : word) = Some W_a10f8.
Proof. vm_refl. Qed.
Lemma D_a10f8 : decode_any W_a10f8 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10fc : bv 32 := 0x03013b03.
Lemma F_a10fc : fetch_word Asan.M.loaded_segments (0xa114c : word) = Some W_a10fc.
Proof. vm_refl. Qed.
Lemma D_a10fc : decode_any W_a10fc = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1100 : bv 32 := 0x02813b83.
Lemma F_a1100 : fetch_word Asan.M.loaded_segments (0xa1150 : word) = Some W_a1100.
Proof. vm_refl. Qed.
Lemma D_a1100 : decode_any W_a1100 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1104 : bv 32 := 0x02013c03.
Lemma F_a1104 : fetch_word Asan.M.loaded_segments (0xa1154 : word) = Some W_a1104.
Proof. vm_refl. Qed.
Lemma D_a1104 : decode_any W_a1104 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1108 : bv 32 := 0x01813c83.
Lemma F_a1108 : fetch_word Asan.M.loaded_segments (0xa1158 : word) = Some W_a1108.
Proof. vm_refl. Qed.
Lemma D_a1108 : decode_any W_a1108 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a110c : bv 32 := 0x07010113.
Lemma F_a110c : fetch_word Asan.M.loaded_segments (0xa115c : word) = Some W_a110c.
Proof. vm_refl. Qed.
Lemma D_a110c : decode_any W_a110c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1110 : bv 32 := 0x00008067.
Lemma F_a1110 : fetch_word Asan.M.loaded_segments (0xa1160 : word) = Some W_a1110.
Proof. vm_refl. Qed.
Lemma D_a1110 : decode_any W_a1110 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r7fbdc_7fe80.
Module Na0_code_r802bc_80400.
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

Definition W_a1630 : bv 32 := 0xfd010113.
Lemma F_a1630 : fetch_word Asan.M.loaded_segments (0xa1680 : word) = Some W_a1630.
Proof. vm_refl. Qed.
Lemma D_a1630 : decode_any W_a1630 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1634 : bv 32 := 0x02113423.
Lemma F_a1634 : fetch_word Asan.M.loaded_segments (0xa1684 : word) = Some W_a1634.
Proof. vm_refl. Qed.
Lemma D_a1634 : decode_any W_a1634 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1638 : bv 32 := 0x02813023.
Lemma F_a1638 : fetch_word Asan.M.loaded_segments (0xa1688 : word) = Some W_a1638.
Proof. vm_refl. Qed.
Lemma D_a1638 : decode_any W_a1638 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a163c : bv 32 := 0x00913c23.
Lemma F_a163c : fetch_word Asan.M.loaded_segments (0xa168c : word) = Some W_a163c.
Proof. vm_refl. Qed.
Lemma D_a163c : decode_any W_a163c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1640 : bv 32 := 0x01213823.
Lemma F_a1640 : fetch_word Asan.M.loaded_segments (0xa1690 : word) = Some W_a1640.
Proof. vm_refl. Qed.
Lemma D_a1640 : decode_any W_a1640 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1644 : bv 32 := 0x01313423.
Lemma F_a1644 : fetch_word Asan.M.loaded_segments (0xa1694 : word) = Some W_a1644.
Proof. vm_refl. Qed.
Lemma D_a1644 : decode_any W_a1644 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1648 : bv 32 := 0x00050413.
Lemma F_a1648 : fetch_word Asan.M.loaded_segments (0xa1698 : word) = Some W_a1648.
Proof. vm_refl. Qed.
Lemma D_a1648 : decode_any W_a1648 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a164c : bv 32 := 0x00000593.
Lemma F_a164c : fetch_word Asan.M.loaded_segments (0xa169c : word) = Some W_a164c.
Proof. vm_refl. Qed.
Lemma D_a164c : decode_any W_a164c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1650 : bv 32 := 0x800004b7.
Lemma F_a1650 : fetch_word Asan.M.loaded_segments (0xa16a0 : word) = Some W_a1650.
Proof. vm_refl. Qed.
Lemma D_a1650 : decode_any W_a1650 = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1654 : bv 32 := 0x00900913.
Lemma F_a1654 : fetch_word Asan.M.loaded_segments (0xa16a4 : word) = Some W_a1654.
Proof. vm_refl. Qed.
Lemma D_a1654 : decode_any W_a1654 = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1658 : bv 32 := 0x00052503.
Lemma F_a1658 : fetch_word Asan.M.loaded_segments (0xa16a8 : word) = Some W_a1658.
Proof. vm_refl. Qed.
Lemma D_a1658 : decode_any W_a1658 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a165c : bv 32 := 0x00055a63.
Lemma F_a165c : fetch_word Asan.M.loaded_segments (0xa16ac : word) = Some W_a165c.
Proof. vm_refl. Qed.
Lemma D_a165c : decode_any W_a165c = Some (Branch BC_GE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1670 : bv 32 := 0x00956633.
Lemma F_a1670 : fetch_word Asan.M.loaded_segments (0xa16c0 : word) = Some W_a1670.
Proof. vm_refl. Qed.
Lemma D_a1670 : decode_any W_a1670 = Some (Op ALU_OR 12 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1674 : bv 32 := 0x160426af.
Lemma F_a1674 : fetch_word Asan.M.loaded_segments (0xa16c4 : word) = Some W_a1674.
Proof. vm_refl. Qed.
Lemma D_a1674 : decode_any W_a1674 = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1678 : bv 32 := 0x00a69663.
Lemma F_a1678 : fetch_word Asan.M.loaded_segments (0xa16c8 : word) = Some W_a1678.
Proof. vm_refl. Qed.
Lemma D_a1678 : decode_any W_a1678 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a167c : bv 32 := 0x1ac4272f.
Lemma F_a167c : fetch_word Asan.M.loaded_segments (0xa16cc : word) = Some W_a167c.
Proof. vm_refl. Qed.
Lemma D_a167c : decode_any W_a167c = Some (Sc AW false true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1680 : bv 32 := 0xfe071ae3.
Lemma F_a1680 : fetch_word Asan.M.loaded_segments (0xa16d0 : word) = Some W_a1680.
Proof. vm_refl. Qed.
Lemma D_a1680 : decode_any W_a1680 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1684 : bv 32 := 0x02a68063.
Lemma F_a1684 : fetch_word Asan.M.loaded_segments (0xa16d4 : word) = Some W_a1684.
Proof. vm_refl. Qed.
Lemma D_a1684 : decode_any W_a1684 = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16a4 : bv 32 := 0x02813083.
Lemma F_a16a4 : fetch_word Asan.M.loaded_segments (0xa16f4 : word) = Some W_a16a4.
Proof. vm_refl. Qed.
Lemma D_a16a4 : decode_any W_a16a4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16a8 : bv 32 := 0x02013403.
Lemma F_a16a8 : fetch_word Asan.M.loaded_segments (0xa16f8 : word) = Some W_a16a8.
Proof. vm_refl. Qed.
Lemma D_a16a8 : decode_any W_a16a8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16ac : bv 32 := 0x01813483.
Lemma F_a16ac : fetch_word Asan.M.loaded_segments (0xa16fc : word) = Some W_a16ac.
Proof. vm_refl. Qed.
Lemma D_a16ac : decode_any W_a16ac = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16b0 : bv 32 := 0x01013903.
Lemma F_a16b0 : fetch_word Asan.M.loaded_segments (0xa1700 : word) = Some W_a16b0.
Proof. vm_refl. Qed.
Lemma D_a16b0 : decode_any W_a16b0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16b4 : bv 32 := 0x00813983.
Lemma F_a16b4 : fetch_word Asan.M.loaded_segments (0xa1704 : word) = Some W_a16b4.
Proof. vm_refl. Qed.
Lemma D_a16b4 : decode_any W_a16b4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16b8 : bv 32 := 0x03010113.
Lemma F_a16b8 : fetch_word Asan.M.loaded_segments (0xa1708 : word) = Some W_a16b8.
Proof. vm_refl. Qed.
Lemma D_a16b8 : decode_any W_a16b8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16bc : bv 32 := 0x00008067.
Lemma F_a16bc : fetch_word Asan.M.loaded_segments (0xa170c : word) = Some W_a16bc.
Proof. vm_refl. Qed.
Lemma D_a16bc : decode_any W_a16bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r802bc_80400.
Module Na0_code_r71154_71230.
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

Definition W_922bc : bv 32 := 0x02060063.
Lemma F_922bc : fetch_word Asan.M.loaded_segments (0x9230c : word) = Some W_922bc.
Proof. vm_refl. Qed.
Lemma D_922bc : decode_any W_922bc = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_922c0 : bv 32 := 0x00c50633.
Lemma F_922c0 : fetch_word Asan.M.loaded_segments (0x92310 : word) = Some W_922c0.
Proof. vm_refl. Qed.
Lemma D_922c0 : decode_any W_922c0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_922c4 : bv 32 := 0x00050693.
Lemma F_922c4 : fetch_word Asan.M.loaded_segments (0x92314 : word) = Some W_922c4.
Proof. vm_refl. Qed.
Lemma D_922c4 : decode_any W_922c4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_922c8 : bv 32 := 0x0005c703.
Lemma F_922c8 : fetch_word Asan.M.loaded_segments (0x92318 : word) = Some W_922c8.
Proof. vm_refl. Qed.
Lemma D_922c8 : decode_any W_922c8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_922cc : bv 32 := 0x00e68023.
Lemma F_922cc : fetch_word Asan.M.loaded_segments (0x9231c : word) = Some W_922cc.
Proof. vm_refl. Qed.
Lemma D_922cc : decode_any W_922cc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_922d0 : bv 32 := 0x00168693.
Lemma F_922d0 : fetch_word Asan.M.loaded_segments (0x92320 : word) = Some W_922d0.
Proof. vm_refl. Qed.
Lemma D_922d0 : decode_any W_922d0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_922d4 : bv 32 := 0x00158593.
Lemma F_922d4 : fetch_word Asan.M.loaded_segments (0x92324 : word) = Some W_922d4.
Proof. vm_refl. Qed.
Lemma D_922d4 : decode_any W_922d4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_922d8 : bv 32 := 0xfec698e3.
Lemma F_922d8 : fetch_word Asan.M.loaded_segments (0x92328 : word) = Some W_922d8.
Proof. vm_refl. Qed.
Lemma D_922d8 : decode_any W_922d8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_922dc : bv 32 := 0x00008067.
Lemma F_922dc : fetch_word Asan.M.loaded_segments (0x9232c : word) = Some W_922dc.
Proof. vm_refl. Qed.
Lemma D_922dc : decode_any W_922dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_922e0 : bv 32 := 0x02b57463.
Lemma F_922e0 : fetch_word Asan.M.loaded_segments (0x92330 : word) = Some W_922e0.
Proof. vm_refl. Qed.
Lemma D_922e0 : decode_any W_922e0 = Some (Branch BC_GEU 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_922e4 : bv 32 := 0x04c05863.
Lemma F_922e4 : fetch_word Asan.M.loaded_segments (0x92334 : word) = Some W_922e4.
Proof. vm_refl. Qed.
Lemma D_922e4 : decode_any W_922e4 = Some (Branch BC_GE 0 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_922e8 : bv 32 := 0x00c50633.
Lemma F_922e8 : fetch_word Asan.M.loaded_segments (0x92338 : word) = Some W_922e8.
Proof. vm_refl. Qed.
Lemma D_922e8 : decode_any W_922e8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_922ec : bv 32 := 0x00050693.
Lemma F_922ec : fetch_word Asan.M.loaded_segments (0x9233c : word) = Some W_922ec.
Proof. vm_refl. Qed.
Lemma D_922ec : decode_any W_922ec = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_922f0 : bv 32 := 0x0005c703.
Lemma F_922f0 : fetch_word Asan.M.loaded_segments (0x92340 : word) = Some W_922f0.
Proof. vm_refl. Qed.
Lemma D_922f0 : decode_any W_922f0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_922f4 : bv 32 := 0x00e68023.
Lemma F_922f4 : fetch_word Asan.M.loaded_segments (0x92344 : word) = Some W_922f4.
Proof. vm_refl. Qed.
Lemma D_922f4 : decode_any W_922f4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_922f8 : bv 32 := 0x00168693.
Lemma F_922f8 : fetch_word Asan.M.loaded_segments (0x92348 : word) = Some W_922f8.
Proof. vm_refl. Qed.
Lemma D_922f8 : decode_any W_922f8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_922fc : bv 32 := 0x00158593.
Lemma F_922fc : fetch_word Asan.M.loaded_segments (0x9234c : word) = Some W_922fc.
Proof. vm_refl. Qed.
Lemma D_922fc : decode_any W_922fc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92300 : bv 32 := 0xfec698e3.
Lemma F_92300 : fetch_word Asan.M.loaded_segments (0x92350 : word) = Some W_92300.
Proof. vm_refl. Qed.
Lemma D_92300 : decode_any W_92300 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_92304 : bv 32 := 0x0300006f.
Lemma F_92304 : fetch_word Asan.M.loaded_segments (0x92354 : word) = Some W_92304.
Proof. vm_refl. Qed.
Lemma D_92304 : decode_any W_92304 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_92308 : bv 32 := 0x02a5f663.
Lemma F_92308 : fetch_word Asan.M.loaded_segments (0x92358 : word) = Some W_92308.
Proof. vm_refl. Qed.
Lemma D_92308 : decode_any W_92308 = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9230c : bv 32 := 0x02c05463.
Lemma F_9230c : fetch_word Asan.M.loaded_segments (0x9235c : word) = Some W_9230c.
Proof. vm_refl. Qed.
Lemma D_9230c : decode_any W_9230c = Some (Branch BC_GE 0 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_92310 : bv 32 := 0xfff60693.
Lemma F_92310 : fetch_word Asan.M.loaded_segments (0x92360 : word) = Some W_92310.
Proof. vm_refl. Qed.
Lemma D_92310 : decode_any W_92310 = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_92314 : bv 32 := 0x00100613.
Lemma F_92314 : fetch_word Asan.M.loaded_segments (0x92364 : word) = Some W_92314.
Proof. vm_refl. Qed.
Lemma D_92314 : decode_any W_92314 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92318 : bv 32 := 0x00d58733.
Lemma F_92318 : fetch_word Asan.M.loaded_segments (0x92368 : word) = Some W_92318.
Proof. vm_refl. Qed.
Lemma D_92318 : decode_any W_92318 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_9231c : bv 32 := 0x00074703.
Lemma F_9231c : fetch_word Asan.M.loaded_segments (0x9236c : word) = Some W_9231c.
Proof. vm_refl. Qed.
Lemma D_9231c : decode_any W_9231c = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92320 : bv 32 := 0x00d507b3.
Lemma F_92320 : fetch_word Asan.M.loaded_segments (0x92370 : word) = Some W_92320.
Proof. vm_refl. Qed.
Lemma D_92320 : decode_any W_92320 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92324 : bv 32 := 0x00168813.
Lemma F_92324 : fetch_word Asan.M.loaded_segments (0x92374 : word) = Some W_92324.
Proof. vm_refl. Qed.
Lemma D_92324 : decode_any W_92324 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92328 : bv 32 := 0xfff68693.
Lemma F_92328 : fetch_word Asan.M.loaded_segments (0x92378 : word) = Some W_92328.
Proof. vm_refl. Qed.
Lemma D_92328 : decode_any W_92328 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9232c : bv 32 := 0x00e78023.
Lemma F_9232c : fetch_word Asan.M.loaded_segments (0x9237c : word) = Some W_9232c.
Proof. vm_refl. Qed.
Lemma D_9232c : decode_any W_9232c = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92330 : bv 32 := 0xff0664e3.
Lemma F_92330 : fetch_word Asan.M.loaded_segments (0x92380 : word) = Some W_92330.
Proof. vm_refl. Qed.
Lemma D_92330 : decode_any W_92330 = Some (Branch BC_LTU 12 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_92334 : bv 32 := 0x00008067.
Lemma F_92334 : fetch_word Asan.M.loaded_segments (0x92384 : word) = Some W_92334.
Proof. vm_refl. Qed.
Lemma D_92334 : decode_any W_92334 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92338 : bv 32 := 0x00a666b3.
Lemma F_92338 : fetch_word Asan.M.loaded_segments (0x92388 : word) = Some W_92338.
Proof. vm_refl. Qed.
Lemma D_92338 : decode_any W_92338 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9233c : bv 32 := 0x00f6f693.
Lemma F_9233c : fetch_word Asan.M.loaded_segments (0x9238c : word) = Some W_9233c.
Proof. vm_refl. Qed.
Lemma D_9233c : decode_any W_9233c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_92340 : bv 32 := 0x02068063.
Lemma F_92340 : fetch_word Asan.M.loaded_segments (0x92390 : word) = Some W_92340.
Proof. vm_refl. Qed.
Lemma D_92340 : decode_any W_92340 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_92344 : bv 32 := 0x04060863.
Lemma F_92344 : fetch_word Asan.M.loaded_segments (0x92394 : word) = Some W_92344.
Proof. vm_refl. Qed.
Lemma D_92344 : decode_any W_92344 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_92348 : bv 32 := 0x00c50633.
Lemma F_92348 : fetch_word Asan.M.loaded_segments (0x92398 : word) = Some W_92348.
Proof. vm_refl. Qed.
Lemma D_92348 : decode_any W_92348 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9234c : bv 32 := 0x00050693.
Lemma F_9234c : fetch_word Asan.M.loaded_segments (0x9239c : word) = Some W_9234c.
Proof. vm_refl. Qed.
Lemma D_9234c : decode_any W_9234c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92350 : bv 32 := 0x00b68023.
Lemma F_92350 : fetch_word Asan.M.loaded_segments (0x923a0 : word) = Some W_92350.
Proof. vm_refl. Qed.
Lemma D_92350 : decode_any W_92350 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92354 : bv 32 := 0x00168693.
Lemma F_92354 : fetch_word Asan.M.loaded_segments (0x923a4 : word) = Some W_92354.
Proof. vm_refl. Qed.
Lemma D_92354 : decode_any W_92354 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92358 : bv 32 := 0xfec69ce3.
Lemma F_92358 : fetch_word Asan.M.loaded_segments (0x923a8 : word) = Some W_92358.
Proof. vm_refl. Qed.
Lemma D_92358 : decode_any W_92358 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_9235c : bv 32 := 0x0380006f.
Lemma F_9235c : fetch_word Asan.M.loaded_segments (0x923ac : word) = Some W_9235c.
Proof. vm_refl. Qed.
Lemma D_9235c : decode_any W_9235c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_92360 : bv 32 := 0x02060a63.
Lemma F_92360 : fetch_word Asan.M.loaded_segments (0x923b0 : word) = Some W_92360.
Proof. vm_refl. Qed.
Lemma D_92360 : decode_any W_92360 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_92364 : bv 32 := 0x00c50633.
Lemma F_92364 : fetch_word Asan.M.loaded_segments (0x923b4 : word) = Some W_92364.
Proof. vm_refl. Qed.
Lemma D_92364 : decode_any W_92364 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92368 : bv 32 := 0x00859693.
Lemma F_92368 : fetch_word Asan.M.loaded_segments (0x923b8 : word) = Some W_92368.
Proof. vm_refl. Qed.
Lemma D_92368 : decode_any W_92368 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9236c : bv 32 := 0x00b6e5b3.
Lemma F_9236c : fetch_word Asan.M.loaded_segments (0x923bc : word) = Some W_9236c.
Proof. vm_refl. Qed.
Lemma D_9236c : decode_any W_9236c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_92370 : bv 32 := 0x01059693.
Lemma F_92370 : fetch_word Asan.M.loaded_segments (0x923c0 : word) = Some W_92370.
Proof. vm_refl. Qed.
Lemma D_92370 : decode_any W_92370 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_92374 : bv 32 := 0x00b6e5b3.
Lemma F_92374 : fetch_word Asan.M.loaded_segments (0x923c4 : word) = Some W_92374.
Proof. vm_refl. Qed.
Lemma D_92374 : decode_any W_92374 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_92378 : bv 32 := 0x02059693.
Lemma F_92378 : fetch_word Asan.M.loaded_segments (0x923c8 : word) = Some W_92378.
Proof. vm_refl. Qed.
Lemma D_92378 : decode_any W_92378 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9237c : bv 32 := 0x00b6e5b3.
Lemma F_9237c : fetch_word Asan.M.loaded_segments (0x923cc : word) = Some W_9237c.
Proof. vm_refl. Qed.
Lemma D_9237c : decode_any W_9237c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_92380 : bv 32 := 0x00050693.
Lemma F_92380 : fetch_word Asan.M.loaded_segments (0x923d0 : word) = Some W_92380.
Proof. vm_refl. Qed.
Lemma D_92380 : decode_any W_92380 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92384 : bv 32 := 0x00b6b023.
Lemma F_92384 : fetch_word Asan.M.loaded_segments (0x923d4 : word) = Some W_92384.
Proof. vm_refl. Qed.
Lemma D_92384 : decode_any W_92384 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92388 : bv 32 := 0x00b6b423.
Lemma F_92388 : fetch_word Asan.M.loaded_segments (0x923d8 : word) = Some W_92388.
Proof. vm_refl. Qed.
Lemma D_92388 : decode_any W_92388 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9238c : bv 32 := 0x01068693.
Lemma F_9238c : fetch_word Asan.M.loaded_segments (0x923dc : word) = Some W_9238c.
Proof. vm_refl. Qed.
Lemma D_9238c : decode_any W_9238c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_92390 : bv 32 := 0xfec6eae3.
Lemma F_92390 : fetch_word Asan.M.loaded_segments (0x923e0 : word) = Some W_92390.
Proof. vm_refl. Qed.
Lemma D_92390 : decode_any W_92390 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_92394 : bv 32 := 0x00008067.
Lemma F_92394 : fetch_word Asan.M.loaded_segments (0x923e4 : word) = Some W_92394.
Proof. vm_refl. Qed.
Lemma D_92394 : decode_any W_92394 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r71154_71230.
Module Na0_code_r7d5e0_7d838.
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

Definition W_9e8a0 : bv 32 := 0xfc010113.
Lemma F_9e8a0 : fetch_word Asan.M.loaded_segments (0x9e8f0 : word) = Some W_9e8a0.
Proof. vm_refl. Qed.
Lemma D_9e8a0 : decode_any W_9e8a0 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8a4 : bv 32 := 0x02113c23.
Lemma F_9e8a4 : fetch_word Asan.M.loaded_segments (0x9e8f4 : word) = Some W_9e8a4.
Proof. vm_refl. Qed.
Lemma D_9e8a4 : decode_any W_9e8a4 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8a8 : bv 32 := 0x02813823.
Lemma F_9e8a8 : fetch_word Asan.M.loaded_segments (0x9e8f8 : word) = Some W_9e8a8.
Proof. vm_refl. Qed.
Lemma D_9e8a8 : decode_any W_9e8a8 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8ac : bv 32 := 0x02913423.
Lemma F_9e8ac : fetch_word Asan.M.loaded_segments (0x9e8fc : word) = Some W_9e8ac.
Proof. vm_refl. Qed.
Lemma D_9e8ac : decode_any W_9e8ac = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8b0 : bv 32 := 0x03213023.
Lemma F_9e8b0 : fetch_word Asan.M.loaded_segments (0x9e900 : word) = Some W_9e8b0.
Proof. vm_refl. Qed.
Lemma D_9e8b0 : decode_any W_9e8b0 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8b4 : bv 32 := 0x01313c23.
Lemma F_9e8b4 : fetch_word Asan.M.loaded_segments (0x9e904 : word) = Some W_9e8b4.
Proof. vm_refl. Qed.
Lemma D_9e8b4 : decode_any W_9e8b4 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8b8 : bv 32 := 0x01413823.
Lemma F_9e8b8 : fetch_word Asan.M.loaded_segments (0x9e908 : word) = Some W_9e8b8.
Proof. vm_refl. Qed.
Lemma D_9e8b8 : decode_any W_9e8b8 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8bc : bv 32 := 0x01513423.
Lemma F_9e8bc : fetch_word Asan.M.loaded_segments (0x9e90c : word) = Some W_9e8bc.
Proof. vm_refl. Qed.
Lemma D_9e8bc : decode_any W_9e8bc = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8c0 : bv 32 := 0x00058993.
Lemma F_9e8c0 : fetch_word Asan.M.loaded_segments (0x9e910 : word) = Some W_9e8c0.
Proof. vm_refl. Qed.
Lemma D_9e8c0 : decode_any W_9e8c0 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8c4 : bv 32 := 0x0085aa03.
Lemma F_9e8c4 : fetch_word Asan.M.loaded_segments (0x9e914 : word) = Some W_9e8c4.
Proof. vm_refl. Qed.
Lemma D_9e8c4 : decode_any W_9e8c4 = Some (Load SZ4 true 20 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8c8 : bv 32 := 0x00c5aa83.
Lemma F_9e8c8 : fetch_word Asan.M.loaded_segments (0x9e918 : word) = Some W_9e8c8.
Proof. vm_refl. Qed.
Lemma D_9e8c8 : decode_any W_9e8c8 = Some (Load SZ4 true 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8cc : bv 32 := 0x015a65b3.
Lemma F_9e8cc : fetch_word Asan.M.loaded_segments (0x9e91c : word) = Some W_9e8cc.
Proof. vm_refl. Qed.
Lemma D_9e8cc : decode_any W_9e8cc = Some (Op ALU_OR 11 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8d0 : bv 32 := 0x00059663.
Lemma F_9e8d0 : fetch_word Asan.M.loaded_segments (0x9e920 : word) = Some W_9e8d0.
Proof. vm_refl. Qed.
Lemma D_9e8d0 : decode_any W_9e8d0 = Some (Branch BC_NE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8dc : bv 32 := 0x00050493.
Lemma F_9e8dc : fetch_word Asan.M.loaded_segments (0x9e92c : word) = Some W_9e8dc.
Proof. vm_refl. Qed.
Lemma D_9e8dc : decode_any W_9e8dc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8e0 : bv 32 := 0x10000513.
Lemma F_9e8e0 : fetch_word Asan.M.loaded_segments (0x9e930 : word) = Some W_9e8e0.
Proof. vm_refl. Qed.
Lemma D_9e8e0 : decode_any W_9e8e0 = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8e4 : bv 32 := 0x0aaafe63.
Lemma F_9e8e4 : fetch_word Asan.M.loaded_segments (0x9e934 : word) = Some W_9e8e4.
Proof. vm_refl. Qed.
Lemma D_9e8e4 : decode_any W_9e8e4 = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8e8 : bv 32 := 0x00060413.
Lemma F_9e8e8 : fetch_word Asan.M.loaded_segments (0x9e938 : word) = Some W_9e8e8.
Proof. vm_refl. Qed.
Lemma D_9e8e8 : decode_any W_9e8e8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8ec : bv 32 := 0x0ff00513.
Lemma F_9e8ec : fetch_word Asan.M.loaded_segments (0x9e93c : word) = Some W_9e8ec.
Proof. vm_refl. Qed.
Lemma D_9e8ec : decode_any W_9e8ec = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8f0 : bv 32 := 0x00aa6463.
Lemma F_9e8f0 : fetch_word Asan.M.loaded_segments (0x9e940 : word) = Some W_9e8f0.
Proof. vm_refl. Qed.
Lemma D_9e8f0 : decode_any W_9e8f0 = Some (Branch BC_LTU 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8f8 : bv 32 := 0x00013023.
Lemma F_9e8f8 : fetch_word Asan.M.loaded_segments (0x9e948 : word) = Some W_9e8f8.
Proof. vm_refl. Qed.
Lemma D_9e8f8 : decode_any W_9e8f8 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e8fc : bv 32 := 0x00043023.
Lemma F_9e8fc : fetch_word Asan.M.loaded_segments (0x9e94c : word) = Some W_9e8fc.
Proof. vm_refl. Qed.
Lemma D_9e8fc : decode_any W_9e8fc = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e900 : bv 32 := 0x001a0913.
Lemma F_9e900 : fetch_word Asan.M.loaded_segments (0x9e950 : word) = Some W_9e900.
Proof. vm_refl. Qed.
Lemma D_9e900 : decode_any W_9e900 = Some (OpImm ALU_ADD 18 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e904 : bv 32 := 0x00010613.
Lemma F_9e904 : fetch_word Asan.M.loaded_segments (0x9e954 : word) = Some W_9e904.
Proof. vm_refl. Qed.
Lemma D_9e904 : decode_any W_9e904 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e908 : bv 32 := 0x00048513.
Lemma F_9e908 : fetch_word Asan.M.loaded_segments (0x9e958 : word) = Some W_9e908.
Proof. vm_refl. Qed.
Lemma D_9e908 : decode_any W_9e908 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e90c : bv 32 := 0x00090593.
Lemma F_9e90c : fetch_word Asan.M.loaded_segments (0x9e95c : word) = Some W_9e90c.
Proof. vm_refl. Qed.
Lemma D_9e90c : decode_any W_9e90c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e910 : bv 32 := 0x00040693.
Lemma F_9e910 : fetch_word Asan.M.loaded_segments (0x9e960 : word) = Some W_9e910.
Proof. vm_refl. Qed.
Lemma D_9e910 : decode_any W_9e910 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e914 : bv 32 := 0x0b0000ef.
Lemma F_9e914 : fetch_word Asan.M.loaded_segments (0x9e964 : word) = Some W_9e914.
Proof. vm_refl. Qed.
Lemma D_9e914 : decode_any W_9e914 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e918 : bv 32 := 0x06050263.
Lemma F_9e918 : fetch_word Asan.M.loaded_segments (0x9e968 : word) = Some W_9e918.
Proof. vm_refl. Qed.
Lemma D_9e918 : decode_any W_9e918 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e91c : bv 32 := 0x008a961b.
Lemma F_9e91c : fetch_word Asan.M.loaded_segments (0x9e96c : word) = Some W_9e91c.
Proof. vm_refl. Qed.
Lemma D_9e91c : decode_any W_9e91c = Some (ShiftImm32 ALU_SLL 12 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e920 : bv 32 := 0x0009b583.
Lemma F_9e920 : fetch_word Asan.M.loaded_segments (0x9e970 : word) = Some W_9e920.
Proof. vm_refl. Qed.
Lemma D_9e920 : decode_any W_9e920 = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e924 : bv 32 := 0x01466633.
Lemma F_9e924 : fetch_word Asan.M.loaded_segments (0x9e974 : word) = Some W_9e924.
Proof. vm_refl. Qed.
Lemma D_9e924 : decode_any W_9e924 = Some (Op ALU_OR 12 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e928 : bv 32 := 0x00c53023.
Lemma F_9e928 : fetch_word Asan.M.loaded_segments (0x9e978 : word) = Some W_9e928.
Proof. vm_refl. Qed.
Lemma D_9e928 : decode_any W_9e928 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e92c : bv 32 := 0x00850513.
Lemma F_9e92c : fetch_word Asan.M.loaded_segments (0x9e97c : word) = Some W_9e92c.
Proof. vm_refl. Qed.
Lemma D_9e92c : decode_any W_9e92c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e930 : bv 32 := 0x003a1613.
Lemma F_9e930 : fetch_word Asan.M.loaded_segments (0x9e980 : word) = Some W_9e930.
Proof. vm_refl. Qed.
Lemma D_9e930 : decode_any W_9e930 = Some (ShiftImm ALU_SLL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e934 : bv 32 := 0x989f30ef.
Lemma F_9e934 : fetch_word Asan.M.loaded_segments (0x9e984 : word) = Some W_9e934.
Proof. vm_refl. Qed.
Lemma D_9e934 : decode_any W_9e934 = Some (Jal 1 2046344, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e938 : bv 32 := 0x00013503.
Lemma F_9e938 : fetch_word Asan.M.loaded_segments (0x9e988 : word) = Some W_9e938.
Proof. vm_refl. Qed.
Lemma D_9e938 : decode_any W_9e938 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e93c : bv 32 := 0x01055513.
Lemma F_9e93c : fetch_word Asan.M.loaded_segments (0x9e98c : word) = Some W_9e93c.
Proof. vm_refl. Qed.
Lemma D_9e93c : decode_any W_9e93c = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e940 : bv 32 := 0xff057513.
Lemma F_9e940 : fetch_word Asan.M.loaded_segments (0x9e990 : word) = Some W_9e940.
Proof. vm_refl. Qed.
Lemma D_9e940 : decode_any W_9e940 = Some (OpImm ALU_AND 10 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e944 : bv 32 := 0x00a48533.
Lemma F_9e944 : fetch_word Asan.M.loaded_segments (0x9e994 : word) = Some W_9e944.
Proof. vm_refl. Qed.
Lemma D_9e944 : decode_any W_9e944 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e948 : bv 32 := 0x01850513.
Lemma F_9e948 : fetch_word Asan.M.loaded_segments (0x9e998 : word) = Some W_9e948.
Proof. vm_refl. Qed.
Lemma D_9e948 : decode_any W_9e948 = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e94c : bv 32 := 0x0325252f.
Lemma F_9e94c : fetch_word Asan.M.loaded_segments (0x9e99c : word) = Some W_9e94c.
Proof. vm_refl. Qed.
Lemma D_9e94c : decode_any W_9e94c = Some (Amo AMO_ADD AW false true 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e950 : bv 32 := 0x001005b7.
Lemma F_9e950 : fetch_word Asan.M.loaded_segments (0x9e9a0 : word) = Some W_9e950.
Proof. vm_refl. Qed.
Lemma D_9e950 : decode_any W_9e950 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e954 : bv 32 := 0x02051513.
Lemma F_9e954 : fetch_word Asan.M.loaded_segments (0x9e9a4 : word) = Some W_9e954.
Proof. vm_refl. Qed.
Lemma D_9e954 : decode_any W_9e954 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e958 : bv 32 := 0x02055513.
Lemma F_9e958 : fetch_word Asan.M.loaded_segments (0x9e9a8 : word) = Some W_9e958.
Proof. vm_refl. Qed.
Lemma D_9e958 : decode_any W_9e958 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e95c : bv 32 := 0x00a90533.
Lemma F_9e95c : fetch_word Asan.M.loaded_segments (0x9e9ac : word) = Some W_9e95c.
Proof. vm_refl. Qed.
Lemma D_9e95c : decode_any W_9e95c = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e960 : bv 32 := 0x00043603.
Lemma F_9e960 : fetch_word Asan.M.loaded_segments (0x9e9b0 : word) = Some W_9e960.
Proof. vm_refl. Qed.
Lemma D_9e960 : decode_any W_9e960 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e964 : bv 32 := 0x00b54533.
Lemma F_9e964 : fetch_word Asan.M.loaded_segments (0x9e9b4 : word) = Some W_9e964.
Proof. vm_refl. Qed.
Lemma D_9e964 : decode_any W_9e964 = Some (Op ALU_XOR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e968 : bv 32 := 0x00012583.
Lemma F_9e968 : fetch_word Asan.M.loaded_segments (0x9e9b8 : word) = Some W_9e968.
Proof. vm_refl. Qed.
Lemma D_9e968 : decode_any W_9e968 = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e96c : bv 32 := 0x00153513.
Lemma F_9e96c : fetch_word Asan.M.loaded_segments (0x9e9bc : word) = Some W_9e96c.
Proof. vm_refl. Qed.
Lemma D_9e96c : decode_any W_9e96c = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e970 : bv 32 := 0x00a60533.
Lemma F_9e970 : fetch_word Asan.M.loaded_segments (0x9e9c0 : word) = Some W_9e970.
Proof. vm_refl. Qed.
Lemma D_9e970 : decode_any W_9e970 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e974 : bv 32 := 0x00a43023.
Lemma F_9e974 : fetch_word Asan.M.loaded_segments (0x9e9c4 : word) = Some W_9e974.
Proof. vm_refl. Qed.
Lemma D_9e974 : decode_any W_9e974 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e978 : bv 32 := 0x0015851b.
Lemma F_9e978 : fetch_word Asan.M.loaded_segments (0x9e9c8 : word) = Some W_9e978.
Proof. vm_refl. Qed.
Lemma D_9e978 : decode_any W_9e978 = Some (OpImm32 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e97c : bv 32 := 0x03813083.
Lemma F_9e97c : fetch_word Asan.M.loaded_segments (0x9e9cc : word) = Some W_9e97c.
Proof. vm_refl. Qed.
Lemma D_9e97c : decode_any W_9e97c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e980 : bv 32 := 0x03013403.
Lemma F_9e980 : fetch_word Asan.M.loaded_segments (0x9e9d0 : word) = Some W_9e980.
Proof. vm_refl. Qed.
Lemma D_9e980 : decode_any W_9e980 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e984 : bv 32 := 0x02813483.
Lemma F_9e984 : fetch_word Asan.M.loaded_segments (0x9e9d4 : word) = Some W_9e984.
Proof. vm_refl. Qed.
Lemma D_9e984 : decode_any W_9e984 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e988 : bv 32 := 0x02013903.
Lemma F_9e988 : fetch_word Asan.M.loaded_segments (0x9e9d8 : word) = Some W_9e988.
Proof. vm_refl. Qed.
Lemma D_9e988 : decode_any W_9e988 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e98c : bv 32 := 0x01813983.
Lemma F_9e98c : fetch_word Asan.M.loaded_segments (0x9e9dc : word) = Some W_9e98c.
Proof. vm_refl. Qed.
Lemma D_9e98c : decode_any W_9e98c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e990 : bv 32 := 0x01013a03.
Lemma F_9e990 : fetch_word Asan.M.loaded_segments (0x9e9e0 : word) = Some W_9e990.
Proof. vm_refl. Qed.
Lemma D_9e990 : decode_any W_9e990 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e994 : bv 32 := 0x00813a83.
Lemma F_9e994 : fetch_word Asan.M.loaded_segments (0x9e9e4 : word) = Some W_9e994.
Proof. vm_refl. Qed.
Lemma D_9e994 : decode_any W_9e994 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e998 : bv 32 := 0x04010113.
Lemma F_9e998 : fetch_word Asan.M.loaded_segments (0x9e9e8 : word) = Some W_9e998.
Proof. vm_refl. Qed.
Lemma D_9e998 : decode_any W_9e998 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e99c : bv 32 := 0x00008067.
Lemma F_9e99c : fetch_word Asan.M.loaded_segments (0x9e9ec : word) = Some W_9e99c.
Proof. vm_refl. Qed.
Lemma D_9e99c : decode_any W_9e99c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9c4 : bv 32 := 0xff010113.
Lemma F_9e9c4 : fetch_word Asan.M.loaded_segments (0x9ea14 : word) = Some W_9e9c4.
Proof. vm_refl. Qed.
Lemma D_9e9c4 : decode_any W_9e9c4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9c8 : bv 32 := 0x00113423.
Lemma F_9e9c8 : fetch_word Asan.M.loaded_segments (0x9ea18 : word) = Some W_9e9c8.
Proof. vm_refl. Qed.
Lemma D_9e9c8 : decode_any W_9e9c8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9cc : bv 32 := 0x00813023.
Lemma F_9e9cc : fetch_word Asan.M.loaded_segments (0x9ea1c : word) = Some W_9e9cc.
Proof. vm_refl. Qed.
Lemma D_9e9cc : decode_any W_9e9cc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9d0 : bv 32 := 0x00058793.
Lemma F_9e9d0 : fetch_word Asan.M.loaded_segments (0x9ea20 : word) = Some W_9e9d0.
Proof. vm_refl. Qed.
Lemma D_9e9d0 : decode_any W_9e9d0 = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9d4 : bv 32 := 0x00050593.
Lemma F_9e9d4 : fetch_word Asan.M.loaded_segments (0x9ea24 : word) = Some W_9e9d4.
Proof. vm_refl. Qed.
Lemma D_9e9d4 : decode_any W_9e9d4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9d8 : bv 32 := 0x00f5342f.
Lemma F_9e9d8 : fetch_word Asan.M.loaded_segments (0x9ea28 : word) = Some W_9e9d8.
Proof. vm_refl. Qed.
Lemma D_9e9d8 : decode_any W_9e9d8 = Some (Amo AMO_ADD AD false false 8 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9dc : bv 32 := 0xfff78513.
Lemma F_9e9dc : fetch_word Asan.M.loaded_segments (0x9ea2c : word) = Some W_9e9dc.
Proof. vm_refl. Qed.
Lemma D_9e9dc : decode_any W_9e9dc = Some (OpImm ALU_ADD 10 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9e0 : bv 32 := 0x01445293.
Lemma F_9e9e0 : fetch_word Asan.M.loaded_segments (0x9ea30 : word) = Some W_9e9e0.
Proof. vm_refl. Qed.
Lemma D_9e9e0 : decode_any W_9e9e0 = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9e4 : bv 32 := 0x00850733.
Lemma F_9e9e4 : fetch_word Asan.M.loaded_segments (0x9ea34 : word) = Some W_9e9e4.
Proof. vm_refl. Qed.
Lemma D_9e9e4 : decode_any W_9e9e4 = Some (Op ALU_ADD 14 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9e8 : bv 32 := 0x01475313.
Lemma F_9e9e8 : fetch_word Asan.M.loaded_segments (0x9ea38 : word) = Some W_9e9e8.
Proof. vm_refl. Qed.
Lemma D_9e9e8 : decode_any W_9e9e8 = Some (ShiftImm ALU_SRL 6 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9ec : bv 32 := 0x04629863.
Lemma F_9e9ec : fetch_word Asan.M.loaded_segments (0x9ea3c : word) = Some W_9e9ec.
Proof. vm_refl. Qed.
Lemma D_9e9ec : decode_any W_9e9ec = Some (Branch BC_NE 5 6 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9f0 : bv 32 := 0x02045513.
Lemma F_9e9f0 : fetch_word Asan.M.loaded_segments (0x9ea40 : word) = Some W_9e9f0.
Proof. vm_refl. Qed.
Lemma D_9e9f0 : decode_any W_9e9f0 = Some (ShiftImm ALU_SRL 10 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9e9f4 : bv 32 := 0x00050c63.
Lemma F_9e9f4 : fetch_word Asan.M.loaded_segments (0x9ea44 : word) = Some W_9e9f4.
Proof. vm_refl. Qed.
Lemma D_9e9f4 : decode_any W_9e9f4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea0c : bv 32 := 0x00863023.
Lemma F_9ea0c : fetch_word Asan.M.loaded_segments (0x9ea5c : word) = Some W_9ea0c.
Proof. vm_refl. Qed.
Lemma D_9ea0c : decode_any W_9ea0c = Some (Store SZ8 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea10 : bv 32 := 0x00429613.
Lemma F_9ea10 : fetch_word Asan.M.loaded_segments (0x9ea60 : word) = Some W_9ea10.
Proof. vm_refl. Qed.
Lemma D_9ea10 : decode_any W_9ea10 = Some (ShiftImm ALU_SLL 12 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea14 : bv 32 := 0x00c58633.
Lemma F_9ea14 : fetch_word Asan.M.loaded_segments (0x9ea64 : word) = Some W_9ea14.
Proof. vm_refl. Qed.
Lemma D_9ea14 : decode_any W_9ea14 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea18 : bv 32 := 0x01063503.
Lemma F_9ea18 : fetch_word Asan.M.loaded_segments (0x9ea68 : word) = Some W_9ea18.
Proof. vm_refl. Qed.
Lemma D_9ea18 : decode_any W_9ea18 = Some (Load SZ8 true 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea1c : bv 32 := 0x0a050a63.
Lemma F_9ea1c : fetch_word Asan.M.loaded_segments (0x9ea6c : word) = Some W_9ea1c.
Proof. vm_refl. Qed.
Lemma D_9ea1c : decode_any W_9ea1c = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea20 : bv 32 := 0x02c41413.
Lemma F_9ea20 : fetch_word Asan.M.loaded_segments (0x9ea70 : word) = Some W_9ea20.
Proof. vm_refl. Qed.
Lemma D_9ea20 : decode_any W_9ea20 = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea24 : bv 32 := 0x02945413.
Lemma F_9ea24 : fetch_word Asan.M.loaded_segments (0x9ea74 : word) = Some W_9ea24.
Proof. vm_refl. Qed.
Lemma D_9ea24 : decode_any W_9ea24 = Some (ShiftImm ALU_SRL 8 8 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea28 : bv 32 := 0x00850533.
Lemma F_9ea28 : fetch_word Asan.M.loaded_segments (0x9ea78 : word) = Some W_9ea28.
Proof. vm_refl. Qed.
Lemma D_9ea28 : decode_any W_9ea28 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea2c : bv 32 := 0x00813083.
Lemma F_9ea2c : fetch_word Asan.M.loaded_segments (0x9ea7c : word) = Some W_9ea2c.
Proof. vm_refl. Qed.
Lemma D_9ea2c : decode_any W_9ea2c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea30 : bv 32 := 0x00013403.
Lemma F_9ea30 : fetch_word Asan.M.loaded_segments (0x9ea80 : word) = Some W_9ea30.
Proof. vm_refl. Qed.
Lemma D_9ea30 : decode_any W_9ea30 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea34 : bv 32 := 0x01010113.
Lemma F_9ea34 : fetch_word Asan.M.loaded_segments (0x9ea84 : word) = Some W_9ea34.
Proof. vm_refl. Qed.
Lemma D_9ea34 : decode_any W_9ea34 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ea38 : bv 32 := 0x00008067.
Lemma F_9ea38 : fetch_word Asan.M.loaded_segments (0x9ea88 : word) = Some W_9ea38.
Proof. vm_refl. Qed.
Lemma D_9ea38 : decode_any W_9ea38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r7d5e0_7d838.
Module Na0_code_r7f8f4_7f950.
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

Definition W_a0bb4 : bv 32 := 0xfe010113.
Lemma F_a0bb4 : fetch_word Asan.M.loaded_segments (0xa0c04 : word) = Some W_a0bb4.
Proof. vm_refl. Qed.
Lemma D_a0bb4 : decode_any W_a0bb4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bb8 : bv 32 := 0x00113c23.
Lemma F_a0bb8 : fetch_word Asan.M.loaded_segments (0xa0c08 : word) = Some W_a0bb8.
Proof. vm_refl. Qed.
Lemma D_a0bb8 : decode_any W_a0bb8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bbc : bv 32 := 0x00813823.
Lemma F_a0bbc : fetch_word Asan.M.loaded_segments (0xa0c0c : word) = Some W_a0bbc.
Proof. vm_refl. Qed.
Lemma D_a0bbc : decode_any W_a0bbc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bc0 : bv 32 := 0x00060593.
Lemma F_a0bc0 : fetch_word Asan.M.loaded_segments (0xa0c10 : word) = Some W_a0bc0.
Proof. vm_refl. Qed.
Lemma D_a0bc0 : decode_any W_a0bc0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bc4 : bv 32 := 0x00050413.
Lemma F_a0bc4 : fetch_word Asan.M.loaded_segments (0xa0c14 : word) = Some W_a0bc4.
Proof. vm_refl. Qed.
Lemma D_a0bc4 : decode_any W_a0bc4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bc8 : bv 32 := 0x00d53023.
Lemma F_a0bc8 : fetch_word Asan.M.loaded_segments (0xa0c18 : word) = Some W_a0bc8.
Proof. vm_refl. Qed.
Lemma D_a0bc8 : decode_any W_a0bc8 = Some (Store SZ8 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bcc : bv 32 := 0x00013423.
Lemma F_a0bcc : fetch_word Asan.M.loaded_segments (0xa0c1c : word) = Some W_a0bcc.
Proof. vm_refl. Qed.
Lemma D_a0bcc : decode_any W_a0bcc = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bd0 : bv 32 := 0x00191517.
Lemma F_a0bd0 : fetch_word Asan.M.loaded_segments (0xa0c20 : word) = Some W_a0bd0.
Proof. vm_refl. Qed.
Lemma D_a0bd0 : decode_any W_a0bd0 = Some (Auipc 10 401, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bd4 : bv 32 := 0xd2850513.
Lemma F_a0bd4 : fetch_word Asan.M.loaded_segments (0xa0c24 : word) = Some W_a0bd4.
Proof. vm_refl. Qed.
Lemma D_a0bd4 : decode_any W_a0bd4 = Some (OpImm ALU_ADD 10 10 3368, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bd8 : bv 32 := 0x00810613.
Lemma F_a0bd8 : fetch_word Asan.M.loaded_segments (0xa0c28 : word) = Some W_a0bd8.
Proof. vm_refl. Qed.
Lemma D_a0bd8 : decode_any W_a0bd8 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bdc : bv 32 := 0xcc5fd0ef.
Lemma F_a0bdc : fetch_word Asan.M.loaded_segments (0xa0c2c : word) = Some W_a0bdc.
Proof. vm_refl. Qed.
Lemma D_a0bdc : decode_any W_a0bdc = Some (Jal 1 2088132, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0be0 : bv 32 := 0x00813583.
Lemma F_a0be0 : fetch_word Asan.M.loaded_segments (0xa0c30 : word) = Some W_a0be0.
Proof. vm_refl. Qed.
Lemma D_a0be0 : decode_any W_a0be0 = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0be4 : bv 32 := 0x00a42623.
Lemma F_a0be4 : fetch_word Asan.M.loaded_segments (0xa0c34 : word) = Some W_a0be4.
Proof. vm_refl. Qed.
Lemma D_a0be4 : decode_any W_a0be4 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0be8 : bv 32 := 0x00059a63.
Lemma F_a0be8 : fetch_word Asan.M.loaded_segments (0xa0c38 : word) = Some W_a0be8.
Proof. vm_refl. Qed.
Lemma D_a0be8 : decode_any W_a0be8 = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bec : bv 32 := 0x01813083.
Lemma F_a0bec : fetch_word Asan.M.loaded_segments (0xa0c3c : word) = Some W_a0bec.
Proof. vm_refl. Qed.
Lemma D_a0bec : decode_any W_a0bec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bf0 : bv 32 := 0x01013403.
Lemma F_a0bf0 : fetch_word Asan.M.loaded_segments (0xa0c40 : word) = Some W_a0bf0.
Proof. vm_refl. Qed.
Lemma D_a0bf0 : decode_any W_a0bf0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bf4 : bv 32 := 0x02010113.
Lemma F_a0bf4 : fetch_word Asan.M.loaded_segments (0xa0c44 : word) = Some W_a0bf4.
Proof. vm_refl. Qed.
Lemma D_a0bf4 : decode_any W_a0bf4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0bf8 : bv 32 := 0x00008067.
Lemma F_a0bf8 : fetch_word Asan.M.loaded_segments (0xa0c48 : word) = Some W_a0bf8.
Proof. vm_refl. Qed.
Lemma D_a0bf8 : decode_any W_a0bf8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r7f8f4_7f950.
Module Na0_code_r3cf10_3de98.
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

Definition W_58e18 : bv 32 := 0x00060793.
Lemma F_58e18 : fetch_word Asan.M.loaded_segments (0x58e68 : word) = Some W_58e18.
Proof. vm_refl. Qed.
Lemma D_58e18 : decode_any W_58e18 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e1c : bv 32 := 0x00058713.
Lemma F_58e1c : fetch_word Asan.M.loaded_segments (0x58e6c : word) = Some W_58e1c.
Proof. vm_refl. Qed.
Lemma D_58e1c : decode_any W_58e1c = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e20 : bv 32 := 0x00103597.
Lemma F_58e20 : fetch_word Asan.M.loaded_segments (0x58e70 : word) = Some W_58e20.
Proof. vm_refl. Qed.
Lemma D_58e20 : decode_any W_58e20 = Some (Auipc 11 259, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e24 : bv 32 := 0x5a858593.
Lemma F_58e24 : fetch_word Asan.M.loaded_segments (0x58e74 : word) = Some W_58e24.
Proof. vm_refl. Qed.
Lemma D_58e24 : decode_any W_58e24 = Some (OpImm ALU_ADD 11 11 1448, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e28 : bv 32 := 0x00050613.
Lemma F_58e28 : fetch_word Asan.M.loaded_segments (0x58e78 : word) = Some W_58e28.
Proof. vm_refl. Qed.
Lemma D_58e28 : decode_any W_58e28 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e2c : bv 32 := 0x00058513.
Lemma F_58e2c : fetch_word Asan.M.loaded_segments (0x58e7c : word) = Some W_58e2c.
Proof. vm_refl. Qed.
Lemma D_58e2c : decode_any W_58e2c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e30 : bv 32 := 0x00060593.
Lemma F_58e30 : fetch_word Asan.M.loaded_segments (0x58e80 : word) = Some W_58e30.
Proof. vm_refl. Qed.
Lemma D_58e30 : decode_any W_58e30 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e34 : bv 32 := 0x00000613.
Lemma F_58e34 : fetch_word Asan.M.loaded_segments (0x58e84 : word) = Some W_58e34.
Proof. vm_refl. Qed.
Lemma D_58e34 : decode_any W_58e34 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e38 : bv 32 := 0x00000693.
Lemma F_58e38 : fetch_word Asan.M.loaded_segments (0x58e88 : word) = Some W_58e38.
Proof. vm_refl. Qed.
Lemma D_58e38 : decode_any W_58e38 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e3c : bv 32 := 0x0040006f.
Lemma F_58e3c : fetch_word Asan.M.loaded_segments (0x58e8c : word) = Some W_58e3c.
Proof. vm_refl. Qed.
Lemma D_58e3c : decode_any W_58e3c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e40 : bv 32 := 0xfc010113.
Lemma F_58e40 : fetch_word Asan.M.loaded_segments (0x58e90 : word) = Some W_58e40.
Proof. vm_refl. Qed.
Lemma D_58e40 : decode_any W_58e40 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e44 : bv 32 := 0x02113c23.
Lemma F_58e44 : fetch_word Asan.M.loaded_segments (0x58e94 : word) = Some W_58e44.
Proof. vm_refl. Qed.
Lemma D_58e44 : decode_any W_58e44 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e48 : bv 32 := 0x02813823.
Lemma F_58e48 : fetch_word Asan.M.loaded_segments (0x58e98 : word) = Some W_58e48.
Proof. vm_refl. Qed.
Lemma D_58e48 : decode_any W_58e48 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e4c : bv 32 := 0x02913423.
Lemma F_58e4c : fetch_word Asan.M.loaded_segments (0x58e9c : word) = Some W_58e4c.
Proof. vm_refl. Qed.
Lemma D_58e4c : decode_any W_58e4c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e50 : bv 32 := 0x03213023.
Lemma F_58e50 : fetch_word Asan.M.loaded_segments (0x58ea0 : word) = Some W_58e50.
Proof. vm_refl. Qed.
Lemma D_58e50 : decode_any W_58e50 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e54 : bv 32 := 0x01313c23.
Lemma F_58e54 : fetch_word Asan.M.loaded_segments (0x58ea4 : word) = Some W_58e54.
Proof. vm_refl. Qed.
Lemma D_58e54 : decode_any W_58e54 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e58 : bv 32 := 0x01413823.
Lemma F_58e58 : fetch_word Asan.M.loaded_segments (0x58ea8 : word) = Some W_58e58.
Proof. vm_refl. Qed.
Lemma D_58e58 : decode_any W_58e58 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e5c : bv 32 := 0x01513423.
Lemma F_58e5c : fetch_word Asan.M.loaded_segments (0x58eac : word) = Some W_58e5c.
Proof. vm_refl. Qed.
Lemma D_58e5c : decode_any W_58e5c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e60 : bv 32 := 0x01613023.
Lemma F_58e60 : fetch_word Asan.M.loaded_segments (0x58eb0 : word) = Some W_58e60.
Proof. vm_refl. Qed.
Lemma D_58e60 : decode_any W_58e60 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e64 : bv 32 := 0x02058e63.
Lemma F_58e64 : fetch_word Asan.M.loaded_segments (0x58eb4 : word) = Some W_58e64.
Proof. vm_refl. Qed.
Lemma D_58e64 : decode_any W_58e64 = Some (Branch BC_EQ 11 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e68 : bv 32 := 0x00078a13.
Lemma F_58e68 : fetch_word Asan.M.loaded_segments (0x58eb8 : word) = Some W_58e68.
Proof. vm_refl. Qed.
Lemma D_58e68 : decode_any W_58e68 = Some (OpImm ALU_ADD 20 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e6c : bv 32 := 0x00070413.
Lemma F_58e6c : fetch_word Asan.M.loaded_segments (0x58ebc : word) = Some W_58e6c.
Proof. vm_refl. Qed.
Lemma D_58e6c : decode_any W_58e6c = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e70 : bv 32 := 0x00058493.
Lemma F_58e70 : fetch_word Asan.M.loaded_segments (0x58ec0 : word) = Some W_58e70.
Proof. vm_refl. Qed.
Lemma D_58e70 : decode_any W_58e70 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e74 : bv 32 := 0x00050993.
Lemma F_58e74 : fetch_word Asan.M.loaded_segments (0x58ec4 : word) = Some W_58e74.
Proof. vm_refl. Qed.
Lemma D_58e74 : decode_any W_58e74 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e78 : bv 32 := 0x00060a93.
Lemma F_58e78 : fetch_word Asan.M.loaded_segments (0x58ec8 : word) = Some W_58e78.
Proof. vm_refl. Qed.
Lemma D_58e78 : decode_any W_58e78 = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e7c : bv 32 := 0x00068b13.
Lemma F_58e7c : fetch_word Asan.M.loaded_segments (0x58ecc : word) = Some W_58e7c.
Proof. vm_refl. Qed.
Lemma D_58e7c : decode_any W_58e7c = Some (OpImm ALU_ADD 22 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e80 : bv 32 := 0xff058913.
Lemma F_58e80 : fetch_word Asan.M.loaded_segments (0x58ed0 : word) = Some W_58e80.
Proof. vm_refl. Qed.
Lemma D_58e80 : decode_any W_58e80 = Some (OpImm ALU_ADD 18 11 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e84 : bv 32 := 0x00058513.
Lemma F_58e84 : fetch_word Asan.M.loaded_segments (0x58ed4 : word) = Some W_58e84.
Proof. vm_refl. Qed.
Lemma D_58e84 : decode_any W_58e84 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e88 : bv 32 := 0x1c4360ef.
Lemma F_58e88 : fetch_word Asan.M.loaded_segments (0x58ed8 : word) = Some W_58e88.
Proof. vm_refl. Qed.
Lemma D_58e88 : decode_any W_58e88 = Some (Jal 1 221636, 4%Z).
Proof. vm_refl. Qed.

Definition W_58e8c : bv 32 := 0x02050e63.
Lemma F_58e8c : fetch_word Asan.M.loaded_segments (0x58edc : word) = Some W_58e8c.
Proof. vm_refl. Qed.
Lemma D_58e8c : decode_any W_58e8c = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ea0 : bv 32 := 0x03813083.
Lemma F_58ea0 : fetch_word Asan.M.loaded_segments (0x58ef0 : word) = Some W_58ea0.
Proof. vm_refl. Qed.
Lemma D_58ea0 : decode_any W_58ea0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ea4 : bv 32 := 0x03013403.
Lemma F_58ea4 : fetch_word Asan.M.loaded_segments (0x58ef4 : word) = Some W_58ea4.
Proof. vm_refl. Qed.
Lemma D_58ea4 : decode_any W_58ea4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ea8 : bv 32 := 0x02813483.
Lemma F_58ea8 : fetch_word Asan.M.loaded_segments (0x58ef8 : word) = Some W_58ea8.
Proof. vm_refl. Qed.
Lemma D_58ea8 : decode_any W_58ea8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_58eac : bv 32 := 0x02013903.
Lemma F_58eac : fetch_word Asan.M.loaded_segments (0x58efc : word) = Some W_58eac.
Proof. vm_refl. Qed.
Lemma D_58eac : decode_any W_58eac = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_58eb0 : bv 32 := 0x01813983.
Lemma F_58eb0 : fetch_word Asan.M.loaded_segments (0x58f00 : word) = Some W_58eb0.
Proof. vm_refl. Qed.
Lemma D_58eb0 : decode_any W_58eb0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58eb4 : bv 32 := 0x01013a03.
Lemma F_58eb4 : fetch_word Asan.M.loaded_segments (0x58f04 : word) = Some W_58eb4.
Proof. vm_refl. Qed.
Lemma D_58eb4 : decode_any W_58eb4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58eb8 : bv 32 := 0x00813a83.
Lemma F_58eb8 : fetch_word Asan.M.loaded_segments (0x58f08 : word) = Some W_58eb8.
Proof. vm_refl. Qed.
Lemma D_58eb8 : decode_any W_58eb8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ebc : bv 32 := 0x00013b03.
Lemma F_58ebc : fetch_word Asan.M.loaded_segments (0x58f0c : word) = Some W_58ebc.
Proof. vm_refl. Qed.
Lemma D_58ebc : decode_any W_58ebc = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ec0 : bv 32 := 0x04010113.
Lemma F_58ec0 : fetch_word Asan.M.loaded_segments (0x58f10 : word) = Some W_58ec0.
Proof. vm_refl. Qed.
Lemma D_58ec0 : decode_any W_58ec0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ec4 : bv 32 := 0x00008067.
Lemma F_58ec4 : fetch_word Asan.M.loaded_segments (0x58f14 : word) = Some W_58ec4.
Proof. vm_refl. Qed.
Lemma D_58ec4 : decode_any W_58ec4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ec8 : bv 32 := 0xffc97693.
Lemma F_58ec8 : fetch_word Asan.M.loaded_segments (0x58f18 : word) = Some W_58ec8.
Proof. vm_refl. Qed.
Lemma D_58ec8 : decode_any W_58ec8 = Some (OpImm ALU_AND 13 18 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ecc : bv 32 := 0x00391513.
Lemma F_58ecc : fetch_word Asan.M.loaded_segments (0x58f1c : word) = Some W_58ecc.
Proof. vm_refl. Qed.
Lemma D_58ecc : decode_any W_58ecc = Some (ShiftImm ALU_SLL 10 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ed0 : bv 32 := 0x0ff00613.
Lemma F_58ed0 : fetch_word Asan.M.loaded_segments (0x58f20 : word) = Some W_58ed0.
Proof. vm_refl. Qed.
Lemma D_58ed0 : decode_any W_58ed0 = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ed4 : bv 32 := 0x00200713.
Lemma F_58ed4 : fetch_word Asan.M.loaded_segments (0x58f24 : word) = Some W_58ed4.
Proof. vm_refl. Qed.
Lemma D_58ed4 : decode_any W_58ed4 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ed8 : bv 32 := 0x00300593.
Lemma F_58ed8 : fetch_word Asan.M.loaded_segments (0x58f28 : word) = Some W_58ed8.
Proof. vm_refl. Qed.
Lemma D_58ed8 : decode_any W_58ed8 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58edc : bv 32 := 0x00a617bb.
Lemma F_58edc : fetch_word Asan.M.loaded_segments (0x58f2c : word) = Some W_58edc.
Proof. vm_refl. Qed.
Lemma D_58edc : decode_any W_58edc = Some (Op32 ALU_SLL 15 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ee0 : bv 32 := 0x00a7173b.
Lemma F_58ee0 : fetch_word Asan.M.loaded_segments (0x58f30 : word) = Some W_58ee0.
Proof. vm_refl. Qed.
Lemma D_58ee0 : decode_any W_58ee0 = Some (Op32 ALU_SLL 14 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ee4 : bv 32 := 0x00a5983b.
Lemma F_58ee4 : fetch_word Asan.M.loaded_segments (0x58f34 : word) = Some W_58ee4.
Proof. vm_refl. Qed.
Lemma D_58ee4 : decode_any W_58ee4 = Some (Op32 ALU_SLL 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ee8 : bv 32 := 0x1606a62f.
Lemma F_58ee8 : fetch_word Asan.M.loaded_segments (0x58f38 : word) = Some W_58ee8.
Proof. vm_refl. Qed.
Lemma D_58ee8 : decode_any W_58ee8 = Some (Lr AW true true 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_58eec : bv 32 := 0x00f678b3.
Lemma F_58eec : fetch_word Asan.M.loaded_segments (0x58f3c : word) = Some W_58eec.
Proof. vm_refl. Qed.
Lemma D_58eec : decode_any W_58eec = Some (Op ALU_AND 17 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ef0 : bv 32 := 0x08e89063.
Lemma F_58ef0 : fetch_word Asan.M.loaded_segments (0x58f40 : word) = Some W_58ef0.
Proof. vm_refl. Qed.
Lemma D_58ef0 : decode_any W_58ef0 = Some (Branch BC_NE 17 14 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ef4 : bv 32 := 0x010648b3.
Lemma F_58ef4 : fetch_word Asan.M.loaded_segments (0x58f44 : word) = Some W_58ef4.
Proof. vm_refl. Qed.
Lemma D_58ef4 : decode_any W_58ef4 = Some (Op ALU_XOR 17 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ef8 : bv 32 := 0x00f8f8b3.
Lemma F_58ef8 : fetch_word Asan.M.loaded_segments (0x58f48 : word) = Some W_58ef8.
Proof. vm_refl. Qed.
Lemma D_58ef8 : decode_any W_58ef8 = Some (Op ALU_AND 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_58efc : bv 32 := 0x011648b3.
Lemma F_58efc : fetch_word Asan.M.loaded_segments (0x58f4c : word) = Some W_58efc.
Proof. vm_refl. Qed.
Lemma D_58efc : decode_any W_58efc = Some (Op ALU_XOR 17 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f00 : bv 32 := 0x1b16a8af.
Lemma F_58f00 : fetch_word Asan.M.loaded_segments (0x58f50 : word) = Some W_58f00.
Proof. vm_refl. Qed.
Lemma D_58f00 : decode_any W_58f00 = Some (Sc AW false true 17 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f04 : bv 32 := 0xfe0892e3.
Lemma F_58f04 : fetch_word Asan.M.loaded_segments (0x58f54 : word) = Some W_58f04.
Proof. vm_refl. Qed.
Lemma D_58f04 : decode_any W_58f04 = Some (Branch BC_NE 17 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f08 : bv 32 := 0xfff00513.
Lemma F_58f08 : fetch_word Asan.M.loaded_segments (0x58f58 : word) = Some W_58f08.
Proof. vm_refl. Qed.
Lemma D_58f08 : decode_any W_58f08 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f0c : bv 32 := 0x02051513.
Lemma F_58f0c : fetch_word Asan.M.loaded_segments (0x58f5c : word) = Some W_58f0c.
Proof. vm_refl. Qed.
Lemma D_58f0c : decode_any W_58f0c = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f10 : bv 32 := 0x00a93823.
Lemma F_58f10 : fetch_word Asan.M.loaded_segments (0x58f60 : word) = Some W_58f10.
Proof. vm_refl. Qed.
Lemma D_58f10 : decode_any W_58f10 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f14 : bv 32 := 0x00194503.
Lemma F_58f14 : fetch_word Asan.M.loaded_segments (0x58f64 : word) = Some W_58f14.
Proof. vm_refl. Qed.
Lemma D_58f14 : decode_any W_58f14 = Some (Load SZ1 false 10 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f18 : bv 32 := 0x00357593.
Lemma F_58f18 : fetch_word Asan.M.loaded_segments (0x58f68 : word) = Some W_58f18.
Proof. vm_refl. Qed.
Lemma D_58f18 : decode_any W_58f18 = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f1c : bv 32 := 0x08ba1863.
Lemma F_58f1c : fetch_word Asan.M.loaded_segments (0x58f6c : word) = Some W_58f1c.
Proof. vm_refl. Qed.
Lemma D_58f1c : decode_any W_58f1c = Some (Branch BC_NE 20 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f20 : bv 32 := 0xffea7693.
Lemma F_58f20 : fetch_word Asan.M.loaded_segments (0x58f70 : word) = Some W_58f20.
Proof. vm_refl. Qed.
Lemma D_58f20 : decode_any W_58f20 = Some (OpImm ALU_AND 13 20 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f24 : bv 32 := 0x00200713.
Lemma F_58f24 : fetch_word Asan.M.loaded_segments (0x58f74 : word) = Some W_58f24.
Proof. vm_refl. Qed.
Lemma D_58f24 : decode_any W_58f24 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f28 : bv 32 := 0x14e69663.
Lemma F_58f28 : fetch_word Asan.M.loaded_segments (0x58f78 : word) = Some W_58f28.
Proof. vm_refl. Qed.
Lemma D_58f28 : decode_any W_58f28 = Some (Branch BC_NE 13 14 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_59074 : bv 32 := 0x115300ef.
Lemma F_59074 : fetch_word Asan.M.loaded_segments (0x590c4 : word) = Some W_59074.
Proof. vm_refl. Qed.
Lemma D_59074 : decode_any W_59074 = Some (Jal 1 198932, 4%Z).
Proof. vm_refl. Qed.

Definition W_59078 : bv 32 := 0xff24d583.
Lemma F_59078 : fetch_word Asan.M.loaded_segments (0x590c8 : word) = Some W_59078.
Proof. vm_refl. Qed.
Lemma D_59078 : decode_any W_59078 = Some (Load SZ2 false 11 9 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_5907c : bv 32 := 0xff44e603.
Lemma F_5907c : fetch_word Asan.M.loaded_segments (0x590cc : word) = Some W_5907c.
Proof. vm_refl. Qed.
Lemma D_5907c : decode_any W_5907c = Some (Load SZ4 false 12 9 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_59080 : bv 32 := 0x02053683.
Lemma F_59080 : fetch_word Asan.M.loaded_segments (0x590d0 : word) = Some W_59080.
Proof. vm_refl. Qed.
Lemma D_59080 : decode_any W_59080 = Some (Load SZ8 true 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59084 : bv 32 := 0x01853703.
Lemma F_59084 : fetch_word Asan.M.loaded_segments (0x590d4 : word) = Some W_59084.
Proof. vm_refl. Qed.
Lemma D_59084 : decode_any W_59084 = Some (Load SZ8 true 14 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_59088 : bv 32 := 0x02059593.
Lemma F_59088 : fetch_word Asan.M.loaded_segments (0x590d8 : word) = Some W_59088.
Proof. vm_refl. Qed.
Lemma D_59088 : decode_any W_59088 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5908c : bv 32 := 0x00c5e5b3.
Lemma F_5908c : fetch_word Asan.M.loaded_segments (0x590dc : word) = Some W_5908c.
Proof. vm_refl. Qed.
Lemma D_5908c : decode_any W_5908c = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59090 : bv 32 := 0x00d585b3.
Lemma F_59090 : fetch_word Asan.M.loaded_segments (0x590e0 : word) = Some W_59090.
Proof. vm_refl. Qed.
Lemma D_59090 : decode_any W_59090 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_59094 : bv 32 := 0x00170713.
Lemma F_59094 : fetch_word Asan.M.loaded_segments (0x590e4 : word) = Some W_59094.
Proof. vm_refl. Qed.
Lemma D_59094 : decode_any W_59094 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59098 : bv 32 := 0x00e53c23.
Lemma F_59098 : fetch_word Asan.M.loaded_segments (0x590e8 : word) = Some W_59098.
Proof. vm_refl. Qed.
Lemma D_59098 : decode_any W_59098 = Some (Store SZ8 10 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5909c : bv 32 := 0x02b53023.
Lemma F_5909c : fetch_word Asan.M.loaded_segments (0x590ec : word) = Some W_5909c.
Proof. vm_refl. Qed.
Lemma D_5909c : decode_any W_5909c = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_590a0 : bv 32 := 0x00098513.
Lemma F_590a0 : fetch_word Asan.M.loaded_segments (0x590f0 : word) = Some W_590a0.
Proof. vm_refl. Qed.
Lemma D_590a0 : decode_any W_590a0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_590a4 : bv 32 := 0x00090593.
Lemma F_590a4 : fetch_word Asan.M.loaded_segments (0x590f4 : word) = Some W_590a4.
Proof. vm_refl. Qed.
Lemma D_590a4 : decode_any W_590a4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_590a8 : bv 32 := 0x00048613.
Lemma F_590a8 : fetch_word Asan.M.loaded_segments (0x590f8 : word) = Some W_590a8.
Proof. vm_refl. Qed.
Lemma D_590a8 : decode_any W_590a8 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_590ac : bv 32 := 0x00040693.
Lemma F_590ac : fetch_word Asan.M.loaded_segments (0x590fc : word) = Some W_590ac.
Proof. vm_refl. Qed.
Lemma D_590ac : decode_any W_590ac = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_590b0 : bv 32 := 0x03813083.
Lemma F_590b0 : fetch_word Asan.M.loaded_segments (0x59100 : word) = Some W_590b0.
Proof. vm_refl. Qed.
Lemma D_590b0 : decode_any W_590b0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_590b4 : bv 32 := 0x03013403.
Lemma F_590b4 : fetch_word Asan.M.loaded_segments (0x59104 : word) = Some W_590b4.
Proof. vm_refl. Qed.
Lemma D_590b4 : decode_any W_590b4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_590b8 : bv 32 := 0x02813483.
Lemma F_590b8 : fetch_word Asan.M.loaded_segments (0x59108 : word) = Some W_590b8.
Proof. vm_refl. Qed.
Lemma D_590b8 : decode_any W_590b8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_590bc : bv 32 := 0x02013903.
Lemma F_590bc : fetch_word Asan.M.loaded_segments (0x5910c : word) = Some W_590bc.
Proof. vm_refl. Qed.
Lemma D_590bc : decode_any W_590bc = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_590c0 : bv 32 := 0x01813983.
Lemma F_590c0 : fetch_word Asan.M.loaded_segments (0x59110 : word) = Some W_590c0.
Proof. vm_refl. Qed.
Lemma D_590c0 : decode_any W_590c0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_590c4 : bv 32 := 0x01013a03.
Lemma F_590c4 : fetch_word Asan.M.loaded_segments (0x59114 : word) = Some W_590c4.
Proof. vm_refl. Qed.
Lemma D_590c4 : decode_any W_590c4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_590c8 : bv 32 := 0x00813a83.
Lemma F_590c8 : fetch_word Asan.M.loaded_segments (0x59118 : word) = Some W_590c8.
Proof. vm_refl. Qed.
Lemma D_590c8 : decode_any W_590c8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_590cc : bv 32 := 0x00013b03.
Lemma F_590cc : fetch_word Asan.M.loaded_segments (0x5911c : word) = Some W_590cc.
Proof. vm_refl. Qed.
Lemma D_590cc : decode_any W_590cc = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_590d0 : bv 32 := 0x04010113.
Lemma F_590d0 : fetch_word Asan.M.loaded_segments (0x59120 : word) = Some W_590d0.
Proof. vm_refl. Qed.
Lemma D_590d0 : decode_any W_590d0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_590d4 : bv 32 := 0x2cc0406f.
Lemma F_590d4 : fetch_word Asan.M.loaded_segments (0x59124 : word) = Some W_590d4.
Proof. vm_refl. Qed.
Lemma D_590d4 : decode_any W_590d4 = Some (Jal 0 17100, 4%Z).
Proof. vm_refl. Qed.

Definition W_590f8 : bv 32 := 0xff010113.
Lemma F_590f8 : fetch_word Asan.M.loaded_segments (0x59148 : word) = Some W_590f8.
Proof. vm_refl. Qed.
Lemma D_590f8 : decode_any W_590f8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_590fc : bv 32 := 0x00113423.
Lemma F_590fc : fetch_word Asan.M.loaded_segments (0x5914c : word) = Some W_590fc.
Proof. vm_refl. Qed.
Lemma D_590fc : decode_any W_590fc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59100 : bv 32 := 0x00813023.
Lemma F_59100 : fetch_word Asan.M.loaded_segments (0x59150 : word) = Some W_59100.
Proof. vm_refl. Qed.
Lemma D_59100 : decode_any W_59100 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59104 : bv 32 := 0x00058693.
Lemma F_59104 : fetch_word Asan.M.loaded_segments (0x59154 : word) = Some W_59104.
Proof. vm_refl. Qed.
Lemma D_59104 : decode_any W_59104 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59108 : bv 32 := 0x00050593.
Lemma F_59108 : fetch_word Asan.M.loaded_segments (0x59158 : word) = Some W_59108.
Proof. vm_refl. Qed.
Lemma D_59108 : decode_any W_59108 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5910c : bv 32 := 0x00103517.
Lemma F_5910c : fetch_word Asan.M.loaded_segments (0x5915c : word) = Some W_5910c.
Proof. vm_refl. Qed.
Lemma D_5910c : decode_any W_5910c = Some (Auipc 10 259, 4%Z).
Proof. vm_refl. Qed.

Definition W_59110 : bv 32 := 0x00800613.
Lemma F_59110 : fetch_word Asan.M.loaded_segments (0x59160 : word) = Some W_59110.
Proof. vm_refl. Qed.
Lemma D_59110 : decode_any W_59110 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59114 : bv 32 := 0x00100713.
Lemma F_59114 : fetch_word Asan.M.loaded_segments (0x59164 : word) = Some W_59114.
Proof. vm_refl. Qed.
Lemma D_59114 : decode_any W_59114 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59118 : bv 32 := 0x2bc50513.
Lemma F_59118 : fetch_word Asan.M.loaded_segments (0x59168 : word) = Some W_59118.
Proof. vm_refl. Qed.
Lemma D_59118 : decode_any W_59118 = Some (OpImm ALU_ADD 10 10 700, 4%Z).
Proof. vm_refl. Qed.

Definition W_5911c : bv 32 := 0x00100793.
Lemma F_5911c : fetch_word Asan.M.loaded_segments (0x5916c : word) = Some W_5911c.
Proof. vm_refl. Qed.
Lemma D_5911c : decode_any W_5911c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59120 : bv 32 := 0x034000ef.
Lemma F_59120 : fetch_word Asan.M.loaded_segments (0x59170 : word) = Some W_59120.
Proof. vm_refl. Qed.
Lemma D_59120 : decode_any W_59120 = Some (Jal 1 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_59124 : bv 32 := 0x00050a63.
Lemma F_59124 : fetch_word Asan.M.loaded_segments (0x59174 : word) = Some W_59124.
Proof. vm_refl. Qed.
Lemma D_59124 : decode_any W_59124 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_59128 : bv 32 := 0x00813083.
Lemma F_59128 : fetch_word Asan.M.loaded_segments (0x59178 : word) = Some W_59128.
Proof. vm_refl. Qed.
Lemma D_59128 : decode_any W_59128 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5912c : bv 32 := 0x00013403.
Lemma F_5912c : fetch_word Asan.M.loaded_segments (0x5917c : word) = Some W_5912c.
Proof. vm_refl. Qed.
Lemma D_5912c : decode_any W_5912c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59130 : bv 32 := 0x01010113.
Lemma F_59130 : fetch_word Asan.M.loaded_segments (0x59180 : word) = Some W_59130.
Proof. vm_refl. Qed.
Lemma D_59130 : decode_any W_59130 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59134 : bv 32 := 0x00008067.
Lemma F_59134 : fetch_word Asan.M.loaded_segments (0x59184 : word) = Some W_59134.
Proof. vm_refl. Qed.
Lemma D_59134 : decode_any W_59134 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59154 : bv 32 := 0xf8010113.
Lemma F_59154 : fetch_word Asan.M.loaded_segments (0x591a4 : word) = Some W_59154.
Proof. vm_refl. Qed.
Lemma D_59154 : decode_any W_59154 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_59158 : bv 32 := 0x06113c23.
Lemma F_59158 : fetch_word Asan.M.loaded_segments (0x591a8 : word) = Some W_59158.
Proof. vm_refl. Qed.
Lemma D_59158 : decode_any W_59158 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5915c : bv 32 := 0x06813823.
Lemma F_5915c : fetch_word Asan.M.loaded_segments (0x591ac : word) = Some W_5915c.
Proof. vm_refl. Qed.
Lemma D_5915c : decode_any W_5915c = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_59160 : bv 32 := 0x06913423.
Lemma F_59160 : fetch_word Asan.M.loaded_segments (0x591b0 : word) = Some W_59160.
Proof. vm_refl. Qed.
Lemma D_59160 : decode_any W_59160 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_59164 : bv 32 := 0x07213023.
Lemma F_59164 : fetch_word Asan.M.loaded_segments (0x591b4 : word) = Some W_59164.
Proof. vm_refl. Qed.
Lemma D_59164 : decode_any W_59164 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_59168 : bv 32 := 0x05313c23.
Lemma F_59168 : fetch_word Asan.M.loaded_segments (0x591b8 : word) = Some W_59168.
Proof. vm_refl. Qed.
Lemma D_59168 : decode_any W_59168 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5916c : bv 32 := 0x05413823.
Lemma F_5916c : fetch_word Asan.M.loaded_segments (0x591bc : word) = Some W_5916c.
Proof. vm_refl. Qed.
Lemma D_5916c : decode_any W_5916c = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_59170 : bv 32 := 0x05513423.
Lemma F_59170 : fetch_word Asan.M.loaded_segments (0x591c0 : word) = Some W_59170.
Proof. vm_refl. Qed.
Lemma D_59170 : decode_any W_59170 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_59174 : bv 32 := 0x05613023.
Lemma F_59174 : fetch_word Asan.M.loaded_segments (0x591c4 : word) = Some W_59174.
Proof. vm_refl. Qed.
Lemma D_59174 : decode_any W_59174 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_59178 : bv 32 := 0x03713c23.
Lemma F_59178 : fetch_word Asan.M.loaded_segments (0x591c8 : word) = Some W_59178.
Proof. vm_refl. Qed.
Lemma D_59178 : decode_any W_59178 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5917c : bv 32 := 0x03813823.
Lemma F_5917c : fetch_word Asan.M.loaded_segments (0x591cc : word) = Some W_5917c.
Proof. vm_refl. Qed.
Lemma D_5917c : decode_any W_5917c = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_59180 : bv 32 := 0x03913423.
Lemma F_59180 : fetch_word Asan.M.loaded_segments (0x591d0 : word) = Some W_59180.
Proof. vm_refl. Qed.
Lemma D_59180 : decode_any W_59180 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_59184 : bv 32 := 0x03a13023.
Lemma F_59184 : fetch_word Asan.M.loaded_segments (0x591d4 : word) = Some W_59184.
Proof. vm_refl. Qed.
Lemma D_59184 : decode_any W_59184 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59188 : bv 32 := 0x01b13c23.
Lemma F_59188 : fetch_word Asan.M.loaded_segments (0x591d8 : word) = Some W_59188.
Proof. vm_refl. Qed.
Lemma D_59188 : decode_any W_59188 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5918c : bv 32 := 0x00078493.
Lemma F_5918c : fetch_word Asan.M.loaded_segments (0x591dc : word) = Some W_5918c.
Proof. vm_refl. Qed.
Lemma D_5918c : decode_any W_5918c = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59190 : bv 32 := 0x00070d93.
Lemma F_59190 : fetch_word Asan.M.loaded_segments (0x591e0 : word) = Some W_59190.
Proof. vm_refl. Qed.
Lemma D_59190 : decode_any W_59190 = Some (OpImm ALU_ADD 27 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59194 : bv 32 := 0x00068b93.
Lemma F_59194 : fetch_word Asan.M.loaded_segments (0x591e4 : word) = Some W_59194.
Proof. vm_refl. Qed.
Lemma D_59194 : decode_any W_59194 = Some (OpImm ALU_ADD 23 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59198 : bv 32 := 0x00060913.
Lemma F_59198 : fetch_word Asan.M.loaded_segments (0x591e8 : word) = Some W_59198.
Proof. vm_refl. Qed.
Lemma D_59198 : decode_any W_59198 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5919c : bv 32 := 0x00058a93.
Lemma F_5919c : fetch_word Asan.M.loaded_segments (0x591ec : word) = Some W_5919c.
Proof. vm_refl. Qed.
Lemma D_5919c : decode_any W_5919c = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_591a0 : bv 32 := 0x00050b13.
Lemma F_591a0 : fetch_word Asan.M.loaded_segments (0x591f0 : word) = Some W_591a0.
Proof. vm_refl. Qed.
Lemma D_591a0 : decode_any W_591a0 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_591a4 : bv 32 := 0x7092d0ef.
Lemma F_591a4 : fetch_word Asan.M.loaded_segments (0x591f4 : word) = Some W_591a4.
Proof. vm_refl. Qed.
Lemma D_591a4 : decode_any W_591a4 = Some (Jal 1 188168, 4%Z).
Proof. vm_refl. Qed.

Definition W_591a8 : bv 32 := 0x7e050463.
Lemma F_591a8 : fetch_word Asan.M.loaded_segments (0x591f8 : word) = Some W_591a8.
Proof. vm_refl. Qed.
Lemma D_591a8 : decode_any W_591a8 = Some (Branch BC_EQ 10 0 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_591ac : bv 32 := 0x3c9330ef.
Lemma F_591ac : fetch_word Asan.M.loaded_segments (0x591fc : word) = Some W_591ac.
Proof. vm_refl. Qed.
Lemma D_591ac : decode_any W_591ac = Some (Jal 1 211912, 4%Z).
Proof. vm_refl. Qed.

Definition W_591b0 : bv 32 := 0x7e051663.
Lemma F_591b0 : fetch_word Asan.M.loaded_segments (0x59200 : word) = Some W_591b0.
Proof. vm_refl. Qed.
Lemma D_591b0 : decode_any W_591b0 = Some (Branch BC_NE 10 0 2028, 4%Z).
Proof. vm_refl. Qed.

Definition W_591b4 : bv 32 := 0x080b86e3.
Lemma F_591b4 : fetch_word Asan.M.loaded_segments (0x59204 : word) = Some W_591b4.
Proof. vm_refl. Qed.
Lemma D_591b4 : decode_any W_591b4 = Some (Branch BC_EQ 23 0 2188, 4%Z).
Proof. vm_refl. Qed.

Definition W_591b8 : bv 32 := 0x00800513.
Lemma F_591b8 : fetch_word Asan.M.loaded_segments (0x59208 : word) = Some W_591b8.
Proof. vm_refl. Qed.
Lemma D_591b8 : decode_any W_591b8 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_591bc : bv 32 := 0x02a97e63.
Lemma F_591bc : fetch_word Asan.M.loaded_segments (0x5920c : word) = Some W_591bc.
Proof. vm_refl. Qed.
Lemma D_591bc : decode_any W_591bc = Some (Branch BC_GEU 18 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_591cc : bv 32 := 0x00800413.
Lemma F_591cc : fetch_word Asan.M.loaded_segments (0x5921c : word) = Some W_591cc.
Proof. vm_refl. Qed.
Lemma D_591cc : decode_any W_591cc = Some (OpImm ALU_ADD 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_591d0 : bv 32 := 0xfff40c93.
Lemma F_591d0 : fetch_word Asan.M.loaded_segments (0x59220 : word) = Some W_591d0.
Proof. vm_refl. Qed.
Lemma D_591d0 : decode_any W_591d0 = Some (OpImm ALU_ADD 25 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_591d4 : bv 32 := 0x01947533.
Lemma F_591d4 : fetch_word Asan.M.loaded_segments (0x59224 : word) = Some W_591d4.
Proof. vm_refl. Qed.
Lemma D_591d4 : decode_any W_591d4 = Some (Op ALU_AND 10 8 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_591d8 : bv 32 := 0x7c051a63.
Lemma F_591d8 : fetch_word Asan.M.loaded_segments (0x59228 : word) = Some W_591d8.
Proof. vm_refl. Qed.
Lemma D_591d8 : decode_any W_591d8 = Some (Branch BC_NE 10 0 2004, 4%Z).
Proof. vm_refl. Qed.

Definition W_591dc : bv 32 := 0x03100513.
Lemma F_591dc : fetch_word Asan.M.loaded_segments (0x5922c : word) = Some W_591dc.
Proof. vm_refl. Qed.
Lemma D_591dc : decode_any W_591dc = Some (OpImm ALU_ADD 10 0 49, 4%Z).
Proof. vm_refl. Qed.

Definition W_591e0 : bv 32 := 0x7ffb0d13.
Lemma F_591e0 : fetch_word Asan.M.loaded_segments (0x59230 : word) = Some W_591e0.
Proof. vm_refl. Qed.
Lemma D_591e0 : decode_any W_591e0 = Some (OpImm ALU_ADD 26 22 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_591e4 : bv 32 := 0x00913423.
Lemma F_591e4 : fetch_word Asan.M.loaded_segments (0x59234 : word) = Some W_591e4.
Proof. vm_refl. Qed.
Lemma D_591e4 : decode_any W_591e4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_591e8 : bv 32 := 0x00b13823.
Lemma F_591e8 : fetch_word Asan.M.loaded_segments (0x59238 : word) = Some W_591e8.
Proof. vm_refl. Qed.
Lemma D_591e8 : decode_any W_591e8 = Some (Store SZ8 2 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_591ec : bv 32 := 0x06aaf463.
Lemma F_591ec : fetch_word Asan.M.loaded_segments (0x5923c : word) = Some W_591ec.
Proof. vm_refl. Qed.
Lemma D_591ec : decode_any W_591ec = Some (Branch BC_GEU 21 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_591f0 : bv 32 := 0x00000993.
Lemma F_591f0 : fetch_word Asan.M.loaded_segments (0x59240 : word) = Some W_591f0.
Proof. vm_refl. Qed.
Lemma D_591f0 : decode_any W_591f0 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_591f4 : bv 32 := 0x0cc0006f.
Lemma F_591f4 : fetch_word Asan.M.loaded_segments (0x59244 : word) = Some W_591f4.
Proof. vm_refl. Qed.
Lemma D_591f4 : decode_any W_591f4 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_591f8 : bv 32 := 0x20000613.
Lemma F_591f8 : fetch_word Asan.M.loaded_segments (0x59248 : word) = Some W_591f8.
Proof. vm_refl. Qed.
Lemma D_591f8 : decode_any W_591f8 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_591fc : bv 32 := 0x00090593.
Lemma F_591fc : fetch_word Asan.M.loaded_segments (0x5924c : word) = Some W_591fc.
Proof. vm_refl. Qed.
Lemma D_591fc : decode_any W_591fc = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59200 : bv 32 := 0x00c96463.
Lemma F_59200 : fetch_word Asan.M.loaded_segments (0x59250 : word) = Some W_59200.
Proof. vm_refl. Qed.
Lemma D_59200 : decode_any W_59200 = Some (Branch BC_LTU 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59208 : bv 32 := 0xfff58613.
Lemma F_59208 : fetch_word Asan.M.loaded_segments (0x59258 : word) = Some W_59208.
Proof. vm_refl. Qed.
Lemma D_59208 : decode_any W_59208 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5920c : bv 32 := 0x00c5f633.
Lemma F_5920c : fetch_word Asan.M.loaded_segments (0x5925c : word) = Some W_5920c.
Proof. vm_refl. Qed.
Lemma D_5920c : decode_any W_5920c = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59210 : bv 32 := 0x040618e3.
Lemma F_59210 : fetch_word Asan.M.loaded_segments (0x59260 : word) = Some W_59210.
Proof. vm_refl. Qed.
Lemma D_59210 : decode_any W_59210 = Some (Branch BC_NE 12 0 2128, 4%Z).
Proof. vm_refl. Qed.

Definition W_59214 : bv 32 := 0xfffb7617.
Lemma F_59214 : fetch_word Asan.M.loaded_segments (0x59264 : word) = Some W_59214.
Proof. vm_refl. Qed.
Lemma D_59214 : decode_any W_59214 = Some (Auipc 12 1048503, 4%Z).
Proof. vm_refl. Qed.

Definition W_59218 : bv 32 := 0x20463603.
Lemma F_59218 : fetch_word Asan.M.loaded_segments (0x59268 : word) = Some W_59218.
Proof. vm_refl. Qed.
Lemma D_59218 : decode_any W_59218 = Some (Load SZ8 true 12 12 516, 4%Z).
Proof. vm_refl. Qed.

Definition W_5921c : bv 32 := 0x40b006b3.
Lemma F_5921c : fetch_word Asan.M.loaded_segments (0x5926c : word) = Some W_5921c.
Proof. vm_refl. Qed.
Lemma D_5921c : decode_any W_5921c = Some (Op ALU_SUB 13 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59220 : bv 32 := 0x00d5f5b3.
Lemma F_59220 : fetch_word Asan.M.loaded_segments (0x59270 : word) = Some W_59220.
Proof. vm_refl. Qed.
Lemma D_59220 : decode_any W_59220 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_59224 : bv 32 := 0x02c585b3.
Lemma F_59224 : fetch_word Asan.M.loaded_segments (0x59274 : word) = Some W_59224.
Proof. vm_refl. Qed.
Lemma D_59224 : decode_any W_59224 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59228 : bv 32 := 0xfffb7617.
Lemma F_59228 : fetch_word Asan.M.loaded_segments (0x59278 : word) = Some W_59228.
Proof. vm_refl. Qed.
Lemma D_59228 : decode_any W_59228 = Some (Auipc 12 1048503, 4%Z).
Proof. vm_refl. Qed.

Definition W_5922c : bv 32 := 0x03a5d593.
Lemma F_5922c : fetch_word Asan.M.loaded_segments (0x5927c : word) = Some W_5922c.
Proof. vm_refl. Qed.
Lemma D_5922c : decode_any W_5922c = Some (ShiftImm ALU_SRL 11 11 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_59230 : bv 32 := 0x27060613.
Lemma F_59230 : fetch_word Asan.M.loaded_segments (0x59280 : word) = Some W_59230.
Proof. vm_refl. Qed.
Lemma D_59230 : decode_any W_59230 = Some (OpImm ALU_ADD 12 12 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_59234 : bv 32 := 0x00b605b3.
Lemma F_59234 : fetch_word Asan.M.loaded_segments (0x59284 : word) = Some W_59234.
Proof. vm_refl. Qed.
Lemma D_59234 : decode_any W_59234 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59238 : bv 32 := 0x0005c583.
Lemma F_59238 : fetch_word Asan.M.loaded_segments (0x59288 : word) = Some W_59238.
Proof. vm_refl. Qed.
Lemma D_59238 : decode_any W_59238 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5923c : bv 32 := 0x00459593.
Lemma F_5923c : fetch_word Asan.M.loaded_segments (0x5928c : word) = Some W_5923c.
Proof. vm_refl. Qed.
Lemma D_5923c : decode_any W_5923c = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_59240 : bv 32 := 0x06058593.
Lemma F_59240 : fetch_word Asan.M.loaded_segments (0x59290 : word) = Some W_59240.
Proof. vm_refl. Qed.
Lemma D_59240 : decode_any W_59240 = Some (OpImm ALU_ADD 11 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_59244 : bv 32 := 0x0705f593.
Lemma F_59244 : fetch_word Asan.M.loaded_segments (0x59294 : word) = Some W_59244.
Proof. vm_refl. Qed.
Lemma D_59244 : decode_any W_59244 = Some (OpImm ALU_AND 11 11 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_59248 : bv 32 := 0x00090413.
Lemma F_59248 : fetch_word Asan.M.loaded_segments (0x59298 : word) = Some W_59248.
Proof. vm_refl. Qed.
Lemma D_59248 : decode_any W_59248 = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5924c : bv 32 := 0xf92570e3.
Lemma F_5924c : fetch_word Asan.M.loaded_segments (0x5929c : word) = Some W_5924c.
Proof. vm_refl. Qed.
Lemma D_5924c : decode_any W_5924c = Some (Branch BC_GEU 10 18 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_59250 : bv 32 := 0xf81ff06f.
Lemma F_59250 : fetch_word Asan.M.loaded_segments (0x592a0 : word) = Some W_59250.
Proof. vm_refl. Qed.
Lemma D_59250 : decode_any W_59250 = Some (Jal 0 2097024, 4%Z).
Proof. vm_refl. Qed.

Definition W_59254 : bv 32 := 0x06100513.
Lemma F_59254 : fetch_word Asan.M.loaded_segments (0x592a4 : word) = Some W_59254.
Proof. vm_refl. Qed.
Lemma D_59254 : decode_any W_59254 = Some (OpImm ALU_ADD 10 0 97, 4%Z).
Proof. vm_refl. Qed.

Definition W_59258 : bv 32 := 0x00aaf663.
Lemma F_59258 : fetch_word Asan.M.loaded_segments (0x592a8 : word) = Some W_59258.
Proof. vm_refl. Qed.
Lemma D_59258 : decode_any W_59258 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5925c : bv 32 := 0x00100993.
Lemma F_5925c : fetch_word Asan.M.loaded_segments (0x592ac : word) = Some W_5925c.
Proof. vm_refl. Qed.
Lemma D_5925c : decode_any W_5925c = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59260 : bv 32 := 0x0600006f.
Lemma F_59260 : fetch_word Asan.M.loaded_segments (0x592b0 : word) = Some W_59260.
Proof. vm_refl. Qed.
Lemma D_59260 : decode_any W_59260 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_59264 : bv 32 := 0x1c100513.
Lemma F_59264 : fetch_word Asan.M.loaded_segments (0x592b4 : word) = Some W_59264.
Proof. vm_refl. Qed.
Lemma D_59264 : decode_any W_59264 = Some (OpImm ALU_ADD 10 0 449, 4%Z).
Proof. vm_refl. Qed.

Definition W_59268 : bv 32 := 0x00aaf663.
Lemma F_59268 : fetch_word Asan.M.loaded_segments (0x592b8 : word) = Some W_59268.
Proof. vm_refl. Qed.
Lemma D_59268 : decode_any W_59268 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5926c : bv 32 := 0x00200993.
Lemma F_5926c : fetch_word Asan.M.loaded_segments (0x592bc : word) = Some W_5926c.
Proof. vm_refl. Qed.
Lemma D_5926c : decode_any W_5926c = Some (OpImm ALU_ADD 19 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_59270 : bv 32 := 0x0500006f.
Lemma F_59270 : fetch_word Asan.M.loaded_segments (0x592c0 : word) = Some W_59270.
Proof. vm_refl. Qed.
Lemma D_59270 : decode_any W_59270 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_59274 : bv 32 := 0x00001537.
Lemma F_59274 : fetch_word Asan.M.loaded_segments (0x592c4 : word) = Some W_59274.
Proof. vm_refl. Qed.
Lemma D_59274 : decode_any W_59274 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59278 : bv 32 := 0xf815051b.
Lemma F_59278 : fetch_word Asan.M.loaded_segments (0x592c8 : word) = Some W_59278.
Proof. vm_refl. Qed.
Lemma D_59278 : decode_any W_59278 = Some (OpImm32 10 10 3969, 4%Z).
Proof. vm_refl. Qed.

Definition W_5927c : bv 32 := 0x00aaf663.
Lemma F_5927c : fetch_word Asan.M.loaded_segments (0x592cc : word) = Some W_5927c.
Proof. vm_refl. Qed.
Lemma D_5927c : decode_any W_5927c = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59280 : bv 32 := 0x00300993.
Lemma F_59280 : fetch_word Asan.M.loaded_segments (0x592d0 : word) = Some W_59280.
Proof. vm_refl. Qed.
Lemma D_59280 : decode_any W_59280 = Some (OpImm ALU_ADD 19 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_59284 : bv 32 := 0x03c0006f.
Lemma F_59284 : fetch_word Asan.M.loaded_segments (0x592d4 : word) = Some W_59284.
Proof. vm_refl. Qed.
Lemma D_59284 : decode_any W_59284 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_59288 : bv 32 := 0x00004537.
Lemma F_59288 : fetch_word Asan.M.loaded_segments (0x592d8 : word) = Some W_59288.
Proof. vm_refl. Qed.
Lemma D_59288 : decode_any W_59288 = Some (Lui 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5928c : bv 32 := 0xf015051b.
Lemma F_5928c : fetch_word Asan.M.loaded_segments (0x592dc : word) = Some W_5928c.
Proof. vm_refl. Qed.
Lemma D_5928c : decode_any W_5928c = Some (OpImm32 10 10 3841, 4%Z).
Proof. vm_refl. Qed.

Definition W_59290 : bv 32 := 0x00aaf663.
Lemma F_59290 : fetch_word Asan.M.loaded_segments (0x592e0 : word) = Some W_59290.
Proof. vm_refl. Qed.
Lemma D_59290 : decode_any W_59290 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59294 : bv 32 := 0x00400993.
Lemma F_59294 : fetch_word Asan.M.loaded_segments (0x592e4 : word) = Some W_59294.
Proof. vm_refl. Qed.
Lemma D_59294 : decode_any W_59294 = Some (OpImm ALU_ADD 19 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_59298 : bv 32 := 0x0280006f.
Lemma F_59298 : fetch_word Asan.M.loaded_segments (0x592e8 : word) = Some W_59298.
Proof. vm_refl. Qed.
Lemma D_59298 : decode_any W_59298 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5929c : bv 32 := 0x00008537.
Lemma F_5929c : fetch_word Asan.M.loaded_segments (0x592ec : word) = Some W_5929c.
Proof. vm_refl. Qed.
Lemma D_5929c : decode_any W_5929c = Some (Lui 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_592a0 : bv 32 := 0xe015051b.
Lemma F_592a0 : fetch_word Asan.M.loaded_segments (0x592f0 : word) = Some W_592a0.
Proof. vm_refl. Qed.
Lemma D_592a0 : decode_any W_592a0 = Some (OpImm32 10 10 3585, 4%Z).
Proof. vm_refl. Qed.

Definition W_592a4 : bv 32 := 0x00aaf663.
Lemma F_592a4 : fetch_word Asan.M.loaded_segments (0x592f4 : word) = Some W_592a4.
Proof. vm_refl. Qed.
Lemma D_592a4 : decode_any W_592a4 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_592a8 : bv 32 := 0x00500993.
Lemma F_592a8 : fetch_word Asan.M.loaded_segments (0x592f8 : word) = Some W_592a8.
Proof. vm_refl. Qed.
Lemma D_592a8 : decode_any W_592a8 = Some (OpImm ALU_ADD 19 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_592ac : bv 32 := 0x0140006f.
Lemma F_592ac : fetch_word Asan.M.loaded_segments (0x592fc : word) = Some W_592ac.
Proof. vm_refl. Qed.
Lemma D_592ac : decode_any W_592ac = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_592b0 : bv 32 := 0x00010537.
Lemma F_592b0 : fetch_word Asan.M.loaded_segments (0x59300 : word) = Some W_592b0.
Proof. vm_refl. Qed.
Lemma D_592b0 : decode_any W_592b0 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_592b4 : bv 32 := 0xc015051b.
Lemma F_592b4 : fetch_word Asan.M.loaded_segments (0x59304 : word) = Some W_592b4.
Proof. vm_refl. Qed.
Lemma D_592b4 : decode_any W_592b4 = Some (OpImm32 10 10 3073, 4%Z).
Proof. vm_refl. Qed.

Definition W_592b8 : bv 32 := 0x00aab533.
Lemma F_592b8 : fetch_word Asan.M.loaded_segments (0x59308 : word) = Some W_592b8.
Proof. vm_refl. Qed.
Lemma D_592b8 : decode_any W_592b8 = Some (Op ALU_SLTU 10 21 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_592bc : bv 32 := 0x00754993.
Lemma F_592bc : fetch_word Asan.M.loaded_segments (0x5930c : word) = Some W_592bc.
Proof. vm_refl. Qed.
Lemma D_592bc : decode_any W_592bc = Some (OpImm ALU_XOR 19 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_592c0 : bv 32 := 0x629d1503.
Lemma F_592c0 : fetch_word Asan.M.loaded_segments (0x59310 : word) = Some W_592c0.
Proof. vm_refl. Qed.
Lemma D_592c0 : decode_any W_592c0 = Some (Load SZ2 true 10 26 1577, 4%Z).
Proof. vm_refl. Qed.

Definition W_592c4 : bv 32 := 0x0230000f.
Lemma F_592c4 : fetch_word Asan.M.loaded_segments (0x59314 : word) = Some W_592c4.
Proof. vm_refl. Qed.
Lemma D_592c4 : decode_any W_592c4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_592c8 : bv 32 := 0x00010a37.
Lemma F_592c8 : fetch_word Asan.M.loaded_segments (0x59318 : word) = Some W_592c8.
Proof. vm_refl. Qed.
Lemma D_592c8 : decode_any W_592c8 = Some (Lui 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_592cc : bv 32 := 0xfffa0c1b.
Lemma F_592cc : fetch_word Asan.M.loaded_segments (0x5931c : word) = Some W_592cc.
Proof. vm_refl. Qed.
Lemma D_592cc : decode_any W_592cc = Some (OpImm32 24 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_592d0 : bv 32 := 0x01857533.
Lemma F_592d0 : fetch_word Asan.M.loaded_segments (0x59320 : word) = Some W_592d0.
Proof. vm_refl. Qed.
Lemma D_592d0 : decode_any W_592d0 = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_592d4 : bv 32 := 0x4a0050ef.
Lemma F_592d4 : fetch_word Asan.M.loaded_segments (0x59324 : word) = Some W_592d4.
Proof. vm_refl. Qed.
Lemma D_592d4 : decode_any W_592d4 = Some (Jal 1 21664, 4%Z).
Proof. vm_refl. Qed.

Definition W_592d8 : bv 32 := 0x00050493.
Lemma F_592d8 : fetch_word Asan.M.loaded_segments (0x59328 : word) = Some W_592d8.
Proof. vm_refl. Qed.
Lemma D_592d8 : decode_any W_592d8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_592dc : bv 32 := 0x62bd1503.
Lemma F_592dc : fetch_word Asan.M.loaded_segments (0x5932c : word) = Some W_592dc.
Proof. vm_refl. Qed.
Lemma D_592dc : decode_any W_592dc = Some (Load SZ2 true 10 26 1579, 4%Z).
Proof. vm_refl. Qed.

Definition W_592e0 : bv 32 := 0x0230000f.
Lemma F_592e0 : fetch_word Asan.M.loaded_segments (0x59330 : word) = Some W_592e0.
Proof. vm_refl. Qed.
Lemma D_592e0 : decode_any W_592e0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_592e4 : bv 32 := 0x01857533.
Lemma F_592e4 : fetch_word Asan.M.loaded_segments (0x59334 : word) = Some W_592e4.
Proof. vm_refl. Qed.
Lemma D_592e4 : decode_any W_592e4 = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_592e8 : bv 32 := 0x48c050ef.
Lemma F_592e8 : fetch_word Asan.M.loaded_segments (0x59338 : word) = Some W_592e8.
Proof. vm_refl. Qed.
Lemma D_592e8 : decode_any W_592e8 = Some (Jal 1 21644, 4%Z).
Proof. vm_refl. Qed.

Definition W_592ec : bv 32 := 0x0b34e663.
Lemma F_592ec : fetch_word Asan.M.loaded_segments (0x5933c : word) = Some W_592ec.
Proof. vm_refl. Qed.
Lemma D_592ec : decode_any W_592ec = Some (Branch BC_LTU 9 19 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_592f0 : bv 32 := 0x00048993.
Lemma F_592f0 : fetch_word Asan.M.loaded_segments (0x59340 : word) = Some W_592f0.
Proof. vm_refl. Qed.
Lemma D_592f0 : decode_any W_592f0 = Some (OpImm ALU_ADD 19 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_592f4 : bv 32 := 0x0aa4f463.
Lemma F_592f4 : fetch_word Asan.M.loaded_segments (0x59344 : word) = Some W_592f4.
Proof. vm_refl. Qed.
Lemma D_592f4 : decode_any W_592f4 = Some (Branch BC_GEU 9 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_592f8 : bv 32 := 0x00800593.
Lemma F_592f8 : fetch_word Asan.M.loaded_segments (0x59348 : word) = Some W_592f8.
Proof. vm_refl. Qed.
Lemma D_592f8 : decode_any W_592f8 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_592fc : bv 32 := 0x000a8513.
Lemma F_592fc : fetch_word Asan.M.loaded_segments (0x5934c : word) = Some W_592fc.
Proof. vm_refl. Qed.
Lemma D_592fc : decode_any W_592fc = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59300 : bv 32 := 0x0155e463.
Lemma F_59300 : fetch_word Asan.M.loaded_segments (0x59350 : word) = Some W_59300.
Proof. vm_refl. Qed.
Lemma D_59300 : decode_any W_59300 = Some (Branch BC_LTU 11 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59304 : bv 32 := 0x00800513.
Lemma F_59304 : fetch_word Asan.M.loaded_segments (0x59354 : word) = Some W_59304.
Proof. vm_refl. Qed.
Lemma D_59304 : decode_any W_59304 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59308 : bv 32 := 0x00850533.
Lemma F_59308 : fetch_word Asan.M.loaded_segments (0x59358 : word) = Some W_59308.
Proof. vm_refl. Qed.
Lemma D_59308 : decode_any W_59308 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5930c : bv 32 := 0x40800c33.
Lemma F_5930c : fetch_word Asan.M.loaded_segments (0x5935c : word) = Some W_5930c.
Proof. vm_refl. Qed.
Lemma D_5930c : decode_any W_5930c = Some (Op ALU_SUB 24 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59310 : bv 32 := 0x00993593.
Lemma F_59310 : fetch_word Asan.M.loaded_segments (0x59360 : word) = Some W_59310.
Proof. vm_refl. Qed.
Lemma D_59310 : decode_any W_59310 = Some (OpImm ALU_SLTU 11 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_59314 : bv 32 := 0xfff50513.
Lemma F_59314 : fetch_word Asan.M.loaded_segments (0x59364 : word) = Some W_59314.
Proof. vm_refl. Qed.
Lemma D_59314 : decode_any W_59314 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_59318 : bv 32 := 0xfff58593.
Lemma F_59318 : fetch_word Asan.M.loaded_segments (0x59368 : word) = Some W_59318.
Proof. vm_refl. Qed.
Lemma D_59318 : decode_any W_59318 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5931c : bv 32 := 0x01857533.
Lemma F_5931c : fetch_word Asan.M.loaded_segments (0x5936c : word) = Some W_5931c.
Proof. vm_refl. Qed.
Lemma D_5931c : decode_any W_5931c = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_59320 : bv 32 := 0x0085f5b3.
Lemma F_59320 : fetch_word Asan.M.loaded_segments (0x59370 : word) = Some W_59320.
Proof. vm_refl. Qed.
Lemma D_59320 : decode_any W_59320 = Some (Op ALU_AND 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59324 : bv 32 := 0x00b50533.
Lemma F_59324 : fetch_word Asan.M.loaded_segments (0x59374 : word) = Some W_59324.
Proof. vm_refl. Qed.
Lemma D_59324 : decode_any W_59324 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59328 : bv 32 := 0x00757593.
Lemma F_59328 : fetch_word Asan.M.loaded_segments (0x59378 : word) = Some W_59328.
Proof. vm_refl. Qed.
Lemma D_59328 : decode_any W_59328 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5932c : bv 32 := 0x6a059063.
Lemma F_5932c : fetch_word Asan.M.loaded_segments (0x5937c : word) = Some W_5932c.
Proof. vm_refl. Qed.
Lemma D_5932c : decode_any W_5932c = Some (Branch BC_NE 11 0 1696, 4%Z).
Proof. vm_refl. Qed.

Definition W_59330 : bv 32 := 0x01000593.
Lemma F_59330 : fetch_word Asan.M.loaded_segments (0x59380 : word) = Some W_59330.
Proof. vm_refl. Qed.
Lemma D_59330 : decode_any W_59330 = Some (OpImm ALU_ADD 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59334 : bv 32 := 0x001ab493.
Lemma F_59334 : fetch_word Asan.M.loaded_segments (0x59384 : word) = Some W_59334.
Proof. vm_refl. Qed.
Lemma D_59334 : decode_any W_59334 = Some (OpImm ALU_SLTU 9 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59338 : bv 32 := 0x001a061b.
Lemma F_59338 : fetch_word Asan.M.loaded_segments (0x59388 : word) = Some W_59338.
Proof. vm_refl. Qed.
Lemma D_59338 : decode_any W_59338 = Some (OpImm32 12 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5933c : bv 32 := 0x01359a3b.
Lemma F_5933c : fetch_word Asan.M.loaded_segments (0x5938c : word) = Some W_5933c.
Proof. vm_refl. Qed.
Lemma D_5933c : decode_any W_5933c = Some (Op32 ALU_SLL 20 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_59340 : bv 32 := 0x00100593.
Lemma F_59340 : fetch_word Asan.M.loaded_segments (0x59390 : word) = Some W_59340.
Proof. vm_refl. Qed.
Lemma D_59340 : decode_any W_59340 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59344 : bv 32 := 0x009a84b3.
Lemma F_59344 : fetch_word Asan.M.loaded_segments (0x59394 : word) = Some W_59344.
Proof. vm_refl. Qed.
Lemma D_59344 : decode_any W_59344 = Some (Op ALU_ADD 9 21 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_59348 : bv 32 := 0x00c936b3.
Lemma F_59348 : fetch_word Asan.M.loaded_segments (0x59398 : word) = Some W_59348.
Proof. vm_refl. Qed.
Lemma D_59348 : decode_any W_59348 = Some (Op ALU_SLTU 13 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5934c : bv 32 := 0x014509b3.
Lemma F_5934c : fetch_word Asan.M.loaded_segments (0x5939c : word) = Some W_5934c.
Proof. vm_refl. Qed.
Lemma D_5934c : decode_any W_5934c = Some (Op ALU_ADD 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_59350 : bv 32 := 0x00c9b433.
Lemma F_59350 : fetch_word Asan.M.loaded_segments (0x593a0 : word) = Some W_59350.
Proof. vm_refl. Qed.
Lemma D_59350 : decode_any W_59350 = Some (Op ALU_SLTU 8 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59354 : bv 32 := 0x0086f433.
Lemma F_59354 : fetch_word Asan.M.loaded_segments (0x593a4 : word) = Some W_59354.
Proof. vm_refl. Qed.
Lemma D_59354 : decode_any W_59354 = Some (Op ALU_AND 8 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59358 : bv 32 := 0xfff40513.
Lemma F_59358 : fetch_word Asan.M.loaded_segments (0x593a8 : word) = Some W_59358.
Proof. vm_refl. Qed.
Lemma D_59358 : decode_any W_59358 = Some (OpImm ALU_ADD 10 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5935c : bv 32 := 0x01457633.
Lemma F_5935c : fetch_word Asan.M.loaded_segments (0x593ac : word) = Some W_5935c.
Proof. vm_refl. Qed.
Lemma D_5935c : decode_any W_5935c = Some (Op ALU_AND 12 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_59360 : bv 32 := 0x02859513.
Lemma F_59360 : fetch_word Asan.M.loaded_segments (0x593b0 : word) = Some W_59360.
Proof. vm_refl. Qed.
Lemma D_59360 : decode_any W_59360 = Some (ShiftImm ALU_SLL 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_59364 : bv 32 := 0x013609b3.
Lemma F_59364 : fetch_word Asan.M.loaded_segments (0x593b4 : word) = Some W_59364.
Proof. vm_refl. Qed.
Lemma D_59364 : decode_any W_59364 = Some (Op ALU_ADD 19 12 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_59368 : bv 32 := 0x01556863.
Lemma F_59368 : fetch_word Asan.M.loaded_segments (0x593b8 : word) = Some W_59368.
Proof. vm_refl. Qed.
Lemma D_59368 : decode_any W_59368 = Some (Branch BC_LTU 10 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5936c : bv 32 := 0x01356663.
Lemma F_5936c : fetch_word Asan.M.loaded_segments (0x593bc : word) = Some W_5936c.
Proof. vm_refl. Qed.
Lemma D_5936c : decode_any W_5936c = Some (Branch BC_LTU 10 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59370 : bv 32 := 0x621d3503.
Lemma F_59370 : fetch_word Asan.M.loaded_segments (0x593c0 : word) = Some W_59370.
Proof. vm_refl. Qed.
Lemma D_59370 : decode_any W_59370 = Some (Load SZ8 true 10 26 1569, 4%Z).
Proof. vm_refl. Qed.

Definition W_59374 : bv 32 := 0x06957063.
Lemma F_59374 : fetch_word Asan.M.loaded_segments (0x593c4 : word) = Some W_59374.
Proof. vm_refl. Qed.
Lemma D_59374 : decode_any W_59374 = Some (Branch BC_GEU 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_59398 : bv 32 := 0xf6a9e0e3.
Lemma F_59398 : fetch_word Asan.M.loaded_segments (0x593e8 : word) = Some W_59398.
Proof. vm_refl. Qed.
Lemma D_59398 : decode_any W_59398 = Some (Branch BC_LTU 19 10 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5939c : bv 32 := 0x00050993.
Lemma F_5939c : fetch_word Asan.M.loaded_segments (0x593ec : word) = Some W_5939c.
Proof. vm_refl. Qed.
Lemma D_5939c : decode_any W_5939c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_593a0 : bv 32 := 0x00800593.
Lemma F_593a0 : fetch_word Asan.M.loaded_segments (0x593f0 : word) = Some W_593a0.
Proof. vm_refl. Qed.
Lemma D_593a0 : decode_any W_593a0 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_593a4 : bv 32 := 0x000a8513.
Lemma F_593a4 : fetch_word Asan.M.loaded_segments (0x593f4 : word) = Some W_593a4.
Proof. vm_refl. Qed.
Lemma D_593a4 : decode_any W_593a4 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_593a8 : bv 32 := 0xf555fee3.
Lemma F_593a8 : fetch_word Asan.M.loaded_segments (0x593f8 : word) = Some W_593a8.
Proof. vm_refl. Qed.
Lemma D_593a8 : decode_any W_593a8 = Some (Branch BC_GEU 11 21 8028, 4%Z).
Proof. vm_refl. Qed.

Definition W_593ac : bv 32 := 0xf5dff06f.
Lemma F_593ac : fetch_word Asan.M.loaded_segments (0x593fc : word) = Some W_593ac.
Proof. vm_refl. Qed.
Lemma D_593ac : decode_any W_593ac = Some (Jal 0 2096988, 4%Z).
Proof. vm_refl. Qed.

Definition W_593d4 : bv 32 := 0x3e8310ef.
Lemma F_593d4 : fetch_word Asan.M.loaded_segments (0x59424 : word) = Some W_593d4.
Proof. vm_refl. Qed.
Lemma D_593d4 : decode_any W_593d4 = Some (Jal 1 201704, 4%Z).
Proof. vm_refl. Qed.

Definition W_593d8 : bv 32 := 0x00050d13.
Lemma F_593d8 : fetch_word Asan.M.loaded_segments (0x59428 : word) = Some W_593d8.
Proof. vm_refl. Qed.
Lemma D_593d8 : decode_any W_593d8 = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_593dc : bv 32 := 0x08050863.
Lemma F_593dc : fetch_word Asan.M.loaded_segments (0x5942c : word) = Some W_593dc.
Proof. vm_refl. Qed.
Lemma D_593dc : decode_any W_593dc = Some (Branch BC_EQ 10 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_593e0 : bv 32 := 0x0d0d0593.
Lemma F_593e0 : fetch_word Asan.M.loaded_segments (0x59430 : word) = Some W_593e0.
Proof. vm_refl. Qed.
Lemma D_593e0 : decode_any W_593e0 = Some (OpImm ALU_ADD 11 26 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_593e4 : bv 32 := 0x00800693.
Lemma F_593e4 : fetch_word Asan.M.loaded_segments (0x59434 : word) = Some W_593e4.
Proof. vm_refl. Qed.
Lemma D_593e4 : decode_any W_593e4 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_593e8 : bv 32 := 0x000b0513.
Lemma F_593e8 : fetch_word Asan.M.loaded_segments (0x59438 : word) = Some W_593e8.
Proof. vm_refl. Qed.
Lemma D_593e8 : decode_any W_593e8 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_593ec : bv 32 := 0x00098613.
Lemma F_593ec : fetch_word Asan.M.loaded_segments (0x5943c : word) = Some W_593ec.
Proof. vm_refl. Qed.
Lemma D_593ec : decode_any W_593ec = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_593f0 : bv 32 := 0x4bc040ef.
Lemma F_593f0 : fetch_word Asan.M.loaded_segments (0x59440 : word) = Some W_593f0.
Proof. vm_refl. Qed.
Lemma D_593f0 : decode_any W_593f0 = Some (Jal 1 17596, 4%Z).
Proof. vm_refl. Qed.

Definition W_593f4 : bv 32 := 0x00050913.
Lemma F_593f4 : fetch_word Asan.M.loaded_segments (0x59444 : word) = Some W_593f4.
Proof. vm_refl. Qed.
Lemma D_593f4 : decode_any W_593f4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_593f8 : bv 32 := 0x0c050663.
Lemma F_593f8 : fetch_word Asan.M.loaded_segments (0x59448 : word) = Some W_593f8.
Proof. vm_refl. Qed.
Lemma D_593f8 : decode_any W_593f8 = Some (Branch BC_EQ 10 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_593fc : bv 32 := 0x01490a33.
Lemma F_593fc : fetch_word Asan.M.loaded_segments (0x5944c : word) = Some W_593fc.
Proof. vm_refl. Qed.
Lemma D_593fc : decode_any W_593fc = Some (Op ALU_ADD 20 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_59400 : bv 32 := 0x019a7533.
Lemma F_59400 : fetch_word Asan.M.loaded_segments (0x59450 : word) = Some W_59400.
Proof. vm_refl. Qed.
Lemma D_59400 : decode_any W_59400 = Some (Op ALU_AND 10 20 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_59404 : bv 32 := 0x01298733.
Lemma F_59404 : fetch_word Asan.M.loaded_segments (0x59454 : word) = Some W_59404.
Proof. vm_refl. Qed.
Lemma D_59404 : decode_any W_59404 = Some (Op ALU_ADD 14 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_59408 : bv 32 := 0x00050663.
Lemma F_59408 : fetch_word Asan.M.loaded_segments (0x59458 : word) = Some W_59408.
Proof. vm_refl. Qed.
Lemma D_59408 : decode_any W_59408 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59414 : bv 32 := 0x009a0cb3.
Lemma F_59414 : fetch_word Asan.M.loaded_segments (0x59464 : word) = Some W_59414.
Proof. vm_refl. Qed.
Lemma D_59414 : decode_any W_59414 = Some (Op ALU_ADD 25 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_59418 : bv 32 := 0x5d976a63.
Lemma F_59418 : fetch_word Asan.M.loaded_segments (0x59468 : word) = Some W_59418.
Proof. vm_refl. Qed.
Lemma D_59418 : decode_any W_59418 = Some (Branch BC_LTU 14 25 1492, 4%Z).
Proof. vm_refl. Qed.

Definition W_5941c : bv 32 := 0xff1a4503.
Lemma F_5941c : fetch_word Asan.M.loaded_segments (0x5946c : word) = Some W_5941c.
Proof. vm_refl. Qed.
Lemma D_5941c : decode_any W_5941c = Some (Load SZ1 false 10 20 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_59420 : bv 32 := 0x003df593.
Lemma F_59420 : fetch_word Asan.M.loaded_segments (0x59470 : word) = Some W_59420.
Proof. vm_refl. Qed.
Lemma D_59420 : decode_any W_59420 = Some (OpImm ALU_AND 11 27 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_59424 : bv 32 := 0xffc57513.
Lemma F_59424 : fetch_word Asan.M.loaded_segments (0x59474 : word) = Some W_59424.
Proof. vm_refl. Qed.
Lemma D_59424 : decode_any W_59424 = Some (OpImm ALU_AND 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_59428 : bv 32 := 0x00b56533.
Lemma F_59428 : fetch_word Asan.M.loaded_segments (0x59478 : word) = Some W_59428.
Proof. vm_refl. Qed.
Lemma D_59428 : decode_any W_59428 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5942c : bv 32 := 0x0204d593.
Lemma F_5942c : fetch_word Asan.M.loaded_segments (0x5947c : word) = Some W_5942c.
Proof. vm_refl. Qed.
Lemma D_5942c : decode_any W_5942c = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59430 : bv 32 := 0x030ad613.
Lemma F_59430 : fetch_word Asan.M.loaded_segments (0x59480 : word) = Some W_59430.
Proof. vm_refl. Qed.
Lemma D_59430 : decode_any W_59430 = Some (ShiftImm ALU_SRL 12 21 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_59434 : bv 32 := 0xfeaa08a3.
Lemma F_59434 : fetch_word Asan.M.loaded_segments (0x59484 : word) = Some W_59434.
Proof. vm_refl. Qed.
Lemma D_59434 : decode_any W_59434 = Some (Store SZ1 20 10 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_59438 : bv 32 := 0xfeba1923.
Lemma F_59438 : fetch_word Asan.M.loaded_segments (0x59488 : word) = Some W_59438.
Proof. vm_refl. Qed.
Lemma D_59438 : decode_any W_59438 = Some (Store SZ2 20 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_5943c : bv 32 := 0xfe9a2a23.
Lemma F_5943c : fetch_word Asan.M.loaded_segments (0x5948c : word) = Some W_5943c.
Proof. vm_refl. Qed.
Lemma D_5943c : decode_any W_5943c = Some (Store SZ4 20 9 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_59440 : bv 32 := 0x5c061463.
Lemma F_59440 : fetch_word Asan.M.loaded_segments (0x59490 : word) = Some W_59440.
Proof. vm_refl. Qed.
Lemma D_59440 : decode_any W_59440 = Some (Branch BC_NE 12 0 1480, 4%Z).
Proof. vm_refl. Qed.

Definition W_59444 : bv 32 := 0xff0a0a93.
Lemma F_59444 : fetch_word Asan.M.loaded_segments (0x59494 : word) = Some W_59444.
Proof. vm_refl. Qed.
Lemma D_59444 : decode_any W_59444 = Some (OpImm ALU_ADD 21 20 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_59448 : bv 32 := 0x08f57513.
Lemma F_59448 : fetch_word Asan.M.loaded_segments (0x59498 : word) = Some W_59448.
Proof. vm_refl. Qed.
Lemma D_59448 : decode_any W_59448 = Some (OpImm ALU_AND 10 10 143, 4%Z).
Proof. vm_refl. Qed.

Definition W_5944c : bv 32 := 0x01013583.
Lemma F_5944c : fetch_word Asan.M.loaded_segments (0x5949c : word) = Some W_5944c.
Proof. vm_refl. Qed.
Lemma D_5944c : decode_any W_5944c = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59450 : bv 32 := 0x00b56533.
Lemma F_59450 : fetch_word Asan.M.loaded_segments (0x594a0 : word) = Some W_59450.
Proof. vm_refl. Qed.
Lemma D_59450 : decode_any W_59450 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59454 : bv 32 := 0x00aa80a3.
Lemma F_59454 : fetch_word Asan.M.loaded_segments (0x594a4 : word) = Some W_59454.
Proof. vm_refl. Qed.
Lemma D_59454 : decode_any W_59454 = Some (Store SZ1 21 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59458 : bv 32 := 0x080d0c63.
Lemma F_59458 : fetch_word Asan.M.loaded_segments (0x594a8 : word) = Some W_59458.
Proof. vm_refl. Qed.
Lemma D_59458 : decode_any W_59458 = Some (Branch BC_EQ 26 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5945c : bv 32 := 0x000d3503.
Lemma F_5945c : fetch_word Asan.M.loaded_segments (0x594ac : word) = Some W_5945c.
Proof. vm_refl. Qed.
Lemma D_5945c : decode_any W_5945c = Some (Load SZ8 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59460 : bv 32 := 0x00852c03.
Lemma F_59460 : fetch_word Asan.M.loaded_segments (0x594b0 : word) = Some W_59460.
Proof. vm_refl. Qed.
Lemma D_59460 : decode_any W_59460 = Some (Load SZ4 true 24 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59464 : bv 32 := 0x020c1c13.
Lemma F_59464 : fetch_word Asan.M.loaded_segments (0x594b4 : word) = Some W_59464.
Proof. vm_refl. Qed.
Lemma D_59464 : decode_any W_59464 = Some (ShiftImm ALU_SLL 24 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59468 : bv 32 := 0x08c0006f.
Lemma F_59468 : fetch_word Asan.M.loaded_segments (0x594b8 : word) = Some W_59468.
Proof. vm_refl. Qed.
Lemma D_59468 : decode_any W_59468 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_594f4 : bv 32 := 0x000bb503.
Lemma F_594f4 : fetch_word Asan.M.loaded_segments (0x59544 : word) = Some W_594f4.
Proof. vm_refl. Qed.
Lemma D_594f4 : decode_any W_594f4 = Some (Load SZ8 true 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_594f8 : bv 32 := 0x008bb583.
Lemma F_594f8 : fetch_word Asan.M.loaded_segments (0x59548 : word) = Some W_594f8.
Proof. vm_refl. Qed.
Lemma D_594f8 : decode_any W_594f8 = Some (Load SZ8 true 11 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_594fc : bv 32 := 0x1a1470ef.
Lemma F_594fc : fetch_word Asan.M.loaded_segments (0x5954c : word) = Some W_594fc.
Proof. vm_refl. Qed.
Lemma D_594fc : decode_any W_594fc = Some (Jal 1 293280, 4%Z).
Proof. vm_refl. Qed.

Definition W_59500 : bv 32 := 0x02051513.
Lemma F_59500 : fetch_word Asan.M.loaded_segments (0x59550 : word) = Some W_59500.
Proof. vm_refl. Qed.
Lemma D_59500 : decode_any W_59500 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59504 : bv 32 := 0x02055513.
Lemma F_59504 : fetch_word Asan.M.loaded_segments (0x59554 : word) = Some W_59504.
Proof. vm_refl. Qed.
Lemma D_59504 : decode_any W_59504 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59508 : bv 32 := 0x00ac6533.
Lemma F_59508 : fetch_word Asan.M.loaded_segments (0x59558 : word) = Some W_59508.
Proof. vm_refl. Qed.
Lemma D_59508 : decode_any W_59508 = Some (Op ALU_OR 10 24 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5950c : bv 32 := 0x00aab423.
Lemma F_5950c : fetch_word Asan.M.loaded_segments (0x5955c : word) = Some W_5950c.
Proof. vm_refl. Qed.
Lemma D_5950c : decode_any W_5950c = Some (Store SZ8 21 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59510 : bv 32 := 0x02040063.
Lemma F_59510 : fetch_word Asan.M.loaded_segments (0x59560 : word) = Some W_59510.
Proof. vm_refl. Qed.
Lemma D_59510 : decode_any W_59510 = Some (Branch BC_EQ 8 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59514 : bv 32 := 0x000fe517.
Lemma F_59514 : fetch_word Asan.M.loaded_segments (0x59564 : word) = Some W_59514.
Proof. vm_refl. Qed.
Lemma D_59514 : decode_any W_59514 = Some (Auipc 10 254, 4%Z).
Proof. vm_refl. Qed.

Definition W_59518 : bv 32 := 0x83453503.
Lemma F_59518 : fetch_word Asan.M.loaded_segments (0x59568 : word) = Some W_59518.
Proof. vm_refl. Qed.
Lemma D_59518 : decode_any W_59518 = Some (Load SZ8 true 10 10 2100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5951c : bv 32 := 0x00053503.
Lemma F_5951c : fetch_word Asan.M.loaded_segments (0x5956c : word) = Some W_5951c.
Proof. vm_refl. Qed.
Lemma D_5951c : decode_any W_5951c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59520 : bv 32 := 0x00395593.
Lemma F_59520 : fetch_word Asan.M.loaded_segments (0x59570 : word) = Some W_59520.
Proof. vm_refl. Qed.
Lemma D_59520 : decode_any W_59520 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_59524 : bv 32 := 0x00b50533.
Lemma F_59524 : fetch_word Asan.M.loaded_segments (0x59574 : word) = Some W_59524.
Proof. vm_refl. Qed.
Lemma D_59524 : decode_any W_59524 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59528 : bv 32 := 0x00054503.
Lemma F_59528 : fetch_word Asan.M.loaded_segments (0x59578 : word) = Some W_59528.
Proof. vm_refl. Qed.
Lemma D_59528 : decode_any W_59528 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5952c : bv 32 := 0x0c051063.
Lemma F_5952c : fetch_word Asan.M.loaded_segments (0x5957c : word) = Some W_5952c.
Proof. vm_refl. Qed.
Lemma D_5952c : decode_any W_5952c = Some (Branch BC_NE 10 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_59530 : bv 32 := 0x020b3503.
Lemma F_59530 : fetch_word Asan.M.loaded_segments (0x59580 : word) = Some W_59530.
Proof. vm_refl. Qed.
Lemma D_59530 : decode_any W_59530 = Some (Load SZ8 true 10 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59534 : bv 32 := 0x02a96c63.
Lemma F_59534 : fetch_word Asan.M.loaded_segments (0x59584 : word) = Some W_59534.
Proof. vm_refl. Qed.
Lemma D_59534 : decode_any W_59534 = Some (Branch BC_LTU 18 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_59538 : bv 32 := 0x00100593.
Lemma F_59538 : fetch_word Asan.M.loaded_segments (0x59588 : word) = Some W_59538.
Proof. vm_refl. Qed.
Lemma D_59538 : decode_any W_59538 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5953c : bv 32 := 0x02559593.
Lemma F_5953c : fetch_word Asan.M.loaded_segments (0x5958c : word) = Some W_5953c.
Proof. vm_refl. Qed.
Lemma D_5953c : decode_any W_5953c = Some (ShiftImm ALU_SLL 11 11 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_59540 : bv 32 := 0x00b505b3.
Lemma F_59540 : fetch_word Asan.M.loaded_segments (0x59590 : word) = Some W_59540.
Proof. vm_refl. Qed.
Lemma D_59540 : decode_any W_59540 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59544 : bv 32 := 0x02b97463.
Lemma F_59544 : fetch_word Asan.M.loaded_segments (0x59594 : word) = Some W_59544.
Proof. vm_refl. Qed.
Lemma D_59544 : decode_any W_59544 = Some (Branch BC_GEU 18 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5956c : bv 32 := 0x040b3503.
Lemma F_5956c : fetch_word Asan.M.loaded_segments (0x595bc : word) = Some W_5956c.
Proof. vm_refl. Qed.
Lemma D_5956c : decode_any W_5956c = Some (Load SZ8 true 10 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_59570 : bv 32 := 0xfff50593.
Lemma F_59570 : fetch_word Asan.M.loaded_segments (0x595c0 : word) = Some W_59570.
Proof. vm_refl. Qed.
Lemma D_59570 : decode_any W_59570 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_59574 : bv 32 := 0x0125f633.
Lemma F_59574 : fetch_word Asan.M.loaded_segments (0x595c4 : word) = Some W_59574.
Proof. vm_refl. Qed.
Lemma D_59574 : decode_any W_59574 = Some (Op ALU_AND 12 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_59578 : bv 32 := 0x52061663.
Lemma F_59578 : fetch_word Asan.M.loaded_segments (0x595c8 : word) = Some W_59578.
Proof. vm_refl. Qed.
Lemma D_59578 : decode_any W_59578 = Some (Branch BC_NE 12 0 1324, 4%Z).
Proof. vm_refl. Qed.

Definition W_5957c : bv 32 := 0x00b57633.
Lemma F_5957c : fetch_word Asan.M.loaded_segments (0x595cc : word) = Some W_5957c.
Proof. vm_refl. Qed.
Lemma D_5957c : decode_any W_5957c = Some (Op ALU_AND 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59580 : bv 32 := 0x54061663.
Lemma F_59580 : fetch_word Asan.M.loaded_segments (0x595d0 : word) = Some W_59580.
Proof. vm_refl. Qed.
Lemma D_59580 : decode_any W_59580 = Some (Branch BC_NE 12 0 1356, 4%Z).
Proof. vm_refl. Qed.

Definition W_59584 : bv 32 := 0x40a90633.
Lemma F_59584 : fetch_word Asan.M.loaded_segments (0x595d4 : word) = Some W_59584.
Proof. vm_refl. Qed.
Lemma D_59584 : decode_any W_59584 = Some (Op ALU_SUB 12 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_59588 : bv 32 := 0x01063603.
Lemma F_59588 : fetch_word Asan.M.loaded_segments (0x595d8 : word) = Some W_59588.
Proof. vm_refl. Qed.
Lemma D_59588 : decode_any W_59588 = Some (Load SZ8 true 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5958c : bv 32 := 0x00b605b3.
Lemma F_5958c : fetch_word Asan.M.loaded_segments (0x595dc : word) = Some W_5958c.
Proof. vm_refl. Qed.
Lemma D_5958c : decode_any W_5958c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59590 : bv 32 := 0x40a00433.
Lemma F_59590 : fetch_word Asan.M.loaded_segments (0x595e0 : word) = Some W_59590.
Proof. vm_refl. Qed.
Lemma D_59590 : decode_any W_59590 = Some (Op ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_59594 : bv 32 := 0x0085f433.
Lemma F_59594 : fetch_word Asan.M.loaded_segments (0x595e4 : word) = Some W_59594.
Proof. vm_refl. Qed.
Lemma D_59594 : decode_any W_59594 = Some (Op ALU_AND 8 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59598 : bv 32 := 0x0280006f.
Lemma F_59598 : fetch_word Asan.M.loaded_segments (0x595e8 : word) = Some W_59598.
Proof. vm_refl. Qed.
Lemma D_59598 : decode_any W_59598 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_595c0 : bv 32 := 0x007c8c93.
Lemma F_595c0 : fetch_word Asan.M.loaded_segments (0x59610 : word) = Some W_595c0.
Proof. vm_refl. Qed.
Lemma D_595c0 : decode_any W_595c0 = Some (OpImm ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_595c4 : bv 32 := 0xff8cfb13.
Lemma F_595c4 : fetch_word Asan.M.loaded_segments (0x59614 : word) = Some W_595c4.
Proof. vm_refl. Qed.
Lemma D_595c4 : decode_any W_595c4 = Some (OpImm ALU_AND 22 25 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_595c8 : bv 32 := 0x412a05b3.
Lemma F_595c8 : fetch_word Asan.M.loaded_segments (0x59618 : word) = Some W_595c8.
Proof. vm_refl. Qed.
Lemma D_595c8 : decode_any W_595c8 = Some (Op ALU_SUB 11 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_595cc : bv 32 := 0x0fa00613.
Lemma F_595cc : fetch_word Asan.M.loaded_segments (0x5961c : word) = Some W_595cc.
Proof. vm_refl. Qed.
Lemma D_595cc : decode_any W_595cc = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_595d0 : bv 32 := 0x00090513.
Lemma F_595d0 : fetch_word Asan.M.loaded_segments (0x59620 : word) = Some W_595d0.
Proof. vm_refl. Qed.
Lemma D_595d0 : decode_any W_595d0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_595d4 : bv 32 := 0x43c280ef.
Lemma F_595d4 : fetch_word Asan.M.loaded_segments (0x59624 : word) = Some W_595d4.
Proof. vm_refl. Qed.
Lemma D_595d4 : decode_any W_595d4 = Some (Jal 1 164924, 4%Z).
Proof. vm_refl. Qed.

Definition W_595d8 : bv 32 := 0x416905b3.
Lemma F_595d8 : fetch_word Asan.M.loaded_segments (0x59628 : word) = Some W_595d8.
Proof. vm_refl. Qed.
Lemma D_595d8 : decode_any W_595d8 = Some (Op ALU_SUB 11 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_595dc : bv 32 := 0x008585b3.
Lemma F_595dc : fetch_word Asan.M.loaded_segments (0x5962c : word) = Some W_595dc.
Proof. vm_refl. Qed.
Lemma D_595dc : decode_any W_595dc = Some (Op ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_595e0 : bv 32 := 0x0fa00613.
Lemma F_595e0 : fetch_word Asan.M.loaded_segments (0x59630 : word) = Some W_595e0.
Proof. vm_refl. Qed.
Lemma D_595e0 : decode_any W_595e0 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_595e4 : bv 32 := 0x000b0513.
Lemma F_595e4 : fetch_word Asan.M.loaded_segments (0x59634 : word) = Some W_595e4.
Proof. vm_refl. Qed.
Lemma D_595e4 : decode_any W_595e4 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_595e8 : bv 32 := 0x428280ef.
Lemma F_595e8 : fetch_word Asan.M.loaded_segments (0x59638 : word) = Some W_595e8.
Proof. vm_refl. Qed.
Lemma D_595e8 : decode_any W_595e8 = Some (Jal 1 164904, 4%Z).
Proof. vm_refl. Qed.

Definition W_595ec : bv 32 := 0xfff80537.
Lemma F_595ec : fetch_word Asan.M.loaded_segments (0x5963c : word) = Some W_595ec.
Proof. vm_refl. Qed.
Lemma D_595ec : decode_any W_595ec = Some (Lui 10 1048448, 4%Z).
Proof. vm_refl. Qed.

Definition W_595f0 : bv 32 := 0x01055513.
Lemma F_595f0 : fetch_word Asan.M.loaded_segments (0x59640 : word) = Some W_595f0.
Proof. vm_refl. Qed.
Lemma D_595f0 : decode_any W_595f0 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_595f4 : bv 32 := 0x00a4fb33.
Lemma F_595f4 : fetch_word Asan.M.loaded_segments (0x59644 : word) = Some W_595f4.
Proof. vm_refl. Qed.
Lemma D_595f4 : decode_any W_595f4 = Some (Op ALU_AND 22 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_595f8 : bv 32 := 0x000b0a63.
Lemma F_595f8 : fetch_word Asan.M.loaded_segments (0x59648 : word) = Some W_595f8.
Proof. vm_refl. Qed.
Lemma D_595f8 : decode_any W_595f8 = Some (Branch BC_EQ 22 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_595fc : bv 32 := 0x000a0513.
Lemma F_595fc : fetch_word Asan.M.loaded_segments (0x5964c : word) = Some W_595fc.
Proof. vm_refl. Qed.
Lemma D_595fc : decode_any W_595fc = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59600 : bv 32 := 0x000b0593.
Lemma F_59600 : fetch_word Asan.M.loaded_segments (0x59650 : word) = Some W_59600.
Proof. vm_refl. Qed.
Lemma D_59600 : decode_any W_59600 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59604 : bv 32 := 0x00000613.
Lemma F_59604 : fetch_word Asan.M.loaded_segments (0x59654 : word) = Some W_59604.
Proof. vm_refl. Qed.
Lemma D_59604 : decode_any W_59604 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59608 : bv 32 := 0x408280ef.
Lemma F_59608 : fetch_word Asan.M.loaded_segments (0x59658 : word) = Some W_59608.
Proof. vm_refl. Qed.
Lemma D_59608 : decode_any W_59608 = Some (Jal 1 164872, 4%Z).
Proof. vm_refl. Qed.

Definition W_5960c : bv 32 := 0x09648a63.
Lemma F_5960c : fetch_word Asan.M.loaded_segments (0x5965c : word) = Some W_5960c.
Proof. vm_refl. Qed.
Lemma D_5960c : decode_any W_5960c = Some (Branch BC_EQ 9 22 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_59610 : bv 32 := 0x3ec280ef.
Lemma F_59610 : fetch_word Asan.M.loaded_segments (0x59660 : word) = Some W_59610.
Proof. vm_refl. Qed.
Lemma D_59610 : decode_any W_59610 = Some (Jal 1 164844, 4%Z).
Proof. vm_refl. Qed.

Definition W_59614 : bv 32 := 0x08050663.
Lemma F_59614 : fetch_word Asan.M.loaded_segments (0x59664 : word) = Some W_59614.
Proof. vm_refl. Qed.
Lemma D_59614 : decode_any W_59614 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_59618 : bv 32 := 0x000fd517.
Lemma F_59618 : fetch_word Asan.M.loaded_segments (0x59668 : word) = Some W_59618.
Proof. vm_refl. Qed.
Lemma D_59618 : decode_any W_59618 = Some (Auipc 10 253, 4%Z).
Proof. vm_refl. Qed.

Definition W_5961c : bv 32 := 0x73053503.
Lemma F_5961c : fetch_word Asan.M.loaded_segments (0x5966c : word) = Some W_5961c.
Proof. vm_refl. Qed.
Lemma D_5961c : decode_any W_5961c = Some (Load SZ8 true 10 10 1840, 4%Z).
Proof. vm_refl. Qed.

Definition W_59620 : bv 32 := 0x00053503.
Lemma F_59620 : fetch_word Asan.M.loaded_segments (0x59670 : word) = Some W_59620.
Proof. vm_refl. Qed.
Lemma D_59620 : decode_any W_59620 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59624 : bv 32 := 0x016a0b33.
Lemma F_59624 : fetch_word Asan.M.loaded_segments (0x59674 : word) = Some W_59624.
Proof. vm_refl. Qed.
Lemma D_59624 : decode_any W_59624 = Some (Op ALU_ADD 22 20 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_59628 : bv 32 := 0xfff50593.
Lemma F_59628 : fetch_word Asan.M.loaded_segments (0x59678 : word) = Some W_59628.
Proof. vm_refl. Qed.
Lemma D_59628 : decode_any W_59628 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5962c : bv 32 := 0x00b53633.
Lemma F_5962c : fetch_word Asan.M.loaded_segments (0x5967c : word) = Some W_5962c.
Proof. vm_refl. Qed.
Lemma D_5962c : decode_any W_5962c = Some (Op ALU_SLTU 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59630 : bv 32 := 0xfff60613.
Lemma F_59630 : fetch_word Asan.M.loaded_segments (0x59680 : word) = Some W_59630.
Proof. vm_refl. Qed.
Lemma D_59630 : decode_any W_59630 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_59634 : bv 32 := 0x00b67633.
Lemma F_59634 : fetch_word Asan.M.loaded_segments (0x59684 : word) = Some W_59634.
Proof. vm_refl. Qed.
Lemma D_59634 : decode_any W_59634 = Some (Op ALU_AND 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59638 : bv 32 := 0x05667263.
Lemma F_59638 : fetch_word Asan.M.loaded_segments (0x59688 : word) = Some W_59638.
Proof. vm_refl. Qed.
Lemma D_59638 : decode_any W_59638 = Some (Branch BC_GEU 12 22 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5963c : bv 32 := 0x000fd617.
Lemma F_5963c : fetch_word Asan.M.loaded_segments (0x5968c : word) = Some W_5963c.
Proof. vm_refl. Qed.
Lemma D_5963c : decode_any W_5963c = Some (Auipc 12 253, 4%Z).
Proof. vm_refl. Qed.

Definition W_59640 : bv 32 := 0x71463603.
Lemma F_59640 : fetch_word Asan.M.loaded_segments (0x59690 : word) = Some W_59640.
Proof. vm_refl. Qed.
Lemma D_59640 : decode_any W_59640 = Some (Load SZ8 true 12 12 1812, 4%Z).
Proof. vm_refl. Qed.

Definition W_59644 : bv 32 := 0x000fd697.
Lemma F_59644 : fetch_word Asan.M.loaded_segments (0x59694 : word) = Some W_59644.
Proof. vm_refl. Qed.
Lemma D_59644 : decode_any W_59644 = Some (Auipc 13 253, 4%Z).
Proof. vm_refl. Qed.

Definition W_59648 : bv 32 := 0x7146b683.
Lemma F_59648 : fetch_word Asan.M.loaded_segments (0x59698 : word) = Some W_59648.
Proof. vm_refl. Qed.
Lemma D_59648 : decode_any W_59648 = Some (Load SZ8 true 13 13 1812, 4%Z).
Proof. vm_refl. Qed.

Definition W_5964c : bv 32 := 0x00063783.
Lemma F_5964c : fetch_word Asan.M.loaded_segments (0x5969c : word) = Some W_5964c.
Proof. vm_refl. Qed.
Lemma D_5964c : decode_any W_5964c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59650 : bv 32 := 0x0006b603.
Lemma F_59650 : fetch_word Asan.M.loaded_segments (0x596a0 : word) = Some W_59650.
Proof. vm_refl. Qed.
Lemma D_59650 : decode_any W_59650 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59654 : bv 32 := 0xfff78713.
Lemma F_59654 : fetch_word Asan.M.loaded_segments (0x596a4 : word) = Some W_59654.
Proof. vm_refl. Qed.
Lemma D_59654 : decode_any W_59654 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_59658 : bv 32 := 0x01677463.
Lemma F_59658 : fetch_word Asan.M.loaded_segments (0x596a8 : word) = Some W_59658.
Proof. vm_refl. Qed.
Lemma D_59658 : decode_any W_59658 = Some (Branch BC_GEU 14 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59660 : bv 32 := 0x000fd697.
Lemma F_59660 : fetch_word Asan.M.loaded_segments (0x596b0 : word) = Some W_59660.
Proof. vm_refl. Qed.
Lemma D_59660 : decode_any W_59660 = Some (Auipc 13 253, 4%Z).
Proof. vm_refl. Qed.

Definition W_59664 : bv 32 := 0x7006b683.
Lemma F_59664 : fetch_word Asan.M.loaded_segments (0x596b4 : word) = Some W_59664.
Proof. vm_refl. Qed.
Lemma D_59664 : decode_any W_59664 = Some (Load SZ8 true 13 13 1792, 4%Z).
Proof. vm_refl. Qed.

Definition W_59668 : bv 32 := 0x0006b883.
Lemma F_59668 : fetch_word Asan.M.loaded_segments (0x596b8 : word) = Some W_59668.
Proof. vm_refl. Qed.
Lemma D_59668 : decode_any W_59668 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5966c : bv 32 := 0x0038d693.
Lemma F_5966c : fetch_word Asan.M.loaded_segments (0x596bc : word) = Some W_5966c.
Proof. vm_refl. Qed.
Lemma D_5966c : decode_any W_5966c = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_59670 : bv 32 := 0x00a68833.
Lemma F_59670 : fetch_word Asan.M.loaded_segments (0x596c0 : word) = Some W_59670.
Proof. vm_refl. Qed.
Lemma D_59670 : decode_any W_59670 = Some (Op ALU_ADD 16 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_59674 : bv 32 := 0x2568ea63.
Lemma F_59674 : fetch_word Asan.M.loaded_segments (0x596c4 : word) = Some W_59674.
Proof. vm_refl. Qed.
Lemma D_59674 : decode_any W_59674 = Some (Branch BC_LTU 17 22 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_59678 : bv 32 := 0x25687863.
Lemma F_59678 : fetch_word Asan.M.loaded_segments (0x596c8 : word) = Some W_59678.
Proof. vm_refl. Qed.
Lemma D_59678 : decode_any W_59678 = Some (Branch BC_GEU 16 22 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_5967c : bv 32 := 0x000fd597.
Lemma F_5967c : fetch_word Asan.M.loaded_segments (0x596cc : word) = Some W_5967c.
Proof. vm_refl. Qed.
Lemma D_5967c : decode_any W_5967c = Some (Auipc 11 253, 4%Z).
Proof. vm_refl. Qed.

Definition W_59680 : bv 32 := 0x6c45b583.
Lemma F_59680 : fetch_word Asan.M.loaded_segments (0x596d0 : word) = Some W_59680.
Proof. vm_refl. Qed.
Lemma D_59680 : decode_any W_59680 = Some (Load SZ8 true 11 11 1732, 4%Z).
Proof. vm_refl. Qed.

Definition W_59684 : bv 32 := 0x0555c583.
Lemma F_59684 : fetch_word Asan.M.loaded_segments (0x596d4 : word) = Some W_59684.
Proof. vm_refl. Qed.
Lemma D_59684 : decode_any W_59684 = Some (Load SZ1 false 11 11 85, 4%Z).
Proof. vm_refl. Qed.

Definition W_59688 : bv 32 := 0x003b5613.
Lemma F_59688 : fetch_word Asan.M.loaded_segments (0x596d8 : word) = Some W_59688.
Proof. vm_refl. Qed.
Lemma D_59688 : decode_any W_59688 = Some (ShiftImm ALU_SRL 12 22 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5968c : bv 32 := 0x00c50533.
Lemma F_5968c : fetch_word Asan.M.loaded_segments (0x596dc : word) = Some W_5968c.
Proof. vm_refl. Qed.
Lemma D_5968c : decode_any W_5968c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59690 : bv 32 := 0x40b005bb.
Lemma F_59690 : fetch_word Asan.M.loaded_segments (0x596e0 : word) = Some W_59690.
Proof. vm_refl. Qed.
Lemma D_59690 : decode_any W_59690 = Some (Op32 ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59694 : bv 32 := 0x00b4f5b3.
Lemma F_59694 : fetch_word Asan.M.loaded_segments (0x596e4 : word) = Some W_59694.
Proof. vm_refl. Qed.
Lemma D_59694 : decode_any W_59694 = Some (Op ALU_AND 11 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59698 : bv 32 := 0x0075f593.
Lemma F_59698 : fetch_word Asan.M.loaded_segments (0x596e8 : word) = Some W_59698.
Proof. vm_refl. Qed.
Lemma D_59698 : decode_any W_59698 = Some (OpImm ALU_AND 11 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5969c : bv 32 := 0x00b50023.
Lemma F_5969c : fetch_word Asan.M.loaded_segments (0x596ec : word) = Some W_5969c.
Proof. vm_refl. Qed.
Lemma D_5969c : decode_any W_5969c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_596a0 : bv 32 := 0x2e8300ef.
Lemma F_596a0 : fetch_word Asan.M.loaded_segments (0x596f0 : word) = Some W_596a0.
Proof. vm_refl. Qed.
Lemma D_596a0 : decode_any W_596a0 = Some (Jal 1 197352, 4%Z).
Proof. vm_refl. Qed.

Definition W_596a4 : bv 32 := 0x01053583.
Lemma F_596a4 : fetch_word Asan.M.loaded_segments (0x596f4 : word) = Some W_596a4.
Proof. vm_refl. Qed.
Lemma D_596a4 : decode_any W_596a4 = Some (Load SZ8 true 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_596a8 : bv 32 := 0x00053603.
Lemma F_596a8 : fetch_word Asan.M.loaded_segments (0x596f8 : word) = Some W_596a8.
Proof. vm_refl. Qed.
Lemma D_596a8 : decode_any W_596a8 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_596ac : bv 32 := 0x00853683.
Lemma F_596ac : fetch_word Asan.M.loaded_segments (0x596fc : word) = Some W_596ac.
Proof. vm_refl. Qed.
Lemma D_596ac : decode_any W_596ac = Some (Load SZ8 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_596b0 : bv 32 := 0x40998733.
Lemma F_596b0 : fetch_word Asan.M.loaded_segments (0x59700 : word) = Some W_596b0.
Proof. vm_refl. Qed.
Lemma D_596b0 : decode_any W_596b0 = Some (Op ALU_SUB 14 19 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_596b4 : bv 32 := 0x00b705b3.
Lemma F_596b4 : fetch_word Asan.M.loaded_segments (0x59704 : word) = Some W_596b4.
Proof. vm_refl. Qed.
Lemma D_596b4 : decode_any W_596b4 = Some (Op ALU_ADD 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_596b8 : bv 32 := 0x00010737.
Lemma F_596b8 : fetch_word Asan.M.loaded_segments (0x59708 : word) = Some W_596b8.
Proof. vm_refl. Qed.
Lemma D_596b8 : decode_any W_596b8 = Some (Lui 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_596bc : bv 32 := 0x0017071b.
Lemma F_596bc : fetch_word Asan.M.loaded_segments (0x5970c : word) = Some W_596bc.
Proof. vm_refl. Qed.
Lemma D_596bc : decode_any W_596bc = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_596c0 : bv 32 := 0x00160613.
Lemma F_596c0 : fetch_word Asan.M.loaded_segments (0x59710 : word) = Some W_596c0.
Proof. vm_refl. Qed.
Lemma D_596c0 : decode_any W_596c0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_596c4 : bv 32 := 0x009686b3.
Lemma F_596c4 : fetch_word Asan.M.loaded_segments (0x59714 : word) = Some W_596c4.
Proof. vm_refl. Qed.
Lemma D_596c4 : decode_any W_596c4 = Some (Op ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_596c8 : bv 32 := 0x00c53023.
Lemma F_596c8 : fetch_word Asan.M.loaded_segments (0x59718 : word) = Some W_596c8.
Proof. vm_refl. Qed.
Lemma D_596c8 : decode_any W_596c8 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_596cc : bv 32 := 0x00d53423.
Lemma F_596cc : fetch_word Asan.M.loaded_segments (0x5971c : word) = Some W_596cc.
Proof. vm_refl. Qed.
Lemma D_596cc : decode_any W_596cc = Some (Store SZ8 10 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_596d0 : bv 32 := 0x00b53823.
Lemma F_596d0 : fetch_word Asan.M.loaded_segments (0x59720 : word) = Some W_596d0.
Proof. vm_refl. Qed.
Lemma D_596d0 : decode_any W_596d0 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_596d4 : bv 32 := 0x00e9ee63.
Lemma F_596d4 : fetch_word Asan.M.loaded_segments (0x59724 : word) = Some W_596d4.
Proof. vm_refl. Qed.
Lemma D_596d4 : decode_any W_596d4 = Some (Branch BC_LTU 19 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_596d8 : bv 32 := 0x06853583.
Lemma F_596d8 : fetch_word Asan.M.loaded_segments (0x59728 : word) = Some W_596d8.
Proof. vm_refl. Qed.
Lemma D_596d8 : decode_any W_596d8 = Some (Load SZ8 true 11 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_596dc : bv 32 := 0x00158593.
Lemma F_596dc : fetch_word Asan.M.loaded_segments (0x5972c : word) = Some W_596dc.
Proof. vm_refl. Qed.
Lemma D_596dc : decode_any W_596dc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_596e0 : bv 32 := 0x06b53423.
Lemma F_596e0 : fetch_word Asan.M.loaded_segments (0x59730 : word) = Some W_596e0.
Proof. vm_refl. Qed.
Lemma D_596e0 : decode_any W_596e0 = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_596e4 : bv 32 := 0x00813503.
Lemma F_596e4 : fetch_word Asan.M.loaded_segments (0x59734 : word) = Some W_596e4.
Proof. vm_refl. Qed.
Lemma D_596e4 : decode_any W_596e4 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_596e8 : bv 32 := 0x10051c63.
Lemma F_596e8 : fetch_word Asan.M.loaded_segments (0x59738 : word) = Some W_596e8.
Proof. vm_refl. Qed.
Lemma D_596e8 : decode_any W_596e8 = Some (Branch BC_NE 10 0 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_596f0 : bv 32 := 0x20000593.
Lemma F_596f0 : fetch_word Asan.M.loaded_segments (0x59740 : word) = Some W_596f0.
Proof. vm_refl. Qed.
Lemma D_596f0 : decode_any W_596f0 = Some (OpImm ALU_ADD 11 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_596f4 : bv 32 := 0x07050513.
Lemma F_596f4 : fetch_word Asan.M.loaded_segments (0x59744 : word) = Some W_596f4.
Proof. vm_refl. Qed.
Lemma D_596f4 : decode_any W_596f4 = Some (OpImm ALU_ADD 10 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_596f8 : bv 32 := 0x0135e863.
Lemma F_596f8 : fetch_word Asan.M.loaded_segments (0x59748 : word) = Some W_596f8.
Proof. vm_refl. Qed.
Lemma D_596f8 : decode_any W_596f8 = Some (Branch BC_LTU 11 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_596fc : bv 32 := 0x01f98593.
Lemma F_596fc : fetch_word Asan.M.loaded_segments (0x5974c : word) = Some W_596fc.
Proof. vm_refl. Qed.
Lemma D_596fc : decode_any W_596fc = Some (OpImm ALU_ADD 11 19 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_59700 : bv 32 := 0x0055d593.
Lemma F_59700 : fetch_word Asan.M.loaded_segments (0x59750 : word) = Some W_59700.
Proof. vm_refl. Qed.
Lemma D_59700 : decode_any W_59700 = Some (ShiftImm ALU_SRL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_59704 : bv 32 := 0x0e00006f.
Lemma F_59704 : fetch_word Asan.M.loaded_segments (0x59754 : word) = Some W_59704.
Proof. vm_refl. Qed.
Lemma D_59704 : decode_any W_59704 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_59708 : bv 32 := 0x0019d593.
Lemma F_59708 : fetch_word Asan.M.loaded_segments (0x59758 : word) = Some W_59708.
Proof. vm_refl. Qed.
Lemma D_59708 : decode_any W_59708 = Some (ShiftImm ALU_SRL 11 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5970c : bv 32 := 0x55555637.
Lemma F_5970c : fetch_word Asan.M.loaded_segments (0x5975c : word) = Some W_5970c.
Proof. vm_refl. Qed.
Lemma D_5970c : decode_any W_5970c = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_59710 : bv 32 := 0x333336b7.
Lemma F_59710 : fetch_word Asan.M.loaded_segments (0x59760 : word) = Some W_59710.
Proof. vm_refl. Qed.
Lemma D_59710 : decode_any W_59710 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_59714 : bv 32 := 0x0f0f1737.
Lemma F_59714 : fetch_word Asan.M.loaded_segments (0x59764 : word) = Some W_59714.
Proof. vm_refl. Qed.
Lemma D_59714 : decode_any W_59714 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_59718 : bv 32 := 0x010107b7.
Lemma F_59718 : fetch_word Asan.M.loaded_segments (0x59768 : word) = Some W_59718.
Proof. vm_refl. Qed.
Lemma D_59718 : decode_any W_59718 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5971c : bv 32 := 0x00b9e5b3.
Lemma F_5971c : fetch_word Asan.M.loaded_segments (0x5976c : word) = Some W_5971c.
Proof. vm_refl. Qed.
Lemma D_5971c : decode_any W_5971c = Some (Op ALU_OR 11 19 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59720 : bv 32 := 0x5556061b.
Lemma F_59720 : fetch_word Asan.M.loaded_segments (0x59770 : word) = Some W_59720.
Proof. vm_refl. Qed.
Lemma D_59720 : decode_any W_59720 = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_59724 : bv 32 := 0x3336869b.
Lemma F_59724 : fetch_word Asan.M.loaded_segments (0x59774 : word) = Some W_59724.
Proof. vm_refl. Qed.
Lemma D_59724 : decode_any W_59724 = Some (OpImm32 13 13 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_59728 : bv 32 := 0xf0f7071b.
Lemma F_59728 : fetch_word Asan.M.loaded_segments (0x59778 : word) = Some W_59728.
Proof. vm_refl. Qed.
Lemma D_59728 : decode_any W_59728 = Some (OpImm32 14 14 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_5972c : bv 32 := 0x1017879b.
Lemma F_5972c : fetch_word Asan.M.loaded_segments (0x5977c : word) = Some W_5972c.
Proof. vm_refl. Qed.
Lemma D_5972c : decode_any W_5972c = Some (OpImm32 15 15 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_59730 : bv 32 := 0x0025d813.
Lemma F_59730 : fetch_word Asan.M.loaded_segments (0x59780 : word) = Some W_59730.
Proof. vm_refl. Qed.
Lemma D_59730 : decode_any W_59730 = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_59734 : bv 32 := 0x0105e5b3.
Lemma F_59734 : fetch_word Asan.M.loaded_segments (0x59784 : word) = Some W_59734.
Proof. vm_refl. Qed.
Lemma D_59734 : decode_any W_59734 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59738 : bv 32 := 0x02061813.
Lemma F_59738 : fetch_word Asan.M.loaded_segments (0x59788 : word) = Some W_59738.
Proof. vm_refl. Qed.
Lemma D_59738 : decode_any W_59738 = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5973c : bv 32 := 0x01060633.
Lemma F_5973c : fetch_word Asan.M.loaded_segments (0x5978c : word) = Some W_5973c.
Proof. vm_refl. Qed.
Lemma D_5973c : decode_any W_5973c = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59740 : bv 32 := 0x02069813.
Lemma F_59740 : fetch_word Asan.M.loaded_segments (0x59790 : word) = Some W_59740.
Proof. vm_refl. Qed.
Lemma D_59740 : decode_any W_59740 = Some (ShiftImm ALU_SLL 16 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59744 : bv 32 := 0x010686b3.
Lemma F_59744 : fetch_word Asan.M.loaded_segments (0x59794 : word) = Some W_59744.
Proof. vm_refl. Qed.
Lemma D_59744 : decode_any W_59744 = Some (Op ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59748 : bv 32 := 0x02071813.
Lemma F_59748 : fetch_word Asan.M.loaded_segments (0x59798 : word) = Some W_59748.
Proof. vm_refl. Qed.
Lemma D_59748 : decode_any W_59748 = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5974c : bv 32 := 0x01070733.
Lemma F_5974c : fetch_word Asan.M.loaded_segments (0x5979c : word) = Some W_5974c.
Proof. vm_refl. Qed.
Lemma D_5974c : decode_any W_5974c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59750 : bv 32 := 0x02079813.
Lemma F_59750 : fetch_word Asan.M.loaded_segments (0x597a0 : word) = Some W_59750.
Proof. vm_refl. Qed.
Lemma D_59750 : decode_any W_59750 = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59754 : bv 32 := 0x010787b3.
Lemma F_59754 : fetch_word Asan.M.loaded_segments (0x597a4 : word) = Some W_59754.
Proof. vm_refl. Qed.
Lemma D_59754 : decode_any W_59754 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59758 : bv 32 := 0x0045d813.
Lemma F_59758 : fetch_word Asan.M.loaded_segments (0x597a8 : word) = Some W_59758.
Proof. vm_refl. Qed.
Lemma D_59758 : decode_any W_59758 = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5975c : bv 32 := 0x0105e5b3.
Lemma F_5975c : fetch_word Asan.M.loaded_segments (0x597ac : word) = Some W_5975c.
Proof. vm_refl. Qed.
Lemma D_5975c : decode_any W_5975c = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59760 : bv 32 := 0x0085d813.
Lemma F_59760 : fetch_word Asan.M.loaded_segments (0x597b0 : word) = Some W_59760.
Proof. vm_refl. Qed.
Lemma D_59760 : decode_any W_59760 = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59764 : bv 32 := 0x0105e5b3.
Lemma F_59764 : fetch_word Asan.M.loaded_segments (0x597b4 : word) = Some W_59764.
Proof. vm_refl. Qed.
Lemma D_59764 : decode_any W_59764 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59768 : bv 32 := 0x0105d813.
Lemma F_59768 : fetch_word Asan.M.loaded_segments (0x597b8 : word) = Some W_59768.
Proof. vm_refl. Qed.
Lemma D_59768 : decode_any W_59768 = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5976c : bv 32 := 0x0105e5b3.
Lemma F_5976c : fetch_word Asan.M.loaded_segments (0x597bc : word) = Some W_5976c.
Proof. vm_refl. Qed.
Lemma D_5976c : decode_any W_5976c = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59770 : bv 32 := 0x0205d813.
Lemma F_59770 : fetch_word Asan.M.loaded_segments (0x597c0 : word) = Some W_59770.
Proof. vm_refl. Qed.
Lemma D_59770 : decode_any W_59770 = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59774 : bv 32 := 0x0105e5b3.
Lemma F_59774 : fetch_word Asan.M.loaded_segments (0x597c4 : word) = Some W_59774.
Proof. vm_refl. Qed.
Lemma D_59774 : decode_any W_59774 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59778 : bv 32 := 0xfff5c593.
Lemma F_59778 : fetch_word Asan.M.loaded_segments (0x597c8 : word) = Some W_59778.
Proof. vm_refl. Qed.
Lemma D_59778 : decode_any W_59778 = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5977c : bv 32 := 0x0015d813.
Lemma F_5977c : fetch_word Asan.M.loaded_segments (0x597cc : word) = Some W_5977c.
Proof. vm_refl. Qed.
Lemma D_5977c : decode_any W_5977c = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59780 : bv 32 := 0x00c87633.
Lemma F_59780 : fetch_word Asan.M.loaded_segments (0x597d0 : word) = Some W_59780.
Proof. vm_refl. Qed.
Lemma D_59780 : decode_any W_59780 = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59784 : bv 32 := 0x40c585b3.
Lemma F_59784 : fetch_word Asan.M.loaded_segments (0x597d4 : word) = Some W_59784.
Proof. vm_refl. Qed.
Lemma D_59784 : decode_any W_59784 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59788 : bv 32 := 0x00d5f633.
Lemma F_59788 : fetch_word Asan.M.loaded_segments (0x597d8 : word) = Some W_59788.
Proof. vm_refl. Qed.
Lemma D_59788 : decode_any W_59788 = Some (Op ALU_AND 12 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5978c : bv 32 := 0x0025d593.
Lemma F_5978c : fetch_word Asan.M.loaded_segments (0x597dc : word) = Some W_5978c.
Proof. vm_refl. Qed.
Lemma D_5978c : decode_any W_5978c = Some (ShiftImm ALU_SRL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_59790 : bv 32 := 0x00d5f5b3.
Lemma F_59790 : fetch_word Asan.M.loaded_segments (0x597e0 : word) = Some W_59790.
Proof. vm_refl. Qed.
Lemma D_59790 : decode_any W_59790 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_59794 : bv 32 := 0x00b605b3.
Lemma F_59794 : fetch_word Asan.M.loaded_segments (0x597e4 : word) = Some W_59794.
Proof. vm_refl. Qed.
Lemma D_59794 : decode_any W_59794 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_59798 : bv 32 := 0x0045d613.
Lemma F_59798 : fetch_word Asan.M.loaded_segments (0x597e8 : word) = Some W_59798.
Proof. vm_refl. Qed.
Lemma D_59798 : decode_any W_59798 = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5979c : bv 32 := 0x00c585b3.
Lemma F_5979c : fetch_word Asan.M.loaded_segments (0x597ec : word) = Some W_5979c.
Proof. vm_refl. Qed.
Lemma D_5979c : decode_any W_5979c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_597a0 : bv 32 := 0x03e00613.
Lemma F_597a0 : fetch_word Asan.M.loaded_segments (0x597f0 : word) = Some W_597a0.
Proof. vm_refl. Qed.
Lemma D_597a0 : decode_any W_597a0 = Some (OpImm ALU_ADD 12 0 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_597a4 : bv 32 := 0x00e5f5b3.
Lemma F_597a4 : fetch_word Asan.M.loaded_segments (0x597f4 : word) = Some W_597a4.
Proof. vm_refl. Qed.
Lemma D_597a4 : decode_any W_597a4 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_597a8 : bv 32 := 0xfff00693.
Lemma F_597a8 : fetch_word Asan.M.loaded_segments (0x597f8 : word) = Some W_597a8.
Proof. vm_refl. Qed.
Lemma D_597a8 : decode_any W_597a8 = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_597ac : bv 32 := 0x02f585b3.
Lemma F_597ac : fetch_word Asan.M.loaded_segments (0x597fc : word) = Some W_597ac.
Proof. vm_refl. Qed.
Lemma D_597ac : decode_any W_597ac = Some (Mul M_MUL 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_597b0 : bv 32 := 0x0385d593.
Lemma F_597b0 : fetch_word Asan.M.loaded_segments (0x59800 : word) = Some W_597b0.
Proof. vm_refl. Qed.
Lemma D_597b0 : decode_any W_597b0 = Some (ShiftImm ALU_SRL 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_597b4 : bv 32 := 0x40b6063b.
Lemma F_597b4 : fetch_word Asan.M.loaded_segments (0x59804 : word) = Some W_597b4.
Proof. vm_refl. Qed.
Lemma D_597b4 : decode_any W_597b4 = Some (Op32 ALU_SUB 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_597b8 : bv 32 := 0x00159593.
Lemma F_597b8 : fetch_word Asan.M.loaded_segments (0x59808 : word) = Some W_597b8.
Proof. vm_refl. Qed.
Lemma D_597b8 : decode_any W_597b8 = Some (ShiftImm ALU_SLL 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_597bc : bv 32 := 0x00c9d733.
Lemma F_597bc : fetch_word Asan.M.loaded_segments (0x5980c : word) = Some W_597bc.
Proof. vm_refl. Qed.
Lemma D_597bc : decode_any W_597bc = Some (Op ALU_SRL 14 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_597c0 : bv 32 := 0x00c6963b.
Lemma F_597c0 : fetch_word Asan.M.loaded_segments (0x59810 : word) = Some W_597c0.
Proof. vm_refl. Qed.
Lemma D_597c0 : decode_any W_597c0 = Some (Op32 ALU_SLL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_597c4 : bv 32 := 0x07e5c593.
Lemma F_597c4 : fetch_word Asan.M.loaded_segments (0x59814 : word) = Some W_597c4.
Proof. vm_refl. Qed.
Lemma D_597c4 : decode_any W_597c4 = Some (OpImm ALU_XOR 11 11 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_597c8 : bv 32 := 0x00177713.
Lemma F_597c8 : fetch_word Asan.M.loaded_segments (0x59818 : word) = Some W_597c8.
Proof. vm_refl. Qed.
Lemma D_597c8 : decode_any W_597c8 = Some (OpImm ALU_AND 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_597cc : bv 32 := 0xfff64613.
Lemma F_597cc : fetch_word Asan.M.loaded_segments (0x5981c : word) = Some W_597cc.
Proof. vm_refl. Qed.
Lemma D_597cc : decode_any W_597cc = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_597d0 : bv 32 := 0x00c9f633.
Lemma F_597d0 : fetch_word Asan.M.loaded_segments (0x59820 : word) = Some W_597d0.
Proof. vm_refl. Qed.
Lemma D_597d0 : decode_any W_597d0 = Some (Op ALU_AND 12 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_597d4 : bv 32 := 0x00e5e5b3.
Lemma F_597d4 : fetch_word Asan.M.loaded_segments (0x59824 : word) = Some W_597d4.
Proof. vm_refl. Qed.
Lemma D_597d4 : decode_any W_597d4 = Some (Op ALU_OR 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_597d8 : bv 32 := 0x00c03633.
Lemma F_597d8 : fetch_word Asan.M.loaded_segments (0x59828 : word) = Some W_597d8.
Proof. vm_refl. Qed.
Lemma D_597d8 : decode_any W_597d8 = Some (Op ALU_SLTU 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_597dc : bv 32 := 0x00c585b3.
Lemma F_597dc : fetch_word Asan.M.loaded_segments (0x5982c : word) = Some W_597dc.
Proof. vm_refl. Qed.
Lemma D_597dc : decode_any W_597dc = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_597e0 : bv 32 := 0xffe58593.
Lemma F_597e0 : fetch_word Asan.M.loaded_segments (0x59830 : word) = Some W_597e0.
Proof. vm_refl. Qed.
Lemma D_597e0 : decode_any W_597e0 = Some (OpImm ALU_ADD 11 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_597e4 : bv 32 := 0x00359593.
Lemma F_597e4 : fetch_word Asan.M.loaded_segments (0x59834 : word) = Some W_597e4.
Proof. vm_refl. Qed.
Lemma D_597e4 : decode_any W_597e4 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_597e8 : bv 32 := 0x00b50533.
Lemma F_597e8 : fetch_word Asan.M.loaded_segments (0x59838 : word) = Some W_597e8.
Proof. vm_refl. Qed.
Lemma D_597e8 : decode_any W_597e8 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_597ec : bv 32 := 0x00053583.
Lemma F_597ec : fetch_word Asan.M.loaded_segments (0x5983c : word) = Some W_597ec.
Proof. vm_refl. Qed.
Lemma D_597ec : decode_any W_597ec = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_597f0 : bv 32 := 0x00158593.
Lemma F_597f0 : fetch_word Asan.M.loaded_segments (0x59840 : word) = Some W_597f0.
Proof. vm_refl. Qed.
Lemma D_597f0 : decode_any W_597f0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_597f4 : bv 32 := 0x00b53023.
Lemma F_597f4 : fetch_word Asan.M.loaded_segments (0x59844 : word) = Some W_597f4.
Proof. vm_refl. Qed.
Lemma D_597f4 : decode_any W_597f4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_597f8 : bv 32 := 0x00813503.
Lemma F_597f8 : fetch_word Asan.M.loaded_segments (0x59848 : word) = Some W_597f8.
Proof. vm_refl. Qed.
Lemma D_597f8 : decode_any W_597f8 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_597fc : bv 32 := 0x02050c63.
Lemma F_597fc : fetch_word Asan.M.loaded_segments (0x5984c : word) = Some W_597fc.
Proof. vm_refl. Qed.
Lemma D_597fc : decode_any W_597fc = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_59800 : bv 32 := 0x000fd517.
Lemma F_59800 : fetch_word Asan.M.loaded_segments (0x59850 : word) = Some W_59800.
Proof. vm_refl. Qed.
Lemma D_59800 : decode_any W_59800 = Some (Auipc 10 253, 4%Z).
Proof. vm_refl. Qed.

Definition W_59804 : bv 32 := 0x54053503.
Lemma F_59804 : fetch_word Asan.M.loaded_segments (0x59854 : word) = Some W_59804.
Proof. vm_refl. Qed.
Lemma D_59804 : decode_any W_59804 = Some (Load SZ8 true 10 10 1344, 4%Z).
Proof. vm_refl. Qed.

Definition W_59808 : bv 32 := 0x02c52583.
Lemma F_59808 : fetch_word Asan.M.loaded_segments (0x59858 : word) = Some W_59808.
Proof. vm_refl. Qed.
Lemma D_59808 : decode_any W_59808 = Some (Load SZ4 true 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5980c : bv 32 := 0x02058463.
Lemma F_5980c : fetch_word Asan.M.loaded_segments (0x5985c : word) = Some W_5980c.
Proof. vm_refl. Qed.
Lemma D_5980c : decode_any W_5980c = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_59810 : bv 32 := 0x00048613.
Lemma F_59810 : fetch_word Asan.M.loaded_segments (0x59860 : word) = Some W_59810.
Proof. vm_refl. Qed.
Lemma D_59810 : decode_any W_59810 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59814 : bv 32 := 0x00b4e463.
Lemma F_59814 : fetch_word Asan.M.loaded_segments (0x59864 : word) = Some W_59814.
Proof. vm_refl. Qed.
Lemma D_59814 : decode_any W_59814 = Some (Branch BC_LTU 9 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59818 : bv 32 := 0x00058613.
Lemma F_59818 : fetch_word Asan.M.loaded_segments (0x59868 : word) = Some W_59818.
Proof. vm_refl. Qed.
Lemma D_59818 : decode_any W_59818 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5981c : bv 32 := 0x000fd597.
Lemma F_5981c : fetch_word Asan.M.loaded_segments (0x5986c : word) = Some W_5981c.
Proof. vm_refl. Qed.
Lemma D_5981c : decode_any W_5981c = Some (Auipc 11 253, 4%Z).
Proof. vm_refl. Qed.

Definition W_59820 : bv 32 := 0x54c5b583.
Lemma F_59820 : fetch_word Asan.M.loaded_segments (0x59870 : word) = Some W_59820.
Proof. vm_refl. Qed.
Lemma D_59820 : decode_any W_59820 = Some (Load SZ8 true 11 11 1356, 4%Z).
Proof. vm_refl. Qed.

Definition W_59824 : bv 32 := 0x0005b683.
Lemma F_59824 : fetch_word Asan.M.loaded_segments (0x59874 : word) = Some W_59824.
Proof. vm_refl. Qed.
Lemma D_59824 : decode_any W_59824 = Some (Load SZ8 true 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59828 : bv 32 := 0x03452583.
Lemma F_59828 : fetch_word Asan.M.loaded_segments (0x59878 : word) = Some W_59828.
Proof. vm_refl. Qed.
Lemma D_59828 : decode_any W_59828 = Some (Load SZ4 true 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5982c : bv 32 := 0x000a0513.
Lemma F_5982c : fetch_word Asan.M.loaded_segments (0x5987c : word) = Some W_5982c.
Proof. vm_refl. Qed.
Lemma D_5982c : decode_any W_5982c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59830 : bv 32 := 0x000680e7.
Lemma F_59830 : fetch_word Asan.M.loaded_segments (0x59880 : word) = Some W_59830.
Proof. vm_refl. Qed.
Lemma D_59830 : decode_any W_59830 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59834 : bv 32 := 0x369540ef.
Lemma F_59834 : fetch_word Asan.M.loaded_segments (0x59884 : word) = Some W_59834.
Proof. vm_refl. Qed.
Lemma D_59834 : decode_any W_59834 = Some (Jal 1 346984, 4%Z).
Proof. vm_refl. Qed.

Definition W_59838 : bv 32 := 0x001ac583.
Lemma F_59838 : fetch_word Asan.M.loaded_segments (0x59888 : word) = Some W_59838.
Proof. vm_refl. Qed.
Lemma D_59838 : decode_any W_59838 = Some (Load SZ1 false 11 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5983c : bv 32 := 0x40a0053b.
Lemma F_5983c : fetch_word Asan.M.loaded_segments (0x5988c : word) = Some W_5983c.
Proof. vm_refl. Qed.
Lemma D_5983c : decode_any W_5983c = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_59840 : bv 32 := 0x00c57513.
Lemma F_59840 : fetch_word Asan.M.loaded_segments (0x59890 : word) = Some W_59840.
Proof. vm_refl. Qed.
Lemma D_59840 : decode_any W_59840 = Some (OpImm ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_59844 : bv 32 := 0x0f35f593.
Lemma F_59844 : fetch_word Asan.M.loaded_segments (0x59894 : word) = Some W_59844.
Proof. vm_refl. Qed.
Lemma D_59844 : decode_any W_59844 = Some (OpImm ALU_AND 11 11 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_59848 : bv 32 := 0x00a5e533.
Lemma F_59848 : fetch_word Asan.M.loaded_segments (0x59898 : word) = Some W_59848.
Proof. vm_refl. Qed.
Lemma D_59848 : decode_any W_59848 = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5984c : bv 32 := 0x00200593.
Lemma F_5984c : fetch_word Asan.M.loaded_segments (0x5989c : word) = Some W_5984c.
Proof. vm_refl. Qed.
Lemma D_5984c : decode_any W_5984c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_59850 : bv 32 := 0x00aa80a3.
Lemma F_59850 : fetch_word Asan.M.loaded_segments (0x598a0 : word) = Some W_59850.
Proof. vm_refl. Qed.
Lemma D_59850 : decode_any W_59850 = Some (Store SZ1 21 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59854 : bv 32 := 0x0310000f.
Lemma F_59854 : fetch_word Asan.M.loaded_segments (0x598a4 : word) = Some W_59854.
Proof. vm_refl. Qed.
Lemma D_59854 : decode_any W_59854 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59858 : bv 32 := 0x00ba8023.
Lemma F_59858 : fetch_word Asan.M.loaded_segments (0x598a8 : word) = Some W_59858.
Proof. vm_refl. Qed.
Lemma D_59858 : decode_any W_59858 = Some (Store SZ1 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5985c : bv 32 := 0x032a8063.
Lemma F_5985c : fetch_word Asan.M.loaded_segments (0x598ac : word) = Some W_5985c.
Proof. vm_refl. Qed.
Lemma D_5985c : decode_any W_5985c = Some (Branch BC_EQ 21 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59860 : bv 32 := 0x01090693.
Lemma F_59860 : fetch_word Asan.M.loaded_segments (0x598b0 : word) = Some W_59860.
Proof. vm_refl. Qed.
Lemma D_59860 : decode_any W_59860 = Some (OpImm ALU_ADD 13 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59864 : bv 32 := 0x20daee63.
Lemma F_59864 : fetch_word Asan.M.loaded_segments (0x598b4 : word) = Some W_59864.
Proof. vm_refl. Qed.
Lemma D_59864 : decode_any W_59864 = Some (Branch BC_LTU 21 13 540, 4%Z).
Proof. vm_refl. Qed.

Definition W_59868 : bv 32 := 0xfffb7517.
Lemma F_59868 : fetch_word Asan.M.loaded_segments (0x598b8 : word) = Some W_59868.
Proof. vm_refl. Qed.
Lemma D_59868 : decode_any W_59868 = Some (Auipc 10 1048503, 4%Z).
Proof. vm_refl. Qed.

Definition W_5986c : bv 32 := 0xac853503.
Lemma F_5986c : fetch_word Asan.M.loaded_segments (0x598bc : word) = Some W_5986c.
Proof. vm_refl. Qed.
Lemma D_5986c : decode_any W_5986c = Some (Load SZ8 true 10 10 2760, 4%Z).
Proof. vm_refl. Qed.

Definition W_59870 : bv 32 := 0x01593423.
Lemma F_59870 : fetch_word Asan.M.loaded_segments (0x598c0 : word) = Some W_59870.
Proof. vm_refl. Qed.
Lemma D_59870 : decode_any W_59870 = Some (Store SZ8 18 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59874 : bv 32 := 0x0310000f.
Lemma F_59874 : fetch_word Asan.M.loaded_segments (0x598c4 : word) = Some W_59874.
Proof. vm_refl. Qed.
Lemma D_59874 : decode_any W_59874 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59878 : bv 32 := 0x00a93023.
Lemma F_59878 : fetch_word Asan.M.loaded_segments (0x598c8 : word) = Some W_59878.
Proof. vm_refl. Qed.
Lemma D_59878 : decode_any W_59878 = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5987c : bv 32 := 0x000a0513.
Lemma F_5987c : fetch_word Asan.M.loaded_segments (0x598cc : word) = Some W_5987c.
Proof. vm_refl. Qed.
Lemma D_5987c : decode_any W_5987c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59880 : bv 32 := 0x00048593.
Lemma F_59880 : fetch_word Asan.M.loaded_segments (0x598d0 : word) = Some W_59880.
Proof. vm_refl. Qed.
Lemma D_59880 : decode_any W_59880 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59884 : bv 32 := 0x70c350ef.
Lemma F_59884 : fetch_word Asan.M.loaded_segments (0x598d4 : word) = Some W_59884.
Proof. vm_refl. Qed.
Lemma D_59884 : decode_any W_59884 = Some (Jal 1 218892, 4%Z).
Proof. vm_refl. Qed.

Definition W_59888 : bv 32 := 0x000a0513.
Lemma F_59888 : fetch_word Asan.M.loaded_segments (0x598d8 : word) = Some W_59888.
Proof. vm_refl. Qed.
Lemma D_59888 : decode_any W_59888 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5988c : bv 32 := 0x07813083.
Lemma F_5988c : fetch_word Asan.M.loaded_segments (0x598dc : word) = Some W_5988c.
Proof. vm_refl. Qed.
Lemma D_5988c : decode_any W_5988c = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_59890 : bv 32 := 0x07013403.
Lemma F_59890 : fetch_word Asan.M.loaded_segments (0x598e0 : word) = Some W_59890.
Proof. vm_refl. Qed.
Lemma D_59890 : decode_any W_59890 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_59894 : bv 32 := 0x06813483.
Lemma F_59894 : fetch_word Asan.M.loaded_segments (0x598e4 : word) = Some W_59894.
Proof. vm_refl. Qed.
Lemma D_59894 : decode_any W_59894 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_59898 : bv 32 := 0x06013903.
Lemma F_59898 : fetch_word Asan.M.loaded_segments (0x598e8 : word) = Some W_59898.
Proof. vm_refl. Qed.
Lemma D_59898 : decode_any W_59898 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5989c : bv 32 := 0x05813983.
Lemma F_5989c : fetch_word Asan.M.loaded_segments (0x598ec : word) = Some W_5989c.
Proof. vm_refl. Qed.
Lemma D_5989c : decode_any W_5989c = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_598a0 : bv 32 := 0x05013a03.
Lemma F_598a0 : fetch_word Asan.M.loaded_segments (0x598f0 : word) = Some W_598a0.
Proof. vm_refl. Qed.
Lemma D_598a0 : decode_any W_598a0 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_598a4 : bv 32 := 0x04813a83.
Lemma F_598a4 : fetch_word Asan.M.loaded_segments (0x598f4 : word) = Some W_598a4.
Proof. vm_refl. Qed.
Lemma D_598a4 : decode_any W_598a4 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_598a8 : bv 32 := 0x04013b03.
Lemma F_598a8 : fetch_word Asan.M.loaded_segments (0x598f8 : word) = Some W_598a8.
Proof. vm_refl. Qed.
Lemma D_598a8 : decode_any W_598a8 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_598ac : bv 32 := 0x03813b83.
Lemma F_598ac : fetch_word Asan.M.loaded_segments (0x598fc : word) = Some W_598ac.
Proof. vm_refl. Qed.
Lemma D_598ac : decode_any W_598ac = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_598b0 : bv 32 := 0x03013c03.
Lemma F_598b0 : fetch_word Asan.M.loaded_segments (0x59900 : word) = Some W_598b0.
Proof. vm_refl. Qed.
Lemma D_598b0 : decode_any W_598b0 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_598b4 : bv 32 := 0x02813c83.
Lemma F_598b4 : fetch_word Asan.M.loaded_segments (0x59904 : word) = Some W_598b4.
Proof. vm_refl. Qed.
Lemma D_598b4 : decode_any W_598b4 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_598b8 : bv 32 := 0x02013d03.
Lemma F_598b8 : fetch_word Asan.M.loaded_segments (0x59908 : word) = Some W_598b8.
Proof. vm_refl. Qed.
Lemma D_598b8 : decode_any W_598b8 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_598bc : bv 32 := 0x01813d83.
Lemma F_598bc : fetch_word Asan.M.loaded_segments (0x5990c : word) = Some W_598bc.
Proof. vm_refl. Qed.
Lemma D_598bc : decode_any W_598bc = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_598c0 : bv 32 := 0x08010113.
Lemma F_598c0 : fetch_word Asan.M.loaded_segments (0x59910 : word) = Some W_598c0.
Proof. vm_refl. Qed.
Lemma D_598c0 : decode_any W_598c0 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_598c4 : bv 32 := 0x00008067.
Lemma F_598c4 : fetch_word Asan.M.loaded_segments (0x59914 : word) = Some W_598c4.
Proof. vm_refl. Qed.
Lemma D_598c4 : decode_any W_598c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59ce8 : bv 32 := 0xfe010113.
Lemma F_59ce8 : fetch_word Asan.M.loaded_segments (0x59d38 : word) = Some W_59ce8.
Proof. vm_refl. Qed.
Lemma D_59ce8 : decode_any W_59ce8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_59cec : bv 32 := 0x00113c23.
Lemma F_59cec : fetch_word Asan.M.loaded_segments (0x59d3c : word) = Some W_59cec.
Proof. vm_refl. Qed.
Lemma D_59cec : decode_any W_59cec = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_59cf0 : bv 32 := 0x00813823.
Lemma F_59cf0 : fetch_word Asan.M.loaded_segments (0x59d40 : word) = Some W_59cf0.
Proof. vm_refl. Qed.
Lemma D_59cf0 : decode_any W_59cf0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59cf4 : bv 32 := 0x00913423.
Lemma F_59cf4 : fetch_word Asan.M.loaded_segments (0x59d44 : word) = Some W_59cf4.
Proof. vm_refl. Qed.
Lemma D_59cf4 : decode_any W_59cf4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59cf8 : bv 32 := 0x01213023.
Lemma F_59cf8 : fetch_word Asan.M.loaded_segments (0x59d48 : word) = Some W_59cf8.
Proof. vm_refl. Qed.
Lemma D_59cf8 : decode_any W_59cf8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59cfc : bv 32 := 0x00060413.
Lemma F_59cfc : fetch_word Asan.M.loaded_segments (0x59d4c : word) = Some W_59cfc.
Proof. vm_refl. Qed.
Lemma D_59cfc : decode_any W_59cfc = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d00 : bv 32 := 0x00050493.
Lemma F_59d00 : fetch_word Asan.M.loaded_segments (0x59d50 : word) = Some W_59d00.
Proof. vm_refl. Qed.
Lemma D_59d00 : decode_any W_59d00 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d04 : bv 32 := 0xfff50513.
Lemma F_59d04 : fetch_word Asan.M.loaded_segments (0x59d54 : word) = Some W_59d04.
Proof. vm_refl. Qed.
Lemma D_59d04 : decode_any W_59d04 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d08 : bv 32 := 0x00a4c633.
Lemma F_59d08 : fetch_word Asan.M.loaded_segments (0x59d58 : word) = Some W_59d08.
Proof. vm_refl. Qed.
Lemma D_59d08 : decode_any W_59d08 = Some (Op ALU_XOR 12 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d0c : bv 32 := 0x04c57263.
Lemma F_59d0c : fetch_word Asan.M.loaded_segments (0x59d5c : word) = Some W_59d0c.
Proof. vm_refl. Qed.
Lemma D_59d0c : decode_any W_59d0c = Some (Branch BC_GEU 10 12 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d10 : bv 32 := 0x00a5f533.
Lemma F_59d10 : fetch_word Asan.M.loaded_segments (0x59d60 : word) = Some W_59d10.
Proof. vm_refl. Qed.
Lemma D_59d10 : decode_any W_59d10 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d14 : bv 32 := 0x02051e63.
Lemma F_59d14 : fetch_word Asan.M.loaded_segments (0x59d64 : word) = Some W_59d14.
Proof. vm_refl. Qed.
Lemma D_59d14 : decode_any W_59d14 = Some (Branch BC_NE 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d18 : bv 32 := 0x00102517.
Lemma F_59d18 : fetch_word Asan.M.loaded_segments (0x59d68 : word) = Some W_59d18.
Proof. vm_refl. Qed.
Lemma D_59d18 : decode_any W_59d18 = Some (Auipc 10 258, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d1c : bv 32 := 0x00100713.
Lemma F_59d1c : fetch_word Asan.M.loaded_segments (0x59d6c : word) = Some W_59d1c.
Proof. vm_refl. Qed.
Lemma D_59d1c : decode_any W_59d1c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d20 : bv 32 := 0x6b050513.
Lemma F_59d20 : fetch_word Asan.M.loaded_segments (0x59d70 : word) = Some W_59d20.
Proof. vm_refl. Qed.
Lemma D_59d20 : decode_any W_59d20 = Some (OpImm ALU_ADD 10 10 1712, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d24 : bv 32 := 0x00100793.
Lemma F_59d24 : fetch_word Asan.M.loaded_segments (0x59d74 : word) = Some W_59d24.
Proof. vm_refl. Qed.
Lemma D_59d24 : decode_any W_59d24 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d28 : bv 32 := 0x00048613.
Lemma F_59d28 : fetch_word Asan.M.loaded_segments (0x59d78 : word) = Some W_59d28.
Proof. vm_refl. Qed.
Lemma D_59d28 : decode_any W_59d28 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d2c : bv 32 := 0x00040693.
Lemma F_59d2c : fetch_word Asan.M.loaded_segments (0x59d7c : word) = Some W_59d2c.
Proof. vm_refl. Qed.
Lemma D_59d2c : decode_any W_59d2c = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d30 : bv 32 := 0xc24ff0ef.
Lemma F_59d30 : fetch_word Asan.M.loaded_segments (0x59d80 : word) = Some W_59d30.
Proof. vm_refl. Qed.
Lemma D_59d30 : decode_any W_59d30 = Some (Jal 1 2094116, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d34 : bv 32 := 0x04050663.
Lemma F_59d34 : fetch_word Asan.M.loaded_segments (0x59d84 : word) = Some W_59d34.
Proof. vm_refl. Qed.
Lemma D_59d34 : decode_any W_59d34 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d38 : bv 32 := 0x01813083.
Lemma F_59d38 : fetch_word Asan.M.loaded_segments (0x59d88 : word) = Some W_59d38.
Proof. vm_refl. Qed.
Lemma D_59d38 : decode_any W_59d38 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d3c : bv 32 := 0x01013403.
Lemma F_59d3c : fetch_word Asan.M.loaded_segments (0x59d8c : word) = Some W_59d3c.
Proof. vm_refl. Qed.
Lemma D_59d3c : decode_any W_59d3c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d40 : bv 32 := 0x00813483.
Lemma F_59d40 : fetch_word Asan.M.loaded_segments (0x59d90 : word) = Some W_59d40.
Proof. vm_refl. Qed.
Lemma D_59d40 : decode_any W_59d40 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d44 : bv 32 := 0x00013903.
Lemma F_59d44 : fetch_word Asan.M.loaded_segments (0x59d94 : word) = Some W_59d44.
Proof. vm_refl. Qed.
Lemma D_59d44 : decode_any W_59d44 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d48 : bv 32 := 0x02010113.
Lemma F_59d48 : fetch_word Asan.M.loaded_segments (0x59d98 : word) = Some W_59d48.
Proof. vm_refl. Qed.
Lemma D_59d48 : decode_any W_59d48 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_59d4c : bv 32 := 0x00008067.
Lemma F_59d4c : fetch_word Asan.M.loaded_segments (0x59d9c : word) = Some W_59d4c.
Proof. vm_refl. Qed.
Lemma D_59d4c : decode_any W_59d4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r3cf10_3de98.
Module Na0_code_r6b6d0_6b828.
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

Definition W_8c838 : bv 32 := 0xfd010113.
Lemma F_8c838 : fetch_word Asan.M.loaded_segments (0x8c888 : word) = Some W_8c838.
Proof. vm_refl. Qed.
Lemma D_8c838 : decode_any W_8c838 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c83c : bv 32 := 0x02113423.
Lemma F_8c83c : fetch_word Asan.M.loaded_segments (0x8c88c : word) = Some W_8c83c.
Proof. vm_refl. Qed.
Lemma D_8c83c : decode_any W_8c83c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c840 : bv 32 := 0x02813023.
Lemma F_8c840 : fetch_word Asan.M.loaded_segments (0x8c890 : word) = Some W_8c840.
Proof. vm_refl. Qed.
Lemma D_8c840 : decode_any W_8c840 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c844 : bv 32 := 0x00913c23.
Lemma F_8c844 : fetch_word Asan.M.loaded_segments (0x8c894 : word) = Some W_8c844.
Proof. vm_refl. Qed.
Lemma D_8c844 : decode_any W_8c844 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c848 : bv 32 := 0x01213823.
Lemma F_8c848 : fetch_word Asan.M.loaded_segments (0x8c898 : word) = Some W_8c848.
Proof. vm_refl. Qed.
Lemma D_8c848 : decode_any W_8c848 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c84c : bv 32 := 0x01313423.
Lemma F_8c84c : fetch_word Asan.M.loaded_segments (0x8c89c : word) = Some W_8c84c.
Proof. vm_refl. Qed.
Lemma D_8c84c : decode_any W_8c84c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c850 : bv 32 := 0x00163517.
Lemma F_8c850 : fetch_word Asan.M.loaded_segments (0x8c8a0 : word) = Some W_8c850.
Proof. vm_refl. Qed.
Lemma D_8c850 : decode_any W_8c850 = Some (Auipc 10 355, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c854 : bv 32 := 0xc6850413.
Lemma F_8c854 : fetch_word Asan.M.loaded_segments (0x8c8a4 : word) = Some W_8c854.
Proof. vm_refl. Qed.
Lemma D_8c854 : decode_any W_8c854 = Some (OpImm ALU_ADD 8 10 3176, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c858 : bv 32 := 0x00040503.
Lemma F_8c858 : fetch_word Asan.M.loaded_segments (0x8c8a8 : word) = Some W_8c858.
Proof. vm_refl. Qed.
Lemma D_8c858 : decode_any W_8c858 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c85c : bv 32 := 0x0230000f.
Lemma F_8c85c : fetch_word Asan.M.loaded_segments (0x8c8ac : word) = Some W_8c85c.
Proof. vm_refl. Qed.
Lemma D_8c85c : decode_any W_8c85c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c860 : bv 32 := 0x0e051e63.
Lemma F_8c860 : fetch_word Asan.M.loaded_segments (0x8c8b0 : word) = Some W_8c860.
Proof. vm_refl. Qed.
Lemma D_8c860 : decode_any W_8c860 = Some (Branch BC_NE 10 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c864 : bv 32 := 0x00140513.
Lemma F_8c864 : fetch_word Asan.M.loaded_segments (0x8c8b4 : word) = Some W_8c864.
Proof. vm_refl. Qed.
Lemma D_8c864 : decode_any W_8c864 = Some (OpImm ALU_ADD 10 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c868 : bv 32 := 0x0ff00593.
Lemma F_8c868 : fetch_word Asan.M.loaded_segments (0x8c8b8 : word) = Some W_8c868.
Proof. vm_refl. Qed.
Lemma D_8c868 : decode_any W_8c868 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c86c : bv 32 := 0x00100613.
Lemma F_8c86c : fetch_word Asan.M.loaded_segments (0x8c8bc : word) = Some W_8c86c.
Proof. vm_refl. Qed.
Lemma D_8c86c : decode_any W_8c86c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c870 : bv 32 := 0xffc57693.
Lemma F_8c870 : fetch_word Asan.M.loaded_segments (0x8c8c0 : word) = Some W_8c870.
Proof. vm_refl. Qed.
Lemma D_8c870 : decode_any W_8c870 = Some (OpImm ALU_AND 13 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c874 : bv 32 := 0x00357713.
Lemma F_8c874 : fetch_word Asan.M.loaded_segments (0x8c8c4 : word) = Some W_8c874.
Proof. vm_refl. Qed.
Lemma D_8c874 : decode_any W_8c874 = Some (OpImm ALU_AND 14 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c878 : bv 32 := 0x00371713.
Lemma F_8c878 : fetch_word Asan.M.loaded_segments (0x8c8c8 : word) = Some W_8c878.
Proof. vm_refl. Qed.
Lemma D_8c878 : decode_any W_8c878 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c87c : bv 32 := 0x00e595bb.
Lemma F_8c87c : fetch_word Asan.M.loaded_segments (0x8c8cc : word) = Some W_8c87c.
Proof. vm_refl. Qed.
Lemma D_8c87c : decode_any W_8c87c = Some (Op32 ALU_SLL 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c880 : bv 32 := 0x00e6163b.
Lemma F_8c880 : fetch_word Asan.M.loaded_segments (0x8c8d0 : word) = Some W_8c880.
Proof. vm_refl. Qed.
Lemma D_8c880 : decode_any W_8c880 = Some (Op32 ALU_SLL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c884 : bv 32 := 0x1406a7af.
Lemma F_8c884 : fetch_word Asan.M.loaded_segments (0x8c8d4 : word) = Some W_8c884.
Proof. vm_refl. Qed.
Lemma D_8c884 : decode_any W_8c884 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c888 : bv 32 := 0x00060813.
Lemma F_8c888 : fetch_word Asan.M.loaded_segments (0x8c8d8 : word) = Some W_8c888.
Proof. vm_refl. Qed.
Lemma D_8c888 : decode_any W_8c888 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c88c : bv 32 := 0x0107c833.
Lemma F_8c88c : fetch_word Asan.M.loaded_segments (0x8c8dc : word) = Some W_8c88c.
Proof. vm_refl. Qed.
Lemma D_8c88c : decode_any W_8c88c = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c890 : bv 32 := 0x00b87833.
Lemma F_8c890 : fetch_word Asan.M.loaded_segments (0x8c8e0 : word) = Some W_8c890.
Proof. vm_refl. Qed.
Lemma D_8c890 : decode_any W_8c890 = Some (Op ALU_AND 16 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c894 : bv 32 := 0x0107c833.
Lemma F_8c894 : fetch_word Asan.M.loaded_segments (0x8c8e4 : word) = Some W_8c894.
Proof. vm_refl. Qed.
Lemma D_8c894 : decode_any W_8c894 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c898 : bv 32 := 0x1906a82f.
Lemma F_8c898 : fetch_word Asan.M.loaded_segments (0x8c8e8 : word) = Some W_8c898.
Proof. vm_refl. Qed.
Lemma D_8c898 : decode_any W_8c898 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c89c : bv 32 := 0xfe0814e3.
Lemma F_8c89c : fetch_word Asan.M.loaded_segments (0x8c8ec : word) = Some W_8c89c.
Proof. vm_refl. Qed.
Lemma D_8c89c : decode_any W_8c89c = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8a0 : bv 32 := 0x00e7d5bb.
Lemma F_8c8a0 : fetch_word Asan.M.loaded_segments (0x8c8f0 : word) = Some W_8c8a0.
Proof. vm_refl. Qed.
Lemma D_8c8a0 : decode_any W_8c8a0 = Some (Op32 ALU_SRL 11 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8a4 : bv 32 := 0x0ff5f593.
Lemma F_8c8a4 : fetch_word Asan.M.loaded_segments (0x8c8f4 : word) = Some W_8c8a4.
Proof. vm_refl. Qed.
Lemma D_8c8a4 : decode_any W_8c8a4 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8a8 : bv 32 := 0x0c059c63.
Lemma F_8c8a8 : fetch_word Asan.M.loaded_segments (0x8c8f8 : word) = Some W_8c8a8.
Proof. vm_refl. Qed.
Lemma D_8c8a8 : decode_any W_8c8a8 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8ac : bv 32 := 0x00040503.
Lemma F_8c8ac : fetch_word Asan.M.loaded_segments (0x8c8fc : word) = Some W_8c8ac.
Proof. vm_refl. Qed.
Lemma D_8c8ac : decode_any W_8c8ac = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8b0 : bv 32 := 0x0a051263.
Lemma F_8c8b0 : fetch_word Asan.M.loaded_segments (0x8c900 : word) = Some W_8c8b0.
Proof. vm_refl. Qed.
Lemma D_8c8b0 : decode_any W_8c8b0 = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8b4 : bv 32 := 0x000d4517.
Lemma F_8c8b4 : fetch_word Asan.M.loaded_segments (0x8c904 : word) = Some W_8c8b4.
Proof. vm_refl. Qed.
Lemma D_8c8b4 : decode_any W_8c8b4 = Some (Auipc 10 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8b8 : bv 32 := 0x000815b7.
Lemma F_8c8b8 : fetch_word Asan.M.loaded_segments (0x8c908 : word) = Some W_8c8b8.
Proof. vm_refl. Qed.
Lemma D_8c8b8 : decode_any W_8c8b8 = Some (Lui 11 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8bc : bv 32 := 0x37c50493.
Lemma F_8c8bc : fetch_word Asan.M.loaded_segments (0x8c90c : word) = Some W_8c8bc.
Proof. vm_refl. Qed.
Lemma D_8c8bc : decode_any W_8c8bc = Some (OpImm ALU_ADD 9 10 892, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8c0 : bv 32 := 0x0085851b.
Lemma F_8c8c0 : fetch_word Asan.M.loaded_segments (0x8c910 : word) = Some W_8c8c0.
Proof. vm_refl. Qed.
Lemma D_8c8c0 : decode_any W_8c8c0 = Some (OpImm32 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8c4 : bv 32 := 0x00a48533.
Lemma F_8c8c4 : fetch_word Asan.M.loaded_segments (0x8c914 : word) = Some W_8c8c4.
Proof. vm_refl. Qed.
Lemma D_8c8c4 : decode_any W_8c8c4 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8c8 : bv 32 := 0x02800613.
Lemma F_8c8c8 : fetch_word Asan.M.loaded_segments (0x8c918 : word) = Some W_8c8c8.
Proof. vm_refl. Qed.
Lemma D_8c8c8 : decode_any W_8c8c8 = Some (OpImm ALU_ADD 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8cc : bv 32 := 0x00000593.
Lemma F_8c8cc : fetch_word Asan.M.loaded_segments (0x8c91c : word) = Some W_8c8cc.
Proof. vm_refl. Qed.
Lemma D_8c8cc : decode_any W_8c8cc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8d0 : bv 32 := 0x269050ef.
Lemma F_8c8d0 : fetch_word Asan.M.loaded_segments (0x8c920 : word) = Some W_8c8d0.
Proof. vm_refl. Qed.
Lemma D_8c8d0 : decode_any W_8c8d0 = Some (Jal 1 23144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8d4 : bv 32 := 0x00048023.
Lemma F_8c8d4 : fetch_word Asan.M.loaded_segments (0x8c924 : word) = Some W_8c8d4.
Proof. vm_refl. Qed.
Lemma D_8c8d4 : decode_any W_8c8d4 = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8d8 : bv 32 := 0x00848513.
Lemma F_8c8d8 : fetch_word Asan.M.loaded_segments (0x8c928 : word) = Some W_8c8d8.
Proof. vm_refl. Qed.
Lemma D_8c8d8 : decode_any W_8c8d8 = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8dc : bv 32 := 0x00040637.
Lemma F_8c8dc : fetch_word Asan.M.loaded_segments (0x8c92c : word) = Some W_8c8dc.
Proof. vm_refl. Qed.
Lemma D_8c8dc : decode_any W_8c8dc = Some (Lui 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8e0 : bv 32 := 0x000409b7.
Lemma F_8c8e0 : fetch_word Asan.M.loaded_segments (0x8c930 : word) = Some W_8c8e0.
Proof. vm_refl. Qed.
Lemma D_8c8e0 : decode_any W_8c8e0 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8e4 : bv 32 := 0x00000593.
Lemma F_8c8e4 : fetch_word Asan.M.loaded_segments (0x8c934 : word) = Some W_8c8e4.
Proof. vm_refl. Qed.
Lemma D_8c8e4 : decode_any W_8c8e4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8e8 : bv 32 := 0x251050ef.
Lemma F_8c8e8 : fetch_word Asan.M.loaded_segments (0x8c938 : word) = Some W_8c8e8.
Proof. vm_refl. Qed.
Lemma D_8c8e8 : decode_any W_8c8e8 = Some (Jal 1 23120, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8ec : bv 32 := 0x0409851b.
Lemma F_8c8ec : fetch_word Asan.M.loaded_segments (0x8c93c : word) = Some W_8c8ec.
Proof. vm_refl. Qed.
Lemma D_8c8ec : decode_any W_8c8ec = Some (OpImm32 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8f0 : bv 32 := 0x00a48533.
Lemma F_8c8f0 : fetch_word Asan.M.loaded_segments (0x8c940 : word) = Some W_8c8f0.
Proof. vm_refl. Qed.
Lemma D_8c8f0 : decode_any W_8c8f0 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8f4 : bv 32 := 0x01b00613.
Lemma F_8c8f4 : fetch_word Asan.M.loaded_segments (0x8c944 : word) = Some W_8c8f4.
Proof. vm_refl. Qed.
Lemma D_8c8f4 : decode_any W_8c8f4 = Some (OpImm ALU_ADD 12 0 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8f8 : bv 32 := 0x00761613.
Lemma F_8c8f8 : fetch_word Asan.M.loaded_segments (0x8c948 : word) = Some W_8c8f8.
Proof. vm_refl. Qed.
Lemma D_8c8f8 : decode_any W_8c8f8 = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c8fc : bv 32 := 0x00000593.
Lemma F_8c8fc : fetch_word Asan.M.loaded_segments (0x8c94c : word) = Some W_8c8fc.
Proof. vm_refl. Qed.
Lemma D_8c8fc : decode_any W_8c8fc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c900 : bv 32 := 0x239050ef.
Lemma F_8c900 : fetch_word Asan.M.loaded_segments (0x8c950 : word) = Some W_8c900.
Proof. vm_refl. Qed.
Lemma D_8c900 : decode_any W_8c900 = Some (Jal 1 23096, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c904 : bv 32 := 0x00041937.
Lemma F_8c904 : fetch_word Asan.M.loaded_segments (0x8c954 : word) = Some W_8c904.
Proof. vm_refl. Qed.
Lemma D_8c904 : decode_any W_8c904 = Some (Lui 18 65, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c908 : bv 32 := 0xdc09051b.
Lemma F_8c908 : fetch_word Asan.M.loaded_segments (0x8c958 : word) = Some W_8c908.
Proof. vm_refl. Qed.
Lemma D_8c908 : decode_any W_8c908 = Some (OpImm32 10 18 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c90c : bv 32 := 0x00a48533.
Lemma F_8c90c : fetch_word Asan.M.loaded_segments (0x8c95c : word) = Some W_8c90c.
Proof. vm_refl. Qed.
Lemma D_8c90c : decode_any W_8c90c = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c910 : bv 32 := 0x2489861b.
Lemma F_8c910 : fetch_word Asan.M.loaded_segments (0x8c960 : word) = Some W_8c910.
Proof. vm_refl. Qed.
Lemma D_8c910 : decode_any W_8c910 = Some (OpImm32 12 19 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c914 : bv 32 := 0x00000593.
Lemma F_8c914 : fetch_word Asan.M.loaded_segments (0x8c964 : word) = Some W_8c914.
Proof. vm_refl. Qed.
Lemma D_8c914 : decode_any W_8c914 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c918 : bv 32 := 0x221050ef.
Lemma F_8c918 : fetch_word Asan.M.loaded_segments (0x8c968 : word) = Some W_8c918.
Proof. vm_refl. Qed.
Lemma D_8c918 : decode_any W_8c918 = Some (Jal 1 23072, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c91c : bv 32 := 0x000ca517.
Lemma F_8c91c : fetch_word Asan.M.loaded_segments (0x8c96c : word) = Some W_8c91c.
Proof. vm_refl. Qed.
Lemma D_8c91c : decode_any W_8c91c = Some (Auipc 10 202, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c920 : bv 32 := 0x40c53983.
Lemma F_8c920 : fetch_word Asan.M.loaded_segments (0x8c970 : word) = Some W_8c920.
Proof. vm_refl. Qed.
Lemma D_8c920 : decode_any W_8c920 = Some (Load SZ8 true 19 10 1036, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c924 : bv 32 := 0x0009b503.
Lemma F_8c924 : fetch_word Asan.M.loaded_segments (0x8c974 : word) = Some W_8c924.
Proof. vm_refl. Qed.
Lemma D_8c924 : decode_any W_8c924 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c928 : bv 32 := 0x00051663.
Lemma F_8c928 : fetch_word Asan.M.loaded_segments (0x8c978 : word) = Some W_8c928.
Proof. vm_refl. Qed.
Lemma D_8c928 : decode_any W_8c928 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c934 : bv 32 := 0x012485b3.
Lemma F_8c934 : fetch_word Asan.M.loaded_segments (0x8c984 : word) = Some W_8c934.
Proof. vm_refl. Qed.
Lemma D_8c934 : decode_any W_8c934 = Some (Op ALU_ADD 11 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c938 : bv 32 := 0xdd09061b.
Lemma F_8c938 : fetch_word Asan.M.loaded_segments (0x8c988 : word) = Some W_8c938.
Proof. vm_refl. Qed.
Lemma D_8c938 : decode_any W_8c938 = Some (OpImm32 12 18 3536, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c93c : bv 32 := 0x00c48633.
Lemma F_8c93c : fetch_word Asan.M.loaded_segments (0x8c98c : word) = Some W_8c93c.
Proof. vm_refl. Qed.
Lemma D_8c93c : decode_any W_8c93c = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c940 : bv 32 := 0x00100693.
Lemma F_8c940 : fetch_word Asan.M.loaded_segments (0x8c990 : word) = Some W_8c940.
Proof. vm_refl. Qed.
Lemma D_8c940 : decode_any W_8c940 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c944 : bv 32 := 0xdca5b023.
Lemma F_8c944 : fetch_word Asan.M.loaded_segments (0x8c994 : word) = Some W_8c944.
Proof. vm_refl. Qed.
Lemma D_8c944 : decode_any W_8c944 = Some (Store SZ8 11 10 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c948 : bv 32 := 0xdcc5b423.
Lemma F_8c948 : fetch_word Asan.M.loaded_segments (0x8c998 : word) = Some W_8c948.
Proof. vm_refl. Qed.
Lemma D_8c948 : decode_any W_8c948 = Some (Store SZ8 11 12 3528, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c94c : bv 32 := 0x0310000f.
Lemma F_8c94c : fetch_word Asan.M.loaded_segments (0x8c99c : word) = Some W_8c94c.
Proof. vm_refl. Qed.
Lemma D_8c94c : decode_any W_8c94c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c950 : bv 32 := 0x00d40023.
Lemma F_8c950 : fetch_word Asan.M.loaded_segments (0x8c9a0 : word) = Some W_8c950.
Proof. vm_refl. Qed.
Lemma D_8c950 : decode_any W_8c950 = Some (Store SZ1 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c954 : bv 32 := 0x0310000f.
Lemma F_8c954 : fetch_word Asan.M.loaded_segments (0x8c9a4 : word) = Some W_8c954.
Proof. vm_refl. Qed.
Lemma D_8c954 : decode_any W_8c954 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c958 : bv 32 := 0x000400a3.
Lemma F_8c958 : fetch_word Asan.M.loaded_segments (0x8c9a8 : word) = Some W_8c958.
Proof. vm_refl. Qed.
Lemma D_8c958 : decode_any W_8c958 = Some (Store SZ1 8 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c95c : bv 32 := 0x000d4517.
Lemma F_8c95c : fetch_word Asan.M.loaded_segments (0x8c9ac : word) = Some W_8c95c.
Proof. vm_refl. Qed.
Lemma D_8c95c : decode_any W_8c95c = Some (Auipc 10 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c960 : bv 32 := 0x2d450513.
Lemma F_8c960 : fetch_word Asan.M.loaded_segments (0x8c9b0 : word) = Some W_8c960.
Proof. vm_refl. Qed.
Lemma D_8c960 : decode_any W_8c960 = Some (OpImm ALU_ADD 10 10 724, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c964 : bv 32 := 0x02813083.
Lemma F_8c964 : fetch_word Asan.M.loaded_segments (0x8c9b4 : word) = Some W_8c964.
Proof. vm_refl. Qed.
Lemma D_8c964 : decode_any W_8c964 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c968 : bv 32 := 0x02013403.
Lemma F_8c968 : fetch_word Asan.M.loaded_segments (0x8c9b8 : word) = Some W_8c968.
Proof. vm_refl. Qed.
Lemma D_8c968 : decode_any W_8c968 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c96c : bv 32 := 0x01813483.
Lemma F_8c96c : fetch_word Asan.M.loaded_segments (0x8c9bc : word) = Some W_8c96c.
Proof. vm_refl. Qed.
Lemma D_8c96c : decode_any W_8c96c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c970 : bv 32 := 0x01013903.
Lemma F_8c970 : fetch_word Asan.M.loaded_segments (0x8c9c0 : word) = Some W_8c970.
Proof. vm_refl. Qed.
Lemma D_8c970 : decode_any W_8c970 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c974 : bv 32 := 0x00813983.
Lemma F_8c974 : fetch_word Asan.M.loaded_segments (0x8c9c4 : word) = Some W_8c974.
Proof. vm_refl. Qed.
Lemma D_8c974 : decode_any W_8c974 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c978 : bv 32 := 0x03010113.
Lemma F_8c978 : fetch_word Asan.M.loaded_segments (0x8c9c8 : word) = Some W_8c978.
Proof. vm_refl. Qed.
Lemma D_8c978 : decode_any W_8c978 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c97c : bv 32 := 0x00008067.
Lemma F_8c97c : fetch_word Asan.M.loaded_segments (0x8c9cc : word) = Some W_8c97c.
Proof. vm_refl. Qed.
Lemma D_8c97c : decode_any W_8c97c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r6b6d0_6b828.
Module Na0_code_r719b0_719e8.
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

Definition W_92b34 : bv 32 := 0xfffff637.
Lemma F_92b34 : fetch_word Asan.M.loaded_segments (0x92b84 : word) = Some W_92b34.
Proof. vm_refl. Qed.
Lemma D_92b34 : decode_any W_92b34 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b38 : bv 32 := 0x0016069b.
Lemma F_92b38 : fetch_word Asan.M.loaded_segments (0x92b88 : word) = Some W_92b38.
Proof. vm_refl. Qed.
Lemma D_92b38 : decode_any W_92b38 = Some (OpImm32 13 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b3c : bv 32 := 0x00d56863.
Lemma F_92b3c : fetch_word Asan.M.loaded_segments (0x92b8c : word) = Some W_92b3c.
Proof. vm_refl. Qed.
Lemma D_92b3c : decode_any W_92b3c = Some (Branch BC_LTU 10 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b4c : bv 32 := 0x00a63533.
Lemma F_92b4c : fetch_word Asan.M.loaded_segments (0x92b9c : word) = Some W_92b4c.
Proof. vm_refl. Qed.
Lemma D_92b4c : decode_any W_92b4c = Some (Op ALU_SLTU 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b50 : bv 32 := 0x00008067.
Lemma F_92b50 : fetch_word Asan.M.loaded_segments (0x92ba0 : word) = Some W_92b50.
Proof. vm_refl. Qed.
Lemma D_92b50 : decode_any W_92b50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b54 : bv 32 := 0x0de00893.
Lemma F_92b54 : fetch_word Asan.M.loaded_segments (0x92ba4 : word) = Some W_92b54.
Proof. vm_refl. Qed.
Lemma D_92b54 : decode_any W_92b54 = Some (OpImm ALU_ADD 17 0 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b58 : bv 32 := 0x00000073.
Lemma F_92b58 : fetch_word Asan.M.loaded_segments (0x92ba8 : word) = Some W_92b58.
Proof. vm_refl. Qed.
Lemma D_92b58 : decode_any W_92b58 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_92b58 : is_ecall W_92b58 = true.
Proof. reflexivity. Qed.

Definition W_92b5c : bv 32 := 0x00008067.
Lemma F_92b5c : fetch_word Asan.M.loaded_segments (0x92bac : word) = Some W_92b5c.
Proof. vm_refl. Qed.
Lemma D_92b5c : decode_any W_92b5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b60 : bv 32 := 0x0d700893.
Lemma F_92b60 : fetch_word Asan.M.loaded_segments (0x92bb0 : word) = Some W_92b60.
Proof. vm_refl. Qed.
Lemma D_92b60 : decode_any W_92b60 = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b64 : bv 32 := 0x00000073.
Lemma F_92b64 : fetch_word Asan.M.loaded_segments (0x92bb4 : word) = Some W_92b64.
Proof. vm_refl. Qed.
Lemma D_92b64 : decode_any W_92b64 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_92b64 : is_ecall W_92b64 = true.
Proof. reflexivity. Qed.

Definition W_92b68 : bv 32 := 0x00008067.
Lemma F_92b68 : fetch_word Asan.M.loaded_segments (0x92bb8 : word) = Some W_92b68.
Proof. vm_refl. Qed.
Lemma D_92b68 : decode_any W_92b68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r719b0_719e8.
Module Na0_code_r6d8b4_6d91c.
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

Definition W_8ea1c : bv 32 := 0x000c8597.
Lemma F_8ea1c : fetch_word Asan.M.loaded_segments (0x8ea6c : word) = Some W_8ea1c.
Proof. vm_refl. Qed.
Lemma D_8ea1c : decode_any W_8ea1c = Some (Auipc 11 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ea20 : bv 32 := 0x31c5b583.
Lemma F_8ea20 : fetch_word Asan.M.loaded_segments (0x8ea70 : word) = Some W_8ea20.
Proof. vm_refl. Qed.
Lemma D_8ea20 : decode_any W_8ea20 = Some (Load SZ8 true 11 11 796, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ea24 : bv 32 := 0x0905b583.
Lemma F_8ea24 : fetch_word Asan.M.loaded_segments (0x8ea74 : word) = Some W_8ea24.
Proof. vm_refl. Qed.
Lemma D_8ea24 : decode_any W_8ea24 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ea28 : bv 32 := 0x00058e63.
Lemma F_8ea28 : fetch_word Asan.M.loaded_segments (0x8ea78 : word) = Some W_8ea28.
Proof. vm_refl. Qed.
Lemma D_8ea28 : decode_any W_8ea28 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ea44 : bv 32 := 0x00008067.
Lemma F_8ea44 : fetch_word Asan.M.loaded_segments (0x8ea94 : word) = Some W_8ea44.
Proof. vm_refl. Qed.
Lemma D_8ea44 : decode_any W_8ea44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ea60 : bv 32 := 0x000c8597.
Lemma F_8ea60 : fetch_word Asan.M.loaded_segments (0x8eab0 : word) = Some W_8ea60.
Proof. vm_refl. Qed.
Lemma D_8ea60 : decode_any W_8ea60 = Some (Auipc 11 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ea64 : bv 32 := 0x2d85b583.
Lemma F_8ea64 : fetch_word Asan.M.loaded_segments (0x8eab4 : word) = Some W_8ea64.
Proof. vm_refl. Qed.
Lemma D_8ea64 : decode_any W_8ea64 = Some (Load SZ8 true 11 11 728, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ea68 : bv 32 := 0x0905b583.
Lemma F_8ea68 : fetch_word Asan.M.loaded_segments (0x8eab8 : word) = Some W_8ea68.
Proof. vm_refl. Qed.
Lemma D_8ea68 : decode_any W_8ea68 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ea6c : bv 32 := 0x00058a63.
Lemma F_8ea6c : fetch_word Asan.M.loaded_segments (0x8eabc : word) = Some W_8ea6c.
Proof. vm_refl. Qed.
Lemma D_8ea6c : decode_any W_8ea6c = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ea80 : bv 32 := 0x00008067.
Lemma F_8ea80 : fetch_word Asan.M.loaded_segments (0x8ead0 : word) = Some W_8ea80.
Proof. vm_refl. Qed.
Lemma D_8ea80 : decode_any W_8ea80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r6d8b4_6d91c.
Module Na0_code_r736dc_7386c.
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

Definition W_94860 : bv 32 := 0x00060693.
Lemma F_94860 : fetch_word Asan.M.loaded_segments (0x948b0 : word) = Some W_94860.
Proof. vm_refl. Qed.
Lemma D_94860 : decode_any W_94860 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94864 : bv 32 := 0x00000613.
Lemma F_94864 : fetch_word Asan.M.loaded_segments (0x948b4 : word) = Some W_94864.
Proof. vm_refl. Qed.
Lemma D_94864 : decode_any W_94864 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94868 : bv 32 := 0x0040006f.
Lemma F_94868 : fetch_word Asan.M.loaded_segments (0x948b8 : word) = Some W_94868.
Proof. vm_refl. Qed.
Lemma D_94868 : decode_any W_94868 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9486c : bv 32 := 0xfa010113.
Lemma F_9486c : fetch_word Asan.M.loaded_segments (0x948bc : word) = Some W_9486c.
Proof. vm_refl. Qed.
Lemma D_9486c : decode_any W_9486c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_94870 : bv 32 := 0x04113c23.
Lemma F_94870 : fetch_word Asan.M.loaded_segments (0x948c0 : word) = Some W_94870.
Proof. vm_refl. Qed.
Lemma D_94870 : decode_any W_94870 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_94874 : bv 32 := 0x04813823.
Lemma F_94874 : fetch_word Asan.M.loaded_segments (0x948c4 : word) = Some W_94874.
Proof. vm_refl. Qed.
Lemma D_94874 : decode_any W_94874 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_94878 : bv 32 := 0x04913423.
Lemma F_94878 : fetch_word Asan.M.loaded_segments (0x948c8 : word) = Some W_94878.
Proof. vm_refl. Qed.
Lemma D_94878 : decode_any W_94878 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_9487c : bv 32 := 0x05213023.
Lemma F_9487c : fetch_word Asan.M.loaded_segments (0x948cc : word) = Some W_9487c.
Proof. vm_refl. Qed.
Lemma D_9487c : decode_any W_9487c = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_94880 : bv 32 := 0x03313c23.
Lemma F_94880 : fetch_word Asan.M.loaded_segments (0x948d0 : word) = Some W_94880.
Proof. vm_refl. Qed.
Lemma D_94880 : decode_any W_94880 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_94884 : bv 32 := 0x03413823.
Lemma F_94884 : fetch_word Asan.M.loaded_segments (0x948d4 : word) = Some W_94884.
Proof. vm_refl. Qed.
Lemma D_94884 : decode_any W_94884 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_94888 : bv 32 := 0x00068993.
Lemma F_94888 : fetch_word Asan.M.loaded_segments (0x948d8 : word) = Some W_94888.
Proof. vm_refl. Qed.
Lemma D_94888 : decode_any W_94888 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9488c : bv 32 := 0x00060493.
Lemma F_9488c : fetch_word Asan.M.loaded_segments (0x948dc : word) = Some W_9488c.
Proof. vm_refl. Qed.
Lemma D_9488c : decode_any W_9488c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94890 : bv 32 := 0x00058413.
Lemma F_94890 : fetch_word Asan.M.loaded_segments (0x948e0 : word) = Some W_94890.
Proof. vm_refl. Qed.
Lemma D_94890 : decode_any W_94890 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94894 : bv 32 := 0x000c2597.
Lemma F_94894 : fetch_word Asan.M.loaded_segments (0x948e4 : word) = Some W_94894.
Proof. vm_refl. Qed.
Lemma D_94894 : decode_any W_94894 = Some (Auipc 11 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_94898 : bv 32 := 0x4945ba03.
Lemma F_94898 : fetch_word Asan.M.loaded_segments (0x948e8 : word) = Some W_94898.
Proof. vm_refl. Qed.
Lemma D_94898 : decode_any W_94898 = Some (Load SZ8 true 20 11 1172, 4%Z).
Proof. vm_refl. Qed.

Definition W_9489c : bv 32 := 0x000a3583.
Lemma F_9489c : fetch_word Asan.M.loaded_segments (0x948ec : word) = Some W_9489c.
Proof. vm_refl. Qed.
Lemma D_9489c : decode_any W_9489c = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_948a0 : bv 32 := 0x00050913.
Lemma F_948a0 : fetch_word Asan.M.loaded_segments (0x948f0 : word) = Some W_948a0.
Proof. vm_refl. Qed.
Lemma D_948a0 : decode_any W_948a0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_948a4 : bv 32 := 0x00059863.
Lemma F_948a4 : fetch_word Asan.M.loaded_segments (0x948f4 : word) = Some W_948a4.
Proof. vm_refl. Qed.
Lemma D_948a4 : decode_any W_948a4 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_948b4 : bv 32 := 0xfff58513.
Lemma F_948b4 : fetch_word Asan.M.loaded_segments (0x94904 : word) = Some W_948b4.
Proof. vm_refl. Qed.
Lemma D_948b4 : decode_any W_948b4 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_948b8 : bv 32 := 0x00a5f533.
Lemma F_948b8 : fetch_word Asan.M.loaded_segments (0x94908 : word) = Some W_948b8.
Proof. vm_refl. Qed.
Lemma D_948b8 : decode_any W_948b8 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_948bc : bv 32 := 0x0a051863.
Lemma F_948bc : fetch_word Asan.M.loaded_segments (0x9490c : word) = Some W_948bc.
Proof. vm_refl. Qed.
Lemma D_948bc : decode_any W_948bc = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_948c0 : bv 32 := 0x00b40433.
Lemma F_948c0 : fetch_word Asan.M.loaded_segments (0x94910 : word) = Some W_948c0.
Proof. vm_refl. Qed.
Lemma D_948c0 : decode_any W_948c0 = Some (Op ALU_ADD 8 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_948c4 : bv 32 := 0xfff40413.
Lemma F_948c4 : fetch_word Asan.M.loaded_segments (0x94914 : word) = Some W_948c4.
Proof. vm_refl. Qed.
Lemma D_948c4 : decode_any W_948c4 = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_948c8 : bv 32 := 0x40b00533.
Lemma F_948c8 : fetch_word Asan.M.loaded_segments (0x94918 : word) = Some W_948c8.
Proof. vm_refl. Qed.
Lemma D_948c8 : decode_any W_948c8 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_948cc : bv 32 := 0x00a47433.
Lemma F_948cc : fetch_word Asan.M.loaded_segments (0x9491c : word) = Some W_948cc.
Proof. vm_refl. Qed.
Lemma D_948cc : decode_any W_948cc = Some (Op ALU_AND 8 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_948d0 : bv 32 := 0x00059863.
Lemma F_948d0 : fetch_word Asan.M.loaded_segments (0x94920 : word) = Some W_948d0.
Proof. vm_refl. Qed.
Lemma D_948d0 : decode_any W_948d0 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_948e0 : bv 32 := 0x00a97933.
Lemma F_948e0 : fetch_word Asan.M.loaded_segments (0x94930 : word) = Some W_948e0.
Proof. vm_refl. Qed.
Lemma D_948e0 : decode_any W_948e0 = Some (Op ALU_AND 18 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_948e4 : bv 32 := 0x03200513.
Lemma F_948e4 : fetch_word Asan.M.loaded_segments (0x94934 : word) = Some W_948e4.
Proof. vm_refl. Qed.
Lemma D_948e4 : decode_any W_948e4 = Some (OpImm ALU_ADD 10 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_948e8 : bv 32 := 0x00a12023.
Lemma F_948e8 : fetch_word Asan.M.loaded_segments (0x94938 : word) = Some W_948e8.
Proof. vm_refl. Qed.
Lemma D_948e8 : decode_any W_948e8 = Some (Store SZ4 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_948ec : bv 32 := 0x00010613.
Lemma F_948ec : fetch_word Asan.M.loaded_segments (0x9493c : word) = Some W_948ec.
Proof. vm_refl. Qed.
Lemma D_948ec : decode_any W_948ec = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_948f0 : bv 32 := 0x00098513.
Lemma F_948f0 : fetch_word Asan.M.loaded_segments (0x94940 : word) = Some W_948f0.
Proof. vm_refl. Qed.
Lemma D_948f0 : decode_any W_948f0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_948f4 : bv 32 := 0x00040593.
Lemma F_948f4 : fetch_word Asan.M.loaded_segments (0x94944 : word) = Some W_948f4.
Proof. vm_refl. Qed.
Lemma D_948f4 : decode_any W_948f4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_948f8 : bv 32 := 0x608000ef.
Lemma F_948f8 : fetch_word Asan.M.loaded_segments (0x94948 : word) = Some W_948f8.
Proof. vm_refl. Qed.
Lemma D_948f8 : decode_any W_948f8 = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

Definition W_948fc : bv 32 := 0x00012683.
Lemma F_948fc : fetch_word Asan.M.loaded_segments (0x9494c : word) = Some W_948fc.
Proof. vm_refl. Qed.
Lemma D_948fc : decode_any W_948fc = Some (Load SZ4 true 13 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94900 : bv 32 := 0x00050713.
Lemma F_94900 : fetch_word Asan.M.loaded_segments (0x94950 : word) = Some W_94900.
Proof. vm_refl. Qed.
Lemma D_94900 : decode_any W_94900 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94904 : bv 32 := 0x00300613.
Lemma F_94904 : fetch_word Asan.M.loaded_segments (0x94954 : word) = Some W_94904.
Proof. vm_refl. Qed.
Lemma D_94904 : decode_any W_94904 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_94908 : bv 32 := 0x00090513.
Lemma F_94908 : fetch_word Asan.M.loaded_segments (0x94958 : word) = Some W_94908.
Proof. vm_refl. Qed.
Lemma D_94908 : decode_any W_94908 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9490c : bv 32 := 0x00040593.
Lemma F_9490c : fetch_word Asan.M.loaded_segments (0x9495c : word) = Some W_9490c.
Proof. vm_refl. Qed.
Lemma D_9490c : decode_any W_9490c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94910 : bv 32 := 0x00000793.
Lemma F_94910 : fetch_word Asan.M.loaded_segments (0x94960 : word) = Some W_94910.
Proof. vm_refl. Qed.
Lemma D_94910 : decode_any W_94910 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94914 : bv 32 := 0xa40fe0ef.
Lemma F_94914 : fetch_word Asan.M.loaded_segments (0x94964 : word) = Some W_94914.
Proof. vm_refl. Qed.
Lemma D_94914 : decode_any W_94914 = Some (Jal 1 2089536, 4%Z).
Proof. vm_refl. Qed.

Definition W_94918 : bv 32 := 0x00050993.
Lemma F_94918 : fetch_word Asan.M.loaded_segments (0x94968 : word) = Some W_94918.
Proof. vm_refl. Qed.
Lemma D_94918 : decode_any W_94918 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9491c : bv 32 := 0x00000593.
Lemma F_9491c : fetch_word Asan.M.loaded_segments (0x9496c : word) = Some W_9491c.
Proof. vm_refl. Qed.
Lemma D_9491c : decode_any W_9491c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94920 : bv 32 := 0xa14fe0ef.
Lemma F_94920 : fetch_word Asan.M.loaded_segments (0x94970 : word) = Some W_94920.
Proof. vm_refl. Qed.
Lemma D_94920 : decode_any W_94920 = Some (Jal 1 2089492, 4%Z).
Proof. vm_refl. Qed.

Definition W_94924 : bv 32 := 0xaaaab537.
Lemma F_94924 : fetch_word Asan.M.loaded_segments (0x94974 : word) = Some W_94924.
Proof. vm_refl. Qed.
Lemma D_94924 : decode_any W_94924 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_94928 : bv 32 := 0xaaa50513.
Lemma F_94928 : fetch_word Asan.M.loaded_segments (0x94978 : word) = Some W_94928.
Proof. vm_refl. Qed.
Lemma D_94928 : decode_any W_94928 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_9492c : bv 32 := 0x02a12623.
Lemma F_9492c : fetch_word Asan.M.loaded_segments (0x9497c : word) = Some W_9492c.
Proof. vm_refl. Qed.
Lemma D_9492c : decode_any W_9492c = Some (Store SZ4 2 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_94930 : bv 32 := 0x02c10593.
Lemma F_94930 : fetch_word Asan.M.loaded_segments (0x94980 : word) = Some W_94930.
Proof. vm_refl. Qed.
Lemma D_94930 : decode_any W_94930 = Some (OpImm ALU_ADD 11 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_94934 : bv 32 := 0x00098513.
Lemma F_94934 : fetch_word Asan.M.loaded_segments (0x94984 : word) = Some W_94934.
Proof. vm_refl. Qed.
Lemma D_94934 : decode_any W_94934 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94938 : bv 32 := 0x9fcfe0ef.
Lemma F_94938 : fetch_word Asan.M.loaded_segments (0x94988 : word) = Some W_94938.
Proof. vm_refl. Qed.
Lemma D_94938 : decode_any W_94938 = Some (Jal 1 2089468, 4%Z).
Proof. vm_refl. Qed.

Definition W_9493c : bv 32 := 0x04051063.
Lemma F_9493c : fetch_word Asan.M.loaded_segments (0x9498c : word) = Some W_9493c.
Proof. vm_refl. Qed.
Lemma D_9493c : decode_any W_9493c = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_94940 : bv 32 := 0x00040513.
Lemma F_94940 : fetch_word Asan.M.loaded_segments (0x94990 : word) = Some W_94940.
Proof. vm_refl. Qed.
Lemma D_94940 : decode_any W_94940 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94944 : bv 32 := 0x8d8fa0ef.
Lemma F_94944 : fetch_word Asan.M.loaded_segments (0x94994 : word) = Some W_94944.
Proof. vm_refl. Qed.
Lemma D_94944 : decode_any W_94944 = Some (Jal 1 2072792, 4%Z).
Proof. vm_refl. Qed.

Definition W_94948 : bv 32 := 0x00098513.
Lemma F_94948 : fetch_word Asan.M.loaded_segments (0x94998 : word) = Some W_94948.
Proof. vm_refl. Qed.
Lemma D_94948 : decode_any W_94948 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9494c : bv 32 := 0x05813083.
Lemma F_9494c : fetch_word Asan.M.loaded_segments (0x9499c : word) = Some W_9494c.
Proof. vm_refl. Qed.
Lemma D_9494c : decode_any W_9494c = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_94950 : bv 32 := 0x05013403.
Lemma F_94950 : fetch_word Asan.M.loaded_segments (0x949a0 : word) = Some W_94950.
Proof. vm_refl. Qed.
Lemma D_94950 : decode_any W_94950 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_94954 : bv 32 := 0x04813483.
Lemma F_94954 : fetch_word Asan.M.loaded_segments (0x949a4 : word) = Some W_94954.
Proof. vm_refl. Qed.
Lemma D_94954 : decode_any W_94954 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_94958 : bv 32 := 0x04013903.
Lemma F_94958 : fetch_word Asan.M.loaded_segments (0x949a8 : word) = Some W_94958.
Proof. vm_refl. Qed.
Lemma D_94958 : decode_any W_94958 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9495c : bv 32 := 0x03813983.
Lemma F_9495c : fetch_word Asan.M.loaded_segments (0x949ac : word) = Some W_9495c.
Proof. vm_refl. Qed.
Lemma D_9495c : decode_any W_9495c = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_94960 : bv 32 := 0x03013a03.
Lemma F_94960 : fetch_word Asan.M.loaded_segments (0x949b0 : word) = Some W_94960.
Proof. vm_refl. Qed.
Lemma D_94960 : decode_any W_94960 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_94964 : bv 32 := 0x06010113.
Lemma F_94964 : fetch_word Asan.M.loaded_segments (0x949b4 : word) = Some W_94964.
Proof. vm_refl. Qed.
Lemma D_94964 : decode_any W_94964 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_94968 : bv 32 := 0x00008067.
Lemma F_94968 : fetch_word Asan.M.loaded_segments (0x949b8 : word) = Some W_94968.
Proof. vm_refl. Qed.
Lemma D_94968 : decode_any W_94968 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_949e4 : bv 32 := 0x00060693.
Lemma F_949e4 : fetch_word Asan.M.loaded_segments (0x94a34 : word) = Some W_949e4.
Proof. vm_refl. Qed.
Lemma D_949e4 : decode_any W_949e4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_949e8 : bv 32 := 0x00100613.
Lemma F_949e8 : fetch_word Asan.M.loaded_segments (0x94a38 : word) = Some W_949e8.
Proof. vm_refl. Qed.
Lemma D_949e8 : decode_any W_949e8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_949ec : bv 32 := 0xe81ff06f.
Lemma F_949ec : fetch_word Asan.M.loaded_segments (0x94a3c : word) = Some W_949ec.
Proof. vm_refl. Qed.
Lemma D_949ec : decode_any W_949ec = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r736dc_7386c.
Module Na0_code_r73d7c_73f88.
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

Definition W_94f00 : bv 32 := 0xef010113.
Lemma F_94f00 : fetch_word Asan.M.loaded_segments (0x94f50 : word) = Some W_94f00.
Proof. vm_refl. Qed.
Lemma D_94f00 : decode_any W_94f00 = Some (OpImm ALU_ADD 2 2 3824, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f04 : bv 32 := 0x10113423.
Lemma F_94f04 : fetch_word Asan.M.loaded_segments (0x94f54 : word) = Some W_94f04.
Proof. vm_refl. Qed.
Lemma D_94f04 : decode_any W_94f04 = Some (Store SZ8 2 1 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f08 : bv 32 := 0x10813023.
Lemma F_94f08 : fetch_word Asan.M.loaded_segments (0x94f58 : word) = Some W_94f08.
Proof. vm_refl. Qed.
Lemma D_94f08 : decode_any W_94f08 = Some (Store SZ8 2 8 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f0c : bv 32 := 0x0e913c23.
Lemma F_94f0c : fetch_word Asan.M.loaded_segments (0x94f5c : word) = Some W_94f0c.
Proof. vm_refl. Qed.
Lemma D_94f0c : decode_any W_94f0c = Some (Store SZ8 2 9 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f10 : bv 32 := 0x0f213823.
Lemma F_94f10 : fetch_word Asan.M.loaded_segments (0x94f60 : word) = Some W_94f10.
Proof. vm_refl. Qed.
Lemma D_94f10 : decode_any W_94f10 = Some (Store SZ8 2 18 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f14 : bv 32 := 0x0f313423.
Lemma F_94f14 : fetch_word Asan.M.loaded_segments (0x94f64 : word) = Some W_94f14.
Proof. vm_refl. Qed.
Lemma D_94f14 : decode_any W_94f14 = Some (Store SZ8 2 19 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f18 : bv 32 := 0x0f413023.
Lemma F_94f18 : fetch_word Asan.M.loaded_segments (0x94f68 : word) = Some W_94f18.
Proof. vm_refl. Qed.
Lemma D_94f18 : decode_any W_94f18 = Some (Store SZ8 2 20 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f1c : bv 32 := 0x0d513c23.
Lemma F_94f1c : fetch_word Asan.M.loaded_segments (0x94f6c : word) = Some W_94f1c.
Proof. vm_refl. Qed.
Lemma D_94f1c : decode_any W_94f1c = Some (Store SZ8 2 21 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f20 : bv 32 := 0x00050913.
Lemma F_94f20 : fetch_word Asan.M.loaded_segments (0x94f70 : word) = Some W_94f20.
Proof. vm_refl. Qed.
Lemma D_94f20 : decode_any W_94f20 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f24 : bv 32 := 0xfff00513.
Lemma F_94f24 : fetch_word Asan.M.loaded_segments (0x94f74 : word) = Some W_94f24.
Proof. vm_refl. Qed.
Lemma D_94f24 : decode_any W_94f24 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f28 : bv 32 := 0x12090463.
Lemma F_94f28 : fetch_word Asan.M.loaded_segments (0x94f78 : word) = Some W_94f28.
Proof. vm_refl. Qed.
Lemma D_94f28 : decode_any W_94f28 = Some (Branch BC_EQ 18 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f2c : bv 32 := 0x00060413.
Lemma F_94f2c : fetch_word Asan.M.loaded_segments (0x94f7c : word) = Some W_94f2c.
Proof. vm_refl. Qed.
Lemma D_94f2c : decode_any W_94f2c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f30 : bv 32 := 0x000c2617.
Lemma F_94f30 : fetch_word Asan.M.loaded_segments (0x94f80 : word) = Some W_94f30.
Proof. vm_refl. Qed.
Lemma D_94f30 : decode_any W_94f30 = Some (Auipc 12 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f34 : bv 32 := 0xe0863603.
Lemma F_94f34 : fetch_word Asan.M.loaded_segments (0x94f84 : word) = Some W_94f34.
Proof. vm_refl. Qed.
Lemma D_94f34 : decode_any W_94f34 = Some (Load SZ8 true 12 12 3592, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f38 : bv 32 := 0x10464603.
Lemma F_94f38 : fetch_word Asan.M.loaded_segments (0x94f88 : word) = Some W_94f38.
Proof. vm_refl. Qed.
Lemma D_94f38 : decode_any W_94f38 = Some (Load SZ1 false 12 12 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f3c : bv 32 := 0x00167613.
Lemma F_94f3c : fetch_word Asan.M.loaded_segments (0x94f8c : word) = Some W_94f3c.
Proof. vm_refl. Qed.
Lemma D_94f3c : decode_any W_94f3c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_94f40 : bv 32 := 0x10060863.
Lemma F_94f40 : fetch_word Asan.M.loaded_segments (0x94f90 : word) = Some W_94f40.
Proof. vm_refl. Qed.
Lemma D_94f40 : decode_any W_94f40 = Some (Branch BC_EQ 12 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_95050 : bv 32 := 0x0005051b.
Lemma F_95050 : fetch_word Asan.M.loaded_segments (0x950a0 : word) = Some W_95050.
Proof. vm_refl. Qed.
Lemma D_95050 : decode_any W_95050 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_95054 : bv 32 := 0x10813083.
Lemma F_95054 : fetch_word Asan.M.loaded_segments (0x950a4 : word) = Some W_95054.
Proof. vm_refl. Qed.
Lemma D_95054 : decode_any W_95054 = Some (Load SZ8 true 1 2 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_95058 : bv 32 := 0x10013403.
Lemma F_95058 : fetch_word Asan.M.loaded_segments (0x950a8 : word) = Some W_95058.
Proof. vm_refl. Qed.
Lemma D_95058 : decode_any W_95058 = Some (Load SZ8 true 8 2 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_9505c : bv 32 := 0x0f813483.
Lemma F_9505c : fetch_word Asan.M.loaded_segments (0x950ac : word) = Some W_9505c.
Proof. vm_refl. Qed.
Lemma D_9505c : decode_any W_9505c = Some (Load SZ8 true 9 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_95060 : bv 32 := 0x0f013903.
Lemma F_95060 : fetch_word Asan.M.loaded_segments (0x950b0 : word) = Some W_95060.
Proof. vm_refl. Qed.
Lemma D_95060 : decode_any W_95060 = Some (Load SZ8 true 18 2 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_95064 : bv 32 := 0x0e813983.
Lemma F_95064 : fetch_word Asan.M.loaded_segments (0x950b4 : word) = Some W_95064.
Proof. vm_refl. Qed.
Lemma D_95064 : decode_any W_95064 = Some (Load SZ8 true 19 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_95068 : bv 32 := 0x0e013a03.
Lemma F_95068 : fetch_word Asan.M.loaded_segments (0x950b8 : word) = Some W_95068.
Proof. vm_refl. Qed.
Lemma D_95068 : decode_any W_95068 = Some (Load SZ8 true 20 2 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_9506c : bv 32 := 0x0d813a83.
Lemma F_9506c : fetch_word Asan.M.loaded_segments (0x950bc : word) = Some W_9506c.
Proof. vm_refl. Qed.
Lemma D_9506c : decode_any W_9506c = Some (Load SZ8 true 21 2 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_95070 : bv 32 := 0x11010113.
Lemma F_95070 : fetch_word Asan.M.loaded_segments (0x950c0 : word) = Some W_95070.
Proof. vm_refl. Qed.
Lemma D_95070 : decode_any W_95070 = Some (OpImm ALU_ADD 2 2 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_95074 : bv 32 := 0x00008067.
Lemma F_95074 : fetch_word Asan.M.loaded_segments (0x950c4 : word) = Some W_95074.
Proof. vm_refl. Qed.
Lemma D_95074 : decode_any W_95074 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r73d7c_73f88.
Module Na0_code_r7b920_7b940.
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

Definition W_9caa4 : bv 32 := 0xfe010113.
Lemma F_9caa4 : fetch_word Asan.M.loaded_segments (0x9caf4 : word) = Some W_9caa4.
Proof. vm_refl. Qed.
Lemma D_9caa4 : decode_any W_9caa4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cbf0 : bv 32 := 0x00058513.
Lemma F_9cbf0 : fetch_word Asan.M.loaded_segments (0x9cc40 : word) = Some W_9cbf0.
Proof. vm_refl. Qed.
Lemma D_9cbf0 : decode_any W_9cbf0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cbf4 : bv 32 := 0x00060593.
Lemma F_9cbf4 : fetch_word Asan.M.loaded_segments (0x9cc44 : word) = Some W_9cbf4.
Proof. vm_refl. Qed.
Lemma D_9cbf4 : decode_any W_9cbf4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cbf8 : bv 32 := 0x00068613.
Lemma F_9cbf8 : fetch_word Asan.M.loaded_segments (0x9cc48 : word) = Some W_9cbf8.
Proof. vm_refl. Qed.
Lemma D_9cbf8 : decode_any W_9cbf8 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cbfc : bv 32 := 0xc65f706f.
Lemma F_9cbfc : fetch_word Asan.M.loaded_segments (0x9cc4c : word) = Some W_9cbfc.
Proof. vm_refl. Qed.
Lemma D_9cbfc : decode_any W_9cbfc = Some (Jal 0 2063460, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r7b920_7b940.
Module Na0_code_r956bc_95730.
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

Definition W_9caa4 : bv 32 := 0xfe010113.
Lemma F_9caa4 : fetch_word Asan.M.loaded_segments (0x9caf4 : word) = Some W_9caa4.
Proof. vm_refl. Qed.
Lemma D_9caa4 : decode_any W_9caa4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9caa8 : bv 32 := 0x00113c23.
Lemma F_9caa8 : fetch_word Asan.M.loaded_segments (0x9caf8 : word) = Some W_9caa8.
Proof. vm_refl. Qed.
Lemma D_9caa8 : decode_any W_9caa8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9caac : bv 32 := 0x00813823.
Lemma F_9caac : fetch_word Asan.M.loaded_segments (0x9cafc : word) = Some W_9caac.
Proof. vm_refl. Qed.
Lemma D_9caac : decode_any W_9caac = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cab0 : bv 32 := 0x00913423.
Lemma F_9cab0 : fetch_word Asan.M.loaded_segments (0x9cb00 : word) = Some W_9cab0.
Proof. vm_refl. Qed.
Lemma D_9cab0 : decode_any W_9cab0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cab4 : bv 32 := 0x01213023.
Lemma F_9cab4 : fetch_word Asan.M.loaded_segments (0x9cb04 : word) = Some W_9cab4.
Proof. vm_refl. Qed.
Lemma D_9cab4 : decode_any W_9cab4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cab8 : bv 32 := 0x00060413.
Lemma F_9cab8 : fetch_word Asan.M.loaded_segments (0x9cb08 : word) = Some W_9cab8.
Proof. vm_refl. Qed.
Lemma D_9cab8 : decode_any W_9cab8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cabc : bv 32 := 0x00058493.
Lemma F_9cabc : fetch_word Asan.M.loaded_segments (0x9cb0c : word) = Some W_9cabc.
Proof. vm_refl. Qed.
Lemma D_9cabc : decode_any W_9cabc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cac0 : bv 32 := 0x00058513.
Lemma F_9cac0 : fetch_word Asan.M.loaded_segments (0x9cb10 : word) = Some W_9cac0.
Proof. vm_refl. Qed.
Lemma D_9cac0 : decode_any W_9cac0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cac4 : bv 32 := 0x00060593.
Lemma F_9cac4 : fetch_word Asan.M.loaded_segments (0x9cb14 : word) = Some W_9cac4.
Proof. vm_refl. Qed.
Lemma D_9cac4 : decode_any W_9cac4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cac8 : bv 32 := 0x00068613.
Lemma F_9cac8 : fetch_word Asan.M.loaded_segments (0x9cb18 : word) = Some W_9cac8.
Proof. vm_refl. Qed.
Lemma D_9cac8 : decode_any W_9cac8 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cacc : bv 32 := 0xf19f70ef.
Lemma F_9cacc : fetch_word Asan.M.loaded_segments (0x9cb1c : word) = Some W_9cacc.
Proof. vm_refl. Qed.
Lemma D_9cacc : decode_any W_9cacc = Some (Jal 1 2064152, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cad0 : bv 32 := 0x00050e63.
Lemma F_9cad0 : fetch_word Asan.M.loaded_segments (0x9cb20 : word) = Some W_9cad0.
Proof. vm_refl. Qed.
Lemma D_9cad0 : decode_any W_9cad0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cad4 : bv 32 := 0x01813083.
Lemma F_9cad4 : fetch_word Asan.M.loaded_segments (0x9cb24 : word) = Some W_9cad4.
Proof. vm_refl. Qed.
Lemma D_9cad4 : decode_any W_9cad4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cad8 : bv 32 := 0x01013403.
Lemma F_9cad8 : fetch_word Asan.M.loaded_segments (0x9cb28 : word) = Some W_9cad8.
Proof. vm_refl. Qed.
Lemma D_9cad8 : decode_any W_9cad8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cadc : bv 32 := 0x00813483.
Lemma F_9cadc : fetch_word Asan.M.loaded_segments (0x9cb2c : word) = Some W_9cadc.
Proof. vm_refl. Qed.
Lemma D_9cadc : decode_any W_9cadc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cae0 : bv 32 := 0x00013903.
Lemma F_9cae0 : fetch_word Asan.M.loaded_segments (0x9cb30 : word) = Some W_9cae0.
Proof. vm_refl. Qed.
Lemma D_9cae0 : decode_any W_9cae0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cae4 : bv 32 := 0x02010113.
Lemma F_9cae4 : fetch_word Asan.M.loaded_segments (0x9cb34 : word) = Some W_9cae4.
Proof. vm_refl. Qed.
Lemma D_9cae4 : decode_any W_9cae4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cae8 : bv 32 := 0x00008067.
Lemma F_9cae8 : fetch_word Asan.M.loaded_segments (0x9cb38 : word) = Some W_9cae8.
Proof. vm_refl. Qed.
Lemma D_9cae8 : decode_any W_9cae8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9caec : bv 32 := 0x00050913.
Lemma F_9caec : fetch_word Asan.M.loaded_segments (0x9cb3c : word) = Some W_9caec.
Proof. vm_refl. Qed.
Lemma D_9caec : decode_any W_9caec = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9caf0 : bv 32 := 0x00048513.
Lemma F_9caf0 : fetch_word Asan.M.loaded_segments (0x9cb40 : word) = Some W_9caf0.
Proof. vm_refl. Qed.
Lemma D_9caf0 : decode_any W_9caf0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9caf4 : bv 32 := 0x00040593.
Lemma F_9caf4 : fetch_word Asan.M.loaded_segments (0x9cb44 : word) = Some W_9caf4.
Proof. vm_refl. Qed.
Lemma D_9caf4 : decode_any W_9caf4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9caf8 : bv 32 := 0x020000ef.
Lemma F_9caf8 : fetch_word Asan.M.loaded_segments (0x9cb48 : word) = Some W_9caf8.
Proof. vm_refl. Qed.
Lemma D_9caf8 : decode_any W_9caf8 = Some (Jal 1 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cafc : bv 32 := 0x00090513.
Lemma F_9cafc : fetch_word Asan.M.loaded_segments (0x9cb4c : word) = Some W_9cafc.
Proof. vm_refl. Qed.
Lemma D_9cafc : decode_any W_9cafc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cb00 : bv 32 := 0x01813083.
Lemma F_9cb00 : fetch_word Asan.M.loaded_segments (0x9cb50 : word) = Some W_9cb00.
Proof. vm_refl. Qed.
Lemma D_9cb00 : decode_any W_9cb00 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cb04 : bv 32 := 0x01013403.
Lemma F_9cb04 : fetch_word Asan.M.loaded_segments (0x9cb54 : word) = Some W_9cb04.
Proof. vm_refl. Qed.
Lemma D_9cb04 : decode_any W_9cb04 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cb08 : bv 32 := 0x00813483.
Lemma F_9cb08 : fetch_word Asan.M.loaded_segments (0x9cb58 : word) = Some W_9cb08.
Proof. vm_refl. Qed.
Lemma D_9cb08 : decode_any W_9cb08 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cb0c : bv 32 := 0x00013903.
Lemma F_9cb0c : fetch_word Asan.M.loaded_segments (0x9cb5c : word) = Some W_9cb0c.
Proof. vm_refl. Qed.
Lemma D_9cb0c : decode_any W_9cb0c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cb10 : bv 32 := 0x02010113.
Lemma F_9cb10 : fetch_word Asan.M.loaded_segments (0x9cb60 : word) = Some W_9cb10.
Proof. vm_refl. Qed.
Lemma D_9cb10 : decode_any W_9cb10 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cb14 : bv 32 := 0x00008067.
Lemma F_9cb14 : fetch_word Asan.M.loaded_segments (0x9cb64 : word) = Some W_9cb14.
Proof. vm_refl. Qed.
Lemma D_9cb14 : decode_any W_9cb14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r956bc_95730.
Module Na0_code_r731ac_733ac.
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

Definition W_943a4 : bv 32 := 0xfd010113.
Lemma F_943a4 : fetch_word Asan.M.loaded_segments (0x943f4 : word) = Some W_943a4.
Proof. vm_refl. Qed.
Lemma D_943a4 : decode_any W_943a4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_943a8 : bv 32 := 0x02113423.
Lemma F_943a8 : fetch_word Asan.M.loaded_segments (0x943f8 : word) = Some W_943a8.
Proof. vm_refl. Qed.
Lemma D_943a8 : decode_any W_943a8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_943ac : bv 32 := 0x02813023.
Lemma F_943ac : fetch_word Asan.M.loaded_segments (0x943fc : word) = Some W_943ac.
Proof. vm_refl. Qed.
Lemma D_943ac : decode_any W_943ac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_943b0 : bv 32 := 0x00913c23.
Lemma F_943b0 : fetch_word Asan.M.loaded_segments (0x94400 : word) = Some W_943b0.
Proof. vm_refl. Qed.
Lemma D_943b0 : decode_any W_943b0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_943b4 : bv 32 := 0x01213823.
Lemma F_943b4 : fetch_word Asan.M.loaded_segments (0x94404 : word) = Some W_943b4.
Proof. vm_refl. Qed.
Lemma D_943b4 : decode_any W_943b4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_943b8 : bv 32 := 0x02050e63.
Lemma F_943b8 : fetch_word Asan.M.loaded_segments (0x94408 : word) = Some W_943b8.
Proof. vm_refl. Qed.
Lemma D_943b8 : decode_any W_943b8 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_943bc : bv 32 := 0x00058413.
Lemma F_943bc : fetch_word Asan.M.loaded_segments (0x9440c : word) = Some W_943bc.
Proof. vm_refl. Qed.
Lemma D_943bc : decode_any W_943bc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_943c0 : bv 32 := 0x02058a63.
Lemma F_943c0 : fetch_word Asan.M.loaded_segments (0x94410 : word) = Some W_943c0.
Proof. vm_refl. Qed.
Lemma D_943c0 : decode_any W_943c0 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_943c4 : bv 32 := 0x00060493.
Lemma F_943c4 : fetch_word Asan.M.loaded_segments (0x94414 : word) = Some W_943c4.
Proof. vm_refl. Qed.
Lemma D_943c4 : decode_any W_943c4 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_943c8 : bv 32 := 0x00050913.
Lemma F_943c8 : fetch_word Asan.M.loaded_segments (0x94418 : word) = Some W_943c8.
Proof. vm_refl. Qed.
Lemma D_943c8 : decode_any W_943c8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_943cc : bv 32 := 0x00040593.
Lemma F_943cc : fetch_word Asan.M.loaded_segments (0x9441c : word) = Some W_943cc.
Proof. vm_refl. Qed.
Lemma D_943cc : decode_any W_943cc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_943d0 : bv 32 := 0xf90fe0ef.
Lemma F_943d0 : fetch_word Asan.M.loaded_segments (0x94420 : word) = Some W_943d0.
Proof. vm_refl. Qed.
Lemma D_943d0 : decode_any W_943d0 = Some (Jal 1 2090896, 4%Z).
Proof. vm_refl. Qed.

Definition W_943d4 : bv 32 := 0xaaaab5b7.
Lemma F_943d4 : fetch_word Asan.M.loaded_segments (0x94424 : word) = Some W_943d4.
Proof. vm_refl. Qed.
Lemma D_943d4 : decode_any W_943d4 = Some (Lui 11 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_943d8 : bv 32 := 0xaaa58593.
Lemma F_943d8 : fetch_word Asan.M.loaded_segments (0x94428 : word) = Some W_943d8.
Proof. vm_refl. Qed.
Lemma D_943d8 : decode_any W_943d8 = Some (OpImm ALU_ADD 11 11 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_943dc : bv 32 := 0x00b12623.
Lemma F_943dc : fetch_word Asan.M.loaded_segments (0x9442c : word) = Some W_943dc.
Proof. vm_refl. Qed.
Lemma D_943dc : decode_any W_943dc = Some (Store SZ4 2 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_943e0 : bv 32 := 0x00c10593.
Lemma F_943e0 : fetch_word Asan.M.loaded_segments (0x94430 : word) = Some W_943e0.
Proof. vm_refl. Qed.
Lemma D_943e0 : decode_any W_943e0 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_943e4 : bv 32 := 0xf50fe0ef.
Lemma F_943e4 : fetch_word Asan.M.loaded_segments (0x94434 : word) = Some W_943e4.
Proof. vm_refl. Qed.
Lemma D_943e4 : decode_any W_943e4 = Some (Jal 1 2090832, 4%Z).
Proof. vm_refl. Qed.

Definition W_943e8 : bv 32 := 0x02051263.
Lemma F_943e8 : fetch_word Asan.M.loaded_segments (0x94438 : word) = Some W_943e8.
Proof. vm_refl. Qed.
Lemma D_943e8 : decode_any W_943e8 = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_943ec : bv 32 := 0x00040513.
Lemma F_943ec : fetch_word Asan.M.loaded_segments (0x9443c : word) = Some W_943ec.
Proof. vm_refl. Qed.
Lemma D_943ec : decode_any W_943ec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_943f0 : bv 32 := 0xe70fa0ef.
Lemma F_943f0 : fetch_word Asan.M.loaded_segments (0x94440 : word) = Some W_943f0.
Proof. vm_refl. Qed.
Lemma D_943f0 : decode_any W_943f0 = Some (Jal 1 2074224, 4%Z).
Proof. vm_refl. Qed.

Definition W_943f4 : bv 32 := 0x02813083.
Lemma F_943f4 : fetch_word Asan.M.loaded_segments (0x94444 : word) = Some W_943f4.
Proof. vm_refl. Qed.
Lemma D_943f4 : decode_any W_943f4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_943f8 : bv 32 := 0x02013403.
Lemma F_943f8 : fetch_word Asan.M.loaded_segments (0x94448 : word) = Some W_943f8.
Proof. vm_refl. Qed.
Lemma D_943f8 : decode_any W_943f8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_943fc : bv 32 := 0x01813483.
Lemma F_943fc : fetch_word Asan.M.loaded_segments (0x9444c : word) = Some W_943fc.
Proof. vm_refl. Qed.
Lemma D_943fc : decode_any W_943fc = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_94400 : bv 32 := 0x01013903.
Lemma F_94400 : fetch_word Asan.M.loaded_segments (0x94450 : word) = Some W_94400.
Proof. vm_refl. Qed.
Lemma D_94400 : decode_any W_94400 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94404 : bv 32 := 0x03010113.
Lemma F_94404 : fetch_word Asan.M.loaded_segments (0x94454 : word) = Some W_94404.
Proof. vm_refl. Qed.
Lemma D_94404 : decode_any W_94404 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_94408 : bv 32 := 0x00008067.
Lemma F_94408 : fetch_word Asan.M.loaded_segments (0x94458 : word) = Some W_94408.
Proof. vm_refl. Qed.
Lemma D_94408 : decode_any W_94408 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94420 : bv 32 := 0xfd010113.
Lemma F_94420 : fetch_word Asan.M.loaded_segments (0x94470 : word) = Some W_94420.
Proof. vm_refl. Qed.
Lemma D_94420 : decode_any W_94420 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_94424 : bv 32 := 0x02113423.
Lemma F_94424 : fetch_word Asan.M.loaded_segments (0x94474 : word) = Some W_94424.
Proof. vm_refl. Qed.
Lemma D_94424 : decode_any W_94424 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_94428 : bv 32 := 0x02813023.
Lemma F_94428 : fetch_word Asan.M.loaded_segments (0x94478 : word) = Some W_94428.
Proof. vm_refl. Qed.
Lemma D_94428 : decode_any W_94428 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9442c : bv 32 := 0x00913c23.
Lemma F_9442c : fetch_word Asan.M.loaded_segments (0x9447c : word) = Some W_9442c.
Proof. vm_refl. Qed.
Lemma D_9442c : decode_any W_9442c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_94430 : bv 32 := 0x01213823.
Lemma F_94430 : fetch_word Asan.M.loaded_segments (0x94480 : word) = Some W_94430.
Proof. vm_refl. Qed.
Lemma D_94430 : decode_any W_94430 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94434 : bv 32 := 0x00058413.
Lemma F_94434 : fetch_word Asan.M.loaded_segments (0x94484 : word) = Some W_94434.
Proof. vm_refl. Qed.
Lemma D_94434 : decode_any W_94434 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94438 : bv 32 := 0x000c3597.
Lemma F_94438 : fetch_word Asan.M.loaded_segments (0x94488 : word) = Some W_94438.
Proof. vm_refl. Qed.
Lemma D_94438 : decode_any W_94438 = Some (Auipc 11 195, 4%Z).
Proof. vm_refl. Qed.

Definition W_9443c : bv 32 := 0x8f05b903.
Lemma F_9443c : fetch_word Asan.M.loaded_segments (0x9448c : word) = Some W_9443c.
Proof. vm_refl. Qed.
Lemma D_9443c : decode_any W_9443c = Some (Load SZ8 true 18 11 2288, 4%Z).
Proof. vm_refl. Qed.

Definition W_94440 : bv 32 := 0x00093583.
Lemma F_94440 : fetch_word Asan.M.loaded_segments (0x94490 : word) = Some W_94440.
Proof. vm_refl. Qed.
Lemma D_94440 : decode_any W_94440 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94444 : bv 32 := 0x00050493.
Lemma F_94444 : fetch_word Asan.M.loaded_segments (0x94494 : word) = Some W_94444.
Proof. vm_refl. Qed.
Lemma D_94444 : decode_any W_94444 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94448 : bv 32 := 0x00059863.
Lemma F_94448 : fetch_word Asan.M.loaded_segments (0x94498 : word) = Some W_94448.
Proof. vm_refl. Qed.
Lemma D_94448 : decode_any W_94448 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_94458 : bv 32 := 0xfff58513.
Lemma F_94458 : fetch_word Asan.M.loaded_segments (0x944a8 : word) = Some W_94458.
Proof. vm_refl. Qed.
Lemma D_94458 : decode_any W_94458 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9445c : bv 32 := 0x00a5f533.
Lemma F_9445c : fetch_word Asan.M.loaded_segments (0x944ac : word) = Some W_9445c.
Proof. vm_refl. Qed.
Lemma D_9445c : decode_any W_9445c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_94460 : bv 32 := 0x08051a63.
Lemma F_94460 : fetch_word Asan.M.loaded_segments (0x944b0 : word) = Some W_94460.
Proof. vm_refl. Qed.
Lemma D_94460 : decode_any W_94460 = Some (Branch BC_NE 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_94464 : bv 32 := 0x00b484b3.
Lemma F_94464 : fetch_word Asan.M.loaded_segments (0x944b4 : word) = Some W_94464.
Proof. vm_refl. Qed.
Lemma D_94464 : decode_any W_94464 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_94468 : bv 32 := 0x40b00533.
Lemma F_94468 : fetch_word Asan.M.loaded_segments (0x944b8 : word) = Some W_94468.
Proof. vm_refl. Qed.
Lemma D_94468 : decode_any W_94468 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9446c : bv 32 := 0xfff48493.
Lemma F_9446c : fetch_word Asan.M.loaded_segments (0x944bc : word) = Some W_9446c.
Proof. vm_refl. Qed.
Lemma D_9446c : decode_any W_9446c = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94470 : bv 32 := 0x00a4f4b3.
Lemma F_94470 : fetch_word Asan.M.loaded_segments (0x944c0 : word) = Some W_94470.
Proof. vm_refl. Qed.
Lemma D_94470 : decode_any W_94470 = Some (Op ALU_AND 9 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_94474 : bv 32 := 0x02200513.
Lemma F_94474 : fetch_word Asan.M.loaded_segments (0x944c4 : word) = Some W_94474.
Proof. vm_refl. Qed.
Lemma D_94474 : decode_any W_94474 = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_94478 : bv 32 := 0x00a12623.
Lemma F_94478 : fetch_word Asan.M.loaded_segments (0x944c8 : word) = Some W_94478.
Proof. vm_refl. Qed.
Lemma D_94478 : decode_any W_94478 = Some (Store SZ4 2 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9447c : bv 32 := 0x00c10613.
Lemma F_9447c : fetch_word Asan.M.loaded_segments (0x944cc : word) = Some W_9447c.
Proof. vm_refl. Qed.
Lemma D_9447c : decode_any W_9447c = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_94480 : bv 32 := 0x00040513.
Lemma F_94480 : fetch_word Asan.M.loaded_segments (0x944d0 : word) = Some W_94480.
Proof. vm_refl. Qed.
Lemma D_94480 : decode_any W_94480 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94484 : bv 32 := 0x00048593.
Lemma F_94484 : fetch_word Asan.M.loaded_segments (0x944d4 : word) = Some W_94484.
Proof. vm_refl. Qed.
Lemma D_94484 : decode_any W_94484 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94488 : bv 32 := 0x279000ef.
Lemma F_94488 : fetch_word Asan.M.loaded_segments (0x944d8 : word) = Some W_94488.
Proof. vm_refl. Qed.
Lemma D_94488 : decode_any W_94488 = Some (Jal 1 2680, 4%Z).
Proof. vm_refl. Qed.

Definition W_9448c : bv 32 := 0x00c12683.
Lemma F_9448c : fetch_word Asan.M.loaded_segments (0x944dc : word) = Some W_9448c.
Proof. vm_refl. Qed.
Lemma D_9448c : decode_any W_9448c = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_94490 : bv 32 := 0x00050713.
Lemma F_94490 : fetch_word Asan.M.loaded_segments (0x944e0 : word) = Some W_94490.
Proof. vm_refl. Qed.
Lemma D_94490 : decode_any W_94490 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94494 : bv 32 := 0x00300613.
Lemma F_94494 : fetch_word Asan.M.loaded_segments (0x944e4 : word) = Some W_94494.
Proof. vm_refl. Qed.
Lemma D_94494 : decode_any W_94494 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_94498 : bv 32 := 0x00000513.
Lemma F_94498 : fetch_word Asan.M.loaded_segments (0x944e8 : word) = Some W_94498.
Proof. vm_refl. Qed.
Lemma D_94498 : decode_any W_94498 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9449c : bv 32 := 0x00048593.
Lemma F_9449c : fetch_word Asan.M.loaded_segments (0x944ec : word) = Some W_9449c.
Proof. vm_refl. Qed.
Lemma D_9449c : decode_any W_9449c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_944a0 : bv 32 := 0x00000793.
Lemma F_944a0 : fetch_word Asan.M.loaded_segments (0x944f0 : word) = Some W_944a0.
Proof. vm_refl. Qed.
Lemma D_944a0 : decode_any W_944a0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_944a4 : bv 32 := 0xeb0fe0ef.
Lemma F_944a4 : fetch_word Asan.M.loaded_segments (0x944f4 : word) = Some W_944a4.
Proof. vm_refl. Qed.
Lemma D_944a4 : decode_any W_944a4 = Some (Jal 1 2090672, 4%Z).
Proof. vm_refl. Qed.

Definition W_944a8 : bv 32 := 0x00050913.
Lemma F_944a8 : fetch_word Asan.M.loaded_segments (0x944f8 : word) = Some W_944a8.
Proof. vm_refl. Qed.
Lemma D_944a8 : decode_any W_944a8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_944ac : bv 32 := 0x00000593.
Lemma F_944ac : fetch_word Asan.M.loaded_segments (0x944fc : word) = Some W_944ac.
Proof. vm_refl. Qed.
Lemma D_944ac : decode_any W_944ac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_944b0 : bv 32 := 0xe84fe0ef.
Lemma F_944b0 : fetch_word Asan.M.loaded_segments (0x94500 : word) = Some W_944b0.
Proof. vm_refl. Qed.
Lemma D_944b0 : decode_any W_944b0 = Some (Jal 1 2090628, 4%Z).
Proof. vm_refl. Qed.

Definition W_944b4 : bv 32 := 0xaaaab537.
Lemma F_944b4 : fetch_word Asan.M.loaded_segments (0x94504 : word) = Some W_944b4.
Proof. vm_refl. Qed.
Lemma D_944b4 : decode_any W_944b4 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_944b8 : bv 32 := 0xaaa50513.
Lemma F_944b8 : fetch_word Asan.M.loaded_segments (0x94508 : word) = Some W_944b8.
Proof. vm_refl. Qed.
Lemma D_944b8 : decode_any W_944b8 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_944bc : bv 32 := 0x00a12423.
Lemma F_944bc : fetch_word Asan.M.loaded_segments (0x9450c : word) = Some W_944bc.
Proof. vm_refl. Qed.
Lemma D_944bc : decode_any W_944bc = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_944c0 : bv 32 := 0x00810593.
Lemma F_944c0 : fetch_word Asan.M.loaded_segments (0x94510 : word) = Some W_944c0.
Proof. vm_refl. Qed.
Lemma D_944c0 : decode_any W_944c0 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_944c4 : bv 32 := 0x00090513.
Lemma F_944c4 : fetch_word Asan.M.loaded_segments (0x94514 : word) = Some W_944c4.
Proof. vm_refl. Qed.
Lemma D_944c4 : decode_any W_944c4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_944c8 : bv 32 := 0xe6cfe0ef.
Lemma F_944c8 : fetch_word Asan.M.loaded_segments (0x94518 : word) = Some W_944c8.
Proof. vm_refl. Qed.
Lemma D_944c8 : decode_any W_944c8 = Some (Jal 1 2090604, 4%Z).
Proof. vm_refl. Qed.

Definition W_944cc : bv 32 := 0x02051c63.
Lemma F_944cc : fetch_word Asan.M.loaded_segments (0x9451c : word) = Some W_944cc.
Proof. vm_refl. Qed.
Lemma D_944cc : decode_any W_944cc = Some (Branch BC_NE 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_944d0 : bv 32 := 0x00048513.
Lemma F_944d0 : fetch_word Asan.M.loaded_segments (0x94520 : word) = Some W_944d0.
Proof. vm_refl. Qed.
Lemma D_944d0 : decode_any W_944d0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_944d4 : bv 32 := 0xd48fa0ef.
Lemma F_944d4 : fetch_word Asan.M.loaded_segments (0x94524 : word) = Some W_944d4.
Proof. vm_refl. Qed.
Lemma D_944d4 : decode_any W_944d4 = Some (Jal 1 2073928, 4%Z).
Proof. vm_refl. Qed.

Definition W_944d8 : bv 32 := 0x00090513.
Lemma F_944d8 : fetch_word Asan.M.loaded_segments (0x94528 : word) = Some W_944d8.
Proof. vm_refl. Qed.
Lemma D_944d8 : decode_any W_944d8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_944dc : bv 32 := 0x02813083.
Lemma F_944dc : fetch_word Asan.M.loaded_segments (0x9452c : word) = Some W_944dc.
Proof. vm_refl. Qed.
Lemma D_944dc : decode_any W_944dc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_944e0 : bv 32 := 0x02013403.
Lemma F_944e0 : fetch_word Asan.M.loaded_segments (0x94530 : word) = Some W_944e0.
Proof. vm_refl. Qed.
Lemma D_944e0 : decode_any W_944e0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_944e4 : bv 32 := 0x01813483.
Lemma F_944e4 : fetch_word Asan.M.loaded_segments (0x94534 : word) = Some W_944e4.
Proof. vm_refl. Qed.
Lemma D_944e4 : decode_any W_944e4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_944e8 : bv 32 := 0x01013903.
Lemma F_944e8 : fetch_word Asan.M.loaded_segments (0x94538 : word) = Some W_944e8.
Proof. vm_refl. Qed.
Lemma D_944e8 : decode_any W_944e8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_944ec : bv 32 := 0x03010113.
Lemma F_944ec : fetch_word Asan.M.loaded_segments (0x9453c : word) = Some W_944ec.
Proof. vm_refl. Qed.
Lemma D_944ec : decode_any W_944ec = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_944f0 : bv 32 := 0x00008067.
Lemma F_944f0 : fetch_word Asan.M.loaded_segments (0x94540 : word) = Some W_944f0.
Proof. vm_refl. Qed.
Lemma D_944f0 : decode_any W_944f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r731ac_733ac.
