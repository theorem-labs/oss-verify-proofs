(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8cb08 : bv 32 := 0xff010113.
Lemma F_8cb08 : fetch_word AsanUbsan.M.loaded_segments (0x8cb58 : word) = Some W_8cb08.
Proof. vm_refl. Qed.
Lemma D_8cb08 : decode_any W_8cb08 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb0c : bv 32 := 0x00113423.
Lemma F_8cb0c : fetch_word AsanUbsan.M.loaded_segments (0x8cb5c : word) = Some W_8cb0c.
Proof. vm_refl. Qed.
Lemma D_8cb0c : decode_any W_8cb0c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb10 : bv 32 := 0x00058693.
Lemma F_8cb10 : fetch_word AsanUbsan.M.loaded_segments (0x8cb60 : word) = Some W_8cb10.
Proof. vm_refl. Qed.
Lemma D_8cb10 : decode_any W_8cb10 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb14 : bv 32 := 0x00100713.
Lemma F_8cb14 : fetch_word AsanUbsan.M.loaded_segments (0x8cb64 : word) = Some W_8cb14.
Proof. vm_refl. Qed.
Lemma D_8cb14 : decode_any W_8cb14 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb18 : bv 32 := 0x02871713.
Lemma F_8cb18 : fetch_word AsanUbsan.M.loaded_segments (0x8cb68 : word) = Some W_8cb18.
Proof. vm_refl. Qed.
Lemma D_8cb18 : decode_any W_8cb18 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb1c : bv 32 := 0x00170593.
Lemma F_8cb1c : fetch_word AsanUbsan.M.loaded_segments (0x8cb6c : word) = Some W_8cb1c.
Proof. vm_refl. Qed.
Lemma D_8cb1c : decode_any W_8cb1c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb20 : bv 32 := 0x08b6f263.
Lemma F_8cb20 : fetch_word AsanUbsan.M.loaded_segments (0x8cb70 : word) = Some W_8cb20.
Proof. vm_refl. Qed.
Lemma D_8cb20 : decode_any W_8cb20 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb24 : bv 32 := 0x00000593.
Lemma F_8cb24 : fetch_word AsanUbsan.M.loaded_segments (0x8cb74 : word) = Some W_8cb24.
Proof. vm_refl. Qed.
Lemma D_8cb24 : decode_any W_8cb24 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb28 : bv 32 := 0x00d50733.
Lemma F_8cb28 : fetch_word AsanUbsan.M.loaded_segments (0x8cb78 : word) = Some W_8cb28.
Proof. vm_refl. Qed.
Lemma D_8cb28 : decode_any W_8cb28 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb2c : bv 32 := 0x00750793.
Lemma F_8cb2c : fetch_word AsanUbsan.M.loaded_segments (0x8cb7c : word) = Some W_8cb2c.
Proof. vm_refl. Qed.
Lemma D_8cb2c : decode_any W_8cb2c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb30 : bv 32 := 0xff87f793.
Lemma F_8cb30 : fetch_word AsanUbsan.M.loaded_segments (0x8cb80 : word) = Some W_8cb30.
Proof. vm_refl. Qed.
Lemma D_8cb30 : decode_any W_8cb30 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb34 : bv 32 := 0xff877613.
Lemma F_8cb34 : fetch_word AsanUbsan.M.loaded_segments (0x8cb84 : word) = Some W_8cb34.
Proof. vm_refl. Qed.
Lemma D_8cb34 : decode_any W_8cb34 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb38 : bv 32 := 0x02f57463.
Lemma F_8cb38 : fetch_word AsanUbsan.M.loaded_segments (0x8cb88 : word) = Some W_8cb38.
Proof. vm_refl. Qed.
Lemma D_8cb38 : decode_any W_8cb38 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb3c : bv 32 := 0x02068263.
Lemma F_8cb3c : fetch_word AsanUbsan.M.loaded_segments (0x8cb8c : word) = Some W_8cb3c.
Proof. vm_refl. Qed.
Lemma D_8cb3c : decode_any W_8cb3c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb40 : bv 32 := 0x00000593.
Lemma F_8cb40 : fetch_word AsanUbsan.M.loaded_segments (0x8cb90 : word) = Some W_8cb40.
Proof. vm_refl. Qed.
Lemma D_8cb40 : decode_any W_8cb40 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb44 : bv 32 := 0x00150693.
Lemma F_8cb44 : fetch_word AsanUbsan.M.loaded_segments (0x8cb94 : word) = Some W_8cb44.
Proof. vm_refl. Qed.
Lemma D_8cb44 : decode_any W_8cb44 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb48 : bv 32 := 0x00068813.
Lemma F_8cb48 : fetch_word AsanUbsan.M.loaded_segments (0x8cb98 : word) = Some W_8cb48.
Proof. vm_refl. Qed.
Lemma D_8cb48 : decode_any W_8cb48 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb4c : bv 32 := 0xfff6c683.
Lemma F_8cb4c : fetch_word AsanUbsan.M.loaded_segments (0x8cb9c : word) = Some W_8cb4c.
Proof. vm_refl. Qed.
Lemma D_8cb4c : decode_any W_8cb4c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb50 : bv 32 := 0x00d5e5b3.
Lemma F_8cb50 : fetch_word AsanUbsan.M.loaded_segments (0x8cba0 : word) = Some W_8cb50.
Proof. vm_refl. Qed.
Lemma D_8cb50 : decode_any W_8cb50 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb54 : bv 32 := 0x00f87663.
Lemma F_8cb54 : fetch_word AsanUbsan.M.loaded_segments (0x8cba4 : word) = Some W_8cb54.
Proof. vm_refl. Qed.
Lemma D_8cb54 : decode_any W_8cb54 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb58 : bv 32 := 0x00180693.
Lemma F_8cb58 : fetch_word AsanUbsan.M.loaded_segments (0x8cba8 : word) = Some W_8cb58.
Proof. vm_refl. Qed.
Lemma D_8cb58 : decode_any W_8cb58 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb5c : bv 32 := 0xfee866e3.
Lemma F_8cb5c : fetch_word AsanUbsan.M.loaded_segments (0x8cbac : word) = Some W_8cb5c.
Proof. vm_refl. Qed.
Lemma D_8cb5c : decode_any W_8cb5c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb60 : bv 32 := 0x00c7fa63.
Lemma F_8cb60 : fetch_word AsanUbsan.M.loaded_segments (0x8cbb0 : word) = Some W_8cb60.
Proof. vm_refl. Qed.
Lemma D_8cb60 : decode_any W_8cb60 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb64 : bv 32 := 0x0007b683.
Lemma F_8cb64 : fetch_word AsanUbsan.M.loaded_segments (0x8cbb4 : word) = Some W_8cb64.
Proof. vm_refl. Qed.
Lemma D_8cb64 : decode_any W_8cb64 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb68 : bv 32 := 0x00878793.
Lemma F_8cb68 : fetch_word AsanUbsan.M.loaded_segments (0x8cbb8 : word) = Some W_8cb68.
Proof. vm_refl. Qed.
Lemma D_8cb68 : decode_any W_8cb68 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb6c : bv 32 := 0x00b6e5b3.
Lemma F_8cb6c : fetch_word AsanUbsan.M.loaded_segments (0x8cbbc : word) = Some W_8cb6c.
Proof. vm_refl. Qed.
Lemma D_8cb6c : decode_any W_8cb6c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb70 : bv 32 := 0xfec7eae3.
Lemma F_8cb70 : fetch_word AsanUbsan.M.loaded_segments (0x8cbc0 : word) = Some W_8cb70.
Proof. vm_refl. Qed.
Lemma D_8cb70 : decode_any W_8cb70 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb74 : bv 32 := 0x02a66063.
Lemma F_8cb74 : fetch_word AsanUbsan.M.loaded_segments (0x8cbc4 : word) = Some W_8cb74.
Proof. vm_refl. Qed.
Lemma D_8cb74 : decode_any W_8cb74 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb78 : bv 32 := 0x00e67e63.
Lemma F_8cb78 : fetch_word AsanUbsan.M.loaded_segments (0x8cbc8 : word) = Some W_8cb78.
Proof. vm_refl. Qed.
Lemma D_8cb78 : decode_any W_8cb78 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb7c : bv 32 := 0x40c70733.
Lemma F_8cb7c : fetch_word AsanUbsan.M.loaded_segments (0x8cbcc : word) = Some W_8cb7c.
Proof. vm_refl. Qed.
Lemma D_8cb7c : decode_any W_8cb7c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb80 : bv 32 := 0x00064503.
Lemma F_8cb80 : fetch_word AsanUbsan.M.loaded_segments (0x8cbd0 : word) = Some W_8cb80.
Proof. vm_refl. Qed.
Lemma D_8cb80 : decode_any W_8cb80 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb84 : bv 32 := 0xfff70713.
Lemma F_8cb84 : fetch_word AsanUbsan.M.loaded_segments (0x8cbd4 : word) = Some W_8cb84.
Proof. vm_refl. Qed.
Lemma D_8cb84 : decode_any W_8cb84 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb88 : bv 32 := 0x00a5e5b3.
Lemma F_8cb88 : fetch_word AsanUbsan.M.loaded_segments (0x8cbd8 : word) = Some W_8cb88.
Proof. vm_refl. Qed.
Lemma D_8cb88 : decode_any W_8cb88 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb8c : bv 32 := 0x00160613.
Lemma F_8cb8c : fetch_word AsanUbsan.M.loaded_segments (0x8cbdc : word) = Some W_8cb8c.
Proof. vm_refl. Qed.
Lemma D_8cb8c : decode_any W_8cb8c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb90 : bv 32 := 0xfe0718e3.
Lemma F_8cb90 : fetch_word AsanUbsan.M.loaded_segments (0x8cbe0 : word) = Some W_8cb90.
Proof. vm_refl. Qed.
Lemma D_8cb90 : decode_any W_8cb90 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb94 : bv 32 := 0x0015b513.
Lemma F_8cb94 : fetch_word AsanUbsan.M.loaded_segments (0x8cbe4 : word) = Some W_8cb94.
Proof. vm_refl. Qed.
Lemma D_8cb94 : decode_any W_8cb94 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb98 : bv 32 := 0x00813083.
Lemma F_8cb98 : fetch_word AsanUbsan.M.loaded_segments (0x8cbe8 : word) = Some W_8cb98.
Proof. vm_refl. Qed.
Lemma D_8cb98 : decode_any W_8cb98 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cb9c : bv 32 := 0x01010113.
Lemma F_8cb9c : fetch_word AsanUbsan.M.loaded_segments (0x8cbec : word) = Some W_8cb9c.
Proof. vm_refl. Qed.
Lemma D_8cb9c : decode_any W_8cb9c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cba0 : bv 32 := 0x00008067.
Lemma F_8cba0 : fetch_word AsanUbsan.M.loaded_segments (0x8cbf0 : word) = Some W_8cba0.
Proof. vm_refl. Qed.
Lemma D_8cba0 : decode_any W_8cba0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
