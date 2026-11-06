(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
Module AsanAIM_codeK.
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

Definition W_81a58 : bv 32 := 0xfff48693.
Lemma F_81a58 : fetch_word Asan.M.loaded_segments (0x81aa8 : word) = Some W_81a58.
Proof. vm_refl. Qed.
Lemma D_81a58 : decode_any W_81a58 = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a5c : bv 32 := 0x00d4b733.
Lemma F_81a5c : fetch_word Asan.M.loaded_segments (0x81aac : word) = Some W_81a5c.
Proof. vm_refl. Qed.
Lemma D_81a5c : decode_any W_81a5c = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a60 : bv 32 := 0xfff70713.
Lemma F_81a60 : fetch_word Asan.M.loaded_segments (0x81ab0 : word) = Some W_81a60.
Proof. vm_refl. Qed.
Lemma D_81a60 : decode_any W_81a60 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a64 : bv 32 := 0x00d77733.
Lemma F_81a64 : fetch_word Asan.M.loaded_segments (0x81ab4 : word) = Some W_81a64.
Proof. vm_refl. Qed.
Lemma D_81a64 : decode_any W_81a64 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a68 : bv 32 := 0x1ca77c63.
Lemma F_81a68 : fetch_word Asan.M.loaded_segments (0x81ab8 : word) = Some W_81a68.
Proof. vm_refl. Qed.
Lemma D_81a68 : decode_any W_81a68 = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a6c : bv 32 := 0x000d5797.
Lemma F_81a6c : fetch_word Asan.M.loaded_segments (0x81abc : word) = Some W_81a6c.
Proof. vm_refl. Qed.
Lemma D_81a6c : decode_any W_81a6c = Some (Auipc 15 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a70 : bv 32 := 0x2e47b783.
Lemma F_81a70 : fetch_word Asan.M.loaded_segments (0x81ac0 : word) = Some W_81a70.
Proof. vm_refl. Qed.
Lemma D_81a70 : decode_any W_81a70 = Some (Load SZ8 true 15 15 740, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a74 : bv 32 := 0x000d5817.
Lemma F_81a74 : fetch_word Asan.M.loaded_segments (0x81ac4 : word) = Some W_81a74.
Proof. vm_refl. Qed.
Lemma D_81a74 : decode_any W_81a74 = Some (Auipc 16 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a78 : bv 32 := 0x2e483803.
Lemma F_81a78 : fetch_word Asan.M.loaded_segments (0x81ac8 : word) = Some W_81a78.
Proof. vm_refl. Qed.
Lemma D_81a78 : decode_any W_81a78 = Some (Load SZ8 true 16 16 740, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a7c : bv 32 := 0x0007b883.
Lemma F_81a7c : fetch_word Asan.M.loaded_segments (0x81acc : word) = Some W_81a7c.
Proof. vm_refl. Qed.
Lemma D_81a7c : decode_any W_81a7c = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a80 : bv 32 := 0x00083783.
Lemma F_81a80 : fetch_word Asan.M.loaded_segments (0x81ad0 : word) = Some W_81a80.
Proof. vm_refl. Qed.
Lemma D_81a80 : decode_any W_81a80 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a84 : bv 32 := 0xfff88813.
Lemma F_81a84 : fetch_word Asan.M.loaded_segments (0x81ad4 : word) = Some W_81a84.
Proof. vm_refl. Qed.
Lemma D_81a84 : decode_any W_81a84 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a88 : bv 32 := 0x00a87463.
Lemma F_81a88 : fetch_word Asan.M.loaded_segments (0x81ad8 : word) = Some W_81a88.
Proof. vm_refl. Qed.
Lemma D_81a88 : decode_any W_81a88 = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a8c : bv 32 := 0x1aa7fa63.
Lemma F_81a8c : fetch_word Asan.M.loaded_segments (0x81adc : word) = Some W_81a8c.
Proof. vm_refl. Qed.
Lemma D_81a8c : decode_any W_81a8c = Some (Branch BC_GEU 15 10 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a90 : bv 32 := 0x000d5297.
Lemma F_81a90 : fetch_word Asan.M.loaded_segments (0x81ae0 : word) = Some W_81a90.
Proof. vm_refl. Qed.
Lemma D_81a90 : decode_any W_81a90 = Some (Auipc 5 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a94 : bv 32 := 0x2d02b283.
Lemma F_81a94 : fetch_word Asan.M.loaded_segments (0x81ae4 : word) = Some W_81a94.
Proof. vm_refl. Qed.
Lemma D_81a94 : decode_any W_81a94 = Some (Load SZ8 true 5 5 720, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a98 : bv 32 := 0x0002be03.
Lemma F_81a98 : fetch_word Asan.M.loaded_segments (0x81ae8 : word) = Some W_81a98.
Proof. vm_refl. Qed.
Lemma D_81a98 : decode_any W_81a98 = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a9c : bv 32 := 0x003e5313.
Lemma F_81a9c : fetch_word Asan.M.loaded_segments (0x81aec : word) = Some W_81a9c.
Proof. vm_refl. Qed.
Lemma D_81a9c : decode_any W_81a9c = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81aa0 : bv 32 := 0x009303b3.
Lemma F_81aa0 : fetch_word Asan.M.loaded_segments (0x81af0 : word) = Some W_81aa0.
Proof. vm_refl. Qed.
Lemma D_81aa0 : decode_any W_81aa0 = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81aa4 : bv 32 := 0x00ae6463.
Lemma F_81aa4 : fetch_word Asan.M.loaded_segments (0x81af4 : word) = Some W_81aa4.
Proof. vm_refl. Qed.
Lemma D_81aa4 : decode_any W_81aa4 = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81aa8 : bv 32 := 0x0ca3e463.
Lemma F_81aa8 : fetch_word Asan.M.loaded_segments (0x81af8 : word) = Some W_81aa8.
Proof. vm_refl. Qed.
Lemma D_81aa8 : decode_any W_81aa8 = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_81aac : bv 32 := 0x000d5e17.
Lemma F_81aac : fetch_word Asan.M.loaded_segments (0x81afc : word) = Some W_81aac.
Proof. vm_refl. Qed.
Lemma D_81aac : decode_any W_81aac = Some (Auipc 28 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ab0 : bv 32 := 0x294e3e03.
Lemma F_81ab0 : fetch_word Asan.M.loaded_segments (0x81b00 : word) = Some W_81ab0.
Proof. vm_refl. Qed.
Lemma D_81ab0 : decode_any W_81ab0 = Some (Load SZ8 true 28 28 660, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ab4 : bv 32 := 0x04ee4e03.
Lemma F_81ab4 : fetch_word Asan.M.loaded_segments (0x81b04 : word) = Some W_81ab4.
Proof. vm_refl. Qed.
Lemma D_81ab4 : decode_any W_81ab4 = Some (Load SZ1 false 28 28 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ab8 : bv 32 := 0x3e0e1063.
Lemma F_81ab8 : fetch_word Asan.M.loaded_segments (0x81b08 : word) = Some W_81ab8.
Proof. vm_refl. Qed.
Lemma D_81ab8 : decode_any W_81ab8 = Some (Branch BC_NE 28 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_81abc : bv 32 := 0x04088e63.
Lemma F_81abc : fetch_word Asan.M.loaded_segments (0x81b0c : word) = Some W_81abc.
Proof. vm_refl. Qed.
Lemma D_81abc : decode_any W_81abc = Some (Branch BC_EQ 17 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ac0 : bv 32 := 0x0038d393.
Lemma F_81ac0 : fetch_word Asan.M.loaded_segments (0x81b10 : word) = Some W_81ac0.
Proof. vm_refl. Qed.
Lemma D_81ac0 : decode_any W_81ac0 = Some (ShiftImm ALU_SRL 7 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ac4 : bv 32 := 0x00d383b3.
Lemma F_81ac4 : fetch_word Asan.M.loaded_segments (0x81b14 : word) = Some W_81ac4.
Proof. vm_refl. Qed.
Lemma D_81ac4 : decode_any W_81ac4 = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ac8 : bv 32 := 0x06a3fe63.
Lemma F_81ac8 : fetch_word Asan.M.loaded_segments (0x81b18 : word) = Some W_81ac8.
Proof. vm_refl. Qed.
Lemma D_81ac8 : decode_any W_81ac8 = Some (Branch BC_GEU 7 10 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_81acc : bv 32 := 0x00148393.
Lemma F_81acc : fetch_word Asan.M.loaded_segments (0x81b1c : word) = Some W_81acc.
Proof. vm_refl. Qed.
Lemma D_81acc : decode_any W_81acc = Some (OpImm ALU_ADD 7 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ad0 : bv 32 := 0x00a86863.
Lemma F_81ad0 : fetch_word Asan.M.loaded_segments (0x81b20 : word) = Some W_81ad0.
Proof. vm_refl. Qed.
Lemma D_81ad0 : decode_any W_81ad0 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ad4 : bv 32 := 0x0037de13.
Lemma F_81ad4 : fetch_word Asan.M.loaded_segments (0x81b24 : word) = Some W_81ad4.
Proof. vm_refl. Qed.
Lemma D_81ad4 : decode_any W_81ad4 = Some (ShiftImm ALU_SRL 28 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ad8 : bv 32 := 0x007e0e33.
Lemma F_81ad8 : fetch_word Asan.M.loaded_segments (0x81b28 : word) = Some W_81ad8.
Proof. vm_refl. Qed.
Lemma D_81ad8 : decode_any W_81ad8 = Some (Op ALU_ADD 28 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_81adc : bv 32 := 0x09c57a63.
Lemma F_81adc : fetch_word Asan.M.loaded_segments (0x81b2c : word) = Some W_81adc.
Proof. vm_refl. Qed.
Lemma D_81adc : decode_any W_81adc = Some (Branch BC_GEU 10 28 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ae0 : bv 32 := 0x00178e13.
Lemma F_81ae0 : fetch_word Asan.M.loaded_segments (0x81b30 : word) = Some W_81ae0.
Proof. vm_refl. Qed.
Lemma D_81ae0 : decode_any W_81ae0 = Some (OpImm ALU_ADD 28 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ae4 : bv 32 := 0x3bc56a63.
Lemma F_81ae4 : fetch_word Asan.M.loaded_segments (0x81b34 : word) = Some W_81ae4.
Proof. vm_refl. Qed.
Lemma D_81ae4 : decode_any W_81ae4 = Some (Branch BC_LTU 10 28 948, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ae8 : bv 32 := 0x00730333.
Lemma F_81ae8 : fetch_word Asan.M.loaded_segments (0x81b38 : word) = Some W_81ae8.
Proof. vm_refl. Qed.
Lemma D_81ae8 : decode_any W_81ae8 = Some (Op ALU_ADD 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_81aec : bv 32 := 0x00335313.
Lemma F_81aec : fetch_word Asan.M.loaded_segments (0x81b3c : word) = Some W_81aec.
Proof. vm_refl. Qed.
Lemma D_81aec : decode_any W_81aec = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81af0 : bv 32 := 0x0480006f.
Lemma F_81af0 : fetch_word Asan.M.loaded_segments (0x81b40 : word) = Some W_81af0.
Proof. vm_refl. Qed.
Lemma D_81af0 : decode_any W_81af0 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_81af4 : bv 32 := 0x03813083.
Lemma F_81af4 : fetch_word Asan.M.loaded_segments (0x81b44 : word) = Some W_81af4.
Proof. vm_refl. Qed.
Lemma D_81af4 : decode_any W_81af4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81af8 : bv 32 := 0x03013403.
Lemma F_81af8 : fetch_word Asan.M.loaded_segments (0x81b48 : word) = Some W_81af8.
Proof. vm_refl. Qed.
Lemma D_81af8 : decode_any W_81af8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_81afc : bv 32 := 0x02813483.
Lemma F_81afc : fetch_word Asan.M.loaded_segments (0x81b4c : word) = Some W_81afc.
Proof. vm_refl. Qed.
Lemma D_81afc : decode_any W_81afc = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b00 : bv 32 := 0x02013903.
Lemma F_81b00 : fetch_word Asan.M.loaded_segments (0x81b50 : word) = Some W_81b00.
Proof. vm_refl. Qed.
Lemma D_81b00 : decode_any W_81b00 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b04 : bv 32 := 0x01813983.
Lemma F_81b04 : fetch_word Asan.M.loaded_segments (0x81b54 : word) = Some W_81b04.
Proof. vm_refl. Qed.
Lemma D_81b04 : decode_any W_81b04 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b08 : bv 32 := 0x01013a03.
Lemma F_81b08 : fetch_word Asan.M.loaded_segments (0x81b58 : word) = Some W_81b08.
Proof. vm_refl. Qed.
Lemma D_81b08 : decode_any W_81b08 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b0c : bv 32 := 0x00813a83.
Lemma F_81b0c : fetch_word Asan.M.loaded_segments (0x81b5c : word) = Some W_81b0c.
Proof. vm_refl. Qed.
Lemma D_81b0c : decode_any W_81b0c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b10 : bv 32 := 0x04010113.
Lemma F_81b10 : fetch_word Asan.M.loaded_segments (0x81b60 : word) = Some W_81b10.
Proof. vm_refl. Qed.
Lemma D_81b10 : decode_any W_81b10 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b14 : bv 32 := 0x00008067.
Lemma F_81b14 : fetch_word Asan.M.loaded_segments (0x81b64 : word) = Some W_81b14.
Proof. vm_refl. Qed.
Lemma D_81b14 : decode_any W_81b14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b18 : bv 32 := 0x04048463.
Lemma F_81b18 : fetch_word Asan.M.loaded_segments (0x81b68 : word) = Some W_81b18.
Proof. vm_refl. Qed.
Lemma D_81b18 : decode_any W_81b18 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b1c : bv 32 := 0x0036d313.
Lemma F_81b1c : fetch_word Asan.M.loaded_segments (0x81b6c : word) = Some W_81b1c.
Proof. vm_refl. Qed.
Lemma D_81b1c : decode_any W_81b1c = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b20 : bv 32 := 0x00930333.
Lemma F_81b20 : fetch_word Asan.M.loaded_segments (0x81b70 : word) = Some W_81b20.
Proof. vm_refl. Qed.
Lemma D_81b20 : decode_any W_81b20 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b24 : bv 32 := 0x00030663.
Lemma F_81b24 : fetch_word Asan.M.loaded_segments (0x81b74 : word) = Some W_81b24.
Proof. vm_refl. Qed.
Lemma D_81b24 : decode_any W_81b24 = Some (Branch BC_EQ 6 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b28 : bv 32 := 0x00130313.
Lemma F_81b28 : fetch_word Asan.M.loaded_segments (0x81b78 : word) = Some W_81b28.
Proof. vm_refl. Qed.
Lemma D_81b28 : decode_any W_81b28 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b2c : bv 32 := 0x36656663.
Lemma F_81b2c : fetch_word Asan.M.loaded_segments (0x81b7c : word) = Some W_81b2c.
Proof. vm_refl. Qed.
Lemma D_81b2c : decode_any W_81b2c = Some (Branch BC_LTU 10 6 876, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b30 : bv 32 := 0x00138393.
Lemma F_81b30 : fetch_word Asan.M.loaded_segments (0x81b80 : word) = Some W_81b30.
Proof. vm_refl. Qed.
Lemma D_81b30 : decode_any W_81b30 = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b34 : bv 32 := 0x0033d313.
Lemma F_81b34 : fetch_word Asan.M.loaded_segments (0x81b84 : word) = Some W_81b34.
Proof. vm_refl. Qed.
Lemma D_81b34 : decode_any W_81b34 = Some (ShiftImm ALU_SRL 6 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b38 : bv 32 := 0x00d30333.
Lemma F_81b38 : fetch_word Asan.M.loaded_segments (0x81b88 : word) = Some W_81b38.
Proof. vm_refl. Qed.
Lemma D_81b38 : decode_any W_81b38 = Some (Op ALU_ADD 6 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b3c : bv 32 := 0x02a37a63.
Lemma F_81b3c : fetch_word Asan.M.loaded_segments (0x81b8c : word) = Some W_81b3c.
Proof. vm_refl. Qed.
Lemma D_81b3c : decode_any W_81b3c = Some (Branch BC_GEU 6 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b40 : bv 32 := 0x3580006f.
Lemma F_81b40 : fetch_word Asan.M.loaded_segments (0x81b90 : word) = Some W_81b40.
Proof. vm_refl. Qed.
Lemma D_81b40 : decode_any W_81b40 = Some (Jal 0 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b44 : bv 32 := 0x02048663.
Lemma F_81b44 : fetch_word Asan.M.loaded_segments (0x81b94 : word) = Some W_81b44.
Proof. vm_refl. Qed.
Lemma D_81b44 : decode_any W_81b44 = Some (Branch BC_EQ 9 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b48 : bv 32 := 0x0036d313.
Lemma F_81b48 : fetch_word Asan.M.loaded_segments (0x81b98 : word) = Some W_81b48.
Proof. vm_refl. Qed.
Lemma D_81b48 : decode_any W_81b48 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b4c : bv 32 := 0x00930333.
Lemma F_81b4c : fetch_word Asan.M.loaded_segments (0x81b9c : word) = Some W_81b4c.
Proof. vm_refl. Qed.
Lemma D_81b4c : decode_any W_81b4c = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b50 : bv 32 := 0x02030063.
Lemma F_81b50 : fetch_word Asan.M.loaded_segments (0x81ba0 : word) = Some W_81b50.
Proof. vm_refl. Qed.
Lemma D_81b50 : decode_any W_81b50 = Some (Branch BC_EQ 6 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b54 : bv 32 := 0x00130313.
Lemma F_81b54 : fetch_word Asan.M.loaded_segments (0x81ba4 : word) = Some W_81b54.
Proof. vm_refl. Qed.
Lemma D_81b54 : decode_any W_81b54 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b58 : bv 32 := 0x00657c63.
Lemma F_81b58 : fetch_word Asan.M.loaded_segments (0x81ba8 : word) = Some W_81b58.
Proof. vm_refl. Qed.
Lemma D_81b58 : decode_any W_81b58 = Some (Branch BC_GEU 10 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b5c : bv 32 := 0x33c0006f.
Lemma F_81b5c : fetch_word Asan.M.loaded_segments (0x81bac : word) = Some W_81b5c.
Proof. vm_refl. Qed.
Lemma D_81b5c : decode_any W_81b5c = Some (Jal 0 828, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b60 : bv 32 := 0x00130313.
Lemma F_81b60 : fetch_word Asan.M.loaded_segments (0x81bb0 : word) = Some W_81b60.
Proof. vm_refl. Qed.
Lemma D_81b60 : decode_any W_81b60 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b64 : bv 32 := 0x00335313.
Lemma F_81b64 : fetch_word Asan.M.loaded_segments (0x81bb4 : word) = Some W_81b64.
Proof. vm_refl. Qed.
Lemma D_81b64 : decode_any W_81b64 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b68 : bv 32 := 0xfff30313.
Lemma F_81b68 : fetch_word Asan.M.loaded_segments (0x81bb8 : word) = Some W_81b68.
Proof. vm_refl. Qed.
Lemma D_81b68 : decode_any W_81b68 = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b6c : bv 32 := 0x32a36663.
Lemma F_81b6c : fetch_word Asan.M.loaded_segments (0x81bbc : word) = Some W_81b6c.
Proof. vm_refl. Qed.
Lemma D_81b6c : decode_any W_81b6c = Some (Branch BC_LTU 6 10 812, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b70 : bv 32 := 0x0002b383.
Lemma F_81b70 : fetch_word Asan.M.loaded_segments (0x81bc0 : word) = Some W_81b70.
Proof. vm_refl. Qed.
Lemma D_81b70 : decode_any W_81b70 = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b74 : bv 32 := 0x0033d293.
Lemma F_81b74 : fetch_word Asan.M.loaded_segments (0x81bc4 : word) = Some W_81b74.
Proof. vm_refl. Qed.
Lemma D_81b74 : decode_any W_81b74 = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b78 : bv 32 := 0x00928333.
Lemma F_81b78 : fetch_word Asan.M.loaded_segments (0x81bc8 : word) = Some W_81b78.
Proof. vm_refl. Qed.
Lemma D_81b78 : decode_any W_81b78 = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b7c : bv 32 := 0x00a3e463.
Lemma F_81b7c : fetch_word Asan.M.loaded_segments (0x81bcc : word) = Some W_81b7c.
Proof. vm_refl. Qed.
Lemma D_81b7c : decode_any W_81b7c = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b80 : bv 32 := 0x0ca36063.
Lemma F_81b80 : fetch_word Asan.M.loaded_segments (0x81bd0 : word) = Some W_81b80.
Proof. vm_refl. Qed.
Lemma D_81b80 : decode_any W_81b80 = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b84 : bv 32 := 0x000d5397.
Lemma F_81b84 : fetch_word Asan.M.loaded_segments (0x81bd4 : word) = Some W_81b84.
Proof. vm_refl. Qed.
Lemma D_81b84 : decode_any W_81b84 = Some (Auipc 7 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b88 : bv 32 := 0x1bc3b383.
Lemma F_81b88 : fetch_word Asan.M.loaded_segments (0x81bd8 : word) = Some W_81b88.
Proof. vm_refl. Qed.
Lemma D_81b88 : decode_any W_81b88 = Some (Load SZ8 true 7 7 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b8c : bv 32 := 0x04e3c383.
Lemma F_81b8c : fetch_word Asan.M.loaded_segments (0x81bdc : word) = Some W_81b8c.
Proof. vm_refl. Qed.
Lemma D_81b8c : decode_any W_81b8c = Some (Load SZ1 false 7 7 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b90 : bv 32 := 0x08039063.
Lemma F_81b90 : fetch_word Asan.M.loaded_segments (0x81be0 : word) = Some W_81b90.
Proof. vm_refl. Qed.
Lemma D_81b90 : decode_any W_81b90 = Some (Branch BC_NE 7 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b94 : bv 32 := 0x02088c63.
Lemma F_81b94 : fetch_word Asan.M.loaded_segments (0x81be4 : word) = Some W_81b94.
Proof. vm_refl. Qed.
Lemma D_81b94 : decode_any W_81b94 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b98 : bv 32 := 0x0038d893.
Lemma F_81b98 : fetch_word Asan.M.loaded_segments (0x81be8 : word) = Some W_81b98.
Proof. vm_refl. Qed.
Lemma D_81b98 : decode_any W_81b98 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b9c : bv 32 := 0x00d888b3.
Lemma F_81b9c : fetch_word Asan.M.loaded_segments (0x81bec : word) = Some W_81b9c.
Proof. vm_refl. Qed.
Lemma D_81b9c : decode_any W_81b9c = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ba0 : bv 32 := 0x04a8fc63.
Lemma F_81ba0 : fetch_word Asan.M.loaded_segments (0x81bf0 : word) = Some W_81ba0.
Proof. vm_refl. Qed.
Lemma D_81ba0 : decode_any W_81ba0 = Some (Branch BC_GEU 17 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ba4 : bv 32 := 0x00148893.
Lemma F_81ba4 : fetch_word Asan.M.loaded_segments (0x81bf4 : word) = Some W_81ba4.
Proof. vm_refl. Qed.
Lemma D_81ba4 : decode_any W_81ba4 = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ba8 : bv 32 := 0x00a86863.
Lemma F_81ba8 : fetch_word Asan.M.loaded_segments (0x81bf8 : word) = Some W_81ba8.
Proof. vm_refl. Qed.
Lemma D_81ba8 : decode_any W_81ba8 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bac : bv 32 := 0x0037d813.
Lemma F_81bac : fetch_word Asan.M.loaded_segments (0x81bfc : word) = Some W_81bac.
Proof. vm_refl. Qed.
Lemma D_81bac : decode_any W_81bac = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bb0 : bv 32 := 0x01180833.
Lemma F_81bb0 : fetch_word Asan.M.loaded_segments (0x81c00 : word) = Some W_81bb0.
Proof. vm_refl. Qed.
Lemma D_81bb0 : decode_any W_81bb0 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bb4 : bv 32 := 0x09057663.
Lemma F_81bb4 : fetch_word Asan.M.loaded_segments (0x81c04 : word) = Some W_81bb4.
Proof. vm_refl. Qed.
Lemma D_81bb4 : decode_any W_81bb4 = Some (Branch BC_GEU 10 16 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bb8 : bv 32 := 0x00178793.
Lemma F_81bb8 : fetch_word Asan.M.loaded_segments (0x81c08 : word) = Some W_81bb8.
Proof. vm_refl. Qed.
Lemma D_81bb8 : decode_any W_81bb8 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bbc : bv 32 := 0x04f56a63.
Lemma F_81bbc : fetch_word Asan.M.loaded_segments (0x81c0c : word) = Some W_81bbc.
Proof. vm_refl. Qed.
Lemma D_81bbc : decode_any W_81bbc = Some (Branch BC_LTU 10 15 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bc0 : bv 32 := 0x011288b3.
Lemma F_81bc0 : fetch_word Asan.M.loaded_segments (0x81c10 : word) = Some W_81bc0.
Proof. vm_refl. Qed.
Lemma D_81bc0 : decode_any W_81bc0 = Some (Op ALU_ADD 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bc4 : bv 32 := 0x0038d793.
Lemma F_81bc4 : fetch_word Asan.M.loaded_segments (0x81c14 : word) = Some W_81bc4.
Proof. vm_refl. Qed.
Lemma D_81bc4 : decode_any W_81bc4 = Some (ShiftImm ALU_SRL 15 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bc8 : bv 32 := 0x0240006f.
Lemma F_81bc8 : fetch_word Asan.M.loaded_segments (0x81c18 : word) = Some W_81bc8.
Proof. vm_refl. Qed.
Lemma D_81bc8 : decode_any W_81bc8 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bcc : bv 32 := 0x06048263.
Lemma F_81bcc : fetch_word Asan.M.loaded_segments (0x81c1c : word) = Some W_81bcc.
Proof. vm_refl. Qed.
Lemma D_81bcc : decode_any W_81bcc = Some (Branch BC_EQ 9 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bd0 : bv 32 := 0x0036d793.
Lemma F_81bd0 : fetch_word Asan.M.loaded_segments (0x81c20 : word) = Some W_81bd0.
Proof. vm_refl. Qed.
Lemma D_81bd0 : decode_any W_81bd0 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bd4 : bv 32 := 0x009787b3.
Lemma F_81bd4 : fetch_word Asan.M.loaded_segments (0x81c24 : word) = Some W_81bd4.
Proof. vm_refl. Qed.
Lemma D_81bd4 : decode_any W_81bd4 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bd8 : bv 32 := 0x00078663.
Lemma F_81bd8 : fetch_word Asan.M.loaded_segments (0x81c28 : word) = Some W_81bd8.
Proof. vm_refl. Qed.
Lemma D_81bd8 : decode_any W_81bd8 = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bdc : bv 32 := 0x00178793.
Lemma F_81bdc : fetch_word Asan.M.loaded_segments (0x81c2c : word) = Some W_81bdc.
Proof. vm_refl. Qed.
Lemma D_81bdc : decode_any W_81bdc = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81be0 : bv 32 := 0x02f56863.
Lemma F_81be0 : fetch_word Asan.M.loaded_segments (0x81c30 : word) = Some W_81be0.
Proof. vm_refl. Qed.
Lemma D_81be0 : decode_any W_81be0 = Some (Branch BC_LTU 10 15 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_81be4 : bv 32 := 0x00130313.
Lemma F_81be4 : fetch_word Asan.M.loaded_segments (0x81c34 : word) = Some W_81be4.
Proof. vm_refl. Qed.
Lemma D_81be4 : decode_any W_81be4 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81be8 : bv 32 := 0x00335793.
Lemma F_81be8 : fetch_word Asan.M.loaded_segments (0x81c38 : word) = Some W_81be8.
Proof. vm_refl. Qed.
Lemma D_81be8 : decode_any W_81be8 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bec : bv 32 := 0x00d787b3.
Lemma F_81bec : fetch_word Asan.M.loaded_segments (0x81c3c : word) = Some W_81bec.
Proof. vm_refl. Qed.
Lemma D_81bec : decode_any W_81bec = Some (Op ALU_ADD 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bf0 : bv 32 := 0x04a7f863.
Lemma F_81bf0 : fetch_word Asan.M.loaded_segments (0x81c40 : word) = Some W_81bf0.
Proof. vm_refl. Qed.
Lemma D_81bf0 : decode_any W_81bf0 = Some (Branch BC_GEU 15 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bf4 : bv 32 := 0x01c0006f.
Lemma F_81bf4 : fetch_word Asan.M.loaded_segments (0x81c44 : word) = Some W_81bf4.
Proof. vm_refl. Qed.
Lemma D_81bf4 : decode_any W_81bf4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bf8 : bv 32 := 0x04048463.
Lemma F_81bf8 : fetch_word Asan.M.loaded_segments (0x81c48 : word) = Some W_81bf8.
Proof. vm_refl. Qed.
Lemma D_81bf8 : decode_any W_81bf8 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bfc : bv 32 := 0x0036d793.
Lemma F_81bfc : fetch_word Asan.M.loaded_segments (0x81c4c : word) = Some W_81bfc.
Proof. vm_refl. Qed.
Lemma D_81bfc : decode_any W_81bfc = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c00 : bv 32 := 0x009787b3.
Lemma F_81c00 : fetch_word Asan.M.loaded_segments (0x81c50 : word) = Some W_81c00.
Proof. vm_refl. Qed.
Lemma D_81c00 : decode_any W_81c00 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c04 : bv 32 := 0x02078e63.
Lemma F_81c04 : fetch_word Asan.M.loaded_segments (0x81c54 : word) = Some W_81c04.
Proof. vm_refl. Qed.
Lemma D_81c04 : decode_any W_81c04 = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c08 : bv 32 := 0x00178793.
Lemma F_81c08 : fetch_word Asan.M.loaded_segments (0x81c58 : word) = Some W_81c08.
Proof. vm_refl. Qed.
Lemma D_81c08 : decode_any W_81c08 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c0c : bv 32 := 0x02f57a63.
Lemma F_81c0c : fetch_word Asan.M.loaded_segments (0x81c5c : word) = Some W_81c0c.
Proof. vm_refl. Qed.
Lemma D_81c0c : decode_any W_81c0c = Some (Branch BC_GEU 10 15 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c10 : bv 32 := 0xfffa0517.
Lemma F_81c10 : fetch_word Asan.M.loaded_segments (0x81c60 : word) = Some W_81c10.
Proof. vm_refl. Qed.
Lemma D_81c10 : decode_any W_81c10 = Some (Auipc 10 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c14 : bv 32 := 0xfff97597.
Lemma F_81c14 : fetch_word Asan.M.loaded_segments (0x81c64 : word) = Some W_81c14.
Proof. vm_refl. Qed.
Lemma D_81c14 : decode_any W_81c14 = Some (Auipc 11 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c18 : bv 32 := 0xdf150513.
Lemma F_81c18 : fetch_word Asan.M.loaded_segments (0x81c68 : word) = Some W_81c18.
Proof. vm_refl. Qed.
Lemma D_81c18 : decode_any W_81c18 = Some (OpImm ALU_ADD 10 10 3569, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c1c : bv 32 := 0xf9958613.
Lemma F_81c1c : fetch_word Asan.M.loaded_segments (0x81c6c : word) = Some W_81c1c.
Proof. vm_refl. Qed.
Lemma D_81c1c : decode_any W_81c1c = Some (OpImm ALU_ADD 12 11 3993, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c20 : bv 32 := 0x02f00593.
Lemma F_81c20 : fetch_word Asan.M.loaded_segments (0x81c70 : word) = Some W_81c20.
Proof. vm_refl. Qed.
Lemma D_81c20 : decode_any W_81c20 = Some (OpImm ALU_ADD 11 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c24 : bv 32 := 0x00000693.
Lemma F_81c24 : fetch_word Asan.M.loaded_segments (0x81c74 : word) = Some W_81c24.
Proof. vm_refl. Qed.
Lemma D_81c24 : decode_any W_81c24 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c28 : bv 32 := 0x00000713.
Lemma F_81c28 : fetch_word Asan.M.loaded_segments (0x81c78 : word) = Some W_81c28.
Proof. vm_refl. Qed.
Lemma D_81c28 : decode_any W_81c28 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c2c : bv 32 := 0x430180ef.
Lemma F_81c2c : fetch_word Asan.M.loaded_segments (0x81c7c : word) = Some W_81c2c.
Proof. vm_refl. Qed.
Lemma D_81c2c : decode_any W_81c2c = Some (Jal 1 99376, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c30 : bv 32 := 0x00128293.
Lemma F_81c30 : fetch_word Asan.M.loaded_segments (0x81c80 : word) = Some W_81c30.
Proof. vm_refl. Qed.
Lemma D_81c30 : decode_any W_81c30 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c34 : bv 32 := 0x0032d793.
Lemma F_81c34 : fetch_word Asan.M.loaded_segments (0x81c84 : word) = Some W_81c34.
Proof. vm_refl. Qed.
Lemma D_81c34 : decode_any W_81c34 = Some (ShiftImm ALU_SRL 15 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c38 : bv 32 := 0xfff78793.
Lemma F_81c38 : fetch_word Asan.M.loaded_segments (0x81c88 : word) = Some W_81c38.
Proof. vm_refl. Qed.
Lemma D_81c38 : decode_any W_81c38 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c3c : bv 32 := 0xfca7eae3.
Lemma F_81c3c : fetch_word Asan.M.loaded_segments (0x81c8c : word) = Some W_81c3c.
Proof. vm_refl. Qed.
Lemma D_81c3c : decode_any W_81c3c = Some (Branch BC_LTU 15 10 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c40 : bv 32 := 0x0075f793.
Lemma F_81c40 : fetch_word Asan.M.loaded_segments (0x81c90 : word) = Some W_81c40.
Proof. vm_refl. Qed.
Lemma D_81c40 : decode_any W_81c40 = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c44 : bv 32 := 0x26079a63.
Lemma F_81c44 : fetch_word Asan.M.loaded_segments (0x81c94 : word) = Some W_81c44.
Proof. vm_refl. Qed.
Lemma D_81c44 : decode_any W_81c44 = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c48 : bv 32 := 0x00b505b3.
Lemma F_81c48 : fetch_word Asan.M.loaded_segments (0x81c98 : word) = Some W_81c48.
Proof. vm_refl. Qed.
Lemma D_81c48 : decode_any W_81c48 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c4c : bv 32 := 0xff858593.
Lemma F_81c4c : fetch_word Asan.M.loaded_segments (0x81c9c : word) = Some W_81c4c.
Proof. vm_refl. Qed.
Lemma D_81c4c : decode_any W_81c4c = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c50 : bv 32 := 0x04b77263.
Lemma F_81c50 : fetch_word Asan.M.loaded_segments (0x81ca0 : word) = Some W_81c50.
Proof. vm_refl. Qed.
Lemma D_81c50 : decode_any W_81c50 = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c54 : bv 32 := 0x000d5717.
Lemma F_81c54 : fetch_word Asan.M.loaded_segments (0x81ca4 : word) = Some W_81c54.
Proof. vm_refl. Qed.
Lemma D_81c54 : decode_any W_81c54 = Some (Auipc 14 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c58 : bv 32 := 0x0fc73703.
Lemma F_81c58 : fetch_word Asan.M.loaded_segments (0x81ca8 : word) = Some W_81c58.
Proof. vm_refl. Qed.
Lemma D_81c58 : decode_any W_81c58 = Some (Load SZ8 true 14 14 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c5c : bv 32 := 0x000d5797.
Lemma F_81c5c : fetch_word Asan.M.loaded_segments (0x81cac : word) = Some W_81c5c.
Proof. vm_refl. Qed.
Lemma D_81c5c : decode_any W_81c5c = Some (Auipc 15 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c60 : bv 32 := 0x0fc7b783.
Lemma F_81c60 : fetch_word Asan.M.loaded_segments (0x81cb0 : word) = Some W_81c60.
Proof. vm_refl. Qed.
Lemma D_81c60 : decode_any W_81c60 = Some (Load SZ8 true 15 15 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c64 : bv 32 := 0x00073883.
Lemma F_81c64 : fetch_word Asan.M.loaded_segments (0x81cb4 : word) = Some W_81c64.
Proof. vm_refl. Qed.
Lemma D_81c64 : decode_any W_81c64 = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c68 : bv 32 := 0x0007b703.
Lemma F_81c68 : fetch_word Asan.M.loaded_segments (0x81cb8 : word) = Some W_81c68.
Proof. vm_refl. Qed.
Lemma D_81c68 : decode_any W_81c68 = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c6c : bv 32 := 0xfff88813.
Lemma F_81c6c : fetch_word Asan.M.loaded_segments (0x81cbc : word) = Some W_81c6c.
Proof. vm_refl. Qed.
Lemma D_81c6c : decode_any W_81c6c = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c70 : bv 32 := 0x00b87463.
Lemma F_81c70 : fetch_word Asan.M.loaded_segments (0x81cc0 : word) = Some W_81c70.
Proof. vm_refl. Qed.
Lemma D_81c70 : decode_any W_81c70 = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c74 : bv 32 := 0x02b77063.
Lemma F_81c74 : fetch_word Asan.M.loaded_segments (0x81cc4 : word) = Some W_81c74.
Proof. vm_refl. Qed.
Lemma D_81c74 : decode_any W_81c74 = Some (Branch BC_GEU 14 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c78 : bv 32 := 0x000d5797.
Lemma F_81c78 : fetch_word Asan.M.loaded_segments (0x81cc8 : word) = Some W_81c78.
Proof. vm_refl. Qed.
Lemma D_81c78 : decode_any W_81c78 = Some (Auipc 15 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c7c : bv 32 := 0x0e87b783.
Lemma F_81c7c : fetch_word Asan.M.loaded_segments (0x81ccc : word) = Some W_81c7c.
Proof. vm_refl. Qed.
Lemma D_81c7c : decode_any W_81c7c = Some (Load SZ8 true 15 15 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c80 : bv 32 := 0x0007b303.
Lemma F_81c80 : fetch_word Asan.M.loaded_segments (0x81cd0 : word) = Some W_81c80.
Proof. vm_refl. Qed.
Lemma D_81c80 : decode_any W_81c80 = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c84 : bv 32 := 0x00335793.
Lemma F_81c84 : fetch_word Asan.M.loaded_segments (0x81cd4 : word) = Some W_81c84.
Proof. vm_refl. Qed.
Lemma D_81c84 : decode_any W_81c84 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c88 : bv 32 := 0x009782b3.
Lemma F_81c88 : fetch_word Asan.M.loaded_segments (0x81cd8 : word) = Some W_81c88.
Proof. vm_refl. Qed.
Lemma D_81c88 : decode_any W_81c88 = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c8c : bv 32 := 0x12b36263.
Lemma F_81c8c : fetch_word Asan.M.loaded_segments (0x81cdc : word) = Some W_81c8c.
Proof. vm_refl. Qed.
Lemma D_81c8c : decode_any W_81c8c = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c90 : bv 32 := 0x12b2f063.
Lemma F_81c90 : fetch_word Asan.M.loaded_segments (0x81ce0 : word) = Some W_81c90.
Proof. vm_refl. Qed.
Lemma D_81c90 : decode_any W_81c90 = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c94 : bv 32 := 0x000d5697.
Lemma F_81c94 : fetch_word Asan.M.loaded_segments (0x81ce4 : word) = Some W_81c94.
Proof. vm_refl. Qed.
Lemma D_81c94 : decode_any W_81c94 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

End AsanAIM_codeK.
Module AsanMaxVA_codeK.
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

Definition W_9399c : bv 32 := 0x00155593.
Lemma F_9399c : fetch_word Asan.M.loaded_segments (0x939ec : word) = Some W_9399c.
Proof. vm_refl. Qed.
Lemma D_9399c : decode_any W_9399c = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_939a0 : bv 32 := 0x55555637.
Lemma F_939a0 : fetch_word Asan.M.loaded_segments (0x939f0 : word) = Some W_939a0.
Proof. vm_refl. Qed.
Lemma D_939a0 : decode_any W_939a0 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_939a4 : bv 32 := 0x333336b7.
Lemma F_939a4 : fetch_word Asan.M.loaded_segments (0x939f4 : word) = Some W_939a4.
Proof. vm_refl. Qed.
Lemma D_939a4 : decode_any W_939a4 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_939a8 : bv 32 := 0x0f0f1737.
Lemma F_939a8 : fetch_word Asan.M.loaded_segments (0x939f8 : word) = Some W_939a8.
Proof. vm_refl. Qed.
Lemma D_939a8 : decode_any W_939a8 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_939ac : bv 32 := 0x010107b7.
Lemma F_939ac : fetch_word Asan.M.loaded_segments (0x939fc : word) = Some W_939ac.
Proof. vm_refl. Qed.
Lemma D_939ac : decode_any W_939ac = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_939b0 : bv 32 := 0x00b56533.
Lemma F_939b0 : fetch_word Asan.M.loaded_segments (0x93a00 : word) = Some W_939b0.
Proof. vm_refl. Qed.
Lemma D_939b0 : decode_any W_939b0 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_939b4 : bv 32 := 0x5556059b.
Lemma F_939b4 : fetch_word Asan.M.loaded_segments (0x93a04 : word) = Some W_939b4.
Proof. vm_refl. Qed.
Lemma D_939b4 : decode_any W_939b4 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_939b8 : bv 32 := 0x3336861b.
Lemma F_939b8 : fetch_word Asan.M.loaded_segments (0x93a08 : word) = Some W_939b8.
Proof. vm_refl. Qed.
Lemma D_939b8 : decode_any W_939b8 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_939bc : bv 32 := 0xf0f7069b.
Lemma F_939bc : fetch_word Asan.M.loaded_segments (0x93a0c : word) = Some W_939bc.
Proof. vm_refl. Qed.
Lemma D_939bc : decode_any W_939bc = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_939c0 : bv 32 := 0x1017871b.
Lemma F_939c0 : fetch_word Asan.M.loaded_segments (0x93a10 : word) = Some W_939c0.
Proof. vm_refl. Qed.
Lemma D_939c0 : decode_any W_939c0 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_939c4 : bv 32 := 0x00255793.
Lemma F_939c4 : fetch_word Asan.M.loaded_segments (0x93a14 : word) = Some W_939c4.
Proof. vm_refl. Qed.
Lemma D_939c4 : decode_any W_939c4 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_939c8 : bv 32 := 0x00f56533.
Lemma F_939c8 : fetch_word Asan.M.loaded_segments (0x93a18 : word) = Some W_939c8.
Proof. vm_refl. Qed.
Lemma D_939c8 : decode_any W_939c8 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_939cc : bv 32 := 0x02059793.
Lemma F_939cc : fetch_word Asan.M.loaded_segments (0x93a1c : word) = Some W_939cc.
Proof. vm_refl. Qed.
Lemma D_939cc : decode_any W_939cc = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_939d0 : bv 32 := 0x00f585b3.
Lemma F_939d0 : fetch_word Asan.M.loaded_segments (0x93a20 : word) = Some W_939d0.
Proof. vm_refl. Qed.
Lemma D_939d0 : decode_any W_939d0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_939d4 : bv 32 := 0x02061793.
Lemma F_939d4 : fetch_word Asan.M.loaded_segments (0x93a24 : word) = Some W_939d4.
Proof. vm_refl. Qed.
Lemma D_939d4 : decode_any W_939d4 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_939d8 : bv 32 := 0x00f60633.
Lemma F_939d8 : fetch_word Asan.M.loaded_segments (0x93a28 : word) = Some W_939d8.
Proof. vm_refl. Qed.
Lemma D_939d8 : decode_any W_939d8 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_939dc : bv 32 := 0x02069793.
Lemma F_939dc : fetch_word Asan.M.loaded_segments (0x93a2c : word) = Some W_939dc.
Proof. vm_refl. Qed.
Lemma D_939dc : decode_any W_939dc = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_939e0 : bv 32 := 0x00f686b3.
Lemma F_939e0 : fetch_word Asan.M.loaded_segments (0x93a30 : word) = Some W_939e0.
Proof. vm_refl. Qed.
Lemma D_939e0 : decode_any W_939e0 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_939e4 : bv 32 := 0x02071793.
Lemma F_939e4 : fetch_word Asan.M.loaded_segments (0x93a34 : word) = Some W_939e4.
Proof. vm_refl. Qed.
Lemma D_939e4 : decode_any W_939e4 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_939e8 : bv 32 := 0x00f70733.
Lemma F_939e8 : fetch_word Asan.M.loaded_segments (0x93a38 : word) = Some W_939e8.
Proof. vm_refl. Qed.
Lemma D_939e8 : decode_any W_939e8 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_939ec : bv 32 := 0x00455793.
Lemma F_939ec : fetch_word Asan.M.loaded_segments (0x93a3c : word) = Some W_939ec.
Proof. vm_refl. Qed.
Lemma D_939ec : decode_any W_939ec = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_939f0 : bv 32 := 0x00f56533.
Lemma F_939f0 : fetch_word Asan.M.loaded_segments (0x93a40 : word) = Some W_939f0.
Proof. vm_refl. Qed.
Lemma D_939f0 : decode_any W_939f0 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_939f4 : bv 32 := 0x00855793.
Lemma F_939f4 : fetch_word Asan.M.loaded_segments (0x93a44 : word) = Some W_939f4.
Proof. vm_refl. Qed.
Lemma D_939f4 : decode_any W_939f4 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_939f8 : bv 32 := 0x00f56533.
Lemma F_939f8 : fetch_word Asan.M.loaded_segments (0x93a48 : word) = Some W_939f8.
Proof. vm_refl. Qed.
Lemma D_939f8 : decode_any W_939f8 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_939fc : bv 32 := 0x01055793.
Lemma F_939fc : fetch_word Asan.M.loaded_segments (0x93a4c : word) = Some W_939fc.
Proof. vm_refl. Qed.
Lemma D_939fc : decode_any W_939fc = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a00 : bv 32 := 0x00f56533.
Lemma F_93a00 : fetch_word Asan.M.loaded_segments (0x93a50 : word) = Some W_93a00.
Proof. vm_refl. Qed.
Lemma D_93a00 : decode_any W_93a00 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a04 : bv 32 := 0x02055793.
Lemma F_93a04 : fetch_word Asan.M.loaded_segments (0x93a54 : word) = Some W_93a04.
Proof. vm_refl. Qed.
Lemma D_93a04 : decode_any W_93a04 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a08 : bv 32 := 0x00f56533.
Lemma F_93a08 : fetch_word Asan.M.loaded_segments (0x93a58 : word) = Some W_93a08.
Proof. vm_refl. Qed.
Lemma D_93a08 : decode_any W_93a08 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a0c : bv 32 := 0xfff54513.
Lemma F_93a0c : fetch_word Asan.M.loaded_segments (0x93a5c : word) = Some W_93a0c.
Proof. vm_refl. Qed.
Lemma D_93a0c : decode_any W_93a0c = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a10 : bv 32 := 0x00155793.
Lemma F_93a10 : fetch_word Asan.M.loaded_segments (0x93a60 : word) = Some W_93a10.
Proof. vm_refl. Qed.
Lemma D_93a10 : decode_any W_93a10 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a14 : bv 32 := 0x00b7f5b3.
Lemma F_93a14 : fetch_word Asan.M.loaded_segments (0x93a64 : word) = Some W_93a14.
Proof. vm_refl. Qed.
Lemma D_93a14 : decode_any W_93a14 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a18 : bv 32 := 0x40b50533.
Lemma F_93a18 : fetch_word Asan.M.loaded_segments (0x93a68 : word) = Some W_93a18.
Proof. vm_refl. Qed.
Lemma D_93a18 : decode_any W_93a18 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a1c : bv 32 := 0x00c575b3.
Lemma F_93a1c : fetch_word Asan.M.loaded_segments (0x93a6c : word) = Some W_93a1c.
Proof. vm_refl. Qed.
Lemma D_93a1c : decode_any W_93a1c = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a20 : bv 32 := 0x00255513.
Lemma F_93a20 : fetch_word Asan.M.loaded_segments (0x93a70 : word) = Some W_93a20.
Proof. vm_refl. Qed.
Lemma D_93a20 : decode_any W_93a20 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a24 : bv 32 := 0x00c57533.
Lemma F_93a24 : fetch_word Asan.M.loaded_segments (0x93a74 : word) = Some W_93a24.
Proof. vm_refl. Qed.
Lemma D_93a24 : decode_any W_93a24 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a28 : bv 32 := 0x00a58533.
Lemma F_93a28 : fetch_word Asan.M.loaded_segments (0x93a78 : word) = Some W_93a28.
Proof. vm_refl. Qed.
Lemma D_93a28 : decode_any W_93a28 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a2c : bv 32 := 0x00455593.
Lemma F_93a2c : fetch_word Asan.M.loaded_segments (0x93a7c : word) = Some W_93a2c.
Proof. vm_refl. Qed.
Lemma D_93a2c : decode_any W_93a2c = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a30 : bv 32 := 0x00b50533.
Lemma F_93a30 : fetch_word Asan.M.loaded_segments (0x93a80 : word) = Some W_93a30.
Proof. vm_refl. Qed.
Lemma D_93a30 : decode_any W_93a30 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a34 : bv 32 := 0x00d57533.
Lemma F_93a34 : fetch_word Asan.M.loaded_segments (0x93a84 : word) = Some W_93a34.
Proof. vm_refl. Qed.
Lemma D_93a34 : decode_any W_93a34 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a38 : bv 32 := 0x02e50533.
Lemma F_93a38 : fetch_word Asan.M.loaded_segments (0x93a88 : word) = Some W_93a38.
Proof. vm_refl. Qed.
Lemma D_93a38 : decode_any W_93a38 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a3c : bv 32 := 0x03855513.
Lemma F_93a3c : fetch_word Asan.M.loaded_segments (0x93a8c : word) = Some W_93a3c.
Proof. vm_refl. Qed.
Lemma D_93a3c : decode_any W_93a3c = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a40 : bv 32 := 0x40a0053b.
Lemma F_93a40 : fetch_word Asan.M.loaded_segments (0x93a90 : word) = Some W_93a40.
Proof. vm_refl. Qed.
Lemma D_93a40 : decode_any W_93a40 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a44 : bv 32 := 0xfff00593.
Lemma F_93a44 : fetch_word Asan.M.loaded_segments (0x93a94 : word) = Some W_93a44.
Proof. vm_refl. Qed.
Lemma D_93a44 : decode_any W_93a44 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a48 : bv 32 := 0x00a59533.
Lemma F_93a48 : fetch_word Asan.M.loaded_segments (0x93a98 : word) = Some W_93a48.
Proof. vm_refl. Qed.
Lemma D_93a48 : decode_any W_93a48 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_93a4c : bv 32 := 0xfff54513.
Lemma F_93a4c : fetch_word Asan.M.loaded_segments (0x93a9c : word) = Some W_93a4c.
Proof. vm_refl. Qed.
Lemma D_93a4c : decode_any W_93a4c = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

End AsanMaxVA_codeK.
Module Asan_code_memcpyK.
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

Definition W_148d24 : bv 32 := 0x0035f693.
Lemma F_148d24 : fetch_word Asan.M.loaded_segments (0x148d68 : word) = Some W_148d24.
Proof. vm_refl. Qed.
Lemma D_148d24 : decode_any W_148d24 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d28 : bv 32 := 0x10068863.
Lemma F_148d28 : fetch_word Asan.M.loaded_segments (0x148d6c : word) = Some W_148d28.
Proof. vm_refl. Qed.
Lemma D_148d28 : decode_any W_148d28 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d2c : bv 32 := 0x02060e63.
Lemma F_148d2c : fetch_word Asan.M.loaded_segments (0x148d70 : word) = Some W_148d2c.
Proof. vm_refl. Qed.
Lemma D_148d2c : decode_any W_148d2c = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d30 : bv 32 := 0x00158713.
Lemma F_148d30 : fetch_word Asan.M.loaded_segments (0x148d74 : word) = Some W_148d30.
Proof. vm_refl. Qed.
Lemma D_148d30 : decode_any W_148d30 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d34 : bv 32 := 0x00100793.
Lemma F_148d34 : fetch_word Asan.M.loaded_segments (0x148d78 : word) = Some W_148d34.
Proof. vm_refl. Qed.
Lemma D_148d34 : decode_any W_148d34 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d38 : bv 32 := 0x00050693.
Lemma F_148d38 : fetch_word Asan.M.loaded_segments (0x148d7c : word) = Some W_148d38.
Proof. vm_refl. Qed.
Lemma D_148d38 : decode_any W_148d38 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d3c : bv 32 := 0x0005c883.
Lemma F_148d3c : fetch_word Asan.M.loaded_segments (0x148d80 : word) = Some W_148d3c.
Proof. vm_refl. Qed.
Lemma D_148d3c : decode_any W_148d3c = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d40 : bv 32 := 0x00060813.
Lemma F_148d40 : fetch_word Asan.M.loaded_segments (0x148d84 : word) = Some W_148d40.
Proof. vm_refl. Qed.
Lemma D_148d40 : decode_any W_148d40 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d44 : bv 32 := 0x00158593.
Lemma F_148d44 : fetch_word Asan.M.loaded_segments (0x148d88 : word) = Some W_148d44.
Proof. vm_refl. Qed.
Lemma D_148d44 : decode_any W_148d44 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d48 : bv 32 := 0x00377293.
Lemma F_148d48 : fetch_word Asan.M.loaded_segments (0x148d8c : word) = Some W_148d48.
Proof. vm_refl. Qed.
Lemma D_148d48 : decode_any W_148d48 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d4c : bv 32 := 0x01168023.
Lemma F_148d4c : fetch_word Asan.M.loaded_segments (0x148d90 : word) = Some W_148d4c.
Proof. vm_refl. Qed.
Lemma D_148d4c : decode_any W_148d4c = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d50 : bv 32 := 0x00168693.
Lemma F_148d50 : fetch_word Asan.M.loaded_segments (0x148d94 : word) = Some W_148d50.
Proof. vm_refl. Qed.
Lemma D_148d50 : decode_any W_148d50 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d54 : bv 32 := 0xfff60613.
Lemma F_148d54 : fetch_word Asan.M.loaded_segments (0x148d98 : word) = Some W_148d54.
Proof. vm_refl. Qed.
Lemma D_148d54 : decode_any W_148d54 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d58 : bv 32 := 0x00028a63.
Lemma F_148d58 : fetch_word Asan.M.loaded_segments (0x148d9c : word) = Some W_148d58.
Proof. vm_refl. Qed.
Lemma D_148d58 : decode_any W_148d58 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d5c : bv 32 := 0x00170713.
Lemma F_148d5c : fetch_word Asan.M.loaded_segments (0x148da0 : word) = Some W_148d5c.
Proof. vm_refl. Qed.
Lemma D_148d5c : decode_any W_148d5c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d60 : bv 32 := 0xfcf81ee3.
Lemma F_148d60 : fetch_word Asan.M.loaded_segments (0x148da4 : word) = Some W_148d60.
Proof. vm_refl. Qed.
Lemma D_148d60 : decode_any W_148d60 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d64 : bv 32 := 0x0080006f.
Lemma F_148d64 : fetch_word Asan.M.loaded_segments (0x148da8 : word) = Some W_148d64.
Proof. vm_refl. Qed.
Lemma D_148d64 : decode_any W_148d64 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d68 : bv 32 := 0x00050693.
Lemma F_148d68 : fetch_word Asan.M.loaded_segments (0x148dac : word) = Some W_148d68.
Proof. vm_refl. Qed.
Lemma D_148d68 : decode_any W_148d68 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d6c : bv 32 := 0x0036f793.
Lemma F_148d6c : fetch_word Asan.M.loaded_segments (0x148db0 : word) = Some W_148d6c.
Proof. vm_refl. Qed.
Lemma D_148d6c : decode_any W_148d6c = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d70 : bv 32 := 0x0c078a63.
Lemma F_148d70 : fetch_word Asan.M.loaded_segments (0x148db4 : word) = Some W_148d70.
Proof. vm_refl. Qed.
Lemma D_148d70 : decode_any W_148d70 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d74 : bv 32 := 0x02000713.
Lemma F_148d74 : fetch_word Asan.M.loaded_segments (0x148db8 : word) = Some W_148d74.
Proof. vm_refl. Qed.
Lemma D_148d74 : decode_any W_148d74 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d78 : bv 32 := 0x02e67063.
Lemma F_148d78 : fetch_word Asan.M.loaded_segments (0x148dbc : word) = Some W_148d78.
Proof. vm_refl. Qed.
Lemma D_148d78 : decode_any W_148d78 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d7c : bv 32 := 0x01000713.
Lemma F_148d7c : fetch_word Asan.M.loaded_segments (0x148dc0 : word) = Some W_148d7c.
Proof. vm_refl. Qed.
Lemma D_148d7c : decode_any W_148d7c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d80 : bv 32 := 0x24e67863.
Lemma F_148d80 : fetch_word Asan.M.loaded_segments (0x148dc4 : word) = Some W_148d80.
Proof. vm_refl. Qed.
Lemma D_148d80 : decode_any W_148d80 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d84 : bv 32 := 0x00867713.
Lemma F_148d84 : fetch_word Asan.M.loaded_segments (0x148dc8 : word) = Some W_148d84.
Proof. vm_refl. Qed.
Lemma D_148d84 : decode_any W_148d84 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d88 : bv 32 := 0x2c071e63.
Lemma F_148d88 : fetch_word Asan.M.loaded_segments (0x148dcc : word) = Some W_148d88.
Proof. vm_refl. Qed.
Lemma D_148d88 : decode_any W_148d88 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d8c : bv 32 := 0x00467713.
Lemma F_148d8c : fetch_word Asan.M.loaded_segments (0x148dd0 : word) = Some W_148d8c.
Proof. vm_refl. Qed.
Lemma D_148d8c : decode_any W_148d8c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d90 : bv 32 := 0x32071463.
Lemma F_148d90 : fetch_word Asan.M.loaded_segments (0x148dd4 : word) = Some W_148d90.
Proof. vm_refl. Qed.
Lemma D_148d90 : decode_any W_148d90 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d94 : bv 32 := 0x3500006f.
Lemma F_148d94 : fetch_word Asan.M.loaded_segments (0x148dd8 : word) = Some W_148d94.
Proof. vm_refl. Qed.
Lemma D_148d94 : decode_any W_148d94 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d98 : bv 32 := 0x0005a703.
Lemma F_148d98 : fetch_word Asan.M.loaded_segments (0x148ddc : word) = Some W_148d98.
Proof. vm_refl. Qed.
Lemma D_148d98 : decode_any W_148d98 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148d9c : bv 32 := 0x00300813.
Lemma F_148d9c : fetch_word Asan.M.loaded_segments (0x148de0 : word) = Some W_148d9c.
Proof. vm_refl. Qed.
Lemma D_148d9c : decode_any W_148d9c = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_148da0 : bv 32 := 0x11078e63.
Lemma F_148da0 : fetch_word Asan.M.loaded_segments (0x148de4 : word) = Some W_148da0.
Proof. vm_refl. Qed.
Lemma D_148da0 : decode_any W_148da0 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_148da4 : bv 32 := 0x00200813.
Lemma F_148da4 : fetch_word Asan.M.loaded_segments (0x148de8 : word) = Some W_148da4.
Proof. vm_refl. Qed.
Lemma D_148da4 : decode_any W_148da4 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_148da8 : bv 32 := 0x19079c63.
Lemma F_148da8 : fetch_word Asan.M.loaded_segments (0x148dec : word) = Some W_148da8.
Proof. vm_refl. Qed.
Lemma D_148da8 : decode_any W_148da8 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_148dac : bv 32 := 0x00875793.
Lemma F_148dac : fetch_word Asan.M.loaded_segments (0x148df0 : word) = Some W_148dac.
Proof. vm_refl. Qed.
Lemma D_148dac : decode_any W_148dac = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148db0 : bv 32 := 0xffe60613.
Lemma F_148db0 : fetch_word Asan.M.loaded_segments (0x148df4 : word) = Some W_148db0.
Proof. vm_refl. Qed.
Lemma D_148db0 : decode_any W_148db0 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_148db4 : bv 32 := 0x00e68023.
Lemma F_148db4 : fetch_word Asan.M.loaded_segments (0x148df8 : word) = Some W_148db4.
Proof. vm_refl. Qed.
Lemma D_148db4 : decode_any W_148db4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148db8 : bv 32 := 0x00f680a3.
Lemma F_148db8 : fetch_word Asan.M.loaded_segments (0x148dfc : word) = Some W_148db8.
Proof. vm_refl. Qed.
Lemma D_148db8 : decode_any W_148db8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_148dbc : bv 32 := 0x00268693.
Lemma F_148dbc : fetch_word Asan.M.loaded_segments (0x148e00 : word) = Some W_148dbc.
Proof. vm_refl. Qed.
Lemma D_148dbc : decode_any W_148dbc = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_148dc0 : bv 32 := 0x01058593.
Lemma F_148dc0 : fetch_word Asan.M.loaded_segments (0x148e04 : word) = Some W_148dc0.
Proof. vm_refl. Qed.
Lemma D_148dc0 : decode_any W_148dc0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148dc4 : bv 32 := 0x01100793.
Lemma F_148dc4 : fetch_word Asan.M.loaded_segments (0x148e08 : word) = Some W_148dc4.
Proof. vm_refl. Qed.
Lemma D_148dc4 : decode_any W_148dc4 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_148dc8 : bv 32 := 0x0107581b.
Lemma F_148dc8 : fetch_word Asan.M.loaded_segments (0x148e0c : word) = Some W_148dc8.
Proof. vm_refl. Qed.
Lemma D_148dc8 : decode_any W_148dc8 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148dcc : bv 32 := 0xff45a883.
Lemma F_148dcc : fetch_word Asan.M.loaded_segments (0x148e10 : word) = Some W_148dcc.
Proof. vm_refl. Qed.
Lemma D_148dcc : decode_any W_148dcc = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_148dd0 : bv 32 := 0xff85a283.
Lemma F_148dd0 : fetch_word Asan.M.loaded_segments (0x148e14 : word) = Some W_148dd0.
Proof. vm_refl. Qed.
Lemma D_148dd0 : decode_any W_148dd0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_148dd4 : bv 32 := 0xffc5a303.
Lemma F_148dd4 : fetch_word Asan.M.loaded_segments (0x148e18 : word) = Some W_148dd4.
Proof. vm_refl. Qed.
Lemma D_148dd4 : decode_any W_148dd4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_148dd8 : bv 32 := 0x0005a703.
Lemma F_148dd8 : fetch_word Asan.M.loaded_segments (0x148e1c : word) = Some W_148dd8.
Proof. vm_refl. Qed.
Lemma D_148dd8 : decode_any W_148dd8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ddc : bv 32 := 0x01089393.
Lemma F_148ddc : fetch_word Asan.M.loaded_segments (0x148e20 : word) = Some W_148ddc.
Proof. vm_refl. Qed.
Lemma D_148ddc : decode_any W_148ddc = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148de0 : bv 32 := 0x0108d89b.
Lemma F_148de0 : fetch_word Asan.M.loaded_segments (0x148e24 : word) = Some W_148de0.
Proof. vm_refl. Qed.
Lemma D_148de0 : decode_any W_148de0 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148de4 : bv 32 := 0x0103e833.
Lemma F_148de4 : fetch_word Asan.M.loaded_segments (0x148e28 : word) = Some W_148de4.
Proof. vm_refl. Qed.
Lemma D_148de4 : decode_any W_148de4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148de8 : bv 32 := 0x01029393.
Lemma F_148de8 : fetch_word Asan.M.loaded_segments (0x148e2c : word) = Some W_148de8.
Proof. vm_refl. Qed.
Lemma D_148de8 : decode_any W_148de8 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148dec : bv 32 := 0x0102d29b.
Lemma F_148dec : fetch_word Asan.M.loaded_segments (0x148e30 : word) = Some W_148dec.
Proof. vm_refl. Qed.
Lemma D_148dec : decode_any W_148dec = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148df0 : bv 32 := 0x0113e8b3.
Lemma F_148df0 : fetch_word Asan.M.loaded_segments (0x148e34 : word) = Some W_148df0.
Proof. vm_refl. Qed.
Lemma D_148df0 : decode_any W_148df0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_148df4 : bv 32 := 0x01031393.
Lemma F_148df4 : fetch_word Asan.M.loaded_segments (0x148e38 : word) = Some W_148df4.
Proof. vm_refl. Qed.
Lemma D_148df4 : decode_any W_148df4 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148df8 : bv 32 := 0x0103531b.
Lemma F_148df8 : fetch_word Asan.M.loaded_segments (0x148e3c : word) = Some W_148df8.
Proof. vm_refl. Qed.
Lemma D_148df8 : decode_any W_148df8 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148dfc : bv 32 := 0x0053e2b3.
Lemma F_148dfc : fetch_word Asan.M.loaded_segments (0x148e40 : word) = Some W_148dfc.
Proof. vm_refl. Qed.
Lemma D_148dfc : decode_any W_148dfc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e00 : bv 32 := 0x01071393.
Lemma F_148e00 : fetch_word Asan.M.loaded_segments (0x148e44 : word) = Some W_148e00.
Proof. vm_refl. Qed.
Lemma D_148e00 : decode_any W_148e00 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e04 : bv 32 := 0x0063e333.
Lemma F_148e04 : fetch_word Asan.M.loaded_segments (0x148e48 : word) = Some W_148e04.
Proof. vm_refl. Qed.
Lemma D_148e04 : decode_any W_148e04 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e08 : bv 32 := 0xff060613.
Lemma F_148e08 : fetch_word Asan.M.loaded_segments (0x148e4c : word) = Some W_148e08.
Proof. vm_refl. Qed.
Lemma D_148e08 : decode_any W_148e08 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e0c : bv 32 := 0x0106a023.
Lemma F_148e0c : fetch_word Asan.M.loaded_segments (0x148e50 : word) = Some W_148e0c.
Proof. vm_refl. Qed.
Lemma D_148e0c : decode_any W_148e0c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e10 : bv 32 := 0x0116a223.
Lemma F_148e10 : fetch_word Asan.M.loaded_segments (0x148e54 : word) = Some W_148e10.
Proof. vm_refl. Qed.
Lemma D_148e10 : decode_any W_148e10 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e14 : bv 32 := 0x0056a423.
Lemma F_148e14 : fetch_word Asan.M.loaded_segments (0x148e58 : word) = Some W_148e14.
Proof. vm_refl. Qed.
Lemma D_148e14 : decode_any W_148e14 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e18 : bv 32 := 0x0066a623.
Lemma F_148e18 : fetch_word Asan.M.loaded_segments (0x148e5c : word) = Some W_148e18.
Proof. vm_refl. Qed.
Lemma D_148e18 : decode_any W_148e18 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e1c : bv 32 := 0x01068693.
Lemma F_148e1c : fetch_word Asan.M.loaded_segments (0x148e60 : word) = Some W_148e1c.
Proof. vm_refl. Qed.
Lemma D_148e1c : decode_any W_148e1c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e20 : bv 32 := 0x01058593.
Lemma F_148e20 : fetch_word Asan.M.loaded_segments (0x148e64 : word) = Some W_148e20.
Proof. vm_refl. Qed.
Lemma D_148e20 : decode_any W_148e20 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e24 : bv 32 := 0xfac7e2e3.
Lemma F_148e24 : fetch_word Asan.M.loaded_segments (0x148e68 : word) = Some W_148e24.
Proof. vm_refl. Qed.
Lemma D_148e24 : decode_any W_148e24 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e28 : bv 32 := 0xff258593.
Lemma F_148e28 : fetch_word Asan.M.loaded_segments (0x148e6c : word) = Some W_148e28.
Proof. vm_refl. Qed.
Lemma D_148e28 : decode_any W_148e28 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e2c : bv 32 := 0x01000713.
Lemma F_148e2c : fetch_word Asan.M.loaded_segments (0x148e70 : word) = Some W_148e2c.
Proof. vm_refl. Qed.
Lemma D_148e2c : decode_any W_148e2c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e30 : bv 32 := 0xf4e66ae3.
Lemma F_148e30 : fetch_word Asan.M.loaded_segments (0x148e74 : word) = Some W_148e30.
Proof. vm_refl. Qed.
Lemma D_148e30 : decode_any W_148e30 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e34 : bv 32 := 0x19c0006f.
Lemma F_148e34 : fetch_word Asan.M.loaded_segments (0x148e78 : word) = Some W_148e34.
Proof. vm_refl. Qed.
Lemma D_148e34 : decode_any W_148e34 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e38 : bv 32 := 0x00050693.
Lemma F_148e38 : fetch_word Asan.M.loaded_segments (0x148e7c : word) = Some W_148e38.
Proof. vm_refl. Qed.
Lemma D_148e38 : decode_any W_148e38 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e3c : bv 32 := 0x00357793.
Lemma F_148e3c : fetch_word Asan.M.loaded_segments (0x148e80 : word) = Some W_148e3c.
Proof. vm_refl. Qed.
Lemma D_148e3c : decode_any W_148e3c = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e40 : bv 32 := 0xf2079ae3.
Lemma F_148e40 : fetch_word Asan.M.loaded_segments (0x148e84 : word) = Some W_148e40.
Proof. vm_refl. Qed.
Lemma D_148e40 : decode_any W_148e40 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e44 : bv 32 := 0x01000713.
Lemma F_148e44 : fetch_word Asan.M.loaded_segments (0x148e88 : word) = Some W_148e44.
Proof. vm_refl. Qed.
Lemma D_148e44 : decode_any W_148e44 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e48 : bv 32 := 0x02e66c63.
Lemma F_148e48 : fetch_word Asan.M.loaded_segments (0x148e8c : word) = Some W_148e48.
Proof. vm_refl. Qed.
Lemma D_148e48 : decode_any W_148e48 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e4c : bv 32 := 0x00f00713.
Lemma F_148e4c : fetch_word Asan.M.loaded_segments (0x148e90 : word) = Some W_148e4c.
Proof. vm_refl. Qed.
Lemma D_148e4c : decode_any W_148e4c = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e50 : bv 32 := 0x0005a783.
Lemma F_148e50 : fetch_word Asan.M.loaded_segments (0x148e94 : word) = Some W_148e50.
Proof. vm_refl. Qed.
Lemma D_148e50 : decode_any W_148e50 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e54 : bv 32 := 0x0045a803.
Lemma F_148e54 : fetch_word Asan.M.loaded_segments (0x148e98 : word) = Some W_148e54.
Proof. vm_refl. Qed.
Lemma D_148e54 : decode_any W_148e54 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e58 : bv 32 := 0x0085a883.
Lemma F_148e58 : fetch_word Asan.M.loaded_segments (0x148e9c : word) = Some W_148e58.
Proof. vm_refl. Qed.
Lemma D_148e58 : decode_any W_148e58 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e5c : bv 32 := 0x00c5a283.
Lemma F_148e5c : fetch_word Asan.M.loaded_segments (0x148ea0 : word) = Some W_148e5c.
Proof. vm_refl. Qed.
Lemma D_148e5c : decode_any W_148e5c = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e60 : bv 32 := 0x01058593.
Lemma F_148e60 : fetch_word Asan.M.loaded_segments (0x148ea4 : word) = Some W_148e60.
Proof. vm_refl. Qed.
Lemma D_148e60 : decode_any W_148e60 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e64 : bv 32 := 0xff060613.
Lemma F_148e64 : fetch_word Asan.M.loaded_segments (0x148ea8 : word) = Some W_148e64.
Proof. vm_refl. Qed.
Lemma D_148e64 : decode_any W_148e64 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e68 : bv 32 := 0x00f6a023.
Lemma F_148e68 : fetch_word Asan.M.loaded_segments (0x148eac : word) = Some W_148e68.
Proof. vm_refl. Qed.
Lemma D_148e68 : decode_any W_148e68 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e6c : bv 32 := 0x0106a223.
Lemma F_148e6c : fetch_word Asan.M.loaded_segments (0x148eb0 : word) = Some W_148e6c.
Proof. vm_refl. Qed.
Lemma D_148e6c : decode_any W_148e6c = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e70 : bv 32 := 0x0116a423.
Lemma F_148e70 : fetch_word Asan.M.loaded_segments (0x148eb4 : word) = Some W_148e70.
Proof. vm_refl. Qed.
Lemma D_148e70 : decode_any W_148e70 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e74 : bv 32 := 0x0056a623.
Lemma F_148e74 : fetch_word Asan.M.loaded_segments (0x148eb8 : word) = Some W_148e74.
Proof. vm_refl. Qed.
Lemma D_148e74 : decode_any W_148e74 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e78 : bv 32 := 0x01068693.
Lemma F_148e78 : fetch_word Asan.M.loaded_segments (0x148ebc : word) = Some W_148e78.
Proof. vm_refl. Qed.
Lemma D_148e78 : decode_any W_148e78 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e7c : bv 32 := 0xfcc76ae3.
Lemma F_148e7c : fetch_word Asan.M.loaded_segments (0x148ec0 : word) = Some W_148e7c.
Proof. vm_refl. Qed.
Lemma D_148e7c : decode_any W_148e7c = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e80 : bv 32 := 0x00800713.
Lemma F_148e80 : fetch_word Asan.M.loaded_segments (0x148ec4 : word) = Some W_148e80.
Proof. vm_refl. Qed.
Lemma D_148e80 : decode_any W_148e80 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e84 : bv 32 := 0x00e66e63.
Lemma F_148e84 : fetch_word Asan.M.loaded_segments (0x148ec8 : word) = Some W_148e84.
Proof. vm_refl. Qed.
Lemma D_148e84 : decode_any W_148e84 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e88 : bv 32 := 0x0005a703.
Lemma F_148e88 : fetch_word Asan.M.loaded_segments (0x148ecc : word) = Some W_148e88.
Proof. vm_refl. Qed.
Lemma D_148e88 : decode_any W_148e88 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e8c : bv 32 := 0x0045a783.
Lemma F_148e8c : fetch_word Asan.M.loaded_segments (0x148ed0 : word) = Some W_148e8c.
Proof. vm_refl. Qed.
Lemma D_148e8c : decode_any W_148e8c = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e90 : bv 32 := 0x00e6a023.
Lemma F_148e90 : fetch_word Asan.M.loaded_segments (0x148ed4 : word) = Some W_148e90.
Proof. vm_refl. Qed.
Lemma D_148e90 : decode_any W_148e90 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e94 : bv 32 := 0x00f6a223.
Lemma F_148e94 : fetch_word Asan.M.loaded_segments (0x148ed8 : word) = Some W_148e94.
Proof. vm_refl. Qed.
Lemma D_148e94 : decode_any W_148e94 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e98 : bv 32 := 0x00868693.
Lemma F_148e98 : fetch_word Asan.M.loaded_segments (0x148edc : word) = Some W_148e98.
Proof. vm_refl. Qed.
Lemma D_148e98 : decode_any W_148e98 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148e9c : bv 32 := 0x00858593.
Lemma F_148e9c : fetch_word Asan.M.loaded_segments (0x148ee0 : word) = Some W_148e9c.
Proof. vm_refl. Qed.
Lemma D_148e9c : decode_any W_148e9c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ea0 : bv 32 := 0x00467713.
Lemma F_148ea0 : fetch_word Asan.M.loaded_segments (0x148ee4 : word) = Some W_148ea0.
Proof. vm_refl. Qed.
Lemma D_148ea0 : decode_any W_148ea0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ea4 : bv 32 := 0x24070063.
Lemma F_148ea4 : fetch_word Asan.M.loaded_segments (0x148ee8 : word) = Some W_148ea4.
Proof. vm_refl. Qed.
Lemma D_148ea4 : decode_any W_148ea4 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ea8 : bv 32 := 0x0005a703.
Lemma F_148ea8 : fetch_word Asan.M.loaded_segments (0x148eec : word) = Some W_148ea8.
Proof. vm_refl. Qed.
Lemma D_148ea8 : decode_any W_148ea8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148eac : bv 32 := 0x00458593.
Lemma F_148eac : fetch_word Asan.M.loaded_segments (0x148ef0 : word) = Some W_148eac.
Proof. vm_refl. Qed.
Lemma D_148eac : decode_any W_148eac = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148eb0 : bv 32 := 0x00e6a023.
Lemma F_148eb0 : fetch_word Asan.M.loaded_segments (0x148ef4 : word) = Some W_148eb0.
Proof. vm_refl. Qed.
Lemma D_148eb0 : decode_any W_148eb0 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148eb4 : bv 32 := 0x00468693.
Lemma F_148eb4 : fetch_word Asan.M.loaded_segments (0x148ef8 : word) = Some W_148eb4.
Proof. vm_refl. Qed.
Lemma D_148eb4 : decode_any W_148eb4 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148eb8 : bv 32 := 0x22c0006f.
Lemma F_148eb8 : fetch_word Asan.M.loaded_segments (0x148efc : word) = Some W_148eb8.
Proof. vm_refl. Qed.
Lemma D_148eb8 : decode_any W_148eb8 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ebc : bv 32 := 0x00e68023.
Lemma F_148ebc : fetch_word Asan.M.loaded_segments (0x148f00 : word) = Some W_148ebc.
Proof. vm_refl. Qed.
Lemma D_148ebc : decode_any W_148ebc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ec0 : bv 32 := 0x00168693.
Lemma F_148ec0 : fetch_word Asan.M.loaded_segments (0x148f04 : word) = Some W_148ec0.
Proof. vm_refl. Qed.
Lemma D_148ec0 : decode_any W_148ec0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ec4 : bv 32 := 0xfff60613.
Lemma F_148ec4 : fetch_word Asan.M.loaded_segments (0x148f08 : word) = Some W_148ec4.
Proof. vm_refl. Qed.
Lemma D_148ec4 : decode_any W_148ec4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ec8 : bv 32 := 0x01058593.
Lemma F_148ec8 : fetch_word Asan.M.loaded_segments (0x148f0c : word) = Some W_148ec8.
Proof. vm_refl. Qed.
Lemma D_148ec8 : decode_any W_148ec8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ecc : bv 32 := 0x01200793.
Lemma F_148ecc : fetch_word Asan.M.loaded_segments (0x148f10 : word) = Some W_148ecc.
Proof. vm_refl. Qed.
Lemma D_148ecc : decode_any W_148ecc = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ed0 : bv 32 := 0x0087581b.
Lemma F_148ed0 : fetch_word Asan.M.loaded_segments (0x148f14 : word) = Some W_148ed0.
Proof. vm_refl. Qed.
Lemma D_148ed0 : decode_any W_148ed0 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ed4 : bv 32 := 0xff45a883.
Lemma F_148ed4 : fetch_word Asan.M.loaded_segments (0x148f18 : word) = Some W_148ed4.
Proof. vm_refl. Qed.
Lemma D_148ed4 : decode_any W_148ed4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ed8 : bv 32 := 0xff85a283.
Lemma F_148ed8 : fetch_word Asan.M.loaded_segments (0x148f1c : word) = Some W_148ed8.
Proof. vm_refl. Qed.
Lemma D_148ed8 : decode_any W_148ed8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_148edc : bv 32 := 0xffc5a303.
Lemma F_148edc : fetch_word Asan.M.loaded_segments (0x148f20 : word) = Some W_148edc.
Proof. vm_refl. Qed.
Lemma D_148edc : decode_any W_148edc = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ee0 : bv 32 := 0x0005a703.
Lemma F_148ee0 : fetch_word Asan.M.loaded_segments (0x148f24 : word) = Some W_148ee0.
Proof. vm_refl. Qed.
Lemma D_148ee0 : decode_any W_148ee0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ee4 : bv 32 := 0x01889393.
Lemma F_148ee4 : fetch_word Asan.M.loaded_segments (0x148f28 : word) = Some W_148ee4.
Proof. vm_refl. Qed.
Lemma D_148ee4 : decode_any W_148ee4 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ee8 : bv 32 := 0x0088d89b.
Lemma F_148ee8 : fetch_word Asan.M.loaded_segments (0x148f2c : word) = Some W_148ee8.
Proof. vm_refl. Qed.
Lemma D_148ee8 : decode_any W_148ee8 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148eec : bv 32 := 0x0103e833.
Lemma F_148eec : fetch_word Asan.M.loaded_segments (0x148f30 : word) = Some W_148eec.
Proof. vm_refl. Qed.
Lemma D_148eec : decode_any W_148eec = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ef0 : bv 32 := 0x01829393.
Lemma F_148ef0 : fetch_word Asan.M.loaded_segments (0x148f34 : word) = Some W_148ef0.
Proof. vm_refl. Qed.
Lemma D_148ef0 : decode_any W_148ef0 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ef4 : bv 32 := 0x0082d29b.
Lemma F_148ef4 : fetch_word Asan.M.loaded_segments (0x148f38 : word) = Some W_148ef4.
Proof. vm_refl. Qed.
Lemma D_148ef4 : decode_any W_148ef4 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ef8 : bv 32 := 0x0113e8b3.
Lemma F_148ef8 : fetch_word Asan.M.loaded_segments (0x148f3c : word) = Some W_148ef8.
Proof. vm_refl. Qed.
Lemma D_148ef8 : decode_any W_148ef8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_148efc : bv 32 := 0x01831393.
Lemma F_148efc : fetch_word Asan.M.loaded_segments (0x148f40 : word) = Some W_148efc.
Proof. vm_refl. Qed.
Lemma D_148efc : decode_any W_148efc = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f00 : bv 32 := 0x0083531b.
Lemma F_148f00 : fetch_word Asan.M.loaded_segments (0x148f44 : word) = Some W_148f00.
Proof. vm_refl. Qed.
Lemma D_148f00 : decode_any W_148f00 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f04 : bv 32 := 0x0053e2b3.
Lemma F_148f04 : fetch_word Asan.M.loaded_segments (0x148f48 : word) = Some W_148f04.
Proof. vm_refl. Qed.
Lemma D_148f04 : decode_any W_148f04 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f08 : bv 32 := 0x01871393.
Lemma F_148f08 : fetch_word Asan.M.loaded_segments (0x148f4c : word) = Some W_148f08.
Proof. vm_refl. Qed.
Lemma D_148f08 : decode_any W_148f08 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f0c : bv 32 := 0x0063e333.
Lemma F_148f0c : fetch_word Asan.M.loaded_segments (0x148f50 : word) = Some W_148f0c.
Proof. vm_refl. Qed.
Lemma D_148f0c : decode_any W_148f0c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f10 : bv 32 := 0xff060613.
Lemma F_148f10 : fetch_word Asan.M.loaded_segments (0x148f54 : word) = Some W_148f10.
Proof. vm_refl. Qed.
Lemma D_148f10 : decode_any W_148f10 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f14 : bv 32 := 0x0106a023.
Lemma F_148f14 : fetch_word Asan.M.loaded_segments (0x148f58 : word) = Some W_148f14.
Proof. vm_refl. Qed.
Lemma D_148f14 : decode_any W_148f14 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f18 : bv 32 := 0x0116a223.
Lemma F_148f18 : fetch_word Asan.M.loaded_segments (0x148f5c : word) = Some W_148f18.
Proof. vm_refl. Qed.
Lemma D_148f18 : decode_any W_148f18 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f1c : bv 32 := 0x0056a423.
Lemma F_148f1c : fetch_word Asan.M.loaded_segments (0x148f60 : word) = Some W_148f1c.
Proof. vm_refl. Qed.
Lemma D_148f1c : decode_any W_148f1c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f20 : bv 32 := 0x0066a623.
Lemma F_148f20 : fetch_word Asan.M.loaded_segments (0x148f64 : word) = Some W_148f20.
Proof. vm_refl. Qed.
Lemma D_148f20 : decode_any W_148f20 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f24 : bv 32 := 0x01068693.
Lemma F_148f24 : fetch_word Asan.M.loaded_segments (0x148f68 : word) = Some W_148f24.
Proof. vm_refl. Qed.
Lemma D_148f24 : decode_any W_148f24 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f28 : bv 32 := 0x01058593.
Lemma F_148f28 : fetch_word Asan.M.loaded_segments (0x148f6c : word) = Some W_148f28.
Proof. vm_refl. Qed.
Lemma D_148f28 : decode_any W_148f28 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f2c : bv 32 := 0xfac7e2e3.
Lemma F_148f2c : fetch_word Asan.M.loaded_segments (0x148f70 : word) = Some W_148f2c.
Proof. vm_refl. Qed.
Lemma D_148f2c : decode_any W_148f2c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f30 : bv 32 := 0xff158593.
Lemma F_148f30 : fetch_word Asan.M.loaded_segments (0x148f74 : word) = Some W_148f30.
Proof. vm_refl. Qed.
Lemma D_148f30 : decode_any W_148f30 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f34 : bv 32 := 0x01000713.
Lemma F_148f34 : fetch_word Asan.M.loaded_segments (0x148f78 : word) = Some W_148f34.
Proof. vm_refl. Qed.
Lemma D_148f34 : decode_any W_148f34 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f38 : bv 32 := 0xe4e666e3.
Lemma F_148f38 : fetch_word Asan.M.loaded_segments (0x148f7c : word) = Some W_148f38.
Proof. vm_refl. Qed.
Lemma D_148f38 : decode_any W_148f38 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f3c : bv 32 := 0x0940006f.
Lemma F_148f3c : fetch_word Asan.M.loaded_segments (0x148f80 : word) = Some W_148f3c.
Proof. vm_refl. Qed.
Lemma D_148f3c : decode_any W_148f3c = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f40 : bv 32 := 0x00875793.
Lemma F_148f40 : fetch_word Asan.M.loaded_segments (0x148f84 : word) = Some W_148f40.
Proof. vm_refl. Qed.
Lemma D_148f40 : decode_any W_148f40 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f44 : bv 32 := 0x01075813.
Lemma F_148f44 : fetch_word Asan.M.loaded_segments (0x148f88 : word) = Some W_148f44.
Proof. vm_refl. Qed.
Lemma D_148f44 : decode_any W_148f44 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f48 : bv 32 := 0xffd60613.
Lemma F_148f48 : fetch_word Asan.M.loaded_segments (0x148f8c : word) = Some W_148f48.
Proof. vm_refl. Qed.
Lemma D_148f48 : decode_any W_148f48 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f4c : bv 32 := 0x00e68023.
Lemma F_148f4c : fetch_word Asan.M.loaded_segments (0x148f90 : word) = Some W_148f4c.
Proof. vm_refl. Qed.
Lemma D_148f4c : decode_any W_148f4c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f50 : bv 32 := 0x00f680a3.
Lemma F_148f50 : fetch_word Asan.M.loaded_segments (0x148f94 : word) = Some W_148f50.
Proof. vm_refl. Qed.
Lemma D_148f50 : decode_any W_148f50 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f54 : bv 32 := 0x01068123.
Lemma F_148f54 : fetch_word Asan.M.loaded_segments (0x148f98 : word) = Some W_148f54.
Proof. vm_refl. Qed.
Lemma D_148f54 : decode_any W_148f54 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f58 : bv 32 := 0x00368693.
Lemma F_148f58 : fetch_word Asan.M.loaded_segments (0x148f9c : word) = Some W_148f58.
Proof. vm_refl. Qed.
Lemma D_148f58 : decode_any W_148f58 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f5c : bv 32 := 0x01058593.
Lemma F_148f5c : fetch_word Asan.M.loaded_segments (0x148fa0 : word) = Some W_148f5c.
Proof. vm_refl. Qed.
Lemma D_148f5c : decode_any W_148f5c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f60 : bv 32 := 0x01000793.
Lemma F_148f60 : fetch_word Asan.M.loaded_segments (0x148fa4 : word) = Some W_148f60.
Proof. vm_refl. Qed.
Lemma D_148f60 : decode_any W_148f60 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f64 : bv 32 := 0x0187581b.
Lemma F_148f64 : fetch_word Asan.M.loaded_segments (0x148fa8 : word) = Some W_148f64.
Proof. vm_refl. Qed.
Lemma D_148f64 : decode_any W_148f64 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f68 : bv 32 := 0xff45a883.
Lemma F_148f68 : fetch_word Asan.M.loaded_segments (0x148fac : word) = Some W_148f68.
Proof. vm_refl. Qed.
Lemma D_148f68 : decode_any W_148f68 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f6c : bv 32 := 0xff85a283.
Lemma F_148f6c : fetch_word Asan.M.loaded_segments (0x148fb0 : word) = Some W_148f6c.
Proof. vm_refl. Qed.
Lemma D_148f6c : decode_any W_148f6c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f70 : bv 32 := 0xffc5a303.
Lemma F_148f70 : fetch_word Asan.M.loaded_segments (0x148fb4 : word) = Some W_148f70.
Proof. vm_refl. Qed.
Lemma D_148f70 : decode_any W_148f70 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f74 : bv 32 := 0x0005a703.
Lemma F_148f74 : fetch_word Asan.M.loaded_segments (0x148fb8 : word) = Some W_148f74.
Proof. vm_refl. Qed.
Lemma D_148f74 : decode_any W_148f74 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f78 : bv 32 := 0x00889393.
Lemma F_148f78 : fetch_word Asan.M.loaded_segments (0x148fbc : word) = Some W_148f78.
Proof. vm_refl. Qed.
Lemma D_148f78 : decode_any W_148f78 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f7c : bv 32 := 0x0188d89b.
Lemma F_148f7c : fetch_word Asan.M.loaded_segments (0x148fc0 : word) = Some W_148f7c.
Proof. vm_refl. Qed.
Lemma D_148f7c : decode_any W_148f7c = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f80 : bv 32 := 0x0103e833.
Lemma F_148f80 : fetch_word Asan.M.loaded_segments (0x148fc4 : word) = Some W_148f80.
Proof. vm_refl. Qed.
Lemma D_148f80 : decode_any W_148f80 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f84 : bv 32 := 0x00829393.
Lemma F_148f84 : fetch_word Asan.M.loaded_segments (0x148fc8 : word) = Some W_148f84.
Proof. vm_refl. Qed.
Lemma D_148f84 : decode_any W_148f84 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f88 : bv 32 := 0x0182d29b.
Lemma F_148f88 : fetch_word Asan.M.loaded_segments (0x148fcc : word) = Some W_148f88.
Proof. vm_refl. Qed.
Lemma D_148f88 : decode_any W_148f88 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f8c : bv 32 := 0x0113e8b3.
Lemma F_148f8c : fetch_word Asan.M.loaded_segments (0x148fd0 : word) = Some W_148f8c.
Proof. vm_refl. Qed.
Lemma D_148f8c : decode_any W_148f8c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f90 : bv 32 := 0x00831393.
Lemma F_148f90 : fetch_word Asan.M.loaded_segments (0x148fd4 : word) = Some W_148f90.
Proof. vm_refl. Qed.
Lemma D_148f90 : decode_any W_148f90 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f94 : bv 32 := 0x0183531b.
Lemma F_148f94 : fetch_word Asan.M.loaded_segments (0x148fd8 : word) = Some W_148f94.
Proof. vm_refl. Qed.
Lemma D_148f94 : decode_any W_148f94 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f98 : bv 32 := 0x0053e2b3.
Lemma F_148f98 : fetch_word Asan.M.loaded_segments (0x148fdc : word) = Some W_148f98.
Proof. vm_refl. Qed.
Lemma D_148f98 : decode_any W_148f98 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_148f9c : bv 32 := 0x00871393.
Lemma F_148f9c : fetch_word Asan.M.loaded_segments (0x148fe0 : word) = Some W_148f9c.
Proof. vm_refl. Qed.
Lemma D_148f9c : decode_any W_148f9c = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fa0 : bv 32 := 0x0063e333.
Lemma F_148fa0 : fetch_word Asan.M.loaded_segments (0x148fe4 : word) = Some W_148fa0.
Proof. vm_refl. Qed.
Lemma D_148fa0 : decode_any W_148fa0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fa4 : bv 32 := 0xff060613.
Lemma F_148fa4 : fetch_word Asan.M.loaded_segments (0x148fe8 : word) = Some W_148fa4.
Proof. vm_refl. Qed.
Lemma D_148fa4 : decode_any W_148fa4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fa8 : bv 32 := 0x0106a023.
Lemma F_148fa8 : fetch_word Asan.M.loaded_segments (0x148fec : word) = Some W_148fa8.
Proof. vm_refl. Qed.
Lemma D_148fa8 : decode_any W_148fa8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fac : bv 32 := 0x0116a223.
Lemma F_148fac : fetch_word Asan.M.loaded_segments (0x148ff0 : word) = Some W_148fac.
Proof. vm_refl. Qed.
Lemma D_148fac : decode_any W_148fac = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fb0 : bv 32 := 0x0056a423.
Lemma F_148fb0 : fetch_word Asan.M.loaded_segments (0x148ff4 : word) = Some W_148fb0.
Proof. vm_refl. Qed.
Lemma D_148fb0 : decode_any W_148fb0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fb4 : bv 32 := 0x0066a623.
Lemma F_148fb4 : fetch_word Asan.M.loaded_segments (0x148ff8 : word) = Some W_148fb4.
Proof. vm_refl. Qed.
Lemma D_148fb4 : decode_any W_148fb4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fb8 : bv 32 := 0x01068693.
Lemma F_148fb8 : fetch_word Asan.M.loaded_segments (0x148ffc : word) = Some W_148fb8.
Proof. vm_refl. Qed.
Lemma D_148fb8 : decode_any W_148fb8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fbc : bv 32 := 0x01058593.
Lemma F_148fbc : fetch_word Asan.M.loaded_segments (0x149000 : word) = Some W_148fbc.
Proof. vm_refl. Qed.
Lemma D_148fbc : decode_any W_148fbc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fc0 : bv 32 := 0xfac7e2e3.
Lemma F_148fc0 : fetch_word Asan.M.loaded_segments (0x149004 : word) = Some W_148fc0.
Proof. vm_refl. Qed.
Lemma D_148fc0 : decode_any W_148fc0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fc4 : bv 32 := 0xff358593.
Lemma F_148fc4 : fetch_word Asan.M.loaded_segments (0x149008 : word) = Some W_148fc4.
Proof. vm_refl. Qed.
Lemma D_148fc4 : decode_any W_148fc4 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fc8 : bv 32 := 0x01000713.
Lemma F_148fc8 : fetch_word Asan.M.loaded_segments (0x14900c : word) = Some W_148fc8.
Proof. vm_refl. Qed.
Lemma D_148fc8 : decode_any W_148fc8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fcc : bv 32 := 0xdae66ce3.
Lemma F_148fcc : fetch_word Asan.M.loaded_segments (0x149010 : word) = Some W_148fcc.
Proof. vm_refl. Qed.
Lemma D_148fcc : decode_any W_148fcc = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fd0 : bv 32 := 0x0005c703.
Lemma F_148fd0 : fetch_word Asan.M.loaded_segments (0x149014 : word) = Some W_148fd0.
Proof. vm_refl. Qed.
Lemma D_148fd0 : decode_any W_148fd0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fd4 : bv 32 := 0x0015c783.
Lemma F_148fd4 : fetch_word Asan.M.loaded_segments (0x149018 : word) = Some W_148fd4.
Proof. vm_refl. Qed.
Lemma D_148fd4 : decode_any W_148fd4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fd8 : bv 32 := 0x0025c803.
Lemma F_148fd8 : fetch_word Asan.M.loaded_segments (0x14901c : word) = Some W_148fd8.
Proof. vm_refl. Qed.
Lemma D_148fd8 : decode_any W_148fd8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fdc : bv 32 := 0x0035c883.
Lemma F_148fdc : fetch_word Asan.M.loaded_segments (0x149020 : word) = Some W_148fdc.
Proof. vm_refl. Qed.
Lemma D_148fdc : decode_any W_148fdc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fe0 : bv 32 := 0x0045c283.
Lemma F_148fe0 : fetch_word Asan.M.loaded_segments (0x149024 : word) = Some W_148fe0.
Proof. vm_refl. Qed.
Lemma D_148fe0 : decode_any W_148fe0 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fe4 : bv 32 := 0x0055c303.
Lemma F_148fe4 : fetch_word Asan.M.loaded_segments (0x149028 : word) = Some W_148fe4.
Proof. vm_refl. Qed.
Lemma D_148fe4 : decode_any W_148fe4 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fe8 : bv 32 := 0x0065c383.
Lemma F_148fe8 : fetch_word Asan.M.loaded_segments (0x14902c : word) = Some W_148fe8.
Proof. vm_refl. Qed.
Lemma D_148fe8 : decode_any W_148fe8 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_148fec : bv 32 := 0x0075ce03.
Lemma F_148fec : fetch_word Asan.M.loaded_segments (0x149030 : word) = Some W_148fec.
Proof. vm_refl. Qed.
Lemma D_148fec : decode_any W_148fec = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ff0 : bv 32 := 0x00e68023.
Lemma F_148ff0 : fetch_word Asan.M.loaded_segments (0x149034 : word) = Some W_148ff0.
Proof. vm_refl. Qed.
Lemma D_148ff0 : decode_any W_148ff0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ff4 : bv 32 := 0x00f680a3.
Lemma F_148ff4 : fetch_word Asan.M.loaded_segments (0x149038 : word) = Some W_148ff4.
Proof. vm_refl. Qed.
Lemma D_148ff4 : decode_any W_148ff4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ff8 : bv 32 := 0x01068123.
Lemma F_148ff8 : fetch_word Asan.M.loaded_segments (0x14903c : word) = Some W_148ff8.
Proof. vm_refl. Qed.
Lemma D_148ff8 : decode_any W_148ff8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_148ffc : bv 32 := 0x011681a3.
Lemma F_148ffc : fetch_word Asan.M.loaded_segments (0x149040 : word) = Some W_148ffc.
Proof. vm_refl. Qed.
Lemma D_148ffc : decode_any W_148ffc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_149000 : bv 32 := 0x0085c703.
Lemma F_149000 : fetch_word Asan.M.loaded_segments (0x149044 : word) = Some W_149000.
Proof. vm_refl. Qed.
Lemma D_149000 : decode_any W_149000 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_149004 : bv 32 := 0x0095c783.
Lemma F_149004 : fetch_word Asan.M.loaded_segments (0x149048 : word) = Some W_149004.
Proof. vm_refl. Qed.
Lemma D_149004 : decode_any W_149004 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_149008 : bv 32 := 0x00a5c803.
Lemma F_149008 : fetch_word Asan.M.loaded_segments (0x14904c : word) = Some W_149008.
Proof. vm_refl. Qed.
Lemma D_149008 : decode_any W_149008 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_14900c : bv 32 := 0x00b5c883.
Lemma F_14900c : fetch_word Asan.M.loaded_segments (0x149050 : word) = Some W_14900c.
Proof. vm_refl. Qed.
Lemma D_14900c : decode_any W_14900c = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_149010 : bv 32 := 0x00568223.
Lemma F_149010 : fetch_word Asan.M.loaded_segments (0x149054 : word) = Some W_149010.
Proof. vm_refl. Qed.
Lemma D_149010 : decode_any W_149010 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_149014 : bv 32 := 0x006682a3.
Lemma F_149014 : fetch_word Asan.M.loaded_segments (0x149058 : word) = Some W_149014.
Proof. vm_refl. Qed.
Lemma D_149014 : decode_any W_149014 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_149018 : bv 32 := 0x00768323.
Lemma F_149018 : fetch_word Asan.M.loaded_segments (0x14905c : word) = Some W_149018.
Proof. vm_refl. Qed.
Lemma D_149018 : decode_any W_149018 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_14901c : bv 32 := 0x01c683a3.
Lemma F_14901c : fetch_word Asan.M.loaded_segments (0x149060 : word) = Some W_14901c.
Proof. vm_refl. Qed.
Lemma D_14901c : decode_any W_14901c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_149020 : bv 32 := 0x00c5c283.
Lemma F_149020 : fetch_word Asan.M.loaded_segments (0x149064 : word) = Some W_149020.
Proof. vm_refl. Qed.
Lemma D_149020 : decode_any W_149020 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_149024 : bv 32 := 0x00d5c303.
Lemma F_149024 : fetch_word Asan.M.loaded_segments (0x149068 : word) = Some W_149024.
Proof. vm_refl. Qed.
Lemma D_149024 : decode_any W_149024 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_149028 : bv 32 := 0x00e5c383.
Lemma F_149028 : fetch_word Asan.M.loaded_segments (0x14906c : word) = Some W_149028.
Proof. vm_refl. Qed.
Lemma D_149028 : decode_any W_149028 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_14902c : bv 32 := 0x00f5ce03.
Lemma F_14902c : fetch_word Asan.M.loaded_segments (0x149070 : word) = Some W_14902c.
Proof. vm_refl. Qed.
Lemma D_14902c : decode_any W_14902c = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_149030 : bv 32 := 0x01058593.
Lemma F_149030 : fetch_word Asan.M.loaded_segments (0x149074 : word) = Some W_149030.
Proof. vm_refl. Qed.
Lemma D_149030 : decode_any W_149030 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_149034 : bv 32 := 0x00e68423.
Lemma F_149034 : fetch_word Asan.M.loaded_segments (0x149078 : word) = Some W_149034.
Proof. vm_refl. Qed.
Lemma D_149034 : decode_any W_149034 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_149038 : bv 32 := 0x00f684a3.
Lemma F_149038 : fetch_word Asan.M.loaded_segments (0x14907c : word) = Some W_149038.
Proof. vm_refl. Qed.
Lemma D_149038 : decode_any W_149038 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_14903c : bv 32 := 0x01068523.
Lemma F_14903c : fetch_word Asan.M.loaded_segments (0x149080 : word) = Some W_14903c.
Proof. vm_refl. Qed.
Lemma D_14903c : decode_any W_14903c = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_149040 : bv 32 := 0x011685a3.
Lemma F_149040 : fetch_word Asan.M.loaded_segments (0x149084 : word) = Some W_149040.
Proof. vm_refl. Qed.
Lemma D_149040 : decode_any W_149040 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_149044 : bv 32 := 0x01068713.
Lemma F_149044 : fetch_word Asan.M.loaded_segments (0x149088 : word) = Some W_149044.
Proof. vm_refl. Qed.
Lemma D_149044 : decode_any W_149044 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_149048 : bv 32 := 0x00568623.
Lemma F_149048 : fetch_word Asan.M.loaded_segments (0x14908c : word) = Some W_149048.
Proof. vm_refl. Qed.
Lemma D_149048 : decode_any W_149048 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_14904c : bv 32 := 0x006686a3.
Lemma F_14904c : fetch_word Asan.M.loaded_segments (0x149090 : word) = Some W_14904c.
Proof. vm_refl. Qed.
Lemma D_14904c : decode_any W_14904c = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_149050 : bv 32 := 0x00768723.
Lemma F_149050 : fetch_word Asan.M.loaded_segments (0x149094 : word) = Some W_149050.
Proof. vm_refl. Qed.
Lemma D_149050 : decode_any W_149050 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_149054 : bv 32 := 0x01c687a3.
Lemma F_149054 : fetch_word Asan.M.loaded_segments (0x149098 : word) = Some W_149054.
Proof. vm_refl. Qed.
Lemma D_149054 : decode_any W_149054 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_149058 : bv 32 := 0x00070693.
Lemma F_149058 : fetch_word Asan.M.loaded_segments (0x14909c : word) = Some W_149058.
Proof. vm_refl. Qed.
Lemma D_149058 : decode_any W_149058 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14905c : bv 32 := 0x00867713.
Lemma F_14905c : fetch_word Asan.M.loaded_segments (0x1490a0 : word) = Some W_14905c.
Proof. vm_refl. Qed.
Lemma D_14905c : decode_any W_14905c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_149060 : bv 32 := 0xd20706e3.
Lemma F_149060 : fetch_word Asan.M.loaded_segments (0x1490a4 : word) = Some W_149060.
Proof. vm_refl. Qed.
Lemma D_149060 : decode_any W_149060 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_149064 : bv 32 := 0x0005c703.
Lemma F_149064 : fetch_word Asan.M.loaded_segments (0x1490a8 : word) = Some W_149064.
Proof. vm_refl. Qed.
Lemma D_149064 : decode_any W_149064 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149068 : bv 32 := 0x0015c783.
Lemma F_149068 : fetch_word Asan.M.loaded_segments (0x1490ac : word) = Some W_149068.
Proof. vm_refl. Qed.
Lemma D_149068 : decode_any W_149068 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14906c : bv 32 := 0x0025c803.
Lemma F_14906c : fetch_word Asan.M.loaded_segments (0x1490b0 : word) = Some W_14906c.
Proof. vm_refl. Qed.
Lemma D_14906c : decode_any W_14906c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_149070 : bv 32 := 0x0035c883.
Lemma F_149070 : fetch_word Asan.M.loaded_segments (0x1490b4 : word) = Some W_149070.
Proof. vm_refl. Qed.
Lemma D_149070 : decode_any W_149070 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_149074 : bv 32 := 0x0045c283.
Lemma F_149074 : fetch_word Asan.M.loaded_segments (0x1490b8 : word) = Some W_149074.
Proof. vm_refl. Qed.
Lemma D_149074 : decode_any W_149074 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_149078 : bv 32 := 0x0055c303.
Lemma F_149078 : fetch_word Asan.M.loaded_segments (0x1490bc : word) = Some W_149078.
Proof. vm_refl. Qed.
Lemma D_149078 : decode_any W_149078 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_14907c : bv 32 := 0x0065c383.
Lemma F_14907c : fetch_word Asan.M.loaded_segments (0x1490c0 : word) = Some W_14907c.
Proof. vm_refl. Qed.
Lemma D_14907c : decode_any W_14907c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_149080 : bv 32 := 0x0075ce03.
Lemma F_149080 : fetch_word Asan.M.loaded_segments (0x1490c4 : word) = Some W_149080.
Proof. vm_refl. Qed.
Lemma D_149080 : decode_any W_149080 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_149084 : bv 32 := 0x00858593.
Lemma F_149084 : fetch_word Asan.M.loaded_segments (0x1490c8 : word) = Some W_149084.
Proof. vm_refl. Qed.
Lemma D_149084 : decode_any W_149084 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_149088 : bv 32 := 0x00e68023.
Lemma F_149088 : fetch_word Asan.M.loaded_segments (0x1490cc : word) = Some W_149088.
Proof. vm_refl. Qed.
Lemma D_149088 : decode_any W_149088 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14908c : bv 32 := 0x00f680a3.
Lemma F_14908c : fetch_word Asan.M.loaded_segments (0x1490d0 : word) = Some W_14908c.
Proof. vm_refl. Qed.
Lemma D_14908c : decode_any W_14908c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_149090 : bv 32 := 0x01068123.
Lemma F_149090 : fetch_word Asan.M.loaded_segments (0x1490d4 : word) = Some W_149090.
Proof. vm_refl. Qed.
Lemma D_149090 : decode_any W_149090 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_149094 : bv 32 := 0x011681a3.
Lemma F_149094 : fetch_word Asan.M.loaded_segments (0x1490d8 : word) = Some W_149094.
Proof. vm_refl. Qed.
Lemma D_149094 : decode_any W_149094 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_149098 : bv 32 := 0x00868713.
Lemma F_149098 : fetch_word Asan.M.loaded_segments (0x1490dc : word) = Some W_149098.
Proof. vm_refl. Qed.
Lemma D_149098 : decode_any W_149098 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14909c : bv 32 := 0x00568223.
Lemma F_14909c : fetch_word Asan.M.loaded_segments (0x1490e0 : word) = Some W_14909c.
Proof. vm_refl. Qed.
Lemma D_14909c : decode_any W_14909c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490a0 : bv 32 := 0x006682a3.
Lemma F_1490a0 : fetch_word Asan.M.loaded_segments (0x1490e4 : word) = Some W_1490a0.
Proof. vm_refl. Qed.
Lemma D_1490a0 : decode_any W_1490a0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490a4 : bv 32 := 0x00768323.
Lemma F_1490a4 : fetch_word Asan.M.loaded_segments (0x1490e8 : word) = Some W_1490a4.
Proof. vm_refl. Qed.
Lemma D_1490a4 : decode_any W_1490a4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490a8 : bv 32 := 0x01c683a3.
Lemma F_1490a8 : fetch_word Asan.M.loaded_segments (0x1490ec : word) = Some W_1490a8.
Proof. vm_refl. Qed.
Lemma D_1490a8 : decode_any W_1490a8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490ac : bv 32 := 0x00070693.
Lemma F_1490ac : fetch_word Asan.M.loaded_segments (0x1490f0 : word) = Some W_1490ac.
Proof. vm_refl. Qed.
Lemma D_1490ac : decode_any W_1490ac = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490b0 : bv 32 := 0x00467713.
Lemma F_1490b0 : fetch_word Asan.M.loaded_segments (0x1490f4 : word) = Some W_1490b0.
Proof. vm_refl. Qed.
Lemma D_1490b0 : decode_any W_1490b0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490b4 : bv 32 := 0x02070863.
Lemma F_1490b4 : fetch_word Asan.M.loaded_segments (0x1490f8 : word) = Some W_1490b4.
Proof. vm_refl. Qed.
Lemma D_1490b4 : decode_any W_1490b4 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490b8 : bv 32 := 0x0005c703.
Lemma F_1490b8 : fetch_word Asan.M.loaded_segments (0x1490fc : word) = Some W_1490b8.
Proof. vm_refl. Qed.
Lemma D_1490b8 : decode_any W_1490b8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490bc : bv 32 := 0x0015c783.
Lemma F_1490bc : fetch_word Asan.M.loaded_segments (0x149100 : word) = Some W_1490bc.
Proof. vm_refl. Qed.
Lemma D_1490bc : decode_any W_1490bc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490c0 : bv 32 := 0x0025c803.
Lemma F_1490c0 : fetch_word Asan.M.loaded_segments (0x149104 : word) = Some W_1490c0.
Proof. vm_refl. Qed.
Lemma D_1490c0 : decode_any W_1490c0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490c4 : bv 32 := 0x0035c883.
Lemma F_1490c4 : fetch_word Asan.M.loaded_segments (0x149108 : word) = Some W_1490c4.
Proof. vm_refl. Qed.
Lemma D_1490c4 : decode_any W_1490c4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490c8 : bv 32 := 0x00458593.
Lemma F_1490c8 : fetch_word Asan.M.loaded_segments (0x14910c : word) = Some W_1490c8.
Proof. vm_refl. Qed.
Lemma D_1490c8 : decode_any W_1490c8 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490cc : bv 32 := 0x00468293.
Lemma F_1490cc : fetch_word Asan.M.loaded_segments (0x149110 : word) = Some W_1490cc.
Proof. vm_refl. Qed.
Lemma D_1490cc : decode_any W_1490cc = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490d0 : bv 32 := 0x00e68023.
Lemma F_1490d0 : fetch_word Asan.M.loaded_segments (0x149114 : word) = Some W_1490d0.
Proof. vm_refl. Qed.
Lemma D_1490d0 : decode_any W_1490d0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490d4 : bv 32 := 0x00f680a3.
Lemma F_1490d4 : fetch_word Asan.M.loaded_segments (0x149118 : word) = Some W_1490d4.
Proof. vm_refl. Qed.
Lemma D_1490d4 : decode_any W_1490d4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490d8 : bv 32 := 0x01068123.
Lemma F_1490d8 : fetch_word Asan.M.loaded_segments (0x14911c : word) = Some W_1490d8.
Proof. vm_refl. Qed.
Lemma D_1490d8 : decode_any W_1490d8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490dc : bv 32 := 0x011681a3.
Lemma F_1490dc : fetch_word Asan.M.loaded_segments (0x149120 : word) = Some W_1490dc.
Proof. vm_refl. Qed.
Lemma D_1490dc : decode_any W_1490dc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490e0 : bv 32 := 0x00028693.
Lemma F_1490e0 : fetch_word Asan.M.loaded_segments (0x149124 : word) = Some W_1490e0.
Proof. vm_refl. Qed.
Lemma D_1490e0 : decode_any W_1490e0 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490e4 : bv 32 := 0x00267713.
Lemma F_1490e4 : fetch_word Asan.M.loaded_segments (0x149128 : word) = Some W_1490e4.
Proof. vm_refl. Qed.
Lemma D_1490e4 : decode_any W_1490e4 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490e8 : bv 32 := 0x00071863.
Lemma F_1490e8 : fetch_word Asan.M.loaded_segments (0x14912c : word) = Some W_1490e8.
Proof. vm_refl. Qed.
Lemma D_1490e8 : decode_any W_1490e8 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490ec : bv 32 := 0x00167613.
Lemma F_1490ec : fetch_word Asan.M.loaded_segments (0x149130 : word) = Some W_1490ec.
Proof. vm_refl. Qed.
Lemma D_1490ec : decode_any W_1490ec = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490f0 : bv 32 := 0x02061663.
Lemma F_1490f0 : fetch_word Asan.M.loaded_segments (0x149134 : word) = Some W_1490f0.
Proof. vm_refl. Qed.
Lemma D_1490f0 : decode_any W_1490f0 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490f4 : bv 32 := 0x00008067.
Lemma F_1490f4 : fetch_word Asan.M.loaded_segments (0x149138 : word) = Some W_1490f4.
Proof. vm_refl. Qed.
Lemma D_1490f4 : decode_any W_1490f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490f8 : bv 32 := 0x0005c703.
Lemma F_1490f8 : fetch_word Asan.M.loaded_segments (0x14913c : word) = Some W_1490f8.
Proof. vm_refl. Qed.
Lemma D_1490f8 : decode_any W_1490f8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1490fc : bv 32 := 0x0015c783.
Lemma F_1490fc : fetch_word Asan.M.loaded_segments (0x149140 : word) = Some W_1490fc.
Proof. vm_refl. Qed.
Lemma D_1490fc : decode_any W_1490fc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_149100 : bv 32 := 0x00258593.
Lemma F_149100 : fetch_word Asan.M.loaded_segments (0x149144 : word) = Some W_149100.
Proof. vm_refl. Qed.
Lemma D_149100 : decode_any W_149100 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_149104 : bv 32 := 0x00268813.
Lemma F_149104 : fetch_word Asan.M.loaded_segments (0x149148 : word) = Some W_149104.
Proof. vm_refl. Qed.
Lemma D_149104 : decode_any W_149104 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_149108 : bv 32 := 0x00e68023.
Lemma F_149108 : fetch_word Asan.M.loaded_segments (0x14914c : word) = Some W_149108.
Proof. vm_refl. Qed.
Lemma D_149108 : decode_any W_149108 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14910c : bv 32 := 0x00f680a3.
Lemma F_14910c : fetch_word Asan.M.loaded_segments (0x149150 : word) = Some W_14910c.
Proof. vm_refl. Qed.
Lemma D_14910c : decode_any W_14910c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_149110 : bv 32 := 0x00080693.
Lemma F_149110 : fetch_word Asan.M.loaded_segments (0x149154 : word) = Some W_149110.
Proof. vm_refl. Qed.
Lemma D_149110 : decode_any W_149110 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149114 : bv 32 := 0x00167613.
Lemma F_149114 : fetch_word Asan.M.loaded_segments (0x149158 : word) = Some W_149114.
Proof. vm_refl. Qed.
Lemma D_149114 : decode_any W_149114 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_149118 : bv 32 := 0xfc060ee3.
Lemma F_149118 : fetch_word Asan.M.loaded_segments (0x14915c : word) = Some W_149118.
Proof. vm_refl. Qed.
Lemma D_149118 : decode_any W_149118 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_14911c : bv 32 := 0x0005c583.
Lemma F_14911c : fetch_word Asan.M.loaded_segments (0x149160 : word) = Some W_14911c.
Proof. vm_refl. Qed.
Lemma D_14911c : decode_any W_14911c = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149120 : bv 32 := 0x00b68023.
Lemma F_149120 : fetch_word Asan.M.loaded_segments (0x149164 : word) = Some W_149120.
Proof. vm_refl. Qed.
Lemma D_149120 : decode_any W_149120 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149124 : bv 32 := 0x00008067.
Lemma F_149124 : fetch_word Asan.M.loaded_segments (0x149168 : word) = Some W_149124.
Proof. vm_refl. Qed.
Lemma D_149124 : decode_any W_149124 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Asan_code_memcpyK.
Module AsanMemset_codeK.
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

Definition W_149128 : bv 32 := 0x0e060a63.
Lemma F_149128 : fetch_word Asan.M.loaded_segments (0x14916c : word) = Some W_149128.
Proof. vm_refl. Qed.
Lemma D_149128 : decode_any W_149128 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_14912c : bv 32 := 0x00b50023.
Lemma F_14912c : fetch_word Asan.M.loaded_segments (0x149170 : word) = Some W_14912c.
Proof. vm_refl. Qed.
Lemma D_14912c : decode_any W_14912c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149130 : bv 32 := 0x00c506b3.
Lemma F_149130 : fetch_word Asan.M.loaded_segments (0x149174 : word) = Some W_149130.
Proof. vm_refl. Qed.
Lemma D_149130 : decode_any W_149130 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_149134 : bv 32 := 0x00300713.
Lemma F_149134 : fetch_word Asan.M.loaded_segments (0x149178 : word) = Some W_149134.
Proof. vm_refl. Qed.
Lemma D_149134 : decode_any W_149134 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_149138 : bv 32 := 0xfeb68fa3.
Lemma F_149138 : fetch_word Asan.M.loaded_segments (0x14917c : word) = Some W_149138.
Proof. vm_refl. Qed.
Lemma D_149138 : decode_any W_149138 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_14913c : bv 32 := 0x0ee66063.
Lemma F_14913c : fetch_word Asan.M.loaded_segments (0x149180 : word) = Some W_14913c.
Proof. vm_refl. Qed.
Lemma D_14913c : decode_any W_14913c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_149140 : bv 32 := 0x00b500a3.
Lemma F_149140 : fetch_word Asan.M.loaded_segments (0x149184 : word) = Some W_149140.
Proof. vm_refl. Qed.
Lemma D_149140 : decode_any W_149140 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_149144 : bv 32 := 0x00b50123.
Lemma F_149144 : fetch_word Asan.M.loaded_segments (0x149188 : word) = Some W_149144.
Proof. vm_refl. Qed.
Lemma D_149144 : decode_any W_149144 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_149148 : bv 32 := 0x00700713.
Lemma F_149148 : fetch_word Asan.M.loaded_segments (0x14918c : word) = Some W_149148.
Proof. vm_refl. Qed.
Lemma D_149148 : decode_any W_149148 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_14914c : bv 32 := 0xfeb68ea3.
Lemma F_14914c : fetch_word Asan.M.loaded_segments (0x149190 : word) = Some W_14914c.
Proof. vm_refl. Qed.
Lemma D_14914c : decode_any W_14914c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_149150 : bv 32 := 0xfeb68f23.
Lemma F_149150 : fetch_word Asan.M.loaded_segments (0x149194 : word) = Some W_149150.
Proof. vm_refl. Qed.
Lemma D_149150 : decode_any W_149150 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_149154 : bv 32 := 0x0ce66463.
Lemma F_149154 : fetch_word Asan.M.loaded_segments (0x149198 : word) = Some W_149154.
Proof. vm_refl. Qed.
Lemma D_149154 : decode_any W_149154 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_149158 : bv 32 := 0x00b501a3.
Lemma F_149158 : fetch_word Asan.M.loaded_segments (0x14919c : word) = Some W_149158.
Proof. vm_refl. Qed.
Lemma D_149158 : decode_any W_149158 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_14915c : bv 32 := 0x00900793.
Lemma F_14915c : fetch_word Asan.M.loaded_segments (0x1491a0 : word) = Some W_14915c.
Proof. vm_refl. Qed.
Lemma D_14915c : decode_any W_14915c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_149160 : bv 32 := 0xfeb68e23.
Lemma F_149160 : fetch_word Asan.M.loaded_segments (0x1491a4 : word) = Some W_149160.
Proof. vm_refl. Qed.
Lemma D_149160 : decode_any W_149160 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_149164 : bv 32 := 0x0af66c63.
Lemma F_149164 : fetch_word Asan.M.loaded_segments (0x1491a8 : word) = Some W_149164.
Proof. vm_refl. Qed.
Lemma D_149164 : decode_any W_149164 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_149168 : bv 32 := 0x40a006bb.
Lemma F_149168 : fetch_word Asan.M.loaded_segments (0x1491ac : word) = Some W_149168.
Proof. vm_refl. Qed.
Lemma D_149168 : decode_any W_149168 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_14916c : bv 32 := 0x03859813.
Lemma F_14916c : fetch_word Asan.M.loaded_segments (0x1491b0 : word) = Some W_14916c.
Proof. vm_refl. Qed.
Lemma D_14916c : decode_any W_14916c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_149170 : bv 32 := 0x101015b7.
Lemma F_149170 : fetch_word Asan.M.loaded_segments (0x1491b4 : word) = Some W_149170.
Proof. vm_refl. Qed.
Lemma D_149170 : decode_any W_149170 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_149174 : bv 32 := 0x0036f693.
Lemma F_149174 : fetch_word Asan.M.loaded_segments (0x1491b8 : word) = Some W_149174.
Proof. vm_refl. Qed.
Lemma D_149174 : decode_any W_149174 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_149178 : bv 32 := 0x00459713.
Lemma F_149178 : fetch_word Asan.M.loaded_segments (0x1491bc : word) = Some W_149178.
Proof. vm_refl. Qed.
Lemma D_149178 : decode_any W_149178 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_14917c : bv 32 := 0x40d60633.
Lemma F_14917c : fetch_word Asan.M.loaded_segments (0x1491c0 : word) = Some W_14917c.
Proof. vm_refl. Qed.
Lemma D_14917c : decode_any W_14917c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_149180 : bv 32 := 0x00d505b3.
Lemma F_149180 : fetch_word Asan.M.loaded_segments (0x1491c4 : word) = Some W_149180.
Proof. vm_refl. Qed.
Lemma D_149180 : decode_any W_149180 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_149184 : bv 32 := 0x10070693.
Lemma F_149184 : fetch_word Asan.M.loaded_segments (0x1491c8 : word) = Some W_149184.
Proof. vm_refl. Qed.
Lemma D_149184 : decode_any W_149184 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_149188 : bv 32 := 0xffc67713.
Lemma F_149188 : fetch_word Asan.M.loaded_segments (0x1491cc : word) = Some W_149188.
Proof. vm_refl. Qed.
Lemma D_149188 : decode_any W_149188 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_14918c : bv 32 := 0x02d83633.
Lemma F_14918c : fetch_word Asan.M.loaded_segments (0x1491d0 : word) = Some W_14918c.
Proof. vm_refl. Qed.
Lemma D_14918c : decode_any W_14918c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_149190 : bv 32 := 0x00c5a023.
Lemma F_149190 : fetch_word Asan.M.loaded_segments (0x1491d4 : word) = Some W_149190.
Proof. vm_refl. Qed.
Lemma D_149190 : decode_any W_149190 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149194 : bv 32 := 0x00e586b3.
Lemma F_149194 : fetch_word Asan.M.loaded_segments (0x1491d8 : word) = Some W_149194.
Proof. vm_refl. Qed.
Lemma D_149194 : decode_any W_149194 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_149198 : bv 32 := 0xfec6ae23.
Lemma F_149198 : fetch_word Asan.M.loaded_segments (0x1491dc : word) = Some W_149198.
Proof. vm_refl. Qed.
Lemma D_149198 : decode_any W_149198 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_14919c : bv 32 := 0x08f76063.
Lemma F_14919c : fetch_word Asan.M.loaded_segments (0x1491e0 : word) = Some W_14919c.
Proof. vm_refl. Qed.
Lemma D_14919c : decode_any W_14919c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491a0 : bv 32 := 0x00c5a223.
Lemma F_1491a0 : fetch_word Asan.M.loaded_segments (0x1491e4 : word) = Some W_1491a0.
Proof. vm_refl. Qed.
Lemma D_1491a0 : decode_any W_1491a0 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491a4 : bv 32 := 0x00c5a423.
Lemma F_1491a4 : fetch_word Asan.M.loaded_segments (0x1491e8 : word) = Some W_1491a4.
Proof. vm_refl. Qed.
Lemma D_1491a4 : decode_any W_1491a4 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491a8 : bv 32 := 0x01900793.
Lemma F_1491a8 : fetch_word Asan.M.loaded_segments (0x1491ec : word) = Some W_1491a8.
Proof. vm_refl. Qed.
Lemma D_1491a8 : decode_any W_1491a8 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491ac : bv 32 := 0xfec6aa23.
Lemma F_1491ac : fetch_word Asan.M.loaded_segments (0x1491f0 : word) = Some W_1491ac.
Proof. vm_refl. Qed.
Lemma D_1491ac : decode_any W_1491ac = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491b0 : bv 32 := 0xfec6ac23.
Lemma F_1491b0 : fetch_word Asan.M.loaded_segments (0x1491f4 : word) = Some W_1491b0.
Proof. vm_refl. Qed.
Lemma D_1491b0 : decode_any W_1491b0 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491b4 : bv 32 := 0x06f76463.
Lemma F_1491b4 : fetch_word Asan.M.loaded_segments (0x1491f8 : word) = Some W_1491b4.
Proof. vm_refl. Qed.
Lemma D_1491b4 : decode_any W_1491b4 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491b8 : bv 32 := 0x00c5a623.
Lemma F_1491b8 : fetch_word Asan.M.loaded_segments (0x1491fc : word) = Some W_1491b8.
Proof. vm_refl. Qed.
Lemma D_1491b8 : decode_any W_1491b8 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491bc : bv 32 := 0x00c5a823.
Lemma F_1491bc : fetch_word Asan.M.loaded_segments (0x149200 : word) = Some W_1491bc.
Proof. vm_refl. Qed.
Lemma D_1491bc : decode_any W_1491bc = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491c0 : bv 32 := 0x00c5aa23.
Lemma F_1491c0 : fetch_word Asan.M.loaded_segments (0x149204 : word) = Some W_1491c0.
Proof. vm_refl. Qed.
Lemma D_1491c0 : decode_any W_1491c0 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491c4 : bv 32 := 0x00c5ac23.
Lemma F_1491c4 : fetch_word Asan.M.loaded_segments (0x149208 : word) = Some W_1491c4.
Proof. vm_refl. Qed.
Lemma D_1491c4 : decode_any W_1491c4 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491c8 : bv 32 := 0x0045f793.
Lemma F_1491c8 : fetch_word Asan.M.loaded_segments (0x14920c : word) = Some W_1491c8.
Proof. vm_refl. Qed.
Lemma D_1491c8 : decode_any W_1491c8 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491cc : bv 32 := 0x02000813.
Lemma F_1491cc : fetch_word Asan.M.loaded_segments (0x149210 : word) = Some W_1491cc.
Proof. vm_refl. Qed.
Lemma D_1491cc : decode_any W_1491cc = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491d0 : bv 32 := 0x01878793.
Lemma F_1491d0 : fetch_word Asan.M.loaded_segments (0x149214 : word) = Some W_1491d0.
Proof. vm_refl. Qed.
Lemma D_1491d0 : decode_any W_1491d0 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491d4 : bv 32 := 0x40f70733.
Lemma F_1491d4 : fetch_word Asan.M.loaded_segments (0x149218 : word) = Some W_1491d4.
Proof. vm_refl. Qed.
Lemma D_1491d4 : decode_any W_1491d4 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491d8 : bv 32 := 0xfec6a223.
Lemma F_1491d8 : fetch_word Asan.M.loaded_segments (0x14921c : word) = Some W_1491d8.
Proof. vm_refl. Qed.
Lemma D_1491d8 : decode_any W_1491d8 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491dc : bv 32 := 0xfec6a423.
Lemma F_1491dc : fetch_word Asan.M.loaded_segments (0x149220 : word) = Some W_1491dc.
Proof. vm_refl. Qed.
Lemma D_1491dc : decode_any W_1491dc = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491e0 : bv 32 := 0xfec6a623.
Lemma F_1491e0 : fetch_word Asan.M.loaded_segments (0x149224 : word) = Some W_1491e0.
Proof. vm_refl. Qed.
Lemma D_1491e0 : decode_any W_1491e0 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491e4 : bv 32 := 0xfec6a823.
Lemma F_1491e4 : fetch_word Asan.M.loaded_segments (0x149228 : word) = Some W_1491e4.
Proof. vm_refl. Qed.
Lemma D_1491e4 : decode_any W_1491e4 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491e8 : bv 32 := 0x03076a63.
Lemma F_1491e8 : fetch_word Asan.M.loaded_segments (0x14922c : word) = Some W_1491e8.
Proof. vm_refl. Qed.
Lemma D_1491e8 : decode_any W_1491e8 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491ec : bv 32 := 0x02061613.
Lemma F_1491ec : fetch_word Asan.M.loaded_segments (0x149230 : word) = Some W_1491ec.
Proof. vm_refl. Qed.
Lemma D_1491ec : decode_any W_1491ec = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491f0 : bv 32 := 0x00f585b3.
Lemma F_1491f0 : fetch_word Asan.M.loaded_segments (0x149234 : word) = Some W_1491f0.
Proof. vm_refl. Qed.
Lemma D_1491f0 : decode_any W_1491f0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491f4 : bv 32 := 0x02065693.
Lemma F_1491f4 : fetch_word Asan.M.loaded_segments (0x149238 : word) = Some W_1491f4.
Proof. vm_refl. Qed.
Lemma D_1491f4 : decode_any W_1491f4 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491f8 : bv 32 := 0x00d66633.
Lemma F_1491f8 : fetch_word Asan.M.loaded_segments (0x14923c : word) = Some W_1491f8.
Proof. vm_refl. Qed.
Lemma D_1491f8 : decode_any W_1491f8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1491fc : bv 32 := 0x01f00693.
Lemma F_1491fc : fetch_word Asan.M.loaded_segments (0x149240 : word) = Some W_1491fc.
Proof. vm_refl. Qed.
Lemma D_1491fc : decode_any W_1491fc = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_149200 : bv 32 := 0x00c5b023.
Lemma F_149200 : fetch_word Asan.M.loaded_segments (0x149244 : word) = Some W_149200.
Proof. vm_refl. Qed.
Lemma D_149200 : decode_any W_149200 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_149204 : bv 32 := 0x00c5b423.
Lemma F_149204 : fetch_word Asan.M.loaded_segments (0x149248 : word) = Some W_149204.
Proof. vm_refl. Qed.
Lemma D_149204 : decode_any W_149204 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_149208 : bv 32 := 0x00c5b823.
Lemma F_149208 : fetch_word Asan.M.loaded_segments (0x14924c : word) = Some W_149208.
Proof. vm_refl. Qed.
Lemma D_149208 : decode_any W_149208 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14920c : bv 32 := 0x00c5bc23.
Lemma F_14920c : fetch_word Asan.M.loaded_segments (0x149250 : word) = Some W_14920c.
Proof. vm_refl. Qed.
Lemma D_14920c : decode_any W_14920c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_149210 : bv 32 := 0xfe070713.
Lemma F_149210 : fetch_word Asan.M.loaded_segments (0x149254 : word) = Some W_149210.
Proof. vm_refl. Qed.
Lemma D_149210 : decode_any W_149210 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_149214 : bv 32 := 0x02058593.
Lemma F_149214 : fetch_word Asan.M.loaded_segments (0x149258 : word) = Some W_149214.
Proof. vm_refl. Qed.
Lemma D_149214 : decode_any W_149214 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_149218 : bv 32 := 0xfee6e4e3.
Lemma F_149218 : fetch_word Asan.M.loaded_segments (0x14925c : word) = Some W_149218.
Proof. vm_refl. Qed.
Lemma D_149218 : decode_any W_149218 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_14921c : bv 32 := 0x00008067.
Lemma F_14921c : fetch_word Asan.M.loaded_segments (0x149260 : word) = Some W_14921c.
Proof. vm_refl. Qed.
Lemma D_14921c : decode_any W_14921c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x14916c%Z.
Definition Fo_000 := F_149128.
Definition Do_000 := D_149128.
Definition Fo_004 := F_14912c.
Definition Do_004 := D_14912c.
Definition Fo_008 := F_149130.
Definition Do_008 := D_149130.
Definition Fo_00c := F_149134.
Definition Do_00c := D_149134.
Definition Fo_010 := F_149138.
Definition Do_010 := D_149138.
Definition Fo_014 := F_14913c.
Definition Do_014 := D_14913c.
Definition Fo_018 := F_149140.
Definition Do_018 := D_149140.
Definition Fo_01c := F_149144.
Definition Do_01c := D_149144.
Definition Fo_020 := F_149148.
Definition Do_020 := D_149148.
Definition Fo_024 := F_14914c.
Definition Do_024 := D_14914c.
Definition Fo_028 := F_149150.
Definition Do_028 := D_149150.
Definition Fo_02c := F_149154.
Definition Do_02c := D_149154.
Definition Fo_030 := F_149158.
Definition Do_030 := D_149158.
Definition Fo_034 := F_14915c.
Definition Do_034 := D_14915c.
Definition Fo_038 := F_149160.
Definition Do_038 := D_149160.
Definition Fo_03c := F_149164.
Definition Do_03c := D_149164.
Definition Fo_040 := F_149168.
Definition Do_040 := D_149168.
Definition Fo_044 := F_14916c.
Definition Do_044 := D_14916c.
Definition Fo_048 := F_149170.
Definition Do_048 := D_149170.
Definition Fo_04c := F_149174.
Definition Do_04c := D_149174.
Definition Fo_050 := F_149178.
Definition Do_050 := D_149178.
Definition Fo_054 := F_14917c.
Definition Do_054 := D_14917c.
Definition Fo_058 := F_149180.
Definition Do_058 := D_149180.
Definition Fo_05c := F_149184.
Definition Do_05c := D_149184.
Definition Fo_060 := F_149188.
Definition Do_060 := D_149188.
Definition Fo_064 := F_14918c.
Definition Do_064 := D_14918c.
Definition Fo_068 := F_149190.
Definition Do_068 := D_149190.
Definition Fo_06c := F_149194.
Definition Do_06c := D_149194.
Definition Fo_070 := F_149198.
Definition Do_070 := D_149198.
Definition Fo_074 := F_14919c.
Definition Do_074 := D_14919c.
Definition Fo_078 := F_1491a0.
Definition Do_078 := D_1491a0.
Definition Fo_07c := F_1491a4.
Definition Do_07c := D_1491a4.
Definition Fo_080 := F_1491a8.
Definition Do_080 := D_1491a8.
Definition Fo_084 := F_1491ac.
Definition Do_084 := D_1491ac.
Definition Fo_088 := F_1491b0.
Definition Do_088 := D_1491b0.
Definition Fo_08c := F_1491b4.
Definition Do_08c := D_1491b4.
Definition Fo_090 := F_1491b8.
Definition Do_090 := D_1491b8.
Definition Fo_094 := F_1491bc.
Definition Do_094 := D_1491bc.
Definition Fo_098 := F_1491c0.
Definition Do_098 := D_1491c0.
Definition Fo_09c := F_1491c4.
Definition Do_09c := D_1491c4.
Definition Fo_0a0 := F_1491c8.
Definition Do_0a0 := D_1491c8.
Definition Fo_0a4 := F_1491cc.
Definition Do_0a4 := D_1491cc.
Definition Fo_0a8 := F_1491d0.
Definition Do_0a8 := D_1491d0.
Definition Fo_0ac := F_1491d4.
Definition Do_0ac := D_1491d4.
Definition Fo_0b0 := F_1491d8.
Definition Do_0b0 := D_1491d8.
Definition Fo_0b4 := F_1491dc.
Definition Do_0b4 := D_1491dc.
Definition Fo_0b8 := F_1491e0.
Definition Do_0b8 := D_1491e0.
Definition Fo_0bc := F_1491e4.
Definition Do_0bc := D_1491e4.
Definition Fo_0c0 := F_1491e8.
Definition Do_0c0 := D_1491e8.
Definition Fo_0c4 := F_1491ec.
Definition Do_0c4 := D_1491ec.
Definition Fo_0c8 := F_1491f0.
Definition Do_0c8 := D_1491f0.
Definition Fo_0cc := F_1491f4.
Definition Do_0cc := D_1491f4.
Definition Fo_0d0 := F_1491f8.
Definition Do_0d0 := D_1491f8.
Definition Fo_0d4 := F_1491fc.
Definition Do_0d4 := D_1491fc.
Definition Fo_0d8 := F_149200.
Definition Do_0d8 := D_149200.
Definition Fo_0dc := F_149204.
Definition Do_0dc := D_149204.
Definition Fo_0e0 := F_149208.
Definition Do_0e0 := D_149208.
Definition Fo_0e4 := F_14920c.
Definition Do_0e4 := D_14920c.
Definition Fo_0e8 := F_149210.
Definition Do_0e8 := D_149210.
Definition Fo_0ec := F_149214.
Definition Do_0ec := D_149214.
Definition Fo_0f0 := F_149218.
Definition Do_0f0 := D_149218.
Definition Fo_0f4 := F_14921c.
Definition Do_0f4 := D_14921c.

End AsanMemset_codeK.
Module Asan_code_startxK.
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

Definition W_1371cc : bv 32 := 0x0004b503.
Lemma F_1371cc : fetch_word Asan.M.loaded_segments (0x13721c : word) = Some W_1371cc.
Proof. vm_refl. Qed.
Lemma D_1371cc : decode_any W_1371cc = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1371d0 : bv 32 := 0x00848493.
Lemma F_1371d0 : fetch_word Asan.M.loaded_segments (0x137220 : word) = Some W_1371d0.
Proof. vm_refl. Qed.
Lemma D_1371d0 : decode_any W_1371d0 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1371d4 : bv 32 := 0xfe051ce3.
Lemma F_1371d4 : fetch_word Asan.M.loaded_segments (0x137224 : word) = Some W_1371d4.
Proof. vm_refl. Qed.
Lemma D_1371d4 : decode_any W_1371d4 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_137288 : bv 32 := 0x00b53023.
Lemma F_137288 : fetch_word Asan.M.loaded_segments (0x1372d8 : word) = Some W_137288.
Proof. vm_refl. Qed.
Lemma D_137288 : decode_any W_137288 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13728c : bv 32 := 0x00158593.
Lemma F_13728c : fetch_word Asan.M.loaded_segments (0x1372dc : word) = Some W_13728c.
Proof. vm_refl. Qed.
Lemma D_13728c : decode_any W_13728c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_137290 : bv 32 := 0xfff5c683.
Lemma F_137290 : fetch_word Asan.M.loaded_segments (0x1372e0 : word) = Some W_137290.
Proof. vm_refl. Qed.
Lemma D_137290 : decode_any W_137290 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_137294 : bv 32 := 0xfec68ae3.
Lemma F_137294 : fetch_word Asan.M.loaded_segments (0x1372e4 : word) = Some W_137294.
Proof. vm_refl. Qed.
Lemma D_137294 : decode_any W_137294 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_137298 : bv 32 := 0xfe069ae3.
Lemma F_137298 : fetch_word Asan.M.loaded_segments (0x1372e8 : word) = Some W_137298.
Proof. vm_refl. Qed.
Lemma D_137298 : decode_any W_137298 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

End Asan_code_startxK.
Module Na0_code_r7af8c_7b250.
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

Definition W_82954 : bv 32 := 0x81010113.
Lemma F_82954 : fetch_word Asan.M.loaded_segments (0x829a4 : word) = Some W_82954.
Proof. vm_refl. Qed.
Lemma D_82954 : decode_any W_82954 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_82958 : bv 32 := 0x7e113423.
Lemma F_82958 : fetch_word Asan.M.loaded_segments (0x829a8 : word) = Some W_82958.
Proof. vm_refl. Qed.
Lemma D_82958 : decode_any W_82958 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_8295c : bv 32 := 0x7e813023.
Lemma F_8295c : fetch_word Asan.M.loaded_segments (0x829ac : word) = Some W_8295c.
Proof. vm_refl. Qed.
Lemma D_8295c : decode_any W_8295c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_82960 : bv 32 := 0x7c913c23.
Lemma F_82960 : fetch_word Asan.M.loaded_segments (0x829b0 : word) = Some W_82960.
Proof. vm_refl. Qed.
Lemma D_82960 : decode_any W_82960 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_82964 : bv 32 := 0x7d213823.
Lemma F_82964 : fetch_word Asan.M.loaded_segments (0x829b4 : word) = Some W_82964.
Proof. vm_refl. Qed.
Lemma D_82964 : decode_any W_82964 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_82968 : bv 32 := 0x7d313423.
Lemma F_82968 : fetch_word Asan.M.loaded_segments (0x829b8 : word) = Some W_82968.
Proof. vm_refl. Qed.
Lemma D_82968 : decode_any W_82968 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_8296c : bv 32 := 0x7d413023.
Lemma F_8296c : fetch_word Asan.M.loaded_segments (0x829bc : word) = Some W_8296c.
Proof. vm_refl. Qed.
Lemma D_8296c : decode_any W_8296c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_82970 : bv 32 := 0x7b513c23.
Lemma F_82970 : fetch_word Asan.M.loaded_segments (0x829c0 : word) = Some W_82970.
Proof. vm_refl. Qed.
Lemma D_82970 : decode_any W_82970 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_82974 : bv 32 := 0x7f010413.
Lemma F_82974 : fetch_word Asan.M.loaded_segments (0x829c4 : word) = Some W_82974.
Proof. vm_refl. Qed.
Lemma D_82974 : decode_any W_82974 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_82978 : bv 32 := 0xfa010113.
Lemma F_82978 : fetch_word Asan.M.loaded_segments (0x829c8 : word) = Some W_82978.
Proof. vm_refl. Qed.
Lemma D_82978 : decode_any W_82978 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_8297c : bv 32 := 0x00058a13.
Lemma F_8297c : fetch_word Asan.M.loaded_segments (0x829cc : word) = Some W_8297c.
Proof. vm_refl. Qed.
Lemma D_8297c : decode_any W_8297c = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82980 : bv 32 := 0x000d4597.
Lemma F_82980 : fetch_word Asan.M.loaded_segments (0x829d0 : word) = Some W_82980.
Proof. vm_refl. Qed.
Lemma D_82980 : decode_any W_82980 = Some (Auipc 11 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_82984 : bv 32 := 0x3c05b583.
Lemma F_82984 : fetch_word Asan.M.loaded_segments (0x829d4 : word) = Some W_82984.
Proof. vm_refl. Qed.
Lemma D_82984 : decode_any W_82984 = Some (Load SZ8 true 11 11 960, 4%Z).
Proof. vm_refl. Qed.

Definition W_82988 : bv 32 := 0x0605c583.
Lemma F_82988 : fetch_word Asan.M.loaded_segments (0x829d8 : word) = Some W_82988.
Proof. vm_refl. Qed.
Lemma D_82988 : decode_any W_82988 = Some (Load SZ1 false 11 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_8298c : bv 32 := 0x22058863.
Lemma F_8298c : fetch_word Asan.M.loaded_segments (0x829dc : word) = Some W_8298c.
Proof. vm_refl. Qed.
Lemma D_8298c : decode_any W_8298c = Some (Branch BC_EQ 11 0 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_82990 : bv 32 := 0x00068913.
Lemma F_82990 : fetch_word Asan.M.loaded_segments (0x829e0 : word) = Some W_82990.
Proof. vm_refl. Qed.
Lemma D_82990 : decode_any W_82990 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82994 : bv 32 := 0x00060993.
Lemma F_82994 : fetch_word Asan.M.loaded_segments (0x829e4 : word) = Some W_82994.
Proof. vm_refl. Qed.
Lemma D_82994 : decode_any W_82994 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82998 : bv 32 := 0x00050493.
Lemma F_82998 : fetch_word Asan.M.loaded_segments (0x829e8 : word) = Some W_82998.
Proof. vm_refl. Qed.
Lemma D_82998 : decode_any W_82998 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8299c : bv 32 := 0x000d4517.
Lemma F_8299c : fetch_word Asan.M.loaded_segments (0x829ec : word) = Some W_8299c.
Proof. vm_refl. Qed.
Lemma D_8299c : decode_any W_8299c = Some (Auipc 10 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_829a0 : bv 32 := 0x3fc53503.
Lemma F_829a0 : fetch_word Asan.M.loaded_segments (0x829f0 : word) = Some W_829a0.
Proof. vm_refl. Qed.
Lemma D_829a0 : decode_any W_829a0 = Some (Load SZ8 true 10 10 1020, 4%Z).
Proof. vm_refl. Qed.

Definition W_829a4 : bv 32 := 0x00052503.
Lemma F_829a4 : fetch_word Asan.M.loaded_segments (0x829f4 : word) = Some W_829a4.
Proof. vm_refl. Qed.
Lemma D_829a4 : decode_any W_829a4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_829a8 : bv 32 := 0x00300593.
Lemma F_829a8 : fetch_word Asan.M.loaded_segments (0x829f8 : word) = Some W_829a8.
Proof. vm_refl. Qed.
Lemma D_829a8 : decode_any W_829a8 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_829ac : bv 32 := 0x08b57063.
Lemma F_829ac : fetch_word Asan.M.loaded_segments (0x829fc : word) = Some W_829ac.
Proof. vm_refl. Qed.
Lemma D_829ac : decode_any W_829ac = Some (Branch BC_GEU 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_829b0 : bv 32 := 0x0899fe63.
Lemma F_829b0 : fetch_word Asan.M.loaded_segments (0x82a00 : word) = Some W_829b0.
Proof. vm_refl. Qed.
Lemma D_829b0 : decode_any W_829b0 = Some (Branch BC_GEU 19 9 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_829b4 : bv 32 := 0x80040513.
Lemma F_829b4 : fetch_word Asan.M.loaded_segments (0x82a04 : word) = Some W_829b4.
Proof. vm_refl. Qed.
Lemma D_829b4 : decode_any W_829b4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_829b8 : bv 32 := 0xfb050513.
Lemma F_829b8 : fetch_word Asan.M.loaded_segments (0x82a08 : word) = Some W_829b8.
Proof. vm_refl. Qed.
Lemma D_829b8 : decode_any W_829b8 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_829bc : bv 32 := 0x80040593.
Lemma F_829bc : fetch_word Asan.M.loaded_segments (0x82a0c : word) = Some W_829bc.
Proof. vm_refl. Qed.
Lemma D_829bc : decode_any W_829bc = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_829c0 : bv 32 := 0xfc058593.
Lemma F_829c0 : fetch_word Asan.M.loaded_segments (0x82a10 : word) = Some W_829c0.
Proof. vm_refl. Qed.
Lemma D_829c0 : decode_any W_829c0 = Some (OpImm ALU_ADD 11 11 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_829c4 : bv 32 := 0x80040613.
Lemma F_829c4 : fetch_word Asan.M.loaded_segments (0x82a14 : word) = Some W_829c4.
Proof. vm_refl. Qed.
Lemma D_829c4 : decode_any W_829c4 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_829c8 : bv 32 := 0xfb060613.
Lemma F_829c8 : fetch_word Asan.M.loaded_segments (0x82a18 : word) = Some W_829c8.
Proof. vm_refl. Qed.
Lemma D_829c8 : decode_any W_829c8 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_829cc : bv 32 := 0x7ff60a93.
Lemma F_829cc : fetch_word Asan.M.loaded_segments (0x82a1c : word) = Some W_829cc.
Proof. vm_refl. Qed.
Lemma D_829cc : decode_any W_829cc = Some (OpImm ALU_ADD 21 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_829d0 : bv 32 := 0x000ab4a3.
Lemma F_829d0 : fetch_word Asan.M.loaded_segments (0x82a20 : word) = Some W_829d0.
Proof. vm_refl. Qed.
Lemma D_829d0 : decode_any W_829d0 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_829d4 : bv 32 := 0x00b53023.
Lemma F_829d4 : fetch_word Asan.M.loaded_segments (0x82a24 : word) = Some W_829d4.
Proof. vm_refl. Qed.
Lemma D_829d4 : decode_any W_829d4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_829d8 : bv 32 := 0x00053423.
Lemma F_829d8 : fetch_word Asan.M.loaded_segments (0x82a28 : word) = Some W_829d8.
Proof. vm_refl. Qed.
Lemma D_829d8 : decode_any W_829d8 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_829dc : bv 32 := 0x6451e0ef.
Lemma F_829dc : fetch_word Asan.M.loaded_segments (0x82a2c : word) = Some W_829dc.
Proof. vm_refl. Qed.
Lemma D_829dc : decode_any W_829dc = Some (Jal 1 126532, 4%Z).
Proof. vm_refl. Qed.

Definition W_829e0 : bv 32 := 0x00050593.
Lemma F_829e0 : fetch_word Asan.M.loaded_segments (0x82a30 : word) = Some W_829e0.
Proof. vm_refl. Qed.
Lemma D_829e0 : decode_any W_829e0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_829e4 : bv 32 := 0x000d4517.
Lemma F_829e4 : fetch_word Asan.M.loaded_segments (0x82a34 : word) = Some W_829e4.
Proof. vm_refl. Qed.
Lemma D_829e4 : decode_any W_829e4 = Some (Auipc 10 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_829e8 : bv 32 := 0x35453503.
Lemma F_829e8 : fetch_word Asan.M.loaded_segments (0x82a38 : word) = Some W_829e8.
Proof. vm_refl. Qed.
Lemma D_829e8 : decode_any W_829e8 = Some (Load SZ8 true 10 10 852, 4%Z).
Proof. vm_refl. Qed.

Definition W_829ec : bv 32 := 0x02154703.
Lemma F_829ec : fetch_word Asan.M.loaded_segments (0x82a3c : word) = Some W_829ec.
Proof. vm_refl. Qed.
Lemma D_829ec : decode_any W_829ec = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_829f0 : bv 32 := 0x008ab4a3.
Lemma F_829f0 : fetch_word Asan.M.loaded_segments (0x82a40 : word) = Some W_829f0.
Proof. vm_refl. Qed.
Lemma D_829f0 : decode_any W_829f0 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_829f4 : bv 32 := 0x80040513.
Lemma F_829f4 : fetch_word Asan.M.loaded_segments (0x82a44 : word) = Some W_829f4.
Proof. vm_refl. Qed.
Lemma D_829f4 : decode_any W_829f4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_829f8 : bv 32 := 0xfb050513.
Lemma F_829f8 : fetch_word Asan.M.loaded_segments (0x82a48 : word) = Some W_829f8.
Proof. vm_refl. Qed.
Lemma D_829f8 : decode_any W_829f8 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_829fc : bv 32 := 0x0ff00793.
Lemma F_829fc : fetch_word Asan.M.loaded_segments (0x82a4c : word) = Some W_829fc.
Proof. vm_refl. Qed.
Lemma D_829fc : decode_any W_829fc = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a00 : bv 32 := 0x00040613.
Lemma F_82a00 : fetch_word Asan.M.loaded_segments (0x82a50 : word) = Some W_82a00.
Proof. vm_refl. Qed.
Lemma D_82a00 : decode_any W_82a00 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a04 : bv 32 := 0x00000693.
Lemma F_82a04 : fetch_word Asan.M.loaded_segments (0x82a54 : word) = Some W_82a04.
Proof. vm_refl. Qed.
Lemma D_82a04 : decode_any W_82a04 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a08 : bv 32 := 0x34c060ef.
Lemma F_82a08 : fetch_word Asan.M.loaded_segments (0x82a58 : word) = Some W_82a08.
Proof. vm_refl. Qed.
Lemma D_82a08 : decode_any W_82a08 = Some (Jal 1 25420, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a0c : bv 32 := 0x80040713.
Lemma F_82a0c : fetch_word Asan.M.loaded_segments (0x82a5c : word) = Some W_82a0c.
Proof. vm_refl. Qed.
Lemma D_82a0c : decode_any W_82a0c = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a10 : bv 32 := 0xfb070713.
Lemma F_82a10 : fetch_word Asan.M.loaded_segments (0x82a60 : word) = Some W_82a10.
Proof. vm_refl. Qed.
Lemma D_82a10 : decode_any W_82a10 = Some (OpImm ALU_ADD 14 14 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a14 : bv 32 := 0x00048513.
Lemma F_82a14 : fetch_word Asan.M.loaded_segments (0x82a64 : word) = Some W_82a14.
Proof. vm_refl. Qed.
Lemma D_82a14 : decode_any W_82a14 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a18 : bv 32 := 0x000a0593.
Lemma F_82a18 : fetch_word Asan.M.loaded_segments (0x82a68 : word) = Some W_82a18.
Proof. vm_refl. Qed.
Lemma D_82a18 : decode_any W_82a18 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a1c : bv 32 := 0x00098613.
Lemma F_82a1c : fetch_word Asan.M.loaded_segments (0x82a6c : word) = Some W_82a1c.
Proof. vm_refl. Qed.
Lemma D_82a1c : decode_any W_82a1c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a20 : bv 32 := 0x00090693.
Lemma F_82a20 : fetch_word Asan.M.loaded_segments (0x82a70 : word) = Some W_82a20.
Proof. vm_refl. Qed.
Lemma D_82a20 : decode_any W_82a20 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a24 : bv 32 := 0x0e0030ef.
Lemma F_82a24 : fetch_word Asan.M.loaded_segments (0x82a74 : word) = Some W_82a24.
Proof. vm_refl. Qed.
Lemma D_82a24 : decode_any W_82a24 = Some (Jal 1 12512, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a28 : bv 32 := 0x0300006f.
Lemma F_82a28 : fetch_word Asan.M.loaded_segments (0x82a78 : word) = Some W_82a28.
Proof. vm_refl. Qed.
Lemma D_82a28 : decode_any W_82a28 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a2c : bv 32 := 0xfff97517.
Lemma F_82a2c : fetch_word Asan.M.loaded_segments (0x82a7c : word) = Some W_82a2c.
Proof. vm_refl. Qed.
Lemma D_82a2c : decode_any W_82a2c = Some (Auipc 10 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a30 : bv 32 := 0xbe650513.
Lemma F_82a30 : fetch_word Asan.M.loaded_segments (0x82a80 : word) = Some W_82a30.
Proof. vm_refl. Qed.
Lemma D_82a30 : decode_any W_82a30 = Some (OpImm ALU_ADD 10 10 3046, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a34 : bv 32 := 0x00048593.
Lemma F_82a34 : fetch_word Asan.M.loaded_segments (0x82a84 : word) = Some W_82a34.
Proof. vm_refl. Qed.
Lemma D_82a34 : decode_any W_82a34 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a38 : bv 32 := 0x000a0613.
Lemma F_82a38 : fetch_word Asan.M.loaded_segments (0x82a88 : word) = Some W_82a38.
Proof. vm_refl. Qed.
Lemma D_82a38 : decode_any W_82a38 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a3c : bv 32 := 0x00098693.
Lemma F_82a3c : fetch_word Asan.M.loaded_segments (0x82a8c : word) = Some W_82a3c.
Proof. vm_refl. Qed.
Lemma D_82a3c : decode_any W_82a3c = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a40 : bv 32 := 0x00090713.
Lemma F_82a40 : fetch_word Asan.M.loaded_segments (0x82a90 : word) = Some W_82a40.
Proof. vm_refl. Qed.
Lemma D_82a40 : decode_any W_82a40 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a44 : bv 32 := 0x491120ef.
Lemma F_82a44 : fetch_word Asan.M.loaded_segments (0x82a94 : word) = Some W_82a44.
Proof. vm_refl. Qed.
Lemma D_82a44 : decode_any W_82a44 = Some (Jal 1 76944, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a48 : bv 32 := 0xf699e6e3.
Lemma F_82a48 : fetch_word Asan.M.loaded_segments (0x82a98 : word) = Some W_82a48.
Proof. vm_refl. Qed.
Lemma D_82a48 : decode_any W_82a48 = Some (Branch BC_LTU 19 9 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a4c : bv 32 := 0xf72a64e3.
Lemma F_82a4c : fetch_word Asan.M.loaded_segments (0x82a9c : word) = Some W_82a4c.
Proof. vm_refl. Qed.
Lemma D_82a4c : decode_any W_82a4c = Some (Branch BC_LTU 20 18 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a50 : bv 32 := 0xf73a62e3.
Lemma F_82a50 : fetch_word Asan.M.loaded_segments (0x82aa0 : word) = Some W_82a50.
Proof. vm_refl. Qed.
Lemma D_82a50 : decode_any W_82a50 = Some (Branch BC_LTU 20 19 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a54 : bv 32 := 0xf69960e3.
Lemma F_82a54 : fetch_word Asan.M.loaded_segments (0x82aa4 : word) = Some W_82a54.
Proof. vm_refl. Qed.
Lemma D_82a54 : decode_any W_82a54 = Some (Branch BC_LTU 18 9 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a58 : bv 32 := 0x409a06b3.
Lemma F_82a58 : fetch_word Asan.M.loaded_segments (0x82aa8 : word) = Some W_82a58.
Proof. vm_refl. Qed.
Lemma D_82a58 : decode_any W_82a58 = Some (Op ALU_SUB 13 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a5c : bv 32 := 0x00100713.
Lemma F_82a5c : fetch_word Asan.M.loaded_segments (0x82aac : word) = Some W_82a5c.
Proof. vm_refl. Qed.
Lemma D_82a5c : decode_any W_82a5c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a60 : bv 32 := 0x02871713.
Lemma F_82a60 : fetch_word Asan.M.loaded_segments (0x82ab0 : word) = Some W_82a60.
Proof. vm_refl. Qed.
Lemma D_82a60 : decode_any W_82a60 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a64 : bv 32 := 0x00170513.
Lemma F_82a64 : fetch_word Asan.M.loaded_segments (0x82ab4 : word) = Some W_82a64.
Proof. vm_refl. Qed.
Lemma D_82a64 : decode_any W_82a64 = Some (OpImm ALU_ADD 10 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a68 : bv 32 := 0x04a6fa63.
Lemma F_82a68 : fetch_word Asan.M.loaded_segments (0x82ab8 : word) = Some W_82a68.
Proof. vm_refl. Qed.
Lemma D_82a68 : decode_any W_82a68 = Some (Branch BC_GEU 13 10 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a6c : bv 32 := 0x15298863.
Lemma F_82a6c : fetch_word Asan.M.loaded_segments (0x82abc : word) = Some W_82a6c.
Proof. vm_refl. Qed.
Lemma D_82a6c : decode_any W_82a6c = Some (Branch BC_EQ 19 18 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a70 : bv 32 := 0x007a7513.
Lemma F_82a70 : fetch_word Asan.M.loaded_segments (0x82ac0 : word) = Some W_82a70.
Proof. vm_refl. Qed.
Lemma D_82a70 : decode_any W_82a70 = Some (OpImm ALU_AND 10 20 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a74 : bv 32 := 0x06051063.
Lemma F_82a74 : fetch_word Asan.M.loaded_segments (0x82ac4 : word) = Some W_82a74.
Proof. vm_refl. Qed.
Lemma D_82a74 : decode_any W_82a74 = Some (Branch BC_NE 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a78 : bv 32 := 0x00098a13.
Lemma F_82a78 : fetch_word Asan.M.loaded_segments (0x82ac8 : word) = Some W_82a78.
Proof. vm_refl. Qed.
Lemma D_82a78 : decode_any W_82a78 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a7c : bv 32 := 0x00090a93.
Lemma F_82a7c : fetch_word Asan.M.loaded_segments (0x82acc : word) = Some W_82a7c.
Proof. vm_refl. Qed.
Lemma D_82a7c : decode_any W_82a7c = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a80 : bv 32 := 0x00048513.
Lemma F_82a80 : fetch_word Asan.M.loaded_segments (0x82ad0 : word) = Some W_82a80.
Proof. vm_refl. Qed.
Lemma D_82a80 : decode_any W_82a80 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a84 : bv 32 := 0x0074f993.
Lemma F_82a84 : fetch_word Asan.M.loaded_segments (0x82ad4 : word) = Some W_82a84.
Proof. vm_refl. Qed.
Lemma D_82a84 : decode_any W_82a84 = Some (OpImm ALU_AND 19 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a88 : bv 32 := 0x08099e63.
Lemma F_82a88 : fetch_word Asan.M.loaded_segments (0x82ad8 : word) = Some W_82a88.
Proof. vm_refl. Qed.
Lemma D_82a88 : decode_any W_82a88 = Some (Branch BC_NE 19 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a8c : bv 32 := 0x000a0593.
Lemma F_82a8c : fetch_word Asan.M.loaded_segments (0x82adc : word) = Some W_82a8c.
Proof. vm_refl. Qed.
Lemma D_82a8c : decode_any W_82a8c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a90 : bv 32 := 0x000a0513.
Lemma F_82a90 : fetch_word Asan.M.loaded_segments (0x82ae0 : word) = Some W_82a90.
Proof. vm_refl. Qed.
Lemma D_82a90 : decode_any W_82a90 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a94 : bv 32 := 0x0d5a6863.
Lemma F_82a94 : fetch_word Asan.M.loaded_segments (0x82ae4 : word) = Some W_82a94.
Proof. vm_refl. Qed.
Lemma D_82a94 : decode_any W_82a94 = Some (Branch BC_LTU 20 21 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a98 : bv 32 := 0xff8af513.
Lemma F_82a98 : fetch_word Asan.M.loaded_segments (0x82ae8 : word) = Some W_82a98.
Proof. vm_refl. Qed.
Lemma D_82a98 : decode_any W_82a98 = Some (OpImm ALU_AND 10 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82a9c : bv 32 := 0x0cbaf863.
Lemma F_82a9c : fetch_word Asan.M.loaded_segments (0x82aec : word) = Some W_82a9c.
Proof. vm_refl. Qed.
Lemma D_82a9c : decode_any W_82a9c = Some (Branch BC_GEU 21 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aa0 : bv 32 := 0xff8af493.
Lemma F_82aa0 : fetch_word Asan.M.loaded_segments (0x82af0 : word) = Some W_82aa0.
Proof. vm_refl. Qed.
Lemma D_82aa0 : decode_any W_82aa0 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aa4 : bv 32 := 0x007a8613.
Lemma F_82aa4 : fetch_word Asan.M.loaded_segments (0x82af4 : word) = Some W_82aa4.
Proof. vm_refl. Qed.
Lemma D_82aa4 : decode_any W_82aa4 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aa8 : bv 32 := 0xff867913.
Lemma F_82aa8 : fetch_word Asan.M.loaded_segments (0x82af8 : word) = Some W_82aa8.
Proof. vm_refl. Qed.
Lemma D_82aa8 : decode_any W_82aa8 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aac : bv 32 := 0x0c957a63.
Lemma F_82aac : fetch_word Asan.M.loaded_segments (0x82afc : word) = Some W_82aac.
Proof. vm_refl. Qed.
Lemma D_82aac : decode_any W_82aac = Some (Branch BC_GEU 10 9 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ab0 : bv 32 := 0x40a485b3.
Lemma F_82ab0 : fetch_word Asan.M.loaded_segments (0x82b00 : word) = Some W_82ab0.
Proof. vm_refl. Qed.
Lemma D_82ab0 : decode_any W_82ab0 = Some (Op ALU_SUB 11 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ab4 : bv 32 := 0x00000613.
Lemma F_82ab4 : fetch_word Asan.M.loaded_segments (0x82b04 : word) = Some W_82ab4.
Proof. vm_refl. Qed.
Lemma D_82ab4 : decode_any W_82ab4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ab8 : bv 32 := 0x0e00006f.
Lemma F_82ab8 : fetch_word Asan.M.loaded_segments (0x82b08 : word) = Some W_82ab8.
Proof. vm_refl. Qed.
Lemma D_82ab8 : decode_any W_82ab8 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_82abc : bv 32 := 0xfff9f517.
Lemma F_82abc : fetch_word Asan.M.loaded_segments (0x82b0c : word) = Some W_82abc.
Proof. vm_refl. Qed.
Lemma D_82abc : decode_any W_82abc = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ac0 : bv 32 := 0xfffa0597.
Lemma F_82ac0 : fetch_word Asan.M.loaded_segments (0x82b10 : word) = Some W_82ac0.
Proof. vm_refl. Qed.
Lemma D_82ac0 : decode_any W_82ac0 = Some (Auipc 11 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ac4 : bv 32 := 0xf4550513.
Lemma F_82ac4 : fetch_word Asan.M.loaded_segments (0x82b14 : word) = Some W_82ac4.
Proof. vm_refl. Qed.
Lemma D_82ac4 : decode_any W_82ac4 = Some (OpImm ALU_ADD 10 10 3909, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ac8 : bv 32 := 0x0d258613.
Lemma F_82ac8 : fetch_word Asan.M.loaded_segments (0x82b18 : word) = Some W_82ac8.
Proof. vm_refl. Qed.
Lemma D_82ac8 : decode_any W_82ac8 = Some (OpImm ALU_ADD 12 11 210, 4%Z).
Proof. vm_refl. Qed.

Definition W_82acc : bv 32 := 0x1b600593.
Lemma F_82acc : fetch_word Asan.M.loaded_segments (0x82b1c : word) = Some W_82acc.
Proof. vm_refl. Qed.
Lemma D_82acc : decode_any W_82acc = Some (OpImm ALU_ADD 11 0 438, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ad0 : bv 32 := 0x58c170ef.
Lemma F_82ad0 : fetch_word Asan.M.loaded_segments (0x82b20 : word) = Some W_82ad0.
Proof. vm_refl. Qed.
Lemma D_82ad0 : decode_any W_82ad0 = Some (Jal 1 95628, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ad4 : bv 32 := 0xff8a7a93.
Lemma F_82ad4 : fetch_word Asan.M.loaded_segments (0x82b24 : word) = Some W_82ad4.
Proof. vm_refl. Qed.
Lemma D_82ad4 : decode_any W_82ad4 = Some (OpImm ALU_AND 21 20 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ad8 : bv 32 := 0x00098593.
Lemma F_82ad8 : fetch_word Asan.M.loaded_segments (0x82b28 : word) = Some W_82ad8.
Proof. vm_refl. Qed.
Lemma D_82ad8 : decode_any W_82ad8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82adc : bv 32 := 0x01396463.
Lemma F_82adc : fetch_word Asan.M.loaded_segments (0x82b2c : word) = Some W_82adc.
Proof. vm_refl. Qed.
Lemma D_82adc : decode_any W_82adc = Some (Branch BC_LTU 18 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ae0 : bv 32 := 0x00090593.
Lemma F_82ae0 : fetch_word Asan.M.loaded_segments (0x82b30 : word) = Some W_82ae0.
Proof. vm_refl. Qed.
Lemma D_82ae0 : decode_any W_82ae0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ae4 : bv 32 := 0xf8bafae3.
Lemma F_82ae4 : fetch_word Asan.M.loaded_segments (0x82b34 : word) = Some W_82ae4.
Proof. vm_refl. Qed.
Lemma D_82ae4 : decode_any W_82ae4 = Some (Branch BC_GEU 21 11 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ae8 : bv 32 := 0x000d4597.
Lemma F_82ae8 : fetch_word Asan.M.loaded_segments (0x82b38 : word) = Some W_82ae8.
Proof. vm_refl. Qed.
Lemma D_82ae8 : decode_any W_82ae8 = Some (Auipc 11 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_82aec : bv 32 := 0x2605b583.
Lemma F_82aec : fetch_word Asan.M.loaded_segments (0x82b3c : word) = Some W_82aec.
Proof. vm_refl. Qed.
Lemma D_82aec : decode_any W_82aec = Some (Load SZ8 true 11 11 608, 4%Z).
Proof. vm_refl. Qed.

Definition W_82af0 : bv 32 := 0x0005b583.
Lemma F_82af0 : fetch_word Asan.M.loaded_segments (0x82b40 : word) = Some W_82af0.
Proof. vm_refl. Qed.
Lemma D_82af0 : decode_any W_82af0 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82af4 : bv 32 := 0x003a5613.
Lemma F_82af4 : fetch_word Asan.M.loaded_segments (0x82b44 : word) = Some W_82af4.
Proof. vm_refl. Qed.
Lemma D_82af4 : decode_any W_82af4 = Some (ShiftImm ALU_SRL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_82af8 : bv 32 := 0x00c585b3.
Lemma F_82af8 : fetch_word Asan.M.loaded_segments (0x82b48 : word) = Some W_82af8.
Proof. vm_refl. Qed.
Lemma D_82af8 : decode_any W_82af8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82afc : bv 32 := 0x00058583.
Lemma F_82afc : fetch_word Asan.M.loaded_segments (0x82b4c : word) = Some W_82afc.
Proof. vm_refl. Qed.
Lemma D_82afc : decode_any W_82afc = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b00 : bv 32 := 0x00058463.
Lemma F_82b00 : fetch_word Asan.M.loaded_segments (0x82b50 : word) = Some W_82b00.
Proof. vm_refl. Qed.
Lemma D_82b00 : decode_any W_82b00 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b04 : bv 32 := 0xf6b55ae3.
Lemma F_82b04 : fetch_word Asan.M.loaded_segments (0x82b54 : word) = Some W_82b04.
Proof. vm_refl. Qed.
Lemma D_82b04 : decode_any W_82b04 = Some (Branch BC_GE 10 11 8052, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b08 : bv 32 := 0x000a8513.
Lemma F_82b08 : fetch_word Asan.M.loaded_segments (0x82b58 : word) = Some W_82b08.
Proof. vm_refl. Qed.
Lemma D_82b08 : decode_any W_82b08 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b0c : bv 32 := 0x0e9aea63.
Lemma F_82b0c : fetch_word Asan.M.loaded_segments (0x82b5c : word) = Some W_82b0c.
Proof. vm_refl. Qed.
Lemma D_82b0c : decode_any W_82b0c = Some (Branch BC_LTU 21 9 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b10 : bv 32 := 0x00048513.
Lemma F_82b10 : fetch_word Asan.M.loaded_segments (0x82b60 : word) = Some W_82b10.
Proof. vm_refl. Qed.
Lemma D_82b10 : decode_any W_82b10 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b14 : bv 32 := 0x000a8a13.
Lemma F_82b14 : fetch_word Asan.M.loaded_segments (0x82b64 : word) = Some W_82b14.
Proof. vm_refl. Qed.
Lemma D_82b14 : decode_any W_82b14 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b18 : bv 32 := 0x0f3af863.
Lemma F_82b18 : fetch_word Asan.M.loaded_segments (0x82b68 : word) = Some W_82b18.
Proof. vm_refl. Qed.
Lemma D_82b18 : decode_any W_82b18 = Some (Branch BC_GEU 21 19 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b1c : bv 32 := 0xf72ae4e3.
Lemma F_82b1c : fetch_word Asan.M.loaded_segments (0x82b6c : word) = Some W_82b1c.
Proof. vm_refl. Qed.
Lemma D_82b1c : decode_any W_82b1c = Some (Branch BC_LTU 21 18 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b20 : bv 32 := 0x0f00006f.
Lemma F_82b20 : fetch_word Asan.M.loaded_segments (0x82b70 : word) = Some W_82b20.
Proof. vm_refl. Qed.
Lemma D_82b20 : decode_any W_82b20 = Some (Jal 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b24 : bv 32 := 0xf74504e3.
Lemma F_82b24 : fetch_word Asan.M.loaded_segments (0x82b74 : word) = Some W_82b24.
Proof. vm_refl. Qed.
Lemma D_82b24 : decode_any W_82b24 = Some (Branch BC_EQ 10 20 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b28 : bv 32 := 0xf75512e3.
Lemma F_82b28 : fetch_word Asan.M.loaded_segments (0x82b78 : word) = Some W_82b28.
Proof. vm_refl. Qed.
Lemma D_82b28 : decode_any W_82b28 = Some (Branch BC_NE 10 21 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b2c : bv 32 := 0x00748593.
Lemma F_82b2c : fetch_word Asan.M.loaded_segments (0x82b7c : word) = Some W_82b2c.
Proof. vm_refl. Qed.
Lemma D_82b2c : decode_any W_82b2c = Some (OpImm ALU_ADD 11 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b30 : bv 32 := 0xff85f913.
Lemma F_82b30 : fetch_word Asan.M.loaded_segments (0x82b80 : word) = Some W_82b30.
Proof. vm_refl. Qed.
Lemma D_82b30 : decode_any W_82b30 = Some (OpImm ALU_AND 18 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b34 : bv 32 := 0xf5257ce3.
Lemma F_82b34 : fetch_word Asan.M.loaded_segments (0x82b84 : word) = Some W_82b34.
Proof. vm_refl. Qed.
Lemma D_82b34 : decode_any W_82b34 = Some (Branch BC_GEU 10 18 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b38 : bv 32 := 0xff84f513.
Lemma F_82b38 : fetch_word Asan.M.loaded_segments (0x82b88 : word) = Some W_82b38.
Proof. vm_refl. Qed.
Lemma D_82b38 : decode_any W_82b38 = Some (OpImm ALU_AND 10 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b3c : bv 32 := 0xbd0ff0ef.
Lemma F_82b3c : fetch_word Asan.M.loaded_segments (0x82b8c : word) = Some W_82b3c.
Proof. vm_refl. Qed.
Lemma D_82b3c : decode_any W_82b3c = Some (Jal 1 2094032, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b40 : bv 32 := 0x01350023.
Lemma F_82b40 : fetch_word Asan.M.loaded_segments (0x82b90 : word) = Some W_82b40.
Proof. vm_refl. Qed.
Lemma D_82b40 : decode_any W_82b40 = Some (Store SZ1 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b44 : bv 32 := 0x00090593.
Lemma F_82b44 : fetch_word Asan.M.loaded_segments (0x82b94 : word) = Some W_82b44.
Proof. vm_refl. Qed.
Lemma D_82b44 : decode_any W_82b44 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b48 : bv 32 := 0x012a6463.
Lemma F_82b48 : fetch_word Asan.M.loaded_segments (0x82b98 : word) = Some W_82b48.
Proof. vm_refl. Qed.
Lemma D_82b48 : decode_any W_82b48 = Some (Branch BC_LTU 20 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b4c : bv 32 := 0x000a0593.
Lemma F_82b4c : fetch_word Asan.M.loaded_segments (0x82b9c : word) = Some W_82b4c.
Proof. vm_refl. Qed.
Lemma D_82b4c : decode_any W_82b4c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b50 : bv 32 := 0x012ae463.
Lemma F_82b50 : fetch_word Asan.M.loaded_segments (0x82ba0 : word) = Some W_82b50.
Proof. vm_refl. Qed.
Lemma D_82b50 : decode_any W_82b50 = Some (Branch BC_LTU 21 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b54 : bv 32 := 0x000a8913.
Lemma F_82b54 : fetch_word Asan.M.loaded_segments (0x82ba4 : word) = Some W_82b54.
Proof. vm_refl. Qed.
Lemma D_82b54 : decode_any W_82b54 = Some (OpImm ALU_ADD 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b58 : bv 32 := 0x00090a93.
Lemma F_82b58 : fetch_word Asan.M.loaded_segments (0x82ba8 : word) = Some W_82b58.
Proof. vm_refl. Qed.
Lemma D_82b58 : decode_any W_82b58 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b5c : bv 32 := 0x00058513.
Lemma F_82b5c : fetch_word Asan.M.loaded_segments (0x82bac : word) = Some W_82b5c.
Proof. vm_refl. Qed.
Lemma D_82b5c : decode_any W_82b5c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b60 : bv 32 := 0xf325fce3.
Lemma F_82b60 : fetch_word Asan.M.loaded_segments (0x82bb0 : word) = Some W_82b60.
Proof. vm_refl. Qed.
Lemma D_82b60 : decode_any W_82b60 = Some (Branch BC_GEU 11 18 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b64 : bv 32 := 0xff857513.
Lemma F_82b64 : fetch_word Asan.M.loaded_segments (0x82bb4 : word) = Some W_82b64.
Proof. vm_refl. Qed.
Lemma D_82b64 : decode_any W_82b64 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b68 : bv 32 := 0xf2baece3.
Lemma F_82b68 : fetch_word Asan.M.loaded_segments (0x82bb8 : word) = Some W_82b68.
Proof. vm_refl. Qed.
Lemma D_82b68 : decode_any W_82b68 = Some (Branch BC_LTU 21 11 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b6c : bv 32 := 0x000a8593.
Lemma F_82b6c : fetch_word Asan.M.loaded_segments (0x82bbc : word) = Some W_82b6c.
Proof. vm_refl. Qed.
Lemma D_82b6c : decode_any W_82b6c = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b70 : bv 32 := 0xff8af493.
Lemma F_82b70 : fetch_word Asan.M.loaded_segments (0x82bc0 : word) = Some W_82b70.
Proof. vm_refl. Qed.
Lemma D_82b70 : decode_any W_82b70 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b74 : bv 32 := 0x007a8613.
Lemma F_82b74 : fetch_word Asan.M.loaded_segments (0x82bc4 : word) = Some W_82b74.
Proof. vm_refl. Qed.
Lemma D_82b74 : decode_any W_82b74 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b78 : bv 32 := 0xff867913.
Lemma F_82b78 : fetch_word Asan.M.loaded_segments (0x82bc8 : word) = Some W_82b78.
Proof. vm_refl. Qed.
Lemma D_82b78 : decode_any W_82b78 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b7c : bv 32 := 0xf2956ae3.
Lemma F_82b7c : fetch_word Asan.M.loaded_segments (0x82bcc : word) = Some W_82b7c.
Proof. vm_refl. Qed.
Lemma D_82b7c : decode_any W_82b7c = Some (Branch BC_LTU 10 9 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b80 : bv 32 := 0x00758513.
Lemma F_82b80 : fetch_word Asan.M.loaded_segments (0x82bd0 : word) = Some W_82b80.
Proof. vm_refl. Qed.
Lemma D_82b80 : decode_any W_82b80 = Some (OpImm ALU_ADD 10 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b84 : bv 32 := 0xff857513.
Lemma F_82b84 : fetch_word Asan.M.loaded_segments (0x82bd4 : word) = Some W_82b84.
Proof. vm_refl. Qed.
Lemma D_82b84 : decode_any W_82b84 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b88 : bv 32 := 0x00a97a63.
Lemma F_82b88 : fetch_word Asan.M.loaded_segments (0x82bd8 : word) = Some W_82b88.
Proof. vm_refl. Qed.
Lemma D_82b88 : decode_any W_82b88 = Some (Branch BC_GEU 18 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b8c : bv 32 := 0x412505b3.
Lemma F_82b8c : fetch_word Asan.M.loaded_segments (0x82bdc : word) = Some W_82b8c.
Proof. vm_refl. Qed.
Lemma D_82b8c : decode_any W_82b8c = Some (Op ALU_SUB 11 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b90 : bv 32 := 0x0fc00613.
Lemma F_82b90 : fetch_word Asan.M.loaded_segments (0x82be0 : word) = Some W_82b90.
Proof. vm_refl. Qed.
Lemma D_82b90 : decode_any W_82b90 = Some (OpImm ALU_ADD 12 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b94 : bv 32 := 0x00090513.
Lemma F_82b94 : fetch_word Asan.M.loaded_segments (0x82be4 : word) = Some W_82b94.
Proof. vm_refl. Qed.
Lemma D_82b94 : decode_any W_82b94 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b98 : bv 32 := 0xe79fe0ef.
Lemma F_82b98 : fetch_word Asan.M.loaded_segments (0x82be8 : word) = Some W_82b98.
Proof. vm_refl. Qed.
Lemma D_82b98 : decode_any W_82b98 = Some (Jal 1 2092664, 4%Z).
Proof. vm_refl. Qed.

Definition W_82b9c : bv 32 := 0x02990063.
Lemma F_82b9c : fetch_word Asan.M.loaded_segments (0x82bec : word) = Some W_82b9c.
Proof. vm_refl. Qed.
Lemma D_82b9c : decode_any W_82b9c = Some (Branch BC_EQ 18 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ba0 : bv 32 := 0x409906b3.
Lemma F_82ba0 : fetch_word Asan.M.loaded_segments (0x82bf0 : word) = Some W_82ba0.
Proof. vm_refl. Qed.
Lemma D_82ba0 : decode_any W_82ba0 = Some (Op ALU_SUB 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ba4 : bv 32 := 0x00800513.
Lemma F_82ba4 : fetch_word Asan.M.loaded_segments (0x82bf4 : word) = Some W_82ba4.
Proof. vm_refl. Qed.
Lemma D_82ba4 : decode_any W_82ba4 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82ba8 : bv 32 := 0x02a69e63.
Lemma F_82ba8 : fetch_word Asan.M.loaded_segments (0x82bf8 : word) = Some W_82ba8.
Proof. vm_refl. Qed.
Lemma D_82ba8 : decode_any W_82ba8 = Some (Branch BC_NE 13 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bac : bv 32 := 0x007af913.
Lemma F_82bac : fetch_word Asan.M.loaded_segments (0x82bfc : word) = Some W_82bac.
Proof. vm_refl. Qed.
Lemma D_82bac : decode_any W_82bac = Some (OpImm ALU_AND 18 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bb0 : bv 32 := 0x00048513.
Lemma F_82bb0 : fetch_word Asan.M.loaded_segments (0x82c00 : word) = Some W_82bb0.
Proof. vm_refl. Qed.
Lemma D_82bb0 : decode_any W_82bb0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bb4 : bv 32 := 0xb58ff0ef.
Lemma F_82bb4 : fetch_word Asan.M.loaded_segments (0x82c04 : word) = Some W_82bb4.
Proof. vm_refl. Qed.
Lemma D_82bb4 : decode_any W_82bb4 = Some (Jal 1 2093912, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bb8 : bv 32 := 0x01250023.
Lemma F_82bb8 : fetch_word Asan.M.loaded_segments (0x82c08 : word) = Some W_82bb8.
Proof. vm_refl. Qed.
Lemma D_82bb8 : decode_any W_82bb8 = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bbc : bv 32 := 0x06010113.
Lemma F_82bbc : fetch_word Asan.M.loaded_segments (0x82c0c : word) = Some W_82bbc.
Proof. vm_refl. Qed.
Lemma D_82bbc : decode_any W_82bbc = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bc0 : bv 32 := 0x7e813083.
Lemma F_82bc0 : fetch_word Asan.M.loaded_segments (0x82c10 : word) = Some W_82bc0.
Proof. vm_refl. Qed.
Lemma D_82bc0 : decode_any W_82bc0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bc4 : bv 32 := 0x7e013403.
Lemma F_82bc4 : fetch_word Asan.M.loaded_segments (0x82c14 : word) = Some W_82bc4.
Proof. vm_refl. Qed.
Lemma D_82bc4 : decode_any W_82bc4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bc8 : bv 32 := 0x7d813483.
Lemma F_82bc8 : fetch_word Asan.M.loaded_segments (0x82c18 : word) = Some W_82bc8.
Proof. vm_refl. Qed.
Lemma D_82bc8 : decode_any W_82bc8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bcc : bv 32 := 0x7d013903.
Lemma F_82bcc : fetch_word Asan.M.loaded_segments (0x82c1c : word) = Some W_82bcc.
Proof. vm_refl. Qed.
Lemma D_82bcc : decode_any W_82bcc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bd0 : bv 32 := 0x7c813983.
Lemma F_82bd0 : fetch_word Asan.M.loaded_segments (0x82c20 : word) = Some W_82bd0.
Proof. vm_refl. Qed.
Lemma D_82bd0 : decode_any W_82bd0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bd4 : bv 32 := 0x7c013a03.
Lemma F_82bd4 : fetch_word Asan.M.loaded_segments (0x82c24 : word) = Some W_82bd4.
Proof. vm_refl. Qed.
Lemma D_82bd4 : decode_any W_82bd4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bd8 : bv 32 := 0x7b813a83.
Lemma F_82bd8 : fetch_word Asan.M.loaded_segments (0x82c28 : word) = Some W_82bd8.
Proof. vm_refl. Qed.
Lemma D_82bd8 : decode_any W_82bd8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bdc : bv 32 := 0x7f010113.
Lemma F_82bdc : fetch_word Asan.M.loaded_segments (0x82c2c : word) = Some W_82bdc.
Proof. vm_refl. Qed.
Lemma D_82bdc : decode_any W_82bdc = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_82be0 : bv 32 := 0x00008067.
Lemma F_82be0 : fetch_word Asan.M.loaded_segments (0x82c30 : word) = Some W_82be0.
Proof. vm_refl. Qed.
Lemma D_82be0 : decode_any W_82be0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82be4 : bv 32 := 0xfff9f517.
Lemma F_82be4 : fetch_word Asan.M.loaded_segments (0x82c34 : word) = Some W_82be4.
Proof. vm_refl. Qed.
Lemma D_82be4 : decode_any W_82be4 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_82be8 : bv 32 := 0xfff96617.
Lemma F_82be8 : fetch_word Asan.M.loaded_segments (0x82c38 : word) = Some W_82be8.
Proof. vm_refl. Qed.
Lemma D_82be8 : decode_any W_82be8 = Some (Auipc 12 1048470, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bec : bv 32 := 0x1dc00593.
Lemma F_82bec : fetch_word Asan.M.loaded_segments (0x82c3c : word) = Some W_82bec.
Proof. vm_refl. Qed.
Lemma D_82bec : decode_any W_82bec = Some (OpImm ALU_ADD 11 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bf0 : bv 32 := 0xe1d50513.
Lemma F_82bf0 : fetch_word Asan.M.loaded_segments (0x82c40 : word) = Some W_82bf0.
Proof. vm_refl. Qed.
Lemma D_82bf0 : decode_any W_82bf0 = Some (OpImm ALU_ADD 10 10 3613, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bf4 : bv 32 := 0x00060613.
Lemma F_82bf4 : fetch_word Asan.M.loaded_segments (0x82c44 : word) = Some W_82bf4.
Proof. vm_refl. Qed.
Lemma D_82bf4 : decode_any W_82bf4 = Some (OpImm ALU_ADD 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bf8 : bv 32 := 0x00800713.
Lemma F_82bf8 : fetch_word Asan.M.loaded_segments (0x82c48 : word) = Some W_82bf8.
Proof. vm_refl. Qed.
Lemma D_82bf8 : decode_any W_82bf8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_82bfc : bv 32 := 0x460170ef.
Lemma F_82bfc : fetch_word Asan.M.loaded_segments (0x82c4c : word) = Some W_82bfc.
Proof. vm_refl. Qed.
Lemma D_82bfc : decode_any W_82bfc = Some (Jal 1 95328, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c00 : bv 32 := 0x000a8a13.
Lemma F_82c00 : fetch_word Asan.M.loaded_segments (0x82c50 : word) = Some W_82c00.
Proof. vm_refl. Qed.
Lemma D_82c00 : decode_any W_82c00 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c04 : bv 32 := 0xf13aece3.
Lemma F_82c04 : fetch_word Asan.M.loaded_segments (0x82c54 : word) = Some W_82c04.
Proof. vm_refl. Qed.
Lemma D_82c04 : decode_any W_82c04 = Some (Branch BC_LTU 21 19 7960, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c08 : bv 32 := 0x00098a13.
Lemma F_82c08 : fetch_word Asan.M.loaded_segments (0x82c58 : word) = Some W_82c08.
Proof. vm_refl. Qed.
Lemma D_82c08 : decode_any W_82c08 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c0c : bv 32 := 0xe72aece3.
Lemma F_82c0c : fetch_word Asan.M.loaded_segments (0x82c5c : word) = Some W_82c0c.
Proof. vm_refl. Qed.
Lemma D_82c0c : decode_any W_82c0c = Some (Branch BC_LTU 21 18 7800, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c10 : bv 32 := 0x00090a93.
Lemma F_82c10 : fetch_word Asan.M.loaded_segments (0x82c60 : word) = Some W_82c10.
Proof. vm_refl. Qed.
Lemma D_82c10 : decode_any W_82c10 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82c14 : bv 32 := 0xe71ff06f.
Lemma F_82c14 : fetch_word Asan.M.loaded_segments (0x82c64 : word) = Some W_82c14.
Proof. vm_refl. Qed.
Lemma D_82c14 : decode_any W_82c14 = Some (Jal 0 2096752, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r7af8c_7b250.
