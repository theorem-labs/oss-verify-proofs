(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
Module Na0_code_r60dd4_61420.
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

Definition W_819fc : bv 32 := 0x000de517.
Lemma F_819fc : fetch_word Asan.M.loaded_segments (0x81a4c : word) = Some W_819fc.
Proof. vm_refl. Qed.
Lemma D_819fc : decode_any W_819fc = Some (Auipc 10 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a00 : bv 32 := 0x89050503.
Lemma F_81a00 : fetch_word Asan.M.loaded_segments (0x81a50 : word) = Some W_81a00.
Proof. vm_refl. Qed.
Lemma D_81a00 : decode_any W_81a00 = Some (Load SZ1 true 10 10 2192, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a04 : bv 32 := 0x0230000f.
Lemma F_81a04 : fetch_word Asan.M.loaded_segments (0x81a54 : word) = Some W_81a04.
Proof. vm_refl. Qed.
Lemma D_81a04 : decode_any W_81a04 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a08 : bv 32 := 0x00a03533.
Lemma F_81a08 : fetch_word Asan.M.loaded_segments (0x81a58 : word) = Some W_81a08.
Proof. vm_refl. Qed.
Lemma D_81a08 : decode_any W_81a08 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a0c : bv 32 := 0x00008067.
Lemma F_81a0c : fetch_word Asan.M.loaded_segments (0x81a5c : word) = Some W_81a0c.
Proof. vm_refl. Qed.
Lemma D_81a0c : decode_any W_81a0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a10 : bv 32 := 0xfc010113.
Lemma F_81a10 : fetch_word Asan.M.loaded_segments (0x81a60 : word) = Some W_81a10.
Proof. vm_refl. Qed.
Lemma D_81a10 : decode_any W_81a10 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a14 : bv 32 := 0x02113c23.
Lemma F_81a14 : fetch_word Asan.M.loaded_segments (0x81a64 : word) = Some W_81a14.
Proof. vm_refl. Qed.
Lemma D_81a14 : decode_any W_81a14 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a18 : bv 32 := 0x02813823.
Lemma F_81a18 : fetch_word Asan.M.loaded_segments (0x81a68 : word) = Some W_81a18.
Proof. vm_refl. Qed.
Lemma D_81a18 : decode_any W_81a18 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a1c : bv 32 := 0x02913423.
Lemma F_81a1c : fetch_word Asan.M.loaded_segments (0x81a6c : word) = Some W_81a1c.
Proof. vm_refl. Qed.
Lemma D_81a1c : decode_any W_81a1c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a20 : bv 32 := 0x03213023.
Lemma F_81a20 : fetch_word Asan.M.loaded_segments (0x81a70 : word) = Some W_81a20.
Proof. vm_refl. Qed.
Lemma D_81a20 : decode_any W_81a20 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a24 : bv 32 := 0x01313c23.
Lemma F_81a24 : fetch_word Asan.M.loaded_segments (0x81a74 : word) = Some W_81a24.
Proof. vm_refl. Qed.
Lemma D_81a24 : decode_any W_81a24 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a28 : bv 32 := 0x01413823.
Lemma F_81a28 : fetch_word Asan.M.loaded_segments (0x81a78 : word) = Some W_81a28.
Proof. vm_refl. Qed.
Lemma D_81a28 : decode_any W_81a28 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a2c : bv 32 := 0x01513423.
Lemma F_81a2c : fetch_word Asan.M.loaded_segments (0x81a7c : word) = Some W_81a2c.
Proof. vm_refl. Qed.
Lemma D_81a2c : decode_any W_81a2c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a30 : bv 32 := 0x00060a63.
Lemma F_81a30 : fetch_word Asan.M.loaded_segments (0x81a80 : word) = Some W_81a30.
Proof. vm_refl. Qed.
Lemma D_81a30 : decode_any W_81a30 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a34 : bv 32 := 0x000de697.
Lemma F_81a34 : fetch_word Asan.M.loaded_segments (0x81a84 : word) = Some W_81a34.
Proof. vm_refl. Qed.
Lemma D_81a34 : decode_any W_81a34 = Some (Auipc 13 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a38 : bv 32 := 0x85868683.
Lemma F_81a38 : fetch_word Asan.M.loaded_segments (0x81a88 : word) = Some W_81a38.
Proof. vm_refl. Qed.
Lemma D_81a38 : decode_any W_81a38 = Some (Load SZ1 true 13 13 2136, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a3c : bv 32 := 0x0230000f.
Lemma F_81a3c : fetch_word Asan.M.loaded_segments (0x81a8c : word) = Some W_81a3c.
Proof. vm_refl. Qed.
Lemma D_81a3c : decode_any W_81a3c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a40 : bv 32 := 0x0a068a63.
Lemma F_81a40 : fetch_word Asan.M.loaded_segments (0x81a90 : word) = Some W_81a40.
Proof. vm_refl. Qed.
Lemma D_81a40 : decode_any W_81a40 = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a44 : bv 32 := 0x00757693.
Lemma F_81a44 : fetch_word Asan.M.loaded_segments (0x81a94 : word) = Some W_81a44.
Proof. vm_refl. Qed.
Lemma D_81a44 : decode_any W_81a44 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a48 : bv 32 := 0x42069863.
Lemma F_81a48 : fetch_word Asan.M.loaded_segments (0x81a98 : word) = Some W_81a48.
Proof. vm_refl. Qed.
Lemma D_81a48 : decode_any W_81a48 = Some (Branch BC_NE 13 0 1072, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a4c : bv 32 := 0x000d5697.
Lemma F_81a4c : fetch_word Asan.M.loaded_segments (0x81a9c : word) = Some W_81a4c.
Proof. vm_refl. Qed.
Lemma D_81a4c : decode_any W_81a4c = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a50 : bv 32 := 0x2fc6b683.
Lemma F_81a50 : fetch_word Asan.M.loaded_segments (0x81aa0 : word) = Some W_81a50.
Proof. vm_refl. Qed.
Lemma D_81a50 : decode_any W_81a50 = Some (Load SZ8 true 13 13 764, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a54 : bv 32 := 0x0006b483.
Lemma F_81a54 : fetch_word Asan.M.loaded_segments (0x81aa4 : word) = Some W_81a54.
Proof. vm_refl. Qed.
Lemma D_81a54 : decode_any W_81a54 = Some (Load SZ8 true 9 13 0, 4%Z).
Proof. vm_refl. Qed.

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

Definition W_81c98 : bv 32 := 0x0d46b983.
Lemma F_81c98 : fetch_word Asan.M.loaded_segments (0x81ce8 : word) = Some W_81c98.
Proof. vm_refl. Qed.
Lemma D_81c98 : decode_any W_81c98 = Some (Load SZ8 true 19 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c9c : bv 32 := 0x0009b303.
Lemma F_81c9c : fetch_word Asan.M.loaded_segments (0x81cec : word) = Some W_81c9c.
Proof. vm_refl. Qed.
Lemma D_81c9c : decode_any W_81c9c = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ca0 : bv 32 := 0x22030c63.
Lemma F_81ca0 : fetch_word Asan.M.loaded_segments (0x81cf0 : word) = Some W_81ca0.
Proof. vm_refl. Qed.
Lemma D_81ca0 : decode_any W_81ca0 = Some (Branch BC_EQ 6 0 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ca4 : bv 32 := 0x00355693.
Lemma F_81ca4 : fetch_word Asan.M.loaded_segments (0x81cf4 : word) = Some W_81ca4.
Proof. vm_refl. Qed.
Lemma D_81ca4 : decode_any W_81ca4 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ca8 : bv 32 := 0x0035d593.
Lemma F_81ca8 : fetch_word Asan.M.loaded_segments (0x81cf8 : word) = Some W_81ca8.
Proof. vm_refl. Qed.
Lemma D_81ca8 : decode_any W_81ca8 = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cac : bv 32 := 0x00d48533.
Lemma F_81cac : fetch_word Asan.M.loaded_segments (0x81cfc : word) = Some W_81cac.
Proof. vm_refl. Qed.
Lemma D_81cac : decode_any W_81cac = Some (Op ALU_ADD 10 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cb0 : bv 32 := 0x00158913.
Lemma F_81cb0 : fetch_word Asan.M.loaded_segments (0x81d00 : word) = Some W_81cb0.
Proof. vm_refl. Qed.
Lemma D_81cb0 : decode_any W_81cb0 = Some (OpImm ALU_ADD 18 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cb4 : bv 32 := 0x40d90433.
Lemma F_81cb4 : fetch_word Asan.M.loaded_segments (0x81d04 : word) = Some W_81cb4.
Proof. vm_refl. Qed.
Lemma D_81cb4 : decode_any W_81cb4 = Some (Op ALU_SUB 8 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cb8 : bv 32 := 0x0c061063.
Lemma F_81cb8 : fetch_word Asan.M.loaded_segments (0x81d08 : word) = Some W_81cb8.
Proof. vm_refl. Qed.
Lemma D_81cb8 : decode_any W_81cb8 = Some (Branch BC_NE 12 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cbc : bv 32 := 0x000d5597.
Lemma F_81cbc : fetch_word Asan.M.loaded_segments (0x81d0c : word) = Some W_81cbc.
Proof. vm_refl. Qed.
Lemma D_81cbc : decode_any W_81cbc = Some (Auipc 11 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cc0 : bv 32 := 0x07c5b583.
Lemma F_81cc0 : fetch_word Asan.M.loaded_segments (0x81d10 : word) = Some W_81cc0.
Proof. vm_refl. Qed.
Lemma D_81cc0 : decode_any W_81cc0 = Some (Load SZ8 true 11 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cc4 : bv 32 := 0x0785b583.
Lemma F_81cc4 : fetch_word Asan.M.loaded_segments (0x81d14 : word) = Some W_81cc4.
Proof. vm_refl. Qed.
Lemma D_81cc4 : decode_any W_81cc4 = Some (Load SZ8 true 11 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cc8 : bv 32 := 0x0ab46863.
Lemma F_81cc8 : fetch_word Asan.M.loaded_segments (0x81d18 : word) = Some W_81cc8.
Proof. vm_refl. Qed.
Lemma D_81cc8 : decode_any W_81cc8 = Some (Branch BC_LTU 8 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cd8 : bv 32 := 0x00059c63.
Lemma F_81cd8 : fetch_word Asan.M.loaded_segments (0x81d28 : word) = Some W_81cd8.
Proof. vm_refl. Qed.
Lemma D_81cd8 : decode_any W_81cd8 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cdc : bv 32 := 0x00050a93.
Lemma F_81cdc : fetch_word Asan.M.loaded_segments (0x81d2c : word) = Some W_81cdc.
Proof. vm_refl. Qed.
Lemma D_81cdc : decode_any W_81cdc = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ce0 : bv 32 := 0x5a1110ef.
Lemma F_81ce0 : fetch_word Asan.M.loaded_segments (0x81d30 : word) = Some W_81ce0.
Proof. vm_refl. Qed.
Lemma D_81ce0 : decode_any W_81ce0 = Some (Jal 1 73120, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ce4 : bv 32 := 0x00050593.
Lemma F_81ce4 : fetch_word Asan.M.loaded_segments (0x81d34 : word) = Some W_81ce4.
Proof. vm_refl. Qed.
Lemma D_81ce4 : decode_any W_81ce4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ce8 : bv 32 := 0x000a8513.
Lemma F_81ce8 : fetch_word Asan.M.loaded_segments (0x81d38 : word) = Some W_81ce8.
Proof. vm_refl. Qed.
Lemma D_81ce8 : decode_any W_81ce8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cec : bv 32 := 0x00ba3023.
Lemma F_81cec : fetch_word Asan.M.loaded_segments (0x81d3c : word) = Some W_81cec.
Proof. vm_refl. Qed.
Lemma D_81cec : decode_any W_81cec = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cf0 : bv 32 := 0xfff58613.
Lemma F_81cf0 : fetch_word Asan.M.loaded_segments (0x81d40 : word) = Some W_81cf0.
Proof. vm_refl. Qed.
Lemma D_81cf0 : decode_any W_81cf0 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cf4 : bv 32 := 0x00c5f633.
Lemma F_81cf4 : fetch_word Asan.M.loaded_segments (0x81d44 : word) = Some W_81cf4.
Proof. vm_refl. Qed.
Lemma D_81cf4 : decode_any W_81cf4 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cf8 : bv 32 := 0x20061063.
Lemma F_81cf8 : fetch_word Asan.M.loaded_segments (0x81d48 : word) = Some W_81cf8.
Proof. vm_refl. Qed.
Lemma D_81cf8 : decode_any W_81cf8 = Some (Branch BC_NE 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_81cfc : bv 32 := 0x00990a33.
Lemma F_81cfc : fetch_word Asan.M.loaded_segments (0x81d4c : word) = Some W_81cfc.
Proof. vm_refl. Qed.
Lemma D_81cfc : decode_any W_81cfc = Some (Op ALU_ADD 20 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d00 : bv 32 := 0x00b50633.
Lemma F_81d00 : fetch_word Asan.M.loaded_segments (0x81d50 : word) = Some W_81d00.
Proof. vm_refl. Qed.
Lemma D_81d00 : decode_any W_81d00 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d04 : bv 32 := 0x40b005b3.
Lemma F_81d04 : fetch_word Asan.M.loaded_segments (0x81d54 : word) = Some W_81d04.
Proof. vm_refl. Qed.
Lemma D_81d04 : decode_any W_81d04 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d08 : bv 32 := 0xfff60613.
Lemma F_81d08 : fetch_word Asan.M.loaded_segments (0x81d58 : word) = Some W_81d08.
Proof. vm_refl. Qed.
Lemma D_81d08 : decode_any W_81d08 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d0c : bv 32 := 0x00b674b3.
Lemma F_81d0c : fetch_word Asan.M.loaded_segments (0x81d5c : word) = Some W_81d0c.
Proof. vm_refl. Qed.
Lemma D_81d0c : decode_any W_81d0c = Some (Op ALU_AND 9 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d10 : bv 32 := 0x00ba7933.
Lemma F_81d10 : fetch_word Asan.M.loaded_segments (0x81d60 : word) = Some W_81d10.
Proof. vm_refl. Qed.
Lemma D_81d10 : decode_any W_81d10 = Some (Op ALU_AND 18 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d14 : bv 32 := 0x0724f663.
Lemma F_81d14 : fetch_word Asan.M.loaded_segments (0x81d64 : word) = Some W_81d14.
Proof. vm_refl. Qed.
Lemma D_81d14 : decode_any W_81d14 = Some (Branch BC_GEU 9 18 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d18 : bv 32 := 0x00a48a63.
Lemma F_81d18 : fetch_word Asan.M.loaded_segments (0x81d68 : word) = Some W_81d18.
Proof. vm_refl. Qed.
Lemma D_81d18 : decode_any W_81d18 = Some (Branch BC_EQ 9 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d1c : bv 32 := 0x0009b683.
Lemma F_81d1c : fetch_word Asan.M.loaded_segments (0x81d6c : word) = Some W_81d1c.
Proof. vm_refl. Qed.
Lemma D_81d1c : decode_any W_81d1c = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d20 : bv 32 := 0x40a48633.
Lemma F_81d20 : fetch_word Asan.M.loaded_segments (0x81d70 : word) = Some W_81d20.
Proof. vm_refl. Qed.
Lemma D_81d20 : decode_any W_81d20 = Some (Op ALU_SUB 12 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d24 : bv 32 := 0x00000593.
Lemma F_81d24 : fetch_word Asan.M.loaded_segments (0x81d74 : word) = Some W_81d24.
Proof. vm_refl. Qed.
Lemma D_81d24 : decode_any W_81d24 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d28 : bv 32 := 0x000680e7.
Lemma F_81d28 : fetch_word Asan.M.loaded_segments (0x81d78 : word) = Some W_81d28.
Proof. vm_refl. Qed.
Lemma D_81d28 : decode_any W_81d28 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d2c : bv 32 := 0x012a0c63.
Lemma F_81d2c : fetch_word Asan.M.loaded_segments (0x81d7c : word) = Some W_81d2c.
Proof. vm_refl. Qed.
Lemma D_81d2c : decode_any W_81d2c = Some (Branch BC_EQ 20 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d30 : bv 32 := 0x0009b683.
Lemma F_81d30 : fetch_word Asan.M.loaded_segments (0x81d80 : word) = Some W_81d30.
Proof. vm_refl. Qed.
Lemma D_81d30 : decode_any W_81d30 = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d34 : bv 32 := 0x412a0633.
Lemma F_81d34 : fetch_word Asan.M.loaded_segments (0x81d84 : word) = Some W_81d34.
Proof. vm_refl. Qed.
Lemma D_81d34 : decode_any W_81d34 = Some (Op ALU_SUB 12 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d38 : bv 32 := 0x00090513.
Lemma F_81d38 : fetch_word Asan.M.loaded_segments (0x81d88 : word) = Some W_81d38.
Proof. vm_refl. Qed.
Lemma D_81d38 : decode_any W_81d38 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d3c : bv 32 := 0x00000593.
Lemma F_81d3c : fetch_word Asan.M.loaded_segments (0x81d8c : word) = Some W_81d3c.
Proof. vm_refl. Qed.
Lemma D_81d3c : decode_any W_81d3c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d40 : bv 32 := 0x000680e7.
Lemma F_81d40 : fetch_word Asan.M.loaded_segments (0x81d90 : word) = Some W_81d40.
Proof. vm_refl. Qed.
Lemma D_81d40 : decode_any W_81d40 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d44 : bv 32 := 0xfff90593.
Lemma F_81d44 : fetch_word Asan.M.loaded_segments (0x81d94 : word) = Some W_81d44.
Proof. vm_refl. Qed.
Lemma D_81d44 : decode_any W_81d44 = Some (OpImm ALU_ADD 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d48 : bv 32 := 0x00100693.
Lemma F_81d48 : fetch_word Asan.M.loaded_segments (0x81d98 : word) = Some W_81d48.
Proof. vm_refl. Qed.
Lemma D_81d48 : decode_any W_81d48 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d4c : bv 32 := 0x00048513.
Lemma F_81d4c : fetch_word Asan.M.loaded_segments (0x81d9c : word) = Some W_81d4c.
Proof. vm_refl. Qed.
Lemma D_81d4c : decode_any W_81d4c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d50 : bv 32 := 0x00000613.
Lemma F_81d50 : fetch_word Asan.M.loaded_segments (0x81da0 : word) = Some W_81d50.
Proof. vm_refl. Qed.
Lemma D_81d50 : decode_any W_81d50 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d54 : bv 32 := 0x03813083.
Lemma F_81d54 : fetch_word Asan.M.loaded_segments (0x81da4 : word) = Some W_81d54.
Proof. vm_refl. Qed.
Lemma D_81d54 : decode_any W_81d54 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d58 : bv 32 := 0x03013403.
Lemma F_81d58 : fetch_word Asan.M.loaded_segments (0x81da8 : word) = Some W_81d58.
Proof. vm_refl. Qed.
Lemma D_81d58 : decode_any W_81d58 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d5c : bv 32 := 0x02813483.
Lemma F_81d5c : fetch_word Asan.M.loaded_segments (0x81dac : word) = Some W_81d5c.
Proof. vm_refl. Qed.
Lemma D_81d5c : decode_any W_81d5c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d60 : bv 32 := 0x02013903.
Lemma F_81d60 : fetch_word Asan.M.loaded_segments (0x81db0 : word) = Some W_81d60.
Proof. vm_refl. Qed.
Lemma D_81d60 : decode_any W_81d60 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d64 : bv 32 := 0x01813983.
Lemma F_81d64 : fetch_word Asan.M.loaded_segments (0x81db4 : word) = Some W_81d64.
Proof. vm_refl. Qed.
Lemma D_81d64 : decode_any W_81d64 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d68 : bv 32 := 0x01013a03.
Lemma F_81d68 : fetch_word Asan.M.loaded_segments (0x81db8 : word) = Some W_81d68.
Proof. vm_refl. Qed.
Lemma D_81d68 : decode_any W_81d68 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d6c : bv 32 := 0x00813a83.
Lemma F_81d6c : fetch_word Asan.M.loaded_segments (0x81dbc : word) = Some W_81d6c.
Proof. vm_refl. Qed.
Lemma D_81d6c : decode_any W_81d6c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d70 : bv 32 := 0x04010113.
Lemma F_81d70 : fetch_word Asan.M.loaded_segments (0x81dc0 : word) = Some W_81d70.
Proof. vm_refl. Qed.
Lemma D_81d70 : decode_any W_81d70 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d74 : bv 32 := 0x2f11806f.
Lemma F_81d74 : fetch_word Asan.M.loaded_segments (0x81dc4 : word) = Some W_81d74.
Proof. vm_refl. Qed.
Lemma D_81d74 : decode_any W_81d74 = Some (Jal 0 101104, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d78 : bv 32 := 0x00060593.
Lemma F_81d78 : fetch_word Asan.M.loaded_segments (0x81dc8 : word) = Some W_81d78.
Proof. vm_refl. Qed.
Lemma D_81d78 : decode_any W_81d78 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d7c : bv 32 := 0x00c0006f.
Lemma F_81d7c : fetch_word Asan.M.loaded_segments (0x81dcc : word) = Some W_81d7c.
Proof. vm_refl. Qed.
Lemma D_81d7c : decode_any W_81d7c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d80 : bv 32 := 0x0009b303.
Lemma F_81d80 : fetch_word Asan.M.loaded_segments (0x81dd0 : word) = Some W_81d80.
Proof. vm_refl. Qed.
Lemma D_81d80 : decode_any W_81d80 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d84 : bv 32 := 0x00000593.
Lemma F_81d84 : fetch_word Asan.M.loaded_segments (0x81dd4 : word) = Some W_81d84.
Proof. vm_refl. Qed.
Lemma D_81d84 : decode_any W_81d84 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d88 : bv 32 := 0x00040613.
Lemma F_81d88 : fetch_word Asan.M.loaded_segments (0x81dd8 : word) = Some W_81d88.
Proof. vm_refl. Qed.
Lemma D_81d88 : decode_any W_81d88 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d8c : bv 32 := 0x03813083.
Lemma F_81d8c : fetch_word Asan.M.loaded_segments (0x81ddc : word) = Some W_81d8c.
Proof. vm_refl. Qed.
Lemma D_81d8c : decode_any W_81d8c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d90 : bv 32 := 0x03013403.
Lemma F_81d90 : fetch_word Asan.M.loaded_segments (0x81de0 : word) = Some W_81d90.
Proof. vm_refl. Qed.
Lemma D_81d90 : decode_any W_81d90 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d94 : bv 32 := 0x02813483.
Lemma F_81d94 : fetch_word Asan.M.loaded_segments (0x81de4 : word) = Some W_81d94.
Proof. vm_refl. Qed.
Lemma D_81d94 : decode_any W_81d94 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d98 : bv 32 := 0x02013903.
Lemma F_81d98 : fetch_word Asan.M.loaded_segments (0x81de8 : word) = Some W_81d98.
Proof. vm_refl. Qed.
Lemma D_81d98 : decode_any W_81d98 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81d9c : bv 32 := 0x01813983.
Lemma F_81d9c : fetch_word Asan.M.loaded_segments (0x81dec : word) = Some W_81d9c.
Proof. vm_refl. Qed.
Lemma D_81d9c : decode_any W_81d9c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81da0 : bv 32 := 0x01013a03.
Lemma F_81da0 : fetch_word Asan.M.loaded_segments (0x81df0 : word) = Some W_81da0.
Proof. vm_refl. Qed.
Lemma D_81da0 : decode_any W_81da0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81da4 : bv 32 := 0x00813a83.
Lemma F_81da4 : fetch_word Asan.M.loaded_segments (0x81df4 : word) = Some W_81da4.
Proof. vm_refl. Qed.
Lemma D_81da4 : decode_any W_81da4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81da8 : bv 32 := 0x04010113.
Lemma F_81da8 : fetch_word Asan.M.loaded_segments (0x81df8 : word) = Some W_81da8.
Proof. vm_refl. Qed.
Lemma D_81da8 : decode_any W_81da8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_81dac : bv 32 := 0x00030067.
Lemma F_81dac : fetch_word Asan.M.loaded_segments (0x81dfc : word) = Some W_81dac.
Proof. vm_refl. Qed.
Lemma D_81dac : decode_any W_81dac = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81db0 : bv 32 := 0x000d5317.
Lemma F_81db0 : fetch_word Asan.M.loaded_segments (0x81e00 : word) = Some W_81db0.
Proof. vm_refl. Qed.
Lemma D_81db0 : decode_any W_81db0 = Some (Auipc 6 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81db4 : bv 32 := 0xf9033303.
Lemma F_81db4 : fetch_word Asan.M.loaded_segments (0x81e04 : word) = Some W_81db4.
Proof. vm_refl. Qed.
Lemma D_81db4 : decode_any W_81db4 = Some (Load SZ8 true 6 6 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_81db8 : bv 32 := 0x04e34303.
Lemma F_81db8 : fetch_word Asan.M.loaded_segments (0x81e08 : word) = Some W_81db8.
Proof. vm_refl. Qed.
Lemma D_81db8 : decode_any W_81db8 = Some (Load SZ1 false 6 6 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_81dbc : bv 32 := 0x08031e63.
Lemma F_81dbc : fetch_word Asan.M.loaded_segments (0x81e0c : word) = Some W_81dbc.
Proof. vm_refl. Qed.
Lemma D_81dbc : decode_any W_81dbc = Some (Branch BC_NE 6 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_81dc0 : bv 32 := 0x04088063.
Lemma F_81dc0 : fetch_word Asan.M.loaded_segments (0x81e10 : word) = Some W_81dc0.
Proof. vm_refl. Qed.
Lemma D_81dc0 : decode_any W_81dc0 = Some (Branch BC_EQ 17 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_81dc4 : bv 32 := 0x0038d893.
Lemma F_81dc4 : fetch_word Asan.M.loaded_segments (0x81e14 : word) = Some W_81dc4.
Proof. vm_refl. Qed.
Lemma D_81dc4 : decode_any W_81dc4 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81dc8 : bv 32 := 0x00d888b3.
Lemma F_81dc8 : fetch_word Asan.M.loaded_segments (0x81e18 : word) = Some W_81dc8.
Proof. vm_refl. Qed.
Lemma D_81dc8 : decode_any W_81dc8 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81dcc : bv 32 := 0x06b8f063.
Lemma F_81dcc : fetch_word Asan.M.loaded_segments (0x81e1c : word) = Some W_81dcc.
Proof. vm_refl. Qed.
Lemma D_81dcc : decode_any W_81dcc = Some (Branch BC_GEU 17 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_81dd0 : bv 32 := 0x00148893.
Lemma F_81dd0 : fetch_word Asan.M.loaded_segments (0x81e20 : word) = Some W_81dd0.
Proof. vm_refl. Qed.
Lemma D_81dd0 : decode_any W_81dd0 = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81dd4 : bv 32 := 0x00b86863.
Lemma F_81dd4 : fetch_word Asan.M.loaded_segments (0x81e24 : word) = Some W_81dd4.
Proof. vm_refl. Qed.
Lemma D_81dd4 : decode_any W_81dd4 = Some (Branch BC_LTU 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81dd8 : bv 32 := 0x00375813.
Lemma F_81dd8 : fetch_word Asan.M.loaded_segments (0x81e28 : word) = Some W_81dd8.
Proof. vm_refl. Qed.
Lemma D_81dd8 : decode_any W_81dd8 = Some (ShiftImm ALU_SRL 16 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ddc : bv 32 := 0x01180833.
Lemma F_81ddc : fetch_word Asan.M.loaded_segments (0x81e2c : word) = Some W_81ddc.
Proof. vm_refl. Qed.
Lemma D_81ddc : decode_any W_81ddc = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_81de0 : bv 32 := 0xeb05fae3.
Lemma F_81de0 : fetch_word Asan.M.loaded_segments (0x81e30 : word) = Some W_81de0.
Proof. vm_refl. Qed.
Lemma D_81de0 : decode_any W_81de0 = Some (Branch BC_GEU 11 16 7860, 4%Z).
Proof. vm_refl. Qed.

Definition W_81de4 : bv 32 := 0x00170713.
Lemma F_81de4 : fetch_word Asan.M.loaded_segments (0x81e34 : word) = Some W_81de4.
Proof. vm_refl. Qed.
Lemma D_81de4 : decode_any W_81de4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81de8 : bv 32 := 0x06e5e863.
Lemma F_81de8 : fetch_word Asan.M.loaded_segments (0x81e38 : word) = Some W_81de8.
Proof. vm_refl. Qed.
Lemma D_81de8 : decode_any W_81de8 = Some (Branch BC_LTU 11 14 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_81dec : bv 32 := 0x011787b3.
Lemma F_81dec : fetch_word Asan.M.loaded_segments (0x81e3c : word) = Some W_81dec.
Proof. vm_refl. Qed.
Lemma D_81dec : decode_any W_81dec = Some (Op ALU_ADD 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_81df0 : bv 32 := 0x0037d793.
Lemma F_81df0 : fetch_word Asan.M.loaded_segments (0x81e40 : word) = Some W_81df0.
Proof. vm_refl. Qed.
Lemma D_81df0 : decode_any W_81df0 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81df4 : bv 32 := 0x00d786b3.
Lemma F_81df4 : fetch_word Asan.M.loaded_segments (0x81e44 : word) = Some W_81df4.
Proof. vm_refl. Qed.
Lemma D_81df4 : decode_any W_81df4 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81df8 : bv 32 := 0xe8b6fee3.
Lemma F_81df8 : fetch_word Asan.M.loaded_segments (0x81e48 : word) = Some W_81df8.
Proof. vm_refl. Qed.
Lemma D_81df8 : decode_any W_81df8 = Some (Branch BC_GEU 13 11 7836, 4%Z).
Proof. vm_refl. Qed.

Definition W_81dfc : bv 32 := 0x05c0006f.
Lemma F_81dfc : fetch_word Asan.M.loaded_segments (0x81e4c : word) = Some W_81dfc.
Proof. vm_refl. Qed.
Lemma D_81dfc : decode_any W_81dfc = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e00 : bv 32 := 0x04048463.
Lemma F_81e00 : fetch_word Asan.M.loaded_segments (0x81e50 : word) = Some W_81e00.
Proof. vm_refl. Qed.
Lemma D_81e00 : decode_any W_81e00 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e04 : bv 32 := 0x0036d713.
Lemma F_81e04 : fetch_word Asan.M.loaded_segments (0x81e54 : word) = Some W_81e04.
Proof. vm_refl. Qed.
Lemma D_81e04 : decode_any W_81e04 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e08 : bv 32 := 0x00970733.
Lemma F_81e08 : fetch_word Asan.M.loaded_segments (0x81e58 : word) = Some W_81e08.
Proof. vm_refl. Qed.
Lemma D_81e08 : decode_any W_81e08 = Some (Op ALU_ADD 14 14 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e0c : bv 32 := 0x00070663.
Lemma F_81e0c : fetch_word Asan.M.loaded_segments (0x81e5c : word) = Some W_81e0c.
Proof. vm_refl. Qed.
Lemma D_81e0c : decode_any W_81e0c = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e10 : bv 32 := 0x00170713.
Lemma F_81e10 : fetch_word Asan.M.loaded_segments (0x81e60 : word) = Some W_81e10.
Proof. vm_refl. Qed.
Lemma D_81e10 : decode_any W_81e10 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e14 : bv 32 := 0x04e5e263.
Lemma F_81e14 : fetch_word Asan.M.loaded_segments (0x81e64 : word) = Some W_81e14.
Proof. vm_refl. Qed.
Lemma D_81e14 : decode_any W_81e14 = Some (Branch BC_LTU 11 14 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e18 : bv 32 := 0x00128293.
Lemma F_81e18 : fetch_word Asan.M.loaded_segments (0x81e68 : word) = Some W_81e18.
Proof. vm_refl. Qed.
Lemma D_81e18 : decode_any W_81e18 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e1c : bv 32 := 0x0032d713.
Lemma F_81e1c : fetch_word Asan.M.loaded_segments (0x81e6c : word) = Some W_81e1c.
Proof. vm_refl. Qed.
Lemma D_81e1c : decode_any W_81e1c = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e20 : bv 32 := 0x00d706b3.
Lemma F_81e20 : fetch_word Asan.M.loaded_segments (0x81e70 : word) = Some W_81e20.
Proof. vm_refl. Qed.
Lemma D_81e20 : decode_any W_81e20 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e24 : bv 32 := 0xe6b6f8e3.
Lemma F_81e24 : fetch_word Asan.M.loaded_segments (0x81e74 : word) = Some W_81e24.
Proof. vm_refl. Qed.
Lemma D_81e24 : decode_any W_81e24 = Some (Branch BC_GEU 13 11 7792, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e28 : bv 32 := 0x0300006f.
Lemma F_81e28 : fetch_word Asan.M.loaded_segments (0x81e78 : word) = Some W_81e28.
Proof. vm_refl. Qed.
Lemma D_81e28 : decode_any W_81e28 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e2c : bv 32 := 0xe60484e3.
Lemma F_81e2c : fetch_word Asan.M.loaded_segments (0x81e7c : word) = Some W_81e2c.
Proof. vm_refl. Qed.
Lemma D_81e2c : decode_any W_81e2c = Some (Branch BC_EQ 9 0 7784, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e30 : bv 32 := 0x0036d693.
Lemma F_81e30 : fetch_word Asan.M.loaded_segments (0x81e80 : word) = Some W_81e30.
Proof. vm_refl. Qed.
Lemma D_81e30 : decode_any W_81e30 = Some (ShiftImm ALU_SRL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e34 : bv 32 := 0x009686b3.
Lemma F_81e34 : fetch_word Asan.M.loaded_segments (0x81e84 : word) = Some W_81e34.
Proof. vm_refl. Qed.
Lemma D_81e34 : decode_any W_81e34 = Some (Op ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e38 : bv 32 := 0xe4068ee3.
Lemma F_81e38 : fetch_word Asan.M.loaded_segments (0x81e88 : word) = Some W_81e38.
Proof. vm_refl. Qed.
Lemma D_81e38 : decode_any W_81e38 = Some (Branch BC_EQ 13 0 7772, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e3c : bv 32 := 0x00168693.
Lemma F_81e3c : fetch_word Asan.M.loaded_segments (0x81e8c : word) = Some W_81e3c.
Proof. vm_refl. Qed.
Lemma D_81e3c : decode_any W_81e3c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e40 : bv 32 := 0xe4d5fae3.
Lemma F_81e40 : fetch_word Asan.M.loaded_segments (0x81e90 : word) = Some W_81e40.
Proof. vm_refl. Qed.
Lemma D_81e40 : decode_any W_81e40 = Some (Branch BC_GEU 11 13 7764, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e44 : bv 32 := 0x0140006f.
Lemma F_81e44 : fetch_word Asan.M.loaded_segments (0x81e94 : word) = Some W_81e44.
Proof. vm_refl. Qed.
Lemma D_81e44 : decode_any W_81e44 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e48 : bv 32 := 0x00178793.
Lemma F_81e48 : fetch_word Asan.M.loaded_segments (0x81e98 : word) = Some W_81e48.
Proof. vm_refl. Qed.
Lemma D_81e48 : decode_any W_81e48 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e4c : bv 32 := 0x0037d793.
Lemma F_81e4c : fetch_word Asan.M.loaded_segments (0x81e9c : word) = Some W_81e4c.
Proof. vm_refl. Qed.
Lemma D_81e4c : decode_any W_81e4c = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e50 : bv 32 := 0xfff78793.
Lemma F_81e50 : fetch_word Asan.M.loaded_segments (0x81ea0 : word) = Some W_81e50.
Proof. vm_refl. Qed.
Lemma D_81e50 : decode_any W_81e50 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e54 : bv 32 := 0xe4b7f0e3.
Lemma F_81e54 : fetch_word Asan.M.loaded_segments (0x81ea4 : word) = Some W_81e54.
Proof. vm_refl. Qed.
Lemma D_81e54 : decode_any W_81e54 = Some (Branch BC_GEU 15 11 7744, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e58 : bv 32 := 0xfffa0517.
Lemma F_81e58 : fetch_word Asan.M.loaded_segments (0x81ea8 : word) = Some W_81e58.
Proof. vm_refl. Qed.
Lemma D_81e58 : decode_any W_81e58 = Some (Auipc 10 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e5c : bv 32 := 0xfff92597.
Lemma F_81e5c : fetch_word Asan.M.loaded_segments (0x81eac : word) = Some W_81e5c.
Proof. vm_refl. Qed.
Lemma D_81e5c : decode_any W_81e5c = Some (Auipc 11 1048466, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e60 : bv 32 := 0xba950513.
Lemma F_81e60 : fetch_word Asan.M.loaded_segments (0x81eb0 : word) = Some W_81e60.
Proof. vm_refl. Qed.
Lemma D_81e60 : decode_any W_81e60 = Some (OpImm ALU_ADD 10 10 2985, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e64 : bv 32 := 0x40a58613.
Lemma F_81e64 : fetch_word Asan.M.loaded_segments (0x81eb4 : word) = Some W_81e64.
Proof. vm_refl. Qed.
Lemma D_81e64 : decode_any W_81e64 = Some (OpImm ALU_ADD 12 11 1034, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e68 : bv 32 := 0x03100593.
Lemma F_81e68 : fetch_word Asan.M.loaded_segments (0x81eb8 : word) = Some W_81e68.
Proof. vm_refl. Qed.
Lemma D_81e68 : decode_any W_81e68 = Some (OpImm ALU_ADD 11 0 49, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e6c : bv 32 := 0x00000693.
Lemma F_81e6c : fetch_word Asan.M.loaded_segments (0x81ebc : word) = Some W_81e6c.
Proof. vm_refl. Qed.
Lemma D_81e6c : decode_any W_81e6c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e70 : bv 32 := 0x00000713.
Lemma F_81e70 : fetch_word Asan.M.loaded_segments (0x81ec0 : word) = Some W_81e70.
Proof. vm_refl. Qed.
Lemma D_81e70 : decode_any W_81e70 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e74 : bv 32 := 0x1e8180ef.
Lemma F_81e74 : fetch_word Asan.M.loaded_segments (0x81ec4 : word) = Some W_81e74.
Proof. vm_refl. Qed.
Lemma D_81e74 : decode_any W_81e74 = Some (Jal 1 98792, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e78 : bv 32 := 0xfffa0517.
Lemma F_81e78 : fetch_word Asan.M.loaded_segments (0x81ec8 : word) = Some W_81e78.
Proof. vm_refl. Qed.
Lemma D_81e78 : decode_any W_81e78 = Some (Auipc 10 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e7c : bv 32 := 0xfff9d597.
Lemma F_81e7c : fetch_word Asan.M.loaded_segments (0x81ecc : word) = Some W_81e7c.
Proof. vm_refl. Qed.
Lemma D_81e7c : decode_any W_81e7c = Some (Auipc 11 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e80 : bv 32 := 0xb8950513.
Lemma F_81e80 : fetch_word Asan.M.loaded_segments (0x81ed0 : word) = Some W_81e80.
Proof. vm_refl. Qed.
Lemma D_81e80 : decode_any W_81e80 = Some (OpImm ALU_ADD 10 10 2953, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e84 : bv 32 := 0x67e58613.
Lemma F_81e84 : fetch_word Asan.M.loaded_segments (0x81ed4 : word) = Some W_81e84.
Proof. vm_refl. Qed.
Lemma D_81e84 : decode_any W_81e84 = Some (OpImm ALU_ADD 12 11 1662, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e88 : bv 32 := 0x02700593.
Lemma F_81e88 : fetch_word Asan.M.loaded_segments (0x81ed8 : word) = Some W_81e88.
Proof. vm_refl. Qed.
Lemma D_81e88 : decode_any W_81e88 = Some (OpImm ALU_ADD 11 0 39, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e8c : bv 32 := 0x00000693.
Lemma F_81e8c : fetch_word Asan.M.loaded_segments (0x81edc : word) = Some W_81e8c.
Proof. vm_refl. Qed.
Lemma D_81e8c : decode_any W_81e8c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e90 : bv 32 := 0x00000713.
Lemma F_81e90 : fetch_word Asan.M.loaded_segments (0x81ee0 : word) = Some W_81e90.
Proof. vm_refl. Qed.
Lemma D_81e90 : decode_any W_81e90 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e94 : bv 32 := 0x1c8180ef.
Lemma F_81e94 : fetch_word Asan.M.loaded_segments (0x81ee4 : word) = Some W_81e94.
Proof. vm_refl. Qed.
Lemma D_81e94 : decode_any W_81e94 = Some (Jal 1 98760, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e98 : bv 32 := 0x000d5317.
Lemma F_81e98 : fetch_word Asan.M.loaded_segments (0x81ee8 : word) = Some W_81e98.
Proof. vm_refl. Qed.
Lemma D_81e98 : decode_any W_81e98 = Some (Auipc 6 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81e9c : bv 32 := 0xef033303.
Lemma F_81e9c : fetch_word Asan.M.loaded_segments (0x81eec : word) = Some W_81e9c.
Proof. vm_refl. Qed.
Lemma D_81e9c : decode_any W_81e9c = Some (Load SZ8 true 6 6 3824, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ea0 : bv 32 := 0xcc0308e3.
Lemma F_81ea0 : fetch_word Asan.M.loaded_segments (0x81ef0 : word) = Some W_81ea0.
Proof. vm_refl. Qed.
Lemma D_81ea0 : decode_any W_81ea0 = Some (Branch BC_EQ 6 0 7376, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ea4 : bv 32 := 0x000d5517.
Lemma F_81ea4 : fetch_word Asan.M.loaded_segments (0x81ef4 : word) = Some W_81ea4.
Proof. vm_refl. Qed.
Lemma D_81ea4 : decode_any W_81ea4 = Some (Auipc 10 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ea8 : bv 32 := 0xeec53503.
Lemma F_81ea8 : fetch_word Asan.M.loaded_segments (0x81ef8 : word) = Some W_81ea8.
Proof. vm_refl. Qed.
Lemma D_81ea8 : decode_any W_81ea8 = Some (Load SZ8 true 10 10 3820, 4%Z).
Proof. vm_refl. Qed.

Definition W_81eac : bv 32 := 0x00052503.
Lemma F_81eac : fetch_word Asan.M.loaded_segments (0x81efc : word) = Some W_81eac.
Proof. vm_refl. Qed.
Lemma D_81eac : decode_any W_81eac = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81eb0 : bv 32 := 0x04051c63.
Lemma F_81eb0 : fetch_word Asan.M.loaded_segments (0x81f00 : word) = Some W_81eb0.
Proof. vm_refl. Qed.
Lemma D_81eb0 : decode_any W_81eb0 = Some (Branch BC_NE 10 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_81eb4 : bv 32 := 0x0000006f.
Lemma F_81eb4 : fetch_word Asan.M.loaded_segments (0x81f04 : word) = Some W_81eb4.
Proof. vm_refl. Qed.
Lemma D_81eb4 : decode_any W_81eb4 = Some (Jal 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81eb8 : bv 32 := 0xfffa0517.
Lemma F_81eb8 : fetch_word Asan.M.loaded_segments (0x81f08 : word) = Some W_81eb8.
Proof. vm_refl. Qed.
Lemma D_81eb8 : decode_any W_81eb8 = Some (Auipc 10 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ebc : bv 32 := 0xfff92597.
Lemma F_81ebc : fetch_word Asan.M.loaded_segments (0x81f0c : word) = Some W_81ebc.
Proof. vm_refl. Qed.
Lemma D_81ebc : decode_any W_81ebc = Some (Auipc 11 1048466, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ec0 : bv 32 := 0xb4950513.
Lemma F_81ec0 : fetch_word Asan.M.loaded_segments (0x81f10 : word) = Some W_81ec0.
Proof. vm_refl. Qed.
Lemma D_81ec0 : decode_any W_81ec0 = Some (OpImm ALU_ADD 10 10 2889, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ec4 : bv 32 := 0x91658613.
Lemma F_81ec4 : fetch_word Asan.M.loaded_segments (0x81f14 : word) = Some W_81ec4.
Proof. vm_refl. Qed.
Lemma D_81ec4 : decode_any W_81ec4 = Some (OpImm ALU_ADD 12 11 2326, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ec8 : bv 32 := 0x03000593.
Lemma F_81ec8 : fetch_word Asan.M.loaded_segments (0x81f18 : word) = Some W_81ec8.
Proof. vm_refl. Qed.
Lemma D_81ec8 : decode_any W_81ec8 = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ecc : bv 32 := 0x00000693.
Lemma F_81ecc : fetch_word Asan.M.loaded_segments (0x81f1c : word) = Some W_81ecc.
Proof. vm_refl. Qed.
Lemma D_81ecc : decode_any W_81ecc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ed0 : bv 32 := 0x00000713.
Lemma F_81ed0 : fetch_word Asan.M.loaded_segments (0x81f20 : word) = Some W_81ed0.
Proof. vm_refl. Qed.
Lemma D_81ed0 : decode_any W_81ed0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ed4 : bv 32 := 0x188180ef.
Lemma F_81ed4 : fetch_word Asan.M.loaded_segments (0x81f24 : word) = Some W_81ed4.
Proof. vm_refl. Qed.
Lemma D_81ed4 : decode_any W_81ed4 = Some (Jal 1 98696, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ed8 : bv 32 := 0xfffa0517.
Lemma F_81ed8 : fetch_word Asan.M.loaded_segments (0x81f28 : word) = Some W_81ed8.
Proof. vm_refl. Qed.
Lemma D_81ed8 : decode_any W_81ed8 = Some (Auipc 10 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition W_81edc : bv 32 := 0xfff97597.
Lemma F_81edc : fetch_word Asan.M.loaded_segments (0x81f2c : word) = Some W_81edc.
Proof. vm_refl. Qed.
Lemma D_81edc : decode_any W_81edc = Some (Auipc 11 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ee0 : bv 32 := 0xb2950513.
Lemma F_81ee0 : fetch_word Asan.M.loaded_segments (0x81f30 : word) = Some W_81ee0.
Proof. vm_refl. Qed.
Lemma D_81ee0 : decode_any W_81ee0 = Some (OpImm ALU_ADD 10 10 2857, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ee4 : bv 32 := 0x70f58613.
Lemma F_81ee4 : fetch_word Asan.M.loaded_segments (0x81f34 : word) = Some W_81ee4.
Proof. vm_refl. Qed.
Lemma D_81ee4 : decode_any W_81ee4 = Some (OpImm ALU_ADD 12 11 1807, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ee8 : bv 32 := 0x03200593.
Lemma F_81ee8 : fetch_word Asan.M.loaded_segments (0x81f38 : word) = Some W_81ee8.
Proof. vm_refl. Qed.
Lemma D_81ee8 : decode_any W_81ee8 = Some (OpImm ALU_ADD 11 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_81eec : bv 32 := 0x00000693.
Lemma F_81eec : fetch_word Asan.M.loaded_segments (0x81f3c : word) = Some W_81eec.
Proof. vm_refl. Qed.
Lemma D_81eec : decode_any W_81eec = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ef0 : bv 32 := 0x00000713.
Lemma F_81ef0 : fetch_word Asan.M.loaded_segments (0x81f40 : word) = Some W_81ef0.
Proof. vm_refl. Qed.
Lemma D_81ef0 : decode_any W_81ef0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ef4 : bv 32 := 0x168180ef.
Lemma F_81ef4 : fetch_word Asan.M.loaded_segments (0x81f44 : word) = Some W_81ef4.
Proof. vm_refl. Qed.
Lemma D_81ef4 : decode_any W_81ef4 = Some (Jal 1 98664, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ef8 : bv 32 := 0xfff91517.
Lemma F_81ef8 : fetch_word Asan.M.loaded_segments (0x81f48 : word) = Some W_81ef8.
Proof. vm_refl. Qed.
Lemma D_81ef8 : decode_any W_81ef8 = Some (Auipc 10 1048465, 4%Z).
Proof. vm_refl. Qed.

Definition W_81efc : bv 32 := 0xaec50513.
Lemma F_81efc : fetch_word Asan.M.loaded_segments (0x81f4c : word) = Some W_81efc.
Proof. vm_refl. Qed.
Lemma D_81efc : decode_any W_81efc = Some (OpImm ALU_ADD 10 10 2796, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f00 : bv 32 := 0x2ec0d0ef.
Lemma F_81f00 : fetch_word Asan.M.loaded_segments (0x81f50 : word) = Some W_81f00.
Proof. vm_refl. Qed.
Lemma D_81f00 : decode_any W_81f00 = Some (Jal 1 53996, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f04 : bv 32 := 0x08c180ef.
Lemma F_81f04 : fetch_word Asan.M.loaded_segments (0x81f54 : word) = Some W_81f04.
Proof. vm_refl. Qed.
Lemma D_81f04 : decode_any W_81f04 = Some (Jal 1 98444, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f08 : bv 32 := 0x1b01a0ef.
Lemma F_81f08 : fetch_word Asan.M.loaded_segments (0x81f58 : word) = Some W_81f08.
Proof. vm_refl. Qed.
Lemma D_81f08 : decode_any W_81f08 = Some (Jal 1 106928, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f0c : bv 32 := 0x000d5597.
Lemma F_81f0c : fetch_word Asan.M.loaded_segments (0x81f5c : word) = Some W_81f0c.
Proof. vm_refl. Qed.
Lemma D_81f0c : decode_any W_81f0c = Some (Auipc 11 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f10 : bv 32 := 0xe3c5b583.
Lemma F_81f10 : fetch_word Asan.M.loaded_segments (0x81f60 : word) = Some W_81f10.
Proof. vm_refl. Qed.
Lemma D_81f10 : decode_any W_81f10 = Some (Load SZ8 true 11 11 3644, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f14 : bv 32 := 0x0005b583.
Lemma F_81f14 : fetch_word Asan.M.loaded_segments (0x81f64 : word) = Some W_81f14.
Proof. vm_refl. Qed.
Lemma D_81f14 : decode_any W_81f14 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f18 : bv 32 := 0xfff58613.
Lemma F_81f18 : fetch_word Asan.M.loaded_segments (0x81f68 : word) = Some W_81f18.
Proof. vm_refl. Qed.
Lemma D_81f18 : decode_any W_81f18 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f1c : bv 32 := 0x00c5b6b3.
Lemma F_81f1c : fetch_word Asan.M.loaded_segments (0x81f6c : word) = Some W_81f1c.
Proof. vm_refl. Qed.
Lemma D_81f1c : decode_any W_81f1c = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f20 : bv 32 := 0xfff68693.
Lemma F_81f20 : fetch_word Asan.M.loaded_segments (0x81f70 : word) = Some W_81f20.
Proof. vm_refl. Qed.
Lemma D_81f20 : decode_any W_81f20 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f24 : bv 32 := 0x00c6f6b3.
Lemma F_81f24 : fetch_word Asan.M.loaded_segments (0x81f74 : word) = Some W_81f24.
Proof. vm_refl. Qed.
Lemma D_81f24 : decode_any W_81f24 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f28 : bv 32 := 0x04a6f263.
Lemma F_81f28 : fetch_word Asan.M.loaded_segments (0x81f78 : word) = Some W_81f28.
Proof. vm_refl. Qed.
Lemma D_81f28 : decode_any W_81f28 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f2c : bv 32 := 0x000d5697.
Lemma F_81f2c : fetch_word Asan.M.loaded_segments (0x81f7c : word) = Some W_81f2c.
Proof. vm_refl. Qed.
Lemma D_81f2c : decode_any W_81f2c = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f30 : bv 32 := 0xe246b683.
Lemma F_81f30 : fetch_word Asan.M.loaded_segments (0x81f80 : word) = Some W_81f30.
Proof. vm_refl. Qed.
Lemma D_81f30 : decode_any W_81f30 = Some (Load SZ8 true 13 13 3620, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f34 : bv 32 := 0x000d5717.
Lemma F_81f34 : fetch_word Asan.M.loaded_segments (0x81f84 : word) = Some W_81f34.
Proof. vm_refl. Qed.
Lemma D_81f34 : decode_any W_81f34 = Some (Auipc 14 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f38 : bv 32 := 0xe2473703.
Lemma F_81f38 : fetch_word Asan.M.loaded_segments (0x81f88 : word) = Some W_81f38.
Proof. vm_refl. Qed.
Lemma D_81f38 : decode_any W_81f38 = Some (Load SZ8 true 14 14 3620, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f3c : bv 32 := 0x0006b803.
Lemma F_81f3c : fetch_word Asan.M.loaded_segments (0x81f8c : word) = Some W_81f3c.
Proof. vm_refl. Qed.
Lemma D_81f3c : decode_any W_81f3c = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f40 : bv 32 := 0x00073683.
Lemma F_81f40 : fetch_word Asan.M.loaded_segments (0x81f90 : word) = Some W_81f40.
Proof. vm_refl. Qed.
Lemma D_81f40 : decode_any W_81f40 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f44 : bv 32 := 0xfff80793.
Lemma F_81f44 : fetch_word Asan.M.loaded_segments (0x81f94 : word) = Some W_81f44.
Proof. vm_refl. Qed.
Lemma D_81f44 : decode_any W_81f44 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f48 : bv 32 := 0x00a7f463.
Lemma F_81f48 : fetch_word Asan.M.loaded_segments (0x81f98 : word) = Some W_81f48.
Proof. vm_refl. Qed.
Lemma D_81f48 : decode_any W_81f48 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f50 : bv 32 := 0x000d5717.
Lemma F_81f50 : fetch_word Asan.M.loaded_segments (0x81fa0 : word) = Some W_81f50.
Proof. vm_refl. Qed.
Lemma D_81f50 : decode_any W_81f50 = Some (Auipc 14 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f54 : bv 32 := 0xe1073703.
Lemma F_81f54 : fetch_word Asan.M.loaded_segments (0x81fa4 : word) = Some W_81f54.
Proof. vm_refl. Qed.
Lemma D_81f54 : decode_any W_81f54 = Some (Load SZ8 true 14 14 3600, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f58 : bv 32 := 0x00073283.
Lemma F_81f58 : fetch_word Asan.M.loaded_segments (0x81fa8 : word) = Some W_81f58.
Proof. vm_refl. Qed.
Lemma D_81f58 : decode_any W_81f58 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f5c : bv 32 := 0x0032d713.
Lemma F_81f5c : fetch_word Asan.M.loaded_segments (0x81fac : word) = Some W_81f5c.
Proof. vm_refl. Qed.
Lemma D_81f5c : decode_any W_81f5c = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f60 : bv 32 := 0x00b708b3.
Lemma F_81f60 : fetch_word Asan.M.loaded_segments (0x81fb0 : word) = Some W_81f60.
Proof. vm_refl. Qed.
Lemma D_81f60 : decode_any W_81f60 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f64 : bv 32 := 0x00a2ea63.
Lemma F_81f64 : fetch_word Asan.M.loaded_segments (0x81fb4 : word) = Some W_81f64.
Proof. vm_refl. Qed.
Lemma D_81f64 : decode_any W_81f64 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f68 : bv 32 := 0x00a8f863.
Lemma F_81f68 : fetch_word Asan.M.loaded_segments (0x81fb8 : word) = Some W_81f68.
Proof. vm_refl. Qed.
Lemma D_81f68 : decode_any W_81f68 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f6c : bv 32 := 0x00355513.
Lemma F_81f6c : fetch_word Asan.M.loaded_segments (0x81fbc : word) = Some W_81f6c.
Proof. vm_refl. Qed.
Lemma D_81f6c : decode_any W_81f6c = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f70 : bv 32 := 0x00a58533.
Lemma F_81f70 : fetch_word Asan.M.loaded_segments (0x81fc0 : word) = Some W_81f70.
Proof. vm_refl. Qed.
Lemma D_81f70 : decode_any W_81f70 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_81f74 : bv 32 := 0x00008067.
Lemma F_81f74 : fetch_word Asan.M.loaded_segments (0x81fc4 : word) = Some W_81f74.
Proof. vm_refl. Qed.
Lemma D_81f74 : decode_any W_81f74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r60dd4_61420.
Module Na0_code_r65f44_65f5c.
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

Definition W_870ac : bv 32 := 0x000d9517.
Lemma F_870ac : fetch_word Asan.M.loaded_segments (0x870fc : word) = Some W_870ac.
Proof. vm_refl. Qed.
Lemma D_870ac : decode_any W_870ac = Some (Auipc 10 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_870b0 : bv 32 := 0x65c50503.
Lemma F_870b0 : fetch_word Asan.M.loaded_segments (0x87100 : word) = Some W_870b0.
Proof. vm_refl. Qed.
Lemma D_870b0 : decode_any W_870b0 = Some (Load SZ1 true 10 10 1628, 4%Z).
Proof. vm_refl. Qed.

Definition W_870b4 : bv 32 := 0x0230000f.
Lemma F_870b4 : fetch_word Asan.M.loaded_segments (0x87104 : word) = Some W_870b4.
Proof. vm_refl. Qed.
Lemma D_870b4 : decode_any W_870b4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_870b8 : bv 32 := 0xfff50513.
Lemma F_870b8 : fetch_word Asan.M.loaded_segments (0x87108 : word) = Some W_870b8.
Proof. vm_refl. Qed.
Lemma D_870b8 : decode_any W_870b8 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_870bc : bv 32 := 0x00153513.
Lemma F_870bc : fetch_word Asan.M.loaded_segments (0x8710c : word) = Some W_870bc.
Proof. vm_refl. Qed.
Lemma D_870bc : decode_any W_870bc = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_870c0 : bv 32 := 0x00008067.
Lemma F_870c0 : fetch_word Asan.M.loaded_segments (0x87110 : word) = Some W_870c0.
Proof. vm_refl. Qed.
Lemma D_870c0 : decode_any W_870c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r65f44_65f5c.
Module Na0_code_r67bcc_67d3c.
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

Definition W_88d44 : bv 32 := 0x000d8517.
Lemma F_88d44 : fetch_word Asan.M.loaded_segments (0x88d94 : word) = Some W_88d44.
Proof. vm_refl. Qed.
Lemma D_88d44 : decode_any W_88d44 = Some (Auipc 10 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d48 : bv 32 := 0x9e852503.
Lemma F_88d48 : fetch_word Asan.M.loaded_segments (0x88d98 : word) = Some W_88d48.
Proof. vm_refl. Qed.
Lemma D_88d48 : decode_any W_88d48 = Some (Load SZ4 true 10 10 2536, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d4c : bv 32 := 0x0230000f.
Lemma F_88d4c : fetch_word Asan.M.loaded_segments (0x88d9c : word) = Some W_88d4c.
Proof. vm_refl. Qed.
Lemma D_88d4c : decode_any W_88d4c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d50 : bv 32 := 0x00008067.
Lemma F_88d50 : fetch_word Asan.M.loaded_segments (0x88da0 : word) = Some W_88d50.
Proof. vm_refl. Qed.
Lemma D_88d50 : decode_any W_88d50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d54 : bv 32 := 0xfb010113.
Lemma F_88d54 : fetch_word Asan.M.loaded_segments (0x88da4 : word) = Some W_88d54.
Proof. vm_refl. Qed.
Lemma D_88d54 : decode_any W_88d54 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d58 : bv 32 := 0x04113423.
Lemma F_88d58 : fetch_word Asan.M.loaded_segments (0x88da8 : word) = Some W_88d58.
Proof. vm_refl. Qed.
Lemma D_88d58 : decode_any W_88d58 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d5c : bv 32 := 0x04813023.
Lemma F_88d5c : fetch_word Asan.M.loaded_segments (0x88dac : word) = Some W_88d5c.
Proof. vm_refl. Qed.
Lemma D_88d5c : decode_any W_88d5c = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d60 : bv 32 := 0x02913c23.
Lemma F_88d60 : fetch_word Asan.M.loaded_segments (0x88db0 : word) = Some W_88d60.
Proof. vm_refl. Qed.
Lemma D_88d60 : decode_any W_88d60 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d64 : bv 32 := 0x03213823.
Lemma F_88d64 : fetch_word Asan.M.loaded_segments (0x88db4 : word) = Some W_88d64.
Proof. vm_refl. Qed.
Lemma D_88d64 : decode_any W_88d64 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d68 : bv 32 := 0x03313423.
Lemma F_88d68 : fetch_word Asan.M.loaded_segments (0x88db8 : word) = Some W_88d68.
Proof. vm_refl. Qed.
Lemma D_88d68 : decode_any W_88d68 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d6c : bv 32 := 0x03413023.
Lemma F_88d6c : fetch_word Asan.M.loaded_segments (0x88dbc : word) = Some W_88d6c.
Proof. vm_refl. Qed.
Lemma D_88d6c : decode_any W_88d6c = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d70 : bv 32 := 0x01513c23.
Lemma F_88d70 : fetch_word Asan.M.loaded_segments (0x88dc0 : word) = Some W_88d70.
Proof. vm_refl. Qed.
Lemma D_88d70 : decode_any W_88d70 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d74 : bv 32 := 0x01613823.
Lemma F_88d74 : fetch_word Asan.M.loaded_segments (0x88dc4 : word) = Some W_88d74.
Proof. vm_refl. Qed.
Lemma D_88d74 : decode_any W_88d74 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d78 : bv 32 := 0x01713423.
Lemma F_88d78 : fetch_word Asan.M.loaded_segments (0x88dc8 : word) = Some W_88d78.
Proof. vm_refl. Qed.
Lemma D_88d78 : decode_any W_88d78 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d7c : bv 32 := 0x01813023.
Lemma F_88d7c : fetch_word Asan.M.loaded_segments (0x88dcc : word) = Some W_88d7c.
Proof. vm_refl. Qed.
Lemma D_88d7c : decode_any W_88d7c = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d80 : bv 32 := 0x00078493.
Lemma F_88d80 : fetch_word Asan.M.loaded_segments (0x88dd0 : word) = Some W_88d80.
Proof. vm_refl. Qed.
Lemma D_88d80 : decode_any W_88d80 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d84 : bv 32 := 0x00070a93.
Lemma F_88d84 : fetch_word Asan.M.loaded_segments (0x88dd4 : word) = Some W_88d84.
Proof. vm_refl. Qed.
Lemma D_88d84 : decode_any W_88d84 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d88 : bv 32 := 0x00068a13.
Lemma F_88d88 : fetch_word Asan.M.loaded_segments (0x88dd8 : word) = Some W_88d88.
Proof. vm_refl. Qed.
Lemma D_88d88 : decode_any W_88d88 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d8c : bv 32 := 0x00060413.
Lemma F_88d8c : fetch_word Asan.M.loaded_segments (0x88ddc : word) = Some W_88d8c.
Proof. vm_refl. Qed.
Lemma D_88d8c : decode_any W_88d8c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d90 : bv 32 := 0x00058913.
Lemma F_88d90 : fetch_word Asan.M.loaded_segments (0x88de0 : word) = Some W_88d90.
Proof. vm_refl. Qed.
Lemma D_88d90 : decode_any W_88d90 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d94 : bv 32 := 0x00050993.
Lemma F_88d94 : fetch_word Asan.M.loaded_segments (0x88de4 : word) = Some W_88d94.
Proof. vm_refl. Qed.
Lemma D_88d94 : decode_any W_88d94 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d98 : bv 32 := 0x00052423.
Lemma F_88d98 : fetch_word Asan.M.loaded_segments (0x88de8 : word) = Some W_88d98.
Proof. vm_refl. Qed.
Lemma D_88d98 : decode_any W_88d98 = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88d9c : bv 32 := 0xb10fe0ef.
Lemma F_88d9c : fetch_word Asan.M.loaded_segments (0x88dec : word) = Some W_88d9c.
Proof. vm_refl. Qed.
Lemma D_88d9c : decode_any W_88d9c = Some (Jal 1 2089744, 4%Z).
Proof. vm_refl. Qed.

Definition W_88da0 : bv 32 := 0x0c050a63.
Lemma F_88da0 : fetch_word Asan.M.loaded_segments (0x88df0 : word) = Some W_88da0.
Proof. vm_refl. Qed.
Lemma D_88da0 : decode_any W_88da0 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_88da4 : bv 32 := 0x219010ef.
Lemma F_88da4 : fetch_word Asan.M.loaded_segments (0x88df4 : word) = Some W_88da4.
Proof. vm_refl. Qed.
Lemma D_88da4 : decode_any W_88da4 = Some (Jal 1 6680, 4%Z).
Proof. vm_refl. Qed.

Definition W_88da8 : bv 32 := 0x04050a63.
Lemma F_88da8 : fetch_word Asan.M.loaded_segments (0x88df8 : word) = Some W_88da8.
Proof. vm_refl. Qed.
Lemma D_88da8 : decode_any W_88da8 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_88dac : bv 32 := 0x7ff50c13.
Lemma F_88dac : fetch_word Asan.M.loaded_segments (0x88dfc : word) = Some W_88dac.
Proof. vm_refl. Qed.
Lemma D_88dac : decode_any W_88dac = Some (OpImm ALU_ADD 24 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_88db0 : bv 32 := 0x461c4583.
Lemma F_88db0 : fetch_word Asan.M.loaded_segments (0x88e00 : word) = Some W_88db0.
Proof. vm_refl. Qed.
Lemma D_88db0 : decode_any W_88db0 = Some (Load SZ1 false 11 24 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_88db4 : bv 32 := 0x00100613.
Lemma F_88db4 : fetch_word Asan.M.loaded_segments (0x88e04 : word) = Some W_88db4.
Proof. vm_refl. Qed.
Lemma D_88db4 : decode_any W_88db4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_88db8 : bv 32 := 0x46cc00a3.
Lemma F_88db8 : fetch_word Asan.M.loaded_segments (0x88e08 : word) = Some W_88db8.
Proof. vm_refl. Qed.
Lemma D_88db8 : decode_any W_88db8 = Some (Store SZ1 24 12 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_88dbc : bv 32 := 0x0a059a63.
Lemma F_88dbc : fetch_word Asan.M.loaded_segments (0x88e0c : word) = Some W_88dbc.
Proof. vm_refl. Qed.
Lemma D_88dbc : decode_any W_88dbc = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_88dc0 : bv 32 := 0x00050b93.
Lemma F_88dc0 : fetch_word Asan.M.loaded_segments (0x88e10 : word) = Some W_88dc0.
Proof. vm_refl. Qed.
Lemma D_88dc0 : decode_any W_88dc0 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88dc4 : bv 32 := 0x3bd010ef.
Lemma F_88dc4 : fetch_word Asan.M.loaded_segments (0x88e14 : word) = Some W_88dc4.
Proof. vm_refl. Qed.
Lemma D_88dc4 : decode_any W_88dc4 = Some (Jal 1 7100, 4%Z).
Proof. vm_refl. Qed.

Definition W_88dc8 : bv 32 := 0x00050b13.
Lemma F_88dc8 : fetch_word Asan.M.loaded_segments (0x88e18 : word) = Some W_88dc8.
Proof. vm_refl. Qed.
Lemma D_88dc8 : decode_any W_88dc8 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88dcc : bv 32 := 0x000b8513.
Lemma F_88dcc : fetch_word Asan.M.loaded_segments (0x88e1c : word) = Some W_88dcc.
Proof. vm_refl. Qed.
Lemma D_88dcc : decode_any W_88dcc = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88dd0 : bv 32 := 0x409010ef.
Lemma F_88dd0 : fetch_word Asan.M.loaded_segments (0x88e20 : word) = Some W_88dd0.
Proof. vm_refl. Qed.
Lemma D_88dd0 : decode_any W_88dd0 = Some (Jal 1 7176, 4%Z).
Proof. vm_refl. Qed.

Definition W_88dd4 : bv 32 := 0x00050813.
Lemma F_88dd4 : fetch_word Asan.M.loaded_segments (0x88e24 : word) = Some W_88dd4.
Proof. vm_refl. Qed.
Lemma D_88dd4 : decode_any W_88dd4 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88dd8 : bv 32 := 0x060a8c63.
Lemma F_88dd8 : fetch_word Asan.M.loaded_segments (0x88e28 : word) = Some W_88dd8.
Proof. vm_refl. Qed.
Lemma D_88dd8 : decode_any W_88dd8 = Some (Branch BC_EQ 21 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ddc : bv 32 := 0x00100893.
Lemma F_88ddc : fetch_word Asan.M.loaded_segments (0x88e2c : word) = Some W_88ddc.
Proof. vm_refl. Qed.
Lemma D_88ddc : decode_any W_88ddc = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_88de0 : bv 32 := 0x00098513.
Lemma F_88de0 : fetch_word Asan.M.loaded_segments (0x88e30 : word) = Some W_88de0.
Proof. vm_refl. Qed.
Lemma D_88de0 : decode_any W_88de0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88de4 : bv 32 := 0x00048593.
Lemma F_88de4 : fetch_word Asan.M.loaded_segments (0x88e34 : word) = Some W_88de4.
Proof. vm_refl. Qed.
Lemma D_88de4 : decode_any W_88de4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88de8 : bv 32 := 0x00090613.
Lemma F_88de8 : fetch_word Asan.M.loaded_segments (0x88e38 : word) = Some W_88de8.
Proof. vm_refl. Qed.
Lemma D_88de8 : decode_any W_88de8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88dec : bv 32 := 0x00040693.
Lemma F_88dec : fetch_word Asan.M.loaded_segments (0x88e3c : word) = Some W_88dec.
Proof. vm_refl. Qed.
Lemma D_88dec : decode_any W_88dec = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88df0 : bv 32 := 0x00000713.
Lemma F_88df0 : fetch_word Asan.M.loaded_segments (0x88e40 : word) = Some W_88df0.
Proof. vm_refl. Qed.
Lemma D_88df0 : decode_any W_88df0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88df4 : bv 32 := 0x000b0793.
Lemma F_88df4 : fetch_word Asan.M.loaded_segments (0x88e44 : word) = Some W_88df4.
Proof. vm_refl. Qed.
Lemma D_88df4 : decode_any W_88df4 = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88df8 : bv 32 := 0x0740006f.
Lemma F_88df8 : fetch_word Asan.M.loaded_segments (0x88e48 : word) = Some W_88df8.
Proof. vm_refl. Qed.
Lemma D_88df8 : decode_any W_88df8 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e6c : bv 32 := 0x018190ef.
Lemma F_88e6c : fetch_word Asan.M.loaded_segments (0x88ebc : word) = Some W_88e6c.
Proof. vm_refl. Qed.
Lemma D_88e6c : decode_any W_88e6c = Some (Jal 1 102424, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e70 : bv 32 := 0x460c00a3.
Lemma F_88e70 : fetch_word Asan.M.loaded_segments (0x88ec0 : word) = Some W_88e70.
Proof. vm_refl. Qed.
Lemma D_88e70 : decode_any W_88e70 = Some (Store SZ1 24 0 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e74 : bv 32 := 0x04813083.
Lemma F_88e74 : fetch_word Asan.M.loaded_segments (0x88ec4 : word) = Some W_88e74.
Proof. vm_refl. Qed.
Lemma D_88e74 : decode_any W_88e74 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e78 : bv 32 := 0x04013403.
Lemma F_88e78 : fetch_word Asan.M.loaded_segments (0x88ec8 : word) = Some W_88e78.
Proof. vm_refl. Qed.
Lemma D_88e78 : decode_any W_88e78 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e7c : bv 32 := 0x03813483.
Lemma F_88e7c : fetch_word Asan.M.loaded_segments (0x88ecc : word) = Some W_88e7c.
Proof. vm_refl. Qed.
Lemma D_88e7c : decode_any W_88e7c = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e80 : bv 32 := 0x03013903.
Lemma F_88e80 : fetch_word Asan.M.loaded_segments (0x88ed0 : word) = Some W_88e80.
Proof. vm_refl. Qed.
Lemma D_88e80 : decode_any W_88e80 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e84 : bv 32 := 0x02813983.
Lemma F_88e84 : fetch_word Asan.M.loaded_segments (0x88ed4 : word) = Some W_88e84.
Proof. vm_refl. Qed.
Lemma D_88e84 : decode_any W_88e84 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e88 : bv 32 := 0x02013a03.
Lemma F_88e88 : fetch_word Asan.M.loaded_segments (0x88ed8 : word) = Some W_88e88.
Proof. vm_refl. Qed.
Lemma D_88e88 : decode_any W_88e88 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e8c : bv 32 := 0x01813a83.
Lemma F_88e8c : fetch_word Asan.M.loaded_segments (0x88edc : word) = Some W_88e8c.
Proof. vm_refl. Qed.
Lemma D_88e8c : decode_any W_88e8c = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e90 : bv 32 := 0x01013b03.
Lemma F_88e90 : fetch_word Asan.M.loaded_segments (0x88ee0 : word) = Some W_88e90.
Proof. vm_refl. Qed.
Lemma D_88e90 : decode_any W_88e90 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e94 : bv 32 := 0x00813b83.
Lemma F_88e94 : fetch_word Asan.M.loaded_segments (0x88ee4 : word) = Some W_88e94.
Proof. vm_refl. Qed.
Lemma D_88e94 : decode_any W_88e94 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e98 : bv 32 := 0x00013c03.
Lemma F_88e98 : fetch_word Asan.M.loaded_segments (0x88ee8 : word) = Some W_88e98.
Proof. vm_refl. Qed.
Lemma D_88e98 : decode_any W_88e98 = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88e9c : bv 32 := 0x05010113.
Lemma F_88e9c : fetch_word Asan.M.loaded_segments (0x88eec : word) = Some W_88e9c.
Proof. vm_refl. Qed.
Lemma D_88e9c : decode_any W_88e9c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_88ea0 : bv 32 := 0x00008067.
Lemma F_88ea0 : fetch_word Asan.M.loaded_segments (0x88ef0 : word) = Some W_88ea0.
Proof. vm_refl. Qed.
Lemma D_88ea0 : decode_any W_88ea0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r67bcc_67d3c.
Module Na0_code_r6bbd4_6bc28.
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

Definition W_8cd4c : bv 32 := 0x00155517.
Lemma F_8cd4c : fetch_word Asan.M.loaded_segments (0x8cd9c : word) = Some W_8cd4c.
Proof. vm_refl. Qed.
Lemma D_8cd4c : decode_any W_8cd4c = Some (Auipc 10 341, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cd50 : bv 32 := 0xf4550503.
Lemma F_8cd50 : fetch_word Asan.M.loaded_segments (0x8cda0 : word) = Some W_8cd50.
Proof. vm_refl. Qed.
Lemma D_8cd50 : decode_any W_8cd50 = Some (Load SZ1 true 10 10 3909, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cd54 : bv 32 := 0x00a03533.
Lemma F_8cd54 : fetch_word Asan.M.loaded_segments (0x8cda4 : word) = Some W_8cd54.
Proof. vm_refl. Qed.
Lemma D_8cd54 : decode_any W_8cd54 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cd58 : bv 32 := 0x00008067.
Lemma F_8cd58 : fetch_word Asan.M.loaded_segments (0x8cda8 : word) = Some W_8cd58.
Proof. vm_refl. Qed.
Lemma D_8cd58 : decode_any W_8cd58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cd74 : bv 32 := 0x00155517.
Lemma F_8cd74 : fetch_word Asan.M.loaded_segments (0x8cdc4 : word) = Some W_8cd74.
Proof. vm_refl. Qed.
Lemma D_8cd74 : decode_any W_8cd74 = Some (Auipc 10 341, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cd78 : bv 32 := 0xf1e50503.
Lemma F_8cd78 : fetch_word Asan.M.loaded_segments (0x8cdc8 : word) = Some W_8cd78.
Proof. vm_refl. Qed.
Lemma D_8cd78 : decode_any W_8cd78 = Some (Load SZ1 true 10 10 3870, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cd7c : bv 32 := 0x00a03533.
Lemma F_8cd7c : fetch_word Asan.M.loaded_segments (0x8cdcc : word) = Some W_8cd7c.
Proof. vm_refl. Qed.
Lemma D_8cd7c : decode_any W_8cd7c = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8cd80 : bv 32 := 0x00008067.
Lemma F_8cd80 : fetch_word Asan.M.loaded_segments (0x8cdd0 : word) = Some W_8cd80.
Proof. vm_refl. Qed.
Lemma D_8cd80 : decode_any W_8cd80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r6bbd4_6bc28.
Module Na0_code_r66e54_66ef4.
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

Definition W_87fbc : bv 32 := 0xff010113.
Lemma F_87fbc : fetch_word Asan.M.loaded_segments (0x8800c : word) = Some W_87fbc.
Proof. vm_refl. Qed.
Lemma D_87fbc : decode_any W_87fbc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fc0 : bv 32 := 0x00113423.
Lemma F_87fc0 : fetch_word Asan.M.loaded_segments (0x88010 : word) = Some W_87fc0.
Proof. vm_refl. Qed.
Lemma D_87fc0 : decode_any W_87fc0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fc4 : bv 32 := 0x00813023.
Lemma F_87fc4 : fetch_word Asan.M.loaded_segments (0x88014 : word) = Some W_87fc4.
Proof. vm_refl. Qed.
Lemma D_87fc4 : decode_any W_87fc4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fc8 : bv 32 := 0x000d8517.
Lemma F_87fc8 : fetch_word Asan.M.loaded_segments (0x88018 : word) = Some W_87fc8.
Proof. vm_refl. Qed.
Lemma D_87fc8 : decode_any W_87fc8 = Some (Auipc 10 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fcc : bv 32 := 0x74050413.
Lemma F_87fcc : fetch_word Asan.M.loaded_segments (0x8801c : word) = Some W_87fcc.
Proof. vm_refl. Qed.
Lemma D_87fcc : decode_any W_87fcc = Some (OpImm ALU_ADD 8 10 1856, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fd0 : bv 32 := 0x00040583.
Lemma F_87fd0 : fetch_word Asan.M.loaded_segments (0x88020 : word) = Some W_87fd0.
Proof. vm_refl. Qed.
Lemma D_87fd0 : decode_any W_87fd0 = Some (Load SZ1 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fd4 : bv 32 := 0x00100513.
Lemma F_87fd4 : fetch_word Asan.M.loaded_segments (0x88024 : word) = Some W_87fd4.
Proof. vm_refl. Qed.
Lemma D_87fd4 : decode_any W_87fd4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fd8 : bv 32 := 0x0230000f.
Lemma F_87fd8 : fetch_word Asan.M.loaded_segments (0x88028 : word) = Some W_87fd8.
Proof. vm_refl. Qed.
Lemma D_87fd8 : decode_any W_87fd8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fdc : bv 32 := 0x00a59a63.
Lemma F_87fdc : fetch_word Asan.M.loaded_segments (0x8802c : word) = Some W_87fdc.
Proof. vm_refl. Qed.
Lemma D_87fdc : decode_any W_87fdc = Some (Branch BC_NE 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fe0 : bv 32 := 0x00813083.
Lemma F_87fe0 : fetch_word Asan.M.loaded_segments (0x88030 : word) = Some W_87fe0.
Proof. vm_refl. Qed.
Lemma D_87fe0 : decode_any W_87fe0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fe4 : bv 32 := 0x00013403.
Lemma F_87fe4 : fetch_word Asan.M.loaded_segments (0x88034 : word) = Some W_87fe4.
Proof. vm_refl. Qed.
Lemma D_87fe4 : decode_any W_87fe4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fe8 : bv 32 := 0x01010113.
Lemma F_87fe8 : fetch_word Asan.M.loaded_segments (0x88038 : word) = Some W_87fe8.
Proof. vm_refl. Qed.
Lemma D_87fe8 : decode_any W_87fe8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_87fec : bv 32 := 0x00008067.
Lemma F_87fec : fetch_word Asan.M.loaded_segments (0x8803c : word) = Some W_87fec.
Proof. vm_refl. Qed.
Lemma D_87fec : decode_any W_87fec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r66e54_66ef4.
Module Na0_code_r61f50_61f68.
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

Definition W_82e3c : bv 32 := 0x000dc517.
Lemma F_82e3c : fetch_word Asan.M.loaded_segments (0x82e8c : word) = Some W_82e3c.
Proof. vm_refl. Qed.
Lemma D_82e3c : decode_any W_82e3c = Some (Auipc 10 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e40 : bv 32 := 0x45450513.
Lemma F_82e40 : fetch_word Asan.M.loaded_segments (0x82e90 : word) = Some W_82e40.
Proof. vm_refl. Qed.
Lemma D_82e40 : decode_any W_82e40 = Some (OpImm ALU_ADD 10 10 1108, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e44 : bv 32 := 0x00054583.
Lemma F_82e44 : fetch_word Asan.M.loaded_segments (0x82e94 : word) = Some W_82e44.
Proof. vm_refl. Qed.
Lemma D_82e44 : decode_any W_82e44 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e48 : bv 32 := 0x00058663.
Lemma F_82e48 : fetch_word Asan.M.loaded_segments (0x82e98 : word) = Some W_82e48.
Proof. vm_refl. Qed.
Lemma D_82e48 : decode_any W_82e48 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e4c : bv 32 := 0x00452503.
Lemma F_82e4c : fetch_word Asan.M.loaded_segments (0x82e9c : word) = Some W_82e4c.
Proof. vm_refl. Qed.
Lemma D_82e4c : decode_any W_82e4c = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_82e50 : bv 32 := 0x2f5c806f.
Lemma F_82e50 : fetch_word Asan.M.loaded_segments (0x82ea0 : word) = Some W_82e50.
Proof. vm_refl. Qed.
Lemma D_82e50 : decode_any W_82e50 = Some (Jal 0 822004, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r61f50_61f68.
Module Na0_code_r69654_69674.
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

Definition W_8a7bc : bv 32 := 0xff010113.
Lemma F_8a7bc : fetch_word Asan.M.loaded_segments (0x8a80c : word) = Some W_8a7bc.
Proof. vm_refl. Qed.
Lemma D_8a7bc : decode_any W_8a7bc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a7c0 : bv 32 := 0x00113423.
Lemma F_8a7c0 : fetch_word Asan.M.loaded_segments (0x8a810 : word) = Some W_8a7c0.
Proof. vm_refl. Qed.
Lemma D_8a7c0 : decode_any W_8a7c0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a7c4 : bv 32 := 0xe78f80ef.
Lemma F_8a7c4 : fetch_word Asan.M.loaded_segments (0x8a814 : word) = Some W_8a7c4.
Proof. vm_refl. Qed.
Lemma D_8a7c4 : decode_any W_8a7c4 = Some (Jal 1 2066040, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a7c8 : bv 32 := 0x00050463.
Lemma F_8a7c8 : fetch_word Asan.M.loaded_segments (0x8a818 : word) = Some W_8a7c8.
Proof. vm_refl. Qed.
Lemma D_8a7c8 : decode_any W_8a7c8 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a7cc : bv 32 := 0x09853503.
Lemma F_8a7cc : fetch_word Asan.M.loaded_segments (0x8a81c : word) = Some W_8a7cc.
Proof. vm_refl. Qed.
Lemma D_8a7cc : decode_any W_8a7cc = Some (Load SZ8 true 10 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a7d0 : bv 32 := 0x00813083.
Lemma F_8a7d0 : fetch_word Asan.M.loaded_segments (0x8a820 : word) = Some W_8a7d0.
Proof. vm_refl. Qed.
Lemma D_8a7d0 : decode_any W_8a7d0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a7d4 : bv 32 := 0x01010113.
Lemma F_8a7d4 : fetch_word Asan.M.loaded_segments (0x8a824 : word) = Some W_8a7d4.
Proof. vm_refl. Qed.
Lemma D_8a7d4 : decode_any W_8a7d4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a7d8 : bv 32 := 0x00008067.
Lemma F_8a7d8 : fetch_word Asan.M.loaded_segments (0x8a828 : word) = Some W_8a7d8.
Proof. vm_refl. Qed.
Lemma D_8a7d8 : decode_any W_8a7d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r69654_69674.
Module Na0_code_rcd208_cd224.
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

Definition W_14b950 : bv 32 := 0x00020593.
Lemma F_14b950 : fetch_word Asan.M.loaded_segments (0x14b994 : word) = Some W_14b950.
Proof. vm_refl. Qed.
Lemma D_14b950 : decode_any W_14b950 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b954 : bv 32 := 0xfa85b583.
Lemma F_14b954 : fetch_word Asan.M.loaded_segments (0x14b998 : word) = Some W_14b954.
Proof. vm_refl. Qed.
Lemma D_14b954 : decode_any W_14b954 = Some (Load SZ8 true 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b958 : bv 32 := 0x02051513.
Lemma F_14b958 : fetch_word Asan.M.loaded_segments (0x14b99c : word) = Some W_14b958.
Proof. vm_refl. Qed.
Lemma D_14b958 : decode_any W_14b958 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b95c : bv 32 := 0x01d55513.
Lemma F_14b95c : fetch_word Asan.M.loaded_segments (0x14b9a0 : word) = Some W_14b95c.
Proof. vm_refl. Qed.
Lemma D_14b95c : decode_any W_14b95c = Some (ShiftImm ALU_SRL 10 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b960 : bv 32 := 0x00a58533.
Lemma F_14b960 : fetch_word Asan.M.loaded_segments (0x14b9a4 : word) = Some W_14b960.
Proof. vm_refl. Qed.
Lemma D_14b960 : decode_any W_14b960 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b964 : bv 32 := 0x00053503.
Lemma F_14b964 : fetch_word Asan.M.loaded_segments (0x14b9a8 : word) = Some W_14b964.
Proof. vm_refl. Qed.
Lemma D_14b964 : decode_any W_14b964 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b968 : bv 32 := 0x00008067.
Lemma F_14b968 : fetch_word Asan.M.loaded_segments (0x14b9ac : word) = Some W_14b968.
Proof. vm_refl. Qed.
Lemma D_14b968 : decode_any W_14b968 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_rcd208_cd224.
Module Na0_code_r68820_68858.
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

Definition W_89988 : bv 32 := 0xff010113.
Lemma F_89988 : fetch_word Asan.M.loaded_segments (0x899d8 : word) = Some W_89988.
Proof. vm_refl. Qed.
Lemma D_89988 : decode_any W_89988 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_8998c : bv 32 := 0x00113423.
Lemma F_8998c : fetch_word Asan.M.loaded_segments (0x899dc : word) = Some W_8998c.
Proof. vm_refl. Qed.
Lemma D_8998c : decode_any W_8998c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_89990 : bv 32 := 0x62d000ef.
Lemma F_89990 : fetch_word Asan.M.loaded_segments (0x899e0 : word) = Some W_89990.
Proof. vm_refl. Qed.
Lemma D_89990 : decode_any W_89990 = Some (Jal 1 3628, 4%Z).
Proof. vm_refl. Qed.

Definition W_89994 : bv 32 := 0x00050c63.
Lemma F_89994 : fetch_word Asan.M.loaded_segments (0x899e4 : word) = Some W_89994.
Proof. vm_refl. Qed.
Lemma D_89994 : decode_any W_89994 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_89998 : bv 32 := 0x7ff50513.
Lemma F_89998 : fetch_word Asan.M.loaded_segments (0x899e8 : word) = Some W_89998.
Proof. vm_refl. Qed.
Lemma D_89998 : decode_any W_89998 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_8999c : bv 32 := 0x2f150513.
Lemma F_8999c : fetch_word Asan.M.loaded_segments (0x899ec : word) = Some W_8999c.
Proof. vm_refl. Qed.
Lemma D_8999c : decode_any W_8999c = Some (OpImm ALU_ADD 10 10 753, 4%Z).
Proof. vm_refl. Qed.

Definition W_899a0 : bv 32 := 0x00813083.
Lemma F_899a0 : fetch_word Asan.M.loaded_segments (0x899f0 : word) = Some W_899a0.
Proof. vm_refl. Qed.
Lemma D_899a0 : decode_any W_899a0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_899a4 : bv 32 := 0x01010113.
Lemma F_899a4 : fetch_word Asan.M.loaded_segments (0x899f4 : word) = Some W_899a4.
Proof. vm_refl. Qed.
Lemma D_899a4 : decode_any W_899a4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_899a8 : bv 32 := 0x00008067.
Lemma F_899a8 : fetch_word Asan.M.loaded_segments (0x899f8 : word) = Some W_899a8.
Proof. vm_refl. Qed.
Lemma D_899a8 : decode_any W_899a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r68820_68858.
Module Na0_code_r69818_698c8.
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

Definition W_8a980 : bv 32 := 0x02850583.
Lemma F_8a980 : fetch_word Asan.M.loaded_segments (0x8a9d0 : word) = Some W_8a980.
Proof. vm_refl. Qed.
Lemma D_8a980 : decode_any W_8a980 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a984 : bv 32 := 0x0230000f.
Lemma F_8a984 : fetch_word Asan.M.loaded_segments (0x8a9d4 : word) = Some W_8a984.
Proof. vm_refl. Qed.
Lemma D_8a984 : decode_any W_8a984 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a988 : bv 32 := 0x02058c63.
Lemma F_8a988 : fetch_word Asan.M.loaded_segments (0x8a9d8 : word) = Some W_8a988.
Proof. vm_refl. Qed.
Lemma D_8a988 : decode_any W_8a988 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a9c0 : bv 32 := 0x00853583.
Lemma F_8a9c0 : fetch_word Asan.M.loaded_segments (0x8aa10 : word) = Some W_8a9c0.
Proof. vm_refl. Qed.
Lemma D_8a9c0 : decode_any W_8a9c0 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a9c4 : bv 32 := 0x01053503.
Lemma F_8a9c4 : fetch_word Asan.M.loaded_segments (0x8aa14 : word) = Some W_8a9c4.
Proof. vm_refl. Qed.
Lemma D_8a9c4 : decode_any W_8a9c4 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a9c8 : bv 32 := 0x00b53533.
Lemma F_8a9c8 : fetch_word Asan.M.loaded_segments (0x8aa18 : word) = Some W_8a9c8.
Proof. vm_refl. Qed.
Lemma D_8a9c8 : decode_any W_8a9c8 = Some (Op ALU_SLTU 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a9cc : bv 32 := 0x40a00533.
Lemma F_8a9cc : fetch_word Asan.M.loaded_segments (0x8aa1c : word) = Some W_8a9cc.
Proof. vm_refl. Qed.
Lemma D_8a9cc : decode_any W_8a9cc = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a9d0 : bv 32 := 0x00b57533.
Lemma F_8a9d0 : fetch_word Asan.M.loaded_segments (0x8aa20 : word) = Some W_8a9d0.
Proof. vm_refl. Qed.
Lemma D_8a9d0 : decode_any W_8a9d0 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a9d4 : bv 32 := 0x00008067.
Lemma F_8a9d4 : fetch_word Asan.M.loaded_segments (0x8aa24 : word) = Some W_8a9d4.
Proof. vm_refl. Qed.
Lemma D_8a9d4 : decode_any W_8a9d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a9d8 : bv 32 := 0x02850583.
Lemma F_8a9d8 : fetch_word Asan.M.loaded_segments (0x8aa28 : word) = Some W_8a9d8.
Proof. vm_refl. Qed.
Lemma D_8a9d8 : decode_any W_8a9d8 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a9dc : bv 32 := 0x0230000f.
Lemma F_8a9dc : fetch_word Asan.M.loaded_segments (0x8aa2c : word) = Some W_8a9dc.
Proof. vm_refl. Qed.
Lemma D_8a9dc : decode_any W_8a9dc = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8a9e0 : bv 32 := 0x02058c63.
Lemma F_8a9e0 : fetch_word Asan.M.loaded_segments (0x8aa30 : word) = Some W_8a9e0.
Proof. vm_refl. Qed.
Lemma D_8a9e0 : decode_any W_8a9e0 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa18 : bv 32 := 0x00853583.
Lemma F_8aa18 : fetch_word Asan.M.loaded_segments (0x8aa68 : word) = Some W_8aa18.
Proof. vm_refl. Qed.
Lemma D_8aa18 : decode_any W_8aa18 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa1c : bv 32 := 0x01053503.
Lemma F_8aa1c : fetch_word Asan.M.loaded_segments (0x8aa6c : word) = Some W_8aa1c.
Proof. vm_refl. Qed.
Lemma D_8aa1c : decode_any W_8aa1c = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa20 : bv 32 := 0x00b535b3.
Lemma F_8aa20 : fetch_word Asan.M.loaded_segments (0x8aa70 : word) = Some W_8aa20.
Proof. vm_refl. Qed.
Lemma D_8aa20 : decode_any W_8aa20 = Some (Op ALU_SLTU 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa24 : bv 32 := 0x40b005b3.
Lemma F_8aa24 : fetch_word Asan.M.loaded_segments (0x8aa74 : word) = Some W_8aa24.
Proof. vm_refl. Qed.
Lemma D_8aa24 : decode_any W_8aa24 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa28 : bv 32 := 0x00a5f533.
Lemma F_8aa28 : fetch_word Asan.M.loaded_segments (0x8aa78 : word) = Some W_8aa28.
Proof. vm_refl. Qed.
Lemma D_8aa28 : decode_any W_8aa28 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8aa2c : bv 32 := 0x00008067.
Lemma F_8aa2c : fetch_word Asan.M.loaded_segments (0x8aa7c : word) = Some W_8aa2c.
Proof. vm_refl. Qed.
Lemma D_8aa2c : decode_any W_8aa2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r69818_698c8.
Module Na0_code_r6de28_6df9c.
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

Definition W_8ef90 : bv 32 := 0xfe010113.
Lemma F_8ef90 : fetch_word Asan.M.loaded_segments (0x8efe0 : word) = Some W_8ef90.
Proof. vm_refl. Qed.
Lemma D_8ef90 : decode_any W_8ef90 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ef94 : bv 32 := 0x00113c23.
Lemma F_8ef94 : fetch_word Asan.M.loaded_segments (0x8efe4 : word) = Some W_8ef94.
Proof. vm_refl. Qed.
Lemma D_8ef94 : decode_any W_8ef94 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ef98 : bv 32 := 0x00813823.
Lemma F_8ef98 : fetch_word Asan.M.loaded_segments (0x8efe8 : word) = Some W_8ef98.
Proof. vm_refl. Qed.
Lemma D_8ef98 : decode_any W_8ef98 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ef9c : bv 32 := 0x00913423.
Lemma F_8ef9c : fetch_word Asan.M.loaded_segments (0x8efec : word) = Some W_8ef9c.
Proof. vm_refl. Qed.
Lemma D_8ef9c : decode_any W_8ef9c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8efa0 : bv 32 := 0x01213023.
Lemma F_8efa0 : fetch_word Asan.M.loaded_segments (0x8eff0 : word) = Some W_8efa0.
Proof. vm_refl. Qed.
Lemma D_8efa0 : decode_any W_8efa0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8efa4 : bv 32 := 0x00058413.
Lemma F_8efa4 : fetch_word Asan.M.loaded_segments (0x8eff4 : word) = Some W_8efa4.
Proof. vm_refl. Qed.
Lemma D_8efa4 : decode_any W_8efa4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8efa8 : bv 32 := 0x00050493.
Lemma F_8efa8 : fetch_word Asan.M.loaded_segments (0x8eff8 : word) = Some W_8efa8.
Proof. vm_refl. Qed.
Lemma D_8efa8 : decode_any W_8efa8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8efac : bv 32 := 0x09c000ef.
Lemma F_8efac : fetch_word Asan.M.loaded_segments (0x8effc : word) = Some W_8efac.
Proof. vm_refl. Qed.
Lemma D_8efac : decode_any W_8efac = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_8efb0 : bv 32 := 0x00162517.
Lemma F_8efb0 : fetch_word Asan.M.loaded_segments (0x8f000 : word) = Some W_8efb0.
Proof. vm_refl. Qed.
Lemma D_8efb0 : decode_any W_8efb0 = Some (Auipc 10 354, 4%Z).
Proof. vm_refl. Qed.

Definition W_8efb4 : bv 32 := 0x54050913.
Lemma F_8efb4 : fetch_word Asan.M.loaded_segments (0x8f004 : word) = Some W_8efb4.
Proof. vm_refl. Qed.
Lemma D_8efb4 : decode_any W_8efb4 = Some (OpImm ALU_ADD 18 10 1344, 4%Z).
Proof. vm_refl. Qed.

Definition W_8efb8 : bv 32 := 0x00093603.
Lemma F_8efb8 : fetch_word Asan.M.loaded_segments (0x8f008 : word) = Some W_8efb8.
Proof. vm_refl. Qed.
Lemma D_8efb8 : decode_any W_8efb8 = Some (Load SZ8 true 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8efbc : bv 32 := 0x06060a63.
Lemma F_8efbc : fetch_word Asan.M.loaded_segments (0x8f00c : word) = Some W_8efbc.
Proof. vm_refl. Qed.
Lemma D_8efbc : decode_any W_8efbc = Some (Branch BC_EQ 12 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f030 : bv 32 := 0x01813083.
Lemma F_8f030 : fetch_word Asan.M.loaded_segments (0x8f080 : word) = Some W_8f030.
Proof. vm_refl. Qed.
Lemma D_8f030 : decode_any W_8f030 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f034 : bv 32 := 0x01013403.
Lemma F_8f034 : fetch_word Asan.M.loaded_segments (0x8f084 : word) = Some W_8f034.
Proof. vm_refl. Qed.
Lemma D_8f034 : decode_any W_8f034 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f038 : bv 32 := 0x00813483.
Lemma F_8f038 : fetch_word Asan.M.loaded_segments (0x8f088 : word) = Some W_8f038.
Proof. vm_refl. Qed.
Lemma D_8f038 : decode_any W_8f038 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f03c : bv 32 := 0x00013903.
Lemma F_8f03c : fetch_word Asan.M.loaded_segments (0x8f08c : word) = Some W_8f03c.
Proof. vm_refl. Qed.
Lemma D_8f03c : decode_any W_8f03c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f040 : bv 32 := 0x02010113.
Lemma F_8f040 : fetch_word Asan.M.loaded_segments (0x8f090 : word) = Some W_8f040.
Proof. vm_refl. Qed.
Lemma D_8f040 : decode_any W_8f040 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f044 : bv 32 := 0x00008067.
Lemma F_8f044 : fetch_word Asan.M.loaded_segments (0x8f094 : word) = Some W_8f044.
Proof. vm_refl. Qed.
Lemma D_8f044 : decode_any W_8f044 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f048 : bv 32 := 0x00008067.
Lemma F_8f048 : fetch_word Asan.M.loaded_segments (0x8f098 : word) = Some W_8f048.
Proof. vm_refl. Qed.
Lemma D_8f048 : decode_any W_8f048 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f04c : bv 32 := 0xfe010113.
Lemma F_8f04c : fetch_word Asan.M.loaded_segments (0x8f09c : word) = Some W_8f04c.
Proof. vm_refl. Qed.
Lemma D_8f04c : decode_any W_8f04c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f050 : bv 32 := 0x00113c23.
Lemma F_8f050 : fetch_word Asan.M.loaded_segments (0x8f0a0 : word) = Some W_8f050.
Proof. vm_refl. Qed.
Lemma D_8f050 : decode_any W_8f050 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f054 : bv 32 := 0x00813823.
Lemma F_8f054 : fetch_word Asan.M.loaded_segments (0x8f0a4 : word) = Some W_8f054.
Proof. vm_refl. Qed.
Lemma D_8f054 : decode_any W_8f054 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f058 : bv 32 := 0x00913423.
Lemma F_8f058 : fetch_word Asan.M.loaded_segments (0x8f0a8 : word) = Some W_8f058.
Proof. vm_refl. Qed.
Lemma D_8f058 : decode_any W_8f058 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f05c : bv 32 := 0x00050413.
Lemma F_8f05c : fetch_word Asan.M.loaded_segments (0x8f0ac : word) = Some W_8f05c.
Proof. vm_refl. Qed.
Lemma D_8f05c : decode_any W_8f05c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f060 : bv 32 := 0x098000ef.
Lemma F_8f060 : fetch_word Asan.M.loaded_segments (0x8f0b0 : word) = Some W_8f060.
Proof. vm_refl. Qed.
Lemma D_8f060 : decode_any W_8f060 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f064 : bv 32 := 0x00050e63.
Lemma F_8f064 : fetch_word Asan.M.loaded_segments (0x8f0b4 : word) = Some W_8f064.
Proof. vm_refl. Qed.
Lemma D_8f064 : decode_any W_8f064 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f080 : bv 32 := 0x00040513.
Lemma F_8f080 : fetch_word Asan.M.loaded_segments (0x8f0d0 : word) = Some W_8f080.
Proof. vm_refl. Qed.
Lemma D_8f080 : decode_any W_8f080 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f084 : bv 32 := 0x07c000ef.
Lemma F_8f084 : fetch_word Asan.M.loaded_segments (0x8f0d4 : word) = Some W_8f084.
Proof. vm_refl. Qed.
Lemma D_8f084 : decode_any W_8f084 = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f088 : bv 32 := 0x00162517.
Lemma F_8f088 : fetch_word Asan.M.loaded_segments (0x8f0d8 : word) = Some W_8f088.
Proof. vm_refl. Qed.
Lemma D_8f088 : decode_any W_8f088 = Some (Auipc 10 354, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f08c : bv 32 := 0x46850493.
Lemma F_8f08c : fetch_word Asan.M.loaded_segments (0x8f0dc : word) = Some W_8f08c.
Proof. vm_refl. Qed.
Lemma D_8f08c : decode_any W_8f08c = Some (OpImm ALU_ADD 9 10 1128, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f090 : bv 32 := 0x0084b583.
Lemma F_8f090 : fetch_word Asan.M.loaded_segments (0x8f0e0 : word) = Some W_8f090.
Proof. vm_refl. Qed.
Lemma D_8f090 : decode_any W_8f090 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f094 : bv 32 := 0x04058663.
Lemma F_8f094 : fetch_word Asan.M.loaded_segments (0x8f0e4 : word) = Some W_8f094.
Proof. vm_refl. Qed.
Lemma D_8f094 : decode_any W_8f094 = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0e0 : bv 32 := 0x00000513.
Lemma F_8f0e0 : fetch_word Asan.M.loaded_segments (0x8f130 : word) = Some W_8f0e0.
Proof. vm_refl. Qed.
Lemma D_8f0e0 : decode_any W_8f0e0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0e4 : bv 32 := 0x01813083.
Lemma F_8f0e4 : fetch_word Asan.M.loaded_segments (0x8f134 : word) = Some W_8f0e4.
Proof. vm_refl. Qed.
Lemma D_8f0e4 : decode_any W_8f0e4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0e8 : bv 32 := 0x01013403.
Lemma F_8f0e8 : fetch_word Asan.M.loaded_segments (0x8f138 : word) = Some W_8f0e8.
Proof. vm_refl. Qed.
Lemma D_8f0e8 : decode_any W_8f0e8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0ec : bv 32 := 0x00813483.
Lemma F_8f0ec : fetch_word Asan.M.loaded_segments (0x8f13c : word) = Some W_8f0ec.
Proof. vm_refl. Qed.
Lemma D_8f0ec : decode_any W_8f0ec = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0f0 : bv 32 := 0x02010113.
Lemma F_8f0f0 : fetch_word Asan.M.loaded_segments (0x8f140 : word) = Some W_8f0f0.
Proof. vm_refl. Qed.
Lemma D_8f0f0 : decode_any W_8f0f0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0f4 : bv 32 := 0x00008067.
Lemma F_8f0f4 : fetch_word Asan.M.loaded_segments (0x8f144 : word) = Some W_8f0f4.
Proof. vm_refl. Qed.
Lemma D_8f0f4 : decode_any W_8f0f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0f8 : bv 32 := 0x00000513.
Lemma F_8f0f8 : fetch_word Asan.M.loaded_segments (0x8f148 : word) = Some W_8f0f8.
Proof. vm_refl. Qed.
Lemma D_8f0f8 : decode_any W_8f0f8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0fc : bv 32 := 0x00008067.
Lemma F_8f0fc : fetch_word Asan.M.loaded_segments (0x8f14c : word) = Some W_8f0fc.
Proof. vm_refl. Qed.
Lemma D_8f0fc : decode_any W_8f0fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f100 : bv 32 := 0x00008067.
Lemma F_8f100 : fetch_word Asan.M.loaded_segments (0x8f150 : word) = Some W_8f100.
Proof. vm_refl. Qed.
Lemma D_8f100 : decode_any W_8f100 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

End Na0_code_r6de28_6df9c.
