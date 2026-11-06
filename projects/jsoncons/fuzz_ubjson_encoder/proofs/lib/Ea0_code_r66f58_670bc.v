(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_81b1c : bv 32 := 0xfb010113.
Lemma F_81b1c : fetch_word Asan.M.loaded_segments (0x81b6c : word) = Some W_81b1c.
Proof. vm_refl. Qed.
Lemma D_81b1c : decode_any W_81b1c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b20 : bv 32 := 0x04113423.
Lemma F_81b20 : fetch_word Asan.M.loaded_segments (0x81b70 : word) = Some W_81b20.
Proof. vm_refl. Qed.
Lemma D_81b20 : decode_any W_81b20 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b24 : bv 32 := 0x04813023.
Lemma F_81b24 : fetch_word Asan.M.loaded_segments (0x81b74 : word) = Some W_81b24.
Proof. vm_refl. Qed.
Lemma D_81b24 : decode_any W_81b24 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b28 : bv 32 := 0x02913c23.
Lemma F_81b28 : fetch_word Asan.M.loaded_segments (0x81b78 : word) = Some W_81b28.
Proof. vm_refl. Qed.
Lemma D_81b28 : decode_any W_81b28 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b2c : bv 32 := 0x03213823.
Lemma F_81b2c : fetch_word Asan.M.loaded_segments (0x81b7c : word) = Some W_81b2c.
Proof. vm_refl. Qed.
Lemma D_81b2c : decode_any W_81b2c = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b30 : bv 32 := 0x03313423.
Lemma F_81b30 : fetch_word Asan.M.loaded_segments (0x81b80 : word) = Some W_81b30.
Proof. vm_refl. Qed.
Lemma D_81b30 : decode_any W_81b30 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b34 : bv 32 := 0x000c1517.
Lemma F_81b34 : fetch_word Asan.M.loaded_segments (0x81b84 : word) = Some W_81b34.
Proof. vm_refl. Qed.
Lemma D_81b34 : decode_any W_81b34 = Some (Auipc 10 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b38 : bv 32 := 0xb5450493.
Lemma F_81b38 : fetch_word Asan.M.loaded_segments (0x81b88 : word) = Some W_81b38.
Proof. vm_refl. Qed.
Lemma D_81b38 : decode_any W_81b38 = Some (OpImm ALU_ADD 9 10 2900, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b3c : bv 32 := 0x00048503.
Lemma F_81b3c : fetch_word Asan.M.loaded_segments (0x81b8c : word) = Some W_81b3c.
Proof. vm_refl. Qed.
Lemma D_81b3c : decode_any W_81b3c = Some (Load SZ1 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b40 : bv 32 := 0x00100593.
Lemma F_81b40 : fetch_word Asan.M.loaded_segments (0x81b90 : word) = Some W_81b40.
Proof. vm_refl. Qed.
Lemma D_81b40 : decode_any W_81b40 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b44 : bv 32 := 0x0230000f.
Lemma F_81b44 : fetch_word Asan.M.loaded_segments (0x81b94 : word) = Some W_81b44.
Proof. vm_refl. Qed.
Lemma D_81b44 : decode_any W_81b44 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b48 : bv 32 := 0x10b51e63.
Lemma F_81b48 : fetch_word Asan.M.loaded_segments (0x81b98 : word) = Some W_81b48.
Proof. vm_refl. Qed.
Lemma D_81b48 : decode_any W_81b48 = Some (Branch BC_NE 10 11 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b4c : bv 32 := 0xbe1fa0ef.
Lemma F_81b4c : fetch_word Asan.M.loaded_segments (0x81b9c : word) = Some W_81b4c.
Proof. vm_refl. Qed.
Lemma D_81b4c : decode_any W_81b4c = Some (Jal 1 2075616, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b50 : bv 32 := 0x0e051663.
Lemma F_81b50 : fetch_word Asan.M.loaded_segments (0x81ba0 : word) = Some W_81b50.
Proof. vm_refl. Qed.
Lemma D_81b50 : decode_any W_81b50 = Some (Branch BC_NE 10 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b54 : bv 32 := 0xfff8f517.
Lemma F_81b54 : fetch_word Asan.M.loaded_segments (0x81ba4 : word) = Some W_81b54.
Proof. vm_refl. Qed.
Lemma D_81b54 : decode_any W_81b54 = Some (Auipc 10 1048463, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b58 : bv 32 := 0x8c453403.
Lemma F_81b58 : fetch_word Asan.M.loaded_segments (0x81ba8 : word) = Some W_81b58.
Proof. vm_refl. Qed.
Lemma D_81b58 : decode_any W_81b58 = Some (Load SZ8 true 8 10 2244, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b5c : bv 32 := 0x02813023.
Lemma F_81b5c : fetch_word Asan.M.loaded_segments (0x81bac : word) = Some W_81b5c.
Proof. vm_refl. Qed.
Lemma D_81b5c : decode_any W_81b5c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b60 : bv 32 := 0x00813c23.
Lemma F_81b60 : fetch_word Asan.M.loaded_segments (0x81bb0 : word) = Some W_81b60.
Proof. vm_refl. Qed.
Lemma D_81b60 : decode_any W_81b60 = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b64 : bv 32 := 0x6b4020ef.
Lemma F_81b64 : fetch_word Asan.M.loaded_segments (0x81bb4 : word) = Some W_81b64.
Proof. vm_refl. Qed.
Lemma D_81b64 : decode_any W_81b64 = Some (Jal 1 9908, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b68 : bv 32 := 0x08050263.
Lemma F_81b68 : fetch_word Asan.M.loaded_segments (0x81bb8 : word) = Some W_81b68.
Proof. vm_refl. Qed.
Lemma D_81b68 : decode_any W_81b68 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b6c : bv 32 := 0x000b7597.
Lemma F_81b6c : fetch_word Asan.M.loaded_segments (0x81bbc : word) = Some W_81b6c.
Proof. vm_refl. Qed.
Lemma D_81b6c : decode_any W_81b6c = Some (Auipc 11 183, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b70 : bv 32 := 0x5dc5b903.
Lemma F_81b70 : fetch_word Asan.M.loaded_segments (0x81bc0 : word) = Some W_81b70.
Proof. vm_refl. Qed.
Lemma D_81b70 : decode_any W_81b70 = Some (Load SZ8 true 18 11 1500, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b74 : bv 32 := 0x00093403.
Lemma F_81b74 : fetch_word Asan.M.loaded_segments (0x81bc4 : word) = Some W_81b74.
Proof. vm_refl. Qed.
Lemma D_81b74 : decode_any W_81b74 = Some (Load SZ8 true 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b78 : bv 32 := 0x00041c63.
Lemma F_81b78 : fetch_word Asan.M.loaded_segments (0x81bc8 : word) = Some W_81b78.
Proof. vm_refl. Qed.
Lemma D_81b78 : decode_any W_81b78 = Some (Branch BC_NE 8 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b90 : bv 32 := 0x04d020ef.
Lemma F_81b90 : fetch_word Asan.M.loaded_segments (0x81be0 : word) = Some W_81b90.
Proof. vm_refl. Qed.
Lemma D_81b90 : decode_any W_81b90 = Some (Jal 1 10316, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b94 : bv 32 := 0x00050613.
Lemma F_81b94 : fetch_word Asan.M.loaded_segments (0x81be4 : word) = Some W_81b94.
Proof. vm_refl. Qed.
Lemma D_81b94 : decode_any W_81b94 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b98 : bv 32 := 0x00a13c23.
Lemma F_81b98 : fetch_word Asan.M.loaded_segments (0x81be8 : word) = Some W_81b98.
Proof. vm_refl. Qed.
Lemma D_81b98 : decode_any W_81b98 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_81b9c : bv 32 := 0x01010513.
Lemma F_81b9c : fetch_word Asan.M.loaded_segments (0x81bec : word) = Some W_81b9c.
Proof. vm_refl. Qed.
Lemma D_81b9c : decode_any W_81b9c = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ba0 : bv 32 := 0x40850533.
Lemma F_81ba0 : fetch_word Asan.M.loaded_segments (0x81bf0 : word) = Some W_81ba0.
Proof. vm_refl. Qed.
Lemma D_81ba0 : decode_any W_81ba0 = Some (Op ALU_SUB 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ba4 : bv 32 := 0x408006b3.
Lemma F_81ba4 : fetch_word Asan.M.loaded_segments (0x81bf4 : word) = Some W_81ba4.
Proof. vm_refl. Qed.
Lemma D_81ba4 : decode_any W_81ba4 = Some (Op ALU_SUB 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81ba8 : bv 32 := 0x00d576b3.
Lemma F_81ba8 : fetch_word Asan.M.loaded_segments (0x81bf8 : word) = Some W_81ba8.
Proof. vm_refl. Qed.
Lemma D_81ba8 : decode_any W_81ba8 = Some (Op ALU_AND 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bac : bv 32 := 0x02d13023.
Lemma F_81bac : fetch_word Asan.M.loaded_segments (0x81bfc : word) = Some W_81bac.
Proof. vm_refl. Qed.
Lemma D_81bac : decode_any W_81bac = Some (Store SZ8 2 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bb0 : bv 32 := 0x40d60733.
Lemma F_81bb0 : fetch_word Asan.M.loaded_segments (0x81c00 : word) = Some W_81bb0.
Proof. vm_refl. Qed.
Lemma D_81bb0 : decode_any W_81bb0 = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bb4 : bv 32 := 0x04000537.
Lemma F_81bb4 : fetch_word Asan.M.loaded_segments (0x81c04 : word) = Some W_81bb4.
Proof. vm_refl. Qed.
Lemma D_81bb4 : decode_any W_81bb4 = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bb8 : bv 32 := 0x0015051b.
Lemma F_81bb8 : fetch_word Asan.M.loaded_segments (0x81c08 : word) = Some W_81bb8.
Proof. vm_refl. Qed.
Lemma D_81bb8 : decode_any W_81bb8 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81bbc : bv 32 := 0x06a76263.
Lemma F_81bbc : fetch_word Asan.M.loaded_segments (0x81c0c : word) = Some W_81bbc.
Proof. vm_refl. Qed.
Lemma D_81bbc : decode_any W_81bbc = Some (Branch BC_LTU 14 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c20 : bv 32 := 0x00770713.
Lemma F_81c20 : fetch_word Asan.M.loaded_segments (0x81c70 : word) = Some W_81c20.
Proof. vm_refl. Qed.
Lemma D_81c20 : decode_any W_81c20 = Some (OpImm ALU_ADD 14 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c24 : bv 32 := 0x10000537.
Lemma F_81c24 : fetch_word Asan.M.loaded_segments (0x81c74 : word) = Some W_81c24.
Proof. vm_refl. Qed.
Lemma D_81c24 : decode_any W_81c24 = Some (Lui 10 65536, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c28 : bv 32 := 0xff85051b.
Lemma F_81c28 : fetch_word Asan.M.loaded_segments (0x81c78 : word) = Some W_81c28.
Proof. vm_refl. Qed.
Lemma D_81c28 : decode_any W_81c28 = Some (OpImm32 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c2c : bv 32 := 0x00a775b3.
Lemma F_81c2c : fetch_word Asan.M.loaded_segments (0x81c7c : word) = Some W_81c2c.
Proof. vm_refl. Qed.
Lemma D_81c2c : decode_any W_81c2c = Some (Op ALU_AND 11 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c30 : bv 32 := 0x00068513.
Lemma F_81c30 : fetch_word Asan.M.loaded_segments (0x81c80 : word) = Some W_81c30.
Proof. vm_refl. Qed.
Lemma D_81c30 : decode_any W_81c30 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c34 : bv 32 := 0x00000613.
Lemma F_81c34 : fetch_word Asan.M.loaded_segments (0x81c84 : word) = Some W_81c34.
Proof. vm_refl. Qed.
Lemma D_81c34 : decode_any W_81c34 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c38 : bv 32 := 0x835f90ef.
Lemma F_81c38 : fetch_word Asan.M.loaded_segments (0x81c88 : word) = Some W_81c38.
Proof. vm_refl. Qed.
Lemma D_81c38 : decode_any W_81c38 = Some (Jal 1 2070580, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c3c : bv 32 := 0x5dc020ef.
Lemma F_81c3c : fetch_word Asan.M.loaded_segments (0x81c8c : word) = Some W_81c3c.
Proof. vm_refl. Qed.
Lemma D_81c3c : decode_any W_81c3c = Some (Jal 1 9692, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c40 : bv 32 := 0x02050263.
Lemma F_81c40 : fetch_word Asan.M.loaded_segments (0x81c90 : word) = Some W_81c40.
Proof. vm_refl. Qed.
Lemma D_81c40 : decode_any W_81c40 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c44 : bv 32 := 0x02850583.
Lemma F_81c44 : fetch_word Asan.M.loaded_segments (0x81c94 : word) = Some W_81c44.
Proof. vm_refl. Qed.
Lemma D_81c44 : decode_any W_81c44 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c48 : bv 32 := 0x00059e63.
Lemma F_81c48 : fetch_word Asan.M.loaded_segments (0x81c98 : word) = Some W_81c48.
Proof. vm_refl. Qed.
Lemma D_81c48 : decode_any W_81c48 = Some (Branch BC_NE 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c4c : bv 32 := 0x04853503.
Lemma F_81c4c : fetch_word Asan.M.loaded_segments (0x81c9c : word) = Some W_81c4c.
Proof. vm_refl. Qed.
Lemma D_81c4c : decode_any W_81c4c = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c50 : bv 32 := 0x00253593.
Lemma F_81c50 : fetch_word Asan.M.loaded_segments (0x81ca0 : word) = Some W_81c50.
Proof. vm_refl. Qed.
Lemma D_81c50 : decode_any W_81c50 = Some (OpImm ALU_SLTU 11 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c54 : bv 32 := 0xfff58593.
Lemma F_81c54 : fetch_word Asan.M.loaded_segments (0x81ca4 : word) = Some W_81c54.
Proof. vm_refl. Qed.
Lemma D_81c54 : decode_any W_81c54 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c58 : bv 32 := 0x00a5f533.
Lemma F_81c58 : fetch_word Asan.M.loaded_segments (0x81ca8 : word) = Some W_81c58.
Proof. vm_refl. Qed.
Lemma D_81c58 : decode_any W_81c58 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c5c : bv 32 := 0x00050463.
Lemma F_81c5c : fetch_word Asan.M.loaded_segments (0x81cac : word) = Some W_81c5c.
Proof. vm_refl. Qed.
Lemma D_81c5c : decode_any W_81c5c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c60 : bv 32 := 0xe00dc0ef.
Lemma F_81c60 : fetch_word Asan.M.loaded_segments (0x81cb0 : word) = Some W_81c60.
Proof. vm_refl. Qed.
Lemma D_81c60 : decode_any W_81c60 = Some (Jal 1 1951232, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c64 : bv 32 := 0x04813083.
Lemma F_81c64 : fetch_word Asan.M.loaded_segments (0x81cb4 : word) = Some W_81c64.
Proof. vm_refl. Qed.
Lemma D_81c64 : decode_any W_81c64 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c68 : bv 32 := 0x04013403.
Lemma F_81c68 : fetch_word Asan.M.loaded_segments (0x81cb8 : word) = Some W_81c68.
Proof. vm_refl. Qed.
Lemma D_81c68 : decode_any W_81c68 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c6c : bv 32 := 0x03813483.
Lemma F_81c6c : fetch_word Asan.M.loaded_segments (0x81cbc : word) = Some W_81c6c.
Proof. vm_refl. Qed.
Lemma D_81c6c : decode_any W_81c6c = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c70 : bv 32 := 0x03013903.
Lemma F_81c70 : fetch_word Asan.M.loaded_segments (0x81cc0 : word) = Some W_81c70.
Proof. vm_refl. Qed.
Lemma D_81c70 : decode_any W_81c70 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c74 : bv 32 := 0x02813983.
Lemma F_81c74 : fetch_word Asan.M.loaded_segments (0x81cc4 : word) = Some W_81c74.
Proof. vm_refl. Qed.
Lemma D_81c74 : decode_any W_81c74 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c78 : bv 32 := 0x05010113.
Lemma F_81c78 : fetch_word Asan.M.loaded_segments (0x81cc8 : word) = Some W_81c78.
Proof. vm_refl. Qed.
Lemma D_81c78 : decode_any W_81c78 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_81c7c : bv 32 := 0x00008067.
Lemma F_81c7c : fetch_word Asan.M.loaded_segments (0x81ccc : word) = Some W_81c7c.
Proof. vm_refl. Qed.
Lemma D_81c7c : decode_any W_81c7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
