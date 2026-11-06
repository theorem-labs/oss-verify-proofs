(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a2b2c : bv 32 := 0xf9010113.
Lemma F_a2b2c : fetch_word Ubsan.M.loaded_segments (0xa2b78 : word) = Some W_a2b2c.
Proof. vm_refl. Qed.
Lemma D_a2b2c : decode_any W_a2b2c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b30 : bv 32 := 0x06113423.
Lemma F_a2b30 : fetch_word Ubsan.M.loaded_segments (0xa2b7c : word) = Some W_a2b30.
Proof. vm_refl. Qed.
Lemma D_a2b30 : decode_any W_a2b30 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b34 : bv 32 := 0x06813023.
Lemma F_a2b34 : fetch_word Ubsan.M.loaded_segments (0xa2b80 : word) = Some W_a2b34.
Proof. vm_refl. Qed.
Lemma D_a2b34 : decode_any W_a2b34 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b38 : bv 32 := 0x04913c23.
Lemma F_a2b38 : fetch_word Ubsan.M.loaded_segments (0xa2b84 : word) = Some W_a2b38.
Proof. vm_refl. Qed.
Lemma D_a2b38 : decode_any W_a2b38 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b3c : bv 32 := 0x05213823.
Lemma F_a2b3c : fetch_word Ubsan.M.loaded_segments (0xa2b88 : word) = Some W_a2b3c.
Proof. vm_refl. Qed.
Lemma D_a2b3c : decode_any W_a2b3c = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b40 : bv 32 := 0x05313423.
Lemma F_a2b40 : fetch_word Ubsan.M.loaded_segments (0xa2b8c : word) = Some W_a2b40.
Proof. vm_refl. Qed.
Lemma D_a2b40 : decode_any W_a2b40 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b44 : bv 32 := 0x05413023.
Lemma F_a2b44 : fetch_word Ubsan.M.loaded_segments (0xa2b90 : word) = Some W_a2b44.
Proof. vm_refl. Qed.
Lemma D_a2b44 : decode_any W_a2b44 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b48 : bv 32 := 0x03513c23.
Lemma F_a2b48 : fetch_word Ubsan.M.loaded_segments (0xa2b94 : word) = Some W_a2b48.
Proof. vm_refl. Qed.
Lemma D_a2b48 : decode_any W_a2b48 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b4c : bv 32 := 0x03613823.
Lemma F_a2b4c : fetch_word Ubsan.M.loaded_segments (0xa2b98 : word) = Some W_a2b4c.
Proof. vm_refl. Qed.
Lemma D_a2b4c : decode_any W_a2b4c = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b50 : bv 32 := 0x00060413.
Lemma F_a2b50 : fetch_word Ubsan.M.loaded_segments (0xa2b9c : word) = Some W_a2b50.
Proof. vm_refl. Qed.
Lemma D_a2b50 : decode_any W_a2b50 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b54 : bv 32 := 0x00050493.
Lemma F_a2b54 : fetch_word Ubsan.M.loaded_segments (0xa2ba0 : word) = Some W_a2b54.
Proof. vm_refl. Qed.
Lemma D_a2b54 : decode_any W_a2b54 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b58 : bv 32 := 0x00017517.
Lemma F_a2b58 : fetch_word Ubsan.M.loaded_segments (0xa2ba4 : word) = Some W_a2b58.
Proof. vm_refl. Qed.
Lemma D_a2b58 : decode_any W_a2b58 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b5c : bv 32 := 0x27c53a83.
Lemma F_a2b5c : fetch_word Ubsan.M.loaded_segments (0xa2ba8 : word) = Some W_a2b5c.
Proof. vm_refl. Qed.
Lemma D_a2b5c : decode_any W_a2b5c = Some (Load SZ8 true 21 10 636, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b60 : bv 32 := 0x000ab503.
Lemma F_a2b60 : fetch_word Ubsan.M.loaded_segments (0xa2bac : word) = Some W_a2b60.
Proof. vm_refl. Qed.
Lemma D_a2b60 : decode_any W_a2b60 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b64 : bv 32 := 0x02a13423.
Lemma F_a2b64 : fetch_word Ubsan.M.loaded_segments (0xa2bb0 : word) = Some W_a2b64.
Proof. vm_refl. Qed.
Lemma D_a2b64 : decode_any W_a2b64 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b68 : bv 32 := 0x0284b503.
Lemma F_a2b68 : fetch_word Ubsan.M.loaded_segments (0xa2bb4 : word) = Some W_a2b68.
Proof. vm_refl. Qed.
Lemma D_a2b68 : decode_any W_a2b68 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b6c : bv 32 := 0x0384b603.
Lemma F_a2b6c : fetch_word Ubsan.M.loaded_segments (0xa2bb8 : word) = Some W_a2b6c.
Proof. vm_refl. Qed.
Lemma D_a2b6c : decode_any W_a2b6c = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b70 : bv 32 := 0x40c50b33.
Lemma F_a2b70 : fetch_word Ubsan.M.loaded_segments (0xa2bbc : word) = Some W_a2b70.
Proof. vm_refl. Qed.
Lemma D_a2b70 : decode_any W_a2b70 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b74 : bv 32 := 0x00c546b3.
Lemma F_a2b74 : fetch_word Ubsan.M.loaded_segments (0xa2bc0 : word) = Some W_a2b74.
Proof. vm_refl. Qed.
Lemma D_a2b74 : decode_any W_a2b74 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b78 : bv 32 := 0x00c13423.
Lemma F_a2b78 : fetch_word Ubsan.M.loaded_segments (0xa2bc4 : word) = Some W_a2b78.
Proof. vm_refl. Qed.
Lemma D_a2b78 : decode_any W_a2b78 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b7c : bv 32 := 0x01613823.
Lemma F_a2b7c : fetch_word Ubsan.M.loaded_segments (0xa2bc8 : word) = Some W_a2b7c.
Proof. vm_refl. Qed.
Lemma D_a2b7c : decode_any W_a2b7c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b80 : bv 32 := 0x00b13c23.
Lemma F_a2b80 : fetch_word Ubsan.M.loaded_segments (0xa2bcc : word) = Some W_a2b80.
Proof. vm_refl. Qed.
Lemma D_a2b80 : decode_any W_a2b80 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b84 : bv 32 := 0x02813023.
Lemma F_a2b84 : fetch_word Ubsan.M.loaded_segments (0xa2bd0 : word) = Some W_a2b84.
Proof. vm_refl. Qed.
Lemma D_a2b84 : decode_any W_a2b84 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b88 : bv 32 := 0x008b0b33.
Lemma F_a2b88 : fetch_word Ubsan.M.loaded_segments (0xa2bd4 : word) = Some W_a2b88.
Proof. vm_refl. Qed.
Lemma D_a2b88 : decode_any W_a2b88 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b8c : bv 32 := 0x00d03933.
Lemma F_a2b8c : fetch_word Ubsan.M.loaded_segments (0xa2bd8 : word) = Some W_a2b8c.
Proof. vm_refl. Qed.
Lemma D_a2b8c : decode_any W_a2b8c = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b90 : bv 32 := 0x00c50663.
Lemma F_a2b90 : fetch_word Ubsan.M.loaded_segments (0xa2bdc : word) = Some W_a2b90.
Proof. vm_refl. Qed.
Lemma D_a2b90 : decode_any W_a2b90 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b94 : bv 32 := 0x00810993.
Lemma F_a2b94 : fetch_word Ubsan.M.loaded_segments (0xa2be0 : word) = Some W_a2b94.
Proof. vm_refl. Qed.
Lemma D_a2b94 : decode_any W_a2b94 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b98 : bv 32 := 0x0080006f.
Lemma F_a2b98 : fetch_word Ubsan.M.loaded_segments (0xa2be4 : word) = Some W_a2b98.
Proof. vm_refl. Qed.
Lemma D_a2b98 : decode_any W_a2b98 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2b9c : bv 32 := 0x01810993.
Lemma F_a2b9c : fetch_word Ubsan.M.loaded_segments (0xa2be8 : word) = Some W_a2b9c.
Proof. vm_refl. Qed.
Lemma D_a2b9c : decode_any W_a2b9c = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2ba0 : bv 32 := 0x0784a503.
Lemma F_a2ba0 : fetch_word Ubsan.M.loaded_segments (0xa2bec : word) = Some W_a2ba0.
Proof. vm_refl. Qed.
Lemma D_a2ba0 : decode_any W_a2ba0 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2ba4 : bv 32 := 0x00190913.
Lemma F_a2ba4 : fetch_word Ubsan.M.loaded_segments (0xa2bf0 : word) = Some W_a2ba4.
Proof. vm_refl. Qed.
Lemma D_a2ba4 : decode_any W_a2ba4 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2ba8 : bv 32 := 0x04200893.
Lemma F_a2ba8 : fetch_word Ubsan.M.loaded_segments (0xa2bf4 : word) = Some W_a2ba8.
Proof. vm_refl. Qed.
Lemma D_a2ba8 : decode_any W_a2ba8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bac : bv 32 := 0x00098593.
Lemma F_a2bac : fetch_word Ubsan.M.loaded_segments (0xa2bf8 : word) = Some W_a2bac.
Proof. vm_refl. Qed.
Lemma D_a2bac : decode_any W_a2bac = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bb0 : bv 32 := 0x00090613.
Lemma F_a2bb0 : fetch_word Ubsan.M.loaded_segments (0xa2bfc : word) = Some W_a2bb0.
Proof. vm_refl. Qed.
Lemma D_a2bb0 : decode_any W_a2bb0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bb4 : bv 32 := 0x00000073.
Lemma F_a2bb4 : fetch_word Ubsan.M.loaded_segments (0xa2c00 : word) = Some W_a2bb4.
Proof. vm_refl. Qed.
Lemma D_a2bb4 : decode_any W_a2bb4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a2bb4 : is_ecall W_a2bb4 = true.
Proof. reflexivity. Qed.

Definition W_a2bb8 : bv 32 := 0xf31fa0ef.
Lemma F_a2bb8 : fetch_word Ubsan.M.loaded_segments (0xa2c04 : word) = Some W_a2bb8.
Proof. vm_refl. Qed.
Lemma D_a2bb8 : decode_any W_a2bb8 = Some (Jal 1 2076464, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bbc : bv 32 := 0x09651863.
Lemma F_a2bbc : fetch_word Ubsan.M.loaded_segments (0xa2c08 : word) = Some W_a2bbc.
Proof. vm_refl. Qed.
Lemma D_a2bbc : decode_any W_a2bbc = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bc0 : bv 32 := 0x0584b503.
Lemma F_a2bc0 : fetch_word Ubsan.M.loaded_segments (0xa2c0c : word) = Some W_a2bc0.
Proof. vm_refl. Qed.
Lemma D_a2bc0 : decode_any W_a2bc0 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bc4 : bv 32 := 0x0604b583.
Lemma F_a2bc4 : fetch_word Ubsan.M.loaded_segments (0xa2c10 : word) = Some W_a2bc4.
Proof. vm_refl. Qed.
Lemma D_a2bc4 : decode_any W_a2bc4 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bc8 : bv 32 := 0x00b505b3.
Lemma F_a2bc8 : fetch_word Ubsan.M.loaded_segments (0xa2c14 : word) = Some W_a2bc8.
Proof. vm_refl. Qed.
Lemma D_a2bc8 : decode_any W_a2bc8 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bcc : bv 32 := 0x02b4b023.
Lemma F_a2bcc : fetch_word Ubsan.M.loaded_segments (0xa2c18 : word) = Some W_a2bcc.
Proof. vm_refl. Qed.
Lemma D_a2bcc : decode_any W_a2bcc = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bd0 : bv 32 := 0x02a4b423.
Lemma F_a2bd0 : fetch_word Ubsan.M.loaded_segments (0xa2c1c : word) = Some W_a2bd0.
Proof. vm_refl. Qed.
Lemma D_a2bd0 : decode_any W_a2bd0 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bd4 : bv 32 := 0x02a4bc23.
Lemma F_a2bd4 : fetch_word Ubsan.M.loaded_segments (0xa2c20 : word) = Some W_a2bd4.
Proof. vm_refl. Qed.
Lemma D_a2bd4 : decode_any W_a2bd4 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bd8 : bv 32 := 0x00040513.
Lemma F_a2bd8 : fetch_word Ubsan.M.loaded_segments (0xa2c24 : word) = Some W_a2bd8.
Proof. vm_refl. Qed.
Lemma D_a2bd8 : decode_any W_a2bd8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bdc : bv 32 := 0x000ab583.
Lemma F_a2bdc : fetch_word Ubsan.M.loaded_segments (0xa2c28 : word) = Some W_a2bdc.
Proof. vm_refl. Qed.
Lemma D_a2bdc : decode_any W_a2bdc = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2be0 : bv 32 := 0x02813603.
Lemma F_a2be0 : fetch_word Ubsan.M.loaded_segments (0xa2c2c : word) = Some W_a2be0.
Proof. vm_refl. Qed.
Lemma D_a2be0 : decode_any W_a2be0 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2be4 : bv 32 := 0x0cc59a63.
Lemma F_a2be4 : fetch_word Ubsan.M.loaded_segments (0xa2c30 : word) = Some W_a2be4.
Proof. vm_refl. Qed.
Lemma D_a2be4 : decode_any W_a2be4 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2be8 : bv 32 := 0x06813083.
Lemma F_a2be8 : fetch_word Ubsan.M.loaded_segments (0xa2c34 : word) = Some W_a2be8.
Proof. vm_refl. Qed.
Lemma D_a2be8 : decode_any W_a2be8 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bec : bv 32 := 0x06013403.
Lemma F_a2bec : fetch_word Ubsan.M.loaded_segments (0xa2c38 : word) = Some W_a2bec.
Proof. vm_refl. Qed.
Lemma D_a2bec : decode_any W_a2bec = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bf0 : bv 32 := 0x05813483.
Lemma F_a2bf0 : fetch_word Ubsan.M.loaded_segments (0xa2c3c : word) = Some W_a2bf0.
Proof. vm_refl. Qed.
Lemma D_a2bf0 : decode_any W_a2bf0 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bf4 : bv 32 := 0x05013903.
Lemma F_a2bf4 : fetch_word Ubsan.M.loaded_segments (0xa2c40 : word) = Some W_a2bf4.
Proof. vm_refl. Qed.
Lemma D_a2bf4 : decode_any W_a2bf4 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bf8 : bv 32 := 0x04813983.
Lemma F_a2bf8 : fetch_word Ubsan.M.loaded_segments (0xa2c44 : word) = Some W_a2bf8.
Proof. vm_refl. Qed.
Lemma D_a2bf8 : decode_any W_a2bf8 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2bfc : bv 32 := 0x04013a03.
Lemma F_a2bfc : fetch_word Ubsan.M.loaded_segments (0xa2c48 : word) = Some W_a2bfc.
Proof. vm_refl. Qed.
Lemma D_a2bfc : decode_any W_a2bfc = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c00 : bv 32 := 0x03813a83.
Lemma F_a2c00 : fetch_word Ubsan.M.loaded_segments (0xa2c4c : word) = Some W_a2c00.
Proof. vm_refl. Qed.
Lemma D_a2c00 : decode_any W_a2c00 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c04 : bv 32 := 0x03013b03.
Lemma F_a2c04 : fetch_word Ubsan.M.loaded_segments (0xa2c50 : word) = Some W_a2c04.
Proof. vm_refl. Qed.
Lemma D_a2c04 : decode_any W_a2c04 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c08 : bv 32 := 0x07010113.
Lemma F_a2c08 : fetch_word Ubsan.M.loaded_segments (0xa2c54 : word) = Some W_a2c08.
Proof. vm_refl. Qed.
Lemma D_a2c08 : decode_any W_a2c08 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c0c : bv 32 := 0x00008067.
Lemma F_a2c0c : fetch_word Ubsan.M.loaded_segments (0xa2c58 : word) = Some W_a2c0c.
Proof. vm_refl. Qed.
Lemma D_a2c0c : decode_any W_a2c0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c10 : bv 32 := 0x00800713.
Lemma F_a2c10 : fetch_word Ubsan.M.loaded_segments (0xa2c5c : word) = Some W_a2c10.
Proof. vm_refl. Qed.
Lemma D_a2c10 : decode_any W_a2c10 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c14 : bv 32 := 0x000a0593.
Lemma F_a2c14 : fetch_word Ubsan.M.loaded_segments (0xa2c60 : word) = Some W_a2c14.
Proof. vm_refl. Qed.
Lemma D_a2c14 : decode_any W_a2c14 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c18 : bv 32 := 0x00e98733.
Lemma F_a2c18 : fetch_word Ubsan.M.loaded_segments (0xa2c64 : word) = Some W_a2c18.
Proof. vm_refl. Qed.
Lemma D_a2c18 : decode_any W_a2c18 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c1c : bv 32 := 0x00073783.
Lemma F_a2c1c : fetch_word Ubsan.M.loaded_segments (0xa2c68 : word) = Some W_a2c1c.
Proof. vm_refl. Qed.
Lemma D_a2c1c : decode_any W_a2c1c = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c20 : bv 32 := 0x40ab0b33.
Lemma F_a2c20 : fetch_word Ubsan.M.loaded_segments (0xa2c6c : word) = Some W_a2c20.
Proof. vm_refl. Qed.
Lemma D_a2c20 : decode_any W_a2c20 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c24 : bv 32 := 0x0784a503.
Lemma F_a2c24 : fetch_word Ubsan.M.loaded_segments (0xa2c70 : word) = Some W_a2c24.
Proof. vm_refl. Qed.
Lemma D_a2c24 : decode_any W_a2c24 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c28 : bv 32 := 0x40c9093b.
Lemma F_a2c28 : fetch_word Ubsan.M.loaded_segments (0xa2c74 : word) = Some W_a2c28.
Proof. vm_refl. Qed.
Lemma D_a2c28 : decode_any W_a2c28 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c2c : bv 32 := 0x40d787b3.
Lemma F_a2c2c : fetch_word Ubsan.M.loaded_segments (0xa2c78 : word) = Some W_a2c2c.
Proof. vm_refl. Qed.
Lemma D_a2c2c : decode_any W_a2c2c = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c30 : bv 32 := 0x00f73023.
Lemma F_a2c30 : fetch_word Ubsan.M.loaded_segments (0xa2c7c : word) = Some W_a2c30.
Proof. vm_refl. Qed.
Lemma D_a2c30 : decode_any W_a2c30 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c34 : bv 32 := 0x04200893.
Lemma F_a2c34 : fetch_word Ubsan.M.loaded_segments (0xa2c80 : word) = Some W_a2c34.
Proof. vm_refl. Qed.
Lemma D_a2c34 : decode_any W_a2c34 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c38 : bv 32 := 0x00090613.
Lemma F_a2c38 : fetch_word Ubsan.M.loaded_segments (0xa2c84 : word) = Some W_a2c38.
Proof. vm_refl. Qed.
Lemma D_a2c38 : decode_any W_a2c38 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c3c : bv 32 := 0x00000073.
Lemma F_a2c3c : fetch_word Ubsan.M.loaded_segments (0xa2c88 : word) = Some W_a2c3c.
Proof. vm_refl. Qed.
Lemma D_a2c3c : decode_any W_a2c3c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a2c3c : is_ecall W_a2c3c = true.
Proof. reflexivity. Qed.

Definition W_a2c40 : bv 32 := 0xea9fa0ef.
Lemma F_a2c40 : fetch_word Ubsan.M.loaded_segments (0xa2c8c : word) = Some W_a2c40.
Proof. vm_refl. Qed.
Lemma D_a2c40 : decode_any W_a2c40 = Some (Jal 1 2076328, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c44 : bv 32 := 0x000a0993.
Lemma F_a2c44 : fetch_word Ubsan.M.loaded_segments (0xa2c90 : word) = Some W_a2c44.
Proof. vm_refl. Qed.
Lemma D_a2c44 : decode_any W_a2c44 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c48 : bv 32 := 0xf7650ce3.
Lemma F_a2c48 : fetch_word Ubsan.M.loaded_segments (0xa2c94 : word) = Some W_a2c48.
Proof. vm_refl. Qed.
Lemma D_a2c48 : decode_any W_a2c48 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c4c : bv 32 := 0x02054c63.
Lemma F_a2c4c : fetch_word Ubsan.M.loaded_segments (0xa2c98 : word) = Some W_a2c4c.
Proof. vm_refl. Qed.
Lemma D_a2c4c : decode_any W_a2c4c = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c50 : bv 32 := 0x0089b583.
Lemma F_a2c50 : fetch_word Ubsan.M.loaded_segments (0xa2c9c : word) = Some W_a2c50.
Proof. vm_refl. Qed.
Lemma D_a2c50 : decode_any W_a2c50 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c54 : bv 32 := 0x00a5b633.
Lemma F_a2c54 : fetch_word Ubsan.M.loaded_segments (0xa2ca0 : word) = Some W_a2c54.
Proof. vm_refl. Qed.
Lemma D_a2c54 : decode_any W_a2c54 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c58 : bv 32 := 0x00461a13.
Lemma F_a2c58 : fetch_word Ubsan.M.loaded_segments (0xa2ca4 : word) = Some W_a2c58.
Proof. vm_refl. Qed.
Lemma D_a2c58 : decode_any W_a2c58 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c5c : bv 32 := 0x01498a33.
Lemma F_a2c5c : fetch_word Ubsan.M.loaded_segments (0xa2ca8 : word) = Some W_a2c5c.
Proof. vm_refl. Qed.
Lemma D_a2c5c : decode_any W_a2c5c = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c60 : bv 32 := 0x000a3703.
Lemma F_a2c60 : fetch_word Ubsan.M.loaded_segments (0xa2cac : word) = Some W_a2c60.
Proof. vm_refl. Qed.
Lemma D_a2c60 : decode_any W_a2c60 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c64 : bv 32 := 0x40c006b3.
Lemma F_a2c64 : fetch_word Ubsan.M.loaded_segments (0xa2cb0 : word) = Some W_a2c64.
Proof. vm_refl. Qed.
Lemma D_a2c64 : decode_any W_a2c64 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c68 : bv 32 := 0x00b6f6b3.
Lemma F_a2c68 : fetch_word Ubsan.M.loaded_segments (0xa2cb4 : word) = Some W_a2c68.
Proof. vm_refl. Qed.
Lemma D_a2c68 : decode_any W_a2c68 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c6c : bv 32 := 0x40d506b3.
Lemma F_a2c6c : fetch_word Ubsan.M.loaded_segments (0xa2cb8 : word) = Some W_a2c6c.
Proof. vm_refl. Qed.
Lemma D_a2c6c : decode_any W_a2c6c = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c70 : bv 32 := 0x00d70733.
Lemma F_a2c70 : fetch_word Ubsan.M.loaded_segments (0xa2cbc : word) = Some W_a2c70.
Proof. vm_refl. Qed.
Lemma D_a2c70 : decode_any W_a2c70 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c74 : bv 32 := 0x00ea3023.
Lemma F_a2c74 : fetch_word Ubsan.M.loaded_segments (0xa2cc0 : word) = Some W_a2c74.
Proof. vm_refl. Qed.
Lemma D_a2c74 : decode_any W_a2c74 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c78 : bv 32 := 0xf8a5fce3.
Lemma F_a2c78 : fetch_word Ubsan.M.loaded_segments (0xa2cc4 : word) = Some W_a2c78.
Proof. vm_refl. Qed.
Lemma D_a2c78 : decode_any W_a2c78 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c7c : bv 32 := 0x01800713.
Lemma F_a2c7c : fetch_word Ubsan.M.loaded_segments (0xa2cc8 : word) = Some W_a2c7c.
Proof. vm_refl. Qed.
Lemma D_a2c7c : decode_any W_a2c7c = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2c80 : bv 32 := 0xf95ff06f.
Lemma F_a2c80 : fetch_word Ubsan.M.loaded_segments (0xa2ccc : word) = Some W_a2c80.
Proof. vm_refl. Qed.
Lemma D_a2c80 : decode_any W_a2c80 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2cc4 : bv 32 := 0x00008067.
Lemma F_a2cc4 : fetch_word Ubsan.M.loaded_segments (0xa2d10 : word) = Some W_a2cc4.
Proof. vm_refl. Qed.
Lemma D_a2cc4 : decode_any W_a2cc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2fcc : bv 32 := 0xff010113.
Lemma F_a2fcc : fetch_word Ubsan.M.loaded_segments (0xa3018 : word) = Some W_a2fcc.
Proof. vm_refl. Qed.
Lemma D_a2fcc : decode_any W_a2fcc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2fd0 : bv 32 := 0x00113423.
Lemma F_a2fd0 : fetch_word Ubsan.M.loaded_segments (0xa301c : word) = Some W_a2fd0.
Proof. vm_refl. Qed.
Lemma D_a2fd0 : decode_any W_a2fd0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2fd4 : bv 32 := 0x00813023.
Lemma F_a2fd4 : fetch_word Ubsan.M.loaded_segments (0xa3020 : word) = Some W_a2fd4.
Proof. vm_refl. Qed.
Lemma D_a2fd4 : decode_any W_a2fd4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2fd8 : bv 32 := 0x41c000ef.
Lemma F_a2fd8 : fetch_word Ubsan.M.loaded_segments (0xa3024 : word) = Some W_a2fd8.
Proof. vm_refl. Qed.
Lemma D_a2fd8 : decode_any W_a2fd8 = Some (Jal 1 1052, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2fdc : bv 32 := 0x00053403.
Lemma F_a2fdc : fetch_word Ubsan.M.loaded_segments (0xa3028 : word) = Some W_a2fdc.
Proof. vm_refl. Qed.
Lemma D_a2fdc : decode_any W_a2fdc = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2fe0 : bv 32 := 0x12041663.
Lemma F_a2fe0 : fetch_word Ubsan.M.loaded_segments (0xa302c : word) = Some W_a2fe0.
Proof. vm_refl. Qed.
Lemma D_a2fe0 : decode_any W_a2fe0 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2fe4 : bv 32 := 0x0004a517.
Lemma F_a2fe4 : fetch_word Ubsan.M.loaded_segments (0xa3030 : word) = Some W_a2fe4.
Proof. vm_refl. Qed.
Lemma D_a2fe4 : decode_any W_a2fe4 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2fe8 : bv 32 := 0x35853403.
Lemma F_a2fe8 : fetch_word Ubsan.M.loaded_segments (0xa3034 : word) = Some W_a2fe8.
Proof. vm_refl. Qed.
Lemma D_a2fe8 : decode_any W_a2fe8 = Some (Load SZ8 true 8 10 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_a2fec : bv 32 := 0x04040a63.
Lemma F_a2fec : fetch_word Ubsan.M.loaded_segments (0xa3038 : word) = Some W_a2fec.
Proof. vm_refl. Qed.
Lemma D_a2fec : decode_any W_a2fec = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3040 : bv 32 := 0x00018517.
Lemma F_a3040 : fetch_word Ubsan.M.loaded_segments (0xa308c : word) = Some W_a3040.
Proof. vm_refl. Qed.
Lemma D_a3040 : decode_any W_a3040 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3044 : bv 32 := 0x08453403.
Lemma F_a3044 : fetch_word Ubsan.M.loaded_segments (0xa3090 : word) = Some W_a3044.
Proof. vm_refl. Qed.
Lemma D_a3044 : decode_any W_a3044 = Some (Load SZ8 true 8 10 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3048 : bv 32 := 0x04040a63.
Lemma F_a3048 : fetch_word Ubsan.M.loaded_segments (0xa3094 : word) = Some W_a3048.
Proof. vm_refl. Qed.
Lemma D_a3048 : decode_any W_a3048 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_a304c : bv 32 := 0x08c42503.
Lemma F_a304c : fetch_word Ubsan.M.loaded_segments (0xa3098 : word) = Some W_a304c.
Proof. vm_refl. Qed.
Lemma D_a304c : decode_any W_a304c = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3050 : bv 32 := 0x00054663.
Lemma F_a3050 : fetch_word Ubsan.M.loaded_segments (0xa309c : word) = Some W_a3050.
Proof. vm_refl. Qed.
Lemma D_a3050 : decode_any W_a3050 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a305c : bv 32 := 0x02843503.
Lemma F_a305c : fetch_word Ubsan.M.loaded_segments (0xa30a8 : word) = Some W_a305c.
Proof. vm_refl. Qed.
Lemma D_a305c : decode_any W_a305c = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3060 : bv 32 := 0x03843583.
Lemma F_a3060 : fetch_word Ubsan.M.loaded_segments (0xa30ac : word) = Some W_a3060.
Proof. vm_refl. Qed.
Lemma D_a3060 : decode_any W_a3060 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3064 : bv 32 := 0x00b50c63.
Lemma F_a3064 : fetch_word Ubsan.M.loaded_segments (0xa30b0 : word) = Some W_a3064.
Proof. vm_refl. Qed.
Lemma D_a3064 : decode_any W_a3064 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3068 : bv 32 := 0x04843683.
Lemma F_a3068 : fetch_word Ubsan.M.loaded_segments (0xa30b4 : word) = Some W_a3068.
Proof. vm_refl. Qed.
Lemma D_a3068 : decode_any W_a3068 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a306c : bv 32 := 0x00040513.
Lemma F_a306c : fetch_word Ubsan.M.loaded_segments (0xa30b8 : word) = Some W_a306c.
Proof. vm_refl. Qed.
Lemma D_a306c : decode_any W_a306c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3070 : bv 32 := 0x00000593.
Lemma F_a3070 : fetch_word Ubsan.M.loaded_segments (0xa30bc : word) = Some W_a3070.
Proof. vm_refl. Qed.
Lemma D_a3070 : decode_any W_a3070 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3074 : bv 32 := 0x00000613.
Lemma F_a3074 : fetch_word Ubsan.M.loaded_segments (0xa30c0 : word) = Some W_a3074.
Proof. vm_refl. Qed.
Lemma D_a3074 : decode_any W_a3074 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3078 : bv 32 := 0x000680e7.
Lemma F_a3078 : fetch_word Ubsan.M.loaded_segments (0xa30c4 : word) = Some W_a3078.
Proof. vm_refl. Qed.
Lemma D_a3078 : decode_any W_a3078 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a307c : bv 32 := 0x00843503.
Lemma F_a307c : fetch_word Ubsan.M.loaded_segments (0xa30c8 : word) = Some W_a307c.
Proof. vm_refl. Qed.
Lemma D_a307c : decode_any W_a307c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3080 : bv 32 := 0x01043583.
Lemma F_a3080 : fetch_word Ubsan.M.loaded_segments (0xa30cc : word) = Some W_a3080.
Proof. vm_refl. Qed.
Lemma D_a3080 : decode_any W_a3080 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3084 : bv 32 := 0x00b50c63.
Lemma F_a3084 : fetch_word Ubsan.M.loaded_segments (0xa30d0 : word) = Some W_a3084.
Proof. vm_refl. Qed.
Lemma D_a3084 : decode_any W_a3084 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a309c : bv 32 := 0x00018517.
Lemma F_a309c : fetch_word Ubsan.M.loaded_segments (0xa30e8 : word) = Some W_a309c.
Proof. vm_refl. Qed.
Lemma D_a309c : decode_any W_a309c = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a30a0 : bv 32 := 0xf3853403.
Lemma F_a30a0 : fetch_word Ubsan.M.loaded_segments (0xa30ec : word) = Some W_a30a0.
Proof. vm_refl. Qed.
Lemma D_a30a0 : decode_any W_a30a0 = Some (Load SZ8 true 8 10 3896, 4%Z).
Proof. vm_refl. Qed.

Definition W_a30a4 : bv 32 := 0x0a040e63.
Lemma F_a30a4 : fetch_word Ubsan.M.loaded_segments (0xa30f0 : word) = Some W_a30a4.
Proof. vm_refl. Qed.
Lemma D_a30a4 : decode_any W_a30a4 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_a30a8 : bv 32 := 0x08c42503.
Lemma F_a30a8 : fetch_word Ubsan.M.loaded_segments (0xa30f4 : word) = Some W_a30a8.
Proof. vm_refl. Qed.
Lemma D_a30a8 : decode_any W_a30a8 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_a30ac : bv 32 := 0x00054663.
Lemma F_a30ac : fetch_word Ubsan.M.loaded_segments (0xa30f8 : word) = Some W_a30ac.
Proof. vm_refl. Qed.
Lemma D_a30ac : decode_any W_a30ac = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a30b8 : bv 32 := 0x02843503.
Lemma F_a30b8 : fetch_word Ubsan.M.loaded_segments (0xa3104 : word) = Some W_a30b8.
Proof. vm_refl. Qed.
Lemma D_a30b8 : decode_any W_a30b8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a30bc : bv 32 := 0x03843583.
Lemma F_a30bc : fetch_word Ubsan.M.loaded_segments (0xa3108 : word) = Some W_a30bc.
Proof. vm_refl. Qed.
Lemma D_a30bc : decode_any W_a30bc = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a30c0 : bv 32 := 0x00b50c63.
Lemma F_a30c0 : fetch_word Ubsan.M.loaded_segments (0xa310c : word) = Some W_a30c0.
Proof. vm_refl. Qed.
Lemma D_a30c0 : decode_any W_a30c0 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a30d8 : bv 32 := 0x00843503.
Lemma F_a30d8 : fetch_word Ubsan.M.loaded_segments (0xa3124 : word) = Some W_a30d8.
Proof. vm_refl. Qed.
Lemma D_a30d8 : decode_any W_a30d8 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a30dc : bv 32 := 0x01043583.
Lemma F_a30dc : fetch_word Ubsan.M.loaded_segments (0xa3128 : word) = Some W_a30dc.
Proof. vm_refl. Qed.
Lemma D_a30dc : decode_any W_a30dc = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a30e0 : bv 32 := 0x08b50063.
Lemma F_a30e0 : fetch_word Ubsan.M.loaded_segments (0xa312c : word) = Some W_a30e0.
Proof. vm_refl. Qed.
Lemma D_a30e0 : decode_any W_a30e0 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3160 : bv 32 := 0x00813083.
Lemma F_a3160 : fetch_word Ubsan.M.loaded_segments (0xa31ac : word) = Some W_a3160.
Proof. vm_refl. Qed.
Lemma D_a3160 : decode_any W_a3160 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3164 : bv 32 := 0x00013403.
Lemma F_a3164 : fetch_word Ubsan.M.loaded_segments (0xa31b0 : word) = Some W_a3164.
Proof. vm_refl. Qed.
Lemma D_a3164 : decode_any W_a3164 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3168 : bv 32 := 0x01010113.
Lemma F_a3168 : fetch_word Ubsan.M.loaded_segments (0xa31b4 : word) = Some W_a3168.
Proof. vm_refl. Qed.
Lemma D_a3168 : decode_any W_a3168 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a316c : bv 32 := 0x00008067.
Lemma F_a316c : fetch_word Ubsan.M.loaded_segments (0xa31b8 : word) = Some W_a316c.
Proof. vm_refl. Qed.
Lemma D_a316c : decode_any W_a316c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a33f4 : bv 32 := 0xff010113.
Lemma F_a33f4 : fetch_word Ubsan.M.loaded_segments (0xa3440 : word) = Some W_a33f4.
Proof. vm_refl. Qed.
Lemma D_a33f4 : decode_any W_a33f4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a33f8 : bv 32 := 0x00113423.
Lemma F_a33f8 : fetch_word Ubsan.M.loaded_segments (0xa3444 : word) = Some W_a33f8.
Proof. vm_refl. Qed.
Lemma D_a33f8 : decode_any W_a33f8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a33fc : bv 32 := 0x00813023.
Lemma F_a33fc : fetch_word Ubsan.M.loaded_segments (0xa3448 : word) = Some W_a33fc.
Proof. vm_refl. Qed.
Lemma D_a33fc : decode_any W_a33fc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3400 : bv 32 := 0x0004a517.
Lemma F_a3400 : fetch_word Ubsan.M.loaded_segments (0xa344c : word) = Some W_a3400.
Proof. vm_refl. Qed.
Lemma D_a3400 : decode_any W_a3400 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3404 : bv 32 := 0xf4450413.
Lemma F_a3404 : fetch_word Ubsan.M.loaded_segments (0xa3450 : word) = Some W_a3404.
Proof. vm_refl. Qed.
Lemma D_a3404 : decode_any W_a3404 = Some (OpImm ALU_ADD 8 10 3908, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3408 : bv 32 := 0x00040513.
Lemma F_a3408 : fetch_word Ubsan.M.loaded_segments (0xa3454 : word) = Some W_a3408.
Proof. vm_refl. Qed.
Lemma D_a3408 : decode_any W_a3408 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a340c : bv 32 := 0x0410b0ef.
Lemma F_a340c : fetch_word Ubsan.M.loaded_segments (0xa3458 : word) = Some W_a340c.
Proof. vm_refl. Qed.
Lemma D_a340c : decode_any W_a340c = Some (Jal 1 47168, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3410 : bv 32 := 0x00840513.
Lemma F_a3410 : fetch_word Ubsan.M.loaded_segments (0xa345c : word) = Some W_a3410.
Proof. vm_refl. Qed.
Lemma D_a3410 : decode_any W_a3410 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3414 : bv 32 := 0x00813083.
Lemma F_a3414 : fetch_word Ubsan.M.loaded_segments (0xa3460 : word) = Some W_a3414.
Proof. vm_refl. Qed.
Lemma D_a3414 : decode_any W_a3414 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3418 : bv 32 := 0x00013403.
Lemma F_a3418 : fetch_word Ubsan.M.loaded_segments (0xa3464 : word) = Some W_a3418.
Proof. vm_refl. Qed.
Lemma D_a3418 : decode_any W_a3418 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a341c : bv 32 := 0x01010113.
Lemma F_a341c : fetch_word Ubsan.M.loaded_segments (0xa3468 : word) = Some W_a341c.
Proof. vm_refl. Qed.
Lemma D_a341c : decode_any W_a341c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a3420 : bv 32 := 0x00008067.
Lemma F_a3420 : fetch_word Ubsan.M.loaded_segments (0xa346c : word) = Some W_a3420.
Proof. vm_refl. Qed.
Lemma D_a3420 : decode_any W_a3420 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
