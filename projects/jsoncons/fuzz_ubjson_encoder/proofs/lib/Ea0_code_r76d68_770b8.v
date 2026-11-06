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

Definition W_91948 : bv 32 := 0xf7010113.
Lemma F_91948 : fetch_word Asan.M.loaded_segments (0x91998 : word) = Some W_91948.
Proof. vm_refl. Qed.
Lemma D_91948 : decode_any W_91948 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_9194c : bv 32 := 0x08113423.
Lemma F_9194c : fetch_word Asan.M.loaded_segments (0x9199c : word) = Some W_9194c.
Proof. vm_refl. Qed.
Lemma D_9194c : decode_any W_9194c = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_91950 : bv 32 := 0x08813023.
Lemma F_91950 : fetch_word Asan.M.loaded_segments (0x919a0 : word) = Some W_91950.
Proof. vm_refl. Qed.
Lemma D_91950 : decode_any W_91950 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_91954 : bv 32 := 0x06913c23.
Lemma F_91954 : fetch_word Asan.M.loaded_segments (0x919a4 : word) = Some W_91954.
Proof. vm_refl. Qed.
Lemma D_91954 : decode_any W_91954 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_91958 : bv 32 := 0x07213823.
Lemma F_91958 : fetch_word Asan.M.loaded_segments (0x919a8 : word) = Some W_91958.
Proof. vm_refl. Qed.
Lemma D_91958 : decode_any W_91958 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_9195c : bv 32 := 0x07313423.
Lemma F_9195c : fetch_word Asan.M.loaded_segments (0x919ac : word) = Some W_9195c.
Proof. vm_refl. Qed.
Lemma D_9195c : decode_any W_9195c = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_91960 : bv 32 := 0x07413023.
Lemma F_91960 : fetch_word Asan.M.loaded_segments (0x919b0 : word) = Some W_91960.
Proof. vm_refl. Qed.
Lemma D_91960 : decode_any W_91960 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_91964 : bv 32 := 0x05513c23.
Lemma F_91964 : fetch_word Asan.M.loaded_segments (0x919b4 : word) = Some W_91964.
Proof. vm_refl. Qed.
Lemma D_91964 : decode_any W_91964 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_91968 : bv 32 := 0x05613823.
Lemma F_91968 : fetch_word Asan.M.loaded_segments (0x919b8 : word) = Some W_91968.
Proof. vm_refl. Qed.
Lemma D_91968 : decode_any W_91968 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9196c : bv 32 := 0x05713423.
Lemma F_9196c : fetch_word Asan.M.loaded_segments (0x919bc : word) = Some W_9196c.
Proof. vm_refl. Qed.
Lemma D_9196c : decode_any W_9196c = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_91970 : bv 32 := 0x05813023.
Lemma F_91970 : fetch_word Asan.M.loaded_segments (0x919c0 : word) = Some W_91970.
Proof. vm_refl. Qed.
Lemma D_91970 : decode_any W_91970 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_91974 : bv 32 := 0x03913c23.
Lemma F_91974 : fetch_word Asan.M.loaded_segments (0x919c4 : word) = Some W_91974.
Proof. vm_refl. Qed.
Lemma D_91974 : decode_any W_91974 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_91978 : bv 32 := 0x03a13823.
Lemma F_91978 : fetch_word Asan.M.loaded_segments (0x919c8 : word) = Some W_91978.
Proof. vm_refl. Qed.
Lemma D_91978 : decode_any W_91978 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9197c : bv 32 := 0x03b13423.
Lemma F_9197c : fetch_word Asan.M.loaded_segments (0x919cc : word) = Some W_9197c.
Proof. vm_refl. Qed.
Lemma D_9197c : decode_any W_9197c = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_91980 : bv 32 := 0x00058913.
Lemma F_91980 : fetch_word Asan.M.loaded_segments (0x919d0 : word) = Some W_91980.
Proof. vm_refl. Qed.
Lemma D_91980 : decode_any W_91980 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_91984 : bv 32 := 0x000a7597.
Lemma F_91984 : fetch_word Asan.M.loaded_segments (0x919d4 : word) = Some W_91984.
Proof. vm_refl. Qed.
Lemma D_91984 : decode_any W_91984 = Some (Auipc 11 167, 4%Z).
Proof. vm_refl. Qed.

Definition W_91988 : bv 32 := 0x7d45b583.
Lemma F_91988 : fetch_word Asan.M.loaded_segments (0x919d8 : word) = Some W_91988.
Proof. vm_refl. Qed.
Lemma D_91988 : decode_any W_91988 = Some (Load SZ8 true 11 11 2004, 4%Z).
Proof. vm_refl. Qed.

Definition W_9198c : bv 32 := 0x0895c583.
Lemma F_9198c : fetch_word Asan.M.loaded_segments (0x919dc : word) = Some W_9198c.
Proof. vm_refl. Qed.
Lemma D_9198c : decode_any W_9198c = Some (Load SZ1 false 11 11 137, 4%Z).
Proof. vm_refl. Qed.

Definition W_91990 : bv 32 := 0x18058a63.
Lemma F_91990 : fetch_word Asan.M.loaded_segments (0x919e0 : word) = Some W_91990.
Proof. vm_refl. Qed.
Lemma D_91990 : decode_any W_91990 = Some (Branch BC_EQ 11 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_91994 : bv 32 := 0x00050993.
Lemma F_91994 : fetch_word Asan.M.loaded_segments (0x919e4 : word) = Some W_91994.
Proof. vm_refl. Qed.
Lemma D_91994 : decode_any W_91994 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_91998 : bv 32 := 0x000a8517.
Lemma F_91998 : fetch_word Asan.M.loaded_segments (0x919e8 : word) = Some W_91998.
Proof. vm_refl. Qed.
Lemma D_91998 : decode_any W_91998 = Some (Auipc 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_9199c : bv 32 := 0x82053d03.
Lemma F_9199c : fetch_word Asan.M.loaded_segments (0x919ec : word) = Some W_9199c.
Proof. vm_refl. Qed.
Lemma D_9199c : decode_any W_9199c = Some (Load SZ8 true 26 10 2080, 4%Z).
Proof. vm_refl. Qed.

Definition W_919a0 : bv 32 := 0x0009ba03.
Lemma F_919a0 : fetch_word Asan.M.loaded_segments (0x919f0 : word) = Some W_919a0.
Proof. vm_refl. Qed.
Lemma D_919a0 : decode_any W_919a0 = Some (Load SZ8 true 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_919a4 : bv 32 := 0x000a8517.
Lemma F_919a4 : fetch_word Asan.M.loaded_segments (0x919f4 : word) = Some W_919a4.
Proof. vm_refl. Qed.
Lemma D_919a4 : decode_any W_919a4 = Some (Auipc 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_919a8 : bv 32 := 0x000d2583.
Lemma F_919a8 : fetch_word Asan.M.loaded_segments (0x919f8 : word) = Some W_919a8.
Proof. vm_refl. Qed.
Lemma D_919a8 : decode_any W_919a8 = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_919ac : bv 32 := 0x5cc53a83.
Lemma F_919ac : fetch_word Asan.M.loaded_segments (0x919fc : word) = Some W_919ac.
Proof. vm_refl. Qed.
Lemma D_919ac : decode_any W_919ac = Some (Load SZ8 true 21 10 1484, 4%Z).
Proof. vm_refl. Qed.

Definition W_919b0 : bv 32 := 0x00300513.
Lemma F_919b0 : fetch_word Asan.M.loaded_segments (0x91a00 : word) = Some W_919b0.
Proof. vm_refl. Qed.
Lemma D_919b0 : decode_any W_919b0 = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_919b4 : bv 32 := 0x004a8ab3.
Lemma F_919b4 : fetch_word Asan.M.loaded_segments (0x91a04 : word) = Some W_919b4.
Proof. vm_refl. Qed.
Lemma D_919b4 : decode_any W_919b4 = Some (Op ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_919b8 : bv 32 := 0x1ea5fa63.
Lemma F_919b8 : fetch_word Asan.M.loaded_segments (0x91a08 : word) = Some W_919b8.
Proof. vm_refl. Qed.
Lemma D_919b8 : decode_any W_919b8 = Some (Branch BC_GEU 11 10 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_919bc : bv 32 := 0x000abb03.
Lemma F_919bc : fetch_word Asan.M.loaded_segments (0x91a0c : word) = Some W_919bc.
Proof. vm_refl. Qed.
Lemma D_919bc : decode_any W_919bc = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_919c0 : bv 32 := 0xfff00513.
Lemma F_919c0 : fetch_word Asan.M.loaded_segments (0x91a10 : word) = Some W_919c0.
Proof. vm_refl. Qed.
Lemma D_919c0 : decode_any W_919c0 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_919c4 : bv 32 := 0x0230000f.
Lemma F_919c4 : fetch_word Asan.M.loaded_segments (0x91a14 : word) = Some W_919c4.
Proof. vm_refl. Qed.
Lemma D_919c4 : decode_any W_919c4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_919c8 : bv 32 := 0x14ab0e63.
Lemma F_919c8 : fetch_word Asan.M.loaded_segments (0x91a18 : word) = Some W_919c8.
Proof. vm_refl. Qed.
Lemma D_919c8 : decode_any W_919c8 = Some (Branch BC_EQ 22 10 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_919cc : bv 32 := 0x080b1263.
Lemma F_919cc : fetch_word Asan.M.loaded_segments (0x91a1c : word) = Some W_919cc.
Proof. vm_refl. Qed.
Lemma D_919cc : decode_any W_919cc = Some (Branch BC_NE 22 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_91a50 : bv 32 := 0x0c0b0a63.
Lemma F_91a50 : fetch_word Asan.M.loaded_segments (0x91aa0 : word) = Some W_91a50.
Proof. vm_refl. Qed.
Lemma D_91a50 : decode_any W_91a50 = Some (Branch BC_EQ 22 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_91a54 : bv 32 := 0x00c13823.
Lemma F_91a54 : fetch_word Asan.M.loaded_segments (0x91aa4 : word) = Some W_91a54.
Proof. vm_refl. Qed.
Lemma D_91a54 : decode_any W_91a54 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_91a58 : bv 32 := 0x00d13c23.
Lemma F_91a58 : fetch_word Asan.M.loaded_segments (0x91aa8 : word) = Some W_91a58.
Proof. vm_refl. Qed.
Lemma D_91a58 : decode_any W_91a58 = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_91a5c : bv 32 := 0x0ff00513.
Lemma F_91a5c : fetch_word Asan.M.loaded_segments (0x91aac : word) = Some W_91a5c.
Proof. vm_refl. Qed.
Lemma D_91a5c : decode_any W_91a5c = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_91a60 : bv 32 := 0x0aaa6863.
Lemma F_91a60 : fetch_word Asan.M.loaded_segments (0x91ab0 : word) = Some W_91a60.
Proof. vm_refl. Qed.
Lemma D_91a60 : decode_any W_91a60 = Some (Branch BC_LTU 20 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b10 : bv 32 := 0x000b0513.
Lemma F_91b10 : fetch_word Asan.M.loaded_segments (0x91b60 : word) = Some W_91b10.
Proof. vm_refl. Qed.
Lemma D_91b10 : decode_any W_91b10 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b14 : bv 32 := 0x004a1413.
Lemma F_91b14 : fetch_word Asan.M.loaded_segments (0x91b64 : word) = Some W_91b14.
Proof. vm_refl. Qed.
Lemma D_91b14 : decode_any W_91b14 = Some (ShiftImm ALU_SLL 8 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b18 : bv 32 := 0x00850433.
Lemma F_91b18 : fetch_word Asan.M.loaded_segments (0x91b68 : word) = Some W_91b18.
Proof. vm_refl. Qed.
Lemma D_91b18 : decode_any W_91b18 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b1c : bv 32 := 0x00843503.
Lemma F_91b1c : fetch_word Asan.M.loaded_segments (0x91b6c : word) = Some W_91b1c.
Proof. vm_refl. Qed.
Lemma D_91b1c : decode_any W_91b1c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b20 : bv 32 := 0x04050263.
Lemma F_91b20 : fetch_word Asan.M.loaded_segments (0x91b70 : word) = Some W_91b20.
Proof. vm_refl. Qed.
Lemma D_91b20 : decode_any W_91b20 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b24 : bv 32 := 0x00000513.
Lemma F_91b24 : fetch_word Asan.M.loaded_segments (0x91b74 : word) = Some W_91b24.
Proof. vm_refl. Qed.
Lemma D_91b24 : decode_any W_91b24 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b28 : bv 32 := 0x08813083.
Lemma F_91b28 : fetch_word Asan.M.loaded_segments (0x91b78 : word) = Some W_91b28.
Proof. vm_refl. Qed.
Lemma D_91b28 : decode_any W_91b28 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b2c : bv 32 := 0x08013403.
Lemma F_91b2c : fetch_word Asan.M.loaded_segments (0x91b7c : word) = Some W_91b2c.
Proof. vm_refl. Qed.
Lemma D_91b2c : decode_any W_91b2c = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b30 : bv 32 := 0x07813483.
Lemma F_91b30 : fetch_word Asan.M.loaded_segments (0x91b80 : word) = Some W_91b30.
Proof. vm_refl. Qed.
Lemma D_91b30 : decode_any W_91b30 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b34 : bv 32 := 0x07013903.
Lemma F_91b34 : fetch_word Asan.M.loaded_segments (0x91b84 : word) = Some W_91b34.
Proof. vm_refl. Qed.
Lemma D_91b34 : decode_any W_91b34 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b38 : bv 32 := 0x06813983.
Lemma F_91b38 : fetch_word Asan.M.loaded_segments (0x91b88 : word) = Some W_91b38.
Proof. vm_refl. Qed.
Lemma D_91b38 : decode_any W_91b38 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b3c : bv 32 := 0x06013a03.
Lemma F_91b3c : fetch_word Asan.M.loaded_segments (0x91b8c : word) = Some W_91b3c.
Proof. vm_refl. Qed.
Lemma D_91b3c : decode_any W_91b3c = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b40 : bv 32 := 0x05813a83.
Lemma F_91b40 : fetch_word Asan.M.loaded_segments (0x91b90 : word) = Some W_91b40.
Proof. vm_refl. Qed.
Lemma D_91b40 : decode_any W_91b40 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b44 : bv 32 := 0x05013b03.
Lemma F_91b44 : fetch_word Asan.M.loaded_segments (0x91b94 : word) = Some W_91b44.
Proof. vm_refl. Qed.
Lemma D_91b44 : decode_any W_91b44 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b48 : bv 32 := 0x04813b83.
Lemma F_91b48 : fetch_word Asan.M.loaded_segments (0x91b98 : word) = Some W_91b48.
Proof. vm_refl. Qed.
Lemma D_91b48 : decode_any W_91b48 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b4c : bv 32 := 0x04013c03.
Lemma F_91b4c : fetch_word Asan.M.loaded_segments (0x91b9c : word) = Some W_91b4c.
Proof. vm_refl. Qed.
Lemma D_91b4c : decode_any W_91b4c = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b50 : bv 32 := 0x03813c83.
Lemma F_91b50 : fetch_word Asan.M.loaded_segments (0x91ba0 : word) = Some W_91b50.
Proof. vm_refl. Qed.
Lemma D_91b50 : decode_any W_91b50 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b54 : bv 32 := 0x03013d03.
Lemma F_91b54 : fetch_word Asan.M.loaded_segments (0x91ba4 : word) = Some W_91b54.
Proof. vm_refl. Qed.
Lemma D_91b54 : decode_any W_91b54 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b58 : bv 32 := 0x02813d83.
Lemma F_91b58 : fetch_word Asan.M.loaded_segments (0x91ba8 : word) = Some W_91b58.
Proof. vm_refl. Qed.
Lemma D_91b58 : decode_any W_91b58 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b5c : bv 32 := 0x09010113.
Lemma F_91b5c : fetch_word Asan.M.loaded_segments (0x91bac : word) = Some W_91b5c.
Proof. vm_refl. Qed.
Lemma D_91b5c : decode_any W_91b5c = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_91b60 : bv 32 := 0x00008067.
Lemma F_91b60 : fetch_word Asan.M.loaded_segments (0x91bb0 : word) = Some W_91b60.
Proof. vm_refl. Qed.
Lemma D_91b60 : decode_any W_91b60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
