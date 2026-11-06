(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c39c0 : bv 32 := 0xf9010113.
Lemma F_c39c0 : fetch_word AsanUbsan.M.loaded_segments (0xc39c0 : word) = Some W_c39c0.
Proof. vm_refl. Qed.
Lemma D_c39c0 : decode_any W_c39c0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39c4 : bv 32 := 0x06113423.
Lemma F_c39c4 : fetch_word AsanUbsan.M.loaded_segments (0xc39c4 : word) = Some W_c39c4.
Proof. vm_refl. Qed.
Lemma D_c39c4 : decode_any W_c39c4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39c8 : bv 32 := 0x06813023.
Lemma F_c39c8 : fetch_word AsanUbsan.M.loaded_segments (0xc39c8 : word) = Some W_c39c8.
Proof. vm_refl. Qed.
Lemma D_c39c8 : decode_any W_c39c8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39cc : bv 32 := 0x04913c23.
Lemma F_c39cc : fetch_word AsanUbsan.M.loaded_segments (0xc39cc : word) = Some W_c39cc.
Proof. vm_refl. Qed.
Lemma D_c39cc : decode_any W_c39cc = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39d0 : bv 32 := 0x05213823.
Lemma F_c39d0 : fetch_word AsanUbsan.M.loaded_segments (0xc39d0 : word) = Some W_c39d0.
Proof. vm_refl. Qed.
Lemma D_c39d0 : decode_any W_c39d0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39d4 : bv 32 := 0x05313423.
Lemma F_c39d4 : fetch_word AsanUbsan.M.loaded_segments (0xc39d4 : word) = Some W_c39d4.
Proof. vm_refl. Qed.
Lemma D_c39d4 : decode_any W_c39d4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39d8 : bv 32 := 0x05413023.
Lemma F_c39d8 : fetch_word AsanUbsan.M.loaded_segments (0xc39d8 : word) = Some W_c39d8.
Proof. vm_refl. Qed.
Lemma D_c39d8 : decode_any W_c39d8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39dc : bv 32 := 0x03513c23.
Lemma F_c39dc : fetch_word AsanUbsan.M.loaded_segments (0xc39dc : word) = Some W_c39dc.
Proof. vm_refl. Qed.
Lemma D_c39dc : decode_any W_c39dc = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39e0 : bv 32 := 0x03613823.
Lemma F_c39e0 : fetch_word AsanUbsan.M.loaded_segments (0xc39e0 : word) = Some W_c39e0.
Proof. vm_refl. Qed.
Lemma D_c39e0 : decode_any W_c39e0 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39e4 : bv 32 := 0x00060413.
Lemma F_c39e4 : fetch_word AsanUbsan.M.loaded_segments (0xc39e4 : word) = Some W_c39e4.
Proof. vm_refl. Qed.
Lemma D_c39e4 : decode_any W_c39e4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39e8 : bv 32 := 0x00050493.
Lemma F_c39e8 : fetch_word AsanUbsan.M.loaded_segments (0xc39e8 : word) = Some W_c39e8.
Proof. vm_refl. Qed.
Lemma D_c39e8 : decode_any W_c39e8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39ec : bv 32 := 0x00014517.
Lemma F_c39ec : fetch_word AsanUbsan.M.loaded_segments (0xc39ec : word) = Some W_c39ec.
Proof. vm_refl. Qed.
Lemma D_c39ec : decode_any W_c39ec = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39f0 : bv 32 := 0x83c53a83.
Lemma F_c39f0 : fetch_word AsanUbsan.M.loaded_segments (0xc39f0 : word) = Some W_c39f0.
Proof. vm_refl. Qed.
Lemma D_c39f0 : decode_any W_c39f0 = Some (Load SZ8 true 21 10 2108, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39f4 : bv 32 := 0x000ab503.
Lemma F_c39f4 : fetch_word AsanUbsan.M.loaded_segments (0xc39f4 : word) = Some W_c39f4.
Proof. vm_refl. Qed.
Lemma D_c39f4 : decode_any W_c39f4 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39f8 : bv 32 := 0x02a13423.
Lemma F_c39f8 : fetch_word AsanUbsan.M.loaded_segments (0xc39f8 : word) = Some W_c39f8.
Proof. vm_refl. Qed.
Lemma D_c39f8 : decode_any W_c39f8 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_c39fc : bv 32 := 0x0284b503.
Lemma F_c39fc : fetch_word AsanUbsan.M.loaded_segments (0xc39fc : word) = Some W_c39fc.
Proof. vm_refl. Qed.
Lemma D_c39fc : decode_any W_c39fc = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a00 : bv 32 := 0x0384b603.
Lemma F_c3a00 : fetch_word AsanUbsan.M.loaded_segments (0xc3a00 : word) = Some W_c3a00.
Proof. vm_refl. Qed.
Lemma D_c3a00 : decode_any W_c3a00 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a04 : bv 32 := 0x40c50b33.
Lemma F_c3a04 : fetch_word AsanUbsan.M.loaded_segments (0xc3a04 : word) = Some W_c3a04.
Proof. vm_refl. Qed.
Lemma D_c3a04 : decode_any W_c3a04 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a08 : bv 32 := 0x00c546b3.
Lemma F_c3a08 : fetch_word AsanUbsan.M.loaded_segments (0xc3a08 : word) = Some W_c3a08.
Proof. vm_refl. Qed.
Lemma D_c3a08 : decode_any W_c3a08 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a0c : bv 32 := 0x00c13423.
Lemma F_c3a0c : fetch_word AsanUbsan.M.loaded_segments (0xc3a0c : word) = Some W_c3a0c.
Proof. vm_refl. Qed.
Lemma D_c3a0c : decode_any W_c3a0c = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a10 : bv 32 := 0x01613823.
Lemma F_c3a10 : fetch_word AsanUbsan.M.loaded_segments (0xc3a10 : word) = Some W_c3a10.
Proof. vm_refl. Qed.
Lemma D_c3a10 : decode_any W_c3a10 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a14 : bv 32 := 0x00b13c23.
Lemma F_c3a14 : fetch_word AsanUbsan.M.loaded_segments (0xc3a14 : word) = Some W_c3a14.
Proof. vm_refl. Qed.
Lemma D_c3a14 : decode_any W_c3a14 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a18 : bv 32 := 0x02813023.
Lemma F_c3a18 : fetch_word AsanUbsan.M.loaded_segments (0xc3a18 : word) = Some W_c3a18.
Proof. vm_refl. Qed.
Lemma D_c3a18 : decode_any W_c3a18 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a1c : bv 32 := 0x008b0b33.
Lemma F_c3a1c : fetch_word AsanUbsan.M.loaded_segments (0xc3a1c : word) = Some W_c3a1c.
Proof. vm_refl. Qed.
Lemma D_c3a1c : decode_any W_c3a1c = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a20 : bv 32 := 0x00d03933.
Lemma F_c3a20 : fetch_word AsanUbsan.M.loaded_segments (0xc3a20 : word) = Some W_c3a20.
Proof. vm_refl. Qed.
Lemma D_c3a20 : decode_any W_c3a20 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a24 : bv 32 := 0x00c50663.
Lemma F_c3a24 : fetch_word AsanUbsan.M.loaded_segments (0xc3a24 : word) = Some W_c3a24.
Proof. vm_refl. Qed.
Lemma D_c3a24 : decode_any W_c3a24 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a28 : bv 32 := 0x00810993.
Lemma F_c3a28 : fetch_word AsanUbsan.M.loaded_segments (0xc3a28 : word) = Some W_c3a28.
Proof. vm_refl. Qed.
Lemma D_c3a28 : decode_any W_c3a28 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a2c : bv 32 := 0x0080006f.
Lemma F_c3a2c : fetch_word AsanUbsan.M.loaded_segments (0xc3a2c : word) = Some W_c3a2c.
Proof. vm_refl. Qed.
Lemma D_c3a2c : decode_any W_c3a2c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a30 : bv 32 := 0x01810993.
Lemma F_c3a30 : fetch_word AsanUbsan.M.loaded_segments (0xc3a30 : word) = Some W_c3a30.
Proof. vm_refl. Qed.
Lemma D_c3a30 : decode_any W_c3a30 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a34 : bv 32 := 0x0784a503.
Lemma F_c3a34 : fetch_word AsanUbsan.M.loaded_segments (0xc3a34 : word) = Some W_c3a34.
Proof. vm_refl. Qed.
Lemma D_c3a34 : decode_any W_c3a34 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a38 : bv 32 := 0x00190913.
Lemma F_c3a38 : fetch_word AsanUbsan.M.loaded_segments (0xc3a38 : word) = Some W_c3a38.
Proof. vm_refl. Qed.
Lemma D_c3a38 : decode_any W_c3a38 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a3c : bv 32 := 0x04200893.
Lemma F_c3a3c : fetch_word AsanUbsan.M.loaded_segments (0xc3a3c : word) = Some W_c3a3c.
Proof. vm_refl. Qed.
Lemma D_c3a3c : decode_any W_c3a3c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a40 : bv 32 := 0x00098593.
Lemma F_c3a40 : fetch_word AsanUbsan.M.loaded_segments (0xc3a40 : word) = Some W_c3a40.
Proof. vm_refl. Qed.
Lemma D_c3a40 : decode_any W_c3a40 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a44 : bv 32 := 0x00090613.
Lemma F_c3a44 : fetch_word AsanUbsan.M.loaded_segments (0xc3a44 : word) = Some W_c3a44.
Proof. vm_refl. Qed.
Lemma D_c3a44 : decode_any W_c3a44 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a48 : bv 32 := 0x00000073.
Lemma F_c3a48 : fetch_word AsanUbsan.M.loaded_segments (0xc3a48 : word) = Some W_c3a48.
Proof. vm_refl. Qed.
Lemma D_c3a48 : decode_any W_c3a48 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_c3a48 : is_ecall W_c3a48 = true.
Proof. reflexivity. Qed.

Definition W_c3a4c : bv 32 := 0x985fa0ef.
Lemma F_c3a4c : fetch_word AsanUbsan.M.loaded_segments (0xc3a4c : word) = Some W_c3a4c.
Proof. vm_refl. Qed.
Lemma D_c3a4c : decode_any W_c3a4c = Some (Jal 1 2075012, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a50 : bv 32 := 0x09651863.
Lemma F_c3a50 : fetch_word AsanUbsan.M.loaded_segments (0xc3a50 : word) = Some W_c3a50.
Proof. vm_refl. Qed.
Lemma D_c3a50 : decode_any W_c3a50 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a54 : bv 32 := 0x0584b503.
Lemma F_c3a54 : fetch_word AsanUbsan.M.loaded_segments (0xc3a54 : word) = Some W_c3a54.
Proof. vm_refl. Qed.
Lemma D_c3a54 : decode_any W_c3a54 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a58 : bv 32 := 0x0604b583.
Lemma F_c3a58 : fetch_word AsanUbsan.M.loaded_segments (0xc3a58 : word) = Some W_c3a58.
Proof. vm_refl. Qed.
Lemma D_c3a58 : decode_any W_c3a58 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a5c : bv 32 := 0x00b505b3.
Lemma F_c3a5c : fetch_word AsanUbsan.M.loaded_segments (0xc3a5c : word) = Some W_c3a5c.
Proof. vm_refl. Qed.
Lemma D_c3a5c : decode_any W_c3a5c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a60 : bv 32 := 0x02b4b023.
Lemma F_c3a60 : fetch_word AsanUbsan.M.loaded_segments (0xc3a60 : word) = Some W_c3a60.
Proof. vm_refl. Qed.
Lemma D_c3a60 : decode_any W_c3a60 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a64 : bv 32 := 0x02a4b423.
Lemma F_c3a64 : fetch_word AsanUbsan.M.loaded_segments (0xc3a64 : word) = Some W_c3a64.
Proof. vm_refl. Qed.
Lemma D_c3a64 : decode_any W_c3a64 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a68 : bv 32 := 0x02a4bc23.
Lemma F_c3a68 : fetch_word AsanUbsan.M.loaded_segments (0xc3a68 : word) = Some W_c3a68.
Proof. vm_refl. Qed.
Lemma D_c3a68 : decode_any W_c3a68 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a6c : bv 32 := 0x00040513.
Lemma F_c3a6c : fetch_word AsanUbsan.M.loaded_segments (0xc3a6c : word) = Some W_c3a6c.
Proof. vm_refl. Qed.
Lemma D_c3a6c : decode_any W_c3a6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a70 : bv 32 := 0x000ab583.
Lemma F_c3a70 : fetch_word AsanUbsan.M.loaded_segments (0xc3a70 : word) = Some W_c3a70.
Proof. vm_refl. Qed.
Lemma D_c3a70 : decode_any W_c3a70 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a74 : bv 32 := 0x02813603.
Lemma F_c3a74 : fetch_word AsanUbsan.M.loaded_segments (0xc3a74 : word) = Some W_c3a74.
Proof. vm_refl. Qed.
Lemma D_c3a74 : decode_any W_c3a74 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a78 : bv 32 := 0x0cc59a63.
Lemma F_c3a78 : fetch_word AsanUbsan.M.loaded_segments (0xc3a78 : word) = Some W_c3a78.
Proof. vm_refl. Qed.
Lemma D_c3a78 : decode_any W_c3a78 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a7c : bv 32 := 0x06813083.
Lemma F_c3a7c : fetch_word AsanUbsan.M.loaded_segments (0xc3a7c : word) = Some W_c3a7c.
Proof. vm_refl. Qed.
Lemma D_c3a7c : decode_any W_c3a7c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a80 : bv 32 := 0x06013403.
Lemma F_c3a80 : fetch_word AsanUbsan.M.loaded_segments (0xc3a80 : word) = Some W_c3a80.
Proof. vm_refl. Qed.
Lemma D_c3a80 : decode_any W_c3a80 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a84 : bv 32 := 0x05813483.
Lemma F_c3a84 : fetch_word AsanUbsan.M.loaded_segments (0xc3a84 : word) = Some W_c3a84.
Proof. vm_refl. Qed.
Lemma D_c3a84 : decode_any W_c3a84 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a88 : bv 32 := 0x05013903.
Lemma F_c3a88 : fetch_word AsanUbsan.M.loaded_segments (0xc3a88 : word) = Some W_c3a88.
Proof. vm_refl. Qed.
Lemma D_c3a88 : decode_any W_c3a88 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a8c : bv 32 := 0x04813983.
Lemma F_c3a8c : fetch_word AsanUbsan.M.loaded_segments (0xc3a8c : word) = Some W_c3a8c.
Proof. vm_refl. Qed.
Lemma D_c3a8c : decode_any W_c3a8c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a90 : bv 32 := 0x04013a03.
Lemma F_c3a90 : fetch_word AsanUbsan.M.loaded_segments (0xc3a90 : word) = Some W_c3a90.
Proof. vm_refl. Qed.
Lemma D_c3a90 : decode_any W_c3a90 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a94 : bv 32 := 0x03813a83.
Lemma F_c3a94 : fetch_word AsanUbsan.M.loaded_segments (0xc3a94 : word) = Some W_c3a94.
Proof. vm_refl. Qed.
Lemma D_c3a94 : decode_any W_c3a94 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a98 : bv 32 := 0x03013b03.
Lemma F_c3a98 : fetch_word AsanUbsan.M.loaded_segments (0xc3a98 : word) = Some W_c3a98.
Proof. vm_refl. Qed.
Lemma D_c3a98 : decode_any W_c3a98 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3a9c : bv 32 := 0x07010113.
Lemma F_c3a9c : fetch_word AsanUbsan.M.loaded_segments (0xc3a9c : word) = Some W_c3a9c.
Proof. vm_refl. Qed.
Lemma D_c3a9c : decode_any W_c3a9c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3aa0 : bv 32 := 0x00008067.
Lemma F_c3aa0 : fetch_word AsanUbsan.M.loaded_segments (0xc3aa0 : word) = Some W_c3aa0.
Proof. vm_refl. Qed.
Lemma D_c3aa0 : decode_any W_c3aa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3aa4 : bv 32 := 0x00800713.
Lemma F_c3aa4 : fetch_word AsanUbsan.M.loaded_segments (0xc3aa4 : word) = Some W_c3aa4.
Proof. vm_refl. Qed.
Lemma D_c3aa4 : decode_any W_c3aa4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3aa8 : bv 32 := 0x000a0593.
Lemma F_c3aa8 : fetch_word AsanUbsan.M.loaded_segments (0xc3aa8 : word) = Some W_c3aa8.
Proof. vm_refl. Qed.
Lemma D_c3aa8 : decode_any W_c3aa8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3aac : bv 32 := 0x00e98733.
Lemma F_c3aac : fetch_word AsanUbsan.M.loaded_segments (0xc3aac : word) = Some W_c3aac.
Proof. vm_refl. Qed.
Lemma D_c3aac : decode_any W_c3aac = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3ab0 : bv 32 := 0x00073783.
Lemma F_c3ab0 : fetch_word AsanUbsan.M.loaded_segments (0xc3ab0 : word) = Some W_c3ab0.
Proof. vm_refl. Qed.
Lemma D_c3ab0 : decode_any W_c3ab0 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3ab4 : bv 32 := 0x40ab0b33.
Lemma F_c3ab4 : fetch_word AsanUbsan.M.loaded_segments (0xc3ab4 : word) = Some W_c3ab4.
Proof. vm_refl. Qed.
Lemma D_c3ab4 : decode_any W_c3ab4 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3ab8 : bv 32 := 0x0784a503.
Lemma F_c3ab8 : fetch_word AsanUbsan.M.loaded_segments (0xc3ab8 : word) = Some W_c3ab8.
Proof. vm_refl. Qed.
Lemma D_c3ab8 : decode_any W_c3ab8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3abc : bv 32 := 0x40c9093b.
Lemma F_c3abc : fetch_word AsanUbsan.M.loaded_segments (0xc3abc : word) = Some W_c3abc.
Proof. vm_refl. Qed.
Lemma D_c3abc : decode_any W_c3abc = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3ac0 : bv 32 := 0x40d787b3.
Lemma F_c3ac0 : fetch_word AsanUbsan.M.loaded_segments (0xc3ac0 : word) = Some W_c3ac0.
Proof. vm_refl. Qed.
Lemma D_c3ac0 : decode_any W_c3ac0 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3ac4 : bv 32 := 0x00f73023.
Lemma F_c3ac4 : fetch_word AsanUbsan.M.loaded_segments (0xc3ac4 : word) = Some W_c3ac4.
Proof. vm_refl. Qed.
Lemma D_c3ac4 : decode_any W_c3ac4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3ac8 : bv 32 := 0x04200893.
Lemma F_c3ac8 : fetch_word AsanUbsan.M.loaded_segments (0xc3ac8 : word) = Some W_c3ac8.
Proof. vm_refl. Qed.
Lemma D_c3ac8 : decode_any W_c3ac8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3acc : bv 32 := 0x00090613.
Lemma F_c3acc : fetch_word AsanUbsan.M.loaded_segments (0xc3acc : word) = Some W_c3acc.
Proof. vm_refl. Qed.
Lemma D_c3acc : decode_any W_c3acc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3ad0 : bv 32 := 0x00000073.
Lemma F_c3ad0 : fetch_word AsanUbsan.M.loaded_segments (0xc3ad0 : word) = Some W_c3ad0.
Proof. vm_refl. Qed.
Lemma D_c3ad0 : decode_any W_c3ad0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_c3ad0 : is_ecall W_c3ad0 = true.
Proof. reflexivity. Qed.

Definition W_c3ad4 : bv 32 := 0x8fdfa0ef.
Lemma F_c3ad4 : fetch_word AsanUbsan.M.loaded_segments (0xc3ad4 : word) = Some W_c3ad4.
Proof. vm_refl. Qed.
Lemma D_c3ad4 : decode_any W_c3ad4 = Some (Jal 1 2074876, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3ad8 : bv 32 := 0x000a0993.
Lemma F_c3ad8 : fetch_word AsanUbsan.M.loaded_segments (0xc3ad8 : word) = Some W_c3ad8.
Proof. vm_refl. Qed.
Lemma D_c3ad8 : decode_any W_c3ad8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3adc : bv 32 := 0xf7650ce3.
Lemma F_c3adc : fetch_word AsanUbsan.M.loaded_segments (0xc3adc : word) = Some W_c3adc.
Proof. vm_refl. Qed.
Lemma D_c3adc : decode_any W_c3adc = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3ae0 : bv 32 := 0x02054c63.
Lemma F_c3ae0 : fetch_word AsanUbsan.M.loaded_segments (0xc3ae0 : word) = Some W_c3ae0.
Proof. vm_refl. Qed.
Lemma D_c3ae0 : decode_any W_c3ae0 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3ae4 : bv 32 := 0x0089b583.
Lemma F_c3ae4 : fetch_word AsanUbsan.M.loaded_segments (0xc3ae4 : word) = Some W_c3ae4.
Proof. vm_refl. Qed.
Lemma D_c3ae4 : decode_any W_c3ae4 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3ae8 : bv 32 := 0x00a5b633.
Lemma F_c3ae8 : fetch_word AsanUbsan.M.loaded_segments (0xc3ae8 : word) = Some W_c3ae8.
Proof. vm_refl. Qed.
Lemma D_c3ae8 : decode_any W_c3ae8 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3aec : bv 32 := 0x00461a13.
Lemma F_c3aec : fetch_word AsanUbsan.M.loaded_segments (0xc3aec : word) = Some W_c3aec.
Proof. vm_refl. Qed.
Lemma D_c3aec : decode_any W_c3aec = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3af0 : bv 32 := 0x01498a33.
Lemma F_c3af0 : fetch_word AsanUbsan.M.loaded_segments (0xc3af0 : word) = Some W_c3af0.
Proof. vm_refl. Qed.
Lemma D_c3af0 : decode_any W_c3af0 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3af4 : bv 32 := 0x000a3703.
Lemma F_c3af4 : fetch_word AsanUbsan.M.loaded_segments (0xc3af4 : word) = Some W_c3af4.
Proof. vm_refl. Qed.
Lemma D_c3af4 : decode_any W_c3af4 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3af8 : bv 32 := 0x40c006b3.
Lemma F_c3af8 : fetch_word AsanUbsan.M.loaded_segments (0xc3af8 : word) = Some W_c3af8.
Proof. vm_refl. Qed.
Lemma D_c3af8 : decode_any W_c3af8 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3afc : bv 32 := 0x00b6f6b3.
Lemma F_c3afc : fetch_word AsanUbsan.M.loaded_segments (0xc3afc : word) = Some W_c3afc.
Proof. vm_refl. Qed.
Lemma D_c3afc : decode_any W_c3afc = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b00 : bv 32 := 0x40d506b3.
Lemma F_c3b00 : fetch_word AsanUbsan.M.loaded_segments (0xc3b00 : word) = Some W_c3b00.
Proof. vm_refl. Qed.
Lemma D_c3b00 : decode_any W_c3b00 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b04 : bv 32 := 0x00d70733.
Lemma F_c3b04 : fetch_word AsanUbsan.M.loaded_segments (0xc3b04 : word) = Some W_c3b04.
Proof. vm_refl. Qed.
Lemma D_c3b04 : decode_any W_c3b04 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b08 : bv 32 := 0x00ea3023.
Lemma F_c3b08 : fetch_word AsanUbsan.M.loaded_segments (0xc3b08 : word) = Some W_c3b08.
Proof. vm_refl. Qed.
Lemma D_c3b08 : decode_any W_c3b08 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b0c : bv 32 := 0xf8a5fce3.
Lemma F_c3b0c : fetch_word AsanUbsan.M.loaded_segments (0xc3b0c : word) = Some W_c3b0c.
Proof. vm_refl. Qed.
Lemma D_c3b0c : decode_any W_c3b0c = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b10 : bv 32 := 0x01800713.
Lemma F_c3b10 : fetch_word AsanUbsan.M.loaded_segments (0xc3b10 : word) = Some W_c3b10.
Proof. vm_refl. Qed.
Lemma D_c3b10 : decode_any W_c3b10 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b14 : bv 32 := 0xf95ff06f.
Lemma F_c3b14 : fetch_word AsanUbsan.M.loaded_segments (0xc3b14 : word) = Some W_c3b14.
Proof. vm_refl. Qed.
Lemma D_c3b14 : decode_any W_c3b14 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b18 : bv 32 := 0x00000513.
Lemma F_c3b18 : fetch_word AsanUbsan.M.loaded_segments (0xc3b18 : word) = Some W_c3b18.
Proof. vm_refl. Qed.
Lemma D_c3b18 : decode_any W_c3b18 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b1c : bv 32 := 0x0004a583.
Lemma F_c3b1c : fetch_word AsanUbsan.M.loaded_segments (0xc3b1c : word) = Some W_c3b1c.
Proof. vm_refl. Qed.
Lemma D_c3b1c : decode_any W_c3b1c = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b20 : bv 32 := 0x0009091b.
Lemma F_c3b20 : fetch_word AsanUbsan.M.loaded_segments (0xc3b20 : word) = Some W_c3b20.
Proof. vm_refl. Qed.
Lemma D_c3b20 : decode_any W_c3b20 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b24 : bv 32 := 0x00200613.
Lemma F_c3b24 : fetch_word AsanUbsan.M.loaded_segments (0xc3b24 : word) = Some W_c3b24.
Proof. vm_refl. Qed.
Lemma D_c3b24 : decode_any W_c3b24 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b28 : bv 32 := 0x0205e593.
Lemma F_c3b28 : fetch_word AsanUbsan.M.loaded_segments (0xc3b28 : word) = Some W_c3b28.
Proof. vm_refl. Qed.
Lemma D_c3b28 : decode_any W_c3b28 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b2c : bv 32 := 0x00b4a023.
Lemma F_c3b2c : fetch_word AsanUbsan.M.loaded_segments (0xc3b2c : word) = Some W_c3b2c.
Proof. vm_refl. Qed.
Lemma D_c3b2c : decode_any W_c3b2c = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b30 : bv 32 := 0x0204b023.
Lemma F_c3b30 : fetch_word AsanUbsan.M.loaded_segments (0xc3b30 : word) = Some W_c3b30.
Proof. vm_refl. Qed.
Lemma D_c3b30 : decode_any W_c3b30 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b34 : bv 32 := 0x0204b423.
Lemma F_c3b34 : fetch_word AsanUbsan.M.loaded_segments (0xc3b34 : word) = Some W_c3b34.
Proof. vm_refl. Qed.
Lemma D_c3b34 : decode_any W_c3b34 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b38 : bv 32 := 0x0204bc23.
Lemma F_c3b38 : fetch_word AsanUbsan.M.loaded_segments (0xc3b38 : word) = Some W_c3b38.
Proof. vm_refl. Qed.
Lemma D_c3b38 : decode_any W_c3b38 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b3c : bv 32 := 0xf2c90ae3.
Lemma F_c3b3c : fetch_word AsanUbsan.M.loaded_segments (0xc3b3c : word) = Some W_c3b3c.
Proof. vm_refl. Qed.
Lemma D_c3b3c : decode_any W_c3b3c = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b40 : bv 32 := 0x0089b503.
Lemma F_c3b40 : fetch_word AsanUbsan.M.loaded_segments (0xc3b40 : word) = Some W_c3b40.
Proof. vm_refl. Qed.
Lemma D_c3b40 : decode_any W_c3b40 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b44 : bv 32 := 0x40a40533.
Lemma F_c3b44 : fetch_word AsanUbsan.M.loaded_segments (0xc3b44 : word) = Some W_c3b44.
Proof. vm_refl. Qed.
Lemma D_c3b44 : decode_any W_c3b44 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b48 : bv 32 := 0xf29ff06f.
Lemma F_c3b48 : fetch_word AsanUbsan.M.loaded_segments (0xc3b48 : word) = Some W_c3b48.
Proof. vm_refl. Qed.
Lemma D_c3b48 : decode_any W_c3b48 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

Definition W_c3b4c : bv 32 := 0xa18fa0ef.
Lemma F_c3b4c : fetch_word AsanUbsan.M.loaded_segments (0xc3b4c : word) = Some W_c3b4c.
Proof. vm_refl. Qed.
Lemma D_c3b4c : decode_any W_c3b4c = Some (Jal 1 2073112, 4%Z).
Proof. vm_refl. Qed.
