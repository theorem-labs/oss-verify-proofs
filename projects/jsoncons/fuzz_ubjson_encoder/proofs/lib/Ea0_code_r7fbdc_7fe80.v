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

Definition W_9a8f8 : bv 32 := 0x00058613.
Lemma F_9a8f8 : fetch_word Asan.M.loaded_segments (0x9a948 : word) = Some W_9a8f8.
Proof. vm_refl. Qed.
Lemma D_9a8f8 : decode_any W_9a8f8 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a8fc : bv 32 := 0x00189597.
Lemma F_9a8fc : fetch_word Asan.M.loaded_segments (0x9a94c : word) = Some W_9a8fc.
Proof. vm_refl. Qed.
Lemma D_9a8fc : decode_any W_9a8fc = Some (Auipc 11 393, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a900 : bv 32 := 0xf8c58593.
Lemma F_9a900 : fetch_word Asan.M.loaded_segments (0x9a950 : word) = Some W_9a900.
Proof. vm_refl. Qed.
Lemma D_9a900 : decode_any W_9a900 = Some (OpImm ALU_ADD 11 11 3980, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a904 : bv 32 := 0x00050693.
Lemma F_9a904 : fetch_word Asan.M.loaded_segments (0x9a954 : word) = Some W_9a904.
Proof. vm_refl. Qed.
Lemma D_9a904 : decode_any W_9a904 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a908 : bv 32 := 0x00058513.
Lemma F_9a908 : fetch_word Asan.M.loaded_segments (0x9a958 : word) = Some W_9a908.
Proof. vm_refl. Qed.
Lemma D_9a908 : decode_any W_9a908 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a90c : bv 32 := 0x00068593.
Lemma F_9a90c : fetch_word Asan.M.loaded_segments (0x9a95c : word) = Some W_9a90c.
Proof. vm_refl. Qed.
Lemma D_9a90c : decode_any W_9a90c = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a910 : bv 32 := 0x00000693.
Lemma F_9a910 : fetch_word Asan.M.loaded_segments (0x9a960 : word) = Some W_9a910.
Proof. vm_refl. Qed.
Lemma D_9a910 : decode_any W_9a910 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a914 : bv 32 := 0x0040006f.
Lemma F_9a914 : fetch_word Asan.M.loaded_segments (0x9a964 : word) = Some W_9a914.
Proof. vm_refl. Qed.
Lemma D_9a914 : decode_any W_9a914 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a918 : bv 32 := 0xf9010113.
Lemma F_9a918 : fetch_word Asan.M.loaded_segments (0x9a968 : word) = Some W_9a918.
Proof. vm_refl. Qed.
Lemma D_9a918 : decode_any W_9a918 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a91c : bv 32 := 0x06113423.
Lemma F_9a91c : fetch_word Asan.M.loaded_segments (0x9a96c : word) = Some W_9a91c.
Proof. vm_refl. Qed.
Lemma D_9a91c : decode_any W_9a91c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a920 : bv 32 := 0x06813023.
Lemma F_9a920 : fetch_word Asan.M.loaded_segments (0x9a970 : word) = Some W_9a920.
Proof. vm_refl. Qed.
Lemma D_9a920 : decode_any W_9a920 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a924 : bv 32 := 0x04913c23.
Lemma F_9a924 : fetch_word Asan.M.loaded_segments (0x9a974 : word) = Some W_9a924.
Proof. vm_refl. Qed.
Lemma D_9a924 : decode_any W_9a924 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a928 : bv 32 := 0x05213823.
Lemma F_9a928 : fetch_word Asan.M.loaded_segments (0x9a978 : word) = Some W_9a928.
Proof. vm_refl. Qed.
Lemma D_9a928 : decode_any W_9a928 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a92c : bv 32 := 0x05313423.
Lemma F_9a92c : fetch_word Asan.M.loaded_segments (0x9a97c : word) = Some W_9a92c.
Proof. vm_refl. Qed.
Lemma D_9a92c : decode_any W_9a92c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a930 : bv 32 := 0x05413023.
Lemma F_9a930 : fetch_word Asan.M.loaded_segments (0x9a980 : word) = Some W_9a930.
Proof. vm_refl. Qed.
Lemma D_9a930 : decode_any W_9a930 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a934 : bv 32 := 0x03513c23.
Lemma F_9a934 : fetch_word Asan.M.loaded_segments (0x9a984 : word) = Some W_9a934.
Proof. vm_refl. Qed.
Lemma D_9a934 : decode_any W_9a934 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a938 : bv 32 := 0x03613823.
Lemma F_9a938 : fetch_word Asan.M.loaded_segments (0x9a988 : word) = Some W_9a938.
Proof. vm_refl. Qed.
Lemma D_9a938 : decode_any W_9a938 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a93c : bv 32 := 0x03713423.
Lemma F_9a93c : fetch_word Asan.M.loaded_segments (0x9a98c : word) = Some W_9a93c.
Proof. vm_refl. Qed.
Lemma D_9a93c : decode_any W_9a93c = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a940 : bv 32 := 0x03813023.
Lemma F_9a940 : fetch_word Asan.M.loaded_segments (0x9a990 : word) = Some W_9a940.
Proof. vm_refl. Qed.
Lemma D_9a940 : decode_any W_9a940 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a944 : bv 32 := 0x01913c23.
Lemma F_9a944 : fetch_word Asan.M.loaded_segments (0x9a994 : word) = Some W_9a944.
Proof. vm_refl. Qed.
Lemma D_9a944 : decode_any W_9a944 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a948 : bv 32 := 0x00068413.
Lemma F_9a948 : fetch_word Asan.M.loaded_segments (0x9a998 : word) = Some W_9a948.
Proof. vm_refl. Qed.
Lemma D_9a948 : decode_any W_9a948 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a94c : bv 32 := 0x00050493.
Lemma F_9a94c : fetch_word Asan.M.loaded_segments (0x9a99c : word) = Some W_9a94c.
Proof. vm_refl. Qed.
Lemma D_9a94c : decode_any W_9a94c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a950 : bv 32 := 0x00b13423.
Lemma F_9a950 : fetch_word Asan.M.loaded_segments (0x9a9a0 : word) = Some W_9a950.
Proof. vm_refl. Qed.
Lemma D_9a950 : decode_any W_9a950 = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a954 : bv 32 := 0x00c13823.
Lemma F_9a954 : fetch_word Asan.M.loaded_segments (0x9a9a4 : word) = Some W_9a954.
Proof. vm_refl. Qed.
Lemma D_9a954 : decode_any W_9a954 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a958 : bv 32 := 0x00068463.
Lemma F_9a958 : fetch_word Asan.M.loaded_segments (0x9a9a8 : word) = Some W_9a958.
Proof. vm_refl. Qed.
Lemma D_9a958 : decode_any W_9a958 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a960 : bv 32 := 0x0006069b.
Lemma F_9a960 : fetch_word Asan.M.loaded_segments (0x9a9b0 : word) = Some W_9a960.
Proof. vm_refl. Qed.
Lemma D_9a960 : decode_any W_9a960 = Some (OpImm32 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a964 : bv 32 := 0x00000513.
Lemma F_9a964 : fetch_word Asan.M.loaded_segments (0x9a9b4 : word) = Some W_9a964.
Proof. vm_refl. Qed.
Lemma D_9a964 : decode_any W_9a964 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a968 : bv 32 := 0x1c068a63.
Lemma F_9a968 : fetch_word Asan.M.loaded_segments (0x9a9b8 : word) = Some W_9a968.
Proof. vm_refl. Qed.
Lemma D_9a968 : decode_any W_9a968 = Some (Branch BC_EQ 13 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a96c : bv 32 := 0x1c058863.
Lemma F_9a96c : fetch_word Asan.M.loaded_segments (0x9a9bc : word) = Some W_9a96c.
Proof. vm_refl. Qed.
Lemma D_9a96c : decode_any W_9a96c = Some (Branch BC_EQ 11 0 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a970 : bv 32 := 0x02065693.
Lemma F_9a970 : fetch_word Asan.M.loaded_segments (0x9a9c0 : word) = Some W_9a970.
Proof. vm_refl. Qed.
Lemma D_9a970 : decode_any W_9a970 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a974 : bv 32 := 0xfff00513.
Lemma F_9a974 : fetch_word Asan.M.loaded_segments (0x9a9c4 : word) = Some W_9a974.
Proof. vm_refl. Qed.
Lemma D_9a974 : decode_any W_9a974 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a978 : bv 32 := 0xfff76717.
Lemma F_9a978 : fetch_word Asan.M.loaded_segments (0x9a9c8 : word) = Some W_9a978.
Proof. vm_refl. Qed.
Lemma D_9a978 : decode_any W_9a978 = Some (Auipc 14 1048438, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a97c : bv 32 := 0xfff76797.
Lemma F_9a97c : fetch_word Asan.M.loaded_segments (0x9a9cc : word) = Some W_9a97c.
Proof. vm_refl. Qed.
Lemma D_9a97c : decode_any W_9a97c = Some (Auipc 15 1048438, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a980 : bv 32 := 0x02055513.
Lemma F_9a980 : fetch_word Asan.M.loaded_segments (0x9a9d0 : word) = Some W_9a980.
Proof. vm_refl. Qed.
Lemma D_9a980 : decode_any W_9a980 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a984 : bv 32 := 0x9547b783.
Lemma F_9a984 : fetch_word Asan.M.loaded_segments (0x9a9d4 : word) = Some W_9a984.
Proof. vm_refl. Qed.
Lemma D_9a984 : decode_any W_9a984 = Some (Load SZ8 true 15 15 2388, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a988 : bv 32 := 0x00a67633.
Lemma F_9a988 : fetch_word Asan.M.loaded_segments (0x9a9d8 : word) = Some W_9a988.
Proof. vm_refl. Qed.
Lemma D_9a988 : decode_any W_9a988 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a98c : bv 32 := 0xfff76517.
Lemma F_9a98c : fetch_word Asan.M.loaded_segments (0x9a9dc : word) = Some W_9a98c.
Proof. vm_refl. Qed.
Lemma D_9a98c : decode_any W_9a98c = Some (Auipc 10 1048438, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a990 : bv 32 := 0xa4453803.
Lemma F_9a990 : fetch_word Asan.M.loaded_segments (0x9a9e0 : word) = Some W_9a990.
Proof. vm_refl. Qed.
Lemma D_9a990 : decode_any W_9a990 = Some (Load SZ8 true 16 10 2628, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a994 : bv 32 := 0x92073503.
Lemma F_9a994 : fetch_word Asan.M.loaded_segments (0x9a9e4 : word) = Some W_9a994.
Proof. vm_refl. Qed.
Lemma D_9a994 : decode_any W_9a994 = Some (Load SZ8 true 10 14 2336, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a998 : bv 32 := 0x02f60733.
Lemma F_9a998 : fetch_word Asan.M.loaded_segments (0x9a9e8 : word) = Some W_9a998.
Proof. vm_refl. Qed.
Lemma D_9a998 : decode_any W_9a998 = Some (Mul M_MUL 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a99c : bv 32 := 0x00361793.
Lemma F_9a99c : fetch_word Asan.M.loaded_segments (0x9a9ec : word) = Some W_9a99c.
Proof. vm_refl. Qed.
Lemma D_9a99c : decode_any W_9a99c = Some (ShiftImm ALU_SLL 15 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9a0 : bv 32 := 0x01074633.
Lemma F_9a9a0 : fetch_word Asan.M.loaded_segments (0x9a9f0 : word) = Some W_9a9a0.
Proof. vm_refl. Qed.
Lemma D_9a9a0 : decode_any W_9a9a0 = Some (Op ALU_XOR 12 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9a4 : bv 32 := 0x00f58733.
Lemma F_9a9a4 : fetch_word Asan.M.loaded_segments (0x9a9f4 : word) = Some W_9a9a4.
Proof. vm_refl. Qed.
Lemma D_9a9a4 : decode_any W_9a9a4 = Some (Op ALU_ADD 14 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9a8 : bv 32 := 0x0005b783.
Lemma F_9a9a8 : fetch_word Asan.M.loaded_segments (0x9a9f8 : word) = Some W_9a9a8.
Proof. vm_refl. Qed.
Lemma D_9a9a8 : decode_any W_9a9a8 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9ac : bv 32 := 0x00858593.
Lemma F_9a9ac : fetch_word Asan.M.loaded_segments (0x9a9fc : word) = Some W_9a9ac.
Proof. vm_refl. Qed.
Lemma D_9a9ac : decode_any W_9a9ac = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9b0 : bv 32 := 0x02a787b3.
Lemma F_9a9b0 : fetch_word Asan.M.loaded_segments (0x9aa00 : word) = Some W_9a9b0.
Proof. vm_refl. Qed.
Lemma D_9a9b0 : decode_any W_9a9b0 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9b4 : bv 32 := 0x02f7d813.
Lemma F_9a9b4 : fetch_word Asan.M.loaded_segments (0x9aa04 : word) = Some W_9a9b4.
Proof. vm_refl. Qed.
Lemma D_9a9b4 : decode_any W_9a9b4 = Some (ShiftImm ALU_SRL 16 15 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9b8 : bv 32 := 0x00f847b3.
Lemma F_9a9b8 : fetch_word Asan.M.loaded_segments (0x9aa08 : word) = Some W_9a9b8.
Proof. vm_refl. Qed.
Lemma D_9a9b8 : decode_any W_9a9b8 = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9bc : bv 32 := 0x02a787b3.
Lemma F_9a9bc : fetch_word Asan.M.loaded_segments (0x9aa0c : word) = Some W_9a9bc.
Proof. vm_refl. Qed.
Lemma D_9a9bc : decode_any W_9a9bc = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9c0 : bv 32 := 0x00c7c633.
Lemma F_9a9c0 : fetch_word Asan.M.loaded_segments (0x9aa10 : word) = Some W_9a9c0.
Proof. vm_refl. Qed.
Lemma D_9a9c0 : decode_any W_9a9c0 = Some (Op ALU_XOR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9c4 : bv 32 := 0x02a60633.
Lemma F_9a9c4 : fetch_word Asan.M.loaded_segments (0x9aa14 : word) = Some W_9a9c4.
Proof. vm_refl. Qed.
Lemma D_9a9c4 : decode_any W_9a9c4 = Some (Mul M_MUL 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9c8 : bv 32 := 0xfee590e3.
Lemma F_9a9c8 : fetch_word Asan.M.loaded_segments (0x9aa18 : word) = Some W_9a9c8.
Proof. vm_refl. Qed.
Lemma D_9a9c8 : decode_any W_9a9c8 = Some (Branch BC_NE 11 14 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9cc : bv 32 := 0x00010b37.
Lemma F_9a9cc : fetch_word Asan.M.loaded_segments (0x9aa1c : word) = Some W_9a9cc.
Proof. vm_refl. Qed.
Lemma D_9a9cc : decode_any W_9a9cc = Some (Lui 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9d0 : bv 32 := 0x80000bb7.
Lemma F_9a9d0 : fetch_word Asan.M.loaded_segments (0x9aa20 : word) = Some W_9a9d0.
Proof. vm_refl. Qed.
Lemma D_9a9d0 : decode_any W_9a9d0 = Some (Lui 23 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9d4 : bv 32 := 0x02a685b3.
Lemma F_9a9d4 : fetch_word Asan.M.loaded_segments (0x9aa24 : word) = Some W_9a9d4.
Proof. vm_refl. Qed.
Lemma D_9a9d4 : decode_any W_9a9d4 = Some (Mul M_MUL 11 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9d8 : bv 32 := 0x004006b7.
Lemma F_9a9d8 : fetch_word Asan.M.loaded_segments (0x9aa28 : word) = Some W_9a9d8.
Proof. vm_refl. Qed.
Lemma D_9a9d8 : decode_any W_9a9d8 = Some (Lui 13 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9dc : bv 32 := 0xfffb0b1b.
Lemma F_9a9dc : fetch_word Asan.M.loaded_segments (0x9aa2c : word) = Some W_9a9dc.
Proof. vm_refl. Qed.
Lemma D_9a9dc : decode_any W_9a9dc = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9e0 : bv 32 := 0xfffb8b9b.
Lemma F_9a9e0 : fetch_word Asan.M.loaded_segments (0x9aa30 : word) = Some W_9a9e0.
Proof. vm_refl. Qed.
Lemma D_9a9e0 : decode_any W_9a9e0 = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9e4 : bv 32 := 0x02f5d713.
Lemma F_9a9e4 : fetch_word Asan.M.loaded_segments (0x9aa34 : word) = Some W_9a9e4.
Proof. vm_refl. Qed.
Lemma D_9a9e4 : decode_any W_9a9e4 = Some (ShiftImm ALU_SRL 14 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9e8 : bv 32 := 0x00b745b3.
Lemma F_9a9e8 : fetch_word Asan.M.loaded_segments (0x9aa38 : word) = Some W_9a9e8.
Proof. vm_refl. Qed.
Lemma D_9a9e8 : decode_any W_9a9e8 = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9ec : bv 32 := 0x02a585b3.
Lemma F_9a9ec : fetch_word Asan.M.loaded_segments (0x9aa3c : word) = Some W_9a9ec.
Proof. vm_refl. Qed.
Lemma D_9a9ec : decode_any W_9a9ec = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9f0 : bv 32 := 0x00c5c5b3.
Lemma F_9a9f0 : fetch_word Asan.M.loaded_segments (0x9aa40 : word) = Some W_9a9f0.
Proof. vm_refl. Qed.
Lemma D_9a9f0 : decode_any W_9a9f0 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9f4 : bv 32 := 0x02a585b3.
Lemma F_9a9f4 : fetch_word Asan.M.loaded_segments (0x9aa44 : word) = Some W_9a9f4.
Proof. vm_refl. Qed.
Lemma D_9a9f4 : decode_any W_9a9f4 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9f8 : bv 32 := 0x02f5d613.
Lemma F_9a9f8 : fetch_word Asan.M.loaded_segments (0x9aa48 : word) = Some W_9a9f8.
Proof. vm_refl. Qed.
Lemma D_9a9f8 : decode_any W_9a9f8 = Some (ShiftImm ALU_SRL 12 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a9fc : bv 32 := 0x00b645b3.
Lemma F_9a9fc : fetch_word Asan.M.loaded_segments (0x9aa4c : word) = Some W_9a9fc.
Proof. vm_refl. Qed.
Lemma D_9a9fc : decode_any W_9a9fc = Some (Op ALU_XOR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa00 : bv 32 := 0x02a58533.
Lemma F_9aa00 : fetch_word Asan.M.loaded_segments (0x9aa50 : word) = Some W_9aa00.
Proof. vm_refl. Qed.
Lemma D_9aa00 : decode_any W_9aa00 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa04 : bv 32 := 0x02f55593.
Lemma F_9aa04 : fetch_word Asan.M.loaded_segments (0x9aa54 : word) = Some W_9aa04.
Proof. vm_refl. Qed.
Lemma D_9aa04 : decode_any W_9aa04 = Some (ShiftImm ALU_SRL 11 10 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa08 : bv 32 := 0x00a5c9b3.
Lemma F_9aa08 : fetch_word Asan.M.loaded_segments (0x9aa58 : word) = Some W_9aa08.
Proof. vm_refl. Qed.
Lemma D_9aa08 : decode_any W_9aa08 = Some (Op ALU_XOR 19 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa0c : bv 32 := 0x02c99513.
Lemma F_9aa0c : fetch_word Asan.M.loaded_segments (0x9aa5c : word) = Some W_9aa0c.
Proof. vm_refl. Qed.
Lemma D_9aa0c : decode_any W_9aa0c = Some (ShiftImm ALU_SLL 10 19 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa10 : bv 32 := 0x02a55513.
Lemma F_9aa10 : fetch_word Asan.M.loaded_segments (0x9aa60 : word) = Some W_9aa10.
Proof. vm_refl. Qed.
Lemma D_9aa10 : decode_any W_9aa10 = Some (ShiftImm ALU_SRL 10 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa14 : bv 32 := 0x00a48933.
Lemma F_9aa14 : fetch_word Asan.M.loaded_segments (0x9aa64 : word) = Some W_9aa14.
Proof. vm_refl. Qed.
Lemma D_9aa14 : decode_any W_9aa14 = Some (Op ALU_ADD 18 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa18 : bv 32 := 0x00092503.
Lemma F_9aa18 : fetch_word Asan.M.loaded_segments (0x9aa68 : word) = Some W_9aa18.
Proof. vm_refl. Qed.
Lemma D_9aa18 : decode_any W_9aa18 = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa1c : bv 32 := 0x01068c1b.
Lemma F_9aa1c : fetch_word Asan.M.loaded_segments (0x9aa6c : word) = Some W_9aa1c.
Proof. vm_refl. Qed.
Lemma D_9aa1c : decode_any W_9aa1c = Some (OpImm32 24 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa20 : bv 32 := 0x01848c33.
Lemma F_9aa20 : fetch_word Asan.M.loaded_segments (0x9aa70 : word) = Some W_9aa20.
Proof. vm_refl. Qed.
Lemma D_9aa20 : decode_any W_9aa20 = Some (Op ALU_ADD 24 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa24 : bv 32 := 0x0230000f.
Lemma F_9aa24 : fetch_word Asan.M.loaded_segments (0x9aa74 : word) = Some W_9aa24.
Proof. vm_refl. Qed.
Lemma D_9aa24 : decode_any W_9aa24 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa28 : bv 32 := 0x01757cb3.
Lemma F_9aa28 : fetch_word Asan.M.loaded_segments (0x9aa78 : word) = Some W_9aa28.
Proof. vm_refl. Qed.
Lemma D_9aa28 : decode_any W_9aa28 = Some (Op ALU_AND 25 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa2c : bv 32 := 0x0086869b.
Lemma F_9aa2c : fetch_word Asan.M.loaded_segments (0x9aa7c : word) = Some W_9aa2c.
Proof. vm_refl. Qed.
Lemma D_9aa2c : decode_any W_9aa2c = Some (OpImm32 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa30 : bv 32 := 0x00d48a33.
Lemma F_9aa30 : fetch_word Asan.M.loaded_segments (0x9aa80 : word) = Some W_9aa30.
Proof. vm_refl. Qed.
Lemma D_9aa30 : decode_any W_9aa30 = Some (Op ALU_ADD 20 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa34 : bv 32 := 0x000c8593.
Lemma F_9aa34 : fetch_word Asan.M.loaded_segments (0x9aa84 : word) = Some W_9aa34.
Proof. vm_refl. Qed.
Lemma D_9aa34 : decode_any W_9aa34 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa38 : bv 32 := 0x04058c63.
Lemma F_9aa38 : fetch_word Asan.M.loaded_segments (0x9aa88 : word) = Some W_9aa38.
Proof. vm_refl. Qed.
Lemma D_9aa38 : decode_any W_9aa38 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa3c : bv 32 := 0x00058513.
Lemma F_9aa3c : fetch_word Asan.M.loaded_segments (0x9aa8c : word) = Some W_9aa3c.
Proof. vm_refl. Qed.
Lemma D_9aa3c : decode_any W_9aa3c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa40 : bv 32 := 0x0105d59b.
Lemma F_9aa40 : fetch_word Asan.M.loaded_segments (0x9aa90 : word) = Some W_9aa40.
Proof. vm_refl. Qed.
Lemma D_9aa40 : decode_any W_9aa40 = Some (ShiftImm32 ALU_SRL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa44 : bv 32 := 0x00359613.
Lemma F_9aa44 : fetch_word Asan.M.loaded_segments (0x9aa94 : word) = Some W_9aa44.
Proof. vm_refl. Qed.
Lemma D_9aa44 : decode_any W_9aa44 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa48 : bv 32 := 0x00cc0633.
Lemma F_9aa48 : fetch_word Asan.M.loaded_segments (0x9aa98 : word) = Some W_9aa48.
Proof. vm_refl. Qed.
Lemma D_9aa48 : decode_any W_9aa48 = Some (Op ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa4c : bv 32 := 0x00063603.
Lemma F_9aa4c : fetch_word Asan.M.loaded_segments (0x9aa9c : word) = Some W_9aa4c.
Proof. vm_refl. Qed.
Lemma D_9aa4c : decode_any W_9aa4c = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa50 : bv 32 := 0x02060463.
Lemma F_9aa50 : fetch_word Asan.M.loaded_segments (0x9aaa0 : word) = Some W_9aa50.
Proof. vm_refl. Qed.
Lemma D_9aa50 : decode_any W_9aa50 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa54 : bv 32 := 0x02051593.
Lemma F_9aa54 : fetch_word Asan.M.loaded_segments (0x9aaa4 : word) = Some W_9aa54.
Proof. vm_refl. Qed.
Lemma D_9aa54 : decode_any W_9aa54 = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa58 : bv 32 := 0x0205d593.
Lemma F_9aa58 : fetch_word Asan.M.loaded_segments (0x9aaa8 : word) = Some W_9aa58.
Proof. vm_refl. Qed.
Lemma D_9aa58 : decode_any W_9aa58 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa5c : bv 32 := 0x0165f5b3.
Lemma F_9aa5c : fetch_word Asan.M.loaded_segments (0x9aaac : word) = Some W_9aa5c.
Proof. vm_refl. Qed.
Lemma D_9aa5c : decode_any W_9aa5c = Some (Op ALU_AND 11 11 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa60 : bv 32 := 0x00459593.
Lemma F_9aa60 : fetch_word Asan.M.loaded_segments (0x9aab0 : word) = Some W_9aa60.
Proof. vm_refl. Qed.
Lemma D_9aa60 : decode_any W_9aa60 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa64 : bv 32 := 0x00b605b3.
Lemma F_9aa64 : fetch_word Asan.M.loaded_segments (0x9aab4 : word) = Some W_9aa64.
Proof. vm_refl. Qed.
Lemma D_9aa64 : decode_any W_9aa64 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa68 : bv 32 := 0x0005b603.
Lemma F_9aa68 : fetch_word Asan.M.loaded_segments (0x9aab8 : word) = Some W_9aa68.
Proof. vm_refl. Qed.
Lemma D_9aa68 : decode_any W_9aa68 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa6c : bv 32 := 0x0085a583.
Lemma F_9aa6c : fetch_word Asan.M.loaded_segments (0x9aabc : word) = Some W_9aa6c.
Proof. vm_refl. Qed.
Lemma D_9aa6c : decode_any W_9aa6c = Some (Load SZ4 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa70 : bv 32 := 0xfcc994e3.
Lemma F_9aa70 : fetch_word Asan.M.loaded_segments (0x9aac0 : word) = Some W_9aa70.
Proof. vm_refl. Qed.
Lemma D_9aa70 : decode_any W_9aa70 = Some (Branch BC_NE 19 12 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa74 : bv 32 := 0x0c80006f.
Lemma F_9aa74 : fetch_word Asan.M.loaded_segments (0x9aac4 : word) = Some W_9aa74.
Proof. vm_refl. Qed.
Lemma D_9aa74 : decode_any W_9aa74 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa90 : bv 32 := 0x00090513.
Lemma F_9aa90 : fetch_word Asan.M.loaded_segments (0x9aae0 : word) = Some W_9aa90.
Proof. vm_refl. Qed.
Lemma D_9aa90 : decode_any W_9aa90 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa94 : bv 32 := 0x5f8000ef.
Lemma F_9aa94 : fetch_word Asan.M.loaded_segments (0x9aae4 : word) = Some W_9aa94.
Proof. vm_refl. Qed.
Lemma D_9aa94 : decode_any W_9aa94 = Some (Jal 1 1528, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa98 : bv 32 := 0x00050a93.
Lemma F_9aa98 : fetch_word Asan.M.loaded_segments (0x9aae8 : word) = Some W_9aa98.
Proof. vm_refl. Qed.
Lemma D_9aa98 : decode_any W_9aa98 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aa9c : bv 32 := 0x03950663.
Lemma F_9aa9c : fetch_word Asan.M.loaded_segments (0x9aaec : word) = Some W_9aa9c.
Proof. vm_refl. Qed.
Lemma D_9aa9c : decode_any W_9aa9c = Some (Branch BC_EQ 10 25 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aac8 : bv 32 := 0x00400537.
Lemma F_9aac8 : fetch_word Asan.M.loaded_segments (0x9ab18 : word) = Some W_9aac8.
Proof. vm_refl. Qed.
Lemma D_9aac8 : decode_any W_9aac8 = Some (Lui 10 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aacc : bv 32 := 0x00a48533.
Lemma F_9aacc : fetch_word Asan.M.loaded_segments (0x9ab1c : word) = Some W_9aacc.
Proof. vm_refl. Qed.
Lemma D_9aacc : decode_any W_9aacc = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aad0 : bv 32 := 0x00100593.
Lemma F_9aad0 : fetch_word Asan.M.loaded_segments (0x9ab20 : word) = Some W_9aad0.
Proof. vm_refl. Qed.
Lemma D_9aad0 : decode_any W_9aad0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aad4 : bv 32 := 0x00b5252f.
Lemma F_9aad4 : fetch_word Asan.M.loaded_segments (0x9ab24 : word) = Some W_9aad4.
Proof. vm_refl. Qed.
Lemma D_9aad4 : decode_any W_9aad4 = Some (Amo AMO_ADD AW false false 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aad8 : bv 32 := 0x0015051b.
Lemma F_9aad8 : fetch_word Asan.M.loaded_segments (0x9ab28 : word) = Some W_9aad8.
Proof. vm_refl. Qed.
Lemma D_9aad8 : decode_any W_9aad8 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aadc : bv 32 := 0x02051493.
Lemma F_9aadc : fetch_word Asan.M.loaded_segments (0x9ab2c : word) = Some W_9aadc.
Proof. vm_refl. Qed.
Lemma D_9aadc : decode_any W_9aadc = Some (ShiftImm ALU_SLL 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aae0 : bv 32 := 0x0204d493.
Lemma F_9aae0 : fetch_word Asan.M.loaded_segments (0x9ab30 : word) = Some W_9aae0.
Proof. vm_refl. Qed.
Lemma D_9aae0 : decode_any W_9aae0 = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aae4 : bv 32 := 0x08054663.
Lemma F_9aae4 : fetch_word Asan.M.loaded_segments (0x9ab34 : word) = Some W_9aae4.
Proof. vm_refl. Qed.
Lemma D_9aae4 : decode_any W_9aae4 = Some (Branch BC_LT 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aae8 : bv 32 := 0x00050b93.
Lemma F_9aae8 : fetch_word Asan.M.loaded_segments (0x9ab38 : word) = Some W_9aae8.
Proof. vm_refl. Qed.
Lemma D_9aae8 : decode_any W_9aae8 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aaec : bv 32 := 0x0104d593.
Lemma F_9aaec : fetch_word Asan.M.loaded_segments (0x9ab3c : word) = Some W_9aaec.
Proof. vm_refl. Qed.
Lemma D_9aaec : decode_any W_9aaec = Some (ShiftImm ALU_SRL 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aaf0 : bv 32 := 0x00359513.
Lemma F_9aaf0 : fetch_word Asan.M.loaded_segments (0x9ab40 : word) = Some W_9aaf0.
Proof. vm_refl. Qed.
Lemma D_9aaf0 : decode_any W_9aaf0 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aaf4 : bv 32 := 0x00ac0533.
Lemma F_9aaf4 : fetch_word Asan.M.loaded_segments (0x9ab44 : word) = Some W_9aaf4.
Proof. vm_refl. Qed.
Lemma D_9aaf4 : decode_any W_9aaf4 = Some (Op ALU_ADD 10 24 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aaf8 : bv 32 := 0x00053503.
Lemma F_9aaf8 : fetch_word Asan.M.loaded_segments (0x9ab48 : word) = Some W_9aaf8.
Proof. vm_refl. Qed.
Lemma D_9aaf8 : decode_any W_9aaf8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9aafc : bv 32 := 0x08050a63.
Lemma F_9aafc : fetch_word Asan.M.loaded_segments (0x9ab4c : word) = Some W_9aafc.
Proof. vm_refl. Qed.
Lemma D_9aafc : decode_any W_9aafc = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab00 : bv 32 := 0x0164f5b3.
Lemma F_9ab00 : fetch_word Asan.M.loaded_segments (0x9ab50 : word) = Some W_9ab00.
Proof. vm_refl. Qed.
Lemma D_9ab00 : decode_any W_9ab00 = Some (Op ALU_AND 11 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab04 : bv 32 := 0x00459593.
Lemma F_9ab04 : fetch_word Asan.M.loaded_segments (0x9ab54 : word) = Some W_9ab04.
Proof. vm_refl. Qed.
Lemma D_9ab04 : decode_any W_9ab04 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab08 : bv 32 := 0x00b504b3.
Lemma F_9ab08 : fetch_word Asan.M.loaded_segments (0x9ab58 : word) = Some W_9ab08.
Proof. vm_refl. Qed.
Lemma D_9ab08 : decode_any W_9ab08 = Some (Op ALU_ADD 9 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab0c : bv 32 := 0x00810613.
Lemma F_9ab0c : fetch_word Asan.M.loaded_segments (0x9ab5c : word) = Some W_9ab0c.
Proof. vm_refl. Qed.
Lemma D_9ab0c : decode_any W_9ab0c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab10 : bv 32 := 0x00048513.
Lemma F_9ab10 : fetch_word Asan.M.loaded_segments (0x9ab60 : word) = Some W_9ab10.
Proof. vm_refl. Qed.
Lemma D_9ab10 : decode_any W_9ab10 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab14 : bv 32 := 0x00000593.
Lemma F_9ab14 : fetch_word Asan.M.loaded_segments (0x9ab64 : word) = Some W_9ab14.
Proof. vm_refl. Qed.
Lemma D_9ab14 : decode_any W_9ab14 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab18 : bv 32 := 0x00098693.
Lemma F_9ab18 : fetch_word Asan.M.loaded_segments (0x9ab68 : word) = Some W_9ab18.
Proof. vm_refl. Qed.
Lemma D_9ab18 : decode_any W_9ab18 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab1c : bv 32 := 0xaf5ff0ef.
Lemma F_9ab1c : fetch_word Asan.M.loaded_segments (0x9ab6c : word) = Some W_9ab1c.
Proof. vm_refl. Qed.
Lemma D_9ab1c : decode_any W_9ab1c = Some (Jal 1 2095860, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab20 : bv 32 := 0x0154a423.
Lemma F_9ab20 : fetch_word Asan.M.loaded_segments (0x9ab70 : word) = Some W_9ab20.
Proof. vm_refl. Qed.
Lemma D_9ab20 : decode_any W_9ab20 = Some (Store SZ4 9 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab24 : bv 32 := 0x0310000f.
Lemma F_9ab24 : fetch_word Asan.M.loaded_segments (0x9ab74 : word) = Some W_9ab24.
Proof. vm_refl. Qed.
Lemma D_9ab24 : decode_any W_9ab24 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab28 : bv 32 := 0x000b8513.
Lemma F_9ab28 : fetch_word Asan.M.loaded_segments (0x9ab78 : word) = Some W_9ab28.
Proof. vm_refl. Qed.
Lemma D_9ab28 : decode_any W_9ab28 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab2c : bv 32 := 0x01792023.
Lemma F_9ab2c : fetch_word Asan.M.loaded_segments (0x9ab7c : word) = Some W_9ab2c.
Proof. vm_refl. Qed.
Lemma D_9ab2c : decode_any W_9ab2c = Some (Store SZ4 18 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab30 : bv 32 := 0x00040663.
Lemma F_9ab30 : fetch_word Asan.M.loaded_segments (0x9ab80 : word) = Some W_9ab30.
Proof. vm_refl. Qed.
Lemma D_9ab30 : decode_any W_9ab30 = Some (Branch BC_EQ 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab3c : bv 32 := 0x06813083.
Lemma F_9ab3c : fetch_word Asan.M.loaded_segments (0x9ab8c : word) = Some W_9ab3c.
Proof. vm_refl. Qed.
Lemma D_9ab3c : decode_any W_9ab3c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab40 : bv 32 := 0x06013403.
Lemma F_9ab40 : fetch_word Asan.M.loaded_segments (0x9ab90 : word) = Some W_9ab40.
Proof. vm_refl. Qed.
Lemma D_9ab40 : decode_any W_9ab40 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab44 : bv 32 := 0x05813483.
Lemma F_9ab44 : fetch_word Asan.M.loaded_segments (0x9ab94 : word) = Some W_9ab44.
Proof. vm_refl. Qed.
Lemma D_9ab44 : decode_any W_9ab44 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab48 : bv 32 := 0x05013903.
Lemma F_9ab48 : fetch_word Asan.M.loaded_segments (0x9ab98 : word) = Some W_9ab48.
Proof. vm_refl. Qed.
Lemma D_9ab48 : decode_any W_9ab48 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab4c : bv 32 := 0x04813983.
Lemma F_9ab4c : fetch_word Asan.M.loaded_segments (0x9ab9c : word) = Some W_9ab4c.
Proof. vm_refl. Qed.
Lemma D_9ab4c : decode_any W_9ab4c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab50 : bv 32 := 0x04013a03.
Lemma F_9ab50 : fetch_word Asan.M.loaded_segments (0x9aba0 : word) = Some W_9ab50.
Proof. vm_refl. Qed.
Lemma D_9ab50 : decode_any W_9ab50 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab54 : bv 32 := 0x03813a83.
Lemma F_9ab54 : fetch_word Asan.M.loaded_segments (0x9aba4 : word) = Some W_9ab54.
Proof. vm_refl. Qed.
Lemma D_9ab54 : decode_any W_9ab54 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab58 : bv 32 := 0x03013b03.
Lemma F_9ab58 : fetch_word Asan.M.loaded_segments (0x9aba8 : word) = Some W_9ab58.
Proof. vm_refl. Qed.
Lemma D_9ab58 : decode_any W_9ab58 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab5c : bv 32 := 0x02813b83.
Lemma F_9ab5c : fetch_word Asan.M.loaded_segments (0x9abac : word) = Some W_9ab5c.
Proof. vm_refl. Qed.
Lemma D_9ab5c : decode_any W_9ab5c = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab60 : bv 32 := 0x02013c03.
Lemma F_9ab60 : fetch_word Asan.M.loaded_segments (0x9abb0 : word) = Some W_9ab60.
Proof. vm_refl. Qed.
Lemma D_9ab60 : decode_any W_9ab60 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab64 : bv 32 := 0x01813c83.
Lemma F_9ab64 : fetch_word Asan.M.loaded_segments (0x9abb4 : word) = Some W_9ab64.
Proof. vm_refl. Qed.
Lemma D_9ab64 : decode_any W_9ab64 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab68 : bv 32 := 0x07010113.
Lemma F_9ab68 : fetch_word Asan.M.loaded_segments (0x9abb8 : word) = Some W_9ab68.
Proof. vm_refl. Qed.
Lemma D_9ab68 : decode_any W_9ab68 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ab6c : bv 32 := 0x00008067.
Lemma F_9ab6c : fetch_word Asan.M.loaded_segments (0x9abbc : word) = Some W_9ab6c.
Proof. vm_refl. Qed.
Lemma D_9ab6c : decode_any W_9ab6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
