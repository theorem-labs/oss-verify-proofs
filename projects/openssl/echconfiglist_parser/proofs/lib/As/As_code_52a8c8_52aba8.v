(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_52a8c8 : bv 32 := 0x00008067.
Lemma F_52a8c8 : fetch_word Asan.M.loaded_segments (0x52a91c : word) = Some W_52a8c8.
Proof. vm_refl. Qed.
Lemma D_52a8c8 : decode_any W_52a8c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8cc : bv 32 := 0xff010113.
Lemma F_52a8cc : fetch_word Asan.M.loaded_segments (0x52a920 : word) = Some W_52a8cc.
Proof. vm_refl. Qed.
Lemma D_52a8cc : decode_any W_52a8cc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8d0 : bv 32 := 0x00113423.
Lemma F_52a8d0 : fetch_word Asan.M.loaded_segments (0x52a924 : word) = Some W_52a8d0.
Proof. vm_refl. Qed.
Lemma D_52a8d0 : decode_any W_52a8d0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8d4 : bv 32 := 0x07852503.
Lemma F_52a8d4 : fetch_word Asan.M.loaded_segments (0x52a928 : word) = Some W_52a8d4.
Proof. vm_refl. Qed.
Lemma D_52a8d4 : decode_any W_52a8d4 = Some (Load SZ4 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8d8 : bv 32 := 0xff1ff0ef.
Lemma F_52a8d8 : fetch_word Asan.M.loaded_segments (0x52a92c : word) = Some W_52a8d8.
Proof. vm_refl. Qed.
Lemma D_52a8d8 : decode_any W_52a8d8 = Some (Jal 1 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8dc : bv 32 := 0x03900893.
Lemma F_52a8dc : fetch_word Asan.M.loaded_segments (0x52a930 : word) = Some W_52a8dc.
Proof. vm_refl. Qed.
Lemma D_52a8dc : decode_any W_52a8dc = Some (OpImm ALU_ADD 17 0 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8e0 : bv 32 := 0x00000073.
Lemma F_52a8e0 : fetch_word Asan.M.loaded_segments (0x52a934 : word) = Some W_52a8e0.
Proof. vm_refl. Qed.
Lemma D_52a8e0 : decode_any W_52a8e0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_52a8e0 : is_ecall W_52a8e0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_52a8e4 : bv 32 := 0x96dfa0ef.
Lemma F_52a8e4 : fetch_word Asan.M.loaded_segments (0x52a938 : word) = Some W_52a8e4.
Proof. vm_refl. Qed.
Lemma D_52a8e4 : decode_any W_52a8e4 = Some (Jal 1 2074988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8e8 : bv 32 := 0x0005051b.
Lemma F_52a8e8 : fetch_word Asan.M.loaded_segments (0x52a93c : word) = Some W_52a8e8.
Proof. vm_refl. Qed.
Lemma D_52a8e8 : decode_any W_52a8e8 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8ec : bv 32 := 0x00813083.
Lemma F_52a8ec : fetch_word Asan.M.loaded_segments (0x52a940 : word) = Some W_52a8ec.
Proof. vm_refl. Qed.
Lemma D_52a8ec : decode_any W_52a8ec = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8f0 : bv 32 := 0x01010113.
Lemma F_52a8f0 : fetch_word Asan.M.loaded_segments (0x52a944 : word) = Some W_52a8f0.
Proof. vm_refl. Qed.
Lemma D_52a8f0 : decode_any W_52a8f0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8f4 : bv 32 := 0x00008067.
Lemma F_52a8f4 : fetch_word Asan.M.loaded_segments (0x52a948 : word) = Some W_52a8f4.
Proof. vm_refl. Qed.
Lemma D_52a8f4 : decode_any W_52a8f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8f8 : bv 32 := 0xfb010113.
Lemma F_52a8f8 : fetch_word Asan.M.loaded_segments (0x52a94c : word) = Some W_52a8f8.
Proof. vm_refl. Qed.
Lemma D_52a8f8 : decode_any W_52a8f8 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8fc : bv 32 := 0x04113423.
Lemma F_52a8fc : fetch_word Asan.M.loaded_segments (0x52a950 : word) = Some W_52a8fc.
Proof. vm_refl. Qed.
Lemma D_52a8fc : decode_any W_52a8fc = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a900 : bv 32 := 0x04813023.
Lemma F_52a900 : fetch_word Asan.M.loaded_segments (0x52a954 : word) = Some W_52a900.
Proof. vm_refl. Qed.
Lemma D_52a900 : decode_any W_52a900 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a904 : bv 32 := 0x02913c23.
Lemma F_52a904 : fetch_word Asan.M.loaded_segments (0x52a958 : word) = Some W_52a904.
Proof. vm_refl. Qed.
Lemma D_52a904 : decode_any W_52a904 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a908 : bv 32 := 0x03213823.
Lemma F_52a908 : fetch_word Asan.M.loaded_segments (0x52a95c : word) = Some W_52a908.
Proof. vm_refl. Qed.
Lemma D_52a908 : decode_any W_52a908 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a90c : bv 32 := 0x03313423.
Lemma F_52a90c : fetch_word Asan.M.loaded_segments (0x52a960 : word) = Some W_52a90c.
Proof. vm_refl. Qed.
Lemma D_52a90c : decode_any W_52a90c = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a910 : bv 32 := 0x00060413.
Lemma F_52a910 : fetch_word Asan.M.loaded_segments (0x52a964 : word) = Some W_52a910.
Proof. vm_refl. Qed.
Lemma D_52a910 : decode_any W_52a910 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a914 : bv 32 := 0x00058913.
Lemma F_52a914 : fetch_word Asan.M.loaded_segments (0x52a968 : word) = Some W_52a914.
Proof. vm_refl. Qed.
Lemma D_52a914 : decode_any W_52a914 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a918 : bv 32 := 0x00050493.
Lemma F_52a918 : fetch_word Asan.M.loaded_segments (0x52a96c : word) = Some W_52a918.
Proof. vm_refl. Qed.
Lemma D_52a918 : decode_any W_52a918 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a91c : bv 32 := 0x00086517.
Lemma F_52a91c : fetch_word Asan.M.loaded_segments (0x52a970 : word) = Some W_52a91c.
Proof. vm_refl. Qed.
Lemma D_52a91c : decode_any W_52a91c = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a920 : bv 32 := 0xca053983.
Lemma F_52a920 : fetch_word Asan.M.loaded_segments (0x52a974 : word) = Some W_52a920.
Proof. vm_refl. Qed.
Lemma D_52a920 : decode_any W_52a920 = Some (Load SZ8 true 19 10 3232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a924 : bv 32 := 0x0009b503.
Lemma F_52a924 : fetch_word Asan.M.loaded_segments (0x52a978 : word) = Some W_52a924.
Proof. vm_refl. Qed.
Lemma D_52a924 : decode_any W_52a924 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a928 : bv 32 := 0x02a13023.
Lemma F_52a928 : fetch_word Asan.M.loaded_segments (0x52a97c : word) = Some W_52a928.
Proof. vm_refl. Qed.
Lemma D_52a928 : decode_any W_52a928 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a92c : bv 32 := 0x0604b603.
Lemma F_52a92c : fetch_word Asan.M.loaded_segments (0x52a980 : word) = Some W_52a92c.
Proof. vm_refl. Qed.
Lemma D_52a92c : decode_any W_52a92c = Some (Load SZ8 true 12 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a930 : bv 32 := 0x0584b583.
Lemma F_52a930 : fetch_word Asan.M.loaded_segments (0x52a984 : word) = Some W_52a930.
Proof. vm_refl. Qed.
Lemma D_52a930 : decode_any W_52a930 = Some (Load SZ8 true 11 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a934 : bv 32 := 0x0784a503.
Lemma F_52a934 : fetch_word Asan.M.loaded_segments (0x52a988 : word) = Some W_52a934.
Proof. vm_refl. Qed.
Lemma D_52a934 : decode_any W_52a934 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a938 : bv 32 := 0x00c036b3.
Lemma F_52a938 : fetch_word Asan.M.loaded_segments (0x52a98c : word) = Some W_52a938.
Proof. vm_refl. Qed.
Lemma D_52a938 : decode_any W_52a938 = Some (Op ALU_SLTU 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a93c : bv 32 := 0x40d406b3.
Lemma F_52a93c : fetch_word Asan.M.loaded_segments (0x52a990 : word) = Some W_52a93c.
Proof. vm_refl. Qed.
Lemma D_52a93c : decode_any W_52a93c = Some (Op ALU_SUB 13 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a940 : bv 32 := 0x01213023.
Lemma F_52a940 : fetch_word Asan.M.loaded_segments (0x52a994 : word) = Some W_52a940.
Proof. vm_refl. Qed.
Lemma D_52a940 : decode_any W_52a940 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a944 : bv 32 := 0x00d13423.
Lemma F_52a944 : fetch_word Asan.M.loaded_segments (0x52a998 : word) = Some W_52a944.
Proof. vm_refl. Qed.
Lemma D_52a944 : decode_any W_52a944 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a948 : bv 32 := 0x00b13823.
Lemma F_52a948 : fetch_word Asan.M.loaded_segments (0x52a99c : word) = Some W_52a948.
Proof. vm_refl. Qed.
Lemma D_52a948 : decode_any W_52a948 = Some (Store SZ8 2 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a94c : bv 32 := 0x00c13c23.
Lemma F_52a94c : fetch_word Asan.M.loaded_segments (0x52a9a0 : word) = Some W_52a94c.
Proof. vm_refl. Qed.
Lemma D_52a94c : decode_any W_52a94c = Some (Store SZ8 2 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a950 : bv 32 := 0x04068c63.
Lemma F_52a950 : fetch_word Asan.M.loaded_segments (0x52a9a4 : word) = Some W_52a950.
Proof. vm_refl. Qed.
Lemma D_52a950 : decode_any W_52a950 = Some (Branch BC_EQ 13 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a954 : bv 32 := 0x04100893.
Lemma F_52a954 : fetch_word Asan.M.loaded_segments (0x52a9a8 : word) = Some W_52a954.
Proof. vm_refl. Qed.
Lemma D_52a954 : decode_any W_52a954 = Some (OpImm ALU_ADD 17 0 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a958 : bv 32 := 0x00010593.
Lemma F_52a958 : fetch_word Asan.M.loaded_segments (0x52a9ac : word) = Some W_52a958.
Proof. vm_refl. Qed.
Lemma D_52a958 : decode_any W_52a958 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a95c : bv 32 := 0x00200613.
Lemma F_52a95c : fetch_word Asan.M.loaded_segments (0x52a9b0 : word) = Some W_52a95c.
Proof. vm_refl. Qed.
Lemma D_52a95c : decode_any W_52a95c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a960 : bv 32 := 0x00000073.
Lemma F_52a960 : fetch_word Asan.M.loaded_segments (0x52a9b4 : word) = Some W_52a960.
Proof. vm_refl. Qed.
Lemma D_52a960 : decode_any W_52a960 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_52a960 : is_ecall W_52a960 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_52a964 : bv 32 := 0x8edfa0ef.
Lemma F_52a964 : fetch_word Asan.M.loaded_segments (0x52a9b8 : word) = Some W_52a964.
Proof. vm_refl. Qed.
Lemma D_52a964 : decode_any W_52a964 = Some (Jal 1 2074860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a968 : bv 32 := 0x04a05863.
Lemma F_52a968 : fetch_word Asan.M.loaded_segments (0x52a9bc : word) = Some W_52a968.
Proof. vm_refl. Qed.
Lemma D_52a968 : decode_any W_52a968 = Some (Branch BC_GE 0 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a96c : bv 32 := 0x00813603.
Lemma F_52a96c : fetch_word Asan.M.loaded_segments (0x52a9c0 : word) = Some W_52a96c.
Proof. vm_refl. Qed.
Lemma D_52a96c : decode_any W_52a96c = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a970 : bv 32 := 0x04a67a63.
Lemma F_52a970 : fetch_word Asan.M.loaded_segments (0x52a9c4 : word) = Some W_52a970.
Proof. vm_refl. Qed.
Lemma D_52a970 : decode_any W_52a970 = Some (Branch BC_GEU 12 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a974 : bv 32 := 0x0584b583.
Lemma F_52a974 : fetch_word Asan.M.loaded_segments (0x52a9c8 : word) = Some W_52a974.
Proof. vm_refl. Qed.
Lemma D_52a974 : decode_any W_52a974 = Some (Load SZ8 true 11 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a978 : bv 32 := 0x0604b683.
Lemma F_52a978 : fetch_word Asan.M.loaded_segments (0x52a9cc : word) = Some W_52a978.
Proof. vm_refl. Qed.
Lemma D_52a978 : decode_any W_52a978 = Some (Load SZ8 true 13 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a97c : bv 32 := 0x40c50533.
Lemma F_52a97c : fetch_word Asan.M.loaded_segments (0x52a9d0 : word) = Some W_52a97c.
Proof. vm_refl. Qed.
Lemma D_52a97c : decode_any W_52a97c = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a980 : bv 32 := 0x00a58533.
Lemma F_52a980 : fetch_word Asan.M.loaded_segments (0x52a9d4 : word) = Some W_52a980.
Proof. vm_refl. Qed.
Lemma D_52a980 : decode_any W_52a980 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a984 : bv 32 := 0x00b4b423.
Lemma F_52a984 : fetch_word Asan.M.loaded_segments (0x52a9d8 : word) = Some W_52a984.
Proof. vm_refl. Qed.
Lemma D_52a984 : decode_any W_52a984 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a988 : bv 32 := 0x00a4b823.
Lemma F_52a988 : fetch_word Asan.M.loaded_segments (0x52a9dc : word) = Some W_52a988.
Proof. vm_refl. Qed.
Lemma D_52a988 : decode_any W_52a988 = Some (Store SZ8 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a98c : bv 32 := 0x04068a63.
Lemma F_52a98c : fetch_word Asan.M.loaded_segments (0x52a9e0 : word) = Some W_52a98c.
Proof. vm_refl. Qed.
Lemma D_52a98c : decode_any W_52a98c = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a990 : bv 32 := 0x00158513.
Lemma F_52a990 : fetch_word Asan.M.loaded_segments (0x52a9e4 : word) = Some W_52a990.
Proof. vm_refl. Qed.
Lemma D_52a990 : decode_any W_52a990 = Some (OpImm ALU_ADD 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a994 : bv 32 := 0x00a4b423.
Lemma F_52a994 : fetch_word Asan.M.loaded_segments (0x52a9e8 : word) = Some W_52a994.
Proof. vm_refl. Qed.
Lemma D_52a994 : decode_any W_52a994 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a998 : bv 32 := 0x0005c503.
Lemma F_52a998 : fetch_word Asan.M.loaded_segments (0x52a9ec : word) = Some W_52a998.
Proof. vm_refl. Qed.
Lemma D_52a998 : decode_any W_52a998 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a99c : bv 32 := 0x00890933.
Lemma F_52a99c : fetch_word Asan.M.loaded_segments (0x52a9f0 : word) = Some W_52a99c.
Proof. vm_refl. Qed.
Lemma D_52a99c : decode_any W_52a99c = Some (Op ALU_ADD 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9a0 : bv 32 := 0xfea90fa3.
Lemma F_52a9a0 : fetch_word Asan.M.loaded_segments (0x52a9f4 : word) = Some W_52a9a0.
Proof. vm_refl. Qed.
Lemma D_52a9a0 : decode_any W_52a9a0 = Some (Store SZ1 18 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9a4 : bv 32 := 0x03c0006f.
Lemma F_52a9a4 : fetch_word Asan.M.loaded_segments (0x52a9f8 : word) = Some W_52a9a4.
Proof. vm_refl. Qed.
Lemma D_52a9a4 : decode_any W_52a9a4 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9a8 : bv 32 := 0x03f00893.
Lemma F_52a9a8 : fetch_word Asan.M.loaded_segments (0x52a9fc : word) = Some W_52a9a8.
Proof. vm_refl. Qed.
Lemma D_52a9a8 : decode_any W_52a9a8 = Some (OpImm ALU_ADD 17 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9ac : bv 32 := 0x00000073.
Lemma F_52a9ac : fetch_word Asan.M.loaded_segments (0x52aa00 : word) = Some W_52a9ac.
Proof. vm_refl. Qed.
Lemma D_52a9ac : decode_any W_52a9ac = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_52a9ac : is_ecall W_52a9ac = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_52a9b0 : bv 32 := 0x8a1fa0ef.
Lemma F_52a9b0 : fetch_word Asan.M.loaded_segments (0x52aa04 : word) = Some W_52a9b0.
Proof. vm_refl. Qed.
Lemma D_52a9b0 : decode_any W_52a9b0 = Some (Jal 1 2074784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9b4 : bv 32 := 0xfaa04ce3.
Lemma F_52a9b4 : fetch_word Asan.M.loaded_segments (0x52aa08 : word) = Some W_52a9b4.
Proof. vm_refl. Qed.
Lemma D_52a9b4 : decode_any W_52a9b4 = Some (Branch BC_LT 0 10 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9b8 : bv 32 := 0x00050a63.
Lemma F_52a9b8 : fetch_word Asan.M.loaded_segments (0x52aa0c : word) = Some W_52a9b8.
Proof. vm_refl. Qed.
Lemma D_52a9b8 : decode_any W_52a9b8 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9bc : bv 32 := 0x02000513.
Lemma F_52a9bc : fetch_word Asan.M.loaded_segments (0x52aa10 : word) = Some W_52a9bc.
Proof. vm_refl. Qed.
Lemma D_52a9bc : decode_any W_52a9bc = Some (OpImm ALU_ADD 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9c0 : bv 32 := 0x0100006f.
Lemma F_52a9c0 : fetch_word Asan.M.loaded_segments (0x52aa14 : word) = Some W_52a9c0.
Proof. vm_refl. Qed.
Lemma D_52a9c0 : decode_any W_52a9c0 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9c4 : bv 32 := 0x00050413.
Lemma F_52a9c4 : fetch_word Asan.M.loaded_segments (0x52aa18 : word) = Some W_52a9c4.
Proof. vm_refl. Qed.
Lemma D_52a9c4 : decode_any W_52a9c4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9c8 : bv 32 := 0x0180006f.
Lemma F_52a9c8 : fetch_word Asan.M.loaded_segments (0x52aa1c : word) = Some W_52a9c8.
Proof. vm_refl. Qed.
Lemma D_52a9c8 : decode_any W_52a9c8 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9cc : bv 32 := 0x01000513.
Lemma F_52a9cc : fetch_word Asan.M.loaded_segments (0x52aa20 : word) = Some W_52a9cc.
Proof. vm_refl. Qed.
Lemma D_52a9cc : decode_any W_52a9cc = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9d0 : bv 32 := 0x00000413.
Lemma F_52a9d0 : fetch_word Asan.M.loaded_segments (0x52aa24 : word) = Some W_52a9d0.
Proof. vm_refl. Qed.
Lemma D_52a9d0 : decode_any W_52a9d0 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9d4 : bv 32 := 0x0004a583.
Lemma F_52a9d4 : fetch_word Asan.M.loaded_segments (0x52aa28 : word) = Some W_52a9d4.
Proof. vm_refl. Qed.
Lemma D_52a9d4 : decode_any W_52a9d4 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9d8 : bv 32 := 0x00a5e533.
Lemma F_52a9d8 : fetch_word Asan.M.loaded_segments (0x52aa2c : word) = Some W_52a9d8.
Proof. vm_refl. Qed.
Lemma D_52a9d8 : decode_any W_52a9d8 = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9dc : bv 32 := 0x00a4a023.
Lemma F_52a9dc : fetch_word Asan.M.loaded_segments (0x52aa30 : word) = Some W_52a9dc.
Proof. vm_refl. Qed.
Lemma D_52a9dc : decode_any W_52a9dc = Some (Store SZ4 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9e0 : bv 32 := 0x0009b503.
Lemma F_52a9e0 : fetch_word Asan.M.loaded_segments (0x52aa34 : word) = Some W_52a9e0.
Proof. vm_refl. Qed.
Lemma D_52a9e0 : decode_any W_52a9e0 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9e4 : bv 32 := 0x02013583.
Lemma F_52a9e4 : fetch_word Asan.M.loaded_segments (0x52aa38 : word) = Some W_52a9e4.
Proof. vm_refl. Qed.
Lemma D_52a9e4 : decode_any W_52a9e4 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9e8 : bv 32 := 0x02b51263.
Lemma F_52a9e8 : fetch_word Asan.M.loaded_segments (0x52aa3c : word) = Some W_52a9e8.
Proof. vm_refl. Qed.
Lemma D_52a9e8 : decode_any W_52a9e8 = Some (Branch BC_NE 10 11 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9ec : bv 32 := 0x00040513.
Lemma F_52a9ec : fetch_word Asan.M.loaded_segments (0x52aa40 : word) = Some W_52a9ec.
Proof. vm_refl. Qed.
Lemma D_52a9ec : decode_any W_52a9ec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9f0 : bv 32 := 0x04813083.
Lemma F_52a9f0 : fetch_word Asan.M.loaded_segments (0x52aa44 : word) = Some W_52a9f0.
Proof. vm_refl. Qed.
Lemma D_52a9f0 : decode_any W_52a9f0 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9f4 : bv 32 := 0x04013403.
Lemma F_52a9f4 : fetch_word Asan.M.loaded_segments (0x52aa48 : word) = Some W_52a9f4.
Proof. vm_refl. Qed.
Lemma D_52a9f4 : decode_any W_52a9f4 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9f8 : bv 32 := 0x03813483.
Lemma F_52a9f8 : fetch_word Asan.M.loaded_segments (0x52aa4c : word) = Some W_52a9f8.
Proof. vm_refl. Qed.
Lemma D_52a9f8 : decode_any W_52a9f8 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9fc : bv 32 := 0x03013903.
Lemma F_52a9fc : fetch_word Asan.M.loaded_segments (0x52aa50 : word) = Some W_52a9fc.
Proof. vm_refl. Qed.
Lemma D_52a9fc : decode_any W_52a9fc = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa00 : bv 32 := 0x02813983.
Lemma F_52aa00 : fetch_word Asan.M.loaded_segments (0x52aa54 : word) = Some W_52aa00.
Proof. vm_refl. Qed.
Lemma D_52aa00 : decode_any W_52aa00 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa04 : bv 32 := 0x05010113.
Lemma F_52aa04 : fetch_word Asan.M.loaded_segments (0x52aa58 : word) = Some W_52aa04.
Proof. vm_refl. Qed.
Lemma D_52aa04 : decode_any W_52aa04 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa08 : bv 32 := 0x00008067.
Lemma F_52aa08 : fetch_word Asan.M.loaded_segments (0x52aa5c : word) = Some W_52aa08.
Proof. vm_refl. Qed.
Lemma D_52aa08 : decode_any W_52aa08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa0c : bv 32 := 0x9d4fa0ef.
Lemma F_52aa0c : fetch_word Asan.M.loaded_segments (0x52aa60 : word) = Some W_52aa0c.
Proof. vm_refl. Qed.
Lemma D_52aa0c : decode_any W_52aa0c = Some (Jal 1 2073044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa10 : bv 32 := 0x07852503.
Lemma F_52aa10 : fetch_word Asan.M.loaded_segments (0x52aa64 : word) = Some W_52aa10.
Proof. vm_refl. Qed.
Lemma D_52aa10 : decode_any W_52aa10 = Some (Load SZ4 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa14 : bv 32 := 0x4590c06f.
Lemma F_52aa14 : fetch_word Asan.M.loaded_segments (0x52aa68 : word) = Some W_52aa14.
Proof. vm_refl. Qed.
Lemma D_52aa14 : decode_any W_52aa14 = Some (Jal 0 52312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa18 : bv 32 := 0xf9010113.
Lemma F_52aa18 : fetch_word Asan.M.loaded_segments (0x52aa6c : word) = Some W_52aa18.
Proof. vm_refl. Qed.
Lemma D_52aa18 : decode_any W_52aa18 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa1c : bv 32 := 0x06113423.
Lemma F_52aa1c : fetch_word Asan.M.loaded_segments (0x52aa70 : word) = Some W_52aa1c.
Proof. vm_refl. Qed.
Lemma D_52aa1c : decode_any W_52aa1c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa20 : bv 32 := 0x06813023.
Lemma F_52aa20 : fetch_word Asan.M.loaded_segments (0x52aa74 : word) = Some W_52aa20.
Proof. vm_refl. Qed.
Lemma D_52aa20 : decode_any W_52aa20 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa24 : bv 32 := 0x04913c23.
Lemma F_52aa24 : fetch_word Asan.M.loaded_segments (0x52aa78 : word) = Some W_52aa24.
Proof. vm_refl. Qed.
Lemma D_52aa24 : decode_any W_52aa24 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa28 : bv 32 := 0x05213823.
Lemma F_52aa28 : fetch_word Asan.M.loaded_segments (0x52aa7c : word) = Some W_52aa28.
Proof. vm_refl. Qed.
Lemma D_52aa28 : decode_any W_52aa28 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa2c : bv 32 := 0x05313423.
Lemma F_52aa2c : fetch_word Asan.M.loaded_segments (0x52aa80 : word) = Some W_52aa2c.
Proof. vm_refl. Qed.
Lemma D_52aa2c : decode_any W_52aa2c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa30 : bv 32 := 0x05413023.
Lemma F_52aa30 : fetch_word Asan.M.loaded_segments (0x52aa84 : word) = Some W_52aa30.
Proof. vm_refl. Qed.
Lemma D_52aa30 : decode_any W_52aa30 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa34 : bv 32 := 0x03513c23.
Lemma F_52aa34 : fetch_word Asan.M.loaded_segments (0x52aa88 : word) = Some W_52aa34.
Proof. vm_refl. Qed.
Lemma D_52aa34 : decode_any W_52aa34 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa38 : bv 32 := 0x03613823.
Lemma F_52aa38 : fetch_word Asan.M.loaded_segments (0x52aa8c : word) = Some W_52aa38.
Proof. vm_refl. Qed.
Lemma D_52aa38 : decode_any W_52aa38 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa3c : bv 32 := 0x00060413.
Lemma F_52aa3c : fetch_word Asan.M.loaded_segments (0x52aa90 : word) = Some W_52aa3c.
Proof. vm_refl. Qed.
Lemma D_52aa3c : decode_any W_52aa3c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa40 : bv 32 := 0x00050493.
Lemma F_52aa40 : fetch_word Asan.M.loaded_segments (0x52aa94 : word) = Some W_52aa40.
Proof. vm_refl. Qed.
Lemma D_52aa40 : decode_any W_52aa40 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa44 : bv 32 := 0x00086517.
Lemma F_52aa44 : fetch_word Asan.M.loaded_segments (0x52aa98 : word) = Some W_52aa44.
Proof. vm_refl. Qed.
Lemma D_52aa44 : decode_any W_52aa44 = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa48 : bv 32 := 0xb7853a83.
Lemma F_52aa48 : fetch_word Asan.M.loaded_segments (0x52aa9c : word) = Some W_52aa48.
Proof. vm_refl. Qed.
Lemma D_52aa48 : decode_any W_52aa48 = Some (Load SZ8 true 21 10 2936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa4c : bv 32 := 0x000ab503.
Lemma F_52aa4c : fetch_word Asan.M.loaded_segments (0x52aaa0 : word) = Some W_52aa4c.
Proof. vm_refl. Qed.
Lemma D_52aa4c : decode_any W_52aa4c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa50 : bv 32 := 0x02a13423.
Lemma F_52aa50 : fetch_word Asan.M.loaded_segments (0x52aaa4 : word) = Some W_52aa50.
Proof. vm_refl. Qed.
Lemma D_52aa50 : decode_any W_52aa50 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa54 : bv 32 := 0x0284b503.
Lemma F_52aa54 : fetch_word Asan.M.loaded_segments (0x52aaa8 : word) = Some W_52aa54.
Proof. vm_refl. Qed.
Lemma D_52aa54 : decode_any W_52aa54 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa58 : bv 32 := 0x0384b603.
Lemma F_52aa58 : fetch_word Asan.M.loaded_segments (0x52aaac : word) = Some W_52aa58.
Proof. vm_refl. Qed.
Lemma D_52aa58 : decode_any W_52aa58 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa5c : bv 32 := 0x40c50b33.
Lemma F_52aa5c : fetch_word Asan.M.loaded_segments (0x52aab0 : word) = Some W_52aa5c.
Proof. vm_refl. Qed.
Lemma D_52aa5c : decode_any W_52aa5c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa60 : bv 32 := 0x00c546b3.
Lemma F_52aa60 : fetch_word Asan.M.loaded_segments (0x52aab4 : word) = Some W_52aa60.
Proof. vm_refl. Qed.
Lemma D_52aa60 : decode_any W_52aa60 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa64 : bv 32 := 0x00c13423.
Lemma F_52aa64 : fetch_word Asan.M.loaded_segments (0x52aab8 : word) = Some W_52aa64.
Proof. vm_refl. Qed.
Lemma D_52aa64 : decode_any W_52aa64 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa68 : bv 32 := 0x01613823.
Lemma F_52aa68 : fetch_word Asan.M.loaded_segments (0x52aabc : word) = Some W_52aa68.
Proof. vm_refl. Qed.
Lemma D_52aa68 : decode_any W_52aa68 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa6c : bv 32 := 0x00b13c23.
Lemma F_52aa6c : fetch_word Asan.M.loaded_segments (0x52aac0 : word) = Some W_52aa6c.
Proof. vm_refl. Qed.
Lemma D_52aa6c : decode_any W_52aa6c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa70 : bv 32 := 0x02813023.
Lemma F_52aa70 : fetch_word Asan.M.loaded_segments (0x52aac4 : word) = Some W_52aa70.
Proof. vm_refl. Qed.
Lemma D_52aa70 : decode_any W_52aa70 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa74 : bv 32 := 0x008b0b33.
Lemma F_52aa74 : fetch_word Asan.M.loaded_segments (0x52aac8 : word) = Some W_52aa74.
Proof. vm_refl. Qed.
Lemma D_52aa74 : decode_any W_52aa74 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa78 : bv 32 := 0x00d03933.
Lemma F_52aa78 : fetch_word Asan.M.loaded_segments (0x52aacc : word) = Some W_52aa78.
Proof. vm_refl. Qed.
Lemma D_52aa78 : decode_any W_52aa78 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa7c : bv 32 := 0x00c50663.
Lemma F_52aa7c : fetch_word Asan.M.loaded_segments (0x52aad0 : word) = Some W_52aa7c.
Proof. vm_refl. Qed.
Lemma D_52aa7c : decode_any W_52aa7c = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa80 : bv 32 := 0x00810993.
Lemma F_52aa80 : fetch_word Asan.M.loaded_segments (0x52aad4 : word) = Some W_52aa80.
Proof. vm_refl. Qed.
Lemma D_52aa80 : decode_any W_52aa80 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa84 : bv 32 := 0x0080006f.
Lemma F_52aa84 : fetch_word Asan.M.loaded_segments (0x52aad8 : word) = Some W_52aa84.
Proof. vm_refl. Qed.
Lemma D_52aa84 : decode_any W_52aa84 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa88 : bv 32 := 0x01810993.
Lemma F_52aa88 : fetch_word Asan.M.loaded_segments (0x52aadc : word) = Some W_52aa88.
Proof. vm_refl. Qed.
Lemma D_52aa88 : decode_any W_52aa88 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa8c : bv 32 := 0x0784a503.
Lemma F_52aa8c : fetch_word Asan.M.loaded_segments (0x52aae0 : word) = Some W_52aa8c.
Proof. vm_refl. Qed.
Lemma D_52aa8c : decode_any W_52aa8c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa90 : bv 32 := 0x00190913.
Lemma F_52aa90 : fetch_word Asan.M.loaded_segments (0x52aae4 : word) = Some W_52aa90.
Proof. vm_refl. Qed.
Lemma D_52aa90 : decode_any W_52aa90 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa94 : bv 32 := 0x04200893.
Lemma F_52aa94 : fetch_word Asan.M.loaded_segments (0x52aae8 : word) = Some W_52aa94.
Proof. vm_refl. Qed.
Lemma D_52aa94 : decode_any W_52aa94 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa98 : bv 32 := 0x00098593.
Lemma F_52aa98 : fetch_word Asan.M.loaded_segments (0x52aaec : word) = Some W_52aa98.
Proof. vm_refl. Qed.
Lemma D_52aa98 : decode_any W_52aa98 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aa9c : bv 32 := 0x00090613.
Lemma F_52aa9c : fetch_word Asan.M.loaded_segments (0x52aaf0 : word) = Some W_52aa9c.
Proof. vm_refl. Qed.
Lemma D_52aa9c : decode_any W_52aa9c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aaa0 : bv 32 := 0x00000073.
Lemma F_52aaa0 : fetch_word Asan.M.loaded_segments (0x52aaf4 : word) = Some W_52aaa0.
Proof. vm_refl. Qed.
Lemma D_52aaa0 : decode_any W_52aaa0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_52aaa0 : is_ecall W_52aaa0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_52aaa4 : bv 32 := 0xfacfa0ef.
Lemma F_52aaa4 : fetch_word Asan.M.loaded_segments (0x52aaf8 : word) = Some W_52aaa4.
Proof. vm_refl. Qed.
Lemma D_52aaa4 : decode_any W_52aaa4 = Some (Jal 1 2074540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aaa8 : bv 32 := 0x09651863.
Lemma F_52aaa8 : fetch_word Asan.M.loaded_segments (0x52aafc : word) = Some W_52aaa8.
Proof. vm_refl. Qed.
Lemma D_52aaa8 : decode_any W_52aaa8 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aaac : bv 32 := 0x0584b503.
Lemma F_52aaac : fetch_word Asan.M.loaded_segments (0x52ab00 : word) = Some W_52aaac.
Proof. vm_refl. Qed.
Lemma D_52aaac : decode_any W_52aaac = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aab0 : bv 32 := 0x0604b583.
Lemma F_52aab0 : fetch_word Asan.M.loaded_segments (0x52ab04 : word) = Some W_52aab0.
Proof. vm_refl. Qed.
Lemma D_52aab0 : decode_any W_52aab0 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aab4 : bv 32 := 0x00b505b3.
Lemma F_52aab4 : fetch_word Asan.M.loaded_segments (0x52ab08 : word) = Some W_52aab4.
Proof. vm_refl. Qed.
Lemma D_52aab4 : decode_any W_52aab4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aab8 : bv 32 := 0x02b4b023.
Lemma F_52aab8 : fetch_word Asan.M.loaded_segments (0x52ab0c : word) = Some W_52aab8.
Proof. vm_refl. Qed.
Lemma D_52aab8 : decode_any W_52aab8 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aabc : bv 32 := 0x02a4b423.
Lemma F_52aabc : fetch_word Asan.M.loaded_segments (0x52ab10 : word) = Some W_52aabc.
Proof. vm_refl. Qed.
Lemma D_52aabc : decode_any W_52aabc = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aac0 : bv 32 := 0x02a4bc23.
Lemma F_52aac0 : fetch_word Asan.M.loaded_segments (0x52ab14 : word) = Some W_52aac0.
Proof. vm_refl. Qed.
Lemma D_52aac0 : decode_any W_52aac0 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aac4 : bv 32 := 0x00040513.
Lemma F_52aac4 : fetch_word Asan.M.loaded_segments (0x52ab18 : word) = Some W_52aac4.
Proof. vm_refl. Qed.
Lemma D_52aac4 : decode_any W_52aac4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aac8 : bv 32 := 0x000ab583.
Lemma F_52aac8 : fetch_word Asan.M.loaded_segments (0x52ab1c : word) = Some W_52aac8.
Proof. vm_refl. Qed.
Lemma D_52aac8 : decode_any W_52aac8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aacc : bv 32 := 0x02813603.
Lemma F_52aacc : fetch_word Asan.M.loaded_segments (0x52ab20 : word) = Some W_52aacc.
Proof. vm_refl. Qed.
Lemma D_52aacc : decode_any W_52aacc = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aad0 : bv 32 := 0x0cc59a63.
Lemma F_52aad0 : fetch_word Asan.M.loaded_segments (0x52ab24 : word) = Some W_52aad0.
Proof. vm_refl. Qed.
Lemma D_52aad0 : decode_any W_52aad0 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aad4 : bv 32 := 0x06813083.
Lemma F_52aad4 : fetch_word Asan.M.loaded_segments (0x52ab28 : word) = Some W_52aad4.
Proof. vm_refl. Qed.
Lemma D_52aad4 : decode_any W_52aad4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aad8 : bv 32 := 0x06013403.
Lemma F_52aad8 : fetch_word Asan.M.loaded_segments (0x52ab2c : word) = Some W_52aad8.
Proof. vm_refl. Qed.
Lemma D_52aad8 : decode_any W_52aad8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aadc : bv 32 := 0x05813483.
Lemma F_52aadc : fetch_word Asan.M.loaded_segments (0x52ab30 : word) = Some W_52aadc.
Proof. vm_refl. Qed.
Lemma D_52aadc : decode_any W_52aadc = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aae0 : bv 32 := 0x05013903.
Lemma F_52aae0 : fetch_word Asan.M.loaded_segments (0x52ab34 : word) = Some W_52aae0.
Proof. vm_refl. Qed.
Lemma D_52aae0 : decode_any W_52aae0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aae4 : bv 32 := 0x04813983.
Lemma F_52aae4 : fetch_word Asan.M.loaded_segments (0x52ab38 : word) = Some W_52aae4.
Proof. vm_refl. Qed.
Lemma D_52aae4 : decode_any W_52aae4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aae8 : bv 32 := 0x04013a03.
Lemma F_52aae8 : fetch_word Asan.M.loaded_segments (0x52ab3c : word) = Some W_52aae8.
Proof. vm_refl. Qed.
Lemma D_52aae8 : decode_any W_52aae8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aaec : bv 32 := 0x03813a83.
Lemma F_52aaec : fetch_word Asan.M.loaded_segments (0x52ab40 : word) = Some W_52aaec.
Proof. vm_refl. Qed.
Lemma D_52aaec : decode_any W_52aaec = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aaf0 : bv 32 := 0x03013b03.
Lemma F_52aaf0 : fetch_word Asan.M.loaded_segments (0x52ab44 : word) = Some W_52aaf0.
Proof. vm_refl. Qed.
Lemma D_52aaf0 : decode_any W_52aaf0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aaf4 : bv 32 := 0x07010113.
Lemma F_52aaf4 : fetch_word Asan.M.loaded_segments (0x52ab48 : word) = Some W_52aaf4.
Proof. vm_refl. Qed.
Lemma D_52aaf4 : decode_any W_52aaf4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aaf8 : bv 32 := 0x00008067.
Lemma F_52aaf8 : fetch_word Asan.M.loaded_segments (0x52ab4c : word) = Some W_52aaf8.
Proof. vm_refl. Qed.
Lemma D_52aaf8 : decode_any W_52aaf8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aafc : bv 32 := 0x00800713.
Lemma F_52aafc : fetch_word Asan.M.loaded_segments (0x52ab50 : word) = Some W_52aafc.
Proof. vm_refl. Qed.
Lemma D_52aafc : decode_any W_52aafc = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab00 : bv 32 := 0x000a0593.
Lemma F_52ab00 : fetch_word Asan.M.loaded_segments (0x52ab54 : word) = Some W_52ab00.
Proof. vm_refl. Qed.
Lemma D_52ab00 : decode_any W_52ab00 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab04 : bv 32 := 0x00e98733.
Lemma F_52ab04 : fetch_word Asan.M.loaded_segments (0x52ab58 : word) = Some W_52ab04.
Proof. vm_refl. Qed.
Lemma D_52ab04 : decode_any W_52ab04 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab08 : bv 32 := 0x00073783.
Lemma F_52ab08 : fetch_word Asan.M.loaded_segments (0x52ab5c : word) = Some W_52ab08.
Proof. vm_refl. Qed.
Lemma D_52ab08 : decode_any W_52ab08 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab0c : bv 32 := 0x40ab0b33.
Lemma F_52ab0c : fetch_word Asan.M.loaded_segments (0x52ab60 : word) = Some W_52ab0c.
Proof. vm_refl. Qed.
Lemma D_52ab0c : decode_any W_52ab0c = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab10 : bv 32 := 0x0784a503.
Lemma F_52ab10 : fetch_word Asan.M.loaded_segments (0x52ab64 : word) = Some W_52ab10.
Proof. vm_refl. Qed.
Lemma D_52ab10 : decode_any W_52ab10 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab14 : bv 32 := 0x40c9093b.
Lemma F_52ab14 : fetch_word Asan.M.loaded_segments (0x52ab68 : word) = Some W_52ab14.
Proof. vm_refl. Qed.
Lemma D_52ab14 : decode_any W_52ab14 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab18 : bv 32 := 0x40d787b3.
Lemma F_52ab18 : fetch_word Asan.M.loaded_segments (0x52ab6c : word) = Some W_52ab18.
Proof. vm_refl. Qed.
Lemma D_52ab18 : decode_any W_52ab18 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab1c : bv 32 := 0x00f73023.
Lemma F_52ab1c : fetch_word Asan.M.loaded_segments (0x52ab70 : word) = Some W_52ab1c.
Proof. vm_refl. Qed.
Lemma D_52ab1c : decode_any W_52ab1c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab20 : bv 32 := 0x04200893.
Lemma F_52ab20 : fetch_word Asan.M.loaded_segments (0x52ab74 : word) = Some W_52ab20.
Proof. vm_refl. Qed.
Lemma D_52ab20 : decode_any W_52ab20 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab24 : bv 32 := 0x00090613.
Lemma F_52ab24 : fetch_word Asan.M.loaded_segments (0x52ab78 : word) = Some W_52ab24.
Proof. vm_refl. Qed.
Lemma D_52ab24 : decode_any W_52ab24 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab28 : bv 32 := 0x00000073.
Lemma F_52ab28 : fetch_word Asan.M.loaded_segments (0x52ab7c : word) = Some W_52ab28.
Proof. vm_refl. Qed.
Lemma D_52ab28 : decode_any W_52ab28 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_52ab28 : is_ecall W_52ab28 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_52ab2c : bv 32 := 0xf24fa0ef.
Lemma F_52ab2c : fetch_word Asan.M.loaded_segments (0x52ab80 : word) = Some W_52ab2c.
Proof. vm_refl. Qed.
Lemma D_52ab2c : decode_any W_52ab2c = Some (Jal 1 2074404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab30 : bv 32 := 0x000a0993.
Lemma F_52ab30 : fetch_word Asan.M.loaded_segments (0x52ab84 : word) = Some W_52ab30.
Proof. vm_refl. Qed.
Lemma D_52ab30 : decode_any W_52ab30 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab34 : bv 32 := 0xf7650ce3.
Lemma F_52ab34 : fetch_word Asan.M.loaded_segments (0x52ab88 : word) = Some W_52ab34.
Proof. vm_refl. Qed.
Lemma D_52ab34 : decode_any W_52ab34 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab38 : bv 32 := 0x02054c63.
Lemma F_52ab38 : fetch_word Asan.M.loaded_segments (0x52ab8c : word) = Some W_52ab38.
Proof. vm_refl. Qed.
Lemma D_52ab38 : decode_any W_52ab38 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab3c : bv 32 := 0x0089b583.
Lemma F_52ab3c : fetch_word Asan.M.loaded_segments (0x52ab90 : word) = Some W_52ab3c.
Proof. vm_refl. Qed.
Lemma D_52ab3c : decode_any W_52ab3c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab40 : bv 32 := 0x00a5b633.
Lemma F_52ab40 : fetch_word Asan.M.loaded_segments (0x52ab94 : word) = Some W_52ab40.
Proof. vm_refl. Qed.
Lemma D_52ab40 : decode_any W_52ab40 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab44 : bv 32 := 0x00461a13.
Lemma F_52ab44 : fetch_word Asan.M.loaded_segments (0x52ab98 : word) = Some W_52ab44.
Proof. vm_refl. Qed.
Lemma D_52ab44 : decode_any W_52ab44 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab48 : bv 32 := 0x01498a33.
Lemma F_52ab48 : fetch_word Asan.M.loaded_segments (0x52ab9c : word) = Some W_52ab48.
Proof. vm_refl. Qed.
Lemma D_52ab48 : decode_any W_52ab48 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab4c : bv 32 := 0x000a3703.
Lemma F_52ab4c : fetch_word Asan.M.loaded_segments (0x52aba0 : word) = Some W_52ab4c.
Proof. vm_refl. Qed.
Lemma D_52ab4c : decode_any W_52ab4c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab50 : bv 32 := 0x40c006b3.
Lemma F_52ab50 : fetch_word Asan.M.loaded_segments (0x52aba4 : word) = Some W_52ab50.
Proof. vm_refl. Qed.
Lemma D_52ab50 : decode_any W_52ab50 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab54 : bv 32 := 0x00b6f6b3.
Lemma F_52ab54 : fetch_word Asan.M.loaded_segments (0x52aba8 : word) = Some W_52ab54.
Proof. vm_refl. Qed.
Lemma D_52ab54 : decode_any W_52ab54 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab58 : bv 32 := 0x40d506b3.
Lemma F_52ab58 : fetch_word Asan.M.loaded_segments (0x52abac : word) = Some W_52ab58.
Proof. vm_refl. Qed.
Lemma D_52ab58 : decode_any W_52ab58 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab5c : bv 32 := 0x00d70733.
Lemma F_52ab5c : fetch_word Asan.M.loaded_segments (0x52abb0 : word) = Some W_52ab5c.
Proof. vm_refl. Qed.
Lemma D_52ab5c : decode_any W_52ab5c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab60 : bv 32 := 0x00ea3023.
Lemma F_52ab60 : fetch_word Asan.M.loaded_segments (0x52abb4 : word) = Some W_52ab60.
Proof. vm_refl. Qed.
Lemma D_52ab60 : decode_any W_52ab60 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab64 : bv 32 := 0xf8a5fce3.
Lemma F_52ab64 : fetch_word Asan.M.loaded_segments (0x52abb8 : word) = Some W_52ab64.
Proof. vm_refl. Qed.
Lemma D_52ab64 : decode_any W_52ab64 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab68 : bv 32 := 0x01800713.
Lemma F_52ab68 : fetch_word Asan.M.loaded_segments (0x52abbc : word) = Some W_52ab68.
Proof. vm_refl. Qed.
Lemma D_52ab68 : decode_any W_52ab68 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab6c : bv 32 := 0xf95ff06f.
Lemma F_52ab6c : fetch_word Asan.M.loaded_segments (0x52abc0 : word) = Some W_52ab6c.
Proof. vm_refl. Qed.
Lemma D_52ab6c : decode_any W_52ab6c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab70 : bv 32 := 0x00000513.
Lemma F_52ab70 : fetch_word Asan.M.loaded_segments (0x52abc4 : word) = Some W_52ab70.
Proof. vm_refl. Qed.
Lemma D_52ab70 : decode_any W_52ab70 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab74 : bv 32 := 0x0004a583.
Lemma F_52ab74 : fetch_word Asan.M.loaded_segments (0x52abc8 : word) = Some W_52ab74.
Proof. vm_refl. Qed.
Lemma D_52ab74 : decode_any W_52ab74 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab78 : bv 32 := 0x0009091b.
Lemma F_52ab78 : fetch_word Asan.M.loaded_segments (0x52abcc : word) = Some W_52ab78.
Proof. vm_refl. Qed.
Lemma D_52ab78 : decode_any W_52ab78 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab7c : bv 32 := 0x00200613.
Lemma F_52ab7c : fetch_word Asan.M.loaded_segments (0x52abd0 : word) = Some W_52ab7c.
Proof. vm_refl. Qed.
Lemma D_52ab7c : decode_any W_52ab7c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab80 : bv 32 := 0x0205e593.
Lemma F_52ab80 : fetch_word Asan.M.loaded_segments (0x52abd4 : word) = Some W_52ab80.
Proof. vm_refl. Qed.
Lemma D_52ab80 : decode_any W_52ab80 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab84 : bv 32 := 0x00b4a023.
Lemma F_52ab84 : fetch_word Asan.M.loaded_segments (0x52abd8 : word) = Some W_52ab84.
Proof. vm_refl. Qed.
Lemma D_52ab84 : decode_any W_52ab84 = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab88 : bv 32 := 0x0204b023.
Lemma F_52ab88 : fetch_word Asan.M.loaded_segments (0x52abdc : word) = Some W_52ab88.
Proof. vm_refl. Qed.
Lemma D_52ab88 : decode_any W_52ab88 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab8c : bv 32 := 0x0204b423.
Lemma F_52ab8c : fetch_word Asan.M.loaded_segments (0x52abe0 : word) = Some W_52ab8c.
Proof. vm_refl. Qed.
Lemma D_52ab8c : decode_any W_52ab8c = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab90 : bv 32 := 0x0204bc23.
Lemma F_52ab90 : fetch_word Asan.M.loaded_segments (0x52abe4 : word) = Some W_52ab90.
Proof. vm_refl. Qed.
Lemma D_52ab90 : decode_any W_52ab90 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab94 : bv 32 := 0xf2c90ae3.
Lemma F_52ab94 : fetch_word Asan.M.loaded_segments (0x52abe8 : word) = Some W_52ab94.
Proof. vm_refl. Qed.
Lemma D_52ab94 : decode_any W_52ab94 = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab98 : bv 32 := 0x0089b503.
Lemma F_52ab98 : fetch_word Asan.M.loaded_segments (0x52abec : word) = Some W_52ab98.
Proof. vm_refl. Qed.
Lemma D_52ab98 : decode_any W_52ab98 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52ab9c : bv 32 := 0x40a40533.
Lemma F_52ab9c : fetch_word Asan.M.loaded_segments (0x52abf0 : word) = Some W_52ab9c.
Proof. vm_refl. Qed.
Lemma D_52ab9c : decode_any W_52ab9c = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aba0 : bv 32 := 0xf29ff06f.
Lemma F_52aba0 : fetch_word Asan.M.loaded_segments (0x52abf4 : word) = Some W_52aba0.
Proof. vm_refl. Qed.
Lemma D_52aba0 : decode_any W_52aba0 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52aba4 : bv 32 := 0x83cfa0ef.
Lemma F_52aba4 : fetch_word Asan.M.loaded_segments (0x52abf8 : word) = Some W_52aba4.
Proof. vm_refl. Qed.
Lemma D_52aba4 : decode_any W_52aba4 = Some (Jal 1 2072636, 4%Z).
Proof. vm_refl. Qed.
