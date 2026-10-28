(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9e924 : bv 32 := 0xf9010113.
Lemma F_9e924 : fetch_word Ubsan.M.loaded_segments (0x9ff58 : word) = Some W_9e924.
Proof. vm_refl. Qed.
Lemma D_9e924 : decode_any W_9e924 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e928 : bv 32 := 0x06113423.
Lemma F_9e928 : fetch_word Ubsan.M.loaded_segments (0x9ff5c : word) = Some W_9e928.
Proof. vm_refl. Qed.
Lemma D_9e928 : decode_any W_9e928 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e92c : bv 32 := 0x06813023.
Lemma F_9e92c : fetch_word Ubsan.M.loaded_segments (0x9ff60 : word) = Some W_9e92c.
Proof. vm_refl. Qed.
Lemma D_9e92c : decode_any W_9e92c = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e930 : bv 32 := 0x04913c23.
Lemma F_9e930 : fetch_word Ubsan.M.loaded_segments (0x9ff64 : word) = Some W_9e930.
Proof. vm_refl. Qed.
Lemma D_9e930 : decode_any W_9e930 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e934 : bv 32 := 0x05213823.
Lemma F_9e934 : fetch_word Ubsan.M.loaded_segments (0x9ff68 : word) = Some W_9e934.
Proof. vm_refl. Qed.
Lemma D_9e934 : decode_any W_9e934 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e938 : bv 32 := 0x05313423.
Lemma F_9e938 : fetch_word Ubsan.M.loaded_segments (0x9ff6c : word) = Some W_9e938.
Proof. vm_refl. Qed.
Lemma D_9e938 : decode_any W_9e938 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e93c : bv 32 := 0x05413023.
Lemma F_9e93c : fetch_word Ubsan.M.loaded_segments (0x9ff70 : word) = Some W_9e93c.
Proof. vm_refl. Qed.
Lemma D_9e93c : decode_any W_9e93c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e940 : bv 32 := 0x03513c23.
Lemma F_9e940 : fetch_word Ubsan.M.loaded_segments (0x9ff74 : word) = Some W_9e940.
Proof. vm_refl. Qed.
Lemma D_9e940 : decode_any W_9e940 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e944 : bv 32 := 0x03613823.
Lemma F_9e944 : fetch_word Ubsan.M.loaded_segments (0x9ff78 : word) = Some W_9e944.
Proof. vm_refl. Qed.
Lemma D_9e944 : decode_any W_9e944 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e948 : bv 32 := 0x00060413.
Lemma F_9e948 : fetch_word Ubsan.M.loaded_segments (0x9ff7c : word) = Some W_9e948.
Proof. vm_refl. Qed.
Lemma D_9e948 : decode_any W_9e948 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e94c : bv 32 := 0x00050493.
Lemma F_9e94c : fetch_word Ubsan.M.loaded_segments (0x9ff80 : word) = Some W_9e94c.
Proof. vm_refl. Qed.
Lemma D_9e94c : decode_any W_9e94c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e950 : bv 32 := 0x00017517.
Lemma F_9e950 : fetch_word Ubsan.M.loaded_segments (0x9ff84 : word) = Some W_9e950.
Proof. vm_refl. Qed.
Lemma D_9e950 : decode_any W_9e950 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e954 : bv 32 := 0x26453a83.
Lemma F_9e954 : fetch_word Ubsan.M.loaded_segments (0x9ff88 : word) = Some W_9e954.
Proof. vm_refl. Qed.
Lemma D_9e954 : decode_any W_9e954 = Some (Load SZ8 true 21 10 612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e958 : bv 32 := 0x000ab503.
Lemma F_9e958 : fetch_word Ubsan.M.loaded_segments (0x9ff8c : word) = Some W_9e958.
Proof. vm_refl. Qed.
Lemma D_9e958 : decode_any W_9e958 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e95c : bv 32 := 0x02a13423.
Lemma F_9e95c : fetch_word Ubsan.M.loaded_segments (0x9ff90 : word) = Some W_9e95c.
Proof. vm_refl. Qed.
Lemma D_9e95c : decode_any W_9e95c = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e960 : bv 32 := 0x0284b503.
Lemma F_9e960 : fetch_word Ubsan.M.loaded_segments (0x9ff94 : word) = Some W_9e960.
Proof. vm_refl. Qed.
Lemma D_9e960 : decode_any W_9e960 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e964 : bv 32 := 0x0384b603.
Lemma F_9e964 : fetch_word Ubsan.M.loaded_segments (0x9ff98 : word) = Some W_9e964.
Proof. vm_refl. Qed.
Lemma D_9e964 : decode_any W_9e964 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e968 : bv 32 := 0x40c50b33.
Lemma F_9e968 : fetch_word Ubsan.M.loaded_segments (0x9ff9c : word) = Some W_9e968.
Proof. vm_refl. Qed.
Lemma D_9e968 : decode_any W_9e968 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e96c : bv 32 := 0x00c546b3.
Lemma F_9e96c : fetch_word Ubsan.M.loaded_segments (0x9ffa0 : word) = Some W_9e96c.
Proof. vm_refl. Qed.
Lemma D_9e96c : decode_any W_9e96c = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e970 : bv 32 := 0x00c13423.
Lemma F_9e970 : fetch_word Ubsan.M.loaded_segments (0x9ffa4 : word) = Some W_9e970.
Proof. vm_refl. Qed.
Lemma D_9e970 : decode_any W_9e970 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e974 : bv 32 := 0x01613823.
Lemma F_9e974 : fetch_word Ubsan.M.loaded_segments (0x9ffa8 : word) = Some W_9e974.
Proof. vm_refl. Qed.
Lemma D_9e974 : decode_any W_9e974 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e978 : bv 32 := 0x00b13c23.
Lemma F_9e978 : fetch_word Ubsan.M.loaded_segments (0x9ffac : word) = Some W_9e978.
Proof. vm_refl. Qed.
Lemma D_9e978 : decode_any W_9e978 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e97c : bv 32 := 0x02813023.
Lemma F_9e97c : fetch_word Ubsan.M.loaded_segments (0x9ffb0 : word) = Some W_9e97c.
Proof. vm_refl. Qed.
Lemma D_9e97c : decode_any W_9e97c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e980 : bv 32 := 0x008b0b33.
Lemma F_9e980 : fetch_word Ubsan.M.loaded_segments (0x9ffb4 : word) = Some W_9e980.
Proof. vm_refl. Qed.
Lemma D_9e980 : decode_any W_9e980 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e984 : bv 32 := 0x00d03933.
Lemma F_9e984 : fetch_word Ubsan.M.loaded_segments (0x9ffb8 : word) = Some W_9e984.
Proof. vm_refl. Qed.
Lemma D_9e984 : decode_any W_9e984 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e988 : bv 32 := 0x00c50663.
Lemma F_9e988 : fetch_word Ubsan.M.loaded_segments (0x9ffbc : word) = Some W_9e988.
Proof. vm_refl. Qed.
Lemma D_9e988 : decode_any W_9e988 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e98c : bv 32 := 0x00810993.
Lemma F_9e98c : fetch_word Ubsan.M.loaded_segments (0x9ffc0 : word) = Some W_9e98c.
Proof. vm_refl. Qed.
Lemma D_9e98c : decode_any W_9e98c = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e990 : bv 32 := 0x0080006f.
Lemma F_9e990 : fetch_word Ubsan.M.loaded_segments (0x9ffc4 : word) = Some W_9e990.
Proof. vm_refl. Qed.
Lemma D_9e990 : decode_any W_9e990 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e994 : bv 32 := 0x01810993.
Lemma F_9e994 : fetch_word Ubsan.M.loaded_segments (0x9ffc8 : word) = Some W_9e994.
Proof. vm_refl. Qed.
Lemma D_9e994 : decode_any W_9e994 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e998 : bv 32 := 0x0784a503.
Lemma F_9e998 : fetch_word Ubsan.M.loaded_segments (0x9ffcc : word) = Some W_9e998.
Proof. vm_refl. Qed.
Lemma D_9e998 : decode_any W_9e998 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e99c : bv 32 := 0x00190913.
Lemma F_9e99c : fetch_word Ubsan.M.loaded_segments (0x9ffd0 : word) = Some W_9e99c.
Proof. vm_refl. Qed.
Lemma D_9e99c : decode_any W_9e99c = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9a0 : bv 32 := 0x04200893.
Lemma F_9e9a0 : fetch_word Ubsan.M.loaded_segments (0x9ffd4 : word) = Some W_9e9a0.
Proof. vm_refl. Qed.
Lemma D_9e9a0 : decode_any W_9e9a0 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9a4 : bv 32 := 0x00098593.
Lemma F_9e9a4 : fetch_word Ubsan.M.loaded_segments (0x9ffd8 : word) = Some W_9e9a4.
Proof. vm_refl. Qed.
Lemma D_9e9a4 : decode_any W_9e9a4 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9a8 : bv 32 := 0x00090613.
Lemma F_9e9a8 : fetch_word Ubsan.M.loaded_segments (0x9ffdc : word) = Some W_9e9a8.
Proof. vm_refl. Qed.
Lemma D_9e9a8 : decode_any W_9e9a8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9ac : bv 32 := 0x00000073.
Lemma F_9e9ac : fetch_word Ubsan.M.loaded_segments (0x9ffe0 : word) = Some W_9e9ac.
Proof. vm_refl. Qed.
Lemma D_9e9ac : decode_any W_9e9ac = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9e9ac : is_ecall W_9e9ac = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9e9b0 : bv 32 := 0xfcdfa0ef.
Lemma F_9e9b0 : fetch_word Ubsan.M.loaded_segments (0x9ffe4 : word) = Some W_9e9b0.
Proof. vm_refl. Qed.
Lemma D_9e9b0 : decode_any W_9e9b0 = Some (Jal 1 2076620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9b4 : bv 32 := 0x09651863.
Lemma F_9e9b4 : fetch_word Ubsan.M.loaded_segments (0x9ffe8 : word) = Some W_9e9b4.
Proof. vm_refl. Qed.
Lemma D_9e9b4 : decode_any W_9e9b4 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9b8 : bv 32 := 0x0584b503.
Lemma F_9e9b8 : fetch_word Ubsan.M.loaded_segments (0x9ffec : word) = Some W_9e9b8.
Proof. vm_refl. Qed.
Lemma D_9e9b8 : decode_any W_9e9b8 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9bc : bv 32 := 0x0604b583.
Lemma F_9e9bc : fetch_word Ubsan.M.loaded_segments (0x9fff0 : word) = Some W_9e9bc.
Proof. vm_refl. Qed.
Lemma D_9e9bc : decode_any W_9e9bc = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9c0 : bv 32 := 0x00b505b3.
Lemma F_9e9c0 : fetch_word Ubsan.M.loaded_segments (0x9fff4 : word) = Some W_9e9c0.
Proof. vm_refl. Qed.
Lemma D_9e9c0 : decode_any W_9e9c0 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9c4 : bv 32 := 0x02b4b023.
Lemma F_9e9c4 : fetch_word Ubsan.M.loaded_segments (0x9fff8 : word) = Some W_9e9c4.
Proof. vm_refl. Qed.
Lemma D_9e9c4 : decode_any W_9e9c4 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9c8 : bv 32 := 0x02a4b423.
Lemma F_9e9c8 : fetch_word Ubsan.M.loaded_segments (0x9fffc : word) = Some W_9e9c8.
Proof. vm_refl. Qed.
Lemma D_9e9c8 : decode_any W_9e9c8 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9cc : bv 32 := 0x02a4bc23.
Lemma F_9e9cc : fetch_word Ubsan.M.loaded_segments (0xa0000 : word) = Some W_9e9cc.
Proof. vm_refl. Qed.
Lemma D_9e9cc : decode_any W_9e9cc = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9d0 : bv 32 := 0x00040513.
Lemma F_9e9d0 : fetch_word Ubsan.M.loaded_segments (0xa0004 : word) = Some W_9e9d0.
Proof. vm_refl. Qed.
Lemma D_9e9d0 : decode_any W_9e9d0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9d4 : bv 32 := 0x000ab583.
Lemma F_9e9d4 : fetch_word Ubsan.M.loaded_segments (0xa0008 : word) = Some W_9e9d4.
Proof. vm_refl. Qed.
Lemma D_9e9d4 : decode_any W_9e9d4 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9d8 : bv 32 := 0x02813603.
Lemma F_9e9d8 : fetch_word Ubsan.M.loaded_segments (0xa000c : word) = Some W_9e9d8.
Proof. vm_refl. Qed.
Lemma D_9e9d8 : decode_any W_9e9d8 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9dc : bv 32 := 0x0cc59a63.
Lemma F_9e9dc : fetch_word Ubsan.M.loaded_segments (0xa0010 : word) = Some W_9e9dc.
Proof. vm_refl. Qed.
Lemma D_9e9dc : decode_any W_9e9dc = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9e0 : bv 32 := 0x06813083.
Lemma F_9e9e0 : fetch_word Ubsan.M.loaded_segments (0xa0014 : word) = Some W_9e9e0.
Proof. vm_refl. Qed.
Lemma D_9e9e0 : decode_any W_9e9e0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9e4 : bv 32 := 0x06013403.
Lemma F_9e9e4 : fetch_word Ubsan.M.loaded_segments (0xa0018 : word) = Some W_9e9e4.
Proof. vm_refl. Qed.
Lemma D_9e9e4 : decode_any W_9e9e4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9e8 : bv 32 := 0x05813483.
Lemma F_9e9e8 : fetch_word Ubsan.M.loaded_segments (0xa001c : word) = Some W_9e9e8.
Proof. vm_refl. Qed.
Lemma D_9e9e8 : decode_any W_9e9e8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9ec : bv 32 := 0x05013903.
Lemma F_9e9ec : fetch_word Ubsan.M.loaded_segments (0xa0020 : word) = Some W_9e9ec.
Proof. vm_refl. Qed.
Lemma D_9e9ec : decode_any W_9e9ec = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9f0 : bv 32 := 0x04813983.
Lemma F_9e9f0 : fetch_word Ubsan.M.loaded_segments (0xa0024 : word) = Some W_9e9f0.
Proof. vm_refl. Qed.
Lemma D_9e9f0 : decode_any W_9e9f0 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9f4 : bv 32 := 0x04013a03.
Lemma F_9e9f4 : fetch_word Ubsan.M.loaded_segments (0xa0028 : word) = Some W_9e9f4.
Proof. vm_refl. Qed.
Lemma D_9e9f4 : decode_any W_9e9f4 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9f8 : bv 32 := 0x03813a83.
Lemma F_9e9f8 : fetch_word Ubsan.M.loaded_segments (0xa002c : word) = Some W_9e9f8.
Proof. vm_refl. Qed.
Lemma D_9e9f8 : decode_any W_9e9f8 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e9fc : bv 32 := 0x03013b03.
Lemma F_9e9fc : fetch_word Ubsan.M.loaded_segments (0xa0030 : word) = Some W_9e9fc.
Proof. vm_refl. Qed.
Lemma D_9e9fc : decode_any W_9e9fc = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea00 : bv 32 := 0x07010113.
Lemma F_9ea00 : fetch_word Ubsan.M.loaded_segments (0xa0034 : word) = Some W_9ea00.
Proof. vm_refl. Qed.
Lemma D_9ea00 : decode_any W_9ea00 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea04 : bv 32 := 0x00008067.
Lemma F_9ea04 : fetch_word Ubsan.M.loaded_segments (0xa0038 : word) = Some W_9ea04.
Proof. vm_refl. Qed.
Lemma D_9ea04 : decode_any W_9ea04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea08 : bv 32 := 0x00800713.
Lemma F_9ea08 : fetch_word Ubsan.M.loaded_segments (0xa003c : word) = Some W_9ea08.
Proof. vm_refl. Qed.
Lemma D_9ea08 : decode_any W_9ea08 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea0c : bv 32 := 0x000a0593.
Lemma F_9ea0c : fetch_word Ubsan.M.loaded_segments (0xa0040 : word) = Some W_9ea0c.
Proof. vm_refl. Qed.
Lemma D_9ea0c : decode_any W_9ea0c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea10 : bv 32 := 0x00e98733.
Lemma F_9ea10 : fetch_word Ubsan.M.loaded_segments (0xa0044 : word) = Some W_9ea10.
Proof. vm_refl. Qed.
Lemma D_9ea10 : decode_any W_9ea10 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea14 : bv 32 := 0x00073783.
Lemma F_9ea14 : fetch_word Ubsan.M.loaded_segments (0xa0048 : word) = Some W_9ea14.
Proof. vm_refl. Qed.
Lemma D_9ea14 : decode_any W_9ea14 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea18 : bv 32 := 0x40ab0b33.
Lemma F_9ea18 : fetch_word Ubsan.M.loaded_segments (0xa004c : word) = Some W_9ea18.
Proof. vm_refl. Qed.
Lemma D_9ea18 : decode_any W_9ea18 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea1c : bv 32 := 0x0784a503.
Lemma F_9ea1c : fetch_word Ubsan.M.loaded_segments (0xa0050 : word) = Some W_9ea1c.
Proof. vm_refl. Qed.
Lemma D_9ea1c : decode_any W_9ea1c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea20 : bv 32 := 0x40c9093b.
Lemma F_9ea20 : fetch_word Ubsan.M.loaded_segments (0xa0054 : word) = Some W_9ea20.
Proof. vm_refl. Qed.
Lemma D_9ea20 : decode_any W_9ea20 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea24 : bv 32 := 0x40d787b3.
Lemma F_9ea24 : fetch_word Ubsan.M.loaded_segments (0xa0058 : word) = Some W_9ea24.
Proof. vm_refl. Qed.
Lemma D_9ea24 : decode_any W_9ea24 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea28 : bv 32 := 0x00f73023.
Lemma F_9ea28 : fetch_word Ubsan.M.loaded_segments (0xa005c : word) = Some W_9ea28.
Proof. vm_refl. Qed.
Lemma D_9ea28 : decode_any W_9ea28 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea2c : bv 32 := 0x04200893.
Lemma F_9ea2c : fetch_word Ubsan.M.loaded_segments (0xa0060 : word) = Some W_9ea2c.
Proof. vm_refl. Qed.
Lemma D_9ea2c : decode_any W_9ea2c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea30 : bv 32 := 0x00090613.
Lemma F_9ea30 : fetch_word Ubsan.M.loaded_segments (0xa0064 : word) = Some W_9ea30.
Proof. vm_refl. Qed.
Lemma D_9ea30 : decode_any W_9ea30 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea34 : bv 32 := 0x00000073.
Lemma F_9ea34 : fetch_word Ubsan.M.loaded_segments (0xa0068 : word) = Some W_9ea34.
Proof. vm_refl. Qed.
Lemma D_9ea34 : decode_any W_9ea34 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9ea34 : is_ecall W_9ea34 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9ea38 : bv 32 := 0xf45fa0ef.
Lemma F_9ea38 : fetch_word Ubsan.M.loaded_segments (0xa006c : word) = Some W_9ea38.
Proof. vm_refl. Qed.
Lemma D_9ea38 : decode_any W_9ea38 = Some (Jal 1 2076484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea3c : bv 32 := 0x000a0993.
Lemma F_9ea3c : fetch_word Ubsan.M.loaded_segments (0xa0070 : word) = Some W_9ea3c.
Proof. vm_refl. Qed.
Lemma D_9ea3c : decode_any W_9ea3c = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea40 : bv 32 := 0xf7650ce3.
Lemma F_9ea40 : fetch_word Ubsan.M.loaded_segments (0xa0074 : word) = Some W_9ea40.
Proof. vm_refl. Qed.
Lemma D_9ea40 : decode_any W_9ea40 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea44 : bv 32 := 0x02054c63.
Lemma F_9ea44 : fetch_word Ubsan.M.loaded_segments (0xa0078 : word) = Some W_9ea44.
Proof. vm_refl. Qed.
Lemma D_9ea44 : decode_any W_9ea44 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea48 : bv 32 := 0x0089b583.
Lemma F_9ea48 : fetch_word Ubsan.M.loaded_segments (0xa007c : word) = Some W_9ea48.
Proof. vm_refl. Qed.
Lemma D_9ea48 : decode_any W_9ea48 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea4c : bv 32 := 0x00a5b633.
Lemma F_9ea4c : fetch_word Ubsan.M.loaded_segments (0xa0080 : word) = Some W_9ea4c.
Proof. vm_refl. Qed.
Lemma D_9ea4c : decode_any W_9ea4c = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea50 : bv 32 := 0x00461a13.
Lemma F_9ea50 : fetch_word Ubsan.M.loaded_segments (0xa0084 : word) = Some W_9ea50.
Proof. vm_refl. Qed.
Lemma D_9ea50 : decode_any W_9ea50 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea54 : bv 32 := 0x01498a33.
Lemma F_9ea54 : fetch_word Ubsan.M.loaded_segments (0xa0088 : word) = Some W_9ea54.
Proof. vm_refl. Qed.
Lemma D_9ea54 : decode_any W_9ea54 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea58 : bv 32 := 0x000a3703.
Lemma F_9ea58 : fetch_word Ubsan.M.loaded_segments (0xa008c : word) = Some W_9ea58.
Proof. vm_refl. Qed.
Lemma D_9ea58 : decode_any W_9ea58 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea5c : bv 32 := 0x40c006b3.
Lemma F_9ea5c : fetch_word Ubsan.M.loaded_segments (0xa0090 : word) = Some W_9ea5c.
Proof. vm_refl. Qed.
Lemma D_9ea5c : decode_any W_9ea5c = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea60 : bv 32 := 0x00b6f6b3.
Lemma F_9ea60 : fetch_word Ubsan.M.loaded_segments (0xa0094 : word) = Some W_9ea60.
Proof. vm_refl. Qed.
Lemma D_9ea60 : decode_any W_9ea60 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea64 : bv 32 := 0x40d506b3.
Lemma F_9ea64 : fetch_word Ubsan.M.loaded_segments (0xa0098 : word) = Some W_9ea64.
Proof. vm_refl. Qed.
Lemma D_9ea64 : decode_any W_9ea64 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea68 : bv 32 := 0x00d70733.
Lemma F_9ea68 : fetch_word Ubsan.M.loaded_segments (0xa009c : word) = Some W_9ea68.
Proof. vm_refl. Qed.
Lemma D_9ea68 : decode_any W_9ea68 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea6c : bv 32 := 0x00ea3023.
Lemma F_9ea6c : fetch_word Ubsan.M.loaded_segments (0xa00a0 : word) = Some W_9ea6c.
Proof. vm_refl. Qed.
Lemma D_9ea6c : decode_any W_9ea6c = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea70 : bv 32 := 0xf8a5fce3.
Lemma F_9ea70 : fetch_word Ubsan.M.loaded_segments (0xa00a4 : word) = Some W_9ea70.
Proof. vm_refl. Qed.
Lemma D_9ea70 : decode_any W_9ea70 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea74 : bv 32 := 0x01800713.
Lemma F_9ea74 : fetch_word Ubsan.M.loaded_segments (0xa00a8 : word) = Some W_9ea74.
Proof. vm_refl. Qed.
Lemma D_9ea74 : decode_any W_9ea74 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea78 : bv 32 := 0xf95ff06f.
Lemma F_9ea78 : fetch_word Ubsan.M.loaded_segments (0xa00ac : word) = Some W_9ea78.
Proof. vm_refl. Qed.
Lemma D_9ea78 : decode_any W_9ea78 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eabc : bv 32 := 0x00008067.
Lemma F_9eabc : fetch_word Ubsan.M.loaded_segments (0xa00f0 : word) = Some W_9eabc.
Proof. vm_refl. Qed.
Lemma D_9eabc : decode_any W_9eabc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f1ec : bv 32 := 0xff010113.
Lemma F_9f1ec : fetch_word Ubsan.M.loaded_segments (0xa0820 : word) = Some W_9f1ec.
Proof. vm_refl. Qed.
Lemma D_9f1ec : decode_any W_9f1ec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f1f0 : bv 32 := 0x00113423.
Lemma F_9f1f0 : fetch_word Ubsan.M.loaded_segments (0xa0824 : word) = Some W_9f1f0.
Proof. vm_refl. Qed.
Lemma D_9f1f0 : decode_any W_9f1f0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f1f4 : bv 32 := 0x00813023.
Lemma F_9f1f4 : fetch_word Ubsan.M.loaded_segments (0xa0828 : word) = Some W_9f1f4.
Proof. vm_refl. Qed.
Lemma D_9f1f4 : decode_any W_9f1f4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f1f8 : bv 32 := 0x0004a517.
Lemma F_9f1f8 : fetch_word Ubsan.M.loaded_segments (0xa082c : word) = Some W_9f1f8.
Proof. vm_refl. Qed.
Lemma D_9f1f8 : decode_any W_9f1f8 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f1fc : bv 32 := 0xf6450413.
Lemma F_9f1fc : fetch_word Ubsan.M.loaded_segments (0xa0830 : word) = Some W_9f1fc.
Proof. vm_refl. Qed.
Lemma D_9f1fc : decode_any W_9f1fc = Some (OpImm ALU_ADD 8 10 3940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f200 : bv 32 := 0x00040513.
Lemma F_9f200 : fetch_word Ubsan.M.loaded_segments (0xa0834 : word) = Some W_9f200.
Proof. vm_refl. Qed.
Lemma D_9f200 : decode_any W_9f200 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f204 : bv 32 := 0x0d90b0ef.
Lemma F_9f204 : fetch_word Ubsan.M.loaded_segments (0xa0838 : word) = Some W_9f204.
Proof. vm_refl. Qed.
Lemma D_9f204 : decode_any W_9f204 = Some (Jal 1 47320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f208 : bv 32 := 0x00840513.
Lemma F_9f208 : fetch_word Ubsan.M.loaded_segments (0xa083c : word) = Some W_9f208.
Proof. vm_refl. Qed.
Lemma D_9f208 : decode_any W_9f208 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f20c : bv 32 := 0x00813083.
Lemma F_9f20c : fetch_word Ubsan.M.loaded_segments (0xa0840 : word) = Some W_9f20c.
Proof. vm_refl. Qed.
Lemma D_9f20c : decode_any W_9f20c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f210 : bv 32 := 0x00013403.
Lemma F_9f210 : fetch_word Ubsan.M.loaded_segments (0xa0844 : word) = Some W_9f210.
Proof. vm_refl. Qed.
Lemma D_9f210 : decode_any W_9f210 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f214 : bv 32 := 0x01010113.
Lemma F_9f214 : fetch_word Ubsan.M.loaded_segments (0xa0848 : word) = Some W_9f214.
Proof. vm_refl. Qed.
Lemma D_9f214 : decode_any W_9f214 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9f218 : bv 32 := 0x00008067.
Lemma F_9f218 : fetch_word Ubsan.M.loaded_segments (0xa084c : word) = Some W_9f218.
Proof. vm_refl. Qed.
Lemma D_9f218 : decode_any W_9f218 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
