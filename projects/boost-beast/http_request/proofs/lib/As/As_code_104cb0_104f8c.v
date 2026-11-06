(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_104cb0 : bv 32 := 0xff010113.
Lemma F_104cb0 : fetch_word Asan.M.loaded_segments (0x104cb0 : word) = Some W_104cb0.
Proof. vm_refl. Qed.
Lemma D_104cb0 : decode_any W_104cb0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cb4 : bv 32 := 0x00113423.
Lemma F_104cb4 : fetch_word Asan.M.loaded_segments (0x104cb4 : word) = Some W_104cb4.
Proof. vm_refl. Qed.
Lemma D_104cb4 : decode_any W_104cb4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cb8 : bv 32 := 0x07852503.
Lemma F_104cb8 : fetch_word Asan.M.loaded_segments (0x104cb8 : word) = Some W_104cb8.
Proof. vm_refl. Qed.
Lemma D_104cb8 : decode_any W_104cb8 = Some (Load SZ4 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cbc : bv 32 := 0xff1ff0ef.
Lemma F_104cbc : fetch_word Asan.M.loaded_segments (0x104cbc : word) = Some W_104cbc.
Proof. vm_refl. Qed.
Lemma D_104cbc : decode_any W_104cbc = Some (Jal 1 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cc0 : bv 32 := 0x03900893.
Lemma F_104cc0 : fetch_word Asan.M.loaded_segments (0x104cc0 : word) = Some W_104cc0.
Proof. vm_refl. Qed.
Lemma D_104cc0 : decode_any W_104cc0 = Some (OpImm ALU_ADD 17 0 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cc4 : bv 32 := 0x00000073.
Lemma F_104cc4 : fetch_word Asan.M.loaded_segments (0x104cc4 : word) = Some W_104cc4.
Proof. vm_refl. Qed.
Lemma D_104cc4 : decode_any W_104cc4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_104cc4 : is_ecall W_104cc4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_104cc8 : bv 32 := 0x93dfa0ef.
Lemma F_104cc8 : fetch_word Asan.M.loaded_segments (0x104cc8 : word) = Some W_104cc8.
Proof. vm_refl. Qed.
Lemma D_104cc8 : decode_any W_104cc8 = Some (Jal 1 2074940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ccc : bv 32 := 0x0005051b.
Lemma F_104ccc : fetch_word Asan.M.loaded_segments (0x104ccc : word) = Some W_104ccc.
Proof. vm_refl. Qed.
Lemma D_104ccc : decode_any W_104ccc = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cd0 : bv 32 := 0x00813083.
Lemma F_104cd0 : fetch_word Asan.M.loaded_segments (0x104cd0 : word) = Some W_104cd0.
Proof. vm_refl. Qed.
Lemma D_104cd0 : decode_any W_104cd0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cd4 : bv 32 := 0x01010113.
Lemma F_104cd4 : fetch_word Asan.M.loaded_segments (0x104cd4 : word) = Some W_104cd4.
Proof. vm_refl. Qed.
Lemma D_104cd4 : decode_any W_104cd4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cd8 : bv 32 := 0x00008067.
Lemma F_104cd8 : fetch_word Asan.M.loaded_segments (0x104cd8 : word) = Some W_104cd8.
Proof. vm_refl. Qed.
Lemma D_104cd8 : decode_any W_104cd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cdc : bv 32 := 0xfb010113.
Lemma F_104cdc : fetch_word Asan.M.loaded_segments (0x104cdc : word) = Some W_104cdc.
Proof. vm_refl. Qed.
Lemma D_104cdc : decode_any W_104cdc = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ce0 : bv 32 := 0x04113423.
Lemma F_104ce0 : fetch_word Asan.M.loaded_segments (0x104ce0 : word) = Some W_104ce0.
Proof. vm_refl. Qed.
Lemma D_104ce0 : decode_any W_104ce0 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ce4 : bv 32 := 0x04813023.
Lemma F_104ce4 : fetch_word Asan.M.loaded_segments (0x104ce4 : word) = Some W_104ce4.
Proof. vm_refl. Qed.
Lemma D_104ce4 : decode_any W_104ce4 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ce8 : bv 32 := 0x02913c23.
Lemma F_104ce8 : fetch_word Asan.M.loaded_segments (0x104ce8 : word) = Some W_104ce8.
Proof. vm_refl. Qed.
Lemma D_104ce8 : decode_any W_104ce8 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cec : bv 32 := 0x03213823.
Lemma F_104cec : fetch_word Asan.M.loaded_segments (0x104cec : word) = Some W_104cec.
Proof. vm_refl. Qed.
Lemma D_104cec : decode_any W_104cec = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cf0 : bv 32 := 0x03313423.
Lemma F_104cf0 : fetch_word Asan.M.loaded_segments (0x104cf0 : word) = Some W_104cf0.
Proof. vm_refl. Qed.
Lemma D_104cf0 : decode_any W_104cf0 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cf4 : bv 32 := 0x00060413.
Lemma F_104cf4 : fetch_word Asan.M.loaded_segments (0x104cf4 : word) = Some W_104cf4.
Proof. vm_refl. Qed.
Lemma D_104cf4 : decode_any W_104cf4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cf8 : bv 32 := 0x00058913.
Lemma F_104cf8 : fetch_word Asan.M.loaded_segments (0x104cf8 : word) = Some W_104cf8.
Proof. vm_refl. Qed.
Lemma D_104cf8 : decode_any W_104cf8 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104cfc : bv 32 := 0x00050493.
Lemma F_104cfc : fetch_word Asan.M.loaded_segments (0x104cfc : word) = Some W_104cfc.
Proof. vm_refl. Qed.
Lemma D_104cfc : decode_any W_104cfc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d00 : bv 32 := 0x00017517.
Lemma F_104d00 : fetch_word Asan.M.loaded_segments (0x104d00 : word) = Some W_104d00.
Proof. vm_refl. Qed.
Lemma D_104d00 : decode_any W_104d00 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d04 : bv 32 := 0x43053983.
Lemma F_104d04 : fetch_word Asan.M.loaded_segments (0x104d04 : word) = Some W_104d04.
Proof. vm_refl. Qed.
Lemma D_104d04 : decode_any W_104d04 = Some (Load SZ8 true 19 10 1072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d08 : bv 32 := 0x0009b503.
Lemma F_104d08 : fetch_word Asan.M.loaded_segments (0x104d08 : word) = Some W_104d08.
Proof. vm_refl. Qed.
Lemma D_104d08 : decode_any W_104d08 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d0c : bv 32 := 0x02a13023.
Lemma F_104d0c : fetch_word Asan.M.loaded_segments (0x104d0c : word) = Some W_104d0c.
Proof. vm_refl. Qed.
Lemma D_104d0c : decode_any W_104d0c = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d10 : bv 32 := 0x0604b603.
Lemma F_104d10 : fetch_word Asan.M.loaded_segments (0x104d10 : word) = Some W_104d10.
Proof. vm_refl. Qed.
Lemma D_104d10 : decode_any W_104d10 = Some (Load SZ8 true 12 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d14 : bv 32 := 0x0584b583.
Lemma F_104d14 : fetch_word Asan.M.loaded_segments (0x104d14 : word) = Some W_104d14.
Proof. vm_refl. Qed.
Lemma D_104d14 : decode_any W_104d14 = Some (Load SZ8 true 11 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d18 : bv 32 := 0x0784a503.
Lemma F_104d18 : fetch_word Asan.M.loaded_segments (0x104d18 : word) = Some W_104d18.
Proof. vm_refl. Qed.
Lemma D_104d18 : decode_any W_104d18 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d1c : bv 32 := 0x00c036b3.
Lemma F_104d1c : fetch_word Asan.M.loaded_segments (0x104d1c : word) = Some W_104d1c.
Proof. vm_refl. Qed.
Lemma D_104d1c : decode_any W_104d1c = Some (Op ALU_SLTU 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d20 : bv 32 := 0x40d406b3.
Lemma F_104d20 : fetch_word Asan.M.loaded_segments (0x104d20 : word) = Some W_104d20.
Proof. vm_refl. Qed.
Lemma D_104d20 : decode_any W_104d20 = Some (Op ALU_SUB 13 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d24 : bv 32 := 0x01213023.
Lemma F_104d24 : fetch_word Asan.M.loaded_segments (0x104d24 : word) = Some W_104d24.
Proof. vm_refl. Qed.
Lemma D_104d24 : decode_any W_104d24 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d28 : bv 32 := 0x00d13423.
Lemma F_104d28 : fetch_word Asan.M.loaded_segments (0x104d28 : word) = Some W_104d28.
Proof. vm_refl. Qed.
Lemma D_104d28 : decode_any W_104d28 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d2c : bv 32 := 0x00b13823.
Lemma F_104d2c : fetch_word Asan.M.loaded_segments (0x104d2c : word) = Some W_104d2c.
Proof. vm_refl. Qed.
Lemma D_104d2c : decode_any W_104d2c = Some (Store SZ8 2 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d30 : bv 32 := 0x00c13c23.
Lemma F_104d30 : fetch_word Asan.M.loaded_segments (0x104d30 : word) = Some W_104d30.
Proof. vm_refl. Qed.
Lemma D_104d30 : decode_any W_104d30 = Some (Store SZ8 2 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d34 : bv 32 := 0x04068c63.
Lemma F_104d34 : fetch_word Asan.M.loaded_segments (0x104d34 : word) = Some W_104d34.
Proof. vm_refl. Qed.
Lemma D_104d34 : decode_any W_104d34 = Some (Branch BC_EQ 13 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d38 : bv 32 := 0x04100893.
Lemma F_104d38 : fetch_word Asan.M.loaded_segments (0x104d38 : word) = Some W_104d38.
Proof. vm_refl. Qed.
Lemma D_104d38 : decode_any W_104d38 = Some (OpImm ALU_ADD 17 0 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d3c : bv 32 := 0x00010593.
Lemma F_104d3c : fetch_word Asan.M.loaded_segments (0x104d3c : word) = Some W_104d3c.
Proof. vm_refl. Qed.
Lemma D_104d3c : decode_any W_104d3c = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d40 : bv 32 := 0x00200613.
Lemma F_104d40 : fetch_word Asan.M.loaded_segments (0x104d40 : word) = Some W_104d40.
Proof. vm_refl. Qed.
Lemma D_104d40 : decode_any W_104d40 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d44 : bv 32 := 0x00000073.
Lemma F_104d44 : fetch_word Asan.M.loaded_segments (0x104d44 : word) = Some W_104d44.
Proof. vm_refl. Qed.
Lemma D_104d44 : decode_any W_104d44 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_104d44 : is_ecall W_104d44 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_104d48 : bv 32 := 0x8bdfa0ef.
Lemma F_104d48 : fetch_word Asan.M.loaded_segments (0x104d48 : word) = Some W_104d48.
Proof. vm_refl. Qed.
Lemma D_104d48 : decode_any W_104d48 = Some (Jal 1 2074812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d4c : bv 32 := 0x04a05863.
Lemma F_104d4c : fetch_word Asan.M.loaded_segments (0x104d4c : word) = Some W_104d4c.
Proof. vm_refl. Qed.
Lemma D_104d4c : decode_any W_104d4c = Some (Branch BC_GE 0 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d50 : bv 32 := 0x00813603.
Lemma F_104d50 : fetch_word Asan.M.loaded_segments (0x104d50 : word) = Some W_104d50.
Proof. vm_refl. Qed.
Lemma D_104d50 : decode_any W_104d50 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d54 : bv 32 := 0x04a67a63.
Lemma F_104d54 : fetch_word Asan.M.loaded_segments (0x104d54 : word) = Some W_104d54.
Proof. vm_refl. Qed.
Lemma D_104d54 : decode_any W_104d54 = Some (Branch BC_GEU 12 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d58 : bv 32 := 0x0584b583.
Lemma F_104d58 : fetch_word Asan.M.loaded_segments (0x104d58 : word) = Some W_104d58.
Proof. vm_refl. Qed.
Lemma D_104d58 : decode_any W_104d58 = Some (Load SZ8 true 11 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d5c : bv 32 := 0x0604b683.
Lemma F_104d5c : fetch_word Asan.M.loaded_segments (0x104d5c : word) = Some W_104d5c.
Proof. vm_refl. Qed.
Lemma D_104d5c : decode_any W_104d5c = Some (Load SZ8 true 13 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d60 : bv 32 := 0x40c50533.
Lemma F_104d60 : fetch_word Asan.M.loaded_segments (0x104d60 : word) = Some W_104d60.
Proof. vm_refl. Qed.
Lemma D_104d60 : decode_any W_104d60 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d64 : bv 32 := 0x00a58533.
Lemma F_104d64 : fetch_word Asan.M.loaded_segments (0x104d64 : word) = Some W_104d64.
Proof. vm_refl. Qed.
Lemma D_104d64 : decode_any W_104d64 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d68 : bv 32 := 0x00b4b423.
Lemma F_104d68 : fetch_word Asan.M.loaded_segments (0x104d68 : word) = Some W_104d68.
Proof. vm_refl. Qed.
Lemma D_104d68 : decode_any W_104d68 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d6c : bv 32 := 0x00a4b823.
Lemma F_104d6c : fetch_word Asan.M.loaded_segments (0x104d6c : word) = Some W_104d6c.
Proof. vm_refl. Qed.
Lemma D_104d6c : decode_any W_104d6c = Some (Store SZ8 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d70 : bv 32 := 0x04068a63.
Lemma F_104d70 : fetch_word Asan.M.loaded_segments (0x104d70 : word) = Some W_104d70.
Proof. vm_refl. Qed.
Lemma D_104d70 : decode_any W_104d70 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d74 : bv 32 := 0x00158513.
Lemma F_104d74 : fetch_word Asan.M.loaded_segments (0x104d74 : word) = Some W_104d74.
Proof. vm_refl. Qed.
Lemma D_104d74 : decode_any W_104d74 = Some (OpImm ALU_ADD 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d78 : bv 32 := 0x00a4b423.
Lemma F_104d78 : fetch_word Asan.M.loaded_segments (0x104d78 : word) = Some W_104d78.
Proof. vm_refl. Qed.
Lemma D_104d78 : decode_any W_104d78 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d7c : bv 32 := 0x0005c503.
Lemma F_104d7c : fetch_word Asan.M.loaded_segments (0x104d7c : word) = Some W_104d7c.
Proof. vm_refl. Qed.
Lemma D_104d7c : decode_any W_104d7c = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d80 : bv 32 := 0x00890933.
Lemma F_104d80 : fetch_word Asan.M.loaded_segments (0x104d80 : word) = Some W_104d80.
Proof. vm_refl. Qed.
Lemma D_104d80 : decode_any W_104d80 = Some (Op ALU_ADD 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d84 : bv 32 := 0xfea90fa3.
Lemma F_104d84 : fetch_word Asan.M.loaded_segments (0x104d84 : word) = Some W_104d84.
Proof. vm_refl. Qed.
Lemma D_104d84 : decode_any W_104d84 = Some (Store SZ1 18 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d88 : bv 32 := 0x03c0006f.
Lemma F_104d88 : fetch_word Asan.M.loaded_segments (0x104d88 : word) = Some W_104d88.
Proof. vm_refl. Qed.
Lemma D_104d88 : decode_any W_104d88 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d8c : bv 32 := 0x03f00893.
Lemma F_104d8c : fetch_word Asan.M.loaded_segments (0x104d8c : word) = Some W_104d8c.
Proof. vm_refl. Qed.
Lemma D_104d8c : decode_any W_104d8c = Some (OpImm ALU_ADD 17 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d90 : bv 32 := 0x00000073.
Lemma F_104d90 : fetch_word Asan.M.loaded_segments (0x104d90 : word) = Some W_104d90.
Proof. vm_refl. Qed.
Lemma D_104d90 : decode_any W_104d90 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_104d90 : is_ecall W_104d90 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_104d94 : bv 32 := 0x871fa0ef.
Lemma F_104d94 : fetch_word Asan.M.loaded_segments (0x104d94 : word) = Some W_104d94.
Proof. vm_refl. Qed.
Lemma D_104d94 : decode_any W_104d94 = Some (Jal 1 2074736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d98 : bv 32 := 0xfaa04ce3.
Lemma F_104d98 : fetch_word Asan.M.loaded_segments (0x104d98 : word) = Some W_104d98.
Proof. vm_refl. Qed.
Lemma D_104d98 : decode_any W_104d98 = Some (Branch BC_LT 0 10 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104d9c : bv 32 := 0x00050a63.
Lemma F_104d9c : fetch_word Asan.M.loaded_segments (0x104d9c : word) = Some W_104d9c.
Proof. vm_refl. Qed.
Lemma D_104d9c : decode_any W_104d9c = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104da0 : bv 32 := 0x02000513.
Lemma F_104da0 : fetch_word Asan.M.loaded_segments (0x104da0 : word) = Some W_104da0.
Proof. vm_refl. Qed.
Lemma D_104da0 : decode_any W_104da0 = Some (OpImm ALU_ADD 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104da4 : bv 32 := 0x0100006f.
Lemma F_104da4 : fetch_word Asan.M.loaded_segments (0x104da4 : word) = Some W_104da4.
Proof. vm_refl. Qed.
Lemma D_104da4 : decode_any W_104da4 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104da8 : bv 32 := 0x00050413.
Lemma F_104da8 : fetch_word Asan.M.loaded_segments (0x104da8 : word) = Some W_104da8.
Proof. vm_refl. Qed.
Lemma D_104da8 : decode_any W_104da8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104dac : bv 32 := 0x0180006f.
Lemma F_104dac : fetch_word Asan.M.loaded_segments (0x104dac : word) = Some W_104dac.
Proof. vm_refl. Qed.
Lemma D_104dac : decode_any W_104dac = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104db0 : bv 32 := 0x01000513.
Lemma F_104db0 : fetch_word Asan.M.loaded_segments (0x104db0 : word) = Some W_104db0.
Proof. vm_refl. Qed.
Lemma D_104db0 : decode_any W_104db0 = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104db4 : bv 32 := 0x00000413.
Lemma F_104db4 : fetch_word Asan.M.loaded_segments (0x104db4 : word) = Some W_104db4.
Proof. vm_refl. Qed.
Lemma D_104db4 : decode_any W_104db4 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104db8 : bv 32 := 0x0004a583.
Lemma F_104db8 : fetch_word Asan.M.loaded_segments (0x104db8 : word) = Some W_104db8.
Proof. vm_refl. Qed.
Lemma D_104db8 : decode_any W_104db8 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104dbc : bv 32 := 0x00a5e533.
Lemma F_104dbc : fetch_word Asan.M.loaded_segments (0x104dbc : word) = Some W_104dbc.
Proof. vm_refl. Qed.
Lemma D_104dbc : decode_any W_104dbc = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104dc0 : bv 32 := 0x00a4a023.
Lemma F_104dc0 : fetch_word Asan.M.loaded_segments (0x104dc0 : word) = Some W_104dc0.
Proof. vm_refl. Qed.
Lemma D_104dc0 : decode_any W_104dc0 = Some (Store SZ4 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104dc4 : bv 32 := 0x0009b503.
Lemma F_104dc4 : fetch_word Asan.M.loaded_segments (0x104dc4 : word) = Some W_104dc4.
Proof. vm_refl. Qed.
Lemma D_104dc4 : decode_any W_104dc4 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104dc8 : bv 32 := 0x02013583.
Lemma F_104dc8 : fetch_word Asan.M.loaded_segments (0x104dc8 : word) = Some W_104dc8.
Proof. vm_refl. Qed.
Lemma D_104dc8 : decode_any W_104dc8 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104dcc : bv 32 := 0x02b51263.
Lemma F_104dcc : fetch_word Asan.M.loaded_segments (0x104dcc : word) = Some W_104dcc.
Proof. vm_refl. Qed.
Lemma D_104dcc : decode_any W_104dcc = Some (Branch BC_NE 10 11 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104dd0 : bv 32 := 0x00040513.
Lemma F_104dd0 : fetch_word Asan.M.loaded_segments (0x104dd0 : word) = Some W_104dd0.
Proof. vm_refl. Qed.
Lemma D_104dd0 : decode_any W_104dd0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104dd4 : bv 32 := 0x04813083.
Lemma F_104dd4 : fetch_word Asan.M.loaded_segments (0x104dd4 : word) = Some W_104dd4.
Proof. vm_refl. Qed.
Lemma D_104dd4 : decode_any W_104dd4 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104dd8 : bv 32 := 0x04013403.
Lemma F_104dd8 : fetch_word Asan.M.loaded_segments (0x104dd8 : word) = Some W_104dd8.
Proof. vm_refl. Qed.
Lemma D_104dd8 : decode_any W_104dd8 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ddc : bv 32 := 0x03813483.
Lemma F_104ddc : fetch_word Asan.M.loaded_segments (0x104ddc : word) = Some W_104ddc.
Proof. vm_refl. Qed.
Lemma D_104ddc : decode_any W_104ddc = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104de0 : bv 32 := 0x03013903.
Lemma F_104de0 : fetch_word Asan.M.loaded_segments (0x104de0 : word) = Some W_104de0.
Proof. vm_refl. Qed.
Lemma D_104de0 : decode_any W_104de0 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104de4 : bv 32 := 0x02813983.
Lemma F_104de4 : fetch_word Asan.M.loaded_segments (0x104de4 : word) = Some W_104de4.
Proof. vm_refl. Qed.
Lemma D_104de4 : decode_any W_104de4 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104de8 : bv 32 := 0x05010113.
Lemma F_104de8 : fetch_word Asan.M.loaded_segments (0x104de8 : word) = Some W_104de8.
Proof. vm_refl. Qed.
Lemma D_104de8 : decode_any W_104de8 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104dec : bv 32 := 0x00008067.
Lemma F_104dec : fetch_word Asan.M.loaded_segments (0x104dec : word) = Some W_104dec.
Proof. vm_refl. Qed.
Lemma D_104dec : decode_any W_104dec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104df0 : bv 32 := 0x9a8fa0ef.
Lemma F_104df0 : fetch_word Asan.M.loaded_segments (0x104df0 : word) = Some W_104df0.
Proof. vm_refl. Qed.
Lemma D_104df0 : decode_any W_104df0 = Some (Jal 1 2073000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104df4 : bv 32 := 0x07852503.
Lemma F_104df4 : fetch_word Asan.M.loaded_segments (0x104df4 : word) = Some W_104df4.
Proof. vm_refl. Qed.
Lemma D_104df4 : decode_any W_104df4 = Some (Load SZ4 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104df8 : bv 32 := 0x5440f06f.
Lemma F_104df8 : fetch_word Asan.M.loaded_segments (0x104df8 : word) = Some W_104df8.
Proof. vm_refl. Qed.
Lemma D_104df8 : decode_any W_104df8 = Some (Jal 0 62788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104dfc : bv 32 := 0xf9010113.
Lemma F_104dfc : fetch_word Asan.M.loaded_segments (0x104dfc : word) = Some W_104dfc.
Proof. vm_refl. Qed.
Lemma D_104dfc : decode_any W_104dfc = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e00 : bv 32 := 0x06113423.
Lemma F_104e00 : fetch_word Asan.M.loaded_segments (0x104e00 : word) = Some W_104e00.
Proof. vm_refl. Qed.
Lemma D_104e00 : decode_any W_104e00 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e04 : bv 32 := 0x06813023.
Lemma F_104e04 : fetch_word Asan.M.loaded_segments (0x104e04 : word) = Some W_104e04.
Proof. vm_refl. Qed.
Lemma D_104e04 : decode_any W_104e04 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e08 : bv 32 := 0x04913c23.
Lemma F_104e08 : fetch_word Asan.M.loaded_segments (0x104e08 : word) = Some W_104e08.
Proof. vm_refl. Qed.
Lemma D_104e08 : decode_any W_104e08 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e0c : bv 32 := 0x05213823.
Lemma F_104e0c : fetch_word Asan.M.loaded_segments (0x104e0c : word) = Some W_104e0c.
Proof. vm_refl. Qed.
Lemma D_104e0c : decode_any W_104e0c = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e10 : bv 32 := 0x05313423.
Lemma F_104e10 : fetch_word Asan.M.loaded_segments (0x104e10 : word) = Some W_104e10.
Proof. vm_refl. Qed.
Lemma D_104e10 : decode_any W_104e10 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e14 : bv 32 := 0x05413023.
Lemma F_104e14 : fetch_word Asan.M.loaded_segments (0x104e14 : word) = Some W_104e14.
Proof. vm_refl. Qed.
Lemma D_104e14 : decode_any W_104e14 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e18 : bv 32 := 0x03513c23.
Lemma F_104e18 : fetch_word Asan.M.loaded_segments (0x104e18 : word) = Some W_104e18.
Proof. vm_refl. Qed.
Lemma D_104e18 : decode_any W_104e18 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e1c : bv 32 := 0x03613823.
Lemma F_104e1c : fetch_word Asan.M.loaded_segments (0x104e1c : word) = Some W_104e1c.
Proof. vm_refl. Qed.
Lemma D_104e1c : decode_any W_104e1c = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e20 : bv 32 := 0x00060413.
Lemma F_104e20 : fetch_word Asan.M.loaded_segments (0x104e20 : word) = Some W_104e20.
Proof. vm_refl. Qed.
Lemma D_104e20 : decode_any W_104e20 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e24 : bv 32 := 0x00050493.
Lemma F_104e24 : fetch_word Asan.M.loaded_segments (0x104e24 : word) = Some W_104e24.
Proof. vm_refl. Qed.
Lemma D_104e24 : decode_any W_104e24 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e28 : bv 32 := 0x00017517.
Lemma F_104e28 : fetch_word Asan.M.loaded_segments (0x104e28 : word) = Some W_104e28.
Proof. vm_refl. Qed.
Lemma D_104e28 : decode_any W_104e28 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e2c : bv 32 := 0x30853a83.
Lemma F_104e2c : fetch_word Asan.M.loaded_segments (0x104e2c : word) = Some W_104e2c.
Proof. vm_refl. Qed.
Lemma D_104e2c : decode_any W_104e2c = Some (Load SZ8 true 21 10 776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e30 : bv 32 := 0x000ab503.
Lemma F_104e30 : fetch_word Asan.M.loaded_segments (0x104e30 : word) = Some W_104e30.
Proof. vm_refl. Qed.
Lemma D_104e30 : decode_any W_104e30 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e34 : bv 32 := 0x02a13423.
Lemma F_104e34 : fetch_word Asan.M.loaded_segments (0x104e34 : word) = Some W_104e34.
Proof. vm_refl. Qed.
Lemma D_104e34 : decode_any W_104e34 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e38 : bv 32 := 0x0284b503.
Lemma F_104e38 : fetch_word Asan.M.loaded_segments (0x104e38 : word) = Some W_104e38.
Proof. vm_refl. Qed.
Lemma D_104e38 : decode_any W_104e38 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e3c : bv 32 := 0x0384b603.
Lemma F_104e3c : fetch_word Asan.M.loaded_segments (0x104e3c : word) = Some W_104e3c.
Proof. vm_refl. Qed.
Lemma D_104e3c : decode_any W_104e3c = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e40 : bv 32 := 0x40c50b33.
Lemma F_104e40 : fetch_word Asan.M.loaded_segments (0x104e40 : word) = Some W_104e40.
Proof. vm_refl. Qed.
Lemma D_104e40 : decode_any W_104e40 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e44 : bv 32 := 0x00c546b3.
Lemma F_104e44 : fetch_word Asan.M.loaded_segments (0x104e44 : word) = Some W_104e44.
Proof. vm_refl. Qed.
Lemma D_104e44 : decode_any W_104e44 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e48 : bv 32 := 0x00c13423.
Lemma F_104e48 : fetch_word Asan.M.loaded_segments (0x104e48 : word) = Some W_104e48.
Proof. vm_refl. Qed.
Lemma D_104e48 : decode_any W_104e48 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e4c : bv 32 := 0x01613823.
Lemma F_104e4c : fetch_word Asan.M.loaded_segments (0x104e4c : word) = Some W_104e4c.
Proof. vm_refl. Qed.
Lemma D_104e4c : decode_any W_104e4c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e50 : bv 32 := 0x00b13c23.
Lemma F_104e50 : fetch_word Asan.M.loaded_segments (0x104e50 : word) = Some W_104e50.
Proof. vm_refl. Qed.
Lemma D_104e50 : decode_any W_104e50 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e54 : bv 32 := 0x02813023.
Lemma F_104e54 : fetch_word Asan.M.loaded_segments (0x104e54 : word) = Some W_104e54.
Proof. vm_refl. Qed.
Lemma D_104e54 : decode_any W_104e54 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e58 : bv 32 := 0x008b0b33.
Lemma F_104e58 : fetch_word Asan.M.loaded_segments (0x104e58 : word) = Some W_104e58.
Proof. vm_refl. Qed.
Lemma D_104e58 : decode_any W_104e58 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e5c : bv 32 := 0x00d03933.
Lemma F_104e5c : fetch_word Asan.M.loaded_segments (0x104e5c : word) = Some W_104e5c.
Proof. vm_refl. Qed.
Lemma D_104e5c : decode_any W_104e5c = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e60 : bv 32 := 0x00c50663.
Lemma F_104e60 : fetch_word Asan.M.loaded_segments (0x104e60 : word) = Some W_104e60.
Proof. vm_refl. Qed.
Lemma D_104e60 : decode_any W_104e60 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e64 : bv 32 := 0x00810993.
Lemma F_104e64 : fetch_word Asan.M.loaded_segments (0x104e64 : word) = Some W_104e64.
Proof. vm_refl. Qed.
Lemma D_104e64 : decode_any W_104e64 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e68 : bv 32 := 0x0080006f.
Lemma F_104e68 : fetch_word Asan.M.loaded_segments (0x104e68 : word) = Some W_104e68.
Proof. vm_refl. Qed.
Lemma D_104e68 : decode_any W_104e68 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e6c : bv 32 := 0x01810993.
Lemma F_104e6c : fetch_word Asan.M.loaded_segments (0x104e6c : word) = Some W_104e6c.
Proof. vm_refl. Qed.
Lemma D_104e6c : decode_any W_104e6c = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e70 : bv 32 := 0x0784a503.
Lemma F_104e70 : fetch_word Asan.M.loaded_segments (0x104e70 : word) = Some W_104e70.
Proof. vm_refl. Qed.
Lemma D_104e70 : decode_any W_104e70 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e74 : bv 32 := 0x00190913.
Lemma F_104e74 : fetch_word Asan.M.loaded_segments (0x104e74 : word) = Some W_104e74.
Proof. vm_refl. Qed.
Lemma D_104e74 : decode_any W_104e74 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e78 : bv 32 := 0x04200893.
Lemma F_104e78 : fetch_word Asan.M.loaded_segments (0x104e78 : word) = Some W_104e78.
Proof. vm_refl. Qed.
Lemma D_104e78 : decode_any W_104e78 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e7c : bv 32 := 0x00098593.
Lemma F_104e7c : fetch_word Asan.M.loaded_segments (0x104e7c : word) = Some W_104e7c.
Proof. vm_refl. Qed.
Lemma D_104e7c : decode_any W_104e7c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e80 : bv 32 := 0x00090613.
Lemma F_104e80 : fetch_word Asan.M.loaded_segments (0x104e80 : word) = Some W_104e80.
Proof. vm_refl. Qed.
Lemma D_104e80 : decode_any W_104e80 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e84 : bv 32 := 0x00000073.
Lemma F_104e84 : fetch_word Asan.M.loaded_segments (0x104e84 : word) = Some W_104e84.
Proof. vm_refl. Qed.
Lemma D_104e84 : decode_any W_104e84 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_104e84 : is_ecall W_104e84 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_104e88 : bv 32 := 0xf7cfa0ef.
Lemma F_104e88 : fetch_word Asan.M.loaded_segments (0x104e88 : word) = Some W_104e88.
Proof. vm_refl. Qed.
Lemma D_104e88 : decode_any W_104e88 = Some (Jal 1 2074492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e8c : bv 32 := 0x09651863.
Lemma F_104e8c : fetch_word Asan.M.loaded_segments (0x104e8c : word) = Some W_104e8c.
Proof. vm_refl. Qed.
Lemma D_104e8c : decode_any W_104e8c = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e90 : bv 32 := 0x0584b503.
Lemma F_104e90 : fetch_word Asan.M.loaded_segments (0x104e90 : word) = Some W_104e90.
Proof. vm_refl. Qed.
Lemma D_104e90 : decode_any W_104e90 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e94 : bv 32 := 0x0604b583.
Lemma F_104e94 : fetch_word Asan.M.loaded_segments (0x104e94 : word) = Some W_104e94.
Proof. vm_refl. Qed.
Lemma D_104e94 : decode_any W_104e94 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e98 : bv 32 := 0x00b505b3.
Lemma F_104e98 : fetch_word Asan.M.loaded_segments (0x104e98 : word) = Some W_104e98.
Proof. vm_refl. Qed.
Lemma D_104e98 : decode_any W_104e98 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104e9c : bv 32 := 0x02b4b023.
Lemma F_104e9c : fetch_word Asan.M.loaded_segments (0x104e9c : word) = Some W_104e9c.
Proof. vm_refl. Qed.
Lemma D_104e9c : decode_any W_104e9c = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ea0 : bv 32 := 0x02a4b423.
Lemma F_104ea0 : fetch_word Asan.M.loaded_segments (0x104ea0 : word) = Some W_104ea0.
Proof. vm_refl. Qed.
Lemma D_104ea0 : decode_any W_104ea0 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ea4 : bv 32 := 0x02a4bc23.
Lemma F_104ea4 : fetch_word Asan.M.loaded_segments (0x104ea4 : word) = Some W_104ea4.
Proof. vm_refl. Qed.
Lemma D_104ea4 : decode_any W_104ea4 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ea8 : bv 32 := 0x00040513.
Lemma F_104ea8 : fetch_word Asan.M.loaded_segments (0x104ea8 : word) = Some W_104ea8.
Proof. vm_refl. Qed.
Lemma D_104ea8 : decode_any W_104ea8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104eac : bv 32 := 0x000ab583.
Lemma F_104eac : fetch_word Asan.M.loaded_segments (0x104eac : word) = Some W_104eac.
Proof. vm_refl. Qed.
Lemma D_104eac : decode_any W_104eac = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104eb0 : bv 32 := 0x02813603.
Lemma F_104eb0 : fetch_word Asan.M.loaded_segments (0x104eb0 : word) = Some W_104eb0.
Proof. vm_refl. Qed.
Lemma D_104eb0 : decode_any W_104eb0 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104eb4 : bv 32 := 0x0cc59a63.
Lemma F_104eb4 : fetch_word Asan.M.loaded_segments (0x104eb4 : word) = Some W_104eb4.
Proof. vm_refl. Qed.
Lemma D_104eb4 : decode_any W_104eb4 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104eb8 : bv 32 := 0x06813083.
Lemma F_104eb8 : fetch_word Asan.M.loaded_segments (0x104eb8 : word) = Some W_104eb8.
Proof. vm_refl. Qed.
Lemma D_104eb8 : decode_any W_104eb8 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ebc : bv 32 := 0x06013403.
Lemma F_104ebc : fetch_word Asan.M.loaded_segments (0x104ebc : word) = Some W_104ebc.
Proof. vm_refl. Qed.
Lemma D_104ebc : decode_any W_104ebc = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ec0 : bv 32 := 0x05813483.
Lemma F_104ec0 : fetch_word Asan.M.loaded_segments (0x104ec0 : word) = Some W_104ec0.
Proof. vm_refl. Qed.
Lemma D_104ec0 : decode_any W_104ec0 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ec4 : bv 32 := 0x05013903.
Lemma F_104ec4 : fetch_word Asan.M.loaded_segments (0x104ec4 : word) = Some W_104ec4.
Proof. vm_refl. Qed.
Lemma D_104ec4 : decode_any W_104ec4 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ec8 : bv 32 := 0x04813983.
Lemma F_104ec8 : fetch_word Asan.M.loaded_segments (0x104ec8 : word) = Some W_104ec8.
Proof. vm_refl. Qed.
Lemma D_104ec8 : decode_any W_104ec8 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ecc : bv 32 := 0x04013a03.
Lemma F_104ecc : fetch_word Asan.M.loaded_segments (0x104ecc : word) = Some W_104ecc.
Proof. vm_refl. Qed.
Lemma D_104ecc : decode_any W_104ecc = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ed0 : bv 32 := 0x03813a83.
Lemma F_104ed0 : fetch_word Asan.M.loaded_segments (0x104ed0 : word) = Some W_104ed0.
Proof. vm_refl. Qed.
Lemma D_104ed0 : decode_any W_104ed0 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ed4 : bv 32 := 0x03013b03.
Lemma F_104ed4 : fetch_word Asan.M.loaded_segments (0x104ed4 : word) = Some W_104ed4.
Proof. vm_refl. Qed.
Lemma D_104ed4 : decode_any W_104ed4 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ed8 : bv 32 := 0x07010113.
Lemma F_104ed8 : fetch_word Asan.M.loaded_segments (0x104ed8 : word) = Some W_104ed8.
Proof. vm_refl. Qed.
Lemma D_104ed8 : decode_any W_104ed8 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104edc : bv 32 := 0x00008067.
Lemma F_104edc : fetch_word Asan.M.loaded_segments (0x104edc : word) = Some W_104edc.
Proof. vm_refl. Qed.
Lemma D_104edc : decode_any W_104edc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ee0 : bv 32 := 0x00800713.
Lemma F_104ee0 : fetch_word Asan.M.loaded_segments (0x104ee0 : word) = Some W_104ee0.
Proof. vm_refl. Qed.
Lemma D_104ee0 : decode_any W_104ee0 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ee4 : bv 32 := 0x000a0593.
Lemma F_104ee4 : fetch_word Asan.M.loaded_segments (0x104ee4 : word) = Some W_104ee4.
Proof. vm_refl. Qed.
Lemma D_104ee4 : decode_any W_104ee4 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ee8 : bv 32 := 0x00e98733.
Lemma F_104ee8 : fetch_word Asan.M.loaded_segments (0x104ee8 : word) = Some W_104ee8.
Proof. vm_refl. Qed.
Lemma D_104ee8 : decode_any W_104ee8 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104eec : bv 32 := 0x00073783.
Lemma F_104eec : fetch_word Asan.M.loaded_segments (0x104eec : word) = Some W_104eec.
Proof. vm_refl. Qed.
Lemma D_104eec : decode_any W_104eec = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ef0 : bv 32 := 0x40ab0b33.
Lemma F_104ef0 : fetch_word Asan.M.loaded_segments (0x104ef0 : word) = Some W_104ef0.
Proof. vm_refl. Qed.
Lemma D_104ef0 : decode_any W_104ef0 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ef4 : bv 32 := 0x0784a503.
Lemma F_104ef4 : fetch_word Asan.M.loaded_segments (0x104ef4 : word) = Some W_104ef4.
Proof. vm_refl. Qed.
Lemma D_104ef4 : decode_any W_104ef4 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104ef8 : bv 32 := 0x40c9093b.
Lemma F_104ef8 : fetch_word Asan.M.loaded_segments (0x104ef8 : word) = Some W_104ef8.
Proof. vm_refl. Qed.
Lemma D_104ef8 : decode_any W_104ef8 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104efc : bv 32 := 0x40d787b3.
Lemma F_104efc : fetch_word Asan.M.loaded_segments (0x104efc : word) = Some W_104efc.
Proof. vm_refl. Qed.
Lemma D_104efc : decode_any W_104efc = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f00 : bv 32 := 0x00f73023.
Lemma F_104f00 : fetch_word Asan.M.loaded_segments (0x104f00 : word) = Some W_104f00.
Proof. vm_refl. Qed.
Lemma D_104f00 : decode_any W_104f00 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f04 : bv 32 := 0x04200893.
Lemma F_104f04 : fetch_word Asan.M.loaded_segments (0x104f04 : word) = Some W_104f04.
Proof. vm_refl. Qed.
Lemma D_104f04 : decode_any W_104f04 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f08 : bv 32 := 0x00090613.
Lemma F_104f08 : fetch_word Asan.M.loaded_segments (0x104f08 : word) = Some W_104f08.
Proof. vm_refl. Qed.
Lemma D_104f08 : decode_any W_104f08 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f0c : bv 32 := 0x00000073.
Lemma F_104f0c : fetch_word Asan.M.loaded_segments (0x104f0c : word) = Some W_104f0c.
Proof. vm_refl. Qed.
Lemma D_104f0c : decode_any W_104f0c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_104f0c : is_ecall W_104f0c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_104f10 : bv 32 := 0xef4fa0ef.
Lemma F_104f10 : fetch_word Asan.M.loaded_segments (0x104f10 : word) = Some W_104f10.
Proof. vm_refl. Qed.
Lemma D_104f10 : decode_any W_104f10 = Some (Jal 1 2074356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f14 : bv 32 := 0x000a0993.
Lemma F_104f14 : fetch_word Asan.M.loaded_segments (0x104f14 : word) = Some W_104f14.
Proof. vm_refl. Qed.
Lemma D_104f14 : decode_any W_104f14 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f18 : bv 32 := 0xf7650ce3.
Lemma F_104f18 : fetch_word Asan.M.loaded_segments (0x104f18 : word) = Some W_104f18.
Proof. vm_refl. Qed.
Lemma D_104f18 : decode_any W_104f18 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f1c : bv 32 := 0x02054c63.
Lemma F_104f1c : fetch_word Asan.M.loaded_segments (0x104f1c : word) = Some W_104f1c.
Proof. vm_refl. Qed.
Lemma D_104f1c : decode_any W_104f1c = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f20 : bv 32 := 0x0089b583.
Lemma F_104f20 : fetch_word Asan.M.loaded_segments (0x104f20 : word) = Some W_104f20.
Proof. vm_refl. Qed.
Lemma D_104f20 : decode_any W_104f20 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f24 : bv 32 := 0x00a5b633.
Lemma F_104f24 : fetch_word Asan.M.loaded_segments (0x104f24 : word) = Some W_104f24.
Proof. vm_refl. Qed.
Lemma D_104f24 : decode_any W_104f24 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f28 : bv 32 := 0x00461a13.
Lemma F_104f28 : fetch_word Asan.M.loaded_segments (0x104f28 : word) = Some W_104f28.
Proof. vm_refl. Qed.
Lemma D_104f28 : decode_any W_104f28 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f2c : bv 32 := 0x01498a33.
Lemma F_104f2c : fetch_word Asan.M.loaded_segments (0x104f2c : word) = Some W_104f2c.
Proof. vm_refl. Qed.
Lemma D_104f2c : decode_any W_104f2c = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f30 : bv 32 := 0x000a3703.
Lemma F_104f30 : fetch_word Asan.M.loaded_segments (0x104f30 : word) = Some W_104f30.
Proof. vm_refl. Qed.
Lemma D_104f30 : decode_any W_104f30 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f34 : bv 32 := 0x40c006b3.
Lemma F_104f34 : fetch_word Asan.M.loaded_segments (0x104f34 : word) = Some W_104f34.
Proof. vm_refl. Qed.
Lemma D_104f34 : decode_any W_104f34 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f38 : bv 32 := 0x00b6f6b3.
Lemma F_104f38 : fetch_word Asan.M.loaded_segments (0x104f38 : word) = Some W_104f38.
Proof. vm_refl. Qed.
Lemma D_104f38 : decode_any W_104f38 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f3c : bv 32 := 0x40d506b3.
Lemma F_104f3c : fetch_word Asan.M.loaded_segments (0x104f3c : word) = Some W_104f3c.
Proof. vm_refl. Qed.
Lemma D_104f3c : decode_any W_104f3c = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f40 : bv 32 := 0x00d70733.
Lemma F_104f40 : fetch_word Asan.M.loaded_segments (0x104f40 : word) = Some W_104f40.
Proof. vm_refl. Qed.
Lemma D_104f40 : decode_any W_104f40 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f44 : bv 32 := 0x00ea3023.
Lemma F_104f44 : fetch_word Asan.M.loaded_segments (0x104f44 : word) = Some W_104f44.
Proof. vm_refl. Qed.
Lemma D_104f44 : decode_any W_104f44 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f48 : bv 32 := 0xf8a5fce3.
Lemma F_104f48 : fetch_word Asan.M.loaded_segments (0x104f48 : word) = Some W_104f48.
Proof. vm_refl. Qed.
Lemma D_104f48 : decode_any W_104f48 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f4c : bv 32 := 0x01800713.
Lemma F_104f4c : fetch_word Asan.M.loaded_segments (0x104f4c : word) = Some W_104f4c.
Proof. vm_refl. Qed.
Lemma D_104f4c : decode_any W_104f4c = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f50 : bv 32 := 0xf95ff06f.
Lemma F_104f50 : fetch_word Asan.M.loaded_segments (0x104f50 : word) = Some W_104f50.
Proof. vm_refl. Qed.
Lemma D_104f50 : decode_any W_104f50 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f54 : bv 32 := 0x00000513.
Lemma F_104f54 : fetch_word Asan.M.loaded_segments (0x104f54 : word) = Some W_104f54.
Proof. vm_refl. Qed.
Lemma D_104f54 : decode_any W_104f54 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f58 : bv 32 := 0x0004a583.
Lemma F_104f58 : fetch_word Asan.M.loaded_segments (0x104f58 : word) = Some W_104f58.
Proof. vm_refl. Qed.
Lemma D_104f58 : decode_any W_104f58 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f5c : bv 32 := 0x0009091b.
Lemma F_104f5c : fetch_word Asan.M.loaded_segments (0x104f5c : word) = Some W_104f5c.
Proof. vm_refl. Qed.
Lemma D_104f5c : decode_any W_104f5c = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f60 : bv 32 := 0x00200613.
Lemma F_104f60 : fetch_word Asan.M.loaded_segments (0x104f60 : word) = Some W_104f60.
Proof. vm_refl. Qed.
Lemma D_104f60 : decode_any W_104f60 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f64 : bv 32 := 0x0205e593.
Lemma F_104f64 : fetch_word Asan.M.loaded_segments (0x104f64 : word) = Some W_104f64.
Proof. vm_refl. Qed.
Lemma D_104f64 : decode_any W_104f64 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f68 : bv 32 := 0x00b4a023.
Lemma F_104f68 : fetch_word Asan.M.loaded_segments (0x104f68 : word) = Some W_104f68.
Proof. vm_refl. Qed.
Lemma D_104f68 : decode_any W_104f68 = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f6c : bv 32 := 0x0204b023.
Lemma F_104f6c : fetch_word Asan.M.loaded_segments (0x104f6c : word) = Some W_104f6c.
Proof. vm_refl. Qed.
Lemma D_104f6c : decode_any W_104f6c = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f70 : bv 32 := 0x0204b423.
Lemma F_104f70 : fetch_word Asan.M.loaded_segments (0x104f70 : word) = Some W_104f70.
Proof. vm_refl. Qed.
Lemma D_104f70 : decode_any W_104f70 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f74 : bv 32 := 0x0204bc23.
Lemma F_104f74 : fetch_word Asan.M.loaded_segments (0x104f74 : word) = Some W_104f74.
Proof. vm_refl. Qed.
Lemma D_104f74 : decode_any W_104f74 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f78 : bv 32 := 0xf2c90ae3.
Lemma F_104f78 : fetch_word Asan.M.loaded_segments (0x104f78 : word) = Some W_104f78.
Proof. vm_refl. Qed.
Lemma D_104f78 : decode_any W_104f78 = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f7c : bv 32 := 0x0089b503.
Lemma F_104f7c : fetch_word Asan.M.loaded_segments (0x104f7c : word) = Some W_104f7c.
Proof. vm_refl. Qed.
Lemma D_104f7c : decode_any W_104f7c = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f80 : bv 32 := 0x40a40533.
Lemma F_104f80 : fetch_word Asan.M.loaded_segments (0x104f80 : word) = Some W_104f80.
Proof. vm_refl. Qed.
Lemma D_104f80 : decode_any W_104f80 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f84 : bv 32 := 0xf29ff06f.
Lemma F_104f84 : fetch_word Asan.M.loaded_segments (0x104f84 : word) = Some W_104f84.
Proof. vm_refl. Qed.
Lemma D_104f84 : decode_any W_104f84 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_104f88 : bv 32 := 0x810fa0ef.
Lemma F_104f88 : fetch_word Asan.M.loaded_segments (0x104f88 : word) = Some W_104f88.
Proof. vm_refl. Qed.
Lemma D_104f88 : decode_any W_104f88 = Some (Jal 1 2072592, 4%Z).
Proof. vm_refl. Qed.
