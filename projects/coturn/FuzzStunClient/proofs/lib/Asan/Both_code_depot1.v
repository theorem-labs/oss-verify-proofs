(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_74cf4 : bv 32 := 0x00058613.
Lemma F_74cf4 : fetch_word AsanUbsan.M.loaded_segments (0x74cf4 : word) = Some W_74cf4.
Proof. vm_refl. Qed.
Lemma D_74cf4 : decode_any W_74cf4 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74cf8 : bv 32 := 0x0011f597.
Lemma F_74cf8 : fetch_word AsanUbsan.M.loaded_segments (0x74cf8 : word) = Some W_74cf8.
Proof. vm_refl. Qed.
Lemma D_74cf8 : decode_any W_74cf8 = Some (Auipc 11 287, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74cfc : bv 32 := 0xda058593.
Lemma F_74cfc : fetch_word AsanUbsan.M.loaded_segments (0x74cfc : word) = Some W_74cfc.
Proof. vm_refl. Qed.
Lemma D_74cfc : decode_any W_74cfc = Some (OpImm ALU_ADD 11 11 3488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d00 : bv 32 := 0x00050693.
Lemma F_74d00 : fetch_word AsanUbsan.M.loaded_segments (0x74d00 : word) = Some W_74d00.
Proof. vm_refl. Qed.
Lemma D_74d00 : decode_any W_74d00 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d04 : bv 32 := 0x00058513.
Lemma F_74d04 : fetch_word AsanUbsan.M.loaded_segments (0x74d04 : word) = Some W_74d04.
Proof. vm_refl. Qed.
Lemma D_74d04 : decode_any W_74d04 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d08 : bv 32 := 0x00068593.
Lemma F_74d08 : fetch_word AsanUbsan.M.loaded_segments (0x74d08 : word) = Some W_74d08.
Proof. vm_refl. Qed.
Lemma D_74d08 : decode_any W_74d08 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d0c : bv 32 := 0x00000693.
Lemma F_74d0c : fetch_word AsanUbsan.M.loaded_segments (0x74d0c : word) = Some W_74d0c.
Proof. vm_refl. Qed.
Lemma D_74d0c : decode_any W_74d0c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d10 : bv 32 := 0x0040006f.
Lemma F_74d10 : fetch_word AsanUbsan.M.loaded_segments (0x74d10 : word) = Some W_74d10.
Proof. vm_refl. Qed.
Lemma D_74d10 : decode_any W_74d10 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d14 : bv 32 := 0xf9010113.
Lemma F_74d14 : fetch_word AsanUbsan.M.loaded_segments (0x74d14 : word) = Some W_74d14.
Proof. vm_refl. Qed.
Lemma D_74d14 : decode_any W_74d14 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d18 : bv 32 := 0x06113423.
Lemma F_74d18 : fetch_word AsanUbsan.M.loaded_segments (0x74d18 : word) = Some W_74d18.
Proof. vm_refl. Qed.
Lemma D_74d18 : decode_any W_74d18 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d1c : bv 32 := 0x06813023.
Lemma F_74d1c : fetch_word AsanUbsan.M.loaded_segments (0x74d1c : word) = Some W_74d1c.
Proof. vm_refl. Qed.
Lemma D_74d1c : decode_any W_74d1c = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d20 : bv 32 := 0x04913c23.
Lemma F_74d20 : fetch_word AsanUbsan.M.loaded_segments (0x74d20 : word) = Some W_74d20.
Proof. vm_refl. Qed.
Lemma D_74d20 : decode_any W_74d20 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d24 : bv 32 := 0x05213823.
Lemma F_74d24 : fetch_word AsanUbsan.M.loaded_segments (0x74d24 : word) = Some W_74d24.
Proof. vm_refl. Qed.
Lemma D_74d24 : decode_any W_74d24 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d28 : bv 32 := 0x05313423.
Lemma F_74d28 : fetch_word AsanUbsan.M.loaded_segments (0x74d28 : word) = Some W_74d28.
Proof. vm_refl. Qed.
Lemma D_74d28 : decode_any W_74d28 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d2c : bv 32 := 0x05413023.
Lemma F_74d2c : fetch_word AsanUbsan.M.loaded_segments (0x74d2c : word) = Some W_74d2c.
Proof. vm_refl. Qed.
Lemma D_74d2c : decode_any W_74d2c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d30 : bv 32 := 0x03513c23.
Lemma F_74d30 : fetch_word AsanUbsan.M.loaded_segments (0x74d30 : word) = Some W_74d30.
Proof. vm_refl. Qed.
Lemma D_74d30 : decode_any W_74d30 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d34 : bv 32 := 0x03613823.
Lemma F_74d34 : fetch_word AsanUbsan.M.loaded_segments (0x74d34 : word) = Some W_74d34.
Proof. vm_refl. Qed.
Lemma D_74d34 : decode_any W_74d34 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d38 : bv 32 := 0x03713423.
Lemma F_74d38 : fetch_word AsanUbsan.M.loaded_segments (0x74d38 : word) = Some W_74d38.
Proof. vm_refl. Qed.
Lemma D_74d38 : decode_any W_74d38 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d3c : bv 32 := 0x03813023.
Lemma F_74d3c : fetch_word AsanUbsan.M.loaded_segments (0x74d3c : word) = Some W_74d3c.
Proof. vm_refl. Qed.
Lemma D_74d3c : decode_any W_74d3c = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d40 : bv 32 := 0x01913c23.
Lemma F_74d40 : fetch_word AsanUbsan.M.loaded_segments (0x74d40 : word) = Some W_74d40.
Proof. vm_refl. Qed.
Lemma D_74d40 : decode_any W_74d40 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d44 : bv 32 := 0x00068413.
Lemma F_74d44 : fetch_word AsanUbsan.M.loaded_segments (0x74d44 : word) = Some W_74d44.
Proof. vm_refl. Qed.
Lemma D_74d44 : decode_any W_74d44 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d48 : bv 32 := 0x00050493.
Lemma F_74d48 : fetch_word AsanUbsan.M.loaded_segments (0x74d48 : word) = Some W_74d48.
Proof. vm_refl. Qed.
Lemma D_74d48 : decode_any W_74d48 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d4c : bv 32 := 0x00b13423.
Lemma F_74d4c : fetch_word AsanUbsan.M.loaded_segments (0x74d4c : word) = Some W_74d4c.
Proof. vm_refl. Qed.
Lemma D_74d4c : decode_any W_74d4c = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d50 : bv 32 := 0x00c13823.
Lemma F_74d50 : fetch_word AsanUbsan.M.loaded_segments (0x74d50 : word) = Some W_74d50.
Proof. vm_refl. Qed.
Lemma D_74d50 : decode_any W_74d50 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d54 : bv 32 := 0x00068463.
Lemma F_74d54 : fetch_word AsanUbsan.M.loaded_segments (0x74d54 : word) = Some W_74d54.
Proof. vm_refl. Qed.
Lemma D_74d54 : decode_any W_74d54 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d58 : bv 32 := 0x00040023.
Lemma F_74d58 : fetch_word AsanUbsan.M.loaded_segments (0x74d58 : word) = Some W_74d58.
Proof. vm_refl. Qed.
Lemma D_74d58 : decode_any W_74d58 = Some (Store SZ1 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d5c : bv 32 := 0x0006069b.
Lemma F_74d5c : fetch_word AsanUbsan.M.loaded_segments (0x74d5c : word) = Some W_74d5c.
Proof. vm_refl. Qed.
Lemma D_74d5c : decode_any W_74d5c = Some (OpImm32 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d60 : bv 32 := 0x00000513.
Lemma F_74d60 : fetch_word AsanUbsan.M.loaded_segments (0x74d60 : word) = Some W_74d60.
Proof. vm_refl. Qed.
Lemma D_74d60 : decode_any W_74d60 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d64 : bv 32 := 0x1c068a63.
Lemma F_74d64 : fetch_word AsanUbsan.M.loaded_segments (0x74d64 : word) = Some W_74d64.
Proof. vm_refl. Qed.
Lemma D_74d64 : decode_any W_74d64 = Some (Branch BC_EQ 13 0 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d68 : bv 32 := 0x1c058863.
Lemma F_74d68 : fetch_word AsanUbsan.M.loaded_segments (0x74d68 : word) = Some W_74d68.
Proof. vm_refl. Qed.
Lemma D_74d68 : decode_any W_74d68 = Some (Branch BC_EQ 11 0 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d6c : bv 32 := 0x02065693.
Lemma F_74d6c : fetch_word AsanUbsan.M.loaded_segments (0x74d6c : word) = Some W_74d6c.
Proof. vm_refl. Qed.
Lemma D_74d6c : decode_any W_74d6c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d70 : bv 32 := 0xfff00513.
Lemma F_74d70 : fetch_word AsanUbsan.M.loaded_segments (0x74d70 : word) = Some W_74d70.
Proof. vm_refl. Qed.
Lemma D_74d70 : decode_any W_74d70 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d74 : bv 32 := 0xfff9b717.
Lemma F_74d74 : fetch_word AsanUbsan.M.loaded_segments (0x74d74 : word) = Some W_74d74.
Proof. vm_refl. Qed.
Lemma D_74d74 : decode_any W_74d74 = Some (Auipc 14 1048475, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d78 : bv 32 := 0xfff9b797.
Lemma F_74d78 : fetch_word AsanUbsan.M.loaded_segments (0x74d78 : word) = Some W_74d78.
Proof. vm_refl. Qed.
Lemma D_74d78 : decode_any W_74d78 = Some (Auipc 15 1048475, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d7c : bv 32 := 0x02055513.
Lemma F_74d7c : fetch_word AsanUbsan.M.loaded_segments (0x74d7c : word) = Some W_74d7c.
Proof. vm_refl. Qed.
Lemma D_74d7c : decode_any W_74d7c = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d80 : bv 32 := 0x5987b783.
Lemma F_74d80 : fetch_word AsanUbsan.M.loaded_segments (0x74d80 : word) = Some W_74d80.
Proof. vm_refl. Qed.
Lemma D_74d80 : decode_any W_74d80 = Some (Load SZ8 true 15 15 1432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d84 : bv 32 := 0x00a67633.
Lemma F_74d84 : fetch_word AsanUbsan.M.loaded_segments (0x74d84 : word) = Some W_74d84.
Proof. vm_refl. Qed.
Lemma D_74d84 : decode_any W_74d84 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d88 : bv 32 := 0xfff9b517.
Lemma F_74d88 : fetch_word AsanUbsan.M.loaded_segments (0x74d88 : word) = Some W_74d88.
Proof. vm_refl. Qed.
Lemma D_74d88 : decode_any W_74d88 = Some (Auipc 10 1048475, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d8c : bv 32 := 0x62853803.
Lemma F_74d8c : fetch_word AsanUbsan.M.loaded_segments (0x74d8c : word) = Some W_74d8c.
Proof. vm_refl. Qed.
Lemma D_74d8c : decode_any W_74d8c = Some (Load SZ8 true 16 10 1576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d90 : bv 32 := 0x57473503.
Lemma F_74d90 : fetch_word AsanUbsan.M.loaded_segments (0x74d90 : word) = Some W_74d90.
Proof. vm_refl. Qed.
Lemma D_74d90 : decode_any W_74d90 = Some (Load SZ8 true 10 14 1396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d94 : bv 32 := 0x02f60733.
Lemma F_74d94 : fetch_word AsanUbsan.M.loaded_segments (0x74d94 : word) = Some W_74d94.
Proof. vm_refl. Qed.
Lemma D_74d94 : decode_any W_74d94 = Some (Mul M_MUL 14 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d98 : bv 32 := 0x00361793.
Lemma F_74d98 : fetch_word AsanUbsan.M.loaded_segments (0x74d98 : word) = Some W_74d98.
Proof. vm_refl. Qed.
Lemma D_74d98 : decode_any W_74d98 = Some (ShiftImm ALU_SLL 15 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74d9c : bv 32 := 0x01074633.
Lemma F_74d9c : fetch_word AsanUbsan.M.loaded_segments (0x74d9c : word) = Some W_74d9c.
Proof. vm_refl. Qed.
Lemma D_74d9c : decode_any W_74d9c = Some (Op ALU_XOR 12 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74da0 : bv 32 := 0x00f58733.
Lemma F_74da0 : fetch_word AsanUbsan.M.loaded_segments (0x74da0 : word) = Some W_74da0.
Proof. vm_refl. Qed.
Lemma D_74da0 : decode_any W_74da0 = Some (Op ALU_ADD 14 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74da4 : bv 32 := 0x0005b783.
Lemma F_74da4 : fetch_word AsanUbsan.M.loaded_segments (0x74da4 : word) = Some W_74da4.
Proof. vm_refl. Qed.
Lemma D_74da4 : decode_any W_74da4 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74da8 : bv 32 := 0x00858593.
Lemma F_74da8 : fetch_word AsanUbsan.M.loaded_segments (0x74da8 : word) = Some W_74da8.
Proof. vm_refl. Qed.
Lemma D_74da8 : decode_any W_74da8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74dac : bv 32 := 0x02a787b3.
Lemma F_74dac : fetch_word AsanUbsan.M.loaded_segments (0x74dac : word) = Some W_74dac.
Proof. vm_refl. Qed.
Lemma D_74dac : decode_any W_74dac = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74db0 : bv 32 := 0x02f7d813.
Lemma F_74db0 : fetch_word AsanUbsan.M.loaded_segments (0x74db0 : word) = Some W_74db0.
Proof. vm_refl. Qed.
Lemma D_74db0 : decode_any W_74db0 = Some (ShiftImm ALU_SRL 16 15 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74db4 : bv 32 := 0x00f847b3.
Lemma F_74db4 : fetch_word AsanUbsan.M.loaded_segments (0x74db4 : word) = Some W_74db4.
Proof. vm_refl. Qed.
Lemma D_74db4 : decode_any W_74db4 = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74db8 : bv 32 := 0x02a787b3.
Lemma F_74db8 : fetch_word AsanUbsan.M.loaded_segments (0x74db8 : word) = Some W_74db8.
Proof. vm_refl. Qed.
Lemma D_74db8 : decode_any W_74db8 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74dbc : bv 32 := 0x00c7c633.
Lemma F_74dbc : fetch_word AsanUbsan.M.loaded_segments (0x74dbc : word) = Some W_74dbc.
Proof. vm_refl. Qed.
Lemma D_74dbc : decode_any W_74dbc = Some (Op ALU_XOR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74dc0 : bv 32 := 0x02a60633.
Lemma F_74dc0 : fetch_word AsanUbsan.M.loaded_segments (0x74dc0 : word) = Some W_74dc0.
Proof. vm_refl. Qed.
Lemma D_74dc0 : decode_any W_74dc0 = Some (Mul M_MUL 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74dc4 : bv 32 := 0xfee590e3.
Lemma F_74dc4 : fetch_word AsanUbsan.M.loaded_segments (0x74dc4 : word) = Some W_74dc4.
Proof. vm_refl. Qed.
Lemma D_74dc4 : decode_any W_74dc4 = Some (Branch BC_NE 11 14 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74dc8 : bv 32 := 0x00010b37.
Lemma F_74dc8 : fetch_word AsanUbsan.M.loaded_segments (0x74dc8 : word) = Some W_74dc8.
Proof. vm_refl. Qed.
Lemma D_74dc8 : decode_any W_74dc8 = Some (Lui 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74dcc : bv 32 := 0x80000bb7.
Lemma F_74dcc : fetch_word AsanUbsan.M.loaded_segments (0x74dcc : word) = Some W_74dcc.
Proof. vm_refl. Qed.
Lemma D_74dcc : decode_any W_74dcc = Some (Lui 23 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74dd0 : bv 32 := 0x02a685b3.
Lemma F_74dd0 : fetch_word AsanUbsan.M.loaded_segments (0x74dd0 : word) = Some W_74dd0.
Proof. vm_refl. Qed.
Lemma D_74dd0 : decode_any W_74dd0 = Some (Mul M_MUL 11 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74dd4 : bv 32 := 0x004006b7.
Lemma F_74dd4 : fetch_word AsanUbsan.M.loaded_segments (0x74dd4 : word) = Some W_74dd4.
Proof. vm_refl. Qed.
Lemma D_74dd4 : decode_any W_74dd4 = Some (Lui 13 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74dd8 : bv 32 := 0xfffb0b1b.
Lemma F_74dd8 : fetch_word AsanUbsan.M.loaded_segments (0x74dd8 : word) = Some W_74dd8.
Proof. vm_refl. Qed.
Lemma D_74dd8 : decode_any W_74dd8 = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ddc : bv 32 := 0xfffb8b9b.
Lemma F_74ddc : fetch_word AsanUbsan.M.loaded_segments (0x74ddc : word) = Some W_74ddc.
Proof. vm_refl. Qed.
Lemma D_74ddc : decode_any W_74ddc = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74de0 : bv 32 := 0x02f5d713.
Lemma F_74de0 : fetch_word AsanUbsan.M.loaded_segments (0x74de0 : word) = Some W_74de0.
Proof. vm_refl. Qed.
Lemma D_74de0 : decode_any W_74de0 = Some (ShiftImm ALU_SRL 14 11 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74de4 : bv 32 := 0x00b745b3.
Lemma F_74de4 : fetch_word AsanUbsan.M.loaded_segments (0x74de4 : word) = Some W_74de4.
Proof. vm_refl. Qed.
Lemma D_74de4 : decode_any W_74de4 = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74de8 : bv 32 := 0x02a585b3.
Lemma F_74de8 : fetch_word AsanUbsan.M.loaded_segments (0x74de8 : word) = Some W_74de8.
Proof. vm_refl. Qed.
Lemma D_74de8 : decode_any W_74de8 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74dec : bv 32 := 0x00c5c5b3.
Lemma F_74dec : fetch_word AsanUbsan.M.loaded_segments (0x74dec : word) = Some W_74dec.
Proof. vm_refl. Qed.
Lemma D_74dec : decode_any W_74dec = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74df0 : bv 32 := 0x02a585b3.
Lemma F_74df0 : fetch_word AsanUbsan.M.loaded_segments (0x74df0 : word) = Some W_74df0.
Proof. vm_refl. Qed.
Lemma D_74df0 : decode_any W_74df0 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74df4 : bv 32 := 0x02f5d613.
Lemma F_74df4 : fetch_word AsanUbsan.M.loaded_segments (0x74df4 : word) = Some W_74df4.
Proof. vm_refl. Qed.
Lemma D_74df4 : decode_any W_74df4 = Some (ShiftImm ALU_SRL 12 11 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74df8 : bv 32 := 0x00b645b3.
Lemma F_74df8 : fetch_word AsanUbsan.M.loaded_segments (0x74df8 : word) = Some W_74df8.
Proof. vm_refl. Qed.
Lemma D_74df8 : decode_any W_74df8 = Some (Op ALU_XOR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74dfc : bv 32 := 0x02a58533.
Lemma F_74dfc : fetch_word AsanUbsan.M.loaded_segments (0x74dfc : word) = Some W_74dfc.
Proof. vm_refl. Qed.
Lemma D_74dfc : decode_any W_74dfc = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e00 : bv 32 := 0x02f55593.
Lemma F_74e00 : fetch_word AsanUbsan.M.loaded_segments (0x74e00 : word) = Some W_74e00.
Proof. vm_refl. Qed.
Lemma D_74e00 : decode_any W_74e00 = Some (ShiftImm ALU_SRL 11 10 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e04 : bv 32 := 0x00a5c9b3.
Lemma F_74e04 : fetch_word AsanUbsan.M.loaded_segments (0x74e04 : word) = Some W_74e04.
Proof. vm_refl. Qed.
Lemma D_74e04 : decode_any W_74e04 = Some (Op ALU_XOR 19 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e08 : bv 32 := 0x02c99513.
Lemma F_74e08 : fetch_word AsanUbsan.M.loaded_segments (0x74e08 : word) = Some W_74e08.
Proof. vm_refl. Qed.
Lemma D_74e08 : decode_any W_74e08 = Some (ShiftImm ALU_SLL 10 19 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e0c : bv 32 := 0x02a55513.
Lemma F_74e0c : fetch_word AsanUbsan.M.loaded_segments (0x74e0c : word) = Some W_74e0c.
Proof. vm_refl. Qed.
Lemma D_74e0c : decode_any W_74e0c = Some (ShiftImm ALU_SRL 10 10 42, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e10 : bv 32 := 0x00a48933.
Lemma F_74e10 : fetch_word AsanUbsan.M.loaded_segments (0x74e10 : word) = Some W_74e10.
Proof. vm_refl. Qed.
Lemma D_74e10 : decode_any W_74e10 = Some (Op ALU_ADD 18 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e14 : bv 32 := 0x00092503.
Lemma F_74e14 : fetch_word AsanUbsan.M.loaded_segments (0x74e14 : word) = Some W_74e14.
Proof. vm_refl. Qed.
Lemma D_74e14 : decode_any W_74e14 = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e18 : bv 32 := 0x01068c1b.
Lemma F_74e18 : fetch_word AsanUbsan.M.loaded_segments (0x74e18 : word) = Some W_74e18.
Proof. vm_refl. Qed.
Lemma D_74e18 : decode_any W_74e18 = Some (OpImm32 24 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e1c : bv 32 := 0x01848c33.
Lemma F_74e1c : fetch_word AsanUbsan.M.loaded_segments (0x74e1c : word) = Some W_74e1c.
Proof. vm_refl. Qed.
Lemma D_74e1c : decode_any W_74e1c = Some (Op ALU_ADD 24 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e20 : bv 32 := 0x0230000f.
Lemma F_74e20 : fetch_word AsanUbsan.M.loaded_segments (0x74e20 : word) = Some W_74e20.
Proof. vm_refl. Qed.
Lemma D_74e20 : decode_any W_74e20 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e24 : bv 32 := 0x01757cb3.
Lemma F_74e24 : fetch_word AsanUbsan.M.loaded_segments (0x74e24 : word) = Some W_74e24.
Proof. vm_refl. Qed.
Lemma D_74e24 : decode_any W_74e24 = Some (Op ALU_AND 25 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e28 : bv 32 := 0x0086869b.
Lemma F_74e28 : fetch_word AsanUbsan.M.loaded_segments (0x74e28 : word) = Some W_74e28.
Proof. vm_refl. Qed.
Lemma D_74e28 : decode_any W_74e28 = Some (OpImm32 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e2c : bv 32 := 0x00d48a33.
Lemma F_74e2c : fetch_word AsanUbsan.M.loaded_segments (0x74e2c : word) = Some W_74e2c.
Proof. vm_refl. Qed.
Lemma D_74e2c : decode_any W_74e2c = Some (Op ALU_ADD 20 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e30 : bv 32 := 0x000c8593.
Lemma F_74e30 : fetch_word AsanUbsan.M.loaded_segments (0x74e30 : word) = Some W_74e30.
Proof. vm_refl. Qed.
Lemma D_74e30 : decode_any W_74e30 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e34 : bv 32 := 0x04058c63.
Lemma F_74e34 : fetch_word AsanUbsan.M.loaded_segments (0x74e34 : word) = Some W_74e34.
Proof. vm_refl. Qed.
Lemma D_74e34 : decode_any W_74e34 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e38 : bv 32 := 0x00058513.
Lemma F_74e38 : fetch_word AsanUbsan.M.loaded_segments (0x74e38 : word) = Some W_74e38.
Proof. vm_refl. Qed.
Lemma D_74e38 : decode_any W_74e38 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e3c : bv 32 := 0x0105d59b.
Lemma F_74e3c : fetch_word AsanUbsan.M.loaded_segments (0x74e3c : word) = Some W_74e3c.
Proof. vm_refl. Qed.
Lemma D_74e3c : decode_any W_74e3c = Some (ShiftImm32 ALU_SRL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e40 : bv 32 := 0x00359613.
Lemma F_74e40 : fetch_word AsanUbsan.M.loaded_segments (0x74e40 : word) = Some W_74e40.
Proof. vm_refl. Qed.
Lemma D_74e40 : decode_any W_74e40 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e44 : bv 32 := 0x00cc0633.
Lemma F_74e44 : fetch_word AsanUbsan.M.loaded_segments (0x74e44 : word) = Some W_74e44.
Proof. vm_refl. Qed.
Lemma D_74e44 : decode_any W_74e44 = Some (Op ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e48 : bv 32 := 0x00063603.
Lemma F_74e48 : fetch_word AsanUbsan.M.loaded_segments (0x74e48 : word) = Some W_74e48.
Proof. vm_refl. Qed.
Lemma D_74e48 : decode_any W_74e48 = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e4c : bv 32 := 0x02060463.
Lemma F_74e4c : fetch_word AsanUbsan.M.loaded_segments (0x74e4c : word) = Some W_74e4c.
Proof. vm_refl. Qed.
Lemma D_74e4c : decode_any W_74e4c = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e50 : bv 32 := 0x02051593.
Lemma F_74e50 : fetch_word AsanUbsan.M.loaded_segments (0x74e50 : word) = Some W_74e50.
Proof. vm_refl. Qed.
Lemma D_74e50 : decode_any W_74e50 = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e54 : bv 32 := 0x0205d593.
Lemma F_74e54 : fetch_word AsanUbsan.M.loaded_segments (0x74e54 : word) = Some W_74e54.
Proof. vm_refl. Qed.
Lemma D_74e54 : decode_any W_74e54 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e58 : bv 32 := 0x0165f5b3.
Lemma F_74e58 : fetch_word AsanUbsan.M.loaded_segments (0x74e58 : word) = Some W_74e58.
Proof. vm_refl. Qed.
Lemma D_74e58 : decode_any W_74e58 = Some (Op ALU_AND 11 11 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e5c : bv 32 := 0x00459593.
Lemma F_74e5c : fetch_word AsanUbsan.M.loaded_segments (0x74e5c : word) = Some W_74e5c.
Proof. vm_refl. Qed.
Lemma D_74e5c : decode_any W_74e5c = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e60 : bv 32 := 0x00b605b3.
Lemma F_74e60 : fetch_word AsanUbsan.M.loaded_segments (0x74e60 : word) = Some W_74e60.
Proof. vm_refl. Qed.
Lemma D_74e60 : decode_any W_74e60 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e64 : bv 32 := 0x0005b603.
Lemma F_74e64 : fetch_word AsanUbsan.M.loaded_segments (0x74e64 : word) = Some W_74e64.
Proof. vm_refl. Qed.
Lemma D_74e64 : decode_any W_74e64 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e68 : bv 32 := 0x0085a583.
Lemma F_74e68 : fetch_word AsanUbsan.M.loaded_segments (0x74e68 : word) = Some W_74e68.
Proof. vm_refl. Qed.
Lemma D_74e68 : decode_any W_74e68 = Some (Load SZ4 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e6c : bv 32 := 0xfcc994e3.
Lemma F_74e6c : fetch_word AsanUbsan.M.loaded_segments (0x74e6c : word) = Some W_74e6c.
Proof. vm_refl. Qed.
Lemma D_74e6c : decode_any W_74e6c = Some (Branch BC_NE 19 12 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e70 : bv 32 := 0x0c80006f.
Lemma F_74e70 : fetch_word AsanUbsan.M.loaded_segments (0x74e70 : word) = Some W_74e70.
Proof. vm_refl. Qed.
Lemma D_74e70 : decode_any W_74e70 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e74 : bv 32 := 0x00050a93.
Lemma F_74e74 : fetch_word AsanUbsan.M.loaded_segments (0x74e74 : word) = Some W_74e74.
Proof. vm_refl. Qed.
Lemma D_74e74 : decode_any W_74e74 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e78 : bv 32 := 0x000a0513.
Lemma F_74e78 : fetch_word AsanUbsan.M.loaded_segments (0x74e78 : word) = Some W_74e78.
Proof. vm_refl. Qed.
Lemma D_74e78 : decode_any W_74e78 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e7c : bv 32 := 0x69c000ef.
Lemma F_74e7c : fetch_word AsanUbsan.M.loaded_segments (0x74e7c : word) = Some W_74e7c.
Proof. vm_refl. Qed.
Lemma D_74e7c : decode_any W_74e7c = Some (Jal 1 1692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e80 : bv 32 := 0x00050613.
Lemma F_74e80 : fetch_word AsanUbsan.M.loaded_segments (0x74e80 : word) = Some W_74e80.
Proof. vm_refl. Qed.
Lemma D_74e80 : decode_any W_74e80 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e84 : bv 32 := 0x000a8513.
Lemma F_74e84 : fetch_word AsanUbsan.M.loaded_segments (0x74e84 : word) = Some W_74e84.
Proof. vm_refl. Qed.
Lemma D_74e84 : decode_any W_74e84 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e88 : bv 32 := 0xfc9ff06f.
Lemma F_74e88 : fetch_word AsanUbsan.M.loaded_segments (0x74e88 : word) = Some W_74e88.
Proof. vm_refl. Qed.
Lemma D_74e88 : decode_any W_74e88 = Some (Jal 0 2097096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e8c : bv 32 := 0x00090513.
Lemma F_74e8c : fetch_word AsanUbsan.M.loaded_segments (0x74e8c : word) = Some W_74e8c.
Proof. vm_refl. Qed.
Lemma D_74e8c : decode_any W_74e8c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e90 : bv 32 := 0x5f8000ef.
Lemma F_74e90 : fetch_word AsanUbsan.M.loaded_segments (0x74e90 : word) = Some W_74e90.
Proof. vm_refl. Qed.
Lemma D_74e90 : decode_any W_74e90 = Some (Jal 1 1528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e94 : bv 32 := 0x00050a93.
Lemma F_74e94 : fetch_word AsanUbsan.M.loaded_segments (0x74e94 : word) = Some W_74e94.
Proof. vm_refl. Qed.
Lemma D_74e94 : decode_any W_74e94 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e98 : bv 32 := 0x03950663.
Lemma F_74e98 : fetch_word AsanUbsan.M.loaded_segments (0x74e98 : word) = Some W_74e98.
Proof. vm_refl. Qed.
Lemma D_74e98 : decode_any W_74e98 = Some (Branch BC_EQ 10 25 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74e9c : bv 32 := 0x00813603.
Lemma F_74e9c : fetch_word AsanUbsan.M.loaded_segments (0x74e9c : word) = Some W_74e9c.
Proof. vm_refl. Qed.
Lemma D_74e9c : decode_any W_74e9c = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ea0 : bv 32 := 0x01013683.
Lemma F_74ea0 : fetch_word AsanUbsan.M.loaded_segments (0x74ea0 : word) = Some W_74ea0.
Proof. vm_refl. Qed.
Lemma D_74ea0 : decode_any W_74ea0 = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ea4 : bv 32 := 0x00048513.
Lemma F_74ea4 : fetch_word AsanUbsan.M.loaded_segments (0x74ea4 : word) = Some W_74ea4.
Proof. vm_refl. Qed.
Lemma D_74ea4 : decode_any W_74ea4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ea8 : bv 32 := 0x000a8593.
Lemma F_74ea8 : fetch_word AsanUbsan.M.loaded_segments (0x74ea8 : word) = Some W_74ea8.
Proof. vm_refl. Qed.
Lemma D_74ea8 : decode_any W_74ea8 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74eac : bv 32 := 0x00098713.
Lemma F_74eac : fetch_word AsanUbsan.M.loaded_segments (0x74eac : word) = Some W_74eac.
Proof. vm_refl. Qed.
Lemma D_74eac : decode_any W_74eac = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74eb0 : bv 32 := 0x524000ef.
Lemma F_74eb0 : fetch_word AsanUbsan.M.loaded_segments (0x74eb0 : word) = Some W_74eb0.
Proof. vm_refl. Qed.
Lemma D_74eb0 : decode_any W_74eb0 = Some (Jal 1 1316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74eb4 : bv 32 := 0x00050863.
Lemma F_74eb4 : fetch_word AsanUbsan.M.loaded_segments (0x74eb4 : word) = Some W_74eb4.
Proof. vm_refl. Qed.
Lemma D_74eb4 : decode_any W_74eb4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74eb8 : bv 32 := 0x0310000f.
Lemma F_74eb8 : fetch_word AsanUbsan.M.loaded_segments (0x74eb8 : word) = Some W_74eb8.
Proof. vm_refl. Qed.
Lemma D_74eb8 : decode_any W_74eb8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ebc : bv 32 := 0x01592023.
Lemma F_74ebc : fetch_word AsanUbsan.M.loaded_segments (0x74ebc : word) = Some W_74ebc.
Proof. vm_refl. Qed.
Lemma D_74ebc : decode_any W_74ebc = Some (Store SZ4 18 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ec0 : bv 32 := 0x0780006f.
Lemma F_74ec0 : fetch_word AsanUbsan.M.loaded_segments (0x74ec0 : word) = Some W_74ec0.
Proof. vm_refl. Qed.
Lemma D_74ec0 : decode_any W_74ec0 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ec4 : bv 32 := 0x00400537.
Lemma F_74ec4 : fetch_word AsanUbsan.M.loaded_segments (0x74ec4 : word) = Some W_74ec4.
Proof. vm_refl. Qed.
Lemma D_74ec4 : decode_any W_74ec4 = Some (Lui 10 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ec8 : bv 32 := 0x00a48533.
Lemma F_74ec8 : fetch_word AsanUbsan.M.loaded_segments (0x74ec8 : word) = Some W_74ec8.
Proof. vm_refl. Qed.
Lemma D_74ec8 : decode_any W_74ec8 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ecc : bv 32 := 0x00100593.
Lemma F_74ecc : fetch_word AsanUbsan.M.loaded_segments (0x74ecc : word) = Some W_74ecc.
Proof. vm_refl. Qed.
Lemma D_74ecc : decode_any W_74ecc = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ed0 : bv 32 := 0x00b5252f.
Lemma F_74ed0 : fetch_word AsanUbsan.M.loaded_segments (0x74ed0 : word) = Some W_74ed0.
Proof. vm_refl. Qed.
Lemma D_74ed0 : decode_any W_74ed0 = Some (Amo AMO_ADD AW false false 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ed4 : bv 32 := 0x0015051b.
Lemma F_74ed4 : fetch_word AsanUbsan.M.loaded_segments (0x74ed4 : word) = Some W_74ed4.
Proof. vm_refl. Qed.
Lemma D_74ed4 : decode_any W_74ed4 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ed8 : bv 32 := 0x02051493.
Lemma F_74ed8 : fetch_word AsanUbsan.M.loaded_segments (0x74ed8 : word) = Some W_74ed8.
Proof. vm_refl. Qed.
Lemma D_74ed8 : decode_any W_74ed8 = Some (ShiftImm ALU_SLL 9 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74edc : bv 32 := 0x0204d493.
Lemma F_74edc : fetch_word AsanUbsan.M.loaded_segments (0x74edc : word) = Some W_74edc.
Proof. vm_refl. Qed.
Lemma D_74edc : decode_any W_74edc = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ee0 : bv 32 := 0x08054663.
Lemma F_74ee0 : fetch_word AsanUbsan.M.loaded_segments (0x74ee0 : word) = Some W_74ee0.
Proof. vm_refl. Qed.
Lemma D_74ee0 : decode_any W_74ee0 = Some (Branch BC_LT 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ee4 : bv 32 := 0x00050b93.
Lemma F_74ee4 : fetch_word AsanUbsan.M.loaded_segments (0x74ee4 : word) = Some W_74ee4.
Proof. vm_refl. Qed.
Lemma D_74ee4 : decode_any W_74ee4 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ee8 : bv 32 := 0x0104d593.
Lemma F_74ee8 : fetch_word AsanUbsan.M.loaded_segments (0x74ee8 : word) = Some W_74ee8.
Proof. vm_refl. Qed.
Lemma D_74ee8 : decode_any W_74ee8 = Some (ShiftImm ALU_SRL 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74eec : bv 32 := 0x00359513.
Lemma F_74eec : fetch_word AsanUbsan.M.loaded_segments (0x74eec : word) = Some W_74eec.
Proof. vm_refl. Qed.
Lemma D_74eec : decode_any W_74eec = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ef0 : bv 32 := 0x00ac0533.
Lemma F_74ef0 : fetch_word AsanUbsan.M.loaded_segments (0x74ef0 : word) = Some W_74ef0.
Proof. vm_refl. Qed.
Lemma D_74ef0 : decode_any W_74ef0 = Some (Op ALU_ADD 10 24 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ef4 : bv 32 := 0x00053503.
Lemma F_74ef4 : fetch_word AsanUbsan.M.loaded_segments (0x74ef4 : word) = Some W_74ef4.
Proof. vm_refl. Qed.
Lemma D_74ef4 : decode_any W_74ef4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ef8 : bv 32 := 0x08050a63.
Lemma F_74ef8 : fetch_word AsanUbsan.M.loaded_segments (0x74ef8 : word) = Some W_74ef8.
Proof. vm_refl. Qed.
Lemma D_74ef8 : decode_any W_74ef8 = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74efc : bv 32 := 0x0164f5b3.
Lemma F_74efc : fetch_word AsanUbsan.M.loaded_segments (0x74efc : word) = Some W_74efc.
Proof. vm_refl. Qed.
Lemma D_74efc : decode_any W_74efc = Some (Op ALU_AND 11 9 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f00 : bv 32 := 0x00459593.
Lemma F_74f00 : fetch_word AsanUbsan.M.loaded_segments (0x74f00 : word) = Some W_74f00.
Proof. vm_refl. Qed.
Lemma D_74f00 : decode_any W_74f00 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f04 : bv 32 := 0x00b504b3.
Lemma F_74f04 : fetch_word AsanUbsan.M.loaded_segments (0x74f04 : word) = Some W_74f04.
Proof. vm_refl. Qed.
Lemma D_74f04 : decode_any W_74f04 = Some (Op ALU_ADD 9 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f08 : bv 32 := 0x00810613.
Lemma F_74f08 : fetch_word AsanUbsan.M.loaded_segments (0x74f08 : word) = Some W_74f08.
Proof. vm_refl. Qed.
Lemma D_74f08 : decode_any W_74f08 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f0c : bv 32 := 0x00048513.
Lemma F_74f0c : fetch_word AsanUbsan.M.loaded_segments (0x74f0c : word) = Some W_74f0c.
Proof. vm_refl. Qed.
Lemma D_74f0c : decode_any W_74f0c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f10 : bv 32 := 0x00000593.
Lemma F_74f10 : fetch_word AsanUbsan.M.loaded_segments (0x74f10 : word) = Some W_74f10.
Proof. vm_refl. Qed.
Lemma D_74f10 : decode_any W_74f10 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f14 : bv 32 := 0x00098693.
Lemma F_74f14 : fetch_word AsanUbsan.M.loaded_segments (0x74f14 : word) = Some W_74f14.
Proof. vm_refl. Qed.
Lemma D_74f14 : decode_any W_74f14 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f18 : bv 32 := 0xaf5ff0ef.
Lemma F_74f18 : fetch_word AsanUbsan.M.loaded_segments (0x74f18 : word) = Some W_74f18.
Proof. vm_refl. Qed.
Lemma D_74f18 : decode_any W_74f18 = Some (Jal 1 2095860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f1c : bv 32 := 0x0154a423.
Lemma F_74f1c : fetch_word AsanUbsan.M.loaded_segments (0x74f1c : word) = Some W_74f1c.
Proof. vm_refl. Qed.
Lemma D_74f1c : decode_any W_74f1c = Some (Store SZ4 9 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f20 : bv 32 := 0x0310000f.
Lemma F_74f20 : fetch_word AsanUbsan.M.loaded_segments (0x74f20 : word) = Some W_74f20.
Proof. vm_refl. Qed.
Lemma D_74f20 : decode_any W_74f20 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f24 : bv 32 := 0x000b8513.
Lemma F_74f24 : fetch_word AsanUbsan.M.loaded_segments (0x74f24 : word) = Some W_74f24.
Proof. vm_refl. Qed.
Lemma D_74f24 : decode_any W_74f24 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f28 : bv 32 := 0x01792023.
Lemma F_74f28 : fetch_word AsanUbsan.M.loaded_segments (0x74f28 : word) = Some W_74f28.
Proof. vm_refl. Qed.
Lemma D_74f28 : decode_any W_74f28 = Some (Store SZ4 18 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f2c : bv 32 := 0x00040663.
Lemma F_74f2c : fetch_word AsanUbsan.M.loaded_segments (0x74f2c : word) = Some W_74f2c.
Proof. vm_refl. Qed.
Lemma D_74f2c : decode_any W_74f2c = Some (Branch BC_EQ 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f30 : bv 32 := 0x00100593.
Lemma F_74f30 : fetch_word AsanUbsan.M.loaded_segments (0x74f30 : word) = Some W_74f30.
Proof. vm_refl. Qed.
Lemma D_74f30 : decode_any W_74f30 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f34 : bv 32 := 0x00b40023.
Lemma F_74f34 : fetch_word AsanUbsan.M.loaded_segments (0x74f34 : word) = Some W_74f34.
Proof. vm_refl. Qed.
Lemma D_74f34 : decode_any W_74f34 = Some (Store SZ1 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f38 : bv 32 := 0x06813083.
Lemma F_74f38 : fetch_word AsanUbsan.M.loaded_segments (0x74f38 : word) = Some W_74f38.
Proof. vm_refl. Qed.
Lemma D_74f38 : decode_any W_74f38 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f3c : bv 32 := 0x06013403.
Lemma F_74f3c : fetch_word AsanUbsan.M.loaded_segments (0x74f3c : word) = Some W_74f3c.
Proof. vm_refl. Qed.
Lemma D_74f3c : decode_any W_74f3c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f40 : bv 32 := 0x05813483.
Lemma F_74f40 : fetch_word AsanUbsan.M.loaded_segments (0x74f40 : word) = Some W_74f40.
Proof. vm_refl. Qed.
Lemma D_74f40 : decode_any W_74f40 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f44 : bv 32 := 0x05013903.
Lemma F_74f44 : fetch_word AsanUbsan.M.loaded_segments (0x74f44 : word) = Some W_74f44.
Proof. vm_refl. Qed.
Lemma D_74f44 : decode_any W_74f44 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f48 : bv 32 := 0x04813983.
Lemma F_74f48 : fetch_word AsanUbsan.M.loaded_segments (0x74f48 : word) = Some W_74f48.
Proof. vm_refl. Qed.
Lemma D_74f48 : decode_any W_74f48 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f4c : bv 32 := 0x04013a03.
Lemma F_74f4c : fetch_word AsanUbsan.M.loaded_segments (0x74f4c : word) = Some W_74f4c.
Proof. vm_refl. Qed.
Lemma D_74f4c : decode_any W_74f4c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f50 : bv 32 := 0x03813a83.
Lemma F_74f50 : fetch_word AsanUbsan.M.loaded_segments (0x74f50 : word) = Some W_74f50.
Proof. vm_refl. Qed.
Lemma D_74f50 : decode_any W_74f50 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f54 : bv 32 := 0x03013b03.
Lemma F_74f54 : fetch_word AsanUbsan.M.loaded_segments (0x74f54 : word) = Some W_74f54.
Proof. vm_refl. Qed.
Lemma D_74f54 : decode_any W_74f54 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f58 : bv 32 := 0x02813b83.
Lemma F_74f58 : fetch_word AsanUbsan.M.loaded_segments (0x74f58 : word) = Some W_74f58.
Proof. vm_refl. Qed.
Lemma D_74f58 : decode_any W_74f58 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f5c : bv 32 := 0x02013c03.
Lemma F_74f5c : fetch_word AsanUbsan.M.loaded_segments (0x74f5c : word) = Some W_74f5c.
Proof. vm_refl. Qed.
Lemma D_74f5c : decode_any W_74f5c = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f60 : bv 32 := 0x01813c83.
Lemma F_74f60 : fetch_word AsanUbsan.M.loaded_segments (0x74f60 : word) = Some W_74f60.
Proof. vm_refl. Qed.
Lemma D_74f60 : decode_any W_74f60 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f64 : bv 32 := 0x07010113.
Lemma F_74f64 : fetch_word AsanUbsan.M.loaded_segments (0x74f64 : word) = Some W_74f64.
Proof. vm_refl. Qed.
Lemma D_74f64 : decode_any W_74f64 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f68 : bv 32 := 0x00008067.
Lemma F_74f68 : fetch_word AsanUbsan.M.loaded_segments (0x74f68 : word) = Some W_74f68.
Proof. vm_refl. Qed.
Lemma D_74f68 : decode_any W_74f68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f6c : bv 32 := 0x017576b3.
Lemma F_74f6c : fetch_word AsanUbsan.M.loaded_segments (0x74f6c : word) = Some W_74f6c.
Proof. vm_refl. Qed.
Lemma D_74f6c : decode_any W_74f6c = Some (Op ALU_AND 13 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f70 : bv 32 := 0xfffa4517.
Lemma F_74f70 : fetch_word AsanUbsan.M.loaded_segments (0x74f70 : word) = Some W_74f70.
Proof. vm_refl. Qed.
Lemma D_74f70 : decode_any W_74f70 = Some (Auipc 10 1048484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f74 : bv 32 := 0xfffa1597.
Lemma F_74f74 : fetch_word AsanUbsan.M.loaded_segments (0x74f74 : word) = Some W_74f74.
Proof. vm_refl. Qed.
Lemma D_74f74 : decode_any W_74f74 = Some (Auipc 11 1048481, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f78 : bv 32 := 0xa6750513.
Lemma F_74f78 : fetch_word AsanUbsan.M.loaded_segments (0x74f78 : word) = Some W_74f78.
Proof. vm_refl. Qed.
Lemma D_74f78 : decode_any W_74f78 = Some (OpImm ALU_ADD 10 10 2663, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f7c : bv 32 := 0x2b558613.
Lemma F_74f7c : fetch_word AsanUbsan.M.loaded_segments (0x74f7c : word) = Some W_74f7c.
Proof. vm_refl. Qed.
Lemma D_74f7c : decode_any W_74f7c = Some (OpImm ALU_ADD 12 11 693, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f80 : bv 32 := 0x08c00593.
Lemma F_74f80 : fetch_word AsanUbsan.M.loaded_segments (0x74f80 : word) = Some W_74f80.
Proof. vm_refl. Qed.
Lemma D_74f80 : decode_any W_74f80 = Some (OpImm ALU_ADD 11 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f84 : bv 32 := 0x00048713.
Lemma F_74f84 : fetch_word AsanUbsan.M.loaded_segments (0x74f84 : word) = Some W_74f84.
Proof. vm_refl. Qed.
Lemma D_74f84 : decode_any W_74f84 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f88 : bv 32 := 0xf2df80ef.
Lemma F_74f88 : fetch_word AsanUbsan.M.loaded_segments (0x74f88 : word) = Some W_74f88.
Proof. vm_refl. Qed.
Lemma D_74f88 : decode_any W_74f88 = Some (Jal 1 2068268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f8c : bv 32 := 0x000a0513.
Lemma F_74f8c : fetch_word AsanUbsan.M.loaded_segments (0x74f8c : word) = Some W_74f8c.
Proof. vm_refl. Qed.
Lemma D_74f8c : decode_any W_74f8c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f90 : bv 32 := 0x588000ef.
Lemma F_74f90 : fetch_word AsanUbsan.M.loaded_segments (0x74f90 : word) = Some W_74f90.
Proof. vm_refl. Qed.
Lemma D_74f90 : decode_any W_74f90 = Some (Jal 1 1416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f94 : bv 32 := 0xf69ff06f.
Lemma F_74f94 : fetch_word AsanUbsan.M.loaded_segments (0x74f94 : word) = Some W_74f94.
Proof. vm_refl. Qed.
Lemma D_74f94 : decode_any W_74f94 = Some (Jal 0 2097000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f98 : bv 32 := 0xff010113.
Lemma F_74f98 : fetch_word AsanUbsan.M.loaded_segments (0x74f98 : word) = Some W_74f98.
Proof. vm_refl. Qed.
Lemma D_74f98 : decode_any W_74f98 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74f9c : bv 32 := 0x00113423.
Lemma F_74f9c : fetch_word AsanUbsan.M.loaded_segments (0x74f9c : word) = Some W_74f9c.
Proof. vm_refl. Qed.
Lemma D_74f9c : decode_any W_74f9c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74fa0 : bv 32 := 0x00813023.
Lemma F_74fa0 : fetch_word AsanUbsan.M.loaded_segments (0x74fa0 : word) = Some W_74fa0.
Proof. vm_refl. Qed.
Lemma D_74fa0 : decode_any W_74fa0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74fa4 : bv 32 := 0x06050463.
Lemma F_74fa4 : fetch_word AsanUbsan.M.loaded_segments (0x74fa4 : word) = Some W_74fa4.
Proof. vm_refl. Qed.
Lemma D_74fa4 : decode_any W_74fa4 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.
