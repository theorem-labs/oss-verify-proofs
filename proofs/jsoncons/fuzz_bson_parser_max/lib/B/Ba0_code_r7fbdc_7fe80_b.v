(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_99bac : bv 32 := 0x00058613.
Lemma F_99bac : fetch_word AsanUbsan.M.loaded_segments (0x99fc4 : word) = Some W_99bac.
Proof. vm_refl. Qed.
Lemma D_99bac : decode_any W_99bac = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bb0 : bv 32 := 0x00188597.
Lemma F_99bb0 : fetch_word AsanUbsan.M.loaded_segments (0x99fc8 : word) = Some W_99bb0.
Proof. vm_refl. Qed.
Lemma D_99bb0 : decode_any W_99bb0 = Some (Auipc 11 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bb4 : bv 32 := 0xb5058593.
Lemma F_99bb4 : fetch_word AsanUbsan.M.loaded_segments (0x99fcc : word) = Some W_99bb4.
Proof. vm_refl. Qed.
Lemma D_99bb4 : decode_any W_99bb4 = Some (OpImm ALU_ADD 11 11 2896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bb8 : bv 32 := 0x00050693.
Lemma F_99bb8 : fetch_word AsanUbsan.M.loaded_segments (0x99fd0 : word) = Some W_99bb8.
Proof. vm_refl. Qed.
Lemma D_99bb8 : decode_any W_99bb8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bbc : bv 32 := 0x00058513.
Lemma F_99bbc : fetch_word AsanUbsan.M.loaded_segments (0x99fd4 : word) = Some W_99bbc.
Proof. vm_refl. Qed.
Lemma D_99bbc : decode_any W_99bbc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bc0 : bv 32 := 0x00068593.
Lemma F_99bc0 : fetch_word AsanUbsan.M.loaded_segments (0x99fd8 : word) = Some W_99bc0.
Proof. vm_refl. Qed.
Lemma D_99bc0 : decode_any W_99bc0 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bc4 : bv 32 := 0x00000693.
Lemma F_99bc4 : fetch_word AsanUbsan.M.loaded_segments (0x99fdc : word) = Some W_99bc4.
Proof. vm_refl. Qed.
Lemma D_99bc4 : decode_any W_99bc4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bc8 : bv 32 := 0x0040006f.
Lemma F_99bc8 : fetch_word AsanUbsan.M.loaded_segments (0x99fe0 : word) = Some W_99bc8.
Proof. vm_refl. Qed.
Lemma D_99bc8 : decode_any W_99bc8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bcc : bv 32 := 0xf9010113.
Lemma F_99bcc : fetch_word AsanUbsan.M.loaded_segments (0x99fe4 : word) = Some W_99bcc.
Proof. vm_refl. Qed.
Lemma D_99bcc : decode_any W_99bcc = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bd0 : bv 32 := 0x06113423.
Lemma F_99bd0 : fetch_word AsanUbsan.M.loaded_segments (0x99fe8 : word) = Some W_99bd0.
Proof. vm_refl. Qed.
Lemma D_99bd0 : decode_any W_99bd0 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bd4 : bv 32 := 0x06813023.
Lemma F_99bd4 : fetch_word AsanUbsan.M.loaded_segments (0x99fec : word) = Some W_99bd4.
Proof. vm_refl. Qed.
Lemma D_99bd4 : decode_any W_99bd4 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bd8 : bv 32 := 0x04913c23.
Lemma F_99bd8 : fetch_word AsanUbsan.M.loaded_segments (0x99ff0 : word) = Some W_99bd8.
Proof. vm_refl. Qed.
Lemma D_99bd8 : decode_any W_99bd8 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bdc : bv 32 := 0x05213823.
Lemma F_99bdc : fetch_word AsanUbsan.M.loaded_segments (0x99ff4 : word) = Some W_99bdc.
Proof. vm_refl. Qed.
Lemma D_99bdc : decode_any W_99bdc = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99be0 : bv 32 := 0x05313423.
Lemma F_99be0 : fetch_word AsanUbsan.M.loaded_segments (0x99ff8 : word) = Some W_99be0.
Proof. vm_refl. Qed.
Lemma D_99be0 : decode_any W_99be0 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99be4 : bv 32 := 0x05413023.
Lemma F_99be4 : fetch_word AsanUbsan.M.loaded_segments (0x99ffc : word) = Some W_99be4.
Proof. vm_refl. Qed.
Lemma D_99be4 : decode_any W_99be4 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99be8 : bv 32 := 0x03513c23.
Lemma F_99be8 : fetch_word AsanUbsan.M.loaded_segments (0x9a000 : word) = Some W_99be8.
Proof. vm_refl. Qed.
Lemma D_99be8 : decode_any W_99be8 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bec : bv 32 := 0x03613823.
Lemma F_99bec : fetch_word AsanUbsan.M.loaded_segments (0x9a004 : word) = Some W_99bec.
Proof. vm_refl. Qed.
Lemma D_99bec : decode_any W_99bec = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bf0 : bv 32 := 0x03713423.
Lemma F_99bf0 : fetch_word AsanUbsan.M.loaded_segments (0x9a008 : word) = Some W_99bf0.
Proof. vm_refl. Qed.
Lemma D_99bf0 : decode_any W_99bf0 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bf4 : bv 32 := 0x03813023.
Lemma F_99bf4 : fetch_word AsanUbsan.M.loaded_segments (0x9a00c : word) = Some W_99bf4.
Proof. vm_refl. Qed.
Lemma D_99bf4 : decode_any W_99bf4 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bf8 : bv 32 := 0x01913c23.
Lemma F_99bf8 : fetch_word AsanUbsan.M.loaded_segments (0x9a010 : word) = Some W_99bf8.
Proof. vm_refl. Qed.
Lemma D_99bf8 : decode_any W_99bf8 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99bfc : bv 32 := 0x00068413.
Lemma F_99bfc : fetch_word AsanUbsan.M.loaded_segments (0x9a014 : word) = Some W_99bfc.
Proof. vm_refl. Qed.
Lemma D_99bfc : decode_any W_99bfc = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c00 : bv 32 := 0x00050493.
Lemma F_99c00 : fetch_word AsanUbsan.M.loaded_segments (0x9a018 : word) = Some W_99c00.
Proof. vm_refl. Qed.
Lemma D_99c00 : decode_any W_99c00 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c04 : bv 32 := 0x00b13423.
Lemma F_99c04 : fetch_word AsanUbsan.M.loaded_segments (0x9a01c : word) = Some W_99c04.
Proof. vm_refl. Qed.
Lemma D_99c04 : decode_any W_99c04 = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c08 : bv 32 := 0x00c13823.
Lemma F_99c08 : fetch_word AsanUbsan.M.loaded_segments (0x9a020 : word) = Some W_99c08.
Proof. vm_refl. Qed.
Lemma D_99c08 : decode_any W_99c08 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c0c : bv 32 := 0x00068463.
Lemma F_99c0c : fetch_word AsanUbsan.M.loaded_segments (0x9a024 : word) = Some W_99c0c.
Proof. vm_refl. Qed.
Lemma D_99c0c : decode_any W_99c0c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c14 : bv 32 := 0x0006069b.
Lemma F_99c14 : fetch_word AsanUbsan.M.loaded_segments (0x9a02c : word) = Some W_99c14.
Proof. vm_refl. Qed.
Lemma D_99c14 : decode_any W_99c14 = Some (OpImm32 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c18 : bv 32 := 0x00000513.
Lemma F_99c18 : fetch_word AsanUbsan.M.loaded_segments (0x9a030 : word) = Some W_99c18.
Proof. vm_refl. Qed.
Lemma D_99c18 : decode_any W_99c18 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c1c : bv 32 := 0x1c068a63.
Lemma F_99c1c : fetch_word AsanUbsan.M.loaded_segments (0x9a034 : word) = Some W_99c1c.
Proof. vm_refl. Qed.
Lemma D_99c1c : decode_any W_99c1c = Some (Branch BC_EQ 13 0 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c20 : bv 32 := 0x1c058863.
Lemma F_99c20 : fetch_word AsanUbsan.M.loaded_segments (0x9a038 : word) = Some W_99c20.
Proof. vm_refl. Qed.
Lemma D_99c20 : decode_any W_99c20 = Some (Branch BC_EQ 11 0 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c24 : bv 32 := 0x02065693.
Lemma F_99c24 : fetch_word AsanUbsan.M.loaded_segments (0x9a03c : word) = Some W_99c24.
Proof. vm_refl. Qed.
Lemma D_99c24 : decode_any W_99c24 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c28 : bv 32 := 0xfff00513.
Lemma F_99c28 : fetch_word AsanUbsan.M.loaded_segments (0x9a040 : word) = Some W_99c28.
Proof. vm_refl. Qed.
Lemma D_99c28 : decode_any W_99c28 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c2c : bv 32 := 0xfff76717.
Lemma F_99c2c : fetch_word AsanUbsan.M.loaded_segments (0x9a044 : word) = Some W_99c2c.
Proof. vm_refl. Qed.
Lemma D_99c2c : decode_any W_99c2c = Some (Auipc 14 1048438, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c30 : bv 32 := 0xfff76797.
Lemma F_99c30 : fetch_word AsanUbsan.M.loaded_segments (0x9a048 : word) = Some W_99c30.
Proof. vm_refl. Qed.
Lemma D_99c30 : decode_any W_99c30 = Some (Auipc 15 1048438, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c34 : bv 32 := 0x02055513.
Lemma F_99c34 : fetch_word AsanUbsan.M.loaded_segments (0x9a04c : word) = Some W_99c34.
Proof. vm_refl. Qed.
Lemma D_99c34 : decode_any W_99c34 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c38 : bv 32 := 0x2d87b783.
Lemma F_99c38 : fetch_word AsanUbsan.M.loaded_segments (0x9a050 : word) = Some W_99c38.
Proof. vm_refl. Qed.
Lemma D_99c38 : decode_any W_99c38 = Some (Load SZ8 true 15 15 728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c3c : bv 32 := 0x00a67633.
Lemma F_99c3c : fetch_word AsanUbsan.M.loaded_segments (0x9a054 : word) = Some W_99c3c.
Proof. vm_refl. Qed.
Lemma D_99c3c : decode_any W_99c3c = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c40 : bv 32 := 0xfff76517.
Lemma F_99c40 : fetch_word AsanUbsan.M.loaded_segments (0x9a058 : word) = Some W_99c40.
Proof. vm_refl. Qed.
Lemma D_99c40 : decode_any W_99c40 = Some (Auipc 10 1048438, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c44 : bv 32 := 0x3c053803.
Lemma F_99c44 : fetch_word AsanUbsan.M.loaded_segments (0x9a05c : word) = Some W_99c44.
Proof. vm_refl. Qed.
Lemma D_99c44 : decode_any W_99c44 = Some (Load SZ8 true 16 10 960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c48 : bv 32 := 0x2a473503.
Lemma F_99c48 : fetch_word AsanUbsan.M.loaded_segments (0x9a060 : word) = Some W_99c48.
Proof. vm_refl. Qed.
Lemma D_99c48 : decode_any W_99c48 = Some (Load SZ8 true 10 14 676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c4c : bv 32 := 0x02f60733.
Lemma F_99c4c : fetch_word AsanUbsan.M.loaded_segments (0x9a064 : word) = Some W_99c4c.
Proof. vm_refl. Qed.
Lemma D_99c4c : decode_any W_99c4c = Some (Mul M_MUL 14 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c50 : bv 32 := 0x00361793.
Lemma F_99c50 : fetch_word AsanUbsan.M.loaded_segments (0x9a068 : word) = Some W_99c50.
Proof. vm_refl. Qed.
Lemma D_99c50 : decode_any W_99c50 = Some (ShiftImm ALU_SLL 15 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c54 : bv 32 := 0x01074633.
Lemma F_99c54 : fetch_word AsanUbsan.M.loaded_segments (0x9a06c : word) = Some W_99c54.
Proof. vm_refl. Qed.
Lemma D_99c54 : decode_any W_99c54 = Some (Op ALU_XOR 12 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c58 : bv 32 := 0x00f58733.
Lemma F_99c58 : fetch_word AsanUbsan.M.loaded_segments (0x9a070 : word) = Some W_99c58.
Proof. vm_refl. Qed.
Lemma D_99c58 : decode_any W_99c58 = Some (Op ALU_ADD 14 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c5c : bv 32 := 0x0005b783.
Lemma F_99c5c : fetch_word AsanUbsan.M.loaded_segments (0x9a074 : word) = Some W_99c5c.
Proof. vm_refl. Qed.
Lemma D_99c5c : decode_any W_99c5c = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c60 : bv 32 := 0x00858593.
Lemma F_99c60 : fetch_word AsanUbsan.M.loaded_segments (0x9a078 : word) = Some W_99c60.
Proof. vm_refl. Qed.
Lemma D_99c60 : decode_any W_99c60 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c64 : bv 32 := 0x02a787b3.
Lemma F_99c64 : fetch_word AsanUbsan.M.loaded_segments (0x9a07c : word) = Some W_99c64.
Proof. vm_refl. Qed.
Lemma D_99c64 : decode_any W_99c64 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c68 : bv 32 := 0x02f7d813.
Lemma F_99c68 : fetch_word AsanUbsan.M.loaded_segments (0x9a080 : word) = Some W_99c68.
Proof. vm_refl. Qed.
Lemma D_99c68 : decode_any W_99c68 = Some (ShiftImm ALU_SRL 16 15 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c6c : bv 32 := 0x00f847b3.
Lemma F_99c6c : fetch_word AsanUbsan.M.loaded_segments (0x9a084 : word) = Some W_99c6c.
Proof. vm_refl. Qed.
Lemma D_99c6c : decode_any W_99c6c = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c70 : bv 32 := 0x02a787b3.
Lemma F_99c70 : fetch_word AsanUbsan.M.loaded_segments (0x9a088 : word) = Some W_99c70.
Proof. vm_refl. Qed.
Lemma D_99c70 : decode_any W_99c70 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c74 : bv 32 := 0x00c7c633.
Lemma F_99c74 : fetch_word AsanUbsan.M.loaded_segments (0x9a08c : word) = Some W_99c74.
Proof. vm_refl. Qed.
Lemma D_99c74 : decode_any W_99c74 = Some (Op ALU_XOR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c78 : bv 32 := 0x02a60633.
Lemma F_99c78 : fetch_word AsanUbsan.M.loaded_segments (0x9a090 : word) = Some W_99c78.
Proof. vm_refl. Qed.
Lemma D_99c78 : decode_any W_99c78 = Some (Mul M_MUL 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c7c : bv 32 := 0xfee590e3.
Lemma F_99c7c : fetch_word AsanUbsan.M.loaded_segments (0x9a094 : word) = Some W_99c7c.
Proof. vm_refl. Qed.
Lemma D_99c7c : decode_any W_99c7c = Some (Branch BC_NE 11 14 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c80 : bv 32 := 0x00010b37.
Lemma F_99c80 : fetch_word AsanUbsan.M.loaded_segments (0x9a098 : word) = Some W_99c80.
Proof. vm_refl. Qed.
Lemma D_99c80 : decode_any W_99c80 = Some (Lui 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c84 : bv 32 := 0x80000bb7.
Lemma F_99c84 : fetch_word AsanUbsan.M.loaded_segments (0x9a09c : word) = Some W_99c84.
Proof. vm_refl. Qed.
Lemma D_99c84 : decode_any W_99c84 = Some (Lui 23 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c88 : bv 32 := 0x02a685b3.
Lemma F_99c88 : fetch_word AsanUbsan.M.loaded_segments (0x9a0a0 : word) = Some W_99c88.
Proof. vm_refl. Qed.
Lemma D_99c88 : decode_any W_99c88 = Some (Mul M_MUL 11 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c8c : bv 32 := 0x004006b7.
Lemma F_99c8c : fetch_word AsanUbsan.M.loaded_segments (0x9a0a4 : word) = Some W_99c8c.
Proof. vm_refl. Qed.
Lemma D_99c8c : decode_any W_99c8c = Some (Lui 13 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c90 : bv 32 := 0xfffb0b1b.
Lemma F_99c90 : fetch_word AsanUbsan.M.loaded_segments (0x9a0a8 : word) = Some W_99c90.
Proof. vm_refl. Qed.
Lemma D_99c90 : decode_any W_99c90 = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c94 : bv 32 := 0xfffb8b9b.
Lemma F_99c94 : fetch_word AsanUbsan.M.loaded_segments (0x9a0ac : word) = Some W_99c94.
Proof. vm_refl. Qed.
Lemma D_99c94 : decode_any W_99c94 = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c98 : bv 32 := 0x02f5d713.
Lemma F_99c98 : fetch_word AsanUbsan.M.loaded_segments (0x9a0b0 : word) = Some W_99c98.
Proof. vm_refl. Qed.
Lemma D_99c98 : decode_any W_99c98 = Some (ShiftImm ALU_SRL 14 11 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99c9c : bv 32 := 0x00b745b3.
Lemma F_99c9c : fetch_word AsanUbsan.M.loaded_segments (0x9a0b4 : word) = Some W_99c9c.
Proof. vm_refl. Qed.
Lemma D_99c9c : decode_any W_99c9c = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ca0 : bv 32 := 0x02a585b3.
Lemma F_99ca0 : fetch_word AsanUbsan.M.loaded_segments (0x9a0b8 : word) = Some W_99ca0.
Proof. vm_refl. Qed.
Lemma D_99ca0 : decode_any W_99ca0 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ca4 : bv 32 := 0x00c5c5b3.
Lemma F_99ca4 : fetch_word AsanUbsan.M.loaded_segments (0x9a0bc : word) = Some W_99ca4.
Proof. vm_refl. Qed.
Lemma D_99ca4 : decode_any W_99ca4 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ca8 : bv 32 := 0x02a585b3.
Lemma F_99ca8 : fetch_word AsanUbsan.M.loaded_segments (0x9a0c0 : word) = Some W_99ca8.
Proof. vm_refl. Qed.
Lemma D_99ca8 : decode_any W_99ca8 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cac : bv 32 := 0x02f5d613.
Lemma F_99cac : fetch_word AsanUbsan.M.loaded_segments (0x9a0c4 : word) = Some W_99cac.
Proof. vm_refl. Qed.
Lemma D_99cac : decode_any W_99cac = Some (ShiftImm ALU_SRL 12 11 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cb0 : bv 32 := 0x00b645b3.
Lemma F_99cb0 : fetch_word AsanUbsan.M.loaded_segments (0x9a0c8 : word) = Some W_99cb0.
Proof. vm_refl. Qed.
Lemma D_99cb0 : decode_any W_99cb0 = Some (Op ALU_XOR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cb4 : bv 32 := 0x02a58533.
Lemma F_99cb4 : fetch_word AsanUbsan.M.loaded_segments (0x9a0cc : word) = Some W_99cb4.
Proof. vm_refl. Qed.
Lemma D_99cb4 : decode_any W_99cb4 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cb8 : bv 32 := 0x02f55593.
Lemma F_99cb8 : fetch_word AsanUbsan.M.loaded_segments (0x9a0d0 : word) = Some W_99cb8.
Proof. vm_refl. Qed.
Lemma D_99cb8 : decode_any W_99cb8 = Some (ShiftImm ALU_SRL 11 10 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cbc : bv 32 := 0x00a5c9b3.
Lemma F_99cbc : fetch_word AsanUbsan.M.loaded_segments (0x9a0d4 : word) = Some W_99cbc.
Proof. vm_refl. Qed.
Lemma D_99cbc : decode_any W_99cbc = Some (Op ALU_XOR 19 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cc0 : bv 32 := 0x02c99513.
Lemma F_99cc0 : fetch_word AsanUbsan.M.loaded_segments (0x9a0d8 : word) = Some W_99cc0.
Proof. vm_refl. Qed.
Lemma D_99cc0 : decode_any W_99cc0 = Some (ShiftImm ALU_SLL 10 19 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cc4 : bv 32 := 0x02a55513.
Lemma F_99cc4 : fetch_word AsanUbsan.M.loaded_segments (0x9a0dc : word) = Some W_99cc4.
Proof. vm_refl. Qed.
Lemma D_99cc4 : decode_any W_99cc4 = Some (ShiftImm ALU_SRL 10 10 42, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cc8 : bv 32 := 0x00a48933.
Lemma F_99cc8 : fetch_word AsanUbsan.M.loaded_segments (0x9a0e0 : word) = Some W_99cc8.
Proof. vm_refl. Qed.
Lemma D_99cc8 : decode_any W_99cc8 = Some (Op ALU_ADD 18 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ccc : bv 32 := 0x00092503.
Lemma F_99ccc : fetch_word AsanUbsan.M.loaded_segments (0x9a0e4 : word) = Some W_99ccc.
Proof. vm_refl. Qed.
Lemma D_99ccc : decode_any W_99ccc = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cd0 : bv 32 := 0x01068c1b.
Lemma F_99cd0 : fetch_word AsanUbsan.M.loaded_segments (0x9a0e8 : word) = Some W_99cd0.
Proof. vm_refl. Qed.
Lemma D_99cd0 : decode_any W_99cd0 = Some (OpImm32 24 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cd4 : bv 32 := 0x01848c33.
Lemma F_99cd4 : fetch_word AsanUbsan.M.loaded_segments (0x9a0ec : word) = Some W_99cd4.
Proof. vm_refl. Qed.
Lemma D_99cd4 : decode_any W_99cd4 = Some (Op ALU_ADD 24 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cd8 : bv 32 := 0x0230000f.
Lemma F_99cd8 : fetch_word AsanUbsan.M.loaded_segments (0x9a0f0 : word) = Some W_99cd8.
Proof. vm_refl. Qed.
Lemma D_99cd8 : decode_any W_99cd8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cdc : bv 32 := 0x01757cb3.
Lemma F_99cdc : fetch_word AsanUbsan.M.loaded_segments (0x9a0f4 : word) = Some W_99cdc.
Proof. vm_refl. Qed.
Lemma D_99cdc : decode_any W_99cdc = Some (Op ALU_AND 25 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ce0 : bv 32 := 0x0086869b.
Lemma F_99ce0 : fetch_word AsanUbsan.M.loaded_segments (0x9a0f8 : word) = Some W_99ce0.
Proof. vm_refl. Qed.
Lemma D_99ce0 : decode_any W_99ce0 = Some (OpImm32 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ce4 : bv 32 := 0x00d48a33.
Lemma F_99ce4 : fetch_word AsanUbsan.M.loaded_segments (0x9a0fc : word) = Some W_99ce4.
Proof. vm_refl. Qed.
Lemma D_99ce4 : decode_any W_99ce4 = Some (Op ALU_ADD 20 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ce8 : bv 32 := 0x000c8593.
Lemma F_99ce8 : fetch_word AsanUbsan.M.loaded_segments (0x9a100 : word) = Some W_99ce8.
Proof. vm_refl. Qed.
Lemma D_99ce8 : decode_any W_99ce8 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cec : bv 32 := 0x04058c63.
Lemma F_99cec : fetch_word AsanUbsan.M.loaded_segments (0x9a104 : word) = Some W_99cec.
Proof. vm_refl. Qed.
Lemma D_99cec : decode_any W_99cec = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cf0 : bv 32 := 0x00058513.
Lemma F_99cf0 : fetch_word AsanUbsan.M.loaded_segments (0x9a108 : word) = Some W_99cf0.
Proof. vm_refl. Qed.
Lemma D_99cf0 : decode_any W_99cf0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cf4 : bv 32 := 0x0105d59b.
Lemma F_99cf4 : fetch_word AsanUbsan.M.loaded_segments (0x9a10c : word) = Some W_99cf4.
Proof. vm_refl. Qed.
Lemma D_99cf4 : decode_any W_99cf4 = Some (ShiftImm32 ALU_SRL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cf8 : bv 32 := 0x00359613.
Lemma F_99cf8 : fetch_word AsanUbsan.M.loaded_segments (0x9a110 : word) = Some W_99cf8.
Proof. vm_refl. Qed.
Lemma D_99cf8 : decode_any W_99cf8 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99cfc : bv 32 := 0x00cc0633.
Lemma F_99cfc : fetch_word AsanUbsan.M.loaded_segments (0x9a114 : word) = Some W_99cfc.
Proof. vm_refl. Qed.
Lemma D_99cfc : decode_any W_99cfc = Some (Op ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d00 : bv 32 := 0x00063603.
Lemma F_99d00 : fetch_word AsanUbsan.M.loaded_segments (0x9a118 : word) = Some W_99d00.
Proof. vm_refl. Qed.
Lemma D_99d00 : decode_any W_99d00 = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d04 : bv 32 := 0x02060463.
Lemma F_99d04 : fetch_word AsanUbsan.M.loaded_segments (0x9a11c : word) = Some W_99d04.
Proof. vm_refl. Qed.
Lemma D_99d04 : decode_any W_99d04 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d08 : bv 32 := 0x02051593.
Lemma F_99d08 : fetch_word AsanUbsan.M.loaded_segments (0x9a120 : word) = Some W_99d08.
Proof. vm_refl. Qed.
Lemma D_99d08 : decode_any W_99d08 = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d0c : bv 32 := 0x0205d593.
Lemma F_99d0c : fetch_word AsanUbsan.M.loaded_segments (0x9a124 : word) = Some W_99d0c.
Proof. vm_refl. Qed.
Lemma D_99d0c : decode_any W_99d0c = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d10 : bv 32 := 0x0165f5b3.
Lemma F_99d10 : fetch_word AsanUbsan.M.loaded_segments (0x9a128 : word) = Some W_99d10.
Proof. vm_refl. Qed.
Lemma D_99d10 : decode_any W_99d10 = Some (Op ALU_AND 11 11 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d14 : bv 32 := 0x00459593.
Lemma F_99d14 : fetch_word AsanUbsan.M.loaded_segments (0x9a12c : word) = Some W_99d14.
Proof. vm_refl. Qed.
Lemma D_99d14 : decode_any W_99d14 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d18 : bv 32 := 0x00b605b3.
Lemma F_99d18 : fetch_word AsanUbsan.M.loaded_segments (0x9a130 : word) = Some W_99d18.
Proof. vm_refl. Qed.
Lemma D_99d18 : decode_any W_99d18 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d1c : bv 32 := 0x0005b603.
Lemma F_99d1c : fetch_word AsanUbsan.M.loaded_segments (0x9a134 : word) = Some W_99d1c.
Proof. vm_refl. Qed.
Lemma D_99d1c : decode_any W_99d1c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d20 : bv 32 := 0x0085a583.
Lemma F_99d20 : fetch_word AsanUbsan.M.loaded_segments (0x9a138 : word) = Some W_99d20.
Proof. vm_refl. Qed.
Lemma D_99d20 : decode_any W_99d20 = Some (Load SZ4 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d24 : bv 32 := 0xfcc994e3.
Lemma F_99d24 : fetch_word AsanUbsan.M.loaded_segments (0x9a13c : word) = Some W_99d24.
Proof. vm_refl. Qed.
Lemma D_99d24 : decode_any W_99d24 = Some (Branch BC_NE 19 12 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d28 : bv 32 := 0x0c80006f.
Lemma F_99d28 : fetch_word AsanUbsan.M.loaded_segments (0x9a140 : word) = Some W_99d28.
Proof. vm_refl. Qed.
Lemma D_99d28 : decode_any W_99d28 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d44 : bv 32 := 0x00090513.
Lemma F_99d44 : fetch_word AsanUbsan.M.loaded_segments (0x9a15c : word) = Some W_99d44.
Proof. vm_refl. Qed.
Lemma D_99d44 : decode_any W_99d44 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d48 : bv 32 := 0x5f8000ef.
Lemma F_99d48 : fetch_word AsanUbsan.M.loaded_segments (0x9a160 : word) = Some W_99d48.
Proof. vm_refl. Qed.
Lemma D_99d48 : decode_any W_99d48 = Some (Jal 1 1528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d4c : bv 32 := 0x00050a93.
Lemma F_99d4c : fetch_word AsanUbsan.M.loaded_segments (0x9a164 : word) = Some W_99d4c.
Proof. vm_refl. Qed.
Lemma D_99d4c : decode_any W_99d4c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d50 : bv 32 := 0x03950663.
Lemma F_99d50 : fetch_word AsanUbsan.M.loaded_segments (0x9a168 : word) = Some W_99d50.
Proof. vm_refl. Qed.
Lemma D_99d50 : decode_any W_99d50 = Some (Branch BC_EQ 10 25 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d7c : bv 32 := 0x00400537.
Lemma F_99d7c : fetch_word AsanUbsan.M.loaded_segments (0x9a194 : word) = Some W_99d7c.
Proof. vm_refl. Qed.
Lemma D_99d7c : decode_any W_99d7c = Some (Lui 10 1024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d80 : bv 32 := 0x00a48533.
Lemma F_99d80 : fetch_word AsanUbsan.M.loaded_segments (0x9a198 : word) = Some W_99d80.
Proof. vm_refl. Qed.
Lemma D_99d80 : decode_any W_99d80 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d84 : bv 32 := 0x00100593.
Lemma F_99d84 : fetch_word AsanUbsan.M.loaded_segments (0x9a19c : word) = Some W_99d84.
Proof. vm_refl. Qed.
Lemma D_99d84 : decode_any W_99d84 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d88 : bv 32 := 0x00b5252f.
Lemma F_99d88 : fetch_word AsanUbsan.M.loaded_segments (0x9a1a0 : word) = Some W_99d88.
Proof. vm_refl. Qed.
Lemma D_99d88 : decode_any W_99d88 = Some (Amo AMO_ADD AW false false 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d8c : bv 32 := 0x0015051b.
Lemma F_99d8c : fetch_word AsanUbsan.M.loaded_segments (0x9a1a4 : word) = Some W_99d8c.
Proof. vm_refl. Qed.
Lemma D_99d8c : decode_any W_99d8c = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d90 : bv 32 := 0x02051493.
Lemma F_99d90 : fetch_word AsanUbsan.M.loaded_segments (0x9a1a8 : word) = Some W_99d90.
Proof. vm_refl. Qed.
Lemma D_99d90 : decode_any W_99d90 = Some (ShiftImm ALU_SLL 9 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d94 : bv 32 := 0x0204d493.
Lemma F_99d94 : fetch_word AsanUbsan.M.loaded_segments (0x9a1ac : word) = Some W_99d94.
Proof. vm_refl. Qed.
Lemma D_99d94 : decode_any W_99d94 = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d98 : bv 32 := 0x08054663.
Lemma F_99d98 : fetch_word AsanUbsan.M.loaded_segments (0x9a1b0 : word) = Some W_99d98.
Proof. vm_refl. Qed.
Lemma D_99d98 : decode_any W_99d98 = Some (Branch BC_LT 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99d9c : bv 32 := 0x00050b93.
Lemma F_99d9c : fetch_word AsanUbsan.M.loaded_segments (0x9a1b4 : word) = Some W_99d9c.
Proof. vm_refl. Qed.
Lemma D_99d9c : decode_any W_99d9c = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99da0 : bv 32 := 0x0104d593.
Lemma F_99da0 : fetch_word AsanUbsan.M.loaded_segments (0x9a1b8 : word) = Some W_99da0.
Proof. vm_refl. Qed.
Lemma D_99da0 : decode_any W_99da0 = Some (ShiftImm ALU_SRL 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99da4 : bv 32 := 0x00359513.
Lemma F_99da4 : fetch_word AsanUbsan.M.loaded_segments (0x9a1bc : word) = Some W_99da4.
Proof. vm_refl. Qed.
Lemma D_99da4 : decode_any W_99da4 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99da8 : bv 32 := 0x00ac0533.
Lemma F_99da8 : fetch_word AsanUbsan.M.loaded_segments (0x9a1c0 : word) = Some W_99da8.
Proof. vm_refl. Qed.
Lemma D_99da8 : decode_any W_99da8 = Some (Op ALU_ADD 10 24 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99dac : bv 32 := 0x00053503.
Lemma F_99dac : fetch_word AsanUbsan.M.loaded_segments (0x9a1c4 : word) = Some W_99dac.
Proof. vm_refl. Qed.
Lemma D_99dac : decode_any W_99dac = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99db0 : bv 32 := 0x08050a63.
Lemma F_99db0 : fetch_word AsanUbsan.M.loaded_segments (0x9a1c8 : word) = Some W_99db0.
Proof. vm_refl. Qed.
Lemma D_99db0 : decode_any W_99db0 = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99db4 : bv 32 := 0x0164f5b3.
Lemma F_99db4 : fetch_word AsanUbsan.M.loaded_segments (0x9a1cc : word) = Some W_99db4.
Proof. vm_refl. Qed.
Lemma D_99db4 : decode_any W_99db4 = Some (Op ALU_AND 11 9 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99db8 : bv 32 := 0x00459593.
Lemma F_99db8 : fetch_word AsanUbsan.M.loaded_segments (0x9a1d0 : word) = Some W_99db8.
Proof. vm_refl. Qed.
Lemma D_99db8 : decode_any W_99db8 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99dbc : bv 32 := 0x00b504b3.
Lemma F_99dbc : fetch_word AsanUbsan.M.loaded_segments (0x9a1d4 : word) = Some W_99dbc.
Proof. vm_refl. Qed.
Lemma D_99dbc : decode_any W_99dbc = Some (Op ALU_ADD 9 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99dc0 : bv 32 := 0x00810613.
Lemma F_99dc0 : fetch_word AsanUbsan.M.loaded_segments (0x9a1d8 : word) = Some W_99dc0.
Proof. vm_refl. Qed.
Lemma D_99dc0 : decode_any W_99dc0 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99dc4 : bv 32 := 0x00048513.
Lemma F_99dc4 : fetch_word AsanUbsan.M.loaded_segments (0x9a1dc : word) = Some W_99dc4.
Proof. vm_refl. Qed.
Lemma D_99dc4 : decode_any W_99dc4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99dc8 : bv 32 := 0x00000593.
Lemma F_99dc8 : fetch_word AsanUbsan.M.loaded_segments (0x9a1e0 : word) = Some W_99dc8.
Proof. vm_refl. Qed.
Lemma D_99dc8 : decode_any W_99dc8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99dcc : bv 32 := 0x00098693.
Lemma F_99dcc : fetch_word AsanUbsan.M.loaded_segments (0x9a1e4 : word) = Some W_99dcc.
Proof. vm_refl. Qed.
Lemma D_99dcc : decode_any W_99dcc = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99dd0 : bv 32 := 0xaf5ff0ef.
Lemma F_99dd0 : fetch_word AsanUbsan.M.loaded_segments (0x9a1e8 : word) = Some W_99dd0.
Proof. vm_refl. Qed.
Lemma D_99dd0 : decode_any W_99dd0 = Some (Jal 1 2095860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99dd4 : bv 32 := 0x0154a423.
Lemma F_99dd4 : fetch_word AsanUbsan.M.loaded_segments (0x9a1ec : word) = Some W_99dd4.
Proof. vm_refl. Qed.
Lemma D_99dd4 : decode_any W_99dd4 = Some (Store SZ4 9 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99dd8 : bv 32 := 0x0310000f.
Lemma F_99dd8 : fetch_word AsanUbsan.M.loaded_segments (0x9a1f0 : word) = Some W_99dd8.
Proof. vm_refl. Qed.
Lemma D_99dd8 : decode_any W_99dd8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99ddc : bv 32 := 0x000b8513.
Lemma F_99ddc : fetch_word AsanUbsan.M.loaded_segments (0x9a1f4 : word) = Some W_99ddc.
Proof. vm_refl. Qed.
Lemma D_99ddc : decode_any W_99ddc = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99de0 : bv 32 := 0x01792023.
Lemma F_99de0 : fetch_word AsanUbsan.M.loaded_segments (0x9a1f8 : word) = Some W_99de0.
Proof. vm_refl. Qed.
Lemma D_99de0 : decode_any W_99de0 = Some (Store SZ4 18 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99de4 : bv 32 := 0x00040663.
Lemma F_99de4 : fetch_word AsanUbsan.M.loaded_segments (0x9a1fc : word) = Some W_99de4.
Proof. vm_refl. Qed.
Lemma D_99de4 : decode_any W_99de4 = Some (Branch BC_EQ 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99df0 : bv 32 := 0x06813083.
Lemma F_99df0 : fetch_word AsanUbsan.M.loaded_segments (0x9a208 : word) = Some W_99df0.
Proof. vm_refl. Qed.
Lemma D_99df0 : decode_any W_99df0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99df4 : bv 32 := 0x06013403.
Lemma F_99df4 : fetch_word AsanUbsan.M.loaded_segments (0x9a20c : word) = Some W_99df4.
Proof. vm_refl. Qed.
Lemma D_99df4 : decode_any W_99df4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99df8 : bv 32 := 0x05813483.
Lemma F_99df8 : fetch_word AsanUbsan.M.loaded_segments (0x9a210 : word) = Some W_99df8.
Proof. vm_refl. Qed.
Lemma D_99df8 : decode_any W_99df8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99dfc : bv 32 := 0x05013903.
Lemma F_99dfc : fetch_word AsanUbsan.M.loaded_segments (0x9a214 : word) = Some W_99dfc.
Proof. vm_refl. Qed.
Lemma D_99dfc : decode_any W_99dfc = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e00 : bv 32 := 0x04813983.
Lemma F_99e00 : fetch_word AsanUbsan.M.loaded_segments (0x9a218 : word) = Some W_99e00.
Proof. vm_refl. Qed.
Lemma D_99e00 : decode_any W_99e00 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e04 : bv 32 := 0x04013a03.
Lemma F_99e04 : fetch_word AsanUbsan.M.loaded_segments (0x9a21c : word) = Some W_99e04.
Proof. vm_refl. Qed.
Lemma D_99e04 : decode_any W_99e04 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e08 : bv 32 := 0x03813a83.
Lemma F_99e08 : fetch_word AsanUbsan.M.loaded_segments (0x9a220 : word) = Some W_99e08.
Proof. vm_refl. Qed.
Lemma D_99e08 : decode_any W_99e08 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e0c : bv 32 := 0x03013b03.
Lemma F_99e0c : fetch_word AsanUbsan.M.loaded_segments (0x9a224 : word) = Some W_99e0c.
Proof. vm_refl. Qed.
Lemma D_99e0c : decode_any W_99e0c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e10 : bv 32 := 0x02813b83.
Lemma F_99e10 : fetch_word AsanUbsan.M.loaded_segments (0x9a228 : word) = Some W_99e10.
Proof. vm_refl. Qed.
Lemma D_99e10 : decode_any W_99e10 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e14 : bv 32 := 0x02013c03.
Lemma F_99e14 : fetch_word AsanUbsan.M.loaded_segments (0x9a22c : word) = Some W_99e14.
Proof. vm_refl. Qed.
Lemma D_99e14 : decode_any W_99e14 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e18 : bv 32 := 0x01813c83.
Lemma F_99e18 : fetch_word AsanUbsan.M.loaded_segments (0x9a230 : word) = Some W_99e18.
Proof. vm_refl. Qed.
Lemma D_99e18 : decode_any W_99e18 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e1c : bv 32 := 0x07010113.
Lemma F_99e1c : fetch_word AsanUbsan.M.loaded_segments (0x9a234 : word) = Some W_99e1c.
Proof. vm_refl. Qed.
Lemma D_99e1c : decode_any W_99e1c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99e20 : bv 32 := 0x00008067.
Lemma F_99e20 : fetch_word AsanUbsan.M.loaded_segments (0x9a238 : word) = Some W_99e20.
Proof. vm_refl. Qed.
Lemma D_99e20 : decode_any W_99e20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
