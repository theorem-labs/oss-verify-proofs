(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9b120 : bv 32 := 0x00058613.
Lemma F_9b120 : fetch_word AsanUbsan.M.loaded_segments (0x9b170 : word) = Some W_9b120.
Proof. vm_refl. Qed.
Lemma D_9b120 : decode_any W_9b120 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b124 : bv 32 := 0x0018d597.
Lemma F_9b124 : fetch_word AsanUbsan.M.loaded_segments (0x9b174 : word) = Some W_9b124.
Proof. vm_refl. Qed.
Lemma D_9b124 : decode_any W_9b124 = Some (Auipc 11 397, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b128 : bv 32 := 0xe6458593.
Lemma F_9b128 : fetch_word AsanUbsan.M.loaded_segments (0x9b178 : word) = Some W_9b128.
Proof. vm_refl. Qed.
Lemma D_9b128 : decode_any W_9b128 = Some (OpImm ALU_ADD 11 11 3684, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b12c : bv 32 := 0x00050693.
Lemma F_9b12c : fetch_word AsanUbsan.M.loaded_segments (0x9b17c : word) = Some W_9b12c.
Proof. vm_refl. Qed.
Lemma D_9b12c : decode_any W_9b12c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b130 : bv 32 := 0x00058513.
Lemma F_9b130 : fetch_word AsanUbsan.M.loaded_segments (0x9b180 : word) = Some W_9b130.
Proof. vm_refl. Qed.
Lemma D_9b130 : decode_any W_9b130 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b134 : bv 32 := 0x00068593.
Lemma F_9b134 : fetch_word AsanUbsan.M.loaded_segments (0x9b184 : word) = Some W_9b134.
Proof. vm_refl. Qed.
Lemma D_9b134 : decode_any W_9b134 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b138 : bv 32 := 0x00000693.
Lemma F_9b138 : fetch_word AsanUbsan.M.loaded_segments (0x9b188 : word) = Some W_9b138.
Proof. vm_refl. Qed.
Lemma D_9b138 : decode_any W_9b138 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b13c : bv 32 := 0x0040006f.
Lemma F_9b13c : fetch_word AsanUbsan.M.loaded_segments (0x9b18c : word) = Some W_9b13c.
Proof. vm_refl. Qed.
Lemma D_9b13c : decode_any W_9b13c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b140 : bv 32 := 0xf9010113.
Lemma F_9b140 : fetch_word AsanUbsan.M.loaded_segments (0x9b190 : word) = Some W_9b140.
Proof. vm_refl. Qed.
Lemma D_9b140 : decode_any W_9b140 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b144 : bv 32 := 0x06113423.
Lemma F_9b144 : fetch_word AsanUbsan.M.loaded_segments (0x9b194 : word) = Some W_9b144.
Proof. vm_refl. Qed.
Lemma D_9b144 : decode_any W_9b144 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b148 : bv 32 := 0x06813023.
Lemma F_9b148 : fetch_word AsanUbsan.M.loaded_segments (0x9b198 : word) = Some W_9b148.
Proof. vm_refl. Qed.
Lemma D_9b148 : decode_any W_9b148 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b14c : bv 32 := 0x04913c23.
Lemma F_9b14c : fetch_word AsanUbsan.M.loaded_segments (0x9b19c : word) = Some W_9b14c.
Proof. vm_refl. Qed.
Lemma D_9b14c : decode_any W_9b14c = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b150 : bv 32 := 0x05213823.
Lemma F_9b150 : fetch_word AsanUbsan.M.loaded_segments (0x9b1a0 : word) = Some W_9b150.
Proof. vm_refl. Qed.
Lemma D_9b150 : decode_any W_9b150 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b154 : bv 32 := 0x05313423.
Lemma F_9b154 : fetch_word AsanUbsan.M.loaded_segments (0x9b1a4 : word) = Some W_9b154.
Proof. vm_refl. Qed.
Lemma D_9b154 : decode_any W_9b154 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b158 : bv 32 := 0x05413023.
Lemma F_9b158 : fetch_word AsanUbsan.M.loaded_segments (0x9b1a8 : word) = Some W_9b158.
Proof. vm_refl. Qed.
Lemma D_9b158 : decode_any W_9b158 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b15c : bv 32 := 0x03513c23.
Lemma F_9b15c : fetch_word AsanUbsan.M.loaded_segments (0x9b1ac : word) = Some W_9b15c.
Proof. vm_refl. Qed.
Lemma D_9b15c : decode_any W_9b15c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b160 : bv 32 := 0x03613823.
Lemma F_9b160 : fetch_word AsanUbsan.M.loaded_segments (0x9b1b0 : word) = Some W_9b160.
Proof. vm_refl. Qed.
Lemma D_9b160 : decode_any W_9b160 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b164 : bv 32 := 0x03713423.
Lemma F_9b164 : fetch_word AsanUbsan.M.loaded_segments (0x9b1b4 : word) = Some W_9b164.
Proof. vm_refl. Qed.
Lemma D_9b164 : decode_any W_9b164 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b168 : bv 32 := 0x03813023.
Lemma F_9b168 : fetch_word AsanUbsan.M.loaded_segments (0x9b1b8 : word) = Some W_9b168.
Proof. vm_refl. Qed.
Lemma D_9b168 : decode_any W_9b168 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b16c : bv 32 := 0x01913c23.
Lemma F_9b16c : fetch_word AsanUbsan.M.loaded_segments (0x9b1bc : word) = Some W_9b16c.
Proof. vm_refl. Qed.
Lemma D_9b16c : decode_any W_9b16c = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b170 : bv 32 := 0x00068413.
Lemma F_9b170 : fetch_word AsanUbsan.M.loaded_segments (0x9b1c0 : word) = Some W_9b170.
Proof. vm_refl. Qed.
Lemma D_9b170 : decode_any W_9b170 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b174 : bv 32 := 0x00050493.
Lemma F_9b174 : fetch_word AsanUbsan.M.loaded_segments (0x9b1c4 : word) = Some W_9b174.
Proof. vm_refl. Qed.
Lemma D_9b174 : decode_any W_9b174 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b178 : bv 32 := 0x00b13423.
Lemma F_9b178 : fetch_word AsanUbsan.M.loaded_segments (0x9b1c8 : word) = Some W_9b178.
Proof. vm_refl. Qed.
Lemma D_9b178 : decode_any W_9b178 = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b17c : bv 32 := 0x00c13823.
Lemma F_9b17c : fetch_word AsanUbsan.M.loaded_segments (0x9b1cc : word) = Some W_9b17c.
Proof. vm_refl. Qed.
Lemma D_9b17c : decode_any W_9b17c = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b180 : bv 32 := 0x00068463.
Lemma F_9b180 : fetch_word AsanUbsan.M.loaded_segments (0x9b1d0 : word) = Some W_9b180.
Proof. vm_refl. Qed.
Lemma D_9b180 : decode_any W_9b180 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b188 : bv 32 := 0x0006069b.
Lemma F_9b188 : fetch_word AsanUbsan.M.loaded_segments (0x9b1d8 : word) = Some W_9b188.
Proof. vm_refl. Qed.
Lemma D_9b188 : decode_any W_9b188 = Some (OpImm32 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b18c : bv 32 := 0x00000513.
Lemma F_9b18c : fetch_word AsanUbsan.M.loaded_segments (0x9b1dc : word) = Some W_9b18c.
Proof. vm_refl. Qed.
Lemma D_9b18c : decode_any W_9b18c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b190 : bv 32 := 0x1c068a63.
Lemma F_9b190 : fetch_word AsanUbsan.M.loaded_segments (0x9b1e0 : word) = Some W_9b190.
Proof. vm_refl. Qed.
Lemma D_9b190 : decode_any W_9b190 = Some (Branch BC_EQ 13 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b194 : bv 32 := 0x1c058863.
Lemma F_9b194 : fetch_word AsanUbsan.M.loaded_segments (0x9b1e4 : word) = Some W_9b194.
Proof. vm_refl. Qed.
Lemma D_9b194 : decode_any W_9b194 = Some (Branch BC_EQ 11 0 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b198 : bv 32 := 0x02065693.
Lemma F_9b198 : fetch_word AsanUbsan.M.loaded_segments (0x9b1e8 : word) = Some W_9b198.
Proof. vm_refl. Qed.
Lemma D_9b198 : decode_any W_9b198 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b19c : bv 32 := 0xfff00513.
Lemma F_9b19c : fetch_word AsanUbsan.M.loaded_segments (0x9b1ec : word) = Some W_9b19c.
Proof. vm_refl. Qed.
Lemma D_9b19c : decode_any W_9b19c = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1a0 : bv 32 := 0xfff75717.
Lemma F_9b1a0 : fetch_word AsanUbsan.M.loaded_segments (0x9b1f0 : word) = Some W_9b1a0.
Proof. vm_refl. Qed.
Lemma D_9b1a0 : decode_any W_9b1a0 = Some (Auipc 14 1048437, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1a4 : bv 32 := 0xfff75797.
Lemma F_9b1a4 : fetch_word AsanUbsan.M.loaded_segments (0x9b1f4 : word) = Some W_9b1a4.
Proof. vm_refl. Qed.
Lemma D_9b1a4 : decode_any W_9b1a4 = Some (Auipc 15 1048437, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1a8 : bv 32 := 0x02055513.
Lemma F_9b1a8 : fetch_word AsanUbsan.M.loaded_segments (0x9b1f8 : word) = Some W_9b1a8.
Proof. vm_refl. Qed.
Lemma D_9b1a8 : decode_any W_9b1a8 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1ac : bv 32 := 0x12c7b783.
Lemma F_9b1ac : fetch_word AsanUbsan.M.loaded_segments (0x9b1fc : word) = Some W_9b1ac.
Proof. vm_refl. Qed.
Lemma D_9b1ac : decode_any W_9b1ac = Some (Load SZ8 true 15 15 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1b0 : bv 32 := 0x00a67633.
Lemma F_9b1b0 : fetch_word AsanUbsan.M.loaded_segments (0x9b200 : word) = Some W_9b1b0.
Proof. vm_refl. Qed.
Lemma D_9b1b0 : decode_any W_9b1b0 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1b4 : bv 32 := 0xfff75517.
Lemma F_9b1b4 : fetch_word AsanUbsan.M.loaded_segments (0x9b204 : word) = Some W_9b1b4.
Proof. vm_refl. Qed.
Lemma D_9b1b4 : decode_any W_9b1b4 = Some (Auipc 10 1048437, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1b8 : bv 32 := 0x22453803.
Lemma F_9b1b8 : fetch_word AsanUbsan.M.loaded_segments (0x9b208 : word) = Some W_9b1b8.
Proof. vm_refl. Qed.
Lemma D_9b1b8 : decode_any W_9b1b8 = Some (Load SZ8 true 16 10 548, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1bc : bv 32 := 0x0f873503.
Lemma F_9b1bc : fetch_word AsanUbsan.M.loaded_segments (0x9b20c : word) = Some W_9b1bc.
Proof. vm_refl. Qed.
Lemma D_9b1bc : decode_any W_9b1bc = Some (Load SZ8 true 10 14 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1c0 : bv 32 := 0x02f60733.
Lemma F_9b1c0 : fetch_word AsanUbsan.M.loaded_segments (0x9b210 : word) = Some W_9b1c0.
Proof. vm_refl. Qed.
Lemma D_9b1c0 : decode_any W_9b1c0 = Some (Mul M_MUL 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1c4 : bv 32 := 0x00361793.
Lemma F_9b1c4 : fetch_word AsanUbsan.M.loaded_segments (0x9b214 : word) = Some W_9b1c4.
Proof. vm_refl. Qed.
Lemma D_9b1c4 : decode_any W_9b1c4 = Some (ShiftImm ALU_SLL 15 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1c8 : bv 32 := 0x01074633.
Lemma F_9b1c8 : fetch_word AsanUbsan.M.loaded_segments (0x9b218 : word) = Some W_9b1c8.
Proof. vm_refl. Qed.
Lemma D_9b1c8 : decode_any W_9b1c8 = Some (Op ALU_XOR 12 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1cc : bv 32 := 0x00f58733.
Lemma F_9b1cc : fetch_word AsanUbsan.M.loaded_segments (0x9b21c : word) = Some W_9b1cc.
Proof. vm_refl. Qed.
Lemma D_9b1cc : decode_any W_9b1cc = Some (Op ALU_ADD 14 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1d0 : bv 32 := 0x0005b783.
Lemma F_9b1d0 : fetch_word AsanUbsan.M.loaded_segments (0x9b220 : word) = Some W_9b1d0.
Proof. vm_refl. Qed.
Lemma D_9b1d0 : decode_any W_9b1d0 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1d4 : bv 32 := 0x00858593.
Lemma F_9b1d4 : fetch_word AsanUbsan.M.loaded_segments (0x9b224 : word) = Some W_9b1d4.
Proof. vm_refl. Qed.
Lemma D_9b1d4 : decode_any W_9b1d4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1d8 : bv 32 := 0x02a787b3.
Lemma F_9b1d8 : fetch_word AsanUbsan.M.loaded_segments (0x9b228 : word) = Some W_9b1d8.
Proof. vm_refl. Qed.
Lemma D_9b1d8 : decode_any W_9b1d8 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1dc : bv 32 := 0x02f7d813.
Lemma F_9b1dc : fetch_word AsanUbsan.M.loaded_segments (0x9b22c : word) = Some W_9b1dc.
Proof. vm_refl. Qed.
Lemma D_9b1dc : decode_any W_9b1dc = Some (ShiftImm ALU_SRL 16 15 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1e0 : bv 32 := 0x00f847b3.
Lemma F_9b1e0 : fetch_word AsanUbsan.M.loaded_segments (0x9b230 : word) = Some W_9b1e0.
Proof. vm_refl. Qed.
Lemma D_9b1e0 : decode_any W_9b1e0 = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1e4 : bv 32 := 0x02a787b3.
Lemma F_9b1e4 : fetch_word AsanUbsan.M.loaded_segments (0x9b234 : word) = Some W_9b1e4.
Proof. vm_refl. Qed.
Lemma D_9b1e4 : decode_any W_9b1e4 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1e8 : bv 32 := 0x00c7c633.
Lemma F_9b1e8 : fetch_word AsanUbsan.M.loaded_segments (0x9b238 : word) = Some W_9b1e8.
Proof. vm_refl. Qed.
Lemma D_9b1e8 : decode_any W_9b1e8 = Some (Op ALU_XOR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1ec : bv 32 := 0x02a60633.
Lemma F_9b1ec : fetch_word AsanUbsan.M.loaded_segments (0x9b23c : word) = Some W_9b1ec.
Proof. vm_refl. Qed.
Lemma D_9b1ec : decode_any W_9b1ec = Some (Mul M_MUL 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1f0 : bv 32 := 0xfee590e3.
Lemma F_9b1f0 : fetch_word AsanUbsan.M.loaded_segments (0x9b240 : word) = Some W_9b1f0.
Proof. vm_refl. Qed.
Lemma D_9b1f0 : decode_any W_9b1f0 = Some (Branch BC_NE 11 14 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1f4 : bv 32 := 0x00010b37.
Lemma F_9b1f4 : fetch_word AsanUbsan.M.loaded_segments (0x9b244 : word) = Some W_9b1f4.
Proof. vm_refl. Qed.
Lemma D_9b1f4 : decode_any W_9b1f4 = Some (Lui 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1f8 : bv 32 := 0x80000bb7.
Lemma F_9b1f8 : fetch_word AsanUbsan.M.loaded_segments (0x9b248 : word) = Some W_9b1f8.
Proof. vm_refl. Qed.
Lemma D_9b1f8 : decode_any W_9b1f8 = Some (Lui 23 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b1fc : bv 32 := 0x02a685b3.
Lemma F_9b1fc : fetch_word AsanUbsan.M.loaded_segments (0x9b24c : word) = Some W_9b1fc.
Proof. vm_refl. Qed.
Lemma D_9b1fc : decode_any W_9b1fc = Some (Mul M_MUL 11 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b200 : bv 32 := 0x004006b7.
Lemma F_9b200 : fetch_word AsanUbsan.M.loaded_segments (0x9b250 : word) = Some W_9b200.
Proof. vm_refl. Qed.
Lemma D_9b200 : decode_any W_9b200 = Some (Lui 13 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b204 : bv 32 := 0xfffb0b1b.
Lemma F_9b204 : fetch_word AsanUbsan.M.loaded_segments (0x9b254 : word) = Some W_9b204.
Proof. vm_refl. Qed.
Lemma D_9b204 : decode_any W_9b204 = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b208 : bv 32 := 0xfffb8b9b.
Lemma F_9b208 : fetch_word AsanUbsan.M.loaded_segments (0x9b258 : word) = Some W_9b208.
Proof. vm_refl. Qed.
Lemma D_9b208 : decode_any W_9b208 = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b20c : bv 32 := 0x02f5d713.
Lemma F_9b20c : fetch_word AsanUbsan.M.loaded_segments (0x9b25c : word) = Some W_9b20c.
Proof. vm_refl. Qed.
Lemma D_9b20c : decode_any W_9b20c = Some (ShiftImm ALU_SRL 14 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b210 : bv 32 := 0x00b745b3.
Lemma F_9b210 : fetch_word AsanUbsan.M.loaded_segments (0x9b260 : word) = Some W_9b210.
Proof. vm_refl. Qed.
Lemma D_9b210 : decode_any W_9b210 = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b214 : bv 32 := 0x02a585b3.
Lemma F_9b214 : fetch_word AsanUbsan.M.loaded_segments (0x9b264 : word) = Some W_9b214.
Proof. vm_refl. Qed.
Lemma D_9b214 : decode_any W_9b214 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b218 : bv 32 := 0x00c5c5b3.
Lemma F_9b218 : fetch_word AsanUbsan.M.loaded_segments (0x9b268 : word) = Some W_9b218.
Proof. vm_refl. Qed.
Lemma D_9b218 : decode_any W_9b218 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b21c : bv 32 := 0x02a585b3.
Lemma F_9b21c : fetch_word AsanUbsan.M.loaded_segments (0x9b26c : word) = Some W_9b21c.
Proof. vm_refl. Qed.
Lemma D_9b21c : decode_any W_9b21c = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b220 : bv 32 := 0x02f5d613.
Lemma F_9b220 : fetch_word AsanUbsan.M.loaded_segments (0x9b270 : word) = Some W_9b220.
Proof. vm_refl. Qed.
Lemma D_9b220 : decode_any W_9b220 = Some (ShiftImm ALU_SRL 12 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b224 : bv 32 := 0x00b645b3.
Lemma F_9b224 : fetch_word AsanUbsan.M.loaded_segments (0x9b274 : word) = Some W_9b224.
Proof. vm_refl. Qed.
Lemma D_9b224 : decode_any W_9b224 = Some (Op ALU_XOR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b228 : bv 32 := 0x02a58533.
Lemma F_9b228 : fetch_word AsanUbsan.M.loaded_segments (0x9b278 : word) = Some W_9b228.
Proof. vm_refl. Qed.
Lemma D_9b228 : decode_any W_9b228 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b22c : bv 32 := 0x02f55593.
Lemma F_9b22c : fetch_word AsanUbsan.M.loaded_segments (0x9b27c : word) = Some W_9b22c.
Proof. vm_refl. Qed.
Lemma D_9b22c : decode_any W_9b22c = Some (ShiftImm ALU_SRL 11 10 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b230 : bv 32 := 0x00a5c9b3.
Lemma F_9b230 : fetch_word AsanUbsan.M.loaded_segments (0x9b280 : word) = Some W_9b230.
Proof. vm_refl. Qed.
Lemma D_9b230 : decode_any W_9b230 = Some (Op ALU_XOR 19 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b234 : bv 32 := 0x02c99513.
Lemma F_9b234 : fetch_word AsanUbsan.M.loaded_segments (0x9b284 : word) = Some W_9b234.
Proof. vm_refl. Qed.
Lemma D_9b234 : decode_any W_9b234 = Some (ShiftImm ALU_SLL 10 19 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b238 : bv 32 := 0x02a55513.
Lemma F_9b238 : fetch_word AsanUbsan.M.loaded_segments (0x9b288 : word) = Some W_9b238.
Proof. vm_refl. Qed.
Lemma D_9b238 : decode_any W_9b238 = Some (ShiftImm ALU_SRL 10 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b23c : bv 32 := 0x00a48933.
Lemma F_9b23c : fetch_word AsanUbsan.M.loaded_segments (0x9b28c : word) = Some W_9b23c.
Proof. vm_refl. Qed.
Lemma D_9b23c : decode_any W_9b23c = Some (Op ALU_ADD 18 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b240 : bv 32 := 0x00092503.
Lemma F_9b240 : fetch_word AsanUbsan.M.loaded_segments (0x9b290 : word) = Some W_9b240.
Proof. vm_refl. Qed.
Lemma D_9b240 : decode_any W_9b240 = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b244 : bv 32 := 0x01068c1b.
Lemma F_9b244 : fetch_word AsanUbsan.M.loaded_segments (0x9b294 : word) = Some W_9b244.
Proof. vm_refl. Qed.
Lemma D_9b244 : decode_any W_9b244 = Some (OpImm32 24 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b248 : bv 32 := 0x01848c33.
Lemma F_9b248 : fetch_word AsanUbsan.M.loaded_segments (0x9b298 : word) = Some W_9b248.
Proof. vm_refl. Qed.
Lemma D_9b248 : decode_any W_9b248 = Some (Op ALU_ADD 24 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b24c : bv 32 := 0x0230000f.
Lemma F_9b24c : fetch_word AsanUbsan.M.loaded_segments (0x9b29c : word) = Some W_9b24c.
Proof. vm_refl. Qed.
Lemma D_9b24c : decode_any W_9b24c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b250 : bv 32 := 0x01757cb3.
Lemma F_9b250 : fetch_word AsanUbsan.M.loaded_segments (0x9b2a0 : word) = Some W_9b250.
Proof. vm_refl. Qed.
Lemma D_9b250 : decode_any W_9b250 = Some (Op ALU_AND 25 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b254 : bv 32 := 0x0086869b.
Lemma F_9b254 : fetch_word AsanUbsan.M.loaded_segments (0x9b2a4 : word) = Some W_9b254.
Proof. vm_refl. Qed.
Lemma D_9b254 : decode_any W_9b254 = Some (OpImm32 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b258 : bv 32 := 0x00d48a33.
Lemma F_9b258 : fetch_word AsanUbsan.M.loaded_segments (0x9b2a8 : word) = Some W_9b258.
Proof. vm_refl. Qed.
Lemma D_9b258 : decode_any W_9b258 = Some (Op ALU_ADD 20 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b25c : bv 32 := 0x000c8593.
Lemma F_9b25c : fetch_word AsanUbsan.M.loaded_segments (0x9b2ac : word) = Some W_9b25c.
Proof. vm_refl. Qed.
Lemma D_9b25c : decode_any W_9b25c = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b260 : bv 32 := 0x04058c63.
Lemma F_9b260 : fetch_word AsanUbsan.M.loaded_segments (0x9b2b0 : word) = Some W_9b260.
Proof. vm_refl. Qed.
Lemma D_9b260 : decode_any W_9b260 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b264 : bv 32 := 0x00058513.
Lemma F_9b264 : fetch_word AsanUbsan.M.loaded_segments (0x9b2b4 : word) = Some W_9b264.
Proof. vm_refl. Qed.
Lemma D_9b264 : decode_any W_9b264 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b268 : bv 32 := 0x0105d59b.
Lemma F_9b268 : fetch_word AsanUbsan.M.loaded_segments (0x9b2b8 : word) = Some W_9b268.
Proof. vm_refl. Qed.
Lemma D_9b268 : decode_any W_9b268 = Some (ShiftImm32 ALU_SRL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b26c : bv 32 := 0x00359613.
Lemma F_9b26c : fetch_word AsanUbsan.M.loaded_segments (0x9b2bc : word) = Some W_9b26c.
Proof. vm_refl. Qed.
Lemma D_9b26c : decode_any W_9b26c = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b270 : bv 32 := 0x00cc0633.
Lemma F_9b270 : fetch_word AsanUbsan.M.loaded_segments (0x9b2c0 : word) = Some W_9b270.
Proof. vm_refl. Qed.
Lemma D_9b270 : decode_any W_9b270 = Some (Op ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b274 : bv 32 := 0x00063603.
Lemma F_9b274 : fetch_word AsanUbsan.M.loaded_segments (0x9b2c4 : word) = Some W_9b274.
Proof. vm_refl. Qed.
Lemma D_9b274 : decode_any W_9b274 = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b278 : bv 32 := 0x02060463.
Lemma F_9b278 : fetch_word AsanUbsan.M.loaded_segments (0x9b2c8 : word) = Some W_9b278.
Proof. vm_refl. Qed.
Lemma D_9b278 : decode_any W_9b278 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b27c : bv 32 := 0x02051593.
Lemma F_9b27c : fetch_word AsanUbsan.M.loaded_segments (0x9b2cc : word) = Some W_9b27c.
Proof. vm_refl. Qed.
Lemma D_9b27c : decode_any W_9b27c = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b280 : bv 32 := 0x0205d593.
Lemma F_9b280 : fetch_word AsanUbsan.M.loaded_segments (0x9b2d0 : word) = Some W_9b280.
Proof. vm_refl. Qed.
Lemma D_9b280 : decode_any W_9b280 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b284 : bv 32 := 0x0165f5b3.
Lemma F_9b284 : fetch_word AsanUbsan.M.loaded_segments (0x9b2d4 : word) = Some W_9b284.
Proof. vm_refl. Qed.
Lemma D_9b284 : decode_any W_9b284 = Some (Op ALU_AND 11 11 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b288 : bv 32 := 0x00459593.
Lemma F_9b288 : fetch_word AsanUbsan.M.loaded_segments (0x9b2d8 : word) = Some W_9b288.
Proof. vm_refl. Qed.
Lemma D_9b288 : decode_any W_9b288 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b28c : bv 32 := 0x00b605b3.
Lemma F_9b28c : fetch_word AsanUbsan.M.loaded_segments (0x9b2dc : word) = Some W_9b28c.
Proof. vm_refl. Qed.
Lemma D_9b28c : decode_any W_9b28c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b290 : bv 32 := 0x0005b603.
Lemma F_9b290 : fetch_word AsanUbsan.M.loaded_segments (0x9b2e0 : word) = Some W_9b290.
Proof. vm_refl. Qed.
Lemma D_9b290 : decode_any W_9b290 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b294 : bv 32 := 0x0085a583.
Lemma F_9b294 : fetch_word AsanUbsan.M.loaded_segments (0x9b2e4 : word) = Some W_9b294.
Proof. vm_refl. Qed.
Lemma D_9b294 : decode_any W_9b294 = Some (Load SZ4 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b298 : bv 32 := 0xfcc994e3.
Lemma F_9b298 : fetch_word AsanUbsan.M.loaded_segments (0x9b2e8 : word) = Some W_9b298.
Proof. vm_refl. Qed.
Lemma D_9b298 : decode_any W_9b298 = Some (Branch BC_NE 19 12 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b29c : bv 32 := 0x0c80006f.
Lemma F_9b29c : fetch_word AsanUbsan.M.loaded_segments (0x9b2ec : word) = Some W_9b29c.
Proof. vm_refl. Qed.
Lemma D_9b29c : decode_any W_9b29c = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2b8 : bv 32 := 0x00090513.
Lemma F_9b2b8 : fetch_word AsanUbsan.M.loaded_segments (0x9b308 : word) = Some W_9b2b8.
Proof. vm_refl. Qed.
Lemma D_9b2b8 : decode_any W_9b2b8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2bc : bv 32 := 0x5f8000ef.
Lemma F_9b2bc : fetch_word AsanUbsan.M.loaded_segments (0x9b30c : word) = Some W_9b2bc.
Proof. vm_refl. Qed.
Lemma D_9b2bc : decode_any W_9b2bc = Some (Jal 1 1528, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2c0 : bv 32 := 0x00050a93.
Lemma F_9b2c0 : fetch_word AsanUbsan.M.loaded_segments (0x9b310 : word) = Some W_9b2c0.
Proof. vm_refl. Qed.
Lemma D_9b2c0 : decode_any W_9b2c0 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2c4 : bv 32 := 0x03950663.
Lemma F_9b2c4 : fetch_word AsanUbsan.M.loaded_segments (0x9b314 : word) = Some W_9b2c4.
Proof. vm_refl. Qed.
Lemma D_9b2c4 : decode_any W_9b2c4 = Some (Branch BC_EQ 10 25 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2f0 : bv 32 := 0x00400537.
Lemma F_9b2f0 : fetch_word AsanUbsan.M.loaded_segments (0x9b340 : word) = Some W_9b2f0.
Proof. vm_refl. Qed.
Lemma D_9b2f0 : decode_any W_9b2f0 = Some (Lui 10 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2f4 : bv 32 := 0x00a48533.
Lemma F_9b2f4 : fetch_word AsanUbsan.M.loaded_segments (0x9b344 : word) = Some W_9b2f4.
Proof. vm_refl. Qed.
Lemma D_9b2f4 : decode_any W_9b2f4 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2f8 : bv 32 := 0x00100593.
Lemma F_9b2f8 : fetch_word AsanUbsan.M.loaded_segments (0x9b348 : word) = Some W_9b2f8.
Proof. vm_refl. Qed.
Lemma D_9b2f8 : decode_any W_9b2f8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2fc : bv 32 := 0x00b5252f.
Lemma F_9b2fc : fetch_word AsanUbsan.M.loaded_segments (0x9b34c : word) = Some W_9b2fc.
Proof. vm_refl. Qed.
Lemma D_9b2fc : decode_any W_9b2fc = Some (Amo AMO_ADD AW false false 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b300 : bv 32 := 0x0015051b.
Lemma F_9b300 : fetch_word AsanUbsan.M.loaded_segments (0x9b350 : word) = Some W_9b300.
Proof. vm_refl. Qed.
Lemma D_9b300 : decode_any W_9b300 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b304 : bv 32 := 0x02051493.
Lemma F_9b304 : fetch_word AsanUbsan.M.loaded_segments (0x9b354 : word) = Some W_9b304.
Proof. vm_refl. Qed.
Lemma D_9b304 : decode_any W_9b304 = Some (ShiftImm ALU_SLL 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b308 : bv 32 := 0x0204d493.
Lemma F_9b308 : fetch_word AsanUbsan.M.loaded_segments (0x9b358 : word) = Some W_9b308.
Proof. vm_refl. Qed.
Lemma D_9b308 : decode_any W_9b308 = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b30c : bv 32 := 0x08054663.
Lemma F_9b30c : fetch_word AsanUbsan.M.loaded_segments (0x9b35c : word) = Some W_9b30c.
Proof. vm_refl. Qed.
Lemma D_9b30c : decode_any W_9b30c = Some (Branch BC_LT 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b310 : bv 32 := 0x00050b93.
Lemma F_9b310 : fetch_word AsanUbsan.M.loaded_segments (0x9b360 : word) = Some W_9b310.
Proof. vm_refl. Qed.
Lemma D_9b310 : decode_any W_9b310 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b314 : bv 32 := 0x0104d593.
Lemma F_9b314 : fetch_word AsanUbsan.M.loaded_segments (0x9b364 : word) = Some W_9b314.
Proof. vm_refl. Qed.
Lemma D_9b314 : decode_any W_9b314 = Some (ShiftImm ALU_SRL 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b318 : bv 32 := 0x00359513.
Lemma F_9b318 : fetch_word AsanUbsan.M.loaded_segments (0x9b368 : word) = Some W_9b318.
Proof. vm_refl. Qed.
Lemma D_9b318 : decode_any W_9b318 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b31c : bv 32 := 0x00ac0533.
Lemma F_9b31c : fetch_word AsanUbsan.M.loaded_segments (0x9b36c : word) = Some W_9b31c.
Proof. vm_refl. Qed.
Lemma D_9b31c : decode_any W_9b31c = Some (Op ALU_ADD 10 24 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b320 : bv 32 := 0x00053503.
Lemma F_9b320 : fetch_word AsanUbsan.M.loaded_segments (0x9b370 : word) = Some W_9b320.
Proof. vm_refl. Qed.
Lemma D_9b320 : decode_any W_9b320 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b324 : bv 32 := 0x08050a63.
Lemma F_9b324 : fetch_word AsanUbsan.M.loaded_segments (0x9b374 : word) = Some W_9b324.
Proof. vm_refl. Qed.
Lemma D_9b324 : decode_any W_9b324 = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b328 : bv 32 := 0x0164f5b3.
Lemma F_9b328 : fetch_word AsanUbsan.M.loaded_segments (0x9b378 : word) = Some W_9b328.
Proof. vm_refl. Qed.
Lemma D_9b328 : decode_any W_9b328 = Some (Op ALU_AND 11 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b32c : bv 32 := 0x00459593.
Lemma F_9b32c : fetch_word AsanUbsan.M.loaded_segments (0x9b37c : word) = Some W_9b32c.
Proof. vm_refl. Qed.
Lemma D_9b32c : decode_any W_9b32c = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b330 : bv 32 := 0x00b504b3.
Lemma F_9b330 : fetch_word AsanUbsan.M.loaded_segments (0x9b380 : word) = Some W_9b330.
Proof. vm_refl. Qed.
Lemma D_9b330 : decode_any W_9b330 = Some (Op ALU_ADD 9 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b334 : bv 32 := 0x00810613.
Lemma F_9b334 : fetch_word AsanUbsan.M.loaded_segments (0x9b384 : word) = Some W_9b334.
Proof. vm_refl. Qed.
Lemma D_9b334 : decode_any W_9b334 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b338 : bv 32 := 0x00048513.
Lemma F_9b338 : fetch_word AsanUbsan.M.loaded_segments (0x9b388 : word) = Some W_9b338.
Proof. vm_refl. Qed.
Lemma D_9b338 : decode_any W_9b338 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b33c : bv 32 := 0x00000593.
Lemma F_9b33c : fetch_word AsanUbsan.M.loaded_segments (0x9b38c : word) = Some W_9b33c.
Proof. vm_refl. Qed.
Lemma D_9b33c : decode_any W_9b33c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b340 : bv 32 := 0x00098693.
Lemma F_9b340 : fetch_word AsanUbsan.M.loaded_segments (0x9b390 : word) = Some W_9b340.
Proof. vm_refl. Qed.
Lemma D_9b340 : decode_any W_9b340 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b344 : bv 32 := 0xaf5ff0ef.
Lemma F_9b344 : fetch_word AsanUbsan.M.loaded_segments (0x9b394 : word) = Some W_9b344.
Proof. vm_refl. Qed.
Lemma D_9b344 : decode_any W_9b344 = Some (Jal 1 2095860, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b348 : bv 32 := 0x0154a423.
Lemma F_9b348 : fetch_word AsanUbsan.M.loaded_segments (0x9b398 : word) = Some W_9b348.
Proof. vm_refl. Qed.
Lemma D_9b348 : decode_any W_9b348 = Some (Store SZ4 9 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b34c : bv 32 := 0x0310000f.
Lemma F_9b34c : fetch_word AsanUbsan.M.loaded_segments (0x9b39c : word) = Some W_9b34c.
Proof. vm_refl. Qed.
Lemma D_9b34c : decode_any W_9b34c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b350 : bv 32 := 0x000b8513.
Lemma F_9b350 : fetch_word AsanUbsan.M.loaded_segments (0x9b3a0 : word) = Some W_9b350.
Proof. vm_refl. Qed.
Lemma D_9b350 : decode_any W_9b350 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b354 : bv 32 := 0x01792023.
Lemma F_9b354 : fetch_word AsanUbsan.M.loaded_segments (0x9b3a4 : word) = Some W_9b354.
Proof. vm_refl. Qed.
Lemma D_9b354 : decode_any W_9b354 = Some (Store SZ4 18 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b358 : bv 32 := 0x00040663.
Lemma F_9b358 : fetch_word AsanUbsan.M.loaded_segments (0x9b3a8 : word) = Some W_9b358.
Proof. vm_refl. Qed.
Lemma D_9b358 : decode_any W_9b358 = Some (Branch BC_EQ 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b364 : bv 32 := 0x06813083.
Lemma F_9b364 : fetch_word AsanUbsan.M.loaded_segments (0x9b3b4 : word) = Some W_9b364.
Proof. vm_refl. Qed.
Lemma D_9b364 : decode_any W_9b364 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b368 : bv 32 := 0x06013403.
Lemma F_9b368 : fetch_word AsanUbsan.M.loaded_segments (0x9b3b8 : word) = Some W_9b368.
Proof. vm_refl. Qed.
Lemma D_9b368 : decode_any W_9b368 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b36c : bv 32 := 0x05813483.
Lemma F_9b36c : fetch_word AsanUbsan.M.loaded_segments (0x9b3bc : word) = Some W_9b36c.
Proof. vm_refl. Qed.
Lemma D_9b36c : decode_any W_9b36c = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b370 : bv 32 := 0x05013903.
Lemma F_9b370 : fetch_word AsanUbsan.M.loaded_segments (0x9b3c0 : word) = Some W_9b370.
Proof. vm_refl. Qed.
Lemma D_9b370 : decode_any W_9b370 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b374 : bv 32 := 0x04813983.
Lemma F_9b374 : fetch_word AsanUbsan.M.loaded_segments (0x9b3c4 : word) = Some W_9b374.
Proof. vm_refl. Qed.
Lemma D_9b374 : decode_any W_9b374 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b378 : bv 32 := 0x04013a03.
Lemma F_9b378 : fetch_word AsanUbsan.M.loaded_segments (0x9b3c8 : word) = Some W_9b378.
Proof. vm_refl. Qed.
Lemma D_9b378 : decode_any W_9b378 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b37c : bv 32 := 0x03813a83.
Lemma F_9b37c : fetch_word AsanUbsan.M.loaded_segments (0x9b3cc : word) = Some W_9b37c.
Proof. vm_refl. Qed.
Lemma D_9b37c : decode_any W_9b37c = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b380 : bv 32 := 0x03013b03.
Lemma F_9b380 : fetch_word AsanUbsan.M.loaded_segments (0x9b3d0 : word) = Some W_9b380.
Proof. vm_refl. Qed.
Lemma D_9b380 : decode_any W_9b380 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b384 : bv 32 := 0x02813b83.
Lemma F_9b384 : fetch_word AsanUbsan.M.loaded_segments (0x9b3d4 : word) = Some W_9b384.
Proof. vm_refl. Qed.
Lemma D_9b384 : decode_any W_9b384 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b388 : bv 32 := 0x02013c03.
Lemma F_9b388 : fetch_word AsanUbsan.M.loaded_segments (0x9b3d8 : word) = Some W_9b388.
Proof. vm_refl. Qed.
Lemma D_9b388 : decode_any W_9b388 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b38c : bv 32 := 0x01813c83.
Lemma F_9b38c : fetch_word AsanUbsan.M.loaded_segments (0x9b3dc : word) = Some W_9b38c.
Proof. vm_refl. Qed.
Lemma D_9b38c : decode_any W_9b38c = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b390 : bv 32 := 0x07010113.
Lemma F_9b390 : fetch_word AsanUbsan.M.loaded_segments (0x9b3e0 : word) = Some W_9b390.
Proof. vm_refl. Qed.
Lemma D_9b390 : decode_any W_9b390 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b394 : bv 32 := 0x00008067.
Lemma F_9b394 : fetch_word AsanUbsan.M.loaded_segments (0x9b3e4 : word) = Some W_9b394.
Proof. vm_refl. Qed.
Lemma D_9b394 : decode_any W_9b394 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
