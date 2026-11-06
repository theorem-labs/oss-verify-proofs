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

Definition W_80128 : bv 32 := 0x00058613.
Lemma F_80128 : fetch_word AsanUbsan.M.loaded_segments (0x80128 : word) = Some W_80128.
Proof. vm_refl. Qed.
Lemma D_80128 : decode_any W_80128 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8012c : bv 32 := 0x00140597.
Lemma F_8012c : fetch_word AsanUbsan.M.loaded_segments (0x8012c : word) = Some W_8012c.
Proof. vm_refl. Qed.
Lemma D_8012c : decode_any W_8012c = Some (Auipc 11 320, 4%Z).
Proof. vm_refl. Qed.

Definition W_80130 : bv 32 := 0x4ec58593.
Lemma F_80130 : fetch_word AsanUbsan.M.loaded_segments (0x80130 : word) = Some W_80130.
Proof. vm_refl. Qed.
Lemma D_80130 : decode_any W_80130 = Some (OpImm ALU_ADD 11 11 1260, 4%Z).
Proof. vm_refl. Qed.

Definition W_80134 : bv 32 := 0x00050693.
Lemma F_80134 : fetch_word AsanUbsan.M.loaded_segments (0x80134 : word) = Some W_80134.
Proof. vm_refl. Qed.
Lemma D_80134 : decode_any W_80134 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80138 : bv 32 := 0x00058513.
Lemma F_80138 : fetch_word AsanUbsan.M.loaded_segments (0x80138 : word) = Some W_80138.
Proof. vm_refl. Qed.
Lemma D_80138 : decode_any W_80138 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8013c : bv 32 := 0x00068593.
Lemma F_8013c : fetch_word AsanUbsan.M.loaded_segments (0x8013c : word) = Some W_8013c.
Proof. vm_refl. Qed.
Lemma D_8013c : decode_any W_8013c = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80140 : bv 32 := 0x00000693.
Lemma F_80140 : fetch_word AsanUbsan.M.loaded_segments (0x80140 : word) = Some W_80140.
Proof. vm_refl. Qed.
Lemma D_80140 : decode_any W_80140 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80144 : bv 32 := 0x0040006f.
Lemma F_80144 : fetch_word AsanUbsan.M.loaded_segments (0x80144 : word) = Some W_80144.
Proof. vm_refl. Qed.
Lemma D_80144 : decode_any W_80144 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80148 : bv 32 := 0xf9010113.
Lemma F_80148 : fetch_word AsanUbsan.M.loaded_segments (0x80148 : word) = Some W_80148.
Proof. vm_refl. Qed.
Lemma D_80148 : decode_any W_80148 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_8014c : bv 32 := 0x06113423.
Lemma F_8014c : fetch_word AsanUbsan.M.loaded_segments (0x8014c : word) = Some W_8014c.
Proof. vm_refl. Qed.
Lemma D_8014c : decode_any W_8014c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_80150 : bv 32 := 0x06813023.
Lemma F_80150 : fetch_word AsanUbsan.M.loaded_segments (0x80150 : word) = Some W_80150.
Proof. vm_refl. Qed.
Lemma D_80150 : decode_any W_80150 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80154 : bv 32 := 0x04913c23.
Lemma F_80154 : fetch_word AsanUbsan.M.loaded_segments (0x80154 : word) = Some W_80154.
Proof. vm_refl. Qed.
Lemma D_80154 : decode_any W_80154 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_80158 : bv 32 := 0x05213823.
Lemma F_80158 : fetch_word AsanUbsan.M.loaded_segments (0x80158 : word) = Some W_80158.
Proof. vm_refl. Qed.
Lemma D_80158 : decode_any W_80158 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8015c : bv 32 := 0x05313423.
Lemma F_8015c : fetch_word AsanUbsan.M.loaded_segments (0x8015c : word) = Some W_8015c.
Proof. vm_refl. Qed.
Lemma D_8015c : decode_any W_8015c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_80160 : bv 32 := 0x05413023.
Lemma F_80160 : fetch_word AsanUbsan.M.loaded_segments (0x80160 : word) = Some W_80160.
Proof. vm_refl. Qed.
Lemma D_80160 : decode_any W_80160 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_80164 : bv 32 := 0x03513c23.
Lemma F_80164 : fetch_word AsanUbsan.M.loaded_segments (0x80164 : word) = Some W_80164.
Proof. vm_refl. Qed.
Lemma D_80164 : decode_any W_80164 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80168 : bv 32 := 0x03613823.
Lemma F_80168 : fetch_word AsanUbsan.M.loaded_segments (0x80168 : word) = Some W_80168.
Proof. vm_refl. Qed.
Lemma D_80168 : decode_any W_80168 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8016c : bv 32 := 0x03713423.
Lemma F_8016c : fetch_word AsanUbsan.M.loaded_segments (0x8016c : word) = Some W_8016c.
Proof. vm_refl. Qed.
Lemma D_8016c : decode_any W_8016c = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80170 : bv 32 := 0x03813023.
Lemma F_80170 : fetch_word AsanUbsan.M.loaded_segments (0x80170 : word) = Some W_80170.
Proof. vm_refl. Qed.
Lemma D_80170 : decode_any W_80170 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80174 : bv 32 := 0x01913c23.
Lemma F_80174 : fetch_word AsanUbsan.M.loaded_segments (0x80174 : word) = Some W_80174.
Proof. vm_refl. Qed.
Lemma D_80174 : decode_any W_80174 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80178 : bv 32 := 0x00068413.
Lemma F_80178 : fetch_word AsanUbsan.M.loaded_segments (0x80178 : word) = Some W_80178.
Proof. vm_refl. Qed.
Lemma D_80178 : decode_any W_80178 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8017c : bv 32 := 0x00050493.
Lemma F_8017c : fetch_word AsanUbsan.M.loaded_segments (0x8017c : word) = Some W_8017c.
Proof. vm_refl. Qed.
Lemma D_8017c : decode_any W_8017c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80180 : bv 32 := 0x00b13423.
Lemma F_80180 : fetch_word AsanUbsan.M.loaded_segments (0x80180 : word) = Some W_80180.
Proof. vm_refl. Qed.
Lemma D_80180 : decode_any W_80180 = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80184 : bv 32 := 0x00c13823.
Lemma F_80184 : fetch_word AsanUbsan.M.loaded_segments (0x80184 : word) = Some W_80184.
Proof. vm_refl. Qed.
Lemma D_80184 : decode_any W_80184 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80188 : bv 32 := 0x00068463.
Lemma F_80188 : fetch_word AsanUbsan.M.loaded_segments (0x80188 : word) = Some W_80188.
Proof. vm_refl. Qed.
Lemma D_80188 : decode_any W_80188 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8018c : bv 32 := 0x00040023.
Lemma F_8018c : fetch_word AsanUbsan.M.loaded_segments (0x8018c : word) = Some W_8018c.
Proof. vm_refl. Qed.
Lemma D_8018c : decode_any W_8018c = Some (Store SZ1 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80190 : bv 32 := 0x0006069b.
Lemma F_80190 : fetch_word AsanUbsan.M.loaded_segments (0x80190 : word) = Some W_80190.
Proof. vm_refl. Qed.
Lemma D_80190 : decode_any W_80190 = Some (OpImm32 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80194 : bv 32 := 0x00000513.
Lemma F_80194 : fetch_word AsanUbsan.M.loaded_segments (0x80194 : word) = Some W_80194.
Proof. vm_refl. Qed.
Lemma D_80194 : decode_any W_80194 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80198 : bv 32 := 0x1c068a63.
Lemma F_80198 : fetch_word AsanUbsan.M.loaded_segments (0x80198 : word) = Some W_80198.
Proof. vm_refl. Qed.
Lemma D_80198 : decode_any W_80198 = Some (Branch BC_EQ 13 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_8019c : bv 32 := 0x1c058863.
Lemma F_8019c : fetch_word AsanUbsan.M.loaded_segments (0x8019c : word) = Some W_8019c.
Proof. vm_refl. Qed.
Lemma D_8019c : decode_any W_8019c = Some (Branch BC_EQ 11 0 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_801a0 : bv 32 := 0x02065693.
Lemma F_801a0 : fetch_word AsanUbsan.M.loaded_segments (0x801a0 : word) = Some W_801a0.
Proof. vm_refl. Qed.
Lemma D_801a0 : decode_any W_801a0 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_801a4 : bv 32 := 0xfff00513.
Lemma F_801a4 : fetch_word AsanUbsan.M.loaded_segments (0x801a4 : word) = Some W_801a4.
Proof. vm_refl. Qed.
Lemma D_801a4 : decode_any W_801a4 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_801a8 : bv 32 := 0xfff90717.
Lemma F_801a8 : fetch_word AsanUbsan.M.loaded_segments (0x801a8 : word) = Some W_801a8.
Proof. vm_refl. Qed.
Lemma D_801a8 : decode_any W_801a8 = Some (Auipc 14 1048464, 4%Z).
Proof. vm_refl. Qed.

Definition W_801ac : bv 32 := 0xfff90797.
Lemma F_801ac : fetch_word AsanUbsan.M.loaded_segments (0x801ac : word) = Some W_801ac.
Proof. vm_refl. Qed.
Lemma D_801ac : decode_any W_801ac = Some (Auipc 15 1048464, 4%Z).
Proof. vm_refl. Qed.

Definition W_801b0 : bv 32 := 0x02055513.
Lemma F_801b0 : fetch_word AsanUbsan.M.loaded_segments (0x801b0 : word) = Some W_801b0.
Proof. vm_refl. Qed.
Lemma D_801b0 : decode_any W_801b0 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_801b4 : bv 32 := 0x1647b783.
Lemma F_801b4 : fetch_word AsanUbsan.M.loaded_segments (0x801b4 : word) = Some W_801b4.
Proof. vm_refl. Qed.
Lemma D_801b4 : decode_any W_801b4 = Some (Load SZ8 true 15 15 356, 4%Z).
Proof. vm_refl. Qed.

Definition W_801b8 : bv 32 := 0x00a67633.
Lemma F_801b8 : fetch_word AsanUbsan.M.loaded_segments (0x801b8 : word) = Some W_801b8.
Proof. vm_refl. Qed.
Lemma D_801b8 : decode_any W_801b8 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_801bc : bv 32 := 0xfff90517.
Lemma F_801bc : fetch_word AsanUbsan.M.loaded_segments (0x801bc : word) = Some W_801bc.
Proof. vm_refl. Qed.
Lemma D_801bc : decode_any W_801bc = Some (Auipc 10 1048464, 4%Z).
Proof. vm_refl. Qed.

Definition W_801c0 : bv 32 := 0x21453803.
Lemma F_801c0 : fetch_word AsanUbsan.M.loaded_segments (0x801c0 : word) = Some W_801c0.
Proof. vm_refl. Qed.
Lemma D_801c0 : decode_any W_801c0 = Some (Load SZ8 true 16 10 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_801c4 : bv 32 := 0x14073503.
Lemma F_801c4 : fetch_word AsanUbsan.M.loaded_segments (0x801c4 : word) = Some W_801c4.
Proof. vm_refl. Qed.
Lemma D_801c4 : decode_any W_801c4 = Some (Load SZ8 true 10 14 320, 4%Z).
Proof. vm_refl. Qed.

Definition W_801c8 : bv 32 := 0x02f60733.
Lemma F_801c8 : fetch_word AsanUbsan.M.loaded_segments (0x801c8 : word) = Some W_801c8.
Proof. vm_refl. Qed.
Lemma D_801c8 : decode_any W_801c8 = Some (Mul M_MUL 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_801cc : bv 32 := 0x00361793.
Lemma F_801cc : fetch_word AsanUbsan.M.loaded_segments (0x801cc : word) = Some W_801cc.
Proof. vm_refl. Qed.
Lemma D_801cc : decode_any W_801cc = Some (ShiftImm ALU_SLL 15 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_801d0 : bv 32 := 0x01074633.
Lemma F_801d0 : fetch_word AsanUbsan.M.loaded_segments (0x801d0 : word) = Some W_801d0.
Proof. vm_refl. Qed.
Lemma D_801d0 : decode_any W_801d0 = Some (Op ALU_XOR 12 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_801d4 : bv 32 := 0x00f58733.
Lemma F_801d4 : fetch_word AsanUbsan.M.loaded_segments (0x801d4 : word) = Some W_801d4.
Proof. vm_refl. Qed.
Lemma D_801d4 : decode_any W_801d4 = Some (Op ALU_ADD 14 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_801d8 : bv 32 := 0x0005b783.
Lemma F_801d8 : fetch_word AsanUbsan.M.loaded_segments (0x801d8 : word) = Some W_801d8.
Proof. vm_refl. Qed.
Lemma D_801d8 : decode_any W_801d8 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801dc : bv 32 := 0x00858593.
Lemma F_801dc : fetch_word AsanUbsan.M.loaded_segments (0x801dc : word) = Some W_801dc.
Proof. vm_refl. Qed.
Lemma D_801dc : decode_any W_801dc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_801e0 : bv 32 := 0x02a787b3.
Lemma F_801e0 : fetch_word AsanUbsan.M.loaded_segments (0x801e0 : word) = Some W_801e0.
Proof. vm_refl. Qed.
Lemma D_801e0 : decode_any W_801e0 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_801e4 : bv 32 := 0x02f7d813.
Lemma F_801e4 : fetch_word AsanUbsan.M.loaded_segments (0x801e4 : word) = Some W_801e4.
Proof. vm_refl. Qed.
Lemma D_801e4 : decode_any W_801e4 = Some (ShiftImm ALU_SRL 16 15 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_801e8 : bv 32 := 0x00f847b3.
Lemma F_801e8 : fetch_word AsanUbsan.M.loaded_segments (0x801e8 : word) = Some W_801e8.
Proof. vm_refl. Qed.
Lemma D_801e8 : decode_any W_801e8 = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_801ec : bv 32 := 0x02a787b3.
Lemma F_801ec : fetch_word AsanUbsan.M.loaded_segments (0x801ec : word) = Some W_801ec.
Proof. vm_refl. Qed.
Lemma D_801ec : decode_any W_801ec = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_801f0 : bv 32 := 0x00c7c633.
Lemma F_801f0 : fetch_word AsanUbsan.M.loaded_segments (0x801f0 : word) = Some W_801f0.
Proof. vm_refl. Qed.
Lemma D_801f0 : decode_any W_801f0 = Some (Op ALU_XOR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_801f4 : bv 32 := 0x02a60633.
Lemma F_801f4 : fetch_word AsanUbsan.M.loaded_segments (0x801f4 : word) = Some W_801f4.
Proof. vm_refl. Qed.
Lemma D_801f4 : decode_any W_801f4 = Some (Mul M_MUL 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_801f8 : bv 32 := 0xfee590e3.
Lemma F_801f8 : fetch_word AsanUbsan.M.loaded_segments (0x801f8 : word) = Some W_801f8.
Proof. vm_refl. Qed.
Lemma D_801f8 : decode_any W_801f8 = Some (Branch BC_NE 11 14 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_801fc : bv 32 := 0x00010b37.
Lemma F_801fc : fetch_word AsanUbsan.M.loaded_segments (0x801fc : word) = Some W_801fc.
Proof. vm_refl. Qed.
Lemma D_801fc : decode_any W_801fc = Some (Lui 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80200 : bv 32 := 0x80000bb7.
Lemma F_80200 : fetch_word AsanUbsan.M.loaded_segments (0x80200 : word) = Some W_80200.
Proof. vm_refl. Qed.
Lemma D_80200 : decode_any W_80200 = Some (Lui 23 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_80204 : bv 32 := 0x02a685b3.
Lemma F_80204 : fetch_word AsanUbsan.M.loaded_segments (0x80204 : word) = Some W_80204.
Proof. vm_refl. Qed.
Lemma D_80204 : decode_any W_80204 = Some (Mul M_MUL 11 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80208 : bv 32 := 0x004006b7.
Lemma F_80208 : fetch_word AsanUbsan.M.loaded_segments (0x80208 : word) = Some W_80208.
Proof. vm_refl. Qed.
Lemma D_80208 : decode_any W_80208 = Some (Lui 13 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_8020c : bv 32 := 0xfffb0b1b.
Lemma F_8020c : fetch_word AsanUbsan.M.loaded_segments (0x8020c : word) = Some W_8020c.
Proof. vm_refl. Qed.
Lemma D_8020c : decode_any W_8020c = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80210 : bv 32 := 0xfffb8b9b.
Lemma F_80210 : fetch_word AsanUbsan.M.loaded_segments (0x80210 : word) = Some W_80210.
Proof. vm_refl. Qed.
Lemma D_80210 : decode_any W_80210 = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80214 : bv 32 := 0x02f5d713.
Lemma F_80214 : fetch_word AsanUbsan.M.loaded_segments (0x80214 : word) = Some W_80214.
Proof. vm_refl. Qed.
Lemma D_80214 : decode_any W_80214 = Some (ShiftImm ALU_SRL 14 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_80218 : bv 32 := 0x00b745b3.
Lemma F_80218 : fetch_word AsanUbsan.M.loaded_segments (0x80218 : word) = Some W_80218.
Proof. vm_refl. Qed.
Lemma D_80218 : decode_any W_80218 = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8021c : bv 32 := 0x02a585b3.
Lemma F_8021c : fetch_word AsanUbsan.M.loaded_segments (0x8021c : word) = Some W_8021c.
Proof. vm_refl. Qed.
Lemma D_8021c : decode_any W_8021c = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80220 : bv 32 := 0x00c5c5b3.
Lemma F_80220 : fetch_word AsanUbsan.M.loaded_segments (0x80220 : word) = Some W_80220.
Proof. vm_refl. Qed.
Lemma D_80220 : decode_any W_80220 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80224 : bv 32 := 0x02a585b3.
Lemma F_80224 : fetch_word AsanUbsan.M.loaded_segments (0x80224 : word) = Some W_80224.
Proof. vm_refl. Qed.
Lemma D_80224 : decode_any W_80224 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80228 : bv 32 := 0x02f5d613.
Lemma F_80228 : fetch_word AsanUbsan.M.loaded_segments (0x80228 : word) = Some W_80228.
Proof. vm_refl. Qed.
Lemma D_80228 : decode_any W_80228 = Some (ShiftImm ALU_SRL 12 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_8022c : bv 32 := 0x00b645b3.
Lemma F_8022c : fetch_word AsanUbsan.M.loaded_segments (0x8022c : word) = Some W_8022c.
Proof. vm_refl. Qed.
Lemma D_8022c : decode_any W_8022c = Some (Op ALU_XOR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80230 : bv 32 := 0x02a58533.
Lemma F_80230 : fetch_word AsanUbsan.M.loaded_segments (0x80230 : word) = Some W_80230.
Proof. vm_refl. Qed.
Lemma D_80230 : decode_any W_80230 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80234 : bv 32 := 0x02f55593.
Lemma F_80234 : fetch_word AsanUbsan.M.loaded_segments (0x80234 : word) = Some W_80234.
Proof. vm_refl. Qed.
Lemma D_80234 : decode_any W_80234 = Some (ShiftImm ALU_SRL 11 10 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_80238 : bv 32 := 0x00a5c9b3.
Lemma F_80238 : fetch_word AsanUbsan.M.loaded_segments (0x80238 : word) = Some W_80238.
Proof. vm_refl. Qed.
Lemma D_80238 : decode_any W_80238 = Some (Op ALU_XOR 19 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8023c : bv 32 := 0x02c99513.
Lemma F_8023c : fetch_word AsanUbsan.M.loaded_segments (0x8023c : word) = Some W_8023c.
Proof. vm_refl. Qed.
Lemma D_8023c : decode_any W_8023c = Some (ShiftImm ALU_SLL 10 19 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_80240 : bv 32 := 0x02a55513.
Lemma F_80240 : fetch_word AsanUbsan.M.loaded_segments (0x80240 : word) = Some W_80240.
Proof. vm_refl. Qed.
Lemma D_80240 : decode_any W_80240 = Some (ShiftImm ALU_SRL 10 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_80244 : bv 32 := 0x00a48933.
Lemma F_80244 : fetch_word AsanUbsan.M.loaded_segments (0x80244 : word) = Some W_80244.
Proof. vm_refl. Qed.
Lemma D_80244 : decode_any W_80244 = Some (Op ALU_ADD 18 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80248 : bv 32 := 0x00092503.
Lemma F_80248 : fetch_word AsanUbsan.M.loaded_segments (0x80248 : word) = Some W_80248.
Proof. vm_refl. Qed.
Lemma D_80248 : decode_any W_80248 = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8024c : bv 32 := 0x01068c1b.
Lemma F_8024c : fetch_word AsanUbsan.M.loaded_segments (0x8024c : word) = Some W_8024c.
Proof. vm_refl. Qed.
Lemma D_8024c : decode_any W_8024c = Some (OpImm32 24 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80250 : bv 32 := 0x01848c33.
Lemma F_80250 : fetch_word AsanUbsan.M.loaded_segments (0x80250 : word) = Some W_80250.
Proof. vm_refl. Qed.
Lemma D_80250 : decode_any W_80250 = Some (Op ALU_ADD 24 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80254 : bv 32 := 0x0230000f.
Lemma F_80254 : fetch_word AsanUbsan.M.loaded_segments (0x80254 : word) = Some W_80254.
Proof. vm_refl. Qed.
Lemma D_80254 : decode_any W_80254 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80258 : bv 32 := 0x01757cb3.
Lemma F_80258 : fetch_word AsanUbsan.M.loaded_segments (0x80258 : word) = Some W_80258.
Proof. vm_refl. Qed.
Lemma D_80258 : decode_any W_80258 = Some (Op ALU_AND 25 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_8025c : bv 32 := 0x0086869b.
Lemma F_8025c : fetch_word AsanUbsan.M.loaded_segments (0x8025c : word) = Some W_8025c.
Proof. vm_refl. Qed.
Lemma D_8025c : decode_any W_8025c = Some (OpImm32 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80260 : bv 32 := 0x00d48a33.
Lemma F_80260 : fetch_word AsanUbsan.M.loaded_segments (0x80260 : word) = Some W_80260.
Proof. vm_refl. Qed.
Lemma D_80260 : decode_any W_80260 = Some (Op ALU_ADD 20 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80264 : bv 32 := 0x000c8593.
Lemma F_80264 : fetch_word AsanUbsan.M.loaded_segments (0x80264 : word) = Some W_80264.
Proof. vm_refl. Qed.
Lemma D_80264 : decode_any W_80264 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80268 : bv 32 := 0x04058c63.
Lemma F_80268 : fetch_word AsanUbsan.M.loaded_segments (0x80268 : word) = Some W_80268.
Proof. vm_refl. Qed.
Lemma D_80268 : decode_any W_80268 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8026c : bv 32 := 0x00058513.
Lemma F_8026c : fetch_word AsanUbsan.M.loaded_segments (0x8026c : word) = Some W_8026c.
Proof. vm_refl. Qed.
Lemma D_8026c : decode_any W_8026c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80270 : bv 32 := 0x0105d59b.
Lemma F_80270 : fetch_word AsanUbsan.M.loaded_segments (0x80270 : word) = Some W_80270.
Proof. vm_refl. Qed.
Lemma D_80270 : decode_any W_80270 = Some (ShiftImm32 ALU_SRL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80274 : bv 32 := 0x00359613.
Lemma F_80274 : fetch_word AsanUbsan.M.loaded_segments (0x80274 : word) = Some W_80274.
Proof. vm_refl. Qed.
Lemma D_80274 : decode_any W_80274 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80278 : bv 32 := 0x00cc0633.
Lemma F_80278 : fetch_word AsanUbsan.M.loaded_segments (0x80278 : word) = Some W_80278.
Proof. vm_refl. Qed.
Lemma D_80278 : decode_any W_80278 = Some (Op ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8027c : bv 32 := 0x00063603.
Lemma F_8027c : fetch_word AsanUbsan.M.loaded_segments (0x8027c : word) = Some W_8027c.
Proof. vm_refl. Qed.
Lemma D_8027c : decode_any W_8027c = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80280 : bv 32 := 0x02060463.
Lemma F_80280 : fetch_word AsanUbsan.M.loaded_segments (0x80280 : word) = Some W_80280.
Proof. vm_refl. Qed.
Lemma D_80280 : decode_any W_80280 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80284 : bv 32 := 0x02051593.
Lemma F_80284 : fetch_word AsanUbsan.M.loaded_segments (0x80284 : word) = Some W_80284.
Proof. vm_refl. Qed.
Lemma D_80284 : decode_any W_80284 = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80288 : bv 32 := 0x0205d593.
Lemma F_80288 : fetch_word AsanUbsan.M.loaded_segments (0x80288 : word) = Some W_80288.
Proof. vm_refl. Qed.
Lemma D_80288 : decode_any W_80288 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8028c : bv 32 := 0x0165f5b3.
Lemma F_8028c : fetch_word AsanUbsan.M.loaded_segments (0x8028c : word) = Some W_8028c.
Proof. vm_refl. Qed.
Lemma D_8028c : decode_any W_8028c = Some (Op ALU_AND 11 11 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_80290 : bv 32 := 0x00459593.
Lemma F_80290 : fetch_word AsanUbsan.M.loaded_segments (0x80290 : word) = Some W_80290.
Proof. vm_refl. Qed.
Lemma D_80290 : decode_any W_80290 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80294 : bv 32 := 0x00b605b3.
Lemma F_80294 : fetch_word AsanUbsan.M.loaded_segments (0x80294 : word) = Some W_80294.
Proof. vm_refl. Qed.
Lemma D_80294 : decode_any W_80294 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80298 : bv 32 := 0x0005b603.
Lemma F_80298 : fetch_word AsanUbsan.M.loaded_segments (0x80298 : word) = Some W_80298.
Proof. vm_refl. Qed.
Lemma D_80298 : decode_any W_80298 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8029c : bv 32 := 0x0085a583.
Lemma F_8029c : fetch_word AsanUbsan.M.loaded_segments (0x8029c : word) = Some W_8029c.
Proof. vm_refl. Qed.
Lemma D_8029c : decode_any W_8029c = Some (Load SZ4 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_802a0 : bv 32 := 0xfcc994e3.
Lemma F_802a0 : fetch_word AsanUbsan.M.loaded_segments (0x802a0 : word) = Some W_802a0.
Proof. vm_refl. Qed.
Lemma D_802a0 : decode_any W_802a0 = Some (Branch BC_NE 19 12 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_802a4 : bv 32 := 0x0c80006f.
Lemma F_802a4 : fetch_word AsanUbsan.M.loaded_segments (0x802a4 : word) = Some W_802a4.
Proof. vm_refl. Qed.
Lemma D_802a4 : decode_any W_802a4 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_802a8 : bv 32 := 0x00050a93.
Lemma F_802a8 : fetch_word AsanUbsan.M.loaded_segments (0x802a8 : word) = Some W_802a8.
Proof. vm_refl. Qed.
Lemma D_802a8 : decode_any W_802a8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802ac : bv 32 := 0x000a0513.
Lemma F_802ac : fetch_word AsanUbsan.M.loaded_segments (0x802ac : word) = Some W_802ac.
Proof. vm_refl. Qed.
Lemma D_802ac : decode_any W_802ac = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802b0 : bv 32 := 0x69c000ef.
Lemma F_802b0 : fetch_word AsanUbsan.M.loaded_segments (0x802b0 : word) = Some W_802b0.
Proof. vm_refl. Qed.
Lemma D_802b0 : decode_any W_802b0 = Some (Jal 1 1692, 4%Z).
Proof. vm_refl. Qed.

Definition W_802b4 : bv 32 := 0x00050613.
Lemma F_802b4 : fetch_word AsanUbsan.M.loaded_segments (0x802b4 : word) = Some W_802b4.
Proof. vm_refl. Qed.
Lemma D_802b4 : decode_any W_802b4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802b8 : bv 32 := 0x000a8513.
Lemma F_802b8 : fetch_word AsanUbsan.M.loaded_segments (0x802b8 : word) = Some W_802b8.
Proof. vm_refl. Qed.
Lemma D_802b8 : decode_any W_802b8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802bc : bv 32 := 0xfc9ff06f.
Lemma F_802bc : fetch_word AsanUbsan.M.loaded_segments (0x802bc : word) = Some W_802bc.
Proof. vm_refl. Qed.
Lemma D_802bc : decode_any W_802bc = Some (Jal 0 2097096, 4%Z).
Proof. vm_refl. Qed.

Definition W_802c0 : bv 32 := 0x00090513.
Lemma F_802c0 : fetch_word AsanUbsan.M.loaded_segments (0x802c0 : word) = Some W_802c0.
Proof. vm_refl. Qed.
Lemma D_802c0 : decode_any W_802c0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802c4 : bv 32 := 0x5f8000ef.
Lemma F_802c4 : fetch_word AsanUbsan.M.loaded_segments (0x802c4 : word) = Some W_802c4.
Proof. vm_refl. Qed.
Lemma D_802c4 : decode_any W_802c4 = Some (Jal 1 1528, 4%Z).
Proof. vm_refl. Qed.

Definition W_802c8 : bv 32 := 0x00050a93.
Lemma F_802c8 : fetch_word AsanUbsan.M.loaded_segments (0x802c8 : word) = Some W_802c8.
Proof. vm_refl. Qed.
Lemma D_802c8 : decode_any W_802c8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802cc : bv 32 := 0x03950663.
Lemma F_802cc : fetch_word AsanUbsan.M.loaded_segments (0x802cc : word) = Some W_802cc.
Proof. vm_refl. Qed.
Lemma D_802cc : decode_any W_802cc = Some (Branch BC_EQ 10 25 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_802d0 : bv 32 := 0x00813603.
Lemma F_802d0 : fetch_word AsanUbsan.M.loaded_segments (0x802d0 : word) = Some W_802d0.
Proof. vm_refl. Qed.
Lemma D_802d0 : decode_any W_802d0 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_802d4 : bv 32 := 0x01013683.
Lemma F_802d4 : fetch_word AsanUbsan.M.loaded_segments (0x802d4 : word) = Some W_802d4.
Proof. vm_refl. Qed.
Lemma D_802d4 : decode_any W_802d4 = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_802d8 : bv 32 := 0x00048513.
Lemma F_802d8 : fetch_word AsanUbsan.M.loaded_segments (0x802d8 : word) = Some W_802d8.
Proof. vm_refl. Qed.
Lemma D_802d8 : decode_any W_802d8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802dc : bv 32 := 0x000a8593.
Lemma F_802dc : fetch_word AsanUbsan.M.loaded_segments (0x802dc : word) = Some W_802dc.
Proof. vm_refl. Qed.
Lemma D_802dc : decode_any W_802dc = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802e0 : bv 32 := 0x00098713.
Lemma F_802e0 : fetch_word AsanUbsan.M.loaded_segments (0x802e0 : word) = Some W_802e0.
Proof. vm_refl. Qed.
Lemma D_802e0 : decode_any W_802e0 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802e4 : bv 32 := 0x524000ef.
Lemma F_802e4 : fetch_word AsanUbsan.M.loaded_segments (0x802e4 : word) = Some W_802e4.
Proof. vm_refl. Qed.
Lemma D_802e4 : decode_any W_802e4 = Some (Jal 1 1316, 4%Z).
Proof. vm_refl. Qed.

Definition W_802e8 : bv 32 := 0x00050863.
Lemma F_802e8 : fetch_word AsanUbsan.M.loaded_segments (0x802e8 : word) = Some W_802e8.
Proof. vm_refl. Qed.
Lemma D_802e8 : decode_any W_802e8 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_802ec : bv 32 := 0x0310000f.
Lemma F_802ec : fetch_word AsanUbsan.M.loaded_segments (0x802ec : word) = Some W_802ec.
Proof. vm_refl. Qed.
Lemma D_802ec : decode_any W_802ec = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802f0 : bv 32 := 0x01592023.
Lemma F_802f0 : fetch_word AsanUbsan.M.loaded_segments (0x802f0 : word) = Some W_802f0.
Proof. vm_refl. Qed.
Lemma D_802f0 : decode_any W_802f0 = Some (Store SZ4 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802f4 : bv 32 := 0x0780006f.
Lemma F_802f4 : fetch_word AsanUbsan.M.loaded_segments (0x802f4 : word) = Some W_802f4.
Proof. vm_refl. Qed.
Lemma D_802f4 : decode_any W_802f4 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_802f8 : bv 32 := 0x00400537.
Lemma F_802f8 : fetch_word AsanUbsan.M.loaded_segments (0x802f8 : word) = Some W_802f8.
Proof. vm_refl. Qed.
Lemma D_802f8 : decode_any W_802f8 = Some (Lui 10 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_802fc : bv 32 := 0x00a48533.
Lemma F_802fc : fetch_word AsanUbsan.M.loaded_segments (0x802fc : word) = Some W_802fc.
Proof. vm_refl. Qed.
Lemma D_802fc : decode_any W_802fc = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80300 : bv 32 := 0x00100593.
Lemma F_80300 : fetch_word AsanUbsan.M.loaded_segments (0x80300 : word) = Some W_80300.
Proof. vm_refl. Qed.
Lemma D_80300 : decode_any W_80300 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80304 : bv 32 := 0x00b5252f.
Lemma F_80304 : fetch_word AsanUbsan.M.loaded_segments (0x80304 : word) = Some W_80304.
Proof. vm_refl. Qed.
Lemma D_80304 : decode_any W_80304 = Some (Amo AMO_ADD AW false false 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80308 : bv 32 := 0x0015051b.
Lemma F_80308 : fetch_word AsanUbsan.M.loaded_segments (0x80308 : word) = Some W_80308.
Proof. vm_refl. Qed.
Lemma D_80308 : decode_any W_80308 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8030c : bv 32 := 0x02051493.
Lemma F_8030c : fetch_word AsanUbsan.M.loaded_segments (0x8030c : word) = Some W_8030c.
Proof. vm_refl. Qed.
Lemma D_8030c : decode_any W_8030c = Some (ShiftImm ALU_SLL 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80310 : bv 32 := 0x0204d493.
Lemma F_80310 : fetch_word AsanUbsan.M.loaded_segments (0x80310 : word) = Some W_80310.
Proof. vm_refl. Qed.
Lemma D_80310 : decode_any W_80310 = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80314 : bv 32 := 0x08054663.
Lemma F_80314 : fetch_word AsanUbsan.M.loaded_segments (0x80314 : word) = Some W_80314.
Proof. vm_refl. Qed.
Lemma D_80314 : decode_any W_80314 = Some (Branch BC_LT 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_80318 : bv 32 := 0x00050b93.
Lemma F_80318 : fetch_word AsanUbsan.M.loaded_segments (0x80318 : word) = Some W_80318.
Proof. vm_refl. Qed.
Lemma D_80318 : decode_any W_80318 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8031c : bv 32 := 0x0104d593.
Lemma F_8031c : fetch_word AsanUbsan.M.loaded_segments (0x8031c : word) = Some W_8031c.
Proof. vm_refl. Qed.
Lemma D_8031c : decode_any W_8031c = Some (ShiftImm ALU_SRL 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80320 : bv 32 := 0x00359513.
Lemma F_80320 : fetch_word AsanUbsan.M.loaded_segments (0x80320 : word) = Some W_80320.
Proof. vm_refl. Qed.
Lemma D_80320 : decode_any W_80320 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80324 : bv 32 := 0x00ac0533.
Lemma F_80324 : fetch_word AsanUbsan.M.loaded_segments (0x80324 : word) = Some W_80324.
Proof. vm_refl. Qed.
Lemma D_80324 : decode_any W_80324 = Some (Op ALU_ADD 10 24 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80328 : bv 32 := 0x00053503.
Lemma F_80328 : fetch_word AsanUbsan.M.loaded_segments (0x80328 : word) = Some W_80328.
Proof. vm_refl. Qed.
Lemma D_80328 : decode_any W_80328 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8032c : bv 32 := 0x08050a63.
Lemma F_8032c : fetch_word AsanUbsan.M.loaded_segments (0x8032c : word) = Some W_8032c.
Proof. vm_refl. Qed.
Lemma D_8032c : decode_any W_8032c = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_80330 : bv 32 := 0x0164f5b3.
Lemma F_80330 : fetch_word AsanUbsan.M.loaded_segments (0x80330 : word) = Some W_80330.
Proof. vm_refl. Qed.
Lemma D_80330 : decode_any W_80330 = Some (Op ALU_AND 11 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_80334 : bv 32 := 0x00459593.
Lemma F_80334 : fetch_word AsanUbsan.M.loaded_segments (0x80334 : word) = Some W_80334.
Proof. vm_refl. Qed.
Lemma D_80334 : decode_any W_80334 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80338 : bv 32 := 0x00b504b3.
Lemma F_80338 : fetch_word AsanUbsan.M.loaded_segments (0x80338 : word) = Some W_80338.
Proof. vm_refl. Qed.
Lemma D_80338 : decode_any W_80338 = Some (Op ALU_ADD 9 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8033c : bv 32 := 0x00810613.
Lemma F_8033c : fetch_word AsanUbsan.M.loaded_segments (0x8033c : word) = Some W_8033c.
Proof. vm_refl. Qed.
Lemma D_8033c : decode_any W_8033c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80340 : bv 32 := 0x00048513.
Lemma F_80340 : fetch_word AsanUbsan.M.loaded_segments (0x80340 : word) = Some W_80340.
Proof. vm_refl. Qed.
Lemma D_80340 : decode_any W_80340 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80344 : bv 32 := 0x00000593.
Lemma F_80344 : fetch_word AsanUbsan.M.loaded_segments (0x80344 : word) = Some W_80344.
Proof. vm_refl. Qed.
Lemma D_80344 : decode_any W_80344 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80348 : bv 32 := 0x00098693.
Lemma F_80348 : fetch_word AsanUbsan.M.loaded_segments (0x80348 : word) = Some W_80348.
Proof. vm_refl. Qed.
Lemma D_80348 : decode_any W_80348 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8034c : bv 32 := 0xaf5ff0ef.
Lemma F_8034c : fetch_word AsanUbsan.M.loaded_segments (0x8034c : word) = Some W_8034c.
Proof. vm_refl. Qed.
Lemma D_8034c : decode_any W_8034c = Some (Jal 1 2095860, 4%Z).
Proof. vm_refl. Qed.

Definition W_80350 : bv 32 := 0x0154a423.
Lemma F_80350 : fetch_word AsanUbsan.M.loaded_segments (0x80350 : word) = Some W_80350.
Proof. vm_refl. Qed.
Lemma D_80350 : decode_any W_80350 = Some (Store SZ4 9 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80354 : bv 32 := 0x0310000f.
Lemma F_80354 : fetch_word AsanUbsan.M.loaded_segments (0x80354 : word) = Some W_80354.
Proof. vm_refl. Qed.
Lemma D_80354 : decode_any W_80354 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80358 : bv 32 := 0x000b8513.
Lemma F_80358 : fetch_word AsanUbsan.M.loaded_segments (0x80358 : word) = Some W_80358.
Proof. vm_refl. Qed.
Lemma D_80358 : decode_any W_80358 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8035c : bv 32 := 0x01792023.
Lemma F_8035c : fetch_word AsanUbsan.M.loaded_segments (0x8035c : word) = Some W_8035c.
Proof. vm_refl. Qed.
Lemma D_8035c : decode_any W_8035c = Some (Store SZ4 18 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80360 : bv 32 := 0x00040663.
Lemma F_80360 : fetch_word AsanUbsan.M.loaded_segments (0x80360 : word) = Some W_80360.
Proof. vm_refl. Qed.
Lemma D_80360 : decode_any W_80360 = Some (Branch BC_EQ 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80364 : bv 32 := 0x00100593.
Lemma F_80364 : fetch_word AsanUbsan.M.loaded_segments (0x80364 : word) = Some W_80364.
Proof. vm_refl. Qed.
Lemma D_80364 : decode_any W_80364 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80368 : bv 32 := 0x00b40023.
Lemma F_80368 : fetch_word AsanUbsan.M.loaded_segments (0x80368 : word) = Some W_80368.
Proof. vm_refl. Qed.
Lemma D_80368 : decode_any W_80368 = Some (Store SZ1 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8036c : bv 32 := 0x06813083.
Lemma F_8036c : fetch_word AsanUbsan.M.loaded_segments (0x8036c : word) = Some W_8036c.
Proof. vm_refl. Qed.
Lemma D_8036c : decode_any W_8036c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_80370 : bv 32 := 0x06013403.
Lemma F_80370 : fetch_word AsanUbsan.M.loaded_segments (0x80370 : word) = Some W_80370.
Proof. vm_refl. Qed.
Lemma D_80370 : decode_any W_80370 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80374 : bv 32 := 0x05813483.
Lemma F_80374 : fetch_word AsanUbsan.M.loaded_segments (0x80374 : word) = Some W_80374.
Proof. vm_refl. Qed.
Lemma D_80374 : decode_any W_80374 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_80378 : bv 32 := 0x05013903.
Lemma F_80378 : fetch_word AsanUbsan.M.loaded_segments (0x80378 : word) = Some W_80378.
Proof. vm_refl. Qed.
Lemma D_80378 : decode_any W_80378 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8037c : bv 32 := 0x04813983.
Lemma F_8037c : fetch_word AsanUbsan.M.loaded_segments (0x8037c : word) = Some W_8037c.
Proof. vm_refl. Qed.
Lemma D_8037c : decode_any W_8037c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_80380 : bv 32 := 0x04013a03.
Lemma F_80380 : fetch_word AsanUbsan.M.loaded_segments (0x80380 : word) = Some W_80380.
Proof. vm_refl. Qed.
Lemma D_80380 : decode_any W_80380 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_80384 : bv 32 := 0x03813a83.
Lemma F_80384 : fetch_word AsanUbsan.M.loaded_segments (0x80384 : word) = Some W_80384.
Proof. vm_refl. Qed.
Lemma D_80384 : decode_any W_80384 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80388 : bv 32 := 0x03013b03.
Lemma F_80388 : fetch_word AsanUbsan.M.loaded_segments (0x80388 : word) = Some W_80388.
Proof. vm_refl. Qed.
Lemma D_80388 : decode_any W_80388 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8038c : bv 32 := 0x02813b83.
Lemma F_8038c : fetch_word AsanUbsan.M.loaded_segments (0x8038c : word) = Some W_8038c.
Proof. vm_refl. Qed.
Lemma D_8038c : decode_any W_8038c = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80390 : bv 32 := 0x02013c03.
Lemma F_80390 : fetch_word AsanUbsan.M.loaded_segments (0x80390 : word) = Some W_80390.
Proof. vm_refl. Qed.
Lemma D_80390 : decode_any W_80390 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80394 : bv 32 := 0x01813c83.
Lemma F_80394 : fetch_word AsanUbsan.M.loaded_segments (0x80394 : word) = Some W_80394.
Proof. vm_refl. Qed.
Lemma D_80394 : decode_any W_80394 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80398 : bv 32 := 0x07010113.
Lemma F_80398 : fetch_word AsanUbsan.M.loaded_segments (0x80398 : word) = Some W_80398.
Proof. vm_refl. Qed.
Lemma D_80398 : decode_any W_80398 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_8039c : bv 32 := 0x00008067.
Lemma F_8039c : fetch_word AsanUbsan.M.loaded_segments (0x8039c : word) = Some W_8039c.
Proof. vm_refl. Qed.
Lemma D_8039c : decode_any W_8039c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803a0 : bv 32 := 0x017576b3.
Lemma F_803a0 : fetch_word AsanUbsan.M.loaded_segments (0x803a0 : word) = Some W_803a0.
Proof. vm_refl. Qed.
Lemma D_803a0 : decode_any W_803a0 = Some (Op ALU_AND 13 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_803a4 : bv 32 := 0xfff99517.
Lemma F_803a4 : fetch_word AsanUbsan.M.loaded_segments (0x803a4 : word) = Some W_803a4.
Proof. vm_refl. Qed.
Lemma D_803a4 : decode_any W_803a4 = Some (Auipc 10 1048473, 4%Z).
Proof. vm_refl. Qed.

Definition W_803a8 : bv 32 := 0xfff96597.
Lemma F_803a8 : fetch_word AsanUbsan.M.loaded_segments (0x803a8 : word) = Some W_803a8.
Proof. vm_refl. Qed.
Lemma D_803a8 : decode_any W_803a8 = Some (Auipc 11 1048470, 4%Z).
Proof. vm_refl. Qed.

Definition W_803ac : bv 32 := 0xea950513.
Lemma F_803ac : fetch_word AsanUbsan.M.loaded_segments (0x803ac : word) = Some W_803ac.
Proof. vm_refl. Qed.
Lemma D_803ac : decode_any W_803ac = Some (OpImm ALU_ADD 10 10 3753, 4%Z).
Proof. vm_refl. Qed.

Definition W_803b0 : bv 32 := 0x22b58613.
Lemma F_803b0 : fetch_word AsanUbsan.M.loaded_segments (0x803b0 : word) = Some W_803b0.
Proof. vm_refl. Qed.
Lemma D_803b0 : decode_any W_803b0 = Some (OpImm ALU_ADD 12 11 555, 4%Z).
Proof. vm_refl. Qed.

Definition W_803b4 : bv 32 := 0x08c00593.
Lemma F_803b4 : fetch_word AsanUbsan.M.loaded_segments (0x803b4 : word) = Some W_803b4.
Proof. vm_refl. Qed.
Lemma D_803b4 : decode_any W_803b4 = Some (OpImm ALU_ADD 11 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_803b8 : bv 32 := 0x00048713.
Lemma F_803b8 : fetch_word AsanUbsan.M.loaded_segments (0x803b8 : word) = Some W_803b8.
Proof. vm_refl. Qed.
Lemma D_803b8 : decode_any W_803b8 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803bc : bv 32 := 0xf2df80ef.
Lemma F_803bc : fetch_word AsanUbsan.M.loaded_segments (0x803bc : word) = Some W_803bc.
Proof. vm_refl. Qed.
Lemma D_803bc : decode_any W_803bc = Some (Jal 1 2068268, 4%Z).
Proof. vm_refl. Qed.

Definition W_803c0 : bv 32 := 0x000a0513.
Lemma F_803c0 : fetch_word AsanUbsan.M.loaded_segments (0x803c0 : word) = Some W_803c0.
Proof. vm_refl. Qed.
Lemma D_803c0 : decode_any W_803c0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803c4 : bv 32 := 0x588000ef.
Lemma F_803c4 : fetch_word AsanUbsan.M.loaded_segments (0x803c4 : word) = Some W_803c4.
Proof. vm_refl. Qed.
Lemma D_803c4 : decode_any W_803c4 = Some (Jal 1 1416, 4%Z).
Proof. vm_refl. Qed.

Definition W_803c8 : bv 32 := 0xf69ff06f.
Lemma F_803c8 : fetch_word AsanUbsan.M.loaded_segments (0x803c8 : word) = Some W_803c8.
Proof. vm_refl. Qed.
Lemma D_803c8 : decode_any W_803c8 = Some (Jal 0 2097000, 4%Z).
Proof. vm_refl. Qed.
