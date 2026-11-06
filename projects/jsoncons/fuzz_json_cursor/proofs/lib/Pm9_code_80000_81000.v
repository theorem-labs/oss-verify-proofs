(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_80000 : bv 32 := 0x0008b883.
Lemma F_80000 : fetch_word AsanUbsan.M.loaded_segments (0x80048 : word) = Some W_80000.
Proof. vm_refl. Qed.
Lemma D_80000 : decode_any W_80000 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80004 : bv 32 := 0x0108e833.
Lemma F_80004 : fetch_word AsanUbsan.M.loaded_segments (0x8004c : word) = Some W_80004.
Proof. vm_refl. Qed.
Lemma D_80004 : decode_any W_80004 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80008 : bv 32 := 0x24081a63.
Lemma F_80008 : fetch_word AsanUbsan.M.loaded_segments (0x80050 : word) = Some W_80008.
Proof. vm_refl. Qed.
Lemma D_80008 : decode_any W_80008 = Some (Branch BC_NE 16 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_8000c : bv 32 := 0x155120ef.
Lemma F_8000c : fetch_word AsanUbsan.M.loaded_segments (0x80054 : word) = Some W_8000c.
Proof. vm_refl. Qed.
Lemma D_8000c : decode_any W_8000c = Some (Jal 1 76116, 4%Z).
Proof. vm_refl. Qed.

Definition W_80010 : bv 32 := 0x07010113.
Lemma F_80010 : fetch_word AsanUbsan.M.loaded_segments (0x80058 : word) = Some W_80010.
Proof. vm_refl. Qed.
Lemma D_80010 : decode_any W_80010 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_80014 : bv 32 := 0x7e813083.
Lemma F_80014 : fetch_word AsanUbsan.M.loaded_segments (0x8005c : word) = Some W_80014.
Proof. vm_refl. Qed.
Lemma D_80014 : decode_any W_80014 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80018 : bv 32 := 0x7e013403.
Lemma F_80018 : fetch_word AsanUbsan.M.loaded_segments (0x80060 : word) = Some W_80018.
Proof. vm_refl. Qed.
Lemma D_80018 : decode_any W_80018 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_8001c : bv 32 := 0x7d813483.
Lemma F_8001c : fetch_word AsanUbsan.M.loaded_segments (0x80064 : word) = Some W_8001c.
Proof. vm_refl. Qed.
Lemma D_8001c : decode_any W_8001c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80020 : bv 32 := 0x7d013903.
Lemma F_80020 : fetch_word AsanUbsan.M.loaded_segments (0x80068 : word) = Some W_80020.
Proof. vm_refl. Qed.
Lemma D_80020 : decode_any W_80020 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80024 : bv 32 := 0x7c813983.
Lemma F_80024 : fetch_word AsanUbsan.M.loaded_segments (0x8006c : word) = Some W_80024.
Proof. vm_refl. Qed.
Lemma D_80024 : decode_any W_80024 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80028 : bv 32 := 0x7c013a03.
Lemma F_80028 : fetch_word AsanUbsan.M.loaded_segments (0x80070 : word) = Some W_80028.
Proof. vm_refl. Qed.
Lemma D_80028 : decode_any W_80028 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_8002c : bv 32 := 0x7b813a83.
Lemma F_8002c : fetch_word AsanUbsan.M.loaded_segments (0x80074 : word) = Some W_8002c.
Proof. vm_refl. Qed.
Lemma D_8002c : decode_any W_8002c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80030 : bv 32 := 0x7b013b03.
Lemma F_80030 : fetch_word AsanUbsan.M.loaded_segments (0x80078 : word) = Some W_80030.
Proof. vm_refl. Qed.
Lemma D_80030 : decode_any W_80030 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_80034 : bv 32 := 0x7a813b83.
Lemma F_80034 : fetch_word AsanUbsan.M.loaded_segments (0x8007c : word) = Some W_80034.
Proof. vm_refl. Qed.
Lemma D_80034 : decode_any W_80034 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_80038 : bv 32 := 0x7f010113.
Lemma F_80038 : fetch_word AsanUbsan.M.loaded_segments (0x80080 : word) = Some W_80038.
Proof. vm_refl. Qed.
Lemma D_80038 : decode_any W_80038 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_8003c : bv 32 := 0x00008067.
Lemma F_8003c : fetch_word AsanUbsan.M.loaded_segments (0x80084 : word) = Some W_8003c.
Proof. vm_refl. Qed.
Lemma D_8003c : decode_any W_8003c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c8 : bv 32 := 0x0c061463.
Lemma F_800c8 : fetch_word AsanUbsan.M.loaded_segments (0x80110 : word) = Some W_800c8.
Proof. vm_refl. Qed.
Lemma D_800c8 : decode_any W_800c8 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_800cc : bv 32 := 0xef5ff06f.
Lemma F_800cc : fetch_word AsanUbsan.M.loaded_segments (0x80114 : word) = Some W_800cc.
Proof. vm_refl. Qed.
Lemma D_800cc : decode_any W_800cc = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_80154 : bv 32 := 0x12061e63.
Lemma F_80154 : fetch_word AsanUbsan.M.loaded_segments (0x8019c : word) = Some W_80154.
Proof. vm_refl. Qed.
Lemma D_80154 : decode_any W_80154 = Some (Branch BC_NE 12 0 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_80158 : bv 32 := 0xeb5ff06f.
Lemma F_80158 : fetch_word AsanUbsan.M.loaded_segments (0x801a0 : word) = Some W_80158.
Proof. vm_refl. Qed.
Lemma D_80158 : decode_any W_80158 = Some (Jal 0 2096820, 4%Z).
Proof. vm_refl. Qed.

Definition W_8015c : bv 32 := 0x00070803.
Lemma F_8015c : fetch_word AsanUbsan.M.loaded_segments (0x801a4 : word) = Some W_8015c.
Proof. vm_refl. Qed.
Lemma D_8015c : decode_any W_8015c = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80160 : bv 32 := 0x0077f793.
Lemma F_80160 : fetch_word AsanUbsan.M.loaded_segments (0x801a8 : word) = Some W_80160.
Proof. vm_refl. Qed.
Lemma D_80160 : decode_any W_80160 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80164 : bv 32 := 0x010038b3.
Lemma F_80164 : fetch_word AsanUbsan.M.loaded_segments (0x801ac : word) = Some W_80164.
Proof. vm_refl. Qed.
Lemma D_80164 : decode_any W_80164 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80168 : bv 32 := 0x0107a7b3.
Lemma F_80168 : fetch_word AsanUbsan.M.loaded_segments (0x801b0 : word) = Some W_80168.
Proof. vm_refl. Qed.
Lemma D_80168 : decode_any W_80168 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8016c : bv 32 := 0x0017c793.
Lemma F_8016c : fetch_word AsanUbsan.M.loaded_segments (0x801b4 : word) = Some W_8016c.
Proof. vm_refl. Qed.
Lemma D_8016c : decode_any W_8016c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80170 : bv 32 := 0x00f8f7b3.
Lemma F_80170 : fetch_word AsanUbsan.M.loaded_segments (0x801b8 : word) = Some W_80170.
Proof. vm_refl. Qed.
Lemma D_80170 : decode_any W_80170 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80174 : bv 32 := 0x00e6fa63.
Lemma F_80174 : fetch_word AsanUbsan.M.loaded_segments (0x801bc : word) = Some W_80174.
Proof. vm_refl. Qed.
Lemma D_80174 : decode_any W_80174 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80178 : bv 32 := 0x0006c803.
Lemma F_80178 : fetch_word AsanUbsan.M.loaded_segments (0x801c0 : word) = Some W_80178.
Proof. vm_refl. Qed.
Lemma D_80178 : decode_any W_80178 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8017c : bv 32 := 0x00168693.
Lemma F_8017c : fetch_word AsanUbsan.M.loaded_segments (0x801c4 : word) = Some W_8017c.
Proof. vm_refl. Qed.
Lemma D_8017c : decode_any W_8017c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80180 : bv 32 := 0x00f867b3.
Lemma F_80180 : fetch_word AsanUbsan.M.loaded_segments (0x801c8 : word) = Some W_80180.
Proof. vm_refl. Qed.
Lemma D_80180 : decode_any W_80180 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80184 : bv 32 := 0xfee69ae3.
Lemma F_80184 : fetch_word AsanUbsan.M.loaded_segments (0x801cc : word) = Some W_80184.
Proof. vm_refl. Qed.
Lemma D_80184 : decode_any W_80184 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_80188 : bv 32 := 0x0ff7f693.
Lemma F_80188 : fetch_word AsanUbsan.M.loaded_segments (0x801d0 : word) = Some W_80188.
Proof. vm_refl. Qed.
Lemma D_80188 : decode_any W_80188 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_8018c : bv 32 := 0xe2068ae3.
Lemma F_8018c : fetch_word AsanUbsan.M.loaded_segments (0x801d4 : word) = Some W_8018c.
Proof. vm_refl. Qed.
Lemma D_8018c : decode_any W_8018c = Some (Branch BC_EQ 13 0 7732, 4%Z).
Proof. vm_refl. Qed.

Definition W_80190 : bv 32 := 0x00050b13.
Lemma F_80190 : fetch_word AsanUbsan.M.loaded_segments (0x801d8 : word) = Some W_80190.
Proof. vm_refl. Qed.
Lemma D_80190 : decode_any W_80190 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80194 : bv 32 := 0x00058513.
Lemma F_80194 : fetch_word AsanUbsan.M.loaded_segments (0x801dc : word) = Some W_80194.
Proof. vm_refl. Qed.
Lemma D_80194 : decode_any W_80194 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80198 : bv 32 := 0x00058b93.
Lemma F_80198 : fetch_word AsanUbsan.M.loaded_segments (0x801e0 : word) = Some W_80198.
Proof. vm_refl. Qed.
Lemma D_80198 : decode_any W_80198 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8019c : bv 32 := 0x00060593.
Lemma F_8019c : fetch_word AsanUbsan.M.loaded_segments (0x801e4 : word) = Some W_8019c.
Proof. vm_refl. Qed.
Lemma D_8019c : decode_any W_8019c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801a0 : bv 32 := 0x00060493.
Lemma F_801a0 : fetch_word AsanUbsan.M.loaded_segments (0x801e8 : word) = Some W_801a0.
Proof. vm_refl. Qed.
Lemma D_801a0 : decode_any W_801a0 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801a4 : bv 32 := 0x075020ef.
Lemma F_801a4 : fetch_word AsanUbsan.M.loaded_segments (0x801ec : word) = Some W_801a4.
Proof. vm_refl. Qed.
Lemma D_801a4 : decode_any W_801a4 = Some (Jal 1 10356, 4%Z).
Proof. vm_refl. Qed.

Definition W_801a8 : bv 32 := 0x000b8593.
Lemma F_801a8 : fetch_word AsanUbsan.M.loaded_segments (0x801f0 : word) = Some W_801a8.
Proof. vm_refl. Qed.
Lemma D_801a8 : decode_any W_801a8 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801ac : bv 32 := 0x00048613.
Lemma F_801ac : fetch_word AsanUbsan.M.loaded_segments (0x801f4 : word) = Some W_801ac.
Proof. vm_refl. Qed.
Lemma D_801ac : decode_any W_801ac = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801b0 : bv 32 := 0x00050913.
Lemma F_801b0 : fetch_word AsanUbsan.M.loaded_segments (0x801f8 : word) = Some W_801b0.
Proof. vm_refl. Qed.
Lemma D_801b0 : decode_any W_801b0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801b4 : bv 32 := 0x000b0513.
Lemma F_801b4 : fetch_word AsanUbsan.M.loaded_segments (0x801fc : word) = Some W_801b4.
Proof. vm_refl. Qed.
Lemma D_801b4 : decode_any W_801b4 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801b8 : bv 32 := 0xe00904e3.
Lemma F_801b8 : fetch_word AsanUbsan.M.loaded_segments (0x80200 : word) = Some W_801b8.
Proof. vm_refl. Qed.
Lemma D_801b8 : decode_any W_801b8 = Some (Branch BC_EQ 18 0 7688, 4%Z).
Proof. vm_refl. Qed.

Definition W_8025c : bv 32 := 0x00070803.
Lemma F_8025c : fetch_word AsanUbsan.M.loaded_segments (0x802a4 : word) = Some W_8025c.
Proof. vm_refl. Qed.
Lemma D_8025c : decode_any W_8025c = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80260 : bv 32 := 0x0077f793.
Lemma F_80260 : fetch_word AsanUbsan.M.loaded_segments (0x802a8 : word) = Some W_80260.
Proof. vm_refl. Qed.
Lemma D_80260 : decode_any W_80260 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80264 : bv 32 := 0x010038b3.
Lemma F_80264 : fetch_word AsanUbsan.M.loaded_segments (0x802ac : word) = Some W_80264.
Proof. vm_refl. Qed.
Lemma D_80264 : decode_any W_80264 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80268 : bv 32 := 0x0107a7b3.
Lemma F_80268 : fetch_word AsanUbsan.M.loaded_segments (0x802b0 : word) = Some W_80268.
Proof. vm_refl. Qed.
Lemma D_80268 : decode_any W_80268 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8026c : bv 32 := 0x0017c793.
Lemma F_8026c : fetch_word AsanUbsan.M.loaded_segments (0x802b4 : word) = Some W_8026c.
Proof. vm_refl. Qed.
Lemma D_8026c : decode_any W_8026c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80270 : bv 32 := 0x00f8f7b3.
Lemma F_80270 : fetch_word AsanUbsan.M.loaded_segments (0x802b8 : word) = Some W_80270.
Proof. vm_refl. Qed.
Lemma D_80270 : decode_any W_80270 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80274 : bv 32 := 0x00e6fa63.
Lemma F_80274 : fetch_word AsanUbsan.M.loaded_segments (0x802bc : word) = Some W_80274.
Proof. vm_refl. Qed.
Lemma D_80274 : decode_any W_80274 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80278 : bv 32 := 0x0006c803.
Lemma F_80278 : fetch_word AsanUbsan.M.loaded_segments (0x802c0 : word) = Some W_80278.
Proof. vm_refl. Qed.
Lemma D_80278 : decode_any W_80278 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8027c : bv 32 := 0x00168693.
Lemma F_8027c : fetch_word AsanUbsan.M.loaded_segments (0x802c4 : word) = Some W_8027c.
Proof. vm_refl. Qed.
Lemma D_8027c : decode_any W_8027c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80280 : bv 32 := 0x00f867b3.
Lemma F_80280 : fetch_word AsanUbsan.M.loaded_segments (0x802c8 : word) = Some W_80280.
Proof. vm_refl. Qed.
Lemma D_80280 : decode_any W_80280 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80284 : bv 32 := 0xfee69ae3.
Lemma F_80284 : fetch_word AsanUbsan.M.loaded_segments (0x802cc : word) = Some W_80284.
Proof. vm_refl. Qed.
Lemma D_80284 : decode_any W_80284 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_80288 : bv 32 := 0x0ff7f693.
Lemma F_80288 : fetch_word AsanUbsan.M.loaded_segments (0x802d0 : word) = Some W_80288.
Proof. vm_refl. Qed.
Lemma D_80288 : decode_any W_80288 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_8028c : bv 32 := 0xd80680e3.
Lemma F_8028c : fetch_word AsanUbsan.M.loaded_segments (0x802d4 : word) = Some W_8028c.
Proof. vm_refl. Qed.
Lemma D_8028c : decode_any W_8028c = Some (Branch BC_EQ 13 0 7552, 4%Z).
Proof. vm_refl. Qed.

Definition W_80290 : bv 32 := 0x00050493.
Lemma F_80290 : fetch_word AsanUbsan.M.loaded_segments (0x802d8 : word) = Some W_80290.
Proof. vm_refl. Qed.
Lemma D_80290 : decode_any W_80290 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80294 : bv 32 := 0x00058b13.
Lemma F_80294 : fetch_word AsanUbsan.M.loaded_segments (0x802dc : word) = Some W_80294.
Proof. vm_refl. Qed.
Lemma D_80294 : decode_any W_80294 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80298 : bv 32 := 0x00060593.
Lemma F_80298 : fetch_word AsanUbsan.M.loaded_segments (0x802e0 : word) = Some W_80298.
Proof. vm_refl. Qed.
Lemma D_80298 : decode_any W_80298 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8029c : bv 32 := 0x00060913.
Lemma F_8029c : fetch_word AsanUbsan.M.loaded_segments (0x802e4 : word) = Some W_8029c.
Proof. vm_refl. Qed.
Lemma D_8029c : decode_any W_8029c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802a0 : bv 32 := 0x778020ef.
Lemma F_802a0 : fetch_word AsanUbsan.M.loaded_segments (0x802e8 : word) = Some W_802a0.
Proof. vm_refl. Qed.
Lemma D_802a0 : decode_any W_802a0 = Some (Jal 1 10104, 4%Z).
Proof. vm_refl. Qed.

Definition W_802a4 : bv 32 := 0x000b0593.
Lemma F_802a4 : fetch_word AsanUbsan.M.loaded_segments (0x802ec : word) = Some W_802a4.
Proof. vm_refl. Qed.
Lemma D_802a4 : decode_any W_802a4 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802a8 : bv 32 := 0x00090613.
Lemma F_802a8 : fetch_word AsanUbsan.M.loaded_segments (0x802f0 : word) = Some W_802a8.
Proof. vm_refl. Qed.
Lemma D_802a8 : decode_any W_802a8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802ac : bv 32 := 0x00050993.
Lemma F_802ac : fetch_word AsanUbsan.M.loaded_segments (0x802f4 : word) = Some W_802ac.
Proof. vm_refl. Qed.
Lemma D_802ac : decode_any W_802ac = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802b0 : bv 32 := 0x00048513.
Lemma F_802b0 : fetch_word AsanUbsan.M.loaded_segments (0x802f8 : word) = Some W_802b0.
Proof. vm_refl. Qed.
Lemma D_802b0 : decode_any W_802b0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802b4 : bv 32 := 0xd4098ce3.
Lemma F_802b4 : fetch_word AsanUbsan.M.loaded_segments (0x802fc : word) = Some W_802b4.
Proof. vm_refl. Qed.
Lemma D_802b4 : decode_any W_802b4 = Some (Branch BC_EQ 19 0 7512, 4%Z).
Proof. vm_refl. Qed.

Definition W_803e8 : bv 32 := 0x81010113.
Lemma F_803e8 : fetch_word AsanUbsan.M.loaded_segments (0x80430 : word) = Some W_803e8.
Proof. vm_refl. Qed.
Lemma D_803e8 : decode_any W_803e8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_803ec : bv 32 := 0x7e113423.
Lemma F_803ec : fetch_word AsanUbsan.M.loaded_segments (0x80434 : word) = Some W_803ec.
Proof. vm_refl. Qed.
Lemma D_803ec : decode_any W_803ec = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_803f0 : bv 32 := 0x7e813023.
Lemma F_803f0 : fetch_word AsanUbsan.M.loaded_segments (0x80438 : word) = Some W_803f0.
Proof. vm_refl. Qed.
Lemma D_803f0 : decode_any W_803f0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_803f4 : bv 32 := 0x7c913c23.
Lemma F_803f4 : fetch_word AsanUbsan.M.loaded_segments (0x8043c : word) = Some W_803f4.
Proof. vm_refl. Qed.
Lemma D_803f4 : decode_any W_803f4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_803f8 : bv 32 := 0x7d213823.
Lemma F_803f8 : fetch_word AsanUbsan.M.loaded_segments (0x80440 : word) = Some W_803f8.
Proof. vm_refl. Qed.
Lemma D_803f8 : decode_any W_803f8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_803fc : bv 32 := 0x7d313423.
Lemma F_803fc : fetch_word AsanUbsan.M.loaded_segments (0x80444 : word) = Some W_803fc.
Proof. vm_refl. Qed.
Lemma D_803fc : decode_any W_803fc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80400 : bv 32 := 0x7d413023.
Lemma F_80400 : fetch_word AsanUbsan.M.loaded_segments (0x80448 : word) = Some W_80400.
Proof. vm_refl. Qed.
Lemma D_80400 : decode_any W_80400 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80404 : bv 32 := 0x7b513c23.
Lemma F_80404 : fetch_word AsanUbsan.M.loaded_segments (0x8044c : word) = Some W_80404.
Proof. vm_refl. Qed.
Lemma D_80404 : decode_any W_80404 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80408 : bv 32 := 0x7b613823.
Lemma F_80408 : fetch_word AsanUbsan.M.loaded_segments (0x80450 : word) = Some W_80408.
Proof. vm_refl. Qed.
Lemma D_80408 : decode_any W_80408 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_8040c : bv 32 := 0x7b713423.
Lemma F_8040c : fetch_word AsanUbsan.M.loaded_segments (0x80454 : word) = Some W_8040c.
Proof. vm_refl. Qed.
Lemma D_8040c : decode_any W_8040c = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_80410 : bv 32 := 0x7b813023.
Lemma F_80410 : fetch_word AsanUbsan.M.loaded_segments (0x80458 : word) = Some W_80410.
Proof. vm_refl. Qed.
Lemma D_80410 : decode_any W_80410 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_80414 : bv 32 := 0x7f010413.
Lemma F_80414 : fetch_word AsanUbsan.M.loaded_segments (0x8045c : word) = Some W_80414.
Proof. vm_refl. Qed.
Lemma D_80414 : decode_any W_80414 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80418 : bv 32 := 0xf8010113.
Lemma F_80418 : fetch_word AsanUbsan.M.loaded_segments (0x80460 : word) = Some W_80418.
Proof. vm_refl. Qed.
Lemma D_80418 : decode_any W_80418 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_8041c : bv 32 := 0x000d5697.
Lemma F_8041c : fetch_word AsanUbsan.M.loaded_segments (0x80464 : word) = Some W_8041c.
Proof. vm_refl. Qed.
Lemma D_8041c : decode_any W_8041c = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_80420 : bv 32 := 0xc046b683.
Lemma F_80420 : fetch_word AsanUbsan.M.loaded_segments (0x80468 : word) = Some W_80420.
Proof. vm_refl. Qed.
Lemma D_80420 : decode_any W_80420 = Some (Load SZ8 true 13 13 3076, 4%Z).
Proof. vm_refl. Qed.

Definition W_80424 : bv 32 := 0x0006c683.
Lemma F_80424 : fetch_word AsanUbsan.M.loaded_segments (0x8046c : word) = Some W_80424.
Proof. vm_refl. Qed.
Lemma D_80424 : decode_any W_80424 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80428 : bv 32 := 0x0e068a63.
Lemma F_80428 : fetch_word AsanUbsan.M.loaded_segments (0x80470 : word) = Some W_80428.
Proof. vm_refl. Qed.
Lemma D_80428 : decode_any W_80428 = Some (Branch BC_EQ 13 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_8042c : bv 32 := 0x80040a93.
Lemma F_8042c : fetch_word AsanUbsan.M.loaded_segments (0x80474 : word) = Some W_8042c.
Proof. vm_refl. Qed.
Lemma D_8042c : decode_any W_8042c = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80430 : bv 32 := 0xf98a8a93.
Lemma F_80430 : fetch_word AsanUbsan.M.loaded_segments (0x80478 : word) = Some W_80430.
Proof. vm_refl. Qed.
Lemma D_80430 : decode_any W_80430 = Some (OpImm ALU_ADD 21 21 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80434 : bv 32 := 0x00c589b3.
Lemma F_80434 : fetch_word AsanUbsan.M.loaded_segments (0x8047c : word) = Some W_80434.
Proof. vm_refl. Qed.
Lemma D_80434 : decode_any W_80434 = Some (Op ALU_ADD 19 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80438 : bv 32 := 0x00c50a33.
Lemma F_80438 : fetch_word AsanUbsan.M.loaded_segments (0x80480 : word) = Some W_80438.
Proof. vm_refl. Qed.
Lemma D_80438 : decode_any W_80438 = Some (Op ALU_ADD 20 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8043c : bv 32 := 0x00b50663.
Lemma F_8043c : fetch_word AsanUbsan.M.loaded_segments (0x80484 : word) = Some W_8043c.
Proof. vm_refl. Qed.
Lemma D_8043c : decode_any W_8043c = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80440 : bv 32 := 0x0145f463.
Lemma F_80440 : fetch_word AsanUbsan.M.loaded_segments (0x80488 : word) = Some W_80440.
Proof. vm_refl. Qed.
Lemma D_80440 : decode_any W_80440 = Some (Branch BC_GEU 11 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80444 : bv 32 := 0x1b356e63.
Lemma F_80444 : fetch_word AsanUbsan.M.loaded_segments (0x8048c : word) = Some W_80444.
Proof. vm_refl. Qed.
Lemma D_80444 : decode_any W_80444 = Some (Branch BC_LTU 10 19 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_80448 : bv 32 := 0xfff5c693.
Lemma F_80448 : fetch_word AsanUbsan.M.loaded_segments (0x80490 : word) = Some W_80448.
Proof. vm_refl. Qed.
Lemma D_80448 : decode_any W_80448 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8044c : bv 32 := 0x26c6e863.
Lemma F_8044c : fetch_word AsanUbsan.M.loaded_segments (0x80494 : word) = Some W_8044c.
Proof. vm_refl. Qed.
Lemma D_8044c : decode_any W_8044c = Some (Branch BC_LTU 13 12 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_80450 : bv 32 := 0xfbf60b13.
Lemma F_80450 : fetch_word AsanUbsan.M.loaded_segments (0x80498 : word) = Some W_80450.
Proof. vm_refl. Qed.
Lemma D_80450 : decode_any W_80450 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_80454 : bv 32 := 0xfbf00693.
Lemma F_80454 : fetch_word AsanUbsan.M.loaded_segments (0x8049c : word) = Some W_80454.
Proof. vm_refl. Qed.
Lemma D_80454 : decode_any W_80454 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_80458 : bv 32 := 0x2f66f663.
Lemma F_80458 : fetch_word AsanUbsan.M.loaded_segments (0x804a0 : word) = Some W_80458.
Proof. vm_refl. Qed.
Lemma D_80458 : decode_any W_80458 = Some (Branch BC_GEU 13 22 748, 4%Z).
Proof. vm_refl. Qed.

Definition W_8045c : bv 32 := 0x000d4697.
Lemma F_8045c : fetch_word AsanUbsan.M.loaded_segments (0x804a4 : word) = Some W_8045c.
Proof. vm_refl. Qed.
Lemma D_8045c : decode_any W_8045c = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_80460 : bv 32 := 0x05c6b683.
Lemma F_80460 : fetch_word AsanUbsan.M.loaded_segments (0x804a8 : word) = Some W_80460.
Proof. vm_refl. Qed.
Lemma D_80460 : decode_any W_80460 = Some (Load SZ8 true 13 13 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_80464 : bv 32 := 0x0006b703.
Lemma F_80464 : fetch_word AsanUbsan.M.loaded_segments (0x804ac : word) = Some W_80464.
Proof. vm_refl. Qed.
Lemma D_80464 : decode_any W_80464 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80468 : bv 32 := 0xfff98993.
Lemma F_80468 : fetch_word AsanUbsan.M.loaded_segments (0x804b0 : word) = Some W_80468.
Proof. vm_refl. Qed.
Lemma D_80468 : decode_any W_80468 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8046c : bv 32 := 0x0035d693.
Lemma F_8046c : fetch_word AsanUbsan.M.loaded_segments (0x804b4 : word) = Some W_8046c.
Proof. vm_refl. Qed.
Lemma D_8046c : decode_any W_8046c = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80470 : bv 32 := 0x0039d793.
Lemma F_80470 : fetch_word AsanUbsan.M.loaded_segments (0x804b8 : word) = Some W_80470.
Proof. vm_refl. Qed.
Lemma D_80470 : decode_any W_80470 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80474 : bv 32 := 0x00d706b3.
Lemma F_80474 : fetch_word AsanUbsan.M.loaded_segments (0x804bc : word) = Some W_80474.
Proof. vm_refl. Qed.
Lemma D_80474 : decode_any W_80474 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80478 : bv 32 := 0x00f70733.
Lemma F_80478 : fetch_word AsanUbsan.M.loaded_segments (0x804c0 : word) = Some W_80478.
Proof. vm_refl. Qed.
Lemma D_80478 : decode_any W_80478 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8047c : bv 32 := 0xff86f793.
Lemma F_8047c : fetch_word AsanUbsan.M.loaded_segments (0x804c4 : word) = Some W_8047c.
Proof. vm_refl. Qed.
Lemma D_8047c : decode_any W_8047c = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_80480 : bv 32 := 0xff877813.
Lemma F_80480 : fetch_word AsanUbsan.M.loaded_segments (0x804c8 : word) = Some W_80480.
Proof. vm_refl. Qed.
Lemma D_80480 : decode_any W_80480 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_80484 : bv 32 := 0x0007b783.
Lemma F_80484 : fetch_word AsanUbsan.M.loaded_segments (0x804cc : word) = Some W_80484.
Proof. vm_refl. Qed.
Lemma D_80484 : decode_any W_80484 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80488 : bv 32 := 0x00083803.
Lemma F_80488 : fetch_word AsanUbsan.M.loaded_segments (0x804d0 : word) = Some W_80488.
Proof. vm_refl. Qed.
Lemma D_80488 : decode_any W_80488 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8048c : bv 32 := 0x00f867b3.
Lemma F_8048c : fetch_word AsanUbsan.M.loaded_segments (0x804d4 : word) = Some W_8048c.
Proof. vm_refl. Qed.
Lemma D_8048c : decode_any W_8048c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80490 : bv 32 := 0x2a079e63.
Lemma F_80490 : fetch_word AsanUbsan.M.loaded_segments (0x804d8 : word) = Some W_80490.
Proof. vm_refl. Qed.
Lemma D_80490 : decode_any W_80490 = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

Definition W_80494 : bv 32 := 0xfff54693.
Lemma F_80494 : fetch_word AsanUbsan.M.loaded_segments (0x804dc : word) = Some W_80494.
Proof. vm_refl. Qed.
Lemma D_80494 : decode_any W_80494 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80498 : bv 32 := 0x0cc6ee63.
Lemma F_80498 : fetch_word AsanUbsan.M.loaded_segments (0x804e0 : word) = Some W_80498.
Proof. vm_refl. Qed.
Lemma D_80498 : decode_any W_80498 = Some (Branch BC_LTU 13 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_8049c : bv 32 := 0xfbf00693.
Lemma F_8049c : fetch_word AsanUbsan.M.loaded_segments (0x804e4 : word) = Some W_8049c.
Proof. vm_refl. Qed.
Lemma D_8049c : decode_any W_8049c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a0 : bv 32 := 0x1566fc63.
Lemma F_804a0 : fetch_word AsanUbsan.M.loaded_segments (0x804e8 : word) = Some W_804a0.
Proof. vm_refl. Qed.
Lemma D_804a0 : decode_any W_804a0 = Some (Branch BC_GEU 13 22 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a4 : bv 32 := 0x000d4697.
Lemma F_804a4 : fetch_word AsanUbsan.M.loaded_segments (0x804ec : word) = Some W_804a4.
Proof. vm_refl. Qed.
Lemma D_804a4 : decode_any W_804a4 = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a8 : bv 32 := 0x0146b683.
Lemma F_804a8 : fetch_word AsanUbsan.M.loaded_segments (0x804f0 : word) = Some W_804a8.
Proof. vm_refl. Qed.
Lemma D_804a8 : decode_any W_804a8 = Some (Load SZ8 true 13 13 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_804ac : bv 32 := 0x0006b703.
Lemma F_804ac : fetch_word AsanUbsan.M.loaded_segments (0x804f4 : word) = Some W_804ac.
Proof. vm_refl. Qed.
Lemma D_804ac : decode_any W_804ac = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804b0 : bv 32 := 0xfffa0a13.
Lemma F_804b0 : fetch_word AsanUbsan.M.loaded_segments (0x804f8 : word) = Some W_804b0.
Proof. vm_refl. Qed.
Lemma D_804b0 : decode_any W_804b0 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_804b4 : bv 32 := 0x00355693.
Lemma F_804b4 : fetch_word AsanUbsan.M.loaded_segments (0x804fc : word) = Some W_804b4.
Proof. vm_refl. Qed.
Lemma D_804b4 : decode_any W_804b4 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_804b8 : bv 32 := 0x003a5793.
Lemma F_804b8 : fetch_word AsanUbsan.M.loaded_segments (0x80500 : word) = Some W_804b8.
Proof. vm_refl. Qed.
Lemma D_804b8 : decode_any W_804b8 = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_804bc : bv 32 := 0x00d706b3.
Lemma F_804bc : fetch_word AsanUbsan.M.loaded_segments (0x80504 : word) = Some W_804bc.
Proof. vm_refl. Qed.
Lemma D_804bc : decode_any W_804bc = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_804c0 : bv 32 := 0x00f70733.
Lemma F_804c0 : fetch_word AsanUbsan.M.loaded_segments (0x80508 : word) = Some W_804c0.
Proof. vm_refl. Qed.
Lemma D_804c0 : decode_any W_804c0 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_804c4 : bv 32 := 0xff86f793.
Lemma F_804c4 : fetch_word AsanUbsan.M.loaded_segments (0x8050c : word) = Some W_804c4.
Proof. vm_refl. Qed.
Lemma D_804c4 : decode_any W_804c4 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_804c8 : bv 32 := 0xff877813.
Lemma F_804c8 : fetch_word AsanUbsan.M.loaded_segments (0x80510 : word) = Some W_804c8.
Proof. vm_refl. Qed.
Lemma D_804c8 : decode_any W_804c8 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_804cc : bv 32 := 0x0007b783.
Lemma F_804cc : fetch_word AsanUbsan.M.loaded_segments (0x80514 : word) = Some W_804cc.
Proof. vm_refl. Qed.
Lemma D_804cc : decode_any W_804cc = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804d0 : bv 32 := 0x00083803.
Lemma F_804d0 : fetch_word AsanUbsan.M.loaded_segments (0x80518 : word) = Some W_804d0.
Proof. vm_refl. Qed.
Lemma D_804d0 : decode_any W_804d0 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804d4 : bv 32 := 0x00f867b3.
Lemma F_804d4 : fetch_word AsanUbsan.M.loaded_segments (0x8051c : word) = Some W_804d4.
Proof. vm_refl. Qed.
Lemma D_804d4 : decode_any W_804d4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_804d8 : bv 32 := 0x36079a63.
Lemma F_804d8 : fetch_word AsanUbsan.M.loaded_segments (0x80520 : word) = Some W_804d8.
Proof. vm_refl. Qed.
Lemma D_804d8 : decode_any W_804d8 = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

Definition W_804dc : bv 32 := 0x000d6697.
Lemma F_804dc : fetch_word AsanUbsan.M.loaded_segments (0x80524 : word) = Some W_804dc.
Proof. vm_refl. Qed.
Lemma D_804dc : decode_any W_804dc = Some (Auipc 13 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_804e0 : bv 32 := 0xffc6b683.
Lemma F_804e0 : fetch_word AsanUbsan.M.loaded_segments (0x80528 : word) = Some W_804e0.
Proof. vm_refl. Qed.
Lemma D_804e0 : decode_any W_804e0 = Some (Load SZ8 true 13 13 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_804e4 : bv 32 := 0x000680e7.
Lemma F_804e4 : fetch_word AsanUbsan.M.loaded_segments (0x8052c : word) = Some W_804e4.
Proof. vm_refl. Qed.
Lemma D_804e4 : decode_any W_804e4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804e8 : bv 32 := 0x08010113.
Lemma F_804e8 : fetch_word AsanUbsan.M.loaded_segments (0x80530 : word) = Some W_804e8.
Proof. vm_refl. Qed.
Lemma D_804e8 : decode_any W_804e8 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_804ec : bv 32 := 0x7e813083.
Lemma F_804ec : fetch_word AsanUbsan.M.loaded_segments (0x80534 : word) = Some W_804ec.
Proof. vm_refl. Qed.
Lemma D_804ec : decode_any W_804ec = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_804f0 : bv 32 := 0x7e013403.
Lemma F_804f0 : fetch_word AsanUbsan.M.loaded_segments (0x80538 : word) = Some W_804f0.
Proof. vm_refl. Qed.
Lemma D_804f0 : decode_any W_804f0 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_804f4 : bv 32 := 0x7d813483.
Lemma F_804f4 : fetch_word AsanUbsan.M.loaded_segments (0x8053c : word) = Some W_804f4.
Proof. vm_refl. Qed.
Lemma D_804f4 : decode_any W_804f4 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_804f8 : bv 32 := 0x7d013903.
Lemma F_804f8 : fetch_word AsanUbsan.M.loaded_segments (0x80540 : word) = Some W_804f8.
Proof. vm_refl. Qed.
Lemma D_804f8 : decode_any W_804f8 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_804fc : bv 32 := 0x7c813983.
Lemma F_804fc : fetch_word AsanUbsan.M.loaded_segments (0x80544 : word) = Some W_804fc.
Proof. vm_refl. Qed.
Lemma D_804fc : decode_any W_804fc = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80500 : bv 32 := 0x7c013a03.
Lemma F_80500 : fetch_word AsanUbsan.M.loaded_segments (0x80548 : word) = Some W_80500.
Proof. vm_refl. Qed.
Lemma D_80500 : decode_any W_80500 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80504 : bv 32 := 0x7b813a83.
Lemma F_80504 : fetch_word AsanUbsan.M.loaded_segments (0x8054c : word) = Some W_80504.
Proof. vm_refl. Qed.
Lemma D_80504 : decode_any W_80504 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80508 : bv 32 := 0x7b013b03.
Lemma F_80508 : fetch_word AsanUbsan.M.loaded_segments (0x80550 : word) = Some W_80508.
Proof. vm_refl. Qed.
Lemma D_80508 : decode_any W_80508 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_8050c : bv 32 := 0x7a813b83.
Lemma F_8050c : fetch_word AsanUbsan.M.loaded_segments (0x80554 : word) = Some W_8050c.
Proof. vm_refl. Qed.
Lemma D_8050c : decode_any W_8050c = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_80510 : bv 32 := 0x7a013c03.
Lemma F_80510 : fetch_word AsanUbsan.M.loaded_segments (0x80558 : word) = Some W_80510.
Proof. vm_refl. Qed.
Lemma D_80510 : decode_any W_80510 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_80514 : bv 32 := 0x7f010113.
Lemma F_80514 : fetch_word AsanUbsan.M.loaded_segments (0x8055c : word) = Some W_80514.
Proof. vm_refl. Qed.
Lemma D_80514 : decode_any W_80514 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80518 : bv 32 := 0x00008067.
Lemma F_80518 : fetch_word AsanUbsan.M.loaded_segments (0x80560 : word) = Some W_80518.
Proof. vm_refl. Qed.
Lemma D_80518 : decode_any W_80518 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_805f8 : bv 32 := 0x28061463.
Lemma F_805f8 : fetch_word AsanUbsan.M.loaded_segments (0x80640 : word) = Some W_805f8.
Proof. vm_refl. Qed.
Lemma D_805f8 : decode_any W_805f8 = Some (Branch BC_NE 12 0 648, 4%Z).
Proof. vm_refl. Qed.

Definition W_805fc : bv 32 := 0xee1ff06f.
Lemma F_805fc : fetch_word AsanUbsan.M.loaded_segments (0x80644 : word) = Some W_805fc.
Proof. vm_refl. Qed.
Lemma D_805fc : decode_any W_805fc = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

Definition W_80744 : bv 32 := 0x02061e63.
Lemma F_80744 : fetch_word AsanUbsan.M.loaded_segments (0x8078c : word) = Some W_80744.
Proof. vm_refl. Qed.
Lemma D_80744 : decode_any W_80744 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_80748 : bv 32 := 0xd4dff06f.
Lemma F_80748 : fetch_word AsanUbsan.M.loaded_segments (0x80790 : word) = Some W_80748.
Proof. vm_refl. Qed.
Lemma D_80748 : decode_any W_80748 = Some (Jal 0 2096460, 4%Z).
Proof. vm_refl. Qed.

Definition W_8074c : bv 32 := 0x00070783.
Lemma F_8074c : fetch_word AsanUbsan.M.loaded_segments (0x80794 : word) = Some W_8074c.
Proof. vm_refl. Qed.
Lemma D_8074c : decode_any W_8074c = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80750 : bv 32 := 0x0079f813.
Lemma F_80750 : fetch_word AsanUbsan.M.loaded_segments (0x80798 : word) = Some W_80750.
Proof. vm_refl. Qed.
Lemma D_80750 : decode_any W_80750 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80754 : bv 32 := 0x00f038b3.
Lemma F_80754 : fetch_word AsanUbsan.M.loaded_segments (0x8079c : word) = Some W_80754.
Proof. vm_refl. Qed.
Lemma D_80754 : decode_any W_80754 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80758 : bv 32 := 0x00f827b3.
Lemma F_80758 : fetch_word AsanUbsan.M.loaded_segments (0x807a0 : word) = Some W_80758.
Proof. vm_refl. Qed.
Lemma D_80758 : decode_any W_80758 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8075c : bv 32 := 0x0017c793.
Lemma F_8075c : fetch_word AsanUbsan.M.loaded_segments (0x807a4 : word) = Some W_8075c.
Proof. vm_refl. Qed.
Lemma D_8075c : decode_any W_8075c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80760 : bv 32 := 0x00f8f7b3.
Lemma F_80760 : fetch_word AsanUbsan.M.loaded_segments (0x807a8 : word) = Some W_80760.
Proof. vm_refl. Qed.
Lemma D_80760 : decode_any W_80760 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80764 : bv 32 := 0x00e6fa63.
Lemma F_80764 : fetch_word AsanUbsan.M.loaded_segments (0x807ac : word) = Some W_80764.
Proof. vm_refl. Qed.
Lemma D_80764 : decode_any W_80764 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80768 : bv 32 := 0x0006c803.
Lemma F_80768 : fetch_word AsanUbsan.M.loaded_segments (0x807b0 : word) = Some W_80768.
Proof. vm_refl. Qed.
Lemma D_80768 : decode_any W_80768 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8076c : bv 32 := 0x00168693.
Lemma F_8076c : fetch_word AsanUbsan.M.loaded_segments (0x807b4 : word) = Some W_8076c.
Proof. vm_refl. Qed.
Lemma D_8076c : decode_any W_8076c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80770 : bv 32 := 0x00f867b3.
Lemma F_80770 : fetch_word AsanUbsan.M.loaded_segments (0x807b8 : word) = Some W_80770.
Proof. vm_refl. Qed.
Lemma D_80770 : decode_any W_80770 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80774 : bv 32 := 0xfee69ae3.
Lemma F_80774 : fetch_word AsanUbsan.M.loaded_segments (0x807bc : word) = Some W_80774.
Proof. vm_refl. Qed.
Lemma D_80774 : decode_any W_80774 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_80778 : bv 32 := 0x0ff7f693.
Lemma F_80778 : fetch_word AsanUbsan.M.loaded_segments (0x807c0 : word) = Some W_80778.
Proof. vm_refl. Qed.
Lemma D_80778 : decode_any W_80778 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_8077c : bv 32 := 0xd0068ce3.
Lemma F_8077c : fetch_word AsanUbsan.M.loaded_segments (0x807c4 : word) = Some W_8077c.
Proof. vm_refl. Qed.
Lemma D_8077c : decode_any W_8077c = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

Definition W_80780 : bv 32 := 0x00050b93.
Lemma F_80780 : fetch_word AsanUbsan.M.loaded_segments (0x807c8 : word) = Some W_80780.
Proof. vm_refl. Qed.
Lemma D_80780 : decode_any W_80780 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80784 : bv 32 := 0x00058513.
Lemma F_80784 : fetch_word AsanUbsan.M.loaded_segments (0x807cc : word) = Some W_80784.
Proof. vm_refl. Qed.
Lemma D_80784 : decode_any W_80784 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80788 : bv 32 := 0x00058c13.
Lemma F_80788 : fetch_word AsanUbsan.M.loaded_segments (0x807d0 : word) = Some W_80788.
Proof. vm_refl. Qed.
Lemma D_80788 : decode_any W_80788 = Some (OpImm ALU_ADD 24 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8078c : bv 32 := 0x00060593.
Lemma F_8078c : fetch_word AsanUbsan.M.loaded_segments (0x807d4 : word) = Some W_8078c.
Proof. vm_refl. Qed.
Lemma D_8078c : decode_any W_8078c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80790 : bv 32 := 0x00060493.
Lemma F_80790 : fetch_word AsanUbsan.M.loaded_segments (0x807d8 : word) = Some W_80790.
Proof. vm_refl. Qed.
Lemma D_80790 : decode_any W_80790 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80794 : bv 32 := 0x284020ef.
Lemma F_80794 : fetch_word AsanUbsan.M.loaded_segments (0x807dc : word) = Some W_80794.
Proof. vm_refl. Qed.
Lemma D_80794 : decode_any W_80794 = Some (Jal 1 8836, 4%Z).
Proof. vm_refl. Qed.

Definition W_80798 : bv 32 := 0x000c0593.
Lemma F_80798 : fetch_word AsanUbsan.M.loaded_segments (0x807e0 : word) = Some W_80798.
Proof. vm_refl. Qed.
Lemma D_80798 : decode_any W_80798 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8079c : bv 32 := 0x00048613.
Lemma F_8079c : fetch_word AsanUbsan.M.loaded_segments (0x807e4 : word) = Some W_8079c.
Proof. vm_refl. Qed.
Lemma D_8079c : decode_any W_8079c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_807a0 : bv 32 := 0x00050913.
Lemma F_807a0 : fetch_word AsanUbsan.M.loaded_segments (0x807e8 : word) = Some W_807a0.
Proof. vm_refl. Qed.
Lemma D_807a0 : decode_any W_807a0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_807a4 : bv 32 := 0x000b8513.
Lemma F_807a4 : fetch_word AsanUbsan.M.loaded_segments (0x807ec : word) = Some W_807a4.
Proof. vm_refl. Qed.
Lemma D_807a4 : decode_any W_807a4 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_807a8 : bv 32 := 0xce0906e3.
Lemma F_807a8 : fetch_word AsanUbsan.M.loaded_segments (0x807f0 : word) = Some W_807a8.
Proof. vm_refl. Qed.
Lemma D_807a8 : decode_any W_807a8 = Some (Branch BC_EQ 18 0 7404, 4%Z).
Proof. vm_refl. Qed.

Definition W_8084c : bv 32 := 0x00070783.
Lemma F_8084c : fetch_word AsanUbsan.M.loaded_segments (0x80894 : word) = Some W_8084c.
Proof. vm_refl. Qed.
Lemma D_8084c : decode_any W_8084c = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80850 : bv 32 := 0x007a7813.
Lemma F_80850 : fetch_word AsanUbsan.M.loaded_segments (0x80898 : word) = Some W_80850.
Proof. vm_refl. Qed.
Lemma D_80850 : decode_any W_80850 = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80854 : bv 32 := 0x00f038b3.
Lemma F_80854 : fetch_word AsanUbsan.M.loaded_segments (0x8089c : word) = Some W_80854.
Proof. vm_refl. Qed.
Lemma D_80854 : decode_any W_80854 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80858 : bv 32 := 0x00f827b3.
Lemma F_80858 : fetch_word AsanUbsan.M.loaded_segments (0x808a0 : word) = Some W_80858.
Proof. vm_refl. Qed.
Lemma D_80858 : decode_any W_80858 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8085c : bv 32 := 0x0017c793.
Lemma F_8085c : fetch_word AsanUbsan.M.loaded_segments (0x808a4 : word) = Some W_8085c.
Proof. vm_refl. Qed.
Lemma D_8085c : decode_any W_8085c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80860 : bv 32 := 0x00f8f7b3.
Lemma F_80860 : fetch_word AsanUbsan.M.loaded_segments (0x808a8 : word) = Some W_80860.
Proof. vm_refl. Qed.
Lemma D_80860 : decode_any W_80860 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80864 : bv 32 := 0x00e6fa63.
Lemma F_80864 : fetch_word AsanUbsan.M.loaded_segments (0x808ac : word) = Some W_80864.
Proof. vm_refl. Qed.
Lemma D_80864 : decode_any W_80864 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80868 : bv 32 := 0x0006c803.
Lemma F_80868 : fetch_word AsanUbsan.M.loaded_segments (0x808b0 : word) = Some W_80868.
Proof. vm_refl. Qed.
Lemma D_80868 : decode_any W_80868 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8086c : bv 32 := 0x00168693.
Lemma F_8086c : fetch_word AsanUbsan.M.loaded_segments (0x808b4 : word) = Some W_8086c.
Proof. vm_refl. Qed.
Lemma D_8086c : decode_any W_8086c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80870 : bv 32 := 0x00f867b3.
Lemma F_80870 : fetch_word AsanUbsan.M.loaded_segments (0x808b8 : word) = Some W_80870.
Proof. vm_refl. Qed.
Lemma D_80870 : decode_any W_80870 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80874 : bv 32 := 0xfee69ae3.
Lemma F_80874 : fetch_word AsanUbsan.M.loaded_segments (0x808bc : word) = Some W_80874.
Proof. vm_refl. Qed.
Lemma D_80874 : decode_any W_80874 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_80878 : bv 32 := 0x0ff7f693.
Lemma F_80878 : fetch_word AsanUbsan.M.loaded_segments (0x808c0 : word) = Some W_80878.
Proof. vm_refl. Qed.
Lemma D_80878 : decode_any W_80878 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_8087c : bv 32 := 0xc60680e3.
Lemma F_8087c : fetch_word AsanUbsan.M.loaded_segments (0x808c4 : word) = Some W_8087c.
Proof. vm_refl. Qed.
Lemma D_8087c : decode_any W_8087c = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.

Definition W_80880 : bv 32 := 0x00050493.
Lemma F_80880 : fetch_word AsanUbsan.M.loaded_segments (0x808c8 : word) = Some W_80880.
Proof. vm_refl. Qed.
Lemma D_80880 : decode_any W_80880 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80884 : bv 32 := 0x00058b13.
Lemma F_80884 : fetch_word AsanUbsan.M.loaded_segments (0x808cc : word) = Some W_80884.
Proof. vm_refl. Qed.
Lemma D_80884 : decode_any W_80884 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80888 : bv 32 := 0x00060593.
Lemma F_80888 : fetch_word AsanUbsan.M.loaded_segments (0x808d0 : word) = Some W_80888.
Proof. vm_refl. Qed.
Lemma D_80888 : decode_any W_80888 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8088c : bv 32 := 0x00060913.
Lemma F_8088c : fetch_word AsanUbsan.M.loaded_segments (0x808d4 : word) = Some W_8088c.
Proof. vm_refl. Qed.
Lemma D_8088c : decode_any W_8088c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80890 : bv 32 := 0x188020ef.
Lemma F_80890 : fetch_word AsanUbsan.M.loaded_segments (0x808d8 : word) = Some W_80890.
Proof. vm_refl. Qed.
Lemma D_80890 : decode_any W_80890 = Some (Jal 1 8584, 4%Z).
Proof. vm_refl. Qed.

Definition W_80894 : bv 32 := 0x000b0593.
Lemma F_80894 : fetch_word AsanUbsan.M.loaded_segments (0x808dc : word) = Some W_80894.
Proof. vm_refl. Qed.
Lemma D_80894 : decode_any W_80894 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80898 : bv 32 := 0x00090613.
Lemma F_80898 : fetch_word AsanUbsan.M.loaded_segments (0x808e0 : word) = Some W_80898.
Proof. vm_refl. Qed.
Lemma D_80898 : decode_any W_80898 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8089c : bv 32 := 0x00050993.
Lemma F_8089c : fetch_word AsanUbsan.M.loaded_segments (0x808e4 : word) = Some W_8089c.
Proof. vm_refl. Qed.
Lemma D_8089c : decode_any W_8089c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a0 : bv 32 := 0x00048513.
Lemma F_808a0 : fetch_word AsanUbsan.M.loaded_segments (0x808e8 : word) = Some W_808a0.
Proof. vm_refl. Qed.
Lemma D_808a0 : decode_any W_808a0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a4 : bv 32 := 0xc2098ce3.
Lemma F_808a4 : fetch_word AsanUbsan.M.loaded_segments (0x808ec : word) = Some W_808a4.
Proof. vm_refl. Qed.
Lemma D_808a4 : decode_any W_808a4 = Some (Branch BC_EQ 19 0 7224, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a78 : bv 32 := 0xfe010113.
Lemma F_80a78 : fetch_word AsanUbsan.M.loaded_segments (0x80ac0 : word) = Some W_80a78.
Proof. vm_refl. Qed.
Lemma D_80a78 : decode_any W_80a78 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a7c : bv 32 := 0x00113c23.
Lemma F_80a7c : fetch_word AsanUbsan.M.loaded_segments (0x80ac4 : word) = Some W_80a7c.
Proof. vm_refl. Qed.
Lemma D_80a7c : decode_any W_80a7c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a80 : bv 32 := 0x00813823.
Lemma F_80a80 : fetch_word AsanUbsan.M.loaded_segments (0x80ac8 : word) = Some W_80a80.
Proof. vm_refl. Qed.
Lemma D_80a80 : decode_any W_80a80 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a84 : bv 32 := 0x00913423.
Lemma F_80a84 : fetch_word AsanUbsan.M.loaded_segments (0x80acc : word) = Some W_80a84.
Proof. vm_refl. Qed.
Lemma D_80a84 : decode_any W_80a84 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a88 : bv 32 := 0x01213023.
Lemma F_80a88 : fetch_word AsanUbsan.M.loaded_segments (0x80ad0 : word) = Some W_80a88.
Proof. vm_refl. Qed.
Lemma D_80a88 : decode_any W_80a88 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a8c : bv 32 := 0x00058413.
Lemma F_80a8c : fetch_word AsanUbsan.M.loaded_segments (0x80ad4 : word) = Some W_80a8c.
Proof. vm_refl. Qed.
Lemma D_80a8c : decode_any W_80a8c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a90 : bv 32 := 0x00050493.
Lemma F_80a90 : fetch_word AsanUbsan.M.loaded_segments (0x80ad8 : word) = Some W_80a90.
Proof. vm_refl. Qed.
Lemma D_80a90 : decode_any W_80a90 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a94 : bv 32 := 0x030000ef.
Lemma F_80a94 : fetch_word AsanUbsan.M.loaded_segments (0x80adc : word) = Some W_80a94.
Proof. vm_refl. Qed.
Lemma D_80a94 : decode_any W_80a94 = Some (Jal 1 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a98 : bv 32 := 0x00050913.
Lemma F_80a98 : fetch_word AsanUbsan.M.loaded_segments (0x80ae0 : word) = Some W_80a98.
Proof. vm_refl. Qed.
Lemma D_80a98 : decode_any W_80a98 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a9c : bv 32 := 0x00940533.
Lemma F_80a9c : fetch_word AsanUbsan.M.loaded_segments (0x80ae4 : word) = Some W_80a9c.
Proof. vm_refl. Qed.
Lemma D_80a9c : decode_any W_80a9c = Some (Op ALU_ADD 10 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aa0 : bv 32 := 0x024000ef.
Lemma F_80aa0 : fetch_word AsanUbsan.M.loaded_segments (0x80ae8 : word) = Some W_80aa0.
Proof. vm_refl. Qed.
Lemma D_80aa0 : decode_any W_80aa0 = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aa4 : bv 32 := 0x00050593.
Lemma F_80aa4 : fetch_word AsanUbsan.M.loaded_segments (0x80aec : word) = Some W_80aa4.
Proof. vm_refl. Qed.
Lemma D_80aa4 : decode_any W_80aa4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aa8 : bv 32 := 0x00090513.
Lemma F_80aa8 : fetch_word AsanUbsan.M.loaded_segments (0x80af0 : word) = Some W_80aa8.
Proof. vm_refl. Qed.
Lemma D_80aa8 : decode_any W_80aa8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aac : bv 32 := 0x01813083.
Lemma F_80aac : fetch_word AsanUbsan.M.loaded_segments (0x80af4 : word) = Some W_80aac.
Proof. vm_refl. Qed.
Lemma D_80aac : decode_any W_80aac = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ab0 : bv 32 := 0x01013403.
Lemma F_80ab0 : fetch_word AsanUbsan.M.loaded_segments (0x80af8 : word) = Some W_80ab0.
Proof. vm_refl. Qed.
Lemma D_80ab0 : decode_any W_80ab0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ab4 : bv 32 := 0x00813483.
Lemma F_80ab4 : fetch_word AsanUbsan.M.loaded_segments (0x80afc : word) = Some W_80ab4.
Proof. vm_refl. Qed.
Lemma D_80ab4 : decode_any W_80ab4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ab8 : bv 32 := 0x00013903.
Lemma F_80ab8 : fetch_word AsanUbsan.M.loaded_segments (0x80b00 : word) = Some W_80ab8.
Proof. vm_refl. Qed.
Lemma D_80ab8 : decode_any W_80ab8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80abc : bv 32 := 0x02010113.
Lemma F_80abc : fetch_word AsanUbsan.M.loaded_segments (0x80b04 : word) = Some W_80abc.
Proof. vm_refl. Qed.
Lemma D_80abc : decode_any W_80abc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ac0 : bv 32 := 0x3151b06f.
Lemma F_80ac0 : fetch_word AsanUbsan.M.loaded_segments (0x80b08 : word) = Some W_80ac0.
Proof. vm_refl. Qed.
Lemma D_80ac0 : decode_any W_80ac0 = Some (Jal 0 113428, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ac4 : bv 32 := 0x000d4597.
Lemma F_80ac4 : fetch_word AsanUbsan.M.loaded_segments (0x80b0c : word) = Some W_80ac4.
Proof. vm_refl. Qed.
Lemma D_80ac4 : decode_any W_80ac4 = Some (Auipc 11 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ac8 : bv 32 := 0x9f45b583.
Lemma F_80ac8 : fetch_word AsanUbsan.M.loaded_segments (0x80b10 : word) = Some W_80ac8.
Proof. vm_refl. Qed.
Lemma D_80ac8 : decode_any W_80ac8 = Some (Load SZ8 true 11 11 2548, 4%Z).
Proof. vm_refl. Qed.

Definition W_80acc : bv 32 := 0x0005b583.
Lemma F_80acc : fetch_word AsanUbsan.M.loaded_segments (0x80b14 : word) = Some W_80acc.
Proof. vm_refl. Qed.
Lemma D_80acc : decode_any W_80acc = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ad0 : bv 32 := 0xfff58613.
Lemma F_80ad0 : fetch_word AsanUbsan.M.loaded_segments (0x80b18 : word) = Some W_80ad0.
Proof. vm_refl. Qed.
Lemma D_80ad0 : decode_any W_80ad0 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ad4 : bv 32 := 0x00c5b6b3.
Lemma F_80ad4 : fetch_word AsanUbsan.M.loaded_segments (0x80b1c : word) = Some W_80ad4.
Proof. vm_refl. Qed.
Lemma D_80ad4 : decode_any W_80ad4 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ad8 : bv 32 := 0xfff68693.
Lemma F_80ad8 : fetch_word AsanUbsan.M.loaded_segments (0x80b20 : word) = Some W_80ad8.
Proof. vm_refl. Qed.
Lemma D_80ad8 : decode_any W_80ad8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80adc : bv 32 := 0x00c6f6b3.
Lemma F_80adc : fetch_word AsanUbsan.M.loaded_segments (0x80b24 : word) = Some W_80adc.
Proof. vm_refl. Qed.
Lemma D_80adc : decode_any W_80adc = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ae0 : bv 32 := 0x04a6f263.
Lemma F_80ae0 : fetch_word AsanUbsan.M.loaded_segments (0x80b28 : word) = Some W_80ae0.
Proof. vm_refl. Qed.
Lemma D_80ae0 : decode_any W_80ae0 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ae4 : bv 32 := 0x000d4697.
Lemma F_80ae4 : fetch_word AsanUbsan.M.loaded_segments (0x80b2c : word) = Some W_80ae4.
Proof. vm_refl. Qed.
Lemma D_80ae4 : decode_any W_80ae4 = Some (Auipc 13 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ae8 : bv 32 := 0x9dc6b683.
Lemma F_80ae8 : fetch_word AsanUbsan.M.loaded_segments (0x80b30 : word) = Some W_80ae8.
Proof. vm_refl. Qed.
Lemma D_80ae8 : decode_any W_80ae8 = Some (Load SZ8 true 13 13 2524, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aec : bv 32 := 0x000d4717.
Lemma F_80aec : fetch_word AsanUbsan.M.loaded_segments (0x80b34 : word) = Some W_80aec.
Proof. vm_refl. Qed.
Lemma D_80aec : decode_any W_80aec = Some (Auipc 14 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af0 : bv 32 := 0x9dc73703.
Lemma F_80af0 : fetch_word AsanUbsan.M.loaded_segments (0x80b38 : word) = Some W_80af0.
Proof. vm_refl. Qed.
Lemma D_80af0 : decode_any W_80af0 = Some (Load SZ8 true 14 14 2524, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af4 : bv 32 := 0x0006b803.
Lemma F_80af4 : fetch_word AsanUbsan.M.loaded_segments (0x80b3c : word) = Some W_80af4.
Proof. vm_refl. Qed.
Lemma D_80af4 : decode_any W_80af4 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af8 : bv 32 := 0x00073683.
Lemma F_80af8 : fetch_word AsanUbsan.M.loaded_segments (0x80b40 : word) = Some W_80af8.
Proof. vm_refl. Qed.
Lemma D_80af8 : decode_any W_80af8 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80afc : bv 32 := 0xfff80793.
Lemma F_80afc : fetch_word AsanUbsan.M.loaded_segments (0x80b44 : word) = Some W_80afc.
Proof. vm_refl. Qed.
Lemma D_80afc : decode_any W_80afc = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b00 : bv 32 := 0x00a7f463.
Lemma F_80b00 : fetch_word AsanUbsan.M.loaded_segments (0x80b48 : word) = Some W_80b00.
Proof. vm_refl. Qed.
Lemma D_80b00 : decode_any W_80b00 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b08 : bv 32 := 0x000d4717.
Lemma F_80b08 : fetch_word AsanUbsan.M.loaded_segments (0x80b50 : word) = Some W_80b08.
Proof. vm_refl. Qed.
Lemma D_80b08 : decode_any W_80b08 = Some (Auipc 14 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b0c : bv 32 := 0x9c873703.
Lemma F_80b0c : fetch_word AsanUbsan.M.loaded_segments (0x80b54 : word) = Some W_80b0c.
Proof. vm_refl. Qed.
Lemma D_80b0c : decode_any W_80b0c = Some (Load SZ8 true 14 14 2504, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b10 : bv 32 := 0x00073283.
Lemma F_80b10 : fetch_word AsanUbsan.M.loaded_segments (0x80b58 : word) = Some W_80b10.
Proof. vm_refl. Qed.
Lemma D_80b10 : decode_any W_80b10 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b14 : bv 32 := 0x0032d713.
Lemma F_80b14 : fetch_word AsanUbsan.M.loaded_segments (0x80b5c : word) = Some W_80b14.
Proof. vm_refl. Qed.
Lemma D_80b14 : decode_any W_80b14 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b18 : bv 32 := 0x00b708b3.
Lemma F_80b18 : fetch_word AsanUbsan.M.loaded_segments (0x80b60 : word) = Some W_80b18.
Proof. vm_refl. Qed.
Lemma D_80b18 : decode_any W_80b18 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b1c : bv 32 := 0x00a2ea63.
Lemma F_80b1c : fetch_word AsanUbsan.M.loaded_segments (0x80b64 : word) = Some W_80b1c.
Proof. vm_refl. Qed.
Lemma D_80b1c : decode_any W_80b1c = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b20 : bv 32 := 0x00a8f863.
Lemma F_80b20 : fetch_word AsanUbsan.M.loaded_segments (0x80b68 : word) = Some W_80b20.
Proof. vm_refl. Qed.
Lemma D_80b20 : decode_any W_80b20 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b24 : bv 32 := 0x00355513.
Lemma F_80b24 : fetch_word AsanUbsan.M.loaded_segments (0x80b6c : word) = Some W_80b24.
Proof. vm_refl. Qed.
Lemma D_80b24 : decode_any W_80b24 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b28 : bv 32 := 0x00a58533.
Lemma F_80b28 : fetch_word AsanUbsan.M.loaded_segments (0x80b70 : word) = Some W_80b28.
Proof. vm_refl. Qed.
Lemma D_80b28 : decode_any W_80b28 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b2c : bv 32 := 0x00008067.
Lemma F_80b2c : fetch_word AsanUbsan.M.loaded_segments (0x80b74 : word) = Some W_80b2c.
Proof. vm_refl. Qed.
Lemma D_80b2c : decode_any W_80b2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d6c : bv 32 := 0x0100006f.
Lemma F_80d6c : fetch_word AsanUbsan.M.loaded_segments (0x80db4 : word) = Some W_80d6c.
Proof. vm_refl. Qed.
Lemma D_80d6c : decode_any W_80d6c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d70 : bv 32 := 0x1dc0006f.
Lemma F_80d70 : fetch_word AsanUbsan.M.loaded_segments (0x80db8 : word) = Some W_80d70.
Proof. vm_refl. Qed.
Lemma D_80d70 : decode_any W_80d70 = Some (Jal 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d78 : bv 32 := 0x7400006f.
Lemma F_80d78 : fetch_word AsanUbsan.M.loaded_segments (0x80dc0 : word) = Some W_80d78.
Proof. vm_refl. Qed.
Lemma D_80d78 : decode_any W_80d78 = Some (Jal 0 1856, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d7c : bv 32 := 0x81010113.
Lemma F_80d7c : fetch_word AsanUbsan.M.loaded_segments (0x80dc4 : word) = Some W_80d7c.
Proof. vm_refl. Qed.
Lemma D_80d7c : decode_any W_80d7c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d80 : bv 32 := 0x7e113423.
Lemma F_80d80 : fetch_word AsanUbsan.M.loaded_segments (0x80dc8 : word) = Some W_80d80.
Proof. vm_refl. Qed.
Lemma D_80d80 : decode_any W_80d80 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d84 : bv 32 := 0x7e813023.
Lemma F_80d84 : fetch_word AsanUbsan.M.loaded_segments (0x80dcc : word) = Some W_80d84.
Proof. vm_refl. Qed.
Lemma D_80d84 : decode_any W_80d84 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d88 : bv 32 := 0x7c913c23.
Lemma F_80d88 : fetch_word AsanUbsan.M.loaded_segments (0x80dd0 : word) = Some W_80d88.
Proof. vm_refl. Qed.
Lemma D_80d88 : decode_any W_80d88 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d8c : bv 32 := 0x7d213823.
Lemma F_80d8c : fetch_word AsanUbsan.M.loaded_segments (0x80dd4 : word) = Some W_80d8c.
Proof. vm_refl. Qed.
Lemma D_80d8c : decode_any W_80d8c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d90 : bv 32 := 0x7d313423.
Lemma F_80d90 : fetch_word AsanUbsan.M.loaded_segments (0x80dd8 : word) = Some W_80d90.
Proof. vm_refl. Qed.
Lemma D_80d90 : decode_any W_80d90 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d94 : bv 32 := 0x7d413023.
Lemma F_80d94 : fetch_word AsanUbsan.M.loaded_segments (0x80ddc : word) = Some W_80d94.
Proof. vm_refl. Qed.
Lemma D_80d94 : decode_any W_80d94 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d98 : bv 32 := 0x7b513c23.
Lemma F_80d98 : fetch_word AsanUbsan.M.loaded_segments (0x80de0 : word) = Some W_80d98.
Proof. vm_refl. Qed.
Lemma D_80d98 : decode_any W_80d98 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d9c : bv 32 := 0x7f010413.
Lemma F_80d9c : fetch_word AsanUbsan.M.loaded_segments (0x80de4 : word) = Some W_80d9c.
Proof. vm_refl. Qed.
Lemma D_80d9c : decode_any W_80d9c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80da0 : bv 32 := 0xfa010113.
Lemma F_80da0 : fetch_word AsanUbsan.M.loaded_segments (0x80de8 : word) = Some W_80da0.
Proof. vm_refl. Qed.
Lemma D_80da0 : decode_any W_80da0 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80da4 : bv 32 := 0x00008913.
Lemma F_80da4 : fetch_word AsanUbsan.M.loaded_segments (0x80dec : word) = Some W_80da4.
Proof. vm_refl. Qed.
Lemma D_80da4 : decode_any W_80da4 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80da8 : bv 32 := 0x00050493.
Lemma F_80da8 : fetch_word AsanUbsan.M.loaded_segments (0x80df0 : word) = Some W_80da8.
Proof. vm_refl. Qed.
Lemma D_80da8 : decode_any W_80da8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dac : bv 32 := 0x10c0c0ef.
Lemma F_80dac : fetch_word AsanUbsan.M.loaded_segments (0x80df4 : word) = Some W_80dac.
Proof. vm_refl. Qed.
Lemma D_80dac : decode_any W_80dac = Some (Jal 1 49420, 4%Z).
Proof. vm_refl. Qed.

Definition W_80db0 : bv 32 := 0x02f4d593.
Lemma F_80db0 : fetch_word AsanUbsan.M.loaded_segments (0x80df8 : word) = Some W_80db0.
Proof. vm_refl. Qed.
Lemma D_80db0 : decode_any W_80db0 = Some (ShiftImm ALU_SRL 11 9 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_80db4 : bv 32 := 0x0a059063.
Lemma F_80db4 : fetch_word AsanUbsan.M.loaded_segments (0x80dfc : word) = Some W_80db4.
Proof. vm_refl. Qed.
Lemma D_80db4 : decode_any W_80db4 = Some (Branch BC_NE 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_80db8 : bv 32 := 0x0204d593.
Lemma F_80db8 : fetch_word AsanUbsan.M.loaded_segments (0x80e00 : word) = Some W_80db8.
Proof. vm_refl. Qed.
Lemma D_80db8 : decode_any W_80db8 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dbc : bv 32 := 0x00359613.
Lemma F_80dbc : fetch_word AsanUbsan.M.loaded_segments (0x80e04 : word) = Some W_80dbc.
Proof. vm_refl. Qed.
Lemma D_80dbc : decode_any W_80dbc = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dc0 : bv 32 := 0x00c50633.
Lemma F_80dc0 : fetch_word AsanUbsan.M.loaded_segments (0x80e08 : word) = Some W_80dc0.
Proof. vm_refl. Qed.
Lemma D_80dc0 : decode_any W_80dc0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dc4 : bv 32 := 0x00863683.
Lemma F_80dc4 : fetch_word AsanUbsan.M.loaded_segments (0x80e0c : word) = Some W_80dc4.
Proof. vm_refl. Qed.
Lemma D_80dc4 : decode_any W_80dc4 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dc8 : bv 32 := 0x0230000f.
Lemma F_80dc8 : fetch_word AsanUbsan.M.loaded_segments (0x80e10 : word) = Some W_80dc8.
Proof. vm_refl. Qed.
Lemma D_80dc8 : decode_any W_80dc8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dcc : bv 32 := 0x08068463.
Lemma F_80dcc : fetch_word AsanUbsan.M.loaded_segments (0x80e14 : word) = Some W_80dcc.
Proof. vm_refl. Qed.
Lemma D_80dcc : decode_any W_80dcc = Some (Branch BC_EQ 13 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e54 : bv 32 := 0x80040a13.
Lemma F_80e54 : fetch_word AsanUbsan.M.loaded_segments (0x80e9c : word) = Some W_80e54.
Proof. vm_refl. Qed.
Lemma D_80e54 : decode_any W_80e54 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e58 : bv 32 := 0xfb0a0a13.
Lemma F_80e58 : fetch_word AsanUbsan.M.loaded_segments (0x80ea0 : word) = Some W_80e58.
Proof. vm_refl. Qed.
Lemma D_80e58 : decode_any W_80e58 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e5c : bv 32 := 0x80040513.
Lemma F_80e5c : fetch_word AsanUbsan.M.loaded_segments (0x80ea4 : word) = Some W_80e5c.
Proof. vm_refl. Qed.
Lemma D_80e5c : decode_any W_80e5c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e60 : bv 32 := 0xfc050513.
Lemma F_80e60 : fetch_word AsanUbsan.M.loaded_segments (0x80ea8 : word) = Some W_80e60.
Proof. vm_refl. Qed.
Lemma D_80e60 : decode_any W_80e60 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e64 : bv 32 := 0x7ffa0a93.
Lemma F_80e64 : fetch_word AsanUbsan.M.loaded_segments (0x80eac : word) = Some W_80e64.
Proof. vm_refl. Qed.
Lemma D_80e64 : decode_any W_80e64 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e68 : bv 32 := 0x000ab4a3.
Lemma F_80e68 : fetch_word AsanUbsan.M.loaded_segments (0x80eb0 : word) = Some W_80e68.
Proof. vm_refl. Qed.
Lemma D_80e68 : decode_any W_80e68 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e6c : bv 32 := 0x00aa3023.
Lemma F_80e6c : fetch_word AsanUbsan.M.loaded_segments (0x80eb4 : word) = Some W_80e6c.
Proof. vm_refl. Qed.
Lemma D_80e6c : decode_any W_80e6c = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e70 : bv 32 := 0x000a3423.
Lemma F_80e70 : fetch_word AsanUbsan.M.loaded_segments (0x80eb8 : word) = Some W_80e70.
Proof. vm_refl. Qed.
Lemma D_80e70 : decode_any W_80e70 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e74 : bv 32 := 0x550080ef.
Lemma F_80e74 : fetch_word AsanUbsan.M.loaded_segments (0x80ebc : word) = Some W_80e74.
Proof. vm_refl. Qed.
Lemma D_80e74 : decode_any W_80e74 = Some (Jal 1 34128, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e78 : bv 32 := 0x00200593.
Lemma F_80e78 : fetch_word AsanUbsan.M.loaded_segments (0x80ec0 : word) = Some W_80e78.
Proof. vm_refl. Qed.
Lemma D_80e78 : decode_any W_80e78 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e7c : bv 32 := 0x02a5ea63.
Lemma F_80e7c : fetch_word AsanUbsan.M.loaded_segments (0x80ec4 : word) = Some W_80e7c.
Proof. vm_refl. Qed.
Lemma D_80e7c : decode_any W_80e7c = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eb0 : bv 32 := 0x7f1200ef.
Lemma F_80eb0 : fetch_word AsanUbsan.M.loaded_segments (0x80ef8 : word) = Some W_80eb0.
Proof. vm_refl. Qed.
Lemma D_80eb0 : decode_any W_80eb0 = Some (Jal 1 135152, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eb4 : bv 32 := 0x000d3597.
Lemma F_80eb4 : fetch_word AsanUbsan.M.loaded_segments (0x80efc : word) = Some W_80eb4.
Proof. vm_refl. Qed.
Lemma D_80eb4 : decode_any W_80eb4 = Some (Auipc 11 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eb8 : bv 32 := 0x5f45b583.
Lemma F_80eb8 : fetch_word AsanUbsan.M.loaded_segments (0x80f00 : word) = Some W_80eb8.
Proof. vm_refl. Qed.
Lemma D_80eb8 : decode_any W_80eb8 = Some (Load SZ8 true 11 11 1524, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ebc : bv 32 := 0x0225c983.
Lemma F_80ebc : fetch_word AsanUbsan.M.loaded_segments (0x80f04 : word) = Some W_80ebc.
Proof. vm_refl. Qed.
Lemma D_80ebc : decode_any W_80ebc = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ec0 : bv 32 := 0x00050913.
Lemma F_80ec0 : fetch_word AsanUbsan.M.loaded_segments (0x80f08 : word) = Some W_80ec0.
Proof. vm_refl. Qed.
Lemma D_80ec0 : decode_any W_80ec0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ec4 : bv 32 := 0x500080ef.
Lemma F_80ec4 : fetch_word AsanUbsan.M.loaded_segments (0x80f0c : word) = Some W_80ec4.
Proof. vm_refl. Qed.
Lemma D_80ec4 : decode_any W_80ec4 = Some (Jal 1 34048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ec8 : bv 32 := 0x00050793.
Lemma F_80ec8 : fetch_word AsanUbsan.M.loaded_segments (0x80f10 : word) = Some W_80ec8.
Proof. vm_refl. Qed.
Lemma D_80ec8 : decode_any W_80ec8 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ecc : bv 32 := 0x00153513.
Lemma F_80ecc : fetch_word AsanUbsan.M.loaded_segments (0x80f14 : word) = Some W_80ecc.
Proof. vm_refl. Qed.
Lemma D_80ecc : decode_any W_80ecc = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed0 : bv 32 := 0xfff50513.
Lemma F_80ed0 : fetch_word AsanUbsan.M.loaded_segments (0x80f18 : word) = Some W_80ed0.
Proof. vm_refl. Qed.
Lemma D_80ed0 : decode_any W_80ed0 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed4 : bv 32 := 0x008575b3.
Lemma F_80ed4 : fetch_word AsanUbsan.M.loaded_segments (0x80f1c : word) = Some W_80ed4.
Proof. vm_refl. Qed.
Lemma D_80ed4 : decode_any W_80ed4 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed8 : bv 32 := 0x00100513.
Lemma F_80ed8 : fetch_word AsanUbsan.M.loaded_segments (0x80f20 : word) = Some W_80ed8.
Proof. vm_refl. Qed.
Lemma D_80ed8 : decode_any W_80ed8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80edc : bv 32 := 0x00bab4a3.
Lemma F_80edc : fetch_word AsanUbsan.M.loaded_segments (0x80f24 : word) = Some W_80edc.
Proof. vm_refl. Qed.
Lemma D_80edc : decode_any W_80edc = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ee0 : bv 32 := 0x00f56a63.
Lemma F_80ee0 : fetch_word AsanUbsan.M.loaded_segments (0x80f28 : word) = Some W_80ee0.
Proof. vm_refl. Qed.
Lemma D_80ee0 : decode_any W_80ee0 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ef4 : bv 32 := 0x80040513.
Lemma F_80ef4 : fetch_word AsanUbsan.M.loaded_segments (0x80f3c : word) = Some W_80ef4.
Proof. vm_refl. Qed.
Lemma D_80ef4 : decode_any W_80ef4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ef8 : bv 32 := 0xfb050513.
Lemma F_80ef8 : fetch_word AsanUbsan.M.loaded_segments (0x80f40 : word) = Some W_80ef8.
Proof. vm_refl. Qed.
Lemma D_80ef8 : decode_any W_80ef8 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80efc : bv 32 := 0x00090593.
Lemma F_80efc : fetch_word AsanUbsan.M.loaded_segments (0x80f44 : word) = Some W_80efc.
Proof. vm_refl. Qed.
Lemma D_80efc : decode_any W_80efc = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f00 : bv 32 := 0x00040613.
Lemma F_80f00 : fetch_word AsanUbsan.M.loaded_segments (0x80f48 : word) = Some W_80f00.
Proof. vm_refl. Qed.
Lemma D_80f00 : decode_any W_80f00 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f04 : bv 32 := 0x00000693.
Lemma F_80f04 : fetch_word AsanUbsan.M.loaded_segments (0x80f4c : word) = Some W_80f04.
Proof. vm_refl. Qed.
Lemma D_80f04 : decode_any W_80f04 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f08 : bv 32 := 0x00098713.
Lemma F_80f08 : fetch_word AsanUbsan.M.loaded_segments (0x80f50 : word) = Some W_80f08.
Proof. vm_refl. Qed.
Lemma D_80f08 : decode_any W_80f08 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f0c : bv 32 := 0x4c8080ef.
Lemma F_80f0c : fetch_word AsanUbsan.M.loaded_segments (0x80f54 : word) = Some W_80f0c.
Proof. vm_refl. Qed.
Lemma D_80f0c : decode_any W_80f0c = Some (Jal 1 33992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f10 : bv 32 := 0x80040593.
Lemma F_80f10 : fetch_word AsanUbsan.M.loaded_segments (0x80f58 : word) = Some W_80f10.
Proof. vm_refl. Qed.
Lemma D_80f10 : decode_any W_80f10 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f14 : bv 32 := 0xfb058593.
Lemma F_80f14 : fetch_word AsanUbsan.M.loaded_segments (0x80f5c : word) = Some W_80f14.
Proof. vm_refl. Qed.
Lemma D_80f14 : decode_any W_80f14 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f18 : bv 32 := 0x00100613.
Lemma F_80f18 : fetch_word AsanUbsan.M.loaded_segments (0x80f60 : word) = Some W_80f18.
Proof. vm_refl. Qed.
Lemma D_80f18 : decode_any W_80f18 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f1c : bv 32 := 0x00048513.
Lemma F_80f1c : fetch_word AsanUbsan.M.loaded_segments (0x80f64 : word) = Some W_80f1c.
Proof. vm_refl. Qed.
Lemma D_80f1c : decode_any W_80f1c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f20 : bv 32 := 0xd78d80ef.
Lemma F_80f20 : fetch_word AsanUbsan.M.loaded_segments (0x80f68 : word) = Some W_80f20.
Proof. vm_refl. Qed.
Lemma D_80f20 : decode_any W_80f20 = Some (Jal 1 1934712, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f24 : bv 32 := 0x06010113.
Lemma F_80f24 : fetch_word AsanUbsan.M.loaded_segments (0x80f6c : word) = Some W_80f24.
Proof. vm_refl. Qed.
Lemma D_80f24 : decode_any W_80f24 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f28 : bv 32 := 0x7e813083.
Lemma F_80f28 : fetch_word AsanUbsan.M.loaded_segments (0x80f70 : word) = Some W_80f28.
Proof. vm_refl. Qed.
Lemma D_80f28 : decode_any W_80f28 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f2c : bv 32 := 0x7e013403.
Lemma F_80f2c : fetch_word AsanUbsan.M.loaded_segments (0x80f74 : word) = Some W_80f2c.
Proof. vm_refl. Qed.
Lemma D_80f2c : decode_any W_80f2c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f30 : bv 32 := 0x7d813483.
Lemma F_80f30 : fetch_word AsanUbsan.M.loaded_segments (0x80f78 : word) = Some W_80f30.
Proof. vm_refl. Qed.
Lemma D_80f30 : decode_any W_80f30 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f34 : bv 32 := 0x7d013903.
Lemma F_80f34 : fetch_word AsanUbsan.M.loaded_segments (0x80f7c : word) = Some W_80f34.
Proof. vm_refl. Qed.
Lemma D_80f34 : decode_any W_80f34 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f38 : bv 32 := 0x7c813983.
Lemma F_80f38 : fetch_word AsanUbsan.M.loaded_segments (0x80f80 : word) = Some W_80f38.
Proof. vm_refl. Qed.
Lemma D_80f38 : decode_any W_80f38 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f3c : bv 32 := 0x7c013a03.
Lemma F_80f3c : fetch_word AsanUbsan.M.loaded_segments (0x80f84 : word) = Some W_80f3c.
Proof. vm_refl. Qed.
Lemma D_80f3c : decode_any W_80f3c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f40 : bv 32 := 0x7b813a83.
Lemma F_80f40 : fetch_word AsanUbsan.M.loaded_segments (0x80f88 : word) = Some W_80f40.
Proof. vm_refl. Qed.
Lemma D_80f40 : decode_any W_80f40 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f44 : bv 32 := 0x7f010113.
Lemma F_80f44 : fetch_word AsanUbsan.M.loaded_segments (0x80f8c : word) = Some W_80f44.
Proof. vm_refl. Qed.
Lemma D_80f44 : decode_any W_80f44 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f48 : bv 32 := 0x00008067.
Lemma F_80f48 : fetch_word AsanUbsan.M.loaded_segments (0x80f90 : word) = Some W_80f48.
Proof. vm_refl. Qed.
Lemma D_80f48 : decode_any W_80f48 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f4c : bv 32 := 0x81010113.
Lemma F_80f4c : fetch_word AsanUbsan.M.loaded_segments (0x80f94 : word) = Some W_80f4c.
Proof. vm_refl. Qed.
Lemma D_80f4c : decode_any W_80f4c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f50 : bv 32 := 0x7e113423.
Lemma F_80f50 : fetch_word AsanUbsan.M.loaded_segments (0x80f98 : word) = Some W_80f50.
Proof. vm_refl. Qed.
Lemma D_80f50 : decode_any W_80f50 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f54 : bv 32 := 0x7e813023.
Lemma F_80f54 : fetch_word AsanUbsan.M.loaded_segments (0x80f9c : word) = Some W_80f54.
Proof. vm_refl. Qed.
Lemma D_80f54 : decode_any W_80f54 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f58 : bv 32 := 0x7c913c23.
Lemma F_80f58 : fetch_word AsanUbsan.M.loaded_segments (0x80fa0 : word) = Some W_80f58.
Proof. vm_refl. Qed.
Lemma D_80f58 : decode_any W_80f58 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f5c : bv 32 := 0x7d213823.
Lemma F_80f5c : fetch_word AsanUbsan.M.loaded_segments (0x80fa4 : word) = Some W_80f5c.
Proof. vm_refl. Qed.
Lemma D_80f5c : decode_any W_80f5c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f60 : bv 32 := 0x7d313423.
Lemma F_80f60 : fetch_word AsanUbsan.M.loaded_segments (0x80fa8 : word) = Some W_80f60.
Proof. vm_refl. Qed.
Lemma D_80f60 : decode_any W_80f60 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f64 : bv 32 := 0x7d413023.
Lemma F_80f64 : fetch_word AsanUbsan.M.loaded_segments (0x80fac : word) = Some W_80f64.
Proof. vm_refl. Qed.
Lemma D_80f64 : decode_any W_80f64 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f68 : bv 32 := 0x7b513c23.
Lemma F_80f68 : fetch_word AsanUbsan.M.loaded_segments (0x80fb0 : word) = Some W_80f68.
Proof. vm_refl. Qed.
Lemma D_80f68 : decode_any W_80f68 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f6c : bv 32 := 0x7f010413.
Lemma F_80f6c : fetch_word AsanUbsan.M.loaded_segments (0x80fb4 : word) = Some W_80f6c.
Proof. vm_refl. Qed.
Lemma D_80f6c : decode_any W_80f6c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f70 : bv 32 := 0xfa010113.
Lemma F_80f70 : fetch_word AsanUbsan.M.loaded_segments (0x80fb8 : word) = Some W_80f70.
Proof. vm_refl. Qed.
Lemma D_80f70 : decode_any W_80f70 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f74 : bv 32 := 0x00008913.
Lemma F_80f74 : fetch_word AsanUbsan.M.loaded_segments (0x80fbc : word) = Some W_80f74.
Proof. vm_refl. Qed.
Lemma D_80f74 : decode_any W_80f74 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f78 : bv 32 := 0x00050493.
Lemma F_80f78 : fetch_word AsanUbsan.M.loaded_segments (0x80fc0 : word) = Some W_80f78.
Proof. vm_refl. Qed.
Lemma D_80f78 : decode_any W_80f78 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f7c : bv 32 := 0x6c0070ef.
Lemma F_80f7c : fetch_word AsanUbsan.M.loaded_segments (0x80fc4 : word) = Some W_80f7c.
Proof. vm_refl. Qed.
Lemma D_80f7c : decode_any W_80f7c = Some (Jal 1 30400, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f80 : bv 32 := 0x06050063.
Lemma F_80f80 : fetch_word AsanUbsan.M.loaded_segments (0x80fc8 : word) = Some W_80f80.
Proof. vm_refl. Qed.
Lemma D_80f80 : decode_any W_80f80 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f84 : bv 32 := 0x80040a13.
Lemma F_80f84 : fetch_word AsanUbsan.M.loaded_segments (0x80fcc : word) = Some W_80f84.
Proof. vm_refl. Qed.
Lemma D_80f84 : decode_any W_80f84 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f88 : bv 32 := 0xfb0a0a13.
Lemma F_80f88 : fetch_word AsanUbsan.M.loaded_segments (0x80fd0 : word) = Some W_80f88.
Proof. vm_refl. Qed.
Lemma D_80f88 : decode_any W_80f88 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f8c : bv 32 := 0x80040513.
Lemma F_80f8c : fetch_word AsanUbsan.M.loaded_segments (0x80fd4 : word) = Some W_80f8c.
Proof. vm_refl. Qed.
Lemma D_80f8c : decode_any W_80f8c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f90 : bv 32 := 0xfc050513.
Lemma F_80f90 : fetch_word AsanUbsan.M.loaded_segments (0x80fd8 : word) = Some W_80f90.
Proof. vm_refl. Qed.
Lemma D_80f90 : decode_any W_80f90 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f94 : bv 32 := 0x7ffa0a93.
Lemma F_80f94 : fetch_word AsanUbsan.M.loaded_segments (0x80fdc : word) = Some W_80f94.
Proof. vm_refl. Qed.
Lemma D_80f94 : decode_any W_80f94 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f98 : bv 32 := 0x000ab4a3.
Lemma F_80f98 : fetch_word AsanUbsan.M.loaded_segments (0x80fe0 : word) = Some W_80f98.
Proof. vm_refl. Qed.
Lemma D_80f98 : decode_any W_80f98 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f9c : bv 32 := 0x00aa3023.
Lemma F_80f9c : fetch_word AsanUbsan.M.loaded_segments (0x80fe4 : word) = Some W_80f9c.
Proof. vm_refl. Qed.
Lemma D_80f9c : decode_any W_80f9c = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fa0 : bv 32 := 0x000a3423.
Lemma F_80fa0 : fetch_word AsanUbsan.M.loaded_segments (0x80fe8 : word) = Some W_80fa0.
Proof. vm_refl. Qed.
Lemma D_80fa0 : decode_any W_80fa0 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fa4 : bv 32 := 0x420080ef.
Lemma F_80fa4 : fetch_word AsanUbsan.M.loaded_segments (0x80fec : word) = Some W_80fa4.
Proof. vm_refl. Qed.
Lemma D_80fa4 : decode_any W_80fa4 = Some (Jal 1 33824, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fa8 : bv 32 := 0x00200593.
Lemma F_80fa8 : fetch_word AsanUbsan.M.loaded_segments (0x80ff0 : word) = Some W_80fa8.
Proof. vm_refl. Qed.
Lemma D_80fa8 : decode_any W_80fa8 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fac : bv 32 := 0x06a5e263.
Lemma F_80fac : fetch_word AsanUbsan.M.loaded_segments (0x80ff4 : word) = Some W_80fac.
Proof. vm_refl. Qed.
Lemma D_80fac : decode_any W_80fac = Some (Branch BC_LTU 11 10 100, 4%Z).
Proof. vm_refl. Qed.

