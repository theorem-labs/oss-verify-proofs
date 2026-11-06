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

Definition W_67fdc : bv 32 := 0x0310000f.
Lemma F_67fdc : fetch_word AsanUbsan.M.loaded_segments (0x67fdc : word) = Some W_67fdc.
Proof. vm_refl. Qed.
Lemma D_67fdc : decode_any W_67fdc = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67fe0 : bv 32 := 0x00077597.
Lemma F_67fe0 : fetch_word AsanUbsan.M.loaded_segments (0x67fe0 : word) = Some W_67fe0.
Proof. vm_refl. Qed.
Lemma D_67fe0 : decode_any W_67fe0 = Some (Auipc 11 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_67fe4 : bv 32 := 0x44a5ae23.
Lemma F_67fe4 : fetch_word AsanUbsan.M.loaded_segments (0x67fe4 : word) = Some W_67fe4.
Proof. vm_refl. Qed.
Lemma D_67fe4 : decode_any W_67fe4 = Some (Store SZ4 11 10 1116, 4%Z).
Proof. vm_refl. Qed.

Definition W_67fe8 : bv 32 := 0x00008067.
Lemma F_67fe8 : fetch_word AsanUbsan.M.loaded_segments (0x67fe8 : word) = Some W_67fe8.
Proof. vm_refl. Qed.
Lemma D_67fe8 : decode_any W_67fe8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67fec : bv 32 := 0x00077517.
Lemma F_67fec : fetch_word AsanUbsan.M.loaded_segments (0x67fec : word) = Some W_67fec.
Proof. vm_refl. Qed.
Lemma D_67fec : decode_any W_67fec = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ff0 : bv 32 := 0x45052503.
Lemma F_67ff0 : fetch_word AsanUbsan.M.loaded_segments (0x67ff0 : word) = Some W_67ff0.
Proof. vm_refl. Qed.
Lemma D_67ff0 : decode_any W_67ff0 = Some (Load SZ4 true 10 10 1104, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ff4 : bv 32 := 0x0230000f.
Lemma F_67ff4 : fetch_word AsanUbsan.M.loaded_segments (0x67ff4 : word) = Some W_67ff4.
Proof. vm_refl. Qed.
Lemma D_67ff4 : decode_any W_67ff4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ff8 : bv 32 := 0x00008067.
Lemma F_67ff8 : fetch_word AsanUbsan.M.loaded_segments (0x67ff8 : word) = Some W_67ff8.
Proof. vm_refl. Qed.
Lemma D_67ff8 : decode_any W_67ff8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ffc : bv 32 := 0xfb010113.
Lemma F_67ffc : fetch_word AsanUbsan.M.loaded_segments (0x67ffc : word) = Some W_67ffc.
Proof. vm_refl. Qed.
Lemma D_67ffc : decode_any W_67ffc = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_68000 : bv 32 := 0x04113423.
Lemma F_68000 : fetch_word AsanUbsan.M.loaded_segments (0x68000 : word) = Some W_68000.
Proof. vm_refl. Qed.
Lemma D_68000 : decode_any W_68000 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_68004 : bv 32 := 0x04813023.
Lemma F_68004 : fetch_word AsanUbsan.M.loaded_segments (0x68004 : word) = Some W_68004.
Proof. vm_refl. Qed.
Lemma D_68004 : decode_any W_68004 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_68008 : bv 32 := 0x02913c23.
Lemma F_68008 : fetch_word AsanUbsan.M.loaded_segments (0x68008 : word) = Some W_68008.
Proof. vm_refl. Qed.
Lemma D_68008 : decode_any W_68008 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6800c : bv 32 := 0x03213823.
Lemma F_6800c : fetch_word AsanUbsan.M.loaded_segments (0x6800c : word) = Some W_6800c.
Proof. vm_refl. Qed.
Lemma D_6800c : decode_any W_6800c = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_68010 : bv 32 := 0x03313423.
Lemma F_68010 : fetch_word AsanUbsan.M.loaded_segments (0x68010 : word) = Some W_68010.
Proof. vm_refl. Qed.
Lemma D_68010 : decode_any W_68010 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_68014 : bv 32 := 0x03413023.
Lemma F_68014 : fetch_word AsanUbsan.M.loaded_segments (0x68014 : word) = Some W_68014.
Proof. vm_refl. Qed.
Lemma D_68014 : decode_any W_68014 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_68018 : bv 32 := 0x01513c23.
Lemma F_68018 : fetch_word AsanUbsan.M.loaded_segments (0x68018 : word) = Some W_68018.
Proof. vm_refl. Qed.
Lemma D_68018 : decode_any W_68018 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6801c : bv 32 := 0x01613823.
Lemma F_6801c : fetch_word AsanUbsan.M.loaded_segments (0x6801c : word) = Some W_6801c.
Proof. vm_refl. Qed.
Lemma D_6801c : decode_any W_6801c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_68020 : bv 32 := 0x01713423.
Lemma F_68020 : fetch_word AsanUbsan.M.loaded_segments (0x68020 : word) = Some W_68020.
Proof. vm_refl. Qed.
Lemma D_68020 : decode_any W_68020 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_68024 : bv 32 := 0x01813023.
Lemma F_68024 : fetch_word AsanUbsan.M.loaded_segments (0x68024 : word) = Some W_68024.
Proof. vm_refl. Qed.
Lemma D_68024 : decode_any W_68024 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68028 : bv 32 := 0x00078493.
Lemma F_68028 : fetch_word AsanUbsan.M.loaded_segments (0x68028 : word) = Some W_68028.
Proof. vm_refl. Qed.
Lemma D_68028 : decode_any W_68028 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6802c : bv 32 := 0x00070a93.
Lemma F_6802c : fetch_word AsanUbsan.M.loaded_segments (0x6802c : word) = Some W_6802c.
Proof. vm_refl. Qed.
Lemma D_6802c : decode_any W_6802c = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68030 : bv 32 := 0x00068a13.
Lemma F_68030 : fetch_word AsanUbsan.M.loaded_segments (0x68030 : word) = Some W_68030.
Proof. vm_refl. Qed.
Lemma D_68030 : decode_any W_68030 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68034 : bv 32 := 0x00060413.
Lemma F_68034 : fetch_word AsanUbsan.M.loaded_segments (0x68034 : word) = Some W_68034.
Proof. vm_refl. Qed.
Lemma D_68034 : decode_any W_68034 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68038 : bv 32 := 0x00058913.
Lemma F_68038 : fetch_word AsanUbsan.M.loaded_segments (0x68038 : word) = Some W_68038.
Proof. vm_refl. Qed.
Lemma D_68038 : decode_any W_68038 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6803c : bv 32 := 0x00050993.
Lemma F_6803c : fetch_word AsanUbsan.M.loaded_segments (0x6803c : word) = Some W_6803c.
Proof. vm_refl. Qed.
Lemma D_6803c : decode_any W_6803c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68040 : bv 32 := 0x00052423.
Lemma F_68040 : fetch_word AsanUbsan.M.loaded_segments (0x68040 : word) = Some W_68040.
Proof. vm_refl. Qed.
Lemma D_68040 : decode_any W_68040 = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_68044 : bv 32 := 0xb10fe0ef.
Lemma F_68044 : fetch_word AsanUbsan.M.loaded_segments (0x68044 : word) = Some W_68044.
Proof. vm_refl. Qed.
Lemma D_68044 : decode_any W_68044 = Some (Jal 1 2089744, 4%Z).
Proof. vm_refl. Qed.

Definition W_68048 : bv 32 := 0x0c050a63.
Lemma F_68048 : fetch_word AsanUbsan.M.loaded_segments (0x68048 : word) = Some W_68048.
Proof. vm_refl. Qed.
Lemma D_68048 : decode_any W_68048 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_6804c : bv 32 := 0x219010ef.
Lemma F_6804c : fetch_word AsanUbsan.M.loaded_segments (0x6804c : word) = Some W_6804c.
Proof. vm_refl. Qed.
Lemma D_6804c : decode_any W_6804c = Some (Jal 1 6680, 4%Z).
Proof. vm_refl. Qed.

Definition W_68050 : bv 32 := 0x04050a63.
Lemma F_68050 : fetch_word AsanUbsan.M.loaded_segments (0x68050 : word) = Some W_68050.
Proof. vm_refl. Qed.
Lemma D_68050 : decode_any W_68050 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_68054 : bv 32 := 0x7ff50c13.
Lemma F_68054 : fetch_word AsanUbsan.M.loaded_segments (0x68054 : word) = Some W_68054.
Proof. vm_refl. Qed.
Lemma D_68054 : decode_any W_68054 = Some (OpImm ALU_ADD 24 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_68058 : bv 32 := 0x461c4583.
Lemma F_68058 : fetch_word AsanUbsan.M.loaded_segments (0x68058 : word) = Some W_68058.
Proof. vm_refl. Qed.
Lemma D_68058 : decode_any W_68058 = Some (Load SZ1 false 11 24 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_6805c : bv 32 := 0x00100613.
Lemma F_6805c : fetch_word AsanUbsan.M.loaded_segments (0x6805c : word) = Some W_6805c.
Proof. vm_refl. Qed.
Lemma D_6805c : decode_any W_6805c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_68060 : bv 32 := 0x46cc00a3.
Lemma F_68060 : fetch_word AsanUbsan.M.loaded_segments (0x68060 : word) = Some W_68060.
Proof. vm_refl. Qed.
Lemma D_68060 : decode_any W_68060 = Some (Store SZ1 24 12 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_68064 : bv 32 := 0x0a059a63.
Lemma F_68064 : fetch_word AsanUbsan.M.loaded_segments (0x68064 : word) = Some W_68064.
Proof. vm_refl. Qed.
Lemma D_68064 : decode_any W_68064 = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_68068 : bv 32 := 0x00050b93.
Lemma F_68068 : fetch_word AsanUbsan.M.loaded_segments (0x68068 : word) = Some W_68068.
Proof. vm_refl. Qed.
Lemma D_68068 : decode_any W_68068 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6806c : bv 32 := 0x3bd010ef.
Lemma F_6806c : fetch_word AsanUbsan.M.loaded_segments (0x6806c : word) = Some W_6806c.
Proof. vm_refl. Qed.
Lemma D_6806c : decode_any W_6806c = Some (Jal 1 7100, 4%Z).
Proof. vm_refl. Qed.

Definition W_68070 : bv 32 := 0x00050b13.
Lemma F_68070 : fetch_word AsanUbsan.M.loaded_segments (0x68070 : word) = Some W_68070.
Proof. vm_refl. Qed.
Lemma D_68070 : decode_any W_68070 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68074 : bv 32 := 0x000b8513.
Lemma F_68074 : fetch_word AsanUbsan.M.loaded_segments (0x68074 : word) = Some W_68074.
Proof. vm_refl. Qed.
Lemma D_68074 : decode_any W_68074 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68078 : bv 32 := 0x409010ef.
Lemma F_68078 : fetch_word AsanUbsan.M.loaded_segments (0x68078 : word) = Some W_68078.
Proof. vm_refl. Qed.
Lemma D_68078 : decode_any W_68078 = Some (Jal 1 7176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6807c : bv 32 := 0x00050813.
Lemma F_6807c : fetch_word AsanUbsan.M.loaded_segments (0x6807c : word) = Some W_6807c.
Proof. vm_refl. Qed.
Lemma D_6807c : decode_any W_6807c = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68080 : bv 32 := 0x060a8c63.
Lemma F_68080 : fetch_word AsanUbsan.M.loaded_segments (0x68080 : word) = Some W_68080.
Proof. vm_refl. Qed.
Lemma D_68080 : decode_any W_68080 = Some (Branch BC_EQ 21 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_68084 : bv 32 := 0x00100893.
Lemma F_68084 : fetch_word AsanUbsan.M.loaded_segments (0x68084 : word) = Some W_68084.
Proof. vm_refl. Qed.
Lemma D_68084 : decode_any W_68084 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_68088 : bv 32 := 0x00098513.
Lemma F_68088 : fetch_word AsanUbsan.M.loaded_segments (0x68088 : word) = Some W_68088.
Proof. vm_refl. Qed.
Lemma D_68088 : decode_any W_68088 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6808c : bv 32 := 0x00048593.
Lemma F_6808c : fetch_word AsanUbsan.M.loaded_segments (0x6808c : word) = Some W_6808c.
Proof. vm_refl. Qed.
Lemma D_6808c : decode_any W_6808c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68090 : bv 32 := 0x00090613.
Lemma F_68090 : fetch_word AsanUbsan.M.loaded_segments (0x68090 : word) = Some W_68090.
Proof. vm_refl. Qed.
Lemma D_68090 : decode_any W_68090 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68094 : bv 32 := 0x00040693.
Lemma F_68094 : fetch_word AsanUbsan.M.loaded_segments (0x68094 : word) = Some W_68094.
Proof. vm_refl. Qed.
Lemma D_68094 : decode_any W_68094 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68098 : bv 32 := 0x00000713.
Lemma F_68098 : fetch_word AsanUbsan.M.loaded_segments (0x68098 : word) = Some W_68098.
Proof. vm_refl. Qed.
Lemma D_68098 : decode_any W_68098 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6809c : bv 32 := 0x000b0793.
Lemma F_6809c : fetch_word AsanUbsan.M.loaded_segments (0x6809c : word) = Some W_6809c.
Proof. vm_refl. Qed.
Lemma D_6809c : decode_any W_6809c = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_680a0 : bv 32 := 0x0740006f.
Lemma F_680a0 : fetch_word AsanUbsan.M.loaded_segments (0x680a0 : word) = Some W_680a0.
Proof. vm_refl. Qed.
Lemma D_680a0 : decode_any W_680a0 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_680a4 : bv 32 := 0x060a9c63.
Lemma F_680a4 : fetch_word AsanUbsan.M.loaded_segments (0x680a4 : word) = Some W_680a4.
Proof. vm_refl. Qed.
Lemma D_680a4 : decode_any W_680a4 = Some (Branch BC_NE 21 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_680a8 : bv 32 := 0x00098513.
Lemma F_680a8 : fetch_word AsanUbsan.M.loaded_segments (0x680a8 : word) = Some W_680a8.
Proof. vm_refl. Qed.
Lemma D_680a8 : decode_any W_680a8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_680ac : bv 32 := 0x00048593.
Lemma F_680ac : fetch_word AsanUbsan.M.loaded_segments (0x680ac : word) = Some W_680ac.
Proof. vm_refl. Qed.
Lemma D_680ac : decode_any W_680ac = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_680b0 : bv 32 := 0x00090613.
Lemma F_680b0 : fetch_word AsanUbsan.M.loaded_segments (0x680b0 : word) = Some W_680b0.
Proof. vm_refl. Qed.
Lemma D_680b0 : decode_any W_680b0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_680b4 : bv 32 := 0x00040693.
Lemma F_680b4 : fetch_word AsanUbsan.M.loaded_segments (0x680b4 : word) = Some W_680b4.
Proof. vm_refl. Qed.
Lemma D_680b4 : decode_any W_680b4 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_680b8 : bv 32 := 0x000a0713.
Lemma F_680b8 : fetch_word AsanUbsan.M.loaded_segments (0x680b8 : word) = Some W_680b8.
Proof. vm_refl. Qed.
Lemma D_680b8 : decode_any W_680b8 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_680bc : bv 32 := 0x00000793.
Lemma F_680bc : fetch_word AsanUbsan.M.loaded_segments (0x680bc : word) = Some W_680bc.
Proof. vm_refl. Qed.
Lemma D_680bc : decode_any W_680bc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_680c0 : bv 32 := 0x00000813.
Lemma F_680c0 : fetch_word AsanUbsan.M.loaded_segments (0x680c0 : word) = Some W_680c0.
Proof. vm_refl. Qed.
Lemma D_680c0 : decode_any W_680c0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_680c4 : bv 32 := 0x00000893.
Lemma F_680c4 : fetch_word AsanUbsan.M.loaded_segments (0x680c4 : word) = Some W_680c4.
Proof. vm_refl. Qed.
Lemma D_680c4 : decode_any W_680c4 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_680c8 : bv 32 := 0x04813083.
Lemma F_680c8 : fetch_word AsanUbsan.M.loaded_segments (0x680c8 : word) = Some W_680c8.
Proof. vm_refl. Qed.
Lemma D_680c8 : decode_any W_680c8 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_680cc : bv 32 := 0x04013403.
Lemma F_680cc : fetch_word AsanUbsan.M.loaded_segments (0x680cc : word) = Some W_680cc.
Proof. vm_refl. Qed.
Lemma D_680cc : decode_any W_680cc = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_680d0 : bv 32 := 0x03813483.
Lemma F_680d0 : fetch_word AsanUbsan.M.loaded_segments (0x680d0 : word) = Some W_680d0.
Proof. vm_refl. Qed.
Lemma D_680d0 : decode_any W_680d0 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_680d4 : bv 32 := 0x03013903.
Lemma F_680d4 : fetch_word AsanUbsan.M.loaded_segments (0x680d4 : word) = Some W_680d4.
Proof. vm_refl. Qed.
Lemma D_680d4 : decode_any W_680d4 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_680d8 : bv 32 := 0x02813983.
Lemma F_680d8 : fetch_word AsanUbsan.M.loaded_segments (0x680d8 : word) = Some W_680d8.
Proof. vm_refl. Qed.
Lemma D_680d8 : decode_any W_680d8 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_680dc : bv 32 := 0x02013a03.
Lemma F_680dc : fetch_word AsanUbsan.M.loaded_segments (0x680dc : word) = Some W_680dc.
Proof. vm_refl. Qed.
Lemma D_680dc : decode_any W_680dc = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_680e0 : bv 32 := 0x01813a83.
Lemma F_680e0 : fetch_word AsanUbsan.M.loaded_segments (0x680e0 : word) = Some W_680e0.
Proof. vm_refl. Qed.
Lemma D_680e0 : decode_any W_680e0 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_680e4 : bv 32 := 0x01013b03.
Lemma F_680e4 : fetch_word AsanUbsan.M.loaded_segments (0x680e4 : word) = Some W_680e4.
Proof. vm_refl. Qed.
Lemma D_680e4 : decode_any W_680e4 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_680e8 : bv 32 := 0x00813b83.
Lemma F_680e8 : fetch_word AsanUbsan.M.loaded_segments (0x680e8 : word) = Some W_680e8.
Proof. vm_refl. Qed.
Lemma D_680e8 : decode_any W_680e8 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_680ec : bv 32 := 0x00013c03.
Lemma F_680ec : fetch_word AsanUbsan.M.loaded_segments (0x680ec : word) = Some W_680ec.
Proof. vm_refl. Qed.
Lemma D_680ec : decode_any W_680ec = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_680f0 : bv 32 := 0x05010113.
Lemma F_680f0 : fetch_word AsanUbsan.M.loaded_segments (0x680f0 : word) = Some W_680f0.
Proof. vm_refl. Qed.
Lemma D_680f0 : decode_any W_680f0 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_680f4 : bv 32 := 0x01c1906f.
Lemma F_680f4 : fetch_word AsanUbsan.M.loaded_segments (0x680f4 : word) = Some W_680f4.
Proof. vm_refl. Qed.
Lemma D_680f4 : decode_any W_680f4 = Some (Jal 0 102428, 4%Z).
Proof. vm_refl. Qed.

Definition W_680f8 : bv 32 := 0x00098513.
Lemma F_680f8 : fetch_word AsanUbsan.M.loaded_segments (0x680f8 : word) = Some W_680f8.
Proof. vm_refl. Qed.
Lemma D_680f8 : decode_any W_680f8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_680fc : bv 32 := 0x00048593.
Lemma F_680fc : fetch_word AsanUbsan.M.loaded_segments (0x680fc : word) = Some W_680fc.
Proof. vm_refl. Qed.
Lemma D_680fc : decode_any W_680fc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68100 : bv 32 := 0x00090613.
Lemma F_68100 : fetch_word AsanUbsan.M.loaded_segments (0x68100 : word) = Some W_68100.
Proof. vm_refl. Qed.
Lemma D_68100 : decode_any W_68100 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68104 : bv 32 := 0x00040693.
Lemma F_68104 : fetch_word AsanUbsan.M.loaded_segments (0x68104 : word) = Some W_68104.
Proof. vm_refl. Qed.
Lemma D_68104 : decode_any W_68104 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68108 : bv 32 := 0x000a0713.
Lemma F_68108 : fetch_word AsanUbsan.M.loaded_segments (0x68108 : word) = Some W_68108.
Proof. vm_refl. Qed.
Lemma D_68108 : decode_any W_68108 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6810c : bv 32 := 0x000b0793.
Lemma F_6810c : fetch_word AsanUbsan.M.loaded_segments (0x6810c : word) = Some W_6810c.
Proof. vm_refl. Qed.
Lemma D_6810c : decode_any W_6810c = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68110 : bv 32 := 0x00000893.
Lemma F_68110 : fetch_word AsanUbsan.M.loaded_segments (0x68110 : word) = Some W_68110.
Proof. vm_refl. Qed.
Lemma D_68110 : decode_any W_68110 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68114 : bv 32 := 0x7fd180ef.
Lemma F_68114 : fetch_word AsanUbsan.M.loaded_segments (0x68114 : word) = Some W_68114.
Proof. vm_refl. Qed.
Lemma D_68114 : decode_any W_68114 = Some (Jal 1 102396, 4%Z).
Proof. vm_refl. Qed.

Definition W_68118 : bv 32 := 0x460c00a3.
Lemma F_68118 : fetch_word AsanUbsan.M.loaded_segments (0x68118 : word) = Some W_68118.
Proof. vm_refl. Qed.
Lemma D_68118 : decode_any W_68118 = Some (Store SZ1 24 0 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_6811c : bv 32 := 0x04813083.
Lemma F_6811c : fetch_word AsanUbsan.M.loaded_segments (0x6811c : word) = Some W_6811c.
Proof. vm_refl. Qed.
Lemma D_6811c : decode_any W_6811c = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_68120 : bv 32 := 0x04013403.
Lemma F_68120 : fetch_word AsanUbsan.M.loaded_segments (0x68120 : word) = Some W_68120.
Proof. vm_refl. Qed.
Lemma D_68120 : decode_any W_68120 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_68124 : bv 32 := 0x03813483.
Lemma F_68124 : fetch_word AsanUbsan.M.loaded_segments (0x68124 : word) = Some W_68124.
Proof. vm_refl. Qed.
Lemma D_68124 : decode_any W_68124 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_68128 : bv 32 := 0x03013903.
Lemma F_68128 : fetch_word AsanUbsan.M.loaded_segments (0x68128 : word) = Some W_68128.
Proof. vm_refl. Qed.
Lemma D_68128 : decode_any W_68128 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6812c : bv 32 := 0x02813983.
Lemma F_6812c : fetch_word AsanUbsan.M.loaded_segments (0x6812c : word) = Some W_6812c.
Proof. vm_refl. Qed.
Lemma D_6812c : decode_any W_6812c = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_68130 : bv 32 := 0x02013a03.
Lemma F_68130 : fetch_word AsanUbsan.M.loaded_segments (0x68130 : word) = Some W_68130.
Proof. vm_refl. Qed.
Lemma D_68130 : decode_any W_68130 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_68134 : bv 32 := 0x01813a83.
Lemma F_68134 : fetch_word AsanUbsan.M.loaded_segments (0x68134 : word) = Some W_68134.
Proof. vm_refl. Qed.
Lemma D_68134 : decode_any W_68134 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_68138 : bv 32 := 0x01013b03.
Lemma F_68138 : fetch_word AsanUbsan.M.loaded_segments (0x68138 : word) = Some W_68138.
Proof. vm_refl. Qed.
Lemma D_68138 : decode_any W_68138 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6813c : bv 32 := 0x00813b83.
Lemma F_6813c : fetch_word AsanUbsan.M.loaded_segments (0x6813c : word) = Some W_6813c.
Proof. vm_refl. Qed.
Lemma D_6813c : decode_any W_6813c = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_68140 : bv 32 := 0x00013c03.
Lemma F_68140 : fetch_word AsanUbsan.M.loaded_segments (0x68140 : word) = Some W_68140.
Proof. vm_refl. Qed.
Lemma D_68140 : decode_any W_68140 = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68144 : bv 32 := 0x05010113.
Lemma F_68144 : fetch_word AsanUbsan.M.loaded_segments (0x68144 : word) = Some W_68144.
Proof. vm_refl. Qed.
Lemma D_68144 : decode_any W_68144 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_68148 : bv 32 := 0x00008067.
Lemma F_68148 : fetch_word AsanUbsan.M.loaded_segments (0x68148 : word) = Some W_68148.
Proof. vm_refl. Qed.
Lemma D_68148 : decode_any W_68148 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
