(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1d000 : bv 32 := 0x0025c803.
Lemma F_1d000 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0a0 : word) = Some W_1d000.
Proof. vm_refl. Qed.
Lemma D_1d000 : decode_any W_1d000 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d004 : bv 32 := 0x0035c883.
Lemma F_1d004 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0a4 : word) = Some W_1d004.
Proof. vm_refl. Qed.
Lemma D_1d004 : decode_any W_1d004 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d008 : bv 32 := 0x00458593.
Lemma F_1d008 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0a8 : word) = Some W_1d008.
Proof. vm_refl. Qed.
Lemma D_1d008 : decode_any W_1d008 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d00c : bv 32 := 0x00468293.
Lemma F_1d00c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0ac : word) = Some W_1d00c.
Proof. vm_refl. Qed.
Lemma D_1d00c : decode_any W_1d00c = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d010 : bv 32 := 0x00e68023.
Lemma F_1d010 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0b0 : word) = Some W_1d010.
Proof. vm_refl. Qed.
Lemma D_1d010 : decode_any W_1d010 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d014 : bv 32 := 0x00f680a3.
Lemma F_1d014 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0b4 : word) = Some W_1d014.
Proof. vm_refl. Qed.
Lemma D_1d014 : decode_any W_1d014 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d018 : bv 32 := 0x01068123.
Lemma F_1d018 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0b8 : word) = Some W_1d018.
Proof. vm_refl. Qed.
Lemma D_1d018 : decode_any W_1d018 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d01c : bv 32 := 0x011681a3.
Lemma F_1d01c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0bc : word) = Some W_1d01c.
Proof. vm_refl. Qed.
Lemma D_1d01c : decode_any W_1d01c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d020 : bv 32 := 0x00028693.
Lemma F_1d020 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0c0 : word) = Some W_1d020.
Proof. vm_refl. Qed.
Lemma D_1d020 : decode_any W_1d020 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d024 : bv 32 := 0x00267713.
Lemma F_1d024 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0c4 : word) = Some W_1d024.
Proof. vm_refl. Qed.
Lemma D_1d024 : decode_any W_1d024 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d028 : bv 32 := 0x00071863.
Lemma F_1d028 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0c8 : word) = Some W_1d028.
Proof. vm_refl. Qed.
Lemma D_1d028 : decode_any W_1d028 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d02c : bv 32 := 0x00167613.
Lemma F_1d02c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0cc : word) = Some W_1d02c.
Proof. vm_refl. Qed.
Lemma D_1d02c : decode_any W_1d02c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d030 : bv 32 := 0x02061663.
Lemma F_1d030 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0d0 : word) = Some W_1d030.
Proof. vm_refl. Qed.
Lemma D_1d030 : decode_any W_1d030 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d034 : bv 32 := 0x00008067.
Lemma F_1d034 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0d4 : word) = Some W_1d034.
Proof. vm_refl. Qed.
Lemma D_1d034 : decode_any W_1d034 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d038 : bv 32 := 0x0005c703.
Lemma F_1d038 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0d8 : word) = Some W_1d038.
Proof. vm_refl. Qed.
Lemma D_1d038 : decode_any W_1d038 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d03c : bv 32 := 0x0015c783.
Lemma F_1d03c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0dc : word) = Some W_1d03c.
Proof. vm_refl. Qed.
Lemma D_1d03c : decode_any W_1d03c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d040 : bv 32 := 0x00258593.
Lemma F_1d040 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0e0 : word) = Some W_1d040.
Proof. vm_refl. Qed.
Lemma D_1d040 : decode_any W_1d040 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d044 : bv 32 := 0x00268813.
Lemma F_1d044 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0e4 : word) = Some W_1d044.
Proof. vm_refl. Qed.
Lemma D_1d044 : decode_any W_1d044 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d048 : bv 32 := 0x00e68023.
Lemma F_1d048 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0e8 : word) = Some W_1d048.
Proof. vm_refl. Qed.
Lemma D_1d048 : decode_any W_1d048 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d04c : bv 32 := 0x00f680a3.
Lemma F_1d04c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0ec : word) = Some W_1d04c.
Proof. vm_refl. Qed.
Lemma D_1d04c : decode_any W_1d04c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d050 : bv 32 := 0x00080693.
Lemma F_1d050 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0f0 : word) = Some W_1d050.
Proof. vm_refl. Qed.
Lemma D_1d050 : decode_any W_1d050 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d054 : bv 32 := 0x00167613.
Lemma F_1d054 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0f4 : word) = Some W_1d054.
Proof. vm_refl. Qed.
Lemma D_1d054 : decode_any W_1d054 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d058 : bv 32 := 0xfc060ee3.
Lemma F_1d058 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0f8 : word) = Some W_1d058.
Proof. vm_refl. Qed.
Lemma D_1d058 : decode_any W_1d058 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d05c : bv 32 := 0x0005c583.
Lemma F_1d05c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d0fc : word) = Some W_1d05c.
Proof. vm_refl. Qed.
Lemma D_1d05c : decode_any W_1d05c = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d060 : bv 32 := 0x00b68023.
Lemma F_1d060 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d100 : word) = Some W_1d060.
Proof. vm_refl. Qed.
Lemma D_1d060 : decode_any W_1d060 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d064 : bv 32 := 0x00008067.
Lemma F_1d064 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d104 : word) = Some W_1d064.
Proof. vm_refl. Qed.
Lemma D_1d064 : decode_any W_1d064 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d068 : bv 32 := 0x0e060a63.
Lemma F_1d068 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d108 : word) = Some W_1d068.
Proof. vm_refl. Qed.
Lemma D_1d068 : decode_any W_1d068 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d06c : bv 32 := 0x00b50023.
Lemma F_1d06c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d10c : word) = Some W_1d06c.
Proof. vm_refl. Qed.
Lemma D_1d06c : decode_any W_1d06c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d070 : bv 32 := 0x00c506b3.
Lemma F_1d070 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d110 : word) = Some W_1d070.
Proof. vm_refl. Qed.
Lemma D_1d070 : decode_any W_1d070 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d074 : bv 32 := 0x00300713.
Lemma F_1d074 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d114 : word) = Some W_1d074.
Proof. vm_refl. Qed.
Lemma D_1d074 : decode_any W_1d074 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d078 : bv 32 := 0xfeb68fa3.
Lemma F_1d078 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d118 : word) = Some W_1d078.
Proof. vm_refl. Qed.
Lemma D_1d078 : decode_any W_1d078 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d07c : bv 32 := 0x0ee66063.
Lemma F_1d07c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d11c : word) = Some W_1d07c.
Proof. vm_refl. Qed.
Lemma D_1d07c : decode_any W_1d07c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d080 : bv 32 := 0x00b500a3.
Lemma F_1d080 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d120 : word) = Some W_1d080.
Proof. vm_refl. Qed.
Lemma D_1d080 : decode_any W_1d080 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d084 : bv 32 := 0x00b50123.
Lemma F_1d084 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d124 : word) = Some W_1d084.
Proof. vm_refl. Qed.
Lemma D_1d084 : decode_any W_1d084 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d088 : bv 32 := 0x00700713.
Lemma F_1d088 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d128 : word) = Some W_1d088.
Proof. vm_refl. Qed.
Lemma D_1d088 : decode_any W_1d088 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d08c : bv 32 := 0xfeb68ea3.
Lemma F_1d08c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d12c : word) = Some W_1d08c.
Proof. vm_refl. Qed.
Lemma D_1d08c : decode_any W_1d08c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d090 : bv 32 := 0xfeb68f23.
Lemma F_1d090 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d130 : word) = Some W_1d090.
Proof. vm_refl. Qed.
Lemma D_1d090 : decode_any W_1d090 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d094 : bv 32 := 0x0ce66463.
Lemma F_1d094 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d134 : word) = Some W_1d094.
Proof. vm_refl. Qed.
Lemma D_1d094 : decode_any W_1d094 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d098 : bv 32 := 0x00b501a3.
Lemma F_1d098 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d138 : word) = Some W_1d098.
Proof. vm_refl. Qed.
Lemma D_1d098 : decode_any W_1d098 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d09c : bv 32 := 0x00900793.
Lemma F_1d09c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d13c : word) = Some W_1d09c.
Proof. vm_refl. Qed.
Lemma D_1d09c : decode_any W_1d09c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0a0 : bv 32 := 0xfeb68e23.
Lemma F_1d0a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d140 : word) = Some W_1d0a0.
Proof. vm_refl. Qed.
Lemma D_1d0a0 : decode_any W_1d0a0 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0a4 : bv 32 := 0x0af66c63.
Lemma F_1d0a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d144 : word) = Some W_1d0a4.
Proof. vm_refl. Qed.
Lemma D_1d0a4 : decode_any W_1d0a4 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0a8 : bv 32 := 0x40a006bb.
Lemma F_1d0a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d148 : word) = Some W_1d0a8.
Proof. vm_refl. Qed.
Lemma D_1d0a8 : decode_any W_1d0a8 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0ac : bv 32 := 0x03859813.
Lemma F_1d0ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d14c : word) = Some W_1d0ac.
Proof. vm_refl. Qed.
Lemma D_1d0ac : decode_any W_1d0ac = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0b0 : bv 32 := 0x101015b7.
Lemma F_1d0b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d150 : word) = Some W_1d0b0.
Proof. vm_refl. Qed.
Lemma D_1d0b0 : decode_any W_1d0b0 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0b4 : bv 32 := 0x0036f693.
Lemma F_1d0b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d154 : word) = Some W_1d0b4.
Proof. vm_refl. Qed.
Lemma D_1d0b4 : decode_any W_1d0b4 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0b8 : bv 32 := 0x00459713.
Lemma F_1d0b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d158 : word) = Some W_1d0b8.
Proof. vm_refl. Qed.
Lemma D_1d0b8 : decode_any W_1d0b8 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0bc : bv 32 := 0x40d60633.
Lemma F_1d0bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d15c : word) = Some W_1d0bc.
Proof. vm_refl. Qed.
Lemma D_1d0bc : decode_any W_1d0bc = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0c0 : bv 32 := 0x00d505b3.
Lemma F_1d0c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d160 : word) = Some W_1d0c0.
Proof. vm_refl. Qed.
Lemma D_1d0c0 : decode_any W_1d0c0 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0c4 : bv 32 := 0x10070693.
Lemma F_1d0c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d164 : word) = Some W_1d0c4.
Proof. vm_refl. Qed.
Lemma D_1d0c4 : decode_any W_1d0c4 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0c8 : bv 32 := 0xffc67713.
Lemma F_1d0c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d168 : word) = Some W_1d0c8.
Proof. vm_refl. Qed.
Lemma D_1d0c8 : decode_any W_1d0c8 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0cc : bv 32 := 0x02d83633.
Lemma F_1d0cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d16c : word) = Some W_1d0cc.
Proof. vm_refl. Qed.
Lemma D_1d0cc : decode_any W_1d0cc = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0d0 : bv 32 := 0x00c5a023.
Lemma F_1d0d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d170 : word) = Some W_1d0d0.
Proof. vm_refl. Qed.
Lemma D_1d0d0 : decode_any W_1d0d0 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0d4 : bv 32 := 0x00e586b3.
Lemma F_1d0d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d174 : word) = Some W_1d0d4.
Proof. vm_refl. Qed.
Lemma D_1d0d4 : decode_any W_1d0d4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0d8 : bv 32 := 0xfec6ae23.
Lemma F_1d0d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d178 : word) = Some W_1d0d8.
Proof. vm_refl. Qed.
Lemma D_1d0d8 : decode_any W_1d0d8 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0dc : bv 32 := 0x08f76063.
Lemma F_1d0dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d17c : word) = Some W_1d0dc.
Proof. vm_refl. Qed.
Lemma D_1d0dc : decode_any W_1d0dc = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0e0 : bv 32 := 0x00c5a223.
Lemma F_1d0e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d180 : word) = Some W_1d0e0.
Proof. vm_refl. Qed.
Lemma D_1d0e0 : decode_any W_1d0e0 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0e4 : bv 32 := 0x00c5a423.
Lemma F_1d0e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d184 : word) = Some W_1d0e4.
Proof. vm_refl. Qed.
Lemma D_1d0e4 : decode_any W_1d0e4 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0e8 : bv 32 := 0x01900793.
Lemma F_1d0e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d188 : word) = Some W_1d0e8.
Proof. vm_refl. Qed.
Lemma D_1d0e8 : decode_any W_1d0e8 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0ec : bv 32 := 0xfec6aa23.
Lemma F_1d0ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d18c : word) = Some W_1d0ec.
Proof. vm_refl. Qed.
Lemma D_1d0ec : decode_any W_1d0ec = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0f0 : bv 32 := 0xfec6ac23.
Lemma F_1d0f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d190 : word) = Some W_1d0f0.
Proof. vm_refl. Qed.
Lemma D_1d0f0 : decode_any W_1d0f0 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0f4 : bv 32 := 0x06f76463.
Lemma F_1d0f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d194 : word) = Some W_1d0f4.
Proof. vm_refl. Qed.
Lemma D_1d0f4 : decode_any W_1d0f4 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0f8 : bv 32 := 0x00c5a623.
Lemma F_1d0f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d198 : word) = Some W_1d0f8.
Proof. vm_refl. Qed.
Lemma D_1d0f8 : decode_any W_1d0f8 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d0fc : bv 32 := 0x00c5a823.
Lemma F_1d0fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d19c : word) = Some W_1d0fc.
Proof. vm_refl. Qed.
Lemma D_1d0fc : decode_any W_1d0fc = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d100 : bv 32 := 0x00c5aa23.
Lemma F_1d100 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1a0 : word) = Some W_1d100.
Proof. vm_refl. Qed.
Lemma D_1d100 : decode_any W_1d100 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d104 : bv 32 := 0x00c5ac23.
Lemma F_1d104 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1a4 : word) = Some W_1d104.
Proof. vm_refl. Qed.
Lemma D_1d104 : decode_any W_1d104 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d108 : bv 32 := 0x0045f793.
Lemma F_1d108 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1a8 : word) = Some W_1d108.
Proof. vm_refl. Qed.
Lemma D_1d108 : decode_any W_1d108 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d10c : bv 32 := 0x02000813.
Lemma F_1d10c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1ac : word) = Some W_1d10c.
Proof. vm_refl. Qed.
Lemma D_1d10c : decode_any W_1d10c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d110 : bv 32 := 0x01878793.
Lemma F_1d110 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1b0 : word) = Some W_1d110.
Proof. vm_refl. Qed.
Lemma D_1d110 : decode_any W_1d110 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d114 : bv 32 := 0x40f70733.
Lemma F_1d114 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1b4 : word) = Some W_1d114.
Proof. vm_refl. Qed.
Lemma D_1d114 : decode_any W_1d114 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d118 : bv 32 := 0xfec6a223.
Lemma F_1d118 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1b8 : word) = Some W_1d118.
Proof. vm_refl. Qed.
Lemma D_1d118 : decode_any W_1d118 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d11c : bv 32 := 0xfec6a423.
Lemma F_1d11c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1bc : word) = Some W_1d11c.
Proof. vm_refl. Qed.
Lemma D_1d11c : decode_any W_1d11c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d120 : bv 32 := 0xfec6a623.
Lemma F_1d120 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1c0 : word) = Some W_1d120.
Proof. vm_refl. Qed.
Lemma D_1d120 : decode_any W_1d120 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d124 : bv 32 := 0xfec6a823.
Lemma F_1d124 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1c4 : word) = Some W_1d124.
Proof. vm_refl. Qed.
Lemma D_1d124 : decode_any W_1d124 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d128 : bv 32 := 0x03076a63.
Lemma F_1d128 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1c8 : word) = Some W_1d128.
Proof. vm_refl. Qed.
Lemma D_1d128 : decode_any W_1d128 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d12c : bv 32 := 0x02061613.
Lemma F_1d12c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1cc : word) = Some W_1d12c.
Proof. vm_refl. Qed.
Lemma D_1d12c : decode_any W_1d12c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d130 : bv 32 := 0x00f585b3.
Lemma F_1d130 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1d0 : word) = Some W_1d130.
Proof. vm_refl. Qed.
Lemma D_1d130 : decode_any W_1d130 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d134 : bv 32 := 0x02065693.
Lemma F_1d134 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1d4 : word) = Some W_1d134.
Proof. vm_refl. Qed.
Lemma D_1d134 : decode_any W_1d134 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d138 : bv 32 := 0x00d66633.
Lemma F_1d138 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1d8 : word) = Some W_1d138.
Proof. vm_refl. Qed.
Lemma D_1d138 : decode_any W_1d138 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d13c : bv 32 := 0x01f00693.
Lemma F_1d13c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1dc : word) = Some W_1d13c.
Proof. vm_refl. Qed.
Lemma D_1d13c : decode_any W_1d13c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d140 : bv 32 := 0x00c5b023.
Lemma F_1d140 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1e0 : word) = Some W_1d140.
Proof. vm_refl. Qed.
Lemma D_1d140 : decode_any W_1d140 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d144 : bv 32 := 0x00c5b423.
Lemma F_1d144 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1e4 : word) = Some W_1d144.
Proof. vm_refl. Qed.
Lemma D_1d144 : decode_any W_1d144 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d148 : bv 32 := 0x00c5b823.
Lemma F_1d148 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1e8 : word) = Some W_1d148.
Proof. vm_refl. Qed.
Lemma D_1d148 : decode_any W_1d148 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d14c : bv 32 := 0x00c5bc23.
Lemma F_1d14c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1ec : word) = Some W_1d14c.
Proof. vm_refl. Qed.
Lemma D_1d14c : decode_any W_1d14c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d150 : bv 32 := 0xfe070713.
Lemma F_1d150 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1f0 : word) = Some W_1d150.
Proof. vm_refl. Qed.
Lemma D_1d150 : decode_any W_1d150 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d154 : bv 32 := 0x02058593.
Lemma F_1d154 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1f4 : word) = Some W_1d154.
Proof. vm_refl. Qed.
Lemma D_1d154 : decode_any W_1d154 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d158 : bv 32 := 0xfee6e4e3.
Lemma F_1d158 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1f8 : word) = Some W_1d158.
Proof. vm_refl. Qed.
Lemma D_1d158 : decode_any W_1d158 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d15c : bv 32 := 0x00008067.
Lemma F_1d15c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d1fc : word) = Some W_1d15c.
Proof. vm_refl. Qed.
Lemma D_1d15c : decode_any W_1d15c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d160 : bv 32 := 0xfe010113.
Lemma F_1d160 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d200 : word) = Some W_1d160.
Proof. vm_refl. Qed.
Lemma D_1d160 : decode_any W_1d160 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d164 : bv 32 := 0x00113c23.
Lemma F_1d164 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d204 : word) = Some W_1d164.
Proof. vm_refl. Qed.
Lemma D_1d164 : decode_any W_1d164 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d168 : bv 32 := 0x00813823.
Lemma F_1d168 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d208 : word) = Some W_1d168.
Proof. vm_refl. Qed.
Lemma D_1d168 : decode_any W_1d168 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d16c : bv 32 := 0x00913423.
Lemma F_1d16c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d20c : word) = Some W_1d16c.
Proof. vm_refl. Qed.
Lemma D_1d16c : decode_any W_1d16c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d170 : bv 32 := 0x00058413.
Lemma F_1d170 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d210 : word) = Some W_1d170.
Proof. vm_refl. Qed.
Lemma D_1d170 : decode_any W_1d170 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d174 : bv 32 := 0x00050493.
Lemma F_1d174 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d214 : word) = Some W_1d174.
Proof. vm_refl. Qed.
Lemma D_1d174 : decode_any W_1d174 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d178 : bv 32 := 0x00000593.
Lemma F_1d178 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d218 : word) = Some W_1d178.
Proof. vm_refl. Qed.
Lemma D_1d178 : decode_any W_1d178 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d17c : bv 32 := 0x00040613.
Lemma F_1d17c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d21c : word) = Some W_1d17c.
Proof. vm_refl. Qed.
Lemma D_1d17c : decode_any W_1d17c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d180 : bv 32 := 0x024000ef.
Lemma F_1d180 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d220 : word) = Some W_1d180.
Proof. vm_refl. Qed.
Lemma D_1d180 : decode_any W_1d180 = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d184 : bv 32 := 0x00050463.
Lemma F_1d184 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d224 : word) = Some W_1d184.
Proof. vm_refl. Qed.
Lemma D_1d184 : decode_any W_1d184 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d188 : bv 32 := 0x40950433.
Lemma F_1d188 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d228 : word) = Some W_1d188.
Proof. vm_refl. Qed.
Lemma D_1d188 : decode_any W_1d188 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d18c : bv 32 := 0x00040513.
Lemma F_1d18c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d22c : word) = Some W_1d18c.
Proof. vm_refl. Qed.
Lemma D_1d18c : decode_any W_1d18c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d190 : bv 32 := 0x01813083.
Lemma F_1d190 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d230 : word) = Some W_1d190.
Proof. vm_refl. Qed.
Lemma D_1d190 : decode_any W_1d190 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d194 : bv 32 := 0x01013403.
Lemma F_1d194 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d234 : word) = Some W_1d194.
Proof. vm_refl. Qed.
Lemma D_1d194 : decode_any W_1d194 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d198 : bv 32 := 0x00813483.
Lemma F_1d198 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d238 : word) = Some W_1d198.
Proof. vm_refl. Qed.
Lemma D_1d198 : decode_any W_1d198 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d19c : bv 32 := 0x02010113.
Lemma F_1d19c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d23c : word) = Some W_1d19c.
Proof. vm_refl. Qed.
Lemma D_1d19c : decode_any W_1d19c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1a0 : bv 32 := 0x00008067.
Lemma F_1d1a0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d240 : word) = Some W_1d1a0.
Proof. vm_refl. Qed.
Lemma D_1d1a0 : decode_any W_1d1a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1a4 : bv 32 := 0x0ff5f593.
Lemma F_1d1a4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d244 : word) = Some W_1d1a4.
Proof. vm_refl. Qed.
Lemma D_1d1a4 : decode_any W_1d1a4 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1a8 : bv 32 := 0x00757693.
Lemma F_1d1a8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d248 : word) = Some W_1d1a8.
Proof. vm_refl. Qed.
Lemma D_1d1a8 : decode_any W_1d1a8 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1ac : bv 32 := 0x00c03733.
Lemma F_1d1ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d24c : word) = Some W_1d1ac.
Proof. vm_refl. Qed.
Lemma D_1d1ac : decode_any W_1d1ac = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1b0 : bv 32 := 0x02068c63.
Lemma F_1d1b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d250 : word) = Some W_1d1b0.
Proof. vm_refl. Qed.
Lemma D_1d1b0 : decode_any W_1d1b0 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1b4 : bv 32 := 0x02060a63.
Lemma F_1d1b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d254 : word) = Some W_1d1b4.
Proof. vm_refl. Qed.
Lemma D_1d1b4 : decode_any W_1d1b4 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1b8 : bv 32 := 0x00150793.
Lemma F_1d1b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d258 : word) = Some W_1d1b8.
Proof. vm_refl. Qed.
Lemma D_1d1b8 : decode_any W_1d1b8 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1bc : bv 32 := 0x00100813.
Lemma F_1d1bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d25c : word) = Some W_1d1bc.
Proof. vm_refl. Qed.
Lemma D_1d1bc : decode_any W_1d1bc = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1c0 : bv 32 := 0x00054703.
Lemma F_1d1c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d260 : word) = Some W_1d1c0.
Proof. vm_refl. Qed.
Lemma D_1d1c0 : decode_any W_1d1c0 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1c4 : bv 32 := 0x00060693.
Lemma F_1d1c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d264 : word) = Some W_1d1c4.
Proof. vm_refl. Qed.
Lemma D_1d1c4 : decode_any W_1d1c4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1c8 : bv 32 := 0x06b70e63.
Lemma F_1d1c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d268 : word) = Some W_1d1c8.
Proof. vm_refl. Qed.
Lemma D_1d1c8 : decode_any W_1d1c8 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1cc : bv 32 := 0x00150513.
Lemma F_1d1cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d26c : word) = Some W_1d1cc.
Proof. vm_refl. Qed.
Lemma D_1d1cc : decode_any W_1d1cc = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1d0 : bv 32 := 0xfff68613.
Lemma F_1d1d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d270 : word) = Some W_1d1d0.
Proof. vm_refl. Qed.
Lemma D_1d1d0 : decode_any W_1d1d0 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1d4 : bv 32 := 0x0077f893.
Lemma F_1d1d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d274 : word) = Some W_1d1d4.
Proof. vm_refl. Qed.
Lemma D_1d1d4 : decode_any W_1d1d4 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1d8 : bv 32 := 0x00c03733.
Lemma F_1d1d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d278 : word) = Some W_1d1d8.
Proof. vm_refl. Qed.
Lemma D_1d1d8 : decode_any W_1d1d8 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1dc : bv 32 := 0x00088663.
Lemma F_1d1dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d27c : word) = Some W_1d1dc.
Proof. vm_refl. Qed.
Lemma D_1d1dc : decode_any W_1d1dc = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1e0 : bv 32 := 0x00178793.
Lemma F_1d1e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d280 : word) = Some W_1d1e0.
Proof. vm_refl. Qed.
Lemma D_1d1e0 : decode_any W_1d1e0 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1e4 : bv 32 := 0xfd069ee3.
Lemma F_1d1e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d284 : word) = Some W_1d1e4.
Proof. vm_refl. Qed.
Lemma D_1d1e4 : decode_any W_1d1e4 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1e8 : bv 32 := 0x06070863.
Lemma F_1d1e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d288 : word) = Some W_1d1e8.
Proof. vm_refl. Qed.
Lemma D_1d1e8 : decode_any W_1d1e8 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1ec : bv 32 := 0x00054683.
Lemma F_1d1ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d28c : word) = Some W_1d1ec.
Proof. vm_refl. Qed.
Lemma D_1d1ec : decode_any W_1d1ec = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1f0 : bv 32 := 0x04b68663.
Lemma F_1d1f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d290 : word) = Some W_1d1f0.
Proof. vm_refl. Qed.
Lemma D_1d1f0 : decode_any W_1d1f0 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1f4 : bv 32 := 0x00800693.
Lemma F_1d1f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d294 : word) = Some W_1d1f4.
Proof. vm_refl. Qed.
Lemma D_1d1f4 : decode_any W_1d1f4 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1f8 : bv 32 := 0x04d66263.
Lemma F_1d1f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d298 : word) = Some W_1d1f8.
Proof. vm_refl. Qed.
Lemma D_1d1f8 : decode_any W_1d1f8 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d1fc : bv 32 := 0xffff4697.
Lemma F_1d1fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d29c : word) = Some W_1d1fc.
Proof. vm_refl. Qed.
Lemma D_1d1fc : decode_any W_1d1fc = Some (Auipc 13 1048564, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d200 : bv 32 := 0x7646b683.
Lemma F_1d200 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2a0 : word) = Some W_1d200.
Proof. vm_refl. Qed.
Lemma D_1d200 : decode_any W_1d200 = Some (Load SZ8 true 13 13 1892, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d204 : bv 32 := 0xffff4717.
Lemma F_1d204 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2a4 : word) = Some W_1d204.
Proof. vm_refl. Qed.
Lemma D_1d204 : decode_any W_1d204 = Some (Auipc 14 1048564, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d208 : bv 32 := 0x74c73703.
Lemma F_1d208 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2a8 : word) = Some W_1d208.
Proof. vm_refl. Qed.
Lemma D_1d208 : decode_any W_1d208 = Some (Load SZ8 true 14 14 1868, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d20c : bv 32 := 0x00168793.
Lemma F_1d20c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2ac : word) = Some W_1d20c.
Proof. vm_refl. Qed.
Lemma D_1d20c : decode_any W_1d20c = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d210 : bv 32 := 0x02f587b3.
Lemma F_1d210 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2b0 : word) = Some W_1d210.
Proof. vm_refl. Qed.
Lemma D_1d210 : decode_any W_1d210 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d214 : bv 32 := 0x00700813.
Lemma F_1d214 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2b4 : word) = Some W_1d214.
Proof. vm_refl. Qed.
Lemma D_1d214 : decode_any W_1d214 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d218 : bv 32 := 0x00053883.
Lemma F_1d218 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2b8 : word) = Some W_1d218.
Proof. vm_refl. Qed.
Lemma D_1d218 : decode_any W_1d218 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d21c : bv 32 := 0x00f8c8b3.
Lemma F_1d21c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2bc : word) = Some W_1d21c.
Proof. vm_refl. Qed.
Lemma D_1d21c : decode_any W_1d21c = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d220 : bv 32 := 0x411682b3.
Lemma F_1d220 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2c0 : word) = Some W_1d220.
Proof. vm_refl. Qed.
Lemma D_1d220 : decode_any W_1d220 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d224 : bv 32 := 0x0112e8b3.
Lemma F_1d224 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2c4 : word) = Some W_1d224.
Proof. vm_refl. Qed.
Lemma D_1d224 : decode_any W_1d224 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d228 : bv 32 := 0x00e8f8b3.
Lemma F_1d228 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2c8 : word) = Some W_1d228.
Proof. vm_refl. Qed.
Lemma D_1d228 : decode_any W_1d228 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d22c : bv 32 := 0x02e89a63.
Lemma F_1d22c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2cc : word) = Some W_1d22c.
Proof. vm_refl. Qed.
Lemma D_1d22c : decode_any W_1d22c = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d230 : bv 32 := 0xff860613.
Lemma F_1d230 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2d0 : word) = Some W_1d230.
Proof. vm_refl. Qed.
Lemma D_1d230 : decode_any W_1d230 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d234 : bv 32 := 0x00850513.
Lemma F_1d234 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2d4 : word) = Some W_1d234.
Proof. vm_refl. Qed.
Lemma D_1d234 : decode_any W_1d234 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d238 : bv 32 := 0xfec860e3.
Lemma F_1d238 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2d8 : word) = Some W_1d238.
Proof. vm_refl. Qed.
Lemma D_1d238 : decode_any W_1d238 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d23c : bv 32 := 0x00060693.
Lemma F_1d23c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2dc : word) = Some W_1d23c.
Proof. vm_refl. Qed.
Lemma D_1d23c : decode_any W_1d23c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d240 : bv 32 := 0x00060c63.
Lemma F_1d240 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2e0 : word) = Some W_1d240.
Proof. vm_refl. Qed.
Lemma D_1d240 : decode_any W_1d240 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d244 : bv 32 := 0x00054603.
Lemma F_1d244 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2e4 : word) = Some W_1d244.
Proof. vm_refl. Qed.
Lemma D_1d244 : decode_any W_1d244 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d248 : bv 32 := 0x00b60a63.
Lemma F_1d248 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2e8 : word) = Some W_1d248.
Proof. vm_refl. Qed.
Lemma D_1d248 : decode_any W_1d248 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d24c : bv 32 := 0xfff68693.
Lemma F_1d24c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2ec : word) = Some W_1d24c.
Proof. vm_refl. Qed.
Lemma D_1d24c : decode_any W_1d24c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d250 : bv 32 := 0x00150513.
Lemma F_1d250 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2f0 : word) = Some W_1d250.
Proof. vm_refl. Qed.
Lemma D_1d250 : decode_any W_1d250 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d254 : bv 32 := 0xfe0698e3.
Lemma F_1d254 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2f4 : word) = Some W_1d254.
Proof. vm_refl. Qed.
Lemma D_1d254 : decode_any W_1d254 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d25c : bv 32 := 0x00008067.
Lemma F_1d25c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d2fc : word) = Some W_1d25c.
Proof. vm_refl. Qed.
Lemma D_1d25c : decode_any W_1d25c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d260 : bv 32 := 0x00060693.
Lemma F_1d260 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d300 : word) = Some W_1d260.
Proof. vm_refl. Qed.
Lemma D_1d260 : decode_any W_1d260 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d264 : bv 32 := 0x00054603.
Lemma F_1d264 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d304 : word) = Some W_1d264.
Proof. vm_refl. Qed.
Lemma D_1d264 : decode_any W_1d264 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d268 : bv 32 := 0xfeb612e3.
Lemma F_1d268 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d308 : word) = Some W_1d268.
Proof. vm_refl. Qed.
Lemma D_1d268 : decode_any W_1d268 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d26c : bv 32 := 0xff1ff06f.
Lemma F_1d26c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d30c : word) = Some W_1d26c.
Proof. vm_refl. Qed.
Lemma D_1d26c : decode_any W_1d26c = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d270 : bv 32 := 0x00033597.
Lemma F_1d270 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d310 : word) = Some W_1d270.
Proof. vm_refl. Qed.
Lemma D_1d270 : decode_any W_1d270 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d274 : bv 32 := 0xa8358683.
Lemma F_1d274 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d314 : word) = Some W_1d274.
Proof. vm_refl. Qed.
Lemma D_1d274 : decode_any W_1d274 = Some (Load SZ1 true 13 11 2691, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d278 : bv 32 := 0x1e068863.
Lemma F_1d278 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d318 : word) = Some W_1d278.
Proof. vm_refl. Qed.
Lemma D_1d278 : decode_any W_1d278 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d468 : bv 32 := 0x00008067.
Lemma F_1d468 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d508 : word) = Some W_1d468.
Proof. vm_refl. Qed.
Lemma D_1d468 : decode_any W_1d468 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d4f8 : bv 32 := 0x00052583.
Lemma F_1d4f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d598 : word) = Some W_1d4f8.
Proof. vm_refl. Qed.
Lemma D_1d4f8 : decode_any W_1d4f8 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d4fc : bv 32 := 0x0005c463.
Lemma F_1d4fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d59c : word) = Some W_1d4fc.
Proof. vm_refl. Qed.
Lemma D_1d4fc : decode_any W_1d4fc = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d500 : bv 32 := 0x00008067.
Lemma F_1d500 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d5a0 : word) = Some W_1d500.
Proof. vm_refl. Qed.
Lemma D_1d500 : decode_any W_1d500 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d56c : bv 32 := 0x00050893.
Lemma F_1d56c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d60c : word) = Some W_1d56c.
Proof. vm_refl. Qed.
Lemma D_1d56c : decode_any W_1d56c = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d570 : bv 32 := 0x00058513.
Lemma F_1d570 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d610 : word) = Some W_1d570.
Proof. vm_refl. Qed.
Lemma D_1d570 : decode_any W_1d570 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d574 : bv 32 := 0x00060593.
Lemma F_1d574 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d614 : word) = Some W_1d574.
Proof. vm_refl. Qed.
Lemma D_1d574 : decode_any W_1d574 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d578 : bv 32 := 0x00068613.
Lemma F_1d578 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d618 : word) = Some W_1d578.
Proof. vm_refl. Qed.
Lemma D_1d578 : decode_any W_1d578 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d57c : bv 32 := 0x00070693.
Lemma F_1d57c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d61c : word) = Some W_1d57c.
Proof. vm_refl. Qed.
Lemma D_1d57c : decode_any W_1d57c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d580 : bv 32 := 0x00078713.
Lemma F_1d580 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d620 : word) = Some W_1d580.
Proof. vm_refl. Qed.
Lemma D_1d580 : decode_any W_1d580 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d584 : bv 32 := 0x00080793.
Lemma F_1d584 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d624 : word) = Some W_1d584.
Proof. vm_refl. Qed.
Lemma D_1d584 : decode_any W_1d584 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d588 : bv 32 := 0x00000073.
Lemma F_1d588 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d628 : word) = Some W_1d588.
Proof. vm_refl. Qed.
Lemma D_1d588 : decode_any W_1d588 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1d588 : is_ecall W_1d588 = true.
Proof. reflexivity. Qed.

Definition W_1d58c : bv 32 := 0x00008067.
Lemma F_1d58c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d62c : word) = Some W_1d58c.
Proof. vm_refl. Qed.
Lemma D_1d58c : decode_any W_1d58c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d590 : bv 32 := 0xfddff06f.
Lemma F_1d590 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d630 : word) = Some W_1d590.
Proof. vm_refl. Qed.
Lemma D_1d590 : decode_any W_1d590 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d594 : bv 32 := 0x00050213.
Lemma F_1d594 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d634 : word) = Some W_1d594.
Proof. vm_refl. Qed.
Lemma D_1d594 : decode_any W_1d594 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d598 : bv 32 := 0x00000513.
Lemma F_1d598 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d638 : word) = Some W_1d598.
Proof. vm_refl. Qed.
Lemma D_1d598 : decode_any W_1d598 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d59c : bv 32 := 0x00008067.
Lemma F_1d59c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d63c : word) = Some W_1d59c.
Proof. vm_refl. Qed.
Lemma D_1d59c : decode_any W_1d59c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5ac : bv 32 := 0xff010113.
Lemma F_1d5ac : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d64c : word) = Some W_1d5ac.
Proof. vm_refl. Qed.
Lemma D_1d5ac : decode_any W_1d5ac = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5b0 : bv 32 := 0x00113423.
Lemma F_1d5b0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d650 : word) = Some W_1d5b0.
Proof. vm_refl. Qed.
Lemma D_1d5b0 : decode_any W_1d5b0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5b4 : bv 32 := 0xa89fa0ef.
Lemma F_1d5b4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d654 : word) = Some W_1d5b4.
Proof. vm_refl. Qed.
Lemma D_1d5b4 : decode_any W_1d5b4 = Some (Jal 1 2075272, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5b8 : bv 32 := 0x00050593.
Lemma F_1d5b8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d658 : word) = Some W_1d5b8.
Proof. vm_refl. Qed.
Lemma D_1d5b8 : decode_any W_1d5b8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5bc : bv 32 := 0x03900513.
Lemma F_1d5bc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d65c : word) = Some W_1d5bc.
Proof. vm_refl. Qed.
Lemma D_1d5bc : decode_any W_1d5bc = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5c0 : bv 32 := 0x00000613.
Lemma F_1d5c0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d660 : word) = Some W_1d5c0.
Proof. vm_refl. Qed.
Lemma D_1d5c0 : decode_any W_1d5c0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5c4 : bv 32 := 0x00000693.
Lemma F_1d5c4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d664 : word) = Some W_1d5c4.
Proof. vm_refl. Qed.
Lemma D_1d5c4 : decode_any W_1d5c4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5c8 : bv 32 := 0x00000713.
Lemma F_1d5c8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d668 : word) = Some W_1d5c8.
Proof. vm_refl. Qed.
Lemma D_1d5c8 : decode_any W_1d5c8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5cc : bv 32 := 0x00000793.
Lemma F_1d5cc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d66c : word) = Some W_1d5cc.
Proof. vm_refl. Qed.
Lemma D_1d5cc : decode_any W_1d5cc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5d0 : bv 32 := 0x00000813.
Lemma F_1d5d0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d670 : word) = Some W_1d5d0.
Proof. vm_refl. Qed.
Lemma D_1d5d0 : decode_any W_1d5d0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5d4 : bv 32 := 0xfbdff0ef.
Lemma F_1d5d4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d674 : word) = Some W_1d5d4.
Proof. vm_refl. Qed.
Lemma D_1d5d4 : decode_any W_1d5d4 = Some (Jal 1 2097084, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5d8 : bv 32 := 0x0005051b.
Lemma F_1d5d8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d678 : word) = Some W_1d5d8.
Proof. vm_refl. Qed.
Lemma D_1d5d8 : decode_any W_1d5d8 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5dc : bv 32 := 0x00450593.
Lemma F_1d5dc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d67c : word) = Some W_1d5dc.
Proof. vm_refl. Qed.
Lemma D_1d5dc : decode_any W_1d5dc = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5e0 : bv 32 := 0x0015b593.
Lemma F_1d5e0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d680 : word) = Some W_1d5e0.
Proof. vm_refl. Qed.
Lemma D_1d5e0 : decode_any W_1d5e0 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5e4 : bv 32 := 0xfff58593.
Lemma F_1d5e4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d684 : word) = Some W_1d5e4.
Proof. vm_refl. Qed.
Lemma D_1d5e4 : decode_any W_1d5e4 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5e8 : bv 32 := 0x00a5f533.
Lemma F_1d5e8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d688 : word) = Some W_1d5e8.
Proof. vm_refl. Qed.
Lemma D_1d5e8 : decode_any W_1d5e8 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5ec : bv 32 := 0xeb8f80ef.
Lemma F_1d5ec : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d68c : word) = Some W_1d5ec.
Proof. vm_refl. Qed.
Lemma D_1d5ec : decode_any W_1d5ec = Some (Jal 1 2066104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5f0 : bv 32 := 0x0005051b.
Lemma F_1d5f0 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d690 : word) = Some W_1d5f0.
Proof. vm_refl. Qed.
Lemma D_1d5f0 : decode_any W_1d5f0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5f4 : bv 32 := 0x00813083.
Lemma F_1d5f4 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d694 : word) = Some W_1d5f4.
Proof. vm_refl. Qed.
Lemma D_1d5f4 : decode_any W_1d5f4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5f8 : bv 32 := 0x01010113.
Lemma F_1d5f8 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d698 : word) = Some W_1d5f8.
Proof. vm_refl. Qed.
Lemma D_1d5f8 : decode_any W_1d5f8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d5fc : bv 32 := 0x00008067.
Lemma F_1d5fc : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d69c : word) = Some W_1d5fc.
Proof. vm_refl. Qed.
Lemma D_1d5fc : decode_any W_1d5fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d600 : bv 32 := 0x03e00893.
Lemma F_1d600 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6a0 : word) = Some W_1d600.
Proof. vm_refl. Qed.
Lemma D_1d600 : decode_any W_1d600 = Some (OpImm ALU_ADD 17 0 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d604 : bv 32 := 0x00000073.
Lemma F_1d604 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6a4 : word) = Some W_1d604.
Proof. vm_refl. Qed.
Lemma D_1d604 : decode_any W_1d604 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1d604 : is_ecall W_1d604 = true.
Proof. reflexivity. Qed.

Definition W_1d608 : bv 32 := 0xe9cf806f.
Lemma F_1d608 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6a8 : word) = Some W_1d608.
Proof. vm_refl. Qed.
Lemma D_1d608 : decode_any W_1d608 = Some (Jal 0 2066076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d60c : bv 32 := 0xff010113.
Lemma F_1d60c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6ac : word) = Some W_1d60c.
Proof. vm_refl. Qed.
Lemma D_1d60c : decode_any W_1d60c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d610 : bv 32 := 0x00113423.
Lemma F_1d610 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6b0 : word) = Some W_1d610.
Proof. vm_refl. Qed.
Lemma D_1d610 : decode_any W_1d610 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d614 : bv 32 := 0x00060693.
Lemma F_1d614 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6b4 : word) = Some W_1d614.
Proof. vm_refl. Qed.
Lemma D_1d614 : decode_any W_1d614 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d618 : bv 32 := 0x00058613.
Lemma F_1d618 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6b8 : word) = Some W_1d618.
Proof. vm_refl. Qed.
Lemma D_1d618 : decode_any W_1d618 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d61c : bv 32 := 0x00050593.
Lemma F_1d61c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6bc : word) = Some W_1d61c.
Proof. vm_refl. Qed.
Lemma D_1d61c : decode_any W_1d61c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d620 : bv 32 := 0x03f00513.
Lemma F_1d620 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6c0 : word) = Some W_1d620.
Proof. vm_refl. Qed.
Lemma D_1d620 : decode_any W_1d620 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d624 : bv 32 := 0x00000713.
Lemma F_1d624 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6c4 : word) = Some W_1d624.
Proof. vm_refl. Qed.
Lemma D_1d624 : decode_any W_1d624 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d628 : bv 32 := 0x00000793.
Lemma F_1d628 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6c8 : word) = Some W_1d628.
Proof. vm_refl. Qed.
Lemma D_1d628 : decode_any W_1d628 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d62c : bv 32 := 0x00000813.
Lemma F_1d62c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6cc : word) = Some W_1d62c.
Proof. vm_refl. Qed.
Lemma D_1d62c : decode_any W_1d62c = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d630 : bv 32 := 0xf61ff0ef.
Lemma F_1d630 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6d0 : word) = Some W_1d630.
Proof. vm_refl. Qed.
Lemma D_1d630 : decode_any W_1d630 = Some (Jal 1 2096992, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d634 : bv 32 := 0x00813083.
Lemma F_1d634 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6d4 : word) = Some W_1d634.
Proof. vm_refl. Qed.
Lemma D_1d634 : decode_any W_1d634 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d638 : bv 32 := 0x01010113.
Lemma F_1d638 : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6d8 : word) = Some W_1d638.
Proof. vm_refl. Qed.
Lemma D_1d638 : decode_any W_1d638 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d63c : bv 32 := 0xe68f806f.
Lemma F_1d63c : fetch_word Src_zlib_checksum_fuzzer_repro.M.loaded_segments (0x1d6dc : word) = Some W_1d63c.
Proof. vm_refl. Qed.
Lemma D_1d63c : decode_any W_1d63c = Some (Jal 0 2066024, 4%Z).
Proof. vm_refl. Qed.
