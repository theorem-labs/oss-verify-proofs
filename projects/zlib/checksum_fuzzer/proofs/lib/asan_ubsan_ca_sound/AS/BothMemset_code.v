(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.World Require Import Tgt_checksum_fuzzer_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_92f68 : bv 32 := 0x0e060a63.
Lemma F_92f68 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x9300c : word) = Some W_92f68.
Proof. vm_refl. Qed.
Lemma D_92f68 : decode_any W_92f68 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f6c : bv 32 := 0x00b50023.
Lemma F_92f6c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93010 : word) = Some W_92f6c.
Proof. vm_refl. Qed.
Lemma D_92f6c : decode_any W_92f6c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f70 : bv 32 := 0x00c506b3.
Lemma F_92f70 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93014 : word) = Some W_92f70.
Proof. vm_refl. Qed.
Lemma D_92f70 : decode_any W_92f70 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f74 : bv 32 := 0x00300713.
Lemma F_92f74 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93018 : word) = Some W_92f74.
Proof. vm_refl. Qed.
Lemma D_92f74 : decode_any W_92f74 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f78 : bv 32 := 0xfeb68fa3.
Lemma F_92f78 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x9301c : word) = Some W_92f78.
Proof. vm_refl. Qed.
Lemma D_92f78 : decode_any W_92f78 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f7c : bv 32 := 0x0ee66063.
Lemma F_92f7c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93020 : word) = Some W_92f7c.
Proof. vm_refl. Qed.
Lemma D_92f7c : decode_any W_92f7c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f80 : bv 32 := 0x00b500a3.
Lemma F_92f80 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93024 : word) = Some W_92f80.
Proof. vm_refl. Qed.
Lemma D_92f80 : decode_any W_92f80 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f84 : bv 32 := 0x00b50123.
Lemma F_92f84 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93028 : word) = Some W_92f84.
Proof. vm_refl. Qed.
Lemma D_92f84 : decode_any W_92f84 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f88 : bv 32 := 0x00700713.
Lemma F_92f88 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x9302c : word) = Some W_92f88.
Proof. vm_refl. Qed.
Lemma D_92f88 : decode_any W_92f88 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f8c : bv 32 := 0xfeb68ea3.
Lemma F_92f8c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93030 : word) = Some W_92f8c.
Proof. vm_refl. Qed.
Lemma D_92f8c : decode_any W_92f8c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f90 : bv 32 := 0xfeb68f23.
Lemma F_92f90 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93034 : word) = Some W_92f90.
Proof. vm_refl. Qed.
Lemma D_92f90 : decode_any W_92f90 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f94 : bv 32 := 0x0ce66463.
Lemma F_92f94 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93038 : word) = Some W_92f94.
Proof. vm_refl. Qed.
Lemma D_92f94 : decode_any W_92f94 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f98 : bv 32 := 0x00b501a3.
Lemma F_92f98 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x9303c : word) = Some W_92f98.
Proof. vm_refl. Qed.
Lemma D_92f98 : decode_any W_92f98 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f9c : bv 32 := 0x00900793.
Lemma F_92f9c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93040 : word) = Some W_92f9c.
Proof. vm_refl. Qed.
Lemma D_92f9c : decode_any W_92f9c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fa0 : bv 32 := 0xfeb68e23.
Lemma F_92fa0 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93044 : word) = Some W_92fa0.
Proof. vm_refl. Qed.
Lemma D_92fa0 : decode_any W_92fa0 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fa4 : bv 32 := 0x0af66c63.
Lemma F_92fa4 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93048 : word) = Some W_92fa4.
Proof. vm_refl. Qed.
Lemma D_92fa4 : decode_any W_92fa4 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fa8 : bv 32 := 0x40a006bb.
Lemma F_92fa8 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x9304c : word) = Some W_92fa8.
Proof. vm_refl. Qed.
Lemma D_92fa8 : decode_any W_92fa8 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fac : bv 32 := 0x03859813.
Lemma F_92fac : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93050 : word) = Some W_92fac.
Proof. vm_refl. Qed.
Lemma D_92fac : decode_any W_92fac = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fb0 : bv 32 := 0x101015b7.
Lemma F_92fb0 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93054 : word) = Some W_92fb0.
Proof. vm_refl. Qed.
Lemma D_92fb0 : decode_any W_92fb0 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fb4 : bv 32 := 0x0036f693.
Lemma F_92fb4 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93058 : word) = Some W_92fb4.
Proof. vm_refl. Qed.
Lemma D_92fb4 : decode_any W_92fb4 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fb8 : bv 32 := 0x00459713.
Lemma F_92fb8 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x9305c : word) = Some W_92fb8.
Proof. vm_refl. Qed.
Lemma D_92fb8 : decode_any W_92fb8 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fbc : bv 32 := 0x40d60633.
Lemma F_92fbc : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93060 : word) = Some W_92fbc.
Proof. vm_refl. Qed.
Lemma D_92fbc : decode_any W_92fbc = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fc0 : bv 32 := 0x00d505b3.
Lemma F_92fc0 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93064 : word) = Some W_92fc0.
Proof. vm_refl. Qed.
Lemma D_92fc0 : decode_any W_92fc0 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fc4 : bv 32 := 0x10070693.
Lemma F_92fc4 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93068 : word) = Some W_92fc4.
Proof. vm_refl. Qed.
Lemma D_92fc4 : decode_any W_92fc4 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fc8 : bv 32 := 0xffc67713.
Lemma F_92fc8 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x9306c : word) = Some W_92fc8.
Proof. vm_refl. Qed.
Lemma D_92fc8 : decode_any W_92fc8 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fcc : bv 32 := 0x02d83633.
Lemma F_92fcc : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93070 : word) = Some W_92fcc.
Proof. vm_refl. Qed.
Lemma D_92fcc : decode_any W_92fcc = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fd0 : bv 32 := 0x00c5a023.
Lemma F_92fd0 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93074 : word) = Some W_92fd0.
Proof. vm_refl. Qed.
Lemma D_92fd0 : decode_any W_92fd0 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fd4 : bv 32 := 0x00e586b3.
Lemma F_92fd4 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93078 : word) = Some W_92fd4.
Proof. vm_refl. Qed.
Lemma D_92fd4 : decode_any W_92fd4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fd8 : bv 32 := 0xfec6ae23.
Lemma F_92fd8 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x9307c : word) = Some W_92fd8.
Proof. vm_refl. Qed.
Lemma D_92fd8 : decode_any W_92fd8 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fdc : bv 32 := 0x08f76063.
Lemma F_92fdc : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93080 : word) = Some W_92fdc.
Proof. vm_refl. Qed.
Lemma D_92fdc : decode_any W_92fdc = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fe0 : bv 32 := 0x00c5a223.
Lemma F_92fe0 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93084 : word) = Some W_92fe0.
Proof. vm_refl. Qed.
Lemma D_92fe0 : decode_any W_92fe0 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fe4 : bv 32 := 0x00c5a423.
Lemma F_92fe4 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93088 : word) = Some W_92fe4.
Proof. vm_refl. Qed.
Lemma D_92fe4 : decode_any W_92fe4 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fe8 : bv 32 := 0x01900793.
Lemma F_92fe8 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x9308c : word) = Some W_92fe8.
Proof. vm_refl. Qed.
Lemma D_92fe8 : decode_any W_92fe8 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_92fec : bv 32 := 0xfec6aa23.
Lemma F_92fec : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93090 : word) = Some W_92fec.
Proof. vm_refl. Qed.
Lemma D_92fec : decode_any W_92fec = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ff0 : bv 32 := 0xfec6ac23.
Lemma F_92ff0 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93094 : word) = Some W_92ff0.
Proof. vm_refl. Qed.
Lemma D_92ff0 : decode_any W_92ff0 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ff4 : bv 32 := 0x06f76463.
Lemma F_92ff4 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93098 : word) = Some W_92ff4.
Proof. vm_refl. Qed.
Lemma D_92ff4 : decode_any W_92ff4 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ff8 : bv 32 := 0x00c5a623.
Lemma F_92ff8 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x9309c : word) = Some W_92ff8.
Proof. vm_refl. Qed.
Lemma D_92ff8 : decode_any W_92ff8 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ffc : bv 32 := 0x00c5a823.
Lemma F_92ffc : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930a0 : word) = Some W_92ffc.
Proof. vm_refl. Qed.
Lemma D_92ffc : decode_any W_92ffc = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_93000 : bv 32 := 0x00c5aa23.
Lemma F_93000 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930a4 : word) = Some W_93000.
Proof. vm_refl. Qed.
Lemma D_93000 : decode_any W_93000 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_93004 : bv 32 := 0x00c5ac23.
Lemma F_93004 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930a8 : word) = Some W_93004.
Proof. vm_refl. Qed.
Lemma D_93004 : decode_any W_93004 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_93008 : bv 32 := 0x0045f793.
Lemma F_93008 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930ac : word) = Some W_93008.
Proof. vm_refl. Qed.
Lemma D_93008 : decode_any W_93008 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9300c : bv 32 := 0x02000813.
Lemma F_9300c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930b0 : word) = Some W_9300c.
Proof. vm_refl. Qed.
Lemma D_9300c : decode_any W_9300c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_93010 : bv 32 := 0x01878793.
Lemma F_93010 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930b4 : word) = Some W_93010.
Proof. vm_refl. Qed.
Lemma D_93010 : decode_any W_93010 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_93014 : bv 32 := 0x40f70733.
Lemma F_93014 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930b8 : word) = Some W_93014.
Proof. vm_refl. Qed.
Lemma D_93014 : decode_any W_93014 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93018 : bv 32 := 0xfec6a223.
Lemma F_93018 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930bc : word) = Some W_93018.
Proof. vm_refl. Qed.
Lemma D_93018 : decode_any W_93018 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_9301c : bv 32 := 0xfec6a423.
Lemma F_9301c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930c0 : word) = Some W_9301c.
Proof. vm_refl. Qed.
Lemma D_9301c : decode_any W_9301c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_93020 : bv 32 := 0xfec6a623.
Lemma F_93020 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930c4 : word) = Some W_93020.
Proof. vm_refl. Qed.
Lemma D_93020 : decode_any W_93020 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_93024 : bv 32 := 0xfec6a823.
Lemma F_93024 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930c8 : word) = Some W_93024.
Proof. vm_refl. Qed.
Lemma D_93024 : decode_any W_93024 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_93028 : bv 32 := 0x03076a63.
Lemma F_93028 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930cc : word) = Some W_93028.
Proof. vm_refl. Qed.
Lemma D_93028 : decode_any W_93028 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_9302c : bv 32 := 0x02061613.
Lemma F_9302c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930d0 : word) = Some W_9302c.
Proof. vm_refl. Qed.
Lemma D_9302c : decode_any W_9302c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_93030 : bv 32 := 0x00f585b3.
Lemma F_93030 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930d4 : word) = Some W_93030.
Proof. vm_refl. Qed.
Lemma D_93030 : decode_any W_93030 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_93034 : bv 32 := 0x02065693.
Lemma F_93034 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930d8 : word) = Some W_93034.
Proof. vm_refl. Qed.
Lemma D_93034 : decode_any W_93034 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_93038 : bv 32 := 0x00d66633.
Lemma F_93038 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930dc : word) = Some W_93038.
Proof. vm_refl. Qed.
Lemma D_93038 : decode_any W_93038 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_9303c : bv 32 := 0x01f00693.
Lemma F_9303c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930e0 : word) = Some W_9303c.
Proof. vm_refl. Qed.
Lemma D_9303c : decode_any W_9303c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_93040 : bv 32 := 0x00c5b023.
Lemma F_93040 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930e4 : word) = Some W_93040.
Proof. vm_refl. Qed.
Lemma D_93040 : decode_any W_93040 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93044 : bv 32 := 0x00c5b423.
Lemma F_93044 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930e8 : word) = Some W_93044.
Proof. vm_refl. Qed.
Lemma D_93044 : decode_any W_93044 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_93048 : bv 32 := 0x00c5b823.
Lemma F_93048 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930ec : word) = Some W_93048.
Proof. vm_refl. Qed.
Lemma D_93048 : decode_any W_93048 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9304c : bv 32 := 0x00c5bc23.
Lemma F_9304c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930f0 : word) = Some W_9304c.
Proof. vm_refl. Qed.
Lemma D_9304c : decode_any W_9304c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_93050 : bv 32 := 0xfe070713.
Lemma F_93050 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930f4 : word) = Some W_93050.
Proof. vm_refl. Qed.
Lemma D_93050 : decode_any W_93050 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_93054 : bv 32 := 0x02058593.
Lemma F_93054 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930f8 : word) = Some W_93054.
Proof. vm_refl. Qed.
Lemma D_93054 : decode_any W_93054 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_93058 : bv 32 := 0xfee6e4e3.
Lemma F_93058 : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x930fc : word) = Some W_93058.
Proof. vm_refl. Qed.
Lemma D_93058 : decode_any W_93058 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_9305c : bv 32 := 0x00008067.
Lemma F_9305c : fetch_word Tgt_checksum_fuzzer_both.M.loaded_segments (0x93100 : word) = Some W_9305c.
Proof. vm_refl. Qed.
Lemma D_9305c : decode_any W_9305c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := Tgt_checksum_fuzzer_both.M.loaded_segments.
Definition ms_base : Z := 0x9300c%Z.
Definition Fo_000 := F_92f68.
Definition Do_000 := D_92f68.
Definition Fo_004 := F_92f6c.
Definition Do_004 := D_92f6c.
Definition Fo_008 := F_92f70.
Definition Do_008 := D_92f70.
Definition Fo_00c := F_92f74.
Definition Do_00c := D_92f74.
Definition Fo_010 := F_92f78.
Definition Do_010 := D_92f78.
Definition Fo_014 := F_92f7c.
Definition Do_014 := D_92f7c.
Definition Fo_018 := F_92f80.
Definition Do_018 := D_92f80.
Definition Fo_01c := F_92f84.
Definition Do_01c := D_92f84.
Definition Fo_020 := F_92f88.
Definition Do_020 := D_92f88.
Definition Fo_024 := F_92f8c.
Definition Do_024 := D_92f8c.
Definition Fo_028 := F_92f90.
Definition Do_028 := D_92f90.
Definition Fo_02c := F_92f94.
Definition Do_02c := D_92f94.
Definition Fo_030 := F_92f98.
Definition Do_030 := D_92f98.
Definition Fo_034 := F_92f9c.
Definition Do_034 := D_92f9c.
Definition Fo_038 := F_92fa0.
Definition Do_038 := D_92fa0.
Definition Fo_03c := F_92fa4.
Definition Do_03c := D_92fa4.
Definition Fo_040 := F_92fa8.
Definition Do_040 := D_92fa8.
Definition Fo_044 := F_92fac.
Definition Do_044 := D_92fac.
Definition Fo_048 := F_92fb0.
Definition Do_048 := D_92fb0.
Definition Fo_04c := F_92fb4.
Definition Do_04c := D_92fb4.
Definition Fo_050 := F_92fb8.
Definition Do_050 := D_92fb8.
Definition Fo_054 := F_92fbc.
Definition Do_054 := D_92fbc.
Definition Fo_058 := F_92fc0.
Definition Do_058 := D_92fc0.
Definition Fo_05c := F_92fc4.
Definition Do_05c := D_92fc4.
Definition Fo_060 := F_92fc8.
Definition Do_060 := D_92fc8.
Definition Fo_064 := F_92fcc.
Definition Do_064 := D_92fcc.
Definition Fo_068 := F_92fd0.
Definition Do_068 := D_92fd0.
Definition Fo_06c := F_92fd4.
Definition Do_06c := D_92fd4.
Definition Fo_070 := F_92fd8.
Definition Do_070 := D_92fd8.
Definition Fo_074 := F_92fdc.
Definition Do_074 := D_92fdc.
Definition Fo_078 := F_92fe0.
Definition Do_078 := D_92fe0.
Definition Fo_07c := F_92fe4.
Definition Do_07c := D_92fe4.
Definition Fo_080 := F_92fe8.
Definition Do_080 := D_92fe8.
Definition Fo_084 := F_92fec.
Definition Do_084 := D_92fec.
Definition Fo_088 := F_92ff0.
Definition Do_088 := D_92ff0.
Definition Fo_08c := F_92ff4.
Definition Do_08c := D_92ff4.
Definition Fo_090 := F_92ff8.
Definition Do_090 := D_92ff8.
Definition Fo_094 := F_92ffc.
Definition Do_094 := D_92ffc.
Definition Fo_098 := F_93000.
Definition Do_098 := D_93000.
Definition Fo_09c := F_93004.
Definition Do_09c := D_93004.
Definition Fo_0a0 := F_93008.
Definition Do_0a0 := D_93008.
Definition Fo_0a4 := F_9300c.
Definition Do_0a4 := D_9300c.
Definition Fo_0a8 := F_93010.
Definition Do_0a8 := D_93010.
Definition Fo_0ac := F_93014.
Definition Do_0ac := D_93014.
Definition Fo_0b0 := F_93018.
Definition Do_0b0 := D_93018.
Definition Fo_0b4 := F_9301c.
Definition Do_0b4 := D_9301c.
Definition Fo_0b8 := F_93020.
Definition Do_0b8 := D_93020.
Definition Fo_0bc := F_93024.
Definition Do_0bc := D_93024.
Definition Fo_0c0 := F_93028.
Definition Do_0c0 := D_93028.
Definition Fo_0c4 := F_9302c.
Definition Do_0c4 := D_9302c.
Definition Fo_0c8 := F_93030.
Definition Do_0c8 := D_93030.
Definition Fo_0cc := F_93034.
Definition Do_0cc := D_93034.
Definition Fo_0d0 := F_93038.
Definition Do_0d0 := D_93038.
Definition Fo_0d4 := F_9303c.
Definition Do_0d4 := D_9303c.
Definition Fo_0d8 := F_93040.
Definition Do_0d8 := D_93040.
Definition Fo_0dc := F_93044.
Definition Do_0dc := D_93044.
Definition Fo_0e0 := F_93048.
Definition Do_0e0 := D_93048.
Definition Fo_0e4 := F_9304c.
Definition Do_0e4 := D_9304c.
Definition Fo_0e8 := F_93050.
Definition Do_0e8 := D_93050.
Definition Fo_0ec := F_93054.
Definition Do_0ec := D_93054.
Definition Fo_0f0 := F_93058.
Definition Do_0f0 := D_93058.
Definition Fo_0f4 := F_9305c.
Definition Do_0f4 := D_9305c.
