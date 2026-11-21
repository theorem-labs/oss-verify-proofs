(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.World Require Import Tgt_checksum_fuzzer_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_92e20 : bv 32 := 0x0e060a63.
Lemma F_92e20 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ebc : word) = Some W_92e20.
Proof. vm_refl. Qed.
Lemma D_92e20 : decode_any W_92e20 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e24 : bv 32 := 0x00b50023.
Lemma F_92e24 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ec0 : word) = Some W_92e24.
Proof. vm_refl. Qed.
Lemma D_92e24 : decode_any W_92e24 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e28 : bv 32 := 0x00c506b3.
Lemma F_92e28 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ec4 : word) = Some W_92e28.
Proof. vm_refl. Qed.
Lemma D_92e28 : decode_any W_92e28 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e2c : bv 32 := 0x00300713.
Lemma F_92e2c : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ec8 : word) = Some W_92e2c.
Proof. vm_refl. Qed.
Lemma D_92e2c : decode_any W_92e2c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e30 : bv 32 := 0xfeb68fa3.
Lemma F_92e30 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ecc : word) = Some W_92e30.
Proof. vm_refl. Qed.
Lemma D_92e30 : decode_any W_92e30 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e34 : bv 32 := 0x0ee66063.
Lemma F_92e34 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ed0 : word) = Some W_92e34.
Proof. vm_refl. Qed.
Lemma D_92e34 : decode_any W_92e34 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e38 : bv 32 := 0x00b500a3.
Lemma F_92e38 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ed4 : word) = Some W_92e38.
Proof. vm_refl. Qed.
Lemma D_92e38 : decode_any W_92e38 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e3c : bv 32 := 0x00b50123.
Lemma F_92e3c : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ed8 : word) = Some W_92e3c.
Proof. vm_refl. Qed.
Lemma D_92e3c : decode_any W_92e3c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e40 : bv 32 := 0x00700713.
Lemma F_92e40 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92edc : word) = Some W_92e40.
Proof. vm_refl. Qed.
Lemma D_92e40 : decode_any W_92e40 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e44 : bv 32 := 0xfeb68ea3.
Lemma F_92e44 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ee0 : word) = Some W_92e44.
Proof. vm_refl. Qed.
Lemma D_92e44 : decode_any W_92e44 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e48 : bv 32 := 0xfeb68f23.
Lemma F_92e48 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ee4 : word) = Some W_92e48.
Proof. vm_refl. Qed.
Lemma D_92e48 : decode_any W_92e48 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e4c : bv 32 := 0x0ce66463.
Lemma F_92e4c : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ee8 : word) = Some W_92e4c.
Proof. vm_refl. Qed.
Lemma D_92e4c : decode_any W_92e4c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e50 : bv 32 := 0x00b501a3.
Lemma F_92e50 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92eec : word) = Some W_92e50.
Proof. vm_refl. Qed.
Lemma D_92e50 : decode_any W_92e50 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e54 : bv 32 := 0x00900793.
Lemma F_92e54 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ef0 : word) = Some W_92e54.
Proof. vm_refl. Qed.
Lemma D_92e54 : decode_any W_92e54 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e58 : bv 32 := 0xfeb68e23.
Lemma F_92e58 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ef4 : word) = Some W_92e58.
Proof. vm_refl. Qed.
Lemma D_92e58 : decode_any W_92e58 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e5c : bv 32 := 0x0af66c63.
Lemma F_92e5c : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92ef8 : word) = Some W_92e5c.
Proof. vm_refl. Qed.
Lemma D_92e5c : decode_any W_92e5c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e60 : bv 32 := 0x40a006bb.
Lemma F_92e60 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92efc : word) = Some W_92e60.
Proof. vm_refl. Qed.
Lemma D_92e60 : decode_any W_92e60 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e64 : bv 32 := 0x03859813.
Lemma F_92e64 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f00 : word) = Some W_92e64.
Proof. vm_refl. Qed.
Lemma D_92e64 : decode_any W_92e64 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e68 : bv 32 := 0x101015b7.
Lemma F_92e68 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f04 : word) = Some W_92e68.
Proof. vm_refl. Qed.
Lemma D_92e68 : decode_any W_92e68 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e6c : bv 32 := 0x0036f693.
Lemma F_92e6c : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f08 : word) = Some W_92e6c.
Proof. vm_refl. Qed.
Lemma D_92e6c : decode_any W_92e6c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e70 : bv 32 := 0x00459713.
Lemma F_92e70 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f0c : word) = Some W_92e70.
Proof. vm_refl. Qed.
Lemma D_92e70 : decode_any W_92e70 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e74 : bv 32 := 0x40d60633.
Lemma F_92e74 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f10 : word) = Some W_92e74.
Proof. vm_refl. Qed.
Lemma D_92e74 : decode_any W_92e74 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e78 : bv 32 := 0x00d505b3.
Lemma F_92e78 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f14 : word) = Some W_92e78.
Proof. vm_refl. Qed.
Lemma D_92e78 : decode_any W_92e78 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e7c : bv 32 := 0x10070693.
Lemma F_92e7c : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f18 : word) = Some W_92e7c.
Proof. vm_refl. Qed.
Lemma D_92e7c : decode_any W_92e7c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e80 : bv 32 := 0xffc67713.
Lemma F_92e80 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f1c : word) = Some W_92e80.
Proof. vm_refl. Qed.
Lemma D_92e80 : decode_any W_92e80 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e84 : bv 32 := 0x02d83633.
Lemma F_92e84 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f20 : word) = Some W_92e84.
Proof. vm_refl. Qed.
Lemma D_92e84 : decode_any W_92e84 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e88 : bv 32 := 0x00c5a023.
Lemma F_92e88 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f24 : word) = Some W_92e88.
Proof. vm_refl. Qed.
Lemma D_92e88 : decode_any W_92e88 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e8c : bv 32 := 0x00e586b3.
Lemma F_92e8c : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f28 : word) = Some W_92e8c.
Proof. vm_refl. Qed.
Lemma D_92e8c : decode_any W_92e8c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e90 : bv 32 := 0xfec6ae23.
Lemma F_92e90 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f2c : word) = Some W_92e90.
Proof. vm_refl. Qed.
Lemma D_92e90 : decode_any W_92e90 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e94 : bv 32 := 0x08f76063.
Lemma F_92e94 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f30 : word) = Some W_92e94.
Proof. vm_refl. Qed.
Lemma D_92e94 : decode_any W_92e94 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e98 : bv 32 := 0x00c5a223.
Lemma F_92e98 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f34 : word) = Some W_92e98.
Proof. vm_refl. Qed.
Lemma D_92e98 : decode_any W_92e98 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e9c : bv 32 := 0x00c5a423.
Lemma F_92e9c : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f38 : word) = Some W_92e9c.
Proof. vm_refl. Qed.
Lemma D_92e9c : decode_any W_92e9c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ea0 : bv 32 := 0x01900793.
Lemma F_92ea0 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f3c : word) = Some W_92ea0.
Proof. vm_refl. Qed.
Lemma D_92ea0 : decode_any W_92ea0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ea4 : bv 32 := 0xfec6aa23.
Lemma F_92ea4 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f40 : word) = Some W_92ea4.
Proof. vm_refl. Qed.
Lemma D_92ea4 : decode_any W_92ea4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ea8 : bv 32 := 0xfec6ac23.
Lemma F_92ea8 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f44 : word) = Some W_92ea8.
Proof. vm_refl. Qed.
Lemma D_92ea8 : decode_any W_92ea8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_92eac : bv 32 := 0x06f76463.
Lemma F_92eac : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f48 : word) = Some W_92eac.
Proof. vm_refl. Qed.
Lemma D_92eac : decode_any W_92eac = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_92eb0 : bv 32 := 0x00c5a623.
Lemma F_92eb0 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f4c : word) = Some W_92eb0.
Proof. vm_refl. Qed.
Lemma D_92eb0 : decode_any W_92eb0 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92eb4 : bv 32 := 0x00c5a823.
Lemma F_92eb4 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f50 : word) = Some W_92eb4.
Proof. vm_refl. Qed.
Lemma D_92eb4 : decode_any W_92eb4 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_92eb8 : bv 32 := 0x00c5aa23.
Lemma F_92eb8 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f54 : word) = Some W_92eb8.
Proof. vm_refl. Qed.
Lemma D_92eb8 : decode_any W_92eb8 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ebc : bv 32 := 0x00c5ac23.
Lemma F_92ebc : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f58 : word) = Some W_92ebc.
Proof. vm_refl. Qed.
Lemma D_92ebc : decode_any W_92ebc = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ec0 : bv 32 := 0x0045f793.
Lemma F_92ec0 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f5c : word) = Some W_92ec0.
Proof. vm_refl. Qed.
Lemma D_92ec0 : decode_any W_92ec0 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ec4 : bv 32 := 0x02000813.
Lemma F_92ec4 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f60 : word) = Some W_92ec4.
Proof. vm_refl. Qed.
Lemma D_92ec4 : decode_any W_92ec4 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ec8 : bv 32 := 0x01878793.
Lemma F_92ec8 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f64 : word) = Some W_92ec8.
Proof. vm_refl. Qed.
Lemma D_92ec8 : decode_any W_92ec8 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ecc : bv 32 := 0x40f70733.
Lemma F_92ecc : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f68 : word) = Some W_92ecc.
Proof. vm_refl. Qed.
Lemma D_92ecc : decode_any W_92ecc = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ed0 : bv 32 := 0xfec6a223.
Lemma F_92ed0 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f6c : word) = Some W_92ed0.
Proof. vm_refl. Qed.
Lemma D_92ed0 : decode_any W_92ed0 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ed4 : bv 32 := 0xfec6a423.
Lemma F_92ed4 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f70 : word) = Some W_92ed4.
Proof. vm_refl. Qed.
Lemma D_92ed4 : decode_any W_92ed4 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ed8 : bv 32 := 0xfec6a623.
Lemma F_92ed8 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f74 : word) = Some W_92ed8.
Proof. vm_refl. Qed.
Lemma D_92ed8 : decode_any W_92ed8 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_92edc : bv 32 := 0xfec6a823.
Lemma F_92edc : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f78 : word) = Some W_92edc.
Proof. vm_refl. Qed.
Lemma D_92edc : decode_any W_92edc = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ee0 : bv 32 := 0x03076a63.
Lemma F_92ee0 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f7c : word) = Some W_92ee0.
Proof. vm_refl. Qed.
Lemma D_92ee0 : decode_any W_92ee0 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ee4 : bv 32 := 0x02061613.
Lemma F_92ee4 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f80 : word) = Some W_92ee4.
Proof. vm_refl. Qed.
Lemma D_92ee4 : decode_any W_92ee4 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ee8 : bv 32 := 0x00f585b3.
Lemma F_92ee8 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f84 : word) = Some W_92ee8.
Proof. vm_refl. Qed.
Lemma D_92ee8 : decode_any W_92ee8 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_92eec : bv 32 := 0x02065693.
Lemma F_92eec : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f88 : word) = Some W_92eec.
Proof. vm_refl. Qed.
Lemma D_92eec : decode_any W_92eec = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ef0 : bv 32 := 0x00d66633.
Lemma F_92ef0 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f8c : word) = Some W_92ef0.
Proof. vm_refl. Qed.
Lemma D_92ef0 : decode_any W_92ef0 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ef4 : bv 32 := 0x01f00693.
Lemma F_92ef4 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f90 : word) = Some W_92ef4.
Proof. vm_refl. Qed.
Lemma D_92ef4 : decode_any W_92ef4 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ef8 : bv 32 := 0x00c5b023.
Lemma F_92ef8 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f94 : word) = Some W_92ef8.
Proof. vm_refl. Qed.
Lemma D_92ef8 : decode_any W_92ef8 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92efc : bv 32 := 0x00c5b423.
Lemma F_92efc : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f98 : word) = Some W_92efc.
Proof. vm_refl. Qed.
Lemma D_92efc : decode_any W_92efc = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f00 : bv 32 := 0x00c5b823.
Lemma F_92f00 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92f9c : word) = Some W_92f00.
Proof. vm_refl. Qed.
Lemma D_92f00 : decode_any W_92f00 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f04 : bv 32 := 0x00c5bc23.
Lemma F_92f04 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92fa0 : word) = Some W_92f04.
Proof. vm_refl. Qed.
Lemma D_92f04 : decode_any W_92f04 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f08 : bv 32 := 0xfe070713.
Lemma F_92f08 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92fa4 : word) = Some W_92f08.
Proof. vm_refl. Qed.
Lemma D_92f08 : decode_any W_92f08 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f0c : bv 32 := 0x02058593.
Lemma F_92f0c : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92fa8 : word) = Some W_92f0c.
Proof. vm_refl. Qed.
Lemma D_92f0c : decode_any W_92f0c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f10 : bv 32 := 0xfee6e4e3.
Lemma F_92f10 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92fac : word) = Some W_92f10.
Proof. vm_refl. Qed.
Lemma D_92f10 : decode_any W_92f10 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f14 : bv 32 := 0x00008067.
Lemma F_92f14 : fetch_word Tgt_checksum_fuzzer_asan.M.loaded_segments (0x92fb0 : word) = Some W_92f14.
Proof. vm_refl. Qed.
Lemma D_92f14 : decode_any W_92f14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := Tgt_checksum_fuzzer_asan.M.loaded_segments.
Definition ms_base : Z := 0x92ebc%Z.
Definition Fo_000 := F_92e20.
Definition Do_000 := D_92e20.
Definition Fo_004 := F_92e24.
Definition Do_004 := D_92e24.
Definition Fo_008 := F_92e28.
Definition Do_008 := D_92e28.
Definition Fo_00c := F_92e2c.
Definition Do_00c := D_92e2c.
Definition Fo_010 := F_92e30.
Definition Do_010 := D_92e30.
Definition Fo_014 := F_92e34.
Definition Do_014 := D_92e34.
Definition Fo_018 := F_92e38.
Definition Do_018 := D_92e38.
Definition Fo_01c := F_92e3c.
Definition Do_01c := D_92e3c.
Definition Fo_020 := F_92e40.
Definition Do_020 := D_92e40.
Definition Fo_024 := F_92e44.
Definition Do_024 := D_92e44.
Definition Fo_028 := F_92e48.
Definition Do_028 := D_92e48.
Definition Fo_02c := F_92e4c.
Definition Do_02c := D_92e4c.
Definition Fo_030 := F_92e50.
Definition Do_030 := D_92e50.
Definition Fo_034 := F_92e54.
Definition Do_034 := D_92e54.
Definition Fo_038 := F_92e58.
Definition Do_038 := D_92e58.
Definition Fo_03c := F_92e5c.
Definition Do_03c := D_92e5c.
Definition Fo_040 := F_92e60.
Definition Do_040 := D_92e60.
Definition Fo_044 := F_92e64.
Definition Do_044 := D_92e64.
Definition Fo_048 := F_92e68.
Definition Do_048 := D_92e68.
Definition Fo_04c := F_92e6c.
Definition Do_04c := D_92e6c.
Definition Fo_050 := F_92e70.
Definition Do_050 := D_92e70.
Definition Fo_054 := F_92e74.
Definition Do_054 := D_92e74.
Definition Fo_058 := F_92e78.
Definition Do_058 := D_92e78.
Definition Fo_05c := F_92e7c.
Definition Do_05c := D_92e7c.
Definition Fo_060 := F_92e80.
Definition Do_060 := D_92e80.
Definition Fo_064 := F_92e84.
Definition Do_064 := D_92e84.
Definition Fo_068 := F_92e88.
Definition Do_068 := D_92e88.
Definition Fo_06c := F_92e8c.
Definition Do_06c := D_92e8c.
Definition Fo_070 := F_92e90.
Definition Do_070 := D_92e90.
Definition Fo_074 := F_92e94.
Definition Do_074 := D_92e94.
Definition Fo_078 := F_92e98.
Definition Do_078 := D_92e98.
Definition Fo_07c := F_92e9c.
Definition Do_07c := D_92e9c.
Definition Fo_080 := F_92ea0.
Definition Do_080 := D_92ea0.
Definition Fo_084 := F_92ea4.
Definition Do_084 := D_92ea4.
Definition Fo_088 := F_92ea8.
Definition Do_088 := D_92ea8.
Definition Fo_08c := F_92eac.
Definition Do_08c := D_92eac.
Definition Fo_090 := F_92eb0.
Definition Do_090 := D_92eb0.
Definition Fo_094 := F_92eb4.
Definition Do_094 := D_92eb4.
Definition Fo_098 := F_92eb8.
Definition Do_098 := D_92eb8.
Definition Fo_09c := F_92ebc.
Definition Do_09c := D_92ebc.
Definition Fo_0a0 := F_92ec0.
Definition Do_0a0 := D_92ec0.
Definition Fo_0a4 := F_92ec4.
Definition Do_0a4 := D_92ec4.
Definition Fo_0a8 := F_92ec8.
Definition Do_0a8 := D_92ec8.
Definition Fo_0ac := F_92ecc.
Definition Do_0ac := D_92ecc.
Definition Fo_0b0 := F_92ed0.
Definition Do_0b0 := D_92ed0.
Definition Fo_0b4 := F_92ed4.
Definition Do_0b4 := D_92ed4.
Definition Fo_0b8 := F_92ed8.
Definition Do_0b8 := D_92ed8.
Definition Fo_0bc := F_92edc.
Definition Do_0bc := D_92edc.
Definition Fo_0c0 := F_92ee0.
Definition Do_0c0 := D_92ee0.
Definition Fo_0c4 := F_92ee4.
Definition Do_0c4 := D_92ee4.
Definition Fo_0c8 := F_92ee8.
Definition Do_0c8 := D_92ee8.
Definition Fo_0cc := F_92eec.
Definition Do_0cc := D_92eec.
Definition Fo_0d0 := F_92ef0.
Definition Do_0d0 := D_92ef0.
Definition Fo_0d4 := F_92ef4.
Definition Do_0d4 := D_92ef4.
Definition Fo_0d8 := F_92ef8.
Definition Do_0d8 := D_92ef8.
Definition Fo_0dc := F_92efc.
Definition Do_0dc := D_92efc.
Definition Fo_0e0 := F_92f00.
Definition Do_0e0 := D_92f00.
Definition Fo_0e4 := F_92f04.
Definition Do_0e4 := D_92f04.
Definition Fo_0e8 := F_92f08.
Definition Do_0e8 := D_92f08.
Definition Fo_0ec := F_92f0c.
Definition Do_0ec := D_92f0c.
Definition Fo_0f0 := F_92f10.
Definition Do_0f0 := D_92f10.
Definition Fo_0f4 := F_92f14.
Definition Do_0f4 := D_92f14.
