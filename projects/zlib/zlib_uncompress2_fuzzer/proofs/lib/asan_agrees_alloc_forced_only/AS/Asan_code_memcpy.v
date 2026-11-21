(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c5e3c : bv 32 := 0x0035f693.
Lemma F_c5e3c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc63fc : word) = Some W_c5e3c.
Proof. vm_refl. Qed.
Lemma D_c5e3c : decode_any W_c5e3c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e40 : bv 32 := 0x10068863.
Lemma F_c5e40 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6400 : word) = Some W_c5e40.
Proof. vm_refl. Qed.
Lemma D_c5e40 : decode_any W_c5e40 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e44 : bv 32 := 0x02060e63.
Lemma F_c5e44 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6404 : word) = Some W_c5e44.
Proof. vm_refl. Qed.
Lemma D_c5e44 : decode_any W_c5e44 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e48 : bv 32 := 0x00158713.
Lemma F_c5e48 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6408 : word) = Some W_c5e48.
Proof. vm_refl. Qed.
Lemma D_c5e48 : decode_any W_c5e48 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e4c : bv 32 := 0x00100793.
Lemma F_c5e4c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc640c : word) = Some W_c5e4c.
Proof. vm_refl. Qed.
Lemma D_c5e4c : decode_any W_c5e4c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e50 : bv 32 := 0x00050693.
Lemma F_c5e50 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6410 : word) = Some W_c5e50.
Proof. vm_refl. Qed.
Lemma D_c5e50 : decode_any W_c5e50 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e54 : bv 32 := 0x0005c883.
Lemma F_c5e54 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6414 : word) = Some W_c5e54.
Proof. vm_refl. Qed.
Lemma D_c5e54 : decode_any W_c5e54 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e58 : bv 32 := 0x00060813.
Lemma F_c5e58 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6418 : word) = Some W_c5e58.
Proof. vm_refl. Qed.
Lemma D_c5e58 : decode_any W_c5e58 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e5c : bv 32 := 0x00158593.
Lemma F_c5e5c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc641c : word) = Some W_c5e5c.
Proof. vm_refl. Qed.
Lemma D_c5e5c : decode_any W_c5e5c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e60 : bv 32 := 0x00377293.
Lemma F_c5e60 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6420 : word) = Some W_c5e60.
Proof. vm_refl. Qed.
Lemma D_c5e60 : decode_any W_c5e60 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e64 : bv 32 := 0x01168023.
Lemma F_c5e64 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6424 : word) = Some W_c5e64.
Proof. vm_refl. Qed.
Lemma D_c5e64 : decode_any W_c5e64 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e68 : bv 32 := 0x00168693.
Lemma F_c5e68 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6428 : word) = Some W_c5e68.
Proof. vm_refl. Qed.
Lemma D_c5e68 : decode_any W_c5e68 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e6c : bv 32 := 0xfff60613.
Lemma F_c5e6c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc642c : word) = Some W_c5e6c.
Proof. vm_refl. Qed.
Lemma D_c5e6c : decode_any W_c5e6c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e70 : bv 32 := 0x00028a63.
Lemma F_c5e70 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6430 : word) = Some W_c5e70.
Proof. vm_refl. Qed.
Lemma D_c5e70 : decode_any W_c5e70 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e74 : bv 32 := 0x00170713.
Lemma F_c5e74 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6434 : word) = Some W_c5e74.
Proof. vm_refl. Qed.
Lemma D_c5e74 : decode_any W_c5e74 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e78 : bv 32 := 0xfcf81ee3.
Lemma F_c5e78 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6438 : word) = Some W_c5e78.
Proof. vm_refl. Qed.
Lemma D_c5e78 : decode_any W_c5e78 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e7c : bv 32 := 0x0080006f.
Lemma F_c5e7c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc643c : word) = Some W_c5e7c.
Proof. vm_refl. Qed.
Lemma D_c5e7c : decode_any W_c5e7c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e80 : bv 32 := 0x00050693.
Lemma F_c5e80 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6440 : word) = Some W_c5e80.
Proof. vm_refl. Qed.
Lemma D_c5e80 : decode_any W_c5e80 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e84 : bv 32 := 0x0036f793.
Lemma F_c5e84 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6444 : word) = Some W_c5e84.
Proof. vm_refl. Qed.
Lemma D_c5e84 : decode_any W_c5e84 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e88 : bv 32 := 0x0c078a63.
Lemma F_c5e88 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6448 : word) = Some W_c5e88.
Proof. vm_refl. Qed.
Lemma D_c5e88 : decode_any W_c5e88 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e8c : bv 32 := 0x02000713.
Lemma F_c5e8c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc644c : word) = Some W_c5e8c.
Proof. vm_refl. Qed.
Lemma D_c5e8c : decode_any W_c5e8c = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e90 : bv 32 := 0x02e67063.
Lemma F_c5e90 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6450 : word) = Some W_c5e90.
Proof. vm_refl. Qed.
Lemma D_c5e90 : decode_any W_c5e90 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e94 : bv 32 := 0x01000713.
Lemma F_c5e94 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6454 : word) = Some W_c5e94.
Proof. vm_refl. Qed.
Lemma D_c5e94 : decode_any W_c5e94 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e98 : bv 32 := 0x24e67863.
Lemma F_c5e98 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6458 : word) = Some W_c5e98.
Proof. vm_refl. Qed.
Lemma D_c5e98 : decode_any W_c5e98 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e9c : bv 32 := 0x00867713.
Lemma F_c5e9c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc645c : word) = Some W_c5e9c.
Proof. vm_refl. Qed.
Lemma D_c5e9c : decode_any W_c5e9c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ea0 : bv 32 := 0x2c071e63.
Lemma F_c5ea0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6460 : word) = Some W_c5ea0.
Proof. vm_refl. Qed.
Lemma D_c5ea0 : decode_any W_c5ea0 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ea4 : bv 32 := 0x00467713.
Lemma F_c5ea4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6464 : word) = Some W_c5ea4.
Proof. vm_refl. Qed.
Lemma D_c5ea4 : decode_any W_c5ea4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ea8 : bv 32 := 0x32071463.
Lemma F_c5ea8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6468 : word) = Some W_c5ea8.
Proof. vm_refl. Qed.
Lemma D_c5ea8 : decode_any W_c5ea8 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5eac : bv 32 := 0x3500006f.
Lemma F_c5eac : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc646c : word) = Some W_c5eac.
Proof. vm_refl. Qed.
Lemma D_c5eac : decode_any W_c5eac = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5eb0 : bv 32 := 0x0005a703.
Lemma F_c5eb0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6470 : word) = Some W_c5eb0.
Proof. vm_refl. Qed.
Lemma D_c5eb0 : decode_any W_c5eb0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5eb4 : bv 32 := 0x00300813.
Lemma F_c5eb4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6474 : word) = Some W_c5eb4.
Proof. vm_refl. Qed.
Lemma D_c5eb4 : decode_any W_c5eb4 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5eb8 : bv 32 := 0x11078e63.
Lemma F_c5eb8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6478 : word) = Some W_c5eb8.
Proof. vm_refl. Qed.
Lemma D_c5eb8 : decode_any W_c5eb8 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ebc : bv 32 := 0x00200813.
Lemma F_c5ebc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc647c : word) = Some W_c5ebc.
Proof. vm_refl. Qed.
Lemma D_c5ebc : decode_any W_c5ebc = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ec0 : bv 32 := 0x19079c63.
Lemma F_c5ec0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6480 : word) = Some W_c5ec0.
Proof. vm_refl. Qed.
Lemma D_c5ec0 : decode_any W_c5ec0 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ec4 : bv 32 := 0x00875793.
Lemma F_c5ec4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6484 : word) = Some W_c5ec4.
Proof. vm_refl. Qed.
Lemma D_c5ec4 : decode_any W_c5ec4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ec8 : bv 32 := 0xffe60613.
Lemma F_c5ec8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6488 : word) = Some W_c5ec8.
Proof. vm_refl. Qed.
Lemma D_c5ec8 : decode_any W_c5ec8 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ecc : bv 32 := 0x00e68023.
Lemma F_c5ecc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc648c : word) = Some W_c5ecc.
Proof. vm_refl. Qed.
Lemma D_c5ecc : decode_any W_c5ecc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ed0 : bv 32 := 0x00f680a3.
Lemma F_c5ed0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6490 : word) = Some W_c5ed0.
Proof. vm_refl. Qed.
Lemma D_c5ed0 : decode_any W_c5ed0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ed4 : bv 32 := 0x00268693.
Lemma F_c5ed4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6494 : word) = Some W_c5ed4.
Proof. vm_refl. Qed.
Lemma D_c5ed4 : decode_any W_c5ed4 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ed8 : bv 32 := 0x01058593.
Lemma F_c5ed8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6498 : word) = Some W_c5ed8.
Proof. vm_refl. Qed.
Lemma D_c5ed8 : decode_any W_c5ed8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5edc : bv 32 := 0x01100793.
Lemma F_c5edc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc649c : word) = Some W_c5edc.
Proof. vm_refl. Qed.
Lemma D_c5edc : decode_any W_c5edc = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ee0 : bv 32 := 0x0107581b.
Lemma F_c5ee0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64a0 : word) = Some W_c5ee0.
Proof. vm_refl. Qed.
Lemma D_c5ee0 : decode_any W_c5ee0 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ee4 : bv 32 := 0xff45a883.
Lemma F_c5ee4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64a4 : word) = Some W_c5ee4.
Proof. vm_refl. Qed.
Lemma D_c5ee4 : decode_any W_c5ee4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ee8 : bv 32 := 0xff85a283.
Lemma F_c5ee8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64a8 : word) = Some W_c5ee8.
Proof. vm_refl. Qed.
Lemma D_c5ee8 : decode_any W_c5ee8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5eec : bv 32 := 0xffc5a303.
Lemma F_c5eec : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64ac : word) = Some W_c5eec.
Proof. vm_refl. Qed.
Lemma D_c5eec : decode_any W_c5eec = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ef0 : bv 32 := 0x0005a703.
Lemma F_c5ef0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64b0 : word) = Some W_c5ef0.
Proof. vm_refl. Qed.
Lemma D_c5ef0 : decode_any W_c5ef0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ef4 : bv 32 := 0x01089393.
Lemma F_c5ef4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64b4 : word) = Some W_c5ef4.
Proof. vm_refl. Qed.
Lemma D_c5ef4 : decode_any W_c5ef4 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ef8 : bv 32 := 0x0108d89b.
Lemma F_c5ef8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64b8 : word) = Some W_c5ef8.
Proof. vm_refl. Qed.
Lemma D_c5ef8 : decode_any W_c5ef8 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5efc : bv 32 := 0x0103e833.
Lemma F_c5efc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64bc : word) = Some W_c5efc.
Proof. vm_refl. Qed.
Lemma D_c5efc : decode_any W_c5efc = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f00 : bv 32 := 0x01029393.
Lemma F_c5f00 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64c0 : word) = Some W_c5f00.
Proof. vm_refl. Qed.
Lemma D_c5f00 : decode_any W_c5f00 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f04 : bv 32 := 0x0102d29b.
Lemma F_c5f04 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64c4 : word) = Some W_c5f04.
Proof. vm_refl. Qed.
Lemma D_c5f04 : decode_any W_c5f04 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f08 : bv 32 := 0x0113e8b3.
Lemma F_c5f08 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64c8 : word) = Some W_c5f08.
Proof. vm_refl. Qed.
Lemma D_c5f08 : decode_any W_c5f08 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f0c : bv 32 := 0x01031393.
Lemma F_c5f0c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64cc : word) = Some W_c5f0c.
Proof. vm_refl. Qed.
Lemma D_c5f0c : decode_any W_c5f0c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f10 : bv 32 := 0x0103531b.
Lemma F_c5f10 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64d0 : word) = Some W_c5f10.
Proof. vm_refl. Qed.
Lemma D_c5f10 : decode_any W_c5f10 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f14 : bv 32 := 0x0053e2b3.
Lemma F_c5f14 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64d4 : word) = Some W_c5f14.
Proof. vm_refl. Qed.
Lemma D_c5f14 : decode_any W_c5f14 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f18 : bv 32 := 0x01071393.
Lemma F_c5f18 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64d8 : word) = Some W_c5f18.
Proof. vm_refl. Qed.
Lemma D_c5f18 : decode_any W_c5f18 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f1c : bv 32 := 0x0063e333.
Lemma F_c5f1c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64dc : word) = Some W_c5f1c.
Proof. vm_refl. Qed.
Lemma D_c5f1c : decode_any W_c5f1c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f20 : bv 32 := 0xff060613.
Lemma F_c5f20 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64e0 : word) = Some W_c5f20.
Proof. vm_refl. Qed.
Lemma D_c5f20 : decode_any W_c5f20 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f24 : bv 32 := 0x0106a023.
Lemma F_c5f24 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64e4 : word) = Some W_c5f24.
Proof. vm_refl. Qed.
Lemma D_c5f24 : decode_any W_c5f24 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f28 : bv 32 := 0x0116a223.
Lemma F_c5f28 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64e8 : word) = Some W_c5f28.
Proof. vm_refl. Qed.
Lemma D_c5f28 : decode_any W_c5f28 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f2c : bv 32 := 0x0056a423.
Lemma F_c5f2c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64ec : word) = Some W_c5f2c.
Proof. vm_refl. Qed.
Lemma D_c5f2c : decode_any W_c5f2c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f30 : bv 32 := 0x0066a623.
Lemma F_c5f30 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64f0 : word) = Some W_c5f30.
Proof. vm_refl. Qed.
Lemma D_c5f30 : decode_any W_c5f30 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f34 : bv 32 := 0x01068693.
Lemma F_c5f34 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64f4 : word) = Some W_c5f34.
Proof. vm_refl. Qed.
Lemma D_c5f34 : decode_any W_c5f34 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f38 : bv 32 := 0x01058593.
Lemma F_c5f38 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64f8 : word) = Some W_c5f38.
Proof. vm_refl. Qed.
Lemma D_c5f38 : decode_any W_c5f38 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f3c : bv 32 := 0xfac7e2e3.
Lemma F_c5f3c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc64fc : word) = Some W_c5f3c.
Proof. vm_refl. Qed.
Lemma D_c5f3c : decode_any W_c5f3c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f40 : bv 32 := 0xff258593.
Lemma F_c5f40 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6500 : word) = Some W_c5f40.
Proof. vm_refl. Qed.
Lemma D_c5f40 : decode_any W_c5f40 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f44 : bv 32 := 0x01000713.
Lemma F_c5f44 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6504 : word) = Some W_c5f44.
Proof. vm_refl. Qed.
Lemma D_c5f44 : decode_any W_c5f44 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f48 : bv 32 := 0xf4e66ae3.
Lemma F_c5f48 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6508 : word) = Some W_c5f48.
Proof. vm_refl. Qed.
Lemma D_c5f48 : decode_any W_c5f48 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f4c : bv 32 := 0x19c0006f.
Lemma F_c5f4c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc650c : word) = Some W_c5f4c.
Proof. vm_refl. Qed.
Lemma D_c5f4c : decode_any W_c5f4c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f50 : bv 32 := 0x00050693.
Lemma F_c5f50 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6510 : word) = Some W_c5f50.
Proof. vm_refl. Qed.
Lemma D_c5f50 : decode_any W_c5f50 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f54 : bv 32 := 0x00357793.
Lemma F_c5f54 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6514 : word) = Some W_c5f54.
Proof. vm_refl. Qed.
Lemma D_c5f54 : decode_any W_c5f54 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f58 : bv 32 := 0xf2079ae3.
Lemma F_c5f58 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6518 : word) = Some W_c5f58.
Proof. vm_refl. Qed.
Lemma D_c5f58 : decode_any W_c5f58 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f5c : bv 32 := 0x01000713.
Lemma F_c5f5c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc651c : word) = Some W_c5f5c.
Proof. vm_refl. Qed.
Lemma D_c5f5c : decode_any W_c5f5c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f60 : bv 32 := 0x02e66c63.
Lemma F_c5f60 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6520 : word) = Some W_c5f60.
Proof. vm_refl. Qed.
Lemma D_c5f60 : decode_any W_c5f60 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f64 : bv 32 := 0x00f00713.
Lemma F_c5f64 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6524 : word) = Some W_c5f64.
Proof. vm_refl. Qed.
Lemma D_c5f64 : decode_any W_c5f64 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f68 : bv 32 := 0x0005a783.
Lemma F_c5f68 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6528 : word) = Some W_c5f68.
Proof. vm_refl. Qed.
Lemma D_c5f68 : decode_any W_c5f68 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f6c : bv 32 := 0x0045a803.
Lemma F_c5f6c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc652c : word) = Some W_c5f6c.
Proof. vm_refl. Qed.
Lemma D_c5f6c : decode_any W_c5f6c = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f70 : bv 32 := 0x0085a883.
Lemma F_c5f70 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6530 : word) = Some W_c5f70.
Proof. vm_refl. Qed.
Lemma D_c5f70 : decode_any W_c5f70 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f74 : bv 32 := 0x00c5a283.
Lemma F_c5f74 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6534 : word) = Some W_c5f74.
Proof. vm_refl. Qed.
Lemma D_c5f74 : decode_any W_c5f74 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f78 : bv 32 := 0x01058593.
Lemma F_c5f78 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6538 : word) = Some W_c5f78.
Proof. vm_refl. Qed.
Lemma D_c5f78 : decode_any W_c5f78 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f7c : bv 32 := 0xff060613.
Lemma F_c5f7c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc653c : word) = Some W_c5f7c.
Proof. vm_refl. Qed.
Lemma D_c5f7c : decode_any W_c5f7c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f80 : bv 32 := 0x00f6a023.
Lemma F_c5f80 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6540 : word) = Some W_c5f80.
Proof. vm_refl. Qed.
Lemma D_c5f80 : decode_any W_c5f80 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f84 : bv 32 := 0x0106a223.
Lemma F_c5f84 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6544 : word) = Some W_c5f84.
Proof. vm_refl. Qed.
Lemma D_c5f84 : decode_any W_c5f84 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f88 : bv 32 := 0x0116a423.
Lemma F_c5f88 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6548 : word) = Some W_c5f88.
Proof. vm_refl. Qed.
Lemma D_c5f88 : decode_any W_c5f88 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f8c : bv 32 := 0x0056a623.
Lemma F_c5f8c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc654c : word) = Some W_c5f8c.
Proof. vm_refl. Qed.
Lemma D_c5f8c : decode_any W_c5f8c = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f90 : bv 32 := 0x01068693.
Lemma F_c5f90 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6550 : word) = Some W_c5f90.
Proof. vm_refl. Qed.
Lemma D_c5f90 : decode_any W_c5f90 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f94 : bv 32 := 0xfcc76ae3.
Lemma F_c5f94 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6554 : word) = Some W_c5f94.
Proof. vm_refl. Qed.
Lemma D_c5f94 : decode_any W_c5f94 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f98 : bv 32 := 0x00800713.
Lemma F_c5f98 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6558 : word) = Some W_c5f98.
Proof. vm_refl. Qed.
Lemma D_c5f98 : decode_any W_c5f98 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f9c : bv 32 := 0x00e66e63.
Lemma F_c5f9c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc655c : word) = Some W_c5f9c.
Proof. vm_refl. Qed.
Lemma D_c5f9c : decode_any W_c5f9c = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fa0 : bv 32 := 0x0005a703.
Lemma F_c5fa0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6560 : word) = Some W_c5fa0.
Proof. vm_refl. Qed.
Lemma D_c5fa0 : decode_any W_c5fa0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fa4 : bv 32 := 0x0045a783.
Lemma F_c5fa4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6564 : word) = Some W_c5fa4.
Proof. vm_refl. Qed.
Lemma D_c5fa4 : decode_any W_c5fa4 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fa8 : bv 32 := 0x00e6a023.
Lemma F_c5fa8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6568 : word) = Some W_c5fa8.
Proof. vm_refl. Qed.
Lemma D_c5fa8 : decode_any W_c5fa8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fac : bv 32 := 0x00f6a223.
Lemma F_c5fac : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc656c : word) = Some W_c5fac.
Proof. vm_refl. Qed.
Lemma D_c5fac : decode_any W_c5fac = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fb0 : bv 32 := 0x00868693.
Lemma F_c5fb0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6570 : word) = Some W_c5fb0.
Proof. vm_refl. Qed.
Lemma D_c5fb0 : decode_any W_c5fb0 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fb4 : bv 32 := 0x00858593.
Lemma F_c5fb4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6574 : word) = Some W_c5fb4.
Proof. vm_refl. Qed.
Lemma D_c5fb4 : decode_any W_c5fb4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fb8 : bv 32 := 0x00467713.
Lemma F_c5fb8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6578 : word) = Some W_c5fb8.
Proof. vm_refl. Qed.
Lemma D_c5fb8 : decode_any W_c5fb8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fbc : bv 32 := 0x24070063.
Lemma F_c5fbc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc657c : word) = Some W_c5fbc.
Proof. vm_refl. Qed.
Lemma D_c5fbc : decode_any W_c5fbc = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fc0 : bv 32 := 0x0005a703.
Lemma F_c5fc0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6580 : word) = Some W_c5fc0.
Proof. vm_refl. Qed.
Lemma D_c5fc0 : decode_any W_c5fc0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fc4 : bv 32 := 0x00458593.
Lemma F_c5fc4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6584 : word) = Some W_c5fc4.
Proof. vm_refl. Qed.
Lemma D_c5fc4 : decode_any W_c5fc4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fc8 : bv 32 := 0x00e6a023.
Lemma F_c5fc8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6588 : word) = Some W_c5fc8.
Proof. vm_refl. Qed.
Lemma D_c5fc8 : decode_any W_c5fc8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fcc : bv 32 := 0x00468693.
Lemma F_c5fcc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc658c : word) = Some W_c5fcc.
Proof. vm_refl. Qed.
Lemma D_c5fcc : decode_any W_c5fcc = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fd0 : bv 32 := 0x22c0006f.
Lemma F_c5fd0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6590 : word) = Some W_c5fd0.
Proof. vm_refl. Qed.
Lemma D_c5fd0 : decode_any W_c5fd0 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fd4 : bv 32 := 0x00e68023.
Lemma F_c5fd4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6594 : word) = Some W_c5fd4.
Proof. vm_refl. Qed.
Lemma D_c5fd4 : decode_any W_c5fd4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fd8 : bv 32 := 0x00168693.
Lemma F_c5fd8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6598 : word) = Some W_c5fd8.
Proof. vm_refl. Qed.
Lemma D_c5fd8 : decode_any W_c5fd8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fdc : bv 32 := 0xfff60613.
Lemma F_c5fdc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc659c : word) = Some W_c5fdc.
Proof. vm_refl. Qed.
Lemma D_c5fdc : decode_any W_c5fdc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fe0 : bv 32 := 0x01058593.
Lemma F_c5fe0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65a0 : word) = Some W_c5fe0.
Proof. vm_refl. Qed.
Lemma D_c5fe0 : decode_any W_c5fe0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fe4 : bv 32 := 0x01200793.
Lemma F_c5fe4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65a4 : word) = Some W_c5fe4.
Proof. vm_refl. Qed.
Lemma D_c5fe4 : decode_any W_c5fe4 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fe8 : bv 32 := 0x0087581b.
Lemma F_c5fe8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65a8 : word) = Some W_c5fe8.
Proof. vm_refl. Qed.
Lemma D_c5fe8 : decode_any W_c5fe8 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fec : bv 32 := 0xff45a883.
Lemma F_c5fec : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65ac : word) = Some W_c5fec.
Proof. vm_refl. Qed.
Lemma D_c5fec : decode_any W_c5fec = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ff0 : bv 32 := 0xff85a283.
Lemma F_c5ff0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65b0 : word) = Some W_c5ff0.
Proof. vm_refl. Qed.
Lemma D_c5ff0 : decode_any W_c5ff0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ff4 : bv 32 := 0xffc5a303.
Lemma F_c5ff4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65b4 : word) = Some W_c5ff4.
Proof. vm_refl. Qed.
Lemma D_c5ff4 : decode_any W_c5ff4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ff8 : bv 32 := 0x0005a703.
Lemma F_c5ff8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65b8 : word) = Some W_c5ff8.
Proof. vm_refl. Qed.
Lemma D_c5ff8 : decode_any W_c5ff8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ffc : bv 32 := 0x01889393.
Lemma F_c5ffc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65bc : word) = Some W_c5ffc.
Proof. vm_refl. Qed.
Lemma D_c5ffc : decode_any W_c5ffc = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6000 : bv 32 := 0x0088d89b.
Lemma F_c6000 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65c0 : word) = Some W_c6000.
Proof. vm_refl. Qed.
Lemma D_c6000 : decode_any W_c6000 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6004 : bv 32 := 0x0103e833.
Lemma F_c6004 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65c4 : word) = Some W_c6004.
Proof. vm_refl. Qed.
Lemma D_c6004 : decode_any W_c6004 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6008 : bv 32 := 0x01829393.
Lemma F_c6008 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65c8 : word) = Some W_c6008.
Proof. vm_refl. Qed.
Lemma D_c6008 : decode_any W_c6008 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c600c : bv 32 := 0x0082d29b.
Lemma F_c600c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65cc : word) = Some W_c600c.
Proof. vm_refl. Qed.
Lemma D_c600c : decode_any W_c600c = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6010 : bv 32 := 0x0113e8b3.
Lemma F_c6010 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65d0 : word) = Some W_c6010.
Proof. vm_refl. Qed.
Lemma D_c6010 : decode_any W_c6010 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6014 : bv 32 := 0x01831393.
Lemma F_c6014 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65d4 : word) = Some W_c6014.
Proof. vm_refl. Qed.
Lemma D_c6014 : decode_any W_c6014 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6018 : bv 32 := 0x0083531b.
Lemma F_c6018 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65d8 : word) = Some W_c6018.
Proof. vm_refl. Qed.
Lemma D_c6018 : decode_any W_c6018 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c601c : bv 32 := 0x0053e2b3.
Lemma F_c601c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65dc : word) = Some W_c601c.
Proof. vm_refl. Qed.
Lemma D_c601c : decode_any W_c601c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6020 : bv 32 := 0x01871393.
Lemma F_c6020 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65e0 : word) = Some W_c6020.
Proof. vm_refl. Qed.
Lemma D_c6020 : decode_any W_c6020 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6024 : bv 32 := 0x0063e333.
Lemma F_c6024 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65e4 : word) = Some W_c6024.
Proof. vm_refl. Qed.
Lemma D_c6024 : decode_any W_c6024 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6028 : bv 32 := 0xff060613.
Lemma F_c6028 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65e8 : word) = Some W_c6028.
Proof. vm_refl. Qed.
Lemma D_c6028 : decode_any W_c6028 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c602c : bv 32 := 0x0106a023.
Lemma F_c602c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65ec : word) = Some W_c602c.
Proof. vm_refl. Qed.
Lemma D_c602c : decode_any W_c602c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6030 : bv 32 := 0x0116a223.
Lemma F_c6030 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65f0 : word) = Some W_c6030.
Proof. vm_refl. Qed.
Lemma D_c6030 : decode_any W_c6030 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6034 : bv 32 := 0x0056a423.
Lemma F_c6034 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65f4 : word) = Some W_c6034.
Proof. vm_refl. Qed.
Lemma D_c6034 : decode_any W_c6034 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6038 : bv 32 := 0x0066a623.
Lemma F_c6038 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65f8 : word) = Some W_c6038.
Proof. vm_refl. Qed.
Lemma D_c6038 : decode_any W_c6038 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c603c : bv 32 := 0x01068693.
Lemma F_c603c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc65fc : word) = Some W_c603c.
Proof. vm_refl. Qed.
Lemma D_c603c : decode_any W_c603c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6040 : bv 32 := 0x01058593.
Lemma F_c6040 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6600 : word) = Some W_c6040.
Proof. vm_refl. Qed.
Lemma D_c6040 : decode_any W_c6040 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6044 : bv 32 := 0xfac7e2e3.
Lemma F_c6044 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6604 : word) = Some W_c6044.
Proof. vm_refl. Qed.
Lemma D_c6044 : decode_any W_c6044 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6048 : bv 32 := 0xff158593.
Lemma F_c6048 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6608 : word) = Some W_c6048.
Proof. vm_refl. Qed.
Lemma D_c6048 : decode_any W_c6048 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_c604c : bv 32 := 0x01000713.
Lemma F_c604c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc660c : word) = Some W_c604c.
Proof. vm_refl. Qed.
Lemma D_c604c : decode_any W_c604c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6050 : bv 32 := 0xe4e666e3.
Lemma F_c6050 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6610 : word) = Some W_c6050.
Proof. vm_refl. Qed.
Lemma D_c6050 : decode_any W_c6050 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6054 : bv 32 := 0x0940006f.
Lemma F_c6054 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6614 : word) = Some W_c6054.
Proof. vm_refl. Qed.
Lemma D_c6054 : decode_any W_c6054 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6058 : bv 32 := 0x00875793.
Lemma F_c6058 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6618 : word) = Some W_c6058.
Proof. vm_refl. Qed.
Lemma D_c6058 : decode_any W_c6058 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c605c : bv 32 := 0x01075813.
Lemma F_c605c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc661c : word) = Some W_c605c.
Proof. vm_refl. Qed.
Lemma D_c605c : decode_any W_c605c = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6060 : bv 32 := 0xffd60613.
Lemma F_c6060 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6620 : word) = Some W_c6060.
Proof. vm_refl. Qed.
Lemma D_c6060 : decode_any W_c6060 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6064 : bv 32 := 0x00e68023.
Lemma F_c6064 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6624 : word) = Some W_c6064.
Proof. vm_refl. Qed.
Lemma D_c6064 : decode_any W_c6064 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6068 : bv 32 := 0x00f680a3.
Lemma F_c6068 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6628 : word) = Some W_c6068.
Proof. vm_refl. Qed.
Lemma D_c6068 : decode_any W_c6068 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c606c : bv 32 := 0x01068123.
Lemma F_c606c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc662c : word) = Some W_c606c.
Proof. vm_refl. Qed.
Lemma D_c606c : decode_any W_c606c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6070 : bv 32 := 0x00368693.
Lemma F_c6070 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6630 : word) = Some W_c6070.
Proof. vm_refl. Qed.
Lemma D_c6070 : decode_any W_c6070 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6074 : bv 32 := 0x01058593.
Lemma F_c6074 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6634 : word) = Some W_c6074.
Proof. vm_refl. Qed.
Lemma D_c6074 : decode_any W_c6074 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6078 : bv 32 := 0x01000793.
Lemma F_c6078 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6638 : word) = Some W_c6078.
Proof. vm_refl. Qed.
Lemma D_c6078 : decode_any W_c6078 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c607c : bv 32 := 0x0187581b.
Lemma F_c607c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc663c : word) = Some W_c607c.
Proof. vm_refl. Qed.
Lemma D_c607c : decode_any W_c607c = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6080 : bv 32 := 0xff45a883.
Lemma F_c6080 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6640 : word) = Some W_c6080.
Proof. vm_refl. Qed.
Lemma D_c6080 : decode_any W_c6080 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6084 : bv 32 := 0xff85a283.
Lemma F_c6084 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6644 : word) = Some W_c6084.
Proof. vm_refl. Qed.
Lemma D_c6084 : decode_any W_c6084 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6088 : bv 32 := 0xffc5a303.
Lemma F_c6088 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6648 : word) = Some W_c6088.
Proof. vm_refl. Qed.
Lemma D_c6088 : decode_any W_c6088 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c608c : bv 32 := 0x0005a703.
Lemma F_c608c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc664c : word) = Some W_c608c.
Proof. vm_refl. Qed.
Lemma D_c608c : decode_any W_c608c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6090 : bv 32 := 0x00889393.
Lemma F_c6090 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6650 : word) = Some W_c6090.
Proof. vm_refl. Qed.
Lemma D_c6090 : decode_any W_c6090 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6094 : bv 32 := 0x0188d89b.
Lemma F_c6094 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6654 : word) = Some W_c6094.
Proof. vm_refl. Qed.
Lemma D_c6094 : decode_any W_c6094 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6098 : bv 32 := 0x0103e833.
Lemma F_c6098 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6658 : word) = Some W_c6098.
Proof. vm_refl. Qed.
Lemma D_c6098 : decode_any W_c6098 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c609c : bv 32 := 0x00829393.
Lemma F_c609c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc665c : word) = Some W_c609c.
Proof. vm_refl. Qed.
Lemma D_c609c : decode_any W_c609c = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60a0 : bv 32 := 0x0182d29b.
Lemma F_c60a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6660 : word) = Some W_c60a0.
Proof. vm_refl. Qed.
Lemma D_c60a0 : decode_any W_c60a0 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60a4 : bv 32 := 0x0113e8b3.
Lemma F_c60a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6664 : word) = Some W_c60a4.
Proof. vm_refl. Qed.
Lemma D_c60a4 : decode_any W_c60a4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60a8 : bv 32 := 0x00831393.
Lemma F_c60a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6668 : word) = Some W_c60a8.
Proof. vm_refl. Qed.
Lemma D_c60a8 : decode_any W_c60a8 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60ac : bv 32 := 0x0183531b.
Lemma F_c60ac : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc666c : word) = Some W_c60ac.
Proof. vm_refl. Qed.
Lemma D_c60ac : decode_any W_c60ac = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60b0 : bv 32 := 0x0053e2b3.
Lemma F_c60b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6670 : word) = Some W_c60b0.
Proof. vm_refl. Qed.
Lemma D_c60b0 : decode_any W_c60b0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60b4 : bv 32 := 0x00871393.
Lemma F_c60b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6674 : word) = Some W_c60b4.
Proof. vm_refl. Qed.
Lemma D_c60b4 : decode_any W_c60b4 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60b8 : bv 32 := 0x0063e333.
Lemma F_c60b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6678 : word) = Some W_c60b8.
Proof. vm_refl. Qed.
Lemma D_c60b8 : decode_any W_c60b8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60bc : bv 32 := 0xff060613.
Lemma F_c60bc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc667c : word) = Some W_c60bc.
Proof. vm_refl. Qed.
Lemma D_c60bc : decode_any W_c60bc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60c0 : bv 32 := 0x0106a023.
Lemma F_c60c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6680 : word) = Some W_c60c0.
Proof. vm_refl. Qed.
Lemma D_c60c0 : decode_any W_c60c0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60c4 : bv 32 := 0x0116a223.
Lemma F_c60c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6684 : word) = Some W_c60c4.
Proof. vm_refl. Qed.
Lemma D_c60c4 : decode_any W_c60c4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60c8 : bv 32 := 0x0056a423.
Lemma F_c60c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6688 : word) = Some W_c60c8.
Proof. vm_refl. Qed.
Lemma D_c60c8 : decode_any W_c60c8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60cc : bv 32 := 0x0066a623.
Lemma F_c60cc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc668c : word) = Some W_c60cc.
Proof. vm_refl. Qed.
Lemma D_c60cc : decode_any W_c60cc = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60d0 : bv 32 := 0x01068693.
Lemma F_c60d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6690 : word) = Some W_c60d0.
Proof. vm_refl. Qed.
Lemma D_c60d0 : decode_any W_c60d0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60d4 : bv 32 := 0x01058593.
Lemma F_c60d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6694 : word) = Some W_c60d4.
Proof. vm_refl. Qed.
Lemma D_c60d4 : decode_any W_c60d4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60d8 : bv 32 := 0xfac7e2e3.
Lemma F_c60d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6698 : word) = Some W_c60d8.
Proof. vm_refl. Qed.
Lemma D_c60d8 : decode_any W_c60d8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60dc : bv 32 := 0xff358593.
Lemma F_c60dc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc669c : word) = Some W_c60dc.
Proof. vm_refl. Qed.
Lemma D_c60dc : decode_any W_c60dc = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60e0 : bv 32 := 0x01000713.
Lemma F_c60e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66a0 : word) = Some W_c60e0.
Proof. vm_refl. Qed.
Lemma D_c60e0 : decode_any W_c60e0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60e4 : bv 32 := 0xdae66ce3.
Lemma F_c60e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66a4 : word) = Some W_c60e4.
Proof. vm_refl. Qed.
Lemma D_c60e4 : decode_any W_c60e4 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60e8 : bv 32 := 0x0005c703.
Lemma F_c60e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66a8 : word) = Some W_c60e8.
Proof. vm_refl. Qed.
Lemma D_c60e8 : decode_any W_c60e8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60ec : bv 32 := 0x0015c783.
Lemma F_c60ec : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66ac : word) = Some W_c60ec.
Proof. vm_refl. Qed.
Lemma D_c60ec : decode_any W_c60ec = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60f0 : bv 32 := 0x0025c803.
Lemma F_c60f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66b0 : word) = Some W_c60f0.
Proof. vm_refl. Qed.
Lemma D_c60f0 : decode_any W_c60f0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60f4 : bv 32 := 0x0035c883.
Lemma F_c60f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66b4 : word) = Some W_c60f4.
Proof. vm_refl. Qed.
Lemma D_c60f4 : decode_any W_c60f4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60f8 : bv 32 := 0x0045c283.
Lemma F_c60f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66b8 : word) = Some W_c60f8.
Proof. vm_refl. Qed.
Lemma D_c60f8 : decode_any W_c60f8 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60fc : bv 32 := 0x0055c303.
Lemma F_c60fc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66bc : word) = Some W_c60fc.
Proof. vm_refl. Qed.
Lemma D_c60fc : decode_any W_c60fc = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6100 : bv 32 := 0x0065c383.
Lemma F_c6100 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66c0 : word) = Some W_c6100.
Proof. vm_refl. Qed.
Lemma D_c6100 : decode_any W_c6100 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6104 : bv 32 := 0x0075ce03.
Lemma F_c6104 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66c4 : word) = Some W_c6104.
Proof. vm_refl. Qed.
Lemma D_c6104 : decode_any W_c6104 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6108 : bv 32 := 0x00e68023.
Lemma F_c6108 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66c8 : word) = Some W_c6108.
Proof. vm_refl. Qed.
Lemma D_c6108 : decode_any W_c6108 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c610c : bv 32 := 0x00f680a3.
Lemma F_c610c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66cc : word) = Some W_c610c.
Proof. vm_refl. Qed.
Lemma D_c610c : decode_any W_c610c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6110 : bv 32 := 0x01068123.
Lemma F_c6110 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66d0 : word) = Some W_c6110.
Proof. vm_refl. Qed.
Lemma D_c6110 : decode_any W_c6110 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6114 : bv 32 := 0x011681a3.
Lemma F_c6114 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66d4 : word) = Some W_c6114.
Proof. vm_refl. Qed.
Lemma D_c6114 : decode_any W_c6114 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6118 : bv 32 := 0x0085c703.
Lemma F_c6118 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66d8 : word) = Some W_c6118.
Proof. vm_refl. Qed.
Lemma D_c6118 : decode_any W_c6118 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c611c : bv 32 := 0x0095c783.
Lemma F_c611c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66dc : word) = Some W_c611c.
Proof. vm_refl. Qed.
Lemma D_c611c : decode_any W_c611c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6120 : bv 32 := 0x00a5c803.
Lemma F_c6120 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66e0 : word) = Some W_c6120.
Proof. vm_refl. Qed.
Lemma D_c6120 : decode_any W_c6120 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6124 : bv 32 := 0x00b5c883.
Lemma F_c6124 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66e4 : word) = Some W_c6124.
Proof. vm_refl. Qed.
Lemma D_c6124 : decode_any W_c6124 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6128 : bv 32 := 0x00568223.
Lemma F_c6128 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66e8 : word) = Some W_c6128.
Proof. vm_refl. Qed.
Lemma D_c6128 : decode_any W_c6128 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c612c : bv 32 := 0x006682a3.
Lemma F_c612c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66ec : word) = Some W_c612c.
Proof. vm_refl. Qed.
Lemma D_c612c : decode_any W_c612c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6130 : bv 32 := 0x00768323.
Lemma F_c6130 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66f0 : word) = Some W_c6130.
Proof. vm_refl. Qed.
Lemma D_c6130 : decode_any W_c6130 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6134 : bv 32 := 0x01c683a3.
Lemma F_c6134 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66f4 : word) = Some W_c6134.
Proof. vm_refl. Qed.
Lemma D_c6134 : decode_any W_c6134 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6138 : bv 32 := 0x00c5c283.
Lemma F_c6138 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66f8 : word) = Some W_c6138.
Proof. vm_refl. Qed.
Lemma D_c6138 : decode_any W_c6138 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c613c : bv 32 := 0x00d5c303.
Lemma F_c613c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc66fc : word) = Some W_c613c.
Proof. vm_refl. Qed.
Lemma D_c613c : decode_any W_c613c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6140 : bv 32 := 0x00e5c383.
Lemma F_c6140 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6700 : word) = Some W_c6140.
Proof. vm_refl. Qed.
Lemma D_c6140 : decode_any W_c6140 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6144 : bv 32 := 0x00f5ce03.
Lemma F_c6144 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6704 : word) = Some W_c6144.
Proof. vm_refl. Qed.
Lemma D_c6144 : decode_any W_c6144 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6148 : bv 32 := 0x01058593.
Lemma F_c6148 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6708 : word) = Some W_c6148.
Proof. vm_refl. Qed.
Lemma D_c6148 : decode_any W_c6148 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c614c : bv 32 := 0x00e68423.
Lemma F_c614c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc670c : word) = Some W_c614c.
Proof. vm_refl. Qed.
Lemma D_c614c : decode_any W_c614c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6150 : bv 32 := 0x00f684a3.
Lemma F_c6150 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6710 : word) = Some W_c6150.
Proof. vm_refl. Qed.
Lemma D_c6150 : decode_any W_c6150 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6154 : bv 32 := 0x01068523.
Lemma F_c6154 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6714 : word) = Some W_c6154.
Proof. vm_refl. Qed.
Lemma D_c6154 : decode_any W_c6154 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6158 : bv 32 := 0x011685a3.
Lemma F_c6158 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6718 : word) = Some W_c6158.
Proof. vm_refl. Qed.
Lemma D_c6158 : decode_any W_c6158 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c615c : bv 32 := 0x01068713.
Lemma F_c615c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc671c : word) = Some W_c615c.
Proof. vm_refl. Qed.
Lemma D_c615c : decode_any W_c615c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6160 : bv 32 := 0x00568623.
Lemma F_c6160 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6720 : word) = Some W_c6160.
Proof. vm_refl. Qed.
Lemma D_c6160 : decode_any W_c6160 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6164 : bv 32 := 0x006686a3.
Lemma F_c6164 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6724 : word) = Some W_c6164.
Proof. vm_refl. Qed.
Lemma D_c6164 : decode_any W_c6164 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6168 : bv 32 := 0x00768723.
Lemma F_c6168 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6728 : word) = Some W_c6168.
Proof. vm_refl. Qed.
Lemma D_c6168 : decode_any W_c6168 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c616c : bv 32 := 0x01c687a3.
Lemma F_c616c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc672c : word) = Some W_c616c.
Proof. vm_refl. Qed.
Lemma D_c616c : decode_any W_c616c = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6170 : bv 32 := 0x00070693.
Lemma F_c6170 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6730 : word) = Some W_c6170.
Proof. vm_refl. Qed.
Lemma D_c6170 : decode_any W_c6170 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6174 : bv 32 := 0x00867713.
Lemma F_c6174 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6734 : word) = Some W_c6174.
Proof. vm_refl. Qed.
Lemma D_c6174 : decode_any W_c6174 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6178 : bv 32 := 0xd20706e3.
Lemma F_c6178 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6738 : word) = Some W_c6178.
Proof. vm_refl. Qed.
Lemma D_c6178 : decode_any W_c6178 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_c617c : bv 32 := 0x0005c703.
Lemma F_c617c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc673c : word) = Some W_c617c.
Proof. vm_refl. Qed.
Lemma D_c617c : decode_any W_c617c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6180 : bv 32 := 0x0015c783.
Lemma F_c6180 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6740 : word) = Some W_c6180.
Proof. vm_refl. Qed.
Lemma D_c6180 : decode_any W_c6180 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6184 : bv 32 := 0x0025c803.
Lemma F_c6184 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6744 : word) = Some W_c6184.
Proof. vm_refl. Qed.
Lemma D_c6184 : decode_any W_c6184 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6188 : bv 32 := 0x0035c883.
Lemma F_c6188 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6748 : word) = Some W_c6188.
Proof. vm_refl. Qed.
Lemma D_c6188 : decode_any W_c6188 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c618c : bv 32 := 0x0045c283.
Lemma F_c618c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc674c : word) = Some W_c618c.
Proof. vm_refl. Qed.
Lemma D_c618c : decode_any W_c618c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6190 : bv 32 := 0x0055c303.
Lemma F_c6190 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6750 : word) = Some W_c6190.
Proof. vm_refl. Qed.
Lemma D_c6190 : decode_any W_c6190 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6194 : bv 32 := 0x0065c383.
Lemma F_c6194 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6754 : word) = Some W_c6194.
Proof. vm_refl. Qed.
Lemma D_c6194 : decode_any W_c6194 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6198 : bv 32 := 0x0075ce03.
Lemma F_c6198 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6758 : word) = Some W_c6198.
Proof. vm_refl. Qed.
Lemma D_c6198 : decode_any W_c6198 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c619c : bv 32 := 0x00858593.
Lemma F_c619c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc675c : word) = Some W_c619c.
Proof. vm_refl. Qed.
Lemma D_c619c : decode_any W_c619c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61a0 : bv 32 := 0x00e68023.
Lemma F_c61a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6760 : word) = Some W_c61a0.
Proof. vm_refl. Qed.
Lemma D_c61a0 : decode_any W_c61a0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61a4 : bv 32 := 0x00f680a3.
Lemma F_c61a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6764 : word) = Some W_c61a4.
Proof. vm_refl. Qed.
Lemma D_c61a4 : decode_any W_c61a4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61a8 : bv 32 := 0x01068123.
Lemma F_c61a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6768 : word) = Some W_c61a8.
Proof. vm_refl. Qed.
Lemma D_c61a8 : decode_any W_c61a8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61ac : bv 32 := 0x011681a3.
Lemma F_c61ac : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc676c : word) = Some W_c61ac.
Proof. vm_refl. Qed.
Lemma D_c61ac : decode_any W_c61ac = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61b0 : bv 32 := 0x00868713.
Lemma F_c61b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6770 : word) = Some W_c61b0.
Proof. vm_refl. Qed.
Lemma D_c61b0 : decode_any W_c61b0 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61b4 : bv 32 := 0x00568223.
Lemma F_c61b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6774 : word) = Some W_c61b4.
Proof. vm_refl. Qed.
Lemma D_c61b4 : decode_any W_c61b4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61b8 : bv 32 := 0x006682a3.
Lemma F_c61b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6778 : word) = Some W_c61b8.
Proof. vm_refl. Qed.
Lemma D_c61b8 : decode_any W_c61b8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61bc : bv 32 := 0x00768323.
Lemma F_c61bc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc677c : word) = Some W_c61bc.
Proof. vm_refl. Qed.
Lemma D_c61bc : decode_any W_c61bc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61c0 : bv 32 := 0x01c683a3.
Lemma F_c61c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6780 : word) = Some W_c61c0.
Proof. vm_refl. Qed.
Lemma D_c61c0 : decode_any W_c61c0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61c4 : bv 32 := 0x00070693.
Lemma F_c61c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6784 : word) = Some W_c61c4.
Proof. vm_refl. Qed.
Lemma D_c61c4 : decode_any W_c61c4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61c8 : bv 32 := 0x00467713.
Lemma F_c61c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6788 : word) = Some W_c61c8.
Proof. vm_refl. Qed.
Lemma D_c61c8 : decode_any W_c61c8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61cc : bv 32 := 0x02070863.
Lemma F_c61cc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc678c : word) = Some W_c61cc.
Proof. vm_refl. Qed.
Lemma D_c61cc : decode_any W_c61cc = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61d0 : bv 32 := 0x0005c703.
Lemma F_c61d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6790 : word) = Some W_c61d0.
Proof. vm_refl. Qed.
Lemma D_c61d0 : decode_any W_c61d0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61d4 : bv 32 := 0x0015c783.
Lemma F_c61d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6794 : word) = Some W_c61d4.
Proof. vm_refl. Qed.
Lemma D_c61d4 : decode_any W_c61d4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61d8 : bv 32 := 0x0025c803.
Lemma F_c61d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6798 : word) = Some W_c61d8.
Proof. vm_refl. Qed.
Lemma D_c61d8 : decode_any W_c61d8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61dc : bv 32 := 0x0035c883.
Lemma F_c61dc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc679c : word) = Some W_c61dc.
Proof. vm_refl. Qed.
Lemma D_c61dc : decode_any W_c61dc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61e0 : bv 32 := 0x00458593.
Lemma F_c61e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67a0 : word) = Some W_c61e0.
Proof. vm_refl. Qed.
Lemma D_c61e0 : decode_any W_c61e0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61e4 : bv 32 := 0x00468293.
Lemma F_c61e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67a4 : word) = Some W_c61e4.
Proof. vm_refl. Qed.
Lemma D_c61e4 : decode_any W_c61e4 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61e8 : bv 32 := 0x00e68023.
Lemma F_c61e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67a8 : word) = Some W_c61e8.
Proof. vm_refl. Qed.
Lemma D_c61e8 : decode_any W_c61e8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61ec : bv 32 := 0x00f680a3.
Lemma F_c61ec : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67ac : word) = Some W_c61ec.
Proof. vm_refl. Qed.
Lemma D_c61ec : decode_any W_c61ec = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61f0 : bv 32 := 0x01068123.
Lemma F_c61f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67b0 : word) = Some W_c61f0.
Proof. vm_refl. Qed.
Lemma D_c61f0 : decode_any W_c61f0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61f4 : bv 32 := 0x011681a3.
Lemma F_c61f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67b4 : word) = Some W_c61f4.
Proof. vm_refl. Qed.
Lemma D_c61f4 : decode_any W_c61f4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61f8 : bv 32 := 0x00028693.
Lemma F_c61f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67b8 : word) = Some W_c61f8.
Proof. vm_refl. Qed.
Lemma D_c61f8 : decode_any W_c61f8 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c61fc : bv 32 := 0x00267713.
Lemma F_c61fc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67bc : word) = Some W_c61fc.
Proof. vm_refl. Qed.
Lemma D_c61fc : decode_any W_c61fc = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6200 : bv 32 := 0x00071863.
Lemma F_c6200 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67c0 : word) = Some W_c6200.
Proof. vm_refl. Qed.
Lemma D_c6200 : decode_any W_c6200 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6204 : bv 32 := 0x00167613.
Lemma F_c6204 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67c4 : word) = Some W_c6204.
Proof. vm_refl. Qed.
Lemma D_c6204 : decode_any W_c6204 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6208 : bv 32 := 0x02061663.
Lemma F_c6208 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67c8 : word) = Some W_c6208.
Proof. vm_refl. Qed.
Lemma D_c6208 : decode_any W_c6208 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_c620c : bv 32 := 0x00008067.
Lemma F_c620c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67cc : word) = Some W_c620c.
Proof. vm_refl. Qed.
Lemma D_c620c : decode_any W_c620c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6210 : bv 32 := 0x0005c703.
Lemma F_c6210 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67d0 : word) = Some W_c6210.
Proof. vm_refl. Qed.
Lemma D_c6210 : decode_any W_c6210 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6214 : bv 32 := 0x0015c783.
Lemma F_c6214 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67d4 : word) = Some W_c6214.
Proof. vm_refl. Qed.
Lemma D_c6214 : decode_any W_c6214 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6218 : bv 32 := 0x00258593.
Lemma F_c6218 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67d8 : word) = Some W_c6218.
Proof. vm_refl. Qed.
Lemma D_c6218 : decode_any W_c6218 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c621c : bv 32 := 0x00268813.
Lemma F_c621c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67dc : word) = Some W_c621c.
Proof. vm_refl. Qed.
Lemma D_c621c : decode_any W_c621c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6220 : bv 32 := 0x00e68023.
Lemma F_c6220 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67e0 : word) = Some W_c6220.
Proof. vm_refl. Qed.
Lemma D_c6220 : decode_any W_c6220 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6224 : bv 32 := 0x00f680a3.
Lemma F_c6224 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67e4 : word) = Some W_c6224.
Proof. vm_refl. Qed.
Lemma D_c6224 : decode_any W_c6224 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6228 : bv 32 := 0x00080693.
Lemma F_c6228 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67e8 : word) = Some W_c6228.
Proof. vm_refl. Qed.
Lemma D_c6228 : decode_any W_c6228 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c622c : bv 32 := 0x00167613.
Lemma F_c622c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67ec : word) = Some W_c622c.
Proof. vm_refl. Qed.
Lemma D_c622c : decode_any W_c622c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6230 : bv 32 := 0xfc060ee3.
Lemma F_c6230 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67f0 : word) = Some W_c6230.
Proof. vm_refl. Qed.
Lemma D_c6230 : decode_any W_c6230 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6234 : bv 32 := 0x0005c583.
Lemma F_c6234 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67f4 : word) = Some W_c6234.
Proof. vm_refl. Qed.
Lemma D_c6234 : decode_any W_c6234 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6238 : bv 32 := 0x00b68023.
Lemma F_c6238 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67f8 : word) = Some W_c6238.
Proof. vm_refl. Qed.
Lemma D_c6238 : decode_any W_c6238 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c623c : bv 32 := 0x00008067.
Lemma F_c623c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc67fc : word) = Some W_c623c.
Proof. vm_refl. Qed.
Lemma D_c623c : decode_any W_c623c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
