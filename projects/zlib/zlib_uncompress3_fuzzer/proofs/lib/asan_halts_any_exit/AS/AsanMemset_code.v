(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.World Require Import Tgt_zlib_uncompress3_fuzzer_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c630c : bv 32 := 0x0e060a63.
Lemma F_c630c : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68cc : word) = Some W_c630c.
Proof. vm_refl. Qed.
Lemma D_c630c : decode_any W_c630c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6310 : bv 32 := 0x00b50023.
Lemma F_c6310 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68d0 : word) = Some W_c6310.
Proof. vm_refl. Qed.
Lemma D_c6310 : decode_any W_c6310 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6314 : bv 32 := 0x00c506b3.
Lemma F_c6314 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68d4 : word) = Some W_c6314.
Proof. vm_refl. Qed.
Lemma D_c6314 : decode_any W_c6314 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6318 : bv 32 := 0x00300713.
Lemma F_c6318 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68d8 : word) = Some W_c6318.
Proof. vm_refl. Qed.
Lemma D_c6318 : decode_any W_c6318 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c631c : bv 32 := 0xfeb68fa3.
Lemma F_c631c : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68dc : word) = Some W_c631c.
Proof. vm_refl. Qed.
Lemma D_c631c : decode_any W_c631c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6320 : bv 32 := 0x0ee66063.
Lemma F_c6320 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68e0 : word) = Some W_c6320.
Proof. vm_refl. Qed.
Lemma D_c6320 : decode_any W_c6320 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6324 : bv 32 := 0x00b500a3.
Lemma F_c6324 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68e4 : word) = Some W_c6324.
Proof. vm_refl. Qed.
Lemma D_c6324 : decode_any W_c6324 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6328 : bv 32 := 0x00b50123.
Lemma F_c6328 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68e8 : word) = Some W_c6328.
Proof. vm_refl. Qed.
Lemma D_c6328 : decode_any W_c6328 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c632c : bv 32 := 0x00700713.
Lemma F_c632c : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68ec : word) = Some W_c632c.
Proof. vm_refl. Qed.
Lemma D_c632c : decode_any W_c632c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6330 : bv 32 := 0xfeb68ea3.
Lemma F_c6330 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68f0 : word) = Some W_c6330.
Proof. vm_refl. Qed.
Lemma D_c6330 : decode_any W_c6330 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6334 : bv 32 := 0xfeb68f23.
Lemma F_c6334 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68f4 : word) = Some W_c6334.
Proof. vm_refl. Qed.
Lemma D_c6334 : decode_any W_c6334 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6338 : bv 32 := 0x0ce66463.
Lemma F_c6338 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68f8 : word) = Some W_c6338.
Proof. vm_refl. Qed.
Lemma D_c6338 : decode_any W_c6338 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_c633c : bv 32 := 0x00b501a3.
Lemma F_c633c : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc68fc : word) = Some W_c633c.
Proof. vm_refl. Qed.
Lemma D_c633c : decode_any W_c633c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6340 : bv 32 := 0x00900793.
Lemma F_c6340 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6900 : word) = Some W_c6340.
Proof. vm_refl. Qed.
Lemma D_c6340 : decode_any W_c6340 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6344 : bv 32 := 0xfeb68e23.
Lemma F_c6344 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6904 : word) = Some W_c6344.
Proof. vm_refl. Qed.
Lemma D_c6344 : decode_any W_c6344 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6348 : bv 32 := 0x0af66c63.
Lemma F_c6348 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6908 : word) = Some W_c6348.
Proof. vm_refl. Qed.
Lemma D_c6348 : decode_any W_c6348 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_c634c : bv 32 := 0x40a006bb.
Lemma F_c634c : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc690c : word) = Some W_c634c.
Proof. vm_refl. Qed.
Lemma D_c634c : decode_any W_c634c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6350 : bv 32 := 0x03859813.
Lemma F_c6350 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6910 : word) = Some W_c6350.
Proof. vm_refl. Qed.
Lemma D_c6350 : decode_any W_c6350 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6354 : bv 32 := 0x101015b7.
Lemma F_c6354 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6914 : word) = Some W_c6354.
Proof. vm_refl. Qed.
Lemma D_c6354 : decode_any W_c6354 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6358 : bv 32 := 0x0036f693.
Lemma F_c6358 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6918 : word) = Some W_c6358.
Proof. vm_refl. Qed.
Lemma D_c6358 : decode_any W_c6358 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c635c : bv 32 := 0x00459713.
Lemma F_c635c : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc691c : word) = Some W_c635c.
Proof. vm_refl. Qed.
Lemma D_c635c : decode_any W_c635c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6360 : bv 32 := 0x40d60633.
Lemma F_c6360 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6920 : word) = Some W_c6360.
Proof. vm_refl. Qed.
Lemma D_c6360 : decode_any W_c6360 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6364 : bv 32 := 0x00d505b3.
Lemma F_c6364 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6924 : word) = Some W_c6364.
Proof. vm_refl. Qed.
Lemma D_c6364 : decode_any W_c6364 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6368 : bv 32 := 0x10070693.
Lemma F_c6368 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6928 : word) = Some W_c6368.
Proof. vm_refl. Qed.
Lemma D_c6368 : decode_any W_c6368 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_c636c : bv 32 := 0xffc67713.
Lemma F_c636c : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc692c : word) = Some W_c636c.
Proof. vm_refl. Qed.
Lemma D_c636c : decode_any W_c636c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6370 : bv 32 := 0x02d83633.
Lemma F_c6370 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6930 : word) = Some W_c6370.
Proof. vm_refl. Qed.
Lemma D_c6370 : decode_any W_c6370 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6374 : bv 32 := 0x00c5a023.
Lemma F_c6374 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6934 : word) = Some W_c6374.
Proof. vm_refl. Qed.
Lemma D_c6374 : decode_any W_c6374 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6378 : bv 32 := 0x00e586b3.
Lemma F_c6378 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6938 : word) = Some W_c6378.
Proof. vm_refl. Qed.
Lemma D_c6378 : decode_any W_c6378 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c637c : bv 32 := 0xfec6ae23.
Lemma F_c637c : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc693c : word) = Some W_c637c.
Proof. vm_refl. Qed.
Lemma D_c637c : decode_any W_c637c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6380 : bv 32 := 0x08f76063.
Lemma F_c6380 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6940 : word) = Some W_c6380.
Proof. vm_refl. Qed.
Lemma D_c6380 : decode_any W_c6380 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6384 : bv 32 := 0x00c5a223.
Lemma F_c6384 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6944 : word) = Some W_c6384.
Proof. vm_refl. Qed.
Lemma D_c6384 : decode_any W_c6384 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6388 : bv 32 := 0x00c5a423.
Lemma F_c6388 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6948 : word) = Some W_c6388.
Proof. vm_refl. Qed.
Lemma D_c6388 : decode_any W_c6388 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c638c : bv 32 := 0x01900793.
Lemma F_c638c : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc694c : word) = Some W_c638c.
Proof. vm_refl. Qed.
Lemma D_c638c : decode_any W_c638c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6390 : bv 32 := 0xfec6aa23.
Lemma F_c6390 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6950 : word) = Some W_c6390.
Proof. vm_refl. Qed.
Lemma D_c6390 : decode_any W_c6390 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6394 : bv 32 := 0xfec6ac23.
Lemma F_c6394 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6954 : word) = Some W_c6394.
Proof. vm_refl. Qed.
Lemma D_c6394 : decode_any W_c6394 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6398 : bv 32 := 0x06f76463.
Lemma F_c6398 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6958 : word) = Some W_c6398.
Proof. vm_refl. Qed.
Lemma D_c6398 : decode_any W_c6398 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_c639c : bv 32 := 0x00c5a623.
Lemma F_c639c : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc695c : word) = Some W_c639c.
Proof. vm_refl. Qed.
Lemma D_c639c : decode_any W_c639c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63a0 : bv 32 := 0x00c5a823.
Lemma F_c63a0 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6960 : word) = Some W_c63a0.
Proof. vm_refl. Qed.
Lemma D_c63a0 : decode_any W_c63a0 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63a4 : bv 32 := 0x00c5aa23.
Lemma F_c63a4 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6964 : word) = Some W_c63a4.
Proof. vm_refl. Qed.
Lemma D_c63a4 : decode_any W_c63a4 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63a8 : bv 32 := 0x00c5ac23.
Lemma F_c63a8 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6968 : word) = Some W_c63a8.
Proof. vm_refl. Qed.
Lemma D_c63a8 : decode_any W_c63a8 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63ac : bv 32 := 0x0045f793.
Lemma F_c63ac : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc696c : word) = Some W_c63ac.
Proof. vm_refl. Qed.
Lemma D_c63ac : decode_any W_c63ac = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63b0 : bv 32 := 0x02000813.
Lemma F_c63b0 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6970 : word) = Some W_c63b0.
Proof. vm_refl. Qed.
Lemma D_c63b0 : decode_any W_c63b0 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63b4 : bv 32 := 0x01878793.
Lemma F_c63b4 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6974 : word) = Some W_c63b4.
Proof. vm_refl. Qed.
Lemma D_c63b4 : decode_any W_c63b4 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63b8 : bv 32 := 0x40f70733.
Lemma F_c63b8 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6978 : word) = Some W_c63b8.
Proof. vm_refl. Qed.
Lemma D_c63b8 : decode_any W_c63b8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63bc : bv 32 := 0xfec6a223.
Lemma F_c63bc : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc697c : word) = Some W_c63bc.
Proof. vm_refl. Qed.
Lemma D_c63bc : decode_any W_c63bc = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63c0 : bv 32 := 0xfec6a423.
Lemma F_c63c0 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6980 : word) = Some W_c63c0.
Proof. vm_refl. Qed.
Lemma D_c63c0 : decode_any W_c63c0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63c4 : bv 32 := 0xfec6a623.
Lemma F_c63c4 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6984 : word) = Some W_c63c4.
Proof. vm_refl. Qed.
Lemma D_c63c4 : decode_any W_c63c4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63c8 : bv 32 := 0xfec6a823.
Lemma F_c63c8 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6988 : word) = Some W_c63c8.
Proof. vm_refl. Qed.
Lemma D_c63c8 : decode_any W_c63c8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63cc : bv 32 := 0x03076a63.
Lemma F_c63cc : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc698c : word) = Some W_c63cc.
Proof. vm_refl. Qed.
Lemma D_c63cc : decode_any W_c63cc = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63d0 : bv 32 := 0x02061613.
Lemma F_c63d0 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6990 : word) = Some W_c63d0.
Proof. vm_refl. Qed.
Lemma D_c63d0 : decode_any W_c63d0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63d4 : bv 32 := 0x00f585b3.
Lemma F_c63d4 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6994 : word) = Some W_c63d4.
Proof. vm_refl. Qed.
Lemma D_c63d4 : decode_any W_c63d4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63d8 : bv 32 := 0x02065693.
Lemma F_c63d8 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc6998 : word) = Some W_c63d8.
Proof. vm_refl. Qed.
Lemma D_c63d8 : decode_any W_c63d8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63dc : bv 32 := 0x00d66633.
Lemma F_c63dc : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc699c : word) = Some W_c63dc.
Proof. vm_refl. Qed.
Lemma D_c63dc : decode_any W_c63dc = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63e0 : bv 32 := 0x01f00693.
Lemma F_c63e0 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc69a0 : word) = Some W_c63e0.
Proof. vm_refl. Qed.
Lemma D_c63e0 : decode_any W_c63e0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63e4 : bv 32 := 0x00c5b023.
Lemma F_c63e4 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc69a4 : word) = Some W_c63e4.
Proof. vm_refl. Qed.
Lemma D_c63e4 : decode_any W_c63e4 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63e8 : bv 32 := 0x00c5b423.
Lemma F_c63e8 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc69a8 : word) = Some W_c63e8.
Proof. vm_refl. Qed.
Lemma D_c63e8 : decode_any W_c63e8 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63ec : bv 32 := 0x00c5b823.
Lemma F_c63ec : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc69ac : word) = Some W_c63ec.
Proof. vm_refl. Qed.
Lemma D_c63ec : decode_any W_c63ec = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63f0 : bv 32 := 0x00c5bc23.
Lemma F_c63f0 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc69b0 : word) = Some W_c63f0.
Proof. vm_refl. Qed.
Lemma D_c63f0 : decode_any W_c63f0 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63f4 : bv 32 := 0xfe070713.
Lemma F_c63f4 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc69b4 : word) = Some W_c63f4.
Proof. vm_refl. Qed.
Lemma D_c63f4 : decode_any W_c63f4 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63f8 : bv 32 := 0x02058593.
Lemma F_c63f8 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc69b8 : word) = Some W_c63f8.
Proof. vm_refl. Qed.
Lemma D_c63f8 : decode_any W_c63f8 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c63fc : bv 32 := 0xfee6e4e3.
Lemma F_c63fc : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc69bc : word) = Some W_c63fc.
Proof. vm_refl. Qed.
Lemma D_c63fc : decode_any W_c63fc = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6400 : bv 32 := 0x00008067.
Lemma F_c6400 : fetch_word Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments (0xc69c0 : word) = Some W_c6400.
Proof. vm_refl. Qed.
Lemma D_c6400 : decode_any W_c6400 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments.
Definition ms_base : Z := 0xc68cc%Z.
Definition Fo_000 := F_c630c.
Definition Do_000 := D_c630c.
Definition Fo_004 := F_c6310.
Definition Do_004 := D_c6310.
Definition Fo_008 := F_c6314.
Definition Do_008 := D_c6314.
Definition Fo_00c := F_c6318.
Definition Do_00c := D_c6318.
Definition Fo_010 := F_c631c.
Definition Do_010 := D_c631c.
Definition Fo_014 := F_c6320.
Definition Do_014 := D_c6320.
Definition Fo_018 := F_c6324.
Definition Do_018 := D_c6324.
Definition Fo_01c := F_c6328.
Definition Do_01c := D_c6328.
Definition Fo_020 := F_c632c.
Definition Do_020 := D_c632c.
Definition Fo_024 := F_c6330.
Definition Do_024 := D_c6330.
Definition Fo_028 := F_c6334.
Definition Do_028 := D_c6334.
Definition Fo_02c := F_c6338.
Definition Do_02c := D_c6338.
Definition Fo_030 := F_c633c.
Definition Do_030 := D_c633c.
Definition Fo_034 := F_c6340.
Definition Do_034 := D_c6340.
Definition Fo_038 := F_c6344.
Definition Do_038 := D_c6344.
Definition Fo_03c := F_c6348.
Definition Do_03c := D_c6348.
Definition Fo_040 := F_c634c.
Definition Do_040 := D_c634c.
Definition Fo_044 := F_c6350.
Definition Do_044 := D_c6350.
Definition Fo_048 := F_c6354.
Definition Do_048 := D_c6354.
Definition Fo_04c := F_c6358.
Definition Do_04c := D_c6358.
Definition Fo_050 := F_c635c.
Definition Do_050 := D_c635c.
Definition Fo_054 := F_c6360.
Definition Do_054 := D_c6360.
Definition Fo_058 := F_c6364.
Definition Do_058 := D_c6364.
Definition Fo_05c := F_c6368.
Definition Do_05c := D_c6368.
Definition Fo_060 := F_c636c.
Definition Do_060 := D_c636c.
Definition Fo_064 := F_c6370.
Definition Do_064 := D_c6370.
Definition Fo_068 := F_c6374.
Definition Do_068 := D_c6374.
Definition Fo_06c := F_c6378.
Definition Do_06c := D_c6378.
Definition Fo_070 := F_c637c.
Definition Do_070 := D_c637c.
Definition Fo_074 := F_c6380.
Definition Do_074 := D_c6380.
Definition Fo_078 := F_c6384.
Definition Do_078 := D_c6384.
Definition Fo_07c := F_c6388.
Definition Do_07c := D_c6388.
Definition Fo_080 := F_c638c.
Definition Do_080 := D_c638c.
Definition Fo_084 := F_c6390.
Definition Do_084 := D_c6390.
Definition Fo_088 := F_c6394.
Definition Do_088 := D_c6394.
Definition Fo_08c := F_c6398.
Definition Do_08c := D_c6398.
Definition Fo_090 := F_c639c.
Definition Do_090 := D_c639c.
Definition Fo_094 := F_c63a0.
Definition Do_094 := D_c63a0.
Definition Fo_098 := F_c63a4.
Definition Do_098 := D_c63a4.
Definition Fo_09c := F_c63a8.
Definition Do_09c := D_c63a8.
Definition Fo_0a0 := F_c63ac.
Definition Do_0a0 := D_c63ac.
Definition Fo_0a4 := F_c63b0.
Definition Do_0a4 := D_c63b0.
Definition Fo_0a8 := F_c63b4.
Definition Do_0a8 := D_c63b4.
Definition Fo_0ac := F_c63b8.
Definition Do_0ac := D_c63b8.
Definition Fo_0b0 := F_c63bc.
Definition Do_0b0 := D_c63bc.
Definition Fo_0b4 := F_c63c0.
Definition Do_0b4 := D_c63c0.
Definition Fo_0b8 := F_c63c4.
Definition Do_0b8 := D_c63c4.
Definition Fo_0bc := F_c63c8.
Definition Do_0bc := D_c63c8.
Definition Fo_0c0 := F_c63cc.
Definition Do_0c0 := D_c63cc.
Definition Fo_0c4 := F_c63d0.
Definition Do_0c4 := D_c63d0.
Definition Fo_0c8 := F_c63d4.
Definition Do_0c8 := D_c63d4.
Definition Fo_0cc := F_c63d8.
Definition Do_0cc := D_c63d8.
Definition Fo_0d0 := F_c63dc.
Definition Do_0d0 := D_c63dc.
Definition Fo_0d4 := F_c63e0.
Definition Do_0d4 := D_c63e0.
Definition Fo_0d8 := F_c63e4.
Definition Do_0d8 := D_c63e4.
Definition Fo_0dc := F_c63e8.
Definition Do_0dc := D_c63e8.
Definition Fo_0e0 := F_c63ec.
Definition Do_0e0 := D_c63ec.
Definition Fo_0e4 := F_c63f0.
Definition Do_0e4 := D_c63f0.
Definition Fo_0e8 := F_c63f4.
Definition Do_0e8 := D_c63f4.
Definition Fo_0ec := F_c63f8.
Definition Do_0ec := D_c63f8.
Definition Fo_0f0 := F_c63fc.
Definition Do_0f0 := D_c63fc.
Definition Fo_0f4 := F_c6400.
Definition Do_0f4 := D_c6400.
