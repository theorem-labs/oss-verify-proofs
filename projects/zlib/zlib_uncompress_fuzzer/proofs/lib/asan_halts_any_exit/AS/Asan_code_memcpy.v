(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.World Require Import Tgt_zlib_uncompress_fuzzer_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c5bf8 : bv 32 := 0x0035f693.
Lemma F_c5bf8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6168 : word) = Some W_c5bf8.
Proof. vm_refl. Qed.
Lemma D_c5bf8 : decode_any W_c5bf8 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5bfc : bv 32 := 0x10068863.
Lemma F_c5bfc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc616c : word) = Some W_c5bfc.
Proof. vm_refl. Qed.
Lemma D_c5bfc : decode_any W_c5bfc = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c00 : bv 32 := 0x02060e63.
Lemma F_c5c00 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6170 : word) = Some W_c5c00.
Proof. vm_refl. Qed.
Lemma D_c5c00 : decode_any W_c5c00 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c04 : bv 32 := 0x00158713.
Lemma F_c5c04 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6174 : word) = Some W_c5c04.
Proof. vm_refl. Qed.
Lemma D_c5c04 : decode_any W_c5c04 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c08 : bv 32 := 0x00100793.
Lemma F_c5c08 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6178 : word) = Some W_c5c08.
Proof. vm_refl. Qed.
Lemma D_c5c08 : decode_any W_c5c08 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c0c : bv 32 := 0x00050693.
Lemma F_c5c0c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc617c : word) = Some W_c5c0c.
Proof. vm_refl. Qed.
Lemma D_c5c0c : decode_any W_c5c0c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c10 : bv 32 := 0x0005c883.
Lemma F_c5c10 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6180 : word) = Some W_c5c10.
Proof. vm_refl. Qed.
Lemma D_c5c10 : decode_any W_c5c10 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c14 : bv 32 := 0x00060813.
Lemma F_c5c14 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6184 : word) = Some W_c5c14.
Proof. vm_refl. Qed.
Lemma D_c5c14 : decode_any W_c5c14 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c18 : bv 32 := 0x00158593.
Lemma F_c5c18 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6188 : word) = Some W_c5c18.
Proof. vm_refl. Qed.
Lemma D_c5c18 : decode_any W_c5c18 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c1c : bv 32 := 0x00377293.
Lemma F_c5c1c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc618c : word) = Some W_c5c1c.
Proof. vm_refl. Qed.
Lemma D_c5c1c : decode_any W_c5c1c = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c20 : bv 32 := 0x01168023.
Lemma F_c5c20 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6190 : word) = Some W_c5c20.
Proof. vm_refl. Qed.
Lemma D_c5c20 : decode_any W_c5c20 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c24 : bv 32 := 0x00168693.
Lemma F_c5c24 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6194 : word) = Some W_c5c24.
Proof. vm_refl. Qed.
Lemma D_c5c24 : decode_any W_c5c24 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c28 : bv 32 := 0xfff60613.
Lemma F_c5c28 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6198 : word) = Some W_c5c28.
Proof. vm_refl. Qed.
Lemma D_c5c28 : decode_any W_c5c28 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c2c : bv 32 := 0x00028a63.
Lemma F_c5c2c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc619c : word) = Some W_c5c2c.
Proof. vm_refl. Qed.
Lemma D_c5c2c : decode_any W_c5c2c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c30 : bv 32 := 0x00170713.
Lemma F_c5c30 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61a0 : word) = Some W_c5c30.
Proof. vm_refl. Qed.
Lemma D_c5c30 : decode_any W_c5c30 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c34 : bv 32 := 0xfcf81ee3.
Lemma F_c5c34 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61a4 : word) = Some W_c5c34.
Proof. vm_refl. Qed.
Lemma D_c5c34 : decode_any W_c5c34 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c38 : bv 32 := 0x0080006f.
Lemma F_c5c38 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61a8 : word) = Some W_c5c38.
Proof. vm_refl. Qed.
Lemma D_c5c38 : decode_any W_c5c38 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c3c : bv 32 := 0x00050693.
Lemma F_c5c3c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61ac : word) = Some W_c5c3c.
Proof. vm_refl. Qed.
Lemma D_c5c3c : decode_any W_c5c3c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c40 : bv 32 := 0x0036f793.
Lemma F_c5c40 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61b0 : word) = Some W_c5c40.
Proof. vm_refl. Qed.
Lemma D_c5c40 : decode_any W_c5c40 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c44 : bv 32 := 0x0c078a63.
Lemma F_c5c44 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61b4 : word) = Some W_c5c44.
Proof. vm_refl. Qed.
Lemma D_c5c44 : decode_any W_c5c44 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c48 : bv 32 := 0x02000713.
Lemma F_c5c48 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61b8 : word) = Some W_c5c48.
Proof. vm_refl. Qed.
Lemma D_c5c48 : decode_any W_c5c48 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c4c : bv 32 := 0x02e67063.
Lemma F_c5c4c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61bc : word) = Some W_c5c4c.
Proof. vm_refl. Qed.
Lemma D_c5c4c : decode_any W_c5c4c = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c50 : bv 32 := 0x01000713.
Lemma F_c5c50 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61c0 : word) = Some W_c5c50.
Proof. vm_refl. Qed.
Lemma D_c5c50 : decode_any W_c5c50 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c54 : bv 32 := 0x24e67863.
Lemma F_c5c54 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61c4 : word) = Some W_c5c54.
Proof. vm_refl. Qed.
Lemma D_c5c54 : decode_any W_c5c54 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c58 : bv 32 := 0x00867713.
Lemma F_c5c58 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61c8 : word) = Some W_c5c58.
Proof. vm_refl. Qed.
Lemma D_c5c58 : decode_any W_c5c58 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c5c : bv 32 := 0x2c071e63.
Lemma F_c5c5c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61cc : word) = Some W_c5c5c.
Proof. vm_refl. Qed.
Lemma D_c5c5c : decode_any W_c5c5c = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c60 : bv 32 := 0x00467713.
Lemma F_c5c60 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61d0 : word) = Some W_c5c60.
Proof. vm_refl. Qed.
Lemma D_c5c60 : decode_any W_c5c60 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c64 : bv 32 := 0x32071463.
Lemma F_c5c64 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61d4 : word) = Some W_c5c64.
Proof. vm_refl. Qed.
Lemma D_c5c64 : decode_any W_c5c64 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c68 : bv 32 := 0x3500006f.
Lemma F_c5c68 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61d8 : word) = Some W_c5c68.
Proof. vm_refl. Qed.
Lemma D_c5c68 : decode_any W_c5c68 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c6c : bv 32 := 0x0005a703.
Lemma F_c5c6c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61dc : word) = Some W_c5c6c.
Proof. vm_refl. Qed.
Lemma D_c5c6c : decode_any W_c5c6c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c70 : bv 32 := 0x00300813.
Lemma F_c5c70 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61e0 : word) = Some W_c5c70.
Proof. vm_refl. Qed.
Lemma D_c5c70 : decode_any W_c5c70 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c74 : bv 32 := 0x11078e63.
Lemma F_c5c74 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61e4 : word) = Some W_c5c74.
Proof. vm_refl. Qed.
Lemma D_c5c74 : decode_any W_c5c74 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c78 : bv 32 := 0x00200813.
Lemma F_c5c78 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61e8 : word) = Some W_c5c78.
Proof. vm_refl. Qed.
Lemma D_c5c78 : decode_any W_c5c78 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c7c : bv 32 := 0x19079c63.
Lemma F_c5c7c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61ec : word) = Some W_c5c7c.
Proof. vm_refl. Qed.
Lemma D_c5c7c : decode_any W_c5c7c = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c80 : bv 32 := 0x00875793.
Lemma F_c5c80 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61f0 : word) = Some W_c5c80.
Proof. vm_refl. Qed.
Lemma D_c5c80 : decode_any W_c5c80 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c84 : bv 32 := 0xffe60613.
Lemma F_c5c84 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61f4 : word) = Some W_c5c84.
Proof. vm_refl. Qed.
Lemma D_c5c84 : decode_any W_c5c84 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c88 : bv 32 := 0x00e68023.
Lemma F_c5c88 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61f8 : word) = Some W_c5c88.
Proof. vm_refl. Qed.
Lemma D_c5c88 : decode_any W_c5c88 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c8c : bv 32 := 0x00f680a3.
Lemma F_c5c8c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc61fc : word) = Some W_c5c8c.
Proof. vm_refl. Qed.
Lemma D_c5c8c : decode_any W_c5c8c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c90 : bv 32 := 0x00268693.
Lemma F_c5c90 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6200 : word) = Some W_c5c90.
Proof. vm_refl. Qed.
Lemma D_c5c90 : decode_any W_c5c90 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c94 : bv 32 := 0x01058593.
Lemma F_c5c94 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6204 : word) = Some W_c5c94.
Proof. vm_refl. Qed.
Lemma D_c5c94 : decode_any W_c5c94 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c98 : bv 32 := 0x01100793.
Lemma F_c5c98 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6208 : word) = Some W_c5c98.
Proof. vm_refl. Qed.
Lemma D_c5c98 : decode_any W_c5c98 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5c9c : bv 32 := 0x0107581b.
Lemma F_c5c9c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc620c : word) = Some W_c5c9c.
Proof. vm_refl. Qed.
Lemma D_c5c9c : decode_any W_c5c9c = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ca0 : bv 32 := 0xff45a883.
Lemma F_c5ca0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6210 : word) = Some W_c5ca0.
Proof. vm_refl. Qed.
Lemma D_c5ca0 : decode_any W_c5ca0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ca4 : bv 32 := 0xff85a283.
Lemma F_c5ca4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6214 : word) = Some W_c5ca4.
Proof. vm_refl. Qed.
Lemma D_c5ca4 : decode_any W_c5ca4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ca8 : bv 32 := 0xffc5a303.
Lemma F_c5ca8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6218 : word) = Some W_c5ca8.
Proof. vm_refl. Qed.
Lemma D_c5ca8 : decode_any W_c5ca8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cac : bv 32 := 0x0005a703.
Lemma F_c5cac : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc621c : word) = Some W_c5cac.
Proof. vm_refl. Qed.
Lemma D_c5cac : decode_any W_c5cac = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cb0 : bv 32 := 0x01089393.
Lemma F_c5cb0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6220 : word) = Some W_c5cb0.
Proof. vm_refl. Qed.
Lemma D_c5cb0 : decode_any W_c5cb0 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cb4 : bv 32 := 0x0108d89b.
Lemma F_c5cb4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6224 : word) = Some W_c5cb4.
Proof. vm_refl. Qed.
Lemma D_c5cb4 : decode_any W_c5cb4 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cb8 : bv 32 := 0x0103e833.
Lemma F_c5cb8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6228 : word) = Some W_c5cb8.
Proof. vm_refl. Qed.
Lemma D_c5cb8 : decode_any W_c5cb8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cbc : bv 32 := 0x01029393.
Lemma F_c5cbc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc622c : word) = Some W_c5cbc.
Proof. vm_refl. Qed.
Lemma D_c5cbc : decode_any W_c5cbc = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cc0 : bv 32 := 0x0102d29b.
Lemma F_c5cc0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6230 : word) = Some W_c5cc0.
Proof. vm_refl. Qed.
Lemma D_c5cc0 : decode_any W_c5cc0 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cc4 : bv 32 := 0x0113e8b3.
Lemma F_c5cc4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6234 : word) = Some W_c5cc4.
Proof. vm_refl. Qed.
Lemma D_c5cc4 : decode_any W_c5cc4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cc8 : bv 32 := 0x01031393.
Lemma F_c5cc8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6238 : word) = Some W_c5cc8.
Proof. vm_refl. Qed.
Lemma D_c5cc8 : decode_any W_c5cc8 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ccc : bv 32 := 0x0103531b.
Lemma F_c5ccc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc623c : word) = Some W_c5ccc.
Proof. vm_refl. Qed.
Lemma D_c5ccc : decode_any W_c5ccc = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cd0 : bv 32 := 0x0053e2b3.
Lemma F_c5cd0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6240 : word) = Some W_c5cd0.
Proof. vm_refl. Qed.
Lemma D_c5cd0 : decode_any W_c5cd0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cd4 : bv 32 := 0x01071393.
Lemma F_c5cd4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6244 : word) = Some W_c5cd4.
Proof. vm_refl. Qed.
Lemma D_c5cd4 : decode_any W_c5cd4 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cd8 : bv 32 := 0x0063e333.
Lemma F_c5cd8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6248 : word) = Some W_c5cd8.
Proof. vm_refl. Qed.
Lemma D_c5cd8 : decode_any W_c5cd8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cdc : bv 32 := 0xff060613.
Lemma F_c5cdc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc624c : word) = Some W_c5cdc.
Proof. vm_refl. Qed.
Lemma D_c5cdc : decode_any W_c5cdc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ce0 : bv 32 := 0x0106a023.
Lemma F_c5ce0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6250 : word) = Some W_c5ce0.
Proof. vm_refl. Qed.
Lemma D_c5ce0 : decode_any W_c5ce0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ce4 : bv 32 := 0x0116a223.
Lemma F_c5ce4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6254 : word) = Some W_c5ce4.
Proof. vm_refl. Qed.
Lemma D_c5ce4 : decode_any W_c5ce4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ce8 : bv 32 := 0x0056a423.
Lemma F_c5ce8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6258 : word) = Some W_c5ce8.
Proof. vm_refl. Qed.
Lemma D_c5ce8 : decode_any W_c5ce8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cec : bv 32 := 0x0066a623.
Lemma F_c5cec : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc625c : word) = Some W_c5cec.
Proof. vm_refl. Qed.
Lemma D_c5cec : decode_any W_c5cec = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cf0 : bv 32 := 0x01068693.
Lemma F_c5cf0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6260 : word) = Some W_c5cf0.
Proof. vm_refl. Qed.
Lemma D_c5cf0 : decode_any W_c5cf0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cf4 : bv 32 := 0x01058593.
Lemma F_c5cf4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6264 : word) = Some W_c5cf4.
Proof. vm_refl. Qed.
Lemma D_c5cf4 : decode_any W_c5cf4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cf8 : bv 32 := 0xfac7e2e3.
Lemma F_c5cf8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6268 : word) = Some W_c5cf8.
Proof. vm_refl. Qed.
Lemma D_c5cf8 : decode_any W_c5cf8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5cfc : bv 32 := 0xff258593.
Lemma F_c5cfc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc626c : word) = Some W_c5cfc.
Proof. vm_refl. Qed.
Lemma D_c5cfc : decode_any W_c5cfc = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d00 : bv 32 := 0x01000713.
Lemma F_c5d00 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6270 : word) = Some W_c5d00.
Proof. vm_refl. Qed.
Lemma D_c5d00 : decode_any W_c5d00 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d04 : bv 32 := 0xf4e66ae3.
Lemma F_c5d04 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6274 : word) = Some W_c5d04.
Proof. vm_refl. Qed.
Lemma D_c5d04 : decode_any W_c5d04 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d08 : bv 32 := 0x19c0006f.
Lemma F_c5d08 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6278 : word) = Some W_c5d08.
Proof. vm_refl. Qed.
Lemma D_c5d08 : decode_any W_c5d08 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d0c : bv 32 := 0x00050693.
Lemma F_c5d0c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc627c : word) = Some W_c5d0c.
Proof. vm_refl. Qed.
Lemma D_c5d0c : decode_any W_c5d0c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d10 : bv 32 := 0x00357793.
Lemma F_c5d10 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6280 : word) = Some W_c5d10.
Proof. vm_refl. Qed.
Lemma D_c5d10 : decode_any W_c5d10 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d14 : bv 32 := 0xf2079ae3.
Lemma F_c5d14 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6284 : word) = Some W_c5d14.
Proof. vm_refl. Qed.
Lemma D_c5d14 : decode_any W_c5d14 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d18 : bv 32 := 0x01000713.
Lemma F_c5d18 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6288 : word) = Some W_c5d18.
Proof. vm_refl. Qed.
Lemma D_c5d18 : decode_any W_c5d18 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d1c : bv 32 := 0x02e66c63.
Lemma F_c5d1c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc628c : word) = Some W_c5d1c.
Proof. vm_refl. Qed.
Lemma D_c5d1c : decode_any W_c5d1c = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d20 : bv 32 := 0x00f00713.
Lemma F_c5d20 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6290 : word) = Some W_c5d20.
Proof. vm_refl. Qed.
Lemma D_c5d20 : decode_any W_c5d20 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d24 : bv 32 := 0x0005a783.
Lemma F_c5d24 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6294 : word) = Some W_c5d24.
Proof. vm_refl. Qed.
Lemma D_c5d24 : decode_any W_c5d24 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d28 : bv 32 := 0x0045a803.
Lemma F_c5d28 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6298 : word) = Some W_c5d28.
Proof. vm_refl. Qed.
Lemma D_c5d28 : decode_any W_c5d28 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d2c : bv 32 := 0x0085a883.
Lemma F_c5d2c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc629c : word) = Some W_c5d2c.
Proof. vm_refl. Qed.
Lemma D_c5d2c : decode_any W_c5d2c = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d30 : bv 32 := 0x00c5a283.
Lemma F_c5d30 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62a0 : word) = Some W_c5d30.
Proof. vm_refl. Qed.
Lemma D_c5d30 : decode_any W_c5d30 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d34 : bv 32 := 0x01058593.
Lemma F_c5d34 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62a4 : word) = Some W_c5d34.
Proof. vm_refl. Qed.
Lemma D_c5d34 : decode_any W_c5d34 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d38 : bv 32 := 0xff060613.
Lemma F_c5d38 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62a8 : word) = Some W_c5d38.
Proof. vm_refl. Qed.
Lemma D_c5d38 : decode_any W_c5d38 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d3c : bv 32 := 0x00f6a023.
Lemma F_c5d3c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62ac : word) = Some W_c5d3c.
Proof. vm_refl. Qed.
Lemma D_c5d3c : decode_any W_c5d3c = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d40 : bv 32 := 0x0106a223.
Lemma F_c5d40 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62b0 : word) = Some W_c5d40.
Proof. vm_refl. Qed.
Lemma D_c5d40 : decode_any W_c5d40 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d44 : bv 32 := 0x0116a423.
Lemma F_c5d44 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62b4 : word) = Some W_c5d44.
Proof. vm_refl. Qed.
Lemma D_c5d44 : decode_any W_c5d44 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d48 : bv 32 := 0x0056a623.
Lemma F_c5d48 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62b8 : word) = Some W_c5d48.
Proof. vm_refl. Qed.
Lemma D_c5d48 : decode_any W_c5d48 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d4c : bv 32 := 0x01068693.
Lemma F_c5d4c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62bc : word) = Some W_c5d4c.
Proof. vm_refl. Qed.
Lemma D_c5d4c : decode_any W_c5d4c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d50 : bv 32 := 0xfcc76ae3.
Lemma F_c5d50 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62c0 : word) = Some W_c5d50.
Proof. vm_refl. Qed.
Lemma D_c5d50 : decode_any W_c5d50 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d54 : bv 32 := 0x00800713.
Lemma F_c5d54 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62c4 : word) = Some W_c5d54.
Proof. vm_refl. Qed.
Lemma D_c5d54 : decode_any W_c5d54 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d58 : bv 32 := 0x00e66e63.
Lemma F_c5d58 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62c8 : word) = Some W_c5d58.
Proof. vm_refl. Qed.
Lemma D_c5d58 : decode_any W_c5d58 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d5c : bv 32 := 0x0005a703.
Lemma F_c5d5c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62cc : word) = Some W_c5d5c.
Proof. vm_refl. Qed.
Lemma D_c5d5c : decode_any W_c5d5c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d60 : bv 32 := 0x0045a783.
Lemma F_c5d60 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62d0 : word) = Some W_c5d60.
Proof. vm_refl. Qed.
Lemma D_c5d60 : decode_any W_c5d60 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d64 : bv 32 := 0x00e6a023.
Lemma F_c5d64 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62d4 : word) = Some W_c5d64.
Proof. vm_refl. Qed.
Lemma D_c5d64 : decode_any W_c5d64 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d68 : bv 32 := 0x00f6a223.
Lemma F_c5d68 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62d8 : word) = Some W_c5d68.
Proof. vm_refl. Qed.
Lemma D_c5d68 : decode_any W_c5d68 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d6c : bv 32 := 0x00868693.
Lemma F_c5d6c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62dc : word) = Some W_c5d6c.
Proof. vm_refl. Qed.
Lemma D_c5d6c : decode_any W_c5d6c = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d70 : bv 32 := 0x00858593.
Lemma F_c5d70 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62e0 : word) = Some W_c5d70.
Proof. vm_refl. Qed.
Lemma D_c5d70 : decode_any W_c5d70 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d74 : bv 32 := 0x00467713.
Lemma F_c5d74 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62e4 : word) = Some W_c5d74.
Proof. vm_refl. Qed.
Lemma D_c5d74 : decode_any W_c5d74 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d78 : bv 32 := 0x24070063.
Lemma F_c5d78 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62e8 : word) = Some W_c5d78.
Proof. vm_refl. Qed.
Lemma D_c5d78 : decode_any W_c5d78 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d7c : bv 32 := 0x0005a703.
Lemma F_c5d7c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62ec : word) = Some W_c5d7c.
Proof. vm_refl. Qed.
Lemma D_c5d7c : decode_any W_c5d7c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d80 : bv 32 := 0x00458593.
Lemma F_c5d80 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62f0 : word) = Some W_c5d80.
Proof. vm_refl. Qed.
Lemma D_c5d80 : decode_any W_c5d80 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d84 : bv 32 := 0x00e6a023.
Lemma F_c5d84 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62f4 : word) = Some W_c5d84.
Proof. vm_refl. Qed.
Lemma D_c5d84 : decode_any W_c5d84 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d88 : bv 32 := 0x00468693.
Lemma F_c5d88 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62f8 : word) = Some W_c5d88.
Proof. vm_refl. Qed.
Lemma D_c5d88 : decode_any W_c5d88 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d8c : bv 32 := 0x22c0006f.
Lemma F_c5d8c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc62fc : word) = Some W_c5d8c.
Proof. vm_refl. Qed.
Lemma D_c5d8c : decode_any W_c5d8c = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d90 : bv 32 := 0x00e68023.
Lemma F_c5d90 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6300 : word) = Some W_c5d90.
Proof. vm_refl. Qed.
Lemma D_c5d90 : decode_any W_c5d90 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d94 : bv 32 := 0x00168693.
Lemma F_c5d94 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6304 : word) = Some W_c5d94.
Proof. vm_refl. Qed.
Lemma D_c5d94 : decode_any W_c5d94 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d98 : bv 32 := 0xfff60613.
Lemma F_c5d98 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6308 : word) = Some W_c5d98.
Proof. vm_refl. Qed.
Lemma D_c5d98 : decode_any W_c5d98 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5d9c : bv 32 := 0x01058593.
Lemma F_c5d9c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc630c : word) = Some W_c5d9c.
Proof. vm_refl. Qed.
Lemma D_c5d9c : decode_any W_c5d9c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5da0 : bv 32 := 0x01200793.
Lemma F_c5da0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6310 : word) = Some W_c5da0.
Proof. vm_refl. Qed.
Lemma D_c5da0 : decode_any W_c5da0 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5da4 : bv 32 := 0x0087581b.
Lemma F_c5da4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6314 : word) = Some W_c5da4.
Proof. vm_refl. Qed.
Lemma D_c5da4 : decode_any W_c5da4 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5da8 : bv 32 := 0xff45a883.
Lemma F_c5da8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6318 : word) = Some W_c5da8.
Proof. vm_refl. Qed.
Lemma D_c5da8 : decode_any W_c5da8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5dac : bv 32 := 0xff85a283.
Lemma F_c5dac : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc631c : word) = Some W_c5dac.
Proof. vm_refl. Qed.
Lemma D_c5dac : decode_any W_c5dac = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5db0 : bv 32 := 0xffc5a303.
Lemma F_c5db0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6320 : word) = Some W_c5db0.
Proof. vm_refl. Qed.
Lemma D_c5db0 : decode_any W_c5db0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5db4 : bv 32 := 0x0005a703.
Lemma F_c5db4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6324 : word) = Some W_c5db4.
Proof. vm_refl. Qed.
Lemma D_c5db4 : decode_any W_c5db4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5db8 : bv 32 := 0x01889393.
Lemma F_c5db8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6328 : word) = Some W_c5db8.
Proof. vm_refl. Qed.
Lemma D_c5db8 : decode_any W_c5db8 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5dbc : bv 32 := 0x0088d89b.
Lemma F_c5dbc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc632c : word) = Some W_c5dbc.
Proof. vm_refl. Qed.
Lemma D_c5dbc : decode_any W_c5dbc = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5dc0 : bv 32 := 0x0103e833.
Lemma F_c5dc0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6330 : word) = Some W_c5dc0.
Proof. vm_refl. Qed.
Lemma D_c5dc0 : decode_any W_c5dc0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5dc4 : bv 32 := 0x01829393.
Lemma F_c5dc4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6334 : word) = Some W_c5dc4.
Proof. vm_refl. Qed.
Lemma D_c5dc4 : decode_any W_c5dc4 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5dc8 : bv 32 := 0x0082d29b.
Lemma F_c5dc8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6338 : word) = Some W_c5dc8.
Proof. vm_refl. Qed.
Lemma D_c5dc8 : decode_any W_c5dc8 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5dcc : bv 32 := 0x0113e8b3.
Lemma F_c5dcc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc633c : word) = Some W_c5dcc.
Proof. vm_refl. Qed.
Lemma D_c5dcc : decode_any W_c5dcc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5dd0 : bv 32 := 0x01831393.
Lemma F_c5dd0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6340 : word) = Some W_c5dd0.
Proof. vm_refl. Qed.
Lemma D_c5dd0 : decode_any W_c5dd0 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5dd4 : bv 32 := 0x0083531b.
Lemma F_c5dd4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6344 : word) = Some W_c5dd4.
Proof. vm_refl. Qed.
Lemma D_c5dd4 : decode_any W_c5dd4 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5dd8 : bv 32 := 0x0053e2b3.
Lemma F_c5dd8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6348 : word) = Some W_c5dd8.
Proof. vm_refl. Qed.
Lemma D_c5dd8 : decode_any W_c5dd8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ddc : bv 32 := 0x01871393.
Lemma F_c5ddc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc634c : word) = Some W_c5ddc.
Proof. vm_refl. Qed.
Lemma D_c5ddc : decode_any W_c5ddc = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5de0 : bv 32 := 0x0063e333.
Lemma F_c5de0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6350 : word) = Some W_c5de0.
Proof. vm_refl. Qed.
Lemma D_c5de0 : decode_any W_c5de0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5de4 : bv 32 := 0xff060613.
Lemma F_c5de4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6354 : word) = Some W_c5de4.
Proof. vm_refl. Qed.
Lemma D_c5de4 : decode_any W_c5de4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5de8 : bv 32 := 0x0106a023.
Lemma F_c5de8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6358 : word) = Some W_c5de8.
Proof. vm_refl. Qed.
Lemma D_c5de8 : decode_any W_c5de8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5dec : bv 32 := 0x0116a223.
Lemma F_c5dec : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc635c : word) = Some W_c5dec.
Proof. vm_refl. Qed.
Lemma D_c5dec : decode_any W_c5dec = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5df0 : bv 32 := 0x0056a423.
Lemma F_c5df0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6360 : word) = Some W_c5df0.
Proof. vm_refl. Qed.
Lemma D_c5df0 : decode_any W_c5df0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5df4 : bv 32 := 0x0066a623.
Lemma F_c5df4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6364 : word) = Some W_c5df4.
Proof. vm_refl. Qed.
Lemma D_c5df4 : decode_any W_c5df4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5df8 : bv 32 := 0x01068693.
Lemma F_c5df8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6368 : word) = Some W_c5df8.
Proof. vm_refl. Qed.
Lemma D_c5df8 : decode_any W_c5df8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5dfc : bv 32 := 0x01058593.
Lemma F_c5dfc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc636c : word) = Some W_c5dfc.
Proof. vm_refl. Qed.
Lemma D_c5dfc : decode_any W_c5dfc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e00 : bv 32 := 0xfac7e2e3.
Lemma F_c5e00 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6370 : word) = Some W_c5e00.
Proof. vm_refl. Qed.
Lemma D_c5e00 : decode_any W_c5e00 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e04 : bv 32 := 0xff158593.
Lemma F_c5e04 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6374 : word) = Some W_c5e04.
Proof. vm_refl. Qed.
Lemma D_c5e04 : decode_any W_c5e04 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e08 : bv 32 := 0x01000713.
Lemma F_c5e08 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6378 : word) = Some W_c5e08.
Proof. vm_refl. Qed.
Lemma D_c5e08 : decode_any W_c5e08 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e0c : bv 32 := 0xe4e666e3.
Lemma F_c5e0c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc637c : word) = Some W_c5e0c.
Proof. vm_refl. Qed.
Lemma D_c5e0c : decode_any W_c5e0c = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e10 : bv 32 := 0x0940006f.
Lemma F_c5e10 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6380 : word) = Some W_c5e10.
Proof. vm_refl. Qed.
Lemma D_c5e10 : decode_any W_c5e10 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e14 : bv 32 := 0x00875793.
Lemma F_c5e14 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6384 : word) = Some W_c5e14.
Proof. vm_refl. Qed.
Lemma D_c5e14 : decode_any W_c5e14 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e18 : bv 32 := 0x01075813.
Lemma F_c5e18 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6388 : word) = Some W_c5e18.
Proof. vm_refl. Qed.
Lemma D_c5e18 : decode_any W_c5e18 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e1c : bv 32 := 0xffd60613.
Lemma F_c5e1c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc638c : word) = Some W_c5e1c.
Proof. vm_refl. Qed.
Lemma D_c5e1c : decode_any W_c5e1c = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e20 : bv 32 := 0x00e68023.
Lemma F_c5e20 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6390 : word) = Some W_c5e20.
Proof. vm_refl. Qed.
Lemma D_c5e20 : decode_any W_c5e20 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e24 : bv 32 := 0x00f680a3.
Lemma F_c5e24 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6394 : word) = Some W_c5e24.
Proof. vm_refl. Qed.
Lemma D_c5e24 : decode_any W_c5e24 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e28 : bv 32 := 0x01068123.
Lemma F_c5e28 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6398 : word) = Some W_c5e28.
Proof. vm_refl. Qed.
Lemma D_c5e28 : decode_any W_c5e28 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e2c : bv 32 := 0x00368693.
Lemma F_c5e2c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc639c : word) = Some W_c5e2c.
Proof. vm_refl. Qed.
Lemma D_c5e2c : decode_any W_c5e2c = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e30 : bv 32 := 0x01058593.
Lemma F_c5e30 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63a0 : word) = Some W_c5e30.
Proof. vm_refl. Qed.
Lemma D_c5e30 : decode_any W_c5e30 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e34 : bv 32 := 0x01000793.
Lemma F_c5e34 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63a4 : word) = Some W_c5e34.
Proof. vm_refl. Qed.
Lemma D_c5e34 : decode_any W_c5e34 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e38 : bv 32 := 0x0187581b.
Lemma F_c5e38 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63a8 : word) = Some W_c5e38.
Proof. vm_refl. Qed.
Lemma D_c5e38 : decode_any W_c5e38 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e3c : bv 32 := 0xff45a883.
Lemma F_c5e3c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63ac : word) = Some W_c5e3c.
Proof. vm_refl. Qed.
Lemma D_c5e3c : decode_any W_c5e3c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e40 : bv 32 := 0xff85a283.
Lemma F_c5e40 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63b0 : word) = Some W_c5e40.
Proof. vm_refl. Qed.
Lemma D_c5e40 : decode_any W_c5e40 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e44 : bv 32 := 0xffc5a303.
Lemma F_c5e44 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63b4 : word) = Some W_c5e44.
Proof. vm_refl. Qed.
Lemma D_c5e44 : decode_any W_c5e44 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e48 : bv 32 := 0x0005a703.
Lemma F_c5e48 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63b8 : word) = Some W_c5e48.
Proof. vm_refl. Qed.
Lemma D_c5e48 : decode_any W_c5e48 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e4c : bv 32 := 0x00889393.
Lemma F_c5e4c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63bc : word) = Some W_c5e4c.
Proof. vm_refl. Qed.
Lemma D_c5e4c : decode_any W_c5e4c = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e50 : bv 32 := 0x0188d89b.
Lemma F_c5e50 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63c0 : word) = Some W_c5e50.
Proof. vm_refl. Qed.
Lemma D_c5e50 : decode_any W_c5e50 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e54 : bv 32 := 0x0103e833.
Lemma F_c5e54 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63c4 : word) = Some W_c5e54.
Proof. vm_refl. Qed.
Lemma D_c5e54 : decode_any W_c5e54 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e58 : bv 32 := 0x00829393.
Lemma F_c5e58 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63c8 : word) = Some W_c5e58.
Proof. vm_refl. Qed.
Lemma D_c5e58 : decode_any W_c5e58 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e5c : bv 32 := 0x0182d29b.
Lemma F_c5e5c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63cc : word) = Some W_c5e5c.
Proof. vm_refl. Qed.
Lemma D_c5e5c : decode_any W_c5e5c = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e60 : bv 32 := 0x0113e8b3.
Lemma F_c5e60 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63d0 : word) = Some W_c5e60.
Proof. vm_refl. Qed.
Lemma D_c5e60 : decode_any W_c5e60 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e64 : bv 32 := 0x00831393.
Lemma F_c5e64 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63d4 : word) = Some W_c5e64.
Proof. vm_refl. Qed.
Lemma D_c5e64 : decode_any W_c5e64 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e68 : bv 32 := 0x0183531b.
Lemma F_c5e68 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63d8 : word) = Some W_c5e68.
Proof. vm_refl. Qed.
Lemma D_c5e68 : decode_any W_c5e68 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e6c : bv 32 := 0x0053e2b3.
Lemma F_c5e6c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63dc : word) = Some W_c5e6c.
Proof. vm_refl. Qed.
Lemma D_c5e6c : decode_any W_c5e6c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e70 : bv 32 := 0x00871393.
Lemma F_c5e70 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63e0 : word) = Some W_c5e70.
Proof. vm_refl. Qed.
Lemma D_c5e70 : decode_any W_c5e70 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e74 : bv 32 := 0x0063e333.
Lemma F_c5e74 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63e4 : word) = Some W_c5e74.
Proof. vm_refl. Qed.
Lemma D_c5e74 : decode_any W_c5e74 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e78 : bv 32 := 0xff060613.
Lemma F_c5e78 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63e8 : word) = Some W_c5e78.
Proof. vm_refl. Qed.
Lemma D_c5e78 : decode_any W_c5e78 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e7c : bv 32 := 0x0106a023.
Lemma F_c5e7c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63ec : word) = Some W_c5e7c.
Proof. vm_refl. Qed.
Lemma D_c5e7c : decode_any W_c5e7c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e80 : bv 32 := 0x0116a223.
Lemma F_c5e80 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63f0 : word) = Some W_c5e80.
Proof. vm_refl. Qed.
Lemma D_c5e80 : decode_any W_c5e80 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e84 : bv 32 := 0x0056a423.
Lemma F_c5e84 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63f4 : word) = Some W_c5e84.
Proof. vm_refl. Qed.
Lemma D_c5e84 : decode_any W_c5e84 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e88 : bv 32 := 0x0066a623.
Lemma F_c5e88 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63f8 : word) = Some W_c5e88.
Proof. vm_refl. Qed.
Lemma D_c5e88 : decode_any W_c5e88 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e8c : bv 32 := 0x01068693.
Lemma F_c5e8c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc63fc : word) = Some W_c5e8c.
Proof. vm_refl. Qed.
Lemma D_c5e8c : decode_any W_c5e8c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e90 : bv 32 := 0x01058593.
Lemma F_c5e90 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6400 : word) = Some W_c5e90.
Proof. vm_refl. Qed.
Lemma D_c5e90 : decode_any W_c5e90 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e94 : bv 32 := 0xfac7e2e3.
Lemma F_c5e94 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6404 : word) = Some W_c5e94.
Proof. vm_refl. Qed.
Lemma D_c5e94 : decode_any W_c5e94 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e98 : bv 32 := 0xff358593.
Lemma F_c5e98 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6408 : word) = Some W_c5e98.
Proof. vm_refl. Qed.
Lemma D_c5e98 : decode_any W_c5e98 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5e9c : bv 32 := 0x01000713.
Lemma F_c5e9c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc640c : word) = Some W_c5e9c.
Proof. vm_refl. Qed.
Lemma D_c5e9c : decode_any W_c5e9c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ea0 : bv 32 := 0xdae66ce3.
Lemma F_c5ea0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6410 : word) = Some W_c5ea0.
Proof. vm_refl. Qed.
Lemma D_c5ea0 : decode_any W_c5ea0 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ea4 : bv 32 := 0x0005c703.
Lemma F_c5ea4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6414 : word) = Some W_c5ea4.
Proof. vm_refl. Qed.
Lemma D_c5ea4 : decode_any W_c5ea4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ea8 : bv 32 := 0x0015c783.
Lemma F_c5ea8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6418 : word) = Some W_c5ea8.
Proof. vm_refl. Qed.
Lemma D_c5ea8 : decode_any W_c5ea8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5eac : bv 32 := 0x0025c803.
Lemma F_c5eac : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc641c : word) = Some W_c5eac.
Proof. vm_refl. Qed.
Lemma D_c5eac : decode_any W_c5eac = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5eb0 : bv 32 := 0x0035c883.
Lemma F_c5eb0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6420 : word) = Some W_c5eb0.
Proof. vm_refl. Qed.
Lemma D_c5eb0 : decode_any W_c5eb0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5eb4 : bv 32 := 0x0045c283.
Lemma F_c5eb4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6424 : word) = Some W_c5eb4.
Proof. vm_refl. Qed.
Lemma D_c5eb4 : decode_any W_c5eb4 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5eb8 : bv 32 := 0x0055c303.
Lemma F_c5eb8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6428 : word) = Some W_c5eb8.
Proof. vm_refl. Qed.
Lemma D_c5eb8 : decode_any W_c5eb8 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ebc : bv 32 := 0x0065c383.
Lemma F_c5ebc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc642c : word) = Some W_c5ebc.
Proof. vm_refl. Qed.
Lemma D_c5ebc : decode_any W_c5ebc = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ec0 : bv 32 := 0x0075ce03.
Lemma F_c5ec0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6430 : word) = Some W_c5ec0.
Proof. vm_refl. Qed.
Lemma D_c5ec0 : decode_any W_c5ec0 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ec4 : bv 32 := 0x00e68023.
Lemma F_c5ec4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6434 : word) = Some W_c5ec4.
Proof. vm_refl. Qed.
Lemma D_c5ec4 : decode_any W_c5ec4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ec8 : bv 32 := 0x00f680a3.
Lemma F_c5ec8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6438 : word) = Some W_c5ec8.
Proof. vm_refl. Qed.
Lemma D_c5ec8 : decode_any W_c5ec8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ecc : bv 32 := 0x01068123.
Lemma F_c5ecc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc643c : word) = Some W_c5ecc.
Proof. vm_refl. Qed.
Lemma D_c5ecc : decode_any W_c5ecc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ed0 : bv 32 := 0x011681a3.
Lemma F_c5ed0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6440 : word) = Some W_c5ed0.
Proof. vm_refl. Qed.
Lemma D_c5ed0 : decode_any W_c5ed0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ed4 : bv 32 := 0x0085c703.
Lemma F_c5ed4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6444 : word) = Some W_c5ed4.
Proof. vm_refl. Qed.
Lemma D_c5ed4 : decode_any W_c5ed4 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ed8 : bv 32 := 0x0095c783.
Lemma F_c5ed8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6448 : word) = Some W_c5ed8.
Proof. vm_refl. Qed.
Lemma D_c5ed8 : decode_any W_c5ed8 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5edc : bv 32 := 0x00a5c803.
Lemma F_c5edc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc644c : word) = Some W_c5edc.
Proof. vm_refl. Qed.
Lemma D_c5edc : decode_any W_c5edc = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ee0 : bv 32 := 0x00b5c883.
Lemma F_c5ee0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6450 : word) = Some W_c5ee0.
Proof. vm_refl. Qed.
Lemma D_c5ee0 : decode_any W_c5ee0 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ee4 : bv 32 := 0x00568223.
Lemma F_c5ee4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6454 : word) = Some W_c5ee4.
Proof. vm_refl. Qed.
Lemma D_c5ee4 : decode_any W_c5ee4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ee8 : bv 32 := 0x006682a3.
Lemma F_c5ee8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6458 : word) = Some W_c5ee8.
Proof. vm_refl. Qed.
Lemma D_c5ee8 : decode_any W_c5ee8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5eec : bv 32 := 0x00768323.
Lemma F_c5eec : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc645c : word) = Some W_c5eec.
Proof. vm_refl. Qed.
Lemma D_c5eec : decode_any W_c5eec = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ef0 : bv 32 := 0x01c683a3.
Lemma F_c5ef0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6460 : word) = Some W_c5ef0.
Proof. vm_refl. Qed.
Lemma D_c5ef0 : decode_any W_c5ef0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ef4 : bv 32 := 0x00c5c283.
Lemma F_c5ef4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6464 : word) = Some W_c5ef4.
Proof. vm_refl. Qed.
Lemma D_c5ef4 : decode_any W_c5ef4 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ef8 : bv 32 := 0x00d5c303.
Lemma F_c5ef8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6468 : word) = Some W_c5ef8.
Proof. vm_refl. Qed.
Lemma D_c5ef8 : decode_any W_c5ef8 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5efc : bv 32 := 0x00e5c383.
Lemma F_c5efc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc646c : word) = Some W_c5efc.
Proof. vm_refl. Qed.
Lemma D_c5efc : decode_any W_c5efc = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f00 : bv 32 := 0x00f5ce03.
Lemma F_c5f00 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6470 : word) = Some W_c5f00.
Proof. vm_refl. Qed.
Lemma D_c5f00 : decode_any W_c5f00 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f04 : bv 32 := 0x01058593.
Lemma F_c5f04 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6474 : word) = Some W_c5f04.
Proof. vm_refl. Qed.
Lemma D_c5f04 : decode_any W_c5f04 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f08 : bv 32 := 0x00e68423.
Lemma F_c5f08 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6478 : word) = Some W_c5f08.
Proof. vm_refl. Qed.
Lemma D_c5f08 : decode_any W_c5f08 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f0c : bv 32 := 0x00f684a3.
Lemma F_c5f0c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc647c : word) = Some W_c5f0c.
Proof. vm_refl. Qed.
Lemma D_c5f0c : decode_any W_c5f0c = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f10 : bv 32 := 0x01068523.
Lemma F_c5f10 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6480 : word) = Some W_c5f10.
Proof. vm_refl. Qed.
Lemma D_c5f10 : decode_any W_c5f10 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f14 : bv 32 := 0x011685a3.
Lemma F_c5f14 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6484 : word) = Some W_c5f14.
Proof. vm_refl. Qed.
Lemma D_c5f14 : decode_any W_c5f14 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f18 : bv 32 := 0x01068713.
Lemma F_c5f18 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6488 : word) = Some W_c5f18.
Proof. vm_refl. Qed.
Lemma D_c5f18 : decode_any W_c5f18 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f1c : bv 32 := 0x00568623.
Lemma F_c5f1c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc648c : word) = Some W_c5f1c.
Proof. vm_refl. Qed.
Lemma D_c5f1c : decode_any W_c5f1c = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f20 : bv 32 := 0x006686a3.
Lemma F_c5f20 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6490 : word) = Some W_c5f20.
Proof. vm_refl. Qed.
Lemma D_c5f20 : decode_any W_c5f20 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f24 : bv 32 := 0x00768723.
Lemma F_c5f24 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6494 : word) = Some W_c5f24.
Proof. vm_refl. Qed.
Lemma D_c5f24 : decode_any W_c5f24 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f28 : bv 32 := 0x01c687a3.
Lemma F_c5f28 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6498 : word) = Some W_c5f28.
Proof. vm_refl. Qed.
Lemma D_c5f28 : decode_any W_c5f28 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f2c : bv 32 := 0x00070693.
Lemma F_c5f2c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc649c : word) = Some W_c5f2c.
Proof. vm_refl. Qed.
Lemma D_c5f2c : decode_any W_c5f2c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f30 : bv 32 := 0x00867713.
Lemma F_c5f30 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64a0 : word) = Some W_c5f30.
Proof. vm_refl. Qed.
Lemma D_c5f30 : decode_any W_c5f30 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f34 : bv 32 := 0xd20706e3.
Lemma F_c5f34 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64a4 : word) = Some W_c5f34.
Proof. vm_refl. Qed.
Lemma D_c5f34 : decode_any W_c5f34 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f38 : bv 32 := 0x0005c703.
Lemma F_c5f38 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64a8 : word) = Some W_c5f38.
Proof. vm_refl. Qed.
Lemma D_c5f38 : decode_any W_c5f38 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f3c : bv 32 := 0x0015c783.
Lemma F_c5f3c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64ac : word) = Some W_c5f3c.
Proof. vm_refl. Qed.
Lemma D_c5f3c : decode_any W_c5f3c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f40 : bv 32 := 0x0025c803.
Lemma F_c5f40 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64b0 : word) = Some W_c5f40.
Proof. vm_refl. Qed.
Lemma D_c5f40 : decode_any W_c5f40 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f44 : bv 32 := 0x0035c883.
Lemma F_c5f44 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64b4 : word) = Some W_c5f44.
Proof. vm_refl. Qed.
Lemma D_c5f44 : decode_any W_c5f44 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f48 : bv 32 := 0x0045c283.
Lemma F_c5f48 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64b8 : word) = Some W_c5f48.
Proof. vm_refl. Qed.
Lemma D_c5f48 : decode_any W_c5f48 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f4c : bv 32 := 0x0055c303.
Lemma F_c5f4c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64bc : word) = Some W_c5f4c.
Proof. vm_refl. Qed.
Lemma D_c5f4c : decode_any W_c5f4c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f50 : bv 32 := 0x0065c383.
Lemma F_c5f50 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64c0 : word) = Some W_c5f50.
Proof. vm_refl. Qed.
Lemma D_c5f50 : decode_any W_c5f50 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f54 : bv 32 := 0x0075ce03.
Lemma F_c5f54 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64c4 : word) = Some W_c5f54.
Proof. vm_refl. Qed.
Lemma D_c5f54 : decode_any W_c5f54 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f58 : bv 32 := 0x00858593.
Lemma F_c5f58 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64c8 : word) = Some W_c5f58.
Proof. vm_refl. Qed.
Lemma D_c5f58 : decode_any W_c5f58 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f5c : bv 32 := 0x00e68023.
Lemma F_c5f5c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64cc : word) = Some W_c5f5c.
Proof. vm_refl. Qed.
Lemma D_c5f5c : decode_any W_c5f5c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f60 : bv 32 := 0x00f680a3.
Lemma F_c5f60 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64d0 : word) = Some W_c5f60.
Proof. vm_refl. Qed.
Lemma D_c5f60 : decode_any W_c5f60 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f64 : bv 32 := 0x01068123.
Lemma F_c5f64 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64d4 : word) = Some W_c5f64.
Proof. vm_refl. Qed.
Lemma D_c5f64 : decode_any W_c5f64 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f68 : bv 32 := 0x011681a3.
Lemma F_c5f68 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64d8 : word) = Some W_c5f68.
Proof. vm_refl. Qed.
Lemma D_c5f68 : decode_any W_c5f68 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f6c : bv 32 := 0x00868713.
Lemma F_c5f6c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64dc : word) = Some W_c5f6c.
Proof. vm_refl. Qed.
Lemma D_c5f6c : decode_any W_c5f6c = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f70 : bv 32 := 0x00568223.
Lemma F_c5f70 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64e0 : word) = Some W_c5f70.
Proof. vm_refl. Qed.
Lemma D_c5f70 : decode_any W_c5f70 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f74 : bv 32 := 0x006682a3.
Lemma F_c5f74 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64e4 : word) = Some W_c5f74.
Proof. vm_refl. Qed.
Lemma D_c5f74 : decode_any W_c5f74 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f78 : bv 32 := 0x00768323.
Lemma F_c5f78 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64e8 : word) = Some W_c5f78.
Proof. vm_refl. Qed.
Lemma D_c5f78 : decode_any W_c5f78 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f7c : bv 32 := 0x01c683a3.
Lemma F_c5f7c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64ec : word) = Some W_c5f7c.
Proof. vm_refl. Qed.
Lemma D_c5f7c : decode_any W_c5f7c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f80 : bv 32 := 0x00070693.
Lemma F_c5f80 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64f0 : word) = Some W_c5f80.
Proof. vm_refl. Qed.
Lemma D_c5f80 : decode_any W_c5f80 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f84 : bv 32 := 0x00467713.
Lemma F_c5f84 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64f4 : word) = Some W_c5f84.
Proof. vm_refl. Qed.
Lemma D_c5f84 : decode_any W_c5f84 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f88 : bv 32 := 0x02070863.
Lemma F_c5f88 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64f8 : word) = Some W_c5f88.
Proof. vm_refl. Qed.
Lemma D_c5f88 : decode_any W_c5f88 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f8c : bv 32 := 0x0005c703.
Lemma F_c5f8c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc64fc : word) = Some W_c5f8c.
Proof. vm_refl. Qed.
Lemma D_c5f8c : decode_any W_c5f8c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f90 : bv 32 := 0x0015c783.
Lemma F_c5f90 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6500 : word) = Some W_c5f90.
Proof. vm_refl. Qed.
Lemma D_c5f90 : decode_any W_c5f90 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f94 : bv 32 := 0x0025c803.
Lemma F_c5f94 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6504 : word) = Some W_c5f94.
Proof. vm_refl. Qed.
Lemma D_c5f94 : decode_any W_c5f94 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f98 : bv 32 := 0x0035c883.
Lemma F_c5f98 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6508 : word) = Some W_c5f98.
Proof. vm_refl. Qed.
Lemma D_c5f98 : decode_any W_c5f98 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5f9c : bv 32 := 0x00458593.
Lemma F_c5f9c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc650c : word) = Some W_c5f9c.
Proof. vm_refl. Qed.
Lemma D_c5f9c : decode_any W_c5f9c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fa0 : bv 32 := 0x00468293.
Lemma F_c5fa0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6510 : word) = Some W_c5fa0.
Proof. vm_refl. Qed.
Lemma D_c5fa0 : decode_any W_c5fa0 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fa4 : bv 32 := 0x00e68023.
Lemma F_c5fa4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6514 : word) = Some W_c5fa4.
Proof. vm_refl. Qed.
Lemma D_c5fa4 : decode_any W_c5fa4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fa8 : bv 32 := 0x00f680a3.
Lemma F_c5fa8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6518 : word) = Some W_c5fa8.
Proof. vm_refl. Qed.
Lemma D_c5fa8 : decode_any W_c5fa8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fac : bv 32 := 0x01068123.
Lemma F_c5fac : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc651c : word) = Some W_c5fac.
Proof. vm_refl. Qed.
Lemma D_c5fac : decode_any W_c5fac = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fb0 : bv 32 := 0x011681a3.
Lemma F_c5fb0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6520 : word) = Some W_c5fb0.
Proof. vm_refl. Qed.
Lemma D_c5fb0 : decode_any W_c5fb0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fb4 : bv 32 := 0x00028693.
Lemma F_c5fb4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6524 : word) = Some W_c5fb4.
Proof. vm_refl. Qed.
Lemma D_c5fb4 : decode_any W_c5fb4 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fb8 : bv 32 := 0x00267713.
Lemma F_c5fb8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6528 : word) = Some W_c5fb8.
Proof. vm_refl. Qed.
Lemma D_c5fb8 : decode_any W_c5fb8 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fbc : bv 32 := 0x00071863.
Lemma F_c5fbc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc652c : word) = Some W_c5fbc.
Proof. vm_refl. Qed.
Lemma D_c5fbc : decode_any W_c5fbc = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fc0 : bv 32 := 0x00167613.
Lemma F_c5fc0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6530 : word) = Some W_c5fc0.
Proof. vm_refl. Qed.
Lemma D_c5fc0 : decode_any W_c5fc0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fc4 : bv 32 := 0x02061663.
Lemma F_c5fc4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6534 : word) = Some W_c5fc4.
Proof. vm_refl. Qed.
Lemma D_c5fc4 : decode_any W_c5fc4 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fc8 : bv 32 := 0x00008067.
Lemma F_c5fc8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6538 : word) = Some W_c5fc8.
Proof. vm_refl. Qed.
Lemma D_c5fc8 : decode_any W_c5fc8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fcc : bv 32 := 0x0005c703.
Lemma F_c5fcc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc653c : word) = Some W_c5fcc.
Proof. vm_refl. Qed.
Lemma D_c5fcc : decode_any W_c5fcc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fd0 : bv 32 := 0x0015c783.
Lemma F_c5fd0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6540 : word) = Some W_c5fd0.
Proof. vm_refl. Qed.
Lemma D_c5fd0 : decode_any W_c5fd0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fd4 : bv 32 := 0x00258593.
Lemma F_c5fd4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6544 : word) = Some W_c5fd4.
Proof. vm_refl. Qed.
Lemma D_c5fd4 : decode_any W_c5fd4 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fd8 : bv 32 := 0x00268813.
Lemma F_c5fd8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6548 : word) = Some W_c5fd8.
Proof. vm_refl. Qed.
Lemma D_c5fd8 : decode_any W_c5fd8 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fdc : bv 32 := 0x00e68023.
Lemma F_c5fdc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc654c : word) = Some W_c5fdc.
Proof. vm_refl. Qed.
Lemma D_c5fdc : decode_any W_c5fdc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fe0 : bv 32 := 0x00f680a3.
Lemma F_c5fe0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6550 : word) = Some W_c5fe0.
Proof. vm_refl. Qed.
Lemma D_c5fe0 : decode_any W_c5fe0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fe4 : bv 32 := 0x00080693.
Lemma F_c5fe4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6554 : word) = Some W_c5fe4.
Proof. vm_refl. Qed.
Lemma D_c5fe4 : decode_any W_c5fe4 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fe8 : bv 32 := 0x00167613.
Lemma F_c5fe8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6558 : word) = Some W_c5fe8.
Proof. vm_refl. Qed.
Lemma D_c5fe8 : decode_any W_c5fe8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5fec : bv 32 := 0xfc060ee3.
Lemma F_c5fec : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc655c : word) = Some W_c5fec.
Proof. vm_refl. Qed.
Lemma D_c5fec : decode_any W_c5fec = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ff0 : bv 32 := 0x0005c583.
Lemma F_c5ff0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6560 : word) = Some W_c5ff0.
Proof. vm_refl. Qed.
Lemma D_c5ff0 : decode_any W_c5ff0 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ff4 : bv 32 := 0x00b68023.
Lemma F_c5ff4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6564 : word) = Some W_c5ff4.
Proof. vm_refl. Qed.
Lemma D_c5ff4 : decode_any W_c5ff4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c5ff8 : bv 32 := 0x00008067.
Lemma F_c5ff8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6568 : word) = Some W_c5ff8.
Proof. vm_refl. Qed.
Lemma D_c5ff8 : decode_any W_c5ff8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
