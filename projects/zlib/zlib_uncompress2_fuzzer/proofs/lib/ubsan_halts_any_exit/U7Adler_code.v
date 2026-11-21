(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_17c88 : bv 32 := 0xf8010113.
Lemma F_17c88 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17da0 : word) = Some W_17c88.
Proof. vm_refl. Qed.
Lemma D_17c88 : decode_any W_17c88 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_17c8c : bv 32 := 0x06113c23.
Lemma F_17c8c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17da4 : word) = Some W_17c8c.
Proof. vm_refl. Qed.
Lemma D_17c8c : decode_any W_17c8c = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_17c90 : bv 32 := 0x06813823.
Lemma F_17c90 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17da8 : word) = Some W_17c90.
Proof. vm_refl. Qed.
Lemma D_17c90 : decode_any W_17c90 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_17c94 : bv 32 := 0x06913423.
Lemma F_17c94 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17dac : word) = Some W_17c94.
Proof. vm_refl. Qed.
Lemma D_17c94 : decode_any W_17c94 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_17c98 : bv 32 := 0x07213023.
Lemma F_17c98 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17db0 : word) = Some W_17c98.
Proof. vm_refl. Qed.
Lemma D_17c98 : decode_any W_17c98 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_17c9c : bv 32 := 0x05313c23.
Lemma F_17c9c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17db4 : word) = Some W_17c9c.
Proof. vm_refl. Qed.
Lemma D_17c9c : decode_any W_17c9c = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ca0 : bv 32 := 0x05413823.
Lemma F_17ca0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17db8 : word) = Some W_17ca0.
Proof. vm_refl. Qed.
Lemma D_17ca0 : decode_any W_17ca0 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ca4 : bv 32 := 0x05513423.
Lemma F_17ca4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17dbc : word) = Some W_17ca4.
Proof. vm_refl. Qed.
Lemma D_17ca4 : decode_any W_17ca4 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ca8 : bv 32 := 0x05613023.
Lemma F_17ca8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17dc0 : word) = Some W_17ca8.
Proof. vm_refl. Qed.
Lemma D_17ca8 : decode_any W_17ca8 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cac : bv 32 := 0x03713c23.
Lemma F_17cac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17dc4 : word) = Some W_17cac.
Proof. vm_refl. Qed.
Lemma D_17cac : decode_any W_17cac = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cb0 : bv 32 := 0x03813823.
Lemma F_17cb0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17dc8 : word) = Some W_17cb0.
Proof. vm_refl. Qed.
Lemma D_17cb0 : decode_any W_17cb0 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cb4 : bv 32 := 0x03913423.
Lemma F_17cb4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17dcc : word) = Some W_17cb4.
Proof. vm_refl. Qed.
Lemma D_17cb4 : decode_any W_17cb4 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cb8 : bv 32 := 0x03a13023.
Lemma F_17cb8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17dd0 : word) = Some W_17cb8.
Proof. vm_refl. Qed.
Lemma D_17cb8 : decode_any W_17cb8 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cbc : bv 32 := 0x01b13c23.
Lemma F_17cbc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17dd4 : word) = Some W_17cbc.
Proof. vm_refl. Qed.
Lemma D_17cbc : decode_any W_17cbc = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cc0 : bv 32 := 0x0105569b.
Lemma F_17cc0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17dd8 : word) = Some W_17cc0.
Proof. vm_refl. Qed.
Lemma D_17cc0 : decode_any W_17cc0 = Some (ShiftImm32 ALU_SRL 13 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cc4 : bv 32 := 0x03051713.
Lemma F_17cc4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ddc : word) = Some W_17cc4.
Proof. vm_refl. Qed.
Lemma D_17cc4 : decode_any W_17cc4 = Some (ShiftImm ALU_SLL 14 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cc8 : bv 32 := 0x00100513.
Lemma F_17cc8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17de0 : word) = Some W_17cc8.
Proof. vm_refl. Qed.
Lemma D_17cc8 : decode_any W_17cc8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ccc : bv 32 := 0x03075713.
Lemma F_17ccc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17de4 : word) = Some W_17ccc.
Proof. vm_refl. Qed.
Lemma D_17ccc : decode_any W_17ccc = Some (ShiftImm ALU_SRL 14 14 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cd0 : bv 32 := 0x04a61c63.
Lemma F_17cd0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17de8 : word) = Some W_17cd0.
Proof. vm_refl. Qed.
Lemma D_17cd0 : decode_any W_17cd0 = Some (Branch BC_NE 12 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cd4 : bv 32 := 0x4e058063.
Lemma F_17cd4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17dec : word) = Some W_17cd4.
Proof. vm_refl. Qed.
Lemma D_17cd4 : decode_any W_17cd4 = Some (Branch BC_EQ 11 0 1248, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cd8 : bv 32 := 0x0005c503.
Lemma F_17cd8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17df0 : word) = Some W_17cd8.
Proof. vm_refl. Qed.
Lemma D_17cd8 : decode_any W_17cd8 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cdc : bv 32 := 0x000105b7.
Lemma F_17cdc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17df4 : word) = Some W_17cdc.
Proof. vm_refl. Qed.
Lemma D_17cdc : decode_any W_17cdc = Some (Lui 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ce0 : bv 32 := 0xffff0637.
Lemma F_17ce0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17df8 : word) = Some W_17ce0.
Proof. vm_refl. Qed.
Lemma D_17ce0 : decode_any W_17ce0 = Some (Lui 12 1048560, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ce4 : bv 32 := 0xff05859b.
Lemma F_17ce4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17dfc : word) = Some W_17ce4.
Proof. vm_refl. Qed.
Lemma D_17ce4 : decode_any W_17ce4 = Some (OpImm32 11 11 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ce8 : bv 32 := 0x00f6061b.
Lemma F_17ce8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e00 : word) = Some W_17ce8.
Proof. vm_refl. Qed.
Lemma D_17ce8 : decode_any W_17ce8 = Some (OpImm32 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cec : bv 32 := 0x00a70533.
Lemma F_17cec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e04 : word) = Some W_17cec.
Proof. vm_refl. Qed.
Lemma D_17cec : decode_any W_17cec = Some (Op ALU_ADD 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cf0 : bv 32 := 0x00a5b733.
Lemma F_17cf0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e08 : word) = Some W_17cf0.
Proof. vm_refl. Qed.
Lemma D_17cf0 : decode_any W_17cf0 = Some (Op ALU_SLTU 14 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cf4 : bv 32 := 0x40e00733.
Lemma F_17cf4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e0c : word) = Some W_17cf4.
Proof. vm_refl. Qed.
Lemma D_17cf4 : decode_any W_17cf4 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cf8 : bv 32 := 0x00c77633.
Lemma F_17cf8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e10 : word) = Some W_17cf8.
Proof. vm_refl. Qed.
Lemma D_17cf8 : decode_any W_17cf8 = Some (Op ALU_AND 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17cfc : bv 32 := 0xf000f737.
Lemma F_17cfc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e14 : word) = Some W_17cfc.
Proof. vm_refl. Qed.
Lemma D_17cfc : decode_any W_17cfc = Some (Lui 14 983055, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d00 : bv 32 := 0x00c50533.
Lemma F_17d00 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e18 : word) = Some W_17d00.
Proof. vm_refl. Qed.
Lemma D_17d00 : decode_any W_17d00 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d04 : bv 32 := 0x00d506b3.
Lemma F_17d04 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e1c : word) = Some W_17d04.
Proof. vm_refl. Qed.
Lemma D_17d04 : decode_any W_17d04 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d08 : bv 32 := 0x00d5b5b3.
Lemma F_17d08 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e20 : word) = Some W_17d08.
Proof. vm_refl. Qed.
Lemma D_17d08 : decode_any W_17d08 = Some (Op ALU_SLTU 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d0c : bv 32 := 0x01069693.
Lemma F_17d0c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e24 : word) = Some W_17d0c.
Proof. vm_refl. Qed.
Lemma D_17d0c : decode_any W_17d0c = Some (ShiftImm ALU_SLL 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d10 : bv 32 := 0x40b005b3.
Lemma F_17d10 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e28 : word) = Some W_17d10.
Proof. vm_refl. Qed.
Lemma D_17d10 : decode_any W_17d10 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d14 : bv 32 := 0x00471713.
Lemma F_17d14 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e2c : word) = Some W_17d14.
Proof. vm_refl. Qed.
Lemma D_17d14 : decode_any W_17d14 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d18 : bv 32 := 0x00e5f5b3.
Lemma F_17d18 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e30 : word) = Some W_17d18.
Proof. vm_refl. Qed.
Lemma D_17d18 : decode_any W_17d18 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d1c : bv 32 := 0x00b685b3.
Lemma F_17d1c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e34 : word) = Some W_17d1c.
Proof. vm_refl. Qed.
Lemma D_17d1c : decode_any W_17d1c = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d20 : bv 32 := 0x00a5e533.
Lemma F_17d20 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e38 : word) = Some W_17d20.
Proof. vm_refl. Qed.
Lemma D_17d20 : decode_any W_17d20 = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d24 : bv 32 := 0x4540006f.
Lemma F_17d24 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e3c : word) = Some W_17d24.
Proof. vm_refl. Qed.
Lemma D_17d24 : decode_any W_17d24 = Some (Jal 0 1108, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d28 : bv 32 := 0x44058863.
Lemma F_17d28 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e40 : word) = Some W_17d28.
Proof. vm_refl. Qed.
Lemma D_17d28 : decode_any W_17d28 = Some (Branch BC_EQ 11 0 1104, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d2c : bv 32 := 0x01000513.
Lemma F_17d2c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e44 : word) = Some W_17d2c.
Proof. vm_refl. Qed.
Lemma D_17d2c : decode_any W_17d2c = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d30 : bv 32 := 0x08a67a63.
Lemma F_17d30 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e48 : word) = Some W_17d30.
Proof. vm_refl. Qed.
Lemma D_17d30 : decode_any W_17d30 = Some (Branch BC_GEU 12 10 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d34 : bv 32 := 0x02060e63.
Lemma F_17d34 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e4c : word) = Some W_17d34.
Proof. vm_refl. Qed.
Lemma D_17d34 : decode_any W_17d34 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d38 : bv 32 := 0xfff5c513.
Lemma F_17d38 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e50 : word) = Some W_17d38.
Proof. vm_refl. Qed.
Lemma D_17d38 : decode_any W_17d38 = Some (OpImm ALU_XOR 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d3c : bv 32 := 0xfff60613.
Lemma F_17d3c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e54 : word) = Some W_17d3c.
Proof. vm_refl. Qed.
Lemma D_17d3c : decode_any W_17d3c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d40 : bv 32 := 0x00c56463.
Lemma F_17d40 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e58 : word) = Some W_17d40.
Proof. vm_refl. Qed.
Lemma D_17d40 : decode_any W_17d40 = Some (Branch BC_LTU 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d44 : bv 32 := 0x00060513.
Lemma F_17d44 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e5c : word) = Some W_17d44.
Proof. vm_refl. Qed.
Lemma D_17d44 : decode_any W_17d44 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d48 : bv 32 := 0x00b50533.
Lemma F_17d48 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e60 : word) = Some W_17d48.
Proof. vm_refl. Qed.
Lemma D_17d48 : decode_any W_17d48 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d4c : bv 32 := 0x00150513.
Lemma F_17d4c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e64 : word) = Some W_17d4c.
Proof. vm_refl. Qed.
Lemma D_17d4c : decode_any W_17d4c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d50 : bv 32 := 0xfff00613.
Lemma F_17d50 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e68 : word) = Some W_17d50.
Proof. vm_refl. Qed.
Lemma D_17d50 : decode_any W_17d50 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d54 : bv 32 := 0x46c58063.
Lemma F_17d54 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e6c : word) = Some W_17d54.
Proof. vm_refl. Qed.
Lemma D_17d54 : decode_any W_17d54 = Some (Branch BC_EQ 11 12 1120, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d58 : bv 32 := 0x0005c783.
Lemma F_17d58 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e70 : word) = Some W_17d58.
Proof. vm_refl. Qed.
Lemma D_17d58 : decode_any W_17d58 = Some (Load SZ1 false 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d5c : bv 32 := 0x00158813.
Lemma F_17d5c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e74 : word) = Some W_17d5c.
Proof. vm_refl. Qed.
Lemma D_17d5c : decode_any W_17d5c = Some (OpImm ALU_ADD 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d60 : bv 32 := 0x00f70733.
Lemma F_17d60 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e78 : word) = Some W_17d60.
Proof. vm_refl. Qed.
Lemma D_17d60 : decode_any W_17d60 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d64 : bv 32 := 0x00d706b3.
Lemma F_17d64 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e7c : word) = Some W_17d64.
Proof. vm_refl. Qed.
Lemma D_17d64 : decode_any W_17d64 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d68 : bv 32 := 0x00080593.
Lemma F_17d68 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e80 : word) = Some W_17d68.
Proof. vm_refl. Qed.
Lemma D_17d68 : decode_any W_17d68 = Some (OpImm ALU_ADD 11 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d6c : bv 32 := 0xfea814e3.
Lemma F_17d6c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e84 : word) = Some W_17d6c.
Proof. vm_refl. Qed.
Lemma D_17d6c : decode_any W_17d6c = Some (Branch BC_NE 16 10 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d70 : bv 32 := 0x00010537.
Lemma F_17d70 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e88 : word) = Some W_17d70.
Proof. vm_refl. Qed.
Lemma D_17d70 : decode_any W_17d70 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d74 : bv 32 := 0xffff05b7.
Lemma F_17d74 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e8c : word) = Some W_17d74.
Proof. vm_refl. Qed.
Lemma D_17d74 : decode_any W_17d74 = Some (Lui 11 1048560, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d78 : bv 32 := 0xffff8617.
Lemma F_17d78 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e90 : word) = Some W_17d78.
Proof. vm_refl. Qed.
Lemma D_17d78 : decode_any W_17d78 = Some (Auipc 12 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d7c : bv 32 := 0xff05079b.
Lemma F_17d7c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e94 : word) = Some W_17d7c.
Proof. vm_refl. Qed.
Lemma D_17d7c : decode_any W_17d7c = Some (OpImm32 15 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d80 : bv 32 := 0x00f5859b.
Lemma F_17d80 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e98 : word) = Some W_17d80.
Proof. vm_refl. Qed.
Lemma D_17d80 : decode_any W_17d80 = Some (OpImm32 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d84 : bv 32 := 0x6d863603.
Lemma F_17d84 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17e9c : word) = Some W_17d84.
Proof. vm_refl. Qed.
Lemma D_17d84 : decode_any W_17d84 = Some (Load SZ8 true 12 12 1752, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d88 : bv 32 := 0x00e7b7b3.
Lemma F_17d88 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ea0 : word) = Some W_17d88.
Proof. vm_refl. Qed.
Lemma D_17d88 : decode_any W_17d88 = Some (Op ALU_SLTU 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d8c : bv 32 := 0x40f007b3.
Lemma F_17d8c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ea4 : word) = Some W_17d8c.
Proof. vm_refl. Qed.
Lemma D_17d8c : decode_any W_17d8c = Some (Op ALU_SUB 15 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d90 : bv 32 := 0x00b7f5b3.
Lemma F_17d90 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ea8 : word) = Some W_17d90.
Proof. vm_refl. Qed.
Lemma D_17d90 : decode_any W_17d90 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d94 : bv 32 := 0x00b705b3.
Lemma F_17d94 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17eac : word) = Some W_17d94.
Proof. vm_refl. Qed.
Lemma D_17d94 : decode_any W_17d94 = Some (Op ALU_ADD 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d98 : bv 32 := 0x02c6b633.
Lemma F_17d98 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17eb0 : word) = Some W_17d98.
Proof. vm_refl. Qed.
Lemma D_17d98 : decode_any W_17d98 = Some (Mul M_MULHU 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17d9c : bv 32 := 0x40c68733.
Lemma F_17d9c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17eb4 : word) = Some W_17d9c.
Proof. vm_refl. Qed.
Lemma D_17d9c : decode_any W_17d9c = Some (Op ALU_SUB 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17da0 : bv 32 := 0x00175713.
Lemma F_17da0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17eb8 : word) = Some W_17da0.
Proof. vm_refl. Qed.
Lemma D_17da0 : decode_any W_17da0 = Some (ShiftImm ALU_SRL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17da4 : bv 32 := 0x00c70633.
Lemma F_17da4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ebc : word) = Some W_17da4.
Proof. vm_refl. Qed.
Lemma D_17da4 : decode_any W_17da4 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17da8 : bv 32 := 0x00f65613.
Lemma F_17da8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ec0 : word) = Some W_17da8.
Proof. vm_refl. Qed.
Lemma D_17da8 : decode_any W_17da8 = Some (ShiftImm ALU_SRL 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dac : bv 32 := 0xff15051b.
Lemma F_17dac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ec4 : word) = Some W_17dac.
Proof. vm_refl. Qed.
Lemma D_17dac : decode_any W_17dac = Some (OpImm32 10 10 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_17db0 : bv 32 := 0x02a60533.
Lemma F_17db0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ec8 : word) = Some W_17db0.
Proof. vm_refl. Qed.
Lemma D_17db0 : decode_any W_17db0 = Some (Mul M_MUL 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_17db4 : bv 32 := 0x40a686b3.
Lemma F_17db4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ecc : word) = Some W_17db4.
Proof. vm_refl. Qed.
Lemma D_17db4 : decode_any W_17db4 = Some (Op ALU_SUB 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_17db8 : bv 32 := 0x01069513.
Lemma F_17db8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ed0 : word) = Some W_17db8.
Proof. vm_refl. Qed.
Lemma D_17db8 : decode_any W_17db8 = Some (ShiftImm ALU_SLL 10 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dbc : bv 32 := 0x00b56533.
Lemma F_17dbc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ed4 : word) = Some W_17dbc.
Proof. vm_refl. Qed.
Lemma D_17dbc : decode_any W_17dbc = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dc0 : bv 32 := 0x3b80006f.
Lemma F_17dc0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ed8 : word) = Some W_17dc0.
Proof. vm_refl. Qed.
Lemma D_17dc0 : decode_any W_17dc0 = Some (Jal 0 952, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dc4 : bv 32 := 0x00465513.
Lemma F_17dc4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17edc : word) = Some W_17dc4.
Proof. vm_refl. Qed.
Lemma D_17dc4 : decode_any W_17dc4 = Some (ShiftImm ALU_SRL 10 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dc8 : bv 32 := 0x15b00793.
Lemma F_17dc8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ee0 : word) = Some W_17dc8.
Proof. vm_refl. Qed.
Lemma D_17dc8 : decode_any W_17dc8 = Some (OpImm ALU_ADD 15 0 347, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dcc : bv 32 := 0x1ef56063.
Lemma F_17dcc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ee4 : word) = Some W_17dcc.
Proof. vm_refl. Qed.
Lemma D_17dcc : decode_any W_17dcc = Some (Branch BC_LTU 10 15 480, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dd0 : bv 32 := 0xfffffab7.
Lemma F_17dd0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ee8 : word) = Some W_17dd0.
Proof. vm_refl. Qed.
Lemma D_17dd0 : decode_any W_17dd0 = Some (Lui 21 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dd4 : bv 32 := 0x00001b37.
Lemma F_17dd4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17eec : word) = Some W_17dd4.
Proof. vm_refl. Qed.
Lemma D_17dd4 : decode_any W_17dd4 = Some (Lui 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dd8 : bv 32 := 0xfff00513.
Lemma F_17dd8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ef0 : word) = Some W_17dd8.
Proof. vm_refl. Qed.
Lemma D_17dd8 : decode_any W_17dd8 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ddc : bv 32 := 0xffd00793.
Lemma F_17ddc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ef4 : word) = Some W_17ddc.
Proof. vm_refl. Qed.
Lemma D_17ddc : decode_any W_17ddc = Some (OpImm ALU_ADD 15 0 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_17de0 : bv 32 := 0xffc00813.
Lemma F_17de0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ef8 : word) = Some W_17de0.
Proof. vm_refl. Qed.
Lemma D_17de0 : decode_any W_17de0 = Some (OpImm ALU_ADD 16 0 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_17de4 : bv 32 := 0xffb00893.
Lemma F_17de4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17efc : word) = Some W_17de4.
Proof. vm_refl. Qed.
Lemma D_17de4 : decode_any W_17de4 = Some (OpImm ALU_ADD 17 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_17de8 : bv 32 := 0xffa00293.
Lemma F_17de8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f00 : word) = Some W_17de8.
Proof. vm_refl. Qed.
Lemma D_17de8 : decode_any W_17de8 = Some (OpImm ALU_ADD 5 0 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dec : bv 32 := 0xff900313.
Lemma F_17dec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f04 : word) = Some W_17dec.
Proof. vm_refl. Qed.
Lemma D_17dec : decode_any W_17dec = Some (OpImm ALU_ADD 6 0 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_17df0 : bv 32 := 0xff800393.
Lemma F_17df0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f08 : word) = Some W_17df0.
Proof. vm_refl. Qed.
Lemma D_17df0 : decode_any W_17df0 = Some (OpImm ALU_ADD 7 0 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_17df4 : bv 32 := 0xff700e13.
Lemma F_17df4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f0c : word) = Some W_17df4.
Proof. vm_refl. Qed.
Lemma D_17df4 : decode_any W_17df4 = Some (OpImm ALU_ADD 28 0 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_17df8 : bv 32 := 0xff600e93.
Lemma F_17df8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f10 : word) = Some W_17df8.
Proof. vm_refl. Qed.
Lemma D_17df8 : decode_any W_17df8 = Some (OpImm ALU_ADD 29 0 4086, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dfc : bv 32 := 0xff500f13.
Lemma F_17dfc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f14 : word) = Some W_17dfc.
Proof. vm_refl. Qed.
Lemma D_17dfc : decode_any W_17dfc = Some (OpImm ALU_ADD 30 0 4085, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e00 : bv 32 := 0xff400f93.
Lemma F_17e00 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f18 : word) = Some W_17e00.
Proof. vm_refl. Qed.
Lemma D_17e00 : decode_any W_17e00 = Some (OpImm ALU_ADD 31 0 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e04 : bv 32 := 0xff300413.
Lemma F_17e04 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f1c : word) = Some W_17e04.
Proof. vm_refl. Qed.
Lemma D_17e04 : decode_any W_17e04 = Some (OpImm ALU_ADD 8 0 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e08 : bv 32 := 0xff200493.
Lemma F_17e08 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f20 : word) = Some W_17e08.
Proof. vm_refl. Qed.
Lemma D_17e08 : decode_any W_17e08 = Some (OpImm ALU_ADD 9 0 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e0c : bv 32 := 0xff100913.
Lemma F_17e0c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f24 : word) = Some W_17e0c.
Proof. vm_refl. Qed.
Lemma D_17e0c : decode_any W_17e0c = Some (OpImm ALU_ADD 18 0 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e10 : bv 32 := 0xff000993.
Lemma F_17e10 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f28 : word) = Some W_17e10.
Proof. vm_refl. Qed.
Lemma D_17e10 : decode_any W_17e10 = Some (OpImm ALU_ADD 19 0 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e14 : bv 32 := 0xfef00a13.
Lemma F_17e14 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f2c : word) = Some W_17e14.
Proof. vm_refl. Qed.
Lemma D_17e14 : decode_any W_17e14 = Some (OpImm ALU_ADD 20 0 4079, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e18 : bv 32 := 0xffff8b97.
Lemma F_17e18 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f30 : word) = Some W_17e18.
Proof. vm_refl. Qed.
Lemma D_17e18 : decode_any W_17e18 = Some (Auipc 23 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e1c : bv 32 := 0xa50a8a9b.
Lemma F_17e1c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f34 : word) = Some W_17e1c.
Proof. vm_refl. Qed.
Lemma D_17e1c : decode_any W_17e1c = Some (OpImm32 21 21 2640, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e20 : bv 32 := 0x01513823.
Lemma F_17e20 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f38 : word) = Some W_17e20.
Proof. vm_refl. Qed.
Lemma D_17e20 : decode_any W_17e20 = Some (Store SZ8 2 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e24 : bv 32 := 0x5b0b0a9b.
Lemma F_17e24 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f3c : word) = Some W_17e24.
Proof. vm_refl. Qed.
Lemma D_17e24 : decode_any W_17e24 = Some (OpImm32 21 22 1456, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e28 : bv 32 := 0x01513423.
Lemma F_17e28 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f40 : word) = Some W_17e28.
Proof. vm_refl. Qed.
Lemma D_17e28 : decode_any W_17e28 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e2c : bv 32 := 0x638bbb83.
Lemma F_17e2c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f44 : word) = Some W_17e2c.
Proof. vm_refl. Qed.
Lemma D_17e2c : decode_any W_17e2c = Some (Load SZ8 true 23 23 1592, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e30 : bv 32 := 0x00010c37.
Lemma F_17e30 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f48 : word) = Some W_17e30.
Proof. vm_refl. Qed.
Lemma D_17e30 : decode_any W_17e30 = Some (Lui 24 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e34 : bv 32 := 0xff1c0c1b.
Lemma F_17e34 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f4c : word) = Some W_17e34.
Proof. vm_refl. Qed.
Lemma D_17e34 : decode_any W_17e34 = Some (OpImm32 24 24 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e38 : bv 32 := 0x00058d13.
Lemma F_17e38 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f50 : word) = Some W_17e38.
Proof. vm_refl. Qed.
Lemma D_17e38 : decode_any W_17e38 = Some (OpImm ALU_ADD 26 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e3c : bv 32 := 0x01013583.
Lemma F_17e3c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f54 : word) = Some W_17e3c.
Proof. vm_refl. Qed.
Lemma D_17e3c : decode_any W_17e3c = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e40 : bv 32 := 0x00b60633.
Lemma F_17e40 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f58 : word) = Some W_17e40.
Proof. vm_refl. Qed.
Lemma D_17e40 : decode_any W_17e40 = Some (Op ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e44 : bv 32 := 0x00813583.
Lemma F_17e44 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f5c : word) = Some W_17e44.
Proof. vm_refl. Qed.
Lemma D_17e44 : decode_any W_17e44 = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e48 : bv 32 := 0x00bd05b3.
Lemma F_17e48 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f60 : word) = Some W_17e48.
Proof. vm_refl. Qed.
Lemma D_17e48 : decode_any W_17e48 = Some (Op ALU_ADD 11 26 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e4c : bv 32 := 0xea500d93.
Lemma F_17e4c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f64 : word) = Some W_17e4c.
Proof. vm_refl. Qed.
Lemma D_17e4c : decode_any W_17e4c = Some (OpImm ALU_ADD 27 0 3749, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e50 : bv 32 := 0x36ad0263.
Lemma F_17e50 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f68 : word) = Some W_17e50.
Proof. vm_refl. Qed.
Lemma D_17e50 : decode_any W_17e50 = Some (Branch BC_EQ 26 10 868, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e54 : bv 32 := 0x37a7e063.
Lemma F_17e54 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f6c : word) = Some W_17e54.
Proof. vm_refl. Qed.
Lemma D_17e54 : decode_any W_17e54 = Some (Branch BC_LTU 15 26 864, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e58 : bv 32 := 0x35a86e63.
Lemma F_17e58 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f70 : word) = Some W_17e58.
Proof. vm_refl. Qed.
Lemma D_17e58 : decode_any W_17e58 = Some (Branch BC_LTU 16 26 860, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e5c : bv 32 := 0x35a8ec63.
Lemma F_17e5c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f74 : word) = Some W_17e5c.
Proof. vm_refl. Qed.
Lemma D_17e5c : decode_any W_17e5c = Some (Branch BC_LTU 17 26 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e60 : bv 32 := 0x35a2ea63.
Lemma F_17e60 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f78 : word) = Some W_17e60.
Proof. vm_refl. Qed.
Lemma D_17e60 : decode_any W_17e60 = Some (Branch BC_LTU 5 26 852, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e64 : bv 32 := 0x35a36863.
Lemma F_17e64 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f7c : word) = Some W_17e64.
Proof. vm_refl. Qed.
Lemma D_17e64 : decode_any W_17e64 = Some (Branch BC_LTU 6 26 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e68 : bv 32 := 0x35a3e663.
Lemma F_17e68 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f80 : word) = Some W_17e68.
Proof. vm_refl. Qed.
Lemma D_17e68 : decode_any W_17e68 = Some (Branch BC_LTU 7 26 844, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e6c : bv 32 := 0x35ae6463.
Lemma F_17e6c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f84 : word) = Some W_17e6c.
Proof. vm_refl. Qed.
Lemma D_17e6c : decode_any W_17e6c = Some (Branch BC_LTU 28 26 840, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e70 : bv 32 := 0x35aee263.
Lemma F_17e70 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f88 : word) = Some W_17e70.
Proof. vm_refl. Qed.
Lemma D_17e70 : decode_any W_17e70 = Some (Branch BC_LTU 29 26 836, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e74 : bv 32 := 0x35af6063.
Lemma F_17e74 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f8c : word) = Some W_17e74.
Proof. vm_refl. Qed.
Lemma D_17e74 : decode_any W_17e74 = Some (Branch BC_LTU 30 26 832, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e78 : bv 32 := 0x33afee63.
Lemma F_17e78 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f90 : word) = Some W_17e78.
Proof. vm_refl. Qed.
Lemma D_17e78 : decode_any W_17e78 = Some (Branch BC_LTU 31 26 828, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e7c : bv 32 := 0x33a46c63.
Lemma F_17e7c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f94 : word) = Some W_17e7c.
Proof. vm_refl. Qed.
Lemma D_17e7c : decode_any W_17e7c = Some (Branch BC_LTU 8 26 824, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e80 : bv 32 := 0x33a4ea63.
Lemma F_17e80 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f98 : word) = Some W_17e80.
Proof. vm_refl. Qed.
Lemma D_17e80 : decode_any W_17e80 = Some (Branch BC_LTU 9 26 820, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e84 : bv 32 := 0x33a96863.
Lemma F_17e84 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17f9c : word) = Some W_17e84.
Proof. vm_refl. Qed.
Lemma D_17e84 : decode_any W_17e84 = Some (Branch BC_LTU 18 26 816, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e88 : bv 32 := 0x33a9e663.
Lemma F_17e88 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fa0 : word) = Some W_17e88.
Proof. vm_refl. Qed.
Lemma D_17e88 : decode_any W_17e88 = Some (Branch BC_LTU 19 26 812, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e8c : bv 32 := 0x33aa6463.
Lemma F_17e8c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fa4 : word) = Some W_17e8c.
Proof. vm_refl. Qed.
Lemma D_17e8c : decode_any W_17e8c = Some (Branch BC_LTU 20 26 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e90 : bv 32 := 0x000d4083.
Lemma F_17e90 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fa8 : word) = Some W_17e90.
Proof. vm_refl. Qed.
Lemma D_17e90 : decode_any W_17e90 = Some (Load SZ1 false 1 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e94 : bv 32 := 0x001d4c83.
Lemma F_17e94 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fac : word) = Some W_17e94.
Proof. vm_refl. Qed.
Lemma D_17e94 : decode_any W_17e94 = Some (Load SZ1 false 25 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e98 : bv 32 := 0x002d4a83.
Lemma F_17e98 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fb0 : word) = Some W_17e98.
Proof. vm_refl. Qed.
Lemma D_17e98 : decode_any W_17e98 = Some (Load SZ1 false 21 26 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e9c : bv 32 := 0x003d4b03.
Lemma F_17e9c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fb4 : word) = Some W_17e9c.
Proof. vm_refl. Qed.
Lemma D_17e9c : decode_any W_17e9c = Some (Load SZ1 false 22 26 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ea0 : bv 32 := 0x00170733.
Lemma F_17ea0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fb8 : word) = Some W_17ea0.
Proof. vm_refl. Qed.
Lemma D_17ea0 : decode_any W_17ea0 = Some (Op ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ea4 : bv 32 := 0x00d706b3.
Lemma F_17ea4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fbc : word) = Some W_17ea4.
Proof. vm_refl. Qed.
Lemma D_17ea4 : decode_any W_17ea4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ea8 : bv 32 := 0x01970733.
Lemma F_17ea8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fc0 : word) = Some W_17ea8.
Proof. vm_refl. Qed.
Lemma D_17ea8 : decode_any W_17ea8 = Some (Op ALU_ADD 14 14 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_17eac : bv 32 := 0x00e686b3.
Lemma F_17eac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fc4 : word) = Some W_17eac.
Proof. vm_refl. Qed.
Lemma D_17eac : decode_any W_17eac = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17eb0 : bv 32 := 0x01570733.
Lemma F_17eb0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fc8 : word) = Some W_17eb0.
Proof. vm_refl. Qed.
Lemma D_17eb0 : decode_any W_17eb0 = Some (Op ALU_ADD 14 14 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_17eb4 : bv 32 := 0x00e686b3.
Lemma F_17eb4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fcc : word) = Some W_17eb4.
Proof. vm_refl. Qed.
Lemma D_17eb4 : decode_any W_17eb4 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17eb8 : bv 32 := 0x01670733.
Lemma F_17eb8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fd0 : word) = Some W_17eb8.
Proof. vm_refl. Qed.
Lemma D_17eb8 : decode_any W_17eb8 = Some (Op ALU_ADD 14 14 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ebc : bv 32 := 0x004d4a83.
Lemma F_17ebc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fd4 : word) = Some W_17ebc.
Proof. vm_refl. Qed.
Lemma D_17ebc : decode_any W_17ebc = Some (Load SZ1 false 21 26 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ec0 : bv 32 := 0x005d4b03.
Lemma F_17ec0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fd8 : word) = Some W_17ec0.
Proof. vm_refl. Qed.
Lemma D_17ec0 : decode_any W_17ec0 = Some (Load SZ1 false 22 26 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ec4 : bv 32 := 0x006d4c83.
Lemma F_17ec4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fdc : word) = Some W_17ec4.
Proof. vm_refl. Qed.
Lemma D_17ec4 : decode_any W_17ec4 = Some (Load SZ1 false 25 26 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ec8 : bv 32 := 0x007d4083.
Lemma F_17ec8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fe0 : word) = Some W_17ec8.
Proof. vm_refl. Qed.
Lemma D_17ec8 : decode_any W_17ec8 = Some (Load SZ1 false 1 26 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ecc : bv 32 := 0x00e686b3.
Lemma F_17ecc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fe4 : word) = Some W_17ecc.
Proof. vm_refl. Qed.
Lemma D_17ecc : decode_any W_17ecc = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ed0 : bv 32 := 0x01570733.
Lemma F_17ed0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fe8 : word) = Some W_17ed0.
Proof. vm_refl. Qed.
Lemma D_17ed0 : decode_any W_17ed0 = Some (Op ALU_ADD 14 14 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ed4 : bv 32 := 0x00e686b3.
Lemma F_17ed4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17fec : word) = Some W_17ed4.
Proof. vm_refl. Qed.
Lemma D_17ed4 : decode_any W_17ed4 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ed8 : bv 32 := 0x01670733.
Lemma F_17ed8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ff0 : word) = Some W_17ed8.
Proof. vm_refl. Qed.
Lemma D_17ed8 : decode_any W_17ed8 = Some (Op ALU_ADD 14 14 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_17edc : bv 32 := 0x00e686b3.
Lemma F_17edc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ff4 : word) = Some W_17edc.
Proof. vm_refl. Qed.
Lemma D_17edc : decode_any W_17edc = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ee0 : bv 32 := 0x01970733.
Lemma F_17ee0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ff8 : word) = Some W_17ee0.
Proof. vm_refl. Qed.
Lemma D_17ee0 : decode_any W_17ee0 = Some (Op ALU_ADD 14 14 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ee4 : bv 32 := 0x00e686b3.
Lemma F_17ee4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x17ffc : word) = Some W_17ee4.
Proof. vm_refl. Qed.
Lemma D_17ee4 : decode_any W_17ee4 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ee8 : bv 32 := 0x00170733.
Lemma F_17ee8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18000 : word) = Some W_17ee8.
Proof. vm_refl. Qed.
Lemma D_17ee8 : decode_any W_17ee8 = Some (Op ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17eec : bv 32 := 0x008d4a83.
Lemma F_17eec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18004 : word) = Some W_17eec.
Proof. vm_refl. Qed.
Lemma D_17eec : decode_any W_17eec = Some (Load SZ1 false 21 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ef0 : bv 32 := 0x009d4b03.
Lemma F_17ef0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18008 : word) = Some W_17ef0.
Proof. vm_refl. Qed.
Lemma D_17ef0 : decode_any W_17ef0 = Some (Load SZ1 false 22 26 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ef4 : bv 32 := 0x00ad4c83.
Lemma F_17ef4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1800c : word) = Some W_17ef4.
Proof. vm_refl. Qed.
Lemma D_17ef4 : decode_any W_17ef4 = Some (Load SZ1 false 25 26 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ef8 : bv 32 := 0x00bd4083.
Lemma F_17ef8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18010 : word) = Some W_17ef8.
Proof. vm_refl. Qed.
Lemma D_17ef8 : decode_any W_17ef8 = Some (Load SZ1 false 1 26 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17efc : bv 32 := 0x00e686b3.
Lemma F_17efc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18014 : word) = Some W_17efc.
Proof. vm_refl. Qed.
Lemma D_17efc : decode_any W_17efc = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f00 : bv 32 := 0x01570733.
Lemma F_17f00 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18018 : word) = Some W_17f00.
Proof. vm_refl. Qed.
Lemma D_17f00 : decode_any W_17f00 = Some (Op ALU_ADD 14 14 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f04 : bv 32 := 0x00e686b3.
Lemma F_17f04 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1801c : word) = Some W_17f04.
Proof. vm_refl. Qed.
Lemma D_17f04 : decode_any W_17f04 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f08 : bv 32 := 0x01670733.
Lemma F_17f08 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18020 : word) = Some W_17f08.
Proof. vm_refl. Qed.
Lemma D_17f08 : decode_any W_17f08 = Some (Op ALU_ADD 14 14 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f0c : bv 32 := 0x00e686b3.
Lemma F_17f0c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18024 : word) = Some W_17f0c.
Proof. vm_refl. Qed.
Lemma D_17f0c : decode_any W_17f0c = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f10 : bv 32 := 0x01970733.
Lemma F_17f10 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18028 : word) = Some W_17f10.
Proof. vm_refl. Qed.
Lemma D_17f10 : decode_any W_17f10 = Some (Op ALU_ADD 14 14 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f14 : bv 32 := 0x00e686b3.
Lemma F_17f14 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1802c : word) = Some W_17f14.
Proof. vm_refl. Qed.
Lemma D_17f14 : decode_any W_17f14 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f18 : bv 32 := 0x00170733.
Lemma F_17f18 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18030 : word) = Some W_17f18.
Proof. vm_refl. Qed.
Lemma D_17f18 : decode_any W_17f18 = Some (Op ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f1c : bv 32 := 0x00cd4a83.
Lemma F_17f1c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18034 : word) = Some W_17f1c.
Proof. vm_refl. Qed.
Lemma D_17f1c : decode_any W_17f1c = Some (Load SZ1 false 21 26 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f20 : bv 32 := 0x00dd4b03.
Lemma F_17f20 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18038 : word) = Some W_17f20.
Proof. vm_refl. Qed.
Lemma D_17f20 : decode_any W_17f20 = Some (Load SZ1 false 22 26 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f24 : bv 32 := 0x00ed4c83.
Lemma F_17f24 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1803c : word) = Some W_17f24.
Proof. vm_refl. Qed.
Lemma D_17f24 : decode_any W_17f24 = Some (Load SZ1 false 25 26 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f28 : bv 32 := 0x00fd4083.
Lemma F_17f28 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18040 : word) = Some W_17f28.
Proof. vm_refl. Qed.
Lemma D_17f28 : decode_any W_17f28 = Some (Load SZ1 false 1 26 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f2c : bv 32 := 0x00e686b3.
Lemma F_17f2c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18044 : word) = Some W_17f2c.
Proof. vm_refl. Qed.
Lemma D_17f2c : decode_any W_17f2c = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f30 : bv 32 := 0x01570733.
Lemma F_17f30 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18048 : word) = Some W_17f30.
Proof. vm_refl. Qed.
Lemma D_17f30 : decode_any W_17f30 = Some (Op ALU_ADD 14 14 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f34 : bv 32 := 0x00e686b3.
Lemma F_17f34 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1804c : word) = Some W_17f34.
Proof. vm_refl. Qed.
Lemma D_17f34 : decode_any W_17f34 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f38 : bv 32 := 0x01670733.
Lemma F_17f38 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18050 : word) = Some W_17f38.
Proof. vm_refl. Qed.
Lemma D_17f38 : decode_any W_17f38 = Some (Op ALU_ADD 14 14 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f3c : bv 32 := 0x00e686b3.
Lemma F_17f3c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18054 : word) = Some W_17f3c.
Proof. vm_refl. Qed.
Lemma D_17f3c : decode_any W_17f3c = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f40 : bv 32 := 0x01970733.
Lemma F_17f40 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18058 : word) = Some W_17f40.
Proof. vm_refl. Qed.
Lemma D_17f40 : decode_any W_17f40 = Some (Op ALU_ADD 14 14 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f44 : bv 32 := 0x001d8d9b.
Lemma F_17f44 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1805c : word) = Some W_17f44.
Proof. vm_refl. Qed.
Lemma D_17f44 : decode_any W_17f44 = Some (OpImm32 27 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f48 : bv 32 := 0x00e686b3.
Lemma F_17f48 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18060 : word) = Some W_17f48.
Proof. vm_refl. Qed.
Lemma D_17f48 : decode_any W_17f48 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f4c : bv 32 := 0x00170733.
Lemma F_17f4c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18064 : word) = Some W_17f4c.
Proof. vm_refl. Qed.
Lemma D_17f4c : decode_any W_17f4c = Some (Op ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f50 : bv 32 := 0x00e686b3.
Lemma F_17f50 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18068 : word) = Some W_17f50.
Proof. vm_refl. Qed.
Lemma D_17f50 : decode_any W_17f50 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f54 : bv 32 := 0x010d0d13.
Lemma F_17f54 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1806c : word) = Some W_17f54.
Proof. vm_refl. Qed.
Lemma D_17f54 : decode_any W_17f54 = Some (OpImm ALU_ADD 26 26 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f58 : bv 32 := 0xee0d9ce3.
Lemma F_17f58 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18070 : word) = Some W_17f58.
Proof. vm_refl. Qed.
Lemma D_17f58 : decode_any W_17f58 = Some (Branch BC_NE 27 0 7928, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f5c : bv 32 := 0x03773ab3.
Lemma F_17f5c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18074 : word) = Some W_17f5c.
Proof. vm_refl. Qed.
Lemma D_17f5c : decode_any W_17f5c = Some (Mul M_MULHU 21 14 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f60 : bv 32 := 0x0376bb33.
Lemma F_17f60 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18078 : word) = Some W_17f60.
Proof. vm_refl. Qed.
Lemma D_17f60 : decode_any W_17f60 = Some (Mul M_MULHU 22 13 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f64 : bv 32 := 0x41570cb3.
Lemma F_17f64 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1807c : word) = Some W_17f64.
Proof. vm_refl. Qed.
Lemma D_17f64 : decode_any W_17f64 = Some (Op ALU_SUB 25 14 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f68 : bv 32 := 0x001cdc93.
Lemma F_17f68 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18080 : word) = Some W_17f68.
Proof. vm_refl. Qed.
Lemma D_17f68 : decode_any W_17f68 = Some (ShiftImm ALU_SRL 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f6c : bv 32 := 0x015c8ab3.
Lemma F_17f6c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18084 : word) = Some W_17f6c.
Proof. vm_refl. Qed.
Lemma D_17f6c : decode_any W_17f6c = Some (Op ALU_ADD 21 25 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f70 : bv 32 := 0x41668cb3.
Lemma F_17f70 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18088 : word) = Some W_17f70.
Proof. vm_refl. Qed.
Lemma D_17f70 : decode_any W_17f70 = Some (Op ALU_SUB 25 13 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f74 : bv 32 := 0x001cdc93.
Lemma F_17f74 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1808c : word) = Some W_17f74.
Proof. vm_refl. Qed.
Lemma D_17f74 : decode_any W_17f74 = Some (ShiftImm ALU_SRL 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f78 : bv 32 := 0x016c8b33.
Lemma F_17f78 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18090 : word) = Some W_17f78.
Proof. vm_refl. Qed.
Lemma D_17f78 : decode_any W_17f78 = Some (Op ALU_ADD 22 25 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f7c : bv 32 := 0x00fada93.
Lemma F_17f7c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18094 : word) = Some W_17f7c.
Proof. vm_refl. Qed.
Lemma D_17f7c : decode_any W_17f7c = Some (ShiftImm ALU_SRL 21 21 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f80 : bv 32 := 0x038a8ab3.
Lemma F_17f80 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18098 : word) = Some W_17f80.
Proof. vm_refl. Qed.
Lemma D_17f80 : decode_any W_17f80 = Some (Mul M_MUL 21 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f84 : bv 32 := 0x41570733.
Lemma F_17f84 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1809c : word) = Some W_17f84.
Proof. vm_refl. Qed.
Lemma D_17f84 : decode_any W_17f84 = Some (Op ALU_SUB 14 14 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f88 : bv 32 := 0x00465a93.
Lemma F_17f88 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180a0 : word) = Some W_17f88.
Proof. vm_refl. Qed.
Lemma D_17f88 : decode_any W_17f88 = Some (ShiftImm ALU_SRL 21 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f8c : bv 32 := 0x00fb5b13.
Lemma F_17f8c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180a4 : word) = Some W_17f8c.
Proof. vm_refl. Qed.
Lemma D_17f8c : decode_any W_17f8c = Some (ShiftImm ALU_SRL 22 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f90 : bv 32 := 0x038b0b33.
Lemma F_17f90 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180a8 : word) = Some W_17f90.
Proof. vm_refl. Qed.
Lemma D_17f90 : decode_any W_17f90 = Some (Mul M_MUL 22 22 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f94 : bv 32 := 0x416686b3.
Lemma F_17f94 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180ac : word) = Some W_17f94.
Proof. vm_refl. Qed.
Lemma D_17f94 : decode_any W_17f94 = Some (Op ALU_SUB 13 13 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f98 : bv 32 := 0x15a00b13.
Lemma F_17f98 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180b0 : word) = Some W_17f98.
Proof. vm_refl. Qed.
Lemma D_17f98 : decode_any W_17f98 = Some (OpImm ALU_ADD 22 0 346, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f9c : bv 32 := 0xe95b6ee3.
Lemma F_17f9c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180b4 : word) = Some W_17f9c.
Proof. vm_refl. Qed.
Lemma D_17f9c : decode_any W_17f9c = Some (Branch BC_LTU 22 21 7836, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fa0 : bv 32 := 0x1c060863.
Lemma F_17fa0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180b8 : word) = Some W_17fa0.
Proof. vm_refl. Qed.
Lemma D_17fa0 : decode_any W_17fa0 = Some (Branch BC_EQ 12 0 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fa4 : bv 32 := 0x01000513.
Lemma F_17fa4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180bc : word) = Some W_17fa4.
Proof. vm_refl. Qed.
Lemma D_17fa4 : decode_any W_17fa4 = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fa8 : bv 32 := 0x16a66063.
Lemma F_17fa8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180c0 : word) = Some W_17fa8.
Proof. vm_refl. Qed.
Lemma D_17fa8 : decode_any W_17fa8 = Some (Branch BC_LTU 12 10 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fac : bv 32 := 0xfff00513.
Lemma F_17fac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180c4 : word) = Some W_17fac.
Proof. vm_refl. Qed.
Lemma D_17fac : decode_any W_17fac = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fb0 : bv 32 := 0xffd00793.
Lemma F_17fb0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180c8 : word) = Some W_17fb0.
Proof. vm_refl. Qed.
Lemma D_17fb0 : decode_any W_17fb0 = Some (OpImm ALU_ADD 15 0 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fb4 : bv 32 := 0xffc00813.
Lemma F_17fb4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180cc : word) = Some W_17fb4.
Proof. vm_refl. Qed.
Lemma D_17fb4 : decode_any W_17fb4 = Some (OpImm ALU_ADD 16 0 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fb8 : bv 32 := 0xffb00893.
Lemma F_17fb8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180d0 : word) = Some W_17fb8.
Proof. vm_refl. Qed.
Lemma D_17fb8 : decode_any W_17fb8 = Some (OpImm ALU_ADD 17 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fbc : bv 32 := 0xffa00293.
Lemma F_17fbc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180d4 : word) = Some W_17fbc.
Proof. vm_refl. Qed.
Lemma D_17fbc : decode_any W_17fbc = Some (OpImm ALU_ADD 5 0 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fc0 : bv 32 := 0xff900313.
Lemma F_17fc0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180d8 : word) = Some W_17fc0.
Proof. vm_refl. Qed.
Lemma D_17fc0 : decode_any W_17fc0 = Some (OpImm ALU_ADD 6 0 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fc4 : bv 32 := 0xff800393.
Lemma F_17fc4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180dc : word) = Some W_17fc4.
Proof. vm_refl. Qed.
Lemma D_17fc4 : decode_any W_17fc4 = Some (OpImm ALU_ADD 7 0 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fc8 : bv 32 := 0xff700e13.
Lemma F_17fc8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180e0 : word) = Some W_17fc8.
Proof. vm_refl. Qed.
Lemma D_17fc8 : decode_any W_17fc8 = Some (OpImm ALU_ADD 28 0 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fcc : bv 32 := 0xff600e93.
Lemma F_17fcc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180e4 : word) = Some W_17fcc.
Proof. vm_refl. Qed.
Lemma D_17fcc : decode_any W_17fcc = Some (OpImm ALU_ADD 29 0 4086, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fd0 : bv 32 := 0xff500f13.
Lemma F_17fd0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180e8 : word) = Some W_17fd0.
Proof. vm_refl. Qed.
Lemma D_17fd0 : decode_any W_17fd0 = Some (OpImm ALU_ADD 30 0 4085, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fd4 : bv 32 := 0xff400f93.
Lemma F_17fd4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180ec : word) = Some W_17fd4.
Proof. vm_refl. Qed.
Lemma D_17fd4 : decode_any W_17fd4 = Some (OpImm ALU_ADD 31 0 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fd8 : bv 32 := 0xff300413.
Lemma F_17fd8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180f0 : word) = Some W_17fd8.
Proof. vm_refl. Qed.
Lemma D_17fd8 : decode_any W_17fd8 = Some (OpImm ALU_ADD 8 0 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fdc : bv 32 := 0xff200493.
Lemma F_17fdc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180f4 : word) = Some W_17fdc.
Proof. vm_refl. Qed.
Lemma D_17fdc : decode_any W_17fdc = Some (OpImm ALU_ADD 9 0 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fe0 : bv 32 := 0xff100913.
Lemma F_17fe0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180f8 : word) = Some W_17fe0.
Proof. vm_refl. Qed.
Lemma D_17fe0 : decode_any W_17fe0 = Some (OpImm ALU_ADD 18 0 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fe4 : bv 32 := 0xff000993.
Lemma F_17fe4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x180fc : word) = Some W_17fe4.
Proof. vm_refl. Qed.
Lemma D_17fe4 : decode_any W_17fe4 = Some (OpImm ALU_ADD 19 0 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fe8 : bv 32 := 0xfef00a13.
Lemma F_17fe8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18100 : word) = Some W_17fe8.
Proof. vm_refl. Qed.
Lemma D_17fe8 : decode_any W_17fe8 = Some (OpImm ALU_ADD 20 0 4079, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fec : bv 32 := 0x00f00a93.
Lemma F_17fec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18104 : word) = Some W_17fec.
Proof. vm_refl. Qed.
Lemma D_17fec : decode_any W_17fec = Some (OpImm ALU_ADD 21 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ff0 : bv 32 := 0x1ca58263.
Lemma F_17ff0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18108 : word) = Some W_17ff0.
Proof. vm_refl. Qed.
Lemma D_17ff0 : decode_any W_17ff0 = Some (Branch BC_EQ 11 10 452, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ff4 : bv 32 := 0x1cb7e063.
Lemma F_17ff4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1810c : word) = Some W_17ff4.
Proof. vm_refl. Qed.
Lemma D_17ff4 : decode_any W_17ff4 = Some (Branch BC_LTU 15 11 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ff8 : bv 32 := 0x1ab86e63.
Lemma F_17ff8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18110 : word) = Some W_17ff8.
Proof. vm_refl. Qed.
Lemma D_17ff8 : decode_any W_17ff8 = Some (Branch BC_LTU 16 11 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ffc : bv 32 := 0x1ab8ec63.
Lemma F_17ffc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18114 : word) = Some W_17ffc.
Proof. vm_refl. Qed.
Lemma D_17ffc : decode_any W_17ffc = Some (Branch BC_LTU 17 11 440, 4%Z).
Proof. vm_refl. Qed.

Definition W_18000 : bv 32 := 0x1ab2ea63.
Lemma F_18000 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18118 : word) = Some W_18000.   (* the relocation left this one fetch at its 1.3.1 address (every other fact moved by 0xb8) *)
Proof. vm_refl. Qed.
Lemma D_18000 : decode_any W_18000 = Some (Branch BC_LTU 5 11 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_18004 : bv 32 := 0x1ab36863.
Lemma F_18004 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1811c : word) = Some W_18004.
Proof. vm_refl. Qed.
Lemma D_18004 : decode_any W_18004 = Some (Branch BC_LTU 6 11 432, 4%Z).
Proof. vm_refl. Qed.

Definition W_18008 : bv 32 := 0x1ab3e663.
Lemma F_18008 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18120 : word) = Some W_18008.
Proof. vm_refl. Qed.
Lemma D_18008 : decode_any W_18008 = Some (Branch BC_LTU 7 11 428, 4%Z).
Proof. vm_refl. Qed.

Definition W_1800c : bv 32 := 0x1abe6463.
Lemma F_1800c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18124 : word) = Some W_1800c.
Proof. vm_refl. Qed.
Lemma D_1800c : decode_any W_1800c = Some (Branch BC_LTU 28 11 424, 4%Z).
Proof. vm_refl. Qed.

Definition W_18010 : bv 32 := 0x1abee263.
Lemma F_18010 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18128 : word) = Some W_18010.
Proof. vm_refl. Qed.
Lemma D_18010 : decode_any W_18010 = Some (Branch BC_LTU 29 11 420, 4%Z).
Proof. vm_refl. Qed.

Definition W_18014 : bv 32 := 0x1abf6063.
Lemma F_18014 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1812c : word) = Some W_18014.
Proof. vm_refl. Qed.
Lemma D_18014 : decode_any W_18014 = Some (Branch BC_LTU 30 11 416, 4%Z).
Proof. vm_refl. Qed.

Definition W_18018 : bv 32 := 0x18bfee63.
Lemma F_18018 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18130 : word) = Some W_18018.
Proof. vm_refl. Qed.
Lemma D_18018 : decode_any W_18018 = Some (Branch BC_LTU 31 11 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_1801c : bv 32 := 0x18b46c63.
Lemma F_1801c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18134 : word) = Some W_1801c.
Proof. vm_refl. Qed.
Lemma D_1801c : decode_any W_1801c = Some (Branch BC_LTU 8 11 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_18020 : bv 32 := 0x18b4ea63.
Lemma F_18020 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18138 : word) = Some W_18020.
Proof. vm_refl. Qed.
Lemma D_18020 : decode_any W_18020 = Some (Branch BC_LTU 9 11 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_18024 : bv 32 := 0x18b96863.
Lemma F_18024 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1813c : word) = Some W_18024.
Proof. vm_refl. Qed.
Lemma D_18024 : decode_any W_18024 = Some (Branch BC_LTU 18 11 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_18028 : bv 32 := 0x18b9e663.
Lemma F_18028 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18140 : word) = Some W_18028.
Proof. vm_refl. Qed.
Lemma D_18028 : decode_any W_18028 = Some (Branch BC_LTU 19 11 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_1802c : bv 32 := 0x18ba6463.
Lemma F_1802c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18144 : word) = Some W_1802c.
Proof. vm_refl. Qed.
Lemma D_1802c : decode_any W_1802c = Some (Branch BC_LTU 20 11 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_18030 : bv 32 := 0x0005cb03.
Lemma F_18030 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18148 : word) = Some W_18030.
Proof. vm_refl. Qed.
Lemma D_18030 : decode_any W_18030 = Some (Load SZ1 false 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18034 : bv 32 := 0x0015cb83.
Lemma F_18034 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1814c : word) = Some W_18034.
Proof. vm_refl. Qed.
Lemma D_18034 : decode_any W_18034 = Some (Load SZ1 false 23 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18038 : bv 32 := 0x0025cc03.
Lemma F_18038 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18150 : word) = Some W_18038.
Proof. vm_refl. Qed.
Lemma D_18038 : decode_any W_18038 = Some (Load SZ1 false 24 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1803c : bv 32 := 0x0035cc83.
Lemma F_1803c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18154 : word) = Some W_1803c.
Proof. vm_refl. Qed.
Lemma D_1803c : decode_any W_1803c = Some (Load SZ1 false 25 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_18040 : bv 32 := 0x01670733.
Lemma F_18040 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18158 : word) = Some W_18040.
Proof. vm_refl. Qed.
Lemma D_18040 : decode_any W_18040 = Some (Op ALU_ADD 14 14 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_18044 : bv 32 := 0x00d706b3.
Lemma F_18044 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1815c : word) = Some W_18044.
Proof. vm_refl. Qed.
Lemma D_18044 : decode_any W_18044 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18048 : bv 32 := 0x01770733.
Lemma F_18048 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18160 : word) = Some W_18048.
Proof. vm_refl. Qed.
Lemma D_18048 : decode_any W_18048 = Some (Op ALU_ADD 14 14 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_1804c : bv 32 := 0x00e686b3.
Lemma F_1804c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18164 : word) = Some W_1804c.
Proof. vm_refl. Qed.
Lemma D_1804c : decode_any W_1804c = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_18050 : bv 32 := 0x01870733.
Lemma F_18050 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18168 : word) = Some W_18050.
Proof. vm_refl. Qed.
Lemma D_18050 : decode_any W_18050 = Some (Op ALU_ADD 14 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18054 : bv 32 := 0x00e686b3.
Lemma F_18054 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1816c : word) = Some W_18054.
Proof. vm_refl. Qed.
Lemma D_18054 : decode_any W_18054 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_18058 : bv 32 := 0x01970733.
Lemma F_18058 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18170 : word) = Some W_18058.
Proof. vm_refl. Qed.
Lemma D_18058 : decode_any W_18058 = Some (Op ALU_ADD 14 14 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_1805c : bv 32 := 0x0045cb03.
Lemma F_1805c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18174 : word) = Some W_1805c.
Proof. vm_refl. Qed.
Lemma D_1805c : decode_any W_1805c = Some (Load SZ1 false 22 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18060 : bv 32 := 0x0055cb83.
Lemma F_18060 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18178 : word) = Some W_18060.
Proof. vm_refl. Qed.
Lemma D_18060 : decode_any W_18060 = Some (Load SZ1 false 23 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18064 : bv 32 := 0x0065cc03.
Lemma F_18064 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1817c : word) = Some W_18064.
Proof. vm_refl. Qed.
Lemma D_18064 : decode_any W_18064 = Some (Load SZ1 false 24 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_18068 : bv 32 := 0x0075cc83.
Lemma F_18068 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18180 : word) = Some W_18068.
Proof. vm_refl. Qed.
Lemma D_18068 : decode_any W_18068 = Some (Load SZ1 false 25 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1806c : bv 32 := 0x00e686b3.
Lemma F_1806c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18184 : word) = Some W_1806c.
Proof. vm_refl. Qed.
Lemma D_1806c : decode_any W_1806c = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_18070 : bv 32 := 0x01670733.
Lemma F_18070 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18188 : word) = Some W_18070.
Proof. vm_refl. Qed.
Lemma D_18070 : decode_any W_18070 = Some (Op ALU_ADD 14 14 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_18074 : bv 32 := 0x00e686b3.
Lemma F_18074 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1818c : word) = Some W_18074.
Proof. vm_refl. Qed.
Lemma D_18074 : decode_any W_18074 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_18078 : bv 32 := 0x01770733.
Lemma F_18078 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18190 : word) = Some W_18078.
Proof. vm_refl. Qed.
Lemma D_18078 : decode_any W_18078 = Some (Op ALU_ADD 14 14 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_1807c : bv 32 := 0x00e686b3.
Lemma F_1807c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18194 : word) = Some W_1807c.
Proof. vm_refl. Qed.
Lemma D_1807c : decode_any W_1807c = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_18080 : bv 32 := 0x01870733.
Lemma F_18080 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18198 : word) = Some W_18080.
Proof. vm_refl. Qed.
Lemma D_18080 : decode_any W_18080 = Some (Op ALU_ADD 14 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18084 : bv 32 := 0x00e686b3.
Lemma F_18084 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1819c : word) = Some W_18084.
Proof. vm_refl. Qed.
Lemma D_18084 : decode_any W_18084 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_18088 : bv 32 := 0x01970733.
Lemma F_18088 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181a0 : word) = Some W_18088.
Proof. vm_refl. Qed.
Lemma D_18088 : decode_any W_18088 = Some (Op ALU_ADD 14 14 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_1808c : bv 32 := 0x0085cb03.
Lemma F_1808c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181a4 : word) = Some W_1808c.
Proof. vm_refl. Qed.
Lemma D_1808c : decode_any W_1808c = Some (Load SZ1 false 22 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18090 : bv 32 := 0x0095cb83.
Lemma F_18090 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181a8 : word) = Some W_18090.
Proof. vm_refl. Qed.
Lemma D_18090 : decode_any W_18090 = Some (Load SZ1 false 23 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_18094 : bv 32 := 0x00a5cc03.
Lemma F_18094 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181ac : word) = Some W_18094.
Proof. vm_refl. Qed.
Lemma D_18094 : decode_any W_18094 = Some (Load SZ1 false 24 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_18098 : bv 32 := 0x00b5cc83.
Lemma F_18098 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181b0 : word) = Some W_18098.
Proof. vm_refl. Qed.
Lemma D_18098 : decode_any W_18098 = Some (Load SZ1 false 25 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1809c : bv 32 := 0x00e686b3.
Lemma F_1809c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181b4 : word) = Some W_1809c.
Proof. vm_refl. Qed.
Lemma D_1809c : decode_any W_1809c = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_180a0 : bv 32 := 0x01670733.
Lemma F_180a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181b8 : word) = Some W_180a0.
Proof. vm_refl. Qed.
Lemma D_180a0 : decode_any W_180a0 = Some (Op ALU_ADD 14 14 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_180a4 : bv 32 := 0x00e686b3.
Lemma F_180a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181bc : word) = Some W_180a4.
Proof. vm_refl. Qed.
Lemma D_180a4 : decode_any W_180a4 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_180a8 : bv 32 := 0x01770733.
Lemma F_180a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181c0 : word) = Some W_180a8.
Proof. vm_refl. Qed.
Lemma D_180a8 : decode_any W_180a8 = Some (Op ALU_ADD 14 14 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_180ac : bv 32 := 0x00e686b3.
Lemma F_180ac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181c4 : word) = Some W_180ac.
Proof. vm_refl. Qed.
Lemma D_180ac : decode_any W_180ac = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_180b0 : bv 32 := 0x01870733.
Lemma F_180b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181c8 : word) = Some W_180b0.
Proof. vm_refl. Qed.
Lemma D_180b0 : decode_any W_180b0 = Some (Op ALU_ADD 14 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_180b4 : bv 32 := 0x00e686b3.
Lemma F_180b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181cc : word) = Some W_180b4.
Proof. vm_refl. Qed.
Lemma D_180b4 : decode_any W_180b4 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_180b8 : bv 32 := 0x01970733.
Lemma F_180b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181d0 : word) = Some W_180b8.
Proof. vm_refl. Qed.
Lemma D_180b8 : decode_any W_180b8 = Some (Op ALU_ADD 14 14 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_180bc : bv 32 := 0x00c5cb03.
Lemma F_180bc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181d4 : word) = Some W_180bc.
Proof. vm_refl. Qed.
Lemma D_180bc : decode_any W_180bc = Some (Load SZ1 false 22 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_180c0 : bv 32 := 0x00d5cb83.
Lemma F_180c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181d8 : word) = Some W_180c0.
Proof. vm_refl. Qed.
Lemma D_180c0 : decode_any W_180c0 = Some (Load SZ1 false 23 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_180c4 : bv 32 := 0x00e5cc03.
Lemma F_180c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181dc : word) = Some W_180c4.
Proof. vm_refl. Qed.
Lemma D_180c4 : decode_any W_180c4 = Some (Load SZ1 false 24 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_180c8 : bv 32 := 0x00f5cc83.
Lemma F_180c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181e0 : word) = Some W_180c8.
Proof. vm_refl. Qed.
Lemma D_180c8 : decode_any W_180c8 = Some (Load SZ1 false 25 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_180cc : bv 32 := 0x00e686b3.
Lemma F_180cc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181e4 : word) = Some W_180cc.
Proof. vm_refl. Qed.
Lemma D_180cc : decode_any W_180cc = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_180d0 : bv 32 := 0x01670733.
Lemma F_180d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181e8 : word) = Some W_180d0.
Proof. vm_refl. Qed.
Lemma D_180d0 : decode_any W_180d0 = Some (Op ALU_ADD 14 14 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_180d4 : bv 32 := 0x00e686b3.
Lemma F_180d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181ec : word) = Some W_180d4.
Proof. vm_refl. Qed.
Lemma D_180d4 : decode_any W_180d4 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_180d8 : bv 32 := 0x01770733.
Lemma F_180d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181f0 : word) = Some W_180d8.
Proof. vm_refl. Qed.
Lemma D_180d8 : decode_any W_180d8 = Some (Op ALU_ADD 14 14 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_180dc : bv 32 := 0x00e686b3.
Lemma F_180dc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181f4 : word) = Some W_180dc.
Proof. vm_refl. Qed.
Lemma D_180dc : decode_any W_180dc = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_180e0 : bv 32 := 0x01870733.
Lemma F_180e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181f8 : word) = Some W_180e0.
Proof. vm_refl. Qed.
Lemma D_180e0 : decode_any W_180e0 = Some (Op ALU_ADD 14 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_180e4 : bv 32 := 0xff060613.
Lemma F_180e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x181fc : word) = Some W_180e4.
Proof. vm_refl. Qed.
Lemma D_180e4 : decode_any W_180e4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_180e8 : bv 32 := 0x01058b13.
Lemma F_180e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18200 : word) = Some W_180e8.
Proof. vm_refl. Qed.
Lemma D_180e8 : decode_any W_180e8 = Some (OpImm ALU_ADD 22 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_180ec : bv 32 := 0x00e686b3.
Lemma F_180ec : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18204 : word) = Some W_180ec.
Proof. vm_refl. Qed.
Lemma D_180ec : decode_any W_180ec = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_180f0 : bv 32 := 0x01970733.
Lemma F_180f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18208 : word) = Some W_180f0.
Proof. vm_refl. Qed.
Lemma D_180f0 : decode_any W_180f0 = Some (Op ALU_ADD 14 14 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_180f4 : bv 32 := 0x00e686b3.
Lemma F_180f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1820c : word) = Some W_180f4.
Proof. vm_refl. Qed.
Lemma D_180f4 : decode_any W_180f4 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_180f8 : bv 32 := 0x000b0593.
Lemma F_180f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18210 : word) = Some W_180f8.
Proof. vm_refl. Qed.
Lemma D_180f8 : decode_any W_180f8 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_180fc : bv 32 := 0xeecaeae3.
Lemma F_180fc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18214 : word) = Some W_180fc.
Proof. vm_refl. Qed.
Lemma D_180fc : decode_any W_180fc = Some (Branch BC_LTU 21 12 7924, 4%Z).
Proof. vm_refl. Qed.

Definition W_18100 : bv 32 := 0x000b0593.
Lemma F_18100 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18218 : word) = Some W_18100.
Proof. vm_refl. Qed.
Lemma D_18100 : decode_any W_18100 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18104 : bv 32 := 0x02060263.
Lemma F_18104 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1821c : word) = Some W_18104.
Proof. vm_refl. Qed.
Lemma D_18104 : decode_any W_18104 = Some (Branch BC_EQ 12 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_18108 : bv 32 := 0xfff00513.
Lemma F_18108 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18220 : word) = Some W_18108.
Proof. vm_refl. Qed.
Lemma D_18108 : decode_any W_18108 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1810c : bv 32 := 0x0aa58463.
Lemma F_1810c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18224 : word) = Some W_1810c.
Proof. vm_refl. Qed.
Lemma D_1810c : decode_any W_1810c = Some (Branch BC_EQ 11 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_18110 : bv 32 := 0x0005c783.
Lemma F_18110 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18228 : word) = Some W_18110.
Proof. vm_refl. Qed.
Lemma D_18110 : decode_any W_18110 = Some (Load SZ1 false 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18114 : bv 32 := 0x00158593.
Lemma F_18114 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1822c : word) = Some W_18114.
Proof. vm_refl. Qed.
Lemma D_18114 : decode_any W_18114 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18118 : bv 32 := 0xfff60613.
Lemma F_18118 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18230 : word) = Some W_18118.
Proof. vm_refl. Qed.
Lemma D_18118 : decode_any W_18118 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1811c : bv 32 := 0x00f70733.
Lemma F_1811c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18234 : word) = Some W_1811c.
Proof. vm_refl. Qed.
Lemma D_1811c : decode_any W_1811c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_18120 : bv 32 := 0x00d706b3.
Lemma F_18120 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18238 : word) = Some W_18120.
Proof. vm_refl. Qed.
Lemma D_18120 : decode_any W_18120 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18124 : bv 32 := 0xfe0614e3.
Lemma F_18124 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1823c : word) = Some W_18124.
Proof. vm_refl. Qed.
Lemma D_18124 : decode_any W_18124 = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_18128 : bv 32 := 0xffff8517.
Lemma F_18128 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18240 : word) = Some W_18128.
Proof. vm_refl. Qed.
Lemma D_18128 : decode_any W_18128 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_1812c : bv 32 := 0x32853503.
Lemma F_1812c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18244 : word) = Some W_1812c.
Proof. vm_refl. Qed.
Lemma D_1812c : decode_any W_1812c = Some (Load SZ8 true 10 10 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_18130 : bv 32 := 0x02a735b3.
Lemma F_18130 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18248 : word) = Some W_18130.
Proof. vm_refl. Qed.
Lemma D_18130 : decode_any W_18130 = Some (Mul M_MULHU 11 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_18134 : bv 32 := 0x02a6b533.
Lemma F_18134 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1824c : word) = Some W_18134.
Proof. vm_refl. Qed.
Lemma D_18134 : decode_any W_18134 = Some (Mul M_MULHU 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_18138 : bv 32 := 0x40b70633.
Lemma F_18138 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18250 : word) = Some W_18138.
Proof. vm_refl. Qed.
Lemma D_18138 : decode_any W_18138 = Some (Op ALU_SUB 12 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1813c : bv 32 := 0x00165613.
Lemma F_1813c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18254 : word) = Some W_1813c.
Proof. vm_refl. Qed.
Lemma D_1813c : decode_any W_1813c = Some (ShiftImm ALU_SRL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18140 : bv 32 := 0x00b605b3.
Lemma F_18140 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18258 : word) = Some W_18140.
Proof. vm_refl. Qed.
Lemma D_18140 : decode_any W_18140 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18144 : bv 32 := 0x40a68633.
Lemma F_18144 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1825c : word) = Some W_18144.
Proof. vm_refl. Qed.
Lemma D_18144 : decode_any W_18144 = Some (Op ALU_SUB 12 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_18148 : bv 32 := 0x00165613.
Lemma F_18148 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18260 : word) = Some W_18148.
Proof. vm_refl. Qed.
Lemma D_18148 : decode_any W_18148 = Some (ShiftImm ALU_SRL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1814c : bv 32 := 0x00a60533.
Lemma F_1814c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18264 : word) = Some W_1814c.
Proof. vm_refl. Qed.
Lemma D_1814c : decode_any W_1814c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_18150 : bv 32 := 0x00010637.
Lemma F_18150 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18268 : word) = Some W_18150.
Proof. vm_refl. Qed.
Lemma D_18150 : decode_any W_18150 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18154 : bv 32 := 0xff16061b.
Lemma F_18154 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1826c : word) = Some W_18154.
Proof. vm_refl. Qed.
Lemma D_18154 : decode_any W_18154 = Some (OpImm32 12 12 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_18158 : bv 32 := 0x00f5d593.
Lemma F_18158 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18270 : word) = Some W_18158.
Proof. vm_refl. Qed.
Lemma D_18158 : decode_any W_18158 = Some (ShiftImm ALU_SRL 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1815c : bv 32 := 0x00f55513.
Lemma F_1815c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18274 : word) = Some W_1815c.
Proof. vm_refl. Qed.
Lemma D_1815c : decode_any W_1815c = Some (ShiftImm ALU_SRL 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_18160 : bv 32 := 0x02c585b3.
Lemma F_18160 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18278 : word) = Some W_18160.
Proof. vm_refl. Qed.
Lemma D_18160 : decode_any W_18160 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18164 : bv 32 := 0x02c50533.
Lemma F_18164 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1827c : word) = Some W_18164.
Proof. vm_refl. Qed.
Lemma D_18164 : decode_any W_18164 = Some (Mul M_MUL 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18168 : bv 32 := 0x40b70733.
Lemma F_18168 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18280 : word) = Some W_18168.
Proof. vm_refl. Qed.
Lemma D_18168 : decode_any W_18168 = Some (Op ALU_SUB 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1816c : bv 32 := 0x40a686b3.
Lemma F_1816c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18284 : word) = Some W_1816c.
Proof. vm_refl. Qed.
Lemma D_1816c : decode_any W_1816c = Some (Op ALU_SUB 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_18170 : bv 32 := 0x01069513.
Lemma F_18170 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18288 : word) = Some W_18170.
Proof. vm_refl. Qed.
Lemma D_18170 : decode_any W_18170 = Some (ShiftImm ALU_SLL 10 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18174 : bv 32 := 0x00e56533.
Lemma F_18174 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1828c : word) = Some W_18174.
Proof. vm_refl. Qed.
Lemma D_18174 : decode_any W_18174 = Some (Op ALU_OR 10 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_18178 : bv 32 := 0x07813083.
Lemma F_18178 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18290 : word) = Some W_18178.
Proof. vm_refl. Qed.
Lemma D_18178 : decode_any W_18178 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1817c : bv 32 := 0x07013403.
Lemma F_1817c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18294 : word) = Some W_1817c.
Proof. vm_refl. Qed.
Lemma D_1817c : decode_any W_1817c = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_18180 : bv 32 := 0x06813483.
Lemma F_18180 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x18298 : word) = Some W_18180.
Proof. vm_refl. Qed.
Lemma D_18180 : decode_any W_18180 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_18184 : bv 32 := 0x06013903.
Lemma F_18184 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x1829c : word) = Some W_18184.
Proof. vm_refl. Qed.
Lemma D_18184 : decode_any W_18184 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_18188 : bv 32 := 0x05813983.
Lemma F_18188 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182a0 : word) = Some W_18188.
Proof. vm_refl. Qed.
Lemma D_18188 : decode_any W_18188 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1818c : bv 32 := 0x05013a03.
Lemma F_1818c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182a4 : word) = Some W_1818c.
Proof. vm_refl. Qed.
Lemma D_1818c : decode_any W_1818c = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_18190 : bv 32 := 0x04813a83.
Lemma F_18190 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182a8 : word) = Some W_18190.
Proof. vm_refl. Qed.
Lemma D_18190 : decode_any W_18190 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_18194 : bv 32 := 0x04013b03.
Lemma F_18194 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182ac : word) = Some W_18194.
Proof. vm_refl. Qed.
Lemma D_18194 : decode_any W_18194 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_18198 : bv 32 := 0x03813b83.
Lemma F_18198 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182b0 : word) = Some W_18198.
Proof. vm_refl. Qed.
Lemma D_18198 : decode_any W_18198 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1819c : bv 32 := 0x03013c03.
Lemma F_1819c : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182b4 : word) = Some W_1819c.
Proof. vm_refl. Qed.
Lemma D_1819c : decode_any W_1819c = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_181a0 : bv 32 := 0x02813c83.
Lemma F_181a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182b8 : word) = Some W_181a0.
Proof. vm_refl. Qed.
Lemma D_181a0 : decode_any W_181a0 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_181a4 : bv 32 := 0x02013d03.
Lemma F_181a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182bc : word) = Some W_181a4.
Proof. vm_refl. Qed.
Lemma D_181a4 : decode_any W_181a4 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_181a8 : bv 32 := 0x01813d83.
Lemma F_181a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182c0 : word) = Some W_181a8.
Proof. vm_refl. Qed.
Lemma D_181a8 : decode_any W_181a8 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_181ac : bv 32 := 0x08010113.
Lemma F_181ac : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182c4 : word) = Some W_181ac.
Proof. vm_refl. Qed.
Lemma D_181ac : decode_any W_181ac = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_181b0 : bv 32 := 0x00008067.
Lemma F_181b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182c8 : word) = Some W_181b0.
Proof. vm_refl. Qed.
Lemma D_181b0 : decode_any W_181b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_181b4 : bv 32 := 0xc0001073.
Lemma F_181b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182cc : word) = Some W_181b4.
Proof. vm_refl. Qed.
Lemma D_181b4 : decode_any W_181b4 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

Definition W_181b8 : bv 32 := 0x02061613.
Lemma F_181b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182d0 : word) = Some W_181b8.
Proof. vm_refl. Qed.
Lemma D_181b8 : decode_any W_181b8 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_181bc : bv 32 := 0x02065613.
Lemma F_181bc : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182d4 : word) = Some W_181bc.
Proof. vm_refl. Qed.
Lemma D_181bc : decode_any W_181bc = Some (ShiftImm ALU_SRL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_181c0 : bv 32 := 0xac9ff06f.
Lemma F_181c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments (0x182d8 : word) = Some W_181c0.
Proof. vm_refl. Qed.
Lemma D_181c0 : decode_any W_181c0 = Some (Jal 0 2095816, 4%Z).
Proof. vm_refl. Qed.
