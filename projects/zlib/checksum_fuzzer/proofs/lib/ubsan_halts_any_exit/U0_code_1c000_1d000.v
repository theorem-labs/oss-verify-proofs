(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)
(* reloc14 *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1cee8 : bv 32 := 0x0035f693.
Lemma F_1cee8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cf88 : word) = Some W_1cee8.
Proof. vm_refl. Qed.
Lemma D_1cee8 : decode_any W_1cee8 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ceec : bv 32 := 0x10068863.
Lemma F_1ceec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cf8c : word) = Some W_1ceec.
Proof. vm_refl. Qed.
Lemma D_1ceec : decode_any W_1ceec = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cef0 : bv 32 := 0x02060e63.
Lemma F_1cef0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cf90 : word) = Some W_1cef0.
Proof. vm_refl. Qed.
Lemma D_1cef0 : decode_any W_1cef0 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cef4 : bv 32 := 0x00158713.
Lemma F_1cef4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cf94 : word) = Some W_1cef4.
Proof. vm_refl. Qed.
Lemma D_1cef4 : decode_any W_1cef4 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cef8 : bv 32 := 0x00100793.
Lemma F_1cef8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cf98 : word) = Some W_1cef8.
Proof. vm_refl. Qed.
Lemma D_1cef8 : decode_any W_1cef8 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cefc : bv 32 := 0x00050693.
Lemma F_1cefc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cf9c : word) = Some W_1cefc.
Proof. vm_refl. Qed.
Lemma D_1cefc : decode_any W_1cefc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf00 : bv 32 := 0x0005c883.
Lemma F_1cf00 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfa0 : word) = Some W_1cf00.
Proof. vm_refl. Qed.
Lemma D_1cf00 : decode_any W_1cf00 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf04 : bv 32 := 0x00060813.
Lemma F_1cf04 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfa4 : word) = Some W_1cf04.
Proof. vm_refl. Qed.
Lemma D_1cf04 : decode_any W_1cf04 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf08 : bv 32 := 0x00158593.
Lemma F_1cf08 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfa8 : word) = Some W_1cf08.
Proof. vm_refl. Qed.
Lemma D_1cf08 : decode_any W_1cf08 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf0c : bv 32 := 0x00377293.
Lemma F_1cf0c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfac : word) = Some W_1cf0c.
Proof. vm_refl. Qed.
Lemma D_1cf0c : decode_any W_1cf0c = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf10 : bv 32 := 0x01168023.
Lemma F_1cf10 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfb0 : word) = Some W_1cf10.
Proof. vm_refl. Qed.
Lemma D_1cf10 : decode_any W_1cf10 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf14 : bv 32 := 0x00168693.
Lemma F_1cf14 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfb4 : word) = Some W_1cf14.
Proof. vm_refl. Qed.
Lemma D_1cf14 : decode_any W_1cf14 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf18 : bv 32 := 0xfff60613.
Lemma F_1cf18 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfb8 : word) = Some W_1cf18.
Proof. vm_refl. Qed.
Lemma D_1cf18 : decode_any W_1cf18 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf1c : bv 32 := 0x00028a63.
Lemma F_1cf1c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfbc : word) = Some W_1cf1c.
Proof. vm_refl. Qed.
Lemma D_1cf1c : decode_any W_1cf1c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf20 : bv 32 := 0x00170713.
Lemma F_1cf20 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfc0 : word) = Some W_1cf20.
Proof. vm_refl. Qed.
Lemma D_1cf20 : decode_any W_1cf20 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf24 : bv 32 := 0xfcf81ee3.
Lemma F_1cf24 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfc4 : word) = Some W_1cf24.
Proof. vm_refl. Qed.
Lemma D_1cf24 : decode_any W_1cf24 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf28 : bv 32 := 0x0080006f.
Lemma F_1cf28 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfc8 : word) = Some W_1cf28.
Proof. vm_refl. Qed.
Lemma D_1cf28 : decode_any W_1cf28 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf2c : bv 32 := 0x00050693.
Lemma F_1cf2c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfcc : word) = Some W_1cf2c.
Proof. vm_refl. Qed.
Lemma D_1cf2c : decode_any W_1cf2c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf30 : bv 32 := 0x0036f793.
Lemma F_1cf30 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfd0 : word) = Some W_1cf30.
Proof. vm_refl. Qed.
Lemma D_1cf30 : decode_any W_1cf30 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf34 : bv 32 := 0x0c078a63.
Lemma F_1cf34 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfd4 : word) = Some W_1cf34.
Proof. vm_refl. Qed.
Lemma D_1cf34 : decode_any W_1cf34 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf38 : bv 32 := 0x02000713.
Lemma F_1cf38 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfd8 : word) = Some W_1cf38.
Proof. vm_refl. Qed.
Lemma D_1cf38 : decode_any W_1cf38 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf3c : bv 32 := 0x02e67063.
Lemma F_1cf3c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfdc : word) = Some W_1cf3c.
Proof. vm_refl. Qed.
Lemma D_1cf3c : decode_any W_1cf3c = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf40 : bv 32 := 0x01000713.
Lemma F_1cf40 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfe0 : word) = Some W_1cf40.
Proof. vm_refl. Qed.
Lemma D_1cf40 : decode_any W_1cf40 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf44 : bv 32 := 0x24e67863.
Lemma F_1cf44 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfe4 : word) = Some W_1cf44.
Proof. vm_refl. Qed.
Lemma D_1cf44 : decode_any W_1cf44 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf48 : bv 32 := 0x00867713.
Lemma F_1cf48 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfe8 : word) = Some W_1cf48.
Proof. vm_refl. Qed.
Lemma D_1cf48 : decode_any W_1cf48 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf4c : bv 32 := 0x2c071e63.
Lemma F_1cf4c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cfec : word) = Some W_1cf4c.
Proof. vm_refl. Qed.
Lemma D_1cf4c : decode_any W_1cf4c = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf50 : bv 32 := 0x00467713.
Lemma F_1cf50 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cff0 : word) = Some W_1cf50.
Proof. vm_refl. Qed.
Lemma D_1cf50 : decode_any W_1cf50 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf54 : bv 32 := 0x32071463.
Lemma F_1cf54 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cff4 : word) = Some W_1cf54.
Proof. vm_refl. Qed.
Lemma D_1cf54 : decode_any W_1cf54 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf58 : bv 32 := 0x3500006f.
Lemma F_1cf58 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cff8 : word) = Some W_1cf58.
Proof. vm_refl. Qed.
Lemma D_1cf58 : decode_any W_1cf58 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf5c : bv 32 := 0x0005a703.
Lemma F_1cf5c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1cffc : word) = Some W_1cf5c.
Proof. vm_refl. Qed.
Lemma D_1cf5c : decode_any W_1cf5c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf60 : bv 32 := 0x00300813.
Lemma F_1cf60 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d000 : word) = Some W_1cf60.
Proof. vm_refl. Qed.
Lemma D_1cf60 : decode_any W_1cf60 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf64 : bv 32 := 0x11078e63.
Lemma F_1cf64 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d004 : word) = Some W_1cf64.
Proof. vm_refl. Qed.
Lemma D_1cf64 : decode_any W_1cf64 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf68 : bv 32 := 0x00200813.
Lemma F_1cf68 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d008 : word) = Some W_1cf68.
Proof. vm_refl. Qed.
Lemma D_1cf68 : decode_any W_1cf68 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf6c : bv 32 := 0x19079c63.
Lemma F_1cf6c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d00c : word) = Some W_1cf6c.
Proof. vm_refl. Qed.
Lemma D_1cf6c : decode_any W_1cf6c = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf70 : bv 32 := 0x00875793.
Lemma F_1cf70 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d010 : word) = Some W_1cf70.
Proof. vm_refl. Qed.
Lemma D_1cf70 : decode_any W_1cf70 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf74 : bv 32 := 0xffe60613.
Lemma F_1cf74 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d014 : word) = Some W_1cf74.
Proof. vm_refl. Qed.
Lemma D_1cf74 : decode_any W_1cf74 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf78 : bv 32 := 0x00e68023.
Lemma F_1cf78 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d018 : word) = Some W_1cf78.
Proof. vm_refl. Qed.
Lemma D_1cf78 : decode_any W_1cf78 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf7c : bv 32 := 0x00f680a3.
Lemma F_1cf7c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d01c : word) = Some W_1cf7c.
Proof. vm_refl. Qed.
Lemma D_1cf7c : decode_any W_1cf7c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf80 : bv 32 := 0x00268693.
Lemma F_1cf80 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d020 : word) = Some W_1cf80.
Proof. vm_refl. Qed.
Lemma D_1cf80 : decode_any W_1cf80 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf84 : bv 32 := 0x01058593.
Lemma F_1cf84 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d024 : word) = Some W_1cf84.
Proof. vm_refl. Qed.
Lemma D_1cf84 : decode_any W_1cf84 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf88 : bv 32 := 0x01100793.
Lemma F_1cf88 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d028 : word) = Some W_1cf88.
Proof. vm_refl. Qed.
Lemma D_1cf88 : decode_any W_1cf88 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf8c : bv 32 := 0x0107581b.
Lemma F_1cf8c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d02c : word) = Some W_1cf8c.
Proof. vm_refl. Qed.
Lemma D_1cf8c : decode_any W_1cf8c = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf90 : bv 32 := 0xff45a883.
Lemma F_1cf90 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d030 : word) = Some W_1cf90.
Proof. vm_refl. Qed.
Lemma D_1cf90 : decode_any W_1cf90 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf94 : bv 32 := 0xff85a283.
Lemma F_1cf94 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d034 : word) = Some W_1cf94.
Proof. vm_refl. Qed.
Lemma D_1cf94 : decode_any W_1cf94 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf98 : bv 32 := 0xffc5a303.
Lemma F_1cf98 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d038 : word) = Some W_1cf98.
Proof. vm_refl. Qed.
Lemma D_1cf98 : decode_any W_1cf98 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cf9c : bv 32 := 0x0005a703.
Lemma F_1cf9c : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d03c : word) = Some W_1cf9c.
Proof. vm_refl. Qed.
Lemma D_1cf9c : decode_any W_1cf9c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfa0 : bv 32 := 0x01089393.
Lemma F_1cfa0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d040 : word) = Some W_1cfa0.
Proof. vm_refl. Qed.
Lemma D_1cfa0 : decode_any W_1cfa0 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfa4 : bv 32 := 0x0108d89b.
Lemma F_1cfa4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d044 : word) = Some W_1cfa4.
Proof. vm_refl. Qed.
Lemma D_1cfa4 : decode_any W_1cfa4 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfa8 : bv 32 := 0x0103e833.
Lemma F_1cfa8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d048 : word) = Some W_1cfa8.
Proof. vm_refl. Qed.
Lemma D_1cfa8 : decode_any W_1cfa8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfac : bv 32 := 0x01029393.
Lemma F_1cfac : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d04c : word) = Some W_1cfac.
Proof. vm_refl. Qed.
Lemma D_1cfac : decode_any W_1cfac = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfb0 : bv 32 := 0x0102d29b.
Lemma F_1cfb0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d050 : word) = Some W_1cfb0.
Proof. vm_refl. Qed.
Lemma D_1cfb0 : decode_any W_1cfb0 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfb4 : bv 32 := 0x0113e8b3.
Lemma F_1cfb4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d054 : word) = Some W_1cfb4.
Proof. vm_refl. Qed.
Lemma D_1cfb4 : decode_any W_1cfb4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfb8 : bv 32 := 0x01031393.
Lemma F_1cfb8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d058 : word) = Some W_1cfb8.
Proof. vm_refl. Qed.
Lemma D_1cfb8 : decode_any W_1cfb8 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfbc : bv 32 := 0x0103531b.
Lemma F_1cfbc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d05c : word) = Some W_1cfbc.
Proof. vm_refl. Qed.
Lemma D_1cfbc : decode_any W_1cfbc = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfc0 : bv 32 := 0x0053e2b3.
Lemma F_1cfc0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d060 : word) = Some W_1cfc0.
Proof. vm_refl. Qed.
Lemma D_1cfc0 : decode_any W_1cfc0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfc4 : bv 32 := 0x01071393.
Lemma F_1cfc4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d064 : word) = Some W_1cfc4.
Proof. vm_refl. Qed.
Lemma D_1cfc4 : decode_any W_1cfc4 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfc8 : bv 32 := 0x0063e333.
Lemma F_1cfc8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d068 : word) = Some W_1cfc8.
Proof. vm_refl. Qed.
Lemma D_1cfc8 : decode_any W_1cfc8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfcc : bv 32 := 0xff060613.
Lemma F_1cfcc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d06c : word) = Some W_1cfcc.
Proof. vm_refl. Qed.
Lemma D_1cfcc : decode_any W_1cfcc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfd0 : bv 32 := 0x0106a023.
Lemma F_1cfd0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d070 : word) = Some W_1cfd0.
Proof. vm_refl. Qed.
Lemma D_1cfd0 : decode_any W_1cfd0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfd4 : bv 32 := 0x0116a223.
Lemma F_1cfd4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d074 : word) = Some W_1cfd4.
Proof. vm_refl. Qed.
Lemma D_1cfd4 : decode_any W_1cfd4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfd8 : bv 32 := 0x0056a423.
Lemma F_1cfd8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d078 : word) = Some W_1cfd8.
Proof. vm_refl. Qed.
Lemma D_1cfd8 : decode_any W_1cfd8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfdc : bv 32 := 0x0066a623.
Lemma F_1cfdc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d07c : word) = Some W_1cfdc.
Proof. vm_refl. Qed.
Lemma D_1cfdc : decode_any W_1cfdc = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfe0 : bv 32 := 0x01068693.
Lemma F_1cfe0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d080 : word) = Some W_1cfe0.
Proof. vm_refl. Qed.
Lemma D_1cfe0 : decode_any W_1cfe0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfe4 : bv 32 := 0x01058593.
Lemma F_1cfe4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d084 : word) = Some W_1cfe4.
Proof. vm_refl. Qed.
Lemma D_1cfe4 : decode_any W_1cfe4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfe8 : bv 32 := 0xfac7e2e3.
Lemma F_1cfe8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d088 : word) = Some W_1cfe8.
Proof. vm_refl. Qed.
Lemma D_1cfe8 : decode_any W_1cfe8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cfec : bv 32 := 0xff258593.
Lemma F_1cfec : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d08c : word) = Some W_1cfec.
Proof. vm_refl. Qed.
Lemma D_1cfec : decode_any W_1cfec = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cff0 : bv 32 := 0x01000713.
Lemma F_1cff0 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d090 : word) = Some W_1cff0.
Proof. vm_refl. Qed.
Lemma D_1cff0 : decode_any W_1cff0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cff4 : bv 32 := 0xf4e66ae3.
Lemma F_1cff4 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d094 : word) = Some W_1cff4.
Proof. vm_refl. Qed.
Lemma D_1cff4 : decode_any W_1cff4 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cff8 : bv 32 := 0x19c0006f.
Lemma F_1cff8 : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d098 : word) = Some W_1cff8.
Proof. vm_refl. Qed.
Lemma D_1cff8 : decode_any W_1cff8 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_1cffc : bv 32 := 0x00050693.
Lemma F_1cffc : fetch_word Tgt_checksum_fuzzer_ubsan.M.loaded_segments (0x1d09c : word) = Some W_1cffc.
Proof. vm_refl. Qed.
Lemma D_1cffc : decode_any W_1cffc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
