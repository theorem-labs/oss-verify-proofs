(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress_fuzzer_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c709c : bv 32 := 0x0035f693.
Lemma F_c709c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7668 : word) = Some W_c709c.
Proof. vm_refl. Qed.
Lemma D_c709c : decode_any W_c709c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70a0 : bv 32 := 0x10068863.
Lemma F_c70a0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc766c : word) = Some W_c70a0.
Proof. vm_refl. Qed.
Lemma D_c70a0 : decode_any W_c70a0 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70a4 : bv 32 := 0x02060e63.
Lemma F_c70a4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7670 : word) = Some W_c70a4.
Proof. vm_refl. Qed.
Lemma D_c70a4 : decode_any W_c70a4 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70a8 : bv 32 := 0x00158713.
Lemma F_c70a8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7674 : word) = Some W_c70a8.
Proof. vm_refl. Qed.
Lemma D_c70a8 : decode_any W_c70a8 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70ac : bv 32 := 0x00100793.
Lemma F_c70ac : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7678 : word) = Some W_c70ac.
Proof. vm_refl. Qed.
Lemma D_c70ac : decode_any W_c70ac = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70b0 : bv 32 := 0x00050693.
Lemma F_c70b0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc767c : word) = Some W_c70b0.
Proof. vm_refl. Qed.
Lemma D_c70b0 : decode_any W_c70b0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70b4 : bv 32 := 0x0005c883.
Lemma F_c70b4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7680 : word) = Some W_c70b4.
Proof. vm_refl. Qed.
Lemma D_c70b4 : decode_any W_c70b4 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70b8 : bv 32 := 0x00060813.
Lemma F_c70b8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7684 : word) = Some W_c70b8.
Proof. vm_refl. Qed.
Lemma D_c70b8 : decode_any W_c70b8 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70bc : bv 32 := 0x00158593.
Lemma F_c70bc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7688 : word) = Some W_c70bc.
Proof. vm_refl. Qed.
Lemma D_c70bc : decode_any W_c70bc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70c0 : bv 32 := 0x00377293.
Lemma F_c70c0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc768c : word) = Some W_c70c0.
Proof. vm_refl. Qed.
Lemma D_c70c0 : decode_any W_c70c0 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70c4 : bv 32 := 0x01168023.
Lemma F_c70c4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7690 : word) = Some W_c70c4.
Proof. vm_refl. Qed.
Lemma D_c70c4 : decode_any W_c70c4 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70c8 : bv 32 := 0x00168693.
Lemma F_c70c8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7694 : word) = Some W_c70c8.
Proof. vm_refl. Qed.
Lemma D_c70c8 : decode_any W_c70c8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70cc : bv 32 := 0xfff60613.
Lemma F_c70cc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7698 : word) = Some W_c70cc.
Proof. vm_refl. Qed.
Lemma D_c70cc : decode_any W_c70cc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70d0 : bv 32 := 0x00028a63.
Lemma F_c70d0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc769c : word) = Some W_c70d0.
Proof. vm_refl. Qed.
Lemma D_c70d0 : decode_any W_c70d0 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70d4 : bv 32 := 0x00170713.
Lemma F_c70d4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76a0 : word) = Some W_c70d4.
Proof. vm_refl. Qed.
Lemma D_c70d4 : decode_any W_c70d4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70d8 : bv 32 := 0xfcf81ee3.
Lemma F_c70d8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76a4 : word) = Some W_c70d8.
Proof. vm_refl. Qed.
Lemma D_c70d8 : decode_any W_c70d8 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70dc : bv 32 := 0x0080006f.
Lemma F_c70dc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76a8 : word) = Some W_c70dc.
Proof. vm_refl. Qed.
Lemma D_c70dc : decode_any W_c70dc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70e0 : bv 32 := 0x00050693.
Lemma F_c70e0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76ac : word) = Some W_c70e0.
Proof. vm_refl. Qed.
Lemma D_c70e0 : decode_any W_c70e0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70e4 : bv 32 := 0x0036f793.
Lemma F_c70e4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76b0 : word) = Some W_c70e4.
Proof. vm_refl. Qed.
Lemma D_c70e4 : decode_any W_c70e4 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70e8 : bv 32 := 0x0c078a63.
Lemma F_c70e8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76b4 : word) = Some W_c70e8.
Proof. vm_refl. Qed.
Lemma D_c70e8 : decode_any W_c70e8 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70ec : bv 32 := 0x02000713.
Lemma F_c70ec : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76b8 : word) = Some W_c70ec.
Proof. vm_refl. Qed.
Lemma D_c70ec : decode_any W_c70ec = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70f0 : bv 32 := 0x02e67063.
Lemma F_c70f0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76bc : word) = Some W_c70f0.
Proof. vm_refl. Qed.
Lemma D_c70f0 : decode_any W_c70f0 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70f4 : bv 32 := 0x01000713.
Lemma F_c70f4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76c0 : word) = Some W_c70f4.
Proof. vm_refl. Qed.
Lemma D_c70f4 : decode_any W_c70f4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70f8 : bv 32 := 0x24e67863.
Lemma F_c70f8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76c4 : word) = Some W_c70f8.
Proof. vm_refl. Qed.
Lemma D_c70f8 : decode_any W_c70f8 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_c70fc : bv 32 := 0x00867713.
Lemma F_c70fc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76c8 : word) = Some W_c70fc.
Proof. vm_refl. Qed.
Lemma D_c70fc : decode_any W_c70fc = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7100 : bv 32 := 0x2c071e63.
Lemma F_c7100 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76cc : word) = Some W_c7100.
Proof. vm_refl. Qed.
Lemma D_c7100 : decode_any W_c7100 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7104 : bv 32 := 0x00467713.
Lemma F_c7104 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76d0 : word) = Some W_c7104.
Proof. vm_refl. Qed.
Lemma D_c7104 : decode_any W_c7104 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7108 : bv 32 := 0x32071463.
Lemma F_c7108 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76d4 : word) = Some W_c7108.
Proof. vm_refl. Qed.
Lemma D_c7108 : decode_any W_c7108 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_c710c : bv 32 := 0x3500006f.
Lemma F_c710c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76d8 : word) = Some W_c710c.
Proof. vm_refl. Qed.
Lemma D_c710c : decode_any W_c710c = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7110 : bv 32 := 0x0005a703.
Lemma F_c7110 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76dc : word) = Some W_c7110.
Proof. vm_refl. Qed.
Lemma D_c7110 : decode_any W_c7110 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7114 : bv 32 := 0x00300813.
Lemma F_c7114 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76e0 : word) = Some W_c7114.
Proof. vm_refl. Qed.
Lemma D_c7114 : decode_any W_c7114 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7118 : bv 32 := 0x11078e63.
Lemma F_c7118 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76e4 : word) = Some W_c7118.
Proof. vm_refl. Qed.
Lemma D_c7118 : decode_any W_c7118 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_c711c : bv 32 := 0x00200813.
Lemma F_c711c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76e8 : word) = Some W_c711c.
Proof. vm_refl. Qed.
Lemma D_c711c : decode_any W_c711c = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7120 : bv 32 := 0x19079c63.
Lemma F_c7120 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76ec : word) = Some W_c7120.
Proof. vm_refl. Qed.
Lemma D_c7120 : decode_any W_c7120 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7124 : bv 32 := 0x00875793.
Lemma F_c7124 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76f0 : word) = Some W_c7124.
Proof. vm_refl. Qed.
Lemma D_c7124 : decode_any W_c7124 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7128 : bv 32 := 0xffe60613.
Lemma F_c7128 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76f4 : word) = Some W_c7128.
Proof. vm_refl. Qed.
Lemma D_c7128 : decode_any W_c7128 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c712c : bv 32 := 0x00e68023.
Lemma F_c712c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76f8 : word) = Some W_c712c.
Proof. vm_refl. Qed.
Lemma D_c712c : decode_any W_c712c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7130 : bv 32 := 0x00f680a3.
Lemma F_c7130 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc76fc : word) = Some W_c7130.
Proof. vm_refl. Qed.
Lemma D_c7130 : decode_any W_c7130 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7134 : bv 32 := 0x00268693.
Lemma F_c7134 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7700 : word) = Some W_c7134.
Proof. vm_refl. Qed.
Lemma D_c7134 : decode_any W_c7134 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7138 : bv 32 := 0x01058593.
Lemma F_c7138 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7704 : word) = Some W_c7138.
Proof. vm_refl. Qed.
Lemma D_c7138 : decode_any W_c7138 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c713c : bv 32 := 0x01100793.
Lemma F_c713c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7708 : word) = Some W_c713c.
Proof. vm_refl. Qed.
Lemma D_c713c : decode_any W_c713c = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7140 : bv 32 := 0x0107581b.
Lemma F_c7140 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc770c : word) = Some W_c7140.
Proof. vm_refl. Qed.
Lemma D_c7140 : decode_any W_c7140 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7144 : bv 32 := 0xff45a883.
Lemma F_c7144 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7710 : word) = Some W_c7144.
Proof. vm_refl. Qed.
Lemma D_c7144 : decode_any W_c7144 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7148 : bv 32 := 0xff85a283.
Lemma F_c7148 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7714 : word) = Some W_c7148.
Proof. vm_refl. Qed.
Lemma D_c7148 : decode_any W_c7148 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c714c : bv 32 := 0xffc5a303.
Lemma F_c714c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7718 : word) = Some W_c714c.
Proof. vm_refl. Qed.
Lemma D_c714c : decode_any W_c714c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7150 : bv 32 := 0x0005a703.
Lemma F_c7150 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc771c : word) = Some W_c7150.
Proof. vm_refl. Qed.
Lemma D_c7150 : decode_any W_c7150 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7154 : bv 32 := 0x01089393.
Lemma F_c7154 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7720 : word) = Some W_c7154.
Proof. vm_refl. Qed.
Lemma D_c7154 : decode_any W_c7154 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7158 : bv 32 := 0x0108d89b.
Lemma F_c7158 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7724 : word) = Some W_c7158.
Proof. vm_refl. Qed.
Lemma D_c7158 : decode_any W_c7158 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c715c : bv 32 := 0x0103e833.
Lemma F_c715c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7728 : word) = Some W_c715c.
Proof. vm_refl. Qed.
Lemma D_c715c : decode_any W_c715c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7160 : bv 32 := 0x01029393.
Lemma F_c7160 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc772c : word) = Some W_c7160.
Proof. vm_refl. Qed.
Lemma D_c7160 : decode_any W_c7160 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7164 : bv 32 := 0x0102d29b.
Lemma F_c7164 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7730 : word) = Some W_c7164.
Proof. vm_refl. Qed.
Lemma D_c7164 : decode_any W_c7164 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7168 : bv 32 := 0x0113e8b3.
Lemma F_c7168 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7734 : word) = Some W_c7168.
Proof. vm_refl. Qed.
Lemma D_c7168 : decode_any W_c7168 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c716c : bv 32 := 0x01031393.
Lemma F_c716c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7738 : word) = Some W_c716c.
Proof. vm_refl. Qed.
Lemma D_c716c : decode_any W_c716c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7170 : bv 32 := 0x0103531b.
Lemma F_c7170 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc773c : word) = Some W_c7170.
Proof. vm_refl. Qed.
Lemma D_c7170 : decode_any W_c7170 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7174 : bv 32 := 0x0053e2b3.
Lemma F_c7174 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7740 : word) = Some W_c7174.
Proof. vm_refl. Qed.
Lemma D_c7174 : decode_any W_c7174 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7178 : bv 32 := 0x01071393.
Lemma F_c7178 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7744 : word) = Some W_c7178.
Proof. vm_refl. Qed.
Lemma D_c7178 : decode_any W_c7178 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c717c : bv 32 := 0x0063e333.
Lemma F_c717c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7748 : word) = Some W_c717c.
Proof. vm_refl. Qed.
Lemma D_c717c : decode_any W_c717c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7180 : bv 32 := 0xff060613.
Lemma F_c7180 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc774c : word) = Some W_c7180.
Proof. vm_refl. Qed.
Lemma D_c7180 : decode_any W_c7180 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7184 : bv 32 := 0x0106a023.
Lemma F_c7184 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7750 : word) = Some W_c7184.
Proof. vm_refl. Qed.
Lemma D_c7184 : decode_any W_c7184 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7188 : bv 32 := 0x0116a223.
Lemma F_c7188 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7754 : word) = Some W_c7188.
Proof. vm_refl. Qed.
Lemma D_c7188 : decode_any W_c7188 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c718c : bv 32 := 0x0056a423.
Lemma F_c718c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7758 : word) = Some W_c718c.
Proof. vm_refl. Qed.
Lemma D_c718c : decode_any W_c718c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7190 : bv 32 := 0x0066a623.
Lemma F_c7190 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc775c : word) = Some W_c7190.
Proof. vm_refl. Qed.
Lemma D_c7190 : decode_any W_c7190 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7194 : bv 32 := 0x01068693.
Lemma F_c7194 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7760 : word) = Some W_c7194.
Proof. vm_refl. Qed.
Lemma D_c7194 : decode_any W_c7194 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7198 : bv 32 := 0x01058593.
Lemma F_c7198 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7764 : word) = Some W_c7198.
Proof. vm_refl. Qed.
Lemma D_c7198 : decode_any W_c7198 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c719c : bv 32 := 0xfac7e2e3.
Lemma F_c719c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7768 : word) = Some W_c719c.
Proof. vm_refl. Qed.
Lemma D_c719c : decode_any W_c719c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71a0 : bv 32 := 0xff258593.
Lemma F_c71a0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc776c : word) = Some W_c71a0.
Proof. vm_refl. Qed.
Lemma D_c71a0 : decode_any W_c71a0 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71a4 : bv 32 := 0x01000713.
Lemma F_c71a4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7770 : word) = Some W_c71a4.
Proof. vm_refl. Qed.
Lemma D_c71a4 : decode_any W_c71a4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71a8 : bv 32 := 0xf4e66ae3.
Lemma F_c71a8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7774 : word) = Some W_c71a8.
Proof. vm_refl. Qed.
Lemma D_c71a8 : decode_any W_c71a8 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71ac : bv 32 := 0x19c0006f.
Lemma F_c71ac : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7778 : word) = Some W_c71ac.
Proof. vm_refl. Qed.
Lemma D_c71ac : decode_any W_c71ac = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71b0 : bv 32 := 0x00050693.
Lemma F_c71b0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc777c : word) = Some W_c71b0.
Proof. vm_refl. Qed.
Lemma D_c71b0 : decode_any W_c71b0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71b4 : bv 32 := 0x00357793.
Lemma F_c71b4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7780 : word) = Some W_c71b4.
Proof. vm_refl. Qed.
Lemma D_c71b4 : decode_any W_c71b4 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71b8 : bv 32 := 0xf2079ae3.
Lemma F_c71b8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7784 : word) = Some W_c71b8.
Proof. vm_refl. Qed.
Lemma D_c71b8 : decode_any W_c71b8 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71bc : bv 32 := 0x01000713.
Lemma F_c71bc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7788 : word) = Some W_c71bc.
Proof. vm_refl. Qed.
Lemma D_c71bc : decode_any W_c71bc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71c0 : bv 32 := 0x02e66c63.
Lemma F_c71c0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc778c : word) = Some W_c71c0.
Proof. vm_refl. Qed.
Lemma D_c71c0 : decode_any W_c71c0 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71c4 : bv 32 := 0x00f00713.
Lemma F_c71c4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7790 : word) = Some W_c71c4.
Proof. vm_refl. Qed.
Lemma D_c71c4 : decode_any W_c71c4 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71c8 : bv 32 := 0x0005a783.
Lemma F_c71c8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7794 : word) = Some W_c71c8.
Proof. vm_refl. Qed.
Lemma D_c71c8 : decode_any W_c71c8 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71cc : bv 32 := 0x0045a803.
Lemma F_c71cc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7798 : word) = Some W_c71cc.
Proof. vm_refl. Qed.
Lemma D_c71cc : decode_any W_c71cc = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71d0 : bv 32 := 0x0085a883.
Lemma F_c71d0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc779c : word) = Some W_c71d0.
Proof. vm_refl. Qed.
Lemma D_c71d0 : decode_any W_c71d0 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71d4 : bv 32 := 0x00c5a283.
Lemma F_c71d4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77a0 : word) = Some W_c71d4.
Proof. vm_refl. Qed.
Lemma D_c71d4 : decode_any W_c71d4 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71d8 : bv 32 := 0x01058593.
Lemma F_c71d8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77a4 : word) = Some W_c71d8.
Proof. vm_refl. Qed.
Lemma D_c71d8 : decode_any W_c71d8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71dc : bv 32 := 0xff060613.
Lemma F_c71dc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77a8 : word) = Some W_c71dc.
Proof. vm_refl. Qed.
Lemma D_c71dc : decode_any W_c71dc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71e0 : bv 32 := 0x00f6a023.
Lemma F_c71e0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77ac : word) = Some W_c71e0.
Proof. vm_refl. Qed.
Lemma D_c71e0 : decode_any W_c71e0 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71e4 : bv 32 := 0x0106a223.
Lemma F_c71e4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77b0 : word) = Some W_c71e4.
Proof. vm_refl. Qed.
Lemma D_c71e4 : decode_any W_c71e4 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71e8 : bv 32 := 0x0116a423.
Lemma F_c71e8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77b4 : word) = Some W_c71e8.
Proof. vm_refl. Qed.
Lemma D_c71e8 : decode_any W_c71e8 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71ec : bv 32 := 0x0056a623.
Lemma F_c71ec : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77b8 : word) = Some W_c71ec.
Proof. vm_refl. Qed.
Lemma D_c71ec : decode_any W_c71ec = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71f0 : bv 32 := 0x01068693.
Lemma F_c71f0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77bc : word) = Some W_c71f0.
Proof. vm_refl. Qed.
Lemma D_c71f0 : decode_any W_c71f0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71f4 : bv 32 := 0xfcc76ae3.
Lemma F_c71f4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77c0 : word) = Some W_c71f4.
Proof. vm_refl. Qed.
Lemma D_c71f4 : decode_any W_c71f4 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71f8 : bv 32 := 0x00800713.
Lemma F_c71f8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77c4 : word) = Some W_c71f8.
Proof. vm_refl. Qed.
Lemma D_c71f8 : decode_any W_c71f8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c71fc : bv 32 := 0x00e66e63.
Lemma F_c71fc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77c8 : word) = Some W_c71fc.
Proof. vm_refl. Qed.
Lemma D_c71fc : decode_any W_c71fc = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7200 : bv 32 := 0x0005a703.
Lemma F_c7200 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77cc : word) = Some W_c7200.
Proof. vm_refl. Qed.
Lemma D_c7200 : decode_any W_c7200 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7204 : bv 32 := 0x0045a783.
Lemma F_c7204 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77d0 : word) = Some W_c7204.
Proof. vm_refl. Qed.
Lemma D_c7204 : decode_any W_c7204 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7208 : bv 32 := 0x00e6a023.
Lemma F_c7208 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77d4 : word) = Some W_c7208.
Proof. vm_refl. Qed.
Lemma D_c7208 : decode_any W_c7208 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c720c : bv 32 := 0x00f6a223.
Lemma F_c720c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77d8 : word) = Some W_c720c.
Proof. vm_refl. Qed.
Lemma D_c720c : decode_any W_c720c = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7210 : bv 32 := 0x00868693.
Lemma F_c7210 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77dc : word) = Some W_c7210.
Proof. vm_refl. Qed.
Lemma D_c7210 : decode_any W_c7210 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7214 : bv 32 := 0x00858593.
Lemma F_c7214 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77e0 : word) = Some W_c7214.
Proof. vm_refl. Qed.
Lemma D_c7214 : decode_any W_c7214 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7218 : bv 32 := 0x00467713.
Lemma F_c7218 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77e4 : word) = Some W_c7218.
Proof. vm_refl. Qed.
Lemma D_c7218 : decode_any W_c7218 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c721c : bv 32 := 0x24070063.
Lemma F_c721c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77e8 : word) = Some W_c721c.
Proof. vm_refl. Qed.
Lemma D_c721c : decode_any W_c721c = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7220 : bv 32 := 0x0005a703.
Lemma F_c7220 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77ec : word) = Some W_c7220.
Proof. vm_refl. Qed.
Lemma D_c7220 : decode_any W_c7220 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7224 : bv 32 := 0x00458593.
Lemma F_c7224 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77f0 : word) = Some W_c7224.
Proof. vm_refl. Qed.
Lemma D_c7224 : decode_any W_c7224 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7228 : bv 32 := 0x00e6a023.
Lemma F_c7228 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77f4 : word) = Some W_c7228.
Proof. vm_refl. Qed.
Lemma D_c7228 : decode_any W_c7228 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c722c : bv 32 := 0x00468693.
Lemma F_c722c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77f8 : word) = Some W_c722c.
Proof. vm_refl. Qed.
Lemma D_c722c : decode_any W_c722c = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7230 : bv 32 := 0x22c0006f.
Lemma F_c7230 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc77fc : word) = Some W_c7230.
Proof. vm_refl. Qed.
Lemma D_c7230 : decode_any W_c7230 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7234 : bv 32 := 0x00e68023.
Lemma F_c7234 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7800 : word) = Some W_c7234.
Proof. vm_refl. Qed.
Lemma D_c7234 : decode_any W_c7234 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7238 : bv 32 := 0x00168693.
Lemma F_c7238 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7804 : word) = Some W_c7238.
Proof. vm_refl. Qed.
Lemma D_c7238 : decode_any W_c7238 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c723c : bv 32 := 0xfff60613.
Lemma F_c723c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7808 : word) = Some W_c723c.
Proof. vm_refl. Qed.
Lemma D_c723c : decode_any W_c723c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7240 : bv 32 := 0x01058593.
Lemma F_c7240 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc780c : word) = Some W_c7240.
Proof. vm_refl. Qed.
Lemma D_c7240 : decode_any W_c7240 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7244 : bv 32 := 0x01200793.
Lemma F_c7244 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7810 : word) = Some W_c7244.
Proof. vm_refl. Qed.
Lemma D_c7244 : decode_any W_c7244 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7248 : bv 32 := 0x0087581b.
Lemma F_c7248 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7814 : word) = Some W_c7248.
Proof. vm_refl. Qed.
Lemma D_c7248 : decode_any W_c7248 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c724c : bv 32 := 0xff45a883.
Lemma F_c724c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7818 : word) = Some W_c724c.
Proof. vm_refl. Qed.
Lemma D_c724c : decode_any W_c724c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7250 : bv 32 := 0xff85a283.
Lemma F_c7250 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc781c : word) = Some W_c7250.
Proof. vm_refl. Qed.
Lemma D_c7250 : decode_any W_c7250 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7254 : bv 32 := 0xffc5a303.
Lemma F_c7254 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7820 : word) = Some W_c7254.
Proof. vm_refl. Qed.
Lemma D_c7254 : decode_any W_c7254 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7258 : bv 32 := 0x0005a703.
Lemma F_c7258 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7824 : word) = Some W_c7258.
Proof. vm_refl. Qed.
Lemma D_c7258 : decode_any W_c7258 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c725c : bv 32 := 0x01889393.
Lemma F_c725c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7828 : word) = Some W_c725c.
Proof. vm_refl. Qed.
Lemma D_c725c : decode_any W_c725c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7260 : bv 32 := 0x0088d89b.
Lemma F_c7260 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc782c : word) = Some W_c7260.
Proof. vm_refl. Qed.
Lemma D_c7260 : decode_any W_c7260 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7264 : bv 32 := 0x0103e833.
Lemma F_c7264 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7830 : word) = Some W_c7264.
Proof. vm_refl. Qed.
Lemma D_c7264 : decode_any W_c7264 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7268 : bv 32 := 0x01829393.
Lemma F_c7268 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7834 : word) = Some W_c7268.
Proof. vm_refl. Qed.
Lemma D_c7268 : decode_any W_c7268 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c726c : bv 32 := 0x0082d29b.
Lemma F_c726c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7838 : word) = Some W_c726c.
Proof. vm_refl. Qed.
Lemma D_c726c : decode_any W_c726c = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7270 : bv 32 := 0x0113e8b3.
Lemma F_c7270 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc783c : word) = Some W_c7270.
Proof. vm_refl. Qed.
Lemma D_c7270 : decode_any W_c7270 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7274 : bv 32 := 0x01831393.
Lemma F_c7274 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7840 : word) = Some W_c7274.
Proof. vm_refl. Qed.
Lemma D_c7274 : decode_any W_c7274 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7278 : bv 32 := 0x0083531b.
Lemma F_c7278 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7844 : word) = Some W_c7278.
Proof. vm_refl. Qed.
Lemma D_c7278 : decode_any W_c7278 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c727c : bv 32 := 0x0053e2b3.
Lemma F_c727c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7848 : word) = Some W_c727c.
Proof. vm_refl. Qed.
Lemma D_c727c : decode_any W_c727c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7280 : bv 32 := 0x01871393.
Lemma F_c7280 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc784c : word) = Some W_c7280.
Proof. vm_refl. Qed.
Lemma D_c7280 : decode_any W_c7280 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7284 : bv 32 := 0x0063e333.
Lemma F_c7284 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7850 : word) = Some W_c7284.
Proof. vm_refl. Qed.
Lemma D_c7284 : decode_any W_c7284 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7288 : bv 32 := 0xff060613.
Lemma F_c7288 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7854 : word) = Some W_c7288.
Proof. vm_refl. Qed.
Lemma D_c7288 : decode_any W_c7288 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c728c : bv 32 := 0x0106a023.
Lemma F_c728c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7858 : word) = Some W_c728c.
Proof. vm_refl. Qed.
Lemma D_c728c : decode_any W_c728c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7290 : bv 32 := 0x0116a223.
Lemma F_c7290 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc785c : word) = Some W_c7290.
Proof. vm_refl. Qed.
Lemma D_c7290 : decode_any W_c7290 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7294 : bv 32 := 0x0056a423.
Lemma F_c7294 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7860 : word) = Some W_c7294.
Proof. vm_refl. Qed.
Lemma D_c7294 : decode_any W_c7294 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7298 : bv 32 := 0x0066a623.
Lemma F_c7298 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7864 : word) = Some W_c7298.
Proof. vm_refl. Qed.
Lemma D_c7298 : decode_any W_c7298 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c729c : bv 32 := 0x01068693.
Lemma F_c729c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7868 : word) = Some W_c729c.
Proof. vm_refl. Qed.
Lemma D_c729c : decode_any W_c729c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72a0 : bv 32 := 0x01058593.
Lemma F_c72a0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc786c : word) = Some W_c72a0.
Proof. vm_refl. Qed.
Lemma D_c72a0 : decode_any W_c72a0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72a4 : bv 32 := 0xfac7e2e3.
Lemma F_c72a4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7870 : word) = Some W_c72a4.
Proof. vm_refl. Qed.
Lemma D_c72a4 : decode_any W_c72a4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72a8 : bv 32 := 0xff158593.
Lemma F_c72a8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7874 : word) = Some W_c72a8.
Proof. vm_refl. Qed.
Lemma D_c72a8 : decode_any W_c72a8 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72ac : bv 32 := 0x01000713.
Lemma F_c72ac : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7878 : word) = Some W_c72ac.
Proof. vm_refl. Qed.
Lemma D_c72ac : decode_any W_c72ac = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72b0 : bv 32 := 0xe4e666e3.
Lemma F_c72b0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc787c : word) = Some W_c72b0.
Proof. vm_refl. Qed.
Lemma D_c72b0 : decode_any W_c72b0 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72b4 : bv 32 := 0x0940006f.
Lemma F_c72b4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7880 : word) = Some W_c72b4.
Proof. vm_refl. Qed.
Lemma D_c72b4 : decode_any W_c72b4 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72b8 : bv 32 := 0x00875793.
Lemma F_c72b8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7884 : word) = Some W_c72b8.
Proof. vm_refl. Qed.
Lemma D_c72b8 : decode_any W_c72b8 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72bc : bv 32 := 0x01075813.
Lemma F_c72bc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7888 : word) = Some W_c72bc.
Proof. vm_refl. Qed.
Lemma D_c72bc : decode_any W_c72bc = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72c0 : bv 32 := 0xffd60613.
Lemma F_c72c0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc788c : word) = Some W_c72c0.
Proof. vm_refl. Qed.
Lemma D_c72c0 : decode_any W_c72c0 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72c4 : bv 32 := 0x00e68023.
Lemma F_c72c4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7890 : word) = Some W_c72c4.
Proof. vm_refl. Qed.
Lemma D_c72c4 : decode_any W_c72c4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72c8 : bv 32 := 0x00f680a3.
Lemma F_c72c8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7894 : word) = Some W_c72c8.
Proof. vm_refl. Qed.
Lemma D_c72c8 : decode_any W_c72c8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72cc : bv 32 := 0x01068123.
Lemma F_c72cc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7898 : word) = Some W_c72cc.
Proof. vm_refl. Qed.
Lemma D_c72cc : decode_any W_c72cc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72d0 : bv 32 := 0x00368693.
Lemma F_c72d0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc789c : word) = Some W_c72d0.
Proof. vm_refl. Qed.
Lemma D_c72d0 : decode_any W_c72d0 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72d4 : bv 32 := 0x01058593.
Lemma F_c72d4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78a0 : word) = Some W_c72d4.
Proof. vm_refl. Qed.
Lemma D_c72d4 : decode_any W_c72d4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72d8 : bv 32 := 0x01000793.
Lemma F_c72d8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78a4 : word) = Some W_c72d8.
Proof. vm_refl. Qed.
Lemma D_c72d8 : decode_any W_c72d8 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72dc : bv 32 := 0x0187581b.
Lemma F_c72dc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78a8 : word) = Some W_c72dc.
Proof. vm_refl. Qed.
Lemma D_c72dc : decode_any W_c72dc = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72e0 : bv 32 := 0xff45a883.
Lemma F_c72e0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78ac : word) = Some W_c72e0.
Proof. vm_refl. Qed.
Lemma D_c72e0 : decode_any W_c72e0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72e4 : bv 32 := 0xff85a283.
Lemma F_c72e4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78b0 : word) = Some W_c72e4.
Proof. vm_refl. Qed.
Lemma D_c72e4 : decode_any W_c72e4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72e8 : bv 32 := 0xffc5a303.
Lemma F_c72e8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78b4 : word) = Some W_c72e8.
Proof. vm_refl. Qed.
Lemma D_c72e8 : decode_any W_c72e8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72ec : bv 32 := 0x0005a703.
Lemma F_c72ec : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78b8 : word) = Some W_c72ec.
Proof. vm_refl. Qed.
Lemma D_c72ec : decode_any W_c72ec = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72f0 : bv 32 := 0x00889393.
Lemma F_c72f0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78bc : word) = Some W_c72f0.
Proof. vm_refl. Qed.
Lemma D_c72f0 : decode_any W_c72f0 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72f4 : bv 32 := 0x0188d89b.
Lemma F_c72f4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78c0 : word) = Some W_c72f4.
Proof. vm_refl. Qed.
Lemma D_c72f4 : decode_any W_c72f4 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72f8 : bv 32 := 0x0103e833.
Lemma F_c72f8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78c4 : word) = Some W_c72f8.
Proof. vm_refl. Qed.
Lemma D_c72f8 : decode_any W_c72f8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c72fc : bv 32 := 0x00829393.
Lemma F_c72fc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78c8 : word) = Some W_c72fc.
Proof. vm_refl. Qed.
Lemma D_c72fc : decode_any W_c72fc = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7300 : bv 32 := 0x0182d29b.
Lemma F_c7300 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78cc : word) = Some W_c7300.
Proof. vm_refl. Qed.
Lemma D_c7300 : decode_any W_c7300 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7304 : bv 32 := 0x0113e8b3.
Lemma F_c7304 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78d0 : word) = Some W_c7304.
Proof. vm_refl. Qed.
Lemma D_c7304 : decode_any W_c7304 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7308 : bv 32 := 0x00831393.
Lemma F_c7308 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78d4 : word) = Some W_c7308.
Proof. vm_refl. Qed.
Lemma D_c7308 : decode_any W_c7308 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c730c : bv 32 := 0x0183531b.
Lemma F_c730c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78d8 : word) = Some W_c730c.
Proof. vm_refl. Qed.
Lemma D_c730c : decode_any W_c730c = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7310 : bv 32 := 0x0053e2b3.
Lemma F_c7310 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78dc : word) = Some W_c7310.
Proof. vm_refl. Qed.
Lemma D_c7310 : decode_any W_c7310 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7314 : bv 32 := 0x00871393.
Lemma F_c7314 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78e0 : word) = Some W_c7314.
Proof. vm_refl. Qed.
Lemma D_c7314 : decode_any W_c7314 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7318 : bv 32 := 0x0063e333.
Lemma F_c7318 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78e4 : word) = Some W_c7318.
Proof. vm_refl. Qed.
Lemma D_c7318 : decode_any W_c7318 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c731c : bv 32 := 0xff060613.
Lemma F_c731c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78e8 : word) = Some W_c731c.
Proof. vm_refl. Qed.
Lemma D_c731c : decode_any W_c731c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7320 : bv 32 := 0x0106a023.
Lemma F_c7320 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78ec : word) = Some W_c7320.
Proof. vm_refl. Qed.
Lemma D_c7320 : decode_any W_c7320 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7324 : bv 32 := 0x0116a223.
Lemma F_c7324 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78f0 : word) = Some W_c7324.
Proof. vm_refl. Qed.
Lemma D_c7324 : decode_any W_c7324 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7328 : bv 32 := 0x0056a423.
Lemma F_c7328 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78f4 : word) = Some W_c7328.
Proof. vm_refl. Qed.
Lemma D_c7328 : decode_any W_c7328 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c732c : bv 32 := 0x0066a623.
Lemma F_c732c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78f8 : word) = Some W_c732c.
Proof. vm_refl. Qed.
Lemma D_c732c : decode_any W_c732c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7330 : bv 32 := 0x01068693.
Lemma F_c7330 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc78fc : word) = Some W_c7330.
Proof. vm_refl. Qed.
Lemma D_c7330 : decode_any W_c7330 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7334 : bv 32 := 0x01058593.
Lemma F_c7334 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7900 : word) = Some W_c7334.
Proof. vm_refl. Qed.
Lemma D_c7334 : decode_any W_c7334 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7338 : bv 32 := 0xfac7e2e3.
Lemma F_c7338 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7904 : word) = Some W_c7338.
Proof. vm_refl. Qed.
Lemma D_c7338 : decode_any W_c7338 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c733c : bv 32 := 0xff358593.
Lemma F_c733c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7908 : word) = Some W_c733c.
Proof. vm_refl. Qed.
Lemma D_c733c : decode_any W_c733c = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7340 : bv 32 := 0x01000713.
Lemma F_c7340 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc790c : word) = Some W_c7340.
Proof. vm_refl. Qed.
Lemma D_c7340 : decode_any W_c7340 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7344 : bv 32 := 0xdae66ce3.
Lemma F_c7344 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7910 : word) = Some W_c7344.
Proof. vm_refl. Qed.
Lemma D_c7344 : decode_any W_c7344 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7348 : bv 32 := 0x0005c703.
Lemma F_c7348 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7914 : word) = Some W_c7348.
Proof. vm_refl. Qed.
Lemma D_c7348 : decode_any W_c7348 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c734c : bv 32 := 0x0015c783.
Lemma F_c734c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7918 : word) = Some W_c734c.
Proof. vm_refl. Qed.
Lemma D_c734c : decode_any W_c734c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7350 : bv 32 := 0x0025c803.
Lemma F_c7350 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc791c : word) = Some W_c7350.
Proof. vm_refl. Qed.
Lemma D_c7350 : decode_any W_c7350 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7354 : bv 32 := 0x0035c883.
Lemma F_c7354 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7920 : word) = Some W_c7354.
Proof. vm_refl. Qed.
Lemma D_c7354 : decode_any W_c7354 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7358 : bv 32 := 0x0045c283.
Lemma F_c7358 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7924 : word) = Some W_c7358.
Proof. vm_refl. Qed.
Lemma D_c7358 : decode_any W_c7358 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c735c : bv 32 := 0x0055c303.
Lemma F_c735c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7928 : word) = Some W_c735c.
Proof. vm_refl. Qed.
Lemma D_c735c : decode_any W_c735c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7360 : bv 32 := 0x0065c383.
Lemma F_c7360 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc792c : word) = Some W_c7360.
Proof. vm_refl. Qed.
Lemma D_c7360 : decode_any W_c7360 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7364 : bv 32 := 0x0075ce03.
Lemma F_c7364 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7930 : word) = Some W_c7364.
Proof. vm_refl. Qed.
Lemma D_c7364 : decode_any W_c7364 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7368 : bv 32 := 0x00e68023.
Lemma F_c7368 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7934 : word) = Some W_c7368.
Proof. vm_refl. Qed.
Lemma D_c7368 : decode_any W_c7368 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c736c : bv 32 := 0x00f680a3.
Lemma F_c736c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7938 : word) = Some W_c736c.
Proof. vm_refl. Qed.
Lemma D_c736c : decode_any W_c736c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7370 : bv 32 := 0x01068123.
Lemma F_c7370 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc793c : word) = Some W_c7370.
Proof. vm_refl. Qed.
Lemma D_c7370 : decode_any W_c7370 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7374 : bv 32 := 0x011681a3.
Lemma F_c7374 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7940 : word) = Some W_c7374.
Proof. vm_refl. Qed.
Lemma D_c7374 : decode_any W_c7374 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7378 : bv 32 := 0x0085c703.
Lemma F_c7378 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7944 : word) = Some W_c7378.
Proof. vm_refl. Qed.
Lemma D_c7378 : decode_any W_c7378 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c737c : bv 32 := 0x0095c783.
Lemma F_c737c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7948 : word) = Some W_c737c.
Proof. vm_refl. Qed.
Lemma D_c737c : decode_any W_c737c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7380 : bv 32 := 0x00a5c803.
Lemma F_c7380 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc794c : word) = Some W_c7380.
Proof. vm_refl. Qed.
Lemma D_c7380 : decode_any W_c7380 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7384 : bv 32 := 0x00b5c883.
Lemma F_c7384 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7950 : word) = Some W_c7384.
Proof. vm_refl. Qed.
Lemma D_c7384 : decode_any W_c7384 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7388 : bv 32 := 0x00568223.
Lemma F_c7388 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7954 : word) = Some W_c7388.
Proof. vm_refl. Qed.
Lemma D_c7388 : decode_any W_c7388 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c738c : bv 32 := 0x006682a3.
Lemma F_c738c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7958 : word) = Some W_c738c.
Proof. vm_refl. Qed.
Lemma D_c738c : decode_any W_c738c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7390 : bv 32 := 0x00768323.
Lemma F_c7390 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc795c : word) = Some W_c7390.
Proof. vm_refl. Qed.
Lemma D_c7390 : decode_any W_c7390 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7394 : bv 32 := 0x01c683a3.
Lemma F_c7394 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7960 : word) = Some W_c7394.
Proof. vm_refl. Qed.
Lemma D_c7394 : decode_any W_c7394 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7398 : bv 32 := 0x00c5c283.
Lemma F_c7398 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7964 : word) = Some W_c7398.
Proof. vm_refl. Qed.
Lemma D_c7398 : decode_any W_c7398 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c739c : bv 32 := 0x00d5c303.
Lemma F_c739c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7968 : word) = Some W_c739c.
Proof. vm_refl. Qed.
Lemma D_c739c : decode_any W_c739c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73a0 : bv 32 := 0x00e5c383.
Lemma F_c73a0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc796c : word) = Some W_c73a0.
Proof. vm_refl. Qed.
Lemma D_c73a0 : decode_any W_c73a0 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73a4 : bv 32 := 0x00f5ce03.
Lemma F_c73a4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7970 : word) = Some W_c73a4.
Proof. vm_refl. Qed.
Lemma D_c73a4 : decode_any W_c73a4 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73a8 : bv 32 := 0x01058593.
Lemma F_c73a8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7974 : word) = Some W_c73a8.
Proof. vm_refl. Qed.
Lemma D_c73a8 : decode_any W_c73a8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73ac : bv 32 := 0x00e68423.
Lemma F_c73ac : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7978 : word) = Some W_c73ac.
Proof. vm_refl. Qed.
Lemma D_c73ac : decode_any W_c73ac = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73b0 : bv 32 := 0x00f684a3.
Lemma F_c73b0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc797c : word) = Some W_c73b0.
Proof. vm_refl. Qed.
Lemma D_c73b0 : decode_any W_c73b0 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73b4 : bv 32 := 0x01068523.
Lemma F_c73b4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7980 : word) = Some W_c73b4.
Proof. vm_refl. Qed.
Lemma D_c73b4 : decode_any W_c73b4 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73b8 : bv 32 := 0x011685a3.
Lemma F_c73b8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7984 : word) = Some W_c73b8.
Proof. vm_refl. Qed.
Lemma D_c73b8 : decode_any W_c73b8 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73bc : bv 32 := 0x01068713.
Lemma F_c73bc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7988 : word) = Some W_c73bc.
Proof. vm_refl. Qed.
Lemma D_c73bc : decode_any W_c73bc = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73c0 : bv 32 := 0x00568623.
Lemma F_c73c0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc798c : word) = Some W_c73c0.
Proof. vm_refl. Qed.
Lemma D_c73c0 : decode_any W_c73c0 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73c4 : bv 32 := 0x006686a3.
Lemma F_c73c4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7990 : word) = Some W_c73c4.
Proof. vm_refl. Qed.
Lemma D_c73c4 : decode_any W_c73c4 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73c8 : bv 32 := 0x00768723.
Lemma F_c73c8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7994 : word) = Some W_c73c8.
Proof. vm_refl. Qed.
Lemma D_c73c8 : decode_any W_c73c8 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73cc : bv 32 := 0x01c687a3.
Lemma F_c73cc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7998 : word) = Some W_c73cc.
Proof. vm_refl. Qed.
Lemma D_c73cc : decode_any W_c73cc = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73d0 : bv 32 := 0x00070693.
Lemma F_c73d0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc799c : word) = Some W_c73d0.
Proof. vm_refl. Qed.
Lemma D_c73d0 : decode_any W_c73d0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73d4 : bv 32 := 0x00867713.
Lemma F_c73d4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79a0 : word) = Some W_c73d4.
Proof. vm_refl. Qed.
Lemma D_c73d4 : decode_any W_c73d4 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73d8 : bv 32 := 0xd20706e3.
Lemma F_c73d8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79a4 : word) = Some W_c73d8.
Proof. vm_refl. Qed.
Lemma D_c73d8 : decode_any W_c73d8 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73dc : bv 32 := 0x0005c703.
Lemma F_c73dc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79a8 : word) = Some W_c73dc.
Proof. vm_refl. Qed.
Lemma D_c73dc : decode_any W_c73dc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73e0 : bv 32 := 0x0015c783.
Lemma F_c73e0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79ac : word) = Some W_c73e0.
Proof. vm_refl. Qed.
Lemma D_c73e0 : decode_any W_c73e0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73e4 : bv 32 := 0x0025c803.
Lemma F_c73e4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79b0 : word) = Some W_c73e4.
Proof. vm_refl. Qed.
Lemma D_c73e4 : decode_any W_c73e4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73e8 : bv 32 := 0x0035c883.
Lemma F_c73e8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79b4 : word) = Some W_c73e8.
Proof. vm_refl. Qed.
Lemma D_c73e8 : decode_any W_c73e8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73ec : bv 32 := 0x0045c283.
Lemma F_c73ec : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79b8 : word) = Some W_c73ec.
Proof. vm_refl. Qed.
Lemma D_c73ec : decode_any W_c73ec = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73f0 : bv 32 := 0x0055c303.
Lemma F_c73f0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79bc : word) = Some W_c73f0.
Proof. vm_refl. Qed.
Lemma D_c73f0 : decode_any W_c73f0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73f4 : bv 32 := 0x0065c383.
Lemma F_c73f4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79c0 : word) = Some W_c73f4.
Proof. vm_refl. Qed.
Lemma D_c73f4 : decode_any W_c73f4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73f8 : bv 32 := 0x0075ce03.
Lemma F_c73f8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79c4 : word) = Some W_c73f8.
Proof. vm_refl. Qed.
Lemma D_c73f8 : decode_any W_c73f8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c73fc : bv 32 := 0x00858593.
Lemma F_c73fc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79c8 : word) = Some W_c73fc.
Proof. vm_refl. Qed.
Lemma D_c73fc : decode_any W_c73fc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7400 : bv 32 := 0x00e68023.
Lemma F_c7400 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79cc : word) = Some W_c7400.
Proof. vm_refl. Qed.
Lemma D_c7400 : decode_any W_c7400 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7404 : bv 32 := 0x00f680a3.
Lemma F_c7404 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79d0 : word) = Some W_c7404.
Proof. vm_refl. Qed.
Lemma D_c7404 : decode_any W_c7404 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7408 : bv 32 := 0x01068123.
Lemma F_c7408 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79d4 : word) = Some W_c7408.
Proof. vm_refl. Qed.
Lemma D_c7408 : decode_any W_c7408 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c740c : bv 32 := 0x011681a3.
Lemma F_c740c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79d8 : word) = Some W_c740c.
Proof. vm_refl. Qed.
Lemma D_c740c : decode_any W_c740c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7410 : bv 32 := 0x00868713.
Lemma F_c7410 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79dc : word) = Some W_c7410.
Proof. vm_refl. Qed.
Lemma D_c7410 : decode_any W_c7410 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7414 : bv 32 := 0x00568223.
Lemma F_c7414 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79e0 : word) = Some W_c7414.
Proof. vm_refl. Qed.
Lemma D_c7414 : decode_any W_c7414 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7418 : bv 32 := 0x006682a3.
Lemma F_c7418 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79e4 : word) = Some W_c7418.
Proof. vm_refl. Qed.
Lemma D_c7418 : decode_any W_c7418 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c741c : bv 32 := 0x00768323.
Lemma F_c741c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79e8 : word) = Some W_c741c.
Proof. vm_refl. Qed.
Lemma D_c741c : decode_any W_c741c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7420 : bv 32 := 0x01c683a3.
Lemma F_c7420 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79ec : word) = Some W_c7420.
Proof. vm_refl. Qed.
Lemma D_c7420 : decode_any W_c7420 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7424 : bv 32 := 0x00070693.
Lemma F_c7424 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79f0 : word) = Some W_c7424.
Proof. vm_refl. Qed.
Lemma D_c7424 : decode_any W_c7424 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7428 : bv 32 := 0x00467713.
Lemma F_c7428 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79f4 : word) = Some W_c7428.
Proof. vm_refl. Qed.
Lemma D_c7428 : decode_any W_c7428 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c742c : bv 32 := 0x02070863.
Lemma F_c742c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79f8 : word) = Some W_c742c.
Proof. vm_refl. Qed.
Lemma D_c742c : decode_any W_c742c = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7430 : bv 32 := 0x0005c703.
Lemma F_c7430 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc79fc : word) = Some W_c7430.
Proof. vm_refl. Qed.
Lemma D_c7430 : decode_any W_c7430 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7434 : bv 32 := 0x0015c783.
Lemma F_c7434 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a00 : word) = Some W_c7434.
Proof. vm_refl. Qed.
Lemma D_c7434 : decode_any W_c7434 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7438 : bv 32 := 0x0025c803.
Lemma F_c7438 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a04 : word) = Some W_c7438.
Proof. vm_refl. Qed.
Lemma D_c7438 : decode_any W_c7438 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c743c : bv 32 := 0x0035c883.
Lemma F_c743c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a08 : word) = Some W_c743c.
Proof. vm_refl. Qed.
Lemma D_c743c : decode_any W_c743c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7440 : bv 32 := 0x00458593.
Lemma F_c7440 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a0c : word) = Some W_c7440.
Proof. vm_refl. Qed.
Lemma D_c7440 : decode_any W_c7440 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7444 : bv 32 := 0x00468293.
Lemma F_c7444 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a10 : word) = Some W_c7444.
Proof. vm_refl. Qed.
Lemma D_c7444 : decode_any W_c7444 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7448 : bv 32 := 0x00e68023.
Lemma F_c7448 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a14 : word) = Some W_c7448.
Proof. vm_refl. Qed.
Lemma D_c7448 : decode_any W_c7448 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c744c : bv 32 := 0x00f680a3.
Lemma F_c744c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a18 : word) = Some W_c744c.
Proof. vm_refl. Qed.
Lemma D_c744c : decode_any W_c744c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7450 : bv 32 := 0x01068123.
Lemma F_c7450 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a1c : word) = Some W_c7450.
Proof. vm_refl. Qed.
Lemma D_c7450 : decode_any W_c7450 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7454 : bv 32 := 0x011681a3.
Lemma F_c7454 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a20 : word) = Some W_c7454.
Proof. vm_refl. Qed.
Lemma D_c7454 : decode_any W_c7454 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7458 : bv 32 := 0x00028693.
Lemma F_c7458 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a24 : word) = Some W_c7458.
Proof. vm_refl. Qed.
Lemma D_c7458 : decode_any W_c7458 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c745c : bv 32 := 0x00267713.
Lemma F_c745c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a28 : word) = Some W_c745c.
Proof. vm_refl. Qed.
Lemma D_c745c : decode_any W_c745c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7460 : bv 32 := 0x00071863.
Lemma F_c7460 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a2c : word) = Some W_c7460.
Proof. vm_refl. Qed.
Lemma D_c7460 : decode_any W_c7460 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7464 : bv 32 := 0x00167613.
Lemma F_c7464 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a30 : word) = Some W_c7464.
Proof. vm_refl. Qed.
Lemma D_c7464 : decode_any W_c7464 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7468 : bv 32 := 0x02061663.
Lemma F_c7468 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a34 : word) = Some W_c7468.
Proof. vm_refl. Qed.
Lemma D_c7468 : decode_any W_c7468 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_c746c : bv 32 := 0x00008067.
Lemma F_c746c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a38 : word) = Some W_c746c.
Proof. vm_refl. Qed.
Lemma D_c746c : decode_any W_c746c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7470 : bv 32 := 0x0005c703.
Lemma F_c7470 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a3c : word) = Some W_c7470.
Proof. vm_refl. Qed.
Lemma D_c7470 : decode_any W_c7470 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7474 : bv 32 := 0x0015c783.
Lemma F_c7474 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a40 : word) = Some W_c7474.
Proof. vm_refl. Qed.
Lemma D_c7474 : decode_any W_c7474 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7478 : bv 32 := 0x00258593.
Lemma F_c7478 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a44 : word) = Some W_c7478.
Proof. vm_refl. Qed.
Lemma D_c7478 : decode_any W_c7478 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c747c : bv 32 := 0x00268813.
Lemma F_c747c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a48 : word) = Some W_c747c.
Proof. vm_refl. Qed.
Lemma D_c747c : decode_any W_c747c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7480 : bv 32 := 0x00e68023.
Lemma F_c7480 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a4c : word) = Some W_c7480.
Proof. vm_refl. Qed.
Lemma D_c7480 : decode_any W_c7480 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7484 : bv 32 := 0x00f680a3.
Lemma F_c7484 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a50 : word) = Some W_c7484.
Proof. vm_refl. Qed.
Lemma D_c7484 : decode_any W_c7484 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7488 : bv 32 := 0x00080693.
Lemma F_c7488 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a54 : word) = Some W_c7488.
Proof. vm_refl. Qed.
Lemma D_c7488 : decode_any W_c7488 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c748c : bv 32 := 0x00167613.
Lemma F_c748c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a58 : word) = Some W_c748c.
Proof. vm_refl. Qed.
Lemma D_c748c : decode_any W_c748c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7490 : bv 32 := 0xfc060ee3.
Lemma F_c7490 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a5c : word) = Some W_c7490.
Proof. vm_refl. Qed.
Lemma D_c7490 : decode_any W_c7490 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7494 : bv 32 := 0x0005c583.
Lemma F_c7494 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a60 : word) = Some W_c7494.
Proof. vm_refl. Qed.
Lemma D_c7494 : decode_any W_c7494 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7498 : bv 32 := 0x00b68023.
Lemma F_c7498 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a64 : word) = Some W_c7498.
Proof. vm_refl. Qed.
Lemma D_c7498 : decode_any W_c7498 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c749c : bv 32 := 0x00008067.
Lemma F_c749c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a68 : word) = Some W_c749c.
Proof. vm_refl. Qed.
Lemma D_c749c : decode_any W_c749c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
