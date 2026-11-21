(* reloc-zl14c *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress3_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition TW_1a158 : bv 32 := 0x0e868513.
Lemma TF_1a158 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a164 : word) = Some TW_1a158.
Proof. vm_refl. Qed.
Lemma TD_1a158 : decode_any TW_1a158 = Some (OpImm ALU_ADD 10 13 232, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a15c : bv 32 := 0x40a787b3.
Lemma TF_1a15c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a168 : word) = Some TW_1a15c.
Proof. vm_refl. Qed.
Lemma TD_1a15c : decode_any TW_1a15c = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a160 : bv 32 := 0x00f77733.
Lemma TF_1a160 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a16c : word) = Some TW_1a160.
Proof. vm_refl. Qed.
Lemma TD_1a160 : decode_any TW_1a160 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a164 : bv 32 := 0xfff64693.
Lemma TF_1a164 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a170 : word) = Some TW_1a164.
Proof. vm_refl. Qed.
Lemma TD_1a164 : decode_any TW_1a164 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a168 : bv 32 := 0x00e50933.
Lemma TF_1a168 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a174 : word) = Some TW_1a168.
Proof. vm_refl. Qed.
Lemma TD_1a168 : decode_any TW_1a168 = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a16c : bv 32 := 0x00369693.
Lemma TF_1a16c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a178 : word) = Some TW_1a16c.
Proof. vm_refl. Qed.
Lemma TD_1a16c : decode_any TW_1a16c = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a170 : bv 32 := 0x00d506b3.
Lemma TF_1a170 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a17c : word) = Some TW_1a170.
Proof. vm_refl. Qed.
Lemma TD_1a170 : decode_any TW_1a170 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a174 : bv 32 := 0x00b68a33.
Lemma TF_1a174 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a180 : word) = Some TW_1a174.
Proof. vm_refl. Qed.
Lemma TD_1a174 : decode_any TW_1a174 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a178 : bv 32 := 0x0c890413.
Lemma TF_1a178 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a184 : word) = Some TW_1a178.
Proof. vm_refl. Qed.
Lemma TD_1a178 : decode_any TW_1a178 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a17c : bv 32 := 0x04098463.
Lemma TF_1a17c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a188 : word) = Some TW_1a17c.
Proof. vm_refl. Qed.
Lemma TD_1a17c : decode_any TW_1a17c = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a180 : bv 32 := 0x00361613.
Lemma TF_1a180 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a18c : word) = Some TW_1a180.
Proof. vm_refl. Qed.
Lemma TD_1a180 : decode_any TW_1a180 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a184 : bv 32 := 0x40c50533.
Lemma TF_1a184 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a190 : word) = Some TW_1a184.
Proof. vm_refl. Qed.
Lemma TD_1a184 : decode_any TW_1a184 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a188 : bv 32 := 0x00b50ab3.
Lemma TF_1a188 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a194 : word) = Some TW_1a188.
Proof. vm_refl. Qed.
Lemma TD_1a188 : decode_any TW_1a188 = Some (Op ALU_ADD 21 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a18c : bv 32 := 0x0289b503.
Lemma TF_1a18c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a198 : word) = Some TW_1a18c.
Proof. vm_refl. Qed.
Lemma TD_1a18c : decode_any TW_1a18c = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a190 : bv 32 := 0x00a40533.
Lemma TF_1a190 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a19c : word) = Some TW_1a190.
Proof. vm_refl. Qed.
Lemma TD_1a190 : decode_any TW_1a190 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a194 : bv 32 := 0x7ff50513.
Lemma TF_1a194 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1a0 : word) = Some TW_1a194.
Proof. vm_refl. Qed.
Lemma TD_1a194 : decode_any TW_1a194 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a198 : bv 32 := 0x00150513.
Lemma TF_1a198 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1a4 : word) = Some TW_1a198.
Proof. vm_refl. Qed.
Lemma TD_1a198 : decode_any TW_1a198 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a19c : bv 32 := 0x00aab023.
Lemma TF_1a19c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1a8 : word) = Some TW_1a19c.
Proof. vm_refl. Qed.
Lemma TD_1a19c : decode_any TW_1a19c = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1a0 : bv 32 := 0x0289b503.
Lemma TF_1a1a0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1ac : word) = Some TW_1a1a0.
Proof. vm_refl. Qed.
Lemma TD_1a1a0 : decode_any TW_1a1a0 = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1a4 : bv 32 := 0x0089b583.
Lemma TF_1a1a4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1b0 : word) = Some TW_1a1a4.
Proof. vm_refl. Qed.
Lemma TD_1a1a4 : decode_any TW_1a1a4 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1a8 : bv 32 := 0x0109b603.
Lemma TF_1a1a8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1b4 : word) = Some TW_1a1a8.
Proof. vm_refl. Qed.
Lemma TD_1a1a8 : decode_any TW_1a1a8 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1ac : bv 32 := 0x00a40533.
Lemma TF_1a1ac : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1b8 : word) = Some TW_1a1ac.
Proof. vm_refl. Qed.
Lemma TD_1a1ac : decode_any TW_1a1ac = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1b0 : bv 32 := 0x350070ef.
Lemma TF_1a1b0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1bc : word) = Some TW_1a1b0.
Proof. vm_refl. Qed.
Lemma TD_1a1b0 : decode_any TW_1a1b0 = Some (Jal 1 29520, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1b4 : bv 32 := 0x0009b983.
Lemma TF_1a1b4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1c0 : word) = Some TW_1a1b4.
Proof. vm_refl. Qed.
Lemma TD_1a1b4 : decode_any TW_1a1b4 = Some (Load SZ8 true 19 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1b8 : bv 32 := 0x008a8a93.
Lemma TF_1a1b8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1c4 : word) = Some TW_1a1b8.
Proof. vm_refl. Qed.
Lemma TD_1a1b8 : decode_any TW_1a1b8 = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1bc : bv 32 := 0xfc0998e3.
Lemma TF_1a1bc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1c8 : word) = Some TW_1a1bc.
Proof. vm_refl. Qed.
Lemma TD_1a1bc : decode_any TW_1a1bc = Some (Branch BC_NE 19 0 8144, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1c0 : bv 32 := 0x0284b603.
Lemma TF_1a1c0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1cc : word) = Some TW_1a1c0.
Proof. vm_refl. Qed.
Lemma TD_1a1c0 : decode_any TW_1a1c0 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1c4 : bv 32 := 0x00ca3023.
Lemma TF_1a1c4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1d0 : word) = Some TW_1a1c4.
Proof. vm_refl. Qed.
Lemma TD_1a1c4 : decode_any TW_1a1c4 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1c8 : bv 32 := 0x0d493023.
Lemma TF_1a1c8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1d4 : word) = Some TW_1a1c8.
Proof. vm_refl. Qed.
Lemma TD_1a1c8 : decode_any TW_1a1c8 = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1cc : bv 32 := 0x01293023.
Lemma TF_1a1cc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1d8 : word) = Some TW_1a1cc.
Proof. vm_refl. Qed.
Lemma TD_1a1cc : decode_any TW_1a1cc = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1d0 : bv 32 := 0x00040513.
Lemma TF_1a1d0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1dc : word) = Some TW_1a1d0.
Proof. vm_refl. Qed.
Lemma TD_1a1d0 : decode_any TW_1a1d0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1d4 : bv 32 := 0x45d070ef.
Lemma TF_1a1d4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1e0 : word) = Some TW_1a1d4.
Proof. vm_refl. Qed.
Lemma TD_1a1d4 : decode_any TW_1a1d4 = Some (Jal 1 31836, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1d8 : bv 32 := 0x04054a63.
Lemma TF_1a1d8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1e4 : word) = Some TW_1a1d8.
Proof. vm_refl. Qed.
Lemma TD_1a1d8 : decode_any TW_1a1d8 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1dc : bv 32 := 0x00051663.
Lemma TF_1a1dc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1e8 : word) = Some TW_1a1dc.
Proof. vm_refl. Qed.
Lemma TD_1a1dc : decode_any TW_1a1dc = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1e0 : bv 32 := 0x00100513.
Lemma TF_1a1e0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1ec : word) = Some TW_1a1e0.
Proof. vm_refl. Qed.
Lemma TD_1a1e0 : decode_any TW_1a1e0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1e4 : bv 32 := 0x00a48023.
Lemma TF_1a1e4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1f0 : word) = Some TW_1a1e4.
Proof. vm_refl. Qed.
Lemma TD_1a1e4 : decode_any TW_1a1e4 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1e8 : bv 32 := 0x00200513.
Lemma TF_1a1e8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1f4 : word) = Some TW_1a1e8.
Proof. vm_refl. Qed.
Lemma TD_1a1e8 : decode_any TW_1a1e8 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1ec : bv 32 := 0x0007a597.
Lemma TF_1a1ec : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1f8 : word) = Some TW_1a1ec.
Proof. vm_refl. Qed.
Lemma TD_1a1ec : decode_any TW_1a1ec = Some (Auipc 11 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1f0 : bv 32 := 0x02a92423.
Lemma TF_1a1f0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a1fc : word) = Some TW_1a1f0.
Proof. vm_refl. Qed.
Lemma TD_1a1f0 : decode_any TW_1a1f0 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1f4 : bv 32 := 0x06000893.
Lemma TF_1a1f4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a200 : word) = Some TW_1a1f4.
Proof. vm_refl. Qed.
Lemma TD_1a1f4 : decode_any TW_1a1f4 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1f8 : bv 32 := 0x11058513.
Lemma TF_1a1f8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a204 : word) = Some TW_1a1f8.
Proof. vm_refl. Qed.
Lemma TD_1a1f8 : decode_any TW_1a1f8 = Some (OpImm ALU_ADD 10 11 272, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a1fc : bv 32 := 0x03848593.
Lemma TF_1a1fc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a208 : word) = Some TW_1a1fc.
Proof. vm_refl. Qed.
Lemma TD_1a1fc : decode_any TW_1a1fc = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a200 : bv 32 := 0x00000073.
Lemma TF_1a200 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a20c : word) = Some TW_1a200.
Proof. vm_refl. Qed.
Lemma TD_1a200 : decode_any TW_1a200 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_1a200 : is_ecall TW_1a200 = true.
Proof. reflexivity. Qed.

Definition TW_1a204 : bv 32 := 0x07890613.
Lemma TF_1a204 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a210 : word) = Some TW_1a204.
Proof. vm_refl. Qed.
Lemma TD_1a204 : decode_any TW_1a204 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a208 : bv 32 := 0x02a92023.
Lemma TF_1a208 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a214 : word) = Some TW_1a208.
Proof. vm_refl. Qed.
Lemma TD_1a208 : decode_any TW_1a208 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a20c : bv 32 := 0x08b93c23.
Lemma TF_1a20c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a218 : word) = Some TW_1a20c.
Proof. vm_refl. Qed.
Lemma TD_1a20c : decode_any TW_1a20c = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a210 : bv 32 := 0x06c93c23.
Lemma TF_1a210 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a21c : word) = Some TW_1a210.
Proof. vm_refl. Qed.
Lemma TD_1a210 : decode_any TW_1a210 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a214 : bv 32 := 0x0007a517.
Lemma TF_1a214 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a220 : word) = Some TW_1a214.
Proof. vm_refl. Qed.
Lemma TD_1a214 : decode_any TW_1a214 = Some (Auipc 10 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a218 : bv 32 := 0x35053503.
Lemma TF_1a218 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a224 : word) = Some TW_1a218.
Proof. vm_refl. Qed.
Lemma TD_1a218 : decode_any TW_1a218 = Some (Load SZ8 true 10 10 848, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a21c : bv 32 := 0x01293423.
Lemma TF_1a21c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a228 : word) = Some TW_1a21c.
Proof. vm_refl. Qed.
Lemma TD_1a21c : decode_any TW_1a21c = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a220 : bv 32 := 0x01293823.
Lemma TF_1a220 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a22c : word) = Some TW_1a220.
Proof. vm_refl. Qed.
Lemma TD_1a220 : decode_any TW_1a220 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a224 : bv 32 := 0x00a93c23.
Lemma TF_1a224 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a230 : word) = Some TW_1a224.
Proof. vm_refl. Qed.
Lemma TD_1a224 : decode_any TW_1a224 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a228 : bv 32 := 0x0080006f.
Lemma TF_1a228 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a234 : word) = Some TW_1a228.
Proof. vm_refl. Qed.
Lemma TD_1a228 : decode_any TW_1a228 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a22c : bv 32 := 0x00000023.
Lemma TF_1a22c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a238 : word) = Some TW_1a22c.
Proof. vm_refl. Qed.
Lemma TD_1a22c : decode_any TW_1a22c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a230 : bv 32 := 0x03813083.
Lemma TF_1a230 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a23c : word) = Some TW_1a230.
Proof. vm_refl. Qed.
Lemma TD_1a230 : decode_any TW_1a230 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a234 : bv 32 := 0x03013403.
Lemma TF_1a234 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a240 : word) = Some TW_1a234.
Proof. vm_refl. Qed.
Lemma TD_1a234 : decode_any TW_1a234 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a238 : bv 32 := 0x02813483.
Lemma TF_1a238 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a244 : word) = Some TW_1a238.
Proof. vm_refl. Qed.
Lemma TD_1a238 : decode_any TW_1a238 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a23c : bv 32 := 0x02013903.
Lemma TF_1a23c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a248 : word) = Some TW_1a23c.
Proof. vm_refl. Qed.
Lemma TD_1a23c : decode_any TW_1a23c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a240 : bv 32 := 0x01813983.
Lemma TF_1a240 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a24c : word) = Some TW_1a240.
Proof. vm_refl. Qed.
Lemma TD_1a240 : decode_any TW_1a240 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a244 : bv 32 := 0x01013a03.
Lemma TF_1a244 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a250 : word) = Some TW_1a244.
Proof. vm_refl. Qed.
Lemma TD_1a244 : decode_any TW_1a244 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a248 : bv 32 := 0x00813a83.
Lemma TF_1a248 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a254 : word) = Some TW_1a248.
Proof. vm_refl. Qed.
Lemma TD_1a248 : decode_any TW_1a248 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a24c : bv 32 := 0x04010113.
Lemma TF_1a24c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a258 : word) = Some TW_1a24c.
Proof. vm_refl. Qed.
Lemma TD_1a24c : decode_any TW_1a24c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition TW_1a250 : bv 32 := 0x00008067.
Lemma TF_1a250 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a25c : word) = Some TW_1a250.
Proof. vm_refl. Qed.
Lemma TD_1a250 : decode_any TW_1a250 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a108 : bv 32 := 0xfd010113.
Lemma F_1a108 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a260 : word) = Some W_1a108.
Proof. vm_refl. Qed.
Lemma D_1a108 : decode_any W_1a108 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a10c : bv 32 := 0x02113423.
Lemma F_1a10c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a264 : word) = Some W_1a10c.
Proof. vm_refl. Qed.
Lemma D_1a10c : decode_any W_1a10c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a110 : bv 32 := 0x02813023.
Lemma F_1a110 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a268 : word) = Some W_1a110.
Proof. vm_refl. Qed.
Lemma D_1a110 : decode_any W_1a110 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a114 : bv 32 := 0x00913c23.
Lemma F_1a114 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a26c : word) = Some W_1a114.
Proof. vm_refl. Qed.
Lemma D_1a114 : decode_any W_1a114 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a118 : bv 32 := 0x01213823.
Lemma F_1a118 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a270 : word) = Some W_1a118.
Proof. vm_refl. Qed.
Lemma D_1a118 : decode_any W_1a118 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a11c : bv 32 := 0x01313423.
Lemma F_1a11c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a274 : word) = Some W_1a11c.
Proof. vm_refl. Qed.
Lemma D_1a11c : decode_any W_1a11c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a120 : bv 32 := 0x0007a517.
Lemma F_1a120 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a278 : word) = Some W_1a120.
Proof. vm_refl. Qed.
Lemma D_1a120 : decode_any W_1a120 = Some (Auipc 10 122, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a124 : bv 32 := 0x0c850913.
Lemma F_1a124 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a27c : word) = Some W_1a124.
Proof. vm_refl. Qed.
Lemma D_1a124 : decode_any W_1a124 = Some (OpImm ALU_ADD 18 10 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a128 : bv 32 := 0x00490413.
Lemma F_1a128 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a280 : word) = Some W_1a128.
Proof. vm_refl. Qed.
Lemma D_1a128 : decode_any W_1a128 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a12c : bv 32 := 0x00040513.
Lemma F_1a12c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a284 : word) = Some W_1a12c.
Proof. vm_refl. Qed.
Lemma D_1a12c : decode_any W_1a12c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a130 : bv 32 := 0x091070ef.
Lemma F_1a130 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a288 : word) = Some W_1a130.
Proof. vm_refl. Qed.
Lemma D_1a130 : decode_any W_1a130 = Some (Jal 1 30864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a134 : bv 32 := 0x01093503.
Lemma F_1a134 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a28c : word) = Some W_1a134.
Proof. vm_refl. Qed.
Lemma D_1a134 : decode_any W_1a134 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a138 : bv 32 := 0x06050863.
Lemma F_1a138 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a290 : word) = Some W_1a138.
Proof. vm_refl. Qed.
Lemma D_1a138 : decode_any W_1a138 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a13c : bv 32 := 0x00892583.
Lemma F_1a13c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a294 : word) = Some W_1a13c.
Proof. vm_refl. Qed.
Lemma D_1a13c : decode_any W_1a13c = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a140 : bv 32 := 0x0180006f.
Lemma F_1a140 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a298 : word) = Some W_1a140.
Proof. vm_refl. Qed.
Lemma D_1a140 : decode_any W_1a140 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a144 : bv 32 := 0x00053503.
Lemma F_1a144 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a29c : word) = Some W_1a144.
Proof. vm_refl. Qed.
Lemma D_1a144 : decode_any W_1a144 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a148 : bv 32 := 0x02000593.
Lemma F_1a148 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2a0 : word) = Some W_1a148.
Proof. vm_refl. Qed.
Lemma D_1a148 : decode_any W_1a148 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a14c : bv 32 := 0x00b92423.
Lemma F_1a14c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2a4 : word) = Some W_1a14c.
Proof. vm_refl. Qed.
Lemma D_1a14c : decode_any W_1a14c = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a150 : bv 32 := 0x00a93823.
Lemma F_1a150 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2a8 : word) = Some W_1a150.
Proof. vm_refl. Qed.
Lemma D_1a150 : decode_any W_1a150 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a154 : bv 32 := 0x04050a63.
Lemma F_1a154 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2ac : word) = Some W_1a154.
Proof. vm_refl. Qed.
Lemma D_1a154 : decode_any W_1a154 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a158 : bv 32 := 0xfff5861b.
Lemma F_1a158 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2b0 : word) = Some W_1a158.
Proof. vm_refl. Qed.
Lemma D_1a158 : decode_any W_1a158 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a15c : bv 32 := 0x00c92423.
Lemma F_1a15c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2b4 : word) = Some W_1a15c.
Proof. vm_refl. Qed.
Lemma D_1a15c : decode_any W_1a15c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a160 : bv 32 := 0xfeb052e3.
Lemma F_1a160 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2b8 : word) = Some W_1a160.
Proof. vm_refl. Qed.
Lemma D_1a160 : decode_any W_1a160 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a164 : bv 32 := 0x01093503.
Lemma F_1a164 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2bc : word) = Some W_1a164.
Proof. vm_refl. Qed.
Lemma D_1a164 : decode_any W_1a164 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a168 : bv 32 := 0x00361613.
Lemma F_1a168 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2c0 : word) = Some W_1a168.
Proof. vm_refl. Qed.
Lemma D_1a168 : decode_any W_1a168 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a16c : bv 32 := 0x00c50533.
Lemma F_1a16c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2c4 : word) = Some W_1a16c.
Proof. vm_refl. Qed.
Lemma D_1a16c : decode_any W_1a16c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a170 : bv 32 := 0x00853983.
Lemma F_1a170 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2c8 : word) = Some W_1a170.
Proof. vm_refl. Qed.
Lemma D_1a170 : decode_any W_1a170 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a174 : bv 32 := 0x10853483.
Lemma F_1a174 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2cc : word) = Some W_1a174.
Proof. vm_refl. Qed.
Lemma D_1a174 : decode_any W_1a174 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a178 : bv 32 := 0x00040513.
Lemma F_1a178 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2d0 : word) = Some W_1a178.
Proof. vm_refl. Qed.
Lemma D_1a178 : decode_any W_1a178 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a17c : bv 32 := 0x2cd070ef.
Lemma F_1a17c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2d4 : word) = Some W_1a17c.
Proof. vm_refl. Qed.
Lemma D_1a17c : decode_any W_1a17c = Some (Jal 1 31436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a180 : bv 32 := 0x00048513.
Lemma F_1a180 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2d8 : word) = Some W_1a180.
Proof. vm_refl. Qed.
Lemma D_1a180 : decode_any W_1a180 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a184 : bv 32 := 0x000980e7.
Lemma F_1a184 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2dc : word) = Some W_1a184.
Proof. vm_refl. Qed.
Lemma D_1a184 : decode_any W_1a184 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a188 : bv 32 := 0x00040513.
Lemma F_1a188 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2e0 : word) = Some W_1a188.
Proof. vm_refl. Qed.
Lemma D_1a188 : decode_any W_1a188 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a18c : bv 32 := 0x035070ef.
Lemma F_1a18c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2e4 : word) = Some W_1a18c.
Proof. vm_refl. Qed.
Lemma D_1a18c : decode_any W_1a18c = Some (Jal 1 30772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a190 : bv 32 := 0x00892503.
Lemma F_1a190 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2e8 : word) = Some W_1a190.
Proof. vm_refl. Qed.
Lemma D_1a190 : decode_any W_1a190 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a194 : bv 32 := 0xfff5061b.
Lemma F_1a194 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2ec : word) = Some W_1a194.
Proof. vm_refl. Qed.
Lemma D_1a194 : decode_any W_1a194 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a198 : bv 32 := 0x00c92423.
Lemma F_1a198 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2f0 : word) = Some W_1a198.
Proof. vm_refl. Qed.
Lemma D_1a198 : decode_any W_1a198 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a19c : bv 32 := 0xfca044e3.
Lemma F_1a19c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2f4 : word) = Some W_1a19c.
Proof. vm_refl. Qed.
Lemma D_1a19c : decode_any W_1a19c = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1a0 : bv 32 := 0x01093503.
Lemma F_1a1a0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2f8 : word) = Some W_1a1a0.
Proof. vm_refl. Qed.
Lemma D_1a1a0 : decode_any W_1a1a0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1a4 : bv 32 := 0xfa1ff06f.
Lemma F_1a1a4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a2fc : word) = Some W_1a1a4.
Proof. vm_refl. Qed.
Lemma D_1a1a4 : decode_any W_1a1a4 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1a8 : bv 32 := 0x00100513.
Lemma F_1a1a8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a300 : word) = Some W_1a1a8.
Proof. vm_refl. Qed.
Lemma D_1a1a8 : decode_any W_1a1a8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1ac : bv 32 := 0x00a90023.
Lemma F_1a1ac : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a304 : word) = Some W_1a1ac.
Proof. vm_refl. Qed.
Lemma D_1a1ac : decode_any W_1a1ac = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1b0 : bv 32 := 0x00040513.
Lemma F_1a1b0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a308 : word) = Some W_1a1b0.
Proof. vm_refl. Qed.
Lemma D_1a1b0 : decode_any W_1a1b0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1b4 : bv 32 := 0x02813083.
Lemma F_1a1b4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a30c : word) = Some W_1a1b4.
Proof. vm_refl. Qed.
Lemma D_1a1b4 : decode_any W_1a1b4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1b8 : bv 32 := 0x02013403.
Lemma F_1a1b8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a310 : word) = Some W_1a1b8.
Proof. vm_refl. Qed.
Lemma D_1a1b8 : decode_any W_1a1b8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1bc : bv 32 := 0x01813483.
Lemma F_1a1bc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a314 : word) = Some W_1a1bc.
Proof. vm_refl. Qed.
Lemma D_1a1bc : decode_any W_1a1bc = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1c0 : bv 32 := 0x01013903.
Lemma F_1a1c0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a318 : word) = Some W_1a1c0.
Proof. vm_refl. Qed.
Lemma D_1a1c0 : decode_any W_1a1c0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1c4 : bv 32 := 0x00813983.
Lemma F_1a1c4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a31c : word) = Some W_1a1c4.
Proof. vm_refl. Qed.
Lemma D_1a1c4 : decode_any W_1a1c4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1c8 : bv 32 := 0x03010113.
Lemma F_1a1c8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a320 : word) = Some W_1a1c8.
Proof. vm_refl. Qed.
Lemma D_1a1c8 : decode_any W_1a1c8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1cc : bv 32 := 0x27d0706f.
Lemma F_1a1cc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a324 : word) = Some W_1a1cc.
Proof. vm_refl. Qed.
Lemma D_1a1cc : decode_any W_1a1cc = Some (Jal 0 31356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a1d0 : bv 32 := 0x00008067.
Lemma F_1a1d0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a328 : word) = Some W_1a1d0.
Proof. vm_refl. Qed.
Lemma D_1a1d0 : decode_any W_1a1d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a298 : bv 32 := 0x00050067.
Lemma F_1a298 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a3f0 : word) = Some W_1a298.
Proof. vm_refl. Qed.
Lemma D_1a298 : decode_any W_1a298 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a29c : bv 32 := 0x00008067.
Lemma F_1a29c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a3f4 : word) = Some W_1a29c.
Proof. vm_refl. Qed.
Lemma D_1a29c : decode_any W_1a29c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2a0 : bv 32 := 0xfe010113.
Lemma F_1a2a0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a3f8 : word) = Some W_1a2a0.
Proof. vm_refl. Qed.
Lemma D_1a2a0 : decode_any W_1a2a0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2a4 : bv 32 := 0x00113c23.
Lemma F_1a2a4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a3fc : word) = Some W_1a2a4.
Proof. vm_refl. Qed.
Lemma D_1a2a4 : decode_any W_1a2a4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2a8 : bv 32 := 0x00813823.
Lemma F_1a2a8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a400 : word) = Some W_1a2a8.
Proof. vm_refl. Qed.
Lemma D_1a2a8 : decode_any W_1a2a8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2ac : bv 32 := 0x00913423.
Lemma F_1a2ac : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a404 : word) = Some W_1a2ac.
Proof. vm_refl. Qed.
Lemma D_1a2ac : decode_any W_1a2ac = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2b0 : bv 32 := 0x00009517.
Lemma F_1a2b0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a408 : word) = Some W_1a2b0.
Proof. vm_refl. Qed.
Lemma D_1a2b0 : decode_any W_1a2b0 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2b4 : bv 32 := 0x00009597.
Lemma F_1a2b4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a40c : word) = Some W_1a2b4.
Proof. vm_refl. Qed.
Lemma D_1a2b4 : decode_any W_1a2b4 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2b8 : bv 32 := 0xb8853503.
Lemma F_1a2b8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a410 : word) = Some W_1a2b8.
Proof. vm_refl. Qed.
Lemma D_1a2b8 : decode_any W_1a2b8 = Some (Load SZ8 true 10 10 2952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2bc : bv 32 := 0xb8c5b403.
Lemma F_1a2bc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a414 : word) = Some W_1a2bc.
Proof. vm_refl. Qed.
Lemma D_1a2bc : decode_any W_1a2bc = Some (Load SZ8 true 8 11 2956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2c0 : bv 32 := 0x00a47c63.
Lemma F_1a2c0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a418 : word) = Some W_1a2c0.
Proof. vm_refl. Qed.
Lemma D_1a2c0 : decode_any W_1a2c0 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2c4 : bv 32 := 0xff853583.
Lemma F_1a2c4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a41c : word) = Some W_1a2c4.
Proof. vm_refl. Qed.
Lemma D_1a2c4 : decode_any W_1a2c4 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2c8 : bv 32 := 0xff850493.
Lemma F_1a2c8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a420 : word) = Some W_1a2c8.
Proof. vm_refl. Qed.
Lemma D_1a2c8 : decode_any W_1a2c8 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2cc : bv 32 := 0x000580e7.
Lemma F_1a2cc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a424 : word) = Some W_1a2cc.
Proof. vm_refl. Qed.
Lemma D_1a2cc : decode_any W_1a2cc = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2d0 : bv 32 := 0x00048513.
Lemma F_1a2d0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a428 : word) = Some W_1a2d0.
Proof. vm_refl. Qed.
Lemma D_1a2d0 : decode_any W_1a2d0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2d4 : bv 32 := 0xfe9468e3.
Lemma F_1a2d4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a42c : word) = Some W_1a2d4.
Proof. vm_refl. Qed.
Lemma D_1a2d4 : decode_any W_1a2d4 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2d8 : bv 32 := 0x01813083.
Lemma F_1a2d8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a430 : word) = Some W_1a2d8.
Proof. vm_refl. Qed.
Lemma D_1a2d8 : decode_any W_1a2d8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2dc : bv 32 := 0x01013403.
Lemma F_1a2dc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a434 : word) = Some W_1a2dc.
Proof. vm_refl. Qed.
Lemma D_1a2dc : decode_any W_1a2dc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2e0 : bv 32 := 0x00813483.
Lemma F_1a2e0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a438 : word) = Some W_1a2e0.
Proof. vm_refl. Qed.
Lemma D_1a2e0 : decode_any W_1a2e0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2e4 : bv 32 := 0x02010113.
Lemma F_1a2e4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a43c : word) = Some W_1a2e4.
Proof. vm_refl. Qed.
Lemma D_1a2e4 : decode_any W_1a2e4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2e8 : bv 32 := 0xfb5ff06f.
Lemma F_1a2e8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a440 : word) = Some W_1a2e8.
Proof. vm_refl. Qed.
Lemma D_1a2e8 : decode_any W_1a2e8 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2ec : bv 32 := 0xff010113.
Lemma F_1a2ec : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a444 : word) = Some W_1a2ec.
Proof. vm_refl. Qed.
Lemma D_1a2ec : decode_any W_1a2ec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2f0 : bv 32 := 0x00113423.
Lemma F_1a2f0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a448 : word) = Some W_1a2f0.
Proof. vm_refl. Qed.
Lemma D_1a2f0 : decode_any W_1a2f0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2f4 : bv 32 := 0x00813023.
Lemma F_1a2f4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a44c : word) = Some W_1a2f4.
Proof. vm_refl. Qed.
Lemma D_1a2f4 : decode_any W_1a2f4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2f8 : bv 32 := 0x00000593.
Lemma F_1a2f8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a450 : word) = Some W_1a2f8.
Proof. vm_refl. Qed.
Lemma D_1a2f8 : decode_any W_1a2f8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a2fc : bv 32 := 0x00020613.
Lemma F_1a2fc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a454 : word) = Some W_1a2fc.
Proof. vm_refl. Qed.
Lemma D_1a2fc : decode_any W_1a2fc = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a300 : bv 32 := 0xf5862603.
Lemma F_1a300 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a458 : word) = Some W_1a300.
Proof. vm_refl. Qed.
Lemma D_1a300 : decode_any W_1a300 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a304 : bv 32 := 0x0007a697.
Lemma F_1a304 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a45c : word) = Some W_1a304.
Proof. vm_refl. Qed.
Lemma D_1a304 : decode_any W_1a304 = Some (Auipc 13 122, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a308 : bv 32 := 0x10468693.
Lemma F_1a308 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a460 : word) = Some W_1a308.
Proof. vm_refl. Qed.
Lemma D_1a308 : decode_any W_1a308 = Some (OpImm ALU_ADD 13 13 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a30c : bv 32 := 0x1606a72f.
Lemma F_1a30c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a464 : word) = Some W_1a30c.
Proof. vm_refl. Qed.
Lemma D_1a30c : decode_any W_1a30c = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a310 : bv 32 := 0x00b71663.
Lemma F_1a310 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a468 : word) = Some W_1a310.
Proof. vm_refl. Qed.
Lemma D_1a310 : decode_any W_1a310 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a314 : bv 32 := 0x1ec6a7af.
Lemma F_1a314 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a46c : word) = Some W_1a314.
Proof. vm_refl. Qed.
Lemma D_1a314 : decode_any W_1a314 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a318 : bv 32 := 0xfe079ae3.
Lemma F_1a318 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a470 : word) = Some W_1a318.
Proof. vm_refl. Qed.
Lemma D_1a318 : decode_any W_1a318 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a31c : bv 32 := 0x0007059b.
Lemma F_1a31c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a474 : word) = Some W_1a31c.
Proof. vm_refl. Qed.
Lemma D_1a31c : decode_any W_1a31c = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a320 : bv 32 := 0x02c58263.
Lemma F_1a320 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a478 : word) = Some W_1a320.
Proof. vm_refl. Qed.
Lemma D_1a320 : decode_any W_1a320 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a324 : bv 32 := 0x02058263.
Lemma F_1a324 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a47c : word) = Some W_1a324.
Proof. vm_refl. Qed.
Lemma D_1a324 : decode_any W_1a324 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a328 : bv 32 := 0x04900893.
Lemma F_1a328 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a480 : word) = Some W_1a328.
Proof. vm_refl. Qed.
Lemma D_1a328 : decode_any W_1a328 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a32c : bv 32 := 0x00000593.
Lemma F_1a32c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a484 : word) = Some W_1a32c.
Proof. vm_refl. Qed.
Lemma D_1a32c : decode_any W_1a32c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a330 : bv 32 := 0x00000613.
Lemma F_1a330 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a488 : word) = Some W_1a330.
Proof. vm_refl. Qed.
Lemma D_1a330 : decode_any W_1a330 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a334 : bv 32 := 0x00000693.
Lemma F_1a334 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a48c : word) = Some W_1a334.
Proof. vm_refl. Qed.
Lemma D_1a334 : decode_any W_1a334 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a338 : bv 32 := 0x00000513.
Lemma F_1a338 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a490 : word) = Some W_1a338.
Proof. vm_refl. Qed.
Lemma D_1a338 : decode_any W_1a338 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a33c : bv 32 := 0x00000073.
Lemma F_1a33c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a494 : word) = Some W_1a33c.
Proof. vm_refl. Qed.
Lemma D_1a33c : decode_any W_1a33c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1a33c : is_ecall W_1a33c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1a340 : bv 32 := 0xff9ff06f.
Lemma F_1a340 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a498 : word) = Some W_1a340.
Proof. vm_refl. Qed.
Lemma D_1a340 : decode_any W_1a340 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a344 : bv 32 := 0x00000023.
Lemma F_1a344 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a49c : word) = Some W_1a344.
Proof. vm_refl. Qed.
Lemma D_1a344 : decode_any W_1a344 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a348 : bv 32 := 0x00050413.
Lemma F_1a348 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a4a0 : word) = Some W_1a348.
Proof. vm_refl. Qed.
Lemma D_1a348 : decode_any W_1a348 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a34c : bv 32 := 0xdbdff0ef.
Lemma F_1a34c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a4a4 : word) = Some W_1a34c.
Proof. vm_refl. Qed.
Lemma D_1a34c : decode_any W_1a34c = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a350 : bv 32 := 0xf51ff0ef.
Lemma F_1a350 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a4a8 : word) = Some W_1a350.
Proof. vm_refl. Qed.
Lemma D_1a350 : decode_any W_1a350 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a354 : bv 32 := 0x258020ef.
Lemma F_1a354 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a4ac : word) = Some W_1a354.
Proof. vm_refl. Qed.
Lemma D_1a354 : decode_any W_1a354 = Some (Jal 1 8792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a358 : bv 32 := 0x00040513.
Lemma F_1a358 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a4b0 : word) = Some W_1a358.
Proof. vm_refl. Qed.
Lemma D_1a358 : decode_any W_1a358 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a35c : bv 32 := 0x004000ef.
Lemma F_1a35c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a4b4 : word) = Some W_1a35c.
Proof. vm_refl. Qed.
Lemma D_1a35c : decode_any W_1a35c = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a360 : bv 32 := 0x00050593.
Lemma F_1a360 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a4b8 : word) = Some W_1a360.
Proof. vm_refl. Qed.
Lemma D_1a360 : decode_any W_1a360 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a364 : bv 32 := 0x05e00893.
Lemma F_1a364 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a4bc : word) = Some W_1a364.
Proof. vm_refl. Qed.
Lemma D_1a364 : decode_any W_1a364 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a368 : bv 32 := 0x00000073.
Lemma F_1a368 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a4c0 : word) = Some W_1a368.
Proof. vm_refl. Qed.
Lemma D_1a368 : decode_any W_1a368 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1a368 : is_ecall W_1a368 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1a460 : bv 32 := 0xff010113.
Lemma F_1a460 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5b8 : word) = Some W_1a460.
Proof. vm_refl. Qed.
Lemma D_1a460 : decode_any W_1a460 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a464 : bv 32 := 0x00113423.
Lemma F_1a464 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5bc : word) = Some W_1a464.
Proof. vm_refl. Qed.
Lemma D_1a464 : decode_any W_1a464 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a468 : bv 32 := 0x00050e63.
Lemma F_1a468 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5c0 : word) = Some W_1a468.
Proof. vm_refl. Qed.
Lemma D_1a468 : decode_any W_1a468 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a46c : bv 32 := 0x00050593.
Lemma F_1a46c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5c4 : word) = Some W_1a46c.
Proof. vm_refl. Qed.
Lemma D_1a46c : decode_any W_1a46c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a470 : bv 32 := 0x00009517.
Lemma F_1a470 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5c8 : word) = Some W_1a470.
Proof. vm_refl. Qed.
Lemma D_1a470 : decode_any W_1a470 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a474 : bv 32 := 0x9c053503.
Lemma F_1a474 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5cc : word) = Some W_1a474.
Proof. vm_refl. Qed.
Lemma D_1a474 : decode_any W_1a474 = Some (Load SZ8 true 10 10 2496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a478 : bv 32 := 0x00800613.
Lemma F_1a478 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5d0 : word) = Some W_1a478.
Proof. vm_refl. Qed.
Lemma D_1a478 : decode_any W_1a478 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a47c : bv 32 := 0x739060ef.
Lemma F_1a47c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5d4 : word) = Some W_1a47c.
Proof. vm_refl. Qed.
Lemma D_1a47c : decode_any W_1a47c = Some (Jal 1 28472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a480 : bv 32 := 0x01c0006f.
Lemma F_1a480 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5d8 : word) = Some W_1a480.
Proof. vm_refl. Qed.
Lemma D_1a480 : decode_any W_1a480 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a484 : bv 32 := 0x00009517.
Lemma F_1a484 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5dc : word) = Some W_1a484.
Proof. vm_refl. Qed.
Lemma D_1a484 : decode_any W_1a484 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a488 : bv 32 := 0x9ac53503.
Lemma F_1a488 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5e0 : word) = Some W_1a488.
Proof. vm_refl. Qed.
Lemma D_1a488 : decode_any W_1a488 = Some (Load SZ8 true 10 10 2476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a48c : bv 32 := 0x41c655b7.
Lemma F_1a48c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5e4 : word) = Some W_1a48c.
Proof. vm_refl. Qed.
Lemma D_1a48c : decode_any W_1a48c = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a490 : bv 32 := 0xe6d5859b.
Lemma F_1a490 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5e8 : word) = Some W_1a490.
Proof. vm_refl. Qed.
Lemma D_1a490 : decode_any W_1a490 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a494 : bv 32 := 0x02b505b3.
Lemma F_1a494 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5ec : word) = Some W_1a494.
Proof. vm_refl. Qed.
Lemma D_1a494 : decode_any W_1a494 = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a498 : bv 32 := 0x00b53023.
Lemma F_1a498 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5f0 : word) = Some W_1a498.
Proof. vm_refl. Qed.
Lemma D_1a498 : decode_any W_1a498 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a49c : bv 32 := 0x00009517.
Lemma F_1a49c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5f4 : word) = Some W_1a49c.
Proof. vm_refl. Qed.
Lemma D_1a49c : decode_any W_1a49c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4a0 : bv 32 := 0x99453503.
Lemma F_1a4a0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5f8 : word) = Some W_1a4a0.
Proof. vm_refl. Qed.
Lemma D_1a4a0 : decode_any W_1a4a0 = Some (Load SZ8 true 10 10 2452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4a4 : bv 32 := 0x000500a3.
Lemma F_1a4a4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a5fc : word) = Some W_1a4a4.
Proof. vm_refl. Qed.
Lemma D_1a4a4 : decode_any W_1a4a4 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4a8 : bv 32 := 0x00053503.
Lemma F_1a4a8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a600 : word) = Some W_1a4a8.
Proof. vm_refl. Qed.
Lemma D_1a4a8 : decode_any W_1a4a8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4ac : bv 32 := 0x00020593.
Lemma F_1a4ac : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a604 : word) = Some W_1a4ac.
Proof. vm_refl. Qed.
Lemma D_1a4ac : decode_any W_1a4ac = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4b0 : bv 32 := 0xfea5b823.
Lemma F_1a4b0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a608 : word) = Some W_1a4b0.
Proof. vm_refl. Qed.
Lemma D_1a4b0 : decode_any W_1a4b0 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4b4 : bv 32 := 0x00813083.
Lemma F_1a4b4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a60c : word) = Some W_1a4b4.
Proof. vm_refl. Qed.
Lemma D_1a4b4 : decode_any W_1a4b4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4b8 : bv 32 := 0x01010113.
Lemma F_1a4b8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a610 : word) = Some W_1a4b8.
Proof. vm_refl. Qed.
Lemma D_1a4b8 : decode_any W_1a4b8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4bc : bv 32 := 0x00008067.
Lemma F_1a4bc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a614 : word) = Some W_1a4bc.
Proof. vm_refl. Qed.
Lemma D_1a4bc : decode_any W_1a4bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4c8 : bv 32 := 0xfffff5b7.
Lemma F_1a4c8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a620 : word) = Some W_1a4c8.
Proof. vm_refl. Qed.
Lemma D_1a4c8 : decode_any W_1a4c8 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4cc : bv 32 := 0x0015859b.
Lemma F_1a4cc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a624 : word) = Some W_1a4cc.
Proof. vm_refl. Qed.
Lemma D_1a4cc : decode_any W_1a4cc = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4d0 : bv 32 := 0x02b56663.
Lemma F_1a4d0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a628 : word) = Some W_1a4d0.
Proof. vm_refl. Qed.
Lemma D_1a4d0 : decode_any W_1a4d0 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4fc : bv 32 := 0x00008067.
Lemma F_1a4fc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a654 : word) = Some W_1a4fc.
Proof. vm_refl. Qed.
Lemma D_1a4fc : decode_any W_1a4fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a650 : bv 32 := 0x1c050463.
Lemma F_1a650 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7a8 : word) = Some W_1a650.
Proof. vm_refl. Qed.
Lemma D_1a650 : decode_any W_1a650 = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a654 : bv 32 := 0xfd010113.
Lemma F_1a654 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7ac : word) = Some W_1a654.
Proof. vm_refl. Qed.
Lemma D_1a654 : decode_any W_1a654 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a658 : bv 32 := 0x02113423.
Lemma F_1a658 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7b0 : word) = Some W_1a658.
Proof. vm_refl. Qed.
Lemma D_1a658 : decode_any W_1a658 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a65c : bv 32 := 0x02813023.
Lemma F_1a65c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7b4 : word) = Some W_1a65c.
Proof. vm_refl. Qed.
Lemma D_1a65c : decode_any W_1a65c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a660 : bv 32 := 0x00913c23.
Lemma F_1a660 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7b8 : word) = Some W_1a660.
Proof. vm_refl. Qed.
Lemma D_1a660 : decode_any W_1a660 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a664 : bv 32 := 0x01213823.
Lemma F_1a664 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7bc : word) = Some W_1a664.
Proof. vm_refl. Qed.
Lemma D_1a664 : decode_any W_1a664 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a668 : bv 32 := 0x01313423.
Lemma F_1a668 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7c0 : word) = Some W_1a668.
Proof. vm_refl. Qed.
Lemma D_1a668 : decode_any W_1a668 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a66c : bv 32 := 0x00050493.
Lemma F_1a66c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7c4 : word) = Some W_1a66c.
Proof. vm_refl. Qed.
Lemma D_1a66c : decode_any W_1a66c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a670 : bv 32 := 0x1ac000ef.
Lemma F_1a670 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7c8 : word) = Some W_1a670.
Proof. vm_refl. Qed.
Lemma D_1a670 : decode_any W_1a670 = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a674 : bv 32 := 0x02053583.
Lemma F_1a674 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7cc : word) = Some W_1a674.
Proof. vm_refl. Qed.
Lemma D_1a674 : decode_any W_1a674 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a678 : bv 32 := 0xffd4c683.
Lemma F_1a678 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7d0 : word) = Some W_1a678.
Proof. vm_refl. Qed.
Lemma D_1a678 : decode_any W_1a678 = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a67c : bv 32 := 0x00c5d613.
Lemma F_1a67c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7d4 : word) = Some W_1a67c.
Proof. vm_refl. Qed.
Lemma D_1a67c : decode_any W_1a67c = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a680 : bv 32 := 0x01f6f413.
Lemma F_1a680 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7d8 : word) = Some W_1a680.
Proof. vm_refl. Qed.
Lemma D_1a680 : decode_any W_1a680 = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a684 : bv 32 := 0x00060e63.
Lemma F_1a684 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7dc : word) = Some W_1a684.
Proof. vm_refl. Qed.
Lemma D_1a684 : decode_any W_1a684 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a688 : bv 32 := 0x01f5f613.
Lemma F_1a688 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7e0 : word) = Some W_1a688.
Proof. vm_refl. Qed.
Lemma D_1a688 : decode_any W_1a688 = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a68c : bv 32 := 0x00061a63.
Lemma F_1a68c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7e4 : word) = Some W_1a68c.
Proof. vm_refl. Qed.
Lemma D_1a68c : decode_any W_1a68c = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a690 : bv 32 := 0xfffff637.
Lemma F_1a690 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7e8 : word) = Some W_1a690.
Proof. vm_refl. Qed.
Lemma D_1a690 : decode_any W_1a690 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a694 : bv 32 := 0x00c5f633.
Lemma F_1a694 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7ec : word) = Some W_1a694.
Proof. vm_refl. Qed.
Lemma D_1a694 : decode_any W_1a694 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a698 : bv 32 := 0xff060613.
Lemma F_1a698 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7f0 : word) = Some W_1a698.
Proof. vm_refl. Qed.
Lemma D_1a698 : decode_any W_1a698 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a69c : bv 32 := 0x0200006f.
Lemma F_1a69c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7f4 : word) = Some W_1a69c.
Proof. vm_refl. Qed.
Lemma D_1a69c : decode_any W_1a69c = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6a0 : bv 32 := 0x0055d613.
Lemma F_1a6a0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7f8 : word) = Some W_1a6a0.
Proof. vm_refl. Qed.
Lemma D_1a6a0 : decode_any W_1a6a0 = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6a4 : bv 32 := 0xffff8717.
Lemma F_1a6a4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a7fc : word) = Some W_1a6a4.
Proof. vm_refl. Qed.
Lemma D_1a6a4 : decode_any W_1a6a4 = Some (Auipc 14 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6a8 : bv 32 := 0x07e67613.
Lemma F_1a6a8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a800 : word) = Some W_1a6a8.
Proof. vm_refl. Qed.
Lemma D_1a6a8 : decode_any W_1a6a8 = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6ac : bv 32 := 0xc6070713.
Lemma F_1a6ac : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a804 : word) = Some W_1a6ac.
Proof. vm_refl. Qed.
Lemma D_1a6ac : decode_any W_1a6ac = Some (OpImm ALU_ADD 14 14 3168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6b0 : bv 32 := 0x00c70633.
Lemma F_1a6b0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a808 : word) = Some W_1a6b0.
Proof. vm_refl. Qed.
Lemma D_1a6b0 : decode_any W_1a6b0 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6b4 : bv 32 := 0x00065603.
Lemma F_1a6b4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a80c : word) = Some W_1a6b4.
Proof. vm_refl. Qed.
Lemma D_1a6b4 : decode_any W_1a6b4 = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6b8 : bv 32 := 0x00461613.
Lemma F_1a6b8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a810 : word) = Some W_1a6b8.
Proof. vm_refl. Qed.
Lemma D_1a6b8 : decode_any W_1a6b8 = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6bc : bv 32 := 0x01053703.
Lemma F_1a6bc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a814 : word) = Some W_1a6bc.
Proof. vm_refl. Qed.
Lemma D_1a6bc : decode_any W_1a6bc = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6c0 : bv 32 := 0x028607b3.
Lemma F_1a6c0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a818 : word) = Some W_1a6c0.
Proof. vm_refl. Qed.
Lemma D_1a6c0 : decode_any W_1a6c0 = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6c4 : bv 32 := 0x0a000813.
Lemma F_1a6c4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a81c : word) = Some W_1a6c4.
Proof. vm_refl. Qed.
Lemma D_1a6c4 : decode_any W_1a6c4 = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6c8 : bv 32 := 0x00c70633.
Lemma F_1a6c8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a820 : word) = Some W_1a6c8.
Proof. vm_refl. Qed.
Lemma D_1a6c8 : decode_any W_1a6c8 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6cc : bv 32 := 0x00f607b3.
Lemma F_1a6cc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a824 : word) = Some W_1a6cc.
Proof. vm_refl. Qed.
Lemma D_1a6cc : decode_any W_1a6cc = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6d0 : bv 32 := 0x00c78613.
Lemma F_1a6d0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a828 : word) = Some W_1a6d0.
Proof. vm_refl. Qed.
Lemma D_1a6d0 : decode_any W_1a6d0 = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6d4 : bv 32 := 0x0056d713.
Lemma F_1a6d4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a82c : word) = Some W_1a6d4.
Proof. vm_refl. Qed.
Lemma D_1a6d4 : decode_any W_1a6d4 = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6d8 : bv 32 := 0x0306e663.
Lemma F_1a6d8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a830 : word) = Some W_1a6d8.
Proof. vm_refl. Qed.
Lemma D_1a6d8 : decode_any W_1a6d8 = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6dc : bv 32 := 0x00500693.
Lemma F_1a6dc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a834 : word) = Some W_1a6dc.
Proof. vm_refl. Qed.
Lemma D_1a6dc : decode_any W_1a6dc = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6e0 : bv 32 := 0x00d70463.
Lemma F_1a6e0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a838 : word) = Some W_1a6e0.
Proof. vm_refl. Qed.
Lemma D_1a6e0 : decode_any W_1a6e0 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6e8 : bv 32 := 0x0087e703.
Lemma F_1a6e8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a840 : word) = Some W_1a6e8.
Proof. vm_refl. Qed.
Lemma D_1a6e8 : decode_any W_1a6e8 = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6ec : bv 32 := 0x00400693.
Lemma F_1a6ec : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a844 : word) = Some W_1a6ec.
Proof. vm_refl. Qed.
Lemma D_1a6ec : decode_any W_1a6ec = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6f0 : bv 32 := 0x00e6e463.
Lemma F_1a6f0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a848 : word) = Some W_1a6f0.
Proof. vm_refl. Qed.
Lemma D_1a6f0 : decode_any W_1a6f0 = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6f8 : bv 32 := 0x0077c683.
Lemma F_1a6f8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a850 : word) = Some W_1a6f8.
Proof. vm_refl. Qed.
Lemma D_1a6f8 : decode_any W_1a6f8 = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a6fc : bv 32 := 0x00068463.
Lemma F_1a6fc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a854 : word) = Some W_1a6fc.
Proof. vm_refl. Qed.
Lemma D_1a6fc : decode_any W_1a6fc = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a704 : bv 32 := 0x409606b3.
Lemma F_1a704 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a85c : word) = Some W_1a704.
Proof. vm_refl. Qed.
Lemma D_1a704 : decode_any W_1a704 = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a708 : bv 32 := 0x00e6f463.
Lemma F_1a708 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a860 : word) = Some W_1a708.
Proof. vm_refl. Qed.
Lemma D_1a708 : decode_any W_1a708 = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a710 : bv 32 := 0x40e606b3.
Lemma F_1a710 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a868 : word) = Some W_1a710.
Proof. vm_refl. Qed.
Lemma D_1a710 : decode_any W_1a710 = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a714 : bv 32 := 0x0006c683.
Lemma F_1a714 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a86c : word) = Some W_1a714.
Proof. vm_refl. Qed.
Lemma D_1a714 : decode_any W_1a714 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a718 : bv 32 := 0x00068463.
Lemma F_1a718 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a870 : word) = Some W_1a718.
Proof. vm_refl. Qed.
Lemma D_1a718 : decode_any W_1a718 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a720 : bv 32 := 0x00064603.
Lemma F_1a720 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a878 : word) = Some W_1a720.
Proof. vm_refl. Qed.
Lemma D_1a720 : decode_any W_1a720 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a724 : bv 32 := 0x00060463.
Lemma F_1a724 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a87c : word) = Some W_1a724.
Proof. vm_refl. Qed.
Lemma D_1a724 : decode_any W_1a724 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a81c : bv 32 := 0x00f57593.
Lemma F_1a81c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a974 : word) = Some W_1a81c.
Proof. vm_refl. Qed.
Lemma D_1a81c : decode_any W_1a81c = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a820 : bv 32 := 0x00058463.
Lemma F_1a820 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a978 : word) = Some W_1a820.
Proof. vm_refl. Qed.
Lemma D_1a820 : decode_any W_1a820 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a828 : bv 32 := 0xffc54603.
Lemma F_1a828 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a980 : word) = Some W_1a828.
Proof. vm_refl. Qed.
Lemma D_1a828 : decode_any W_1a828 = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a82c : bv 32 := 0xffd54683.
Lemma F_1a82c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a984 : word) = Some W_1a82c.
Proof. vm_refl. Qed.
Lemma D_1a82c : decode_any W_1a82c = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a830 : bv 32 := 0xffe55583.
Lemma F_1a830 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a988 : word) = Some W_1a830.
Proof. vm_refl. Qed.
Lemma D_1a830 : decode_any W_1a830 = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a834 : bv 32 := 0x00060e63.
Lemma F_1a834 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a98c : word) = Some W_1a834.
Proof. vm_refl. Qed.
Lemma D_1a834 : decode_any W_1a834 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a850 : bv 32 := 0x00459613.
Lemma F_1a850 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9a8 : word) = Some W_1a850.
Proof. vm_refl. Qed.
Lemma D_1a850 : decode_any W_1a850 = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a854 : bv 32 := 0x40c50633.
Lemma F_1a854 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9ac : word) = Some W_1a854.
Proof. vm_refl. Qed.
Lemma D_1a854 : decode_any W_1a854 = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a858 : bv 32 := 0xff063503.
Lemma F_1a858 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9b0 : word) = Some W_1a858.
Proof. vm_refl. Qed.
Lemma D_1a858 : decode_any W_1a858 = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a85c : bv 32 := 0x01053703.
Lemma F_1a85c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9b4 : word) = Some W_1a85c.
Proof. vm_refl. Qed.
Lemma D_1a85c : decode_any W_1a85c = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a860 : bv 32 := 0xff060613.
Lemma F_1a860 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9b8 : word) = Some W_1a860.
Proof. vm_refl. Qed.
Lemma D_1a860 : decode_any W_1a860 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a864 : bv 32 := 0x01f6f693.
Lemma F_1a864 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9bc : word) = Some W_1a864.
Proof. vm_refl. Qed.
Lemma D_1a864 : decode_any W_1a864 = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a868 : bv 32 := 0x00c70463.
Lemma F_1a868 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9c0 : word) = Some W_1a868.
Proof. vm_refl. Qed.
Lemma D_1a868 : decode_any W_1a868 = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a870 : bv 32 := 0x02053603.
Lemma F_1a870 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9c8 : word) = Some W_1a870.
Proof. vm_refl. Qed.
Lemma D_1a870 : decode_any W_1a870 = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a874 : bv 32 := 0x01f67713.
Lemma F_1a874 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9cc : word) = Some W_1a874.
Proof. vm_refl. Qed.
Lemma D_1a874 : decode_any W_1a874 = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a878 : bv 32 := 0x00d77463.
Lemma F_1a878 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9d0 : word) = Some W_1a878.
Proof. vm_refl. Qed.
Lemma D_1a878 : decode_any W_1a878 = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a880 : bv 32 := 0x01852783.
Lemma F_1a880 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9d8 : word) = Some W_1a880.
Proof. vm_refl. Qed.
Lemma D_1a880 : decode_any W_1a880 = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a884 : bv 32 := 0x00100713.
Lemma F_1a884 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9dc : word) = Some W_1a884.
Proof. vm_refl. Qed.
Lemma D_1a884 : decode_any W_1a884 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a888 : bv 32 := 0x00d7173b.
Lemma F_1a888 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9e0 : word) = Some W_1a888.
Proof. vm_refl. Qed.
Lemma D_1a888 : decode_any W_1a888 = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a88c : bv 32 := 0x00e7f7b3.
Lemma F_1a88c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9e4 : word) = Some W_1a88c.
Proof. vm_refl. Qed.
Lemma D_1a88c : decode_any W_1a88c = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a890 : bv 32 := 0x00078463.
Lemma F_1a890 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9e8 : word) = Some W_1a890.
Proof. vm_refl. Qed.
Lemma D_1a890 : decode_any W_1a890 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a898 : bv 32 := 0x01c52783.
Lemma F_1a898 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9f0 : word) = Some W_1a898.
Proof. vm_refl. Qed.
Lemma D_1a898 : decode_any W_1a898 = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a89c : bv 32 := 0x00e7f733.
Lemma F_1a89c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9f4 : word) = Some W_1a89c.
Proof. vm_refl. Qed.
Lemma D_1a89c : decode_any W_1a89c = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8a0 : bv 32 := 0x00070463.
Lemma F_1a8a0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1a9f8 : word) = Some W_1a8a0.
Proof. vm_refl. Qed.
Lemma D_1a8a0 : decode_any W_1a8a0 = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8a8 : bv 32 := 0xfffff737.
Lemma F_1a8a8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa00 : word) = Some W_1a8a8.
Proof. vm_refl. Qed.
Lemma D_1a8a8 : decode_any W_1a8a8 = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8ac : bv 32 := 0x0007a797.
Lemma F_1a8ac : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa04 : word) = Some W_1a8ac.
Proof. vm_refl. Qed.
Lemma D_1a8ac : decode_any W_1a8ac = Some (Auipc 15 122, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8b0 : bv 32 := 0x00e57733.
Lemma F_1a8b0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa08 : word) = Some W_1a8b0.
Proof. vm_refl. Qed.
Lemma D_1a8b0 : decode_any W_1a8b0 = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8b4 : bv 32 := 0x00073703.
Lemma F_1a8b4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa0c : word) = Some W_1a8b4.
Proof. vm_refl. Qed.
Lemma D_1a8b4 : decode_any W_1a8b4 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8b8 : bv 32 := 0xbfc7b783.
Lemma F_1a8b8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa10 : word) = Some W_1a8b8.
Proof. vm_refl. Qed.
Lemma D_1a8b8 : decode_any W_1a8b8 = Some (Load SZ8 true 15 15 3068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8bc : bv 32 := 0x00f70463.
Lemma F_1a8bc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa14 : word) = Some W_1a8bc.
Proof. vm_refl. Qed.
Lemma D_1a8bc : decode_any W_1a8bc = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8c4 : bv 32 := 0x03461713.
Lemma F_1a8c4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa1c : word) = Some W_1a8c4.
Proof. vm_refl. Qed.
Lemma D_1a8c4 : decode_any W_1a8c4 = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8c8 : bv 32 := 0x03a75713.
Lemma F_1a8c8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa20 : word) = Some W_1a8c8.
Proof. vm_refl. Qed.
Lemma D_1a8c8 : decode_any W_1a8c8 = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8cc : bv 32 := 0x02f00793.
Lemma F_1a8cc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa24 : word) = Some W_1a8cc.
Proof. vm_refl. Qed.
Lemma D_1a8cc : decode_any W_1a8cc = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8d0 : bv 32 := 0x02e7ea63.
Lemma F_1a8d0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa28 : word) = Some W_1a8d0.
Proof. vm_refl. Qed.
Lemma D_1a8d0 : decode_any W_1a8d0 = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8d4 : bv 32 := 0x00171713.
Lemma F_1a8d4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa2c : word) = Some W_1a8d4.
Proof. vm_refl. Qed.
Lemma D_1a8d4 : decode_any W_1a8d4 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8d8 : bv 32 := 0xffff8797.
Lemma F_1a8d8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa30 : word) = Some W_1a8d8.
Proof. vm_refl. Qed.
Lemma D_1a8d8 : decode_any W_1a8d8 = Some (Auipc 15 1048568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8dc : bv 32 := 0xa2c78793.
Lemma F_1a8dc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa34 : word) = Some W_1a8dc.
Proof. vm_refl. Qed.
Lemma D_1a8dc : decode_any W_1a8dc = Some (OpImm ALU_ADD 15 15 2604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8e0 : bv 32 := 0x00e78733.
Lemma F_1a8e0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa38 : word) = Some W_1a8e0.
Proof. vm_refl. Qed.
Lemma D_1a8e0 : decode_any W_1a8e0 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8e4 : bv 32 := 0x00075703.
Lemma F_1a8e4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa3c : word) = Some W_1a8e4.
Proof. vm_refl. Qed.
Lemma D_1a8e4 : decode_any W_1a8e4 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8e8 : bv 32 := 0x02d707b3.
Lemma F_1a8e8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa40 : word) = Some W_1a8e8.
Proof. vm_refl. Qed.
Lemma D_1a8e8 : decode_any W_1a8e8 = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8ec : bv 32 := 0x00f5f463.
Lemma F_1a8ec : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa44 : word) = Some W_1a8ec.
Proof. vm_refl. Qed.
Lemma D_1a8ec : decode_any W_1a8ec = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8f4 : bv 32 := 0x00168693.
Lemma F_1a8f4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa4c : word) = Some W_1a8f4.
Proof. vm_refl. Qed.
Lemma D_1a8f4 : decode_any W_1a8f4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8f8 : bv 32 := 0x02e686b3.
Lemma F_1a8f8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa50 : word) = Some W_1a8f8.
Proof. vm_refl. Qed.
Lemma D_1a8f8 : decode_any W_1a8f8 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a8fc : bv 32 := 0x00d5f863.
Lemma F_1a8fc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa54 : word) = Some W_1a8fc.
Proof. vm_refl. Qed.
Lemma D_1a8fc : decode_any W_1a8fc = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a900 : bv 32 := 0x0100006f.
Lemma F_1a900 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa58 : word) = Some W_1a900.
Proof. vm_refl. Qed.
Lemma D_1a900 : decode_any W_1a900 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a904 : bv 32 := 0x03f00693.
Lemma F_1a904 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa5c : word) = Some W_1a904.
Proof. vm_refl. Qed.
Lemma D_1a904 : decode_any W_1a904 = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a908 : bv 32 := 0x00d70463.
Lemma F_1a908 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa60 : word) = Some W_1a908.
Proof. vm_refl. Qed.
Lemma D_1a908 : decode_any W_1a908 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a910 : bv 32 := 0x00c65613.
Lemma F_1a910 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa68 : word) = Some W_1a910.
Proof. vm_refl. Qed.
Lemma D_1a910 : decode_any W_1a910 = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a914 : bv 32 := 0x00060a63.
Lemma F_1a914 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa6c : word) = Some W_1a914.
Proof. vm_refl. Qed.
Lemma D_1a914 : decode_any W_1a914 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a918 : bv 32 := 0x00861613.
Lemma F_1a918 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa70 : word) = Some W_1a918.
Proof. vm_refl. Qed.
Lemma D_1a918 : decode_any W_1a918 = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a91c : bv 32 := 0xfff60613.
Lemma F_1a91c : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa74 : word) = Some W_1a91c.
Proof. vm_refl. Qed.
Lemma D_1a91c : decode_any W_1a91c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a920 : bv 32 := 0x00b67463.
Lemma F_1a920 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa78 : word) = Some W_1a920.
Proof. vm_refl. Qed.
Lemma D_1a920 : decode_any W_1a920 = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a928 : bv 32 := 0x00008067.
Lemma F_1a928 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1aa80 : word) = Some W_1a928.
Proof. vm_refl. Qed.
Lemma D_1a928 : decode_any W_1a928 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1acac : bv 32 := 0x00072503.
Lemma F_1acac : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1ae04 : word) = Some W_1acac.
Proof. vm_refl. Qed.
Lemma D_1acac : decode_any W_1acac = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1acb0 : bv 32 := 0x00b56633.
Lemma F_1acb0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1ae08 : word) = Some W_1acb0.
Proof. vm_refl. Qed.
Lemma D_1acb0 : decode_any W_1acb0 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1acb4 : bv 32 := 0x160726af.
Lemma F_1acb4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1ae0c : word) = Some W_1acb4.
Proof. vm_refl. Qed.
Lemma D_1acb4 : decode_any W_1acb4 = Some (Lr AW true true 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1acb8 : bv 32 := 0x00a69663.
Lemma F_1acb8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1ae10 : word) = Some W_1acb8.
Proof. vm_refl. Qed.
Lemma D_1acb8 : decode_any W_1acb8 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1acbc : bv 32 := 0x1ec727af.
Lemma F_1acbc : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1ae14 : word) = Some W_1acbc.
Proof. vm_refl. Qed.
Lemma D_1acbc : decode_any W_1acbc = Some (Sc AW true true 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1acc0 : bv 32 := 0xfe079ae3.
Lemma F_1acc0 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1ae18 : word) = Some W_1acc0.
Proof. vm_refl. Qed.
Lemma D_1acc0 : decode_any W_1acc0 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1acc4 : bv 32 := 0x0006869b.
Lemma F_1acc4 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1ae1c : word) = Some W_1acc4.
Proof. vm_refl. Qed.
Lemma D_1acc4 : decode_any W_1acc4 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1acc8 : bv 32 := 0xfea692e3.
Lemma F_1acc8 : fetch_word TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments (0x1ae20 : word) = Some W_1acc8.
Proof. vm_refl. Qed.
Lemma D_1acc8 : decode_any W_1acc8 = Some (Branch BC_NE 13 10 8164, 4%Z).
Proof. vm_refl. Qed.
