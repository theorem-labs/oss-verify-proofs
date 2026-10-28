(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_3116c : bv 32 := 0xe0050553.
Lemma F_3116c : fetch_word Ubsan.M.loaded_segments (0x3dbdc : word) = Some W_3116c.
Proof. vm_refl. Qed.
Lemma D_3116c : decode_any W_3116c = Some (Fmv FMV_X_F FMT_S 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31170 : bv 32 := 0x02151513.
Lemma F_31170 : fetch_word Ubsan.M.loaded_segments (0x3dbe0 : word) = Some W_31170.
Proof. vm_refl. Qed.
Lemma D_31170 : decode_any W_31170 = Some (ShiftImm ALU_SLL 10 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31174 : bv 32 := 0x03555513.
Lemma F_31174 : fetch_word Ubsan.M.loaded_segments (0x3dbe4 : word) = Some W_31174.
Proof. vm_refl. Qed.
Lemma D_31174 : decode_any W_31174 = Some (ShiftImm ALU_SRL 10 10 53, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31178 : bv 32 := 0x42b00593.
Lemma F_31178 : fetch_word Ubsan.M.loaded_segments (0x3dbe8 : word) = Some W_31178.
Proof. vm_refl. Qed.
Lemma D_31178 : decode_any W_31178 = Some (OpImm ALU_ADD 11 0 1067, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3117c : bv 32 := 0x06b57c63.
Lemma F_3117c : fetch_word Ubsan.M.loaded_segments (0x3dbec : word) = Some W_3117c.
Proof. vm_refl. Qed.
Lemma D_3117c : decode_any W_3117c = Some (Branch BC_GEU 10 11 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31180 : bv 32 := 0x420507d3.
Lemma F_31180 : fetch_word Ubsan.M.loaded_segments (0x3dbf0 : word) = Some W_31180.
Proof. vm_refl. Qed.
Lemma D_31180 : decode_any W_31180 = Some (Fcvt FC_D FC_S 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31184 : bv 32 := 0xfffd5517.
Lemma F_31184 : fetch_word Ubsan.M.loaded_segments (0x3dbf4 : word) = Some W_31184.
Proof. vm_refl. Qed.
Lemma D_31184 : decode_any W_31184 = Some (Auipc 10 1048533, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31188 : bv 32 := 0x00100593.
Lemma F_31188 : fetch_word Ubsan.M.loaded_segments (0x3dbf8 : word) = Some W_31188.
Proof. vm_refl. Qed.
Lemma D_31188 : decode_any W_31188 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3118c : bv 32 := 0x7ac50513.
Lemma F_3118c : fetch_word Ubsan.M.loaded_segments (0x3dbfc : word) = Some W_3118c.
Proof. vm_refl. Qed.
Lemma D_3118c : decode_any W_3118c = Some (OpImm ALU_ADD 10 10 1964, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31190 : bv 32 := 0x12053707.
Lemma F_31190 : fetch_word Ubsan.M.loaded_segments (0x3dc00 : word) = Some W_31190.
Proof. vm_refl. Qed.
Lemma D_31190 : decode_any W_31190 = Some (FLoad FMT_D 14 10 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31194 : bv 32 := 0x12853687.
Lemma F_31194 : fetch_word Ubsan.M.loaded_segments (0x3dc04 : word) = Some W_31194.
Proof. vm_refl. Qed.
Lemma D_31194 : decode_any W_31194 = Some (FLoad FMT_D 13 10 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31198 : bv 32 := 0xd2058653.
Lemma F_31198 : fetch_word Ubsan.M.loaded_segments (0x3dc08 : word) = Some W_31198.
Proof. vm_refl. Qed.
Lemma D_31198 : decode_any W_31198 = Some (Fcvt FC_D FC_W 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3119c : bv 32 := 0x13053587.
Lemma F_3119c : fetch_word Ubsan.M.loaded_segments (0x3dc0c : word) = Some W_3119c.
Proof. vm_refl. Qed.
Lemma D_3119c : decode_any W_3119c = Some (FLoad FMT_D 11 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311a0 : bv 32 := 0x13853507.
Lemma F_311a0 : fetch_word Ubsan.M.loaded_segments (0x3dc10 : word) = Some W_311a0.
Proof. vm_refl. Qed.
Lemma D_311a0 : decode_any W_311a0 = Some (FLoad FMT_D 10 10 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311a4 : bv 32 := 0x12f6f7d3.
Lemma F_311a4 : fetch_word Ubsan.M.loaded_segments (0x3dc14 : word) = Some W_311a4.
Proof. vm_refl. Qed.
Lemma D_311a4 : decode_any W_311a4 = Some (Fari F_MUL FMT_D 15 13 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311a8 : bv 32 := 0x02e7f6d3.
Lemma F_311a8 : fetch_word Ubsan.M.loaded_segments (0x3dc18 : word) = Some W_311a8.
Proof. vm_refl. Qed.
Lemma D_311a8 : decode_any W_311a8 = Some (Fari F_ADD FMT_D 13 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311ac : bv 32 := 0xe20685d3.
Lemma F_311ac : fetch_word Ubsan.M.loaded_segments (0x3dc1c : word) = Some W_311ac.
Proof. vm_refl. Qed.
Lemma D_311ac : decode_any W_311ac = Some (Fmv FMV_X_F FMT_D 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311b0 : bv 32 := 0x0ae6f753.
Lemma F_311b0 : fetch_word Ubsan.M.loaded_segments (0x3dc20 : word) = Some W_311b0.
Proof. vm_refl. Qed.
Lemma D_311b0 : decode_any W_311b0 = Some (Fari F_SUB FMT_D 14 13 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311b4 : bv 32 := 0x14053687.
Lemma F_311b4 : fetch_word Ubsan.M.loaded_segments (0x3dc24 : word) = Some W_311b4.
Proof. vm_refl. Qed.
Lemma D_311b4 : decode_any W_311b4 = Some (FLoad FMT_D 13 10 320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311b8 : bv 32 := 0x0ae7f7d3.
Lemma F_311b8 : fetch_word Ubsan.M.loaded_segments (0x3dc28 : word) = Some W_311b8.
Proof. vm_refl. Qed.
Lemma D_311b8 : decode_any W_311b8 = Some (Fari F_SUB FMT_D 15 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311bc : bv 32 := 0x01f5f613.
Lemma F_311bc : fetch_word Ubsan.M.loaded_segments (0x3dc2c : word) = Some W_311bc.
Proof. vm_refl. Qed.
Lemma D_311bc : decode_any W_311bc = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311c0 : bv 32 := 0x02f59593.
Lemma F_311c0 : fetch_word Ubsan.M.loaded_segments (0x3dc30 : word) = Some W_311c0.
Proof. vm_refl. Qed.
Lemma D_311c0 : decode_any W_311c0 = Some (ShiftImm ALU_SLL 11 11 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311c4 : bv 32 := 0x00361613.
Lemma F_311c4 : fetch_word Ubsan.M.loaded_segments (0x3dc34 : word) = Some W_311c4.
Proof. vm_refl. Qed.
Lemma D_311c4 : decode_any W_311c4 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311c8 : bv 32 := 0x00c50533.
Lemma F_311c8 : fetch_word Ubsan.M.loaded_segments (0x3dc38 : word) = Some W_311c8.
Proof. vm_refl. Qed.
Lemma D_311c8 : decode_any W_311c8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311cc : bv 32 := 0x00053503.
Lemma F_311cc : fetch_word Ubsan.M.loaded_segments (0x3dc3c : word) = Some W_311cc.
Proof. vm_refl. Qed.
Lemma D_311cc : decode_any W_311cc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311d0 : bv 32 := 0x52f5f743.
Lemma F_311d0 : fetch_word Ubsan.M.loaded_segments (0x3dc40 : word) = Some W_311d0.
Proof. vm_refl. Qed.
Lemma D_311d0 : decode_any W_311d0 = Some (Fma F_MADD FMT_D 14 11 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311d4 : bv 32 := 0x12f7f5d3.
Lemma F_311d4 : fetch_word Ubsan.M.loaded_segments (0x3dc44 : word) = Some W_311d4.
Proof. vm_refl. Qed.
Lemma D_311d4 : decode_any W_311d4 = Some (Fari F_MUL FMT_D 11 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311d8 : bv 32 := 0x62f6f7c3.
Lemma F_311d8 : fetch_word Ubsan.M.loaded_segments (0x3dc48 : word) = Some W_311d8.
Proof. vm_refl. Qed.
Lemma D_311d8 : decode_any W_311d8 = Some (Fma F_MADD FMT_D 15 13 15 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311dc : bv 32 := 0x00b50533.
Lemma F_311dc : fetch_word Ubsan.M.loaded_segments (0x3dc4c : word) = Some W_311dc.
Proof. vm_refl. Qed.
Lemma D_311dc : decode_any W_311dc = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311e0 : bv 32 := 0xf20506d3.
Lemma F_311e0 : fetch_word Ubsan.M.loaded_segments (0x3dc50 : word) = Some W_311e0.
Proof. vm_refl. Qed.
Lemma D_311e0 : decode_any W_311e0 = Some (Fmv FMV_F_X FMT_D 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311e4 : bv 32 := 0x7ab777c3.
Lemma F_311e4 : fetch_word Ubsan.M.loaded_segments (0x3dc54 : word) = Some W_311e4.
Proof. vm_refl. Qed.
Lemma D_311e4 : decode_any W_311e4 = Some (Fma F_MADD FMT_D 15 14 11 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311e8 : bv 32 := 0x12d7f7d3.
Lemma F_311e8 : fetch_word Ubsan.M.loaded_segments (0x3dc58 : word) = Some W_311e8.
Proof. vm_refl. Qed.
Lemma D_311e8 : decode_any W_311e8 = Some (Fari F_MUL FMT_D 15 15 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311ec : bv 32 := 0x4017f553.
Lemma F_311ec : fetch_word Ubsan.M.loaded_segments (0x3dc5c : word) = Some W_311ec.
Proof. vm_refl. Qed.
Lemma D_311ec : decode_any W_311ec = Some (Fcvt FC_S FC_D 10 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311f0 : bv 32 := 0x00008067.
Lemma F_311f0 : fetch_word Ubsan.M.loaded_segments (0x3dc60 : word) = Some W_311f0.
Proof. vm_refl. Qed.
Lemma D_311f0 : decode_any W_311f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311f4 : bv 32 := 0xe00515d3.
Lemma F_311f4 : fetch_word Ubsan.M.loaded_segments (0x3dc64 : word) = Some W_311f4.
Proof. vm_refl. Qed.
Lemma D_311f4 : decode_any W_311f4 = Some (Fclass FMT_S 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311f8 : bv 32 := 0x0015f593.
Lemma F_311f8 : fetch_word Ubsan.M.loaded_segments (0x3dc68 : word) = Some W_311f8.
Proof. vm_refl. Qed.
Lemma D_311f8 : decode_any W_311f8 = Some (OpImm ALU_AND 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_311fc : bv 32 := 0x00058663.
Lemma F_311fc : fetch_word Ubsan.M.loaded_segments (0x3dc6c : word) = Some W_311fc.
Proof. vm_refl. Qed.
Lemma D_311fc : decode_any W_311fc = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31200 : bv 32 := 0xf0000553.
Lemma F_31200 : fetch_word Ubsan.M.loaded_segments (0x3dc70 : word) = Some W_31200.
Proof. vm_refl. Qed.
Lemma D_31200 : decode_any W_31200 = Some (Fmv FMV_F_X FMT_S 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31204 : bv 32 := 0x00008067.
Lemma F_31204 : fetch_word Ubsan.M.loaded_segments (0x3dc74 : word) = Some W_31204.
Proof. vm_refl. Qed.
Lemma D_31204 : decode_any W_31204 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31208 : bv 32 := 0x7f800593.
Lemma F_31208 : fetch_word Ubsan.M.loaded_segments (0x3dc78 : word) = Some W_31208.
Proof. vm_refl. Qed.
Lemma D_31208 : decode_any W_31208 = Some (OpImm ALU_ADD 11 0 2040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3120c : bv 32 := 0x00b57e63.
Lemma F_3120c : fetch_word Ubsan.M.loaded_segments (0x3dc7c : word) = Some W_3120c.
Proof. vm_refl. Qed.
Lemma D_3120c : decode_any W_3120c = Some (Branch BC_GEU 10 11 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31210 : bv 32 := 0xfffd5517.
Lemma F_31210 : fetch_word Ubsan.M.loaded_segments (0x3dc80 : word) = Some W_31210.
Proof. vm_refl. Qed.
Lemma D_31210 : decode_any W_31210 = Some (Auipc 10 1048533, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31214 : bv 32 := 0xb3452787.
Lemma F_31214 : fetch_word Ubsan.M.loaded_segments (0x3dc84 : word) = Some W_31214.
Proof. vm_refl. Qed.
Lemma D_31214 : decode_any W_31214 = Some (FLoad FMT_S 15 10 2868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31218 : bv 32 := 0xa0a79553.
Lemma F_31218 : fetch_word Ubsan.M.loaded_segments (0x3dc88 : word) = Some W_31218.
Proof. vm_refl. Qed.
Lemma D_31218 : decode_any W_31218 = Some (Fcmp F_LT FMT_S 10 15 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3121c : bv 32 := 0x00050a63.
Lemma F_3121c : fetch_word Ubsan.M.loaded_segments (0x3dc8c : word) = Some W_3121c.
Proof. vm_refl. Qed.
Lemma D_3121c : decode_any W_3121c = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31220 : bv 32 := 0x00000513.
Lemma F_31220 : fetch_word Ubsan.M.loaded_segments (0x3dc90 : word) = Some W_31220.
Proof. vm_refl. Qed.
Lemma D_31220 : decode_any W_31220 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31224 : bv 32 := 0x0240006f.
Lemma F_31224 : fetch_word Ubsan.M.loaded_segments (0x3dc94 : word) = Some W_31224.
Proof. vm_refl. Qed.
Lemma D_31224 : decode_any W_31224 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31228 : bv 32 := 0x00a57553.
Lemma F_31228 : fetch_word Ubsan.M.loaded_segments (0x3dc98 : word) = Some W_31228.
Proof. vm_refl. Qed.
Lemma D_31228 : decode_any W_31228 = Some (Fari F_ADD FMT_S 10 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3122c : bv 32 := 0x00008067.
Lemma F_3122c : fetch_word Ubsan.M.loaded_segments (0x3dc9c : word) = Some W_3122c.
Proof. vm_refl. Qed.
Lemma D_3122c : decode_any W_3122c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31230 : bv 32 := 0xfffd5517.
Lemma F_31230 : fetch_word Ubsan.M.loaded_segments (0x3dca0 : word) = Some W_31230.
Proof. vm_refl. Qed.
Lemma D_31230 : decode_any W_31230 = Some (Auipc 10 1048533, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31234 : bv 32 := 0xb1c52787.
Lemma F_31234 : fetch_word Ubsan.M.loaded_segments (0x3dca4 : word) = Some W_31234.
Proof. vm_refl. Qed.
Lemma D_31234 : decode_any W_31234 = Some (FLoad FMT_S 15 10 2844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31238 : bv 32 := 0xa0f51553.
Lemma F_31238 : fetch_word Ubsan.M.loaded_segments (0x3dca8 : word) = Some W_31238.
Proof. vm_refl. Qed.
Lemma D_31238 : decode_any W_31238 = Some (Fcmp F_LT FMT_S 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3123c : bv 32 := 0xf40502e3.
Lemma F_3123c : fetch_word Ubsan.M.loaded_segments (0x3dcac : word) = Some W_3123c.
Proof. vm_refl. Qed.
Lemma D_3123c : decode_any W_3123c = Some (Branch BC_EQ 10 0 8004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31240 : bv 32 := 0x00000513.
Lemma F_31240 : fetch_word Ubsan.M.loaded_segments (0x3dcb0 : word) = Some W_31240.
Proof. vm_refl. Qed.
Lemma D_31240 : decode_any W_31240 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31244 : bv 32 := 0x0340006f.
Lemma F_31244 : fetch_word Ubsan.M.loaded_segments (0x3dcb4 : word) = Some W_31244.
Proof. vm_refl. Qed.
Lemma D_31244 : decode_any W_31244 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31248 : bv 32 := 0x700005b7.
Lemma F_31248 : fetch_word Ubsan.M.loaded_segments (0x3dcb8 : word) = Some W_31248.
Proof. vm_refl. Qed.
Lemma D_31248 : decode_any W_31248 = Some (Lui 11 458752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3124c : bv 32 := 0xf0058553.
Lemma F_3124c : fetch_word Ubsan.M.loaded_segments (0x3dcbc : word) = Some W_3124c.
Proof. vm_refl. Qed.
Lemma D_3124c : decode_any W_3124c = Some (Fmv FMV_F_X FMT_S 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31250 : bv 32 := 0x0040006f.
Lemma F_31250 : fetch_word Ubsan.M.loaded_segments (0x3dcc0 : word) = Some W_31250.
Proof. vm_refl. Qed.
Lemma D_31250 : decode_any W_31250 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31254 : bv 32 := 0x20a507d3.
Lemma F_31254 : fetch_word Ubsan.M.loaded_segments (0x3dcc4 : word) = Some W_31254.
Proof. vm_refl. Qed.
Lemma D_31254 : decode_any W_31254 = Some (Fsgnj F_SGNJ FMT_S 15 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31258 : bv 32 := 0x00050463.
Lemma F_31258 : fetch_word Ubsan.M.loaded_segments (0x3dcc8 : word) = Some W_31258.
Proof. vm_refl. Qed.
Lemma D_31258 : decode_any W_31258 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31260 : bv 32 := 0xff010113.
Lemma F_31260 : fetch_word Ubsan.M.loaded_segments (0x3dcd0 : word) = Some W_31260.
Proof. vm_refl. Qed.
Lemma D_31260 : decode_any W_31260 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31264 : bv 32 := 0x00f12627.
Lemma F_31264 : fetch_word Ubsan.M.loaded_segments (0x3dcd4 : word) = Some W_31264.
Proof. vm_refl. Qed.
Lemma D_31264 : decode_any W_31264 = Some (FStore FMT_S 2 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31268 : bv 32 := 0x00c12787.
Lemma F_31268 : fetch_word Ubsan.M.loaded_segments (0x3dcd8 : word) = Some W_31268.
Proof. vm_refl. Qed.
Lemma D_31268 : decode_any W_31268 = Some (FLoad FMT_S 15 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3126c : bv 32 := 0x10a7f553.
Lemma F_3126c : fetch_word Ubsan.M.loaded_segments (0x3dcdc : word) = Some W_3126c.
Proof. vm_refl. Qed.
Lemma D_3126c : decode_any W_3126c = Some (Fari F_MUL FMT_S 10 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31270 : bv 32 := 0x01010113.
Lemma F_31270 : fetch_word Ubsan.M.loaded_segments (0x3dce0 : word) = Some W_31270.
Proof. vm_refl. Qed.
Lemma D_31270 : decode_any W_31270 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31274 : bv 32 := 0x00008067.
Lemma F_31274 : fetch_word Ubsan.M.loaded_segments (0x3dce4 : word) = Some W_31274.
Proof. vm_refl. Qed.
Lemma D_31274 : decode_any W_31274 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31278 : bv 32 := 0x100005b7.
Lemma F_31278 : fetch_word Ubsan.M.loaded_segments (0x3dce8 : word) = Some W_31278.
Proof. vm_refl. Qed.
Lemma D_31278 : decode_any W_31278 = Some (Lui 11 65536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3127c : bv 32 := 0xf0058553.
Lemma F_3127c : fetch_word Ubsan.M.loaded_segments (0x3dcec : word) = Some W_3127c.
Proof. vm_refl. Qed.
Lemma D_3127c : decode_any W_3127c = Some (Fmv FMV_F_X FMT_S 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31280 : bv 32 := 0xfd5ff06f.
Lemma F_31280 : fetch_word Ubsan.M.loaded_segments (0x3dcf0 : word) = Some W_31280.
Proof. vm_refl. Qed.
Lemma D_31280 : decode_any W_31280 = Some (Jal 0 2097108, 4%Z).
Proof. vm_refl. Qed.
