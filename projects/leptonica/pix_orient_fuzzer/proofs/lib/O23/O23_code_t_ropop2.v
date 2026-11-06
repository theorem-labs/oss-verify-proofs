(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_7a0a4 : bv 32 := 0x09813683.
Lemma F_7a0a4 : fetch_word Plain.M.loaded_segments (0x7a0fc : word) = Some W_7a0a4.
Proof. vm_refl. Qed.
Lemma D_7a0a4 : decode_any W_7a0a4 = Some (Load SZ8 true 13 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0a8 : bv 32 := 0x07813583.
Lemma F_7a0a8 : fetch_word Plain.M.loaded_segments (0x7a100 : word) = Some W_7a0a8.
Proof. vm_refl. Qed.
Lemma D_7a0a8 : decode_any W_7a0a8 = Some (Load SZ8 true 11 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0ac : bv 32 := 0x08013b03.
Lemma F_7a0ac : fetch_word Plain.M.loaded_segments (0x7a104 : word) = Some W_7a0ac.
Proof. vm_refl. Qed.
Lemma D_7a0ac : decode_any W_7a0ac = Some (Load SZ8 true 22 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b0 : bv 32 := 0x01a9e7b3.
Lemma F_7a0b0 : fetch_word Plain.M.loaded_segments (0x7a108 : word) = Some W_7a0b0.
Proof. vm_refl. Qed.
Lemma D_7a0b0 : decode_any W_7a0b0 = Some (Op ALU_OR 15 19 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b4 : bv 32 := 0x01f7f793.
Lemma F_7a0b4 : fetch_word Plain.M.loaded_segments (0x7a10c : word) = Some W_7a0b4.
Proof. vm_refl. Qed.
Lemma D_7a0b4 : decode_any W_7a0b4 = Some (OpImm ALU_AND 15 15 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0b8 : bv 32 := 0xfff58a93.
Lemma F_7a0b8 : fetch_word Plain.M.loaded_segments (0x7a110 : word) = Some W_7a0b8.
Proof. vm_refl. Qed.
Lemma D_7a0b8 : decode_any W_7a0b8 = Some (OpImm ALU_ADD 21 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a0bc : bv 32 := 0x0a078463.
Lemma F_7a0bc : fetch_word Plain.M.loaded_segments (0x7a114 : word) = Some W_7a0bc.
Proof. vm_refl. Qed.
Lemma D_7a0bc : decode_any W_7a0bc = Some (Branch BC_EQ 15 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a26c : bv 32 := 0xfffa4517.
Lemma F_7a26c : fetch_word Plain.M.loaded_segments (0x7a2c4 : word) = Some W_7a26c.
Proof. vm_refl. Qed.
Lemma D_7a26c : decode_any W_7a26c = Some (Auipc 10 1048484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a270 : bv 32 := 0x00d00813.
Lemma F_7a270 : fetch_word Plain.M.loaded_segments (0x7a2c8 : word) = Some W_7a270.
Proof. vm_refl. Qed.
Lemma D_7a270 : decode_any W_7a270 = Some (OpImm ALU_ADD 16 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a274 : bv 32 := 0x1be50513.
Lemma F_7a274 : fetch_word Plain.M.loaded_segments (0x7a2cc : word) = Some W_7a274.
Proof. vm_refl. Qed.
Lemma D_7a274 : decode_any W_7a274 = Some (OpImm ALU_ADD 10 10 446, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a278 : bv 32 := 0x47586663.
Lemma F_7a278 : fetch_word Plain.M.loaded_segments (0x7a2d0 : word) = Some W_7a278.
Proof. vm_refl. Qed.
Lemma D_7a278 : decode_any W_7a278 = Some (Branch BC_LTU 16 21 1132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a27c : bv 32 := 0x00535e1b.
Lemma F_7a27c : fetch_word Plain.M.loaded_segments (0x7a2d4 : word) = Some W_7a27c.
Proof. vm_refl. Qed.
Lemma D_7a27c : decode_any W_7a27c = Some (ShiftImm32 ALU_SRL 28 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a280 : bv 32 := 0x02db883b.
Lemma F_7a280 : fetch_word Plain.M.loaded_segments (0x7a2d8 : word) = Some W_7a280.
Proof. vm_refl. Qed.
Lemma D_7a280 : decode_any W_7a280 = Some (Mul32 M_MUL 16 23 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a284 : bv 32 := 0x005d589b.
Lemma F_7a284 : fetch_word Plain.M.loaded_segments (0x7a2dc : word) = Some W_7a284.
Proof. vm_refl. Qed.
Lemma D_7a284 : decode_any W_7a284 = Some (ShiftImm32 ALU_SRL 17 26 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a288 : bv 32 := 0x02ed8ebb.
Lemma F_7a288 : fetch_word Plain.M.loaded_segments (0x7a2e0 : word) = Some W_7a288.
Proof. vm_refl. Qed.
Lemma D_7a288 : decode_any W_7a288 = Some (Mul32 M_MUL 29 27 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a28c : bv 32 := 0x002a9a93.
Lemma F_7a28c : fetch_word Plain.M.loaded_segments (0x7a2e4 : word) = Some W_7a28c.
Proof. vm_refl. Qed.
Lemma D_7a28c : decode_any W_7a28c = Some (ShiftImm ALU_SLL 21 21 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a290 : bv 32 := 0x00281813.
Lemma F_7a290 : fetch_word Plain.M.loaded_segments (0x7a2e8 : word) = Some W_7a290.
Proof. vm_refl. Qed.
Lemma D_7a290 : decode_any W_7a290 = Some (ShiftImm ALU_SLL 16 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a294 : bv 32 := 0x010b0833.
Lemma F_7a294 : fetch_word Plain.M.loaded_segments (0x7a2ec : word) = Some W_7a294.
Proof. vm_refl. Qed.
Lemma D_7a294 : decode_any W_7a294 = Some (Op ALU_ADD 16 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a298 : bv 32 := 0xfffa5f17.
Lemma F_7a298 : fetch_word Plain.M.loaded_segments (0x7a2f0 : word) = Some W_7a298.
Proof. vm_refl. Qed.
Lemma D_7a298 : decode_any W_7a298 = Some (Auipc 30 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a29c : bv 32 := 0x00289893.
Lemma F_7a29c : fetch_word Plain.M.loaded_segments (0x7a2f4 : word) = Some W_7a29c.
Proof. vm_refl. Qed.
Lemma D_7a29c : decode_any W_7a29c = Some (ShiftImm ALU_SLL 17 17 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2a0 : bv 32 := 0x002e9e93.
Lemma F_7a2a0 : fetch_word Plain.M.loaded_segments (0x7a2f8 : word) = Some W_7a2a0.
Proof. vm_refl. Qed.
Lemma D_7a2a0 : decode_any W_7a2a0 = Some (ShiftImm ALU_SLL 29 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2a4 : bv 32 := 0x078f0f93.
Lemma F_7a2a4 : fetch_word Plain.M.loaded_segments (0x7a2fc : word) = Some W_7a2a4.
Proof. vm_refl. Qed.
Lemma D_7a2a4 : decode_any W_7a2a4 = Some (OpImm ALU_ADD 31 30 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2a8 : bv 32 := 0x01fa8ab3.
Lemma F_7a2a8 : fetch_word Plain.M.loaded_segments (0x7a300 : word) = Some W_7a2a8.
Proof. vm_refl. Qed.
Lemma D_7a2a8 : decode_any W_7a2a8 = Some (Op ALU_ADD 21 21 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2ac : bv 32 := 0x01180833.
Lemma F_7a2ac : fetch_word Plain.M.loaded_segments (0x7a304 : word) = Some W_7a2ac.
Proof. vm_refl. Qed.
Lemma D_7a2ac : decode_any W_7a2ac = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2b0 : bv 32 := 0x000aa883.
Lemma F_7a2b0 : fetch_word Plain.M.loaded_segments (0x7a308 : word) = Some W_7a2b0.
Proof. vm_refl. Qed.
Lemma D_7a2b0 : decode_any W_7a2b0 = Some (Load SZ4 true 17 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2b4 : bv 32 := 0x01d28433.
Lemma F_7a2b4 : fetch_word Plain.M.loaded_segments (0x7a30c : word) = Some W_7a2b4.
Proof. vm_refl. Qed.
Lemma D_7a2b4 : decode_any W_7a2b4 = Some (Op ALU_ADD 8 5 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2b8 : bv 32 := 0x0059df1b.
Lemma F_7a2b8 : fetch_word Plain.M.loaded_segments (0x7a310 : word) = Some W_7a2b8.
Proof. vm_refl. Qed.
Lemma D_7a2b8 : decode_any W_7a2b8 = Some (ShiftImm32 ALU_SRL 30 19 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2bc : bv 32 := 0x002f1f13.
Lemma F_7a2bc : fetch_word Plain.M.loaded_segments (0x7a314 : word) = Some W_7a2bc.
Proof. vm_refl. Qed.
Lemma D_7a2bc : decode_any W_7a2bc = Some (ShiftImm ALU_SLL 30 30 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2c0 : bv 32 := 0x01f88fb3.
Lemma F_7a2c0 : fetch_word Plain.M.loaded_segments (0x7a318 : word) = Some W_7a2c0.
Proof. vm_refl. Qed.
Lemma D_7a2c0 : decode_any W_7a2c0 = Some (Op ALU_ADD 31 17 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2c4 : bv 32 := 0x01e408b3.
Lemma F_7a2c4 : fetch_word Plain.M.loaded_segments (0x7a31c : word) = Some W_7a2c4.
Proof. vm_refl. Qed.
Lemma D_7a2c4 : decode_any W_7a2c4 = Some (Op ALU_ADD 17 8 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a2c8 : bv 32 := 0x000f8067.
Lemma F_7a2c8 : fetch_word Plain.M.loaded_segments (0x7a320 : word) = Some W_7a2c8.
Proof. vm_refl. Qed.
Lemma D_7a2c8 : decode_any W_7a2c8 = Some (Jalr 0 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a9fc : bv 32 := 0x00000513.
Lemma F_7a9fc : fetch_word Plain.M.loaded_segments (0x7aa54 : word) = Some W_7a9fc.
Proof. vm_refl. Qed.
Lemma D_7a9fc : decode_any W_7a9fc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa00 : bv 32 := 0x00271593.
Lemma F_7aa00 : fetch_word Plain.M.loaded_segments (0x7aa58 : word) = Some W_7aa00.
Proof. vm_refl. Qed.
Lemma D_7aa00 : decode_any W_7aa00 = Some (ShiftImm ALU_SLL 11 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa04 : bv 32 := 0x00269293.
Lemma F_7aa04 : fetch_word Plain.M.loaded_segments (0x7aa5c : word) = Some W_7aa04.
Proof. vm_refl. Qed.
Lemma D_7aa04 : decode_any W_7aa04 = Some (ShiftImm ALU_SLL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa08 : bv 32 := 0xfffe0e13.
Lemma F_7aa08 : fetch_word Plain.M.loaded_segments (0x7aa60 : word) = Some W_7aa08.
Proof. vm_refl. Qed.
Lemma D_7aa08 : decode_any W_7aa08 = Some (OpImm ALU_ADD 28 28 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa0c : bv 32 := 0x020e1e13.
Lemma F_7aa0c : fetch_word Plain.M.loaded_segments (0x7aa64 : word) = Some W_7aa0c.
Proof. vm_refl. Qed.
Lemma D_7aa0c : decode_any W_7aa0c = Some (ShiftImm ALU_SLL 28 28 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa10 : bv 32 := 0x01ee5e13.
Lemma F_7aa10 : fetch_word Plain.M.loaded_segments (0x7aa68 : word) = Some W_7aa10.
Proof. vm_refl. Qed.
Lemma D_7aa10 : decode_any W_7aa10 = Some (ShiftImm ALU_SRL 28 28 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa14 : bv 32 := 0x004e0e13.
Lemma F_7aa14 : fetch_word Plain.M.loaded_segments (0x7aa6c : word) = Some W_7aa14.
Proof. vm_refl. Qed.
Lemma D_7aa14 : decode_any W_7aa14 = Some (OpImm ALU_ADD 28 28 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa18 : bv 32 := 0x02000e93.
Lemma F_7aa18 : fetch_word Plain.M.loaded_segments (0x7aa70 : word) = Some W_7aa18.
Proof. vm_refl. Qed.
Lemma D_7aa18 : decode_any W_7aa18 = Some (OpImm ALU_ADD 29 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa1c : bv 32 := 0x00080f13.
Lemma F_7aa1c : fetch_word Plain.M.loaded_segments (0x7aa74 : word) = Some W_7aa1c.
Proof. vm_refl. Qed.
Lemma D_7aa1c : decode_any W_7aa1c = Some (OpImm ALU_ADD 30 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa20 : bv 32 := 0x00088f93.
Lemma F_7aa20 : fetch_word Plain.M.loaded_segments (0x7aa78 : word) = Some W_7aa20.
Proof. vm_refl. Qed.
Lemma D_7aa20 : decode_any W_7aa20 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa24 : bv 32 := 0x04c0006f.
Lemma F_7aa24 : fetch_word Plain.M.loaded_segments (0x7aa7c : word) = Some W_7aa24.
Proof. vm_refl. Qed.
Lemma D_7aa24 : decode_any W_7aa24 = Some (Jal 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa28 : bv 32 := 0x02d50433.
Lemma F_7aa28 : fetch_word Plain.M.loaded_segments (0x7aa80 : word) = Some W_7aa28.
Proof. vm_refl. Qed.
Lemma D_7aa28 : decode_any W_7aa28 = Some (Mul M_MUL 8 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa2c : bv 32 := 0x02e504b3.
Lemma F_7aa2c : fetch_word Plain.M.loaded_segments (0x7aa84 : word) = Some W_7aa2c.
Proof. vm_refl. Qed.
Lemma D_7aa2c : decode_any W_7aa2c = Some (Mul M_MUL 9 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa30 : bv 32 := 0x00241413.
Lemma F_7aa30 : fetch_word Plain.M.loaded_segments (0x7aa88 : word) = Some W_7aa30.
Proof. vm_refl. Qed.
Lemma D_7aa30 : decode_any W_7aa30 = Some (ShiftImm ALU_SLL 8 8 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa34 : bv 32 := 0x00249913.
Lemma F_7aa34 : fetch_word Plain.M.loaded_segments (0x7aa8c : word) = Some W_7aa34.
Proof. vm_refl. Qed.
Lemma D_7aa34 : decode_any W_7aa34 = Some (ShiftImm ALU_SLL 18 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa38 : bv 32 := 0x008804b3.
Lemma F_7aa38 : fetch_word Plain.M.loaded_segments (0x7aa90 : word) = Some W_7aa38.
Proof. vm_refl. Qed.
Lemma D_7aa38 : decode_any W_7aa38 = Some (Op ALU_ADD 9 16 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa3c : bv 32 := 0x01288433.
Lemma F_7aa3c : fetch_word Plain.M.loaded_segments (0x7aa94 : word) = Some W_7aa3c.
Proof. vm_refl. Qed.
Lemma D_7aa3c : decode_any W_7aa3c = Some (Op ALU_ADD 8 17 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa40 : bv 32 := 0x00078e63.
Lemma F_7aa40 : fetch_word Plain.M.loaded_segments (0x7aa98 : word) = Some W_7aa40.
Proof. vm_refl. Qed.
Lemma D_7aa40 : decode_any W_7aa40 = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa44 : bv 32 := 0x0004a483.
Lemma F_7aa44 : fetch_word Plain.M.loaded_segments (0x7aa9c : word) = Some W_7aa44.
Proof. vm_refl. Qed.
Lemma D_7aa44 : decode_any W_7aa44 = Some (Load SZ4 true 9 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa48 : bv 32 := 0x00042903.
Lemma F_7aa48 : fetch_word Plain.M.loaded_segments (0x7aaa0 : word) = Some W_7aa48.
Proof. vm_refl. Qed.
Lemma D_7aa48 : decode_any W_7aa48 = Some (Load SZ4 true 18 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa4c : bv 32 := 0x0074f4b3.
Lemma F_7aa4c : fetch_word Plain.M.loaded_segments (0x7aaa4 : word) = Some W_7aa4c.
Proof. vm_refl. Qed.
Lemma D_7aa4c : decode_any W_7aa4c = Some (Op ALU_AND 9 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa50 : bv 32 := 0xfff4c493.
Lemma F_7aa50 : fetch_word Plain.M.loaded_segments (0x7aaa8 : word) = Some W_7aa50.
Proof. vm_refl. Qed.
Lemma D_7aa50 : decode_any W_7aa50 = Some (OpImm ALU_XOR 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa54 : bv 32 := 0x009974b3.
Lemma F_7aa54 : fetch_word Plain.M.loaded_segments (0x7aaac : word) = Some W_7aa54.
Proof. vm_refl. Qed.
Lemma D_7aa54 : decode_any W_7aa54 = Some (Op ALU_AND 9 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa58 : bv 32 := 0x00942023.
Lemma F_7aa58 : fetch_word Plain.M.loaded_segments (0x7aab0 : word) = Some W_7aa58.
Proof. vm_refl. Qed.
Lemma D_7aa58 : decode_any W_7aa58 = Some (Store SZ4 8 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa5c : bv 32 := 0x00150513.
Lemma F_7aa5c : fetch_word Plain.M.loaded_segments (0x7aab4 : word) = Some W_7aa5c.
Proof. vm_refl. Qed.
Lemma D_7aa5c : decode_any W_7aa5c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa60 : bv 32 := 0x00bf8fb3.
Lemma F_7aa60 : fetch_word Plain.M.loaded_segments (0x7aab8 : word) = Some W_7aa60.
Proof. vm_refl. Qed.
Lemma D_7aa60 : decode_any W_7aa60 = Some (Op ALU_ADD 31 31 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa64 : bv 32 := 0x005f0f33.
Lemma F_7aa64 : fetch_word Plain.M.loaded_segments (0x7aabc : word) = Some W_7aa64.
Proof. vm_refl. Qed.
Lemma D_7aa64 : decode_any W_7aa64 = Some (Op ALU_ADD 30 30 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa68 : bv 32 := 0x00c51463.
Lemma F_7aa68 : fetch_word Plain.M.loaded_segments (0x7aac0 : word) = Some W_7aa68.
Proof. vm_refl. Qed.
Lemma D_7aa68 : decode_any W_7aa68 = Some (Branch BC_NE 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa6c : bv 32 := 0x4840106f.
Lemma F_7aa6c : fetch_word Plain.M.loaded_segments (0x7aac4 : word) = Some W_7aa6c.
Proof. vm_refl. Qed.
Lemma D_7aa6c : decode_any W_7aa6c = Some (Jal 0 5252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa70 : bv 32 := 0xfbd36ce3.
Lemma F_7aa70 : fetch_word Plain.M.loaded_segments (0x7aac8 : word) = Some W_7aa70.
Proof. vm_refl. Qed.
Lemma D_7aa70 : decode_any W_7aa70 = Some (Branch BC_LTU 6 29 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa74 : bv 32 := 0x00000493.
Lemma F_7aa74 : fetch_word Plain.M.loaded_segments (0x7aacc : word) = Some W_7aa74.
Proof. vm_refl. Qed.
Lemma D_7aa74 : decode_any W_7aa74 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa78 : bv 32 := 0x009f8433.
Lemma F_7aa78 : fetch_word Plain.M.loaded_segments (0x7aad0 : word) = Some W_7aa78.
Proof. vm_refl. Qed.
Lemma D_7aa78 : decode_any W_7aa78 = Some (Op ALU_ADD 8 31 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa7c : bv 32 := 0x009f0933.
Lemma F_7aa7c : fetch_word Plain.M.loaded_segments (0x7aad4 : word) = Some W_7aa7c.
Proof. vm_refl. Qed.
Lemma D_7aa7c : decode_any W_7aa7c = Some (Op ALU_ADD 18 30 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa80 : bv 32 := 0x00092903.
Lemma F_7aa80 : fetch_word Plain.M.loaded_segments (0x7aad8 : word) = Some W_7aa80.
Proof. vm_refl. Qed.
Lemma D_7aa80 : decode_any W_7aa80 = Some (Load SZ4 true 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa84 : bv 32 := 0x00042983.
Lemma F_7aa84 : fetch_word Plain.M.loaded_segments (0x7aadc : word) = Some W_7aa84.
Proof. vm_refl. Qed.
Lemma D_7aa84 : decode_any W_7aa84 = Some (Load SZ4 true 19 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa88 : bv 32 := 0xfff94913.
Lemma F_7aa88 : fetch_word Plain.M.loaded_segments (0x7aae0 : word) = Some W_7aa88.
Proof. vm_refl. Qed.
Lemma D_7aa88 : decode_any W_7aa88 = Some (OpImm ALU_XOR 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa8c : bv 32 := 0x0129f933.
Lemma F_7aa8c : fetch_word Plain.M.loaded_segments (0x7aae4 : word) = Some W_7aa8c.
Proof. vm_refl. Qed.
Lemma D_7aa8c : decode_any W_7aa8c = Some (Op ALU_AND 18 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa90 : bv 32 := 0x00448493.
Lemma F_7aa90 : fetch_word Plain.M.loaded_segments (0x7aae8 : word) = Some W_7aa90.
Proof. vm_refl. Qed.
Lemma D_7aa90 : decode_any W_7aa90 = Some (OpImm ALU_ADD 9 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa94 : bv 32 := 0x01242023.
Lemma F_7aa94 : fetch_word Plain.M.loaded_segments (0x7aaec : word) = Some W_7aa94.
Proof. vm_refl. Qed.
Lemma D_7aa94 : decode_any W_7aa94 = Some (Store SZ4 8 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa98 : bv 32 := 0xffc490e3.
Lemma F_7aa98 : fetch_word Plain.M.loaded_segments (0x7aaf0 : word) = Some W_7aa98.
Proof. vm_refl. Qed.
Lemma D_7aa98 : decode_any W_7aa98 = Some (Branch BC_NE 9 28 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aa9c : bv 32 := 0x009f8433.
Lemma F_7aa9c : fetch_word Plain.M.loaded_segments (0x7aaf4 : word) = Some W_7aa9c.
Proof. vm_refl. Qed.
Lemma D_7aa9c : decode_any W_7aa9c = Some (Op ALU_ADD 8 31 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaa0 : bv 32 := 0x009f04b3.
Lemma F_7aaa0 : fetch_word Plain.M.loaded_segments (0x7aaf8 : word) = Some W_7aaa0.
Proof. vm_refl. Qed.
Lemma D_7aaa0 : decode_any W_7aaa0 = Some (Op ALU_ADD 9 30 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaa4 : bv 32 := 0xfa0790e3.
Lemma F_7aaa4 : fetch_word Plain.M.loaded_segments (0x7aafc : word) = Some W_7aaa4.
Proof. vm_refl. Qed.
Lemma D_7aaa4 : decode_any W_7aaa4 = Some (Branch BC_NE 15 0 8096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7aaa8 : bv 32 := 0xfb5ff06f.
Lemma F_7aaa8 : fetch_word Plain.M.loaded_segments (0x7ab00 : word) = Some W_7aaa8.
Proof. vm_refl. Qed.
Lemma D_7aaa8 : decode_any W_7aaa8 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bef0 : bv 32 := 0x06813083.
Lemma F_7bef0 : fetch_word Plain.M.loaded_segments (0x7bf48 : word) = Some W_7bef0.
Proof. vm_refl. Qed.
Lemma D_7bef0 : decode_any W_7bef0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bef4 : bv 32 := 0x06013403.
Lemma F_7bef4 : fetch_word Plain.M.loaded_segments (0x7bf4c : word) = Some W_7bef4.
Proof. vm_refl. Qed.
Lemma D_7bef4 : decode_any W_7bef4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bef8 : bv 32 := 0x05813483.
Lemma F_7bef8 : fetch_word Plain.M.loaded_segments (0x7bf50 : word) = Some W_7bef8.
Proof. vm_refl. Qed.
Lemma D_7bef8 : decode_any W_7bef8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7befc : bv 32 := 0x05013903.
Lemma F_7befc : fetch_word Plain.M.loaded_segments (0x7bf54 : word) = Some W_7befc.
Proof. vm_refl. Qed.
Lemma D_7befc : decode_any W_7befc = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf00 : bv 32 := 0x04813983.
Lemma F_7bf00 : fetch_word Plain.M.loaded_segments (0x7bf58 : word) = Some W_7bf00.
Proof. vm_refl. Qed.
Lemma D_7bf00 : decode_any W_7bf00 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf04 : bv 32 := 0x04013a03.
Lemma F_7bf04 : fetch_word Plain.M.loaded_segments (0x7bf5c : word) = Some W_7bf04.
Proof. vm_refl. Qed.
Lemma D_7bf04 : decode_any W_7bf04 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf08 : bv 32 := 0x03813a83.
Lemma F_7bf08 : fetch_word Plain.M.loaded_segments (0x7bf60 : word) = Some W_7bf08.
Proof. vm_refl. Qed.
Lemma D_7bf08 : decode_any W_7bf08 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf0c : bv 32 := 0x03013b03.
Lemma F_7bf0c : fetch_word Plain.M.loaded_segments (0x7bf64 : word) = Some W_7bf0c.
Proof. vm_refl. Qed.
Lemma D_7bf0c : decode_any W_7bf0c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf10 : bv 32 := 0x02813b83.
Lemma F_7bf10 : fetch_word Plain.M.loaded_segments (0x7bf68 : word) = Some W_7bf10.
Proof. vm_refl. Qed.
Lemma D_7bf10 : decode_any W_7bf10 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf14 : bv 32 := 0x02013c03.
Lemma F_7bf14 : fetch_word Plain.M.loaded_segments (0x7bf6c : word) = Some W_7bf14.
Proof. vm_refl. Qed.
Lemma D_7bf14 : decode_any W_7bf14 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf18 : bv 32 := 0x01813c83.
Lemma F_7bf18 : fetch_word Plain.M.loaded_segments (0x7bf70 : word) = Some W_7bf18.
Proof. vm_refl. Qed.
Lemma D_7bf18 : decode_any W_7bf18 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf1c : bv 32 := 0x01013d03.
Lemma F_7bf1c : fetch_word Plain.M.loaded_segments (0x7bf74 : word) = Some W_7bf1c.
Proof. vm_refl. Qed.
Lemma D_7bf1c : decode_any W_7bf1c = Some (Load SZ8 true 26 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf20 : bv 32 := 0x00813d83.
Lemma F_7bf20 : fetch_word Plain.M.loaded_segments (0x7bf78 : word) = Some W_7bf20.
Proof. vm_refl. Qed.
Lemma D_7bf20 : decode_any W_7bf20 = Some (Load SZ8 true 27 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf24 : bv 32 := 0x07010113.
Lemma F_7bf24 : fetch_word Plain.M.loaded_segments (0x7bf7c : word) = Some W_7bf24.
Proof. vm_refl. Qed.
Lemma D_7bf24 : decode_any W_7bf24 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf28 : bv 32 := 0x00008067.
Lemma F_7bf28 : fetch_word Plain.M.loaded_segments (0x7bf80 : word) = Some W_7bf28.
Proof. vm_refl. Qed.
Lemma D_7bf28 : decode_any W_7bf28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

