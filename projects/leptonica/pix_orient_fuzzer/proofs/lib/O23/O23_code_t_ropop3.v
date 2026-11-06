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
Definition W_7a7dc : bv 32 := 0x00000513.
Lemma F_7a7dc : fetch_word Plain.M.loaded_segments (0x7a834 : word) = Some W_7a7dc.
Proof. vm_refl. Qed.
Lemma D_7a7dc : decode_any W_7a7dc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7e0 : bv 32 := 0xfff3c593.
Lemma F_7a7e0 : fetch_word Plain.M.loaded_segments (0x7a838 : word) = Some W_7a7e0.
Proof. vm_refl. Qed.
Lemma D_7a7e0 : decode_any W_7a7e0 = Some (OpImm ALU_XOR 11 7 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7e4 : bv 32 := 0x00271293.
Lemma F_7a7e4 : fetch_word Plain.M.loaded_segments (0x7a83c : word) = Some W_7a7e4.
Proof. vm_refl. Qed.
Lemma D_7a7e4 : decode_any W_7a7e4 = Some (ShiftImm ALU_SLL 5 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7e8 : bv 32 := 0x00269e93.
Lemma F_7a7e8 : fetch_word Plain.M.loaded_segments (0x7a840 : word) = Some W_7a7e8.
Proof. vm_refl. Qed.
Lemma D_7a7e8 : decode_any W_7a7e8 = Some (ShiftImm ALU_SLL 29 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7ec : bv 32 := 0xfffe0e13.
Lemma F_7a7ec : fetch_word Plain.M.loaded_segments (0x7a844 : word) = Some W_7a7ec.
Proof. vm_refl. Qed.
Lemma D_7a7ec : decode_any W_7a7ec = Some (OpImm ALU_ADD 28 28 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7f0 : bv 32 := 0x020e1e13.
Lemma F_7a7f0 : fetch_word Plain.M.loaded_segments (0x7a848 : word) = Some W_7a7f0.
Proof. vm_refl. Qed.
Lemma D_7a7f0 : decode_any W_7a7f0 = Some (ShiftImm ALU_SLL 28 28 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7f4 : bv 32 := 0x01ee5e13.
Lemma F_7a7f4 : fetch_word Plain.M.loaded_segments (0x7a84c : word) = Some W_7a7f4.
Proof. vm_refl. Qed.
Lemma D_7a7f4 : decode_any W_7a7f4 = Some (ShiftImm ALU_SRL 28 28 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7f8 : bv 32 := 0x004e0e13.
Lemma F_7a7f8 : fetch_word Plain.M.loaded_segments (0x7a850 : word) = Some W_7a7f8.
Proof. vm_refl. Qed.
Lemma D_7a7f8 : decode_any W_7a7f8 = Some (OpImm ALU_ADD 28 28 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a7fc : bv 32 := 0x02000f13.
Lemma F_7a7fc : fetch_word Plain.M.loaded_segments (0x7a854 : word) = Some W_7a7fc.
Proof. vm_refl. Qed.
Lemma D_7a7fc : decode_any W_7a7fc = Some (OpImm ALU_ADD 30 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a800 : bv 32 := 0x00080f93.
Lemma F_7a800 : fetch_word Plain.M.loaded_segments (0x7a858 : word) = Some W_7a800.
Proof. vm_refl. Qed.
Lemma D_7a800 : decode_any W_7a800 = Some (OpImm ALU_ADD 31 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a804 : bv 32 := 0x00088413.
Lemma F_7a804 : fetch_word Plain.M.loaded_segments (0x7a85c : word) = Some W_7a804.
Proof. vm_refl. Qed.
Lemma D_7a804 : decode_any W_7a804 = Some (OpImm ALU_ADD 8 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a808 : bv 32 := 0x0500006f.
Lemma F_7a808 : fetch_word Plain.M.loaded_segments (0x7a860 : word) = Some W_7a808.
Proof. vm_refl. Qed.
Lemma D_7a808 : decode_any W_7a808 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a80c : bv 32 := 0x02d504b3.
Lemma F_7a80c : fetch_word Plain.M.loaded_segments (0x7a864 : word) = Some W_7a80c.
Proof. vm_refl. Qed.
Lemma D_7a80c : decode_any W_7a80c = Some (Mul M_MUL 9 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a810 : bv 32 := 0x02e50933.
Lemma F_7a810 : fetch_word Plain.M.loaded_segments (0x7a868 : word) = Some W_7a810.
Proof. vm_refl. Qed.
Lemma D_7a810 : decode_any W_7a810 = Some (Mul M_MUL 18 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a814 : bv 32 := 0x00249493.
Lemma F_7a814 : fetch_word Plain.M.loaded_segments (0x7a86c : word) = Some W_7a814.
Proof. vm_refl. Qed.
Lemma D_7a814 : decode_any W_7a814 = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a818 : bv 32 := 0x00291993.
Lemma F_7a818 : fetch_word Plain.M.loaded_segments (0x7a870 : word) = Some W_7a818.
Proof. vm_refl. Qed.
Lemma D_7a818 : decode_any W_7a818 = Some (ShiftImm ALU_SLL 19 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a81c : bv 32 := 0x00980933.
Lemma F_7a81c : fetch_word Plain.M.loaded_segments (0x7a874 : word) = Some W_7a81c.
Proof. vm_refl. Qed.
Lemma D_7a81c : decode_any W_7a81c = Some (Op ALU_ADD 18 16 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a820 : bv 32 := 0x013884b3.
Lemma F_7a820 : fetch_word Plain.M.loaded_segments (0x7a878 : word) = Some W_7a820.
Proof. vm_refl. Qed.
Lemma D_7a820 : decode_any W_7a820 = Some (Op ALU_ADD 9 17 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a824 : bv 32 := 0x02078063.
Lemma F_7a824 : fetch_word Plain.M.loaded_segments (0x7a87c : word) = Some W_7a824.
Proof. vm_refl. Qed.
Lemma D_7a824 : decode_any W_7a824 = Some (Branch BC_EQ 15 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a828 : bv 32 := 0x0004a983.
Lemma F_7a828 : fetch_word Plain.M.loaded_segments (0x7a880 : word) = Some W_7a828.
Proof. vm_refl. Qed.
Lemma D_7a828 : decode_any W_7a828 = Some (Load SZ4 true 19 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a82c : bv 32 := 0x00092903.
Lemma F_7a82c : fetch_word Plain.M.loaded_segments (0x7a884 : word) = Some W_7a82c.
Proof. vm_refl. Qed.
Lemma D_7a82c : decode_any W_7a82c = Some (Load SZ4 true 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a830 : bv 32 := 0x00b9f9b3.
Lemma F_7a830 : fetch_word Plain.M.loaded_segments (0x7a888 : word) = Some W_7a830.
Proof. vm_refl. Qed.
Lemma D_7a830 : decode_any W_7a830 = Some (Op ALU_AND 19 19 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a834 : bv 32 := 0xfff94913.
Lemma F_7a834 : fetch_word Plain.M.loaded_segments (0x7a88c : word) = Some W_7a834.
Proof. vm_refl. Qed.
Lemma D_7a834 : decode_any W_7a834 = Some (OpImm ALU_XOR 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a838 : bv 32 := 0x0123f933.
Lemma F_7a838 : fetch_word Plain.M.loaded_segments (0x7a890 : word) = Some W_7a838.
Proof. vm_refl. Qed.
Lemma D_7a838 : decode_any W_7a838 = Some (Op ALU_AND 18 7 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a83c : bv 32 := 0x01396933.
Lemma F_7a83c : fetch_word Plain.M.loaded_segments (0x7a894 : word) = Some W_7a83c.
Proof. vm_refl. Qed.
Lemma D_7a83c : decode_any W_7a83c = Some (Op ALU_OR 18 18 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a840 : bv 32 := 0x0124a023.
Lemma F_7a840 : fetch_word Plain.M.loaded_segments (0x7a898 : word) = Some W_7a840.
Proof. vm_refl. Qed.
Lemma D_7a840 : decode_any W_7a840 = Some (Store SZ4 9 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a844 : bv 32 := 0x00150513.
Lemma F_7a844 : fetch_word Plain.M.loaded_segments (0x7a89c : word) = Some W_7a844.
Proof. vm_refl. Qed.
Lemma D_7a844 : decode_any W_7a844 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a848 : bv 32 := 0x00540433.
Lemma F_7a848 : fetch_word Plain.M.loaded_segments (0x7a8a0 : word) = Some W_7a848.
Proof. vm_refl. Qed.
Lemma D_7a848 : decode_any W_7a848 = Some (Op ALU_ADD 8 8 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a84c : bv 32 := 0x01df8fb3.
Lemma F_7a84c : fetch_word Plain.M.loaded_segments (0x7a8a4 : word) = Some W_7a84c.
Proof. vm_refl. Qed.
Lemma D_7a84c : decode_any W_7a84c = Some (Op ALU_ADD 31 31 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a850 : bv 32 := 0x00c51463.
Lemma F_7a850 : fetch_word Plain.M.loaded_segments (0x7a8a8 : word) = Some W_7a850.
Proof. vm_refl. Qed.
Lemma D_7a850 : decode_any W_7a850 = Some (Branch BC_NE 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a854 : bv 32 := 0x69c0106f.
Lemma F_7a854 : fetch_word Plain.M.loaded_segments (0x7a8ac : word) = Some W_7a854.
Proof. vm_refl. Qed.
Lemma D_7a854 : decode_any W_7a854 = Some (Jal 0 5788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a858 : bv 32 := 0xfbe36ae3.
Lemma F_7a858 : fetch_word Plain.M.loaded_segments (0x7a8b0 : word) = Some W_7a858.
Proof. vm_refl. Qed.
Lemma D_7a858 : decode_any W_7a858 = Some (Branch BC_LTU 6 30 8116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a85c : bv 32 := 0x00000913.
Lemma F_7a85c : fetch_word Plain.M.loaded_segments (0x7a8b4 : word) = Some W_7a85c.
Proof. vm_refl. Qed.
Lemma D_7a85c : decode_any W_7a85c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a860 : bv 32 := 0x012f84b3.
Lemma F_7a860 : fetch_word Plain.M.loaded_segments (0x7a8b8 : word) = Some W_7a860.
Proof. vm_refl. Qed.
Lemma D_7a860 : decode_any W_7a860 = Some (Op ALU_ADD 9 31 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a864 : bv 32 := 0x0004a483.
Lemma F_7a864 : fetch_word Plain.M.loaded_segments (0x7a8bc : word) = Some W_7a864.
Proof. vm_refl. Qed.
Lemma D_7a864 : decode_any W_7a864 = Some (Load SZ4 true 9 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a868 : bv 32 := 0x012409b3.
Lemma F_7a868 : fetch_word Plain.M.loaded_segments (0x7a8c0 : word) = Some W_7a868.
Proof. vm_refl. Qed.
Lemma D_7a868 : decode_any W_7a868 = Some (Op ALU_ADD 19 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a86c : bv 32 := 0xfff4c493.
Lemma F_7a86c : fetch_word Plain.M.loaded_segments (0x7a8c4 : word) = Some W_7a86c.
Proof. vm_refl. Qed.
Lemma D_7a86c : decode_any W_7a86c = Some (OpImm ALU_XOR 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a870 : bv 32 := 0x00490913.
Lemma F_7a870 : fetch_word Plain.M.loaded_segments (0x7a8c8 : word) = Some W_7a870.
Proof. vm_refl. Qed.
Lemma D_7a870 : decode_any W_7a870 = Some (OpImm ALU_ADD 18 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a874 : bv 32 := 0x0099a023.
Lemma F_7a874 : fetch_word Plain.M.loaded_segments (0x7a8cc : word) = Some W_7a874.
Proof. vm_refl. Qed.
Lemma D_7a874 : decode_any W_7a874 = Some (Store SZ4 19 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a878 : bv 32 := 0xffc914e3.
Lemma F_7a878 : fetch_word Plain.M.loaded_segments (0x7a8d0 : word) = Some W_7a878.
Proof. vm_refl. Qed.
Lemma D_7a878 : decode_any W_7a878 = Some (Branch BC_NE 18 28 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a87c : bv 32 := 0x012404b3.
Lemma F_7a87c : fetch_word Plain.M.loaded_segments (0x7a8d4 : word) = Some W_7a87c.
Proof. vm_refl. Qed.
Lemma D_7a87c : decode_any W_7a87c = Some (Op ALU_ADD 9 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a880 : bv 32 := 0x012f8933.
Lemma F_7a880 : fetch_word Plain.M.loaded_segments (0x7a8d8 : word) = Some W_7a880.
Proof. vm_refl. Qed.
Lemma D_7a880 : decode_any W_7a880 = Some (Op ALU_ADD 18 31 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a884 : bv 32 := 0xfa0792e3.
Lemma F_7a884 : fetch_word Plain.M.loaded_segments (0x7a8dc : word) = Some W_7a884.
Proof. vm_refl. Qed.
Lemma D_7a884 : decode_any W_7a884 = Some (Branch BC_NE 15 0 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a888 : bv 32 := 0xfbdff06f.
Lemma F_7a888 : fetch_word Plain.M.loaded_segments (0x7a8e0 : word) = Some W_7a888.
Proof. vm_refl. Qed.
Lemma D_7a888 : decode_any W_7a888 = Some (Jal 0 2097084, 4%Z).
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

