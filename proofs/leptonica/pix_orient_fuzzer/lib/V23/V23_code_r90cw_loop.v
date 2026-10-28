(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushU23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9726c : bv 32 := 0x05412f83.
Lemma F_9726c : fetch_word Ubsan.M.loaded_segments (0x9726c : word) = Some W_9726c.
Proof. vm_refl. Qed.
Lemma D_9726c : decode_any W_9726c = Some (Load SZ4 true 31 2 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_97270 : bv 32 := 0x01f04463.
Lemma F_97270 : fetch_word Ubsan.M.loaded_segments (0x97270 : word) = Some W_97270.
Proof. vm_refl. Qed.
Lemma D_97270 : decode_any W_97270 = Some (Branch BC_LT 0 31 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97274 : bv 32 := 0x7b80106f.
Lemma F_97274 : fetch_word Ubsan.M.loaded_segments (0x97274 : word) = Some W_97274.
Proof. vm_refl. Qed.
Lemma D_97274 : decode_any W_97274 = Some (Jal 0 6072, 4%Z).
Proof. vm_refl. Qed.

Definition W_97278 : bv 32 := 0x00000593.
Lemma F_97278 : fetch_word Ubsan.M.loaded_segments (0x97278 : word) = Some W_97278.
Proof. vm_refl. Qed.
Lemma D_97278 : decode_any W_97278 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9727c : bv 32 := 0x00000613.
Lemma F_9727c : fetch_word Ubsan.M.loaded_segments (0x9727c : word) = Some W_9727c.
Proof. vm_refl. Qed.
Lemma D_9727c : decode_any W_9727c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97280 : bv 32 := 0x05012483.
Lemma F_97280 : fetch_word Ubsan.M.loaded_segments (0x97280 : word) = Some W_97280.
Proof. vm_refl. Qed.
Lemma D_97280 : decode_any W_97280 = Some (Load SZ4 true 9 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_97284 : bv 32 := 0x04000737.
Lemma F_97284 : fetch_word Ubsan.M.loaded_segments (0x97284 : word) = Some W_97284.
Proof. vm_refl. Qed.
Lemma D_97284 : decode_any W_97284 = Some (Lui 14 16384, 4%Z).
Proof. vm_refl. Qed.

Definition W_97288 : bv 32 := 0x00251793.
Lemma F_97288 : fetch_word Ubsan.M.loaded_segments (0x97288 : word) = Some W_97288.
Proof. vm_refl. Qed.
Lemma D_97288 : decode_any W_97288 = Some (ShiftImm ALU_SLL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_9728c : bv 32 := 0x0055139b.
Lemma F_9728c : fetch_word Ubsan.M.loaded_segments (0x9728c : word) = Some W_9728c.
Proof. vm_refl. Qed.
Lemma D_9728c : decode_any W_9728c = Some (ShiftImm32 ALU_SLL 7 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_97290 : bv 32 := 0x00803833.
Lemma F_97290 : fetch_word Ubsan.M.loaded_segments (0x97290 : word) = Some W_97290.
Proof. vm_refl. Qed.
Lemma D_97290 : decode_any W_97290 = Some (Op ALU_SLTU 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97294 : bv 32 := 0x02000893.
Lemma F_97294 : fetch_word Ubsan.M.loaded_segments (0x97294 : word) = Some W_97294.
Proof. vm_refl. Qed.
Lemma D_97294 : decode_any W_97294 = Some (OpImm ALU_ADD 17 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_97298 : bv 32 := 0x00170313.
Lemma F_97298 : fetch_word Ubsan.M.loaded_segments (0x97298 : word) = Some W_97298.
Proof. vm_refl. Qed.
Lemma D_97298 : decode_any W_97298 = Some (OpImm ALU_ADD 6 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9729c : bv 32 := 0x00e50f33.
Lemma F_9729c : fetch_word Ubsan.M.loaded_segments (0x9729c : word) = Some W_9729c.
Proof. vm_refl. Qed.
Lemma D_9729c : decode_any W_9729c = Some (Op ALU_ADD 30 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_972a0 : bv 32 := 0x00239393.
Lemma F_972a0 : fetch_word Ubsan.M.loaded_segments (0x972a0 : word) = Some W_972a0.
Proof. vm_refl. Qed.
Lemma D_972a0 : decode_any W_972a0 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_972a4 : bv 32 := 0x00149e13.
Lemma F_972a4 : fetch_word Ubsan.M.loaded_segments (0x972a4 : word) = Some W_972a4.
Proof. vm_refl. Qed.
Lemma D_972a4 : decode_any W_972a4 = Some (ShiftImm ALU_SLL 28 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_972a8 : bv 32 := 0x03be5e13.
Lemma F_972a8 : fetch_word Ubsan.M.loaded_segments (0x972a8 : word) = Some W_972a8.
Proof. vm_refl. Qed.
Lemma D_972a8 : decode_any W_972a8 = Some (ShiftImm ALU_SRL 28 28 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_972ac : bv 32 := 0x01c48e33.
Lemma F_972ac : fetch_word Ubsan.M.loaded_segments (0x972ac : word) = Some W_972ac.
Proof. vm_refl. Qed.
Lemma D_972ac : decode_any W_972ac = Some (Op ALU_ADD 28 9 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_972b0 : bv 32 := 0x405e5e1b.
Lemma F_972b0 : fetch_word Ubsan.M.loaded_segments (0x972b0 : word) = Some W_972b0.
Proof. vm_refl. Qed.
Lemma D_972b0 : decode_any W_972b0 = Some (ShiftImm32 ALU_SRA 28 28 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_972b4 : bv 32 := 0x005e1e93.
Lemma F_972b4 : fetch_word Ubsan.M.loaded_segments (0x972b4 : word) = Some W_972b4.
Proof. vm_refl. Qed.
Lemma D_972b4 : decode_any W_972b4 = Some (ShiftImm ALU_SLL 29 28 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_972b8 : bv 32 := 0x01bf5f1b.
Lemma F_972b8 : fetch_word Ubsan.M.loaded_segments (0x972b8 : word) = Some W_972b8.
Proof. vm_refl. Qed.
Lemma D_972b8 : decode_any W_972b8 = Some (ShiftImm32 ALU_SRL 30 30 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_972bc : bv 32 := 0x02913823.
Lemma F_972bc : fetch_word Ubsan.M.loaded_segments (0x972bc : word) = Some W_972bc.
Proof. vm_refl. Qed.
Lemma D_972bc : decode_any W_972bc = Some (Store SZ8 2 9 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_972c0 : bv 32 := 0x07c0006f.
Lemma F_972c0 : fetch_word Ubsan.M.loaded_segments (0x972c0 : word) = Some W_972c0.
Proof. vm_refl. Qed.
Lemma D_972c0 : decode_any W_972c0 = Some (Jal 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_972c4 : bv 32 := 0x0008f517.
Lemma F_972c4 : fetch_word Ubsan.M.loaded_segments (0x972c4 : word) = Some W_972c4.
Proof. vm_refl. Qed.
Lemma D_972c4 : decode_any W_972c4 = Some (Auipc 10 143, 4%Z).
Proof. vm_refl. Qed.

Definition W_972c8 : bv 32 := 0x7ac53503.
Lemma F_972c8 : fetch_word Ubsan.M.loaded_segments (0x972c8 : word) = Some W_972c8.
Proof. vm_refl. Qed.
Lemma D_972c8 : decode_any W_972c8 = Some (Load SZ8 true 10 10 1964, 4%Z).
Proof. vm_refl. Qed.

Definition W_972cc : bv 32 := 0x00052503.
Lemma F_972cc : fetch_word Ubsan.M.loaded_segments (0x972cc : word) = Some W_972cc.
Proof. vm_refl. Qed.
Lemma D_972cc : decode_any W_972cc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_972d0 : bv 32 := 0x00500593.
Lemma F_972d0 : fetch_word Ubsan.M.loaded_segments (0x972d0 : word) = Some W_972d0.
Proof. vm_refl. Qed.
Lemma D_972d0 : decode_any W_972d0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_972d4 : bv 32 := 0x78a5c063.
Lemma F_972d4 : fetch_word Ubsan.M.loaded_segments (0x972d4 : word) = Some W_972d4.
Proof. vm_refl. Qed.
Lemma D_972d4 : decode_any W_972d4 = Some (Branch BC_LT 11 10 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_972d8 : bv 32 := 0xfff79517.
Lemma F_972d8 : fetch_word Ubsan.M.loaded_segments (0x972d8 : word) = Some W_972d8.
Proof. vm_refl. Qed.
Lemma D_972d8 : decode_any W_972d8 = Some (Auipc 10 1048441, 4%Z).
Proof. vm_refl. Qed.

Definition W_972dc : bv 32 := 0xfff82597.
Lemma F_972dc : fetch_word Ubsan.M.loaded_segments (0x972dc : word) = Some W_972dc.
Proof. vm_refl. Qed.
Lemma D_972dc : decode_any W_972dc = Some (Auipc 11 1048450, 4%Z).
Proof. vm_refl. Qed.

Definition W_972e0 : bv 32 := 0x07d50513.
Lemma F_972e0 : fetch_word Ubsan.M.loaded_segments (0x972e0 : word) = Some W_972e0.
Proof. vm_refl. Qed.
Lemma D_972e0 : decode_any W_972e0 = Some (OpImm ALU_ADD 10 10 125, 4%Z).
Proof. vm_refl. Qed.

Definition W_972e4 : bv 32 := 0x11758593.
Lemma F_972e4 : fetch_word Ubsan.M.loaded_segments (0x972e4 : word) = Some W_972e4.
Proof. vm_refl. Qed.
Lemma D_972e4 : decode_any W_972e4 = Some (OpImm ALU_ADD 11 11 279, 4%Z).
Proof. vm_refl. Qed.

Definition W_972e8 : bv 32 := 0x00000613.
Lemma F_972e8 : fetch_word Ubsan.M.loaded_segments (0x972e8 : word) = Some W_972e8.
Proof. vm_refl. Qed.
Lemma D_972e8 : decode_any W_972e8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_972ec : bv 32 := 0x0b813083.
Lemma F_972ec : fetch_word Ubsan.M.loaded_segments (0x972ec : word) = Some W_972ec.
Proof. vm_refl. Qed.
Lemma D_972ec : decode_any W_972ec = Some (Load SZ8 true 1 2 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_972f0 : bv 32 := 0x0b013403.
Lemma F_972f0 : fetch_word Ubsan.M.loaded_segments (0x972f0 : word) = Some W_972f0.
Proof. vm_refl. Qed.
Lemma D_972f0 : decode_any W_972f0 = Some (Load SZ8 true 8 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_972f4 : bv 32 := 0x0a813483.
Lemma F_972f4 : fetch_word Ubsan.M.loaded_segments (0x972f4 : word) = Some W_972f4.
Proof. vm_refl. Qed.
Lemma D_972f4 : decode_any W_972f4 = Some (Load SZ8 true 9 2 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_972f8 : bv 32 := 0x0a013903.
Lemma F_972f8 : fetch_word Ubsan.M.loaded_segments (0x972f8 : word) = Some W_972f8.
Proof. vm_refl. Qed.
Lemma D_972f8 : decode_any W_972f8 = Some (Load SZ8 true 18 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_972fc : bv 32 := 0x09813983.
Lemma F_972fc : fetch_word Ubsan.M.loaded_segments (0x972fc : word) = Some W_972fc.
Proof. vm_refl. Qed.
Lemma D_972fc : decode_any W_972fc = Some (Load SZ8 true 19 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_97300 : bv 32 := 0x09013a03.
Lemma F_97300 : fetch_word Ubsan.M.loaded_segments (0x97300 : word) = Some W_97300.
Proof. vm_refl. Qed.
Lemma D_97300 : decode_any W_97300 = Some (Load SZ8 true 20 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_97304 : bv 32 := 0x08813a83.
Lemma F_97304 : fetch_word Ubsan.M.loaded_segments (0x97304 : word) = Some W_97304.
Proof. vm_refl. Qed.
Lemma D_97304 : decode_any W_97304 = Some (Load SZ8 true 21 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_97308 : bv 32 := 0x08013b03.
Lemma F_97308 : fetch_word Ubsan.M.loaded_segments (0x97308 : word) = Some W_97308.
Proof. vm_refl. Qed.
Lemma D_97308 : decode_any W_97308 = Some (Load SZ8 true 22 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_9730c : bv 32 := 0x07813b83.
Lemma F_9730c : fetch_word Ubsan.M.loaded_segments (0x9730c : word) = Some W_9730c.
Proof. vm_refl. Qed.
Lemma D_9730c : decode_any W_9730c = Some (Load SZ8 true 23 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_97310 : bv 32 := 0x07013c03.
Lemma F_97310 : fetch_word Ubsan.M.loaded_segments (0x97310 : word) = Some W_97310.
Proof. vm_refl. Qed.
Lemma D_97310 : decode_any W_97310 = Some (Load SZ8 true 24 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_97314 : bv 32 := 0x06813c83.
Lemma F_97314 : fetch_word Ubsan.M.loaded_segments (0x97314 : word) = Some W_97314.
Proof. vm_refl. Qed.
Lemma D_97314 : decode_any W_97314 = Some (Load SZ8 true 25 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_97318 : bv 32 := 0x06013d03.
Lemma F_97318 : fetch_word Ubsan.M.loaded_segments (0x97318 : word) = Some W_97318.
Proof. vm_refl. Qed.
Lemma D_97318 : decode_any W_97318 = Some (Load SZ8 true 26 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9731c : bv 32 := 0x05813d83.
Lemma F_9731c : fetch_word Ubsan.M.loaded_segments (0x9731c : word) = Some W_9731c.
Proof. vm_refl. Qed.
Lemma D_9731c : decode_any W_9731c = Some (Load SZ8 true 27 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_97320 : bv 32 := 0x0c010113.
Lemma F_97320 : fetch_word Ubsan.M.loaded_segments (0x97320 : word) = Some W_97320.
Proof. vm_refl. Qed.
Lemma D_97320 : decode_any W_97320 = Some (OpImm ALU_ADD 2 2 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_97324 : bv 32 := 0xc1ccc06f.
Lemma F_97324 : fetch_word Ubsan.M.loaded_segments (0x97324 : word) = Some W_97324.
Proof. vm_refl. Qed.
Lemma D_97324 : decode_any W_97324 = Some (Jal 0 1885212, 4%Z).
Proof. vm_refl. Qed.

Definition W_97328 : bv 32 := 0x05412f83.
Lemma F_97328 : fetch_word Ubsan.M.loaded_segments (0x97328 : word) = Some W_97328.
Proof. vm_refl. Qed.
Lemma D_97328 : decode_any W_97328 = Some (Load SZ4 true 31 2 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_9732c : bv 32 := 0x0016061b.
Lemma F_9732c : fetch_word Ubsan.M.loaded_segments (0x9732c : word) = Some W_9732c.
Proof. vm_refl. Qed.
Lemma D_9732c : decode_any W_9732c = Some (OpImm32 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_97330 : bv 32 := 0x00158593.
Lemma F_97330 : fetch_word Ubsan.M.loaded_segments (0x97330 : word) = Some W_97330.
Proof. vm_refl. Qed.
Lemma D_97330 : decode_any W_97330 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_97334 : bv 32 := 0x01f64463.
Lemma F_97334 : fetch_word Ubsan.M.loaded_segments (0x97334 : word) = Some W_97334.
Proof. vm_refl. Qed.
Lemma D_97334 : decode_any W_97334 = Some (Branch BC_LT 12 31 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97338 : bv 32 := 0x6f40106f.
Lemma F_97338 : fetch_word Ubsan.M.loaded_segments (0x97338 : word) = Some W_97338.
Proof. vm_refl. Qed.
Lemma D_97338 : decode_any W_97338 = Some (Jal 0 5876, 4%Z).
Proof. vm_refl. Qed.

Definition W_9733c : bv 32 := 0xffff899b.
Lemma F_9733c : fetch_word Ubsan.M.loaded_segments (0x9733c : word) = Some W_9733c.
Proof. vm_refl. Qed.
Lemma D_9733c : decode_any W_9733c = Some (OpImm32 19 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_97340 : bv 32 := 0x40c98fb3.
Lemma F_97340 : fetch_word Ubsan.M.loaded_segments (0x97340 : word) = Some W_97340.
Proof. vm_refl. Qed.
Lemma D_97340 : decode_any W_97340 = Some (Op ALU_SUB 31 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_97344 : bv 32 := 0x40c989bb.
Lemma F_97344 : fetch_word Ubsan.M.loaded_segments (0x97344 : word) = Some W_97344.
Proof. vm_refl. Qed.
Lemma D_97344 : decode_any W_97344 = Some (Op32 ALU_SUB 19 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_97348 : bv 32 := 0x01f98463.
Lemma F_97348 : fetch_word Ubsan.M.loaded_segments (0x97348 : word) = Some W_97348.
Proof. vm_refl. Qed.
Lemma D_97348 : decode_any W_97348 = Some (Branch BC_EQ 19 31 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9734c : bv 32 := 0x7200106f.
Lemma F_9734c : fetch_word Ubsan.M.loaded_segments (0x9734c : word) = Some W_9734c.
Proof. vm_refl. Qed.
Lemma D_9734c : decode_any W_9734c = Some (Jal 0 5920, 4%Z).
Proof. vm_refl. Qed.

Definition W_97350 : bv 32 := 0x000f8f9b.
Lemma F_97350 : fetch_word Ubsan.M.loaded_segments (0x97350 : word) = Some W_97350.
Proof. vm_refl. Qed.
Lemma D_97350 : decode_any W_97350 = Some (OpImm32 31 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97354 : bv 32 := 0x032f89b3.
Lemma F_97354 : fetch_word Ubsan.M.loaded_segments (0x97354 : word) = Some W_97354.
Proof. vm_refl. Qed.
Lemma D_97354 : decode_any W_97354 = Some (Mul M_MUL 19 31 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_97358 : bv 32 := 0x032f8fbb.
Lemma F_97358 : fetch_word Ubsan.M.loaded_segments (0x97358 : word) = Some W_97358.
Proof. vm_refl. Qed.
Lemma D_97358 : decode_any W_97358 = Some (Mul32 M_MUL 31 31 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_9735c : bv 32 := 0x013f8463.
Lemma F_9735c : fetch_word Ubsan.M.loaded_segments (0x9735c : word) = Some W_9735c.
Proof. vm_refl. Qed.
Lemma D_9735c : decode_any W_9735c = Some (Branch BC_EQ 31 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97360 : bv 32 := 0x70c0106f.
Lemma F_97360 : fetch_word Ubsan.M.loaded_segments (0x97360 : word) = Some W_97360.
Proof. vm_refl. Qed.
Lemma D_97360 : decode_any W_97360 = Some (Jal 0 5900, 4%Z).
Proof. vm_refl. Qed.

Definition W_97364 : bv 32 := 0x0009899b.
Lemma F_97364 : fetch_word Ubsan.M.loaded_segments (0x97364 : word) = Some W_97364.
Proof. vm_refl. Qed.
Lemma D_97364 : decode_any W_97364 = Some (OpImm32 19 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97368 : bv 32 := 0x00299f93.
Lemma F_97368 : fetch_word Ubsan.M.loaded_segments (0x97368 : word) = Some W_97368.
Proof. vm_refl. Qed.
Lemma D_97368 : decode_any W_97368 = Some (ShiftImm ALU_SLL 31 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_9736c : bv 32 := 0x01f40fb3.
Lemma F_9736c : fetch_word Ubsan.M.loaded_segments (0x9736c : word) = Some W_9736c.
Proof. vm_refl. Qed.
Lemma D_9736c : decode_any W_9736c = Some (Op ALU_ADD 31 8 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_97370 : bv 32 := 0x001fba13.
Lemma F_97370 : fetch_word Ubsan.M.loaded_segments (0x97370 : word) = Some W_97370.
Proof. vm_refl. Qed.
Lemma D_97370 : decode_any W_97370 = Some (OpImm ALU_SLTU 20 31 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_97374 : bv 32 := 0x01481463.
Lemma F_97374 : fetch_word Ubsan.M.loaded_segments (0x97374 : word) = Some W_97374.
Proof. vm_refl. Qed.
Lemma D_97374 : decode_any W_97374 = Some (Branch BC_NE 16 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97378 : bv 32 := 0x6f40106f.
Lemma F_97378 : fetch_word Ubsan.M.loaded_segments (0x97378 : word) = Some W_97378.
Proof. vm_refl. Qed.
Lemma D_97378 : decode_any W_97378 = Some (Jal 0 5876, 4%Z).
Proof. vm_refl. Qed.

Definition W_9737c : bv 32 := 0x008fba33.
Lemma F_9737c : fetch_word Ubsan.M.loaded_segments (0x9737c : word) = Some W_9737c.
Proof. vm_refl. Qed.
Lemma D_9737c : decode_any W_9737c = Some (Op ALU_SLTU 20 31 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97380 : bv 32 := 0x0009a993.
Lemma F_97380 : fetch_word Ubsan.M.loaded_segments (0x97380 : word) = Some W_97380.
Proof. vm_refl. Qed.
Lemma D_97380 : decode_any W_97380 = Some (OpImm ALU_SLT 19 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97384 : bv 32 := 0x013a49b3.
Lemma F_97384 : fetch_word Ubsan.M.loaded_segments (0x97384 : word) = Some W_97384.
Proof. vm_refl. Qed.
Lemma D_97384 : decode_any W_97384 = Some (Op ALU_XOR 19 20 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_97388 : bv 32 := 0x0019c993.
Lemma F_97388 : fetch_word Ubsan.M.loaded_segments (0x97388 : word) = Some W_97388.
Proof. vm_refl. Qed.
Lemma D_97388 : decode_any W_97388 = Some (OpImm ALU_XOR 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9738c : bv 32 := 0x00099463.
Lemma F_9738c : fetch_word Ubsan.M.loaded_segments (0x9738c : word) = Some W_9738c.
Proof. vm_refl. Qed.
Lemma D_9738c : decode_any W_9738c = Some (Branch BC_NE 19 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97390 : bv 32 := 0x6dc0106f.
Lemma F_97390 : fetch_word Ubsan.M.loaded_segments (0x97390 : word) = Some W_97390.
Proof. vm_refl. Qed.
Lemma D_97390 : decode_any W_97390 = Some (Jal 0 5852, 4%Z).
Proof. vm_refl. Qed.

Definition W_97394 : bv 32 := 0x0035d993.
Lemma F_97394 : fetch_word Ubsan.M.loaded_segments (0x97394 : word) = Some W_97394.
Proof. vm_refl. Qed.
Lemma D_97394 : decode_any W_97394 = Some (ShiftImm ALU_SRL 19 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_97398 : bv 32 := 0xffc9f993.
Lemma F_97398 : fetch_word Ubsan.M.loaded_segments (0x97398 : word) = Some W_97398.
Proof. vm_refl. Qed.
Lemma D_97398 : decode_any W_97398 = Some (OpImm ALU_AND 19 19 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_9739c : bv 32 := 0x00052a13.
Lemma F_9739c : fetch_word Ubsan.M.loaded_segments (0x9739c : word) = Some W_9739c.
Proof. vm_refl. Qed.
Lemma D_9739c : decode_any W_9739c = Some (OpImm ALU_SLT 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_973a0 : bv 32 := 0x03813a83.
Lemma F_973a0 : fetch_word Ubsan.M.loaded_segments (0x973a0 : word) = Some W_973a0.
Proof. vm_refl. Qed.
Lemma D_973a0 : decode_any W_973a0 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_973a4 : bv 32 := 0x03013683.
Lemma F_973a4 : fetch_word Ubsan.M.loaded_segments (0x973a4 : word) = Some W_973a4.
Proof. vm_refl. Qed.
Lemma D_973a4 : decode_any W_973a4 = Some (Load SZ8 true 13 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_973a8 : bv 32 := 0x1316ce63.
Lemma F_973a8 : fetch_word Ubsan.M.loaded_segments (0x973a8 : word) = Some W_973a8.
Proof. vm_refl. Qed.
Lemma D_973a8 : decode_any W_973a8 = Some (Branch BC_LT 13 17 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_973ac : bv 32 := 0x00000b13.
Lemma F_973ac : fetch_word Ubsan.M.loaded_segments (0x973ac : word) = Some W_973ac.
Proof. vm_refl. Qed.
Lemma D_973ac : decode_any W_973ac = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_973b0 : bv 32 := 0x800006b7.
Lemma F_973b0 : fetch_word Ubsan.M.loaded_segments (0x973b0 : word) = Some W_973b0.
Proof. vm_refl. Qed.
Lemma D_973b0 : decode_any W_973b0 = Some (Lui 13 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_973b4 : bv 32 := 0x00c6dbbb.
Lemma F_973b4 : fetch_word Ubsan.M.loaded_segments (0x973b4 : word) = Some W_973b4.
Proof. vm_refl. Qed.
Lemma D_973b4 : decode_any W_973b4 = Some (Op32 ALU_SRL 23 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_973b8 : bv 32 := 0x03813a83.
Lemma F_973b8 : fetch_word Ubsan.M.loaded_segments (0x973b8 : word) = Some W_973b8.
Proof. vm_refl. Qed.
Lemma D_973b8 : decode_any W_973b8 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_973bc : bv 32 := 0x00c0006f.
Lemma F_973bc : fetch_word Ubsan.M.loaded_segments (0x973bc : word) = Some W_973bc.
Proof. vm_refl. Qed.
Lemma D_973bc : decode_any W_973bc = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_973c0 : bv 32 := 0x001b0b1b.
Lemma F_973c0 : fetch_word Ubsan.M.loaded_segments (0x973c0 : word) = Some W_973c0.
Proof. vm_refl. Qed.
Lemma D_973c0 : decode_any W_973c0 = Some (OpImm32 22 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_973c4 : bv 32 := 0x11cb0e63.
Lemma F_973c4 : fetch_word Ubsan.M.loaded_segments (0x973c4 : word) = Some W_973c4.
Proof. vm_refl. Qed.
Lemma D_973c4 : decode_any W_973c4 = Some (Branch BC_EQ 22 28 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_973c8 : bv 32 := 0x002b1493.
Lemma F_973c8 : fetch_word Ubsan.M.loaded_segments (0x973c8 : word) = Some W_973c8.
Proof. vm_refl. Qed.
Lemma D_973c8 : decode_any W_973c8 = Some (ShiftImm ALU_SLL 9 22 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_973cc : bv 32 := 0x009f84b3.
Lemma F_973cc : fetch_word Ubsan.M.loaded_segments (0x973cc : word) = Some W_973cc.
Proof. vm_refl. Qed.
Lemma D_973cc : decode_any W_973cc = Some (Op ALU_ADD 9 31 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_973d0 : bv 32 := 0x0014bc13.
Lemma F_973d0 : fetch_word Ubsan.M.loaded_segments (0x973d0 : word) = Some W_973d0.
Proof. vm_refl. Qed.
Lemma D_973d0 : decode_any W_973d0 = Some (OpImm ALU_SLTU 24 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_973d4 : bv 32 := 0x01881463.
Lemma F_973d4 : fetch_word Ubsan.M.loaded_segments (0x973d4 : word) = Some W_973d4.
Proof. vm_refl. Qed.
Lemma D_973d4 : decode_any W_973d4 = Some (Branch BC_NE 16 24 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_973d8 : bv 32 := 0x6940106f.
Lemma F_973d8 : fetch_word Ubsan.M.loaded_segments (0x973d8 : word) = Some W_973d8.
Proof. vm_refl. Qed.
Lemma D_973d8 : decode_any W_973d8 = Some (Jal 0 5780, 4%Z).
Proof. vm_refl. Qed.

Definition W_973dc : bv 32 := 0x01f4f463.
Lemma F_973dc : fetch_word Ubsan.M.loaded_segments (0x973dc : word) = Some W_973dc.
Proof. vm_refl. Qed.
Lemma D_973dc : decode_any W_973dc = Some (Branch BC_GEU 9 31 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_973e0 : bv 32 := 0x68c0106f.
Lemma F_973e0 : fetch_word Ubsan.M.loaded_segments (0x973e0 : word) = Some W_973e0.
Proof. vm_refl. Qed.
Lemma D_973e0 : decode_any W_973e0 = Some (Jal 0 5772, 4%Z).
Proof. vm_refl. Qed.

Definition W_973e4 : bv 32 := 0x00041463.
Lemma F_973e4 : fetch_word Ubsan.M.loaded_segments (0x973e4 : word) = Some W_973e4.
Proof. vm_refl. Qed.
Lemma D_973e4 : decode_any W_973e4 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_973e8 : bv 32 := 0x6840106f.
Lemma F_973e8 : fetch_word Ubsan.M.loaded_segments (0x973e8 : word) = Some W_973e8.
Proof. vm_refl. Qed.
Lemma D_973e8 : decode_any W_973e8 = Some (Jal 0 5764, 4%Z).
Proof. vm_refl. Qed.

Definition W_973ec : bv 32 := 0x0034fc13.
Lemma F_973ec : fetch_word Ubsan.M.loaded_segments (0x973ec : word) = Some W_973ec.
Proof. vm_refl. Qed.
Lemma D_973ec : decode_any W_973ec = Some (OpImm ALU_AND 24 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_973f0 : bv 32 := 0x000c0463.
Lemma F_973f0 : fetch_word Ubsan.M.loaded_segments (0x973f0 : word) = Some W_973f0.
Proof. vm_refl. Qed.
Lemma D_973f0 : decode_any W_973f0 = Some (Branch BC_EQ 24 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_973f4 : bv 32 := 0x6780106f.
Lemma F_973f4 : fetch_word Ubsan.M.loaded_segments (0x973f4 : word) = Some W_973f4.
Proof. vm_refl. Qed.
Lemma D_973f4 : decode_any W_973f4 = Some (Jal 0 5752, 4%Z).
Proof. vm_refl. Qed.

Definition W_973f8 : bv 32 := 0x0004a483.
Lemma F_973f8 : fetch_word Ubsan.M.loaded_segments (0x973f8 : word) = Some W_973f8.
Proof. vm_refl. Qed.
Lemma D_973f8 : decode_any W_973f8 = Some (Load SZ4 true 9 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_973fc : bv 32 := 0x0a048663.
Lemma F_973fc : fetch_word Ubsan.M.loaded_segments (0x973fc : word) = Some W_973fc.
Proof. vm_refl. Qed.
Lemma D_973fc : decode_any W_973fc = Some (Branch BC_EQ 9 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_97400 : bv 32 := 0x006b0c33.
Lemma F_97400 : fetch_word Ubsan.M.loaded_segments (0x97400 : word) = Some W_97400.
Proof. vm_refl. Qed.
Lemma D_97400 : decode_any W_97400 = Some (Op ALU_ADD 24 22 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_97404 : bv 32 := 0x00eb0cb3.
Lemma F_97404 : fetch_word Ubsan.M.loaded_segments (0x97404 : word) = Some W_97404.
Proof. vm_refl. Qed.
Lemma D_97404 : decode_any W_97404 = Some (Op ALU_ADD 25 22 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_97408 : bv 32 := 0x019c6c33.
Lemma F_97408 : fetch_word Ubsan.M.loaded_segments (0x97408 : word) = Some W_97408.
Proof. vm_refl. Qed.
Lemma D_97408 : decode_any W_97408 = Some (Op ALU_OR 24 24 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_9740c : bv 32 := 0x01bc5c1b.
Lemma F_9740c : fetch_word Ubsan.M.loaded_segments (0x9740c : word) = Some W_9740c.
Proof. vm_refl. Qed.
Lemma D_9740c : decode_any W_9740c = Some (ShiftImm32 ALU_SRL 24 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_97410 : bv 32 := 0x000c0463.
Lemma F_97410 : fetch_word Ubsan.M.loaded_segments (0x97410 : word) = Some W_97410.
Proof. vm_refl. Qed.
Lemma D_97410 : decode_any W_97410 = Some (Branch BC_EQ 24 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97414 : bv 32 := 0x6580106f.
Lemma F_97414 : fetch_word Ubsan.M.loaded_segments (0x97414 : word) = Some W_97414.
Proof. vm_refl. Qed.
Lemma D_97414 : decode_any W_97414 = Some (Jal 0 5720, 4%Z).
Proof. vm_refl. Qed.

Definition W_97418 : bv 32 := 0x003afc93.
Lemma F_97418 : fetch_word Ubsan.M.loaded_segments (0x97418 : word) = Some W_97418.
Proof. vm_refl. Qed.
Lemma D_97418 : decode_any W_97418 = Some (OpImm ALU_AND 25 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9741c : bv 32 := 0x000a8d13.
Lemma F_9741c : fetch_word Ubsan.M.loaded_segments (0x9741c : word) = Some W_9741c.
Proof. vm_refl. Qed.
Lemma D_9741c : decode_any W_9741c = Some (OpImm ALU_ADD 26 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97420 : bv 32 := 0x018490bb.
Lemma F_97420 : fetch_word Ubsan.M.loaded_segments (0x97420 : word) = Some W_97420.
Proof. vm_refl. Qed.
Lemma D_97420 : decode_any W_97420 = Some (Op32 ALU_SLL 1 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_97424 : bv 32 := 0x000d0d93.
Lemma F_97424 : fetch_word Ubsan.M.loaded_segments (0x97424 : word) = Some W_97424.
Proof. vm_refl. Qed.
Lemma D_97424 : decode_any W_97424 = Some (OpImm ALU_ADD 27 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97428 : bv 32 := 0x0400d263.
Lemma F_97428 : fetch_word Ubsan.M.loaded_segments (0x97428 : word) = Some W_97428.
Proof. vm_refl. Qed.
Lemma D_97428 : decode_any W_97428 = Some (Branch BC_GE 1 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_9742c : bv 32 := 0x01a98db3.
Lemma F_9742c : fetch_word Ubsan.M.loaded_segments (0x9742c : word) = Some W_9742c.
Proof. vm_refl. Qed.
Lemma D_9742c : decode_any W_9742c = Some (Op ALU_ADD 27 19 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_97430 : bv 32 := 0x015030b3.
Lemma F_97430 : fetch_word Ubsan.M.loaded_segments (0x97430 : word) = Some W_97430.
Proof. vm_refl. Qed.
Lemma D_97430 : decode_any W_97430 = Some (Op ALU_SLTU 1 0 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_97434 : bv 32 := 0x001db293.
Lemma F_97434 : fetch_word Ubsan.M.loaded_segments (0x97434 : word) = Some W_97434.
Proof. vm_refl. Qed.
Lemma D_97434 : decode_any W_97434 = Some (OpImm ALU_SLTU 5 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_97438 : bv 32 := 0x00509463.
Lemma F_97438 : fetch_word Ubsan.M.loaded_segments (0x97438 : word) = Some W_97438.
Proof. vm_refl. Qed.
Lemma D_97438 : decode_any W_97438 = Some (Branch BC_NE 1 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9743c : bv 32 := 0x6300106f.
Lemma F_9743c : fetch_word Ubsan.M.loaded_segments (0x9743c : word) = Some W_9743c.
Proof. vm_refl. Qed.
Lemma D_9743c : decode_any W_9743c = Some (Jal 0 5680, 4%Z).
Proof. vm_refl. Qed.

Definition W_97440 : bv 32 := 0x01adf463.
Lemma F_97440 : fetch_word Ubsan.M.loaded_segments (0x97440 : word) = Some W_97440.
Proof. vm_refl. Qed.
Lemma D_97440 : decode_any W_97440 = Some (Branch BC_GEU 27 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97444 : bv 32 := 0x6280106f.
Lemma F_97444 : fetch_word Ubsan.M.loaded_segments (0x97444 : word) = Some W_97444.
Proof. vm_refl. Qed.
Lemma D_97444 : decode_any W_97444 = Some (Jal 0 5672, 4%Z).
Proof. vm_refl. Qed.

Definition W_97448 : bv 32 := 0x000a9463.
Lemma F_97448 : fetch_word Ubsan.M.loaded_segments (0x97448 : word) = Some W_97448.
Proof. vm_refl. Qed.
Lemma D_97448 : decode_any W_97448 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9744c : bv 32 := 0x6200106f.
Lemma F_9744c : fetch_word Ubsan.M.loaded_segments (0x9744c : word) = Some W_9744c.
Proof. vm_refl. Qed.
Lemma D_9744c : decode_any W_9744c = Some (Jal 0 5664, 4%Z).
Proof. vm_refl. Qed.

Definition W_97450 : bv 32 := 0x000c8463.
Lemma F_97450 : fetch_word Ubsan.M.loaded_segments (0x97450 : word) = Some W_97450.
Proof. vm_refl. Qed.
Lemma D_97450 : decode_any W_97450 = Some (Branch BC_EQ 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97454 : bv 32 := 0x6180106f.
Lemma F_97454 : fetch_word Ubsan.M.loaded_segments (0x97454 : word) = Some W_97454.
Proof. vm_refl. Qed.
Lemma D_97454 : decode_any W_97454 = Some (Jal 0 5656, 4%Z).
Proof. vm_refl. Qed.

Definition W_97458 : bv 32 := 0x013a82b3.
Lemma F_97458 : fetch_word Ubsan.M.loaded_segments (0x97458 : word) = Some W_97458.
Proof. vm_refl. Qed.
Lemma D_97458 : decode_any W_97458 = Some (Op ALU_ADD 5 21 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_9745c : bv 32 := 0x0002ad83.
Lemma F_9745c : fetch_word Ubsan.M.loaded_segments (0x9745c : word) = Some W_9745c.
Proof. vm_refl. Qed.
Lemma D_9745c : decode_any W_9745c = Some (Load SZ4 true 27 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97460 : bv 32 := 0x017dedb3.
Lemma F_97460 : fetch_word Ubsan.M.loaded_segments (0x97460 : word) = Some W_97460.
Proof. vm_refl. Qed.
Lemma D_97460 : decode_any W_97460 = Some (Op ALU_OR 27 27 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_97464 : bv 32 := 0x01b2a023.
Lemma F_97464 : fetch_word Ubsan.M.loaded_segments (0x97464 : word) = Some W_97464.
Proof. vm_refl. Qed.
Lemma D_97464 : decode_any W_97464 = Some (Store SZ4 5 27 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97468 : bv 32 := 0x000a8d93.
Lemma F_97468 : fetch_word Ubsan.M.loaded_segments (0x97468 : word) = Some W_97468.
Proof. vm_refl. Qed.
Lemma D_97468 : decode_any W_97468 = Some (OpImm ALU_ADD 27 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9746c : bv 32 := 0x01b780b3.
Lemma F_9746c : fetch_word Ubsan.M.loaded_segments (0x9746c : word) = Some W_9746c.
Proof. vm_refl. Qed.
Lemma D_9746c : decode_any W_9746c = Some (Op ALU_ADD 1 15 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_97470 : bv 32 := 0x015032b3.
Lemma F_97470 : fetch_word Ubsan.M.loaded_segments (0x97470 : word) = Some W_97470.
Proof. vm_refl. Qed.
Lemma D_97470 : decode_any W_97470 = Some (Op ALU_SLTU 5 0 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_97474 : bv 32 := 0x0010b693.
Lemma F_97474 : fetch_word Ubsan.M.loaded_segments (0x97474 : word) = Some W_97474.
Proof. vm_refl. Qed.
Lemma D_97474 : decode_any W_97474 = Some (OpImm ALU_SLTU 13 1 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_97478 : bv 32 := 0x00d29463.
Lemma F_97478 : fetch_word Ubsan.M.loaded_segments (0x97478 : word) = Some W_97478.
Proof. vm_refl. Qed.
Lemma D_97478 : decode_any W_97478 = Some (Branch BC_NE 5 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9747c : bv 32 := 0x5f00106f.
Lemma F_9747c : fetch_word Ubsan.M.loaded_segments (0x9747c : word) = Some W_9747c.
Proof. vm_refl. Qed.
Lemma D_9747c : decode_any W_9747c = Some (Jal 0 5616, 4%Z).
Proof. vm_refl. Qed.

Definition W_97480 : bv 32 := 0x01b0b6b3.
Lemma F_97480 : fetch_word Ubsan.M.loaded_segments (0x97480 : word) = Some W_97480.
Proof. vm_refl. Qed.
Lemma D_97480 : decode_any W_97480 = Some (Op ALU_SLTU 13 1 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_97484 : bv 32 := 0x0146c6b3.
Lemma F_97484 : fetch_word Ubsan.M.loaded_segments (0x97484 : word) = Some W_97484.
Proof. vm_refl. Qed.
Lemma D_97484 : decode_any W_97484 = Some (Op ALU_XOR 13 13 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_97488 : bv 32 := 0x0016c693.
Lemma F_97488 : fetch_word Ubsan.M.loaded_segments (0x97488 : word) = Some W_97488.
Proof. vm_refl. Qed.
Lemma D_97488 : decode_any W_97488 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9748c : bv 32 := 0x00069463.
Lemma F_9748c : fetch_word Ubsan.M.loaded_segments (0x9748c : word) = Some W_9748c.
Proof. vm_refl. Qed.
Lemma D_9748c : decode_any W_9748c = Some (Branch BC_NE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97490 : bv 32 := 0x5dc0106f.
Lemma F_97490 : fetch_word Ubsan.M.loaded_segments (0x97490 : word) = Some W_97490.
Proof. vm_refl. Qed.
Lemma D_97490 : decode_any W_97490 = Some (Jal 0 5596, 4%Z).
Proof. vm_refl. Qed.

Definition W_97494 : bv 32 := 0x00fa8ab3.
Lemma F_97494 : fetch_word Ubsan.M.loaded_segments (0x97494 : word) = Some W_97494.
Proof. vm_refl. Qed.
Lemma D_97494 : decode_any W_97494 = Some (Op ALU_ADD 21 21 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_97498 : bv 32 := 0x001c0c1b.
Lemma F_97498 : fetch_word Ubsan.M.loaded_segments (0x97498 : word) = Some W_97498.
Proof. vm_refl. Qed.
Lemma D_97498 : decode_any W_97498 = Some (OpImm32 24 24 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9749c : bv 32 := 0x00fd0d33.
Lemma F_9749c : fetch_word Ubsan.M.loaded_segments (0x9749c : word) = Some W_9749c.
Proof. vm_refl. Qed.
Lemma D_9749c : decode_any W_9749c = Some (Op ALU_ADD 26 26 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_974a0 : bv 32 := 0xf91c10e3.
Lemma F_974a0 : fetch_word Ubsan.M.loaded_segments (0x974a0 : word) = Some W_974a0.
Proof. vm_refl. Qed.
Lemma D_974a0 : decode_any W_974a0 = Some (Branch BC_NE 24 17 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_974a4 : bv 32 := 0xf1dff06f.
Lemma F_974a4 : fetch_word Ubsan.M.loaded_segments (0x974a4 : word) = Some W_974a4.
Proof. vm_refl. Qed.
Lemma D_974a4 : decode_any W_974a4 = Some (Jal 0 2096924, 4%Z).
Proof. vm_refl. Qed.

Definition W_974a8 : bv 32 := 0x000f0463.
Lemma F_974a8 : fetch_word Ubsan.M.loaded_segments (0x974a8 : word) = Some W_974a8.
Proof. vm_refl. Qed.
Lemma D_974a8 : decode_any W_974a8 = Some (Branch BC_EQ 30 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_974ac : bv 32 := 0x5c00106f.
Lemma F_974ac : fetch_word Ubsan.M.loaded_segments (0x974ac : word) = Some W_974ac.
Proof. vm_refl. Qed.
Lemma D_974ac : decode_any W_974ac = Some (Jal 0 5568, 4%Z).
Proof. vm_refl. Qed.

Definition W_974b0 : bv 32 := 0x015384b3.
Lemma F_974b0 : fetch_word Ubsan.M.loaded_segments (0x974b0 : word) = Some W_974b0.
Proof. vm_refl. Qed.
Lemma D_974b0 : decode_any W_974b0 = Some (Op ALU_ADD 9 7 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_974b4 : bv 32 := 0x01503c33.
Lemma F_974b4 : fetch_word Ubsan.M.loaded_segments (0x974b4 : word) = Some W_974b4.
Proof. vm_refl. Qed.
Lemma D_974b4 : decode_any W_974b4 = Some (Op ALU_SLTU 24 0 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_974b8 : bv 32 := 0x0014bc93.
Lemma F_974b8 : fetch_word Ubsan.M.loaded_segments (0x974b8 : word) = Some W_974b8.
Proof. vm_refl. Qed.
Lemma D_974b8 : decode_any W_974b8 = Some (OpImm ALU_SLTU 25 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_974bc : bv 32 := 0x019c1463.
Lemma F_974bc : fetch_word Ubsan.M.loaded_segments (0x974bc : word) = Some W_974bc.
Proof. vm_refl. Qed.
Lemma D_974bc : decode_any W_974bc = Some (Branch BC_NE 24 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_974c0 : bv 32 := 0x5ac0106f.
Lemma F_974c0 : fetch_word Ubsan.M.loaded_segments (0x974c0 : word) = Some W_974c0.
Proof. vm_refl. Qed.
Lemma D_974c0 : decode_any W_974c0 = Some (Jal 0 5548, 4%Z).
Proof. vm_refl. Qed.

Definition W_974c4 : bv 32 := 0x0154bab3.
Lemma F_974c4 : fetch_word Ubsan.M.loaded_segments (0x974c4 : word) = Some W_974c4.
Proof. vm_refl. Qed.
Lemma D_974c4 : decode_any W_974c4 = Some (Op ALU_SLTU 21 9 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_974c8 : bv 32 := 0x014acab3.
Lemma F_974c8 : fetch_word Ubsan.M.loaded_segments (0x974c8 : word) = Some W_974c8.
Proof. vm_refl. Qed.
Lemma D_974c8 : decode_any W_974c8 = Some (Op ALU_XOR 21 21 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_974cc : bv 32 := 0x001aca93.
Lemma F_974cc : fetch_word Ubsan.M.loaded_segments (0x974cc : word) = Some W_974cc.
Proof. vm_refl. Qed.
Lemma D_974cc : decode_any W_974cc = Some (OpImm ALU_XOR 21 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_974d0 : bv 32 := 0x000a9463.
Lemma F_974d0 : fetch_word Ubsan.M.loaded_segments (0x974d0 : word) = Some W_974d0.
Proof. vm_refl. Qed.
Lemma D_974d0 : decode_any W_974d0 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_974d4 : bv 32 := 0x5980106f.
Lemma F_974d4 : fetch_word Ubsan.M.loaded_segments (0x974d4 : word) = Some W_974d4.
Proof. vm_refl. Qed.
Lemma D_974d4 : decode_any W_974d4 = Some (Jal 0 5528, 4%Z).
Proof. vm_refl. Qed.

Definition W_974d8 : bv 32 := 0x00048a93.
Lemma F_974d8 : fetch_word Ubsan.M.loaded_segments (0x974d8 : word) = Some W_974d8.
Proof. vm_refl. Qed.
Lemma D_974d8 : decode_any W_974d8 = Some (OpImm ALU_ADD 21 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_974dc : bv 32 := 0xee5ff06f.
Lemma F_974dc : fetch_word Ubsan.M.loaded_segments (0x974dc : word) = Some W_974dc.
Proof. vm_refl. Qed.
Lemma D_974dc : decode_any W_974dc = Some (Jal 0 2096868, 4%Z).
Proof. vm_refl. Qed.

Definition W_974e0 : bv 32 := 0x05012483.
Lemma F_974e0 : fetch_word Ubsan.M.loaded_segments (0x974e0 : word) = Some W_974e0.
Proof. vm_refl. Qed.
Lemma D_974e0 : decode_any W_974e0 = Some (Load SZ4 true 9 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_974e4 : bv 32 := 0xe49ed2e3.
Lemma F_974e4 : fetch_word Ubsan.M.loaded_segments (0x974e4 : word) = Some W_974e4.
Proof. vm_refl. Qed.
Lemma D_974e4 : decode_any W_974e4 = Some (Branch BC_GE 29 9 7748, 4%Z).
Proof. vm_refl. Qed.

Definition W_974e8 : bv 32 := 0x800006b7.
Lemma F_974e8 : fetch_word Ubsan.M.loaded_segments (0x974e8 : word) = Some W_974e8.
Proof. vm_refl. Qed.
Lemma D_974e8 : decode_any W_974e8 = Some (Lui 13 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_974ec : bv 32 := 0x00c6db3b.
Lemma F_974ec : fetch_word Ubsan.M.loaded_segments (0x974ec : word) = Some W_974ec.
Proof. vm_refl. Qed.
Lemma D_974ec : decode_any W_974ec = Some (Op32 ALU_SRL 22 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_974f0 : bv 32 := 0x003afb93.
Lemma F_974f0 : fetch_word Ubsan.M.loaded_segments (0x974f0 : word) = Some W_974f0.
Proof. vm_refl. Qed.
Lemma D_974f0 : decode_any W_974f0 = Some (OpImm ALU_AND 23 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_974f4 : bv 32 := 0x000a8c13.
Lemma F_974f4 : fetch_word Ubsan.M.loaded_segments (0x974f4 : word) = Some W_974f4.
Proof. vm_refl. Qed.
Lemma D_974f4 : decode_any W_974f4 = Some (OpImm ALU_ADD 24 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_974f8 : bv 32 := 0x000e8c93.
Lemma F_974f8 : fetch_word Ubsan.M.loaded_segments (0x974f8 : word) = Some W_974f8.
Proof. vm_refl. Qed.
Lemma D_974f8 : decode_any W_974f8 = Some (OpImm ALU_ADD 25 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_974fc : bv 32 := 0x405cdd1b.
Lemma F_974fc : fetch_word Ubsan.M.loaded_segments (0x974fc : word) = Some W_974fc.
Proof. vm_refl. Qed.
Lemma D_974fc : decode_any W_974fc = Some (ShiftImm32 ALU_SRA 26 25 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_97500 : bv 32 := 0x002d1493.
Lemma F_97500 : fetch_word Ubsan.M.loaded_segments (0x97500 : word) = Some W_97500.
Proof. vm_refl. Qed.
Lemma D_97500 : decode_any W_97500 = Some (ShiftImm ALU_SLL 9 26 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_97504 : bv 32 := 0x009f84b3.
Lemma F_97504 : fetch_word Ubsan.M.loaded_segments (0x97504 : word) = Some W_97504.
Proof. vm_refl. Qed.
Lemma D_97504 : decode_any W_97504 = Some (Op ALU_ADD 9 31 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_97508 : bv 32 := 0x0014b693.
Lemma F_97508 : fetch_word Ubsan.M.loaded_segments (0x97508 : word) = Some W_97508.
Proof. vm_refl. Qed.
Lemma D_97508 : decode_any W_97508 = Some (OpImm ALU_SLTU 13 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9750c : bv 32 := 0x00d81463.
Lemma F_9750c : fetch_word Ubsan.M.loaded_segments (0x9750c : word) = Some W_9750c.
Proof. vm_refl. Qed.
Lemma D_9750c : decode_any W_9750c = Some (Branch BC_NE 16 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97510 : bv 32 := 0x55c0106f.
Lemma F_97510 : fetch_word Ubsan.M.loaded_segments (0x97510 : word) = Some W_97510.
Proof. vm_refl. Qed.
Lemma D_97510 : decode_any W_97510 = Some (Jal 0 5468, 4%Z).
Proof. vm_refl. Qed.

Definition W_97514 : bv 32 := 0x01f4b6b3.
Lemma F_97514 : fetch_word Ubsan.M.loaded_segments (0x97514 : word) = Some W_97514.
Proof. vm_refl. Qed.
Lemma D_97514 : decode_any W_97514 = Some (Op ALU_SLTU 13 9 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_97518 : bv 32 := 0x000d2293.
Lemma F_97518 : fetch_word Ubsan.M.loaded_segments (0x97518 : word) = Some W_97518.
Proof. vm_refl. Qed.
Lemma D_97518 : decode_any W_97518 = Some (OpImm ALU_SLT 5 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9751c : bv 32 := 0x0056c6b3.
Lemma F_9751c : fetch_word Ubsan.M.loaded_segments (0x9751c : word) = Some W_9751c.
Proof. vm_refl. Qed.
Lemma D_9751c : decode_any W_9751c = Some (Op ALU_XOR 13 13 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_97520 : bv 32 := 0x0016c693.
Lemma F_97520 : fetch_word Ubsan.M.loaded_segments (0x97520 : word) = Some W_97520.
Proof. vm_refl. Qed.
Lemma D_97520 : decode_any W_97520 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_97524 : bv 32 := 0x00069463.
Lemma F_97524 : fetch_word Ubsan.M.loaded_segments (0x97524 : word) = Some W_97524.
Proof. vm_refl. Qed.
Lemma D_97524 : decode_any W_97524 = Some (Branch BC_NE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97528 : bv 32 := 0x5440106f.
Lemma F_97528 : fetch_word Ubsan.M.loaded_segments (0x97528 : word) = Some W_97528.
Proof. vm_refl. Qed.
Lemma D_97528 : decode_any W_97528 = Some (Jal 0 5444, 4%Z).
Proof. vm_refl. Qed.

Definition W_9752c : bv 32 := 0x00041463.
Lemma F_9752c : fetch_word Ubsan.M.loaded_segments (0x9752c : word) = Some W_9752c.
Proof. vm_refl. Qed.
Lemma D_9752c : decode_any W_9752c = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97530 : bv 32 := 0x53c0106f.
Lemma F_97530 : fetch_word Ubsan.M.loaded_segments (0x97530 : word) = Some W_97530.
Proof. vm_refl. Qed.
Lemma D_97530 : decode_any W_97530 = Some (Jal 0 5436, 4%Z).
Proof. vm_refl. Qed.

Definition W_97534 : bv 32 := 0x0034f693.
Lemma F_97534 : fetch_word Ubsan.M.loaded_segments (0x97534 : word) = Some W_97534.
Proof. vm_refl. Qed.
Lemma D_97534 : decode_any W_97534 = Some (OpImm ALU_AND 13 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_97538 : bv 32 := 0x00068463.
Lemma F_97538 : fetch_word Ubsan.M.loaded_segments (0x97538 : word) = Some W_97538.
Proof. vm_refl. Qed.
Lemma D_97538 : decode_any W_97538 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9753c : bv 32 := 0x5300106f.
Lemma F_9753c : fetch_word Ubsan.M.loaded_segments (0x9753c : word) = Some W_9753c.
Proof. vm_refl. Qed.
Lemma D_9753c : decode_any W_9753c = Some (Jal 0 5424, 4%Z).
Proof. vm_refl. Qed.

Definition W_97540 : bv 32 := 0x0004a683.
Lemma F_97540 : fetch_word Ubsan.M.loaded_segments (0x97540 : word) = Some W_97540.
Proof. vm_refl. Qed.
Lemma D_97540 : decode_any W_97540 = Some (Load SZ4 true 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97544 : bv 32 := 0xfffcc293.
Lemma F_97544 : fetch_word Ubsan.M.loaded_segments (0x97544 : word) = Some W_97544.
Proof. vm_refl. Qed.
Lemma D_97544 : decode_any W_97544 = Some (OpImm ALU_XOR 5 25 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_97548 : bv 32 := 0x0056d6bb.
Lemma F_97548 : fetch_word Ubsan.M.loaded_segments (0x97548 : word) = Some W_97548.
Proof. vm_refl. Qed.
Lemma D_97548 : decode_any W_97548 = Some (Op32 ALU_SRL 13 13 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_9754c : bv 32 := 0x0016f693.
Lemma F_9754c : fetch_word Ubsan.M.loaded_segments (0x9754c : word) = Some W_9754c.
Proof. vm_refl. Qed.
Lemma D_9754c : decode_any W_9754c = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_97550 : bv 32 := 0x000c0493.
Lemma F_97550 : fetch_word Ubsan.M.loaded_segments (0x97550 : word) = Some W_97550.
Proof. vm_refl. Qed.
Lemma D_97550 : decode_any W_97550 = Some (OpImm ALU_ADD 9 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97554 : bv 32 := 0x04068263.
Lemma F_97554 : fetch_word Ubsan.M.loaded_segments (0x97554 : word) = Some W_97554.
Proof. vm_refl. Qed.
Lemma D_97554 : decode_any W_97554 = Some (Branch BC_EQ 13 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_97558 : bv 32 := 0x018984b3.
Lemma F_97558 : fetch_word Ubsan.M.loaded_segments (0x97558 : word) = Some W_97558.
Proof. vm_refl. Qed.
Lemma D_97558 : decode_any W_97558 = Some (Op ALU_ADD 9 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9755c : bv 32 := 0x015036b3.
Lemma F_9755c : fetch_word Ubsan.M.loaded_segments (0x9755c : word) = Some W_9755c.
Proof. vm_refl. Qed.
Lemma D_9755c : decode_any W_9755c = Some (Op ALU_SLTU 13 0 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_97560 : bv 32 := 0x0014b293.
Lemma F_97560 : fetch_word Ubsan.M.loaded_segments (0x97560 : word) = Some W_97560.
Proof. vm_refl. Qed.
Lemma D_97560 : decode_any W_97560 = Some (OpImm ALU_SLTU 5 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_97564 : bv 32 := 0x00569463.
Lemma F_97564 : fetch_word Ubsan.M.loaded_segments (0x97564 : word) = Some W_97564.
Proof. vm_refl. Qed.
Lemma D_97564 : decode_any W_97564 = Some (Branch BC_NE 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97568 : bv 32 := 0x5040106f.
Lemma F_97568 : fetch_word Ubsan.M.loaded_segments (0x97568 : word) = Some W_97568.
Proof. vm_refl. Qed.
Lemma D_97568 : decode_any W_97568 = Some (Jal 0 5380, 4%Z).
Proof. vm_refl. Qed.

Definition W_9756c : bv 32 := 0x0184f463.
Lemma F_9756c : fetch_word Ubsan.M.loaded_segments (0x9756c : word) = Some W_9756c.
Proof. vm_refl. Qed.
Lemma D_9756c : decode_any W_9756c = Some (Branch BC_GEU 9 24 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97570 : bv 32 := 0x4fc0106f.
Lemma F_97570 : fetch_word Ubsan.M.loaded_segments (0x97570 : word) = Some W_97570.
Proof. vm_refl. Qed.
Lemma D_97570 : decode_any W_97570 = Some (Jal 0 5372, 4%Z).
Proof. vm_refl. Qed.

Definition W_97574 : bv 32 := 0x000a9463.
Lemma F_97574 : fetch_word Ubsan.M.loaded_segments (0x97574 : word) = Some W_97574.
Proof. vm_refl. Qed.
Lemma D_97574 : decode_any W_97574 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97578 : bv 32 := 0x4f40106f.
Lemma F_97578 : fetch_word Ubsan.M.loaded_segments (0x97578 : word) = Some W_97578.
Proof. vm_refl. Qed.
Lemma D_97578 : decode_any W_97578 = Some (Jal 0 5364, 4%Z).
Proof. vm_refl. Qed.

Definition W_9757c : bv 32 := 0x000b8463.
Lemma F_9757c : fetch_word Ubsan.M.loaded_segments (0x9757c : word) = Some W_9757c.
Proof. vm_refl. Qed.
Lemma D_9757c : decode_any W_9757c = Some (Branch BC_EQ 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_97580 : bv 32 := 0x4ec0106f.
Lemma F_97580 : fetch_word Ubsan.M.loaded_segments (0x97580 : word) = Some W_97580.
Proof. vm_refl. Qed.
Lemma D_97580 : decode_any W_97580 = Some (Jal 0 5356, 4%Z).
Proof. vm_refl. Qed.

Definition W_97584 : bv 32 := 0x013a86b3.
Lemma F_97584 : fetch_word Ubsan.M.loaded_segments (0x97584 : word) = Some W_97584.
Proof. vm_refl. Qed.
Lemma D_97584 : decode_any W_97584 = Some (Op ALU_ADD 13 21 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_97588 : bv 32 := 0x0006a283.
Lemma F_97588 : fetch_word Ubsan.M.loaded_segments (0x97588 : word) = Some W_97588.
Proof. vm_refl. Qed.
Lemma D_97588 : decode_any W_97588 = Some (Load SZ4 true 5 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9758c : bv 32 := 0x0162e2b3.
Lemma F_9758c : fetch_word Ubsan.M.loaded_segments (0x9758c : word) = Some W_9758c.
Proof. vm_refl. Qed.
Lemma D_9758c : decode_any W_9758c = Some (Op ALU_OR 5 5 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_97590 : bv 32 := 0x0056a023.
Lemma F_97590 : fetch_word Ubsan.M.loaded_segments (0x97590 : word) = Some W_97590.
Proof. vm_refl. Qed.
Lemma D_97590 : decode_any W_97590 = Some (Store SZ4 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97594 : bv 32 := 0x000a8493.
Lemma F_97594 : fetch_word Ubsan.M.loaded_segments (0x97594 : word) = Some W_97594.
Proof. vm_refl. Qed.
Lemma D_97594 : decode_any W_97594 = Some (OpImm ALU_ADD 9 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97598 : bv 32 := 0x00978d33.
Lemma F_97598 : fetch_word Ubsan.M.loaded_segments (0x97598 : word) = Some W_97598.
Proof. vm_refl. Qed.
Lemma D_97598 : decode_any W_97598 = Some (Op ALU_ADD 26 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_9759c : bv 32 := 0x015036b3.
Lemma F_9759c : fetch_word Ubsan.M.loaded_segments (0x9759c : word) = Some W_9759c.
Proof. vm_refl. Qed.
Lemma D_9759c : decode_any W_9759c = Some (Op ALU_SLTU 13 0 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_975a0 : bv 32 := 0x001d3293.
Lemma F_975a0 : fetch_word Ubsan.M.loaded_segments (0x975a0 : word) = Some W_975a0.
Proof. vm_refl. Qed.
Lemma D_975a0 : decode_any W_975a0 = Some (OpImm ALU_SLTU 5 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_975a4 : bv 32 := 0x00569463.
Lemma F_975a4 : fetch_word Ubsan.M.loaded_segments (0x975a4 : word) = Some W_975a4.
Proof. vm_refl. Qed.
Lemma D_975a4 : decode_any W_975a4 = Some (Branch BC_NE 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_975a8 : bv 32 := 0x4c40106f.
Lemma F_975a8 : fetch_word Ubsan.M.loaded_segments (0x975a8 : word) = Some W_975a8.
Proof. vm_refl. Qed.
Lemma D_975a8 : decode_any W_975a8 = Some (Jal 0 5316, 4%Z).
Proof. vm_refl. Qed.

Definition W_975ac : bv 32 := 0x009d36b3.
Lemma F_975ac : fetch_word Ubsan.M.loaded_segments (0x975ac : word) = Some W_975ac.
Proof. vm_refl. Qed.
Lemma D_975ac : decode_any W_975ac = Some (Op ALU_SLTU 13 26 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_975b0 : bv 32 := 0x0146c6b3.
Lemma F_975b0 : fetch_word Ubsan.M.loaded_segments (0x975b0 : word) = Some W_975b0.
Proof. vm_refl. Qed.
Lemma D_975b0 : decode_any W_975b0 = Some (Op ALU_XOR 13 13 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_975b4 : bv 32 := 0x0016c693.
Lemma F_975b4 : fetch_word Ubsan.M.loaded_segments (0x975b4 : word) = Some W_975b4.
Proof. vm_refl. Qed.
Lemma D_975b4 : decode_any W_975b4 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_975b8 : bv 32 := 0x00069463.
Lemma F_975b8 : fetch_word Ubsan.M.loaded_segments (0x975b8 : word) = Some W_975b8.
Proof. vm_refl. Qed.
Lemma D_975b8 : decode_any W_975b8 = Some (Branch BC_NE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_975bc : bv 32 := 0x4b00106f.
Lemma F_975bc : fetch_word Ubsan.M.loaded_segments (0x975bc : word) = Some W_975bc.
Proof. vm_refl. Qed.
Lemma D_975bc : decode_any W_975bc = Some (Jal 0 5296, 4%Z).
Proof. vm_refl. Qed.

Definition W_975c0 : bv 32 := 0x05012483.
Lemma F_975c0 : fetch_word Ubsan.M.loaded_segments (0x975c0 : word) = Some W_975c0.
Proof. vm_refl. Qed.
Lemma D_975c0 : decode_any W_975c0 = Some (Load SZ4 true 9 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_975c4 : bv 32 := 0x001c8c9b.
Lemma F_975c4 : fetch_word Ubsan.M.loaded_segments (0x975c4 : word) = Some W_975c4.
Proof. vm_refl. Qed.
Lemma D_975c4 : decode_any W_975c4 = Some (OpImm32 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_975c8 : bv 32 := 0x00fa8ab3.
Lemma F_975c8 : fetch_word Ubsan.M.loaded_segments (0x975c8 : word) = Some W_975c8.
Proof. vm_refl. Qed.
Lemma D_975c8 : decode_any W_975c8 = Some (Op ALU_ADD 21 21 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_975cc : bv 32 := 0x00fc0c33.
Lemma F_975cc : fetch_word Ubsan.M.loaded_segments (0x975cc : word) = Some W_975cc.
Proof. vm_refl. Qed.
Lemma D_975cc : decode_any W_975cc = Some (Op ALU_ADD 24 24 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_975d0 : bv 32 := 0xf29cc6e3.
Lemma F_975d0 : fetch_word Ubsan.M.loaded_segments (0x975d0 : word) = Some W_975d0.
Proof. vm_refl. Qed.
Lemma D_975d0 : decode_any W_975d0 = Some (Branch BC_LT 25 9 7980, 4%Z).
Proof. vm_refl. Qed.

Definition W_975d4 : bv 32 := 0xd55ff06f.
Lemma F_975d4 : fetch_word Ubsan.M.loaded_segments (0x975d4 : word) = Some W_975d4.
Proof. vm_refl. Qed.
Lemma D_975d4 : decode_any W_975d4 = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.
