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

Definition W_38a54 : bv 32 := 0x00050e63.
Lemma F_38a54 : fetch_word Ubsan.M.loaded_segments (0x38a54 : word) = Some W_38a54.
Proof. vm_refl. Qed.
Lemma D_38a54 : decode_any W_38a54 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a58 : bv 32 := 0x00050693.
Lemma F_38a58 : fetch_word Ubsan.M.loaded_segments (0x38a58 : word) = Some W_38a58.
Proof. vm_refl. Qed.
Lemma D_38a58 : decode_any W_38a58 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a5c : bv 32 := 0x00757513.
Lemma F_38a5c : fetch_word Ubsan.M.loaded_segments (0x38a5c : word) = Some W_38a5c.
Proof. vm_refl. Qed.
Lemma D_38a5c : decode_any W_38a5c = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a60 : bv 32 := 0x04051263.
Lemma F_38a60 : fetch_word Ubsan.M.loaded_segments (0x38a60 : word) = Some W_38a60.
Proof. vm_refl. Qed.
Lemma D_38a60 : decode_any W_38a60 = Some (Branch BC_NE 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a64 : bv 32 := 0x00b6a423.
Lemma F_38a64 : fetch_word Ubsan.M.loaded_segments (0x38a64 : word) = Some W_38a64.
Proof. vm_refl. Qed.
Lemma D_38a64 : decode_any W_38a64 = Some (Store SZ4 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a68 : bv 32 := 0x00c6a623.
Lemma F_38a68 : fetch_word Ubsan.M.loaded_segments (0x38a68 : word) = Some W_38a68.
Proof. vm_refl. Qed.
Lemma D_38a68 : decode_any W_38a68 = Some (Store SZ4 13 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a6c : bv 32 := 0x00008067.
Lemma F_38a6c : fetch_word Ubsan.M.loaded_segments (0x38a6c : word) = Some W_38a6c.
Proof. vm_refl. Qed.
Lemma D_38a6c : decode_any W_38a6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a70 : bv 32 := 0x0000c517.
Lemma F_38a70 : fetch_word Ubsan.M.loaded_segments (0x38a70 : word) = Some W_38a70.
Proof. vm_refl. Qed.
Lemma D_38a70 : decode_any W_38a70 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a74 : bv 32 := 0x42853503.
Lemma F_38a74 : fetch_word Ubsan.M.loaded_segments (0x38a74 : word) = Some W_38a74.
Proof. vm_refl. Qed.
Lemma D_38a74 : decode_any W_38a74 = Some (Load SZ8 true 10 10 1064, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a78 : bv 32 := 0x00052503.
Lemma F_38a78 : fetch_word Ubsan.M.loaded_segments (0x38a78 : word) = Some W_38a78.
Proof. vm_refl. Qed.
Lemma D_38a78 : decode_any W_38a78 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a7c : bv 32 := 0x00500593.
Lemma F_38a7c : fetch_word Ubsan.M.loaded_segments (0x38a7c : word) = Some W_38a7c.
Proof. vm_refl. Qed.
Lemma D_38a7c : decode_any W_38a7c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a80 : bv 32 := 0x00a5ce63.
Lemma F_38a80 : fetch_word Ubsan.M.loaded_segments (0x38a80 : word) = Some W_38a80.
Proof. vm_refl. Qed.
Lemma D_38a80 : decode_any W_38a80 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a84 : bv 32 := 0xfffd8517.
Lemma F_38a84 : fetch_word Ubsan.M.loaded_segments (0x38a84 : word) = Some W_38a84.
Proof. vm_refl. Qed.
Lemma D_38a84 : decode_any W_38a84 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a88 : bv 32 := 0xfffd8597.
Lemma F_38a88 : fetch_word Ubsan.M.loaded_segments (0x38a88 : word) = Some W_38a88.
Proof. vm_refl. Qed.
Lemma D_38a88 : decode_any W_38a88 = Some (Auipc 11 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a8c : bv 32 := 0xc1550513.
Lemma F_38a8c : fetch_word Ubsan.M.loaded_segments (0x38a8c : word) = Some W_38a8c.
Proof. vm_refl. Qed.
Lemma D_38a8c : decode_any W_38a8c = Some (OpImm ALU_ADD 10 10 3093, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a90 : bv 32 := 0xf7758593.
Lemma F_38a90 : fetch_word Ubsan.M.loaded_segments (0x38a90 : word) = Some W_38a90.
Proof. vm_refl. Qed.
Lemma D_38a90 : decode_any W_38a90 = Some (OpImm ALU_ADD 11 11 3959, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a94 : bv 32 := 0x00100613.
Lemma F_38a94 : fetch_word Ubsan.M.loaded_segments (0x38a94 : word) = Some W_38a94.
Proof. vm_refl. Qed.
Lemma D_38a94 : decode_any W_38a94 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a98 : bv 32 := 0xb5cdf06f.
Lemma F_38a98 : fetch_word Ubsan.M.loaded_segments (0x38a98 : word) = Some W_38a98.
Proof. vm_refl. Qed.
Lemma D_38a98 : decode_any W_38a98 = Some (Jal 0 1962844, 4%Z).
Proof. vm_refl. Qed.

Definition W_38a9c : bv 32 := 0x00100513.
Lemma F_38a9c : fetch_word Ubsan.M.loaded_segments (0x38a9c : word) = Some W_38a9c.
Proof. vm_refl. Qed.
Lemma D_38a9c : decode_any W_38a9c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38aa0 : bv 32 := 0x00008067.
Lemma F_38aa0 : fetch_word Ubsan.M.loaded_segments (0x38aa0 : word) = Some W_38aa0.
Proof. vm_refl. Qed.
Lemma D_38aa0 : decode_any W_38aa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38aa4 : bv 32 := 0xc0001073.
Lemma F_38aa4 : fetch_word Ubsan.M.loaded_segments (0x38aa4 : word) = Some W_38aa4.
Proof. vm_refl. Qed.
Lemma D_38aa4 : decode_any W_38aa4 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5c4 : bv 32 := 0xfd010113.
Lemma F_3b5c4 : fetch_word Ubsan.M.loaded_segments (0x3b5c4 : word) = Some W_3b5c4.
Proof. vm_refl. Qed.
Lemma D_3b5c4 : decode_any W_3b5c4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5c8 : bv 32 := 0x02113423.
Lemma F_3b5c8 : fetch_word Ubsan.M.loaded_segments (0x3b5c8 : word) = Some W_3b5c8.
Proof. vm_refl. Qed.
Lemma D_3b5c8 : decode_any W_3b5c8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5cc : bv 32 := 0x02813023.
Lemma F_3b5cc : fetch_word Ubsan.M.loaded_segments (0x3b5cc : word) = Some W_3b5cc.
Proof. vm_refl. Qed.
Lemma D_3b5cc : decode_any W_3b5cc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5d0 : bv 32 := 0x00913c23.
Lemma F_3b5d0 : fetch_word Ubsan.M.loaded_segments (0x3b5d0 : word) = Some W_3b5d0.
Proof. vm_refl. Qed.
Lemma D_3b5d0 : decode_any W_3b5d0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5d4 : bv 32 := 0x01213823.
Lemma F_3b5d4 : fetch_word Ubsan.M.loaded_segments (0x3b5d4 : word) = Some W_3b5d4.
Proof. vm_refl. Qed.
Lemma D_3b5d4 : decode_any W_3b5d4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5d8 : bv 32 := 0x00813427.
Lemma F_3b5d8 : fetch_word Ubsan.M.loaded_segments (0x3b5d8 : word) = Some W_3b5d8.
Proof. vm_refl. Qed.
Lemma D_3b5d8 : decode_any W_3b5d8 = Some (FStore FMT_D 2 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5dc : bv 32 := 0xf00007d3.
Lemma F_3b5dc : fetch_word Ubsan.M.loaded_segments (0x3b5dc : word) = Some W_3b5dc.
Proof. vm_refl. Qed.
Lemma D_3b5dc : decode_any W_3b5dc = Some (Fmv FMV_F_X FMT_S 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5e0 : bv 32 := 0xa0f50553.
Lemma F_3b5e0 : fetch_word Ubsan.M.loaded_segments (0x3b5e0 : word) = Some W_3b5e0.
Proof. vm_refl. Qed.
Lemma D_3b5e0 : decode_any W_3b5e0 = Some (Fcmp F_LE FMT_S 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5e4 : bv 32 := 0x06051863.
Lemma F_3b5e4 : fetch_word Ubsan.M.loaded_segments (0x3b5e4 : word) = Some W_3b5e4.
Proof. vm_refl. Qed.
Lemma D_3b5e4 : decode_any W_3b5e4 = Some (Branch BC_NE 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5e8 : bv 32 := 0x20a50453.
Lemma F_3b5e8 : fetch_word Ubsan.M.loaded_segments (0x3b5e8 : word) = Some W_3b5e8.
Proof. vm_refl. Qed.
Lemma D_3b5e8 : decode_any W_3b5e8 = Some (Fsgnj F_SGNJ FMT_S 8 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5ec : bv 32 := 0x00100513.
Lemma F_3b5ec : fetch_word Ubsan.M.loaded_segments (0x3b5ec : word) = Some W_3b5ec.
Proof. vm_refl. Qed.
Lemma D_3b5ec : decode_any W_3b5ec = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5f0 : bv 32 := 0x10000593.
Lemma F_3b5f0 : fetch_word Ubsan.M.loaded_segments (0x3b5f0 : word) = Some W_3b5f0.
Proof. vm_refl. Qed.
Lemma D_3b5f0 : decode_any W_3b5f0 = Some (OpImm ALU_ADD 11 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5f4 : bv 32 := 0x10000913.
Lemma F_3b5f4 : fetch_word Ubsan.M.loaded_segments (0x3b5f4 : word) = Some W_3b5f4.
Proof. vm_refl. Qed.
Lemma D_3b5f4 : decode_any W_3b5f4 = Some (OpImm ALU_ADD 18 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5f8 : bv 32 := 0xcd9fc0ef.
Lemma F_3b5f8 : fetch_word Ubsan.M.loaded_segments (0x3b5f8 : word) = Some W_3b5f8.
Proof. vm_refl. Qed.
Lemma D_3b5f8 : decode_any W_3b5f8 = Some (Jal 1 2084056, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5fc : bv 32 := 0x06050c63.
Lemma F_3b5fc : fetch_word Ubsan.M.loaded_segments (0x3b5fc : word) = Some W_3b5fc.
Proof. vm_refl. Qed.
Lemma D_3b5fc : decode_any W_3b5fc = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b600 : bv 32 := 0x00050413.
Lemma F_3b600 : fetch_word Ubsan.M.loaded_segments (0x3b600 : word) = Some W_3b600.
Proof. vm_refl. Qed.
Lemma D_3b600 : decode_any W_3b600 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b604 : bv 32 := 0x420407d3.
Lemma F_3b604 : fetch_word Ubsan.M.loaded_segments (0x3b604 : word) = Some W_3b604.
Proof. vm_refl. Qed.
Lemma D_3b604 : decode_any W_3b604 = Some (Fcvt FC_D FC_S 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b608 : bv 32 := 0x02f7f753.
Lemma F_3b608 : fetch_word Ubsan.M.loaded_segments (0x3b608 : word) = Some W_3b608.
Proof. vm_refl. Qed.
Lemma D_3b608 : decode_any W_3b608 = Some (Fari F_ADD FMT_D 14 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b60c : bv 32 := 0x12f777d3.
Lemma F_3b60c : fetch_word Ubsan.M.loaded_segments (0x3b60c : word) = Some W_3b60c.
Proof. vm_refl. Qed.
Lemma D_3b60c : decode_any W_3b60c = Some (Fari F_MUL FMT_D 15 14 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b610 : bv 32 := 0x4017f453.
Lemma F_3b610 : fetch_word Ubsan.M.loaded_segments (0x3b610 : word) = Some W_3b610.
Proof. vm_refl. Qed.
Lemma D_3b610 : decode_any W_3b610 = Some (Fcvt FC_S FC_D 8 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b614 : bv 32 := 0x00000593.
Lemma F_3b614 : fetch_word Ubsan.M.loaded_segments (0x3b614 : word) = Some W_3b614.
Proof. vm_refl. Qed.
Lemma D_3b614 : decode_any W_3b614 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b618 : bv 32 := 0x00000613.
Lemma F_3b618 : fetch_word Ubsan.M.loaded_segments (0x3b618 : word) = Some W_3b618.
Proof. vm_refl. Qed.
Lemma D_3b618 : decode_any W_3b618 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b61c : bv 32 := 0xc38fd0ef.
Lemma F_3b61c : fetch_word Ubsan.M.loaded_segments (0x3b61c : word) = Some W_3b61c.
Proof. vm_refl. Qed.
Lemma D_3b61c : decode_any W_3b61c = Some (Jal 1 2085944, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b620 : bv 32 := 0x00000493.
Lemma F_3b620 : fetch_word Ubsan.M.loaded_segments (0x3b620 : word) = Some W_3b620.
Proof. vm_refl. Qed.
Lemma D_3b620 : decode_any W_3b620 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b624 : bv 32 := 0x02948533.
Lemma F_3b624 : fetch_word Ubsan.M.loaded_segments (0x3b624 : word) = Some W_3b624.
Proof. vm_refl. Qed.
Lemma D_3b624 : decode_any W_3b624 = Some (Mul M_MUL 10 9 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b628 : bv 32 := 0xd01577d3.
Lemma F_3b628 : fetch_word Ubsan.M.loaded_segments (0x3b628 : word) = Some W_3b628.
Proof. vm_refl. Qed.
Lemma D_3b628 : decode_any W_3b628 = Some (Fcvt FC_S FC_WU 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b62c : bv 32 := 0x20f797d3.
Lemma F_3b62c : fetch_word Ubsan.M.loaded_segments (0x3b62c : word) = Some W_3b62c.
Proof. vm_refl. Qed.
Lemma D_3b62c : decode_any W_3b62c = Some (Fsgnj F_SGNJN FMT_S 15 15 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b630 : bv 32 := 0x1887f553.
Lemma F_3b630 : fetch_word Ubsan.M.loaded_segments (0x3b630 : word) = Some W_3b630.
Proof. vm_refl. Qed.
Lemma D_3b630 : decode_any W_3b630 = Some (Fari F_DIV FMT_S 10 15 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b634 : bv 32 := 0x5a8020ef.
Lemma F_3b634 : fetch_word Ubsan.M.loaded_segments (0x3b634 : word) = Some W_3b634.
Proof. vm_refl. Qed.
Lemma D_3b634 : decode_any W_3b634 = Some (Jal 1 9640, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b638 : bv 32 := 0x00040513.
Lemma F_3b638 : fetch_word Ubsan.M.loaded_segments (0x3b638 : word) = Some W_3b638.
Proof. vm_refl. Qed.
Lemma D_3b638 : decode_any W_3b638 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b63c : bv 32 := 0x00000593.
Lemma F_3b63c : fetch_word Ubsan.M.loaded_segments (0x3b63c : word) = Some W_3b63c.
Proof. vm_refl. Qed.
Lemma D_3b63c : decode_any W_3b63c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b640 : bv 32 := 0x00048613.
Lemma F_3b640 : fetch_word Ubsan.M.loaded_segments (0x3b640 : word) = Some W_3b640.
Proof. vm_refl. Qed.
Lemma D_3b640 : decode_any W_3b640 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b644 : bv 32 := 0xafcfd0ef.
Lemma F_3b644 : fetch_word Ubsan.M.loaded_segments (0x3b644 : word) = Some W_3b644.
Proof. vm_refl. Qed.
Lemma D_3b644 : decode_any W_3b644 = Some (Jal 1 2085628, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b648 : bv 32 := 0x0014849b.
Lemma F_3b648 : fetch_word Ubsan.M.loaded_segments (0x3b648 : word) = Some W_3b648.
Proof. vm_refl. Qed.
Lemma D_3b648 : decode_any W_3b648 = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b64c : bv 32 := 0xfd249ce3.
Lemma F_3b64c : fetch_word Ubsan.M.loaded_segments (0x3b64c : word) = Some W_3b64c.
Proof. vm_refl. Qed.
Lemma D_3b64c : decode_any W_3b64c = Some (Branch BC_NE 9 18 8152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b650 : bv 32 := 0x06c0006f.
Lemma F_3b650 : fetch_word Ubsan.M.loaded_segments (0x3b650 : word) = Some W_3b650.
Proof. vm_refl. Qed.
Lemma D_3b650 : decode_any W_3b650 = Some (Jal 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b654 : bv 32 := 0x0000a517.
Lemma F_3b654 : fetch_word Ubsan.M.loaded_segments (0x3b654 : word) = Some W_3b654.
Proof. vm_refl. Qed.
Lemma D_3b654 : decode_any W_3b654 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b658 : bv 32 := 0x84453503.
Lemma F_3b658 : fetch_word Ubsan.M.loaded_segments (0x3b658 : word) = Some W_3b658.
Proof. vm_refl. Qed.
Lemma D_3b658 : decode_any W_3b658 = Some (Load SZ8 true 10 10 2116, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b65c : bv 32 := 0x00052503.
Lemma F_3b65c : fetch_word Ubsan.M.loaded_segments (0x3b65c : word) = Some W_3b65c.
Proof. vm_refl. Qed.
Lemma D_3b65c : decode_any W_3b65c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b660 : bv 32 := 0x00600593.
Lemma F_3b660 : fetch_word Ubsan.M.loaded_segments (0x3b660 : word) = Some W_3b660.
Proof. vm_refl. Qed.
Lemma D_3b660 : decode_any W_3b660 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b664 : bv 32 := 0x04b55a63.
Lemma F_3b664 : fetch_word Ubsan.M.loaded_segments (0x3b664 : word) = Some W_3b664.
Proof. vm_refl. Qed.
Lemma D_3b664 : decode_any W_3b664 = Some (Branch BC_GE 10 11 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b668 : bv 32 := 0xfffd6517.
Lemma F_3b668 : fetch_word Ubsan.M.loaded_segments (0x3b668 : word) = Some W_3b668.
Proof. vm_refl. Qed.
Lemma D_3b668 : decode_any W_3b668 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b66c : bv 32 := 0xd5d50513.
Lemma F_3b66c : fetch_word Ubsan.M.loaded_segments (0x3b66c : word) = Some W_3b66c.
Proof. vm_refl. Qed.
Lemma D_3b66c : decode_any W_3b66c = Some (OpImm ALU_ADD 10 10 3421, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b670 : bv 32 := 0x0200006f.
Lemma F_3b670 : fetch_word Ubsan.M.loaded_segments (0x3b670 : word) = Some W_3b670.
Proof. vm_refl. Qed.
Lemma D_3b670 : decode_any W_3b670 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b674 : bv 32 := 0x0000a517.
Lemma F_3b674 : fetch_word Ubsan.M.loaded_segments (0x3b674 : word) = Some W_3b674.
Proof. vm_refl. Qed.
Lemma D_3b674 : decode_any W_3b674 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b678 : bv 32 := 0x82453503.
Lemma F_3b678 : fetch_word Ubsan.M.loaded_segments (0x3b678 : word) = Some W_3b678.
Proof. vm_refl. Qed.
Lemma D_3b678 : decode_any W_3b678 = Some (Load SZ8 true 10 10 2084, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b67c : bv 32 := 0x00052503.
Lemma F_3b67c : fetch_word Ubsan.M.loaded_segments (0x3b67c : word) = Some W_3b67c.
Proof. vm_refl. Qed.
Lemma D_3b67c : decode_any W_3b67c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b680 : bv 32 := 0x00600593.
Lemma F_3b680 : fetch_word Ubsan.M.loaded_segments (0x3b680 : word) = Some W_3b680.
Proof. vm_refl. Qed.
Lemma D_3b680 : decode_any W_3b680 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b684 : bv 32 := 0x02b55a63.
Lemma F_3b684 : fetch_word Ubsan.M.loaded_segments (0x3b684 : word) = Some W_3b684.
Proof. vm_refl. Qed.
Lemma D_3b684 : decode_any W_3b684 = Some (Branch BC_GE 10 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b688 : bv 32 := 0xfffd6517.
Lemma F_3b688 : fetch_word Ubsan.M.loaded_segments (0x3b688 : word) = Some W_3b688.
Proof. vm_refl. Qed.
Lemma D_3b688 : decode_any W_3b688 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b68c : bv 32 := 0x15350513.
Lemma F_3b68c : fetch_word Ubsan.M.loaded_segments (0x3b68c : word) = Some W_3b68c.
Proof. vm_refl. Qed.
Lemma D_3b68c : decode_any W_3b68c = Some (OpImm ALU_ADD 10 10 339, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b690 : bv 32 := 0xfffd6597.
Lemma F_3b690 : fetch_word Ubsan.M.loaded_segments (0x3b690 : word) = Some W_3b690.
Proof. vm_refl. Qed.
Lemma D_3b690 : decode_any W_3b690 = Some (Auipc 11 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b694 : bv 32 := 0x27b58593.
Lemma F_3b694 : fetch_word Ubsan.M.loaded_segments (0x3b694 : word) = Some W_3b694.
Proof. vm_refl. Qed.
Lemma D_3b694 : decode_any W_3b694 = Some (OpImm ALU_ADD 11 11 635, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b698 : bv 32 := 0x00000613.
Lemma F_3b698 : fetch_word Ubsan.M.loaded_segments (0x3b698 : word) = Some W_3b698.
Proof. vm_refl. Qed.
Lemma D_3b698 : decode_any W_3b698 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b69c : bv 32 := 0x02813083.
Lemma F_3b69c : fetch_word Ubsan.M.loaded_segments (0x3b69c : word) = Some W_3b69c.
Proof. vm_refl. Qed.
Lemma D_3b69c : decode_any W_3b69c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6a0 : bv 32 := 0x02013403.
Lemma F_3b6a0 : fetch_word Ubsan.M.loaded_segments (0x3b6a0 : word) = Some W_3b6a0.
Proof. vm_refl. Qed.
Lemma D_3b6a0 : decode_any W_3b6a0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6a4 : bv 32 := 0x01813483.
Lemma F_3b6a4 : fetch_word Ubsan.M.loaded_segments (0x3b6a4 : word) = Some W_3b6a4.
Proof. vm_refl. Qed.
Lemma D_3b6a4 : decode_any W_3b6a4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6a8 : bv 32 := 0x01013903.
Lemma F_3b6a8 : fetch_word Ubsan.M.loaded_segments (0x3b6a8 : word) = Some W_3b6a8.
Proof. vm_refl. Qed.
Lemma D_3b6a8 : decode_any W_3b6a8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6ac : bv 32 := 0x00813407.
Lemma F_3b6ac : fetch_word Ubsan.M.loaded_segments (0x3b6ac : word) = Some W_3b6ac.
Proof. vm_refl. Qed.
Lemma D_3b6ac : decode_any W_3b6ac = Some (FLoad FMT_D 8 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6b0 : bv 32 := 0x03010113.
Lemma F_3b6b0 : fetch_word Ubsan.M.loaded_segments (0x3b6b0 : word) = Some W_3b6b0.
Proof. vm_refl. Qed.
Lemma D_3b6b0 : decode_any W_3b6b0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6b4 : bv 32 := 0x811dc06f.
Lemma F_3b6b4 : fetch_word Ubsan.M.loaded_segments (0x3b6b4 : word) = Some W_3b6b4.
Proof. vm_refl. Qed.
Lemma D_3b6b4 : decode_any W_3b6b4 = Some (Jal 0 1951760, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6b8 : bv 32 := 0x00000413.
Lemma F_3b6b8 : fetch_word Ubsan.M.loaded_segments (0x3b6b8 : word) = Some W_3b6b8.
Proof. vm_refl. Qed.
Lemma D_3b6b8 : decode_any W_3b6b8 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6bc : bv 32 := 0x00040513.
Lemma F_3b6bc : fetch_word Ubsan.M.loaded_segments (0x3b6bc : word) = Some W_3b6bc.
Proof. vm_refl. Qed.
Lemma D_3b6bc : decode_any W_3b6bc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6c0 : bv 32 := 0x02813083.
Lemma F_3b6c0 : fetch_word Ubsan.M.loaded_segments (0x3b6c0 : word) = Some W_3b6c0.
Proof. vm_refl. Qed.
Lemma D_3b6c0 : decode_any W_3b6c0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6c4 : bv 32 := 0x02013403.
Lemma F_3b6c4 : fetch_word Ubsan.M.loaded_segments (0x3b6c4 : word) = Some W_3b6c4.
Proof. vm_refl. Qed.
Lemma D_3b6c4 : decode_any W_3b6c4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6c8 : bv 32 := 0x01813483.
Lemma F_3b6c8 : fetch_word Ubsan.M.loaded_segments (0x3b6c8 : word) = Some W_3b6c8.
Proof. vm_refl. Qed.
Lemma D_3b6c8 : decode_any W_3b6c8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6cc : bv 32 := 0x01013903.
Lemma F_3b6cc : fetch_word Ubsan.M.loaded_segments (0x3b6cc : word) = Some W_3b6cc.
Proof. vm_refl. Qed.
Lemma D_3b6cc : decode_any W_3b6cc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6d0 : bv 32 := 0x00813407.
Lemma F_3b6d0 : fetch_word Ubsan.M.loaded_segments (0x3b6d0 : word) = Some W_3b6d0.
Proof. vm_refl. Qed.
Lemma D_3b6d0 : decode_any W_3b6d0 = Some (FLoad FMT_D 8 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6d4 : bv 32 := 0x03010113.
Lemma F_3b6d4 : fetch_word Ubsan.M.loaded_segments (0x3b6d4 : word) = Some W_3b6d4.
Proof. vm_refl. Qed.
Lemma D_3b6d4 : decode_any W_3b6d4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b6d8 : bv 32 := 0x00008067.
Lemma F_3b6d8 : fetch_word Ubsan.M.loaded_segments (0x3b6d8 : word) = Some W_3b6d8.
Proof. vm_refl. Qed.
Lemma D_3b6d8 : decode_any W_3b6d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
