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

Definition W_3b3e4 : bv 32 := 0xfc010113.
Lemma F_3b3e4 : fetch_word Ubsan.M.loaded_segments (0x3b3e4 : word) = Some W_3b3e4.
Proof. vm_refl. Qed.
Lemma D_3b3e4 : decode_any W_3b3e4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3e8 : bv 32 := 0x02113c23.
Lemma F_3b3e8 : fetch_word Ubsan.M.loaded_segments (0x3b3e8 : word) = Some W_3b3e8.
Proof. vm_refl. Qed.
Lemma D_3b3e8 : decode_any W_3b3e8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3ec : bv 32 := 0x02813823.
Lemma F_3b3ec : fetch_word Ubsan.M.loaded_segments (0x3b3ec : word) = Some W_3b3ec.
Proof. vm_refl. Qed.
Lemma D_3b3ec : decode_any W_3b3ec = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3f0 : bv 32 := 0x02913423.
Lemma F_3b3f0 : fetch_word Ubsan.M.loaded_segments (0x3b3f0 : word) = Some W_3b3f0.
Proof. vm_refl. Qed.
Lemma D_3b3f0 : decode_any W_3b3f0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3f4 : bv 32 := 0x02813027.
Lemma F_3b3f4 : fetch_word Ubsan.M.loaded_segments (0x3b3f4 : word) = Some W_3b3f4.
Proof. vm_refl. Qed.
Lemma D_3b3f4 : decode_any W_3b3f4 = Some (FStore FMT_D 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3f8 : bv 32 := 0x00913c27.
Lemma F_3b3f8 : fetch_word Ubsan.M.loaded_segments (0x3b3f8 : word) = Some W_3b3f8.
Proof. vm_refl. Qed.
Lemma D_3b3f8 : decode_any W_3b3f8 = Some (FStore FMT_D 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b3fc : bv 32 := 0x04050c63.
Lemma F_3b3fc : fetch_word Ubsan.M.loaded_segments (0x3b3fc : word) = Some W_3b3fc.
Proof. vm_refl. Qed.
Lemma D_3b3fc : decode_any W_3b3fc = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b400 : bv 32 := 0x20b58453.
Lemma F_3b400 : fetch_word Ubsan.M.loaded_segments (0x3b400 : word) = Some W_3b400.
Proof. vm_refl. Qed.
Lemma D_3b400 : decode_any W_3b400 = Some (Fsgnj F_SGNJ FMT_S 8 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b404 : bv 32 := 0x20a504d3.
Lemma F_3b404 : fetch_word Ubsan.M.loaded_segments (0x3b404 : word) = Some W_3b404.
Proof. vm_refl. Qed.
Lemma D_3b404 : decode_any W_3b404 = Some (Fsgnj F_SGNJ FMT_S 9 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b408 : bv 32 := 0x00050413.
Lemma F_3b408 : fetch_word Ubsan.M.loaded_segments (0x3b408 : word) = Some W_3b408.
Proof. vm_refl. Qed.
Lemma D_3b408 : decode_any W_3b408 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b40c : bv 32 := 0xcc0df0ef.
Lemma F_3b40c : fetch_word Ubsan.M.loaded_segments (0x3b40c : word) = Some W_3b40c.
Proof. vm_refl. Qed.
Lemma D_3b40c : decode_any W_3b40c = Some (Jal 1 1963200, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b410 : bv 32 := 0x00800593.
Lemma F_3b410 : fetch_word Ubsan.M.loaded_segments (0x3b410 : word) = Some W_3b410.
Proof. vm_refl. Qed.
Lemma D_3b410 : decode_any W_3b410 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b414 : bv 32 := 0x00b50663.
Lemma F_3b414 : fetch_word Ubsan.M.loaded_segments (0x3b414 : word) = Some W_3b414.
Proof. vm_refl. Qed.
Lemma D_3b414 : decode_any W_3b414 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b418 : bv 32 := 0x02000593.
Lemma F_3b418 : fetch_word Ubsan.M.loaded_segments (0x3b418 : word) = Some W_3b418.
Proof. vm_refl. Qed.
Lemma D_3b418 : decode_any W_3b418 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b41c : bv 32 := 0x06b51063.
Lemma F_3b41c : fetch_word Ubsan.M.loaded_segments (0x3b41c : word) = Some W_3b41c.
Proof. vm_refl. Qed.
Lemma D_3b41c : decode_any W_3b41c = Some (Branch BC_NE 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b420 : bv 32 := 0x00040513.
Lemma F_3b420 : fetch_word Ubsan.M.loaded_segments (0x3b420 : word) = Some W_3b420.
Proof. vm_refl. Qed.
Lemma D_3b420 : decode_any W_3b420 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b424 : bv 32 := 0xdccdf0ef.
Lemma F_3b424 : fetch_word Ubsan.M.loaded_segments (0x3b424 : word) = Some W_3b424.
Proof. vm_refl. Qed.
Lemma D_3b424 : decode_any W_3b424 = Some (Jal 1 1963468, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b428 : bv 32 := 0x06050e63.
Lemma F_3b428 : fetch_word Ubsan.M.loaded_segments (0x3b428 : word) = Some W_3b428.
Proof. vm_refl. Qed.
Lemma D_3b428 : decode_any W_3b428 = Some (Branch BC_EQ 10 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b42c : bv 32 := 0x0000a517.
Lemma F_3b42c : fetch_word Ubsan.M.loaded_segments (0x3b42c : word) = Some W_3b42c.
Proof. vm_refl. Qed.
Lemma D_3b42c : decode_any W_3b42c = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b430 : bv 32 := 0xa6c53503.
Lemma F_3b430 : fetch_word Ubsan.M.loaded_segments (0x3b430 : word) = Some W_3b430.
Proof. vm_refl. Qed.
Lemma D_3b430 : decode_any W_3b430 = Some (Load SZ8 true 10 10 2668, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b434 : bv 32 := 0x00052503.
Lemma F_3b434 : fetch_word Ubsan.M.loaded_segments (0x3b434 : word) = Some W_3b434.
Proof. vm_refl. Qed.
Lemma D_3b434 : decode_any W_3b434 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b438 : bv 32 := 0x00500593.
Lemma F_3b438 : fetch_word Ubsan.M.loaded_segments (0x3b438 : word) = Some W_3b438.
Proof. vm_refl. Qed.
Lemma D_3b438 : decode_any W_3b438 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b43c : bv 32 := 0x16a5c263.
Lemma F_3b43c : fetch_word Ubsan.M.loaded_segments (0x3b43c : word) = Some W_3b43c.
Proof. vm_refl. Qed.
Lemma D_3b43c : decode_any W_3b43c = Some (Branch BC_LT 11 10 356, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b440 : bv 32 := 0xfffd6517.
Lemma F_3b440 : fetch_word Ubsan.M.loaded_segments (0x3b440 : word) = Some W_3b440.
Proof. vm_refl. Qed.
Lemma D_3b440 : decode_any W_3b440 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b444 : bv 32 := 0xfffd7597.
Lemma F_3b444 : fetch_word Ubsan.M.loaded_segments (0x3b444 : word) = Some W_3b444.
Proof. vm_refl. Qed.
Lemma D_3b444 : decode_any W_3b444 = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b448 : bv 32 := 0x19650513.
Lemma F_3b448 : fetch_word Ubsan.M.loaded_segments (0x3b448 : word) = Some W_3b448.
Proof. vm_refl. Qed.
Lemma D_3b448 : decode_any W_3b448 = Some (OpImm ALU_ADD 10 10 406, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b44c : bv 32 := 0xb6e58593.
Lemma F_3b44c : fetch_word Ubsan.M.loaded_segments (0x3b44c : word) = Some W_3b44c.
Proof. vm_refl. Qed.
Lemma D_3b44c : decode_any W_3b44c = Some (OpImm ALU_ADD 11 11 2926, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b450 : bv 32 := 0x1300006f.
Lemma F_3b450 : fetch_word Ubsan.M.loaded_segments (0x3b450 : word) = Some W_3b450.
Proof. vm_refl. Qed.
Lemma D_3b450 : decode_any W_3b450 = Some (Jal 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b454 : bv 32 := 0x0000a517.
Lemma F_3b454 : fetch_word Ubsan.M.loaded_segments (0x3b454 : word) = Some W_3b454.
Proof. vm_refl. Qed.
Lemma D_3b454 : decode_any W_3b454 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b458 : bv 32 := 0xa4453503.
Lemma F_3b458 : fetch_word Ubsan.M.loaded_segments (0x3b458 : word) = Some W_3b458.
Proof. vm_refl. Qed.
Lemma D_3b458 : decode_any W_3b458 = Some (Load SZ8 true 10 10 2628, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b45c : bv 32 := 0x00052503.
Lemma F_3b45c : fetch_word Ubsan.M.loaded_segments (0x3b45c : word) = Some W_3b45c.
Proof. vm_refl. Qed.
Lemma D_3b45c : decode_any W_3b45c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b460 : bv 32 := 0x00500593.
Lemma F_3b460 : fetch_word Ubsan.M.loaded_segments (0x3b460 : word) = Some W_3b460.
Proof. vm_refl. Qed.
Lemma D_3b460 : decode_any W_3b460 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b464 : bv 32 := 0x12a5ce63.
Lemma F_3b464 : fetch_word Ubsan.M.loaded_segments (0x3b464 : word) = Some W_3b464.
Proof. vm_refl. Qed.
Lemma D_3b464 : decode_any W_3b464 = Some (Branch BC_LT 11 10 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b468 : bv 32 := 0xfffd5517.
Lemma F_3b468 : fetch_word Ubsan.M.loaded_segments (0x3b468 : word) = Some W_3b468.
Proof. vm_refl. Qed.
Lemma D_3b468 : decode_any W_3b468 = Some (Auipc 10 1048533, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b46c : bv 32 := 0xfffd7597.
Lemma F_3b46c : fetch_word Ubsan.M.loaded_segments (0x3b46c : word) = Some W_3b46c.
Proof. vm_refl. Qed.
Lemma D_3b46c : decode_any W_3b46c = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b470 : bv 32 := 0xe4c50513.
Lemma F_3b470 : fetch_word Ubsan.M.loaded_segments (0x3b470 : word) = Some W_3b470.
Proof. vm_refl. Qed.
Lemma D_3b470 : decode_any W_3b470 = Some (OpImm ALU_ADD 10 10 3660, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b474 : bv 32 := 0xb4658593.
Lemma F_3b474 : fetch_word Ubsan.M.loaded_segments (0x3b474 : word) = Some W_3b474.
Proof. vm_refl. Qed.
Lemma D_3b474 : decode_any W_3b474 = Some (OpImm ALU_ADD 11 11 2886, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b478 : bv 32 := 0x1080006f.
Lemma F_3b478 : fetch_word Ubsan.M.loaded_segments (0x3b478 : word) = Some W_3b478.
Proof. vm_refl. Qed.
Lemma D_3b478 : decode_any W_3b478 = Some (Jal 0 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b47c : bv 32 := 0x0000a517.
Lemma F_3b47c : fetch_word Ubsan.M.loaded_segments (0x3b47c : word) = Some W_3b47c.
Proof. vm_refl. Qed.
Lemma D_3b47c : decode_any W_3b47c = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b480 : bv 32 := 0xa1c53503.
Lemma F_3b480 : fetch_word Ubsan.M.loaded_segments (0x3b480 : word) = Some W_3b480.
Proof. vm_refl. Qed.
Lemma D_3b480 : decode_any W_3b480 = Some (Load SZ8 true 10 10 2588, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b484 : bv 32 := 0x00052503.
Lemma F_3b484 : fetch_word Ubsan.M.loaded_segments (0x3b484 : word) = Some W_3b484.
Proof. vm_refl. Qed.
Lemma D_3b484 : decode_any W_3b484 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b488 : bv 32 := 0x00500593.
Lemma F_3b488 : fetch_word Ubsan.M.loaded_segments (0x3b488 : word) = Some W_3b488.
Proof. vm_refl. Qed.
Lemma D_3b488 : decode_any W_3b488 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b48c : bv 32 := 0x10a5ca63.
Lemma F_3b48c : fetch_word Ubsan.M.loaded_segments (0x3b48c : word) = Some W_3b48c.
Proof. vm_refl. Qed.
Lemma D_3b48c : decode_any W_3b48c = Some (Branch BC_LT 11 10 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b490 : bv 32 := 0xfffd6517.
Lemma F_3b490 : fetch_word Ubsan.M.loaded_segments (0x3b490 : word) = Some W_3b490.
Proof. vm_refl. Qed.
Lemma D_3b490 : decode_any W_3b490 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b494 : bv 32 := 0xfffd7597.
Lemma F_3b494 : fetch_word Ubsan.M.loaded_segments (0x3b494 : word) = Some W_3b494.
Proof. vm_refl. Qed.
Lemma D_3b494 : decode_any W_3b494 = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b498 : bv 32 := 0x1cf50513.
Lemma F_3b498 : fetch_word Ubsan.M.loaded_segments (0x3b498 : word) = Some W_3b498.
Proof. vm_refl. Qed.
Lemma D_3b498 : decode_any W_3b498 = Some (OpImm ALU_ADD 10 10 463, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b49c : bv 32 := 0xb1e58593.
Lemma F_3b49c : fetch_word Ubsan.M.loaded_segments (0x3b49c : word) = Some W_3b49c.
Proof. vm_refl. Qed.
Lemma D_3b49c : decode_any W_3b49c = Some (OpImm ALU_ADD 11 11 2846, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4a0 : bv 32 := 0x0e00006f.
Lemma F_3b4a0 : fetch_word Ubsan.M.loaded_segments (0x3b4a0 : word) = Some W_3b4a0.
Proof. vm_refl. Qed.
Lemma D_3b4a0 : decode_any W_3b4a0 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4a4 : bv 32 := 0xf00007d3.
Lemma F_3b4a4 : fetch_word Ubsan.M.loaded_segments (0x3b4a4 : word) = Some W_3b4a4.
Proof. vm_refl. Qed.
Lemma D_3b4a4 : decode_any W_3b4a4 = Some (Fmv FMV_F_X FMT_S 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4a8 : bv 32 := 0xa0f48553.
Lemma F_3b4a8 : fetch_word Ubsan.M.loaded_segments (0x3b4a8 : word) = Some W_3b4a8.
Proof. vm_refl. Qed.
Lemma D_3b4a8 : decode_any W_3b4a8 = Some (Fcmp F_LE FMT_S 10 9 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4ac : bv 32 := 0x08051463.
Lemma F_3b4ac : fetch_word Ubsan.M.loaded_segments (0x3b4ac : word) = Some W_3b4ac.
Proof. vm_refl. Qed.
Lemma D_3b4ac : decode_any W_3b4ac = Some (Branch BC_NE 10 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4b0 : bv 32 := 0xa0f40553.
Lemma F_3b4b0 : fetch_word Ubsan.M.loaded_segments (0x3b4b0 : word) = Some W_3b4b0.
Proof. vm_refl. Qed.
Lemma D_3b4b0 : decode_any W_3b4b0 = Some (Fcmp F_LE FMT_S 10 8 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4b4 : bv 32 := 0x0a051463.
Lemma F_3b4b4 : fetch_word Ubsan.M.loaded_segments (0x3b4b4 : word) = Some W_3b4b4.
Proof. vm_refl. Qed.
Lemma D_3b4b4 : decode_any W_3b4b4 = Some (Branch BC_NE 10 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4b8 : bv 32 := 0xfffd7517.
Lemma F_3b4b8 : fetch_word Ubsan.M.loaded_segments (0x3b4b8 : word) = Some W_3b4b8.
Proof. vm_refl. Qed.
Lemma D_3b4b8 : decode_any W_3b4b8 = Some (Auipc 10 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4bc : bv 32 := 0x2f452707.
Lemma F_3b4bc : fetch_word Ubsan.M.loaded_segments (0x3b4bc : word) = Some W_3b4bc.
Proof. vm_refl. Qed.
Lemma D_3b4bc : decode_any W_3b4bc = Some (FLoad FMT_S 14 10 756, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4c0 : bv 32 := 0x0094f7d3.
Lemma F_3b4c0 : fetch_word Ubsan.M.loaded_segments (0x3b4c0 : word) = Some W_3b4c0.
Proof. vm_refl. Qed.
Lemma D_3b4c0 : decode_any W_3b4c0 = Some (Fari F_ADD FMT_S 15 9 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4c4 : bv 32 := 0xa0f71553.
Lemma F_3b4c4 : fetch_word Ubsan.M.loaded_segments (0x3b4c4 : word) = Some W_3b4c4.
Proof. vm_refl. Qed.
Lemma D_3b4c4 : decode_any W_3b4c4 = Some (Fcmp F_LT FMT_S 10 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4c8 : bv 32 := 0x0e050c63.
Lemma F_3b4c8 : fetch_word Ubsan.M.loaded_segments (0x3b4c8 : word) = Some W_3b4c8.
Proof. vm_refl. Qed.
Lemma D_3b4c8 : decode_any W_3b4c8 = Some (Branch BC_EQ 10 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4cc : bv 32 := 0x4f000537.
Lemma F_3b4cc : fetch_word Ubsan.M.loaded_segments (0x3b4cc : word) = Some W_3b4cc.
Proof. vm_refl. Qed.
Lemma D_3b4cc : decode_any W_3b4cc = Some (Lui 10 323584, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4d0 : bv 32 := 0xf0050753.
Lemma F_3b4d0 : fetch_word Ubsan.M.loaded_segments (0x3b4d0 : word) = Some W_3b4d0.
Proof. vm_refl. Qed.
Lemma D_3b4d0 : decode_any W_3b4d0 = Some (Fmv FMV_F_X FMT_S 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4d4 : bv 32 := 0xa0e79553.
Lemma F_3b4d4 : fetch_word Ubsan.M.loaded_segments (0x3b4d4 : word) = Some W_3b4d4.
Proof. vm_refl. Qed.
Lemma D_3b4d4 : decode_any W_3b4d4 = Some (Fcmp F_LT FMT_S 10 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4d8 : bv 32 := 0x0e050463.
Lemma F_3b4d8 : fetch_word Ubsan.M.loaded_segments (0x3b4d8 : word) = Some W_3b4d8.
Proof. vm_refl. Qed.
Lemma D_3b4d8 : decode_any W_3b4d8 = Some (Branch BC_EQ 10 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4dc : bv 32 := 0xc0079553.
Lemma F_3b4dc : fetch_word Ubsan.M.loaded_segments (0x3b4dc : word) = Some W_3b4dc.
Proof. vm_refl. Qed.
Lemma D_3b4dc : decode_any W_3b4dc = Some (Fcvt FC_W FC_S 10 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4e0 : bv 32 := 0x3f8005b7.
Lemma F_3b4e0 : fetch_word Ubsan.M.loaded_segments (0x3b4e0 : word) = Some W_3b4e0.
Proof. vm_refl. Qed.
Lemma D_3b4e0 : decode_any W_3b4e0 = Some (Lui 11 260096, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4e4 : bv 32 := 0xf00585d3.
Lemma F_3b4e4 : fetch_word Ubsan.M.loaded_segments (0x3b4e4 : word) = Some W_3b4e4.
Proof. vm_refl. Qed.
Lemma D_3b4e4 : decode_any W_3b4e4 = Some (Fmv FMV_F_X FMT_S 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4e8 : bv 32 := 0x00050593.
Lemma F_3b4e8 : fetch_word Ubsan.M.loaded_segments (0x3b4e8 : word) = Some W_3b4e8.
Proof. vm_refl. Qed.
Lemma D_3b4e8 : decode_any W_3b4e8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4ec : bv 32 := 0x20948553.
Lemma F_3b4ec : fetch_word Ubsan.M.loaded_segments (0x3b4ec : word) = Some W_3b4ec.
Proof. vm_refl. Qed.
Lemma D_3b4ec : decode_any W_3b4ec = Some (Fsgnj F_SGNJ FMT_S 10 9 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4f0 : bv 32 := 0xbbdfd0ef.
Lemma F_3b4f0 : fetch_word Ubsan.M.loaded_segments (0x3b4f0 : word) = Some W_3b4f0.
Proof. vm_refl. Qed.
Lemma D_3b4f0 : decode_any W_3b4f0 = Some (Jal 1 2087868, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4f4 : bv 32 := 0x00050493.
Lemma F_3b4f4 : fetch_word Ubsan.M.loaded_segments (0x3b4f4 : word) = Some W_3b4f4.
Proof. vm_refl. Qed.
Lemma D_3b4f4 : decode_any W_3b4f4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4f8 : bv 32 := 0x00a13823.
Lemma F_3b4f8 : fetch_word Ubsan.M.loaded_segments (0x3b4f8 : word) = Some W_3b4f8.
Proof. vm_refl. Qed.
Lemma D_3b4f8 : decode_any W_3b4f8 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b4fc : bv 32 := 0x20840553.
Lemma F_3b4fc : fetch_word Ubsan.M.loaded_segments (0x3b4fc : word) = Some W_3b4fc.
Proof. vm_refl. Qed.
Lemma D_3b4fc : decode_any W_3b4fc = Some (Fsgnj F_SGNJ FMT_S 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b500 : bv 32 := 0x0c4000ef.
Lemma F_3b500 : fetch_word Ubsan.M.loaded_segments (0x3b500 : word) = Some W_3b500.
Proof. vm_refl. Qed.
Lemma D_3b500 : decode_any W_3b500 = Some (Jal 1 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b504 : bv 32 := 0x00050613.
Lemma F_3b504 : fetch_word Ubsan.M.loaded_segments (0x3b504 : word) = Some W_3b504.
Proof. vm_refl. Qed.
Lemma D_3b504 : decode_any W_3b504 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b508 : bv 32 := 0x00a13423.
Lemma F_3b508 : fetch_word Ubsan.M.loaded_segments (0x3b508 : word) = Some W_3b508.
Proof. vm_refl. Qed.
Lemma D_3b508 : decode_any W_3b508 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b50c : bv 32 := 0x00040513.
Lemma F_3b50c : fetch_word Ubsan.M.loaded_segments (0x3b50c : word) = Some W_3b50c.
Proof. vm_refl. Qed.
Lemma D_3b50c : decode_any W_3b50c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b510 : bv 32 := 0x00048593.
Lemma F_3b510 : fetch_word Ubsan.M.loaded_segments (0x3b510 : word) = Some W_3b510.
Proof. vm_refl. Qed.
Lemma D_3b510 : decode_any W_3b510 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b514 : bv 32 := 0xe44ff0ef.
Lemma F_3b514 : fetch_word Ubsan.M.loaded_segments (0x3b514 : word) = Some W_3b514.
Proof. vm_refl. Qed.
Lemma D_3b514 : decode_any W_3b514 = Some (Jal 1 2094660, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b518 : bv 32 := 0x00050413.
Lemma F_3b518 : fetch_word Ubsan.M.loaded_segments (0x3b518 : word) = Some W_3b518.
Proof. vm_refl. Qed.
Lemma D_3b518 : decode_any W_3b518 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b51c : bv 32 := 0x01010513.
Lemma F_3b51c : fetch_word Ubsan.M.loaded_segments (0x3b51c : word) = Some W_3b51c.
Proof. vm_refl. Qed.
Lemma D_3b51c : decode_any W_3b51c = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b520 : bv 32 := 0x850fd0ef.
Lemma F_3b520 : fetch_word Ubsan.M.loaded_segments (0x3b520 : word) = Some W_3b520.
Proof. vm_refl. Qed.
Lemma D_3b520 : decode_any W_3b520 = Some (Jal 1 2084944, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b524 : bv 32 := 0x00810513.
Lemma F_3b524 : fetch_word Ubsan.M.loaded_segments (0x3b524 : word) = Some W_3b524.
Proof. vm_refl. Qed.
Lemma D_3b524 : decode_any W_3b524 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b528 : bv 32 := 0x848fd0ef.
Lemma F_3b528 : fetch_word Ubsan.M.loaded_segments (0x3b528 : word) = Some W_3b528.
Proof. vm_refl. Qed.
Lemma D_3b528 : decode_any W_3b528 = Some (Jal 1 2084936, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b52c : bv 32 := 0x00040513.
Lemma F_3b52c : fetch_word Ubsan.M.loaded_segments (0x3b52c : word) = Some W_3b52c.
Proof. vm_refl. Qed.
Lemma D_3b52c : decode_any W_3b52c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b530 : bv 32 := 0x0740006f.
Lemma F_3b530 : fetch_word Ubsan.M.loaded_segments (0x3b530 : word) = Some W_3b530.
Proof. vm_refl. Qed.
Lemma D_3b530 : decode_any W_3b530 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b534 : bv 32 := 0x0000a517.
Lemma F_3b534 : fetch_word Ubsan.M.loaded_segments (0x3b534 : word) = Some W_3b534.
Proof. vm_refl. Qed.
Lemma D_3b534 : decode_any W_3b534 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b538 : bv 32 := 0x96453503.
Lemma F_3b538 : fetch_word Ubsan.M.loaded_segments (0x3b538 : word) = Some W_3b538.
Proof. vm_refl. Qed.
Lemma D_3b538 : decode_any W_3b538 = Some (Load SZ8 true 10 10 2404, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b53c : bv 32 := 0x00052503.
Lemma F_3b53c : fetch_word Ubsan.M.loaded_segments (0x3b53c : word) = Some W_3b53c.
Proof. vm_refl. Qed.
Lemma D_3b53c : decode_any W_3b53c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b540 : bv 32 := 0x00500593.
Lemma F_3b540 : fetch_word Ubsan.M.loaded_segments (0x3b540 : word) = Some W_3b540.
Proof. vm_refl. Qed.
Lemma D_3b540 : decode_any W_3b540 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b544 : bv 32 := 0x04a5ce63.
Lemma F_3b544 : fetch_word Ubsan.M.loaded_segments (0x3b544 : word) = Some W_3b544.
Proof. vm_refl. Qed.
Lemma D_3b544 : decode_any W_3b544 = Some (Branch BC_LT 11 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b548 : bv 32 := 0xfffd6517.
Lemma F_3b548 : fetch_word Ubsan.M.loaded_segments (0x3b548 : word) = Some W_3b548.
Proof. vm_refl. Qed.
Lemma D_3b548 : decode_any W_3b548 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b54c : bv 32 := 0xfffd7597.
Lemma F_3b54c : fetch_word Ubsan.M.loaded_segments (0x3b54c : word) = Some W_3b54c.
Proof. vm_refl. Qed.
Lemma D_3b54c : decode_any W_3b54c = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b550 : bv 32 := 0xa6e50513.
Lemma F_3b550 : fetch_word Ubsan.M.loaded_segments (0x3b550 : word) = Some W_3b550.
Proof. vm_refl. Qed.
Lemma D_3b550 : decode_any W_3b550 = Some (OpImm ALU_ADD 10 10 2670, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b554 : bv 32 := 0xa6658593.
Lemma F_3b554 : fetch_word Ubsan.M.loaded_segments (0x3b554 : word) = Some W_3b554.
Proof. vm_refl. Qed.
Lemma D_3b554 : decode_any W_3b554 = Some (OpImm ALU_ADD 11 11 2662, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b558 : bv 32 := 0x0280006f.
Lemma F_3b558 : fetch_word Ubsan.M.loaded_segments (0x3b558 : word) = Some W_3b558.
Proof. vm_refl. Qed.
Lemma D_3b558 : decode_any W_3b558 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b55c : bv 32 := 0x0000a517.
Lemma F_3b55c : fetch_word Ubsan.M.loaded_segments (0x3b55c : word) = Some W_3b55c.
Proof. vm_refl. Qed.
Lemma D_3b55c : decode_any W_3b55c = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b560 : bv 32 := 0x93c53503.
Lemma F_3b560 : fetch_word Ubsan.M.loaded_segments (0x3b560 : word) = Some W_3b560.
Proof. vm_refl. Qed.
Lemma D_3b560 : decode_any W_3b560 = Some (Load SZ8 true 10 10 2364, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b564 : bv 32 := 0x00052503.
Lemma F_3b564 : fetch_word Ubsan.M.loaded_segments (0x3b564 : word) = Some W_3b564.
Proof. vm_refl. Qed.
Lemma D_3b564 : decode_any W_3b564 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b568 : bv 32 := 0x00500593.
Lemma F_3b568 : fetch_word Ubsan.M.loaded_segments (0x3b568 : word) = Some W_3b568.
Proof. vm_refl. Qed.
Lemma D_3b568 : decode_any W_3b568 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b56c : bv 32 := 0x02a5ca63.
Lemma F_3b56c : fetch_word Ubsan.M.loaded_segments (0x3b56c : word) = Some W_3b56c.
Proof. vm_refl. Qed.
Lemma D_3b56c : decode_any W_3b56c = Some (Branch BC_LT 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b570 : bv 32 := 0xfffd7517.
Lemma F_3b570 : fetch_word Ubsan.M.loaded_segments (0x3b570 : word) = Some W_3b570.
Proof. vm_refl. Qed.
Lemma D_3b570 : decode_any W_3b570 = Some (Auipc 10 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b574 : bv 32 := 0xfffd7597.
Lemma F_3b574 : fetch_word Ubsan.M.loaded_segments (0x3b574 : word) = Some W_3b574.
Proof. vm_refl. Qed.
Lemma D_3b574 : decode_any W_3b574 = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b578 : bv 32 := 0xb8450513.
Lemma F_3b578 : fetch_word Ubsan.M.loaded_segments (0x3b578 : word) = Some W_3b578.
Proof. vm_refl. Qed.
Lemma D_3b578 : decode_any W_3b578 = Some (OpImm ALU_ADD 10 10 2948, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b57c : bv 32 := 0xa3e58593.
Lemma F_3b57c : fetch_word Ubsan.M.loaded_segments (0x3b57c : word) = Some W_3b57c.
Proof. vm_refl. Qed.
Lemma D_3b57c : decode_any W_3b57c = Some (OpImm ALU_ADD 11 11 2622, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b580 : bv 32 := 0x00000613.
Lemma F_3b580 : fetch_word Ubsan.M.loaded_segments (0x3b580 : word) = Some W_3b580.
Proof. vm_refl. Qed.
Lemma D_3b580 : decode_any W_3b580 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b584 : bv 32 := 0x03813083.
Lemma F_3b584 : fetch_word Ubsan.M.loaded_segments (0x3b584 : word) = Some W_3b584.
Proof. vm_refl. Qed.
Lemma D_3b584 : decode_any W_3b584 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b588 : bv 32 := 0x03013403.
Lemma F_3b588 : fetch_word Ubsan.M.loaded_segments (0x3b588 : word) = Some W_3b588.
Proof. vm_refl. Qed.
Lemma D_3b588 : decode_any W_3b588 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b58c : bv 32 := 0x02813483.
Lemma F_3b58c : fetch_word Ubsan.M.loaded_segments (0x3b58c : word) = Some W_3b58c.
Proof. vm_refl. Qed.
Lemma D_3b58c : decode_any W_3b58c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b590 : bv 32 := 0x02013407.
Lemma F_3b590 : fetch_word Ubsan.M.loaded_segments (0x3b590 : word) = Some W_3b590.
Proof. vm_refl. Qed.
Lemma D_3b590 : decode_any W_3b590 = Some (FLoad FMT_D 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b594 : bv 32 := 0x01813487.
Lemma F_3b594 : fetch_word Ubsan.M.loaded_segments (0x3b594 : word) = Some W_3b594.
Proof. vm_refl. Qed.
Lemma D_3b594 : decode_any W_3b594 = Some (FLoad FMT_D 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b598 : bv 32 := 0x04010113.
Lemma F_3b598 : fetch_word Ubsan.M.loaded_segments (0x3b598 : word) = Some W_3b598.
Proof. vm_refl. Qed.
Lemma D_3b598 : decode_any W_3b598 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b59c : bv 32 := 0x929dc06f.
Lemma F_3b59c : fetch_word Ubsan.M.loaded_segments (0x3b59c : word) = Some W_3b59c.
Proof. vm_refl. Qed.
Lemma D_3b59c : decode_any W_3b59c = Some (Jal 0 1952040, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5a0 : bv 32 := 0x00000513.
Lemma F_3b5a0 : fetch_word Ubsan.M.loaded_segments (0x3b5a0 : word) = Some W_3b5a0.
Proof. vm_refl. Qed.
Lemma D_3b5a0 : decode_any W_3b5a0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5a4 : bv 32 := 0x03813083.
Lemma F_3b5a4 : fetch_word Ubsan.M.loaded_segments (0x3b5a4 : word) = Some W_3b5a4.
Proof. vm_refl. Qed.
Lemma D_3b5a4 : decode_any W_3b5a4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5a8 : bv 32 := 0x03013403.
Lemma F_3b5a8 : fetch_word Ubsan.M.loaded_segments (0x3b5a8 : word) = Some W_3b5a8.
Proof. vm_refl. Qed.
Lemma D_3b5a8 : decode_any W_3b5a8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5ac : bv 32 := 0x02813483.
Lemma F_3b5ac : fetch_word Ubsan.M.loaded_segments (0x3b5ac : word) = Some W_3b5ac.
Proof. vm_refl. Qed.
Lemma D_3b5ac : decode_any W_3b5ac = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5b0 : bv 32 := 0x02013407.
Lemma F_3b5b0 : fetch_word Ubsan.M.loaded_segments (0x3b5b0 : word) = Some W_3b5b0.
Proof. vm_refl. Qed.
Lemma D_3b5b0 : decode_any W_3b5b0 = Some (FLoad FMT_D 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5b4 : bv 32 := 0x01813487.
Lemma F_3b5b4 : fetch_word Ubsan.M.loaded_segments (0x3b5b4 : word) = Some W_3b5b4.
Proof. vm_refl. Qed.
Lemma D_3b5b4 : decode_any W_3b5b4 = Some (FLoad FMT_D 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5b8 : bv 32 := 0x04010113.
Lemma F_3b5b8 : fetch_word Ubsan.M.loaded_segments (0x3b5b8 : word) = Some W_3b5b8.
Proof. vm_refl. Qed.
Lemma D_3b5b8 : decode_any W_3b5b8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5bc : bv 32 := 0x00008067.
Lemma F_3b5bc : fetch_word Ubsan.M.loaded_segments (0x3b5bc : word) = Some W_3b5bc.
Proof. vm_refl. Qed.
Lemma D_3b5bc : decode_any W_3b5bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3b5c0 : bv 32 := 0xc0001073.
Lemma F_3b5c0 : fetch_word Ubsan.M.loaded_segments (0x3b5c0 : word) = Some W_3b5c0.
Proof. vm_refl. Qed.
Lemma D_3b5c0 : decode_any W_3b5c0 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
