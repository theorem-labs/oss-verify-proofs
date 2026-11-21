(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No the author licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1c560 : bv 32 := 0xff010113.
Lemma F_1c560 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c63c : word) = Some W_1c560.
Proof. vm_refl. Qed.
Lemma D_1c560 : decode_any W_1c560 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c564 : bv 32 := 0x00113423.
Lemma F_1c564 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c640 : word) = Some W_1c564.
Proof. vm_refl. Qed.
Lemma D_1c564 : decode_any W_1c564 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c568 : bv 32 := 0x00813023.
Lemma F_1c568 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c644 : word) = Some W_1c568.
Proof. vm_refl. Qed.
Lemma D_1c568 : decode_any W_1c568 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c56c : bv 32 := 0x198000ef.
Lemma F_1c56c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c648 : word) = Some W_1c56c.
Proof. vm_refl. Qed.
Lemma D_1c56c : decode_any W_1c56c = Some (Jal 1 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c570 : bv 32 := 0x00053403.
Lemma F_1c570 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c64c : word) = Some W_1c570.
Proof. vm_refl. Qed.
Lemma D_1c570 : decode_any W_1c570 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c574 : bv 32 := 0x12041663.
Lemma F_1c574 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c650 : word) = Some W_1c574.
Proof. vm_refl. Qed.
Lemma D_1c574 : decode_any W_1c574 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c578 : bv 32 := 0x00078517.
Lemma F_1c578 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c654 : word) = Some W_1c578.
Proof. vm_refl. Qed.
Lemma D_1c578 : decode_any W_1c578 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c57c : bv 32 := 0x29453403.
Lemma F_1c57c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c658 : word) = Some W_1c57c.
Proof. vm_refl. Qed.
Lemma D_1c57c : decode_any W_1c57c = Some (Load SZ8 true 8 10 660, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c580 : bv 32 := 0x04040a63.
Lemma F_1c580 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c65c : word) = Some W_1c580.
Proof. vm_refl. Qed.
Lemma D_1c580 : decode_any W_1c580 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5d4 : bv 32 := 0x00008517.
Lemma F_1c5d4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6b0 : word) = Some W_1c5d4.
Proof. vm_refl. Qed.
Lemma D_1c5d4 : decode_any W_1c5d4 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5d8 : bv 32 := 0xa2853403.
Lemma F_1c5d8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6b4 : word) = Some W_1c5d8.
Proof. vm_refl. Qed.
Lemma D_1c5d8 : decode_any W_1c5d8 = Some (Load SZ8 true 8 10 2600, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5dc : bv 32 := 0x04040a63.
Lemma F_1c5dc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6b8 : word) = Some W_1c5dc.
Proof. vm_refl. Qed.
Lemma D_1c5dc : decode_any W_1c5dc = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5e0 : bv 32 := 0x08c42503.
Lemma F_1c5e0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6bc : word) = Some W_1c5e0.
Proof. vm_refl. Qed.
Lemma D_1c5e0 : decode_any W_1c5e0 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5e4 : bv 32 := 0x00054663.
Lemma F_1c5e4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6c0 : word) = Some W_1c5e4.
Proof. vm_refl. Qed.
Lemma D_1c5e4 : decode_any W_1c5e4 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5f0 : bv 32 := 0x02843503.
Lemma F_1c5f0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6cc : word) = Some W_1c5f0.
Proof. vm_refl. Qed.
Lemma D_1c5f0 : decode_any W_1c5f0 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5f4 : bv 32 := 0x03843583.
Lemma F_1c5f4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6d0 : word) = Some W_1c5f4.
Proof. vm_refl. Qed.
Lemma D_1c5f4 : decode_any W_1c5f4 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5f8 : bv 32 := 0x00b50c63.
Lemma F_1c5f8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6d4 : word) = Some W_1c5f8.
Proof. vm_refl. Qed.
Lemma D_1c5f8 : decode_any W_1c5f8 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c5fc : bv 32 := 0x04843683.
Lemma F_1c5fc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6d8 : word) = Some W_1c5fc.
Proof. vm_refl. Qed.
Lemma D_1c5fc : decode_any W_1c5fc = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c600 : bv 32 := 0x00040513.
Lemma F_1c600 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6dc : word) = Some W_1c600.
Proof. vm_refl. Qed.
Lemma D_1c600 : decode_any W_1c600 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c604 : bv 32 := 0x00000593.
Lemma F_1c604 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6e0 : word) = Some W_1c604.
Proof. vm_refl. Qed.
Lemma D_1c604 : decode_any W_1c604 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c608 : bv 32 := 0x00000613.
Lemma F_1c608 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6e4 : word) = Some W_1c608.
Proof. vm_refl. Qed.
Lemma D_1c608 : decode_any W_1c608 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c60c : bv 32 := 0x000680e7.
Lemma F_1c60c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6e8 : word) = Some W_1c60c.
Proof. vm_refl. Qed.
Lemma D_1c60c : decode_any W_1c60c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c610 : bv 32 := 0x00843503.
Lemma F_1c610 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6ec : word) = Some W_1c610.
Proof. vm_refl. Qed.
Lemma D_1c610 : decode_any W_1c610 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c614 : bv 32 := 0x01043583.
Lemma F_1c614 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6f0 : word) = Some W_1c614.
Proof. vm_refl. Qed.
Lemma D_1c614 : decode_any W_1c614 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c618 : bv 32 := 0x00b50c63.
Lemma F_1c618 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c6f4 : word) = Some W_1c618.
Proof. vm_refl. Qed.
Lemma D_1c618 : decode_any W_1c618 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c630 : bv 32 := 0x00008517.
Lemma F_1c630 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c70c : word) = Some W_1c630.
Proof. vm_refl. Qed.
Lemma D_1c630 : decode_any W_1c630 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c634 : bv 32 := 0x8dc53403.
Lemma F_1c634 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c710 : word) = Some W_1c634.
Proof. vm_refl. Qed.
Lemma D_1c634 : decode_any W_1c634 = Some (Load SZ8 true 8 10 2268, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c638 : bv 32 := 0x0a040e63.
Lemma F_1c638 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c714 : word) = Some W_1c638.
Proof. vm_refl. Qed.
Lemma D_1c638 : decode_any W_1c638 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c63c : bv 32 := 0x08c42503.
Lemma F_1c63c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c718 : word) = Some W_1c63c.
Proof. vm_refl. Qed.
Lemma D_1c63c : decode_any W_1c63c = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c640 : bv 32 := 0x00054663.
Lemma F_1c640 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c71c : word) = Some W_1c640.
Proof. vm_refl. Qed.
Lemma D_1c640 : decode_any W_1c640 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c64c : bv 32 := 0x02843503.
Lemma F_1c64c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c728 : word) = Some W_1c64c.
Proof. vm_refl. Qed.
Lemma D_1c64c : decode_any W_1c64c = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c650 : bv 32 := 0x03843583.
Lemma F_1c650 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c72c : word) = Some W_1c650.
Proof. vm_refl. Qed.
Lemma D_1c650 : decode_any W_1c650 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c654 : bv 32 := 0x00b50c63.
Lemma F_1c654 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c730 : word) = Some W_1c654.
Proof. vm_refl. Qed.
Lemma D_1c654 : decode_any W_1c654 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c66c : bv 32 := 0x00843503.
Lemma F_1c66c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c748 : word) = Some W_1c66c.
Proof. vm_refl. Qed.
Lemma D_1c66c : decode_any W_1c66c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c670 : bv 32 := 0x01043583.
Lemma F_1c670 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c74c : word) = Some W_1c670.
Proof. vm_refl. Qed.
Lemma D_1c670 : decode_any W_1c670 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c674 : bv 32 := 0x08b50063.
Lemma F_1c674 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c750 : word) = Some W_1c674.
Proof. vm_refl. Qed.
Lemma D_1c674 : decode_any W_1c674 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6f4 : bv 32 := 0x00813083.
Lemma F_1c6f4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7d0 : word) = Some W_1c6f4.
Proof. vm_refl. Qed.
Lemma D_1c6f4 : decode_any W_1c6f4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6f8 : bv 32 := 0x00013403.
Lemma F_1c6f8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7d4 : word) = Some W_1c6f8.
Proof. vm_refl. Qed.
Lemma D_1c6f8 : decode_any W_1c6f8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c6fc : bv 32 := 0x01010113.
Lemma F_1c6fc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7d8 : word) = Some W_1c6fc.
Proof. vm_refl. Qed.
Lemma D_1c6fc : decode_any W_1c6fc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c700 : bv 32 := 0x00008067.
Lemma F_1c700 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7dc : word) = Some W_1c700.
Proof. vm_refl. Qed.
Lemma D_1c700 : decode_any W_1c700 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c704 : bv 32 := 0xff010113.
Lemma F_1c704 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7e0 : word) = Some W_1c704.
Proof. vm_refl. Qed.
Lemma D_1c704 : decode_any W_1c704 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c708 : bv 32 := 0x00113423.
Lemma F_1c708 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7e4 : word) = Some W_1c708.
Proof. vm_refl. Qed.
Lemma D_1c708 : decode_any W_1c708 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c70c : bv 32 := 0x00813023.
Lemma F_1c70c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7e8 : word) = Some W_1c70c.
Proof. vm_refl. Qed.
Lemma D_1c70c : decode_any W_1c70c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c710 : bv 32 := 0x00078517.
Lemma F_1c710 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7ec : word) = Some W_1c710.
Proof. vm_refl. Qed.
Lemma D_1c710 : decode_any W_1c710 = Some (Auipc 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c714 : bv 32 := 0x10450413.
Lemma F_1c714 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7f0 : word) = Some W_1c714.
Proof. vm_refl. Qed.
Lemma D_1c714 : decode_any W_1c714 = Some (OpImm ALU_ADD 8 10 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c718 : bv 32 := 0x00040513.
Lemma F_1c718 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7f4 : word) = Some W_1c718.
Proof. vm_refl. Qed.
Lemma D_1c718 : decode_any W_1c718 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c71c : bv 32 := 0x258050ef.
Lemma F_1c71c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7f8 : word) = Some W_1c71c.
Proof. vm_refl. Qed.
Lemma D_1c71c : decode_any W_1c71c = Some (Jal 1 21080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c720 : bv 32 := 0x00840513.
Lemma F_1c720 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c7fc : word) = Some W_1c720.
Proof. vm_refl. Qed.
Lemma D_1c720 : decode_any W_1c720 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c724 : bv 32 := 0x00813083.
Lemma F_1c724 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c800 : word) = Some W_1c724.
Proof. vm_refl. Qed.
Lemma D_1c724 : decode_any W_1c724 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c728 : bv 32 := 0x00013403.
Lemma F_1c728 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c804 : word) = Some W_1c728.
Proof. vm_refl. Qed.
Lemma D_1c728 : decode_any W_1c728 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c72c : bv 32 := 0x01010113.
Lemma F_1c72c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c808 : word) = Some W_1c72c.
Proof. vm_refl. Qed.
Lemma D_1c72c : decode_any W_1c72c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c730 : bv 32 := 0x00008067.
Lemma F_1c730 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c80c : word) = Some W_1c730.
Proof. vm_refl. Qed.
Lemma D_1c730 : decode_any W_1c730 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c740 : bv 32 := 0x00008067.
Lemma F_1c740 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c81c : word) = Some W_1c740.
Proof. vm_refl. Qed.
Lemma D_1c740 : decode_any W_1c740 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c770 : bv 32 := 0xf9010113.
Lemma F_1c770 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c84c : word) = Some W_1c770.
Proof. vm_refl. Qed.
Lemma D_1c770 : decode_any W_1c770 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c774 : bv 32 := 0x06113423.
Lemma F_1c774 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c850 : word) = Some W_1c774.
Proof. vm_refl. Qed.
Lemma D_1c774 : decode_any W_1c774 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c778 : bv 32 := 0x06813023.
Lemma F_1c778 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c854 : word) = Some W_1c778.
Proof. vm_refl. Qed.
Lemma D_1c778 : decode_any W_1c778 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c77c : bv 32 := 0x04913c23.
Lemma F_1c77c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c858 : word) = Some W_1c77c.
Proof. vm_refl. Qed.
Lemma D_1c77c : decode_any W_1c77c = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c780 : bv 32 := 0x05213823.
Lemma F_1c780 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c85c : word) = Some W_1c780.
Proof. vm_refl. Qed.
Lemma D_1c780 : decode_any W_1c780 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c784 : bv 32 := 0x05313423.
Lemma F_1c784 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c860 : word) = Some W_1c784.
Proof. vm_refl. Qed.
Lemma D_1c784 : decode_any W_1c784 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c788 : bv 32 := 0x05413023.
Lemma F_1c788 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c864 : word) = Some W_1c788.
Proof. vm_refl. Qed.
Lemma D_1c788 : decode_any W_1c788 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c78c : bv 32 := 0x03513c23.
Lemma F_1c78c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c868 : word) = Some W_1c78c.
Proof. vm_refl. Qed.
Lemma D_1c78c : decode_any W_1c78c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c790 : bv 32 := 0x03613823.
Lemma F_1c790 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c86c : word) = Some W_1c790.
Proof. vm_refl. Qed.
Lemma D_1c790 : decode_any W_1c790 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c794 : bv 32 := 0x00060413.
Lemma F_1c794 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c870 : word) = Some W_1c794.
Proof. vm_refl. Qed.
Lemma D_1c794 : decode_any W_1c794 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c798 : bv 32 := 0x00050493.
Lemma F_1c798 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c874 : word) = Some W_1c798.
Proof. vm_refl. Qed.
Lemma D_1c798 : decode_any W_1c798 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c79c : bv 32 := 0x00006517.
Lemma F_1c79c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c878 : word) = Some W_1c79c.
Proof. vm_refl. Qed.
Lemma D_1c79c : decode_any W_1c79c = Some (Auipc 10 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7a0 : bv 32 := 0x64853a83.
Lemma F_1c7a0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c87c : word) = Some W_1c7a0.
Proof. vm_refl. Qed.
Lemma D_1c7a0 : decode_any W_1c7a0 = Some (Load SZ8 true 21 10 1608, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7a4 : bv 32 := 0x000ab503.
Lemma F_1c7a4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c880 : word) = Some W_1c7a4.
Proof. vm_refl. Qed.
Lemma D_1c7a4 : decode_any W_1c7a4 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7a8 : bv 32 := 0x02a13423.
Lemma F_1c7a8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c884 : word) = Some W_1c7a8.
Proof. vm_refl. Qed.
Lemma D_1c7a8 : decode_any W_1c7a8 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7ac : bv 32 := 0x0284b503.
Lemma F_1c7ac : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c888 : word) = Some W_1c7ac.
Proof. vm_refl. Qed.
Lemma D_1c7ac : decode_any W_1c7ac = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7b0 : bv 32 := 0x0384b603.
Lemma F_1c7b0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c88c : word) = Some W_1c7b0.
Proof. vm_refl. Qed.
Lemma D_1c7b0 : decode_any W_1c7b0 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7b4 : bv 32 := 0x40c50b33.
Lemma F_1c7b4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c890 : word) = Some W_1c7b4.
Proof. vm_refl. Qed.
Lemma D_1c7b4 : decode_any W_1c7b4 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7b8 : bv 32 := 0x00c546b3.
Lemma F_1c7b8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c894 : word) = Some W_1c7b8.
Proof. vm_refl. Qed.
Lemma D_1c7b8 : decode_any W_1c7b8 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7bc : bv 32 := 0x00c13423.
Lemma F_1c7bc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c898 : word) = Some W_1c7bc.
Proof. vm_refl. Qed.
Lemma D_1c7bc : decode_any W_1c7bc = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7c0 : bv 32 := 0x01613823.
Lemma F_1c7c0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c89c : word) = Some W_1c7c0.
Proof. vm_refl. Qed.
Lemma D_1c7c0 : decode_any W_1c7c0 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7c4 : bv 32 := 0x00b13c23.
Lemma F_1c7c4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8a0 : word) = Some W_1c7c4.
Proof. vm_refl. Qed.
Lemma D_1c7c4 : decode_any W_1c7c4 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7c8 : bv 32 := 0x02813023.
Lemma F_1c7c8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8a4 : word) = Some W_1c7c8.
Proof. vm_refl. Qed.
Lemma D_1c7c8 : decode_any W_1c7c8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7cc : bv 32 := 0x008b0b33.
Lemma F_1c7cc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8a8 : word) = Some W_1c7cc.
Proof. vm_refl. Qed.
Lemma D_1c7cc : decode_any W_1c7cc = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7d0 : bv 32 := 0x00d03933.
Lemma F_1c7d0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8ac : word) = Some W_1c7d0.
Proof. vm_refl. Qed.
Lemma D_1c7d0 : decode_any W_1c7d0 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7d4 : bv 32 := 0x00c50663.
Lemma F_1c7d4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8b0 : word) = Some W_1c7d4.
Proof. vm_refl. Qed.
Lemma D_1c7d4 : decode_any W_1c7d4 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7d8 : bv 32 := 0x00810993.
Lemma F_1c7d8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8b4 : word) = Some W_1c7d8.
Proof. vm_refl. Qed.
Lemma D_1c7d8 : decode_any W_1c7d8 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7dc : bv 32 := 0x0080006f.
Lemma F_1c7dc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8b8 : word) = Some W_1c7dc.
Proof. vm_refl. Qed.
Lemma D_1c7dc : decode_any W_1c7dc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7e0 : bv 32 := 0x01810993.
Lemma F_1c7e0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8bc : word) = Some W_1c7e0.
Proof. vm_refl. Qed.
Lemma D_1c7e0 : decode_any W_1c7e0 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7e4 : bv 32 := 0x0784a503.
Lemma F_1c7e4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8c0 : word) = Some W_1c7e4.
Proof. vm_refl. Qed.
Lemma D_1c7e4 : decode_any W_1c7e4 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7e8 : bv 32 := 0x00190913.
Lemma F_1c7e8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8c4 : word) = Some W_1c7e8.
Proof. vm_refl. Qed.
Lemma D_1c7e8 : decode_any W_1c7e8 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7ec : bv 32 := 0x04200893.
Lemma F_1c7ec : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8c8 : word) = Some W_1c7ec.
Proof. vm_refl. Qed.
Lemma D_1c7ec : decode_any W_1c7ec = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7f0 : bv 32 := 0x00098593.
Lemma F_1c7f0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8cc : word) = Some W_1c7f0.
Proof. vm_refl. Qed.
Lemma D_1c7f0 : decode_any W_1c7f0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7f4 : bv 32 := 0x00090613.
Lemma F_1c7f4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8d0 : word) = Some W_1c7f4.
Proof. vm_refl. Qed.
Lemma D_1c7f4 : decode_any W_1c7f4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c7f8 : bv 32 := 0x00000073.
Lemma F_1c7f8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8d4 : word) = Some W_1c7f8.
Proof. vm_refl. Qed.
Lemma D_1c7f8 : decode_any W_1c7f8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1c7f8 : is_ecall W_1c7f8 = true.
Proof. reflexivity. Qed.

Definition W_1c7fc : bv 32 := 0xc81fd0ef.
Lemma F_1c7fc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8d8 : word) = Some W_1c7fc.
Proof. vm_refl. Qed.
Lemma D_1c7fc : decode_any W_1c7fc = Some (Jal 1 2088064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c800 : bv 32 := 0x09651863.
Lemma F_1c800 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8dc : word) = Some W_1c800.
Proof. vm_refl. Qed.
Lemma D_1c800 : decode_any W_1c800 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c804 : bv 32 := 0x0584b503.
Lemma F_1c804 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8e0 : word) = Some W_1c804.
Proof. vm_refl. Qed.
Lemma D_1c804 : decode_any W_1c804 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c808 : bv 32 := 0x0604b583.
Lemma F_1c808 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8e4 : word) = Some W_1c808.
Proof. vm_refl. Qed.
Lemma D_1c808 : decode_any W_1c808 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c80c : bv 32 := 0x00b505b3.
Lemma F_1c80c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8e8 : word) = Some W_1c80c.
Proof. vm_refl. Qed.
Lemma D_1c80c : decode_any W_1c80c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c810 : bv 32 := 0x02b4b023.
Lemma F_1c810 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8ec : word) = Some W_1c810.
Proof. vm_refl. Qed.
Lemma D_1c810 : decode_any W_1c810 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c814 : bv 32 := 0x02a4b423.
Lemma F_1c814 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8f0 : word) = Some W_1c814.
Proof. vm_refl. Qed.
Lemma D_1c814 : decode_any W_1c814 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c818 : bv 32 := 0x02a4bc23.
Lemma F_1c818 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8f4 : word) = Some W_1c818.
Proof. vm_refl. Qed.
Lemma D_1c818 : decode_any W_1c818 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c81c : bv 32 := 0x00040513.
Lemma F_1c81c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8f8 : word) = Some W_1c81c.
Proof. vm_refl. Qed.
Lemma D_1c81c : decode_any W_1c81c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c820 : bv 32 := 0x000ab583.
Lemma F_1c820 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c8fc : word) = Some W_1c820.
Proof. vm_refl. Qed.
Lemma D_1c820 : decode_any W_1c820 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c824 : bv 32 := 0x02813603.
Lemma F_1c824 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c900 : word) = Some W_1c824.
Proof. vm_refl. Qed.
Lemma D_1c824 : decode_any W_1c824 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c828 : bv 32 := 0x0cc59a63.
Lemma F_1c828 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c904 : word) = Some W_1c828.
Proof. vm_refl. Qed.
Lemma D_1c828 : decode_any W_1c828 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c82c : bv 32 := 0x06813083.
Lemma F_1c82c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c908 : word) = Some W_1c82c.
Proof. vm_refl. Qed.
Lemma D_1c82c : decode_any W_1c82c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c830 : bv 32 := 0x06013403.
Lemma F_1c830 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c90c : word) = Some W_1c830.
Proof. vm_refl. Qed.
Lemma D_1c830 : decode_any W_1c830 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c834 : bv 32 := 0x05813483.
Lemma F_1c834 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c910 : word) = Some W_1c834.
Proof. vm_refl. Qed.
Lemma D_1c834 : decode_any W_1c834 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c838 : bv 32 := 0x05013903.
Lemma F_1c838 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c914 : word) = Some W_1c838.
Proof. vm_refl. Qed.
Lemma D_1c838 : decode_any W_1c838 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c83c : bv 32 := 0x04813983.
Lemma F_1c83c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c918 : word) = Some W_1c83c.
Proof. vm_refl. Qed.
Lemma D_1c83c : decode_any W_1c83c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c840 : bv 32 := 0x04013a03.
Lemma F_1c840 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c91c : word) = Some W_1c840.
Proof. vm_refl. Qed.
Lemma D_1c840 : decode_any W_1c840 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c844 : bv 32 := 0x03813a83.
Lemma F_1c844 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c920 : word) = Some W_1c844.
Proof. vm_refl. Qed.
Lemma D_1c844 : decode_any W_1c844 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c848 : bv 32 := 0x03013b03.
Lemma F_1c848 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c924 : word) = Some W_1c848.
Proof. vm_refl. Qed.
Lemma D_1c848 : decode_any W_1c848 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c84c : bv 32 := 0x07010113.
Lemma F_1c84c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c928 : word) = Some W_1c84c.
Proof. vm_refl. Qed.
Lemma D_1c84c : decode_any W_1c84c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c850 : bv 32 := 0x00008067.
Lemma F_1c850 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c92c : word) = Some W_1c850.
Proof. vm_refl. Qed.
Lemma D_1c850 : decode_any W_1c850 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c854 : bv 32 := 0x00800713.
Lemma F_1c854 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c930 : word) = Some W_1c854.
Proof. vm_refl. Qed.
Lemma D_1c854 : decode_any W_1c854 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c858 : bv 32 := 0x000a0593.
Lemma F_1c858 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c934 : word) = Some W_1c858.
Proof. vm_refl. Qed.
Lemma D_1c858 : decode_any W_1c858 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c85c : bv 32 := 0x00e98733.
Lemma F_1c85c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c938 : word) = Some W_1c85c.
Proof. vm_refl. Qed.
Lemma D_1c85c : decode_any W_1c85c = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c860 : bv 32 := 0x00073783.
Lemma F_1c860 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c93c : word) = Some W_1c860.
Proof. vm_refl. Qed.
Lemma D_1c860 : decode_any W_1c860 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c864 : bv 32 := 0x40ab0b33.
Lemma F_1c864 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c940 : word) = Some W_1c864.
Proof. vm_refl. Qed.
Lemma D_1c864 : decode_any W_1c864 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c868 : bv 32 := 0x0784a503.
Lemma F_1c868 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c944 : word) = Some W_1c868.
Proof. vm_refl. Qed.
Lemma D_1c868 : decode_any W_1c868 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c86c : bv 32 := 0x40c9093b.
Lemma F_1c86c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c948 : word) = Some W_1c86c.
Proof. vm_refl. Qed.
Lemma D_1c86c : decode_any W_1c86c = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c870 : bv 32 := 0x40d787b3.
Lemma F_1c870 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c94c : word) = Some W_1c870.
Proof. vm_refl. Qed.
Lemma D_1c870 : decode_any W_1c870 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c874 : bv 32 := 0x00f73023.
Lemma F_1c874 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c950 : word) = Some W_1c874.
Proof. vm_refl. Qed.
Lemma D_1c874 : decode_any W_1c874 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c878 : bv 32 := 0x04200893.
Lemma F_1c878 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c954 : word) = Some W_1c878.
Proof. vm_refl. Qed.
Lemma D_1c878 : decode_any W_1c878 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c87c : bv 32 := 0x00090613.
Lemma F_1c87c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c958 : word) = Some W_1c87c.
Proof. vm_refl. Qed.
Lemma D_1c87c : decode_any W_1c87c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c880 : bv 32 := 0x00000073.
Lemma F_1c880 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c95c : word) = Some W_1c880.
Proof. vm_refl. Qed.
Lemma D_1c880 : decode_any W_1c880 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1c880 : is_ecall W_1c880 = true.
Proof. reflexivity. Qed.

Definition W_1c884 : bv 32 := 0xbf9fd0ef.
Lemma F_1c884 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c960 : word) = Some W_1c884.
Proof. vm_refl. Qed.
Lemma D_1c884 : decode_any W_1c884 = Some (Jal 1 2087928, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c888 : bv 32 := 0x000a0993.
Lemma F_1c888 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c964 : word) = Some W_1c888.
Proof. vm_refl. Qed.
Lemma D_1c888 : decode_any W_1c888 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c88c : bv 32 := 0xf7650ce3.
Lemma F_1c88c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c968 : word) = Some W_1c88c.
Proof. vm_refl. Qed.
Lemma D_1c88c : decode_any W_1c88c = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c890 : bv 32 := 0x02054c63.
Lemma F_1c890 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c96c : word) = Some W_1c890.
Proof. vm_refl. Qed.
Lemma D_1c890 : decode_any W_1c890 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c894 : bv 32 := 0x0089b583.
Lemma F_1c894 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c970 : word) = Some W_1c894.
Proof. vm_refl. Qed.
Lemma D_1c894 : decode_any W_1c894 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c898 : bv 32 := 0x00a5b633.
Lemma F_1c898 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c974 : word) = Some W_1c898.
Proof. vm_refl. Qed.
Lemma D_1c898 : decode_any W_1c898 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c89c : bv 32 := 0x00461a13.
Lemma F_1c89c : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c978 : word) = Some W_1c89c.
Proof. vm_refl. Qed.
Lemma D_1c89c : decode_any W_1c89c = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c8a0 : bv 32 := 0x01498a33.
Lemma F_1c8a0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c97c : word) = Some W_1c8a0.
Proof. vm_refl. Qed.
Lemma D_1c8a0 : decode_any W_1c8a0 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c8a4 : bv 32 := 0x000a3703.
Lemma F_1c8a4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c980 : word) = Some W_1c8a4.
Proof. vm_refl. Qed.
Lemma D_1c8a4 : decode_any W_1c8a4 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c8a8 : bv 32 := 0x40c006b3.
Lemma F_1c8a8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c984 : word) = Some W_1c8a8.
Proof. vm_refl. Qed.
Lemma D_1c8a8 : decode_any W_1c8a8 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c8ac : bv 32 := 0x00b6f6b3.
Lemma F_1c8ac : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c988 : word) = Some W_1c8ac.
Proof. vm_refl. Qed.
Lemma D_1c8ac : decode_any W_1c8ac = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c8b0 : bv 32 := 0x40d506b3.
Lemma F_1c8b0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c98c : word) = Some W_1c8b0.
Proof. vm_refl. Qed.
Lemma D_1c8b0 : decode_any W_1c8b0 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c8b4 : bv 32 := 0x00d70733.
Lemma F_1c8b4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c990 : word) = Some W_1c8b4.
Proof. vm_refl. Qed.
Lemma D_1c8b4 : decode_any W_1c8b4 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c8b8 : bv 32 := 0x00ea3023.
Lemma F_1c8b8 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c994 : word) = Some W_1c8b8.
Proof. vm_refl. Qed.
Lemma D_1c8b8 : decode_any W_1c8b8 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c8bc : bv 32 := 0xf8a5fce3.
Lemma F_1c8bc : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c998 : word) = Some W_1c8bc.
Proof. vm_refl. Qed.
Lemma D_1c8bc : decode_any W_1c8bc = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c8c0 : bv 32 := 0x01800713.
Lemma F_1c8c0 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c99c : word) = Some W_1c8c0.
Proof. vm_refl. Qed.
Lemma D_1c8c0 : decode_any W_1c8c0 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1c8c4 : bv 32 := 0xf95ff06f.
Lemma F_1c8c4 : fetch_word Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments (0x1c9a0 : word) = Some W_1c8c4.
Proof. vm_refl. Qed.
Lemma D_1c8c4 : decode_any W_1c8c4 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
