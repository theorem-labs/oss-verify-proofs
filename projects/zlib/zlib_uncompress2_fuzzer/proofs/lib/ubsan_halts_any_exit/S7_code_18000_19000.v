(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_187c8 : bv 32 := 0x00008067.
Lemma F_187c8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18904 : word) = Some W_187c8.
Proof. vm_refl. Qed.
Lemma D_187c8 : decode_any W_187c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_187cc : bv 32 := 0xe8010113.
Lemma F_187cc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18908 : word) = Some W_187cc.
Proof. vm_refl. Qed.
Lemma D_187cc : decode_any W_187cc = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_187d0 : bv 32 := 0x16113c23.
Lemma F_187d0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1890c : word) = Some W_187d0.
Proof. vm_refl. Qed.
Lemma D_187d0 : decode_any W_187d0 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_187d4 : bv 32 := 0x16813823.
Lemma F_187d4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18910 : word) = Some W_187d4.
Proof. vm_refl. Qed.
Lemma D_187d4 : decode_any W_187d4 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_187d8 : bv 32 := 0x16913423.
Lemma F_187d8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18914 : word) = Some W_187d8.
Proof. vm_refl. Qed.
Lemma D_187d8 : decode_any W_187d8 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_187dc : bv 32 := 0x17213023.
Lemma F_187dc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18918 : word) = Some W_187dc.
Proof. vm_refl. Qed.
Lemma D_187dc : decode_any W_187dc = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_187e0 : bv 32 := 0x00058413.
Lemma F_187e0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1891c : word) = Some W_187e0.
Proof. vm_refl. Qed.
Lemma D_187e0 : decode_any W_187e0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_187e4 : bv 32 := 0x00050493.
Lemma F_187e4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18920 : word) = Some W_187e4.
Proof. vm_refl. Qed.
Lemma D_187e4 : decode_any W_187e4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_187e8 : bv 32 := 0x03010513.
Lemma F_187e8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18924 : word) = Some W_187e8.
Proof. vm_refl. Qed.
Lemma D_187e8 : decode_any W_187e8 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_187ec : bv 32 := 0x13000613.
Lemma F_187ec : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18928 : word) = Some W_187ec.
Proof. vm_refl. Qed.
Lemma D_187ec : decode_any W_187ec = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_187f0 : bv 32 := 0x00000593.
Lemma F_187f0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1892c : word) = Some W_187f0.
Proof. vm_refl. Qed.
Lemma D_187f0 : decode_any W_187f0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_187f4 : bv 32 := 0x459070ef.
Lemma F_187f4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18930 : word) = Some W_187f4.
Proof. vm_refl. Qed.
Lemma D_187f4 : decode_any W_187f4 = Some (Jal 1 31832, 4%Z).
Proof. vm_refl. Qed.

Definition W_187f8 : bv 32 := 0x00009517.
Lemma F_187f8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18934 : word) = Some W_187f8.
Proof. vm_refl. Qed.
Lemma D_187f8 : decode_any W_187f8 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_187fc : bv 32 := 0x2a453503.
Lemma F_187fc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18938 : word) = Some W_187fc.
Proof. vm_refl. Qed.
Lemma D_187fc : decode_any W_187fc = Some (Load SZ8 true 10 10 676, 4%Z).
Proof. vm_refl. Qed.

Definition W_18800 : bv 32 := 0x00953023.
Lemma F_18800 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1893c : word) = Some W_18800.
Proof. vm_refl. Qed.
Lemma D_18800 : decode_any W_18800 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18804 : bv 32 := 0x0004b503.
Lemma F_18804 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18940 : word) = Some W_18804.
Proof. vm_refl. Qed.
Lemma D_18804 : decode_any W_18804 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18808 : bv 32 := 0x00848493.
Lemma F_18808 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18944 : word) = Some W_18808.
Proof. vm_refl. Qed.
Lemma D_18808 : decode_any W_18808 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1880c : bv 32 := 0xfe051ce3.
Lemma F_1880c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18948 : word) = Some W_1880c.
Proof. vm_refl. Qed.
Lemma D_1880c : decode_any W_1880c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_18810 : bv 32 := 0x0007b517.
Lemma F_18810 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1894c : word) = Some W_18810.
Proof. vm_refl. Qed.
Lemma D_18810 : decode_any W_18810 = Some (Auipc 10 123, 4%Z).
Proof. vm_refl. Qed.

Definition W_18814 : bv 32 := 0x8bc50913.
Lemma F_18814 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18950 : word) = Some W_18814.
Proof. vm_refl. Qed.
Lemma D_18814 : decode_any W_18814 = Some (OpImm ALU_ADD 18 10 2236, 4%Z).
Proof. vm_refl. Qed.

Definition W_18818 : bv 32 := 0x00993423.
Lemma F_18818 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18954 : word) = Some W_18818.
Proof. vm_refl. Qed.
Lemma D_18818 : decode_any W_18818 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1881c : bv 32 := 0x0004b583.
Lemma F_1881c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18958 : word) = Some W_1881c.
Proof. vm_refl. Qed.
Lemma D_1881c : decode_any W_1881c = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18820 : bv 32 := 0x04058c63.
Lemma F_18820 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1895c : word) = Some W_18820.
Proof. vm_refl. Qed.
Lemma D_18820 : decode_any W_18820 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_18824 : bv 32 := 0x01048493.
Lemma F_18824 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18960 : word) = Some W_18824.
Proof. vm_refl. Qed.
Lemma D_18824 : decode_any W_18824 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18828 : bv 32 := 0x02500513.
Lemma F_18828 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18964 : word) = Some W_18828.
Proof. vm_refl. Qed.
Lemma D_18828 : decode_any W_18828 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_1882c : bv 32 := 0x03010613.
Lemma F_1882c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18968 : word) = Some W_1882c.
Proof. vm_refl. Qed.
Lemma D_1882c : decode_any W_1882c = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18830 : bv 32 := 0x0100006f.
Lemma F_18830 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1896c : word) = Some W_18830.
Proof. vm_refl. Qed.
Lemma D_18830 : decode_any W_18830 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18834 : bv 32 := 0x0004b583.
Lemma F_18834 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18970 : word) = Some W_18834.
Proof. vm_refl. Qed.
Lemma D_18834 : decode_any W_18834 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18838 : bv 32 := 0x01048493.
Lemma F_18838 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18974 : word) = Some W_18838.
Proof. vm_refl. Qed.
Lemma D_18838 : decode_any W_18838 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1883c : bv 32 := 0x00058e63.
Lemma F_1883c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18978 : word) = Some W_1883c.
Proof. vm_refl. Qed.
Lemma D_1883c : decode_any W_1883c = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_18840 : bv 32 := 0xfeb56ae3.
Lemma F_18840 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1897c : word) = Some W_18840.
Proof. vm_refl. Qed.
Lemma D_18840 : decode_any W_18840 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_18844 : bv 32 := 0xff84b683.
Lemma F_18844 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18980 : word) = Some W_18844.
Proof. vm_refl. Qed.
Lemma D_18844 : decode_any W_18844 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_18848 : bv 32 := 0x00359593.
Lemma F_18848 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18984 : word) = Some W_18848.
Proof. vm_refl. Qed.
Lemma D_18848 : decode_any W_18848 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1884c : bv 32 := 0x00b605b3.
Lemma F_1884c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18988 : word) = Some W_1884c.
Proof. vm_refl. Qed.
Lemma D_1884c : decode_any W_1884c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18850 : bv 32 := 0x00d5b023.
Lemma F_18850 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1898c : word) = Some W_18850.
Proof. vm_refl. Qed.
Lemma D_18850 : decode_any W_18850 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18854 : bv 32 := 0xfe1ff06f.
Lemma F_18854 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18990 : word) = Some W_18854.
Proof. vm_refl. Qed.
Lemma D_18854 : decode_any W_18854 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_18858 : bv 32 := 0x0b013583.
Lemma F_18858 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18994 : word) = Some W_18858.
Proof. vm_refl. Qed.
Lemma D_18858 : decode_any W_18858 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_1885c : bv 32 := 0x13013503.
Lemma F_1885c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18998 : word) = Some W_1885c.
Proof. vm_refl. Qed.
Lemma D_1885c : decode_any W_1885c = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_18860 : bv 32 := 0x0007b617.
Lemma F_18860 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1899c : word) = Some W_18860.
Proof. vm_refl. Qed.
Lemma D_18860 : decode_any W_18860 = Some (Auipc 12 123, 4%Z).
Proof. vm_refl. Qed.

Definition W_18864 : bv 32 := 0x8cb63a23.
Lemma F_18864 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189a0 : word) = Some W_18864.
Proof. vm_refl. Qed.
Lemma D_18864 : decode_any W_18864 = Some (Store SZ8 12 11 2260, 4%Z).
Proof. vm_refl. Qed.

Definition W_18868 : bv 32 := 0x00050c63.
Lemma F_18868 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189a4 : word) = Some W_18868.
Proof. vm_refl. Qed.
Lemma D_18868 : decode_any W_18868 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1886c : bv 32 := 0x0007b597.
Lemma F_1886c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189a8 : word) = Some W_1886c.
Proof. vm_refl. Qed.
Lemma D_1886c : decode_any W_1886c = Some (Auipc 11 123, 4%Z).
Proof. vm_refl. Qed.

Definition W_18870 : bv 32 := 0x84a5b423.
Lemma F_18870 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189ac : word) = Some W_18870.
Proof. vm_refl. Qed.
Lemma D_18870 : decode_any W_18870 = Some (Store SZ8 11 10 2120, 4%Z).
Proof. vm_refl. Qed.

Definition W_18874 : bv 32 := 0x00c0006f.
Lemma F_18874 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189b0 : word) = Some W_18874.
Proof. vm_refl. Qed.
Lemma D_18874 : decode_any W_18874 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18878 : bv 32 := 0x0007b517.
Lemma F_18878 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189b4 : word) = Some W_18878.
Proof. vm_refl. Qed.
Lemma D_18878 : decode_any W_18878 = Some (Auipc 10 123, 4%Z).
Proof. vm_refl. Qed.

Definition W_1887c : bv 32 := 0x8a053e23.
Lemma F_1887c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189b8 : word) = Some W_1887c.
Proof. vm_refl. Qed.
Lemma D_1887c : decode_any W_1887c = Some (Store SZ8 10 0 2236, 4%Z).
Proof. vm_refl. Qed.

Definition W_18880 : bv 32 := 0x06013503.
Lemma F_18880 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189bc : word) = Some W_18880.
Proof. vm_refl. Qed.
Lemma D_18880 : decode_any W_18880 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_18884 : bv 32 := 0x02a93823.
Lemma F_18884 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189c0 : word) = Some W_18884.
Proof. vm_refl. Qed.
Lemma D_18884 : decode_any W_18884 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18888 : bv 32 := 0x00041463.
Lemma F_18888 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189c4 : word) = Some W_18888.
Proof. vm_refl. Qed.
Lemma D_18888 : decode_any W_18888 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1888c : bv 32 := 0x12813403.
Lemma F_1888c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189c8 : word) = Some W_1888c.
Proof. vm_refl. Qed.
Lemma D_1888c : decode_any W_1888c = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_18890 : bv 32 := 0x00041663.
Lemma F_18890 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189cc : word) = Some W_18890.
Proof. vm_refl. Qed.
Lemma D_18890 : decode_any W_18890 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18894 : bv 32 := 0xffff8517.
Lemma F_18894 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189d0 : word) = Some W_18894.
Proof. vm_refl. Qed.
Lemma D_18894 : decode_any W_18894 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18898 : bv 32 := 0x96850413.
Lemma F_18898 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189d4 : word) = Some W_18898.
Proof. vm_refl. Qed.
Lemma D_18898 : decode_any W_18898 = Some (OpImm ALU_ADD 8 10 2408, 4%Z).
Proof. vm_refl. Qed.

Definition W_1889c : bv 32 := 0x00009517.
Lemma F_1889c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189d8 : word) = Some W_1889c.
Proof. vm_refl. Qed.
Lemma D_1889c : decode_any W_1889c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_188a0 : bv 32 := 0x20853583.
Lemma F_188a0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189dc : word) = Some W_188a0.
Proof. vm_refl. Qed.
Lemma D_188a0 : decode_any W_188a0 = Some (Load SZ8 true 11 10 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_188a4 : bv 32 := 0x00009517.
Lemma F_188a4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189e0 : word) = Some W_188a4.
Proof. vm_refl. Qed.
Lemma D_188a4 : decode_any W_188a4 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_188a8 : bv 32 := 0x20853503.
Lemma F_188a8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189e4 : word) = Some W_188a8.
Proof. vm_refl. Qed.
Lemma D_188a8 : decode_any W_188a8 = Some (Load SZ8 true 10 10 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_188ac : bv 32 := 0x0085b023.
Lemma F_188ac : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189e8 : word) = Some W_188ac.
Proof. vm_refl. Qed.
Lemma D_188ac : decode_any W_188ac = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_188b0 : bv 32 := 0x00140593.
Lemma F_188b0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189ec : word) = Some W_188b0.
Proof. vm_refl. Qed.
Lemma D_188b0 : decode_any W_188b0 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_188b4 : bv 32 := 0x00853023.
Lemma F_188b4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189f0 : word) = Some W_188b4.
Proof. vm_refl. Qed.
Lemma D_188b4 : decode_any W_188b4 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_188b8 : bv 32 := 0x02f00613.
Lemma F_188b8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189f4 : word) = Some W_188b8.
Proof. vm_refl. Qed.
Lemma D_188b8 : decode_any W_188b8 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_188bc : bv 32 := 0x00c0006f.
Lemma F_188bc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189f8 : word) = Some W_188bc.
Proof. vm_refl. Qed.
Lemma D_188bc : decode_any W_188bc = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_188c0 : bv 32 := 0x00b53023.
Lemma F_188c0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x189fc : word) = Some W_188c0.
Proof. vm_refl. Qed.
Lemma D_188c0 : decode_any W_188c0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_188c4 : bv 32 := 0x00158593.
Lemma F_188c4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a00 : word) = Some W_188c4.
Proof. vm_refl. Qed.
Lemma D_188c4 : decode_any W_188c4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_188c8 : bv 32 := 0xfff5c683.
Lemma F_188c8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a04 : word) = Some W_188c8.
Proof. vm_refl. Qed.
Lemma D_188c8 : decode_any W_188c8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_188cc : bv 32 := 0xfec68ae3.
Lemma F_188cc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a08 : word) = Some W_188cc.
Proof. vm_refl. Qed.
Lemma D_188cc : decode_any W_188cc = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_188d0 : bv 32 := 0xfe069ae3.
Lemma F_188d0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a0c : word) = Some W_188d0.
Proof. vm_refl. Qed.
Lemma D_188d0 : decode_any W_188d0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_188d4 : bv 32 := 0x03010513.
Lemma F_188d4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a10 : word) = Some W_188d4.
Proof. vm_refl. Qed.
Lemma D_188d4 : decode_any W_188d4 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_188d8 : bv 32 := 0x214000ef.
Lemma F_188d8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a14 : word) = Some W_188d8.
Proof. vm_refl. Qed.
Lemma D_188d8 : decode_any W_188d8 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_188dc : bv 32 := 0x0f813503.
Lemma F_188dc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a18 : word) = Some W_188dc.
Proof. vm_refl. Qed.
Lemma D_188dc : decode_any W_188dc = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_188e0 : bv 32 := 0x015000ef.
Lemma F_188e0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a1c : word) = Some W_188e0.
Proof. vm_refl. Qed.
Lemma D_188e0 : decode_any W_188e0 = Some (Jal 1 2068, 4%Z).
Proof. vm_refl. Qed.

Definition W_188e4 : bv 32 := 0x08813503.
Lemma F_188e4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a20 : word) = Some W_188e4.
Proof. vm_refl. Qed.
Lemma D_188e4 : decode_any W_188e4 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_188e8 : bv 32 := 0x09013583.
Lemma F_188e8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a24 : word) = Some W_188e8.
Proof. vm_refl. Qed.
Lemma D_188e8 : decode_any W_188e8 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_188ec : bv 32 := 0x00b51c63.
Lemma F_188ec : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a28 : word) = Some W_188ec.
Proof. vm_refl. Qed.
Lemma D_188ec : decode_any W_188ec = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_188f0 : bv 32 := 0x09813503.
Lemma F_188f0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a2c : word) = Some W_188f0.
Proof. vm_refl. Qed.
Lemma D_188f0 : decode_any W_188f0 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_188f4 : bv 32 := 0x0a013583.
Lemma F_188f4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a30 : word) = Some W_188f4.
Proof. vm_refl. Qed.
Lemma D_188f4 : decode_any W_188f4 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_188f8 : bv 32 := 0x00b51663.
Lemma F_188f8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a34 : word) = Some W_188f8.
Proof. vm_refl. Qed.
Lemma D_188f8 : decode_any W_188f8 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_188fc : bv 32 := 0x0e813503.
Lemma F_188fc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a38 : word) = Some W_188fc.
Proof. vm_refl. Qed.
Lemma D_188fc : decode_any W_188fc = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_18900 : bv 32 := 0x0e050063.
Lemma F_18900 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a3c : word) = Some W_18900.
Proof. vm_refl. Qed.
Lemma D_18900 : decode_any W_18900 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_18904 : bv 32 := 0x00200693.
Lemma F_18904 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a40 : word) = Some W_18904.
Proof. vm_refl. Qed.
Lemma D_18904 : decode_any W_18904 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_18908 : bv 32 := 0x00100793.
Lemma F_18908 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a44 : word) = Some W_18908.
Proof. vm_refl. Qed.
Lemma D_18908 : decode_any W_18908 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1890c : bv 32 := 0x00013423.
Lemma F_1890c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a48 : word) = Some W_1890c.
Proof. vm_refl. Qed.
Lemma D_1890c : decode_any W_1890c = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18910 : bv 32 := 0x00013823.
Lemma F_18910 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a4c : word) = Some W_18910.
Proof. vm_refl. Qed.
Lemma D_18910 : decode_any W_18910 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18914 : bv 32 := 0x04900893.
Lemma F_18914 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a50 : word) = Some W_18914.
Proof. vm_refl. Qed.
Lemma D_18914 : decode_any W_18914 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_18918 : bv 32 := 0x01810513.
Lemma F_18918 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a54 : word) = Some W_18918.
Proof. vm_refl. Qed.
Lemma D_18918 : decode_any W_18918 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1891c : bv 32 := 0x00300593.
Lemma F_1891c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a58 : word) = Some W_1891c.
Proof. vm_refl. Qed.
Lemma D_1891c : decode_any W_1891c = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_18920 : bv 32 := 0x00810613.
Lemma F_18920 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a5c : word) = Some W_18920.
Proof. vm_refl. Qed.
Lemma D_18920 : decode_any W_18920 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18924 : bv 32 := 0x00800713.
Lemma F_18924 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a60 : word) = Some W_18924.
Proof. vm_refl. Qed.
Lemma D_18924 : decode_any W_18924 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18928 : bv 32 := 0x00013c23.
Lemma F_18928 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a64 : word) = Some W_18928.
Proof. vm_refl. Qed.
Lemma D_18928 : decode_any W_18928 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1892c : bv 32 := 0x02f13023.
Lemma F_1892c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a68 : word) = Some W_1892c.
Proof. vm_refl. Qed.
Lemma D_1892c : decode_any W_1892c = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18930 : bv 32 := 0x02d13423.
Lemma F_18930 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a6c : word) = Some W_18930.
Proof. vm_refl. Qed.
Lemma D_18930 : decode_any W_18930 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18934 : bv 32 := 0x00000693.
Lemma F_18934 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a70 : word) = Some W_18934.
Proof. vm_refl. Qed.
Lemma D_18934 : decode_any W_18934 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18938 : bv 32 := 0x00000073.
Lemma F_18938 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a74 : word) = Some W_18938.
Proof. vm_refl. Qed.
Lemma D_18938 : decode_any W_18938 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_18938 : is_ecall W_18938 = true.
Proof. reflexivity. Qed.

Definition W_1893c : bv 32 := 0x02051513.
Lemma F_1893c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a78 : word) = Some W_1893c.
Proof. vm_refl. Qed.
Lemma D_1893c : decode_any W_1893c = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18940 : bv 32 := 0x00055463.
Lemma F_18940 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a7c : word) = Some W_18940.
Proof. vm_refl. Qed.
Lemma D_18940 : decode_any W_18940 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18944 : bv 32 := 0x00000023.
Lemma F_18944 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a80 : word) = Some W_18944.
Proof. vm_refl. Qed.
Lemma D_18944 : decode_any W_18944 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18948 : bv 32 := 0x01e15503.
Lemma F_18948 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a84 : word) = Some W_18948.
Proof. vm_refl. Qed.
Lemma D_18948 : decode_any W_18948 = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_1894c : bv 32 := 0x02057513.
Lemma F_1894c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a88 : word) = Some W_1894c.
Proof. vm_refl. Qed.
Lemma D_1894c : decode_any W_1894c = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18950 : bv 32 := 0x02050463.
Lemma F_18950 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a8c : word) = Some W_18950.
Proof. vm_refl. Qed.
Lemma D_18950 : decode_any W_18950 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18954 : bv 32 := 0xffff8517.
Lemma F_18954 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a90 : word) = Some W_18954.
Proof. vm_refl. Qed.
Lemma D_18954 : decode_any W_18954 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18958 : bv 32 := 0x00008637.
Lemma F_18958 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a94 : word) = Some W_18958.
Proof. vm_refl. Qed.
Lemma D_18958 : decode_any W_18958 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1895c : bv 32 := 0x03800893.
Lemma F_1895c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a98 : word) = Some W_1895c.
Proof. vm_refl. Qed.
Lemma D_1895c : decode_any W_1895c = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18960 : bv 32 := 0xabf50593.
Lemma F_18960 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18a9c : word) = Some W_18960.
Proof. vm_refl. Qed.
Lemma D_18960 : decode_any W_18960 = Some (OpImm ALU_ADD 11 10 2751, 4%Z).
Proof. vm_refl. Qed.

Definition W_18964 : bv 32 := 0x0026061b.
Lemma F_18964 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18aa0 : word) = Some W_18964.
Proof. vm_refl. Qed.
Lemma D_18964 : decode_any W_18964 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_18968 : bv 32 := 0xf9c00513.
Lemma F_18968 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18aa4 : word) = Some W_18968.
Proof. vm_refl. Qed.
Lemma D_18968 : decode_any W_18968 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_1896c : bv 32 := 0x00000073.
Lemma F_1896c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18aa8 : word) = Some W_1896c.
Proof. vm_refl. Qed.
Lemma D_1896c : decode_any W_1896c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1896c : is_ecall W_1896c = true.
Proof. reflexivity. Qed.

Definition W_18970 : bv 32 := 0x00055463.
Lemma F_18970 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18aac : word) = Some W_18970.
Proof. vm_refl. Qed.
Lemma D_18970 : decode_any W_18970 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18974 : bv 32 := 0x00000023.
Lemma F_18974 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ab0 : word) = Some W_18974.
Proof. vm_refl. Qed.
Lemma D_18974 : decode_any W_18974 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18978 : bv 32 := 0x02615503.
Lemma F_18978 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ab4 : word) = Some W_18978.
Proof. vm_refl. Qed.
Lemma D_18978 : decode_any W_18978 = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

Definition W_1897c : bv 32 := 0x02057513.
Lemma F_1897c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ab8 : word) = Some W_1897c.
Proof. vm_refl. Qed.
Lemma D_1897c : decode_any W_1897c = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18980 : bv 32 := 0x02050463.
Lemma F_18980 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18abc : word) = Some W_18980.
Proof. vm_refl. Qed.
Lemma D_18980 : decode_any W_18980 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18984 : bv 32 := 0xffff8517.
Lemma F_18984 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ac0 : word) = Some W_18984.
Proof. vm_refl. Qed.
Lemma D_18984 : decode_any W_18984 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_18988 : bv 32 := 0x00008637.
Lemma F_18988 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ac4 : word) = Some W_18988.
Proof. vm_refl. Qed.
Lemma D_18988 : decode_any W_18988 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1898c : bv 32 := 0x03800893.
Lemma F_1898c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ac8 : word) = Some W_1898c.
Proof. vm_refl. Qed.
Lemma D_1898c : decode_any W_1898c = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18990 : bv 32 := 0xa8f50593.
Lemma F_18990 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18acc : word) = Some W_18990.
Proof. vm_refl. Qed.
Lemma D_18990 : decode_any W_18990 = Some (OpImm ALU_ADD 11 10 2703, 4%Z).
Proof. vm_refl. Qed.

Definition W_18994 : bv 32 := 0x0026061b.
Lemma F_18994 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ad0 : word) = Some W_18994.
Proof. vm_refl. Qed.
Lemma D_18994 : decode_any W_18994 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_18998 : bv 32 := 0xf9c00513.
Lemma F_18998 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ad4 : word) = Some W_18998.
Proof. vm_refl. Qed.
Lemma D_18998 : decode_any W_18998 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_1899c : bv 32 := 0x00000073.
Lemma F_1899c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ad8 : word) = Some W_1899c.
Proof. vm_refl. Qed.
Lemma D_1899c : decode_any W_1899c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1899c : is_ecall W_1899c = true.
Proof. reflexivity. Qed.

Definition W_189a0 : bv 32 := 0x00055463.
Lemma F_189a0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18adc : word) = Some W_189a0.
Proof. vm_refl. Qed.
Lemma D_189a0 : decode_any W_189a0 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_189a4 : bv 32 := 0x00000023.
Lemma F_189a4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ae0 : word) = Some W_189a4.
Proof. vm_refl. Qed.
Lemma D_189a4 : decode_any W_189a4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_189a8 : bv 32 := 0x02e15503.
Lemma F_189a8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ae4 : word) = Some W_189a8.
Proof. vm_refl. Qed.
Lemma D_189a8 : decode_any W_189a8 = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

Definition W_189ac : bv 32 := 0x02057513.
Lemma F_189ac : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ae8 : word) = Some W_189ac.
Proof. vm_refl. Qed.
Lemma D_189ac : decode_any W_189ac = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_189b0 : bv 32 := 0x02050463.
Lemma F_189b0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18aec : word) = Some W_189b0.
Proof. vm_refl. Qed.
Lemma D_189b0 : decode_any W_189b0 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_189b4 : bv 32 := 0xffff8517.
Lemma F_189b4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18af0 : word) = Some W_189b4.
Proof. vm_refl. Qed.
Lemma D_189b4 : decode_any W_189b4 = Some (Auipc 10 1048568, 4%Z).
Proof. vm_refl. Qed.

Definition W_189b8 : bv 32 := 0x00008637.
Lemma F_189b8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18af4 : word) = Some W_189b8.
Proof. vm_refl. Qed.
Lemma D_189b8 : decode_any W_189b8 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_189bc : bv 32 := 0x03800893.
Lemma F_189bc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18af8 : word) = Some W_189bc.
Proof. vm_refl. Qed.
Lemma D_189bc : decode_any W_189bc = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_189c0 : bv 32 := 0xa5f50593.
Lemma F_189c0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18afc : word) = Some W_189c0.
Proof. vm_refl. Qed.
Lemma D_189c0 : decode_any W_189c0 = Some (OpImm ALU_ADD 11 10 2655, 4%Z).
Proof. vm_refl. Qed.

Definition W_189c4 : bv 32 := 0x0026061b.
Lemma F_189c4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b00 : word) = Some W_189c4.
Proof. vm_refl. Qed.
Lemma D_189c4 : decode_any W_189c4 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_189c8 : bv 32 := 0xf9c00513.
Lemma F_189c8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b04 : word) = Some W_189c8.
Proof. vm_refl. Qed.
Lemma D_189c8 : decode_any W_189c8 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

Definition W_189cc : bv 32 := 0x00000073.
Lemma F_189cc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b08 : word) = Some W_189cc.
Proof. vm_refl. Qed.
Lemma D_189cc : decode_any W_189cc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_189cc : is_ecall W_189cc = true.
Proof. reflexivity. Qed.

Definition W_189d0 : bv 32 := 0x00055463.
Lemma F_189d0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b0c : word) = Some W_189d0.
Proof. vm_refl. Qed.
Lemma D_189d0 : decode_any W_189d0 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_189d4 : bv 32 := 0x00000023.
Lemma F_189d4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b10 : word) = Some W_189d4.
Proof. vm_refl. Qed.
Lemma D_189d4 : decode_any W_189d4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_189d8 : bv 32 := 0x00100513.
Lemma F_189d8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b14 : word) = Some W_189d8.
Proof. vm_refl. Qed.
Lemma D_189d8 : decode_any W_189d8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_189dc : bv 32 := 0x00a90123.
Lemma F_189dc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b18 : word) = Some W_189dc.
Proof. vm_refl. Qed.
Lemma D_189dc : decode_any W_189dc = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_189e0 : bv 32 := 0x17813083.
Lemma F_189e0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b1c : word) = Some W_189e0.
Proof. vm_refl. Qed.
Lemma D_189e0 : decode_any W_189e0 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_189e4 : bv 32 := 0x17013403.
Lemma F_189e4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b20 : word) = Some W_189e4.
Proof. vm_refl. Qed.
Lemma D_189e4 : decode_any W_189e4 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_189e8 : bv 32 := 0x16813483.
Lemma F_189e8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b24 : word) = Some W_189e8.
Proof. vm_refl. Qed.
Lemma D_189e8 : decode_any W_189e8 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_189ec : bv 32 := 0x16013903.
Lemma F_189ec : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b28 : word) = Some W_189ec.
Proof. vm_refl. Qed.
Lemma D_189ec : decode_any W_189ec = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_189f0 : bv 32 := 0x18010113.
Lemma F_189f0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b2c : word) = Some W_189f0.
Proof. vm_refl. Qed.
Lemma D_189f0 : decode_any W_189f0 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_189f4 : bv 32 := 0x00008067.
Lemma F_189f4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b30 : word) = Some W_189f4.
Proof. vm_refl. Qed.
Lemma D_189f4 : decode_any W_189f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_189f8 : bv 32 := 0xfe010113.
Lemma F_189f8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b34 : word) = Some W_189f8.
Proof. vm_refl. Qed.
Lemma D_189f8 : decode_any W_189f8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_189fc : bv 32 := 0x00113c23.
Lemma F_189fc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b38 : word) = Some W_189fc.
Proof. vm_refl. Qed.
Lemma D_189fc : decode_any W_189fc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a00 : bv 32 := 0x00813823.
Lemma F_18a00 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b3c : word) = Some W_18a00.
Proof. vm_refl. Qed.
Lemma D_18a00 : decode_any W_18a00 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a04 : bv 32 := 0x00913423.
Lemma F_18a04 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b40 : word) = Some W_18a04.
Proof. vm_refl. Qed.
Lemma D_18a04 : decode_any W_18a04 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a08 : bv 32 := 0xdc1ff0ef.
Lemma F_18a08 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b44 : word) = Some W_18a08.
Proof. vm_refl. Qed.
Lemma D_18a08 : decode_any W_18a08 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a0c : bv 32 := 0x00009517.
Lemma F_18a0c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b48 : word) = Some W_18a0c.
Proof. vm_refl. Qed.
Lemma D_18a0c : decode_any W_18a0c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a10 : bv 32 := 0x00009597.
Lemma F_18a10 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b4c : word) = Some W_18a10.
Proof. vm_refl. Qed.
Lemma D_18a10 : decode_any W_18a10 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a14 : bv 32 := 0x0a853403.
Lemma F_18a14 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b50 : word) = Some W_18a14.
Proof. vm_refl. Qed.
Lemma D_18a14 : decode_any W_18a14 = Some (Load SZ8 true 8 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a18 : bv 32 := 0x0ac5b483.
Lemma F_18a18 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b54 : word) = Some W_18a18.
Proof. vm_refl. Qed.
Lemma D_18a18 : decode_any W_18a18 = Some (Load SZ8 true 9 11 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a1c : bv 32 := 0x0084fa63.
Lemma F_18a1c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b58 : word) = Some W_18a1c.
Proof. vm_refl. Qed.
Lemma D_18a1c : decode_any W_18a1c = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a20 : bv 32 := 0x0004b503.
Lemma F_18a20 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b5c : word) = Some W_18a20.
Proof. vm_refl. Qed.
Lemma D_18a20 : decode_any W_18a20 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a24 : bv 32 := 0x000500e7.
Lemma F_18a24 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b60 : word) = Some W_18a24.
Proof. vm_refl. Qed.
Lemma D_18a24 : decode_any W_18a24 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a28 : bv 32 := 0x00848493.
Lemma F_18a28 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b64 : word) = Some W_18a28.
Proof. vm_refl. Qed.
Lemma D_18a28 : decode_any W_18a28 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a2c : bv 32 := 0xfe84eae3.
Lemma F_18a2c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b68 : word) = Some W_18a2c.
Proof. vm_refl. Qed.
Lemma D_18a2c : decode_any W_18a2c = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a30 : bv 32 := 0x01813083.
Lemma F_18a30 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b6c : word) = Some W_18a30.
Proof. vm_refl. Qed.
Lemma D_18a30 : decode_any W_18a30 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a34 : bv 32 := 0x01013403.
Lemma F_18a34 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b70 : word) = Some W_18a34.
Proof. vm_refl. Qed.
Lemma D_18a34 : decode_any W_18a34 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a38 : bv 32 := 0x00813483.
Lemma F_18a38 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b74 : word) = Some W_18a38.
Proof. vm_refl. Qed.
Lemma D_18a38 : decode_any W_18a38 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a3c : bv 32 := 0x02010113.
Lemma F_18a3c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b78 : word) = Some W_18a3c.
Proof. vm_refl. Qed.
Lemma D_18a3c : decode_any W_18a3c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a40 : bv 32 := 0x00008067.
Lemma F_18a40 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b7c : word) = Some W_18a40.
Proof. vm_refl. Qed.
Lemma D_18a40 : decode_any W_18a40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a44 : bv 32 := 0xfe010113.
Lemma F_18a44 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b80 : word) = Some W_18a44.
Proof. vm_refl. Qed.
Lemma D_18a44 : decode_any W_18a44 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a48 : bv 32 := 0x00113c23.
Lemma F_18a48 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b84 : word) = Some W_18a48.
Proof. vm_refl. Qed.
Lemma D_18a48 : decode_any W_18a48 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a4c : bv 32 := 0x00813823.
Lemma F_18a4c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b88 : word) = Some W_18a4c.
Proof. vm_refl. Qed.
Lemma D_18a4c : decode_any W_18a4c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a50 : bv 32 := 0x00913423.
Lemma F_18a50 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b8c : word) = Some W_18a50.
Proof. vm_refl. Qed.
Lemma D_18a50 : decode_any W_18a50 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a54 : bv 32 := 0x01213023.
Lemma F_18a54 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b90 : word) = Some W_18a54.
Proof. vm_refl. Qed.
Lemma D_18a54 : decode_any W_18a54 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a58 : bv 32 := 0x00060413.
Lemma F_18a58 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b94 : word) = Some W_18a58.
Proof. vm_refl. Qed.
Lemma D_18a58 : decode_any W_18a58 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a5c : bv 32 := 0x00058493.
Lemma F_18a5c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b98 : word) = Some W_18a5c.
Proof. vm_refl. Qed.
Lemma D_18a5c : decode_any W_18a5c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a60 : bv 32 := 0x00050913.
Lemma F_18a60 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18b9c : word) = Some W_18a60.
Proof. vm_refl. Qed.
Lemma D_18a60 : decode_any W_18a60 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a64 : bv 32 := 0x00063583.
Lemma F_18a64 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ba0 : word) = Some W_18a64.
Proof. vm_refl. Qed.
Lemma D_18a64 : decode_any W_18a64 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a68 : bv 32 := 0x00349513.
Lemma F_18a68 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ba4 : word) = Some W_18a68.
Proof. vm_refl. Qed.
Lemma D_18a68 : decode_any W_18a68 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a6c : bv 32 := 0x00a60533.
Lemma F_18a6c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ba8 : word) = Some W_18a6c.
Proof. vm_refl. Qed.
Lemma D_18a6c : decode_any W_18a6c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a70 : bv 32 := 0x00850513.
Lemma F_18a70 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bac : word) = Some W_18a70.
Proof. vm_refl. Qed.
Lemma D_18a70 : decode_any W_18a70 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a74 : bv 32 := 0xd59ff0ef.
Lemma F_18a74 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bb0 : word) = Some W_18a74.
Proof. vm_refl. Qed.
Lemma D_18a74 : decode_any W_18a74 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a78 : bv 32 := 0x00000517.
Lemma F_18a78 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bb4 : word) = Some W_18a78.
Proof. vm_refl. Qed.
Lemma D_18a78 : decode_any W_18a78 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a7c : bv 32 := 0x02c50313.
Lemma F_18a7c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bb8 : word) = Some W_18a7c.
Proof. vm_refl. Qed.
Lemma D_18a7c : decode_any W_18a7c = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a80 : bv 32 := 0x00090513.
Lemma F_18a80 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bbc : word) = Some W_18a80.
Proof. vm_refl. Qed.
Lemma D_18a80 : decode_any W_18a80 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a84 : bv 32 := 0x00048593.
Lemma F_18a84 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bc0 : word) = Some W_18a84.
Proof. vm_refl. Qed.
Lemma D_18a84 : decode_any W_18a84 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a88 : bv 32 := 0x00040613.
Lemma F_18a88 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bc4 : word) = Some W_18a88.
Proof. vm_refl. Qed.
Lemma D_18a88 : decode_any W_18a88 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a8c : bv 32 := 0x01813083.
Lemma F_18a8c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bc8 : word) = Some W_18a8c.
Proof. vm_refl. Qed.
Lemma D_18a8c : decode_any W_18a8c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a90 : bv 32 := 0x01013403.
Lemma F_18a90 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bcc : word) = Some W_18a90.
Proof. vm_refl. Qed.
Lemma D_18a90 : decode_any W_18a90 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a94 : bv 32 := 0x00813483.
Lemma F_18a94 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bd0 : word) = Some W_18a94.
Proof. vm_refl. Qed.
Lemma D_18a94 : decode_any W_18a94 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a98 : bv 32 := 0x00013903.
Lemma F_18a98 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bd4 : word) = Some W_18a98.
Proof. vm_refl. Qed.
Lemma D_18a98 : decode_any W_18a98 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18a9c : bv 32 := 0x02010113.
Lemma F_18a9c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bd8 : word) = Some W_18a9c.
Proof. vm_refl. Qed.
Lemma D_18a9c : decode_any W_18a9c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18aa0 : bv 32 := 0x00030067.
Lemma F_18aa0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bdc : word) = Some W_18aa0.
Proof. vm_refl. Qed.
Lemma D_18aa0 : decode_any W_18aa0 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18aa4 : bv 32 := 0xfd010113.
Lemma F_18aa4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18be0 : word) = Some W_18aa4.
Proof. vm_refl. Qed.
Lemma D_18aa4 : decode_any W_18aa4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_18aa8 : bv 32 := 0x02113423.
Lemma F_18aa8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18be4 : word) = Some W_18aa8.
Proof. vm_refl. Qed.
Lemma D_18aa8 : decode_any W_18aa8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18aac : bv 32 := 0x02813023.
Lemma F_18aac : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18be8 : word) = Some W_18aac.
Proof. vm_refl. Qed.
Lemma D_18aac : decode_any W_18aac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ab0 : bv 32 := 0x00913c23.
Lemma F_18ab0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bec : word) = Some W_18ab0.
Proof. vm_refl. Qed.
Lemma D_18ab0 : decode_any W_18ab0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ab4 : bv 32 := 0x01213823.
Lemma F_18ab4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bf0 : word) = Some W_18ab4.
Proof. vm_refl. Qed.
Lemma D_18ab4 : decode_any W_18ab4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ab8 : bv 32 := 0x01313423.
Lemma F_18ab8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bf4 : word) = Some W_18ab8.
Proof. vm_refl. Qed.
Lemma D_18ab8 : decode_any W_18ab8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18abc : bv 32 := 0x00060413.
Lemma F_18abc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bf8 : word) = Some W_18abc.
Proof. vm_refl. Qed.
Lemma D_18abc : decode_any W_18abc = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ac0 : bv 32 := 0x00058493.
Lemma F_18ac0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18bfc : word) = Some W_18ac0.
Proof. vm_refl. Qed.
Lemma D_18ac0 : decode_any W_18ac0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ac4 : bv 32 := 0x00050913.
Lemma F_18ac4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c00 : word) = Some W_18ac4.
Proof. vm_refl. Qed.
Lemma D_18ac4 : decode_any W_18ac4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ac8 : bv 32 := 0x00359513.
Lemma F_18ac8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c04 : word) = Some W_18ac8.
Proof. vm_refl. Qed.
Lemma D_18ac8 : decode_any W_18ac8 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_18acc : bv 32 := 0x00a60533.
Lemma F_18acc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c08 : word) = Some W_18acc.
Proof. vm_refl. Qed.
Lemma D_18acc : decode_any W_18acc = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ad0 : bv 32 := 0x00850993.
Lemma F_18ad0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c0c : word) = Some W_18ad0.
Proof. vm_refl. Qed.
Lemma D_18ad0 : decode_any W_18ad0 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ad4 : bv 32 := 0xf25ff0ef.
Lemma F_18ad4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c10 : word) = Some W_18ad4.
Proof. vm_refl. Qed.
Lemma D_18ad4 : decode_any W_18ad4 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ad8 : bv 32 := 0x00048513.
Lemma F_18ad8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c14 : word) = Some W_18ad8.
Proof. vm_refl. Qed.
Lemma D_18ad8 : decode_any W_18ad8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18adc : bv 32 := 0x00040593.
Lemma F_18adc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c18 : word) = Some W_18adc.
Proof. vm_refl. Qed.
Lemma D_18adc : decode_any W_18adc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ae0 : bv 32 := 0x00098613.
Lemma F_18ae0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c1c : word) = Some W_18ae0.
Proof. vm_refl. Qed.
Lemma D_18ae0 : decode_any W_18ae0 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ae4 : bv 32 := 0x000900e7.
Lemma F_18ae4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c20 : word) = Some W_18ae4.
Proof. vm_refl. Qed.
Lemma D_18ae4 : decode_any W_18ae4 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ae8 : bv 32 := 0x498000ef.
Lemma F_18ae8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c24 : word) = Some W_18ae8.
Proof. vm_refl. Qed.
Lemma D_18ae8 : decode_any W_18ae8 = Some (Jal 1 1176, 4%Z).
Proof. vm_refl. Qed.

Definition W_18aec : bv 32 := 0xfc010113.
Lemma F_18aec : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c28 : word) = Some W_18aec.
Proof. vm_refl. Qed.
Lemma D_18aec : decode_any W_18aec = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c2c : bv 32 := 0x02113c23.
Lemma TF_18c2c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c2c : word) = Some TW_18c2c.
Proof. vm_refl. Qed.
Lemma TD_18c2c : decode_any TW_18c2c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c30 : bv 32 := 0x02813823.
Lemma TF_18c30 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c30 : word) = Some TW_18c30.
Proof. vm_refl. Qed.
Lemma TD_18c30 : decode_any TW_18c30 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c34 : bv 32 := 0x02913423.
Lemma TF_18c34 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c34 : word) = Some TW_18c34.
Proof. vm_refl. Qed.
Lemma TD_18c34 : decode_any TW_18c34 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c38 : bv 32 := 0x03213023.
Lemma TF_18c38 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c38 : word) = Some TW_18c38.
Proof. vm_refl. Qed.
Lemma TD_18c38 : decode_any TW_18c38 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c3c : bv 32 := 0x01313c23.
Lemma TF_18c3c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c3c : word) = Some TW_18c3c.
Proof. vm_refl. Qed.
Lemma TD_18c3c : decode_any TW_18c3c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c40 : bv 32 := 0x01413823.
Lemma TF_18c40 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c40 : word) = Some TW_18c40.
Proof. vm_refl. Qed.
Lemma TD_18c40 : decode_any TW_18c40 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c44 : bv 32 := 0x01513423.
Lemma TF_18c44 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c44 : word) = Some TW_18c44.
Proof. vm_refl. Qed.
Lemma TD_18c44 : decode_any TW_18c44 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c48 : bv 32 := 0x02853683.
Lemma TF_18c48 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c48 : word) = Some TW_18c48.
Proof. vm_refl. Qed.
Lemma TD_18c48 : decode_any TW_18c48 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c4c : bv 32 := 0x0007a597.
Lemma TF_18c4c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c4c : word) = Some TW_18c4c.
Proof. vm_refl. Qed.
Lemma TD_18c4c : decode_any TW_18c4c = Some (Auipc 11 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c50 : bv 32 := 0x33c58593.
Lemma TF_18c50 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c50 : word) = Some TW_18c50.
Proof. vm_refl. Qed.
Lemma TD_18c50 : decode_any TW_18c50 = Some (OpImm ALU_ADD 11 11 828, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c54 : bv 32 := 0x0007a617.
Lemma TF_18c54 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c54 : word) = Some TW_18c54.
Proof. vm_refl. Qed.
Lemma TD_18c54 : decode_any TW_18c54 = Some (Auipc 12 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c58 : bv 32 := 0x5b460493.
Lemma TF_18c58 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c58 : word) = Some TW_18c58.
Proof. vm_refl. Qed.
Lemma TD_18c58 : decode_any TW_18c58 = Some (OpImm ALU_ADD 9 12 1460, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c5c : bv 32 := 0x0c068e63.
Lemma TF_18c5c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c5c : word) = Some TW_18c5c.
Proof. vm_refl. Qed.
Lemma TD_18c5c : decode_any TW_18c5c = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c60 : bv 32 := 0x00000613.
Lemma TF_18c60 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c60 : word) = Some TW_18c60.
Proof. vm_refl. Qed.
Lemma TD_18c60 : decode_any TW_18c60 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c64 : bv 32 := 0x00000893.
Lemma TF_18c64 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c64 : word) = Some TW_18c64.
Proof. vm_refl. Qed.
Lemma TD_18c64 : decode_any TW_18c64 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c68 : bv 32 := 0x0000a717.
Lemma TF_18c68 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c68 : word) = Some TW_18c68.
Proof. vm_refl. Qed.
Lemma TD_18c68 : decode_any TW_18c68 = Some (Auipc 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c6c : bv 32 := 0x01853783.
Lemma TF_18c6c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c6c : word) = Some TW_18c6c.
Proof. vm_refl. Qed.
Lemma TD_18c6c : decode_any TW_18c6c = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c70 : bv 32 := 0x02053503.
Lemma TF_18c70 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c70 : word) = Some TW_18c70.
Proof. vm_refl. Qed.
Lemma TD_18c70 : decode_any TW_18c70 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c74 : bv 32 := 0x00600813.
Lemma TF_18c74 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c74 : word) = Some TW_18c74.
Proof. vm_refl. Qed.
Lemma TD_18c74 : decode_any TW_18c74 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c78 : bv 32 := 0x00009297.
Lemma TF_18c78 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c78 : word) = Some TW_18c78.
Proof. vm_refl. Qed.
Lemma TD_18c78 : decode_any TW_18c78 = Some (Auipc 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c7c : bv 32 := 0x1b876f03.
Lemma TF_18c7c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c7c : word) = Some TW_18c7c.
Proof. vm_refl. Qed.
Lemma TD_18c7c : decode_any TW_18c7c = Some (Load SZ4 false 30 14 440, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c80 : bv 32 := 0xf102b283.
Lemma TF_18c80 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c80 : word) = Some TW_18c80.
Proof. vm_refl. Qed.
Lemma TD_18c80 : decode_any TW_18c80 = Some (Load SZ8 true 5 5 3856, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c84 : bv 32 := 0x00200313.
Lemma TF_18c84 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c84 : word) = Some TW_18c84.
Proof. vm_refl. Qed.
Lemma TD_18c84 : decode_any TW_18c84 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c88 : bv 32 := 0x00700393.
Lemma TF_18c88 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c88 : word) = Some TW_18c88.
Proof. vm_refl. Qed.
Lemma TD_18c88 : decode_any TW_18c88 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c8c : bv 32 := 0x6474ee37.
Lemma TF_18c8c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c8c : word) = Some TW_18c8c.
Proof. vm_refl. Qed.
Lemma TD_18c8c : decode_any TW_18c8c = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c90 : bv 32 := 0x551e0e1b.
Lemma TF_18c90 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c90 : word) = Some TW_18c90.
Proof. vm_refl. Qed.
Lemma TD_18c90 : decode_any TW_18c90 = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c94 : bv 32 := 0x00078e93.
Lemma TF_18c94 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c94 : word) = Some TW_18c94.
Proof. vm_refl. Qed.
Lemma TD_18c94 : decode_any TW_18c94 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c98 : bv 32 := 0x0180006f.
Lemma TF_18c98 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c98 : word) = Some TW_18c98.
Proof. vm_refl. Qed.
Lemma TD_18c98 : decode_any TW_18c98 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18c9c : bv 32 := 0x010eb603.
Lemma TF_18c9c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18c9c : word) = Some TW_18c9c.
Proof. vm_refl. Qed.
Lemma TD_18c9c : decode_any TW_18c9c = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ca0 : bv 32 := 0x40c78633.
Lemma TF_18ca0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ca0 : word) = Some TW_18ca0.
Proof. vm_refl. Qed.
Lemma TD_18ca0 : decode_any TW_18ca0 = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ca4 : bv 32 := 0xfff68693.
Lemma TF_18ca4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ca4 : word) = Some TW_18ca4.
Proof. vm_refl. Qed.
Lemma TD_18ca4 : decode_any TW_18ca4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ca8 : bv 32 := 0x00ae8eb3.
Lemma TF_18ca8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ca8 : word) = Some TW_18ca8.
Proof. vm_refl. Qed.
Lemma TD_18ca8 : decode_any TW_18ca8 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cac : bv 32 := 0x04068a63.
Lemma TF_18cac : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cac : word) = Some TW_18cac.
Proof. vm_refl. Qed.
Lemma TD_18cac : decode_any TW_18cac = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cb0 : bv 32 := 0x000ea403.
Lemma TF_18cb0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cb0 : word) = Some TW_18cb0.
Proof. vm_refl. Qed.
Lemma TD_18cb0 : decode_any TW_18cb0 = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cb4 : bv 32 := 0xff0404e3.
Lemma TF_18cb4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cb4 : word) = Some TW_18cb4.
Proof. vm_refl. Qed.
Lemma TD_18cb4 : decode_any TW_18cb4 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cb8 : bv 32 := 0x00028a63.
Lemma TF_18cb8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cb8 : word) = Some TW_18cb8.
Proof. vm_refl. Qed.
Lemma TD_18cb8 : decode_any TW_18cb8 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cbc : bv 32 := 0x00641863.
Lemma TF_18cbc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cbc : word) = Some TW_18cbc.
Proof. vm_refl. Qed.
Lemma TD_18cbc : decode_any TW_18cbc = Some (Branch BC_NE 8 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cc0 : bv 32 := 0x010eb603.
Lemma TF_18cc0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cc0 : word) = Some TW_18cc0.
Proof. vm_refl. Qed.
Lemma TD_18cc0 : decode_any TW_18cc0 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cc4 : bv 32 := 0x40c28633.
Lemma TF_18cc4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cc4 : word) = Some TW_18cc4.
Proof. vm_refl. Qed.
Lemma TD_18cc4 : decode_any TW_18cc4 = Some (Op ALU_SUB 12 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cc8 : bv 32 := 0xfddff06f.
Lemma TF_18cc8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cc8 : word) = Some TW_18cc8.
Proof. vm_refl. Qed.
Lemma TD_18cc8 : decode_any TW_18cc8 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ccc : bv 32 := 0x000e8f93.
Lemma TF_18ccc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ccc : word) = Some TW_18ccc.
Proof. vm_refl. Qed.
Lemma TD_18ccc : decode_any TW_18ccc = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cd0 : bv 32 := 0x00740463.
Lemma TF_18cd0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cd0 : word) = Some TW_18cd0.
Proof. vm_refl. Qed.
Lemma TD_18cd0 : decode_any TW_18cd0 = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cd4 : bv 32 := 0x00088f93.
Lemma TF_18cd4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cd4 : word) = Some TW_18cd4.
Proof. vm_refl. Qed.
Lemma TD_18cd4 : decode_any TW_18cd4 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cd8 : bv 32 := 0x03c41063.
Lemma TF_18cd8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cd8 : word) = Some TW_18cd8.
Proof. vm_refl. Qed.
Lemma TD_18cd8 : decode_any TW_18cd8 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cdc : bv 32 := 0x028eb883.
Lemma TF_18cdc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cdc : word) = Some TW_18cdc.
Proof. vm_refl. Qed.
Lemma TD_18cdc : decode_any TW_18cdc = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ce0 : bv 32 := 0x011f7c63.
Lemma TF_18ce0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ce0 : word) = Some TW_18ce0.
Proof. vm_refl. Qed.
Lemma TD_18ce0 : decode_any TW_18ce0 = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ce4 : bv 32 := 0x00800f37.
Lemma TF_18ce4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ce4 : word) = Some TW_18ce4.
Proof. vm_refl. Qed.
Lemma TD_18ce4 : decode_any TW_18ce4 = Some (Lui 30 2048, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ce8 : bv 32 := 0x01e8e463.
Lemma TF_18ce8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ce8 : word) = Some TW_18ce8.
Proof. vm_refl. Qed.
Lemma TD_18ce8 : decode_any TW_18ce8 = Some (Branch BC_LTU 17 30 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cec : bv 32 := 0x008008b7.
Lemma TF_18cec : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cec : word) = Some TW_18cec.
Proof. vm_refl. Qed.
Lemma TD_18cec : decode_any TW_18cec = Some (Lui 17 2048, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cf0 : bv 32 := 0x1b172c23.
Lemma TF_18cf0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cf0 : word) = Some TW_18cf0.
Proof. vm_refl. Qed.
Lemma TD_18cf0 : decode_any TW_18cf0 = Some (Store SZ4 14 17 440, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cf4 : bv 32 := 0x00088f13.
Lemma TF_18cf4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cf4 : word) = Some TW_18cf4.
Proof. vm_refl. Qed.
Lemma TD_18cf4 : decode_any TW_18cf4 = Some (OpImm ALU_ADD 30 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cf8 : bv 32 := 0x000f8893.
Lemma TF_18cf8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cf8 : word) = Some TW_18cf8.
Proof. vm_refl. Qed.
Lemma TD_18cf8 : decode_any TW_18cf8 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18cfc : bv 32 := 0xfa9ff06f.
Lemma TF_18cfc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18cfc : word) = Some TW_18cfc.
Proof. vm_refl. Qed.
Lemma TD_18cfc : decode_any TW_18cfc = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d00 : bv 32 := 0x02088c63.
Lemma TF_18d00 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d00 : word) = Some TW_18d00.
Proof. vm_refl. Qed.
Lemma TD_18d00 : decode_any TW_18d00 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d04 : bv 32 := 0x00858713.
Lemma TF_18d04 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d04 : word) = Some TW_18d04.
Proof. vm_refl. Qed.
Lemma TD_18d04 : decode_any TW_18d04 = Some (OpImm ALU_ADD 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d08 : bv 32 := 0x0108b783.
Lemma TF_18d08 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d08 : word) = Some TW_18d08.
Proof. vm_refl. Qed.
Lemma TD_18d08 : decode_any TW_18d08 = Some (Load SZ8 true 15 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d0c : bv 32 := 0x0208b803.
Lemma TF_18d0c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d0c : word) = Some TW_18d0c.
Proof. vm_refl. Qed.
Lemma TD_18d0c : decode_any TW_18d0c = Some (Load SZ8 true 16 17 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d10 : bv 32 := 0x0288b683.
Lemma TF_18d10 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d10 : word) = Some TW_18d10.
Proof. vm_refl. Qed.
Lemma TD_18d10 : decode_any TW_18d10 = Some (Load SZ8 true 13 17 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d14 : bv 32 := 0x0308b503.
Lemma TF_18d14 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d14 : word) = Some TW_18d14.
Proof. vm_refl. Qed.
Lemma TD_18d14 : decode_any TW_18d14 = Some (Load SZ8 true 10 17 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d18 : bv 32 := 0x00c78633.
Lemma TF_18d18 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d18 : word) = Some TW_18d18.
Proof. vm_refl. Qed.
Lemma TD_18d18 : decode_any TW_18d18 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d1c : bv 32 := 0x00100793.
Lemma TF_18d1c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d1c : word) = Some TW_18d1c.
Proof. vm_refl. Qed.
Lemma TD_18d1c : decode_any TW_18d1c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d20 : bv 32 := 0x00c5b823.
Lemma TF_18d20 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d20 : word) = Some TW_18d20.
Proof. vm_refl. Qed.
Lemma TD_18d20 : decode_any TW_18d20 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d24 : bv 32 := 0x0105bc23.
Lemma TF_18d24 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d24 : word) = Some TW_18d24.
Proof. vm_refl. Qed.
Lemma TD_18d24 : decode_any TW_18d24 = Some (Store SZ8 11 16 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d28 : bv 32 := 0x02a5b423.
Lemma TF_18d28 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d28 : word) = Some TW_18d28.
Proof. vm_refl. Qed.
Lemma TD_18d28 : decode_any TW_18d28 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d2c : bv 32 := 0x00e4b823.
Lemma TF_18d2c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d2c : word) = Some TW_18d2c.
Proof. vm_refl. Qed.
Lemma TD_18d2c : decode_any TW_18d2c = Some (Store SZ8 9 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d30 : bv 32 := 0x02f4b423.
Lemma TF_18d30 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d30 : word) = Some TW_18d30.
Proof. vm_refl. Qed.
Lemma TD_18d30 : decode_any TW_18d30 = Some (Store SZ8 9 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d34 : bv 32 := 0x0100006f.
Lemma TF_18d34 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d34 : word) = Some TW_18d34.
Proof. vm_refl. Qed.
Lemma TD_18d34 : decode_any TW_18d34 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d38 : bv 32 := 0x0105b603.
Lemma TF_18d38 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d38 : word) = Some TW_18d38.
Proof. vm_refl. Qed.
Lemma TD_18d38 : decode_any TW_18d38 = Some (Load SZ8 true 12 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d3c : bv 32 := 0x0205b683.
Lemma TF_18d3c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d3c : word) = Some TW_18d3c.
Proof. vm_refl. Qed.
Lemma TD_18d3c : decode_any TW_18d3c = Some (Load SZ8 true 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d40 : bv 32 := 0x0285b503.
Lemma TF_18d40 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d40 : word) = Some TW_18d40.
Proof. vm_refl. Qed.
Lemma TD_18d40 : decode_any TW_18d40 = Some (Load SZ8 true 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d44 : bv 32 := 0x00c68733.
Lemma TF_18d44 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d44 : word) = Some TW_18d44.
Proof. vm_refl. Qed.
Lemma TD_18d44 : decode_any TW_18d44 = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d48 : bv 32 := 0xfff50793.
Lemma TF_18d48 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d48 : word) = Some TW_18d48.
Proof. vm_refl. Qed.
Lemma TD_18d48 : decode_any TW_18d48 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d4c : bv 32 := 0x40e00733.
Lemma TF_18d4c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d4c : word) = Some TW_18d4c.
Proof. vm_refl. Qed.
Lemma TD_18d4c : decode_any TW_18d4c = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d50 : bv 32 := 0x00c7f633.
Lemma TF_18d50 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d50 : word) = Some TW_18d50.
Proof. vm_refl. Qed.
Lemma TD_18d50 : decode_any TW_18d50 = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d54 : bv 32 := 0x00e7f733.
Lemma TF_18d54 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d54 : word) = Some TW_18d54.
Proof. vm_refl. Qed.
Lemma TD_18d54 : decode_any TW_18d54 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d58 : bv 32 := 0x00700793.
Lemma TF_18d58 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d58 : word) = Some TW_18d58.
Proof. vm_refl. Qed.
Lemma TD_18d58 : decode_any TW_18d58 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d5c : bv 32 := 0x00d706b3.
Lemma TF_18d5c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d5c : word) = Some TW_18d5c.
Proof. vm_refl. Qed.
Lemma TD_18d5c : decode_any TW_18d5c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d60 : bv 32 := 0x02d5b023.
Lemma TF_18d60 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d60 : word) = Some TW_18d60.
Proof. vm_refl. Qed.
Lemma TD_18d60 : decode_any TW_18d60 = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d64 : bv 32 := 0x02c5b823.
Lemma TF_18d64 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d64 : word) = Some TW_18d64.
Proof. vm_refl. Qed.
Lemma TD_18d64 : decode_any TW_18d64 = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d68 : bv 32 := 0x00a7e663.
Lemma TF_18d68 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d68 : word) = Some TW_18d68.
Proof. vm_refl. Qed.
Lemma TD_18d68 : decode_any TW_18d68 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d6c : bv 32 := 0x00800513.
Lemma TF_18d6c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d6c : word) = Some TW_18d6c.
Proof. vm_refl. Qed.
Lemma TD_18d6c : decode_any TW_18d6c = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d70 : bv 32 := 0x02a5b423.
Lemma TF_18d70 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d70 : word) = Some TW_18d70.
Proof. vm_refl. Qed.
Lemma TD_18d70 : decode_any TW_18d70 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d74 : bv 32 := 0x00d60633.
Lemma TF_18d74 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d74 : word) = Some TW_18d74.
Proof. vm_refl. Qed.
Lemma TD_18d74 : decode_any TW_18d74 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d78 : bv 32 := 0x000205b7.
Lemma TF_18d78 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d78 : word) = Some TW_18d78.
Proof. vm_refl. Qed.
Lemma TD_18d78 : decode_any TW_18d78 = Some (Lui 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d7c : bv 32 := 0x00a60633.
Lemma TF_18d7c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d7c : word) = Some TW_18d7c.
Proof. vm_refl. Qed.
Lemma TD_18d7c : decode_any TW_18d7c = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d80 : bv 32 := 0x0d15869b.
Lemma TF_18d80 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d80 : word) = Some TW_18d80.
Proof. vm_refl. Qed.
Lemma TD_18d80 : decode_any TW_18d80 = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d84 : bv 32 := 0x0df60593.
Lemma TF_18d84 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d84 : word) = Some TW_18d84.
Proof. vm_refl. Qed.
Lemma TD_18d84 : decode_any TW_18d84 = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d88 : bv 32 := 0xff85f593.
Lemma TF_18d88 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d88 : word) = Some TW_18d88.
Proof. vm_refl. Qed.
Lemma TD_18d88 : decode_any TW_18d88 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d8c : bv 32 := 0x00b4bc23.
Lemma TF_18d8c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d8c : word) = Some TW_18d8c.
Proof. vm_refl. Qed.
Lemma TD_18d8c : decode_any TW_18d8c = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d90 : bv 32 := 0x02a4b023.
Lemma TF_18d90 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d90 : word) = Some TW_18d90.
Proof. vm_refl. Qed.
Lemma TD_18d90 : decode_any TW_18d90 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d94 : bv 32 := 0x02d5ea63.
Lemma TF_18d94 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d94 : word) = Some TW_18d94.
Proof. vm_refl. Qed.
Lemma TD_18d94 : decode_any TW_18d94 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d98 : bv 32 := 0xffff9597.
Lemma TF_18d98 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d98 : word) = Some TW_18d98.
Proof. vm_refl. Qed.
Lemma TD_18d98 : decode_any TW_18d98 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18d9c : bv 32 := 0x04000893.
Lemma TF_18d9c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18d9c : word) = Some TW_18d9c.
Proof. vm_refl. Qed.
Lemma TD_18d9c : decode_any TW_18d9c = Some (OpImm ALU_ADD 17 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18da0 : bv 32 := 0x00200513.
Lemma TF_18da0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18da0 : word) = Some TW_18da0.
Proof. vm_refl. Qed.
Lemma TD_18da0 : decode_any TW_18da0 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18da4 : bv 32 := 0x64858593.
Lemma TF_18da4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18da4 : word) = Some TW_18da4.
Proof. vm_refl. Qed.
Lemma TD_18da4 : decode_any TW_18da4 = Some (OpImm ALU_ADD 11 11 1608, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18da8 : bv 32 := 0x05b00613.
Lemma TF_18da8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18da8 : word) = Some TW_18da8.
Proof. vm_refl. Qed.
Lemma TD_18da8 : decode_any TW_18da8 = Some (OpImm ALU_ADD 12 0 91, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18dac : bv 32 := 0x00000073.
Lemma TF_18dac : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18dac : word) = Some TW_18dac.
Proof. vm_refl. Qed.
Lemma TD_18dac : decode_any TW_18dac = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_18dac : is_ecall TW_18dac = true.
Proof. reflexivity. Qed.

Definition TW_18db0 : bv 32 := 0x00000023.
Lemma TF_18db0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18db0 : word) = Some TW_18db0.
Proof. vm_refl. Qed.
Lemma TD_18db0 : decode_any TW_18db0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18db4 : bv 32 := 0x05e00893.
Lemma TF_18db4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18db4 : word) = Some TW_18db4.
Proof. vm_refl. Qed.
Lemma TD_18db4 : decode_any TW_18db4 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18db8 : bv 32 := 0x07f00513.
Lemma TF_18db8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18db8 : word) = Some TW_18db8.
Proof. vm_refl. Qed.
Lemma TD_18db8 : decode_any TW_18db8 = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18dbc : bv 32 := 0x00000073.
Lemma TF_18dbc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18dbc : word) = Some TW_18dbc.
Proof. vm_refl. Qed.
Lemma TD_18dbc : decode_any TW_18dbc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_18dbc : is_ecall TW_18dbc = true.
Proof. reflexivity. Qed.

Definition TW_18dc0 : bv 32 := 0x0184b583.
Lemma TF_18dc0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18dc0 : word) = Some TW_18dc0.
Proof. vm_refl. Qed.
Lemma TD_18dc0 : decode_any TW_18dc0 = Some (Load SZ8 true 11 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18dc4 : bv 32 := 0x0204b503.
Lemma TF_18dc4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18dc4 : word) = Some TW_18dc4.
Proof. vm_refl. Qed.
Lemma TD_18dc4 : decode_any TW_18dc4 = Some (Load SZ8 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18dc8 : bv 32 := 0x0005a697.
Lemma TF_18dc8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18dc8 : word) = Some TW_18dc8.
Proof. vm_refl. Qed.
Lemma TD_18dc8 : decode_any TW_18dc8 = Some (Auipc 13 90, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18dcc : bv 32 := 0x0104b983.
Lemma TF_18dcc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18dcc : word) = Some TW_18dcc.
Proof. vm_refl. Qed.
Lemma TD_18dcc : decode_any TW_18dcc = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18dd0 : bv 32 := 0x0284b603.
Lemma TF_18dd0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18dd0 : word) = Some TW_18dd0.
Proof. vm_refl. Qed.
Lemma TD_18dd0 : decode_any TW_18dd0 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18dd4 : bv 32 := 0xfff50713.
Lemma TF_18dd4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18dd4 : word) = Some TW_18dd4.
Proof. vm_refl. Qed.
Lemma TD_18dd4 : decode_any TW_18dd4 = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18dd8 : bv 32 := 0xf3800793.
Lemma TF_18dd8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18dd8 : word) = Some TW_18dd8.
Proof. vm_refl. Qed.
Lemma TD_18dd8 : decode_any TW_18dd8 = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ddc : bv 32 := 0x0f068513.
Lemma TF_18ddc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ddc : word) = Some TW_18ddc.
Proof. vm_refl. Qed.
Lemma TD_18ddc : decode_any TW_18ddc = Some (OpImm ALU_ADD 10 13 240, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18de0 : bv 32 := 0x40a787b3.
Lemma TF_18de0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18de0 : word) = Some TW_18de0.
Proof. vm_refl. Qed.
Lemma TD_18de0 : decode_any TW_18de0 = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18de4 : bv 32 := 0x00f77733.
Lemma TF_18de4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18de4 : word) = Some TW_18de4.
Proof. vm_refl. Qed.
Lemma TD_18de4 : decode_any TW_18de4 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18de8 : bv 32 := 0xfff64693.
Lemma TF_18de8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18de8 : word) = Some TW_18de8.
Proof. vm_refl. Qed.
Lemma TD_18de8 : decode_any TW_18de8 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18dec : bv 32 := 0x00e50933.
Lemma TF_18dec : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18dec : word) = Some TW_18dec.
Proof. vm_refl. Qed.
Lemma TD_18dec : decode_any TW_18dec = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18df0 : bv 32 := 0x00369693.
Lemma TF_18df0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18df0 : word) = Some TW_18df0.
Proof. vm_refl. Qed.
Lemma TD_18df0 : decode_any TW_18df0 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18df4 : bv 32 := 0x00d506b3.
Lemma TF_18df4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18df4 : word) = Some TW_18df4.
Proof. vm_refl. Qed.
Lemma TD_18df4 : decode_any TW_18df4 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18df8 : bv 32 := 0x00b68a33.
Lemma TF_18df8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18df8 : word) = Some TW_18df8.
Proof. vm_refl. Qed.
Lemma TD_18df8 : decode_any TW_18df8 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18dfc : bv 32 := 0x0c890413.
Lemma TF_18dfc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18dfc : word) = Some TW_18dfc.
Proof. vm_refl. Qed.
Lemma TD_18dfc : decode_any TW_18dfc = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e00 : bv 32 := 0x04098463.
Lemma TF_18e00 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e00 : word) = Some TW_18e00.
Proof. vm_refl. Qed.
Lemma TD_18e00 : decode_any TW_18e00 = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e04 : bv 32 := 0x00361613.
Lemma TF_18e04 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e04 : word) = Some TW_18e04.
Proof. vm_refl. Qed.
Lemma TD_18e04 : decode_any TW_18e04 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e08 : bv 32 := 0x40c50533.
Lemma TF_18e08 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e08 : word) = Some TW_18e08.
Proof. vm_refl. Qed.
Lemma TD_18e08 : decode_any TW_18e08 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e0c : bv 32 := 0x00b50ab3.
Lemma TF_18e0c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e0c : word) = Some TW_18e0c.
Proof. vm_refl. Qed.
Lemma TD_18e0c : decode_any TW_18e0c = Some (Op ALU_ADD 21 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e10 : bv 32 := 0x0289b503.
Lemma TF_18e10 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e10 : word) = Some TW_18e10.
Proof. vm_refl. Qed.
Lemma TD_18e10 : decode_any TW_18e10 = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e14 : bv 32 := 0x00a40533.
Lemma TF_18e14 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e14 : word) = Some TW_18e14.
Proof. vm_refl. Qed.
Lemma TD_18e14 : decode_any TW_18e14 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e18 : bv 32 := 0x7ff50513.
Lemma TF_18e18 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e18 : word) = Some TW_18e18.
Proof. vm_refl. Qed.
Lemma TD_18e18 : decode_any TW_18e18 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e1c : bv 32 := 0x00150513.
Lemma TF_18e1c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e1c : word) = Some TW_18e1c.
Proof. vm_refl. Qed.
Lemma TD_18e1c : decode_any TW_18e1c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e20 : bv 32 := 0x00aab023.
Lemma TF_18e20 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e20 : word) = Some TW_18e20.
Proof. vm_refl. Qed.
Lemma TD_18e20 : decode_any TW_18e20 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e24 : bv 32 := 0x0289b503.
Lemma TF_18e24 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e24 : word) = Some TW_18e24.
Proof. vm_refl. Qed.
Lemma TD_18e24 : decode_any TW_18e24 = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e28 : bv 32 := 0x0089b583.
Lemma TF_18e28 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e28 : word) = Some TW_18e28.
Proof. vm_refl. Qed.
Lemma TD_18e28 : decode_any TW_18e28 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e2c : bv 32 := 0x0109b603.
Lemma TF_18e2c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e2c : word) = Some TW_18e2c.
Proof. vm_refl. Qed.
Lemma TD_18e2c : decode_any TW_18e2c = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e30 : bv 32 := 0x00a40533.
Lemma TF_18e30 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e30 : word) = Some TW_18e30.
Proof. vm_refl. Qed.
Lemma TD_18e30 : decode_any TW_18e30 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e34 : bv 32 := 0x350070ef.
Lemma TF_18e34 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e34 : word) = Some TW_18e34.
Proof. vm_refl. Qed.
Lemma TD_18e34 : decode_any TW_18e34 = Some (Jal 1 29520, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e38 : bv 32 := 0x0009b983.
Lemma TF_18e38 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e38 : word) = Some TW_18e38.
Proof. vm_refl. Qed.
Lemma TD_18e38 : decode_any TW_18e38 = Some (Load SZ8 true 19 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e3c : bv 32 := 0x008a8a93.
Lemma TF_18e3c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e3c : word) = Some TW_18e3c.
Proof. vm_refl. Qed.
Lemma TD_18e3c : decode_any TW_18e3c = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e40 : bv 32 := 0xfc0998e3.
Lemma TF_18e40 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e40 : word) = Some TW_18e40.
Proof. vm_refl. Qed.
Lemma TD_18e40 : decode_any TW_18e40 = Some (Branch BC_NE 19 0 8144, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e44 : bv 32 := 0x0284b603.
Lemma TF_18e44 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e44 : word) = Some TW_18e44.
Proof. vm_refl. Qed.
Lemma TD_18e44 : decode_any TW_18e44 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e48 : bv 32 := 0x00ca3023.
Lemma TF_18e48 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e48 : word) = Some TW_18e48.
Proof. vm_refl. Qed.
Lemma TD_18e48 : decode_any TW_18e48 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e4c : bv 32 := 0x0d493023.
Lemma TF_18e4c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e4c : word) = Some TW_18e4c.
Proof. vm_refl. Qed.
Lemma TD_18e4c : decode_any TW_18e4c = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e50 : bv 32 := 0x01293023.
Lemma TF_18e50 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e50 : word) = Some TW_18e50.
Proof. vm_refl. Qed.
Lemma TD_18e50 : decode_any TW_18e50 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e54 : bv 32 := 0x00040513.
Lemma TF_18e54 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e54 : word) = Some TW_18e54.
Proof. vm_refl. Qed.
Lemma TD_18e54 : decode_any TW_18e54 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e58 : bv 32 := 0x45d070ef.
Lemma TF_18e58 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e58 : word) = Some TW_18e58.
Proof. vm_refl. Qed.
Lemma TD_18e58 : decode_any TW_18e58 = Some (Jal 1 31836, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e5c : bv 32 := 0x04054a63.
Lemma TF_18e5c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e5c : word) = Some TW_18e5c.
Proof. vm_refl. Qed.
Lemma TD_18e5c : decode_any TW_18e5c = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e60 : bv 32 := 0x00051663.
Lemma TF_18e60 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e60 : word) = Some TW_18e60.
Proof. vm_refl. Qed.
Lemma TD_18e60 : decode_any TW_18e60 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e64 : bv 32 := 0x00100513.
Lemma TF_18e64 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e64 : word) = Some TW_18e64.
Proof. vm_refl. Qed.
Lemma TD_18e64 : decode_any TW_18e64 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e68 : bv 32 := 0x00a48023.
Lemma TF_18e68 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e68 : word) = Some TW_18e68.
Proof. vm_refl. Qed.
Lemma TD_18e68 : decode_any TW_18e68 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e6c : bv 32 := 0x00200513.
Lemma TF_18e6c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e6c : word) = Some TW_18e6c.
Proof. vm_refl. Qed.
Lemma TD_18e6c : decode_any TW_18e6c = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e70 : bv 32 := 0x0007a597.
Lemma TF_18e70 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e70 : word) = Some TW_18e70.
Proof. vm_refl. Qed.
Lemma TD_18e70 : decode_any TW_18e70 = Some (Auipc 11 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e74 : bv 32 := 0x02a92423.
Lemma TF_18e74 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e74 : word) = Some TW_18e74.
Proof. vm_refl. Qed.
Lemma TD_18e74 : decode_any TW_18e74 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e78 : bv 32 := 0x06000893.
Lemma TF_18e78 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e78 : word) = Some TW_18e78.
Proof. vm_refl. Qed.
Lemma TD_18e78 : decode_any TW_18e78 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e7c : bv 32 := 0x11858513.
Lemma TF_18e7c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e7c : word) = Some TW_18e7c.
Proof. vm_refl. Qed.
Lemma TD_18e7c : decode_any TW_18e7c = Some (OpImm ALU_ADD 10 11 280, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e80 : bv 32 := 0x03848593.
Lemma TF_18e80 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e80 : word) = Some TW_18e80.
Proof. vm_refl. Qed.
Lemma TD_18e80 : decode_any TW_18e80 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e84 : bv 32 := 0x00000073.
Lemma TF_18e84 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e84 : word) = Some TW_18e84.
Proof. vm_refl. Qed.
Lemma TD_18e84 : decode_any TW_18e84 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma TE_18e84 : is_ecall TW_18e84 = true.
Proof. reflexivity. Qed.

Definition TW_18e88 : bv 32 := 0x07890613.
Lemma TF_18e88 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e88 : word) = Some TW_18e88.
Proof. vm_refl. Qed.
Lemma TD_18e88 : decode_any TW_18e88 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e8c : bv 32 := 0x02a92023.
Lemma TF_18e8c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e8c : word) = Some TW_18e8c.
Proof. vm_refl. Qed.
Lemma TD_18e8c : decode_any TW_18e8c = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e90 : bv 32 := 0x08b93c23.
Lemma TF_18e90 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e90 : word) = Some TW_18e90.
Proof. vm_refl. Qed.
Lemma TD_18e90 : decode_any TW_18e90 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e94 : bv 32 := 0x06c93c23.
Lemma TF_18e94 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e94 : word) = Some TW_18e94.
Proof. vm_refl. Qed.
Lemma TD_18e94 : decode_any TW_18e94 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e98 : bv 32 := 0x0007a517.
Lemma TF_18e98 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e98 : word) = Some TW_18e98.
Proof. vm_refl. Qed.
Lemma TD_18e98 : decode_any TW_18e98 = Some (Auipc 10 122, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18e9c : bv 32 := 0x35853503.
Lemma TF_18e9c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18e9c : word) = Some TW_18e9c.
Proof. vm_refl. Qed.
Lemma TD_18e9c : decode_any TW_18e9c = Some (Load SZ8 true 10 10 856, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ea0 : bv 32 := 0x01293423.
Lemma TF_18ea0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ea0 : word) = Some TW_18ea0.
Proof. vm_refl. Qed.
Lemma TD_18ea0 : decode_any TW_18ea0 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ea4 : bv 32 := 0x01293823.
Lemma TF_18ea4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ea4 : word) = Some TW_18ea4.
Proof. vm_refl. Qed.
Lemma TD_18ea4 : decode_any TW_18ea4 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ea8 : bv 32 := 0x00a93c23.
Lemma TF_18ea8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ea8 : word) = Some TW_18ea8.
Proof. vm_refl. Qed.
Lemma TD_18ea8 : decode_any TW_18ea8 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18eac : bv 32 := 0x0080006f.
Lemma TF_18eac : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18eac : word) = Some TW_18eac.
Proof. vm_refl. Qed.
Lemma TD_18eac : decode_any TW_18eac = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18eb0 : bv 32 := 0x00000023.
Lemma TF_18eb0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18eb0 : word) = Some TW_18eb0.
Proof. vm_refl. Qed.
Lemma TD_18eb0 : decode_any TW_18eb0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18eb4 : bv 32 := 0x03813083.
Lemma TF_18eb4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18eb4 : word) = Some TW_18eb4.
Proof. vm_refl. Qed.
Lemma TD_18eb4 : decode_any TW_18eb4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18eb8 : bv 32 := 0x03013403.
Lemma TF_18eb8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18eb8 : word) = Some TW_18eb8.
Proof. vm_refl. Qed.
Lemma TD_18eb8 : decode_any TW_18eb8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ebc : bv 32 := 0x02813483.
Lemma TF_18ebc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ebc : word) = Some TW_18ebc.
Proof. vm_refl. Qed.
Lemma TD_18ebc : decode_any TW_18ebc = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ec0 : bv 32 := 0x02013903.
Lemma TF_18ec0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ec0 : word) = Some TW_18ec0.
Proof. vm_refl. Qed.
Lemma TD_18ec0 : decode_any TW_18ec0 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ec4 : bv 32 := 0x01813983.
Lemma TF_18ec4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ec4 : word) = Some TW_18ec4.
Proof. vm_refl. Qed.
Lemma TD_18ec4 : decode_any TW_18ec4 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ec8 : bv 32 := 0x01013a03.
Lemma TF_18ec8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ec8 : word) = Some TW_18ec8.
Proof. vm_refl. Qed.
Lemma TD_18ec8 : decode_any TW_18ec8 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ecc : bv 32 := 0x00813a83.
Lemma TF_18ecc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ecc : word) = Some TW_18ecc.
Proof. vm_refl. Qed.
Lemma TD_18ecc : decode_any TW_18ecc = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ed0 : bv 32 := 0x04010113.
Lemma TF_18ed0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ed0 : word) = Some TW_18ed0.
Proof. vm_refl. Qed.
Lemma TD_18ed0 : decode_any TW_18ed0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition TW_18ed4 : bv 32 := 0x00008067.
Lemma TF_18ed4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ed4 : word) = Some TW_18ed4.
Proof. vm_refl. Qed.
Lemma TD_18ed4 : decode_any TW_18ed4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18da8 : bv 32 := 0xfd010113.
Lemma F_18da8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ed8 : word) = Some W_18da8.
Proof. vm_refl. Qed.
Lemma D_18da8 : decode_any W_18da8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dac : bv 32 := 0x02113423.
Lemma F_18dac : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18edc : word) = Some W_18dac.
Proof. vm_refl. Qed.
Lemma D_18dac : decode_any W_18dac = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18db0 : bv 32 := 0x02813023.
Lemma F_18db0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ee0 : word) = Some W_18db0.
Proof. vm_refl. Qed.
Lemma D_18db0 : decode_any W_18db0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18db4 : bv 32 := 0x00913c23.
Lemma F_18db4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ee4 : word) = Some W_18db4.
Proof. vm_refl. Qed.
Lemma D_18db4 : decode_any W_18db4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18db8 : bv 32 := 0x01213823.
Lemma F_18db8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ee8 : word) = Some W_18db8.
Proof. vm_refl. Qed.
Lemma D_18db8 : decode_any W_18db8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dbc : bv 32 := 0x01313423.
Lemma F_18dbc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18eec : word) = Some W_18dbc.
Proof. vm_refl. Qed.
Lemma D_18dbc : decode_any W_18dbc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dc0 : bv 32 := 0x0007a517.
Lemma F_18dc0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ef0 : word) = Some W_18dc0.
Proof. vm_refl. Qed.
Lemma D_18dc0 : decode_any W_18dc0 = Some (Auipc 10 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dc4 : bv 32 := 0x0d050913.
Lemma F_18dc4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ef4 : word) = Some W_18dc4.
Proof. vm_refl. Qed.
Lemma D_18dc4 : decode_any W_18dc4 = Some (OpImm ALU_ADD 18 10 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dc8 : bv 32 := 0x00490413.
Lemma F_18dc8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18ef8 : word) = Some W_18dc8.
Proof. vm_refl. Qed.
Lemma D_18dc8 : decode_any W_18dc8 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dcc : bv 32 := 0x00040513.
Lemma F_18dcc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18efc : word) = Some W_18dcc.
Proof. vm_refl. Qed.
Lemma D_18dcc : decode_any W_18dcc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dd0 : bv 32 := 0x091070ef.
Lemma F_18dd0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f00 : word) = Some W_18dd0.
Proof. vm_refl. Qed.
Lemma D_18dd0 : decode_any W_18dd0 = Some (Jal 1 30864, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dd4 : bv 32 := 0x01093503.
Lemma F_18dd4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f04 : word) = Some W_18dd4.
Proof. vm_refl. Qed.
Lemma D_18dd4 : decode_any W_18dd4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dd8 : bv 32 := 0x06050863.
Lemma F_18dd8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f08 : word) = Some W_18dd8.
Proof. vm_refl. Qed.
Lemma D_18dd8 : decode_any W_18dd8 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ddc : bv 32 := 0x00892583.
Lemma F_18ddc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f0c : word) = Some W_18ddc.
Proof. vm_refl. Qed.
Lemma D_18ddc : decode_any W_18ddc = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18de0 : bv 32 := 0x0180006f.
Lemma F_18de0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f10 : word) = Some W_18de0.
Proof. vm_refl. Qed.
Lemma D_18de0 : decode_any W_18de0 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18de4 : bv 32 := 0x00053503.
Lemma F_18de4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f14 : word) = Some W_18de4.
Proof. vm_refl. Qed.
Lemma D_18de4 : decode_any W_18de4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18de8 : bv 32 := 0x02000593.
Lemma F_18de8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f18 : word) = Some W_18de8.
Proof. vm_refl. Qed.
Lemma D_18de8 : decode_any W_18de8 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dec : bv 32 := 0x00b92423.
Lemma F_18dec : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f1c : word) = Some W_18dec.
Proof. vm_refl. Qed.
Lemma D_18dec : decode_any W_18dec = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18df0 : bv 32 := 0x00a93823.
Lemma F_18df0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f20 : word) = Some W_18df0.
Proof. vm_refl. Qed.
Lemma D_18df0 : decode_any W_18df0 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18df4 : bv 32 := 0x04050a63.
Lemma F_18df4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f24 : word) = Some W_18df4.
Proof. vm_refl. Qed.
Lemma D_18df4 : decode_any W_18df4 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_18df8 : bv 32 := 0xfff5861b.
Lemma F_18df8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f28 : word) = Some W_18df8.
Proof. vm_refl. Qed.
Lemma D_18df8 : decode_any W_18df8 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_18dfc : bv 32 := 0x00c92423.
Lemma F_18dfc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f2c : word) = Some W_18dfc.
Proof. vm_refl. Qed.
Lemma D_18dfc : decode_any W_18dfc = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e00 : bv 32 := 0xfeb052e3.
Lemma F_18e00 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f30 : word) = Some W_18e00.
Proof. vm_refl. Qed.
Lemma D_18e00 : decode_any W_18e00 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e04 : bv 32 := 0x01093503.
Lemma F_18e04 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f34 : word) = Some W_18e04.
Proof. vm_refl. Qed.
Lemma D_18e04 : decode_any W_18e04 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e08 : bv 32 := 0x00361613.
Lemma F_18e08 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f38 : word) = Some W_18e08.
Proof. vm_refl. Qed.
Lemma D_18e08 : decode_any W_18e08 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e0c : bv 32 := 0x00c50533.
Lemma F_18e0c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f3c : word) = Some W_18e0c.
Proof. vm_refl. Qed.
Lemma D_18e0c : decode_any W_18e0c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e10 : bv 32 := 0x00853983.
Lemma F_18e10 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f40 : word) = Some W_18e10.
Proof. vm_refl. Qed.
Lemma D_18e10 : decode_any W_18e10 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e14 : bv 32 := 0x10853483.
Lemma F_18e14 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f44 : word) = Some W_18e14.
Proof. vm_refl. Qed.
Lemma D_18e14 : decode_any W_18e14 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e18 : bv 32 := 0x00040513.
Lemma F_18e18 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f48 : word) = Some W_18e18.
Proof. vm_refl. Qed.
Lemma D_18e18 : decode_any W_18e18 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e1c : bv 32 := 0x2cd070ef.
Lemma F_18e1c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f4c : word) = Some W_18e1c.
Proof. vm_refl. Qed.
Lemma D_18e1c : decode_any W_18e1c = Some (Jal 1 31436, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e20 : bv 32 := 0x00048513.
Lemma F_18e20 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f50 : word) = Some W_18e20.
Proof. vm_refl. Qed.
Lemma D_18e20 : decode_any W_18e20 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e24 : bv 32 := 0x000980e7.
Lemma F_18e24 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f54 : word) = Some W_18e24.
Proof. vm_refl. Qed.
Lemma D_18e24 : decode_any W_18e24 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e28 : bv 32 := 0x00040513.
Lemma F_18e28 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f58 : word) = Some W_18e28.
Proof. vm_refl. Qed.
Lemma D_18e28 : decode_any W_18e28 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e2c : bv 32 := 0x035070ef.
Lemma F_18e2c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f5c : word) = Some W_18e2c.
Proof. vm_refl. Qed.
Lemma D_18e2c : decode_any W_18e2c = Some (Jal 1 30772, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e30 : bv 32 := 0x00892503.
Lemma F_18e30 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f60 : word) = Some W_18e30.
Proof. vm_refl. Qed.
Lemma D_18e30 : decode_any W_18e30 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e34 : bv 32 := 0xfff5061b.
Lemma F_18e34 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f64 : word) = Some W_18e34.
Proof. vm_refl. Qed.
Lemma D_18e34 : decode_any W_18e34 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e38 : bv 32 := 0x00c92423.
Lemma F_18e38 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f68 : word) = Some W_18e38.
Proof. vm_refl. Qed.
Lemma D_18e38 : decode_any W_18e38 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e3c : bv 32 := 0xfca044e3.
Lemma F_18e3c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f6c : word) = Some W_18e3c.
Proof. vm_refl. Qed.
Lemma D_18e3c : decode_any W_18e3c = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e40 : bv 32 := 0x01093503.
Lemma F_18e40 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f70 : word) = Some W_18e40.
Proof. vm_refl. Qed.
Lemma D_18e40 : decode_any W_18e40 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e44 : bv 32 := 0xfa1ff06f.
Lemma F_18e44 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f74 : word) = Some W_18e44.
Proof. vm_refl. Qed.
Lemma D_18e44 : decode_any W_18e44 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e48 : bv 32 := 0x00100513.
Lemma F_18e48 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f78 : word) = Some W_18e48.
Proof. vm_refl. Qed.
Lemma D_18e48 : decode_any W_18e48 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e4c : bv 32 := 0x00a90023.
Lemma F_18e4c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f7c : word) = Some W_18e4c.
Proof. vm_refl. Qed.
Lemma D_18e4c : decode_any W_18e4c = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e50 : bv 32 := 0x00040513.
Lemma F_18e50 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f80 : word) = Some W_18e50.
Proof. vm_refl. Qed.
Lemma D_18e50 : decode_any W_18e50 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e54 : bv 32 := 0x02813083.
Lemma F_18e54 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f84 : word) = Some W_18e54.
Proof. vm_refl. Qed.
Lemma D_18e54 : decode_any W_18e54 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e58 : bv 32 := 0x02013403.
Lemma F_18e58 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f88 : word) = Some W_18e58.
Proof. vm_refl. Qed.
Lemma D_18e58 : decode_any W_18e58 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e5c : bv 32 := 0x01813483.
Lemma F_18e5c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f8c : word) = Some W_18e5c.
Proof. vm_refl. Qed.
Lemma D_18e5c : decode_any W_18e5c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e60 : bv 32 := 0x01013903.
Lemma F_18e60 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f90 : word) = Some W_18e60.
Proof. vm_refl. Qed.
Lemma D_18e60 : decode_any W_18e60 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e64 : bv 32 := 0x00813983.
Lemma F_18e64 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f94 : word) = Some W_18e64.
Proof. vm_refl. Qed.
Lemma D_18e64 : decode_any W_18e64 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e68 : bv 32 := 0x03010113.
Lemma F_18e68 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f98 : word) = Some W_18e68.
Proof. vm_refl. Qed.
Lemma D_18e68 : decode_any W_18e68 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e6c : bv 32 := 0x27d0706f.
Lemma F_18e6c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18f9c : word) = Some W_18e6c.
Proof. vm_refl. Qed.
Lemma D_18e6c : decode_any W_18e6c = Some (Jal 0 31356, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e70 : bv 32 := 0x00008067.
Lemma F_18e70 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x18fa0 : word) = Some W_18e70.
Proof. vm_refl. Qed.
Lemma D_18e70 : decode_any W_18e70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f38 : bv 32 := 0x00050067.
Lemma F_18f38 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19068 : word) = Some W_18f38.
Proof. vm_refl. Qed.
Lemma D_18f38 : decode_any W_18f38 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f3c : bv 32 := 0x00008067.
Lemma F_18f3c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1906c : word) = Some W_18f3c.
Proof. vm_refl. Qed.
Lemma D_18f3c : decode_any W_18f3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f40 : bv 32 := 0xfe010113.
Lemma F_18f40 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19070 : word) = Some W_18f40.
Proof. vm_refl. Qed.
Lemma D_18f40 : decode_any W_18f40 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f44 : bv 32 := 0x00113c23.
Lemma F_18f44 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19074 : word) = Some W_18f44.
Proof. vm_refl. Qed.
Lemma D_18f44 : decode_any W_18f44 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f48 : bv 32 := 0x00813823.
Lemma F_18f48 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19078 : word) = Some W_18f48.
Proof. vm_refl. Qed.
Lemma D_18f48 : decode_any W_18f48 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f4c : bv 32 := 0x00913423.
Lemma F_18f4c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1907c : word) = Some W_18f4c.
Proof. vm_refl. Qed.
Lemma D_18f4c : decode_any W_18f4c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f50 : bv 32 := 0x00009517.
Lemma F_18f50 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19080 : word) = Some W_18f50.
Proof. vm_refl. Qed.
Lemma D_18f50 : decode_any W_18f50 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f54 : bv 32 := 0x00009597.
Lemma F_18f54 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19084 : word) = Some W_18f54.
Proof. vm_refl. Qed.
Lemma D_18f54 : decode_any W_18f54 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f58 : bv 32 := 0xb8853503.
Lemma F_18f58 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19088 : word) = Some W_18f58.
Proof. vm_refl. Qed.
Lemma D_18f58 : decode_any W_18f58 = Some (Load SZ8 true 10 10 2952, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f5c : bv 32 := 0xb8c5b403.
Lemma F_18f5c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1908c : word) = Some W_18f5c.
Proof. vm_refl. Qed.
Lemma D_18f5c : decode_any W_18f5c = Some (Load SZ8 true 8 11 2956, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f60 : bv 32 := 0x00a47c63.
Lemma F_18f60 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19090 : word) = Some W_18f60.
Proof. vm_refl. Qed.
Lemma D_18f60 : decode_any W_18f60 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f64 : bv 32 := 0xff853583.
Lemma F_18f64 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19094 : word) = Some W_18f64.
Proof. vm_refl. Qed.
Lemma D_18f64 : decode_any W_18f64 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f68 : bv 32 := 0xff850493.
Lemma F_18f68 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19098 : word) = Some W_18f68.
Proof. vm_refl. Qed.
Lemma D_18f68 : decode_any W_18f68 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f6c : bv 32 := 0x000580e7.
Lemma F_18f6c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1909c : word) = Some W_18f6c.
Proof. vm_refl. Qed.
Lemma D_18f6c : decode_any W_18f6c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f70 : bv 32 := 0x00048513.
Lemma F_18f70 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190a0 : word) = Some W_18f70.
Proof. vm_refl. Qed.
Lemma D_18f70 : decode_any W_18f70 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f74 : bv 32 := 0xfe9468e3.
Lemma F_18f74 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190a4 : word) = Some W_18f74.
Proof. vm_refl. Qed.
Lemma D_18f74 : decode_any W_18f74 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f78 : bv 32 := 0x01813083.
Lemma F_18f78 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190a8 : word) = Some W_18f78.
Proof. vm_refl. Qed.
Lemma D_18f78 : decode_any W_18f78 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f7c : bv 32 := 0x01013403.
Lemma F_18f7c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190ac : word) = Some W_18f7c.
Proof. vm_refl. Qed.
Lemma D_18f7c : decode_any W_18f7c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f80 : bv 32 := 0x00813483.
Lemma F_18f80 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190b0 : word) = Some W_18f80.
Proof. vm_refl. Qed.
Lemma D_18f80 : decode_any W_18f80 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f84 : bv 32 := 0x02010113.
Lemma F_18f84 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190b4 : word) = Some W_18f84.
Proof. vm_refl. Qed.
Lemma D_18f84 : decode_any W_18f84 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f88 : bv 32 := 0xfb5ff06f.
Lemma F_18f88 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190b8 : word) = Some W_18f88.
Proof. vm_refl. Qed.
Lemma D_18f88 : decode_any W_18f88 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f8c : bv 32 := 0xff010113.
Lemma F_18f8c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190bc : word) = Some W_18f8c.
Proof. vm_refl. Qed.
Lemma D_18f8c : decode_any W_18f8c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f90 : bv 32 := 0x00113423.
Lemma F_18f90 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190c0 : word) = Some W_18f90.
Proof. vm_refl. Qed.
Lemma D_18f90 : decode_any W_18f90 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f94 : bv 32 := 0x00813023.
Lemma F_18f94 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190c4 : word) = Some W_18f94.
Proof. vm_refl. Qed.
Lemma D_18f94 : decode_any W_18f94 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f98 : bv 32 := 0x00000593.
Lemma F_18f98 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190c8 : word) = Some W_18f98.
Proof. vm_refl. Qed.
Lemma D_18f98 : decode_any W_18f98 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f9c : bv 32 := 0x00020613.
Lemma F_18f9c : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190cc : word) = Some W_18f9c.
Proof. vm_refl. Qed.
Lemma D_18f9c : decode_any W_18f9c = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fa0 : bv 32 := 0xf5862603.
Lemma F_18fa0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190d0 : word) = Some W_18fa0.
Proof. vm_refl. Qed.
Lemma D_18fa0 : decode_any W_18fa0 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fa4 : bv 32 := 0x0007a697.
Lemma F_18fa4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190d4 : word) = Some W_18fa4.
Proof. vm_refl. Qed.
Lemma D_18fa4 : decode_any W_18fa4 = Some (Auipc 13 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fa8 : bv 32 := 0x10c68693.
Lemma F_18fa8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190d8 : word) = Some W_18fa8.
Proof. vm_refl. Qed.
Lemma D_18fa8 : decode_any W_18fa8 = Some (OpImm ALU_ADD 13 13 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fac : bv 32 := 0x1606a72f.
Lemma F_18fac : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190dc : word) = Some W_18fac.
Proof. vm_refl. Qed.
Lemma D_18fac : decode_any W_18fac = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fb0 : bv 32 := 0x00b71663.
Lemma F_18fb0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190e0 : word) = Some W_18fb0.
Proof. vm_refl. Qed.
Lemma D_18fb0 : decode_any W_18fb0 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fb4 : bv 32 := 0x1ec6a7af.
Lemma F_18fb4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190e4 : word) = Some W_18fb4.
Proof. vm_refl. Qed.
Lemma D_18fb4 : decode_any W_18fb4 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fb8 : bv 32 := 0xfe079ae3.
Lemma F_18fb8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190e8 : word) = Some W_18fb8.
Proof. vm_refl. Qed.
Lemma D_18fb8 : decode_any W_18fb8 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fbc : bv 32 := 0x0007059b.
Lemma F_18fbc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190ec : word) = Some W_18fbc.
Proof. vm_refl. Qed.
Lemma D_18fbc : decode_any W_18fbc = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fc0 : bv 32 := 0x02c58263.
Lemma F_18fc0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190f0 : word) = Some W_18fc0.
Proof. vm_refl. Qed.
Lemma D_18fc0 : decode_any W_18fc0 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fc4 : bv 32 := 0x02058263.
Lemma F_18fc4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190f4 : word) = Some W_18fc4.
Proof. vm_refl. Qed.
Lemma D_18fc4 : decode_any W_18fc4 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fc8 : bv 32 := 0x04900893.
Lemma F_18fc8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190f8 : word) = Some W_18fc8.
Proof. vm_refl. Qed.
Lemma D_18fc8 : decode_any W_18fc8 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fcc : bv 32 := 0x00000593.
Lemma F_18fcc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x190fc : word) = Some W_18fcc.
Proof. vm_refl. Qed.
Lemma D_18fcc : decode_any W_18fcc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fd0 : bv 32 := 0x00000613.
Lemma F_18fd0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19100 : word) = Some W_18fd0.
Proof. vm_refl. Qed.
Lemma D_18fd0 : decode_any W_18fd0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fd4 : bv 32 := 0x00000693.
Lemma F_18fd4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19104 : word) = Some W_18fd4.
Proof. vm_refl. Qed.
Lemma D_18fd4 : decode_any W_18fd4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fd8 : bv 32 := 0x00000513.
Lemma F_18fd8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19108 : word) = Some W_18fd8.
Proof. vm_refl. Qed.
Lemma D_18fd8 : decode_any W_18fd8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fdc : bv 32 := 0x00000073.
Lemma F_18fdc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1910c : word) = Some W_18fdc.
Proof. vm_refl. Qed.
Lemma D_18fdc : decode_any W_18fdc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_18fdc : is_ecall W_18fdc = true.
Proof. reflexivity. Qed.

Definition W_18fe0 : bv 32 := 0xff9ff06f.
Lemma F_18fe0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19110 : word) = Some W_18fe0.
Proof. vm_refl. Qed.
Lemma D_18fe0 : decode_any W_18fe0 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fe4 : bv 32 := 0x00000023.
Lemma F_18fe4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19114 : word) = Some W_18fe4.
Proof. vm_refl. Qed.
Lemma D_18fe4 : decode_any W_18fe4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fe8 : bv 32 := 0x00050413.
Lemma F_18fe8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19118 : word) = Some W_18fe8.
Proof. vm_refl. Qed.
Lemma D_18fe8 : decode_any W_18fe8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18fec : bv 32 := 0xdbdff0ef.
Lemma F_18fec : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1911c : word) = Some W_18fec.
Proof. vm_refl. Qed.
Lemma D_18fec : decode_any W_18fec = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ff0 : bv 32 := 0xf51ff0ef.
Lemma F_18ff0 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19120 : word) = Some W_18ff0.
Proof. vm_refl. Qed.
Lemma D_18ff0 : decode_any W_18ff0 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ff4 : bv 32 := 0x258020ef.
Lemma F_18ff4 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19124 : word) = Some W_18ff4.
Proof. vm_refl. Qed.
Lemma D_18ff4 : decode_any W_18ff4 = Some (Jal 1 8792, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ff8 : bv 32 := 0x00040513.
Lemma F_18ff8 : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x19128 : word) = Some W_18ff8.
Proof. vm_refl. Qed.
Lemma D_18ff8 : decode_any W_18ff8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ffc : bv 32 := 0x004000ef.
Lemma F_18ffc : fetch_word Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments (0x1912c : word) = Some W_18ffc.
Proof. vm_refl. Qed.
Lemma D_18ffc : decode_any W_18ffc = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.
