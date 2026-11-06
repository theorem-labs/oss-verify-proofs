(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.H Require GcFlushU21.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_137f0 : bv 32 := 0xffffe517.
Lemma F_137f0 : fetch_word Ubsan.M.loaded_segments (0x137f0 : word) = Some W_137f0.
Proof. vm_refl. Qed.
Lemma D_137f0 : decode_any W_137f0 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_137f4 : bv 32 := 0x55050513.
Lemma F_137f4 : fetch_word Ubsan.M.loaded_segments (0x137f4 : word) = Some W_137f4.
Proof. vm_refl. Qed.
Lemma D_137f4 : decode_any W_137f4 = Some (OpImm ALU_ADD 10 10 1360, 4%Z).
Proof. vm_refl. Qed.

Definition W_137f8 : bv 32 := 0x0000f597.
Lemma F_137f8 : fetch_word Ubsan.M.loaded_segments (0x137f8 : word) = Some W_137f8.
Proof. vm_refl. Qed.
Lemma D_137f8 : decode_any W_137f8 = Some (Auipc 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_137fc : bv 32 := 0x8e058593.
Lemma F_137fc : fetch_word Ubsan.M.loaded_segments (0x137fc : word) = Some W_137fc.
Proof. vm_refl. Qed.
Lemma D_137fc : decode_any W_137fc = Some (OpImm ALU_ADD 11 11 2272, 4%Z).
Proof. vm_refl. Qed.

Definition W_13800 : bv 32 := 0x000000ef.
Lemma F_13800 : fetch_word Ubsan.M.loaded_segments (0x13800 : word) = Some W_13800.
Proof. vm_refl. Qed.
Lemma D_13800 : decode_any W_13800 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13804 : bv 32 := 0x0040006f.
Lemma F_13804 : fetch_word Ubsan.M.loaded_segments (0x13804 : word) = Some W_13804.
Proof. vm_refl. Qed.
Lemma D_13804 : decode_any W_13804 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13808 : bv 32 := 0x00813083.
Lemma F_13808 : fetch_word Ubsan.M.loaded_segments (0x13808 : word) = Some W_13808.
Proof. vm_refl. Qed.
Lemma D_13808 : decode_any W_13808 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1380c : bv 32 := 0x00013403.
Lemma F_1380c : fetch_word Ubsan.M.loaded_segments (0x1380c : word) = Some W_1380c.
Proof. vm_refl. Qed.
Lemma D_1380c : decode_any W_1380c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13810 : bv 32 := 0x01010113.
Lemma F_13810 : fetch_word Ubsan.M.loaded_segments (0x13810 : word) = Some W_13810.
Proof. vm_refl. Qed.
Lemma D_13810 : decode_any W_13810 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13814 : bv 32 := 0x00008067.
Lemma F_13814 : fetch_word Ubsan.M.loaded_segments (0x13814 : word) = Some W_13814.
Proof. vm_refl. Qed.
Lemma D_13814 : decode_any W_13814 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13818 : bv 32 := 0xff010113.
Lemma F_13818 : fetch_word Ubsan.M.loaded_segments (0x13818 : word) = Some W_13818.
Proof. vm_refl. Qed.
Lemma D_13818 : decode_any W_13818 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1381c : bv 32 := 0x00113423.
Lemma F_1381c : fetch_word Ubsan.M.loaded_segments (0x1381c : word) = Some W_1381c.
Proof. vm_refl. Qed.
Lemma D_1381c : decode_any W_1381c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13820 : bv 32 := 0x00813023.
Lemma F_13820 : fetch_word Ubsan.M.loaded_segments (0x13820 : word) = Some W_13820.
Proof. vm_refl. Qed.
Lemma D_13820 : decode_any W_13820 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13824 : bv 32 := 0x01010413.
Lemma F_13824 : fetch_word Ubsan.M.loaded_segments (0x13824 : word) = Some W_13824.
Proof. vm_refl. Qed.
Lemma D_13824 : decode_any W_13824 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13828 : bv 32 := 0x0000f517.
Lemma F_13828 : fetch_word Ubsan.M.loaded_segments (0x13828 : word) = Some W_13828.
Proof. vm_refl. Qed.
Lemma D_13828 : decode_any W_13828 = Some (Auipc 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_1382c : bv 32 := 0x8f050513.
Lemma F_1382c : fetch_word Ubsan.M.loaded_segments (0x1382c : word) = Some W_1382c.
Proof. vm_refl. Qed.
Lemma D_1382c : decode_any W_1382c = Some (OpImm ALU_ADD 10 10 2288, 4%Z).
Proof. vm_refl. Qed.

Definition W_13830 : bv 32 := 0x00054503.
Lemma F_13830 : fetch_word Ubsan.M.loaded_segments (0x13830 : word) = Some W_13830.
Proof. vm_refl. Qed.
Lemma D_13830 : decode_any W_13830 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13834 : bv 32 := 0x00157513.
Lemma F_13834 : fetch_word Ubsan.M.loaded_segments (0x13834 : word) = Some W_13834.
Proof. vm_refl. Qed.
Lemma D_13834 : decode_any W_13834 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13838 : bv 32 := 0x00050663.
Lemma F_13838 : fetch_word Ubsan.M.loaded_segments (0x13838 : word) = Some W_13838.
Proof. vm_refl. Qed.
Lemma D_13838 : decode_any W_13838 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1383c : bv 32 := 0x0040006f.
Lemma F_1383c : fetch_word Ubsan.M.loaded_segments (0x1383c : word) = Some W_1383c.
Proof. vm_refl. Qed.
Lemma D_1383c : decode_any W_1383c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13840 : bv 32 := 0x0580006f.
Lemma F_13840 : fetch_word Ubsan.M.loaded_segments (0x13840 : word) = Some W_13840.
Proof. vm_refl. Qed.
Lemma D_13840 : decode_any W_13840 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_13844 : bv 32 := 0x0000f517.
Lemma F_13844 : fetch_word Ubsan.M.loaded_segments (0x13844 : word) = Some W_13844.
Proof. vm_refl. Qed.
Lemma D_13844 : decode_any W_13844 = Some (Auipc 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_13848 : bv 32 := 0x8d450593.
Lemma F_13848 : fetch_word Ubsan.M.loaded_segments (0x13848 : word) = Some W_13848.
Proof. vm_refl. Qed.
Lemma D_13848 : decode_any W_13848 = Some (OpImm ALU_ADD 11 10 2260, 4%Z).
Proof. vm_refl. Qed.

Definition W_1384c : bv 32 := 0x00100513.
Lemma F_1384c : fetch_word Ubsan.M.loaded_segments (0x1384c : word) = Some W_1384c.
Proof. vm_refl. Qed.
Lemma D_1384c : decode_any W_1384c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13850 : bv 32 := 0x00a58023.
Lemma F_13850 : fetch_word Ubsan.M.loaded_segments (0x13850 : word) = Some W_13850.
Proof. vm_refl. Qed.
Lemma D_13850 : decode_any W_13850 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13854 : bv 32 := 0x0000d517.
Lemma F_13854 : fetch_word Ubsan.M.loaded_segments (0x13854 : word) = Some W_13854.
Proof. vm_refl. Qed.
Lemma D_13854 : decode_any W_13854 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13858 : bv 32 := 0x5dc53503.
Lemma F_13858 : fetch_word Ubsan.M.loaded_segments (0x13858 : word) = Some W_13858.
Proof. vm_refl. Qed.
Lemma D_13858 : decode_any W_13858 = Some (Load SZ8 true 10 10 1500, 4%Z).
Proof. vm_refl. Qed.

Definition W_1385c : bv 32 := 0x00050e63.
Lemma F_1385c : fetch_word Ubsan.M.loaded_segments (0x1385c : word) = Some W_1385c.
Proof. vm_refl. Qed.
Lemma D_1385c : decode_any W_1385c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_13860 : bv 32 := 0x0040006f.
Lemma F_13860 : fetch_word Ubsan.M.loaded_segments (0x13860 : word) = Some W_13860.
Proof. vm_refl. Qed.
Lemma D_13860 : decode_any W_13860 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13864 : bv 32 := 0x0000e517.
Lemma F_13864 : fetch_word Ubsan.M.loaded_segments (0x13864 : word) = Some W_13864.
Proof. vm_refl. Qed.
Lemma D_13864 : decode_any W_13864 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_13868 : bv 32 := 0x63c50513.
Lemma F_13868 : fetch_word Ubsan.M.loaded_segments (0x13868 : word) = Some W_13868.
Proof. vm_refl. Qed.
Lemma D_13868 : decode_any W_13868 = Some (OpImm ALU_ADD 10 10 1596, 4%Z).
Proof. vm_refl. Qed.

Definition W_1386c : bv 32 := 0x00053503.
Lemma F_1386c : fetch_word Ubsan.M.loaded_segments (0x1386c : word) = Some W_1386c.
Proof. vm_refl. Qed.
Lemma D_1386c : decode_any W_1386c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13870 : bv 32 := 0x648040ef.
Lemma F_13870 : fetch_word Ubsan.M.loaded_segments (0x13870 : word) = Some W_13870.
Proof. vm_refl. Qed.
Lemma D_13870 : decode_any W_13870 = Some (Jal 1 17992, 4%Z).
Proof. vm_refl. Qed.

Definition W_13874 : bv 32 := 0x0040006f.
Lemma F_13874 : fetch_word Ubsan.M.loaded_segments (0x13874 : word) = Some W_13874.
Proof. vm_refl. Qed.
Lemma D_13874 : decode_any W_13874 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13878 : bv 32 := 0x0000d517.
Lemma F_13878 : fetch_word Ubsan.M.loaded_segments (0x13878 : word) = Some W_13878.
Proof. vm_refl. Qed.
Lemma D_13878 : decode_any W_13878 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1387c : bv 32 := 0x5c053503.
Lemma F_1387c : fetch_word Ubsan.M.loaded_segments (0x1387c : word) = Some W_1387c.
Proof. vm_refl. Qed.
Lemma D_1387c : decode_any W_1387c = Some (Load SZ8 true 10 10 1472, 4%Z).
Proof. vm_refl. Qed.

Definition W_13880 : bv 32 := 0x00050c63.
Lemma F_13880 : fetch_word Ubsan.M.loaded_segments (0x13880 : word) = Some W_13880.
Proof. vm_refl. Qed.
Lemma D_13880 : decode_any W_13880 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13884 : bv 32 := 0x0040006f.
Lemma F_13884 : fetch_word Ubsan.M.loaded_segments (0x13884 : word) = Some W_13884.
Proof. vm_refl. Qed.
Lemma D_13884 : decode_any W_13884 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13888 : bv 32 := 0xffffe517.
Lemma F_13888 : fetch_word Ubsan.M.loaded_segments (0x13888 : word) = Some W_13888.
Proof. vm_refl. Qed.
Lemma D_13888 : decode_any W_13888 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_1388c : bv 32 := 0x4b850513.
Lemma F_1388c : fetch_word Ubsan.M.loaded_segments (0x1388c : word) = Some W_1388c.
Proof. vm_refl. Qed.
Lemma D_1388c : decode_any W_1388c = Some (OpImm ALU_ADD 10 10 1208, 4%Z).
Proof. vm_refl. Qed.

Definition W_13890 : bv 32 := 0x000000ef.
Lemma F_13890 : fetch_word Ubsan.M.loaded_segments (0x13890 : word) = Some W_13890.
Proof. vm_refl. Qed.
Lemma D_13890 : decode_any W_13890 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13894 : bv 32 := 0x0040006f.
Lemma F_13894 : fetch_word Ubsan.M.loaded_segments (0x13894 : word) = Some W_13894.
Proof. vm_refl. Qed.
Lemma D_13894 : decode_any W_13894 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13898 : bv 32 := 0x00813083.
Lemma F_13898 : fetch_word Ubsan.M.loaded_segments (0x13898 : word) = Some W_13898.
Proof. vm_refl. Qed.
Lemma D_13898 : decode_any W_13898 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1389c : bv 32 := 0x00013403.
Lemma F_1389c : fetch_word Ubsan.M.loaded_segments (0x1389c : word) = Some W_1389c.
Proof. vm_refl. Qed.
Lemma D_1389c : decode_any W_1389c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_138a0 : bv 32 := 0x01010113.
Lemma F_138a0 : fetch_word Ubsan.M.loaded_segments (0x138a0 : word) = Some W_138a0.
Proof. vm_refl. Qed.
Lemma D_138a0 : decode_any W_138a0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_138a4 : bv 32 := 0x00008067.
Lemma F_138a4 : fetch_word Ubsan.M.loaded_segments (0x138a4 : word) = Some W_138a4.
Proof. vm_refl. Qed.
Lemma D_138a4 : decode_any W_138a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cd0 : bv 32 := 0x0001e517.
Lemma F_13cd0 : fetch_word Ubsan.M.loaded_segments (0x13cd0 : word) = Some W_13cd0.
Proof. vm_refl. Qed.
Lemma D_13cd0 : decode_any W_13cd0 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cd4 : bv 32 := 0x45454503.
Lemma F_13cd4 : fetch_word Ubsan.M.loaded_segments (0x13cd4 : word) = Some W_13cd4.
Proof. vm_refl. Qed.
Lemma D_13cd4 : decode_any W_13cd4 = Some (Load SZ1 false 10 10 1108, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cd8 : bv 32 := 0x00051463.
Lemma F_13cd8 : fetch_word Ubsan.M.loaded_segments (0x13cd8 : word) = Some W_13cd8.
Proof. vm_refl. Qed.
Lemma D_13cd8 : decode_any W_13cd8 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cdc : bv 32 := 0x00008067.
Lemma F_13cdc : fetch_word Ubsan.M.loaded_segments (0x13cdc : word) = Some W_13cdc.
Proof. vm_refl. Qed.
Lemma D_13cdc : decode_any W_13cdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce0 : bv 32 := 0xff010113.
Lemma F_13ce0 : fetch_word Ubsan.M.loaded_segments (0x13ce0 : word) = Some W_13ce0.
Proof. vm_refl. Qed.
Lemma D_13ce0 : decode_any W_13ce0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce4 : bv 32 := 0x00113423.
Lemma F_13ce4 : fetch_word Ubsan.M.loaded_segments (0x13ce4 : word) = Some W_13ce4.
Proof. vm_refl. Qed.
Lemma D_13ce4 : decode_any W_13ce4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13ce8 : bv 32 := 0x0000d517.
Lemma F_13ce8 : fetch_word Ubsan.M.loaded_segments (0x13ce8 : word) = Some W_13ce8.
Proof. vm_refl. Qed.
Lemma D_13ce8 : decode_any W_13ce8 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cec : bv 32 := 0x16853503.
Lemma F_13cec : fetch_word Ubsan.M.loaded_segments (0x13cec : word) = Some W_13cec.
Proof. vm_refl. Qed.
Lemma D_13cec : decode_any W_13cec = Some (Load SZ8 true 10 10 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cf0 : bv 32 := 0x00053503.
Lemma F_13cf0 : fetch_word Ubsan.M.loaded_segments (0x13cf0 : word) = Some W_13cf0.
Proof. vm_refl. Qed.
Lemma D_13cf0 : decode_any W_13cf0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cf4 : bv 32 := 0x338060ef.
Lemma F_13cf4 : fetch_word Ubsan.M.loaded_segments (0x13cf4 : word) = Some W_13cf4.
Proof. vm_refl. Qed.
Lemma D_13cf4 : decode_any W_13cf4 = Some (Jal 1 25400, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cf8 : bv 32 := 0x04d00513.
Lemma F_13cf8 : fetch_word Ubsan.M.loaded_segments (0x13cf8 : word) = Some W_13cf8.
Proof. vm_refl. Qed.
Lemma D_13cf8 : decode_any W_13cf8 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_13cfc : bv 32 := 0x0440c0ef.
Lemma F_13cfc : fetch_word Ubsan.M.loaded_segments (0x13cfc : word) = Some W_13cfc.
Proof. vm_refl. Qed.
Lemma D_13cfc : decode_any W_13cfc = Some (Jal 1 49220, 4%Z).
Proof. vm_refl. Qed.

Definition W_17df0 : bv 32 := 0xfd010113.
Lemma F_17df0 : fetch_word Ubsan.M.loaded_segments (0x17df0 : word) = Some W_17df0.
Proof. vm_refl. Qed.
Lemma D_17df0 : decode_any W_17df0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_17df4 : bv 32 := 0x02113423.
Lemma F_17df4 : fetch_word Ubsan.M.loaded_segments (0x17df4 : word) = Some W_17df4.
Proof. vm_refl. Qed.
Lemma D_17df4 : decode_any W_17df4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17df8 : bv 32 := 0x02813023.
Lemma F_17df8 : fetch_word Ubsan.M.loaded_segments (0x17df8 : word) = Some W_17df8.
Proof. vm_refl. Qed.
Lemma D_17df8 : decode_any W_17df8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17dfc : bv 32 := 0x00913c23.
Lemma F_17dfc : fetch_word Ubsan.M.loaded_segments (0x17dfc : word) = Some W_17dfc.
Proof. vm_refl. Qed.
Lemma D_17dfc : decode_any W_17dfc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e00 : bv 32 := 0x01213823.
Lemma F_17e00 : fetch_word Ubsan.M.loaded_segments (0x17e00 : word) = Some W_17e00.
Proof. vm_refl. Qed.
Lemma D_17e00 : decode_any W_17e00 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e04 : bv 32 := 0x01313423.
Lemma F_17e04 : fetch_word Ubsan.M.loaded_segments (0x17e04 : word) = Some W_17e04.
Proof. vm_refl. Qed.
Lemma D_17e04 : decode_any W_17e04 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e08 : bv 32 := 0x0003a517.
Lemma F_17e08 : fetch_word Ubsan.M.loaded_segments (0x17e08 : word) = Some W_17e08.
Proof. vm_refl. Qed.
Lemma D_17e08 : decode_any W_17e08 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e0c : bv 32 := 0x45850913.
Lemma F_17e0c : fetch_word Ubsan.M.loaded_segments (0x17e0c : word) = Some W_17e0c.
Proof. vm_refl. Qed.
Lemma D_17e0c : decode_any W_17e0c = Some (OpImm ALU_ADD 18 10 1112, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e10 : bv 32 := 0x00490413.
Lemma F_17e10 : fetch_word Ubsan.M.loaded_segments (0x17e10 : word) = Some W_17e10.
Proof. vm_refl. Qed.
Lemma D_17e10 : decode_any W_17e10 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e14 : bv 32 := 0x00040513.
Lemma F_17e14 : fetch_word Ubsan.M.loaded_segments (0x17e14 : word) = Some W_17e14.
Proof. vm_refl. Qed.
Lemma D_17e14 : decode_any W_17e14 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e18 : bv 32 := 0x3f9070ef.
Lemma F_17e18 : fetch_word Ubsan.M.loaded_segments (0x17e18 : word) = Some W_17e18.
Proof. vm_refl. Qed.
Lemma D_17e18 : decode_any W_17e18 = Some (Jal 1 31736, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e1c : bv 32 := 0x01093503.
Lemma F_17e1c : fetch_word Ubsan.M.loaded_segments (0x17e1c : word) = Some W_17e1c.
Proof. vm_refl. Qed.
Lemma D_17e1c : decode_any W_17e1c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e20 : bv 32 := 0x06050863.
Lemma F_17e20 : fetch_word Ubsan.M.loaded_segments (0x17e20 : word) = Some W_17e20.
Proof. vm_refl. Qed.
Lemma D_17e20 : decode_any W_17e20 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e24 : bv 32 := 0x00892583.
Lemma F_17e24 : fetch_word Ubsan.M.loaded_segments (0x17e24 : word) = Some W_17e24.
Proof. vm_refl. Qed.
Lemma D_17e24 : decode_any W_17e24 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e28 : bv 32 := 0x0180006f.
Lemma F_17e28 : fetch_word Ubsan.M.loaded_segments (0x17e28 : word) = Some W_17e28.
Proof. vm_refl. Qed.
Lemma D_17e28 : decode_any W_17e28 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e2c : bv 32 := 0x00053503.
Lemma F_17e2c : fetch_word Ubsan.M.loaded_segments (0x17e2c : word) = Some W_17e2c.
Proof. vm_refl. Qed.
Lemma D_17e2c : decode_any W_17e2c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e30 : bv 32 := 0x02000593.
Lemma F_17e30 : fetch_word Ubsan.M.loaded_segments (0x17e30 : word) = Some W_17e30.
Proof. vm_refl. Qed.
Lemma D_17e30 : decode_any W_17e30 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e34 : bv 32 := 0x00b92423.
Lemma F_17e34 : fetch_word Ubsan.M.loaded_segments (0x17e34 : word) = Some W_17e34.
Proof. vm_refl. Qed.
Lemma D_17e34 : decode_any W_17e34 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e38 : bv 32 := 0x00a93823.
Lemma F_17e38 : fetch_word Ubsan.M.loaded_segments (0x17e38 : word) = Some W_17e38.
Proof. vm_refl. Qed.
Lemma D_17e38 : decode_any W_17e38 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e3c : bv 32 := 0x04050a63.
Lemma F_17e3c : fetch_word Ubsan.M.loaded_segments (0x17e3c : word) = Some W_17e3c.
Proof. vm_refl. Qed.
Lemma D_17e3c : decode_any W_17e3c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e40 : bv 32 := 0xfff5861b.
Lemma F_17e40 : fetch_word Ubsan.M.loaded_segments (0x17e40 : word) = Some W_17e40.
Proof. vm_refl. Qed.
Lemma D_17e40 : decode_any W_17e40 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e44 : bv 32 := 0x00c92423.
Lemma F_17e44 : fetch_word Ubsan.M.loaded_segments (0x17e44 : word) = Some W_17e44.
Proof. vm_refl. Qed.
Lemma D_17e44 : decode_any W_17e44 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e48 : bv 32 := 0xfeb052e3.
Lemma F_17e48 : fetch_word Ubsan.M.loaded_segments (0x17e48 : word) = Some W_17e48.
Proof. vm_refl. Qed.
Lemma D_17e48 : decode_any W_17e48 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e4c : bv 32 := 0x01093503.
Lemma F_17e4c : fetch_word Ubsan.M.loaded_segments (0x17e4c : word) = Some W_17e4c.
Proof. vm_refl. Qed.
Lemma D_17e4c : decode_any W_17e4c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e50 : bv 32 := 0x00361613.
Lemma F_17e50 : fetch_word Ubsan.M.loaded_segments (0x17e50 : word) = Some W_17e50.
Proof. vm_refl. Qed.
Lemma D_17e50 : decode_any W_17e50 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e54 : bv 32 := 0x00c50533.
Lemma F_17e54 : fetch_word Ubsan.M.loaded_segments (0x17e54 : word) = Some W_17e54.
Proof. vm_refl. Qed.
Lemma D_17e54 : decode_any W_17e54 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e58 : bv 32 := 0x00853983.
Lemma F_17e58 : fetch_word Ubsan.M.loaded_segments (0x17e58 : word) = Some W_17e58.
Proof. vm_refl. Qed.
Lemma D_17e58 : decode_any W_17e58 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e5c : bv 32 := 0x10853483.
Lemma F_17e5c : fetch_word Ubsan.M.loaded_segments (0x17e5c : word) = Some W_17e5c.
Proof. vm_refl. Qed.
Lemma D_17e5c : decode_any W_17e5c = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e60 : bv 32 := 0x00040513.
Lemma F_17e60 : fetch_word Ubsan.M.loaded_segments (0x17e60 : word) = Some W_17e60.
Proof. vm_refl. Qed.
Lemma D_17e60 : decode_any W_17e60 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e64 : bv 32 := 0x635070ef.
Lemma F_17e64 : fetch_word Ubsan.M.loaded_segments (0x17e64 : word) = Some W_17e64.
Proof. vm_refl. Qed.
Lemma D_17e64 : decode_any W_17e64 = Some (Jal 1 32308, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e68 : bv 32 := 0x00048513.
Lemma F_17e68 : fetch_word Ubsan.M.loaded_segments (0x17e68 : word) = Some W_17e68.
Proof. vm_refl. Qed.
Lemma D_17e68 : decode_any W_17e68 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e6c : bv 32 := 0x000980e7.
Lemma F_17e6c : fetch_word Ubsan.M.loaded_segments (0x17e6c : word) = Some W_17e6c.
Proof. vm_refl. Qed.
Lemma D_17e6c : decode_any W_17e6c = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e70 : bv 32 := 0x00040513.
Lemma F_17e70 : fetch_word Ubsan.M.loaded_segments (0x17e70 : word) = Some W_17e70.
Proof. vm_refl. Qed.
Lemma D_17e70 : decode_any W_17e70 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e74 : bv 32 := 0x39d070ef.
Lemma F_17e74 : fetch_word Ubsan.M.loaded_segments (0x17e74 : word) = Some W_17e74.
Proof. vm_refl. Qed.
Lemma D_17e74 : decode_any W_17e74 = Some (Jal 1 31644, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e78 : bv 32 := 0x00892503.
Lemma F_17e78 : fetch_word Ubsan.M.loaded_segments (0x17e78 : word) = Some W_17e78.
Proof. vm_refl. Qed.
Lemma D_17e78 : decode_any W_17e78 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e7c : bv 32 := 0xfff5061b.
Lemma F_17e7c : fetch_word Ubsan.M.loaded_segments (0x17e7c : word) = Some W_17e7c.
Proof. vm_refl. Qed.
Lemma D_17e7c : decode_any W_17e7c = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e80 : bv 32 := 0x00c92423.
Lemma F_17e80 : fetch_word Ubsan.M.loaded_segments (0x17e80 : word) = Some W_17e80.
Proof. vm_refl. Qed.
Lemma D_17e80 : decode_any W_17e80 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e84 : bv 32 := 0xfca044e3.
Lemma F_17e84 : fetch_word Ubsan.M.loaded_segments (0x17e84 : word) = Some W_17e84.
Proof. vm_refl. Qed.
Lemma D_17e84 : decode_any W_17e84 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e88 : bv 32 := 0x01093503.
Lemma F_17e88 : fetch_word Ubsan.M.loaded_segments (0x17e88 : word) = Some W_17e88.
Proof. vm_refl. Qed.
Lemma D_17e88 : decode_any W_17e88 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e8c : bv 32 := 0xfa1ff06f.
Lemma F_17e8c : fetch_word Ubsan.M.loaded_segments (0x17e8c : word) = Some W_17e8c.
Proof. vm_refl. Qed.
Lemma D_17e8c : decode_any W_17e8c = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e90 : bv 32 := 0x00100513.
Lemma F_17e90 : fetch_word Ubsan.M.loaded_segments (0x17e90 : word) = Some W_17e90.
Proof. vm_refl. Qed.
Lemma D_17e90 : decode_any W_17e90 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e94 : bv 32 := 0x00a90023.
Lemma F_17e94 : fetch_word Ubsan.M.loaded_segments (0x17e94 : word) = Some W_17e94.
Proof. vm_refl. Qed.
Lemma D_17e94 : decode_any W_17e94 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e98 : bv 32 := 0x00040513.
Lemma F_17e98 : fetch_word Ubsan.M.loaded_segments (0x17e98 : word) = Some W_17e98.
Proof. vm_refl. Qed.
Lemma D_17e98 : decode_any W_17e98 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17e9c : bv 32 := 0x02813083.
Lemma F_17e9c : fetch_word Ubsan.M.loaded_segments (0x17e9c : word) = Some W_17e9c.
Proof. vm_refl. Qed.
Lemma D_17e9c : decode_any W_17e9c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ea0 : bv 32 := 0x02013403.
Lemma F_17ea0 : fetch_word Ubsan.M.loaded_segments (0x17ea0 : word) = Some W_17ea0.
Proof. vm_refl. Qed.
Lemma D_17ea0 : decode_any W_17ea0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ea4 : bv 32 := 0x01813483.
Lemma F_17ea4 : fetch_word Ubsan.M.loaded_segments (0x17ea4 : word) = Some W_17ea4.
Proof. vm_refl. Qed.
Lemma D_17ea4 : decode_any W_17ea4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ea8 : bv 32 := 0x01013903.
Lemma F_17ea8 : fetch_word Ubsan.M.loaded_segments (0x17ea8 : word) = Some W_17ea8.
Proof. vm_refl. Qed.
Lemma D_17ea8 : decode_any W_17ea8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17eac : bv 32 := 0x00813983.
Lemma F_17eac : fetch_word Ubsan.M.loaded_segments (0x17eac : word) = Some W_17eac.
Proof. vm_refl. Qed.
Lemma D_17eac : decode_any W_17eac = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17eb0 : bv 32 := 0x03010113.
Lemma F_17eb0 : fetch_word Ubsan.M.loaded_segments (0x17eb0 : word) = Some W_17eb0.
Proof. vm_refl. Qed.
Lemma D_17eb0 : decode_any W_17eb0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_17eb4 : bv 32 := 0x5e50706f.
Lemma F_17eb4 : fetch_word Ubsan.M.loaded_segments (0x17eb4 : word) = Some W_17eb4.
Proof. vm_refl. Qed.
Lemma D_17eb4 : decode_any W_17eb4 = Some (Jal 0 32228, 4%Z).
Proof. vm_refl. Qed.

Definition W_17eb8 : bv 32 := 0x00008067.
Lemma F_17eb8 : fetch_word Ubsan.M.loaded_segments (0x17eb8 : word) = Some W_17eb8.
Proof. vm_refl. Qed.
Lemma D_17eb8 : decode_any W_17eb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ebc : bv 32 := 0xfd010113.
Lemma F_17ebc : fetch_word Ubsan.M.loaded_segments (0x17ebc : word) = Some W_17ebc.
Proof. vm_refl. Qed.
Lemma D_17ebc : decode_any W_17ebc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ec0 : bv 32 := 0x02113423.
Lemma F_17ec0 : fetch_word Ubsan.M.loaded_segments (0x17ec0 : word) = Some W_17ec0.
Proof. vm_refl. Qed.
Lemma D_17ec0 : decode_any W_17ec0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ec4 : bv 32 := 0x02813023.
Lemma F_17ec4 : fetch_word Ubsan.M.loaded_segments (0x17ec4 : word) = Some W_17ec4.
Proof. vm_refl. Qed.
Lemma D_17ec4 : decode_any W_17ec4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ec8 : bv 32 := 0x00913c23.
Lemma F_17ec8 : fetch_word Ubsan.M.loaded_segments (0x17ec8 : word) = Some W_17ec8.
Proof. vm_refl. Qed.
Lemma D_17ec8 : decode_any W_17ec8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ecc : bv 32 := 0x01213823.
Lemma F_17ecc : fetch_word Ubsan.M.loaded_segments (0x17ecc : word) = Some W_17ecc.
Proof. vm_refl. Qed.
Lemma D_17ecc : decode_any W_17ecc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ed0 : bv 32 := 0x01313423.
Lemma F_17ed0 : fetch_word Ubsan.M.loaded_segments (0x17ed0 : word) = Some W_17ed0.
Proof. vm_refl. Qed.
Lemma D_17ed0 : decode_any W_17ed0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ed4 : bv 32 := 0x00050493.
Lemma F_17ed4 : fetch_word Ubsan.M.loaded_segments (0x17ed4 : word) = Some W_17ed4.
Proof. vm_refl. Qed.
Lemma D_17ed4 : decode_any W_17ed4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ed8 : bv 32 := 0x0003a517.
Lemma F_17ed8 : fetch_word Ubsan.M.loaded_segments (0x17ed8 : word) = Some W_17ed8.
Proof. vm_refl. Qed.
Lemma D_17ed8 : decode_any W_17ed8 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17edc : bv 32 := 0x38850993.
Lemma F_17edc : fetch_word Ubsan.M.loaded_segments (0x17edc : word) = Some W_17edc.
Proof. vm_refl. Qed.
Lemma D_17edc : decode_any W_17edc = Some (OpImm ALU_ADD 19 10 904, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ee0 : bv 32 := 0x00498413.
Lemma F_17ee0 : fetch_word Ubsan.M.loaded_segments (0x17ee0 : word) = Some W_17ee0.
Proof. vm_refl. Qed.
Lemma D_17ee0 : decode_any W_17ee0 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ee4 : bv 32 := 0x00040513.
Lemma F_17ee4 : fetch_word Ubsan.M.loaded_segments (0x17ee4 : word) = Some W_17ee4.
Proof. vm_refl. Qed.
Lemma D_17ee4 : decode_any W_17ee4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ee8 : bv 32 := 0x329070ef.
Lemma F_17ee8 : fetch_word Ubsan.M.loaded_segments (0x17ee8 : word) = Some W_17ee8.
Proof. vm_refl. Qed.
Lemma D_17ee8 : decode_any W_17ee8 = Some (Jal 1 31528, 4%Z).
Proof. vm_refl. Qed.

Definition W_17eec : bv 32 := 0x0009c503.
Lemma F_17eec : fetch_word Ubsan.M.loaded_segments (0x17eec : word) = Some W_17eec.
Proof. vm_refl. Qed.
Lemma D_17eec : decode_any W_17eec = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ef0 : bv 32 := 0xfff00913.
Lemma F_17ef0 : fetch_word Ubsan.M.loaded_segments (0x17ef0 : word) = Some W_17ef0.
Proof. vm_refl. Qed.
Lemma D_17ef0 : decode_any W_17ef0 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ef4 : bv 32 := 0x06051263.
Lemma F_17ef4 : fetch_word Ubsan.M.loaded_segments (0x17ef4 : word) = Some W_17ef4.
Proof. vm_refl. Qed.
Lemma D_17ef4 : decode_any W_17ef4 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ef8 : bv 32 := 0x0109b503.
Lemma F_17ef8 : fetch_word Ubsan.M.loaded_segments (0x17ef8 : word) = Some W_17ef8.
Proof. vm_refl. Qed.
Lemma D_17ef8 : decode_any W_17ef8 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17efc : bv 32 := 0x00051663.
Lemma F_17efc : fetch_word Ubsan.M.loaded_segments (0x17efc : word) = Some W_17efc.
Proof. vm_refl. Qed.
Lemma D_17efc : decode_any W_17efc = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f00 : bv 32 := 0x01898513.
Lemma F_17f00 : fetch_word Ubsan.M.loaded_segments (0x17f00 : word) = Some W_17f00.
Proof. vm_refl. Qed.
Lemma D_17f00 : decode_any W_17f00 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f04 : bv 32 := 0x00a9b823.
Lemma F_17f04 : fetch_word Ubsan.M.loaded_segments (0x17f04 : word) = Some W_17f04.
Proof. vm_refl. Qed.
Lemma D_17f04 : decode_any W_17f04 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f08 : bv 32 := 0x0089a583.
Lemma F_17f08 : fetch_word Ubsan.M.loaded_segments (0x17f08 : word) = Some W_17f08.
Proof. vm_refl. Qed.
Lemma D_17f08 : decode_any W_17f08 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f0c : bv 32 := 0x02000613.
Lemma F_17f0c : fetch_word Ubsan.M.loaded_segments (0x17f0c : word) = Some W_17f0c.
Proof. vm_refl. Qed.
Lemma D_17f0c : decode_any W_17f0c = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f10 : bv 32 := 0x02c59263.
Lemma F_17f10 : fetch_word Ubsan.M.loaded_segments (0x17f10 : word) = Some W_17f10.
Proof. vm_refl. Qed.
Lemma D_17f10 : decode_any W_17f10 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f14 : bv 32 := 0x20800513.
Lemma F_17f14 : fetch_word Ubsan.M.loaded_segments (0x17f14 : word) = Some W_17f14.
Proof. vm_refl. Qed.
Lemma D_17f14 : decode_any W_17f14 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f18 : bv 32 := 0x00100593.
Lemma F_17f18 : fetch_word Ubsan.M.loaded_segments (0x17f18 : word) = Some W_17f18.
Proof. vm_refl. Qed.
Lemma D_17f18 : decode_any W_17f18 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f1c : bv 32 := 0x3f4000ef.
Lemma F_17f1c : fetch_word Ubsan.M.loaded_segments (0x17f1c : word) = Some W_17f1c.
Proof. vm_refl. Qed.
Lemma D_17f1c : decode_any W_17f1c = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f20 : bv 32 := 0x02050c63.
Lemma F_17f20 : fetch_word Ubsan.M.loaded_segments (0x17f20 : word) = Some W_17f20.
Proof. vm_refl. Qed.
Lemma D_17f20 : decode_any W_17f20 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f24 : bv 32 := 0x00000593.
Lemma F_17f24 : fetch_word Ubsan.M.loaded_segments (0x17f24 : word) = Some W_17f24.
Proof. vm_refl. Qed.
Lemma D_17f24 : decode_any W_17f24 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f28 : bv 32 := 0x0109b603.
Lemma F_17f28 : fetch_word Ubsan.M.loaded_segments (0x17f28 : word) = Some W_17f28.
Proof. vm_refl. Qed.
Lemma D_17f28 : decode_any W_17f28 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f2c : bv 32 := 0x00c53023.
Lemma F_17f2c : fetch_word Ubsan.M.loaded_segments (0x17f2c : word) = Some W_17f2c.
Proof. vm_refl. Qed.
Lemma D_17f2c : decode_any W_17f2c = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f30 : bv 32 := 0x00a9b823.
Lemma F_17f30 : fetch_word Ubsan.M.loaded_segments (0x17f30 : word) = Some W_17f30.
Proof. vm_refl. Qed.
Lemma D_17f30 : decode_any W_17f30 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f34 : bv 32 := 0x00000913.
Lemma F_17f34 : fetch_word Ubsan.M.loaded_segments (0x17f34 : word) = Some W_17f34.
Proof. vm_refl. Qed.
Lemma D_17f34 : decode_any W_17f34 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f38 : bv 32 := 0x00359613.
Lemma F_17f38 : fetch_word Ubsan.M.loaded_segments (0x17f38 : word) = Some W_17f38.
Proof. vm_refl. Qed.
Lemma D_17f38 : decode_any W_17f38 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f3c : bv 32 := 0x00c50533.
Lemma F_17f3c : fetch_word Ubsan.M.loaded_segments (0x17f3c : word) = Some W_17f3c.
Proof. vm_refl. Qed.
Lemma D_17f3c : decode_any W_17f3c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f40 : bv 32 := 0x00000617.
Lemma F_17f40 : fetch_word Ubsan.M.loaded_segments (0x17f40 : word) = Some W_17f40.
Proof. vm_refl. Qed.
Lemma D_17f40 : decode_any W_17f40 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f44 : bv 32 := 0x00158593.
Lemma F_17f44 : fetch_word Ubsan.M.loaded_segments (0x17f44 : word) = Some W_17f44.
Proof. vm_refl. Qed.
Lemma D_17f44 : decode_any W_17f44 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f48 : bv 32 := 0x04060613.
Lemma F_17f48 : fetch_word Ubsan.M.loaded_segments (0x17f48 : word) = Some W_17f48.
Proof. vm_refl. Qed.
Lemma D_17f48 : decode_any W_17f48 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f4c : bv 32 := 0x00c53423.
Lemma F_17f4c : fetch_word Ubsan.M.loaded_segments (0x17f4c : word) = Some W_17f4c.
Proof. vm_refl. Qed.
Lemma D_17f4c : decode_any W_17f4c = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f50 : bv 32 := 0x10953423.
Lemma F_17f50 : fetch_word Ubsan.M.loaded_segments (0x17f50 : word) = Some W_17f50.
Proof. vm_refl. Qed.
Lemma D_17f50 : decode_any W_17f50 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f54 : bv 32 := 0x00b9a423.
Lemma F_17f54 : fetch_word Ubsan.M.loaded_segments (0x17f54 : word) = Some W_17f54.
Proof. vm_refl. Qed.
Lemma D_17f54 : decode_any W_17f54 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f58 : bv 32 := 0x00040513.
Lemma F_17f58 : fetch_word Ubsan.M.loaded_segments (0x17f58 : word) = Some W_17f58.
Proof. vm_refl. Qed.
Lemma D_17f58 : decode_any W_17f58 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f5c : bv 32 := 0x53d070ef.
Lemma F_17f5c : fetch_word Ubsan.M.loaded_segments (0x17f5c : word) = Some W_17f5c.
Proof. vm_refl. Qed.
Lemma D_17f5c : decode_any W_17f5c = Some (Jal 1 32060, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f60 : bv 32 := 0x00090513.
Lemma F_17f60 : fetch_word Ubsan.M.loaded_segments (0x17f60 : word) = Some W_17f60.
Proof. vm_refl. Qed.
Lemma D_17f60 : decode_any W_17f60 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f64 : bv 32 := 0x02813083.
Lemma F_17f64 : fetch_word Ubsan.M.loaded_segments (0x17f64 : word) = Some W_17f64.
Proof. vm_refl. Qed.
Lemma D_17f64 : decode_any W_17f64 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f68 : bv 32 := 0x02013403.
Lemma F_17f68 : fetch_word Ubsan.M.loaded_segments (0x17f68 : word) = Some W_17f68.
Proof. vm_refl. Qed.
Lemma D_17f68 : decode_any W_17f68 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f6c : bv 32 := 0x01813483.
Lemma F_17f6c : fetch_word Ubsan.M.loaded_segments (0x17f6c : word) = Some W_17f6c.
Proof. vm_refl. Qed.
Lemma D_17f6c : decode_any W_17f6c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f70 : bv 32 := 0x01013903.
Lemma F_17f70 : fetch_word Ubsan.M.loaded_segments (0x17f70 : word) = Some W_17f70.
Proof. vm_refl. Qed.
Lemma D_17f70 : decode_any W_17f70 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f74 : bv 32 := 0x00813983.
Lemma F_17f74 : fetch_word Ubsan.M.loaded_segments (0x17f74 : word) = Some W_17f74.
Proof. vm_refl. Qed.
Lemma D_17f74 : decode_any W_17f74 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f78 : bv 32 := 0x03010113.
Lemma F_17f78 : fetch_word Ubsan.M.loaded_segments (0x17f78 : word) = Some W_17f78.
Proof. vm_refl. Qed.
Lemma D_17f78 : decode_any W_17f78 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f7c : bv 32 := 0x00008067.
Lemma F_17f7c : fetch_word Ubsan.M.loaded_segments (0x17f7c : word) = Some W_17f7c.
Proof. vm_refl. Qed.
Lemma D_17f7c : decode_any W_17f7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f80 : bv 32 := 0x00050067.
Lemma F_17f80 : fetch_word Ubsan.M.loaded_segments (0x17f80 : word) = Some W_17f80.
Proof. vm_refl. Qed.
Lemma D_17f80 : decode_any W_17f80 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f84 : bv 32 := 0x00008067.
Lemma F_17f84 : fetch_word Ubsan.M.loaded_segments (0x17f84 : word) = Some W_17f84.
Proof. vm_refl. Qed.
Lemma D_17f84 : decode_any W_17f84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f88 : bv 32 := 0xfe010113.
Lemma F_17f88 : fetch_word Ubsan.M.loaded_segments (0x17f88 : word) = Some W_17f88.
Proof. vm_refl. Qed.
Lemma D_17f88 : decode_any W_17f88 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f8c : bv 32 := 0x00113c23.
Lemma F_17f8c : fetch_word Ubsan.M.loaded_segments (0x17f8c : word) = Some W_17f8c.
Proof. vm_refl. Qed.
Lemma D_17f8c : decode_any W_17f8c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f90 : bv 32 := 0x00813823.
Lemma F_17f90 : fetch_word Ubsan.M.loaded_segments (0x17f90 : word) = Some W_17f90.
Proof. vm_refl. Qed.
Lemma D_17f90 : decode_any W_17f90 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f94 : bv 32 := 0x00913423.
Lemma F_17f94 : fetch_word Ubsan.M.loaded_segments (0x17f94 : word) = Some W_17f94.
Proof. vm_refl. Qed.
Lemma D_17f94 : decode_any W_17f94 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f98 : bv 32 := 0x00009517.
Lemma F_17f98 : fetch_word Ubsan.M.loaded_segments (0x17f98 : word) = Some W_17f98.
Proof. vm_refl. Qed.
Lemma D_17f98 : decode_any W_17f98 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f9c : bv 32 := 0x00009597.
Lemma F_17f9c : fetch_word Ubsan.M.loaded_segments (0x17f9c : word) = Some W_17f9c.
Proof. vm_refl. Qed.
Lemma D_17f9c : decode_any W_17f9c = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fa0 : bv 32 := 0xef853503.
Lemma F_17fa0 : fetch_word Ubsan.M.loaded_segments (0x17fa0 : word) = Some W_17fa0.
Proof. vm_refl. Qed.
Lemma D_17fa0 : decode_any W_17fa0 = Some (Load SZ8 true 10 10 3832, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fa4 : bv 32 := 0xefc5b403.
Lemma F_17fa4 : fetch_word Ubsan.M.loaded_segments (0x17fa4 : word) = Some W_17fa4.
Proof. vm_refl. Qed.
Lemma D_17fa4 : decode_any W_17fa4 = Some (Load SZ8 true 8 11 3836, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fa8 : bv 32 := 0x00a47c63.
Lemma F_17fa8 : fetch_word Ubsan.M.loaded_segments (0x17fa8 : word) = Some W_17fa8.
Proof. vm_refl. Qed.
Lemma D_17fa8 : decode_any W_17fa8 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fac : bv 32 := 0xff853583.
Lemma F_17fac : fetch_word Ubsan.M.loaded_segments (0x17fac : word) = Some W_17fac.
Proof. vm_refl. Qed.
Lemma D_17fac : decode_any W_17fac = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fb0 : bv 32 := 0xff850493.
Lemma F_17fb0 : fetch_word Ubsan.M.loaded_segments (0x17fb0 : word) = Some W_17fb0.
Proof. vm_refl. Qed.
Lemma D_17fb0 : decode_any W_17fb0 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fb4 : bv 32 := 0x000580e7.
Lemma F_17fb4 : fetch_word Ubsan.M.loaded_segments (0x17fb4 : word) = Some W_17fb4.
Proof. vm_refl. Qed.
Lemma D_17fb4 : decode_any W_17fb4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fb8 : bv 32 := 0x00048513.
Lemma F_17fb8 : fetch_word Ubsan.M.loaded_segments (0x17fb8 : word) = Some W_17fb8.
Proof. vm_refl. Qed.
Lemma D_17fb8 : decode_any W_17fb8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fbc : bv 32 := 0xfe9468e3.
Lemma F_17fbc : fetch_word Ubsan.M.loaded_segments (0x17fbc : word) = Some W_17fbc.
Proof. vm_refl. Qed.
Lemma D_17fbc : decode_any W_17fbc = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fc0 : bv 32 := 0x01813083.
Lemma F_17fc0 : fetch_word Ubsan.M.loaded_segments (0x17fc0 : word) = Some W_17fc0.
Proof. vm_refl. Qed.
Lemma D_17fc0 : decode_any W_17fc0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fc4 : bv 32 := 0x01013403.
Lemma F_17fc4 : fetch_word Ubsan.M.loaded_segments (0x17fc4 : word) = Some W_17fc4.
Proof. vm_refl. Qed.
Lemma D_17fc4 : decode_any W_17fc4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fc8 : bv 32 := 0x00813483.
Lemma F_17fc8 : fetch_word Ubsan.M.loaded_segments (0x17fc8 : word) = Some W_17fc8.
Proof. vm_refl. Qed.
Lemma D_17fc8 : decode_any W_17fc8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fcc : bv 32 := 0x02010113.
Lemma F_17fcc : fetch_word Ubsan.M.loaded_segments (0x17fcc : word) = Some W_17fcc.
Proof. vm_refl. Qed.
Lemma D_17fcc : decode_any W_17fcc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fd0 : bv 32 := 0xfb5ff06f.
Lemma F_17fd0 : fetch_word Ubsan.M.loaded_segments (0x17fd0 : word) = Some W_17fd0.
Proof. vm_refl. Qed.
Lemma D_17fd0 : decode_any W_17fd0 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fd4 : bv 32 := 0xff010113.
Lemma F_17fd4 : fetch_word Ubsan.M.loaded_segments (0x17fd4 : word) = Some W_17fd4.
Proof. vm_refl. Qed.
Lemma D_17fd4 : decode_any W_17fd4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fd8 : bv 32 := 0x00113423.
Lemma F_17fd8 : fetch_word Ubsan.M.loaded_segments (0x17fd8 : word) = Some W_17fd8.
Proof. vm_refl. Qed.
Lemma D_17fd8 : decode_any W_17fd8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fdc : bv 32 := 0x00813023.
Lemma F_17fdc : fetch_word Ubsan.M.loaded_segments (0x17fdc : word) = Some W_17fdc.
Proof. vm_refl. Qed.
Lemma D_17fdc : decode_any W_17fdc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fe0 : bv 32 := 0x00000593.
Lemma F_17fe0 : fetch_word Ubsan.M.loaded_segments (0x17fe0 : word) = Some W_17fe0.
Proof. vm_refl. Qed.
Lemma D_17fe0 : decode_any W_17fe0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fe4 : bv 32 := 0x00020613.
Lemma F_17fe4 : fetch_word Ubsan.M.loaded_segments (0x17fe4 : word) = Some W_17fe4.
Proof. vm_refl. Qed.
Lemma D_17fe4 : decode_any W_17fe4 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fe8 : bv 32 := 0xf5862603.
Lemma F_17fe8 : fetch_word Ubsan.M.loaded_segments (0x17fe8 : word) = Some W_17fe8.
Proof. vm_refl. Qed.
Lemma D_17fe8 : decode_any W_17fe8 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_17fec : bv 32 := 0x0003a697.
Lemma F_17fec : fetch_word Ubsan.M.loaded_segments (0x17fec : word) = Some W_17fec.
Proof. vm_refl. Qed.
Lemma D_17fec : decode_any W_17fec = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ff0 : bv 32 := 0x49468693.
Lemma F_17ff0 : fetch_word Ubsan.M.loaded_segments (0x17ff0 : word) = Some W_17ff0.
Proof. vm_refl. Qed.
Lemma D_17ff0 : decode_any W_17ff0 = Some (OpImm ALU_ADD 13 13 1172, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ff4 : bv 32 := 0x1606a72f.
Lemma F_17ff4 : fetch_word Ubsan.M.loaded_segments (0x17ff4 : word) = Some W_17ff4.
Proof. vm_refl. Qed.
Lemma D_17ff4 : decode_any W_17ff4 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ff8 : bv 32 := 0x00b71663.
Lemma F_17ff8 : fetch_word Ubsan.M.loaded_segments (0x17ff8 : word) = Some W_17ff8.
Proof. vm_refl. Qed.
Lemma D_17ff8 : decode_any W_17ff8 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ffc : bv 32 := 0x1ec6a7af.
Lemma F_17ffc : fetch_word Ubsan.M.loaded_segments (0x17ffc : word) = Some W_17ffc.
Proof. vm_refl. Qed.
Lemma D_17ffc : decode_any W_17ffc = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18000 : bv 32 := 0xfe079ae3.
Lemma F_18000 : fetch_word Ubsan.M.loaded_segments (0x18000 : word) = Some W_18000.
Proof. vm_refl. Qed.
Lemma D_18000 : decode_any W_18000 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_18004 : bv 32 := 0x0007059b.
Lemma F_18004 : fetch_word Ubsan.M.loaded_segments (0x18004 : word) = Some W_18004.
Proof. vm_refl. Qed.
Lemma D_18004 : decode_any W_18004 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18008 : bv 32 := 0x02c58263.
Lemma F_18008 : fetch_word Ubsan.M.loaded_segments (0x18008 : word) = Some W_18008.
Proof. vm_refl. Qed.
Lemma D_18008 : decode_any W_18008 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1800c : bv 32 := 0x02058263.
Lemma F_1800c : fetch_word Ubsan.M.loaded_segments (0x1800c : word) = Some W_1800c.
Proof. vm_refl. Qed.
Lemma D_1800c : decode_any W_1800c = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_18010 : bv 32 := 0x04900893.
Lemma F_18010 : fetch_word Ubsan.M.loaded_segments (0x18010 : word) = Some W_18010.
Proof. vm_refl. Qed.
Lemma D_18010 : decode_any W_18010 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_18014 : bv 32 := 0x00000593.
Lemma F_18014 : fetch_word Ubsan.M.loaded_segments (0x18014 : word) = Some W_18014.
Proof. vm_refl. Qed.
Lemma D_18014 : decode_any W_18014 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18018 : bv 32 := 0x00000613.
Lemma F_18018 : fetch_word Ubsan.M.loaded_segments (0x18018 : word) = Some W_18018.
Proof. vm_refl. Qed.
Lemma D_18018 : decode_any W_18018 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1801c : bv 32 := 0x00000693.
Lemma F_1801c : fetch_word Ubsan.M.loaded_segments (0x1801c : word) = Some W_1801c.
Proof. vm_refl. Qed.
Lemma D_1801c : decode_any W_1801c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18020 : bv 32 := 0x00000513.
Lemma F_18020 : fetch_word Ubsan.M.loaded_segments (0x18020 : word) = Some W_18020.
Proof. vm_refl. Qed.
Lemma D_18020 : decode_any W_18020 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18024 : bv 32 := 0x00000073.
Lemma F_18024 : fetch_word Ubsan.M.loaded_segments (0x18024 : word) = Some W_18024.
Proof. vm_refl. Qed.
Lemma E_18024 : is_ecall W_18024 = true.
Proof. vm_refl. Qed.

Definition W_18028 : bv 32 := 0xff9ff06f.
Lemma F_18028 : fetch_word Ubsan.M.loaded_segments (0x18028 : word) = Some W_18028.
Proof. vm_refl. Qed.
Lemma D_18028 : decode_any W_18028 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_1802c : bv 32 := 0x00000023.
Lemma F_1802c : fetch_word Ubsan.M.loaded_segments (0x1802c : word) = Some W_1802c.
Proof. vm_refl. Qed.
Lemma D_1802c : decode_any W_1802c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18030 : bv 32 := 0x00050413.
Lemma F_18030 : fetch_word Ubsan.M.loaded_segments (0x18030 : word) = Some W_18030.
Proof. vm_refl. Qed.
Lemma D_18030 : decode_any W_18030 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18034 : bv 32 := 0xdbdff0ef.
Lemma F_18034 : fetch_word Ubsan.M.loaded_segments (0x18034 : word) = Some W_18034.
Proof. vm_refl. Qed.
Lemma D_18034 : decode_any W_18034 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_18038 : bv 32 := 0xf51ff0ef.
Lemma F_18038 : fetch_word Ubsan.M.loaded_segments (0x18038 : word) = Some W_18038.
Proof. vm_refl. Qed.
Lemma D_18038 : decode_any W_18038 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_1803c : bv 32 := 0x160020ef.
Lemma F_1803c : fetch_word Ubsan.M.loaded_segments (0x1803c : word) = Some W_1803c.
Proof. vm_refl. Qed.
Lemma D_1803c : decode_any W_1803c = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

Definition W_18040 : bv 32 := 0x00040513.
Lemma F_18040 : fetch_word Ubsan.M.loaded_segments (0x18040 : word) = Some W_18040.
Proof. vm_refl. Qed.
Lemma D_18040 : decode_any W_18040 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18044 : bv 32 := 0xd91ff0ef.
Lemma F_18044 : fetch_word Ubsan.M.loaded_segments (0x18044 : word) = Some W_18044.
Proof. vm_refl. Qed.
Lemma D_18044 : decode_any W_18044 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_1fa10 : bv 32 := 0x00033597.
Lemma F_1fa10 : fetch_word Ubsan.M.loaded_segments (0x1fa10 : word) = Some W_1fa10.
Proof. vm_refl. Qed.
Lemma D_1fa10 : decode_any W_1fa10 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_1fa14 : bv 32 := 0xa9b58683.
Lemma F_1fa14 : fetch_word Ubsan.M.loaded_segments (0x1fa14 : word) = Some W_1fa14.
Proof. vm_refl. Qed.
Lemma D_1fa14 : decode_any W_1fa14 = Some (Load SZ1 true 13 11 2715, 4%Z).
Proof. vm_refl. Qed.

Definition W_1fa18 : bv 32 := 0x1e068863.
Lemma F_1fa18 : fetch_word Ubsan.M.loaded_segments (0x1fa18 : word) = Some W_1fa18.
Proof. vm_refl. Qed.
Lemma D_1fa18 : decode_any W_1fa18 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_1fc08 : bv 32 := 0x00008067.
Lemma F_1fc08 : fetch_word Ubsan.M.loaded_segments (0x1fc08 : word) = Some W_1fc08.
Proof. vm_refl. Qed.
Lemma D_1fc08 : decode_any W_1fc08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1fc98 : bv 32 := 0x00052583.
Lemma F_1fc98 : fetch_word Ubsan.M.loaded_segments (0x1fc98 : word) = Some W_1fc98.
Proof. vm_refl. Qed.
Lemma D_1fc98 : decode_any W_1fc98 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1fc9c : bv 32 := 0x0005c463.
Lemma F_1fc9c : fetch_word Ubsan.M.loaded_segments (0x1fc9c : word) = Some W_1fc9c.
Proof. vm_refl. Qed.
Lemma D_1fc9c : decode_any W_1fc9c = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1fca0 : bv 32 := 0x00008067.
Lemma F_1fca0 : fetch_word Ubsan.M.loaded_segments (0x1fca0 : word) = Some W_1fca0.
Proof. vm_refl. Qed.
Lemma D_1fca0 : decode_any W_1fca0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
