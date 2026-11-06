(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.H Require GcFlushS8.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1377c : bv 32 := 0xffffe517.
Lemma F_1377c : fetch_word Plain.M.loaded_segments (0x1377c : word) = Some W_1377c.
Proof. vm_refl. Qed.
Lemma D_1377c : decode_any W_1377c = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_13780 : bv 32 := 0x54c50513.
Lemma F_13780 : fetch_word Plain.M.loaded_segments (0x13780 : word) = Some W_13780.
Proof. vm_refl. Qed.
Lemma D_13780 : decode_any W_13780 = Some (OpImm ALU_ADD 10 10 1356, 4%Z).
Proof. vm_refl. Qed.

Definition W_13784 : bv 32 := 0x0000e597.
Lemma F_13784 : fetch_word Plain.M.loaded_segments (0x13784 : word) = Some W_13784.
Proof. vm_refl. Qed.
Lemma D_13784 : decode_any W_13784 = Some (Auipc 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_13788 : bv 32 := 0xaa458593.
Lemma F_13788 : fetch_word Plain.M.loaded_segments (0x13788 : word) = Some W_13788.
Proof. vm_refl. Qed.
Lemma D_13788 : decode_any W_13788 = Some (OpImm ALU_ADD 11 11 2724, 4%Z).
Proof. vm_refl. Qed.

Definition W_1378c : bv 32 := 0x000000ef.
Lemma F_1378c : fetch_word Plain.M.loaded_segments (0x1378c : word) = Some W_1378c.
Proof. vm_refl. Qed.
Lemma D_1378c : decode_any W_1378c = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13790 : bv 32 := 0x0040006f.
Lemma F_13790 : fetch_word Plain.M.loaded_segments (0x13790 : word) = Some W_13790.
Proof. vm_refl. Qed.
Lemma D_13790 : decode_any W_13790 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13794 : bv 32 := 0x00813083.
Lemma F_13794 : fetch_word Plain.M.loaded_segments (0x13794 : word) = Some W_13794.
Proof. vm_refl. Qed.
Lemma D_13794 : decode_any W_13794 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13798 : bv 32 := 0x00013403.
Lemma F_13798 : fetch_word Plain.M.loaded_segments (0x13798 : word) = Some W_13798.
Proof. vm_refl. Qed.
Lemma D_13798 : decode_any W_13798 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1379c : bv 32 := 0x01010113.
Lemma F_1379c : fetch_word Plain.M.loaded_segments (0x1379c : word) = Some W_1379c.
Proof. vm_refl. Qed.
Lemma D_1379c : decode_any W_1379c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_137a0 : bv 32 := 0x00008067.
Lemma F_137a0 : fetch_word Plain.M.loaded_segments (0x137a0 : word) = Some W_137a0.
Proof. vm_refl. Qed.
Lemma D_137a0 : decode_any W_137a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_137a4 : bv 32 := 0xff010113.
Lemma F_137a4 : fetch_word Plain.M.loaded_segments (0x137a4 : word) = Some W_137a4.
Proof. vm_refl. Qed.
Lemma D_137a4 : decode_any W_137a4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_137a8 : bv 32 := 0x00113423.
Lemma F_137a8 : fetch_word Plain.M.loaded_segments (0x137a8 : word) = Some W_137a8.
Proof. vm_refl. Qed.
Lemma D_137a8 : decode_any W_137a8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_137ac : bv 32 := 0x00813023.
Lemma F_137ac : fetch_word Plain.M.loaded_segments (0x137ac : word) = Some W_137ac.
Proof. vm_refl. Qed.
Lemma D_137ac : decode_any W_137ac = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_137b0 : bv 32 := 0x01010413.
Lemma F_137b0 : fetch_word Plain.M.loaded_segments (0x137b0 : word) = Some W_137b0.
Proof. vm_refl. Qed.
Lemma D_137b0 : decode_any W_137b0 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_137b4 : bv 32 := 0x0000e517.
Lemma F_137b4 : fetch_word Plain.M.loaded_segments (0x137b4 : word) = Some W_137b4.
Proof. vm_refl. Qed.
Lemma D_137b4 : decode_any W_137b4 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_137b8 : bv 32 := 0xab450513.
Lemma F_137b8 : fetch_word Plain.M.loaded_segments (0x137b8 : word) = Some W_137b8.
Proof. vm_refl. Qed.
Lemma D_137b8 : decode_any W_137b8 = Some (OpImm ALU_ADD 10 10 2740, 4%Z).
Proof. vm_refl. Qed.

Definition W_137bc : bv 32 := 0x00054503.
Lemma F_137bc : fetch_word Plain.M.loaded_segments (0x137bc : word) = Some W_137bc.
Proof. vm_refl. Qed.
Lemma D_137bc : decode_any W_137bc = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_137c0 : bv 32 := 0x00157513.
Lemma F_137c0 : fetch_word Plain.M.loaded_segments (0x137c0 : word) = Some W_137c0.
Proof. vm_refl. Qed.
Lemma D_137c0 : decode_any W_137c0 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_137c4 : bv 32 := 0x00050663.
Lemma F_137c4 : fetch_word Plain.M.loaded_segments (0x137c4 : word) = Some W_137c4.
Proof. vm_refl. Qed.
Lemma D_137c4 : decode_any W_137c4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_137c8 : bv 32 := 0x0040006f.
Lemma F_137c8 : fetch_word Plain.M.loaded_segments (0x137c8 : word) = Some W_137c8.
Proof. vm_refl. Qed.
Lemma D_137c8 : decode_any W_137c8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_137cc : bv 32 := 0x0580006f.
Lemma F_137cc : fetch_word Plain.M.loaded_segments (0x137cc : word) = Some W_137cc.
Proof. vm_refl. Qed.
Lemma D_137cc : decode_any W_137cc = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_137d0 : bv 32 := 0x0000e517.
Lemma F_137d0 : fetch_word Plain.M.loaded_segments (0x137d0 : word) = Some W_137d0.
Proof. vm_refl. Qed.
Lemma D_137d0 : decode_any W_137d0 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_137d4 : bv 32 := 0xa9850593.
Lemma F_137d4 : fetch_word Plain.M.loaded_segments (0x137d4 : word) = Some W_137d4.
Proof. vm_refl. Qed.
Lemma D_137d4 : decode_any W_137d4 = Some (OpImm ALU_ADD 11 10 2712, 4%Z).
Proof. vm_refl. Qed.

Definition W_137d8 : bv 32 := 0x00100513.
Lemma F_137d8 : fetch_word Plain.M.loaded_segments (0x137d8 : word) = Some W_137d8.
Proof. vm_refl. Qed.
Lemma D_137d8 : decode_any W_137d8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_137dc : bv 32 := 0x00a58023.
Lemma F_137dc : fetch_word Plain.M.loaded_segments (0x137dc : word) = Some W_137dc.
Proof. vm_refl. Qed.
Lemma D_137dc : decode_any W_137dc = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_137e0 : bv 32 := 0x0000c517.
Lemma F_137e0 : fetch_word Plain.M.loaded_segments (0x137e0 : word) = Some W_137e0.
Proof. vm_refl. Qed.
Lemma D_137e0 : decode_any W_137e0 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_137e4 : bv 32 := 0x79853503.
Lemma F_137e4 : fetch_word Plain.M.loaded_segments (0x137e4 : word) = Some W_137e4.
Proof. vm_refl. Qed.
Lemma D_137e4 : decode_any W_137e4 = Some (Load SZ8 true 10 10 1944, 4%Z).
Proof. vm_refl. Qed.

Definition W_137e8 : bv 32 := 0x00050e63.
Lemma F_137e8 : fetch_word Plain.M.loaded_segments (0x137e8 : word) = Some W_137e8.
Proof. vm_refl. Qed.
Lemma D_137e8 : decode_any W_137e8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_137ec : bv 32 := 0x0040006f.
Lemma F_137ec : fetch_word Plain.M.loaded_segments (0x137ec : word) = Some W_137ec.
Proof. vm_refl. Qed.
Lemma D_137ec : decode_any W_137ec = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_137f0 : bv 32 := 0x0000d517.
Lemma F_137f0 : fetch_word Plain.M.loaded_segments (0x137f0 : word) = Some W_137f0.
Proof. vm_refl. Qed.
Lemma D_137f0 : decode_any W_137f0 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_137f4 : bv 32 := 0x7f850513.
Lemma F_137f4 : fetch_word Plain.M.loaded_segments (0x137f4 : word) = Some W_137f4.
Proof. vm_refl. Qed.
Lemma D_137f4 : decode_any W_137f4 = Some (OpImm ALU_ADD 10 10 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_137f8 : bv 32 := 0x00053503.
Lemma F_137f8 : fetch_word Plain.M.loaded_segments (0x137f8 : word) = Some W_137f8.
Proof. vm_refl. Qed.
Lemma D_137f8 : decode_any W_137f8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_137fc : bv 32 := 0x005030ef.
Lemma F_137fc : fetch_word Plain.M.loaded_segments (0x137fc : word) = Some W_137fc.
Proof. vm_refl. Qed.
Lemma D_137fc : decode_any W_137fc = Some (Jal 1 14340, 4%Z).
Proof. vm_refl. Qed.

Definition W_13800 : bv 32 := 0x0040006f.
Lemma F_13800 : fetch_word Plain.M.loaded_segments (0x13800 : word) = Some W_13800.
Proof. vm_refl. Qed.
Lemma D_13800 : decode_any W_13800 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13804 : bv 32 := 0x0000c517.
Lemma F_13804 : fetch_word Plain.M.loaded_segments (0x13804 : word) = Some W_13804.
Proof. vm_refl. Qed.
Lemma D_13804 : decode_any W_13804 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13808 : bv 32 := 0x77c53503.
Lemma F_13808 : fetch_word Plain.M.loaded_segments (0x13808 : word) = Some W_13808.
Proof. vm_refl. Qed.
Lemma D_13808 : decode_any W_13808 = Some (Load SZ8 true 10 10 1916, 4%Z).
Proof. vm_refl. Qed.

Definition W_1380c : bv 32 := 0x00050c63.
Lemma F_1380c : fetch_word Plain.M.loaded_segments (0x1380c : word) = Some W_1380c.
Proof. vm_refl. Qed.
Lemma D_1380c : decode_any W_1380c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13810 : bv 32 := 0x0040006f.
Lemma F_13810 : fetch_word Plain.M.loaded_segments (0x13810 : word) = Some W_13810.
Proof. vm_refl. Qed.
Lemma D_13810 : decode_any W_13810 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13814 : bv 32 := 0xffffe517.
Lemma F_13814 : fetch_word Plain.M.loaded_segments (0x13814 : word) = Some W_13814.
Proof. vm_refl. Qed.
Lemma D_13814 : decode_any W_13814 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_13818 : bv 32 := 0x4b450513.
Lemma F_13818 : fetch_word Plain.M.loaded_segments (0x13818 : word) = Some W_13818.
Proof. vm_refl. Qed.
Lemma D_13818 : decode_any W_13818 = Some (OpImm ALU_ADD 10 10 1204, 4%Z).
Proof. vm_refl. Qed.

Definition W_1381c : bv 32 := 0x000000ef.
Lemma F_1381c : fetch_word Plain.M.loaded_segments (0x1381c : word) = Some W_1381c.
Proof. vm_refl. Qed.
Lemma D_1381c : decode_any W_1381c = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13820 : bv 32 := 0x0040006f.
Lemma F_13820 : fetch_word Plain.M.loaded_segments (0x13820 : word) = Some W_13820.
Proof. vm_refl. Qed.
Lemma D_13820 : decode_any W_13820 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13824 : bv 32 := 0x00813083.
Lemma F_13824 : fetch_word Plain.M.loaded_segments (0x13824 : word) = Some W_13824.
Proof. vm_refl. Qed.
Lemma D_13824 : decode_any W_13824 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13828 : bv 32 := 0x00013403.
Lemma F_13828 : fetch_word Plain.M.loaded_segments (0x13828 : word) = Some W_13828.
Proof. vm_refl. Qed.
Lemma D_13828 : decode_any W_13828 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1382c : bv 32 := 0x01010113.
Lemma F_1382c : fetch_word Plain.M.loaded_segments (0x1382c : word) = Some W_1382c.
Proof. vm_refl. Qed.
Lemma D_1382c : decode_any W_1382c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13830 : bv 32 := 0x00008067.
Lemma F_13830 : fetch_word Plain.M.loaded_segments (0x13830 : word) = Some W_13830.
Proof. vm_refl. Qed.
Lemma D_13830 : decode_any W_13830 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c5c : bv 32 := 0x0001d517.
Lemma F_13c5c : fetch_word Plain.M.loaded_segments (0x13c5c : word) = Some W_13c5c.
Proof. vm_refl. Qed.
Lemma D_13c5c : decode_any W_13c5c = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c60 : bv 32 := 0x61854503.
Lemma F_13c60 : fetch_word Plain.M.loaded_segments (0x13c60 : word) = Some W_13c60.
Proof. vm_refl. Qed.
Lemma D_13c60 : decode_any W_13c60 = Some (Load SZ1 false 10 10 1560, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c64 : bv 32 := 0x00051463.
Lemma F_13c64 : fetch_word Plain.M.loaded_segments (0x13c64 : word) = Some W_13c64.
Proof. vm_refl. Qed.
Lemma D_13c64 : decode_any W_13c64 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c68 : bv 32 := 0x00008067.
Lemma F_13c68 : fetch_word Plain.M.loaded_segments (0x13c68 : word) = Some W_13c68.
Proof. vm_refl. Qed.
Lemma D_13c68 : decode_any W_13c68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c6c : bv 32 := 0xff010113.
Lemma F_13c6c : fetch_word Plain.M.loaded_segments (0x13c6c : word) = Some W_13c6c.
Proof. vm_refl. Qed.
Lemma D_13c6c : decode_any W_13c6c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c70 : bv 32 := 0x00113423.
Lemma F_13c70 : fetch_word Plain.M.loaded_segments (0x13c70 : word) = Some W_13c70.
Proof. vm_refl. Qed.
Lemma D_13c70 : decode_any W_13c70 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c74 : bv 32 := 0x0000c517.
Lemma F_13c74 : fetch_word Plain.M.loaded_segments (0x13c74 : word) = Some W_13c74.
Proof. vm_refl. Qed.
Lemma D_13c74 : decode_any W_13c74 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c78 : bv 32 := 0x32453503.
Lemma F_13c78 : fetch_word Plain.M.loaded_segments (0x13c78 : word) = Some W_13c78.
Proof. vm_refl. Qed.
Lemma D_13c78 : decode_any W_13c78 = Some (Load SZ8 true 10 10 804, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c7c : bv 32 := 0x00053503.
Lemma F_13c7c : fetch_word Plain.M.loaded_segments (0x13c7c : word) = Some W_13c7c.
Proof. vm_refl. Qed.
Lemma D_13c7c : decode_any W_13c7c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c80 : bv 32 := 0x4f4050ef.
Lemma F_13c80 : fetch_word Plain.M.loaded_segments (0x13c80 : word) = Some W_13c80.
Proof. vm_refl. Qed.
Lemma D_13c80 : decode_any W_13c80 = Some (Jal 1 21748, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c84 : bv 32 := 0x04d00513.
Lemma F_13c84 : fetch_word Plain.M.loaded_segments (0x13c84 : word) = Some W_13c84.
Proof. vm_refl. Qed.
Lemma D_13c84 : decode_any W_13c84 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c88 : bv 32 := 0x2000b0ef.
Lemma F_13c88 : fetch_word Plain.M.loaded_segments (0x13c88 : word) = Some W_13c88.
Proof. vm_refl. Qed.
Lemma D_13c88 : decode_any W_13c88 = Some (Jal 1 45568, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f38 : bv 32 := 0xfd010113.
Lemma F_16f38 : fetch_word Plain.M.loaded_segments (0x16f38 : word) = Some W_16f38.
Proof. vm_refl. Qed.
Lemma D_16f38 : decode_any W_16f38 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f3c : bv 32 := 0x02113423.
Lemma F_16f3c : fetch_word Plain.M.loaded_segments (0x16f3c : word) = Some W_16f3c.
Proof. vm_refl. Qed.
Lemma D_16f3c : decode_any W_16f3c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f40 : bv 32 := 0x02813023.
Lemma F_16f40 : fetch_word Plain.M.loaded_segments (0x16f40 : word) = Some W_16f40.
Proof. vm_refl. Qed.
Lemma D_16f40 : decode_any W_16f40 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f44 : bv 32 := 0x00913c23.
Lemma F_16f44 : fetch_word Plain.M.loaded_segments (0x16f44 : word) = Some W_16f44.
Proof. vm_refl. Qed.
Lemma D_16f44 : decode_any W_16f44 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f48 : bv 32 := 0x01213823.
Lemma F_16f48 : fetch_word Plain.M.loaded_segments (0x16f48 : word) = Some W_16f48.
Proof. vm_refl. Qed.
Lemma D_16f48 : decode_any W_16f48 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f4c : bv 32 := 0x01313423.
Lemma F_16f4c : fetch_word Plain.M.loaded_segments (0x16f4c : word) = Some W_16f4c.
Proof. vm_refl. Qed.
Lemma D_16f4c : decode_any W_16f4c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f50 : bv 32 := 0x0003a517.
Lemma F_16f50 : fetch_word Plain.M.loaded_segments (0x16f50 : word) = Some W_16f50.
Proof. vm_refl. Qed.
Lemma D_16f50 : decode_any W_16f50 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f54 : bv 32 := 0x46050913.
Lemma F_16f54 : fetch_word Plain.M.loaded_segments (0x16f54 : word) = Some W_16f54.
Proof. vm_refl. Qed.
Lemma D_16f54 : decode_any W_16f54 = Some (OpImm ALU_ADD 18 10 1120, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f58 : bv 32 := 0x00490413.
Lemma F_16f58 : fetch_word Plain.M.loaded_segments (0x16f58 : word) = Some W_16f58.
Proof. vm_refl. Qed.
Lemma D_16f58 : decode_any W_16f58 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f5c : bv 32 := 0x00040513.
Lemma F_16f5c : fetch_word Plain.M.loaded_segments (0x16f5c : word) = Some W_16f5c.
Proof. vm_refl. Qed.
Lemma D_16f5c : decode_any W_16f5c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f60 : bv 32 := 0x3f9070ef.
Lemma F_16f60 : fetch_word Plain.M.loaded_segments (0x16f60 : word) = Some W_16f60.
Proof. vm_refl. Qed.
Lemma D_16f60 : decode_any W_16f60 = Some (Jal 1 31736, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f64 : bv 32 := 0x01093503.
Lemma F_16f64 : fetch_word Plain.M.loaded_segments (0x16f64 : word) = Some W_16f64.
Proof. vm_refl. Qed.
Lemma D_16f64 : decode_any W_16f64 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f68 : bv 32 := 0x06050863.
Lemma F_16f68 : fetch_word Plain.M.loaded_segments (0x16f68 : word) = Some W_16f68.
Proof. vm_refl. Qed.
Lemma D_16f68 : decode_any W_16f68 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f6c : bv 32 := 0x00892583.
Lemma F_16f6c : fetch_word Plain.M.loaded_segments (0x16f6c : word) = Some W_16f6c.
Proof. vm_refl. Qed.
Lemma D_16f6c : decode_any W_16f6c = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f70 : bv 32 := 0x0180006f.
Lemma F_16f70 : fetch_word Plain.M.loaded_segments (0x16f70 : word) = Some W_16f70.
Proof. vm_refl. Qed.
Lemma D_16f70 : decode_any W_16f70 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f74 : bv 32 := 0x00053503.
Lemma F_16f74 : fetch_word Plain.M.loaded_segments (0x16f74 : word) = Some W_16f74.
Proof. vm_refl. Qed.
Lemma D_16f74 : decode_any W_16f74 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f78 : bv 32 := 0x02000593.
Lemma F_16f78 : fetch_word Plain.M.loaded_segments (0x16f78 : word) = Some W_16f78.
Proof. vm_refl. Qed.
Lemma D_16f78 : decode_any W_16f78 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f7c : bv 32 := 0x00b92423.
Lemma F_16f7c : fetch_word Plain.M.loaded_segments (0x16f7c : word) = Some W_16f7c.
Proof. vm_refl. Qed.
Lemma D_16f7c : decode_any W_16f7c = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f80 : bv 32 := 0x00a93823.
Lemma F_16f80 : fetch_word Plain.M.loaded_segments (0x16f80 : word) = Some W_16f80.
Proof. vm_refl. Qed.
Lemma D_16f80 : decode_any W_16f80 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f84 : bv 32 := 0x04050a63.
Lemma F_16f84 : fetch_word Plain.M.loaded_segments (0x16f84 : word) = Some W_16f84.
Proof. vm_refl. Qed.
Lemma D_16f84 : decode_any W_16f84 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f88 : bv 32 := 0xfff5861b.
Lemma F_16f88 : fetch_word Plain.M.loaded_segments (0x16f88 : word) = Some W_16f88.
Proof. vm_refl. Qed.
Lemma D_16f88 : decode_any W_16f88 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f8c : bv 32 := 0x00c92423.
Lemma F_16f8c : fetch_word Plain.M.loaded_segments (0x16f8c : word) = Some W_16f8c.
Proof. vm_refl. Qed.
Lemma D_16f8c : decode_any W_16f8c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f90 : bv 32 := 0xfeb052e3.
Lemma F_16f90 : fetch_word Plain.M.loaded_segments (0x16f90 : word) = Some W_16f90.
Proof. vm_refl. Qed.
Lemma D_16f90 : decode_any W_16f90 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f94 : bv 32 := 0x01093503.
Lemma F_16f94 : fetch_word Plain.M.loaded_segments (0x16f94 : word) = Some W_16f94.
Proof. vm_refl. Qed.
Lemma D_16f94 : decode_any W_16f94 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f98 : bv 32 := 0x00361613.
Lemma F_16f98 : fetch_word Plain.M.loaded_segments (0x16f98 : word) = Some W_16f98.
Proof. vm_refl. Qed.
Lemma D_16f98 : decode_any W_16f98 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_16f9c : bv 32 := 0x00c50533.
Lemma F_16f9c : fetch_word Plain.M.loaded_segments (0x16f9c : word) = Some W_16f9c.
Proof. vm_refl. Qed.
Lemma D_16f9c : decode_any W_16f9c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fa0 : bv 32 := 0x00853983.
Lemma F_16fa0 : fetch_word Plain.M.loaded_segments (0x16fa0 : word) = Some W_16fa0.
Proof. vm_refl. Qed.
Lemma D_16fa0 : decode_any W_16fa0 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fa4 : bv 32 := 0x10853483.
Lemma F_16fa4 : fetch_word Plain.M.loaded_segments (0x16fa4 : word) = Some W_16fa4.
Proof. vm_refl. Qed.
Lemma D_16fa4 : decode_any W_16fa4 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fa8 : bv 32 := 0x00040513.
Lemma F_16fa8 : fetch_word Plain.M.loaded_segments (0x16fa8 : word) = Some W_16fa8.
Proof. vm_refl. Qed.
Lemma D_16fa8 : decode_any W_16fa8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fac : bv 32 := 0x635070ef.
Lemma F_16fac : fetch_word Plain.M.loaded_segments (0x16fac : word) = Some W_16fac.
Proof. vm_refl. Qed.
Lemma D_16fac : decode_any W_16fac = Some (Jal 1 32308, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fb0 : bv 32 := 0x00048513.
Lemma F_16fb0 : fetch_word Plain.M.loaded_segments (0x16fb0 : word) = Some W_16fb0.
Proof. vm_refl. Qed.
Lemma D_16fb0 : decode_any W_16fb0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fb4 : bv 32 := 0x000980e7.
Lemma F_16fb4 : fetch_word Plain.M.loaded_segments (0x16fb4 : word) = Some W_16fb4.
Proof. vm_refl. Qed.
Lemma D_16fb4 : decode_any W_16fb4 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fb8 : bv 32 := 0x00040513.
Lemma F_16fb8 : fetch_word Plain.M.loaded_segments (0x16fb8 : word) = Some W_16fb8.
Proof. vm_refl. Qed.
Lemma D_16fb8 : decode_any W_16fb8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fbc : bv 32 := 0x39d070ef.
Lemma F_16fbc : fetch_word Plain.M.loaded_segments (0x16fbc : word) = Some W_16fbc.
Proof. vm_refl. Qed.
Lemma D_16fbc : decode_any W_16fbc = Some (Jal 1 31644, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fc0 : bv 32 := 0x00892503.
Lemma F_16fc0 : fetch_word Plain.M.loaded_segments (0x16fc0 : word) = Some W_16fc0.
Proof. vm_refl. Qed.
Lemma D_16fc0 : decode_any W_16fc0 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fc4 : bv 32 := 0xfff5061b.
Lemma F_16fc4 : fetch_word Plain.M.loaded_segments (0x16fc4 : word) = Some W_16fc4.
Proof. vm_refl. Qed.
Lemma D_16fc4 : decode_any W_16fc4 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fc8 : bv 32 := 0x00c92423.
Lemma F_16fc8 : fetch_word Plain.M.loaded_segments (0x16fc8 : word) = Some W_16fc8.
Proof. vm_refl. Qed.
Lemma D_16fc8 : decode_any W_16fc8 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fcc : bv 32 := 0xfca044e3.
Lemma F_16fcc : fetch_word Plain.M.loaded_segments (0x16fcc : word) = Some W_16fcc.
Proof. vm_refl. Qed.
Lemma D_16fcc : decode_any W_16fcc = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fd0 : bv 32 := 0x01093503.
Lemma F_16fd0 : fetch_word Plain.M.loaded_segments (0x16fd0 : word) = Some W_16fd0.
Proof. vm_refl. Qed.
Lemma D_16fd0 : decode_any W_16fd0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fd4 : bv 32 := 0xfa1ff06f.
Lemma F_16fd4 : fetch_word Plain.M.loaded_segments (0x16fd4 : word) = Some W_16fd4.
Proof. vm_refl. Qed.
Lemma D_16fd4 : decode_any W_16fd4 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fd8 : bv 32 := 0x00100513.
Lemma F_16fd8 : fetch_word Plain.M.loaded_segments (0x16fd8 : word) = Some W_16fd8.
Proof. vm_refl. Qed.
Lemma D_16fd8 : decode_any W_16fd8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fdc : bv 32 := 0x00a90023.
Lemma F_16fdc : fetch_word Plain.M.loaded_segments (0x16fdc : word) = Some W_16fdc.
Proof. vm_refl. Qed.
Lemma D_16fdc : decode_any W_16fdc = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fe0 : bv 32 := 0x00040513.
Lemma F_16fe0 : fetch_word Plain.M.loaded_segments (0x16fe0 : word) = Some W_16fe0.
Proof. vm_refl. Qed.
Lemma D_16fe0 : decode_any W_16fe0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fe4 : bv 32 := 0x02813083.
Lemma F_16fe4 : fetch_word Plain.M.loaded_segments (0x16fe4 : word) = Some W_16fe4.
Proof. vm_refl. Qed.
Lemma D_16fe4 : decode_any W_16fe4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fe8 : bv 32 := 0x02013403.
Lemma F_16fe8 : fetch_word Plain.M.loaded_segments (0x16fe8 : word) = Some W_16fe8.
Proof. vm_refl. Qed.
Lemma D_16fe8 : decode_any W_16fe8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16fec : bv 32 := 0x01813483.
Lemma F_16fec : fetch_word Plain.M.loaded_segments (0x16fec : word) = Some W_16fec.
Proof. vm_refl. Qed.
Lemma D_16fec : decode_any W_16fec = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ff0 : bv 32 := 0x01013903.
Lemma F_16ff0 : fetch_word Plain.M.loaded_segments (0x16ff0 : word) = Some W_16ff0.
Proof. vm_refl. Qed.
Lemma D_16ff0 : decode_any W_16ff0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ff4 : bv 32 := 0x00813983.
Lemma F_16ff4 : fetch_word Plain.M.loaded_segments (0x16ff4 : word) = Some W_16ff4.
Proof. vm_refl. Qed.
Lemma D_16ff4 : decode_any W_16ff4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ff8 : bv 32 := 0x03010113.
Lemma F_16ff8 : fetch_word Plain.M.loaded_segments (0x16ff8 : word) = Some W_16ff8.
Proof. vm_refl. Qed.
Lemma D_16ff8 : decode_any W_16ff8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_16ffc : bv 32 := 0x5e50706f.
Lemma F_16ffc : fetch_word Plain.M.loaded_segments (0x16ffc : word) = Some W_16ffc.
Proof. vm_refl. Qed.
Lemma D_16ffc : decode_any W_16ffc = Some (Jal 0 32228, 4%Z).
Proof. vm_refl. Qed.

Definition W_17000 : bv 32 := 0x00008067.
Lemma F_17000 : fetch_word Plain.M.loaded_segments (0x17000 : word) = Some W_17000.
Proof. vm_refl. Qed.
Lemma D_17000 : decode_any W_17000 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17004 : bv 32 := 0xfd010113.
Lemma F_17004 : fetch_word Plain.M.loaded_segments (0x17004 : word) = Some W_17004.
Proof. vm_refl. Qed.
Lemma D_17004 : decode_any W_17004 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_17008 : bv 32 := 0x02113423.
Lemma F_17008 : fetch_word Plain.M.loaded_segments (0x17008 : word) = Some W_17008.
Proof. vm_refl. Qed.
Lemma D_17008 : decode_any W_17008 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1700c : bv 32 := 0x02813023.
Lemma F_1700c : fetch_word Plain.M.loaded_segments (0x1700c : word) = Some W_1700c.
Proof. vm_refl. Qed.
Lemma D_1700c : decode_any W_1700c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17010 : bv 32 := 0x00913c23.
Lemma F_17010 : fetch_word Plain.M.loaded_segments (0x17010 : word) = Some W_17010.
Proof. vm_refl. Qed.
Lemma D_17010 : decode_any W_17010 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17014 : bv 32 := 0x01213823.
Lemma F_17014 : fetch_word Plain.M.loaded_segments (0x17014 : word) = Some W_17014.
Proof. vm_refl. Qed.
Lemma D_17014 : decode_any W_17014 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17018 : bv 32 := 0x01313423.
Lemma F_17018 : fetch_word Plain.M.loaded_segments (0x17018 : word) = Some W_17018.
Proof. vm_refl. Qed.
Lemma D_17018 : decode_any W_17018 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1701c : bv 32 := 0x00050493.
Lemma F_1701c : fetch_word Plain.M.loaded_segments (0x1701c : word) = Some W_1701c.
Proof. vm_refl. Qed.
Lemma D_1701c : decode_any W_1701c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17020 : bv 32 := 0x0003a517.
Lemma F_17020 : fetch_word Plain.M.loaded_segments (0x17020 : word) = Some W_17020.
Proof. vm_refl. Qed.
Lemma D_17020 : decode_any W_17020 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17024 : bv 32 := 0x39050993.
Lemma F_17024 : fetch_word Plain.M.loaded_segments (0x17024 : word) = Some W_17024.
Proof. vm_refl. Qed.
Lemma D_17024 : decode_any W_17024 = Some (OpImm ALU_ADD 19 10 912, 4%Z).
Proof. vm_refl. Qed.

Definition W_17028 : bv 32 := 0x00498413.
Lemma F_17028 : fetch_word Plain.M.loaded_segments (0x17028 : word) = Some W_17028.
Proof. vm_refl. Qed.
Lemma D_17028 : decode_any W_17028 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1702c : bv 32 := 0x00040513.
Lemma F_1702c : fetch_word Plain.M.loaded_segments (0x1702c : word) = Some W_1702c.
Proof. vm_refl. Qed.
Lemma D_1702c : decode_any W_1702c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17030 : bv 32 := 0x329070ef.
Lemma F_17030 : fetch_word Plain.M.loaded_segments (0x17030 : word) = Some W_17030.
Proof. vm_refl. Qed.
Lemma D_17030 : decode_any W_17030 = Some (Jal 1 31528, 4%Z).
Proof. vm_refl. Qed.

Definition W_17034 : bv 32 := 0x0009c503.
Lemma F_17034 : fetch_word Plain.M.loaded_segments (0x17034 : word) = Some W_17034.
Proof. vm_refl. Qed.
Lemma D_17034 : decode_any W_17034 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17038 : bv 32 := 0xfff00913.
Lemma F_17038 : fetch_word Plain.M.loaded_segments (0x17038 : word) = Some W_17038.
Proof. vm_refl. Qed.
Lemma D_17038 : decode_any W_17038 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_1703c : bv 32 := 0x06051263.
Lemma F_1703c : fetch_word Plain.M.loaded_segments (0x1703c : word) = Some W_1703c.
Proof. vm_refl. Qed.
Lemma D_1703c : decode_any W_1703c = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_17040 : bv 32 := 0x0109b503.
Lemma F_17040 : fetch_word Plain.M.loaded_segments (0x17040 : word) = Some W_17040.
Proof. vm_refl. Qed.
Lemma D_17040 : decode_any W_17040 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17044 : bv 32 := 0x00051663.
Lemma F_17044 : fetch_word Plain.M.loaded_segments (0x17044 : word) = Some W_17044.
Proof. vm_refl. Qed.
Lemma D_17044 : decode_any W_17044 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17048 : bv 32 := 0x01898513.
Lemma F_17048 : fetch_word Plain.M.loaded_segments (0x17048 : word) = Some W_17048.
Proof. vm_refl. Qed.
Lemma D_17048 : decode_any W_17048 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1704c : bv 32 := 0x00a9b823.
Lemma F_1704c : fetch_word Plain.M.loaded_segments (0x1704c : word) = Some W_1704c.
Proof. vm_refl. Qed.
Lemma D_1704c : decode_any W_1704c = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17050 : bv 32 := 0x0089a583.
Lemma F_17050 : fetch_word Plain.M.loaded_segments (0x17050 : word) = Some W_17050.
Proof. vm_refl. Qed.
Lemma D_17050 : decode_any W_17050 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17054 : bv 32 := 0x02000613.
Lemma F_17054 : fetch_word Plain.M.loaded_segments (0x17054 : word) = Some W_17054.
Proof. vm_refl. Qed.
Lemma D_17054 : decode_any W_17054 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17058 : bv 32 := 0x02c59263.
Lemma F_17058 : fetch_word Plain.M.loaded_segments (0x17058 : word) = Some W_17058.
Proof. vm_refl. Qed.
Lemma D_17058 : decode_any W_17058 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1705c : bv 32 := 0x20800513.
Lemma F_1705c : fetch_word Plain.M.loaded_segments (0x1705c : word) = Some W_1705c.
Proof. vm_refl. Qed.
Lemma D_1705c : decode_any W_1705c = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_17060 : bv 32 := 0x00100593.
Lemma F_17060 : fetch_word Plain.M.loaded_segments (0x17060 : word) = Some W_17060.
Proof. vm_refl. Qed.
Lemma D_17060 : decode_any W_17060 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17064 : bv 32 := 0x3f4000ef.
Lemma F_17064 : fetch_word Plain.M.loaded_segments (0x17064 : word) = Some W_17064.
Proof. vm_refl. Qed.
Lemma D_17064 : decode_any W_17064 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_17068 : bv 32 := 0x02050c63.
Lemma F_17068 : fetch_word Plain.M.loaded_segments (0x17068 : word) = Some W_17068.
Proof. vm_refl. Qed.
Lemma D_17068 : decode_any W_17068 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1706c : bv 32 := 0x00000593.
Lemma F_1706c : fetch_word Plain.M.loaded_segments (0x1706c : word) = Some W_1706c.
Proof. vm_refl. Qed.
Lemma D_1706c : decode_any W_1706c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17070 : bv 32 := 0x0109b603.
Lemma F_17070 : fetch_word Plain.M.loaded_segments (0x17070 : word) = Some W_17070.
Proof. vm_refl. Qed.
Lemma D_17070 : decode_any W_17070 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17074 : bv 32 := 0x00c53023.
Lemma F_17074 : fetch_word Plain.M.loaded_segments (0x17074 : word) = Some W_17074.
Proof. vm_refl. Qed.
Lemma D_17074 : decode_any W_17074 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17078 : bv 32 := 0x00a9b823.
Lemma F_17078 : fetch_word Plain.M.loaded_segments (0x17078 : word) = Some W_17078.
Proof. vm_refl. Qed.
Lemma D_17078 : decode_any W_17078 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1707c : bv 32 := 0x00000913.
Lemma F_1707c : fetch_word Plain.M.loaded_segments (0x1707c : word) = Some W_1707c.
Proof. vm_refl. Qed.
Lemma D_1707c : decode_any W_1707c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17080 : bv 32 := 0x00359613.
Lemma F_17080 : fetch_word Plain.M.loaded_segments (0x17080 : word) = Some W_17080.
Proof. vm_refl. Qed.
Lemma D_17080 : decode_any W_17080 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_17084 : bv 32 := 0x00c50533.
Lemma F_17084 : fetch_word Plain.M.loaded_segments (0x17084 : word) = Some W_17084.
Proof. vm_refl. Qed.
Lemma D_17084 : decode_any W_17084 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17088 : bv 32 := 0x00000617.
Lemma F_17088 : fetch_word Plain.M.loaded_segments (0x17088 : word) = Some W_17088.
Proof. vm_refl. Qed.
Lemma D_17088 : decode_any W_17088 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1708c : bv 32 := 0x00158593.
Lemma F_1708c : fetch_word Plain.M.loaded_segments (0x1708c : word) = Some W_1708c.
Proof. vm_refl. Qed.
Lemma D_1708c : decode_any W_1708c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17090 : bv 32 := 0x04060613.
Lemma F_17090 : fetch_word Plain.M.loaded_segments (0x17090 : word) = Some W_17090.
Proof. vm_refl. Qed.
Lemma D_17090 : decode_any W_17090 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_17094 : bv 32 := 0x00c53423.
Lemma F_17094 : fetch_word Plain.M.loaded_segments (0x17094 : word) = Some W_17094.
Proof. vm_refl. Qed.
Lemma D_17094 : decode_any W_17094 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17098 : bv 32 := 0x10953423.
Lemma F_17098 : fetch_word Plain.M.loaded_segments (0x17098 : word) = Some W_17098.
Proof. vm_refl. Qed.
Lemma D_17098 : decode_any W_17098 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_1709c : bv 32 := 0x00b9a423.
Lemma F_1709c : fetch_word Plain.M.loaded_segments (0x1709c : word) = Some W_1709c.
Proof. vm_refl. Qed.
Lemma D_1709c : decode_any W_1709c = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_170a0 : bv 32 := 0x00040513.
Lemma F_170a0 : fetch_word Plain.M.loaded_segments (0x170a0 : word) = Some W_170a0.
Proof. vm_refl. Qed.
Lemma D_170a0 : decode_any W_170a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_170a4 : bv 32 := 0x53d070ef.
Lemma F_170a4 : fetch_word Plain.M.loaded_segments (0x170a4 : word) = Some W_170a4.
Proof. vm_refl. Qed.
Lemma D_170a4 : decode_any W_170a4 = Some (Jal 1 32060, 4%Z).
Proof. vm_refl. Qed.

Definition W_170a8 : bv 32 := 0x00090513.
Lemma F_170a8 : fetch_word Plain.M.loaded_segments (0x170a8 : word) = Some W_170a8.
Proof. vm_refl. Qed.
Lemma D_170a8 : decode_any W_170a8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_170ac : bv 32 := 0x02813083.
Lemma F_170ac : fetch_word Plain.M.loaded_segments (0x170ac : word) = Some W_170ac.
Proof. vm_refl. Qed.
Lemma D_170ac : decode_any W_170ac = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_170b0 : bv 32 := 0x02013403.
Lemma F_170b0 : fetch_word Plain.M.loaded_segments (0x170b0 : word) = Some W_170b0.
Proof. vm_refl. Qed.
Lemma D_170b0 : decode_any W_170b0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_170b4 : bv 32 := 0x01813483.
Lemma F_170b4 : fetch_word Plain.M.loaded_segments (0x170b4 : word) = Some W_170b4.
Proof. vm_refl. Qed.
Lemma D_170b4 : decode_any W_170b4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_170b8 : bv 32 := 0x01013903.
Lemma F_170b8 : fetch_word Plain.M.loaded_segments (0x170b8 : word) = Some W_170b8.
Proof. vm_refl. Qed.
Lemma D_170b8 : decode_any W_170b8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_170bc : bv 32 := 0x00813983.
Lemma F_170bc : fetch_word Plain.M.loaded_segments (0x170bc : word) = Some W_170bc.
Proof. vm_refl. Qed.
Lemma D_170bc : decode_any W_170bc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_170c0 : bv 32 := 0x03010113.
Lemma F_170c0 : fetch_word Plain.M.loaded_segments (0x170c0 : word) = Some W_170c0.
Proof. vm_refl. Qed.
Lemma D_170c0 : decode_any W_170c0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_170c4 : bv 32 := 0x00008067.
Lemma F_170c4 : fetch_word Plain.M.loaded_segments (0x170c4 : word) = Some W_170c4.
Proof. vm_refl. Qed.
Lemma D_170c4 : decode_any W_170c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_170c8 : bv 32 := 0x00050067.
Lemma F_170c8 : fetch_word Plain.M.loaded_segments (0x170c8 : word) = Some W_170c8.
Proof. vm_refl. Qed.
Lemma D_170c8 : decode_any W_170c8 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_170cc : bv 32 := 0x00008067.
Lemma F_170cc : fetch_word Plain.M.loaded_segments (0x170cc : word) = Some W_170cc.
Proof. vm_refl. Qed.
Lemma D_170cc : decode_any W_170cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_170d0 : bv 32 := 0xfe010113.
Lemma F_170d0 : fetch_word Plain.M.loaded_segments (0x170d0 : word) = Some W_170d0.
Proof. vm_refl. Qed.
Lemma D_170d0 : decode_any W_170d0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_170d4 : bv 32 := 0x00113c23.
Lemma F_170d4 : fetch_word Plain.M.loaded_segments (0x170d4 : word) = Some W_170d4.
Proof. vm_refl. Qed.
Lemma D_170d4 : decode_any W_170d4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_170d8 : bv 32 := 0x00813823.
Lemma F_170d8 : fetch_word Plain.M.loaded_segments (0x170d8 : word) = Some W_170d8.
Proof. vm_refl. Qed.
Lemma D_170d8 : decode_any W_170d8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_170dc : bv 32 := 0x00913423.
Lemma F_170dc : fetch_word Plain.M.loaded_segments (0x170dc : word) = Some W_170dc.
Proof. vm_refl. Qed.
Lemma D_170dc : decode_any W_170dc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_170e0 : bv 32 := 0x00009517.
Lemma F_170e0 : fetch_word Plain.M.loaded_segments (0x170e0 : word) = Some W_170e0.
Proof. vm_refl. Qed.
Lemma D_170e0 : decode_any W_170e0 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_170e4 : bv 32 := 0x00009597.
Lemma F_170e4 : fetch_word Plain.M.loaded_segments (0x170e4 : word) = Some W_170e4.
Proof. vm_refl. Qed.
Lemma D_170e4 : decode_any W_170e4 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_170e8 : bv 32 := 0xef853503.
Lemma F_170e8 : fetch_word Plain.M.loaded_segments (0x170e8 : word) = Some W_170e8.
Proof. vm_refl. Qed.
Lemma D_170e8 : decode_any W_170e8 = Some (Load SZ8 true 10 10 3832, 4%Z).
Proof. vm_refl. Qed.

Definition W_170ec : bv 32 := 0xefc5b403.
Lemma F_170ec : fetch_word Plain.M.loaded_segments (0x170ec : word) = Some W_170ec.
Proof. vm_refl. Qed.
Lemma D_170ec : decode_any W_170ec = Some (Load SZ8 true 8 11 3836, 4%Z).
Proof. vm_refl. Qed.

Definition W_170f0 : bv 32 := 0x00a47c63.
Lemma F_170f0 : fetch_word Plain.M.loaded_segments (0x170f0 : word) = Some W_170f0.
Proof. vm_refl. Qed.
Lemma D_170f0 : decode_any W_170f0 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_170f4 : bv 32 := 0xff853583.
Lemma F_170f4 : fetch_word Plain.M.loaded_segments (0x170f4 : word) = Some W_170f4.
Proof. vm_refl. Qed.
Lemma D_170f4 : decode_any W_170f4 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_170f8 : bv 32 := 0xff850493.
Lemma F_170f8 : fetch_word Plain.M.loaded_segments (0x170f8 : word) = Some W_170f8.
Proof. vm_refl. Qed.
Lemma D_170f8 : decode_any W_170f8 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_170fc : bv 32 := 0x000580e7.
Lemma F_170fc : fetch_word Plain.M.loaded_segments (0x170fc : word) = Some W_170fc.
Proof. vm_refl. Qed.
Lemma D_170fc : decode_any W_170fc = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17100 : bv 32 := 0x00048513.
Lemma F_17100 : fetch_word Plain.M.loaded_segments (0x17100 : word) = Some W_17100.
Proof. vm_refl. Qed.
Lemma D_17100 : decode_any W_17100 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17104 : bv 32 := 0xfe9468e3.
Lemma F_17104 : fetch_word Plain.M.loaded_segments (0x17104 : word) = Some W_17104.
Proof. vm_refl. Qed.
Lemma D_17104 : decode_any W_17104 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_17108 : bv 32 := 0x01813083.
Lemma F_17108 : fetch_word Plain.M.loaded_segments (0x17108 : word) = Some W_17108.
Proof. vm_refl. Qed.
Lemma D_17108 : decode_any W_17108 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1710c : bv 32 := 0x01013403.
Lemma F_1710c : fetch_word Plain.M.loaded_segments (0x1710c : word) = Some W_1710c.
Proof. vm_refl. Qed.
Lemma D_1710c : decode_any W_1710c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17110 : bv 32 := 0x00813483.
Lemma F_17110 : fetch_word Plain.M.loaded_segments (0x17110 : word) = Some W_17110.
Proof. vm_refl. Qed.
Lemma D_17110 : decode_any W_17110 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17114 : bv 32 := 0x02010113.
Lemma F_17114 : fetch_word Plain.M.loaded_segments (0x17114 : word) = Some W_17114.
Proof. vm_refl. Qed.
Lemma D_17114 : decode_any W_17114 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17118 : bv 32 := 0xfb5ff06f.
Lemma F_17118 : fetch_word Plain.M.loaded_segments (0x17118 : word) = Some W_17118.
Proof. vm_refl. Qed.
Lemma D_17118 : decode_any W_17118 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1711c : bv 32 := 0xff010113.
Lemma F_1711c : fetch_word Plain.M.loaded_segments (0x1711c : word) = Some W_1711c.
Proof. vm_refl. Qed.
Lemma D_1711c : decode_any W_1711c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17120 : bv 32 := 0x00113423.
Lemma F_17120 : fetch_word Plain.M.loaded_segments (0x17120 : word) = Some W_17120.
Proof. vm_refl. Qed.
Lemma D_17120 : decode_any W_17120 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17124 : bv 32 := 0x00813023.
Lemma F_17124 : fetch_word Plain.M.loaded_segments (0x17124 : word) = Some W_17124.
Proof. vm_refl. Qed.
Lemma D_17124 : decode_any W_17124 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17128 : bv 32 := 0x00000593.
Lemma F_17128 : fetch_word Plain.M.loaded_segments (0x17128 : word) = Some W_17128.
Proof. vm_refl. Qed.
Lemma D_17128 : decode_any W_17128 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1712c : bv 32 := 0x00020613.
Lemma F_1712c : fetch_word Plain.M.loaded_segments (0x1712c : word) = Some W_1712c.
Proof. vm_refl. Qed.
Lemma D_1712c : decode_any W_1712c = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17130 : bv 32 := 0xf5862603.
Lemma F_17130 : fetch_word Plain.M.loaded_segments (0x17130 : word) = Some W_17130.
Proof. vm_refl. Qed.
Lemma D_17130 : decode_any W_17130 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_17134 : bv 32 := 0x0003a697.
Lemma F_17134 : fetch_word Plain.M.loaded_segments (0x17134 : word) = Some W_17134.
Proof. vm_refl. Qed.
Lemma D_17134 : decode_any W_17134 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17138 : bv 32 := 0x49c68693.
Lemma F_17138 : fetch_word Plain.M.loaded_segments (0x17138 : word) = Some W_17138.
Proof. vm_refl. Qed.
Lemma D_17138 : decode_any W_17138 = Some (OpImm ALU_ADD 13 13 1180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1713c : bv 32 := 0x1606a72f.
Lemma F_1713c : fetch_word Plain.M.loaded_segments (0x1713c : word) = Some W_1713c.
Proof. vm_refl. Qed.
Lemma D_1713c : decode_any W_1713c = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17140 : bv 32 := 0x00b71663.
Lemma F_17140 : fetch_word Plain.M.loaded_segments (0x17140 : word) = Some W_17140.
Proof. vm_refl. Qed.
Lemma D_17140 : decode_any W_17140 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17144 : bv 32 := 0x1ec6a7af.
Lemma F_17144 : fetch_word Plain.M.loaded_segments (0x17144 : word) = Some W_17144.
Proof. vm_refl. Qed.
Lemma D_17144 : decode_any W_17144 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17148 : bv 32 := 0xfe079ae3.
Lemma F_17148 : fetch_word Plain.M.loaded_segments (0x17148 : word) = Some W_17148.
Proof. vm_refl. Qed.
Lemma D_17148 : decode_any W_17148 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1714c : bv 32 := 0x0007059b.
Lemma F_1714c : fetch_word Plain.M.loaded_segments (0x1714c : word) = Some W_1714c.
Proof. vm_refl. Qed.
Lemma D_1714c : decode_any W_1714c = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17150 : bv 32 := 0x02c58263.
Lemma F_17150 : fetch_word Plain.M.loaded_segments (0x17150 : word) = Some W_17150.
Proof. vm_refl. Qed.
Lemma D_17150 : decode_any W_17150 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_17154 : bv 32 := 0x02058263.
Lemma F_17154 : fetch_word Plain.M.loaded_segments (0x17154 : word) = Some W_17154.
Proof. vm_refl. Qed.
Lemma D_17154 : decode_any W_17154 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_17158 : bv 32 := 0x04900893.
Lemma F_17158 : fetch_word Plain.M.loaded_segments (0x17158 : word) = Some W_17158.
Proof. vm_refl. Qed.
Lemma D_17158 : decode_any W_17158 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_1715c : bv 32 := 0x00000593.
Lemma F_1715c : fetch_word Plain.M.loaded_segments (0x1715c : word) = Some W_1715c.
Proof. vm_refl. Qed.
Lemma D_1715c : decode_any W_1715c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17160 : bv 32 := 0x00000613.
Lemma F_17160 : fetch_word Plain.M.loaded_segments (0x17160 : word) = Some W_17160.
Proof. vm_refl. Qed.
Lemma D_17160 : decode_any W_17160 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17164 : bv 32 := 0x00000693.
Lemma F_17164 : fetch_word Plain.M.loaded_segments (0x17164 : word) = Some W_17164.
Proof. vm_refl. Qed.
Lemma D_17164 : decode_any W_17164 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17168 : bv 32 := 0x00000513.
Lemma F_17168 : fetch_word Plain.M.loaded_segments (0x17168 : word) = Some W_17168.
Proof. vm_refl. Qed.
Lemma D_17168 : decode_any W_17168 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1716c : bv 32 := 0x00000073.
Lemma F_1716c : fetch_word Plain.M.loaded_segments (0x1716c : word) = Some W_1716c.
Proof. vm_refl. Qed.
Lemma E_1716c : is_ecall W_1716c = true.
Proof. vm_refl. Qed.

Definition W_17170 : bv 32 := 0xff9ff06f.
Lemma F_17170 : fetch_word Plain.M.loaded_segments (0x17170 : word) = Some W_17170.
Proof. vm_refl. Qed.
Lemma D_17170 : decode_any W_17170 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_17174 : bv 32 := 0x00000023.
Lemma F_17174 : fetch_word Plain.M.loaded_segments (0x17174 : word) = Some W_17174.
Proof. vm_refl. Qed.
Lemma D_17174 : decode_any W_17174 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17178 : bv 32 := 0x00050413.
Lemma F_17178 : fetch_word Plain.M.loaded_segments (0x17178 : word) = Some W_17178.
Proof. vm_refl. Qed.
Lemma D_17178 : decode_any W_17178 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1717c : bv 32 := 0xdbdff0ef.
Lemma F_1717c : fetch_word Plain.M.loaded_segments (0x1717c : word) = Some W_1717c.
Proof. vm_refl. Qed.
Lemma D_1717c : decode_any W_1717c = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_17180 : bv 32 := 0xf51ff0ef.
Lemma F_17180 : fetch_word Plain.M.loaded_segments (0x17180 : word) = Some W_17180.
Proof. vm_refl. Qed.
Lemma D_17180 : decode_any W_17180 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_17184 : bv 32 := 0x160020ef.
Lemma F_17184 : fetch_word Plain.M.loaded_segments (0x17184 : word) = Some W_17184.
Proof. vm_refl. Qed.
Lemma D_17184 : decode_any W_17184 = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

Definition W_17188 : bv 32 := 0x00040513.
Lemma F_17188 : fetch_word Plain.M.loaded_segments (0x17188 : word) = Some W_17188.
Proof. vm_refl. Qed.
Lemma D_17188 : decode_any W_17188 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1718c : bv 32 := 0xd91ff0ef.
Lemma F_1718c : fetch_word Plain.M.loaded_segments (0x1718c : word) = Some W_1718c.
Proof. vm_refl. Qed.
Lemma D_1718c : decode_any W_1718c = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_1eb58 : bv 32 := 0x00033597.
Lemma F_1eb58 : fetch_word Plain.M.loaded_segments (0x1eb58 : word) = Some W_1eb58.
Proof. vm_refl. Qed.
Lemma D_1eb58 : decode_any W_1eb58 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_1eb5c : bv 32 := 0xaa358683.
Lemma F_1eb5c : fetch_word Plain.M.loaded_segments (0x1eb5c : word) = Some W_1eb5c.
Proof. vm_refl. Qed.
Lemma D_1eb5c : decode_any W_1eb5c = Some (Load SZ1 true 13 11 2723, 4%Z).
Proof. vm_refl. Qed.

Definition W_1eb60 : bv 32 := 0x1e068863.
Lemma F_1eb60 : fetch_word Plain.M.loaded_segments (0x1eb60 : word) = Some W_1eb60.
Proof. vm_refl. Qed.
Lemma D_1eb60 : decode_any W_1eb60 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ed50 : bv 32 := 0x00008067.
Lemma F_1ed50 : fetch_word Plain.M.loaded_segments (0x1ed50 : word) = Some W_1ed50.
Proof. vm_refl. Qed.
Lemma D_1ed50 : decode_any W_1ed50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ede0 : bv 32 := 0x00052583.
Lemma F_1ede0 : fetch_word Plain.M.loaded_segments (0x1ede0 : word) = Some W_1ede0.
Proof. vm_refl. Qed.
Lemma D_1ede0 : decode_any W_1ede0 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ede4 : bv 32 := 0x0005c463.
Lemma F_1ede4 : fetch_word Plain.M.loaded_segments (0x1ede4 : word) = Some W_1ede4.
Proof. vm_refl. Qed.
Lemma D_1ede4 : decode_any W_1ede4 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ede8 : bv 32 := 0x00008067.
Lemma F_1ede8 : fetch_word Plain.M.loaded_segments (0x1ede8 : word) = Some W_1ede8.
Proof. vm_refl. Qed.
Lemma D_1ede8 : decode_any W_1ede8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
