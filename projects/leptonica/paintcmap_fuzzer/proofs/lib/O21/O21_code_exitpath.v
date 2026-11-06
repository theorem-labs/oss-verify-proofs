(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.H Require GcFlushS21.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_13768 : bv 32 := 0xffffe517.
Lemma F_13768 : fetch_word Plain.M.loaded_segments (0x13768 : word) = Some W_13768.
Proof. vm_refl. Qed.
Lemma D_13768 : decode_any W_13768 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_1376c : bv 32 := 0x5c050513.
Lemma F_1376c : fetch_word Plain.M.loaded_segments (0x1376c : word) = Some W_1376c.
Proof. vm_refl. Qed.
Lemma D_1376c : decode_any W_1376c = Some (OpImm ALU_ADD 10 10 1472, 4%Z).
Proof. vm_refl. Qed.

Definition W_13770 : bv 32 := 0x0000e597.
Lemma F_13770 : fetch_word Plain.M.loaded_segments (0x13770 : word) = Some W_13770.
Proof. vm_refl. Qed.
Lemma D_13770 : decode_any W_13770 = Some (Auipc 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_13774 : bv 32 := 0x03858593.
Lemma F_13774 : fetch_word Plain.M.loaded_segments (0x13774 : word) = Some W_13774.
Proof. vm_refl. Qed.
Lemma D_13774 : decode_any W_13774 = Some (OpImm ALU_ADD 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_13778 : bv 32 := 0x000000ef.
Lemma F_13778 : fetch_word Plain.M.loaded_segments (0x13778 : word) = Some W_13778.
Proof. vm_refl. Qed.
Lemma D_13778 : decode_any W_13778 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1377c : bv 32 := 0x0040006f.
Lemma F_1377c : fetch_word Plain.M.loaded_segments (0x1377c : word) = Some W_1377c.
Proof. vm_refl. Qed.
Lemma D_1377c : decode_any W_1377c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13780 : bv 32 := 0x00813083.
Lemma F_13780 : fetch_word Plain.M.loaded_segments (0x13780 : word) = Some W_13780.
Proof. vm_refl. Qed.
Lemma D_13780 : decode_any W_13780 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13784 : bv 32 := 0x00013403.
Lemma F_13784 : fetch_word Plain.M.loaded_segments (0x13784 : word) = Some W_13784.
Proof. vm_refl. Qed.
Lemma D_13784 : decode_any W_13784 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13788 : bv 32 := 0x01010113.
Lemma F_13788 : fetch_word Plain.M.loaded_segments (0x13788 : word) = Some W_13788.
Proof. vm_refl. Qed.
Lemma D_13788 : decode_any W_13788 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1378c : bv 32 := 0x00008067.
Lemma F_1378c : fetch_word Plain.M.loaded_segments (0x1378c : word) = Some W_1378c.
Proof. vm_refl. Qed.
Lemma D_1378c : decode_any W_1378c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13790 : bv 32 := 0xff010113.
Lemma F_13790 : fetch_word Plain.M.loaded_segments (0x13790 : word) = Some W_13790.
Proof. vm_refl. Qed.
Lemma D_13790 : decode_any W_13790 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_13794 : bv 32 := 0x00113423.
Lemma F_13794 : fetch_word Plain.M.loaded_segments (0x13794 : word) = Some W_13794.
Proof. vm_refl. Qed.
Lemma D_13794 : decode_any W_13794 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13798 : bv 32 := 0x00813023.
Lemma F_13798 : fetch_word Plain.M.loaded_segments (0x13798 : word) = Some W_13798.
Proof. vm_refl. Qed.
Lemma D_13798 : decode_any W_13798 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1379c : bv 32 := 0x01010413.
Lemma F_1379c : fetch_word Plain.M.loaded_segments (0x1379c : word) = Some W_1379c.
Proof. vm_refl. Qed.
Lemma D_1379c : decode_any W_1379c = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_137a0 : bv 32 := 0x0000e517.
Lemma F_137a0 : fetch_word Plain.M.loaded_segments (0x137a0 : word) = Some W_137a0.
Proof. vm_refl. Qed.
Lemma D_137a0 : decode_any W_137a0 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_137a4 : bv 32 := 0x04850513.
Lemma F_137a4 : fetch_word Plain.M.loaded_segments (0x137a4 : word) = Some W_137a4.
Proof. vm_refl. Qed.
Lemma D_137a4 : decode_any W_137a4 = Some (OpImm ALU_ADD 10 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_137a8 : bv 32 := 0x00054503.
Lemma F_137a8 : fetch_word Plain.M.loaded_segments (0x137a8 : word) = Some W_137a8.
Proof. vm_refl. Qed.
Lemma D_137a8 : decode_any W_137a8 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_137ac : bv 32 := 0x00157513.
Lemma F_137ac : fetch_word Plain.M.loaded_segments (0x137ac : word) = Some W_137ac.
Proof. vm_refl. Qed.
Lemma D_137ac : decode_any W_137ac = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_137b0 : bv 32 := 0x00050663.
Lemma F_137b0 : fetch_word Plain.M.loaded_segments (0x137b0 : word) = Some W_137b0.
Proof. vm_refl. Qed.
Lemma D_137b0 : decode_any W_137b0 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_137b4 : bv 32 := 0x0040006f.
Lemma F_137b4 : fetch_word Plain.M.loaded_segments (0x137b4 : word) = Some W_137b4.
Proof. vm_refl. Qed.
Lemma D_137b4 : decode_any W_137b4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_137b8 : bv 32 := 0x0580006f.
Lemma F_137b8 : fetch_word Plain.M.loaded_segments (0x137b8 : word) = Some W_137b8.
Proof. vm_refl. Qed.
Lemma D_137b8 : decode_any W_137b8 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_137bc : bv 32 := 0x0000e517.
Lemma F_137bc : fetch_word Plain.M.loaded_segments (0x137bc : word) = Some W_137bc.
Proof. vm_refl. Qed.
Lemma D_137bc : decode_any W_137bc = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_137c0 : bv 32 := 0x02c50593.
Lemma F_137c0 : fetch_word Plain.M.loaded_segments (0x137c0 : word) = Some W_137c0.
Proof. vm_refl. Qed.
Lemma D_137c0 : decode_any W_137c0 = Some (OpImm ALU_ADD 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_137c4 : bv 32 := 0x00100513.
Lemma F_137c4 : fetch_word Plain.M.loaded_segments (0x137c4 : word) = Some W_137c4.
Proof. vm_refl. Qed.
Lemma D_137c4 : decode_any W_137c4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_137c8 : bv 32 := 0x00a58023.
Lemma F_137c8 : fetch_word Plain.M.loaded_segments (0x137c8 : word) = Some W_137c8.
Proof. vm_refl. Qed.
Lemma D_137c8 : decode_any W_137c8 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_137cc : bv 32 := 0x0000d517.
Lemma F_137cc : fetch_word Plain.M.loaded_segments (0x137cc : word) = Some W_137cc.
Proof. vm_refl. Qed.
Lemma D_137cc : decode_any W_137cc = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_137d0 : bv 32 := 0xd2c53503.
Lemma F_137d0 : fetch_word Plain.M.loaded_segments (0x137d0 : word) = Some W_137d0.
Proof. vm_refl. Qed.
Lemma D_137d0 : decode_any W_137d0 = Some (Load SZ8 true 10 10 3372, 4%Z).
Proof. vm_refl. Qed.

Definition W_137d4 : bv 32 := 0x00050e63.
Lemma F_137d4 : fetch_word Plain.M.loaded_segments (0x137d4 : word) = Some W_137d4.
Proof. vm_refl. Qed.
Lemma D_137d4 : decode_any W_137d4 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_137d8 : bv 32 := 0x0040006f.
Lemma F_137d8 : fetch_word Plain.M.loaded_segments (0x137d8 : word) = Some W_137d8.
Proof. vm_refl. Qed.
Lemma D_137d8 : decode_any W_137d8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_137dc : bv 32 := 0x0000e517.
Lemma F_137dc : fetch_word Plain.M.loaded_segments (0x137dc : word) = Some W_137dc.
Proof. vm_refl. Qed.
Lemma D_137dc : decode_any W_137dc = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_137e0 : bv 32 := 0xd8c50513.
Lemma F_137e0 : fetch_word Plain.M.loaded_segments (0x137e0 : word) = Some W_137e0.
Proof. vm_refl. Qed.
Lemma D_137e0 : decode_any W_137e0 = Some (OpImm ALU_ADD 10 10 3468, 4%Z).
Proof. vm_refl. Qed.

Definition W_137e4 : bv 32 := 0x00053503.
Lemma F_137e4 : fetch_word Plain.M.loaded_segments (0x137e4 : word) = Some W_137e4.
Proof. vm_refl. Qed.
Lemma D_137e4 : decode_any W_137e4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_137e8 : bv 32 := 0x595030ef.
Lemma F_137e8 : fetch_word Plain.M.loaded_segments (0x137e8 : word) = Some W_137e8.
Proof. vm_refl. Qed.
Lemma D_137e8 : decode_any W_137e8 = Some (Jal 1 15764, 4%Z).
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

Definition W_137f4 : bv 32 := 0xd1053503.
Lemma F_137f4 : fetch_word Plain.M.loaded_segments (0x137f4 : word) = Some W_137f4.
Proof. vm_refl. Qed.
Lemma D_137f4 : decode_any W_137f4 = Some (Load SZ8 true 10 10 3344, 4%Z).
Proof. vm_refl. Qed.

Definition W_137f8 : bv 32 := 0x00050c63.
Lemma F_137f8 : fetch_word Plain.M.loaded_segments (0x137f8 : word) = Some W_137f8.
Proof. vm_refl. Qed.
Lemma D_137f8 : decode_any W_137f8 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_137fc : bv 32 := 0x0040006f.
Lemma F_137fc : fetch_word Plain.M.loaded_segments (0x137fc : word) = Some W_137fc.
Proof. vm_refl. Qed.
Lemma D_137fc : decode_any W_137fc = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13800 : bv 32 := 0xffffe517.
Lemma F_13800 : fetch_word Plain.M.loaded_segments (0x13800 : word) = Some W_13800.
Proof. vm_refl. Qed.
Lemma D_13800 : decode_any W_13800 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

Definition W_13804 : bv 32 := 0x52850513.
Lemma F_13804 : fetch_word Plain.M.loaded_segments (0x13804 : word) = Some W_13804.
Proof. vm_refl. Qed.
Lemma D_13804 : decode_any W_13804 = Some (OpImm ALU_ADD 10 10 1320, 4%Z).
Proof. vm_refl. Qed.

Definition W_13808 : bv 32 := 0x000000ef.
Lemma F_13808 : fetch_word Plain.M.loaded_segments (0x13808 : word) = Some W_13808.
Proof. vm_refl. Qed.
Lemma D_13808 : decode_any W_13808 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1380c : bv 32 := 0x0040006f.
Lemma F_1380c : fetch_word Plain.M.loaded_segments (0x1380c : word) = Some W_1380c.
Proof. vm_refl. Qed.
Lemma D_1380c : decode_any W_1380c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13810 : bv 32 := 0x00813083.
Lemma F_13810 : fetch_word Plain.M.loaded_segments (0x13810 : word) = Some W_13810.
Proof. vm_refl. Qed.
Lemma D_13810 : decode_any W_13810 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13814 : bv 32 := 0x00013403.
Lemma F_13814 : fetch_word Plain.M.loaded_segments (0x13814 : word) = Some W_13814.
Proof. vm_refl. Qed.
Lemma D_13814 : decode_any W_13814 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13818 : bv 32 := 0x01010113.
Lemma F_13818 : fetch_word Plain.M.loaded_segments (0x13818 : word) = Some W_13818.
Proof. vm_refl. Qed.
Lemma D_13818 : decode_any W_13818 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1381c : bv 32 := 0x00008067.
Lemma F_1381c : fetch_word Plain.M.loaded_segments (0x1381c : word) = Some W_1381c.
Proof. vm_refl. Qed.
Lemma D_1381c : decode_any W_1381c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c48 : bv 32 := 0x0001e517.
Lemma F_13c48 : fetch_word Plain.M.loaded_segments (0x13c48 : word) = Some W_13c48.
Proof. vm_refl. Qed.
Lemma D_13c48 : decode_any W_13c48 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c4c : bv 32 := 0xbac54503.
Lemma F_13c4c : fetch_word Plain.M.loaded_segments (0x13c4c : word) = Some W_13c4c.
Proof. vm_refl. Qed.
Lemma D_13c4c : decode_any W_13c4c = Some (Load SZ1 false 10 10 2988, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c50 : bv 32 := 0x00051463.
Lemma F_13c50 : fetch_word Plain.M.loaded_segments (0x13c50 : word) = Some W_13c50.
Proof. vm_refl. Qed.
Lemma D_13c50 : decode_any W_13c50 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c54 : bv 32 := 0x00008067.
Lemma F_13c54 : fetch_word Plain.M.loaded_segments (0x13c54 : word) = Some W_13c54.
Proof. vm_refl. Qed.
Lemma D_13c54 : decode_any W_13c54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c58 : bv 32 := 0xff010113.
Lemma F_13c58 : fetch_word Plain.M.loaded_segments (0x13c58 : word) = Some W_13c58.
Proof. vm_refl. Qed.
Lemma D_13c58 : decode_any W_13c58 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c5c : bv 32 := 0x00113423.
Lemma F_13c5c : fetch_word Plain.M.loaded_segments (0x13c5c : word) = Some W_13c5c.
Proof. vm_refl. Qed.
Lemma D_13c5c : decode_any W_13c5c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c60 : bv 32 := 0x0000d517.
Lemma F_13c60 : fetch_word Plain.M.loaded_segments (0x13c60 : word) = Some W_13c60.
Proof. vm_refl. Qed.
Lemma D_13c60 : decode_any W_13c60 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c64 : bv 32 := 0x8b853503.
Lemma F_13c64 : fetch_word Plain.M.loaded_segments (0x13c64 : word) = Some W_13c64.
Proof. vm_refl. Qed.
Lemma D_13c64 : decode_any W_13c64 = Some (Load SZ8 true 10 10 2232, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c68 : bv 32 := 0x00053503.
Lemma F_13c68 : fetch_word Plain.M.loaded_segments (0x13c68 : word) = Some W_13c68.
Proof. vm_refl. Qed.
Lemma D_13c68 : decode_any W_13c68 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c6c : bv 32 := 0x285050ef.
Lemma F_13c6c : fetch_word Plain.M.loaded_segments (0x13c6c : word) = Some W_13c6c.
Proof. vm_refl. Qed.
Lemma D_13c6c : decode_any W_13c6c = Some (Jal 1 23172, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c70 : bv 32 := 0x04d00513.
Lemma F_13c70 : fetch_word Plain.M.loaded_segments (0x13c70 : word) = Some W_13c70.
Proof. vm_refl. Qed.
Lemma D_13c70 : decode_any W_13c70 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

Definition W_13c74 : bv 32 := 0x7900b0ef.
Lemma F_13c74 : fetch_word Plain.M.loaded_segments (0x13c74 : word) = Some W_13c74.
Proof. vm_refl. Qed.
Lemma D_13c74 : decode_any W_13c74 = Some (Jal 1 46992, 4%Z).
Proof. vm_refl. Qed.

Definition W_174b4 : bv 32 := 0xfd010113.
Lemma F_174b4 : fetch_word Plain.M.loaded_segments (0x174b4 : word) = Some W_174b4.
Proof. vm_refl. Qed.
Lemma D_174b4 : decode_any W_174b4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_174b8 : bv 32 := 0x02113423.
Lemma F_174b8 : fetch_word Plain.M.loaded_segments (0x174b8 : word) = Some W_174b8.
Proof. vm_refl. Qed.
Lemma D_174b8 : decode_any W_174b8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_174bc : bv 32 := 0x02813023.
Lemma F_174bc : fetch_word Plain.M.loaded_segments (0x174bc : word) = Some W_174bc.
Proof. vm_refl. Qed.
Lemma D_174bc : decode_any W_174bc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_174c0 : bv 32 := 0x00913c23.
Lemma F_174c0 : fetch_word Plain.M.loaded_segments (0x174c0 : word) = Some W_174c0.
Proof. vm_refl. Qed.
Lemma D_174c0 : decode_any W_174c0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_174c4 : bv 32 := 0x01213823.
Lemma F_174c4 : fetch_word Plain.M.loaded_segments (0x174c4 : word) = Some W_174c4.
Proof. vm_refl. Qed.
Lemma D_174c4 : decode_any W_174c4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_174c8 : bv 32 := 0x01313423.
Lemma F_174c8 : fetch_word Plain.M.loaded_segments (0x174c8 : word) = Some W_174c8.
Proof. vm_refl. Qed.
Lemma D_174c8 : decode_any W_174c8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_174cc : bv 32 := 0x0003a517.
Lemma F_174cc : fetch_word Plain.M.loaded_segments (0x174cc : word) = Some W_174cc.
Proof. vm_refl. Qed.
Lemma D_174cc : decode_any W_174cc = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_174d0 : bv 32 := 0x46450913.
Lemma F_174d0 : fetch_word Plain.M.loaded_segments (0x174d0 : word) = Some W_174d0.
Proof. vm_refl. Qed.
Lemma D_174d0 : decode_any W_174d0 = Some (OpImm ALU_ADD 18 10 1124, 4%Z).
Proof. vm_refl. Qed.

Definition W_174d4 : bv 32 := 0x00490413.
Lemma F_174d4 : fetch_word Plain.M.loaded_segments (0x174d4 : word) = Some W_174d4.
Proof. vm_refl. Qed.
Lemma D_174d4 : decode_any W_174d4 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_174d8 : bv 32 := 0x00040513.
Lemma F_174d8 : fetch_word Plain.M.loaded_segments (0x174d8 : word) = Some W_174d8.
Proof. vm_refl. Qed.
Lemma D_174d8 : decode_any W_174d8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_174dc : bv 32 := 0x3f9070ef.
Lemma F_174dc : fetch_word Plain.M.loaded_segments (0x174dc : word) = Some W_174dc.
Proof. vm_refl. Qed.
Lemma D_174dc : decode_any W_174dc = Some (Jal 1 31736, 4%Z).
Proof. vm_refl. Qed.

Definition W_174e0 : bv 32 := 0x01093503.
Lemma F_174e0 : fetch_word Plain.M.loaded_segments (0x174e0 : word) = Some W_174e0.
Proof. vm_refl. Qed.
Lemma D_174e0 : decode_any W_174e0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_174e4 : bv 32 := 0x06050863.
Lemma F_174e4 : fetch_word Plain.M.loaded_segments (0x174e4 : word) = Some W_174e4.
Proof. vm_refl. Qed.
Lemma D_174e4 : decode_any W_174e4 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_174e8 : bv 32 := 0x00892583.
Lemma F_174e8 : fetch_word Plain.M.loaded_segments (0x174e8 : word) = Some W_174e8.
Proof. vm_refl. Qed.
Lemma D_174e8 : decode_any W_174e8 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_174ec : bv 32 := 0x0180006f.
Lemma F_174ec : fetch_word Plain.M.loaded_segments (0x174ec : word) = Some W_174ec.
Proof. vm_refl. Qed.
Lemma D_174ec : decode_any W_174ec = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_174f0 : bv 32 := 0x00053503.
Lemma F_174f0 : fetch_word Plain.M.loaded_segments (0x174f0 : word) = Some W_174f0.
Proof. vm_refl. Qed.
Lemma D_174f0 : decode_any W_174f0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_174f4 : bv 32 := 0x02000593.
Lemma F_174f4 : fetch_word Plain.M.loaded_segments (0x174f4 : word) = Some W_174f4.
Proof. vm_refl. Qed.
Lemma D_174f4 : decode_any W_174f4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_174f8 : bv 32 := 0x00b92423.
Lemma F_174f8 : fetch_word Plain.M.loaded_segments (0x174f8 : word) = Some W_174f8.
Proof. vm_refl. Qed.
Lemma D_174f8 : decode_any W_174f8 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_174fc : bv 32 := 0x00a93823.
Lemma F_174fc : fetch_word Plain.M.loaded_segments (0x174fc : word) = Some W_174fc.
Proof. vm_refl. Qed.
Lemma D_174fc : decode_any W_174fc = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17500 : bv 32 := 0x04050a63.
Lemma F_17500 : fetch_word Plain.M.loaded_segments (0x17500 : word) = Some W_17500.
Proof. vm_refl. Qed.
Lemma D_17500 : decode_any W_17500 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_17504 : bv 32 := 0xfff5861b.
Lemma F_17504 : fetch_word Plain.M.loaded_segments (0x17504 : word) = Some W_17504.
Proof. vm_refl. Qed.
Lemma D_17504 : decode_any W_17504 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17508 : bv 32 := 0x00c92423.
Lemma F_17508 : fetch_word Plain.M.loaded_segments (0x17508 : word) = Some W_17508.
Proof. vm_refl. Qed.
Lemma D_17508 : decode_any W_17508 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1750c : bv 32 := 0xfeb052e3.
Lemma F_1750c : fetch_word Plain.M.loaded_segments (0x1750c : word) = Some W_1750c.
Proof. vm_refl. Qed.
Lemma D_1750c : decode_any W_1750c = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_17510 : bv 32 := 0x01093503.
Lemma F_17510 : fetch_word Plain.M.loaded_segments (0x17510 : word) = Some W_17510.
Proof. vm_refl. Qed.
Lemma D_17510 : decode_any W_17510 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17514 : bv 32 := 0x00361613.
Lemma F_17514 : fetch_word Plain.M.loaded_segments (0x17514 : word) = Some W_17514.
Proof. vm_refl. Qed.
Lemma D_17514 : decode_any W_17514 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_17518 : bv 32 := 0x00c50533.
Lemma F_17518 : fetch_word Plain.M.loaded_segments (0x17518 : word) = Some W_17518.
Proof. vm_refl. Qed.
Lemma D_17518 : decode_any W_17518 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1751c : bv 32 := 0x00853983.
Lemma F_1751c : fetch_word Plain.M.loaded_segments (0x1751c : word) = Some W_1751c.
Proof. vm_refl. Qed.
Lemma D_1751c : decode_any W_1751c = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17520 : bv 32 := 0x10853483.
Lemma F_17520 : fetch_word Plain.M.loaded_segments (0x17520 : word) = Some W_17520.
Proof. vm_refl. Qed.
Lemma D_17520 : decode_any W_17520 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_17524 : bv 32 := 0x00040513.
Lemma F_17524 : fetch_word Plain.M.loaded_segments (0x17524 : word) = Some W_17524.
Proof. vm_refl. Qed.
Lemma D_17524 : decode_any W_17524 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17528 : bv 32 := 0x635070ef.
Lemma F_17528 : fetch_word Plain.M.loaded_segments (0x17528 : word) = Some W_17528.
Proof. vm_refl. Qed.
Lemma D_17528 : decode_any W_17528 = Some (Jal 1 32308, 4%Z).
Proof. vm_refl. Qed.

Definition W_1752c : bv 32 := 0x00048513.
Lemma F_1752c : fetch_word Plain.M.loaded_segments (0x1752c : word) = Some W_1752c.
Proof. vm_refl. Qed.
Lemma D_1752c : decode_any W_1752c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17530 : bv 32 := 0x000980e7.
Lemma F_17530 : fetch_word Plain.M.loaded_segments (0x17530 : word) = Some W_17530.
Proof. vm_refl. Qed.
Lemma D_17530 : decode_any W_17530 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17534 : bv 32 := 0x00040513.
Lemma F_17534 : fetch_word Plain.M.loaded_segments (0x17534 : word) = Some W_17534.
Proof. vm_refl. Qed.
Lemma D_17534 : decode_any W_17534 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17538 : bv 32 := 0x39d070ef.
Lemma F_17538 : fetch_word Plain.M.loaded_segments (0x17538 : word) = Some W_17538.
Proof. vm_refl. Qed.
Lemma D_17538 : decode_any W_17538 = Some (Jal 1 31644, 4%Z).
Proof. vm_refl. Qed.

Definition W_1753c : bv 32 := 0x00892503.
Lemma F_1753c : fetch_word Plain.M.loaded_segments (0x1753c : word) = Some W_1753c.
Proof. vm_refl. Qed.
Lemma D_1753c : decode_any W_1753c = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17540 : bv 32 := 0xfff5061b.
Lemma F_17540 : fetch_word Plain.M.loaded_segments (0x17540 : word) = Some W_17540.
Proof. vm_refl. Qed.
Lemma D_17540 : decode_any W_17540 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17544 : bv 32 := 0x00c92423.
Lemma F_17544 : fetch_word Plain.M.loaded_segments (0x17544 : word) = Some W_17544.
Proof. vm_refl. Qed.
Lemma D_17544 : decode_any W_17544 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17548 : bv 32 := 0xfca044e3.
Lemma F_17548 : fetch_word Plain.M.loaded_segments (0x17548 : word) = Some W_17548.
Proof. vm_refl. Qed.
Lemma D_17548 : decode_any W_17548 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_1754c : bv 32 := 0x01093503.
Lemma F_1754c : fetch_word Plain.M.loaded_segments (0x1754c : word) = Some W_1754c.
Proof. vm_refl. Qed.
Lemma D_1754c : decode_any W_1754c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17550 : bv 32 := 0xfa1ff06f.
Lemma F_17550 : fetch_word Plain.M.loaded_segments (0x17550 : word) = Some W_17550.
Proof. vm_refl. Qed.
Lemma D_17550 : decode_any W_17550 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_17554 : bv 32 := 0x00100513.
Lemma F_17554 : fetch_word Plain.M.loaded_segments (0x17554 : word) = Some W_17554.
Proof. vm_refl. Qed.
Lemma D_17554 : decode_any W_17554 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17558 : bv 32 := 0x00a90023.
Lemma F_17558 : fetch_word Plain.M.loaded_segments (0x17558 : word) = Some W_17558.
Proof. vm_refl. Qed.
Lemma D_17558 : decode_any W_17558 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1755c : bv 32 := 0x00040513.
Lemma F_1755c : fetch_word Plain.M.loaded_segments (0x1755c : word) = Some W_1755c.
Proof. vm_refl. Qed.
Lemma D_1755c : decode_any W_1755c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17560 : bv 32 := 0x02813083.
Lemma F_17560 : fetch_word Plain.M.loaded_segments (0x17560 : word) = Some W_17560.
Proof. vm_refl. Qed.
Lemma D_17560 : decode_any W_17560 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17564 : bv 32 := 0x02013403.
Lemma F_17564 : fetch_word Plain.M.loaded_segments (0x17564 : word) = Some W_17564.
Proof. vm_refl. Qed.
Lemma D_17564 : decode_any W_17564 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17568 : bv 32 := 0x01813483.
Lemma F_17568 : fetch_word Plain.M.loaded_segments (0x17568 : word) = Some W_17568.
Proof. vm_refl. Qed.
Lemma D_17568 : decode_any W_17568 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1756c : bv 32 := 0x01013903.
Lemma F_1756c : fetch_word Plain.M.loaded_segments (0x1756c : word) = Some W_1756c.
Proof. vm_refl. Qed.
Lemma D_1756c : decode_any W_1756c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17570 : bv 32 := 0x00813983.
Lemma F_17570 : fetch_word Plain.M.loaded_segments (0x17570 : word) = Some W_17570.
Proof. vm_refl. Qed.
Lemma D_17570 : decode_any W_17570 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17574 : bv 32 := 0x03010113.
Lemma F_17574 : fetch_word Plain.M.loaded_segments (0x17574 : word) = Some W_17574.
Proof. vm_refl. Qed.
Lemma D_17574 : decode_any W_17574 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_17578 : bv 32 := 0x5e50706f.
Lemma F_17578 : fetch_word Plain.M.loaded_segments (0x17578 : word) = Some W_17578.
Proof. vm_refl. Qed.
Lemma D_17578 : decode_any W_17578 = Some (Jal 0 32228, 4%Z).
Proof. vm_refl. Qed.

Definition W_1757c : bv 32 := 0x00008067.
Lemma F_1757c : fetch_word Plain.M.loaded_segments (0x1757c : word) = Some W_1757c.
Proof. vm_refl. Qed.
Lemma D_1757c : decode_any W_1757c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17580 : bv 32 := 0xfd010113.
Lemma F_17580 : fetch_word Plain.M.loaded_segments (0x17580 : word) = Some W_17580.
Proof. vm_refl. Qed.
Lemma D_17580 : decode_any W_17580 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_17584 : bv 32 := 0x02113423.
Lemma F_17584 : fetch_word Plain.M.loaded_segments (0x17584 : word) = Some W_17584.
Proof. vm_refl. Qed.
Lemma D_17584 : decode_any W_17584 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_17588 : bv 32 := 0x02813023.
Lemma F_17588 : fetch_word Plain.M.loaded_segments (0x17588 : word) = Some W_17588.
Proof. vm_refl. Qed.
Lemma D_17588 : decode_any W_17588 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1758c : bv 32 := 0x00913c23.
Lemma F_1758c : fetch_word Plain.M.loaded_segments (0x1758c : word) = Some W_1758c.
Proof. vm_refl. Qed.
Lemma D_1758c : decode_any W_1758c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17590 : bv 32 := 0x01213823.
Lemma F_17590 : fetch_word Plain.M.loaded_segments (0x17590 : word) = Some W_17590.
Proof. vm_refl. Qed.
Lemma D_17590 : decode_any W_17590 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17594 : bv 32 := 0x01313423.
Lemma F_17594 : fetch_word Plain.M.loaded_segments (0x17594 : word) = Some W_17594.
Proof. vm_refl. Qed.
Lemma D_17594 : decode_any W_17594 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17598 : bv 32 := 0x00050493.
Lemma F_17598 : fetch_word Plain.M.loaded_segments (0x17598 : word) = Some W_17598.
Proof. vm_refl. Qed.
Lemma D_17598 : decode_any W_17598 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1759c : bv 32 := 0x0003a517.
Lemma F_1759c : fetch_word Plain.M.loaded_segments (0x1759c : word) = Some W_1759c.
Proof. vm_refl. Qed.
Lemma D_1759c : decode_any W_1759c = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_175a0 : bv 32 := 0x39450993.
Lemma F_175a0 : fetch_word Plain.M.loaded_segments (0x175a0 : word) = Some W_175a0.
Proof. vm_refl. Qed.
Lemma D_175a0 : decode_any W_175a0 = Some (OpImm ALU_ADD 19 10 916, 4%Z).
Proof. vm_refl. Qed.

Definition W_175a4 : bv 32 := 0x00498413.
Lemma F_175a4 : fetch_word Plain.M.loaded_segments (0x175a4 : word) = Some W_175a4.
Proof. vm_refl. Qed.
Lemma D_175a4 : decode_any W_175a4 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_175a8 : bv 32 := 0x00040513.
Lemma F_175a8 : fetch_word Plain.M.loaded_segments (0x175a8 : word) = Some W_175a8.
Proof. vm_refl. Qed.
Lemma D_175a8 : decode_any W_175a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_175ac : bv 32 := 0x329070ef.
Lemma F_175ac : fetch_word Plain.M.loaded_segments (0x175ac : word) = Some W_175ac.
Proof. vm_refl. Qed.
Lemma D_175ac : decode_any W_175ac = Some (Jal 1 31528, 4%Z).
Proof. vm_refl. Qed.

Definition W_175b0 : bv 32 := 0x0009c503.
Lemma F_175b0 : fetch_word Plain.M.loaded_segments (0x175b0 : word) = Some W_175b0.
Proof. vm_refl. Qed.
Lemma D_175b0 : decode_any W_175b0 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_175b4 : bv 32 := 0xfff00913.
Lemma F_175b4 : fetch_word Plain.M.loaded_segments (0x175b4 : word) = Some W_175b4.
Proof. vm_refl. Qed.
Lemma D_175b4 : decode_any W_175b4 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_175b8 : bv 32 := 0x06051263.
Lemma F_175b8 : fetch_word Plain.M.loaded_segments (0x175b8 : word) = Some W_175b8.
Proof. vm_refl. Qed.
Lemma D_175b8 : decode_any W_175b8 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_175bc : bv 32 := 0x0109b503.
Lemma F_175bc : fetch_word Plain.M.loaded_segments (0x175bc : word) = Some W_175bc.
Proof. vm_refl. Qed.
Lemma D_175bc : decode_any W_175bc = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_175c0 : bv 32 := 0x00051663.
Lemma F_175c0 : fetch_word Plain.M.loaded_segments (0x175c0 : word) = Some W_175c0.
Proof. vm_refl. Qed.
Lemma D_175c0 : decode_any W_175c0 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_175c4 : bv 32 := 0x01898513.
Lemma F_175c4 : fetch_word Plain.M.loaded_segments (0x175c4 : word) = Some W_175c4.
Proof. vm_refl. Qed.
Lemma D_175c4 : decode_any W_175c4 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_175c8 : bv 32 := 0x00a9b823.
Lemma F_175c8 : fetch_word Plain.M.loaded_segments (0x175c8 : word) = Some W_175c8.
Proof. vm_refl. Qed.
Lemma D_175c8 : decode_any W_175c8 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_175cc : bv 32 := 0x0089a583.
Lemma F_175cc : fetch_word Plain.M.loaded_segments (0x175cc : word) = Some W_175cc.
Proof. vm_refl. Qed.
Lemma D_175cc : decode_any W_175cc = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_175d0 : bv 32 := 0x02000613.
Lemma F_175d0 : fetch_word Plain.M.loaded_segments (0x175d0 : word) = Some W_175d0.
Proof. vm_refl. Qed.
Lemma D_175d0 : decode_any W_175d0 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_175d4 : bv 32 := 0x02c59263.
Lemma F_175d4 : fetch_word Plain.M.loaded_segments (0x175d4 : word) = Some W_175d4.
Proof. vm_refl. Qed.
Lemma D_175d4 : decode_any W_175d4 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_175d8 : bv 32 := 0x20800513.
Lemma F_175d8 : fetch_word Plain.M.loaded_segments (0x175d8 : word) = Some W_175d8.
Proof. vm_refl. Qed.
Lemma D_175d8 : decode_any W_175d8 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

Definition W_175dc : bv 32 := 0x00100593.
Lemma F_175dc : fetch_word Plain.M.loaded_segments (0x175dc : word) = Some W_175dc.
Proof. vm_refl. Qed.
Lemma D_175dc : decode_any W_175dc = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_175e0 : bv 32 := 0x3f4000ef.
Lemma F_175e0 : fetch_word Plain.M.loaded_segments (0x175e0 : word) = Some W_175e0.
Proof. vm_refl. Qed.
Lemma D_175e0 : decode_any W_175e0 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

Definition W_175e4 : bv 32 := 0x02050c63.
Lemma F_175e4 : fetch_word Plain.M.loaded_segments (0x175e4 : word) = Some W_175e4.
Proof. vm_refl. Qed.
Lemma D_175e4 : decode_any W_175e4 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_175e8 : bv 32 := 0x00000593.
Lemma F_175e8 : fetch_word Plain.M.loaded_segments (0x175e8 : word) = Some W_175e8.
Proof. vm_refl. Qed.
Lemma D_175e8 : decode_any W_175e8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_175ec : bv 32 := 0x0109b603.
Lemma F_175ec : fetch_word Plain.M.loaded_segments (0x175ec : word) = Some W_175ec.
Proof. vm_refl. Qed.
Lemma D_175ec : decode_any W_175ec = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_175f0 : bv 32 := 0x00c53023.
Lemma F_175f0 : fetch_word Plain.M.loaded_segments (0x175f0 : word) = Some W_175f0.
Proof. vm_refl. Qed.
Lemma D_175f0 : decode_any W_175f0 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_175f4 : bv 32 := 0x00a9b823.
Lemma F_175f4 : fetch_word Plain.M.loaded_segments (0x175f4 : word) = Some W_175f4.
Proof. vm_refl. Qed.
Lemma D_175f4 : decode_any W_175f4 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_175f8 : bv 32 := 0x00000913.
Lemma F_175f8 : fetch_word Plain.M.loaded_segments (0x175f8 : word) = Some W_175f8.
Proof. vm_refl. Qed.
Lemma D_175f8 : decode_any W_175f8 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_175fc : bv 32 := 0x00359613.
Lemma F_175fc : fetch_word Plain.M.loaded_segments (0x175fc : word) = Some W_175fc.
Proof. vm_refl. Qed.
Lemma D_175fc : decode_any W_175fc = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_17600 : bv 32 := 0x00c50533.
Lemma F_17600 : fetch_word Plain.M.loaded_segments (0x17600 : word) = Some W_17600.
Proof. vm_refl. Qed.
Lemma D_17600 : decode_any W_17600 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17604 : bv 32 := 0x00000617.
Lemma F_17604 : fetch_word Plain.M.loaded_segments (0x17604 : word) = Some W_17604.
Proof. vm_refl. Qed.
Lemma D_17604 : decode_any W_17604 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17608 : bv 32 := 0x00158593.
Lemma F_17608 : fetch_word Plain.M.loaded_segments (0x17608 : word) = Some W_17608.
Proof. vm_refl. Qed.
Lemma D_17608 : decode_any W_17608 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1760c : bv 32 := 0x04060613.
Lemma F_1760c : fetch_word Plain.M.loaded_segments (0x1760c : word) = Some W_1760c.
Proof. vm_refl. Qed.
Lemma D_1760c : decode_any W_1760c = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_17610 : bv 32 := 0x00c53423.
Lemma F_17610 : fetch_word Plain.M.loaded_segments (0x17610 : word) = Some W_17610.
Proof. vm_refl. Qed.
Lemma D_17610 : decode_any W_17610 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17614 : bv 32 := 0x10953423.
Lemma F_17614 : fetch_word Plain.M.loaded_segments (0x17614 : word) = Some W_17614.
Proof. vm_refl. Qed.
Lemma D_17614 : decode_any W_17614 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_17618 : bv 32 := 0x00b9a423.
Lemma F_17618 : fetch_word Plain.M.loaded_segments (0x17618 : word) = Some W_17618.
Proof. vm_refl. Qed.
Lemma D_17618 : decode_any W_17618 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1761c : bv 32 := 0x00040513.
Lemma F_1761c : fetch_word Plain.M.loaded_segments (0x1761c : word) = Some W_1761c.
Proof. vm_refl. Qed.
Lemma D_1761c : decode_any W_1761c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17620 : bv 32 := 0x53d070ef.
Lemma F_17620 : fetch_word Plain.M.loaded_segments (0x17620 : word) = Some W_17620.
Proof. vm_refl. Qed.
Lemma D_17620 : decode_any W_17620 = Some (Jal 1 32060, 4%Z).
Proof. vm_refl. Qed.

Definition W_17624 : bv 32 := 0x00090513.
Lemma F_17624 : fetch_word Plain.M.loaded_segments (0x17624 : word) = Some W_17624.
Proof. vm_refl. Qed.
Lemma D_17624 : decode_any W_17624 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17628 : bv 32 := 0x02813083.
Lemma F_17628 : fetch_word Plain.M.loaded_segments (0x17628 : word) = Some W_17628.
Proof. vm_refl. Qed.
Lemma D_17628 : decode_any W_17628 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1762c : bv 32 := 0x02013403.
Lemma F_1762c : fetch_word Plain.M.loaded_segments (0x1762c : word) = Some W_1762c.
Proof. vm_refl. Qed.
Lemma D_1762c : decode_any W_1762c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17630 : bv 32 := 0x01813483.
Lemma F_17630 : fetch_word Plain.M.loaded_segments (0x17630 : word) = Some W_17630.
Proof. vm_refl. Qed.
Lemma D_17630 : decode_any W_17630 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17634 : bv 32 := 0x01013903.
Lemma F_17634 : fetch_word Plain.M.loaded_segments (0x17634 : word) = Some W_17634.
Proof. vm_refl. Qed.
Lemma D_17634 : decode_any W_17634 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17638 : bv 32 := 0x00813983.
Lemma F_17638 : fetch_word Plain.M.loaded_segments (0x17638 : word) = Some W_17638.
Proof. vm_refl. Qed.
Lemma D_17638 : decode_any W_17638 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1763c : bv 32 := 0x03010113.
Lemma F_1763c : fetch_word Plain.M.loaded_segments (0x1763c : word) = Some W_1763c.
Proof. vm_refl. Qed.
Lemma D_1763c : decode_any W_1763c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_17640 : bv 32 := 0x00008067.
Lemma F_17640 : fetch_word Plain.M.loaded_segments (0x17640 : word) = Some W_17640.
Proof. vm_refl. Qed.
Lemma D_17640 : decode_any W_17640 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17644 : bv 32 := 0x00050067.
Lemma F_17644 : fetch_word Plain.M.loaded_segments (0x17644 : word) = Some W_17644.
Proof. vm_refl. Qed.
Lemma D_17644 : decode_any W_17644 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17648 : bv 32 := 0x00008067.
Lemma F_17648 : fetch_word Plain.M.loaded_segments (0x17648 : word) = Some W_17648.
Proof. vm_refl. Qed.
Lemma D_17648 : decode_any W_17648 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1764c : bv 32 := 0xfe010113.
Lemma F_1764c : fetch_word Plain.M.loaded_segments (0x1764c : word) = Some W_1764c.
Proof. vm_refl. Qed.
Lemma D_1764c : decode_any W_1764c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_17650 : bv 32 := 0x00113c23.
Lemma F_17650 : fetch_word Plain.M.loaded_segments (0x17650 : word) = Some W_17650.
Proof. vm_refl. Qed.
Lemma D_17650 : decode_any W_17650 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17654 : bv 32 := 0x00813823.
Lemma F_17654 : fetch_word Plain.M.loaded_segments (0x17654 : word) = Some W_17654.
Proof. vm_refl. Qed.
Lemma D_17654 : decode_any W_17654 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17658 : bv 32 := 0x00913423.
Lemma F_17658 : fetch_word Plain.M.loaded_segments (0x17658 : word) = Some W_17658.
Proof. vm_refl. Qed.
Lemma D_17658 : decode_any W_17658 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1765c : bv 32 := 0x00009517.
Lemma F_1765c : fetch_word Plain.M.loaded_segments (0x1765c : word) = Some W_1765c.
Proof. vm_refl. Qed.
Lemma D_1765c : decode_any W_1765c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_17660 : bv 32 := 0x00009597.
Lemma F_17660 : fetch_word Plain.M.loaded_segments (0x17660 : word) = Some W_17660.
Proof. vm_refl. Qed.
Lemma D_17660 : decode_any W_17660 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_17664 : bv 32 := 0xefc53503.
Lemma F_17664 : fetch_word Plain.M.loaded_segments (0x17664 : word) = Some W_17664.
Proof. vm_refl. Qed.
Lemma D_17664 : decode_any W_17664 = Some (Load SZ8 true 10 10 3836, 4%Z).
Proof. vm_refl. Qed.

Definition W_17668 : bv 32 := 0xf005b403.
Lemma F_17668 : fetch_word Plain.M.loaded_segments (0x17668 : word) = Some W_17668.
Proof. vm_refl. Qed.
Lemma D_17668 : decode_any W_17668 = Some (Load SZ8 true 8 11 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_1766c : bv 32 := 0x00a47c63.
Lemma F_1766c : fetch_word Plain.M.loaded_segments (0x1766c : word) = Some W_1766c.
Proof. vm_refl. Qed.
Lemma D_1766c : decode_any W_1766c = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17670 : bv 32 := 0xff853583.
Lemma F_17670 : fetch_word Plain.M.loaded_segments (0x17670 : word) = Some W_17670.
Proof. vm_refl. Qed.
Lemma D_17670 : decode_any W_17670 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_17674 : bv 32 := 0xff850493.
Lemma F_17674 : fetch_word Plain.M.loaded_segments (0x17674 : word) = Some W_17674.
Proof. vm_refl. Qed.
Lemma D_17674 : decode_any W_17674 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_17678 : bv 32 := 0x000580e7.
Lemma F_17678 : fetch_word Plain.M.loaded_segments (0x17678 : word) = Some W_17678.
Proof. vm_refl. Qed.
Lemma D_17678 : decode_any W_17678 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1767c : bv 32 := 0x00048513.
Lemma F_1767c : fetch_word Plain.M.loaded_segments (0x1767c : word) = Some W_1767c.
Proof. vm_refl. Qed.
Lemma D_1767c : decode_any W_1767c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17680 : bv 32 := 0xfe9468e3.
Lemma F_17680 : fetch_word Plain.M.loaded_segments (0x17680 : word) = Some W_17680.
Proof. vm_refl. Qed.
Lemma D_17680 : decode_any W_17680 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_17684 : bv 32 := 0x01813083.
Lemma F_17684 : fetch_word Plain.M.loaded_segments (0x17684 : word) = Some W_17684.
Proof. vm_refl. Qed.
Lemma D_17684 : decode_any W_17684 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17688 : bv 32 := 0x01013403.
Lemma F_17688 : fetch_word Plain.M.loaded_segments (0x17688 : word) = Some W_17688.
Proof. vm_refl. Qed.
Lemma D_17688 : decode_any W_17688 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1768c : bv 32 := 0x00813483.
Lemma F_1768c : fetch_word Plain.M.loaded_segments (0x1768c : word) = Some W_1768c.
Proof. vm_refl. Qed.
Lemma D_1768c : decode_any W_1768c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17690 : bv 32 := 0x02010113.
Lemma F_17690 : fetch_word Plain.M.loaded_segments (0x17690 : word) = Some W_17690.
Proof. vm_refl. Qed.
Lemma D_17690 : decode_any W_17690 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17694 : bv 32 := 0xfb5ff06f.
Lemma F_17694 : fetch_word Plain.M.loaded_segments (0x17694 : word) = Some W_17694.
Proof. vm_refl. Qed.
Lemma D_17694 : decode_any W_17694 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_17698 : bv 32 := 0xff010113.
Lemma F_17698 : fetch_word Plain.M.loaded_segments (0x17698 : word) = Some W_17698.
Proof. vm_refl. Qed.
Lemma D_17698 : decode_any W_17698 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1769c : bv 32 := 0x00113423.
Lemma F_1769c : fetch_word Plain.M.loaded_segments (0x1769c : word) = Some W_1769c.
Proof. vm_refl. Qed.
Lemma D_1769c : decode_any W_1769c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_176a0 : bv 32 := 0x00813023.
Lemma F_176a0 : fetch_word Plain.M.loaded_segments (0x176a0 : word) = Some W_176a0.
Proof. vm_refl. Qed.
Lemma D_176a0 : decode_any W_176a0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_176a4 : bv 32 := 0x00000593.
Lemma F_176a4 : fetch_word Plain.M.loaded_segments (0x176a4 : word) = Some W_176a4.
Proof. vm_refl. Qed.
Lemma D_176a4 : decode_any W_176a4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_176a8 : bv 32 := 0x00020613.
Lemma F_176a8 : fetch_word Plain.M.loaded_segments (0x176a8 : word) = Some W_176a8.
Proof. vm_refl. Qed.
Lemma D_176a8 : decode_any W_176a8 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_176ac : bv 32 := 0xf5862603.
Lemma F_176ac : fetch_word Plain.M.loaded_segments (0x176ac : word) = Some W_176ac.
Proof. vm_refl. Qed.
Lemma D_176ac : decode_any W_176ac = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_176b0 : bv 32 := 0x0003a697.
Lemma F_176b0 : fetch_word Plain.M.loaded_segments (0x176b0 : word) = Some W_176b0.
Proof. vm_refl. Qed.
Lemma D_176b0 : decode_any W_176b0 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_176b4 : bv 32 := 0x4a068693.
Lemma F_176b4 : fetch_word Plain.M.loaded_segments (0x176b4 : word) = Some W_176b4.
Proof. vm_refl. Qed.
Lemma D_176b4 : decode_any W_176b4 = Some (OpImm ALU_ADD 13 13 1184, 4%Z).
Proof. vm_refl. Qed.

Definition W_176b8 : bv 32 := 0x1606a72f.
Lemma F_176b8 : fetch_word Plain.M.loaded_segments (0x176b8 : word) = Some W_176b8.
Proof. vm_refl. Qed.
Lemma D_176b8 : decode_any W_176b8 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_176bc : bv 32 := 0x00b71663.
Lemma F_176bc : fetch_word Plain.M.loaded_segments (0x176bc : word) = Some W_176bc.
Proof. vm_refl. Qed.
Lemma D_176bc : decode_any W_176bc = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_176c0 : bv 32 := 0x1ec6a7af.
Lemma F_176c0 : fetch_word Plain.M.loaded_segments (0x176c0 : word) = Some W_176c0.
Proof. vm_refl. Qed.
Lemma D_176c0 : decode_any W_176c0 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_176c4 : bv 32 := 0xfe079ae3.
Lemma F_176c4 : fetch_word Plain.M.loaded_segments (0x176c4 : word) = Some W_176c4.
Proof. vm_refl. Qed.
Lemma D_176c4 : decode_any W_176c4 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_176c8 : bv 32 := 0x0007059b.
Lemma F_176c8 : fetch_word Plain.M.loaded_segments (0x176c8 : word) = Some W_176c8.
Proof. vm_refl. Qed.
Lemma D_176c8 : decode_any W_176c8 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_176cc : bv 32 := 0x02c58263.
Lemma F_176cc : fetch_word Plain.M.loaded_segments (0x176cc : word) = Some W_176cc.
Proof. vm_refl. Qed.
Lemma D_176cc : decode_any W_176cc = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_176d0 : bv 32 := 0x02058263.
Lemma F_176d0 : fetch_word Plain.M.loaded_segments (0x176d0 : word) = Some W_176d0.
Proof. vm_refl. Qed.
Lemma D_176d0 : decode_any W_176d0 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_176d4 : bv 32 := 0x04900893.
Lemma F_176d4 : fetch_word Plain.M.loaded_segments (0x176d4 : word) = Some W_176d4.
Proof. vm_refl. Qed.
Lemma D_176d4 : decode_any W_176d4 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_176d8 : bv 32 := 0x00000593.
Lemma F_176d8 : fetch_word Plain.M.loaded_segments (0x176d8 : word) = Some W_176d8.
Proof. vm_refl. Qed.
Lemma D_176d8 : decode_any W_176d8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_176dc : bv 32 := 0x00000613.
Lemma F_176dc : fetch_word Plain.M.loaded_segments (0x176dc : word) = Some W_176dc.
Proof. vm_refl. Qed.
Lemma D_176dc : decode_any W_176dc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_176e0 : bv 32 := 0x00000693.
Lemma F_176e0 : fetch_word Plain.M.loaded_segments (0x176e0 : word) = Some W_176e0.
Proof. vm_refl. Qed.
Lemma D_176e0 : decode_any W_176e0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_176e4 : bv 32 := 0x00000513.
Lemma F_176e4 : fetch_word Plain.M.loaded_segments (0x176e4 : word) = Some W_176e4.
Proof. vm_refl. Qed.
Lemma D_176e4 : decode_any W_176e4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_176e8 : bv 32 := 0x00000073.
Lemma F_176e8 : fetch_word Plain.M.loaded_segments (0x176e8 : word) = Some W_176e8.
Proof. vm_refl. Qed.
Lemma E_176e8 : is_ecall W_176e8 = true.
Proof. vm_refl. Qed.

Definition W_176ec : bv 32 := 0xff9ff06f.
Lemma F_176ec : fetch_word Plain.M.loaded_segments (0x176ec : word) = Some W_176ec.
Proof. vm_refl. Qed.
Lemma D_176ec : decode_any W_176ec = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

Definition W_176f0 : bv 32 := 0x00000023.
Lemma F_176f0 : fetch_word Plain.M.loaded_segments (0x176f0 : word) = Some W_176f0.
Proof. vm_refl. Qed.
Lemma D_176f0 : decode_any W_176f0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_176f4 : bv 32 := 0x00050413.
Lemma F_176f4 : fetch_word Plain.M.loaded_segments (0x176f4 : word) = Some W_176f4.
Proof. vm_refl. Qed.
Lemma D_176f4 : decode_any W_176f4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_176f8 : bv 32 := 0xdbdff0ef.
Lemma F_176f8 : fetch_word Plain.M.loaded_segments (0x176f8 : word) = Some W_176f8.
Proof. vm_refl. Qed.
Lemma D_176f8 : decode_any W_176f8 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_176fc : bv 32 := 0xf51ff0ef.
Lemma F_176fc : fetch_word Plain.M.loaded_segments (0x176fc : word) = Some W_176fc.
Proof. vm_refl. Qed.
Lemma D_176fc : decode_any W_176fc = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_17700 : bv 32 := 0x160020ef.
Lemma F_17700 : fetch_word Plain.M.loaded_segments (0x17700 : word) = Some W_17700.
Proof. vm_refl. Qed.
Lemma D_17700 : decode_any W_17700 = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

Definition W_17704 : bv 32 := 0x00040513.
Lemma F_17704 : fetch_word Plain.M.loaded_segments (0x17704 : word) = Some W_17704.
Proof. vm_refl. Qed.
Lemma D_17704 : decode_any W_17704 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17708 : bv 32 := 0xd91ff0ef.
Lemma F_17708 : fetch_word Plain.M.loaded_segments (0x17708 : word) = Some W_17708.
Proof. vm_refl. Qed.
Lemma D_17708 : decode_any W_17708 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f0d4 : bv 32 := 0x00033597.
Lemma F_1f0d4 : fetch_word Plain.M.loaded_segments (0x1f0d4 : word) = Some W_1f0d4.
Proof. vm_refl. Qed.
Lemma D_1f0d4 : decode_any W_1f0d4 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f0d8 : bv 32 := 0xaa758683.
Lemma F_1f0d8 : fetch_word Plain.M.loaded_segments (0x1f0d8 : word) = Some W_1f0d8.
Proof. vm_refl. Qed.
Lemma D_1f0d8 : decode_any W_1f0d8 = Some (Load SZ1 true 13 11 2727, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f0dc : bv 32 := 0x1e068863.
Lemma F_1f0dc : fetch_word Plain.M.loaded_segments (0x1f0dc : word) = Some W_1f0dc.
Proof. vm_refl. Qed.
Lemma D_1f0dc : decode_any W_1f0dc = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f2cc : bv 32 := 0x00008067.
Lemma F_1f2cc : fetch_word Plain.M.loaded_segments (0x1f2cc : word) = Some W_1f2cc.
Proof. vm_refl. Qed.
Lemma D_1f2cc : decode_any W_1f2cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f35c : bv 32 := 0x00052583.
Lemma F_1f35c : fetch_word Plain.M.loaded_segments (0x1f35c : word) = Some W_1f35c.
Proof. vm_refl. Qed.
Lemma D_1f35c : decode_any W_1f35c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f360 : bv 32 := 0x0005c463.
Lemma F_1f360 : fetch_word Plain.M.loaded_segments (0x1f360 : word) = Some W_1f360.
Proof. vm_refl. Qed.
Lemma D_1f360 : decode_any W_1f360 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1f364 : bv 32 := 0x00008067.
Lemma F_1f364 : fetch_word Plain.M.loaded_segments (0x1f364 : word) = Some W_1f364.
Proof. vm_refl. Qed.
Lemma D_1f364 : decode_any W_1f364 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
