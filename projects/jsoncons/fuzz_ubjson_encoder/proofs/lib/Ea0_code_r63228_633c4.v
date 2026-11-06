(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5e6c8 : bv 32 := 0xfe010113.
Lemma F_5e6c8 : fetch_word Asan.M.loaded_segments (0x5e718 : word) = Some W_5e6c8.
Proof. vm_refl. Qed.
Lemma D_5e6c8 : decode_any W_5e6c8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6cc : bv 32 := 0x00113c23.
Lemma F_5e6cc : fetch_word Asan.M.loaded_segments (0x5e71c : word) = Some W_5e6cc.
Proof. vm_refl. Qed.
Lemma D_5e6cc : decode_any W_5e6cc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d0 : bv 32 := 0x00813823.
Lemma F_5e6d0 : fetch_word Asan.M.loaded_segments (0x5e720 : word) = Some W_5e6d0.
Proof. vm_refl. Qed.
Lemma D_5e6d0 : decode_any W_5e6d0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d4 : bv 32 := 0x00913423.
Lemma F_5e6d4 : fetch_word Asan.M.loaded_segments (0x5e724 : word) = Some W_5e6d4.
Proof. vm_refl. Qed.
Lemma D_5e6d4 : decode_any W_5e6d4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6d8 : bv 32 := 0x01213023.
Lemma F_5e6d8 : fetch_word Asan.M.loaded_segments (0x5e728 : word) = Some W_5e6d8.
Proof. vm_refl. Qed.
Lemma D_5e6d8 : decode_any W_5e6d8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6dc : bv 32 := 0x02010413.
Lemma F_5e6dc : fetch_word Asan.M.loaded_segments (0x5e72c : word) = Some W_5e6dc.
Proof. vm_refl. Qed.
Lemma D_5e6dc : decode_any W_5e6dc = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e0 : bv 32 := 0x000dc517.
Lemma F_5e6e0 : fetch_word Asan.M.loaded_segments (0x5e730 : word) = Some W_5e6e0.
Proof. vm_refl. Qed.
Lemma D_5e6e0 : decode_any W_5e6e0 = Some (Auipc 10 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e4 : bv 32 := 0x88050513.
Lemma F_5e6e4 : fetch_word Asan.M.loaded_segments (0x5e734 : word) = Some W_5e6e4.
Proof. vm_refl. Qed.
Lemma D_5e6e4 : decode_any W_5e6e4 = Some (OpImm ALU_ADD 10 10 2176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6e8 : bv 32 := 0x63c050ef.
Lemma F_5e6e8 : fetch_word Asan.M.loaded_segments (0x5e738 : word) = Some W_5e6e8.
Proof. vm_refl. Qed.
Lemma D_5e6e8 : decode_any W_5e6e8 = Some (Jal 1 22076, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6ec : bv 32 := 0x00053483.
Lemma F_5e6ec : fetch_word Asan.M.loaded_segments (0x5e73c : word) = Some W_5e6ec.
Proof. vm_refl. Qed.
Lemma D_5e6ec : decode_any W_5e6ec = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f0 : bv 32 := 0x08048863.
Lemma F_5e6f0 : fetch_word Asan.M.loaded_segments (0x5e740 : word) = Some W_5e6f0.
Proof. vm_refl. Qed.
Lemma D_5e6f0 : decode_any W_5e6f0 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f4 : bv 32 := 0x0604c503.
Lemma F_5e6f4 : fetch_word Asan.M.loaded_segments (0x5e744 : word) = Some W_5e6f4.
Proof. vm_refl. Qed.
Lemma D_5e6f4 : decode_any W_5e6f4 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6f8 : bv 32 := 0x0584b903.
Lemma F_5e6f8 : fetch_word Asan.M.loaded_segments (0x5e748 : word) = Some W_5e6f8.
Proof. vm_refl. Qed.
Lemma D_5e6f8 : decode_any W_5e6f8 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e6fc : bv 32 := 0x00050863.
Lemma F_5e6fc : fetch_word Asan.M.loaded_segments (0x5e74c : word) = Some W_5e6fc.
Proof. vm_refl. Qed.
Lemma D_5e6fc : decode_any W_5e6fc = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e700 : bv 32 := 0x00048513.
Lemma F_5e700 : fetch_word Asan.M.loaded_segments (0x5e750 : word) = Some W_5e700.
Proof. vm_refl. Qed.
Lemma D_5e700 : decode_any W_5e700 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e704 : bv 32 := 0x00040593.
Lemma F_5e704 : fetch_word Asan.M.loaded_segments (0x5e754 : word) = Some W_5e704.
Proof. vm_refl. Qed.
Lemma D_5e704 : decode_any W_5e704 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e708 : bv 32 := 0x871ff0ef.
Lemma F_5e708 : fetch_word Asan.M.loaded_segments (0x5e758 : word) = Some W_5e708.
Proof. vm_refl. Qed.
Lemma D_5e708 : decode_any W_5e708 = Some (Jal 1 2095216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e70c : bv 32 := 0xff890593.
Lemma F_5e70c : fetch_word Asan.M.loaded_segments (0x5e75c : word) = Some W_5e70c.
Proof. vm_refl. Qed.
Lemma D_5e70c : decode_any W_5e70c = Some (OpImm ALU_ADD 11 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e710 : bv 32 := 0x00100513.
Lemma F_5e710 : fetch_word Asan.M.loaded_segments (0x5e760 : word) = Some W_5e710.
Proof. vm_refl. Qed.
Lemma D_5e710 : decode_any W_5e710 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e714 : bv 32 := 0x00b51533.
Lemma F_5e714 : fetch_word Asan.M.loaded_segments (0x5e764 : word) = Some W_5e714.
Proof. vm_refl. Qed.
Lemma D_5e714 : decode_any W_5e714 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e718 : bv 32 := 0x0005061b.
Lemma F_5e718 : fetch_word Asan.M.loaded_segments (0x5e768 : word) = Some W_5e718.
Proof. vm_refl. Qed.
Lemma D_5e718 : decode_any W_5e718 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e71c : bv 32 := 0x08c05263.
Lemma F_5e71c : fetch_word Asan.M.loaded_segments (0x5e76c : word) = Some W_5e71c.
Proof. vm_refl. Qed.
Lemma D_5e71c : decode_any W_5e71c = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e720 : bv 32 := 0x000016b7.
Lemma F_5e720 : fetch_word Asan.M.loaded_segments (0x5e770 : word) = Some W_5e720.
Proof. vm_refl. Qed.
Lemma D_5e720 : decode_any W_5e720 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e724 : bv 32 := 0xff190613.
Lemma F_5e724 : fetch_word Asan.M.loaded_segments (0x5e774 : word) = Some W_5e724.
Proof. vm_refl. Qed.
Lemma D_5e724 : decode_any W_5e724 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e728 : bv 32 := 0x30000713.
Lemma F_5e728 : fetch_word Asan.M.loaded_segments (0x5e778 : word) = Some W_5e728.
Proof. vm_refl. Qed.
Lemma D_5e728 : decode_any W_5e728 = Some (OpImm ALU_ADD 14 0 768, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e72c : bv 32 := 0xfff00793.
Lemma F_5e72c : fetch_word Asan.M.loaded_segments (0x5e77c : word) = Some W_5e72c.
Proof. vm_refl. Qed.
Lemma D_5e72c : decode_any W_5e72c = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e730 : bv 32 := 0x00c71733.
Lemma F_5e730 : fetch_word Asan.M.loaded_segments (0x5e780 : word) = Some W_5e730.
Proof. vm_refl. Qed.
Lemma D_5e730 : decode_any W_5e730 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e734 : bv 32 := 0x0104b603.
Lemma F_5e734 : fetch_word Asan.M.loaded_segments (0x5e784 : word) = Some W_5e734.
Proof. vm_refl. Qed.
Lemma D_5e734 : decode_any W_5e734 = Some (Load SZ8 true 12 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e738 : bv 32 := 0x00b797b3.
Lemma F_5e738 : fetch_word Asan.M.loaded_segments (0x5e788 : word) = Some W_5e738.
Proof. vm_refl. Qed.
Lemma D_5e738 : decode_any W_5e738 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e73c : bv 32 := 0xfff50813.
Lemma F_5e73c : fetch_word Asan.M.loaded_segments (0x5e78c : word) = Some W_5e73c.
Proof. vm_refl. Qed.
Lemma D_5e73c : decode_any W_5e73c = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e740 : bv 32 := 0x00d485b3.
Lemma F_5e740 : fetch_word Asan.M.loaded_segments (0x5e790 : word) = Some W_5e740.
Proof. vm_refl. Qed.
Lemma D_5e740 : decode_any W_5e740 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e744 : bv 32 := 0x00e586b3.
Lemma F_5e744 : fetch_word Asan.M.loaded_segments (0x5e794 : word) = Some W_5e744.
Proof. vm_refl. Qed.
Lemma D_5e744 : decode_any W_5e744 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e748 : bv 32 := 0xfff7c713.
Lemma F_5e748 : fetch_word Asan.M.loaded_segments (0x5e798 : word) = Some W_5e748.
Proof. vm_refl. Qed.
Lemma D_5e748 : decode_any W_5e748 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e74c : bv 32 := 0x02081813.
Lemma F_5e74c : fetch_word Asan.M.loaded_segments (0x5e79c : word) = Some W_5e74c.
Proof. vm_refl. Qed.
Lemma D_5e74c : decode_any W_5e74c = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e750 : bv 32 := 0x02085793.
Lemma F_5e750 : fetch_word Asan.M.loaded_segments (0x5e7a0 : word) = Some W_5e750.
Proof. vm_refl. Qed.
Lemma D_5e750 : decode_any W_5e750 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e754 : bv 32 := 0x00f607b3.
Lemma F_5e754 : fetch_word Asan.M.loaded_segments (0x5e7a4 : word) = Some W_5e754.
Proof. vm_refl. Qed.
Lemma D_5e754 : decode_any W_5e754 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e758 : bv 32 := 0x00178813.
Lemma F_5e758 : fetch_word Asan.M.loaded_segments (0x5e7a8 : word) = Some W_5e758.
Proof. vm_refl. Qed.
Lemma D_5e758 : decode_any W_5e758 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e75c : bv 32 := 0x00e678b3.
Lemma F_5e75c : fetch_word Asan.M.loaded_segments (0x5e7ac : word) = Some W_5e75c.
Proof. vm_refl. Qed.
Lemma D_5e75c : decode_any W_5e75c = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e760 : bv 32 := 0x011687b3.
Lemma F_5e760 : fetch_word Asan.M.loaded_segments (0x5e7b0 : word) = Some W_5e760.
Proof. vm_refl. Qed.
Lemma D_5e760 : decode_any W_5e760 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e764 : bv 32 := 0x0007c283.
Lemma F_5e764 : fetch_word Asan.M.loaded_segments (0x5e7b4 : word) = Some W_5e764.
Proof. vm_refl. Qed.
Lemma D_5e764 : decode_any W_5e764 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e768 : bv 32 := 0x06028663.
Lemma F_5e768 : fetch_word Asan.M.loaded_segments (0x5e7b8 : word) = Some W_5e768.
Proof. vm_refl. Qed.
Lemma D_5e768 : decode_any W_5e768 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e76c : bv 32 := 0xfff5051b.
Lemma F_5e76c : fetch_word Asan.M.loaded_segments (0x5e7bc : word) = Some W_5e76c.
Proof. vm_refl. Qed.
Lemma D_5e76c : decode_any W_5e76c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e770 : bv 32 := 0x00160613.
Lemma F_5e770 : fetch_word Asan.M.loaded_segments (0x5e7c0 : word) = Some W_5e770.
Proof. vm_refl. Qed.
Lemma D_5e770 : decode_any W_5e770 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e774 : bv 32 := 0xfe0514e3.
Lemma F_5e774 : fetch_word Asan.M.loaded_segments (0x5e7c4 : word) = Some W_5e774.
Proof. vm_refl. Qed.
Lemma D_5e774 : decode_any W_5e774 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e778 : bv 32 := 0x0104b823.
Lemma F_5e778 : fetch_word Asan.M.loaded_segments (0x5e7c8 : word) = Some W_5e778.
Proof. vm_refl. Qed.
Lemma D_5e778 : decode_any W_5e778 = Some (Store SZ8 9 16 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e77c : bv 32 := 0x0400006f.
Lemma F_5e77c : fetch_word Asan.M.loaded_segments (0x5e7cc : word) = Some W_5e77c.
Proof. vm_refl. Qed.
Lemma D_5e77c : decode_any W_5e77c = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e780 : bv 32 := 0x000db517.
Lemma F_5e780 : fetch_word Asan.M.loaded_segments (0x5e7d0 : word) = Some W_5e780.
Proof. vm_refl. Qed.
Lemma D_5e780 : decode_any W_5e780 = Some (Auipc 10 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e784 : bv 32 := 0xa4053503.
Lemma F_5e784 : fetch_word Asan.M.loaded_segments (0x5e7d4 : word) = Some W_5e784.
Proof. vm_refl. Qed.
Lemma D_5e784 : decode_any W_5e784 = Some (Load SZ8 true 10 10 2624, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e788 : bv 32 := 0x00052503.
Lemma F_5e788 : fetch_word Asan.M.loaded_segments (0x5e7d8 : word) = Some W_5e788.
Proof. vm_refl. Qed.
Lemma D_5e788 : decode_any W_5e788 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e78c : bv 32 := 0x02050863.
Lemma F_5e78c : fetch_word Asan.M.loaded_segments (0x5e7dc : word) = Some W_5e78c.
Proof. vm_refl. Qed.
Lemma D_5e78c : decode_any W_5e78c = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e790 : bv 32 := 0x289250ef.
Lemma F_5e790 : fetch_word Asan.M.loaded_segments (0x5e7e0 : word) = Some W_5e790.
Proof. vm_refl. Qed.
Lemma D_5e790 : decode_any W_5e790 = Some (Jal 1 154248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e794 : bv 32 := 0x02050463.
Lemma F_5e794 : fetch_word Asan.M.loaded_segments (0x5e7e4 : word) = Some W_5e794.
Proof. vm_refl. Qed.
Lemma D_5e794 : decode_any W_5e794 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e798 : bv 32 := 0x02850583.
Lemma F_5e798 : fetch_word Asan.M.loaded_segments (0x5e7e8 : word) = Some W_5e798.
Proof. vm_refl. Qed.
Lemma D_5e798 : decode_any W_5e798 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e79c : bv 32 := 0x0a058663.
Lemma F_5e79c : fetch_word Asan.M.loaded_segments (0x5e7ec : word) = Some W_5e79c.
Proof. vm_refl. Qed.
Lemma D_5e79c : decode_any W_5e79c = Some (Branch BC_EQ 11 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a0 : bv 32 := 0x00000513.
Lemma F_5e7a0 : fetch_word Asan.M.loaded_segments (0x5e7f0 : word) = Some W_5e7a0.
Proof. vm_refl. Qed.
Lemma D_5e7a0 : decode_any W_5e7a0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a4 : bv 32 := 0x01813083.
Lemma F_5e7a4 : fetch_word Asan.M.loaded_segments (0x5e7f4 : word) = Some W_5e7a4.
Proof. vm_refl. Qed.
Lemma D_5e7a4 : decode_any W_5e7a4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a8 : bv 32 := 0x01013403.
Lemma F_5e7a8 : fetch_word Asan.M.loaded_segments (0x5e7f8 : word) = Some W_5e7a8.
Proof. vm_refl. Qed.
Lemma D_5e7a8 : decode_any W_5e7a8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7ac : bv 32 := 0x00813483.
Lemma F_5e7ac : fetch_word Asan.M.loaded_segments (0x5e7fc : word) = Some W_5e7ac.
Proof. vm_refl. Qed.
Lemma D_5e7ac : decode_any W_5e7ac = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b0 : bv 32 := 0x00013903.
Lemma F_5e7b0 : fetch_word Asan.M.loaded_segments (0x5e800 : word) = Some W_5e7b0.
Proof. vm_refl. Qed.
Lemma D_5e7b0 : decode_any W_5e7b0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b4 : bv 32 := 0x02010113.
Lemma F_5e7b4 : fetch_word Asan.M.loaded_segments (0x5e804 : word) = Some W_5e7b4.
Proof. vm_refl. Qed.
Lemma D_5e7b4 : decode_any W_5e7b4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b8 : bv 32 := 0x00008067.
Lemma F_5e7b8 : fetch_word Asan.M.loaded_segments (0x5e808 : word) = Some W_5e7b8.
Proof. vm_refl. Qed.
Lemma D_5e7b8 : decode_any W_5e7b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7bc : bv 32 := 0x01813083.
Lemma F_5e7bc : fetch_word Asan.M.loaded_segments (0x5e80c : word) = Some W_5e7bc.
Proof. vm_refl. Qed.
Lemma D_5e7bc : decode_any W_5e7bc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c0 : bv 32 := 0x01013403.
Lemma F_5e7c0 : fetch_word Asan.M.loaded_segments (0x5e810 : word) = Some W_5e7c0.
Proof. vm_refl. Qed.
Lemma D_5e7c0 : decode_any W_5e7c0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c4 : bv 32 := 0x00813483.
Lemma F_5e7c4 : fetch_word Asan.M.loaded_segments (0x5e814 : word) = Some W_5e7c4.
Proof. vm_refl. Qed.
Lemma D_5e7c4 : decode_any W_5e7c4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c8 : bv 32 := 0x00013903.
Lemma F_5e7c8 : fetch_word Asan.M.loaded_segments (0x5e818 : word) = Some W_5e7c8.
Proof. vm_refl. Qed.
Lemma D_5e7c8 : decode_any W_5e7c8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7cc : bv 32 := 0x02010113.
Lemma F_5e7cc : fetch_word Asan.M.loaded_segments (0x5e81c : word) = Some W_5e7cc.
Proof. vm_refl. Qed.
Lemma D_5e7cc : decode_any W_5e7cc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d0 : bv 32 := 0x00008067.
Lemma F_5e7d0 : fetch_word Asan.M.loaded_segments (0x5e820 : word) = Some W_5e7d0.
Proof. vm_refl. Qed.
Lemma D_5e7d0 : decode_any W_5e7d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d4 : bv 32 := 0x00160613.
Lemma F_5e7d4 : fetch_word Asan.M.loaded_segments (0x5e824 : word) = Some W_5e7d4.
Proof. vm_refl. Qed.
Lemma D_5e7d4 : decode_any W_5e7d4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d8 : bv 32 := 0x00100513.
Lemma F_5e7d8 : fetch_word Asan.M.loaded_segments (0x5e828 : word) = Some W_5e7d8.
Proof. vm_refl. Qed.
Lemma D_5e7d8 : decode_any W_5e7d8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7dc : bv 32 := 0xffb90693.
Lemma F_5e7dc : fetch_word Asan.M.loaded_segments (0x5e82c : word) = Some W_5e7dc.
Proof. vm_refl. Qed.
Lemma D_5e7dc : decode_any W_5e7dc = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e0 : bv 32 := 0x00c4b823.
Lemma F_5e7e0 : fetch_word Asan.M.loaded_segments (0x5e830 : word) = Some W_5e7e0.
Proof. vm_refl. Qed.
Lemma D_5e7e0 : decode_any W_5e7e0 = Some (Store SZ8 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e4 : bv 32 := 0x00a78023.
Lemma F_5e7e4 : fetch_word Asan.M.loaded_segments (0x5e834 : word) = Some W_5e7e4.
Proof. vm_refl. Qed.
Lemma D_5e7e4 : decode_any W_5e7e4 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e8 : bv 32 := 0x00d51533.
Lemma F_5e7e8 : fetch_word Asan.M.loaded_segments (0x5e838 : word) = Some W_5e7e8.
Proof. vm_refl. Qed.
Lemma D_5e7e8 : decode_any W_5e7e8 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7ec : bv 32 := 0x00200613.
Lemma F_5e7ec : fetch_word Asan.M.loaded_segments (0x5e83c : word) = Some W_5e7ec.
Proof. vm_refl. Qed.
Lemma D_5e7ec : decode_any W_5e7ec = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f0 : bv 32 := 0x00889893.
Lemma F_5e7f0 : fetch_word Asan.M.loaded_segments (0x5e840 : word) = Some W_5e7f0.
Proof. vm_refl. Qed.
Lemma D_5e7f0 : decode_any W_5e7f0 = Some (ShiftImm ALU_SLL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f4 : bv 32 := 0x01261633.
Lemma F_5e7f4 : fetch_word Asan.M.loaded_segments (0x5e844 : word) = Some W_5e7f4.
Proof. vm_refl. Qed.
Lemma D_5e7f4 : decode_any W_5e7f4 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f8 : bv 32 := 0x00a58533.
Lemma F_5e7f8 : fetch_word Asan.M.loaded_segments (0x5e848 : word) = Some W_5e7f8.
Proof. vm_refl. Qed.
Lemma D_5e7f8 : decode_any W_5e7f8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7fc : bv 32 := 0x01160633.
Lemma F_5e7fc : fetch_word Asan.M.loaded_segments (0x5e84c : word) = Some W_5e7fc.
Proof. vm_refl. Qed.
Lemma D_5e7fc : decode_any W_5e7fc = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e800 : bv 32 := 0x00c504b3.
Lemma F_5e800 : fetch_word Asan.M.loaded_segments (0x5e850 : word) = Some W_5e800.
Proof. vm_refl. Qed.
Lemma D_5e800 : decode_any W_5e800 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e804 : bv 32 := 0x0084bc23.
Lemma F_5e804 : fetch_word Asan.M.loaded_segments (0x5e854 : word) = Some W_5e804.
Proof. vm_refl. Qed.
Lemma D_5e804 : decode_any W_5e804 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e808 : bv 32 := 0x0ef4bc23.
Lemma F_5e808 : fetch_word Asan.M.loaded_segments (0x5e858 : word) = Some W_5e808.
Proof. vm_refl. Qed.
Lemma D_5e808 : decode_any W_5e808 = Some (Store SZ8 9 15 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e80c : bv 32 := 0x00048513.
Lemma F_5e80c : fetch_word Asan.M.loaded_segments (0x5e85c : word) = Some W_5e80c.
Proof. vm_refl. Qed.
Lemma D_5e80c : decode_any W_5e80c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e810 : bv 32 := 0x4c0000ef.
Lemma F_5e810 : fetch_word Asan.M.loaded_segments (0x5e860 : word) = Some W_5e810.
Proof. vm_refl. Qed.
Lemma D_5e810 : decode_any W_5e810 = Some (Jal 1 1216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e814 : bv 32 := 0x00050593.
Lemma F_5e814 : fetch_word Asan.M.loaded_segments (0x5e864 : word) = Some W_5e814.
Proof. vm_refl. Qed.
Lemma D_5e814 : decode_any W_5e814 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e818 : bv 32 := 0x00048513.
Lemma F_5e818 : fetch_word Asan.M.loaded_segments (0x5e868 : word) = Some W_5e818.
Proof. vm_refl. Qed.
Lemma D_5e818 : decode_any W_5e818 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e81c : bv 32 := 0x00000613.
Lemma F_5e81c : fetch_word Asan.M.loaded_segments (0x5e86c : word) = Some W_5e81c.
Proof. vm_refl. Qed.
Lemma D_5e81c : decode_any W_5e81c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e820 : bv 32 := 0x0005b023.
Lemma F_5e820 : fetch_word Asan.M.loaded_segments (0x5e870 : word) = Some W_5e820.
Proof. vm_refl. Qed.
Lemma D_5e820 : decode_any W_5e820 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e824 : bv 32 := 0x0005b423.
Lemma F_5e824 : fetch_word Asan.M.loaded_segments (0x5e874 : word) = Some W_5e824.
Proof. vm_refl. Qed.
Lemma D_5e824 : decode_any W_5e824 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e828 : bv 32 := 0x0005b823.
Lemma F_5e828 : fetch_word Asan.M.loaded_segments (0x5e878 : word) = Some W_5e828.
Proof. vm_refl. Qed.
Lemma D_5e828 : decode_any W_5e828 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e82c : bv 32 := 0x0005bc23.
Lemma F_5e82c : fetch_word Asan.M.loaded_segments (0x5e87c : word) = Some W_5e82c.
Proof. vm_refl. Qed.
Lemma D_5e82c : decode_any W_5e82c = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e830 : bv 32 := 0x01813083.
Lemma F_5e830 : fetch_word Asan.M.loaded_segments (0x5e880 : word) = Some W_5e830.
Proof. vm_refl. Qed.
Lemma D_5e830 : decode_any W_5e830 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e834 : bv 32 := 0x01013403.
Lemma F_5e834 : fetch_word Asan.M.loaded_segments (0x5e884 : word) = Some W_5e834.
Proof. vm_refl. Qed.
Lemma D_5e834 : decode_any W_5e834 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e838 : bv 32 := 0x00813483.
Lemma F_5e838 : fetch_word Asan.M.loaded_segments (0x5e888 : word) = Some W_5e838.
Proof. vm_refl. Qed.
Lemma D_5e838 : decode_any W_5e838 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e83c : bv 32 := 0x00013903.
Lemma F_5e83c : fetch_word Asan.M.loaded_segments (0x5e88c : word) = Some W_5e83c.
Proof. vm_refl. Qed.
Lemma D_5e83c : decode_any W_5e83c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e840 : bv 32 := 0x02010113.
Lemma F_5e840 : fetch_word Asan.M.loaded_segments (0x5e890 : word) = Some W_5e840.
Proof. vm_refl. Qed.
Lemma D_5e840 : decode_any W_5e840 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e844 : bv 32 := 0x00008067.
Lemma F_5e844 : fetch_word Asan.M.loaded_segments (0x5e894 : word) = Some W_5e844.
Proof. vm_refl. Qed.
Lemma D_5e844 : decode_any W_5e844 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e848 : bv 32 := 0x04853483.
Lemma F_5e848 : fetch_word Asan.M.loaded_segments (0x5e898 : word) = Some W_5e848.
Proof. vm_refl. Qed.
Lemma D_5e848 : decode_any W_5e848 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e84c : bv 32 := 0x00100593.
Lemma F_5e84c : fetch_word Asan.M.loaded_segments (0x5e89c : word) = Some W_5e84c.
Proof. vm_refl. Qed.
Lemma D_5e84c : decode_any W_5e84c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e850 : bv 32 := 0x0095e663.
Lemma F_5e850 : fetch_word Asan.M.loaded_segments (0x5e8a0 : word) = Some W_5e850.
Proof. vm_refl. Qed.
Lemma D_5e850 : decode_any W_5e850 = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e854 : bv 32 := 0x439250ef.
Lemma F_5e854 : fetch_word Asan.M.loaded_segments (0x5e8a4 : word) = Some W_5e854.
Proof. vm_refl. Qed.
Lemma D_5e854 : decode_any W_5e854 = Some (Jal 1 154680, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e858 : bv 32 := 0x00050493.
Lemma F_5e858 : fetch_word Asan.M.loaded_segments (0x5e8a8 : word) = Some W_5e858.
Proof. vm_refl. Qed.
Lemma D_5e858 : decode_any W_5e858 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e85c : bv 32 := 0xe8049ce3.
Lemma F_5e85c : fetch_word Asan.M.loaded_segments (0x5e8ac : word) = Some W_5e85c.
Proof. vm_refl. Qed.
Lemma D_5e85c : decode_any W_5e85c = Some (Branch BC_NE 9 0 7832, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e860 : bv 32 := 0xf41ff06f.
Lemma F_5e860 : fetch_word Asan.M.loaded_segments (0x5e8b0 : word) = Some W_5e860.
Proof. vm_refl. Qed.
Lemma D_5e860 : decode_any W_5e860 = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.
