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

Definition W_7e6fc : bv 32 := 0xf9010113.
Lemma F_7e6fc : fetch_word Ubsan.M.loaded_segments (0x7e6fc : word) = Some W_7e6fc.
Proof. vm_refl. Qed.
Lemma D_7e6fc : decode_any W_7e6fc = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e700 : bv 32 := 0x06113423.
Lemma F_7e700 : fetch_word Ubsan.M.loaded_segments (0x7e700 : word) = Some W_7e700.
Proof. vm_refl. Qed.
Lemma D_7e700 : decode_any W_7e700 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e704 : bv 32 := 0x06813023.
Lemma F_7e704 : fetch_word Ubsan.M.loaded_segments (0x7e704 : word) = Some W_7e704.
Proof. vm_refl. Qed.
Lemma D_7e704 : decode_any W_7e704 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e708 : bv 32 := 0x04913c23.
Lemma F_7e708 : fetch_word Ubsan.M.loaded_segments (0x7e708 : word) = Some W_7e708.
Proof. vm_refl. Qed.
Lemma D_7e708 : decode_any W_7e708 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e70c : bv 32 := 0x05213823.
Lemma F_7e70c : fetch_word Ubsan.M.loaded_segments (0x7e70c : word) = Some W_7e70c.
Proof. vm_refl. Qed.
Lemma D_7e70c : decode_any W_7e70c = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e710 : bv 32 := 0x05313423.
Lemma F_7e710 : fetch_word Ubsan.M.loaded_segments (0x7e710 : word) = Some W_7e710.
Proof. vm_refl. Qed.
Lemma D_7e710 : decode_any W_7e710 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e714 : bv 32 := 0x05413023.
Lemma F_7e714 : fetch_word Ubsan.M.loaded_segments (0x7e714 : word) = Some W_7e714.
Proof. vm_refl. Qed.
Lemma D_7e714 : decode_any W_7e714 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e718 : bv 32 := 0x03513c23.
Lemma F_7e718 : fetch_word Ubsan.M.loaded_segments (0x7e718 : word) = Some W_7e718.
Proof. vm_refl. Qed.
Lemma D_7e718 : decode_any W_7e718 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e71c : bv 32 := 0x03613823.
Lemma F_7e71c : fetch_word Ubsan.M.loaded_segments (0x7e71c : word) = Some W_7e71c.
Proof. vm_refl. Qed.
Lemma D_7e71c : decode_any W_7e71c = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e720 : bv 32 := 0x03713423.
Lemma F_7e720 : fetch_word Ubsan.M.loaded_segments (0x7e720 : word) = Some W_7e720.
Proof. vm_refl. Qed.
Lemma D_7e720 : decode_any W_7e720 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e724 : bv 32 := 0x03813023.
Lemma F_7e724 : fetch_word Ubsan.M.loaded_segments (0x7e724 : word) = Some W_7e724.
Proof. vm_refl. Qed.
Lemma D_7e724 : decode_any W_7e724 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e728 : bv 32 := 0x01913c23.
Lemma F_7e728 : fetch_word Ubsan.M.loaded_segments (0x7e728 : word) = Some W_7e728.
Proof. vm_refl. Qed.
Lemma D_7e728 : decode_any W_7e728 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e72c : bv 32 := 0x01a13823.
Lemma F_7e72c : fetch_word Ubsan.M.loaded_segments (0x7e72c : word) = Some W_7e72c.
Proof. vm_refl. Qed.
Lemma D_7e72c : decode_any W_7e72c = Some (Store SZ8 2 26 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e730 : bv 32 := 0x3a058463.
Lemma F_7e730 : fetch_word Ubsan.M.loaded_segments (0x7e730 : word) = Some W_7e730.
Proof. vm_refl. Qed.
Lemma D_7e730 : decode_any W_7e730 = Some (Branch BC_EQ 11 0 936, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e734 : bv 32 := 0x00058493.
Lemma F_7e734 : fetch_word Ubsan.M.loaded_segments (0x7e734 : word) = Some W_7e734.
Proof. vm_refl. Qed.
Lemma D_7e734 : decode_any W_7e734 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e738 : bv 32 := 0x00050a13.
Lemma F_7e738 : fetch_word Ubsan.M.loaded_segments (0x7e738 : word) = Some W_7e738.
Proof. vm_refl. Qed.
Lemma D_7e738 : decode_any W_7e738 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e73c : bv 32 := 0x0035f513.
Lemma F_7e73c : fetch_word Ubsan.M.loaded_segments (0x7e73c : word) = Some W_7e73c.
Proof. vm_refl. Qed.
Lemma D_7e73c : decode_any W_7e73c = Some (OpImm ALU_AND 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e740 : bv 32 := 0x44051463.
Lemma F_7e740 : fetch_word Ubsan.M.loaded_segments (0x7e740 : word) = Some W_7e740.
Proof. vm_refl. Qed.
Lemma D_7e740 : decode_any W_7e740 = Some (Branch BC_NE 10 0 1096, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e744 : bv 32 := 0x0004a023.
Lemma F_7e744 : fetch_word Ubsan.M.loaded_segments (0x7e744 : word) = Some W_7e744.
Proof. vm_refl. Qed.
Lemma D_7e744 : decode_any W_7e744 = Some (Store SZ4 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e748 : bv 32 := 0x360a0463.
Lemma F_7e748 : fetch_word Ubsan.M.loaded_segments (0x7e748 : word) = Some W_7e748.
Proof. vm_refl. Qed.
Lemma D_7e748 : decode_any W_7e748 = Some (Branch BC_EQ 20 0 872, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e74c : bv 32 := 0x00060413.
Lemma F_7e74c : fetch_word Ubsan.M.loaded_segments (0x7e74c : word) = Some W_7e74c.
Proof. vm_refl. Qed.
Lemma D_7e74c : decode_any W_7e74c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e750 : bv 32 := 0x000a0513.
Lemma F_7e750 : fetch_word Ubsan.M.loaded_segments (0x7e750 : word) = Some W_7e750.
Proof. vm_refl. Qed.
Lemma D_7e750 : decode_any W_7e750 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e754 : bv 32 := 0x9c1f00ef.
Lemma F_7e754 : fetch_word Ubsan.M.loaded_segments (0x7e754 : word) = Some W_7e754.
Proof. vm_refl. Qed.
Lemma D_7e754 : decode_any W_7e754 = Some (Jal 1 2034112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e758 : bv 32 := 0x00100593.
Lemma F_7e758 : fetch_word Ubsan.M.loaded_segments (0x7e758 : word) = Some W_7e758.
Proof. vm_refl. Qed.
Lemma D_7e758 : decode_any W_7e758 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e75c : bv 32 := 0x34b51a63.
Lemma F_7e75c : fetch_word Ubsan.M.loaded_segments (0x7e75c : word) = Some W_7e75c.
Proof. vm_refl. Qed.
Lemma D_7e75c : decode_any W_7e75c = Some (Branch BC_NE 10 11 852, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e760 : bv 32 := 0x00040913.
Lemma F_7e760 : fetch_word Ubsan.M.loaded_segments (0x7e760 : word) = Some W_7e760.
Proof. vm_refl. Qed.
Lemma D_7e760 : decode_any W_7e760 = Some (OpImm ALU_ADD 18 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e764 : bv 32 := 0x0a041a63.
Lemma F_7e764 : fetch_word Ubsan.M.loaded_segments (0x7e764 : word) = Some W_7e764.
Proof. vm_refl. Qed.
Lemma D_7e764 : decode_any W_7e764 = Some (Branch BC_NE 8 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e768 : bv 32 := 0x10000513.
Lemma F_7e768 : fetch_word Ubsan.M.loaded_segments (0x7e768 : word) = Some W_7e768.
Proof. vm_refl. Qed.
Lemma D_7e768 : decode_any W_7e768 = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e76c : bv 32 := 0x00400593.
Lemma F_7e76c : fetch_word Ubsan.M.loaded_segments (0x7e76c : word) = Some W_7e76c.
Proof. vm_refl. Qed.
Lemma D_7e76c : decode_any W_7e76c = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e770 : bv 32 := 0x10000993.
Lemma F_7e770 : fetch_word Ubsan.M.loaded_segments (0x7e770 : word) = Some W_7e770.
Proof. vm_refl. Qed.
Lemma D_7e770 : decode_any W_7e770 = Some (OpImm ALU_ADD 19 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e774 : bv 32 := 0x76d8f0ef.
Lemma F_7e774 : fetch_word Ubsan.M.loaded_segments (0x7e774 : word) = Some W_7e774.
Proof. vm_refl. Qed.
Lemma D_7e774 : decode_any W_7e774 = Some (Jal 1 589676, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e778 : bv 32 := 0x00050913.
Lemma F_7e778 : fetch_word Ubsan.M.loaded_segments (0x7e778 : word) = Some W_7e778.
Proof. vm_refl. Qed.
Lemma D_7e778 : decode_any W_7e778 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e77c : bv 32 := 0x00000513.
Lemma F_7e77c : fetch_word Ubsan.M.loaded_segments (0x7e77c : word) = Some W_7e77c.
Proof. vm_refl. Qed.
Lemma D_7e77c : decode_any W_7e77c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e780 : bv 32 := 0x012035b3.
Lemma F_7e780 : fetch_word Ubsan.M.loaded_segments (0x7e780 : word) = Some W_7e780.
Proof. vm_refl. Qed.
Lemma D_7e780 : decode_any W_7e780 = Some (Op ALU_SLTU 11 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e784 : bv 32 := 0x00397613.
Lemma F_7e784 : fetch_word Ubsan.M.loaded_segments (0x7e784 : word) = Some W_7e784.
Proof. vm_refl. Qed.
Lemma D_7e784 : decode_any W_7e784 = Some (OpImm ALU_AND 12 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e788 : bv 32 := 0x00163613.
Lemma F_7e788 : fetch_word Ubsan.M.loaded_segments (0x7e788 : word) = Some W_7e788.
Proof. vm_refl. Qed.
Lemma D_7e788 : decode_any W_7e788 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e78c : bv 32 := 0x00b67633.
Lemma F_7e78c : fetch_word Ubsan.M.loaded_segments (0x7e78c : word) = Some W_7e78c.
Proof. vm_refl. Qed.
Lemma D_7e78c : decode_any W_7e78c = Some (Op ALU_AND 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e790 : bv 32 := 0x00090693.
Lemma F_7e790 : fetch_word Ubsan.M.loaded_segments (0x7e790 : word) = Some W_7e790.
Proof. vm_refl. Qed.
Lemma D_7e790 : decode_any W_7e790 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e794 : bv 32 := 0x00090713.
Lemma F_7e794 : fetch_word Ubsan.M.loaded_segments (0x7e794 : word) = Some W_7e794.
Proof. vm_refl. Qed.
Lemma D_7e794 : decode_any W_7e794 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e798 : bv 32 := 0x3f276863.
Lemma F_7e798 : fetch_word Ubsan.M.loaded_segments (0x7e798 : word) = Some W_7e798.
Proof. vm_refl. Qed.
Lemma D_7e798 : decode_any W_7e798 = Some (Branch BC_LTU 14 18 1008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e79c : bv 32 := 0x00173793.
Lemma F_7e79c : fetch_word Ubsan.M.loaded_segments (0x7e79c : word) = Some W_7e79c.
Proof. vm_refl. Qed.
Lemma D_7e79c : decode_any W_7e79c = Some (OpImm ALU_SLTU 15 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7a0 : bv 32 := 0x00f5c7b3.
Lemma F_7e7a0 : fetch_word Ubsan.M.loaded_segments (0x7e7a0 : word) = Some W_7e7a0.
Proof. vm_refl. Qed.
Lemma D_7e7a0 : decode_any W_7e7a0 = Some (Op ALU_XOR 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7a4 : bv 32 := 0x3e078263.
Lemma F_7e7a4 : fetch_word Ubsan.M.loaded_segments (0x7e7a4 : word) = Some W_7e7a4.
Proof. vm_refl. Qed.
Lemma D_7e7a4 : decode_any W_7e7a4 = Some (Branch BC_EQ 15 0 996, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7a8 : bv 32 := 0x3e060063.
Lemma F_7e7a8 : fetch_word Ubsan.M.loaded_segments (0x7e7a8 : word) = Some W_7e7a8.
Proof. vm_refl. Qed.
Lemma D_7e7a8 : decode_any W_7e7a8 = Some (Branch BC_EQ 12 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7ac : bv 32 := 0x00157793.
Lemma F_7e7ac : fetch_word Ubsan.M.loaded_segments (0x7e7ac : word) = Some W_7e7ac.
Proof. vm_refl. Qed.
Lemma D_7e7ac : decode_any W_7e7ac = Some (OpImm ALU_AND 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7b0 : bv 32 := 0x03e51813.
Lemma F_7e7b0 : fetch_word Ubsan.M.loaded_segments (0x7e7b0 : word) = Some W_7e7b0.
Proof. vm_refl. Qed.
Lemma D_7e7b0 : decode_any W_7e7b0 = Some (ShiftImm ALU_SLL 16 10 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7b4 : bv 32 := 0x03d51893.
Lemma F_7e7b4 : fetch_word Ubsan.M.loaded_segments (0x7e7b4 : word) = Some W_7e7b4.
Proof. vm_refl. Qed.
Lemma D_7e7b4 : decode_any W_7e7b4 = Some (ShiftImm ALU_SLL 17 10 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7b8 : bv 32 := 0x03c51293.
Lemma F_7e7b8 : fetch_word Ubsan.M.loaded_segments (0x7e7b8 : word) = Some W_7e7b8.
Proof. vm_refl. Qed.
Lemma D_7e7b8 : decode_any W_7e7b8 = Some (ShiftImm ALU_SLL 5 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7bc : bv 32 := 0x03b51313.
Lemma F_7e7bc : fetch_word Ubsan.M.loaded_segments (0x7e7bc : word) = Some W_7e7bc.
Proof. vm_refl. Qed.
Lemma D_7e7bc : decode_any W_7e7bc = Some (ShiftImm ALU_SLL 6 10 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7c0 : bv 32 := 0x03a51393.
Lemma F_7e7c0 : fetch_word Ubsan.M.loaded_segments (0x7e7c0 : word) = Some W_7e7c0.
Proof. vm_refl. Qed.
Lemma D_7e7c0 : decode_any W_7e7c0 = Some (ShiftImm ALU_SLL 7 10 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7c4 : bv 32 := 0x03951e13.
Lemma F_7e7c4 : fetch_word Ubsan.M.loaded_segments (0x7e7c4 : word) = Some W_7e7c4.
Proof. vm_refl. Qed.
Lemma D_7e7c4 : decode_any W_7e7c4 = Some (ShiftImm ALU_SLL 28 10 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7c8 : bv 32 := 0x00755e9b.
Lemma F_7e7c8 : fetch_word Ubsan.M.loaded_segments (0x7e7c8 : word) = Some W_7e7c8.
Proof. vm_refl. Qed.
Lemma D_7e7c8 : decode_any W_7e7c8 = Some (ShiftImm32 ALU_SRL 29 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7cc : bv 32 := 0xfff98993.
Lemma F_7e7cc : fetch_word Ubsan.M.loaded_segments (0x7e7cc : word) = Some W_7e7cc.
Proof. vm_refl. Qed.
Lemma D_7e7cc : decode_any W_7e7cc = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7d0 : bv 32 := 0x00470713.
Lemma F_7e7d0 : fetch_word Ubsan.M.loaded_segments (0x7e7d0 : word) = Some W_7e7d0.
Proof. vm_refl. Qed.
Lemma D_7e7d0 : decode_any W_7e7d0 = Some (OpImm ALU_ADD 14 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7d4 : bv 32 := 0x03f85813.
Lemma F_7e7d4 : fetch_word Ubsan.M.loaded_segments (0x7e7d4 : word) = Some W_7e7d4.
Proof. vm_refl. Qed.
Lemma D_7e7d4 : decode_any W_7e7d4 = Some (ShiftImm ALU_SRL 16 16 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7d8 : bv 32 := 0x03f8d893.
Lemma F_7e7d8 : fetch_word Ubsan.M.loaded_segments (0x7e7d8 : word) = Some W_7e7d8.
Proof. vm_refl. Qed.
Lemma D_7e7d8 : decode_any W_7e7d8 = Some (ShiftImm ALU_SRL 17 17 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7dc : bv 32 := 0x03f2d293.
Lemma F_7e7dc : fetch_word Ubsan.M.loaded_segments (0x7e7dc : word) = Some W_7e7dc.
Proof. vm_refl. Qed.
Lemma D_7e7dc : decode_any W_7e7dc = Some (ShiftImm ALU_SRL 5 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7e0 : bv 32 := 0x03f35313.
Lemma F_7e7e0 : fetch_word Ubsan.M.loaded_segments (0x7e7e0 : word) = Some W_7e7e0.
Proof. vm_refl. Qed.
Lemma D_7e7e0 : decode_any W_7e7e0 = Some (ShiftImm ALU_SRL 6 6 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7e4 : bv 32 := 0x03f3d393.
Lemma F_7e7e4 : fetch_word Ubsan.M.loaded_segments (0x7e7e4 : word) = Some W_7e7e4.
Proof. vm_refl. Qed.
Lemma D_7e7e4 : decode_any W_7e7e4 = Some (ShiftImm ALU_SRL 7 7 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7e8 : bv 32 := 0x03fe5e13.
Lemma F_7e7e8 : fetch_word Ubsan.M.loaded_segments (0x7e7e8 : word) = Some W_7e7e8.
Proof. vm_refl. Qed.
Lemma D_7e7e8 : decode_any W_7e7e8 = Some (ShiftImm ALU_SRL 28 28 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7ec : bv 32 := 0x00fe87b3.
Lemma F_7e7ec : fetch_word Ubsan.M.loaded_segments (0x7e7ec : word) = Some W_7e7ec.
Proof. vm_refl. Qed.
Lemma D_7e7ec : decode_any W_7e7ec = Some (Op ALU_ADD 15 29 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7f0 : bv 32 := 0x010787b3.
Lemma F_7e7f0 : fetch_word Ubsan.M.loaded_segments (0x7e7f0 : word) = Some W_7e7f0.
Proof. vm_refl. Qed.
Lemma D_7e7f0 : decode_any W_7e7f0 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7f4 : bv 32 := 0x005888b3.
Lemma F_7e7f4 : fetch_word Ubsan.M.loaded_segments (0x7e7f4 : word) = Some W_7e7f4.
Proof. vm_refl. Qed.
Lemma D_7e7f4 : decode_any W_7e7f4 = Some (Op ALU_ADD 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7f8 : bv 32 := 0x00730333.
Lemma F_7e7f8 : fetch_word Ubsan.M.loaded_segments (0x7e7f8 : word) = Some W_7e7f8.
Proof. vm_refl. Qed.
Lemma D_7e7f8 : decode_any W_7e7f8 = Some (Op ALU_ADD 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e7fc : bv 32 := 0x011787b3.
Lemma F_7e7fc : fetch_word Ubsan.M.loaded_segments (0x7e7fc : word) = Some W_7e7fc.
Proof. vm_refl. Qed.
Lemma D_7e7fc : decode_any W_7e7fc = Some (Op ALU_ADD 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e800 : bv 32 := 0x01c30333.
Lemma F_7e800 : fetch_word Ubsan.M.loaded_segments (0x7e800 : word) = Some W_7e800.
Proof. vm_refl. Qed.
Lemma D_7e800 : decode_any W_7e800 = Some (Op ALU_ADD 6 6 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e804 : bv 32 := 0x006787b3.
Lemma F_7e804 : fetch_word Ubsan.M.loaded_segments (0x7e804 : word) = Some W_7e804.
Proof. vm_refl. Qed.
Lemma D_7e804 : decode_any W_7e804 = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e808 : bv 32 := 0x00f6a023.
Lemma F_7e808 : fetch_word Ubsan.M.loaded_segments (0x7e808 : word) = Some W_7e808.
Proof. vm_refl. Qed.
Lemma D_7e808 : decode_any W_7e808 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e80c : bv 32 := 0x00468693.
Lemma F_7e80c : fetch_word Ubsan.M.loaded_segments (0x7e80c : word) = Some W_7e80c.
Proof. vm_refl. Qed.
Lemma D_7e80c : decode_any W_7e80c = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e810 : bv 32 := 0x00150513.
Lemma F_7e810 : fetch_word Ubsan.M.loaded_segments (0x7e810 : word) = Some W_7e810.
Proof. vm_refl. Qed.
Lemma D_7e810 : decode_any W_7e810 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e814 : bv 32 := 0xf80992e3.
Lemma F_7e814 : fetch_word Ubsan.M.loaded_segments (0x7e814 : word) = Some W_7e814.
Proof. vm_refl. Qed.
Lemma D_7e814 : decode_any W_7e814 = Some (Branch BC_NE 19 0 8068, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e818 : bv 32 := 0x00c10593.
Lemma F_7e818 : fetch_word Ubsan.M.loaded_segments (0x7e818 : word) = Some W_7e818.
Proof. vm_refl. Qed.
Lemma D_7e818 : decode_any W_7e818 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e81c : bv 32 := 0x00810613.
Lemma F_7e81c : fetch_word Ubsan.M.loaded_segments (0x7e81c : word) = Some W_7e81c.
Proof. vm_refl. Qed.
Lemma D_7e81c : decode_any W_7e81c = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e820 : bv 32 := 0x000a0513.
Lemma F_7e820 : fetch_word Ubsan.M.loaded_segments (0x7e820 : word) = Some W_7e820.
Proof. vm_refl. Qed.
Lemma D_7e820 : decode_any W_7e820 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e824 : bv 32 := 0x00000693.
Lemma F_7e824 : fetch_word Ubsan.M.loaded_segments (0x7e824 : word) = Some W_7e824.
Proof. vm_refl. Qed.
Lemma D_7e824 : decode_any W_7e824 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e828 : bv 32 := 0xa7def0ef.
Lemma F_7e828 : fetch_word Ubsan.M.loaded_segments (0x7e828 : word) = Some W_7e828.
Proof. vm_refl. Qed.
Lemma D_7e828 : decode_any W_7e828 = Some (Jal 1 2030204, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e82c : bv 32 := 0x000a0513.
Lemma F_7e82c : fetch_word Ubsan.M.loaded_segments (0x7e82c : word) = Some W_7e82c.
Proof. vm_refl. Qed.
Lemma D_7e82c : decode_any W_7e82c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e830 : bv 32 := 0xf1cef0ef.
Lemma F_7e830 : fetch_word Ubsan.M.loaded_segments (0x7e830 : word) = Some W_7e830.
Proof. vm_refl. Qed.
Lemma D_7e830 : decode_any W_7e830 = Some (Jal 1 2029340, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e834 : bv 32 := 0x00050993.
Lemma F_7e834 : fetch_word Ubsan.M.loaded_segments (0x7e834 : word) = Some W_7e834.
Proof. vm_refl. Qed.
Lemma D_7e834 : decode_any W_7e834 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e838 : bv 32 := 0x000a0513.
Lemma F_7e838 : fetch_word Ubsan.M.loaded_segments (0x7e838 : word) = Some W_7e838.
Proof. vm_refl. Qed.
Lemma D_7e838 : decode_any W_7e838 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e83c : bv 32 := 0x9b1f00ef.
Lemma F_7e83c : fetch_word Ubsan.M.loaded_segments (0x7e83c : word) = Some W_7e83c.
Proof. vm_refl. Qed.
Lemma D_7e83c : decode_any W_7e83c = Some (Jal 1 2034096, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e840 : bv 32 := 0x00812583.
Lemma F_7e840 : fetch_word Ubsan.M.loaded_segments (0x7e840 : word) = Some W_7e840.
Proof. vm_refl. Qed.
Lemma D_7e840 : decode_any W_7e840 = Some (Load SZ4 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e844 : bv 32 := 0x32b05863.
Lemma F_7e844 : fetch_word Ubsan.M.loaded_segments (0x7e844 : word) = Some W_7e844.
Proof. vm_refl. Qed.
Lemma D_7e844 : decode_any W_7e844 = Some (Branch BC_GE 0 11 816, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e848 : bv 32 := 0x00000693.
Lemma F_7e848 : fetch_word Ubsan.M.loaded_segments (0x7e848 : word) = Some W_7e848.
Proof. vm_refl. Qed.
Lemma D_7e848 : decode_any W_7e848 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e84c : bv 32 := 0x00000613.
Lemma F_7e84c : fetch_word Ubsan.M.loaded_segments (0x7e84c : word) = Some W_7e84c.
Proof. vm_refl. Qed.
Lemma D_7e84c : decode_any W_7e84c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e850 : bv 32 := 0x00c16283.
Lemma F_7e850 : fetch_word Ubsan.M.loaded_segments (0x7e850 : word) = Some W_7e850.
Proof. vm_refl. Qed.
Lemma D_7e850 : decode_any W_7e850 = Some (Load SZ4 false 5 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e854 : bv 32 := 0xfff00313.
Lemma F_7e854 : fetch_word Ubsan.M.loaded_segments (0x7e854 : word) = Some W_7e854.
Proof. vm_refl. Qed.
Lemma D_7e854 : decode_any W_7e854 = Some (OpImm ALU_ADD 6 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e858 : bv 32 := 0xfff94713.
Lemma F_7e858 : fetch_word Ubsan.M.loaded_segments (0x7e858 : word) = Some W_7e858.
Proof. vm_refl. Qed.
Lemma D_7e858 : decode_any W_7e858 = Some (OpImm ALU_XOR 14 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e85c : bv 32 := 0x00299793.
Lemma F_7e85c : fetch_word Ubsan.M.loaded_segments (0x7e85c : word) = Some W_7e85c.
Proof. vm_refl. Qed.
Lemma D_7e85c : decode_any W_7e85c = Some (ShiftImm ALU_SLL 15 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e860 : bv 32 := 0x00357813.
Lemma F_7e860 : fetch_word Ubsan.M.loaded_segments (0x7e860 : word) = Some W_7e860.
Proof. vm_refl. Qed.
Lemma D_7e860 : decode_any W_7e860 = Some (OpImm ALU_AND 16 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e864 : bv 32 := 0x01f2f893.
Lemma F_7e864 : fetch_word Ubsan.M.loaded_segments (0x7e864 : word) = Some W_7e864.
Proof. vm_refl. Qed.
Lemma D_7e864 : decode_any W_7e864 = Some (OpImm ALU_AND 17 5 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e868 : bv 32 := 0x405003bb.
Lemma F_7e868 : fetch_word Ubsan.M.loaded_segments (0x7e868 : word) = Some W_7e868.
Proof. vm_refl. Qed.
Lemma D_7e868 : decode_any W_7e868 = Some (Op32 ALU_SUB 7 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e86c : bv 32 := 0x4052d29b.
Lemma F_7e86c : fetch_word Ubsan.M.loaded_segments (0x7e86c : word) = Some W_7e86c.
Proof. vm_refl. Qed.
Lemma D_7e86c : decode_any W_7e86c = Some (ShiftImm32 ALU_SRA 5 5 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e870 : bv 32 := 0x0073133b.
Lemma F_7e870 : fetch_word Ubsan.M.loaded_segments (0x7e870 : word) = Some W_7e870.
Proof. vm_refl. Qed.
Lemma D_7e870 : decode_any W_7e870 = Some (Op32 ALU_SLL 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e874 : bv 32 := 0x02029393.
Lemma F_7e874 : fetch_word Ubsan.M.loaded_segments (0x7e874 : word) = Some W_7e874.
Proof. vm_refl. Qed.
Lemma D_7e874 : decode_any W_7e874 = Some (ShiftImm ALU_SLL 7 5 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e878 : bv 32 := 0x0203d393.
Lemma F_7e878 : fetch_word Ubsan.M.loaded_segments (0x7e878 : word) = Some W_7e878.
Proof. vm_refl. Qed.
Lemma D_7e878 : decode_any W_7e878 = Some (ShiftImm ALU_SRL 7 7 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e87c : bv 32 := 0x00183e13.
Lemma F_7e87c : fetch_word Ubsan.M.loaded_segments (0x7e87c : word) = Some W_7e87c.
Proof. vm_refl. Qed.
Lemma D_7e87c : decode_any W_7e87c = Some (OpImm ALU_SLTU 28 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e880 : bv 32 := 0x00050e93.
Lemma F_7e880 : fetch_word Ubsan.M.loaded_segments (0x7e880 : word) = Some W_7e880.
Proof. vm_refl. Qed.
Lemma D_7e880 : decode_any W_7e880 = Some (OpImm ALU_ADD 29 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e884 : bv 32 := 0x00a03f33.
Lemma F_7e884 : fetch_word Ubsan.M.loaded_segments (0x7e884 : word) = Some W_7e884.
Proof. vm_refl. Qed.
Lemma D_7e884 : decode_any W_7e884 = Some (Op ALU_SLTU 30 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e888 : bv 32 := 0x10505263.
Lemma F_7e888 : fetch_word Ubsan.M.loaded_segments (0x7e888 : word) = Some W_7e888.
Proof. vm_refl. Qed.
Lemma D_7e888 : decode_any W_7e888 = Some (Branch BC_GE 0 5 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e88c : bv 32 := 0x01ee7fb3.
Lemma F_7e88c : fetch_word Ubsan.M.loaded_segments (0x7e88c : word) = Some W_7e88c.
Proof. vm_refl. Qed.
Lemma D_7e88c : decode_any W_7e88c = Some (Op ALU_AND 31 28 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e890 : bv 32 := 0x00038a13.
Lemma F_7e890 : fetch_word Ubsan.M.loaded_segments (0x7e890 : word) = Some W_7e890.
Proof. vm_refl. Qed.
Lemma D_7e890 : decode_any W_7e890 = Some (OpImm ALU_ADD 20 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e894 : bv 32 := 0x00050a93.
Lemma F_7e894 : fetch_word Ubsan.M.loaded_segments (0x7e894 : word) = Some W_7e894.
Proof. vm_refl. Qed.
Lemma D_7e894 : decode_any W_7e894 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e898 : bv 32 := 0x000e8b13.
Lemma F_7e898 : fetch_word Ubsan.M.loaded_segments (0x7e898 : word) = Some W_7e898.
Proof. vm_refl. Qed.
Lemma D_7e898 : decode_any W_7e898 = Some (OpImm ALU_ADD 22 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e89c : bv 32 := 0x0140006f.
Lemma F_7e89c : fetch_word Ubsan.M.loaded_segments (0x7e89c : word) = Some W_7e89c.
Proof. vm_refl. Qed.
Lemma D_7e89c : decode_any W_7e89c = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8a0 : bv 32 := 0x004b0b13.
Lemma F_7e8a0 : fetch_word Ubsan.M.loaded_segments (0x7e8a0 : word) = Some W_7e8a0.
Proof. vm_refl. Qed.
Lemma D_7e8a0 : decode_any W_7e8a0 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8a4 : bv 32 := 0xfffa0a13.
Lemma F_7e8a4 : fetch_word Ubsan.M.loaded_segments (0x7e8a4 : word) = Some W_7e8a4.
Proof. vm_refl. Qed.
Lemma D_7e8a4 : decode_any W_7e8a4 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8a8 : bv 32 := 0x004a8a93.
Lemma F_7e8a8 : fetch_word Ubsan.M.loaded_segments (0x7e8a8 : word) = Some W_7e8a8.
Proof. vm_refl. Qed.
Lemma D_7e8a8 : decode_any W_7e8a8 = Some (OpImm ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8ac : bv 32 := 0x0c0a0a63.
Lemma F_7e8ac : fetch_word Ubsan.M.loaded_segments (0x7e8ac : word) = Some W_7e8ac.
Proof. vm_refl. Qed.
Lemma D_7e8ac : decode_any W_7e8ac = Some (Branch BC_EQ 20 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8b0 : bv 32 := 0x2cab6c63.
Lemma F_7e8b0 : fetch_word Ubsan.M.loaded_segments (0x7e8b0 : word) = Some W_7e8b0.
Proof. vm_refl. Qed.
Lemma D_7e8b0 : decode_any W_7e8b0 = Some (Branch BC_LTU 22 10 728, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8b4 : bv 32 := 0x001b3b93.
Lemma F_7e8b4 : fetch_word Ubsan.M.loaded_segments (0x7e8b4 : word) = Some W_7e8b4.
Proof. vm_refl. Qed.
Lemma D_7e8b4 : decode_any W_7e8b4 = Some (OpImm ALU_SLTU 23 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8b8 : bv 32 := 0x017f4bb3.
Lemma F_7e8b8 : fetch_word Ubsan.M.loaded_segments (0x7e8b8 : word) = Some W_7e8b8.
Proof. vm_refl. Qed.
Lemma D_7e8b8 : decode_any W_7e8b8 = Some (Op ALU_XOR 23 30 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8bc : bv 32 := 0x2c0b8663.
Lemma F_7e8bc : fetch_word Ubsan.M.loaded_segments (0x7e8bc : word) = Some W_7e8bc.
Proof. vm_refl. Qed.
Lemma D_7e8bc : decode_any W_7e8bc = Some (Branch BC_EQ 23 0 716, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8c0 : bv 32 := 0x2c0f8463.
Lemma F_7e8c0 : fetch_word Ubsan.M.loaded_segments (0x7e8c0 : word) = Some W_7e8c0.
Proof. vm_refl. Qed.
Lemma D_7e8c0 : decode_any W_7e8c0 = Some (Branch BC_EQ 31 0 712, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8c4 : bv 32 := 0x000aeb83.
Lemma F_7e8c4 : fetch_word Ubsan.M.loaded_segments (0x7e8c4 : word) = Some W_7e8c4.
Proof. vm_refl. Qed.
Lemma D_7e8c4 : decode_any W_7e8c4 = Some (Load SZ4 false 23 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8c8 : bv 32 := 0xfc0b8ce3.
Lemma F_7e8c8 : fetch_word Ubsan.M.loaded_segments (0x7e8c8 : word) = Some W_7e8c8.
Proof. vm_refl. Qed.
Lemma D_7e8c8 : decode_any W_7e8c8 = Some (Branch BC_EQ 23 0 8152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8cc : bv 32 := 0x0ffbfc13.
Lemma F_7e8cc : fetch_word Ubsan.M.loaded_segments (0x7e8cc : word) = Some W_7e8cc.
Proof. vm_refl. Qed.
Lemma D_7e8cc : decode_any W_7e8cc = Some (OpImm ALU_AND 24 23 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8d0 : bv 32 := 0x002c1c13.
Lemma F_7e8d0 : fetch_word Ubsan.M.loaded_segments (0x7e8d0 : word) = Some W_7e8d0.
Proof. vm_refl. Qed.
Lemma D_7e8d0 : decode_any W_7e8d0 = Some (ShiftImm ALU_SLL 24 24 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8d4 : bv 32 := 0x2b876a63.
Lemma F_7e8d4 : fetch_word Ubsan.M.loaded_segments (0x7e8d4 : word) = Some W_7e8d4.
Proof. vm_refl. Qed.
Lemma D_7e8d4 : decode_any W_7e8d4 = Some (Branch BC_LTU 14 24 692, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8d8 : bv 32 := 0x01890c33.
Lemma F_7e8d8 : fetch_word Ubsan.M.loaded_segments (0x7e8d8 : word) = Some W_7e8d8.
Proof. vm_refl. Qed.
Lemma D_7e8d8 : decode_any W_7e8d8 = Some (Op ALU_ADD 24 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8dc : bv 32 := 0x003c7c93.
Lemma F_7e8dc : fetch_word Ubsan.M.loaded_segments (0x7e8dc : word) = Some W_7e8dc.
Proof. vm_refl. Qed.
Lemma D_7e8dc : decode_any W_7e8dc = Some (OpImm ALU_AND 25 24 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8e0 : bv 32 := 0x2a0c9463.
Lemma F_7e8e0 : fetch_word Ubsan.M.loaded_segments (0x7e8e0 : word) = Some W_7e8e0.
Proof. vm_refl. Qed.
Lemma D_7e8e0 : decode_any W_7e8e0 = Some (Branch BC_NE 25 0 680, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8e4 : bv 32 := 0x006bdc93.
Lemma F_7e8e4 : fetch_word Ubsan.M.loaded_segments (0x7e8e4 : word) = Some W_7e8e4.
Proof. vm_refl. Qed.
Lemma D_7e8e4 : decode_any W_7e8e4 = Some (ShiftImm ALU_SRL 25 23 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8e8 : bv 32 := 0x3fccfc93.
Lemma F_7e8e8 : fetch_word Ubsan.M.loaded_segments (0x7e8e8 : word) = Some W_7e8e8.
Proof. vm_refl. Qed.
Lemma D_7e8e8 : decode_any W_7e8e8 = Some (OpImm ALU_AND 25 25 1020, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8ec : bv 32 := 0x29976e63.
Lemma F_7e8ec : fetch_word Ubsan.M.loaded_segments (0x7e8ec : word) = Some W_7e8ec.
Proof. vm_refl. Qed.
Lemma D_7e8ec : decode_any W_7e8ec = Some (Branch BC_LTU 14 25 668, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8f0 : bv 32 := 0x01990cb3.
Lemma F_7e8f0 : fetch_word Ubsan.M.loaded_segments (0x7e8f0 : word) = Some W_7e8f0.
Proof. vm_refl. Qed.
Lemma D_7e8f0 : decode_any W_7e8f0 = Some (Op ALU_ADD 25 18 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8f4 : bv 32 := 0x003cfd13.
Lemma F_7e8f4 : fetch_word Ubsan.M.loaded_segments (0x7e8f4 : word) = Some W_7e8f4.
Proof. vm_refl. Qed.
Lemma D_7e8f4 : decode_any W_7e8f4 = Some (OpImm ALU_AND 26 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8f8 : bv 32 := 0x280d1863.
Lemma F_7e8f8 : fetch_word Ubsan.M.loaded_segments (0x7e8f8 : word) = Some W_7e8f8.
Proof. vm_refl. Qed.
Lemma D_7e8f8 : decode_any W_7e8f8 = Some (Branch BC_NE 26 0 656, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e8fc : bv 32 := 0x000c2d03.
Lemma F_7e8fc : fetch_word Ubsan.M.loaded_segments (0x7e8fc : word) = Some W_7e8fc.
Proof. vm_refl. Qed.
Lemma D_7e8fc : decode_any W_7e8fc = Some (Load SZ4 true 26 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e900 : bv 32 := 0x000cac83.
Lemma F_7e900 : fetch_word Ubsan.M.loaded_segments (0x7e900 : word) = Some W_7e900.
Proof. vm_refl. Qed.
Lemma D_7e900 : decode_any W_7e900 = Some (Load SZ4 true 25 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e904 : bv 32 := 0x019d0c33.
Lemma F_7e904 : fetch_word Ubsan.M.loaded_segments (0x7e904 : word) = Some W_7e904.
Proof. vm_refl. Qed.
Lemma D_7e904 : decode_any W_7e904 = Some (Op ALU_ADD 24 26 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e908 : bv 32 := 0x019d0cbb.
Lemma F_7e908 : fetch_word Ubsan.M.loaded_segments (0x7e908 : word) = Some W_7e908.
Proof. vm_refl. Qed.
Lemma D_7e908 : decode_any W_7e908 = Some (Op32 ALU_ADD 25 26 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e90c : bv 32 := 0x278c9e63.
Lemma F_7e90c : fetch_word Ubsan.M.loaded_segments (0x7e90c : word) = Some W_7e90c.
Proof. vm_refl. Qed.
Lemma D_7e90c : decode_any W_7e90c = Some (Branch BC_NE 25 24 636, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e910 : bv 32 := 0x00ebdc93.
Lemma F_7e910 : fetch_word Ubsan.M.loaded_segments (0x7e910 : word) = Some W_7e910.
Proof. vm_refl. Qed.
Lemma D_7e910 : decode_any W_7e910 = Some (ShiftImm ALU_SRL 25 23 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e914 : bv 32 := 0x3fccfc93.
Lemma F_7e914 : fetch_word Ubsan.M.loaded_segments (0x7e914 : word) = Some W_7e914.
Proof. vm_refl. Qed.
Lemma D_7e914 : decode_any W_7e914 = Some (OpImm ALU_AND 25 25 1020, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e918 : bv 32 := 0x27976863.
Lemma F_7e918 : fetch_word Ubsan.M.loaded_segments (0x7e918 : word) = Some W_7e918.
Proof. vm_refl. Qed.
Lemma D_7e918 : decode_any W_7e918 = Some (Branch BC_LTU 14 25 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e91c : bv 32 := 0x01990cb3.
Lemma F_7e91c : fetch_word Ubsan.M.loaded_segments (0x7e91c : word) = Some W_7e91c.
Proof. vm_refl. Qed.
Lemma D_7e91c : decode_any W_7e91c = Some (Op ALU_ADD 25 18 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e920 : bv 32 := 0x003cfd13.
Lemma F_7e920 : fetch_word Ubsan.M.loaded_segments (0x7e920 : word) = Some W_7e920.
Proof. vm_refl. Qed.
Lemma D_7e920 : decode_any W_7e920 = Some (OpImm ALU_AND 26 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e924 : bv 32 := 0x260d1263.
Lemma F_7e924 : fetch_word Ubsan.M.loaded_segments (0x7e924 : word) = Some W_7e924.
Proof. vm_refl. Qed.
Lemma D_7e924 : decode_any W_7e924 = Some (Branch BC_NE 26 0 612, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e928 : bv 32 := 0x000cac83.
Lemma F_7e928 : fetch_word Ubsan.M.loaded_segments (0x7e928 : word) = Some W_7e928.
Proof. vm_refl. Qed.
Lemma D_7e928 : decode_any W_7e928 = Some (Load SZ4 true 25 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e92c : bv 32 := 0x000c0d1b.
Lemma F_7e92c : fetch_word Ubsan.M.loaded_segments (0x7e92c : word) = Some W_7e92c.
Proof. vm_refl. Qed.
Lemma D_7e92c : decode_any W_7e92c = Some (OpImm32 26 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e930 : bv 32 := 0x019d0c33.
Lemma F_7e930 : fetch_word Ubsan.M.loaded_segments (0x7e930 : word) = Some W_7e930.
Proof. vm_refl. Qed.
Lemma D_7e930 : decode_any W_7e930 = Some (Op ALU_ADD 24 26 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e934 : bv 32 := 0x019d0cbb.
Lemma F_7e934 : fetch_word Ubsan.M.loaded_segments (0x7e934 : word) = Some W_7e934.
Proof. vm_refl. Qed.
Lemma D_7e934 : decode_any W_7e934 = Some (Op32 ALU_ADD 25 26 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e938 : bv 32 := 0x258c9863.
Lemma F_7e938 : fetch_word Ubsan.M.loaded_segments (0x7e938 : word) = Some W_7e938.
Proof. vm_refl. Qed.
Lemma D_7e938 : decode_any W_7e938 = Some (Branch BC_NE 25 24 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e93c : bv 32 := 0x018bdb9b.
Lemma F_7e93c : fetch_word Ubsan.M.loaded_segments (0x7e93c : word) = Some W_7e93c.
Proof. vm_refl. Qed.
Lemma D_7e93c : decode_any W_7e93c = Some (ShiftImm32 ALU_SRL 23 23 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e940 : bv 32 := 0x002b9b93.
Lemma F_7e940 : fetch_word Ubsan.M.loaded_segments (0x7e940 : word) = Some W_7e940.
Proof. vm_refl. Qed.
Lemma D_7e940 : decode_any W_7e940 = Some (ShiftImm ALU_SLL 23 23 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e944 : bv 32 := 0x25776263.
Lemma F_7e944 : fetch_word Ubsan.M.loaded_segments (0x7e944 : word) = Some W_7e944.
Proof. vm_refl. Qed.
Lemma D_7e944 : decode_any W_7e944 = Some (Branch BC_LTU 14 23 580, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e948 : bv 32 := 0x01790bb3.
Lemma F_7e948 : fetch_word Ubsan.M.loaded_segments (0x7e948 : word) = Some W_7e948.
Proof. vm_refl. Qed.
Lemma D_7e948 : decode_any W_7e948 = Some (Op ALU_ADD 23 18 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e94c : bv 32 := 0x003bfc93.
Lemma F_7e94c : fetch_word Ubsan.M.loaded_segments (0x7e94c : word) = Some W_7e94c.
Proof. vm_refl. Qed.
Lemma D_7e94c : decode_any W_7e94c = Some (OpImm ALU_AND 25 23 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e950 : bv 32 := 0x220c9c63.
Lemma F_7e950 : fetch_word Ubsan.M.loaded_segments (0x7e950 : word) = Some W_7e950.
Proof. vm_refl. Qed.
Lemma D_7e950 : decode_any W_7e950 = Some (Branch BC_NE 25 0 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e954 : bv 32 := 0x000bac83.
Lemma F_7e954 : fetch_word Ubsan.M.loaded_segments (0x7e954 : word) = Some W_7e954.
Proof. vm_refl. Qed.
Lemma D_7e954 : decode_any W_7e954 = Some (Load SZ4 true 25 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e958 : bv 32 := 0x000c0c1b.
Lemma F_7e958 : fetch_word Ubsan.M.loaded_segments (0x7e958 : word) = Some W_7e958.
Proof. vm_refl. Qed.
Lemma D_7e958 : decode_any W_7e958 = Some (OpImm32 24 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e95c : bv 32 := 0x019c0bb3.
Lemma F_7e95c : fetch_word Ubsan.M.loaded_segments (0x7e95c : word) = Some W_7e95c.
Proof. vm_refl. Qed.
Lemma D_7e95c : decode_any W_7e95c = Some (Op ALU_ADD 23 24 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e960 : bv 32 := 0x019c0c3b.
Lemma F_7e960 : fetch_word Ubsan.M.loaded_segments (0x7e960 : word) = Some W_7e960.
Proof. vm_refl. Qed.
Lemma D_7e960 : decode_any W_7e960 = Some (Op32 ALU_ADD 24 24 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e964 : bv 32 := 0x237c1263.
Lemma F_7e964 : fetch_word Ubsan.M.loaded_segments (0x7e964 : word) = Some W_7e964.
Proof. vm_refl. Qed.
Lemma D_7e964 : decode_any W_7e964 = Some (Branch BC_NE 24 23 548, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e968 : bv 32 := 0x000b8b9b.
Lemma F_7e968 : fetch_word Ubsan.M.loaded_segments (0x7e968 : word) = Some W_7e968.
Proof. vm_refl. Qed.
Lemma D_7e968 : decode_any W_7e968 = Some (OpImm32 23 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e96c : bv 32 := 0x00060c1b.
Lemma F_7e96c : fetch_word Ubsan.M.loaded_segments (0x7e96c : word) = Some W_7e96c.
Proof. vm_refl. Qed.
Lemma D_7e96c : decode_any W_7e96c = Some (OpImm32 24 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e970 : bv 32 := 0x017c0633.
Lemma F_7e970 : fetch_word Ubsan.M.loaded_segments (0x7e970 : word) = Some W_7e970.
Proof. vm_refl. Qed.
Lemma D_7e970 : decode_any W_7e970 = Some (Op ALU_ADD 12 24 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e974 : bv 32 := 0x017c0bbb.
Lemma F_7e974 : fetch_word Ubsan.M.loaded_segments (0x7e974 : word) = Some W_7e974.
Proof. vm_refl. Qed.
Lemma D_7e974 : decode_any W_7e974 = Some (Op32 ALU_ADD 23 24 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e978 : bv 32 := 0xf2cb84e3.
Lemma F_7e978 : fetch_word Ubsan.M.loaded_segments (0x7e978 : word) = Some W_7e978.
Proof. vm_refl. Qed.
Lemma D_7e978 : decode_any W_7e978 = Some (Branch BC_EQ 23 12 7976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e97c : bv 32 := 0x20c0006f.
Lemma F_7e97c : fetch_word Ubsan.M.loaded_segments (0x7e97c : word) = Some W_7e97c.
Proof. vm_refl. Qed.
Lemma D_7e97c : decode_any W_7e97c = Some (Jal 0 524, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e980 : bv 32 := 0x00028f93.
Lemma F_7e980 : fetch_word Ubsan.M.loaded_segments (0x7e980 : word) = Some W_7e980.
Proof. vm_refl. Qed.
Lemma D_7e980 : decode_any W_7e980 = Some (OpImm ALU_ADD 31 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e984 : bv 32 := 0x00089863.
Lemma F_7e984 : fetch_word Ubsan.M.loaded_segments (0x7e984 : word) = Some W_7e984.
Proof. vm_refl. Qed.
Lemma D_7e984 : decode_any W_7e984 = Some (Branch BC_NE 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e988 : bv 32 := 0x0e80006f.
Lemma F_7e988 : fetch_word Ubsan.M.loaded_segments (0x7e988 : word) = Some W_7e988.
Proof. vm_refl. Qed.
Lemma D_7e988 : decode_any W_7e988 = Some (Jal 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e98c : bv 32 := 0x00000f93.
Lemma F_7e98c : fetch_word Ubsan.M.loaded_segments (0x7e98c : word) = Some W_7e98c.
Proof. vm_refl. Qed.
Lemma D_7e98c : decode_any W_7e98c = Some (OpImm ALU_ADD 31 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e990 : bv 32 := 0x0e088063.
Lemma F_7e990 : fetch_word Ubsan.M.loaded_segments (0x7e990 : word) = Some W_7e990.
Proof. vm_refl. Qed.
Lemma D_7e990 : decode_any W_7e990 = Some (Branch BC_EQ 17 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e994 : bv 32 := 0x002f9f93.
Lemma F_7e994 : fetch_word Ubsan.M.loaded_segments (0x7e994 : word) = Some W_7e994.
Proof. vm_refl. Qed.
Lemma D_7e994 : decode_any W_7e994 = Some (ShiftImm ALU_SLL 31 31 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e998 : bv 32 := 0x01f50fb3.
Lemma F_7e998 : fetch_word Ubsan.M.loaded_segments (0x7e998 : word) = Some W_7e998.
Proof. vm_refl. Qed.
Lemma D_7e998 : decode_any W_7e998 = Some (Op ALU_ADD 31 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e99c : bv 32 := 0x1eafe663.
Lemma F_7e99c : fetch_word Ubsan.M.loaded_segments (0x7e99c : word) = Some W_7e99c.
Proof. vm_refl. Qed.
Lemma D_7e99c : decode_any W_7e99c = Some (Branch BC_LTU 31 10 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9a0 : bv 32 := 0x001fba13.
Lemma F_7e9a0 : fetch_word Ubsan.M.loaded_segments (0x7e9a0 : word) = Some W_7e9a0.
Proof. vm_refl. Qed.
Lemma D_7e9a0 : decode_any W_7e9a0 = Some (OpImm ALU_SLTU 20 31 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9a4 : bv 32 := 0x014f4a33.
Lemma F_7e9a4 : fetch_word Ubsan.M.loaded_segments (0x7e9a4 : word) = Some W_7e9a4.
Proof. vm_refl. Qed.
Lemma D_7e9a4 : decode_any W_7e9a4 = Some (Op ALU_XOR 20 30 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9a8 : bv 32 := 0x1e0a0063.
Lemma F_7e9a8 : fetch_word Ubsan.M.loaded_segments (0x7e9a8 : word) = Some W_7e9a8.
Proof. vm_refl. Qed.
Lemma D_7e9a8 : decode_any W_7e9a8 = Some (Branch BC_EQ 20 0 480, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9ac : bv 32 := 0x1c050e63.
Lemma F_7e9ac : fetch_word Ubsan.M.loaded_segments (0x7e9ac : word) = Some W_7e9ac.
Proof. vm_refl. Qed.
Lemma D_7e9ac : decode_any W_7e9ac = Some (Branch BC_EQ 10 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9b0 : bv 32 := 0x1c081c63.
Lemma F_7e9b0 : fetch_word Ubsan.M.loaded_segments (0x7e9b0 : word) = Some W_7e9b0.
Proof. vm_refl. Qed.
Lemma D_7e9b0 : decode_any W_7e9b0 = Some (Branch BC_NE 16 0 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9b4 : bv 32 := 0x000faf83.
Lemma F_7e9b4 : fetch_word Ubsan.M.loaded_segments (0x7e9b4 : word) = Some W_7e9b4.
Proof. vm_refl. Qed.
Lemma D_7e9b4 : decode_any W_7e9b4 = Some (Load SZ4 true 31 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9b8 : bv 32 := 0x006fffb3.
Lemma F_7e9b8 : fetch_word Ubsan.M.loaded_segments (0x7e9b8 : word) = Some W_7e9b8.
Proof. vm_refl. Qed.
Lemma D_7e9b8 : decode_any W_7e9b8 = Some (Op ALU_AND 31 31 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9bc : bv 32 := 0x0a0f8a63.
Lemma F_7e9bc : fetch_word Ubsan.M.loaded_segments (0x7e9bc : word) = Some W_7e9bc.
Proof. vm_refl. Qed.
Lemma D_7e9bc : decode_any W_7e9bc = Some (Branch BC_EQ 31 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9c0 : bv 32 := 0x0ffffa13.
Lemma F_7e9c0 : fetch_word Ubsan.M.loaded_segments (0x7e9c0 : word) = Some W_7e9c0.
Proof. vm_refl. Qed.
Lemma D_7e9c0 : decode_any W_7e9c0 = Some (OpImm ALU_AND 20 31 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9c4 : bv 32 := 0x002a1a13.
Lemma F_7e9c4 : fetch_word Ubsan.M.loaded_segments (0x7e9c4 : word) = Some W_7e9c4.
Proof. vm_refl. Qed.
Lemma D_7e9c4 : decode_any W_7e9c4 = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9c8 : bv 32 := 0x1d476063.
Lemma F_7e9c8 : fetch_word Ubsan.M.loaded_segments (0x7e9c8 : word) = Some W_7e9c8.
Proof. vm_refl. Qed.
Lemma D_7e9c8 : decode_any W_7e9c8 = Some (Branch BC_LTU 14 20 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9cc : bv 32 := 0x01490a33.
Lemma F_7e9cc : fetch_word Ubsan.M.loaded_segments (0x7e9cc : word) = Some W_7e9cc.
Proof. vm_refl. Qed.
Lemma D_7e9cc : decode_any W_7e9cc = Some (Op ALU_ADD 20 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9d0 : bv 32 := 0x003a7a93.
Lemma F_7e9d0 : fetch_word Ubsan.M.loaded_segments (0x7e9d0 : word) = Some W_7e9d0.
Proof. vm_refl. Qed.
Lemma D_7e9d0 : decode_any W_7e9d0 = Some (OpImm ALU_AND 21 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9d4 : bv 32 := 0x1a0a9a63.
Lemma F_7e9d4 : fetch_word Ubsan.M.loaded_segments (0x7e9d4 : word) = Some W_7e9d4.
Proof. vm_refl. Qed.
Lemma D_7e9d4 : decode_any W_7e9d4 = Some (Branch BC_NE 21 0 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9d8 : bv 32 := 0x006fda93.
Lemma F_7e9d8 : fetch_word Ubsan.M.loaded_segments (0x7e9d8 : word) = Some W_7e9d8.
Proof. vm_refl. Qed.
Lemma D_7e9d8 : decode_any W_7e9d8 = Some (ShiftImm ALU_SRL 21 31 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9dc : bv 32 := 0x3fcafa93.
Lemma F_7e9dc : fetch_word Ubsan.M.loaded_segments (0x7e9dc : word) = Some W_7e9dc.
Proof. vm_refl. Qed.
Lemma D_7e9dc : decode_any W_7e9dc = Some (OpImm ALU_AND 21 21 1020, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9e0 : bv 32 := 0x1b576463.
Lemma F_7e9e0 : fetch_word Ubsan.M.loaded_segments (0x7e9e0 : word) = Some W_7e9e0.
Proof. vm_refl. Qed.
Lemma D_7e9e0 : decode_any W_7e9e0 = Some (Branch BC_LTU 14 21 424, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9e4 : bv 32 := 0x01590ab3.
Lemma F_7e9e4 : fetch_word Ubsan.M.loaded_segments (0x7e9e4 : word) = Some W_7e9e4.
Proof. vm_refl. Qed.
Lemma D_7e9e4 : decode_any W_7e9e4 = Some (Op ALU_ADD 21 18 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9e8 : bv 32 := 0x003afb13.
Lemma F_7e9e8 : fetch_word Ubsan.M.loaded_segments (0x7e9e8 : word) = Some W_7e9e8.
Proof. vm_refl. Qed.
Lemma D_7e9e8 : decode_any W_7e9e8 = Some (OpImm ALU_AND 22 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9ec : bv 32 := 0x180b1e63.
Lemma F_7e9ec : fetch_word Ubsan.M.loaded_segments (0x7e9ec : word) = Some W_7e9ec.
Proof. vm_refl. Qed.
Lemma D_7e9ec : decode_any W_7e9ec = Some (Branch BC_NE 22 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9f0 : bv 32 := 0x000a2b03.
Lemma F_7e9f0 : fetch_word Ubsan.M.loaded_segments (0x7e9f0 : word) = Some W_7e9f0.
Proof. vm_refl. Qed.
Lemma D_7e9f0 : decode_any W_7e9f0 = Some (Load SZ4 true 22 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9f4 : bv 32 := 0x000aaa83.
Lemma F_7e9f4 : fetch_word Ubsan.M.loaded_segments (0x7e9f4 : word) = Some W_7e9f4.
Proof. vm_refl. Qed.
Lemma D_7e9f4 : decode_any W_7e9f4 = Some (Load SZ4 true 21 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9f8 : bv 32 := 0x015b0a33.
Lemma F_7e9f8 : fetch_word Ubsan.M.loaded_segments (0x7e9f8 : word) = Some W_7e9f8.
Proof. vm_refl. Qed.
Lemma D_7e9f8 : decode_any W_7e9f8 = Some (Op ALU_ADD 20 22 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_7e9fc : bv 32 := 0x015b0abb.
Lemma F_7e9fc : fetch_word Ubsan.M.loaded_segments (0x7e9fc : word) = Some W_7e9fc.
Proof. vm_refl. Qed.
Lemma D_7e9fc : decode_any W_7e9fc = Some (Op32 ALU_ADD 21 22 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea00 : bv 32 := 0x194a9463.
Lemma F_7ea00 : fetch_word Ubsan.M.loaded_segments (0x7ea00 : word) = Some W_7ea00.
Proof. vm_refl. Qed.
Lemma D_7ea00 : decode_any W_7ea00 = Some (Branch BC_NE 21 20 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea04 : bv 32 := 0x00efda93.
Lemma F_7ea04 : fetch_word Ubsan.M.loaded_segments (0x7ea04 : word) = Some W_7ea04.
Proof. vm_refl. Qed.
Lemma D_7ea04 : decode_any W_7ea04 = Some (ShiftImm ALU_SRL 21 31 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea08 : bv 32 := 0x3fcafa93.
Lemma F_7ea08 : fetch_word Ubsan.M.loaded_segments (0x7ea08 : word) = Some W_7ea08.
Proof. vm_refl. Qed.
Lemma D_7ea08 : decode_any W_7ea08 = Some (OpImm ALU_AND 21 21 1020, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea0c : bv 32 := 0x17576e63.
Lemma F_7ea0c : fetch_word Ubsan.M.loaded_segments (0x7ea0c : word) = Some W_7ea0c.
Proof. vm_refl. Qed.
Lemma D_7ea0c : decode_any W_7ea0c = Some (Branch BC_LTU 14 21 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea10 : bv 32 := 0x01590ab3.
Lemma F_7ea10 : fetch_word Ubsan.M.loaded_segments (0x7ea10 : word) = Some W_7ea10.
Proof. vm_refl. Qed.
Lemma D_7ea10 : decode_any W_7ea10 = Some (Op ALU_ADD 21 18 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea14 : bv 32 := 0x003afb13.
Lemma F_7ea14 : fetch_word Ubsan.M.loaded_segments (0x7ea14 : word) = Some W_7ea14.
Proof. vm_refl. Qed.
Lemma D_7ea14 : decode_any W_7ea14 = Some (OpImm ALU_AND 22 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea18 : bv 32 := 0x160b1863.
Lemma F_7ea18 : fetch_word Ubsan.M.loaded_segments (0x7ea18 : word) = Some W_7ea18.
Proof. vm_refl. Qed.
Lemma D_7ea18 : decode_any W_7ea18 = Some (Branch BC_NE 22 0 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea1c : bv 32 := 0x000aaa83.
Lemma F_7ea1c : fetch_word Ubsan.M.loaded_segments (0x7ea1c : word) = Some W_7ea1c.
Proof. vm_refl. Qed.
Lemma D_7ea1c : decode_any W_7ea1c = Some (Load SZ4 true 21 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea20 : bv 32 := 0x000a0b1b.
Lemma F_7ea20 : fetch_word Ubsan.M.loaded_segments (0x7ea20 : word) = Some W_7ea20.
Proof. vm_refl. Qed.
Lemma D_7ea20 : decode_any W_7ea20 = Some (OpImm32 22 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea24 : bv 32 := 0x015b0a33.
Lemma F_7ea24 : fetch_word Ubsan.M.loaded_segments (0x7ea24 : word) = Some W_7ea24.
Proof. vm_refl. Qed.
Lemma D_7ea24 : decode_any W_7ea24 = Some (Op ALU_ADD 20 22 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea28 : bv 32 := 0x015b0abb.
Lemma F_7ea28 : fetch_word Ubsan.M.loaded_segments (0x7ea28 : word) = Some W_7ea28.
Proof. vm_refl. Qed.
Lemma D_7ea28 : decode_any W_7ea28 = Some (Op32 ALU_ADD 21 22 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea2c : bv 32 := 0x154a9e63.
Lemma F_7ea2c : fetch_word Ubsan.M.loaded_segments (0x7ea2c : word) = Some W_7ea2c.
Proof. vm_refl. Qed.
Lemma D_7ea2c : decode_any W_7ea2c = Some (Branch BC_NE 21 20 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea30 : bv 32 := 0x018fdf9b.
Lemma F_7ea30 : fetch_word Ubsan.M.loaded_segments (0x7ea30 : word) = Some W_7ea30.
Proof. vm_refl. Qed.
Lemma D_7ea30 : decode_any W_7ea30 = Some (ShiftImm32 ALU_SRL 31 31 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea34 : bv 32 := 0x002f9f93.
Lemma F_7ea34 : fetch_word Ubsan.M.loaded_segments (0x7ea34 : word) = Some W_7ea34.
Proof. vm_refl. Qed.
Lemma D_7ea34 : decode_any W_7ea34 = Some (ShiftImm ALU_SLL 31 31 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea38 : bv 32 := 0x15f76863.
Lemma F_7ea38 : fetch_word Ubsan.M.loaded_segments (0x7ea38 : word) = Some W_7ea38.
Proof. vm_refl. Qed.
Lemma D_7ea38 : decode_any W_7ea38 = Some (Branch BC_LTU 14 31 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea3c : bv 32 := 0x01f90fb3.
Lemma F_7ea3c : fetch_word Ubsan.M.loaded_segments (0x7ea3c : word) = Some W_7ea3c.
Proof. vm_refl. Qed.
Lemma D_7ea3c : decode_any W_7ea3c = Some (Op ALU_ADD 31 18 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea40 : bv 32 := 0x003ffa93.
Lemma F_7ea40 : fetch_word Ubsan.M.loaded_segments (0x7ea40 : word) = Some W_7ea40.
Proof. vm_refl. Qed.
Lemma D_7ea40 : decode_any W_7ea40 = Some (OpImm ALU_AND 21 31 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea44 : bv 32 := 0x140a9263.
Lemma F_7ea44 : fetch_word Ubsan.M.loaded_segments (0x7ea44 : word) = Some W_7ea44.
Proof. vm_refl. Qed.
Lemma D_7ea44 : decode_any W_7ea44 = Some (Branch BC_NE 21 0 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea48 : bv 32 := 0x000faa83.
Lemma F_7ea48 : fetch_word Ubsan.M.loaded_segments (0x7ea48 : word) = Some W_7ea48.
Proof. vm_refl. Qed.
Lemma D_7ea48 : decode_any W_7ea48 = Some (Load SZ4 true 21 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea4c : bv 32 := 0x000a0a1b.
Lemma F_7ea4c : fetch_word Ubsan.M.loaded_segments (0x7ea4c : word) = Some W_7ea4c.
Proof. vm_refl. Qed.
Lemma D_7ea4c : decode_any W_7ea4c = Some (OpImm32 20 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea50 : bv 32 := 0x015a0fb3.
Lemma F_7ea50 : fetch_word Ubsan.M.loaded_segments (0x7ea50 : word) = Some W_7ea50.
Proof. vm_refl. Qed.
Lemma D_7ea50 : decode_any W_7ea50 = Some (Op ALU_ADD 31 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea54 : bv 32 := 0x015a0a3b.
Lemma F_7ea54 : fetch_word Ubsan.M.loaded_segments (0x7ea54 : word) = Some W_7ea54.
Proof. vm_refl. Qed.
Lemma D_7ea54 : decode_any W_7ea54 = Some (Op32 ALU_ADD 20 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea58 : bv 32 := 0x13fa1863.
Lemma F_7ea58 : fetch_word Ubsan.M.loaded_segments (0x7ea58 : word) = Some W_7ea58.
Proof. vm_refl. Qed.
Lemma D_7ea58 : decode_any W_7ea58 = Some (Branch BC_NE 20 31 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea5c : bv 32 := 0x000f8f9b.
Lemma F_7ea5c : fetch_word Ubsan.M.loaded_segments (0x7ea5c : word) = Some W_7ea5c.
Proof. vm_refl. Qed.
Lemma D_7ea5c : decode_any W_7ea5c = Some (OpImm32 31 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea60 : bv 32 := 0x00060a1b.
Lemma F_7ea60 : fetch_word Ubsan.M.loaded_segments (0x7ea60 : word) = Some W_7ea60.
Proof. vm_refl. Qed.
Lemma D_7ea60 : decode_any W_7ea60 = Some (OpImm32 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea64 : bv 32 := 0x01fa0633.
Lemma F_7ea64 : fetch_word Ubsan.M.loaded_segments (0x7ea64 : word) = Some W_7ea64.
Proof. vm_refl. Qed.
Lemma D_7ea64 : decode_any W_7ea64 = Some (Op ALU_ADD 12 20 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea68 : bv 32 := 0x01fa0fbb.
Lemma F_7ea68 : fetch_word Ubsan.M.loaded_segments (0x7ea68 : word) = Some W_7ea68.
Proof. vm_refl. Qed.
Lemma D_7ea68 : decode_any W_7ea68 = Some (Op32 ALU_ADD 31 20 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea6c : bv 32 := 0x10cf9e63.
Lemma F_7ea6c : fetch_word Ubsan.M.loaded_segments (0x7ea6c : word) = Some W_7ea6c.
Proof. vm_refl. Qed.
Lemma D_7ea6c : decode_any W_7ea6c = Some (Branch BC_NE 31 12 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea70 : bv 32 := 0x00a78fb3.
Lemma F_7ea70 : fetch_word Ubsan.M.loaded_segments (0x7ea70 : word) = Some W_7ea70.
Proof. vm_refl. Qed.
Lemma D_7ea70 : decode_any W_7ea70 = Some (Op ALU_ADD 31 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea74 : bv 32 := 0x001fba13.
Lemma F_7ea74 : fetch_word Ubsan.M.loaded_segments (0x7ea74 : word) = Some W_7ea74.
Proof. vm_refl. Qed.
Lemma D_7ea74 : decode_any W_7ea74 = Some (OpImm ALU_SLTU 20 31 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea78 : bv 32 := 0x114f0863.
Lemma F_7ea78 : fetch_word Ubsan.M.loaded_segments (0x7ea78 : word) = Some W_7ea78.
Proof. vm_refl. Qed.
Lemma D_7ea78 : decode_any W_7ea78 = Some (Branch BC_EQ 30 20 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea7c : bv 32 := 0x0009af13.
Lemma F_7ea7c : fetch_word Ubsan.M.loaded_segments (0x7ea7c : word) = Some W_7ea7c.
Proof. vm_refl. Qed.
Lemma D_7ea7c : decode_any W_7ea7c = Some (OpImm ALU_SLT 30 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea80 : bv 32 := 0x00afb533.
Lemma F_7ea80 : fetch_word Ubsan.M.loaded_segments (0x7ea80 : word) = Some W_7ea80.
Proof. vm_refl. Qed.
Lemma D_7ea80 : decode_any W_7ea80 = Some (Op ALU_SLTU 10 31 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea84 : bv 32 := 0x01e54533.
Lemma F_7ea84 : fetch_word Ubsan.M.loaded_segments (0x7ea84 : word) = Some W_7ea84.
Proof. vm_refl. Qed.
Lemma D_7ea84 : decode_any W_7ea84 = Some (Op ALU_XOR 10 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea88 : bv 32 := 0x00154513.
Lemma F_7ea88 : fetch_word Ubsan.M.loaded_segments (0x7ea88 : word) = Some W_7ea88.
Proof. vm_refl. Qed.
Lemma D_7ea88 : decode_any W_7ea88 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea8c : bv 32 := 0x0e050e63.
Lemma F_7ea8c : fetch_word Ubsan.M.loaded_segments (0x7ea8c : word) = Some W_7ea8c.
Proof. vm_refl. Qed.
Lemma D_7ea8c : decode_any W_7ea8c = Some (Branch BC_EQ 10 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea90 : bv 32 := 0x0016869b.
Lemma F_7ea90 : fetch_word Ubsan.M.loaded_segments (0x7ea90 : word) = Some W_7ea90.
Proof. vm_refl. Qed.
Lemma D_7ea90 : decode_any W_7ea90 = Some (OpImm32 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea94 : bv 32 := 0x00fe8eb3.
Lemma F_7ea94 : fetch_word Ubsan.M.loaded_segments (0x7ea94 : word) = Some W_7ea94.
Proof. vm_refl. Qed.
Lemma D_7ea94 : decode_any W_7ea94 = Some (Op ALU_ADD 29 29 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea98 : bv 32 := 0x000f8513.
Lemma F_7ea98 : fetch_word Ubsan.M.loaded_segments (0x7ea98 : word) = Some W_7ea98.
Proof. vm_refl. Qed.
Lemma D_7ea98 : decode_any W_7ea98 = Some (OpImm ALU_ADD 10 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ea9c : bv 32 := 0xdeb694e3.
Lemma F_7ea9c : fetch_word Ubsan.M.loaded_segments (0x7ea9c : word) = Some W_7ea9c.
Proof. vm_refl. Qed.
Lemma D_7ea9c : decode_any W_7ea9c = Some (Branch BC_NE 13 11 7656, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eaa0 : bv 32 := 0x00c4a023.
Lemma F_7eaa0 : fetch_word Ubsan.M.loaded_segments (0x7eaa0 : word) = Some W_7eaa0.
Proof. vm_refl. Qed.
Lemma D_7eaa0 : decode_any W_7eaa0 = Some (Store SZ4 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eaa4 : bv 32 := 0x0c040c63.
Lemma F_7eaa4 : fetch_word Ubsan.M.loaded_segments (0x7eaa4 : word) = Some W_7eaa4.
Proof. vm_refl. Qed.
Lemma D_7eaa4 : decode_any W_7eaa4 = Some (Branch BC_EQ 8 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eaa8 : bv 32 := 0x00000513.
Lemma F_7eaa8 : fetch_word Ubsan.M.loaded_segments (0x7eaa8 : word) = Some W_7eaa8.
Proof. vm_refl. Qed.
Lemma D_7eaa8 : decode_any W_7eaa8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eaac : bv 32 := 0x0900006f.
Lemma F_7eaac : fetch_word Ubsan.M.loaded_segments (0x7eaac : word) = Some W_7eaac.
Proof. vm_refl. Qed.
Lemma D_7eaac : decode_any W_7eaac = Some (Jal 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eab0 : bv 32 := 0x000a8517.
Lemma F_7eab0 : fetch_word Ubsan.M.loaded_segments (0x7eab0 : word) = Some W_7eab0.
Proof. vm_refl. Qed.
Lemma D_7eab0 : decode_any W_7eab0 = Some (Auipc 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eab4 : bv 32 := 0xfc053503.
Lemma F_7eab4 : fetch_word Ubsan.M.loaded_segments (0x7eab4 : word) = Some W_7eab4.
Proof. vm_refl. Qed.
Lemma D_7eab4 : decode_any W_7eab4 = Some (Load SZ8 true 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eab8 : bv 32 := 0x00052503.
Lemma F_7eab8 : fetch_word Ubsan.M.loaded_segments (0x7eab8 : word) = Some W_7eab8.
Proof. vm_refl. Qed.
Lemma D_7eab8 : decode_any W_7eab8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eabc : bv 32 := 0x00500593.
Lemma F_7eabc : fetch_word Ubsan.M.loaded_segments (0x7eabc : word) = Some W_7eabc.
Proof. vm_refl. Qed.
Lemma D_7eabc : decode_any W_7eabc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eac0 : bv 32 := 0x06a5cc63.
Lemma F_7eac0 : fetch_word Ubsan.M.loaded_segments (0x7eac0 : word) = Some W_7eac0.
Proof. vm_refl. Qed.
Lemma D_7eac0 : decode_any W_7eac0 = Some (Branch BC_LT 11 10 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eac4 : bv 32 := 0xfff93517.
Lemma F_7eac4 : fetch_word Ubsan.M.loaded_segments (0x7eac4 : word) = Some W_7eac4.
Proof. vm_refl. Qed.
Lemma D_7eac4 : decode_any W_7eac4 = Some (Auipc 10 1048467, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eac8 : bv 32 := 0xfff97597.
Lemma F_7eac8 : fetch_word Ubsan.M.loaded_segments (0x7eac8 : word) = Some W_7eac8.
Proof. vm_refl. Qed.
Lemma D_7eac8 : decode_any W_7eac8 = Some (Auipc 11 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eacc : bv 32 := 0xdd950513.
Lemma F_7eacc : fetch_word Ubsan.M.loaded_segments (0x7eacc : word) = Some W_7eacc.
Proof. vm_refl. Qed.
Lemma D_7eacc : decode_any W_7eacc = Some (OpImm ALU_ADD 10 10 3545, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ead0 : bv 32 := 0x7d658593.
Lemma F_7ead0 : fetch_word Ubsan.M.loaded_segments (0x7ead0 : word) = Some W_7ead0.
Proof. vm_refl. Qed.
Lemma D_7ead0 : decode_any W_7ead0 = Some (OpImm ALU_ADD 11 11 2006, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ead4 : bv 32 := 0x0280006f.
Lemma F_7ead4 : fetch_word Ubsan.M.loaded_segments (0x7ead4 : word) = Some W_7ead4.
Proof. vm_refl. Qed.
Lemma D_7ead4 : decode_any W_7ead4 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ead8 : bv 32 := 0x000a8517.
Lemma F_7ead8 : fetch_word Ubsan.M.loaded_segments (0x7ead8 : word) = Some W_7ead8.
Proof. vm_refl. Qed.
Lemma D_7ead8 : decode_any W_7ead8 = Some (Auipc 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eadc : bv 32 := 0xf9853503.
Lemma F_7eadc : fetch_word Ubsan.M.loaded_segments (0x7eadc : word) = Some W_7eadc.
Proof. vm_refl. Qed.
Lemma D_7eadc : decode_any W_7eadc = Some (Load SZ8 true 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eae0 : bv 32 := 0x00052503.
Lemma F_7eae0 : fetch_word Ubsan.M.loaded_segments (0x7eae0 : word) = Some W_7eae0.
Proof. vm_refl. Qed.
Lemma D_7eae0 : decode_any W_7eae0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eae4 : bv 32 := 0x00500593.
Lemma F_7eae4 : fetch_word Ubsan.M.loaded_segments (0x7eae4 : word) = Some W_7eae4.
Proof. vm_refl. Qed.
Lemma D_7eae4 : decode_any W_7eae4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eae8 : bv 32 := 0x04a5c863.
Lemma F_7eae8 : fetch_word Ubsan.M.loaded_segments (0x7eae8 : word) = Some W_7eae8.
Proof. vm_refl. Qed.
Lemma D_7eae8 : decode_any W_7eae8 = Some (Branch BC_LT 11 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eaec : bv 32 := 0xfff92517.
Lemma F_7eaec : fetch_word Ubsan.M.loaded_segments (0x7eaec : word) = Some W_7eaec.
Proof. vm_refl. Qed.
Lemma D_7eaec : decode_any W_7eaec = Some (Auipc 10 1048466, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eaf0 : bv 32 := 0xfff97597.
Lemma F_7eaf0 : fetch_word Ubsan.M.loaded_segments (0x7eaf0 : word) = Some W_7eaf0.
Proof. vm_refl. Qed.
Lemma D_7eaf0 : decode_any W_7eaf0 = Some (Auipc 11 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eaf4 : bv 32 := 0x58c50513.
Lemma F_7eaf4 : fetch_word Ubsan.M.loaded_segments (0x7eaf4 : word) = Some W_7eaf4.
Proof. vm_refl. Qed.
Lemma D_7eaf4 : decode_any W_7eaf4 = Some (OpImm ALU_ADD 10 10 1420, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eaf8 : bv 32 := 0x7ae58593.
Lemma F_7eaf8 : fetch_word Ubsan.M.loaded_segments (0x7eaf8 : word) = Some W_7eaf8.
Proof. vm_refl. Qed.
Lemma D_7eaf8 : decode_any W_7eaf8 = Some (OpImm ALU_ADD 11 11 1966, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eafc : bv 32 := 0x00100613.
Lemma F_7eafc : fetch_word Ubsan.M.loaded_segments (0x7eafc : word) = Some W_7eafc.
Proof. vm_refl. Qed.
Lemma D_7eafc : decode_any W_7eafc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb00 : bv 32 := 0x06813083.
Lemma F_7eb00 : fetch_word Ubsan.M.loaded_segments (0x7eb00 : word) = Some W_7eb00.
Proof. vm_refl. Qed.
Lemma D_7eb00 : decode_any W_7eb00 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb04 : bv 32 := 0x06013403.
Lemma F_7eb04 : fetch_word Ubsan.M.loaded_segments (0x7eb04 : word) = Some W_7eb04.
Proof. vm_refl. Qed.
Lemma D_7eb04 : decode_any W_7eb04 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb08 : bv 32 := 0x05813483.
Lemma F_7eb08 : fetch_word Ubsan.M.loaded_segments (0x7eb08 : word) = Some W_7eb08.
Proof. vm_refl. Qed.
Lemma D_7eb08 : decode_any W_7eb08 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb0c : bv 32 := 0x05013903.
Lemma F_7eb0c : fetch_word Ubsan.M.loaded_segments (0x7eb0c : word) = Some W_7eb0c.
Proof. vm_refl. Qed.
Lemma D_7eb0c : decode_any W_7eb0c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb10 : bv 32 := 0x04813983.
Lemma F_7eb10 : fetch_word Ubsan.M.loaded_segments (0x7eb10 : word) = Some W_7eb10.
Proof. vm_refl. Qed.
Lemma D_7eb10 : decode_any W_7eb10 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb14 : bv 32 := 0x04013a03.
Lemma F_7eb14 : fetch_word Ubsan.M.loaded_segments (0x7eb14 : word) = Some W_7eb14.
Proof. vm_refl. Qed.
Lemma D_7eb14 : decode_any W_7eb14 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb18 : bv 32 := 0x03813a83.
Lemma F_7eb18 : fetch_word Ubsan.M.loaded_segments (0x7eb18 : word) = Some W_7eb18.
Proof. vm_refl. Qed.
Lemma D_7eb18 : decode_any W_7eb18 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb1c : bv 32 := 0x03013b03.
Lemma F_7eb1c : fetch_word Ubsan.M.loaded_segments (0x7eb1c : word) = Some W_7eb1c.
Proof. vm_refl. Qed.
Lemma D_7eb1c : decode_any W_7eb1c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb20 : bv 32 := 0x02813b83.
Lemma F_7eb20 : fetch_word Ubsan.M.loaded_segments (0x7eb20 : word) = Some W_7eb20.
Proof. vm_refl. Qed.
Lemma D_7eb20 : decode_any W_7eb20 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb24 : bv 32 := 0x02013c03.
Lemma F_7eb24 : fetch_word Ubsan.M.loaded_segments (0x7eb24 : word) = Some W_7eb24.
Proof. vm_refl. Qed.
Lemma D_7eb24 : decode_any W_7eb24 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb28 : bv 32 := 0x01813c83.
Lemma F_7eb28 : fetch_word Ubsan.M.loaded_segments (0x7eb28 : word) = Some W_7eb28.
Proof. vm_refl. Qed.
Lemma D_7eb28 : decode_any W_7eb28 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb2c : bv 32 := 0x01013d03.
Lemma F_7eb2c : fetch_word Ubsan.M.loaded_segments (0x7eb2c : word) = Some W_7eb2c.
Proof. vm_refl. Qed.
Lemma D_7eb2c : decode_any W_7eb2c = Some (Load SZ8 true 26 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb30 : bv 32 := 0x07010113.
Lemma F_7eb30 : fetch_word Ubsan.M.loaded_segments (0x7eb30 : word) = Some W_7eb30.
Proof. vm_refl. Qed.
Lemma D_7eb30 : decode_any W_7eb30 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb34 : bv 32 := 0xb3de406f.
Lemma F_7eb34 : fetch_word Ubsan.M.loaded_segments (0x7eb34 : word) = Some W_7eb34.
Proof. vm_refl. Qed.
Lemma D_7eb34 : decode_any W_7eb34 = Some (Jal 0 1985340, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb38 : bv 32 := 0x00100513.
Lemma F_7eb38 : fetch_word Ubsan.M.loaded_segments (0x7eb38 : word) = Some W_7eb38.
Proof. vm_refl. Qed.
Lemma D_7eb38 : decode_any W_7eb38 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb3c : bv 32 := 0x06813083.
Lemma F_7eb3c : fetch_word Ubsan.M.loaded_segments (0x7eb3c : word) = Some W_7eb3c.
Proof. vm_refl. Qed.
Lemma D_7eb3c : decode_any W_7eb3c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb40 : bv 32 := 0x06013403.
Lemma F_7eb40 : fetch_word Ubsan.M.loaded_segments (0x7eb40 : word) = Some W_7eb40.
Proof. vm_refl. Qed.
Lemma D_7eb40 : decode_any W_7eb40 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb44 : bv 32 := 0x05813483.
Lemma F_7eb44 : fetch_word Ubsan.M.loaded_segments (0x7eb44 : word) = Some W_7eb44.
Proof. vm_refl. Qed.
Lemma D_7eb44 : decode_any W_7eb44 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb48 : bv 32 := 0x05013903.
Lemma F_7eb48 : fetch_word Ubsan.M.loaded_segments (0x7eb48 : word) = Some W_7eb48.
Proof. vm_refl. Qed.
Lemma D_7eb48 : decode_any W_7eb48 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb4c : bv 32 := 0x04813983.
Lemma F_7eb4c : fetch_word Ubsan.M.loaded_segments (0x7eb4c : word) = Some W_7eb4c.
Proof. vm_refl. Qed.
Lemma D_7eb4c : decode_any W_7eb4c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb50 : bv 32 := 0x04013a03.
Lemma F_7eb50 : fetch_word Ubsan.M.loaded_segments (0x7eb50 : word) = Some W_7eb50.
Proof. vm_refl. Qed.
Lemma D_7eb50 : decode_any W_7eb50 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb54 : bv 32 := 0x03813a83.
Lemma F_7eb54 : fetch_word Ubsan.M.loaded_segments (0x7eb54 : word) = Some W_7eb54.
Proof. vm_refl. Qed.
Lemma D_7eb54 : decode_any W_7eb54 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb58 : bv 32 := 0x03013b03.
Lemma F_7eb58 : fetch_word Ubsan.M.loaded_segments (0x7eb58 : word) = Some W_7eb58.
Proof. vm_refl. Qed.
Lemma D_7eb58 : decode_any W_7eb58 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb5c : bv 32 := 0x02813b83.
Lemma F_7eb5c : fetch_word Ubsan.M.loaded_segments (0x7eb5c : word) = Some W_7eb5c.
Proof. vm_refl. Qed.
Lemma D_7eb5c : decode_any W_7eb5c = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb60 : bv 32 := 0x02013c03.
Lemma F_7eb60 : fetch_word Ubsan.M.loaded_segments (0x7eb60 : word) = Some W_7eb60.
Proof. vm_refl. Qed.
Lemma D_7eb60 : decode_any W_7eb60 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb64 : bv 32 := 0x01813c83.
Lemma F_7eb64 : fetch_word Ubsan.M.loaded_segments (0x7eb64 : word) = Some W_7eb64.
Proof. vm_refl. Qed.
Lemma D_7eb64 : decode_any W_7eb64 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb68 : bv 32 := 0x01013d03.
Lemma F_7eb68 : fetch_word Ubsan.M.loaded_segments (0x7eb68 : word) = Some W_7eb68.
Proof. vm_refl. Qed.
Lemma D_7eb68 : decode_any W_7eb68 = Some (Load SZ8 true 26 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb6c : bv 32 := 0x07010113.
Lemma F_7eb6c : fetch_word Ubsan.M.loaded_segments (0x7eb6c : word) = Some W_7eb6c.
Proof. vm_refl. Qed.
Lemma D_7eb6c : decode_any W_7eb6c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb70 : bv 32 := 0x00008067.
Lemma F_7eb70 : fetch_word Ubsan.M.loaded_segments (0x7eb70 : word) = Some W_7eb70.
Proof. vm_refl. Qed.
Lemma D_7eb70 : decode_any W_7eb70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb74 : bv 32 := 0x0004a023.
Lemma F_7eb74 : fetch_word Ubsan.M.loaded_segments (0x7eb74 : word) = Some W_7eb74.
Proof. vm_refl. Qed.
Lemma D_7eb74 : decode_any W_7eb74 = Some (Store SZ4 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb78 : bv 32 := 0xf20418e3.
Lemma F_7eb78 : fetch_word Ubsan.M.loaded_segments (0x7eb78 : word) = Some W_7eb78.
Proof. vm_refl. Qed.
Lemma D_7eb78 : decode_any W_7eb78 = Some (Branch BC_NE 8 0 7984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb7c : bv 32 := 0x00090513.
Lemma F_7eb7c : fetch_word Ubsan.M.loaded_segments (0x7eb7c : word) = Some W_7eb7c.
Proof. vm_refl. Qed.
Lemma D_7eb7c : decode_any W_7eb7c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb80 : bv 32 := 0x4998f0ef.
Lemma F_7eb80 : fetch_word Ubsan.M.loaded_segments (0x7eb80 : word) = Some W_7eb80.
Proof. vm_refl. Qed.
Lemma D_7eb80 : decode_any W_7eb80 = Some (Jal 1 588952, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb84 : bv 32 := 0xf25ff06f.
Lemma F_7eb84 : fetch_word Ubsan.M.loaded_segments (0x7eb84 : word) = Some W_7eb84.
Proof. vm_refl. Qed.
Lemma D_7eb84 : decode_any W_7eb84 = Some (Jal 0 2096932, 4%Z).
Proof. vm_refl. Qed.
