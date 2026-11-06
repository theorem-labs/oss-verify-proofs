(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8e628 : bv 32 := 0xfd010113.
Lemma F_8e628 : fetch_word AsanUbsan.M.loaded_segments (0x8e678 : word) = Some W_8e628.
Proof. vm_refl. Qed.
Lemma D_8e628 : decode_any W_8e628 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e62c : bv 32 := 0x02113423.
Lemma F_8e62c : fetch_word AsanUbsan.M.loaded_segments (0x8e67c : word) = Some W_8e62c.
Proof. vm_refl. Qed.
Lemma D_8e62c : decode_any W_8e62c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e630 : bv 32 := 0x02813023.
Lemma F_8e630 : fetch_word AsanUbsan.M.loaded_segments (0x8e680 : word) = Some W_8e630.
Proof. vm_refl. Qed.
Lemma D_8e630 : decode_any W_8e630 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e634 : bv 32 := 0x00913c23.
Lemma F_8e634 : fetch_word AsanUbsan.M.loaded_segments (0x8e684 : word) = Some W_8e634.
Proof. vm_refl. Qed.
Lemma D_8e634 : decode_any W_8e634 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e638 : bv 32 := 0x01213823.
Lemma F_8e638 : fetch_word AsanUbsan.M.loaded_segments (0x8e688 : word) = Some W_8e638.
Proof. vm_refl. Qed.
Lemma D_8e638 : decode_any W_8e638 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e63c : bv 32 := 0x02050e63.
Lemma F_8e63c : fetch_word AsanUbsan.M.loaded_segments (0x8e68c : word) = Some W_8e63c.
Proof. vm_refl. Qed.
Lemma D_8e63c : decode_any W_8e63c = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e640 : bv 32 := 0x00058413.
Lemma F_8e640 : fetch_word AsanUbsan.M.loaded_segments (0x8e690 : word) = Some W_8e640.
Proof. vm_refl. Qed.
Lemma D_8e640 : decode_any W_8e640 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e644 : bv 32 := 0x02058a63.
Lemma F_8e644 : fetch_word AsanUbsan.M.loaded_segments (0x8e694 : word) = Some W_8e644.
Proof. vm_refl. Qed.
Lemma D_8e644 : decode_any W_8e644 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e648 : bv 32 := 0x00060493.
Lemma F_8e648 : fetch_word AsanUbsan.M.loaded_segments (0x8e698 : word) = Some W_8e648.
Proof. vm_refl. Qed.
Lemma D_8e648 : decode_any W_8e648 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e64c : bv 32 := 0x00050913.
Lemma F_8e64c : fetch_word AsanUbsan.M.loaded_segments (0x8e69c : word) = Some W_8e64c.
Proof. vm_refl. Qed.
Lemma D_8e64c : decode_any W_8e64c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e650 : bv 32 := 0x00040593.
Lemma F_8e650 : fetch_word AsanUbsan.M.loaded_segments (0x8e6a0 : word) = Some W_8e650.
Proof. vm_refl. Qed.
Lemma D_8e650 : decode_any W_8e650 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e654 : bv 32 := 0xf90fe0ef.
Lemma F_8e654 : fetch_word AsanUbsan.M.loaded_segments (0x8e6a4 : word) = Some W_8e654.
Proof. vm_refl. Qed.
Lemma D_8e654 : decode_any W_8e654 = Some (Jal 1 2090896, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e658 : bv 32 := 0xaaaab5b7.
Lemma F_8e658 : fetch_word AsanUbsan.M.loaded_segments (0x8e6a8 : word) = Some W_8e658.
Proof. vm_refl. Qed.
Lemma D_8e658 : decode_any W_8e658 = Some (Lui 11 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e65c : bv 32 := 0xaaa58593.
Lemma F_8e65c : fetch_word AsanUbsan.M.loaded_segments (0x8e6ac : word) = Some W_8e65c.
Proof. vm_refl. Qed.
Lemma D_8e65c : decode_any W_8e65c = Some (OpImm ALU_ADD 11 11 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e660 : bv 32 := 0x00b12623.
Lemma F_8e660 : fetch_word AsanUbsan.M.loaded_segments (0x8e6b0 : word) = Some W_8e660.
Proof. vm_refl. Qed.
Lemma D_8e660 : decode_any W_8e660 = Some (Store SZ4 2 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e664 : bv 32 := 0x00c10593.
Lemma F_8e664 : fetch_word AsanUbsan.M.loaded_segments (0x8e6b4 : word) = Some W_8e664.
Proof. vm_refl. Qed.
Lemma D_8e664 : decode_any W_8e664 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e668 : bv 32 := 0xf50fe0ef.
Lemma F_8e668 : fetch_word AsanUbsan.M.loaded_segments (0x8e6b8 : word) = Some W_8e668.
Proof. vm_refl. Qed.
Lemma D_8e668 : decode_any W_8e668 = Some (Jal 1 2090832, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e66c : bv 32 := 0x02051263.
Lemma F_8e66c : fetch_word AsanUbsan.M.loaded_segments (0x8e6bc : word) = Some W_8e66c.
Proof. vm_refl. Qed.
Lemma D_8e66c : decode_any W_8e66c = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e670 : bv 32 := 0x00040513.
Lemma F_8e670 : fetch_word AsanUbsan.M.loaded_segments (0x8e6c0 : word) = Some W_8e670.
Proof. vm_refl. Qed.
Lemma D_8e670 : decode_any W_8e670 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e674 : bv 32 := 0xe70fa0ef.
Lemma F_8e674 : fetch_word AsanUbsan.M.loaded_segments (0x8e6c4 : word) = Some W_8e674.
Proof. vm_refl. Qed.
Lemma D_8e674 : decode_any W_8e674 = Some (Jal 1 2074224, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e678 : bv 32 := 0x02813083.
Lemma F_8e678 : fetch_word AsanUbsan.M.loaded_segments (0x8e6c8 : word) = Some W_8e678.
Proof. vm_refl. Qed.
Lemma D_8e678 : decode_any W_8e678 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e67c : bv 32 := 0x02013403.
Lemma F_8e67c : fetch_word AsanUbsan.M.loaded_segments (0x8e6cc : word) = Some W_8e67c.
Proof. vm_refl. Qed.
Lemma D_8e67c : decode_any W_8e67c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e680 : bv 32 := 0x01813483.
Lemma F_8e680 : fetch_word AsanUbsan.M.loaded_segments (0x8e6d0 : word) = Some W_8e680.
Proof. vm_refl. Qed.
Lemma D_8e680 : decode_any W_8e680 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e684 : bv 32 := 0x01013903.
Lemma F_8e684 : fetch_word AsanUbsan.M.loaded_segments (0x8e6d4 : word) = Some W_8e684.
Proof. vm_refl. Qed.
Lemma D_8e684 : decode_any W_8e684 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e688 : bv 32 := 0x03010113.
Lemma F_8e688 : fetch_word AsanUbsan.M.loaded_segments (0x8e6d8 : word) = Some W_8e688.
Proof. vm_refl. Qed.
Lemma D_8e688 : decode_any W_8e688 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e68c : bv 32 := 0x00008067.
Lemma F_8e68c : fetch_word AsanUbsan.M.loaded_segments (0x8e6dc : word) = Some W_8e68c.
Proof. vm_refl. Qed.
Lemma D_8e68c : decode_any W_8e68c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6a4 : bv 32 := 0xfd010113.
Lemma F_8e6a4 : fetch_word AsanUbsan.M.loaded_segments (0x8e6f4 : word) = Some W_8e6a4.
Proof. vm_refl. Qed.
Lemma D_8e6a4 : decode_any W_8e6a4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6a8 : bv 32 := 0x02113423.
Lemma F_8e6a8 : fetch_word AsanUbsan.M.loaded_segments (0x8e6f8 : word) = Some W_8e6a8.
Proof. vm_refl. Qed.
Lemma D_8e6a8 : decode_any W_8e6a8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6ac : bv 32 := 0x02813023.
Lemma F_8e6ac : fetch_word AsanUbsan.M.loaded_segments (0x8e6fc : word) = Some W_8e6ac.
Proof. vm_refl. Qed.
Lemma D_8e6ac : decode_any W_8e6ac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6b0 : bv 32 := 0x00913c23.
Lemma F_8e6b0 : fetch_word AsanUbsan.M.loaded_segments (0x8e700 : word) = Some W_8e6b0.
Proof. vm_refl. Qed.
Lemma D_8e6b0 : decode_any W_8e6b0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6b4 : bv 32 := 0x01213823.
Lemma F_8e6b4 : fetch_word AsanUbsan.M.loaded_segments (0x8e704 : word) = Some W_8e6b4.
Proof. vm_refl. Qed.
Lemma D_8e6b4 : decode_any W_8e6b4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6b8 : bv 32 := 0x00058413.
Lemma F_8e6b8 : fetch_word AsanUbsan.M.loaded_segments (0x8e708 : word) = Some W_8e6b8.
Proof. vm_refl. Qed.
Lemma D_8e6b8 : decode_any W_8e6b8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6bc : bv 32 := 0x000af597.
Lemma F_8e6bc : fetch_word AsanUbsan.M.loaded_segments (0x8e70c : word) = Some W_8e6bc.
Proof. vm_refl. Qed.
Lemma D_8e6bc : decode_any W_8e6bc = Some (Auipc 11 175, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6c0 : bv 32 := 0x19c5b903.
Lemma F_8e6c0 : fetch_word AsanUbsan.M.loaded_segments (0x8e710 : word) = Some W_8e6c0.
Proof. vm_refl. Qed.
Lemma D_8e6c0 : decode_any W_8e6c0 = Some (Load SZ8 true 18 11 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6c4 : bv 32 := 0x00093583.
Lemma F_8e6c4 : fetch_word AsanUbsan.M.loaded_segments (0x8e714 : word) = Some W_8e6c4.
Proof. vm_refl. Qed.
Lemma D_8e6c4 : decode_any W_8e6c4 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6c8 : bv 32 := 0x00050493.
Lemma F_8e6c8 : fetch_word AsanUbsan.M.loaded_segments (0x8e718 : word) = Some W_8e6c8.
Proof. vm_refl. Qed.
Lemma D_8e6c8 : decode_any W_8e6c8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6cc : bv 32 := 0x00059863.
Lemma F_8e6cc : fetch_word AsanUbsan.M.loaded_segments (0x8e71c : word) = Some W_8e6cc.
Proof. vm_refl. Qed.
Lemma D_8e6cc : decode_any W_8e6cc = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6dc : bv 32 := 0xfff58513.
Lemma F_8e6dc : fetch_word AsanUbsan.M.loaded_segments (0x8e72c : word) = Some W_8e6dc.
Proof. vm_refl. Qed.
Lemma D_8e6dc : decode_any W_8e6dc = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6e0 : bv 32 := 0x00a5f533.
Lemma F_8e6e0 : fetch_word AsanUbsan.M.loaded_segments (0x8e730 : word) = Some W_8e6e0.
Proof. vm_refl. Qed.
Lemma D_8e6e0 : decode_any W_8e6e0 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6e4 : bv 32 := 0x08051a63.
Lemma F_8e6e4 : fetch_word AsanUbsan.M.loaded_segments (0x8e734 : word) = Some W_8e6e4.
Proof. vm_refl. Qed.
Lemma D_8e6e4 : decode_any W_8e6e4 = Some (Branch BC_NE 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6e8 : bv 32 := 0x00b484b3.
Lemma F_8e6e8 : fetch_word AsanUbsan.M.loaded_segments (0x8e738 : word) = Some W_8e6e8.
Proof. vm_refl. Qed.
Lemma D_8e6e8 : decode_any W_8e6e8 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6ec : bv 32 := 0x40b00533.
Lemma F_8e6ec : fetch_word AsanUbsan.M.loaded_segments (0x8e73c : word) = Some W_8e6ec.
Proof. vm_refl. Qed.
Lemma D_8e6ec : decode_any W_8e6ec = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6f0 : bv 32 := 0xfff48493.
Lemma F_8e6f0 : fetch_word AsanUbsan.M.loaded_segments (0x8e740 : word) = Some W_8e6f0.
Proof. vm_refl. Qed.
Lemma D_8e6f0 : decode_any W_8e6f0 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6f4 : bv 32 := 0x00a4f4b3.
Lemma F_8e6f4 : fetch_word AsanUbsan.M.loaded_segments (0x8e744 : word) = Some W_8e6f4.
Proof. vm_refl. Qed.
Lemma D_8e6f4 : decode_any W_8e6f4 = Some (Op ALU_AND 9 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6f8 : bv 32 := 0x02200513.
Lemma F_8e6f8 : fetch_word AsanUbsan.M.loaded_segments (0x8e748 : word) = Some W_8e6f8.
Proof. vm_refl. Qed.
Lemma D_8e6f8 : decode_any W_8e6f8 = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e6fc : bv 32 := 0x00a12623.
Lemma F_8e6fc : fetch_word AsanUbsan.M.loaded_segments (0x8e74c : word) = Some W_8e6fc.
Proof. vm_refl. Qed.
Lemma D_8e6fc : decode_any W_8e6fc = Some (Store SZ4 2 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e700 : bv 32 := 0x00c10613.
Lemma F_8e700 : fetch_word AsanUbsan.M.loaded_segments (0x8e750 : word) = Some W_8e700.
Proof. vm_refl. Qed.
Lemma D_8e700 : decode_any W_8e700 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e704 : bv 32 := 0x00040513.
Lemma F_8e704 : fetch_word AsanUbsan.M.loaded_segments (0x8e754 : word) = Some W_8e704.
Proof. vm_refl. Qed.
Lemma D_8e704 : decode_any W_8e704 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e708 : bv 32 := 0x00048593.
Lemma F_8e708 : fetch_word AsanUbsan.M.loaded_segments (0x8e758 : word) = Some W_8e708.
Proof. vm_refl. Qed.
Lemma D_8e708 : decode_any W_8e708 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e70c : bv 32 := 0x279000ef.
Lemma F_8e70c : fetch_word AsanUbsan.M.loaded_segments (0x8e75c : word) = Some W_8e70c.
Proof. vm_refl. Qed.
Lemma D_8e70c : decode_any W_8e70c = Some (Jal 1 2680, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e710 : bv 32 := 0x00c12683.
Lemma F_8e710 : fetch_word AsanUbsan.M.loaded_segments (0x8e760 : word) = Some W_8e710.
Proof. vm_refl. Qed.
Lemma D_8e710 : decode_any W_8e710 = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e714 : bv 32 := 0x00050713.
Lemma F_8e714 : fetch_word AsanUbsan.M.loaded_segments (0x8e764 : word) = Some W_8e714.
Proof. vm_refl. Qed.
Lemma D_8e714 : decode_any W_8e714 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e718 : bv 32 := 0x00300613.
Lemma F_8e718 : fetch_word AsanUbsan.M.loaded_segments (0x8e768 : word) = Some W_8e718.
Proof. vm_refl. Qed.
Lemma D_8e718 : decode_any W_8e718 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e71c : bv 32 := 0x00000513.
Lemma F_8e71c : fetch_word AsanUbsan.M.loaded_segments (0x8e76c : word) = Some W_8e71c.
Proof. vm_refl. Qed.
Lemma D_8e71c : decode_any W_8e71c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e720 : bv 32 := 0x00048593.
Lemma F_8e720 : fetch_word AsanUbsan.M.loaded_segments (0x8e770 : word) = Some W_8e720.
Proof. vm_refl. Qed.
Lemma D_8e720 : decode_any W_8e720 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e724 : bv 32 := 0x00000793.
Lemma F_8e724 : fetch_word AsanUbsan.M.loaded_segments (0x8e774 : word) = Some W_8e724.
Proof. vm_refl. Qed.
Lemma D_8e724 : decode_any W_8e724 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e728 : bv 32 := 0xeb0fe0ef.
Lemma F_8e728 : fetch_word AsanUbsan.M.loaded_segments (0x8e778 : word) = Some W_8e728.
Proof. vm_refl. Qed.
Lemma D_8e728 : decode_any W_8e728 = Some (Jal 1 2090672, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e72c : bv 32 := 0x00050913.
Lemma F_8e72c : fetch_word AsanUbsan.M.loaded_segments (0x8e77c : word) = Some W_8e72c.
Proof. vm_refl. Qed.
Lemma D_8e72c : decode_any W_8e72c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e730 : bv 32 := 0x00000593.
Lemma F_8e730 : fetch_word AsanUbsan.M.loaded_segments (0x8e780 : word) = Some W_8e730.
Proof. vm_refl. Qed.
Lemma D_8e730 : decode_any W_8e730 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e734 : bv 32 := 0xe84fe0ef.
Lemma F_8e734 : fetch_word AsanUbsan.M.loaded_segments (0x8e784 : word) = Some W_8e734.
Proof. vm_refl. Qed.
Lemma D_8e734 : decode_any W_8e734 = Some (Jal 1 2090628, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e738 : bv 32 := 0xaaaab537.
Lemma F_8e738 : fetch_word AsanUbsan.M.loaded_segments (0x8e788 : word) = Some W_8e738.
Proof. vm_refl. Qed.
Lemma D_8e738 : decode_any W_8e738 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e73c : bv 32 := 0xaaa50513.
Lemma F_8e73c : fetch_word AsanUbsan.M.loaded_segments (0x8e78c : word) = Some W_8e73c.
Proof. vm_refl. Qed.
Lemma D_8e73c : decode_any W_8e73c = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e740 : bv 32 := 0x00a12423.
Lemma F_8e740 : fetch_word AsanUbsan.M.loaded_segments (0x8e790 : word) = Some W_8e740.
Proof. vm_refl. Qed.
Lemma D_8e740 : decode_any W_8e740 = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e744 : bv 32 := 0x00810593.
Lemma F_8e744 : fetch_word AsanUbsan.M.loaded_segments (0x8e794 : word) = Some W_8e744.
Proof. vm_refl. Qed.
Lemma D_8e744 : decode_any W_8e744 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e748 : bv 32 := 0x00090513.
Lemma F_8e748 : fetch_word AsanUbsan.M.loaded_segments (0x8e798 : word) = Some W_8e748.
Proof. vm_refl. Qed.
Lemma D_8e748 : decode_any W_8e748 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e74c : bv 32 := 0xe6cfe0ef.
Lemma F_8e74c : fetch_word AsanUbsan.M.loaded_segments (0x8e79c : word) = Some W_8e74c.
Proof. vm_refl. Qed.
Lemma D_8e74c : decode_any W_8e74c = Some (Jal 1 2090604, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e750 : bv 32 := 0x02051c63.
Lemma F_8e750 : fetch_word AsanUbsan.M.loaded_segments (0x8e7a0 : word) = Some W_8e750.
Proof. vm_refl. Qed.
Lemma D_8e750 : decode_any W_8e750 = Some (Branch BC_NE 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e754 : bv 32 := 0x00048513.
Lemma F_8e754 : fetch_word AsanUbsan.M.loaded_segments (0x8e7a4 : word) = Some W_8e754.
Proof. vm_refl. Qed.
Lemma D_8e754 : decode_any W_8e754 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e758 : bv 32 := 0xd48fa0ef.
Lemma F_8e758 : fetch_word AsanUbsan.M.loaded_segments (0x8e7a8 : word) = Some W_8e758.
Proof. vm_refl. Qed.
Lemma D_8e758 : decode_any W_8e758 = Some (Jal 1 2073928, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e75c : bv 32 := 0x00090513.
Lemma F_8e75c : fetch_word AsanUbsan.M.loaded_segments (0x8e7ac : word) = Some W_8e75c.
Proof. vm_refl. Qed.
Lemma D_8e75c : decode_any W_8e75c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e760 : bv 32 := 0x02813083.
Lemma F_8e760 : fetch_word AsanUbsan.M.loaded_segments (0x8e7b0 : word) = Some W_8e760.
Proof. vm_refl. Qed.
Lemma D_8e760 : decode_any W_8e760 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e764 : bv 32 := 0x02013403.
Lemma F_8e764 : fetch_word AsanUbsan.M.loaded_segments (0x8e7b4 : word) = Some W_8e764.
Proof. vm_refl. Qed.
Lemma D_8e764 : decode_any W_8e764 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e768 : bv 32 := 0x01813483.
Lemma F_8e768 : fetch_word AsanUbsan.M.loaded_segments (0x8e7b8 : word) = Some W_8e768.
Proof. vm_refl. Qed.
Lemma D_8e768 : decode_any W_8e768 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e76c : bv 32 := 0x01013903.
Lemma F_8e76c : fetch_word AsanUbsan.M.loaded_segments (0x8e7bc : word) = Some W_8e76c.
Proof. vm_refl. Qed.
Lemma D_8e76c : decode_any W_8e76c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e770 : bv 32 := 0x03010113.
Lemma F_8e770 : fetch_word AsanUbsan.M.loaded_segments (0x8e7c0 : word) = Some W_8e770.
Proof. vm_refl. Qed.
Lemma D_8e770 : decode_any W_8e770 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e774 : bv 32 := 0x00008067.
Lemma F_8e774 : fetch_word AsanUbsan.M.loaded_segments (0x8e7c4 : word) = Some W_8e774.
Proof. vm_refl. Qed.
Lemma D_8e774 : decode_any W_8e774 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
