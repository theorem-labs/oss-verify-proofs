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

Definition W_5e7a0 : bv 32 := 0xf7010113.
Lemma F_5e7a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e7f0 : word) = Some W_5e7a0.
Proof. vm_refl. Qed.
Lemma D_5e7a0 : decode_any W_5e7a0 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a4 : bv 32 := 0x08113423.
Lemma F_5e7a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e7f4 : word) = Some W_5e7a4.
Proof. vm_refl. Qed.
Lemma D_5e7a4 : decode_any W_5e7a4 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7a8 : bv 32 := 0x08813023.
Lemma F_5e7a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e7f8 : word) = Some W_5e7a8.
Proof. vm_refl. Qed.
Lemma D_5e7a8 : decode_any W_5e7a8 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7ac : bv 32 := 0x06913c23.
Lemma F_5e7ac : fetch_word AsanUbsan.M.loaded_segments (0x5e7fc : word) = Some W_5e7ac.
Proof. vm_refl. Qed.
Lemma D_5e7ac : decode_any W_5e7ac = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b0 : bv 32 := 0x07213823.
Lemma F_5e7b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e800 : word) = Some W_5e7b0.
Proof. vm_refl. Qed.
Lemma D_5e7b0 : decode_any W_5e7b0 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b4 : bv 32 := 0x07313423.
Lemma F_5e7b4 : fetch_word AsanUbsan.M.loaded_segments (0x5e804 : word) = Some W_5e7b4.
Proof. vm_refl. Qed.
Lemma D_5e7b4 : decode_any W_5e7b4 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7b8 : bv 32 := 0x07413023.
Lemma F_5e7b8 : fetch_word AsanUbsan.M.loaded_segments (0x5e808 : word) = Some W_5e7b8.
Proof. vm_refl. Qed.
Lemma D_5e7b8 : decode_any W_5e7b8 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7bc : bv 32 := 0x05513c23.
Lemma F_5e7bc : fetch_word AsanUbsan.M.loaded_segments (0x5e80c : word) = Some W_5e7bc.
Proof. vm_refl. Qed.
Lemma D_5e7bc : decode_any W_5e7bc = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c0 : bv 32 := 0x05613823.
Lemma F_5e7c0 : fetch_word AsanUbsan.M.loaded_segments (0x5e810 : word) = Some W_5e7c0.
Proof. vm_refl. Qed.
Lemma D_5e7c0 : decode_any W_5e7c0 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c4 : bv 32 := 0x05713423.
Lemma F_5e7c4 : fetch_word AsanUbsan.M.loaded_segments (0x5e814 : word) = Some W_5e7c4.
Proof. vm_refl. Qed.
Lemma D_5e7c4 : decode_any W_5e7c4 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7c8 : bv 32 := 0x05813023.
Lemma F_5e7c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e818 : word) = Some W_5e7c8.
Proof. vm_refl. Qed.
Lemma D_5e7c8 : decode_any W_5e7c8 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7cc : bv 32 := 0x03913c23.
Lemma F_5e7cc : fetch_word AsanUbsan.M.loaded_segments (0x5e81c : word) = Some W_5e7cc.
Proof. vm_refl. Qed.
Lemma D_5e7cc : decode_any W_5e7cc = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d0 : bv 32 := 0x03a13823.
Lemma F_5e7d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e820 : word) = Some W_5e7d0.
Proof. vm_refl. Qed.
Lemma D_5e7d0 : decode_any W_5e7d0 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d4 : bv 32 := 0x03b13423.
Lemma F_5e7d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e824 : word) = Some W_5e7d4.
Proof. vm_refl. Qed.
Lemma D_5e7d4 : decode_any W_5e7d4 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7d8 : bv 32 := 0x00058493.
Lemma F_5e7d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e828 : word) = Some W_5e7d8.
Proof. vm_refl. Qed.
Lemma D_5e7d8 : decode_any W_5e7d8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7dc : bv 32 := 0x00050c93.
Lemma F_5e7dc : fetch_word AsanUbsan.M.loaded_segments (0x5e82c : word) = Some W_5e7dc.
Proof. vm_refl. Qed.
Lemma D_5e7dc : decode_any W_5e7dc = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e0 : bv 32 := 0x260260ef.
Lemma F_5e7e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e830 : word) = Some W_5e7e0.
Proof. vm_refl. Qed.
Lemma D_5e7e0 : decode_any W_5e7e0 = Some (Jal 1 156256, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e4 : bv 32 := 0x26050463.
Lemma F_5e7e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e834 : word) = Some W_5e7e4.
Proof. vm_refl. Qed.
Lemma D_5e7e4 : decode_any W_5e7e4 = Some (Branch BC_EQ 10 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7e8 : bv 32 := 0x00050913.
Lemma F_5e7e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e838 : word) = Some W_5e7e8.
Proof. vm_refl. Qed.
Lemma D_5e7e8 : decode_any W_5e7e8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7ec : bv 32 := 0x418260ef.
Lemma F_5e7ec : fetch_word AsanUbsan.M.loaded_segments (0x5e83c : word) = Some W_5e7ec.
Proof. vm_refl. Qed.
Lemma D_5e7ec : decode_any W_5e7ec = Some (Jal 1 156696, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f0 : bv 32 := 0x00050993.
Lemma F_5e7f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e840 : word) = Some W_5e7f0.
Proof. vm_refl. Qed.
Lemma D_5e7f0 : decode_any W_5e7f0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f4 : bv 32 := 0x00090513.
Lemma F_5e7f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e844 : word) = Some W_5e7f4.
Proof. vm_refl. Qed.
Lemma D_5e7f4 : decode_any W_5e7f4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7f8 : bv 32 := 0x464260ef.
Lemma F_5e7f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e848 : word) = Some W_5e7f8.
Proof. vm_refl. Qed.
Lemma D_5e7f8 : decode_any W_5e7f8 = Some (Jal 1 156772, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e7fc : bv 32 := 0x2499e863.
Lemma F_5e7fc : fetch_word AsanUbsan.M.loaded_segments (0x5e84c : word) = Some W_5e7fc.
Proof. vm_refl. Qed.
Lemma D_5e7fc : decode_any W_5e7fc = Some (Branch BC_LTU 19 9 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e800 : bv 32 := 0x00050913.
Lemma F_5e800 : fetch_word AsanUbsan.M.loaded_segments (0x5e850 : word) = Some W_5e800.
Proof. vm_refl. Qed.
Lemma D_5e800 : decode_any W_5e800 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e804 : bv 32 := 0x24a4e463.
Lemma F_5e804 : fetch_word AsanUbsan.M.loaded_segments (0x5e854 : word) = Some W_5e804.
Proof. vm_refl. Qed.
Lemma D_5e804 : decode_any W_5e804 = Some (Branch BC_LTU 9 10 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e808 : bv 32 := 0x00000d13.
Lemma F_5e808 : fetch_word AsanUbsan.M.loaded_segments (0x5e858 : word) = Some W_5e808.
Proof. vm_refl. Qed.
Lemma D_5e808 : decode_any W_5e808 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e80c : bv 32 := 0x00001437.
Lemma F_5e80c : fetch_word AsanUbsan.M.loaded_segments (0x5e85c : word) = Some W_5e80c.
Proof. vm_refl. Qed.
Lemma D_5e80c : decode_any W_5e80c = Some (Lui 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e810 : bv 32 := 0x000df517.
Lemma F_5e810 : fetch_word AsanUbsan.M.loaded_segments (0x5e860 : word) = Some W_5e810.
Proof. vm_refl. Qed.
Lemma D_5e810 : decode_any W_5e810 = Some (Auipc 10 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e814 : bv 32 := 0x000df597.
Lemma F_5e814 : fetch_word AsanUbsan.M.loaded_segments (0x5e864 : word) = Some W_5e814.
Proof. vm_refl. Qed.
Lemma D_5e814 : decode_any W_5e814 = Some (Auipc 11 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e818 : bv 32 := 0x000df617.
Lemma F_5e818 : fetch_word AsanUbsan.M.loaded_segments (0x5e868 : word) = Some W_5e818.
Proof. vm_refl. Qed.
Lemma D_5e818 : decode_any W_5e818 = Some (Auipc 12 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e81c : bv 32 := 0x000df697.
Lemma F_5e81c : fetch_word AsanUbsan.M.loaded_segments (0x5e86c : word) = Some W_5e81c.
Proof. vm_refl. Qed.
Lemma D_5e81c : decode_any W_5e81c = Some (Auipc 13 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e820 : bv 32 := 0x000df717.
Lemma F_5e820 : fetch_word AsanUbsan.M.loaded_segments (0x5e870 : word) = Some W_5e820.
Proof. vm_refl. Qed.
Lemma D_5e820 : decode_any W_5e820 = Some (Auipc 14 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e824 : bv 32 := 0xfffb2797.
Lemma F_5e824 : fetch_word AsanUbsan.M.loaded_segments (0x5e874 : word) = Some W_5e824.
Proof. vm_refl. Qed.
Lemma D_5e824 : decode_any W_5e824 = Some (Auipc 15 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e828 : bv 32 := 0x008c8433.
Lemma F_5e828 : fetch_word AsanUbsan.M.loaded_segments (0x5e878 : word) = Some W_5e828.
Proof. vm_refl. Qed.
Lemma D_5e828 : decode_any W_5e828 = Some (Op ALU_ADD 8 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e82c : bv 32 := 0x06853b03.
Lemma F_5e82c : fetch_word AsanUbsan.M.loaded_segments (0x5e87c : word) = Some W_5e82c.
Proof. vm_refl. Qed.
Lemma D_5e82c : decode_any W_5e82c = Some (Load SZ8 true 22 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e830 : bv 32 := 0x06c5b503.
Lemma F_5e830 : fetch_word AsanUbsan.M.loaded_segments (0x5e880 : word) = Some W_5e830.
Proof. vm_refl. Qed.
Lemma D_5e830 : decode_any W_5e830 = Some (Load SZ8 true 10 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e834 : bv 32 := 0x00a13c23.
Lemma F_5e834 : fetch_word AsanUbsan.M.loaded_segments (0x5e884 : word) = Some W_5e834.
Proof. vm_refl. Qed.
Lemma D_5e834 : decode_any W_5e834 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e838 : bv 32 := 0x07063503.
Lemma F_5e838 : fetch_word AsanUbsan.M.loaded_segments (0x5e888 : word) = Some W_5e838.
Proof. vm_refl. Qed.
Lemma D_5e838 : decode_any W_5e838 = Some (Load SZ8 true 10 12 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e83c : bv 32 := 0x00a13823.
Lemma F_5e83c : fetch_word AsanUbsan.M.loaded_segments (0x5e88c : word) = Some W_5e83c.
Proof. vm_refl. Qed.
Lemma D_5e83c : decode_any W_5e83c = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e840 : bv 32 := 0x0746b503.
Lemma F_5e840 : fetch_word AsanUbsan.M.loaded_segments (0x5e890 : word) = Some W_5e840.
Proof. vm_refl. Qed.
Lemma D_5e840 : decode_any W_5e840 = Some (Load SZ8 true 10 13 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e844 : bv 32 := 0x00a13423.
Lemma F_5e844 : fetch_word AsanUbsan.M.loaded_segments (0x5e894 : word) = Some W_5e844.
Proof. vm_refl. Qed.
Lemma D_5e844 : decode_any W_5e844 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e848 : bv 32 := 0x05073503.
Lemma F_5e848 : fetch_word AsanUbsan.M.loaded_segments (0x5e898 : word) = Some W_5e848.
Proof. vm_refl. Qed.
Lemma D_5e848 : decode_any W_5e848 = Some (Load SZ8 true 10 14 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e84c : bv 32 := 0x00a13023.
Lemma F_5e84c : fetch_word AsanUbsan.M.loaded_segments (0x5e89c : word) = Some W_5e84c.
Proof. vm_refl. Qed.
Lemma D_5e84c : decode_any W_5e84c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e850 : bv 32 := 0xb247bb83.
Lemma F_5e850 : fetch_word AsanUbsan.M.loaded_segments (0x5e8a0 : word) = Some W_5e850.
Proof. vm_refl. Qed.
Lemma D_5e850 : decode_any W_5e850 = Some (Load SZ8 true 23 15 2852, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e854 : bv 32 := 0x00100393.
Lemma F_5e854 : fetch_word AsanUbsan.M.loaded_segments (0x5e8a4 : word) = Some W_5e854.
Proof. vm_refl. Qed.
Lemma D_5e854 : decode_any W_5e854 = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e858 : bv 32 := 0x00600e13.
Lemma F_5e858 : fetch_word AsanUbsan.M.loaded_segments (0x5e8a8 : word) = Some W_5e858.
Proof. vm_refl. Qed.
Lemma D_5e858 : decode_any W_5e858 = Some (OpImm ALU_ADD 28 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e85c : bv 32 := 0x00000a13.
Lemma F_5e85c : fetch_word AsanUbsan.M.loaded_segments (0x5e8ac : word) = Some W_5e85c.
Proof. vm_refl. Qed.
Lemma D_5e85c : decode_any W_5e85c = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e860 : bv 32 := 0x0100006f.
Lemma F_5e860 : fetch_word AsanUbsan.M.loaded_segments (0x5e8b0 : word) = Some W_5e860.
Proof. vm_refl. Qed.
Lemma D_5e860 : decode_any W_5e860 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e864 : bv 32 := 0x001a0a13.
Lemma F_5e864 : fetch_word AsanUbsan.M.loaded_segments (0x5e8b4 : word) = Some W_5e864.
Proof. vm_refl. Qed.
Lemma D_5e864 : decode_any W_5e864 = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e868 : bv 32 := 0x00b00513.
Lemma F_5e868 : fetch_word AsanUbsan.M.loaded_segments (0x5e8b8 : word) = Some W_5e868.
Proof. vm_refl. Qed.
Lemma D_5e868 : decode_any W_5e868 = Some (OpImm ALU_ADD 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e86c : bv 32 := 0x1caa0e63.
Lemma F_5e86c : fetch_word AsanUbsan.M.loaded_segments (0x5e8bc : word) = Some W_5e86c.
Proof. vm_refl. Qed.
Lemma D_5e86c : decode_any W_5e86c = Some (Branch BC_EQ 20 10 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e870 : bv 32 := 0x00000d93.
Lemma F_5e870 : fetch_word AsanUbsan.M.loaded_segments (0x5e8c0 : word) = Some W_5e870.
Proof. vm_refl. Qed.
Lemma D_5e870 : decode_any W_5e870 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e874 : bv 32 := 0x058cb503.
Lemma F_5e874 : fetch_word AsanUbsan.M.loaded_segments (0x5e8c4 : word) = Some W_5e874.
Proof. vm_refl. Qed.
Lemma D_5e874 : decode_any W_5e874 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e878 : bv 32 := 0x00a00593.
Lemma F_5e878 : fetch_word AsanUbsan.M.loaded_segments (0x5e8c8 : word) = Some W_5e878.
Proof. vm_refl. Qed.
Lemma D_5e878 : decode_any W_5e878 = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e87c : bv 32 := 0x414585bb.
Lemma F_5e87c : fetch_word AsanUbsan.M.loaded_segments (0x5e8cc : word) = Some W_5e87c.
Proof. vm_refl. Qed.
Lemma D_5e87c : decode_any W_5e87c = Some (Op32 ALU_SUB 11 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e880 : bv 32 := 0x006a0a93.
Lemma F_5e880 : fetch_word AsanUbsan.M.loaded_segments (0x5e8d0 : word) = Some W_5e880.
Proof. vm_refl. Qed.
Lemma D_5e880 : decode_any W_5e880 = Some (OpImm ALU_ADD 21 20 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e884 : bv 32 := 0xfff00613.
Lemma F_5e884 : fetch_word AsanUbsan.M.loaded_segments (0x5e8d4 : word) = Some W_5e884.
Proof. vm_refl. Qed.
Lemma D_5e884 : decode_any W_5e884 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e888 : bv 32 := 0x00b615b3.
Lemma F_5e888 : fetch_word AsanUbsan.M.loaded_segments (0x5e8d8 : word) = Some W_5e888.
Proof. vm_refl. Qed.
Lemma D_5e888 : decode_any W_5e888 = Some (Op ALU_SLL 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e88c : bv 32 := 0x3ff5f593.
Lemma F_5e88c : fetch_word AsanUbsan.M.loaded_segments (0x5e8dc : word) = Some W_5e88c.
Proof. vm_refl. Qed.
Lemma D_5e88c : decode_any W_5e88c = Some (OpImm ALU_AND 11 11 1023, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e890 : bv 32 := 0xff150613.
Lemma F_5e890 : fetch_word AsanUbsan.M.loaded_segments (0x5e8e0 : word) = Some W_5e890.
Proof. vm_refl. Qed.
Lemma D_5e890 : decode_any W_5e890 = Some (OpImm ALU_ADD 12 10 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e894 : bv 32 := 0x414509b3.
Lemma F_5e894 : fetch_word AsanUbsan.M.loaded_segments (0x5e8e4 : word) = Some W_5e894.
Proof. vm_refl. Qed.
Lemma D_5e894 : decode_any W_5e894 = Some (Op ALU_SUB 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e898 : bv 32 := 0x00c59c33.
Lemma F_5e898 : fetch_word AsanUbsan.M.loaded_segments (0x5e8e8 : word) = Some W_5e898.
Proof. vm_refl. Qed.
Lemma D_5e898 : decode_any W_5e898 = Some (Op ALU_SLL 24 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e89c : bv 32 := 0xffa98993.
Lemma F_5e89c : fetch_word AsanUbsan.M.loaded_segments (0x5e8ec : word) = Some W_5e89c.
Proof. vm_refl. Qed.
Lemma D_5e89c : decode_any W_5e89c = Some (OpImm ALU_ADD 19 19 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a0 : bv 32 := 0x01840c33.
Lemma F_5e8a0 : fetch_word AsanUbsan.M.loaded_segments (0x5e8f0 : word) = Some W_5e8a0.
Proof. vm_refl. Qed.
Lemma D_5e8a0 : decode_any W_5e8a0 = Some (Op ALU_ADD 24 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a4 : bv 32 := 0x04000513.
Lemma F_5e8a4 : fetch_word AsanUbsan.M.loaded_segments (0x5e8f4 : word) = Some W_5e8a4.
Proof. vm_refl. Qed.
Lemma D_5e8a4 : decode_any W_5e8a4 = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8a8 : bv 32 := 0x01451533.
Lemma F_5e8a8 : fetch_word AsanUbsan.M.loaded_segments (0x5e8f8 : word) = Some W_5e8a8.
Proof. vm_refl. Qed.
Lemma D_5e8a8 : decode_any W_5e8a8 = Some (Op ALU_SLL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8ac : bv 32 := 0x02a13023.
Lemma F_5e8ac : fetch_word AsanUbsan.M.loaded_segments (0x5e8fc : word) = Some W_5e8ac.
Proof. vm_refl. Qed.
Lemma D_5e8ac : decode_any W_5e8ac = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8b0 : bv 32 := 0x0240006f.
Lemma F_5e8b0 : fetch_word AsanUbsan.M.loaded_segments (0x5e900 : word) = Some W_5e8b0.
Proof. vm_refl. Qed.
Lemma D_5e8b0 : decode_any W_5e8b0 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8c8 : bv 32 := 0x001d8d93.
Lemma F_5e8c8 : fetch_word AsanUbsan.M.loaded_segments (0x5e918 : word) = Some W_5e8c8.
Proof. vm_refl. Qed.
Lemma D_5e8c8 : decode_any W_5e8c8 = Some (OpImm ALU_ADD 27 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8cc : bv 32 := 0x013dd533.
Lemma F_5e8cc : fetch_word AsanUbsan.M.loaded_segments (0x5e91c : word) = Some W_5e8cc.
Proof. vm_refl. Qed.
Lemma D_5e8cc : decode_any W_5e8cc = Some (Op ALU_SRL 10 27 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d0 : bv 32 := 0xf8051ae3.
Lemma F_5e8d0 : fetch_word AsanUbsan.M.loaded_segments (0x5e920 : word) = Some W_5e8d0.
Proof. vm_refl. Qed.
Lemma D_5e8d0 : decode_any W_5e8d0 = Some (Branch BC_NE 10 0 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d4 : bv 32 := 0x01bc05b3.
Lemma F_5e8d4 : fetch_word AsanUbsan.M.loaded_segments (0x5e924 : word) = Some W_5e8d4.
Proof. vm_refl. Qed.
Lemma D_5e8d4 : decode_any W_5e8d4 = Some (Op ALU_ADD 11 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8d8 : bv 32 := 0x0005c503.
Lemma F_5e8d8 : fetch_word AsanUbsan.M.loaded_segments (0x5e928 : word) = Some W_5e8d8.
Proof. vm_refl. Qed.
Lemma D_5e8d8 : decode_any W_5e8d8 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8dc : bv 32 := 0xfe0506e3.
Lemma F_5e8dc : fetch_word AsanUbsan.M.loaded_segments (0x5e92c : word) = Some W_5e8dc.
Proof. vm_refl. Qed.
Lemma D_5e8dc : decode_any W_5e8dc = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e0 : bv 32 := 0x058cb503.
Lemma F_5e8e0 : fetch_word AsanUbsan.M.loaded_segments (0x5e930 : word) = Some W_5e8e0.
Proof. vm_refl. Qed.
Lemma D_5e8e0 : decode_any W_5e8e0 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e4 : bv 32 := 0xffb50613.
Lemma F_5e8e4 : fetch_word AsanUbsan.M.loaded_segments (0x5e934 : word) = Some W_5e8e4.
Proof. vm_refl. Qed.
Lemma D_5e8e4 : decode_any W_5e8e4 = Some (OpImm ALU_ADD 12 10 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8e8 : bv 32 := 0x00aa1533.
Lemma F_5e8e8 : fetch_word AsanUbsan.M.loaded_segments (0x5e938 : word) = Some W_5e8e8.
Proof. vm_refl. Qed.
Lemma D_5e8e8 : decode_any W_5e8e8 = Some (Op ALU_SLL 10 20 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8ec : bv 32 := 0x00c39633.
Lemma F_5e8ec : fetch_word AsanUbsan.M.loaded_segments (0x5e93c : word) = Some W_5e8ec.
Proof. vm_refl. Qed.
Lemma D_5e8ec : decode_any W_5e8ec = Some (Op ALU_SLL 12 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f0 : bv 32 := 0x00a40533.
Lemma F_5e8f0 : fetch_word AsanUbsan.M.loaded_segments (0x5e940 : word) = Some W_5e8f0.
Proof. vm_refl. Qed.
Lemma D_5e8f0 : decode_any W_5e8f0 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f4 : bv 32 := 0x00c50533.
Lemma F_5e8f4 : fetch_word AsanUbsan.M.loaded_segments (0x5e944 : word) = Some W_5e8f4.
Proof. vm_refl. Qed.
Lemma D_5e8f4 : decode_any W_5e8f4 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8f8 : bv 32 := 0x015d9633.
Lemma F_5e8f8 : fetch_word AsanUbsan.M.loaded_segments (0x5e948 : word) = Some W_5e8f8.
Proof. vm_refl. Qed.
Lemma D_5e8f8 : decode_any W_5e8f8 = Some (Op ALU_SLL 12 27 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e8fc : bv 32 := 0x00c50533.
Lemma F_5e8fc : fetch_word AsanUbsan.M.loaded_segments (0x5e94c : word) = Some W_5e8fc.
Proof. vm_refl. Qed.
Lemma D_5e8fc : decode_any W_5e8fc = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e900 : bv 32 := 0x01853603.
Lemma F_5e900 : fetch_word AsanUbsan.M.loaded_segments (0x5e950 : word) = Some W_5e900.
Proof. vm_refl. Qed.
Lemma D_5e900 : decode_any W_5e900 = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e904 : bv 32 := 0xfcc972e3.
Lemma F_5e904 : fetch_word AsanUbsan.M.loaded_segments (0x5e954 : word) = Some W_5e904.
Proof. vm_refl. Qed.
Lemma D_5e904 : decode_any W_5e904 = Some (Branch BC_GEU 18 12 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e908 : bv 32 := 0xfc9670e3.
Lemma F_5e908 : fetch_word AsanUbsan.M.loaded_segments (0x5e958 : word) = Some W_5e908.
Proof. vm_refl. Qed.
Lemma D_5e908 : decode_any W_5e908 = Some (Branch BC_GEU 12 9 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e90c : bv 32 := 0x01a58023.
Lemma F_5e90c : fetch_word AsanUbsan.M.loaded_segments (0x5e95c : word) = Some W_5e90c.
Proof. vm_refl. Qed.
Lemma D_5e90c : decode_any W_5e90c = Some (Store SZ1 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e910 : bv 32 := 0x000b3583.
Lemma F_5e910 : fetch_word AsanUbsan.M.loaded_segments (0x5e960 : word) = Some W_5e910.
Proof. vm_refl. Qed.
Lemma D_5e910 : decode_any W_5e910 = Some (Load SZ8 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e914 : bv 32 := 0xfff58613.
Lemma F_5e914 : fetch_word AsanUbsan.M.loaded_segments (0x5e964 : word) = Some W_5e914.
Proof. vm_refl. Qed.
Lemma D_5e914 : decode_any W_5e914 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e918 : bv 32 := 0x00c5b6b3.
Lemma F_5e918 : fetch_word AsanUbsan.M.loaded_segments (0x5e968 : word) = Some W_5e918.
Proof. vm_refl. Qed.
Lemma D_5e918 : decode_any W_5e918 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e91c : bv 32 := 0xfff68693.
Lemma F_5e91c : fetch_word AsanUbsan.M.loaded_segments (0x5e96c : word) = Some W_5e91c.
Proof. vm_refl. Qed.
Lemma D_5e91c : decode_any W_5e91c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e920 : bv 32 := 0x00c6f6b3.
Lemma F_5e920 : fetch_word AsanUbsan.M.loaded_segments (0x5e970 : word) = Some W_5e920.
Proof. vm_refl. Qed.
Lemma D_5e920 : decode_any W_5e920 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e924 : bv 32 := 0x02a6fc63.
Lemma F_5e924 : fetch_word AsanUbsan.M.loaded_segments (0x5e974 : word) = Some W_5e924.
Proof. vm_refl. Qed.
Lemma D_5e924 : decode_any W_5e924 = Some (Branch BC_GEU 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e928 : bv 32 := 0x01813683.
Lemma F_5e928 : fetch_word AsanUbsan.M.loaded_segments (0x5e978 : word) = Some W_5e928.
Proof. vm_refl. Qed.
Lemma D_5e928 : decode_any W_5e928 = Some (Load SZ8 true 13 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e92c : bv 32 := 0x0006b803.
Lemma F_5e92c : fetch_word AsanUbsan.M.loaded_segments (0x5e97c : word) = Some W_5e92c.
Proof. vm_refl. Qed.
Lemma D_5e92c : decode_any W_5e92c = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e930 : bv 32 := 0x01013683.
Lemma F_5e930 : fetch_word AsanUbsan.M.loaded_segments (0x5e980 : word) = Some W_5e930.
Proof. vm_refl. Qed.
Lemma D_5e930 : decode_any W_5e930 = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e934 : bv 32 := 0x0006b683.
Lemma F_5e934 : fetch_word AsanUbsan.M.loaded_segments (0x5e984 : word) = Some W_5e934.
Proof. vm_refl. Qed.
Lemma D_5e934 : decode_any W_5e934 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e938 : bv 32 := 0xfff80793.
Lemma F_5e938 : fetch_word AsanUbsan.M.loaded_segments (0x5e988 : word) = Some W_5e938.
Proof. vm_refl. Qed.
Lemma D_5e938 : decode_any W_5e938 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e93c : bv 32 := 0x00a7f463.
Lemma F_5e93c : fetch_word AsanUbsan.M.loaded_segments (0x5e98c : word) = Some W_5e93c.
Proof. vm_refl. Qed.
Lemma D_5e93c : decode_any W_5e93c = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e944 : bv 32 := 0x00813703.
Lemma F_5e944 : fetch_word AsanUbsan.M.loaded_segments (0x5e994 : word) = Some W_5e944.
Proof. vm_refl. Qed.
Lemma D_5e944 : decode_any W_5e944 = Some (Load SZ8 true 14 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e948 : bv 32 := 0x00073283.
Lemma F_5e948 : fetch_word AsanUbsan.M.loaded_segments (0x5e998 : word) = Some W_5e948.
Proof. vm_refl. Qed.
Lemma D_5e948 : decode_any W_5e948 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e94c : bv 32 := 0x0032d713.
Lemma F_5e94c : fetch_word AsanUbsan.M.loaded_segments (0x5e99c : word) = Some W_5e94c.
Proof. vm_refl. Qed.
Lemma D_5e94c : decode_any W_5e94c = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e950 : bv 32 := 0x00b708b3.
Lemma F_5e950 : fetch_word AsanUbsan.M.loaded_segments (0x5e9a0 : word) = Some W_5e950.
Proof. vm_refl. Qed.
Lemma D_5e950 : decode_any W_5e950 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e954 : bv 32 := 0x02a2e863.
Lemma F_5e954 : fetch_word AsanUbsan.M.loaded_segments (0x5e9a4 : word) = Some W_5e954.
Proof. vm_refl. Qed.
Lemma D_5e954 : decode_any W_5e954 = Some (Branch BC_LTU 5 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e958 : bv 32 := 0x02a8f663.
Lemma F_5e958 : fetch_word AsanUbsan.M.loaded_segments (0x5e9a8 : word) = Some W_5e958.
Proof. vm_refl. Qed.
Lemma D_5e958 : decode_any W_5e958 = Some (Branch BC_GEU 17 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e95c : bv 32 := 0xf54e6ce3.
Lemma F_5e95c : fetch_word AsanUbsan.M.loaded_segments (0x5e9ac : word) = Some W_5e95c.
Proof. vm_refl. Qed.
Lemma D_5e95c : decode_any W_5e95c = Some (Branch BC_LTU 28 20 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e960 : bv 32 := 0x00355513.
Lemma F_5e960 : fetch_word AsanUbsan.M.loaded_segments (0x5e9b0 : word) = Some W_5e960.
Proof. vm_refl. Qed.
Lemma D_5e960 : decode_any W_5e960 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e964 : bv 32 := 0x00a585b3.
Lemma F_5e964 : fetch_word AsanUbsan.M.loaded_segments (0x5e9b4 : word) = Some W_5e964.
Proof. vm_refl. Qed.
Lemma D_5e964 : decode_any W_5e964 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e968 : bv 32 := 0x00100513.
Lemma F_5e968 : fetch_word AsanUbsan.M.loaded_segments (0x5e9b8 : word) = Some W_5e968.
Proof. vm_refl. Qed.
Lemma D_5e968 : decode_any W_5e968 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e96c : bv 32 := 0x0175b023.
Lemma F_5e96c : fetch_word AsanUbsan.M.loaded_segments (0x5e9bc : word) = Some W_5e96c.
Proof. vm_refl. Qed.
Lemma D_5e96c : decode_any W_5e96c = Some (Store SZ8 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e970 : bv 32 := 0x01455633.
Lemma F_5e970 : fetch_word AsanUbsan.M.loaded_segments (0x5e9c0 : word) = Some W_5e970.
Proof. vm_refl. Qed.
Lemma D_5e970 : decode_any W_5e970 = Some (Op ALU_SRL 12 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e974 : bv 32 := 0x00858593.
Lemma F_5e974 : fetch_word AsanUbsan.M.loaded_segments (0x5e9c4 : word) = Some W_5e974.
Proof. vm_refl. Qed.
Lemma D_5e974 : decode_any W_5e974 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e978 : bv 32 := 0x00150513.
Lemma F_5e978 : fetch_word AsanUbsan.M.loaded_segments (0x5e9c8 : word) = Some W_5e978.
Proof. vm_refl. Qed.
Lemma D_5e978 : decode_any W_5e978 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e97c : bv 32 := 0xfe0608e3.
Lemma F_5e97c : fetch_word AsanUbsan.M.loaded_segments (0x5e9cc : word) = Some W_5e97c.
Proof. vm_refl. Qed.
Lemma D_5e97c : decode_any W_5e97c = Some (Branch BC_EQ 12 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e980 : bv 32 := 0xf49ff06f.
Lemma F_5e980 : fetch_word AsanUbsan.M.loaded_segments (0x5e9d0 : word) = Some W_5e980.
Proof. vm_refl. Qed.
Lemma D_5e980 : decode_any W_5e980 = Some (Jal 0 2096968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea48 : bv 32 := 0x060c8023.
Lemma F_5ea48 : fetch_word AsanUbsan.M.loaded_segments (0x5ea98 : word) = Some W_5ea48.
Proof. vm_refl. Qed.
Lemma D_5ea48 : decode_any W_5ea48 = Some (Store SZ1 25 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea4c : bv 32 := 0x08813083.
Lemma F_5ea4c : fetch_word AsanUbsan.M.loaded_segments (0x5ea9c : word) = Some W_5ea4c.
Proof. vm_refl. Qed.
Lemma D_5ea4c : decode_any W_5ea4c = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea50 : bv 32 := 0x08013403.
Lemma F_5ea50 : fetch_word AsanUbsan.M.loaded_segments (0x5eaa0 : word) = Some W_5ea50.
Proof. vm_refl. Qed.
Lemma D_5ea50 : decode_any W_5ea50 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea54 : bv 32 := 0x07813483.
Lemma F_5ea54 : fetch_word AsanUbsan.M.loaded_segments (0x5eaa4 : word) = Some W_5ea54.
Proof. vm_refl. Qed.
Lemma D_5ea54 : decode_any W_5ea54 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea58 : bv 32 := 0x07013903.
Lemma F_5ea58 : fetch_word AsanUbsan.M.loaded_segments (0x5eaa8 : word) = Some W_5ea58.
Proof. vm_refl. Qed.
Lemma D_5ea58 : decode_any W_5ea58 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea5c : bv 32 := 0x06813983.
Lemma F_5ea5c : fetch_word AsanUbsan.M.loaded_segments (0x5eaac : word) = Some W_5ea5c.
Proof. vm_refl. Qed.
Lemma D_5ea5c : decode_any W_5ea5c = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea60 : bv 32 := 0x06013a03.
Lemma F_5ea60 : fetch_word AsanUbsan.M.loaded_segments (0x5eab0 : word) = Some W_5ea60.
Proof. vm_refl. Qed.
Lemma D_5ea60 : decode_any W_5ea60 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea64 : bv 32 := 0x05813a83.
Lemma F_5ea64 : fetch_word AsanUbsan.M.loaded_segments (0x5eab4 : word) = Some W_5ea64.
Proof. vm_refl. Qed.
Lemma D_5ea64 : decode_any W_5ea64 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea68 : bv 32 := 0x05013b03.
Lemma F_5ea68 : fetch_word AsanUbsan.M.loaded_segments (0x5eab8 : word) = Some W_5ea68.
Proof. vm_refl. Qed.
Lemma D_5ea68 : decode_any W_5ea68 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea6c : bv 32 := 0x04813b83.
Lemma F_5ea6c : fetch_word AsanUbsan.M.loaded_segments (0x5eabc : word) = Some W_5ea6c.
Proof. vm_refl. Qed.
Lemma D_5ea6c : decode_any W_5ea6c = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea70 : bv 32 := 0x04013c03.
Lemma F_5ea70 : fetch_word AsanUbsan.M.loaded_segments (0x5eac0 : word) = Some W_5ea70.
Proof. vm_refl. Qed.
Lemma D_5ea70 : decode_any W_5ea70 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea74 : bv 32 := 0x03813c83.
Lemma F_5ea74 : fetch_word AsanUbsan.M.loaded_segments (0x5eac4 : word) = Some W_5ea74.
Proof. vm_refl. Qed.
Lemma D_5ea74 : decode_any W_5ea74 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea78 : bv 32 := 0x03013d03.
Lemma F_5ea78 : fetch_word AsanUbsan.M.loaded_segments (0x5eac8 : word) = Some W_5ea78.
Proof. vm_refl. Qed.
Lemma D_5ea78 : decode_any W_5ea78 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea7c : bv 32 := 0x02813d83.
Lemma F_5ea7c : fetch_word AsanUbsan.M.loaded_segments (0x5eacc : word) = Some W_5ea7c.
Proof. vm_refl. Qed.
Lemma D_5ea7c : decode_any W_5ea7c = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea80 : bv 32 := 0x09010113.
Lemma F_5ea80 : fetch_word AsanUbsan.M.loaded_segments (0x5ead0 : word) = Some W_5ea80.
Proof. vm_refl. Qed.
Lemma D_5ea80 : decode_any W_5ea80 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea84 : bv 32 := 0x00008067.
Lemma F_5ea84 : fetch_word AsanUbsan.M.loaded_segments (0x5ead4 : word) = Some W_5ea84.
Proof. vm_refl. Qed.
Lemma D_5ea84 : decode_any W_5ea84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea88 : bv 32 := 0x00100593.
Lemma F_5ea88 : fetch_word AsanUbsan.M.loaded_segments (0x5ead8 : word) = Some W_5ea88.
Proof. vm_refl. Qed.
Lemma D_5ea88 : decode_any W_5ea88 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea8c : bv 32 := 0x06b50023.
Lemma F_5ea8c : fetch_word AsanUbsan.M.loaded_segments (0x5eadc : word) = Some W_5ea8c.
Proof. vm_refl. Qed.
Lemma D_5ea8c : decode_any W_5ea8c = Some (Store SZ1 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea90 : bv 32 := 0x00008067.
Lemma F_5ea90 : fetch_word AsanUbsan.M.loaded_segments (0x5eae0 : word) = Some W_5ea90.
Proof. vm_refl. Qed.
Lemma D_5ea90 : decode_any W_5ea90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed60 : bv 32 := 0xfe010113.
Lemma F_5ed60 : fetch_word AsanUbsan.M.loaded_segments (0x5edb0 : word) = Some W_5ed60.
Proof. vm_refl. Qed.
Lemma D_5ed60 : decode_any W_5ed60 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed64 : bv 32 := 0x00113c23.
Lemma F_5ed64 : fetch_word AsanUbsan.M.loaded_segments (0x5edb4 : word) = Some W_5ed64.
Proof. vm_refl. Qed.
Lemma D_5ed64 : decode_any W_5ed64 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed68 : bv 32 := 0x00813823.
Lemma F_5ed68 : fetch_word AsanUbsan.M.loaded_segments (0x5edb8 : word) = Some W_5ed68.
Proof. vm_refl. Qed.
Lemma D_5ed68 : decode_any W_5ed68 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed6c : bv 32 := 0x00913423.
Lemma F_5ed6c : fetch_word AsanUbsan.M.loaded_segments (0x5edbc : word) = Some W_5ed6c.
Proof. vm_refl. Qed.
Lemma D_5ed6c : decode_any W_5ed6c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed70 : bv 32 := 0x01213023.
Lemma F_5ed70 : fetch_word AsanUbsan.M.loaded_segments (0x5edc0 : word) = Some W_5ed70.
Proof. vm_refl. Qed.
Lemma D_5ed70 : decode_any W_5ed70 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed74 : bv 32 := 0x02010413.
Lemma F_5ed74 : fetch_word AsanUbsan.M.loaded_segments (0x5edc4 : word) = Some W_5ed74.
Proof. vm_refl. Qed.
Lemma D_5ed74 : decode_any W_5ed74 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed78 : bv 32 := 0x000e0517.
Lemma F_5ed78 : fetch_word AsanUbsan.M.loaded_segments (0x5edc8 : word) = Some W_5ed78.
Proof. vm_refl. Qed.
Lemma D_5ed78 : decode_any W_5ed78 = Some (Auipc 10 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed7c : bv 32 := 0x8f850513.
Lemma F_5ed7c : fetch_word AsanUbsan.M.loaded_segments (0x5edcc : word) = Some W_5ed7c.
Proof. vm_refl. Qed.
Lemma D_5ed7c : decode_any W_5ed7c = Some (OpImm ALU_ADD 10 10 2296, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed80 : bv 32 := 0x7cc050ef.
Lemma F_5ed80 : fetch_word AsanUbsan.M.loaded_segments (0x5edd0 : word) = Some W_5ed80.
Proof. vm_refl. Qed.
Lemma D_5ed80 : decode_any W_5ed80 = Some (Jal 1 22476, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed84 : bv 32 := 0x00053483.
Lemma F_5ed84 : fetch_word AsanUbsan.M.loaded_segments (0x5edd4 : word) = Some W_5ed84.
Proof. vm_refl. Qed.
Lemma D_5ed84 : decode_any W_5ed84 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed88 : bv 32 := 0x08048863.
Lemma F_5ed88 : fetch_word AsanUbsan.M.loaded_segments (0x5edd8 : word) = Some W_5ed88.
Proof. vm_refl. Qed.
Lemma D_5ed88 : decode_any W_5ed88 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed8c : bv 32 := 0x0604c503.
Lemma F_5ed8c : fetch_word AsanUbsan.M.loaded_segments (0x5eddc : word) = Some W_5ed8c.
Proof. vm_refl. Qed.
Lemma D_5ed8c : decode_any W_5ed8c = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed90 : bv 32 := 0x0584b903.
Lemma F_5ed90 : fetch_word AsanUbsan.M.loaded_segments (0x5ede0 : word) = Some W_5ed90.
Proof. vm_refl. Qed.
Lemma D_5ed90 : decode_any W_5ed90 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed94 : bv 32 := 0x00050863.
Lemma F_5ed94 : fetch_word AsanUbsan.M.loaded_segments (0x5ede4 : word) = Some W_5ed94.
Proof. vm_refl. Qed.
Lemma D_5ed94 : decode_any W_5ed94 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed98 : bv 32 := 0x00048513.
Lemma F_5ed98 : fetch_word AsanUbsan.M.loaded_segments (0x5ede8 : word) = Some W_5ed98.
Proof. vm_refl. Qed.
Lemma D_5ed98 : decode_any W_5ed98 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed9c : bv 32 := 0x00040593.
Lemma F_5ed9c : fetch_word AsanUbsan.M.loaded_segments (0x5edec : word) = Some W_5ed9c.
Proof. vm_refl. Qed.
Lemma D_5ed9c : decode_any W_5ed9c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eda0 : bv 32 := 0xa01ff0ef.
Lemma F_5eda0 : fetch_word AsanUbsan.M.loaded_segments (0x5edf0 : word) = Some W_5eda0.
Proof. vm_refl. Qed.
Lemma D_5eda0 : decode_any W_5eda0 = Some (Jal 1 2095616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eda4 : bv 32 := 0xff990593.
Lemma F_5eda4 : fetch_word AsanUbsan.M.loaded_segments (0x5edf4 : word) = Some W_5eda4.
Proof. vm_refl. Qed.
Lemma D_5eda4 : decode_any W_5eda4 = Some (OpImm ALU_ADD 11 18 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eda8 : bv 32 := 0x00100513.
Lemma F_5eda8 : fetch_word AsanUbsan.M.loaded_segments (0x5edf8 : word) = Some W_5eda8.
Proof. vm_refl. Qed.
Lemma D_5eda8 : decode_any W_5eda8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edac : bv 32 := 0x00b51533.
Lemma F_5edac : fetch_word AsanUbsan.M.loaded_segments (0x5edfc : word) = Some W_5edac.
Proof. vm_refl. Qed.
Lemma D_5edac : decode_any W_5edac = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edb0 : bv 32 := 0x0005061b.
Lemma F_5edb0 : fetch_word AsanUbsan.M.loaded_segments (0x5ee00 : word) = Some W_5edb0.
Proof. vm_refl. Qed.
Lemma D_5edb0 : decode_any W_5edb0 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edb4 : bv 32 := 0x08c05263.
Lemma F_5edb4 : fetch_word AsanUbsan.M.loaded_segments (0x5ee04 : word) = Some W_5edb4.
Proof. vm_refl. Qed.
Lemma D_5edb4 : decode_any W_5edb4 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edb8 : bv 32 := 0x000016b7.
Lemma F_5edb8 : fetch_word AsanUbsan.M.loaded_segments (0x5ee08 : word) = Some W_5edb8.
Proof. vm_refl. Qed.
Lemma D_5edb8 : decode_any W_5edb8 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edbc : bv 32 := 0xff190613.
Lemma F_5edbc : fetch_word AsanUbsan.M.loaded_segments (0x5ee0c : word) = Some W_5edbc.
Proof. vm_refl. Qed.
Lemma D_5edbc : decode_any W_5edbc = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edc0 : bv 32 := 0x20000713.
Lemma F_5edc0 : fetch_word AsanUbsan.M.loaded_segments (0x5ee10 : word) = Some W_5edc0.
Proof. vm_refl. Qed.
Lemma D_5edc0 : decode_any W_5edc0 = Some (OpImm ALU_ADD 14 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edc4 : bv 32 := 0xfff00793.
Lemma F_5edc4 : fetch_word AsanUbsan.M.loaded_segments (0x5ee14 : word) = Some W_5edc4.
Proof. vm_refl. Qed.
Lemma D_5edc4 : decode_any W_5edc4 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edc8 : bv 32 := 0x00c71733.
Lemma F_5edc8 : fetch_word AsanUbsan.M.loaded_segments (0x5ee18 : word) = Some W_5edc8.
Proof. vm_refl. Qed.
Lemma D_5edc8 : decode_any W_5edc8 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edcc : bv 32 := 0x0084b603.
Lemma F_5edcc : fetch_word AsanUbsan.M.loaded_segments (0x5ee1c : word) = Some W_5edcc.
Proof. vm_refl. Qed.
Lemma D_5edcc : decode_any W_5edcc = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edd0 : bv 32 := 0x00b797b3.
Lemma F_5edd0 : fetch_word AsanUbsan.M.loaded_segments (0x5ee20 : word) = Some W_5edd0.
Proof. vm_refl. Qed.
Lemma D_5edd0 : decode_any W_5edd0 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edd4 : bv 32 := 0xfff50813.
Lemma F_5edd4 : fetch_word AsanUbsan.M.loaded_segments (0x5ee24 : word) = Some W_5edd4.
Proof. vm_refl. Qed.
Lemma D_5edd4 : decode_any W_5edd4 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edd8 : bv 32 := 0x00d485b3.
Lemma F_5edd8 : fetch_word AsanUbsan.M.loaded_segments (0x5ee28 : word) = Some W_5edd8.
Proof. vm_refl. Qed.
Lemma D_5edd8 : decode_any W_5edd8 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eddc : bv 32 := 0x00e586b3.
Lemma F_5eddc : fetch_word AsanUbsan.M.loaded_segments (0x5ee2c : word) = Some W_5eddc.
Proof. vm_refl. Qed.
Lemma D_5eddc : decode_any W_5eddc = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ede0 : bv 32 := 0xfff7c713.
Lemma F_5ede0 : fetch_word AsanUbsan.M.loaded_segments (0x5ee30 : word) = Some W_5ede0.
Proof. vm_refl. Qed.
Lemma D_5ede0 : decode_any W_5ede0 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ede4 : bv 32 := 0x02081813.
Lemma F_5ede4 : fetch_word AsanUbsan.M.loaded_segments (0x5ee34 : word) = Some W_5ede4.
Proof. vm_refl. Qed.
Lemma D_5ede4 : decode_any W_5ede4 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ede8 : bv 32 := 0x02085793.
Lemma F_5ede8 : fetch_word AsanUbsan.M.loaded_segments (0x5ee38 : word) = Some W_5ede8.
Proof. vm_refl. Qed.
Lemma D_5ede8 : decode_any W_5ede8 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edec : bv 32 := 0x00f607b3.
Lemma F_5edec : fetch_word AsanUbsan.M.loaded_segments (0x5ee3c : word) = Some W_5edec.
Proof. vm_refl. Qed.
Lemma D_5edec : decode_any W_5edec = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edf0 : bv 32 := 0x00178813.
Lemma F_5edf0 : fetch_word AsanUbsan.M.loaded_segments (0x5ee40 : word) = Some W_5edf0.
Proof. vm_refl. Qed.
Lemma D_5edf0 : decode_any W_5edf0 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edf4 : bv 32 := 0x00e678b3.
Lemma F_5edf4 : fetch_word AsanUbsan.M.loaded_segments (0x5ee44 : word) = Some W_5edf4.
Proof. vm_refl. Qed.
Lemma D_5edf4 : decode_any W_5edf4 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edf8 : bv 32 := 0x011687b3.
Lemma F_5edf8 : fetch_word AsanUbsan.M.loaded_segments (0x5ee48 : word) = Some W_5edf8.
Proof. vm_refl. Qed.
Lemma D_5edf8 : decode_any W_5edf8 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5edfc : bv 32 := 0x0007c283.
Lemma F_5edfc : fetch_word AsanUbsan.M.loaded_segments (0x5ee4c : word) = Some W_5edfc.
Proof. vm_refl. Qed.
Lemma D_5edfc : decode_any W_5edfc = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee00 : bv 32 := 0x06028663.
Lemma F_5ee00 : fetch_word AsanUbsan.M.loaded_segments (0x5ee50 : word) = Some W_5ee00.
Proof. vm_refl. Qed.
Lemma D_5ee00 : decode_any W_5ee00 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee04 : bv 32 := 0xfff5051b.
Lemma F_5ee04 : fetch_word AsanUbsan.M.loaded_segments (0x5ee54 : word) = Some W_5ee04.
Proof. vm_refl. Qed.
Lemma D_5ee04 : decode_any W_5ee04 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee08 : bv 32 := 0x00160613.
Lemma F_5ee08 : fetch_word AsanUbsan.M.loaded_segments (0x5ee58 : word) = Some W_5ee08.
Proof. vm_refl. Qed.
Lemma D_5ee08 : decode_any W_5ee08 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee0c : bv 32 := 0xfe0514e3.
Lemma F_5ee0c : fetch_word AsanUbsan.M.loaded_segments (0x5ee5c : word) = Some W_5ee0c.
Proof. vm_refl. Qed.
Lemma D_5ee0c : decode_any W_5ee0c = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee6c : bv 32 := 0x00160613.
Lemma F_5ee6c : fetch_word AsanUbsan.M.loaded_segments (0x5eebc : word) = Some W_5ee6c.
Proof. vm_refl. Qed.
Lemma D_5ee6c : decode_any W_5ee6c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee70 : bv 32 := 0x00100513.
Lemma F_5ee70 : fetch_word AsanUbsan.M.loaded_segments (0x5eec0 : word) = Some W_5ee70.
Proof. vm_refl. Qed.
Lemma D_5ee70 : decode_any W_5ee70 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee74 : bv 32 := 0xffb90693.
Lemma F_5ee74 : fetch_word AsanUbsan.M.loaded_segments (0x5eec4 : word) = Some W_5ee74.
Proof. vm_refl. Qed.
Lemma D_5ee74 : decode_any W_5ee74 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee78 : bv 32 := 0x00789893.
Lemma F_5ee78 : fetch_word AsanUbsan.M.loaded_segments (0x5eec8 : word) = Some W_5ee78.
Proof. vm_refl. Qed.
Lemma D_5ee78 : decode_any W_5ee78 = Some (ShiftImm ALU_SLL 17 17 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee7c : bv 32 := 0x00c4b423.
Lemma F_5ee7c : fetch_word AsanUbsan.M.loaded_segments (0x5eecc : word) = Some W_5ee7c.
Proof. vm_refl. Qed.
Lemma D_5ee7c : decode_any W_5ee7c = Some (Store SZ8 9 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee80 : bv 32 := 0x00a78023.
Lemma F_5ee80 : fetch_word AsanUbsan.M.loaded_segments (0x5eed0 : word) = Some W_5ee80.
Proof. vm_refl. Qed.
Lemma D_5ee80 : decode_any W_5ee80 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee84 : bv 32 := 0x00d51633.
Lemma F_5ee84 : fetch_word AsanUbsan.M.loaded_segments (0x5eed4 : word) = Some W_5ee84.
Proof. vm_refl. Qed.
Lemma D_5ee84 : decode_any W_5ee84 = Some (Op ALU_SLL 12 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee88 : bv 32 := 0x01251533.
Lemma F_5ee88 : fetch_word AsanUbsan.M.loaded_segments (0x5eed8 : word) = Some W_5ee88.
Proof. vm_refl. Qed.
Lemma D_5ee88 : decode_any W_5ee88 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee8c : bv 32 := 0x00c585b3.
Lemma F_5ee8c : fetch_word AsanUbsan.M.loaded_segments (0x5eedc : word) = Some W_5ee8c.
Proof. vm_refl. Qed.
Lemma D_5ee8c : decode_any W_5ee8c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee90 : bv 32 := 0x01150533.
Lemma F_5ee90 : fetch_word AsanUbsan.M.loaded_segments (0x5eee0 : word) = Some W_5ee90.
Proof. vm_refl. Qed.
Lemma D_5ee90 : decode_any W_5ee90 = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee94 : bv 32 := 0x00a584b3.
Lemma F_5ee94 : fetch_word AsanUbsan.M.loaded_segments (0x5eee4 : word) = Some W_5ee94.
Proof. vm_refl. Qed.
Lemma D_5ee94 : decode_any W_5ee94 = Some (Op ALU_ADD 9 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee98 : bv 32 := 0x0084bc23.
Lemma F_5ee98 : fetch_word AsanUbsan.M.loaded_segments (0x5eee8 : word) = Some W_5ee98.
Proof. vm_refl. Qed.
Lemma D_5ee98 : decode_any W_5ee98 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ee9c : bv 32 := 0x06f4bc23.
Lemma F_5ee9c : fetch_word AsanUbsan.M.loaded_segments (0x5eeec : word) = Some W_5ee9c.
Proof. vm_refl. Qed.
Lemma D_5ee9c : decode_any W_5ee9c = Some (Store SZ8 9 15 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eea0 : bv 32 := 0x00048513.
Lemma F_5eea0 : fetch_word AsanUbsan.M.loaded_segments (0x5eef0 : word) = Some W_5eea0.
Proof. vm_refl. Qed.
Lemma D_5eea0 : decode_any W_5eea0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eea4 : bv 32 := 0x654000ef.
Lemma F_5eea4 : fetch_word AsanUbsan.M.loaded_segments (0x5eef4 : word) = Some W_5eea4.
Proof. vm_refl. Qed.
Lemma D_5eea4 : decode_any W_5eea4 = Some (Jal 1 1620, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eea8 : bv 32 := 0x00050593.
Lemma F_5eea8 : fetch_word AsanUbsan.M.loaded_segments (0x5eef8 : word) = Some W_5eea8.
Proof. vm_refl. Qed.
Lemma D_5eea8 : decode_any W_5eea8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eeac : bv 32 := 0x00048513.
Lemma F_5eeac : fetch_word AsanUbsan.M.loaded_segments (0x5eefc : word) = Some W_5eeac.
Proof. vm_refl. Qed.
Lemma D_5eeac : decode_any W_5eeac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eeb0 : bv 32 := 0x00000613.
Lemma F_5eeb0 : fetch_word AsanUbsan.M.loaded_segments (0x5ef00 : word) = Some W_5eeb0.
Proof. vm_refl. Qed.
Lemma D_5eeb0 : decode_any W_5eeb0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eeb4 : bv 32 := 0x0005b023.
Lemma F_5eeb4 : fetch_word AsanUbsan.M.loaded_segments (0x5ef04 : word) = Some W_5eeb4.
Proof. vm_refl. Qed.
Lemma D_5eeb4 : decode_any W_5eeb4 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eeb8 : bv 32 := 0x0005b423.
Lemma F_5eeb8 : fetch_word AsanUbsan.M.loaded_segments (0x5ef08 : word) = Some W_5eeb8.
Proof. vm_refl. Qed.
Lemma D_5eeb8 : decode_any W_5eeb8 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eebc : bv 32 := 0x01813083.
Lemma F_5eebc : fetch_word AsanUbsan.M.loaded_segments (0x5ef0c : word) = Some W_5eebc.
Proof. vm_refl. Qed.
Lemma D_5eebc : decode_any W_5eebc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eec0 : bv 32 := 0x01013403.
Lemma F_5eec0 : fetch_word AsanUbsan.M.loaded_segments (0x5ef10 : word) = Some W_5eec0.
Proof. vm_refl. Qed.
Lemma D_5eec0 : decode_any W_5eec0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eec4 : bv 32 := 0x00813483.
Lemma F_5eec4 : fetch_word AsanUbsan.M.loaded_segments (0x5ef14 : word) = Some W_5eec4.
Proof. vm_refl. Qed.
Lemma D_5eec4 : decode_any W_5eec4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eec8 : bv 32 := 0x00013903.
Lemma F_5eec8 : fetch_word AsanUbsan.M.loaded_segments (0x5ef18 : word) = Some W_5eec8.
Proof. vm_refl. Qed.
Lemma D_5eec8 : decode_any W_5eec8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eecc : bv 32 := 0x02010113.
Lemma F_5eecc : fetch_word AsanUbsan.M.loaded_segments (0x5ef1c : word) = Some W_5eecc.
Proof. vm_refl. Qed.
Lemma D_5eecc : decode_any W_5eecc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eed0 : bv 32 := 0x00008067.
Lemma F_5eed0 : fetch_word AsanUbsan.M.loaded_segments (0x5ef20 : word) = Some W_5eed0.
Proof. vm_refl. Qed.
Lemma D_5eed0 : decode_any W_5eed0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f08c : bv 32 := 0xfe010113.
Lemma F_5f08c : fetch_word AsanUbsan.M.loaded_segments (0x5f0dc : word) = Some W_5f08c.
Proof. vm_refl. Qed.
Lemma D_5f08c : decode_any W_5f08c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f090 : bv 32 := 0x00113c23.
Lemma F_5f090 : fetch_word AsanUbsan.M.loaded_segments (0x5f0e0 : word) = Some W_5f090.
Proof. vm_refl. Qed.
Lemma D_5f090 : decode_any W_5f090 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f094 : bv 32 := 0x00813823.
Lemma F_5f094 : fetch_word AsanUbsan.M.loaded_segments (0x5f0e4 : word) = Some W_5f094.
Proof. vm_refl. Qed.
Lemma D_5f094 : decode_any W_5f094 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f098 : bv 32 := 0x00913423.
Lemma F_5f098 : fetch_word AsanUbsan.M.loaded_segments (0x5f0e8 : word) = Some W_5f098.
Proof. vm_refl. Qed.
Lemma D_5f098 : decode_any W_5f098 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f09c : bv 32 := 0x01213023.
Lemma F_5f09c : fetch_word AsanUbsan.M.loaded_segments (0x5f0ec : word) = Some W_5f09c.
Proof. vm_refl. Qed.
Lemma D_5f09c : decode_any W_5f09c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0a0 : bv 32 := 0x02010413.
Lemma F_5f0a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f0f0 : word) = Some W_5f0a0.
Proof. vm_refl. Qed.
Lemma D_5f0a0 : decode_any W_5f0a0 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0a4 : bv 32 := 0x000df517.
Lemma F_5f0a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f0f4 : word) = Some W_5f0a4.
Proof. vm_refl. Qed.
Lemma D_5f0a4 : decode_any W_5f0a4 = Some (Auipc 10 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0a8 : bv 32 := 0x5cc50513.
Lemma F_5f0a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f0f8 : word) = Some W_5f0a8.
Proof. vm_refl. Qed.
Lemma D_5f0a8 : decode_any W_5f0a8 = Some (OpImm ALU_ADD 10 10 1484, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0ac : bv 32 := 0x4a0050ef.
Lemma F_5f0ac : fetch_word AsanUbsan.M.loaded_segments (0x5f0fc : word) = Some W_5f0ac.
Proof. vm_refl. Qed.
Lemma D_5f0ac : decode_any W_5f0ac = Some (Jal 1 21664, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0b0 : bv 32 := 0x00053483.
Lemma F_5f0b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f100 : word) = Some W_5f0b0.
Proof. vm_refl. Qed.
Lemma D_5f0b0 : decode_any W_5f0b0 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0b4 : bv 32 := 0x08048863.
Lemma F_5f0b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f104 : word) = Some W_5f0b4.
Proof. vm_refl. Qed.
Lemma D_5f0b4 : decode_any W_5f0b4 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0b8 : bv 32 := 0x0604c503.
Lemma F_5f0b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f108 : word) = Some W_5f0b8.
Proof. vm_refl. Qed.
Lemma D_5f0b8 : decode_any W_5f0b8 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0bc : bv 32 := 0x0584b903.
Lemma F_5f0bc : fetch_word AsanUbsan.M.loaded_segments (0x5f10c : word) = Some W_5f0bc.
Proof. vm_refl. Qed.
Lemma D_5f0bc : decode_any W_5f0bc = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0c0 : bv 32 := 0x00050863.
Lemma F_5f0c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f110 : word) = Some W_5f0c0.
Proof. vm_refl. Qed.
Lemma D_5f0c0 : decode_any W_5f0c0 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0c4 : bv 32 := 0x00048513.
Lemma F_5f0c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f114 : word) = Some W_5f0c4.
Proof. vm_refl. Qed.
Lemma D_5f0c4 : decode_any W_5f0c4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0c8 : bv 32 := 0x00040593.
Lemma F_5f0c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f118 : word) = Some W_5f0c8.
Proof. vm_refl. Qed.
Lemma D_5f0c8 : decode_any W_5f0c8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0cc : bv 32 := 0xed4ff0ef.
Lemma F_5f0cc : fetch_word AsanUbsan.M.loaded_segments (0x5f11c : word) = Some W_5f0cc.
Proof. vm_refl. Qed.
Lemma D_5f0cc : decode_any W_5f0cc = Some (Jal 1 2094804, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0d0 : bv 32 := 0xff790593.
Lemma F_5f0d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f120 : word) = Some W_5f0d0.
Proof. vm_refl. Qed.
Lemma D_5f0d0 : decode_any W_5f0d0 = Some (OpImm ALU_ADD 11 18 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0d4 : bv 32 := 0x00100513.
Lemma F_5f0d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f124 : word) = Some W_5f0d4.
Proof. vm_refl. Qed.
Lemma D_5f0d4 : decode_any W_5f0d4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0d8 : bv 32 := 0x00b51533.
Lemma F_5f0d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f128 : word) = Some W_5f0d8.
Proof. vm_refl. Qed.
Lemma D_5f0d8 : decode_any W_5f0d8 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0dc : bv 32 := 0x0005061b.
Lemma F_5f0dc : fetch_word AsanUbsan.M.loaded_segments (0x5f12c : word) = Some W_5f0dc.
Proof. vm_refl. Qed.
Lemma D_5f0dc : decode_any W_5f0dc = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0e0 : bv 32 := 0x08c05263.
Lemma F_5f0e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f130 : word) = Some W_5f0e0.
Proof. vm_refl. Qed.
Lemma D_5f0e0 : decode_any W_5f0e0 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0e4 : bv 32 := 0x000016b7.
Lemma F_5f0e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f134 : word) = Some W_5f0e4.
Proof. vm_refl. Qed.
Lemma D_5f0e4 : decode_any W_5f0e4 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0e8 : bv 32 := 0xff190613.
Lemma F_5f0e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f138 : word) = Some W_5f0e8.
Proof. vm_refl. Qed.
Lemma D_5f0e8 : decode_any W_5f0e8 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0ec : bv 32 := 0x38000713.
Lemma F_5f0ec : fetch_word AsanUbsan.M.loaded_segments (0x5f13c : word) = Some W_5f0ec.
Proof. vm_refl. Qed.
Lemma D_5f0ec : decode_any W_5f0ec = Some (OpImm ALU_ADD 14 0 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0f0 : bv 32 := 0xfff00793.
Lemma F_5f0f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f140 : word) = Some W_5f0f0.
Proof. vm_refl. Qed.
Lemma D_5f0f0 : decode_any W_5f0f0 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0f4 : bv 32 := 0x00c71733.
Lemma F_5f0f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f144 : word) = Some W_5f0f4.
Proof. vm_refl. Qed.
Lemma D_5f0f4 : decode_any W_5f0f4 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0f8 : bv 32 := 0x0184b603.
Lemma F_5f0f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f148 : word) = Some W_5f0f8.
Proof. vm_refl. Qed.
Lemma D_5f0f8 : decode_any W_5f0f8 = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f0fc : bv 32 := 0x00b797b3.
Lemma F_5f0fc : fetch_word AsanUbsan.M.loaded_segments (0x5f14c : word) = Some W_5f0fc.
Proof. vm_refl. Qed.
Lemma D_5f0fc : decode_any W_5f0fc = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f100 : bv 32 := 0xfff50813.
Lemma F_5f100 : fetch_word AsanUbsan.M.loaded_segments (0x5f150 : word) = Some W_5f100.
Proof. vm_refl. Qed.
Lemma D_5f100 : decode_any W_5f100 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f104 : bv 32 := 0x00d485b3.
Lemma F_5f104 : fetch_word AsanUbsan.M.loaded_segments (0x5f154 : word) = Some W_5f104.
Proof. vm_refl. Qed.
Lemma D_5f104 : decode_any W_5f104 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f108 : bv 32 := 0x00e586b3.
Lemma F_5f108 : fetch_word AsanUbsan.M.loaded_segments (0x5f158 : word) = Some W_5f108.
Proof. vm_refl. Qed.
Lemma D_5f108 : decode_any W_5f108 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f10c : bv 32 := 0xfff7c713.
Lemma F_5f10c : fetch_word AsanUbsan.M.loaded_segments (0x5f15c : word) = Some W_5f10c.
Proof. vm_refl. Qed.
Lemma D_5f10c : decode_any W_5f10c = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f110 : bv 32 := 0x02081813.
Lemma F_5f110 : fetch_word AsanUbsan.M.loaded_segments (0x5f160 : word) = Some W_5f110.
Proof. vm_refl. Qed.
Lemma D_5f110 : decode_any W_5f110 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f114 : bv 32 := 0x02085793.
Lemma F_5f114 : fetch_word AsanUbsan.M.loaded_segments (0x5f164 : word) = Some W_5f114.
Proof. vm_refl. Qed.
Lemma D_5f114 : decode_any W_5f114 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f118 : bv 32 := 0x00f607b3.
Lemma F_5f118 : fetch_word AsanUbsan.M.loaded_segments (0x5f168 : word) = Some W_5f118.
Proof. vm_refl. Qed.
Lemma D_5f118 : decode_any W_5f118 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f11c : bv 32 := 0x00178813.
Lemma F_5f11c : fetch_word AsanUbsan.M.loaded_segments (0x5f16c : word) = Some W_5f11c.
Proof. vm_refl. Qed.
Lemma D_5f11c : decode_any W_5f11c = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f120 : bv 32 := 0x00e678b3.
Lemma F_5f120 : fetch_word AsanUbsan.M.loaded_segments (0x5f170 : word) = Some W_5f120.
Proof. vm_refl. Qed.
Lemma D_5f120 : decode_any W_5f120 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f124 : bv 32 := 0x011687b3.
Lemma F_5f124 : fetch_word AsanUbsan.M.loaded_segments (0x5f174 : word) = Some W_5f124.
Proof. vm_refl. Qed.
Lemma D_5f124 : decode_any W_5f124 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f128 : bv 32 := 0x0007c283.
Lemma F_5f128 : fetch_word AsanUbsan.M.loaded_segments (0x5f178 : word) = Some W_5f128.
Proof. vm_refl. Qed.
Lemma D_5f128 : decode_any W_5f128 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f12c : bv 32 := 0x06028663.
Lemma F_5f12c : fetch_word AsanUbsan.M.loaded_segments (0x5f17c : word) = Some W_5f12c.
Proof. vm_refl. Qed.
Lemma D_5f12c : decode_any W_5f12c = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f130 : bv 32 := 0xfff5051b.
Lemma F_5f130 : fetch_word AsanUbsan.M.loaded_segments (0x5f180 : word) = Some W_5f130.
Proof. vm_refl. Qed.
Lemma D_5f130 : decode_any W_5f130 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f134 : bv 32 := 0x00160613.
Lemma F_5f134 : fetch_word AsanUbsan.M.loaded_segments (0x5f184 : word) = Some W_5f134.
Proof. vm_refl. Qed.
Lemma D_5f134 : decode_any W_5f134 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f138 : bv 32 := 0xfe0514e3.
Lemma F_5f138 : fetch_word AsanUbsan.M.loaded_segments (0x5f188 : word) = Some W_5f138.
Proof. vm_refl. Qed.
Lemma D_5f138 : decode_any W_5f138 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f198 : bv 32 := 0x00160613.
Lemma F_5f198 : fetch_word AsanUbsan.M.loaded_segments (0x5f1e8 : word) = Some W_5f198.
Proof. vm_refl. Qed.
Lemma D_5f198 : decode_any W_5f198 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f19c : bv 32 := 0x00100513.
Lemma F_5f19c : fetch_word AsanUbsan.M.loaded_segments (0x5f1ec : word) = Some W_5f19c.
Proof. vm_refl. Qed.
Lemma D_5f19c : decode_any W_5f19c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1a0 : bv 32 := 0xffb90693.
Lemma F_5f1a0 : fetch_word AsanUbsan.M.loaded_segments (0x5f1f0 : word) = Some W_5f1a0.
Proof. vm_refl. Qed.
Lemma D_5f1a0 : decode_any W_5f1a0 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1a4 : bv 32 := 0x00c4bc23.
Lemma F_5f1a4 : fetch_word AsanUbsan.M.loaded_segments (0x5f1f4 : word) = Some W_5f1a4.
Proof. vm_refl. Qed.
Lemma D_5f1a4 : decode_any W_5f1a4 = Some (Store SZ8 9 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1a8 : bv 32 := 0x00a78023.
Lemma F_5f1a8 : fetch_word AsanUbsan.M.loaded_segments (0x5f1f8 : word) = Some W_5f1a8.
Proof. vm_refl. Qed.
Lemma D_5f1a8 : decode_any W_5f1a8 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1ac : bv 32 := 0x00d51533.
Lemma F_5f1ac : fetch_word AsanUbsan.M.loaded_segments (0x5f1fc : word) = Some W_5f1ac.
Proof. vm_refl. Qed.
Lemma D_5f1ac : decode_any W_5f1ac = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1b0 : bv 32 := 0x00300613.
Lemma F_5f1b0 : fetch_word AsanUbsan.M.loaded_segments (0x5f200 : word) = Some W_5f1b0.
Proof. vm_refl. Qed.
Lemma D_5f1b0 : decode_any W_5f1b0 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1b4 : bv 32 := 0x00989893.
Lemma F_5f1b4 : fetch_word AsanUbsan.M.loaded_segments (0x5f204 : word) = Some W_5f1b4.
Proof. vm_refl. Qed.
Lemma D_5f1b4 : decode_any W_5f1b4 = Some (ShiftImm ALU_SLL 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1b8 : bv 32 := 0x01261633.
Lemma F_5f1b8 : fetch_word AsanUbsan.M.loaded_segments (0x5f208 : word) = Some W_5f1b8.
Proof. vm_refl. Qed.
Lemma D_5f1b8 : decode_any W_5f1b8 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1bc : bv 32 := 0x00a58533.
Lemma F_5f1bc : fetch_word AsanUbsan.M.loaded_segments (0x5f20c : word) = Some W_5f1bc.
Proof. vm_refl. Qed.
Lemma D_5f1bc : decode_any W_5f1bc = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1c0 : bv 32 := 0x01160633.
Lemma F_5f1c0 : fetch_word AsanUbsan.M.loaded_segments (0x5f210 : word) = Some W_5f1c0.
Proof. vm_refl. Qed.
Lemma D_5f1c0 : decode_any W_5f1c0 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1c4 : bv 32 := 0x00c504b3.
Lemma F_5f1c4 : fetch_word AsanUbsan.M.loaded_segments (0x5f214 : word) = Some W_5f1c4.
Proof. vm_refl. Qed.
Lemma D_5f1c4 : decode_any W_5f1c4 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1c8 : bv 32 := 0x0084bc23.
Lemma F_5f1c8 : fetch_word AsanUbsan.M.loaded_segments (0x5f218 : word) = Some W_5f1c8.
Proof. vm_refl. Qed.
Lemma D_5f1c8 : decode_any W_5f1c8 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1cc : bv 32 := 0x1ef4bc23.
Lemma F_5f1cc : fetch_word AsanUbsan.M.loaded_segments (0x5f21c : word) = Some W_5f1cc.
Proof. vm_refl. Qed.
Lemma D_5f1cc : decode_any W_5f1cc = Some (Store SZ8 9 15 504, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1d0 : bv 32 := 0x00048513.
Lemma F_5f1d0 : fetch_word AsanUbsan.M.loaded_segments (0x5f220 : word) = Some W_5f1d0.
Proof. vm_refl. Qed.
Lemma D_5f1d0 : decode_any W_5f1d0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1d4 : bv 32 := 0x324000ef.
Lemma F_5f1d4 : fetch_word AsanUbsan.M.loaded_segments (0x5f224 : word) = Some W_5f1d4.
Proof. vm_refl. Qed.
Lemma D_5f1d4 : decode_any W_5f1d4 = Some (Jal 1 804, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1d8 : bv 32 := 0x00050593.
Lemma F_5f1d8 : fetch_word AsanUbsan.M.loaded_segments (0x5f228 : word) = Some W_5f1d8.
Proof. vm_refl. Qed.
Lemma D_5f1d8 : decode_any W_5f1d8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1dc : bv 32 := 0x00048513.
Lemma F_5f1dc : fetch_word AsanUbsan.M.loaded_segments (0x5f22c : word) = Some W_5f1dc.
Proof. vm_refl. Qed.
Lemma D_5f1dc : decode_any W_5f1dc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1e0 : bv 32 := 0x00000613.
Lemma F_5f1e0 : fetch_word AsanUbsan.M.loaded_segments (0x5f230 : word) = Some W_5f1e0.
Proof. vm_refl. Qed.
Lemma D_5f1e0 : decode_any W_5f1e0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1e4 : bv 32 := 0x0005b023.
Lemma F_5f1e4 : fetch_word AsanUbsan.M.loaded_segments (0x5f234 : word) = Some W_5f1e4.
Proof. vm_refl. Qed.
Lemma D_5f1e4 : decode_any W_5f1e4 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1e8 : bv 32 := 0x0005b423.
Lemma F_5f1e8 : fetch_word AsanUbsan.M.loaded_segments (0x5f238 : word) = Some W_5f1e8.
Proof. vm_refl. Qed.
Lemma D_5f1e8 : decode_any W_5f1e8 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1ec : bv 32 := 0x0005b823.
Lemma F_5f1ec : fetch_word AsanUbsan.M.loaded_segments (0x5f23c : word) = Some W_5f1ec.
Proof. vm_refl. Qed.
Lemma D_5f1ec : decode_any W_5f1ec = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1f0 : bv 32 := 0x0005bc23.
Lemma F_5f1f0 : fetch_word AsanUbsan.M.loaded_segments (0x5f240 : word) = Some W_5f1f0.
Proof. vm_refl. Qed.
Lemma D_5f1f0 : decode_any W_5f1f0 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1f4 : bv 32 := 0x0205b023.
Lemma F_5f1f4 : fetch_word AsanUbsan.M.loaded_segments (0x5f244 : word) = Some W_5f1f4.
Proof. vm_refl. Qed.
Lemma D_5f1f4 : decode_any W_5f1f4 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1f8 : bv 32 := 0x0205b423.
Lemma F_5f1f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f248 : word) = Some W_5f1f8.
Proof. vm_refl. Qed.
Lemma D_5f1f8 : decode_any W_5f1f8 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f1fc : bv 32 := 0x0205b823.
Lemma F_5f1fc : fetch_word AsanUbsan.M.loaded_segments (0x5f24c : word) = Some W_5f1fc.
Proof. vm_refl. Qed.
Lemma D_5f1fc : decode_any W_5f1fc = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f200 : bv 32 := 0x0205bc23.
Lemma F_5f200 : fetch_word AsanUbsan.M.loaded_segments (0x5f250 : word) = Some W_5f200.
Proof. vm_refl. Qed.
Lemma D_5f200 : decode_any W_5f200 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f204 : bv 32 := 0x01813083.
Lemma F_5f204 : fetch_word AsanUbsan.M.loaded_segments (0x5f254 : word) = Some W_5f204.
Proof. vm_refl. Qed.
Lemma D_5f204 : decode_any W_5f204 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f208 : bv 32 := 0x01013403.
Lemma F_5f208 : fetch_word AsanUbsan.M.loaded_segments (0x5f258 : word) = Some W_5f208.
Proof. vm_refl. Qed.
Lemma D_5f208 : decode_any W_5f208 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f20c : bv 32 := 0x00813483.
Lemma F_5f20c : fetch_word AsanUbsan.M.loaded_segments (0x5f25c : word) = Some W_5f20c.
Proof. vm_refl. Qed.
Lemma D_5f20c : decode_any W_5f20c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f210 : bv 32 := 0x00013903.
Lemma F_5f210 : fetch_word AsanUbsan.M.loaded_segments (0x5f260 : word) = Some W_5f210.
Proof. vm_refl. Qed.
Lemma D_5f210 : decode_any W_5f210 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f214 : bv 32 := 0x02010113.
Lemma F_5f214 : fetch_word AsanUbsan.M.loaded_segments (0x5f264 : word) = Some W_5f214.
Proof. vm_refl. Qed.
Lemma D_5f214 : decode_any W_5f214 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f218 : bv 32 := 0x00008067.
Lemma F_5f218 : fetch_word AsanUbsan.M.loaded_segments (0x5f268 : word) = Some W_5f218.
Proof. vm_refl. Qed.
Lemma D_5f218 : decode_any W_5f218 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4f8 : bv 32 := 0x000de597.
Lemma F_5f4f8 : fetch_word AsanUbsan.M.loaded_segments (0x5f548 : word) = Some W_5f4f8.
Proof. vm_refl. Qed.
Lemma D_5f4f8 : decode_any W_5f4f8 = Some (Auipc 11 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f4fc : bv 32 := 0x3805b583.
Lemma F_5f4fc : fetch_word AsanUbsan.M.loaded_segments (0x5f54c : word) = Some W_5f4fc.
Proof. vm_refl. Qed.
Lemma D_5f4fc : decode_any W_5f4fc = Some (Load SZ8 true 11 11 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f500 : bv 32 := 0x0005b583.
Lemma F_5f500 : fetch_word AsanUbsan.M.loaded_segments (0x5f550 : word) = Some W_5f500.
Proof. vm_refl. Qed.
Lemma D_5f500 : decode_any W_5f500 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f504 : bv 32 := 0xfff58613.
Lemma F_5f504 : fetch_word AsanUbsan.M.loaded_segments (0x5f554 : word) = Some W_5f504.
Proof. vm_refl. Qed.
Lemma D_5f504 : decode_any W_5f504 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f508 : bv 32 := 0x00c5b6b3.
Lemma F_5f508 : fetch_word AsanUbsan.M.loaded_segments (0x5f558 : word) = Some W_5f508.
Proof. vm_refl. Qed.
Lemma D_5f508 : decode_any W_5f508 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f50c : bv 32 := 0xfff68693.
Lemma F_5f50c : fetch_word AsanUbsan.M.loaded_segments (0x5f55c : word) = Some W_5f50c.
Proof. vm_refl. Qed.
Lemma D_5f50c : decode_any W_5f50c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f510 : bv 32 := 0x00c6f6b3.
Lemma F_5f510 : fetch_word AsanUbsan.M.loaded_segments (0x5f560 : word) = Some W_5f510.
Proof. vm_refl. Qed.
Lemma D_5f510 : decode_any W_5f510 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f514 : bv 32 := 0x04a6f263.
Lemma F_5f514 : fetch_word AsanUbsan.M.loaded_segments (0x5f564 : word) = Some W_5f514.
Proof. vm_refl. Qed.
Lemma D_5f514 : decode_any W_5f514 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f518 : bv 32 := 0x000de697.
Lemma F_5f518 : fetch_word AsanUbsan.M.loaded_segments (0x5f568 : word) = Some W_5f518.
Proof. vm_refl. Qed.
Lemma D_5f518 : decode_any W_5f518 = Some (Auipc 13 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f51c : bv 32 := 0x3686b683.
Lemma F_5f51c : fetch_word AsanUbsan.M.loaded_segments (0x5f56c : word) = Some W_5f51c.
Proof. vm_refl. Qed.
Lemma D_5f51c : decode_any W_5f51c = Some (Load SZ8 true 13 13 872, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f520 : bv 32 := 0x000de717.
Lemma F_5f520 : fetch_word AsanUbsan.M.loaded_segments (0x5f570 : word) = Some W_5f520.
Proof. vm_refl. Qed.
Lemma D_5f520 : decode_any W_5f520 = Some (Auipc 14 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f524 : bv 32 := 0x36873703.
Lemma F_5f524 : fetch_word AsanUbsan.M.loaded_segments (0x5f574 : word) = Some W_5f524.
Proof. vm_refl. Qed.
Lemma D_5f524 : decode_any W_5f524 = Some (Load SZ8 true 14 14 872, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f528 : bv 32 := 0x0006b803.
Lemma F_5f528 : fetch_word AsanUbsan.M.loaded_segments (0x5f578 : word) = Some W_5f528.
Proof. vm_refl. Qed.
Lemma D_5f528 : decode_any W_5f528 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f52c : bv 32 := 0x00073683.
Lemma F_5f52c : fetch_word AsanUbsan.M.loaded_segments (0x5f57c : word) = Some W_5f52c.
Proof. vm_refl. Qed.
Lemma D_5f52c : decode_any W_5f52c = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f530 : bv 32 := 0xfff80793.
Lemma F_5f530 : fetch_word AsanUbsan.M.loaded_segments (0x5f580 : word) = Some W_5f530.
Proof. vm_refl. Qed.
Lemma D_5f530 : decode_any W_5f530 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f534 : bv 32 := 0x00a7f463.
Lemma F_5f534 : fetch_word AsanUbsan.M.loaded_segments (0x5f584 : word) = Some W_5f534.
Proof. vm_refl. Qed.
Lemma D_5f534 : decode_any W_5f534 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f53c : bv 32 := 0x000de717.
Lemma F_5f53c : fetch_word AsanUbsan.M.loaded_segments (0x5f58c : word) = Some W_5f53c.
Proof. vm_refl. Qed.
Lemma D_5f53c : decode_any W_5f53c = Some (Auipc 14 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f540 : bv 32 := 0x35473703.
Lemma F_5f540 : fetch_word AsanUbsan.M.loaded_segments (0x5f590 : word) = Some W_5f540.
Proof. vm_refl. Qed.
Lemma D_5f540 : decode_any W_5f540 = Some (Load SZ8 true 14 14 852, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f544 : bv 32 := 0x00073283.
Lemma F_5f544 : fetch_word AsanUbsan.M.loaded_segments (0x5f594 : word) = Some W_5f544.
Proof. vm_refl. Qed.
Lemma D_5f544 : decode_any W_5f544 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f548 : bv 32 := 0x0032d713.
Lemma F_5f548 : fetch_word AsanUbsan.M.loaded_segments (0x5f598 : word) = Some W_5f548.
Proof. vm_refl. Qed.
Lemma D_5f548 : decode_any W_5f548 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f54c : bv 32 := 0x00b708b3.
Lemma F_5f54c : fetch_word AsanUbsan.M.loaded_segments (0x5f59c : word) = Some W_5f54c.
Proof. vm_refl. Qed.
Lemma D_5f54c : decode_any W_5f54c = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f550 : bv 32 := 0x00a2ea63.
Lemma F_5f550 : fetch_word AsanUbsan.M.loaded_segments (0x5f5a0 : word) = Some W_5f550.
Proof. vm_refl. Qed.
Lemma D_5f550 : decode_any W_5f550 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f554 : bv 32 := 0x00a8f863.
Lemma F_5f554 : fetch_word AsanUbsan.M.loaded_segments (0x5f5a4 : word) = Some W_5f554.
Proof. vm_refl. Qed.
Lemma D_5f554 : decode_any W_5f554 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f558 : bv 32 := 0x00355513.
Lemma F_5f558 : fetch_word AsanUbsan.M.loaded_segments (0x5f5a8 : word) = Some W_5f558.
Proof. vm_refl. Qed.
Lemma D_5f558 : decode_any W_5f558 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f55c : bv 32 := 0x00a58533.
Lemma F_5f55c : fetch_word AsanUbsan.M.loaded_segments (0x5f5ac : word) = Some W_5f55c.
Proof. vm_refl. Qed.
Lemma D_5f55c : decode_any W_5f55c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f560 : bv 32 := 0x00008067.
Lemma F_5f560 : fetch_word AsanUbsan.M.loaded_segments (0x5f5b0 : word) = Some W_5f560.
Proof. vm_refl. Qed.
Lemma D_5f560 : decode_any W_5f560 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
