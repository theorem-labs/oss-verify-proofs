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

Definition W_827a0 : bv 32 := 0x000c0517.
Lemma F_827a0 : fetch_word Asan.M.loaded_segments (0x827f0 : word) = Some W_827a0.
Proof. vm_refl. Qed.
Lemma D_827a0 : decode_any W_827a0 = Some (Auipc 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_827a4 : bv 32 := 0xf0c52503.
Lemma F_827a4 : fetch_word Asan.M.loaded_segments (0x827f4 : word) = Some W_827a4.
Proof. vm_refl. Qed.
Lemma D_827a4 : decode_any W_827a4 = Some (Load SZ4 true 10 10 3852, 4%Z).
Proof. vm_refl. Qed.

Definition W_827a8 : bv 32 := 0x0230000f.
Lemma F_827a8 : fetch_word Asan.M.loaded_segments (0x827f8 : word) = Some W_827a8.
Proof. vm_refl. Qed.
Lemma D_827a8 : decode_any W_827a8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827ac : bv 32 := 0x00008067.
Lemma F_827ac : fetch_word Asan.M.loaded_segments (0x827fc : word) = Some W_827ac.
Proof. vm_refl. Qed.
Lemma D_827ac : decode_any W_827ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827b0 : bv 32 := 0xfb010113.
Lemma F_827b0 : fetch_word Asan.M.loaded_segments (0x82800 : word) = Some W_827b0.
Proof. vm_refl. Qed.
Lemma D_827b0 : decode_any W_827b0 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_827b4 : bv 32 := 0x04113423.
Lemma F_827b4 : fetch_word Asan.M.loaded_segments (0x82804 : word) = Some W_827b4.
Proof. vm_refl. Qed.
Lemma D_827b4 : decode_any W_827b4 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_827b8 : bv 32 := 0x04813023.
Lemma F_827b8 : fetch_word Asan.M.loaded_segments (0x82808 : word) = Some W_827b8.
Proof. vm_refl. Qed.
Lemma D_827b8 : decode_any W_827b8 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_827bc : bv 32 := 0x02913c23.
Lemma F_827bc : fetch_word Asan.M.loaded_segments (0x8280c : word) = Some W_827bc.
Proof. vm_refl. Qed.
Lemma D_827bc : decode_any W_827bc = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_827c0 : bv 32 := 0x03213823.
Lemma F_827c0 : fetch_word Asan.M.loaded_segments (0x82810 : word) = Some W_827c0.
Proof. vm_refl. Qed.
Lemma D_827c0 : decode_any W_827c0 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_827c4 : bv 32 := 0x03313423.
Lemma F_827c4 : fetch_word Asan.M.loaded_segments (0x82814 : word) = Some W_827c4.
Proof. vm_refl. Qed.
Lemma D_827c4 : decode_any W_827c4 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_827c8 : bv 32 := 0x03413023.
Lemma F_827c8 : fetch_word Asan.M.loaded_segments (0x82818 : word) = Some W_827c8.
Proof. vm_refl. Qed.
Lemma D_827c8 : decode_any W_827c8 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_827cc : bv 32 := 0x01513c23.
Lemma F_827cc : fetch_word Asan.M.loaded_segments (0x8281c : word) = Some W_827cc.
Proof. vm_refl. Qed.
Lemma D_827cc : decode_any W_827cc = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_827d0 : bv 32 := 0x01613823.
Lemma F_827d0 : fetch_word Asan.M.loaded_segments (0x82820 : word) = Some W_827d0.
Proof. vm_refl. Qed.
Lemma D_827d0 : decode_any W_827d0 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_827d4 : bv 32 := 0x01713423.
Lemma F_827d4 : fetch_word Asan.M.loaded_segments (0x82824 : word) = Some W_827d4.
Proof. vm_refl. Qed.
Lemma D_827d4 : decode_any W_827d4 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_827d8 : bv 32 := 0x01813023.
Lemma F_827d8 : fetch_word Asan.M.loaded_segments (0x82828 : word) = Some W_827d8.
Proof. vm_refl. Qed.
Lemma D_827d8 : decode_any W_827d8 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827dc : bv 32 := 0x00078493.
Lemma F_827dc : fetch_word Asan.M.loaded_segments (0x8282c : word) = Some W_827dc.
Proof. vm_refl. Qed.
Lemma D_827dc : decode_any W_827dc = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827e0 : bv 32 := 0x00070a93.
Lemma F_827e0 : fetch_word Asan.M.loaded_segments (0x82830 : word) = Some W_827e0.
Proof. vm_refl. Qed.
Lemma D_827e0 : decode_any W_827e0 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827e4 : bv 32 := 0x00068a13.
Lemma F_827e4 : fetch_word Asan.M.loaded_segments (0x82834 : word) = Some W_827e4.
Proof. vm_refl. Qed.
Lemma D_827e4 : decode_any W_827e4 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827e8 : bv 32 := 0x00060413.
Lemma F_827e8 : fetch_word Asan.M.loaded_segments (0x82838 : word) = Some W_827e8.
Proof. vm_refl. Qed.
Lemma D_827e8 : decode_any W_827e8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827ec : bv 32 := 0x00058913.
Lemma F_827ec : fetch_word Asan.M.loaded_segments (0x8283c : word) = Some W_827ec.
Proof. vm_refl. Qed.
Lemma D_827ec : decode_any W_827ec = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827f0 : bv 32 := 0x00050993.
Lemma F_827f0 : fetch_word Asan.M.loaded_segments (0x82840 : word) = Some W_827f0.
Proof. vm_refl. Qed.
Lemma D_827f0 : decode_any W_827f0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_827f4 : bv 32 := 0x00052423.
Lemma F_827f4 : fetch_word Asan.M.loaded_segments (0x82844 : word) = Some W_827f4.
Proof. vm_refl. Qed.
Lemma D_827f4 : decode_any W_827f4 = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_827f8 : bv 32 := 0xb10fe0ef.
Lemma F_827f8 : fetch_word Asan.M.loaded_segments (0x82848 : word) = Some W_827f8.
Proof. vm_refl. Qed.
Lemma D_827f8 : decode_any W_827f8 = Some (Jal 1 2089744, 4%Z).
Proof. vm_refl. Qed.

Definition W_827fc : bv 32 := 0x0c050a63.
Lemma F_827fc : fetch_word Asan.M.loaded_segments (0x8284c : word) = Some W_827fc.
Proof. vm_refl. Qed.
Lemma D_827fc : decode_any W_827fc = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_82800 : bv 32 := 0x219010ef.
Lemma F_82800 : fetch_word Asan.M.loaded_segments (0x82850 : word) = Some W_82800.
Proof. vm_refl. Qed.
Lemma D_82800 : decode_any W_82800 = Some (Jal 1 6680, 4%Z).
Proof. vm_refl. Qed.

Definition W_82804 : bv 32 := 0x04050a63.
Lemma F_82804 : fetch_word Asan.M.loaded_segments (0x82854 : word) = Some W_82804.
Proof. vm_refl. Qed.
Lemma D_82804 : decode_any W_82804 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_82808 : bv 32 := 0x7ff50c13.
Lemma F_82808 : fetch_word Asan.M.loaded_segments (0x82858 : word) = Some W_82808.
Proof. vm_refl. Qed.
Lemma D_82808 : decode_any W_82808 = Some (OpImm ALU_ADD 24 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_8280c : bv 32 := 0x461c4583.
Lemma F_8280c : fetch_word Asan.M.loaded_segments (0x8285c : word) = Some W_8280c.
Proof. vm_refl. Qed.
Lemma D_8280c : decode_any W_8280c = Some (Load SZ1 false 11 24 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_82810 : bv 32 := 0x00100613.
Lemma F_82810 : fetch_word Asan.M.loaded_segments (0x82860 : word) = Some W_82810.
Proof. vm_refl. Qed.
Lemma D_82810 : decode_any W_82810 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_82814 : bv 32 := 0x46cc00a3.
Lemma F_82814 : fetch_word Asan.M.loaded_segments (0x82864 : word) = Some W_82814.
Proof. vm_refl. Qed.
Lemma D_82814 : decode_any W_82814 = Some (Store SZ1 24 12 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_82818 : bv 32 := 0x0a059a63.
Lemma F_82818 : fetch_word Asan.M.loaded_segments (0x82868 : word) = Some W_82818.
Proof. vm_refl. Qed.
Lemma D_82818 : decode_any W_82818 = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_8281c : bv 32 := 0x00050b93.
Lemma F_8281c : fetch_word Asan.M.loaded_segments (0x8286c : word) = Some W_8281c.
Proof. vm_refl. Qed.
Lemma D_8281c : decode_any W_8281c = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82820 : bv 32 := 0x3bd010ef.
Lemma F_82820 : fetch_word Asan.M.loaded_segments (0x82870 : word) = Some W_82820.
Proof. vm_refl. Qed.
Lemma D_82820 : decode_any W_82820 = Some (Jal 1 7100, 4%Z).
Proof. vm_refl. Qed.

Definition W_82824 : bv 32 := 0x00050b13.
Lemma F_82824 : fetch_word Asan.M.loaded_segments (0x82874 : word) = Some W_82824.
Proof. vm_refl. Qed.
Lemma D_82824 : decode_any W_82824 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82828 : bv 32 := 0x000b8513.
Lemma F_82828 : fetch_word Asan.M.loaded_segments (0x82878 : word) = Some W_82828.
Proof. vm_refl. Qed.
Lemma D_82828 : decode_any W_82828 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8282c : bv 32 := 0x409010ef.
Lemma F_8282c : fetch_word Asan.M.loaded_segments (0x8287c : word) = Some W_8282c.
Proof. vm_refl. Qed.
Lemma D_8282c : decode_any W_8282c = Some (Jal 1 7176, 4%Z).
Proof. vm_refl. Qed.

Definition W_82830 : bv 32 := 0x00050813.
Lemma F_82830 : fetch_word Asan.M.loaded_segments (0x82880 : word) = Some W_82830.
Proof. vm_refl. Qed.
Lemma D_82830 : decode_any W_82830 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82834 : bv 32 := 0x060a8c63.
Lemma F_82834 : fetch_word Asan.M.loaded_segments (0x82884 : word) = Some W_82834.
Proof. vm_refl. Qed.
Lemma D_82834 : decode_any W_82834 = Some (Branch BC_EQ 21 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_82838 : bv 32 := 0x00100893.
Lemma F_82838 : fetch_word Asan.M.loaded_segments (0x82888 : word) = Some W_82838.
Proof. vm_refl. Qed.
Lemma D_82838 : decode_any W_82838 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8283c : bv 32 := 0x00098513.
Lemma F_8283c : fetch_word Asan.M.loaded_segments (0x8288c : word) = Some W_8283c.
Proof. vm_refl. Qed.
Lemma D_8283c : decode_any W_8283c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82840 : bv 32 := 0x00048593.
Lemma F_82840 : fetch_word Asan.M.loaded_segments (0x82890 : word) = Some W_82840.
Proof. vm_refl. Qed.
Lemma D_82840 : decode_any W_82840 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82844 : bv 32 := 0x00090613.
Lemma F_82844 : fetch_word Asan.M.loaded_segments (0x82894 : word) = Some W_82844.
Proof. vm_refl. Qed.
Lemma D_82844 : decode_any W_82844 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82848 : bv 32 := 0x00040693.
Lemma F_82848 : fetch_word Asan.M.loaded_segments (0x82898 : word) = Some W_82848.
Proof. vm_refl. Qed.
Lemma D_82848 : decode_any W_82848 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8284c : bv 32 := 0x00000713.
Lemma F_8284c : fetch_word Asan.M.loaded_segments (0x8289c : word) = Some W_8284c.
Proof. vm_refl. Qed.
Lemma D_8284c : decode_any W_8284c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82850 : bv 32 := 0x000b0793.
Lemma F_82850 : fetch_word Asan.M.loaded_segments (0x828a0 : word) = Some W_82850.
Proof. vm_refl. Qed.
Lemma D_82850 : decode_any W_82850 = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_82854 : bv 32 := 0x0740006f.
Lemma F_82854 : fetch_word Asan.M.loaded_segments (0x828a4 : word) = Some W_82854.
Proof. vm_refl. Qed.
Lemma D_82854 : decode_any W_82854 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_828c8 : bv 32 := 0x018190ef.
Lemma F_828c8 : fetch_word Asan.M.loaded_segments (0x82918 : word) = Some W_828c8.
Proof. vm_refl. Qed.
Lemma D_828c8 : decode_any W_828c8 = Some (Jal 1 102424, 4%Z).
Proof. vm_refl. Qed.

Definition W_828cc : bv 32 := 0x460c00a3.
Lemma F_828cc : fetch_word Asan.M.loaded_segments (0x8291c : word) = Some W_828cc.
Proof. vm_refl. Qed.
Lemma D_828cc : decode_any W_828cc = Some (Store SZ1 24 0 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_828d0 : bv 32 := 0x04813083.
Lemma F_828d0 : fetch_word Asan.M.loaded_segments (0x82920 : word) = Some W_828d0.
Proof. vm_refl. Qed.
Lemma D_828d0 : decode_any W_828d0 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_828d4 : bv 32 := 0x04013403.
Lemma F_828d4 : fetch_word Asan.M.loaded_segments (0x82924 : word) = Some W_828d4.
Proof. vm_refl. Qed.
Lemma D_828d4 : decode_any W_828d4 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_828d8 : bv 32 := 0x03813483.
Lemma F_828d8 : fetch_word Asan.M.loaded_segments (0x82928 : word) = Some W_828d8.
Proof. vm_refl. Qed.
Lemma D_828d8 : decode_any W_828d8 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_828dc : bv 32 := 0x03013903.
Lemma F_828dc : fetch_word Asan.M.loaded_segments (0x8292c : word) = Some W_828dc.
Proof. vm_refl. Qed.
Lemma D_828dc : decode_any W_828dc = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_828e0 : bv 32 := 0x02813983.
Lemma F_828e0 : fetch_word Asan.M.loaded_segments (0x82930 : word) = Some W_828e0.
Proof. vm_refl. Qed.
Lemma D_828e0 : decode_any W_828e0 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_828e4 : bv 32 := 0x02013a03.
Lemma F_828e4 : fetch_word Asan.M.loaded_segments (0x82934 : word) = Some W_828e4.
Proof. vm_refl. Qed.
Lemma D_828e4 : decode_any W_828e4 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_828e8 : bv 32 := 0x01813a83.
Lemma F_828e8 : fetch_word Asan.M.loaded_segments (0x82938 : word) = Some W_828e8.
Proof. vm_refl. Qed.
Lemma D_828e8 : decode_any W_828e8 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_828ec : bv 32 := 0x01013b03.
Lemma F_828ec : fetch_word Asan.M.loaded_segments (0x8293c : word) = Some W_828ec.
Proof. vm_refl. Qed.
Lemma D_828ec : decode_any W_828ec = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_828f0 : bv 32 := 0x00813b83.
Lemma F_828f0 : fetch_word Asan.M.loaded_segments (0x82940 : word) = Some W_828f0.
Proof. vm_refl. Qed.
Lemma D_828f0 : decode_any W_828f0 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_828f4 : bv 32 := 0x00013c03.
Lemma F_828f4 : fetch_word Asan.M.loaded_segments (0x82944 : word) = Some W_828f4.
Proof. vm_refl. Qed.
Lemma D_828f4 : decode_any W_828f4 = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_828f8 : bv 32 := 0x05010113.
Lemma F_828f8 : fetch_word Asan.M.loaded_segments (0x82948 : word) = Some W_828f8.
Proof. vm_refl. Qed.
Lemma D_828f8 : decode_any W_828f8 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_828fc : bv 32 := 0x00008067.
Lemma F_828fc : fetch_word Asan.M.loaded_segments (0x8294c : word) = Some W_828fc.
Proof. vm_refl. Qed.
Lemma D_828fc : decode_any W_828fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
