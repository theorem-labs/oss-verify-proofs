(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6b860 : bv 32 := 0xfd010113.
Lemma F_6b860 : fetch_word Asan.M.loaded_segments (0x6b860 : word) = Some W_6b860.
Proof. vm_refl. Qed.
Lemma D_6b860 : decode_any W_6b860 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b864 : bv 32 := 0x02113423.
Lemma F_6b864 : fetch_word Asan.M.loaded_segments (0x6b864 : word) = Some W_6b864.
Proof. vm_refl. Qed.
Lemma D_6b864 : decode_any W_6b864 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b868 : bv 32 := 0x02813023.
Lemma F_6b868 : fetch_word Asan.M.loaded_segments (0x6b868 : word) = Some W_6b868.
Proof. vm_refl. Qed.
Lemma D_6b868 : decode_any W_6b868 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b86c : bv 32 := 0x00913c23.
Lemma F_6b86c : fetch_word Asan.M.loaded_segments (0x6b86c : word) = Some W_6b86c.
Proof. vm_refl. Qed.
Lemma D_6b86c : decode_any W_6b86c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b870 : bv 32 := 0x01213823.
Lemma F_6b870 : fetch_word Asan.M.loaded_segments (0x6b870 : word) = Some W_6b870.
Proof. vm_refl. Qed.
Lemma D_6b870 : decode_any W_6b870 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b874 : bv 32 := 0x01313423.
Lemma F_6b874 : fetch_word Asan.M.loaded_segments (0x6b874 : word) = Some W_6b874.
Proof. vm_refl. Qed.
Lemma D_6b874 : decode_any W_6b874 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b878 : bv 32 := 0x00102517.
Lemma F_6b878 : fetch_word Asan.M.loaded_segments (0x6b878 : word) = Some W_6b878.
Proof. vm_refl. Qed.
Lemma D_6b878 : decode_any W_6b878 = Some (Auipc 10 258, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b87c : bv 32 := 0xd5050413.
Lemma F_6b87c : fetch_word Asan.M.loaded_segments (0x6b87c : word) = Some W_6b87c.
Proof. vm_refl. Qed.
Lemma D_6b87c : decode_any W_6b87c = Some (OpImm ALU_ADD 8 10 3408, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b880 : bv 32 := 0x00040503.
Lemma F_6b880 : fetch_word Asan.M.loaded_segments (0x6b880 : word) = Some W_6b880.
Proof. vm_refl. Qed.
Lemma D_6b880 : decode_any W_6b880 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b884 : bv 32 := 0x0230000f.
Lemma F_6b884 : fetch_word Asan.M.loaded_segments (0x6b884 : word) = Some W_6b884.
Proof. vm_refl. Qed.
Lemma D_6b884 : decode_any W_6b884 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b888 : bv 32 := 0x0e051e63.
Lemma F_6b888 : fetch_word Asan.M.loaded_segments (0x6b888 : word) = Some W_6b888.
Proof. vm_refl. Qed.
Lemma D_6b888 : decode_any W_6b888 = Some (Branch BC_NE 10 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b88c : bv 32 := 0x00140513.
Lemma F_6b88c : fetch_word Asan.M.loaded_segments (0x6b88c : word) = Some W_6b88c.
Proof. vm_refl. Qed.
Lemma D_6b88c : decode_any W_6b88c = Some (OpImm ALU_ADD 10 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b890 : bv 32 := 0x0ff00593.
Lemma F_6b890 : fetch_word Asan.M.loaded_segments (0x6b890 : word) = Some W_6b890.
Proof. vm_refl. Qed.
Lemma D_6b890 : decode_any W_6b890 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b894 : bv 32 := 0x00100613.
Lemma F_6b894 : fetch_word Asan.M.loaded_segments (0x6b894 : word) = Some W_6b894.
Proof. vm_refl. Qed.
Lemma D_6b894 : decode_any W_6b894 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b898 : bv 32 := 0xffc57693.
Lemma F_6b898 : fetch_word Asan.M.loaded_segments (0x6b898 : word) = Some W_6b898.
Proof. vm_refl. Qed.
Lemma D_6b898 : decode_any W_6b898 = Some (OpImm ALU_AND 13 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b89c : bv 32 := 0x00357713.
Lemma F_6b89c : fetch_word Asan.M.loaded_segments (0x6b89c : word) = Some W_6b89c.
Proof. vm_refl. Qed.
Lemma D_6b89c : decode_any W_6b89c = Some (OpImm ALU_AND 14 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8a0 : bv 32 := 0x00371713.
Lemma F_6b8a0 : fetch_word Asan.M.loaded_segments (0x6b8a0 : word) = Some W_6b8a0.
Proof. vm_refl. Qed.
Lemma D_6b8a0 : decode_any W_6b8a0 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8a4 : bv 32 := 0x00e595bb.
Lemma F_6b8a4 : fetch_word Asan.M.loaded_segments (0x6b8a4 : word) = Some W_6b8a4.
Proof. vm_refl. Qed.
Lemma D_6b8a4 : decode_any W_6b8a4 = Some (Op32 ALU_SLL 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8a8 : bv 32 := 0x00e6163b.
Lemma F_6b8a8 : fetch_word Asan.M.loaded_segments (0x6b8a8 : word) = Some W_6b8a8.
Proof. vm_refl. Qed.
Lemma D_6b8a8 : decode_any W_6b8a8 = Some (Op32 ALU_SLL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8ac : bv 32 := 0x1406a7af.
Lemma F_6b8ac : fetch_word Asan.M.loaded_segments (0x6b8ac : word) = Some W_6b8ac.
Proof. vm_refl. Qed.
Lemma D_6b8ac : decode_any W_6b8ac = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8b0 : bv 32 := 0x00060813.
Lemma F_6b8b0 : fetch_word Asan.M.loaded_segments (0x6b8b0 : word) = Some W_6b8b0.
Proof. vm_refl. Qed.
Lemma D_6b8b0 : decode_any W_6b8b0 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8b4 : bv 32 := 0x0107c833.
Lemma F_6b8b4 : fetch_word Asan.M.loaded_segments (0x6b8b4 : word) = Some W_6b8b4.
Proof. vm_refl. Qed.
Lemma D_6b8b4 : decode_any W_6b8b4 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8b8 : bv 32 := 0x00b87833.
Lemma F_6b8b8 : fetch_word Asan.M.loaded_segments (0x6b8b8 : word) = Some W_6b8b8.
Proof. vm_refl. Qed.
Lemma D_6b8b8 : decode_any W_6b8b8 = Some (Op ALU_AND 16 16 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8bc : bv 32 := 0x0107c833.
Lemma F_6b8bc : fetch_word Asan.M.loaded_segments (0x6b8bc : word) = Some W_6b8bc.
Proof. vm_refl. Qed.
Lemma D_6b8bc : decode_any W_6b8bc = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8c0 : bv 32 := 0x1906a82f.
Lemma F_6b8c0 : fetch_word Asan.M.loaded_segments (0x6b8c0 : word) = Some W_6b8c0.
Proof. vm_refl. Qed.
Lemma D_6b8c0 : decode_any W_6b8c0 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8c4 : bv 32 := 0xfe0814e3.
Lemma F_6b8c4 : fetch_word Asan.M.loaded_segments (0x6b8c4 : word) = Some W_6b8c4.
Proof. vm_refl. Qed.
Lemma D_6b8c4 : decode_any W_6b8c4 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8c8 : bv 32 := 0x00e7d5bb.
Lemma F_6b8c8 : fetch_word Asan.M.loaded_segments (0x6b8c8 : word) = Some W_6b8c8.
Proof. vm_refl. Qed.
Lemma D_6b8c8 : decode_any W_6b8c8 = Some (Op32 ALU_SRL 11 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8cc : bv 32 := 0x0ff5f593.
Lemma F_6b8cc : fetch_word Asan.M.loaded_segments (0x6b8cc : word) = Some W_6b8cc.
Proof. vm_refl. Qed.
Lemma D_6b8cc : decode_any W_6b8cc = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8d0 : bv 32 := 0x0c059c63.
Lemma F_6b8d0 : fetch_word Asan.M.loaded_segments (0x6b8d0 : word) = Some W_6b8d0.
Proof. vm_refl. Qed.
Lemma D_6b8d0 : decode_any W_6b8d0 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8d4 : bv 32 := 0x00040503.
Lemma F_6b8d4 : fetch_word Asan.M.loaded_segments (0x6b8d4 : word) = Some W_6b8d4.
Proof. vm_refl. Qed.
Lemma D_6b8d4 : decode_any W_6b8d4 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8d8 : bv 32 := 0x0a051263.
Lemma F_6b8d8 : fetch_word Asan.M.loaded_segments (0x6b8d8 : word) = Some W_6b8d8.
Proof. vm_refl. Qed.
Lemma D_6b8d8 : decode_any W_6b8d8 = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8dc : bv 32 := 0x00073517.
Lemma F_6b8dc : fetch_word Asan.M.loaded_segments (0x6b8dc : word) = Some W_6b8dc.
Proof. vm_refl. Qed.
Lemma D_6b8dc : decode_any W_6b8dc = Some (Auipc 10 115, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8e0 : bv 32 := 0x000815b7.
Lemma F_6b8e0 : fetch_word Asan.M.loaded_segments (0x6b8e0 : word) = Some W_6b8e0.
Proof. vm_refl. Qed.
Lemma D_6b8e0 : decode_any W_6b8e0 = Some (Lui 11 129, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8e4 : bv 32 := 0x46450493.
Lemma F_6b8e4 : fetch_word Asan.M.loaded_segments (0x6b8e4 : word) = Some W_6b8e4.
Proof. vm_refl. Qed.
Lemma D_6b8e4 : decode_any W_6b8e4 = Some (OpImm ALU_ADD 9 10 1124, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8e8 : bv 32 := 0x0085851b.
Lemma F_6b8e8 : fetch_word Asan.M.loaded_segments (0x6b8e8 : word) = Some W_6b8e8.
Proof. vm_refl. Qed.
Lemma D_6b8e8 : decode_any W_6b8e8 = Some (OpImm32 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8ec : bv 32 := 0x00a48533.
Lemma F_6b8ec : fetch_word Asan.M.loaded_segments (0x6b8ec : word) = Some W_6b8ec.
Proof. vm_refl. Qed.
Lemma D_6b8ec : decode_any W_6b8ec = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8f0 : bv 32 := 0x02800613.
Lemma F_6b8f0 : fetch_word Asan.M.loaded_segments (0x6b8f0 : word) = Some W_6b8f0.
Proof. vm_refl. Qed.
Lemma D_6b8f0 : decode_any W_6b8f0 = Some (OpImm ALU_ADD 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8f4 : bv 32 := 0x00000593.
Lemma F_6b8f4 : fetch_word Asan.M.loaded_segments (0x6b8f4 : word) = Some W_6b8f4.
Proof. vm_refl. Qed.
Lemma D_6b8f4 : decode_any W_6b8f4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8f8 : bv 32 := 0x269050ef.
Lemma F_6b8f8 : fetch_word Asan.M.loaded_segments (0x6b8f8 : word) = Some W_6b8f8.
Proof. vm_refl. Qed.
Lemma D_6b8f8 : decode_any W_6b8f8 = Some (Jal 1 23144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b8fc : bv 32 := 0x00048023.
Lemma F_6b8fc : fetch_word Asan.M.loaded_segments (0x6b8fc : word) = Some W_6b8fc.
Proof. vm_refl. Qed.
Lemma D_6b8fc : decode_any W_6b8fc = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b900 : bv 32 := 0x00848513.
Lemma F_6b900 : fetch_word Asan.M.loaded_segments (0x6b900 : word) = Some W_6b900.
Proof. vm_refl. Qed.
Lemma D_6b900 : decode_any W_6b900 = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b904 : bv 32 := 0x00040637.
Lemma F_6b904 : fetch_word Asan.M.loaded_segments (0x6b904 : word) = Some W_6b904.
Proof. vm_refl. Qed.
Lemma D_6b904 : decode_any W_6b904 = Some (Lui 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b908 : bv 32 := 0x000409b7.
Lemma F_6b908 : fetch_word Asan.M.loaded_segments (0x6b908 : word) = Some W_6b908.
Proof. vm_refl. Qed.
Lemma D_6b908 : decode_any W_6b908 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b90c : bv 32 := 0x00000593.
Lemma F_6b90c : fetch_word Asan.M.loaded_segments (0x6b90c : word) = Some W_6b90c.
Proof. vm_refl. Qed.
Lemma D_6b90c : decode_any W_6b90c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b910 : bv 32 := 0x251050ef.
Lemma F_6b910 : fetch_word Asan.M.loaded_segments (0x6b910 : word) = Some W_6b910.
Proof. vm_refl. Qed.
Lemma D_6b910 : decode_any W_6b910 = Some (Jal 1 23120, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b914 : bv 32 := 0x0409851b.
Lemma F_6b914 : fetch_word Asan.M.loaded_segments (0x6b914 : word) = Some W_6b914.
Proof. vm_refl. Qed.
Lemma D_6b914 : decode_any W_6b914 = Some (OpImm32 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b918 : bv 32 := 0x00a48533.
Lemma F_6b918 : fetch_word Asan.M.loaded_segments (0x6b918 : word) = Some W_6b918.
Proof. vm_refl. Qed.
Lemma D_6b918 : decode_any W_6b918 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b91c : bv 32 := 0x01b00613.
Lemma F_6b91c : fetch_word Asan.M.loaded_segments (0x6b91c : word) = Some W_6b91c.
Proof. vm_refl. Qed.
Lemma D_6b91c : decode_any W_6b91c = Some (OpImm ALU_ADD 12 0 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b920 : bv 32 := 0x00761613.
Lemma F_6b920 : fetch_word Asan.M.loaded_segments (0x6b920 : word) = Some W_6b920.
Proof. vm_refl. Qed.
Lemma D_6b920 : decode_any W_6b920 = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b924 : bv 32 := 0x00000593.
Lemma F_6b924 : fetch_word Asan.M.loaded_segments (0x6b924 : word) = Some W_6b924.
Proof. vm_refl. Qed.
Lemma D_6b924 : decode_any W_6b924 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b928 : bv 32 := 0x239050ef.
Lemma F_6b928 : fetch_word Asan.M.loaded_segments (0x6b928 : word) = Some W_6b928.
Proof. vm_refl. Qed.
Lemma D_6b928 : decode_any W_6b928 = Some (Jal 1 23096, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b92c : bv 32 := 0x00041937.
Lemma F_6b92c : fetch_word Asan.M.loaded_segments (0x6b92c : word) = Some W_6b92c.
Proof. vm_refl. Qed.
Lemma D_6b92c : decode_any W_6b92c = Some (Lui 18 65, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b930 : bv 32 := 0xdc09051b.
Lemma F_6b930 : fetch_word Asan.M.loaded_segments (0x6b930 : word) = Some W_6b930.
Proof. vm_refl. Qed.
Lemma D_6b930 : decode_any W_6b930 = Some (OpImm32 10 18 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b934 : bv 32 := 0x00a48533.
Lemma F_6b934 : fetch_word Asan.M.loaded_segments (0x6b934 : word) = Some W_6b934.
Proof. vm_refl. Qed.
Lemma D_6b934 : decode_any W_6b934 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b938 : bv 32 := 0x2489861b.
Lemma F_6b938 : fetch_word Asan.M.loaded_segments (0x6b938 : word) = Some W_6b938.
Proof. vm_refl. Qed.
Lemma D_6b938 : decode_any W_6b938 = Some (OpImm32 12 19 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b93c : bv 32 := 0x00000593.
Lemma F_6b93c : fetch_word Asan.M.loaded_segments (0x6b93c : word) = Some W_6b93c.
Proof. vm_refl. Qed.
Lemma D_6b93c : decode_any W_6b93c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b940 : bv 32 := 0x221050ef.
Lemma F_6b940 : fetch_word Asan.M.loaded_segments (0x6b940 : word) = Some W_6b940.
Proof. vm_refl. Qed.
Lemma D_6b940 : decode_any W_6b940 = Some (Jal 1 23072, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b944 : bv 32 := 0x0006a517.
Lemma F_6b944 : fetch_word Asan.M.loaded_segments (0x6b944 : word) = Some W_6b944.
Proof. vm_refl. Qed.
Lemma D_6b944 : decode_any W_6b944 = Some (Auipc 10 106, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b948 : bv 32 := 0xf5453983.
Lemma F_6b948 : fetch_word Asan.M.loaded_segments (0x6b948 : word) = Some W_6b948.
Proof. vm_refl. Qed.
Lemma D_6b948 : decode_any W_6b948 = Some (Load SZ8 true 19 10 3924, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b94c : bv 32 := 0x0009b503.
Lemma F_6b94c : fetch_word Asan.M.loaded_segments (0x6b94c : word) = Some W_6b94c.
Proof. vm_refl. Qed.
Lemma D_6b94c : decode_any W_6b94c = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b950 : bv 32 := 0x00051663.
Lemma F_6b950 : fetch_word Asan.M.loaded_segments (0x6b950 : word) = Some W_6b950.
Proof. vm_refl. Qed.
Lemma D_6b950 : decode_any W_6b950 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b954 : bv 32 := 0x138070ef.
Lemma F_6b954 : fetch_word Asan.M.loaded_segments (0x6b954 : word) = Some W_6b954.
Proof. vm_refl. Qed.
Lemma D_6b954 : decode_any W_6b954 = Some (Jal 1 28984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b958 : bv 32 := 0x00a9b023.
Lemma F_6b958 : fetch_word Asan.M.loaded_segments (0x6b958 : word) = Some W_6b958.
Proof. vm_refl. Qed.
Lemma D_6b958 : decode_any W_6b958 = Some (Store SZ8 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b95c : bv 32 := 0x012485b3.
Lemma F_6b95c : fetch_word Asan.M.loaded_segments (0x6b95c : word) = Some W_6b95c.
Proof. vm_refl. Qed.
Lemma D_6b95c : decode_any W_6b95c = Some (Op ALU_ADD 11 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b960 : bv 32 := 0xdd09061b.
Lemma F_6b960 : fetch_word Asan.M.loaded_segments (0x6b960 : word) = Some W_6b960.
Proof. vm_refl. Qed.
Lemma D_6b960 : decode_any W_6b960 = Some (OpImm32 12 18 3536, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b964 : bv 32 := 0x00c48633.
Lemma F_6b964 : fetch_word Asan.M.loaded_segments (0x6b964 : word) = Some W_6b964.
Proof. vm_refl. Qed.
Lemma D_6b964 : decode_any W_6b964 = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b968 : bv 32 := 0x00100693.
Lemma F_6b968 : fetch_word Asan.M.loaded_segments (0x6b968 : word) = Some W_6b968.
Proof. vm_refl. Qed.
Lemma D_6b968 : decode_any W_6b968 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b96c : bv 32 := 0xdca5b023.
Lemma F_6b96c : fetch_word Asan.M.loaded_segments (0x6b96c : word) = Some W_6b96c.
Proof. vm_refl. Qed.
Lemma D_6b96c : decode_any W_6b96c = Some (Store SZ8 11 10 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b970 : bv 32 := 0xdcc5b423.
Lemma F_6b970 : fetch_word Asan.M.loaded_segments (0x6b970 : word) = Some W_6b970.
Proof. vm_refl. Qed.
Lemma D_6b970 : decode_any W_6b970 = Some (Store SZ8 11 12 3528, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b974 : bv 32 := 0x0310000f.
Lemma F_6b974 : fetch_word Asan.M.loaded_segments (0x6b974 : word) = Some W_6b974.
Proof. vm_refl. Qed.
Lemma D_6b974 : decode_any W_6b974 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b978 : bv 32 := 0x00d40023.
Lemma F_6b978 : fetch_word Asan.M.loaded_segments (0x6b978 : word) = Some W_6b978.
Proof. vm_refl. Qed.
Lemma D_6b978 : decode_any W_6b978 = Some (Store SZ1 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b97c : bv 32 := 0x0310000f.
Lemma F_6b97c : fetch_word Asan.M.loaded_segments (0x6b97c : word) = Some W_6b97c.
Proof. vm_refl. Qed.
Lemma D_6b97c : decode_any W_6b97c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b980 : bv 32 := 0x000400a3.
Lemma F_6b980 : fetch_word Asan.M.loaded_segments (0x6b980 : word) = Some W_6b980.
Proof. vm_refl. Qed.
Lemma D_6b980 : decode_any W_6b980 = Some (Store SZ1 8 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b984 : bv 32 := 0x00073517.
Lemma F_6b984 : fetch_word Asan.M.loaded_segments (0x6b984 : word) = Some W_6b984.
Proof. vm_refl. Qed.
Lemma D_6b984 : decode_any W_6b984 = Some (Auipc 10 115, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b988 : bv 32 := 0x3bc50513.
Lemma F_6b988 : fetch_word Asan.M.loaded_segments (0x6b988 : word) = Some W_6b988.
Proof. vm_refl. Qed.
Lemma D_6b988 : decode_any W_6b988 = Some (OpImm ALU_ADD 10 10 956, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b98c : bv 32 := 0x02813083.
Lemma F_6b98c : fetch_word Asan.M.loaded_segments (0x6b98c : word) = Some W_6b98c.
Proof. vm_refl. Qed.
Lemma D_6b98c : decode_any W_6b98c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b990 : bv 32 := 0x02013403.
Lemma F_6b990 : fetch_word Asan.M.loaded_segments (0x6b990 : word) = Some W_6b990.
Proof. vm_refl. Qed.
Lemma D_6b990 : decode_any W_6b990 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b994 : bv 32 := 0x01813483.
Lemma F_6b994 : fetch_word Asan.M.loaded_segments (0x6b994 : word) = Some W_6b994.
Proof. vm_refl. Qed.
Lemma D_6b994 : decode_any W_6b994 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b998 : bv 32 := 0x01013903.
Lemma F_6b998 : fetch_word Asan.M.loaded_segments (0x6b998 : word) = Some W_6b998.
Proof. vm_refl. Qed.
Lemma D_6b998 : decode_any W_6b998 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b99c : bv 32 := 0x00813983.
Lemma F_6b99c : fetch_word Asan.M.loaded_segments (0x6b99c : word) = Some W_6b99c.
Proof. vm_refl. Qed.
Lemma D_6b99c : decode_any W_6b99c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9a0 : bv 32 := 0x03010113.
Lemma F_6b9a0 : fetch_word Asan.M.loaded_segments (0x6b9a0 : word) = Some W_6b9a0.
Proof. vm_refl. Qed.
Lemma D_6b9a0 : decode_any W_6b9a0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9a4 : bv 32 := 0x00008067.
Lemma F_6b9a4 : fetch_word Asan.M.loaded_segments (0x6b9a4 : word) = Some W_6b9a4.
Proof. vm_refl. Qed.
Lemma D_6b9a4 : decode_any W_6b9a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9a8 : bv 32 := 0x734070ef.
Lemma F_6b9a8 : fetch_word Asan.M.loaded_segments (0x6b9a8 : word) = Some W_6b9a8.
Proof. vm_refl. Qed.
Lemma D_6b9a8 : decode_any W_6b9a8 = Some (Jal 1 30516, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9ac : bv 32 := 0x00040503.
Lemma F_6b9ac : fetch_word Asan.M.loaded_segments (0x6b9ac : word) = Some W_6b9ac.
Proof. vm_refl. Qed.
Lemma D_6b9ac : decode_any W_6b9ac = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9b0 : bv 32 := 0xfc0516e3.
Lemma F_6b9b0 : fetch_word Asan.M.loaded_segments (0x6b9b0 : word) = Some W_6b9b0.
Proof. vm_refl. Qed.
Lemma D_6b9b0 : decode_any W_6b9b0 = Some (Branch BC_NE 10 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9b4 : bv 32 := 0xf29ff06f.
Lemma F_6b9b4 : fetch_word Asan.M.loaded_segments (0x6b9b4 : word) = Some W_6b9b4.
Proof. vm_refl. Qed.
Lemma D_6b9b4 : decode_any W_6b9b4 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.
