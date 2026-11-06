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

Definition W_4f8ec : bv 32 := 0x81010113.
Lemma F_4f8ec : fetch_word Asan.M.loaded_segments (0x4f8ec : word) = Some W_4f8ec.
Proof. vm_refl. Qed.
Lemma D_4f8ec : decode_any W_4f8ec = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f8f0 : bv 32 := 0x7e113423.
Lemma F_4f8f0 : fetch_word Asan.M.loaded_segments (0x4f8f0 : word) = Some W_4f8f0.
Proof. vm_refl. Qed.
Lemma D_4f8f0 : decode_any W_4f8f0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f8f4 : bv 32 := 0x7e813023.
Lemma F_4f8f4 : fetch_word Asan.M.loaded_segments (0x4f8f4 : word) = Some W_4f8f4.
Proof. vm_refl. Qed.
Lemma D_4f8f4 : decode_any W_4f8f4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f8f8 : bv 32 := 0x7c913c23.
Lemma F_4f8f8 : fetch_word Asan.M.loaded_segments (0x4f8f8 : word) = Some W_4f8f8.
Proof. vm_refl. Qed.
Lemma D_4f8f8 : decode_any W_4f8f8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f8fc : bv 32 := 0x7d213823.
Lemma F_4f8fc : fetch_word Asan.M.loaded_segments (0x4f8fc : word) = Some W_4f8fc.
Proof. vm_refl. Qed.
Lemma D_4f8fc : decode_any W_4f8fc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f900 : bv 32 := 0x7d313423.
Lemma F_4f900 : fetch_word Asan.M.loaded_segments (0x4f900 : word) = Some W_4f900.
Proof. vm_refl. Qed.
Lemma D_4f900 : decode_any W_4f900 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f904 : bv 32 := 0x7d413023.
Lemma F_4f904 : fetch_word Asan.M.loaded_segments (0x4f904 : word) = Some W_4f904.
Proof. vm_refl. Qed.
Lemma D_4f904 : decode_any W_4f904 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f908 : bv 32 := 0x7f010413.
Lemma F_4f908 : fetch_word Asan.M.loaded_segments (0x4f908 : word) = Some W_4f908.
Proof. vm_refl. Qed.
Lemma D_4f908 : decode_any W_4f908 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f90c : bv 32 := 0xfa010113.
Lemma F_4f90c : fetch_word Asan.M.loaded_segments (0x4f90c : word) = Some W_4f90c.
Proof. vm_refl. Qed.
Lemma D_4f90c : decode_any W_4f90c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f910 : bv 32 := 0x00060913.
Lemma F_4f910 : fetch_word Asan.M.loaded_segments (0x4f910 : word) = Some W_4f910.
Proof. vm_refl. Qed.
Lemma D_4f910 : decode_any W_4f910 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f914 : bv 32 := 0x00058493.
Lemma F_4f914 : fetch_word Asan.M.loaded_segments (0x4f914 : word) = Some W_4f914.
Proof. vm_refl. Qed.
Lemma D_4f914 : decode_any W_4f914 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f918 : bv 32 := 0x00050993.
Lemma F_4f918 : fetch_word Asan.M.loaded_segments (0x4f918 : word) = Some W_4f918.
Proof. vm_refl. Qed.
Lemma D_4f918 : decode_any W_4f918 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f91c : bv 32 := 0x6c8170ef.
Lemma F_4f91c : fetch_word Asan.M.loaded_segments (0x4f91c : word) = Some W_4f91c.
Proof. vm_refl. Qed.
Lemma D_4f91c : decode_any W_4f91c = Some (Jal 1 95944, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f920 : bv 32 := 0x00088597.
Lemma F_4f920 : fetch_word Asan.M.loaded_segments (0x4f920 : word) = Some W_4f920.
Proof. vm_refl. Qed.
Lemma D_4f920 : decode_any W_4f920 = Some (Auipc 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f924 : bv 32 := 0xda85b683.
Lemma F_4f924 : fetch_word Asan.M.loaded_segments (0x4f924 : word) = Some W_4f924.
Proof. vm_refl. Qed.
Lemma D_4f924 : decode_any W_4f924 = Some (Load SZ8 true 13 11 3496, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f928 : bv 32 := 0x00050a13.
Lemma F_4f928 : fetch_word Asan.M.loaded_segments (0x4f928 : word) = Some W_4f928.
Proof. vm_refl. Qed.
Lemma D_4f928 : decode_any W_4f928 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f92c : bv 32 := 0x00098513.
Lemma F_4f92c : fetch_word Asan.M.loaded_segments (0x4f92c : word) = Some W_4f92c.
Proof. vm_refl. Qed.
Lemma D_4f92c : decode_any W_4f92c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f930 : bv 32 := 0x00048593.
Lemma F_4f930 : fetch_word Asan.M.loaded_segments (0x4f930 : word) = Some W_4f930.
Proof. vm_refl. Qed.
Lemma D_4f930 : decode_any W_4f930 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f934 : bv 32 := 0x00090613.
Lemma F_4f934 : fetch_word Asan.M.loaded_segments (0x4f934 : word) = Some W_4f934.
Proof. vm_refl. Qed.
Lemma D_4f934 : decode_any W_4f934 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f938 : bv 32 := 0x000680e7.
Lemma F_4f938 : fetch_word Asan.M.loaded_segments (0x4f938 : word) = Some W_4f938.
Proof. vm_refl. Qed.
Lemma D_4f938 : decode_any W_4f938 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f93c : bv 32 := 0x060a0063.
Lemma F_4f93c : fetch_word Asan.M.loaded_segments (0x4f93c : word) = Some W_4f93c.
Proof. vm_refl. Qed.
Lemma D_4f93c : decode_any W_4f93c = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f940 : bv 32 := 0x04a05e63.
Lemma F_4f940 : fetch_word Asan.M.loaded_segments (0x4f940 : word) = Some W_4f940.
Proof. vm_refl. Qed.
Lemma D_4f940 : decode_any W_4f940 = Some (Branch BC_GE 0 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f944 : bv 32 := 0xfff4c593.
Lemma F_4f944 : fetch_word Asan.M.loaded_segments (0x4f944 : word) = Some W_4f944.
Proof. vm_refl. Qed.
Lemma D_4f944 : decode_any W_4f944 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f948 : bv 32 := 0x80040a13.
Lemma F_4f948 : fetch_word Asan.M.loaded_segments (0x4f948 : word) = Some W_4f948.
Proof. vm_refl. Qed.
Lemma D_4f948 : decode_any W_4f948 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f94c : bv 32 := 0xfb8a0a13.
Lemma F_4f94c : fetch_word Asan.M.loaded_segments (0x4f94c : word) = Some W_4f94c.
Proof. vm_refl. Qed.
Lemma D_4f94c : decode_any W_4f94c = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f950 : bv 32 := 0x06a5e863.
Lemma F_4f950 : fetch_word Asan.M.loaded_segments (0x4f950 : word) = Some W_4f950.
Proof. vm_refl. Qed.
Lemma D_4f950 : decode_any W_4f950 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f954 : bv 32 := 0xfbf50593.
Lemma F_4f954 : fetch_word Asan.M.loaded_segments (0x4f954 : word) = Some W_4f954.
Proof. vm_refl. Qed.
Lemma D_4f954 : decode_any W_4f954 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f958 : bv 32 := 0xfc000613.
Lemma F_4f958 : fetch_word Asan.M.loaded_segments (0x4f958 : word) = Some W_4f958.
Proof. vm_refl. Qed.
Lemma D_4f958 : decode_any W_4f958 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f95c : bv 32 := 0x0cc5ee63.
Lemma F_4f95c : fetch_word Asan.M.loaded_segments (0x4f95c : word) = Some W_4f95c.
Proof. vm_refl. Qed.
Lemma D_4f95c : decode_any W_4f95c = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f960 : bv 32 := 0x00086597.
Lemma F_4f960 : fetch_word Asan.M.loaded_segments (0x4f960 : word) = Some W_4f960.
Proof. vm_refl. Qed.
Lemma D_4f960 : decode_any W_4f960 = Some (Auipc 11 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f964 : bv 32 := 0xf585b583.
Lemma F_4f964 : fetch_word Asan.M.loaded_segments (0x4f964 : word) = Some W_4f964.
Proof. vm_refl. Qed.
Lemma D_4f964 : decode_any W_4f964 = Some (Load SZ8 true 11 11 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f968 : bv 32 := 0x00a486b3.
Lemma F_4f968 : fetch_word Asan.M.loaded_segments (0x4f968 : word) = Some W_4f968.
Proof. vm_refl. Qed.
Lemma D_4f968 : decode_any W_4f968 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f96c : bv 32 := 0x0005b603.
Lemma F_4f96c : fetch_word Asan.M.loaded_segments (0x4f96c : word) = Some W_4f96c.
Proof. vm_refl. Qed.
Lemma D_4f96c : decode_any W_4f96c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f970 : bv 32 := 0x0034d593.
Lemma F_4f970 : fetch_word Asan.M.loaded_segments (0x4f970 : word) = Some W_4f970.
Proof. vm_refl. Qed.
Lemma D_4f970 : decode_any W_4f970 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f974 : bv 32 := 0xfff68693.
Lemma F_4f974 : fetch_word Asan.M.loaded_segments (0x4f974 : word) = Some W_4f974.
Proof. vm_refl. Qed.
Lemma D_4f974 : decode_any W_4f974 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f978 : bv 32 := 0x0036d713.
Lemma F_4f978 : fetch_word Asan.M.loaded_segments (0x4f978 : word) = Some W_4f978.
Proof. vm_refl. Qed.
Lemma D_4f978 : decode_any W_4f978 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f97c : bv 32 := 0x00b605b3.
Lemma F_4f97c : fetch_word Asan.M.loaded_segments (0x4f97c : word) = Some W_4f97c.
Proof. vm_refl. Qed.
Lemma D_4f97c : decode_any W_4f97c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f980 : bv 32 := 0x00e60633.
Lemma F_4f980 : fetch_word Asan.M.loaded_segments (0x4f980 : word) = Some W_4f980.
Proof. vm_refl. Qed.
Lemma D_4f980 : decode_any W_4f980 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f984 : bv 32 := 0xff85f713.
Lemma F_4f984 : fetch_word Asan.M.loaded_segments (0x4f984 : word) = Some W_4f984.
Proof. vm_refl. Qed.
Lemma D_4f984 : decode_any W_4f984 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f988 : bv 32 := 0xff867793.
Lemma F_4f988 : fetch_word Asan.M.loaded_segments (0x4f988 : word) = Some W_4f988.
Proof. vm_refl. Qed.
Lemma D_4f988 : decode_any W_4f988 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f98c : bv 32 := 0x00073703.
Lemma F_4f98c : fetch_word Asan.M.loaded_segments (0x4f98c : word) = Some W_4f98c.
Proof. vm_refl. Qed.
Lemma D_4f98c : decode_any W_4f98c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f990 : bv 32 := 0x0007b783.
Lemma F_4f990 : fetch_word Asan.M.loaded_segments (0x4f990 : word) = Some W_4f990.
Proof. vm_refl. Qed.
Lemma D_4f990 : decode_any W_4f990 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f994 : bv 32 := 0x00e7e733.
Lemma F_4f994 : fetch_word Asan.M.loaded_segments (0x4f994 : word) = Some W_4f994.
Proof. vm_refl. Qed.
Lemma D_4f994 : decode_any W_4f994 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f998 : bv 32 := 0x14071663.
Lemma F_4f998 : fetch_word Asan.M.loaded_segments (0x4f998 : word) = Some W_4f998.
Proof. vm_refl. Qed.
Lemma D_4f998 : decode_any W_4f998 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f99c : bv 32 := 0x06010113.
Lemma F_4f99c : fetch_word Asan.M.loaded_segments (0x4f99c : word) = Some W_4f99c.
Proof. vm_refl. Qed.
Lemma D_4f99c : decode_any W_4f99c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9a0 : bv 32 := 0x7e813083.
Lemma F_4f9a0 : fetch_word Asan.M.loaded_segments (0x4f9a0 : word) = Some W_4f9a0.
Proof. vm_refl. Qed.
Lemma D_4f9a0 : decode_any W_4f9a0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9a4 : bv 32 := 0x7e013403.
Lemma F_4f9a4 : fetch_word Asan.M.loaded_segments (0x4f9a4 : word) = Some W_4f9a4.
Proof. vm_refl. Qed.
Lemma D_4f9a4 : decode_any W_4f9a4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9a8 : bv 32 := 0x7d813483.
Lemma F_4f9a8 : fetch_word Asan.M.loaded_segments (0x4f9a8 : word) = Some W_4f9a8.
Proof. vm_refl. Qed.
Lemma D_4f9a8 : decode_any W_4f9a8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9ac : bv 32 := 0x7d013903.
Lemma F_4f9ac : fetch_word Asan.M.loaded_segments (0x4f9ac : word) = Some W_4f9ac.
Proof. vm_refl. Qed.
Lemma D_4f9ac : decode_any W_4f9ac = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9b0 : bv 32 := 0x7c813983.
Lemma F_4f9b0 : fetch_word Asan.M.loaded_segments (0x4f9b0 : word) = Some W_4f9b0.
Proof. vm_refl. Qed.
Lemma D_4f9b0 : decode_any W_4f9b0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9b4 : bv 32 := 0x7c013a03.
Lemma F_4f9b4 : fetch_word Asan.M.loaded_segments (0x4f9b4 : word) = Some W_4f9b4.
Proof. vm_refl. Qed.
Lemma D_4f9b4 : decode_any W_4f9b4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9b8 : bv 32 := 0x7f010113.
Lemma F_4f9b8 : fetch_word Asan.M.loaded_segments (0x4f9b8 : word) = Some W_4f9b8.
Proof. vm_refl. Qed.
Lemma D_4f9b8 : decode_any W_4f9b8 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9bc : bv 32 := 0x00008067.
Lemma F_4f9bc : fetch_word Asan.M.loaded_segments (0x4f9bc : word) = Some W_4f9bc.
Proof. vm_refl. Qed.
Lemma D_4f9bc : decode_any W_4f9bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9c0 : bv 32 := 0x80040593.
Lemma F_4f9c0 : fetch_word Asan.M.loaded_segments (0x4f9c0 : word) = Some W_4f9c0.
Proof. vm_refl. Qed.
Lemma D_4f9c0 : decode_any W_4f9c0 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9c4 : bv 32 := 0xfc858593.
Lemma F_4f9c4 : fetch_word Asan.M.loaded_segments (0x4f9c4 : word) = Some W_4f9c4.
Proof. vm_refl. Qed.
Lemma D_4f9c4 : decode_any W_4f9c4 = Some (OpImm ALU_ADD 11 11 4040, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9c8 : bv 32 := 0x80040613.
Lemma F_4f9c8 : fetch_word Asan.M.loaded_segments (0x4f9c8 : word) = Some W_4f9c8.
Proof. vm_refl. Qed.
Lemma D_4f9c8 : decode_any W_4f9c8 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9cc : bv 32 := 0xfb860613.
Lemma F_4f9cc : fetch_word Asan.M.loaded_segments (0x4f9cc : word) = Some W_4f9cc.
Proof. vm_refl. Qed.
Lemma D_4f9cc : decode_any W_4f9cc = Some (OpImm ALU_ADD 12 12 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9d0 : bv 32 := 0x7ff60993.
Lemma F_4f9d0 : fetch_word Asan.M.loaded_segments (0x4f9d0 : word) = Some W_4f9d0.
Proof. vm_refl. Qed.
Lemma D_4f9d0 : decode_any W_4f9d0 = Some (OpImm ALU_ADD 19 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9d4 : bv 32 := 0x0009b4a3.
Lemma F_4f9d4 : fetch_word Asan.M.loaded_segments (0x4f9d4 : word) = Some W_4f9d4.
Proof. vm_refl. Qed.
Lemma D_4f9d4 : decode_any W_4f9d4 = Some (Store SZ8 19 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9d8 : bv 32 := 0x00ba3023.
Lemma F_4f9d8 : fetch_word Asan.M.loaded_segments (0x4f9d8 : word) = Some W_4f9d8.
Proof. vm_refl. Qed.
Lemma D_4f9d8 : decode_any W_4f9d8 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9dc : bv 32 := 0x000a3423.
Lemma F_4f9dc : fetch_word Asan.M.loaded_segments (0x4f9dc : word) = Some W_4f9dc.
Proof. vm_refl. Qed.
Lemma D_4f9dc : decode_any W_4f9dc = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9e0 : bv 32 := 0x00050913.
Lemma F_4f9e0 : fetch_word Asan.M.loaded_segments (0x4f9e0 : word) = Some W_4f9e0.
Proof. vm_refl. Qed.
Lemma D_4f9e0 : decode_any W_4f9e0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9e4 : bv 32 := 0x649300ef.
Lemma F_4f9e4 : fetch_word Asan.M.loaded_segments (0x4f9e4 : word) = Some W_4f9e4.
Proof. vm_refl. Qed.
Lemma D_4f9e4 : decode_any W_4f9e4 = Some (Jal 1 200264, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9e8 : bv 32 := 0x00050593.
Lemma F_4f9e8 : fetch_word Asan.M.loaded_segments (0x4f9e8 : word) = Some W_4f9e8.
Proof. vm_refl. Qed.
Lemma D_4f9e8 : decode_any W_4f9e8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9ec : bv 32 := 0x00086517.
Lemma F_4f9ec : fetch_word Asan.M.loaded_segments (0x4f9ec : word) = Some W_4f9ec.
Proof. vm_refl. Qed.
Lemma D_4f9ec : decode_any W_4f9ec = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9f0 : bv 32 := 0xebc53503.
Lemma F_4f9f0 : fetch_word Asan.M.loaded_segments (0x4f9f0 : word) = Some W_4f9f0.
Proof. vm_refl. Qed.
Lemma D_4f9f0 : decode_any W_4f9f0 = Some (Load SZ8 true 10 10 3772, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9f4 : bv 32 := 0x02154703.
Lemma F_4f9f4 : fetch_word Asan.M.loaded_segments (0x4f9f4 : word) = Some W_4f9f4.
Proof. vm_refl. Qed.
Lemma D_4f9f4 : decode_any W_4f9f4 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9f8 : bv 32 := 0x0089b4a3.
Lemma F_4f9f8 : fetch_word Asan.M.loaded_segments (0x4f9f8 : word) = Some W_4f9f8.
Proof. vm_refl. Qed.
Lemma D_4f9f8 : decode_any W_4f9f8 = Some (Store SZ8 19 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f9fc : bv 32 := 0x80040513.
Lemma F_4f9fc : fetch_word Asan.M.loaded_segments (0x4f9fc : word) = Some W_4f9fc.
Proof. vm_refl. Qed.
Lemma D_4f9fc : decode_any W_4f9fc = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa00 : bv 32 := 0xfb850513.
Lemma F_4fa00 : fetch_word Asan.M.loaded_segments (0x4fa00 : word) = Some W_4fa00.
Proof. vm_refl. Qed.
Lemma D_4fa00 : decode_any W_4fa00 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa04 : bv 32 := 0x0ff00793.
Lemma F_4fa04 : fetch_word Asan.M.loaded_segments (0x4fa04 : word) = Some W_4fa04.
Proof. vm_refl. Qed.
Lemma D_4fa04 : decode_any W_4fa04 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa08 : bv 32 := 0x00040613.
Lemma F_4fa08 : fetch_word Asan.M.loaded_segments (0x4fa08 : word) = Some W_4fa08.
Proof. vm_refl. Qed.
Lemma D_4fa08 : decode_any W_4fa08 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa0c : bv 32 := 0x00000693.
Lemma F_4fa0c : fetch_word Asan.M.loaded_segments (0x4fa0c : word) = Some W_4fa0c.
Proof. vm_refl. Qed.
Lemma D_4fa0c : decode_any W_4fa0c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa10 : bv 32 := 0x36c180ef.
Lemma F_4fa10 : fetch_word Asan.M.loaded_segments (0x4fa10 : word) = Some W_4fa10.
Proof. vm_refl. Qed.
Lemma D_4fa10 : decode_any W_4fa10 = Some (Jal 1 99180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa14 : bv 32 := 0x80040613.
Lemma F_4fa14 : fetch_word Asan.M.loaded_segments (0x4fa14 : word) = Some W_4fa14.
Proof. vm_refl. Qed.
Lemma D_4fa14 : decode_any W_4fa14 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa18 : bv 32 := 0xfb860613.
Lemma F_4fa18 : fetch_word Asan.M.loaded_segments (0x4fa18 : word) = Some W_4fa18.
Proof. vm_refl. Qed.
Lemma D_4fa18 : decode_any W_4fa18 = Some (OpImm ALU_ADD 12 12 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa1c : bv 32 := 0x00048513.
Lemma F_4fa1c : fetch_word Asan.M.loaded_segments (0x4fa1c : word) = Some W_4fa1c.
Proof. vm_refl. Qed.
Lemma D_4fa1c : decode_any W_4fa1c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa20 : bv 32 := 0x00090593.
Lemma F_4fa20 : fetch_word Asan.M.loaded_segments (0x4fa20 : word) = Some W_4fa20.
Proof. vm_refl. Qed.
Lemma D_4fa20 : decode_any W_4fa20 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa24 : bv 32 := 0x110150ef.
Lemma F_4fa24 : fetch_word Asan.M.loaded_segments (0x4fa24 : word) = Some W_4fa24.
Proof. vm_refl. Qed.
Lemma D_4fa24 : decode_any W_4fa24 = Some (Jal 1 86288, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa28 : bv 32 := 0x00090513.
Lemma F_4fa28 : fetch_word Asan.M.loaded_segments (0x4fa28 : word) = Some W_4fa28.
Proof. vm_refl. Qed.
Lemma D_4fa28 : decode_any W_4fa28 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa2c : bv 32 := 0xfbf90593.
Lemma F_4fa2c : fetch_word Asan.M.loaded_segments (0x4fa2c : word) = Some W_4fa2c.
Proof. vm_refl. Qed.
Lemma D_4fa2c : decode_any W_4fa2c = Some (OpImm ALU_ADD 11 18 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa30 : bv 32 := 0xfc000613.
Lemma F_4fa30 : fetch_word Asan.M.loaded_segments (0x4fa30 : word) = Some W_4fa30.
Proof. vm_refl. Qed.
Lemma D_4fa30 : decode_any W_4fa30 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa34 : bv 32 := 0xf2c5f6e3.
Lemma F_4fa34 : fetch_word Asan.M.loaded_segments (0x4fa34 : word) = Some W_4fa34.
Proof. vm_refl. Qed.
Lemma D_4fa34 : decode_any W_4fa34 = Some (Branch BC_GEU 11 12 7980, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa38 : bv 32 := 0x00050913.
Lemma F_4fa38 : fetch_word Asan.M.loaded_segments (0x4fa38 : word) = Some W_4fa38.
Proof. vm_refl. Qed.
Lemma D_4fa38 : decode_any W_4fa38 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa3c : bv 32 := 0x00048513.
Lemma F_4fa3c : fetch_word Asan.M.loaded_segments (0x4fa3c : word) = Some W_4fa3c.
Proof. vm_refl. Qed.
Lemma D_4fa3c : decode_any W_4fa3c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa40 : bv 32 := 0x00090593.
Lemma F_4fa40 : fetch_word Asan.M.loaded_segments (0x4fa40 : word) = Some W_4fa40.
Proof. vm_refl. Qed.
Lemma D_4fa40 : decode_any W_4fa40 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa44 : bv 32 := 0x6bd110ef.
Lemma F_4fa44 : fetch_word Asan.M.loaded_segments (0x4fa44 : word) = Some W_4fa44.
Proof. vm_refl. Qed.
Lemma D_4fa44 : decode_any W_4fa44 = Some (Jal 1 73404, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa48 : bv 32 := 0x00050493.
Lemma F_4fa48 : fetch_word Asan.M.loaded_segments (0x4fa48 : word) = Some W_4fa48.
Proof. vm_refl. Qed.
Lemma D_4fa48 : decode_any W_4fa48 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa4c : bv 32 := 0x00090513.
Lemma F_4fa4c : fetch_word Asan.M.loaded_segments (0x4fa4c : word) = Some W_4fa4c.
Proof. vm_refl. Qed.
Lemma D_4fa4c : decode_any W_4fa4c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa50 : bv 32 := 0xf40486e3.
Lemma F_4fa50 : fetch_word Asan.M.loaded_segments (0x4fa50 : word) = Some W_4fa50.
Proof. vm_refl. Qed.
Lemma D_4fa50 : decode_any W_4fa50 = Some (Branch BC_EQ 9 0 8012, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa54 : bv 32 := 0xfffc6517.
Lemma F_4fa54 : fetch_word Asan.M.loaded_segments (0x4fa54 : word) = Some W_4fa54.
Proof. vm_refl. Qed.
Lemma D_4fa54 : decode_any W_4fa54 = Some (Auipc 10 1048518, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa58 : bv 32 := 0x7c250513.
Lemma F_4fa58 : fetch_word Asan.M.loaded_segments (0x4fa58 : word) = Some W_4fa58.
Proof. vm_refl. Qed.
Lemma D_4fa58 : decode_any W_4fa58 = Some (OpImm ALU_ADD 10 10 1986, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa5c : bv 32 := 0x2cc190ef.
Lemma F_4fa5c : fetch_word Asan.M.loaded_segments (0x4fa5c : word) = Some W_4fa5c.
Proof. vm_refl. Qed.
Lemma D_4fa5c : decode_any W_4fa5c = Some (Jal 1 103116, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa60 : bv 32 := 0x00050593.
Lemma F_4fa60 : fetch_word Asan.M.loaded_segments (0x4fa60 : word) = Some W_4fa60.
Proof. vm_refl. Qed.
Lemma D_4fa60 : decode_any W_4fa60 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa64 : bv 32 := 0x00090513.
Lemma F_4fa64 : fetch_word Asan.M.loaded_segments (0x4fa64 : word) = Some W_4fa64.
Proof. vm_refl. Qed.
Lemma D_4fa64 : decode_any W_4fa64 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa68 : bv 32 := 0xf2059ae3.
Lemma F_4fa68 : fetch_word Asan.M.loaded_segments (0x4fa68 : word) = Some W_4fa68.
Proof. vm_refl. Qed.
Lemma D_4fa68 : decode_any W_4fa68 = Some (Branch BC_NE 11 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa6c : bv 32 := 0x324190ef.
Lemma F_4fa6c : fetch_word Asan.M.loaded_segments (0x4fa6c : word) = Some W_4fa6c.
Proof. vm_refl. Qed.
Lemma D_4fa6c : decode_any W_4fa6c = Some (Jal 1 103204, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa70 : bv 32 := 0x0a050663.
Lemma F_4fa70 : fetch_word Asan.M.loaded_segments (0x4fa70 : word) = Some W_4fa70.
Proof. vm_refl. Qed.
Lemma D_4fa70 : decode_any W_4fa70 = Some (Branch BC_EQ 10 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa74 : bv 32 := 0x80040513.
Lemma F_4fa74 : fetch_word Asan.M.loaded_segments (0x4fa74 : word) = Some W_4fa74.
Proof. vm_refl. Qed.
Lemma D_4fa74 : decode_any W_4fa74 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa78 : bv 32 := 0xfc850513.
Lemma F_4fa78 : fetch_word Asan.M.loaded_segments (0x4fa78 : word) = Some W_4fa78.
Proof. vm_refl. Qed.
Lemma D_4fa78 : decode_any W_4fa78 = Some (OpImm ALU_ADD 10 10 4040, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa7c : bv 32 := 0x80040593.
Lemma F_4fa7c : fetch_word Asan.M.loaded_segments (0x4fa7c : word) = Some W_4fa7c.
Proof. vm_refl. Qed.
Lemma D_4fa7c : decode_any W_4fa7c = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa80 : bv 32 := 0xfb858593.
Lemma F_4fa80 : fetch_word Asan.M.loaded_segments (0x4fa80 : word) = Some W_4fa80.
Proof. vm_refl. Qed.
Lemma D_4fa80 : decode_any W_4fa80 = Some (OpImm ALU_ADD 11 11 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa84 : bv 32 := 0x7ff58993.
Lemma F_4fa84 : fetch_word Asan.M.loaded_segments (0x4fa84 : word) = Some W_4fa84.
Proof. vm_refl. Qed.
Lemma D_4fa84 : decode_any W_4fa84 = Some (OpImm ALU_ADD 19 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa88 : bv 32 := 0x0009b4a3.
Lemma F_4fa88 : fetch_word Asan.M.loaded_segments (0x4fa88 : word) = Some W_4fa88.
Proof. vm_refl. Qed.
Lemma D_4fa88 : decode_any W_4fa88 = Some (Store SZ8 19 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa8c : bv 32 := 0x00aa3023.
Lemma F_4fa8c : fetch_word Asan.M.loaded_segments (0x4fa8c : word) = Some W_4fa8c.
Proof. vm_refl. Qed.
Lemma D_4fa8c : decode_any W_4fa8c = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa90 : bv 32 := 0x000a3423.
Lemma F_4fa90 : fetch_word Asan.M.loaded_segments (0x4fa90 : word) = Some W_4fa90.
Proof. vm_refl. Qed.
Lemma D_4fa90 : decode_any W_4fa90 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa94 : bv 32 := 0x599300ef.
Lemma F_4fa94 : fetch_word Asan.M.loaded_segments (0x4fa94 : word) = Some W_4fa94.
Proof. vm_refl. Qed.
Lemma D_4fa94 : decode_any W_4fa94 = Some (Jal 1 200088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa98 : bv 32 := 0x00050593.
Lemma F_4fa98 : fetch_word Asan.M.loaded_segments (0x4fa98 : word) = Some W_4fa98.
Proof. vm_refl. Qed.
Lemma D_4fa98 : decode_any W_4fa98 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fa9c : bv 32 := 0x00086517.
Lemma F_4fa9c : fetch_word Asan.M.loaded_segments (0x4fa9c : word) = Some W_4fa9c.
Proof. vm_refl. Qed.
Lemma D_4fa9c : decode_any W_4fa9c = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_4faa0 : bv 32 := 0xe0c53503.
Lemma F_4faa0 : fetch_word Asan.M.loaded_segments (0x4faa0 : word) = Some W_4faa0.
Proof. vm_refl. Qed.
Lemma D_4faa0 : decode_any W_4faa0 = Some (Load SZ8 true 10 10 3596, 4%Z).
Proof. vm_refl. Qed.

Definition W_4faa4 : bv 32 := 0x02154703.
Lemma F_4faa4 : fetch_word Asan.M.loaded_segments (0x4faa4 : word) = Some W_4faa4.
Proof. vm_refl. Qed.
Lemma D_4faa4 : decode_any W_4faa4 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4faa8 : bv 32 := 0x0089b4a3.
Lemma F_4faa8 : fetch_word Asan.M.loaded_segments (0x4faa8 : word) = Some W_4faa8.
Proof. vm_refl. Qed.
Lemma D_4faa8 : decode_any W_4faa8 = Some (Store SZ8 19 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4faac : bv 32 := 0x80040513.
Lemma F_4faac : fetch_word Asan.M.loaded_segments (0x4faac : word) = Some W_4faac.
Proof. vm_refl. Qed.
Lemma D_4faac : decode_any W_4faac = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fab0 : bv 32 := 0xfb850513.
Lemma F_4fab0 : fetch_word Asan.M.loaded_segments (0x4fab0 : word) = Some W_4fab0.
Proof. vm_refl. Qed.
Lemma D_4fab0 : decode_any W_4fab0 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fab4 : bv 32 := 0x0ff00793.
Lemma F_4fab4 : fetch_word Asan.M.loaded_segments (0x4fab4 : word) = Some W_4fab4.
Proof. vm_refl. Qed.
Lemma D_4fab4 : decode_any W_4fab4 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fab8 : bv 32 := 0x00040613.
Lemma F_4fab8 : fetch_word Asan.M.loaded_segments (0x4fab8 : word) = Some W_4fab8.
Proof. vm_refl. Qed.
Lemma D_4fab8 : decode_any W_4fab8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fabc : bv 32 := 0x00000693.
Lemma F_4fabc : fetch_word Asan.M.loaded_segments (0x4fabc : word) = Some W_4fabc.
Proof. vm_refl. Qed.
Lemma D_4fabc : decode_any W_4fabc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fac0 : bv 32 := 0x2bc180ef.
Lemma F_4fac0 : fetch_word Asan.M.loaded_segments (0x4fac0 : word) = Some W_4fac0.
Proof. vm_refl. Qed.
Lemma D_4fac0 : decode_any W_4fac0 = Some (Jal 1 99004, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fac4 : bv 32 := 0x80040513.
Lemma F_4fac4 : fetch_word Asan.M.loaded_segments (0x4fac4 : word) = Some W_4fac4.
Proof. vm_refl. Qed.
Lemma D_4fac4 : decode_any W_4fac4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fac8 : bv 32 := 0xfb850513.
Lemma F_4fac8 : fetch_word Asan.M.loaded_segments (0x4fac8 : word) = Some W_4fac8.
Proof. vm_refl. Qed.
Lemma D_4fac8 : decode_any W_4fac8 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4facc : bv 32 := 0x5cc190ef.
Lemma F_4facc : fetch_word Asan.M.loaded_segments (0x4facc : word) = Some W_4facc.
Proof. vm_refl. Qed.
Lemma D_4facc : decode_any W_4facc = Some (Jal 1 103884, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fad0 : bv 32 := 0x00050593.
Lemma F_4fad0 : fetch_word Asan.M.loaded_segments (0x4fad0 : word) = Some W_4fad0.
Proof. vm_refl. Qed.
Lemma D_4fad0 : decode_any W_4fad0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fad4 : bv 32 := 0x00040993.
Lemma F_4fad4 : fetch_word Asan.M.loaded_segments (0x4fad4 : word) = Some W_4fad4.
Proof. vm_refl. Qed.
Lemma D_4fad4 : decode_any W_4fad4 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fad8 : bv 32 := 0x00090513.
Lemma F_4fad8 : fetch_word Asan.M.loaded_segments (0x4fad8 : word) = Some W_4fad8.
Proof. vm_refl. Qed.
Lemma D_4fad8 : decode_any W_4fad8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fadc : bv 32 := 0xec0590e3.
Lemma F_4fadc : fetch_word Asan.M.loaded_segments (0x4fadc : word) = Some W_4fadc.
Proof. vm_refl. Qed.
Lemma D_4fadc : decode_any W_4fadc = Some (Branch BC_NE 11 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fae0 : bv 32 := 0x0400006f.
Lemma F_4fae0 : fetch_word Asan.M.loaded_segments (0x4fae0 : word) = Some W_4fae0.
Proof. vm_refl. Qed.
Lemma D_4fae0 : decode_any W_4fae0 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fae4 : bv 32 := 0x00060703.
Lemma F_4fae4 : fetch_word Asan.M.loaded_segments (0x4fae4 : word) = Some W_4fae4.
Proof. vm_refl. Qed.
Lemma D_4fae4 : decode_any W_4fae4 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fae8 : bv 32 := 0x0076f693.
Lemma F_4fae8 : fetch_word Asan.M.loaded_segments (0x4fae8 : word) = Some W_4fae8.
Proof. vm_refl. Qed.
Lemma D_4fae8 : decode_any W_4fae8 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4faec : bv 32 := 0x00e037b3.
Lemma F_4faec : fetch_word Asan.M.loaded_segments (0x4faec : word) = Some W_4faec.
Proof. vm_refl. Qed.
Lemma D_4faec : decode_any W_4faec = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4faf0 : bv 32 := 0x00e6a6b3.
Lemma F_4faf0 : fetch_word Asan.M.loaded_segments (0x4faf0 : word) = Some W_4faf0.
Proof. vm_refl. Qed.
Lemma D_4faf0 : decode_any W_4faf0 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4faf4 : bv 32 := 0x0016c693.
Lemma F_4faf4 : fetch_word Asan.M.loaded_segments (0x4faf4 : word) = Some W_4faf4.
Proof. vm_refl. Qed.
Lemma D_4faf4 : decode_any W_4faf4 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4faf8 : bv 32 := 0x00d7f6b3.
Lemma F_4faf8 : fetch_word Asan.M.loaded_segments (0x4faf8 : word) = Some W_4faf8.
Proof. vm_refl. Qed.
Lemma D_4faf8 : decode_any W_4faf8 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fafc : bv 32 := 0x00c5fa63.
Lemma F_4fafc : fetch_word Asan.M.loaded_segments (0x4fafc : word) = Some W_4fafc.
Proof. vm_refl. Qed.
Lemma D_4fafc : decode_any W_4fafc = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb00 : bv 32 := 0x0005c703.
Lemma F_4fb00 : fetch_word Asan.M.loaded_segments (0x4fb00 : word) = Some W_4fb00.
Proof. vm_refl. Qed.
Lemma D_4fb00 : decode_any W_4fb00 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb04 : bv 32 := 0x00158593.
Lemma F_4fb04 : fetch_word Asan.M.loaded_segments (0x4fb04 : word) = Some W_4fb04.
Proof. vm_refl. Qed.
Lemma D_4fb04 : decode_any W_4fb04 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb08 : bv 32 := 0x00d766b3.
Lemma F_4fb08 : fetch_word Asan.M.loaded_segments (0x4fb08 : word) = Some W_4fb08.
Proof. vm_refl. Qed.
Lemma D_4fb08 : decode_any W_4fb08 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb0c : bv 32 := 0xfec59ae3.
Lemma F_4fb0c : fetch_word Asan.M.loaded_segments (0x4fb0c : word) = Some W_4fb0c.
Proof. vm_refl. Qed.
Lemma D_4fb0c : decode_any W_4fb0c = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb10 : bv 32 := 0x0ff6f593.
Lemma F_4fb10 : fetch_word Asan.M.loaded_segments (0x4fb10 : word) = Some W_4fb10.
Proof. vm_refl. Qed.
Lemma D_4fb10 : decode_any W_4fb10 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb14 : bv 32 := 0xe80584e3.
Lemma F_4fb14 : fetch_word Asan.M.loaded_segments (0x4fb14 : word) = Some W_4fb14.
Proof. vm_refl. Qed.
Lemma D_4fb14 : decode_any W_4fb14 = Some (Branch BC_EQ 11 0 7816, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb18 : bv 32 := 0xf21ff06f.
Lemma F_4fb18 : fetch_word Asan.M.loaded_segments (0x4fb18 : word) = Some W_4fb18.
Proof. vm_refl. Qed.
Lemma D_4fb18 : decode_any W_4fb18 = Some (Jal 0 2096928, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb1c : bv 32 := 0x00040993.
Lemma F_4fb1c : fetch_word Asan.M.loaded_segments (0x4fb1c : word) = Some W_4fb1c.
Proof. vm_refl. Qed.
Lemma D_4fb1c : decode_any W_4fb1c = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb20 : bv 32 := 0x50d300ef.
Lemma F_4fb20 : fetch_word Asan.M.loaded_segments (0x4fb20 : word) = Some W_4fb20.
Proof. vm_refl. Qed.
Lemma D_4fb20 : decode_any W_4fb20 = Some (Jal 1 199948, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb24 : bv 32 := 0xfffc1597.
Lemma F_4fb24 : fetch_word Asan.M.loaded_segments (0x4fb24 : word) = Some W_4fb24.
Proof. vm_refl. Qed.
Lemma D_4fb24 : decode_any W_4fb24 = Some (Auipc 11 1048513, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb28 : bv 32 := 0x8e45b583.
Lemma F_4fb28 : fetch_word Asan.M.loaded_segments (0x4fb28 : word) = Some W_4fb28.
Proof. vm_refl. Qed.
Lemma D_4fb28 : decode_any W_4fb28 = Some (Load SZ8 true 11 11 2276, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb2c : bv 32 := 0x00ba3023.
Lemma F_4fb2c : fetch_word Asan.M.loaded_segments (0x4fb2c : word) = Some W_4fb2c.
Proof. vm_refl. Qed.
Lemma D_4fb2c : decode_any W_4fb2c = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb30 : bv 32 := 0x80040613.
Lemma F_4fb30 : fetch_word Asan.M.loaded_segments (0x4fb30 : word) = Some W_4fb30.
Proof. vm_refl. Qed.
Lemma D_4fb30 : decode_any W_4fb30 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb34 : bv 32 := 0xfb860613.
Lemma F_4fb34 : fetch_word Asan.M.loaded_segments (0x4fb34 : word) = Some W_4fb34.
Proof. vm_refl. Qed.
Lemma D_4fb34 : decode_any W_4fb34 = Some (OpImm ALU_ADD 12 12 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb38 : bv 32 := 0x00100713.
Lemma F_4fb38 : fetch_word Asan.M.loaded_segments (0x4fb38 : word) = Some W_4fb38.
Proof. vm_refl. Qed.
Lemma D_4fb38 : decode_any W_4fb38 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb3c : bv 32 := 0x00098593.
Lemma F_4fb3c : fetch_word Asan.M.loaded_segments (0x4fb3c : word) = Some W_4fb3c.
Proof. vm_refl. Qed.
Lemma D_4fb3c : decode_any W_4fb3c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb40 : bv 32 := 0x00048693.
Lemma F_4fb40 : fetch_word Asan.M.loaded_segments (0x4fb40 : word) = Some W_4fb40.
Proof. vm_refl. Qed.
Lemma D_4fb40 : decode_any W_4fb40 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb44 : bv 32 := 0x00090793.
Lemma F_4fb44 : fetch_word Asan.M.loaded_segments (0x4fb44 : word) = Some W_4fb44.
Proof. vm_refl. Qed.
Lemma D_4fb44 : decode_any W_4fb44 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb48 : bv 32 := 0x00000813.
Lemma F_4fb48 : fetch_word Asan.M.loaded_segments (0x4fb48 : word) = Some W_4fb48.
Proof. vm_refl. Qed.
Lemma D_4fb48 : decode_any W_4fb48 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb4c : bv 32 := 0x00000893.
Lemma F_4fb4c : fetch_word Asan.M.loaded_segments (0x4fb4c : word) = Some W_4fb4c.
Proof. vm_refl. Qed.
Lemma D_4fb4c : decode_any W_4fb4c = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb50 : bv 32 := 0x53c150ef.
Lemma F_4fb50 : fetch_word Asan.M.loaded_segments (0x4fb50 : word) = Some W_4fb50.
Proof. vm_refl. Qed.
Lemma D_4fb50 : decode_any W_4fb50 = Some (Jal 1 87356, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb54 : bv 32 := 0x00090513.
Lemma F_4fb54 : fetch_word Asan.M.loaded_segments (0x4fb54 : word) = Some W_4fb54.
Proof. vm_refl. Qed.
Lemma D_4fb54 : decode_any W_4fb54 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb58 : bv 32 := 0xe45ff06f.
Lemma F_4fb58 : fetch_word Asan.M.loaded_segments (0x4fb58 : word) = Some W_4fb58.
Proof. vm_refl. Qed.
Lemma D_4fb58 : decode_any W_4fb58 = Some (Jal 0 2096708, 4%Z).
Proof. vm_refl. Qed.
