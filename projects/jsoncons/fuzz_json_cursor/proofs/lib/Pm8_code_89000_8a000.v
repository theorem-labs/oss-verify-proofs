(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_89000 : bv 32 := 0x67052503.
Lemma F_89000 : fetch_word Asan.M.loaded_segments (0x89050 : word) = Some W_89000.
Proof. vm_refl. Qed.
Lemma D_89000 : decode_any W_89000 = Some (Load SZ4 true 10 10 1648, 4%Z).
Proof. vm_refl. Qed.

Definition W_89004 : bv 32 := 0x0230000f.
Lemma F_89004 : fetch_word Asan.M.loaded_segments (0x89054 : word) = Some W_89004.
Proof. vm_refl. Qed.
Lemma D_89004 : decode_any W_89004 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89008 : bv 32 := 0x00008067.
Lemma F_89008 : fetch_word Asan.M.loaded_segments (0x89058 : word) = Some W_89008.
Proof. vm_refl. Qed.
Lemma D_89008 : decode_any W_89008 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8900c : bv 32 := 0xfb010113.
Lemma F_8900c : fetch_word Asan.M.loaded_segments (0x8905c : word) = Some W_8900c.
Proof. vm_refl. Qed.
Lemma D_8900c : decode_any W_8900c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_89010 : bv 32 := 0x04113423.
Lemma F_89010 : fetch_word Asan.M.loaded_segments (0x89060 : word) = Some W_89010.
Proof. vm_refl. Qed.
Lemma D_89010 : decode_any W_89010 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_89014 : bv 32 := 0x04813023.
Lemma F_89014 : fetch_word Asan.M.loaded_segments (0x89064 : word) = Some W_89014.
Proof. vm_refl. Qed.
Lemma D_89014 : decode_any W_89014 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_89018 : bv 32 := 0x02913c23.
Lemma F_89018 : fetch_word Asan.M.loaded_segments (0x89068 : word) = Some W_89018.
Proof. vm_refl. Qed.
Lemma D_89018 : decode_any W_89018 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8901c : bv 32 := 0x03213823.
Lemma F_8901c : fetch_word Asan.M.loaded_segments (0x8906c : word) = Some W_8901c.
Proof. vm_refl. Qed.
Lemma D_8901c : decode_any W_8901c = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_89020 : bv 32 := 0x03313423.
Lemma F_89020 : fetch_word Asan.M.loaded_segments (0x89070 : word) = Some W_89020.
Proof. vm_refl. Qed.
Lemma D_89020 : decode_any W_89020 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_89024 : bv 32 := 0x03413023.
Lemma F_89024 : fetch_word Asan.M.loaded_segments (0x89074 : word) = Some W_89024.
Proof. vm_refl. Qed.
Lemma D_89024 : decode_any W_89024 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_89028 : bv 32 := 0x01513c23.
Lemma F_89028 : fetch_word Asan.M.loaded_segments (0x89078 : word) = Some W_89028.
Proof. vm_refl. Qed.
Lemma D_89028 : decode_any W_89028 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8902c : bv 32 := 0x01613823.
Lemma F_8902c : fetch_word Asan.M.loaded_segments (0x8907c : word) = Some W_8902c.
Proof. vm_refl. Qed.
Lemma D_8902c : decode_any W_8902c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_89030 : bv 32 := 0x01713423.
Lemma F_89030 : fetch_word Asan.M.loaded_segments (0x89080 : word) = Some W_89030.
Proof. vm_refl. Qed.
Lemma D_89030 : decode_any W_89030 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_89034 : bv 32 := 0x01813023.
Lemma F_89034 : fetch_word Asan.M.loaded_segments (0x89084 : word) = Some W_89034.
Proof. vm_refl. Qed.
Lemma D_89034 : decode_any W_89034 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89038 : bv 32 := 0x00078493.
Lemma F_89038 : fetch_word Asan.M.loaded_segments (0x89088 : word) = Some W_89038.
Proof. vm_refl. Qed.
Lemma D_89038 : decode_any W_89038 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8903c : bv 32 := 0x00070a93.
Lemma F_8903c : fetch_word Asan.M.loaded_segments (0x8908c : word) = Some W_8903c.
Proof. vm_refl. Qed.
Lemma D_8903c : decode_any W_8903c = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89040 : bv 32 := 0x00068a13.
Lemma F_89040 : fetch_word Asan.M.loaded_segments (0x89090 : word) = Some W_89040.
Proof. vm_refl. Qed.
Lemma D_89040 : decode_any W_89040 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89044 : bv 32 := 0x00060413.
Lemma F_89044 : fetch_word Asan.M.loaded_segments (0x89094 : word) = Some W_89044.
Proof. vm_refl. Qed.
Lemma D_89044 : decode_any W_89044 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89048 : bv 32 := 0x00058913.
Lemma F_89048 : fetch_word Asan.M.loaded_segments (0x89098 : word) = Some W_89048.
Proof. vm_refl. Qed.
Lemma D_89048 : decode_any W_89048 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8904c : bv 32 := 0x00050993.
Lemma F_8904c : fetch_word Asan.M.loaded_segments (0x8909c : word) = Some W_8904c.
Proof. vm_refl. Qed.
Lemma D_8904c : decode_any W_8904c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89050 : bv 32 := 0x00052423.
Lemma F_89050 : fetch_word Asan.M.loaded_segments (0x890a0 : word) = Some W_89050.
Proof. vm_refl. Qed.
Lemma D_89050 : decode_any W_89050 = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_89054 : bv 32 := 0xb10fe0ef.
Lemma F_89054 : fetch_word Asan.M.loaded_segments (0x890a4 : word) = Some W_89054.
Proof. vm_refl. Qed.
Lemma D_89054 : decode_any W_89054 = Some (Jal 1 2089744, 4%Z).
Proof. vm_refl. Qed.

Definition W_89058 : bv 32 := 0x0c050a63.
Lemma F_89058 : fetch_word Asan.M.loaded_segments (0x890a8 : word) = Some W_89058.
Proof. vm_refl. Qed.
Lemma D_89058 : decode_any W_89058 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_8905c : bv 32 := 0x219010ef.
Lemma F_8905c : fetch_word Asan.M.loaded_segments (0x890ac : word) = Some W_8905c.
Proof. vm_refl. Qed.
Lemma D_8905c : decode_any W_8905c = Some (Jal 1 6680, 4%Z).
Proof. vm_refl. Qed.

Definition W_89060 : bv 32 := 0x04050a63.
Lemma F_89060 : fetch_word Asan.M.loaded_segments (0x890b0 : word) = Some W_89060.
Proof. vm_refl. Qed.
Lemma D_89060 : decode_any W_89060 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_89064 : bv 32 := 0x7ff50c13.
Lemma F_89064 : fetch_word Asan.M.loaded_segments (0x890b4 : word) = Some W_89064.
Proof. vm_refl. Qed.
Lemma D_89064 : decode_any W_89064 = Some (OpImm ALU_ADD 24 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_89068 : bv 32 := 0x461c4583.
Lemma F_89068 : fetch_word Asan.M.loaded_segments (0x890b8 : word) = Some W_89068.
Proof. vm_refl. Qed.
Lemma D_89068 : decode_any W_89068 = Some (Load SZ1 false 11 24 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_8906c : bv 32 := 0x00100613.
Lemma F_8906c : fetch_word Asan.M.loaded_segments (0x890bc : word) = Some W_8906c.
Proof. vm_refl. Qed.
Lemma D_8906c : decode_any W_8906c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_89070 : bv 32 := 0x46cc00a3.
Lemma F_89070 : fetch_word Asan.M.loaded_segments (0x890c0 : word) = Some W_89070.
Proof. vm_refl. Qed.
Lemma D_89070 : decode_any W_89070 = Some (Store SZ1 24 12 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_89074 : bv 32 := 0x0a059a63.
Lemma F_89074 : fetch_word Asan.M.loaded_segments (0x890c4 : word) = Some W_89074.
Proof. vm_refl. Qed.
Lemma D_89074 : decode_any W_89074 = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_89078 : bv 32 := 0x00050b93.
Lemma F_89078 : fetch_word Asan.M.loaded_segments (0x890c8 : word) = Some W_89078.
Proof. vm_refl. Qed.
Lemma D_89078 : decode_any W_89078 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8907c : bv 32 := 0x3bd010ef.
Lemma F_8907c : fetch_word Asan.M.loaded_segments (0x890cc : word) = Some W_8907c.
Proof. vm_refl. Qed.
Lemma D_8907c : decode_any W_8907c = Some (Jal 1 7100, 4%Z).
Proof. vm_refl. Qed.

Definition W_89080 : bv 32 := 0x00050b13.
Lemma F_89080 : fetch_word Asan.M.loaded_segments (0x890d0 : word) = Some W_89080.
Proof. vm_refl. Qed.
Lemma D_89080 : decode_any W_89080 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89084 : bv 32 := 0x000b8513.
Lemma F_89084 : fetch_word Asan.M.loaded_segments (0x890d4 : word) = Some W_89084.
Proof. vm_refl. Qed.
Lemma D_89084 : decode_any W_89084 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89088 : bv 32 := 0x409010ef.
Lemma F_89088 : fetch_word Asan.M.loaded_segments (0x890d8 : word) = Some W_89088.
Proof. vm_refl. Qed.
Lemma D_89088 : decode_any W_89088 = Some (Jal 1 7176, 4%Z).
Proof. vm_refl. Qed.

Definition W_8908c : bv 32 := 0x00050813.
Lemma F_8908c : fetch_word Asan.M.loaded_segments (0x890dc : word) = Some W_8908c.
Proof. vm_refl. Qed.
Lemma D_8908c : decode_any W_8908c = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89090 : bv 32 := 0x060a8c63.
Lemma F_89090 : fetch_word Asan.M.loaded_segments (0x890e0 : word) = Some W_89090.
Proof. vm_refl. Qed.
Lemma D_89090 : decode_any W_89090 = Some (Branch BC_EQ 21 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_89094 : bv 32 := 0x00100893.
Lemma F_89094 : fetch_word Asan.M.loaded_segments (0x890e4 : word) = Some W_89094.
Proof. vm_refl. Qed.
Lemma D_89094 : decode_any W_89094 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_89098 : bv 32 := 0x00098513.
Lemma F_89098 : fetch_word Asan.M.loaded_segments (0x890e8 : word) = Some W_89098.
Proof. vm_refl. Qed.
Lemma D_89098 : decode_any W_89098 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8909c : bv 32 := 0x00048593.
Lemma F_8909c : fetch_word Asan.M.loaded_segments (0x890ec : word) = Some W_8909c.
Proof. vm_refl. Qed.
Lemma D_8909c : decode_any W_8909c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_890a0 : bv 32 := 0x00090613.
Lemma F_890a0 : fetch_word Asan.M.loaded_segments (0x890f0 : word) = Some W_890a0.
Proof. vm_refl. Qed.
Lemma D_890a0 : decode_any W_890a0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_890a4 : bv 32 := 0x00040693.
Lemma F_890a4 : fetch_word Asan.M.loaded_segments (0x890f4 : word) = Some W_890a4.
Proof. vm_refl. Qed.
Lemma D_890a4 : decode_any W_890a4 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_890a8 : bv 32 := 0x00000713.
Lemma F_890a8 : fetch_word Asan.M.loaded_segments (0x890f8 : word) = Some W_890a8.
Proof. vm_refl. Qed.
Lemma D_890a8 : decode_any W_890a8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_890ac : bv 32 := 0x000b0793.
Lemma F_890ac : fetch_word Asan.M.loaded_segments (0x890fc : word) = Some W_890ac.
Proof. vm_refl. Qed.
Lemma D_890ac : decode_any W_890ac = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_890b0 : bv 32 := 0x0740006f.
Lemma F_890b0 : fetch_word Asan.M.loaded_segments (0x89100 : word) = Some W_890b0.
Proof. vm_refl. Qed.
Lemma D_890b0 : decode_any W_890b0 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_89124 : bv 32 := 0x018190ef.
Lemma F_89124 : fetch_word Asan.M.loaded_segments (0x89174 : word) = Some W_89124.
Proof. vm_refl. Qed.
Lemma D_89124 : decode_any W_89124 = Some (Jal 1 102424, 4%Z).
Proof. vm_refl. Qed.

Definition W_89128 : bv 32 := 0x460c00a3.
Lemma F_89128 : fetch_word Asan.M.loaded_segments (0x89178 : word) = Some W_89128.
Proof. vm_refl. Qed.
Lemma D_89128 : decode_any W_89128 = Some (Store SZ1 24 0 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_8912c : bv 32 := 0x04813083.
Lemma F_8912c : fetch_word Asan.M.loaded_segments (0x8917c : word) = Some W_8912c.
Proof. vm_refl. Qed.
Lemma D_8912c : decode_any W_8912c = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_89130 : bv 32 := 0x04013403.
Lemma F_89130 : fetch_word Asan.M.loaded_segments (0x89180 : word) = Some W_89130.
Proof. vm_refl. Qed.
Lemma D_89130 : decode_any W_89130 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_89134 : bv 32 := 0x03813483.
Lemma F_89134 : fetch_word Asan.M.loaded_segments (0x89184 : word) = Some W_89134.
Proof. vm_refl. Qed.
Lemma D_89134 : decode_any W_89134 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_89138 : bv 32 := 0x03013903.
Lemma F_89138 : fetch_word Asan.M.loaded_segments (0x89188 : word) = Some W_89138.
Proof. vm_refl. Qed.
Lemma D_89138 : decode_any W_89138 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8913c : bv 32 := 0x02813983.
Lemma F_8913c : fetch_word Asan.M.loaded_segments (0x8918c : word) = Some W_8913c.
Proof. vm_refl. Qed.
Lemma D_8913c : decode_any W_8913c = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_89140 : bv 32 := 0x02013a03.
Lemma F_89140 : fetch_word Asan.M.loaded_segments (0x89190 : word) = Some W_89140.
Proof. vm_refl. Qed.
Lemma D_89140 : decode_any W_89140 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_89144 : bv 32 := 0x01813a83.
Lemma F_89144 : fetch_word Asan.M.loaded_segments (0x89194 : word) = Some W_89144.
Proof. vm_refl. Qed.
Lemma D_89144 : decode_any W_89144 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_89148 : bv 32 := 0x01013b03.
Lemma F_89148 : fetch_word Asan.M.loaded_segments (0x89198 : word) = Some W_89148.
Proof. vm_refl. Qed.
Lemma D_89148 : decode_any W_89148 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8914c : bv 32 := 0x00813b83.
Lemma F_8914c : fetch_word Asan.M.loaded_segments (0x8919c : word) = Some W_8914c.
Proof. vm_refl. Qed.
Lemma D_8914c : decode_any W_8914c = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_89150 : bv 32 := 0x00013c03.
Lemma F_89150 : fetch_word Asan.M.loaded_segments (0x891a0 : word) = Some W_89150.
Proof. vm_refl. Qed.
Lemma D_89150 : decode_any W_89150 = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89154 : bv 32 := 0x05010113.
Lemma F_89154 : fetch_word Asan.M.loaded_segments (0x891a4 : word) = Some W_89154.
Proof. vm_refl. Qed.
Lemma D_89154 : decode_any W_89154 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_89158 : bv 32 := 0x00008067.
Lemma F_89158 : fetch_word Asan.M.loaded_segments (0x891a8 : word) = Some W_89158.
Proof. vm_refl. Qed.
Lemma D_89158 : decode_any W_89158 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89c40 : bv 32 := 0xff010113.
Lemma F_89c40 : fetch_word Asan.M.loaded_segments (0x89c90 : word) = Some W_89c40.
Proof. vm_refl. Qed.
Lemma D_89c40 : decode_any W_89c40 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_89c44 : bv 32 := 0x00113423.
Lemma F_89c44 : fetch_word Asan.M.loaded_segments (0x89c94 : word) = Some W_89c44.
Proof. vm_refl. Qed.
Lemma D_89c44 : decode_any W_89c44 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_89c48 : bv 32 := 0x62d000ef.
Lemma F_89c48 : fetch_word Asan.M.loaded_segments (0x89c98 : word) = Some W_89c48.
Proof. vm_refl. Qed.
Lemma D_89c48 : decode_any W_89c48 = Some (Jal 1 3628, 4%Z).
Proof. vm_refl. Qed.

Definition W_89c4c : bv 32 := 0x00050c63.
Lemma F_89c4c : fetch_word Asan.M.loaded_segments (0x89c9c : word) = Some W_89c4c.
Proof. vm_refl. Qed.
Lemma D_89c4c : decode_any W_89c4c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_89c50 : bv 32 := 0x7ff50513.
Lemma F_89c50 : fetch_word Asan.M.loaded_segments (0x89ca0 : word) = Some W_89c50.
Proof. vm_refl. Qed.
Lemma D_89c50 : decode_any W_89c50 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_89c54 : bv 32 := 0x2f150513.
Lemma F_89c54 : fetch_word Asan.M.loaded_segments (0x89ca4 : word) = Some W_89c54.
Proof. vm_refl. Qed.
Lemma D_89c54 : decode_any W_89c54 = Some (OpImm ALU_ADD 10 10 753, 4%Z).
Proof. vm_refl. Qed.

Definition W_89c58 : bv 32 := 0x00813083.
Lemma F_89c58 : fetch_word Asan.M.loaded_segments (0x89ca8 : word) = Some W_89c58.
Proof. vm_refl. Qed.
Lemma D_89c58 : decode_any W_89c58 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_89c5c : bv 32 := 0x01010113.
Lemma F_89c5c : fetch_word Asan.M.loaded_segments (0x89cac : word) = Some W_89c5c.
Proof. vm_refl. Qed.
Lemma D_89c5c : decode_any W_89c5c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_89c60 : bv 32 := 0x00008067.
Lemma F_89c60 : fetch_word Asan.M.loaded_segments (0x89cb0 : word) = Some W_89c60.
Proof. vm_refl. Qed.
Lemma D_89c60 : decode_any W_89c60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

