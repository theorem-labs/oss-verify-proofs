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

Definition W_76ef8 : bv 32 := 0xf7010113.
Lemma F_76ef8 : fetch_word Asan.M.loaded_segments (0x76ef8 : word) = Some W_76ef8.
Proof. vm_refl. Qed.
Lemma D_76ef8 : decode_any W_76ef8 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_76efc : bv 32 := 0x08113423.
Lemma F_76efc : fetch_word Asan.M.loaded_segments (0x76efc : word) = Some W_76efc.
Proof. vm_refl. Qed.
Lemma D_76efc : decode_any W_76efc = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f00 : bv 32 := 0x08813023.
Lemma F_76f00 : fetch_word Asan.M.loaded_segments (0x76f00 : word) = Some W_76f00.
Proof. vm_refl. Qed.
Lemma D_76f00 : decode_any W_76f00 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f04 : bv 32 := 0x06913c23.
Lemma F_76f04 : fetch_word Asan.M.loaded_segments (0x76f04 : word) = Some W_76f04.
Proof. vm_refl. Qed.
Lemma D_76f04 : decode_any W_76f04 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f08 : bv 32 := 0x07213823.
Lemma F_76f08 : fetch_word Asan.M.loaded_segments (0x76f08 : word) = Some W_76f08.
Proof. vm_refl. Qed.
Lemma D_76f08 : decode_any W_76f08 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f0c : bv 32 := 0x07313423.
Lemma F_76f0c : fetch_word Asan.M.loaded_segments (0x76f0c : word) = Some W_76f0c.
Proof. vm_refl. Qed.
Lemma D_76f0c : decode_any W_76f0c = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f10 : bv 32 := 0x07413023.
Lemma F_76f10 : fetch_word Asan.M.loaded_segments (0x76f10 : word) = Some W_76f10.
Proof. vm_refl. Qed.
Lemma D_76f10 : decode_any W_76f10 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f14 : bv 32 := 0x05513c23.
Lemma F_76f14 : fetch_word Asan.M.loaded_segments (0x76f14 : word) = Some W_76f14.
Proof. vm_refl. Qed.
Lemma D_76f14 : decode_any W_76f14 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f18 : bv 32 := 0x05613823.
Lemma F_76f18 : fetch_word Asan.M.loaded_segments (0x76f18 : word) = Some W_76f18.
Proof. vm_refl. Qed.
Lemma D_76f18 : decode_any W_76f18 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f1c : bv 32 := 0x05713423.
Lemma F_76f1c : fetch_word Asan.M.loaded_segments (0x76f1c : word) = Some W_76f1c.
Proof. vm_refl. Qed.
Lemma D_76f1c : decode_any W_76f1c = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f20 : bv 32 := 0x05813023.
Lemma F_76f20 : fetch_word Asan.M.loaded_segments (0x76f20 : word) = Some W_76f20.
Proof. vm_refl. Qed.
Lemma D_76f20 : decode_any W_76f20 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f24 : bv 32 := 0x03913c23.
Lemma F_76f24 : fetch_word Asan.M.loaded_segments (0x76f24 : word) = Some W_76f24.
Proof. vm_refl. Qed.
Lemma D_76f24 : decode_any W_76f24 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f28 : bv 32 := 0x03a13823.
Lemma F_76f28 : fetch_word Asan.M.loaded_segments (0x76f28 : word) = Some W_76f28.
Proof. vm_refl. Qed.
Lemma D_76f28 : decode_any W_76f28 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f2c : bv 32 := 0x03b13423.
Lemma F_76f2c : fetch_word Asan.M.loaded_segments (0x76f2c : word) = Some W_76f2c.
Proof. vm_refl. Qed.
Lemma D_76f2c : decode_any W_76f2c = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f30 : bv 32 := 0x00058913.
Lemma F_76f30 : fetch_word Asan.M.loaded_segments (0x76f30 : word) = Some W_76f30.
Proof. vm_refl. Qed.
Lemma D_76f30 : decode_any W_76f30 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f34 : bv 32 := 0x0005f597.
Lemma F_76f34 : fetch_word Asan.M.loaded_segments (0x76f34 : word) = Some W_76f34.
Proof. vm_refl. Qed.
Lemma D_76f34 : decode_any W_76f34 = Some (Auipc 11 95, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f38 : bv 32 := 0x9745b583.
Lemma F_76f38 : fetch_word Asan.M.loaded_segments (0x76f38 : word) = Some W_76f38.
Proof. vm_refl. Qed.
Lemma D_76f38 : decode_any W_76f38 = Some (Load SZ8 true 11 11 2420, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f3c : bv 32 := 0x0895c583.
Lemma F_76f3c : fetch_word Asan.M.loaded_segments (0x76f3c : word) = Some W_76f3c.
Proof. vm_refl. Qed.
Lemma D_76f3c : decode_any W_76f3c = Some (Load SZ1 false 11 11 137, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f40 : bv 32 := 0x18058a63.
Lemma F_76f40 : fetch_word Asan.M.loaded_segments (0x76f40 : word) = Some W_76f40.
Proof. vm_refl. Qed.
Lemma D_76f40 : decode_any W_76f40 = Some (Branch BC_EQ 11 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f44 : bv 32 := 0x00050993.
Lemma F_76f44 : fetch_word Asan.M.loaded_segments (0x76f44 : word) = Some W_76f44.
Proof. vm_refl. Qed.
Lemma D_76f44 : decode_any W_76f44 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f48 : bv 32 := 0x0005f517.
Lemma F_76f48 : fetch_word Asan.M.loaded_segments (0x76f48 : word) = Some W_76f48.
Proof. vm_refl. Qed.
Lemma D_76f48 : decode_any W_76f48 = Some (Auipc 10 95, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f4c : bv 32 := 0x9c053d03.
Lemma F_76f4c : fetch_word Asan.M.loaded_segments (0x76f4c : word) = Some W_76f4c.
Proof. vm_refl. Qed.
Lemma D_76f4c : decode_any W_76f4c = Some (Load SZ8 true 26 10 2496, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f50 : bv 32 := 0x0009ba03.
Lemma F_76f50 : fetch_word Asan.M.loaded_segments (0x76f50 : word) = Some W_76f50.
Proof. vm_refl. Qed.
Lemma D_76f50 : decode_any W_76f50 = Some (Load SZ8 true 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f54 : bv 32 := 0x0005f517.
Lemma F_76f54 : fetch_word Asan.M.loaded_segments (0x76f54 : word) = Some W_76f54.
Proof. vm_refl. Qed.
Lemma D_76f54 : decode_any W_76f54 = Some (Auipc 10 95, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f58 : bv 32 := 0x000d2583.
Lemma F_76f58 : fetch_word Asan.M.loaded_segments (0x76f58 : word) = Some W_76f58.
Proof. vm_refl. Qed.
Lemma D_76f58 : decode_any W_76f58 = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f5c : bv 32 := 0x72c53a83.
Lemma F_76f5c : fetch_word Asan.M.loaded_segments (0x76f5c : word) = Some W_76f5c.
Proof. vm_refl. Qed.
Lemma D_76f5c : decode_any W_76f5c = Some (Load SZ8 true 21 10 1836, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f60 : bv 32 := 0x00300513.
Lemma F_76f60 : fetch_word Asan.M.loaded_segments (0x76f60 : word) = Some W_76f60.
Proof. vm_refl. Qed.
Lemma D_76f60 : decode_any W_76f60 = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f64 : bv 32 := 0x004a8ab3.
Lemma F_76f64 : fetch_word Asan.M.loaded_segments (0x76f64 : word) = Some W_76f64.
Proof. vm_refl. Qed.
Lemma D_76f64 : decode_any W_76f64 = Some (Op ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f68 : bv 32 := 0x1ea5fa63.
Lemma F_76f68 : fetch_word Asan.M.loaded_segments (0x76f68 : word) = Some W_76f68.
Proof. vm_refl. Qed.
Lemma D_76f68 : decode_any W_76f68 = Some (Branch BC_GEU 11 10 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f6c : bv 32 := 0x000abb03.
Lemma F_76f6c : fetch_word Asan.M.loaded_segments (0x76f6c : word) = Some W_76f6c.
Proof. vm_refl. Qed.
Lemma D_76f6c : decode_any W_76f6c = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f70 : bv 32 := 0xfff00513.
Lemma F_76f70 : fetch_word Asan.M.loaded_segments (0x76f70 : word) = Some W_76f70.
Proof. vm_refl. Qed.
Lemma D_76f70 : decode_any W_76f70 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f74 : bv 32 := 0x0230000f.
Lemma F_76f74 : fetch_word Asan.M.loaded_segments (0x76f74 : word) = Some W_76f74.
Proof. vm_refl. Qed.
Lemma D_76f74 : decode_any W_76f74 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f78 : bv 32 := 0x14ab0e63.
Lemma F_76f78 : fetch_word Asan.M.loaded_segments (0x76f78 : word) = Some W_76f78.
Proof. vm_refl. Qed.
Lemma D_76f78 : decode_any W_76f78 = Some (Branch BC_EQ 22 10 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f7c : bv 32 := 0x080b1263.
Lemma F_76f7c : fetch_word Asan.M.loaded_segments (0x76f7c : word) = Some W_76f7c.
Proof. vm_refl. Qed.
Lemma D_76f7c : decode_any W_76f7c = Some (Branch BC_NE 22 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f80 : bv 32 := 0x00060c13.
Lemma F_76f80 : fetch_word Asan.M.loaded_segments (0x76f80 : word) = Some W_76f80.
Proof. vm_refl. Qed.
Lemma D_76f80 : decode_any W_76f80 = Some (OpImm ALU_ADD 24 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f84 : bv 32 := 0x00068493.
Lemma F_76f84 : fetch_word Asan.M.loaded_segments (0x76f84 : word) = Some W_76f84.
Proof. vm_refl. Qed.
Lemma D_76f84 : decode_any W_76f84 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f88 : bv 32 := 0xfff9d517.
Lemma F_76f88 : fetch_word Asan.M.loaded_segments (0x76f88 : word) = Some W_76f88.
Proof. vm_refl. Qed.
Lemma D_76f88 : decode_any W_76f88 = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f8c : bv 32 := 0x00001bb7.
Lemma F_76f8c : fetch_word Asan.M.loaded_segments (0x76f8c : word) = Some W_76f8c.
Proof. vm_refl. Qed.
Lemma D_76f8c : decode_any W_76f8c = Some (Lui 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f90 : bv 32 := 0x00d50593.
Lemma F_76f90 : fetch_word Asan.M.loaded_segments (0x76f90 : word) = Some W_76f90.
Proof. vm_refl. Qed.
Lemma D_76f90 : decode_any W_76f90 = Some (OpImm ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f94 : bv 32 := 0xff8b8b9b.
Lemma F_76f94 : fetch_word Asan.M.loaded_segments (0x76f94 : word) = Some W_76f94.
Proof. vm_refl. Qed.
Lemma D_76f94 : decode_any W_76f94 = Some (OpImm32 23 23 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f98 : bv 32 := 0x000b8513.
Lemma F_76f98 : fetch_word Asan.M.loaded_segments (0x76f98 : word) = Some W_76f98.
Proof. vm_refl. Qed.
Lemma D_76f98 : decode_any W_76f98 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76f9c : bv 32 := 0x00000613.
Lemma F_76f9c : fetch_word Asan.M.loaded_segments (0x76f9c : word) = Some W_76f9c.
Proof. vm_refl. Qed.
Lemma D_76f9c : decode_any W_76f9c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fa0 : bv 32 := 0xa90fc0ef.
Lemma F_76fa0 : fetch_word Asan.M.loaded_segments (0x76fa0 : word) = Some W_76fa0.
Proof. vm_refl. Qed.
Lemma D_76fa0 : decode_any W_76fa0 = Some (Jal 1 2081424, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fa4 : bv 32 := 0x00050b13.
Lemma F_76fa4 : fetch_word Asan.M.loaded_segments (0x76fa4 : word) = Some W_76fa4.
Proof. vm_refl. Qed.
Lemma D_76fa4 : decode_any W_76fa4 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fa8 : bv 32 := 0x160ab42f.
Lemma F_76fa8 : fetch_word Asan.M.loaded_segments (0x76fa8 : word) = Some W_76fa8.
Proof. vm_refl. Qed.
Lemma D_76fa8 : decode_any W_76fa8 = Some (Lr AD true true 8 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fac : bv 32 := 0x02041c63.
Lemma F_76fac : fetch_word Asan.M.loaded_segments (0x76fac : word) = Some W_76fac.
Proof. vm_refl. Qed.
Lemma D_76fac : decode_any W_76fac = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fb0 : bv 32 := 0x1b6ab52f.
Lemma F_76fb0 : fetch_word Asan.M.loaded_segments (0x76fb0 : word) = Some W_76fb0.
Proof. vm_refl. Qed.
Lemma D_76fb0 : decode_any W_76fb0 = Some (Sc AD false true 10 21 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fb4 : bv 32 := 0xfe051ae3.
Lemma F_76fb4 : fetch_word Asan.M.loaded_segments (0x76fb4 : word) = Some W_76fb4.
Proof. vm_refl. Qed.
Lemma D_76fb4 : decode_any W_76fb4 = Some (Branch BC_NE 10 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fb8 : bv 32 := 0x000f9517.
Lemma F_76fb8 : fetch_word Asan.M.loaded_segments (0x76fb8 : word) = Some W_76fb8.
Proof. vm_refl. Qed.
Lemma D_76fb8 : decode_any W_76fb8 = Some (Auipc 10 249, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fbc : bv 32 := 0x8c050513.
Lemma F_76fbc : fetch_word Asan.M.loaded_segments (0x76fbc : word) = Some W_76fbc.
Proof. vm_refl. Qed.
Lemma D_76fbc : decode_any W_76fbc = Some (OpImm ALU_ADD 10 10 2240, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fc0 : bv 32 := 0x00100593.
Lemma F_76fc0 : fetch_word Asan.M.loaded_segments (0x76fc0 : word) = Some W_76fc0.
Proof. vm_refl. Qed.
Lemma D_76fc0 : decode_any W_76fc0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fc4 : bv 32 := 0x00b5362f.
Lemma F_76fc4 : fetch_word Asan.M.loaded_segments (0x76fc4 : word) = Some W_76fc4.
Proof. vm_refl. Qed.
Lemma D_76fc4 : decode_any W_76fc4 = Some (Amo AMO_ADD AD false false 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fc8 : bv 32 := 0x000d2503.
Lemma F_76fc8 : fetch_word Asan.M.loaded_segments (0x76fc8 : word) = Some W_76fc8.
Proof. vm_refl. Qed.
Lemma D_76fc8 : decode_any W_76fc8 = Some (Load SZ4 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fcc : bv 32 := 0x02a5f663.
Lemma F_76fcc : fetch_word Asan.M.loaded_segments (0x76fcc : word) = Some W_76fcc.
Proof. vm_refl. Qed.
Lemma D_76fcc : decode_any W_76fcc = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fd0 : bv 32 := 0xfff9d517.
Lemma F_76fd0 : fetch_word Asan.M.loaded_segments (0x76fd0 : word) = Some W_76fd0.
Proof. vm_refl. Qed.
Lemma D_76fd0 : decode_any W_76fd0 = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fd4 : bv 32 := 0xfd450513.
Lemma F_76fd4 : fetch_word Asan.M.loaded_segments (0x76fd4 : word) = Some W_76fd4.
Proof. vm_refl. Qed.
Lemma D_76fd4 : decode_any W_76fd4 = Some (OpImm ALU_ADD 10 10 4052, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fd8 : bv 32 := 0x000a8593.
Lemma F_76fd8 : fetch_word Asan.M.loaded_segments (0x76fd8 : word) = Some W_76fd8.
Proof. vm_refl. Qed.
Lemma D_76fd8 : decode_any W_76fd8 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fdc : bv 32 := 0xfacfd0ef.
Lemma F_76fdc : fetch_word Asan.M.loaded_segments (0x76fdc : word) = Some W_76fdc.
Proof. vm_refl. Qed.
Lemma D_76fdc : decode_any W_76fdc = Some (Jal 1 2086828, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fe0 : bv 32 := 0x0180006f.
Lemma F_76fe0 : fetch_word Asan.M.loaded_segments (0x76fe0 : word) = Some W_76fe0.
Proof. vm_refl. Qed.
Lemma D_76fe0 : decode_any W_76fe0 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fe4 : bv 32 := 0x000b0513.
Lemma F_76fe4 : fetch_word Asan.M.loaded_segments (0x76fe4 : word) = Some W_76fe4.
Proof. vm_refl. Qed.
Lemma D_76fe4 : decode_any W_76fe4 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fe8 : bv 32 := 0x000b8593.
Lemma F_76fe8 : fetch_word Asan.M.loaded_segments (0x76fe8 : word) = Some W_76fe8.
Proof. vm_refl. Qed.
Lemma D_76fe8 : decode_any W_76fe8 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76fec : bv 32 := 0x00000613.
Lemma F_76fec : fetch_word Asan.M.loaded_segments (0x76fec : word) = Some W_76fec.
Proof. vm_refl. Qed.
Lemma D_76fec : decode_any W_76fec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76ff0 : bv 32 := 0xbc0fc0ef.
Lemma F_76ff0 : fetch_word Asan.M.loaded_segments (0x76ff0 : word) = Some W_76ff0.
Proof. vm_refl. Qed.
Lemma D_76ff0 : decode_any W_76ff0 = Some (Jal 1 2081728, 4%Z).
Proof. vm_refl. Qed.

Definition W_76ff4 : bv 32 := 0x00040b13.
Lemma F_76ff4 : fetch_word Asan.M.loaded_segments (0x76ff4 : word) = Some W_76ff4.
Proof. vm_refl. Qed.
Lemma D_76ff4 : decode_any W_76ff4 = Some (OpImm ALU_ADD 22 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76ff8 : bv 32 := 0x00048693.
Lemma F_76ff8 : fetch_word Asan.M.loaded_segments (0x76ff8 : word) = Some W_76ff8.
Proof. vm_refl. Qed.
Lemma D_76ff8 : decode_any W_76ff8 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_76ffc : bv 32 := 0x000c0613.
Lemma F_76ffc : fetch_word Asan.M.loaded_segments (0x76ffc : word) = Some W_76ffc.
Proof. vm_refl. Qed.
Lemma D_76ffc : decode_any W_76ffc = Some (OpImm ALU_ADD 12 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77000 : bv 32 := 0x0c0b0a63.
Lemma F_77000 : fetch_word Asan.M.loaded_segments (0x77000 : word) = Some W_77000.
Proof. vm_refl. Qed.
Lemma D_77000 : decode_any W_77000 = Some (Branch BC_EQ 22 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_77004 : bv 32 := 0x00c13823.
Lemma F_77004 : fetch_word Asan.M.loaded_segments (0x77004 : word) = Some W_77004.
Proof. vm_refl. Qed.
Lemma D_77004 : decode_any W_77004 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_77008 : bv 32 := 0x00d13c23.
Lemma F_77008 : fetch_word Asan.M.loaded_segments (0x77008 : word) = Some W_77008.
Proof. vm_refl. Qed.
Lemma D_77008 : decode_any W_77008 = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7700c : bv 32 := 0x0ff00513.
Lemma F_7700c : fetch_word Asan.M.loaded_segments (0x7700c : word) = Some W_7700c.
Proof. vm_refl. Qed.
Lemma D_7700c : decode_any W_7700c = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_77010 : bv 32 := 0x0aaa6863.
Lemma F_77010 : fetch_word Asan.M.loaded_segments (0x77010 : word) = Some W_77010.
Proof. vm_refl. Qed.
Lemma D_77010 : decode_any W_77010 = Some (Branch BC_LTU 20 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_77014 : bv 32 := 0xfff00d93.
Lemma F_77014 : fetch_word Asan.M.loaded_segments (0x77014 : word) = Some W_77014.
Proof. vm_refl. Qed.
Lemma D_77014 : decode_any W_77014 = Some (OpImm ALU_ADD 27 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_77018 : bv 32 := 0x0fe00c93.
Lemma F_77018 : fetch_word Asan.M.loaded_segments (0x77018 : word) = Some W_77018.
Proof. vm_refl. Qed.
Lemma D_77018 : decode_any W_77018 = Some (OpImm ALU_ADD 25 0 254, 4%Z).
Proof. vm_refl. Qed.

Definition W_7701c : bv 32 := 0xfff9d517.
Lemma F_7701c : fetch_word Asan.M.loaded_segments (0x7701c : word) = Some W_7701c.
Proof. vm_refl. Qed.
Lemma D_7701c : decode_any W_7701c = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_77020 : bv 32 := 0x00001c37.
Lemma F_77020 : fetch_word Asan.M.loaded_segments (0x77020 : word) = Some W_77020.
Proof. vm_refl. Qed.
Lemma D_77020 : decode_any W_77020 = Some (Lui 24 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_77024 : bv 32 := 0x000f9597.
Lemma F_77024 : fetch_word Asan.M.loaded_segments (0x77024 : word) = Some W_77024.
Proof. vm_refl. Qed.
Lemma D_77024 : decode_any W_77024 = Some (Auipc 11 249, 4%Z).
Proof. vm_refl. Qed.

Definition W_77028 : bv 32 := 0xfff9d617.
Lemma F_77028 : fetch_word Asan.M.loaded_segments (0x77028 : word) = Some W_77028.
Proof. vm_refl. Qed.
Lemma D_77028 : decode_any W_77028 = Some (Auipc 12 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_7702c : bv 32 := 0xf7950b93.
Lemma F_7702c : fetch_word Asan.M.loaded_segments (0x7702c : word) = Some W_7702c.
Proof. vm_refl. Qed.
Lemma D_7702c : decode_any W_7702c = Some (OpImm ALU_ADD 23 10 3961, 4%Z).
Proof. vm_refl. Qed.

Definition W_77030 : bv 32 := 0xff8c0c1b.
Lemma F_77030 : fetch_word Asan.M.loaded_segments (0x77030 : word) = Some W_77030.
Proof. vm_refl. Qed.
Lemma D_77030 : decode_any W_77030 = Some (OpImm32 24 24 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_77034 : bv 32 := 0x85458413.
Lemma F_77034 : fetch_word Asan.M.loaded_segments (0x77034 : word) = Some W_77034.
Proof. vm_refl. Qed.
Lemma D_77034 : decode_any W_77034 = Some (OpImm ALU_ADD 8 11 2132, 4%Z).
Proof. vm_refl. Qed.

Definition W_77038 : bv 32 := 0xf7c60513.
Lemma F_77038 : fetch_word Asan.M.loaded_segments (0x77038 : word) = Some W_77038.
Proof. vm_refl. Qed.
Lemma D_77038 : decode_any W_77038 = Some (OpImm ALU_ADD 10 12 3964, 4%Z).
Proof. vm_refl. Qed.

Definition W_7703c : bv 32 := 0x00a13423.
Lemma F_7703c : fetch_word Asan.M.loaded_segments (0x7703c : word) = Some W_7703c.
Proof. vm_refl. Qed.
Lemma D_7703c : decode_any W_7703c = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_77040 : bv 32 := 0x0140006f.
Lemma F_77040 : fetch_word Asan.M.loaded_segments (0x77040 : word) = Some W_77040.
Proof. vm_refl. Qed.
Lemma D_77040 : decode_any W_77040 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_77044 : bv 32 := 0x00000513.
Lemma F_77044 : fetch_word Asan.M.loaded_segments (0x77044 : word) = Some W_77044.
Proof. vm_refl. Qed.
Lemma D_77044 : decode_any W_77044 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77048 : bv 32 := 0xf01a0a13.
Lemma F_77048 : fetch_word Asan.M.loaded_segments (0x77048 : word) = Some W_77048.
Proof. vm_refl. Qed.
Lemma D_77048 : decode_any W_77048 = Some (OpImm ALU_ADD 20 20 3841, 4%Z).
Proof. vm_refl. Qed.

Definition W_7704c : bv 32 := 0x00050b13.
Lemma F_7704c : fetch_word Asan.M.loaded_segments (0x7704c : word) = Some W_7704c.
Proof. vm_refl. Qed.
Lemma D_7704c : decode_any W_7704c = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77050 : bv 32 := 0x074cfa63.
Lemma F_77050 : fetch_word Asan.M.loaded_segments (0x77050 : word) = Some W_77050.
Proof. vm_refl. Qed.
Lemma D_77050 : decode_any W_77050 = Some (Branch BC_GEU 25 20 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_77054 : bv 32 := 0x000b3503.
Lemma F_77054 : fetch_word Asan.M.loaded_segments (0x77054 : word) = Some W_77054.
Proof. vm_refl. Qed.
Lemma D_77054 : decode_any W_77054 = Some (Load SZ8 true 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77058 : bv 32 := 0x0230000f.
Lemma F_77058 : fetch_word Asan.M.loaded_segments (0x77058 : word) = Some W_77058.
Proof. vm_refl. Qed.
Lemma D_77058 : decode_any W_77058 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7705c : bv 32 := 0xffb504e3.
Lemma F_7705c : fetch_word Asan.M.loaded_segments (0x7705c : word) = Some W_7705c.
Proof. vm_refl. Qed.
Lemma D_7705c : decode_any W_7705c = Some (Branch BC_EQ 10 27 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_77060 : bv 32 := 0xfe0514e3.
Lemma F_77060 : fetch_word Asan.M.loaded_segments (0x77060 : word) = Some W_77060.
Proof. vm_refl. Qed.
Lemma D_77060 : decode_any W_77060 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_77064 : bv 32 := 0x000c0513.
Lemma F_77064 : fetch_word Asan.M.loaded_segments (0x77064 : word) = Some W_77064.
Proof. vm_refl. Qed.
Lemma D_77064 : decode_any W_77064 = Some (OpImm ALU_ADD 10 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77068 : bv 32 := 0x000b8593.
Lemma F_77068 : fetch_word Asan.M.loaded_segments (0x77068 : word) = Some W_77068.
Proof. vm_refl. Qed.
Lemma D_77068 : decode_any W_77068 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7706c : bv 32 := 0x00000613.
Lemma F_7706c : fetch_word Asan.M.loaded_segments (0x7706c : word) = Some W_7706c.
Proof. vm_refl. Qed.
Lemma D_7706c : decode_any W_7706c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77070 : bv 32 := 0x9c0fc0ef.
Lemma F_77070 : fetch_word Asan.M.loaded_segments (0x77070 : word) = Some W_77070.
Proof. vm_refl. Qed.
Lemma D_77070 : decode_any W_77070 = Some (Jal 1 2081216, 4%Z).
Proof. vm_refl. Qed.

Definition W_77074 : bv 32 := 0x160b34af.
Lemma F_77074 : fetch_word Asan.M.loaded_segments (0x77074 : word) = Some W_77074.
Proof. vm_refl. Qed.
Lemma D_77074 : decode_any W_77074 = Some (Lr AD true true 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_77078 : bv 32 := 0x02049a63.
Lemma F_77078 : fetch_word Asan.M.loaded_segments (0x77078 : word) = Some W_77078.
Proof. vm_refl. Qed.
Lemma D_77078 : decode_any W_77078 = Some (Branch BC_NE 9 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7707c : bv 32 := 0x1aab35af.
Lemma F_7707c : fetch_word Asan.M.loaded_segments (0x7707c : word) = Some W_7707c.
Proof. vm_refl. Qed.
Lemma D_7707c : decode_any W_7707c = Some (Sc AD false true 11 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_77080 : bv 32 := 0xfe059ae3.
Lemma F_77080 : fetch_word Asan.M.loaded_segments (0x77080 : word) = Some W_77080.
Proof. vm_refl. Qed.
Lemma D_77080 : decode_any W_77080 = Some (Branch BC_NE 11 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_77084 : bv 32 := 0x00100593.
Lemma F_77084 : fetch_word Asan.M.loaded_segments (0x77084 : word) = Some W_77084.
Proof. vm_refl. Qed.
Lemma D_77084 : decode_any W_77084 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_77088 : bv 32 := 0x00b4362f.
Lemma F_77088 : fetch_word Asan.M.loaded_segments (0x77088 : word) = Some W_77088.
Proof. vm_refl. Qed.
Lemma D_77088 : decode_any W_77088 = Some (Amo AMO_ADD AD false false 12 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7708c : bv 32 := 0x000d2583.
Lemma F_7708c : fetch_word Asan.M.loaded_segments (0x7708c : word) = Some W_7708c.
Proof. vm_refl. Qed.
Lemma D_7708c : decode_any W_7708c = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77090 : bv 32 := 0x00200693.
Lemma F_77090 : fetch_word Asan.M.loaded_segments (0x77090 : word) = Some W_77090.
Proof. vm_refl. Qed.
Lemma D_77090 : decode_any W_77090 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_77094 : bv 32 := 0xfad5eae3.
Lemma F_77094 : fetch_word Asan.M.loaded_segments (0x77094 : word) = Some W_77094.
Proof. vm_refl. Qed.
Lemma D_77094 : decode_any W_77094 = Some (Branch BC_LTU 11 13 8116, 4%Z).
Proof. vm_refl. Qed.

Definition W_77098 : bv 32 := 0x00050493.
Lemma F_77098 : fetch_word Asan.M.loaded_segments (0x77098 : word) = Some W_77098.
Proof. vm_refl. Qed.
Lemma D_77098 : decode_any W_77098 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7709c : bv 32 := 0x00813503.
Lemma F_7709c : fetch_word Asan.M.loaded_segments (0x7709c : word) = Some W_7709c.
Proof. vm_refl. Qed.
Lemma D_7709c : decode_any W_7709c = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_770a0 : bv 32 := 0x000a8593.
Lemma F_770a0 : fetch_word Asan.M.loaded_segments (0x770a0 : word) = Some W_770a0.
Proof. vm_refl. Qed.
Lemma D_770a0 : decode_any W_770a0 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_770a4 : bv 32 := 0xee4fd0ef.
Lemma F_770a4 : fetch_word Asan.M.loaded_segments (0x770a4 : word) = Some W_770a4.
Proof. vm_refl. Qed.
Lemma D_770a4 : decode_any W_770a4 = Some (Jal 1 2086628, 4%Z).
Proof. vm_refl. Qed.

Definition W_770a8 : bv 32 := 0x0100006f.
Lemma F_770a8 : fetch_word Asan.M.loaded_segments (0x770a8 : word) = Some W_770a8.
Proof. vm_refl. Qed.
Lemma D_770a8 : decode_any W_770a8 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_770ac : bv 32 := 0x000c0593.
Lemma F_770ac : fetch_word Asan.M.loaded_segments (0x770ac : word) = Some W_770ac.
Proof. vm_refl. Qed.
Lemma D_770ac : decode_any W_770ac = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_770b0 : bv 32 := 0x00000613.
Lemma F_770b0 : fetch_word Asan.M.loaded_segments (0x770b0 : word) = Some W_770b0.
Proof. vm_refl. Qed.
Lemma D_770b0 : decode_any W_770b0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_770b4 : bv 32 := 0xafcfc0ef.
Lemma F_770b4 : fetch_word Asan.M.loaded_segments (0x770b4 : word) = Some W_770b4.
Proof. vm_refl. Qed.
Lemma D_770b4 : decode_any W_770b4 = Some (Jal 1 2081532, 4%Z).
Proof. vm_refl. Qed.

Definition W_770b8 : bv 32 := 0x00048513.
Lemma F_770b8 : fetch_word Asan.M.loaded_segments (0x770b8 : word) = Some W_770b8.
Proof. vm_refl. Qed.
Lemma D_770b8 : decode_any W_770b8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_770bc : bv 32 := 0xf8dff06f.
Lemma F_770bc : fetch_word Asan.M.loaded_segments (0x770bc : word) = Some W_770bc.
Proof. vm_refl. Qed.
Lemma D_770bc : decode_any W_770bc = Some (Jal 0 2097036, 4%Z).
Proof. vm_refl. Qed.

Definition W_770c0 : bv 32 := 0x000b0513.
Lemma F_770c0 : fetch_word Asan.M.loaded_segments (0x770c0 : word) = Some W_770c0.
Proof. vm_refl. Qed.
Lemma D_770c0 : decode_any W_770c0 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_770c4 : bv 32 := 0x004a1413.
Lemma F_770c4 : fetch_word Asan.M.loaded_segments (0x770c4 : word) = Some W_770c4.
Proof. vm_refl. Qed.
Lemma D_770c4 : decode_any W_770c4 = Some (ShiftImm ALU_SLL 8 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_770c8 : bv 32 := 0x00850433.
Lemma F_770c8 : fetch_word Asan.M.loaded_segments (0x770c8 : word) = Some W_770c8.
Proof. vm_refl. Qed.
Lemma D_770c8 : decode_any W_770c8 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_770cc : bv 32 := 0x00843503.
Lemma F_770cc : fetch_word Asan.M.loaded_segments (0x770cc : word) = Some W_770cc.
Proof. vm_refl. Qed.
Lemma D_770cc : decode_any W_770cc = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_770d0 : bv 32 := 0x04050263.
Lemma F_770d0 : fetch_word Asan.M.loaded_segments (0x770d0 : word) = Some W_770d0.
Proof. vm_refl. Qed.
Lemma D_770d0 : decode_any W_770d0 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_770d4 : bv 32 := 0x00000513.
Lemma F_770d4 : fetch_word Asan.M.loaded_segments (0x770d4 : word) = Some W_770d4.
Proof. vm_refl. Qed.
Lemma D_770d4 : decode_any W_770d4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_770d8 : bv 32 := 0x08813083.
Lemma F_770d8 : fetch_word Asan.M.loaded_segments (0x770d8 : word) = Some W_770d8.
Proof. vm_refl. Qed.
Lemma D_770d8 : decode_any W_770d8 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_770dc : bv 32 := 0x08013403.
Lemma F_770dc : fetch_word Asan.M.loaded_segments (0x770dc : word) = Some W_770dc.
Proof. vm_refl. Qed.
Lemma D_770dc : decode_any W_770dc = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_770e0 : bv 32 := 0x07813483.
Lemma F_770e0 : fetch_word Asan.M.loaded_segments (0x770e0 : word) = Some W_770e0.
Proof. vm_refl. Qed.
Lemma D_770e0 : decode_any W_770e0 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_770e4 : bv 32 := 0x07013903.
Lemma F_770e4 : fetch_word Asan.M.loaded_segments (0x770e4 : word) = Some W_770e4.
Proof. vm_refl. Qed.
Lemma D_770e4 : decode_any W_770e4 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_770e8 : bv 32 := 0x06813983.
Lemma F_770e8 : fetch_word Asan.M.loaded_segments (0x770e8 : word) = Some W_770e8.
Proof. vm_refl. Qed.
Lemma D_770e8 : decode_any W_770e8 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_770ec : bv 32 := 0x06013a03.
Lemma F_770ec : fetch_word Asan.M.loaded_segments (0x770ec : word) = Some W_770ec.
Proof. vm_refl. Qed.
Lemma D_770ec : decode_any W_770ec = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_770f0 : bv 32 := 0x05813a83.
Lemma F_770f0 : fetch_word Asan.M.loaded_segments (0x770f0 : word) = Some W_770f0.
Proof. vm_refl. Qed.
Lemma D_770f0 : decode_any W_770f0 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_770f4 : bv 32 := 0x05013b03.
Lemma F_770f4 : fetch_word Asan.M.loaded_segments (0x770f4 : word) = Some W_770f4.
Proof. vm_refl. Qed.
Lemma D_770f4 : decode_any W_770f4 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_770f8 : bv 32 := 0x04813b83.
Lemma F_770f8 : fetch_word Asan.M.loaded_segments (0x770f8 : word) = Some W_770f8.
Proof. vm_refl. Qed.
Lemma D_770f8 : decode_any W_770f8 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_770fc : bv 32 := 0x04013c03.
Lemma F_770fc : fetch_word Asan.M.loaded_segments (0x770fc : word) = Some W_770fc.
Proof. vm_refl. Qed.
Lemma D_770fc : decode_any W_770fc = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_77100 : bv 32 := 0x03813c83.
Lemma F_77100 : fetch_word Asan.M.loaded_segments (0x77100 : word) = Some W_77100.
Proof. vm_refl. Qed.
Lemma D_77100 : decode_any W_77100 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_77104 : bv 32 := 0x03013d03.
Lemma F_77104 : fetch_word Asan.M.loaded_segments (0x77104 : word) = Some W_77104.
Proof. vm_refl. Qed.
Lemma D_77104 : decode_any W_77104 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_77108 : bv 32 := 0x02813d83.
Lemma F_77108 : fetch_word Asan.M.loaded_segments (0x77108 : word) = Some W_77108.
Proof. vm_refl. Qed.
Lemma D_77108 : decode_any W_77108 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7710c : bv 32 := 0x09010113.
Lemma F_7710c : fetch_word Asan.M.loaded_segments (0x7710c : word) = Some W_7710c.
Proof. vm_refl. Qed.
Lemma D_7710c : decode_any W_7710c = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_77110 : bv 32 := 0x00008067.
Lemma F_77110 : fetch_word Asan.M.loaded_segments (0x77110 : word) = Some W_77110.
Proof. vm_refl. Qed.
Lemma D_77110 : decode_any W_77110 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77114 : bv 32 := 0x01813483.
Lemma F_77114 : fetch_word Asan.M.loaded_segments (0x77114 : word) = Some W_77114.
Proof. vm_refl. Qed.
Lemma D_77114 : decode_any W_77114 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_77118 : bv 32 := 0x01013a03.
Lemma F_77118 : fetch_word Asan.M.loaded_segments (0x77118 : word) = Some W_77118.
Proof. vm_refl. Qed.
Lemma D_77118 : decode_any W_77118 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7711c : bv 32 := 0x0744ec63.
Lemma F_7711c : fetch_word Asan.M.loaded_segments (0x7711c : word) = Some W_7711c.
Proof. vm_refl. Qed.
Lemma D_7711c : decode_any W_7711c = Some (Branch BC_LTU 9 20 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_77120 : bv 32 := 0x0089b683.
Lemma F_77120 : fetch_word Asan.M.loaded_segments (0x77120 : word) = Some W_77120.
Proof. vm_refl. Qed.
Lemma D_77120 : decode_any W_77120 = Some (Load SZ8 true 13 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_77124 : bv 32 := 0x40d90533.
Lemma F_77124 : fetch_word Asan.M.loaded_segments (0x77124 : word) = Some W_77124.
Proof. vm_refl. Qed.
Lemma D_77124 : decode_any W_77124 = Some (Op ALU_SUB 10 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_77128 : bv 32 := 0x80050793.
Lemma F_77128 : fetch_word Asan.M.loaded_segments (0x77128 : word) = Some W_77128.
Proof. vm_refl. Qed.
Lemma D_77128 : decode_any W_77128 = Some (OpImm ALU_ADD 15 10 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7712c : bv 32 := 0x02f13023.
Lemma F_7712c : fetch_word Asan.M.loaded_segments (0x7712c : word) = Some W_7712c.
Proof. vm_refl. Qed.
Lemma D_7712c : decode_any W_7712c = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_77130 : bv 32 := 0x000d2503.
Lemma F_77130 : fetch_word Asan.M.loaded_segments (0x77130 : word) = Some W_77130.
Proof. vm_refl. Qed.
Lemma D_77130 : decode_any W_77130 = Some (Load SZ4 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77134 : bv 32 := 0x00200593.
Lemma F_77134 : fetch_word Asan.M.loaded_segments (0x77134 : word) = Some W_77134.
Proof. vm_refl. Qed.
Lemma D_77134 : decode_any W_77134 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_77138 : bv 32 := 0x06b57e63.
Lemma F_77138 : fetch_word Asan.M.loaded_segments (0x77138 : word) = Some W_77138.
Proof. vm_refl. Qed.
Lemma D_77138 : decode_any W_77138 = Some (Branch BC_GEU 10 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_7713c : bv 32 := 0x00840913.
Lemma F_7713c : fetch_word Asan.M.loaded_segments (0x7713c : word) = Some W_7713c.
Proof. vm_refl. Qed.
Lemma D_7713c : decode_any W_7713c = Some (OpImm ALU_ADD 18 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_77140 : bv 32 := 0x0b47e263.
Lemma F_77140 : fetch_word Asan.M.loaded_segments (0x77140 : word) = Some W_77140.
Proof. vm_refl. Qed.
Lemma D_77140 : decode_any W_77140 = Some (Branch BC_LTU 15 20 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_77144 : bv 32 := 0x0a97f063.
Lemma F_77144 : fetch_word Asan.M.loaded_segments (0x77144 : word) = Some W_77144.
Proof. vm_refl. Qed.
Lemma D_77144 : decode_any W_77144 = Some (Branch BC_GEU 15 9 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_77148 : bv 32 := 0x000d2503.
Lemma F_77148 : fetch_word Asan.M.loaded_segments (0x77148 : word) = Some W_77148.
Proof. vm_refl. Qed.
Lemma D_77148 : decode_any W_77148 = Some (Load SZ4 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7714c : bv 32 := 0x00200593.
Lemma F_7714c : fetch_word Asan.M.loaded_segments (0x7714c : word) = Some W_7714c.
Proof. vm_refl. Qed.
Lemma D_7714c : decode_any W_7714c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_77150 : bv 32 := 0x0cb57a63.
Lemma F_77150 : fetch_word Asan.M.loaded_segments (0x77150 : word) = Some W_77150.
Proof. vm_refl. Qed.
Lemma D_77150 : decode_any W_77150 = Some (Branch BC_GEU 10 11 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_77154 : bv 32 := 0x00000513.
Lemma F_77154 : fetch_word Asan.M.loaded_segments (0x77154 : word) = Some W_77154.
Proof. vm_refl. Qed.
Lemma D_77154 : decode_any W_77154 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77158 : bv 32 := 0x0b80006f.
Lemma F_77158 : fetch_word Asan.M.loaded_segments (0x77158 : word) = Some W_77158.
Proof. vm_refl. Qed.
Lemma D_77158 : decode_any W_77158 = Some (Jal 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_7715c : bv 32 := 0xfff9f517.
Lemma F_7715c : fetch_word Asan.M.loaded_segments (0x7715c : word) = Some W_7715c.
Proof. vm_refl. Qed.
Lemma D_7715c : decode_any W_7715c = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_77160 : bv 32 := 0x47f50513.
Lemma F_77160 : fetch_word Asan.M.loaded_segments (0x77160 : word) = Some W_77160.
Proof. vm_refl. Qed.
Lemma D_77160 : decode_any W_77160 = Some (OpImm ALU_ADD 10 10 1151, 4%Z).
Proof. vm_refl. Qed.

Definition W_77164 : bv 32 := 0x000a8593.
Lemma F_77164 : fetch_word Asan.M.loaded_segments (0x77164 : word) = Some W_77164.
Proof. vm_refl. Qed.
Lemma D_77164 : decode_any W_77164 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77168 : bv 32 := 0x00060493.
Lemma F_77168 : fetch_word Asan.M.loaded_segments (0x77168 : word) = Some W_77168.
Proof. vm_refl. Qed.
Lemma D_77168 : decode_any W_77168 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7716c : bv 32 := 0x000a0613.
Lemma F_7716c : fetch_word Asan.M.loaded_segments (0x7716c : word) = Some W_7716c.
Proof. vm_refl. Qed.
Lemma D_7716c : decode_any W_7716c = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77170 : bv 32 := 0x00068413.
Lemma F_77170 : fetch_word Asan.M.loaded_segments (0x77170 : word) = Some W_77170.
Proof. vm_refl. Qed.
Lemma D_77170 : decode_any W_77170 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77174 : bv 32 := 0xe14fd0ef.
Lemma F_77174 : fetch_word Asan.M.loaded_segments (0x77174 : word) = Some W_77174.
Proof. vm_refl. Qed.
Lemma D_77174 : decode_any W_77174 = Some (Jal 1 2086420, 4%Z).
Proof. vm_refl. Qed.

Definition W_77178 : bv 32 := 0x00048613.
Lemma F_77178 : fetch_word Asan.M.loaded_segments (0x77178 : word) = Some W_77178.
Proof. vm_refl. Qed.
Lemma D_77178 : decode_any W_77178 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7717c : bv 32 := 0x00040693.
Lemma F_7717c : fetch_word Asan.M.loaded_segments (0x7717c : word) = Some W_7717c.
Proof. vm_refl. Qed.
Lemma D_7717c : decode_any W_7717c = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77180 : bv 32 := 0x000abb03.
Lemma F_77180 : fetch_word Asan.M.loaded_segments (0x77180 : word) = Some W_77180.
Proof. vm_refl. Qed.
Lemma D_77180 : decode_any W_77180 = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77184 : bv 32 := 0xfff00513.
Lemma F_77184 : fetch_word Asan.M.loaded_segments (0x77184 : word) = Some W_77184.
Proof. vm_refl. Qed.
Lemma D_77184 : decode_any W_77184 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_77188 : bv 32 := 0x0230000f.
Lemma F_77188 : fetch_word Asan.M.loaded_segments (0x77188 : word) = Some W_77188.
Proof. vm_refl. Qed.
Lemma D_77188 : decode_any W_77188 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7718c : bv 32 := 0xdeab18e3.
Lemma F_7718c : fetch_word Asan.M.loaded_segments (0x7718c : word) = Some W_7718c.
Proof. vm_refl. Qed.
Lemma D_7718c : decode_any W_7718c = Some (Branch BC_NE 22 10 7664, 4%Z).
Proof. vm_refl. Qed.

Definition W_77190 : bv 32 := 0xf45ff06f.
Lemma F_77190 : fetch_word Asan.M.loaded_segments (0x77190 : word) = Some W_77190.
Proof. vm_refl. Qed.
Lemma D_77190 : decode_any W_77190 = Some (Jal 0 2096964, 4%Z).
Proof. vm_refl. Qed.

Definition W_77194 : bv 32 := 0xfffa5517.
Lemma F_77194 : fetch_word Asan.M.loaded_segments (0x77194 : word) = Some W_77194.
Proof. vm_refl. Qed.
Lemma D_77194 : decode_any W_77194 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_77198 : bv 32 := 0xfff9e597.
Lemma F_77198 : fetch_word Asan.M.loaded_segments (0x77198 : word) = Some W_77198.
Proof. vm_refl. Qed.
Lemma D_77198 : decode_any W_77198 = Some (Auipc 11 1048478, 4%Z).
Proof. vm_refl. Qed.

Definition W_7719c : bv 32 := 0x67350513.
Lemma F_7719c : fetch_word Asan.M.loaded_segments (0x7719c : word) = Some W_7719c.
Proof. vm_refl. Qed.
Lemma D_7719c : decode_any W_7719c = Some (OpImm ALU_ADD 10 10 1651, 4%Z).
Proof. vm_refl. Qed.

Definition W_771a0 : bv 32 := 0x81258613.
Lemma F_771a0 : fetch_word Asan.M.loaded_segments (0x771a0 : word) = Some W_771a0.
Proof. vm_refl. Qed.
Lemma D_771a0 : decode_any W_771a0 = Some (OpImm ALU_ADD 12 11 2066, 4%Z).
Proof. vm_refl. Qed.

Definition W_771a4 : bv 32 := 0x08a00593.
Lemma F_771a4 : fetch_word Asan.M.loaded_segments (0x771a4 : word) = Some W_771a4.
Proof. vm_refl. Qed.
Lemma D_771a4 : decode_any W_771a4 = Some (OpImm ALU_ADD 11 0 138, 4%Z).
Proof. vm_refl. Qed.

Definition W_771a8 : bv 32 := 0x000a0693.
Lemma F_771a8 : fetch_word Asan.M.loaded_segments (0x771a8 : word) = Some W_771a8.
Proof. vm_refl. Qed.
Lemma D_771a8 : decode_any W_771a8 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771ac : bv 32 := 0x00048713.
Lemma F_771ac : fetch_word Asan.M.loaded_segments (0x771ac : word) = Some W_771ac.
Proof. vm_refl. Qed.
Lemma D_771ac : decode_any W_771ac = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771b0 : bv 32 := 0x6b9010ef.
Lemma F_771b0 : fetch_word Asan.M.loaded_segments (0x771b0 : word) = Some W_771b0.
Proof. vm_refl. Qed.
Lemma D_771b0 : decode_any W_771b0 = Some (Jal 1 7864, 4%Z).
Proof. vm_refl. Qed.

Definition W_771b4 : bv 32 := 0x0009b603.
Lemma F_771b4 : fetch_word Asan.M.loaded_segments (0x771b4 : word) = Some W_771b4.
Proof. vm_refl. Qed.
Lemma D_771b4 : decode_any W_771b4 = Some (Load SZ8 true 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771b8 : bv 32 := 0x000f8517.
Lemma F_771b8 : fetch_word Asan.M.loaded_segments (0x771b8 : word) = Some W_771b8.
Proof. vm_refl. Qed.
Lemma D_771b8 : decode_any W_771b8 = Some (Auipc 10 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_771bc : bv 32 := 0x6c053883.
Lemma F_771bc : fetch_word Asan.M.loaded_segments (0x771bc : word) = Some W_771bc.
Proof. vm_refl. Qed.
Lemma D_771bc : decode_any W_771bc = Some (Load SZ8 true 17 10 1728, 4%Z).
Proof. vm_refl. Qed.

Definition W_771c0 : bv 32 := 0xfff9f517.
Lemma F_771c0 : fetch_word Asan.M.loaded_segments (0x771c0 : word) = Some W_771c0.
Proof. vm_refl. Qed.
Lemma D_771c0 : decode_any W_771c0 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_771c4 : bv 32 := 0xb2d50513.
Lemma F_771c4 : fetch_word Asan.M.loaded_segments (0x771c4 : word) = Some W_771c4.
Proof. vm_refl. Qed.
Lemma D_771c4 : decode_any W_771c4 = Some (OpImm ALU_ADD 10 10 2861, 4%Z).
Proof. vm_refl. Qed.

Definition W_771c8 : bv 32 := 0x02010813.
Lemma F_771c8 : fetch_word Asan.M.loaded_segments (0x771c8 : word) = Some W_771c8.
Proof. vm_refl. Qed.
Lemma D_771c8 : decode_any W_771c8 = Some (OpImm ALU_ADD 16 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_771cc : bv 32 := 0x00098593.
Lemma F_771cc : fetch_word Asan.M.loaded_segments (0x771cc : word) = Some W_771cc.
Proof. vm_refl. Qed.
Lemma D_771cc : decode_any W_771cc = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771d0 : bv 32 := 0x00090713.
Lemma F_771d0 : fetch_word Asan.M.loaded_segments (0x771d0 : word) = Some W_771d0.
Proof. vm_refl. Qed.
Lemma D_771d0 : decode_any W_771d0 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771d4 : bv 32 := 0xdb4fd0ef.
Lemma F_771d4 : fetch_word Asan.M.loaded_segments (0x771d4 : word) = Some W_771d4.
Proof. vm_refl. Qed.
Lemma D_771d4 : decode_any W_771d4 = Some (Jal 1 2086324, 4%Z).
Proof. vm_refl. Qed.

Definition W_771d8 : bv 32 := 0x02013783.
Lemma F_771d8 : fetch_word Asan.M.loaded_segments (0x771d8 : word) = Some W_771d8.
Proof. vm_refl. Qed.
Lemma D_771d8 : decode_any W_771d8 = Some (Load SZ8 true 15 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_771dc : bv 32 := 0x00840913.
Lemma F_771dc : fetch_word Asan.M.loaded_segments (0x771dc : word) = Some W_771dc.
Proof. vm_refl. Qed.
Lemma D_771dc : decode_any W_771dc = Some (OpImm ALU_ADD 18 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_771e0 : bv 32 := 0xf747f2e3.
Lemma F_771e0 : fetch_word Asan.M.loaded_segments (0x771e0 : word) = Some W_771e0.
Proof. vm_refl. Qed.
Lemma D_771e0 : decode_any W_771e0 = Some (Branch BC_GEU 15 20 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_771e4 : bv 32 := 0x00078513.
Lemma F_771e4 : fetch_word Asan.M.loaded_segments (0x771e4 : word) = Some W_771e4.
Proof. vm_refl. Qed.
Lemma D_771e4 : decode_any W_771e4 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771e8 : bv 32 := 0xc41ff0ef.
Lemma F_771e8 : fetch_word Asan.M.loaded_segments (0x771e8 : word) = Some W_771e8.
Proof. vm_refl. Qed.
Lemma D_771e8 : decode_any W_771e8 = Some (Jal 1 2096192, 4%Z).
Proof. vm_refl. Qed.

Definition W_771ec : bv 32 := 0x00050863.
Lemma F_771ec : fetch_word Asan.M.loaded_segments (0x771ec : word) = Some W_771ec.
Proof. vm_refl. Qed.
Lemma D_771ec : decode_any W_771ec = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_771f0 : bv 32 := 0x02013783.
Lemma F_771f0 : fetch_word Asan.M.loaded_segments (0x771f0 : word) = Some W_771f0.
Proof. vm_refl. Qed.
Lemma D_771f0 : decode_any W_771f0 = Some (Load SZ8 true 15 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_771f4 : bv 32 := 0x00090593.
Lemma F_771f4 : fetch_word Asan.M.loaded_segments (0x771f4 : word) = Some W_771f4.
Proof. vm_refl. Qed.
Lemma D_771f4 : decode_any W_771f4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_771f8 : bv 32 := 0x01c0006f.
Lemma F_771f8 : fetch_word Asan.M.loaded_segments (0x771f8 : word) = Some W_771f8.
Proof. vm_refl. Qed.
Lemma D_771f8 : decode_any W_771f8 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_771fc : bv 32 := 0x000d2503.
Lemma F_771fc : fetch_word Asan.M.loaded_segments (0x771fc : word) = Some W_771fc.
Proof. vm_refl. Qed.
Lemma D_771fc : decode_any W_771fc = Some (Load SZ4 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77200 : bv 32 := 0x00200593.
Lemma F_77200 : fetch_word Asan.M.loaded_segments (0x77200 : word) = Some W_77200.
Proof. vm_refl. Qed.
Lemma D_77200 : decode_any W_77200 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_77204 : bv 32 := 0x02b57a63.
Lemma F_77204 : fetch_word Asan.M.loaded_segments (0x77204 : word) = Some W_77204.
Proof. vm_refl. Qed.
Lemma D_77204 : decode_any W_77204 = Some (Branch BC_GEU 10 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_77208 : bv 32 := 0x00000513.
Lemma F_77208 : fetch_word Asan.M.loaded_segments (0x77208 : word) = Some W_77208.
Proof. vm_refl. Qed.
Lemma D_77208 : decode_any W_77208 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7720c : bv 32 := 0x02013783.
Lemma F_7720c : fetch_word Asan.M.loaded_segments (0x7720c : word) = Some W_7720c.
Proof. vm_refl. Qed.
Lemma D_7720c : decode_any W_7720c = Some (Load SZ8 true 15 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_77210 : bv 32 := 0x00000593.
Lemma F_77210 : fetch_word Asan.M.loaded_segments (0x77210 : word) = Some W_77210.
Proof. vm_refl. Qed.
Lemma D_77210 : decode_any W_77210 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77214 : bv 32 := 0x00f93023.
Lemma F_77214 : fetch_word Asan.M.loaded_segments (0x77214 : word) = Some W_77214.
Proof. vm_refl. Qed.
Lemma D_77214 : decode_any W_77214 = Some (Store SZ8 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77218 : bv 32 := 0x00a93423.
Lemma F_77218 : fetch_word Asan.M.loaded_segments (0x77218 : word) = Some W_77218.
Proof. vm_refl. Qed.
Lemma D_77218 : decode_any W_77218 = Some (Store SZ8 18 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7721c : bv 32 := 0x00058513.
Lemma F_7721c : fetch_word Asan.M.loaded_segments (0x7721c : word) = Some W_7721c.
Proof. vm_refl. Qed.
Lemma D_7721c : decode_any W_7721c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77220 : bv 32 := 0xeb9ff06f.
Lemma F_77220 : fetch_word Asan.M.loaded_segments (0x77220 : word) = Some W_77220.
Proof. vm_refl. Qed.
Lemma D_77220 : decode_any W_77220 = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

Definition W_77224 : bv 32 := 0xfff9d517.
Lemma F_77224 : fetch_word Asan.M.loaded_segments (0x77224 : word) = Some W_77224.
Proof. vm_refl. Qed.
Lemma D_77224 : decode_any W_77224 = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_77228 : bv 32 := 0xd5150513.
Lemma F_77228 : fetch_word Asan.M.loaded_segments (0x77228 : word) = Some W_77228.
Proof. vm_refl. Qed.
Lemma D_77228 : decode_any W_77228 = Some (OpImm ALU_ADD 10 10 3409, 4%Z).
Proof. vm_refl. Qed.

Definition W_7722c : bv 32 := 0x00078593.
Lemma F_7722c : fetch_word Asan.M.loaded_segments (0x7722c : word) = Some W_7722c.
Proof. vm_refl. Qed.
Lemma D_7722c : decode_any W_7722c = Some (OpImm ALU_ADD 11 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_77230 : bv 32 := 0xd58fd0ef.
Lemma F_77230 : fetch_word Asan.M.loaded_segments (0x77230 : word) = Some W_77230.
Proof. vm_refl. Qed.
Lemma D_77230 : decode_any W_77230 = Some (Jal 1 2086232, 4%Z).
Proof. vm_refl. Qed.

Definition W_77234 : bv 32 := 0xfd5ff06f.
Lemma F_77234 : fetch_word Asan.M.loaded_segments (0x77234 : word) = Some W_77234.
Proof. vm_refl. Qed.
Lemma D_77234 : decode_any W_77234 = Some (Jal 0 2097108, 4%Z).
Proof. vm_refl. Qed.

Definition W_77238 : bv 32 := 0xfffa7517.
Lemma F_77238 : fetch_word Asan.M.loaded_segments (0x77238 : word) = Some W_77238.
Proof. vm_refl. Qed.
Lemma D_77238 : decode_any W_77238 = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_7723c : bv 32 := 0x80550513.
Lemma F_7723c : fetch_word Asan.M.loaded_segments (0x7723c : word) = Some W_7723c.
Proof. vm_refl. Qed.
Lemma D_7723c : decode_any W_7723c = Some (OpImm ALU_ADD 10 10 2053, 4%Z).
Proof. vm_refl. Qed.

Definition W_77240 : bv 32 := 0xd48fd0ef.
Lemma F_77240 : fetch_word Asan.M.loaded_segments (0x77240 : word) = Some W_77240.
Proof. vm_refl. Qed.
Lemma D_77240 : decode_any W_77240 = Some (Jal 1 2086216, 4%Z).
Proof. vm_refl. Qed.

Definition W_77244 : bv 32 := 0xfc5ff06f.
Lemma F_77244 : fetch_word Asan.M.loaded_segments (0x77244 : word) = Some W_77244.
Proof. vm_refl. Qed.
Lemma D_77244 : decode_any W_77244 = Some (Jal 0 2097092, 4%Z).
Proof. vm_refl. Qed.
