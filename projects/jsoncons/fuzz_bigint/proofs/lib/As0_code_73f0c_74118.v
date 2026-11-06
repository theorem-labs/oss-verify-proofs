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

Definition W_73f0c : bv 32 := 0xef010113.
Lemma F_73f0c : fetch_word Asan.M.loaded_segments (0x73f0c : word) = Some W_73f0c.
Proof. vm_refl. Qed.
Lemma D_73f0c : decode_any W_73f0c = Some (OpImm ALU_ADD 2 2 3824, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f10 : bv 32 := 0x10113423.
Lemma F_73f10 : fetch_word Asan.M.loaded_segments (0x73f10 : word) = Some W_73f10.
Proof. vm_refl. Qed.
Lemma D_73f10 : decode_any W_73f10 = Some (Store SZ8 2 1 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f14 : bv 32 := 0x10813023.
Lemma F_73f14 : fetch_word Asan.M.loaded_segments (0x73f14 : word) = Some W_73f14.
Proof. vm_refl. Qed.
Lemma D_73f14 : decode_any W_73f14 = Some (Store SZ8 2 8 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f18 : bv 32 := 0x0e913c23.
Lemma F_73f18 : fetch_word Asan.M.loaded_segments (0x73f18 : word) = Some W_73f18.
Proof. vm_refl. Qed.
Lemma D_73f18 : decode_any W_73f18 = Some (Store SZ8 2 9 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f1c : bv 32 := 0x0f213823.
Lemma F_73f1c : fetch_word Asan.M.loaded_segments (0x73f1c : word) = Some W_73f1c.
Proof. vm_refl. Qed.
Lemma D_73f1c : decode_any W_73f1c = Some (Store SZ8 2 18 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f20 : bv 32 := 0x0f313423.
Lemma F_73f20 : fetch_word Asan.M.loaded_segments (0x73f20 : word) = Some W_73f20.
Proof. vm_refl. Qed.
Lemma D_73f20 : decode_any W_73f20 = Some (Store SZ8 2 19 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f24 : bv 32 := 0x0f413023.
Lemma F_73f24 : fetch_word Asan.M.loaded_segments (0x73f24 : word) = Some W_73f24.
Proof. vm_refl. Qed.
Lemma D_73f24 : decode_any W_73f24 = Some (Store SZ8 2 20 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f28 : bv 32 := 0x0d513c23.
Lemma F_73f28 : fetch_word Asan.M.loaded_segments (0x73f28 : word) = Some W_73f28.
Proof. vm_refl. Qed.
Lemma D_73f28 : decode_any W_73f28 = Some (Store SZ8 2 21 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f2c : bv 32 := 0x00050913.
Lemma F_73f2c : fetch_word Asan.M.loaded_segments (0x73f2c : word) = Some W_73f2c.
Proof. vm_refl. Qed.
Lemma D_73f2c : decode_any W_73f2c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f30 : bv 32 := 0xfff00513.
Lemma F_73f30 : fetch_word Asan.M.loaded_segments (0x73f30 : word) = Some W_73f30.
Proof. vm_refl. Qed.
Lemma D_73f30 : decode_any W_73f30 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f34 : bv 32 := 0x12090463.
Lemma F_73f34 : fetch_word Asan.M.loaded_segments (0x73f34 : word) = Some W_73f34.
Proof. vm_refl. Qed.
Lemma D_73f34 : decode_any W_73f34 = Some (Branch BC_EQ 18 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f38 : bv 32 := 0x00060413.
Lemma F_73f38 : fetch_word Asan.M.loaded_segments (0x73f38 : word) = Some W_73f38.
Proof. vm_refl. Qed.
Lemma D_73f38 : decode_any W_73f38 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f3c : bv 32 := 0x00062617.
Lemma F_73f3c : fetch_word Asan.M.loaded_segments (0x73f3c : word) = Some W_73f3c.
Proof. vm_refl. Qed.
Lemma D_73f3c : decode_any W_73f3c = Some (Auipc 12 98, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f40 : bv 32 := 0x96c63603.
Lemma F_73f40 : fetch_word Asan.M.loaded_segments (0x73f40 : word) = Some W_73f40.
Proof. vm_refl. Qed.
Lemma D_73f40 : decode_any W_73f40 = Some (Load SZ8 true 12 12 2412, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f44 : bv 32 := 0x10464603.
Lemma F_73f44 : fetch_word Asan.M.loaded_segments (0x73f44 : word) = Some W_73f44.
Proof. vm_refl. Qed.
Lemma D_73f44 : decode_any W_73f44 = Some (Load SZ1 false 12 12 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f48 : bv 32 := 0x00167613.
Lemma F_73f48 : fetch_word Asan.M.loaded_segments (0x73f48 : word) = Some W_73f48.
Proof. vm_refl. Qed.
Lemma D_73f48 : decode_any W_73f48 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f4c : bv 32 := 0x10060863.
Lemma F_73f4c : fetch_word Asan.M.loaded_segments (0x73f4c : word) = Some W_73f4c.
Proof. vm_refl. Qed.
Lemma D_73f4c : decode_any W_73f4c = Some (Branch BC_EQ 12 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f50 : bv 32 := 0x00058493.
Lemma F_73f50 : fetch_word Asan.M.loaded_segments (0x73f50 : word) = Some W_73f50.
Proof. vm_refl. Qed.
Lemma D_73f50 : decode_any W_73f50 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f54 : bv 32 := 0x00d10513.
Lemma F_73f54 : fetch_word Asan.M.loaded_segments (0x73f54 : word) = Some W_73f54.
Proof. vm_refl. Qed.
Lemma D_73f54 : decode_any W_73f54 = Some (OpImm ALU_ADD 10 2 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f58 : bv 32 := 0x0aa00593.
Lemma F_73f58 : fetch_word Asan.M.loaded_segments (0x73f58 : word) = Some W_73f58.
Proof. vm_refl. Qed.
Lemma D_73f58 : decode_any W_73f58 = Some (OpImm ALU_ADD 11 0 170, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f5c : bv 32 := 0x0c800613.
Lemma F_73f5c : fetch_word Asan.M.loaded_segments (0x73f5c : word) = Some W_73f5c.
Proof. vm_refl. Qed.
Lemma D_73f5c : decode_any W_73f5c = Some (OpImm ALU_ADD 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f60 : bv 32 := 0xc00fd0ef.
Lemma F_73f60 : fetch_word Asan.M.loaded_segments (0x73f60 : word) = Some W_73f60.
Proof. vm_refl. Qed.
Lemma D_73f60 : decode_any W_73f60 = Some (Jal 1 2085888, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f64 : bv 32 := 0x00090513.
Lemma F_73f64 : fetch_word Asan.M.loaded_segments (0x73f64 : word) = Some W_73f64.
Proof. vm_refl. Qed.
Lemma D_73f64 : decode_any W_73f64 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f68 : bv 32 := 0xd4cfd0ef.
Lemma F_73f68 : fetch_word Asan.M.loaded_segments (0x73f68 : word) = Some W_73f68.
Proof. vm_refl. Qed.
Lemma D_73f68 : decode_any W_73f68 = Some (Jal 1 2086220, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f6c : bv 32 := 0x0be00593.
Lemma F_73f6c : fetch_word Asan.M.loaded_segments (0x73f6c : word) = Some W_73f6c.
Proof. vm_refl. Qed.
Lemma D_73f6c : decode_any W_73f6c = Some (OpImm ALU_ADD 11 0 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f70 : bv 32 := 0x14b57463.
Lemma F_73f70 : fetch_word Asan.M.loaded_segments (0x73f70 : word) = Some W_73f70.
Proof. vm_refl. Qed.
Lemma D_73f70 : decode_any W_73f70 = Some (Branch BC_GEU 10 11 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f74 : bv 32 := 0x94cfe0ef.
Lemma F_73f74 : fetch_word Asan.M.loaded_segments (0x73f74 : word) = Some W_73f74.
Proof. vm_refl. Qed.
Lemma D_73f74 : decode_any W_73f74 = Some (Jal 1 2089292, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f78 : bv 32 := 0x00050693.
Lemma F_73f78 : fetch_word Asan.M.loaded_segments (0x73f78 : word) = Some W_73f78.
Proof. vm_refl. Qed.
Lemma D_73f78 : decode_any W_73f78 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f7c : bv 32 := 0xfffae597.
Lemma F_73f7c : fetch_word Asan.M.loaded_segments (0x73f7c : word) = Some W_73f7c.
Proof. vm_refl. Qed.
Lemma D_73f7c : decode_any W_73f7c = Some (Auipc 11 1048494, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f80 : bv 32 := 0x00d10513.
Lemma F_73f80 : fetch_word Asan.M.loaded_segments (0x73f80 : word) = Some W_73f80.
Proof. vm_refl. Qed.
Lemma D_73f80 : decode_any W_73f80 = Some (OpImm ALU_ADD 10 2 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f84 : bv 32 := 0xe7f58613.
Lemma F_73f84 : fetch_word Asan.M.loaded_segments (0x73f84 : word) = Some W_73f84.
Proof. vm_refl. Qed.
Lemma D_73f84 : decode_any W_73f84 = Some (OpImm ALU_ADD 12 11 3711, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f88 : bv 32 := 0x0c800593.
Lemma F_73f88 : fetch_word Asan.M.loaded_segments (0x73f88 : word) = Some W_73f88.
Proof. vm_refl. Qed.
Lemma D_73f88 : decode_any W_73f88 = Some (OpImm ALU_ADD 11 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f8c : bv 32 := 0x00090713.
Lemma F_73f8c : fetch_word Asan.M.loaded_segments (0x73f8c : word) = Some W_73f8c.
Proof. vm_refl. Qed.
Lemma D_73f8c : decode_any W_73f8c = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f90 : bv 32 := 0x045000ef.
Lemma F_73f90 : fetch_word Asan.M.loaded_segments (0x73f90 : word) = Some W_73f90.
Proof. vm_refl. Qed.
Lemma D_73f90 : decode_any W_73f90 = Some (Jal 1 2116, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f94 : bv 32 := 0x000805b7.
Lemma F_73f94 : fetch_word Asan.M.loaded_segments (0x73f94 : word) = Some W_73f94.
Proof. vm_refl. Qed.
Lemma D_73f94 : decode_any W_73f94 = Some (Lui 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f98 : bv 32 := 0x00d10513.
Lemma F_73f98 : fetch_word Asan.M.loaded_segments (0x73f98 : word) = Some W_73f98.
Proof. vm_refl. Qed.
Lemma D_73f98 : decode_any W_73f98 = Some (OpImm ALU_ADD 10 2 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_73f9c : bv 32 := 0x2425859b.
Lemma F_73f9c : fetch_word Asan.M.loaded_segments (0x73f9c : word) = Some W_73f9c.
Proof. vm_refl. Qed.
Lemma D_73f9c : decode_any W_73f9c = Some (OpImm32 11 11 578, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fa0 : bv 32 := 0x1c000613.
Lemma F_73fa0 : fetch_word Asan.M.loaded_segments (0x73fa0 : word) = Some W_73fa0.
Proof. vm_refl. Qed.
Lemma D_73fa0 : decode_any W_73fa0 = Some (OpImm ALU_ADD 12 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fa4 : bv 32 := 0xc1dfd0ef.
Lemma F_73fa4 : fetch_word Asan.M.loaded_segments (0x73fa4 : word) = Some W_73fa4.
Proof. vm_refl. Qed.
Lemma D_73fa4 : decode_any W_73fa4 = Some (Jal 1 2087964, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fa8 : bv 32 := 0x00050913.
Lemma F_73fa8 : fetch_word Asan.M.loaded_segments (0x73fa8 : word) = Some W_73fa8.
Proof. vm_refl. Qed.
Lemma D_73fa8 : decode_any W_73fa8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fac : bv 32 := 0x0005051b.
Lemma F_73fac : fetch_word Asan.M.loaded_segments (0x73fac : word) = Some W_73fac.
Proof. vm_refl. Qed.
Lemma D_73fac : decode_any W_73fac = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fb0 : bv 32 := 0x00200593.
Lemma F_73fb0 : fetch_word Asan.M.loaded_segments (0x73fb0 : word) = Some W_73fb0.
Proof. vm_refl. Qed.
Lemma D_73fb0 : decode_any W_73fb0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fb4 : bv 32 := 0x06a5c863.
Lemma F_73fb4 : fetch_word Asan.M.loaded_segments (0x73fb4 : word) = Some W_73fb4.
Proof. vm_refl. Qed.
Lemma D_73fb4 : decode_any W_73fb4 = Some (Branch BC_LT 11 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fb8 : bv 32 := 0x0aa00513.
Lemma F_73fb8 : fetch_word Asan.M.loaded_segments (0x73fb8 : word) = Some W_73fb8.
Proof. vm_refl. Qed.
Lemma D_73fb8 : decode_any W_73fb8 = Some (OpImm ALU_ADD 10 0 170, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fbc : bv 32 := 0x0ca10aa3.
Lemma F_73fbc : fetch_word Asan.M.loaded_segments (0x73fbc : word) = Some W_73fbc.
Proof. vm_refl. Qed.
Lemma D_73fbc : decode_any W_73fbc = Some (Store SZ1 2 10 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fc0 : bv 32 := 0x0ca10b23.
Lemma F_73fc0 : fetch_word Asan.M.loaded_segments (0x73fc0 : word) = Some W_73fc0.
Proof. vm_refl. Qed.
Lemma D_73fc0 : decode_any W_73fc0 = Some (Store SZ1 2 10 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fc4 : bv 32 := 0x0ca10ba3.
Lemma F_73fc4 : fetch_word Asan.M.loaded_segments (0x73fc4 : word) = Some W_73fc4.
Proof. vm_refl. Qed.
Lemma D_73fc4 : decode_any W_73fc4 = Some (Store SZ1 2 10 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fc8 : bv 32 := 0x0d510993.
Lemma F_73fc8 : fetch_word Asan.M.loaded_segments (0x73fc8 : word) = Some W_73fc8.
Proof. vm_refl. Qed.
Lemma D_73fc8 : decode_any W_73fc8 = Some (OpImm ALU_ADD 19 2 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fcc : bv 32 := 0x0d510513.
Lemma F_73fcc : fetch_word Asan.M.loaded_segments (0x73fcc : word) = Some W_73fcc.
Proof. vm_refl. Qed.
Lemma D_73fcc : decode_any W_73fcc = Some (OpImm ALU_ADD 10 2 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fd0 : bv 32 := 0x00300613.
Lemma F_73fd0 : fetch_word Asan.M.loaded_segments (0x73fd0 : word) = Some W_73fd0.
Proof. vm_refl. Qed.
Lemma D_73fd0 : decode_any W_73fd0 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fd4 : bv 32 := 0x00300a13.
Lemma F_73fd4 : fetch_word Asan.M.loaded_segments (0x73fd4 : word) = Some W_73fd4.
Proof. vm_refl. Qed.
Lemma D_73fd4 : decode_any W_73fd4 = Some (OpImm ALU_ADD 20 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fd8 : bv 32 := 0x00000593.
Lemma F_73fd8 : fetch_word Asan.M.loaded_segments (0x73fd8 : word) = Some W_73fd8.
Proof. vm_refl. Qed.
Lemma D_73fd8 : decode_any W_73fd8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fdc : bv 32 := 0xb84fd0ef.
Lemma F_73fdc : fetch_word Asan.M.loaded_segments (0x73fdc : word) = Some W_73fdc.
Proof. vm_refl. Qed.
Lemma D_73fdc : decode_any W_73fdc = Some (Jal 1 2085764, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fe0 : bv 32 := 0x00100a93.
Lemma F_73fe0 : fetch_word Asan.M.loaded_segments (0x73fe0 : word) = Some W_73fe0.
Proof. vm_refl. Qed.
Lemma D_73fe0 : decode_any W_73fe0 = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fe4 : bv 32 := 0x0009051b.
Lemma F_73fe4 : fetch_word Asan.M.loaded_segments (0x73fe4 : word) = Some W_73fe4.
Proof. vm_refl. Qed.
Lemma D_73fe4 : decode_any W_73fe4 = Some (OpImm32 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fe8 : bv 32 := 0x00a985b3.
Lemma F_73fe8 : fetch_word Asan.M.loaded_segments (0x73fe8 : word) = Some W_73fe8.
Proof. vm_refl. Qed.
Lemma D_73fe8 : decode_any W_73fe8 = Some (Op ALU_ADD 11 19 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_73fec : bv 32 := 0x01558023.
Lemma F_73fec : fetch_word Asan.M.loaded_segments (0x73fec : word) = Some W_73fec.
Proof. vm_refl. Qed.
Lemma D_73fec : decode_any W_73fec = Some (Store SZ1 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73ff0 : bv 32 := 0xc9dfd0ef.
Lemma F_73ff0 : fetch_word Asan.M.loaded_segments (0x73ff0 : word) = Some W_73ff0.
Proof. vm_refl. Qed.
Lemma D_73ff0 : decode_any W_73ff0 = Some (Jal 1 2088092, 4%Z).
Proof. vm_refl. Qed.

Definition W_73ff4 : bv 32 := 0x0005091b.
Lemma F_73ff4 : fetch_word Asan.M.loaded_segments (0x73ff4 : word) = Some W_73ff4.
Proof. vm_refl. Qed.
Lemma D_73ff4 : decode_any W_73ff4 = Some (OpImm32 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73ff8 : bv 32 := 0xff4946e3.
Lemma F_73ff8 : fetch_word Asan.M.loaded_segments (0x73ff8 : word) = Some W_73ff8.
Proof. vm_refl. Qed.
Lemma D_73ff8 : decode_any W_73ff8 = Some (Branch BC_LT 18 20 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_73ffc : bv 32 := 0x0d514583.
Lemma F_73ffc : fetch_word Asan.M.loaded_segments (0x73ffc : word) = Some W_73ffc.
Proof. vm_refl. Qed.
Lemma D_73ffc : decode_any W_73ffc = Some (Load SZ1 false 11 2 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_74000 : bv 32 := 0x08059263.
Lemma F_74000 : fetch_word Asan.M.loaded_segments (0x74000 : word) = Some W_74000.
Proof. vm_refl. Qed.
Lemma D_74000 : decode_any W_74000 = Some (Branch BC_NE 11 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_74004 : bv 32 := 0x0d614583.
Lemma F_74004 : fetch_word Asan.M.loaded_segments (0x74004 : word) = Some W_74004.
Proof. vm_refl. Qed.
Lemma D_74004 : decode_any W_74004 = Some (Load SZ1 false 11 2 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_74008 : bv 32 := 0x08059a63.
Lemma F_74008 : fetch_word Asan.M.loaded_segments (0x74008 : word) = Some W_74008.
Proof. vm_refl. Qed.
Lemma D_74008 : decode_any W_74008 = Some (Branch BC_NE 11 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_7400c : bv 32 := 0x0d714583.
Lemma F_7400c : fetch_word Asan.M.loaded_segments (0x7400c : word) = Some W_7400c.
Proof. vm_refl. Qed.
Lemma D_7400c : decode_any W_7400c = Some (Load SZ1 false 11 2 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_74010 : bv 32 := 0x00058a63.
Lemma F_74010 : fetch_word Asan.M.loaded_segments (0x74010 : word) = Some W_74010.
Proof. vm_refl. Qed.
Lemma D_74010 : decode_any W_74010 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_74014 : bv 32 := 0x00050913.
Lemma F_74014 : fetch_word Asan.M.loaded_segments (0x74014 : word) = Some W_74014.
Proof. vm_refl. Qed.
Lemma D_74014 : decode_any W_74014 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74018 : bv 32 := 0x00200513.
Lemma F_74018 : fetch_word Asan.M.loaded_segments (0x74018 : word) = Some W_74018.
Proof. vm_refl. Qed.
Lemma D_74018 : decode_any W_74018 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7401c : bv 32 := 0xb99fd0ef.
Lemma F_7401c : fetch_word Asan.M.loaded_segments (0x7401c : word) = Some W_7401c.
Proof. vm_refl. Qed.
Lemma D_7401c : decode_any W_7401c = Some (Jal 1 2087832, 4%Z).
Proof. vm_refl. Qed.

Definition W_74020 : bv 32 := 0x00090513.
Lemma F_74020 : fetch_word Asan.M.loaded_segments (0x74020 : word) = Some W_74020.
Proof. vm_refl. Qed.
Lemma D_74020 : decode_any W_74020 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74024 : bv 32 := 0x00050913.
Lemma F_74024 : fetch_word Asan.M.loaded_segments (0x74024 : word) = Some W_74024.
Proof. vm_refl. Qed.
Lemma D_74024 : decode_any W_74024 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74028 : bv 32 := 0x0005051b.
Lemma F_74028 : fetch_word Asan.M.loaded_segments (0x74028 : word) = Some W_74028.
Proof. vm_refl. Qed.
Lemma D_74028 : decode_any W_74028 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7402c : bv 32 := 0x00048593.
Lemma F_7402c : fetch_word Asan.M.loaded_segments (0x7402c : word) = Some W_7402c.
Proof. vm_refl. Qed.
Lemma D_7402c : decode_any W_7402c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74030 : bv 32 := 0xc25fd0ef.
Lemma F_74030 : fetch_word Asan.M.loaded_segments (0x74030 : word) = Some W_74030.
Proof. vm_refl. Qed.
Lemma D_74030 : decode_any W_74030 = Some (Jal 1 2087972, 4%Z).
Proof. vm_refl. Qed.

Definition W_74034 : bv 32 := 0x02051513.
Lemma F_74034 : fetch_word Asan.M.loaded_segments (0x74034 : word) = Some W_74034.
Proof. vm_refl. Qed.
Lemma D_74034 : decode_any W_74034 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_74038 : bv 32 := 0x0a051063.
Lemma F_74038 : fetch_word Asan.M.loaded_segments (0x74038 : word) = Some W_74038.
Proof. vm_refl. Qed.
Lemma D_74038 : decode_any W_74038 = Some (Branch BC_NE 10 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7403c : bv 32 := 0x00d10513.
Lemma F_7403c : fetch_word Asan.M.loaded_segments (0x7403c : word) = Some W_7403c.
Proof. vm_refl. Qed.
Lemma D_7403c : decode_any W_7403c = Some (OpImm ALU_ADD 10 2 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_74040 : bv 32 := 0xc69fd0ef.
Lemma F_74040 : fetch_word Asan.M.loaded_segments (0x74040 : word) = Some W_74040.
Proof. vm_refl. Qed.
Lemma D_74040 : decode_any W_74040 = Some (Jal 1 2088040, 4%Z).
Proof. vm_refl. Qed.

Definition W_74044 : bv 32 := 0x02051513.
Lemma F_74044 : fetch_word Asan.M.loaded_segments (0x74044 : word) = Some W_74044.
Proof. vm_refl. Qed.
Lemma D_74044 : decode_any W_74044 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_74048 : bv 32 := 0x0a051863.
Lemma F_74048 : fetch_word Asan.M.loaded_segments (0x74048 : word) = Some W_74048.
Proof. vm_refl. Qed.
Lemma D_74048 : decode_any W_74048 = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7404c : bv 32 := 0x00046503.
Lemma F_7404c : fetch_word Asan.M.loaded_segments (0x7404c : word) = Some W_7404c.
Proof. vm_refl. Qed.
Lemma D_7404c : decode_any W_7404c = Some (Load SZ4 false 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74050 : bv 32 := 0xfdf57513.
Lemma F_74050 : fetch_word Asan.M.loaded_segments (0x74050 : word) = Some W_74050.
Proof. vm_refl. Qed.
Lemma D_74050 : decode_any W_74050 = Some (OpImm ALU_AND 10 10 4063, 4%Z).
Proof. vm_refl. Qed.

Definition W_74054 : bv 32 := 0x00a42023.
Lemma F_74054 : fetch_word Asan.M.loaded_segments (0x74054 : word) = Some W_74054.
Proof. vm_refl. Qed.
Lemma D_74054 : decode_any W_74054 = Some (Store SZ4 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74058 : bv 32 := 0x00090513.
Lemma F_74058 : fetch_word Asan.M.loaded_segments (0x74058 : word) = Some W_74058.
Proof. vm_refl. Qed.
Lemma D_74058 : decode_any W_74058 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7405c : bv 32 := 0x0005051b.
Lemma F_7405c : fetch_word Asan.M.loaded_segments (0x7405c : word) = Some W_7405c.
Proof. vm_refl. Qed.
Lemma D_7405c : decode_any W_7405c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74060 : bv 32 := 0x10813083.
Lemma F_74060 : fetch_word Asan.M.loaded_segments (0x74060 : word) = Some W_74060.
Proof. vm_refl. Qed.
Lemma D_74060 : decode_any W_74060 = Some (Load SZ8 true 1 2 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_74064 : bv 32 := 0x10013403.
Lemma F_74064 : fetch_word Asan.M.loaded_segments (0x74064 : word) = Some W_74064.
Proof. vm_refl. Qed.
Lemma D_74064 : decode_any W_74064 = Some (Load SZ8 true 8 2 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_74068 : bv 32 := 0x0f813483.
Lemma F_74068 : fetch_word Asan.M.loaded_segments (0x74068 : word) = Some W_74068.
Proof. vm_refl. Qed.
Lemma D_74068 : decode_any W_74068 = Some (Load SZ8 true 9 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_7406c : bv 32 := 0x0f013903.
Lemma F_7406c : fetch_word Asan.M.loaded_segments (0x7406c : word) = Some W_7406c.
Proof. vm_refl. Qed.
Lemma D_7406c : decode_any W_7406c = Some (Load SZ8 true 18 2 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_74070 : bv 32 := 0x0e813983.
Lemma F_74070 : fetch_word Asan.M.loaded_segments (0x74070 : word) = Some W_74070.
Proof. vm_refl. Qed.
Lemma D_74070 : decode_any W_74070 = Some (Load SZ8 true 19 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_74074 : bv 32 := 0x0e013a03.
Lemma F_74074 : fetch_word Asan.M.loaded_segments (0x74074 : word) = Some W_74074.
Proof. vm_refl. Qed.
Lemma D_74074 : decode_any W_74074 = Some (Load SZ8 true 20 2 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_74078 : bv 32 := 0x0d813a83.
Lemma F_74078 : fetch_word Asan.M.loaded_segments (0x74078 : word) = Some W_74078.
Proof. vm_refl. Qed.
Lemma D_74078 : decode_any W_74078 = Some (Load SZ8 true 21 2 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7407c : bv 32 := 0x11010113.
Lemma F_7407c : fetch_word Asan.M.loaded_segments (0x7407c : word) = Some W_7407c.
Proof. vm_refl. Qed.
Lemma D_7407c : decode_any W_7407c = Some (OpImm ALU_ADD 2 2 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_74080 : bv 32 := 0x00008067.
Lemma F_74080 : fetch_word Asan.M.loaded_segments (0x74080 : word) = Some W_74080.
Proof. vm_refl. Qed.
Lemma D_74080 : decode_any W_74080 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74084 : bv 32 := 0x00050913.
Lemma F_74084 : fetch_word Asan.M.loaded_segments (0x74084 : word) = Some W_74084.
Proof. vm_refl. Qed.
Lemma D_74084 : decode_any W_74084 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74088 : bv 32 := 0x00000513.
Lemma F_74088 : fetch_word Asan.M.loaded_segments (0x74088 : word) = Some W_74088.
Proof. vm_refl. Qed.
Lemma D_74088 : decode_any W_74088 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7408c : bv 32 := 0xb29fd0ef.
Lemma F_7408c : fetch_word Asan.M.loaded_segments (0x7408c : word) = Some W_7408c.
Proof. vm_refl. Qed.
Lemma D_7408c : decode_any W_7408c = Some (Jal 1 2087720, 4%Z).
Proof. vm_refl. Qed.

Definition W_74090 : bv 32 := 0x00090513.
Lemma F_74090 : fetch_word Asan.M.loaded_segments (0x74090 : word) = Some W_74090.
Proof. vm_refl. Qed.
Lemma D_74090 : decode_any W_74090 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74094 : bv 32 := 0x0d614583.
Lemma F_74094 : fetch_word Asan.M.loaded_segments (0x74094 : word) = Some W_74094.
Proof. vm_refl. Qed.
Lemma D_74094 : decode_any W_74094 = Some (Load SZ1 false 11 2 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_74098 : bv 32 := 0xf6058ae3.
Lemma F_74098 : fetch_word Asan.M.loaded_segments (0x74098 : word) = Some W_74098.
Proof. vm_refl. Qed.
Lemma D_74098 : decode_any W_74098 = Some (Branch BC_EQ 11 0 8052, 4%Z).
Proof. vm_refl. Qed.

Definition W_7409c : bv 32 := 0x00050913.
Lemma F_7409c : fetch_word Asan.M.loaded_segments (0x7409c : word) = Some W_7409c.
Proof. vm_refl. Qed.
Lemma D_7409c : decode_any W_7409c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_740a0 : bv 32 := 0x00100513.
Lemma F_740a0 : fetch_word Asan.M.loaded_segments (0x740a0 : word) = Some W_740a0.
Proof. vm_refl. Qed.
Lemma D_740a0 : decode_any W_740a0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_740a4 : bv 32 := 0xb11fd0ef.
Lemma F_740a4 : fetch_word Asan.M.loaded_segments (0x740a4 : word) = Some W_740a4.
Proof. vm_refl. Qed.
Lemma D_740a4 : decode_any W_740a4 = Some (Jal 1 2087696, 4%Z).
Proof. vm_refl. Qed.

Definition W_740a8 : bv 32 := 0x00090513.
Lemma F_740a8 : fetch_word Asan.M.loaded_segments (0x740a8 : word) = Some W_740a8.
Proof. vm_refl. Qed.
Lemma D_740a8 : decode_any W_740a8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_740ac : bv 32 := 0x0d714583.
Lemma F_740ac : fetch_word Asan.M.loaded_segments (0x740ac : word) = Some W_740ac.
Proof. vm_refl. Qed.
Lemma D_740ac : decode_any W_740ac = Some (Load SZ1 false 11 2 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_740b0 : bv 32 := 0xf60592e3.
Lemma F_740b0 : fetch_word Asan.M.loaded_segments (0x740b0 : word) = Some W_740b0.
Proof. vm_refl. Qed.
Lemma D_740b0 : decode_any W_740b0 = Some (Branch BC_NE 11 0 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_740b4 : bv 32 := 0xf71ff06f.
Lemma F_740b4 : fetch_word Asan.M.loaded_segments (0x740b4 : word) = Some W_740b4.
Proof. vm_refl. Qed.
Lemma D_740b4 : decode_any W_740b4 = Some (Jal 0 2097008, 4%Z).
Proof. vm_refl. Qed.

Definition W_740b8 : bv 32 := 0xfffa7517.
Lemma F_740b8 : fetch_word Asan.M.loaded_segments (0x740b8 : word) = Some W_740b8.
Proof. vm_refl. Qed.
Lemma D_740b8 : decode_any W_740b8 = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_740bc : bv 32 := 0xfffa4597.
Lemma F_740bc : fetch_word Asan.M.loaded_segments (0x740bc : word) = Some W_740bc.
Proof. vm_refl. Qed.
Lemma D_740bc : decode_any W_740bc = Some (Auipc 11 1048484, 4%Z).
Proof. vm_refl. Qed.

Definition W_740c0 : bv 32 := 0xb2350513.
Lemma F_740c0 : fetch_word Asan.M.loaded_segments (0x740c0 : word) = Some W_740c0.
Proof. vm_refl. Qed.
Lemma D_740c0 : decode_any W_740c0 = Some (OpImm ALU_ADD 10 10 2851, 4%Z).
Proof. vm_refl. Qed.

Definition W_740c4 : bv 32 := 0x5db58613.
Lemma F_740c4 : fetch_word Asan.M.loaded_segments (0x740c4 : word) = Some W_740c4.
Proof. vm_refl. Qed.
Lemma D_740c4 : decode_any W_740c4 = Some (OpImm ALU_ADD 12 11 1499, 4%Z).
Proof. vm_refl. Qed.

Definition W_740c8 : bv 32 := 0x18500593.
Lemma F_740c8 : fetch_word Asan.M.loaded_segments (0x740c8 : word) = Some W_740c8.
Proof. vm_refl. Qed.
Lemma D_740c8 : decode_any W_740c8 = Some (OpImm ALU_ADD 11 0 389, 4%Z).
Proof. vm_refl. Qed.

Definition W_740cc : bv 32 := 0x00000693.
Lemma F_740cc : fetch_word Asan.M.loaded_segments (0x740cc : word) = Some W_740cc.
Proof. vm_refl. Qed.
Lemma D_740cc : decode_any W_740cc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_740d0 : bv 32 := 0x00000713.
Lemma F_740d0 : fetch_word Asan.M.loaded_segments (0x740d0 : word) = Some W_740d0.
Proof. vm_refl. Qed.
Lemma D_740d0 : decode_any W_740d0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_740d4 : bv 32 := 0x795040ef.
Lemma F_740d4 : fetch_word Asan.M.loaded_segments (0x740d4 : word) = Some W_740d4.
Proof. vm_refl. Qed.
Lemma D_740d4 : decode_any W_740d4 = Some (Jal 1 20372, 4%Z).
Proof. vm_refl. Qed.

Definition W_740d8 : bv 32 := 0x42055713.
Lemma F_740d8 : fetch_word Asan.M.loaded_segments (0x740d8 : word) = Some W_740d8.
Proof. vm_refl. Qed.
Lemma D_740d8 : decode_any W_740d8 = Some (ShiftImm ALU_SRA 14 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_740dc : bv 32 := 0xfffa7517.
Lemma F_740dc : fetch_word Asan.M.loaded_segments (0x740dc : word) = Some W_740dc.
Proof. vm_refl. Qed.
Lemma D_740dc : decode_any W_740dc = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_740e0 : bv 32 := 0xfffab597.
Lemma F_740e0 : fetch_word Asan.M.loaded_segments (0x740e0 : word) = Some W_740e0.
Proof. vm_refl. Qed.
Lemma D_740e0 : decode_any W_740e0 = Some (Auipc 11 1048491, 4%Z).
Proof. vm_refl. Qed.

Definition W_740e4 : bv 32 := 0xaff50513.
Lemma F_740e4 : fetch_word Asan.M.loaded_segments (0x740e4 : word) = Some W_740e4.
Proof. vm_refl. Qed.
Lemma D_740e4 : decode_any W_740e4 = Some (OpImm ALU_ADD 10 10 2815, 4%Z).
Proof. vm_refl. Qed.

Definition W_740e8 : bv 32 := 0x93c58613.
Lemma F_740e8 : fetch_word Asan.M.loaded_segments (0x740e8 : word) = Some W_740e8.
Proof. vm_refl. Qed.
Lemma D_740e8 : decode_any W_740e8 = Some (OpImm ALU_ADD 12 11 2364, 4%Z).
Proof. vm_refl. Qed.

Definition W_740ec : bv 32 := 0x19400593.
Lemma F_740ec : fetch_word Asan.M.loaded_segments (0x740ec : word) = Some W_740ec.
Proof. vm_refl. Qed.
Lemma D_740ec : decode_any W_740ec = Some (OpImm ALU_ADD 11 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_740f0 : bv 32 := 0x00000693.
Lemma F_740f0 : fetch_word Asan.M.loaded_segments (0x740f0 : word) = Some W_740f0.
Proof. vm_refl. Qed.
Lemma D_740f0 : decode_any W_740f0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_740f4 : bv 32 := 0x775040ef.
Lemma F_740f4 : fetch_word Asan.M.loaded_segments (0x740f4 : word) = Some W_740f4.
Proof. vm_refl. Qed.
Lemma D_740f4 : decode_any W_740f4 = Some (Jal 1 20340, 4%Z).
Proof. vm_refl. Qed.

Definition W_740f8 : bv 32 := 0x42055713.
Lemma F_740f8 : fetch_word Asan.M.loaded_segments (0x740f8 : word) = Some W_740f8.
Proof. vm_refl. Qed.
Lemma D_740f8 : decode_any W_740f8 = Some (ShiftImm ALU_SRA 14 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_740fc : bv 32 := 0xfffa7517.
Lemma F_740fc : fetch_word Asan.M.loaded_segments (0x740fc : word) = Some W_740fc.
Proof. vm_refl. Qed.
Lemma D_740fc : decode_any W_740fc = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_74100 : bv 32 := 0xfffab597.
Lemma F_74100 : fetch_word Asan.M.loaded_segments (0x74100 : word) = Some W_74100.
Proof. vm_refl. Qed.
Lemma D_74100 : decode_any W_74100 = Some (Auipc 11 1048491, 4%Z).
Proof. vm_refl. Qed.

Definition W_74104 : bv 32 := 0xadf50513.
Lemma F_74104 : fetch_word Asan.M.loaded_segments (0x74104 : word) = Some W_74104.
Proof. vm_refl. Qed.
Lemma D_74104 : decode_any W_74104 = Some (OpImm ALU_ADD 10 10 2783, 4%Z).
Proof. vm_refl. Qed.

Definition W_74108 : bv 32 := 0x91c58613.
Lemma F_74108 : fetch_word Asan.M.loaded_segments (0x74108 : word) = Some W_74108.
Proof. vm_refl. Qed.
Lemma D_74108 : decode_any W_74108 = Some (OpImm ALU_ADD 12 11 2332, 4%Z).
Proof. vm_refl. Qed.

Definition W_7410c : bv 32 := 0x19600593.
Lemma F_7410c : fetch_word Asan.M.loaded_segments (0x7410c : word) = Some W_7410c.
Proof. vm_refl. Qed.
Lemma D_7410c : decode_any W_7410c = Some (OpImm ALU_ADD 11 0 406, 4%Z).
Proof. vm_refl. Qed.

Definition W_74110 : bv 32 := 0x00000693.
Lemma F_74110 : fetch_word Asan.M.loaded_segments (0x74110 : word) = Some W_74110.
Proof. vm_refl. Qed.
Lemma D_74110 : decode_any W_74110 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74114 : bv 32 := 0x755040ef.
Lemma F_74114 : fetch_word Asan.M.loaded_segments (0x74114 : word) = Some W_74114.
Proof. vm_refl. Qed.
Lemma D_74114 : decode_any W_74114 = Some (Jal 1 20308, 4%Z).
Proof. vm_refl. Qed.
