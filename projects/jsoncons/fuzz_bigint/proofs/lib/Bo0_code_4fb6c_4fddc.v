(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_4fb6c : bv 32 := 0x81010113.
Lemma F_4fb6c : fetch_word AsanUbsan.M.loaded_segments (0x4fb6c : word) = Some W_4fb6c.
Proof. vm_refl. Qed.
Lemma D_4fb6c : decode_any W_4fb6c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb70 : bv 32 := 0x7e113423.
Lemma F_4fb70 : fetch_word AsanUbsan.M.loaded_segments (0x4fb70 : word) = Some W_4fb70.
Proof. vm_refl. Qed.
Lemma D_4fb70 : decode_any W_4fb70 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb74 : bv 32 := 0x7e813023.
Lemma F_4fb74 : fetch_word AsanUbsan.M.loaded_segments (0x4fb74 : word) = Some W_4fb74.
Proof. vm_refl. Qed.
Lemma D_4fb74 : decode_any W_4fb74 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb78 : bv 32 := 0x7c913c23.
Lemma F_4fb78 : fetch_word AsanUbsan.M.loaded_segments (0x4fb78 : word) = Some W_4fb78.
Proof. vm_refl. Qed.
Lemma D_4fb78 : decode_any W_4fb78 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb7c : bv 32 := 0x7d213823.
Lemma F_4fb7c : fetch_word AsanUbsan.M.loaded_segments (0x4fb7c : word) = Some W_4fb7c.
Proof. vm_refl. Qed.
Lemma D_4fb7c : decode_any W_4fb7c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb80 : bv 32 := 0x7d313423.
Lemma F_4fb80 : fetch_word AsanUbsan.M.loaded_segments (0x4fb80 : word) = Some W_4fb80.
Proof. vm_refl. Qed.
Lemma D_4fb80 : decode_any W_4fb80 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb84 : bv 32 := 0x7d413023.
Lemma F_4fb84 : fetch_word AsanUbsan.M.loaded_segments (0x4fb84 : word) = Some W_4fb84.
Proof. vm_refl. Qed.
Lemma D_4fb84 : decode_any W_4fb84 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb88 : bv 32 := 0x7f010413.
Lemma F_4fb88 : fetch_word AsanUbsan.M.loaded_segments (0x4fb88 : word) = Some W_4fb88.
Proof. vm_refl. Qed.
Lemma D_4fb88 : decode_any W_4fb88 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb8c : bv 32 := 0xfa010113.
Lemma F_4fb8c : fetch_word AsanUbsan.M.loaded_segments (0x4fb8c : word) = Some W_4fb8c.
Proof. vm_refl. Qed.
Lemma D_4fb8c : decode_any W_4fb8c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb90 : bv 32 := 0x00060913.
Lemma F_4fb90 : fetch_word AsanUbsan.M.loaded_segments (0x4fb90 : word) = Some W_4fb90.
Proof. vm_refl. Qed.
Lemma D_4fb90 : decode_any W_4fb90 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb94 : bv 32 := 0x00058493.
Lemma F_4fb94 : fetch_word AsanUbsan.M.loaded_segments (0x4fb94 : word) = Some W_4fb94.
Proof. vm_refl. Qed.
Lemma D_4fb94 : decode_any W_4fb94 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb98 : bv 32 := 0x00050993.
Lemma F_4fb98 : fetch_word AsanUbsan.M.loaded_segments (0x4fb98 : word) = Some W_4fb98.
Proof. vm_refl. Qed.
Lemma D_4fb98 : decode_any W_4fb98 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fb9c : bv 32 := 0x6c8170ef.
Lemma F_4fb9c : fetch_word AsanUbsan.M.loaded_segments (0x4fb9c : word) = Some W_4fb9c.
Proof. vm_refl. Qed.
Lemma D_4fb9c : decode_any W_4fb9c = Some (Jal 1 95944, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fba0 : bv 32 := 0x00088597.
Lemma F_4fba0 : fetch_word AsanUbsan.M.loaded_segments (0x4fba0 : word) = Some W_4fba0.
Proof. vm_refl. Qed.
Lemma D_4fba0 : decode_any W_4fba0 = Some (Auipc 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fba4 : bv 32 := 0x7385b683.
Lemma F_4fba4 : fetch_word AsanUbsan.M.loaded_segments (0x4fba4 : word) = Some W_4fba4.
Proof. vm_refl. Qed.
Lemma D_4fba4 : decode_any W_4fba4 = Some (Load SZ8 true 13 11 1848, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fba8 : bv 32 := 0x00050a13.
Lemma F_4fba8 : fetch_word AsanUbsan.M.loaded_segments (0x4fba8 : word) = Some W_4fba8.
Proof. vm_refl. Qed.
Lemma D_4fba8 : decode_any W_4fba8 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbac : bv 32 := 0x00098513.
Lemma F_4fbac : fetch_word AsanUbsan.M.loaded_segments (0x4fbac : word) = Some W_4fbac.
Proof. vm_refl. Qed.
Lemma D_4fbac : decode_any W_4fbac = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbb0 : bv 32 := 0x00048593.
Lemma F_4fbb0 : fetch_word AsanUbsan.M.loaded_segments (0x4fbb0 : word) = Some W_4fbb0.
Proof. vm_refl. Qed.
Lemma D_4fbb0 : decode_any W_4fbb0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbb4 : bv 32 := 0x00090613.
Lemma F_4fbb4 : fetch_word AsanUbsan.M.loaded_segments (0x4fbb4 : word) = Some W_4fbb4.
Proof. vm_refl. Qed.
Lemma D_4fbb4 : decode_any W_4fbb4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbb8 : bv 32 := 0x000680e7.
Lemma F_4fbb8 : fetch_word AsanUbsan.M.loaded_segments (0x4fbb8 : word) = Some W_4fbb8.
Proof. vm_refl. Qed.
Lemma D_4fbb8 : decode_any W_4fbb8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbbc : bv 32 := 0x060a0063.
Lemma F_4fbbc : fetch_word AsanUbsan.M.loaded_segments (0x4fbbc : word) = Some W_4fbbc.
Proof. vm_refl. Qed.
Lemma D_4fbbc : decode_any W_4fbbc = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbc0 : bv 32 := 0x04a05e63.
Lemma F_4fbc0 : fetch_word AsanUbsan.M.loaded_segments (0x4fbc0 : word) = Some W_4fbc0.
Proof. vm_refl. Qed.
Lemma D_4fbc0 : decode_any W_4fbc0 = Some (Branch BC_GE 0 10 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbc4 : bv 32 := 0xfff4c593.
Lemma F_4fbc4 : fetch_word AsanUbsan.M.loaded_segments (0x4fbc4 : word) = Some W_4fbc4.
Proof. vm_refl. Qed.
Lemma D_4fbc4 : decode_any W_4fbc4 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbc8 : bv 32 := 0x80040a13.
Lemma F_4fbc8 : fetch_word AsanUbsan.M.loaded_segments (0x4fbc8 : word) = Some W_4fbc8.
Proof. vm_refl. Qed.
Lemma D_4fbc8 : decode_any W_4fbc8 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbcc : bv 32 := 0xfb8a0a13.
Lemma F_4fbcc : fetch_word AsanUbsan.M.loaded_segments (0x4fbcc : word) = Some W_4fbcc.
Proof. vm_refl. Qed.
Lemma D_4fbcc : decode_any W_4fbcc = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbd0 : bv 32 := 0x06a5e863.
Lemma F_4fbd0 : fetch_word AsanUbsan.M.loaded_segments (0x4fbd0 : word) = Some W_4fbd0.
Proof. vm_refl. Qed.
Lemma D_4fbd0 : decode_any W_4fbd0 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbd4 : bv 32 := 0xfbf50593.
Lemma F_4fbd4 : fetch_word AsanUbsan.M.loaded_segments (0x4fbd4 : word) = Some W_4fbd4.
Proof. vm_refl. Qed.
Lemma D_4fbd4 : decode_any W_4fbd4 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbd8 : bv 32 := 0xfc000613.
Lemma F_4fbd8 : fetch_word AsanUbsan.M.loaded_segments (0x4fbd8 : word) = Some W_4fbd8.
Proof. vm_refl. Qed.
Lemma D_4fbd8 : decode_any W_4fbd8 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbdc : bv 32 := 0x0cc5ee63.
Lemma F_4fbdc : fetch_word AsanUbsan.M.loaded_segments (0x4fbdc : word) = Some W_4fbdc.
Proof. vm_refl. Qed.
Lemma D_4fbdc : decode_any W_4fbdc = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbe0 : bv 32 := 0x00087597.
Lemma F_4fbe0 : fetch_word AsanUbsan.M.loaded_segments (0x4fbe0 : word) = Some W_4fbe0.
Proof. vm_refl. Qed.
Lemma D_4fbe0 : decode_any W_4fbe0 = Some (Auipc 11 135, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbe4 : bv 32 := 0x8e85b583.
Lemma F_4fbe4 : fetch_word AsanUbsan.M.loaded_segments (0x4fbe4 : word) = Some W_4fbe4.
Proof. vm_refl. Qed.
Lemma D_4fbe4 : decode_any W_4fbe4 = Some (Load SZ8 true 11 11 2280, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbe8 : bv 32 := 0x00a486b3.
Lemma F_4fbe8 : fetch_word AsanUbsan.M.loaded_segments (0x4fbe8 : word) = Some W_4fbe8.
Proof. vm_refl. Qed.
Lemma D_4fbe8 : decode_any W_4fbe8 = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbec : bv 32 := 0x0005b603.
Lemma F_4fbec : fetch_word AsanUbsan.M.loaded_segments (0x4fbec : word) = Some W_4fbec.
Proof. vm_refl. Qed.
Lemma D_4fbec : decode_any W_4fbec = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbf0 : bv 32 := 0x0034d593.
Lemma F_4fbf0 : fetch_word AsanUbsan.M.loaded_segments (0x4fbf0 : word) = Some W_4fbf0.
Proof. vm_refl. Qed.
Lemma D_4fbf0 : decode_any W_4fbf0 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbf4 : bv 32 := 0xfff68693.
Lemma F_4fbf4 : fetch_word AsanUbsan.M.loaded_segments (0x4fbf4 : word) = Some W_4fbf4.
Proof. vm_refl. Qed.
Lemma D_4fbf4 : decode_any W_4fbf4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbf8 : bv 32 := 0x0036d713.
Lemma F_4fbf8 : fetch_word AsanUbsan.M.loaded_segments (0x4fbf8 : word) = Some W_4fbf8.
Proof. vm_refl. Qed.
Lemma D_4fbf8 : decode_any W_4fbf8 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fbfc : bv 32 := 0x00b605b3.
Lemma F_4fbfc : fetch_word AsanUbsan.M.loaded_segments (0x4fbfc : word) = Some W_4fbfc.
Proof. vm_refl. Qed.
Lemma D_4fbfc : decode_any W_4fbfc = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc00 : bv 32 := 0x00e60633.
Lemma F_4fc00 : fetch_word AsanUbsan.M.loaded_segments (0x4fc00 : word) = Some W_4fc00.
Proof. vm_refl. Qed.
Lemma D_4fc00 : decode_any W_4fc00 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc04 : bv 32 := 0xff85f713.
Lemma F_4fc04 : fetch_word AsanUbsan.M.loaded_segments (0x4fc04 : word) = Some W_4fc04.
Proof. vm_refl. Qed.
Lemma D_4fc04 : decode_any W_4fc04 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc08 : bv 32 := 0xff867793.
Lemma F_4fc08 : fetch_word AsanUbsan.M.loaded_segments (0x4fc08 : word) = Some W_4fc08.
Proof. vm_refl. Qed.
Lemma D_4fc08 : decode_any W_4fc08 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc0c : bv 32 := 0x00073703.
Lemma F_4fc0c : fetch_word AsanUbsan.M.loaded_segments (0x4fc0c : word) = Some W_4fc0c.
Proof. vm_refl. Qed.
Lemma D_4fc0c : decode_any W_4fc0c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc10 : bv 32 := 0x0007b783.
Lemma F_4fc10 : fetch_word AsanUbsan.M.loaded_segments (0x4fc10 : word) = Some W_4fc10.
Proof. vm_refl. Qed.
Lemma D_4fc10 : decode_any W_4fc10 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc14 : bv 32 := 0x00e7e733.
Lemma F_4fc14 : fetch_word AsanUbsan.M.loaded_segments (0x4fc14 : word) = Some W_4fc14.
Proof. vm_refl. Qed.
Lemma D_4fc14 : decode_any W_4fc14 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc18 : bv 32 := 0x14071663.
Lemma F_4fc18 : fetch_word AsanUbsan.M.loaded_segments (0x4fc18 : word) = Some W_4fc18.
Proof. vm_refl. Qed.
Lemma D_4fc18 : decode_any W_4fc18 = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc1c : bv 32 := 0x06010113.
Lemma F_4fc1c : fetch_word AsanUbsan.M.loaded_segments (0x4fc1c : word) = Some W_4fc1c.
Proof. vm_refl. Qed.
Lemma D_4fc1c : decode_any W_4fc1c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc20 : bv 32 := 0x7e813083.
Lemma F_4fc20 : fetch_word AsanUbsan.M.loaded_segments (0x4fc20 : word) = Some W_4fc20.
Proof. vm_refl. Qed.
Lemma D_4fc20 : decode_any W_4fc20 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc24 : bv 32 := 0x7e013403.
Lemma F_4fc24 : fetch_word AsanUbsan.M.loaded_segments (0x4fc24 : word) = Some W_4fc24.
Proof. vm_refl. Qed.
Lemma D_4fc24 : decode_any W_4fc24 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc28 : bv 32 := 0x7d813483.
Lemma F_4fc28 : fetch_word AsanUbsan.M.loaded_segments (0x4fc28 : word) = Some W_4fc28.
Proof. vm_refl. Qed.
Lemma D_4fc28 : decode_any W_4fc28 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc2c : bv 32 := 0x7d013903.
Lemma F_4fc2c : fetch_word AsanUbsan.M.loaded_segments (0x4fc2c : word) = Some W_4fc2c.
Proof. vm_refl. Qed.
Lemma D_4fc2c : decode_any W_4fc2c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc30 : bv 32 := 0x7c813983.
Lemma F_4fc30 : fetch_word AsanUbsan.M.loaded_segments (0x4fc30 : word) = Some W_4fc30.
Proof. vm_refl. Qed.
Lemma D_4fc30 : decode_any W_4fc30 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc34 : bv 32 := 0x7c013a03.
Lemma F_4fc34 : fetch_word AsanUbsan.M.loaded_segments (0x4fc34 : word) = Some W_4fc34.
Proof. vm_refl. Qed.
Lemma D_4fc34 : decode_any W_4fc34 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc38 : bv 32 := 0x7f010113.
Lemma F_4fc38 : fetch_word AsanUbsan.M.loaded_segments (0x4fc38 : word) = Some W_4fc38.
Proof. vm_refl. Qed.
Lemma D_4fc38 : decode_any W_4fc38 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc3c : bv 32 := 0x00008067.
Lemma F_4fc3c : fetch_word AsanUbsan.M.loaded_segments (0x4fc3c : word) = Some W_4fc3c.
Proof. vm_refl. Qed.
Lemma D_4fc3c : decode_any W_4fc3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc40 : bv 32 := 0x80040593.
Lemma F_4fc40 : fetch_word AsanUbsan.M.loaded_segments (0x4fc40 : word) = Some W_4fc40.
Proof. vm_refl. Qed.
Lemma D_4fc40 : decode_any W_4fc40 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc44 : bv 32 := 0xfc858593.
Lemma F_4fc44 : fetch_word AsanUbsan.M.loaded_segments (0x4fc44 : word) = Some W_4fc44.
Proof. vm_refl. Qed.
Lemma D_4fc44 : decode_any W_4fc44 = Some (OpImm ALU_ADD 11 11 4040, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc48 : bv 32 := 0x80040613.
Lemma F_4fc48 : fetch_word AsanUbsan.M.loaded_segments (0x4fc48 : word) = Some W_4fc48.
Proof. vm_refl. Qed.
Lemma D_4fc48 : decode_any W_4fc48 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc4c : bv 32 := 0xfb860613.
Lemma F_4fc4c : fetch_word AsanUbsan.M.loaded_segments (0x4fc4c : word) = Some W_4fc4c.
Proof. vm_refl. Qed.
Lemma D_4fc4c : decode_any W_4fc4c = Some (OpImm ALU_ADD 12 12 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc50 : bv 32 := 0x7ff60993.
Lemma F_4fc50 : fetch_word AsanUbsan.M.loaded_segments (0x4fc50 : word) = Some W_4fc50.
Proof. vm_refl. Qed.
Lemma D_4fc50 : decode_any W_4fc50 = Some (OpImm ALU_ADD 19 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc54 : bv 32 := 0x0009b4a3.
Lemma F_4fc54 : fetch_word AsanUbsan.M.loaded_segments (0x4fc54 : word) = Some W_4fc54.
Proof. vm_refl. Qed.
Lemma D_4fc54 : decode_any W_4fc54 = Some (Store SZ8 19 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc58 : bv 32 := 0x00ba3023.
Lemma F_4fc58 : fetch_word AsanUbsan.M.loaded_segments (0x4fc58 : word) = Some W_4fc58.
Proof. vm_refl. Qed.
Lemma D_4fc58 : decode_any W_4fc58 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc5c : bv 32 := 0x000a3423.
Lemma F_4fc5c : fetch_word AsanUbsan.M.loaded_segments (0x4fc5c : word) = Some W_4fc5c.
Proof. vm_refl. Qed.
Lemma D_4fc5c : decode_any W_4fc5c = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc60 : bv 32 := 0x00050913.
Lemma F_4fc60 : fetch_word AsanUbsan.M.loaded_segments (0x4fc60 : word) = Some W_4fc60.
Proof. vm_refl. Qed.
Lemma D_4fc60 : decode_any W_4fc60 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc64 : bv 32 := 0x649300ef.
Lemma F_4fc64 : fetch_word AsanUbsan.M.loaded_segments (0x4fc64 : word) = Some W_4fc64.
Proof. vm_refl. Qed.
Lemma D_4fc64 : decode_any W_4fc64 = Some (Jal 1 200264, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc68 : bv 32 := 0x00050593.
Lemma F_4fc68 : fetch_word AsanUbsan.M.loaded_segments (0x4fc68 : word) = Some W_4fc68.
Proof. vm_refl. Qed.
Lemma D_4fc68 : decode_any W_4fc68 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc6c : bv 32 := 0x00087517.
Lemma F_4fc6c : fetch_word AsanUbsan.M.loaded_segments (0x4fc6c : word) = Some W_4fc6c.
Proof. vm_refl. Qed.
Lemma D_4fc6c : decode_any W_4fc6c = Some (Auipc 10 135, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc70 : bv 32 := 0x84c53503.
Lemma F_4fc70 : fetch_word AsanUbsan.M.loaded_segments (0x4fc70 : word) = Some W_4fc70.
Proof. vm_refl. Qed.
Lemma D_4fc70 : decode_any W_4fc70 = Some (Load SZ8 true 10 10 2124, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc74 : bv 32 := 0x02154703.
Lemma F_4fc74 : fetch_word AsanUbsan.M.loaded_segments (0x4fc74 : word) = Some W_4fc74.
Proof. vm_refl. Qed.
Lemma D_4fc74 : decode_any W_4fc74 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc78 : bv 32 := 0x0089b4a3.
Lemma F_4fc78 : fetch_word AsanUbsan.M.loaded_segments (0x4fc78 : word) = Some W_4fc78.
Proof. vm_refl. Qed.
Lemma D_4fc78 : decode_any W_4fc78 = Some (Store SZ8 19 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc7c : bv 32 := 0x80040513.
Lemma F_4fc7c : fetch_word AsanUbsan.M.loaded_segments (0x4fc7c : word) = Some W_4fc7c.
Proof. vm_refl. Qed.
Lemma D_4fc7c : decode_any W_4fc7c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc80 : bv 32 := 0xfb850513.
Lemma F_4fc80 : fetch_word AsanUbsan.M.loaded_segments (0x4fc80 : word) = Some W_4fc80.
Proof. vm_refl. Qed.
Lemma D_4fc80 : decode_any W_4fc80 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc84 : bv 32 := 0x0ff00793.
Lemma F_4fc84 : fetch_word AsanUbsan.M.loaded_segments (0x4fc84 : word) = Some W_4fc84.
Proof. vm_refl. Qed.
Lemma D_4fc84 : decode_any W_4fc84 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc88 : bv 32 := 0x00040613.
Lemma F_4fc88 : fetch_word AsanUbsan.M.loaded_segments (0x4fc88 : word) = Some W_4fc88.
Proof. vm_refl. Qed.
Lemma D_4fc88 : decode_any W_4fc88 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc8c : bv 32 := 0x00000693.
Lemma F_4fc8c : fetch_word AsanUbsan.M.loaded_segments (0x4fc8c : word) = Some W_4fc8c.
Proof. vm_refl. Qed.
Lemma D_4fc8c : decode_any W_4fc8c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc90 : bv 32 := 0x36c180ef.
Lemma F_4fc90 : fetch_word AsanUbsan.M.loaded_segments (0x4fc90 : word) = Some W_4fc90.
Proof. vm_refl. Qed.
Lemma D_4fc90 : decode_any W_4fc90 = Some (Jal 1 99180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc94 : bv 32 := 0x80040613.
Lemma F_4fc94 : fetch_word AsanUbsan.M.loaded_segments (0x4fc94 : word) = Some W_4fc94.
Proof. vm_refl. Qed.
Lemma D_4fc94 : decode_any W_4fc94 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc98 : bv 32 := 0xfb860613.
Lemma F_4fc98 : fetch_word AsanUbsan.M.loaded_segments (0x4fc98 : word) = Some W_4fc98.
Proof. vm_refl. Qed.
Lemma D_4fc98 : decode_any W_4fc98 = Some (OpImm ALU_ADD 12 12 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fc9c : bv 32 := 0x00048513.
Lemma F_4fc9c : fetch_word AsanUbsan.M.loaded_segments (0x4fc9c : word) = Some W_4fc9c.
Proof. vm_refl. Qed.
Lemma D_4fc9c : decode_any W_4fc9c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fca0 : bv 32 := 0x00090593.
Lemma F_4fca0 : fetch_word AsanUbsan.M.loaded_segments (0x4fca0 : word) = Some W_4fca0.
Proof. vm_refl. Qed.
Lemma D_4fca0 : decode_any W_4fca0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fca4 : bv 32 := 0x110150ef.
Lemma F_4fca4 : fetch_word AsanUbsan.M.loaded_segments (0x4fca4 : word) = Some W_4fca4.
Proof. vm_refl. Qed.
Lemma D_4fca4 : decode_any W_4fca4 = Some (Jal 1 86288, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fca8 : bv 32 := 0x00090513.
Lemma F_4fca8 : fetch_word AsanUbsan.M.loaded_segments (0x4fca8 : word) = Some W_4fca8.
Proof. vm_refl. Qed.
Lemma D_4fca8 : decode_any W_4fca8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcac : bv 32 := 0xfbf90593.
Lemma F_4fcac : fetch_word AsanUbsan.M.loaded_segments (0x4fcac : word) = Some W_4fcac.
Proof. vm_refl. Qed.
Lemma D_4fcac : decode_any W_4fcac = Some (OpImm ALU_ADD 11 18 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcb0 : bv 32 := 0xfc000613.
Lemma F_4fcb0 : fetch_word AsanUbsan.M.loaded_segments (0x4fcb0 : word) = Some W_4fcb0.
Proof. vm_refl. Qed.
Lemma D_4fcb0 : decode_any W_4fcb0 = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcb4 : bv 32 := 0xf2c5f6e3.
Lemma F_4fcb4 : fetch_word AsanUbsan.M.loaded_segments (0x4fcb4 : word) = Some W_4fcb4.
Proof. vm_refl. Qed.
Lemma D_4fcb4 : decode_any W_4fcb4 = Some (Branch BC_GEU 11 12 7980, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcb8 : bv 32 := 0x00050913.
Lemma F_4fcb8 : fetch_word AsanUbsan.M.loaded_segments (0x4fcb8 : word) = Some W_4fcb8.
Proof. vm_refl. Qed.
Lemma D_4fcb8 : decode_any W_4fcb8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcbc : bv 32 := 0x00048513.
Lemma F_4fcbc : fetch_word AsanUbsan.M.loaded_segments (0x4fcbc : word) = Some W_4fcbc.
Proof. vm_refl. Qed.
Lemma D_4fcbc : decode_any W_4fcbc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcc0 : bv 32 := 0x00090593.
Lemma F_4fcc0 : fetch_word AsanUbsan.M.loaded_segments (0x4fcc0 : word) = Some W_4fcc0.
Proof. vm_refl. Qed.
Lemma D_4fcc0 : decode_any W_4fcc0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcc4 : bv 32 := 0x6bd110ef.
Lemma F_4fcc4 : fetch_word AsanUbsan.M.loaded_segments (0x4fcc4 : word) = Some W_4fcc4.
Proof. vm_refl. Qed.
Lemma D_4fcc4 : decode_any W_4fcc4 = Some (Jal 1 73404, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcc8 : bv 32 := 0x00050493.
Lemma F_4fcc8 : fetch_word AsanUbsan.M.loaded_segments (0x4fcc8 : word) = Some W_4fcc8.
Proof. vm_refl. Qed.
Lemma D_4fcc8 : decode_any W_4fcc8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fccc : bv 32 := 0x00090513.
Lemma F_4fccc : fetch_word AsanUbsan.M.loaded_segments (0x4fccc : word) = Some W_4fccc.
Proof. vm_refl. Qed.
Lemma D_4fccc : decode_any W_4fccc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcd0 : bv 32 := 0xf40486e3.
Lemma F_4fcd0 : fetch_word AsanUbsan.M.loaded_segments (0x4fcd0 : word) = Some W_4fcd0.
Proof. vm_refl. Qed.
Lemma D_4fcd0 : decode_any W_4fcd0 = Some (Branch BC_EQ 9 0 8012, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcd4 : bv 32 := 0xfffc6517.
Lemma F_4fcd4 : fetch_word AsanUbsan.M.loaded_segments (0x4fcd4 : word) = Some W_4fcd4.
Proof. vm_refl. Qed.
Lemma D_4fcd4 : decode_any W_4fcd4 = Some (Auipc 10 1048518, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcd8 : bv 32 := 0x4b050513.
Lemma F_4fcd8 : fetch_word AsanUbsan.M.loaded_segments (0x4fcd8 : word) = Some W_4fcd8.
Proof. vm_refl. Qed.
Lemma D_4fcd8 : decode_any W_4fcd8 = Some (OpImm ALU_ADD 10 10 1200, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcdc : bv 32 := 0x2cc190ef.
Lemma F_4fcdc : fetch_word AsanUbsan.M.loaded_segments (0x4fcdc : word) = Some W_4fcdc.
Proof. vm_refl. Qed.
Lemma D_4fcdc : decode_any W_4fcdc = Some (Jal 1 103116, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fce0 : bv 32 := 0x00050593.
Lemma F_4fce0 : fetch_word AsanUbsan.M.loaded_segments (0x4fce0 : word) = Some W_4fce0.
Proof. vm_refl. Qed.
Lemma D_4fce0 : decode_any W_4fce0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fce4 : bv 32 := 0x00090513.
Lemma F_4fce4 : fetch_word AsanUbsan.M.loaded_segments (0x4fce4 : word) = Some W_4fce4.
Proof. vm_refl. Qed.
Lemma D_4fce4 : decode_any W_4fce4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fce8 : bv 32 := 0xf2059ae3.
Lemma F_4fce8 : fetch_word AsanUbsan.M.loaded_segments (0x4fce8 : word) = Some W_4fce8.
Proof. vm_refl. Qed.
Lemma D_4fce8 : decode_any W_4fce8 = Some (Branch BC_NE 11 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcec : bv 32 := 0x324190ef.
Lemma F_4fcec : fetch_word AsanUbsan.M.loaded_segments (0x4fcec : word) = Some W_4fcec.
Proof. vm_refl. Qed.
Lemma D_4fcec : decode_any W_4fcec = Some (Jal 1 103204, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcf0 : bv 32 := 0x0a050663.
Lemma F_4fcf0 : fetch_word AsanUbsan.M.loaded_segments (0x4fcf0 : word) = Some W_4fcf0.
Proof. vm_refl. Qed.
Lemma D_4fcf0 : decode_any W_4fcf0 = Some (Branch BC_EQ 10 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcf4 : bv 32 := 0x80040513.
Lemma F_4fcf4 : fetch_word AsanUbsan.M.loaded_segments (0x4fcf4 : word) = Some W_4fcf4.
Proof. vm_refl. Qed.
Lemma D_4fcf4 : decode_any W_4fcf4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcf8 : bv 32 := 0xfc850513.
Lemma F_4fcf8 : fetch_word AsanUbsan.M.loaded_segments (0x4fcf8 : word) = Some W_4fcf8.
Proof. vm_refl. Qed.
Lemma D_4fcf8 : decode_any W_4fcf8 = Some (OpImm ALU_ADD 10 10 4040, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fcfc : bv 32 := 0x80040593.
Lemma F_4fcfc : fetch_word AsanUbsan.M.loaded_segments (0x4fcfc : word) = Some W_4fcfc.
Proof. vm_refl. Qed.
Lemma D_4fcfc : decode_any W_4fcfc = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd00 : bv 32 := 0xfb858593.
Lemma F_4fd00 : fetch_word AsanUbsan.M.loaded_segments (0x4fd00 : word) = Some W_4fd00.
Proof. vm_refl. Qed.
Lemma D_4fd00 : decode_any W_4fd00 = Some (OpImm ALU_ADD 11 11 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd04 : bv 32 := 0x7ff58993.
Lemma F_4fd04 : fetch_word AsanUbsan.M.loaded_segments (0x4fd04 : word) = Some W_4fd04.
Proof. vm_refl. Qed.
Lemma D_4fd04 : decode_any W_4fd04 = Some (OpImm ALU_ADD 19 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd08 : bv 32 := 0x0009b4a3.
Lemma F_4fd08 : fetch_word AsanUbsan.M.loaded_segments (0x4fd08 : word) = Some W_4fd08.
Proof. vm_refl. Qed.
Lemma D_4fd08 : decode_any W_4fd08 = Some (Store SZ8 19 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd0c : bv 32 := 0x00aa3023.
Lemma F_4fd0c : fetch_word AsanUbsan.M.loaded_segments (0x4fd0c : word) = Some W_4fd0c.
Proof. vm_refl. Qed.
Lemma D_4fd0c : decode_any W_4fd0c = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd10 : bv 32 := 0x000a3423.
Lemma F_4fd10 : fetch_word AsanUbsan.M.loaded_segments (0x4fd10 : word) = Some W_4fd10.
Proof. vm_refl. Qed.
Lemma D_4fd10 : decode_any W_4fd10 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd14 : bv 32 := 0x599300ef.
Lemma F_4fd14 : fetch_word AsanUbsan.M.loaded_segments (0x4fd14 : word) = Some W_4fd14.
Proof. vm_refl. Qed.
Lemma D_4fd14 : decode_any W_4fd14 = Some (Jal 1 200088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd18 : bv 32 := 0x00050593.
Lemma F_4fd18 : fetch_word AsanUbsan.M.loaded_segments (0x4fd18 : word) = Some W_4fd18.
Proof. vm_refl. Qed.
Lemma D_4fd18 : decode_any W_4fd18 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd1c : bv 32 := 0x00086517.
Lemma F_4fd1c : fetch_word AsanUbsan.M.loaded_segments (0x4fd1c : word) = Some W_4fd1c.
Proof. vm_refl. Qed.
Lemma D_4fd1c : decode_any W_4fd1c = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd20 : bv 32 := 0x79c53503.
Lemma F_4fd20 : fetch_word AsanUbsan.M.loaded_segments (0x4fd20 : word) = Some W_4fd20.
Proof. vm_refl. Qed.
Lemma D_4fd20 : decode_any W_4fd20 = Some (Load SZ8 true 10 10 1948, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd24 : bv 32 := 0x02154703.
Lemma F_4fd24 : fetch_word AsanUbsan.M.loaded_segments (0x4fd24 : word) = Some W_4fd24.
Proof. vm_refl. Qed.
Lemma D_4fd24 : decode_any W_4fd24 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd28 : bv 32 := 0x0089b4a3.
Lemma F_4fd28 : fetch_word AsanUbsan.M.loaded_segments (0x4fd28 : word) = Some W_4fd28.
Proof. vm_refl. Qed.
Lemma D_4fd28 : decode_any W_4fd28 = Some (Store SZ8 19 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd2c : bv 32 := 0x80040513.
Lemma F_4fd2c : fetch_word AsanUbsan.M.loaded_segments (0x4fd2c : word) = Some W_4fd2c.
Proof. vm_refl. Qed.
Lemma D_4fd2c : decode_any W_4fd2c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd30 : bv 32 := 0xfb850513.
Lemma F_4fd30 : fetch_word AsanUbsan.M.loaded_segments (0x4fd30 : word) = Some W_4fd30.
Proof. vm_refl. Qed.
Lemma D_4fd30 : decode_any W_4fd30 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd34 : bv 32 := 0x0ff00793.
Lemma F_4fd34 : fetch_word AsanUbsan.M.loaded_segments (0x4fd34 : word) = Some W_4fd34.
Proof. vm_refl. Qed.
Lemma D_4fd34 : decode_any W_4fd34 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd38 : bv 32 := 0x00040613.
Lemma F_4fd38 : fetch_word AsanUbsan.M.loaded_segments (0x4fd38 : word) = Some W_4fd38.
Proof. vm_refl. Qed.
Lemma D_4fd38 : decode_any W_4fd38 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd3c : bv 32 := 0x00000693.
Lemma F_4fd3c : fetch_word AsanUbsan.M.loaded_segments (0x4fd3c : word) = Some W_4fd3c.
Proof. vm_refl. Qed.
Lemma D_4fd3c : decode_any W_4fd3c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd40 : bv 32 := 0x2bc180ef.
Lemma F_4fd40 : fetch_word AsanUbsan.M.loaded_segments (0x4fd40 : word) = Some W_4fd40.
Proof. vm_refl. Qed.
Lemma D_4fd40 : decode_any W_4fd40 = Some (Jal 1 99004, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd44 : bv 32 := 0x80040513.
Lemma F_4fd44 : fetch_word AsanUbsan.M.loaded_segments (0x4fd44 : word) = Some W_4fd44.
Proof. vm_refl. Qed.
Lemma D_4fd44 : decode_any W_4fd44 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd48 : bv 32 := 0xfb850513.
Lemma F_4fd48 : fetch_word AsanUbsan.M.loaded_segments (0x4fd48 : word) = Some W_4fd48.
Proof. vm_refl. Qed.
Lemma D_4fd48 : decode_any W_4fd48 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd4c : bv 32 := 0x5cc190ef.
Lemma F_4fd4c : fetch_word AsanUbsan.M.loaded_segments (0x4fd4c : word) = Some W_4fd4c.
Proof. vm_refl. Qed.
Lemma D_4fd4c : decode_any W_4fd4c = Some (Jal 1 103884, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd50 : bv 32 := 0x00050593.
Lemma F_4fd50 : fetch_word AsanUbsan.M.loaded_segments (0x4fd50 : word) = Some W_4fd50.
Proof. vm_refl. Qed.
Lemma D_4fd50 : decode_any W_4fd50 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd54 : bv 32 := 0x00040993.
Lemma F_4fd54 : fetch_word AsanUbsan.M.loaded_segments (0x4fd54 : word) = Some W_4fd54.
Proof. vm_refl. Qed.
Lemma D_4fd54 : decode_any W_4fd54 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd58 : bv 32 := 0x00090513.
Lemma F_4fd58 : fetch_word AsanUbsan.M.loaded_segments (0x4fd58 : word) = Some W_4fd58.
Proof. vm_refl. Qed.
Lemma D_4fd58 : decode_any W_4fd58 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd5c : bv 32 := 0xec0590e3.
Lemma F_4fd5c : fetch_word AsanUbsan.M.loaded_segments (0x4fd5c : word) = Some W_4fd5c.
Proof. vm_refl. Qed.
Lemma D_4fd5c : decode_any W_4fd5c = Some (Branch BC_NE 11 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd60 : bv 32 := 0x0400006f.
Lemma F_4fd60 : fetch_word AsanUbsan.M.loaded_segments (0x4fd60 : word) = Some W_4fd60.
Proof. vm_refl. Qed.
Lemma D_4fd60 : decode_any W_4fd60 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd64 : bv 32 := 0x00060703.
Lemma F_4fd64 : fetch_word AsanUbsan.M.loaded_segments (0x4fd64 : word) = Some W_4fd64.
Proof. vm_refl. Qed.
Lemma D_4fd64 : decode_any W_4fd64 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd68 : bv 32 := 0x0076f693.
Lemma F_4fd68 : fetch_word AsanUbsan.M.loaded_segments (0x4fd68 : word) = Some W_4fd68.
Proof. vm_refl. Qed.
Lemma D_4fd68 : decode_any W_4fd68 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd6c : bv 32 := 0x00e037b3.
Lemma F_4fd6c : fetch_word AsanUbsan.M.loaded_segments (0x4fd6c : word) = Some W_4fd6c.
Proof. vm_refl. Qed.
Lemma D_4fd6c : decode_any W_4fd6c = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd70 : bv 32 := 0x00e6a6b3.
Lemma F_4fd70 : fetch_word AsanUbsan.M.loaded_segments (0x4fd70 : word) = Some W_4fd70.
Proof. vm_refl. Qed.
Lemma D_4fd70 : decode_any W_4fd70 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd74 : bv 32 := 0x0016c693.
Lemma F_4fd74 : fetch_word AsanUbsan.M.loaded_segments (0x4fd74 : word) = Some W_4fd74.
Proof. vm_refl. Qed.
Lemma D_4fd74 : decode_any W_4fd74 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd78 : bv 32 := 0x00d7f6b3.
Lemma F_4fd78 : fetch_word AsanUbsan.M.loaded_segments (0x4fd78 : word) = Some W_4fd78.
Proof. vm_refl. Qed.
Lemma D_4fd78 : decode_any W_4fd78 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd7c : bv 32 := 0x00c5fa63.
Lemma F_4fd7c : fetch_word AsanUbsan.M.loaded_segments (0x4fd7c : word) = Some W_4fd7c.
Proof. vm_refl. Qed.
Lemma D_4fd7c : decode_any W_4fd7c = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd80 : bv 32 := 0x0005c703.
Lemma F_4fd80 : fetch_word AsanUbsan.M.loaded_segments (0x4fd80 : word) = Some W_4fd80.
Proof. vm_refl. Qed.
Lemma D_4fd80 : decode_any W_4fd80 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd84 : bv 32 := 0x00158593.
Lemma F_4fd84 : fetch_word AsanUbsan.M.loaded_segments (0x4fd84 : word) = Some W_4fd84.
Proof. vm_refl. Qed.
Lemma D_4fd84 : decode_any W_4fd84 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd88 : bv 32 := 0x00d766b3.
Lemma F_4fd88 : fetch_word AsanUbsan.M.loaded_segments (0x4fd88 : word) = Some W_4fd88.
Proof. vm_refl. Qed.
Lemma D_4fd88 : decode_any W_4fd88 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd8c : bv 32 := 0xfec59ae3.
Lemma F_4fd8c : fetch_word AsanUbsan.M.loaded_segments (0x4fd8c : word) = Some W_4fd8c.
Proof. vm_refl. Qed.
Lemma D_4fd8c : decode_any W_4fd8c = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd90 : bv 32 := 0x0ff6f593.
Lemma F_4fd90 : fetch_word AsanUbsan.M.loaded_segments (0x4fd90 : word) = Some W_4fd90.
Proof. vm_refl. Qed.
Lemma D_4fd90 : decode_any W_4fd90 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd94 : bv 32 := 0xe80584e3.
Lemma F_4fd94 : fetch_word AsanUbsan.M.loaded_segments (0x4fd94 : word) = Some W_4fd94.
Proof. vm_refl. Qed.
Lemma D_4fd94 : decode_any W_4fd94 = Some (Branch BC_EQ 11 0 7816, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd98 : bv 32 := 0xf21ff06f.
Lemma F_4fd98 : fetch_word AsanUbsan.M.loaded_segments (0x4fd98 : word) = Some W_4fd98.
Proof. vm_refl. Qed.
Lemma D_4fd98 : decode_any W_4fd98 = Some (Jal 0 2096928, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fd9c : bv 32 := 0x00040993.
Lemma F_4fd9c : fetch_word AsanUbsan.M.loaded_segments (0x4fd9c : word) = Some W_4fd9c.
Proof. vm_refl. Qed.
Lemma D_4fd9c : decode_any W_4fd9c = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fda0 : bv 32 := 0x50d300ef.
Lemma F_4fda0 : fetch_word AsanUbsan.M.loaded_segments (0x4fda0 : word) = Some W_4fda0.
Proof. vm_refl. Qed.
Lemma D_4fda0 : decode_any W_4fda0 = Some (Jal 1 199948, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fda4 : bv 32 := 0xfffc0597.
Lemma F_4fda4 : fetch_word AsanUbsan.M.loaded_segments (0x4fda4 : word) = Some W_4fda4.
Proof. vm_refl. Qed.
Lemma D_4fda4 : decode_any W_4fda4 = Some (Auipc 11 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fda8 : bv 32 := 0x6645b583.
Lemma F_4fda8 : fetch_word AsanUbsan.M.loaded_segments (0x4fda8 : word) = Some W_4fda8.
Proof. vm_refl. Qed.
Lemma D_4fda8 : decode_any W_4fda8 = Some (Load SZ8 true 11 11 1636, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdac : bv 32 := 0x00ba3023.
Lemma F_4fdac : fetch_word AsanUbsan.M.loaded_segments (0x4fdac : word) = Some W_4fdac.
Proof. vm_refl. Qed.
Lemma D_4fdac : decode_any W_4fdac = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdb0 : bv 32 := 0x80040613.
Lemma F_4fdb0 : fetch_word AsanUbsan.M.loaded_segments (0x4fdb0 : word) = Some W_4fdb0.
Proof. vm_refl. Qed.
Lemma D_4fdb0 : decode_any W_4fdb0 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdb4 : bv 32 := 0xfb860613.
Lemma F_4fdb4 : fetch_word AsanUbsan.M.loaded_segments (0x4fdb4 : word) = Some W_4fdb4.
Proof. vm_refl. Qed.
Lemma D_4fdb4 : decode_any W_4fdb4 = Some (OpImm ALU_ADD 12 12 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdb8 : bv 32 := 0x00100713.
Lemma F_4fdb8 : fetch_word AsanUbsan.M.loaded_segments (0x4fdb8 : word) = Some W_4fdb8.
Proof. vm_refl. Qed.
Lemma D_4fdb8 : decode_any W_4fdb8 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdbc : bv 32 := 0x00098593.
Lemma F_4fdbc : fetch_word AsanUbsan.M.loaded_segments (0x4fdbc : word) = Some W_4fdbc.
Proof. vm_refl. Qed.
Lemma D_4fdbc : decode_any W_4fdbc = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdc0 : bv 32 := 0x00048693.
Lemma F_4fdc0 : fetch_word AsanUbsan.M.loaded_segments (0x4fdc0 : word) = Some W_4fdc0.
Proof. vm_refl. Qed.
Lemma D_4fdc0 : decode_any W_4fdc0 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdc4 : bv 32 := 0x00090793.
Lemma F_4fdc4 : fetch_word AsanUbsan.M.loaded_segments (0x4fdc4 : word) = Some W_4fdc4.
Proof. vm_refl. Qed.
Lemma D_4fdc4 : decode_any W_4fdc4 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdc8 : bv 32 := 0x00000813.
Lemma F_4fdc8 : fetch_word AsanUbsan.M.loaded_segments (0x4fdc8 : word) = Some W_4fdc8.
Proof. vm_refl. Qed.
Lemma D_4fdc8 : decode_any W_4fdc8 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdcc : bv 32 := 0x00000893.
Lemma F_4fdcc : fetch_word AsanUbsan.M.loaded_segments (0x4fdcc : word) = Some W_4fdcc.
Proof. vm_refl. Qed.
Lemma D_4fdcc : decode_any W_4fdcc = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdd0 : bv 32 := 0x53c150ef.
Lemma F_4fdd0 : fetch_word AsanUbsan.M.loaded_segments (0x4fdd0 : word) = Some W_4fdd0.
Proof. vm_refl. Qed.
Lemma D_4fdd0 : decode_any W_4fdd0 = Some (Jal 1 87356, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdd4 : bv 32 := 0x00090513.
Lemma F_4fdd4 : fetch_word AsanUbsan.M.loaded_segments (0x4fdd4 : word) = Some W_4fdd4.
Proof. vm_refl. Qed.
Lemma D_4fdd4 : decode_any W_4fdd4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4fdd8 : bv 32 := 0xe45ff06f.
Lemma F_4fdd8 : fetch_word AsanUbsan.M.loaded_segments (0x4fdd8 : word) = Some W_4fdd8.
Proof. vm_refl. Qed.
Lemma D_4fdd8 : decode_any W_4fdd8 = Some (Jal 0 2096708, 4%Z).
Proof. vm_refl. Qed.
