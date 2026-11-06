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

Definition W_8bd18 : bv 32 := 0x02060063.
Lemma F_8bd18 : fetch_word Asan.M.loaded_segments (0x8bd68 : word) = Some W_8bd18.
Proof. vm_refl. Qed.
Lemma D_8bd18 : decode_any W_8bd18 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd1c : bv 32 := 0x00c50633.
Lemma F_8bd1c : fetch_word Asan.M.loaded_segments (0x8bd6c : word) = Some W_8bd1c.
Proof. vm_refl. Qed.
Lemma D_8bd1c : decode_any W_8bd1c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd20 : bv 32 := 0x00050693.
Lemma F_8bd20 : fetch_word Asan.M.loaded_segments (0x8bd70 : word) = Some W_8bd20.
Proof. vm_refl. Qed.
Lemma D_8bd20 : decode_any W_8bd20 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd24 : bv 32 := 0x0005c703.
Lemma F_8bd24 : fetch_word Asan.M.loaded_segments (0x8bd74 : word) = Some W_8bd24.
Proof. vm_refl. Qed.
Lemma D_8bd24 : decode_any W_8bd24 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd28 : bv 32 := 0x00e68023.
Lemma F_8bd28 : fetch_word Asan.M.loaded_segments (0x8bd78 : word) = Some W_8bd28.
Proof. vm_refl. Qed.
Lemma D_8bd28 : decode_any W_8bd28 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd2c : bv 32 := 0x00168693.
Lemma F_8bd2c : fetch_word Asan.M.loaded_segments (0x8bd7c : word) = Some W_8bd2c.
Proof. vm_refl. Qed.
Lemma D_8bd2c : decode_any W_8bd2c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd30 : bv 32 := 0x00158593.
Lemma F_8bd30 : fetch_word Asan.M.loaded_segments (0x8bd80 : word) = Some W_8bd30.
Proof. vm_refl. Qed.
Lemma D_8bd30 : decode_any W_8bd30 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd34 : bv 32 := 0xfec698e3.
Lemma F_8bd34 : fetch_word Asan.M.loaded_segments (0x8bd84 : word) = Some W_8bd34.
Proof. vm_refl. Qed.
Lemma D_8bd34 : decode_any W_8bd34 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd38 : bv 32 := 0x00008067.
Lemma F_8bd38 : fetch_word Asan.M.loaded_segments (0x8bd88 : word) = Some W_8bd38.
Proof. vm_refl. Qed.
Lemma D_8bd38 : decode_any W_8bd38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd3c : bv 32 := 0x02b57463.
Lemma F_8bd3c : fetch_word Asan.M.loaded_segments (0x8bd8c : word) = Some W_8bd3c.
Proof. vm_refl. Qed.
Lemma D_8bd3c : decode_any W_8bd3c = Some (Branch BC_GEU 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd40 : bv 32 := 0x04c05863.
Lemma F_8bd40 : fetch_word Asan.M.loaded_segments (0x8bd90 : word) = Some W_8bd40.
Proof. vm_refl. Qed.
Lemma D_8bd40 : decode_any W_8bd40 = Some (Branch BC_GE 0 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd44 : bv 32 := 0x00c50633.
Lemma F_8bd44 : fetch_word Asan.M.loaded_segments (0x8bd94 : word) = Some W_8bd44.
Proof. vm_refl. Qed.
Lemma D_8bd44 : decode_any W_8bd44 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd48 : bv 32 := 0x00050693.
Lemma F_8bd48 : fetch_word Asan.M.loaded_segments (0x8bd98 : word) = Some W_8bd48.
Proof. vm_refl. Qed.
Lemma D_8bd48 : decode_any W_8bd48 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd4c : bv 32 := 0x0005c703.
Lemma F_8bd4c : fetch_word Asan.M.loaded_segments (0x8bd9c : word) = Some W_8bd4c.
Proof. vm_refl. Qed.
Lemma D_8bd4c : decode_any W_8bd4c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd50 : bv 32 := 0x00e68023.
Lemma F_8bd50 : fetch_word Asan.M.loaded_segments (0x8bda0 : word) = Some W_8bd50.
Proof. vm_refl. Qed.
Lemma D_8bd50 : decode_any W_8bd50 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd54 : bv 32 := 0x00168693.
Lemma F_8bd54 : fetch_word Asan.M.loaded_segments (0x8bda4 : word) = Some W_8bd54.
Proof. vm_refl. Qed.
Lemma D_8bd54 : decode_any W_8bd54 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd58 : bv 32 := 0x00158593.
Lemma F_8bd58 : fetch_word Asan.M.loaded_segments (0x8bda8 : word) = Some W_8bd58.
Proof. vm_refl. Qed.
Lemma D_8bd58 : decode_any W_8bd58 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd5c : bv 32 := 0xfec698e3.
Lemma F_8bd5c : fetch_word Asan.M.loaded_segments (0x8bdac : word) = Some W_8bd5c.
Proof. vm_refl. Qed.
Lemma D_8bd5c : decode_any W_8bd5c = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd60 : bv 32 := 0x0300006f.
Lemma F_8bd60 : fetch_word Asan.M.loaded_segments (0x8bdb0 : word) = Some W_8bd60.
Proof. vm_refl. Qed.
Lemma D_8bd60 : decode_any W_8bd60 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd64 : bv 32 := 0x02a5f663.
Lemma F_8bd64 : fetch_word Asan.M.loaded_segments (0x8bdb4 : word) = Some W_8bd64.
Proof. vm_refl. Qed.
Lemma D_8bd64 : decode_any W_8bd64 = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd68 : bv 32 := 0x02c05463.
Lemma F_8bd68 : fetch_word Asan.M.loaded_segments (0x8bdb8 : word) = Some W_8bd68.
Proof. vm_refl. Qed.
Lemma D_8bd68 : decode_any W_8bd68 = Some (Branch BC_GE 0 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd6c : bv 32 := 0xfff60693.
Lemma F_8bd6c : fetch_word Asan.M.loaded_segments (0x8bdbc : word) = Some W_8bd6c.
Proof. vm_refl. Qed.
Lemma D_8bd6c : decode_any W_8bd6c = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd70 : bv 32 := 0x00100613.
Lemma F_8bd70 : fetch_word Asan.M.loaded_segments (0x8bdc0 : word) = Some W_8bd70.
Proof. vm_refl. Qed.
Lemma D_8bd70 : decode_any W_8bd70 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd74 : bv 32 := 0x00d58733.
Lemma F_8bd74 : fetch_word Asan.M.loaded_segments (0x8bdc4 : word) = Some W_8bd74.
Proof. vm_refl. Qed.
Lemma D_8bd74 : decode_any W_8bd74 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd78 : bv 32 := 0x00074703.
Lemma F_8bd78 : fetch_word Asan.M.loaded_segments (0x8bdc8 : word) = Some W_8bd78.
Proof. vm_refl. Qed.
Lemma D_8bd78 : decode_any W_8bd78 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd7c : bv 32 := 0x00d507b3.
Lemma F_8bd7c : fetch_word Asan.M.loaded_segments (0x8bdcc : word) = Some W_8bd7c.
Proof. vm_refl. Qed.
Lemma D_8bd7c : decode_any W_8bd7c = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd80 : bv 32 := 0x00168813.
Lemma F_8bd80 : fetch_word Asan.M.loaded_segments (0x8bdd0 : word) = Some W_8bd80.
Proof. vm_refl. Qed.
Lemma D_8bd80 : decode_any W_8bd80 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd84 : bv 32 := 0xfff68693.
Lemma F_8bd84 : fetch_word Asan.M.loaded_segments (0x8bdd4 : word) = Some W_8bd84.
Proof. vm_refl. Qed.
Lemma D_8bd84 : decode_any W_8bd84 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd88 : bv 32 := 0x00e78023.
Lemma F_8bd88 : fetch_word Asan.M.loaded_segments (0x8bdd8 : word) = Some W_8bd88.
Proof. vm_refl. Qed.
Lemma D_8bd88 : decode_any W_8bd88 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd8c : bv 32 := 0xff0664e3.
Lemma F_8bd8c : fetch_word Asan.M.loaded_segments (0x8bddc : word) = Some W_8bd8c.
Proof. vm_refl. Qed.
Lemma D_8bd8c : decode_any W_8bd8c = Some (Branch BC_LTU 12 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd90 : bv 32 := 0x00008067.
Lemma F_8bd90 : fetch_word Asan.M.loaded_segments (0x8bde0 : word) = Some W_8bd90.
Proof. vm_refl. Qed.
Lemma D_8bd90 : decode_any W_8bd90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd94 : bv 32 := 0x00a666b3.
Lemma F_8bd94 : fetch_word Asan.M.loaded_segments (0x8bde4 : word) = Some W_8bd94.
Proof. vm_refl. Qed.
Lemma D_8bd94 : decode_any W_8bd94 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd98 : bv 32 := 0x00f6f693.
Lemma F_8bd98 : fetch_word Asan.M.loaded_segments (0x8bde8 : word) = Some W_8bd98.
Proof. vm_refl. Qed.
Lemma D_8bd98 : decode_any W_8bd98 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bd9c : bv 32 := 0x02068063.
Lemma F_8bd9c : fetch_word Asan.M.loaded_segments (0x8bdec : word) = Some W_8bd9c.
Proof. vm_refl. Qed.
Lemma D_8bd9c : decode_any W_8bd9c = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bda0 : bv 32 := 0x04060863.
Lemma F_8bda0 : fetch_word Asan.M.loaded_segments (0x8bdf0 : word) = Some W_8bda0.
Proof. vm_refl. Qed.
Lemma D_8bda0 : decode_any W_8bda0 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bda4 : bv 32 := 0x00c50633.
Lemma F_8bda4 : fetch_word Asan.M.loaded_segments (0x8bdf4 : word) = Some W_8bda4.
Proof. vm_refl. Qed.
Lemma D_8bda4 : decode_any W_8bda4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bda8 : bv 32 := 0x00050693.
Lemma F_8bda8 : fetch_word Asan.M.loaded_segments (0x8bdf8 : word) = Some W_8bda8.
Proof. vm_refl. Qed.
Lemma D_8bda8 : decode_any W_8bda8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdac : bv 32 := 0x00b68023.
Lemma F_8bdac : fetch_word Asan.M.loaded_segments (0x8bdfc : word) = Some W_8bdac.
Proof. vm_refl. Qed.
Lemma D_8bdac : decode_any W_8bdac = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdb0 : bv 32 := 0x00168693.
Lemma F_8bdb0 : fetch_word Asan.M.loaded_segments (0x8be00 : word) = Some W_8bdb0.
Proof. vm_refl. Qed.
Lemma D_8bdb0 : decode_any W_8bdb0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdb4 : bv 32 := 0xfec69ce3.
Lemma F_8bdb4 : fetch_word Asan.M.loaded_segments (0x8be04 : word) = Some W_8bdb4.
Proof. vm_refl. Qed.
Lemma D_8bdb4 : decode_any W_8bdb4 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdb8 : bv 32 := 0x0380006f.
Lemma F_8bdb8 : fetch_word Asan.M.loaded_segments (0x8be08 : word) = Some W_8bdb8.
Proof. vm_refl. Qed.
Lemma D_8bdb8 : decode_any W_8bdb8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdbc : bv 32 := 0x02060a63.
Lemma F_8bdbc : fetch_word Asan.M.loaded_segments (0x8be0c : word) = Some W_8bdbc.
Proof. vm_refl. Qed.
Lemma D_8bdbc : decode_any W_8bdbc = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdc0 : bv 32 := 0x00c50633.
Lemma F_8bdc0 : fetch_word Asan.M.loaded_segments (0x8be10 : word) = Some W_8bdc0.
Proof. vm_refl. Qed.
Lemma D_8bdc0 : decode_any W_8bdc0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdc4 : bv 32 := 0x00859693.
Lemma F_8bdc4 : fetch_word Asan.M.loaded_segments (0x8be14 : word) = Some W_8bdc4.
Proof. vm_refl. Qed.
Lemma D_8bdc4 : decode_any W_8bdc4 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdc8 : bv 32 := 0x00b6e5b3.
Lemma F_8bdc8 : fetch_word Asan.M.loaded_segments (0x8be18 : word) = Some W_8bdc8.
Proof. vm_refl. Qed.
Lemma D_8bdc8 : decode_any W_8bdc8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdcc : bv 32 := 0x01059693.
Lemma F_8bdcc : fetch_word Asan.M.loaded_segments (0x8be1c : word) = Some W_8bdcc.
Proof. vm_refl. Qed.
Lemma D_8bdcc : decode_any W_8bdcc = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdd0 : bv 32 := 0x00b6e5b3.
Lemma F_8bdd0 : fetch_word Asan.M.loaded_segments (0x8be20 : word) = Some W_8bdd0.
Proof. vm_refl. Qed.
Lemma D_8bdd0 : decode_any W_8bdd0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdd4 : bv 32 := 0x02059693.
Lemma F_8bdd4 : fetch_word Asan.M.loaded_segments (0x8be24 : word) = Some W_8bdd4.
Proof. vm_refl. Qed.
Lemma D_8bdd4 : decode_any W_8bdd4 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdd8 : bv 32 := 0x00b6e5b3.
Lemma F_8bdd8 : fetch_word Asan.M.loaded_segments (0x8be28 : word) = Some W_8bdd8.
Proof. vm_refl. Qed.
Lemma D_8bdd8 : decode_any W_8bdd8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bddc : bv 32 := 0x00050693.
Lemma F_8bddc : fetch_word Asan.M.loaded_segments (0x8be2c : word) = Some W_8bddc.
Proof. vm_refl. Qed.
Lemma D_8bddc : decode_any W_8bddc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bde0 : bv 32 := 0x00b6b023.
Lemma F_8bde0 : fetch_word Asan.M.loaded_segments (0x8be30 : word) = Some W_8bde0.
Proof. vm_refl. Qed.
Lemma D_8bde0 : decode_any W_8bde0 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bde4 : bv 32 := 0x00b6b423.
Lemma F_8bde4 : fetch_word Asan.M.loaded_segments (0x8be34 : word) = Some W_8bde4.
Proof. vm_refl. Qed.
Lemma D_8bde4 : decode_any W_8bde4 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bde8 : bv 32 := 0x01068693.
Lemma F_8bde8 : fetch_word Asan.M.loaded_segments (0x8be38 : word) = Some W_8bde8.
Proof. vm_refl. Qed.
Lemma D_8bde8 : decode_any W_8bde8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdec : bv 32 := 0xfec6eae3.
Lemma F_8bdec : fetch_word Asan.M.loaded_segments (0x8be3c : word) = Some W_8bdec.
Proof. vm_refl. Qed.
Lemma D_8bdec : decode_any W_8bdec = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bdf0 : bv 32 := 0x00008067.
Lemma F_8bdf0 : fetch_word Asan.M.loaded_segments (0x8be40 : word) = Some W_8bdf0.
Proof. vm_refl. Qed.
Lemma D_8bdf0 : decode_any W_8bdf0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
