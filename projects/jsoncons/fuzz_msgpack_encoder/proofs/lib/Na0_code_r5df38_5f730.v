(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7eb60 : bv 32 := 0x2590006f.
Lemma F_7eb60 : fetch_word Asan.M.loaded_segments (0x7ebb0 : word) = Some W_7eb60.
Proof. vm_refl. Qed.
Lemma D_7eb60 : decode_any W_7eb60 = Some (Jal 0 2648, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb64 : bv 32 := 0x5450006f.
Lemma F_7eb64 : fetch_word Asan.M.loaded_segments (0x7ebb4 : word) = Some W_7eb64.
Proof. vm_refl. Qed.
Lemma D_7eb64 : decode_any W_7eb64 = Some (Jal 0 3396, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb68 : bv 32 := 0x2000106f.
Lemma F_7eb68 : fetch_word Asan.M.loaded_segments (0x7ebb8 : word) = Some W_7eb68.
Proof. vm_refl. Qed.
Lemma D_7eb68 : decode_any W_7eb68 = Some (Jal 0 4608, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb6c : bv 32 := 0x81010113.
Lemma F_7eb6c : fetch_word Asan.M.loaded_segments (0x7ebbc : word) = Some W_7eb6c.
Proof. vm_refl. Qed.
Lemma D_7eb6c : decode_any W_7eb6c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb70 : bv 32 := 0x7e113423.
Lemma F_7eb70 : fetch_word Asan.M.loaded_segments (0x7ebc0 : word) = Some W_7eb70.
Proof. vm_refl. Qed.
Lemma D_7eb70 : decode_any W_7eb70 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb74 : bv 32 := 0x7e813023.
Lemma F_7eb74 : fetch_word Asan.M.loaded_segments (0x7ebc4 : word) = Some W_7eb74.
Proof. vm_refl. Qed.
Lemma D_7eb74 : decode_any W_7eb74 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb78 : bv 32 := 0x7c913c23.
Lemma F_7eb78 : fetch_word Asan.M.loaded_segments (0x7ebc8 : word) = Some W_7eb78.
Proof. vm_refl. Qed.
Lemma D_7eb78 : decode_any W_7eb78 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb7c : bv 32 := 0x7d213823.
Lemma F_7eb7c : fetch_word Asan.M.loaded_segments (0x7ebcc : word) = Some W_7eb7c.
Proof. vm_refl. Qed.
Lemma D_7eb7c : decode_any W_7eb7c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb80 : bv 32 := 0x7d313423.
Lemma F_7eb80 : fetch_word Asan.M.loaded_segments (0x7ebd0 : word) = Some W_7eb80.
Proof. vm_refl. Qed.
Lemma D_7eb80 : decode_any W_7eb80 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb84 : bv 32 := 0x7d413023.
Lemma F_7eb84 : fetch_word Asan.M.loaded_segments (0x7ebd4 : word) = Some W_7eb84.
Proof. vm_refl. Qed.
Lemma D_7eb84 : decode_any W_7eb84 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb88 : bv 32 := 0x7b513c23.
Lemma F_7eb88 : fetch_word Asan.M.loaded_segments (0x7ebd8 : word) = Some W_7eb88.
Proof. vm_refl. Qed.
Lemma D_7eb88 : decode_any W_7eb88 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb8c : bv 32 := 0x7b613823.
Lemma F_7eb8c : fetch_word Asan.M.loaded_segments (0x7ebdc : word) = Some W_7eb8c.
Proof. vm_refl. Qed.
Lemma D_7eb8c : decode_any W_7eb8c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb90 : bv 32 := 0x7b713423.
Lemma F_7eb90 : fetch_word Asan.M.loaded_segments (0x7ebe0 : word) = Some W_7eb90.
Proof. vm_refl. Qed.
Lemma D_7eb90 : decode_any W_7eb90 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb94 : bv 32 := 0x7f010413.
Lemma F_7eb94 : fetch_word Asan.M.loaded_segments (0x7ebe4 : word) = Some W_7eb94.
Proof. vm_refl. Qed.
Lemma D_7eb94 : decode_any W_7eb94 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb98 : bv 32 := 0xf9010113.
Lemma F_7eb98 : fetch_word Asan.M.loaded_segments (0x7ebe8 : word) = Some W_7eb98.
Proof. vm_refl. Qed.
Lemma D_7eb98 : decode_any W_7eb98 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eb9c : bv 32 := 0x000d9697.
Lemma F_7eb9c : fetch_word Asan.M.loaded_segments (0x7ebec : word) = Some W_7eb9c.
Proof. vm_refl. Qed.
Lemma D_7eb9c : decode_any W_7eb9c = Some (Auipc 13 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eba0 : bv 32 := 0xd146b683.
Lemma F_7eba0 : fetch_word Asan.M.loaded_segments (0x7ebf0 : word) = Some W_7eba0.
Proof. vm_refl. Qed.
Lemma D_7eba0 : decode_any W_7eba0 = Some (Load SZ8 true 13 13 3348, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eba4 : bv 32 := 0x0006c683.
Lemma F_7eba4 : fetch_word Asan.M.loaded_segments (0x7ebf4 : word) = Some W_7eba4.
Proof. vm_refl. Qed.
Lemma D_7eba4 : decode_any W_7eba4 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eba8 : bv 32 := 0x0e068863.
Lemma F_7eba8 : fetch_word Asan.M.loaded_segments (0x7ebf8 : word) = Some W_7eba8.
Proof. vm_refl. Qed.
Lemma D_7eba8 : decode_any W_7eba8 = Some (Branch BC_EQ 13 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebac : bv 32 := 0x80040a13.
Lemma F_7ebac : fetch_word Asan.M.loaded_segments (0x7ebfc : word) = Some W_7ebac.
Proof. vm_refl. Qed.
Lemma D_7ebac : decode_any W_7ebac = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebb0 : bv 32 := 0xfa0a0a13.
Lemma F_7ebb0 : fetch_word Asan.M.loaded_segments (0x7ec00 : word) = Some W_7ebb0.
Proof. vm_refl. Qed.
Lemma D_7ebb0 : decode_any W_7ebb0 = Some (OpImm ALU_ADD 20 20 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebb4 : bv 32 := 0x00c58ab3.
Lemma F_7ebb4 : fetch_word Asan.M.loaded_segments (0x7ec04 : word) = Some W_7ebb4.
Proof. vm_refl. Qed.
Lemma D_7ebb4 : decode_any W_7ebb4 = Some (Op ALU_ADD 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebb8 : bv 32 := 0x00c509b3.
Lemma F_7ebb8 : fetch_word Asan.M.loaded_segments (0x7ec08 : word) = Some W_7ebb8.
Proof. vm_refl. Qed.
Lemma D_7ebb8 : decode_any W_7ebb8 = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebbc : bv 32 := 0x00b50663.
Lemma F_7ebbc : fetch_word Asan.M.loaded_segments (0x7ec0c : word) = Some W_7ebbc.
Proof. vm_refl. Qed.
Lemma D_7ebbc : decode_any W_7ebbc = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebc0 : bv 32 := 0x0135f463.
Lemma F_7ebc0 : fetch_word Asan.M.loaded_segments (0x7ec10 : word) = Some W_7ebc0.
Proof. vm_refl. Qed.
Lemma D_7ebc0 : decode_any W_7ebc0 = Some (Branch BC_GEU 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebc4 : bv 32 := 0x1b556a63.
Lemma F_7ebc4 : fetch_word Asan.M.loaded_segments (0x7ec14 : word) = Some W_7ebc4.
Proof. vm_refl. Qed.
Lemma D_7ebc4 : decode_any W_7ebc4 = Some (Branch BC_LTU 10 21 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebc8 : bv 32 := 0xfff5c693.
Lemma F_7ebc8 : fetch_word Asan.M.loaded_segments (0x7ec18 : word) = Some W_7ebc8.
Proof. vm_refl. Qed.
Lemma D_7ebc8 : decode_any W_7ebc8 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebcc : bv 32 := 0x26c6e463.
Lemma F_7ebcc : fetch_word Asan.M.loaded_segments (0x7ec1c : word) = Some W_7ebcc.
Proof. vm_refl. Qed.
Lemma D_7ebcc : decode_any W_7ebcc = Some (Branch BC_LTU 13 12 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebd0 : bv 32 := 0xfbf60b13.
Lemma F_7ebd0 : fetch_word Asan.M.loaded_segments (0x7ec20 : word) = Some W_7ebd0.
Proof. vm_refl. Qed.
Lemma D_7ebd0 : decode_any W_7ebd0 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebd4 : bv 32 := 0xfbf00693.
Lemma F_7ebd4 : fetch_word Asan.M.loaded_segments (0x7ec24 : word) = Some W_7ebd4.
Proof. vm_refl. Qed.
Lemma D_7ebd4 : decode_any W_7ebd4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebd8 : bv 32 := 0x2f66f263.
Lemma F_7ebd8 : fetch_word Asan.M.loaded_segments (0x7ec28 : word) = Some W_7ebd8.
Proof. vm_refl. Qed.
Lemma D_7ebd8 : decode_any W_7ebd8 = Some (Branch BC_GEU 13 22 740, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebdc : bv 32 := 0x000d8697.
Lemma F_7ebdc : fetch_word Asan.M.loaded_segments (0x7ec2c : word) = Some W_7ebdc.
Proof. vm_refl. Qed.
Lemma D_7ebdc : decode_any W_7ebdc = Some (Auipc 13 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebe0 : bv 32 := 0x16c6b683.
Lemma F_7ebe0 : fetch_word Asan.M.loaded_segments (0x7ec30 : word) = Some W_7ebe0.
Proof. vm_refl. Qed.
Lemma D_7ebe0 : decode_any W_7ebe0 = Some (Load SZ8 true 13 13 364, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebe4 : bv 32 := 0x0006b703.
Lemma F_7ebe4 : fetch_word Asan.M.loaded_segments (0x7ec34 : word) = Some W_7ebe4.
Proof. vm_refl. Qed.
Lemma D_7ebe4 : decode_any W_7ebe4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebe8 : bv 32 := 0xfffa8a93.
Lemma F_7ebe8 : fetch_word Asan.M.loaded_segments (0x7ec38 : word) = Some W_7ebe8.
Proof. vm_refl. Qed.
Lemma D_7ebe8 : decode_any W_7ebe8 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebec : bv 32 := 0x0035d693.
Lemma F_7ebec : fetch_word Asan.M.loaded_segments (0x7ec3c : word) = Some W_7ebec.
Proof. vm_refl. Qed.
Lemma D_7ebec : decode_any W_7ebec = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebf0 : bv 32 := 0x003ad793.
Lemma F_7ebf0 : fetch_word Asan.M.loaded_segments (0x7ec40 : word) = Some W_7ebf0.
Proof. vm_refl. Qed.
Lemma D_7ebf0 : decode_any W_7ebf0 = Some (ShiftImm ALU_SRL 15 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebf4 : bv 32 := 0x00d706b3.
Lemma F_7ebf4 : fetch_word Asan.M.loaded_segments (0x7ec44 : word) = Some W_7ebf4.
Proof. vm_refl. Qed.
Lemma D_7ebf4 : decode_any W_7ebf4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebf8 : bv 32 := 0x00f70733.
Lemma F_7ebf8 : fetch_word Asan.M.loaded_segments (0x7ec48 : word) = Some W_7ebf8.
Proof. vm_refl. Qed.
Lemma D_7ebf8 : decode_any W_7ebf8 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ebfc : bv 32 := 0xff86f793.
Lemma F_7ebfc : fetch_word Asan.M.loaded_segments (0x7ec4c : word) = Some W_7ebfc.
Proof. vm_refl. Qed.
Lemma D_7ebfc : decode_any W_7ebfc = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec00 : bv 32 := 0xff877813.
Lemma F_7ec00 : fetch_word Asan.M.loaded_segments (0x7ec50 : word) = Some W_7ec00.
Proof. vm_refl. Qed.
Lemma D_7ec00 : decode_any W_7ec00 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec04 : bv 32 := 0x0007b783.
Lemma F_7ec04 : fetch_word Asan.M.loaded_segments (0x7ec54 : word) = Some W_7ec04.
Proof. vm_refl. Qed.
Lemma D_7ec04 : decode_any W_7ec04 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec08 : bv 32 := 0x00083803.
Lemma F_7ec08 : fetch_word Asan.M.loaded_segments (0x7ec58 : word) = Some W_7ec08.
Proof. vm_refl. Qed.
Lemma D_7ec08 : decode_any W_7ec08 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec0c : bv 32 := 0x00f867b3.
Lemma F_7ec0c : fetch_word Asan.M.loaded_segments (0x7ec5c : word) = Some W_7ec0c.
Proof. vm_refl. Qed.
Lemma D_7ec0c : decode_any W_7ec0c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec10 : bv 32 := 0x2a079a63.
Lemma F_7ec10 : fetch_word Asan.M.loaded_segments (0x7ec60 : word) = Some W_7ec10.
Proof. vm_refl. Qed.
Lemma D_7ec10 : decode_any W_7ec10 = Some (Branch BC_NE 15 0 692, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec14 : bv 32 := 0xfff54693.
Lemma F_7ec14 : fetch_word Asan.M.loaded_segments (0x7ec64 : word) = Some W_7ec14.
Proof. vm_refl. Qed.
Lemma D_7ec14 : decode_any W_7ec14 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec18 : bv 32 := 0x0cc6ea63.
Lemma F_7ec18 : fetch_word Asan.M.loaded_segments (0x7ec68 : word) = Some W_7ec18.
Proof. vm_refl. Qed.
Lemma D_7ec18 : decode_any W_7ec18 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec1c : bv 32 := 0xfbf00693.
Lemma F_7ec1c : fetch_word Asan.M.loaded_segments (0x7ec6c : word) = Some W_7ec1c.
Proof. vm_refl. Qed.
Lemma D_7ec1c : decode_any W_7ec1c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec20 : bv 32 := 0x1566f863.
Lemma F_7ec20 : fetch_word Asan.M.loaded_segments (0x7ec70 : word) = Some W_7ec20.
Proof. vm_refl. Qed.
Lemma D_7ec20 : decode_any W_7ec20 = Some (Branch BC_GEU 13 22 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec24 : bv 32 := 0x000d8697.
Lemma F_7ec24 : fetch_word Asan.M.loaded_segments (0x7ec74 : word) = Some W_7ec24.
Proof. vm_refl. Qed.
Lemma D_7ec24 : decode_any W_7ec24 = Some (Auipc 13 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec28 : bv 32 := 0x1246b683.
Lemma F_7ec28 : fetch_word Asan.M.loaded_segments (0x7ec78 : word) = Some W_7ec28.
Proof. vm_refl. Qed.
Lemma D_7ec28 : decode_any W_7ec28 = Some (Load SZ8 true 13 13 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec2c : bv 32 := 0x0006b703.
Lemma F_7ec2c : fetch_word Asan.M.loaded_segments (0x7ec7c : word) = Some W_7ec2c.
Proof. vm_refl. Qed.
Lemma D_7ec2c : decode_any W_7ec2c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec30 : bv 32 := 0xfff98993.
Lemma F_7ec30 : fetch_word Asan.M.loaded_segments (0x7ec80 : word) = Some W_7ec30.
Proof. vm_refl. Qed.
Lemma D_7ec30 : decode_any W_7ec30 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec34 : bv 32 := 0x00355693.
Lemma F_7ec34 : fetch_word Asan.M.loaded_segments (0x7ec84 : word) = Some W_7ec34.
Proof. vm_refl. Qed.
Lemma D_7ec34 : decode_any W_7ec34 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec38 : bv 32 := 0x0039d793.
Lemma F_7ec38 : fetch_word Asan.M.loaded_segments (0x7ec88 : word) = Some W_7ec38.
Proof. vm_refl. Qed.
Lemma D_7ec38 : decode_any W_7ec38 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec3c : bv 32 := 0x00d706b3.
Lemma F_7ec3c : fetch_word Asan.M.loaded_segments (0x7ec8c : word) = Some W_7ec3c.
Proof. vm_refl. Qed.
Lemma D_7ec3c : decode_any W_7ec3c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec40 : bv 32 := 0x00f70733.
Lemma F_7ec40 : fetch_word Asan.M.loaded_segments (0x7ec90 : word) = Some W_7ec40.
Proof. vm_refl. Qed.
Lemma D_7ec40 : decode_any W_7ec40 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec44 : bv 32 := 0xff86f793.
Lemma F_7ec44 : fetch_word Asan.M.loaded_segments (0x7ec94 : word) = Some W_7ec44.
Proof. vm_refl. Qed.
Lemma D_7ec44 : decode_any W_7ec44 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec48 : bv 32 := 0xff877813.
Lemma F_7ec48 : fetch_word Asan.M.loaded_segments (0x7ec98 : word) = Some W_7ec48.
Proof. vm_refl. Qed.
Lemma D_7ec48 : decode_any W_7ec48 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec4c : bv 32 := 0x0007b783.
Lemma F_7ec4c : fetch_word Asan.M.loaded_segments (0x7ec9c : word) = Some W_7ec4c.
Proof. vm_refl. Qed.
Lemma D_7ec4c : decode_any W_7ec4c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec50 : bv 32 := 0x00083803.
Lemma F_7ec50 : fetch_word Asan.M.loaded_segments (0x7eca0 : word) = Some W_7ec50.
Proof. vm_refl. Qed.
Lemma D_7ec50 : decode_any W_7ec50 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec54 : bv 32 := 0x00f867b3.
Lemma F_7ec54 : fetch_word Asan.M.loaded_segments (0x7eca4 : word) = Some W_7ec54.
Proof. vm_refl. Qed.
Lemma D_7ec54 : decode_any W_7ec54 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec58 : bv 32 := 0x30079863.
Lemma F_7ec58 : fetch_word Asan.M.loaded_segments (0x7eca8 : word) = Some W_7ec58.
Proof. vm_refl. Qed.
Lemma D_7ec58 : decode_any W_7ec58 = Some (Branch BC_NE 15 0 784, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec5c : bv 32 := 0x000da697.
Lemma F_7ec5c : fetch_word Asan.M.loaded_segments (0x7ecac : word) = Some W_7ec5c.
Proof. vm_refl. Qed.
Lemma D_7ec5c : decode_any W_7ec5c = Some (Auipc 13 218, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec60 : bv 32 := 0x0f46b683.
Lemma F_7ec60 : fetch_word Asan.M.loaded_segments (0x7ecb0 : word) = Some W_7ec60.
Proof. vm_refl. Qed.
Lemma D_7ec60 : decode_any W_7ec60 = Some (Load SZ8 true 13 13 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec64 : bv 32 := 0x000680e7.
Lemma F_7ec64 : fetch_word Asan.M.loaded_segments (0x7ecb4 : word) = Some W_7ec64.
Proof. vm_refl. Qed.
Lemma D_7ec64 : decode_any W_7ec64 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec68 : bv 32 := 0x07010113.
Lemma F_7ec68 : fetch_word Asan.M.loaded_segments (0x7ecb8 : word) = Some W_7ec68.
Proof. vm_refl. Qed.
Lemma D_7ec68 : decode_any W_7ec68 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec6c : bv 32 := 0x7e813083.
Lemma F_7ec6c : fetch_word Asan.M.loaded_segments (0x7ecbc : word) = Some W_7ec6c.
Proof. vm_refl. Qed.
Lemma D_7ec6c : decode_any W_7ec6c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec70 : bv 32 := 0x7e013403.
Lemma F_7ec70 : fetch_word Asan.M.loaded_segments (0x7ecc0 : word) = Some W_7ec70.
Proof. vm_refl. Qed.
Lemma D_7ec70 : decode_any W_7ec70 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec74 : bv 32 := 0x7d813483.
Lemma F_7ec74 : fetch_word Asan.M.loaded_segments (0x7ecc4 : word) = Some W_7ec74.
Proof. vm_refl. Qed.
Lemma D_7ec74 : decode_any W_7ec74 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec78 : bv 32 := 0x7d013903.
Lemma F_7ec78 : fetch_word Asan.M.loaded_segments (0x7ecc8 : word) = Some W_7ec78.
Proof. vm_refl. Qed.
Lemma D_7ec78 : decode_any W_7ec78 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec7c : bv 32 := 0x7c813983.
Lemma F_7ec7c : fetch_word Asan.M.loaded_segments (0x7eccc : word) = Some W_7ec7c.
Proof. vm_refl. Qed.
Lemma D_7ec7c : decode_any W_7ec7c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec80 : bv 32 := 0x7c013a03.
Lemma F_7ec80 : fetch_word Asan.M.loaded_segments (0x7ecd0 : word) = Some W_7ec80.
Proof. vm_refl. Qed.
Lemma D_7ec80 : decode_any W_7ec80 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec84 : bv 32 := 0x7b813a83.
Lemma F_7ec84 : fetch_word Asan.M.loaded_segments (0x7ecd4 : word) = Some W_7ec84.
Proof. vm_refl. Qed.
Lemma D_7ec84 : decode_any W_7ec84 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec88 : bv 32 := 0x7b013b03.
Lemma F_7ec88 : fetch_word Asan.M.loaded_segments (0x7ecd8 : word) = Some W_7ec88.
Proof. vm_refl. Qed.
Lemma D_7ec88 : decode_any W_7ec88 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec8c : bv 32 := 0x7a813b83.
Lemma F_7ec8c : fetch_word Asan.M.loaded_segments (0x7ecdc : word) = Some W_7ec8c.
Proof. vm_refl. Qed.
Lemma D_7ec8c : decode_any W_7ec8c = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec90 : bv 32 := 0x7f010113.
Lemma F_7ec90 : fetch_word Asan.M.loaded_segments (0x7ece0 : word) = Some W_7ec90.
Proof. vm_refl. Qed.
Lemma D_7ec90 : decode_any W_7ec90 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ec94 : bv 32 := 0x00008067.
Lemma F_7ec94 : fetch_word Asan.M.loaded_segments (0x7ece4 : word) = Some W_7ec94.
Proof. vm_refl. Qed.
Lemma D_7ec94 : decode_any W_7ec94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ed70 : bv 32 := 0x22061663.
Lemma F_7ed70 : fetch_word Asan.M.loaded_segments (0x7edc0 : word) = Some W_7ed70.
Proof. vm_refl. Qed.
Lemma D_7ed70 : decode_any W_7ed70 = Some (Branch BC_NE 12 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ed74 : bv 32 := 0xee9ff06f.
Lemma F_7ed74 : fetch_word Asan.M.loaded_segments (0x7edc4 : word) = Some W_7ed74.
Proof. vm_refl. Qed.
Lemma D_7ed74 : decode_any W_7ed74 = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eebc : bv 32 := 0x02061e63.
Lemma F_7eebc : fetch_word Asan.M.loaded_segments (0x7ef0c : word) = Some W_7eebc.
Proof. vm_refl. Qed.
Lemma D_7eebc : decode_any W_7eebc = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eec0 : bv 32 := 0xd55ff06f.
Lemma F_7eec0 : fetch_word Asan.M.loaded_segments (0x7ef10 : word) = Some W_7eec0.
Proof. vm_refl. Qed.
Lemma D_7eec0 : decode_any W_7eec0 = Some (Jal 0 2096468, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eec4 : bv 32 := 0x00070783.
Lemma F_7eec4 : fetch_word Asan.M.loaded_segments (0x7ef14 : word) = Some W_7eec4.
Proof. vm_refl. Qed.
Lemma D_7eec4 : decode_any W_7eec4 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eec8 : bv 32 := 0x007af813.
Lemma F_7eec8 : fetch_word Asan.M.loaded_segments (0x7ef18 : word) = Some W_7eec8.
Proof. vm_refl. Qed.
Lemma D_7eec8 : decode_any W_7eec8 = Some (OpImm ALU_AND 16 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eecc : bv 32 := 0x00f038b3.
Lemma F_7eecc : fetch_word Asan.M.loaded_segments (0x7ef1c : word) = Some W_7eecc.
Proof. vm_refl. Qed.
Lemma D_7eecc : decode_any W_7eecc = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eed0 : bv 32 := 0x00f827b3.
Lemma F_7eed0 : fetch_word Asan.M.loaded_segments (0x7ef20 : word) = Some W_7eed0.
Proof. vm_refl. Qed.
Lemma D_7eed0 : decode_any W_7eed0 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eed4 : bv 32 := 0x0017c793.
Lemma F_7eed4 : fetch_word Asan.M.loaded_segments (0x7ef24 : word) = Some W_7eed4.
Proof. vm_refl. Qed.
Lemma D_7eed4 : decode_any W_7eed4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eed8 : bv 32 := 0x00f8f7b3.
Lemma F_7eed8 : fetch_word Asan.M.loaded_segments (0x7ef28 : word) = Some W_7eed8.
Proof. vm_refl. Qed.
Lemma D_7eed8 : decode_any W_7eed8 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eedc : bv 32 := 0x00e6fa63.
Lemma F_7eedc : fetch_word Asan.M.loaded_segments (0x7ef2c : word) = Some W_7eedc.
Proof. vm_refl. Qed.
Lemma D_7eedc : decode_any W_7eedc = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eee0 : bv 32 := 0x0006c803.
Lemma F_7eee0 : fetch_word Asan.M.loaded_segments (0x7ef30 : word) = Some W_7eee0.
Proof. vm_refl. Qed.
Lemma D_7eee0 : decode_any W_7eee0 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eee4 : bv 32 := 0x00168693.
Lemma F_7eee4 : fetch_word Asan.M.loaded_segments (0x7ef34 : word) = Some W_7eee4.
Proof. vm_refl. Qed.
Lemma D_7eee4 : decode_any W_7eee4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eee8 : bv 32 := 0x00f867b3.
Lemma F_7eee8 : fetch_word Asan.M.loaded_segments (0x7ef38 : word) = Some W_7eee8.
Proof. vm_refl. Qed.
Lemma D_7eee8 : decode_any W_7eee8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eeec : bv 32 := 0xfee69ae3.
Lemma F_7eeec : fetch_word Asan.M.loaded_segments (0x7ef3c : word) = Some W_7eeec.
Proof. vm_refl. Qed.
Lemma D_7eeec : decode_any W_7eeec = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eef0 : bv 32 := 0x0ff7f693.
Lemma F_7eef0 : fetch_word Asan.M.loaded_segments (0x7ef40 : word) = Some W_7eef0.
Proof. vm_refl. Qed.
Lemma D_7eef0 : decode_any W_7eef0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eef4 : bv 32 := 0xd20680e3.
Lemma F_7eef4 : fetch_word Asan.M.loaded_segments (0x7ef44 : word) = Some W_7eef4.
Proof. vm_refl. Qed.
Lemma D_7eef4 : decode_any W_7eef4 = Some (Branch BC_EQ 13 0 7456, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eef8 : bv 32 := 0x00050a93.
Lemma F_7eef8 : fetch_word Asan.M.loaded_segments (0x7ef48 : word) = Some W_7eef8.
Proof. vm_refl. Qed.
Lemma D_7eef8 : decode_any W_7eef8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7eefc : bv 32 := 0x00058513.
Lemma F_7eefc : fetch_word Asan.M.loaded_segments (0x7ef4c : word) = Some W_7eefc.
Proof. vm_refl. Qed.
Lemma D_7eefc : decode_any W_7eefc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef00 : bv 32 := 0x00058b93.
Lemma F_7ef00 : fetch_word Asan.M.loaded_segments (0x7ef50 : word) = Some W_7ef00.
Proof. vm_refl. Qed.
Lemma D_7ef00 : decode_any W_7ef00 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef04 : bv 32 := 0x00060593.
Lemma F_7ef04 : fetch_word Asan.M.loaded_segments (0x7ef54 : word) = Some W_7ef04.
Proof. vm_refl. Qed.
Lemma D_7ef04 : decode_any W_7ef04 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef08 : bv 32 := 0x00060493.
Lemma F_7ef08 : fetch_word Asan.M.loaded_segments (0x7ef58 : word) = Some W_7ef08.
Proof. vm_refl. Qed.
Lemma D_7ef08 : decode_any W_7ef08 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef0c : bv 32 := 0x48c030ef.
Lemma F_7ef0c : fetch_word Asan.M.loaded_segments (0x7ef5c : word) = Some W_7ef0c.
Proof. vm_refl. Qed.
Lemma D_7ef0c : decode_any W_7ef0c = Some (Jal 1 13452, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef10 : bv 32 := 0x000b8593.
Lemma F_7ef10 : fetch_word Asan.M.loaded_segments (0x7ef60 : word) = Some W_7ef10.
Proof. vm_refl. Qed.
Lemma D_7ef10 : decode_any W_7ef10 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef14 : bv 32 := 0x00048613.
Lemma F_7ef14 : fetch_word Asan.M.loaded_segments (0x7ef64 : word) = Some W_7ef14.
Proof. vm_refl. Qed.
Lemma D_7ef14 : decode_any W_7ef14 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef18 : bv 32 := 0x00050913.
Lemma F_7ef18 : fetch_word Asan.M.loaded_segments (0x7ef68 : word) = Some W_7ef18.
Proof. vm_refl. Qed.
Lemma D_7ef18 : decode_any W_7ef18 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef1c : bv 32 := 0x000a8513.
Lemma F_7ef1c : fetch_word Asan.M.loaded_segments (0x7ef6c : word) = Some W_7ef1c.
Proof. vm_refl. Qed.
Lemma D_7ef1c : decode_any W_7ef1c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef20 : bv 32 := 0xce090ae3.
Lemma F_7ef20 : fetch_word Asan.M.loaded_segments (0x7ef70 : word) = Some W_7ef20.
Proof. vm_refl. Qed.
Lemma D_7ef20 : decode_any W_7ef20 = Some (Branch BC_EQ 18 0 7412, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef68 : bv 32 := 0x00070783.
Lemma F_7ef68 : fetch_word Asan.M.loaded_segments (0x7efb8 : word) = Some W_7ef68.
Proof. vm_refl. Qed.
Lemma D_7ef68 : decode_any W_7ef68 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef6c : bv 32 := 0x0079f813.
Lemma F_7ef6c : fetch_word Asan.M.loaded_segments (0x7efbc : word) = Some W_7ef6c.
Proof. vm_refl. Qed.
Lemma D_7ef6c : decode_any W_7ef6c = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef70 : bv 32 := 0x00f038b3.
Lemma F_7ef70 : fetch_word Asan.M.loaded_segments (0x7efc0 : word) = Some W_7ef70.
Proof. vm_refl. Qed.
Lemma D_7ef70 : decode_any W_7ef70 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef74 : bv 32 := 0x00f827b3.
Lemma F_7ef74 : fetch_word Asan.M.loaded_segments (0x7efc4 : word) = Some W_7ef74.
Proof. vm_refl. Qed.
Lemma D_7ef74 : decode_any W_7ef74 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef78 : bv 32 := 0x0017c793.
Lemma F_7ef78 : fetch_word Asan.M.loaded_segments (0x7efc8 : word) = Some W_7ef78.
Proof. vm_refl. Qed.
Lemma D_7ef78 : decode_any W_7ef78 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef7c : bv 32 := 0x00f8f7b3.
Lemma F_7ef7c : fetch_word Asan.M.loaded_segments (0x7efcc : word) = Some W_7ef7c.
Proof. vm_refl. Qed.
Lemma D_7ef7c : decode_any W_7ef7c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef80 : bv 32 := 0x00e6fa63.
Lemma F_7ef80 : fetch_word Asan.M.loaded_segments (0x7efd0 : word) = Some W_7ef80.
Proof. vm_refl. Qed.
Lemma D_7ef80 : decode_any W_7ef80 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef84 : bv 32 := 0x0006c803.
Lemma F_7ef84 : fetch_word Asan.M.loaded_segments (0x7efd4 : word) = Some W_7ef84.
Proof. vm_refl. Qed.
Lemma D_7ef84 : decode_any W_7ef84 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef88 : bv 32 := 0x00168693.
Lemma F_7ef88 : fetch_word Asan.M.loaded_segments (0x7efd8 : word) = Some W_7ef88.
Proof. vm_refl. Qed.
Lemma D_7ef88 : decode_any W_7ef88 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef8c : bv 32 := 0x00f867b3.
Lemma F_7ef8c : fetch_word Asan.M.loaded_segments (0x7efdc : word) = Some W_7ef8c.
Proof. vm_refl. Qed.
Lemma D_7ef8c : decode_any W_7ef8c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef90 : bv 32 := 0xfee69ae3.
Lemma F_7ef90 : fetch_word Asan.M.loaded_segments (0x7efe0 : word) = Some W_7ef90.
Proof. vm_refl. Qed.
Lemma D_7ef90 : decode_any W_7ef90 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef94 : bv 32 := 0x0ff7f693.
Lemma F_7ef94 : fetch_word Asan.M.loaded_segments (0x7efe4 : word) = Some W_7ef94.
Proof. vm_refl. Qed.
Lemma D_7ef94 : decode_any W_7ef94 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef98 : bv 32 := 0xcc0682e3.
Lemma F_7ef98 : fetch_word Asan.M.loaded_segments (0x7efe8 : word) = Some W_7ef98.
Proof. vm_refl. Qed.
Lemma D_7ef98 : decode_any W_7ef98 = Some (Branch BC_EQ 13 0 7364, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ef9c : bv 32 := 0x00050493.
Lemma F_7ef9c : fetch_word Asan.M.loaded_segments (0x7efec : word) = Some W_7ef9c.
Proof. vm_refl. Qed.
Lemma D_7ef9c : decode_any W_7ef9c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7efa0 : bv 32 := 0x00058a93.
Lemma F_7efa0 : fetch_word Asan.M.loaded_segments (0x7eff0 : word) = Some W_7efa0.
Proof. vm_refl. Qed.
Lemma D_7efa0 : decode_any W_7efa0 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7efa4 : bv 32 := 0x00060593.
Lemma F_7efa4 : fetch_word Asan.M.loaded_segments (0x7eff4 : word) = Some W_7efa4.
Proof. vm_refl. Qed.
Lemma D_7efa4 : decode_any W_7efa4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7efa8 : bv 32 := 0x00060913.
Lemma F_7efa8 : fetch_word Asan.M.loaded_segments (0x7eff8 : word) = Some W_7efa8.
Proof. vm_refl. Qed.
Lemma D_7efa8 : decode_any W_7efa8 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7efac : bv 32 := 0x3ec030ef.
Lemma F_7efac : fetch_word Asan.M.loaded_segments (0x7effc : word) = Some W_7efac.
Proof. vm_refl. Qed.
Lemma D_7efac : decode_any W_7efac = Some (Jal 1 13292, 4%Z).
Proof. vm_refl. Qed.

Definition W_7efb0 : bv 32 := 0x000a8593.
Lemma F_7efb0 : fetch_word Asan.M.loaded_segments (0x7f000 : word) = Some W_7efb0.
Proof. vm_refl. Qed.
Lemma D_7efb0 : decode_any W_7efb0 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7efb4 : bv 32 := 0x00090613.
Lemma F_7efb4 : fetch_word Asan.M.loaded_segments (0x7f004 : word) = Some W_7efb4.
Proof. vm_refl. Qed.
Lemma D_7efb4 : decode_any W_7efb4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7efb8 : bv 32 := 0x00050993.
Lemma F_7efb8 : fetch_word Asan.M.loaded_segments (0x7f008 : word) = Some W_7efb8.
Proof. vm_refl. Qed.
Lemma D_7efb8 : decode_any W_7efb8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7efbc : bv 32 := 0x00048513.
Lemma F_7efbc : fetch_word Asan.M.loaded_segments (0x7f00c : word) = Some W_7efbc.
Proof. vm_refl. Qed.
Lemma D_7efbc : decode_any W_7efbc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7efc0 : bv 32 := 0xc8098ee3.
Lemma F_7efc0 : fetch_word Asan.M.loaded_segments (0x7f010 : word) = Some W_7efc0.
Proof. vm_refl. Qed.
Lemma D_7efc0 : decode_any W_7efc0 = Some (Branch BC_EQ 19 0 7324, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f008 : bv 32 := 0x81010113.
Lemma F_7f008 : fetch_word Asan.M.loaded_segments (0x7f058 : word) = Some W_7f008.
Proof. vm_refl. Qed.
Lemma D_7f008 : decode_any W_7f008 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f00c : bv 32 := 0x7e113423.
Lemma F_7f00c : fetch_word Asan.M.loaded_segments (0x7f05c : word) = Some W_7f00c.
Proof. vm_refl. Qed.
Lemma D_7f00c : decode_any W_7f00c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f010 : bv 32 := 0x7e813023.
Lemma F_7f010 : fetch_word Asan.M.loaded_segments (0x7f060 : word) = Some W_7f010.
Proof. vm_refl. Qed.
Lemma D_7f010 : decode_any W_7f010 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f014 : bv 32 := 0x7c913c23.
Lemma F_7f014 : fetch_word Asan.M.loaded_segments (0x7f064 : word) = Some W_7f014.
Proof. vm_refl. Qed.
Lemma D_7f014 : decode_any W_7f014 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f018 : bv 32 := 0x7d213823.
Lemma F_7f018 : fetch_word Asan.M.loaded_segments (0x7f068 : word) = Some W_7f018.
Proof. vm_refl. Qed.
Lemma D_7f018 : decode_any W_7f018 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f01c : bv 32 := 0x7d313423.
Lemma F_7f01c : fetch_word Asan.M.loaded_segments (0x7f06c : word) = Some W_7f01c.
Proof. vm_refl. Qed.
Lemma D_7f01c : decode_any W_7f01c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f020 : bv 32 := 0x7d413023.
Lemma F_7f020 : fetch_word Asan.M.loaded_segments (0x7f070 : word) = Some W_7f020.
Proof. vm_refl. Qed.
Lemma D_7f020 : decode_any W_7f020 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f024 : bv 32 := 0x7b513c23.
Lemma F_7f024 : fetch_word Asan.M.loaded_segments (0x7f074 : word) = Some W_7f024.
Proof. vm_refl. Qed.
Lemma D_7f024 : decode_any W_7f024 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f028 : bv 32 := 0x7f010413.
Lemma F_7f028 : fetch_word Asan.M.loaded_segments (0x7f078 : word) = Some W_7f028.
Proof. vm_refl. Qed.
Lemma D_7f028 : decode_any W_7f028 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f02c : bv 32 := 0xfa010113.
Lemma F_7f02c : fetch_word Asan.M.loaded_segments (0x7f07c : word) = Some W_7f02c.
Proof. vm_refl. Qed.
Lemma D_7f02c : decode_any W_7f02c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f030 : bv 32 := 0x000d9697.
Lemma F_7f030 : fetch_word Asan.M.loaded_segments (0x7f080 : word) = Some W_7f030.
Proof. vm_refl. Qed.
Lemma D_7f030 : decode_any W_7f030 = Some (Auipc 13 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f034 : bv 32 := 0x8806b683.
Lemma F_7f034 : fetch_word Asan.M.loaded_segments (0x7f084 : word) = Some W_7f034.
Proof. vm_refl. Qed.
Lemma D_7f034 : decode_any W_7f034 = Some (Load SZ8 true 13 13 2176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f038 : bv 32 := 0x0006c683.
Lemma F_7f038 : fetch_word Asan.M.loaded_segments (0x7f088 : word) = Some W_7f038.
Proof. vm_refl. Qed.
Lemma D_7f038 : decode_any W_7f038 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f03c : bv 32 := 0x08068863.
Lemma F_7f03c : fetch_word Asan.M.loaded_segments (0x7f08c : word) = Some W_7f03c.
Proof. vm_refl. Qed.
Lemma D_7f03c : decode_any W_7f03c = Some (Branch BC_EQ 13 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f040 : bv 32 := 0xfff54693.
Lemma F_7f040 : fetch_word Asan.M.loaded_segments (0x7f090 : word) = Some W_7f040.
Proof. vm_refl. Qed.
Lemma D_7f040 : decode_any W_7f040 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f044 : bv 32 := 0x80040a13.
Lemma F_7f044 : fetch_word Asan.M.loaded_segments (0x7f094 : word) = Some W_7f044.
Proof. vm_refl. Qed.
Lemma D_7f044 : decode_any W_7f044 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f048 : bv 32 := 0xfb0a0a13.
Lemma F_7f048 : fetch_word Asan.M.loaded_segments (0x7f098 : word) = Some W_7f048.
Proof. vm_refl. Qed.
Lemma D_7f048 : decode_any W_7f048 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f04c : bv 32 := 0x0cc6e663.
Lemma F_7f04c : fetch_word Asan.M.loaded_segments (0x7f09c : word) = Some W_7f04c.
Proof. vm_refl. Qed.
Lemma D_7f04c : decode_any W_7f04c = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f050 : bv 32 := 0xfbf60693.
Lemma F_7f050 : fetch_word Asan.M.loaded_segments (0x7f0a0 : word) = Some W_7f050.
Proof. vm_refl. Qed.
Lemma D_7f050 : decode_any W_7f050 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f054 : bv 32 := 0xfbf00713.
Lemma F_7f054 : fetch_word Asan.M.loaded_segments (0x7f0a4 : word) = Some W_7f054.
Proof. vm_refl. Qed.
Lemma D_7f054 : decode_any W_7f054 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f058 : bv 32 := 0x14d77463.
Lemma F_7f058 : fetch_word Asan.M.loaded_segments (0x7f0a8 : word) = Some W_7f058.
Proof. vm_refl. Qed.
Lemma D_7f058 : decode_any W_7f058 = Some (Branch BC_GEU 14 13 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f05c : bv 32 := 0x000d8697.
Lemma F_7f05c : fetch_word Asan.M.loaded_segments (0x7f0ac : word) = Some W_7f05c.
Proof. vm_refl. Qed.
Lemma D_7f05c : decode_any W_7f05c = Some (Auipc 13 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f060 : bv 32 := 0xcec6b683.
Lemma F_7f060 : fetch_word Asan.M.loaded_segments (0x7f0b0 : word) = Some W_7f060.
Proof. vm_refl. Qed.
Lemma D_7f060 : decode_any W_7f060 = Some (Load SZ8 true 13 13 3308, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f064 : bv 32 := 0x00c507b3.
Lemma F_7f064 : fetch_word Asan.M.loaded_segments (0x7f0b4 : word) = Some W_7f064.
Proof. vm_refl. Qed.
Lemma D_7f064 : decode_any W_7f064 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f068 : bv 32 := 0x0006b703.
Lemma F_7f068 : fetch_word Asan.M.loaded_segments (0x7f0b8 : word) = Some W_7f068.
Proof. vm_refl. Qed.
Lemma D_7f068 : decode_any W_7f068 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f06c : bv 32 := 0x00355693.
Lemma F_7f06c : fetch_word Asan.M.loaded_segments (0x7f0bc : word) = Some W_7f06c.
Proof. vm_refl. Qed.
Lemma D_7f06c : decode_any W_7f06c = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f070 : bv 32 := 0xfff78793.
Lemma F_7f070 : fetch_word Asan.M.loaded_segments (0x7f0c0 : word) = Some W_7f070.
Proof. vm_refl. Qed.
Lemma D_7f070 : decode_any W_7f070 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f074 : bv 32 := 0x0037d813.
Lemma F_7f074 : fetch_word Asan.M.loaded_segments (0x7f0c4 : word) = Some W_7f074.
Proof. vm_refl. Qed.
Lemma D_7f074 : decode_any W_7f074 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f078 : bv 32 := 0x00d706b3.
Lemma F_7f078 : fetch_word Asan.M.loaded_segments (0x7f0c8 : word) = Some W_7f078.
Proof. vm_refl. Qed.
Lemma D_7f078 : decode_any W_7f078 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f07c : bv 32 := 0x01070733.
Lemma F_7f07c : fetch_word Asan.M.loaded_segments (0x7f0cc : word) = Some W_7f07c.
Proof. vm_refl. Qed.
Lemma D_7f07c : decode_any W_7f07c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f080 : bv 32 := 0xff86f813.
Lemma F_7f080 : fetch_word Asan.M.loaded_segments (0x7f0d0 : word) = Some W_7f080.
Proof. vm_refl. Qed.
Lemma D_7f080 : decode_any W_7f080 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f084 : bv 32 := 0xff877893.
Lemma F_7f084 : fetch_word Asan.M.loaded_segments (0x7f0d4 : word) = Some W_7f084.
Proof. vm_refl. Qed.
Lemma D_7f084 : decode_any W_7f084 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f088 : bv 32 := 0x00083803.
Lemma F_7f088 : fetch_word Asan.M.loaded_segments (0x7f0d8 : word) = Some W_7f088.
Proof. vm_refl. Qed.
Lemma D_7f088 : decode_any W_7f088 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f08c : bv 32 := 0x0008b883.
Lemma F_7f08c : fetch_word Asan.M.loaded_segments (0x7f0dc : word) = Some W_7f08c.
Proof. vm_refl. Qed.
Lemma D_7f08c : decode_any W_7f08c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f090 : bv 32 := 0x0108e833.
Lemma F_7f090 : fetch_word Asan.M.loaded_segments (0x7f0e0 : word) = Some W_7f090.
Proof. vm_refl. Qed.
Lemma D_7f090 : decode_any W_7f090 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f094 : bv 32 := 0x10081a63.
Lemma F_7f094 : fetch_word Asan.M.loaded_segments (0x7f0e4 : word) = Some W_7f094.
Proof. vm_refl. Qed.
Lemma D_7f094 : decode_any W_7f094 = Some (Branch BC_NE 16 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f098 : bv 32 := 0x000da697.
Lemma F_7f098 : fetch_word Asan.M.loaded_segments (0x7f0e8 : word) = Some W_7f098.
Proof. vm_refl. Qed.
Lemma D_7f098 : decode_any W_7f098 = Some (Auipc 13 218, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f09c : bv 32 := 0xcc06b683.
Lemma F_7f09c : fetch_word Asan.M.loaded_segments (0x7f0ec : word) = Some W_7f09c.
Proof. vm_refl. Qed.
Lemma D_7f09c : decode_any W_7f09c = Some (Load SZ8 true 13 13 3264, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f0a0 : bv 32 := 0x000680e7.
Lemma F_7f0a0 : fetch_word Asan.M.loaded_segments (0x7f0f0 : word) = Some W_7f0a0.
Proof. vm_refl. Qed.
Lemma D_7f0a0 : decode_any W_7f0a0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f0a4 : bv 32 := 0x06010113.
Lemma F_7f0a4 : fetch_word Asan.M.loaded_segments (0x7f0f4 : word) = Some W_7f0a4.
Proof. vm_refl. Qed.
Lemma D_7f0a4 : decode_any W_7f0a4 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f0a8 : bv 32 := 0x7e813083.
Lemma F_7f0a8 : fetch_word Asan.M.loaded_segments (0x7f0f8 : word) = Some W_7f0a8.
Proof. vm_refl. Qed.
Lemma D_7f0a8 : decode_any W_7f0a8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f0ac : bv 32 := 0x7e013403.
Lemma F_7f0ac : fetch_word Asan.M.loaded_segments (0x7f0fc : word) = Some W_7f0ac.
Proof. vm_refl. Qed.
Lemma D_7f0ac : decode_any W_7f0ac = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f0b0 : bv 32 := 0x7d813483.
Lemma F_7f0b0 : fetch_word Asan.M.loaded_segments (0x7f100 : word) = Some W_7f0b0.
Proof. vm_refl. Qed.
Lemma D_7f0b0 : decode_any W_7f0b0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f0b4 : bv 32 := 0x7d013903.
Lemma F_7f0b4 : fetch_word Asan.M.loaded_segments (0x7f104 : word) = Some W_7f0b4.
Proof. vm_refl. Qed.
Lemma D_7f0b4 : decode_any W_7f0b4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f0b8 : bv 32 := 0x7c813983.
Lemma F_7f0b8 : fetch_word Asan.M.loaded_segments (0x7f108 : word) = Some W_7f0b8.
Proof. vm_refl. Qed.
Lemma D_7f0b8 : decode_any W_7f0b8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f0bc : bv 32 := 0x7c013a03.
Lemma F_7f0bc : fetch_word Asan.M.loaded_segments (0x7f10c : word) = Some W_7f0bc.
Proof. vm_refl. Qed.
Lemma D_7f0bc : decode_any W_7f0bc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f0c0 : bv 32 := 0x7b813a83.
Lemma F_7f0c0 : fetch_word Asan.M.loaded_segments (0x7f110 : word) = Some W_7f0c0.
Proof. vm_refl. Qed.
Lemma D_7f0c0 : decode_any W_7f0c0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f0c4 : bv 32 := 0x7f010113.
Lemma F_7f0c4 : fetch_word Asan.M.loaded_segments (0x7f114 : word) = Some W_7f0c4.
Proof. vm_refl. Qed.
Lemma D_7f0c4 : decode_any W_7f0c4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f0c8 : bv 32 := 0x00008067.
Lemma F_7f0c8 : fetch_word Asan.M.loaded_segments (0x7f118 : word) = Some W_7f0c8.
Proof. vm_refl. Qed.
Lemma D_7f0c8 : decode_any W_7f0c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1a0 : bv 32 := 0x02061e63.
Lemma F_7f1a0 : fetch_word Asan.M.loaded_segments (0x7f1f0 : word) = Some W_7f1a0.
Proof. vm_refl. Qed.
Lemma D_7f1a0 : decode_any W_7f1a0 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1a4 : bv 32 := 0xef5ff06f.
Lemma F_7f1a4 : fetch_word Asan.M.loaded_segments (0x7f1f4 : word) = Some W_7f1a4.
Proof. vm_refl. Qed.
Lemma D_7f1a4 : decode_any W_7f1a4 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1a8 : bv 32 := 0x00070803.
Lemma F_7f1a8 : fetch_word Asan.M.loaded_segments (0x7f1f8 : word) = Some W_7f1a8.
Proof. vm_refl. Qed.
Lemma D_7f1a8 : decode_any W_7f1a8 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1ac : bv 32 := 0x0077f793.
Lemma F_7f1ac : fetch_word Asan.M.loaded_segments (0x7f1fc : word) = Some W_7f1ac.
Proof. vm_refl. Qed.
Lemma D_7f1ac : decode_any W_7f1ac = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1b0 : bv 32 := 0x010038b3.
Lemma F_7f1b0 : fetch_word Asan.M.loaded_segments (0x7f200 : word) = Some W_7f1b0.
Proof. vm_refl. Qed.
Lemma D_7f1b0 : decode_any W_7f1b0 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1b4 : bv 32 := 0x0107a7b3.
Lemma F_7f1b4 : fetch_word Asan.M.loaded_segments (0x7f204 : word) = Some W_7f1b4.
Proof. vm_refl. Qed.
Lemma D_7f1b4 : decode_any W_7f1b4 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1b8 : bv 32 := 0x0017c793.
Lemma F_7f1b8 : fetch_word Asan.M.loaded_segments (0x7f208 : word) = Some W_7f1b8.
Proof. vm_refl. Qed.
Lemma D_7f1b8 : decode_any W_7f1b8 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1bc : bv 32 := 0x00f8f7b3.
Lemma F_7f1bc : fetch_word Asan.M.loaded_segments (0x7f20c : word) = Some W_7f1bc.
Proof. vm_refl. Qed.
Lemma D_7f1bc : decode_any W_7f1bc = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1c0 : bv 32 := 0x00e6fa63.
Lemma F_7f1c0 : fetch_word Asan.M.loaded_segments (0x7f210 : word) = Some W_7f1c0.
Proof. vm_refl. Qed.
Lemma D_7f1c0 : decode_any W_7f1c0 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1c4 : bv 32 := 0x0006c803.
Lemma F_7f1c4 : fetch_word Asan.M.loaded_segments (0x7f214 : word) = Some W_7f1c4.
Proof. vm_refl. Qed.
Lemma D_7f1c4 : decode_any W_7f1c4 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1c8 : bv 32 := 0x00168693.
Lemma F_7f1c8 : fetch_word Asan.M.loaded_segments (0x7f218 : word) = Some W_7f1c8.
Proof. vm_refl. Qed.
Lemma D_7f1c8 : decode_any W_7f1c8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1cc : bv 32 := 0x00f867b3.
Lemma F_7f1cc : fetch_word Asan.M.loaded_segments (0x7f21c : word) = Some W_7f1cc.
Proof. vm_refl. Qed.
Lemma D_7f1cc : decode_any W_7f1cc = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1d0 : bv 32 := 0xfee69ae3.
Lemma F_7f1d0 : fetch_word Asan.M.loaded_segments (0x7f220 : word) = Some W_7f1d0.
Proof. vm_refl. Qed.
Lemma D_7f1d0 : decode_any W_7f1d0 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1d4 : bv 32 := 0x0ff7f693.
Lemma F_7f1d4 : fetch_word Asan.M.loaded_segments (0x7f224 : word) = Some W_7f1d4.
Proof. vm_refl. Qed.
Lemma D_7f1d4 : decode_any W_7f1d4 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1d8 : bv 32 := 0xec0680e3.
Lemma F_7f1d8 : fetch_word Asan.M.loaded_segments (0x7f228 : word) = Some W_7f1d8.
Proof. vm_refl. Qed.
Lemma D_7f1d8 : decode_any W_7f1d8 = Some (Branch BC_EQ 13 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1dc : bv 32 := 0x00050493.
Lemma F_7f1dc : fetch_word Asan.M.loaded_segments (0x7f22c : word) = Some W_7f1dc.
Proof. vm_refl. Qed.
Lemma D_7f1dc : decode_any W_7f1dc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1e0 : bv 32 := 0x00058a93.
Lemma F_7f1e0 : fetch_word Asan.M.loaded_segments (0x7f230 : word) = Some W_7f1e0.
Proof. vm_refl. Qed.
Lemma D_7f1e0 : decode_any W_7f1e0 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1e4 : bv 32 := 0x00060593.
Lemma F_7f1e4 : fetch_word Asan.M.loaded_segments (0x7f234 : word) = Some W_7f1e4.
Proof. vm_refl. Qed.
Lemma D_7f1e4 : decode_any W_7f1e4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1e8 : bv 32 := 0x00060913.
Lemma F_7f1e8 : fetch_word Asan.M.loaded_segments (0x7f238 : word) = Some W_7f1e8.
Proof. vm_refl. Qed.
Lemma D_7f1e8 : decode_any W_7f1e8 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1ec : bv 32 := 0x1ac030ef.
Lemma F_7f1ec : fetch_word Asan.M.loaded_segments (0x7f23c : word) = Some W_7f1ec.
Proof. vm_refl. Qed.
Lemma D_7f1ec : decode_any W_7f1ec = Some (Jal 1 12716, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1f0 : bv 32 := 0x000a8593.
Lemma F_7f1f0 : fetch_word Asan.M.loaded_segments (0x7f240 : word) = Some W_7f1f0.
Proof. vm_refl. Qed.
Lemma D_7f1f0 : decode_any W_7f1f0 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1f4 : bv 32 := 0x00090613.
Lemma F_7f1f4 : fetch_word Asan.M.loaded_segments (0x7f244 : word) = Some W_7f1f4.
Proof. vm_refl. Qed.
Lemma D_7f1f4 : decode_any W_7f1f4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1f8 : bv 32 := 0x00050993.
Lemma F_7f1f8 : fetch_word Asan.M.loaded_segments (0x7f248 : word) = Some W_7f1f8.
Proof. vm_refl. Qed.
Lemma D_7f1f8 : decode_any W_7f1f8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f1fc : bv 32 := 0x00048513.
Lemma F_7f1fc : fetch_word Asan.M.loaded_segments (0x7f24c : word) = Some W_7f1fc.
Proof. vm_refl. Qed.
Lemma D_7f1fc : decode_any W_7f1fc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f200 : bv 32 := 0xe8098ce3.
Lemma F_7f200 : fetch_word Asan.M.loaded_segments (0x7f250 : word) = Some W_7f200.
Proof. vm_refl. Qed.
Lemma D_7f200 : decode_any W_7f200 = Some (Branch BC_EQ 19 0 7832, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f248 : bv 32 := 0x81010113.
Lemma F_7f248 : fetch_word Asan.M.loaded_segments (0x7f298 : word) = Some W_7f248.
Proof. vm_refl. Qed.
Lemma D_7f248 : decode_any W_7f248 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f24c : bv 32 := 0x7e113423.
Lemma F_7f24c : fetch_word Asan.M.loaded_segments (0x7f29c : word) = Some W_7f24c.
Proof. vm_refl. Qed.
Lemma D_7f24c : decode_any W_7f24c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f250 : bv 32 := 0x7e813023.
Lemma F_7f250 : fetch_word Asan.M.loaded_segments (0x7f2a0 : word) = Some W_7f250.
Proof. vm_refl. Qed.
Lemma D_7f250 : decode_any W_7f250 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f254 : bv 32 := 0x7c913c23.
Lemma F_7f254 : fetch_word Asan.M.loaded_segments (0x7f2a4 : word) = Some W_7f254.
Proof. vm_refl. Qed.
Lemma D_7f254 : decode_any W_7f254 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f258 : bv 32 := 0x7d213823.
Lemma F_7f258 : fetch_word Asan.M.loaded_segments (0x7f2a8 : word) = Some W_7f258.
Proof. vm_refl. Qed.
Lemma D_7f258 : decode_any W_7f258 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f25c : bv 32 := 0x7d313423.
Lemma F_7f25c : fetch_word Asan.M.loaded_segments (0x7f2ac : word) = Some W_7f25c.
Proof. vm_refl. Qed.
Lemma D_7f25c : decode_any W_7f25c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f260 : bv 32 := 0x7d413023.
Lemma F_7f260 : fetch_word Asan.M.loaded_segments (0x7f2b0 : word) = Some W_7f260.
Proof. vm_refl. Qed.
Lemma D_7f260 : decode_any W_7f260 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f264 : bv 32 := 0x7b513c23.
Lemma F_7f264 : fetch_word Asan.M.loaded_segments (0x7f2b4 : word) = Some W_7f264.
Proof. vm_refl. Qed.
Lemma D_7f264 : decode_any W_7f264 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f268 : bv 32 := 0x7b613823.
Lemma F_7f268 : fetch_word Asan.M.loaded_segments (0x7f2b8 : word) = Some W_7f268.
Proof. vm_refl. Qed.
Lemma D_7f268 : decode_any W_7f268 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f26c : bv 32 := 0x7f010413.
Lemma F_7f26c : fetch_word Asan.M.loaded_segments (0x7f2bc : word) = Some W_7f26c.
Proof. vm_refl. Qed.
Lemma D_7f26c : decode_any W_7f26c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f270 : bv 32 := 0xf9010113.
Lemma F_7f270 : fetch_word Asan.M.loaded_segments (0x7f2c0 : word) = Some W_7f270.
Proof. vm_refl. Qed.
Lemma D_7f270 : decode_any W_7f270 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f274 : bv 32 := 0x000d8697.
Lemma F_7f274 : fetch_word Asan.M.loaded_segments (0x7f2c4 : word) = Some W_7f274.
Proof. vm_refl. Qed.
Lemma D_7f274 : decode_any W_7f274 = Some (Auipc 13 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f278 : bv 32 := 0x63c6b683.
Lemma F_7f278 : fetch_word Asan.M.loaded_segments (0x7f2c8 : word) = Some W_7f278.
Proof. vm_refl. Qed.
Lemma D_7f278 : decode_any W_7f278 = Some (Load SZ8 true 13 13 1596, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f27c : bv 32 := 0x0006c683.
Lemma F_7f27c : fetch_word Asan.M.loaded_segments (0x7f2cc : word) = Some W_7f27c.
Proof. vm_refl. Qed.
Lemma D_7f27c : decode_any W_7f27c = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f280 : bv 32 := 0x0a068463.
Lemma F_7f280 : fetch_word Asan.M.loaded_segments (0x7f2d0 : word) = Some W_7f280.
Proof. vm_refl. Qed.
Lemma D_7f280 : decode_any W_7f280 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f284 : bv 32 := 0xfff5c693.
Lemma F_7f284 : fetch_word Asan.M.loaded_segments (0x7f2d4 : word) = Some W_7f284.
Proof. vm_refl. Qed.
Lemma D_7f284 : decode_any W_7f284 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f288 : bv 32 := 0x80040a13.
Lemma F_7f288 : fetch_word Asan.M.loaded_segments (0x7f2d8 : word) = Some W_7f288.
Proof. vm_refl. Qed.
Lemma D_7f288 : decode_any W_7f288 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f28c : bv 32 := 0xfa8a0a13.
Lemma F_7f28c : fetch_word Asan.M.loaded_segments (0x7f2dc : word) = Some W_7f28c.
Proof. vm_refl. Qed.
Lemma D_7f28c : decode_any W_7f28c = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f290 : bv 32 := 0x0cc6e463.
Lemma F_7f290 : fetch_word Asan.M.loaded_segments (0x7f2e0 : word) = Some W_7f290.
Proof. vm_refl. Qed.
Lemma D_7f290 : decode_any W_7f290 = Some (Branch BC_LTU 13 12 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f294 : bv 32 := 0xfbf60993.
Lemma F_7f294 : fetch_word Asan.M.loaded_segments (0x7f2e4 : word) = Some W_7f294.
Proof. vm_refl. Qed.
Lemma D_7f294 : decode_any W_7f294 = Some (OpImm ALU_ADD 19 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f298 : bv 32 := 0xfbf00693.
Lemma F_7f298 : fetch_word Asan.M.loaded_segments (0x7f2e8 : word) = Some W_7f298.
Proof. vm_refl. Qed.
Lemma D_7f298 : decode_any W_7f298 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f29c : bv 32 := 0x1536f263.
Lemma F_7f29c : fetch_word Asan.M.loaded_segments (0x7f2ec : word) = Some W_7f29c.
Proof. vm_refl. Qed.
Lemma D_7f29c : decode_any W_7f29c = Some (Branch BC_GEU 13 19 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2a0 : bv 32 := 0x000d8697.
Lemma F_7f2a0 : fetch_word Asan.M.loaded_segments (0x7f2f0 : word) = Some W_7f2a0.
Proof. vm_refl. Qed.
Lemma D_7f2a0 : decode_any W_7f2a0 = Some (Auipc 13 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2a4 : bv 32 := 0xaa86b683.
Lemma F_7f2a4 : fetch_word Asan.M.loaded_segments (0x7f2f4 : word) = Some W_7f2a4.
Proof. vm_refl. Qed.
Lemma D_7f2a4 : decode_any W_7f2a4 = Some (Load SZ8 true 13 13 2728, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2a8 : bv 32 := 0x00c587b3.
Lemma F_7f2a8 : fetch_word Asan.M.loaded_segments (0x7f2f8 : word) = Some W_7f2a8.
Proof. vm_refl. Qed.
Lemma D_7f2a8 : decode_any W_7f2a8 = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2ac : bv 32 := 0x0006b703.
Lemma F_7f2ac : fetch_word Asan.M.loaded_segments (0x7f2fc : word) = Some W_7f2ac.
Proof. vm_refl. Qed.
Lemma D_7f2ac : decode_any W_7f2ac = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2b0 : bv 32 := 0x0035d693.
Lemma F_7f2b0 : fetch_word Asan.M.loaded_segments (0x7f300 : word) = Some W_7f2b0.
Proof. vm_refl. Qed.
Lemma D_7f2b0 : decode_any W_7f2b0 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2b4 : bv 32 := 0xfff78793.
Lemma F_7f2b4 : fetch_word Asan.M.loaded_segments (0x7f304 : word) = Some W_7f2b4.
Proof. vm_refl. Qed.
Lemma D_7f2b4 : decode_any W_7f2b4 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2b8 : bv 32 := 0x0037d813.
Lemma F_7f2b8 : fetch_word Asan.M.loaded_segments (0x7f308 : word) = Some W_7f2b8.
Proof. vm_refl. Qed.
Lemma D_7f2b8 : decode_any W_7f2b8 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2bc : bv 32 := 0x00d706b3.
Lemma F_7f2bc : fetch_word Asan.M.loaded_segments (0x7f30c : word) = Some W_7f2bc.
Proof. vm_refl. Qed.
Lemma D_7f2bc : decode_any W_7f2bc = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c0 : bv 32 := 0x01070733.
Lemma F_7f2c0 : fetch_word Asan.M.loaded_segments (0x7f310 : word) = Some W_7f2c0.
Proof. vm_refl. Qed.
Lemma D_7f2c0 : decode_any W_7f2c0 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c4 : bv 32 := 0xff86f813.
Lemma F_7f2c4 : fetch_word Asan.M.loaded_segments (0x7f314 : word) = Some W_7f2c4.
Proof. vm_refl. Qed.
Lemma D_7f2c4 : decode_any W_7f2c4 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2c8 : bv 32 := 0xff877893.
Lemma F_7f2c8 : fetch_word Asan.M.loaded_segments (0x7f318 : word) = Some W_7f2c8.
Proof. vm_refl. Qed.
Lemma D_7f2c8 : decode_any W_7f2c8 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2cc : bv 32 := 0x00083803.
Lemma F_7f2cc : fetch_word Asan.M.loaded_segments (0x7f31c : word) = Some W_7f2cc.
Proof. vm_refl. Qed.
Lemma D_7f2cc : decode_any W_7f2cc = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d0 : bv 32 := 0x0008b883.
Lemma F_7f2d0 : fetch_word Asan.M.loaded_segments (0x7f320 : word) = Some W_7f2d0.
Proof. vm_refl. Qed.
Lemma D_7f2d0 : decode_any W_7f2d0 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d4 : bv 32 := 0x0108e833.
Lemma F_7f2d4 : fetch_word Asan.M.loaded_segments (0x7f324 : word) = Some W_7f2d4.
Proof. vm_refl. Qed.
Lemma D_7f2d4 : decode_any W_7f2d4 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2d8 : bv 32 := 0x18081e63.
Lemma F_7f2d8 : fetch_word Asan.M.loaded_segments (0x7f328 : word) = Some W_7f2d8.
Proof. vm_refl. Qed.
Lemma D_7f2d8 : decode_any W_7f2d8 = Some (Branch BC_NE 16 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2dc : bv 32 := 0xfff54693.
Lemma F_7f2dc : fetch_word Asan.M.loaded_segments (0x7f32c : word) = Some W_7f2dc.
Proof. vm_refl. Qed.
Lemma D_7f2dc : decode_any W_7f2dc = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e0 : bv 32 := 0x10c6e463.
Lemma F_7f2e0 : fetch_word Asan.M.loaded_segments (0x7f330 : word) = Some W_7f2e0.
Proof. vm_refl. Qed.
Lemma D_7f2e0 : decode_any W_7f2e0 = Some (Branch BC_LTU 13 12 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e4 : bv 32 := 0xfbf00693.
Lemma F_7f2e4 : fetch_word Asan.M.loaded_segments (0x7f334 : word) = Some W_7f2e4.
Proof. vm_refl. Qed.
Lemma D_7f2e4 : decode_any W_7f2e4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2e8 : bv 32 := 0x1936f263.
Lemma F_7f2e8 : fetch_word Asan.M.loaded_segments (0x7f338 : word) = Some W_7f2e8.
Proof. vm_refl. Qed.
Lemma D_7f2e8 : decode_any W_7f2e8 = Some (Branch BC_GEU 13 19 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2ec : bv 32 := 0x000d8697.
Lemma F_7f2ec : fetch_word Asan.M.loaded_segments (0x7f33c : word) = Some W_7f2ec.
Proof. vm_refl. Qed.
Lemma D_7f2ec : decode_any W_7f2ec = Some (Auipc 13 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f0 : bv 32 := 0xa5c6b683.
Lemma F_7f2f0 : fetch_word Asan.M.loaded_segments (0x7f340 : word) = Some W_7f2f0.
Proof. vm_refl. Qed.
Lemma D_7f2f0 : decode_any W_7f2f0 = Some (Load SZ8 true 13 13 2652, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f4 : bv 32 := 0x00c507b3.
Lemma F_7f2f4 : fetch_word Asan.M.loaded_segments (0x7f344 : word) = Some W_7f2f4.
Proof. vm_refl. Qed.
Lemma D_7f2f4 : decode_any W_7f2f4 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2f8 : bv 32 := 0x0006b703.
Lemma F_7f2f8 : fetch_word Asan.M.loaded_segments (0x7f348 : word) = Some W_7f2f8.
Proof. vm_refl. Qed.
Lemma D_7f2f8 : decode_any W_7f2f8 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f2fc : bv 32 := 0x00355693.
Lemma F_7f2fc : fetch_word Asan.M.loaded_segments (0x7f34c : word) = Some W_7f2fc.
Proof. vm_refl. Qed.
Lemma D_7f2fc : decode_any W_7f2fc = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f300 : bv 32 := 0xfff78793.
Lemma F_7f300 : fetch_word Asan.M.loaded_segments (0x7f350 : word) = Some W_7f300.
Proof. vm_refl. Qed.
Lemma D_7f300 : decode_any W_7f300 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f304 : bv 32 := 0x0037d813.
Lemma F_7f304 : fetch_word Asan.M.loaded_segments (0x7f354 : word) = Some W_7f304.
Proof. vm_refl. Qed.
Lemma D_7f304 : decode_any W_7f304 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f308 : bv 32 := 0x00d706b3.
Lemma F_7f308 : fetch_word Asan.M.loaded_segments (0x7f358 : word) = Some W_7f308.
Proof. vm_refl. Qed.
Lemma D_7f308 : decode_any W_7f308 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f30c : bv 32 := 0x01070733.
Lemma F_7f30c : fetch_word Asan.M.loaded_segments (0x7f35c : word) = Some W_7f30c.
Proof. vm_refl. Qed.
Lemma D_7f30c : decode_any W_7f30c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f310 : bv 32 := 0xff86f813.
Lemma F_7f310 : fetch_word Asan.M.loaded_segments (0x7f360 : word) = Some W_7f310.
Proof. vm_refl. Qed.
Lemma D_7f310 : decode_any W_7f310 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f314 : bv 32 := 0xff877893.
Lemma F_7f314 : fetch_word Asan.M.loaded_segments (0x7f364 : word) = Some W_7f314.
Proof. vm_refl. Qed.
Lemma D_7f314 : decode_any W_7f314 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f318 : bv 32 := 0x00083803.
Lemma F_7f318 : fetch_word Asan.M.loaded_segments (0x7f368 : word) = Some W_7f318.
Proof. vm_refl. Qed.
Lemma D_7f318 : decode_any W_7f318 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f31c : bv 32 := 0x0008b883.
Lemma F_7f31c : fetch_word Asan.M.loaded_segments (0x7f36c : word) = Some W_7f31c.
Proof. vm_refl. Qed.
Lemma D_7f31c : decode_any W_7f31c = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f320 : bv 32 := 0x0108e833.
Lemma F_7f320 : fetch_word Asan.M.loaded_segments (0x7f370 : word) = Some W_7f320.
Proof. vm_refl. Qed.
Lemma D_7f320 : decode_any W_7f320 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f324 : bv 32 := 0x1e081a63.
Lemma F_7f324 : fetch_word Asan.M.loaded_segments (0x7f374 : word) = Some W_7f324.
Proof. vm_refl. Qed.
Lemma D_7f324 : decode_any W_7f324 = Some (Branch BC_NE 16 0 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f328 : bv 32 := 0x7b9120ef.
Lemma F_7f328 : fetch_word Asan.M.loaded_segments (0x7f378 : word) = Some W_7f328.
Proof. vm_refl. Qed.
Lemma D_7f328 : decode_any W_7f328 = Some (Jal 1 77752, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f32c : bv 32 := 0x07010113.
Lemma F_7f32c : fetch_word Asan.M.loaded_segments (0x7f37c : word) = Some W_7f32c.
Proof. vm_refl. Qed.
Lemma D_7f32c : decode_any W_7f32c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f330 : bv 32 := 0x7e813083.
Lemma F_7f330 : fetch_word Asan.M.loaded_segments (0x7f380 : word) = Some W_7f330.
Proof. vm_refl. Qed.
Lemma D_7f330 : decode_any W_7f330 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f334 : bv 32 := 0x7e013403.
Lemma F_7f334 : fetch_word Asan.M.loaded_segments (0x7f384 : word) = Some W_7f334.
Proof. vm_refl. Qed.
Lemma D_7f334 : decode_any W_7f334 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f338 : bv 32 := 0x7d813483.
Lemma F_7f338 : fetch_word Asan.M.loaded_segments (0x7f388 : word) = Some W_7f338.
Proof. vm_refl. Qed.
Lemma D_7f338 : decode_any W_7f338 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f33c : bv 32 := 0x7d013903.
Lemma F_7f33c : fetch_word Asan.M.loaded_segments (0x7f38c : word) = Some W_7f33c.
Proof. vm_refl. Qed.
Lemma D_7f33c : decode_any W_7f33c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f340 : bv 32 := 0x7c813983.
Lemma F_7f340 : fetch_word Asan.M.loaded_segments (0x7f390 : word) = Some W_7f340.
Proof. vm_refl. Qed.
Lemma D_7f340 : decode_any W_7f340 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f344 : bv 32 := 0x7c013a03.
Lemma F_7f344 : fetch_word Asan.M.loaded_segments (0x7f394 : word) = Some W_7f344.
Proof. vm_refl. Qed.
Lemma D_7f344 : decode_any W_7f344 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f348 : bv 32 := 0x7b813a83.
Lemma F_7f348 : fetch_word Asan.M.loaded_segments (0x7f398 : word) = Some W_7f348.
Proof. vm_refl. Qed.
Lemma D_7f348 : decode_any W_7f348 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f34c : bv 32 := 0x7b013b03.
Lemma F_7f34c : fetch_word Asan.M.loaded_segments (0x7f39c : word) = Some W_7f34c.
Proof. vm_refl. Qed.
Lemma D_7f34c : decode_any W_7f34c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f350 : bv 32 := 0x7f010113.
Lemma F_7f350 : fetch_word Asan.M.loaded_segments (0x7f3a0 : word) = Some W_7f350.
Proof. vm_refl. Qed.
Lemma D_7f350 : decode_any W_7f350 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f354 : bv 32 := 0x00008067.
Lemma F_7f354 : fetch_word Asan.M.loaded_segments (0x7f3a4 : word) = Some W_7f354.
Proof. vm_refl. Qed.
Lemma D_7f354 : decode_any W_7f354 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3e0 : bv 32 := 0x0c061463.
Lemma F_7f3e0 : fetch_word Asan.M.loaded_segments (0x7f430 : word) = Some W_7f3e0.
Proof. vm_refl. Qed.
Lemma D_7f3e0 : decode_any W_7f3e0 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f3e4 : bv 32 := 0xef9ff06f.
Lemma F_7f3e4 : fetch_word Asan.M.loaded_segments (0x7f434 : word) = Some W_7f3e4.
Proof. vm_refl. Qed.
Lemma D_7f3e4 : decode_any W_7f3e4 = Some (Jal 0 2096888, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f46c : bv 32 := 0x0e061063.
Lemma F_7f46c : fetch_word Asan.M.loaded_segments (0x7f4bc : word) = Some W_7f46c.
Proof. vm_refl. Qed.
Lemma D_7f46c : decode_any W_7f46c = Some (Branch BC_NE 12 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f470 : bv 32 := 0xeb9ff06f.
Lemma F_7f470 : fetch_word Asan.M.loaded_segments (0x7f4c0 : word) = Some W_7f470.
Proof. vm_refl. Qed.
Lemma D_7f470 : decode_any W_7f470 = Some (Jal 0 2096824, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f474 : bv 32 := 0x00070803.
Lemma F_7f474 : fetch_word Asan.M.loaded_segments (0x7f4c4 : word) = Some W_7f474.
Proof. vm_refl. Qed.
Lemma D_7f474 : decode_any W_7f474 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f478 : bv 32 := 0x0077f793.
Lemma F_7f478 : fetch_word Asan.M.loaded_segments (0x7f4c8 : word) = Some W_7f478.
Proof. vm_refl. Qed.
Lemma D_7f478 : decode_any W_7f478 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f47c : bv 32 := 0x010038b3.
Lemma F_7f47c : fetch_word Asan.M.loaded_segments (0x7f4cc : word) = Some W_7f47c.
Proof. vm_refl. Qed.
Lemma D_7f47c : decode_any W_7f47c = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f480 : bv 32 := 0x0107a7b3.
Lemma F_7f480 : fetch_word Asan.M.loaded_segments (0x7f4d0 : word) = Some W_7f480.
Proof. vm_refl. Qed.
Lemma D_7f480 : decode_any W_7f480 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f484 : bv 32 := 0x0017c793.
Lemma F_7f484 : fetch_word Asan.M.loaded_segments (0x7f4d4 : word) = Some W_7f484.
Proof. vm_refl. Qed.
Lemma D_7f484 : decode_any W_7f484 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f488 : bv 32 := 0x00f8f7b3.
Lemma F_7f488 : fetch_word Asan.M.loaded_segments (0x7f4d8 : word) = Some W_7f488.
Proof. vm_refl. Qed.
Lemma D_7f488 : decode_any W_7f488 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f48c : bv 32 := 0x00e6fa63.
Lemma F_7f48c : fetch_word Asan.M.loaded_segments (0x7f4dc : word) = Some W_7f48c.
Proof. vm_refl. Qed.
Lemma D_7f48c : decode_any W_7f48c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f490 : bv 32 := 0x0006c803.
Lemma F_7f490 : fetch_word Asan.M.loaded_segments (0x7f4e0 : word) = Some W_7f490.
Proof. vm_refl. Qed.
Lemma D_7f490 : decode_any W_7f490 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f494 : bv 32 := 0x00168693.
Lemma F_7f494 : fetch_word Asan.M.loaded_segments (0x7f4e4 : word) = Some W_7f494.
Proof. vm_refl. Qed.
Lemma D_7f494 : decode_any W_7f494 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f498 : bv 32 := 0x00f867b3.
Lemma F_7f498 : fetch_word Asan.M.loaded_segments (0x7f4e8 : word) = Some W_7f498.
Proof. vm_refl. Qed.
Lemma D_7f498 : decode_any W_7f498 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f49c : bv 32 := 0xfee69ae3.
Lemma F_7f49c : fetch_word Asan.M.loaded_segments (0x7f4ec : word) = Some W_7f49c.
Proof. vm_refl. Qed.
Lemma D_7f49c : decode_any W_7f49c = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4a0 : bv 32 := 0x0ff7f693.
Lemma F_7f4a0 : fetch_word Asan.M.loaded_segments (0x7f4f0 : word) = Some W_7f4a0.
Proof. vm_refl. Qed.
Lemma D_7f4a0 : decode_any W_7f4a0 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4a4 : bv 32 := 0xe2068ce3.
Lemma F_7f4a4 : fetch_word Asan.M.loaded_segments (0x7f4f4 : word) = Some W_7f4a4.
Proof. vm_refl. Qed.
Lemma D_7f4a4 : decode_any W_7f4a4 = Some (Branch BC_EQ 13 0 7736, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4a8 : bv 32 := 0x00050a93.
Lemma F_7f4a8 : fetch_word Asan.M.loaded_segments (0x7f4f8 : word) = Some W_7f4a8.
Proof. vm_refl. Qed.
Lemma D_7f4a8 : decode_any W_7f4a8 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4ac : bv 32 := 0x00058513.
Lemma F_7f4ac : fetch_word Asan.M.loaded_segments (0x7f4fc : word) = Some W_7f4ac.
Proof. vm_refl. Qed.
Lemma D_7f4ac : decode_any W_7f4ac = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4b0 : bv 32 := 0x00058b13.
Lemma F_7f4b0 : fetch_word Asan.M.loaded_segments (0x7f500 : word) = Some W_7f4b0.
Proof. vm_refl. Qed.
Lemma D_7f4b0 : decode_any W_7f4b0 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4b4 : bv 32 := 0x00060593.
Lemma F_7f4b4 : fetch_word Asan.M.loaded_segments (0x7f504 : word) = Some W_7f4b4.
Proof. vm_refl. Qed.
Lemma D_7f4b4 : decode_any W_7f4b4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4b8 : bv 32 := 0x00060493.
Lemma F_7f4b8 : fetch_word Asan.M.loaded_segments (0x7f508 : word) = Some W_7f4b8.
Proof. vm_refl. Qed.
Lemma D_7f4b8 : decode_any W_7f4b8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4bc : bv 32 := 0x6dd020ef.
Lemma F_7f4bc : fetch_word Asan.M.loaded_segments (0x7f50c : word) = Some W_7f4bc.
Proof. vm_refl. Qed.
Lemma D_7f4bc : decode_any W_7f4bc = Some (Jal 1 11996, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4c0 : bv 32 := 0x000b0593.
Lemma F_7f4c0 : fetch_word Asan.M.loaded_segments (0x7f510 : word) = Some W_7f4c0.
Proof. vm_refl. Qed.
Lemma D_7f4c0 : decode_any W_7f4c0 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4c4 : bv 32 := 0x00048613.
Lemma F_7f4c4 : fetch_word Asan.M.loaded_segments (0x7f514 : word) = Some W_7f4c4.
Proof. vm_refl. Qed.
Lemma D_7f4c4 : decode_any W_7f4c4 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4c8 : bv 32 := 0x00050913.
Lemma F_7f4c8 : fetch_word Asan.M.loaded_segments (0x7f518 : word) = Some W_7f4c8.
Proof. vm_refl. Qed.
Lemma D_7f4c8 : decode_any W_7f4c8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4cc : bv 32 := 0x000a8513.
Lemma F_7f4cc : fetch_word Asan.M.loaded_segments (0x7f51c : word) = Some W_7f4cc.
Proof. vm_refl. Qed.
Lemma D_7f4cc : decode_any W_7f4cc = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f4d0 : bv 32 := 0xe00906e3.
Lemma F_7f4d0 : fetch_word Asan.M.loaded_segments (0x7f520 : word) = Some W_7f4d0.
Proof. vm_refl. Qed.
Lemma D_7f4d0 : decode_any W_7f4d0 = Some (Branch BC_EQ 18 0 7692, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f518 : bv 32 := 0x00070803.
Lemma F_7f518 : fetch_word Asan.M.loaded_segments (0x7f568 : word) = Some W_7f518.
Proof. vm_refl. Qed.
Lemma D_7f518 : decode_any W_7f518 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f51c : bv 32 := 0x0077f793.
Lemma F_7f51c : fetch_word Asan.M.loaded_segments (0x7f56c : word) = Some W_7f51c.
Proof. vm_refl. Qed.
Lemma D_7f51c : decode_any W_7f51c = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f520 : bv 32 := 0x010038b3.
Lemma F_7f520 : fetch_word Asan.M.loaded_segments (0x7f570 : word) = Some W_7f520.
Proof. vm_refl. Qed.
Lemma D_7f520 : decode_any W_7f520 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f524 : bv 32 := 0x0107a7b3.
Lemma F_7f524 : fetch_word Asan.M.loaded_segments (0x7f574 : word) = Some W_7f524.
Proof. vm_refl. Qed.
Lemma D_7f524 : decode_any W_7f524 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f528 : bv 32 := 0x0017c793.
Lemma F_7f528 : fetch_word Asan.M.loaded_segments (0x7f578 : word) = Some W_7f528.
Proof. vm_refl. Qed.
Lemma D_7f528 : decode_any W_7f528 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f52c : bv 32 := 0x00f8f7b3.
Lemma F_7f52c : fetch_word Asan.M.loaded_segments (0x7f57c : word) = Some W_7f52c.
Proof. vm_refl. Qed.
Lemma D_7f52c : decode_any W_7f52c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f530 : bv 32 := 0x00e6fa63.
Lemma F_7f530 : fetch_word Asan.M.loaded_segments (0x7f580 : word) = Some W_7f530.
Proof. vm_refl. Qed.
Lemma D_7f530 : decode_any W_7f530 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f534 : bv 32 := 0x0006c803.
Lemma F_7f534 : fetch_word Asan.M.loaded_segments (0x7f584 : word) = Some W_7f534.
Proof. vm_refl. Qed.
Lemma D_7f534 : decode_any W_7f534 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f538 : bv 32 := 0x00168693.
Lemma F_7f538 : fetch_word Asan.M.loaded_segments (0x7f588 : word) = Some W_7f538.
Proof. vm_refl. Qed.
Lemma D_7f538 : decode_any W_7f538 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f53c : bv 32 := 0x00f867b3.
Lemma F_7f53c : fetch_word Asan.M.loaded_segments (0x7f58c : word) = Some W_7f53c.
Proof. vm_refl. Qed.
Lemma D_7f53c : decode_any W_7f53c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f540 : bv 32 := 0xfee69ae3.
Lemma F_7f540 : fetch_word Asan.M.loaded_segments (0x7f590 : word) = Some W_7f540.
Proof. vm_refl. Qed.
Lemma D_7f540 : decode_any W_7f540 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f544 : bv 32 := 0x0ff7f693.
Lemma F_7f544 : fetch_word Asan.M.loaded_segments (0x7f594 : word) = Some W_7f544.
Proof. vm_refl. Qed.
Lemma D_7f544 : decode_any W_7f544 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f548 : bv 32 := 0xde0680e3.
Lemma F_7f548 : fetch_word Asan.M.loaded_segments (0x7f598 : word) = Some W_7f548.
Proof. vm_refl. Qed.
Lemma D_7f548 : decode_any W_7f548 = Some (Branch BC_EQ 13 0 7648, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f54c : bv 32 := 0x00050493.
Lemma F_7f54c : fetch_word Asan.M.loaded_segments (0x7f59c : word) = Some W_7f54c.
Proof. vm_refl. Qed.
Lemma D_7f54c : decode_any W_7f54c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f550 : bv 32 := 0x00058a93.
Lemma F_7f550 : fetch_word Asan.M.loaded_segments (0x7f5a0 : word) = Some W_7f550.
Proof. vm_refl. Qed.
Lemma D_7f550 : decode_any W_7f550 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f554 : bv 32 := 0x00060593.
Lemma F_7f554 : fetch_word Asan.M.loaded_segments (0x7f5a4 : word) = Some W_7f554.
Proof. vm_refl. Qed.
Lemma D_7f554 : decode_any W_7f554 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f558 : bv 32 := 0x00060913.
Lemma F_7f558 : fetch_word Asan.M.loaded_segments (0x7f5a8 : word) = Some W_7f558.
Proof. vm_refl. Qed.
Lemma D_7f558 : decode_any W_7f558 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f55c : bv 32 := 0x63d020ef.
Lemma F_7f55c : fetch_word Asan.M.loaded_segments (0x7f5ac : word) = Some W_7f55c.
Proof. vm_refl. Qed.
Lemma D_7f55c : decode_any W_7f55c = Some (Jal 1 11836, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f560 : bv 32 := 0x000a8593.
Lemma F_7f560 : fetch_word Asan.M.loaded_segments (0x7f5b0 : word) = Some W_7f560.
Proof. vm_refl. Qed.
Lemma D_7f560 : decode_any W_7f560 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f564 : bv 32 := 0x00090613.
Lemma F_7f564 : fetch_word Asan.M.loaded_segments (0x7f5b4 : word) = Some W_7f564.
Proof. vm_refl. Qed.
Lemma D_7f564 : decode_any W_7f564 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f568 : bv 32 := 0x00050993.
Lemma F_7f568 : fetch_word Asan.M.loaded_segments (0x7f5b8 : word) = Some W_7f568.
Proof. vm_refl. Qed.
Lemma D_7f568 : decode_any W_7f568 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f56c : bv 32 := 0x00048513.
Lemma F_7f56c : fetch_word Asan.M.loaded_segments (0x7f5bc : word) = Some W_7f56c.
Proof. vm_refl. Qed.
Lemma D_7f56c : decode_any W_7f56c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f570 : bv 32 := 0xda098ce3.
Lemma F_7f570 : fetch_word Asan.M.loaded_segments (0x7f5c0 : word) = Some W_7f570.
Proof. vm_refl. Qed.
Lemma D_7f570 : decode_any W_7f570 = Some (Branch BC_EQ 19 0 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5b8 : bv 32 := 0x81010113.
Lemma F_7f5b8 : fetch_word Asan.M.loaded_segments (0x7f608 : word) = Some W_7f5b8.
Proof. vm_refl. Qed.
Lemma D_7f5b8 : decode_any W_7f5b8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5bc : bv 32 := 0x7e113423.
Lemma F_7f5bc : fetch_word Asan.M.loaded_segments (0x7f60c : word) = Some W_7f5bc.
Proof. vm_refl. Qed.
Lemma D_7f5bc : decode_any W_7f5bc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5c0 : bv 32 := 0x7e813023.
Lemma F_7f5c0 : fetch_word Asan.M.loaded_segments (0x7f610 : word) = Some W_7f5c0.
Proof. vm_refl. Qed.
Lemma D_7f5c0 : decode_any W_7f5c0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5c4 : bv 32 := 0x7c913c23.
Lemma F_7f5c4 : fetch_word Asan.M.loaded_segments (0x7f614 : word) = Some W_7f5c4.
Proof. vm_refl. Qed.
Lemma D_7f5c4 : decode_any W_7f5c4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5c8 : bv 32 := 0x7d213823.
Lemma F_7f5c8 : fetch_word Asan.M.loaded_segments (0x7f618 : word) = Some W_7f5c8.
Proof. vm_refl. Qed.
Lemma D_7f5c8 : decode_any W_7f5c8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5cc : bv 32 := 0x7d313423.
Lemma F_7f5cc : fetch_word Asan.M.loaded_segments (0x7f61c : word) = Some W_7f5cc.
Proof. vm_refl. Qed.
Lemma D_7f5cc : decode_any W_7f5cc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5d0 : bv 32 := 0x7d413023.
Lemma F_7f5d0 : fetch_word Asan.M.loaded_segments (0x7f620 : word) = Some W_7f5d0.
Proof. vm_refl. Qed.
Lemma D_7f5d0 : decode_any W_7f5d0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5d4 : bv 32 := 0x7b513c23.
Lemma F_7f5d4 : fetch_word Asan.M.loaded_segments (0x7f624 : word) = Some W_7f5d4.
Proof. vm_refl. Qed.
Lemma D_7f5d4 : decode_any W_7f5d4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5d8 : bv 32 := 0x7b613823.
Lemma F_7f5d8 : fetch_word Asan.M.loaded_segments (0x7f628 : word) = Some W_7f5d8.
Proof. vm_refl. Qed.
Lemma D_7f5d8 : decode_any W_7f5d8 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5dc : bv 32 := 0x7f010413.
Lemma F_7f5dc : fetch_word Asan.M.loaded_segments (0x7f62c : word) = Some W_7f5dc.
Proof. vm_refl. Qed.
Lemma D_7f5dc : decode_any W_7f5dc = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5e0 : bv 32 := 0xf9010113.
Lemma F_7f5e0 : fetch_word Asan.M.loaded_segments (0x7f630 : word) = Some W_7f5e0.
Proof. vm_refl. Qed.
Lemma D_7f5e0 : decode_any W_7f5e0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5e4 : bv 32 := 0x000d8697.
Lemma F_7f5e4 : fetch_word Asan.M.loaded_segments (0x7f634 : word) = Some W_7f5e4.
Proof. vm_refl. Qed.
Lemma D_7f5e4 : decode_any W_7f5e4 = Some (Auipc 13 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5e8 : bv 32 := 0x2cc6b683.
Lemma F_7f5e8 : fetch_word Asan.M.loaded_segments (0x7f638 : word) = Some W_7f5e8.
Proof. vm_refl. Qed.
Lemma D_7f5e8 : decode_any W_7f5e8 = Some (Load SZ8 true 13 13 716, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5ec : bv 32 := 0x0006c683.
Lemma F_7f5ec : fetch_word Asan.M.loaded_segments (0x7f63c : word) = Some W_7f5ec.
Proof. vm_refl. Qed.
Lemma D_7f5ec : decode_any W_7f5ec = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f0 : bv 32 := 0x08068a63.
Lemma F_7f5f0 : fetch_word Asan.M.loaded_segments (0x7f640 : word) = Some W_7f5f0.
Proof. vm_refl. Qed.
Lemma D_7f5f0 : decode_any W_7f5f0 = Some (Branch BC_EQ 13 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f4 : bv 32 := 0xfff54693.
Lemma F_7f5f4 : fetch_word Asan.M.loaded_segments (0x7f644 : word) = Some W_7f5f4.
Proof. vm_refl. Qed.
Lemma D_7f5f4 : decode_any W_7f5f4 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5f8 : bv 32 := 0x80040a93.
Lemma F_7f5f8 : fetch_word Asan.M.loaded_segments (0x7f648 : word) = Some W_7f5f8.
Proof. vm_refl. Qed.
Lemma D_7f5f8 : decode_any W_7f5f8 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f5fc : bv 32 := 0xfa8a8a93.
Lemma F_7f5fc : fetch_word Asan.M.loaded_segments (0x7f64c : word) = Some W_7f5fc.
Proof. vm_refl. Qed.
Lemma D_7f5fc : decode_any W_7f5fc = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f600 : bv 32 := 0x0cc6ea63.
Lemma F_7f600 : fetch_word Asan.M.loaded_segments (0x7f650 : word) = Some W_7f600.
Proof. vm_refl. Qed.
Lemma D_7f600 : decode_any W_7f600 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f604 : bv 32 := 0xfbf60693.
Lemma F_7f604 : fetch_word Asan.M.loaded_segments (0x7f654 : word) = Some W_7f604.
Proof. vm_refl. Qed.
Lemma D_7f604 : decode_any W_7f604 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f608 : bv 32 := 0xfbf00713.
Lemma F_7f608 : fetch_word Asan.M.loaded_segments (0x7f658 : word) = Some W_7f608.
Proof. vm_refl. Qed.
Lemma D_7f608 : decode_any W_7f608 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f60c : bv 32 := 0x14d77863.
Lemma F_7f60c : fetch_word Asan.M.loaded_segments (0x7f65c : word) = Some W_7f60c.
Proof. vm_refl. Qed.
Lemma D_7f60c : decode_any W_7f60c = Some (Branch BC_GEU 14 13 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f610 : bv 32 := 0x000d7697.
Lemma F_7f610 : fetch_word Asan.M.loaded_segments (0x7f660 : word) = Some W_7f610.
Proof. vm_refl. Qed.
Lemma D_7f610 : decode_any W_7f610 = Some (Auipc 13 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f614 : bv 32 := 0x7386b683.
Lemma F_7f614 : fetch_word Asan.M.loaded_segments (0x7f664 : word) = Some W_7f614.
Proof. vm_refl. Qed.
Lemma D_7f614 : decode_any W_7f614 = Some (Load SZ8 true 13 13 1848, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f618 : bv 32 := 0x00c507b3.
Lemma F_7f618 : fetch_word Asan.M.loaded_segments (0x7f668 : word) = Some W_7f618.
Proof. vm_refl. Qed.
Lemma D_7f618 : decode_any W_7f618 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f61c : bv 32 := 0x0006b703.
Lemma F_7f61c : fetch_word Asan.M.loaded_segments (0x7f66c : word) = Some W_7f61c.
Proof. vm_refl. Qed.
Lemma D_7f61c : decode_any W_7f61c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f620 : bv 32 := 0x00355693.
Lemma F_7f620 : fetch_word Asan.M.loaded_segments (0x7f670 : word) = Some W_7f620.
Proof. vm_refl. Qed.
Lemma D_7f620 : decode_any W_7f620 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f624 : bv 32 := 0xfff78793.
Lemma F_7f624 : fetch_word Asan.M.loaded_segments (0x7f674 : word) = Some W_7f624.
Proof. vm_refl. Qed.
Lemma D_7f624 : decode_any W_7f624 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f628 : bv 32 := 0x0037d813.
Lemma F_7f628 : fetch_word Asan.M.loaded_segments (0x7f678 : word) = Some W_7f628.
Proof. vm_refl. Qed.
Lemma D_7f628 : decode_any W_7f628 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f62c : bv 32 := 0x00d706b3.
Lemma F_7f62c : fetch_word Asan.M.loaded_segments (0x7f67c : word) = Some W_7f62c.
Proof. vm_refl. Qed.
Lemma D_7f62c : decode_any W_7f62c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f630 : bv 32 := 0x01070733.
Lemma F_7f630 : fetch_word Asan.M.loaded_segments (0x7f680 : word) = Some W_7f630.
Proof. vm_refl. Qed.
Lemma D_7f630 : decode_any W_7f630 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f634 : bv 32 := 0xff86f813.
Lemma F_7f634 : fetch_word Asan.M.loaded_segments (0x7f684 : word) = Some W_7f634.
Proof. vm_refl. Qed.
Lemma D_7f634 : decode_any W_7f634 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f638 : bv 32 := 0xff877893.
Lemma F_7f638 : fetch_word Asan.M.loaded_segments (0x7f688 : word) = Some W_7f638.
Proof. vm_refl. Qed.
Lemma D_7f638 : decode_any W_7f638 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f63c : bv 32 := 0x00083803.
Lemma F_7f63c : fetch_word Asan.M.loaded_segments (0x7f68c : word) = Some W_7f63c.
Proof. vm_refl. Qed.
Lemma D_7f63c : decode_any W_7f63c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f640 : bv 32 := 0x0008b883.
Lemma F_7f640 : fetch_word Asan.M.loaded_segments (0x7f690 : word) = Some W_7f640.
Proof. vm_refl. Qed.
Lemma D_7f640 : decode_any W_7f640 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f644 : bv 32 := 0x0108e833.
Lemma F_7f644 : fetch_word Asan.M.loaded_segments (0x7f694 : word) = Some W_7f644.
Proof. vm_refl. Qed.
Lemma D_7f644 : decode_any W_7f644 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f648 : bv 32 := 0x10081e63.
Lemma F_7f648 : fetch_word Asan.M.loaded_segments (0x7f698 : word) = Some W_7f648.
Proof. vm_refl. Qed.
Lemma D_7f648 : decode_any W_7f648 = Some (Branch BC_NE 16 0 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f64c : bv 32 := 0x000d9697.
Lemma F_7f64c : fetch_word Asan.M.loaded_segments (0x7f69c : word) = Some W_7f64c.
Proof. vm_refl. Qed.
Lemma D_7f64c : decode_any W_7f64c = Some (Auipc 13 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f650 : bv 32 := 0x70c6b683.
Lemma F_7f650 : fetch_word Asan.M.loaded_segments (0x7f6a0 : word) = Some W_7f650.
Proof. vm_refl. Qed.
Lemma D_7f650 : decode_any W_7f650 = Some (Load SZ8 true 13 13 1804, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f654 : bv 32 := 0x000680e7.
Lemma F_7f654 : fetch_word Asan.M.loaded_segments (0x7f6a4 : word) = Some W_7f654.
Proof. vm_refl. Qed.
Lemma D_7f654 : decode_any W_7f654 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f658 : bv 32 := 0x07010113.
Lemma F_7f658 : fetch_word Asan.M.loaded_segments (0x7f6a8 : word) = Some W_7f658.
Proof. vm_refl. Qed.
Lemma D_7f658 : decode_any W_7f658 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f65c : bv 32 := 0x7e813083.
Lemma F_7f65c : fetch_word Asan.M.loaded_segments (0x7f6ac : word) = Some W_7f65c.
Proof. vm_refl. Qed.
Lemma D_7f65c : decode_any W_7f65c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f660 : bv 32 := 0x7e013403.
Lemma F_7f660 : fetch_word Asan.M.loaded_segments (0x7f6b0 : word) = Some W_7f660.
Proof. vm_refl. Qed.
Lemma D_7f660 : decode_any W_7f660 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f664 : bv 32 := 0x7d813483.
Lemma F_7f664 : fetch_word Asan.M.loaded_segments (0x7f6b4 : word) = Some W_7f664.
Proof. vm_refl. Qed.
Lemma D_7f664 : decode_any W_7f664 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f668 : bv 32 := 0x7d013903.
Lemma F_7f668 : fetch_word Asan.M.loaded_segments (0x7f6b8 : word) = Some W_7f668.
Proof. vm_refl. Qed.
Lemma D_7f668 : decode_any W_7f668 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f66c : bv 32 := 0x7c813983.
Lemma F_7f66c : fetch_word Asan.M.loaded_segments (0x7f6bc : word) = Some W_7f66c.
Proof. vm_refl. Qed.
Lemma D_7f66c : decode_any W_7f66c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f670 : bv 32 := 0x7c013a03.
Lemma F_7f670 : fetch_word Asan.M.loaded_segments (0x7f6c0 : word) = Some W_7f670.
Proof. vm_refl. Qed.
Lemma D_7f670 : decode_any W_7f670 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f674 : bv 32 := 0x7b813a83.
Lemma F_7f674 : fetch_word Asan.M.loaded_segments (0x7f6c4 : word) = Some W_7f674.
Proof. vm_refl. Qed.
Lemma D_7f674 : decode_any W_7f674 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f678 : bv 32 := 0x7b013b03.
Lemma F_7f678 : fetch_word Asan.M.loaded_segments (0x7f6c8 : word) = Some W_7f678.
Proof. vm_refl. Qed.
Lemma D_7f678 : decode_any W_7f678 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f67c : bv 32 := 0x7f010113.
Lemma F_7f67c : fetch_word Asan.M.loaded_segments (0x7f6cc : word) = Some W_7f67c.
Proof. vm_refl. Qed.
Lemma D_7f67c : decode_any W_7f67c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f680 : bv 32 := 0x00008067.
Lemma F_7f680 : fetch_word Asan.M.loaded_segments (0x7f6d0 : word) = Some W_7f680.
Proof. vm_refl. Qed.
Lemma D_7f680 : decode_any W_7f680 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f75c : bv 32 := 0x02061e63.
Lemma F_7f75c : fetch_word Asan.M.loaded_segments (0x7f7ac : word) = Some W_7f75c.
Proof. vm_refl. Qed.
Lemma D_7f75c : decode_any W_7f75c = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f760 : bv 32 := 0xeedff06f.
Lemma F_7f760 : fetch_word Asan.M.loaded_segments (0x7f7b0 : word) = Some W_7f760.
Proof. vm_refl. Qed.
Lemma D_7f760 : decode_any W_7f760 = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f764 : bv 32 := 0x00070803.
Lemma F_7f764 : fetch_word Asan.M.loaded_segments (0x7f7b4 : word) = Some W_7f764.
Proof. vm_refl. Qed.
Lemma D_7f764 : decode_any W_7f764 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f768 : bv 32 := 0x0077f793.
Lemma F_7f768 : fetch_word Asan.M.loaded_segments (0x7f7b8 : word) = Some W_7f768.
Proof. vm_refl. Qed.
Lemma D_7f768 : decode_any W_7f768 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f76c : bv 32 := 0x010038b3.
Lemma F_7f76c : fetch_word Asan.M.loaded_segments (0x7f7bc : word) = Some W_7f76c.
Proof. vm_refl. Qed.
Lemma D_7f76c : decode_any W_7f76c = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f770 : bv 32 := 0x0107a7b3.
Lemma F_7f770 : fetch_word Asan.M.loaded_segments (0x7f7c0 : word) = Some W_7f770.
Proof. vm_refl. Qed.
Lemma D_7f770 : decode_any W_7f770 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f774 : bv 32 := 0x0017c793.
Lemma F_7f774 : fetch_word Asan.M.loaded_segments (0x7f7c4 : word) = Some W_7f774.
Proof. vm_refl. Qed.
Lemma D_7f774 : decode_any W_7f774 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f778 : bv 32 := 0x00f8f7b3.
Lemma F_7f778 : fetch_word Asan.M.loaded_segments (0x7f7c8 : word) = Some W_7f778.
Proof. vm_refl. Qed.
Lemma D_7f778 : decode_any W_7f778 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f77c : bv 32 := 0x00e6fa63.
Lemma F_7f77c : fetch_word Asan.M.loaded_segments (0x7f7cc : word) = Some W_7f77c.
Proof. vm_refl. Qed.
Lemma D_7f77c : decode_any W_7f77c = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f780 : bv 32 := 0x0006c803.
Lemma F_7f780 : fetch_word Asan.M.loaded_segments (0x7f7d0 : word) = Some W_7f780.
Proof. vm_refl. Qed.
Lemma D_7f780 : decode_any W_7f780 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f784 : bv 32 := 0x00168693.
Lemma F_7f784 : fetch_word Asan.M.loaded_segments (0x7f7d4 : word) = Some W_7f784.
Proof. vm_refl. Qed.
Lemma D_7f784 : decode_any W_7f784 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f788 : bv 32 := 0x00f867b3.
Lemma F_7f788 : fetch_word Asan.M.loaded_segments (0x7f7d8 : word) = Some W_7f788.
Proof. vm_refl. Qed.
Lemma D_7f788 : decode_any W_7f788 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f78c : bv 32 := 0xfee69ae3.
Lemma F_7f78c : fetch_word Asan.M.loaded_segments (0x7f7dc : word) = Some W_7f78c.
Proof. vm_refl. Qed.
Lemma D_7f78c : decode_any W_7f78c = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f790 : bv 32 := 0x0ff7f693.
Lemma F_7f790 : fetch_word Asan.M.loaded_segments (0x7f7e0 : word) = Some W_7f790.
Proof. vm_refl. Qed.
Lemma D_7f790 : decode_any W_7f790 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f794 : bv 32 := 0xea068ce3.
Lemma F_7f794 : fetch_word Asan.M.loaded_segments (0x7f7e4 : word) = Some W_7f794.
Proof. vm_refl. Qed.
Lemma D_7f794 : decode_any W_7f794 = Some (Branch BC_EQ 13 0 7864, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f798 : bv 32 := 0x00050493.
Lemma F_7f798 : fetch_word Asan.M.loaded_segments (0x7f7e8 : word) = Some W_7f798.
Proof. vm_refl. Qed.
Lemma D_7f798 : decode_any W_7f798 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f79c : bv 32 := 0x00058b13.
Lemma F_7f79c : fetch_word Asan.M.loaded_segments (0x7f7ec : word) = Some W_7f79c.
Proof. vm_refl. Qed.
Lemma D_7f79c : decode_any W_7f79c = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7a0 : bv 32 := 0x00060593.
Lemma F_7f7a0 : fetch_word Asan.M.loaded_segments (0x7f7f0 : word) = Some W_7f7a0.
Proof. vm_refl. Qed.
Lemma D_7f7a0 : decode_any W_7f7a0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7a4 : bv 32 := 0x00060913.
Lemma F_7f7a4 : fetch_word Asan.M.loaded_segments (0x7f7f4 : word) = Some W_7f7a4.
Proof. vm_refl. Qed.
Lemma D_7f7a4 : decode_any W_7f7a4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7a8 : bv 32 := 0x3f1020ef.
Lemma F_7f7a8 : fetch_word Asan.M.loaded_segments (0x7f7f8 : word) = Some W_7f7a8.
Proof. vm_refl. Qed.
Lemma D_7f7a8 : decode_any W_7f7a8 = Some (Jal 1 11248, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7ac : bv 32 := 0x000b0593.
Lemma F_7f7ac : fetch_word Asan.M.loaded_segments (0x7f7fc : word) = Some W_7f7ac.
Proof. vm_refl. Qed.
Lemma D_7f7ac : decode_any W_7f7ac = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7b0 : bv 32 := 0x00090613.
Lemma F_7f7b0 : fetch_word Asan.M.loaded_segments (0x7f800 : word) = Some W_7f7b0.
Proof. vm_refl. Qed.
Lemma D_7f7b0 : decode_any W_7f7b0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7b4 : bv 32 := 0x00050993.
Lemma F_7f7b4 : fetch_word Asan.M.loaded_segments (0x7f804 : word) = Some W_7f7b4.
Proof. vm_refl. Qed.
Lemma D_7f7b4 : decode_any W_7f7b4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7b8 : bv 32 := 0x00048513.
Lemma F_7f7b8 : fetch_word Asan.M.loaded_segments (0x7f808 : word) = Some W_7f7b8.
Proof. vm_refl. Qed.
Lemma D_7f7b8 : decode_any W_7f7b8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f7bc : bv 32 := 0xe80988e3.
Lemma F_7f7bc : fetch_word Asan.M.loaded_segments (0x7f80c : word) = Some W_7f7bc.
Proof. vm_refl. Qed.
Lemma D_7f7bc : decode_any W_7f7bc = Some (Branch BC_EQ 19 0 7824, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8a8 : bv 32 := 0x81010113.
Lemma F_7f8a8 : fetch_word Asan.M.loaded_segments (0x7f8f8 : word) = Some W_7f8a8.
Proof. vm_refl. Qed.
Lemma D_7f8a8 : decode_any W_7f8a8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8ac : bv 32 := 0x7e113423.
Lemma F_7f8ac : fetch_word Asan.M.loaded_segments (0x7f8fc : word) = Some W_7f8ac.
Proof. vm_refl. Qed.
Lemma D_7f8ac : decode_any W_7f8ac = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8b0 : bv 32 := 0x7e813023.
Lemma F_7f8b0 : fetch_word Asan.M.loaded_segments (0x7f900 : word) = Some W_7f8b0.
Proof. vm_refl. Qed.
Lemma D_7f8b0 : decode_any W_7f8b0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8b4 : bv 32 := 0x7c913c23.
Lemma F_7f8b4 : fetch_word Asan.M.loaded_segments (0x7f904 : word) = Some W_7f8b4.
Proof. vm_refl. Qed.
Lemma D_7f8b4 : decode_any W_7f8b4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8b8 : bv 32 := 0x7d213823.
Lemma F_7f8b8 : fetch_word Asan.M.loaded_segments (0x7f908 : word) = Some W_7f8b8.
Proof. vm_refl. Qed.
Lemma D_7f8b8 : decode_any W_7f8b8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8bc : bv 32 := 0x7d313423.
Lemma F_7f8bc : fetch_word Asan.M.loaded_segments (0x7f90c : word) = Some W_7f8bc.
Proof. vm_refl. Qed.
Lemma D_7f8bc : decode_any W_7f8bc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8c0 : bv 32 := 0x7d413023.
Lemma F_7f8c0 : fetch_word Asan.M.loaded_segments (0x7f910 : word) = Some W_7f8c0.
Proof. vm_refl. Qed.
Lemma D_7f8c0 : decode_any W_7f8c0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8c4 : bv 32 := 0x7b513c23.
Lemma F_7f8c4 : fetch_word Asan.M.loaded_segments (0x7f914 : word) = Some W_7f8c4.
Proof. vm_refl. Qed.
Lemma D_7f8c4 : decode_any W_7f8c4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8c8 : bv 32 := 0x7b613823.
Lemma F_7f8c8 : fetch_word Asan.M.loaded_segments (0x7f918 : word) = Some W_7f8c8.
Proof. vm_refl. Qed.
Lemma D_7f8c8 : decode_any W_7f8c8 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8cc : bv 32 := 0x7b713423.
Lemma F_7f8cc : fetch_word Asan.M.loaded_segments (0x7f91c : word) = Some W_7f8cc.
Proof. vm_refl. Qed.
Lemma D_7f8cc : decode_any W_7f8cc = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8d0 : bv 32 := 0x7f010413.
Lemma F_7f8d0 : fetch_word Asan.M.loaded_segments (0x7f920 : word) = Some W_7f8d0.
Proof. vm_refl. Qed.
Lemma D_7f8d0 : decode_any W_7f8d0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8d4 : bv 32 := 0xf9010113.
Lemma F_7f8d4 : fetch_word Asan.M.loaded_segments (0x7f924 : word) = Some W_7f8d4.
Proof. vm_refl. Qed.
Lemma D_7f8d4 : decode_any W_7f8d4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8d8 : bv 32 := 0x000d8697.
Lemma F_7f8d8 : fetch_word Asan.M.loaded_segments (0x7f928 : word) = Some W_7f8d8.
Proof. vm_refl. Qed.
Lemma D_7f8d8 : decode_any W_7f8d8 = Some (Auipc 13 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8dc : bv 32 := 0xfd86b683.
Lemma F_7f8dc : fetch_word Asan.M.loaded_segments (0x7f92c : word) = Some W_7f8dc.
Proof. vm_refl. Qed.
Lemma D_7f8dc : decode_any W_7f8dc = Some (Load SZ8 true 13 13 4056, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8e0 : bv 32 := 0x0006c683.
Lemma F_7f8e0 : fetch_word Asan.M.loaded_segments (0x7f930 : word) = Some W_7f8e0.
Proof. vm_refl. Qed.
Lemma D_7f8e0 : decode_any W_7f8e0 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8e4 : bv 32 := 0x0a068463.
Lemma F_7f8e4 : fetch_word Asan.M.loaded_segments (0x7f934 : word) = Some W_7f8e4.
Proof. vm_refl. Qed.
Lemma D_7f8e4 : decode_any W_7f8e4 = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8e8 : bv 32 := 0xfff5c693.
Lemma F_7f8e8 : fetch_word Asan.M.loaded_segments (0x7f938 : word) = Some W_7f8e8.
Proof. vm_refl. Qed.
Lemma D_7f8e8 : decode_any W_7f8e8 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8ec : bv 32 := 0x80040a93.
Lemma F_7f8ec : fetch_word Asan.M.loaded_segments (0x7f93c : word) = Some W_7f8ec.
Proof. vm_refl. Qed.
Lemma D_7f8ec : decode_any W_7f8ec = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8f0 : bv 32 := 0xfa0a8a93.
Lemma F_7f8f0 : fetch_word Asan.M.loaded_segments (0x7f940 : word) = Some W_7f8f0.
Proof. vm_refl. Qed.
Lemma D_7f8f0 : decode_any W_7f8f0 = Some (OpImm ALU_ADD 21 21 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8f4 : bv 32 := 0x0cc6e663.
Lemma F_7f8f4 : fetch_word Asan.M.loaded_segments (0x7f944 : word) = Some W_7f8f4.
Proof. vm_refl. Qed.
Lemma D_7f8f4 : decode_any W_7f8f4 = Some (Branch BC_LTU 13 12 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8f8 : bv 32 := 0xfbf60a13.
Lemma F_7f8f8 : fetch_word Asan.M.loaded_segments (0x7f948 : word) = Some W_7f8f8.
Proof. vm_refl. Qed.
Lemma D_7f8f8 : decode_any W_7f8f8 = Some (OpImm ALU_ADD 20 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f8fc : bv 32 := 0xfbf00693.
Lemma F_7f8fc : fetch_word Asan.M.loaded_segments (0x7f94c : word) = Some W_7f8fc.
Proof. vm_refl. Qed.
Lemma D_7f8fc : decode_any W_7f8fc = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f900 : bv 32 := 0x1546f463.
Lemma F_7f900 : fetch_word Asan.M.loaded_segments (0x7f950 : word) = Some W_7f900.
Proof. vm_refl. Qed.
Lemma D_7f900 : decode_any W_7f900 = Some (Branch BC_GEU 13 20 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f904 : bv 32 := 0x000d7697.
Lemma F_7f904 : fetch_word Asan.M.loaded_segments (0x7f954 : word) = Some W_7f904.
Proof. vm_refl. Qed.
Lemma D_7f904 : decode_any W_7f904 = Some (Auipc 13 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f908 : bv 32 := 0x4446b683.
Lemma F_7f908 : fetch_word Asan.M.loaded_segments (0x7f958 : word) = Some W_7f908.
Proof. vm_refl. Qed.
Lemma D_7f908 : decode_any W_7f908 = Some (Load SZ8 true 13 13 1092, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f90c : bv 32 := 0x00c587b3.
Lemma F_7f90c : fetch_word Asan.M.loaded_segments (0x7f95c : word) = Some W_7f90c.
Proof. vm_refl. Qed.
Lemma D_7f90c : decode_any W_7f90c = Some (Op ALU_ADD 15 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f910 : bv 32 := 0x0006b703.
Lemma F_7f910 : fetch_word Asan.M.loaded_segments (0x7f960 : word) = Some W_7f910.
Proof. vm_refl. Qed.
Lemma D_7f910 : decode_any W_7f910 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f914 : bv 32 := 0x0035d693.
Lemma F_7f914 : fetch_word Asan.M.loaded_segments (0x7f964 : word) = Some W_7f914.
Proof. vm_refl. Qed.
Lemma D_7f914 : decode_any W_7f914 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f918 : bv 32 := 0xfff78793.
Lemma F_7f918 : fetch_word Asan.M.loaded_segments (0x7f968 : word) = Some W_7f918.
Proof. vm_refl. Qed.
Lemma D_7f918 : decode_any W_7f918 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f91c : bv 32 := 0x0037d813.
Lemma F_7f91c : fetch_word Asan.M.loaded_segments (0x7f96c : word) = Some W_7f91c.
Proof. vm_refl. Qed.
Lemma D_7f91c : decode_any W_7f91c = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f920 : bv 32 := 0x00d706b3.
Lemma F_7f920 : fetch_word Asan.M.loaded_segments (0x7f970 : word) = Some W_7f920.
Proof. vm_refl. Qed.
Lemma D_7f920 : decode_any W_7f920 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f924 : bv 32 := 0x01070733.
Lemma F_7f924 : fetch_word Asan.M.loaded_segments (0x7f974 : word) = Some W_7f924.
Proof. vm_refl. Qed.
Lemma D_7f924 : decode_any W_7f924 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f928 : bv 32 := 0xff86f813.
Lemma F_7f928 : fetch_word Asan.M.loaded_segments (0x7f978 : word) = Some W_7f928.
Proof. vm_refl. Qed.
Lemma D_7f928 : decode_any W_7f928 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f92c : bv 32 := 0xff877893.
Lemma F_7f92c : fetch_word Asan.M.loaded_segments (0x7f97c : word) = Some W_7f92c.
Proof. vm_refl. Qed.
Lemma D_7f92c : decode_any W_7f92c = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f930 : bv 32 := 0x00083803.
Lemma F_7f930 : fetch_word Asan.M.loaded_segments (0x7f980 : word) = Some W_7f930.
Proof. vm_refl. Qed.
Lemma D_7f930 : decode_any W_7f930 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f934 : bv 32 := 0x0008b883.
Lemma F_7f934 : fetch_word Asan.M.loaded_segments (0x7f984 : word) = Some W_7f934.
Proof. vm_refl. Qed.
Lemma D_7f934 : decode_any W_7f934 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f938 : bv 32 := 0x0108e833.
Lemma F_7f938 : fetch_word Asan.M.loaded_segments (0x7f988 : word) = Some W_7f938.
Proof. vm_refl. Qed.
Lemma D_7f938 : decode_any W_7f938 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f93c : bv 32 := 0x1a081063.
Lemma F_7f93c : fetch_word Asan.M.loaded_segments (0x7f98c : word) = Some W_7f93c.
Proof. vm_refl. Qed.
Lemma D_7f93c : decode_any W_7f93c = Some (Branch BC_NE 16 0 416, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f940 : bv 32 := 0xfff54693.
Lemma F_7f940 : fetch_word Asan.M.loaded_segments (0x7f990 : word) = Some W_7f940.
Proof. vm_refl. Qed.
Lemma D_7f940 : decode_any W_7f940 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f944 : bv 32 := 0x10c6e663.
Lemma F_7f944 : fetch_word Asan.M.loaded_segments (0x7f994 : word) = Some W_7f944.
Proof. vm_refl. Qed.
Lemma D_7f944 : decode_any W_7f944 = Some (Branch BC_LTU 13 12 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f948 : bv 32 := 0xfbf00693.
Lemma F_7f948 : fetch_word Asan.M.loaded_segments (0x7f998 : word) = Some W_7f948.
Proof. vm_refl. Qed.
Lemma D_7f948 : decode_any W_7f948 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f94c : bv 32 := 0x1946f463.
Lemma F_7f94c : fetch_word Asan.M.loaded_segments (0x7f99c : word) = Some W_7f94c.
Proof. vm_refl. Qed.
Lemma D_7f94c : decode_any W_7f94c = Some (Branch BC_GEU 13 20 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f950 : bv 32 := 0x000d7697.
Lemma F_7f950 : fetch_word Asan.M.loaded_segments (0x7f9a0 : word) = Some W_7f950.
Proof. vm_refl. Qed.
Lemma D_7f950 : decode_any W_7f950 = Some (Auipc 13 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f954 : bv 32 := 0x3f86b683.
Lemma F_7f954 : fetch_word Asan.M.loaded_segments (0x7f9a4 : word) = Some W_7f954.
Proof. vm_refl. Qed.
Lemma D_7f954 : decode_any W_7f954 = Some (Load SZ8 true 13 13 1016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f958 : bv 32 := 0x00c507b3.
Lemma F_7f958 : fetch_word Asan.M.loaded_segments (0x7f9a8 : word) = Some W_7f958.
Proof. vm_refl. Qed.
Lemma D_7f958 : decode_any W_7f958 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f95c : bv 32 := 0x0006b703.
Lemma F_7f95c : fetch_word Asan.M.loaded_segments (0x7f9ac : word) = Some W_7f95c.
Proof. vm_refl. Qed.
Lemma D_7f95c : decode_any W_7f95c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f960 : bv 32 := 0x00355693.
Lemma F_7f960 : fetch_word Asan.M.loaded_segments (0x7f9b0 : word) = Some W_7f960.
Proof. vm_refl. Qed.
Lemma D_7f960 : decode_any W_7f960 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f964 : bv 32 := 0xfff78793.
Lemma F_7f964 : fetch_word Asan.M.loaded_segments (0x7f9b4 : word) = Some W_7f964.
Proof. vm_refl. Qed.
Lemma D_7f964 : decode_any W_7f964 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f968 : bv 32 := 0x0037d813.
Lemma F_7f968 : fetch_word Asan.M.loaded_segments (0x7f9b8 : word) = Some W_7f968.
Proof. vm_refl. Qed.
Lemma D_7f968 : decode_any W_7f968 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f96c : bv 32 := 0x00d706b3.
Lemma F_7f96c : fetch_word Asan.M.loaded_segments (0x7f9bc : word) = Some W_7f96c.
Proof. vm_refl. Qed.
Lemma D_7f96c : decode_any W_7f96c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f970 : bv 32 := 0x01070733.
Lemma F_7f970 : fetch_word Asan.M.loaded_segments (0x7f9c0 : word) = Some W_7f970.
Proof. vm_refl. Qed.
Lemma D_7f970 : decode_any W_7f970 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f974 : bv 32 := 0xff86f813.
Lemma F_7f974 : fetch_word Asan.M.loaded_segments (0x7f9c4 : word) = Some W_7f974.
Proof. vm_refl. Qed.
Lemma D_7f974 : decode_any W_7f974 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f978 : bv 32 := 0xff877893.
Lemma F_7f978 : fetch_word Asan.M.loaded_segments (0x7f9c8 : word) = Some W_7f978.
Proof. vm_refl. Qed.
Lemma D_7f978 : decode_any W_7f978 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f97c : bv 32 := 0x00083803.
Lemma F_7f97c : fetch_word Asan.M.loaded_segments (0x7f9cc : word) = Some W_7f97c.
Proof. vm_refl. Qed.
Lemma D_7f97c : decode_any W_7f97c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f980 : bv 32 := 0x0008b883.
Lemma F_7f980 : fetch_word Asan.M.loaded_segments (0x7f9d0 : word) = Some W_7f980.
Proof. vm_refl. Qed.
Lemma D_7f980 : decode_any W_7f980 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f984 : bv 32 := 0x0108e833.
Lemma F_7f984 : fetch_word Asan.M.loaded_segments (0x7f9d4 : word) = Some W_7f984.
Proof. vm_refl. Qed.
Lemma D_7f984 : decode_any W_7f984 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f988 : bv 32 := 0x24081a63.
Lemma F_7f988 : fetch_word Asan.M.loaded_segments (0x7f9d8 : word) = Some W_7f988.
Proof. vm_refl. Qed.
Lemma D_7f988 : decode_any W_7f988 = Some (Branch BC_NE 16 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f98c : bv 32 := 0x155120ef.
Lemma F_7f98c : fetch_word Asan.M.loaded_segments (0x7f9dc : word) = Some W_7f98c.
Proof. vm_refl. Qed.
Lemma D_7f98c : decode_any W_7f98c = Some (Jal 1 76116, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f990 : bv 32 := 0x07010113.
Lemma F_7f990 : fetch_word Asan.M.loaded_segments (0x7f9e0 : word) = Some W_7f990.
Proof. vm_refl. Qed.
Lemma D_7f990 : decode_any W_7f990 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f994 : bv 32 := 0x7e813083.
Lemma F_7f994 : fetch_word Asan.M.loaded_segments (0x7f9e4 : word) = Some W_7f994.
Proof. vm_refl. Qed.
Lemma D_7f994 : decode_any W_7f994 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f998 : bv 32 := 0x7e013403.
Lemma F_7f998 : fetch_word Asan.M.loaded_segments (0x7f9e8 : word) = Some W_7f998.
Proof. vm_refl. Qed.
Lemma D_7f998 : decode_any W_7f998 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f99c : bv 32 := 0x7d813483.
Lemma F_7f99c : fetch_word Asan.M.loaded_segments (0x7f9ec : word) = Some W_7f99c.
Proof. vm_refl. Qed.
Lemma D_7f99c : decode_any W_7f99c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9a0 : bv 32 := 0x7d013903.
Lemma F_7f9a0 : fetch_word Asan.M.loaded_segments (0x7f9f0 : word) = Some W_7f9a0.
Proof. vm_refl. Qed.
Lemma D_7f9a0 : decode_any W_7f9a0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9a4 : bv 32 := 0x7c813983.
Lemma F_7f9a4 : fetch_word Asan.M.loaded_segments (0x7f9f4 : word) = Some W_7f9a4.
Proof. vm_refl. Qed.
Lemma D_7f9a4 : decode_any W_7f9a4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9a8 : bv 32 := 0x7c013a03.
Lemma F_7f9a8 : fetch_word Asan.M.loaded_segments (0x7f9f8 : word) = Some W_7f9a8.
Proof. vm_refl. Qed.
Lemma D_7f9a8 : decode_any W_7f9a8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9ac : bv 32 := 0x7b813a83.
Lemma F_7f9ac : fetch_word Asan.M.loaded_segments (0x7f9fc : word) = Some W_7f9ac.
Proof. vm_refl. Qed.
Lemma D_7f9ac : decode_any W_7f9ac = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9b0 : bv 32 := 0x7b013b03.
Lemma F_7f9b0 : fetch_word Asan.M.loaded_segments (0x7fa00 : word) = Some W_7f9b0.
Proof. vm_refl. Qed.
Lemma D_7f9b0 : decode_any W_7f9b0 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9b4 : bv 32 := 0x7a813b83.
Lemma F_7f9b4 : fetch_word Asan.M.loaded_segments (0x7fa04 : word) = Some W_7f9b4.
Proof. vm_refl. Qed.
Lemma D_7f9b4 : decode_any W_7f9b4 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9b8 : bv 32 := 0x7f010113.
Lemma F_7f9b8 : fetch_word Asan.M.loaded_segments (0x7fa08 : word) = Some W_7f9b8.
Proof. vm_refl. Qed.
Lemma D_7f9b8 : decode_any W_7f9b8 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7f9bc : bv 32 := 0x00008067.
Lemma F_7f9bc : fetch_word Asan.M.loaded_segments (0x7fa0c : word) = Some W_7f9bc.
Proof. vm_refl. Qed.
Lemma D_7f9bc : decode_any W_7f9bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa48 : bv 32 := 0x0c061463.
Lemma F_7fa48 : fetch_word Asan.M.loaded_segments (0x7fa98 : word) = Some W_7fa48.
Proof. vm_refl. Qed.
Lemma D_7fa48 : decode_any W_7fa48 = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fa4c : bv 32 := 0xef5ff06f.
Lemma F_7fa4c : fetch_word Asan.M.loaded_segments (0x7fa9c : word) = Some W_7fa4c.
Proof. vm_refl. Qed.
Lemma D_7fa4c : decode_any W_7fa4c = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fad4 : bv 32 := 0x12061e63.
Lemma F_7fad4 : fetch_word Asan.M.loaded_segments (0x7fb24 : word) = Some W_7fad4.
Proof. vm_refl. Qed.
Lemma D_7fad4 : decode_any W_7fad4 = Some (Branch BC_NE 12 0 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fad8 : bv 32 := 0xeb5ff06f.
Lemma F_7fad8 : fetch_word Asan.M.loaded_segments (0x7fb28 : word) = Some W_7fad8.
Proof. vm_refl. Qed.
Lemma D_7fad8 : decode_any W_7fad8 = Some (Jal 0 2096820, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fadc : bv 32 := 0x00070803.
Lemma F_7fadc : fetch_word Asan.M.loaded_segments (0x7fb2c : word) = Some W_7fadc.
Proof. vm_refl. Qed.
Lemma D_7fadc : decode_any W_7fadc = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fae0 : bv 32 := 0x0077f793.
Lemma F_7fae0 : fetch_word Asan.M.loaded_segments (0x7fb30 : word) = Some W_7fae0.
Proof. vm_refl. Qed.
Lemma D_7fae0 : decode_any W_7fae0 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fae4 : bv 32 := 0x010038b3.
Lemma F_7fae4 : fetch_word Asan.M.loaded_segments (0x7fb34 : word) = Some W_7fae4.
Proof. vm_refl. Qed.
Lemma D_7fae4 : decode_any W_7fae4 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fae8 : bv 32 := 0x0107a7b3.
Lemma F_7fae8 : fetch_word Asan.M.loaded_segments (0x7fb38 : word) = Some W_7fae8.
Proof. vm_refl. Qed.
Lemma D_7fae8 : decode_any W_7fae8 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faec : bv 32 := 0x0017c793.
Lemma F_7faec : fetch_word Asan.M.loaded_segments (0x7fb3c : word) = Some W_7faec.
Proof. vm_refl. Qed.
Lemma D_7faec : decode_any W_7faec = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faf0 : bv 32 := 0x00f8f7b3.
Lemma F_7faf0 : fetch_word Asan.M.loaded_segments (0x7fb40 : word) = Some W_7faf0.
Proof. vm_refl. Qed.
Lemma D_7faf0 : decode_any W_7faf0 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faf4 : bv 32 := 0x00e6fa63.
Lemma F_7faf4 : fetch_word Asan.M.loaded_segments (0x7fb44 : word) = Some W_7faf4.
Proof. vm_refl. Qed.
Lemma D_7faf4 : decode_any W_7faf4 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7faf8 : bv 32 := 0x0006c803.
Lemma F_7faf8 : fetch_word Asan.M.loaded_segments (0x7fb48 : word) = Some W_7faf8.
Proof. vm_refl. Qed.
Lemma D_7faf8 : decode_any W_7faf8 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fafc : bv 32 := 0x00168693.
Lemma F_7fafc : fetch_word Asan.M.loaded_segments (0x7fb4c : word) = Some W_7fafc.
Proof. vm_refl. Qed.
Lemma D_7fafc : decode_any W_7fafc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb00 : bv 32 := 0x00f867b3.
Lemma F_7fb00 : fetch_word Asan.M.loaded_segments (0x7fb50 : word) = Some W_7fb00.
Proof. vm_refl. Qed.
Lemma D_7fb00 : decode_any W_7fb00 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb04 : bv 32 := 0xfee69ae3.
Lemma F_7fb04 : fetch_word Asan.M.loaded_segments (0x7fb54 : word) = Some W_7fb04.
Proof. vm_refl. Qed.
Lemma D_7fb04 : decode_any W_7fb04 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb08 : bv 32 := 0x0ff7f693.
Lemma F_7fb08 : fetch_word Asan.M.loaded_segments (0x7fb58 : word) = Some W_7fb08.
Proof. vm_refl. Qed.
Lemma D_7fb08 : decode_any W_7fb08 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb0c : bv 32 := 0xe2068ae3.
Lemma F_7fb0c : fetch_word Asan.M.loaded_segments (0x7fb5c : word) = Some W_7fb0c.
Proof. vm_refl. Qed.
Lemma D_7fb0c : decode_any W_7fb0c = Some (Branch BC_EQ 13 0 7732, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb10 : bv 32 := 0x00050b13.
Lemma F_7fb10 : fetch_word Asan.M.loaded_segments (0x7fb60 : word) = Some W_7fb10.
Proof. vm_refl. Qed.
Lemma D_7fb10 : decode_any W_7fb10 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb14 : bv 32 := 0x00058513.
Lemma F_7fb14 : fetch_word Asan.M.loaded_segments (0x7fb64 : word) = Some W_7fb14.
Proof. vm_refl. Qed.
Lemma D_7fb14 : decode_any W_7fb14 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb18 : bv 32 := 0x00058b93.
Lemma F_7fb18 : fetch_word Asan.M.loaded_segments (0x7fb68 : word) = Some W_7fb18.
Proof. vm_refl. Qed.
Lemma D_7fb18 : decode_any W_7fb18 = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb1c : bv 32 := 0x00060593.
Lemma F_7fb1c : fetch_word Asan.M.loaded_segments (0x7fb6c : word) = Some W_7fb1c.
Proof. vm_refl. Qed.
Lemma D_7fb1c : decode_any W_7fb1c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb20 : bv 32 := 0x00060493.
Lemma F_7fb20 : fetch_word Asan.M.loaded_segments (0x7fb70 : word) = Some W_7fb20.
Proof. vm_refl. Qed.
Lemma D_7fb20 : decode_any W_7fb20 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb24 : bv 32 := 0x075020ef.
Lemma F_7fb24 : fetch_word Asan.M.loaded_segments (0x7fb74 : word) = Some W_7fb24.
Proof. vm_refl. Qed.
Lemma D_7fb24 : decode_any W_7fb24 = Some (Jal 1 10356, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb28 : bv 32 := 0x000b8593.
Lemma F_7fb28 : fetch_word Asan.M.loaded_segments (0x7fb78 : word) = Some W_7fb28.
Proof. vm_refl. Qed.
Lemma D_7fb28 : decode_any W_7fb28 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb2c : bv 32 := 0x00048613.
Lemma F_7fb2c : fetch_word Asan.M.loaded_segments (0x7fb7c : word) = Some W_7fb2c.
Proof. vm_refl. Qed.
Lemma D_7fb2c : decode_any W_7fb2c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb30 : bv 32 := 0x00050913.
Lemma F_7fb30 : fetch_word Asan.M.loaded_segments (0x7fb80 : word) = Some W_7fb30.
Proof. vm_refl. Qed.
Lemma D_7fb30 : decode_any W_7fb30 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb34 : bv 32 := 0x000b0513.
Lemma F_7fb34 : fetch_word Asan.M.loaded_segments (0x7fb84 : word) = Some W_7fb34.
Proof. vm_refl. Qed.
Lemma D_7fb34 : decode_any W_7fb34 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fb38 : bv 32 := 0xe00904e3.
Lemma F_7fb38 : fetch_word Asan.M.loaded_segments (0x7fb88 : word) = Some W_7fb38.
Proof. vm_refl. Qed.
Lemma D_7fb38 : decode_any W_7fb38 = Some (Branch BC_EQ 18 0 7688, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbdc : bv 32 := 0x00070803.
Lemma F_7fbdc : fetch_word Asan.M.loaded_segments (0x7fc2c : word) = Some W_7fbdc.
Proof. vm_refl. Qed.
Lemma D_7fbdc : decode_any W_7fbdc = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe0 : bv 32 := 0x0077f793.
Lemma F_7fbe0 : fetch_word Asan.M.loaded_segments (0x7fc30 : word) = Some W_7fbe0.
Proof. vm_refl. Qed.
Lemma D_7fbe0 : decode_any W_7fbe0 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe4 : bv 32 := 0x010038b3.
Lemma F_7fbe4 : fetch_word Asan.M.loaded_segments (0x7fc34 : word) = Some W_7fbe4.
Proof. vm_refl. Qed.
Lemma D_7fbe4 : decode_any W_7fbe4 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe8 : bv 32 := 0x0107a7b3.
Lemma F_7fbe8 : fetch_word Asan.M.loaded_segments (0x7fc38 : word) = Some W_7fbe8.
Proof. vm_refl. Qed.
Lemma D_7fbe8 : decode_any W_7fbe8 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbec : bv 32 := 0x0017c793.
Lemma F_7fbec : fetch_word Asan.M.loaded_segments (0x7fc3c : word) = Some W_7fbec.
Proof. vm_refl. Qed.
Lemma D_7fbec : decode_any W_7fbec = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf0 : bv 32 := 0x00f8f7b3.
Lemma F_7fbf0 : fetch_word Asan.M.loaded_segments (0x7fc40 : word) = Some W_7fbf0.
Proof. vm_refl. Qed.
Lemma D_7fbf0 : decode_any W_7fbf0 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf4 : bv 32 := 0x00e6fa63.
Lemma F_7fbf4 : fetch_word Asan.M.loaded_segments (0x7fc44 : word) = Some W_7fbf4.
Proof. vm_refl. Qed.
Lemma D_7fbf4 : decode_any W_7fbf4 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf8 : bv 32 := 0x0006c803.
Lemma F_7fbf8 : fetch_word Asan.M.loaded_segments (0x7fc48 : word) = Some W_7fbf8.
Proof. vm_refl. Qed.
Lemma D_7fbf8 : decode_any W_7fbf8 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbfc : bv 32 := 0x00168693.
Lemma F_7fbfc : fetch_word Asan.M.loaded_segments (0x7fc4c : word) = Some W_7fbfc.
Proof. vm_refl. Qed.
Lemma D_7fbfc : decode_any W_7fbfc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc00 : bv 32 := 0x00f867b3.
Lemma F_7fc00 : fetch_word Asan.M.loaded_segments (0x7fc50 : word) = Some W_7fc00.
Proof. vm_refl. Qed.
Lemma D_7fc00 : decode_any W_7fc00 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc04 : bv 32 := 0xfee69ae3.
Lemma F_7fc04 : fetch_word Asan.M.loaded_segments (0x7fc54 : word) = Some W_7fc04.
Proof. vm_refl. Qed.
Lemma D_7fc04 : decode_any W_7fc04 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc08 : bv 32 := 0x0ff7f693.
Lemma F_7fc08 : fetch_word Asan.M.loaded_segments (0x7fc58 : word) = Some W_7fc08.
Proof. vm_refl. Qed.
Lemma D_7fc08 : decode_any W_7fc08 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc0c : bv 32 := 0xd80680e3.
Lemma F_7fc0c : fetch_word Asan.M.loaded_segments (0x7fc5c : word) = Some W_7fc0c.
Proof. vm_refl. Qed.
Lemma D_7fc0c : decode_any W_7fc0c = Some (Branch BC_EQ 13 0 7552, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc10 : bv 32 := 0x00050493.
Lemma F_7fc10 : fetch_word Asan.M.loaded_segments (0x7fc60 : word) = Some W_7fc10.
Proof. vm_refl. Qed.
Lemma D_7fc10 : decode_any W_7fc10 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc14 : bv 32 := 0x00058b13.
Lemma F_7fc14 : fetch_word Asan.M.loaded_segments (0x7fc64 : word) = Some W_7fc14.
Proof. vm_refl. Qed.
Lemma D_7fc14 : decode_any W_7fc14 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc18 : bv 32 := 0x00060593.
Lemma F_7fc18 : fetch_word Asan.M.loaded_segments (0x7fc68 : word) = Some W_7fc18.
Proof. vm_refl. Qed.
Lemma D_7fc18 : decode_any W_7fc18 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc1c : bv 32 := 0x00060913.
Lemma F_7fc1c : fetch_word Asan.M.loaded_segments (0x7fc6c : word) = Some W_7fc1c.
Proof. vm_refl. Qed.
Lemma D_7fc1c : decode_any W_7fc1c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc20 : bv 32 := 0x778020ef.
Lemma F_7fc20 : fetch_word Asan.M.loaded_segments (0x7fc70 : word) = Some W_7fc20.
Proof. vm_refl. Qed.
Lemma D_7fc20 : decode_any W_7fc20 = Some (Jal 1 10104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc24 : bv 32 := 0x000b0593.
Lemma F_7fc24 : fetch_word Asan.M.loaded_segments (0x7fc74 : word) = Some W_7fc24.
Proof. vm_refl. Qed.
Lemma D_7fc24 : decode_any W_7fc24 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc28 : bv 32 := 0x00090613.
Lemma F_7fc28 : fetch_word Asan.M.loaded_segments (0x7fc78 : word) = Some W_7fc28.
Proof. vm_refl. Qed.
Lemma D_7fc28 : decode_any W_7fc28 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc2c : bv 32 := 0x00050993.
Lemma F_7fc2c : fetch_word Asan.M.loaded_segments (0x7fc7c : word) = Some W_7fc2c.
Proof. vm_refl. Qed.
Lemma D_7fc2c : decode_any W_7fc2c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc30 : bv 32 := 0x00048513.
Lemma F_7fc30 : fetch_word Asan.M.loaded_segments (0x7fc80 : word) = Some W_7fc30.
Proof. vm_refl. Qed.
Lemma D_7fc30 : decode_any W_7fc30 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc34 : bv 32 := 0xd4098ce3.
Lemma F_7fc34 : fetch_word Asan.M.loaded_segments (0x7fc84 : word) = Some W_7fc34.
Proof. vm_refl. Qed.
Lemma D_7fc34 : decode_any W_7fc34 = Some (Branch BC_EQ 19 0 7512, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd68 : bv 32 := 0x81010113.
Lemma F_7fd68 : fetch_word Asan.M.loaded_segments (0x7fdb8 : word) = Some W_7fd68.
Proof. vm_refl. Qed.
Lemma D_7fd68 : decode_any W_7fd68 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd6c : bv 32 := 0x7e113423.
Lemma F_7fd6c : fetch_word Asan.M.loaded_segments (0x7fdbc : word) = Some W_7fd6c.
Proof. vm_refl. Qed.
Lemma D_7fd6c : decode_any W_7fd6c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd70 : bv 32 := 0x7e813023.
Lemma F_7fd70 : fetch_word Asan.M.loaded_segments (0x7fdc0 : word) = Some W_7fd70.
Proof. vm_refl. Qed.
Lemma D_7fd70 : decode_any W_7fd70 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd74 : bv 32 := 0x7c913c23.
Lemma F_7fd74 : fetch_word Asan.M.loaded_segments (0x7fdc4 : word) = Some W_7fd74.
Proof. vm_refl. Qed.
Lemma D_7fd74 : decode_any W_7fd74 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd78 : bv 32 := 0x7d213823.
Lemma F_7fd78 : fetch_word Asan.M.loaded_segments (0x7fdc8 : word) = Some W_7fd78.
Proof. vm_refl. Qed.
Lemma D_7fd78 : decode_any W_7fd78 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd7c : bv 32 := 0x7d313423.
Lemma F_7fd7c : fetch_word Asan.M.loaded_segments (0x7fdcc : word) = Some W_7fd7c.
Proof. vm_refl. Qed.
Lemma D_7fd7c : decode_any W_7fd7c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd80 : bv 32 := 0x7d413023.
Lemma F_7fd80 : fetch_word Asan.M.loaded_segments (0x7fdd0 : word) = Some W_7fd80.
Proof. vm_refl. Qed.
Lemma D_7fd80 : decode_any W_7fd80 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd84 : bv 32 := 0x7b513c23.
Lemma F_7fd84 : fetch_word Asan.M.loaded_segments (0x7fdd4 : word) = Some W_7fd84.
Proof. vm_refl. Qed.
Lemma D_7fd84 : decode_any W_7fd84 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd88 : bv 32 := 0x7b613823.
Lemma F_7fd88 : fetch_word Asan.M.loaded_segments (0x7fdd8 : word) = Some W_7fd88.
Proof. vm_refl. Qed.
Lemma D_7fd88 : decode_any W_7fd88 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd8c : bv 32 := 0x7b713423.
Lemma F_7fd8c : fetch_word Asan.M.loaded_segments (0x7fddc : word) = Some W_7fd8c.
Proof. vm_refl. Qed.
Lemma D_7fd8c : decode_any W_7fd8c = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd90 : bv 32 := 0x7b813023.
Lemma F_7fd90 : fetch_word Asan.M.loaded_segments (0x7fde0 : word) = Some W_7fd90.
Proof. vm_refl. Qed.
Lemma D_7fd90 : decode_any W_7fd90 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd94 : bv 32 := 0x7f010413.
Lemma F_7fd94 : fetch_word Asan.M.loaded_segments (0x7fde4 : word) = Some W_7fd94.
Proof. vm_refl. Qed.
Lemma D_7fd94 : decode_any W_7fd94 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd98 : bv 32 := 0xf8010113.
Lemma F_7fd98 : fetch_word Asan.M.loaded_segments (0x7fde8 : word) = Some W_7fd98.
Proof. vm_refl. Qed.
Lemma D_7fd98 : decode_any W_7fd98 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fd9c : bv 32 := 0x000d8697.
Lemma F_7fd9c : fetch_word Asan.M.loaded_segments (0x7fdec : word) = Some W_7fd9c.
Proof. vm_refl. Qed.
Lemma D_7fd9c : decode_any W_7fd9c = Some (Auipc 13 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fda0 : bv 32 := 0xb146b683.
Lemma F_7fda0 : fetch_word Asan.M.loaded_segments (0x7fdf0 : word) = Some W_7fda0.
Proof. vm_refl. Qed.
Lemma D_7fda0 : decode_any W_7fda0 = Some (Load SZ8 true 13 13 2836, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fda4 : bv 32 := 0x0006c683.
Lemma F_7fda4 : fetch_word Asan.M.loaded_segments (0x7fdf4 : word) = Some W_7fda4.
Proof. vm_refl. Qed.
Lemma D_7fda4 : decode_any W_7fda4 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fda8 : bv 32 := 0x0e068a63.
Lemma F_7fda8 : fetch_word Asan.M.loaded_segments (0x7fdf8 : word) = Some W_7fda8.
Proof. vm_refl. Qed.
Lemma D_7fda8 : decode_any W_7fda8 = Some (Branch BC_EQ 13 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdac : bv 32 := 0x80040a93.
Lemma F_7fdac : fetch_word Asan.M.loaded_segments (0x7fdfc : word) = Some W_7fdac.
Proof. vm_refl. Qed.
Lemma D_7fdac : decode_any W_7fdac = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdb0 : bv 32 := 0xf98a8a93.
Lemma F_7fdb0 : fetch_word Asan.M.loaded_segments (0x7fe00 : word) = Some W_7fdb0.
Proof. vm_refl. Qed.
Lemma D_7fdb0 : decode_any W_7fdb0 = Some (OpImm ALU_ADD 21 21 3992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdb4 : bv 32 := 0x00c589b3.
Lemma F_7fdb4 : fetch_word Asan.M.loaded_segments (0x7fe04 : word) = Some W_7fdb4.
Proof. vm_refl. Qed.
Lemma D_7fdb4 : decode_any W_7fdb4 = Some (Op ALU_ADD 19 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdb8 : bv 32 := 0x00c50a33.
Lemma F_7fdb8 : fetch_word Asan.M.loaded_segments (0x7fe08 : word) = Some W_7fdb8.
Proof. vm_refl. Qed.
Lemma D_7fdb8 : decode_any W_7fdb8 = Some (Op ALU_ADD 20 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdbc : bv 32 := 0x00b50663.
Lemma F_7fdbc : fetch_word Asan.M.loaded_segments (0x7fe0c : word) = Some W_7fdbc.
Proof. vm_refl. Qed.
Lemma D_7fdbc : decode_any W_7fdbc = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdc0 : bv 32 := 0x0145f463.
Lemma F_7fdc0 : fetch_word Asan.M.loaded_segments (0x7fe10 : word) = Some W_7fdc0.
Proof. vm_refl. Qed.
Lemma D_7fdc0 : decode_any W_7fdc0 = Some (Branch BC_GEU 11 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdc4 : bv 32 := 0x1b356e63.
Lemma F_7fdc4 : fetch_word Asan.M.loaded_segments (0x7fe14 : word) = Some W_7fdc4.
Proof. vm_refl. Qed.
Lemma D_7fdc4 : decode_any W_7fdc4 = Some (Branch BC_LTU 10 19 444, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdc8 : bv 32 := 0xfff5c693.
Lemma F_7fdc8 : fetch_word Asan.M.loaded_segments (0x7fe18 : word) = Some W_7fdc8.
Proof. vm_refl. Qed.
Lemma D_7fdc8 : decode_any W_7fdc8 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdcc : bv 32 := 0x26c6e863.
Lemma F_7fdcc : fetch_word Asan.M.loaded_segments (0x7fe1c : word) = Some W_7fdcc.
Proof. vm_refl. Qed.
Lemma D_7fdcc : decode_any W_7fdcc = Some (Branch BC_LTU 13 12 624, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdd0 : bv 32 := 0xfbf60b13.
Lemma F_7fdd0 : fetch_word Asan.M.loaded_segments (0x7fe20 : word) = Some W_7fdd0.
Proof. vm_refl. Qed.
Lemma D_7fdd0 : decode_any W_7fdd0 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdd4 : bv 32 := 0xfbf00693.
Lemma F_7fdd4 : fetch_word Asan.M.loaded_segments (0x7fe24 : word) = Some W_7fdd4.
Proof. vm_refl. Qed.
Lemma D_7fdd4 : decode_any W_7fdd4 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdd8 : bv 32 := 0x2f66f663.
Lemma F_7fdd8 : fetch_word Asan.M.loaded_segments (0x7fe28 : word) = Some W_7fdd8.
Proof. vm_refl. Qed.
Lemma D_7fdd8 : decode_any W_7fdd8 = Some (Branch BC_GEU 13 22 748, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fddc : bv 32 := 0x000d7697.
Lemma F_7fddc : fetch_word Asan.M.loaded_segments (0x7fe2c : word) = Some W_7fddc.
Proof. vm_refl. Qed.
Lemma D_7fddc : decode_any W_7fddc = Some (Auipc 13 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fde0 : bv 32 := 0xf6c6b683.
Lemma F_7fde0 : fetch_word Asan.M.loaded_segments (0x7fe30 : word) = Some W_7fde0.
Proof. vm_refl. Qed.
Lemma D_7fde0 : decode_any W_7fde0 = Some (Load SZ8 true 13 13 3948, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fde4 : bv 32 := 0x0006b703.
Lemma F_7fde4 : fetch_word Asan.M.loaded_segments (0x7fe34 : word) = Some W_7fde4.
Proof. vm_refl. Qed.
Lemma D_7fde4 : decode_any W_7fde4 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fde8 : bv 32 := 0xfff98993.
Lemma F_7fde8 : fetch_word Asan.M.loaded_segments (0x7fe38 : word) = Some W_7fde8.
Proof. vm_refl. Qed.
Lemma D_7fde8 : decode_any W_7fde8 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdec : bv 32 := 0x0035d693.
Lemma F_7fdec : fetch_word Asan.M.loaded_segments (0x7fe3c : word) = Some W_7fdec.
Proof. vm_refl. Qed.
Lemma D_7fdec : decode_any W_7fdec = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdf0 : bv 32 := 0x0039d793.
Lemma F_7fdf0 : fetch_word Asan.M.loaded_segments (0x7fe40 : word) = Some W_7fdf0.
Proof. vm_refl. Qed.
Lemma D_7fdf0 : decode_any W_7fdf0 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdf4 : bv 32 := 0x00d706b3.
Lemma F_7fdf4 : fetch_word Asan.M.loaded_segments (0x7fe44 : word) = Some W_7fdf4.
Proof. vm_refl. Qed.
Lemma D_7fdf4 : decode_any W_7fdf4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdf8 : bv 32 := 0x00f70733.
Lemma F_7fdf8 : fetch_word Asan.M.loaded_segments (0x7fe48 : word) = Some W_7fdf8.
Proof. vm_refl. Qed.
Lemma D_7fdf8 : decode_any W_7fdf8 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fdfc : bv 32 := 0xff86f793.
Lemma F_7fdfc : fetch_word Asan.M.loaded_segments (0x7fe4c : word) = Some W_7fdfc.
Proof. vm_refl. Qed.
Lemma D_7fdfc : decode_any W_7fdfc = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe00 : bv 32 := 0xff877813.
Lemma F_7fe00 : fetch_word Asan.M.loaded_segments (0x7fe50 : word) = Some W_7fe00.
Proof. vm_refl. Qed.
Lemma D_7fe00 : decode_any W_7fe00 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe04 : bv 32 := 0x0007b783.
Lemma F_7fe04 : fetch_word Asan.M.loaded_segments (0x7fe54 : word) = Some W_7fe04.
Proof. vm_refl. Qed.
Lemma D_7fe04 : decode_any W_7fe04 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe08 : bv 32 := 0x00083803.
Lemma F_7fe08 : fetch_word Asan.M.loaded_segments (0x7fe58 : word) = Some W_7fe08.
Proof. vm_refl. Qed.
Lemma D_7fe08 : decode_any W_7fe08 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe0c : bv 32 := 0x00f867b3.
Lemma F_7fe0c : fetch_word Asan.M.loaded_segments (0x7fe5c : word) = Some W_7fe0c.
Proof. vm_refl. Qed.
Lemma D_7fe0c : decode_any W_7fe0c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe10 : bv 32 := 0x2a079e63.
Lemma F_7fe10 : fetch_word Asan.M.loaded_segments (0x7fe60 : word) = Some W_7fe10.
Proof. vm_refl. Qed.
Lemma D_7fe10 : decode_any W_7fe10 = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe14 : bv 32 := 0xfff54693.
Lemma F_7fe14 : fetch_word Asan.M.loaded_segments (0x7fe64 : word) = Some W_7fe14.
Proof. vm_refl. Qed.
Lemma D_7fe14 : decode_any W_7fe14 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe18 : bv 32 := 0x0cc6ee63.
Lemma F_7fe18 : fetch_word Asan.M.loaded_segments (0x7fe68 : word) = Some W_7fe18.
Proof. vm_refl. Qed.
Lemma D_7fe18 : decode_any W_7fe18 = Some (Branch BC_LTU 13 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe1c : bv 32 := 0xfbf00693.
Lemma F_7fe1c : fetch_word Asan.M.loaded_segments (0x7fe6c : word) = Some W_7fe1c.
Proof. vm_refl. Qed.
Lemma D_7fe1c : decode_any W_7fe1c = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe20 : bv 32 := 0x1566fc63.
Lemma F_7fe20 : fetch_word Asan.M.loaded_segments (0x7fe70 : word) = Some W_7fe20.
Proof. vm_refl. Qed.
Lemma D_7fe20 : decode_any W_7fe20 = Some (Branch BC_GEU 13 22 344, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe24 : bv 32 := 0x000d7697.
Lemma F_7fe24 : fetch_word Asan.M.loaded_segments (0x7fe74 : word) = Some W_7fe24.
Proof. vm_refl. Qed.
Lemma D_7fe24 : decode_any W_7fe24 = Some (Auipc 13 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe28 : bv 32 := 0xf246b683.
Lemma F_7fe28 : fetch_word Asan.M.loaded_segments (0x7fe78 : word) = Some W_7fe28.
Proof. vm_refl. Qed.
Lemma D_7fe28 : decode_any W_7fe28 = Some (Load SZ8 true 13 13 3876, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe2c : bv 32 := 0x0006b703.
Lemma F_7fe2c : fetch_word Asan.M.loaded_segments (0x7fe7c : word) = Some W_7fe2c.
Proof. vm_refl. Qed.
Lemma D_7fe2c : decode_any W_7fe2c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe30 : bv 32 := 0xfffa0a13.
Lemma F_7fe30 : fetch_word Asan.M.loaded_segments (0x7fe80 : word) = Some W_7fe30.
Proof. vm_refl. Qed.
Lemma D_7fe30 : decode_any W_7fe30 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe34 : bv 32 := 0x00355693.
Lemma F_7fe34 : fetch_word Asan.M.loaded_segments (0x7fe84 : word) = Some W_7fe34.
Proof. vm_refl. Qed.
Lemma D_7fe34 : decode_any W_7fe34 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe38 : bv 32 := 0x003a5793.
Lemma F_7fe38 : fetch_word Asan.M.loaded_segments (0x7fe88 : word) = Some W_7fe38.
Proof. vm_refl. Qed.
Lemma D_7fe38 : decode_any W_7fe38 = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe3c : bv 32 := 0x00d706b3.
Lemma F_7fe3c : fetch_word Asan.M.loaded_segments (0x7fe8c : word) = Some W_7fe3c.
Proof. vm_refl. Qed.
Lemma D_7fe3c : decode_any W_7fe3c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe40 : bv 32 := 0x00f70733.
Lemma F_7fe40 : fetch_word Asan.M.loaded_segments (0x7fe90 : word) = Some W_7fe40.
Proof. vm_refl. Qed.
Lemma D_7fe40 : decode_any W_7fe40 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe44 : bv 32 := 0xff86f793.
Lemma F_7fe44 : fetch_word Asan.M.loaded_segments (0x7fe94 : word) = Some W_7fe44.
Proof. vm_refl. Qed.
Lemma D_7fe44 : decode_any W_7fe44 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe48 : bv 32 := 0xff877813.
Lemma F_7fe48 : fetch_word Asan.M.loaded_segments (0x7fe98 : word) = Some W_7fe48.
Proof. vm_refl. Qed.
Lemma D_7fe48 : decode_any W_7fe48 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe4c : bv 32 := 0x0007b783.
Lemma F_7fe4c : fetch_word Asan.M.loaded_segments (0x7fe9c : word) = Some W_7fe4c.
Proof. vm_refl. Qed.
Lemma D_7fe4c : decode_any W_7fe4c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe50 : bv 32 := 0x00083803.
Lemma F_7fe50 : fetch_word Asan.M.loaded_segments (0x7fea0 : word) = Some W_7fe50.
Proof. vm_refl. Qed.
Lemma D_7fe50 : decode_any W_7fe50 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe54 : bv 32 := 0x00f867b3.
Lemma F_7fe54 : fetch_word Asan.M.loaded_segments (0x7fea4 : word) = Some W_7fe54.
Proof. vm_refl. Qed.
Lemma D_7fe54 : decode_any W_7fe54 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe58 : bv 32 := 0x36079a63.
Lemma F_7fe58 : fetch_word Asan.M.loaded_segments (0x7fea8 : word) = Some W_7fe58.
Proof. vm_refl. Qed.
Lemma D_7fe58 : decode_any W_7fe58 = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe5c : bv 32 := 0x000d9697.
Lemma F_7fe5c : fetch_word Asan.M.loaded_segments (0x7feac : word) = Some W_7fe5c.
Proof. vm_refl. Qed.
Lemma D_7fe5c : decode_any W_7fe5c = Some (Auipc 13 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe60 : bv 32 := 0xef46b683.
Lemma F_7fe60 : fetch_word Asan.M.loaded_segments (0x7feb0 : word) = Some W_7fe60.
Proof. vm_refl. Qed.
Lemma D_7fe60 : decode_any W_7fe60 = Some (Load SZ8 true 13 13 3828, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe64 : bv 32 := 0x000680e7.
Lemma F_7fe64 : fetch_word Asan.M.loaded_segments (0x7feb4 : word) = Some W_7fe64.
Proof. vm_refl. Qed.
Lemma D_7fe64 : decode_any W_7fe64 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe68 : bv 32 := 0x08010113.
Lemma F_7fe68 : fetch_word Asan.M.loaded_segments (0x7feb8 : word) = Some W_7fe68.
Proof. vm_refl. Qed.
Lemma D_7fe68 : decode_any W_7fe68 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe6c : bv 32 := 0x7e813083.
Lemma F_7fe6c : fetch_word Asan.M.loaded_segments (0x7febc : word) = Some W_7fe6c.
Proof. vm_refl. Qed.
Lemma D_7fe6c : decode_any W_7fe6c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe70 : bv 32 := 0x7e013403.
Lemma F_7fe70 : fetch_word Asan.M.loaded_segments (0x7fec0 : word) = Some W_7fe70.
Proof. vm_refl. Qed.
Lemma D_7fe70 : decode_any W_7fe70 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe74 : bv 32 := 0x7d813483.
Lemma F_7fe74 : fetch_word Asan.M.loaded_segments (0x7fec4 : word) = Some W_7fe74.
Proof. vm_refl. Qed.
Lemma D_7fe74 : decode_any W_7fe74 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe78 : bv 32 := 0x7d013903.
Lemma F_7fe78 : fetch_word Asan.M.loaded_segments (0x7fec8 : word) = Some W_7fe78.
Proof. vm_refl. Qed.
Lemma D_7fe78 : decode_any W_7fe78 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe7c : bv 32 := 0x7c813983.
Lemma F_7fe7c : fetch_word Asan.M.loaded_segments (0x7fecc : word) = Some W_7fe7c.
Proof. vm_refl. Qed.
Lemma D_7fe7c : decode_any W_7fe7c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe80 : bv 32 := 0x7c013a03.
Lemma F_7fe80 : fetch_word Asan.M.loaded_segments (0x7fed0 : word) = Some W_7fe80.
Proof. vm_refl. Qed.
Lemma D_7fe80 : decode_any W_7fe80 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe84 : bv 32 := 0x7b813a83.
Lemma F_7fe84 : fetch_word Asan.M.loaded_segments (0x7fed4 : word) = Some W_7fe84.
Proof. vm_refl. Qed.
Lemma D_7fe84 : decode_any W_7fe84 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe88 : bv 32 := 0x7b013b03.
Lemma F_7fe88 : fetch_word Asan.M.loaded_segments (0x7fed8 : word) = Some W_7fe88.
Proof. vm_refl. Qed.
Lemma D_7fe88 : decode_any W_7fe88 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe8c : bv 32 := 0x7a813b83.
Lemma F_7fe8c : fetch_word Asan.M.loaded_segments (0x7fedc : word) = Some W_7fe8c.
Proof. vm_refl. Qed.
Lemma D_7fe8c : decode_any W_7fe8c = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe90 : bv 32 := 0x7a013c03.
Lemma F_7fe90 : fetch_word Asan.M.loaded_segments (0x7fee0 : word) = Some W_7fe90.
Proof. vm_refl. Qed.
Lemma D_7fe90 : decode_any W_7fe90 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe94 : bv 32 := 0x7f010113.
Lemma F_7fe94 : fetch_word Asan.M.loaded_segments (0x7fee4 : word) = Some W_7fe94.
Proof. vm_refl. Qed.
Lemma D_7fe94 : decode_any W_7fe94 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe98 : bv 32 := 0x00008067.
Lemma F_7fe98 : fetch_word Asan.M.loaded_segments (0x7fee8 : word) = Some W_7fe98.
Proof. vm_refl. Qed.
Lemma D_7fe98 : decode_any W_7fe98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff78 : bv 32 := 0x28061463.
Lemma F_7ff78 : fetch_word Asan.M.loaded_segments (0x7ffc8 : word) = Some W_7ff78.
Proof. vm_refl. Qed.
Lemma D_7ff78 : decode_any W_7ff78 = Some (Branch BC_NE 12 0 648, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff7c : bv 32 := 0xee1ff06f.
Lemma F_7ff7c : fetch_word Asan.M.loaded_segments (0x7ffcc : word) = Some W_7ff7c.
Proof. vm_refl. Qed.
Lemma D_7ff7c : decode_any W_7ff7c = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c4 : bv 32 := 0x02061e63.
Lemma F_800c4 : fetch_word Asan.M.loaded_segments (0x80114 : word) = Some W_800c4.
Proof. vm_refl. Qed.
Lemma D_800c4 : decode_any W_800c4 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c8 : bv 32 := 0xd4dff06f.
Lemma F_800c8 : fetch_word Asan.M.loaded_segments (0x80118 : word) = Some W_800c8.
Proof. vm_refl. Qed.
Lemma D_800c8 : decode_any W_800c8 = Some (Jal 0 2096460, 4%Z).
Proof. vm_refl. Qed.

Definition W_800cc : bv 32 := 0x00070783.
Lemma F_800cc : fetch_word Asan.M.loaded_segments (0x8011c : word) = Some W_800cc.
Proof. vm_refl. Qed.
Lemma D_800cc : decode_any W_800cc = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d0 : bv 32 := 0x0079f813.
Lemma F_800d0 : fetch_word Asan.M.loaded_segments (0x80120 : word) = Some W_800d0.
Proof. vm_refl. Qed.
Lemma D_800d0 : decode_any W_800d0 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d4 : bv 32 := 0x00f038b3.
Lemma F_800d4 : fetch_word Asan.M.loaded_segments (0x80124 : word) = Some W_800d4.
Proof. vm_refl. Qed.
Lemma D_800d4 : decode_any W_800d4 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d8 : bv 32 := 0x00f827b3.
Lemma F_800d8 : fetch_word Asan.M.loaded_segments (0x80128 : word) = Some W_800d8.
Proof. vm_refl. Qed.
Lemma D_800d8 : decode_any W_800d8 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_800dc : bv 32 := 0x0017c793.
Lemma F_800dc : fetch_word Asan.M.loaded_segments (0x8012c : word) = Some W_800dc.
Proof. vm_refl. Qed.
Lemma D_800dc : decode_any W_800dc = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e0 : bv 32 := 0x00f8f7b3.
Lemma F_800e0 : fetch_word Asan.M.loaded_segments (0x80130 : word) = Some W_800e0.
Proof. vm_refl. Qed.
Lemma D_800e0 : decode_any W_800e0 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e4 : bv 32 := 0x00e6fa63.
Lemma F_800e4 : fetch_word Asan.M.loaded_segments (0x80134 : word) = Some W_800e4.
Proof. vm_refl. Qed.
Lemma D_800e4 : decode_any W_800e4 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e8 : bv 32 := 0x0006c803.
Lemma F_800e8 : fetch_word Asan.M.loaded_segments (0x80138 : word) = Some W_800e8.
Proof. vm_refl. Qed.
Lemma D_800e8 : decode_any W_800e8 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800ec : bv 32 := 0x00168693.
Lemma F_800ec : fetch_word Asan.M.loaded_segments (0x8013c : word) = Some W_800ec.
Proof. vm_refl. Qed.
Lemma D_800ec : decode_any W_800ec = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f0 : bv 32 := 0x00f867b3.
Lemma F_800f0 : fetch_word Asan.M.loaded_segments (0x80140 : word) = Some W_800f0.
Proof. vm_refl. Qed.
Lemma D_800f0 : decode_any W_800f0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f4 : bv 32 := 0xfee69ae3.
Lemma F_800f4 : fetch_word Asan.M.loaded_segments (0x80144 : word) = Some W_800f4.
Proof. vm_refl. Qed.
Lemma D_800f4 : decode_any W_800f4 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f8 : bv 32 := 0x0ff7f693.
Lemma F_800f8 : fetch_word Asan.M.loaded_segments (0x80148 : word) = Some W_800f8.
Proof. vm_refl. Qed.
Lemma D_800f8 : decode_any W_800f8 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_800fc : bv 32 := 0xd0068ce3.
Lemma F_800fc : fetch_word Asan.M.loaded_segments (0x8014c : word) = Some W_800fc.
Proof. vm_refl. Qed.
Lemma D_800fc : decode_any W_800fc = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

Definition W_80100 : bv 32 := 0x00050b93.
Lemma F_80100 : fetch_word Asan.M.loaded_segments (0x80150 : word) = Some W_80100.
Proof. vm_refl. Qed.
Lemma D_80100 : decode_any W_80100 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80104 : bv 32 := 0x00058513.
Lemma F_80104 : fetch_word Asan.M.loaded_segments (0x80154 : word) = Some W_80104.
Proof. vm_refl. Qed.
Lemma D_80104 : decode_any W_80104 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80108 : bv 32 := 0x00058c13.
Lemma F_80108 : fetch_word Asan.M.loaded_segments (0x80158 : word) = Some W_80108.
Proof. vm_refl. Qed.
Lemma D_80108 : decode_any W_80108 = Some (OpImm ALU_ADD 24 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8010c : bv 32 := 0x00060593.
Lemma F_8010c : fetch_word Asan.M.loaded_segments (0x8015c : word) = Some W_8010c.
Proof. vm_refl. Qed.
Lemma D_8010c : decode_any W_8010c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80110 : bv 32 := 0x00060493.
Lemma F_80110 : fetch_word Asan.M.loaded_segments (0x80160 : word) = Some W_80110.
Proof. vm_refl. Qed.
Lemma D_80110 : decode_any W_80110 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80114 : bv 32 := 0x284020ef.
Lemma F_80114 : fetch_word Asan.M.loaded_segments (0x80164 : word) = Some W_80114.
Proof. vm_refl. Qed.
Lemma D_80114 : decode_any W_80114 = Some (Jal 1 8836, 4%Z).
Proof. vm_refl. Qed.

Definition W_80118 : bv 32 := 0x000c0593.
Lemma F_80118 : fetch_word Asan.M.loaded_segments (0x80168 : word) = Some W_80118.
Proof. vm_refl. Qed.
Lemma D_80118 : decode_any W_80118 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8011c : bv 32 := 0x00048613.
Lemma F_8011c : fetch_word Asan.M.loaded_segments (0x8016c : word) = Some W_8011c.
Proof. vm_refl. Qed.
Lemma D_8011c : decode_any W_8011c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80120 : bv 32 := 0x00050913.
Lemma F_80120 : fetch_word Asan.M.loaded_segments (0x80170 : word) = Some W_80120.
Proof. vm_refl. Qed.
Lemma D_80120 : decode_any W_80120 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80124 : bv 32 := 0x000b8513.
Lemma F_80124 : fetch_word Asan.M.loaded_segments (0x80174 : word) = Some W_80124.
Proof. vm_refl. Qed.
Lemma D_80124 : decode_any W_80124 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80128 : bv 32 := 0xce0906e3.
Lemma F_80128 : fetch_word Asan.M.loaded_segments (0x80178 : word) = Some W_80128.
Proof. vm_refl. Qed.
Lemma D_80128 : decode_any W_80128 = Some (Branch BC_EQ 18 0 7404, 4%Z).
Proof. vm_refl. Qed.

Definition W_801cc : bv 32 := 0x00070783.
Lemma F_801cc : fetch_word Asan.M.loaded_segments (0x8021c : word) = Some W_801cc.
Proof. vm_refl. Qed.
Lemma D_801cc : decode_any W_801cc = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801d0 : bv 32 := 0x007a7813.
Lemma F_801d0 : fetch_word Asan.M.loaded_segments (0x80220 : word) = Some W_801d0.
Proof. vm_refl. Qed.
Lemma D_801d0 : decode_any W_801d0 = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_801d4 : bv 32 := 0x00f038b3.
Lemma F_801d4 : fetch_word Asan.M.loaded_segments (0x80224 : word) = Some W_801d4.
Proof. vm_refl. Qed.
Lemma D_801d4 : decode_any W_801d4 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_801d8 : bv 32 := 0x00f827b3.
Lemma F_801d8 : fetch_word Asan.M.loaded_segments (0x80228 : word) = Some W_801d8.
Proof. vm_refl. Qed.
Lemma D_801d8 : decode_any W_801d8 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_801dc : bv 32 := 0x0017c793.
Lemma F_801dc : fetch_word Asan.M.loaded_segments (0x8022c : word) = Some W_801dc.
Proof. vm_refl. Qed.
Lemma D_801dc : decode_any W_801dc = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_801e0 : bv 32 := 0x00f8f7b3.
Lemma F_801e0 : fetch_word Asan.M.loaded_segments (0x80230 : word) = Some W_801e0.
Proof. vm_refl. Qed.
Lemma D_801e0 : decode_any W_801e0 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_801e4 : bv 32 := 0x00e6fa63.
Lemma F_801e4 : fetch_word Asan.M.loaded_segments (0x80234 : word) = Some W_801e4.
Proof. vm_refl. Qed.
Lemma D_801e4 : decode_any W_801e4 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_801e8 : bv 32 := 0x0006c803.
Lemma F_801e8 : fetch_word Asan.M.loaded_segments (0x80238 : word) = Some W_801e8.
Proof. vm_refl. Qed.
Lemma D_801e8 : decode_any W_801e8 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801ec : bv 32 := 0x00168693.
Lemma F_801ec : fetch_word Asan.M.loaded_segments (0x8023c : word) = Some W_801ec.
Proof. vm_refl. Qed.
Lemma D_801ec : decode_any W_801ec = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_801f0 : bv 32 := 0x00f867b3.
Lemma F_801f0 : fetch_word Asan.M.loaded_segments (0x80240 : word) = Some W_801f0.
Proof. vm_refl. Qed.
Lemma D_801f0 : decode_any W_801f0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_801f4 : bv 32 := 0xfee69ae3.
Lemma F_801f4 : fetch_word Asan.M.loaded_segments (0x80244 : word) = Some W_801f4.
Proof. vm_refl. Qed.
Lemma D_801f4 : decode_any W_801f4 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_801f8 : bv 32 := 0x0ff7f693.
Lemma F_801f8 : fetch_word Asan.M.loaded_segments (0x80248 : word) = Some W_801f8.
Proof. vm_refl. Qed.
Lemma D_801f8 : decode_any W_801f8 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_801fc : bv 32 := 0xc60680e3.
Lemma F_801fc : fetch_word Asan.M.loaded_segments (0x8024c : word) = Some W_801fc.
Proof. vm_refl. Qed.
Lemma D_801fc : decode_any W_801fc = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.

Definition W_80200 : bv 32 := 0x00050493.
Lemma F_80200 : fetch_word Asan.M.loaded_segments (0x80250 : word) = Some W_80200.
Proof. vm_refl. Qed.
Lemma D_80200 : decode_any W_80200 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80204 : bv 32 := 0x00058b13.
Lemma F_80204 : fetch_word Asan.M.loaded_segments (0x80254 : word) = Some W_80204.
Proof. vm_refl. Qed.
Lemma D_80204 : decode_any W_80204 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80208 : bv 32 := 0x00060593.
Lemma F_80208 : fetch_word Asan.M.loaded_segments (0x80258 : word) = Some W_80208.
Proof. vm_refl. Qed.
Lemma D_80208 : decode_any W_80208 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8020c : bv 32 := 0x00060913.
Lemma F_8020c : fetch_word Asan.M.loaded_segments (0x8025c : word) = Some W_8020c.
Proof. vm_refl. Qed.
Lemma D_8020c : decode_any W_8020c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80210 : bv 32 := 0x188020ef.
Lemma F_80210 : fetch_word Asan.M.loaded_segments (0x80260 : word) = Some W_80210.
Proof. vm_refl. Qed.
Lemma D_80210 : decode_any W_80210 = Some (Jal 1 8584, 4%Z).
Proof. vm_refl. Qed.

Definition W_80214 : bv 32 := 0x000b0593.
Lemma F_80214 : fetch_word Asan.M.loaded_segments (0x80264 : word) = Some W_80214.
Proof. vm_refl. Qed.
Lemma D_80214 : decode_any W_80214 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80218 : bv 32 := 0x00090613.
Lemma F_80218 : fetch_word Asan.M.loaded_segments (0x80268 : word) = Some W_80218.
Proof. vm_refl. Qed.
Lemma D_80218 : decode_any W_80218 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8021c : bv 32 := 0x00050993.
Lemma F_8021c : fetch_word Asan.M.loaded_segments (0x8026c : word) = Some W_8021c.
Proof. vm_refl. Qed.
Lemma D_8021c : decode_any W_8021c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80220 : bv 32 := 0x00048513.
Lemma F_80220 : fetch_word Asan.M.loaded_segments (0x80270 : word) = Some W_80220.
Proof. vm_refl. Qed.
Lemma D_80220 : decode_any W_80220 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80224 : bv 32 := 0xc2098ce3.
Lemma F_80224 : fetch_word Asan.M.loaded_segments (0x80274 : word) = Some W_80224.
Proof. vm_refl. Qed.
Lemma D_80224 : decode_any W_80224 = Some (Branch BC_EQ 19 0 7224, 4%Z).
Proof. vm_refl. Qed.
