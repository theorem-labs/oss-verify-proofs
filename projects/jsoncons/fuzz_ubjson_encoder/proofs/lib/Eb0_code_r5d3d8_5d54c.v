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

Definition W_5ebec : bv 32 := 0xfe010113.
Lemma F_5ebec : fetch_word AsanUbsan.M.loaded_segments (0x5ec3c : word) = Some W_5ebec.
Proof. vm_refl. Qed.
Lemma D_5ebec : decode_any W_5ebec = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf0 : bv 32 := 0x00113c23.
Lemma F_5ebf0 : fetch_word AsanUbsan.M.loaded_segments (0x5ec40 : word) = Some W_5ebf0.
Proof. vm_refl. Qed.
Lemma D_5ebf0 : decode_any W_5ebf0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf4 : bv 32 := 0x00813823.
Lemma F_5ebf4 : fetch_word AsanUbsan.M.loaded_segments (0x5ec44 : word) = Some W_5ebf4.
Proof. vm_refl. Qed.
Lemma D_5ebf4 : decode_any W_5ebf4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf8 : bv 32 := 0x00913423.
Lemma F_5ebf8 : fetch_word AsanUbsan.M.loaded_segments (0x5ec48 : word) = Some W_5ebf8.
Proof. vm_refl. Qed.
Lemma D_5ebf8 : decode_any W_5ebf8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebfc : bv 32 := 0x01213023.
Lemma F_5ebfc : fetch_word AsanUbsan.M.loaded_segments (0x5ec4c : word) = Some W_5ebfc.
Proof. vm_refl. Qed.
Lemma D_5ebfc : decode_any W_5ebfc = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec00 : bv 32 := 0x02010413.
Lemma F_5ec00 : fetch_word AsanUbsan.M.loaded_segments (0x5ec50 : word) = Some W_5ec00.
Proof. vm_refl. Qed.
Lemma D_5ec00 : decode_any W_5ec00 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec04 : bv 32 := 0x000e0517.
Lemma F_5ec04 : fetch_word AsanUbsan.M.loaded_segments (0x5ec54 : word) = Some W_5ec04.
Proof. vm_refl. Qed.
Lemma D_5ec04 : decode_any W_5ec04 = Some (Auipc 10 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec08 : bv 32 := 0xa6c50513.
Lemma F_5ec08 : fetch_word AsanUbsan.M.loaded_segments (0x5ec58 : word) = Some W_5ec08.
Proof. vm_refl. Qed.
Lemma D_5ec08 : decode_any W_5ec08 = Some (OpImm ALU_ADD 10 10 2668, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec0c : bv 32 := 0x141050ef.
Lemma F_5ec0c : fetch_word AsanUbsan.M.loaded_segments (0x5ec5c : word) = Some W_5ec0c.
Proof. vm_refl. Qed.
Lemma D_5ec0c : decode_any W_5ec0c = Some (Jal 1 22848, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec10 : bv 32 := 0x00053483.
Lemma F_5ec10 : fetch_word AsanUbsan.M.loaded_segments (0x5ec60 : word) = Some W_5ec10.
Proof. vm_refl. Qed.
Lemma D_5ec10 : decode_any W_5ec10 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec14 : bv 32 := 0x08048063.
Lemma F_5ec14 : fetch_word AsanUbsan.M.loaded_segments (0x5ec64 : word) = Some W_5ec14.
Proof. vm_refl. Qed.
Lemma D_5ec14 : decode_any W_5ec14 = Some (Branch BC_EQ 9 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec18 : bv 32 := 0x0604c503.
Lemma F_5ec18 : fetch_word AsanUbsan.M.loaded_segments (0x5ec68 : word) = Some W_5ec18.
Proof. vm_refl. Qed.
Lemma D_5ec18 : decode_any W_5ec18 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec1c : bv 32 := 0x0584b903.
Lemma F_5ec1c : fetch_word AsanUbsan.M.loaded_segments (0x5ec6c : word) = Some W_5ec1c.
Proof. vm_refl. Qed.
Lemma D_5ec1c : decode_any W_5ec1c = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec20 : bv 32 := 0x00050863.
Lemma F_5ec20 : fetch_word AsanUbsan.M.loaded_segments (0x5ec70 : word) = Some W_5ec20.
Proof. vm_refl. Qed.
Lemma D_5ec20 : decode_any W_5ec20 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec24 : bv 32 := 0x00048513.
Lemma F_5ec24 : fetch_word AsanUbsan.M.loaded_segments (0x5ec74 : word) = Some W_5ec24.
Proof. vm_refl. Qed.
Lemma D_5ec24 : decode_any W_5ec24 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec28 : bv 32 := 0x00040593.
Lemma F_5ec28 : fetch_word AsanUbsan.M.loaded_segments (0x5ec78 : word) = Some W_5ec28.
Proof. vm_refl. Qed.
Lemma D_5ec28 : decode_any W_5ec28 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec2c : bv 32 := 0xb75ff0ef.
Lemma F_5ec2c : fetch_word AsanUbsan.M.loaded_segments (0x5ec7c : word) = Some W_5ec2c.
Proof. vm_refl. Qed.
Lemma D_5ec2c : decode_any W_5ec2c = Some (Jal 1 2095988, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec30 : bv 32 := 0xffa90593.
Lemma F_5ec30 : fetch_word AsanUbsan.M.loaded_segments (0x5ec80 : word) = Some W_5ec30.
Proof. vm_refl. Qed.
Lemma D_5ec30 : decode_any W_5ec30 = Some (OpImm ALU_ADD 11 18 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec34 : bv 32 := 0x00100513.
Lemma F_5ec34 : fetch_word AsanUbsan.M.loaded_segments (0x5ec84 : word) = Some W_5ec34.
Proof. vm_refl. Qed.
Lemma D_5ec34 : decode_any W_5ec34 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec38 : bv 32 := 0x00b51533.
Lemma F_5ec38 : fetch_word AsanUbsan.M.loaded_segments (0x5ec88 : word) = Some W_5ec38.
Proof. vm_refl. Qed.
Lemma D_5ec38 : decode_any W_5ec38 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec3c : bv 32 := 0x0005061b.
Lemma F_5ec3c : fetch_word AsanUbsan.M.loaded_segments (0x5ec8c : word) = Some W_5ec3c.
Proof. vm_refl. Qed.
Lemma D_5ec3c : decode_any W_5ec3c = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec40 : bv 32 := 0x06c05a63.
Lemma F_5ec40 : fetch_word AsanUbsan.M.loaded_segments (0x5ec90 : word) = Some W_5ec40.
Proof. vm_refl. Qed.
Lemma D_5ec40 : decode_any W_5ec40 = Some (Branch BC_GE 0 12 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec44 : bv 32 := 0x000016b7.
Lemma F_5ec44 : fetch_word AsanUbsan.M.loaded_segments (0x5ec94 : word) = Some W_5ec44.
Proof. vm_refl. Qed.
Lemma D_5ec44 : decode_any W_5ec44 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec48 : bv 32 := 0xfff00713.
Lemma F_5ec48 : fetch_word AsanUbsan.M.loaded_segments (0x5ec98 : word) = Some W_5ec48.
Proof. vm_refl. Qed.
Lemma D_5ec48 : decode_any W_5ec48 = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec4c : bv 32 := 0x0004b603.
Lemma F_5ec4c : fetch_word AsanUbsan.M.loaded_segments (0x5ec9c : word) = Some W_5ec4c.
Proof. vm_refl. Qed.
Lemma D_5ec4c : decode_any W_5ec4c = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec50 : bv 32 := 0x00b71733.
Lemma F_5ec50 : fetch_word AsanUbsan.M.loaded_segments (0x5eca0 : word) = Some W_5ec50.
Proof. vm_refl. Qed.
Lemma D_5ec50 : decode_any W_5ec50 = Some (Op ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec54 : bv 32 := 0xfff50793.
Lemma F_5ec54 : fetch_word AsanUbsan.M.loaded_segments (0x5eca4 : word) = Some W_5ec54.
Proof. vm_refl. Qed.
Lemma D_5ec54 : decode_any W_5ec54 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec58 : bv 32 := 0x00d485b3.
Lemma F_5ec58 : fetch_word AsanUbsan.M.loaded_segments (0x5eca8 : word) = Some W_5ec58.
Proof. vm_refl. Qed.
Lemma D_5ec58 : decode_any W_5ec58 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec5c : bv 32 := 0xfff74693.
Lemma F_5ec5c : fetch_word AsanUbsan.M.loaded_segments (0x5ecac : word) = Some W_5ec5c.
Proof. vm_refl. Qed.
Lemma D_5ec5c : decode_any W_5ec5c = Some (OpImm ALU_XOR 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec60 : bv 32 := 0x02079793.
Lemma F_5ec60 : fetch_word AsanUbsan.M.loaded_segments (0x5ecb0 : word) = Some W_5ec60.
Proof. vm_refl. Qed.
Lemma D_5ec60 : decode_any W_5ec60 = Some (ShiftImm ALU_SLL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec64 : bv 32 := 0x0207d793.
Lemma F_5ec64 : fetch_word AsanUbsan.M.loaded_segments (0x5ecb4 : word) = Some W_5ec64.
Proof. vm_refl. Qed.
Lemma D_5ec64 : decode_any W_5ec64 = Some (ShiftImm ALU_SRL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec68 : bv 32 := 0x00f60733.
Lemma F_5ec68 : fetch_word AsanUbsan.M.loaded_segments (0x5ecb8 : word) = Some W_5ec68.
Proof. vm_refl. Qed.
Lemma D_5ec68 : decode_any W_5ec68 = Some (Op ALU_ADD 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec6c : bv 32 := 0x00170713.
Lemma F_5ec6c : fetch_word AsanUbsan.M.loaded_segments (0x5ecbc : word) = Some W_5ec6c.
Proof. vm_refl. Qed.
Lemma D_5ec6c : decode_any W_5ec6c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec70 : bv 32 := 0x00d67833.
Lemma F_5ec70 : fetch_word AsanUbsan.M.loaded_segments (0x5ecc0 : word) = Some W_5ec70.
Proof. vm_refl. Qed.
Lemma D_5ec70 : decode_any W_5ec70 = Some (Op ALU_AND 16 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec74 : bv 32 := 0x010587b3.
Lemma F_5ec74 : fetch_word AsanUbsan.M.loaded_segments (0x5ecc4 : word) = Some W_5ec74.
Proof. vm_refl. Qed.
Lemma D_5ec74 : decode_any W_5ec74 = Some (Op ALU_ADD 15 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec78 : bv 32 := 0x0007c883.
Lemma F_5ec78 : fetch_word AsanUbsan.M.loaded_segments (0x5ecc8 : word) = Some W_5ec78.
Proof. vm_refl. Qed.
Lemma D_5ec78 : decode_any W_5ec78 = Some (Load SZ1 false 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec7c : bv 32 := 0x06088663.
Lemma F_5ec7c : fetch_word AsanUbsan.M.loaded_segments (0x5eccc : word) = Some W_5ec7c.
Proof. vm_refl. Qed.
Lemma D_5ec7c : decode_any W_5ec7c = Some (Branch BC_EQ 17 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec80 : bv 32 := 0xfff5051b.
Lemma F_5ec80 : fetch_word AsanUbsan.M.loaded_segments (0x5ecd0 : word) = Some W_5ec80.
Proof. vm_refl. Qed.
Lemma D_5ec80 : decode_any W_5ec80 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec84 : bv 32 := 0x00160613.
Lemma F_5ec84 : fetch_word AsanUbsan.M.loaded_segments (0x5ecd4 : word) = Some W_5ec84.
Proof. vm_refl. Qed.
Lemma D_5ec84 : decode_any W_5ec84 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec88 : bv 32 := 0xfe0514e3.
Lemma F_5ec88 : fetch_word AsanUbsan.M.loaded_segments (0x5ecd8 : word) = Some W_5ec88.
Proof. vm_refl. Qed.
Lemma D_5ec88 : decode_any W_5ec88 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec8c : bv 32 := 0x00e4b023.
Lemma F_5ec8c : fetch_word AsanUbsan.M.loaded_segments (0x5ecdc : word) = Some W_5ec8c.
Proof. vm_refl. Qed.
Lemma D_5ec8c : decode_any W_5ec8c = Some (Store SZ8 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec90 : bv 32 := 0x0400006f.
Lemma F_5ec90 : fetch_word AsanUbsan.M.loaded_segments (0x5ece0 : word) = Some W_5ec90.
Proof. vm_refl. Qed.
Lemma D_5ec90 : decode_any W_5ec90 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec94 : bv 32 := 0x000df517.
Lemma F_5ec94 : fetch_word AsanUbsan.M.loaded_segments (0x5ece4 : word) = Some W_5ec94.
Proof. vm_refl. Qed.
Lemma D_5ec94 : decode_any W_5ec94 = Some (Auipc 10 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec98 : bv 32 := 0xc3c53503.
Lemma F_5ec98 : fetch_word AsanUbsan.M.loaded_segments (0x5ece8 : word) = Some W_5ec98.
Proof. vm_refl. Qed.
Lemma D_5ec98 : decode_any W_5ec98 = Some (Load SZ8 true 10 10 3132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec9c : bv 32 := 0x00052503.
Lemma F_5ec9c : fetch_word AsanUbsan.M.loaded_segments (0x5ecec : word) = Some W_5ec9c.
Proof. vm_refl. Qed.
Lemma D_5ec9c : decode_any W_5ec9c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca0 : bv 32 := 0x02050863.
Lemma F_5eca0 : fetch_word AsanUbsan.M.loaded_segments (0x5ecf0 : word) = Some W_5eca0.
Proof. vm_refl. Qed.
Lemma D_5eca0 : decode_any W_5eca0 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca4 : bv 32 := 0x59d250ef.
Lemma F_5eca4 : fetch_word AsanUbsan.M.loaded_segments (0x5ecf4 : word) = Some W_5eca4.
Proof. vm_refl. Qed.
Lemma D_5eca4 : decode_any W_5eca4 = Some (Jal 1 155036, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca8 : bv 32 := 0x02050463.
Lemma F_5eca8 : fetch_word AsanUbsan.M.loaded_segments (0x5ecf8 : word) = Some W_5eca8.
Proof. vm_refl. Qed.
Lemma D_5eca8 : decode_any W_5eca8 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecac : bv 32 := 0x02850583.
Lemma F_5ecac : fetch_word AsanUbsan.M.loaded_segments (0x5ecfc : word) = Some W_5ecac.
Proof. vm_refl. Qed.
Lemma D_5ecac : decode_any W_5ecac = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb0 : bv 32 := 0x08058a63.
Lemma F_5ecb0 : fetch_word AsanUbsan.M.loaded_segments (0x5ed00 : word) = Some W_5ecb0.
Proof. vm_refl. Qed.
Lemma D_5ecb0 : decode_any W_5ecb0 = Some (Branch BC_EQ 11 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb4 : bv 32 := 0x00000513.
Lemma F_5ecb4 : fetch_word AsanUbsan.M.loaded_segments (0x5ed04 : word) = Some W_5ecb4.
Proof. vm_refl. Qed.
Lemma D_5ecb4 : decode_any W_5ecb4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb8 : bv 32 := 0x01813083.
Lemma F_5ecb8 : fetch_word AsanUbsan.M.loaded_segments (0x5ed08 : word) = Some W_5ecb8.
Proof. vm_refl. Qed.
Lemma D_5ecb8 : decode_any W_5ecb8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecbc : bv 32 := 0x01013403.
Lemma F_5ecbc : fetch_word AsanUbsan.M.loaded_segments (0x5ed0c : word) = Some W_5ecbc.
Proof. vm_refl. Qed.
Lemma D_5ecbc : decode_any W_5ecbc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecc0 : bv 32 := 0x00813483.
Lemma F_5ecc0 : fetch_word AsanUbsan.M.loaded_segments (0x5ed10 : word) = Some W_5ecc0.
Proof. vm_refl. Qed.
Lemma D_5ecc0 : decode_any W_5ecc0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecc4 : bv 32 := 0x00013903.
Lemma F_5ecc4 : fetch_word AsanUbsan.M.loaded_segments (0x5ed14 : word) = Some W_5ecc4.
Proof. vm_refl. Qed.
Lemma D_5ecc4 : decode_any W_5ecc4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecc8 : bv 32 := 0x02010113.
Lemma F_5ecc8 : fetch_word AsanUbsan.M.loaded_segments (0x5ed18 : word) = Some W_5ecc8.
Proof. vm_refl. Qed.
Lemma D_5ecc8 : decode_any W_5ecc8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eccc : bv 32 := 0x00008067.
Lemma F_5eccc : fetch_word AsanUbsan.M.loaded_segments (0x5ed1c : word) = Some W_5eccc.
Proof. vm_refl. Qed.
Lemma D_5eccc : decode_any W_5eccc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecd0 : bv 32 := 0x01813083.
Lemma F_5ecd0 : fetch_word AsanUbsan.M.loaded_segments (0x5ed20 : word) = Some W_5ecd0.
Proof. vm_refl. Qed.
Lemma D_5ecd0 : decode_any W_5ecd0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecd4 : bv 32 := 0x01013403.
Lemma F_5ecd4 : fetch_word AsanUbsan.M.loaded_segments (0x5ed24 : word) = Some W_5ecd4.
Proof. vm_refl. Qed.
Lemma D_5ecd4 : decode_any W_5ecd4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecd8 : bv 32 := 0x00813483.
Lemma F_5ecd8 : fetch_word AsanUbsan.M.loaded_segments (0x5ed28 : word) = Some W_5ecd8.
Proof. vm_refl. Qed.
Lemma D_5ecd8 : decode_any W_5ecd8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecdc : bv 32 := 0x00013903.
Lemma F_5ecdc : fetch_word AsanUbsan.M.loaded_segments (0x5ed2c : word) = Some W_5ecdc.
Proof. vm_refl. Qed.
Lemma D_5ecdc : decode_any W_5ecdc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ece0 : bv 32 := 0x02010113.
Lemma F_5ece0 : fetch_word AsanUbsan.M.loaded_segments (0x5ed30 : word) = Some W_5ece0.
Proof. vm_refl. Qed.
Lemma D_5ece0 : decode_any W_5ece0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ece4 : bv 32 := 0x00008067.
Lemma F_5ece4 : fetch_word AsanUbsan.M.loaded_segments (0x5ed34 : word) = Some W_5ece4.
Proof. vm_refl. Qed.
Lemma D_5ece4 : decode_any W_5ece4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ece8 : bv 32 := 0x00160613.
Lemma F_5ece8 : fetch_word AsanUbsan.M.loaded_segments (0x5ed38 : word) = Some W_5ece8.
Proof. vm_refl. Qed.
Lemma D_5ece8 : decode_any W_5ece8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecec : bv 32 := 0x00100513.
Lemma F_5ecec : fetch_word AsanUbsan.M.loaded_segments (0x5ed3c : word) = Some W_5ecec.
Proof. vm_refl. Qed.
Lemma D_5ecec : decode_any W_5ecec = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecf0 : bv 32 := 0xffb90913.
Lemma F_5ecf0 : fetch_word AsanUbsan.M.loaded_segments (0x5ed40 : word) = Some W_5ecf0.
Proof. vm_refl. Qed.
Lemma D_5ecf0 : decode_any W_5ecf0 = Some (OpImm ALU_ADD 18 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecf4 : bv 32 := 0x00681813.
Lemma F_5ecf4 : fetch_word AsanUbsan.M.loaded_segments (0x5ed44 : word) = Some W_5ecf4.
Proof. vm_refl. Qed.
Lemma D_5ecf4 : decode_any W_5ecf4 = Some (ShiftImm ALU_SLL 16 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecf8 : bv 32 := 0x00c4b023.
Lemma F_5ecf8 : fetch_word AsanUbsan.M.loaded_segments (0x5ed48 : word) = Some W_5ecf8.
Proof. vm_refl. Qed.
Lemma D_5ecf8 : decode_any W_5ecf8 = Some (Store SZ8 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecfc : bv 32 := 0x00a78023.
Lemma F_5ecfc : fetch_word AsanUbsan.M.loaded_segments (0x5ed4c : word) = Some W_5ecfc.
Proof. vm_refl. Qed.
Lemma D_5ecfc : decode_any W_5ecfc = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed00 : bv 32 := 0x01251533.
Lemma F_5ed00 : fetch_word AsanUbsan.M.loaded_segments (0x5ed50 : word) = Some W_5ed00.
Proof. vm_refl. Qed.
Lemma D_5ed00 : decode_any W_5ed00 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed04 : bv 32 := 0x00a58533.
Lemma F_5ed04 : fetch_word AsanUbsan.M.loaded_segments (0x5ed54 : word) = Some W_5ed04.
Proof. vm_refl. Qed.
Lemma D_5ed04 : decode_any W_5ed04 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed08 : bv 32 := 0x010504b3.
Lemma F_5ed08 : fetch_word AsanUbsan.M.loaded_segments (0x5ed58 : word) = Some W_5ed08.
Proof. vm_refl. Qed.
Lemma D_5ed08 : decode_any W_5ed08 = Some (Op ALU_ADD 9 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed0c : bv 32 := 0x0084bc23.
Lemma F_5ed0c : fetch_word AsanUbsan.M.loaded_segments (0x5ed5c : word) = Some W_5ed0c.
Proof. vm_refl. Qed.
Lemma D_5ed0c : decode_any W_5ed0c = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed10 : bv 32 := 0x02f4bc23.
Lemma F_5ed10 : fetch_word AsanUbsan.M.loaded_segments (0x5ed60 : word) = Some W_5ed10.
Proof. vm_refl. Qed.
Lemma D_5ed10 : decode_any W_5ed10 = Some (Store SZ8 9 15 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed14 : bv 32 := 0x00048513.
Lemma F_5ed14 : fetch_word AsanUbsan.M.loaded_segments (0x5ed64 : word) = Some W_5ed14.
Proof. vm_refl. Qed.
Lemma D_5ed14 : decode_any W_5ed14 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed18 : bv 32 := 0x7e0000ef.
Lemma F_5ed18 : fetch_word AsanUbsan.M.loaded_segments (0x5ed68 : word) = Some W_5ed18.
Proof. vm_refl. Qed.
Lemma D_5ed18 : decode_any W_5ed18 = Some (Jal 1 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed1c : bv 32 := 0x00050593.
Lemma F_5ed1c : fetch_word AsanUbsan.M.loaded_segments (0x5ed6c : word) = Some W_5ed1c.
Proof. vm_refl. Qed.
Lemma D_5ed1c : decode_any W_5ed1c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed20 : bv 32 := 0x00048513.
Lemma F_5ed20 : fetch_word AsanUbsan.M.loaded_segments (0x5ed70 : word) = Some W_5ed20.
Proof. vm_refl. Qed.
Lemma D_5ed20 : decode_any W_5ed20 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed24 : bv 32 := 0x00000613.
Lemma F_5ed24 : fetch_word AsanUbsan.M.loaded_segments (0x5ed74 : word) = Some W_5ed24.
Proof. vm_refl. Qed.
Lemma D_5ed24 : decode_any W_5ed24 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed28 : bv 32 := 0x0005b023.
Lemma F_5ed28 : fetch_word AsanUbsan.M.loaded_segments (0x5ed78 : word) = Some W_5ed28.
Proof. vm_refl. Qed.
Lemma D_5ed28 : decode_any W_5ed28 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed2c : bv 32 := 0x01813083.
Lemma F_5ed2c : fetch_word AsanUbsan.M.loaded_segments (0x5ed7c : word) = Some W_5ed2c.
Proof. vm_refl. Qed.
Lemma D_5ed2c : decode_any W_5ed2c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed30 : bv 32 := 0x01013403.
Lemma F_5ed30 : fetch_word AsanUbsan.M.loaded_segments (0x5ed80 : word) = Some W_5ed30.
Proof. vm_refl. Qed.
Lemma D_5ed30 : decode_any W_5ed30 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed34 : bv 32 := 0x00813483.
Lemma F_5ed34 : fetch_word AsanUbsan.M.loaded_segments (0x5ed84 : word) = Some W_5ed34.
Proof. vm_refl. Qed.
Lemma D_5ed34 : decode_any W_5ed34 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed38 : bv 32 := 0x00013903.
Lemma F_5ed38 : fetch_word AsanUbsan.M.loaded_segments (0x5ed88 : word) = Some W_5ed38.
Proof. vm_refl. Qed.
Lemma D_5ed38 : decode_any W_5ed38 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed3c : bv 32 := 0x02010113.
Lemma F_5ed3c : fetch_word AsanUbsan.M.loaded_segments (0x5ed8c : word) = Some W_5ed3c.
Proof. vm_refl. Qed.
Lemma D_5ed3c : decode_any W_5ed3c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed40 : bv 32 := 0x00008067.
Lemma F_5ed40 : fetch_word AsanUbsan.M.loaded_segments (0x5ed90 : word) = Some W_5ed40.
Proof. vm_refl. Qed.
Lemma D_5ed40 : decode_any W_5ed40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed44 : bv 32 := 0x04853483.
Lemma F_5ed44 : fetch_word AsanUbsan.M.loaded_segments (0x5ed94 : word) = Some W_5ed44.
Proof. vm_refl. Qed.
Lemma D_5ed44 : decode_any W_5ed44 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed48 : bv 32 := 0x00100593.
Lemma F_5ed48 : fetch_word AsanUbsan.M.loaded_segments (0x5ed98 : word) = Some W_5ed48.
Proof. vm_refl. Qed.
Lemma D_5ed48 : decode_any W_5ed48 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed4c : bv 32 := 0x0095e663.
Lemma F_5ed4c : fetch_word AsanUbsan.M.loaded_segments (0x5ed9c : word) = Some W_5ed4c.
Proof. vm_refl. Qed.
Lemma D_5ed4c : decode_any W_5ed4c = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed50 : bv 32 := 0x765250ef.
Lemma F_5ed50 : fetch_word AsanUbsan.M.loaded_segments (0x5eda0 : word) = Some W_5ed50.
Proof. vm_refl. Qed.
Lemma D_5ed50 : decode_any W_5ed50 = Some (Jal 1 155492, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed54 : bv 32 := 0x00050493.
Lemma F_5ed54 : fetch_word AsanUbsan.M.loaded_segments (0x5eda4 : word) = Some W_5ed54.
Proof. vm_refl. Qed.
Lemma D_5ed54 : decode_any W_5ed54 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed58 : bv 32 := 0xec0490e3.
Lemma F_5ed58 : fetch_word AsanUbsan.M.loaded_segments (0x5eda8 : word) = Some W_5ed58.
Proof. vm_refl. Qed.
Lemma D_5ed58 : decode_any W_5ed58 = Some (Branch BC_NE 9 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ed5c : bv 32 := 0xf59ff06f.
Lemma F_5ed5c : fetch_word AsanUbsan.M.loaded_segments (0x5edac : word) = Some W_5ed5c.
Proof. vm_refl. Qed.
Lemma D_5ed5c : decode_any W_5ed5c = Some (Jal 0 2096984, 4%Z).
Proof. vm_refl. Qed.
