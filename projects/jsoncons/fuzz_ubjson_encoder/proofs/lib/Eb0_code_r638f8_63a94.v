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

Definition W_5eef0 : bv 32 := 0xfe010113.
Lemma F_5eef0 : fetch_word AsanUbsan.M.loaded_segments (0x5ef40 : word) = Some W_5eef0.
Proof. vm_refl. Qed.
Lemma D_5eef0 : decode_any W_5eef0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eef4 : bv 32 := 0x00113c23.
Lemma F_5eef4 : fetch_word AsanUbsan.M.loaded_segments (0x5ef44 : word) = Some W_5eef4.
Proof. vm_refl. Qed.
Lemma D_5eef4 : decode_any W_5eef4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eef8 : bv 32 := 0x00813823.
Lemma F_5eef8 : fetch_word AsanUbsan.M.loaded_segments (0x5ef48 : word) = Some W_5eef8.
Proof. vm_refl. Qed.
Lemma D_5eef8 : decode_any W_5eef8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eefc : bv 32 := 0x00913423.
Lemma F_5eefc : fetch_word AsanUbsan.M.loaded_segments (0x5ef4c : word) = Some W_5eefc.
Proof. vm_refl. Qed.
Lemma D_5eefc : decode_any W_5eefc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef00 : bv 32 := 0x01213023.
Lemma F_5ef00 : fetch_word AsanUbsan.M.loaded_segments (0x5ef50 : word) = Some W_5ef00.
Proof. vm_refl. Qed.
Lemma D_5ef00 : decode_any W_5ef00 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef04 : bv 32 := 0x02010413.
Lemma F_5ef04 : fetch_word AsanUbsan.M.loaded_segments (0x5ef54 : word) = Some W_5ef04.
Proof. vm_refl. Qed.
Lemma D_5ef04 : decode_any W_5ef04 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef08 : bv 32 := 0x000df517.
Lemma F_5ef08 : fetch_word AsanUbsan.M.loaded_segments (0x5ef58 : word) = Some W_5ef08.
Proof. vm_refl. Qed.
Lemma D_5ef08 : decode_any W_5ef08 = Some (Auipc 10 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef0c : bv 32 := 0x76850513.
Lemma F_5ef0c : fetch_word AsanUbsan.M.loaded_segments (0x5ef5c : word) = Some W_5ef0c.
Proof. vm_refl. Qed.
Lemma D_5ef0c : decode_any W_5ef0c = Some (OpImm ALU_ADD 10 10 1896, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef10 : bv 32 := 0x63c050ef.
Lemma F_5ef10 : fetch_word AsanUbsan.M.loaded_segments (0x5ef60 : word) = Some W_5ef10.
Proof. vm_refl. Qed.
Lemma D_5ef10 : decode_any W_5ef10 = Some (Jal 1 22076, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef14 : bv 32 := 0x00053483.
Lemma F_5ef14 : fetch_word AsanUbsan.M.loaded_segments (0x5ef64 : word) = Some W_5ef14.
Proof. vm_refl. Qed.
Lemma D_5ef14 : decode_any W_5ef14 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef18 : bv 32 := 0x08048863.
Lemma F_5ef18 : fetch_word AsanUbsan.M.loaded_segments (0x5ef68 : word) = Some W_5ef18.
Proof. vm_refl. Qed.
Lemma D_5ef18 : decode_any W_5ef18 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef1c : bv 32 := 0x0604c503.
Lemma F_5ef1c : fetch_word AsanUbsan.M.loaded_segments (0x5ef6c : word) = Some W_5ef1c.
Proof. vm_refl. Qed.
Lemma D_5ef1c : decode_any W_5ef1c = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef20 : bv 32 := 0x0584b903.
Lemma F_5ef20 : fetch_word AsanUbsan.M.loaded_segments (0x5ef70 : word) = Some W_5ef20.
Proof. vm_refl. Qed.
Lemma D_5ef20 : decode_any W_5ef20 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef24 : bv 32 := 0x00050863.
Lemma F_5ef24 : fetch_word AsanUbsan.M.loaded_segments (0x5ef74 : word) = Some W_5ef24.
Proof. vm_refl. Qed.
Lemma D_5ef24 : decode_any W_5ef24 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef28 : bv 32 := 0x00048513.
Lemma F_5ef28 : fetch_word AsanUbsan.M.loaded_segments (0x5ef78 : word) = Some W_5ef28.
Proof. vm_refl. Qed.
Lemma D_5ef28 : decode_any W_5ef28 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef2c : bv 32 := 0x00040593.
Lemma F_5ef2c : fetch_word AsanUbsan.M.loaded_segments (0x5ef7c : word) = Some W_5ef2c.
Proof. vm_refl. Qed.
Lemma D_5ef2c : decode_any W_5ef2c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef30 : bv 32 := 0x871ff0ef.
Lemma F_5ef30 : fetch_word AsanUbsan.M.loaded_segments (0x5ef80 : word) = Some W_5ef30.
Proof. vm_refl. Qed.
Lemma D_5ef30 : decode_any W_5ef30 = Some (Jal 1 2095216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef34 : bv 32 := 0xff890593.
Lemma F_5ef34 : fetch_word AsanUbsan.M.loaded_segments (0x5ef84 : word) = Some W_5ef34.
Proof. vm_refl. Qed.
Lemma D_5ef34 : decode_any W_5ef34 = Some (OpImm ALU_ADD 11 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef38 : bv 32 := 0x00100513.
Lemma F_5ef38 : fetch_word AsanUbsan.M.loaded_segments (0x5ef88 : word) = Some W_5ef38.
Proof. vm_refl. Qed.
Lemma D_5ef38 : decode_any W_5ef38 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef3c : bv 32 := 0x00b51533.
Lemma F_5ef3c : fetch_word AsanUbsan.M.loaded_segments (0x5ef8c : word) = Some W_5ef3c.
Proof. vm_refl. Qed.
Lemma D_5ef3c : decode_any W_5ef3c = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef40 : bv 32 := 0x0005061b.
Lemma F_5ef40 : fetch_word AsanUbsan.M.loaded_segments (0x5ef90 : word) = Some W_5ef40.
Proof. vm_refl. Qed.
Lemma D_5ef40 : decode_any W_5ef40 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef44 : bv 32 := 0x08c05263.
Lemma F_5ef44 : fetch_word AsanUbsan.M.loaded_segments (0x5ef94 : word) = Some W_5ef44.
Proof. vm_refl. Qed.
Lemma D_5ef44 : decode_any W_5ef44 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef48 : bv 32 := 0x000016b7.
Lemma F_5ef48 : fetch_word AsanUbsan.M.loaded_segments (0x5ef98 : word) = Some W_5ef48.
Proof. vm_refl. Qed.
Lemma D_5ef48 : decode_any W_5ef48 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef4c : bv 32 := 0xff190613.
Lemma F_5ef4c : fetch_word AsanUbsan.M.loaded_segments (0x5ef9c : word) = Some W_5ef4c.
Proof. vm_refl. Qed.
Lemma D_5ef4c : decode_any W_5ef4c = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef50 : bv 32 := 0x30000713.
Lemma F_5ef50 : fetch_word AsanUbsan.M.loaded_segments (0x5efa0 : word) = Some W_5ef50.
Proof. vm_refl. Qed.
Lemma D_5ef50 : decode_any W_5ef50 = Some (OpImm ALU_ADD 14 0 768, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef54 : bv 32 := 0xfff00793.
Lemma F_5ef54 : fetch_word AsanUbsan.M.loaded_segments (0x5efa4 : word) = Some W_5ef54.
Proof. vm_refl. Qed.
Lemma D_5ef54 : decode_any W_5ef54 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef58 : bv 32 := 0x00c71733.
Lemma F_5ef58 : fetch_word AsanUbsan.M.loaded_segments (0x5efa8 : word) = Some W_5ef58.
Proof. vm_refl. Qed.
Lemma D_5ef58 : decode_any W_5ef58 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef5c : bv 32 := 0x0104b603.
Lemma F_5ef5c : fetch_word AsanUbsan.M.loaded_segments (0x5efac : word) = Some W_5ef5c.
Proof. vm_refl. Qed.
Lemma D_5ef5c : decode_any W_5ef5c = Some (Load SZ8 true 12 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef60 : bv 32 := 0x00b797b3.
Lemma F_5ef60 : fetch_word AsanUbsan.M.loaded_segments (0x5efb0 : word) = Some W_5ef60.
Proof. vm_refl. Qed.
Lemma D_5ef60 : decode_any W_5ef60 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef64 : bv 32 := 0xfff50813.
Lemma F_5ef64 : fetch_word AsanUbsan.M.loaded_segments (0x5efb4 : word) = Some W_5ef64.
Proof. vm_refl. Qed.
Lemma D_5ef64 : decode_any W_5ef64 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef68 : bv 32 := 0x00d485b3.
Lemma F_5ef68 : fetch_word AsanUbsan.M.loaded_segments (0x5efb8 : word) = Some W_5ef68.
Proof. vm_refl. Qed.
Lemma D_5ef68 : decode_any W_5ef68 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef6c : bv 32 := 0x00e586b3.
Lemma F_5ef6c : fetch_word AsanUbsan.M.loaded_segments (0x5efbc : word) = Some W_5ef6c.
Proof. vm_refl. Qed.
Lemma D_5ef6c : decode_any W_5ef6c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef70 : bv 32 := 0xfff7c713.
Lemma F_5ef70 : fetch_word AsanUbsan.M.loaded_segments (0x5efc0 : word) = Some W_5ef70.
Proof. vm_refl. Qed.
Lemma D_5ef70 : decode_any W_5ef70 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef74 : bv 32 := 0x02081813.
Lemma F_5ef74 : fetch_word AsanUbsan.M.loaded_segments (0x5efc4 : word) = Some W_5ef74.
Proof. vm_refl. Qed.
Lemma D_5ef74 : decode_any W_5ef74 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef78 : bv 32 := 0x02085793.
Lemma F_5ef78 : fetch_word AsanUbsan.M.loaded_segments (0x5efc8 : word) = Some W_5ef78.
Proof. vm_refl. Qed.
Lemma D_5ef78 : decode_any W_5ef78 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef7c : bv 32 := 0x00f607b3.
Lemma F_5ef7c : fetch_word AsanUbsan.M.loaded_segments (0x5efcc : word) = Some W_5ef7c.
Proof. vm_refl. Qed.
Lemma D_5ef7c : decode_any W_5ef7c = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef80 : bv 32 := 0x00178813.
Lemma F_5ef80 : fetch_word AsanUbsan.M.loaded_segments (0x5efd0 : word) = Some W_5ef80.
Proof. vm_refl. Qed.
Lemma D_5ef80 : decode_any W_5ef80 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef84 : bv 32 := 0x00e678b3.
Lemma F_5ef84 : fetch_word AsanUbsan.M.loaded_segments (0x5efd4 : word) = Some W_5ef84.
Proof. vm_refl. Qed.
Lemma D_5ef84 : decode_any W_5ef84 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef88 : bv 32 := 0x011687b3.
Lemma F_5ef88 : fetch_word AsanUbsan.M.loaded_segments (0x5efd8 : word) = Some W_5ef88.
Proof. vm_refl. Qed.
Lemma D_5ef88 : decode_any W_5ef88 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef8c : bv 32 := 0x0007c283.
Lemma F_5ef8c : fetch_word AsanUbsan.M.loaded_segments (0x5efdc : word) = Some W_5ef8c.
Proof. vm_refl. Qed.
Lemma D_5ef8c : decode_any W_5ef8c = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef90 : bv 32 := 0x06028663.
Lemma F_5ef90 : fetch_word AsanUbsan.M.loaded_segments (0x5efe0 : word) = Some W_5ef90.
Proof. vm_refl. Qed.
Lemma D_5ef90 : decode_any W_5ef90 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef94 : bv 32 := 0xfff5051b.
Lemma F_5ef94 : fetch_word AsanUbsan.M.loaded_segments (0x5efe4 : word) = Some W_5ef94.
Proof. vm_refl. Qed.
Lemma D_5ef94 : decode_any W_5ef94 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef98 : bv 32 := 0x00160613.
Lemma F_5ef98 : fetch_word AsanUbsan.M.loaded_segments (0x5efe8 : word) = Some W_5ef98.
Proof. vm_refl. Qed.
Lemma D_5ef98 : decode_any W_5ef98 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ef9c : bv 32 := 0xfe0514e3.
Lemma F_5ef9c : fetch_word AsanUbsan.M.loaded_segments (0x5efec : word) = Some W_5ef9c.
Proof. vm_refl. Qed.
Lemma D_5ef9c : decode_any W_5ef9c = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efa0 : bv 32 := 0x0104b823.
Lemma F_5efa0 : fetch_word AsanUbsan.M.loaded_segments (0x5eff0 : word) = Some W_5efa0.
Proof. vm_refl. Qed.
Lemma D_5efa0 : decode_any W_5efa0 = Some (Store SZ8 9 16 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efa4 : bv 32 := 0x0400006f.
Lemma F_5efa4 : fetch_word AsanUbsan.M.loaded_segments (0x5eff4 : word) = Some W_5efa4.
Proof. vm_refl. Qed.
Lemma D_5efa4 : decode_any W_5efa4 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efa8 : bv 32 := 0x000df517.
Lemma F_5efa8 : fetch_word AsanUbsan.M.loaded_segments (0x5eff8 : word) = Some W_5efa8.
Proof. vm_refl. Qed.
Lemma D_5efa8 : decode_any W_5efa8 = Some (Auipc 10 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efac : bv 32 := 0x92853503.
Lemma F_5efac : fetch_word AsanUbsan.M.loaded_segments (0x5effc : word) = Some W_5efac.
Proof. vm_refl. Qed.
Lemma D_5efac : decode_any W_5efac = Some (Load SZ8 true 10 10 2344, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efb0 : bv 32 := 0x00052503.
Lemma F_5efb0 : fetch_word AsanUbsan.M.loaded_segments (0x5f000 : word) = Some W_5efb0.
Proof. vm_refl. Qed.
Lemma D_5efb0 : decode_any W_5efb0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efb4 : bv 32 := 0x02050863.
Lemma F_5efb4 : fetch_word AsanUbsan.M.loaded_segments (0x5f004 : word) = Some W_5efb4.
Proof. vm_refl. Qed.
Lemma D_5efb4 : decode_any W_5efb4 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efb8 : bv 32 := 0x289250ef.
Lemma F_5efb8 : fetch_word AsanUbsan.M.loaded_segments (0x5f008 : word) = Some W_5efb8.
Proof. vm_refl. Qed.
Lemma D_5efb8 : decode_any W_5efb8 = Some (Jal 1 154248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efbc : bv 32 := 0x02050463.
Lemma F_5efbc : fetch_word AsanUbsan.M.loaded_segments (0x5f00c : word) = Some W_5efbc.
Proof. vm_refl. Qed.
Lemma D_5efbc : decode_any W_5efbc = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efc0 : bv 32 := 0x02850583.
Lemma F_5efc0 : fetch_word AsanUbsan.M.loaded_segments (0x5f010 : word) = Some W_5efc0.
Proof. vm_refl. Qed.
Lemma D_5efc0 : decode_any W_5efc0 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efc4 : bv 32 := 0x0a058663.
Lemma F_5efc4 : fetch_word AsanUbsan.M.loaded_segments (0x5f014 : word) = Some W_5efc4.
Proof. vm_refl. Qed.
Lemma D_5efc4 : decode_any W_5efc4 = Some (Branch BC_EQ 11 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efc8 : bv 32 := 0x00000513.
Lemma F_5efc8 : fetch_word AsanUbsan.M.loaded_segments (0x5f018 : word) = Some W_5efc8.
Proof. vm_refl. Qed.
Lemma D_5efc8 : decode_any W_5efc8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efcc : bv 32 := 0x01813083.
Lemma F_5efcc : fetch_word AsanUbsan.M.loaded_segments (0x5f01c : word) = Some W_5efcc.
Proof. vm_refl. Qed.
Lemma D_5efcc : decode_any W_5efcc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efd0 : bv 32 := 0x01013403.
Lemma F_5efd0 : fetch_word AsanUbsan.M.loaded_segments (0x5f020 : word) = Some W_5efd0.
Proof. vm_refl. Qed.
Lemma D_5efd0 : decode_any W_5efd0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efd4 : bv 32 := 0x00813483.
Lemma F_5efd4 : fetch_word AsanUbsan.M.loaded_segments (0x5f024 : word) = Some W_5efd4.
Proof. vm_refl. Qed.
Lemma D_5efd4 : decode_any W_5efd4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efd8 : bv 32 := 0x00013903.
Lemma F_5efd8 : fetch_word AsanUbsan.M.loaded_segments (0x5f028 : word) = Some W_5efd8.
Proof. vm_refl. Qed.
Lemma D_5efd8 : decode_any W_5efd8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efdc : bv 32 := 0x02010113.
Lemma F_5efdc : fetch_word AsanUbsan.M.loaded_segments (0x5f02c : word) = Some W_5efdc.
Proof. vm_refl. Qed.
Lemma D_5efdc : decode_any W_5efdc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efe0 : bv 32 := 0x00008067.
Lemma F_5efe0 : fetch_word AsanUbsan.M.loaded_segments (0x5f030 : word) = Some W_5efe0.
Proof. vm_refl. Qed.
Lemma D_5efe0 : decode_any W_5efe0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efe4 : bv 32 := 0x01813083.
Lemma F_5efe4 : fetch_word AsanUbsan.M.loaded_segments (0x5f034 : word) = Some W_5efe4.
Proof. vm_refl. Qed.
Lemma D_5efe4 : decode_any W_5efe4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efe8 : bv 32 := 0x01013403.
Lemma F_5efe8 : fetch_word AsanUbsan.M.loaded_segments (0x5f038 : word) = Some W_5efe8.
Proof. vm_refl. Qed.
Lemma D_5efe8 : decode_any W_5efe8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5efec : bv 32 := 0x00813483.
Lemma F_5efec : fetch_word AsanUbsan.M.loaded_segments (0x5f03c : word) = Some W_5efec.
Proof. vm_refl. Qed.
Lemma D_5efec : decode_any W_5efec = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eff0 : bv 32 := 0x00013903.
Lemma F_5eff0 : fetch_word AsanUbsan.M.loaded_segments (0x5f040 : word) = Some W_5eff0.
Proof. vm_refl. Qed.
Lemma D_5eff0 : decode_any W_5eff0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eff4 : bv 32 := 0x02010113.
Lemma F_5eff4 : fetch_word AsanUbsan.M.loaded_segments (0x5f044 : word) = Some W_5eff4.
Proof. vm_refl. Qed.
Lemma D_5eff4 : decode_any W_5eff4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eff8 : bv 32 := 0x00008067.
Lemma F_5eff8 : fetch_word AsanUbsan.M.loaded_segments (0x5f048 : word) = Some W_5eff8.
Proof. vm_refl. Qed.
Lemma D_5eff8 : decode_any W_5eff8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5effc : bv 32 := 0x00160613.
Lemma F_5effc : fetch_word AsanUbsan.M.loaded_segments (0x5f04c : word) = Some W_5effc.
Proof. vm_refl. Qed.
Lemma D_5effc : decode_any W_5effc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f000 : bv 32 := 0x00100513.
Lemma F_5f000 : fetch_word AsanUbsan.M.loaded_segments (0x5f050 : word) = Some W_5f000.
Proof. vm_refl. Qed.
Lemma D_5f000 : decode_any W_5f000 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f004 : bv 32 := 0xffb90693.
Lemma F_5f004 : fetch_word AsanUbsan.M.loaded_segments (0x5f054 : word) = Some W_5f004.
Proof. vm_refl. Qed.
Lemma D_5f004 : decode_any W_5f004 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f008 : bv 32 := 0x00c4b823.
Lemma F_5f008 : fetch_word AsanUbsan.M.loaded_segments (0x5f058 : word) = Some W_5f008.
Proof. vm_refl. Qed.
Lemma D_5f008 : decode_any W_5f008 = Some (Store SZ8 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f00c : bv 32 := 0x00a78023.
Lemma F_5f00c : fetch_word AsanUbsan.M.loaded_segments (0x5f05c : word) = Some W_5f00c.
Proof. vm_refl. Qed.
Lemma D_5f00c : decode_any W_5f00c = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f010 : bv 32 := 0x00d51533.
Lemma F_5f010 : fetch_word AsanUbsan.M.loaded_segments (0x5f060 : word) = Some W_5f010.
Proof. vm_refl. Qed.
Lemma D_5f010 : decode_any W_5f010 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f014 : bv 32 := 0x00200613.
Lemma F_5f014 : fetch_word AsanUbsan.M.loaded_segments (0x5f064 : word) = Some W_5f014.
Proof. vm_refl. Qed.
Lemma D_5f014 : decode_any W_5f014 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f018 : bv 32 := 0x00889893.
Lemma F_5f018 : fetch_word AsanUbsan.M.loaded_segments (0x5f068 : word) = Some W_5f018.
Proof. vm_refl. Qed.
Lemma D_5f018 : decode_any W_5f018 = Some (ShiftImm ALU_SLL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f01c : bv 32 := 0x01261633.
Lemma F_5f01c : fetch_word AsanUbsan.M.loaded_segments (0x5f06c : word) = Some W_5f01c.
Proof. vm_refl. Qed.
Lemma D_5f01c : decode_any W_5f01c = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f020 : bv 32 := 0x00a58533.
Lemma F_5f020 : fetch_word AsanUbsan.M.loaded_segments (0x5f070 : word) = Some W_5f020.
Proof. vm_refl. Qed.
Lemma D_5f020 : decode_any W_5f020 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f024 : bv 32 := 0x01160633.
Lemma F_5f024 : fetch_word AsanUbsan.M.loaded_segments (0x5f074 : word) = Some W_5f024.
Proof. vm_refl. Qed.
Lemma D_5f024 : decode_any W_5f024 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f028 : bv 32 := 0x00c504b3.
Lemma F_5f028 : fetch_word AsanUbsan.M.loaded_segments (0x5f078 : word) = Some W_5f028.
Proof. vm_refl. Qed.
Lemma D_5f028 : decode_any W_5f028 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f02c : bv 32 := 0x0084bc23.
Lemma F_5f02c : fetch_word AsanUbsan.M.loaded_segments (0x5f07c : word) = Some W_5f02c.
Proof. vm_refl. Qed.
Lemma D_5f02c : decode_any W_5f02c = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f030 : bv 32 := 0x0ef4bc23.
Lemma F_5f030 : fetch_word AsanUbsan.M.loaded_segments (0x5f080 : word) = Some W_5f030.
Proof. vm_refl. Qed.
Lemma D_5f030 : decode_any W_5f030 = Some (Store SZ8 9 15 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f034 : bv 32 := 0x00048513.
Lemma F_5f034 : fetch_word AsanUbsan.M.loaded_segments (0x5f084 : word) = Some W_5f034.
Proof. vm_refl. Qed.
Lemma D_5f034 : decode_any W_5f034 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f038 : bv 32 := 0x4c0000ef.
Lemma F_5f038 : fetch_word AsanUbsan.M.loaded_segments (0x5f088 : word) = Some W_5f038.
Proof. vm_refl. Qed.
Lemma D_5f038 : decode_any W_5f038 = Some (Jal 1 1216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f03c : bv 32 := 0x00050593.
Lemma F_5f03c : fetch_word AsanUbsan.M.loaded_segments (0x5f08c : word) = Some W_5f03c.
Proof. vm_refl. Qed.
Lemma D_5f03c : decode_any W_5f03c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f040 : bv 32 := 0x00048513.
Lemma F_5f040 : fetch_word AsanUbsan.M.loaded_segments (0x5f090 : word) = Some W_5f040.
Proof. vm_refl. Qed.
Lemma D_5f040 : decode_any W_5f040 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f044 : bv 32 := 0x00000613.
Lemma F_5f044 : fetch_word AsanUbsan.M.loaded_segments (0x5f094 : word) = Some W_5f044.
Proof. vm_refl. Qed.
Lemma D_5f044 : decode_any W_5f044 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f048 : bv 32 := 0x0005b023.
Lemma F_5f048 : fetch_word AsanUbsan.M.loaded_segments (0x5f098 : word) = Some W_5f048.
Proof. vm_refl. Qed.
Lemma D_5f048 : decode_any W_5f048 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f04c : bv 32 := 0x0005b423.
Lemma F_5f04c : fetch_word AsanUbsan.M.loaded_segments (0x5f09c : word) = Some W_5f04c.
Proof. vm_refl. Qed.
Lemma D_5f04c : decode_any W_5f04c = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f050 : bv 32 := 0x0005b823.
Lemma F_5f050 : fetch_word AsanUbsan.M.loaded_segments (0x5f0a0 : word) = Some W_5f050.
Proof. vm_refl. Qed.
Lemma D_5f050 : decode_any W_5f050 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f054 : bv 32 := 0x0005bc23.
Lemma F_5f054 : fetch_word AsanUbsan.M.loaded_segments (0x5f0a4 : word) = Some W_5f054.
Proof. vm_refl. Qed.
Lemma D_5f054 : decode_any W_5f054 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f058 : bv 32 := 0x01813083.
Lemma F_5f058 : fetch_word AsanUbsan.M.loaded_segments (0x5f0a8 : word) = Some W_5f058.
Proof. vm_refl. Qed.
Lemma D_5f058 : decode_any W_5f058 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f05c : bv 32 := 0x01013403.
Lemma F_5f05c : fetch_word AsanUbsan.M.loaded_segments (0x5f0ac : word) = Some W_5f05c.
Proof. vm_refl. Qed.
Lemma D_5f05c : decode_any W_5f05c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f060 : bv 32 := 0x00813483.
Lemma F_5f060 : fetch_word AsanUbsan.M.loaded_segments (0x5f0b0 : word) = Some W_5f060.
Proof. vm_refl. Qed.
Lemma D_5f060 : decode_any W_5f060 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f064 : bv 32 := 0x00013903.
Lemma F_5f064 : fetch_word AsanUbsan.M.loaded_segments (0x5f0b4 : word) = Some W_5f064.
Proof. vm_refl. Qed.
Lemma D_5f064 : decode_any W_5f064 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f068 : bv 32 := 0x02010113.
Lemma F_5f068 : fetch_word AsanUbsan.M.loaded_segments (0x5f0b8 : word) = Some W_5f068.
Proof. vm_refl. Qed.
Lemma D_5f068 : decode_any W_5f068 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f06c : bv 32 := 0x00008067.
Lemma F_5f06c : fetch_word AsanUbsan.M.loaded_segments (0x5f0bc : word) = Some W_5f06c.
Proof. vm_refl. Qed.
Lemma D_5f06c : decode_any W_5f06c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f070 : bv 32 := 0x04853483.
Lemma F_5f070 : fetch_word AsanUbsan.M.loaded_segments (0x5f0c0 : word) = Some W_5f070.
Proof. vm_refl. Qed.
Lemma D_5f070 : decode_any W_5f070 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f074 : bv 32 := 0x00100593.
Lemma F_5f074 : fetch_word AsanUbsan.M.loaded_segments (0x5f0c4 : word) = Some W_5f074.
Proof. vm_refl. Qed.
Lemma D_5f074 : decode_any W_5f074 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f078 : bv 32 := 0x0095e663.
Lemma F_5f078 : fetch_word AsanUbsan.M.loaded_segments (0x5f0c8 : word) = Some W_5f078.
Proof. vm_refl. Qed.
Lemma D_5f078 : decode_any W_5f078 = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f07c : bv 32 := 0x439250ef.
Lemma F_5f07c : fetch_word AsanUbsan.M.loaded_segments (0x5f0cc : word) = Some W_5f07c.
Proof. vm_refl. Qed.
Lemma D_5f07c : decode_any W_5f07c = Some (Jal 1 154680, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f080 : bv 32 := 0x00050493.
Lemma F_5f080 : fetch_word AsanUbsan.M.loaded_segments (0x5f0d0 : word) = Some W_5f080.
Proof. vm_refl. Qed.
Lemma D_5f080 : decode_any W_5f080 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f084 : bv 32 := 0xe8049ce3.
Lemma F_5f084 : fetch_word AsanUbsan.M.loaded_segments (0x5f0d4 : word) = Some W_5f084.
Proof. vm_refl. Qed.
Lemma D_5f084 : decode_any W_5f084 = Some (Branch BC_NE 9 0 7832, 4%Z).
Proof. vm_refl. Qed.

Definition W_5f088 : bv 32 := 0xf41ff06f.
Lemma F_5f088 : fetch_word AsanUbsan.M.loaded_segments (0x5f0d8 : word) = Some W_5f088.
Proof. vm_refl. Qed.
Lemma D_5f088 : decode_any W_5f088 = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.
