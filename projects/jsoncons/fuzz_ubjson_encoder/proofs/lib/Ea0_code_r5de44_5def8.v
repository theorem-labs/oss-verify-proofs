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

Definition W_5ec1c : bv 32 := 0xff010113.
Lemma F_5ec1c : fetch_word Asan.M.loaded_segments (0x5ec6c : word) = Some W_5ec1c.
Proof. vm_refl. Qed.
Lemma D_5ec1c : decode_any W_5ec1c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec20 : bv 32 := 0x00113423.
Lemma F_5ec20 : fetch_word Asan.M.loaded_segments (0x5ec70 : word) = Some W_5ec20.
Proof. vm_refl. Qed.
Lemma D_5ec20 : decode_any W_5ec20 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec24 : bv 32 := 0x00813023.
Lemma F_5ec24 : fetch_word Asan.M.loaded_segments (0x5ec74 : word) = Some W_5ec24.
Proof. vm_refl. Qed.
Lemma D_5ec24 : decode_any W_5ec24 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec28 : bv 32 := 0x7f853583.
Lemma F_5ec28 : fetch_word Asan.M.loaded_segments (0x5ec78 : word) = Some W_5ec28.
Proof. vm_refl. Qed.
Lemma D_5ec28 : decode_any W_5ec28 = Some (Load SZ8 true 11 10 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec2c : bv 32 := 0x00000413.
Lemma F_5ec2c : fetch_word Asan.M.loaded_segments (0x5ec7c : word) = Some W_5ec2c.
Proof. vm_refl. Qed.
Lemma D_5ec2c : decode_any W_5ec2c = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec30 : bv 32 := 0x00058023.
Lemma F_5ec30 : fetch_word Asan.M.loaded_segments (0x5ec80 : word) = Some W_5ec30.
Proof. vm_refl. Qed.
Lemma D_5ec30 : decode_any W_5ec30 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec34 : bv 32 := 0x09c000ef.
Lemma F_5ec34 : fetch_word Asan.M.loaded_segments (0x5ec84 : word) = Some W_5ec34.
Proof. vm_refl. Qed.
Lemma D_5ec34 : decode_any W_5ec34 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec38 : bv 32 := 0xfffb1597.
Lemma F_5ec38 : fetch_word Asan.M.loaded_segments (0x5ec88 : word) = Some W_5ec38.
Proof. vm_refl. Qed.
Lemma D_5ec38 : decode_any W_5ec38 = Some (Auipc 11 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec3c : bv 32 := 0x7085b583.
Lemma F_5ec3c : fetch_word Asan.M.loaded_segments (0x5ec8c : word) = Some W_5ec3c.
Proof. vm_refl. Qed.
Lemma D_5ec3c : decode_any W_5ec3c = Some (Load SZ8 true 11 11 1800, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec40 : bv 32 := 0x00b53023.
Lemma F_5ec40 : fetch_word Asan.M.loaded_segments (0x5ec90 : word) = Some W_5ec40.
Proof. vm_refl. Qed.
Lemma D_5ec40 : decode_any W_5ec40 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec44 : bv 32 := 0x00b53423.
Lemma F_5ec44 : fetch_word Asan.M.loaded_segments (0x5ec94 : word) = Some W_5ec44.
Proof. vm_refl. Qed.
Lemma D_5ec44 : decode_any W_5ec44 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec48 : bv 32 := 0x00b53823.
Lemma F_5ec48 : fetch_word Asan.M.loaded_segments (0x5ec98 : word) = Some W_5ec48.
Proof. vm_refl. Qed.
Lemma D_5ec48 : decode_any W_5ec48 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec4c : bv 32 := 0x00b53c23.
Lemma F_5ec4c : fetch_word Asan.M.loaded_segments (0x5ec9c : word) = Some W_5ec4c.
Proof. vm_refl. Qed.
Lemma D_5ec4c : decode_any W_5ec4c = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec50 : bv 32 := 0x02b53023.
Lemma F_5ec50 : fetch_word Asan.M.loaded_segments (0x5eca0 : word) = Some W_5ec50.
Proof. vm_refl. Qed.
Lemma D_5ec50 : decode_any W_5ec50 = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec54 : bv 32 := 0x02b53423.
Lemma F_5ec54 : fetch_word Asan.M.loaded_segments (0x5eca4 : word) = Some W_5ec54.
Proof. vm_refl. Qed.
Lemma D_5ec54 : decode_any W_5ec54 = Some (Store SZ8 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec58 : bv 32 := 0x02b53823.
Lemma F_5ec58 : fetch_word Asan.M.loaded_segments (0x5eca8 : word) = Some W_5ec58.
Proof. vm_refl. Qed.
Lemma D_5ec58 : decode_any W_5ec58 = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec5c : bv 32 := 0x02b53c23.
Lemma F_5ec5c : fetch_word Asan.M.loaded_segments (0x5ecac : word) = Some W_5ec5c.
Proof. vm_refl. Qed.
Lemma D_5ec5c : decode_any W_5ec5c = Some (Store SZ8 10 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec60 : bv 32 := 0x04b53023.
Lemma F_5ec60 : fetch_word Asan.M.loaded_segments (0x5ecb0 : word) = Some W_5ec60.
Proof. vm_refl. Qed.
Lemma D_5ec60 : decode_any W_5ec60 = Some (Store SZ8 10 11 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec64 : bv 32 := 0x04b53423.
Lemma F_5ec64 : fetch_word Asan.M.loaded_segments (0x5ecb4 : word) = Some W_5ec64.
Proof. vm_refl. Qed.
Lemma D_5ec64 : decode_any W_5ec64 = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec68 : bv 32 := 0x04b53823.
Lemma F_5ec68 : fetch_word Asan.M.loaded_segments (0x5ecb8 : word) = Some W_5ec68.
Proof. vm_refl. Qed.
Lemma D_5ec68 : decode_any W_5ec68 = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec6c : bv 32 := 0x04b53c23.
Lemma F_5ec6c : fetch_word Asan.M.loaded_segments (0x5ecbc : word) = Some W_5ec6c.
Proof. vm_refl. Qed.
Lemma D_5ec6c : decode_any W_5ec6c = Some (Store SZ8 10 11 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec70 : bv 32 := 0x06b53023.
Lemma F_5ec70 : fetch_word Asan.M.loaded_segments (0x5ecc0 : word) = Some W_5ec70.
Proof. vm_refl. Qed.
Lemma D_5ec70 : decode_any W_5ec70 = Some (Store SZ8 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec74 : bv 32 := 0x06b53423.
Lemma F_5ec74 : fetch_word Asan.M.loaded_segments (0x5ecc4 : word) = Some W_5ec74.
Proof. vm_refl. Qed.
Lemma D_5ec74 : decode_any W_5ec74 = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec78 : bv 32 := 0x06b53823.
Lemma F_5ec78 : fetch_word Asan.M.loaded_segments (0x5ecc8 : word) = Some W_5ec78.
Proof. vm_refl. Qed.
Lemma D_5ec78 : decode_any W_5ec78 = Some (Store SZ8 10 11 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec7c : bv 32 := 0x06b53c23.
Lemma F_5ec7c : fetch_word Asan.M.loaded_segments (0x5eccc : word) = Some W_5ec7c.
Proof. vm_refl. Qed.
Lemma D_5ec7c : decode_any W_5ec7c = Some (Store SZ8 10 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec80 : bv 32 := 0x08b53023.
Lemma F_5ec80 : fetch_word Asan.M.loaded_segments (0x5ecd0 : word) = Some W_5ec80.
Proof. vm_refl. Qed.
Lemma D_5ec80 : decode_any W_5ec80 = Some (Store SZ8 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec84 : bv 32 := 0x08b53423.
Lemma F_5ec84 : fetch_word Asan.M.loaded_segments (0x5ecd4 : word) = Some W_5ec84.
Proof. vm_refl. Qed.
Lemma D_5ec84 : decode_any W_5ec84 = Some (Store SZ8 10 11 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec88 : bv 32 := 0x08b53823.
Lemma F_5ec88 : fetch_word Asan.M.loaded_segments (0x5ecd8 : word) = Some W_5ec88.
Proof. vm_refl. Qed.
Lemma D_5ec88 : decode_any W_5ec88 = Some (Store SZ8 10 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec8c : bv 32 := 0x08b53c23.
Lemma F_5ec8c : fetch_word Asan.M.loaded_segments (0x5ecdc : word) = Some W_5ec8c.
Proof. vm_refl. Qed.
Lemma D_5ec8c : decode_any W_5ec8c = Some (Store SZ8 10 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec90 : bv 32 := 0x0ab53023.
Lemma F_5ec90 : fetch_word Asan.M.loaded_segments (0x5ece0 : word) = Some W_5ec90.
Proof. vm_refl. Qed.
Lemma D_5ec90 : decode_any W_5ec90 = Some (Store SZ8 10 11 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec94 : bv 32 := 0x0ab53423.
Lemma F_5ec94 : fetch_word Asan.M.loaded_segments (0x5ece4 : word) = Some W_5ec94.
Proof. vm_refl. Qed.
Lemma D_5ec94 : decode_any W_5ec94 = Some (Store SZ8 10 11 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec98 : bv 32 := 0x0ab53823.
Lemma F_5ec98 : fetch_word Asan.M.loaded_segments (0x5ece8 : word) = Some W_5ec98.
Proof. vm_refl. Qed.
Lemma D_5ec98 : decode_any W_5ec98 = Some (Store SZ8 10 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec9c : bv 32 := 0x0ab53c23.
Lemma F_5ec9c : fetch_word Asan.M.loaded_segments (0x5ecec : word) = Some W_5ec9c.
Proof. vm_refl. Qed.
Lemma D_5ec9c : decode_any W_5ec9c = Some (Store SZ8 10 11 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca0 : bv 32 := 0x0cb53023.
Lemma F_5eca0 : fetch_word Asan.M.loaded_segments (0x5ecf0 : word) = Some W_5eca0.
Proof. vm_refl. Qed.
Lemma D_5eca0 : decode_any W_5eca0 = Some (Store SZ8 10 11 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca4 : bv 32 := 0x0cb53423.
Lemma F_5eca4 : fetch_word Asan.M.loaded_segments (0x5ecf4 : word) = Some W_5eca4.
Proof. vm_refl. Qed.
Lemma D_5eca4 : decode_any W_5eca4 = Some (Store SZ8 10 11 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eca8 : bv 32 := 0x0cb53823.
Lemma F_5eca8 : fetch_word Asan.M.loaded_segments (0x5ecf8 : word) = Some W_5eca8.
Proof. vm_refl. Qed.
Lemma D_5eca8 : decode_any W_5eca8 = Some (Store SZ8 10 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecac : bv 32 := 0x0cb53c23.
Lemma F_5ecac : fetch_word Asan.M.loaded_segments (0x5ecfc : word) = Some W_5ecac.
Proof. vm_refl. Qed.
Lemma D_5ecac : decode_any W_5ecac = Some (Store SZ8 10 11 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb0 : bv 32 := 0x0eb53023.
Lemma F_5ecb0 : fetch_word Asan.M.loaded_segments (0x5ed00 : word) = Some W_5ecb0.
Proof. vm_refl. Qed.
Lemma D_5ecb0 : decode_any W_5ecb0 = Some (Store SZ8 10 11 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb4 : bv 32 := 0x0eb53423.
Lemma F_5ecb4 : fetch_word Asan.M.loaded_segments (0x5ed04 : word) = Some W_5ecb4.
Proof. vm_refl. Qed.
Lemma D_5ecb4 : decode_any W_5ecb4 = Some (Store SZ8 10 11 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecb8 : bv 32 := 0x0eb53823.
Lemma F_5ecb8 : fetch_word Asan.M.loaded_segments (0x5ed08 : word) = Some W_5ecb8.
Proof. vm_refl. Qed.
Lemma D_5ecb8 : decode_any W_5ecb8 = Some (Store SZ8 10 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecbc : bv 32 := 0x0eb53c23.
Lemma F_5ecbc : fetch_word Asan.M.loaded_segments (0x5ed0c : word) = Some W_5ecbc.
Proof. vm_refl. Qed.
Lemma D_5ecbc : decode_any W_5ecbc = Some (Store SZ8 10 11 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecc0 : bv 32 := 0x00813083.
Lemma F_5ecc0 : fetch_word Asan.M.loaded_segments (0x5ed10 : word) = Some W_5ecc0.
Proof. vm_refl. Qed.
Lemma D_5ecc0 : decode_any W_5ecc0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecc4 : bv 32 := 0x00013403.
Lemma F_5ecc4 : fetch_word Asan.M.loaded_segments (0x5ed14 : word) = Some W_5ecc4.
Proof. vm_refl. Qed.
Lemma D_5ecc4 : decode_any W_5ecc4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ecc8 : bv 32 := 0x01010113.
Lemma F_5ecc8 : fetch_word Asan.M.loaded_segments (0x5ed18 : word) = Some W_5ecc8.
Proof. vm_refl. Qed.
Lemma D_5ecc8 : decode_any W_5ecc8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eccc : bv 32 := 0x00008067.
Lemma F_5eccc : fetch_word Asan.M.loaded_segments (0x5ed1c : word) = Some W_5eccc.
Proof. vm_refl. Qed.
Lemma D_5eccc : decode_any W_5eccc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
