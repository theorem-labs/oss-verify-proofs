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

Definition W_959b0 : bv 32 := 0xfe010113.
Lemma F_959b0 : fetch_word Asan.M.loaded_segments (0x95a00 : word) = Some W_959b0.
Proof. vm_refl. Qed.
Lemma D_959b0 : decode_any W_959b0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_959b4 : bv 32 := 0x00113c23.
Lemma F_959b4 : fetch_word Asan.M.loaded_segments (0x95a04 : word) = Some W_959b4.
Proof. vm_refl. Qed.
Lemma D_959b4 : decode_any W_959b4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_959b8 : bv 32 := 0x00813823.
Lemma F_959b8 : fetch_word Asan.M.loaded_segments (0x95a08 : word) = Some W_959b8.
Proof. vm_refl. Qed.
Lemma D_959b8 : decode_any W_959b8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_959bc : bv 32 := 0x00913423.
Lemma F_959bc : fetch_word Asan.M.loaded_segments (0x95a0c : word) = Some W_959bc.
Proof. vm_refl. Qed.
Lemma D_959bc : decode_any W_959bc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_959c0 : bv 32 := 0x01213023.
Lemma F_959c0 : fetch_word Asan.M.loaded_segments (0x95a10 : word) = Some W_959c0.
Proof. vm_refl. Qed.
Lemma D_959c0 : decode_any W_959c0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_959c4 : bv 32 := 0x00058413.
Lemma F_959c4 : fetch_word Asan.M.loaded_segments (0x95a14 : word) = Some W_959c4.
Proof. vm_refl. Qed.
Lemma D_959c4 : decode_any W_959c4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_959c8 : bv 32 := 0x000a3597.
Lemma F_959c8 : fetch_word Asan.M.loaded_segments (0x95a18 : word) = Some W_959c8.
Proof. vm_refl. Qed.
Lemma D_959c8 : decode_any W_959c8 = Some (Auipc 11 163, 4%Z).
Proof. vm_refl. Qed.

Definition W_959cc : bv 32 := 0x7805b903.
Lemma F_959cc : fetch_word Asan.M.loaded_segments (0x95a1c : word) = Some W_959cc.
Proof. vm_refl. Qed.
Lemma D_959cc : decode_any W_959cc = Some (Load SZ8 true 18 11 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_959d0 : bv 32 := 0x00093583.
Lemma F_959d0 : fetch_word Asan.M.loaded_segments (0x95a20 : word) = Some W_959d0.
Proof. vm_refl. Qed.
Lemma D_959d0 : decode_any W_959d0 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_959d4 : bv 32 := 0x00050493.
Lemma F_959d4 : fetch_word Asan.M.loaded_segments (0x95a24 : word) = Some W_959d4.
Proof. vm_refl. Qed.
Lemma D_959d4 : decode_any W_959d4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_959d8 : bv 32 := 0x00059863.
Lemma F_959d8 : fetch_word Asan.M.loaded_segments (0x95a28 : word) = Some W_959d8.
Proof. vm_refl. Qed.
Lemma D_959d8 : decode_any W_959d8 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_959e8 : bv 32 := 0xfff58513.
Lemma F_959e8 : fetch_word Asan.M.loaded_segments (0x95a38 : word) = Some W_959e8.
Proof. vm_refl. Qed.
Lemma D_959e8 : decode_any W_959e8 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_959ec : bv 32 := 0x00a5f533.
Lemma F_959ec : fetch_word Asan.M.loaded_segments (0x95a3c : word) = Some W_959ec.
Proof. vm_refl. Qed.
Lemma D_959ec : decode_any W_959ec = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_959f0 : bv 32 := 0x04051a63.
Lemma F_959f0 : fetch_word Asan.M.loaded_segments (0x95a40 : word) = Some W_959f0.
Proof. vm_refl. Qed.
Lemma D_959f0 : decode_any W_959f0 = Some (Branch BC_NE 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_959f4 : bv 32 := 0x00b484b3.
Lemma F_959f4 : fetch_word Asan.M.loaded_segments (0x95a44 : word) = Some W_959f4.
Proof. vm_refl. Qed.
Lemma D_959f4 : decode_any W_959f4 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_959f8 : bv 32 := 0x40b005b3.
Lemma F_959f8 : fetch_word Asan.M.loaded_segments (0x95a48 : word) = Some W_959f8.
Proof. vm_refl. Qed.
Lemma D_959f8 : decode_any W_959f8 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_959fc : bv 32 := 0xfff48513.
Lemma F_959fc : fetch_word Asan.M.loaded_segments (0x95a4c : word) = Some W_959fc.
Proof. vm_refl. Qed.
Lemma D_959fc : decode_any W_959fc = Some (OpImm ALU_ADD 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a00 : bv 32 := 0x00b57533.
Lemma F_95a00 : fetch_word Asan.M.loaded_segments (0x95a50 : word) = Some W_95a00.
Proof. vm_refl. Qed.
Lemma D_95a00 : decode_any W_95a00 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a04 : bv 32 := 0x00b475b3.
Lemma F_95a04 : fetch_word Asan.M.loaded_segments (0x95a54 : word) = Some W_95a04.
Proof. vm_refl. Qed.
Lemma D_95a04 : decode_any W_95a04 = Some (Op ALU_AND 11 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a08 : bv 32 := 0x02b57263.
Lemma F_95a08 : fetch_word Asan.M.loaded_segments (0x95a58 : word) = Some W_95a08.
Proof. vm_refl. Qed.
Lemma D_95a08 : decode_any W_95a08 = Some (Branch BC_GEU 10 11 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a0c : bv 32 := 0x40a585b3.
Lemma F_95a0c : fetch_word Asan.M.loaded_segments (0x95a5c : word) = Some W_95a0c.
Proof. vm_refl. Qed.
Lemma D_95a0c : decode_any W_95a0c = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a10 : bv 32 := 0x00400613.
Lemma F_95a10 : fetch_word Asan.M.loaded_segments (0x95a60 : word) = Some W_95a10.
Proof. vm_refl. Qed.
Lemma D_95a10 : decode_any W_95a10 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a14 : bv 32 := 0x01813083.
Lemma F_95a14 : fetch_word Asan.M.loaded_segments (0x95a64 : word) = Some W_95a14.
Proof. vm_refl. Qed.
Lemma D_95a14 : decode_any W_95a14 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a18 : bv 32 := 0x01013403.
Lemma F_95a18 : fetch_word Asan.M.loaded_segments (0x95a68 : word) = Some W_95a18.
Proof. vm_refl. Qed.
Lemma D_95a18 : decode_any W_95a18 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a1c : bv 32 := 0x00813483.
Lemma F_95a1c : fetch_word Asan.M.loaded_segments (0x95a6c : word) = Some W_95a1c.
Proof. vm_refl. Qed.
Lemma D_95a1c : decode_any W_95a1c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a20 : bv 32 := 0x00013903.
Lemma F_95a20 : fetch_word Asan.M.loaded_segments (0x95a70 : word) = Some W_95a20.
Proof. vm_refl. Qed.
Lemma D_95a20 : decode_any W_95a20 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a24 : bv 32 := 0x02010113.
Lemma F_95a24 : fetch_word Asan.M.loaded_segments (0x95a74 : word) = Some W_95a24.
Proof. vm_refl. Qed.
Lemma D_95a24 : decode_any W_95a24 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a28 : bv 32 := 0xbb1f606f.
Lemma F_95a28 : fetch_word Asan.M.loaded_segments (0x95a78 : word) = Some W_95a28.
Proof. vm_refl. Qed.
Lemma D_95a28 : decode_any W_95a28 = Some (Jal 0 2059184, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a2c : bv 32 := 0x01813083.
Lemma F_95a2c : fetch_word Asan.M.loaded_segments (0x95a7c : word) = Some W_95a2c.
Proof. vm_refl. Qed.
Lemma D_95a2c : decode_any W_95a2c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a30 : bv 32 := 0x01013403.
Lemma F_95a30 : fetch_word Asan.M.loaded_segments (0x95a80 : word) = Some W_95a30.
Proof. vm_refl. Qed.
Lemma D_95a30 : decode_any W_95a30 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a34 : bv 32 := 0x00813483.
Lemma F_95a34 : fetch_word Asan.M.loaded_segments (0x95a84 : word) = Some W_95a34.
Proof. vm_refl. Qed.
Lemma D_95a34 : decode_any W_95a34 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a38 : bv 32 := 0x00013903.
Lemma F_95a38 : fetch_word Asan.M.loaded_segments (0x95a88 : word) = Some W_95a38.
Proof. vm_refl. Qed.
Lemma D_95a38 : decode_any W_95a38 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a3c : bv 32 := 0x02010113.
Lemma F_95a3c : fetch_word Asan.M.loaded_segments (0x95a8c : word) = Some W_95a3c.
Proof. vm_refl. Qed.
Lemma D_95a3c : decode_any W_95a3c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_95a40 : bv 32 := 0x00008067.
Lemma F_95a40 : fetch_word Asan.M.loaded_segments (0x95a90 : word) = Some W_95a40.
Proof. vm_refl. Qed.
Lemma D_95a40 : decode_any W_95a40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
