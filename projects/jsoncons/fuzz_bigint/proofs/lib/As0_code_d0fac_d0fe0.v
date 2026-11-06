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

Definition W_d0fac : bv 32 := 0xff010113.
Lemma F_d0fac : fetch_word Asan.M.loaded_segments (0xd0fac : word) = Some W_d0fac.
Proof. vm_refl. Qed.
Lemma D_d0fac : decode_any W_d0fac = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fb0 : bv 32 := 0x00113423.
Lemma F_d0fb0 : fetch_word Asan.M.loaded_segments (0xd0fb0 : word) = Some W_d0fb0.
Proof. vm_refl. Qed.
Lemma D_d0fb0 : decode_any W_d0fb0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fb4 : bv 32 := 0x00060693.
Lemma F_d0fb4 : fetch_word Asan.M.loaded_segments (0xd0fb4 : word) = Some W_d0fb4.
Proof. vm_refl. Qed.
Lemma D_d0fb4 : decode_any W_d0fb4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fb8 : bv 32 := 0x00058613.
Lemma F_d0fb8 : fetch_word Asan.M.loaded_segments (0xd0fb8 : word) = Some W_d0fb8.
Proof. vm_refl. Qed.
Lemma D_d0fb8 : decode_any W_d0fb8 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fbc : bv 32 := 0x00050593.
Lemma F_d0fbc : fetch_word Asan.M.loaded_segments (0xd0fbc : word) = Some W_d0fbc.
Proof. vm_refl. Qed.
Lemma D_d0fbc : decode_any W_d0fbc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fc0 : bv 32 := 0x03f00513.
Lemma F_d0fc0 : fetch_word Asan.M.loaded_segments (0xd0fc0 : word) = Some W_d0fc0.
Proof. vm_refl. Qed.
Lemma D_d0fc0 : decode_any W_d0fc0 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fc4 : bv 32 := 0x00000713.
Lemma F_d0fc4 : fetch_word Asan.M.loaded_segments (0xd0fc4 : word) = Some W_d0fc4.
Proof. vm_refl. Qed.
Lemma D_d0fc4 : decode_any W_d0fc4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fc8 : bv 32 := 0x00000793.
Lemma F_d0fc8 : fetch_word Asan.M.loaded_segments (0xd0fc8 : word) = Some W_d0fc8.
Proof. vm_refl. Qed.
Lemma D_d0fc8 : decode_any W_d0fc8 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fcc : bv 32 := 0x00000813.
Lemma F_d0fcc : fetch_word Asan.M.loaded_segments (0xd0fcc : word) = Some W_d0fcc.
Proof. vm_refl. Qed.
Lemma D_d0fcc : decode_any W_d0fcc = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fd0 : bv 32 := 0xcc8fb0ef.
Lemma F_d0fd0 : fetch_word Asan.M.loaded_segments (0xd0fd0 : word) = Some W_d0fd0.
Proof. vm_refl. Qed.
Lemma D_d0fd0 : decode_any W_d0fd0 = Some (Jal 1 2077896, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fd4 : bv 32 := 0x00813083.
Lemma F_d0fd4 : fetch_word Asan.M.loaded_segments (0xd0fd4 : word) = Some W_d0fd4.
Proof. vm_refl. Qed.
Lemma D_d0fd4 : decode_any W_d0fd4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fd8 : bv 32 := 0x01010113.
Lemma F_d0fd8 : fetch_word Asan.M.loaded_segments (0xd0fd8 : word) = Some W_d0fd8.
Proof. vm_refl. Qed.
Lemma D_d0fd8 : decode_any W_d0fd8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0fdc : bv 32 := 0xfe0ec06f.
Lemma F_d0fdc : fetch_word Asan.M.loaded_segments (0xd0fdc : word) = Some W_d0fdc.
Proof. vm_refl. Qed.
Lemma D_d0fdc : decode_any W_d0fdc = Some (Jal 0 2017248, 4%Z).
Proof. vm_refl. Qed.
