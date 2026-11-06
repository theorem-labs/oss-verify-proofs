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

Definition W_6bd64 : bv 32 := 0x000f4517.
Lemma F_6bd64 : fetch_word Asan.M.loaded_segments (0x6bd64 : word) = Some W_6bd64.
Proof. vm_refl. Qed.
Lemma D_6bd64 : decode_any W_6bd64 = Some (Auipc 10 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd68 : bv 32 := 0x00100593.
Lemma F_6bd68 : fetch_word Asan.M.loaded_segments (0x6bd68 : word) = Some W_6bd68.
Proof. vm_refl. Qed.
Lemma D_6bd68 : decode_any W_6bd68 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd6c : bv 32 := 0x02b50e23.
Lemma F_6bd6c : fetch_word Asan.M.loaded_segments (0x6bd6c : word) = Some W_6bd6c.
Proof. vm_refl. Qed.
Lemma D_6bd6c : decode_any W_6bd6c = Some (Store SZ1 10 11 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd70 : bv 32 := 0x00008067.
Lemma F_6bd70 : fetch_word Asan.M.loaded_segments (0x6bd70 : word) = Some W_6bd70.
Proof. vm_refl. Qed.
Lemma D_6bd70 : decode_any W_6bd70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd74 : bv 32 := 0x000f4517.
Lemma F_6bd74 : fetch_word Asan.M.loaded_segments (0x6bd74 : word) = Some W_6bd74.
Proof. vm_refl. Qed.
Lemma D_6bd74 : decode_any W_6bd74 = Some (Auipc 10 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd78 : bv 32 := 0x02d50503.
Lemma F_6bd78 : fetch_word Asan.M.loaded_segments (0x6bd78 : word) = Some W_6bd78.
Proof. vm_refl. Qed.
Lemma D_6bd78 : decode_any W_6bd78 = Some (Load SZ1 true 10 10 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd7c : bv 32 := 0x00a03533.
Lemma F_6bd7c : fetch_word Asan.M.loaded_segments (0x6bd7c : word) = Some W_6bd7c.
Proof. vm_refl. Qed.
Lemma D_6bd7c : decode_any W_6bd7c = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd80 : bv 32 := 0x00008067.
Lemma F_6bd80 : fetch_word Asan.M.loaded_segments (0x6bd80 : word) = Some W_6bd80.
Proof. vm_refl. Qed.
Lemma D_6bd80 : decode_any W_6bd80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd84 : bv 32 := 0x000f4597.
Lemma F_6bd84 : fetch_word Asan.M.loaded_segments (0x6bd84 : word) = Some W_6bd84.
Proof. vm_refl. Qed.
Lemma D_6bd84 : decode_any W_6bd84 = Some (Auipc 11 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd88 : bv 32 := 0x00a58ea3.
Lemma F_6bd88 : fetch_word Asan.M.loaded_segments (0x6bd88 : word) = Some W_6bd88.
Proof. vm_refl. Qed.
Lemma D_6bd88 : decode_any W_6bd88 = Some (Store SZ1 11 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd8c : bv 32 := 0x00008067.
Lemma F_6bd8c : fetch_word Asan.M.loaded_segments (0x6bd8c : word) = Some W_6bd8c.
Proof. vm_refl. Qed.
Lemma D_6bd8c : decode_any W_6bd8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd90 : bv 32 := 0xfffaa517.
Lemma F_6bd90 : fetch_word Asan.M.loaded_segments (0x6bd90 : word) = Some W_6bd90.
Proof. vm_refl. Qed.
Lemma D_6bd90 : decode_any W_6bd90 = Some (Auipc 10 1048490, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd94 : bv 32 := 0xe4a50513.
Lemma F_6bd94 : fetch_word Asan.M.loaded_segments (0x6bd94 : word) = Some W_6bd94.
Proof. vm_refl. Qed.
Lemma D_6bd94 : decode_any W_6bd94 = Some (OpImm ALU_ADD 10 10 3658, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd98 : bv 32 := 0x1f10806f.
Lemma F_6bd98 : fetch_word Asan.M.loaded_segments (0x6bd98 : word) = Some W_6bd98.
Proof. vm_refl. Qed.
Lemma D_6bd98 : decode_any W_6bd98 = Some (Jal 0 35312, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd9c : bv 32 := 0x000f4517.
Lemma F_6bd9c : fetch_word Asan.M.loaded_segments (0x6bd9c : word) = Some W_6bd9c.
Proof. vm_refl. Qed.
Lemma D_6bd9c : decode_any W_6bd9c = Some (Auipc 10 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bda0 : bv 32 := 0x00650503.
Lemma F_6bda0 : fetch_word Asan.M.loaded_segments (0x6bda0 : word) = Some W_6bda0.
Proof. vm_refl. Qed.
Lemma D_6bda0 : decode_any W_6bda0 = Some (Load SZ1 true 10 10 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bda4 : bv 32 := 0x00a03533.
Lemma F_6bda4 : fetch_word Asan.M.loaded_segments (0x6bda4 : word) = Some W_6bda4.
Proof. vm_refl. Qed.
Lemma D_6bda4 : decode_any W_6bda4 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bda8 : bv 32 := 0x00008067.
Lemma F_6bda8 : fetch_word Asan.M.loaded_segments (0x6bda8 : word) = Some W_6bda8.
Proof. vm_refl. Qed.
Lemma D_6bda8 : decode_any W_6bda8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdac : bv 32 := 0x000f4597.
Lemma F_6bdac : fetch_word Asan.M.loaded_segments (0x6bdac : word) = Some W_6bdac.
Proof. vm_refl. Qed.
Lemma D_6bdac : decode_any W_6bdac = Some (Auipc 11 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdb0 : bv 32 := 0xfea58b23.
Lemma F_6bdb0 : fetch_word Asan.M.loaded_segments (0x6bdb0 : word) = Some W_6bdb0.
Proof. vm_refl. Qed.
Lemma D_6bdb0 : decode_any W_6bdb0 = Some (Store SZ1 11 10 4086, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdb4 : bv 32 := 0x00008067.
Lemma F_6bdb4 : fetch_word Asan.M.loaded_segments (0x6bdb4 : word) = Some W_6bdb4.
Proof. vm_refl. Qed.
Lemma D_6bdb4 : decode_any W_6bdb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
