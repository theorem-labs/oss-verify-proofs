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

Definition W_7fbc0 : bv 32 := 0xfe010113.
Lemma F_7fbc0 : fetch_word Asan.M.loaded_segments (0x7fbc0 : word) = Some W_7fbc0.
Proof. vm_refl. Qed.
Lemma D_7fbc0 : decode_any W_7fbc0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbc4 : bv 32 := 0x00113c23.
Lemma F_7fbc4 : fetch_word Asan.M.loaded_segments (0x7fbc4 : word) = Some W_7fbc4.
Proof. vm_refl. Qed.
Lemma D_7fbc4 : decode_any W_7fbc4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbc8 : bv 32 := 0x00813823.
Lemma F_7fbc8 : fetch_word Asan.M.loaded_segments (0x7fbc8 : word) = Some W_7fbc8.
Proof. vm_refl. Qed.
Lemma D_7fbc8 : decode_any W_7fbc8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbcc : bv 32 := 0x00060593.
Lemma F_7fbcc : fetch_word Asan.M.loaded_segments (0x7fbcc : word) = Some W_7fbcc.
Proof. vm_refl. Qed.
Lemma D_7fbcc : decode_any W_7fbcc = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd0 : bv 32 := 0x00050413.
Lemma F_7fbd0 : fetch_word Asan.M.loaded_segments (0x7fbd0 : word) = Some W_7fbd0.
Proof. vm_refl. Qed.
Lemma D_7fbd0 : decode_any W_7fbd0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd4 : bv 32 := 0x00d53023.
Lemma F_7fbd4 : fetch_word Asan.M.loaded_segments (0x7fbd4 : word) = Some W_7fbd4.
Proof. vm_refl. Qed.
Lemma D_7fbd4 : decode_any W_7fbd4 = Some (Store SZ8 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbd8 : bv 32 := 0x00013423.
Lemma F_7fbd8 : fetch_word Asan.M.loaded_segments (0x7fbd8 : word) = Some W_7fbd8.
Proof. vm_refl. Qed.
Lemma D_7fbd8 : decode_any W_7fbd8 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbdc : bv 32 := 0x00130517.
Lemma F_7fbdc : fetch_word Asan.M.loaded_segments (0x7fbdc : word) = Some W_7fbdc.
Proof. vm_refl. Qed.
Lemma D_7fbdc : decode_any W_7fbdc = Some (Auipc 10 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe0 : bv 32 := 0xe2c50513.
Lemma F_7fbe0 : fetch_word Asan.M.loaded_segments (0x7fbe0 : word) = Some W_7fbe0.
Proof. vm_refl. Qed.
Lemma D_7fbe0 : decode_any W_7fbe0 = Some (OpImm ALU_ADD 10 10 3628, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe4 : bv 32 := 0x00810613.
Lemma F_7fbe4 : fetch_word Asan.M.loaded_segments (0x7fbe4 : word) = Some W_7fbe4.
Proof. vm_refl. Qed.
Lemma D_7fbe4 : decode_any W_7fbe4 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbe8 : bv 32 := 0xcc5fd0ef.
Lemma F_7fbe8 : fetch_word Asan.M.loaded_segments (0x7fbe8 : word) = Some W_7fbe8.
Proof. vm_refl. Qed.
Lemma D_7fbe8 : decode_any W_7fbe8 = Some (Jal 1 2088132, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbec : bv 32 := 0x00813583.
Lemma F_7fbec : fetch_word Asan.M.loaded_segments (0x7fbec : word) = Some W_7fbec.
Proof. vm_refl. Qed.
Lemma D_7fbec : decode_any W_7fbec = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf0 : bv 32 := 0x00a42623.
Lemma F_7fbf0 : fetch_word Asan.M.loaded_segments (0x7fbf0 : word) = Some W_7fbf0.
Proof. vm_refl. Qed.
Lemma D_7fbf0 : decode_any W_7fbf0 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf4 : bv 32 := 0x00059a63.
Lemma F_7fbf4 : fetch_word Asan.M.loaded_segments (0x7fbf4 : word) = Some W_7fbf4.
Proof. vm_refl. Qed.
Lemma D_7fbf4 : decode_any W_7fbf4 = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbf8 : bv 32 := 0x01813083.
Lemma F_7fbf8 : fetch_word Asan.M.loaded_segments (0x7fbf8 : word) = Some W_7fbf8.
Proof. vm_refl. Qed.
Lemma D_7fbf8 : decode_any W_7fbf8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fbfc : bv 32 := 0x01013403.
Lemma F_7fbfc : fetch_word Asan.M.loaded_segments (0x7fbfc : word) = Some W_7fbfc.
Proof. vm_refl. Qed.
Lemma D_7fbfc : decode_any W_7fbfc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc00 : bv 32 := 0x02010113.
Lemma F_7fc00 : fetch_word Asan.M.loaded_segments (0x7fc00 : word) = Some W_7fc00.
Proof. vm_refl. Qed.
Lemma D_7fc00 : decode_any W_7fc00 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc04 : bv 32 := 0x00008067.
Lemma F_7fc04 : fetch_word Asan.M.loaded_segments (0x7fc04 : word) = Some W_7fc04.
Proof. vm_refl. Qed.
Lemma D_7fc04 : decode_any W_7fc04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc08 : bv 32 := 0x014000ef.
Lemma F_7fc08 : fetch_word Asan.M.loaded_segments (0x7fc08 : word) = Some W_7fc08.
Proof. vm_refl. Qed.
Lemma D_7fc08 : decode_any W_7fc08 = Some (Jal 1 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc0c : bv 32 := 0x01813083.
Lemma F_7fc0c : fetch_word Asan.M.loaded_segments (0x7fc0c : word) = Some W_7fc0c.
Proof. vm_refl. Qed.
Lemma D_7fc0c : decode_any W_7fc0c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc10 : bv 32 := 0x01013403.
Lemma F_7fc10 : fetch_word Asan.M.loaded_segments (0x7fc10 : word) = Some W_7fc10.
Proof. vm_refl. Qed.
Lemma D_7fc10 : decode_any W_7fc10 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc14 : bv 32 := 0x02010113.
Lemma F_7fc14 : fetch_word Asan.M.loaded_segments (0x7fc14 : word) = Some W_7fc14.
Proof. vm_refl. Qed.
Lemma D_7fc14 : decode_any W_7fc14 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fc18 : bv 32 := 0x00008067.
Lemma F_7fc18 : fetch_word Asan.M.loaded_segments (0x7fc18 : word) = Some W_7fc18.
Proof. vm_refl. Qed.
Lemma D_7fc18 : decode_any W_7fc18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
