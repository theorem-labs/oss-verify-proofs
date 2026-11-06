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

Definition W_71b40 : bv 32 := 0xfffff637.
Lemma F_71b40 : fetch_word Asan.M.loaded_segments (0x71b40 : word) = Some W_71b40.
Proof. vm_refl. Qed.
Lemma D_71b40 : decode_any W_71b40 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b44 : bv 32 := 0x0016069b.
Lemma F_71b44 : fetch_word Asan.M.loaded_segments (0x71b44 : word) = Some W_71b44.
Proof. vm_refl. Qed.
Lemma D_71b44 : decode_any W_71b44 = Some (OpImm32 13 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b48 : bv 32 := 0x00d56863.
Lemma F_71b48 : fetch_word Asan.M.loaded_segments (0x71b48 : word) = Some W_71b48.
Proof. vm_refl. Qed.
Lemma D_71b48 : decode_any W_71b48 = Some (Branch BC_LTU 10 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b4c : bv 32 := 0x00058663.
Lemma F_71b4c : fetch_word Asan.M.loaded_segments (0x71b4c : word) = Some W_71b4c.
Proof. vm_refl. Qed.
Lemma D_71b4c : decode_any W_71b4c = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b50 : bv 32 := 0x40a006bb.
Lemma F_71b50 : fetch_word Asan.M.loaded_segments (0x71b50 : word) = Some W_71b50.
Proof. vm_refl. Qed.
Lemma D_71b50 : decode_any W_71b50 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b54 : bv 32 := 0x00d5a023.
Lemma F_71b54 : fetch_word Asan.M.loaded_segments (0x71b54 : word) = Some W_71b54.
Proof. vm_refl. Qed.
Lemma D_71b54 : decode_any W_71b54 = Some (Store SZ4 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b58 : bv 32 := 0x00a63533.
Lemma F_71b58 : fetch_word Asan.M.loaded_segments (0x71b58 : word) = Some W_71b58.
Proof. vm_refl. Qed.
Lemma D_71b58 : decode_any W_71b58 = Some (Op ALU_SLTU 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b5c : bv 32 := 0x00008067.
Lemma F_71b5c : fetch_word Asan.M.loaded_segments (0x71b5c : word) = Some W_71b5c.
Proof. vm_refl. Qed.
Lemma D_71b5c : decode_any W_71b5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b60 : bv 32 := 0x0de00893.
Lemma F_71b60 : fetch_word Asan.M.loaded_segments (0x71b60 : word) = Some W_71b60.
Proof. vm_refl. Qed.
Lemma D_71b60 : decode_any W_71b60 = Some (OpImm ALU_ADD 17 0 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b64 : bv 32 := 0x00000073.
Lemma F_71b64 : fetch_word Asan.M.loaded_segments (0x71b64 : word) = Some W_71b64.
Proof. vm_refl. Qed.
Lemma D_71b64 : decode_any W_71b64 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_71b64 : is_ecall W_71b64 = true.
Proof. reflexivity. Qed.

Definition W_71b68 : bv 32 := 0x00008067.
Lemma F_71b68 : fetch_word Asan.M.loaded_segments (0x71b68 : word) = Some W_71b68.
Proof. vm_refl. Qed.
Lemma D_71b68 : decode_any W_71b68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b6c : bv 32 := 0x0d700893.
Lemma F_71b6c : fetch_word Asan.M.loaded_segments (0x71b6c : word) = Some W_71b6c.
Proof. vm_refl. Qed.
Lemma D_71b6c : decode_any W_71b6c = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b70 : bv 32 := 0x00000073.
Lemma F_71b70 : fetch_word Asan.M.loaded_segments (0x71b70 : word) = Some W_71b70.
Proof. vm_refl. Qed.
Lemma D_71b70 : decode_any W_71b70 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_71b70 : is_ecall W_71b70 = true.
Proof. reflexivity. Qed.

Definition W_71b74 : bv 32 := 0x00008067.
Lemma F_71b74 : fetch_word Asan.M.loaded_segments (0x71b74 : word) = Some W_71b74.
Proof. vm_refl. Qed.
Lemma D_71b74 : decode_any W_71b74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
