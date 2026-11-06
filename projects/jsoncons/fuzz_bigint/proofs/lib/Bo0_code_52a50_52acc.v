(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_52a50 : bv 32 := 0xfe010113.
Lemma F_52a50 : fetch_word AsanUbsan.M.loaded_segments (0x52a50 : word) = Some W_52a50.
Proof. vm_refl. Qed.
Lemma D_52a50 : decode_any W_52a50 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a54 : bv 32 := 0x00113c23.
Lemma F_52a54 : fetch_word AsanUbsan.M.loaded_segments (0x52a54 : word) = Some W_52a54.
Proof. vm_refl. Qed.
Lemma D_52a54 : decode_any W_52a54 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a58 : bv 32 := 0x00813823.
Lemma F_52a58 : fetch_word AsanUbsan.M.loaded_segments (0x52a58 : word) = Some W_52a58.
Proof. vm_refl. Qed.
Lemma D_52a58 : decode_any W_52a58 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a5c : bv 32 := 0x00913423.
Lemma F_52a5c : fetch_word AsanUbsan.M.loaded_segments (0x52a5c : word) = Some W_52a5c.
Proof. vm_refl. Qed.
Lemma D_52a5c : decode_any W_52a5c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a60 : bv 32 := 0x01213023.
Lemma F_52a60 : fetch_word AsanUbsan.M.loaded_segments (0x52a60 : word) = Some W_52a60.
Proof. vm_refl. Qed.
Lemma D_52a60 : decode_any W_52a60 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a64 : bv 32 := 0x00050413.
Lemma F_52a64 : fetch_word AsanUbsan.M.loaded_segments (0x52a64 : word) = Some W_52a64.
Proof. vm_refl. Qed.
Lemma D_52a64 : decode_any W_52a64 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a68 : bv 32 := 0x7fc140ef.
Lemma F_52a68 : fetch_word AsanUbsan.M.loaded_segments (0x52a68 : word) = Some W_52a68.
Proof. vm_refl. Qed.
Lemma D_52a68 : decode_any W_52a68 = Some (Jal 1 83964, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a6c : bv 32 := 0x00086597.
Lemma F_52a6c : fetch_word AsanUbsan.M.loaded_segments (0x52a6c : word) = Some W_52a6c.
Proof. vm_refl. Qed.
Lemma D_52a6c : decode_any W_52a6c = Some (Auipc 11 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a70 : bv 32 := 0x8dc5b583.
Lemma F_52a70 : fetch_word AsanUbsan.M.loaded_segments (0x52a70 : word) = Some W_52a70.
Proof. vm_refl. Qed.
Lemma D_52a70 : decode_any W_52a70 = Some (Load SZ8 true 11 11 2268, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a74 : bv 32 := 0x00050913.
Lemma F_52a74 : fetch_word AsanUbsan.M.loaded_segments (0x52a74 : word) = Some W_52a74.
Proof. vm_refl. Qed.
Lemma D_52a74 : decode_any W_52a74 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a78 : bv 32 := 0x00040513.
Lemma F_52a78 : fetch_word AsanUbsan.M.loaded_segments (0x52a78 : word) = Some W_52a78.
Proof. vm_refl. Qed.
Lemma D_52a78 : decode_any W_52a78 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a7c : bv 32 := 0x000580e7.
Lemma F_52a7c : fetch_word AsanUbsan.M.loaded_segments (0x52a7c : word) = Some W_52a7c.
Proof. vm_refl. Qed.
Lemma D_52a7c : decode_any W_52a7c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a80 : bv 32 := 0x00050493.
Lemma F_52a80 : fetch_word AsanUbsan.M.loaded_segments (0x52a80 : word) = Some W_52a80.
Proof. vm_refl. Qed.
Lemma D_52a80 : decode_any W_52a80 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a84 : bv 32 := 0x02090663.
Lemma F_52a84 : fetch_word AsanUbsan.M.loaded_segments (0x52a84 : word) = Some W_52a84.
Proof. vm_refl. Qed.
Lemma D_52a84 : decode_any W_52a84 = Some (Branch BC_EQ 18 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a88 : bv 32 := 0x7dd160ef.
Lemma F_52a88 : fetch_word AsanUbsan.M.loaded_segments (0x52a88 : word) = Some W_52a88.
Proof. vm_refl. Qed.
Lemma D_52a88 : decode_any W_52a88 = Some (Jal 1 94172, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a8c : bv 32 := 0x00050863.
Lemma F_52a8c : fetch_word AsanUbsan.M.loaded_segments (0x52a8c : word) = Some W_52a8c.
Proof. vm_refl. Qed.
Lemma D_52a8c : decode_any W_52a8c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a90 : bv 32 := 0x03053603.
Lemma F_52a90 : fetch_word AsanUbsan.M.loaded_segments (0x52a90 : word) = Some W_52a90.
Proof. vm_refl. Qed.
Lemma D_52a90 : decode_any W_52a90 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a94 : bv 32 := 0x03853683.
Lemma F_52a94 : fetch_word AsanUbsan.M.loaded_segments (0x52a94 : word) = Some W_52a94.
Proof. vm_refl. Qed.
Lemma D_52a94 : decode_any W_52a94 = Some (Load SZ8 true 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a98 : bv 32 := 0x00c0006f.
Lemma F_52a98 : fetch_word AsanUbsan.M.loaded_segments (0x52a98 : word) = Some W_52a98.
Proof. vm_refl. Qed.
Lemma D_52a98 : decode_any W_52a98 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_52a9c : bv 32 := 0x00000613.
Lemma F_52a9c : fetch_word AsanUbsan.M.loaded_segments (0x52a9c : word) = Some W_52a9c.
Proof. vm_refl. Qed.
Lemma D_52a9c : decode_any W_52a9c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52aa0 : bv 32 := 0x00000693.
Lemma F_52aa0 : fetch_word AsanUbsan.M.loaded_segments (0x52aa0 : word) = Some W_52aa0.
Proof. vm_refl. Qed.
Lemma D_52aa0 : decode_any W_52aa0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52aa4 : bv 32 := 0x00040513.
Lemma F_52aa4 : fetch_word AsanUbsan.M.loaded_segments (0x52aa4 : word) = Some W_52aa4.
Proof. vm_refl. Qed.
Lemma D_52aa4 : decode_any W_52aa4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52aa8 : bv 32 := 0x00048593.
Lemma F_52aa8 : fetch_word AsanUbsan.M.loaded_segments (0x52aa8 : word) = Some W_52aa8.
Proof. vm_refl. Qed.
Lemma D_52aa8 : decode_any W_52aa8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52aac : bv 32 := 0x6cc240ef.
Lemma F_52aac : fetch_word AsanUbsan.M.loaded_segments (0x52aac : word) = Some W_52aac.
Proof. vm_refl. Qed.
Lemma D_52aac : decode_any W_52aac = Some (Jal 1 149196, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ab0 : bv 32 := 0x00048513.
Lemma F_52ab0 : fetch_word AsanUbsan.M.loaded_segments (0x52ab0 : word) = Some W_52ab0.
Proof. vm_refl. Qed.
Lemma D_52ab0 : decode_any W_52ab0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ab4 : bv 32 := 0x01813083.
Lemma F_52ab4 : fetch_word AsanUbsan.M.loaded_segments (0x52ab4 : word) = Some W_52ab4.
Proof. vm_refl. Qed.
Lemma D_52ab4 : decode_any W_52ab4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ab8 : bv 32 := 0x01013403.
Lemma F_52ab8 : fetch_word AsanUbsan.M.loaded_segments (0x52ab8 : word) = Some W_52ab8.
Proof. vm_refl. Qed.
Lemma D_52ab8 : decode_any W_52ab8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_52abc : bv 32 := 0x00813483.
Lemma F_52abc : fetch_word AsanUbsan.M.loaded_segments (0x52abc : word) = Some W_52abc.
Proof. vm_refl. Qed.
Lemma D_52abc : decode_any W_52abc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ac0 : bv 32 := 0x00013903.
Lemma F_52ac0 : fetch_word AsanUbsan.M.loaded_segments (0x52ac0 : word) = Some W_52ac0.
Proof. vm_refl. Qed.
Lemma D_52ac0 : decode_any W_52ac0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ac4 : bv 32 := 0x02010113.
Lemma F_52ac4 : fetch_word AsanUbsan.M.loaded_segments (0x52ac4 : word) = Some W_52ac4.
Proof. vm_refl. Qed.
Lemma D_52ac4 : decode_any W_52ac4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_52ac8 : bv 32 := 0x00008067.
Lemma F_52ac8 : fetch_word AsanUbsan.M.loaded_segments (0x52ac8 : word) = Some W_52ac8.
Proof. vm_refl. Qed.
Lemma D_52ac8 : decode_any W_52ac8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
