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

Definition W_69a64 : bv 32 := 0xff010113.
Lemma F_69a64 : fetch_word AsanUbsan.M.loaded_segments (0x69a64 : word) = Some W_69a64.
Proof. vm_refl. Qed.
Lemma D_69a64 : decode_any W_69a64 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a68 : bv 32 := 0x00113423.
Lemma F_69a68 : fetch_word AsanUbsan.M.loaded_segments (0x69a68 : word) = Some W_69a68.
Proof. vm_refl. Qed.
Lemma D_69a68 : decode_any W_69a68 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a6c : bv 32 := 0x8f5f80ef.
Lemma F_69a6c : fetch_word AsanUbsan.M.loaded_segments (0x69a6c : word) = Some W_69a6c.
Proof. vm_refl. Qed.
Lemma D_69a6c : decode_any W_69a6c = Some (Jal 1 2066676, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a70 : bv 32 := 0x00050463.
Lemma F_69a70 : fetch_word AsanUbsan.M.loaded_segments (0x69a70 : word) = Some W_69a70.
Proof. vm_refl. Qed.
Lemma D_69a70 : decode_any W_69a70 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a74 : bv 32 := 0x09853503.
Lemma F_69a74 : fetch_word AsanUbsan.M.loaded_segments (0x69a74 : word) = Some W_69a74.
Proof. vm_refl. Qed.
Lemma D_69a74 : decode_any W_69a74 = Some (Load SZ8 true 10 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a78 : bv 32 := 0x00813083.
Lemma F_69a78 : fetch_word AsanUbsan.M.loaded_segments (0x69a78 : word) = Some W_69a78.
Proof. vm_refl. Qed.
Lemma D_69a78 : decode_any W_69a78 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a7c : bv 32 := 0x01010113.
Lemma F_69a7c : fetch_word AsanUbsan.M.loaded_segments (0x69a7c : word) = Some W_69a7c.
Proof. vm_refl. Qed.
Lemma D_69a7c : decode_any W_69a7c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a80 : bv 32 := 0x00008067.
Lemma F_69a80 : fetch_word AsanUbsan.M.loaded_segments (0x69a80 : word) = Some W_69a80.
Proof. vm_refl. Qed.
Lemma D_69a80 : decode_any W_69a80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
