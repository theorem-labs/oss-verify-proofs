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

Definition W_84a40 : bv 32 := 0xff010113.
Lemma F_84a40 : fetch_word AsanUbsan.M.loaded_segments (0x84a90 : word) = Some W_84a40.
Proof. vm_refl. Qed.
Lemma D_84a40 : decode_any W_84a40 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a44 : bv 32 := 0x00113423.
Lemma F_84a44 : fetch_word AsanUbsan.M.loaded_segments (0x84a94 : word) = Some W_84a44.
Proof. vm_refl. Qed.
Lemma D_84a44 : decode_any W_84a44 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a48 : bv 32 := 0xe78f80ef.
Lemma F_84a48 : fetch_word AsanUbsan.M.loaded_segments (0x84a98 : word) = Some W_84a48.
Proof. vm_refl. Qed.
Lemma D_84a48 : decode_any W_84a48 = Some (Jal 1 2066040, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a4c : bv 32 := 0x00050463.
Lemma F_84a4c : fetch_word AsanUbsan.M.loaded_segments (0x84a9c : word) = Some W_84a4c.
Proof. vm_refl. Qed.
Lemma D_84a4c : decode_any W_84a4c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a50 : bv 32 := 0x09853503.
Lemma F_84a50 : fetch_word AsanUbsan.M.loaded_segments (0x84aa0 : word) = Some W_84a50.
Proof. vm_refl. Qed.
Lemma D_84a50 : decode_any W_84a50 = Some (Load SZ8 true 10 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a54 : bv 32 := 0x00813083.
Lemma F_84a54 : fetch_word AsanUbsan.M.loaded_segments (0x84aa4 : word) = Some W_84a54.
Proof. vm_refl. Qed.
Lemma D_84a54 : decode_any W_84a54 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a58 : bv 32 := 0x01010113.
Lemma F_84a58 : fetch_word AsanUbsan.M.loaded_segments (0x84aa8 : word) = Some W_84a58.
Proof. vm_refl. Qed.
Lemma D_84a58 : decode_any W_84a58 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84a5c : bv 32 := 0x00008067.
Lemma F_84a5c : fetch_word AsanUbsan.M.loaded_segments (0x84aac : word) = Some W_84a5c.
Proof. vm_refl. Qed.
Lemma D_84a5c : decode_any W_84a5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
