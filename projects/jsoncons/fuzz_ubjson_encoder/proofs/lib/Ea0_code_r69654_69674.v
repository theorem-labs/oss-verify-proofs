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

Definition W_84218 : bv 32 := 0xff010113.
Lemma F_84218 : fetch_word Asan.M.loaded_segments (0x84268 : word) = Some W_84218.
Proof. vm_refl. Qed.
Lemma D_84218 : decode_any W_84218 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_8421c : bv 32 := 0x00113423.
Lemma F_8421c : fetch_word Asan.M.loaded_segments (0x8426c : word) = Some W_8421c.
Proof. vm_refl. Qed.
Lemma D_8421c : decode_any W_8421c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84220 : bv 32 := 0xe78f80ef.
Lemma F_84220 : fetch_word Asan.M.loaded_segments (0x84270 : word) = Some W_84220.
Proof. vm_refl. Qed.
Lemma D_84220 : decode_any W_84220 = Some (Jal 1 2066040, 4%Z).
Proof. vm_refl. Qed.

Definition W_84224 : bv 32 := 0x00050463.
Lemma F_84224 : fetch_word Asan.M.loaded_segments (0x84274 : word) = Some W_84224.
Proof. vm_refl. Qed.
Lemma D_84224 : decode_any W_84224 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84228 : bv 32 := 0x09853503.
Lemma F_84228 : fetch_word Asan.M.loaded_segments (0x84278 : word) = Some W_84228.
Proof. vm_refl. Qed.
Lemma D_84228 : decode_any W_84228 = Some (Load SZ8 true 10 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8422c : bv 32 := 0x00813083.
Lemma F_8422c : fetch_word Asan.M.loaded_segments (0x8427c : word) = Some W_8422c.
Proof. vm_refl. Qed.
Lemma D_8422c : decode_any W_8422c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_84230 : bv 32 := 0x01010113.
Lemma F_84230 : fetch_word Asan.M.loaded_segments (0x84280 : word) = Some W_84230.
Proof. vm_refl. Qed.
Lemma D_84230 : decode_any W_84230 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_84234 : bv 32 := 0x00008067.
Lemma F_84234 : fetch_word Asan.M.loaded_segments (0x84284 : word) = Some W_84234.
Proof. vm_refl. Qed.
Lemma D_84234 : decode_any W_84234 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
