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

Definition W_a7df8 : bv 32 := 0x00092517.
Lemma F_a7df8 : fetch_word Asan.M.loaded_segments (0xa7e48 : word) = Some W_a7df8.
Proof. vm_refl. Qed.
Lemma D_a7df8 : decode_any W_a7df8 = Some (Auipc 10 146, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7dfc : bv 32 := 0xfd053503.
Lemma F_a7dfc : fetch_word Asan.M.loaded_segments (0xa7e4c : word) = Some W_a7dfc.
Proof. vm_refl. Qed.
Lemma D_a7dfc : decode_any W_a7dfc = Some (Load SZ8 true 10 10 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7e00 : bv 32 := 0x00450533.
Lemma F_a7e00 : fetch_word Asan.M.loaded_segments (0xa7e50 : word) = Some W_a7e00.
Proof. vm_refl. Qed.
Lemma D_a7e00 : decode_any W_a7e00 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7e04 : bv 32 := 0x00052503.
Lemma F_a7e04 : fetch_word Asan.M.loaded_segments (0xa7e54 : word) = Some W_a7e04.
Proof. vm_refl. Qed.
Lemma D_a7e04 : decode_any W_a7e04 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7e08 : bv 32 := 0x00a02533.
Lemma F_a7e08 : fetch_word Asan.M.loaded_segments (0xa7e58 : word) = Some W_a7e08.
Proof. vm_refl. Qed.
Lemma D_a7e08 : decode_any W_a7e08 = Some (Op ALU_SLT 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a7e0c : bv 32 := 0x00008067.
Lemma F_a7e0c : fetch_word Asan.M.loaded_segments (0xa7e5c : word) = Some W_a7e0c.
Proof. vm_refl. Qed.
Lemma D_a7e0c : decode_any W_a7e0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
