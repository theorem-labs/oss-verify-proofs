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

Definition W_9a610 : bv 32 := 0xfe010113.
Lemma F_9a610 : fetch_word Asan.M.loaded_segments (0x9a660 : word) = Some W_9a610.
Proof. vm_refl. Qed.
Lemma D_9a610 : decode_any W_9a610 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a614 : bv 32 := 0x00113c23.
Lemma F_9a614 : fetch_word Asan.M.loaded_segments (0x9a664 : word) = Some W_9a614.
Proof. vm_refl. Qed.
Lemma D_9a614 : decode_any W_9a614 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a618 : bv 32 := 0x00813823.
Lemma F_9a618 : fetch_word Asan.M.loaded_segments (0x9a668 : word) = Some W_9a618.
Proof. vm_refl. Qed.
Lemma D_9a618 : decode_any W_9a618 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a61c : bv 32 := 0x00060593.
Lemma F_9a61c : fetch_word Asan.M.loaded_segments (0x9a66c : word) = Some W_9a61c.
Proof. vm_refl. Qed.
Lemma D_9a61c : decode_any W_9a61c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a620 : bv 32 := 0x00050413.
Lemma F_9a620 : fetch_word Asan.M.loaded_segments (0x9a670 : word) = Some W_9a620.
Proof. vm_refl. Qed.
Lemma D_9a620 : decode_any W_9a620 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a624 : bv 32 := 0x00d53023.
Lemma F_9a624 : fetch_word Asan.M.loaded_segments (0x9a674 : word) = Some W_9a624.
Proof. vm_refl. Qed.
Lemma D_9a624 : decode_any W_9a624 = Some (Store SZ8 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a628 : bv 32 := 0x00013423.
Lemma F_9a628 : fetch_word Asan.M.loaded_segments (0x9a678 : word) = Some W_9a628.
Proof. vm_refl. Qed.
Lemma D_9a628 : decode_any W_9a628 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a62c : bv 32 := 0x00179517.
Lemma F_9a62c : fetch_word Asan.M.loaded_segments (0x9a67c : word) = Some W_9a62c.
Proof. vm_refl. Qed.
Lemma D_9a62c : decode_any W_9a62c = Some (Auipc 10 377, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a630 : bv 32 := 0x24c50513.
Lemma F_9a630 : fetch_word Asan.M.loaded_segments (0x9a680 : word) = Some W_9a630.
Proof. vm_refl. Qed.
Lemma D_9a630 : decode_any W_9a630 = Some (OpImm ALU_ADD 10 10 588, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a634 : bv 32 := 0x00810613.
Lemma F_9a634 : fetch_word Asan.M.loaded_segments (0x9a684 : word) = Some W_9a634.
Proof. vm_refl. Qed.
Lemma D_9a634 : decode_any W_9a634 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a638 : bv 32 := 0xcc5fd0ef.
Lemma F_9a638 : fetch_word Asan.M.loaded_segments (0x9a688 : word) = Some W_9a638.
Proof. vm_refl. Qed.
Lemma D_9a638 : decode_any W_9a638 = Some (Jal 1 2088132, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a63c : bv 32 := 0x00813583.
Lemma F_9a63c : fetch_word Asan.M.loaded_segments (0x9a68c : word) = Some W_9a63c.
Proof. vm_refl. Qed.
Lemma D_9a63c : decode_any W_9a63c = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a640 : bv 32 := 0x00a42623.
Lemma F_9a640 : fetch_word Asan.M.loaded_segments (0x9a690 : word) = Some W_9a640.
Proof. vm_refl. Qed.
Lemma D_9a640 : decode_any W_9a640 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a644 : bv 32 := 0x00059a63.
Lemma F_9a644 : fetch_word Asan.M.loaded_segments (0x9a694 : word) = Some W_9a644.
Proof. vm_refl. Qed.
Lemma D_9a644 : decode_any W_9a644 = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a648 : bv 32 := 0x01813083.
Lemma F_9a648 : fetch_word Asan.M.loaded_segments (0x9a698 : word) = Some W_9a648.
Proof. vm_refl. Qed.
Lemma D_9a648 : decode_any W_9a648 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a64c : bv 32 := 0x01013403.
Lemma F_9a64c : fetch_word Asan.M.loaded_segments (0x9a69c : word) = Some W_9a64c.
Proof. vm_refl. Qed.
Lemma D_9a64c : decode_any W_9a64c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a650 : bv 32 := 0x02010113.
Lemma F_9a650 : fetch_word Asan.M.loaded_segments (0x9a6a0 : word) = Some W_9a650.
Proof. vm_refl. Qed.
Lemma D_9a650 : decode_any W_9a650 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9a654 : bv 32 := 0x00008067.
Lemma F_9a654 : fetch_word Asan.M.loaded_segments (0x9a6a4 : word) = Some W_9a654.
Proof. vm_refl. Qed.
Lemma D_9a654 : decode_any W_9a654 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
