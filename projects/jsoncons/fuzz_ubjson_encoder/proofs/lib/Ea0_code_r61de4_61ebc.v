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

Definition W_7c72c : bv 32 := 0xfb010113.
Lemma F_7c72c : fetch_word Asan.M.loaded_segments (0x7c77c : word) = Some W_7c72c.
Proof. vm_refl. Qed.
Lemma D_7c72c : decode_any W_7c72c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c730 : bv 32 := 0x04113423.
Lemma F_7c730 : fetch_word Asan.M.loaded_segments (0x7c780 : word) = Some W_7c730.
Proof. vm_refl. Qed.
Lemma D_7c730 : decode_any W_7c730 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c734 : bv 32 := 0x04813023.
Lemma F_7c734 : fetch_word Asan.M.loaded_segments (0x7c784 : word) = Some W_7c734.
Proof. vm_refl. Qed.
Lemma D_7c734 : decode_any W_7c734 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c738 : bv 32 := 0x000bd517.
Lemma F_7c738 : fetch_word Asan.M.loaded_segments (0x7c788 : word) = Some W_7c738.
Proof. vm_refl. Qed.
Lemma D_7c738 : decode_any W_7c738 = Some (Auipc 10 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c73c : bv 32 := 0xa7053503.
Lemma F_7c73c : fetch_word Asan.M.loaded_segments (0x7c78c : word) = Some W_7c73c.
Proof. vm_refl. Qed.
Lemma D_7c73c : decode_any W_7c73c = Some (Load SZ8 true 10 10 2672, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c740 : bv 32 := 0x0a051463.
Lemma F_7c740 : fetch_word Asan.M.loaded_segments (0x7c790 : word) = Some W_7c740.
Proof. vm_refl. Qed.
Lemma D_7c740 : decode_any W_7c740 = Some (Branch BC_NE 10 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7e8 : bv 32 := 0x00000513.
Lemma F_7c7e8 : fetch_word Asan.M.loaded_segments (0x7c838 : word) = Some W_7c7e8.
Proof. vm_refl. Qed.
Lemma D_7c7e8 : decode_any W_7c7e8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7ec : bv 32 := 0x04813083.
Lemma F_7c7ec : fetch_word Asan.M.loaded_segments (0x7c83c : word) = Some W_7c7ec.
Proof. vm_refl. Qed.
Lemma D_7c7ec : decode_any W_7c7ec = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7f0 : bv 32 := 0x04013403.
Lemma F_7c7f0 : fetch_word Asan.M.loaded_segments (0x7c840 : word) = Some W_7c7f0.
Proof. vm_refl. Qed.
Lemma D_7c7f0 : decode_any W_7c7f0 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7f4 : bv 32 := 0x05010113.
Lemma F_7c7f4 : fetch_word Asan.M.loaded_segments (0x7c844 : word) = Some W_7c7f4.
Proof. vm_refl. Qed.
Lemma D_7c7f4 : decode_any W_7c7f4 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c7f8 : bv 32 := 0x00008067.
Lemma F_7c7f8 : fetch_word Asan.M.loaded_segments (0x7c848 : word) = Some W_7c7f8.
Proof. vm_refl. Qed.
Lemma D_7c7f8 : decode_any W_7c7f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
