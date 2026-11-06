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

Definition W_11a710 : bv 32 := 0xfffff5b7.
Lemma F_11a710 : fetch_word Asan.M.loaded_segments (0x11a754 : word) = Some W_11a710.
Proof. vm_refl. Qed.
Lemma D_11a710 : decode_any W_11a710 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a714 : bv 32 := 0x0015859b.
Lemma F_11a714 : fetch_word Asan.M.loaded_segments (0x11a758 : word) = Some W_11a714.
Proof. vm_refl. Qed.
Lemma D_11a714 : decode_any W_11a714 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a718 : bv 32 := 0x02b56663.
Lemma F_11a718 : fetch_word Asan.M.loaded_segments (0x11a75c : word) = Some W_11a718.
Proof. vm_refl. Qed.
Lemma D_11a718 : decode_any W_11a718 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a71c : bv 32 := 0xff010113.
Lemma F_11a71c : fetch_word Asan.M.loaded_segments (0x11a760 : word) = Some W_11a71c.
Proof. vm_refl. Qed.
Lemma D_11a71c : decode_any W_11a71c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a720 : bv 32 := 0x00113423.
Lemma F_11a720 : fetch_word Asan.M.loaded_segments (0x11a764 : word) = Some W_11a720.
Proof. vm_refl. Qed.
Lemma D_11a720 : decode_any W_11a720 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a724 : bv 32 := 0x00813023.
Lemma F_11a724 : fetch_word Asan.M.loaded_segments (0x11a768 : word) = Some W_11a724.
Proof. vm_refl. Qed.
Lemma D_11a724 : decode_any W_11a724 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a728 : bv 32 := 0x40a0043b.
Lemma F_11a728 : fetch_word Asan.M.loaded_segments (0x11a76c : word) = Some W_11a728.
Proof. vm_refl. Qed.
Lemma D_11a728 : decode_any W_11a728 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a72c : bv 32 := 0x8b9ff0ef.
Lemma F_11a72c : fetch_word Asan.M.loaded_segments (0x11a770 : word) = Some W_11a72c.
Proof. vm_refl. Qed.
Lemma D_11a72c : decode_any W_11a72c = Some (Jal 1 2095288, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a730 : bv 32 := 0x00852023.
Lemma F_11a730 : fetch_word Asan.M.loaded_segments (0x11a774 : word) = Some W_11a730.
Proof. vm_refl. Qed.
Lemma D_11a730 : decode_any W_11a730 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a734 : bv 32 := 0xfff00513.
Lemma F_11a734 : fetch_word Asan.M.loaded_segments (0x11a778 : word) = Some W_11a734.
Proof. vm_refl. Qed.
Lemma D_11a734 : decode_any W_11a734 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a738 : bv 32 := 0x00813083.
Lemma F_11a738 : fetch_word Asan.M.loaded_segments (0x11a77c : word) = Some W_11a738.
Proof. vm_refl. Qed.
Lemma D_11a738 : decode_any W_11a738 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a73c : bv 32 := 0x00013403.
Lemma F_11a73c : fetch_word Asan.M.loaded_segments (0x11a780 : word) = Some W_11a73c.
Proof. vm_refl. Qed.
Lemma D_11a73c : decode_any W_11a73c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a740 : bv 32 := 0x01010113.
Lemma F_11a740 : fetch_word Asan.M.loaded_segments (0x11a784 : word) = Some W_11a740.
Proof. vm_refl. Qed.
Lemma D_11a740 : decode_any W_11a740 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_11a744 : bv 32 := 0x00008067.
Lemma F_11a744 : fetch_word Asan.M.loaded_segments (0x11a788 : word) = Some W_11a744.
Proof. vm_refl. Qed.
Lemma D_11a744 : decode_any W_11a744 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
