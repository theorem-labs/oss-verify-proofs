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

Definition W_8c5d8 : bv 32 := 0x000ad697.
Lemma F_8c5d8 : fetch_word Asan.M.loaded_segments (0x8c628 : word) = Some W_8c5d8.
Proof. vm_refl. Qed.
Lemma D_8c5d8 : decode_any W_8c5d8 = Some (Auipc 13 173, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5dc : bv 32 := 0xbd06b683.
Lemma F_8c5dc : fetch_word Asan.M.loaded_segments (0x8c62c : word) = Some W_8c5dc.
Proof. vm_refl. Qed.
Lemma D_8c5dc : decode_any W_8c5dc = Some (Load SZ8 true 13 13 3024, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5e0 : bv 32 := 0x00068a63.
Lemma F_8c5e0 : fetch_word Asan.M.loaded_segments (0x8c630 : word) = Some W_8c5e0.
Proof. vm_refl. Qed.
Lemma D_8c5e0 : decode_any W_8c5e0 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5e4 : bv 32 := 0x00400693.
Lemma F_8c5e4 : fetch_word Asan.M.loaded_segments (0x8c634 : word) = Some W_8c5e4.
Proof. vm_refl. Qed.
Lemma D_8c5e4 : decode_any W_8c5e4 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5e8 : bv 32 := 0x00d60663.
Lemma F_8c5e8 : fetch_word Asan.M.loaded_segments (0x8c638 : word) = Some W_8c5e8.
Proof. vm_refl. Qed.
Lemma D_8c5e8 : decode_any W_8c5e8 = Some (Branch BC_EQ 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5f4 : bv 32 := 0x0e900893.
Lemma F_8c5f4 : fetch_word Asan.M.loaded_segments (0x8c644 : word) = Some W_8c5f4.
Proof. vm_refl. Qed.
Lemma D_8c5f4 : decode_any W_8c5f4 = Some (OpImm ALU_ADD 17 0 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5f8 : bv 32 := 0x00000073.
Lemma F_8c5f8 : fetch_word Asan.M.loaded_segments (0x8c648 : word) = Some W_8c5f8.
Proof. vm_refl. Qed.
Lemma D_8c5f8 : decode_any W_8c5f8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_8c5f8 : is_ecall W_8c5f8 = true.
Proof. reflexivity. Qed.

Definition W_8c5fc : bv 32 := 0x0005051b.
Lemma F_8c5fc : fetch_word Asan.M.loaded_segments (0x8c64c : word) = Some W_8c5fc.
Proof. vm_refl. Qed.
Lemma D_8c5fc : decode_any W_8c5fc = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c600 : bv 32 := 0x00008067.
Lemma F_8c600 : fetch_word Asan.M.loaded_segments (0x8c650 : word) = Some W_8c600.
Proof. vm_refl. Qed.
Lemma D_8c600 : decode_any W_8c600 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
