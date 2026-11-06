(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6c614 : bv 32 := 0x00008067.
Lemma F_6c614 : fetch_word Ubsan.M.loaded_segments (0x6c654 : word) = Some W_6c614.
Proof. vm_refl. Qed.
Lemma D_6c614 : decode_any W_6c614 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c704 : bv 32 := 0x00008067.
Lemma F_6c704 : fetch_word Ubsan.M.loaded_segments (0x6c744 : word) = Some W_6c704.
Proof. vm_refl. Qed.
Lemma D_6c704 : decode_any W_6c704 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c724 : bv 32 := 0x00008067.
Lemma F_6c724 : fetch_word Ubsan.M.loaded_segments (0x6c764 : word) = Some W_6c724.
Proof. vm_refl. Qed.
Lemma D_6c724 : decode_any W_6c724 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c748 : bv 32 := 0x00008067.
Lemma F_6c748 : fetch_word Ubsan.M.loaded_segments (0x6c788 : word) = Some W_6c748.
Proof. vm_refl. Qed.
Lemma D_6c748 : decode_any W_6c748 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c770 : bv 32 := 0x00008067.
Lemma F_6c770 : fetch_word Ubsan.M.loaded_segments (0x6c7b0 : word) = Some W_6c770.
Proof. vm_refl. Qed.
Lemma D_6c770 : decode_any W_6c770 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c794 : bv 32 := 0x00008067.
Lemma F_6c794 : fetch_word Ubsan.M.loaded_segments (0x6c7d4 : word) = Some W_6c794.
Proof. vm_refl. Qed.
Lemma D_6c794 : decode_any W_6c794 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c7bc : bv 32 := 0x00008067.
Lemma F_6c7bc : fetch_word Ubsan.M.loaded_segments (0x6c7fc : word) = Some W_6c7bc.
Proof. vm_refl. Qed.
Lemma D_6c7bc : decode_any W_6c7bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
