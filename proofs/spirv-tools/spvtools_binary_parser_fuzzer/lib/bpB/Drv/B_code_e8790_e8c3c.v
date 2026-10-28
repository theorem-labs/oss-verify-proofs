(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_e8910 : bv 32 := 0x000ac663.
Lemma F_e8910 : fetch_word AsanUbsan.M.loaded_segments (0xe8568 : word) = Some W_e8910.
Proof. vm_refl. Qed.
Lemma D_e8910 : decode_any W_e8910 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_e8914 : bv 32 := 0x00050413.
Lemma F_e8914 : fetch_word AsanUbsan.M.loaded_segments (0xe856c : word) = Some W_e8914.
Proof. vm_refl. Qed.
Lemma D_e8914 : decode_any W_e8914 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e8918 : bv 32 := 0x0780006f.
Lemma F_e8918 : fetch_word AsanUbsan.M.loaded_segments (0xe8570 : word) = Some W_e8918.
Proof. vm_refl. Qed.
Lemma D_e8918 : decode_any W_e8918 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_e891c : bv 32 := 0x148000ef.
Lemma F_e891c : fetch_word AsanUbsan.M.loaded_segments (0xe8574 : word) = Some W_e891c.
Proof. vm_refl. Qed.
Lemma D_e891c : decode_any W_e891c = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_e8920 : bv 32 := 0x0fb00593.
Lemma F_e8920 : fetch_word AsanUbsan.M.loaded_segments (0xe8578 : word) = Some W_e8920.
Proof. vm_refl. Qed.
Lemma D_e8920 : decode_any W_e8920 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_e8924 : bv 32 := 0x00050413.
Lemma F_e8924 : fetch_word AsanUbsan.M.loaded_segments (0xe857c : word) = Some W_e8924.
Proof. vm_refl. Qed.
Lemma D_e8924 : decode_any W_e8924 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e8928 : bv 32 := 0x06b56463.
Lemma F_e8928 : fetch_word AsanUbsan.M.loaded_segments (0xe8580 : word) = Some W_e8928.
Proof. vm_refl. Qed.
Lemma D_e8928 : decode_any W_e8928 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_e8a64 : bv 32 := 0x00000513.
Lemma F_e8a64 : fetch_word AsanUbsan.M.loaded_segments (0xe86bc : word) = Some W_e8a64.
Proof. vm_refl. Qed.
Lemma D_e8a64 : decode_any W_e8a64 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e8a68 : bv 32 := 0x00008067.
Lemma F_e8a68 : fetch_word AsanUbsan.M.loaded_segments (0xe86c0 : word) = Some W_e8a68.
Proof. vm_refl. Qed.
Lemma D_e8a68 : decode_any W_e8a68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
