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

Definition W_8c710 : bv 32 := 0x00000593.
Lemma F_8c710 : fetch_word AsanUbsan.M.loaded_segments (0x8c760 : word) = Some W_8c710.
Proof. vm_refl. Qed.
Lemma D_8c710 : decode_any W_8c710 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c714 : bv 32 := 0x00b50633.
Lemma F_8c714 : fetch_word AsanUbsan.M.loaded_segments (0x8c764 : word) = Some W_8c714.
Proof. vm_refl. Qed.
Lemma D_8c714 : decode_any W_8c714 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c718 : bv 32 := 0x00064603.
Lemma F_8c718 : fetch_word AsanUbsan.M.loaded_segments (0x8c768 : word) = Some W_8c718.
Proof. vm_refl. Qed.
Lemma D_8c718 : decode_any W_8c718 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c71c : bv 32 := 0x00158593.
Lemma F_8c71c : fetch_word AsanUbsan.M.loaded_segments (0x8c76c : word) = Some W_8c71c.
Proof. vm_refl. Qed.
Lemma D_8c71c : decode_any W_8c71c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c720 : bv 32 := 0xfe061ae3.
Lemma F_8c720 : fetch_word AsanUbsan.M.loaded_segments (0x8c770 : word) = Some W_8c720.
Proof. vm_refl. Qed.
Lemma D_8c720 : decode_any W_8c720 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c724 : bv 32 := 0xfff58513.
Lemma F_8c724 : fetch_word AsanUbsan.M.loaded_segments (0x8c774 : word) = Some W_8c724.
Proof. vm_refl. Qed.
Lemma D_8c724 : decode_any W_8c724 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c728 : bv 32 := 0x00008067.
Lemma F_8c728 : fetch_word AsanUbsan.M.loaded_segments (0x8c778 : word) = Some W_8c728.
Proof. vm_refl. Qed.
Lemma D_8c728 : decode_any W_8c728 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
