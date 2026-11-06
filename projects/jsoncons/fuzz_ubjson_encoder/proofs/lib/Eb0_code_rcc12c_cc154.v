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

Definition W_130ba8 : bv 32 := 0x00050893.
Lemma F_130ba8 : fetch_word AsanUbsan.M.loaded_segments (0x130bec : word) = Some W_130ba8.
Proof. vm_refl. Qed.
Lemma D_130ba8 : decode_any W_130ba8 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bac : bv 32 := 0x00058513.
Lemma F_130bac : fetch_word AsanUbsan.M.loaded_segments (0x130bf0 : word) = Some W_130bac.
Proof. vm_refl. Qed.
Lemma D_130bac : decode_any W_130bac = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bb0 : bv 32 := 0x00060593.
Lemma F_130bb0 : fetch_word AsanUbsan.M.loaded_segments (0x130bf4 : word) = Some W_130bb0.
Proof. vm_refl. Qed.
Lemma D_130bb0 : decode_any W_130bb0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bb4 : bv 32 := 0x00068613.
Lemma F_130bb4 : fetch_word AsanUbsan.M.loaded_segments (0x130bf8 : word) = Some W_130bb4.
Proof. vm_refl. Qed.
Lemma D_130bb4 : decode_any W_130bb4 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bb8 : bv 32 := 0x00070693.
Lemma F_130bb8 : fetch_word AsanUbsan.M.loaded_segments (0x130bfc : word) = Some W_130bb8.
Proof. vm_refl. Qed.
Lemma D_130bb8 : decode_any W_130bb8 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bbc : bv 32 := 0x00078713.
Lemma F_130bbc : fetch_word AsanUbsan.M.loaded_segments (0x130c00 : word) = Some W_130bbc.
Proof. vm_refl. Qed.
Lemma D_130bbc : decode_any W_130bbc = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bc0 : bv 32 := 0x00080793.
Lemma F_130bc0 : fetch_word AsanUbsan.M.loaded_segments (0x130c04 : word) = Some W_130bc0.
Proof. vm_refl. Qed.
Lemma D_130bc0 : decode_any W_130bc0 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bc4 : bv 32 := 0x00000073.
Lemma F_130bc4 : fetch_word AsanUbsan.M.loaded_segments (0x130c08 : word) = Some W_130bc4.
Proof. vm_refl. Qed.
Lemma D_130bc4 : decode_any W_130bc4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_130bc4 : is_ecall W_130bc4 = true.
Proof. reflexivity. Qed.

Definition W_130bc8 : bv 32 := 0x00008067.
Lemma F_130bc8 : fetch_word AsanUbsan.M.loaded_segments (0x130c0c : word) = Some W_130bc8.
Proof. vm_refl. Qed.
Lemma D_130bc8 : decode_any W_130bc8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_130bcc : bv 32 := 0xfddff06f.
Lemma F_130bcc : fetch_word AsanUbsan.M.loaded_segments (0x130c10 : word) = Some W_130bcc.
Proof. vm_refl. Qed.
Lemma D_130bcc : decode_any W_130bcc = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.
