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

Definition W_12c400 : bv 32 := 0x00050893.
Lemma F_12c400 : fetch_word Asan.M.loaded_segments (0x12c444 : word) = Some W_12c400.
Proof. vm_refl. Qed.
Lemma D_12c400 : decode_any W_12c400 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c404 : bv 32 := 0x00058513.
Lemma F_12c404 : fetch_word Asan.M.loaded_segments (0x12c448 : word) = Some W_12c404.
Proof. vm_refl. Qed.
Lemma D_12c404 : decode_any W_12c404 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c408 : bv 32 := 0x00060593.
Lemma F_12c408 : fetch_word Asan.M.loaded_segments (0x12c44c : word) = Some W_12c408.
Proof. vm_refl. Qed.
Lemma D_12c408 : decode_any W_12c408 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c40c : bv 32 := 0x00068613.
Lemma F_12c40c : fetch_word Asan.M.loaded_segments (0x12c450 : word) = Some W_12c40c.
Proof. vm_refl. Qed.
Lemma D_12c40c : decode_any W_12c40c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c410 : bv 32 := 0x00070693.
Lemma F_12c410 : fetch_word Asan.M.loaded_segments (0x12c454 : word) = Some W_12c410.
Proof. vm_refl. Qed.
Lemma D_12c410 : decode_any W_12c410 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c414 : bv 32 := 0x00078713.
Lemma F_12c414 : fetch_word Asan.M.loaded_segments (0x12c458 : word) = Some W_12c414.
Proof. vm_refl. Qed.
Lemma D_12c414 : decode_any W_12c414 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c418 : bv 32 := 0x00080793.
Lemma F_12c418 : fetch_word Asan.M.loaded_segments (0x12c45c : word) = Some W_12c418.
Proof. vm_refl. Qed.
Lemma D_12c418 : decode_any W_12c418 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c41c : bv 32 := 0x00000073.
Lemma F_12c41c : fetch_word Asan.M.loaded_segments (0x12c460 : word) = Some W_12c41c.
Proof. vm_refl. Qed.
Lemma D_12c41c : decode_any W_12c41c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_12c41c : is_ecall W_12c41c = true.
Proof. reflexivity. Qed.

Definition W_12c420 : bv 32 := 0x00008067.
Lemma F_12c420 : fetch_word Asan.M.loaded_segments (0x12c464 : word) = Some W_12c420.
Proof. vm_refl. Qed.
Lemma D_12c420 : decode_any W_12c420 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c424 : bv 32 := 0xfddff06f.
Lemma F_12c424 : fetch_word Asan.M.loaded_segments (0x12c468 : word) = Some W_12c424.
Proof. vm_refl. Qed.
Lemma D_12c424 : decode_any W_12c424 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.
