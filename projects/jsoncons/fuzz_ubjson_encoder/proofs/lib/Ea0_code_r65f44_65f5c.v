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

Definition W_80b08 : bv 32 := 0x000c2517.
Lemma F_80b08 : fetch_word Asan.M.loaded_segments (0x80b58 : word) = Some W_80b08.
Proof. vm_refl. Qed.
Lemma D_80b08 : decode_any W_80b08 = Some (Auipc 10 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b0c : bv 32 := 0xb8050503.
Lemma F_80b0c : fetch_word Asan.M.loaded_segments (0x80b5c : word) = Some W_80b0c.
Proof. vm_refl. Qed.
Lemma D_80b0c : decode_any W_80b0c = Some (Load SZ1 true 10 10 2944, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b10 : bv 32 := 0x0230000f.
Lemma F_80b10 : fetch_word Asan.M.loaded_segments (0x80b60 : word) = Some W_80b10.
Proof. vm_refl. Qed.
Lemma D_80b10 : decode_any W_80b10 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b14 : bv 32 := 0xfff50513.
Lemma F_80b14 : fetch_word Asan.M.loaded_segments (0x80b64 : word) = Some W_80b14.
Proof. vm_refl. Qed.
Lemma D_80b14 : decode_any W_80b14 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b18 : bv 32 := 0x00153513.
Lemma F_80b18 : fetch_word Asan.M.loaded_segments (0x80b68 : word) = Some W_80b18.
Proof. vm_refl. Qed.
Lemma D_80b18 : decode_any W_80b18 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b1c : bv 32 := 0x00008067.
Lemma F_80b1c : fetch_word Asan.M.loaded_segments (0x80b6c : word) = Some W_80b1c.
Proof. vm_refl. Qed.
Lemma D_80b1c : decode_any W_80b1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
