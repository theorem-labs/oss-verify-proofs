(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_35bb8 : bv 32 := 0x01013407.
Lemma F_35bb8 : fetch_word Plain.M.loaded_segments (0x35c10 : word) = Some W_35bb8.
Proof. vm_refl. Qed.
Lemma D_35bb8 : decode_any W_35bb8 = Some (FLoad FMT_D 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_35bbc : bv 32 := 0x00813487.
Lemma F_35bbc : fetch_word Plain.M.loaded_segments (0x35c14 : word) = Some W_35bbc.
Proof. vm_refl. Qed.
Lemma D_35bbc : decode_any W_35bbc = Some (FLoad FMT_D 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_35bc0 : bv 32 := 0x03010113.
Lemma F_35bc0 : fetch_word Plain.M.loaded_segments (0x35c18 : word) = Some W_35bc0.
Proof. vm_refl. Qed.
Lemma D_35bc0 : decode_any W_35bc0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_35bc4 : bv 32 := 0x00008067.
Lemma F_35bc4 : fetch_word Plain.M.loaded_segments (0x35c1c : word) = Some W_35bc4.
Proof. vm_refl. Qed.
Lemma D_35bc4 : decode_any W_35bc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
