(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_36304 : bv 32 := 0x01013407.
Lemma F_36304 : fetch_word Ubsan.M.loaded_segments (0x3635c : word) = Some W_36304.
Proof. vm_refl. Qed.
Lemma D_36304 : decode_any W_36304 = Some (FLoad FMT_D 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_36308 : bv 32 := 0x00813487.
Lemma F_36308 : fetch_word Ubsan.M.loaded_segments (0x36360 : word) = Some W_36308.
Proof. vm_refl. Qed.
Lemma D_36308 : decode_any W_36308 = Some (FLoad FMT_D 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3630c : bv 32 := 0x03010113.
Lemma F_3630c : fetch_word Ubsan.M.loaded_segments (0x36364 : word) = Some W_3630c.
Proof. vm_refl. Qed.
Lemma D_3630c : decode_any W_3630c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_36310 : bv 32 := 0x00008067.
Lemma F_36310 : fetch_word Ubsan.M.loaded_segments (0x36368 : word) = Some W_36310.
Proof. vm_refl. Qed.
Lemma D_36310 : decode_any W_36310 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
