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

Definition W_ab7a4 : bv 32 := 0x00813c27.
Lemma F_ab7a4 : fetch_word Asan.M.loaded_segments (0xab7f4 : word) = Some W_ab7a4.
Proof. vm_refl. Qed.
Lemma D_ab7a4 : decode_any W_ab7a4 = Some (FStore FMT_D 2 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ab7a8 : bv 32 := 0x00913827.
Lemma F_ab7a8 : fetch_word Asan.M.loaded_segments (0xab7f8 : word) = Some W_ab7a8.
Proof. vm_refl. Qed.
Lemma D_ab7a8 : decode_any W_ab7a8 = Some (FStore FMT_D 2 9 16, 4%Z).
Proof. vm_refl. Qed.
