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

Definition W_ac1b4 : bv 32 := 0x00747593.
Lemma F_ac1b4 : fetch_word Asan.M.loaded_segments (0xac204 : word) = Some W_ac1b4.
Proof. vm_refl. Qed.
Lemma D_ac1b4 : decode_any W_ac1b4 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac1b8 : bv 32 := 0xfca5c6e3.
Lemma F_ac1b8 : fetch_word Asan.M.loaded_segments (0xac208 : word) = Some W_ac1b8.
Proof. vm_refl. Qed.
Lemma D_ac1b8 : decode_any W_ac1b8 = Some (Branch BC_LT 11 10 8140, 4%Z).
Proof. vm_refl. Qed.
