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

Definition W_ac4cc : bv 32 := 0x00797593.
Lemma F_ac4cc : fetch_word Asan.M.loaded_segments (0xac51c : word) = Some W_ac4cc.
Proof. vm_refl. Qed.
Lemma D_ac4cc : decode_any W_ac4cc = Some (OpImm ALU_AND 11 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ac4d0 : bv 32 := 0xfca5c6e3.
Lemma F_ac4d0 : fetch_word Asan.M.loaded_segments (0xac520 : word) = Some W_ac4d0.
Proof. vm_refl. Qed.
Lemma D_ac4d0 : decode_any W_ac4d0 = Some (Branch BC_LT 11 10 8140, 4%Z).
Proof. vm_refl. Qed.
