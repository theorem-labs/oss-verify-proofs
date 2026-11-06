(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_aad20 : bv 32 := 0x4035d593.
Lemma F_aad20 : fetch_word Asan.M.loaded_segments (0xaad70 : word) = Some W_aad20.
Proof. vm_refl. Qed.
Lemma D_aad20 : decode_any W_aad20 = Some (ShiftImm ALU_SRA 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aad24 : bv 32 := 0x02d585b3.
Lemma F_aad24 : fetch_word Asan.M.loaded_segments (0xaad74 : word) = Some W_aad24.
Proof. vm_refl. Qed.
Lemma D_aad24 : decode_any W_aad24 = Some (Mul M_MUL 11 11 13, 4%Z).
Proof. vm_refl. Qed.
