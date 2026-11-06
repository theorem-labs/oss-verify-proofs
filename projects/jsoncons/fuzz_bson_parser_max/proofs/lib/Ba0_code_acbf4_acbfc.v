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
Definition W_acbf4 : bv 32 := 0x4035d593.
Lemma F_acbf4 : fetch_word Asan.M.loaded_segments (0xacc44 : word) = Some W_acbf4.
Proof. vm_refl. Qed.
Lemma D_acbf4 : decode_any W_acbf4 = Some (ShiftImm ALU_SRA 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_acbf8 : bv 32 := 0x02d585b3.
Lemma F_acbf8 : fetch_word Asan.M.loaded_segments (0xacc48 : word) = Some W_acbf8.
Proof. vm_refl. Qed.
Lemma D_acbf8 : decode_any W_acbf8 = Some (Mul M_MUL 11 11 13, 4%Z).
Proof. vm_refl. Qed.
