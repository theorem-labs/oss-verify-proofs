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
Definition W_d13ac : bv 32 := 0x850a806f.
Lemma F_d13ac : fetch_word Asan.M.loaded_segments (0xd13fc : word) = Some W_d13ac.
Proof. vm_refl. Qed.
Lemma D_d13ac : decode_any W_d13ac = Some (Jal 0 1736784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d13b0 : bv 32 := 0xffdff06f.
Lemma F_d13b0 : fetch_word Asan.M.loaded_segments (0xd1400 : word) = Some W_d13b0.
Proof. vm_refl. Qed.
Lemma D_d13b0 : decode_any W_d13b0 = Some (Jal 0 2097148, 4%Z).
Proof. vm_refl. Qed.
