(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_385e0 : bv 32 := 0x00008067.
Lemma F_385e0 : fetch_word Ubsan.M.loaded_segments (0x39818 : word) = Some W_385e0.
Proof. vm_refl. Qed.
Lemma D_385e0 : decode_any W_385e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_39798 : bv 32 := 0x00008067.
Lemma F_39798 : fetch_word Ubsan.M.loaded_segments (0x39798 : word) = Some W_39798.
Proof. vm_refl. Qed.
Lemma D_39798 : decode_any W_39798 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
