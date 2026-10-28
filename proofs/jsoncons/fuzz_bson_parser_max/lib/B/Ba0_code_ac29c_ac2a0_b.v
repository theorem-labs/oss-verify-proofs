(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ac29c : bv 32 := 0x00008067.
Lemma F_ac29c : fetch_word AsanUbsan.M.loaded_segments (0xad09c : word) = Some W_ac29c.
Proof. vm_refl. Qed.
Lemma D_ac29c : decode_any W_ac29c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_ad314 : bv 32 := 0x00008067.
Lemma F_ad314 : fetch_word AsanUbsan.M.loaded_segments (0xad314 : word) = Some W_ad314.
Proof. vm_refl. Qed.
Lemma D_ad314 : decode_any W_ad314 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
