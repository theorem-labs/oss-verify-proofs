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
Definition W_115eb4 : bv 32 := 0x00020513.
Lemma F_115eb4 : fetch_word AsanUbsan.M.loaded_segments (0x1184a4 : word) = Some W_115eb4.
Proof. vm_refl. Qed.
Lemma D_115eb4 : decode_any W_115eb4 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115eb8 : bv 32 := 0xf5c50513.
Lemma F_115eb8 : fetch_word AsanUbsan.M.loaded_segments (0x1184a8 : word) = Some W_115eb8.
Proof. vm_refl. Qed.
Lemma D_115eb8 : decode_any W_115eb8 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_115ebc : bv 32 := 0x00008067.
Lemma F_115ebc : fetch_word AsanUbsan.M.loaded_segments (0x1184ac : word) = Some W_115ebc.
Proof. vm_refl. Qed.
Lemma D_115ebc : decode_any W_115ebc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
