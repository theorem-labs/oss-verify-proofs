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
Definition W_aad64 : bv 32 := 0x00052583.
Lemma F_aad64 : fetch_word Ubsan.M.loaded_segments (0xac398 : word) = Some W_aad64.
Proof. vm_refl. Qed.
Lemma D_aad64 : decode_any W_aad64 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aad68 : bv 32 := 0x0005c463.
Lemma F_aad68 : fetch_word Ubsan.M.loaded_segments (0xac39c : word) = Some W_aad68.
Proof. vm_refl. Qed.
Lemma D_aad68 : decode_any W_aad68 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_aad6c : bv 32 := 0x00008067.
Lemma F_aad6c : fetch_word Ubsan.M.loaded_segments (0xac3a0 : word) = Some W_aad6c.
Proof. vm_refl. Qed.
Lemma D_aad6c : decode_any W_aad6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
