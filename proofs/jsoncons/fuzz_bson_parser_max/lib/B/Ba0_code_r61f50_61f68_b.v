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
Definition W_7bb4c : bv 32 := 0x000c3517.
Lemma F_7bb4c : fetch_word AsanUbsan.M.loaded_segments (0x7bf64 : word) = Some W_7bb4c.
Proof. vm_refl. Qed.
Lemma D_7bb4c : decode_any W_7bb4c = Some (Auipc 10 195, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bb50 : bv 32 := 0x53c50513.
Lemma F_7bb50 : fetch_word AsanUbsan.M.loaded_segments (0x7bf68 : word) = Some W_7bb50.
Proof. vm_refl. Qed.
Lemma D_7bb50 : decode_any W_7bb50 = Some (OpImm ALU_ADD 10 10 1340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bb54 : bv 32 := 0x00054583.
Lemma F_7bb54 : fetch_word AsanUbsan.M.loaded_segments (0x7bf6c : word) = Some W_7bb54.
Proof. vm_refl. Qed.
Lemma D_7bb54 : decode_any W_7bb54 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bb58 : bv 32 := 0x00058663.
Lemma F_7bb58 : fetch_word AsanUbsan.M.loaded_segments (0x7bf70 : word) = Some W_7bb58.
Proof. vm_refl. Qed.
Lemma D_7bb58 : decode_any W_7bb58 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bb5c : bv 32 := 0x00452503.
Lemma F_7bb5c : fetch_word AsanUbsan.M.loaded_segments (0x7bf74 : word) = Some W_7bb5c.
Proof. vm_refl. Qed.
Lemma D_7bb5c : decode_any W_7bb5c = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bb60 : bv 32 := 0x5b4b006f.
Lemma F_7bb60 : fetch_word AsanUbsan.M.loaded_segments (0x7bf78 : word) = Some W_7bb60.
Proof. vm_refl. Qed.
Lemma D_7bb60 : decode_any W_7bb60 = Some (Jal 0 722356, 4%Z).
Proof. vm_refl. Qed.
