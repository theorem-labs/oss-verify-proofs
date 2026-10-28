(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1d194 : bv 32 := 0x00040517.
Lemma F_1d194 : fetch_word Ubsan.M.loaded_segments (0x1d674 : word) = Some W_1d194.
Proof. vm_refl. Qed.
Lemma D_1d194 : decode_any W_1d194 = Some (Auipc 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d198 : bv 32 := 0x90054503.
Lemma F_1d198 : fetch_word Ubsan.M.loaded_segments (0x1d678 : word) = Some W_1d198.
Proof. vm_refl. Qed.
Lemma D_1d198 : decode_any W_1d198 = Some (Load SZ1 false 10 10 2304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d19c : bv 32 := 0x00051463.
Lemma F_1d19c : fetch_word Ubsan.M.loaded_segments (0x1d67c : word) = Some W_1d19c.
Proof. vm_refl. Qed.
Lemma D_1d19c : decode_any W_1d19c = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1a0 : bv 32 := 0x00008067.
Lemma F_1d1a0 : fetch_word Ubsan.M.loaded_segments (0x1d680 : word) = Some W_1d1a0.
Proof. vm_refl. Qed.
Lemma D_1d1a0 : decode_any W_1d1a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
