(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5f47c : bv 32 := 0x00050213.
Lemma F_5f47c : fetch_word Plain.M.loaded_segments (0x5f47c : word) = Some W_5f47c.
Proof. vm_refl. Qed.
Lemma D_5f47c : decode_any W_5f47c = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f480 : bv 32 := 0x00000513.
Lemma F_5f480 : fetch_word Plain.M.loaded_segments (0x5f480 : word) = Some W_5f480.
Proof. vm_refl. Qed.
Lemma D_5f480 : decode_any W_5f480 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5f484 : bv 32 := 0x00008067.
Lemma F_5f484 : fetch_word Plain.M.loaded_segments (0x5f484 : word) = Some W_5f484.
Proof. vm_refl. Qed.
Lemma D_5f484 : decode_any W_5f484 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
