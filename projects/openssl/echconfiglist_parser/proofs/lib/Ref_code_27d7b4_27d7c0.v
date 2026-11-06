(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_27d7b4 : bv 32 := 0x00050213.
Lemma F_27d7b4 : fetch_word Plain.M.loaded_segments (0x27d7f0 : word) = Some W_27d7b4.
Proof. vm_refl. Qed.
Lemma D_27d7b4 : decode_any W_27d7b4 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27d7b8 : bv 32 := 0x00000513.
Lemma F_27d7b8 : fetch_word Plain.M.loaded_segments (0x27d7f4 : word) = Some W_27d7b8.
Proof. vm_refl. Qed.
Lemma D_27d7b8 : decode_any W_27d7b8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_27d7bc : bv 32 := 0x00008067.
Lemma F_27d7bc : fetch_word Plain.M.loaded_segments (0x27d7f8 : word) = Some W_27d7bc.
Proof. vm_refl. Qed.
Lemma D_27d7bc : decode_any W_27d7bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
