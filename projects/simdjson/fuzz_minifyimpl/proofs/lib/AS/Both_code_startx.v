(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_minifyimpl.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_153d7c : bv 32 := 0x0004b503.
Lemma F_153d7c : fetch_word AsanUbsan.M.loaded_segments (0x153d04 : word) = Some W_153d7c.
Proof. vm_refl. Qed.
Lemma D_153d7c : decode_any W_153d7c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153d80 : bv 32 := 0x00848493.
Lemma F_153d80 : fetch_word AsanUbsan.M.loaded_segments (0x153d08 : word) = Some W_153d80.
Proof. vm_refl. Qed.
Lemma D_153d80 : decode_any W_153d80 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153d84 : bv 32 := 0xfe051ce3.
Lemma F_153d84 : fetch_word AsanUbsan.M.loaded_segments (0x153d0c : word) = Some W_153d84.
Proof. vm_refl. Qed.
Lemma D_153d84 : decode_any W_153d84 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_153e38 : bv 32 := 0x00b53023.
Lemma F_153e38 : fetch_word AsanUbsan.M.loaded_segments (0x153dc0 : word) = Some W_153e38.
Proof. vm_refl. Qed.
Lemma D_153e38 : decode_any W_153e38 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e3c : bv 32 := 0x00158593.
Lemma F_153e3c : fetch_word AsanUbsan.M.loaded_segments (0x153dc4 : word) = Some W_153e3c.
Proof. vm_refl. Qed.
Lemma D_153e3c : decode_any W_153e3c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e40 : bv 32 := 0xfff5c683.
Lemma F_153e40 : fetch_word AsanUbsan.M.loaded_segments (0x153dc8 : word) = Some W_153e40.
Proof. vm_refl. Qed.
Lemma D_153e40 : decode_any W_153e40 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e44 : bv 32 := 0xfec68ae3.
Lemma F_153e44 : fetch_word AsanUbsan.M.loaded_segments (0x153dcc : word) = Some W_153e44.
Proof. vm_refl. Qed.
Lemma D_153e44 : decode_any W_153e44 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_153e48 : bv 32 := 0xfe069ae3.
Lemma F_153e48 : fetch_word AsanUbsan.M.loaded_segments (0x153dd0 : word) = Some W_153e48.
Proof. vm_refl. Qed.
Lemma D_153e48 : decode_any W_153e48 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
