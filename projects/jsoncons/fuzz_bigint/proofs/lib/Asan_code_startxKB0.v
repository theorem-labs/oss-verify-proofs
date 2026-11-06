(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_bd694 : bv 32 := 0x0004b503.
Lemma F_bd694 : fetch_word AsanUbsan.M.loaded_segments (0xbd694 : word) = Some W_bd694.
Proof. vm_refl. Qed.
Lemma D_bd694 : decode_any W_bd694 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd698 : bv 32 := 0x00848493.
Lemma F_bd698 : fetch_word AsanUbsan.M.loaded_segments (0xbd698 : word) = Some W_bd698.
Proof. vm_refl. Qed.
Lemma D_bd698 : decode_any W_bd698 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd69c : bv 32 := 0xfe051ce3.
Lemma F_bd69c : fetch_word AsanUbsan.M.loaded_segments (0xbd69c : word) = Some W_bd69c.
Proof. vm_refl. Qed.
Lemma D_bd69c : decode_any W_bd69c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd750 : bv 32 := 0x00b53023.
Lemma F_bd750 : fetch_word AsanUbsan.M.loaded_segments (0xbd750 : word) = Some W_bd750.
Proof. vm_refl. Qed.
Lemma D_bd750 : decode_any W_bd750 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd754 : bv 32 := 0x00158593.
Lemma F_bd754 : fetch_word AsanUbsan.M.loaded_segments (0xbd754 : word) = Some W_bd754.
Proof. vm_refl. Qed.
Lemma D_bd754 : decode_any W_bd754 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd758 : bv 32 := 0xfff5c683.
Lemma F_bd758 : fetch_word AsanUbsan.M.loaded_segments (0xbd758 : word) = Some W_bd758.
Proof. vm_refl. Qed.
Lemma D_bd758 : decode_any W_bd758 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd75c : bv 32 := 0xfec68ae3.
Lemma F_bd75c : fetch_word AsanUbsan.M.loaded_segments (0xbd75c : word) = Some W_bd75c.
Proof. vm_refl. Qed.
Lemma D_bd75c : decode_any W_bd75c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bd760 : bv 32 := 0xfe069ae3.
Lemma F_bd760 : fetch_word AsanUbsan.M.loaded_segments (0xbd760 : word) = Some W_bd760.
Proof. vm_refl. Qed.
Lemma D_bd760 : decode_any W_bd760 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
