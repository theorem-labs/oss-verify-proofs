(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation BSEGS_I := ImgB.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_10b544 : bv 32 := 0x0004b503.
Lemma F_10b544 : fetch_word BSEGS_I (0x10b544 : word) = Some W_10b544.
Proof. vm_refl. Qed.
Lemma D_10b544 : decode_any W_10b544 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b548 : bv 32 := 0x00848493.
Lemma F_10b548 : fetch_word BSEGS_I (0x10b548 : word) = Some W_10b548.
Proof. vm_refl. Qed.
Lemma D_10b548 : decode_any W_10b548 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b54c : bv 32 := 0xfe051ce3.
Lemma F_10b54c : fetch_word BSEGS_I (0x10b54c : word) = Some W_10b54c.
Proof. vm_refl. Qed.
Lemma D_10b54c : decode_any W_10b54c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b600 : bv 32 := 0x00b53023.
Lemma F_10b600 : fetch_word BSEGS_I (0x10b600 : word) = Some W_10b600.
Proof. vm_refl. Qed.
Lemma D_10b600 : decode_any W_10b600 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b604 : bv 32 := 0x00158593.
Lemma F_10b604 : fetch_word BSEGS_I (0x10b604 : word) = Some W_10b604.
Proof. vm_refl. Qed.
Lemma D_10b604 : decode_any W_10b604 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b608 : bv 32 := 0xfff5c683.
Lemma F_10b608 : fetch_word BSEGS_I (0x10b608 : word) = Some W_10b608.
Proof. vm_refl. Qed.
Lemma D_10b608 : decode_any W_10b608 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b60c : bv 32 := 0xfec68ae3.
Lemma F_10b60c : fetch_word BSEGS_I (0x10b60c : word) = Some W_10b60c.
Proof. vm_refl. Qed.
Lemma D_10b60c : decode_any W_10b60c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b610 : bv 32 := 0xfe069ae3.
Lemma F_10b610 : fetch_word BSEGS_I (0x10b610 : word) = Some W_10b610.
Proof. vm_refl. Qed.
Lemma D_10b610 : decode_any W_10b610 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
