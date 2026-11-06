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
Definition W_10c348 : bv 32 := 0xfffff5b7.
Lemma F_10c348 : fetch_word BSEGS_I (0x10c348 : word) = Some W_10c348.
Proof. vm_refl. Qed.
Lemma D_10c348 : decode_any W_10c348 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c34c : bv 32 := 0x0015859b.
Lemma F_10c34c : fetch_word BSEGS_I (0x10c34c : word) = Some W_10c34c.
Proof. vm_refl. Qed.
Lemma D_10c34c : decode_any W_10c34c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c350 : bv 32 := 0x02b56663.
Lemma F_10c350 : fetch_word BSEGS_I (0x10c350 : word) = Some W_10c350.
Proof. vm_refl. Qed.
Lemma D_10c350 : decode_any W_10c350 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c354 : bv 32 := 0xff010113.
Lemma F_10c354 : fetch_word BSEGS_I (0x10c354 : word) = Some W_10c354.
Proof. vm_refl. Qed.
Lemma D_10c354 : decode_any W_10c354 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c358 : bv 32 := 0x00113423.
Lemma F_10c358 : fetch_word BSEGS_I (0x10c358 : word) = Some W_10c358.
Proof. vm_refl. Qed.
Lemma D_10c358 : decode_any W_10c358 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c35c : bv 32 := 0x00813023.
Lemma F_10c35c : fetch_word BSEGS_I (0x10c35c : word) = Some W_10c35c.
Proof. vm_refl. Qed.
Lemma D_10c35c : decode_any W_10c35c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c360 : bv 32 := 0x40a0043b.
Lemma F_10c360 : fetch_word BSEGS_I (0x10c360 : word) = Some W_10c360.
Proof. vm_refl. Qed.
Lemma D_10c360 : decode_any W_10c360 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c364 : bv 32 := 0x8b9ff0ef.
Lemma F_10c364 : fetch_word BSEGS_I (0x10c364 : word) = Some W_10c364.
Proof. vm_refl. Qed.
Lemma D_10c364 : decode_any W_10c364 = Some (Jal 1 2095288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c368 : bv 32 := 0x00852023.
Lemma F_10c368 : fetch_word BSEGS_I (0x10c368 : word) = Some W_10c368.
Proof. vm_refl. Qed.
Lemma D_10c368 : decode_any W_10c368 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c36c : bv 32 := 0xfff00513.
Lemma F_10c36c : fetch_word BSEGS_I (0x10c36c : word) = Some W_10c36c.
Proof. vm_refl. Qed.
Lemma D_10c36c : decode_any W_10c36c = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c370 : bv 32 := 0x00813083.
Lemma F_10c370 : fetch_word BSEGS_I (0x10c370 : word) = Some W_10c370.
Proof. vm_refl. Qed.
Lemma D_10c370 : decode_any W_10c370 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c374 : bv 32 := 0x00013403.
Lemma F_10c374 : fetch_word BSEGS_I (0x10c374 : word) = Some W_10c374.
Proof. vm_refl. Qed.
Lemma D_10c374 : decode_any W_10c374 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c378 : bv 32 := 0x01010113.
Lemma F_10c378 : fetch_word BSEGS_I (0x10c378 : word) = Some W_10c378.
Proof. vm_refl. Qed.
Lemma D_10c378 : decode_any W_10c378 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10c37c : bv 32 := 0x00008067.
Lemma F_10c37c : fetch_word BSEGS_I (0x10c37c : word) = Some W_10c37c.
Proof. vm_refl. Qed.
Lemma D_10c37c : decode_any W_10c37c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
