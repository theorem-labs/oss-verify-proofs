(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS_I := ImgA.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_10be6c : bv 32 := 0xfffff5b7.
Lemma F_10be6c : fetch_word ASEGS_I (0x10be6c : word) = Some W_10be6c.
Proof. vm_refl. Qed.
Lemma D_10be6c : decode_any W_10be6c = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be70 : bv 32 := 0x0015859b.
Lemma F_10be70 : fetch_word ASEGS_I (0x10be70 : word) = Some W_10be70.
Proof. vm_refl. Qed.
Lemma D_10be70 : decode_any W_10be70 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be74 : bv 32 := 0x02b56663.
Lemma F_10be74 : fetch_word ASEGS_I (0x10be74 : word) = Some W_10be74.
Proof. vm_refl. Qed.
Lemma D_10be74 : decode_any W_10be74 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be78 : bv 32 := 0xff010113.
Lemma F_10be78 : fetch_word ASEGS_I (0x10be78 : word) = Some W_10be78.
Proof. vm_refl. Qed.
Lemma D_10be78 : decode_any W_10be78 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be7c : bv 32 := 0x00113423.
Lemma F_10be7c : fetch_word ASEGS_I (0x10be7c : word) = Some W_10be7c.
Proof. vm_refl. Qed.
Lemma D_10be7c : decode_any W_10be7c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be80 : bv 32 := 0x00813023.
Lemma F_10be80 : fetch_word ASEGS_I (0x10be80 : word) = Some W_10be80.
Proof. vm_refl. Qed.
Lemma D_10be80 : decode_any W_10be80 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be84 : bv 32 := 0x40a0043b.
Lemma F_10be84 : fetch_word ASEGS_I (0x10be84 : word) = Some W_10be84.
Proof. vm_refl. Qed.
Lemma D_10be84 : decode_any W_10be84 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be88 : bv 32 := 0x8b9ff0ef.
Lemma F_10be88 : fetch_word ASEGS_I (0x10be88 : word) = Some W_10be88.
Proof. vm_refl. Qed.
Lemma D_10be88 : decode_any W_10be88 = Some (Jal 1 2095288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be8c : bv 32 := 0x00852023.
Lemma F_10be8c : fetch_word ASEGS_I (0x10be8c : word) = Some W_10be8c.
Proof. vm_refl. Qed.
Lemma D_10be8c : decode_any W_10be8c = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be90 : bv 32 := 0xfff00513.
Lemma F_10be90 : fetch_word ASEGS_I (0x10be90 : word) = Some W_10be90.
Proof. vm_refl. Qed.
Lemma D_10be90 : decode_any W_10be90 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be94 : bv 32 := 0x00813083.
Lemma F_10be94 : fetch_word ASEGS_I (0x10be94 : word) = Some W_10be94.
Proof. vm_refl. Qed.
Lemma D_10be94 : decode_any W_10be94 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be98 : bv 32 := 0x00013403.
Lemma F_10be98 : fetch_word ASEGS_I (0x10be98 : word) = Some W_10be98.
Proof. vm_refl. Qed.
Lemma D_10be98 : decode_any W_10be98 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10be9c : bv 32 := 0x01010113.
Lemma F_10be9c : fetch_word ASEGS_I (0x10be9c : word) = Some W_10be9c.
Proof. vm_refl. Qed.
Lemma D_10be9c : decode_any W_10be9c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10bea0 : bv 32 := 0x00008067.
Lemma F_10bea0 : fetch_word ASEGS_I (0x10bea0 : word) = Some W_10bea0.
Proof. vm_refl. Qed.
Lemma D_10bea0 : decode_any W_10bea0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
