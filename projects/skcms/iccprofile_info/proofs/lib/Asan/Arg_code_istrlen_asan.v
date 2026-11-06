(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_63514 : bv 32 := 0x00000593.
Lemma F_63514 : fetch_word Asan.M.loaded_segments (0x63514 : word) = Some W_63514.
Proof. vm_refl. Qed.
Lemma D_63514 : decode_any W_63514 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63518 : bv 32 := 0x00b50633.
Lemma F_63518 : fetch_word Asan.M.loaded_segments (0x63518 : word) = Some W_63518.
Proof. vm_refl. Qed.
Lemma D_63518 : decode_any W_63518 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6351c : bv 32 := 0x00064603.
Lemma F_6351c : fetch_word Asan.M.loaded_segments (0x6351c : word) = Some W_6351c.
Proof. vm_refl. Qed.
Lemma D_6351c : decode_any W_6351c = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63520 : bv 32 := 0x00158593.
Lemma F_63520 : fetch_word Asan.M.loaded_segments (0x63520 : word) = Some W_63520.
Proof. vm_refl. Qed.
Lemma D_63520 : decode_any W_63520 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63524 : bv 32 := 0xfe061ae3.
Lemma F_63524 : fetch_word Asan.M.loaded_segments (0x63524 : word) = Some W_63524.
Proof. vm_refl. Qed.
Lemma D_63524 : decode_any W_63524 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63528 : bv 32 := 0xfff58513.
Lemma F_63528 : fetch_word Asan.M.loaded_segments (0x63528 : word) = Some W_63528.
Proof. vm_refl. Qed.
Lemma D_63528 : decode_any W_63528 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6352c : bv 32 := 0x00008067.
Lemma F_6352c : fetch_word Asan.M.loaded_segments (0x6352c : word) = Some W_6352c.
Proof. vm_refl. Qed.
Lemma D_6352c : decode_any W_6352c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
