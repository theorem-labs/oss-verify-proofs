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
Definition W_35f68 : bv 32 := 0x00359593.
Lemma F_35f68 : fetch_word Asan.M.loaded_segments (0x35f68 : word) = Some W_35f68.
Proof. vm_refl. Qed.
Lemma D_35f68 : decode_any W_35f68 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f6c : bv 32 := 0x00b485b3.
Lemma F_35f6c : fetch_word Asan.M.loaded_segments (0x35f6c : word) = Some W_35f6c.
Proof. vm_refl. Qed.
Lemma D_35f6c : decode_any W_35f6c = Some (Op ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f70 : bv 32 := 0x0685b683.
Lemma F_35f70 : fetch_word Asan.M.loaded_segments (0x35f70 : word) = Some W_35f70.
Proof. vm_refl. Qed.
Lemma D_35f70 : decode_any W_35f70 = Some (Load SZ8 true 13 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f74 : bv 32 := 0x00168693.
Lemma F_35f74 : fetch_word Asan.M.loaded_segments (0x35f74 : word) = Some W_35f74.
Proof. vm_refl. Qed.
Lemma D_35f74 : decode_any W_35f74 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f78 : bv 32 := 0x06c4b023.
Lemma F_35f78 : fetch_word Asan.M.loaded_segments (0x35f78 : word) = Some W_35f78.
Proof. vm_refl. Qed.
Lemma D_35f78 : decode_any W_35f78 = Some (Store SZ8 9 12 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f7c : bv 32 := 0x06d5b423.
Lemma F_35f7c : fetch_word Asan.M.loaded_segments (0x35f7c : word) = Some W_35f7c.
Proof. vm_refl. Qed.
Lemma D_35f7c : decode_any W_35f7c = Some (Store SZ8 11 13 104, 4%Z).
Proof. vm_refl. Qed.
