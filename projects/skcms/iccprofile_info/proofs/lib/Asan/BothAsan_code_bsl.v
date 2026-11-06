(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_35f94 : bv 32 := 0x00359593.
Lemma F_35f94 : fetch_word AsanUbsan.M.loaded_segments (0x35f94 : word) = Some W_35f94.
Proof. vm_refl. Qed.
Lemma D_35f94 : decode_any W_35f94 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f98 : bv 32 := 0x00b485b3.
Lemma F_35f98 : fetch_word AsanUbsan.M.loaded_segments (0x35f98 : word) = Some W_35f98.
Proof. vm_refl. Qed.
Lemma D_35f98 : decode_any W_35f98 = Some (Op ALU_ADD 11 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35f9c : bv 32 := 0x0685b683.
Lemma F_35f9c : fetch_word AsanUbsan.M.loaded_segments (0x35f9c : word) = Some W_35f9c.
Proof. vm_refl. Qed.
Lemma D_35f9c : decode_any W_35f9c = Some (Load SZ8 true 13 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35fa0 : bv 32 := 0x00168693.
Lemma F_35fa0 : fetch_word AsanUbsan.M.loaded_segments (0x35fa0 : word) = Some W_35fa0.
Proof. vm_refl. Qed.
Lemma D_35fa0 : decode_any W_35fa0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35fa4 : bv 32 := 0x06c4b023.
Lemma F_35fa4 : fetch_word AsanUbsan.M.loaded_segments (0x35fa4 : word) = Some W_35fa4.
Proof. vm_refl. Qed.
Lemma D_35fa4 : decode_any W_35fa4 = Some (Store SZ8 9 12 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_35fa8 : bv 32 := 0x06d5b423.
Lemma F_35fa8 : fetch_word AsanUbsan.M.loaded_segments (0x35fa8 : word) = Some W_35fa8.
Proof. vm_refl. Qed.
Lemma D_35fa8 : decode_any W_35fa8 = Some (Store SZ8 11 13 104, 4%Z).
Proof. vm_refl. Qed.
