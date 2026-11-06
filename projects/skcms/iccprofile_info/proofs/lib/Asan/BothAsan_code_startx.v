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
Definition W_8ea54 : bv 32 := 0x0004b503.
Lemma F_8ea54 : fetch_word AsanUbsan.M.loaded_segments (0x8ea54 : word) = Some W_8ea54.
Proof. vm_refl. Qed.
Lemma D_8ea54 : decode_any W_8ea54 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ea58 : bv 32 := 0x00848493.
Lemma F_8ea58 : fetch_word AsanUbsan.M.loaded_segments (0x8ea58 : word) = Some W_8ea58.
Proof. vm_refl. Qed.
Lemma D_8ea58 : decode_any W_8ea58 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ea5c : bv 32 := 0xfe051ce3.
Lemma F_8ea5c : fetch_word AsanUbsan.M.loaded_segments (0x8ea5c : word) = Some W_8ea5c.
Proof. vm_refl. Qed.
Lemma D_8ea5c : decode_any W_8ea5c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8eb10 : bv 32 := 0x00b53023.
Lemma F_8eb10 : fetch_word AsanUbsan.M.loaded_segments (0x8eb10 : word) = Some W_8eb10.
Proof. vm_refl. Qed.
Lemma D_8eb10 : decode_any W_8eb10 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8eb14 : bv 32 := 0x00158593.
Lemma F_8eb14 : fetch_word AsanUbsan.M.loaded_segments (0x8eb14 : word) = Some W_8eb14.
Proof. vm_refl. Qed.
Lemma D_8eb14 : decode_any W_8eb14 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8eb18 : bv 32 := 0xfff5c683.
Lemma F_8eb18 : fetch_word AsanUbsan.M.loaded_segments (0x8eb18 : word) = Some W_8eb18.
Proof. vm_refl. Qed.
Lemma D_8eb18 : decode_any W_8eb18 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8eb1c : bv 32 := 0xfec68ae3.
Lemma F_8eb1c : fetch_word AsanUbsan.M.loaded_segments (0x8eb1c : word) = Some W_8eb1c.
Proof. vm_refl. Qed.
Lemma D_8eb1c : decode_any W_8eb1c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8eb20 : bv 32 := 0xfe069ae3.
Lemma F_8eb20 : fetch_word AsanUbsan.M.loaded_segments (0x8eb20 : word) = Some W_8eb20.
Proof. vm_refl. Qed.
Lemma D_8eb20 : decode_any W_8eb20 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
