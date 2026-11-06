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
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_d7de4 : bv 32 := 0x0004b503.
Lemma F_d7de4 : fetch_word AsanUbsan.M.loaded_segments (0xd876c : word) = Some W_d7de4.
Proof. vm_refl. Qed.
Lemma D_d7de4 : decode_any W_d7de4 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7de8 : bv 32 := 0x00848493.
Lemma F_d7de8 : fetch_word AsanUbsan.M.loaded_segments (0xd8770 : word) = Some W_d7de8.
Proof. vm_refl. Qed.
Lemma D_d7de8 : decode_any W_d7de8 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7dec : bv 32 := 0xfe051ce3.
Lemma F_d7dec : fetch_word AsanUbsan.M.loaded_segments (0xd8774 : word) = Some W_d7dec.
Proof. vm_refl. Qed.
Lemma D_d7dec : decode_any W_d7dec = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_d7ea0 : bv 32 := 0x00b53023.
Lemma F_d7ea0 : fetch_word AsanUbsan.M.loaded_segments (0xd8828 : word) = Some W_d7ea0.
Proof. vm_refl. Qed.
Lemma D_d7ea0 : decode_any W_d7ea0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7ea4 : bv 32 := 0x00158593.
Lemma F_d7ea4 : fetch_word AsanUbsan.M.loaded_segments (0xd882c : word) = Some W_d7ea4.
Proof. vm_refl. Qed.
Lemma D_d7ea4 : decode_any W_d7ea4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7ea8 : bv 32 := 0xfff5c683.
Lemma F_d7ea8 : fetch_word AsanUbsan.M.loaded_segments (0xd8830 : word) = Some W_d7ea8.
Proof. vm_refl. Qed.
Lemma D_d7ea8 : decode_any W_d7ea8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7eac : bv 32 := 0xfec68ae3.
Lemma F_d7eac : fetch_word AsanUbsan.M.loaded_segments (0xd8834 : word) = Some W_d7eac.
Proof. vm_refl. Qed.
Lemma D_d7eac : decode_any W_d7eac = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7eb0 : bv 32 := 0xfe069ae3.
Lemma F_d7eb0 : fetch_word AsanUbsan.M.loaded_segments (0xd8838 : word) = Some W_d7eb0.
Proof. vm_refl. Qed.
Lemma D_d7eb0 : decode_any W_d7eb0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
