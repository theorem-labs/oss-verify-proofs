(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1b0bf0 : bv 32 := 0x0004b503.
Lemma F_1b0bf0 : fetch_word AsanUbsan.M.loaded_segments (0x1b15a0 : word) = Some W_1b0bf0.
Proof. vm_refl. Qed.
Lemma D_1b0bf0 : decode_any W_1b0bf0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b0bf4 : bv 32 := 0x00848493.
Lemma F_1b0bf4 : fetch_word AsanUbsan.M.loaded_segments (0x1b15a4 : word) = Some W_1b0bf4.
Proof. vm_refl. Qed.
Lemma D_1b0bf4 : decode_any W_1b0bf4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b0bf8 : bv 32 := 0xfe051ce3.
Lemma F_1b0bf8 : fetch_word AsanUbsan.M.loaded_segments (0x1b15a8 : word) = Some W_1b0bf8.
Proof. vm_refl. Qed.
Lemma D_1b0bf8 : decode_any W_1b0bf8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_1b0cac : bv 32 := 0x00b53023.
Lemma F_1b0cac : fetch_word AsanUbsan.M.loaded_segments (0x1b165c : word) = Some W_1b0cac.
Proof. vm_refl. Qed.
Lemma D_1b0cac : decode_any W_1b0cac = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b0cb0 : bv 32 := 0x00158593.
Lemma F_1b0cb0 : fetch_word AsanUbsan.M.loaded_segments (0x1b1660 : word) = Some W_1b0cb0.
Proof. vm_refl. Qed.
Lemma D_1b0cb0 : decode_any W_1b0cb0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b0cb4 : bv 32 := 0xfff5c683.
Lemma F_1b0cb4 : fetch_word AsanUbsan.M.loaded_segments (0x1b1664 : word) = Some W_1b0cb4.
Proof. vm_refl. Qed.
Lemma D_1b0cb4 : decode_any W_1b0cb4 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b0cb8 : bv 32 := 0xfec68ae3.
Lemma F_1b0cb8 : fetch_word AsanUbsan.M.loaded_segments (0x1b1668 : word) = Some W_1b0cb8.
Proof. vm_refl. Qed.
Lemma D_1b0cb8 : decode_any W_1b0cb8 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b0cbc : bv 32 := 0xfe069ae3.
Lemma F_1b0cbc : fetch_word AsanUbsan.M.loaded_segments (0x1b166c : word) = Some W_1b0cbc.
Proof. vm_refl. Qed.
Lemma D_1b0cbc : decode_any W_1b0cbc = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
