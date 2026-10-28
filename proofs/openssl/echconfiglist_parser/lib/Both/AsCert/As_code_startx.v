(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_137b8c : bv 32 := 0x0004b503.
Lemma F_137b8c : fetch_word AsanUbsan.M.loaded_segments (0x55db68 : word) = Some W_137b8c.
Proof. vm_refl. Qed.
Lemma D_137b8c : decode_any W_137b8c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_137b90 : bv 32 := 0x00848493.
Lemma F_137b90 : fetch_word AsanUbsan.M.loaded_segments (0x55db6c : word) = Some W_137b90.
Proof. vm_refl. Qed.
Lemma D_137b90 : decode_any W_137b90 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_137b94 : bv 32 := 0xfe051ce3.
Lemma F_137b94 : fetch_word AsanUbsan.M.loaded_segments (0x55db70 : word) = Some W_137b94.
Proof. vm_refl. Qed.
Lemma D_137b94 : decode_any W_137b94 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_137c48 : bv 32 := 0x00b53023.
Lemma F_137c48 : fetch_word AsanUbsan.M.loaded_segments (0x55dc24 : word) = Some W_137c48.
Proof. vm_refl. Qed.
Lemma D_137c48 : decode_any W_137c48 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_137c4c : bv 32 := 0x00158593.
Lemma F_137c4c : fetch_word AsanUbsan.M.loaded_segments (0x55dc28 : word) = Some W_137c4c.
Proof. vm_refl. Qed.
Lemma D_137c4c : decode_any W_137c4c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_137c50 : bv 32 := 0xfff5c683.
Lemma F_137c50 : fetch_word AsanUbsan.M.loaded_segments (0x55dc2c : word) = Some W_137c50.
Proof. vm_refl. Qed.
Lemma D_137c50 : decode_any W_137c50 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_137c54 : bv 32 := 0xfec68ae3.
Lemma F_137c54 : fetch_word AsanUbsan.M.loaded_segments (0x55dc30 : word) = Some W_137c54.
Proof. vm_refl. Qed.
Lemma D_137c54 : decode_any W_137c54 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_137c58 : bv 32 := 0xfe069ae3.
Lemma F_137c58 : fetch_word AsanUbsan.M.loaded_segments (0x55dc34 : word) = Some W_137c58.
Proof. vm_refl. Qed.
Lemma D_137c58 : decode_any W_137c58 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
