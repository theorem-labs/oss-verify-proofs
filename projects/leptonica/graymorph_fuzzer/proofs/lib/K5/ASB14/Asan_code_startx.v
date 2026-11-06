(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_d5c44 : bv 32 := 0x0004b503.
Lemma F_d5c44 : fetch_word AsanUbsan.M.loaded_segments (0xd6798 : word) = Some W_d5c44.
Proof. vm_refl. Qed.
Lemma D_d5c44 : decode_any W_d5c44 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d5c48 : bv 32 := 0x00848493.
Lemma F_d5c48 : fetch_word AsanUbsan.M.loaded_segments (0xd679c : word) = Some W_d5c48.
Proof. vm_refl. Qed.
Lemma D_d5c48 : decode_any W_d5c48 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d5c4c : bv 32 := 0xfe051ce3.
Lemma F_d5c4c : fetch_word AsanUbsan.M.loaded_segments (0xd67a0 : word) = Some W_d5c4c.
Proof. vm_refl. Qed.
Lemma D_d5c4c : decode_any W_d5c4c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_d5d00 : bv 32 := 0x00b53023.
Lemma F_d5d00 : fetch_word AsanUbsan.M.loaded_segments (0xd6854 : word) = Some W_d5d00.
Proof. vm_refl. Qed.
Lemma D_d5d00 : decode_any W_d5d00 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d5d04 : bv 32 := 0x00158593.
Lemma F_d5d04 : fetch_word AsanUbsan.M.loaded_segments (0xd6858 : word) = Some W_d5d04.
Proof. vm_refl. Qed.
Lemma D_d5d04 : decode_any W_d5d04 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d5d08 : bv 32 := 0xfff5c683.
Lemma F_d5d08 : fetch_word AsanUbsan.M.loaded_segments (0xd685c : word) = Some W_d5d08.
Proof. vm_refl. Qed.
Lemma D_d5d08 : decode_any W_d5d08 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d5d0c : bv 32 := 0xfec68ae3.
Lemma F_d5d0c : fetch_word AsanUbsan.M.loaded_segments (0xd6860 : word) = Some W_d5d0c.
Proof. vm_refl. Qed.
Lemma D_d5d0c : decode_any W_d5d0c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d5d10 : bv 32 := 0xfe069ae3.
Lemma F_d5d10 : fetch_word AsanUbsan.M.loaded_segments (0xd6864 : word) = Some W_d5d10.
Proof. vm_refl. Qed.
Lemma D_d5d10 : decode_any W_d5d10 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
