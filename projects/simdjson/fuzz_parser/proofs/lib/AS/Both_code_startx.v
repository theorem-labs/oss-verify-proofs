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
From OSSVerify.simdjson.fuzz_parser.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_f9a28 : bv 32 := 0x0004b503.
Lemma F_f9a28 : fetch_word AsanUbsan.M.loaded_segments (0xf9bf0 : word) = Some W_f9a28.
Proof. vm_refl. Qed.
Lemma D_f9a28 : decode_any W_f9a28 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f9a2c : bv 32 := 0x00848493.
Lemma F_f9a2c : fetch_word AsanUbsan.M.loaded_segments (0xf9bf4 : word) = Some W_f9a2c.
Proof. vm_refl. Qed.
Lemma D_f9a2c : decode_any W_f9a2c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f9a30 : bv 32 := 0xfe051ce3.
Lemma F_f9a30 : fetch_word AsanUbsan.M.loaded_segments (0xf9bf8 : word) = Some W_f9a30.
Proof. vm_refl. Qed.
Lemma D_f9a30 : decode_any W_f9a30 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_f9ae4 : bv 32 := 0x00b53023.
Lemma F_f9ae4 : fetch_word AsanUbsan.M.loaded_segments (0xf9cac : word) = Some W_f9ae4.
Proof. vm_refl. Qed.
Lemma D_f9ae4 : decode_any W_f9ae4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f9ae8 : bv 32 := 0x00158593.
Lemma F_f9ae8 : fetch_word AsanUbsan.M.loaded_segments (0xf9cb0 : word) = Some W_f9ae8.
Proof. vm_refl. Qed.
Lemma D_f9ae8 : decode_any W_f9ae8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f9aec : bv 32 := 0xfff5c683.
Lemma F_f9aec : fetch_word AsanUbsan.M.loaded_segments (0xf9cb4 : word) = Some W_f9aec.
Proof. vm_refl. Qed.
Lemma D_f9aec : decode_any W_f9aec = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f9af0 : bv 32 := 0xfec68ae3.
Lemma F_f9af0 : fetch_word AsanUbsan.M.loaded_segments (0xf9cb8 : word) = Some W_f9af0.
Proof. vm_refl. Qed.
Lemma D_f9af0 : decode_any W_f9af0 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_f9af4 : bv 32 := 0xfe069ae3.
Lemma F_f9af4 : fetch_word AsanUbsan.M.loaded_segments (0xf9cbc : word) = Some W_f9af4.
Proof. vm_refl. Qed.
Lemma D_f9af4 : decode_any W_f9af4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
