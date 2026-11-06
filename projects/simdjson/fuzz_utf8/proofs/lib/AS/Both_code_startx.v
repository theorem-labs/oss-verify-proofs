(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import AsanUbsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_151f5c : bv 32 := 0x0004b503.
Lemma F_151f5c : fetch_word AsanUbsan.M.loaded_segments (0x1522b8 : word) = Some W_151f5c.
Proof. vm_refl. Qed.
Lemma D_151f5c : decode_any W_151f5c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151f60 : bv 32 := 0x00848493.
Lemma F_151f60 : fetch_word AsanUbsan.M.loaded_segments (0x1522bc : word) = Some W_151f60.
Proof. vm_refl. Qed.
Lemma D_151f60 : decode_any W_151f60 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151f64 : bv 32 := 0xfe051ce3.
Lemma F_151f64 : fetch_word AsanUbsan.M.loaded_segments (0x1522c0 : word) = Some W_151f64.
Proof. vm_refl. Qed.
Lemma D_151f64 : decode_any W_151f64 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_152018 : bv 32 := 0x00b53023.
Lemma F_152018 : fetch_word AsanUbsan.M.loaded_segments (0x152374 : word) = Some W_152018.
Proof. vm_refl. Qed.
Lemma D_152018 : decode_any W_152018 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15201c : bv 32 := 0x00158593.
Lemma F_15201c : fetch_word AsanUbsan.M.loaded_segments (0x152378 : word) = Some W_15201c.
Proof. vm_refl. Qed.
Lemma D_15201c : decode_any W_15201c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152020 : bv 32 := 0xfff5c683.
Lemma F_152020 : fetch_word AsanUbsan.M.loaded_segments (0x15237c : word) = Some W_152020.
Proof. vm_refl. Qed.
Lemma D_152020 : decode_any W_152020 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152024 : bv 32 := 0xfec68ae3.
Lemma F_152024 : fetch_word AsanUbsan.M.loaded_segments (0x152380 : word) = Some W_152024.
Proof. vm_refl. Qed.
Lemma D_152024 : decode_any W_152024 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152028 : bv 32 := 0xfe069ae3.
Lemma F_152028 : fetch_word AsanUbsan.M.loaded_segments (0x152384 : word) = Some W_152028.
Proof. vm_refl. Qed.
Lemma D_152028 : decode_any W_152028 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
