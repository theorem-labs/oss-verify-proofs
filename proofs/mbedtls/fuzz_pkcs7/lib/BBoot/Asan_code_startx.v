(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_dd408 : bv 32 := 0x0004b503.
Lemma F_dd408 : fetch_word AsanUbsan.M.loaded_segments (0x0e07c4 : word) = Some W_dd408.
Proof. vm_refl. Qed.
Lemma D_dd408 : decode_any W_dd408 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd40c : bv 32 := 0x00848493.
Lemma F_dd40c : fetch_word AsanUbsan.M.loaded_segments (0x0e07c8 : word) = Some W_dd40c.
Proof. vm_refl. Qed.
Lemma D_dd40c : decode_any W_dd40c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd410 : bv 32 := 0xfe051ce3.
Lemma F_dd410 : fetch_word AsanUbsan.M.loaded_segments (0x0e07cc : word) = Some W_dd410.
Proof. vm_refl. Qed.
Lemma D_dd410 : decode_any W_dd410 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_dd4c4 : bv 32 := 0x00b53023.
Lemma F_dd4c4 : fetch_word AsanUbsan.M.loaded_segments (0x0e0880 : word) = Some W_dd4c4.
Proof. vm_refl. Qed.
Lemma D_dd4c4 : decode_any W_dd4c4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd4c8 : bv 32 := 0x00158593.
Lemma F_dd4c8 : fetch_word AsanUbsan.M.loaded_segments (0x0e0884 : word) = Some W_dd4c8.
Proof. vm_refl. Qed.
Lemma D_dd4c8 : decode_any W_dd4c8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd4cc : bv 32 := 0xfff5c683.
Lemma F_dd4cc : fetch_word AsanUbsan.M.loaded_segments (0x0e0888 : word) = Some W_dd4cc.
Proof. vm_refl. Qed.
Lemma D_dd4cc : decode_any W_dd4cc = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd4d0 : bv 32 := 0xfec68ae3.
Lemma F_dd4d0 : fetch_word AsanUbsan.M.loaded_segments (0x0e088c : word) = Some W_dd4d0.
Proof. vm_refl. Qed.
Lemma D_dd4d0 : decode_any W_dd4d0 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd4d4 : bv 32 := 0xfe069ae3.
Lemma F_dd4d4 : fetch_word AsanUbsan.M.loaded_segments (0x0e0890 : word) = Some W_dd4d4.
Proof. vm_refl. Qed.
Lemma D_dd4d4 : decode_any W_dd4d4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
