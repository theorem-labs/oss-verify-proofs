(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_557498 : bv 32 := 0x0004b503.
Lemma F_557498 : fetch_word AsanUbsan.M.loaded_segments (0x557490 : word) = Some W_557498.
Proof. vm_refl. Qed.
Lemma D_557498 : decode_any W_557498 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55749c : bv 32 := 0x00848493.
Lemma F_55749c : fetch_word AsanUbsan.M.loaded_segments (0x557494 : word) = Some W_55749c.
Proof. vm_refl. Qed.
Lemma D_55749c : decode_any W_55749c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5574a0 : bv 32 := 0xfe051ce3.
Lemma F_5574a0 : fetch_word AsanUbsan.M.loaded_segments (0x557498 : word) = Some W_5574a0.
Proof. vm_refl. Qed.
Lemma D_5574a0 : decode_any W_5574a0 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_557554 : bv 32 := 0x00b53023.
Lemma F_557554 : fetch_word AsanUbsan.M.loaded_segments (0x55754c : word) = Some W_557554.
Proof. vm_refl. Qed.
Lemma D_557554 : decode_any W_557554 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_557558 : bv 32 := 0x00158593.
Lemma F_557558 : fetch_word AsanUbsan.M.loaded_segments (0x557550 : word) = Some W_557558.
Proof. vm_refl. Qed.
Lemma D_557558 : decode_any W_557558 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55755c : bv 32 := 0xfff5c683.
Lemma F_55755c : fetch_word AsanUbsan.M.loaded_segments (0x557554 : word) = Some W_55755c.
Proof. vm_refl. Qed.
Lemma D_55755c : decode_any W_55755c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_557560 : bv 32 := 0xfec68ae3.
Lemma F_557560 : fetch_word AsanUbsan.M.loaded_segments (0x557558 : word) = Some W_557560.
Proof. vm_refl. Qed.
Lemma D_557560 : decode_any W_557560 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_557564 : bv 32 := 0xfe069ae3.
Lemma F_557564 : fetch_word AsanUbsan.M.loaded_segments (0x55755c : word) = Some W_557564.
Proof. vm_refl. Qed.
Lemma D_557564 : decode_any W_557564 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
