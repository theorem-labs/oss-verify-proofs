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
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8cfb4 : bv 32 := 0x0004b503.
Lemma F_8cfb4 : fetch_word AsanUbsan.M.loaded_segments (0x8cfb4 : word) = Some W_8cfb4.
Proof. vm_refl. Qed.
Lemma D_8cfb4 : decode_any W_8cfb4 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfb8 : bv 32 := 0x00848493.
Lemma F_8cfb8 : fetch_word AsanUbsan.M.loaded_segments (0x8cfb8 : word) = Some W_8cfb8.
Proof. vm_refl. Qed.
Lemma D_8cfb8 : decode_any W_8cfb8 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8cfbc : bv 32 := 0xfe051ce3.
Lemma F_8cfbc : fetch_word AsanUbsan.M.loaded_segments (0x8cfbc : word) = Some W_8cfbc.
Proof. vm_refl. Qed.
Lemma D_8cfbc : decode_any W_8cfbc = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_8d070 : bv 32 := 0x00b53023.
Lemma F_8d070 : fetch_word AsanUbsan.M.loaded_segments (0x8d070 : word) = Some W_8d070.
Proof. vm_refl. Qed.
Lemma D_8d070 : decode_any W_8d070 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d074 : bv 32 := 0x00158593.
Lemma F_8d074 : fetch_word AsanUbsan.M.loaded_segments (0x8d074 : word) = Some W_8d074.
Proof. vm_refl. Qed.
Lemma D_8d074 : decode_any W_8d074 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d078 : bv 32 := 0xfff5c683.
Lemma F_8d078 : fetch_word AsanUbsan.M.loaded_segments (0x8d078 : word) = Some W_8d078.
Proof. vm_refl. Qed.
Lemma D_8d078 : decode_any W_8d078 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d07c : bv 32 := 0xfec68ae3.
Lemma F_8d07c : fetch_word AsanUbsan.M.loaded_segments (0x8d07c : word) = Some W_8d07c.
Proof. vm_refl. Qed.
Lemma D_8d07c : decode_any W_8d07c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d080 : bv 32 := 0xfe069ae3.
Lemma F_8d080 : fetch_word AsanUbsan.M.loaded_segments (0x8d080 : word) = Some W_8d080.
Proof. vm_refl. Qed.
Lemma D_8d080 : decode_any W_8d080 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
