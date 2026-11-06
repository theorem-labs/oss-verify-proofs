(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_88b50 : bv 32 := 0x0004b503.
Lemma F_88b50 : fetch_word Asan.M.loaded_segments (0xf2340 : word) = Some W_88b50.
Proof. vm_refl. Qed.
Lemma D_88b50 : decode_any W_88b50 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88b54 : bv 32 := 0x00848493.
Lemma F_88b54 : fetch_word Asan.M.loaded_segments (0xf2344 : word) = Some W_88b54.
Proof. vm_refl. Qed.
Lemma D_88b54 : decode_any W_88b54 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_88b58 : bv 32 := 0xfe051ce3.
Lemma F_88b58 : fetch_word Asan.M.loaded_segments (0xf2348 : word) = Some W_88b58.
Proof. vm_refl. Qed.
Lemma D_88b58 : decode_any W_88b58 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_88c0c : bv 32 := 0x00b53023.
Lemma F_88c0c : fetch_word Asan.M.loaded_segments (0xf23fc : word) = Some W_88c0c.
Proof. vm_refl. Qed.
Lemma D_88c0c : decode_any W_88c0c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_88c10 : bv 32 := 0x00158593.
Lemma F_88c10 : fetch_word Asan.M.loaded_segments (0xf2400 : word) = Some W_88c10.
Proof. vm_refl. Qed.
Lemma D_88c10 : decode_any W_88c10 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_88c14 : bv 32 := 0xfff5c683.
Lemma F_88c14 : fetch_word Asan.M.loaded_segments (0xf2404 : word) = Some W_88c14.
Proof. vm_refl. Qed.
Lemma D_88c14 : decode_any W_88c14 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_88c18 : bv 32 := 0xfec68ae3.
Lemma F_88c18 : fetch_word Asan.M.loaded_segments (0xf2408 : word) = Some W_88c18.
Proof. vm_refl. Qed.
Lemma D_88c18 : decode_any W_88c18 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_88c1c : bv 32 := 0xfe069ae3.
Lemma F_88c1c : fetch_word Asan.M.loaded_segments (0xf240c : word) = Some W_88c1c.
Proof. vm_refl. Qed.
Lemma D_88c1c : decode_any W_88c1c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
