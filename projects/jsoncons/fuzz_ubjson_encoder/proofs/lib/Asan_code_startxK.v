(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_119900 : bv 32 := 0x0004b503.
Lemma F_119900 : fetch_word Asan.M.loaded_segments (0x119950 : word) = Some W_119900.
Proof. vm_refl. Qed.
Lemma D_119900 : decode_any W_119900 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_119904 : bv 32 := 0x00848493.
Lemma F_119904 : fetch_word Asan.M.loaded_segments (0x119954 : word) = Some W_119904.
Proof. vm_refl. Qed.
Lemma D_119904 : decode_any W_119904 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_119908 : bv 32 := 0xfe051ce3.
Lemma F_119908 : fetch_word Asan.M.loaded_segments (0x119958 : word) = Some W_119908.
Proof. vm_refl. Qed.
Lemma D_119908 : decode_any W_119908 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1199bc : bv 32 := 0x00b53023.
Lemma F_1199bc : fetch_word Asan.M.loaded_segments (0x119a0c : word) = Some W_1199bc.
Proof. vm_refl. Qed.
Lemma D_1199bc : decode_any W_1199bc = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1199c0 : bv 32 := 0x00158593.
Lemma F_1199c0 : fetch_word Asan.M.loaded_segments (0x119a10 : word) = Some W_1199c0.
Proof. vm_refl. Qed.
Lemma D_1199c0 : decode_any W_1199c0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1199c4 : bv 32 := 0xfff5c683.
Lemma F_1199c4 : fetch_word Asan.M.loaded_segments (0x119a14 : word) = Some W_1199c4.
Proof. vm_refl. Qed.
Lemma D_1199c4 : decode_any W_1199c4 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1199c8 : bv 32 := 0xfec68ae3.
Lemma F_1199c8 : fetch_word Asan.M.loaded_segments (0x119a18 : word) = Some W_1199c8.
Proof. vm_refl. Qed.
Lemma D_1199c8 : decode_any W_1199c8 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1199cc : bv 32 := 0xfe069ae3.
Lemma F_1199cc : fetch_word Asan.M.loaded_segments (0x119a1c : word) = Some W_1199cc.
Proof. vm_refl. Qed.
Lemma D_1199cc : decode_any W_1199cc = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
