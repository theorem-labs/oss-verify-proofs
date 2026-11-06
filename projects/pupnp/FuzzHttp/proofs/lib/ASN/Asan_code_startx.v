(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_93d80 : bv 32 := 0x0004b503.
Lemma F_93d80 : fetch_word Asan.M.loaded_segments (0x940a0 : word) = Some W_93d80.
Proof. vm_refl. Qed.
Lemma D_93d80 : decode_any W_93d80 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93d84 : bv 32 := 0x00848493.
Lemma F_93d84 : fetch_word Asan.M.loaded_segments (0x940a4 : word) = Some W_93d84.
Proof. vm_refl. Qed.
Lemma D_93d84 : decode_any W_93d84 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_93d88 : bv 32 := 0xfe051ce3.
Lemma F_93d88 : fetch_word Asan.M.loaded_segments (0x940a8 : word) = Some W_93d88.
Proof. vm_refl. Qed.
Lemma D_93d88 : decode_any W_93d88 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_93e3c : bv 32 := 0x00b53023.
Lemma F_93e3c : fetch_word Asan.M.loaded_segments (0x9415c : word) = Some W_93e3c.
Proof. vm_refl. Qed.
Lemma D_93e3c : decode_any W_93e3c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_93e40 : bv 32 := 0x00158593.
Lemma F_93e40 : fetch_word Asan.M.loaded_segments (0x94160 : word) = Some W_93e40.
Proof. vm_refl. Qed.
Lemma D_93e40 : decode_any W_93e40 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_93e44 : bv 32 := 0xfff5c683.
Lemma F_93e44 : fetch_word Asan.M.loaded_segments (0x94164 : word) = Some W_93e44.
Proof. vm_refl. Qed.
Lemma D_93e44 : decode_any W_93e44 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_93e48 : bv 32 := 0xfec68ae3.
Lemma F_93e48 : fetch_word Asan.M.loaded_segments (0x94168 : word) = Some W_93e48.
Proof. vm_refl. Qed.
Lemma D_93e48 : decode_any W_93e48 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_93e4c : bv 32 := 0xfe069ae3.
Lemma F_93e4c : fetch_word Asan.M.loaded_segments (0x9416c : word) = Some W_93e4c.
Proof. vm_refl. Qed.
Lemma D_93e4c : decode_any W_93e4c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
