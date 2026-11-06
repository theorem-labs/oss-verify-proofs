(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_94a40 : bv 32 := 0x0004b503.
Lemma F_94a40 : fetch_word AsanUbsan.M.loaded_segments (0x94d04 : word) = Some W_94a40.
Proof. vm_refl. Qed.
Lemma D_94a40 : decode_any W_94a40 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a44 : bv 32 := 0x00848493.
Lemma F_94a44 : fetch_word AsanUbsan.M.loaded_segments (0x94d08 : word) = Some W_94a44.
Proof. vm_refl. Qed.
Lemma D_94a44 : decode_any W_94a44 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_94a48 : bv 32 := 0xfe051ce3.
Lemma F_94a48 : fetch_word AsanUbsan.M.loaded_segments (0x94d0c : word) = Some W_94a48.
Proof. vm_refl. Qed.
Lemma D_94a48 : decode_any W_94a48 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_94afc : bv 32 := 0x00b53023.
Lemma F_94afc : fetch_word AsanUbsan.M.loaded_segments (0x94dc0 : word) = Some W_94afc.
Proof. vm_refl. Qed.
Lemma D_94afc : decode_any W_94afc = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b00 : bv 32 := 0x00158593.
Lemma F_94b00 : fetch_word AsanUbsan.M.loaded_segments (0x94dc4 : word) = Some W_94b00.
Proof. vm_refl. Qed.
Lemma D_94b00 : decode_any W_94b00 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b04 : bv 32 := 0xfff5c683.
Lemma F_94b04 : fetch_word AsanUbsan.M.loaded_segments (0x94dc8 : word) = Some W_94b04.
Proof. vm_refl. Qed.
Lemma D_94b04 : decode_any W_94b04 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b08 : bv 32 := 0xfec68ae3.
Lemma F_94b08 : fetch_word AsanUbsan.M.loaded_segments (0x94dcc : word) = Some W_94b08.
Proof. vm_refl. Qed.
Lemma D_94b08 : decode_any W_94b08 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_94b0c : bv 32 := 0xfe069ae3.
Lemma F_94b0c : fetch_word AsanUbsan.M.loaded_segments (0x94dd0 : word) = Some W_94b0c.
Proof. vm_refl. Qed.
Lemma D_94b0c : decode_any W_94b0c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
