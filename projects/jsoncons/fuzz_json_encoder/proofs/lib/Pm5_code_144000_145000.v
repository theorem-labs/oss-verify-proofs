(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_144898 : bv 32 := 0x0004b503.
Lemma F_144898 : fetch_word AsanUbsan.M.loaded_segments (0x1448e0 : word) = Some W_144898.
Proof. vm_refl. Qed.
Lemma D_144898 : decode_any W_144898 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14489c : bv 32 := 0x00848493.
Lemma F_14489c : fetch_word AsanUbsan.M.loaded_segments (0x1448e4 : word) = Some W_14489c.
Proof. vm_refl. Qed.
Lemma D_14489c : decode_any W_14489c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1448a0 : bv 32 := 0xfe051ce3.
Lemma F_1448a0 : fetch_word AsanUbsan.M.loaded_segments (0x1448e8 : word) = Some W_1448a0.
Proof. vm_refl. Qed.
Lemma D_1448a0 : decode_any W_1448a0 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_144954 : bv 32 := 0x00b53023.
Lemma F_144954 : fetch_word AsanUbsan.M.loaded_segments (0x14499c : word) = Some W_144954.
Proof. vm_refl. Qed.
Lemma D_144954 : decode_any W_144954 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_144958 : bv 32 := 0x00158593.
Lemma F_144958 : fetch_word AsanUbsan.M.loaded_segments (0x1449a0 : word) = Some W_144958.
Proof. vm_refl. Qed.
Lemma D_144958 : decode_any W_144958 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14495c : bv 32 := 0xfff5c683.
Lemma F_14495c : fetch_word AsanUbsan.M.loaded_segments (0x1449a4 : word) = Some W_14495c.
Proof. vm_refl. Qed.
Lemma D_14495c : decode_any W_14495c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_144960 : bv 32 := 0xfec68ae3.
Lemma F_144960 : fetch_word AsanUbsan.M.loaded_segments (0x1449a8 : word) = Some W_144960.
Proof. vm_refl. Qed.
Lemma D_144960 : decode_any W_144960 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_144964 : bv 32 := 0xfe069ae3.
Lemma F_144964 : fetch_word AsanUbsan.M.loaded_segments (0x1449ac : word) = Some W_144964.
Proof. vm_refl. Qed.
Lemma D_144964 : decode_any W_144964 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_144f7c : bv 32 := 0x00020513.
Lemma F_144f7c : fetch_word AsanUbsan.M.loaded_segments (0x144fb8 : word) = Some W_144f7c.
Proof. vm_refl. Qed.
Lemma D_144f7c : decode_any W_144f7c = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_144f80 : bv 32 := 0xf5c50513.
Lemma F_144f80 : fetch_word AsanUbsan.M.loaded_segments (0x144fbc : word) = Some W_144f80.
Proof. vm_refl. Qed.
Lemma D_144f80 : decode_any W_144f80 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_144f84 : bv 32 := 0x00008067.
Lemma F_144f84 : fetch_word AsanUbsan.M.loaded_segments (0x144fc0 : word) = Some W_144f84.
Proof. vm_refl. Qed.
Lemma D_144f84 : decode_any W_144f84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

