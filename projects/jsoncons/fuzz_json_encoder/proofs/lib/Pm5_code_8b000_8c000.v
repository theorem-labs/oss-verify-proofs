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
Definition W_8b8e4 : bv 32 := 0xff010113.
Lemma F_8b8e4 : fetch_word AsanUbsan.M.loaded_segments (0x8b92c : word) = Some W_8b8e4.
Proof. vm_refl. Qed.
Lemma D_8b8e4 : decode_any W_8b8e4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b8e8 : bv 32 := 0x00113423.
Lemma F_8b8e8 : fetch_word AsanUbsan.M.loaded_segments (0x8b930 : word) = Some W_8b8e8.
Proof. vm_refl. Qed.
Lemma D_8b8e8 : decode_any W_8b8e8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b8ec : bv 32 := 0x62d000ef.
Lemma F_8b8ec : fetch_word AsanUbsan.M.loaded_segments (0x8b934 : word) = Some W_8b8ec.
Proof. vm_refl. Qed.
Lemma D_8b8ec : decode_any W_8b8ec = Some (Jal 1 3628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b8f0 : bv 32 := 0x00050c63.
Lemma F_8b8f0 : fetch_word AsanUbsan.M.loaded_segments (0x8b938 : word) = Some W_8b8f0.
Proof. vm_refl. Qed.
Lemma D_8b8f0 : decode_any W_8b8f0 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b8f4 : bv 32 := 0x7ff50513.
Lemma F_8b8f4 : fetch_word AsanUbsan.M.loaded_segments (0x8b93c : word) = Some W_8b8f4.
Proof. vm_refl. Qed.
Lemma D_8b8f4 : decode_any W_8b8f4 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b8f8 : bv 32 := 0x2f150513.
Lemma F_8b8f8 : fetch_word AsanUbsan.M.loaded_segments (0x8b940 : word) = Some W_8b8f8.
Proof. vm_refl. Qed.
Lemma D_8b8f8 : decode_any W_8b8f8 = Some (OpImm ALU_ADD 10 10 753, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b8fc : bv 32 := 0x00813083.
Lemma F_8b8fc : fetch_word AsanUbsan.M.loaded_segments (0x8b944 : word) = Some W_8b8fc.
Proof. vm_refl. Qed.
Lemma D_8b8fc : decode_any W_8b8fc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b900 : bv 32 := 0x01010113.
Lemma F_8b900 : fetch_word AsanUbsan.M.loaded_segments (0x8b948 : word) = Some W_8b900.
Proof. vm_refl. Qed.
Lemma D_8b900 : decode_any W_8b900 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b904 : bv 32 := 0x00008067.
Lemma F_8b904 : fetch_word AsanUbsan.M.loaded_segments (0x8b94c : word) = Some W_8b904.
Proof. vm_refl. Qed.
Lemma D_8b904 : decode_any W_8b904 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

